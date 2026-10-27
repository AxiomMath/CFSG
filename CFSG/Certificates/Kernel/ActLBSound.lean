module

public import Certificates.Data.Kernel.ActLB
public import CFSG.Certificates.CosetTablePresented
public import CFSG.Certificates.Kernel.YModel.NetSem
import CFSG.Certificates.Kernel.YModel.ChainSem

public section

namespace CFSG.KS.ActLB

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.YModel CFSG.KC.ActLB CFSG.CosetTable

variable {m k : Nat} {Nf : Nat → Nat}

theorem lcode_true (x : Fin m) : lcode (x, true) = 2 * x.val := Nat.add_zero _

theorem lcode_false (x : Fin m) : lcode (x, false) = 2 * x.val + 1 := rfl

theorem lcode_lt (a : Fin m × Bool) : lcode a < 2 * m := by
  obtain ⟨x, b⟩ := a
  have := x.2
  cases b
  · rw [lcode_false]
    omega
  · rw [lcode_true]
    omega

theorem relsOK_mem' : ∀ {rels : List (List Nat)}, relsOK k m Nf rels = true →
    ∀ r ∈ rels, wordAp k m Nf r (idP k) = idP k
  | [], _, r, hr => absurd hr List.not_mem_nil
  | r' :: rs, h, r, hr => by
    change andB (Nat.beq (wordAp k m Nf r' (idP k)) (idP k)) (relsOK k m Nf rs) = true at h
    obtain ⟨h1, h2⟩ := Sem.andB_eq h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Nat.eq_of_beq_eq_true h1
    · exact relsOK_mem' h2 r hr

theorem wF_of_relsOK {rels : List (List Nat)} (hv : ∀ c < m, StagesValid k (Nf c))
    (h : relsOK k m Nf rels = true) {r : List Nat} (hr : r ∈ rels) :
    ∀ y < 2 ^ k, Sem.wF k m Nf r y = y :=
  Sem.eq_of_idP (Sem.acts_wordAp hv r) (Sem.acts_id k k) (relsOK_mem' h r hr)

@[expose] noncomputable def netPermF (k N : Nat) (h : StagesValid k N) : Equiv.Perm (Fin (2 ^ k)) where
  toFun r := ⟨benesPerm k N r, benesPerm_lt h r.2⟩
  invFun r := ⟨benesInv k N r, benesInv_lt h r.2⟩
  left_inv r := Fin.ext (benesInv_benesPerm h r)
  right_inv r := Fin.ext (benesPerm_benesInv h r)

theorem netPermF_val {N : Nat} (h : StagesValid k N) (r : Fin (2 ^ k)) :
    (netPermF k N h r).val = benesPerm k N r := rfl

theorem netPermF_inv_val {N : Nat} (h : StagesValid k N) (r : Fin (2 ^ k)) :
    ((netPermF k N h)⁻¹ r).val = benesInv k N r := rfl

structure Nets (m k : Nat) (Nf : Nat → Nat) : Prop where
  valid : ∀ c < 2 * m, StagesValid k (Nf c)
  inv : ∀ x < m, ∀ y < 2 ^ k, benesPerm k (Nf (2 * x + 1)) y = benesInv k (Nf (2 * x)) y

theorem nets_of_checks (hv : ∀ c < 2 * m, netOK k (Nf c) = true)
    (hi : relsOK k (2 * m) Nf (invPairs m) = true) : Nets m k Nf := by
  have hv' : ∀ c < 2 * m, StagesValid k (Nf c) := fun c hc => Benes.stagesValid_of_ymodel (hv c hc)
  refine ⟨hv', fun x hx y hy => ?_⟩
  have hmem : [2 * x, 2 * x + 1] ∈ invPairs m := List.mem_map.mpr ⟨x, List.mem_range.mpr hx, rfl⟩
  have e := wF_of_relsOK hv' hi hmem y hy
  simp only [Sem.wF, if_pos (by omega : 2 * x < 2 * m), if_pos (by omega : 2 * x + 1 < 2 * m)] at e
  have e2 := congrArg (benesInv k (Nf (2 * x))) e
  rw [benesInv_benesPerm (hv' _ (by omega))] at e2
  exact e2

@[expose] noncomputable def sig (H : Nets m k Nf) (x : Fin m) : Equiv.Perm (Fin (2 ^ k)) :=
  netPermF k (Nf (2 * x.val)) (H.valid _ (by have := x.2; omega))

@[expose] noncomputable def letP (H : Nets m k Nf) (a : Fin m × Bool) : Equiv.Perm (Fin (2 ^ k)) :=
  cond a.2 (sig H a.1) (sig H a.1)⁻¹

theorem letP_val (H : Nets m k Nf) (a : Fin m × Bool) (r : Fin (2 ^ k)) :
    (letP H a r).val = benesPerm k (Nf (lcode a)) r := by
  obtain ⟨x, b⟩ := a
  cases b
  · change ((sig H x)⁻¹ r).val = _
    rw [sig, netPermF_inv_val, lcode_false, H.inv x x.2 r r.2]
  · change (sig H x r).val = _
    rw [sig, netPermF_val, lcode_true]

theorem prod_val (H : Nets m k Nf) : ∀ (w : List (Fin m × Bool)) (r : Fin (2 ^ k)),
    ((w.map (letP H)).prod r).val = Sem.wF k (2 * m) Nf (w.map lcode) r
  | [], _ => rfl
  | a :: w, r => by
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, letP_val, prod_val H w r,
      List.map_cons]
    simp only [Sem.wF, if_pos (lcode_lt a)]

theorem lift_mk_val (H : Nets m k Nf) (w : List (Fin m × Bool)) (r : Fin (2 ^ k)) :
    (FreeGroup.lift (sig H) (FreeGroup.mk w) r).val = Sem.wF k (2 * m) Nf (w.map lcode) r := by
  rw [FreeGroup.lift_mk, ← prod_val H w r]
  rfl

@[expose] noncomputable def actHom {ws : List (List (Fin m × Bool))} (H : Nets m k Nf)
    (hr : relsOK k (2 * m) Nf (codesOf ws) = true) : PG m ws →* Equiv.Perm (Fin (2 ^ k)) :=
  PresentedGroup.toGroup (f := sig H) (by
    intro r hrel
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrel
    refine Equiv.ext fun y => Fin.ext ?_
    rw [lift_mk_val, Equiv.Perm.coe_one, id]
    exact wF_of_relsOK H.valid hr (List.mem_map_of_mem hw) y y.2)

theorem le_index_of_checks {ws : List (List (Fin m × Bool))} {S : List (Fin m)} {n R : Nat}
    (hn : n ≤ 2 ^ k) (hv : ∀ c < 2 * m, netOK k (Nf c) = true)
    (hi : relsOK k (2 * m) Nf (invPairs m) = true)
    (hr : relsOK k (2 * m) Nf (codesOf ws) = true)
    (hfix : ∀ x ∈ S, fixK k (Nf (2 * x.val)) 0 = true)
    (horb : orbitOK k (nets (2 * m) Nf) 0 R (ones n) = true)
    (hfi : (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S).FiniteIndex) :
    n ≤ (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S).index := by
  have H := nets_of_checks hv hi
  let ψ := actHom (ws := ws) H hr
  let _ : MulAction (PG m ws) (Fin (2 ^ k)) := MulAction.compHom _ ψ
  have hsm : ∀ (g : PG m ws) (r : Fin (2 ^ k)), g • r = ψ g r := fun _ _ => rfl
  have hof : ∀ x, ψ (PresentedGroup.of x) = sig H x := fun _ => PresentedGroup.toGroup.of _
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  let o : Fin (2 ^ k) := ⟨0, hk⟩
  have hHK : genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S ≤
      MulAction.stabilizer (PG m ws) o := by
    unfold genSub
    rw [Subgroup.closure_le]
    rintro g ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, hsm, hof]
    apply Fin.ext
    have hN := H.valid (2 * x.val) (by have := x.2; omega)
    have hf := Nat.eq_of_beq_eq_true (hfix x hx)
    have hA := Sem.acts_netApply (P := 1) hN
    rw [← Sem.repU_one' k] at hA
    unfold wid at hf
    rw [Sem.shl1] at hf
    exact Sem.eq_of_point hA hk hf
  have hNs : ∀ N ∈ nets (2 * m) Nf, StagesValid k N := by
    intro N hN
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hN
    exact H.valid c (List.mem_range.mp hc)
  obtain ⟨-, -, -, hall⟩ := Chain.orbitOK_spec hNs hk horb
  have horbit : ∀ p, (ones n).testBit p = true →
      ∀ hp : p < 2 ^ k, (⟨p, hp⟩ : Fin (2 ^ k)) ∈ MulAction.orbit (PG m ws) o := by
    refine hall (fun p => ∀ hp : p < 2 ^ k, (⟨p, hp⟩ : Fin (2 ^ k)) ∈ MulAction.orbit (PG m ws) o)
      (fun _ => MulAction.mem_orbit_self o) ?_
    intro p hp N hN hC _
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hN
    have hc' := List.mem_range.mp hc
    have hq := hC (benesPerm_lt (H.valid c hc') hp)
    obtain ⟨g, hg⟩ : ∃ g : PG m ws, (g • (⟨p, hp⟩ : Fin (2 ^ k))).val = benesPerm k (Nf c) p := by
      have hx : c / 2 < m := by omega
      rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
      · refine ⟨PresentedGroup.of ⟨c / 2, hx⟩, ?_⟩
        rw [hsm, hof, sig, netPermF_val]
        have e : 2 * (c / 2) = c := by omega
        change benesPerm k (Nf (2 * (c / 2))) p = _
        rw [e]
      · refine ⟨(PresentedGroup.of ⟨c / 2, hx⟩)⁻¹, ?_⟩
        rw [hsm, map_inv, hof, sig, netPermF_inv_val]
        have e : 2 * (c / 2) + 1 = c := by omega
        change benesInv k (Nf (2 * (c / 2))) p = _
        rw [← H.inv (c / 2) hx p hp, e]
    have hq' : g • (⟨p, hp⟩ : Fin (2 ^ k)) ∈ MulAction.orbit (PG m ws) o := by
      have e : g • (⟨p, hp⟩ : Fin (2 ^ k)) = ⟨benesPerm k (Nf c) p, benesPerm_lt (H.valid c hc') hp⟩ :=
        Fin.ext hg
      rw [e]
      exact hq
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hq'
    exact MulAction.mem_orbit_iff.mpr ⟨g⁻¹ * h, by rw [mul_smul, hh, inv_smul_smul]⟩
  let f : Fin n → MulAction.orbit (PG m ws) o := fun i =>
    ⟨⟨i.val, by omega⟩, horbit i.val (by rw [ones_eq, Nat.testBit_two_pow_sub_one,
      decide_eq_true i.2]) (by omega)⟩
  have hf : Function.Injective f := fun i j e => Fin.ext (congrArg (fun z => z.1.val) e)
  have h1 : n ≤ Nat.card (MulAction.orbit (PG m ws) o) := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have h2 : (MulAction.stabilizer (PG m ws) o).index = Nat.card (MulAction.orbit (PG m ws) o) := by
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have hdvd := Subgroup.index_dvd_of_le hHK
  exact (h2 ▸ h1).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hfi.index_ne_zero) hdvd)

end CFSG.KS.ActLB

end
