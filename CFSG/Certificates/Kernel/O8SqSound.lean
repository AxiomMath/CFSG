module

public import Certificates.Data.Kernel.O8Sq
public import Certificates.Data.Kernel.O8SqForest
public import CFSG.Certificates.Kernel.PCentCheck
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.O8Sq

open CFSG.KC.Enum (pcomp allN)
open CFSG.KS (mask pinvS)
open CFSG.KC.PCent CFSG.KC.BfsPin

variable {n w : Nat}

theorem toPerm_comm_iff {a b : Nat} (ha : PP n w a) (hb : PP n w b) :
    Nat.beq (pcomp n w (mask w) a b) (pcomp n w (mask w) b a) = true ↔
      toPerm n w a * toPerm n w b = toPerm n w b * toPerm n w a := by
  rw [Nat.beq_eq, ← toPerm_mul ha hb, ← toPerm_mul hb ha]
  exact ⟨fun h => by rw [h], fun h => toPerm_injective (ha.mul hb) (hb.mul ha) h⟩

theorem card_filter_comm_of_cntCommK [DecidableEq (Equiv.Perm (Fin n))] {x : Nat} (hx : PP n w x) :
    ∀ {R : List Rec}, (∀ r ∈ R, PP n w r.1) → (R.map Prod.fst).Nodup →
      (((R.map Prod.fst).map (toPerm n w)).toFinset.filter
        (fun a => a * toPerm n w x = toPerm n w x * a)).card = cntCommK n w x R
  | [], _, _ => rfl
  | ⟨v, d⟩ :: l, hR, hnd => by
    have hv : PP n w v := hR _ List.mem_cons_self
    have hl : ∀ r ∈ l, PP n w r.1 := fun r hr => hR r (List.mem_cons_of_mem _ hr)
    rw [List.map_cons, List.nodup_cons] at hnd
    have ih := card_filter_comm_of_cntCommK hx hl hnd.2
    have hnot : toPerm n w v ∉ ((l.map Prod.fst).map (toPerm n w)).toFinset := by
      intro hm
      obtain ⟨u, hu, e⟩ := List.mem_map.1 (List.mem_toFinset.1 hm)
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hu
      have ev : r.1 = v := toPerm_injective (hl r hr) hv e
      rw [ev] at hu
      exact hnd.1 hu
    have e : cntCommK n w x (⟨v, d⟩ :: l) = Bool.rec (motive := fun _ => Nat) (cntCommK n w x l)
        (Nat.succ (cntCommK n w x l))
        (Nat.beq (pcomp n w (mask w) v x) (pcomp n w (mask w) x v)) := rfl
    rw [List.map_cons, List.map_cons, List.toFinset_cons, Finset.filter_insert, e]
    by_cases hc : toPerm n w v * toPerm n w x = toPerm n w x * toPerm n w v
    · rw [if_pos hc, (toPerm_comm_iff hv hx).2 hc, Finset.card_insert_of_notMem
        (fun hm => hnot (Finset.mem_filter.1 hm).1), ih]
    · rw [if_neg hc, ih]
      have hb : Nat.beq (pcomp n w (mask w) v x) (pcomp n w (mask w) x v) = false := by
        rw [Bool.eq_false_iff]
        exact fun h => hc ((toPerm_comm_iff hv hx).1 h)
      rw [hb]

theorem walkF_spec {ACT : Nat → Nat → Nat} {ngen N nr : Nat} {RT : Nat → Nat} {T : PTree Rec} :
    ∀ (R : List Rec) (lo : Nat), walkF ACT ngen N nr RT T R lo = true →
      (R.map Prod.fst).Pairwise (· < ·) ∧ (∀ r ∈ R, lo ≤ r.1) ∧
        ∀ r ∈ R, recF ACT ngen N nr RT r (getT T r.2.2.2) = true
  | [], _, _ => by simp
  | r :: l, lo, h => by
    change (Nat.ble lo r.1 && recF ACT ngen N nr RT r (getT T r.2.2.2) &&
      walkF ACT ngen N nr RT T l (Nat.add r.1 1)) = true at h
    simp only [Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨ih1, ih2, ih3⟩ := walkF_spec l _ h3
    refine ⟨?_, ?_, ?_⟩
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun b hb => ?_, ih1⟩
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hb
      have := ih2 r' hr'
      change r.1 + 1 ≤ r'.1 at this
      omega
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact h1
      · have := ih2 r' hr'
        change r.1 + 1 ≤ r'.1 at this
        omega
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact h2
      · exact ih3 r' hr'

theorem forestK_sound {G GI RT : Nat → Nat} {ngen nr : Nat} {R : List Rec}
    (hG : ∀ k < ngen, PP n w (G k)) (hRT : ∀ j < nr, PP n w (RT j))
    (h : forestK n w G GI ngen RT nr R = true) :
    (R.map Prod.fst).Pairwise (· < ·) ∧ ∀ r ∈ R, PP n w r.1 ∧ ∃ j < nr,
      ∃ g ∈ Subgroup.closure (gens n w G ngen), g * toPerm n w (RT j) * g⁻¹ = toPerm n w r.1 := by
  unfold forestK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hI, h⟩ := h
  have hA : ∀ k < ngen, ∀ y, conjI n w G GI k y = CFSG.KC.Misc.ArrEnum.conjAct n w G k y := by
    intro k hk y
    have e := CFSG.KS.Raw.Orb.allN_iff.1 hI k hk
    rw [Nat.beq_eq] at e
    unfold conjI CFSG.KC.Misc.ArrEnum.conjAct
    rw [e]
  obtain ⟨hs, -, h3⟩ := walkF_spec R 0 h
  refine ⟨hs, ?_⟩
  suffices H : ∀ d, ∀ r ∈ R, r.2.1 = d → PP n w r.1 ∧ ∃ j < nr,
      ∃ g ∈ Subgroup.closure (gens n w G ngen), g * toPerm n w (RT j) * g⁻¹ = toPerm n w r.1 from
    fun r hr => H _ r hr rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro r hr hd
    have hc := h3 r hr
    rw [getT_treeOf] at hc
    unfold recF at hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hc
    rcases hc with ⟨⟨-, hj⟩, he⟩ | ⟨⟨⟨hp, hk⟩, hq⟩, he⟩
    · rw [he]
      exact ⟨hRT _ hj, _, hj, 1, Subgroup.one_mem _, by group⟩
    · have hmem : R.getD r.2.2.2 default ∈ R := by
        rw [List.getD_eq_getElem _ _ hp]
        exact List.getElem_mem hp
      obtain ⟨hy, j, hj, g, hg, hge⟩ := ih _ (by omega) _ hmem rfl
      rw [he, hA _ hk]
      refine ⟨PP_conjAct (hG _ hk) hy, j, hj, toPerm n w (G r.2.2.1) * g,
        Subgroup.mul_mem _ (gen_mem hk) hg, ?_⟩
      rw [toPerm_conjAct (hG _ hk) hy, ← hge]
      group

theorem forestK_card [DecidableEq (Equiv.Perm (Fin n))] {G GI RT : Nat → Nat} {ngen nr : Nat}
    {R : List Rec} (hG : ∀ k < ngen, PP n w (G k)) (hRT : ∀ j < nr, PP n w (RT j))
    (h : forestK n w G GI ngen RT nr R = true) :
    (((R.map Prod.fst).map (toPerm n w)).toFinset).card = R.length ∧
      ∀ s ∈ ((R.map Prod.fst).map (toPerm n w)).toFinset, ∃ j < nr,
        ∃ g ∈ Subgroup.closure (gens n w G ngen), g * toPerm n w (RT j) * g⁻¹ = s := by
  obtain ⟨hs, hr⟩ := forestK_sound hG hRT h
  refine ⟨?_, fun s hs' => ?_⟩
  · rw [List.toFinset_card_of_nodup, List.length_map, List.length_map]
    refine List.Nodup.map_on (fun x hx y hy e => ?_) (hs.imp (fun h => Nat.ne_of_lt h))
    obtain ⟨rx, hrx, rfl⟩ := List.mem_map.1 hx
    obtain ⟨ry, hry, rfl⟩ := List.mem_map.1 hy
    exact toPerm_injective (hr rx hrx).1 (hr ry hry).1 e
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs')
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hx
    exact (hr r hr').2

theorem forestK_pp {G GI RT : Nat → Nat} {ngen nr : Nat} {R : List Rec}
    (hG : ∀ k < ngen, PP n w (G k)) (hRT : ∀ j < nr, PP n w (RT j))
    (h : forestK n w G GI ngen RT nr R = true) : ∀ r ∈ R, PP n w r.1 :=
  fun r hr => ((forestK_sound hG hRT h).2 r hr).1

theorem forestK_nodup {G GI RT : Nat → Nat} {ngen nr : Nat} {R : List Rec}
    (hG : ∀ k < ngen, PP n w (G k)) (hRT : ∀ j < nr, PP n w (RT j))
    (h : forestK n w G GI ngen RT nr R = true) : (R.map Prod.fst).Nodup :=
  (forestK_sound hG hRT h).1.imp (fun h => Nat.ne_of_lt h)

theorem cpathK_sound {G : Nat → Nat} {ngen : Nat} (hG : ∀ k < ngen, PP n w (G k))
    (hinv : ∀ k < ngen, G k = pinvS n w (mask w) (G k)) :
    ∀ (ks : List Nat), (∀ c ∈ ks, c < ngen) → ∀ {x : Nat}, PP n w x →
      PP n w (cpathK n w G x ks) ∧ ∃ g ∈ Subgroup.closure (gens n w G ngen),
        g * toPerm n w x * g⁻¹ = toPerm n w (cpathK n w G x ks)
  | [], _, x, hx => ⟨hx, 1, Subgroup.one_mem _, by rw [one_mul, inv_one, mul_one]; rfl⟩
  | k :: ks, hks, x, hx => by
    have hk : k < ngen := hks k List.mem_cons_self
    have e : conjI n w G G k x = CFSG.KC.Misc.ArrEnum.conjAct n w G k x := by
      unfold conjI CFSG.KC.Misc.ArrEnum.conjAct
      rw [← hinv k hk]
    have hy : PP n w (conjI n w G G k x) := e ▸ PP_conjAct (hG k hk) hx
    obtain ⟨h1, g, hg, hge⟩ := cpathK_sound hG hinv ks (fun c hc => hks c (List.mem_cons_of_mem _ hc)) hy
    change PP n w (cpathK n w G (conjI n w G G k x) ks) ∧ _
    refine ⟨h1, g * toPerm n w (G k), Subgroup.mul_mem _ hg (gen_mem hk), ?_⟩
    change _ = toPerm n w (cpathK n w G (conjI n w G G k x) ks)
    rw [← hge, e, toPerm_conjAct (hG k hk) hx]
    group

section Count

variable {M : Type*} [Group M] [Fintype M] [DecidableEq M]

open Classical in
noncomputable def clsF (H : Subgroup M) (a : M) : Finset M :=
  Finset.univ.filter fun x => ∃ c ∈ H, x = c * a * c⁻¹

theorem mem_clsF {H : Subgroup M} {a x : M} : x ∈ clsF H a ↔ ∃ c ∈ H, x = c * a * c⁻¹ := by
  classical
  unfold clsF
  simp

theorem card_filter_comm_conj (H : Subgroup M) (a b : M) {c : M} (hc : c ∈ H) :
    ((clsF H b).filter fun y => y * (c * a * c⁻¹) = c * a * c⁻¹ * y).card =
      ((clsF H b).filter fun y => y * a = a * y).card := by
  symm
  refine Finset.card_bij (fun y _ => c * y * c⁻¹) (fun y hy => ?_) (fun y _ z _ e => ?_)
    (fun y hy => ?_)
  · rw [Finset.mem_filter, mem_clsF] at hy ⊢
    obtain ⟨⟨d, hd, rfl⟩, hya⟩ := hy
    refine ⟨⟨c * d, H.mul_mem hc hd, by group⟩, ?_⟩
    calc c * (d * b * d⁻¹) * c⁻¹ * (c * a * c⁻¹) = c * ((d * b * d⁻¹) * a) * c⁻¹ := by group
      _ = c * (a * (d * b * d⁻¹)) * c⁻¹ := by rw [hya]
      _ = c * a * c⁻¹ * (c * (d * b * d⁻¹) * c⁻¹) := by group
  · simpa using e
  · rw [Finset.mem_filter, mem_clsF] at hy
    obtain ⟨⟨d, hd, rfl⟩, hya⟩ := hy
    refine ⟨c⁻¹ * (d * b * d⁻¹) * c, ?_, by group⟩
    rw [Finset.mem_filter, mem_clsF]
    refine ⟨⟨c⁻¹ * d, H.mul_mem (H.inv_mem hc) hd, by group⟩, ?_⟩
    calc c⁻¹ * (d * b * d⁻¹) * c * a = c⁻¹ * ((d * b * d⁻¹) * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * (d * b * d⁻¹)) * c := by rw [hya]
      _ = a * (c⁻¹ * (d * b * d⁻¹) * c) := by group

theorem card_mul_card_filter_comm (H : Subgroup M) (a b : M) :
    (clsF H a).card * ((clsF H b).filter fun y => y * a = a * y).card =
      (clsF H b).card * ((clsF H a).filter fun x => x * b = b * x).card := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := clsF H a)
    (t := clsF H b) (r := fun x y => y * x = x * y)
  have h1 : ∀ x ∈ clsF H a, (Finset.bipartiteAbove (fun x y => y * x = x * y) (clsF H b) x).card =
      ((clsF H b).filter fun y => y * a = a * y).card := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := mem_clsF.1 hx
    exact card_filter_comm_conj H a b hc
  have h2 : ∀ y ∈ clsF H b, (Finset.bipartiteBelow (fun x y => y * x = x * y) (clsF H a) y).card =
      ((clsF H a).filter fun x => x * b = b * x).card := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := mem_clsF.1 hy
    have e := card_filter_comm_conj H b a hc
    unfold Finset.bipartiteBelow
    rw [← e]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ => eq_comm
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul] at h
  exact h

end Count

section Wit

variable {M : Type*} [Group M]

@[expose] def WitP (c g : M) : Prop :=
  g * (c * c) = (c * c) * g ∧ (c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧
    c * (g * c * g⁻¹) ≠ 1 ∧ c * (g * c * g⁻¹) ≠ c * c

theorem WitP.conj {c g : M} (h : WitP c g) (k : M) : WitP (k * c * k⁻¹) (k * g * k⁻¹) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ey : k * c * k⁻¹ * (k * g * k⁻¹ * (k * c * k⁻¹) * (k * g * k⁻¹)⁻¹) =
      k * (c * (g * c * g⁻¹)) * k⁻¹ := by group
  have ez : k * c * k⁻¹ * (k * c * k⁻¹) = k * (c * c) * k⁻¹ := by group
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc k * g * k⁻¹ * (k * c * k⁻¹ * (k * c * k⁻¹)) = k * (g * (c * c)) * k⁻¹ := by group
      _ = k * (c * c * g) * k⁻¹ := by rw [h1]
      _ = k * c * k⁻¹ * (k * c * k⁻¹) * (k * g * k⁻¹) := by group
  · rw [ey]
    calc k * (c * (g * c * g⁻¹)) * k⁻¹ * (k * (c * (g * c * g⁻¹)) * k⁻¹) =
        k * (c * (g * c * g⁻¹) * (c * (g * c * g⁻¹))) * k⁻¹ := by group
      _ = 1 := by rw [h2]; group
  · rw [ey]
    intro h
    apply h3
    calc c * (g * c * g⁻¹) = k⁻¹ * (k * (c * (g * c * g⁻¹)) * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  · rw [ey, ez]
    intro h
    apply h4
    calc c * (g * c * g⁻¹) = k⁻¹ * (k * (c * (g * c * g⁻¹)) * k⁻¹) * k := by group
      _ = k⁻¹ * (k * (c * c) * k⁻¹) * k := by rw [h]
      _ = c * c := by group

end Wit

theorem exists_conj_mem_of_card {M : Type*} [Group M] {G S : Subgroup M} [Finite G]
    (hSG : S ≤ G) {p k m e : ℕ} [hp : Fact p.Prime] (hS : Nat.card S = p ^ k)
    (hG : Nat.card G = p ^ k * m) (hm : ¬ p ∣ m) {c : M} (hc : c ∈ G) (hce : orderOf c = p ^ e) :
    ∃ g ∈ G, g * c * g⁻¹ ∈ S := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  have hfac : (Nat.card G).factorization p = k := by
    rw [hG, Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow hp.out, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm, Nat.add_zero]
  have hS' : Nat.card (S.subgroupOf G) = p ^ (Nat.card G).factorization p := by
    rw [hfac, ← hS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSG).toEquiv
  set P : Sylow p G := Sylow.ofCard (S.subgroupOf G) hS'
  set x' : G := ⟨c, hc⟩
  have hX : IsPGroup p (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := e) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hce])
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have h1 : x' ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply, Sylow.coe_ofCard,
    Subgroup.mem_subgroupOf] at h1
  refine ⟨(g⁻¹ : G), (g⁻¹ : G).2, ?_⟩
  simpa using h1

end CFSG.KC.O8Sq

end
