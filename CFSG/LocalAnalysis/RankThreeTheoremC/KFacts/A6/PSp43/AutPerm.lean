module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.Rigid
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.Transport
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.ThreeC

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

open CFSG.Open CFSG.GH74.Exceptional CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup

theorem card_P_inf_centralizer (x : P) :
    Nat.card ↥(P ⊓ centralizer ({(x : Equiv.Perm (Fin 45))} : Set (Equiv.Perm (Fin 45)))) =
      Nat.card (centralizer ({x} : Set P)) := by
  rw [← Subgroup.card_map_of_injective P.subtype_injective,
    map_centralizer_singleton P.subtype_injective, P.range_subtype]
  rfl

theorem card_centralizer_mulAut {G : Type*} [Group G] (α : MulAut G) (x : G) :
    Nat.card (centralizer ({α x} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  have hinj : Function.Injective α.toMonoidHom := fun a b hab => α.injective hab
  have h := map_centralizer_singleton hinj x
  have : α.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.2 α.surjective
  rw [this, top_inf_eq] at h
  have h2 := Subgroup.card_map_of_injective (K := centralizer ({x} : Set G)) hinj
  rw [h] at h2
  exact h2

theorem card_centralizer_tau (j : Fin 45) :
    Nat.card ↥(P ⊓ centralizer ({tauPerm j} : Set (Equiv.Perm (Fin 45)))) = 576 := by
  obtain ⟨c, hcP, hc0⟩ := exists_mem_P_apply_zero j
  have h := conj_tauPerm hcP 0
  rw [hc0] at h
  rw [← h, card_centralizer_conj hcP, card_centralizer_tau_zero]

theorem tauTab_ne : (List.range 45).all (fun j => tauTab.getD j [] != tid) = true := by
  decide +kernel

theorem tauPerm_ne_one (j : Fin 45) : tauPerm j ≠ 1 := by
  have h := List.all_eq_true.1 tauTab_ne j.1 (List.mem_range.2 j.2)
  rw [bne_iff_ne] at h
  exact rep_ne (rep_tauPerm j) rep_one h

abbrev tauP (j : Fin 45) : P := ⟨tauPerm j, tauPerm_mem j⟩

theorem exists_tau_eq (α : MulAut P) (j : Fin 45) :
    ∃ k : Fin 45, ((α (tauP j) : P) : Equiv.Perm (Fin 45)) = tauPerm k := by
  set t : P := α (tauP j)
  have ht2 : (t : Equiv.Perm (Fin 45)) ^ 2 = 1 := by
    have : t ^ 2 = 1 := by
      rw [← map_pow]
      have : tauP j ^ 2 = 1 := Subtype.ext (by simp [pow_two, tauPerm_mul_self])
      rw [this, map_one]
    exact congrArg Subtype.val this
  have ht1 : (t : Equiv.Perm (Fin 45)) ≠ 1 := by
    intro h
    have : t = 1 := Subtype.ext h
    have h2 : tauP j = 1 := α.injective (this.trans (map_one α).symm)
    exact tauPerm_ne_one j (congrArg Subtype.val h2)
  have hc : Nat.card ↥(P ⊓ centralizer ({(t : Equiv.Perm (Fin 45))} :
      Set (Equiv.Perm (Fin 45)))) = 576 := by
    rw [card_P_inf_centralizer, card_centralizer_mulAut, ← card_P_inf_centralizer]
    exact card_centralizer_tau j
  obtain ⟨g, hgP, hg⟩ := exists_conj_tau_zero t.2 ht2 ht1 hc
  exact ⟨g 0, by rw [hg, conj_tauPerm hgP]⟩

@[expose] noncomputable def autFun (α : MulAut P) (j : Fin 45) : Fin 45 :=
  Classical.choose (exists_tau_eq α j)

theorem autFun_spec (α : MulAut P) (j : Fin 45) :
    ((α (tauP j) : P) : Equiv.Perm (Fin 45)) = tauPerm (autFun α j) :=
  Classical.choose_spec (exists_tau_eq α j)

theorem autFun_spec' (α : MulAut P) (j : Fin 45) : α (tauP j) = tauP (autFun α j) :=
  Subtype.ext (autFun_spec α j)

theorem tauP_injective : Function.Injective tauP := fun i j h =>
  tauPerm_injective (congrArg Subtype.val h)

theorem autFun_mul (α β : MulAut P) (j : Fin 45) :
    autFun (α * β) j = autFun α (autFun β j) := by
  apply tauP_injective
  rw [← autFun_spec', MulAut.mul_apply, autFun_spec', autFun_spec']

theorem autFun_one (j : Fin 45) : autFun 1 j = j := by
  apply tauP_injective
  rw [← autFun_spec']
  rfl

@[expose] noncomputable def autPerm : MulAut P →* Equiv.Perm (Fin 45) where
  toFun α :=
    { toFun := autFun α
      invFun := autFun α⁻¹
      left_inv := fun j => by rw [← autFun_mul, inv_mul_cancel, autFun_one]
      right_inv := fun j => by rw [← autFun_mul, mul_inv_cancel, autFun_one] }
  map_one' := Equiv.ext autFun_one
  map_mul' α β := Equiv.ext fun j => autFun_mul α β j

theorem autPerm_spec (α : MulAut P) (j : Fin 45) :
    ((α (tauP j) : P) : Equiv.Perm (Fin 45)) = tauPerm (autPerm α j) :=
  autFun_spec α j

theorem tau_conj (j m : Fin 45) : tauPerm j * tauPerm m * tauPerm j = tauPerm (tauPerm j m) := by
  have h := conj_tauPerm (tauPerm_mem j) m
  rwa [inv_eq_of_mul_eq_one_right (tauPerm_mul_self j)] at h

theorem isEquivariant_autPerm (α : MulAut P) : IsEquivariant (autPerm α) := by
  intro j
  set π := autPerm α
  have key : ∀ m, π (tauPerm j m) = tauPerm (π j) (π m) := by
    intro m
    have h1 : tauP j * tauP m * tauP j = tauP (tauPerm j m) := Subtype.ext (tau_conj j m)
    have h2 := congrArg α h1
    rw [map_mul, map_mul, autFun_spec', autFun_spec', autFun_spec'] at h2
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul] at h3
    rw [tau_conj] at h3
    exact (tauPerm_injective h3).symm
  ext k
  simp only [Equiv.Perm.mul_apply]
  have := key (π⁻¹ k)
  rw [show π (π⁻¹ k) = k by simp] at this
  rw [this]

theorem autPerm_conj (p : P) : autPerm (MulAut.conj p) = (p : Equiv.Perm (Fin 45)) := by
  ext j
  have h := autPerm_spec (MulAut.conj p) j
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
  rw [conj_tauPerm p.2] at h
  exact congrArg Fin.val (tauPerm_injective h).symm

theorem autPerm_injective : Function.Injective autPerm := by
  intro α β h
  have hgen : ∀ j, α (tauP j) = β (tauP j) := by
    intro j
    rw [autFun_spec', autFun_spec']
    congr 1
    exact congrArg (fun σ : Equiv.Perm (Fin 45) => σ j) h
  have htop : Subgroup.closure ((Subtype.val : P → Equiv.Perm (Fin 45)) ⁻¹' Set.range tauPerm) =
      ⊤ := Subgroup.closure_closure_coe_preimage
  apply MulEquiv.ext
  intro x
  have hx : x ∈ Subgroup.closure ((Subtype.val : P → Equiv.Perm (Fin 45)) ⁻¹' Set.range tauPerm) :=
    htop ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj⟩ := hy
    have : y = tauP j := Subtype.ext hj.symm
    rw [this, hgen]
  | one => rw [map_one, map_one]
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]
  | inv y _ hy => rw [map_inv, map_inv, hy]

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43
