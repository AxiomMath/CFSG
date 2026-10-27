module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocal
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv

theorem component_eq_alt_fixed {N : ℕ} {τ : Perm (Fin N)} (hτ : τ * τ = 1)
    {P : Subgroup (Perm (Fin N))} (hPA : P ≤ alternatingGroup (Fin N))
    (hPc : P ≤ centralizer ({τ} : Set (Perm (Fin N))))
    (hP : CFSG.IsComponent
      (P.subgroupOf (alternatingGroup (Fin N) ⊓ centralizer ({τ} : Set (Perm (Fin N)))))) :
    5 ≤ Fintype.card {x : Fin N // τ x = x} ∧ (∀ g ∈ P, ∀ x, τ x ≠ x → g x = x) ∧
      Nonempty (P ≃* alternatingGroup {x : Fin N // τ x = x}) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup (Perm (Fin N)) := zpowers τ with hQdef
  have hordτ : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hτ)
  have hQ : IsPGroup 2 Q := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hordτ with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  set Z := normalizer (Q : Set (Perm (Fin N))) with hZdef
  have hcZ : ∀ g : Perm (Fin N), τ * g = g * τ → g ∈ Z := by
    intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [hQdef, ← Subgroup.zpowers_le, Subgroup.zpowers_le, mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute τ g from hg) k).eq
  have hZc : ∀ y ∈ Z, τ * y = y * τ := by
    intro y hy
    have hyτ : y * τ * y⁻¹ ∈ Q := (mem_normalizer_iff.mp hy τ).mp (mem_zpowers τ)
    have hyτ' : y * τ * y⁻¹ = τ := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyτ
      obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
      · have h1 : τ ^ (2 * m) = 1 := by rw [zpow_mul, zpow_two, hτ, one_zpow]
        rw [h1] at hk
        have h2 := conj_eq_one_iff.mp hk.symm
        rw [h2, mul_one, mul_inv_cancel]
      · rw [zpow_add_one, zpow_mul, zpow_two, hτ, one_zpow, one_mul] at hk
        exact hk.symm
    calc τ * y = y * τ * y⁻¹ * y := by rw [hyτ']
      _ = y * τ := by group
  set D : Subgroup (Perm (Fin N)) :=
    alternatingGroup (Fin N) ⊓ centralizer ({τ} : Set (Perm (Fin N))) with hDdef
  have hDZ : D ≤ Z := fun x hx => hcZ x (mem_centralizer_singleton_iff.mp hx.2).symm
  set R : Subgroup Z := (alternatingGroup (Fin N)).subgroupOf Z with hRdef
  have hR : R.Normal := inferInstance
  have hDR : D.subgroupOf Z = R := by
    ext z
    rw [mem_subgroupOf, mem_subgroupOf, hDdef, mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, mem_centralizer_singleton_iff.mpr (hZc z z.2).symm⟩⟩
  let e₁ : D ≃* R := (subgroupOfEquivOfLe hDZ).symm.trans (MulEquiv.subgroupCongr hDR)
  have hPD : P ≤ D := le_inf hPA hPc
  set L₀ := P.subgroupOf D with hL₀def
  have hL₁ : CFSG.IsPComponent 2 (L₀.map e₁.toMonoidHom) :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e₁
      (CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hP)
  have hL := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_of_normal_subgroup 2 R
    (L₀.map e₁.toMonoidHom) hL₁
  set L := (L₀.map e₁.toMonoidHom).map R.subtype with hLdef
  obtain ⟨hdeg, hLeq, -⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternating.symmetric_normalizer_pComponent 2 Q hQ L hL
  have hfix : ∀ x : Fin N, x ∈ MulAction.fixedPoints Q (Fin N) ↔ τ x = x := by
    intro x
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨τ, mem_zpowers τ⟩
    · intro h q
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp q.2
      change (q : Perm (Fin N)) x = x
      rw [← hk]
      exact Perm.zpow_apply_eq_self_of_apply_eq_self h k
  let eT : ↥(MulAction.fixedPoints Q (Fin N)) ≃ {x : Fin N // τ x = x} :=
    Equiv.subtypeEquivRight hfix
  refine ⟨?_, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_congr eT]
    exact hdeg
  · intro g hg x hx
    have hgD : g ∈ D := hPD hg
    have hmem : (⟨g, hDZ hgD⟩ : Z) ∈ L :=
      Subgroup.mem_map_of_mem _
        (Subgroup.mem_map_of_mem e₁.toMonoidHom (show (⟨g, hgD⟩ : D) ∈ L₀ from hg))
    rw [hLeq] at hmem
    obtain ⟨f, -, hf⟩ := Subgroup.mem_map.mp hmem
    have hg' : g = @Equiv.Perm.ofSubtype (Fin N) (· ∈ MulAction.fixedPoints Q (Fin N))
        (Classical.decPred _) f := (congrArg Subtype.val hf).symm
    rw [hg']
    exact Equiv.Perm.ofSubtype_apply_of_not_mem f (fun h => hx ((hfix x).mp h))
  · let eL : L₀ ≃* L := (L₀.equivMapOfInjective e₁.toMonoidHom e₁.injective).trans
      ((L₀.map e₁.toMonoidHom).equivMapOfInjective R.subtype R.subtype_injective)
    let eA : L ≃* alternatingGroup (MulAction.fixedPoints Q (Fin N)) :=
      (MulEquiv.subgroupCongr hLeq).trans
        ((alternatingGroup (MulAction.fixedPoints Q (Fin N))).equivMapOfInjective _
          (CFSG.ComponentClassification.CatalogueBAlternating.fixedPointsNormalizerHom_injective
            Q)).symm
    exact ⟨((subgroupOfEquivOfLe hPD).symm.trans (eL.trans eA)).trans (Equiv.altCongrHom eT)⟩

theorem conjNormal_injective_of_centralizer_bot {X : Type} [Group X] (W : Subgroup X)
    [W.Normal] (hC : centralizer (W : Set X) = ⊥) :
    Function.Injective (MulAut.conjNormal (H := W) : X →* MulAut W) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hcent : x ∈ centralizer (W : Set X) := by
    rw [mem_centralizer_iff]
    intro w hw
    have h3 := congrArg (fun φ : MulAut W => ((φ ⟨w, hw⟩ : W) : X)) hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    calc w * x = (x * w * x⁻¹) * x := by rw [h3]
      _ = x * w := by group
  rw [hC] at hcent
  exact mem_bot.mp hcent

theorem lookup_mulAut_congr_conj {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext a
  simp [MulAut.congr_apply]

theorem lookup_exists_perm_embedding {X : Type} [Group X] (W : Subgroup X) [W.Normal]
    (hC : centralizer (W : Set X) = ⊥) {N : ℕ} (hN : 5 ≤ N) (hN6 : N ≠ 6)
    (e : W ≃* alternatingGroup (Fin N)) :
    ∃ ι : X →* Perm (Fin N), Function.Injective ι ∧
      ∀ w : W, ι (w : X) = ((e w : alternatingGroup (Fin N)) : Perm (Fin N)) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj N hN hN6
  let κ : Perm (Fin N) ≃* MulAut (alternatingGroup (Fin N)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin N))) hbij
  let ι : X →* Perm (Fin N) :=
    κ.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := W)))
  refine ⟨ι, ?_, fun w => ?_⟩
  · exact κ.symm.injective.comp ((MulAut.congr e).injective.comp
      (conjNormal_injective_of_centralizer_bot W hC))
  · apply κ.injective
    have h1 : κ (ι (w : X)) = (MulAut.congr e) (MulAut.conj w) := by
      simp [ι, MulAut.conjNormal_val]
    rw [h1, lookup_mulAut_congr_conj]
    exact (MulAut.conjNormal_val (H := alternatingGroup (Fin N)) (h := e w)).symm

theorem perm_involution_apply_apply {N : ℕ} {τ : Perm (Fin N)} (hτ : τ * τ = 1) (x : Fin N) :
    τ (τ x) = x := by
  have h := congrArg (fun f : Perm (Fin N) => f x) hτ
  simpa using h

theorem perm_involution_ne_self_of_image {N : ℕ} {τ : Perm (Fin N)} (hτ : τ * τ = 1) {a : Fin N}
    (ha : τ a ≠ a) : τ (τ a) ≠ τ a := by
  rw [perm_involution_apply_apply hτ]
  exact ha.symm

theorem exists_even_commuting_swap {N : ℕ} {τ : Perm (Fin N)} (hτ : τ * τ = 1) {a c : Fin N}
    (ha : τ a ≠ a) (hc : τ c ≠ c) (hac : c ≠ a) (hacτ : c ≠ τ a) :
    ∃ g : Perm (Fin N), g ∈ alternatingGroup (Fin N) ∧ g * τ = τ * g ∧ g ≠ 1 ∧ g ≠ τ ∧
      ∀ x, g x ≠ x → τ x ≠ x := by
  have hτ2 := perm_involution_apply_apply hτ
  have hab : a ≠ τ a := ha.symm
  have hcd : c ≠ τ c := hc.symm
  have had : a ≠ τ c := fun h => hacτ (by rw [h, hτ2])
  have hbd : τ a ≠ τ c := fun h => hac (τ.injective h).symm
  have hdisj : (swap a c).Disjoint (swap (τ a) (τ c)) := by
    apply Perm.disjoint_swap_swap
    simp [hac.symm, hab, had, hacτ, hcd, hbd]
  have h1 : τ * swap a c = swap (τ a) (τ c) * τ := mul_swap_eq_swap_mul τ a c
  have h2 : τ * swap (τ a) (τ c) = swap a c * τ := by
    rw [mul_swap_eq_swap_mul, hτ2, hτ2]
  refine ⟨swap a c * swap (τ a) (τ c), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hac.symm, Perm.sign_swap hbd]
    decide
  · calc swap a c * swap (τ a) (τ c) * τ = swap a c * (swap (τ a) (τ c) * τ) := mul_assoc _ _ _
      _ = swap a c * (τ * swap a c) := by rw [h1]
      _ = (swap a c * τ) * swap a c := (mul_assoc _ _ _).symm
      _ = (τ * swap (τ a) (τ c)) * swap a c := by rw [h2]
      _ = τ * (swap (τ a) (τ c) * swap a c) := mul_assoc _ _ _
      _ = τ * (swap a c * swap (τ a) (τ c)) := by rw [hdisj.commute.eq]
  · intro h
    have h' : (swap a c * swap (τ a) (τ c)) a = a := by rw [h]; rfl
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab had, swap_apply_left] at h'
    exact hac h'
  · intro h
    have h' : (swap a c * swap (τ a) (τ c)) a = τ a := by rw [h]
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab had, swap_apply_left] at h'
    exact hacτ h'
  · intro x hx hτx
    apply hx
    have hxa : x ≠ a := fun h => ha (by rw [← h]; exact hτx)
    have hxb : x ≠ τ a := fun h => perm_involution_ne_self_of_image hτ ha (by rw [← h]; exact hτx)
    have hxc : x ≠ c := fun h => hc (by rw [← h]; exact hτx)
    have hxd : x ≠ τ c := fun h => perm_involution_ne_self_of_image hτ hc (by rw [← h]; exact hτx)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxb hxd, swap_apply_of_ne_of_ne hxa hxc]

theorem eq_swap_of_unique_cycle {N : ℕ} {τ : Perm (Fin N)} (hτ : τ * τ = 1) {a : Fin N}
    (ha : τ a ≠ a) (h : ∀ c, τ c ≠ c → c = a ∨ c = τ a) : τ = swap a (τ a) := by
  ext x
  by_cases hx : τ x = x
  · have hxa : x ≠ a := fun h' => ha (by rw [← h']; exact hx)
    have hxb : x ≠ τ a := fun h' => perm_involution_ne_self_of_image hτ ha (by rw [← h']; exact hx)
    rw [hx, swap_apply_of_ne_of_ne hxa hxb]
  · rcases h x hx with h' | h'
    · rw [h', swap_apply_left]
    · rw [h', perm_involution_apply_apply hτ, swap_apply_right]

end CFSG.OddStandard.AltStdSec
