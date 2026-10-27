module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detection
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

theorem wordProd_smul_eq_foldr (τ : Tag) (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd ω • v = ω.foldr (reflect τ) v := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul]
    rfl

section Certs


theorem pinnedX_mem_of_word_pairing {τ : Tag} {K : Type} [Field K]
    {S : Set (Fin τ.rank → ℤ)} (ω : List (Fin τ.rank)) (i : Fin τ.rank)
    (hγ : (coxeterSystem τ).wordProd ω • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ S)
    (hγ' : -((coxeterSystem τ).wordProd ω • (Pi.single i 1 : Fin τ.rank → ℤ)) ∈ S)
    {H : Subgroup (ModGL τ K)} (hX : rootSpan τ K S ≤ H) {β β' : Fin τ.rank → ℤ}
    (hβ' : IsRoot τ β') (hv : (coxeterSystem τ).wordProd ω • β' = β) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hp : ∑ j, τ.cartan i j * β' j = ε) {c : K} (hc : c ≠ 0)
    (hm : pinnedX τ K β c ∈ H) (e : K) : pinnedX τ K β e ∈ H := by
  by_cases he : e = 0
  · subst he
    rw [pinnedX_zero]
    exact H.one_mem
  set N : ModGL τ K := (ω.map fun i => weylElt τ K i 1).prod with hN
  have hx : ∀ c, N * xUnit τ K i c * N⁻¹ ∈ H := by
    intro c
    obtain ⟨ε, -, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K ω (IsRoot.basis (τ := τ) i)
    rw [← pinnedX_single, h]
    exact hX (pinnedX_mem_rootSpan hγ _)
  have hy : ∀ c, N * yUnit τ K i c * N⁻¹ ∈ H := by
    intro c
    obtain ⟨ε, -, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K ω (isRoot_neg_single τ i)
    rw [← pinnedX_neg_single, h, smul_neg]
    exact hX (pinnedX_mem_rootSpan hγ' _)
  have conj3 : ∀ a b : ModGL τ K, N * a * N⁻¹ ∈ H → N * b * N⁻¹ ∈ H →
      N * (a * b * a) * N⁻¹ ∈ H := fun a b ha hb => by
    have : N * (a * b * a) * N⁻¹ = (N * a * N⁻¹) * (N * b * N⁻¹) * (N * a * N⁻¹) := by group
    rw [this]
    exact H.mul_mem (H.mul_mem ha hb) ha
  have hw : ∀ s : Kˣ, N * weylElt τ K i s * N⁻¹ ∈ H := by
    intro s
    rw [weylElt_eq_xUnit_mul]
    exact conj3 _ _ (hx _) (hy _)
  set u : Kˣ := Units.mk0 (e / c) (div_ne_zero he hc) with hu
  set t : Kˣ := u ^ ε with ht
  have hD : N * torusElt τ K i t * N⁻¹ ∈ H := by
    show N * (weylElt τ K i t * weylElt τ K i (-1)) * N⁻¹ ∈ H
    have : N * (weylElt τ K i t * weylElt τ K i (-1)) * N⁻¹ =
        (N * weylElt τ K i t * N⁻¹) * (N * weylElt τ K i (-1) * N⁻¹) := by group
    rw [this]
    exact H.mul_mem (hw t) (hw (-1))
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K ω hβ'
  rw [hv] at h₂
  have h3 : pinnedX τ K β c = N * pinnedX τ K β' (ε₂ * c) * N⁻¹ := by
    rw [h₂, ← mul_assoc, hε₂, one_mul]
  have hd : ∀ s : K, torusElt τ K i t * pinnedX τ K β' s * (torusElt τ K i t)⁻¹ =
      pinnedX τ K β' ((u : K) * s) := by
    intro s
    have htu : t ^ ε = u := by
      rcases hε with rfl | rfl <;> simp [ht]
    rw [torusElt_eq_rootDiagUnit, rootDiagUnit_conj_pinnedX _ hβ', rootChar_cartan_zpow, hp,
      htu]
  have hkey : (N * torusElt τ K i t * N⁻¹) * pinnedX τ K β c * (N * torusElt τ K i t * N⁻¹)⁻¹ =
      pinnedX τ K β e := by
    calc (N * torusElt τ K i t * N⁻¹) * pinnedX τ K β c * (N * torusElt τ K i t * N⁻¹)⁻¹
        = N * (torusElt τ K i t * pinnedX τ K β' (ε₂ * c) * (torusElt τ K i t)⁻¹) * N⁻¹ := by
          rw [h3]; group
      _ = N * pinnedX τ K β' ((u : K) * (ε₂ * c)) * N⁻¹ := by rw [hd]
      _ = pinnedX τ K β (ε₂ * ((u : K) * (ε₂ * c))) := h₂ _
      _ = pinnedX τ K β e := by
          congr 1
          have hue : ((u : Kˣ) : K) * c = e := by simp [hu, div_mul_cancel₀ _ hc]
          linear_combination ((u : K) * c) * hε₂ + hue
  rw [← hkey]
  exact H.mul_mem (H.mul_mem hD hm) (H.inv_mem hD)

end Certs

@[expose] def f4Word : List (Fin Tag.F4.rank) := [1, 2, 1, 0, 3, 2]

theorem f4Word_apply : (f4Word.foldr (reflect .F4) (Pi.single 1 1)) 1 = 3 := by
  decide +kernel

theorem f4_unit_table : ∀ β ∈ rootFinset .F4, β 1 % 3 ≠ 0 →
    (∃ k : Fin Tag.F4.rank, k ≠ 1 ∧ (∑ j, Tag.F4.cartan k j * β j) ∈ ({1, -1} : Finset ℤ)) ∨
    (∑ j, Tag.F4.cartan 1 j * (f4Word.reverse.foldr (reflect .F4) β) j) ∈
      ({1, -1} : Finset ℤ) := by
  decide +kernel

section Certs2


theorem rootSubgroup_le_of_pinnedX_mem_F4 {K : Type} [Field K]
    {H : Subgroup (ModGL Tag.F4 K)} (hX : rootSpan Tag.F4 K (cosetRoots Tag.F4 1 3) ≤ H)
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hβS : β ∉ cosetRoots Tag.F4 1 3)
    {c : K} (hc : c ≠ 0) (hm : pinnedX Tag.F4 K β c ∈ H) : rootSubgroup Tag.F4 K β ≤ H := by
  have hβ3 : β 1 % 3 ≠ 0 := fun h0 =>
    hβS ⟨hβ, by exact_mod_cast Int.dvd_of_emod_eq_zero h0⟩
  intro g hg
  obtain ⟨e, rfl⟩ := mem_rootSubgroup.1 hg
  rcases f4_unit_table β (mem_rootFinset.2 hβ) hβ3 with ⟨k, hk, hpair⟩ | hpair
  · have hsingle : (Pi.single k 1 : Fin Tag.F4.rank → ℤ) 1 = 0 := by simp [Ne.symm hk]
    have h1 : (Pi.single k 1 : Fin Tag.F4.rank → ℤ) ∈ cosetRoots .F4 1 3 :=
      ⟨IsRoot.basis k, by rw [hsingle]; exact dvd_zero _⟩
    have h2 : (-Pi.single k 1 : Fin Tag.F4.rank → ℤ) ∈ cosetRoots .F4 1 3 :=
      ⟨isRoot_neg_single _ k, by rw [Pi.neg_apply, hsingle, neg_zero]; exact dvd_zero _⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    exact pinnedX_mem_of_pairing h1 h2 hX hβ hpair rfl hc hm e
  · have hγ : (coxeterSystem Tag.F4).wordProd f4Word • (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) ∈
        cosetRoots .F4 1 3 :=
      ⟨IsRoot.smul (IsRoot.basis 1) _, by
        rw [wordProd_smul_eq_foldr, f4Word_apply]; exact dvd_refl _⟩
    have hγ' : -((coxeterSystem Tag.F4).wordProd f4Word • (Pi.single 1 1 : Fin Tag.F4.rank → ℤ)) ∈
        cosetRoots .F4 1 3 :=
      ⟨by rw [← smul_neg]; exact IsRoot.smul (isRoot_neg_single _ 1) _, by
        rw [Pi.neg_apply, wordProd_smul_eq_foldr, f4Word_apply]
        exact (dvd_neg.2 (dvd_refl _))⟩
    have hrev : (coxeterSystem Tag.F4).wordProd f4Word.reverse • β =
        f4Word.reverse.foldr (reflect .F4) β := wordProd_smul_eq_foldr _ _ _
    have hv : (coxeterSystem Tag.F4).wordProd f4Word •
        ((coxeterSystem Tag.F4).wordProd f4Word.reverse • β) = β := by
      rw [CoxeterSystem.wordProd_reverse, smul_inv_smul]
    rw [← hrev] at hpair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    exact pinnedX_mem_of_word_pairing f4Word 1 hγ hγ' hX (IsRoot.smul hβ _) hv hpair rfl hc hm e

theorem exists_rootSubgroup_le_of_detection_F4 (K : Type) [Field K]
    (hD : FrameDetection .F4 K (cosetRoots .F4 1 3)) {H : Subgroup (ModGL Tag.F4 K)}
    (hH : H ≤ adjointGroup Tag.F4 K) (hX : rootSpan Tag.F4 K (cosetRoots Tag.F4 1 3) ≤ H)
    (hN : ¬ H ≤ Subgroup.normalizer (rootSpan Tag.F4 K (cosetRoots Tag.F4 1 3) :
      Set (ModGL Tag.F4 K))) :
    ∃ β, IsRoot Tag.F4 β ∧ β ∉ cosetRoots Tag.F4 1 3 ∧ rootSubgroup Tag.F4 K β ≤ H := by
  obtain ⟨β, hβ, hβS, c, hc, hm⟩ := hD H hH hX hN
  exact ⟨β, hβ, hβS, rootSubgroup_le_of_pinnedX_mem_F4 hX hβ hβS hc hm⟩

end Certs2

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
