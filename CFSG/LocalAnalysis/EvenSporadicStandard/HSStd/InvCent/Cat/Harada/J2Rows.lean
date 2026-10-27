module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.One
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.FourClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Action
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.Kernel
open CFSG.ComponentClassification.M12Cover (centralizerEquiv centralizerSubgroupEquiv
  centralizerInConjEquiv)

theorem exists_centralizer_equiv {G M : Type*} [Group G] [Group M] (K : Subgroup M)
    (e : G ≃* ↥K) {t : G} {r c : M} (hc : c ∈ K) (hδ : ((e t : ↥K) : M) = c * r * c⁻¹) :
    Nonempty (↥(centralizer ({t} : Set G)) ≃* ↥(centralizerIn K r)) :=
  ⟨(centralizerEquiv e t).trans ((centralizerSubgroupEquiv K (e t)).trans
    ((MulEquiv.subgroupCongr (congrArg (centralizerIn K) hδ)).trans
      (centralizerInConjEquiv K hc r).symm))⟩

theorem orderOf_ne_four_of_orderFourClassSizes_nil {M : Type*} [Group M] {K : Subgroup M}
    (h : OrderFourClassSizes K []) : ∀ x ∈ K, orderOf x ≠ 4 := by
  obtain ⟨reps, -, hcov, -, hsz⟩ := h
  have hnil : reps = [] := List.map_eq_nil_iff.1 hsz
  intro x hx h4
  obtain ⟨r, hr, -⟩ := hcov x hx h4
  simp [hnil] at hr

theorem fewFour_of_orderFourClassSizes {M : Type*} [Group M] {K : Subgroup M} {sizes : List ℕ}
    (h : OrderFourClassSizes K sizes) : FewFour sizes.length K := by
  classical
  obtain ⟨reps, -, hcov, -, hsz⟩ := h
  refine ⟨reps.toFinset, ?_, ?_⟩
  · calc reps.toFinset.card ≤ reps.length := List.toFinset_card_le _
      _ = sizes.length := by rw [← hsz, List.length_map]
  · intro x hx h4
    obtain ⟨r, hr, c, hc, hxr⟩ := hcov x hx h4
    exact ⟨r, List.mem_toFinset.2 hr, c, hc, hxr⟩

@[expose] noncomputable def j2Rho
    {G : Type} [Group G] (S : Subgroup G) [S.Normal] (ψ : ↥S ≃* ↥P) : G →* ↥R :=
  CFSG.EvenSporadicStandard.HSStd.HL34.rho S ψ rAutEquiv

theorem j2Rho_injective
    {G : Type} [Group G] (S : Subgroup G) [S.Normal] (ψ : ↥S ≃* ↥P)
    (hcent : centralizer (S : Set G) = ⊥) : Function.Injective (j2Rho S ψ) :=
  CFSG.EvenSporadicStandard.HSStd.HL34.rho_injective S ψ rAutEquiv hcent

theorem j2Rho_bijective_of_ne_top
    {G : Type} [Group G] [Finite G] (S : Subgroup G) [S.Normal] (ψ : ↥S ≃* ↥P)
    (hcent : centralizer (S : Set G) = ⊥) (hne : S ≠ ⊤) : Function.Bijective (j2Rho S ψ) := by
  refine (j2Rho_injective S ψ hcent).bijective_of_nat_card_le ?_
  have hS : Nat.card ↥S = 604800 := by rw [Nat.card_congr ψ.toEquiv]; exact card_P
  have h1 : S.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
  have h0 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : 2 ≤ S.index := by omega
  rw [card_R, ← S.card_mul_index, hS]
  calc 1209600 = 604800 * 2 := by norm_num
    _ ≤ 604800 * S.index := Nat.mul_le_mul_left _ h2

theorem exists_equiv_of_eq_top
    {G : Type} [Group G] (S : Subgroup G) [S.Normal] (ψ : ↥S ≃* ↥P) (hS : S = ⊤) {t : G}
    (ht : orderOf t = 2) :
    ∃ r ∈ [permA, permTwoA], Nonempty (↥(centralizer ({t} : Set G)) ≃* ↥(centralizerIn P r)) := by
  let eP : G ≃* ↥P :=
    ((Subgroup.topEquiv (G := G)).symm.trans (MulEquiv.subgroupCongr hS.symm)).trans ψ
  have hu : orderOf ((eP t : ↥P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  obtain ⟨r, hr, c, hc, hδ⟩ := inner_classes.1 _ (eP t).2 hu
  exact ⟨r, hr, exists_centralizer_equiv P eP hc hδ⟩

theorem exists_equiv_of_ne_top
    {G : Type} [Group G] [Finite G] (S : Subgroup G) [S.Normal] (ψ : ↥S ≃* ↥P)
    (hcent : centralizer (S : Set G) = ⊥) (hne : S ≠ ⊤) {t : G} (ht : orderOf t = 2) :
    ∃ r ∈ [permA, permTwoA, permU],
      Nonempty (↥(centralizer ({t} : Set G)) ≃* ↥(centralizerIn R r)) := by
  let eR : G ≃* ↥R := MulEquiv.ofBijective (j2Rho S ψ) (j2Rho_bijective_of_ne_top S ψ hcent hne)
  have hu : orderOf ((eR t : ↥R) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  rcases mem_P_or_coset (eR t).2 with hP | hcos
  · obtain ⟨r, hr, c, hc, hδ⟩ := inner_classes.1 _ hP hu
    refine ⟨r, ?_, exists_centralizer_equiv R eR (P_le_R hc) hδ⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    tauto
  · obtain ⟨c, hc, hδ⟩ := outer_classes.1 _ hcos hu
    exact ⟨permU, by simp, exists_centralizer_equiv R eR (P_le_R hc) hδ⟩

theorem noZ2S5J2_holds :
    NoZ2S5J2 := by
  intro G _ _ S hSn ⟨ψ₀⟩ hcent t ht _ ⟨ζ⟩
  haveI := hSn
  let ψ : ↥S ≃* ↥P := ψ₀.trans nativeEquivP
  have h240 := card_centralizer_of_equiv ζ
  by_cases hS : S = ⊤
  · obtain ⟨r, hr, ⟨e⟩⟩ := exists_equiv_of_eq_top S ψ hS ht
    have hcard := Nat.card_congr e.toEquiv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · obtain ⟨-, -, h3⟩ := centralizerIn_P_permA
      obtain ⟨x, hx⟩ := exists_orderOf_four_z2s5
      have hz : orderOf ((e (ζ.symm x) : ↥(centralizerIn P permA)) : Equiv.Perm (Fin 315)) = 4 := by
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hx]
      exact orderOf_ne_four_of_orderFourClassSizes_nil h3 _ (e (ζ.symm x)).2 hz
    · obtain ⟨-, h2, -⟩ := centralizerIn_P_permTwoA
      omega
  · obtain ⟨r, hr, ⟨e⟩⟩ := exists_equiv_of_ne_top S ψ hcent hS ht
    have hcard := Nat.card_congr e.toEquiv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨-, h2, -⟩ := centralizerIn_R_permA
      omega
    · obtain ⟨-, h2, -⟩ := centralizerIn_R_permTwoA
      omega
    · obtain ⟨-, h2, -⟩ := centralizerIn_R_permU
      omega

theorem noTwoCfgJ2_holds :
    NoTwoCfgJ2 := by
  intro G _ _ S hSn ⟨ψ₀⟩ hcent t v J h _
  haveI := hSn
  let ψ : ↥S ≃* ↥P := ψ₀.trans nativeEquivP
  have htop : centralizer ({t} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hcent h.t_ne_one
  have h480 := h.card_centralizer htop
  by_cases hS : S = ⊤
  · obtain ⟨r, hr, ⟨e⟩⟩ := exists_equiv_of_eq_top S ψ hS h.ht
    have hcard := Nat.card_congr e.toEquiv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · obtain ⟨-, h2, -⟩ := centralizerIn_P_permA
      omega
    · obtain ⟨-, h2, -⟩ := centralizerIn_P_permTwoA
      omega
  · obtain ⟨r, hr, ⟨e⟩⟩ := exists_equiv_of_ne_top S ψ hcent hS h.ht
    have hcard := Nat.card_congr e.toEquiv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨-, -, h3⟩ := centralizerIn_R_permA
      exact h.false_of_fewFour htop e (fewFour_of_orderFourClassSizes h3)
    · obtain ⟨-, h2, -⟩ := centralizerIn_R_permTwoA
      omega
    · obtain ⟨-, h2, -⟩ := centralizerIn_R_permU
      omega

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
