module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Pocket
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrComp

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem l34g_x_comm_mul_central_left {H : Type} [Group H] {x y z : H}
    (hz : z ∈ Subgroup.center H) : ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have hzy : y * z = z * y := Subgroup.mem_center_iff.1 hz y
  calc ⁅x * z, y⁆ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by
        rw [commutatorElement_def]; group
    _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [hzy]
    _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group

private theorem l34g_x_comm_mul_central_right {H : Type} [Group H] {x y z : H}
    (hz : z ∈ Subgroup.center H) : ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have hzx : z * x⁻¹ = x⁻¹ * z := (Subgroup.mem_center_iff.1 hz x⁻¹).symm
  calc ⁅x, y * z⁆ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by
        rw [commutatorElement_def]; group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [hzx]
    _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group

theorem l34g_x_isFStarGroup_of_cover {P P' : Type} [Group P] [Finite P] [Group P'] [Finite P']
    {φ : P →* P'} (h : OddCentralCover φ) (hq : CFSG.IsQuasisimple P) (hF : IsFStarGroup P') :
    IsFStarGroup P := by
  let e := sec63PT_oddCoreQuotientEquiv φ h.surjective h.odd_card_ker
  unfold IsFStarGroup IsFGroup at hF ⊢
  rcases hF with ⟨-, hq'⟩ | ⟨-, hstar⟩
  · refine Or.inl ⟨hq, ?_⟩
    rcases hq' with h' | h'
    · exact Or.inl (smallF3OmegaQuotient_of_mulEquiv e.symm h')
    · exact Or.inr (isTwoU43_of_mulEquiv e.symm h')
  · refine Or.inr ⟨hq, ?_⟩
    rcases hstar with h' | h' | h' | h'
    · exact Or.inl (LieModel.of_mulEquiv e.symm h')
    · exact Or.inr (Or.inl (LieModel.of_mulEquiv e.symm h'))
    · exact Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e.symm h')))
    · exact Or.inr (Or.inr (Or.inr (LieModel.of_mulEquiv e.symm h')))

theorem l34g_x_inFStar_coverDerived {A P : Type} [Group A] [Finite A] [Group P] [Finite P]
    {ρ : A →* P} (h : OddCentralCover ρ) {X : Subgroup P} (hX : InFStar X) :
    InFStar (coverDerived ρ X) := by
  have hq : CFSG.IsQuasisimple ↥X := inFStar_isQuasisimple hX
  exact l34g_x_isFStarGroup_of_cover (h.oddCentralCover_coverDerivedHom hq)
    (h.isQuasisimple_coverDerived hq) hX

theorem l34g_x_inFStar_map_inj {X : Type} [Group X] (f : X →* G) (hf : Function.Injective f)
    {J₀ : Subgroup X} (h : InFStar J₀) : InFStar (J₀.map f) := by
  exact isFStarGroup_of_mulEquiv (Subgroup.equivMapOfInjective J₀ f hf) h

theorem l34g_x_isComponentIn_coverDerived_fix {A P : Type} [Group A] [Group P] {ρ : A →* P}
    (h : OddCentralCover ρ) {σ : MulAut A} {α : MulAut P} (hρσ : ∀ a, ρ (σ a) = α (ρ a))
    {X : Subgroup P} (hX : IsComponentIn X (fixSub α)) :
    IsComponentIn (coverDerived ρ X) (fixSub σ) := by
  have hEfix : ∀ a ∈ X.comap ρ, ρ (σ a) = ρ a := by
    intro a ha
    rw [hρσ a, mem_fixSub_iff.mp (hX.1 (Subgroup.mem_comap.mp ha))]
  have hzc : ∀ a ∈ X.comap ρ, a⁻¹ * σ a ∈ center A := by
    intro a ha
    apply h.ker_le_center
    rw [MonoidHom.mem_ker, map_mul, map_inv, hEfix a ha, inv_mul_cancel]
  have hcomm : ∀ a ∈ X.comap ρ, ∀ b ∈ X.comap ρ, σ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a ha b hb
    have e1 : σ a = a * (a⁻¹ * σ a) := by group
    have e2 : σ b = b * (b⁻¹ * σ b) := by group
    rw [map_commutatorElement, e1, e2,
      l34g_x_comm_mul_central_left (hzc a ha), l34g_x_comm_mul_central_right (hzc b hb)]
  have hfixE : commutator ↥(X.comap ρ) ≤ (fixSub σ).comap (X.comap ρ).subtype := by
    rw [show commutator ↥(X.comap ρ) = ⁅(⊤ : Subgroup ↥(X.comap ρ)), ⊤⁆ from rfl,
      Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_comap, mem_fixSub_iff, map_commutatorElement]
    exact hcomm (a : A) a.2 (b : A) b.2
  have hleS : coverDerived ρ X ≤ fixSub σ := by
    rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_comap.mp (hfixE hc)
  have hq : IsQuasisimple ↥(coverDerived ρ X) := h.isQuasisimple_coverDerived hX.isQuasisimple
  have hq' : IsQuasisimple ↥((coverDerived ρ X).subgroupOf (fixSub σ)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hleS).symm hq
  have h2 : (X.subgroupOf (fixSub α)).comap (fixHom ρ σ α hρσ) =
      (X.comap ρ).subgroupOf (fixSub σ) := by
    ext c
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_fixHom]
  have hsn : ((X.comap ρ).subgroupOf (fixSub σ)).IsSubnormal := by
    rw [← h2]
    exact hX.2.2.comap (fixHom ρ σ α hρσ)
  have hleinf : coverDerived ρ X ≤ X.comap ρ ⊓ fixSub σ :=
    le_inf (coverDerived_le X) hleS
  have hnorm : ∀ k ∈ X.comap ρ ⊓ fixSub σ, ∀ x ∈ coverDerived ρ X,
      k * x * k⁻¹ ∈ coverDerived ρ X :=
    fun k hk x hx => conj_mem_coverDerived X (Subgroup.mem_inf.mp hk).1 hx
  have hK : ((X.comap ρ ⊓ fixSub σ).subgroupOf (fixSub σ)).IsSubnormal := by
    rwa [Subgroup.inf_subgroupOf_right]
  exact ⟨hleS, hq', isSubnormal_subgroupOf_of_normal_le hleinf inf_le_right hnorm hK⟩

theorem l34g_x_lift_fixed_involution {A P : Type} [Group A] [Group P] {ρ : A →* P}
    (h : OddCentralCover ρ) {σ : MulAut A} {α : MulAut P} (hσ : σ * σ = 1)
    (hρσ : ∀ a, ρ (σ a) = α (ρ a)) {e : P} (he : e * e = 1) (hαe : α e = e) :
    ∃ a : A, a * a = 1 ∧ σ a = a ∧ ρ a = e := by
  obtain ⟨a₀, ha₀⟩ := h.fixHom_surjective hσ hρσ ⟨e, mem_fixSub_iff.mpr hαe⟩
  have hρa₀ : ρ (a₀ : A) = e := by
    have h1 := congrArg (fun x : ↥(fixSub α) => (x : P)) ha₀
    rw [coe_fixHom] at h1
    exact h1
  have hpow := h.pow_card_ker (a := (a₀ : A)) (by rw [hρa₀]; exact he)
  exact ⟨(a₀ : A) ^ Nat.card ρ.ker, hpow.1,
    by rw [map_pow, show σ (a₀ : A) = (a₀ : A) from a₀.2], hpow.2.trans hρa₀⟩

end CFSG.OddStandard.SmallF3.Omega
