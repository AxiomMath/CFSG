module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAClose8
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAClose4

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

section Main

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {F : Type} [Field F]
  [Finite F] [CharP F 2] {W S₁ S₀ W₀ : Subgroup G} {ι : G → F × F} {κ : G → F}
  {φ : G → RingAut F} (S : SylowA d W S₁ S₀ W₀ ι κ φ)

include S

namespace SylowA

theorem subcaseII
    (h : Hyp G A) {T : Subgroup G} (hTp : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hST : S₁ ≤ T) (hne : S₁ ≠ T) : False := by
  obtain ⟨δ, hδT, hδN, hδnot, hδsq⟩ := exists_normalizing_sq_mem hTp hST hne
  have D : Delta S₁ T δ := ⟨hδT, hδN, hδnot, hδsq⟩
  have hle : conjSub δ W ≤ S₀ := S.conjSub_le_S₀ D
  obtain ⟨hinf, hκ⟩ := S.inf_conjSub_eq_W₀ hTp hST D
  obtain ⟨hab, hsq⟩ := S.elem_conjSub (δ := δ)
  obtain ⟨e, he1, he2, he3⟩ := S.exists_equiv_unip_of_split hle
    (isElemAbelian_of_forall_two hab hsq) hinf hκ
  have E : SplitEq W S₀ κ δ e := ⟨he1, he2, he3⟩
  have hhat : hat D = T := S.hat_eq hTp hST hle hκ D hinf E
  let ρ := conjAutHom e (hat D) (S.hat_norm_S₀ D hle hκ)
  have C : CloseData S (hat D) (fieldHom.comp ρ) (swapHom.comp ρ) :=
    { isPGroup := by rw [hhat]; exact hTp
      not_two_dvd_index := by rw [hhat]; exact hTidx
      S₁_le := S₁_le_hat D
      norm_S₀ := S.hat_norm_S₀ D hle hκ
      mem_S₀_iff := fun x => S.mem_S₀_iff_rho hle hκ D E x
      ε_eq_one := fun x hx =>
        (swapHom_eq_one_iff _).2 (S.autSwap_rho_of_mem_S₁ hle hκ D E x hx)
      ext := fun y hy2 hψ hε => S.card_inf_centralizer_le_of_rho hle hκ D y hy2 hψ hε }
  exact C.false h

theorem false
    (h : Hyp G A) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hS₁Q⟩ := S.sylow_S₁.isPGroup.exists_le_sylow
  have hTp : IsPGroup 2 (Q : Subgroup G) := Q.isPGroup'
  have hTidx : ¬ 2 ∣ (Q : Subgroup G).index := Q.not_dvd_index
  by_cases hTS : S₁ = (Q : Subgroup G)
  · rw [← hTS] at hTidx
    exact S.subcaseI h hTidx
  · exact S.subcaseII h hTp hTidx hS₁Q hTS

end SylowA

end Main

end CFSG.OddStandard.Seitz77
