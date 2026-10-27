module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAClose3

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools

section SubcaseI

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {F : Type} [Field F]
  [Finite F] [CharP F 2] {W S₁ S₀ W₀ : Subgroup G} {ι : G → F × F} {κ : G → F}
  {φ : G → RingAut F} (S : SylowA d W S₁ S₀ W₀ ι κ φ)

include S

namespace SylowA

@[expose] noncomputable def φHom : ↥S₁ →* RingAut F :=
  MonoidHom.mk' (fun x : S₁ => φ x) (fun x y => S.φ_mul x x.2 y y.2)

theorem φHom_apply (x : S₁) : S.φHom x = φ x := rfl

theorem subcaseI [Finite G]
    (h : Hyp G A) (hS : ¬ 2 ∣ S₁.index) : False := by
  have C : CloseData S S₁ S.φHom 1 :=
    { isPGroup := S.sylow_S₁.isPGroup
      not_two_dvd_index := hS
      S₁_le := le_rfl
      norm_S₀ := fun x hx s => ⟨S.S₀_normal x hx s, fun h' => by
        have := S.S₀_normal x⁻¹ (S₁.inv_mem hx) _ h'
        simpa [mul_assoc] using this⟩
      mem_S₀_iff := fun x => by
        rw [φHom_apply]
        exact ⟨fun hx => ⟨(S.φ_eq_one_iff x x.2).2 hx, rfl⟩,
          fun hx => (S.φ_eq_one_iff x x.2).1 hx.1⟩
      ε_eq_one := fun _ _ => rfl
      ext := fun _ _ _ hε => absurd rfl hε }
  exact C.false h

end SylowA

end SubcaseI

end CFSG.OddStandard.Seitz77
