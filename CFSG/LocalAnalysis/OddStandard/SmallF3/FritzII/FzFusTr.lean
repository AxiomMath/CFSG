module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY11a
public import CFSG.Quasithin.Recognition.M12AscTrans
public import Certificates.Data.FzFusPhi

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 Certificates.FzJ36 Certificates.FzFus

variable {G : Type} [Group G]

theorem fzfus_S_eq [Finite G] {t : G} {L S T₂ : Subgroup G}
    {x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G}
    (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂) :
    S = T₂ ⊓ invCent t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSU : S ≤ T₂ ⊓ invCent t := le_inf h.isT2.S_le h.ctx.le_invCent
  refine le_antisymm hSU ?_
  have hU : IsPGroup 2 (T₂ ⊓ invCent t : Subgroup G) := h.isT2.isPGroup.to_le inf_le_left
  obtain ⟨n, hn⟩ := hU.index (S.subgroupOf (T₂ ⊓ invCent t))
  have hrel : S.relIndex (T₂ ⊓ invCent t) = 2 ^ n := hn
  have hdvd : S.relIndex (T₂ ⊓ invCent t) ∣ S.relIndex (invCent t) :=
    ⟨(T₂ ⊓ invCent t).relIndex (invCent t),
      (Subgroup.relIndex_mul_relIndex S _ _ hSU inf_le_right).symm⟩
  have hn0 : n = 0 := by
    by_contra hne
    exact h.ctx.relIndex_odd (dvd_trans (dvd_pow_self 2 hne) (hrel ▸ hdvd))
  rw [hn0, pow_zero] at hrel
  exact Subgroup.relIndex_eq_one.mp hrel

theorem fzfus_relIndex_two {T₂ : Subgroup G} (π : Model →* G) (hrange : π.range = T₂)
    (φ : Model →* Z2) (hker : ∀ m, π m = 1 → φ m = 1) (hsurj : Function.Surjective φ) :
    ((φ.ker).map π).relIndex T₂ = 2 := by
  have hle : π.ker ≤ φ.ker := fun m hm =>
    MonoidHom.mem_ker.mpr (hker m (MonoidHom.mem_ker.mp hm))
  have h1 : T₂ = (⊤ : Subgroup Model).map π := by rw [← hrange, MonoidHom.range_eq_map]
  have hcard : Nat.card Z2 = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [h1, Subgroup.relIndex_map_map, sup_eq_left.mpr hle, top_sup_eq,
    Subgroup.relIndex_top_right, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
    Subgroup.card_top, hcard]

theorem fzfus_transfer [Finite G] [IsSimpleGroup G] {T₂ : Subgroup G} (hT : FzSylow T₂)
    (hcard : 2 < Nat.card G) (π : Model →* G) (hrange : π.range = T₂)
    (φ : Model →* Z2) (hker : ∀ m, π m = 1 → φ m = 1) (hsurj : Function.Surjective φ)
    {t : G} (htT : t ∈ T₂) (ht2 : t * t = 1) :
    ∃ m : Model, φ m = 1 ∧ ∃ a : G, a⁻¹ * t * a = π m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push_neg at hne
  let P : Sylow 2 G := hT.1.toSylow hT.2
  have hindex : ((φ.ker).map π).relIndex (P : Subgroup G) = 2 :=
    fzfus_relIndex_two π hrange φ hker hsurj
  have hQu : ∀ a : G, a⁻¹ * t * a ∉ (φ.ker).map π := by
    intro a ha
    obtain ⟨m, hm, hmπ⟩ := Subgroup.mem_map.mp ha
    exact hne m (MonoidHom.mem_ker.mp hm) a hmπ.symm
  obtain ⟨X₀, hnorm, hidx, htX, -⟩ :=
    CFSG.Quasithin.thompson_transfer_index_two P hindex ht2 htT hQu
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X₀ with hX | hX
  · rw [hX, Subgroup.index_bot] at hidx
    omega
  · exact htX (hX ▸ Subgroup.mem_top t)

end CFSG.OddStandard.SmallF3.FritzII
