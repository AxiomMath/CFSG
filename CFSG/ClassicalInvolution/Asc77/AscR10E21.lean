module

public import CFSG.ClassicalInvolution.Asc77.AscR10E1
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutLift
public import CFSG.ClassicalInvolution.RouteD.GapsOrthExcl

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic (Commutes conjSub)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open CFSG.ClassicalInvolution.Asc77.T3CII (GenSq genSq_top_sl2 eq_of_map_eq_of_genSq)
open scoped commutatorElement MatrixGroups



theorem genSq_B12_lin {p : ℕ} {F : Type} [Field F] [CharP F p] (hp3 : p = 3) :
    GenSq (B12 F) := by
  have : CharP F 3 := hp3 ▸ inferInstance
  rw [B12, MonoidHom.range_eq_map]
  exact genSq_top_sl2.map _

theorem genSq_B23_lin {p : ℕ} {F : Type} [Field F] [CharP F p] (hp3 : p = 3) :
    GenSq (B23 F) := by
  have : CharP F 3 := hp3 ▸ inferInstance
  rw [B23, MonoidHom.range_eq_map]
  exact genSq_top_sl2.map _

variable {F : Type} [Field F] {KY X : Type} [Group KY] [Group X]

theorem exists_lin_of_map3 {p : ℕ} [Fact p.Prime] [Finite F] [CharP F p] (hp3 : p = 3)
    [Finite KY] (hC : ¬ p ∣ Nat.card (Subgroup.center KY)) (ψ : KY →* X)
    (hker : ψ.ker ≤ Subgroup.center KY) (hker2 : ∀ x ∈ ψ.ker, x * x = 1)
    {R₁ R₂ : Subgroup KY} (hR₁ : GenSq R₁) (hR₂ : GenSq R₂) (h : ∃ W, LinearBlockStandardPair F W
        (R₁.map ψ) (R₂.map ψ)) :
    ∃ W, LinearBlockStandardPair F W R₁ R₂ := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨θ, hrange, hθ, hU, hV⟩ := WeakCT.pair_normalize hW
  have hWsup := linear_eq_sup hW
  have hle : θ.range ≤ ψ.range := by
    rw [hrange, hWsup]
    exact sup_le (Subgroup.map_le_range ψ R₁) (Subgroup.map_le_range ψ R₂)
  let θ' : SL(3, F) →* ψ.range := θ.codRestrict ψ.range fun s => hle ⟨s, rfl⟩
  have hπ : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hπker : ψ.rangeRestrict.ker ≤ Subgroup.center KY := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hπC : ¬ p ∣ Nat.card ψ.rangeRestrict.ker := fun hd =>
    hC (hd.trans (Subgroup.card_dvd_of_le hπker))
  obtain ⟨α, hα, -⟩ := ModelFacts.LinearAut.sl_existsUnique_lift (n := 3) (K := F) (p := p)
    (by norm_num) hπ hπker hπC θ'
  have hαψ : ∀ s, ψ (α s) = θ s := fun s => congrArg Subtype.val (DFunLike.congr_fun hα s)
  have hψα : ψ.comp α = θ := MonoidHom.ext hαψ
  have hp₁ := (genSq_B12_lin (F := F) hp3).map α
  have hp₂ := (genSq_B23_lin (F := F) hp3).map α
  have hR₁' : (B12 F).map α = R₁ :=
    eq_of_map_eq_of_genSq ψ hker hker2 hp₁ hR₁ (by rw [Subgroup.map_map, hψα, hU])
  have hR₂' : (B23 F).map α = R₂ :=
    eq_of_map_eq_of_genSq ψ hker hker2 hp₂ hR₂ (by rw [Subgroup.map_map, hψα, hV])
  have hid : (MulAut.conj (1 : SL(3, F))⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext; simp
  refine ⟨α.range, α, 1, rfl, fun s hs => hθ ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [MonoidHom.mem_ker, ← hαψ, hs, map_one]
  · rw [hid, Subgroup.map_id, hR₁']
  · rw [hid, Subgroup.map_id, hR₂']

end CFSG.ClassicalInvolution.RouteD.Gaps
