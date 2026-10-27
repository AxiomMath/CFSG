module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

@[expose] def NoPNorm {Y : Type} [Group Y] (α : MulAut Y) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ X : Subgroup Y, IsPGroup p ↥X → X ≠ ⊥ →
    fixSub α ≤ normalizer (X : Set Y) → False

@[expose] def InvolFactS {Y : Type} [Group Y] (α : MulAut Y) : Prop :=
  InvolFact α ∨ NoPNorm α

structure CellFactsS (F : (Y : Type) → [Group Y] → Prop) : Prop where
  iso : ∀ {Y Y' : Type} [Group Y] [Group Y'], Y ≃* Y' → F Y → F Y'
  mult : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → IsPGroup 2 ↥(center L) →
    F (L ⧸ center L) → center L = ⊥
  outAbel : ∀ (Y : Type) [Group Y] [Finite Y], F Y → OutAbelian Y
  invol : ∀ (Y : Type) [Group Y] [Finite Y], F Y → ∀ α : MulAut Y, α * α = 1 → α ≠ 1 → InvolFactS α

theorem cell87_of_factsS {F : (Y : Type) → [Group Y] → Prop}
    (hF : CellFactsS F) : Cell87 F := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hFK
  classical
  exfalso
  have hd := CellData.of_ctx hctx hsig hyp
  have hzb2 := hd.z2
  set zb : Sec H₀ H₁ := zSec z H₀ hz H₁ with hzb
  set K : Subgroup (Sec H₀ H₁) := layer (Sec H₀ H₁) with hK
  have hKn : K.Normal := layer_normal
  have hq : IsQuasisimple ↥K := hd.quasi
  have hZ2 : IsPGroup 2 ↥(center ↥K) := by rw [hd.Zcore]; exact CFSG.pCore_isPGroup
  have hZ : center ↥K = ⊥ := hF.mult ↥K hq hZ2 hFK
  let eq0 : (↥K ⧸ center ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hFK' : F ↥K := hF.iso eq0 hFK
  have hsimple : IsSimpleGroup ↥K := (eq0.isSimpleGroup_congr).1 hq.2.1
  have hnonab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact ⟨eq0 a, eq0 b, fun h => hab (eq0.injective (by simpa [map_mul] using h))⟩
  have hOut : OutAbelian ↥K := hF.outAbel ↥K hFK'
  have hXK : X ≤ K :=
    x_le_layer_of_comm hzb2 hsig.A hsig.op hd.gen fun x _ => comm_mem_sup_centralizer K hOut x zb
  let α : MulAut ↥K := layerAut zb
  have hα2 : α * α = 1 := by
    refine MulEquiv.ext fun s => ?_
    show α (α s) = s
    exact layerAut_layerAut hzb2 s
  have hα1 : α ≠ 1 := by
    intro h1
    obtain ⟨k0, hk0, hne⟩ := hd.exists_not_commute
    apply hne
    have h3 : α ⟨k0, hk0⟩ = ⟨k0, hk0⟩ := by rw [h1]; rfl
    have h2' := congrArg Subtype.val h3
    have h2 : zb * k0 * zb⁻¹ = k0 := by
      rw [show ((α ⟨k0, hk0⟩ : ↥K) : Sec H₀ H₁) = zb * k0 * zb⁻¹ from coe_layerAut zb _] at h2'
      exact h2'
    calc zb * k0 = zb * k0 * zb⁻¹ * zb := by group
      _ = k0 * zb := by rw [h2]
  have hfixC : ∀ y ∈ fixSub α, (y : Sec H₀ H₁) ∈ centralizer ({zb} : Set (Sec H₀ H₁)) := by
    intro y hy
    have h1 : α y = y := hy
    have h2 := congrArg Subtype.val h1
    rw [show ((α y : ↥K) : Sec H₀ H₁) = zb * y * zb⁻¹ from coe_layerAut zb y] at h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (y : Sec H₀ H₁) * zb = (zb * y * zb⁻¹) * zb := by rw [h2]
      _ = zb * y := by group
  have : Fact p.Prime := ⟨hsig.A.prime⟩
  have hXT : ∀ (hXT : Subgroup ↥K), hXT = X.subgroupOf K → IsPGroup p ↥hXT ∧ hXT ≠ ⊥ ∧
      fixSub α ≤ normalizer (hXT : Set ↥K) := by
    intro XT hXTdef
    subst hXTdef
    have hXp : IsPGroup p ↥(X.subgroupOf K) :=
      hsig.A.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
    have hXne : X.subgroupOf K ≠ ⊥ := by
      intro h
      apply hsig.A.ne_bot
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hXK hx⟩ : ↥K) ∈ X.subgroupOf K := hx
      rw [h] at h1
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h1))
    have hN : fixSub α ≤ normalizer ((X.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hyN : (y : Sec H₀ H₁) ∈ normalizer (X : Set (Sec H₀ H₁)) :=
        hsig.A.inv _ (Subgroup.mem_top _) (hfixC y hy)
      exact Subgroup.mem_normalizer_iff.mp hyN (x : Sec H₀ H₁)
    exact ⟨hXp, hXne, hN⟩
  rcases hF.invol ↥K hFK' α hα2 hα1 with (⟨hco, hodd⟩ | ⟨T, hTle, hTs, hTn, hbad⟩) | hno
  ·
    obtain ⟨hXp, hXne, hN⟩ := hXT _ rfl
    have := hsimple
    refine false_of_coatom_subgroup hnonab hco ?_ hXp hXne hN
    intro W hWle hWn hWp
    exact hodd W hWle hWn (odd_card_of_isPGroup_odd_prime hsig.A.odd hWp)
  ·
    have := hTs
    have hperf : Group.IsPerfect ↥T := isPerfect_of_simple_nonab hTn
    have hTfix : ∀ s ∈ T, α s = s := fun s hs => hTle hs
    have hCS := centSection_of_fixed_perfect (zb := zb) (π := MonoidHom.id ↥K) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact bot_le) (α := α) (fun x => rfl) T hTfix (T := ↥T) (MonoidHom.id ↥T)
      Function.surjective_id
    have : Nontrivial ↥T := IsSimpleGroup.toNontrivial
    have hns : ¬ Group.IsSolvable ↥T := Group.IsPerfect.not_isSolvable _
    exact hbad k (kindFactor_of_section_sec hctx hsig hns hCS.isSection)
  ·
    obtain ⟨hXp, hXne, hN⟩ := hXT _ rfl
    exact hno p hsig.A.odd _ hXp hXne hN

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
