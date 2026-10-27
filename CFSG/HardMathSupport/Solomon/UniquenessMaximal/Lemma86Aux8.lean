module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux7
import CFSG.LargeExtraspecial.BridgeNat
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section

variable {A' : Type*} [Group A'] [Finite A']

theorem isQuasisimple_of_simple {L : Type*} [Group L] (hT : IsSimpleGroup L)
    (hnab : ∃ a b : L, a * b ≠ b * a) : CFSG.Open.IsQuasisimple L := by
  have hcl := centerless_of_simple hT hnab
  have hcenter : Subgroup.center L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (hcl x fun y => (Subgroup.mem_center_iff.1 hx y).symm)
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator L) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have : ⁅a, b⁆ ∈ _root_.commutator L := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [h, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at this
      exact this
    · exact h
  · have e : L ⧸ Subgroup.center L ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
    exact (MulEquiv.isSimpleGroup_congr e).2 hT

theorem glaPComponent_of_simple {p : ℕ} (hp : p.Prime) {X L : Subgroup A'} (hLX : L ≤ X)
    (hsn : IsSubnormal L X) (hsimple : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hpL : p ∣ Nat.card L) : GLAPComponent p X L := by
  have hO : ∀ x ∈ L, x ∈ GLAPPrimeCoreOf p X → x = 1 := by
    have hnorm : ((GLAPPrimeCoreOf p X).subgroupOf L).Normal := by
      refine ⟨fun m hm l => ?_⟩
      have h := Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p X (hLX l.2))
        (m : A')
      exact (Subgroup.mem_subgroupOf).2 (by
        have := h.1 (Subgroup.mem_subgroupOf.1 hm)
        simpa using this)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((GLAPPrimeCoreOf p X).subgroupOf L) with h | h
    · intro x hx hxO
      have : (⟨x, hx⟩ : L) ∈ (GLAPPrimeCoreOf p X).subgroupOf L := hxO
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hLO : L ≤ GLAPPrimeCoreOf p X := fun x hx => by
        have : (⟨x, hx⟩ : L) ∈ (GLAPPrimeCoreOf p X).subgroupOf L := h ▸ Subgroup.mem_top _
        exact this
      exact not_dvd_card_glaPPrimeCoreOf hp X (hpL.trans (Subgroup.card_dvd_of_le hLO))
  let φ : ↥L →* (↥X ⧸ GLAPPrimeCore p ↥X) :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X)).comp (Subgroup.inclusion hLX)
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : Subgroup.inclusion hLX l ∈ GLAPPrimeCore p ↥X := (QuotientGroup.eq_one_iff _).1 hl
    have h2 : (l : A') ∈ GLAPPrimeCoreOf p X := ⟨Subgroup.inclusion hLX l, h1, rfl⟩
    exact Subgroup.mem_bot.2 (Subtype.ext (hO l l.2 h2))
  have hrange : φ.range = barX p X L := by
    ext z
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨Subgroup.inclusion hLX l, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  let e : ↥L ≃* ↥(barX p X L) :=
    (MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hrange)
  have hq : CFSG.Open.IsQuasisimple ↥(barX p X L) :=
    CFSG.LargeExtraspecial.Bridge.isQuasisimple_of_mulEquiv e (isQuasisimple_of_simple hsimple hnab)
  have hsnb : IsSubnormal (barX p X L) ⊤ := by
    have h1 := isSubnormal_comap' X.subtype hsn
    rw [show X.comap X.subtype = ⊤ from Subgroup.subgroupOf_self X] at h1
    have h2 := isSubnormal_map' (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) h1
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  refine ⟨hLX, hsn, ⟨le_top, hsnb, hq⟩, ?_⟩
  intro J hJL hJsn heq
  have hJsnL : IsSubnormal J L := by
    have := isSubnormal_inf hJsn L
    rwa [inf_eq_left.2 hJL.le, inf_eq_right.2 hLX] at this
  have hJbot : J = ⊥ := by
    obtain ⟨M, hJM, hML, hMne, hMn, -⟩ := isSubnormal_exists_normal hJsnL hJL.ne
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf L) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hxL : x ∈ L := hJL.le hx
      have : (⟨x, hxL⟩ : L) ∈ M.subgroupOf L := hJM hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    · exfalso
      apply hMne
      refine le_antisymm hML fun x hx => ?_
      have : (⟨x, hx⟩ : L) ∈ M.subgroupOf L := h ▸ Subgroup.mem_top _
      exact this
  subst hJbot
  have hbar : barX p X (⊥ : Subgroup A') = ⊥ := by
    simp [barX]
  have heq' : barX p X (⊥ : Subgroup A') = barX p X L := heq
  rw [hbar, ← hrange] at heq'
  obtain ⟨a, b, hab⟩ := hnab
  have h1 : ∀ l : L, l = 1 := by
    intro l
    apply hφinj
    have : φ l ∈ φ.range := ⟨l, rfl⟩
    rw [← heq', Subgroup.mem_bot] at this
    rw [this, map_one]
  apply hab
  rw [h1 a, h1 b]

end

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
