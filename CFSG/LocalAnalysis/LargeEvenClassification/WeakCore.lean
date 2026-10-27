module

public import CFSG.LocalAnalysis.LargeEvenClassification.LocalRank
public import CFSG.LocalAnalysis.LargeEvenClassification.SubgroupTransport

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

@[expose] def weakPCoreEligible {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    (prime : ℕ) (Parent Candidate : Subgroup Ambient) : Prop :=
  Candidate ≤ Parent ∧ 2 ≤ pRank prime Candidate ∧
    3 ≤ pRank prime (Candidate ⊔ (Parent ⊓ Subgroup.centralizer (Candidate : Set Ambient)))

@[expose] noncomputable def weakTwoGeneratedPCore {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (prime : ℕ) (Parent : Subgroup Ambient) : Subgroup Ambient :=
  ⨆ Candidate : {Candidate : Subgroup Ambient // weakPCoreEligible prime Parent Candidate},
    Subgroup.normalizer (Candidate.val : Set Ambient)

@[expose] def WeakCoreLocal (prime : ℕ) (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient] : Prop :=
  3 ≤ pRank prime (⊤ : Subgroup Ambient) ∧
    ∀ Parent : Sylow prime Ambient, ∃ Local : Subgroup Ambient,
      IsTwoLocal Local ∧ weakTwoGeneratedPCore prime (Parent : Subgroup Ambient) ≤ Local

theorem eligible_normalizer_le_weak_core {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (Parent Candidate : Subgroup Ambient)
    (heligible : weakPCoreEligible prime Parent Candidate) :
    Subgroup.normalizer (Candidate : Set Ambient) ≤ weakTwoGeneratedPCore prime Parent :=
  le_iSup_of_le ⟨Candidate, heligible⟩ le_rfl

theorem weak_core_le_iff {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (Parent Target : Subgroup Ambient) :
    weakTwoGeneratedPCore prime Parent ≤ Target ↔
      ∀ Candidate : Subgroup Ambient, weakPCoreEligible prime Parent Candidate →
        Subgroup.normalizer (Candidate : Set Ambient) ≤ Target := by
  constructor
  · intro hle Candidate heligible
    exact (eligible_normalizer_le_weak_core Parent Candidate heligible).trans hle
  · intro hnormalizers
    exact iSup_le fun Candidate => hnormalizers Candidate.val Candidate.property

theorem parent_le_weak_core {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) (Parent : Subgroup Ambient) (hrank : 3 ≤ pRank prime Parent) :
    Parent ≤ weakTwoGeneratedPCore prime Parent := by
  have heligible : weakPCoreEligible prime Parent Parent :=
    ⟨le_rfl, by omega, hrank.trans (pRank_mono hprime le_sup_left)⟩
  exact Subgroup.le_normalizer.trans (eligible_normalizer_le_weak_core Parent Parent heligible)

theorem elementary_normalizer_le_weak_core {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : 1 < prime) (Parent Elementary Candidate : Subgroup Ambient)
    (helementary : IsElemAbelian prime Elementary) (hcandidateLe : Candidate ≤ Elementary)
    (helementaryLe : Elementary ≤ Parent) (hcandidateRank : 2 ≤ pRank prime Candidate)
    (helementaryRank : 3 ≤ pRank prime Elementary) :
    Subgroup.normalizer (Candidate : Set Ambient) ≤ weakTwoGeneratedPCore prime Parent := by
  apply eligible_normalizer_le_weak_core Parent Candidate
  refine ⟨hcandidateLe.trans helementaryLe, hcandidateRank, ?_⟩
  have hcentralizer : Elementary ≤ Subgroup.centralizer (Candidate : Set Ambient) := by
    intro element helement
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    exact congrArg (fun entry : Elementary => entry.val)
      (@mul_comm' Elementary _ helementary.1 ⟨other, hcandidateLe hother⟩ ⟨element, helement⟩)
  exact helementaryRank.trans (pRank_mono hprime
    ((le_inf helementaryLe hcentralizer).trans le_sup_right))

theorem weakPCoreEligible_map {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {Target : Type targetUniverse} [Group Target] [Finite Target] {prime : ℕ}
    (hprime : 1 < prime) (coordinates : Ambient ≃* Target) (Parent Candidate : Subgroup Ambient) :
    weakPCoreEligible prime (Parent.map coordinates.toMonoidHom) (Candidate.map coordinates.toMonoidHom) ↔
      weakPCoreEligible prime Parent Candidate := by
  unfold weakPCoreEligible
  rw [Subgroup.map_le_map_iff_of_injective coordinates.injective,
    pRank_map_mulEquiv hprime coordinates Candidate, ← centralizer_map_mulEquiv coordinates Candidate,
    ← Subgroup.map_inf _ _ _ coordinates.injective, ← Subgroup.map_sup,
    pRank_map_mulEquiv hprime coordinates]

theorem weak_core_map_le {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {Target : Type targetUniverse} [Group Target] [Finite Target] {prime : ℕ}
    (hprime : 1 < prime) (coordinates : Ambient ≃* Target) (Parent : Subgroup Ambient) :
    (weakTwoGeneratedPCore prime Parent).map coordinates.toMonoidHom ≤
      weakTwoGeneratedPCore prime (Parent.map coordinates.toMonoidHom) := by
  unfold weakTwoGeneratedPCore
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro Candidate
  rw [Subgroup.map_equiv_normalizer_eq]
  exact le_iSup_of_le
    ⟨Candidate.val.map coordinates.toMonoidHom,
      (weakPCoreEligible_map hprime coordinates Parent Candidate.val).mpr Candidate.property⟩ le_rfl

theorem weak_core_map_mulEquiv {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {Target : Type targetUniverse} [Group Target] [Finite Target] {prime : ℕ}
    (hprime : 1 < prime) (coordinates : Ambient ≃* Target) (Parent : Subgroup Ambient) :
    (weakTwoGeneratedPCore prime Parent).map coordinates.toMonoidHom =
      weakTwoGeneratedPCore prime (Parent.map coordinates.toMonoidHom) := by
  apply le_antisymm (weak_core_map_le hprime coordinates Parent)
  have hreverse := weak_core_map_le hprime coordinates.symm (Parent.map coordinates.toMonoidHom)
  rw [subgroup_map_inverse_mulEquiv] at hreverse
  have hmap := Subgroup.map_mono (f := coordinates.toMonoidHom) hreverse
  simpa only [subgroup_map_forward_inverse_mulEquiv] using hmap

theorem normalizer_parent_le_normalizer_weak_core {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : 1 < prime) (Parent : Subgroup Ambient) :
    Subgroup.normalizer (Parent : Set Ambient) ≤
      Subgroup.normalizer (weakTwoGeneratedPCore prime Parent : Set Ambient) := by
  intro element helement
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (weakTwoGeneratedPCore prime Parent).map (MulAut.conj element).toMonoidHom = _
  rw [weak_core_map_mulEquiv hprime (MulAut.conj element) Parent]
  have hparent : Parent.map (MulAut.conj element).toMonoidHom = Parent :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp helement
  rw [hparent]

end CFSG.LargeEvenClassification.Helpers
