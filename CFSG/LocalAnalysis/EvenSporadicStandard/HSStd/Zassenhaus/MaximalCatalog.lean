module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.DiagonalLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverE8Rank

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open scoped commutatorElement
open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

variable {G : Type} [Group G]


theorem factorization_le_of_dvd' {a b p : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    a.factorization p ≤ b.factorization p :=
  (Nat.factorization_le_iff_dvd (ne_zero_of_dvd_ne_zero hb h) hb).2 h p

theorem eq_of_le_of_catalog [Finite G] (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (h3 : (Nat.card G).factorization 3 ≤ 4)
    (hcat : ∀ (S : Type) [Group S] [Finite S], CFSG.Blueprint.Catalog S → IsSimpleGroup S →
      (Nat.card S).factorization 3 ≤ 4 → ∀ K : Subgroup S, CFSG.IsQuasisimple ↥K →
        IsSporadic (↥K ⧸ center ↥K) .HS → K = ⊤)
    {K L : Subgroup G} (hK : CFSG.IsQuasisimple ↥K) (hL : CFSG.IsQuasisimple ↥L)
    (hLtop : L ≠ ⊤) (hKL : K ≤ L) (hq : IsSporadic (↥K ⧸ center ↥K) .HS) : K = L := by
  set Z : Subgroup G := (center ↥L).map L.subtype with hZdef
  have hZL : Z ≤ L := by rintro _ ⟨z, -, rfl⟩; exact z.2
  have hZeq : Z.subgroupOf L = center ↥L := by
    ext x
    rw [Subgroup.mem_subgroupOf, hZdef, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hN : (Z.subgroupOf L).Normal := by rw [hZeq]; infer_instance
  set S := ↥L ⧸ Z.subgroupOf L
  let e : S ≃* ↥L ⧸ center ↥L := QuotientGroup.quotientMulEquivOfEq hZeq
  obtain ⟨hLperf, hsimple, a, b, hab⟩ := hL
  have hSs : IsSimpleGroup S := by
    have := hsimple
    have : Nontrivial S := e.toEquiv.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hcatS : CFSG.Blueprint.Catalog S :=
    hKP L Z hLtop hZL hSs ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  let φ : ↥K →* S := (QuotientGroup.mk' (Z.subgroupOf L)).comp (Subgroup.inclusion hKL)
  have hker : φ.ker ≤ center ↥K := by
    intro k hk
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hZeq] at hk
    rw [mem_center_iff]
    intro k'
    have := (mem_center_iff.1 hk) (Subgroup.inclusion hKL k')
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  have hR := isQuasisimple_range_of_ker_le_center hK φ hker
  obtain ⟨eK⟩ := nonempty_quotient_center_equiv_range hK φ hker
  have hRq : IsSporadic (↥φ.range ⧸ center ↥φ.range) .HS := by
    obtain ⟨f⟩ := hq
    exact ⟨eK.symm.trans f⟩
  have h3S : (Nat.card S).factorization 3 ≤ 4 := by
    have hdvd : Nat.card S ∣ Nat.card G := by
      have h1 : Nat.card S ∣ Nat.card ↥L := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf L)]
        exact dvd_mul_right _ _
      exact h1.trans (Subgroup.card_subgroup_dvd_card L)
    exact (factorization_le_of_dvd' Nat.card_pos.ne' hdvd).trans h3
  have htop := hcat S hcatS hSs h3S φ.range hR hRq
  have hsurj : Function.Surjective φ := MonoidHom.range_eq_top.1 htop
  have hdec : ∀ l : ↥L, ∃ k : ↥K, ∃ z ∈ center ↥L, l = Subgroup.inclusion hKL k * z := by
    intro l
    obtain ⟨k, hk⟩ := hsurj (QuotientGroup.mk l)
    refine ⟨k, (Subgroup.inclusion hKL k)⁻¹ * l, ?_, by group⟩
    have := QuotientGroup.eq.1 hk
    rw [hZeq] at this
    exact this
  have hcomm : commutator ↥L ≤ K.subgroupOf L := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨k₁, z₁, hz₁, rfl⟩ := hdec x
    obtain ⟨k₂, z₂, hz₂, rfl⟩ := hdec y
    have e1 : ⁅Subgroup.inclusion hKL k₁ * z₁, Subgroup.inclusion hKL k₂ * z₂⁆ =
        ⁅Subgroup.inclusion hKL k₁, Subgroup.inclusion hKL k₂⁆ := by
      rw [mem_center_iff.1 hz₁ (Subgroup.inclusion hKL k₁),
        mem_center_iff.1 hz₂ (Subgroup.inclusion hKL k₂)]
      exact commutatorElement_mul_central_of_mem hz₁ hz₂ _ _
    rw [e1, Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using K.mul_mem (K.mul_mem (K.mul_mem k₁.2 k₂.2)
      (K.inv_mem k₁.2)) (K.inv_mem k₂.2)
  rw [hLperf.commutator_eq_top] at hcomm
  refine le_antisymm hKL fun l hl => ?_
  have : (⟨l, hl⟩ : ↥L) ∈ K.subgroupOf L := hcomm (mem_top _)
  exact this

theorem maximalF_of_catalog [Finite G] (h13 : FS79Thm13UseSec G)
    {N : Subgroup G} (hN : FStarSimple N)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hGs : IsSimpleGroup G)
    (hGna : ∃ a b : G, a * b ≠ b * a) (h3 : (Nat.card G).factorization 3 ≤ 4)
    (hcat : ∀ (S : Type) [Group S] [Finite S], CFSG.Blueprint.Catalog S → IsSimpleGroup S →
      (Nat.card S).factorization 3 ≤ 4 → ∀ K : Subgroup S, CFSG.IsQuasisimple ↥K →
        IsSporadic (↥K ⧸ center ↥K) .HS → K = ⊤)
    {M : Subgroup G} (hM : InLF M) (hMq : IsSporadic (↥M ⧸ center ↥M) .HS)
    (hrk : ∀ K : Subgroup G, IsSporadic (↥K ⧸ center ↥K) .HS → CFSG.pRank 2 ↥K ≠ 1) :
    MaximalF M := by
  have hperf : ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ N := by
    rcases hN.normal.eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hN.nonabelian
      subst h
      exact hab (Subsingleton.elim _ _)
    · exact fun _ _ => h ▸ le_top
  refine maximalF_of_aLinks h13 hKP hN hperf hM hMq ?_ hrk
  intro K L s t hs ht hst hK hL hLe hKL hq
  have hLtop : L ≠ ⊤ := by
    intro hLt
    have hLle := hL.le
    rw [hLt, top_le_iff] at hLle
    have ht1 : t ≠ 1 := by rintro rfl; simp at ht
    have hcen : t ∈ center G := by
      rw [mem_center_iff]
      intro g
      have : g ∈ centralizer ({t} : Set G) := hLle ▸ mem_top g
      exact (mem_centralizer_singleton_iff.1 this)
    have hn : (center G).Normal := inferInstance
    rcases hn.eq_bot_or_eq_top with h | h
    · rw [h, mem_bot] at hcen
      exact ht1 hcen
    · obtain ⟨a, b, hab⟩ := hGna
      exact hab ((mem_center_iff.1 (h ▸ mem_top b)) a)
  exact eq_of_le_of_catalog hKP h3 hcat hK.isQuasisimple hL.isQuasisimple hLtop hKL hq


theorem pRank_ne_one_of_hsType [Finite G] {K : Subgroup G}
    (hq : IsSporadic (↥K ⧸ center ↥K) .HS) : CFSG.pRank 2 ↥K ≠ 1 := by
  obtain ⟨e⟩ := hq
  have := three_le_pRank_hs_cover e
  omega

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
