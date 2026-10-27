module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3NineOdd
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixLift

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem relativeWeakClosure_subgroupOf {L G T S : Subgroup X} (hG : G ≤ L) (hT : T ≤ L)
    (hS : S ≤ L) :
    (relativeWeakClosure (G.subgroupOf L) (T.subgroupOf L) (S.subgroupOf L)).map L.subtype =
      relativeWeakClosure G T S := by
  have hTm : (T.subgroupOf L).map L.subtype = T := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT]
  have hSm : (S.subgroupOf L).map L.subtype = S := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS]
  have hconj : ∀ x : L, (rightConjugate (T.subgroupOf L) x).map L.subtype =
      rightConjugate T x := fun x => by rw [map_rightConjugate, hTm]; rfl
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, relativeWeakClosure_le_iff]
    intro x hx hle
    rw [← Subgroup.map_le_iff_le_comap, hconj]
    apply rightConjugate_le_relativeWeakClosure (Subgroup.mem_subgroupOf.mp hx)
    rw [← hconj, ← hSm]
    exact Subgroup.map_mono hle
  · rw [relativeWeakClosure_le_iff]
    intro x hx hle
    set x' : L := ⟨x, hG hx⟩
    have h1 : rightConjugate (T.subgroupOf L) x' ≤ S.subgroupOf L := by
      rw [← Subgroup.map_le_map_iff_of_injective L.subtype_injective, hconj, hSm]
      exact hle
    rw [show rightConjugate T x = (rightConjugate (T.subgroupOf L) x').map L.subtype from
      (hconj x').symm]
    exact Subgroup.map_mono (rightConjugate_le_relativeWeakClosure
      (Subgroup.mem_subgroupOf.mpr hx : x' ∈ G.subgroupOf L) h1)

omit [Finite X] in
theorem map_subtype_oddCore_subgroupOf {L G₁ : Subgroup X} (hGL : G₁ ≤ L) :
    ((CFSG.oddCore (G₁.subgroupOf L)).map (G₁.subgroupOf L).subtype).map L.subtype =
      (CFSG.oddCore G₁).map G₁.subtype := by
  set e : G₁.subgroupOf L ≃* G₁ := Subgroup.subgroupOfEquivOfLe hGL
  have hcomp : L.subtype.comp (G₁.subgroupOf L).subtype = G₁.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, map_oddCore_equiv e]

theorem IH46.apply_mod_odd {n : ℕ} (IH : IH46 n) {G₁ T₁ S₁ Q₁ H₁ : Subgroup X} {g₁ : X}
    (hcard : Nat.card (G₁ ⊔ T₁ : Subgroup X) < n)
    (hS : SylowFrame G₁ T₁ S₁) (h43 : Hyp43 G₁ T₁ Q₁ H₁) (hT : T₁ ≠ ⊥) (hg : g₁ ∈ G₁)
    (hW : relativeWeakClosure G₁ T₁ S₁ = T₁ ⊔ rightConjugate T₁ g₁)
    (hgN : rightConjugate T₁ g₁ ≤ Subgroup.normalizer (T₁ : Set X)) :
    pRank 2 T₁ = 1 ∨
    G₁ ≤ Subgroup.normalizer ((relativeWeakClosure G₁ T₁ S₁ ⊔
      (CFSG.oddCore G₁).map G₁.subtype : Subgroup X) : Set X) ∨
    ∃ B : Subgroup X, B ≤ G₁ ∧ G₁ ≤ Subgroup.normalizer (B : Set X) ∧
      relativeWeakClosure G₁ T₁ S₁ ⊓ G₁ ≤ B ∧
      ∀ N : Subgroup X, IsPGroup 2 N → N ≤ B → G₁ ≤ Subgroup.normalizer (N : Set X) →
        N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := G₁ ⊔ T₁ with hL
  have hGL : G₁ ≤ L := le_sup_left
  have hTL : T₁ ≤ L := le_sup_right
  have hSL : S₁ ≤ L := hS.sylow.le
  set G' := G₁.subgroupOf L with hG'
  set T' := T₁.subgroupOf L with hT'def
  set S' := S₁.subgroupOf L with hS'def
  have hS' : SylowFrame G' T' S' := hS.subgroupOf
  have h43' := h43.subgroupOf
  have htop : G' ⊔ T' = ⊤ := sup_subgroupOf_eq_top G₁ T₁
  have hTm : T'.map L.subtype = T₁ := by
    rw [hT'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTL]
  have hGm : G'.map L.subtype = G₁ := by
    rw [hG', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hGL]
  have hT'ne : T' ≠ ⊥ := fun h => hT (by rw [← hTm, h, Subgroup.map_bot])
  set g' : L := ⟨g₁, hGL hg⟩
  have hg' : g' ∈ G' := hg
  have hconjm : ∀ x : L, (rightConjugate T' x).map L.subtype = rightConjugate T₁ x :=
    fun x => by rw [map_rightConjugate, hTm]; rfl
  have hW'm : (relativeWeakClosure G' T' S').map L.subtype = relativeWeakClosure G₁ T₁ S₁ :=
    relativeWeakClosure_subgroupOf hGL hTL hSL
  have hW' : relativeWeakClosure G' T' S' = T' ⊔ rightConjugate T' g' := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hW'm, Subgroup.map_sup, hTm, hconjm, hW]
  have hgN' : rightConjugate T' g' ≤ Subgroup.normalizer (T' : Set L) := by
    intro y hy
    rw [hT'def, ← Subgroup.subgroupOf_normalizer_eq hTL]
    have h1 := Subgroup.mem_map_of_mem L.subtype hy
    rw [hconjm] at h1
    exact hgN h1
  set O' : Subgroup L := (CFSG.oddCore G').map G'.subtype with hO'
  have hO'G : O' ≤ G' := Subgroup.map_subtype_le _
  have hO'odd : Odd (Nat.card O') := by
    rw [hO', Subgroup.card_map_of_injective G'.subtype_injective]
    exact odd_card_oddCore _
  have hO'n : O'.Normal := by
    have : (CFSG.oddCore G').Characteristic := OddCore.characteristic _
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le (fun x hx => mem_normalizer_map_of_characteristic _ (Subgroup.le_normalizer hx))
      (fun x hx => mem_normalizer_map_of_characteristic _ (hS'.toFrame.le_normalizer hx))
  have hO'm : O'.map L.subtype = (CFSG.oddCore G₁).map G₁.subtype :=
    map_subtype_oddCore_subgroupOf hGL
  set π := QuotientGroup.mk' O' with hπ
  have hSb := hS'.map_odd htop O' hO'G hO'odd
  have h43b := Hyp43.map_odd hS'.toFrame h43' htop O' hO'G hO'odd
  have hinjT : ∀ y ∈ T', π y = 1 → y = 1 := fun y hy h1 =>
    mk_eq_one_of_odd hO'odd hS'.isPGroup hy h1
  have hTb : T'.map π ≠ ⊥ := by
    intro hbot
    apply hT'ne
    rw [eq_bot_iff]
    intro y hy
    have : π y ∈ T'.map π := Subgroup.mem_map_of_mem π hy
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (hinjT y hy this)
  have hOb : CFSG.oddCore (G'.map π) = ⊥ := Pre49.oddCore_quotient rfl
  have hWmap := relativeWeakClosure_map_odd (G := G') (S := S') hS'.isPGroup
    hS'.sylow.isPGroup hO'G hO'odd
  have hWb : relativeWeakClosure (G'.map π) (T'.map π) (S'.map π) =
      T'.map π ⊔ rightConjugate (T'.map π) (π g') := by
    rw [hWmap, hW', Subgroup.map_sup, map_rightConjugate]
  have hgNb : rightConjugate (T'.map π) (π g') ≤
      Subgroup.normalizer ((T'.map π : Subgroup (L ⧸ O')) : Set (L ⧸ O')) := by
    rw [← map_rightConjugate]
    exact (Subgroup.map_mono hgN').trans (Subgroup.le_normalizer_map _)
  have hcardb : Nat.card (G'.map π ⊔ T'.map π : Subgroup (L ⧸ O')) < n := by
    calc Nat.card (G'.map π ⊔ T'.map π : Subgroup (L ⧸ O'))
        ≤ Nat.card (G' ⊔ T' : Subgroup L) := by
          rw [← Subgroup.map_sup]
          exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
      _ = Nat.card L := by rw [htop, Subgroup.card_top]
      _ < n := hcard
  have hconcl := IH (L ⧸ O') (G'.map π) (T'.map π) (S'.map π) _ _ (π g') hcardb hSb h43b hTb
    hOb (Subgroup.mem_map_of_mem π hg') hWb hgNb
  have hkerπ : π.ker = O' := QuotientGroup.ker_mk' O'
  rcases hconcl with hm | hN | hB
  ·
    left
    rw [pRank_map_eq_of_ker π hinjT, ← pRank_map_eq L.subtype L.subtype_injective T', hTm] at hm
    exact hm
  ·
    right; left
    intro x hx
    set x' : L := ⟨x, hGL hx⟩
    have h1 : π x' ∈ Subgroup.normalizer
        ((relativeWeakClosure G' T' S').map π : Set (L ⧸ O')) := by
      rw [← hWmap]
      exact hN (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem π (hx : x' ∈ G')))
    have h2 : x' ∈ Subgroup.normalizer
        ((relativeWeakClosure G' T' S' ⊔ O' : Subgroup L) : Set L) := by
      have h3 : x' ∈ (Subgroup.normalizer
          ((relativeWeakClosure G' T' S').map π : Set (L ⧸ O'))).comap π := h1
      rwa [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective O'),
        Subgroup.comap_map_eq, hkerπ] at h3
    have h4 := Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype h2)
    rwa [Subgroup.map_sup, hW'm, hO'm] at h4
  ·
    right; right
    obtain ⟨m, -, -, -, -, -, hBen, -, -, hWB, -⟩ := hB
    set Bb := ⁅T'.map π, G'.map π⁆ with hBb
    have hBbG : Bb ≤ G'.map π := by
      rw [hBb, Subgroup.commutator_comm]
      exact hSb.toFrame.commutator_le
    refine ⟨(Bb.comap π).map L.subtype, ?_, ?_, ?_, ?_⟩
    ·
      rw [← hGm]
      apply Subgroup.map_mono
      have h1 : Bb.comap π ≤ (G'.map π).comap π := Subgroup.comap_mono hBbG
      rwa [Subgroup.comap_map_eq, hkerπ, sup_eq_left.mpr hO'G] at h1
    ·
      intro x hx
      set x' : L := ⟨x, hGL hx⟩
      have h1 : π x' ∈ Subgroup.normalizer (Bb : Set (L ⧸ O')) :=
        Subgroup.normalizer_commutator_ge_right _ _ (Subgroup.mem_map_of_mem π (hx : x' ∈ G'))
      have h2 : x' ∈ Subgroup.normalizer ((Bb.comap π : Subgroup L) : Set L) := by
        have h3 : x' ∈ (Subgroup.normalizer (Bb : Set (L ⧸ O'))).comap π := h1
        rwa [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective O')]
          at h3
      exact Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype h2)
    ·
      rintro y ⟨hyW, hyG⟩
      rw [← hW'm] at hyW
      obtain ⟨y', hy'W, rfl⟩ := hyW
      refine ⟨y', ?_, rfl⟩
      apply hWB
      rw [hWmap]
      exact ⟨Subgroup.mem_map_of_mem π hy'W, Subgroup.mem_map_of_mem π (hyG : y' ∈ G')⟩
    ·
      intro N hN2 hNB hNnorm
      have hNL : N ≤ L := hNB.trans (Subgroup.map_subtype_le _)
      set N' := N.subgroupOf L with hN'
      have hN'm : N'.map L.subtype = N := by
        rw [hN', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNL]
      have hN'B : N' ≤ Bb.comap π := by
        intro y hy
        obtain ⟨z, hz, hzy⟩ := hNB (Subgroup.mem_subgroupOf.mp hy)
        rwa [← Subtype.ext hzy]
      have hN'2 : IsPGroup 2 N' := hN2.comap_subtype
      have hNb2 : IsPGroup 2 (N'.map π) := hN'2.map π
      have hNbB : N'.map π ≤ Bb := Subgroup.map_le_iff_le_comap.mpr hN'B
      have hGN' : G' ≤ Subgroup.normalizer (N' : Set L) := by
        intro x hx
        rw [hN', ← Subgroup.subgroupOf_normalizer_eq hNL]
        exact hNnorm hx
      have hGNb : G'.map π ≤ Subgroup.normalizer ((N'.map π : Subgroup (L ⧸ O')) :
          Set (L ⧸ O')) := (Subgroup.map_mono hGN').trans (Subgroup.le_normalizer_map _)
      have : IsSimpleGroup Bb := hBen.isSimpleGroup
      have hn : ((N'.map π).subgroupOf Bb).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (hBbG.trans hGNb)
      rcases hn.eq_bot_or_eq_top with hbot | htop'
      · have hNb : N'.map π = ⊥ := by
          rw [Subgroup.subgroupOf_eq_bot] at hbot
          have h1 := disjoint_iff.mp hbot
          rwa [inf_eq_left.mpr hNbB] at h1
        rw [Subgroup.map_eq_bot_iff, hkerπ] at hNb
        rw [← hN'm, eq_bot_iff]
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨k, hk⟩ := hN'2 ⟨y, hy⟩
        have hy1 : y = 1 := eq_one_of_two_pow_of_odd (hNb hy) hO'odd (congrArg Subtype.val hk)
        rw [hy1]
        exact Subgroup.mem_bot.mpr rfl
      · exfalso
        apply hBen.not_isPGroup
        refine hNb2.to_le ?_
        intro y hy
        have : (⟨y, hy⟩ : Bb) ∈ (N'.map π).subgroupOf Bb := htop' ▸ Subgroup.mem_top _
        exact this

end CFSG.ComponentClassification.AschbacherTheorem3
