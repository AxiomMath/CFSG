module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def invariantTwoJoinIn (D H : Subgroup G) : Subgroup G :=
  sSup {X : Subgroup G | X ≤ H ∧ IsPGroup 2 X ∧ D ≤ normalizer (X : Set G)}

omit [Finite G] in
theorem le_invariantTwoJoinIn {D H X : Subgroup G} (hXH : X ≤ H) (hX : IsPGroup 2 X)
    (hDX : D ≤ normalizer (X : Set G)) : X ≤ invariantTwoJoinIn D H :=
  le_sSup ⟨hXH, hX, hDX⟩

omit [Finite G] in
theorem invariantTwoJoinIn_le (D H : Subgroup G) : invariantTwoJoinIn D H ≤ H :=
  sSup_le fun _ hX => hX.1

omit [Finite G] in
theorem invariantTwoJoinIn_le_of_forall {D H Y : Subgroup G}
    (h : ∀ X : Subgroup G, X ≤ H → IsPGroup 2 X → D ≤ normalizer (X : Set G) → X ≤ Y) :
    invariantTwoJoinIn D H ≤ Y :=
  sSup_le fun X hX => h X hX.1 hX.2.1 hX.2.2

omit [Finite G] in
theorem invariantTwoJoinIn_mono {D H H' : Subgroup G} (h : H ≤ H') :
    invariantTwoJoinIn D H ≤ invariantTwoJoinIn D H' :=
  invariantTwoJoinIn_le_of_forall fun _ hXH hX hDX => le_invariantTwoJoinIn (hXH.trans h) hX hDX

omit [Finite G] in
theorem map_conj_mem_invariantTwoIn {D K X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (D : Set G)) (hXK : X ≤ K) (hX : IsPGroup 2 X)
    (hDX : D ≤ normalizer (X : Set G)) :
    X.map (MulAut.conj g).toMonoidHom ≤ K.map (MulAut.conj g).toMonoidHom ∧
      IsPGroup 2 (X.map (MulAut.conj g).toMonoidHom) ∧
      D ≤ normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  refine ⟨Subgroup.map_mono hXK, hX.map _, ?_⟩
  have hD : D.map (MulAut.conj g).toMonoidHom = D := mem_normalizer_iff_map_conj_eq.mp hg
  rw [← hD, ← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hDX

omit [Finite G] in
theorem invariantTwoJoinIn_map_le {D K : Subgroup G} {g : G} (hg : g ∈ normalizer (D : Set G)) :
    invariantTwoJoinIn D (K.map (MulAut.conj g).toMonoidHom) ≤
      (invariantTwoJoinIn D K).map (MulAut.conj g).toMonoidHom := by
  refine invariantTwoJoinIn_le_of_forall fun X hXK hX hDX => ?_
  have hD : D.map (MulAut.conj g⁻¹).toMonoidHom = D :=
    mem_normalizer_iff_map_conj_eq.mp (inv_mem hg)
  have hmap : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply]
    group
  have hKK : K = (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply]
      group
    rw [this, Subgroup.map_id]
  have hXX : X = (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map, hmap, Subgroup.map_id]
  have hinv := map_conj_mem_invariantTwoIn (D := D) (K := K.map (MulAut.conj g).toMonoidHom)
    (inv_mem hg) hXK hX hDX
  rw [← hKK] at hinv
  rw [hXX]
  exact Subgroup.map_mono (le_invariantTwoJoinIn hinv.1 hinv.2.1 hinv.2.2)

omit [Finite G] in
theorem le_normalizer_invariantTwoJoinIn (D H : Subgroup G) :
    D ≤ normalizer (invariantTwoJoinIn D H : Set G) := by
  have hle : ∀ g ∈ D, (invariantTwoJoinIn D H).map (MulAut.conj g).toMonoidHom ≤
      invariantTwoJoinIn D H := by
    intro g hg
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun X hX => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hnormX : g ∈ normalizer (X : Set G) := hX.2.2 hg
    have hXX : X.map (MulAut.conj g).toMonoidHom = X := mem_normalizer_iff_map_conj_eq.mp hnormX
    rw [hXX]
    exact le_invariantTwoJoinIn hX.1 hX.2.1 hX.2.2
  intro g hg
  refine mem_normalizer_iff_map_conj_eq.mpr (le_antisymm (hle g hg) ?_)
  intro x hx
  refine ⟨g⁻¹ * x * g, hle g⁻¹ (inv_mem hg) ⟨x, hx, ?_⟩, ?_⟩
  · simp
  · simp [MulAut.conj_apply, mul_assoc]

@[expose] def relPairBase (R T : Subgroup G) : Subgroup G :=
  T ⊓ normalizer ((R ⊓ T : Subgroup G) : Set G)

structure IsRelPairCandidate (p : ℕ) (D R T H : Subgroup G) : Prop where
  twoLocal : IsTwoLocal H
  base_le : relPairBase R T ⊔ D ≤ H
  not_coprime : p ∣ Nat.card (invariantTwoJoinIn D H)

structure IsRelPairCandidatePair (p : ℕ) (M D R T H V : Subgroup G) : Prop where
  cand : IsRelPairCandidate p D R T H
  maximal : invariantTwoMaximalWithin D (H ⊓ M) V
  base_le : relPairBase R T ≤ V

structure IsOptimalRelPair (p : ℕ) (M D R T H V : Subgroup G) : Prop where
  pair : IsRelPairCandidatePair p M D R T H V
  card_le : ∀ H' V' : Subgroup G, IsRelPairCandidatePair p M D R T H' V' →
    Nat.card V' ≤ Nat.card V
  core_le : ∀ H' V' : Subgroup G, IsRelPairCandidatePair p M D R T H' V' →
    Nat.card V' = Nat.card V → Nat.card (pCoreOf 2 H') ≤ Nat.card (pCoreOf 2 H)
  order_le : ∀ H' V' : Subgroup G, IsRelPairCandidatePair p M D R T H' V' →
    Nat.card V' = Nat.card V → Nat.card (pCoreOf 2 H') = Nat.card (pCoreOf 2 H) →
      Nat.card H' ≤ Nat.card H

noncomputable def relPairWeight (H V : Subgroup G) : ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex (Nat.card V, toLex (Nat.card (pCoreOf 2 H), Nat.card H))

theorem exists_isOptimalRelPair {p : ℕ} {M D R T H₀ V₀ : Subgroup G}
    (h₀ : IsRelPairCandidatePair p M D R T H₀ V₀) :
    ∃ H V : Subgroup G, IsOptimalRelPair p M D R T H V := by
  classical
  let pairs := {x : Subgroup G × Subgroup G // IsRelPairCandidatePair p M D R T x.1 x.2}
  have : Nonempty pairs := ⟨⟨(H₀, V₀), h₀⟩⟩
  obtain ⟨⟨⟨H, V⟩, hHV⟩, hmax⟩ := Finite.exists_max
    (fun x : pairs => relPairWeight x.1.1 x.1.2)
  have hle : ∀ H' V' : Subgroup G, IsRelPairCandidatePair p M D R T H' V' →
      relPairWeight H' V' ≤ relPairWeight H V :=
    fun H' V' h' => hmax ⟨(H', V'), h'⟩
  refine ⟨H, V, hHV, fun H' V' h' => ?_, fun H' V' h' hV => ?_, fun H' V' h' hV hC => ?_⟩
  · have := hle H' V' h'
    unfold relPairWeight at this
    rw [Prod.Lex.le_iff] at this
    rcases this with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  · have := hle H' V' h'
    unfold relPairWeight at this
    rw [Prod.Lex.le_iff] at this
    rcases this with h | ⟨-, h⟩
    · exact absurd hV (ne_of_lt h)
    · rw [Prod.Lex.le_iff] at h
      rcases h with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
  · have := hle H' V' h'
    unfold relPairWeight at this
    rw [Prod.Lex.le_iff] at this
    rcases this with h | ⟨-, h⟩
    · exact absurd hV (ne_of_lt h)
    · rw [Prod.Lex.le_iff] at h
      rcases h with h | ⟨-, h⟩
      · exact absurd hC (ne_of_lt h)
      · exact h

theorem IsRelPairCandidate.exists_pair {p : ℕ} {M D R T H : Subgroup G}
    (hH : IsRelPairCandidate p D R T H) (hTM : T ≤ M) (hT : IsPGroup 2 T)
    (hDT : D ≤ normalizer (T : Set G))
    (hDS : D ≤ normalizer ((R ⊓ T : Subgroup G) : Set G)) :
    ∃ V : Subgroup G, IsRelPairCandidatePair p M D R T H V := by
  have hbaseM : relPairBase R T ≤ H ⊓ M :=
    le_inf ((le_sup_left : relPairBase R T ≤ _).trans hH.base_le)
      (inf_le_left.trans hTM)
  obtain ⟨V, hV, hmax⟩ := exists_invariantTwoMaximalWithin_containing D (H ⊓ M)
    (relPairBase R T) hbaseM (hT.to_inf_left)
    (common_normalizer_le_normalizer_inf D T _ hDT (hDS.trans le_normalizer))
  exact ⟨V, hH, hmax, hV⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
