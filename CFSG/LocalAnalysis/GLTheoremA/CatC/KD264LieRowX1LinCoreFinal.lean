module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreMain
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreStd
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreStruct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Final

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Planes
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Assemble
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Main
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Std

theorem pRank_eq_of_card' {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    CFSG.Open.pRank p E = k := by
  unfold CFSG.Open.pRank
  have hbdd : ∀ j ∈ {k : ℕ | ∃ E' : Subgroup G, E' ≤ E ∧ IsElemAbelian p E' ∧
      Nat.card E' = p ^ k}, j ≤ k := by
    rintro j ⟨E', hE'le, -, hcard⟩
    have hle : Nat.card E' ≤ Nat.card E := Subgroup.card_le_of_le hE'le
    rw [hcard, hk] at hle
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  apply le_antisymm
  · exact csSup_le' (fun j hj => hbdd j hj)
  · exact le_csSup ⟨k, fun j hj => hbdd j hj⟩ ⟨E, le_rfl, hE, hk⟩

theorem dual_of_struct {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {E : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype E]
    {k : ℕ} {X : Fin k → Submodule (ZMod 2) V} {ρf : Fin k → (V ≃ₗ[ZMod 2] V)}
    (D : PieceData E X ρf)
    (hpe : ∀ p : {i // Module.finrank (ZMod 2) (X i) = 2}, ∃ e ∈ E,
      ∀ q : {i // Module.finrank (ZMod 2) (X i) = 2},
        expo ρf X q.1 e = if q = p then 1 else 0) :
    DualData E X ρf := by
  classical
  intro j hj
  obtain ⟨e, he, hepx⟩ := hpe ⟨j, hj⟩
  refine ⟨e, he, ?_, ?_⟩
  · intro x hx
    have h1 : expo ρf X j e = 1 := by
      have := hepx ⟨j, hj⟩
      simpa using this
    have := expo_spec (pow_on_plane D hj e he) x hx
    rw [h1] at this
    rw [this]
    rfl
  · intro l hl x hx
    by_cases hpl : Module.finrank (ZMod 2) (X l) = 2
    · have h0 : expo ρf X l e = 0 := by
        have := hepx ⟨l, hpl⟩
        have hne : (⟨l, hpl⟩ : {i // Module.finrank (ZMod 2) (X i) = 2}) ≠ ⟨j, hj⟩ := by
          intro h
          exact hl (congrArg Subtype.val h)
        simpa [hne] using this
      have := expo_spec (pow_on_plane D hpl e he) x hx
      rw [h0] at this
      rw [this]
      rfl
    · exact D.line_triv hpl e he x hx

theorem core_V {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {N : ℕ} (hV : Module.finrank (ZMod 2) V = N) (hN : 5 ≤ N)
    (E : Subgroup (V ≃ₗ[ZMod 2] V)) (hE : IsElemAbelian 3 E)
    (hmax : ∀ E' : Subgroup (V ≃ₗ[ZMod 2] V), IsElemAbelian 3 E' →
      CFSG.Open.pRank 3 E' ≤ CFSG.Open.pRank 3 E) :
    ∃ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ E ∧ IsElemAbelian 3 F ∧ Nat.card E = 3 * Nat.card F ∧
      ∃ L : Subgroup (V ≃ₗ[ZMod 2] V),
        CFSG.Open.IsSubnormal L (Subgroup.centralizer (F : Set (V ≃ₗ[ZMod 2] V))) ∧
          CFSG.Open.IsQuasisimple L ∧ 3 ∣ Nat.card (L ⧸ Subgroup.center L) := by
  classical
  obtain ⟨E0, hE0, hE0card⟩ := exists_elemAb_card V N hV
  have hpE0 : CFSG.Open.pRank 3 E0 = N / 2 :=
    pRank_eq_of_card' Nat.prime_three hE0 hE0card
  obtain ⟨kE, hkE⟩ := card_eq_pow_three hE
  have hpE : CFSG.Open.pRank 3 E = kE := pRank_eq_of_card' Nat.prime_three hE hkE
  have hge : 3 ^ (N / 2) ≤ Nat.card E := by
    rw [hkE]
    apply Nat.pow_le_pow_right (by norm_num)
    have := hmax E0 hE0
    rw [hpE0, hpE] at this
    exact this
  haveI : Fintype E := Fintype.ofFinite E
  have hge' : 3 ^ (Module.finrank (ZMod 2) V / 2) ≤ Fintype.card E := by
    rw [hV, ← Nat.card_eq_fintype_card]
    exact hge
  obtain ⟨k, X, ρf, hXprop, hind, hsup, hρf, hPcard, hpe⟩ := exists_struct E hE hge'
  let D : PieceData E X ρf := ⟨hE, fun i => (hXprop i).1, fun i => (hXprop i).2, hind, hsup, hρf⟩
  have hdual : DualData E X ρf := dual_of_struct D hpe
  have hone : 1 < Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} := by
    rw [hPcard]
    omega
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hone
  have hne : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  obtain ⟨e₁, he₁, he₁a, he₁b⟩ := hdual a.1 a.2
  obtain ⟨e₂, he₂, he₂a, he₂b⟩ := hdual b.1 b.2
  exact core_good D hdual a.2 b.2 hne he₁ he₂ he₁a he₁b he₂a he₂b

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Final

end
