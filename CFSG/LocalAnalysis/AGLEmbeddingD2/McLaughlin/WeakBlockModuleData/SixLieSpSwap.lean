module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieSpLines
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOutOrth
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.BorelTits CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def AutInner (X : Type*) [Group X] : Prop :=
  ∀ ψ : X ≃* X, ∃ a : X, ∀ x, ψ x = a * x * a⁻¹

theorem autInner_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (hY : AutInner Y) :
    AutInner X := by
  intro ψ
  obtain ⟨a, ha⟩ := hY (e.symm.trans (ψ.trans e))
  refine ⟨e.symm a, fun x => ?_⟩
  have hx := ha (e x)
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at hx
  apply e.injective
  rw [hx]
  simp [map_mul, map_inv]

theorem autInner_of_card_outer_le_one {G : Type*} [Group G] [Finite G]
    (h : Nat.card (Outer G) ≤ 1) : AutInner G := by
  intro ψ
  have : Finite (MulAut G) := MulEquiv.finite_left
  have hpos : 0 < Nat.card (Outer G) := Nat.card_pos
  have h1 : Nat.card (Outer G) = 1 := le_antisymm h hpos
  obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp h1
  have hq : (QuotientGroup.mk (s := inner G) ψ : Outer G) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff] at hq
  obtain ⟨a, ha⟩ := hq
  exact ⟨a, fun x => by
    have hx := congrArg (fun φ : MulAut G => φ x) ha
    simp only [MulAut.conj_apply] at hx
    exact hx.symm⟩

theorem autInner_psp_two {X : Type} [Group X] {r : ℕ} (hr : 3 ≤ r)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp r 2 1) : AutInner X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [pow_one] at hK
  have h1 := CFSG.RankThree.PartTwo.Sec19.Step1919EndProof.card_outer_statedSp_le (r := r) hr
    (card_eq_two_units hK)
  have hsub := subsingleton_ringEquiv_of_card_two hK
  have h2 : Nat.card (K ≃+* K) ≤ 1 := by
    have := (Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨RingEquiv.refl K⟩⟩).le
    exact this
  exact autInner_of_mulEquiv e (autInner_of_card_outer_le_one (h1.trans h2))

section SpY

variable {Y : Type} [Group Y] [Finite Y]

theorem sp_lines_Y {r : ℕ} (hr0 : 0 < r) (hr : r ≤ 4)
    (hc : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSp r 2 1) (T : Sylow 2 Y) {J : Subgroup Y}
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hperf : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → Nat.Coprime 3 (Nat.card V))
    {E₀ : Subgroup Y} (hEJ : E₀ ≤ J) (hE : Nat.card E₀ = 9) :
    ∃ E₁ : Subgroup Y, E₁ ≤ E₀ ∧ Nat.card E₁ = 3 ∧
      J ⊓ Subgroup.normalizer (E₀ : Set Y) ≤ Subgroup.normalizer (E₁ : Set Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := hc
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hB := borelQuotient_sp e
  obtain ⟨π', hπ's, hπ'k, hT⟩ := hB.exists_conj_eq T
  have hQ : BorelQuotient (Symplectic.rootDatum r K) (Symplectic.weylRep r K)
      (Symplectic.torus r K) π' (Nat.card K - 1) :=
    { ct := hB.ct, extras := hB.extras, pGroup := hB.pGroup, surj := hπ's, odd := hB.odd,
      torus_pow := hB.torus_pow, ker_central := fun z hz => hB.ker_central z (hπ'k ▸ hz),
      ker_pow := fun z hz => hB.ker_pow z (hπ'k ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hinj : Function.Injective π' := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have := hQ.ker_pow z hz
    rw [hK2] at this
    simpa using this
  have hbij : Function.Bijective π' := ⟨hinj, hπ's⟩
  set A : Subgroup (StatedSp r K) := J.comap π' with hA
  have hBA : borel (Symplectic.rootDatum r K) (Symplectic.torus r K) ≤ A := fun b hb =>
    hNJ (by rw [hNπ]; exact ⟨b, hb, rfl⟩)
  have hperfK : ∀ V : Subgroup (StatedSp r K), V ≤ A → ⁅V, V⁆ = V → ¬ 3 ∣ Nat.card V := by
    intro V hVA hV h3
    have hc := Subgroup.map_commutator V V π'
    have := hperf (V.map π') (Subgroup.map_le_iff_le_comap.mpr hVA) (by rw [← hc, hV])
    have hcard := Subgroup.card_map_of_injective (f := π') hinj (K := V)
    rw [hcard] at this
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 this h3
  set E₂ : Subgroup (StatedSp r K) := E₀.comap π' with hE₂
  have hE₂map : E₂.map π' = E₀ := Subgroup.map_comap_eq_self_of_surjective hπ's E₀
  have hE₂A : E₂ ≤ A := fun x hx => hEJ hx
  have hE₂card : Nat.card E₂ = 9 := by
    have hcard := Subgroup.card_map_of_injective (f := π') hinj (K := E₂)
    rw [← hE, ← hE₂map]
    exact hcard.symm
  obtain ⟨F₁, hF₁E, hF₁c, hF₁N⟩ := sp_lines_core hr0 hr hK2 hBA hperfK hE₂A hE₂card
  refine ⟨F₁.map π', ?_, ?_, ?_⟩
  · rw [← hE₂map]; exact Subgroup.map_mono hF₁E
  · rw [Subgroup.card_map_of_injective (f := π') hinj (K := F₁), hF₁c]
  · rintro y ⟨hyJ, hyN⟩
    obtain ⟨k, rfl⟩ := hπ's y
    have hkA : k ∈ A := hyJ
    have hkE : k ∈ Subgroup.normalizer (E₂ : Set (StatedSp r K)) := by
      have h1 : π' k ∈ Subgroup.normalizer ((E₂.map π' : Subgroup Y) : Set Y) := by
        rw [hE₂map]; exact hyN
      rw [← Subgroup.map_normalizer_eq_of_bijective E₂ hbij] at h1
      obtain ⟨k', hk', hkk'⟩ := h1
      rwa [← hinj hkk']
    exact (Subgroup.le_normalizer_map π') ⟨k, hF₁N ⟨hkA, hkE⟩, rfl⟩

end SpY

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
