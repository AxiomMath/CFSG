module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.LieType.BorelTits CFSG.Open

variable {Y : Type} [Group Y]

theorem exists_mem_normalizer_not_mem [Finite Y] {r : ℕ} [Fact r.Prime] {V W : Subgroup Y}
    (hV : IsPGroup r ↥V) (hWV : W ≤ V) (hne : W ≠ V) :
    ∃ x ∈ V, x ∈ normalizer (W : Set Y) ∧ x ∉ W := by
  have : Group.IsNilpotent ↥V := hV.isNilpotent
  have hlt : W.subgroupOf V < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm hWV ?_)
    exact Subgroup.subgroupOf_eq_top.mp htop
  obtain ⟨x, hx, hxW⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (W.subgroupOf V) hlt)
  refine ⟨x, x.2, ?_, fun h => hxW h⟩
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  constructor
  · intro hh
    have hhV : h ∈ V := hWV hh
    exact ((hx ⟨h, hhV⟩).mp hh : _)
  · intro hh
    have hhV : (x : Y) * h * (x : Y)⁻¹ ∈ V := hWV hh
    have h1 : h ∈ V := by
      have := V.mul_mem (V.mul_mem (V.inv_mem x.2) hhV) x.2
      simpa [mul_assoc] using this
    exact (hx ⟨h, h1⟩).mpr hh

theorem e1_engine [Finite Y] {r : ℕ} [Fact r.Prime] (hBT : Holds Y r) (b : MulAut Y)
    (hHH : ∀ E : Subgroup Y, IsPGroup r ↥E → (∀ x ∈ E, b x ∈ E) → ∀ x ∈ E, b x = x)
    {E : Subgroup Y} (hE : IsPGroup r ↥E) (hinv : ∀ x ∈ E, b x ∈ E) (hne : E ≠ ⊥) :
    ∃ (M : Subgroup Y) (S : Sylow r Y), IsCoatom M ∧
      normalizer ((S : Subgroup Y) : Set Y) ≤ M ∧
      ∀ R : Subgroup Y, IsPGroup r ↥R → R ≤ M → M ≤ normalizer (R : Set Y) →
        ∀ x ∈ R, b x = x := by
  classical
  let 𝒜 : Set (Subgroup Y) := {R | IsPGroup r ↥R ∧ (∀ x ∈ R, b x ∈ R) ∧ E ≤ R}
  obtain ⟨W, hW, hWmax⟩ := (Set.toFinite 𝒜).exists_maximal ⟨E, hE, hinv, le_rfl⟩
  obtain ⟨hWp, hWinv, hEW⟩ := hW
  have hWmax' : ∀ R : Subgroup Y, IsPGroup r ↥R → (∀ x ∈ R, b x ∈ R) → W ≤ R → R = W :=
    fun R hR hRinv hWR => le_antisymm (hWmax ⟨hR, hRinv, hEW.trans hWR⟩ hWR) hWR
  have hWfix : ∀ x ∈ W, b x = x := hHH W hWp hWinv
  have hWne : W ≠ ⊥ := fun h => hne (le_bot_iff.mp (h ▸ hEW))
  have hbW : ∀ y, b y ∈ W ↔ y ∈ W := by
    intro y
    constructor
    · intro hy
      have h1 : b (b y) = b y := hWfix _ hy
      exact b.injective h1 ▸ hy
    · intro hy
      rw [hWfix y hy]
      exact hy
  have hbW' : ∀ y, b⁻¹ y ∈ W ↔ y ∈ W := by
    intro y
    rw [← hbW (b⁻¹ y)]
    simp
  have hNinv : ∀ n ∈ normalizer (W : Set Y), b n ∈ normalizer (W : Set Y) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro h
    have h1 : b n * h * (b n)⁻¹ = b (n * b⁻¹ h * n⁻¹) := by simp [map_mul]
    rw [h1, hbW, ← hn, hbW']
  have hNinv' : ∀ n ∈ normalizer (W : Set Y), b⁻¹ n ∈ normalizer (W : Set Y) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro h
    have h1 : b⁻¹ n * h * (b⁻¹ n)⁻¹ = b⁻¹ (n * b h * n⁻¹) := by simp [map_mul]
    rw [h1, hbW', ← hn, hbW]
  have hNmap : (normalizer (W : Set Y)).map b.toMonoidHom = normalizer (W : Set Y) := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hNinv n hn
    · intro hy
      exact ⟨b⁻¹ y, hNinv' y hy, by simp⟩
  have hQ : pCoreOf r (normalizer (W : Set Y)) = W := by
    refine hWmax' _ (pCoreOf_isPGroup r _) ?_ (le_pCoreOf_normalizer r W hWp)
    intro x hx
    have h1 : b x ∈ (pCoreOf r (normalizer (W : Set Y))).map b.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [← pCoreOf_map_mulEquiv r b, hNmap] at h1
  obtain ⟨S, P, hP, hNP, -, hWP, hSP⟩ := hBT W hWne hWp
  have hV : pCoreOf r P = W := by
    by_contra hVW
    obtain ⟨x, hxV, hxN, hxW⟩ := exists_mem_normalizer_not_mem (pCoreOf_isPGroup r P) hWP
      (Ne.symm hVW)
    apply hxW
    rw [← hQ]
    have hX : pCoreOf r P ⊓ normalizer (W : Set Y) ≤ pCoreOf r (normalizer (W : Set Y)) := by
      refine le_pCoreOf_of_le_normalizer r inf_le_right ?_
        ((pCoreOf_isPGroup r P).to_le inf_le_left)
      intro n hn
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, ?_⟩
      · exact le_normalizer_pCoreOf r P (hNP hn)
      · exact Subgroup.le_normalizer hn
    exact hX ⟨hxV, hxN⟩
  obtain ⟨M, hM, hPM⟩ := (eq_top_or_exists_le_coatom P).resolve_left hP
  refine ⟨M, S, hM, hSP.trans hPM, ?_⟩
  intro R hR hRM hMR x hx
  have hSM : (S : Subgroup Y) ≤ M := Subgroup.le_normalizer.trans (hSP.trans hPM)
  have hRS : IsPGroup r ↥(R ⊔ (S : Subgroup Y)) :=
    hR.to_sup_of_normal_left' S.isPGroup' (hSM.trans hMR)
  have hRS' : R ⊔ (S : Subgroup Y) = S := S.is_maximal' hRS le_sup_right
  have hRP : R ≤ P := (le_sup_left.trans hRS'.le).trans (Subgroup.le_normalizer.trans hSP)
  have hRW : R ≤ W := hV ▸ le_pCoreOf_of_le_normalizer r hRP (hPM.trans hMR) hR
  exact hWfix x (hRW hx)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
