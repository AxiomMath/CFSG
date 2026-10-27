module

public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
public import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G]

private theorem isPGroup_of_elemAbelian_aux {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem mem_gLAPPrimeCoreOf_conj {p : ℕ} {H : Subgroup G} {x h : G}
    (hx : x ∈ GLAPPrimeCoreOf p H) (hh : h ∈ H) : h * x * h⁻¹ ∈ GLAPPrimeCoreOf p H := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, (GLAPPrimeCore.normal p H).conj_mem y hy _, ?_⟩
  simp

theorem exists_sylow_normalized_of_not_dvd [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (L B : Subgroup G) (hBp : IsPGroup p B) (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hcop : ¬ p ∣ Nat.card L) :
    ∃ Q : Subgroup G, Q ≤ L ∧ IsPGroup q Q ∧
      (∀ n : ℕ, q ^ n ∣ Nat.card L → q ^ n ∣ Nat.card Q) ∧ B ≤ Subgroup.normalizer (Q : Set G) := by
  classical
  let φ : B →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBL)
  let _ : MulDistribMulAction B L := MulDistribMulAction.compHom L φ
  let _ : MulAction B (Sylow q L) := Sylow.pointwiseMulAction
  have hcard : ¬ p ∣ Nat.card (Sylow q L) := by
    intro h
    obtain ⟨Q₁⟩ : Nonempty (Sylow q L) := inferInstance
    exact hcop (h.trans (Q₁.card_dvd_index.trans (Q₁ : Subgroup L).index_dvd_card))
  obtain ⟨Q₀, hQ₀⟩ := hBp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q L) hcard
  refine ⟨(Q₀ : Subgroup L).map L.subtype, Subgroup.map_subtype_le _, Q₀.isPGroup'.map _,
    fun n hn => ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective L)]
    exact Q₀.pow_dvd_card_of_pow_dvd_card hn
  · rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨y, hy, rfl⟩
    have hfix : (⟨b, hb⟩ : B) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨b, hb⟩
    have hmem : (⟨b, hb⟩ : B) • y ∈ (Q₀ : Subgroup L) := by
      have h := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : B) (Q₀ : Subgroup L) hy
      rwa [← Sylow.pointwise_smul_def, hfix] at h
    refine ⟨_, hmem, ?_⟩
    change (((L.normalizerMonoidHom) (Subgroup.inclusion hBL ⟨b, hb⟩)) y : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl

theorem lemma23_proved : Lemma23 := by
  intro G _ _ m p hst B hB
  obtain ⟨hBmax, D, hDB, hD, hev⟩ := hB
  have hβ : p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ m ≤ GLATwoLocalRank p G := hst.beta
  have hp : p.Prime := hβ.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hBe, hBcard, -⟩ := hBmax
  refine ⟨le_top, hBe, fun E _ hE hBE => ?_⟩
  have hD1 : D ≠ ⊥ := by
    intro h
    have h1 := hD.2
    rw [h, Subgroup.card_bot] at h1
    have h2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hWcop : Nat.Coprime p (Nat.card (GLADelta p D)) :=
    ComponentInitial.ProjectivePlane.coprime_card_GLADelta hp hD1
  have hconj : ∀ e ∈ E, ∀ w ∈ GLADelta p D, e * w * e⁻¹ ∈ GLADelta p D := by
    intro e he w hw
    simp only [GLADelta, Subgroup.mem_iInf] at hw ⊢
    intro d hd hd1
    have hec : e ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact elemAbelian_comm hE (hBE (hDB hd)) he
    exact mem_gLAPPrimeCoreOf_conj (hw d hd hd1) hec
  have hEW : E ≤ Subgroup.normalizer (GLADelta p D : Set G) := fun e he =>
    Subgroup.mem_normalizer_fintype fun n hn => hconj e he n hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, -, hQ2, hQc, hEQ⟩ := exists_sylow_normalized_of_not_dvd (q := 2) (GLADelta p D) E
    (isPGroup_of_elemAbelian_aux hE) hEW (hp.coprime_iff_not_dvd.1 hWcop)
  have hQ1 : Q ≠ ⊥ := by
    intro h
    have h1 := hQc 1 (by simpa using even_iff_two_dvd.1 hev)
    rw [h, Subgroup.card_bot] at h1
    simp at h1
  have hloc : IsTwoLocal (Subgroup.normalizer (Q : Set G)) := ⟨Q, hQ1, hQ2, rfl⟩
  obtain ⟨k, hk⟩ := exists_card_eq_pow (isPGroup_of_elemAbelian_aux hE)
  have h1 : k ≤ CFSG.Open.pRank p (Subgroup.normalizer (Q : Set G)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hEQ hE hk
  have h2 : CFSG.Open.pRank p (Subgroup.normalizer (Q : Set G)) ≤ GLATwoLocalRank p G :=
    le_csSup ⟨CFSG.Open.pRank p (⊤ : Subgroup G), by
      rintro j ⟨H, -, rfl⟩
      exact CFSG.SectionRank.pRank_mono hp.one_lt le_top⟩ ⟨_, hloc, rfl⟩
  have h3 : Nat.card E ≤ Nat.card B := by
    rw [hk, hBcard]
    exact Nat.pow_le_pow_right hp.pos (h1.trans h2)
  exact (Subgroup.eq_of_le_of_card_ge hBE h3).symm

end CFSG.LocalAnalysis.GLTheoremB
