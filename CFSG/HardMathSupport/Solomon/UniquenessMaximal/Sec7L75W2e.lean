module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75X3a
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75W2d
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L76D
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsA

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem exists_of_mem_sup_of_le_normalizer {J O : Subgroup G}
    (hJ : J ≤ Subgroup.normalizer (O : Set G)) {g : G} (hg : g ∈ J ⊔ O) :
    ∃ j ∈ J, j⁻¹ * g ∈ O := by
  have hg' : g ∈ ((J ⊔ O : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right J O hJ] at hg'
  obtain ⟨j, hj, o, ho, rfl⟩ := hg'
  exact ⟨j, hj, by simpa using ho⟩

private theorem inf_glaPPrimeCoreOf_le {M K : Subgroup G} (hMK : M ≤ K) :
    M ⊓ GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 M := by
  refine Lemma85Aux.le_glaPPrimeCoreOf_of_normalizes Nat.prime_three inf_le_left ?_ ?_
  · intro g hg
    exact Sec7.inf_normalizer_le_normalizer_inf M (GLAPPrimeCoreOf 3 K)
      ⟨Subgroup.le_normalizer hg, le_normalizer_glaPPrimeCoreOf 3 K (hMK hg)⟩
  · intro h
    exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
      (h.trans (Subgroup.card_dvd_of_le inf_le_right))

private theorem le_sup_glaPPrimeCoreOf_of_le {J M K : Subgroup G} (hJM : J ≤ M) (hMK : M ≤ K)
    (h : K ≤ J ⊔ GLAPPrimeCoreOf 3 K) : M ≤ J ⊔ GLAPPrimeCoreOf 3 M := by
  intro m hm
  obtain ⟨j, hj, hjo⟩ := exists_of_mem_sup_of_le_normalizer
    ((hJM.trans hMK).trans (le_normalizer_glaPPrimeCoreOf 3 K)) (h (hMK hm))
  have h1 : j⁻¹ * m ∈ GLAPPrimeCoreOf 3 M :=
    inf_glaPPrimeCoreOf_le hMK ⟨M.mul_mem (M.inv_mem (hJM hj)) hm, hjo⟩
  simpa using Subgroup.mul_mem_sup hj h1

namespace Ctx75

variable {B N K : Subgroup G} {x : G}

theorem exists_J1 (c : Ctx75 B N K x) : ∃ J₁ : Subgroup G, J₁ ≤ N ∧ J₁ ≤ GLAPLayer 3 (K ⊓ N) ∧
    J₁ ≤ Subgroup.centralizer (centralizerQuot B K : Set G) ∧
    GLAPLayer 3 (K ⊓ N) ≤ J₁ ⊔ GLAPPrimeCoreOf 3 (GLAPLayer 3 (K ⊓ N)) ∧
    ∀ a ∈ centralizerQuot B K, a ≠ 1 →
      J₁ ≤ bClosureIa K a ∧ bClosureIa K a ≤ J₁ ⊔ GLAPPrimeCoreOf 3 (bClosureIa K a) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := centralizerQuot B K with hA
  set Y := K ⊓ N with hY
  set O := GLAPPrimeCoreOf 3 K with hO
  set K0 := GLAPLayer 3 Y with hK0
  set ZY : Subgroup G := Y ⊓ Subgroup.centralizer (A : Set G) with hZY
  set J₁ : Subgroup G := Subgroup.closure {g : G | g ∈ ZY ∧ IsPGroup 3 (Subgroup.zpowers g)}
    with hJ
  have hBK := c.hf.normalizes
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 K
  have hYK : Y ≤ K := inf_le_left
  have hBY : B ≤ Subgroup.normalizer (Y : Set G) := fun b hb =>
    Sec7.inf_normalizer_le_normalizer_inf K N ⟨hBK hb, Subgroup.le_normalizer (c.hBN hb)⟩
  have hOY : GLAPPrimeCoreOf 3 Y = Y ⊓ O := Sec7.glaPPrimeCoreOf_inf_eq c.cov
  have hAB : ∀ a ∈ A, a ∈ B ∧ ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ O := fun a ha =>
    comm_of_mem_centralizerQuot' hBK ha
  have hAp : IsPGroup 3 A := isPGroup_of_isElemAbelian' c.hf.aK.2.1
  obtain ⟨hcomp, hbar, hKcov⟩ := c.layer_data
  have hZYY : ZY ≤ Y := inf_le_left
  have hJZY : J₁ ≤ ZY := (Subgroup.closure_le ZY).2 fun g hg => hg.1
  have hcovY : ∀ k ∈ K, ∃ y ∈ Y, y⁻¹ * k ∈ O := by
    intro k hk
    have hcov' : K ≤ Y ⊔ O := by
      have := c.cov
      rwa [Covers3, inf_comm] at this
    exact exists_of_mem_sup_of_le_normalizer (inf_le_left.trans hKO) (hcov' hk)
  have hP1 : ∀ k ∈ K, ∃ z ∈ ZY, z⁻¹ * k ∈ O := by
    intro k hk
    obtain ⟨y, hy, hyo⟩ := hcovY k hk
    have hyK : y ∈ K := hYK hy
    have hX : ∀ b ∈ A, ∀ w ∈ GLAPPrimeCoreOf 3 Y, b * w * b⁻¹ ∈ GLAPPrimeCoreOf 3 Y :=
      fun b hb w hw =>
        (Subgroup.mem_normalizer_iff.1
          (le_normalizer_glaPPrimeCoreOf_of_le' (p := 3) hBY (hAB b hb).1) w).1 hw
    have hg : ∀ b ∈ A, y⁻¹ * (b * y * b⁻¹) ∈ GLAPPrimeCoreOf 3 Y := by
      intro b hb
      rw [hOY]
      refine ⟨Y.mul_mem (Y.inv_mem hy)
        ((Subgroup.mem_normalizer_iff.1 (hBY (hAB b hb).1) y).1 hy), ?_⟩
      have h1 := (Subgroup.mem_normalizer_iff.1 (hKO (K.inv_mem hyK)) _).1
        ((hAB b hb).2 y hyK)
      have e : y⁻¹ * (b * y * b⁻¹) = y⁻¹ * (b * y * b⁻¹ * y⁻¹) * y⁻¹⁻¹ := by group
      rw [e]
      exact h1
    obtain ⟨z', hz', hfix⟩ := exists_mul_mem_fixed_of_coset (p := 3) hAp hX
      (not_dvd_card_glaPPrimeCoreOf Nat.prime_three Y) hg
    rw [hOY] at hz'
    refine ⟨y * z', ⟨Y.mul_mem hy hz'.1, ?_⟩, ?_⟩
    · show _ ∈ Subgroup.centralizer (A : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have := hfix h hh
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    · have e : (y * z')⁻¹ * k = z'⁻¹ * (y⁻¹ * k) := by group
      rw [e]
      exact O.mul_mem (O.inv_mem hz'.2) hyo
  have hJN : J₁ ≤ N := (hJZY.trans hZYY).trans inf_le_right
  have hJC : J₁ ≤ Subgroup.centralizer (A : Set G) := hJZY.trans inf_le_right
  have hYcov : Y ≤ K0 ⊔ GLAPPrimeCoreOf 3 Y := by
    intro y hy
    have hle : barX 3 Y Y ≤ barX 3 Y K0 := by rw [barX_self, hbar]
    obtain ⟨j, hj, hjo⟩ := exists_of_barX_le hle hy hy
    simpa using Subgroup.mul_mem_sup hj hjo
  have hJK0 : J₁ ≤ K0 := by
    refine (Subgroup.closure_le K0).2 fun g hg => ?_
    exact mem_layer_of_isPGroup Nat.prime_three hYcov (hZYY hg.1) hg.2
  have hP3 : K ≤ J₁ ⊔ O := by
    have hZYK : ZY ≤ K := hZYY.trans hYK
    have htop : barX 3 K ZY = ⊤ := by
      rw [eq_top_iff, ← barX_self 3 K]
      exact barX_le_of_forall hZYK hP1
    have hs0 := (isSimpleGroup_of_isLThreeFour c.hf.lThreeFour).1
    have hsimple : IsSimpleGroup ↥(barX 3 K ZY) := by
      rw [htop]
      exact Subgroup.topEquiv.isSimpleGroup_congr.2 hs0
    have hdiv : 3 ∣ Nat.card (barX 3 K ZY) := by
      rw [htop, Subgroup.card_top, card_eq_of_isLThreeFour c.hf.lThreeFour]
      norm_num
    have heq := barX_closure_three_eq hZYK hsimple hdiv
    rw [htop] at heq
    intro k hk
    have hle : barX 3 K K ≤ barX 3 K J₁ := by rw [barX_self, heq]
    obtain ⟨j, hj, hjo⟩ := exists_of_barX_le hle hk hk
    simpa using Subgroup.mul_mem_sup hj hjo
  have hK0K : K0 ≤ K := (glaPLayer_le 3 Y).trans hYK
  have hP4 : K0 ≤ J₁ ⊔ GLAPPrimeCoreOf 3 K0 := le_sup_glaPPrimeCoreOf_of_le hJK0 hK0K hP3
  refine ⟨J₁, hJN, hJK0, hJC, hP4, fun a ha ha1 => ?_⟩
  set JG := kZeroOf B K with hJG
  set ZK : Subgroup G := K ⊓ Subgroup.centralizer (A : Set G) with hZK
  have hJGdef : JG = GLAPLayer 3 ZK := rfl
  have hIa := c.hf.ia a ha ha1
  have hxA : x ∈ A := mem_centralizerQuot_of_le_centralizer c.hxB c.hxK.1
  have hix := c.hf.ia x hxA c.hx1
  have hIx : bClosureIa K x = K := bClosureIa_eq_of_component c.hxK c.hf.lThreeFour hix
  have hKJG : K ≤ JG ⊔ O := by
    have := hix.le_kZero_sup
    rwa [hIx] at this
  have hZKK : ZK ≤ K := inf_le_left
  have hJGZK : JG ≤ ZK := glaPLayer_le 3 ZK
  have hJGK : JG ≤ K := hJGZK.trans hZKK
  have hZKcov : ZK ≤ JG ⊔ GLAPPrimeCoreOf 3 ZK := le_sup_glaPPrimeCoreOf_of_le hJGZK hZKK hKJG
  have hJJG : J₁ ≤ JG := by
    refine (Subgroup.closure_le JG).2 fun g hg => ?_
    have hgZK : g ∈ ZK := ⟨hYK hg.1.1, hg.1.2⟩
    rw [hJGdef]
    exact mem_layer_of_isPGroup Nat.prime_three (hJGdef ▸ hZKcov) hgZK hg.2
  refine ⟨hJJG.trans hIa.kZero_le, ?_⟩
  have hV : JG ⊓ O ≤ GLAPPrimeCoreOf 3 (bClosureIa K a) := by
    refine le_glaPPrimeCoreOf_of_normal_of_cover Nat.prime_three hIa.kZero_le hIa.le_kZero_sup
      (isSimpleGroup_of_isLThreeFour hIa.lThreeFour).1 ?_ inf_le_left ?_ ?_
    · rw [card_eq_of_isLThreeFour hIa.lThreeFour]
      norm_num
    · intro g hg
      exact Sec7.inf_normalizer_le_normalizer_inf JG O
        ⟨Subgroup.le_normalizer hg, hKO (hJGK hg)⟩
    · intro h
      exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
        (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hJGle : JG ≤ J₁ ⊔ GLAPPrimeCoreOf 3 (bClosureIa K a) := by
    intro g hg
    obtain ⟨j, hj, hjo⟩ := exists_of_mem_sup_of_le_normalizer
      ((hJK0.trans hK0K).trans hKO) (hP3 (hJGK hg))
    have h1 : j⁻¹ * g ∈ GLAPPrimeCoreOf 3 (bClosureIa K a) :=
      hV ⟨JG.mul_mem (JG.inv_mem (hJJG hj)) hg, hjo⟩
    simpa using Subgroup.mul_mem_sup hj h1
  exact hIa.le_kZero_sup.trans (sup_le hJGle le_sup_right)

end Ctx75

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
