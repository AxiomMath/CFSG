module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneA1

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.PSL2Table CFSG.AGLEmbedding
open scoped MatrixGroups

theorem psl2GF_index_normalizer {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (T : Sylow p (PSL2GF p n)) :
    (Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) : Set (PSL2GF p n))).index = p ^ n + 1 := by
  have hF : ringChar (GaloisField p n) ≠ 2 := by rw [ringChar.eq (GaloisField p n) p]; exact hp2
  obtain ⟨U, hU⟩ := exists_sylow_eq_unipotent_psl2GF hp2 hn
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2GF p n) U T
  have hT : (T : Subgroup (PSL2GF p n)) =
      (unipotent (GaloisField p n)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hU]
    rfl
  have hN : Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) : Set (PSL2GF p n)) =
      (borel (GaloisField p n)).map (MulAut.conj g).toMonoidHom := by
    rw [hT, normalizer_map_conj, normalizer_unipotent_eq_borel hF]
  let : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p n (by omega)
  have h2 : (2 : GaloisField p n) ≠ 0 := Ring.two_ne_zero hF
  have hB := card_borel h2 (F := GaloisField p n)
  have hG := card_PSL h2 (F := GaloisField p n)
  rw [hq] at hB hG
  have hNc : Nat.card (Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) : Set (PSL2GF p n))) =
      Nat.card (borel (GaloisField p n)) := by
    rw [hN, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hmul := Subgroup.index_mul_card
    (Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) : Set (PSL2GF p n)))
  rw [hNc] at hmul
  have hq3 : 3 ≤ p ^ n := by
    have : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      omega
    calc 3 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (Fact.out : p.Prime).ne_zero) hn
  obtain ⟨r, hr⟩ : ∃ r, p ^ n = r + 1 := ⟨p ^ n - 1, by omega⟩
  rw [hr] at hB hG hq3 ⊢
  have e1 : (r + 1) ^ 2 - 1 = r * (r + 2) := by
    have : (r + 1) ^ 2 = r * (r + 2) + 1 := by ring
    omega
  rw [e1] at hG
  have hr0 : 0 < r * (r + 1) := Nat.mul_pos (by omega) (by omega)
  have key : (Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) : Set (PSL2GF p n))).index *
      (r * (r + 1)) = (r + 2) * (r * (r + 1)) := by
    have : 2 * ((Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) :
        Set (PSL2GF p n))).index * Nat.card (borel (GaloisField p n))) =
        2 * Nat.card (PSL2GF p n) := by rw [hmul]
    have h3 : (Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) :
        Set (PSL2GF p n))).index * (Nat.card (borel (GaloisField p n)) * 2) =
        Nat.card (PSL2GF p n) * 2 := by linarith
    rw [hB, hG] at h3
    have e2 : (r + 1 - 1) = r := by omega
    rw [e2] at h3
    calc _ = (Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) : Set (PSL2GF p n))).index *
          (r * (r + 1)) := rfl
      _ = (r + 1) * (r * (r + 2)) := by linarith
      _ = _ := by ring
  have := Nat.eq_of_mul_eq_mul_right hr0 key
  omega

theorem index_normalizer_of_equiv {K : Type} [Group K] [Finite K] {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 1 ≤ n) (e : K ≃* PSL2GF p n) (T : Sylow p K) :
    (Subgroup.normalizer ((T : Subgroup K) : Set K)).index = p ^ n + 1 := by
  have hfs : Function.Surjective (e : K →* PSL2GF p n) := e.surjective
  let T'' : Sylow p (PSL2GF p n) := T.mapSurjective hfs
  have hT'' : (T'' : Subgroup (PSL2GF p n)) = (T : Subgroup K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective hfs T
  have := psl2GF_index_normalizer hp2 hn T''
  rw [hT'', normalizer_map_equiv] at this
  rw [← this]
  exact (Subgroup.index_map_equiv _ e).symm

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
