module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1CoreAlmost
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L28AutThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3L28
import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCountP27
import CFSG.Walter.W67.Section5.P56R1512

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K278

open CFSG.Open Subgroup
open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open scoped MatrixGroups

theorem mul_pow_three_of_card {P : Type} [Group P] (hP : Nat.card P = 27) (x y : P) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  by_cases hna : ∃ a b : P, a * b ≠ b * a
  · exact CFSG.RankThree.PartTwo.Sec4.RonanK432.mul_pow_three_of_card_27 hP hna x y
  · push Not at hna
    exact (Commute.mul_pow (hna x y) 3)

variable {G : Type} [Group G] [Finite G]

theorem false_of_two_planes {R A B : Subgroup G} (hR : IsPGroup 3 R) (hR27 : Nat.card R ≤ 27)
    (hAR : A ≤ R) (hBR : B ≤ R) (hA : ∀ a ∈ A, a ^ 3 = 1) (hB : ∀ b ∈ B, b ^ 3 = 1)
    (hA9 : Nat.card A = 9) (hB9 : Nat.card B = 9) (hAB : A ≠ B) {t : G} (htR : t ∈ R)
    (ht : t ^ 3 ≠ 1) : False := by
  have hBA : ¬ B ≤ A := fun h => hAB (eq_of_le_of_card_ge h (by rw [hA9, hB9])).symm
  have hsupR : A ⊔ B ≤ R := sup_le hAR hBR
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (hk ▸ card_dvd_of_le hsupR : Nat.card (A ⊔ B : Subgroup G) ∣ 3 ^ k)
  have h9 : 9 ∣ Nat.card (A ⊔ B : Subgroup G) := hA9 ▸ card_dvd_of_le le_sup_left
  have hne9 : Nat.card (A ⊔ B : Subgroup G) ≠ 9 := by
    intro h
    apply hBA
    have : A = A ⊔ B := eq_of_le_of_card_ge le_sup_left (by rw [h, hA9])
    rw [this]
    exact le_sup_right
  have hj3 : j = 3 := by
    rw [hjc] at h9 hne9
    have hj2 : 2 ≤ j := by
      by_contra h
      interval_cases j <;> norm_num at h9
    have : j ≠ 2 := by
      rintro rfl
      norm_num at hne9
    omega
  have hR27' : Nat.card R = 27 := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) (show j ≤ k from hj)
    rw [hj3] at this
    omega
  have hsup : A ⊔ B = R := eq_of_le_of_card_ge hsupR (by rw [hR27', hjc, hj3]; norm_num)
  let φ : R →* R := MonoidHom.mk' (fun x => x ^ 3) (mul_pow_three_of_card hR27')
  have hle : A ⊔ B ≤ φ.ker.map R.subtype := by
    refine sup_le ?_ ?_
    · intro a ha
      refine ⟨⟨a, hAR ha⟩, ?_, rfl⟩
      show φ ⟨a, hAR ha⟩ = 1
      exact Subtype.ext (by simpa [φ] using hA a ha)
    · intro b hb
      refine ⟨⟨b, hBR hb⟩, ?_, rfl⟩
      show φ ⟨b, hBR hb⟩ = 1
      exact Subtype.ext (by simpa [φ] using hB b hb)
  rw [hsup] at hle
  obtain ⟨t', ht', rfl⟩ := hle htR
  apply ht
  have h1 : φ t' = 1 := ht'
  have := congrArg Subtype.val h1
  simpa [φ] using this

variable {X : Type} [Group X] [Finite X]

theorem exists_pow_three_ne_one_of_psl28 (R : Sylow 3 X) {K : Subgroup X}
    (e : K ≃* PSL(2, GaloisField 2 3)) : ∃ t ∈ (R : Subgroup X), t ^ 3 ≠ 1 := by
  by_contra hno
  push Not at hno
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 3 K) := inferInstance
  have hcyc : IsCyclic (P₀ : Subgroup K) := by
    have h1 := CFSG.Walter.W67.Sec56.psl28_sylow_three_cyclic
      (P₀.mapSurjective (f := e.toMonoidHom) e.surjective)
    have hcoe : ((P₀.mapSurjective (f := e.toMonoidHom) e.surjective :
        Sylow 3 PSL(2, GaloisField 2 3)) : Subgroup PSL(2, GaloisField 2 3)) =
        (P₀ : Subgroup K).map e.toMonoidHom :=
      Sylow.coe_mapSurjective e.surjective P₀
    have h2 : IsCyclic ↥((P₀ : Subgroup K).map e.toMonoidHom) := by
      rw [← hcoe]
      exact h1
    exact (equivMapOfInjective (P₀ : Subgroup K) e.toMonoidHom e.injective).isCyclic.mpr h2
  have hexp : ∀ x ∈ (P₀ : Subgroup K), x ^ 3 = 1 := by
    obtain ⟨Q, hQ⟩ := (P₀.isPGroup'.map K.subtype).exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X R Q
    intro x hx
    have hxQ : (x : X) ∈ (Q : Subgroup X) := hQ ⟨x, hx, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hxQ
    obtain ⟨r, hr, hrx⟩ := hxQ
    have hrx' : g * r * g⁻¹ = (x : X) := by simpa [MulAut.smul_def, MulAut.conj_apply] using hrx
    have hx3 : (x : X) ^ 3 = 1 := by
      rw [← hrx', conj_pow, hno r hr]
      group
    exact Subtype.ext (by simpa using hx3)
  obtain ⟨⟨g, hgP⟩, hgen⟩ := IsCyclic.exists_generator (α := (P₀ : Subgroup K))
  have hcard : Nat.card (P₀ : Subgroup K) ∣ 3 := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hgen]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hexp g hgP))
  have hK504 : Nat.card K = 504 :=
    (Nat.card_congr e.toEquiv).trans CFSG.LocalAnalysis.RankThreeTheoremC.card_psl2_eight
  have hidx := P₀.not_dvd_index
  have hmul := (P₀ : Subgroup K).card_mul_index
  rw [hK504] at hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp hcard with h1 | h3
  · rw [h1] at hmul
    exact hidx ⟨168, by omega⟩
  · rw [h3] at hmul
    exact hidx ⟨56, by omega⟩

theorem card_sylow_le_of_l28 {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (h : D2AlmostSimple 3 X R A X₀ K) (hL : IsCaseTwoGroup 3 K) :
    Nat.card (R : Subgroup X) ≤ 27 := by
  have := h.normal
  obtain ⟨ι, hι, -, -⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.k1Core_exists_action
      h.centralizer_eq_bot (MulEquiv.refl K)
  have h27 := kFactL28AutThree K hL ((R : Subgroup X).map ι) (R.isPGroup'.map ι)
  rwa [card_map_of_injective hι] at h27

theorem false_of_l28 {R : Sylow 3 X} {A X₀ K B : Subgroup X} (h : D2AlmostSimple 3 X R A X₀ K)
    (hL : IsCaseTwoGroup 3 K) (e : K ≃* PSL(2, GaloisField 2 3)) (hBR : B ≤ R)
    (hB : IsElemAbelian 3 B) (hBc : Nat.card B = 9) (hBA : B ≠ A) : False := by
  obtain ⟨t, htR, ht⟩ := exists_pow_three_ne_one_of_psl28 R e
  exact false_of_two_planes R.isPGroup' (card_sylow_le_of_l28 h hL) h.A_le hBR h.elem.2 hB.2
    (by rw [h.card_A]; norm_num) hBc (Ne.symm hBA) htR ht

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K278
