module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallSDClose
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Asc25SD
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Asc25Odd

public section

namespace CFSG.ComponentClassification.Foote5.Asc25

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5.HallGen

variable {G : Type} [Group G] [Finite G]

theorem dihedral_or_semidihedral
    {D : Subgroup G} (hD : AschbacherTheorem3.IsDihedralTwoGroup D) (h8 : 8 ≤ Nat.card D)
    (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d)
    {P : Subgroup G} (hP : IsSylowOf 2 P (normalClosure (D : Set G))) :
    AschbacherTheorem3.IsDihedralTwoGroup P ∨ AschbacherTheorem3.IsSemidihedralTwoGroup P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, ⟨e⟩⟩ := id hD
  have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  obtain ⟨c, hcD, hco, hcard, hDc⟩ := data_of_mulEquiv e
  have hm2 : 2 ≤ n - 1 := by
    by_contra h
    have : 2 ^ (n - 1) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk : 4 ∣ orderOf c := by
    rw [hco, show n - 1 = (n - 3) + 2 by omega, pow_add]
    exact Dvd.intro_left _ rfl
  rw [← hco] at hcard
  have hW : HallWeakConclusion D := by
    rcases (show n - 1 = 2 ∨ 3 ≤ n - 1 by omega) with h2 | h3
    · exact weak_d8 hcD (by rw [hco, h2]; rfl) hcard hDc hcl
    · refine hallWeak G D hD ?_ hcl
      rw [hcard, hco]
      have : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) h3
      omega
  obtain ⟨S₀, T, hT, hDS, hST, hsc, hinv, hcardS⟩ := hW
  have hcases : S₀ = D ∨ Nat.card S₀ = 2 * Nat.card D := by
    obtain ⟨q, hq⟩ := card_dvd_of_le hDS
    have hD0 : 0 < Nat.card D := Nat.card_pos
    rcases q with _ | _ | _ | q
    · rw [mul_zero] at hq
      exact absurd hq (Nat.card_pos (α := S₀)).ne'
    · left
      exact (eq_of_le_of_card_ge hDS (by rw [hq, zero_add, mul_one])).symm
    · right
      rw [hq]
      ring
    · exfalso
      have : Nat.card D * (q + 3) ≤ Nat.card D * 2 := by rw [← hq]; linarith
      have := Nat.le_of_mul_le_mul_left this hD0
      omega
  set T' : Sylow 2 G := Sylow.ofCard T (by rw [hT.card_eq, Subgroup.card_top]) with hT'
  have hT'c : (T' : Subgroup G) = T := Sylow.coe_ofCard _ _
  have hB3 := Goldschmidt75.corollaryB3 T' (by rw [hT'c]; exact hST) (by rw [hT'c]; exact hsc)
    (pow_mem_centralizer hDc hk hco hcD hcard hDS hcardS hinv)
  obtain ⟨hSM, hSp, hSmax⟩ := hB3
  set M := normalClosure (S₀ : Set G) with hM
  set N := normalClosure (D : Set G) with hN
  have hSsyl : IsSylowOf 2 S₀ M := by
    obtain ⟨Q, hQ, hSQ⟩ := FooteLit.exists_isSylowOf_ge_of_le hSM hSp
    rw [← hSmax Q hQ.le hQ.isPGroup hSQ]
    exact hQ
  have hNM : N ≤ M := normalClosure_mono hDS
  have hMN : M ≤ normalizer (N : Set G) := (normalizer_eq_top (H := N)).ge.trans' le_top
  have hSN := hSsyl.inf_of_le_normalizer hNM hMN
  have hDSN : D ≤ S₀ ⊓ N := le_inf hDS subset_normalClosure
  have hcases' : S₀ ⊓ N = D ∨ (S₀ ⊓ N = S₀ ∧ Nat.card S₀ = 2 * Nat.card D) := by
    rcases hcases with h | h
    · left
      exact le_antisymm (h ▸ inf_le_left) hDSN
    · obtain ⟨q, hq⟩ := card_dvd_of_le hDSN
      have hle : Nat.card ↥(S₀ ⊓ N) ≤ Nat.card S₀ := card_le_of_le inf_le_left
      have hD0 : 0 < Nat.card D := Nat.card_pos
      rcases q with _ | _ | _ | q
      · rw [mul_zero] at hq
        exact absurd hq (Nat.card_pos (α := ↥(S₀ ⊓ N))).ne'
      · left
        exact (eq_of_le_of_card_ge hDSN (by rw [hq, zero_add, mul_one])).symm
      · right
        refine ⟨eq_of_le_of_card_ge inf_le_left ?_, h⟩
        rw [h, hq]
        ring_nf
        exact le_rfl
      · exfalso
        have : Nat.card D * (q + 3) ≤ Nat.card D * 2 := by
          rw [h] at hle
          rw [← hq]
          linarith
        have := Nat.le_of_mul_le_mul_left this hD0
        omega
  obtain ⟨g, -, hg⟩ := hSN.exists_mem_conj hP
  have hPmap : P = (S₀ ⊓ N).map (MulAut.conj g).toMonoidHom := by
    ext y
    rw [hg y, mem_map_equiv]
    simp
  have eP : ↥(S₀ ⊓ N) ≃* ↥P :=
    ((S₀ ⊓ N).equivMapOfInjective _ (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hPmap.symm)
  rcases hcases' with h | ⟨h, h2⟩
  · left
    exact ⟨n, hn, ⟨eP.symm.trans ((MulEquiv.subgroupCongr h).trans e)⟩⟩
  · right
    obtain ⟨n', hn', ⟨f⟩⟩ := isSemidihedral_of_inv hDc hco hk hcD hcard hDS h2 hinv
    exact ⟨n', hn', ⟨eP.symm.trans ((MulEquiv.subgroupCongr h).trans f)⟩⟩

end CFSG.ComponentClassification.Foote5.Asc25
