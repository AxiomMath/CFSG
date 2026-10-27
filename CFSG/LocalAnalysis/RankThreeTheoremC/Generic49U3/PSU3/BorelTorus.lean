module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Sylow
public import CFSG.Permutation.UnitaryThreeRecognition.ModelBasic
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open

section Counting

private theorem cube_eq_one_of_eq {E : Type} [Field E] (σ : E ≃+* E) (hσ : Function.Involutive σ)
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x * (σ x)⁻¹ ^ 2 = y * (σ y)⁻¹ ^ 2) : (x / y) ^ 3 = 1 := by
  have hx' : σ x ≠ 0 := (map_ne_zero σ).2 hx
  have hy' : σ y ≠ 0 := (map_ne_zero σ).2 hy
  have h1 : x * σ y ^ 2 = y * σ x ^ 2 := by
    field_simp at h
    linear_combination h
  have h2 : σ x * y ^ 2 = σ y * x ^ 2 := by
    have := congrArg σ h1
    simpa [map_mul, map_pow, hσ x, hσ y] using this
  have h3 : σ x ^ 2 * x * y * (y ^ 3 - x ^ 3) = 0 := by
    linear_combination x * (σ x * y ^ 2 + σ y * x ^ 2) * h2 + x ^ 4 * h1
  have h4 : y ^ 3 - x ^ 3 = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hx') hx) hy)
    · exact h
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 3 hy)]
  linear_combination -h4

private theorem addSubgroup_eq_top_of_closed {E : Type} [Field E] [Finite E] {p : ℕ} [Fact p.Prime]
    (hp : 4 ≤ p) (hE : Nat.card E = p ^ 2) (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (S : AddSubgroup E) {s₀ : E} (hs₀ : s₀ ∈ S) (hne : s₀ ≠ 0)
    (hS : ∀ a ∈ S, ∀ k : Eˣ, a * ((k : E) * (σ (k : E))⁻¹ ^ 2) ∈ S) : S = ⊤ := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  let φ : Eˣ → S := fun k => ⟨s₀ * ((k : E) * (σ (k : E))⁻¹ ^ 2), hS s₀ hs₀ k⟩
  have hfib : ∀ b ∈ (Finset.univ : Finset Eˣ).image φ,
      (Finset.univ.filter fun a : Eˣ => φ a = b).card ≤ 3 := by
    intro b hb
    obtain ⟨k₀, -, rfl⟩ := Finset.mem_image.1 hb
    calc (Finset.univ.filter fun a : Eˣ => φ a = φ k₀).card
        ≤ (Finset.univ.filter fun u : Eˣ => u ^ 3 = 1).card := by
          refine Finset.card_le_card_of_injOn (fun a => a * k₀⁻¹) ?_ ?_
          · intro a ha
            have ha' : φ a = φ k₀ := by simpa using ha
            have h1 := congrArg (fun s : S => (s : E)) ha'
            simp only [φ] at h1
            have h2 := cube_eq_one_of_eq σ hσ a.ne_zero k₀.ne_zero (mul_left_cancel₀ hne h1)
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
            apply Units.ext
            simpa [div_eq_mul_inv] using h2
          · intro a _ b _ hab
            simpa using hab
      _ ≤ 3 := IsCyclic.card_pow_eq_one_le (by norm_num)
  have hcard := Finset.card_le_mul_card_image (f := φ) (Finset.univ : Finset Eˣ) 3 hfib
  have himg : (Finset.univ.image φ).card ≤ Nat.card S := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  have hunits : Fintype.card Eˣ = p ^ 2 - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, hE]
  rw [Finset.card_univ, hunits] at hcard
  have hgt : p < Nat.card S := by
    by_contra hle
    replace hle := not_lt.1 hle
    have : p ^ 2 - 1 ≤ 3 * p := by omega
    have h5 : p ^ 2 ≥ 4 * p := by nlinarith
    omega
  have hdvd : Nat.card S ∣ p ^ 2 := hE ▸ AddSubgroup.card_addSubgroup_dvd_card S
  obtain ⟨i, hi, hiS⟩ := (Nat.dvd_prime_pow Fact.out).1 hdvd
  have hi2 : i = 2 := by
    by_contra hne2
    have : i ≤ 1 := by omega
    have : p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos this
    rw [pow_one] at this
    omega
  apply AddSubgroup.eq_top_of_card_eq
  rw [hE, hiS, hi2]

end Counting

section Model

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

variable {E : Type} [Field E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

private theorem coord_comm_of_fst_zero (z w : Coord J) (hz : z.1.1 = 0) : z * w = w * z := by
  apply Subtype.ext
  rw [coord_mul_val, coord_mul_val]
  ext <;> simp [hz, add_comm]

private theorem root_mem_center_of_fst_zero (z : Coord J) (hz : z.1.1 = 0) :
    root J hJ z ∈ rootGroup J hJ ⊓
      Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  refine ⟨root_mem_rootGroup J hJ z, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  obtain ⟨w, rfl⟩ := (mem_rootGroup J hJ).1 hg
  rw [← map_mul, ← map_mul, coord_comm_of_fst_zero J z w hz]

private def fstSet (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : AddSubgroup E where
  carrier := {a | ∃ w : Coord J, w.1.1 = a ∧ root J hJ w ∈ A}
  zero_mem' := ⟨1, rfl, by rw [map_one]; exact A.one_mem⟩
  add_mem' := by
    rintro _ _ ⟨w, rfl, hw⟩ ⟨w', rfl, hw'⟩
    exact ⟨w * w', rfl, by rw [map_mul]; exact A.mul_mem hw hw'⟩
  neg_mem' := by
    rintro _ ⟨w, rfl, hw⟩
    exact ⟨w⁻¹, rfl, by rw [map_inv]; exact A.inv_mem hw⟩

variable {J hJ} in
private theorem fstSet_mul_mem {A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hinv : ∀ n ∈ Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)), ∀ a ∈ A, n * a * n⁻¹ ∈ A)
    {a : E} (ha : a ∈ fstSet J hJ A) (k : Eˣ) :
    a * ((k : E) * (J.conj (k : E))⁻¹ ^ 2) ∈ fstSet J hJ A := by
  obtain ⟨w, rfl, hw⟩ := ha
  have hn := torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ k)
  have h := hinv _ hn _ hw
  rw [torus_mul_root_mul_inv] at h
  exact ⟨hermitianTorusAction J k w, by rw [torusAction_val, mul_assoc], h⟩

private theorem model_torus_irreducible [Finite E] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hE : Nat.card E = p ^ 2) {A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hAR : A ≤ rootGroup J hJ)
    (hZA : rootGroup J hJ ⊓
      Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ A)
    (hinv : ∀ n ∈ Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)), ∀ a ∈ A, n * a * n⁻¹ ∈ A) :
    A = rootGroup J hJ ⊓
        Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∨
      A = rootGroup J hJ := by
  by_cases hA : A ≤ rootGroup J hJ ⊓
      Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  · exact Or.inl (le_antisymm hA hZA)
  right
  obtain ⟨x, hxA, hxZ⟩ := SetLike.not_le_iff_exists.1 hA
  obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).1 (hAR hxA)
  have hz : z.1.1 ≠ 0 := fun h => hxZ (root_mem_center_of_fst_zero J hJ z h)
  have hz1 : z.1.1 ∈ fstSet J hJ A := ⟨z, rfl, hxA⟩
  have htop : fstSet J hJ A = ⊤ :=
    addSubgroup_eq_top_of_closed (by omega) hE J.conj J.conj_involutive (fstSet J hJ A) hz1 hz
      fun a ha k => fstSet_mul_mem hinv ha k
  apply le_antisymm hAR
  intro g hg
  obtain ⟨w', rfl⟩ := (mem_rootGroup J hJ).1 hg
  obtain ⟨w, hw1, hwA⟩ : w'.1.1 ∈ fstSet J hJ A := htop ▸ AddSubgroup.mem_top _
  have h0 : (w⁻¹ * w').1.1 = 0 := by
    rw [coord_mul_val, coord_inv_val]
    simp [hw1]
  have h1 := hZA (root_mem_center_of_fst_zero J hJ (w⁻¹ * w') h0)
  have h2 : root J hJ w' = root J hJ w * root J hJ (w⁻¹ * w') := by
    rw [← map_mul, mul_inv_cancel_left]
  rw [h2]
  exact A.mul_mem hwA h1

end Model

theorem u3_torus_irreducible {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Group K] [Finite K]
    (hK : IsU3Pred p K) (T : Sylow p K) {A : Subgroup K} (hAT : A ≤ (T : Subgroup K))
    (hZA : (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) ≤ A)
    (hinv : ∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ a ∈ A, n * a * n⁻¹ ∈ A) :
    A = (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) ∨
      A = (T : Subgroup K) := by
  obtain ⟨d, hd, hfe, he⟩ := u3Sylow_index_of_isU3Pred hK
  obtain ⟨-, hf, -, K', _, _, J, hJ, hK', hfix, ⟨e⟩⟩ :=
    CFSG.AGLEmbedding.UnitaryModel.exists_equiv_psu
      (CFSG.AGLEmbedding.UnitaryModel.statedClassicalModel hd he)
  obtain ⟨S, hS⟩ := CFSG.AGLEmbedding.UnitaryModel.exists_sylow_eq_rootGroup J hJ hK' hfix hf
  obtain ⟨e', he'⟩ := CFSG.AGLEmbedding.UnitaryModel.exists_equiv_map_eq e T S
  have hU : (T : Subgroup K).map e'.toMonoidHom =
      CFSG.UnitaryThreeRecognition.Model.rootGroup J hJ := he'.trans hS
  have hN : (Subgroup.normalizer ((T : Subgroup K) : Set K)).map e'.toMonoidHom =
      Subgroup.normalizer (CFSG.UnitaryThreeRecognition.Model.rootGroup J hJ : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  have hE : Nat.card K' = p ^ 2 := by rw [hK', hfe, pow_one]
  have hZ : ((T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K)).map
      e'.toMonoidHom = CFSG.UnitaryThreeRecognition.Model.rootGroup J hJ ⊓
        Subgroup.centralizer
          (CFSG.UnitaryThreeRecognition.Model.rootGroup J hJ : Set _) := by
    ext y
    obtain ⟨x, rfl⟩ := e'.surjective y
    rw [CFSG.AGLEmbedding.UnitaryModel.mem_map_iff, Subgroup.mem_inf, Subgroup.mem_inf, ← hU,
      CFSG.AGLEmbedding.UnitaryModel.mem_map_iff,
      CFSG.AGLEmbedding.UnitaryModel.mem_centralizer_map_iff]
  have hAR : A.map e'.toMonoidHom ≤ CFSG.UnitaryThreeRecognition.Model.rootGroup J hJ :=
    hU ▸ Subgroup.map_mono hAT
  have hZA' : CFSG.UnitaryThreeRecognition.Model.rootGroup J hJ ⊓
      Subgroup.centralizer
        (CFSG.UnitaryThreeRecognition.Model.rootGroup J hJ : Set _) ≤ A.map e'.toMonoidHom :=
    hZ ▸ Subgroup.map_mono hZA
  have hinv' : ∀ n ∈ Subgroup.normalizer
      (CFSG.UnitaryThreeRecognition.Model.rootGroup J hJ : Set _), ∀ a ∈ A.map e'.toMonoidHom,
        n * a * n⁻¹ ∈ A.map e'.toMonoidHom := by
    intro n hn a ha
    rw [← hN] at hn
    obtain ⟨n₀, hn₀, rfl⟩ := Subgroup.mem_map.1 hn
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
    exact Subgroup.mem_map.2 ⟨n₀ * a₀ * n₀⁻¹, hinv n₀ hn₀ a₀ ha₀, by simp⟩
  rcases model_torus_irreducible J hJ hp5 hE hAR hZA' hinv' with h | h
  · left
    exact Subgroup.map_injective e'.injective (h.trans hZ.symm)
  · right
    exact Subgroup.map_injective e'.injective (h.trans hU.symm)

theorem u3_torus_fpf {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Group K] [Finite K]
    (hK : IsU3Pred p K) (T : Sylow p K) {t : K} (htT : t ∈ (T : Subgroup K))
    (h : ∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
      n * t * n⁻¹ * t⁻¹ ∈ (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K)) :
    t ∈ (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) := by
  set Z : Subgroup K := (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K)
    with hZdef
  set A : Subgroup K := Subgroup.closure (insert t (Z : Set K)) with hA
  have hZT : Z ≤ (T : Subgroup K) := inf_le_left
  have hZA : Z ≤ A := fun z hz => Subgroup.subset_closure (Set.mem_insert_of_mem _ hz)
  have htA : t ∈ A := Subgroup.subset_closure (Set.mem_insert _ _)
  have hAT : A ≤ (T : Subgroup K) := by
    rw [hA, Subgroup.closure_le]
    intro x hx
    rcases Set.mem_insert_iff.1 hx with hx | hx
    · rw [hx]; exact htT
    · exact hZT hx
  have hnZ : ∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ z ∈ Z, n * z * n⁻¹ ∈ Z := by
    intro n hn z hz
    refine ⟨(Subgroup.mem_normalizer_iff.1 hn z).1 hz.1,
      Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : n⁻¹ * y * n ∈ (T : Subgroup K) := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) y).1 hy
      simpa using this
    have hcomm := Subgroup.mem_centralizer_iff.1 hz.2 _ hy'
    calc y * (n * z * n⁻¹) = n * ((n⁻¹ * y * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * y * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * z * n⁻¹) * y := by group
  have hinv : ∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ a ∈ A,
      n * a * n⁻¹ ∈ A := by
    intro n hn a ha
    have key : A ≤ A.comap (MulAut.conj n).toMonoidHom := by
      rw [hA, Subgroup.closure_le]
      intro x hx
      rcases Set.mem_insert_iff.1 hx with hx | hx
      · rw [hx]
        have h1 : n * t * n⁻¹ = (n * t * n⁻¹ * t⁻¹) * t := by group
        show n * t * n⁻¹ ∈ A
        rw [h1]
        exact A.mul_mem (hZA (h n hn)) htA
      · exact hZA (hnZ n hn x hx)
    exact key ha
  have hcomm : IsMulCommutative A := by
    refine Subgroup.isMulCommutative_closure ?_
    intro x hx y hy _
    rcases Set.mem_insert_iff.1 hx with hx | hx <;> rcases Set.mem_insert_iff.1 hy with hy | hy
    · rw [hx, hy]
    · rw [hx]
      exact Subgroup.mem_centralizer_iff.1 hy.2 t htT
    · rw [hy]
      exact (Subgroup.mem_centralizer_iff.1 hx.2 t htT).symm
    · exact Subgroup.mem_centralizer_iff.1 hy.2 x (hZT hx)
  have hnc := (u3_sylow_data hp5 hK T).2.2.1
  rcases u3_torus_irreducible hp5 hK T hAT hZA hinv with hAZ | hAT'
  · have hAZ' : A = Z := hAZ
    rw [← hAZ']
    exact htA
  · exact absurd (hAT' ▸ hcomm) hnc

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
