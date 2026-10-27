module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieWit
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieBlock
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Certificates.Kernel.Spor.ONKSound
public import CFSG.Foundations
public import CFSG.LieType.Multipliers.U62Sylow

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL)
open CFSG.GroupTheory.WeirSylow (IsPlusType natCard_orthogonalGroup_of_type)
open CFSG.ComponentClassification.HarrisLit.T1.P51e (IsPrimDiv exists_isPrimDiv
  cast_prod_pow_sub_one)

section Orders

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem natCard_orth_plus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hdim : Module.finrank K V = 2 * (m + 1)) (hplus : IsPlusType Q) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * Nat.card K ^ (m * (m + 1)) *
      (Nat.card K ^ (m + 1) - 1) * ∏ i ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * i) - 1) := by
  have h := natCard_orthogonalGroup_of_type hQ hdim (Or.inl ⟨rfl, hplus⟩)
  rw [← cast_prod_pow_sub_one (Nat.card K) m Nat.card_pos] at h
  have h1 : ((Nat.card K ^ (m + 1) - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ (m + 1) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow (m + 1) (Nat.card K) Nat.card_pos), Nat.cast_pow,
      Nat.cast_one]
  rw [← h1] at h
  exact_mod_cast h

theorem natCard_orth_minus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hdim : Module.finrank K V = 2 * (m + 1)) (hplus : ¬ IsPlusType Q) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * Nat.card K ^ (m * (m + 1)) *
      (Nat.card K ^ (m + 1) + 1) * ∏ i ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * i) - 1) := by
  have h := natCard_orthogonalGroup_of_type hQ hdim (Or.inr ⟨rfl, hplus⟩)
  rw [← cast_prod_pow_sub_one (Nat.card K) m Nat.card_pos, sub_neg_eq_add] at h
  exact_mod_cast h

end Orders

theorem dvd_cases_of_dvd_orth {p f m M ℓ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hM : 2 ≤ M)
    (hℓ : IsPrimDiv ℓ p M) {ε : Bool}
    (h : ℓ ∣ 2 * (p ^ f) ^ (m * (m + 1)) * (if ε then (p ^ f) ^ (m + 1) - 1
      else (p ^ f) ^ (m + 1) + 1) * ∏ i ∈ Finset.Icc 1 m, ((p ^ f) ^ (2 * i) - 1)) :
    (∃ i ∈ Finset.Icc 1 m, M ∣ f * (2 * i)) ∨ (ε ∧ M ∣ f * (m + 1)) ∨
      (¬ ε ∧ M ∣ 2 * (f * (m + 1))) := by
  have hp0 : 0 < p := hp.pos
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hℓ2 : ℓ ≠ 2 := hℓ.ne_two hodd hM
  rcases (Nat.Prime.dvd_mul hℓ.1).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hℓ.1).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hℓ.1).1 h2 with h3 | h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ.1 Nat.prime_two).1 h3) hℓ2
      · rw [← pow_mul] at h3
        exact absurd h3 (hℓ.not_dvd_pow_base hp0 (by omega) _)
    · cases ε
      · exact Or.inr (Or.inr ⟨by simp, hℓ.dvd_of_dvd_pow_pow_add_one hp0 (by omega) h2⟩)
      · exact Or.inr (Or.inl ⟨rfl, (hℓ.dvd_pow_pow_sub_one_iff hp0 (by omega) f _).1 h2⟩)
  · obtain ⟨i, hi, hdi⟩ := P51e.exists_mem_dvd_of_dvd_prod hℓ.1 h1
    exact Or.inl ⟨i, hi, (hℓ.dvd_pow_pow_sub_one_iff hp0 (by omega) f _).1 hdi⟩

theorem index_le_of_dvd_orth {p f m D ℓ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 0 < f)
    (hD : 1 ≤ D) (hm : 1 ≤ m) (hℓ : IsPrimDiv ℓ p (2 * f * D)) {ε : Bool}
    (h : ℓ ∣ 2 * (p ^ f) ^ (m * (m + 1)) * (if ε then (p ^ f) ^ (m + 1) - 1
      else (p ^ f) ^ (m + 1) + 1) * ∏ i ∈ Finset.Icc 1 m, ((p ^ f) ^ (2 * i) - 1)) :
    D ≤ m + 1 ∧ (ε → D ≤ m) := by
  have hM : 2 ≤ 2 * f * D := le_trans (by norm_num : 2 ≤ 2 * 1 * 1)
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hf) hD)
  have hcancel : ∀ {x y : ℕ}, 0 < y → 2 * f * D ∣ f * y → 2 * D ≤ y := fun {x y} hy hd => by
    have h1 : f * (2 * D) ≤ f * y := by
      rw [show f * (2 * D) = 2 * f * D by ring]
      exact Nat.le_of_dvd (Nat.mul_pos hf hy) hd
    exact Nat.le_of_mul_le_mul_left h1 hf
  rcases dvd_cases_of_dvd_orth hp hp2 hM hℓ h with ⟨i, hi, hdi⟩ | ⟨hε, hdi⟩ | ⟨hε, hdi⟩
  · have hi' := Finset.mem_Icc.1 hi
    have := hcancel (x := 0) (by omega) hdi
    exact ⟨by omega, fun _ => by omega⟩
  · have := hcancel (x := 0) (by omega) hdi
    exact ⟨by omega, fun _ => by omega⟩
  · have h1 : 2 * f * D ∣ f * (2 * (m + 1)) := by
      rw [show f * (2 * (m + 1)) = 2 * (f * (m + 1)) by ring]
      exact hdi
    have := hcancel (x := 0) (by omega) h1
    exact ⟨by omega, fun h' => absurd h' hε⟩

theorem false_of_minus_psl_le {q a X P : ℕ} (hq : 3 ≤ q) (ha : 4 ≤ a) (hX : 0 < X) (hP : 0 < P)
    (h : X * (P * ((q ^ 2) ^ a - 1)) ≤ a * (2 * X * (q ^ a + 1) * ((q ^ 2 - 1) * P))) :
    False := by
  have h3 : ∀ b : ℕ, 4 ≤ b → 2 * b + 1 ≤ 3 ^ (b - 2) := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base => norm_num
    | succ b hb ih =>
      rw [show b + 1 - 2 = (b - 2) + 1 by omega, pow_succ]
      omega
  have hqa : q ^ a = q ^ 2 * q ^ (a - 2) := by rw [← pow_add]; congr 1; omega
  have hqa2 : (2 * a + 1) * q ^ 2 ≤ q ^ a := by
    rw [hqa, mul_comm]
    refine Nat.mul_le_mul_left _ ((h3 a ha).trans (Nat.pow_le_pow_left hq _))
  have hsq : (q ^ 2) ^ a - 1 = (q ^ a - 1) * (q ^ a + 1) := by
    rw [← pow_mul, mul_comm 2 a, pow_mul]
    have : 1 ≤ q ^ a := Nat.one_le_pow _ _ (by omega)
    zify [this, Nat.one_le_pow 2 (q ^ a) this]
    ring
  rw [hsq] at h
  have h' : (X * P * (q ^ a + 1)) * (q ^ a - 1) ≤
      (X * P * (q ^ a + 1)) * (2 * a * (q ^ 2 - 1)) := by
    calc (X * P * (q ^ a + 1)) * (q ^ a - 1) = X * (P * ((q ^ a - 1) * (q ^ a + 1))) := by ring
      _ ≤ a * (2 * X * (q ^ a + 1) * ((q ^ 2 - 1) * P)) := h
      _ = (X * P * (q ^ a + 1)) * (2 * a * (q ^ 2 - 1)) := by ring
  have h2 := Nat.le_of_mul_le_mul_left h' (by positivity)
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa1 : 1 ≤ q ^ a := Nat.one_le_pow _ _ (by omega)
  have h5 : 9 ≤ q ^ 2 := by nlinarith
  zify [hq2, hqa1] at h2
  have h6 : ((2 * a + 1 : ℕ) : ℤ) * (q : ℤ) ^ 2 ≤ (q : ℤ) ^ a := by exact_mod_cast hqa2
  have h5' : (9 : ℤ) ≤ (q : ℤ) ^ 2 := by exact_mod_cast h5
  push_cast at h6
  nlinarith

theorem not_dvd_add_one_of_isPrimDiv {p M ℓ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hM : 2 ≤ M)
    (hℓ : IsPrimDiv ℓ p M) : ¬ ℓ ∣ p ^ M + 1 := by
  intro h
  have h1 : 1 ≤ p ^ M := Nat.one_le_pow _ _ hp.pos
  have h2 : ℓ ∣ (p ^ M + 1) - (p ^ M - 1) := Nat.dvd_sub h hℓ.2.1
  rw [show p ^ M + 1 - (p ^ M - 1) = 2 by omega] at h2
  exact hℓ.ne_two (hp.odd_of_ne_two hp2) hM ((Nat.prime_dvd_prime_iff_eq hℓ.1 Nat.prime_two).1 h2)

theorem false_of_odd_psl_block {p f m NY NO X : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 0 < f)
    (hodd : Odd (m + 1)) (hm : 2 ≤ m)
    (hord : NY * Nat.gcd (m + 1) (p ^ (2 * f) - 1) =
      X * ∏ i ∈ Finset.Icc 2 (m + 1), ((p ^ (2 * f)) ^ i - 1))
    (hdvd : ∀ ℓ, ℓ ∣ NY → ℓ ∣ NO)
    (hO : NO = 2 * (p ^ f) ^ (m * (m + 1)) * ((p ^ f) ^ (m + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 m, ((p ^ f) ^ (2 * i) - 1)) : False := by
  have hp0 : 0 < p := hp.pos
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_isPrimDiv (show 3 ≤ p by have := hp.two_le; omega)
    (show 3 ≤ f * (m + 1) by nlinarith)
  have hc1 : ℓ₁ ∣ ∏ i ∈ Finset.Icc 2 (m + 1), ((p ^ (2 * f)) ^ i - 1) := by
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun i => (p ^ (2 * f)) ^ i - 1)
      (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩))
    rw [hℓ₁.dvd_pow_pow_sub_one_iff hp0 (by positivity)]
    exact ⟨2, by ring⟩
  have hd1 : ¬ ℓ₁ ∣ Nat.gcd (m + 1) (p ^ (2 * f) - 1) := by
    intro hd
    have h1 := (hℓ₁.dvd_iff hp0 (by positivity) (2 * f)).1 (hd.trans (Nat.gcd_dvd_right _ _))
    obtain ⟨j, hj⟩ := h1
    have h2 : (m + 1) * j = 2 := by
      have : f * ((m + 1) * j) = f * 2 := by rw [← mul_assoc, ← hj]; ring
      exact Nat.eq_of_mul_eq_mul_left hf this
    have hj1 : j ≠ 0 := by
      rintro rfl
      simp at h2
    have := Nat.le_mul_of_pos_right (m + 1) (Nat.pos_of_ne_zero hj1)
    omega
  have hY1 : ℓ₁ ∣ NY := by
    have h1 : ℓ₁ ∣ NY * Nat.gcd (m + 1) (p ^ (2 * f) - 1) := by
      rw [hord]
      exact Dvd.dvd.mul_left hc1 _
    exact ((Nat.Prime.dvd_mul hℓ₁.1).1 h1).resolve_right hd1
  have hO1 := hdvd ℓ₁ hY1
  rw [hO] at hO1
  have hM2 : 2 ≤ f * (m + 1) := by nlinarith
  have hℓ₁2 : ℓ₁ ≠ 2 := hℓ₁.ne_two (hp.odd_of_ne_two hp2) hM2
  rcases (Nat.Prime.dvd_mul hℓ₁.1).1 hO1 with h1 | h1
  · rcases (Nat.Prime.dvd_mul hℓ₁.1).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hℓ₁.1).1 h2 with h3 | h3
      · exact hℓ₁2 ((Nat.prime_dvd_prime_iff_eq hℓ₁.1 Nat.prime_two).1 h3)
      · rw [← pow_mul] at h3
        exact hℓ₁.not_dvd_pow_base hp0 (by positivity) _ h3
    · rw [← pow_mul] at h2
      exact not_dvd_add_one_of_isPrimDiv hp hp2 hM2 hℓ₁ h2
  · obtain ⟨i, hi, hdi⟩ := P51e.exists_mem_dvd_of_dvd_prod hℓ₁.1 h1
    obtain ⟨j, hj⟩ := (hℓ₁.dvd_pow_pow_sub_one_iff hp0 (by positivity) f _).1 hdi
    have h3 : 2 * i = (m + 1) * j := by
      have : f * (2 * i) = f * ((m + 1) * j) := by rw [hj]; ring
      exact Nat.eq_of_mul_eq_mul_left hf this
    have hi' := Finset.mem_Icc.1 hi
    obtain ⟨r, hr⟩ := hodd
    rcases j with _ | _ | j
    · omega
    · omega
    · have : (m + 1) * 2 ≤ (m + 1) * (j + 1 + 1) := Nat.mul_le_mul_left (m + 1) (by omega)
      omega

theorem false_of_even_psl_block {q m NY : ℕ} (hq3 : 3 ≤ q) (hev : Even (m + 1)) (hm : 3 ≤ m)
    (hord : NY * Nat.gcd (m + 1) (q ^ 2 - 1) = (q ^ 2) ^ ((m + 1) * (m + 1 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 (m + 1), ((q ^ 2) ^ i - 1))
    (hYO : NY ≤ 2 * q ^ (m * (m + 1)) * (q ^ (m + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1)) : False := by
  have hPpos : 0 < ∏ i ∈ Finset.Icc 2 m, (q ^ (2 * i) - 1) := Finset.prod_pos fun i hi => by
    have h1 : q ^ 2 ≤ q ^ (2 * i) :=
      Nat.pow_le_pow_right (by omega) (by have := (Finset.mem_Icc.1 hi).1; omega)
    have h2 : 9 ≤ q ^ 2 := by nlinarith
    omega
  have hXN : (q ^ 2) ^ ((m + 1) * (m + 1 - 1) / 2) = q ^ (m * (m + 1)) := by
    rw [← pow_mul]
    congr 1
    rw [Nat.add_sub_cancel, mul_comm (m + 1) m]
    obtain ⟨j, hj⟩ := hev
    rw [hj, show m * (j + j) = 2 * (m * j) by ring, Nat.mul_div_cancel_left _ two_pos]
  have htop : ∏ i ∈ Finset.Icc 2 (m + 1), ((q ^ 2) ^ i - 1) =
      (∏ i ∈ Finset.Icc 2 m, (q ^ (2 * i) - 1)) * ((q ^ 2) ^ (m + 1) - 1) := by
    rw [Finset.prod_Icc_succ_top (by omega)]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul]
  have hbot : ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) =
      (q ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 m, (q ^ (2 * i) - 1) := by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega : 1 ≤ m),
      Finset.prod_insert (by simp)]
    rfl
  refine false_of_minus_psl_le hq3 (by omega : 4 ≤ m + 1)
    (by positivity : 0 < q ^ (m * (m + 1))) hPpos ?_
  calc q ^ (m * (m + 1)) * ((∏ i ∈ Finset.Icc 2 m, (q ^ (2 * i) - 1)) *
        ((q ^ 2) ^ (m + 1) - 1))
      = NY * Nat.gcd (m + 1) (q ^ 2 - 1) := by rw [hord, hXN, htop]
    _ ≤ NY * (m + 1) := Nat.mul_le_mul_left _ (Nat.gcd_le_left _ (by omega))
    _ ≤ (2 * q ^ (m * (m + 1)) * (q ^ (m + 1) + 1) *
          ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1)) * (m + 1) := Nat.mul_le_mul_right _ hYO
    _ = (m + 1) * (2 * q ^ (m * (m + 1)) * (q ^ (m + 1) + 1) *
          ((q ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 m, (q ^ (2 * i) - 1))) := by rw [hbot]; ring

variable {K : Type} [Field K] [Finite K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

include hw in
theorem eq_two_of_lieModel_block (hO : LieOrderFormulasInput) (hK : ringChar K ≠ 2) {p f : ℕ}
    (hp : p.Prime) (hKc : Nat.card K = p ^ f) {I : Finset (Fin d)} (hIc : Iᶜ.Nonempty)
    (hNF : BlockNF w I) (hq : IsQuasisimple (blockP K hw I)) {a : ℕ} (ha : I.card = 2 * a)
    (ha2 : 2 ≤ a) {τ : StatedLieTag} {n : ℕ}
    (hY : Blueprint.LieModel (↥(blockP K hw I) ⧸ center ↥(blockP K hw I)) τ n p (2 * f)) :
    a = 2 ∧ ¬ IsPlusType (CatalogueBLinearHigherB.matrixQuadraticForm
      (diagGL (wRes_ne_zero hw I))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp2, hf⟩ := GSThmB.QPUCl.prime_ne_two_and_one_le hK hp hKc
  have hp0 : 0 < p := hp.pos
  have hadm := LieType.Steinberg.CentralExt.GriessNative.admissible_of_lieModel hY
  obtain ⟨-, hord, hfac⟩ := hO _ τ n p (2 * f) hadm hY
  rw [lieOrderNumerator_eq hadm] at hord
  have := GSThmB.QPUCl.finite_linearEquiv K I.card
  have hR : ((diagGL (wRes_ne_zero hw I) : GL (Fin I.card) K) :
      Matrix (Fin I.card) (Fin I.card) K)ᵀ = diagGL (wRes_ne_zero hw I) := by
    rw [coe_diagGL]
    exact diagonal_transpose _
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK _ hR
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm (diagGL (wRes_ne_zero hw I)) with hQdef
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  have hdim : Module.finrank K (Fin I.card → K) = 2 * (m + 1) := by
    rw [Module.finrank_fin_fun, ha]
  have hcardP := GSThmB.QPUCl.card_blockP_eq hK hw hIc
  have hns : ¬ Group.IsSolvable (blockP K hw I) := by
    intro hs
    have : Group.IsPerfect (blockP K hw I) := hq.1
    have : Nontrivial (blockP K hw I) := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      exact hq.2.2.elim fun a ha => ha.elim fun b hb => hb (Subsingleton.elim _ _)
    exact Group.IsPerfect.not_isSolvable _ hs
  obtain ⟨b, hb⟩ : ∃ b, Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 ^ b * Nat.card (blockP K hw I) := by
    rcases P51e.orth_index_cases hK hQnd (by omega) with ⟨b, hb⟩ | h
    · exact ⟨b, by rw [hb, hcardP]⟩
    · refine absurd (isSolvable_of_prime_dvd_two_three fun ℓ hℓ hd => h ℓ hℓ ?_) hns
      rw [hcardP] at hd
      exact hd.trans (Subgroup.card_subgroup_dvd_card _)
  have hZ2 : IsPGroup 2 (center (blockP K hw I)) := by
    intro z
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact sq_eq_one_of_mem_center_blockP hw hK hIc hNF z.2
  obtain ⟨c, hc⟩ := (IsPGroup.iff_card).1 hZ2
  have hOY : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 ^ (b + c) *
      Nat.card (↥(blockP K hw I) ⧸ center ↥(blockP K hw I)) := by
    rw [hb, Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(blockP K hw I)), hc,
      pow_add]
    ring
  have hfacO := GSThmB.QPUCl.factorization_card_orthogonalGroup hK hp hKc hQnd (by omega)
  rw [hdim, hOY, GSThmB.QPUCl.factorization_two_pow_mul hp2 _ _ Nat.card_pos.ne', hfac] at hfacO
  have he : (2 * (m + 1) - 1) ^ 2 / 4 = m * (m + 1) := by
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega,
      show (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 by ring]
    omega
  rw [he] at hfacO
  have hN : 2 * lieSylowExponent τ n = (m + 1) * m := by
    have h1 : f * (2 * lieSylowExponent τ n) = f * ((m + 1) * m) := by
      rw [← mul_assoc, mul_comm f 2, mul_assoc, mul_comm 2 (f * _)]
      linear_combination hfacO
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  obtain ⟨D, ℓ, hD2, hℓ, hℓY, hND, hNDeq⟩ := exists_witness_index hO hp2 (by omega) hadm hY
  have hℓO : ℓ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [hOY]
    exact Dvd.dvd.mul_left hℓY _
  have hfD : 0 < f := by omega
  by_cases hplus : IsPlusType Q
  · exfalso
    rw [natCard_orth_plus hQnd hdim hplus, hKc] at hℓO
    have hDm : D ≤ m :=
      (index_le_of_dvd_orth (ε := true) hp hp2 hfD (by omega) (by omega) hℓ
        (by simpa using hℓO)).2 rfl
    have h1 : D * (D - 1) ≤ m * (m - 1) := Nat.mul_le_mul hDm (by omega)
    have h2 : m * (m - 1) < (m + 1) * m := by
      rw [mul_comm (m + 1)]
      exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega
  · rw [natCard_orth_minus hQnd hdim hplus, hKc] at hℓO
    have hDa : D ≤ m + 1 :=
      (index_le_of_dvd_orth (ε := false) hp hp2 hfD (by omega) (by omega) hℓ
        (by simpa using hℓO)).1
    have hDeq : D = m + 1 := by
      by_contra hne
      have hlt : D ≤ m := by omega
      have h1 : D * (D - 1) ≤ m * (m - 1) := Nat.mul_le_mul hlt (by omega)
      have h2 : m * (m - 1) < (m + 1) * m := by
        rw [mul_comm (m + 1)]
        exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      omega
    subst hDeq
    obtain ⟨rfl, rfl⟩ := hNDeq (by rw [hN, Nat.add_sub_cancel])
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · exact ⟨by omega, hplus⟩
    exfalso
    change Nat.card (↥(blockP K hw I) ⧸ center ↥(blockP K hw I)) *
        Nat.gcd (m + 1) (p ^ (2 * f) - 1) =
      (p ^ (2 * f)) ^ ((m + 1) * (m + 1 - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 (m + 1), ((p ^ (2 * f)) ^ i - 1) at hord
    rcases Nat.even_or_odd (m + 1) with hev | hodd
    ·
      have hYO : Nat.card (↥(blockP K hw I) ⧸ center ↥(blockP K hw I)) ≤
          Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
        rw [hOY]
        exact Nat.le_mul_of_pos_left _ (by positivity)
      have hO' := natCard_orth_minus hQnd hdim hplus
      rw [hKc] at hO'
      have hq2 : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [hq2] at hord
      have hq3 : 3 ≤ p ^ f := by
        have h3p : 3 ≤ p := by have := hp.two_le; omega
        calc 3 ≤ p ^ 1 := by rw [pow_one]; exact h3p
          _ ≤ p ^ f := Nat.pow_le_pow_right hp0 hf
      rw [hO'] at hYO
      have hm3 : 3 ≤ m := by obtain ⟨j, hj⟩ := hev; omega
      exact false_of_even_psl_block hq3 hev hm3 hord hYO
    ·
      refine false_of_odd_psl_block (NO := Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q))
        hp hp2 hfD hodd hm2 hord (fun ℓ hℓ => ?_)
        (by rw [natCard_orth_minus hQnd hdim hplus, hKc])
      rw [hOY]
      exact Dvd.dvd.mul_left hℓ _

end CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie
