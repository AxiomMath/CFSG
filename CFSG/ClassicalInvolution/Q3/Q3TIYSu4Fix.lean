module

public import CFSG.ClassicalInvolution.RouteD.TWT4Fix

public section

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits Module
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 (aSU suMat_aSU suMat_blockEmb_zero
  suMat_blockEmb_two suMat_rootInvSU_four)
open CFSG.ClassicalInvolution.RouteD.TWT4

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_norm_one_ne3 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 3 ≤ p ^ f) :
    ∃ c : K, unitaryInvolution K p f c * c = 1 ∧ c * c ≠ 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Fintype.card Kˣ = (p ^ f) ^ 2 - 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard]
  have hq1 : 1 ≤ p ^ f := by omega
  have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq1
  have e1 : (p ^ f - 1) * p ^ f + (p ^ f - 1) = (p ^ f) ^ 2 - 1 := by
    zify [hq1, h1]
    ring
  have e2 : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
    zify [hq1, h1]
    ring
  refine ⟨((g ^ (p ^ f - 1) : Kˣ) : K), ?_, ?_⟩
  · rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_mul,
      ← pow_add, e1, ← hord, pow_orderOf_eq_one, Units.val_one]
  · intro h
    rw [← Units.val_mul, ← pow_add, Units.val_eq_one, ← orderOf_dvd_iff_pow_eq_one, hord] at h
    have h2 : 0 < (p ^ f - 1) + (p ^ f - 1) := by omega
    have h3 := Nat.le_of_dvd h2 h
    rw [e2] at h3
    have h4 : (p ^ f - 1) * (p ^ f + 1) ≥ (p ^ f - 1) * 4 := Nat.mul_le_mul_left _ (by omega)
    omega

theorem su4_block0_shape3 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 3 ≤ p ^ f)
    (w : Su K p f 4)
    (hc : ∀ B : Su K p f 2, blockEmb K p f 4 2 0 (by norm_num) B * w =
      w * blockEmb K p f 4 2 0 (by norm_num) B) :
    suMat w 0 1 = 0 ∧ suMat w 1 0 = 0 ∧ suMat w 0 2 = 0 ∧ suMat w 0 3 = 0 ∧ suMat w 1 2 = 0 ∧
      suMat w 1 3 = 0 ∧ suMat w 2 0 = 0 ∧ suMat w 2 1 = 0 ∧ suMat w 3 0 = 0 ∧
      suMat w 3 1 = 0 ∧ suMat w 0 0 = suMat w 1 1 := by
  have hσσ := (isUnitaryInvolution_unitaryInvolution hK).invol
  obtain ⟨c, hcσ, hc2⟩ := exists_norm_one_ne3 hK hq
  have hab : unitaryInvolution K p f c * c + unitaryInvolution K p f 0 * 0 = 1 := by
    rw [map_zero, mul_zero, add_zero]
    exact hcσ
  have hBm : suMat (aSU K p f hab hσσ) =
      !![c, 0; -unitaryInvolution K p f 0, unitaryInvolution K p f c] := suMat_aSU hab hσσ
  have hσc : unitaryInvolution K p f c ≠ c := fun h => hc2 (by
    have := hcσ
    rw [h] at this
    exact this)
  have hc1 : c ≠ 1 := fun h => hc2 (by rw [h, mul_one])
  have hσc1 : unitaryInvolution K p f c ≠ 1 := fun h => hc1 (by
    have := congrArg (unitaryInvolution K p f) h
    rwa [hσσ, map_one] at this)
  have h := congrArg suMat (hc (aSU K p f hab hσσ))
  rw [suMat_mul, suMat_mul, suMat_blockEmb_zero, hBm] at h
  set s := unitaryInvolution K p f c with hs
  have key : ∀ i j : Fin 4, (![c, s, 1, 1] : Fin 4 → K) i * suMat w i j =
      suMat w i j * (![c, s, 1, 1] : Fin 4 → K) j := by
    intro i j
    have := congrFun (congrFun h i) j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four] at this ⊢ <;> linear_combination this
  have z : ∀ i j : Fin 4, ((![c, s, 1, 1] : Fin 4 → K) i - (![c, s, 1, 1] : Fin 4 → K) j ≠ 0) →
      suMat w i j = 0 := by
    intro i j hne
    have := key i j
    have h0 : ((![c, s, 1, 1] : Fin 4 → K) i - (![c, s, 1, 1] : Fin 4 → K) j) * suMat w i j = 0 :=
      by linear_combination this
    exact (mul_eq_zero.mp h0).resolve_left hne
  have hcs : c - s ≠ 0 := fun h' => hσc (by linear_combination -h')
  have hc1' : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hσc1
  have w01 := z 0 1 (by simpa using hcs)
  have w02 := z 0 2 (by simpa using hc1')
  have w03 := z 0 3 (by simpa using hc1')
  have w10 := z 1 0 (by simpa using (neg_ne_zero.mpr hcs))
  have w12 := z 1 2 (by simpa using hs1')
  have w13 := z 1 3 (by simpa using hs1')
  have w20 := z 2 0 (by simpa using (neg_ne_zero.mpr hc1'))
  have w21 := z 2 1 (by simpa using (neg_ne_zero.mpr hs1'))
  have w30 := z 3 0 (by simpa using (neg_ne_zero.mpr hc1'))
  have w31 := z 3 1 (by simpa using (neg_ne_zero.mpr hs1'))
  refine ⟨w01, w10, w02, w03, w12, w13, w20, w21, w30, w31, ?_⟩
  have hab' : unitaryInvolution K p f 0 * 0 + unitaryInvolution K p f 1 * 1 = 1 := by
    simp
  have hWm : suMat (aSU K p f hab' hσσ) =
      !![0, 1; -unitaryInvolution K p f 1, unitaryInvolution K p f 0] := suMat_aSU hab' hσσ
  have h' := congrArg suMat (hc (aSU K p f hab' hσσ))
  rw [suMat_mul, suMat_mul, suMat_blockEmb_zero, hWm] at h'
  have e := congrFun (congrFun h' 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, w01, w02, w03, w21, w31] at e
  linear_combination -e


theorem su4_centralizer_shape3 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 3 ≤ p ^ f)
    (w : Su K p f 4) (hw2 : suMat w * suMat w = -1) (htr : (suMat w).trace = 0)
    (hc : ∀ B : Su K p f 2, blockEmb K p f 4 2 0 (by norm_num) B * w =
      w * blockEmb K p f 4 2 0 (by norm_num) B) :
    ∃ l : K, l * l = -1 ∧
      suMat w = !![l, 0, 0, 0; 0, l, 0, 0; 0, 0, -l, 0; 0, 0, 0, -l] := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_prime_ne_two' hp
  obtain ⟨w01, w10, w02, w03, w12, w13, w20, w21, w30, w31, w11⟩ := su4_block0_shape3 hK hq w hc
  set a := suMat w 0 0 with ha
  have e00 := congrFun (congrFun hw2 0) 0
  have e23 := congrFun (congrFun hw2 2) 3
  have e32 := congrFun (congrFun hw2 3) 2
  have e22 := congrFun (congrFun hw2 2) 2
  have e33 := congrFun (congrFun hw2 3) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, w01, w10, w02, w03, w12, w13, w20, w21, w30,
    w31] at e00 e23 e32 e22 e33
  have htr' : a + suMat w 1 1 + suMat w 2 2 + suMat w 3 3 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_four, Matrix.diag] using htr
  rw [← w11] at htr'
  have ha2 : a * a = -1 := e00
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at ha2
    simp at ha2
  have hs : suMat w 2 2 + suMat w 3 3 = -(2 * a) := by linear_combination htr'
  have hs0 : suMat w 2 2 + suMat w 3 3 ≠ 0 := by
    rw [hs]
    exact neg_ne_zero.mpr (mul_ne_zero h2 ha0)
  have c23 : suMat w 2 3 = 0 := by
    have : suMat w 2 3 * (suMat w 2 2 + suMat w 3 3) = 0 := by linear_combination e23
    exact (mul_eq_zero.mp this).resolve_right hs0
  have c32 : suMat w 3 2 = 0 := by
    have : suMat w 3 2 * (suMat w 2 2 + suMat w 3 3) = 0 := by linear_combination e32
    exact (mul_eq_zero.mp this).resolve_right hs0
  have hsq : (suMat w 2 2 - suMat w 3 3) * (suMat w 2 2 + suMat w 3 3) = 0 := by
    rw [c23, c32] at e22 e33
    linear_combination e22 - e33
  have c22c33 : suMat w 2 2 = suMat w 3 3 := by
    have := (mul_eq_zero.mp hsq).resolve_right hs0
    linear_combination this
  have c22 : suMat w 2 2 = -a := by
    have h0 : 2 * (suMat w 2 2 + a) = 0 := by linear_combination hs + c22c33
    have := (mul_eq_zero.mp h0).resolve_left h2
    linear_combination this
  have c33 : suMat w 3 3 = -a := by rw [← c22c33, c22]
  refine ⟨a, ha2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ha, w01, w10, w02, w03, w12, w13, w20, w21, w30, w31, c23, c32, c22, c33, ← w11]


theorem eq_longRootGroupSU_jEl3 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 3 ≤ p ^ f)
    {u : Su K p f 4} (hu2 : suMat u * suMat u = -1) (htr : (suMat u).trace = 0)
    {ι : K} (hι2 : ι * ι = -1) (hσι : unitaryInvolution K p f ι = -ι)
    {L : Subgroup (Su K p f 4)}
    (hL : L ∈ longRootSetU (K := K) (p := p) (f := f) (by norm_num : 2 ≤ 4))
    (hLc : ∀ x ∈ L, x * u = u * x) :
    L = longRootGroupSU K p f (suMat (jEl u ι hι2 hσι)) ∨
      L = longRootGroupSU K p f (suMat (jEl u (-ι) (neg_iota_props _ hι2 hσι).1
        (neg_iota_props _ hι2 hσι).2)) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_prime_ne_two' hp
  obtain ⟨i, g, hLeq, hi⟩ := hL
  set w : Su K p f 4 := g⁻¹ * u * g with hw
  have hwc : ∀ B : Su K p f 2, blockEmb K p f 4 2 0 (by norm_num) B * w =
      w * blockEmb K p f 4 2 0 (by norm_num) B := by
    intro B
    have hmem : g * blockEmb K p f 4 2 0 (by norm_num) B * g⁻¹ ∈ L := by
      rw [hLeq]
      exact ⟨blockEmb K p f 4 2 0 (by norm_num) B, ⟨B, rfl⟩, by simp [MulAut.conj_apply]⟩
    have := hLc _ hmem
    calc blockEmb K p f 4 2 0 (by norm_num) B * w
        = g⁻¹ * ((g * blockEmb K p f 4 2 0 (by norm_num) B * g⁻¹) * u) * g := by
          rw [hw]; group
      _ = g⁻¹ * (u * (g * blockEmb K p f 4 2 0 (by norm_num) B * g⁻¹)) * g := by rw [this]
      _ = w * blockEmb K p f 4 2 0 (by norm_num) B := by rw [hw]; group
  have hw2 : suMat w * suMat w = -1 := by
    have e : w * w = g⁻¹ * (u * u) * g := by rw [hw]; group
    rw [← suMat_mul, e]
    simp only [suMat_mul, hu2, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
      suMat_inv_mul_suMat]
  have hwtr : (suMat w).trace = 0 := by
    have e : suMat w = suMat g⁻¹ * (suMat u * suMat g) := by
      simp only [hw, suMat_mul, Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, suMat_mul_suMat_inv, Matrix.mul_one, htr]
  obtain ⟨l, hl2, hwl⟩ := su4_centralizer_shape3 hK hp hq w hw2 hwtr hwc
  have hdiag : suMat w = (-l) • suMat (rootInvSU K p f (by norm_num : 2 ≤ 4)) := by
    rw [hwl, suMat_rootInvSU_four]
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  have hui : suMat u = (-l) • suMat i := by
    have e1 : u = g * w * g⁻¹ := by rw [hw]; group
    have e2 : i = g * rootInvSU K p f (by norm_num : 2 ≤ 4) * g⁻¹ := hi
    have e3 : suMat u = suMat g * suMat w * suMat g⁻¹ := by
      conv_lhs => rw [e1]
      simp only [suMat_mul]
    rw [e3, hdiag, e2]
    simp only [suMat_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hil : suMat i = l • suMat u := by
    rw [hui, smul_smul]
    have : l * -l = 1 := by linear_combination -hl2
    rw [this, one_smul]
  have hlι : l = ι ∨ l = -ι := by
    have : (l - ι) * (l + ι) = 0 := by linear_combination hl2 - hι2
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hLi : IsLongRootSU2 K p f (by norm_num : 2 ≤ 4) L i := ⟨g, hLeq, hi⟩
  have hLeq' := hLi.eq_longRootGroupSU h2
  rcases hlι with rfl | rfl
  · left
    rw [hLeq']
    congr 1
  · right
    rw [hLeq']
    congr 1


theorem fund_centralizing_su4_three (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 3 ≤ p ^ f)
    {u : Su K p f 4} (hu2 : suMat u * suMat u = -1) (htr : (suMat u).trace = 0)
    {ι : K} (hι2 : ι * ι = -1) (hσι : unitaryInvolution K p f ι = -ι) :
    ∃ L₁ L₂ : Subgroup (Su K p f 4),
      L₁ ∈ longRootSetU (K := K) (p := p) (f := f) (by norm_num : 2 ≤ 4) ∧
      L₂ ∈ longRootSetU (K := K) (p := p) (f := f) (by norm_num : 2 ≤ 4) ∧ L₁ ≠ L₂ ∧
      (∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) ∧ (∀ x ∈ L₁, x * u = u * x) ∧
      (∀ x ∈ L₂, x * u = u * x) ∧
      ∀ L ∈ longRootSetU (K := K) (p := p) (f := f) (by norm_num : 2 ≤ 4),
        (∀ x ∈ L, x * u = u * x) → L = L₁ ∨ L = L₂ := by
  have hn : (2 : ℕ) ≤ 4 := by norm_num
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_prime_ne_two' hp
  obtain ⟨hι2', hσι'⟩ := neg_iota_props _ hι2 hσι
  have hr₁ := exists_isLongRootSU2_jEl hK hp hu2 htr ι hι2 hσι
  have hr₂ := exists_isLongRootSU2_jEl hK hp hu2 htr (-ι) hι2' hσι'
  have hne := jEl_neg_ne hp hu2 ι hι2 hσι
  refine ⟨longRootGroupSU K p f (suMat (jEl u ι hι2 hσι)),
    longRootGroupSU K p f (suMat (jEl u (-ι) hι2' hσι')), ⟨_, hr₁⟩, ⟨_, hr₂⟩, ?_, ?_,
    fun x hx => longRootGroup_jEl_centralizes ι hι2 hσι hx,
    fun x hx => longRootGroup_jEl_centralizes (-ι) hι2' hσι' hx, ?_⟩
  · intro h
    rw [h] at hr₁
    exact hne (hr₁.involution_unique hK hp hr₂)
  · have hc : Commute (jEl u ι hι2 hσι) (jEl u (-ι) hι2' hσι') := by
      apply suMat_injective
      show suMat (jEl u ι hι2 hσι * jEl u (-ι) hι2' hσι') =
        suMat (jEl u (-ι) hι2' hσι' * jEl u ι hι2 hσι)
      rw [suMat_mul, suMat_mul, suMat_jEl, suMat_jEl, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul, mul_comm]
    have hmem : jEl u (-ι) hι2' hσι' ∈ Subgroup.centralizer
        ((longRootGroupSU K p f (suMat (jEl u ι hι2 hσι)) : Subgroup (Su K p f 4)) :
          Set (Su K p f 4)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxu := longRootGroup_jEl_centralizes ι hι2 hσι hx
      apply suMat_injective
      have hxu' : suMat x * suMat u = suMat u * suMat x := by
        rw [← suMat_mul, ← suMat_mul, hxu]
      rw [suMat_mul, suMat_mul, suMat_jEl, Matrix.mul_smul, Matrix.smul_mul, hxu']
    exact forall_comm_of_mem_centralizer_su hK hp (by norm_num : 3 ≤ 4) hr₁ hr₂ hc hne hmem
  · intro L hL hLc
    exact eq_longRootGroupSU_jEl3 hK hp hq hu2 htr hι2 hσι hL hLc

end CFSG.ClassicalInvolution.Q3.Q3TIY
