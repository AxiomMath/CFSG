module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.KleinBound
public import CFSG.LargeExtraspecial.S5Gen
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.InvolutionPair

public section

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup CFSG.GroupTheory

variable {X : Type*} [Group X] [Finite X]

theorem card_eq_three_pow_of_four {F : Subgroup X} (hodd : Odd (Nat.card F)) {a b : X}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (hFa : ∀ x ∈ F, a * x * a⁻¹ ∈ F) (hFb : ∀ x ∈ F, b * x * b⁻¹ ∈ F)
    (h9a : Nat.card (F ⊓ centralizer ({a} : Set X) : Subgroup X) ∣ 9)
    (h9b : Nat.card (F ⊓ centralizer ({b} : Set X) : Subgroup X) ∣ 9)
    (h9ab : Nat.card (F ⊓ centralizer ({a * b} : Set X) : Subgroup X) ∣ 9) :
    ∃ n, Nat.card F = 3 ^ n := by
  have h2 : ¬ 2 ∣ Nat.card F := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hodd
  have hbw := CFSG.EvenSporadicStandard.HNRecog.Section3.card_mul_sq_eq_prod_of_klein
    (N := F) h2 ha hb hab hFa hFb
  have hdvd : Nat.card F ∣ 3 ^ 6 := by
    refine (show Nat.card F ∣ Nat.card (F ⊓ centralizer ({a} : Set X) : Subgroup X) *
        Nat.card (F ⊓ centralizer ({b} : Set X) : Subgroup X) *
        Nat.card (F ⊓ centralizer ({a * b} : Set X) : Subgroup X) from
      ⟨Nat.card (F ⊓ centralizer ({a, b} : Set X) : Subgroup X) ^ 2, hbw.symm⟩).trans ?_
    refine (Nat.mul_dvd_mul (Nat.mul_dvd_mul h9a h9b) h9ab).trans ?_
    norm_num
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  exact ⟨n, hn⟩

private lemma inf_centralizer_eq_bot_of_complement {L F : Subgroup X}
    (hL8 : Nat.card L = 8)
    (hL2 : ∀ s ∈ L, s * s = 1) (hLc : ∀ s ∈ L, ∀ t ∈ L, s * t = t * s)
    (hCF : ∀ x ∈ F, (∀ s ∈ L, s * x = x * s) → x = 1)
    {p u v : X} (hp : p ∈ L) (hu : u ∈ L) (hv : v ∈ L)
    (hp1 : p ≠ 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u ≠ v)
    (hpW : p ∉ Subgroup.closure ({u, v} : Set X)) :
    F ⊓ centralizer ({p} : Set X) ⊓ centralizer ({u, v} : Set X) = ⊥ := by
  let W : Subgroup X := Subgroup.closure ({u, v} : Set X)
  let P : Subgroup X := Subgroup.zpowers p
  have hWcard : Nat.card W = 4 :=
    card_closure_pair_eq_four (hL2 u hu) (hL2 v hv) (hLc u hu v hv) hu1 hv1 huv
  have hPcard : Nat.card P = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hL2 p hp) hp1]
  have hWle : W ≤ L := by
    rw [show W = Subgroup.closure ({u, v} : Set X) from rfl, Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact hu
    · rw [hx]; exact hv
  have hPle : P ≤ L := Subgroup.zpowers_le.mpr hp
  have hpC : p ∈ Subgroup.centralizer (W : Set X) := by
    rw [show W = Subgroup.closure ({u, v} : Set X) from rfl, Subgroup.centralizer_closure]
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases hz with hz | hz
    · rw [hz]; exact (hLc p hp u hu).symm
    · rw [hz]; exact (hLc p hp v hv).symm
  have hnormal : P ≤ Subgroup.normalizer (W : Set X) :=
    (Subgroup.zpowers_le.mpr hpC).trans (Subgroup.centralizer_le_normalizer _)
  have hdisj : Disjoint W P := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxW : x ∈ W := (Subgroup.mem_inf.mp hx).1
    have hxP : x ∈ P := (Subgroup.mem_inf.mp hx).2
    have hxP' : x ∈ ({1, p} : Set X) := by
      change x ∈ (Subgroup.zpowers p : Set X) at hxP
      rwa [coe_zpowers_eq_pair (hL2 p hp) hp1] at hxP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxP'
    rcases hxP' with hx1 | hxp
    · exact hx1
    · exact absurd (by rw [← hxp]; exact hxW) hpW
  have hcard : Nat.card (W ⊔ P : Subgroup X) = 8 := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      W P hnormal hdisj
    rw [h, hWcard, hPcard]
  have hEqL : (W ⊔ P : Subgroup X) = L := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hWle hPle)
    rw [hcard, hL8]
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx' : x ∈ F ⊓ centralizer ({p} : Set X) := (Subgroup.mem_inf.mp hx).1
  have hxF : x ∈ F := (Subgroup.mem_inf.mp hx').1
  have hxCp : x ∈ centralizer ({p} : Set X) := (Subgroup.mem_inf.mp hx').2
  have hxCuv : x ∈ centralizer ({u, v} : Set X) := (Subgroup.mem_inf.mp hx).2
  have hxUnion : x ∈ centralizer (({u, v} : Set X) ∪ {p}) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_union] at hz
    rcases hz with hz | hz
    · exact (Subgroup.mem_centralizer_iff.mp hxCuv) z hz
    · exact (Subgroup.mem_centralizer_iff.mp hxCp) z hz
  have hxL : x ∈ centralizer (L : Set X) := by
    rw [← hEqL]
    have hP : P = Subgroup.closure ({p} : Set X) := Subgroup.zpowers_eq_closure p
    rw [hP]
    rw [show W = Subgroup.closure ({u, v} : Set X) from rfl]
    rw [← Subgroup.closure_union, Subgroup.centralizer_closure]
    exact hxUnion
  exact hCF x hxF (fun s hs => Subgroup.mem_centralizer_iff.mp hxL s hs)

theorem fano_count : ∀ d0 d1 d2 d3 d4 d5 d6 : Fin 3,
    let c1 := d0.val + d1.val + d2.val; let c2 := d0.val + d3.val + d4.val
    let c3 := d0.val + d5.val + d6.val; let c4 := d1.val + d3.val + d5.val
    let c5 := d1.val + d4.val + d6.val; let c6 := d2.val + d3.val + d6.val
    let c7 := d2.val + d4.val + d5.val
    let n := d0.val + d1.val + d2.val + d3.val + d4.val + d5.val + d6.val
    c1 ≤ 2 → c2 ≤ 2 → c3 ≤ 2 → c4 ≤ 2 → c5 ≤ 2 → c6 ≤ 2 → c7 ≤ 2 →
    c1 < n → c2 < n → c3 < n → c4 < n → c5 < n → c6 < n → c7 < n →
    n = 3 ∨ (n = 4 ∧ (c1 = 0 ∨ c2 = 0 ∨ c3 = 0 ∨ c4 = 0 ∨ c5 = 0 ∨ c6 = 0 ∨ c7 = 0)) := by
  decide

private def fano : Fin 7 → (Fin 3 → ZMod 2)
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![1, 1, 0]
  | 3 => ![0, 0, 1]
  | 4 => ![1, 0, 1]
  | 5 => ![0, 1, 1]
  | 6 => ![1, 1, 1]

theorem card_eq_of_elemTwo {L F : Subgroup X} (hL8 : Nat.card L = 8)
    (hL2 : ∀ s ∈ L, s * s = 1) (hLc : ∀ s ∈ L, ∀ s' ∈ L, s * s' = s' * s)
    (hodd : Odd (Nat.card F)) (hnorm : ∀ s ∈ L, ∀ x ∈ F, s * x * s⁻¹ ∈ F)
    (hCF : ∀ x ∈ F, (∀ s ∈ L, s * x = x * s) → x = 1)
    (hfaith : ∀ s ∈ L, (∀ x ∈ F, s * x = x * s) → s = 1)
    (h9 : ∀ s ∈ L, s ≠ 1 → Nat.card (F ⊓ centralizer ({s} : Set X) : Subgroup X) ∣ 9) :
    Nat.card F = 3 ^ 3 ∨
      (Nat.card F = 3 ^ 4 ∧ ∃ p ∈ L, p ≠ 1 ∧ ∀ x ∈ F, p * x = x * p → x = 1) := by
  classical
  have hL3 : 3 ≤ Nat.card L := by omega
  obtain ⟨a0, ha0L, b0, hb0L, ha01, hb01, hab0⟩ :=
    CFSG.LargeExtraspecial.S5.exists_ne_one_ne_one_ne hL3
  have hab0_comm : a0 * b0 = b0 * a0 := hLc a0 ha0L b0 hb0L
  have hab0_mem : a0 * b0 ∈ L := L.mul_mem ha0L hb0L
  have hab0_ne_one : a0 * b0 ≠ 1 := by
    intro h
    apply hab0
    calc a0 = a0 * 1 := (mul_one a0).symm
      _ = a0 * (a0 * b0) := by rw [h]
      _ = (a0 * a0) * b0 := by rw [mul_assoc]
      _ = b0 := by rw [hL2 a0 ha0L, one_mul]
  obtain ⟨nF, hnF⟩ := card_eq_three_pow_of_four hodd (hL2 a0 ha0L) (hL2 b0 hb0L)
    hab0_comm (hnorm a0 ha0L) (hnorm b0 hb0L) (h9 a0 ha0L ha01) (h9 b0 hb0L hb01)
    (h9 (a0 * b0) hab0_mem hab0_ne_one)
  haveI hLel : CFSG.IsElementaryAbelian 2 L :=
    CFSG.IsElementaryAbelian.two_of_forall_mul_self hLc hL2
  letI : CommGroup L := IsMulCommutative.instCommGroup
  letI : Module (ZMod 2) (Additive L) := CFSG.IsElementaryAbelian.isVectorSpace 2
  have hcardL : Nat.card (Additive L) = 8 :=
    (Nat.card_congr Additive.ofMul).symm.trans hL8
  have hfindim : Module.finrank (ZMod 2) (Additive L) = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive L)
    rw [Nat.card_zmod, hcardL] at h
    have h' : 2 ^ 3 = 2 ^ Module.finrank (ZMod 2) (Additive L) := by
      rw [← h]; norm_num
    exact (Nat.pow_right_injective (le_refl 2)) h'.symm
  let B := Module.finBasisOfFinrankEq (ZMod 2) (Additive L) hfindim
  let g : (Fin 3 → ZMod 2) → L := fun v => Additive.toMul (B.equivFun.symm v)
  have hg_inj : Function.Injective g := by
    intro v w h
    have h1 : B.equivFun.symm v = B.equivFun.symm w := Additive.toMul.injective h
    exact B.equivFun.symm.injective h1
  have hg_mul : ∀ v w : Fin 3 → ZMod 2, g (v + w) = g v * g w := by
    intro v w
    simp only [g, map_add]
    rfl
  have hg_one : g 0 = 1 := by simp [g]
  let p : Fin 7 → X := fun i => ((g (fano i) : L) : X)
  have hp_mem : ∀ i, p i ∈ L := fun i => (g (fano i)).2
  have hp_sq : ∀ i, p i * p i = 1 := fun i => hL2 (p i) (hp_mem i)
  have hp_one : ∀ i, p i ≠ 1 := by
    intro i hi
    have hLi : g (fano i) = 1 := by
      apply Subtype.ext
      simpa [p] using hi
    have h0 : fano i = 0 := hg_inj (by rw [hLi, hg_one])
    have hne : fano i ≠ 0 := by
      fin_cases i <;> decide
    exact hne h0
  have hp_mul : ∀ {i j k : Fin 7}, fano i + fano j = fano k → p i * p j = p k := by
    intro i j k h
    change ((g (fano i) : L) : X) * ((g (fano j) : L) : X) = ((g (fano k) : L) : X)
    rw [← Subgroup.coe_mul, ← hg_mul, h]
  have hp_ne_fano : ∀ {i j : Fin 7}, fano i ≠ fano j → p i ≠ p j := by
    intro i j h hpij
    exact h (hg_inj (Subtype.ext hpij))
  have hfano_inj : Function.Injective fano := by decide
  have hp_ne_of_ne : ∀ {i j : Fin 7}, i ≠ j → p i ≠ p j := by
    intro i j hij hpij
    exact hij (hfano_inj (hg_inj (Subtype.ext hpij)))
  have hfano_sq : ∀ j : Fin 7, fano j + fano j = 0 := by
    intro j
    rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (R := ZMod 2) (n := 2)]
    show ((2 : ZMod 2) • fano j) = 0
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
  have notMem_closure : ∀ {i j k l : Fin 7}, fano j + fano k = fano l →
      fano i ≠ fano j → fano i ≠ fano k → fano i ≠ fano l →
      p i ∉ Subgroup.closure ({p j, p k} : Set X) := by
    intro i j k l hjk hij hik hil hmem
    have hjk_ne : fano j ≠ fano k := by
      intro h
      have hfl : fano l ≠ 0 := by fin_cases l <;> decide
      apply hfl
      calc fano l = fano j + fano k := hjk.symm
        _ = fano j + fano j := by rw [h]
        _ = 0 := hfano_sq j
    have hset := coe_closure_pair_eq (hp_sq j) (hp_sq k)
      (hLc (p j) (hp_mem j) (p k) (hp_mem k)) (hp_one j) (hp_one k)
      (hp_ne_fano hjk_ne)
    change p i ∈ (Subgroup.closure ({p j, p k} : Set X) : Set X) at hmem
    rw [hset] at hmem
    have hpjk : p j * p k = p l := hp_mul hjk
    rw [hpjk] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h
    · exact hp_one i h
    · exact hp_ne_fano hij h
    · exact hp_ne_fano hik h
    · exact hp_ne_fano hil h
  let C : Fin 7 → Subgroup X := fun i => F ⊓ centralizer ({p i} : Set X)
  let D0 : Subgroup X := F ⊓ centralizer ({p 0, p 1} : Set X)
  let D1 : Subgroup X := F ⊓ centralizer ({p 0, p 3} : Set X)
  let D2 : Subgroup X := F ⊓ centralizer ({p 0, p 5} : Set X)
  let D3 : Subgroup X := F ⊓ centralizer ({p 1, p 3} : Set X)
  let D4 : Subgroup X := F ⊓ centralizer ({p 1, p 4} : Set X)
  let D5 : Subgroup X := F ⊓ centralizer ({p 2, p 3} : Set X)
  let D6 : Subgroup X := F ⊓ centralizer ({p 2, p 4} : Set X)
  have hC9 : ∀ i, Nat.card (C i) ∣ 9 := fun i => h9 (p i) (hp_mem i) (hp_one i)
  have hC9' : ∀ i, Nat.card (C i) ∣ 3 ^ 2 := by
    intro i
    simpa using hC9 i
  have hD9_of_pair {G : Subgroup X} {i j : Fin 7}
      (h : G = F ⊓ centralizer ({p i, p j} : Set X)) :
      Nat.card G ∣ 9 := by
    rw [h]
    refine (Subgroup.card_dvd_of_le (inf_le_inf_left F
      (Subgroup.centralizer_le ?_))).trans (hC9 i)
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Set.mem_insert _ _
  have hD90 : Nat.card D0 ∣ 9 := hD9_of_pair rfl
  have hD91 : Nat.card D1 ∣ 9 := hD9_of_pair rfl
  have hD92 : Nat.card D2 ∣ 9 := hD9_of_pair rfl
  have hD93 : Nat.card D3 ∣ 9 := hD9_of_pair rfl
  have hD94 : Nat.card D4 ∣ 9 := hD9_of_pair rfl
  have hD95 : Nat.card D5 ∣ 9 := hD9_of_pair rfl
  have hD96 : Nat.card D6 ∣ 9 := hD9_of_pair rfl
  have hD90' : Nat.card D0 ∣ 3 ^ 2 := by simpa using hD90
  have hD91' : Nat.card D1 ∣ 3 ^ 2 := by simpa using hD91
  have hD92' : Nat.card D2 ∣ 3 ^ 2 := by simpa using hD92
  have hD93' : Nat.card D3 ∣ 3 ^ 2 := by simpa using hD93
  have hD94' : Nat.card D4 ∣ 3 ^ 2 := by simpa using hD94
  have hD95' : Nat.card D5 ∣ 3 ^ 2 := by simpa using hD95
  have hD96' : Nat.card D6 ∣ 3 ^ 2 := by simpa using hD96
  obtain ⟨c0, hc0le, hc0⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp (hC9' 0)
  obtain ⟨c1, hc1le, hc1⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp (hC9' 1)
  obtain ⟨c2, hc2le, hc2⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp (hC9' 2)
  obtain ⟨c3, hc3le, hc3⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp (hC9' 3)
  obtain ⟨c4, hc4le, hc4⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp (hC9' 4)
  obtain ⟨c5, hc5le, hc5⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp (hC9' 5)
  obtain ⟨c6, hc6le, hc6⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp (hC9' 6)
  obtain ⟨d0, hd0le, hd0⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp hD90'
  obtain ⟨d1, hd1le, hd1⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp hD91'
  obtain ⟨d2, hd2le, hd2⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp hD92'
  obtain ⟨d3, hd3le, hd3⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp hD93'
  obtain ⟨d4, hd4le, hd4⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp hD94'
  obtain ⟨d5, hd5le, hd5⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp hD95'
  obtain ⟨d6, hd6le, hd6⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp hD96'
  let c : Fin 7 → ℕ := ![c0, c1, c2, c3, c4, c5, c6]
  let d : Fin 7 → ℕ := ![d0, d1, d2, d3, d4, d5, d6]
  have hc : ∀ i, Nat.card (C i) = 3 ^ c i := by
    intro i
    fin_cases i <;> simp [c, hc0, hc1, hc2, hc3, hc4, hc5, hc6]
  have hd0' : Nat.card D0 = 3 ^ d 0 := by simp [d, hd0]
  have hd1' : Nat.card D1 = 3 ^ d 1 := by simp [d, hd1]
  have hd2' : Nat.card D2 = 3 ^ d 2 := by simp [d, hd2]
  have hd3' : Nat.card D3 = 3 ^ d 3 := by simp [d, hd3]
  have hd4' : Nat.card D4 = 3 ^ d 4 := by simp [d, hd4]
  have hd5' : Nat.card D5 = 3 ^ d 5 := by simp [d, hd5]
  have hd6' : Nat.card D6 = 3 ^ d 6 := by simp [d, hd6]
  have hcle : ∀ i, c i ≤ 2 := by
    intro i
    fin_cases i <;> simp [c, hc0le, hc1le, hc2le, hc3le, hc4le, hc5le, hc6le]
  have hdle0 : d 0 ≤ 2 := by simp [d, hd0le]
  have hdle1 : d 1 ≤ 2 := by simp [d, hd1le]
  have hdle2 : d 2 ≤ 2 := by simp [d, hd2le]
  have hdle3 : d 3 ≤ 2 := by simp [d, hd3le]
  have hdle4 : d 4 ≤ 2 := by simp [d, hd4le]
  have hdle5 : d 5 ≤ 2 := by simp [d, hd5le]
  have hdle6 : d 6 ≤ 2 := by simp [d, hd6le]
  have hbot_of_notMem : ∀ {i j k l : Fin 7}, fano j + fano k = fano l →
      fano i ≠ fano j → fano i ≠ fano k → fano i ≠ fano l →
      C i ⊓ centralizer ({p j, p k} : Set X) = ⊥ := by
    intro i j k l hjk hij hik hil
    have hjk_ne : fano j ≠ fano k := by
      intro h
      have hfl : fano l ≠ 0 := by fin_cases l <;> decide
      apply hfl
      calc fano l = fano j + fano k := hjk.symm
        _ = fano j + fano j := by rw [h]
        _ = 0 := hfano_sq j
    exact inf_centralizer_eq_bot_of_complement hL8 hL2 hLc hCF
      (hp_mem i) (hp_mem j) (hp_mem k) (hp_one i) (hp_one j) (hp_one k)
      (hp_ne_fano hjk_ne) (notMem_closure hjk hij hik hil)
  have hconjC : ∀ (i : Fin 7) (s : X), s ∈ L →
      ∀ x ∈ C i, s * x * s⁻¹ ∈ C i := by
    intro i s hs x hx
    have hxF : x ∈ F := (Subgroup.mem_inf.mp hx).1
    have hxC : x ∈ centralizer ({p i} : Set X) := (Subgroup.mem_inf.mp hx).2
    refine Subgroup.mem_inf.mpr ⟨hnorm s hs x hxF, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hps : Commute (p i) s := (hLc s hs (p i) (hp_mem i)).symm
    have hpx : Commute (p i) x := hxC (p i) (Set.mem_singleton _)
    exact (hps.mul_right hpx).mul_right hps.inv_right
  have bw_C : ∀ (i : Fin 7) {u v : X},
      (∀ x ∈ C i, u * x * u⁻¹ ∈ C i) →
      (∀ x ∈ C i, v * x * v⁻¹ ∈ C i) →
      u * u = 1 → v * v = 1 → u * v = v * u →
      C i ⊓ centralizer ({u, v} : Set X) = ⊥ →
      Nat.card (C i) =
        Nat.card (C i ⊓ centralizer ({u} : Set X) : Subgroup X) *
        Nat.card (C i ⊓ centralizer ({v} : Set X) : Subgroup X) *
        Nat.card (C i ⊓ centralizer ({u * v} : Set X) : Subgroup X) := by
    intro i u v hNu hNv hu2 hv2 huv hbot
    have hoddC : ¬ 2 ∣ Nat.card (C i) := by
      have ho : Odd (Nat.card (C i)) :=
        hodd.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left : C i ≤ F))
      rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]
    have hbw := CFSG.EvenSporadicStandard.HNRecog.Section3.card_mul_sq_eq_prod_of_klein
      (N := C i) hoddC hu2 hv2 huv hNu hNv
    rw [hbot, Subgroup.card_bot, one_pow, mul_one] at hbw
    exact hbw
  have hp01 : p 0 * p 1 = p 2 := hp_mul (by decide)
  have hp03 : p 0 * p 3 = p 4 := hp_mul (by decide)
  have hp05 : p 0 * p 5 = p 6 := hp_mul (by decide)
  have hp13 : p 1 * p 3 = p 5 := hp_mul (by decide)
  have hp14 : p 1 * p 4 = p 6 := hp_mul (by decide)
  have hp23 : p 2 * p 3 = p 6 := hp_mul (by decide)
  have hp24 : p 2 * p 4 = p 5 := hp_mul (by decide)
  have hD0_01 : C 0 ⊓ centralizer ({p 1} : Set X) = D0 := by
    change (F ⊓ centralizer ({p 0} : Set X)) ⊓ centralizer ({p 1} : Set X) = D0
    rw [inf_centralizer_inf_centralizer_eq_pair]
  have hD1_03 : C 0 ⊓ centralizer ({p 3} : Set X) = D1 := by
    change (F ⊓ centralizer ({p 0} : Set X)) ⊓ centralizer ({p 3} : Set X) = D1
    rw [inf_centralizer_inf_centralizer_eq_pair]
  have hD2_013 : C 0 ⊓ centralizer ({p 1 * p 3} : Set X) = D2 := by
    rw [hp13]
    change (F ⊓ centralizer ({p 0} : Set X)) ⊓ centralizer ({p 5} : Set X) = D2
    rw [inf_centralizer_inf_centralizer_eq_pair]
  have hbot0 : C 0 ⊓ centralizer ({p 1, p 3} : Set X) = ⊥ :=
    hbot_of_notMem (i := 0) (j := 1) (k := 3) (l := 5)
      (by decide) (by decide) (by decide) (by decide)
  have hpoint0 : c 0 = d 0 + d 1 + d 2 := by
    have hbw0 := bw_C 0 (u := p 1) (v := p 3)
      (hconjC 0 (p 1) (hp_mem 1)) (hconjC 0 (p 3) (hp_mem 3))
      (hp_sq 1) (hp_sq 3) (hLc (p 1) (hp_mem 1) (p 3) (hp_mem 3)) hbot0
    rw [hD0_01, hD1_03, hD2_013] at hbw0
    apply Nat.pow_right_injective (show 2 ≤ 3 by norm_num)
    calc 3 ^ c 0 = Nat.card (C 0) := (hc 0).symm
      _ = Nat.card D0 * Nat.card D1 * Nat.card D2 := hbw0
      _ = 3 ^ d 0 * 3 ^ d 1 * 3 ^ d 2 := by rw [hd0', hd1', hd2']
      _ = 3 ^ (d 0 + d 1 + d 2) := by rw [← pow_add, ← pow_add]
  have hD0_10 : C 1 ⊓ centralizer ({p 0} : Set X) = D0 := by
    change (F ⊓ centralizer ({p 1} : Set X)) ⊓ centralizer ({p 0} : Set X) = D0
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
  have hD3_13 : C 1 ⊓ centralizer ({p 3} : Set X) = D3 := by
    change (F ⊓ centralizer ({p 1} : Set X)) ⊓ centralizer ({p 3} : Set X) = D3
    rw [inf_centralizer_inf_centralizer_eq_pair]
  have hD4_103 : C 1 ⊓ centralizer ({p 0 * p 3} : Set X) = D4 := by
    rw [hp03]
    change (F ⊓ centralizer ({p 1} : Set X)) ⊓ centralizer ({p 4} : Set X) = D4
    rw [inf_centralizer_inf_centralizer_eq_pair]
  have hbot1 : C 1 ⊓ centralizer ({p 0, p 3} : Set X) = ⊥ :=
    hbot_of_notMem (i := 1) (j := 0) (k := 3) (l := 4)
      (by decide) (by decide) (by decide) (by decide)
  have hpoint1 : c 1 = d 0 + d 3 + d 4 := by
    have hbw := bw_C 1 (u := p 0) (v := p 3)
      (hconjC 1 (p 0) (hp_mem 0)) (hconjC 1 (p 3) (hp_mem 3))
      (hp_sq 0) (hp_sq 3) (hLc (p 0) (hp_mem 0) (p 3) (hp_mem 3)) hbot1
    rw [hD0_10, hD3_13, hD4_103] at hbw
    apply Nat.pow_right_injective (show 2 ≤ 3 by norm_num)
    calc 3 ^ c 1 = Nat.card (C 1) := (hc 1).symm
      _ = Nat.card D0 * Nat.card D3 * Nat.card D4 := hbw
      _ = 3 ^ d 0 * 3 ^ d 3 * 3 ^ d 4 := by rw [hd0', hd3', hd4']
      _ = 3 ^ (d 0 + d 3 + d 4) := by rw [← pow_add, ← pow_add]
  have hD0_20 : C 2 ⊓ centralizer ({p 0} : Set X) = D0 := by
    change (F ⊓ centralizer ({p 2} : Set X)) ⊓ centralizer ({p 0} : Set X) = D0
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
    rw [← centralizer_pair_eq_of_mul (u := p 0) (v := p 1) (w := p 2) (hp_sq 0) hp01]
  have hD5_23 : C 2 ⊓ centralizer ({p 3} : Set X) = D5 := by
    change (F ⊓ centralizer ({p 2} : Set X)) ⊓ centralizer ({p 3} : Set X) = D5
    rw [inf_centralizer_inf_centralizer_eq_pair]
  have hD6_203 : C 2 ⊓ centralizer ({p 0 * p 3} : Set X) = D6 := by
    rw [hp03]
    change (F ⊓ centralizer ({p 2} : Set X)) ⊓ centralizer ({p 4} : Set X) = D6
    rw [inf_centralizer_inf_centralizer_eq_pair]
  have hbot2 : C 2 ⊓ centralizer ({p 0, p 3} : Set X) = ⊥ :=
    hbot_of_notMem (i := 2) (j := 0) (k := 3) (l := 4)
      (by decide) (by decide) (by decide) (by decide)
  have hpoint2 : c 2 = d 0 + d 5 + d 6 := by
    have hbw := bw_C 2 (u := p 0) (v := p 3)
      (hconjC 2 (p 0) (hp_mem 0)) (hconjC 2 (p 3) (hp_mem 3))
      (hp_sq 0) (hp_sq 3) (hLc (p 0) (hp_mem 0) (p 3) (hp_mem 3)) hbot2
    rw [hD0_20, hD5_23, hD6_203] at hbw
    apply Nat.pow_right_injective (show 2 ≤ 3 by norm_num)
    calc 3 ^ c 2 = Nat.card (C 2) := (hc 2).symm
      _ = Nat.card D0 * Nat.card D5 * Nat.card D6 := hbw
      _ = 3 ^ d 0 * 3 ^ d 5 * 3 ^ d 6 := by rw [hd0', hd5', hd6']
      _ = 3 ^ (d 0 + d 5 + d 6) := by rw [← pow_add, ← pow_add]
  have hD1_30 : C 3 ⊓ centralizer ({p 0} : Set X) = D1 := by
    change (F ⊓ centralizer ({p 3} : Set X)) ⊓ centralizer ({p 0} : Set X) = D1
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
  have hD3_31 : C 3 ⊓ centralizer ({p 1} : Set X) = D3 := by
    change (F ⊓ centralizer ({p 3} : Set X)) ⊓ centralizer ({p 1} : Set X) = D3
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
  have hD5_301 : C 3 ⊓ centralizer ({p 0 * p 1} : Set X) = D5 := by
    rw [hp01]
    change (F ⊓ centralizer ({p 3} : Set X)) ⊓ centralizer ({p 2} : Set X) = D5
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
  have hbot3 : C 3 ⊓ centralizer ({p 0, p 1} : Set X) = ⊥ :=
    hbot_of_notMem (i := 3) (j := 0) (k := 1) (l := 2)
      (by decide) (by decide) (by decide) (by decide)
  have hpoint3 : c 3 = d 1 + d 3 + d 5 := by
    have hbw := bw_C 3 (u := p 0) (v := p 1)
      (hconjC 3 (p 0) (hp_mem 0)) (hconjC 3 (p 1) (hp_mem 1))
      (hp_sq 0) (hp_sq 1) (hLc (p 0) (hp_mem 0) (p 1) (hp_mem 1)) hbot3
    rw [hD1_30, hD3_31, hD5_301] at hbw
    apply Nat.pow_right_injective (show 2 ≤ 3 by norm_num)
    calc 3 ^ c 3 = Nat.card (C 3) := (hc 3).symm
      _ = Nat.card D1 * Nat.card D3 * Nat.card D5 := hbw
      _ = 3 ^ d 1 * 3 ^ d 3 * 3 ^ d 5 := by rw [hd1', hd3', hd5']
      _ = 3 ^ (d 1 + d 3 + d 5) := by rw [← pow_add, ← pow_add]
  have hD1_40 : C 4 ⊓ centralizer ({p 0} : Set X) = D1 := by
    change (F ⊓ centralizer ({p 4} : Set X)) ⊓ centralizer ({p 0} : Set X) = D1
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
    rw [← centralizer_pair_eq_of_mul (u := p 0) (v := p 3) (w := p 4) (hp_sq 0) hp03]
  have hD4_41 : C 4 ⊓ centralizer ({p 1} : Set X) = D4 := by
    change (F ⊓ centralizer ({p 4} : Set X)) ⊓ centralizer ({p 1} : Set X) = D4
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
  have hD6_401 : C 4 ⊓ centralizer ({p 0 * p 1} : Set X) = D6 := by
    rw [hp01]
    change (F ⊓ centralizer ({p 4} : Set X)) ⊓ centralizer ({p 2} : Set X) = D6
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
  have hbot4 : C 4 ⊓ centralizer ({p 0, p 1} : Set X) = ⊥ :=
    hbot_of_notMem (i := 4) (j := 0) (k := 1) (l := 2)
      (by decide) (by decide) (by decide) (by decide)
  have hpoint4 : c 4 = d 1 + d 4 + d 6 := by
    have hbw := bw_C 4 (u := p 0) (v := p 1)
      (hconjC 4 (p 0) (hp_mem 0)) (hconjC 4 (p 1) (hp_mem 1))
      (hp_sq 0) (hp_sq 1) (hLc (p 0) (hp_mem 0) (p 1) (hp_mem 1)) hbot4
    rw [hD1_40, hD4_41, hD6_401] at hbw
    apply Nat.pow_right_injective (show 2 ≤ 3 by norm_num)
    calc 3 ^ c 4 = Nat.card (C 4) := (hc 4).symm
      _ = Nat.card D1 * Nat.card D4 * Nat.card D6 := hbw
      _ = 3 ^ d 1 * 3 ^ d 4 * 3 ^ d 6 := by rw [hd1', hd4', hd6']
      _ = 3 ^ (d 1 + d 4 + d 6) := by rw [← pow_add, ← pow_add]
  have hD2_50 : C 5 ⊓ centralizer ({p 0} : Set X) = D2 := by
    change (F ⊓ centralizer ({p 5} : Set X)) ⊓ centralizer ({p 0} : Set X) = D2
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
  have hD3_51 : C 5 ⊓ centralizer ({p 1} : Set X) = D3 := by
    change (F ⊓ centralizer ({p 5} : Set X)) ⊓ centralizer ({p 1} : Set X) = D3
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
    rw [← centralizer_pair_eq_of_mul (u := p 1) (v := p 3) (w := p 5) (hp_sq 1) hp13]
  have hD6_501 : C 5 ⊓ centralizer ({p 0 * p 1} : Set X) = D6 := by
    rw [hp01]
    change (F ⊓ centralizer ({p 5} : Set X)) ⊓ centralizer ({p 2} : Set X) = D6
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
    rw [← centralizer_pair_eq_of_mul (u := p 2) (v := p 4) (w := p 5) (hp_sq 2) hp24]
  have hbot5 : C 5 ⊓ centralizer ({p 0, p 1} : Set X) = ⊥ :=
    hbot_of_notMem (i := 5) (j := 0) (k := 1) (l := 2)
      (by decide) (by decide) (by decide) (by decide)
  have hpoint5 : c 5 = d 2 + d 3 + d 6 := by
    have hbw := bw_C 5 (u := p 0) (v := p 1)
      (hconjC 5 (p 0) (hp_mem 0)) (hconjC 5 (p 1) (hp_mem 1))
      (hp_sq 0) (hp_sq 1) (hLc (p 0) (hp_mem 0) (p 1) (hp_mem 1)) hbot5
    rw [hD2_50, hD3_51, hD6_501] at hbw
    apply Nat.pow_right_injective (show 2 ≤ 3 by norm_num)
    calc 3 ^ c 5 = Nat.card (C 5) := (hc 5).symm
      _ = Nat.card D2 * Nat.card D3 * Nat.card D6 := hbw
      _ = 3 ^ d 2 * 3 ^ d 3 * 3 ^ d 6 := by rw [hd2', hd3', hd6']
      _ = 3 ^ (d 2 + d 3 + d 6) := by rw [← pow_add, ← pow_add]
  have hD2_60 : C 6 ⊓ centralizer ({p 0} : Set X) = D2 := by
    change (F ⊓ centralizer ({p 6} : Set X)) ⊓ centralizer ({p 0} : Set X) = D2
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
    rw [← centralizer_pair_eq_of_mul (u := p 0) (v := p 5) (w := p 6) (hp_sq 0) hp05]
  have hD4_61 : C 6 ⊓ centralizer ({p 1} : Set X) = D4 := by
    change (F ⊓ centralizer ({p 6} : Set X)) ⊓ centralizer ({p 1} : Set X) = D4
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
    rw [← centralizer_pair_eq_of_mul (u := p 1) (v := p 4) (w := p 6) (hp_sq 1) hp14]
  have hD5_601 : C 6 ⊓ centralizer ({p 0 * p 1} : Set X) = D5 := by
    rw [hp01]
    change (F ⊓ centralizer ({p 6} : Set X)) ⊓ centralizer ({p 2} : Set X) = D5
    rw [inf_centralizer_inf_centralizer_eq_pair, centralizer_pair_comm]
    rw [← centralizer_pair_eq_of_mul (u := p 2) (v := p 3) (w := p 6) (hp_sq 2) hp23]
  have hbot6 : C 6 ⊓ centralizer ({p 0, p 1} : Set X) = ⊥ :=
    hbot_of_notMem (i := 6) (j := 0) (k := 1) (l := 2)
      (by decide) (by decide) (by decide) (by decide)
  have hpoint6 : c 6 = d 2 + d 4 + d 5 := by
    have hbw := bw_C 6 (u := p 0) (v := p 1)
      (hconjC 6 (p 0) (hp_mem 0)) (hconjC 6 (p 1) (hp_mem 1))
      (hp_sq 0) (hp_sq 1) (hLc (p 0) (hp_mem 0) (p 1) (hp_mem 1)) hbot6
    rw [hD2_60, hD4_61, hD5_601] at hbw
    apply Nat.pow_right_injective (show 2 ≤ 3 by norm_num)
    calc 3 ^ c 6 = Nat.card (C 6) := (hc 6).symm
      _ = Nat.card D2 * Nat.card D4 * Nat.card D5 := hbw
      _ = 3 ^ d 2 * 3 ^ d 4 * 3 ^ d 5 := by rw [hd2', hd4', hd5']
      _ = 3 ^ (d 2 + d 4 + d 5) := by rw [← pow_add, ← pow_add]
  have hoddF : ¬ 2 ∣ Nat.card F := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hodd
  have hline : nF + 2 * d 0 = c 0 + c 1 + c 2 := by
    have hbwF := CFSG.EvenSporadicStandard.HNRecog.Section3.card_mul_sq_eq_prod_of_klein
      (N := F) hoddF (hp_sq 0) (hp_sq 1) (hLc (p 0) (hp_mem 0) (p 1) (hp_mem 1))
      (hnorm (p 0) (hp_mem 0)) (hnorm (p 1) (hp_mem 1))
    rw [hp01] at hbwF
    change Nat.card F * Nat.card D0 ^ 2 =
      Nat.card (C 0) * Nat.card (C 1) * Nat.card (C 2) at hbwF
    apply Nat.pow_right_injective (show 2 ≤ 3 by norm_num)
    calc 3 ^ (nF + 2 * d 0) = 3 ^ nF * (3 ^ d 0) ^ 2 := by
          rw [pow_add]
          congr 1
          rw [← pow_mul]
          congr 1
          omega
      _ = Nat.card F * Nat.card D0 ^ 2 := by rw [← hnF, ← hd0']
      _ = Nat.card (C 0) * Nat.card (C 1) * Nat.card (C 2) := hbwF
      _ = 3 ^ c 0 * 3 ^ c 1 * 3 ^ c 2 := by rw [hc 0, hc 1, hc 2]
      _ = 3 ^ (c 0 + c 1 + c 2) := by rw [← pow_add, ← pow_add]
  have hnsum : nF = d 0 + d 1 + d 2 + d 3 + d 4 + d 5 + d 6 := by omega
  have hc_lt : ∀ i, c i < nF := by
    intro i
    have hdvd : 3 ^ c i ∣ 3 ^ nF := by
      rw [← hc i, ← hnF]
      exact Subgroup.card_dvd_of_le (inf_le_left : C i ≤ F)
    obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := nF)).mp hdvd
    have hck : c i = k := Nat.pow_right_injective (show 2 ≤ 3 by norm_num) hk_eq
    have hci_le : c i ≤ nF := by omega
    have hne : c i ≠ nF := by
      intro heq
      have hcard : Nat.card (C i) = Nat.card F := by rw [hc i, hnF, heq]
      have hCeq : C i = F := by
        apply Subgroup.eq_of_le_of_card_ge (inf_le_left : C i ≤ F)
        rw [hcard]
      have hcent : ∀ x ∈ F, p i * x = x * p i := by
        intro x hx
        have hxCi : x ∈ C i := by rw [hCeq]; exact hx
        exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxCi).2) (p i)
          (Set.mem_singleton _)
      exact hp_one i (hfaith (p i) (hp_mem i) hcent)
    omega
  have hdle : ∀ i, d i ≤ 2 := by
    intro i
    fin_cases i <;> simp [d, hd0le, hd1le, hd2le, hd3le, hd4le, hd5le, hd6le]
  have hle1 : d 0 + d 1 + d 2 ≤ 2 := by
    have h := hcle 0; rw [hpoint0] at h; exact h
  have hle2 : d 0 + d 3 + d 4 ≤ 2 := by
    have h := hcle 1; rw [hpoint1] at h; exact h
  have hle3 : d 0 + d 5 + d 6 ≤ 2 := by
    have h := hcle 2; rw [hpoint2] at h; exact h
  have hle4 : d 1 + d 3 + d 5 ≤ 2 := by
    have h := hcle 3; rw [hpoint3] at h; exact h
  have hle5 : d 1 + d 4 + d 6 ≤ 2 := by
    have h := hcle 4; rw [hpoint4] at h; exact h
  have hle6 : d 2 + d 3 + d 6 ≤ 2 := by
    have h := hcle 5; rw [hpoint5] at h; exact h
  have hle7 : d 2 + d 4 + d 5 ≤ 2 := by
    have h := hcle 6; rw [hpoint6] at h; exact h
  have hlt1 : d 0 + d 1 + d 2 < nF := by
    have h := hc_lt 0; rw [hpoint0] at h; exact h
  have hlt2 : d 0 + d 3 + d 4 < nF := by
    have h := hc_lt 1; rw [hpoint1] at h; exact h
  have hlt3 : d 0 + d 5 + d 6 < nF := by
    have h := hc_lt 2; rw [hpoint2] at h; exact h
  have hlt4 : d 1 + d 3 + d 5 < nF := by
    have h := hc_lt 3; rw [hpoint3] at h; exact h
  have hlt5 : d 1 + d 4 + d 6 < nF := by
    have h := hc_lt 4; rw [hpoint4] at h; exact h
  have hlt6 : d 2 + d 3 + d 6 < nF := by
    have h := hc_lt 5; rw [hpoint5] at h; exact h
  have hlt7 : d 2 + d 4 + d 5 < nF := by
    have h := hc_lt 6; rw [hpoint6] at h; exact h
  have hnval : d 0 + d 1 + d 2 + d 3 + d 4 + d 5 + d 6 = nF := hnsum.symm
  have hfano := fano_count
    ⟨d 0, by have := hdle 0; omega⟩ ⟨d 1, by have := hdle 1; omega⟩
    ⟨d 2, by have := hdle 2; omega⟩ ⟨d 3, by have := hdle 3; omega⟩
    ⟨d 4, by have := hdle 4; omega⟩ ⟨d 5, by have := hdle 5; omega⟩
    ⟨d 6, by have := hdle 6; omega⟩
    hle1 hle2 hle3 hle4 hle5 hle6 hle7
    (by rw [hnval]; exact hlt1) (by rw [hnval]; exact hlt2)
    (by rw [hnval]; exact hlt3) (by rw [hnval]; exact hlt4)
    (by rw [hnval]; exact hlt5) (by rw [hnval]; exact hlt6)
    (by rw [hnval]; exact hlt7)
  rw [← hnsum] at hfano
  have fixed_of_c_eq_zero : ∀ {i : Fin 7}, c i = 0 →
      ∀ x ∈ F, p i * x = x * p i → x = 1 := by
    intro i hi x hx hcomm
    have hcardC : Nat.card (C i) = 1 := by rw [hc i, hi, pow_zero]
    have hCbot : C i = ⊥ := Subgroup.eq_bot_of_card_eq _ hcardC
    have hxC : x ∈ C i := by
      refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hcomm
    rw [hCbot] at hxC
    simpa using hxC
  rcases hfano with h3 | ⟨h4, hzero⟩
  · left
    rw [hnF, h3]
  · right
    refine ⟨by rw [hnF, h4], ?_⟩
    have hc0 : d 0 + d 1 + d 2 = 0 → c 0 = 0 := by
      intro h; rw [hpoint0, h]
    have hc1 : d 0 + d 3 + d 4 = 0 → c 1 = 0 := by
      intro h; rw [hpoint1, h]
    have hc2 : d 0 + d 5 + d 6 = 0 → c 2 = 0 := by
      intro h; rw [hpoint2, h]
    have hc3 : d 1 + d 3 + d 5 = 0 → c 3 = 0 := by
      intro h; rw [hpoint3, h]
    have hc4 : d 1 + d 4 + d 6 = 0 → c 4 = 0 := by
      intro h; rw [hpoint4, h]
    have hc5 : d 2 + d 3 + d 6 = 0 → c 5 = 0 := by
      intro h; rw [hpoint5, h]
    have hc6 : d 2 + d 4 + d 5 = 0 → c 6 = 0 := by
      intro h; rw [hpoint6, h]
    rcases hzero with h0 | h1 | h2 | h3 | h4' | h5 | h6
    · exact ⟨p 0, hp_mem 0, hp_one 0, fixed_of_c_eq_zero (hc0 h0)⟩
    · exact ⟨p 1, hp_mem 1, hp_one 1, fixed_of_c_eq_zero (hc1 h1)⟩
    · exact ⟨p 2, hp_mem 2, hp_one 2, fixed_of_c_eq_zero (hc2 h2)⟩
    · exact ⟨p 3, hp_mem 3, hp_one 3, fixed_of_c_eq_zero (hc3 h3)⟩
    · exact ⟨p 4, hp_mem 4, hp_one 4, fixed_of_c_eq_zero (hc4 h4')⟩
    · exact ⟨p 5, hp_mem 5, hp_one 5, fixed_of_c_eq_zero (hc5 h5)⟩
    · exact ⟨p 6, hp_mem 6, hp_one 6, fixed_of_c_eq_zero (hc6 h6)⟩

end CFSG.GF2Type.Smith1979.OmegaPlus
