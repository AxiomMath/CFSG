module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74ADefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F1Rad
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Coprime
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RC

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin
open scoped MatrixGroups

theorem eq_of_commute_upperSL2 {K : Type} [Field K] {c : K} (hc : c ≠ 0) {M : SL(2, K)}
    (h : M * upperSL2 c = upperSL2 c * M) : ∃ d : K, M = upperSL2 d ∨ M = -upperSL2 d := by
  have hm := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_upperSL2] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have h10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := e00.resolve_left hc
  have h11 : (M : Matrix (Fin 2) (Fin 2) K) 1 1 = (M : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have e : c * ((M : Matrix (Fin 2) (Fin 2) K) 1 1 -
        (M : Matrix (Fin 2) (Fin 2) K) 0 0) = 0 := by
      linear_combination -e01
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hc)
  have hdet := M.det_coe
  rw [Matrix.det_fin_two, h10, h11, mul_zero, sub_zero] at hdet
  have hsq : ((M : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) *
      ((M : Matrix (Fin 2) (Fin 2) K) 0 0 + 1) = 0 := by
    linear_combination hdet
  rcases mul_eq_zero.mp hsq with h1 | h1
  · have h1' : (M : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := sub_eq_zero.mp h1
    refine ⟨(M : Matrix (Fin 2) (Fin 2) K) 0 1, Or.inl ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_upperSL2, h10, h11, h1']
  · have h1' : (M : Matrix (Fin 2) (Fin 2) K) 0 0 = -1 := eq_neg_of_add_eq_zero_left h1
    refine ⟨-(M : Matrix (Fin 2) (Fin 2) K) 0 1, Or.inr ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_upperSL2, h10, h11, h1', Matrix.SpecialLinearGroup.coe_neg]

theorem commute_of_commute_upperSL2 {K : Type} [Field K] {c : K} (hc : c ≠ 0) {M N : SL(2, K)}
    (hM : M * upperSL2 c = upperSL2 c * M) (hN : N * upperSL2 c = upperSL2 c * N) :
    M * N = N * M := by
  obtain ⟨d, hd⟩ := eq_of_commute_upperSL2 hc hM
  obtain ⟨e, he⟩ := eq_of_commute_upperSL2 hc hN
  have h : Commute (upperSL2 d) (upperSL2 e) := by
    show upperSL2 d * upperSL2 e = upperSL2 e * upperSL2 d
    rw [← upperSL2_add, ← upperSL2_add, add_comm]
  rcases hd with rfl | rfl <;> rcases he with rfl | rfl
  · exact h
  · exact h.neg_right
  · exact h.neg_left
  · exact h.neg_left.neg_right

theorem conj_mul_conj_comm {G : Type*} [Group G] (g : G) {a x : G} (h : a * x = x * a) :
    g * a * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * a * g⁻¹) := by
  calc g * a * g⁻¹ * (g * x * g⁻¹) = g * (a * x) * g⁻¹ := by group
    _ = g * (x * a) * g⁻¹ := by rw [h]
    _ = g * x * g⁻¹ * (g * a * g⁻¹) := by group

theorem commute_of_mem_range_of_conj {K : Type} [Field K] {X : Type*} [Group X]
    {ρ : SL(2, K) →* X} (hρ : Function.Injective ρ) {x g : X} (hg : g ∈ ρ.range) {c : K}
    (hc : c ≠ 0) (hgx : g * x * g⁻¹ = ρ (upperSL2 c)) {a b : X} (ha : a ∈ ρ.range)
    (hb : b ∈ ρ.range) (hax : a * x = x * a) (hbx : b * x = x * b) : a * b = b * a := by
  obtain ⟨M, hM⟩ := mul_mem (mul_mem hg ha) (inv_mem hg)
  obtain ⟨N, hN⟩ := mul_mem (mul_mem hg hb) (inv_mem hg)
  have hMc : M * upperSL2 c = upperSL2 c * M := hρ (by
    rw [map_mul, map_mul, hM, ← hgx]
    exact conj_mul_conj_comm g hax)
  have hNc : N * upperSL2 c = upperSL2 c * N := hρ (by
    rw [map_mul, map_mul, hN, ← hgx]
    exact conj_mul_conj_comm g hbx)
  have hMN := congrArg ρ (commute_of_commute_upperSL2 hc hMc hNc)
  rw [map_mul, map_mul, hM, hN] at hMN
  apply (MulAut.conj g).injective
  simp only [MulAut.conj_apply]
  calc g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := hMN
    _ = g * (b * a) * g⁻¹ := by group

@[expose] def upperHom (K : Type) [Field K] : Multiplicative K →* SL(2, K) where
  toFun c := upperSL2 c.toAdd
  map_one' := upperSL2_zero
  map_mul' a b := upperSL2_add a.toAdd b.toAdd

theorem upperHom_apply {K : Type} [Field K] (c : Multiplicative K) :
    upperHom K c = upperSL2 c.toAdd := rfl

theorem injective_upperHom {K : Type} [Field K] : Function.Injective (upperHom K) := by
  intro a b h
  have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simpa [upperHom_apply, coe_upperSL2] using this

theorem exists_mul_of_mem_sup {G : Type} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hBN : B ≤ normalizer (A : Set G) := le_normalizer_of_conj_mem (fun b hb a ha => by
    rw [← h a ha b hb, mul_inv_cancel_right]
    exact ha) le_rfl
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left A B hBN] at hx'
  obtain ⟨a, ha, b, hb, hab⟩ := hx'
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem mem_normalizer_of_map_conj_eq {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom = A) : g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := by simpa using hyx
    rw [← this]
    exact hy

theorem card_sup_of_commute {G : Type} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hBN : B ≤ normalizer (A : Set G) := le_normalizer_of_conj_mem (fun b hb a ha => by
    rw [← h a ha b hb, mul_inv_cancel_right]
    exact ha) le_rfl
  have e := card_sup_mul_card_inf_of_le_normalizer' hBN
  rw [hAB, card_bot, mul_one] at e
  exact e

section Model

variable {K : Type} [Field K] {p f : ℕ}

theorem ringChar_eq [Finite K] (hp : p.Prime) (hK : Nat.card K = p ^ f) : ringChar K = p := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hcp, hn⟩ := FiniteField.card K (ringChar K)
  have h1 : ringChar K ∣ p ^ f := by
    rw [← hK, Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.ne_zero
  exact (Nat.prime_dvd_prime_iff_eq hcp hp).mp (hcp.dvd_of_dvd_pow h1)

theorem qThree_pow_p [Finite K] (hp : p.Prime) (hK : Nat.card K = p ^ f) : qThree K ^ p = 1 := by
  rw [qThree_eq, ← ringChar_eq hp hK]
  exact rootThree_pow_char 4 1

theorem qThree_ne_one' : qThree K ≠ 1 := by
  intro h
  have h1 : upperSL2 (1 : K) = 1 := injective_shortSeven (h.trans (map_one _).symm)
  have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h1
  simp [coe_upperSL2] at this

theorem qThree_mem_spinJ₁ : qThree K ∈ spinJ₁ K := ⟨_, rfl⟩

abbrev uThree (K : Type) [Field K] : Subgroup (spinGroup (quadOdd 3 K)) :=
  ((shortSeven K).comp (upperHom K)).range

theorem mem_uThree {x : spinGroup (quadOdd 3 K)} :
    x ∈ uThree K ↔ ∃ c : K, shortSeven K (upperSL2 c) = x :=
  ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩

theorem uThree_le_spinJ₁ : uThree K ≤ spinJ₁ K := by
  rintro _ ⟨c, rfl⟩
  exact ⟨_, rfl⟩

theorem qThree_mem_uThree : qThree K ∈ uThree K := mem_uThree.mpr ⟨1, rfl⟩

theorem commute_uThree {a b : spinGroup (quadOdd 3 K)} (ha : a ∈ uThree K) (hb : b ∈ uThree K) :
    a * b = b * a := by
  obtain ⟨c, rfl⟩ := mem_uThree.mp ha
  obtain ⟨d, rfl⟩ := mem_uThree.mp hb
  rw [← map_mul, ← map_mul, ← upperSL2_add, ← upperSL2_add, add_comm]

theorem uThree_le_centralizer :
    uThree K ≤ centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) := fun _ hu =>
  mem_centralizer_singleton_iff.mpr (commute_uThree hu qThree_mem_uThree)

theorem card_uThree [Finite K] : Nat.card ↥(uThree K) = Nat.card K := by
  have hinj : Function.Injective ((shortSeven K).comp (upperHom K)) :=
    injective_shortSeven.comp injective_upperHom
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

theorem spinZ_not_mem_uThree [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    spinZ K ∉ uThree K := by
  intro hz
  obtain ⟨c, hc⟩ := mem_uThree.mp hz
  have h2 := two_ne_zero_spin hp hp2 hK
  have h1 : upperSL2 c = -1 := injective_shortSeven
    (hc.trans (shortSeven_neg_one (nondegenerate_quadOdd 3 K).ne_zero).symm)
  have h00 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h1
  have e : (1 : K) = -1 := by simpa [coe_upperSL2] using h00
  exact h2 (by linear_combination e)

theorem mem_J₁_centralizer_qThree {a : spinGroup (quadOdd 3 K)} (ha : a ∈ spinJ₁ K)
    (haq : a * qThree K = qThree K * a) : a ∈ uThree K ∨ spinZ K * a ∈ uThree K := by
  obtain ⟨M, rfl⟩ := ha
  have hM : M * upperSL2 1 = upperSL2 1 * M := injective_shortSeven (by
    rw [map_mul, map_mul]
    exact haq)
  obtain ⟨d, rfl | rfl⟩ := eq_of_commute_upperSL2 one_ne_zero hM
  · exact Or.inl (mem_uThree.mpr ⟨d, rfl⟩)
  · refine Or.inr (mem_uThree.mpr ⟨d, ?_⟩)
    rw [← neg_one_mul (upperSL2 d), map_mul,
      shortSeven_neg_one (nondegenerate_quadOdd 3 K).ne_zero, ← mul_assoc,
      CliffordAlgebra.spinGroup.negOne_mul_self _ (nondegenerate_quadOdd 3 K).ne_zero, one_mul]

theorem commute_spinJ₂_spinJ₃' [Finite K] (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    ∀ b ∈ spinJ₂ K, ∀ c ∈ spinJ₃ K, b * c = c * b := fun _ hb _ hc =>
  commute_spinJ₂_spinJ₃ (four_le_card_spin hK h5) hb hc

theorem commute_spinJ₁_sup [Finite K] {a : spinGroup (quadOdd 3 K)} (ha : a ∈ spinJ₁ K)
    {x : spinGroup (quadOdd 3 K)} (hx : x ∈ spinJ₂ K ⊔ spinJ₃ K) : a * x = x * a := by
  have hle : spinJ₂ K ⊔ spinJ₃ K ≤ centralizer ({a} : Set (spinGroup (quadOdd 3 K))) :=
    sup_le (fun b hb => mem_centralizer_singleton_iff.mpr (commute_spinJ₁_spinJ₂ ha hb).symm)
      (fun c hc => mem_centralizer_singleton_iff.mpr (commute_spinJ₁_spinJ₃ ha hc).symm)
  exact (mem_centralizer_singleton_iff.mp (hle hx)).symm

theorem spinZ_mem_sup [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    spinZ K ∈ spinJ₂ K ⊔ spinJ₃ K := by
  obtain ⟨-, -, hzc, htt, -, -, -, ht2J, hzt3J, -⟩ := spinZ_facts hp hp2 hK
  have e : spinZ K = tSeven K * (spinZ K * tSeven K) := by
    rw [← mul_assoc, mem_center_iff.mp hzc (tSeven K), mul_assoc, htt, mul_one]
  rw [e]
  exact mul_mem (mem_sup_left ht2J) (mem_sup_right hzt3J)

theorem eq_one_or_eq_spinZ_of_mem_sup [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {x : spinGroup (quadOdd 3 K)}
    (hx1 : x ∈ spinJ₁ K) (hx : x ∈ spinJ₂ K ⊔ spinJ₃ K) : x = 1 ∨ x = spinZ K := by
  have h4 := four_le_card_spin hK h5
  obtain ⟨b, hb, c, hc, rfl⟩ := exists_mul_of_mem_sup (commute_spinJ₂_spinJ₃' hK h5) hx
  have hker : (((⟨(b * c)⁻¹, inv_mem hx1⟩, ⟨b, hb⟩), ⟨c, hc⟩) :
      (spinJ₁ K × spinJ₂ K) × spinJ₃ K) ∈ (spinMul h4).ker := by
    rw [MonoidHom.mem_ker, spinMul_apply]
    show (b * c)⁻¹ * b * c = 1
    group
  rcases (mem_ker_spinMul_iff hp hp2 hK h5 h4 _).mp hker with h | h
  · left
    have h' : ((b * c)⁻¹ : spinGroup (quadOdd 3 K)) = 1 := by
      have := congrArg (fun v : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        (v.1.1 : spinGroup (quadOdd 3 K))) h
      simpa using this
    exact inv_eq_one.mp h'
  · right
    have h' : ((b * c)⁻¹ : spinGroup (quadOdd 3 K)) = spinZ K := by
      have := congrArg (fun v : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        (v.1.1 : spinGroup (quadOdd 3 K))) h
      simpa using this
    calc b * c = ((b * c)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (spinZ K)⁻¹ := by rw [h']
      _ = spinZ K := inv_eq_of_mul_eq_one_right
          (CliffordAlgebra.spinGroup.negOne_mul_self _ (nondegenerate_quadOdd 3 K).ne_zero)

theorem spinJ₂_inf_spinJ₃ [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) : spinJ₂ K ⊓ spinJ₃ K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact (mem_bot).mpr (eq_one_of_mem_spinJ₂_of_mem_spinJ₃ hp hp2 hK h5 (mem_inf.mp hx).1
    (mem_inf.mp hx).2)

theorem card_spinJ₂ [Finite K] : Nat.card ↥(spinJ₂ K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
  card_range_sl2 _ (longSL2_injective (oddFrame 3 K).toHypFrame fin3_zero_ne_one true true)

theorem card_spinJ₃ [Finite K] : Nat.card ↥(spinJ₃ K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
  card_range_sl2 _ (longSL2_injective (oddFrame 3 K).toHypFrame fin3_zero_ne_one true false)

theorem card_spinJ₂_sup_spinJ₃ [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    Nat.card ↥(spinJ₂ K ⊔ spinJ₃ K) = Nat.card ↥(spinJ₂ K) * Nat.card ↥(spinJ₃ K) :=
  card_sup_of_commute (commute_spinJ₂_spinJ₃' hK h5) (spinJ₂_inf_spinJ₃ hp hp2 hK h5)

theorem sup_inf_uThree [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) : (spinJ₂ K ⊔ spinJ₃ K) ⊓ uThree K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxs, hxu⟩ := mem_inf.mp hx
  rcases eq_one_or_eq_spinZ_of_mem_sup hp hp2 hK h5 (uThree_le_spinJ₁ hxu) hxs with h | h
  · exact (mem_bot).mpr h
  · exact absurd (h ▸ hxu) (spinZ_not_mem_uThree hp hp2 hK)

theorem centralizer_inf_eq [Finite K] (hA2 : A2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) =
        (spinJ₂ K ⊔ spinJ₃ K) ⊔ uThree K := by
  have h4 := four_le_card_spin hK h5
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨hJ₁C, hJ₂C, hJ₃C⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  have hzS : spinZ K ∈ (spinJ₂ K ⊔ spinJ₃ K) ⊔ uThree K :=
    mem_sup_left (spinZ_mem_sup hp hp2 hK)
  apply le_antisymm
  · intro x hx
    have hxE : x ∈ spinE K := hA2 K hodd hx
    have hxq := (mem_inf.mp hx).2
    rw [← range_spinMul h4] at hxE
    obtain ⟨⟨⟨a, b⟩, c⟩, rfl⟩ := hxE
    rw [spinMul_apply] at hxq ⊢
    change (a : spinGroup (quadOdd 3 K)) * b * c ∈ _
    change (a : spinGroup (quadOdd 3 K)) * b * c ∈ centralizer _ at hxq
    have hbq : (b : spinGroup (quadOdd 3 K)) * qThree K = qThree K * b :=
      (commute_spinJ₁_spinJ₂ qThree_mem_spinJ₁ b.2).symm
    have hcq : (c : spinGroup (quadOdd 3 K)) * qThree K = qThree K * c :=
      (commute_spinJ₁_spinJ₃ qThree_mem_spinJ₁ c.2).symm
    have haq : (a : spinGroup (quadOdd 3 K)) * qThree K = qThree K * a :=
      comm_left_of_comm hbq hcq (mem_centralizer_singleton_iff.mp hxq)
    have haS : (a : spinGroup (quadOdd 3 K)) ∈ (spinJ₂ K ⊔ spinJ₃ K) ⊔ uThree K := by
      rcases mem_J₁_centralizer_qThree a.2 haq with ha | ha
      · exact mem_sup_right ha
      · have e : (a : spinGroup (quadOdd 3 K)) = (spinZ K)⁻¹ * (spinZ K * a) :=
          (inv_mul_cancel_left _ _).symm
        rw [e]
        exact mul_mem (inv_mem hzS) (mem_sup_right ha)
    exact mul_mem (mul_mem haS (mem_sup_left (mem_sup_left b.2)))
      (mem_sup_left (mem_sup_right c.2))
  · refine sup_le (sup_le (le_inf hJ₂C fun b hb => mem_centralizer_singleton_iff.mpr
      (commute_spinJ₁_spinJ₂ qThree_mem_spinJ₁ hb).symm) (le_inf hJ₃C fun c hc =>
        mem_centralizer_singleton_iff.mpr (commute_spinJ₁_spinJ₃ qThree_mem_spinJ₁ hc).symm))
      (le_inf (uThree_le_spinJ₁.trans hJ₁C) uThree_le_centralizer)

theorem card_centralizer_inf [Finite K] (hA2 : A2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    Nat.card ↥(centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) =
        Nat.card ↥(spinJ₂ K) * Nat.card ↥(spinJ₃ K) * Nat.card K := by
  rw [centralizer_inf_eq hA2 hp hp2 hK h5, card_sup_of_commute
    (fun x hx u hu => (commute_spinJ₁_sup (uThree_le_spinJ₁ hu) hx).symm)
    (sup_inf_uThree hp hp2 hK h5), card_spinJ₂_sup_spinJ₃ hp hp2 hK h5, card_uThree]

theorem commute_of_mem_spinJ₁ [Finite K] (hA3 : A3) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {x : spinGroup (quadOdd 3 K)} (hx : x ∈ spinJ₁ K) (hx1 : x ≠ 1)
    (hxp : x ^ p = 1) {a b : spinGroup (quadOdd 3 K)} (ha : a ∈ spinJ₁ K) (hb : b ∈ spinJ₁ K)
    (hax : a * x = x * a) (hbx : b * x = x * b) : a * b = b * a := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, -, h3, -⟩ := hA3 K hodd
  obtain ⟨g, hg, c, hc, hgx⟩ := h3 x hx hx1 (by rw [ringChar_eq hp hK]; exact hxp)
  exact commute_of_mem_range_of_conj injective_shortSeven hg hc hgx ha hb hax hbx

theorem commute_of_mem_spinJ₂ [Finite K] (hA3 : A3) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {x : spinGroup (quadOdd 3 K)} (hx : x ∈ spinJ₂ K) (hx1 : x ≠ 1)
    (hxp : x ^ p = 1) {a b : spinGroup (quadOdd 3 K)} (ha : a ∈ spinJ₂ K) (hb : b ∈ spinJ₂ K)
    (hax : a * x = x * a) (hbx : b * x = x * b) : a * b = b * a := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, -, -, h4⟩ := hA3 K hodd
  obtain ⟨g, hg, c, hc, hgx⟩ := h4 x hx hx1 (by rw [ringChar_eq hp hK]; exact hxp)
  exact commute_of_mem_range_of_conj
    (longSL2_injective (oddFrame 3 K).toHypFrame fin3_zero_ne_one true true) hg hc hgx ha hb hax hbx

theorem mem_fourT [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {x : spinGroup (quadOdd 3 K)} (hx : x ∈ fourT K) :
    x = 1 ∨ x = spinZ K ∨ x = tSeven K ∨ x = spinZ K * tSeven K := by
  obtain ⟨hzz, -, hzc, htt, -⟩ := spinZ_facts hp hp2 hK
  have hzt : spinZ K * tSeven K = tSeven K * spinZ K := (mem_center_iff.mp hzc _).symm
  have hle : fourT K ≤ CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions (spinZ K)
      (tSeven K) hzz htt hzt := by
    show closure ({spinZ K, tSeven K} : Set (spinGroup (quadOdd 3 K))) ≤ _
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  rcases hle hx with h | h | h | h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inl h

theorem spinZ_mem_fourT : spinZ K ∈ fourT K := subset_closure (Set.mem_insert _ _)

theorem tSeven_mem_fourT : tSeven K ∈ fourT K := subset_closure (Set.mem_insert_of_mem _ rfl)

theorem mem_normalizer_fourT_of_conj [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f)
    {g : spinGroup (quadOdd 3 K)} (ht : g * tSeven K * g⁻¹ ∈ fourT K) :
    g ∈ normalizer (fourT K : Set (spinGroup (quadOdd 3 K))) := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  obtain ⟨-, -, hzc, -⟩ := spinZ_facts hp hp2 hK
  have hz : g * spinZ K * g⁻¹ ∈ fourT K := by
    rw [mem_center_iff.mp hzc g, mul_inv_cancel_right]
    exact spinZ_mem_fourT
  have hle : (fourT K).map (MulAut.conj g).toMonoidHom ≤ fourT K := by
    show (closure ({spinZ K, tSeven K} : Set (spinGroup (quadOdd 3 K)))).map
      (MulAut.conj g).toMonoidHom ≤ closure ({spinZ K, tSeven K} : Set (spinGroup (quadOdd 3 K)))
    rw [MonoidHom.map_closure, closure_le, Set.image_pair]
    rintro _ (rfl | rfl)
    · exact hz
    · exact ht
  have heq : (fourT K).map (MulAut.conj g).toMonoidHom = fourT K :=
    eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj g).injective).ge
  exact mem_normalizer_of_map_conj_eq heq

theorem conj_t_of_mem_normalizer_fourT [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {m : spinGroup (quadOdd 3 K)}
    (hm : m ∈ normalizer (fourT K : Set (spinGroup (quadOdd 3 K)))) :
    m * tSeven K * m⁻¹ = tSeven K ∨ m * tSeven K * m⁻¹ = spinZ K * tSeven K := by
  obtain ⟨-, -, hzc, -, ht1, htc, -⟩ := spinZ_facts hp hp2 hK
  rcases mem_fourT hp hp2 hK ((mem_normalizer_iff.mp hm (tSeven K)).mp tSeven_mem_fourT) with
    h | h | h | h
  · exfalso
    apply ht1
    calc tSeven K = m⁻¹ * (m * tSeven K * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group
  · exfalso
    apply htc
    have e : tSeven K = spinZ K := by
      calc tSeven K = m⁻¹ * (m * tSeven K * m⁻¹) * m := by group
        _ = m⁻¹ * (spinZ K * m) := by rw [h]; group
        _ = spinZ K := by rw [← (mem_center_iff.mp hzc m)]; group
    rw [e]
    exact hzc
  · exact Or.inl h
  · exact Or.inr h

end Model

end CFSG.ComponentClassification.HarrisLit.T1.S74
