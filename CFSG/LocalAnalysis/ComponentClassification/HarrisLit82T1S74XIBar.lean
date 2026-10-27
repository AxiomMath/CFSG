module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74XBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74GComp

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin
open scoped MatrixGroups

theorem conj_mem_centralizer_of_conj {G : Type*} [Group G] {g a b x : G}
    (hab : g * a * g⁻¹ = b) (hx : x ∈ centralizer ({a} : Set G)) :
    g * x * g⁻¹ ∈ centralizer ({b} : Set G) := by
  rw [mem_centralizer_singleton_iff] at hx ⊢
  rw [← hab]
  calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
    _ = g * (a * x) * g⁻¹ := by rw [hx]
    _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group

theorem commute_of_conj_eq {G : Type*} [Group G] {g x : G} (h : g * x * g⁻¹ = x) :
    g * x = x * g := by
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [h]

theorem mem_normalizer_of_involution {G : Type*} [Group G] {g : G} (hgg : g * g = 1)
    {A : Subgroup G} (h : ∀ x ∈ A, g * x * g⁻¹ ∈ A) : g ∈ normalizer (A : Set G) := by
  have hg : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have e : g * (g * x * g⁻¹) * g⁻¹ = x := by
    rw [hg]
    calc g * (g * x * g) * g = (g * g) * x * (g * g) := by group
      _ = x := by rw [hgg, one_mul, mul_one]
  rw [← e]
  exact h _ hx

section Model

variable {K : Type} [Field K] {p f : ℕ}

theorem map_conj_spinJ_of_normalizes [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {g : spinGroup (quadOdd 3 K)}
    (hg : ∀ x ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))),
      g * x * g⁻¹ ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))
    {J : Subgroup (spinGroup (quadOdd 3 K))} (hJ : J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) :
    J.map (MulAut.conj g).toMonoidHom = spinJ₁ K ∨ J.map (MulAut.conj g).toMonoidHom = spinJ₂ K ∨
      J.map (MulAut.conj g).toMonoidHom = spinJ₃ K := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hEC := spinE_le_centralizer hp hp2 hK
  obtain ⟨hJC, -, -, -, hJq⟩ := spinJ_props hp hp2 hK h5 hJ
  have hmapC : ∀ A : Subgroup (spinGroup (quadOdd 3 K)),
      A ≤ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) →
      A.map (MulAut.conj g).toMonoidHom ≤
        centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) := by
    rintro A hA _ ⟨x, hx, rfl⟩
    exact hg x (hA hx)
  have hEperf := isPerfect_spinE hp hp2 hK h5
  have hEperf' : Group.IsPerfect ↥((spinE K).map (MulAut.conj g).toMonoidHom) :=
    Group.IsPerfect.map (H := spinE K) (MulAut.conj g).toMonoidHom
  have hEg : (spinE K).map (MulAut.conj g).toMonoidHom = spinE K :=
    eq_of_le_of_card_ge (le_spinE_of_isPerfect hp hp2 hK h5 (hmapC _ hEC) hEperf')
      (card_map_of_injective (MulAut.conj g).injective).ge
  have hJperf : Group.IsPerfect ↥J := hJq.1
  have hJgperf : Group.IsPerfect ↥(J.map (MulAut.conj g).toMonoidHom) :=
    Group.IsPerfect.map (H := J) (MulAut.conj g).toMonoidHom
  have hJgE : J.map (MulAut.conj g).toMonoidHom ≤ spinE K :=
    le_spinE_of_isPerfect hp hp2 hK h5 (hmapC J hJC) hJgperf
  have hJgn : ∀ e ∈ spinE K, ∀ x ∈ J.map (MulAut.conj g).toMonoidHom,
      e * x * e⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom := by
    intro e he x hx
    rw [← hEg] at he
    obtain ⟨e', he', rfl⟩ := he
    obtain ⟨j, hj, rfl⟩ := hx
    exact ⟨e' * j * e'⁻¹, conj_mem_spinJ hp hp2 hK h5 hJ he' hj, by simp only [map_mul, map_inv]⟩
  have hJgq : IsTwoQuasisimple ↥(J.map (MulAut.conj g).toMonoidHom) :=
    isTwoQuasisimple_of_mulEquiv
      (J.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
      (isTwoQuasisimple_spinJ hp hp2 hK h5 hJ)
  exact eq_spinJ_of_normal hp hp2 hK h5 hJgE hJgn hJgq

theorem eq_of_mul_eq_mul_J₂J₃ [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) {b b' c c' : spinGroup (quadOdd 3 K)} (hb : b ∈ spinJ₂ K)
    (hb' : b' ∈ spinJ₂ K) (hc : c ∈ spinJ₃ K) (hc' : c' ∈ spinJ₃ K) (h : b * c = b' * c') :
    b = b' ∧ c = c' := by
  have e : b'⁻¹ * b = c' * c⁻¹ := by
    calc b'⁻¹ * b = b'⁻¹ * (b * c) * c⁻¹ := by group
      _ = b'⁻¹ * (b' * c') * c⁻¹ := by rw [h]
      _ = c' * c⁻¹ := by group
  have h3 : b'⁻¹ * b ∈ spinJ₃ K := by
    rw [e]
    exact mul_mem hc' (inv_mem hc)
  have h1 : b'⁻¹ * b = 1 :=
    eq_one_of_mem_spinJ₂_of_mem_spinJ₃ hp hp2 hK h5 (mul_mem (inv_mem hb') hb) h3
  refine ⟨(inv_mul_eq_one.mp h1).symm, ?_⟩
  rw [e] at h1
  exact (mul_inv_eq_one.mp h1).symm

theorem eq_one_of_mem_uThree_of_mul_self [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {u : spinGroup (quadOdd 3 K)} (hu : u ∈ uThree K)
    (huu : u * u = 1) : u = 1 := by
  obtain ⟨c, rfl⟩ := mem_uThree.mp hu
  have h2 := two_ne_zero_spin hp hp2 hK
  rw [← map_mul, ← upperSL2_add] at huu
  have h1 : upperSL2 (c + c) = 1 := injective_shortSeven (huu.trans (map_one _).symm)
  have h01 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h1
  have e : c + c = 0 := by simpa [coe_upperSL2] using h01
  have hc : c = 0 := by
    have : (2 : K) * c = 0 := by linear_combination e
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [hc, upperSL2_zero, map_one]

theorem spinJ₂_le_centralizer_inf [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    spinJ₂ K ≤ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) :=
  le_inf (spinJ_le_centralizer (K := K) hp hp2 hK).2.1 fun _ hb =>
    mem_centralizer_singleton_iff.mpr (commute_spinJ₁_spinJ₂ qThree_mem_spinJ₁ hb).symm

theorem sup_le_centralizer_inf [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    spinJ₂ K ⊔ spinJ₃ K ≤ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) :=
  sup_le (spinJ₂_le_centralizer_inf hp hp2 hK)
    (le_inf (spinJ_le_centralizer (K := K) hp hp2 hK).2.2 fun _ hc =>
      mem_centralizer_singleton_iff.mpr (commute_spinJ₁_spinJ₃ qThree_mem_spinJ₁ hc).symm)

theorem uThree_le_centralizer_inf [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    uThree K ≤ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) :=
  le_inf (uThree_le_spinJ₁.trans (spinJ_le_centralizer (K := K) hp hp2 hK).1)
    uThree_le_centralizer

abbrev mX (K : Type) [Field K] : Subgroup (spinGroup (quadOdd 3 K)) :=
  centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ⊓
    normalizer (fourT K : Set (spinGroup (quadOdd 3 K)))

theorem centralizer_inf_le_mX [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ≤ mX K := by
  intro x hx
  obtain ⟨hxt, hxq⟩ := mem_inf.mp hx
  refine mem_inf.mpr ⟨hxq, mem_normalizer_fourT_of_conj hp hp2 hK ?_⟩
  rw [mem_centralizer_singleton_iff.mp hxt, mul_inv_cancel_right]
  exact tSeven_mem_fourT

end Model

structure IsIBar (K : Type) [Field K] (i : spinGroup (quadOdd 3 K)) : Prop where
  mul_self : i * i = 1
  commute_J₁ : ∀ j ∈ spinJ₁ K, i * j = j * i
  conj_t : i * tSeven K * i⁻¹ = spinZ K * tSeven K

theorem exists_isIBar (hA1 : A1) {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K)) :
    ∃ i : spinGroup (quadOdd 3 K), IsIBar K i := by
  obtain ⟨i, h1, h2, h3⟩ := hA1 K hodd
  exact ⟨i, h1, h2, h3⟩

namespace IsIBar

variable {K : Type} [Field K] {p f : ℕ} {i : spinGroup (quadOdd 3 K)}

theorem inv_eq (hI : IsIBar K i) : i⁻¹ = i := inv_eq_of_mul_eq_one_right hI.mul_self

theorem conj_conj (hI : IsIBar K i) (x : spinGroup (quadOdd 3 K)) :
    i * (i * x * i⁻¹) * i⁻¹ = x := by
  rw [hI.inv_eq]
  calc i * (i * x * i) * i = (i * i) * x * (i * i) := by group
    _ = x := by rw [hI.mul_self, one_mul, mul_one]

theorem commute_qThree (hI : IsIBar K i) : i * qThree K = qThree K * i :=
  hI.commute_J₁ _ qThree_mem_spinJ₁

theorem mem_centralizer_qThree (hI : IsIBar K i) :
    i ∈ centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) :=
  mem_centralizer_singleton_iff.mpr hI.commute_qThree

theorem conj_qThree (hI : IsIBar K i) : i * qThree K * i⁻¹ = qThree K := by
  rw [hI.commute_qThree, mul_inv_cancel_right]

theorem conj_mem_centralizer_qThree (hI : IsIBar K i) {x : spinGroup (quadOdd 3 K)}
    (hx : x ∈ centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) :
    i * x * i⁻¹ ∈ centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) :=
  conj_mem_centralizer_of_conj hI.conj_qThree hx

variable [Finite K]

theorem conj_zt (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    i * (spinZ K * tSeven K) * i⁻¹ = tSeven K := by
  obtain ⟨hzz, -, hzc, -⟩ := spinZ_facts hp hp2 hK
  have hzi : i * spinZ K * i⁻¹ = spinZ K := by
    rw [mem_center_iff.mp hzc i, mul_inv_cancel_right]
  calc i * (spinZ K * tSeven K) * i⁻¹ = (i * spinZ K * i⁻¹) * (i * tSeven K * i⁻¹) := by group
    _ = spinZ K * (spinZ K * tSeven K) := by rw [hzi, hI.conj_t]
    _ = tSeven K := by rw [← mul_assoc, hzz, one_mul]

theorem not_commute_t (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : i * tSeven K ≠ tSeven K * i := by
  obtain ⟨-, hz1, -⟩ := spinZ_facts hp hp2 hK
  intro h
  have h1 := hI.conj_t
  rw [h, mul_inv_cancel_right] at h1
  apply hz1
  calc spinZ K = spinZ K * tSeven K * (tSeven K)⁻¹ := by group
    _ = 1 := by rw [← h1]; group

theorem not_mem_centralizer_t (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : i ∉ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) :=
  fun h => hI.not_commute_t hp hp2 hK (mem_centralizer_singleton_iff.mp h)

theorem ne_one (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    i ≠ 1 := fun h => hI.not_commute_t hp hp2 hK (by rw [h, one_mul, mul_one])

theorem orderOf_eq (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    orderOf i = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact hI.mul_self) (hI.ne_one hp hp2 hK)

theorem conj_mem_centralizer_t (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {x : spinGroup (quadOdd 3 K)}
    (hx : x ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) :
    i * x * i⁻¹ ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) := by
  obtain ⟨-, -, hzc, -⟩ := spinZ_facts hp hp2 hK
  have h := conj_mem_centralizer_of_conj hI.conj_t hx
  rwa [centralizer_mul_of_mem_center hzc] at h

theorem mem_normalizer (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : i ∈ normalizer (fourT K : Set (spinGroup (quadOdd 3 K))) :=
  mem_normalizer_fourT_of_conj hp hp2 hK (by
    rw [hI.conj_t]
    exact mul_mem spinZ_mem_fourT tSeven_mem_fourT)

theorem mem_mX (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    i ∈ mX K :=
  mem_inf.mpr ⟨hI.mem_centralizer_qThree, hI.mem_normalizer hp hp2 hK⟩

theorem map_spinJ₂ (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) : (spinJ₂ K).map (MulAut.conj i).toMonoidHom = spinJ₃ K := by
  obtain ⟨hzz, -, hzc, -, -, htc, -, ht2J, hzt3J, -⟩ := spinZ_facts hp hp2 hK
  have hzt1 : spinZ K * tSeven K ≠ 1 := fun h => htc (by
    have e : tSeven K = spinZ K := by
      calc tSeven K = (spinZ K)⁻¹ := eq_inv_of_mul_eq_one_right h
        _ = spinZ K := inv_eq_of_mul_eq_one_right hzz
    rw [e]
    exact hzc)
  have hmem : spinZ K * tSeven K ∈ (spinJ₂ K).map (MulAut.conj i).toMonoidHom :=
    ⟨tSeven K, ht2J, hI.conj_t⟩
  rcases map_conj_spinJ_of_normalizes hp hp2 hK h5
    (fun x hx => hI.conj_mem_centralizer_t hp hp2 hK hx) (Or.inr (Or.inl rfl)) with h | h | h
  · rw [h] at hmem
    exact absurd (eq_one_of_mem_spinJ₁_of_mem_spinJ₃ hp hp2 hK h5 hmem hzt3J) hzt1
  · rw [h] at hmem
    exact absurd (eq_one_of_mem_spinJ₂_of_mem_spinJ₃ hp hp2 hK h5 hmem hzt3J) hzt1
  · exact h

theorem map_spinJ₃ (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) : (spinJ₃ K).map (MulAut.conj i).toMonoidHom = spinJ₂ K := by
  obtain ⟨-, -, -, -, ht1, -, -, ht2J, hzt3J, -⟩ := spinZ_facts hp hp2 hK
  have hmem : tSeven K ∈ (spinJ₃ K).map (MulAut.conj i).toMonoidHom :=
    ⟨spinZ K * tSeven K, hzt3J, hI.conj_zt hp hp2 hK⟩
  rcases map_conj_spinJ_of_normalizes hp hp2 hK h5
    (fun x hx => hI.conj_mem_centralizer_t hp hp2 hK hx) (Or.inr (Or.inr rfl)) with h | h | h
  · rw [h] at hmem
    exact absurd (eq_one_of_mem_spinJ₁_of_mem_spinJ₂ hp hp2 hK h5 hmem ht2J) ht1
  · exact h
  · rw [h] at hmem
    exact absurd (eq_one_of_mem_spinJ₂_of_mem_spinJ₃ hp hp2 hK h5 ht2J hmem) ht1

theorem conj_mem_spinJ₃ (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {b : spinGroup (quadOdd 3 K)}
    (hb : b ∈ spinJ₂ K) : i * b * i⁻¹ ∈ spinJ₃ K := by
  rw [← hI.map_spinJ₂ hp hp2 hK h5]
  exact ⟨b, hb, rfl⟩

theorem conj_mem_spinJ₂ (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {c : spinGroup (quadOdd 3 K)}
    (hc : c ∈ spinJ₃ K) : i * c * i⁻¹ ∈ spinJ₂ K := by
  rw [← hI.map_spinJ₃ hp hp2 hK h5]
  exact ⟨c, hc, rfl⟩

theorem conj_mem_sup (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) {x : spinGroup (quadOdd 3 K)} (hx : x ∈ spinJ₂ K ⊔ spinJ₃ K) :
    i * x * i⁻¹ ∈ spinJ₂ K ⊔ spinJ₃ K := by
  have h : (spinJ₂ K ⊔ spinJ₃ K).map (MulAut.conj i).toMonoidHom = spinJ₂ K ⊔ spinJ₃ K := by
    rw [Subgroup.map_sup, hI.map_spinJ₂ hp hp2 hK h5, hI.map_spinJ₃ hp hp2 hK h5, sup_comm]
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem eq_of_mem_spinJ₃_of_mul_self (hA4 : A4) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {x : spinGroup (quadOdd 3 K)}
    (hx : x ∈ spinJ₃ K) (hxx : x * x = 1) : x = 1 ∨ x = spinZ K * tSeven K := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : i * x * i⁻¹ * (i * x * i⁻¹) = 1 := by
    calc i * x * i⁻¹ * (i * x * i⁻¹) = i * (x * x) * i⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  rcases (hA4 K hodd).1 _ (hI.conj_mem_spinJ₂ hp hp2 hK h5 hx) h2 with h | h
  · left
    calc x = i⁻¹ * (i * x * i⁻¹) * i := by group
      _ = 1 := by rw [h]; group
  · right
    calc x = i * (i * x * i⁻¹) * i⁻¹ := (hI.conj_conj x).symm
      _ = spinZ K * tSeven K := by rw [h, hI.conj_t]

theorem commute_of_mem_spinJ₃ (hA3 : A3) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {x : spinGroup (quadOdd 3 K)}
    (hx : x ∈ spinJ₃ K) (hx1 : x ≠ 1) (hxp : x ^ p = 1) {a b : spinGroup (quadOdd 3 K)}
    (ha : a ∈ spinJ₃ K) (hb : b ∈ spinJ₃ K) (hax : a * x = x * a) (hbx : b * x = x * b) :
    a * b = b * a := by
  have hx1' : i * x * i⁻¹ ≠ 1 := fun h => hx1 (by
    calc x = i⁻¹ * (i * x * i⁻¹) * i := by group
      _ = 1 := by rw [h]; group)
  have hxp' : (i * x * i⁻¹) ^ p = 1 := by
    rw [← MulAut.conj_apply, ← map_pow, hxp, map_one]
  have h := commute_of_mem_spinJ₂ hA3 hp hp2 hK (hI.conj_mem_spinJ₂ hp hp2 hK h5 hx) hx1' hxp'
    (hI.conj_mem_spinJ₂ hp hp2 hK h5 ha) (hI.conj_mem_spinJ₂ hp hp2 hK h5 hb)
    (conj_mul_conj_comm i hax) (conj_mul_conj_comm i hbx)
  apply (MulAut.conj i).injective
  simp only [MulAut.conj_apply]
  calc i * (a * b) * i⁻¹ = i * a * i⁻¹ * (i * b * i⁻¹) := by group
    _ = i * b * i⁻¹ * (i * a * i⁻¹) := h
    _ = i * (b * a) * i⁻¹ := by group

theorem commute_conj (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) (b b' : ↥(spinJ₂ K)) :
    Commute (b : spinGroup (quadOdd 3 K)) (i * b' * i⁻¹) :=
  commute_spinJ₂_spinJ₃ (four_le_card_spin hK h5) b.2 (hI.conj_mem_spinJ₃ hp hp2 hK h5 b'.2)

@[expose] def diag (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) : ↥(spinJ₂ K) →* spinGroup (quadOdd 3 K) :=
  (MonoidHom.noncommCoprod (spinJ₂ K).subtype
    ((MulAut.conj i).toMonoidHom.comp (spinJ₂ K).subtype)
    (hI.commute_conj hp hp2 hK h5)).comp ((MonoidHom.id _).prod (MonoidHom.id _))

theorem diag_apply (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) (b : ↥(spinJ₂ K)) : hI.diag hp hp2 hK h5 b = b * (i * b * i⁻¹) := rfl

abbrev dTwoThree (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) : Subgroup (spinGroup (quadOdd 3 K)) :=
  (hI.diag hp hp2 hK h5).range

theorem injective_diag (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) : Function.Injective (hI.diag hp hp2 hK h5) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  rw [diag_apply] at hb
  have h3 : (b : spinGroup (quadOdd 3 K)) ∈ spinJ₃ K := by
    rw [eq_inv_of_mul_eq_one_left hb]
    exact inv_mem (hI.conj_mem_spinJ₃ hp hp2 hK h5 b.2)
  exact Subtype.ext (eq_one_of_mem_spinJ₂_of_mem_spinJ₃ hp hp2 hK h5 b.2 h3)

theorem card_dTwoThree (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) : Nat.card ↥(hI.dTwoThree hp hp2 hK h5) = Nat.card ↥(spinJ₂ K) :=
  (Nat.card_congr (MonoidHom.ofInjective (hI.injective_diag hp hp2 hK h5)).toEquiv).symm

theorem dTwoThree_le_sup (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    hI.dTwoThree hp hp2 hK h5 ≤ spinJ₂ K ⊔ spinJ₃ K := by
  rintro _ ⟨b, rfl⟩
  rw [diag_apply]
  exact mul_mem (mem_sup_left b.2) (mem_sup_right (hI.conj_mem_spinJ₃ hp hp2 hK h5 b.2))

theorem dTwoThree_le_centralizer_i (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    hI.dTwoThree hp hp2 hK h5 ≤ centralizer ({i} : Set (spinGroup (quadOdd 3 K))) := by
  rintro _ ⟨b, rfl⟩
  rw [mem_centralizer_singleton_iff, diag_apply]
  have hc : (b : spinGroup (quadOdd 3 K)) * (i * b * i⁻¹) = (i * b * i⁻¹) * b :=
    hI.commute_conj hp hp2 hK h5 b b
  calc (b : spinGroup (quadOdd 3 K)) * (i * b * i⁻¹) * i = (i * b * i⁻¹) * b * i := by rw [hc]
    _ = i * (b * (i * b * i⁻¹)) := by
        rw [hI.inv_eq]
        simp only [mul_assoc]

theorem spinZ_mem_dTwoThree (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) : spinZ K ∈ hI.dTwoThree hp hp2 hK h5 := by
  obtain ⟨-, -, hzc, htt, -, -, -, ht2J, -⟩ := spinZ_facts hp hp2 hK
  refine ⟨⟨tSeven K, ht2J⟩, ?_⟩
  rw [diag_apply]
  show tSeven K * (i * tSeven K * i⁻¹) = spinZ K
  rw [hI.conj_t, ← mul_assoc, mem_center_iff.mp hzc (tSeven K), mul_assoc, htt, mul_one]

theorem isPerfect_dTwoThree (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    Group.IsPerfect ↥(hI.dTwoThree hp hp2 hK h5) := by
  have : Group.IsPerfect ↥(spinJ₂ K) :=
    (spinJ_props hp hp2 hK h5 (Or.inr (Or.inl rfl))).2.2.2.2.1
  exact Group.IsPerfect.range (hI.diag hp hp2 hK h5)

theorem mul_mem_of_not_commute (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {w : spinGroup (quadOdd 3 K)} (hw : w ∈ mX K)
    (hwt : w * tSeven K ≠ tSeven K * w) :
    w * i ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) := by
  obtain ⟨hzz, -, hzc, -⟩ := spinZ_facts hp hp2 hK
  obtain ⟨hwq, hwN⟩ := mem_inf.mp hw
  have hwz : w * tSeven K * w⁻¹ = spinZ K * tSeven K := by
    rcases conj_t_of_mem_normalizer_fourT hp hp2 hK hwN with h | h
    · exact absurd (commute_of_conj_eq h) hwt
    · exact h
  have hwz' : w * spinZ K * w⁻¹ = spinZ K := by
    rw [mem_center_iff.mp hzc w, mul_inv_cancel_right]
  have hconj : (w * i) * tSeven K * (w * i)⁻¹ = tSeven K := by
    calc (w * i) * tSeven K * (w * i)⁻¹ = w * (i * tSeven K * i⁻¹) * w⁻¹ := by group
      _ = (w * spinZ K * w⁻¹) * (w * tSeven K * w⁻¹) := by rw [hI.conj_t]; group
      _ = tSeven K := by rw [hwz', hwz, ← mul_assoc, hzz, one_mul]
  exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (commute_of_conj_eq hconj),
    mul_mem hwq hI.mem_centralizer_qThree⟩

theorem mem_normalizer_centralizer_inf (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    i ∈ normalizer ((centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) :
        Subgroup (spinGroup (quadOdd 3 K))) : Set (spinGroup (quadOdd 3 K))) :=
  mem_normalizer_of_involution hI.mul_self fun _ hx =>
    mem_inf.mpr ⟨hI.conj_mem_centralizer_t hp hp2 hK (mem_inf.mp hx).1,
      hI.conj_mem_centralizer_qThree (mem_inf.mp hx).2⟩

theorem centralizer_inf_inf_zpowers (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) ⊓ zpowers i = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hI.mul_self hx2 with h | h
  · exact (mem_bot).mpr h
  · exact absurd (h ▸ (mem_inf.mp hx1).1) (hI.not_mem_centralizer_t hp hp2 hK)

theorem mX_eq (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    mX K = (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) ⊔ zpowers i := by
  apply le_antisymm
  · intro w hw
    by_cases hwt : w * tSeven K = tSeven K * w
    · exact mem_sup_left (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hwt, (mem_inf.mp hw).1⟩)
    · have h := hI.mul_mem_of_not_commute hp hp2 hK hw hwt
      have e : w = (w * i) * i⁻¹ := by group
      rw [e]
      exact mul_mem (mem_sup_left h) (inv_mem (mem_sup_right (mem_zpowers i)))
  · exact sup_le (centralizer_inf_le_mX hp hp2 hK) (zpowers_le.mpr (hI.mem_mX hp hp2 hK))

theorem card_mX (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    Nat.card ↥(mX K) = Nat.card ↥(centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) * 2 := by
  have h := card_sup_mul_card_inf_of_le_normalizer'
    (zpowers_le.mpr (hI.mem_normalizer_centralizer_inf hp hp2 hK))
  rw [hI.centralizer_inf_inf_zpowers hp hp2 hK, card_bot, mul_one, Nat.card_zpowers,
    hI.orderOf_eq hp hp2 hK] at h
  rw [hI.mX_eq hp hp2 hK, h]

theorem card_M (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) : 2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ≤
      Nat.card ↥(mX K ⊓ centralizer ({i} : Set (spinGroup (quadOdd 3 K)))) := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hDS := hI.dTwoThree_le_sup hp hp2 hK h5
  have hUD : Nat.card ↥(uThree K ⊔ hI.dTwoThree hp hp2 hK h5) =
      Nat.card K * Nat.card ↥(spinJ₂ K) := by
    rw [card_sup_of_commute (fun u hu d hd => commute_spinJ₁_sup (uThree_le_spinJ₁ hu) (hDS hd)),
      card_uThree, hI.card_dTwoThree hp hp2 hK h5]
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxu, hxd⟩ := mem_inf.mp hx
    have h := mem_inf.mpr ⟨hDS hxd, hxu⟩
    rwa [sup_inf_uThree hp hp2 hK h5] at h
  have hUDi : uThree K ⊔ hI.dTwoThree hp hp2 hK h5 ≤
      centralizer ({i} : Set (spinGroup (quadOdd 3 K))) :=
    sup_le (fun u hu => mem_centralizer_singleton_iff.mpr (hI.commute_J₁ u
      (uThree_le_spinJ₁ hu)).symm) (hI.dTwoThree_le_centralizer_i hp hp2 hK h5)
  have hUDt : uThree K ⊔ hI.dTwoThree hp hp2 hK h5 ≤
      centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
        centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) :=
    sup_le (uThree_le_centralizer_inf hp hp2 hK) (hDS.trans (sup_le_centralizer_inf hp hp2 hK))
  have hQ : Nat.card ↥((uThree K ⊔ hI.dTwoThree hp hp2 hK h5) ⊔ zpowers i) =
      Nat.card K * Nat.card ↥(spinJ₂ K) * 2 := by
    rw [card_sup_of_commute, hUD, Nat.card_zpowers, hI.orderOf_eq hp hp2 hK]
    · intro a ha y hy
      have hya : y ∈ centralizer ({a} : Set (spinGroup (quadOdd 3 K))) :=
        zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp (hUDi ha)).symm) hy
      exact (mem_centralizer_singleton_iff.mp hya).symm
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
      rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hI.mul_self hx2 with h | h
      · exact (mem_bot).mpr h
      · exact absurd (h ▸ (mem_inf.mp (hUDt hx1)).1) (hI.not_mem_centralizer_t hp hp2 hK)
  have hle : (uThree K ⊔ hI.dTwoThree hp hp2 hK h5) ⊔ zpowers i ≤
      mX K ⊓ centralizer ({i} : Set (spinGroup (quadOdd 3 K))) :=
    sup_le (le_inf (hUDt.trans (centralizer_inf_le_mX hp hp2 hK)) hUDi)
      (zpowers_le.mpr (mem_inf.mpr ⟨hI.mem_mX hp hp2 hK,
        mem_centralizer_singleton_iff.mpr rfl⟩))
  calc 2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) =
      Nat.card K * Nat.card ↥(spinJ₂ K) * 2 := by rw [card_spinJ₂]; ring
    _ = Nat.card ↥((uThree K ⊔ hI.dTwoThree hp hp2 hK h5) ⊔ zpowers i) := hQ.symm
    _ ≤ _ := card_le_of_le hle

theorem conj_M (hA2 : A2) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {w : spinGroup (quadOdd 3 K)} (hw : w ∈ mX K)
    (hww : w * w = 1) (hwt : w * tSeven K ≠ tSeven K * w) : ∃ m ∈ mX K, m * i * m⁻¹ = w := by
  have h4 := four_le_card_spin hK h5
  have hc := hI.mul_mem_of_not_commute hp hp2 hK hw hwt
  rw [centralizer_inf_eq hA2 hp hp2 hK h5] at hc
  obtain ⟨x, hx, u, hu, hxu⟩ := exists_mul_of_mem_sup
    (fun x hx u hu => (commute_spinJ₁_sup (uThree_le_spinJ₁ hu) hx).symm) hc
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hinv : i * (w * i) * i⁻¹ = (w * i)⁻¹ := by
    rw [mul_inv_rev, hwinv]
    calc i * (w * i) * i⁻¹ = i * w := by group
      _ = i⁻¹ * w := by rw [hI.inv_eq]
  rw [hxu] at hinv
  have hiu : i * u * i⁻¹ = u := by
    rw [hI.commute_J₁ u (uThree_le_spinJ₁ hu), mul_inv_cancel_right]
  have hxu' : x * u = u * x := (commute_spinJ₁_sup (uThree_le_spinJ₁ hu) hx).symm
  have hx'S : i * x * i⁻¹ ∈ spinJ₂ K ⊔ spinJ₃ K := hI.conj_mem_sup hp hp2 hK h5 hx
  have e1 : (i * x * i⁻¹) * u = x⁻¹ * u⁻¹ := by
    calc (i * x * i⁻¹) * u = (i * x * i⁻¹) * (i * u * i⁻¹) := by rw [hiu]
      _ = i * (x * u) * i⁻¹ := by group
      _ = (x * u)⁻¹ := hinv
      _ = x⁻¹ * u⁻¹ := by rw [hxu', mul_inv_rev]
  have e2 : u * u = (i * x * i⁻¹)⁻¹ * x⁻¹ := by
    calc u * u = (i * x * i⁻¹)⁻¹ * ((i * x * i⁻¹) * u) * u := by group
      _ = (i * x * i⁻¹)⁻¹ * (x⁻¹ * u⁻¹) * u := by rw [e1]
      _ = (i * x * i⁻¹)⁻¹ * x⁻¹ := by group
  have huu : u * u = 1 := by
    have h1 : u * u ∈ (spinJ₂ K ⊔ spinJ₃ K) ⊓ uThree K := by
      refine mem_inf.mpr ⟨?_, mul_mem hu hu⟩
      rw [e2]
      exact mul_mem (inv_mem hx'S) (inv_mem hx)
    rw [sup_inf_uThree hp hp2 hK h5] at h1
    exact (mem_bot).mp h1
  have hu1 : u = 1 := eq_one_of_mem_uThree_of_mul_self hp hp2 hK hu huu
  subst hu1
  obtain ⟨b, hb, d, hd, rfl⟩ := exists_mul_of_mem_sup (commute_spinJ₂_spinJ₃' hK h5) hx
  have hbd3 : i * b * i⁻¹ ∈ spinJ₃ K := hI.conj_mem_spinJ₃ hp hp2 hK h5 hb
  have hdb2 : i * d * i⁻¹ ∈ spinJ₂ K := hI.conj_mem_spinJ₂ hp hp2 hK h5 hd
  have e3 : (i * d * i⁻¹) * (i * b * i⁻¹) = b⁻¹ * d⁻¹ := by
    calc (i * d * i⁻¹) * (i * b * i⁻¹) = (i * b * i⁻¹) * (i * d * i⁻¹) :=
          commute_spinJ₂_spinJ₃ h4 hdb2 hbd3
      _ = i * (b * d) * i⁻¹ * 1 := by group
      _ = (b * d)⁻¹ * 1⁻¹ := e1
      _ = d⁻¹ * b⁻¹ := by rw [inv_one, mul_one, mul_inv_rev]
      _ = b⁻¹ * d⁻¹ := (commute_spinJ₂_spinJ₃ h4 (inv_mem hb) (inv_mem hd)).symm
  obtain ⟨-, h3⟩ := eq_of_mul_eq_mul_J₂J₃ hp hp2 hK h5 hdb2 (inv_mem hb) hbd3 (inv_mem hd) e3
  refine ⟨b, centralizer_inf_le_mX hp hp2 hK (spinJ₂_le_centralizer_inf hp hp2 hK hb), ?_⟩
  have hd' : d = (i * b * i⁻¹)⁻¹ := by rw [h3, inv_inv]
  have hw' : w = b * d * i⁻¹ := by
    calc w = w * i * i⁻¹ := by group
      _ = b * d * 1 * i⁻¹ := by rw [hxu]
      _ = b * d * i⁻¹ := by rw [mul_one]
  rw [hw', hd']
  calc b * i * b⁻¹ = b * (i * b * i⁻¹)⁻¹ * i⁻¹ * (i * i) := by group
    _ = b * (i * b * i⁻¹)⁻¹ * i⁻¹ := by rw [hI.mul_self, mul_one]

end IsIBar

end CFSG.ComponentClassification.HarrisLit.T1.S74
