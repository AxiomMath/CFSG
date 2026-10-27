module

public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Frame
public import CFSG.ClassicalInvolution.Models.LinearPairs.Pairs

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.WeakCT Module
open scoped MatrixGroups

section Standard

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

@[expose] noncomputable def negOneSU : Su K p f 2 :=
  ⟨-1, by
    refine ⟨?_, ?_⟩
    · simp [Matrix.det_neg]
    · ext a b
      fin_cases a <;> fin_cases b <;> simp [conjTr]⟩

theorem suMat_negOneSU : suMat (negOneSU K p f) = -1 := by
  simp [negOneSU, suMat]

@[expose] noncomputable def rootSU2 {n : ℕ} (hn : 2 ≤ n) : Subgroup (Su K p f n) :=
  (blockEmb K p f n 2 0 (by omega)).range

@[expose] noncomputable def rootInvSU {n : ℕ} (hn : 2 ≤ n) : Su K p f n :=
  blockEmb K p f n 2 0 (by omega) (negOneSU K p f)

variable {K p f}

theorem suMat_blockEmb {m k i : ℕ} (h : i + k ≤ m) (A : Su K p f k) :
    suMat (blockEmb K p f m k i h A) = blockMat m i (suMat A) :=
  rfl

theorem suMat_rootInvSU {n : ℕ} (hn : 2 ≤ n) : suMat (rootInvSU K p f hn) = negBlock K n 0 := by
  rw [rootInvSU, suMat_blockEmb, suMat_negOneSU, negBlock]

theorem rootInvSU_mem_rootSU2 {n : ℕ} (hn : 2 ≤ n) : rootInvSU K p f hn ∈ rootSU2 K p f hn :=
  ⟨negOneSU K p f, rfl⟩

theorem negOneSU_mul_self : negOneSU K p f * negOneSU K p f = 1 :=
  suMat_injective (by simp [suMat_negOneSU])

theorem negOneSU_comm (A : Su K p f 2) : A * negOneSU K p f = negOneSU K p f * A :=
  suMat_injective (by simp [suMat_negOneSU])

theorem negOneSU_ne_one (h2 : (2 : K) ≠ 0) : negOneSU K p f ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg suMat h) 0) 0
  rw [suMat_negOneSU, suMat_one] at this
  exact neg_one_ne_one_of_two_ne_zero h2 (by simpa using this)

theorem orderOf_negOneSU (h2 : (2 : K) ≠ 0) : orderOf (negOneSU K p f) = 2 :=
  orderOf_eq_prime (by rw [pow_two, negOneSU_mul_self]) (negOneSU_ne_one h2)

end Standard

section LongRootGroup

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p] {n : ℕ}

@[expose] noncomputable def longRootGroupSU (I : Matrix (Fin n) (Fin n) K) :
    Subgroup (Su K p f n) :=
  (longRootGroup I).comap (suToSL (unitaryInvolution K p f) n)

variable {K p f}

theorem mem_longRootGroupSU {I : Matrix (Fin n) (Fin n) K} {x : Su K p f n} :
    x ∈ longRootGroupSU K p f I ↔ suMat x * I = I * suMat x ∧ suMat x * (1 + I) = 1 + I :=
  Iff.rfl

theorem suToSL_blockEmb {m k i : ℕ} (h : i + k ≤ m) (A : Su K p f k) :
    suToSL (unitaryInvolution K p f) m (blockEmb K p f m k i h A) =
      blockSL K m k i h (suToSL (unitaryInvolution K p f) k A) :=
  rfl

theorem blockEmb_mem_longRootGroupSU {j : ℕ} (hj : j + 2 ≤ n) (A : Su K p f 2) :
    blockEmb K p f n 2 j hj A ∈ longRootGroupSU K p f (negBlock K n j) :=
  blockSL_mem_longRootGroup (K := K) hj (suToSL (unitaryInvolution K p f) 2 A)

theorem exists_blockEmb_of_mem_longRootGroupSU (h2 : (2 : K) ≠ 0) {j : ℕ} (hj : j + 2 ≤ n)
    {x : Su K p f n} (hx : x ∈ longRootGroupSU K p f (negBlock K n j)) :
    ∃ A : Su K p f 2, blockEmb K p f n 2 j hj A = x := by
  obtain ⟨A, hA⟩ := exists_blockSL_of_mem_longRootGroup h2 hj hx
  have hAm : blockMat n j (A : Matrix (Fin 2) (Fin 2) K) = suMat x :=
    congrArg (fun z : SL(n, K) => (z : Matrix (Fin n) (Fin n) K)) hA
  have hAu : conjTr (unitaryInvolution K p f) (A : Matrix (Fin 2) (Fin 2) K) *
      (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have hx1 : conjTr (unitaryInvolution K p f) (suMat x) * suMat x = 1 := x.2.2
    rw [← hAm, conjTr_blockMat, ← blockMat_mul hj] at hx1
    exact blockMat_injective hj (by rw [hx1, blockMat_one])
  refine ⟨⟨Matrix.SpecialLinearGroup.toGL A, ⟨by simp, by simpa using hAu⟩⟩, ?_⟩
  exact suMat_injective (by rw [suMat_blockEmb]; simpa [suMat] using hAm)

theorem range_blockEmb_eq_longRootGroupSU (h2 : (2 : K) ≠ 0) {j : ℕ} (hj : j + 2 ≤ n) :
    (blockEmb K p f n 2 j hj).range = longRootGroupSU K p f (negBlock K n j) := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    exact blockEmb_mem_longRootGroupSU hj A
  · intro hx
    obtain ⟨A, hA⟩ := exists_blockEmb_of_mem_longRootGroupSU h2 hj hx
    exact ⟨A, hA⟩

theorem rootSU2_eq_longRootGroupSU (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) :
    rootSU2 K p f hn = longRootGroupSU K p f (negBlock K n 0) :=
  range_blockEmb_eq_longRootGroupSU h2 (by omega)

end LongRootGroup

section Conjugation

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem mem_map_conj_iff_of_group {G : Type*} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem conj_mem_longRootGroupSU_conj {I : Matrix (Fin n) (Fin n) K} (g : Su K p f n)
    {x : Su K p f n} (hx : x ∈ longRootGroupSU K p f I) :
    g * x * g⁻¹ ∈ longRootGroupSU K p f (suMat g * I * suMat g⁻¹) := by
  obtain ⟨h1, h3⟩ := hx
  exact mem_longRootGroup_conj_aux (suMat_mul_suMat_inv g) (suMat_inv_mul_suMat g) h1 h3

theorem longRootGroupSU_conj (I : Matrix (Fin n) (Fin n) K) (g : Su K p f n) :
    longRootGroupSU K p f (suMat g * I * suMat g⁻¹) =
      (longRootGroupSU K p f I).map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [mem_map_conj_iff_of_group]
  constructor
  · intro hy
    have h := conj_mem_longRootGroupSU_conj g⁻¹ hy
    have e : suMat g⁻¹ * (suMat g * I * suMat g⁻¹) * suMat (g⁻¹)⁻¹ = I := by
      rw [inv_inv]
      calc _ = (suMat g⁻¹ * suMat g) * I * (suMat g⁻¹ * suMat g) := by
            simp only [Matrix.mul_assoc]
        _ = I := by rw [suMat_inv_mul_suMat, Matrix.one_mul, Matrix.mul_one]
    rw [e] at h
    exact h
  · intro hy
    have h := conj_mem_longRootGroupSU_conj g hy
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at h

theorem longRootGroupSU_eq_map_conj_of_mul_eq {I D : Matrix (Fin n) (Fin n) K} (P : Su K p f n)
    (h : I * suMat P = suMat P * D) :
    longRootGroupSU K p f I = (longRootGroupSU K p f D).map (MulAut.conj P).toMonoidHom := by
  have e : I = suMat P * D * suMat P⁻¹ := by
    rw [← h, Matrix.mul_assoc, suMat_mul_suMat_inv, Matrix.mul_one]
  rw [e]
  exact longRootGroupSU_conj D P

theorem conj_mem_longRootGroupSU_of_commute {I : Matrix (Fin n) (Fin n) K} {c x : Su K p f n}
    (hc : suMat c * I = I * suMat c) (hx : x ∈ longRootGroupSU K p f I) :
    c * x * c⁻¹ ∈ longRootGroupSU K p f I := by
  have h := conj_mem_longRootGroupSU_conj c hx
  have e : suMat c * I * suMat c⁻¹ = I := by
    rw [hc, Matrix.mul_assoc, suMat_mul_suMat_inv, Matrix.mul_one]
  rwa [e] at h

end Conjugation

section LongRoot

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p] {n : ℕ}

@[expose] noncomputable def IsLongRootSU2 (hn : 2 ≤ n) (L : Subgroup (Su K p f n))
    (i : Su K p f n) : Prop :=
  ∃ g : Su K p f n, L = (rootSU2 K p f hn).map (MulAut.conj g).toMonoidHom ∧
    i = g * rootInvSU K p f hn * g⁻¹

variable {K p f}

theorem isLongRootSU2_standard (hn : 2 ≤ n) :
    IsLongRootSU2 K p f hn (rootSU2 K p f hn) (rootInvSU K p f hn) :=
  ⟨1, by ext x; simp, by simp⟩

theorem IsLongRootSU2.conj {hn : 2 ≤ n} {L : Subgroup (Su K p f n)} {i : Su K p f n}
    (h : IsLongRootSU2 K p f hn L i) (g : Su K p f n) :
    IsLongRootSU2 K p f hn (L.map (MulAut.conj g).toMonoidHom) (g * i * g⁻¹) := by
  obtain ⟨g₀, rfl, rfl⟩ := h
  refine ⟨g * g₀, ?_, by group⟩
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem IsLongRootSU2.eq_longRootGroupSU (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n}
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) :
    L = longRootGroupSU K p f (suMat i) := by
  obtain ⟨g, rfl, rfl⟩ := h
  rw [rootSU2_eq_longRootGroupSU h2 hn, ← longRootGroupSU_conj]
  simp only [suMat_mul, suMat_rootInvSU]

theorem IsLongRootSU2.mem_iff (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n}
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i)
    {x : Su K p f n} :
    x ∈ L ↔ suMat x * suMat i = suMat i * suMat x ∧ suMat x * (1 + suMat i) = 1 + suMat i := by
  rw [h.eq_longRootGroupSU h2]
  exact mem_longRootGroupSU

theorem IsLongRootSU2.mem {hn : 2 ≤ n} {L : Subgroup (Su K p f n)} {i : Su K p f n}
    (h : IsLongRootSU2 K p f hn L i) : i ∈ L := by
  obtain ⟨g, rfl, rfl⟩ := h
  exact Subgroup.mem_map.mpr ⟨_, rootInvSU_mem_rootSU2 hn, rfl⟩

theorem IsLongRootSU2.mul_self {hn : 2 ≤ n} {L : Subgroup (Su K p f n)} {i : Su K p f n}
    (h : IsLongRootSU2 K p f hn L i) : i * i = 1 := by
  obtain ⟨g, rfl, rfl⟩ := h
  have : rootInvSU K p f hn * rootInvSU K p f hn = 1 := by
    rw [rootInvSU, ← map_mul, negOneSU_mul_self, map_one]
  calc g * rootInvSU K p f hn * g⁻¹ * (g * rootInvSU K p f hn * g⁻¹)
      = g * (rootInvSU K p f hn * rootInvSU K p f hn) * g⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem IsLongRootSU2.coe_mul_self {hn : 2 ≤ n} {L : Subgroup (Su K p f n)} {i : Su K p f n}
    (h : IsLongRootSU2 K p f hn L i) : suMat i * suMat i = 1 := by
  rw [← suMat_mul, h.mul_self, suMat_one]

end LongRoot

section Classical

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

omit [Finite K] in
theorem two_ne_zero_of_charP_ne_two (hp : p ≠ 2) : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')

theorem prime_pow_ne_two_of_ne_two (hp : p ≠ 2) (f : ℕ) : p ^ f ≠ 2 := by
  intro h
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp at h
  · exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (h ▸ dvd_pow_self p hf.ne'))

theorem nonempty_sl2_mulEquiv_su_two (hK : Nat.card K = (p ^ f) ^ 2) :
    Nonempty (SL(2, fixedSubfield K p f) ≃* Su K p f 2) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 2
  exact ⟨(hypEquiv hζ0 hζ).trans (conjEquiv P hP)⟩

theorem odd_natCard_fixedSubfield (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) :
    Odd (Nat.card (fixedSubfield K p f)) := by
  rw [card_fixedSubfield hK]
  exact (Fact.out (p := p.Prime)).odd_of_ne_two hp |>.pow

theorem isClassicalSL2_rootSU2 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n) :
    IsClassicalSL2 (fixedSubfield K p f) (rootSU2 K p f hn) (rootInvSU K p f hn) where
  nonempty_mulEquiv := by
    obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su_two (K := K) (p := p) (f := f) hK
    exact ⟨(MonoidHom.ofInjective (blockEmb_injective (K := K) (p := p) (f := f)
      (m := n) (k := 2) (i := 0) (by omega))).symm.trans e.symm⟩
  mem := rootInvSU_mem_rootSU2 hn
  orderOf_eq_two := by
    rw [rootInvSU, orderOf_injective (blockEmb K p f n 2 0 (by omega)) (blockEmb_injective _)]
    exact orderOf_negOneSU (two_ne_zero_of_charP_ne_two hp)
  le_centralizer := by
    rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, rootInvSU, ← map_mul, ← map_mul, negOneSU_comm]
  centralizer_le_normalizer := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    have e : ∀ {c : Su K p f n},
        c ∈ Subgroup.centralizer ({rootInvSU K p f hn} : Set (Su K p f n)) →
          suMat c * negBlock K n 0 = negBlock K n 0 * suMat c := fun {c} hc => by
      have := congrArg suMat (Subgroup.mem_centralizer_singleton_iff.mp hc)
      simpa [suMat_rootInvSU] using this
    have e1 := e hc
    have e2 := e ((Subgroup.centralizer ({rootInvSU K p f hn} : Set (Su K p f n))).inv_mem hc)
    intro x
    rw [rootSU2_eq_longRootGroupSU (two_ne_zero_of_charP_ne_two hp) hn]
    constructor
    · exact fun hx => conj_mem_longRootGroupSU_of_commute e1 hx
    · intro hx
      have := conj_mem_longRootGroupSU_of_commute e2 hx
      have e3 : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
      rwa [e3] at this

theorem IsLongRootSU2.isClassicalSL2 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) :
    IsClassicalSL2 (fixedSubfield K p f) L i := by
  obtain ⟨g, rfl, rfl⟩ := h
  exact (isClassicalSL2_rootSU2 hK hp hn).conj g

theorem IsLongRootSU2.eq_of_orderOf_eq_two (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {hn : 2 ≤ n} {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i)
    {t : Su K p f n} (htL : t ∈ L) (ht : orderOf t = 2) : t = i :=
  (h.isClassicalSL2 hK hp).eq_of_orderOf_eq_two (odd_natCard_fixedSubfield hK hp) htL ht

theorem IsLongRootSU2.involution_unique (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    {L : Subgroup (Su K p f n)} {i i' : Su K p f n} (h : IsLongRootSU2 K p f hn L i)
    (h' : IsLongRootSU2 K p f hn L i') : i = i' :=
  (h.eq_of_orderOf_eq_two hK hp h'.mem ((h'.isClassicalSL2 hK hp).orderOf_eq_two)).symm

theorem IsLongRootSU2.normal_subgroupOf_centralizer (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {hn : 2 ≤ n} {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) :
    (L.subgroupOf (Subgroup.centralizer ({i} : Set (Su K p f n)))).Normal := by
  have hc := h.isClassicalSL2 hK hp
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hc.le_centralizer]
  exact hc.centralizer_le_normalizer

theorem IsLongRootSU2.normalizer_eq_centralizer (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {hn : 2 ≤ n} {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) :
    Subgroup.normalizer (L : Set (Su K p f n)) = Subgroup.centralizer ({i} : Set (Su K p f n)) := by
  have hc := h.isClassicalSL2 hK hp
  apply le_antisymm
  · intro c hc'
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmem : c * i * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hc' i).mp h.mem
    have hord : orderOf (c * i * c⁻¹) = 2 := by
      rw [← hc.orderOf_eq_two]
      exact MulEquiv.orderOf_eq (MulAut.conj c) i
    have hci := h.eq_of_orderOf_eq_two hK hp hmem hord
    calc c * i = c * i * c⁻¹ * c := by group
      _ = i * c := by rw [hci]
  · exact hc.centralizer_le_normalizer

end Classical

section Spaces

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

@[expose] noncomputable def minusSpaceSU (i : Su K p f n) : Submodule K (Fin n → K) :=
  eigSpace (suMat i) (-1)

@[expose] noncomputable def fixSpaceSU (i : Su K p f n) : Submodule K (Fin n → K) :=
  eigSpace (suMat i) 1

theorem mem_minusSpaceSU {i : Su K p f n} {v : Fin n → K} :
    v ∈ minusSpaceSU i ↔ suMat i *ᵥ v = -v :=
  mem_eigSpace_neg_one

theorem mem_fixSpaceSU {i : Su K p f n} {v : Fin n → K} :
    v ∈ fixSpaceSU i ↔ suMat i *ᵥ v = v :=
  mem_eigSpace_one

theorem IsLongRootSU2.finrank_minusSpaceSU (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n}
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) :
    finrank K (minusSpaceSU i) = 2 := by
  obtain ⟨g, -, rfl⟩ := h
  have e : suMat (g * rootInvSU K p f hn * g⁻¹) = suMat g * negBlock K n 0 * suMat g⁻¹ := by
    simp only [suMat_mul, suMat_rootInvSU]
  rw [minusSpaceSU, e, eigSpace_conj_aux (suMat_mul_suMat_inv g) (suMat_inv_mul_suMat g),
    finrank_map_toLin' (suMat_inv_mul_suMat g), finrank_eigSpace_negBlock h2 (by omega)]

end Spaces

end CFSG.ClassicalInvolution.Models
