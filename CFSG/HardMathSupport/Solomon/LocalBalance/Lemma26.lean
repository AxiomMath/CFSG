module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Statements2
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma26Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type*} [Group G] [Finite G]

set_option linter.unusedSectionVars false

@[expose] def bar (b : G) {y : G} (hy : y ∈ Subgroup.centralizer ({b} : Set G)) : CBar 3 b :=
  QuotientGroup.mk (⟨y, hy⟩ : ↥(Subgroup.centralizer ({b} : Set G)))

theorem mem_nb_iff {b n : G} :
    n ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ↔
      ∃ h : n ∈ Subgroup.centralizer ({b} : Set G), bar b h = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (QuotientGroup.eq_one_iff y).2 hy⟩
  · rintro ⟨h, h1⟩
    exact ⟨⟨n, h⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩

theorem nb_le_cb (b : G) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.centralizer ({b} : Set G) :=
  Subgroup.map_subtype_le _

theorem bar_mul (b : G) {y z : G} (hy : y ∈ Subgroup.centralizer ({b} : Set G))
    (hz : z ∈ Subgroup.centralizer ({b} : Set G)) :
    bar b hy * bar b hz = bar b (mul_mem hy hz) := rfl

theorem bar_inv (b : G) {y : G} (hy : y ∈ Subgroup.centralizer ({b} : Set G)) :
    (bar b hy)⁻¹ = bar b (inv_mem hy) := rfl

theorem bar_eq_iff {b y z : G} (hy : y ∈ Subgroup.centralizer ({b} : Set G))
    (hz : z ∈ Subgroup.centralizer ({b} : Set G)) :
    bar b hy = bar b hz ↔ y⁻¹ * z ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  unfold bar
  rw [QuotientGroup.eq]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨c, hc, hcz⟩
    have : c = (⟨y, hy⟩ : ↥(Subgroup.centralizer ({b} : Set G)))⁻¹ * ⟨z, hz⟩ :=
      Subtype.ext hcz
    rwa [← this]

theorem mem_barImageAt_iff {b : G} {Y : Subgroup G} {w : CBar 3 b} :
    w ∈ barImageAt 3 b Y ↔
      ∃ (y : G) (hy : y ∈ Subgroup.centralizer ({b} : Set G)), y ∈ Y ∧ bar b hy = w := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, c.2, (Subgroup.mem_subgroupOf).1 hc, rfl⟩
  · rintro ⟨y, hy, hyY, rfl⟩
    exact ⟨⟨y, hy⟩, (Subgroup.mem_subgroupOf).2 hyY, rfl⟩

theorem bar_exists (b : G) (w : CBar 3 b) :
    ∃ (y : G) (hy : y ∈ Subgroup.centralizer ({b} : Set G)), bar b hy = w := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective w
  exact ⟨c, c.2, rfl⟩

theorem coprime_orderOf_of_mem_nb {b n : G}
    (hn : n ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) :
    Nat.Coprime 3 (orderOf n) := by
  have hc := coprime_card_gLAPPrimeCore_aux 3 ↥(Subgroup.centralizer ({b} : Set G))
  have hcard : Nat.card (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) =
      Nat.card (GLAPPrimeCore 3 ↥(Subgroup.centralizer ({b} : Set G))) :=
    Subgroup.card_map_of_injective (Subgroup.centralizer ({b} : Set G)).subtype_injective
  rw [← hcard] at hc
  exact hc.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hn)

theorem nb_conj_mem {b c n : G} (hc : c ∈ Subgroup.centralizer ({b} : Set G))
    (hn : n ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) :
    c * n * c⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨hnC, hn1⟩ := mem_nb_iff.1 hn
  refine mem_nb_iff.2 ⟨mul_mem (mul_mem hc hnC) (inv_mem hc), ?_⟩
  rw [← bar_mul b (mul_mem hc hnC) (inv_mem hc), ← bar_mul b hc hnC, hn1, ← bar_inv b hc, mul_one,
    mul_inv_cancel]

theorem mem_zpowers_of_mul_eq {x j n : G} (hx3 : orderOf x = 3) (hjn : j * n = x)
    (hc : j * n = n * j) (hn : Nat.Coprime 3 (orderOf n)) : x ∈ Subgroup.zpowers j := by
  set m := orderOf n with hm
  have hcomm : Commute j n := hc
  have hxm : x ^ m = j ^ m := by
    rw [← hjn, hcomm.mul_pow, hm, pow_orderOf_eq_one, mul_one]
  have hm3 : ¬ 3 ∣ m := fun h => by
    have := Nat.Coprime.eq_one_of_dvd hn h
    omega
  have hmm : (m * m) % 3 = 1 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  have hx : x ^ (m * m) = x := by
    rw [← pow_mod_orderOf, hx3, hmm, pow_one]
  have hxj : x = j ^ (m * m) := by
    calc x = x ^ (m * m) := hx.symm
      _ = (x ^ m) ^ m := pow_mul x m m
      _ = (j ^ m) ^ m := by rw [hxm]
      _ = j ^ (m * m) := (pow_mul j m m).symm
  rw [hxj]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers j) _


private theorem wp1_two_eq_zero {K : Type} [Field K] [Finite K] (h : 2 ∣ Nat.card K) :
    (2 : K) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := K) 2 h
  have h2 : (2 : ℕ) • x = 0 := hx ▸ addOrderOf_nsmul_eq_zero x
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, addOrderOf_zero] at hx
    omega
  rw [nsmul_eq_mul] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · simpa using h
  · exact absurd h hx0

private def wp1Scal {K : Type} [Field K] (l : Kˣ) : GL (Fin 3) K :=
  Units.map (Matrix.scalar (Fin 3) : K →+* Matrix (Fin 3) (Fin 3) K).toMonoidHom l

private theorem wp1Scal_coe {K : Type} [Field K] (l : Kˣ) :
    ((wp1Scal l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (l : K) := rfl

private theorem wp1Scal_comm {K : Type} [Field K] (l : Kˣ) (w : GL (Fin 3) K) :
    w * wp1Scal l = wp1Scal l * w := by
  apply Units.ext
  simp only [Units.val_mul, wp1Scal_coe]
  exact ((Matrix.scalar_commute (l : K) (fun r' => Commute.all _ _) (w : Matrix (Fin 3) (Fin 3) K)).symm)

private theorem wp1Scal_ne_one {K : Type} [Field K] (l : Kˣ) (hl : l ≠ 1) : wp1Scal l ≠ 1 := by
  intro h
  apply hl
  have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp [wp1Scal_coe] at h2
  exact h2

private theorem wp1Scal_det {K : Type} [Field K] (l : Kˣ) (hl : l ^ 3 = 1) :
    ((wp1Scal l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [wp1Scal_coe, Matrix.scalar_apply, Matrix.det_diagonal]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have := congrArg (fun u : Kˣ => (u : K)) hl
  simpa using this

private theorem wp1_central_transport {X : Type*} [Group X] {K : Type} [Field K]
    {S : Subgroup (GL (Fin 3) K)} (e : X ≃* ↥S) (g : GL (Fin 3) K) (hg : g ∈ S) (hg1 : g ≠ 1)
    (hc : ∀ w : GL (Fin 3) K, w * g = g * w) :
    ∃ z : X, z ≠ 1 ∧ ∀ w : X, w * z = z * w := by
  refine ⟨e.symm ⟨g, hg⟩, ?_, ?_⟩
  · intro h
    apply hg1
    have := congrArg (fun x => ((e x : ↥S) : GL (Fin 3) K)) h
    simpa using this
  · intro w
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hc _

theorem exists_central_ne_one_of_exc {X : Type*} [Group X]
    (h : IsSLThreeExc X ∨ IsSUThreeExc X) : ∃ z : X, z ≠ 1 ∧ ∀ w : X, w * z = z * w := by
  rcases h with ⟨K, _, hfin, hK, ⟨e⟩⟩ | ⟨K, _, hfin, q, hq, hq9, ⟨e⟩⟩
  · have hpos : 0 < Nat.card K := Nat.card_pos
    have h3 : 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_units]; omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
    have hl1 : l ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at hl; omega
    have hl3 : l ^ 3 = 1 := hl ▸ pow_orderOf_eq_one l
    refine wp1_central_transport e (wp1Scal l) ?_ (wp1Scal_ne_one l hl1) (wp1Scal_comm l)
    exact Subgroup.subset_closure (wp1Scal_det l hl3)
  · have hpos : 0 < Nat.card K := Nat.card_pos
    have hq3 : q % 3 = 2 := by omega
    have hq2 : q ^ 2 % 3 = 1 := by simp [pow_two, Nat.mul_mod, hq3]
    have h3 : 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_units]; omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
    have hl1 : l ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at hl; omega
    have hl3 : l ^ 3 = 1 := hl ▸ pow_orderOf_eq_one l
    have hlq : l ^ (q + 1) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hl]; omega
    have hq0 : q ≠ 0 := by omega
    refine wp1_central_transport e (wp1Scal l) ?_ (wp1Scal_ne_one l hl1) (wp1Scal_comm l)
    refine Subgroup.subset_closure ⟨wp1Scal_det l hl3, ?_⟩
    have hm : ((wp1Scal l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map (· ^ q) =
        Matrix.scalar (Fin 3) ((l : K) ^ q) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [wp1Scal_coe, Matrix.scalar_apply]
      · simp [wp1Scal_coe, Matrix.scalar_apply, hij, zero_pow hq0]
    rw [hm, wp1Scal_coe]
    have ht : Matrix.transpose (Matrix.scalar (Fin 3) ((l : K) ^ q)) = Matrix.scalar (Fin 3) ((l : K) ^ q) := by
      simp [Matrix.scalar_apply]
    rw [ht, ← map_mul, ← pow_succ]
    have := congrArg (fun u : Kˣ => (u : K)) hlq
    simp at this
    rw [this]; simp

private def wp1T1 (K : Type) [Field K] : GL (Fin 2) K :=
  ⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private def wp1T2 (K : Type) [Field K] : GL (Fin 2) K :=
  ⟨!![1, 0; 1, 1], !![1, 0; -1, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private theorem wp1T1_mem (K : Type) [Field K] : wp1T1 K ∈ StatedSL 2 K :=
  Subgroup.subset_closure (by simp [wp1T1, Matrix.det_fin_two])

private theorem wp1T2_mem (K : Type) [Field K] : wp1T2 K ∈ StatedSL 2 K :=
  Subgroup.subset_closure (by simp [wp1T2, Matrix.det_fin_two])

private theorem wp1_det_eq_one_of_mem {K : Type} [Field K] {g : GL (Fin 2) K}
    (hg : g ∈ StatedSL 2 K) : (g : Matrix (Fin 2) (Fin 2) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

theorem central_eq_one_of_isLTwoOddPow {X : Type*} [Group X] (h : IsLTwoOddPow X) :
    ∀ z : X, (∀ w : X, w * z = z * w) → z = 1 := by
  obtain ⟨K, _, hfin, n, hn, hn1, hcard, ⟨e⟩⟩ := h
  have h2 : (2 : K) = 0 := wp1_two_eq_zero (by rw [hcard]; exact dvd_pow_self 2 (by omega))
  intro z hz
  have hcomm : ∀ (T : GL (Fin 2) K) (hT : T ∈ StatedSL 2 K),
      T * (e z : GL (Fin 2) K) = (e z : GL (Fin 2) K) * T := by
    intro T hT
    have := congrArg (fun x : X => ((e x : ↥(StatedSL 2 K)) : GL (Fin 2) K)) (hz (e.symm ⟨T, hT⟩))
    simpa using this
  have c1 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K))
    (hcomm _ (wp1T1_mem K))
  have c2 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K))
    (hcomm _ (wp1T2_mem K))
  have hd := wp1_det_eq_one_of_mem (e z).2
  set M : Matrix (Fin 2) (Fin 2) K := (((e z : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hM
  simp only [Units.val_mul] at c1 c2
  have a1 := congrFun (congrFun c1 0) 0
  have a2 := congrFun (congrFun c1 0) 1
  have a3 := congrFun (congrFun c2 0) 0
  have a4 := congrFun (congrFun c2 0) 1
  have a5 := congrFun (congrFun c1 1) 1
  simp [wp1T1, wp1T2, Matrix.mul_apply, Fin.sum_univ_two] at a1 a2 a3 a4 a5
  rw [Matrix.det_fin_two] at hd
  have e10 : M 1 0 = 0 := a1
  have e01 : M 0 1 = 0 := a3
  have e11 : M 1 1 = M 0 0 := by linear_combination a2
  have ha : (M 0 0 - 1) ^ 2 = 0 := by
    rw [e10, e11] at hd
    linear_combination hd + (1 - M 0 0) * h2
  have ha1 : M 0 0 = 1 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.1 ha
    linear_combination this
  have hM1 : M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e10, e01, e11, ha1]
  have hg1 : (e z : GL (Fin 2) K) = 1 := Units.ext hM1
  have : e z = 1 := Subtype.ext hg1
  exact (map_eq_one_iff e e.injective).1 this

private def wp1Inv (K : Type) [Field K] : GL (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], !![0, 1, 0; 1, 0, 0; 0, 0, -1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

private theorem wp1Inv_orderOf (K : Type) [Field K] : orderOf (wp1Inv K) = 2 := by
  apply orderOf_eq_prime
  · apply Units.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [wp1Inv, pow_two, Matrix.mul_apply, Fin.sum_univ_three]
  · intro h
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp [wp1Inv] at this

private theorem wp1Inv_mem_SL (K : Type) [Field K] : wp1Inv K ∈ StatedSL 3 K :=
  Subgroup.subset_closure (by simp [wp1Inv, Matrix.det_fin_three])

private theorem wp1Inv_mem_SU (K : Type) [Field K] (q : ℕ) (hq0 : q ≠ 0) (hq : (-1 : K) ^ q = -1) :
    wp1Inv K ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ⟨by simp [wp1Inv, Matrix.det_fin_three], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wp1Inv, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, hq, zero_pow hq0]

private theorem wp1_orderOf_transport {X : Type*} [Group X] {K : Type} [Field K]
    {S : Subgroup (GL (Fin 3) K)} (e : X ≃* ↥S) (hA : wp1Inv K ∈ S) :
    ∃ u : X, orderOf u = 2 := by
  refine ⟨e.symm ⟨wp1Inv K, hA⟩, ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, wp1Inv_orderOf]

theorem exists_orderOf_two_of_exc {X : Type*} [Group X]
    (h : IsSLThreeExc X ∨ IsSUThreeExc X) : ∃ u : X, orderOf u = 2 := by
  rcases h with ⟨K, _, hfin, hK, ⟨e⟩⟩ | ⟨K, _, hfin, q, hq, hq9, ⟨e⟩⟩
  · exact wp1_orderOf_transport e (wp1Inv_mem_SL K)
  · have hq0 : q ≠ 0 := by omega
    refine wp1_orderOf_transport e (wp1Inv_mem_SU K q hq0 ?_)
    rcases Nat.even_or_odd q with he | ho
    · have h2 : (2 : K) = 0 := wp1_two_eq_zero (by
        rw [hq]; exact dvd_pow (even_iff_two_dvd.1 he) two_ne_zero)
      have : (-1 : K) = 1 := by linear_combination -h2
      rw [he.neg_one_pow, this]
    · exact ho.neg_one_pow

private theorem wp1_core_eq {b : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L) :
    GLAPPrimeCoreOf 3 L = L ⊓ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  apply le_antisymm
  · exact le_inf (Subgroup.map_subtype_le _)
      (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hL.2.1)
  · have := gLAPPrimeCoreOf_inf_le (G := G) Nat.prime_three (Subgroup.centralizer ({b} : Set G)) L
    rw [inf_eq_right.2 hL.1] at this
    rw [inf_comm]
    exact this

private theorem wp1_mem_core_iff {b : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L) (y : ↥L) :
    y ∈ GLAPPrimeCore 3 ↥L ↔ (y : G) ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  have h1 : y ∈ GLAPPrimeCore 3 ↥L ↔ (y : G) ∈ GLAPPrimeCoreOf 3 L :=
    ⟨fun h => ⟨y, h, rfl⟩, fun ⟨y', hy', e⟩ => (Subtype.ext e : y' = y) ▸ hy'⟩
  rw [h1, wp1_core_eq hL]
  exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩

private def wp1Hom (b : G) {L : Subgroup G} (hLC : L ≤ Subgroup.centralizer ({b} : Set G)) :
    ↥L →* CBar 3 b :=
  (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Subgroup.centralizer ({b} : Set G)))).comp
    (Subgroup.inclusion hLC)

private theorem wp1Hom_ker {b : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L) :
    (wp1Hom b hL.1).ker = GLAPPrimeCore 3 ↥L := by
  ext y
  rw [wp1_mem_core_iff hL, MonoidHom.mem_ker]
  change (QuotientGroup.mk (Subgroup.inclusion hL.1 y) : CBar 3 b) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨c, hc, hcy⟩ => by
    have : c = Subgroup.inclusion hL.1 y := Subtype.ext hcy
    exact this ▸ hc⟩

private theorem wp1Hom_range {b : G} {L : Subgroup G} (hLC : L ≤ Subgroup.centralizer ({b} : Set G)) :
    (wp1Hom b hLC).range = barImageAt 3 b L := by
  ext w
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Subgroup.inclusion hLC y, (Subgroup.mem_subgroupOf).2 y.2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c, (Subgroup.mem_subgroupOf).1 hc⟩, rfl⟩

theorem nonempty_mulEquiv_barOf_barImageAt {b : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L) :
    Nonempty (barOf 3 L ≃* ↥(barImageAt 3 b L)) := by
  have e1 : barOf 3 L ≃* (↥L ⧸ (wp1Hom b hL.1).ker) :=
    QuotientGroup.quotientMulEquivOfEq (wp1Hom_ker hL).symm
  exact ⟨e1.trans ((QuotientGroup.quotientKerEquivRange (wp1Hom b hL.1)).trans
    (MulEquiv.subgroupCongr (wp1Hom_range hL.1)))⟩

theorem exists_twoElement_of_shape {b : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hshape : IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L)) :
    ∃ k ∈ L, k ∉ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ∧
      ∃ e : ℕ, orderOf k = 2 ^ e := by
  obtain ⟨u, hu⟩ := exists_orderOf_two_of_exc hshape
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective u
  have hpos : orderOf ℓ ≠ 0 := (orderOf_pos ℓ).ne'
  obtain ⟨a, r, hr, hord⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have hu1 : (QuotientGroup.mk ℓ : barOf 3 L) ^ 2 = 1 := hu ▸ pow_orderOf_eq_one _
  have hne : (QuotientGroup.mk ℓ : barOf 3 L) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hu; omega
  refine ⟨((ℓ ^ r : ↥L) : G), (ℓ ^ r).2, ?_, ?_⟩
  · rw [← wp1_mem_core_iff hL, ← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk ℓ : barOf 3 L) ^ r ≠ 1
    obtain ⟨m, rfl⟩ := hr
    rw [pow_succ, pow_mul, hu1, one_pow, one_mul]
    exact hne
  · have hd : orderOf (ℓ ^ r) ∣ 2 ^ a := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
    obtain ⟨c, _, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact ⟨c, by rw [Subgroup.orderOf_coe]; exact hc⟩


private theorem wp3_shape_transport {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSLThreeExc X ∨ IsSUThreeExc X) : IsSLThreeExc Y ∨ IsSUThreeExc Y := by
  rcases h with ⟨K, F, fin, hk, ⟨e'⟩⟩ | ⟨K, F, fin, q, hk, hq, ⟨e'⟩⟩
  · exact Or.inl ⟨K, F, fin, hk, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨K, F, fin, q, hk, hq, ⟨e.symm.trans e'⟩⟩

private theorem wp3_bar_congr (b : G) {y z : G} (hy : y ∈ Subgroup.centralizer ({b} : Set G))
    (hz : z ∈ Subgroup.centralizer ({b} : Set G)) (h : y = z) : bar b hy = bar b hz := by
  subst h; rfl

private theorem wp3_bar_comm_of_mem {b ℓ y : G} (hℓ : ℓ ∈ Subgroup.centralizer ({b} : Set G))
    (hy : y ∈ Subgroup.centralizer ({b} : Set G))
    (h : y⁻¹ * ℓ⁻¹ * y * ℓ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) :
    bar b hℓ * bar b hy = bar b hy * bar b hℓ := by
  rw [bar_mul, bar_mul, bar_eq_iff]
  simpa [mul_assoc] using h

theorem exists_central_in_conj {B L Li : Subgroup G} {b : G} (hB : IsElemAbelian 3 B) (hbB : b ∈ B)
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hshape : IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L)) (hLi : IsBConjugate B L Li) :
    ∃ (ℓ : G) (hℓ : ℓ ∈ Subgroup.centralizer ({b} : Set G)), ℓ ∈ Li ∧ bar b hℓ ≠ 1 ∧
      bar b hℓ ∈ barCenterAt 3 b (bClosure B L) := by
  classical
  obtain ⟨g₀, hg₀, rfl⟩ := hLi
  have hBC : ∀ g ∈ B, g * b = b * g := fun g hg => by
    have := hB.1.is_comm.comm (⟨g, hg⟩ : B) ⟨b, hbB⟩
    exact congrArg Subtype.val this
  have hcomp : ∀ g ∈ B,
      GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) (GLBConj g L) := fun g hg => by
    have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g
    rwa [gLBConj_centralizer_singleton_of_commute (hBC g hg)] at this
  have hLiC : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) (GLBConj g₀ L) := hcomp g₀ hg₀
  have hshape' : IsSLThreeExc (barOf 3 (GLBConj g₀ L)) ∨ IsSUThreeExc (barOf 3 (GLBConj g₀ L)) :=
    wp3_shape_transport (conjQuotEquiv 3 g₀ L) hshape
  obtain ⟨e⟩ := nonempty_mulEquiv_barOf_barImageAt hLiC
  obtain ⟨ζ, hζ1, hζc⟩ := exists_central_ne_one_of_exc (wp3_shape_transport e hshape')
  have hcommg : ∀ g ∈ B, ∀ (y : G) (hy : y ∈ Subgroup.centralizer ({b} : Set G)),
      y ∈ GLBConj g L → bar b hy * (ζ : CBar 3 b) = (ζ : CBar 3 b) * bar b hy := by
    intro g hg y hy hyg
    obtain ⟨ℓ, hℓ, hℓL, hℓζ⟩ := mem_barImageAt_iff.1 ζ.2
    by_cases hne : GLBConj g L = GLBConj g₀ L
    · rw [hne] at hyg
      have := hζc ⟨bar b hy, mem_barImageAt_iff.2 ⟨y, hy, hyg, rfl⟩⟩
      exact congrArg Subtype.val this
    · have hcm := commutator_le_gLAPPrimeCore_of_ne (by norm_num : Nat.Prime 3)
        (hcomp g hg) hLiC hne
      have hmem : y⁻¹ * ℓ⁻¹ * y * ℓ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
        apply hcm
        have := Subgroup.commutator_mem_commutator (H₁ := GLBConj g L) (H₂ := GLBConj g₀ L)
          (inv_mem hyg) (inv_mem hℓL)
        simpa [commutatorElement_def, mul_assoc] using this
      rw [← hℓζ]
      exact (wp3_bar_comm_of_mem hℓ hy hmem).symm
  let T : Subgroup ↥(Subgroup.centralizer ({b} : Set G)) :=
    (Subgroup.centralizer ({(ζ : CBar 3 b)} : Set (CBar 3 b))).comap
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Subgroup.centralizer ({b} : Set G))))
  let S : Subgroup G := T.map (Subgroup.centralizer ({b} : Set G)).subtype
  have hKS : bClosure B L ≤ S := by
    refine iSup₂_le fun g hg y hy => ?_
    have hyC : y ∈ Subgroup.centralizer ({b} : Set G) := by
      have := (hcomp g hg).1 hy
      exact this
    refine ⟨⟨y, hyC⟩, ?_, rfl⟩
    show QuotientGroup.mk' _ ⟨y, hyC⟩ ∈ Subgroup.centralizer ({(ζ : CBar 3 b)} : Set (CBar 3 b))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcommg g hg y hyC hy
  have hLiK : GLBConj g₀ L ≤ bClosure B L := le_iSup₂ (f := fun (g : G) (_ : g ∈ B) => GLBConj g L) g₀ hg₀
  obtain ⟨ℓ, hℓ, hℓL, hℓζ⟩ := mem_barImageAt_iff.1 ζ.2
  refine ⟨ℓ, hℓ, hℓL, ?_, ?_⟩
  · rw [hℓζ]; exact_mod_cast hζ1
  · have hζK : bar b hℓ ∈ barImageAt 3 b (bClosure B L) :=
      mem_barImageAt_iff.2 ⟨ℓ, hℓ, hLiK hℓL, rfl⟩
    refine ⟨⟨bar b hℓ, hζK⟩, ?_, rfl⟩
    show _ ∈ Subgroup.center _
    rw [Subgroup.mem_center_iff]
    intro v
    obtain ⟨y, hy, hyK, hyv⟩ := mem_barImageAt_iff.1 v.2
    have hyS := hKS hyK
    obtain ⟨c, hc, hcy⟩ := hyS
    have hcy' : c = ⟨y, hy⟩ := Subtype.ext hcy
    subst hcy'
    have hcc : QuotientGroup.mk' _ (⟨y, hy⟩ : ↥(Subgroup.centralizer ({b} : Set G))) ∈
        Subgroup.centralizer ({(ζ : CBar 3 b)} : Set (CBar 3 b)) := hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hcc
    apply Subtype.ext
    show (v : CBar 3 b) * bar b hℓ = bar b hℓ * v
    rw [← hyv, hℓζ]
    exact hcc

theorem mem_of_zpowers_eq_center {B L Li : Subgroup G} {b : G} (hB : IsElemAbelian 3 B) (hbB : b ∈ B)
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hshape : IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L)) (hLi : IsBConjugate B L Li)
    (hZ : barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L)) : b ∈ Li := by
  classical
  obtain ⟨ℓ, hℓ, hℓLi, hℓ1, hℓZ⟩ := exists_central_in_conj hB hbB hL hshape hLi
  rw [← hZ] at hℓZ
  obtain ⟨y, hy, hyz, hyℓ⟩ := mem_barImageAt_iff.1 hℓZ
  have hb3 : b ^ 3 = 1 := hB.2 b hbB
  have hbC : b ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hℓ1
    rw [← hyℓ]
    exact (wp3_bar_congr b hy (one_mem _) rfl).trans rfl
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyz
  have hord : orderOf b = 3 := by
    have hd : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      apply hy1
      rw [h]; simp
    · exact h
  have hi : b ^ (i % 3) = b ^ i := by
    have := zpow_mod_orderOf b i
    rw [hord] at this
    simpa using this
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  have key : ∃ (g : G) (hg : g ∈ Subgroup.centralizer ({b} : Set G)), g ∈ Li ∧
      bar b hbC = bar b hg := by
    rcases hcases with h | h | h
    · exfalso
      apply hy1
      rw [← hi]
      have : i % 3 = 0 := h
      simp [this]
    · refine ⟨ℓ, hℓ, hℓLi, ?_⟩
      rw [hyℓ.symm]
      apply wp3_bar_congr
      rw [← hi]
      have : i % 3 = 1 := h
      simp [this]
    · refine ⟨ℓ * ℓ, mul_mem hℓ hℓ, mul_mem hℓLi hℓLi, ?_⟩
      rw [← bar_mul b hℓ hℓ, ← hyℓ, bar_mul]
      apply wp3_bar_congr
      have hyy : b ^ i = b ^ 2 := by
        rw [← hi]
        have : i % 3 = 2 := h
        simp [this]
      rw [hyy]
      calc b = b ^ 3 * b := by rw [hb3]; simp
        _ = b ^ 2 * b ^ 2 := by group
  obtain ⟨g, hg, hgLi, hbg⟩ := key
  have hn : g⁻¹ * b ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) :=
    (bar_eq_iff hg hbC).1 hbg.symm
  have hgb : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hcomm : g * (g⁻¹ * b) = (g⁻¹ * b) * g := by
    calc g * (g⁻¹ * b) = b := by group
      _ = (g⁻¹ * b) * g := by rw [mul_assoc, ← hgb]; group
  have hmem := mem_zpowers_of_mul_eq hord (by group : g * (g⁻¹ * b) = b) hcomm
    (coprime_orderOf_of_mem_nb hn)
  exact (Subgroup.zpowers_le.2 hgLi) hmem


private theorem wp4_fixed {H : Type*} [Group H] [Finite H] (P Z : Subgroup H)
    (hP : ∀ g ∈ P, g ^ 3 = 1) (hZ3 : ∀ z ∈ Z, z ^ 3 = 1) (hZnt : ∃ z ∈ Z, z ≠ 1)
    (hconj : ∀ g ∈ P, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) :
    ∃ z ∈ Z, z ≠ 1 ∧ ∀ g ∈ P, g * z = z * g := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : P →* Equiv.Perm Z :=
    { toFun := fun g =>
        { toFun := fun z => ⟨(g : H) * z * (g : H)⁻¹, hconj g g.2 z z.2⟩
          invFun := fun z => ⟨(g : H)⁻¹ * z * (g : H), by
            simpa using hconj (g : H)⁻¹ (inv_mem g.2) z z.2⟩
          left_inv := fun z => Subtype.ext (by simp [mul_assoc])
          right_inv := fun z => Subtype.ext (by simp [mul_assoc]) }
      map_one' := Equiv.ext fun z => Subtype.ext (by simp)
      map_mul' := fun g h => Equiv.ext fun z => Subtype.ext (by simp [mul_assoc]) }
  let _ : MulAction P Z := MulAction.compHom Z φ
  have hsmul : ∀ (g : P) (z : Z), ((g • z : Z) : H) = (g : H) * z * (g : H)⁻¹ := fun g z => rfl
  have hPg : IsPGroup 3 P := fun g => ⟨1, by
    refine Subtype.ext ?_
    simpa using hP g g.2⟩
  have hZg : IsPGroup 3 Z := fun g => ⟨1, by
    refine Subtype.ext ?_
    simpa using hZ3 g g.2⟩
  obtain ⟨z0, hz0, hz01⟩ := hZnt
  have hcard : 3 ∣ Nat.card Z := by
    refine hZg.card_eq_or_dvd.resolve_left fun h => ?_
    rw [Subgroup.card_eq_one] at h
    exact hz01 (Subgroup.mem_bot.1 (h ▸ hz0))
  have h1 : (1 : Z) ∈ MulAction.fixedPoints P Z := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact Subtype.ext (by rw [hsmul]; simp)
  obtain ⟨w, hw, hw1⟩ := hPg.exists_fixed_point_of_prime_dvd_card_of_fixed_point Z hcard h1
  refine ⟨w, w.2, fun h => hw1 (Subtype.ext h.symm), fun g hg => ?_⟩
  have := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hw ⟨g, hg⟩)
  rw [hsmul] at this
  simpa [mul_inv_eq_iff_eq_mul] using this

private theorem wp4_bClosure_le {B L : Subgroup G} {g : G} (hg : g ∈ B) :
    GLBConj g (bClosure B L) ≤ bClosure B L := by
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  unfold bClosure
  refine iSup₂_le fun b hb => ?_
  intro z hz
  rw [Subgroup.mem_comap]
  have e : (MulAut.conj g⁻¹).toMonoidHom z = g⁻¹ * z * g := by
    simp
  rw [e]
  have hm : g⁻¹ * z * g ∈ GLBConj (b * g) L := by
    rw [mem_gLBConj]
    have e2 : b * g * (g⁻¹ * z * g) * (b * g)⁻¹ = b * z * b⁻¹ := by group
    rw [e2]
    exact mem_gLBConj.1 hz
  exact (le_iSup₂ (f := fun (c : G) (_ : c ∈ B) => GLBConj c L) (b * g)
    (B.mul_mem hb hg)) hm

private theorem wp4_bClosure_eq {B L : Subgroup G} {g : G} (hg : g ∈ B) :
    GLBConj g (bClosure B L) = bClosure B L := by
  refine le_antisymm (wp4_bClosure_le hg) ?_
  have h0 : GLBConj g⁻¹ (bClosure B L) ≤ bClosure B L :=
    wp4_bClosure_le (B.inv_mem hg)
  have h1 : GLBConj g (GLBConj g⁻¹ (bClosure B L)) ≤ GLBConj g (bClosure B L) :=
    gLBConj_mono g h0
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h1

private theorem wp4_mem_center {b : G} {K : Subgroup G} {z : CBar 3 b} :
    z ∈ barCenterAt 3 b K ↔
      z ∈ barImageAt 3 b K ∧ ∀ w ∈ barImageAt 3 b K, w * z = z * w := by
  unfold barCenterAt
  constructor
  · rintro ⟨⟨c, hc⟩, hcz, rfl⟩
    refine ⟨hc, fun w hw => ?_⟩
    have := Subgroup.mem_center_iff.1 hcz ⟨w, hw⟩
    exact congrArg Subtype.val this
  · rintro ⟨hz, h⟩
    refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun w => Subtype.ext (h w w.2), rfl⟩

theorem exists_B_elem_of_central {B D : Subgroup G} {b : G} {L : Subgroup G}
    (hS : Lemma24Setup 3 B D b L) (hC : Lemma24Conclusion B D b L)
    (hz : ∃ z ∈ barCenterAt 3 b (bClosure B L), z ≠ 1) :
    ∃ (x : G) (hx : x ∈ Subgroup.centralizer ({b} : Set G)), x ∈ B ∧ x ≠ 1 ∧
      bar b hx ∈ barCenterAt 3 b (bClosure B L) := by
  classical
  have hBab : IsMulCommutative B := hS.isBOneMax.1.1.1
  have hB3 : ∀ x ∈ B, x ^ 3 = 1 := hS.isBOneMax.1.1.2
  have hbB : b ∈ B := hS.mem
  have hBC : ∀ {g : G}, g ∈ B → g ∈ Subgroup.centralizer ({b} : Set G) := fun {g} hg => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (hBab.is_comm.comm (⟨b, hbB⟩ : B) ⟨g, hg⟩)).symm
  have hLC : L ≤ Subgroup.centralizer ({b} : Set G) := hS.isComp.1
  have hKC : bClosure B L ≤ Subgroup.centralizer ({b} : Set G) := by
    refine iSup₂_le fun g hg => ?_
    have h1 := gLBConj_mono g hLC
    rwa [gLBConj_centralizer_singleton_of_commute
      (Subgroup.mem_centralizer_singleton_iff.1 (hBC hg))] at h1
  have hKconj : ∀ {y : G}, y ∈ B → ∀ {κ : G}, κ ∈ bClosure B L → y * κ * y⁻¹ ∈ bClosure B L := by
    intro y hy κ hκ
    rw [← wp4_bClosure_eq hy] at hκ
    exact mem_gLBConj.1 hκ
  have hBbar : ∀ g ∈ barImageAt 3 b B, ∀ w ∈ barImageAt 3 b (bClosure B L),
      g * w * g⁻¹ ∈ barImageAt 3 b (bClosure B L) := by
    intro g hg w hw
    obtain ⟨y, hy, hyB, rfl⟩ := mem_barImageAt_iff.1 hg
    obtain ⟨κ, hκ, hκK, rfl⟩ := mem_barImageAt_iff.1 hw
    rw [bar_inv, bar_mul, bar_mul]
    exact mem_barImageAt_iff.2 ⟨_, _, hKconj hyB hκK, rfl⟩
  have hZconj : ∀ g ∈ barImageAt 3 b B, ∀ z ∈ barCenterAt 3 b (bClosure B L),
      g * z * g⁻¹ ∈ barCenterAt 3 b (bClosure B L) := by
    intro g hg z hz
    obtain ⟨hzK, hzc⟩ := wp4_mem_center.1 hz
    refine wp4_mem_center.2 ⟨hBbar g hg z hzK, fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ barImageAt 3 b (bClosure B L) := by
      simpa using hBbar g⁻¹ (inv_mem hg) w hw
    calc w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [hzc _ hw']
      _ = g * z * g⁻¹ * w := by group
  have hP3 : ∀ g ∈ barImageAt 3 b B, g ^ 3 = 1 := by
    intro g hg
    obtain ⟨y, hy, hyB, rfl⟩ := mem_barImageAt_iff.1 hg
    have h1 : bar b hy ^ 3 = bar b (mul_mem hy hy) * bar b hy := by
      rw [← bar_mul b hy hy]; simp only [pow_succ, pow_zero, one_mul]
    rw [h1, bar_mul b (mul_mem hy hy) hy]
    have h2 : y * y * y ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
      have : y * y * y = 1 := by rw [← pow_three']; exact hB3 y hyB
      rw [this]; exact one_mem _
    obtain ⟨h, h3⟩ := mem_nb_iff.1 h2
    exact h3
  have hZ3 : ∀ z ∈ barCenterAt 3 b (bClosure B L), z ^ 3 = 1 := by
    intro z hz
    obtain ⟨hzK, hzc⟩ := wp4_mem_center.1 hz
    have hmem : (⟨z, hzK⟩ : ↥(barImageAt 3 b (bClosure B L))) ∈
        Subgroup.center ↥(barImageAt 3 b (bClosure B L)) :=
      Subgroup.mem_center_iff.2 fun w => Subtype.ext (hzc w w.2)
    have := hC.2.2.2.1.1.2 _ hmem
    exact congrArg Subtype.val this
  have : Finite (CBar 3 b) := inferInstance
  obtain ⟨z, hzZ, hz1, hzc⟩ := wp4_fixed (barImageAt 3 b B) (barCenterAt 3 b (bClosure B L))
    hP3 hZ3 hz hZconj
  have hzB : z ∈ barImageAt 3 b B :=
    hC.2.2.2.2 ⟨hzZ, Subgroup.mem_centralizer_iff.2 fun g hg => hzc g hg⟩
  obtain ⟨x, hx, hxB, rfl⟩ := mem_barImageAt_iff.1 hzB
  refine ⟨x, hx, hxB, fun h => hz1 ?_, hzZ⟩
  subst h
  exact (mem_nb_iff.1 (one_mem _)).choose_spec


private theorem wp5a_hcomm_bar {b x : G} {L : Subgroup G}
    (hLC : L ≤ Subgroup.centralizer ({b} : Set G))
    (hx : x ∈ Subgroup.centralizer ({b} : Set G))
    (hcomm : ∀ ℓ ∈ L, ℓ * x * ℓ⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)))
    {ℓ : G} (hℓ : ℓ ∈ L) :
    bar b (hLC hℓ) * bar b hx = bar b hx * bar b (hLC hℓ) := by
  rw [bar_mul, bar_mul, bar_eq_iff]
  have h := nb_conj_mem (inv_mem hx) (hcomm ℓ⁻¹ (L.inv_mem hℓ))
  convert h using 1
  group

private theorem wp5a_barImageAt_gLBConj {b x : G} {L : Subgroup G}
    (hLC : L ≤ Subgroup.centralizer ({b} : Set G))
    (hx : x ∈ Subgroup.centralizer ({b} : Set G))
    (hcomm : ∀ ℓ ∈ L, ℓ * x * ℓ⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) :
    barImageAt 3 b (GLBConj x L) = barImageAt 3 b L := by
  ext w
  rw [mem_barImageAt_iff, mem_barImageAt_iff]
  constructor
  · rintro ⟨y, hy, hyL, rfl⟩
    have hyL' : x * y * x⁻¹ ∈ L := mem_gLBConj.1 hyL
    have hy' : x * y * x⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
      mul_mem (mul_mem hx hy) (inv_mem hx)
    refine ⟨x * y * x⁻¹, hy', hyL', ?_⟩
    have hc := wp5a_hcomm_bar hLC hx hcomm hyL'
    have e1 : bar b hy' = bar b hx * bar b hy * (bar b hx)⁻¹ := by
      rw [bar_inv, bar_mul, bar_mul]
    have e2 : bar b hy = (bar b hx)⁻¹ * bar b hy' * bar b hx := by
      rw [e1]; group
    have hc' : bar b hy' * bar b hx = bar b hx * bar b hy' := hc
    calc bar b hy' = (bar b hx)⁻¹ * (bar b hx * bar b hy') := by group
      _ = (bar b hx)⁻¹ * (bar b hy' * bar b hx) := by rw [hc']
      _ = bar b hy := by rw [e2]; group
  · rintro ⟨y, hy, hyL, rfl⟩
    have hy' : x⁻¹ * y * x ∈ Subgroup.centralizer ({b} : Set G) :=
      mul_mem (mul_mem (inv_mem hx) hy) hx
    refine ⟨x⁻¹ * y * x, hy', mem_gLBConj.2 (by
      have : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      rw [this]; exact hyL), ?_⟩
    have hc : bar b hy * bar b hx = bar b hx * bar b hy := wp5a_hcomm_bar hLC hx hcomm hyL
    have e1 : bar b hy' = (bar b hx)⁻¹ * bar b hy * bar b hx := by
      rw [bar_inv, bar_mul, bar_mul]
    rw [e1, mul_assoc, hc]
    group

private theorem wp5a_normalizes {b x : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hx : x ∈ Subgroup.centralizer ({b} : Set G))
    (hcomm : ∀ ℓ ∈ L, ℓ * x * ℓ⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  have hxb : x * b = b * x := (Subgroup.mem_centralizer_singleton_iff).1 hx
  have hconj := gLBConj_centralizer_singleton_of_commute hxb
  have h1 : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) (GLBConj x L) := by
    have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL x
    rwa [hconj] at this
  have hbar : barX 3 (Subgroup.centralizer ({b} : Set G)) (GLBConj x L) =
      barX 3 (Subgroup.centralizer ({b} : Set G)) L :=
    wp5a_barImageAt_gLBConj hL.1 hx hcomm
  exact mem_normalizer_iff_gLBConj_eq.2 (glaPComponent_uniqueAux h1 hL hbar)

private theorem wp5a_coprime_card_core (C : Subgroup G) :
    Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 C)) := by
  have hc := coprime_card_gLAPPrimeCore_aux 3 ↥C
  have hcard : Nat.card (GLAPPrimeCoreOf 3 C) = Nat.card (GLAPPrimeCore 3 ↥C) :=
    Subgroup.card_map_of_injective C.subtype_injective
  rwa [hcard]

private theorem wp5a_fixed_point {b x : G} {L : Subgroup G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (hx3 : orderOf x = 3)
    (hcomm : ∀ ℓ ∈ L, ℓ * x * ℓ⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)))
    (hnorm : x ∈ Subgroup.normalizer (L : Set G)) {ℓ : G} (hℓ : ℓ ∈ L) :
    ∃ c ∈ L ⊓ Subgroup.centralizer ({x} : Set G),
      c⁻¹ * ℓ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  classical
  set N := GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) with hN
  have hxL : ∀ g ∈ L, x * g * x⁻¹ ∈ L := fun g hg =>
    (Subgroup.mem_normalizer_iff.1 hnorm g).1 hg
  let α : Type _ := {s : G // ℓ⁻¹ * s ∈ L ⊓ N}
  have hstep : ∀ s : G, ℓ⁻¹ * s ∈ L ⊓ N → ℓ⁻¹ * (x * s * x⁻¹) ∈ L ⊓ N := by
    intro s hs
    have ht : ℓ⁻¹ * x * ℓ * x⁻¹ ∈ N := by
      have := hcomm ℓ⁻¹ (L.inv_mem hℓ)
      simpa using this
    have htL : ℓ⁻¹ * x * ℓ * x⁻¹ ∈ L := by
      have := L.mul_mem (L.inv_mem hℓ) (hxL ℓ hℓ)
      simpa [mul_assoc] using this
    have hmL : x * (ℓ⁻¹ * s) * x⁻¹ ∈ L := hxL _ hs.1
    have hmN : x * (ℓ⁻¹ * s) * x⁻¹ ∈ N := nb_conj_mem hx hs.2
    have : ℓ⁻¹ * (x * s * x⁻¹) = (ℓ⁻¹ * x * ℓ * x⁻¹) * (x * (ℓ⁻¹ * s) * x⁻¹) := by group
    rw [this]
    exact ⟨L.mul_mem htL hmL, N.mul_mem ht hmN⟩
  let f : Function.End α := fun s => ⟨x * s.1 * x⁻¹, hstep s.1 s.2⟩
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    have hx3' : x ^ 3 = 1 := hx3 ▸ pow_orderOf_eq_one x
    have h3 : x * x * x = 1 := (pow_three' x).symm.trans hx3'
    have : x * (x * (x * s.1 * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * s.1 * (x * x * x)⁻¹ := by group
    show x * (x * (x * s.1 * x⁻¹) * x⁻¹) * x⁻¹ = s.1
    rw [this, h3]; group
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype α := Fintype.ofFinite α
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf3
  have hcardα : Fintype.card α = Nat.card ↥(L ⊓ N) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun s => ⟨ℓ⁻¹ * s.1, s.2⟩
        invFun := fun m => ⟨ℓ * m.1, by simp⟩
        left_inv := fun s => by apply Subtype.ext; simp
        right_inv := fun m => by apply Subtype.ext; simp }
  have hcop : Nat.Coprime 3 (Fintype.card α) := by
    rw [hcardα]
    exact (wp5a_coprime_card_core _).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  have hne : Fintype.card (Function.fixedPoints f) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    have h3 : 3 ∣ Fintype.card α := (Nat.modEq_zero_iff_dvd).1 hmod
    have := Nat.Coprime.eq_one_of_dvd hcop h3
    omega
  obtain ⟨⟨s, hs⟩⟩ := Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero hne)
  have hfs : x * s.1 * x⁻¹ = s.1 := congrArg Subtype.val hs
  refine ⟨s.1, ⟨?_, ?_⟩, ?_⟩
  · have := L.mul_mem hℓ s.2.1
    simpa using this
  · show s.1 ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc s.1 * x = (x * s.1 * x⁻¹) * x := by rw [hfs]
      _ = x * s.1 := by group
  · have := N.inv_mem s.2.2
    simpa using this

private def wp5a_hom (b : G) {H : Subgroup G} (hHC : H ≤ Subgroup.centralizer ({b} : Set G)) :
    ↥H →* CBar 3 b :=
  (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Subgroup.centralizer ({b} : Set G)))).comp
    (Subgroup.inclusion hHC)

private theorem wp5a_hom_apply (b : G) {H : Subgroup G}
    (hHC : H ≤ Subgroup.centralizer ({b} : Set G)) (y : ↥H) :
    wp5a_hom b hHC y = bar b (hHC y.2) := rfl

private theorem wp5a_hom_eq_one_iff (b : G) {H : Subgroup G}
    (hHC : H ≤ Subgroup.centralizer ({b} : Set G)) (y : ↥H) :
    wp5a_hom b hHC y = 1 ↔ (y : G) ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) :=
  ⟨fun h => mem_nb_iff.2 ⟨hHC y.2, h⟩, fun h => (mem_nb_iff.1 h).choose_spec⟩

private theorem wp5a_layer_cover {b x : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hcov : ∀ ℓ ∈ L, ∃ c ∈ L ⊓ Subgroup.centralizer ({x} : Set G),
      c⁻¹ * ℓ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) :
    ∀ ℓ ∈ L, ∃ j ∈ GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)),
      j⁻¹ * ℓ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  set Cx : Subgroup G := L ⊓ Subgroup.centralizer ({x} : Set G) with hCx
  have hCxC : Cx ≤ Subgroup.centralizer ({b} : Set G) := inf_le_left.trans hL.1
  set ψ : ↥Cx →* CBar 3 b := wp5a_hom b hCxC with hψ
  set N := GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) with hN
  have hrange : ψ.range = barImageAt 3 b L := by
    ext w
    rw [mem_barImageAt_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, hCxC y.2, y.2.1, rfl⟩
    · rintro ⟨y, hy, hyL, rfl⟩
      obtain ⟨c, hc, hcN⟩ := hcov y hyL
      refine ⟨⟨c, hc⟩, ?_⟩
      rw [wp5a_hom_apply]
      exact (bar_eq_iff _ _).2 hcN
  have hQsub : IsSubnormal (barImageAt 3 b L) ⊤ := hL.2.2.1.2.1
  have hQqs : CFSG.Open.IsQuasisimple ↥(barImageAt 3 b L) := hL.2.2.1.2.2
  have hO : GLAPPrimeCore 3 (CBar 3 b) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
  have hcopP : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥Cx)) := coprime_card_gLAPPrimeCore_aux 3 ↥Cx
  have h3a : ∀ y ∈ GLAPPrimeCore 3 ↥Cx, ψ y = 1 := by
    have hle : (GLAPPrimeCore 3 ↥Cx).map ψ ≤ barImageAt 3 b L :=
      hrange ▸ Subgroup.map_le_range ψ _
    have hn : (((GLAPPrimeCore 3 ↥Cx).map ψ).subgroupOf (barImageAt 3 b L)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hle]
      rintro _ g ⟨p, hp, rfl⟩ hg
      rw [← hrange] at hg
      obtain ⟨c, rfl⟩ := hg
      refine ⟨c * p * c⁻¹, (GLAPPrimeCore.normal 3 ↥Cx).conj_mem p hp c, ?_⟩
      simp
    have hsn : IsSubnormal ((GLAPPrimeCore 3 ↥Cx).map ψ) ⊤ := IsSubnormal.step hle hn hQsub
    have hcop : Nat.Coprime 3 (Nat.card ↥((GLAPPrimeCore 3 ↥Cx).map ψ)) :=
      hcopP.coprime_dvd_right (Subgroup.card_map_dvd _ _)
    have hbot := eq_bot_of_isSubnormal_of_coprime Nat.prime_three hO hsn hcop
    intro y hy
    have : ψ y ∈ (GLAPPrimeCore 3 ↥Cx).map ψ := ⟨y, hy, rfl⟩
    rw [hbot] at this
    exact this
  have hPN : ∀ y ∈ GLAPPrimeCore 3 ↥Cx, (y : G) ∈ N := fun y hy =>
    (wp5a_hom_eq_one_iff b hCxC y).1 (h3a y hy)
  have hker : ψ.ker = GLAPPrimeCore 3 ↥Cx := by
    refine le_antisymm ?_ (fun y hy => h3a y hy)
    refine le_sSup ⟨inferInstance, ?_⟩
    have h1 : Nat.card ↥(ψ.ker.map Cx.subtype) = Nat.card ↥ψ.ker :=
      Subgroup.card_map_of_injective Cx.subtype_injective
    have h2 : ψ.ker.map Cx.subtype ≤ N := by
      rintro _ ⟨y, hy, rfl⟩
      exact (wp5a_hom_eq_one_iff b hCxC y).1 hy
    rw [← h1]
    exact (wp5a_coprime_card_core _).coprime_dvd_right (Subgroup.card_dvd_of_le h2)
  let e : ↥(⊤ : Subgroup (↥Cx ⧸ GLAPPrimeCore 3 ↥Cx)) ≃* ↥(barImageAt 3 b L) :=
    Subgroup.topEquiv.trans ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange)))
  have hK : IsComponentOf (⊤ : Subgroup (↥Cx ⧸ GLAPPrimeCore 3 ↥Cx)) ⊤ :=
    ⟨le_rfl, IsSubnormal.refl _,
      CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hQqs⟩
  obtain ⟨L', hL', hbarL'⟩ := exists_glaPComponent_barX_eq (p := 3) Cx hK
  intro ℓ hℓ
  obtain ⟨c, hc, hcN⟩ := hcov ℓ hℓ
  have hmem : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Cx)) ⟨c, hc⟩ ∈ barX 3 Cx L' := by
    rw [hbarL']; trivial
  obtain ⟨y, hy, hyc⟩ := hmem
  have hyL' : (y : G) ∈ L' := (Subgroup.mem_subgroupOf).1 hy
  have hyP : y⁻¹ * ⟨c, hc⟩ ∈ GLAPPrimeCore 3 ↥Cx := by
    rw [← QuotientGroup.eq]; exact hyc
  refine ⟨y, Subgroup.mem_sSup_of_mem (S := {J | GLAPComponent 3 Cx J}) hL' hyL', ?_⟩
  have h1 : ((y⁻¹ * ⟨c, hc⟩ : ↥Cx) : G) ∈ N := hPN _ hyP
  have : (y : G)⁻¹ * ℓ = (((y⁻¹ * ⟨c, hc⟩ : ↥Cx) : G)) * (c⁻¹ * ℓ) := by
    simp [mul_assoc]
  rw [this]
  exact N.mul_mem h1 hcN

theorem cover_layer {b x : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (hx3 : orderOf x = 3)
    (hcomm : ∀ ℓ ∈ L, ℓ * x * ℓ⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) :
    x ∈ Subgroup.normalizer (L : Set G) ∧
      ∀ ℓ ∈ L, ∃ j ∈ GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)),
        j⁻¹ * ℓ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  have hnorm := wp5a_normalizes hL hx hcomm
  exact ⟨hnorm, wp5a_layer_cover hL fun ℓ hℓ => wp5a_fixed_point hx hx3 hcomm hnorm hℓ⟩


private theorem wp5b_exists_prod {C N J : Subgroup G} (hJ : J ≤ C)
    (hN : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) :
    ∃ P : Subgroup G, ∀ y, y ∈ P ↔ ∃ j ∈ J, ∃ n ∈ N, y = j * n := by
  refine ⟨{ carrier := {y | ∃ j ∈ J, ∃ n ∈ N, y = j * n}
            mul_mem' := ?_
            one_mem' := ⟨1, J.one_mem, 1, N.one_mem, by simp⟩
            inv_mem' := ?_ }, fun y => Iff.rfl⟩
  · rintro _ _ ⟨j, hj, n, hn, rfl⟩ ⟨j', hj', n', hn', rfl⟩
    refine ⟨j * j', J.mul_mem hj hj', j'⁻¹ * n * j' * n', N.mul_mem ?_ hn', by group⟩
    have := hN j'⁻¹ (C.inv_mem (hJ hj')) n hn
    simpa using this
  · rintro _ ⟨j, hj, n, hn, rfl⟩
    refine ⟨j⁻¹, J.inv_mem hj, j * n⁻¹ * j⁻¹, ?_, by group⟩
    exact hN j (hJ hj) n⁻¹ (N.inv_mem hn)

theorem mem_bClosure_Jis {b x : G} {B L : Subgroup G} (hB : IsElemAbelian 3 B) (hbB : b ∈ B)
    (hxB : x ∈ B) (hx3 : orderOf x = 3)
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hcomm : ∀ ℓ ∈ L, ℓ * x * ℓ⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)))
    (hxK : ∃ k ∈ bClosure B L, k⁻¹ * x ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) :
    x ∈ bClosure B (⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)),
          GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)))) := by
  classical
  set C := Subgroup.centralizer ({b} : Set G) with hCdef
  set N := GLAPPrimeCoreOf 3 C with hNdef
  set J₁ := GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) with hJ₁
  set Jis := ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)), GLBConj g J₁ with hJis
  have hBab : IsMulCommutative B := hB.1
  have hcB : ∀ {g : G}, g ∈ B → g * b = b * g := fun {g} hg =>
    congrArg Subtype.val (hBab.is_comm.comm (⟨g, hg⟩ : B) ⟨b, hbB⟩)
  have hcx : ∀ {g : G}, g ∈ B → g * x = x * g := fun {g} hg =>
    congrArg Subtype.val (hBab.is_comm.comm (⟨g, hg⟩ : B) ⟨x, hxB⟩)
  have hgC : ∀ {g : G}, g ∈ B → g ∈ C := fun {g} hg => by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    exact hcB hg
  have hxC : x ∈ C := hgC hxB
  have hLC : L ≤ C := hL.1
  have hJ₁le : J₁ ≤ L ⊓ Subgroup.centralizer ({x} : Set G) :=
    sSup_le fun M hM => hM.1
  have hJ₁Jis : J₁ ≤ Jis := by
    have h1 : (1 : G) ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)) := Subgroup.one_mem _
    have := le_iSup₂ (f := fun (g : G) (_ : g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G))) =>
      GLBConj g J₁) 1 h1
    rwa [gLBConj_one] at this
  set J : Subgroup G := ⨆ g ∈ B, GLBConj g J₁ with hJ
  have hJC : J ≤ C := by
    refine iSup₂_le fun g hg => ?_
    have h1 := gLBConj_mono g (hJ₁le.trans inf_le_left |>.trans hLC)
    rwa [hCdef, gLBConj_centralizer_singleton_of_commute (hcB hg)] at h1
  have hJx : J ≤ Subgroup.centralizer ({x} : Set G) := by
    refine iSup₂_le fun g hg => ?_
    have h1 := gLBConj_mono g (hJ₁le.trans inf_le_right)
    rwa [gLBConj_centralizer_singleton_of_commute (hcx hg)] at h1
  have hJK : J ≤ bClosure B Jis := by
    refine iSup₂_le fun g hg => ?_
    exact (gLBConj_mono g hJ₁Jis).trans
      (le_iSup₂ (f := fun (c : G) (_ : c ∈ B) => GLBConj c Jis) g hg)
  obtain ⟨P, hP⟩ := wp5b_exists_prod (C := C) (N := N) (J := J) hJC
    (fun c hc n hn => nb_conj_mem hc hn)
  have hcover := cover_layer hL hxC hx3 hcomm
  have hKP : bClosure B L ≤ P := by
    refine iSup₂_le fun g hg ℓ hℓ => ?_
    have hℓ' : g * ℓ * g⁻¹ ∈ L := mem_gLBConj.1 hℓ
    obtain ⟨j', hj', hjn⟩ := hcover.2 _ hℓ'
    have hjL : j' ∈ J₁ := hj'
    have hj : g⁻¹ * j' * g ∈ J := by
      have : g⁻¹ * j' * g ∈ GLBConj g J₁ := by
        rw [mem_gLBConj]
        rw [show g * (g⁻¹ * j' * g) * g⁻¹ = j' by group]
        exact hjL
      exact (le_iSup₂ (f := fun (c : G) (_ : c ∈ B) => GLBConj c J₁) g hg) this
    rw [hP]
    refine ⟨g⁻¹ * j' * g, hj, (g⁻¹ * j' * g)⁻¹ * ℓ, ?_, by group⟩
    have := nb_conj_mem (hgC (B.inv_mem hg)) hjn
    have e : g⁻¹ * (j'⁻¹ * (g * ℓ * g⁻¹)) * g⁻¹⁻¹ = (g⁻¹ * j' * g)⁻¹ * ℓ := by group
    rwa [e] at this
  obtain ⟨k, hk, hkx⟩ := hxK
  obtain ⟨j, hjJ, n₁, hn₁, hkj⟩ := (hP k).1 (hKP hk)
  have hn : n₁ * (k⁻¹ * x) ∈ N := N.mul_mem hn₁ hkx
  have hjn : j * (n₁ * (k⁻¹ * x)) = x := by
    rw [← mul_assoc, ← hkj]; group
  have hjxc : j * x = x * j := by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hJx hjJ)
    exact this
  have hcjn : j * (n₁ * (k⁻¹ * x)) = (n₁ * (k⁻¹ * x)) * j := by
    have e : n₁ * (k⁻¹ * x) = j⁻¹ * x := by
      have : j * (n₁ * (k⁻¹ * x)) = x := hjn
      calc n₁ * (k⁻¹ * x) = j⁻¹ * (j * (n₁ * (k⁻¹ * x))) := by group
        _ = j⁻¹ * x := by rw [this]
    rw [e]
    calc j * (j⁻¹ * x) = x := by group
      _ = j⁻¹ * (j * x) := by group
      _ = j⁻¹ * (x * j) := by rw [hjxc]
      _ = j⁻¹ * x * j := by group
  have hx' : x ∈ Subgroup.zpowers j :=
    mem_zpowers_of_mul_eq hx3 hjn hcjn (coprime_orderOf_of_mem_nb hn)
  exact (Subgroup.zpowers_le.2 (hJK hjJ)) hx'


private theorem wp71_ext {A : Type*} [Group A] {H E : Subgroup A} {t : A} (hEH : E ≤ H)
    (hc : ∀ w ∈ H, w * t = t * w) (hE : IsElemAbelian 3 E) (ht3 : t ^ 3 = 1) :
    ∃ E' : Subgroup A, E ≤ E' ∧ t ∈ E' ∧ IsElemAbelian 3 E' := by
  have hpair : ∀ a ∈ (E : Set A) ∪ {t}, ∀ c ∈ (E : Set A) ∪ {t}, a * c = c * a := by
    intro a ha c hc'
    rcases ha with ha | ha <;> rcases hc' with hc' | hc'
    · exact congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨c, hc'⟩)
    · rw [Set.mem_singleton_iff.1 hc']; exact hc a (hEH ha)
    · rw [Set.mem_singleton_iff.1 ha]; exact (hc c (hEH hc')).symm
    · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hc']
  have h1 : ∀ a ∈ (E : Set A) ∪ {t}, ∀ y ∈ Subgroup.closure ((E : Set A) ∪ {t}), a * y = y * a := by
    intro a ha y hy
    have : Subgroup.closure ((E : Set A) ∪ {t}) ≤ Subgroup.centralizer {a} := by
      rw [Subgroup.closure_le]
      intro c hc'
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hpair a ha c hc').symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (this hy)).symm
  have h2 : ∀ y ∈ Subgroup.closure ((E : Set A) ∪ {t}),
      ∀ z ∈ Subgroup.closure ((E : Set A) ∪ {t}), y * z = z * y := by
    intro y hy z hz
    have : Subgroup.closure ((E : Set A) ∪ {t}) ≤ Subgroup.centralizer {z} := by
      rw [Subgroup.closure_le]
      intro c hc'
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact h1 c hc' z hz
    exact Subgroup.mem_centralizer_singleton_iff.1 (this hy)
  refine ⟨Subgroup.closure ((E : Set A) ∪ {t}), ?_, ?_, ⟨⟨⟨fun a b => Subtype.ext (h2 a.1 a.2 b.1 b.2)⟩⟩, ?_⟩⟩
  · exact fun e he => Subgroup.subset_closure (Or.inl he)
  · exact Subgroup.subset_closure (Or.inr rfl)
  · intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hE.2 x hx
      · rw [Set.mem_singleton_iff.1 hx]; exact ht3
    | one => simp
    | mul x y hx hy hx3 hy3 =>
      have hcm : Commute x y := h2 x hx y hy
      rw [hcm.mul_pow, hx3, hy3, one_mul]
    | inv x hx hx3 => rw [inv_pow, hx3, inv_one]

theorem pRank_le_of_central_bar {b x : G} (hx : x ∈ Subgroup.centralizer ({b} : Set G))
    (hx3 : orderOf x = 3) {H : Subgroup (CBar 3 b)} (_hxH : bar b hx ∈ H)
    (hc : ∀ w ∈ H, w * bar b hx = bar b hx * w) {m : ℕ}
    (hm : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({x} : Set G) → IsElemAbelian 3 E →
      CFSG.Open.pRank 3 E ≤ m) : CFSG.Open.pRank 3 H ≤ m := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set π : ↥C →* CBar 3 b := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have ht3 : (bar b hx) ^ 3 = 1 := by
    show (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨x, hx⟩) ^ 3 = 1
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥C) ^ 3 = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one x
      rw [hx3] at this
      exact this
    rw [this, map_one]
  refine csSup_le' ?_
  rintro k ⟨E, hEH, hE, hcard⟩
  obtain ⟨E', hEE', htE', hE'⟩ := wp71_ext hEH hc hE ht3
  let Ehat : Subgroup ↥C := E'.comap π
  have hxE : (⟨x, hx⟩ : ↥C) ∈ Ehat := htE'
  let x' : ↥Ehat := ⟨⟨x, hx⟩, hxE⟩
  have hord' : orderOf x' = 3 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hx3
  have hP3 : IsPGroup 3 (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord']; simp)
  obtain ⟨P, hxP⟩ := hP3.exists_le_sylow
  have hdvd : 3 ^ k ∣ Nat.card P := by
    apply P.pow_dvd_card_of_pow_dvd_card
    rw [← hcard]
    refine (Subgroup.card_dvd_of_le hEE').trans ?_
    have hmap : Ehat.map π = E' := Subgroup.map_comap_eq_self_of_surjective hπs E'
    have := Subgroup.card_map_dvd (H := Ehat) π
    rwa [hmap] at this
  obtain ⟨n, hn⟩ := (P.isPGroup').exists_card_eq
  have hkn : k ≤ n := by
    rw [hn] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  let f : ↥Ehat →* CBar 3 b := π.comp Ehat.subtype
  let ι : ↥Ehat →* G := C.subtype.comp Ehat.subtype
  have hι : Function.Injective ι := C.subtype_injective.comp Ehat.subtype_injective
  have hfP : ∀ p ∈ (P : Subgroup ↥Ehat), f p = 1 → p = 1 := by
    intro p hp hf1
    obtain ⟨a, ha⟩ := P.isPGroup' ⟨p, hp⟩
    have ha' : ι p ^ (3 ^ a) = 1 := by
      rw [← map_pow]
      have : p ^ (3 ^ a) = 1 := congrArg Subtype.val ha
      rw [this, map_one]
    have hN : ι p ∈ GLAPPrimeCoreOf 3 C := mem_nb_iff.2 ⟨p.1.2, hf1⟩
    have hcop := coprime_orderOf_of_mem_nb hN
    have hd : orderOf (ι p) ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one ha'
    have h1 : orderOf (ι p) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right a hcop.symm) hd
    exact hι (orderOf_eq_one_iff.1 h1 |>.trans (map_one ι).symm)
  let g : ↥(P : Subgroup ↥Ehat) →* CBar 3 b := f.comp (P : Subgroup ↥Ehat).subtype
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hfP a.1 a.2 ha)
  have hgE : ∀ a : ↥(P : Subgroup ↥Ehat), g a ∈ E' := fun a => a.1.2
  have hPcomm : ∀ a a' : ↥(P : Subgroup ↥Ehat), a * a' = a' * a := by
    intro a a'
    apply hginj
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE'.1.is_comm.comm (⟨g a, hgE a⟩ : E') ⟨g a', hgE a'⟩)
  have hP3' : ∀ a : ↥(P : Subgroup ↥Ehat), a ^ 3 = 1 := by
    intro a
    apply hginj
    rw [map_pow, map_one]
    exact hE'.2 _ (hgE a)
  let Q : Subgroup G := (P : Subgroup ↥Ehat).map ι
  have hQcard : Nat.card Q = Nat.card P := Subgroup.card_map_of_injective hι
  have hQcomm : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩
    have := congrArg (fun a : ↥(P : Subgroup ↥Ehat) => ι a.1) (hPcomm ⟨p, hp⟩ ⟨p', hp'⟩)
    simpa using this
  have hQ : IsElemAbelian 3 Q := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hQcomm a.1 a.2 b.1 b.2)⟩⟩, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    rw [← map_pow]
    have : p ^ 3 = 1 := congrArg Subtype.val (hP3' ⟨p, hp⟩)
    rw [this, map_one]
  have hxQ : x ∈ Q := ⟨x', hxP (Subgroup.mem_zpowers x'), rfl⟩
  have hQC : Q ≤ Subgroup.centralizer ({x} : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hQcomm q hq x hxQ
  have h1 := hm Q hQC hQ
  have h2 : CFSG.Open.pRank 3 Q = n :=
    CFSG.HardMathSupport.Solomon.LocalBalance.pRank_eq_of_card Nat.prime_three hQ
      (hQcard.trans hn)
  omega


private theorem wp7x_bar_congr (b : G) {y z : G} (hy : y ∈ Subgroup.centralizer ({b} : Set G))
    (hz : z ∈ Subgroup.centralizer ({b} : Set G)) (h : y = z) : bar b hy = bar b hz := by
  subst h; rfl

private theorem wp7x_coprime_card (x : G) :
    ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G))) := by
  have hc := coprime_card_gLAPPrimeCore_aux 3 ↥(Subgroup.centralizer ({x} : Set G))
  have hcard : Nat.card (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G))) =
      Nat.card (GLAPPrimeCore 3 ↥(Subgroup.centralizer ({x} : Set G))) :=
    Subgroup.card_map_of_injective (Subgroup.centralizer ({x} : Set G)).subtype_injective
  rw [← hcard] at hc
  intro h
  have := Nat.Coprime.eq_one_of_dvd hc h
  omega

private theorem wp7x_normalizes (x : G) {c : G} (hc : c ∈ Subgroup.centralizer ({x} : Set G)) :
    c ∈ Subgroup.normalizer
      ((GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => nb_conj_mem hc hh, fun hh => ?_⟩
  have := nb_conj_mem (inv_mem hc) hh
  simpa [mul_assoc] using this

theorem pRank_le_of_even_oPrime {x : G}
    (hev : Even (Nat.card (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G))))) :
    ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({x} : Set G) → IsElemAbelian 3 E →
      CFSG.Open.pRank 3 E ≤ GLATwoLocalRank 3 G := by
  intro E hEC hE
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g.1 g.2)⟩
  obtain ⟨T, hT, -, hT2, hET⟩ := exists_twoGroup_normalized_of_coprime_even (p := 3)
    (by norm_num) (by norm_num) hE3 (fun c hc => wp7x_normalizes x (hEC hc))
    (wp7x_coprime_card x) hev
  exact pRank_le_glaTwoLocalRank_of_normalizes (by norm_num) hT hT2 hET

theorem even_oPrime_of_commutator {x b' c : G} {T : Subgroup G}
    (hb : b' ∈ oPrimePOf 3 (Subgroup.centralizer ({x} : Set G))) (hcx : c ∈ Subgroup.centralizer ({x} : Set G))
    (hT2 : IsPGroup 2 T) (hbT : b' ∈ Subgroup.normalizer (T : Set G)) (hcT : c ∈ T)
    (hne : b' * c * b'⁻¹ * c⁻¹ ≠ 1) :
    Even (Nat.card (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)))) := by
  set C := Subgroup.centralizer ({x} : Set G) with hC
  obtain ⟨b'', hb'', rfl⟩ := hb
  set c'' : ↥C := ⟨c, hcx⟩ with hc''
  set s'' : ↥C := b'' * c'' * b''⁻¹ * c''⁻¹ with hs''
  have hs''O : s'' ∈ oPrimeP 3 ↥C := by
    have : s'' = b'' * (c'' * b''⁻¹ * c''⁻¹) := by rw [hs'']; group
    rw [this]
    exact mul_mem hb'' ((inferInstance : (oPrimeP 3 ↥C).Normal).conj_mem _ (inv_mem hb'') c'')
  have hsval : (s'' : G) = (b'' : G) * c * (b'' : G)⁻¹ * c⁻¹ := rfl
  have hsT : (s'' : G) ∈ T := by
    rw [hsval]
    have h1 : (b'' : G) * c * (b'' : G)⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hbT c).1 hcT
    exact mul_mem h1 (inv_mem hcT)
  obtain ⟨k, hk⟩ := hT2 ⟨(s'' : G), hsT⟩
  have hk' : (s'' : G) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hs1 : s'' ≠ 1 := fun h => hne (by
    have h0 : (s'' : G) = 1 := by rw [h]; rfl
    rw [hsval] at h0
    exact h0)
  have hs''1 : (s'' : G) ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hmk : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) s'' = 1 := by
    set w := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) s'' with hw
    have hwP : w ∈ CFSG.pCore 3 (↥C ⧸ GLAPPrimeCore 3 ↥C) := hs''O
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup : IsPGroup 3 (CFSG.pCore 3 (↥C ⧸ GLAPPrimeCore 3 ↥C)))
      ⟨w, hwP⟩
    have hj' : w ^ (3 ^ j) = 1 := congrArg Subtype.val hj
    have hk2 : w ^ (2 ^ k) = 1 := by
      rw [hw, ← map_pow]
      have : s'' ^ (2 ^ k) = 1 := Subtype.ext hk'
      rw [this, map_one]
    have hg := (pow_gcd_eq_one).2 ⟨hk2, hj'⟩
    have hcop : Nat.gcd (2 ^ k) (3 ^ j) = 1 :=
      Nat.Coprime.pow k j (by norm_num : Nat.Coprime 2 3)
    rwa [hcop, pow_one] at hg
  have hsN : (s'' : G) ∈ GLAPPrimeCoreOf 3 C :=
    ⟨s'', (QuotientGroup.eq_one_iff _).1 hmk, rfl⟩
  have hdvd : orderOf (s'' : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp only [pow_zero, orderOf_eq_one_iff] at hmeq
    exact hs''1 hmeq
  have h2 : 2 ∣ orderOf (s'' : G) := by
    rw [hmeq]
    exact dvd_pow_self 2 hm0
  exact even_iff_two_dvd.2 (h2.trans (Subgroup.orderOf_dvd_natCard _ hsN))

theorem exists_twoGroup_normalized_by_Z {b : G} {K Z : Subgroup G} (hZ3 : IsPGroup 3 Z)
    (hZK : Z ≤ K) (hKC : K ≤ Subgroup.centralizer ({b} : Set G))
    (hZc : ∀ z ∈ Z, ∀ k ∈ K, z * k * z⁻¹ * k⁻¹ ∈
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)))
    (hk : ∃ k ∈ K, k ∉ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ∧
      ∃ e : ℕ, orderOf k = 2 ^ e) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ Z ≤ Subgroup.normalizer (T : Set G) := by
  obtain ⟨k, hkK, hkN, e, he⟩ := hk
  have hkC : k ∈ Subgroup.centralizer ({b} : Set G) := hKC hkK
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set w : CBar 3 b := bar b hkC with hw
  let R : Subgroup G :=
    ((Subgroup.zpowers w).comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C))).map C.subtype
  have hRmem : ∀ y : G, y ∈ R ↔ ∃ hy : y ∈ C, bar b hy ∈ Subgroup.zpowers w := by
    intro y
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.2, hc⟩
    · rintro ⟨hy, h⟩
      exact ⟨⟨y, hy⟩, h, rfl⟩
  have hcommw : ∀ z ∈ Z, ∀ hz : z ∈ C, bar b hz * w = w * bar b hz := by
    intro z hz hzC
    have hn := hZc z hz k hkK
    obtain ⟨hnC, hn1⟩ := mem_nb_iff.1 hn
    have e1 : z * k = (z * k * z⁻¹ * k⁻¹) * (k * z) := by group
    have := bar_mul b hzC hkC
    rw [hw]
    rw [bar_mul b hzC hkC, wp7x_bar_congr b (mul_mem hzC hkC)
      (mul_mem hnC (mul_mem hkC hzC)) e1, ← bar_mul b hnC (mul_mem hkC hzC), hn1, one_mul,
      bar_mul b hkC hzC]
  have hZR : Z ≤ Subgroup.normalizer (R : Set G) := by
    have key : ∀ z ∈ Z, ∀ y ∈ R, z * y * z⁻¹ ∈ R := by
      intro z hz y hy
      obtain ⟨hyC, hyw⟩ := (hRmem y).1 hy
      have hzC : z ∈ C := hKC (hZK hz)
      refine (hRmem _).2 ⟨mul_mem (mul_mem hzC hyC) (inv_mem hzC), ?_⟩
      rw [← bar_mul b (mul_mem hzC hyC) (inv_mem hzC), ← bar_mul b hzC hyC, ← bar_inv b hzC]
      have hcz : Commute (bar b hzC) (bar b hyC) := by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hyw
        rw [← hj]
        exact ((show Commute (bar b hzC) w from hcommw z hz hzC)).zpow_right j
      rw [hcz.eq, mul_assoc, mul_inv_cancel, mul_one]
      exact hyw
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun hy => key z hz y hy, fun hy => by
      have := key z⁻¹ (inv_mem hz) _ hy
      simpa [mul_assoc] using this⟩
  have hkR : k ∈ R := (hRmem k).2 ⟨hkC, Subgroup.mem_zpowers w⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    simp only [pow_zero, orderOf_eq_one_iff] at he
    apply hkN
    rw [he]
    exact one_mem _
  have heven : Even (Nat.card R) := by
    refine even_iff_two_dvd.2 ?_
    have : 2 ∣ orderOf k := by
      rw [he]; exact dvd_pow_self 2 he0
    exact this.trans (Subgroup.orderOf_dvd_natCard R hkR)
  have hcop : ¬ 3 ∣ Nat.card R := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := R) 3 h3
    have hrord : orderOf (r : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hr
    obtain ⟨hrC, hrw⟩ := (hRmem r).1 r.2
    have hw2 : w ^ (2 ^ e) = 1 := by
      have : (⟨k, hkC⟩ : ↥C) ^ (2 ^ e) = 1 := by
        apply Subtype.ext
        have := pow_orderOf_eq_one k
        rw [he] at this
        exact this
      show (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨k, hkC⟩) ^ (2 ^ e) = 1
      rw [← map_pow, this, map_one]
    have h1 : (bar b hrC) ^ (2 ^ e) = 1 := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hrw
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw2, one_zpow]
    have h2 : (bar b hrC) ^ 3 = 1 := by
      show (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨(r : G), hrC⟩) ^ 3 = 1
      rw [← map_pow]
      have : (⟨(r : G), hrC⟩ : ↥C) ^ 3 = 1 := by
        apply Subtype.ext
        have := pow_orderOf_eq_one (r : G)
        rw [hrord] at this
        exact this
      rw [this, map_one]
    have hg := (pow_gcd_eq_one).2 ⟨h1, h2⟩
    have hcp : Nat.gcd (2 ^ e) 3 = 1 := Nat.Coprime.pow_left e (by norm_num : Nat.Coprime 2 3)
    rw [hcp, pow_one] at hg
    have hrN : (r : G) ∈ GLAPPrimeCoreOf 3 C := mem_nb_iff.2 ⟨hrC, hg⟩
    have := coprime_orderOf_of_mem_nb hrN
    rw [hrord] at this
    norm_num at this
  obtain ⟨T, hT, -, hT2, hZT⟩ := exists_twoGroup_normalized_of_coprime_even (p := 3)
    (by norm_num) (by norm_num) hZ3 hZR hcop heven
  exact ⟨T, hT, hT2, hZT⟩


theorem mem_barCenterAt_iff {b : G} {K : Subgroup G} {w : CBar 3 b} :
    w ∈ barCenterAt 3 b K ↔
      w ∈ barImageAt 3 b K ∧ ∀ v ∈ barImageAt 3 b K, v * w = w * v := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun v hv => ?_⟩
    have := Subgroup.mem_center_iff.1 hc ⟨v, hv⟩
    exact congrArg Subtype.val this
  · rintro ⟨hw, hc⟩
    refine ⟨⟨w, hw⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (hc g g.2)

theorem bar_comm_iff {b y z : G} (hy : y ∈ Subgroup.centralizer ({b} : Set G))
    (hz : z ∈ Subgroup.centralizer ({b} : Set G)) :
    bar b hy * bar b hz = bar b hz * bar b hy ↔
      y * z * y⁻¹ * z⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  have hyz : y * z * y⁻¹ * z⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
    mul_mem (mul_mem (mul_mem hy hz) (inv_mem hy)) (inv_mem hz)
  have h1 : bar b hyz = bar b hy * bar b hz * (bar b hy)⁻¹ * (bar b hz)⁻¹ := rfl
  rw [mem_nb_iff]
  constructor
  · intro h
    refine ⟨hyz, ?_⟩
    rw [h1, h]; group
  · rintro ⟨h, h2⟩
    have h3 : bar b h = bar b hyz := rfl
    rw [h3, h1] at h2
    have h5 : bar b hy * bar b hz * (bar b hy)⁻¹ = bar b hz := mul_inv_eq_one.1 h2
    exact mul_inv_eq_iff_eq_mul.1 h5

theorem bar_zpow (b : G) {y : G} (hy : y ∈ Subgroup.centralizer ({b} : Set G)) (i : ℤ) :
    bar b (zpow_mem hy i) = (bar b hy) ^ i := by
  unfold bar
  exact (map_zpow (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Subgroup.centralizer ({b} : Set G))))
    (⟨y, hy⟩ : ↥(Subgroup.centralizer ({b} : Set G))) i).symm


theorem orderOf_eq_three_of_mem {B : Subgroup G} (hB : IsElemAbelian 3 B) {x : G} (hx : x ∈ B)
    (hx1 : x ≠ 1) : orderOf x = 3 :=
  orderOf_eq_prime (hB.2 x hx) hx1

theorem B_le_cb {B : Subgroup G} {b : G} (hB : IsElemAbelian 3 B) (hbB : b ∈ B) :
    B ≤ Subgroup.centralizer ({b} : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hbB⟩ ⟨g, hg⟩)
  simpa using this.symm

theorem bClosure_le_cb {B L : Subgroup G} {b : G} (hB : IsElemAbelian 3 B) (hbB : b ∈ B)
    (hL : L ≤ Subgroup.centralizer ({b} : Set G)) :
    bClosure B L ≤ Subgroup.centralizer ({b} : Set G) := by
  refine iSup₂_le fun g hg => ?_
  have hgb : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.1 (B_le_cb hB hbB hg)
  rw [← gLBConj_centralizer_singleton_of_commute hgb]
  exact gLBConj_mono g hL

theorem comm_mem_nb_of_central {b x y : G} {K : Subgroup G} (hy : y ∈ K)
    (hyC : y ∈ Subgroup.centralizer ({b} : Set G)) (hx : x ∈ Subgroup.centralizer ({b} : Set G))
    (hxc : bar b hx ∈ barCenterAt 3 b K) :
    y * x * y⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  have h := (mem_barCenterAt_iff.1 hxc).2 (bar b hyC) (mem_barImageAt_iff.2 ⟨y, hyC, hy, rfl⟩)
  exact (bar_comm_iff hyC hx).1 h

@[expose] def Input11_2One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ (X B L : Subgroup G), IsElemAbelian p B → B ≤ X →
      GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → GLAPComponent p X L →
      ¬ B ≤ Subgroup.normalizer (L : Set G) →
      p = 3 ∧ (Subgroup.normalizer (L : Set G)).relIndex B = 3 ∧
        (IsLTwoOddPow (barOf 3 L) ∨
          (Nat.card (Subgroup.center ↥(barX 3 X (bClosure B L))) = 3 ∧
            (IsHatSix (barOf 3 L) ∨ IsHatSeven (barOf 3 L) ∨ IsHatMTwentyTwo (barOf 3 L) ∨
              IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L))) ∨
          (Nat.card (Subgroup.center ↥(barX 3 X (bClosure B L))) = 9 ∧
            IsSUThreeTwoPow (barOf 3 L) ∧
            Nat.card ↥((Subgroup.center ↥(barX 3 X (bClosure B L))).map
                (barX 3 X (bClosure B L)).subtype ⊓
              Subgroup.centralizer (barX 3 X B : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) = 3 ∧
            CFSG.Open.pRank 3 B <
              CFSG.Open.pRank 3
                ((barX 3 X B ⊓ Subgroup.centralizer
                    (barX 3 X (bClosure B L) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) ⊔
                  barX 3 X (bClosure B L))))


theorem exists_replacement (h25 : Lemma25Strong) {G : Type} [Group G] [Finite G] {m : ℕ}
    (hS : GLStanding G m 3) {B D : Subgroup G} {b : G} {L : Subgroup G}
    (hS24 : Lemma24Setup 3 B D b L) (hC : Lemma24Conclusion B D b L) :
    ∃ (x : G) (J : Subgroup G), Lemma24Setup 3 B D x J ∧ Lemma24Conclusion B D x J ∧
      x ∈ bClosure B J := by
  have hB : IsElemAbelian 3 B := hS24.isBOneMax.1.1
  have hbB : b ∈ B := hS24.mem
  have hL := hS24.isComp
  have hshape := hC.2.1
  have hLL : IsBConjugate B L L := ⟨1, B.one_mem, (gLBConj_one L).symm⟩
  obtain ⟨ℓ, hℓ, -, hne, hcen⟩ := exists_central_in_conj hB hbB hL hshape hLL
  obtain ⟨x, hx, hxB, hx1, hxc⟩ := exists_B_elem_of_central hS24 hC ⟨_, hcen, hne⟩
  have hord : orderOf x = 3 := orderOf_eq_three_of_mem hB hxB hx1
  have hLK : L ≤ bClosure B L := le_iSup₂_of_le 1 B.one_mem (by rw [gLBConj_one])
  have hcomm : ∀ ℓ' ∈ L, ℓ' * x * ℓ'⁻¹ * x⁻¹ ∈
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := fun ℓ' hℓ' =>
    comm_mem_nb_of_central (hLK hℓ') (hL.1 hℓ') hx hxc
  have hcommz : ⁅L, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
    rw [Subgroup.commutator_le]
    intro ℓ' hℓ' z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hzC : x ^ i ∈ Subgroup.centralizer ({b} : Set G) := zpow_mem hx i
    have h1 := (mem_barCenterAt_iff.1 hxc).2 (bar b (hL.1 hℓ'))
      (mem_barImageAt_iff.2 ⟨ℓ', hL.1 hℓ', hLK hℓ', rfl⟩)
    have h2 : bar b (hL.1 hℓ') * bar b hzC = bar b hzC * bar b (hL.1 hℓ') := by
      have e : bar b hzC = (bar b hx) ^ i := bar_zpow b hx i
      rw [e]
      exact (Commute.zpow_right (show Commute (bar b (hL.1 hℓ')) (bar b hx) from h1) i).eq
    exact (bar_comm_iff (hL.1 hℓ') hzC).1 h2
  have hxK : ∃ k ∈ bClosure B L, k⁻¹ * x ∈
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
    obtain ⟨y, hy, hyK, hyx⟩ := mem_barImageAt_iff.1 (mem_barCenterAt_iff.1 hxc).1
    exact ⟨y, hyK, (bar_eq_iff hy hx).1 hyx⟩
  have h25x := h25 G m hS B D b L hS24 L hLL x hx hord hcommz
  refine ⟨x, _, (h25x.1 hxB).1, (h25x.1 hxB).2, ?_⟩
  exact mem_bClosure_Jis hB hbB hxB hord hL hcomm hxK


theorem bar_pow (b : G) {y : G} (hy : y ∈ Subgroup.centralizer ({b} : Set G)) (i : ℕ) :
    bar b (pow_mem hy i) = (bar b hy) ^ i := by
  unfold bar
  exact (map_pow (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Subgroup.centralizer ({b} : Set G))))
    (⟨y, hy⟩ : ↥(Subgroup.centralizer ({b} : Set G))) i).symm

theorem exists_three_lift {b y : G} (hy : y ∈ Subgroup.centralizer ({b} : Set G))
    (h3 : (bar b hy) ^ 3 = 1) :
    ∃ (k : G) (hk : k ∈ Subgroup.centralizer ({b} : Set G)), k ∈ Subgroup.zpowers y ∧
      bar b hk = bar b hy ∧ k ^ 3 = 1 := by
  have hn : y ^ 3 ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
    rw [mem_nb_iff]
    exact ⟨pow_mem hy 3, by rw [bar_pow b hy 3, h3]⟩
  set m' := orderOf (y ^ 3) with hm'
  have hcop : Nat.Coprime 3 m' := coprime_orderOf_of_mem_nb hn
  have hm3 : ¬ 3 ∣ m' := fun h => by have := Nat.Coprime.eq_one_of_dvd hcop h; omega
  have hmm : (m' * m') % 3 = 1 := by
    have : m' % 3 = 1 ∨ m' % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  refine ⟨y ^ (m' * m'), pow_mem hy _, Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _, ?_, ?_⟩
  · rw [bar_pow b hy]
    obtain ⟨q, hq⟩ : ∃ q, m' * m' = 3 * q + 1 := ⟨m' * m' / 3, by omega⟩
    rw [hq, pow_succ, pow_mul, h3, one_pow, one_mul]
  · calc (y ^ (m' * m')) ^ 3 = (y ^ 3) ^ (m' * m') := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((y ^ 3) ^ m') ^ m' := by rw [pow_mul]
      _ = 1 := by rw [hm', pow_orderOf_eq_one, one_pow]

theorem commutator_le_nb_of_central {b x : G} {L K : Subgroup G} (hLK : L ≤ K)
    (hLC : L ≤ Subgroup.centralizer ({b} : Set G)) (hx : x ∈ Subgroup.centralizer ({b} : Set G))
    (hxc : bar b hx ∈ barCenterAt 3 b K) :
    ⁅L, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  rw [Subgroup.commutator_le]
  intro ℓ' hℓ' z hz
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hzC : x ^ i ∈ Subgroup.centralizer ({b} : Set G) := zpow_mem hx i
  have h1 := (mem_barCenterAt_iff.1 hxc).2 (bar b (hLC hℓ'))
    (mem_barImageAt_iff.2 ⟨ℓ', hLC hℓ', hLK hℓ', rfl⟩)
  have h2 : bar b (hLC hℓ') * bar b hzC = bar b hzC * bar b (hLC hℓ') := by
    have e : bar b hzC = (bar b hx) ^ i := bar_zpow b hx i
    rw [e]
    exact (Commute.zpow_right (show Commute (bar b (hLC hℓ')) (bar b hx) from h1) i).eq
  exact (bar_comm_iff (hLC hℓ') hzC).1 h2


theorem false_of_case_c (h25 : Lemma25Strong) {G : Type} [Group G] [Finite G] {m : ℕ}
    (hS : GLStanding G m 3) {B D : Subgroup G} {b : G} {L : Subgroup G}
    (hS24 : Lemma24Setup 3 B D b L) (hC : Lemma24Conclusion B D b L) (hbK : b ∈ bClosure B L)
    {ζ : CBar 3 b} (hζZ : ζ ∈ barCenterAt 3 b (bClosure B L))
    (hζ : ζ ∉ barImageAt 3 b (Subgroup.zpowers b))
    (hpr : CFSG.Open.pRank 3 B <
      CFSG.Open.pRank 3 ((barX 3 (Subgroup.centralizer ({b} : Set G)) B ⊓ Subgroup.centralizer
          (barX 3 (Subgroup.centralizer ({b} : Set G)) (bClosure B L) : Set (CBar 3 b))) ⊔
        barX 3 (Subgroup.centralizer ({b} : Set G)) (bClosure B L))) : False := by
  classical
  set K := bClosure B L with hK
  have hB : IsElemAbelian 3 B := hS24.isBOneMax.1.1
  have hbB : b ∈ B := hS24.mem
  have hb1 : b ≠ 1 := hS24.ne_one
  have hL := hS24.isComp
  have hshape := hC.2.1
  have hBC := B_le_cb hB hbB
  have hKC : K ≤ Subgroup.centralizer ({b} : Set G) := bClosure_le_cb hB hbB hL.1
  have hbC : b ∈ Subgroup.centralizer ({b} : Set G) := hBC hbB
  have hb3 : orderOf b = 3 := orderOf_eq_three_of_mem hB hbB hb1
  have hLK : L ≤ K := le_iSup₂_of_le 1 B.one_mem (by rw [gLBConj_one])
  have hLL : IsBConjugate B L L := ⟨1, B.one_mem, (gLBConj_one L).symm⟩
  have hbcen : bar b hbC ∈ barCenterAt 3 b K := by
    rw [mem_barCenterAt_iff]
    refine ⟨mem_barImageAt_iff.2 ⟨b, hbC, hbK, rfl⟩, fun v hv => ?_⟩
    obtain ⟨y, hy, -, rfl⟩ := mem_barImageAt_iff.1 hv
    refine (bar_comm_iff hy hbC).2 ?_
    have hyb : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    rw [hyb, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hζK : ζ ∈ barImageAt 3 b K := (mem_barCenterAt_iff.1 hζZ).1
  obtain ⟨k₀, hk₀C, hk₀K, hk₀⟩ := mem_barImageAt_iff.1 hζK
  have hζ3 : ζ ^ 3 = 1 := by
    have hmem : (⟨ζ, hζK⟩ : ↥(barImageAt 3 b K)) ∈ Subgroup.center ↥(barImageAt 3 b K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((mem_barCenterAt_iff.1 hζZ).2 g g.2)
    exact congrArg Subtype.val (hC.2.2.2.1.1.2 _ hmem)
  have hk₀3 : (bar b hk₀C) ^ 3 = 1 := by rw [hk₀]; exact hζ3
  obtain ⟨k, hkC, hkz, hkbar, hk3⟩ := exists_three_lift hk₀C hk₀3
  have hkK : k ∈ K := (Subgroup.zpowers_le.2 hk₀K) hkz
  have hkb : k * b = b * k := Subgroup.mem_centralizer_singleton_iff.1 hkC
  have hbarkζ : bar b hkC = ζ := hkbar.trans hk₀
  have hkb' : k ∉ Subgroup.zpowers b := fun h => hζ (mem_barImageAt_iff.2 ⟨k, hkC, h, hbarkζ⟩)
  have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  have hbel : IsElemAbelian 3 (Subgroup.zpowers b) := by
    have h0 : IsElemAbelian 3 (⊥ : Subgroup G) :=
      ⟨inferInstance, fun x hx => by rw [Subgroup.mem_bot.1 hx]; exact one_pow 3⟩
    simpa using isElemAbelian_sup_zpowers h0 hb3' (fun a ha => by
      rw [Subgroup.mem_bot.1 ha]; simp)
  set Z₀ : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers k with hZ₀
  have hcomm : ∀ h ∈ Subgroup.zpowers b, h * k = k * h := by
    intro h hh
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((Commute.zpow_left (show Commute b k from hkb.symm) i)).eq
  have hZ₀el : IsElemAbelian 3 Z₀ := isElemAbelian_sup_zpowers hbel hk3 hcomm
  have hZ₀card : Nat.card Z₀ = 9 := by
    rw [hZ₀, card_sup_zpowers_of_pow_three_eq_one hk3 hkb' hcomm, Nat.card_zpowers, hb3]
  have hbZ : b ∈ Z₀ := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hkZ : k ∈ Z₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers k)
  have hZ₀K : Z₀ ≤ K := sup_le (Subgroup.zpowers_le.2 hbK) (Subgroup.zpowers_le.2 hkK)
  have hZ₀C : Z₀ ≤ Subgroup.centralizer ({b} : Set G) := hZ₀K.trans hKC
  have hZ₀3 : IsPGroup 3 Z₀ := GL83.isPGroup_of_isElemAbelian hZ₀el
  have hZ₀ne : Z₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ₀card
    omega
  have hZ₀cen : ∀ z ∈ Z₀, ∃ hz : z ∈ Subgroup.centralizer ({b} : Set G),
      bar b hz ∈ barCenterAt 3 b K := by
    intro z hz
    rw [hZ₀, Subgroup.sup_eq_closure] at hz
    induction hz using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        refine ⟨zpow_mem hbC i, ?_⟩
        rw [bar_zpow b hbC i]
        exact zpow_mem hbcen i
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        refine ⟨zpow_mem hkC i, ?_⟩
        rw [bar_zpow b hkC i, hbarkζ]
        exact zpow_mem hζZ i
    | one =>
      exact ⟨one_mem _, by
        have : bar b (one_mem (Subgroup.centralizer ({b} : Set G))) = 1 := rfl
        rw [this]; exact one_mem _⟩
    | mul y z _ _ hy hz =>
      obtain ⟨hy, hyc⟩ := hy
      obtain ⟨hz, hzc⟩ := hz
      exact ⟨mul_mem hy hz, by rw [← bar_mul b hy hz]; exact mul_mem hyc hzc⟩
    | inv y _ hy =>
      obtain ⟨hy, hyc⟩ := hy
      exact ⟨inv_mem hy, by rw [← bar_inv b hy]; exact inv_mem hyc⟩
  have hZ₀comm : ∀ z ∈ Z₀, ∀ k' ∈ K, z * k' * z⁻¹ * k'⁻¹ ∈
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
    intro z hz k' hk'
    obtain ⟨hzC, hzc⟩ := hZ₀cen z hz
    have := comm_mem_nb_of_central hk' (hKC hk') hzC hzc
    have h2 := Subgroup.inv_mem _ this
    simpa [mul_assoc] using h2
  obtain ⟨k₂, hk₂L, hk₂N, e, hk₂e⟩ := exists_twoElement_of_shape hL hshape
  obtain ⟨T₀, hT₀ne, hT₀2, hT₀⟩ := exists_twoGroup_normalized_by_Z hZ₀3 hZ₀K hKC hZ₀comm
    ⟨k₂, hLK hk₂L, hk₂N, e, hk₂e⟩
  obtain ⟨T, ⟨hT2, hZT, hT₀T⟩, hTmax⟩ := Set.Finite.exists_maximal
    (Set.toFinite {T' : Subgroup G | IsPGroup 2 T' ∧ Z₀ ≤ Subgroup.normalizer (T' : Set G) ∧
      T₀ ≤ T'}) ⟨T₀, hT₀2, hT₀, le_rfl⟩
  have hTne : T ≠ ⊥ := fun h => hT₀ne (le_bot_iff.1 (h ▸ hT₀T))
  have hTmax' : ∀ T' : Subgroup G, IsPGroup 2 T' → Z₀ ≤ Subgroup.normalizer (T' : Set G) →
      T ≤ T' → T' = T := fun T' h2 hN hle =>
    le_antisymm (hTmax ⟨h2, hN, hT₀T.trans hle⟩ hle) hle
  obtain ⟨A, hAZ, hAidx, hAne⟩ := ((GL83.I_33_1_proved G hS.charTwo 3 Nat.prime_three
    (by norm_num) Z₀ T hZ₀ne hZ₀el hT2 hZT (Or.inl ⟨hTne, hTmax'⟩)).1) b hbZ hb1
  have hAcard : Nat.card A = 3 := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf Z₀)
    rw [hAidx, hZ₀card] at h1
    have h2 : Nat.card (A.subgroupOf Z₀) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ).toEquiv
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (by rw [hAcard])
  set x : G := (x' : G) with hxdef
  have hxA : x ∈ A := x'.2
  have hxord : orderOf x = 3 := by rw [hxdef, Subgroup.orderOf_coe]; exact hx'
  have hxZ : x ∈ Z₀ := hAZ hxA
  have hxC : x ∈ Subgroup.centralizer ({b} : Set G) := hZ₀C hxZ
  obtain ⟨hxC', hxcen'⟩ := hZ₀cen x hxZ
  have hxcen : bar b hxC ∈ barCenterAt 3 b K := hxcen'
  have hcommz := commutator_le_nb_of_central hLK hL.1 hxC hxcen
  have hle : barImageAt 3 b (Subgroup.closure {x, b}) ≤ barCenterAt 3 b K := by
    intro w hw
    obtain ⟨y, hy, hyc, rfl⟩ := mem_barImageAt_iff.1 hw
    have hyZ : y ∈ Z₀ := ((Subgroup.closure_le _).2 (by
      intro u hu
      rcases hu with rfl | hu
      · exact hxZ
      · rw [Set.mem_singleton_iff.1 hu]; exact hbZ)) hyc
    obtain ⟨hy', h⟩ := hZ₀cen y hyZ
    exact h
  have hbO : b ∈ oPrimePOf 3 (Subgroup.centralizer ({x} : Set G)) :=
    ((h25 G m hS B D b L hS24 L hLL x hxC hxord hcommz).2 (Or.inl hle))
  have hex : ∃ b' ∈ Subgroup.zpowers b, ∃ c ∈ T ⊓ Subgroup.centralizer (A : Set G),
      b' * c * b'⁻¹ * c⁻¹ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hAne
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro b' hb' c hc
    rw [Subgroup.mem_bot, commutatorElement_def]
    exact hcon b' hb' c hc
  obtain ⟨b', hb'z, c, hcT, hbc⟩ := hex
  have hb'O : b' ∈ oPrimePOf 3 (Subgroup.centralizer ({x} : Set G)) :=
    (Subgroup.zpowers_le.2 hbO) hb'z
  have hb'T : b' ∈ Subgroup.normalizer (T : Set G) :=
    hZT ((Subgroup.zpowers_le.2 hbZ) hb'z)
  have hcx : c ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hcT.2 x hxA).symm
  have hev := even_oPrime_of_commutator hb'O hcx hT2 hb'T hcT.1 hbc
  have hm := pRank_le_of_even_oPrime hev
  have hxK : x ∈ K := hZ₀K hxZ
  have hxH : bar b hxC ∈ ((barX 3 (Subgroup.centralizer ({b} : Set G)) B ⊓ Subgroup.centralizer
          (barX 3 (Subgroup.centralizer ({b} : Set G)) K : Set (CBar 3 b))) ⊔
        barX 3 (Subgroup.centralizer ({b} : Set G)) K) :=
    Subgroup.mem_sup_right (mem_barImageAt_iff.2 ⟨x, hxC, hxK, rfl⟩)
  have hHc : ∀ w ∈ ((barX 3 (Subgroup.centralizer ({b} : Set G)) B ⊓ Subgroup.centralizer
          (barX 3 (Subgroup.centralizer ({b} : Set G)) K : Set (CBar 3 b))) ⊔
        barX 3 (Subgroup.centralizer ({b} : Set G)) K), w * bar b hxC = bar b hxC * w := by
    have hle2 : ((barX 3 (Subgroup.centralizer ({b} : Set G)) B ⊓ Subgroup.centralizer
          (barX 3 (Subgroup.centralizer ({b} : Set G)) K : Set (CBar 3 b))) ⊔
        barX 3 (Subgroup.centralizer ({b} : Set G)) K) ≤
          Subgroup.centralizer ({bar b hxC} : Set (CBar 3 b)) := by
      refine sup_le ?_ ?_
      · refine inf_le_right.trans (Subgroup.centralizer_le ?_)
        intro w hw
        rw [Set.mem_singleton_iff.1 hw]
        exact mem_barImageAt_iff.2 ⟨x, hxC, hxK, rfl⟩
      · intro v hv
        exact Subgroup.mem_centralizer_singleton_iff.2 ((mem_barCenterAt_iff.1 hxcen).2 v hv)
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle2 hw)
  have hrk := pRank_le_of_central_bar hxC hxord hxH hHc hm
  have hBrk : CFSG.Open.pRank 3 B = GLATwoLocalRank 3 G :=
    pRank_eq_of_card Nat.prime_three hB hS24.isBOneMax.1.2.1
  omega


theorem center_eq_zpowers (h25 : Lemma25Strong) (hIn : Input11_2One) {G : Type} [Group G] [Finite G]
    {m : ℕ} (hS : GLStanding G m 3) {B D : Subgroup G} {b : G} {L : Subgroup G}
    (hS24 : Lemma24Setup 3 B D b L) (hC : Lemma24Conclusion B D b L) (hbK : b ∈ bClosure B L) :
    barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L) := by
  classical
  set K := bClosure B L with hK
  have hB : IsElemAbelian 3 B := hS24.isBOneMax.1.1
  have hbB : b ∈ B := hS24.mem
  have hb1 : b ≠ 1 := hS24.ne_one
  have hL := hS24.isComp
  have hshape := hC.2.1
  have hBC := B_le_cb hB hbB
  have hKC : K ≤ Subgroup.centralizer ({b} : Set G) := bClosure_le_cb hB hbB hL.1
  have hbC : b ∈ Subgroup.centralizer ({b} : Set G) := hBC hbB
  have hb3 : orderOf b = 3 := orderOf_eq_three_of_mem hB hbB hb1
  have hbcen : bar b hbC ∈ barCenterAt 3 b K := by
    rw [mem_barCenterAt_iff]
    refine ⟨mem_barImageAt_iff.2 ⟨b, hbC, hbK, rfl⟩, fun v hv => ?_⟩
    obtain ⟨y, hy, -, rfl⟩ := mem_barImageAt_iff.1 hv
    refine (bar_comm_iff hy hbC).2 ?_
    have hyb : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    rw [hyb, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  refine le_antisymm ?_ ?_
  · intro w hw
    obtain ⟨y, hy, hyz, rfl⟩ := mem_barImageAt_iff.1 hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyz
    have : bar b hy = (bar b hbC) ^ i := bar_zpow b hbC i
    rw [this]
    exact zpow_mem hbcen i
  · intro ζ hζZ
    by_contra hζ
    have hBrk : CFSG.Open.pRank 3 B = GLATwoLocalRank 3 G :=
      pRank_eq_of_card Nat.prime_three hB hS24.isBOneMax.1.2.1
    have hrank : GLATwoLocalRank 3 ↥(Subgroup.centralizer ({b} : Set G)) ≤ CFSG.Open.pRank 3 B :=
      (glaTwoLocalRank_subgroup_le Nat.prime_three _).trans hBrk.ge
    have hnotN : ¬ B ≤ Subgroup.normalizer (L : Set G) := by
      intro h
      have h1 := hC.1
      rw [Subgroup.relIndex_eq_one.2 h] at h1
      omega
    obtain ⟨-, -, hcase⟩ := hIn G m 3 hS (Subgroup.centralizer ({b} : Set G)) B L hB hBC hrank
      hL hnotN
    rcases hcase with ha | ⟨hcard, -⟩ | ⟨-, -, -, hpr⟩
    · obtain ⟨z, hz1, hzc⟩ := exists_central_ne_one_of_exc hshape
      exact hz1 (central_eq_one_of_isLTwoOddPow ha z hzc)
    ·
      have hbb1 : bar b hbC ≠ 1 := by
        intro h
        have := coprime_orderOf_of_mem_nb (mem_nb_iff.2 ⟨hbC, h⟩)
        rw [hb3] at this
        exact absurd this (by norm_num)
      have hbb3 : orderOf (bar b hbC) = 3 := by
        refine orderOf_eq_prime ?_ hbb1
        rw [← bar_pow b hbC 3]
        have : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
        have h1 : bar b (pow_mem hbC 3) = bar b (one_mem (Subgroup.centralizer ({b} : Set G))) := by
          congr 1
        rw [h1]; rfl
      have hle : Subgroup.zpowers (bar b hbC) ≤ barCenterAt 3 b K := Subgroup.zpowers_le.2 hbcen
      have hcZ : Nat.card (barCenterAt 3 b K) = 3 := by
        unfold barCenterAt
        rw [Subgroup.card_map_of_injective (barImageAt 3 b K).subtype_injective]
        exact hcard
      have heq : Subgroup.zpowers (bar b hbC) = barCenterAt 3 b K :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcZ, Nat.card_zpowers, hbb3])
      rw [← heq] at hζZ
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hζZ
      exact hζ (mem_barImageAt_iff.2 ⟨b ^ i, zpow_mem hbC i, Subgroup.zpow_mem _
        (Subgroup.mem_zpowers b) i, bar_zpow b hbC i⟩)
    · exact false_of_case_c h25 hS hS24 hC hbK hζZ hζ hpr


end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma26Ns

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma26Ns

theorem lemma26plus_of_inputs (h24 : Lemma24) (h25 : Lemma25Strong)
    (h112 : Lemma26Ns.Input11_2One) : Lemma26Plus := by
  intro G _ _ m hS B hB hnot
  have hB1 : IsBOneMax 3 B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (le_refl 3) hB
  have hex : ∃ D : Subgroup G, IsEkIn 3 2 B D ∧ ∃ b ∈ B, b ≠ 1 ∧
      ¬ delta2At 3 B D b ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
    by_contra hcon
    push Not at hcon
    exact hnot fun D hD b hb hb1 => hcon D hD b hb hb1
  obtain ⟨D, hD, b, hb, hb1, hX⟩ := hex
  obtain ⟨-, ⟨L, hL, hnc⟩, hall⟩ := h24 G m 3 hS B hB1 hnot D hD b hb hb1 hX
  have hS24 : Lemma24Setup 3 B D b L := ⟨hB1, hD, hb, hb1, hX, hL, hnc⟩
  have hC := hall L hS24
  obtain ⟨x, J, hSx, hCx, hxJ⟩ := exists_replacement h25 hS hS24 hC
  have hz := center_eq_zpowers h25 h112 hS hSx hCx hxJ
  refine ⟨D, x, J, hSx, hCx, hxJ, hz, ?_⟩
  intro Li hLi
  exact mem_of_zpowers_eq_center hSx.isBOneMax.1.1 hSx.mem hSx.isComp hCx.2.1 hLi hz

theorem lemma26_of_plus (h : Lemma26Plus) : Lemma26 := by
  intro G _ _ m hS B hB hnot
  obtain ⟨D, b, L, h1, h2, h3, h4, -⟩ := h G m hS B hB hnot
  exact ⟨D, b, L, h1, h2, h3, h4⟩

end CFSG.HardMathSupport.Solomon.LocalBalance
