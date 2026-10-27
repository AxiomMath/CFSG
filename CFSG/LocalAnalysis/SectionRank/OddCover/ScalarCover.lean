module

public import CFSG.LocalAnalysis.SectionRank.OddCover.ThreeRank
public import CFSG.LocalAnalysis.SectionRank.CatalogStep
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Linear
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Unitary

public section

namespace CFSG.SectionRank.OddCover

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {K : Type} [Field K]

theorem unitary_of_mem_statedSU [Finite K] {p f n : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) {x : GL (Fin n) K} (hx : x ∈ StatedSU n (p ^ f) K) :
    ((x : Matrix (Fin n) (Fin n) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← SUid_eq_statedSU hK n] at hx
  have h := hx.2
  simp only [conjTr] at h
  convert h using 3
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, unitaryInvolution_apply]

theorem det_eq_one_of_linUni [Finite K] {p f n : ℕ} {H : Subgroup (GL (Fin n) K)}
    (hH : (Nat.card K = p ^ f ∧ H = StatedSL n K) ∨
      (Nat.card K = (p ^ f) ^ 2 ∧ H = StatedSU n (p ^ f) K)) {x : GL (Fin n) K} (hx : x ∈ H) :
    (x : Matrix (Fin n) (Fin n) K).det = 1 := by
  rcases hH with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact det_of_mem_statedSL hx
  · exact det_eq_one_of_mem_statedSU hx

section Torus

variable {r : ℕ}

@[expose] def sumZeroVec {m : ℕ} (u : Fin m → ZMod r) : Fin (m + 2) → ZMod r :=
  Fin.snoc (Fin.snoc u 0 : Fin (m + 1) → ZMod r) (-(∑ i, u i))

theorem sumZeroVec_add {m : ℕ} (u u' : Fin m → ZMod r) :
    sumZeroVec (u + u') = sumZeroVec u + sumZeroVec u' := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [sumZeroVec, Fin.snoc_last, Pi.add_apply, Finset.sum_add_distrib, neg_add]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [sumZeroVec]
    · simp [sumZeroVec]

theorem sumZeroVec_zero {m : ℕ} : sumZeroVec (0 : Fin m → ZMod r) = 0 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [sumZeroVec]
  · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [sumZeroVec]

theorem sum_sumZeroVec {m : ℕ} (u : Fin m → ZMod r) : ∑ i, sumZeroVec u i = 0 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp [sumZeroVec]

@[expose] def sumZeroVec' {m : ℕ} (u : Fin m → ZMod r) : Fin (m + 1) → ZMod r :=
  Fin.snoc u (-(∑ i, u i))

theorem sumZeroVec'_add {m : ℕ} (u u' : Fin m → ZMod r) :
    sumZeroVec' (u + u') = sumZeroVec' u + sumZeroVec' u' := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [sumZeroVec', Fin.snoc_last, Pi.add_apply, Finset.sum_add_distrib, neg_add]
  · simp [sumZeroVec']

theorem sumZeroVec'_zero {m : ℕ} : sumZeroVec' (0 : Fin m → ZMod r) = 0 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [sumZeroVec']

theorem sum_sumZeroVec' {m : ℕ} (u : Fin m → ZMod r) : ∑ i, sumZeroVec' u i = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp [sumZeroVec']

variable [NeZero r] {n : ℕ}

@[expose] def zetaDiag (ζ : Kˣ) (v : Fin n → ZMod r) : Matrix (Fin n) (Fin n) K :=
  diagonal fun i => ((ζ ^ (v i).val : Kˣ) : K)

theorem zetaDiag_add {ζ : Kˣ} (hζ : ζ ^ r = 1) (v w : Fin n → ZMod r) :
    zetaDiag ζ (v + w) = zetaDiag ζ v * zetaDiag ζ w := by
  rw [zetaDiag, zetaDiag, zetaDiag, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add, Units.val_mul]

omit [NeZero r] in
theorem zetaDiag_zero (ζ : Kˣ) : zetaDiag ζ (0 : Fin n → ZMod r) = 1 := by
  simp [zetaDiag]

theorem prod_zeta_eq_one {ζ : Kˣ} (hζ : ζ ^ r = 1) {v : Fin n → ZMod r} (hv : ∑ i, v i = 0) :
    ∏ i, ζ ^ (v i).val = 1 := by
  rw [Finset.prod_pow_eq_pow_sum]
  have h : ((∑ i, (v i).val : ℕ) : ZMod r) = 0 := by
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
    exact hv
  rw [ZMod.natCast_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  rw [hk, pow_mul, hζ, one_pow]

end Torus

section TorusRank

variable {r : ℕ} [NeZero r]

@[expose] noncomputable def torusWit {m n : ℕ} (ζ : Kˣ) (hζ : ζ ^ r = 1)
    (v : (Fin m → ZMod r) →+ (Fin n → ZMod r)) :
    Multiplicative (Fin m → ZMod r) →* GL (Fin n) K where
  toFun u := diagHom n fun i => ζ ^ (v u.toAdd i).val
  map_one' := by
    rw [← map_one (diagHom (K := K) n)]
    congr 1
    funext i
    simp
  map_mul' u u' := by
    rw [← map_mul]
    congr 1
    funext i
    rw [toAdd_mul, map_add, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add]
    rfl

theorem torusWit_apply {m n : ℕ} (ζ : Kˣ) (hζ : ζ ^ r = 1)
    (v : (Fin m → ZMod r) →+ (Fin n → ZMod r)) (u : Multiplicative (Fin m → ZMod r)) :
    torusWit ζ hζ v u = diagHom n fun i => ζ ^ (v u.toAdd i).val :=
  rfl

@[expose] def sumZeroHom (m : ℕ) : (Fin m → ZMod r) →+ (Fin (m + 2) → ZMod r) where
  toFun := sumZeroVec
  map_zero' := sumZeroVec_zero
  map_add' := sumZeroVec_add

@[expose] def sumZeroHom' (m : ℕ) : (Fin m → ZMod r) →+ (Fin (m + 1) → ZMod r) where
  toFun := sumZeroVec'
  map_zero' := sumZeroVec'_zero
  map_add' := sumZeroVec'_add

theorem det_torusWit {m n : ℕ} {ζ : Kˣ} (hζ : ζ ^ r = 1)
    (v : (Fin m → ZMod r) →+ (Fin n → ZMod r)) (hv : ∀ u, ∑ i, v u i = 0)
    (u : Multiplicative (Fin m → ZMod r)) :
    ((torusWit ζ hζ v u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [torusWit_apply, det_diagHom, ← Units.coe_prod, prod_zeta_eq_one hζ (hv _), Units.val_one]

theorem torusWit_mem_SL {m n : ℕ} {ζ : Kˣ} (hζ : ζ ^ r = 1)
    (v : (Fin m → ZMod r) →+ (Fin n → ZMod r)) (hv : ∀ u, ∑ i, v u i = 0)
    (u : Multiplicative (Fin m → ZMod r)) : torusWit ζ hζ v u ∈ StatedSL n K :=
  Subgroup.subset_closure (det_torusWit hζ v hv u)

theorem torusWit_mem_SU {m n q : ℕ} (hq : q ≠ 0) {ζ : Kˣ} (hζ : ζ ^ r = 1)
    (hζu : ζ ^ (q + 1) = 1) (v : (Fin m → ZMod r) →+ (Fin n → ZMod r))
    (hv : ∀ u, ∑ i, v u i = 0) (u : Multiplicative (Fin m → ZMod r)) :
    torusWit ζ hζ v u ∈ StatedSU n q K := by
  refine Subgroup.subset_closure ⟨det_torusWit hζ v hv u, ?_⟩
  rw [torusWit_apply, coe_diagHom, Matrix.diagonal_map (by simp [zero_pow hq]),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← pow_succ, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hζu, one_pow,
    Units.val_one]

theorem eq_one_of_torusWit_scalar {m n : ℕ} {ζ : Kˣ} (hζ : ζ ^ r = 1) (hζr : orderOf ζ = r)
    (v : (Fin m → ZMod r) →+ (Fin n → ZMod r)) (j : Fin n) (hj : ∀ u, v u j = 0)
    (hinj : ∀ u, (∀ i, v u i = 0) → u = 0) (u : Multiplicative (Fin m → ZMod r)) {c : Kˣ}
    (hc : torusWit ζ hζ v u = Matrix.GeneralLinearGroup.scalar (Fin n) c) : u = 1 := by
  have hc' : (fun i => ζ ^ (v u.toAdd i).val) = fun _ => c := by
    apply diagHom_injective n
    rw [← torusWit_apply ζ hζ v u, hc]
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, coe_diagHom]
    rfl
  have hc1 : c = 1 := by
    have := congrFun hc' j
    rw [hj, ZMod.val_zero, pow_zero] at this
    exact this.symm
  have hall : ∀ i, v u.toAdd i = 0 := by
    intro i
    have h := congrFun hc' i
    rw [hc1] at h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hζr] at hdvd
    exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _))
  have h0 := hinj _ hall
  rw [← ofAdd_toAdd u, h0, ofAdd_zero]

theorem torusWit_injective {m n : ℕ} {ζ : Kˣ} (hζ : ζ ^ r = 1) (hζr : orderOf ζ = r)
    (v : (Fin m → ZMod r) →+ (Fin n → ZMod r)) (hinj : ∀ u, (∀ i, v u i = 0) → u = 0) :
    Function.Injective (torusWit (K := K) ζ hζ v) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro u hu
  rw [MonoidHom.mem_ker, torusWit_apply, ← map_one (diagHom (K := K) n)] at hu
  have hc' := diagHom_injective n hu
  have hall : ∀ i, v u.toAdd i = 0 := by
    intro i
    have h := congrFun hc' i
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hζr] at hdvd
    exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _))
  have h0 := hinj _ hall
  rw [Subgroup.mem_bot, ← ofAdd_toAdd u, h0, ofAdd_zero]

theorem exists_zeta [Finite K] {r : ℕ} [Fact r.Prime] (hr : r ∣ Nat.card K - 1) :
    ∃ ζ : Kˣ, orderOf ζ = r := by
  rw [← card_units_eq] at hr
  exact exists_prime_orderOf_dvd_card' r hr

theorem sq_sub_one_eq {q : ℕ} (hq : 1 ≤ q) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  zify [hq, Nat.one_le_pow 2 _ hq]
  ring

omit [NeZero r] in
theorem multiplicative_zmod_pow_eq_one {k : ℕ} (a : Multiplicative (Fin k → ZMod r)) :
    a ^ r = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_pow, Pi.smul_apply, toAdd_one, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self,
    zero_mul]

omit [NeZero r] in
theorem card_multiplicative_zmod (k : ℕ) :
    Nat.card (Multiplicative (Fin k → ZMod r)) = r ^ k := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem scalar_quotient_diagonal_torus_rank [Finite K] {p f n r : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    [hr : Fact r.Prime] (_hr2 : r ≠ 2) {H : Subgroup (GL (Fin n) K)}
    (hH : (Nat.card K = p ^ f ∧ H = StatedSL n K ∧ r ∣ p ^ f - 1) ∨
      (Nat.card K = (p ^ f) ^ 2 ∧ H = StatedSU n (p ^ f) K ∧ r ∣ p ^ f + 1))
    (C : Subgroup H) [C.Normal] (hC : C ≤ (StatedScalars (Fin n) K).subgroupOf H) :
    n - 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (H ⧸ C)) ∧
      (¬ r ∣ Nat.card C → n - 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup (H ⧸ C))) := by
  have hrp := hr.out
  have : NeZero r := ⟨hrp.ne_zero⟩
  obtain ⟨ζ, hζr, hmemH⟩ : ∃ ζ : Kˣ, orderOf ζ = r ∧ ∀ (hζ : ζ ^ r = 1) {m : ℕ}
      (v : (Fin m → ZMod r) →+ (Fin n → ZMod r)), (∀ u, ∑ i, v u i = 0) →
        ∀ u, torusWit ζ hζ v u ∈ H := by
    rcases hH with ⟨hK, rfl, hrq⟩ | ⟨hK, rfl, hrq⟩
    · obtain ⟨ζ, hζ⟩ := exists_zeta (K := K) (r := r) (by rw [hK]; exact hrq)
      exact ⟨ζ, hζ, fun hζ' m v hv u => torusWit_mem_SL hζ' v hv u⟩
    · have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
      obtain ⟨ζ, hζ⟩ := exists_zeta (K := K) (r := r)
        (by rw [hK, sq_sub_one_eq hq]; exact Dvd.dvd.mul_right hrq _)
      have hζu : ζ ^ (p ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hrq)
      exact ⟨ζ, hζ, fun hζ' m v hv u => torusWit_mem_SU (by positivity) hζ' hζu v hv u⟩
  have hζ : ζ ^ r = 1 := by rw [← hζr]; exact pow_orderOf_eq_one ζ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  refine ⟨?_, fun hrC => ?_⟩
  ·
    let φ : Multiplicative (Fin m → ZMod r) →* H ⧸ C := (QuotientGroup.mk' C).comp
      ((torusWit ζ hζ (sumZeroHom m)).codRestrict H (hmemH hζ _ sum_sumZeroVec))
    have hφ : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hu
      obtain ⟨c, hc⟩ := hC hu
      refine Subgroup.mem_bot.2 (eq_one_of_torusWit_scalar hζ hζr (sumZeroHom m)
        (Fin.castSucc (Fin.last m)) (fun u => ?_) (fun u hu0 => ?_) u hc.symm)
      · simp [sumZeroHom, sumZeroVec]
      · funext i
        have := hu0 (Fin.castSucc (Fin.castSucc i))
        simpa [sumZeroHom, sumZeroVec] using this
    have := le_pRank_of_injective hrp.one_lt (fun a b => mul_comm a b)
      multiplicative_zmod_pow_eq_one (card_multiplicative_zmod m) φ hφ le_top
    simpa using this
  ·
    let φ : Multiplicative (Fin (m + 1) → ZMod r) →* H ⧸ C := (QuotientGroup.mk' C).comp
      ((torusWit ζ hζ (sumZeroHom' (m + 1))).codRestrict H (hmemH hζ _ sum_sumZeroVec'))
    have hφ : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hu
      set y := (torusWit ζ hζ (sumZeroHom' (m + 1))).codRestrict H
        (hmemH hζ _ sum_sumZeroVec') u with hy
      have hyr : y ^ r = 1 := by
        rw [hy, ← map_pow, multiplicative_zmod_pow_eq_one, map_one]
      have hyC : orderOf (⟨y, hu⟩ : C) ∣ Nat.card C := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hyC
      have hyo : orderOf y ∣ r := orderOf_dvd_of_pow_eq_one hyr
      have hcop : Nat.Coprime r (Nat.card C) := (Nat.Prime.coprime_iff_not_dvd hrp).2 hrC
      have hy1 : y = 1 := orderOf_eq_one_iff.1
        (Nat.eq_one_of_dvd_coprimes hcop hyo hyC)
      have hu1 : torusWit ζ hζ (sumZeroHom' (m + 1)) u = 1 := congrArg Subtype.val hy1
      rw [← map_one (torusWit ζ hζ (sumZeroHom' (m + 1)))] at hu1
      refine Subgroup.mem_bot.2 (torusWit_injective hζ hζr _ (fun u hu0 => ?_) hu1)
      funext i
      have := hu0 (Fin.castSucc i)
      simpa [sumZeroHom', sumZeroVec'] using this
    have := le_pRank_of_injective hrp.one_lt (fun a b => mul_comm a b)
      multiplicative_zmod_pow_eq_one (card_multiplicative_zmod (m + 1)) φ hφ le_top
    simpa using this

end TorusRank

section Cover

theorem ker_mk'_comp_eq {H L : Type*} [Group H] [Group L] {D : Subgroup H} {π : H →* L}
    (hker : π.ker ≤ D) (hDZ : D.map π = Subgroup.center L) :
    ((QuotientGroup.mk' (Subgroup.center L)).comp π).ker = D := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    ← hDZ, Subgroup.mem_map]
  constructor
  · rintro ⟨d, hd, hdx⟩
    have hk : d⁻¹ * x ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
    rw [show x = d * (d⁻¹ * x) by group]
    exact D.mul_mem hd (hker hk)
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem catalogStepConclusion_of_scalar_cover {n p e : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    {H : Type} [Group H] [Finite H] (D : Subgroup H) [D.Normal] (hDn : Nat.card D ∣ n)
    (hDe : Nat.card D ∣ e)
    (h4 : p ≠ 2 → 4 ≤ n → 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ D)))
    (htor : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ e → ∀ (C : Subgroup H) [C.Normal], C ≤ D →
      n - 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (H ⧸ C)))
    (h3 : n = 3 → Nat.card D = 3 → CFSG.Open.pRank 3 (⊤ : Subgroup (H ⧸ D)) ≤ 2)
    {L : Type} [Group L] [Finite L] (hSQT : IsStronglyQuasithin L)
    (hodd : Odd (Nat.card (Subgroup.center L))) (π : H →* L) (hπ : Function.Surjective π)
    (hker : π.ker ≤ D) (hDZ : D.map π = Subgroup.center L) : CatalogStepConclusion L := by
  have hSQT' := isStronglyQuasithin_iff.1 hSQT
  set ψ := (QuotientGroup.mk' (Subgroup.center L)).comp π
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hπ
  let eHD : H ⧸ D ≃* L ⧸ Subgroup.center L :=
    (QuotientGroup.quotientMulEquivOfEq (ker_mk'_comp_eq hker hDZ).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  let eL : L ≃* H ⧸ π.ker := (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm
  have hrankHD : ∀ r : ℕ, r.Prime → CFSG.Open.pRank r (⊤ : Subgroup (H ⧸ D)) =
      CFSG.Open.pRank r (⊤ : Subgroup (L ⧸ Subgroup.center L)) := fun r hr =>
    pRank_top_eq_of_mulEquiv hr.one_lt eHD
  have hrankL : ∀ r : ℕ, r.Prime → CFSG.Open.pRank r (⊤ : Subgroup L) =
      CFSG.Open.pRank r (⊤ : Subgroup (H ⧸ π.ker)) := fun r hr =>
    pRank_top_eq_of_mulEquiv hr.one_lt eL
  have hZD : Nat.card (Subgroup.center L) ∣ Nat.card D := hDZ ▸ Subgroup.card_map_dvd D π
  have hnot4 : ¬ (p ≠ 2 ∧ 4 ≤ n) := by
    rintro ⟨hp2, hn4⟩
    have : Fact p.Prime := ⟨hp⟩
    have h1 := h4 hp2 hn4
    have h2 := pRank_quotient_le_three hp2 (hSQT' p hp hp2) (Subgroup.center L) le_rfl
    rw [hrankHD p hp] at h1
    omega
  have hZ : Nat.card (Subgroup.center L) = 1 ∨ (Nat.card (Subgroup.center L) = 3 ∧ n = 3) := by
    by_cases hZ1 : Nat.card (Subgroup.center L) = 1
    · exact Or.inl hZ1
    right
    obtain ⟨r, hr, hrZ⟩ := Nat.exists_prime_and_dvd hZ1
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrZ)
    have hrn : r ∣ n := (hrZ.trans hZD).trans hDn
    have hre : r ∣ e := (hrZ.trans hZD).trans hDe
    have hn5 : n ≤ 4 := by
      by_contra hn5
      have : Fact r.Prime := ⟨hr⟩
      have h1 := htor r hr hr2 hre π.ker hker
      rw [← hrankL r hr] at h1
      have h2 := hSQT' r hr hr2
      omega
    have hZn : Nat.card (Subgroup.center L) ∣ n := hZD.trans hDn
    interval_cases n
    ·
      exfalso
      rcases (Nat.dvd_prime Nat.prime_two).1 hZn with h | h
      · exact hZ1 h
      · rw [h] at hodd; exact (by decide : ¬ Odd 2) hodd
    ·
      rcases (Nat.dvd_prime Nat.prime_three).1 hZn with h | h
      · exact absurd h hZ1
      · exact ⟨h, rfl⟩
    ·
      exfalso
      have h4' : Nat.card (Subgroup.center L) ∣ 4 := hZn
      have hle := Nat.le_of_dvd (by norm_num) h4'
      obtain ⟨k, hk⟩ := hodd
      interval_cases h : Nat.card (Subgroup.center L) <;> omega
  rcases hZ with hZ1 | ⟨hZ3, rfl⟩
  ·
    have hbot : Subgroup.center L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
    exact catalogStepConclusion_of hSQT (Or.inl hZ1)
      (isStronglyQuasithin_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot) hSQT)
  ·
    have hD3 : Nat.card D = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hDn with h | h
      · rw [h, hZ3] at hZD; exact absurd hZD (by decide)
      · exact h
    refine catalogStepConclusion_of hSQT (Or.inr hZ3) ?_
    rw [isStronglyQuasithin_iff]
    intro r hr hr2
    have : Fact r.Prime := ⟨hr⟩
    by_cases hr3 : r = 3
    · subst hr3
      rw [← hrankHD 3 hr]
      exact h3 rfl hD3
    · rw [pRank_quotient_eq (Subgroup.center L) (by
        rw [hZ3]
        exact fun hd => hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hd))]
      exact hSQT' r hr hr2

end Cover

section Classical

variable {n : ℕ}

theorem exists_scalar_of_mem_scalars {H : Subgroup (GL (Fin n) K)} {x : H}
    (hx : x ∈ (StatedScalars (Fin n) K).subgroupOf H) :
    ∃ c : Kˣ, (x : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, hc.symm⟩

theorem scalar_injective (hn : 1 ≤ n) :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin n) (R := K)) := by
  intro c d h
  have := congrFun (congrFun (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h)
    ⟨0, hn⟩) ⟨0, hn⟩
  simpa [GeneralLinearGroup.coe_scalar] using Units.ext this

theorem isCyclic_scalars [Finite K] (hn : 1 ≤ n) (H : Subgroup (GL (Fin n) K)) :
    IsCyclic ((StatedScalars (Fin n) K).subgroupOf H) := by
  set D := (StatedScalars (Fin n) K).subgroupOf H
  choose c hc using fun x : D => exists_scalar_of_mem_scalars x.2
  let φ : D →* K :=
    { toFun := fun x => (c x : K)
      map_one' := by
        have h := hc 1
        rw [Subgroup.coe_one, Subgroup.coe_one] at h
        have := scalar_injective hn (h.symm.trans (map_one _).symm)
        rw [this, Units.val_one]
      map_mul' := fun x y => by
        have h := hc (x * y)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hc x, hc y, ← map_mul] at h
        rw [scalar_injective hn h.symm, Units.val_mul] }
  refine isCyclic_of_injective_ringHom φ fun x y hxy => ?_
  have h' : c x = c y := Units.ext hxy
  apply Subtype.ext
  apply Subtype.ext
  rw [hc x, hc y, h']

theorem card_scalars_dvd [Finite K] (hn : 1 ≤ n) (H : Subgroup (GL (Fin n) K)) {m : ℕ}
    (h : ∀ x : (StatedScalars (Fin n) K).subgroupOf H, ∀ c : Kˣ,
      (x : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c → c ^ m = 1) :
    Nat.card ((StatedScalars (Fin n) K).subgroupOf H) ∣ m := by
  have := isCyclic_scalars hn H
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_scalars x.2
  apply Subtype.ext
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_pow, hc, ← map_pow, h x c hc, map_one, Subgroup.coe_one,
    Subgroup.coe_one]

theorem factorization_six_mul_three {x : ℕ} (hx : x ≠ 0) :
    (6 * x).factorization 3 = (3 * x).factorization 3 := by
  rw [show 6 * x = 2 * (3 * x) by ring, Nat.factorization_mul (by norm_num) (by positivity),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by norm_num), zero_add]

theorem not_three_dvd_pow_add_sub {f : ℕ} (hf : 1 ≤ f) :
    ¬ 3 ∣ 3 ^ f + 1 ∧ ¬ 3 ∣ 3 ^ f - 1 := by
  have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
  have h1 : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
  constructor <;> omega

theorem classical_scalar_cover_step {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hn : 2 ≤ n)
    [Finite K] {H : Subgroup (GL (Fin n) K)}
    (hH : (Nat.card K = p ^ f ∧ H = StatedSL n K) ∨
      (Nat.card K = (p ^ f) ^ 2 ∧ H = StatedSU n (p ^ f) K))
    {L : Type} [Group L] [Finite L] (hSQT : IsStronglyQuasithin L)
    (hodd : Odd (Nat.card (Subgroup.center L))) (π : H →* L) (hπ : Function.Surjective π)
    (hker : π.ker ≤ (StatedScalars (Fin n) K).subgroupOf H)
    (hD : ((StatedScalars (Fin n) K).subgroupOf H).map π = Subgroup.center L) :
    CatalogStepConclusion L := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have hn1 : 1 ≤ n := by omega
  set D := (StatedScalars (Fin n) K).subgroupOf H with hDdef
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hq2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have hDn : Nat.card D ∣ n := card_scalars_dvd hn1 H fun x c hc => by
    have hdet := det_eq_one_of_linUni hH x.1.2
    rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  rcases hH with ⟨hK, rfl⟩ | ⟨hK, rfl⟩
  ·
    have hchar : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    have hDe : Nat.card D ∣ p ^ f - 1 := card_scalars_dvd hn1 _ fun x c _ => by
      rw [← hK, ← card_units_eq]
      exact pow_card_eq_one'
    refine catalogStepConclusion_of_scalar_cover hp hn D hDn hDe (fun hp2 hn4 => ?_)
      (fun r hr hr2 hre C _ hC => ?_) (fun hn3 hD3 => ?_) hSQT hodd π hπ hker hD
    · have := ClassicalOdd.le_pRank_SL (a := 2) (b := 2) (by norm_num) hn4 hK
      nlinarith
    · have : Fact r.Prime := ⟨hr⟩
      exact (scalar_quotient_diagonal_torus_rank hp hn hr2 (Or.inl ⟨hK, rfl, hre⟩) C hC).1
    · subst hn3
      have h3e : 3 ∣ p ^ f - 1 := hD3 ▸ hDe
      have hp3 : p ≠ 3 := by
        rintro rfl
        exact (not_three_dvd_pow_add_sub hf).2 h3e
      refine three_pRank_statedProj_le_two monomialData_statedSL ?_ hD3
      have hM : Nat.card (⊤ : Subgroup Kˣ) = p ^ f - 1 := by
        rw [Subgroup.card_top, card_units_eq, hK]
      rw [card_statedSL_three, hK, hM, ← factorization_six_mul_three (by
        have : 0 < p ^ f - 1 := by omega
        positivity)]
      have e1 : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
        zify [hq1, Nat.one_le_pow 2 _ hq1]; ring
      have e2 : (p ^ f) ^ 3 - 1 = (p ^ f - 1) * ((p ^ f) ^ 2 + p ^ f + 1) := by
        zify [hq1, Nat.one_le_pow 3 _ hq1]; ring
      rw [e1, e2]
      exact factorization_order_eq Nat.prime_three (by norm_num) (by positivity) (by omega)
        (by omega) (by positivity)
        (fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
          (Nat.prime_three.dvd_of_dvd_pow h)).symm)
        (by omega) (factorization_sq_add_add_one Nat.prime_three hq1 h3e)
  ·
    have hK' : Nat.card K = p ^ (f * 2) := by rw [hK, ← pow_mul]
    have hchar : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK'])
    have hDe : Nat.card D ∣ p ^ f + 1 := card_scalars_dvd hn1 _ fun x c hc => by
      have hu := unitary_of_mem_statedSU hK x.1.2
      rw [hc, GeneralLinearGroup.coe_scalar] at hu
      have h00 := congrFun (congrFun hu ⟨0, hn1⟩) ⟨0, hn1⟩
      have hq0 : p ^ f ≠ 0 := by omega
      rw [Matrix.scalar_apply, Matrix.diagonal_map (by simp [zero_pow hq0]),
        Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.one_apply_eq,
        Matrix.diagonal_apply_eq] at h00
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one]
      exact h00
    refine catalogStepConclusion_of_scalar_cover hp hn D hDn hDe (fun hp2 hn4 => ?_)
      (fun r hr hr2 hre C _ hC => ?_) (fun hn3 hD3 => ?_) hSQT hodd π hπ hker hD
    · have := ClassicalOdd.four_mul_le_pRank_SU hp2 hn4 hK
      omega
    · have : Fact r.Prime := ⟨hr⟩
      exact (scalar_quotient_diagonal_torus_rank hp hn hr2 (Or.inr ⟨hK, rfl, hre⟩) C hC).1
    · subst hn3
      have h3e : 3 ∣ p ^ f + 1 := hD3 ▸ hDe
      have hp3 : p ≠ 3 := by
        rintro rfl
        exact (not_three_dvd_pow_add_sub hf).1 h3e
      refine three_pRank_statedProj_le_two monomialData_statedSU ?_ hD3
      rw [card_statedSU_three hK, card_normOne hK, ← factorization_six_mul_three (by positivity)]
      have hqq : p ^ f ≤ (p ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
      have e1 : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := sq_sub_one_eq hq1
      have e2 : (p ^ f) ^ 3 + 1 = (p ^ f + 1) * ((p ^ f) ^ 2 - p ^ f + 1) := by
        zify [hqq]
        ring
      rw [e1, e2]
      exact factorization_order_eq Nat.prime_three (by norm_num) (by positivity) (by omega)
        (by omega) (by omega)
        (fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
          (Nat.prime_three.dvd_of_dvd_pow h)).symm)
        (by omega) (factorization_sq_sub_add_one Nat.prime_three h3e)

end Classical

end CFSG.SectionRank.OddCover
