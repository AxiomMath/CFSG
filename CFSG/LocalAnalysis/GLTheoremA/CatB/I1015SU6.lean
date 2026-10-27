module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.LinearCover
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015Cover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Matrix CFSG.Open CFSG.SectionRank.OddCover CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

namespace I1015

@[expose] def swapGL {n : ℕ} (K : Type) [Field K] (i j : Fin n) : GL (Fin n) K :=
  ⟨(Equiv.swap i j).permMatrix K, (Equiv.swap i j).permMatrix K,
    by rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one],
    by rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]⟩

variable {K : Type} [Field K]

theorem coe_swapGL {n : ℕ} (i j : Fin n) :
    ((swapGL K i j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (Equiv.swap i j).permMatrix K :=
  rfl

theorem swapGL_apply {n : ℕ} (i j a b : Fin n) :
    ((swapGL K i j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
      if Equiv.swap i j a = b then 1 else 0 := by
  rw [coe_swapGL, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_eq, Matrix.submatrix_apply,
    Matrix.one_apply]
  rfl

theorem swapGL_mul_self {n : ℕ} (i j : Fin n) : swapGL K i j * swapGL K i j = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_swapGL, ← Matrix.permMatrix_mul, Equiv.swap_mul_self,
    Matrix.permMatrix_one, Units.val_one]

theorem det_swapGL [CharP K 2] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ((swapGL K i j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [coe_swapGL, Matrix.det_permutation, Equiv.Perm.sign_swap hij]
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
  exact CharTwo.neg_eq 1

theorem swapGL_not_scalar {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    swapGL K i j ∉ StatedScalars (Fin n) K := by
  rintro ⟨c, hc⟩
  have h := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, swapGL_apply, Equiv.swap_apply_left,
    if_true] at h
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij] at h
  exact zero_ne_one h

theorem swapGL_mem_SU [CharP K 2] {n q : ℕ} (hq : q ≠ 0) {i j : Fin n} (hij : i ≠ j) :
    swapGL K i j ∈ StatedSU n q K := by
  refine Subgroup.subset_closure ⟨det_swapGL hij, ?_⟩
  have hmap : ((swapGL K i j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (· ^ q) =
      ((swapGL K i j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    ext a b
    rw [Matrix.map_apply, swapGL_apply]
    split_ifs
    · exact one_pow q
    · exact zero_pow hq
  rw [hmap, coe_swapGL, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul,
    mul_inv_cancel, Matrix.permMatrix_one]

theorem diag_mul_swapGL {n : ℕ} (d : Fin n → Kˣ) {i j : Fin n} (hd : d i = d j) :
    diagHom n d * swapGL K i j = swapGL K i j * diagHom n d := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagHom, coe_swapGL]
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, ← coe_swapGL, swapGL_apply]
  by_cases h : Equiv.swap i j a = b
  · rw [if_pos h]
    have hab : ((d a : Kˣ) : K) = (d b : Kˣ) := by
      rw [← h]
      by_cases hai : a = i
      · subst hai
        rw [Equiv.swap_apply_left]
        exact congrArg Units.val hd
      · by_cases haj : a = j
        · subst haj
          rw [Equiv.swap_apply_right]
          exact (congrArg Units.val hd).symm
        · rw [Equiv.swap_apply_of_ne_of_ne hai haj]
    rw [hab]
    simp
  · simp [h]

section Scalars

variable [Finite K] [CharP K 2] {n : ℕ}

theorem pow_three_of_pow_six {M : Type} [Monoid M] (h3 : 3 ∣ 2 ^ n + 1) {c : M} (h6 : c ^ 6 = 1)
    (hq : c ^ (2 ^ n + 1) = 1) : c ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := h3
  have hn : n ≠ 0 := by
    rintro rfl
    omega
  have hodd : Odd (2 ^ n + 1) := by
    have : Even (2 ^ n) := (Nat.even_pow.2 ⟨even_two, hn⟩)
    exact this.add_one
  have hk' : Odd k := by
    rw [hk] at hodd
    exact (Nat.odd_mul.1 hodd).2
  obtain ⟨j, hj⟩ := hk'
  have h2 : (c ^ 3) ^ 2 = 1 := by rw [← pow_mul]; exact h6
  have hx : (c ^ 3) ^ k = 1 := by rw [← pow_mul, ← hk]; exact hq
  rw [hj, pow_succ, pow_mul, h2, one_pow, one_mul] at hx
  exact hx

theorem scalar_pow_three (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {x : ↥(StatedSU 6 (2 ^ n) K)}
    (hx : x ∈ (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ n) K)) : x ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_scalars hx
  have hdet := det_eq_one_of_linUni (n := 6) (p := 2) (f := n) (H := StatedSU 6 (2 ^ n) K)
    (Or.inr ⟨hK, rfl⟩) x.2
  have huni := unitary_of_mem_statedSU (p := 2) (f := n) hK x.2
  rw [hc] at hdet huni
  have h6 : (c : K) ^ 6 = 1 := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] using hdet
  have hq : (c : K) ^ (2 ^ n + 1) = 1 := by
    have := congrFun (congrFun huni 0) 0
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, pow_succ] using this
  have h3c : (c : K) ^ 3 = 1 := pow_three_of_pow_six h3 h6 hq
  apply Subtype.ext
  change (x : GL (Fin 6) K) ^ 3 = 1
  rw [hc, ← map_pow]
  have : c ^ 3 = 1 := Units.ext (by simpa using h3c)
  rw [this, map_one]

end Scalars

section Torus

variable [Finite K] [CharP K 2] {n : ℕ}

@[expose] def vE (R : Type) [CommRing R] : (Fin 3 → R) →+ (Fin 6 → R) where
  toFun u := ![u 0, u 1, u 2, -(u 0 + u 1 + u 2), 0, 0]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' u u' := by ext i; fin_cases i <;> simp <;> ring

theorem sum_vE (R : Type) [CommRing R] (u : Fin 3 → R) : ∑ i, vE R u i = 0 := by
  simp [vE, Fin.sum_univ_succ]

theorem vE_inj (R : Type) [CommRing R] (u : Fin 3 → R) (h : ∀ i, vE R u i = 0) : u = 0 := by
  funext i
  fin_cases i
  · simpa [vE] using h 0
  · simpa [vE] using h 1
  · simpa [vE] using h 2

theorem vE_four (R : Type) [CommRing R] (u : Fin 3 → R) : vE R u 4 = 0 := by simp [vE]

theorem vE_five (R : Type) [CommRing R] (u : Fin 3 → R) : vE R u 5 = 0 := by simp [vE]

theorem su6_data (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) :
    ∃ (E' : Subgroup ↥(StatedSU 6 (2 ^ n) K)) (s₀ : ↥(StatedSU 6 (2 ^ n) K)),
      IsElemAbelian 3 E' ∧ Nat.card E' = 27 ∧
      E' ⊓ (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ n) K) = ⊥ ∧
      IsElemAbelian 3 ((StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ n) K)) ∧
      s₀ * s₀ = 1 ∧ s₀ ∉ (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ n) K) ∧
      ∀ e ∈ E', e * s₀ = s₀ * e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  obtain ⟨ζ, hζr⟩ : ∃ ζ : Kˣ, orderOf ζ = 3 :=
    exists_zeta (K := K) (r := 3) (by rw [hK, sq_sub_one_eq hq]; exact Dvd.dvd.mul_right h3 _)
  have hζ : ζ ^ 3 = 1 := by rw [← hζr]; exact pow_orderOf_eq_one ζ
  have hζu : ζ ^ (2 ^ n + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζr ▸ h3)
  let ψ : Multiplicative (Fin 3 → ZMod 3) →* ↥(StatedSU 6 (2 ^ n) K) :=
    (torusWit ζ hζ (vE (ZMod 3))).codRestrict _
      (fun u => torusWit_mem_SU (by positivity) hζ hζu (vE (ZMod 3)) (sum_vE (ZMod 3)) u)
  have hψc : ∀ u, ((ψ u : ↥(StatedSU 6 (2 ^ n) K)) : GL (Fin 6) K) = torusWit ζ hζ (vE (ZMod 3)) u :=
    fun u => rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact torusWit_injective hζ hζr (vE (ZMod 3)) (vE_inj (ZMod 3)) (by simpa [hψc] using congrArg Subtype.val hab)
  refine ⟨ψ.range, ⟨swapGL K 4 5, swapGL_mem_SU (by positivity) (by decide)⟩,
    isElemAbelian_range ψ (fun a => multiplicative_zmod_pow_eq_one a), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_range_eq_of_injective ψ hψinj, card_multiplicative_zmod]
    norm_num
  · rw [eq_bot_iff]
    rintro x ⟨⟨u, rfl⟩, hxD⟩
    obtain ⟨c, hc⟩ := exists_scalar_of_mem_scalars hxD
    have hu : u = 1 := eq_one_of_torusWit_scalar hζ hζr (vE (ZMod 3)) 4 (vE_four (ZMod 3)) (vE_inj (ZMod 3)) u (by
      rw [← hψc]; exact hc)
    rw [hu, map_one]
    exact Subgroup.one_mem _
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => scalar_pow_three hK h3 hx⟩
    exact (Subgroup.mem_center_iff.1 (scalars_le_center _ a.2) b).symm
  · exact Subtype.ext (swapGL_mul_self 4 5)
  · intro h
    exact swapGL_not_scalar (K := K) (i := (4 : Fin 6)) (j := 5) (by decide)
      (Subgroup.mem_subgroupOf.1 h)
  · rintro _ ⟨u, rfl⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hψc]
    exact diag_mul_swapGL _ (by simp [vE_four, vE_five])

end Torus

section Cover

open CFSG.RankThree.PerfectCover (hopfMultiplier)

variable [Finite K] {f : ℕ}

theorem exists_hom_su6 (hGA : GriessAllModelsStatement) (h3 : 3 ∣ 2 ^ f + 1)
    (hK : Nat.card K = (2 ^ f) ^ 2) {L : Type} [Group L] [Finite L] (hL : Group.IsPerfect L)
    (β : L →* StatedProj (StatedSU 6 (2 ^ f) K)) (hβ : Function.Surjective β)
    (hβc : β.ker ≤ Subgroup.center L) (hβp : IsPGroup 3 β.ker) :
    ∃ φ : ↥(StatedSU 6 (2 ^ f) K) →* L, Function.Surjective φ ∧
      β.comp φ = QuotientGroup.mk' ((StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ f) K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · omega
    · exact h
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hHK : (Nat.card K = 2 ^ f ∧ StatedSU 6 (2 ^ f) K = StatedSL 6 K) ∨
      (Nat.card K = (2 ^ f) ^ 2 ∧ StatedSU 6 (2 ^ f) K = StatedSU 6 (2 ^ f) K) :=
    Or.inr ⟨hK, rfl⟩
  have hHperf : Group.IsPerfect ↥(StatedSU 6 (2 ^ f) K) :=
    isPerfect_linUni Nat.prime_two (by norm_num) hHK
  have hDc : (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ f) K) ≤
      Subgroup.center ↥(StatedSU 6 (2 ^ f) K) := scalars_le_center _
  let α : ↥(StatedSU 6 (2 ^ f) K) →* StatedProj (StatedSU 6 (2 ^ f) K) :=
    QuotientGroup.mk' ((StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ f) K))
  have hα : Function.Surjective α := QuotientGroup.mk'_surjective _
  have hαk : α.ker = (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ f) K) :=
    QuotientGroup.ker_mk' _
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 6 2 f :=
    ⟨Nat.prime_two, hf1, by norm_num, by simp⟩
  have hmm : CFSG.Models.LieModel (StatedProj (StatedSU 6 (2 ^ f) K)) .PSU 6 2 f :=
    lieModel_of_classical ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hfin, hcard⟩ := finite_and_card_hopf hGA hmm
  haveI := hfin
  have hdvd24 : Nat.card (hopfMultiplier (StatedProj (StatedSU 6 (2 ^ f) K))) ∣ 24 := by
    rw [hcard]
    have h1 : (CFSG.Blueprint.Multiplier.genericOrders .PSU 6 2 f).1 ∣ 6 := Nat.gcd_dvd_left _ _
    have h2 : (CFSG.Blueprint.Multiplier.genericOrders .PSU 6 2 f).2 = 1 := rfl
    have h3' : (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 6 2 f).1 ∣ 2 ∧
        (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 6 2 f).2 ∣ 2 := by
      by_cases hf : f = 1
      · subst hf
        exact ⟨by decide, by decide⟩
      · have : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 6 2 f = (1, 1) := by
          unfold CFSG.Blueprint.Multiplier.exceptionalOrders
          split <;> simp_all
        rw [this]
        exact ⟨one_dvd _, one_dvd _⟩
    rw [h2, mul_one]
    exact Nat.mul_dvd_mul h1 (Nat.mul_dvd_mul h3'.1 h3'.2) |>.trans (by norm_num)
  have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSU 6 (2 ^ f) K)))).factorization 3 ≤
      (Nat.card α.ker).factorization 3 := by
    have hD3 : 3 ∣ Nat.card ((StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ f) K)) :=
      dvd_card_scalars (n := 6) (q := 2 ^ f) (d := 3) (by norm_num) hq
        (Or.inr ⟨hK, rfl, by norm_num, h3⟩)
    have hle : (Nat.card (hopfMultiplier (StatedProj (StatedSU 6 (2 ^ f) K)))).factorization 3 ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have h9 : 3 ^ 2 ∣ Nat.card (hopfMultiplier (StatedProj (StatedSU 6 (2 ^ f) K))) :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').2 hlt
      have := h9.trans hdvd24
      omega
    refine hle.trans ?_
    rw [hαk]
    exact (Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hD3)
  exact exists_hom_of_cover hHperf hL α hα (hαk.le.trans hDc) β hβ hβc Nat.prime_three hβp hM

theorem exists_Ebar_s_of_cover (hGA : GriessAllModelsStatement) (h3 : 3 ∣ 2 ^ f + 1)
    (hK : Nat.card K = (2 ^ f) ^ 2) {L : Type} [Group L] [Finite L] (hL : Group.IsPerfect L)
    (β : L →* StatedProj (StatedSU 6 (2 ^ f) K)) (hβ : Function.Surjective β)
    (hβc : β.ker ≤ Subgroup.center L) (hβp : IsPGroup 3 β.ker) :
    ∃ (Eb : Subgroup L) (s : L), IsElemAbelian 3 Eb ∧ Nat.card Eb = 27 * Nat.card β.ker ∧
      s ^ 2 = 1 ∧ β s ≠ 1 ∧ ∀ x ∈ Eb, x * s = s * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2 * f) (by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  obtain ⟨φ, hφs, hβφ⟩ := exists_hom_su6 hGA h3 hK hL β hβ hβc hβp
  obtain ⟨E', s₀, hE', hE'c, hE'D, hD, hs2, hsD, hsc⟩ := su6_data hK h3
  set D := (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ f) K) with hDdef
  have hDcen : D ≤ Subgroup.center (StatedSU 6 (2 ^ f) K) := scalars_le_center _
  have hE : IsElemAbelian 3 (E' ⊔ D) :=
    hE'.sup_of_commute hD (fun a _ b hb => (Subgroup.mem_center_iff.1 (hDcen hb) a))
  refine cover_assembly (QuotientGroup.mk' D) β φ hφs hβφ (QuotientGroup.ker_mk' D) hE'c hE'D hE hs2
    hsD ?_
  intro e he
  have hle : E' ⊔ D ≤ Subgroup.centralizer ({s₀} : Set _) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hsc x hx
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_center_iff.1 (hDcen hx) s₀).symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)

end Cover

end I1015

end CFSG.LocalAnalysis.GLTheoremA.CatB
