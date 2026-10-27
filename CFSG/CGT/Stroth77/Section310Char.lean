module

public import CFSG.CGT.Stroth77.Section310
public import CFSG.CGT.Stroth77.StrothFrameNE
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2GL

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

theorem two_nsmul_natCast_eq_zero_iff {n : ℕ} (a : ℕ) :
    2 • (a : ZMod (2 ^ (n + 1))) = 0 ↔ 2 ^ n ∣ a := by
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, pow_succ, mul_comm (2 ^ n) 2]
  exact Nat.mul_dvd_mul_iff_left (by norm_num)

theorem natCard_two_torsion_zmod {M n : ℕ} (hM : M = 2 ^ (n + 1)) :
    Nat.card {z : ZMod M // 2 • z = 0} = 2 := by
  subst hM
  have hlt : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n)
  have hne : ((2 ^ n : ℕ) : ZMod (2 ^ (n + 1))) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by positivity) h) (by omega)
  have hset : ∀ z : ZMod (2 ^ (n + 1)), 2 • z = 0 ↔ z = 0 ∨ z = ((2 ^ n : ℕ) : ZMod _) := by
    intro z
    obtain ⟨v, hv, rfl⟩ : ∃ v : ℕ, v < 2 ^ (n + 1) ∧ (v : ZMod (2 ^ (n + 1))) = z :=
      ⟨z.val, ZMod.val_lt z, ZMod.natCast_zmod_val z⟩
    rw [two_nsmul_natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hlt]
    constructor
    · rintro ⟨j, rfl⟩
      rw [pow_succ] at hv
      obtain rfl | rfl : j = 0 ∨ j = 1 := by
        rcases Nat.lt_or_ge j 2 with hj | hj
        · omega
        · exact absurd (Nat.mul_le_mul_left (2 ^ n) hj) (by omega)
      · left; simp
      · right; simp
    · rintro (h | h)
      · exact ⟨0, by have := Nat.eq_zero_of_dvd_of_lt h hv; omega⟩
      · exact ⟨1, by rw [h, mul_one]⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    show (Finset.univ.filter fun z : ZMod (2 ^ (n + 1)) => 2 • z = 0) = {0, ((2 ^ n : ℕ) : ZMod _)}
      by ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]; exact hset z]
  exact Finset.card_pair (Ne.symm hne)

theorem exists_four_nsmul_zmod {M n : ℕ} (hM : M = 2 ^ (n + 3)) {z : ZMod M} (hz : 2 • z = 0) :
    ∃ y : ZMod M, z = 4 • y := by
  subst hM
  obtain ⟨v, -, rfl⟩ : ∃ v : ℕ, v < 2 ^ (n + 3) ∧ (v : ZMod (2 ^ (n + 3))) = z :=
    ⟨z.val, ZMod.val_lt z, ZMod.natCast_zmod_val z⟩
  obtain ⟨j, rfl⟩ := (two_nsmul_natCast_eq_zero_iff (n := n + 2) v).mp hz
  exact ⟨((2 ^ n * j : ℕ) : ZMod _), by rw [nsmul_eq_mul]; push_cast; ring⟩

theorem natCard_two_torsion_torus {k : Fin 3 → ℕ} {n : ℕ} (hk : ∀ i, k i = n + 1) :
    Nat.card {w : Torus k // 2 • w = 0} = 8 := by
  have e : {w : Torus k // 2 • w = 0} ≃ ∀ i, {z : ZMod (2 ^ k i) // 2 • z = 0} :=
    (Equiv.subtypeEquivRight fun w => by
      rw [funext_iff]; simp only [Pi.smul_apply, Pi.zero_apply]).trans
      (Equiv.subtypePiEquivPi)
  rw [Nat.card_congr e, Nat.card_pi, Fin.prod_univ_three,
    natCard_two_torsion_zmod (n := n) (congrArg (2 ^ ·) (hk 0)),
    natCard_two_torsion_zmod (n := n) (congrArg (2 ^ ·) (hk 1)),
    natCard_two_torsion_zmod (n := n) (congrArg (2 ^ ·) (hk 2))]
  norm_num

theorem exists_four_nsmul_of_two_nsmul_eq_zero {k : Fin 3 → ℕ} {n : ℕ} (hk : ∀ i, k i = n + 3)
    {w : Torus k} (hw : 2 • w = 0) : ∃ v : Torus k, w = 4 • v := by
  choose y hy using fun i => exists_four_nsmul_zmod (n := n) (congrArg (2 ^ ·) (hk i))
    (z := w i) (by simpa using congrFun hw i)
  exact ⟨y, funext fun i => by simpa using hy i⟩

section Omega

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}

theorem mem_omegaIn_one_iff (hD : IsMulCommutative D) {x : G} :
    x ∈ omegaIn 1 D ↔ x ∈ D ∧ x * x = 1 := by
  refine ⟨?_, fun h => mem_omegaIn_one_of_mul_self h.1 h.2⟩
  rintro ⟨y, hy, rfl⟩
  refine ⟨y.2, ?_⟩
  have key : y * y = 1 := by
    induction hy using Subgroup.closure_induction with
    | mem z hz => simpa [pow_two] using hz
    | one => simp
    | mul a b _ _ ha hb =>
      calc a * b * (a * b) = a * a * (b * b) := by
            rw [mul_assoc, ← mul_assoc b a b, hD.is_comm.comm b a]; group
        _ = 1 := by rw [ha, hb, one_mul]
    | inv a _ ha => rw [← mul_inv_rev, ha, inv_one]
  exact congrArg Subtype.val key

variable {k : Fin 3 → ℕ} (e : Additive D ≃+ Torus k)

include e in
theorem mul_self_eq_one_iff_two_nsmul (y : D) : y * y = 1 ↔ 2 • e (Additive.ofMul y) = 0 := by
  rw [two_nsmul, ← map_add, ← ofMul_mul, AddEquiv.map_eq_zero_iff, ofMul_eq_zero]

include e in
theorem natCard_omegaIn_one {n : ℕ} (hk : ∀ i, k i = n + 1) : Nat.card (omegaIn 1 D) = 8 := by
  have hD : IsMulCommutative D := ⟨⟨fun x y => Additive.ofMul.injective (e.injective (by
    simp only [ofMul_mul, map_add]; exact add_comm _ _))⟩⟩
  let E1 : ↥(omegaIn 1 D) ≃ {y : D // y * y = 1} :=
    { toFun := fun x => ⟨⟨x, ((mem_omegaIn_one_iff hD).mp x.2).1⟩,
        Subtype.ext ((mem_omegaIn_one_iff hD).mp x.2).2⟩
      invFun := fun y => ⟨y.1, mem_omegaIn_one_of_mul_self y.1.2 (congrArg Subtype.val y.2)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  let E2 : {y : D // y * y = 1} ≃ {w : Torus k // 2 • w = 0} :=
    (Additive.ofMul.trans e.toEquiv).subtypeEquiv fun y => mul_self_eq_one_iff_two_nsmul e y
  rw [Nat.card_congr (E1.trans E2), natCard_two_torsion_torus hk]

include e in
theorem exists_pow_four_of_mem_omegaIn {n : ℕ} (hk : ∀ i, k i = n + 3) {x : G}
    (hx : x ∈ omegaIn 1 D) : ∃ y ∈ D, x = y ^ 4 := by
  have hD : IsMulCommutative D := ⟨⟨fun x y => Additive.ofMul.injective (e.injective (by
    simp only [ofMul_mul, map_add]; exact add_comm _ _))⟩⟩
  obtain ⟨hxD, hx2⟩ := (mem_omegaIn_one_iff hD).mp hx
  obtain ⟨v, hv⟩ := exists_four_nsmul_of_two_nsmul_eq_zero hk
    ((mul_self_eq_one_iff_two_nsmul e ⟨x, hxD⟩).mp (Subtype.ext hx2))
  refine ⟨(Additive.toMul (e.symm v) : D), (Additive.toMul (e.symm v)).2, ?_⟩
  have h1 : (⟨x, hxD⟩ : D) = Additive.toMul (e.symm v) ^ 4 := by
    apply Additive.ofMul.injective
    apply e.injective
    rw [hv, ofMul_pow, map_nsmul, ofMul_toMul, AddEquiv.apply_symm_apply]
  exact congrArg Subtype.val h1

end Omega

section Char

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem StrothFrame.IsD.uv_not_mem (h : F.IsD D dD) : F.dA.uv ∉ D := by
  intro huv
  have hmem : F.dA.uv ∈ D ⊓ F.E := ⟨huv, F.uv_mem_E⟩
  rw [h.inf_E] at hmem
  have hle : Subgroup.closure {((F.dA.a : F.A) : G) ^ 2, ((F.dA.b : F.A) : G) ^ 2} ≤ F.A := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact pow_mem F.dA.a.2 2
    · exact pow_mem F.dA.b.2 2
  apply F.uv_not_mem_centralizer_A
  exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
    congrArg Subtype.val (F.dA.isMulCommutative.is_comm.comm ⟨y, hy⟩ ⟨_, hle hmem⟩)

theorem false_of_index_le_four {B : Subgroup D} (hB : B.index ≤ 4)
    (hBc : ∀ y ∈ B, (y : G) * dD.uv = dD.uv * y) (w : Fin 5 → Torus τ.k)
    (hw : ∀ i j, i ≠ j → τ.action.φuv (w j - w i) ≠ w j - w i) : False := by
  have hcomm : ∀ x y : D, x * y = y * x := fun x y => dD.isMulCommutative.is_comm.comm x y
  haveI : B.Normal := ⟨fun n _ g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  let x : Fin 5 → D := fun i => Additive.toMul (dD.e.symm (w i))
  have hinj : Function.Injective fun i => (x i : D ⧸ B) := by
    intro i j hij
    by_contra hne
    have hmem : (x i)⁻¹ * x j ∈ B := QuotientGroup.eq.mp hij
    have hc := hBc _ hmem
    have hconj : conjBy dD.uv_mem ((x i)⁻¹ * x j) = (x i)⁻¹ * x j := by
      apply Subtype.ext
      change dD.uv⁻¹ * (((x i)⁻¹ * x j : D) : G) * dD.uv = _
      rw [mul_assoc, hc, inv_mul_cancel_left]
    have h1 := dD.uv_conj ((x i)⁻¹ * x j)
    rw [hconj] at h1
    have he : dD.e (Additive.ofMul ((x i)⁻¹ * x j)) = w j - w i := by
      simp [x, ofMul_mul, ofMul_inv, map_add, map_neg, sub_eq_add_neg, add_comm]
    rw [he] at h1
    exact hw i j hne h1.symm
  have h5 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fin, ← Subgroup.index] at h5
  omega

theorem exists_five_of_k_eq_two (τ : StrothTypeIndex) (h01 : τ.k 0 = τ.k 1) (h2 : τ.k 1 = 2) :
    ∃ w : Fin 5 → Torus τ.k, ∀ i j, i ≠ j → τ.action.φuv (w j - w i) ≠ w j - w i := by
  cases τ
  case t300 n =>
    obtain rfl : n = 2 := h2
    exact ⟨![0, Torus.c, 2 • Torus.c, 3 • Torus.c, Torus.a], by decide⟩
  case t310 m hm =>
    obtain rfl : m = 2 := h2
    exact ⟨![0, Torus.c, 2 • Torus.c, 3 • Torus.c, Torus.a], by decide +revert⟩
  case t320 m hm => exact absurd h2 (by change m ≠ 2; omega)
  case t330 m hm => exact absurd h2 (by change m ≠ 2; omega)
  case t321 => exact absurd h2 (by decide)
  case t331 => exact absurd h2 (by decide)
  all_goals
    exfalso
    simp [StrothTypeIndex.k, Type100.k, Type101.k, Type110.k, Type111.k, Type120.k, Type121.k,
      Type130.k, Type131.k, Type200.k, Type201.k, Type210.k, Type211.k, Type220.k, Type221.k,
      Type230.k, Type231.k] at h01

theorem mul_comm_of_card_dvd_four {H : Type*} [Group H] [Finite H] (h : Nat.card H ∣ 4)
    (a b : H) : a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card H ∣ 2 ^ 2 from h)
  interval_cases j
  · have : Subsingleton H := (Nat.card_eq_one_iff_unique.mp (by simpa using hcard)).1
    exact Subsingleton.elim _ _
  · have : IsCyclic H := isCyclic_of_prime_card (p := 2) (by simpa using hcard)
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨i', rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    exact zpow_mul_comm g i i'
  · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard).is_comm.comm a b

theorem card_eq_eight_of_dvd {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hd : Nat.card H ∣ 8) {a b : X} (ha : a ∈ H) (hb : b ∈ H) (hab : a * b ≠ b * a) :
    Nat.card H = 8 := by
  by_contra hne
  have h4 : Nat.card H ∣ 4 := by
    have hmem : Nat.card H ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h <;> simp_all
  exact hab (congrArg Subtype.val (mul_comm_of_card_dvd_four h4 ⟨a, ha⟩ ⟨b, hb⟩))

theorem eq_one_or_eq_of_central_of_card_eight {M : Type*} [Group M] [Finite M] {X : Subgroup M}
    (hX8 : Nat.card X = 8) {a b : M} (ha : a ∈ X) (hb : b ∈ X) (hab : a * b ≠ b * a) {x : M}
    (hxX : x ∈ X) (hx1 : x ≠ 1) (hxZ : ∀ d ∈ X, d * x = x * d) {c : M} (hcX : c ∈ X)
    (hcZ : ∀ d ∈ X, d * c = c * d) : c = 1 ∨ c = x := by
  by_contra hne
  push Not at hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center X
  have hmem : ∀ y (hy : y ∈ X), (∀ d ∈ X, d * y = y * d) → (⟨y, hy⟩ : X) ∈ Z :=
    fun y hy hyZ => Subgroup.mem_center_iff.mpr fun d => Subtype.ext (hyZ d d.2)
  have h3 : 3 ≤ Nat.card Z := by
    let f : Fin 3 → Z := ![1, ⟨⟨x, hxX⟩, hmem x hxX hxZ⟩, ⟨⟨c, hcX⟩, hmem c hcX hcZ⟩]
    have hf : Function.Injective f := by
      intro i j hij
      have hij' := congrArg (fun z : Z => ((z : X) : M)) hij
      fin_cases i <;> fin_cases j <;> simp [f] at hij' <;> (try rfl) <;>
        (try exact absurd hij'.symm hx1) <;> (try exact absurd hij' hx1) <;>
        (try exact absurd hij'.symm hne.1) <;> (try exact absurd hij' hne.1) <;>
        (try exact absurd hij'.symm hne.2) <;> exact absurd hij' hne.2
    simpa using Nat.card_le_card_of_injective f hf
  have hdvd : Nat.card Z ∣ 8 := hX8 ▸ Subgroup.card_subgroup_dvd_card Z
  have hcomm : ∀ p q : X, p * q = q * p := by
    have hmem8 : Nat.card Z ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide] at hmem8
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem8
    rcases hmem8 with h | h | h | h
    · omega
    · omega
    · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
      rw [hX8, h] at h1
      have h2 : Nat.card (X ⧸ Z) = 2 := by omega
      have : IsCyclic (X ⧸ Z) := isCyclic_of_prime_card h2
      exact (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
        (QuotientGroup.mk' Z) (by rw [QuotientGroup.ker_mk'])).is_comm.comm
    · have hZ : Z = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h, hX8])
      intro p q
      have hq : q ∈ Z := by rw [hZ]; exact Subgroup.mem_top q
      exact Subgroup.mem_center_iff.mp hq p
  exact hab (congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩))

theorem StrothFrame.IsD.mem_normalizer_of_mem_normalizer_normalizerIn (h : F.IsD D dD)
    (hτ : τ.m = τ.n)
    (hR : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D)
    {g : G} (hgS : g ∈ (F.S : Subgroup G))
    (hgN : g ∈ Subgroup.normalizer
      (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (D : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) with hN
  set Ω : Subgroup G := omegaIn 1 D with hΩ
  have hDc : IsMulCommutative D := dD.isMulCommutative
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDN : D ≤ N := le_inf h.le_S Subgroup.le_normalizer
  have hΩD : Ω ≤ D := omegaIn_le 1 D
  have hΩN : Ω ≤ N := hΩD.trans hDN
  have hRmem : ∀ x ∈ N, (∀ w ∈ Ω, w * x = x * w) → x ∈ D := fun x hx hc => by
    rw [← hR]; exact ⟨hx, Subgroup.mem_centralizer_iff.mpr hc⟩
  have hk : ∀ i, τ.k i = τ.k 1 := by
    intro i
    rw [τ.k_eq]
    fin_cases i <;> simp [hτ]
  have hn2 : 2 ≤ τ.k 1 := by
    have hle := Subgroup.card_le_of_le h.A_le
    rw [F.dA.card, dD.card, hk 0, hk 2] at hle
    have h5 : (StrothTypeIndex.t100 1).k 0 + (StrothTypeIndex.t100 1).k 1 +
        (StrothTypeIndex.t100 1).k 2 = 5 := rfl
    rw [h5] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega
  have huvN : dD.uv ∈ N := ⟨h.uv_eq ▸ F.uv_mem_S, dD.uv_mem⟩
  have htN : dD.t ∈ N := ⟨h.t_eq ▸ F.t_mem_S, dD.t_mem⟩
  have huN : dD.u ∈ N := ⟨h.u_eq ▸ F.u_mem_S, dD.u_mem⟩
  have huvD : dD.uv ∉ D := by rw [h.uv_eq]; exact h.uv_not_mem
  have htu : dD.t⁻¹ * dD.u⁻¹ * dD.t * dD.u = dD.uv := by
    have ht' : dD.t⁻¹ = dD.t := inv_eq_of_mul_eq_one_right dD.t_sq
    have hu' : dD.u⁻¹ = dD.u := inv_eq_of_mul_eq_one_right dD.u_sq
    calc dD.t⁻¹ * dD.u⁻¹ * dD.t * dD.u = dD.t * (dD.u * (dD.t * dD.u)) := by
          rw [ht', hu']; group
      _ = dD.t * (dD.u * dD.u) * dD.uv * dD.t := by rw [dD.t_u]; group
      _ = dD.t * dD.uv * dD.t := by rw [dD.u_sq, mul_one]
      _ = dD.uv * (dD.t * dD.t) := by rw [← dD.uv_comm_t]; group
      _ = dD.uv := by rw [dD.t_sq, mul_one]
  have hΩnorm : ∀ x ∈ N, ∀ w ∈ Ω, x * w * x⁻¹ ∈ Ω := by
    intro x hx w hw
    obtain ⟨hwD, hw2⟩ := (mem_omegaIn_one_iff hDc).mp hw
    refine mem_omegaIn_one_of_mul_self ((Subgroup.mem_normalizer_iff.mp hx.2 w).mp hwD) ?_
    calc x * w * x⁻¹ * (x * w * x⁻¹) = x * (w * w) * x⁻¹ := by group
      _ = 1 := by rw [hw2, mul_one, mul_inv_cancel]
  haveI : (Ω.subgroupOf N).Normal := ⟨fun w hw x => Subgroup.mem_subgroupOf.mpr (by
    simpa using hΩnorm x x.2 w (Subgroup.mem_subgroupOf.mp hw))⟩
  let θ : ↥N →* MulAut ↥(Ω.subgroupOf N) := MulAut.conjNormal
  have hθ : ∀ x : N, θ x = 1 ↔ (x : G) ∈ D := by
    intro x
    constructor
    · intro hx
      refine hRmem x x.2 fun w hw => ?_
      have h1 := congrArg (fun φ : MulAut ↥(Ω.subgroupOf N) =>
        (((φ ⟨⟨w, hΩN hw⟩, Subgroup.mem_subgroupOf.mpr hw⟩ : ↥(Ω.subgroupOf N)) : N) : G)) hx
      simp only [θ, MulAut.conjNormal_apply, MulAut.one_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      calc w * (x : G) = ((x : G) * w * (x : G)⁻¹) * (x : G) := by rw [h1]
        _ = (x : G) * w := by group
    · intro hx
      refine MulEquiv.ext fun w => Subtype.ext (Subtype.ext ?_)
      simp only [θ, MulAut.conjNormal_apply, MulAut.one_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [hcommD _ hx _ (hΩD (Subgroup.mem_subgroupOf.mp w.2)), mul_inv_cancel_right]
  have hV8 : Nat.card ↥(Ω.subgroupOf N) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΩN).toEquiv]
    exact natCard_omegaIn_one dD.e (n := τ.k 1 - 1) (fun i => by rw [hk i]; omega)
  have hV2 : ∀ v : ↥(Ω.subgroupOf N), v * v = 1 := fun v => Subtype.ext (Subtype.ext
    ((mem_omegaIn_one_iff hDc).mp (Subgroup.mem_subgroupOf.mp v.2)).2)
  have h168 : Nat.card (MulAut ↥(Ω.subgroupOf N)) = 168 :=
    CFSG.OddStandard.ChengHeld.card_mulAut_elemAb8 hV8 hV2
  have hNp : IsPGroup 2 N := F.S.isPGroup'.to_le inf_le_left
  have hPp : IsPGroup 2 θ.range := hNp.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have hdvd8 : ∀ H : Subgroup (MulAut ↥(Ω.subgroupOf N)), H ≤ θ.range → Nat.card H ∣ 8 := by
    intro H hH
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp (hPp.to_le hH)
    have hd : Nat.card H ∣ 8 * 21 := by
      rw [show 8 * 21 = 168 by norm_num, ← h168]; exact Subgroup.card_subgroup_dvd_card _
    rw [ha] at hd ⊢
    exact (Nat.Coprime.pow_left a (by norm_num : Nat.Coprime 2 21)).dvd_of_dvd_mul_right hd
  set tN : N := ⟨dD.t, htN⟩
  set uN : N := ⟨dD.u, huN⟩
  set uvN : N := ⟨dD.uv, huvN⟩
  have hnc : θ tN * θ uN ≠ θ uN * θ tN := by
    intro hc
    have h1 : θ (tN⁻¹ * uN⁻¹ * tN * uN) = 1 := by
      simp only [map_mul, map_inv]
      rw [mul_assoc _ (θ tN) (θ uN), hc]
      group
    apply huvD
    rw [← htu]
    simpa [tN, uN] using (hθ _).mp h1
  by_contra hgD
  set K : Subgroup G := D.map (MulAut.conj g).toMonoidHom with hK
  have hmemK : ∀ k ∈ K, ∃ d ∈ D, k = g * d * g⁻¹ := by
    rintro k ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩
  have hKN : K ≤ N := by
    intro k hk'
    obtain ⟨d, hd, rfl⟩ := hmemK k hk'
    exact (Subgroup.mem_normalizer_iff.mp hgN d).mp (hDN hd)
  have hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    obtain ⟨d, hd, rfl⟩ := hmemK a ha
    obtain ⟨d', hd', rfl⟩ := hmemK b hb
    calc g * d * g⁻¹ * (g * d' * g⁻¹) = g * (d * d') * g⁻¹ := by group
      _ = g * (d' * d) * g⁻¹ := by rw [hcommD _ hd _ hd']
      _ = g * d' * g⁻¹ * (g * d * g⁻¹) := by group
  have hKnorm : ∀ x ∈ N, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk'
    obtain ⟨d, hd, rfl⟩ := hmemK k hk'
    have hxN : g⁻¹ * x * g ∈ N := (Subgroup.mem_normalizer_iff''.mp hgN x).mp hx
    have hd' : (g⁻¹ * x * g) * d * (g⁻¹ * x * g)⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp hxN.2 d).mp hd
    refine ⟨_, hd', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hcardK : Nat.card K = Nat.card D :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hKD : ∃ k ∈ K, k ∉ D := by
    by_contra hall
    push Not at hall
    have hKeq : K = D := Subgroup.eq_of_le_of_card_ge hall hcardK.ge
    apply hgD
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hKeq]; exact ⟨x, hx, rfl⟩
    · rw [← hKeq] at hx
      obtain ⟨d, hd, hdx⟩ := hmemK _ hx
      have : x = d := by simpa using hdx
      exact this ▸ hd
  obtain ⟨k, hkK, hkD⟩ := hKD
  set K' : Subgroup N := K.subgroupOf N with hK'
  have hθKle : K'.map θ ≤ θ.range := Subgroup.map_le_range θ K'
  have hθKc : ∀ a ∈ K'.map θ, ∀ b ∈ K'.map θ, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext (hKc _ (Subgroup.mem_subgroupOf.mp ha) _
      (Subgroup.mem_subgroupOf.mp hb)))
  have hθK4 : Nat.card (K'.map θ) ≤ 4 := by
    have hd := hdvd8 _ hθKle
    have hne : Nat.card (K'.map θ) ≠ 8 := by
      intro h8
      have hP8 : Nat.card θ.range = 8 :=
        card_eq_eight_of_dvd (hdvd8 _ le_rfl) ⟨tN, rfl⟩ ⟨uN, rfl⟩ hnc
      have heq : K'.map θ = θ.range := Subgroup.eq_of_le_of_card_ge hθKle (by rw [h8, hP8])
      exact hnc (hθKc _ (by rw [heq]; exact ⟨tN, rfl⟩) _ (by rw [heq]; exact ⟨uN, rfl⟩))
    have hmem : Nat.card (K'.map θ) ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hcardKD : Nat.card D ≤ 4 * Nat.card ↥(K ⊓ D) := by
    let f : ↥K' →* MulAut ↥(Ω.subgroupOf N) := θ.comp K'.subtype
    have hrange : f.range = K'.map θ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange] at h1
    have hker : Nat.card f.ker ≤ Nat.card ↥(K ⊓ D) := by
      refine Nat.card_le_card_of_injective
        (fun x => ⟨(((x : K') : N) : G), Subgroup.mem_subgroupOf.mp (x : K').2,
          (hθ _).mp (MonoidHom.mem_ker.mp x.2)⟩) ?_
      intro x y hxy
      have hxy' := congrArg Subtype.val hxy
      simp only at hxy'
      ext
      exact hxy'
    have hK'c : Nat.card K' = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
    calc Nat.card D = Nat.card K := hcardK.symm
      _ = Nat.card (K'.map θ) * Nat.card f.ker := by rw [← hK'c, h1]
      _ ≤ 4 * Nat.card ↥(K ⊓ D) := Nat.mul_le_mul hθK4 hker
  set B : Subgroup D := (K ⊓ D).subgroupOf D with hB
  have hBidx : B.index ≤ 4 := by
    have h1 := B.index_mul_card
    have hBc : Nat.card B = Nat.card ↥(K ⊓ D) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have hpos : 0 < Nat.card B := Nat.card_pos
    rw [hBc] at h1 hpos
    exact Nat.le_of_mul_le_mul_right (h1 ▸ hcardKD) hpos
  have hcomm' : ∀ x y : D, x * y = y * x := fun x y => hDc.is_comm.comm x y
  rcases Nat.lt_or_ge (τ.k 1) 3 with hlt | hge
  ·
    have hθuv1 : θ uvN ≠ 1 := fun h1 => huvD ((hθ uvN).mp h1)
    have hP8 : Nat.card θ.range = 8 :=
      card_eq_eight_of_dvd (hdvd8 _ le_rfl) ⟨tN, rfl⟩ ⟨uN, rfl⟩ hnc
    have hle : Subgroup.closure {θ uvN, θ tN, θ uN} ≤ θ.range := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
    have hgenP : θ.range ≤ Subgroup.closure {θ uvN, θ tN, θ uN} :=
      (Subgroup.eq_of_le_of_card_ge hle (by
        rw [hP8, card_eq_eight_of_dvd (hdvd8 _ hle) (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)) hnc])).ge
    have hcen' : ∀ p ∈ Subgroup.closure {θ uvN, θ tN, θ uN}, p * θ uvN = θ uvN * p := by
      intro p hp
      induction hp using Subgroup.closure_induction with
      | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · rfl
        · rw [← map_mul, ← map_mul]; exact congrArg θ (Subtype.ext dD.uv_comm_t.symm)
        · rw [← map_mul, ← map_mul]; exact congrArg θ (Subtype.ext dD.uv_comm_u.symm)
      | one => simp
      | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
      | inv x _ hx => rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx, mul_assoc, mul_inv_cancel,
          mul_one]
    have hcen : ∀ p ∈ θ.range, p * θ uvN = θ uvN * p := fun p hp => hcen' p (hgenP hp)
    have hPp' : IsPGroup 2 θ.range := hPp
    haveI : Group.IsNilpotent θ.range := hPp'.isNilpotent
    haveI hHn : ((K'.map θ).subgroupOf θ.range).Normal := by
      refine ⟨fun z hz p => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      obtain ⟨y, hy, hyz⟩ := hz
      obtain ⟨x, hx⟩ := p.2
      refine ⟨x * y * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · simpa using hKnorm x x.2 y (Subgroup.mem_subgroupOf.mp hy)
      · simp [map_mul, map_inv, hx, hyz]
    have hHne : (K'.map θ).subgroupOf θ.range ≠ ⊥ := by
      intro hbot
      have hkK' : (⟨k, hKN hkK⟩ : N) ∈ K' := Subgroup.mem_subgroupOf.mpr hkK
      have hmem : (⟨θ ⟨k, hKN hkK⟩, ⟨_, rfl⟩⟩ : θ.range) ∈ (K'.map θ).subgroupOf θ.range :=
        Subgroup.mem_subgroupOf.mpr ⟨_, hkK', rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hkD ((hθ _).mp (congrArg Subtype.val hmem))
    obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hHne)
    have hzK : (z : MulAut ↥(Ω.subgroupOf N)) ∈ K'.map θ :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp z.2).1
    have hzZ : ∀ d ∈ θ.range, d * (z : MulAut ↥(Ω.subgroupOf N)) = z * d := by
      intro d hd
      have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp z.2).2 ⟨d, hd⟩
      exact congrArg Subtype.val this
    have hz1' : ((z : θ.range) : MulAut ↥(Ω.subgroupOf N)) ≠ 1 := fun h1 =>
      hz1 (Subtype.ext (Subtype.ext h1))
    obtain hzc | hzc := eq_one_or_eq_of_central_of_card_eight hP8 ⟨tN, rfl⟩ ⟨uN, rfl⟩ hnc
      ⟨uvN, rfl⟩ hθuv1 hcen ((z : θ.range).2) hzZ
    · exact hz1' hzc
    rw [hzc] at hzK
    obtain ⟨k', hk'K, hk'⟩ := hzK
    have hdD : ((uvN⁻¹ * k' : N) : G) ∈ D :=
      (hθ _).mp (by rw [map_mul, map_inv, hk', inv_mul_cancel])
    obtain ⟨w, hw⟩ := exists_five_of_k_eq_two τ (hk 0) (by omega)
    refine false_of_index_le_four (dD := dD) hBidx ?_ w hw
    intro y hy
    have hyKD : (y : G) ∈ K ⊓ D := Subgroup.mem_subgroupOf.mp hy
    have h1 := hKc _ (Subgroup.mem_subgroupOf.mp hk'K) _ hyKD.1
    have h2 := hcommD _ hdD _ hyKD.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    have h3 : dD.uv⁻¹ * y = y * dD.uv⁻¹ := by
      rw [mul_assoc, h1, ← mul_assoc, ← mul_assoc] at h2
      exact mul_right_cancel h2
    calc (y : G) * dD.uv = dD.uv * (dD.uv⁻¹ * y) * dD.uv := by group
      _ = dD.uv * (y * dD.uv⁻¹) * dD.uv := by rw [h3]
      _ = dD.uv * y := by group
  ·
    have hidx4 : B.index ∣ 4 := by
      have hd : B.index ∣ 2 ^ (τ.k 0 + τ.k 1 + τ.k 2) := by
        rw [← dD.card]; exact B.index_dvd_card
      obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      rw [hjeq] at hBidx ⊢
      have hj2 : j ≤ 2 := by
        by_contra hj2
        have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact (Nat.pow_dvd_pow 2 hj2).trans (by norm_num)
    haveI : B.Normal := ⟨fun n _ g => by rwa [hcomm' g n, mul_inv_cancel_right]⟩
    have h4 : ∀ x : D, x ^ 4 ∈ B := by
      intro x
      obtain ⟨c, hc⟩ := hidx4
      rw [hc, pow_mul]
      exact Subgroup.pow_mem _ (Subgroup.pow_index_mem B x) _
    apply hkD
    refine hRmem k (hKN hkK) fun w hw => ?_
    obtain ⟨y, hyD, rfl⟩ := exists_pow_four_of_mem_omegaIn dD.e (n := τ.k 1 - 3)
      (fun i => by rw [hk i]; omega) hw
    have hyK : y ^ 4 ∈ K := by
      have := Subgroup.mem_subgroupOf.mp (h4 ⟨y, hyD⟩)
      simpa using this.1
    exact hKc _ hyK _ hkK

theorem StrothFrame.stroth_3_10' (F : StrothFrame G)
    (h223 : ∃ (D : Subgroup G) (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ),
      F.IsD D dD ∧ IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (h223X : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ')
      (X : Subgroup G), F.IsD D' dD' →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      IsMulCommutative X → F.A ≤ X → X ≤ (F.S : Subgroup G) →
      F.dA.L ≤ Subgroup.normalizer ((X ⊔ Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G) →
      ∃ (D₁ : Subgroup G) (τ₁ : StrothTypeIndex) (dD₁ : StrothWeakTypeData D₁ τ₁),
        F.IsD D₁ dD₁ ∧ IsSylowIn 2 (Subgroup.normalizer (D₁ : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D₁ : Set G)) ∧ Nat.card X ≤ Nat.card D₁)
    (h35 : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
      F.IsD D' dD' → τ'.m = τ'.n →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) = D' ∨
        ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
          F.dA.L ≤ Subgroup.normalizer
            ((X ⊔ Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G) ∧
          Nat.card D' < Nat.card X)
    (hcharB : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
      F.IsD D' dD' → τ'.m ≠ τ'.n →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      ∀ g ∈ (F.S : Subgroup G), g ∈ Subgroup.normalizer
          (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) : Subgroup G) : Set G) →
        g ∈ Subgroup.normalizer ((omegaIn 1 D' : Subgroup G) : Set G))
    (h226 : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ')
      (B : Subgroup G), F.IsD D' dD' →
      B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D' → (∃ g : G, B = D'.map (MulAut.conj g).toMonoidHom) → τ'.m = τ'.n) :
    ∃ (D : Subgroup G) (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ),
      F.IsD D dD ∧ IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) ∧
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) ∧
      (τ.m = τ.n → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D) ∧
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) :=
  F.stroth_3_10 h223 h223X h35
    (fun _ _ _ h' hτ' _ hR' _ hgS hgN => h'.mem_normalizer_of_mem_normalizer_normalizerIn hτ' hR'
      hgS hgN) hcharB h226

end Char

end CFSG.CGT.Stroth77
