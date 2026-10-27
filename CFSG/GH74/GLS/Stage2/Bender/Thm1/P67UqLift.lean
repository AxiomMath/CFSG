module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqBase
import CFSG.GH74.GLS.Stage2.OddAut.LinNSmall
import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.GLS.Stage2.OddAut CFSG.RankThree.PartOne.KFU CFSG.ClassicalGroups.UnitaryFlag

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem uq_exists_lifts (hn : 3 ≤ n) {r : ℕ} (hr : r.Prime)
    (V : Subgroup (MulAut (UqT h n))) (hVI : V ≤ primeFormD h ((1 : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K))
    (hVc : Nat.card V = r ^ 2) (hVe : ∀ v ∈ V, v ^ r = 1)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    ∃ (a b : UqU h n) (ua ub u : Kˣ),
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a ∈ V ∧
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b ∈ V ∧
      (a : GL (Fin n) K) ^ r = GeneralLinearGroup.scalar (Fin n) ua ∧
      (b : GL (Fin n) K) ^ r = GeneralLinearGroup.scalar (Fin n) ub ∧
      (a : GL (Fin n) K) * b = GeneralLinearGroup.scalar (Fin n) u * ((b : GL (Fin n) K) * a) ∧
      (∀ i j : ℕ, (∃ w : Kˣ, (a : GL (Fin n) K) ^ i * (b : GL (Fin n) K) ^ j =
        GeneralLinearGroup.scalar (Fin n) w) → r ∣ i ∧ r ∣ j) ∧
      ∀ v ∈ V, ∃ i j : ℕ, v = primeFormConjHom h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) (a ^ i * b ^ j) := by
  obtain ⟨v₁, hv₁, v₂, hv₂, hind, hspan⟩ := exists_basis_elemAbelian hr V hVc hVe hVab
  obtain ⟨a, rfl⟩ := hVI hv₁
  obtain ⟨b, rfl⟩ := hVI hv₂
  set c := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hc
  have hone : ∀ A : UqU h n, c A = 1 → ∃ w : Kˣ, (A : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) w := fun A hA => (uq_conj_eq_one_iff h hn A).1 hA
  have hcomm : c a * c b = c b * c a := hVab _ hv₁ _ hv₂
  obtain ⟨ua, hua⟩ := hone (a ^ r) (by rw [map_pow]; exact hVe _ hv₁)
  obtain ⟨ub, hub⟩ := hone (b ^ r) (by rw [map_pow]; exact hVe _ hv₂)
  obtain ⟨u, hu⟩ := hone (a * b * a⁻¹ * b⁻¹) (by
    simp only [map_mul, map_inv]
    rw [hcomm]
    group)
  refine ⟨a, b, ua, ub, u, hv₁, hv₂, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hua
  · simpa using hub
  · have hu' : (a : GL (Fin n) K) * b * (a : GL (Fin n) K)⁻¹ * (b : GL (Fin n) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin n) u := by simpa using hu
    calc (a : GL (Fin n) K) * b = ((a : GL (Fin n) K) * b * (a : GL (Fin n) K)⁻¹ *
          (b : GL (Fin n) K)⁻¹) * b * a := by group
      _ = GeneralLinearGroup.scalar (Fin n) u * ((b : GL (Fin n) K) * a) := by
          rw [hu', mul_assoc]
  · rintro i j ⟨w, hw⟩
    apply hind
    have := (uq_conj_eq_one_iff h hn (a ^ i * b ^ j)).2 ⟨w, by simpa using hw⟩
    rw [map_mul, map_pow, map_pow] at this
    exact this
  · intro v hv
    obtain ⟨i, j, hij⟩ := hspan v hv
    exact ⟨i, j, by rw [hij, map_mul, map_pow, map_pow]⟩

theorem uq_norm_one_of_pow {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr1 : r ∣ p ^ f + 1) {c : K}
    (hc : c ≠ 0) (hcr : (h.bar c * c) ^ r = 1) : h.bar c * c = 1 := by
  set g : K := h.bar c * c with hg
  have hg0 : g ≠ 0 := mul_ne_zero ((map_ne_zero h.bar).mpr hc) hc
  have hbg : h.bar g = g := by
    rw [hg, map_mul, h.bar_bar, mul_comm]
  have hgq : g ^ (p ^ f) = g := by rw [← h.bar_apply]; exact hbg
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hgq1 : g ^ (p ^ f - 1) = 1 := by
    have : g ^ (p ^ f - 1) * g = g := by
      rw [← pow_succ, Nat.sub_add_cancel hq1, hgq]
    exact mul_right_cancel₀ hg0 (by rw [this, one_mul])
  have hcop : Nat.Coprime r (p ^ f - 1) := by
    refine (Nat.Prime.coprime_iff_not_dvd hr).2 fun hd => ?_
    have h2 : r ∣ (p ^ f + 1) - (p ^ f - 1) := Nat.dvd_sub hr1 hd
    have h3 : (p ^ f + 1) - (p ^ f - 1) = 2 := by omega
    rw [h3] at h2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
  have := (pow_gcd_eq_one (a := g)).2 ⟨hcr, hgq1⟩
  rwa [hcop, pow_one] at this

theorem uq_eig_pow {K : Type} [Field K] {n r : ℕ} {x B : Matrix (Fin n) (Fin n) K}
    {d : Fin n → K} {α : K} (hB : IsUnit B) (hx : x * B = B * Matrix.diagonal d)
    (hxr : x ^ r = α • (1 : Matrix (Fin n) (Fin n) K)) (k : Fin n) : d k ^ r = α := by
  have h1 : x ^ r * B = B * Matrix.diagonal (d ^ r) := mul_pow_diag_n hx r
  rw [hxr, Matrix.smul_mul, Matrix.one_mul] at h1
  have h2 : B * (α • (1 : Matrix (Fin n) (Fin n) K)) = α • B := by
    rw [Matrix.mul_smul, Matrix.mul_one]
  have h3 : B * (α • (1 : Matrix (Fin n) (Fin n) K)) = B * Matrix.diagonal (d ^ r) := by
    rw [h2, h1]
  have h4 := hB.mul_left_cancel h3
  have := congrFun (congrFun h4 k) k
  simpa using this.symm

theorem uq_toral_frame {r : ℕ} (hn : 3 ≤ n) (hrn : n < 2 * r) (hr : r.Prime) (hr2 : r ≠ 2)
    (hr1 : r ∣ p ^ f + 1) (a b : UqU h n) (ua ub : Kˣ)
    (hau : (a : GL (Fin n) K) ^ r = GeneralLinearGroup.scalar (Fin n) ua)
    (hbu : (b : GL (Fin n) K) ^ r = GeneralLinearGroup.scalar (Fin n) ub)
    (hab : (a : GL (Fin n) K) * b = (b : GL (Fin n) K) * a)
    (hind : ∀ i j : ℕ, (∃ w : Kˣ, (a : GL (Fin n) K) ^ i * (b : GL (Fin n) K) ^ j =
      GeneralLinearGroup.scalar (Fin n) w) → r ∣ i ∧ r ∣ j) :
    ∃ (E a' b' : UqU h n),
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a' =
        primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a ∧
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b' =
        primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b ∧
      ∀ i j : ℕ, ∃ d : Fin n → K,
        (((a' ^ i * b' ^ j : UqU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d := by
  classical
  have : Finite K := h.finite
  have hn0 : 0 < n := by omega
  set c := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hc
  have haM : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ r = (ua : K) •
      (1 : Matrix (Fin n) (Fin n) K) := by
    rw [← Units.val_pow_eq_pow_val, hau, coe_scalar_smul_n]
  have hbM : ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ r = (ub : K) •
      (1 : Matrix (Fin n) (Fin n) K) := by
    rw [← Units.val_pow_eq_pow_val, hbu, coe_scalar_smul_n]
  have habM : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← Units.val_mul, ← Units.val_mul, hab]
  have hindM : ∀ (i j : ℕ) (c : K), c ≠ 0 →
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ i *
        ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ j = c • (1 : Matrix (Fin n) (Fin n) K) →
      r ∣ i ∧ r ∣ j := by
    intro i j c hc0 hij
    apply hind i j
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hij,
      coe_scalar_smul_n]
    rfl
  have hrK : r ∣ Nat.card K - 1 := by
    have h1 : Nat.card K - 1 = (p ^ f + 1) * (p ^ f - 1) := by
      rw [h.card_eq_sq]
      have := Nat.mul_self_sub_mul_self_eq (p ^ f) 1
      rw [sq]
      simpa using this
    rw [h1]
    exact Dvd.dvd.mul_right hr1 _
  obtain ⟨B, da, db, hB, h1, h2⟩ := lin_comm_diag_n hr hn0 hrn hrK _ _ (ua : K) (ub : K)
    ua.ne_zero ub.ne_zero haM hbM habM hindM
  have hBu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 hB
  set k0 : Fin n := ⟨0, hn0⟩ with hk0
  have hla : da k0 ^ r = ua := uq_eig_pow hBu h1 haM k0
  have hlb : db k0 ^ r = ub := uq_eig_pow hBu h2 hbM k0
  have hla0 : da k0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow hr.ne_zero] at hla
    exact ua.ne_zero hla.symm
  have hlb0 : db k0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow hr.ne_zero] at hlb
    exact ub.ne_zero hlb.symm
  have hNua : h.bar (ua : K) * ua = 1 :=
    (uq_scalar_mem_iff h hn0 ua).1 (by rw [← hau]; exact pow_mem a.2 r)
  have hNub : h.bar (ub : K) * ub = 1 :=
    (uq_scalar_mem_iff h hn0 ub).1 (by rw [← hbu]; exact pow_mem b.2 r)
  have hNla : h.bar (da k0) * da k0 = 1 := by
    refine uq_norm_one_of_pow h hr hr2 hr1 hla0 ?_
    rw [mul_pow, ← map_pow, hla]
    exact hNua
  have hNlb : h.bar (db k0) * db k0 = 1 := by
    refine uq_norm_one_of_pow h hr hr2 hr1 hlb0 ?_
    rw [mul_pow, ← map_pow, hlb]
    exact hNub
  set la : Kˣ := Units.mk0 (da k0) hla0 with hladef
  set lb : Kˣ := Units.mk0 (db k0) hlb0 with hlbdef
  have hNla' : h.bar ((la⁻¹ : Kˣ) : K) * ((la⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv]
    show (h.bar (da k0) * da k0)⁻¹ = 1
    rw [hNla, inv_one]
  have hNlb' : h.bar ((lb⁻¹ : Kˣ) : K) * ((lb⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv]
    show (h.bar (db k0) * db k0)⁻¹ = 1
    rw [hNlb, inv_one]
  set sa : UqU h n := ⟨GeneralLinearGroup.scalar (Fin n) la⁻¹, (uq_scalar_mem_iff h hn0 _).2 hNla'⟩
    with hsa
  set sb : UqU h n := ⟨GeneralLinearGroup.scalar (Fin n) lb⁻¹, (uq_scalar_mem_iff h hn0 _).2 hNlb'⟩
    with hsb
  have hcsa : c sa = 1 := (uq_conj_eq_one_iff h hn sa).2 ⟨la⁻¹, rfl⟩
  have hcsb : c sb = 1 := (uq_conj_eq_one_iff h hn sb).2 ⟨lb⁻¹, rfl⟩
  have hscen : ∀ (s : Kˣ) (g : GL (Fin n) K), Commute g (GeneralLinearGroup.scalar (Fin n) s) :=
    fun s g => (scalar_commute_n s g).symm
  set a' : UqU h n := sa * a with ha'
  set b' : UqU h n := sb * b with hb'
  have ha'c : (a' : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) la⁻¹ * (a : GL (Fin n) K) :=
    rfl
  have hb'c : (b' : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) lb⁻¹ * (b : GL (Fin n) K) :=
    rfl
  have ha'r : a' ^ r = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ha'c, (scalar_commute_n _ _).mul_pow, hau, ← map_pow, ← map_mul,
      inv_pow]
    have : (la : K) ^ r = ua := hla
    have hh : la ^ r = ua := Units.ext this
    rw [hh, inv_mul_cancel, map_one]
    rfl
  have hb'r : b' ^ r = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hb'c, (scalar_commute_n _ _).mul_pow, hbu, ← map_pow, ← map_mul,
      inv_pow]
    have : (lb : K) ^ r = ub := hlb
    have hh : lb ^ r = ub := Units.ext this
    rw [hh, inv_mul_cancel, map_one]
    rfl
  have hab' : a' * b' = b' * a' := by
    apply Subtype.ext
    show (a' : GL (Fin n) K) * (b' : GL (Fin n) K) = (b' : GL (Fin n) K) * (a' : GL (Fin n) K)
    rw [ha'c, hb'c]
    have hc1 : Commute (a : GL (Fin n) K) (b : GL (Fin n) K) := hab
    have h1 : Commute (a : GL (Fin n) K)
        (GeneralLinearGroup.scalar (Fin n) lb⁻¹ * (b : GL (Fin n) K)) :=
      (scalar_commute_n lb⁻¹ _).symm.mul_right hc1
    exact ((scalar_commute_n la⁻¹ _).mul_left h1).eq
  set G : Subgroup (UqU h n) := Subgroup.closure {a', b'} with hG
  have hcommG : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    have hpw : ({a', b'} : Set (UqU h n)).Pairwise Commute := by
      intro x hx y hy _
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact Commute.refl _
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hab'
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hab'.symm
      · rw [Set.mem_singleton_iff] at hx hy
        rw [hx, hy]
    have hcc := Subgroup.isMulCommutative_closure hpw
    intro x hx y hy
    have := hcc.is_comm.comm (⟨x, hx⟩ : Subgroup.closure ({a', b'} : Set (UqU h n))) ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hpowG : ∀ x ∈ G, x ^ r = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ha'r
      · exact hb'r
    | one => exact one_pow r
    | mul x y hx hy ihx ihy =>
      rw [(show Commute x y from hcommG x hx y hy).mul_pow, ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h hr hr1 G hcommG hpowG
  refine ⟨P, a', b', ?_, ?_, fun i j => ?_⟩
  · rw [ha', map_mul, hcsa, one_mul]
  · rw [hb', map_mul, hcsb, one_mul]
  · have hmem : a' ^ i * b' ^ j ∈ G :=
      G.mul_mem (G.pow_mem (Subgroup.subset_closure (Or.inl rfl)) i)
        (G.pow_mem (Subgroup.subset_closure (Or.inr rfl)) j)
    have hD := hP _ hmem
    set x : UqU h n := a' ^ i * b' ^ j with hx
    set D : Matrix (Fin n) (Fin n) K :=
      (((P⁻¹ * x * P : UqU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hDdef
    have hxP : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * D := by
      have e : (x : GL (Fin n) K) * (P : GL (Fin n) K) =
          (P : GL (Fin n) K) * ((P : GL (Fin n) K)⁻¹ * (x : GL (Fin n) K) * (P : GL (Fin n) K)) :=
        by group
      have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) e
      simpa [hDdef] using this
    refine ⟨D.diag, ?_⟩
    rw [hD.diagonal_diag]
    exact hxP

theorem uq_plane_classify {r : ℕ} (hn : 3 ≤ n) (hrn : n < 2 * r) (hr : r.Prime) (hr2 : r ≠ 2)
    (hr1 : r ∣ p ^ f + 1) (V : Subgroup (MulAut (UqT h n)))
    (hVI : V ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hVc : Nat.card V = r ^ 2) (hVe : ∀ v ∈ V, v ^ r = 1)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    (∃ E : UqU h n, ∀ v ∈ V, ∃ (x : UqU h n) (d : Fin n → K),
        v = primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x ∧
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((E : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) =
          ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d) ∨
      (r ∣ n ∧ ∃ (a b : UqU h n) (u : Kˣ), u ≠ 1 ∧
        primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a ∈ V ∧
        primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b ∈ V ∧
        (a : GL (Fin n) K) * b = GeneralLinearGroup.scalar (Fin n) u * ((b : GL (Fin n) K) * a) ∧
        ∀ v ∈ V, ∃ i j : ℕ, v = primeFormConjHom h ((1 : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) (a ^ i * b ^ j)) := by
  have hn0 : 0 < n := by omega
  obtain ⟨a, b, ua, ub, u, ha, hb, hau, hbu, hab, hind, hspan⟩ :=
    uq_exists_lifts h hn hr V hVI hVc hVe hVab
  by_cases hu : u = 1
  · left
    rw [hu, map_one, one_mul] at hab
    obtain ⟨E, a', b', hca, hcb, hdiag⟩ :=
      uq_toral_frame h hn hrn hr hr2 hr1 a b ua ub hau hbu hab hind
    refine ⟨E, fun v hv => ?_⟩
    obtain ⟨i, j, hij⟩ := hspan v hv
    obtain ⟨d, hd⟩ := hdiag i j
    refine ⟨a' ^ i * b' ^ j, d, ?_, hd⟩
    rw [hij, map_mul, map_pow, map_pow, map_mul, map_pow, map_pow, hca, hcb]
  · right
    refine ⟨?_, a, b, u, hu, ha, hb, hab, hspan⟩
    by_contra hdn
    have hcop : Nat.Coprime n r := ((Nat.Prime.coprime_iff_not_dvd hr).2 hdn).symm
    exact hu (units_eq_one_of_coprime hcop (comm_scalar_pow_n_dim hab)
      (comm_scalar_pow_n hn0 hab hbu))

end CFSG.GH74.GLS.Stage2.Bender.Thm1
