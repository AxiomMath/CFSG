module

public import CFSG.GH74.GLS.Stage1.Thm4.Fstar98
public import CFSG.GH74.GLS.IVK.Lifted.Alt51d

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L96

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm4
  CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement

theorem twoCover_comp_mulEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H') {n : ℕ}
    {π : H' →* alternatingGroup (Fin n)} (hπ : TwoCover π) (hperf : Group.IsPerfect H) :
    TwoCover (π.comp e.toMonoidHom) where
  surj := hπ.surj.comp e.surjective
  ker_le_center := by
    intro x hx
    have hx' : e x ∈ π.ker := hx
    have hc := hπ.ker_le_center hx'
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact hc (e g)
  card_ker := by
    have h1 : (π.comp e.toMonoidHom).ker = π.ker.comap e.toMonoidHom :=
      (MonoidHom.comap_ker π e.toMonoidHom).symm
    rw [h1]
    have h2 : π.ker.comap e.toMonoidHom = π.ker.map e.symm.toMonoidHom := by
      ext x
      simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
      constructor
      · intro hx
        exact ⟨e x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [h2, Subgroup.card_map_of_injective e.symm.injective]
    exact hπ.card_ker
  perfect := hperf

theorem sign_eq_one_of_odd_orderOf {α : Type} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (h : Odd (orderOf σ)) : Equiv.Perm.sign σ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · exact h1
  · exfalso
    have h2 : Equiv.Perm.sign σ ^ orderOf σ = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [h1, h.neg_one_pow] at h2
    exact absurd h2 (by decide)

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}

omit [Finite G] in
theorem zpowers_subgroupOf_normal (z : G) : ((zpowers z).subgroupOf (Cz z)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : G) ∈ zpowers z := hn
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hn'
  rw [Subgroup.mem_subgroupOf]
  have : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
    rw [← hj]
    have hg : (g : G) * z = z * g := Subgroup.mem_centralizer_singleton_iff.1 g.2
    have : (g : G) * z ^ j = z ^ j * g :=
      ((Commute.zpow_right (show Commute (g : G) z from hg) j).eq)
    rw [this]; group
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [this]
  exact hn'

@[expose] noncomputable def phiK' (hK : K ≤ Cz z) : ↥K →* ↥(barOf z K) where
  toFun x := ⟨toBar z ⟨(x : G), hK x.2⟩, ⟨⟨(x : G), hK x.2⟩, x.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (toBar z)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (toBar z) ⟨(x : G), hK x.2⟩ ⟨(y : G), hK y.2⟩

omit [Finite G] in
theorem phiK'_surjective (hK : K ≤ Cz z) : Function.Surjective (phiK' hK) := by
  rintro ⟨_, c, hc, rfl⟩
  exact ⟨⟨(c : G), hc⟩, rfl⟩

theorem phiK'_ker (h : Ctx98 G Lh z t S K) : (phiK' h.K_le).ker = pPrimeCore 2 ↥K := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have h1 : toBar z ⟨(x : G), h.K_le x.2⟩ = 1 := congrArg Subtype.val hx
    have h2 : (x : G) ∈ Oz z :=
      (mem_Oz_iff (z := z) (c := ⟨(x : G), h.K_le x.2⟩)).2 ((QuotientGroup.eq_one_iff _).1 h1)
    have : (x : G) ∈ pPrimeCoreOf 2 K := by
      rw [← h.Oz_inf_K]; exact ⟨h2, x.2⟩
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  · intro hx
    have h2 : (x : G) ∈ Oz z := h.pPrimeCoreOf_le_Oz ⟨x, hx, rfl⟩
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).2 ((mem_Oz_iff (z := z) (c := ⟨(x : G), h.K_le x.2⟩)).1 h2)

@[expose] noncomputable def hatEquiv' (h : Ctx98 G Lh z t S K) : HatT K ≃* ↥(barOf z K) :=
  (QuotientGroup.quotientMulEquivOfEq (phiK'_ker h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (phiK' h.K_le) (phiK'_surjective h.K_le))

structure Act (h : Ctx98 G Lh z t S K) (n : ℕ) where
  ρ : ↥(Cz z) →* Equiv.Perm (Fin n)
  π : HatT K →* alternatingGroup (Fin n)
  cover : TwoCover π
  ρ_K : ∀ k : ↥K, ρ ⟨(k : G), h.K_le k.2⟩ =
    ((π (QuotientGroup.mk k) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
  ker_ρ : ∀ c : ↥(Cz z), ρ c = 1 → (c : G) ∈ zpowers z ⊔ Oz z
  ρ_Oz : ∀ c : ↥(Cz z), (c : G) ∈ Oz z → ρ c = 1

theorem isDoubleCoverOfAlt_hat (h : Ctx98 G Lh z t S K) {n : ℕ} (hcov : IsDoubleCoverOfAlt Lh n) :
    IsDoubleCoverOfAlt (HatT K) n := by
  obtain ⟨e⟩ := h.std.K_rigid.2
  exact isDoubleCoverOfAlt_congr e.symm hcov

theorem Act.exists (h : Ctx98 G Lh z t S K) {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hcov : IsDoubleCoverOfAlt Lh n) : Nonempty (Act h n) := by
  classical
  have hyp := h.hyp5B step9_8_fstar hn8 hn11 hcov
  obtain ⟨R⟩ := exists_permRep hyp
  have hcovHat : IsDoubleCoverOfAlt (HatT K) n := isDoubleCoverOfAlt_hat h hcov
  have hn4 : 4 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  have hzC : z ∈ Cz z := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzbar : toBar z ⟨z, hzC⟩ ∈ barOf z K := mem_barOf_iff.2 ⟨⟨z, hzC⟩, h.z_mem, rfl⟩
  have hz1 : toBar z ⟨z, hzC⟩ ≠ 1 :=
    mk'_ne_one_of_orderOf_two (N := pPrimeCore 2 ↥(Cz z)) odd_card_pPrimeCore
      (by rw [Subgroup.orderOf_mk]; exact h.z_ord)
  have hzker : (⟨toBar z ⟨z, hzC⟩, hzbar⟩ : ↥(barOf z K)) ∈ R.π.ker := by
    rw [MonoidHom.mem_ker]
    have hc : ∀ y : ↥(barOf z K),
        y * ⟨toBar z ⟨z, hzC⟩, hzbar⟩ = ⟨toBar z ⟨z, hzC⟩, hzbar⟩ * y := by
      intro y
      apply Subtype.ext
      obtain ⟨c, -, hc⟩ := mem_barOf_iff.1 y.2
      show (y : CentralizerBar z) * toBar z ⟨z, hzC⟩ = toBar z ⟨z, hzC⟩ * (y : CentralizerBar z)
      rw [← hc, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 c.2
    have hmem : R.π ⟨toBar z ⟨z, hzC⟩, hzbar⟩ ∈ center (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := R.cover.surj g
      rw [← map_mul, ← map_mul, hc y]
    rw [alternatingGroup.center_eq_bot hn4] at hmem
    exact hmem
  obtain ⟨zz, -, hzz1, -, hzzk⟩ := R.cover.exists_z
  have hzzeq : (⟨toBar z ⟨z, hzC⟩, hzbar⟩ : ↥(barOf z K)) = zz := by
    rcases hzzk _ hzker with h1 | h1
    · exact absurd (congrArg Subtype.val h1) hz1
    · exact h1
  refine ⟨{ ρ := R.ρ.comp (toBar z), π := R.π.comp (hatEquiv' h).toMonoidHom,
            cover := twoCover_comp_mulEquiv (hatEquiv' h) R.cover hcovHat.1.1, ρ_K := ?_,
            ker_ρ := ?_, ρ_Oz := ?_ }⟩
  · intro k
    show R.ρ (toBar z ⟨(k : G), h.K_le k.2⟩) = _
    have h1 : toBar z ⟨(k : G), h.K_le k.2⟩ =
        ((phiK' h.K_le k : ↥(barOf z K)) : CentralizerBar z) := rfl
    rw [h1, R.ρ_K]
    rfl
  · intro c hc
    have hc' : R.ρ (toBar z c) = 1 := hc
    obtain ⟨k, hk, hkπ⟩ := R.ker_ρ _ hc'
    have hkker : k ∈ R.π.ker := hkπ
    rcases hzzk k hkker with h1 | h1
    · have : toBar z c = 1 := by rw [← hk, h1]; rfl
      have h2 : c ∈ pPrimeCore 2 ↥(Cz z) := (QuotientGroup.eq_one_iff c).1 this
      exact Subgroup.mem_sup_right ((mem_Oz_iff (z := z)).2 h2)
    · have : toBar z c = toBar z ⟨z, hzC⟩ := by
        rw [← hk, h1, ← hzzeq]
      have h2 : (⟨z, hzC⟩ : ↥(Cz z))⁻¹ * c ∈ pPrimeCore 2 ↥(Cz z) := QuotientGroup.eq.1 this.symm
      have h3 : z⁻¹ * (c : G) ∈ Oz z := (mem_Oz_iff (z := z)).2 h2
      have h4 : (c : G) = z * (z⁻¹ * (c : G)) := by group
      rw [h4]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
        (Subgroup.mem_sup_right h3)
  · intro c hc
    show R.ρ (toBar z c) = 1
    have h1 : toBar z c = 1 := (QuotientGroup.eq_one_iff c).2 ((mem_Oz_iff (z := z)).1 hc)
    rw [h1, map_one]

section Basic

variable {h : Ctx98 G Lh z t S K} {n : ℕ} (A : Act h n)

include A

theorem Act.ker_eq_center (hcov : IsDoubleCoverOfAlt Lh n) : A.π.ker = center (HatT K) := by
  have hcovHat := isDoubleCoverOfAlt_hat h hcov
  have : Finite (HatT K) := inferInstance
  refine Subgroup.eq_of_le_of_card_ge A.cover.ker_le_center ?_
  rw [A.cover.card_ker, hcovHat.2.1]

theorem Act.sign_K (k : ↥K) : Equiv.Perm.sign (A.ρ ⟨(k : G), h.K_le k.2⟩) = 1 := by
  rw [A.ρ_K]
  exact Equiv.Perm.mem_alternatingGroup.mp (A.π (QuotientGroup.mk k)).2

theorem Act.exists_K (σ : Equiv.Perm (Fin n)) (hσ : Equiv.Perm.sign σ = 1) :
    ∃ k : ↥K, A.ρ ⟨(k : G), h.K_le k.2⟩ = σ := by
  obtain ⟨y, hy⟩ := A.cover.surj ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hσ⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨k, ?_⟩
  rw [A.ρ_K, hy]

theorem Act.mem_sup_subgroupOf {c : ↥(Cz z)} (hc : A.ρ c = 1) :
    c ∈ (zpowers z).subgroupOf (Cz z) ⊔ pPrimeCore 2 ↥(Cz z) := by
  have h1 := A.ker_ρ c hc
  have e : ((zpowers z).subgroupOf (Cz z) ⊔ pPrimeCore 2 ↥(Cz z)).map (Cz z).subtype =
      zpowers z ⊔ Oz z := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 rfl))]
    rfl
  rw [← e] at h1
  obtain ⟨y, hy, hyc⟩ := h1
  have : y = c := Subtype.ext hyc
  rwa [this] at hy

theorem Act.mem_zpowers_of_ker {c : ↥(Cz z)} (hc : A.ρ c = 1) {m : ℕ}
    (hcm : (c : G) ^ (2 ^ m) = 1) : (c : G) ∈ zpowers z := by
  have hc2 : c ^ (2 ^ m) = 1 := Subtype.ext (by simpa using hcm)
  have := zpowers_subgroupOf_normal z
  exact mem_of_mem_sup_odd (K := (zpowers z).subgroupOf (Cz z)) odd_card_pPrimeCore hc2
    (A.mem_sup_subgroupOf hc)

theorem Act.toBar_cases {c : ↥(Cz z)} (hc : A.ρ c = 1) :
    toBar z c = 1 ∨
      toBar z c = toBar z ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := by
  have hzC : z ∈ Cz z := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨y, hy, o, ho, hyo⟩ := (Subgroup.mem_sup_of_normal_right
    (s := (zpowers z).subgroupOf (Cz z)) (t := pPrimeCore 2 ↥(Cz z))).1 (A.mem_sup_subgroupOf hc)
  have hy' : (y : G) ∈ zpowers z := hy
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hy'
  have hyz : y = ⟨z, hzC⟩ ^ j := Subtype.ext (by rw [← hj]; simp)
  have hq : toBar z c = toBar z ⟨z, hzC⟩ ^ j := by
    have ho1 : toBar z o = 1 := (QuotientGroup.eq_one_iff o).2 ho
    rw [← hyo, map_mul, ho1, mul_one, hyz, map_zpow]
  have hz2 : toBar z ⟨z, hzC⟩ ^ (2 : ℤ) = 1 := by
    have : (⟨z, hzC⟩ : ↥(Cz z)) ^ (2 : ℤ) = 1 := by
      apply Subtype.ext
      have h2 : z ^ 2 = 1 := by rw [← h.z_ord]; exact pow_orderOf_eq_one z
      simpa using h2
    rw [← map_zpow, this, map_one]
  have hjj : j = j % 2 + 2 * (j / 2) := (Int.emod_add_mul_ediv j 2).symm
  rw [hq, hjj, zpow_add, zpow_mul, hz2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one j with h0 | h1
  · left
    rw [h0, zpow_zero]
  · right
    rw [h1, zpow_one]

theorem Act.mem_Oz_of_ker {c : ↥(Cz z)} (hc : A.ρ c = 1) {m : ℕ} (hm : Odd m)
    (hcm : (c : G) ^ m = 1) : (c : G) ∈ Oz z := by
  have hzC : z ∈ Cz z := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hc1 : c ^ m = 1 := Subtype.ext (by simpa using hcm)
  rcases A.toBar_cases hc with h1 | h1
  · exact (mem_Oz_iff (z := z)).2 ((QuotientGroup.eq_one_iff c).1 h1)
  · exfalso
    have h2 : toBar z c ^ m = 1 := by rw [← map_pow, hc1, map_one]
    have hzm : (⟨z, hzC⟩ : ↥(Cz z)) ^ m = ⟨z, hzC⟩ := by
      obtain ⟨k, rfl⟩ := hm
      apply Subtype.ext
      have h3 : z ^ 2 = 1 := by rw [← h.z_ord]; exact pow_orderOf_eq_one z
      simp only [Subgroup.coe_pow]
      rw [pow_succ, pow_mul, h3, one_pow, one_mul]
    rw [h1, ← map_pow, hzm] at h2
    exact mk'_ne_one_of_orderOf_two (N := pPrimeCore 2 ↥(Cz z)) odd_card_pPrimeCore
      (by rw [Subgroup.orderOf_mk]; exact h.z_ord) h2

theorem Act.mem_K_of_sign {c : ↥(Cz z)} (hc : Equiv.Perm.sign (A.ρ c) = 1) {m : ℕ}
    (hcm : (c : G) ^ (2 ^ m) = 1) : (c : G) ∈ K := by
  obtain ⟨k, hk⟩ := A.exists_K (A.ρ c) hc
  set c' : ↥(Cz z) := c * ⟨(k : G), h.K_le k.2⟩⁻¹ with hc'
  have hρ : A.ρ c' = 1 := by
    rw [hc', map_mul, map_inv, hk, mul_inv_cancel]
  have hcK : (c : G) ∈ K ⊔ Oz z := by
    have h1 := A.mem_sup_subgroupOf hρ
    have e : (c : G) = (c' : G) * (k : G) := by simp [hc']
    have h2 : (c' : G) ∈ zpowers z ⊔ Oz z := A.ker_ρ c' hρ
    have h3 : (c' : G) ∈ K ⊔ Oz z :=
      (sup_le_sup_right ((Subgroup.zpowers_le).2 h.z_mem) _) h2
    rw [e]
    exact Subgroup.mul_mem _ h3 (Subgroup.mem_sup_left k.2)
  have hc2 : (⟨(c : G), c.2⟩ : ↥(Cz z)) ^ (2 ^ m) = 1 := Subtype.ext (by simpa using hcm)
  have := h.K_normal_C
  have h4 := mem_sup_subgroupOf_of_mem h.K_le (c := c) hcK
  have hc3 : c ^ (2 ^ m) = 1 := Subtype.ext (by simpa using hcm)
  exact mem_of_mem_sup_odd (K := K.subgroupOf (Cz z)) (N := pPrimeCore 2 ↥(Cz z))
    odd_card_pPrimeCore hc3 h4

end Basic

end CFSG.GH74.GLS.Stage1.Thm4.L96
