module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.Quasithin.Background.B6Defs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFBlockLiftBasic
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open scoped commutatorElement

section OddGeneration

variable {G : Type*} [Group G]

private theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using this

private theorem le_normalizer_of_forall_conj_mem {S M : Subgroup G}
    (h : ∀ g ∈ S, ∀ x ∈ M, g * x * g⁻¹ ∈ M) : S ≤ Subgroup.normalizer (M : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h g hg y, fun hy => ?_⟩
  have := h g⁻¹ (S.inv_mem hg) _ hy
  simpa [mul_assoc] using this

private theorem conj_mem_closure {S : Set G} {g : G}
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ Subgroup.closure S) {k : G} (hk : k ∈ Subgroup.closure S) :
    g * k * g⁻¹ ∈ Subgroup.closure S := by
  induction hk using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]; exact (Subgroup.closure S).mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]; exact (Subgroup.closure S).inv_mem hx

theorem le_normalizer_of_closure_odd {S K : Subgroup G}
    (hK : K ≤ Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)})
    (h : ∀ g ∈ S, ∀ x ∈ K, Odd (orderOf x) → g * x * g⁻¹ ∈ K) :
    S ≤ Subgroup.normalizer (K : Set G) := by
  have hcl : Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} ≤ K :=
    (Subgroup.closure_le K).2 fun x hx => hx.1
  have key : ∀ g ∈ S, ∀ k ∈ K, g * k * g⁻¹ ∈ K := fun g hg k hk =>
    hcl (conj_mem_closure (fun x hx => hK (h g hg x hx.1 hx.2)) (hK hk))
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (S.inv_mem hg) _ hy
  simpa [mul_assoc] using this

private theorem exists_pow_two_odd [Finite G] (h : G) : ∃ a : ℕ, Odd (orderOf (h ^ 2 ^ a)) := by
  set a := (orderOf h).factorization 2 with ha
  refine ⟨a, ?_⟩
  have hmodd : Odd (orderOf h / 2 ^ a) := by
    have : ¬ 2 ∣ orderOf h / 2 ^ a := Nat.not_dvd_ordCompl Nat.prime_two (orderOf_pos h).ne'
    exact Nat.odd_iff.mpr (by omega)
  have : orderOf (h ^ 2 ^ a) = orderOf h / 2 ^ a := by
    rw [orderOf_pow' _ (by positivity)]
    have hg : Nat.gcd (orderOf h) (2 ^ a) = 2 ^ a := Nat.gcd_eq_right (Nat.ordProj_dvd _ _)
    rw [hg]
  rw [this]; exact hmodd

theorem le_closure_odd_of_twoResidual_eq [Finite G] {K : Subgroup G} (h : twoResidual K = K) :
    K ≤ Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} := by
  set M : Subgroup G := Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} with hM
  have hMK : M ≤ K := (Subgroup.closure_le K).2 fun x hx => hx.1
  have hgen : ∀ g ∈ K, ∀ x ∈ {x : G | x ∈ K ∧ Odd (orderOf x)}, g * x * g⁻¹ ∈ M := fun g hg x hx =>
    Subgroup.subset_closure ⟨K.mul_mem (K.mul_mem hg hx.1) (K.inv_mem hg), by
      rw [orderOf_conj_eq]; exact hx.2⟩
  have hKM : K ≤ Subgroup.normalizer (M : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_closure (hgen g hg) hy, fun hy => ?_⟩
    have := conj_mem_closure (hgen g⁻¹ (K.inv_mem hg)) hy
    simpa [mul_assoc] using this
  have h2 : ∀ y ∈ K, ∃ k : ℕ, y ^ 2 ^ k ∈ M := by
    intro y hy
    obtain ⟨a, ha⟩ := exists_pow_two_odd y
    exact ⟨a, Subgroup.subset_closure ⟨K.pow_mem hy _, ha⟩⟩
  calc K = twoResidual K := h.symm
    _ ≤ M := twoResidual_le_of_isTwoQuotient hMK hKM h2

theorem twoResidual_eq_of_isShort2 [Finite G] {K : Subgroup G} (hK : IsShort2 K) :
    twoResidual K = K := by
  refine le_antisymm (twoResidual_le K) ((le_closure_odd_of_isShort2 hK).trans
    ((Subgroup.closure_le _).2 fun x hx => ?_))
  rw [SetLike.mem_coe, mem_twoResidual_iff]
  intro N _ _ hq
  obtain ⟨k, hk⟩ := hq x hx.1
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hx.2) : Nat.Coprime (2 ^ k) (orderOf x))
  rw [← hj]
  exact N.pow_mem hk j

private theorem exists_mul_eq_of_coprime {x : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (hx : orderOf x = a * b) :
    ∃ y z : G, y ∈ Subgroup.zpowers x ∧ z ∈ Subgroup.zpowers x ∧ x = y * z ∧
      orderOf y ∣ a ∧ orderOf z ∣ b := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  have hxab : x ^ (a * b) = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  refine ⟨x ^ (v * (b : ℤ)), x ^ (u * (a : ℤ)), Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _,
    Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _, ?_, ?_, ?_⟩
  · have : v * (b : ℤ) + u * a = 1 := by linarith
    rw [← zpow_add, this, zpow_one]
  · apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul]
    have : v * (b : ℤ) * a = ((a * b : ℕ) : ℤ) * v := by push_cast; ring
    rw [this, zpow_mul, zpow_natCast, hxab, one_zpow]
  · apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul]
    have : u * (a : ℤ) * b = ((a * b : ℕ) : ℤ) * u := by push_cast; ring
    rw [this, zpow_mul, zpow_natCast, hxab, one_zpow]

theorem commutator_le_commutator_commutator_of_odd [Finite G] {R K : Subgroup G}
    (hR : IsPGroup 2 R) (hKR : K ≤ Subgroup.normalizer (R : Set G))
    (hK : K ≤ Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)}) : ⁅R, K⁆ ≤ ⁅⁅R, K⁆, K⁆ := by
  have hKN : K ≤ Subgroup.normalizer (⁅⁅R, K⁆, K⁆ : Subgroup G) :=
    Subgroup.normalizer_commutator_ge_right _ _
  have hcl : Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} ≤ K :=
    (Subgroup.closure_le K).2 fun x hx => hx.1
  have hmul : ∀ a b : G, a ∈ K → (∀ r ∈ R, ⁅r, a⁆ ∈ (⁅⁅R, K⁆, K⁆ : Subgroup G)) →
      (∀ r ∈ R, ⁅r, b⁆ ∈ (⁅⁅R, K⁆, K⁆ : Subgroup G)) →
      ∀ r ∈ R, ⁅r, a * b⁆ ∈ (⁅⁅R, K⁆, K⁆ : Subgroup G) := by
    intro a b ha hA hB r hr
    have e : ⁅r, a * b⁆ = ⁅r, a⁆ * (a * ⁅r, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (hA r hr) ((Subgroup.mem_normalizer_iff.mp (hKN ha) _).mp (hB r hr))
  have hodd : ∀ m : ℕ, ∀ x ∈ K, orderOf x = m → Odd m →
      ∀ r ∈ R, ⁅r, x⁆ ∈ (⁅⁅R, K⁆, K⁆ : Subgroup G) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hx hxm hmodd
      by_cases hm1 : m = 1
      · subst hm1
        have hx1 : x = 1 := orderOf_eq_one_iff.mp hxm
        subst hx1
        intro r _
        simp
      · have hm0 : m ≠ 0 := by rw [← hxm]; exact (orderOf_pos x).ne'
        obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
        have hq2 : q ≠ 2 := by
          rintro rfl
          exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hqm)
        obtain ⟨e, b, hqb, hmeb⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 q hq.ne_one
        have hcop : Nat.Coprime (q ^ e) b := ((Nat.Prime.coprime_iff_not_dvd hq).2 hqb).pow_left e
        have he0 : e ≠ 0 := by
          rintro rfl
          rw [pow_zero, one_mul] at hmeb
          exact hqb (hmeb ▸ hqm)
        have hb0 : b ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hmeb
          exact hm0 hmeb
        have hqe : 1 < q ^ e := Nat.one_lt_pow he0 hq.one_lt
        by_cases hb1 : b = 1
        ·
          subst hb1
          have hordq : orderOf x = q ^ e := by rw [hxm, hmeb, mul_one]
          have hAK : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.2 hx
          have : Fact q.Prime := ⟨hq⟩
          have hAp : IsPGroup q (Subgroup.zpowers x) := by
            rw [IsPGroup.iff_card]
            exact ⟨e, by rw [Nat.card_zpowers, hordq]⟩
          have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent q hq
            (Subgroup.zpowers x) R hAp (not_dvd_card_of_isPGroup_two hq hq2 hR) (hAK.trans hKR)
          intro r hr
          have h1 : ⁅r, x⁆ ∈ (⁅R, Subgroup.zpowers x⁆ : Subgroup G) :=
            Subgroup.commutator_mem_commutator hr (Subgroup.mem_zpowers x)
          rw [← hidem] at h1
          exact Subgroup.commutator_mono (Subgroup.commutator_mono_right hAK) hAK h1
        · have hb2 : 1 < b := by omega
          have hordx : orderOf x = q ^ e * b := hxm.trans hmeb
          obtain ⟨y, z, hyx, hzx, hxyz, hy, hz⟩ := exists_mul_eq_of_coprime hcop hordx
          have hyK : y ∈ K := Subgroup.zpowers_le.2 hx hyx
          have hzK : z ∈ K := Subgroup.zpowers_le.2 hx hzx
          have hy_odd : Odd (orderOf y) :=
            Odd.of_dvd_nat hmodd (hy.trans (Dvd.intro b hmeb.symm))
          have hz_odd : Odd (orderOf z) :=
            Odd.of_dvd_nat hmodd (hz.trans (Dvd.intro_left (q ^ e) hmeb.symm))
          have h1 : q ^ e < m := by rw [hmeb]; exact lt_mul_of_one_lt_right (by omega) hb2
          have h2 : b < m := by rw [hmeb]; exact lt_mul_of_one_lt_left (by omega) hqe
          have hy_lt : orderOf y < m := lt_of_le_of_lt (Nat.le_of_dvd (by omega) hy) h1
          have hz_lt : orderOf z < m := lt_of_le_of_lt (Nat.le_of_dvd (by omega) hz) h2
          have hyN := ih (orderOf y) hy_lt y hyK rfl hy_odd
          have hzN := ih (orderOf z) hz_lt z hzK rfl hz_odd
          intro r hr
          rw [hxyz]
          exact hmul y z hyK hyN hzN r hr
  have key : ∀ k ∈ Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)},
      ∀ r ∈ R, ⁅r, k⁆ ∈ (⁅⁅R, K⁆, K⁆ : Subgroup G) := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem x hx => exact fun r hr => hodd _ x hx.1 rfl hx.2 r hr
    | one => intro r _; simp
    | mul x y hxc _ hx hy => exact hmul x y (hcl hxc) hx hy
    | inv x hxc hx =>
      intro r hr
      have e : ⁅r, x⁻¹⁆ = x⁻¹ * ⁅r, x⁆⁻¹ * x := by
        simp only [commutatorElement_def]; group
      rw [e]
      have h1 : ⁅r, x⁆⁻¹ ∈ (⁅⁅R, K⁆, K⁆ : Subgroup G) := Subgroup.inv_mem _ (hx r hr)
      have := (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem (hcl hxc))) _).mp h1
      simpa using this
  rw [Subgroup.commutator_le]
  intro r hr k hk
  exact key k (hK hk) r hr

end OddGeneration

section Subnormal

variable {G : Type*} [Group G] [Finite G]

theorem conj_mem_of_isSubnormal_of_pGroup {N S : Subgroup G} [N.Normal] (hN : IsPGroup 2 N)
    (hS : S.IsSubnormal) {x : G} (hx : x ∈ S) (hodd : Odd (orderOf x)) {n : G} (hn : n ∈ N) :
    n * x * n⁻¹ ∈ S := by
  induction hS generalizing x with
  | top => exact Subgroup.mem_top _
  | step S M hle hM hnormal ih =>
    have hMN : M ≤ Subgroup.normalizer (S : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hnormal
    have hxM : x ∈ M := hle hx
    have hyM : n * x * n⁻¹ ∈ M := ih hxM hodd
    have h1 : x * n⁻¹ * x⁻¹ ∈ N := ‹N.Normal›.conj_mem n⁻¹ (N.inv_mem hn) x
    have heN : n * x * n⁻¹ * x⁻¹ ∈ N := by
      have e : n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) := by group
      rw [e]; exact N.mul_mem hn h1
    have heM : n * x * n⁻¹ * x⁻¹ ∈ M := M.mul_mem hyM (M.inv_mem hxM)
    refine mem_of_odd_eq_two_mul (N := S) (x := n * x * n⁻¹) (o := n * x * n⁻¹ * x⁻¹) (c := x)
      (hMN hyM) (hMN heM) hx (by group) ?_ (exists_orderOf_two_pow hN heN)
    rw [orderOf_conj_eq]; exact hodd

end Subnormal

section SubnormalSubgroup

variable {X : Type} [Group X] [Finite X]

theorem le_normalizer_of_isSubnormal_of_odd {H K R : Subgroup X} (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal)
    (hK : K ≤ Subgroup.closure {x : X | x ∈ K ∧ Odd (orderOf x)})
    (hRH : R ≤ H) (hHR : H ≤ Subgroup.normalizer (R : Set X)) (hR : IsPGroup 2 R) :
    R ≤ Subgroup.normalizer (K : Set X) := by
  have hN : (R.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).2 hHR
  have hR' : IsPGroup 2 (R.subgroupOf H) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm
  refine le_normalizer_of_closure_odd hK fun r hr x hx hodd => ?_
  have := conj_mem_of_isSubnormal_of_pGroup (N := R.subgroupOf H) hR' hsub
    (x := ⟨x, hKH hx⟩) (Subgroup.mem_subgroupOf.2 hx) (by rwa [Subgroup.orderOf_mk])
    (n := ⟨r, hRH hr⟩) (Subgroup.mem_subgroupOf.2 hr)
  exact Subgroup.mem_subgroupOf.1 this

theorem le_normalizer_of_isSubnormal_of_pGroup {H K R : Subgroup X} (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal) (hK : twoResidual K = K) (hRH : R ≤ H)
    (hHR : H ≤ Subgroup.normalizer (R : Set X)) (hR : IsPGroup 2 R) :
    R ≤ Subgroup.normalizer (K : Set X) :=
  le_normalizer_of_isSubnormal_of_odd hKH hsub (le_closure_odd_of_twoResidual_eq hK) hRH hHR hR

end SubnormalSubgroup

section Setting

variable {X : Type} [Group X] {T : Subgroup X}

theorem normal_pCoreOf_top : (pCoreOf 2 (⊤ : Subgroup X)).Normal :=
  Subgroup.normalizer_eq_top_iff.1
    (top_le_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤))

theorem normal_gnV (T : Subgroup X) : (gnV T).Normal := Subgroup.normalClosure_normal

@[expose] def gnD (T : Subgroup X) : Subgroup X where
  carrier := {x | ∀ q ∈ pCoreOf 2 (⊤ : Subgroup X), x * q * x⁻¹ * q⁻¹ ∈ gnV T}
  one_mem' := fun q _ => by simp
  mul_mem' := by
    intro x y hx hy q hq
    have e : x * y * q * (x * y)⁻¹ * q⁻¹ =
        (x * (y * q * y⁻¹ * q⁻¹) * x⁻¹) * (x * q * x⁻¹ * q⁻¹) := by group
    rw [e]
    exact (gnV T).mul_mem ((normal_gnV T).conj_mem _ (hy q hq) x) (hx q hq)
  inv_mem' := by
    intro x hx q hq
    have e : x⁻¹ * q * x⁻¹⁻¹ * q⁻¹ = x⁻¹ * (x * q * x⁻¹ * q⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact (normal_gnV T).conj_mem _ ((gnV T).inv_mem (hx q hq)) x⁻¹

theorem le_gnD_iff {A : Subgroup X} :
    A ≤ gnD T ↔ ⁅pCoreOf 2 (⊤ : Subgroup X), A⁆ ≤ gnV T := by
  rw [Subgroup.commutator_le]
  constructor
  · intro h q hq a ha
    have e : ⁅q, a⁆ = (a * q * a⁻¹ * q⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact (gnV T).inv_mem (h ha q hq)
  · intro h a ha q hq
    have e : a * q * a⁻¹ * q⁻¹ = ⁅q, a⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact (gnV T).inv_mem (h q hq a ha)

theorem normal_gnD (T : Subgroup X) : (gnD T).Normal where
  conj_mem x hx g q hq := by
    have hQ := normal_pCoreOf_top (X := X)
    have hq' : g⁻¹ * q * g ∈ pCoreOf 2 (⊤ : Subgroup X) := by
      simpa using hQ.conj_mem q hq g⁻¹
    have h := (normal_gnV T).conj_mem _ (hx _ hq') g
    have e : g * x * g⁻¹ * q * (g * x * g⁻¹)⁻¹ * q⁻¹ =
        g * (x * (g⁻¹ * q * g) * x⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ := by group
    rw [e]; exact h

theorem pCoreOf_le_gnC_of_le (hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T) :
    pCoreOf 2 (⊤ : Subgroup X) ≤ gnC T := by
  have := normal_pCoreOf_top (X := X)
  have hZ : omegaOneCenterOf T ≤ Subgroup.centralizer (pCoreOf 2 (⊤ : Subgroup X) : Set X) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    exact Subgroup.centralizer_le hQT hx.1.2
  exact Subgroup.le_centralizer_iff.1 (Subgroup.normalClosure_le_normal hZ)

theorem omegaOneCenterOf_le_pCoreOf_of_le (hC : CharTwo (⊤ : Subgroup X))
    (hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T) :
    omegaOneCenterOf T ≤ pCoreOf 2 (⊤ : Subgroup X) := by
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  exact hC ⟨Subgroup.mem_top x, Subgroup.centralizer_le hQT hx.1.2⟩

theorem gnV_le_pCoreOf_of_le (hC : CharTwo (⊤ : Subgroup X))
    (hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T) : gnV T ≤ pCoreOf 2 (⊤ : Subgroup X) := by
  have := normal_pCoreOf_top (X := X)
  exact Subgroup.normalClosure_le_normal (omegaOneCenterOf_le_pCoreOf_of_le hC hQT)

variable [Finite X]

theorem omegaOneCenterOf_le_pCoreOf (hX : GNSetting X T) :
    omegaOneCenterOf T ≤ pCoreOf 2 (⊤ : Subgroup X) :=
  omegaOneCenterOf_le_pCoreOf_of_le hX.charTwo (B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow)

theorem gnV_le_pCoreOf (hX : GNSetting X T) : gnV T ≤ pCoreOf 2 (⊤ : Subgroup X) :=
  gnV_le_pCoreOf_of_le hX.charTwo (B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow)

theorem pCoreOf_le_gnC (hX : GNSetting X T) : pCoreOf 2 (⊤ : Subgroup X) ≤ gnC T :=
  pCoreOf_le_gnC_of_le (B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow)

end Setting

section DInfC

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

private theorem isPGroup_two_of_forall_orderOf_prime {G : Type*} [Group G] [Finite G]
    {R : Subgroup G} (h : ∀ x ∈ R, ∀ p : ℕ, p.Prime → p ≠ 2 → orderOf x = p → False) :
    IsPGroup 2 R := by
  rw [IsPGroup.iff_card]
  by_contra hnot
  obtain ⟨p, hp, hpd, hp2⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card R ∧ p ≠ 2 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    refine ⟨(Nat.card R).primeFactorsList.length, ?_⟩
    refine Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := R)).ne' ?_
    intro q hq hqd
    exact hcon q hq hqd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) p hpd
  exact h x x.2 p hp hp2 (by rw [Subgroup.orderOf_coe, hx])

theorem centralizer_quot_inf_le (hX : GNSetting X T) :
    gnD T ⊓ gnC T ≤ pCoreOf 2 (⊤ : Subgroup X) := by
  have hQn := normal_pCoreOf_top (X := X)
  have hDn := normal_gnD T
  have hQ2 : IsPGroup 2 (pCoreOf 2 (⊤ : Subgroup X)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
  have hR2 : IsPGroup 2 (gnD T ⊓ gnC T : Subgroup X) := by
    refine isPGroup_two_of_forall_orderOf_prime fun x hxR p hp hp2 hxo => ?_
    have : Fact p.Prime := ⟨hp⟩
    have hAR : Subgroup.zpowers x ≤ gnD T ⊓ gnC T := Subgroup.zpowers_le.2 hxR
    have hAp : IsPGroup p (Subgroup.zpowers x) := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [Nat.card_zpowers, hxo]; simp⟩
    have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp
      (Subgroup.zpowers x) (pCoreOf 2 (⊤ : Subgroup X)) hAp
      (not_dvd_card_of_isPGroup_two hp hp2 hQ2) Subgroup.le_normalizer_of_normal
    have hQAV := le_gnD_iff.1 (hAR.trans inf_le_left)
    have hAC : Subgroup.zpowers x ≤ gnC T := hAR.trans inf_le_right
    have hbot : ⁅pCoreOf 2 (⊤ : Subgroup X), Subgroup.zpowers x⁆ = ⊥ := by
      rw [← hidem, eq_bot_iff]
      refine (Subgroup.commutator_mono hQAV le_rfl).trans ?_
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.2 hAC).le
    have hxc : x ∈ Subgroup.centralizer (pCoreOf 2 (⊤ : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have : ⁅q, x⁆ ∈ ⁅pCoreOf 2 (⊤ : Subgroup X), Subgroup.zpowers x⁆ :=
        Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers _)
      rw [hbot, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    have hxQ : x ∈ pCoreOf 2 (⊤ : Subgroup X) := hX.charTwo ⟨Subgroup.mem_top _, hxc⟩
    obtain ⟨k, hk⟩ := exists_orderOf_two_pow hQ2 hxQ
    rw [hxo] at hk
    have h2 : p ∣ 2 ^ k := hk ▸ dvd_refl p
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top
    Subgroup.le_normalizer_of_normal hR2

end DInfC

section Blocks

variable {X : Type} [Group X] [Finite X] {T H K : Subgroup X}

theorem pCoreOf_le_normalizer_of_isBlock2_q (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K) :
    pCoreOf 2 (⊤ : Subgroup X) ≤ Subgroup.normalizer (K : Set X) := by
  have hQn := normal_pCoreOf_top (X := X)
  exact le_normalizer_of_isSubnormal_of_odd hK.2.1 hK.2.2 (le_closure_odd_of_isShort2 hK.1)
    hQH Subgroup.le_normalizer_of_normal
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤)

theorem gnV_le_normalizer_of_isBlock2_q (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K) :
    gnV T ≤ Subgroup.normalizer (K : Set X) :=
  (gnV_le_pCoreOf hX).trans (pCoreOf_le_normalizer_of_isBlock2_q hQH hK)

theorem commutator_le_blockU_of_normalizes {R : Subgroup X} (hK : IsShort2 K)
    (hR2 : IsPGroup 2 R) (hRK : R ≤ Subgroup.normalizer (K : Set X))
    (hKR : K ≤ Subgroup.normalizer (R : Set X)) : ⁅R, K⁆ ≤ blockU K := by
  have hRK' : ⁅R, K⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_right.1 hRK
  have hKR' : ⁅R, K⁆ ≤ R := Subgroup.le_normalizer_iff_commutator_le_left.1 hKR
  have h1 : ⁅R, K⁆ ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRK'
      (Subgroup.normalizer_commutator_ge_right R K) (hR2.to_le hKR')
  exact (commutator_le_commutator_commutator_of_odd hR2 hKR
    (le_closure_odd_of_isShort2 hK)).trans (Subgroup.commutator_mono h1 le_rfl)

theorem blockU_le_commutator_of_le_pCoreOf {W : Subgroup X} [W.Normal]
    (hWQ : W ≤ pCoreOf 2 (⊤ : Subgroup X)) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K) (hKC : ¬ K ≤ Subgroup.centralizer (W : Set X)) : blockU K ≤ ⁅W, K⁆ := by
  have hQ2 : IsPGroup 2 (pCoreOf 2 (⊤ : Subgroup X)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
  have hV2 : IsPGroup 2 W := hQ2.to_le hWQ
  have hKV : K ≤ Subgroup.normalizer (W : Set X) := Subgroup.le_normalizer_of_normal
  have hVK : W ≤ Subgroup.normalizer (K : Set X) :=
    hWQ.trans (pCoreOf_le_normalizer_of_isBlock2_q hQH hK)
  have hshort := hK.1
  have hodd := le_closure_odd_of_isShort2 hshort
  have hAU : ⁅W, K⁆ ≤ blockU K := commutator_le_blockU_of_normalizes hshort hV2 hVK hKV
  have hKA : K ≤ Subgroup.normalizer (⁅W, K⁆ : Subgroup X) :=
    Subgroup.normalizer_commutator_ge_right _ _
  have hAZ : ¬ ⁅W, K⁆ ≤ blockZ K := by
    intro h
    have h0 : ⁅⁅W, K⁆, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (h.trans inf_le_right)
    have h3 := commutator_le_commutator_commutator_of_odd hV2 hKV hodd
    rw [h0, le_bot_iff, Subgroup.commutator_comm] at h3
    exact hKC (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3)
  have hZc : blockZ K ≤ Subgroup.centralizer (K : Set X) := inf_le_right
  have hKZ : K ≤ Subgroup.normalizer (blockZ K : Set X) :=
    (Subgroup.le_centralizer_iff.1 hZc).trans (Subgroup.centralizer_le_normalizer _)
  have hUK : blockU K ≤ K :=
    Subgroup.commutator_le_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K) le_rfl
  have hZK : blockZ K ≤ K := inf_le_left.trans hUK
  have hW : ⁅W, K⁆ ⊔ blockZ K = blockU K := by
    rcases hshort.2.2.2.2.2 (⁅W, K⁆ ⊔ blockZ K) le_sup_right (sup_le hAU inf_le_left)
        (fun y hy => mem_normalizer_sup (hKA hy) (hKZ hy)) with h | h
    · exact absurd (le_sup_left.trans h.le) hAZ
    · exact h
  have hUV : ⁅blockU K, K⁆ ≤ ⁅W, K⁆ := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    rw [← hW] at hu
    have hu' : u ∈ ((⁅W, K⁆ ⊔ blockZ K : Subgroup X) : Set X) := hu
    have hZN : blockZ K ≤ Subgroup.normalizer (⁅W, K⁆ : Subgroup X) :=
      fun z hz => hKA (hZK hz)
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZN] at hu'
    obtain ⟨a, ha, z, hz, rfl⟩ := hu'
    have hzk : k * z = z * k := Subgroup.mem_centralizer_iff.1 (hZc hz) k hk
    have h1 : z * k * z⁻¹ = k := by rw [← hzk]; group
    have e : ⁅a * z, k⁆ = a * (z * k * z⁻¹) * a⁻¹ * k⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, h1]
    exact Subgroup.le_normalizer_iff_commutator_le_left.1 hKA
      (Subgroup.commutator_mem_commutator ha hk)
  exact (commutator_le_commutator_commutator_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K) hodd).trans hUV

theorem blockU_le_commutator_gnV_q (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T) : blockU K ≤ ⁅gnV T, K⁆ :=
  haveI := normal_gnV T
  blockU_le_commutator_of_le_pCoreOf (gnV_le_pCoreOf hX) hQH hK hKC

theorem commutator_gnV_eq_blockU_q (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T) : ⁅gnV T, K⁆ = blockU K := by
  have := normal_gnV T
  exact le_antisymm (commutator_le_blockU_of_normalizes hK.1
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤).to_le (gnV_le_pCoreOf hX))
    (gnV_le_normalizer_of_isBlock2_q hX hQH hK) Subgroup.le_normalizer_of_normal)
    (blockU_le_commutator_gnV_q hX hQH hK hKC)

theorem blockU_le_gnV_q (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T) : blockU K ≤ gnV T := by
  have := normal_gnV T
  exact (blockU_le_commutator_gnV_q hX hQH hK hKC).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.1 Subgroup.le_normalizer_of_normal)

theorem blockU_le_gnV_sup_blockZ_q (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T) : blockU K ≤ gnV T ⊔ blockZ K :=
  (blockU_le_gnV_q hX hQH hK hKC).trans le_sup_left

theorem gnImg_blockU_eq_bot_q (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T) : gnImg T (blockU K) = ⊥ := by
  rw [gnImg, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact (blockU_le_gnV_q hX hQH hK hKC).trans ((gnV_le_pCoreOf hX).trans (pCoreOf_le_gnC hX))

theorem commutator_pCoreOf_le_of_le_pCoreOf {W : Subgroup X} [W.Normal]
    (hWQ : W ≤ pCoreOf 2 (⊤ : Subgroup X)) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K) (hKC : ¬ K ≤ Subgroup.centralizer (W : Set X)) :
    ⁅pCoreOf 2 (⊤ : Subgroup X), K⁆ ≤ W := by
  have hQn := normal_pCoreOf_top (X := X)
  exact (commutator_le_blockU_of_normalizes hK.1 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤)
    (pCoreOf_le_normalizer_of_isBlock2_q hQH hK) Subgroup.le_normalizer_of_normal).trans
    ((blockU_le_commutator_of_le_pCoreOf hWQ hQH hK hKC).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.1 Subgroup.le_normalizer_of_normal))

theorem commutator_pCoreOf_le_gnV_q (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T) : ⁅pCoreOf 2 (⊤ : Subgroup X), K⁆ ≤ gnV T :=
  haveI := normal_gnV T
  commutator_pCoreOf_le_of_le_pCoreOf (gnV_le_pCoreOf hX) hQH hK hKC

theorem gnC_le_normalizer_of_isBlock2_q (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T) : gnC T ≤ Subgroup.normalizer (K : Set X) := by
  have hDn := normal_gnD T
  have hKD : K ≤ gnD T := le_gnD_iff.2 (commutator_pCoreOf_le_gnV_q hX hQH hK hKC)
  have hQK := pCoreOf_le_normalizer_of_isBlock2_q hQH hK
  have hQ2 : IsPGroup 2 (pCoreOf 2 (⊤ : Subgroup X)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
  refine le_normalizer_of_closure_odd (le_closure_odd_of_isShort2 hK.1) fun g hg x hx hodd => ?_
  have hrD : g * x * g⁻¹ * x⁻¹ ∈ gnD T :=
    (gnD T).mul_mem (hDn.conj_mem x (hKD hx) g) ((gnD T).inv_mem (hKD hx))
  have hrC : g * x * g⁻¹ * x⁻¹ ∈ gnC T := by
    have e : g * x * g⁻¹ * x⁻¹ = g * (x * g⁻¹ * x⁻¹) := by group
    rw [e]
    exact (gnC T).mul_mem hg ((gnC_normal T).conj_mem g⁻¹ ((gnC T).inv_mem hg) x)
  have hrQ : g * x * g⁻¹ * x⁻¹ ∈ pCoreOf 2 (⊤ : Subgroup X) :=
    centralizer_quot_inf_le hX ⟨hrD, hrC⟩
  have hrN := hQK hrQ
  refine mem_of_odd_eq_two_mul (N := K) (x := g * x * g⁻¹) (o := g * x * g⁻¹ * x⁻¹) (c := x)
    ?_ hrN hx (by group) ?_ (exists_orderOf_two_pow hQ2 hrQ)
  · have e : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact Subgroup.mul_mem _ hrN (Subgroup.le_normalizer hx)
  · rw [orderOf_conj_eq]; exact hodd

theorem le_normal_of_block_q (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T) : (K.subgroupOf (K ⊔ gnC T)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
    (sup_le Subgroup.le_normalizer (gnC_le_normalizer_of_isBlock2_q hX hQH hK hKC))

@[expose] def IsChiBlockGN {G : Type*} [Group G] (H L : Subgroup G) : Prop :=
  IsBlock2 H L ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsAltType L m)

private theorem isSubnormal_comap {X Y : Type*} [Group X] [Group Y] {A B : Subgroup Y}
    (h : IsSubnormal A B) (f : X →* Y) : IsSubnormal (A.comap f) (B.comap f) :=
  h.comap f

theorem false_of_block_subnormal_q (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsChiBlockGN H K)
    (hKC : ¬ K ≤ gnC T) (hsub : IsSubnormal (gnImg T K) ⊤) : False := by
  have h1 := isSubnormal_comap hsub (QuotientGroup.mk' (gnC T))
  rw [Subgroup.comap_top, gnImg, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  have h2 : IsSubnormal K ⊤ :=
    IsSubnormal.step le_sup_left (le_normal_of_block_q hX hQH hK.1 hKC) h1
  refine hX.noXBlock K h2 ⟨hK.1.1, ?_⟩
  rcases hK.2 with ⟨n, hn, hlin⟩ | ⟨m, hm, hm3, halt⟩
  · exact Or.inl ⟨n, hn.le, hlin⟩
  · obtain ⟨k, rfl⟩ := hm
    exact Or.inr ⟨k, by omega, halt⟩

theorem inf_gnC_le_pCoreOf_q (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K)
    (hKC : ¬ K ≤ gnC T) : K ⊓ gnC T ≤ pCoreOf 2 K := by
  have hQn := normal_pCoreOf_top (X := X)
  have hQ2 : IsPGroup 2 (pCoreOf 2 (⊤ : Subgroup X)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
  have hKD : K ≤ gnD T := le_gnD_iff.2 (commutator_pCoreOf_le_gnV_q hX hQH hK hKC)
  have hle : K ⊓ gnC T ≤ K ⊓ pCoreOf 2 (⊤ : Subgroup X) :=
    le_inf inf_le_left
      ((le_inf (inf_le_left.trans hKD) inf_le_right).trans (centralizer_quot_inf_le hX))
  refine hle.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    (hQ2.to_le inf_le_right))
  intro g hg
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
    Subgroup.le_normalizer_of_normal (Subgroup.mem_top g)⟩

omit [Finite X] in
theorem gnImg_le_closure_odd {K : Subgroup X}
    (hK : K ≤ Subgroup.closure {x : X | x ∈ K ∧ Odd (orderOf x)}) :
    gnImg T K ≤ Subgroup.closure {y : X ⧸ gnC T | y ∈ gnImg T K ∧ Odd (orderOf y)} := by
  refine (Subgroup.map_mono hK).trans ?_
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxK, hxodd⟩, rfl⟩
  exact ⟨Subgroup.mem_map_of_mem _ hxK, Odd.of_dvd_nat hxodd (orderOf_map_dvd _ x)⟩

theorem commutator_gnImg_eq_bot_q (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K)
    {N : Subgroup (X ⧸ gnC T)} (hN2 : IsPGroup 2 N)
    (hPN : gnImg T K ≤ Subgroup.normalizer (N : Set (X ⧸ gnC T)))
    (hNP : N ≤ Subgroup.normalizer (gnImg T K : Set (X ⧸ gnC T))) :
    ⁅N, gnImg T K⁆ = ⊥ := by
  by_cases hKC : K ≤ gnC T
  · have : gnImg T K = ⊥ := by
      rw [gnImg, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']; exact hKC
    rw [this, Subgroup.commutator_bot_right]
  have hO2 : IsPGroup 2 (pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hNP' : ⁅N, gnImg T K⁆ ≤ gnImg T K :=
    Subgroup.le_normalizer_iff_commutator_le_right.1 hNP
  have hPN' : ⁅N, gnImg T K⁆ ≤ N := Subgroup.le_normalizer_iff_commutator_le_left.1 hPN
  have hE : N ⊓ gnImg T K ≤ gnImg T (pCoreOf 2 K) := by
    have hPE : gnImg T K ≤
        Subgroup.normalizer ((N ⊓ gnImg T K : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) :=
      fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hPN hg, Subgroup.le_normalizer hg⟩
    let Ê : Subgroup X := K ⊓ (N ⊓ gnImg T K).comap (QuotientGroup.mk' (gnC T))
    have hÊK : Ê ≤ K := inf_le_left
    have hKÊ : K ≤ Subgroup.normalizer (Ê : Set X) := by
      refine le_normalizer_of_forall_conj_mem fun k hk e he => ⟨K.mul_mem (K.mul_mem hk he.1)
        (K.inv_mem hk), Subgroup.mem_comap.2 ?_⟩
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hPE (Subgroup.mem_map_of_mem _ hk)) _).mp
        (Subgroup.mem_comap.1 he.2)
    have hÊ2 : IsPGroup 2 Ê := by
      rw [IsPGroup.iff_orderOf]
      rintro ⟨e, he⟩
      have heK : e ∈ K := he.1
      have hpe : QuotientGroup.mk' (gnC T) e ∈ N := (Subgroup.mem_comap.1 he.2).1
      obtain ⟨a, ha⟩ := exists_orderOf_two_pow hN2 hpe
      have h1 : e ^ 2 ^ a ∈ gnC T := by
        rw [← QuotientGroup.ker_mk' (gnC T), MonoidHom.mem_ker, map_pow, ← ha]
        exact pow_orderOf_eq_one _
      have h2 : e ^ 2 ^ a ∈ pCoreOf 2 K :=
        inf_gnC_le_pCoreOf_q hX hQH hK hKC ⟨K.pow_mem heK _, h1⟩
      obtain ⟨b, hb⟩ := exists_orderOf_two_pow hO2 h2
      have h3 : orderOf e ∣ 2 ^ (a + b) := by
        apply orderOf_dvd_of_pow_eq_one
        rw [pow_add, pow_mul, ← hb]
        exact pow_orderOf_eq_one _
      obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
      exact ⟨c, by rw [Subgroup.orderOf_mk, hc]⟩
    have hÊle : Ê ≤ pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hÊK hKÊ hÊ2
    intro y hy
    obtain ⟨hyN, hyP⟩ := hy
    obtain ⟨k, hkK, rfl⟩ := hyP
    exact ⟨k, hÊle ⟨hkK, hyN, Subgroup.mem_map_of_mem _ hkK⟩, rfl⟩
  have hcentral : ⁅gnImg T (pCoreOf 2 K), gnImg T K⁆ = ⊥ := by
    have h := gnImg_blockU_eq_bot_q hX hQH hK hKC
    rw [gnImg, blockU, blockQ, Subgroup.map_commutator] at h
    exact h
  have h1 := commutator_le_commutator_commutator_of_odd hN2 hPN
    (gnImg_le_closure_odd (le_closure_odd_of_isShort2 hK.1))
  have h2 : ⁅⁅N, gnImg T K⁆, gnImg T K⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (Subgroup.commutator_mono ((le_inf hPN' hNP').trans hE) le_rfl).trans hcentral.le
  rw [eq_bot_iff]
  exact h1.trans h2.le

theorem commutator_eq_bot_of_pGroup_q (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    {r : ℕ}
    {K : Fin r → Subgroup X} (hK : ∀ i, IsChiBlockGN H (K i))
    (hKK : ∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) (hres : twoResidual H = ⨆ i, K i)
    {N : Subgroup (X ⧸ gnC T)} (hN : N ≤ gnImg T (twoResidual H))
    (hNn : gnImg T (twoResidual H) ≤ Subgroup.normalizer (N : Set (X ⧸ gnC T)))
    (hN2 : IsPGroup 2 N) : ⁅N, gnImg T (twoResidual H)⁆ = ⊥ := by
  have hL : gnImg T (twoResidual H) = ⨆ i, gnImg T (K i) := by
    rw [hres]; exact Subgroup.map_iSup _ _
  rw [hL] at hN hNn ⊢
  have hcomm : ∀ i j, i ≠ j →
      gnImg T (K j) ≤ Subgroup.centralizer (gnImg T (K i) : Set (X ⧸ gnC T)) := by
    intro i j hij
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.1 ?_
    unfold gnImg
    rw [← Subgroup.map_commutator, hKK j i hij.symm]
    exact Subgroup.map_bot _
  have hNP : ∀ i, N ≤ Subgroup.normalizer (gnImg T (K i) : Set (X ⧸ gnC T)) := by
    intro i
    refine hN.trans (iSup_le fun j => ?_)
    by_cases hji : j = i
    · subst hji; exact Subgroup.le_normalizer
    · exact (hcomm i j (Ne.symm hji)).trans (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  refine iSup_le fun i => ?_
  have h := commutator_gnImg_eq_bot_q hX hQH (hK i).1 hN2
    ((le_iSup (fun j => gnImg T (K j)) i).trans hNn) (hNP i)
  rw [Subgroup.commutator_comm] at h
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h

theorem false_of_block_subnormal (hX : GNSetting X T) (hTH : T ≤ H) (hK : IsChiBlockGN H K)
    (hKC : ¬ K ≤ gnC T) (hsub : IsSubnormal (gnImg T K) ⊤) : False :=
  false_of_block_subnormal_q hX ((B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow).trans hTH) hK hKC hsub

end Blocks

end CFSG.AGLEmbeddingD2.GN
