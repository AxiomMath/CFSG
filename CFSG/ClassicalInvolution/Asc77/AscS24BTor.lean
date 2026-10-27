module

public import CFSG.ClassicalInvolution.Asc77.AscS24BQ
public import CFSG.ClassicalInvolution.Asc77.AscE184Cent
public import CFSG.ClassicalInvolution.Asc77.AscS24BMu

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] [Fact p.Prime] in
theorem eq_one_of_forall_pow {d : G} (hd : IsPGroup 2 (Subgroup.zpowers d))
    (h : ∀ k : ℕ, d ^ k * d ^ k = 1 → d ^ k = 1) : d = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hd) ⟨d, Subgroup.mem_zpowers d⟩
  rw [Subgroup.orderOf_mk] at hn
  rcases n with _ | n
  · simpa using hn
  · have h1 : d ^ (2 ^ n) * d ^ (2 ^ n) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', ← hn, pow_orderOf_eq_one]
    have h2 := h _ h1
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hn] at h3
    have h4 := Nat.le_of_dvd (by positivity) h3
    have h5 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem conjSub_eq_of_commute (hΩ : HypOmegaMod p f Ω) {J : Subgroup G} (hJ : J ∈ Ω) {x : G}
    (hx : x ∈ J) (o : orderOf x = 4) {w : G} (hw : w * x = x * w) : conjSub w J = J := by
  have hJw : conjSub w J ∈ Ω := hΩ.conjInvariant w J hJ
  have hxw : x ∈ conjSub w J := by
    rw [mem_conjSub_iff]
    have : w⁻¹ * x * w = x := by
      calc w⁻¹ * x * w = w⁻¹ * (x * w) := by group
        _ = w⁻¹ * (w * x) := by rw [hw]
        _ = x := by group
    rw [this]; exact hx
  have h2 : IsPGroup 2 ↥(Subgroup.zpowers x) := T7A.isPGroup_zpowers_of_orderOf_four o
  have h4 : 4 ≤ Nat.card ↥(Subgroup.zpowers x) := by rw [Nat.card_zpowers, o]
  exact hΩ.eq_of_le_of_le hJw hJ h2 h4 (Subgroup.zpowers_le.mpr hxw) (Subgroup.zpowers_le.mpr hx)

omit [Finite G] in
theorem le_centralizer_pow {X : Subgroup G} {d : G} (h : X ≤ Subgroup.centralizer ({d} : Set G))
    (k : ℕ) : X ≤ Subgroup.centralizer ({d ^ k} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : y * d = d * y := Subgroup.mem_centralizer_singleton_iff.mp (h hy)
  exact (Commute.pow_right h1 k).eq

namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

@[expose] def A : Subgroup G :=
  (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) ⊓ Subgroup.centralizer (R : Set G) ⊓
    Subgroup.normalizer (K' : Set G) ⊓ Subgroup.normalizer (C.D.F.ρ₃.K : Set G)

@[expose] def Dg : Subgroup G := C.A ⊓ Subgroup.centralizer (R' : Set G)

theorem mem_A {a : G} : a ∈ C.A ↔ a ∈ (S : Subgroup G) ∧ a ∈ Subgroup.centralizer (W : Set G) ∧
    a ∈ Subgroup.centralizer (R : Set G) ∧ a ∈ Subgroup.normalizer (K' : Set G) ∧
    a ∈ Subgroup.normalizer (C.D.F.ρ₃.K : Set G) := by
  simp only [A, Subgroup.mem_inf, and_assoc]

theorem A_le_S : C.A ≤ (S : Subgroup G) := fun _ h => ((C.mem_A).mp h).1

theorem A_le_centralizer_W : C.A ≤ Subgroup.centralizer (W : Set G) :=
  fun _ h => ((C.mem_A).mp h).2.1

theorem Dg_le_A : C.Dg ≤ C.A := inf_le_left

include C in
theorem inf_S_eq_R' : K' ⊓ (S : Subgroup G) = R' := by
  have hR'syl : IsSylow2In R' K' := T7C.isSylow2In_of_mem_RSet_of_le C.hs.stand.odd
    C.hs.stand.hyp C.hs.hK'.1 C.hd.hR'.1 C.hd.hR'.2.1
  exact hR'syl.2.2 _ inf_le_left S.isPGroup'.to_inf_right (le_inf C.hd.hR'.2.1 C.hd.hR'.2.2)

theorem card_R' : Nat.card ↥R' = 2 * Nat.card ↥(Subgroup.zpowers C.D.x₂) := by
  have h := Thompson.D_card C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW C.D.F.ρ'.hR
  rw [← C.D.h₂] at h
  exact (congrArg (fun X : Subgroup G => Nat.card ↥X) C.hR').symm.trans h

theorem t_not_mem_zpowers : C.D.F.ρ'.r ∉ Subgroup.zpowers C.D.x₂ := fun h =>
  C.D.F.ρ'.hrW ((Subgroup.zpowers_le.mpr C.D.x₂_mem) h)

theorem A_le_normalizer_R' : C.A ≤ Subgroup.normalizer (R' : Set G) := by
  intro a ha
  obtain ⟨haS, -, -, haK', -⟩ := (C.mem_A).mp ha
  rw [← C.inf_S_eq_R']
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyK, hyS⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp haK' y).mp hyK,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ haS hyS) (Subgroup.inv_mem _ haS)⟩
  · rintro ⟨hyK, hyS⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp haK' y).mpr hyK, ?_⟩
    have : y = a⁻¹ * (a * y * a⁻¹) * a := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ haS) hyS) haS

theorem A_le_centralizer_x₂ : C.A ≤ Subgroup.centralizer ({C.D.x₂} : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (C.A_le_centralizer_W ha) _ C.D.x₂_mem).symm

theorem A_le_centralizer_x₃ : C.A ≤ Subgroup.centralizer ({C.D.x₃} : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (C.A_le_centralizer_W ha) _ C.D.x₃_mem).symm

@[expose] noncomputable def lam : ↥C.A →* ↥(Subgroup.zpowers C.D.x₂) :=
  qHom (Subgroup.zpowers_le.mpr C.x₂_mem_R') C.card_R' C.t_mem_R' C.t_not_mem_zpowers
    C.A_le_normalizer_R' C.A_le_centralizer_x₂

theorem lam_apply (a : ↥C.A) :
    (C.lam a : G) = C.D.F.ρ'.r⁻¹ * ((a : G) * C.D.F.ρ'.r * (a : G)⁻¹) := rfl

theorem lam_eq_one_iff (a : ↥C.A) : C.lam a = 1 ↔ (a : G) ∈ C.Dg := by
  rw [lam, qHom_eq_one_iff]
  constructor
  · intro h
    refine ⟨a.2, ?_⟩
    show (a : G) ∈ Subgroup.centralizer (R' : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (h hy)
  · intro h y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp h.2 y hy

include C in
theorem W_le_normalizer (L : Subgroup G) (hL : L ∈ Ω) {x : G} (hx : x ∈ L ⊓ W)
    (o : orderOf x = 4) : W ≤ Subgroup.normalizer (L : Set G) := by
  intro w hw
  have hc : w * x = x * w :=
    Thompson.commutes_of_mem_WSet C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW w hw x hx.2
  exact mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_commute C.hs.stand.hyp hL hx.1 o hc)

theorem x₂_mem_A : C.D.x₂ ∈ C.A := by
  refine (C.mem_A).mpr ⟨C.hd.hWS C.D.x₂_mem, ?_, ?_, Subgroup.le_normalizer C.x₂_mem_K', ?_⟩
  · rw [Subgroup.mem_centralizer_iff]; intro w hw
    exact Thompson.commutes_of_mem_WSet C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW w hw _ C.D.x₂_mem
  · rw [Subgroup.mem_centralizer_iff]; intro y hy
    exact (C.commutes_R_R' y hy _ C.x₂_mem_R')
  · exact C.W_le_normalizer C.D.F.ρ₃.K C.D.F.ρ₃.hK ⟨C.x₃_mem_J, C.D.x₃_mem⟩ C.orderOf_x₃
      C.D.x₂_mem

theorem lam_x₂ : (C.lam ⟨_, C.x₂_mem_A⟩ : G) = z := by
  rw [lam_apply]
  have h1 : C.D.F.ρ'.r * C.D.x₂ * C.D.F.ρ'.r⁻¹ = C.D.x₂⁻¹ := C.D.t₂
  have h3 : C.D.F.ρ'.r * C.D.x₂⁻¹ * C.D.F.ρ'.r⁻¹ = C.D.x₂ := by
    rw [show C.D.F.ρ'.r * C.D.x₂⁻¹ * C.D.F.ρ'.r⁻¹ = (C.D.F.ρ'.r * C.D.x₂ * C.D.F.ρ'.r⁻¹)⁻¹ by
      group, h1, inv_inv]
  have h2 : C.D.F.ρ'.r⁻¹ * C.D.x₂ * C.D.F.ρ'.r = C.D.x₂⁻¹ := by
    conv_lhs => rw [← h3]
    group
  calc C.D.F.ρ'.r⁻¹ * (C.D.x₂ * C.D.F.ρ'.r * C.D.x₂⁻¹)
      = (C.D.F.ρ'.r⁻¹ * C.D.x₂ * C.D.F.ρ'.r) * C.D.x₂⁻¹ := by group
    _ = (C.D.x₂ ^ 2)⁻¹ := by rw [h2]; group
    _ = z := by rw [C.x₂_sq]; exact inv_eq_of_mul_eq_one_right C.hzK.sq

theorem exists_T3 : ∃ T₃ : Subgroup G, IsSylow2In T₃ C.D.F.ρ₃.K ∧ C.D.x₃ ∈ T₃ ∧
    T₃ ≤ Subgroup.normalizer (W : Set G) ∧ C.Dg ≤ Subgroup.normalizer (T₃ : Set G) := by
  set J := C.D.F.ρ₃.K with hJdef
  set H₁ := J ⊓ Subgroup.normalizer (W : Set G) with hH₁
  set Q := C.Dg ⊔ Subgroup.zpowers C.D.x₃ with hQdef
  have hx₃N : C.D.x₃ ∈ Subgroup.normalizer (W : Set G) := Subgroup.le_normalizer C.D.x₃_mem
  have hx₃H : C.D.x₃ ∈ H₁ := ⟨C.x₃_mem_J, hx₃N⟩
  have hQS : Q ≤ (S : Subgroup G) :=
    sup_le (C.Dg_le_A.trans C.A_le_S) (Subgroup.zpowers_le.mpr (C.hd.hWS C.D.x₃_mem))
  have hQ2 : IsPGroup 2 ↥Q := S.isPGroup'.to_le hQS
  have hDH : C.Dg ≤ Subgroup.normalizer (H₁ : Set G) := by
    intro d hd
    have hdA := C.Dg_le_A hd
    have hdJ : d ∈ Subgroup.normalizer (J : Set G) := ((C.mem_A).mp hdA).2.2.2.2
    have hdW : d ∈ Subgroup.normalizer (W : Set G) :=
      (Subgroup.centralizer_le_normalizer (W : Set G)) (C.A_le_centralizer_W hdA)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyJ, hyW⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hdJ y).mp hyJ,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hdW hyW) (Subgroup.inv_mem _ hdW)⟩
    · rintro ⟨hyJ, hyW⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hdJ y).mpr hyJ, ?_⟩
      have e : y = d⁻¹ * (d * y * d⁻¹) * d := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hdW) hyW) hdW
  have hQN : Q ≤ Subgroup.normalizer (H₁ : Set G) :=
    sup_le hDH (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hx₃H))
  have hNN : H₁ ⊔ Q ≤ Subgroup.normalizer (H₁ : Set G) := sup_le Subgroup.le_normalizer hQN
  obtain ⟨V, hV, hQV⟩ := IsSylow2In.exists_ge hQ2 (le_sup_right : Q ≤ H₁ ⊔ Q)
  have hVH : IsSylow2In (V ⊓ H₁) H₁ := isSylow2In_inf_of_le_normalizer hV le_sup_left hNN
  have hR₃H : IsSylow2In C.D.F.ρ₃.R H₁ :=
    ⟨le_inf C.D.F.ρ₃.hRK.1 C.D.F.ρ₃.hR.2, C.D.F.ρ₃.hRK.2.1,
      fun T hTH hT2 hRT => C.D.F.ρ₃.hRK.2.2 T (hTH.trans inf_le_left) hT2 hRT⟩
  have hTJ : IsSylow2In (V ⊓ H₁) J :=
    IsSylow2In.of_natCard_le C.D.F.ρ₃.hRK hVH.2.1 (hVH.1.trans inf_le_left)
      (le_of_eq (hR₃H.natCard_eq hVH))
  refine ⟨V ⊓ H₁, hTJ, ⟨hQV (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)), hx₃H⟩,
    fun y hy => hy.2.2, ?_⟩
  intro d hd
  have hdV : d ∈ V := hQV (Subgroup.mem_sup_left hd)
  have hdH : d ∈ Subgroup.normalizer (H₁ : Set G) := hQN (Subgroup.mem_sup_left hd)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyV, hyH⟩
    exact ⟨V.mul_mem (V.mul_mem hdV hyV) (V.inv_mem hdV),
      (Subgroup.mem_normalizer_iff.mp hdH y).mp hyH⟩
  · rintro ⟨hyV, hyH⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hdH y).mpr hyH⟩
    have e : y = d⁻¹ * (d * y * d⁻¹) * d := by group
    rw [e]
    exact V.mul_mem (V.mul_mem (V.inv_mem hdV) hyV) hdV

theorem exists_inj_D [IsSimpleGroup G] (h3 : H3 p f) :
    ∃ μ : ↥C.Dg →* ↥(Subgroup.zpowers C.D.x₃), Function.Injective μ := by
  obtain ⟨T₃, hT₃, hx₃T, hTW, hDN⟩ := C.exists_T3
  have hcard : Nat.card ↥T₃ = 2 * Nat.card ↥(Subgroup.zpowers C.D.x₃) := by
    rw [IsSylow2In.natCard_eq hT₃ C.D.F.ρ₃.hRK]
    have h := Thompson.D_card C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW C.D.F.ρ₃.hR
    rw [← C.D.h₃] at h
    exact h
  have hU : Subgroup.zpowers C.D.x₃ ≤ T₃ := Subgroup.zpowers_le.mpr hx₃T
  obtain ⟨s₃, hs₃, hs₃U⟩ : ∃ s₃ ∈ T₃, s₃ ∉ Subgroup.zpowers C.D.x₃ := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (fun y hy => hcon y hy : T₃ ≤ Subgroup.zpowers C.D.x₃)
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers C.D.x₃) := Nat.card_pos
    omega
  have hDC : C.Dg ≤ Subgroup.centralizer ({C.D.x₃} : Set G) :=
    C.Dg_le_A.trans C.A_le_centralizer_x₃
  refine ⟨qHom hU hcard hs₃ hs₃U hDN hDC, ?_⟩
  rw [injective_iff_map_eq_one]
  intro d hd
  have hT : T₃ ≤ Subgroup.centralizer ({(d : G)} : Set G) :=
    (qHom_eq_one_iff hU hcard hs₃ hs₃U hDN hDC d).mp hd
  have hdA := C.Dg_le_A d.2
  have hdR : R ≤ Subgroup.centralizer ({(d : G)} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp ((C.mem_A).mp hdA).2.2.1 y hy
  have hdR' : R' ≤ Subgroup.centralizer ({(d : G)} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp d.2.2 y hy
  apply Subtype.ext
  refine eq_one_of_forall_pow (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (C.A_le_S hdA)))
    fun k hk => ?_
  exact h3 G Ω K K' W S R R' z u C.hs C.hd C.h8 C.D C.hK C.hK' C.hR C.hR' _ hk
    (le_centralizer_pow hdR k) (le_centralizer_pow hdR' k) T₃ hT₃ hTW (le_centralizer_pow hT k)

include C in
theorem pow_four_of_mem_W {w : G} (hw : w ∈ W) : w ^ 4 = 1 := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  have h1 : C.D.x₁ ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, ← C.orderOf_x₁,
      pow_orderOf_eq_one]
  have h3 : C.D.x₃ ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, ← C.orderOf_x₃,
      pow_orderOf_eq_one]
  rw [(C.D.comm13.zpow_zpow a b).mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
    ← zpow_mul, mul_comm a, mul_comm b, zpow_mul, zpow_mul]
  push_cast
  rw [h1, h3, one_zpow, one_zpow, mul_one]

theorem s_conj_z : C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹ = z * C.D.F.j := by
  have e1 : C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹ = C.D.F.ρ₃.r * C.D.x₁ ^ 2 * C.D.F.ρ₃.r⁻¹ := by
    rw [C.x₁_sq]
  have e2 : C.D.F.ρ₃.r * C.D.x₁ ^ 2 * C.D.F.ρ₃.r⁻¹ = C.D.x₁ ^ 2 * C.D.x₃ ^ 2 := by
    rw [← conj_pow, C.D.s₁, C.D.comm13.mul_pow]
  have e3 : C.D.x₁ ^ 2 * C.D.x₃ ^ 2 = z * C.D.F.j := by
    rw [C.x₁_sq, C.x₃_sq]
  exact e1.trans (e2.trans e3)

theorem pow_four_ne_z {a : G} (ha : a ∈ C.A) : a ^ 4 ≠ z := by
  intro h4
  obtain ⟨-, haW, haR, haK', haJ⟩ := (C.mem_A).mp ha
  have haN : a ∈ Subgroup.normalizer (W : Set G) :=
    (Subgroup.centralizer_le_normalizer (W : Set G)) haW
  have haK : conjSub a C.D.F.ρ.K = C.D.F.ρ.K := by
    rw [C.hK]
    exact conjSub_eq_of_commute C.hs.stand.hyp C.hs.stand.mem C.x₁_mem_K C.orderOf_x₁
      (Subgroup.mem_centralizer_iff.mp haR _ C.x₁_mem_R).symm
  have hT : TrivMu Ω W a := C.trivMu_of_fix haN haK
    (by rw [C.hK']; exact mem_normalizer_iff_conjSub_eq.mp haK')
    (mem_normalizer_iff_conjSub_eq.mp haJ)
  set s := C.D.F.ρ₃.r with hsdef
  have hsM : s ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ₃.hR C.D.F.ρ₃.hr
  have hn := hT s hsM
  obtain ⟨w, hw, o, ho, hwo⟩ := Thompson.mem_sup_OCW_iff.mp (Subgroup.inv_mem _ hn)
  have hsa : s * a * s⁻¹ = w * o * a := by
    rw [hwo]; group
  have h1 : (s * a * s⁻¹) ^ 4 = z * C.D.F.j := by rw [conj_pow, h4]; exact C.s_conj_z
  have haON : a ∈ Subgroup.normalizer (OCW W : Set G) := Thompson.normalizer_le_normalizer_OCW W haN
  have hconj : ∀ k : ℕ, a ^ k * o * (a ^ k)⁻¹ ∈ OCW W := fun k =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ haON k) o).mp ho
  set o' := o * (a * o * a⁻¹) * (a ^ 2 * o * (a ^ 2)⁻¹) * (a ^ 3 * o * (a ^ 3)⁻¹) with ho'
  have ho'O : o' ∈ OCW W := by
    have h2 := hconj 1
    rw [pow_one] at h2
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ho h2) (hconj 2)) (hconj 3)
  have hwc : Commute w (o * a) := by
    refine Commute.mul_right ?_ ?_
    · exact (Subgroup.mem_centralizer_iff.mp (Thompson.OCW_le_centralizer W ho) w hw)
    · exact (Subgroup.mem_centralizer_iff.mp haW w hw)
  have hkey : (o * a) ^ 4 = o * (a * o * a⁻¹) * (a ^ 2 * o * (a ^ 2)⁻¹) *
      (a ^ 3 * o * (a ^ 3)⁻¹) * a ^ 4 := by
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]
    group
  have h2 : (w * o * a) ^ 4 = o' * a ^ 4 := by
    rw [mul_assoc, hwc.mul_pow, C.pow_four_of_mem_W hw, one_mul, hkey]
  rw [hsa, h2, h4] at h1
  have hj : C.D.F.j = o' := by
    have hzc : z * C.D.F.j = C.D.F.j * z := by
      have := Thompson.commutes_of_mem_WSet C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW z C.hd.hzW
        C.D.F.j (C.x₃_sq ▸ W.pow_mem C.D.x₃_mem 2)
      exact this
    calc C.D.F.j = C.D.F.j * z * z⁻¹ := by group
      _ = z * C.D.F.j * z⁻¹ := by rw [hzc]
      _ = o' * z * z⁻¹ := by rw [h1]
      _ = o' := by group
  have hj1 : C.D.F.j = 1 := by
    refine Asc77.eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) (hj ▸ ho'O) ?_
    exact (Thompson.isPGroup_of_mem_WSet C.hd.hW).to_le
      (Subgroup.zpowers_le.mpr (C.x₃_sq ▸ W.pow_mem C.D.x₃_mem 2))
  exact C.hjJ.ne_one hj1

end Ctx8

end S24B

end CFSG.ClassicalInvolution.Asc77
