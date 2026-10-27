module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43Cfg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf42U3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Lift

variable {T : Type} [Group T] [Finite T] {X : Subgroup T}

theorem mk_ne_one_of_mul_self {x : T} (hx : x ∈ X) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ((⟨x, hx⟩ : ↥X) : SecQuot X) ≠ 1 := by
  intro h
  apply hx1
  have h1 : (⟨x, hx⟩ : ↥X) ∈ classicalInvolutionOddCore ↥X := (QuotientGroup.eq_one_iff _).mp h
  have h2 : (⟨x, hx⟩ : ↥X) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
  exact congrArg Subtype.val (eq_one_of_mem_classicalInvolutionOddCore_of_mul_self h1 h2)

theorem orderOf_mk_eq_four {k : T} (hk : k ∈ X) (hk4 : orderOf k = 4) :
    orderOf ((⟨k, hk⟩ : ↥X) : SecQuot X) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set k' : ↥X := ⟨k, hk⟩ with hk'
  have hk'4 : orderOf k' = 4 := by rw [← Subgroup.orderOf_coe]; exact hk4
  have h4 : (k' : SecQuot X) ^ 2 ^ (1 + 1) = 1 := by
    rw [← QuotientGroup.mk_pow, show 2 ^ (1 + 1) = orderOf k' by rw [hk'4]; norm_num,
      pow_orderOf_eq_one, QuotientGroup.mk_one]
  have h2 : ¬ (k' : SecQuot X) ^ 2 ^ 1 = 1 := by
    intro h
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
    have h3 : k' ^ 2 * k' ^ 2 = 1 := by
      rw [← pow_add, show 2 + 2 = orderOf k' by rw [hk'4], pow_orderOf_eq_one]
    have h5 := orderOf_dvd_of_pow_eq_one (eq_one_of_mem_classicalInvolutionOddCore_of_mul_self h h3)
    rw [hk'4] at h5
    norm_num at h5
  have := orderOf_eq_prime_pow h2 h4
  simpa using this

theorem mk_eq_mk_of_inv_mul_mem {x y : T} (hx : x ∈ X) (hy : y ∈ X) (h : x⁻¹ * y ∈ oddCoreOf X) :
    ((⟨x, hx⟩ : ↥X) : SecQuot X) = ((⟨y, hy⟩ : ↥X) : SecQuot X) := by
  obtain ⟨h1, h2⟩ := mem_oddCoreOf_iff.mp h
  rw [QuotientGroup.eq]
  have e : (⟨x, hx⟩ : ↥X)⁻¹ * ⟨y, hy⟩ = ⟨x⁻¹ * y, h1⟩ := Subtype.ext rfl
  rw [e]
  exact h2

theorem commutator_mem_of_mk_comm {x y : T} (hx : x ∈ X) (hy : y ∈ X)
    (h : ((⟨x, hx⟩ : ↥X) : SecQuot X) * ((⟨y, hy⟩ : ↥X) : SecQuot X) =
      ((⟨y, hy⟩ : ↥X) : SecQuot X) * ((⟨x, hx⟩ : ↥X) : SecQuot X)) :
    x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf X := by
  have hm : x * y * x⁻¹ * y⁻¹ ∈ X :=
    X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy)
  refine mem_oddCoreOf_iff.mpr ⟨hm, ?_⟩
  have e : (⟨x * y * x⁻¹ * y⁻¹, hm⟩ : ↥X) = ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ :=
    Subtype.ext rfl
  rw [e, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, h]
  group

theorem commutator_mem_of_act_fix {t : T} (htN : t ∈ Subgroup.normalizer (X : Set T)) {x : T}
    (hx : x ∈ X)
    (h : Asc77.s26Act X ⟨t, htN⟩ ((⟨x, hx⟩ : ↥X) : SecQuot X) = ((⟨x, hx⟩ : ↥X) : SecQuot X)) :
    t * x * t⁻¹ * x⁻¹ ∈ oddCoreOf X := by
  have htx : t * x * t⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp htN x).mp hx
  have h1 := Asc77.s26Act_mk X ⟨t, htN⟩ ⟨x, hx⟩ ⟨t * x * t⁻¹, htx⟩ rfl
  rw [h] at h1
  have hm : t * x * t⁻¹ * x⁻¹ ∈ X := X.mul_mem htx (X.inv_mem hx)
  refine mem_oddCoreOf_iff.mpr ⟨hm, ?_⟩
  have e : (⟨t * x * t⁻¹ * x⁻¹, hm⟩ : ↥X) = ⟨t * x * t⁻¹, htx⟩ * ⟨x, hx⟩⁻¹ := Subtype.ext rfl
  rw [e, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← h1,
    mul_inv_cancel]

theorem exists_conj_of_mk_conj {u v : T} (hu : u ∈ X) (hv : v ∈ X) (hu2 : u * u = 1)
    (hv2 : v * v = 1)
    (h : ∃ w : SecQuot X, ((⟨v, hv⟩ : ↥X) : SecQuot X) = w * ((⟨u, hu⟩ : ↥X) : SecQuot X) * w⁻¹) :
    ∃ l ∈ X, l * u * l⁻¹ = v := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
  set u' : ↥X := ⟨u, hu⟩ with hu'
  set v' : ↥X := ⟨v, hv⟩ with hv'
  have hu'2 : u' * u' = 1 := Subtype.ext hu2
  have hv'2 : v' * v' = 1 := Subtype.ext hv2
  set y : ↥X := x * u' * x⁻¹ with hy
  have hy2 : y * y = 1 := by
    calc y * y = x * (u' * u') * x⁻¹ := by rw [hy]; group
      _ = 1 := by rw [hu'2]; group
  have hyv : (y : SecQuot X) = (v' : SecQuot X) := by
    rw [hy, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hw.symm
  have hc : y * v' ∈ classicalInvolutionOddCore ↥X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hyv, ← QuotientGroup.mk_mul, hv'2]
    rfl
  obtain ⟨k, hk⟩ := exists_pow_conj_eq_of_odd_orderOf hy2 hv'2
    (odd_orderOf_of_mem_classicalInvolutionOddCore hc)
  generalize (y * v') ^ k = p at hk
  have key : (p * x) * u' * (p * x)⁻¹ = v' := by
    rw [← hk, hy]
    group
  refine ⟨((p * x : ↥X) : T), (p * x).2, ?_⟩
  have := congrArg Subtype.val key
  simpa using this

private theorem isPGroup_zpowers_of_mul_self {x : T} (hx : x * x = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

private theorem mem_normalizer_oddCoreOf {g : T} (hg : g ∈ Subgroup.normalizer (X : Set T)) :
    g ∈ Subgroup.normalizer (oddCoreOf X : Set T) :=
  mem_normalizer_iff_conjSub_eq.mpr (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer hg)

private theorem mem_normalizer_inf {H K : Subgroup T} {g : T}
    (hH : g ∈ Subgroup.normalizer (H : Set T)) (hK : g ∈ Subgroup.normalizer (K : Set T)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup T) : Set T) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.mp hH h) (Subgroup.mem_normalizer_iff.mp hK h)

private theorem commutator_conj_mem {N : Subgroup T} {g c m : T}
    (hg : g ∈ Subgroup.normalizer (N : Set T)) (hc : c ∈ Subgroup.normalizer (N : Set T))
    (hm : m ∈ N) (h : g * c * g⁻¹ * c⁻¹ ∈ N) :
    g * (m * c * m⁻¹) * g⁻¹ * (m * c * m⁻¹)⁻¹ ∈ N := by
  have h1 : g * m * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hg m).mp hm
  have h2 : c * (g * m⁻¹ * g⁻¹) * c⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp hc _).mp ((Subgroup.mem_normalizer_iff.mp hg _).mp (N.inv_mem hm))
  have h3 : c * m * c⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hc m).mp hm
  have e : g * (m * c * m⁻¹) * g⁻¹ * (m * c * m⁻¹)⁻¹ =
      (g * m * g⁻¹) * (g * c * g⁻¹ * c⁻¹) * (c * (g * m⁻¹ * g⁻¹) * c⁻¹) * (c * m * c⁻¹) * m⁻¹ := by
    group
  rw [e]
  exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem h1 h) h2) h3) (N.inv_mem hm)

private theorem exists_conj_commute_inv_mul {N : Subgroup T} (hN : Odd (Nat.card N)) {g c : T}
    (hg2 : g * g = 1) (hc2 : c * c = 1) (hgN : g ∈ Subgroup.normalizer (N : Set T))
    (hcN : c ∈ Subgroup.normalizer (N : Set T)) (h : g * c * g⁻¹ * c⁻¹ ∈ N) :
    ∃ m ∈ N, (m * c * m⁻¹) * (m * c * m⁻¹) = 1 ∧ g * (m * c * m⁻¹) = (m * c * m⁻¹) * g ∧
      (m * c * m⁻¹)⁻¹ * c ∈ N := by
  obtain ⟨m, hm, hcomm⟩ := exists_conj_commute_of_commutator_mem_odd hN
    (isPGroup_zpowers_of_mul_self hg2) (isPGroup_zpowers_of_mul_self hc2) hgN hcN h
  refine ⟨m, hm, ?_, hcomm, ?_⟩
  · have e : (m * c * m⁻¹) * (m * c * m⁻¹) = m * (c * c) * m⁻¹ := by group
    rw [e, hc2, mul_one, mul_inv_cancel]
  · have h1 : c⁻¹ * m⁻¹ * c⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (N : Set T)).inv_mem hcN) _).mp
        (N.inv_mem hm)
    have e : (m * c * m⁻¹)⁻¹ * c = m * (c⁻¹ * m⁻¹ * c⁻¹⁻¹) := by group
    rw [e]
    exact N.mul_mem hm h1

theorem exists_lift_commuting_pair {t a₀ b₀ : T} (ht2 : t * t = 1)
    (htN : t ∈ Subgroup.normalizer (X : Set T)) (ha₀ : a₀ ∈ X) (hb₀ : b₀ ∈ X)
    (ha₀2 : a₀ * a₀ = 1) (hb₀2 : b₀ * b₀ = 1) (hab : a₀ * b₀ * a₀⁻¹ * b₀⁻¹ ∈ oddCoreOf X)
    (hta : t * a₀ * t⁻¹ * a₀⁻¹ ∈ oddCoreOf X) (htb : t * b₀ * t⁻¹ * b₀⁻¹ ∈ oddCoreOf X) :
    ∃ a b : T, a ∈ X ∧ b ∈ X ∧ a⁻¹ * a₀ ∈ oddCoreOf X ∧ b⁻¹ * b₀ ∈ oddCoreOf X ∧
      a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ t * a = a * t ∧ t * b = b * t := by
  have hO : Odd (Nat.card (oddCoreOf X)) := oddCoreOf_odd_natCard X
  have hOX : oddCoreOf X ≤ X := oddCoreOf_le_self X
  have hXO : ∀ {x : T}, x ∈ X → x ∈ Subgroup.normalizer (oddCoreOf X : Set T) := fun hx =>
    mem_normalizer_oddCoreOf (Subgroup.le_normalizer hx)
  have htO : t ∈ Subgroup.normalizer (oddCoreOf X : Set T) := mem_normalizer_oddCoreOf htN
  have hconjX : ∀ {m x : T}, m ∈ oddCoreOf X → x ∈ X → m * x * m⁻¹ ∈ X := fun hm hx =>
    X.mul_mem (X.mul_mem (hOX hm) hx) (X.inv_mem (hOX hm))
  obtain ⟨n, hn, ha2, hta', haa₀⟩ := exists_conj_commute_inv_mul hO ht2 ha₀2 htO (hXO ha₀) hta
  have hba : b₀ * (n * a₀ * n⁻¹) * b₀⁻¹ * (n * a₀ * n⁻¹)⁻¹ ∈ oddCoreOf X := by
    refine commutator_conj_mem (hXO hb₀) (hXO ha₀) hn ?_
    have e : b₀ * a₀ * b₀⁻¹ * a₀⁻¹ = (a₀ * b₀ * a₀⁻¹ * b₀⁻¹)⁻¹ := by group
    rw [e]
    exact (oddCoreOf X).inv_mem hab
  have haX := hconjX hn ha₀
  generalize n * a₀ * n⁻¹ = a at ha2 hta' haa₀ hba haX
  have hab' : a * b₀ * a⁻¹ * b₀⁻¹ ∈ oddCoreOf X := by
    have e : a * b₀ * a⁻¹ * b₀⁻¹ = (b₀ * a * b₀⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]
    exact (oddCoreOf X).inv_mem hba
  obtain ⟨n₁, hn₁, hb₁2, hab₁, hb₁b₀⟩ :=
    exists_conj_commute_inv_mul hO ha2 hb₀2 (hXO haX) (hXO hb₀) hab'
  have htb₁ := commutator_conj_mem htO (hXO hb₀) hn₁ htb
  have hb₁X := hconjX hn₁ hb₀
  generalize n₁ * b₀ * n₁⁻¹ = b₁ at hb₁2 hab₁ hb₁b₀ htb₁ hb₁X
  have htC : t ∈ Subgroup.centralizer ({a} : Set T) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hta'
  have hb₁C : b₁ ∈ Subgroup.centralizer ({a} : Set T) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hab₁.symm
  have hNodd : Odd (Nat.card ↥(oddCoreOf X ⊓ Subgroup.centralizer ({a} : Set T))) :=
    hO.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have htb₁' : t * b₁ * t⁻¹ * b₁⁻¹ ∈ oddCoreOf X ⊓ Subgroup.centralizer ({a} : Set T) :=
    Subgroup.mem_inf.mpr ⟨htb₁, mul_mem (mul_mem (mul_mem htC hb₁C) (inv_mem htC)) (inv_mem hb₁C)⟩
  obtain ⟨n₂, hn₂, hb2, htb', hbb₁⟩ := exists_conj_commute_inv_mul hNodd ht2 hb₁2
    (mem_normalizer_inf htO (Subgroup.le_normalizer htC))
    (mem_normalizer_inf (hXO hb₁X) (Subgroup.le_normalizer hb₁C)) htb₁'
  obtain ⟨hn₂O, hn₂C⟩ := Subgroup.mem_inf.mp hn₂
  refine ⟨a, n₂ * b₁ * n₂⁻¹, haX, hconjX hn₂O hb₁X, haa₀, ?_, ha2, hb2, ?_, hta', htb'⟩
  · have e : (n₂ * b₁ * n₂⁻¹)⁻¹ * b₀ = ((n₂ * b₁ * n₂⁻¹)⁻¹ * b₁) * (b₁⁻¹ * b₀) := by group
    rw [e]
    exact (oddCoreOf X).mul_mem (Subgroup.mem_inf.mp hbb₁).1 hb₁b₀
  · have hbC : n₂ * b₁ * n₂⁻¹ ∈ Subgroup.centralizer ({a} : Set T) :=
      mul_mem (mul_mem hn₂C hb₁C) (inv_mem hn₂C)
    exact (Subgroup.mem_centralizer_singleton_iff.mp hbC).symm

end Lift

theorem exists_orderOf_four_of_datum {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T}
    (hd : FrameTightDatum K z) :
    ∃ R₀ : Subgroup T, IsSylow2In R₀ K ∧ ∃ k ∈ R₀, orderOf k = 4 ∧ k * k = z := by
  obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup T))
    (bot_le : (⊥ : Subgroup T) ≤ K)
  obtain ⟨e⟩ := hd.quat R₀ hR₀
  set r : ↥R₀ := e.symm (QuaternionGroup.a 1) with hr
  have hr4 : orderOf r = 4 := by
    rw [hr, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
  have hrr1 : r * r ≠ 1 := by
    intro h
    have h1 := congrArg e h
    rw [hr, map_mul, MulEquiv.apply_symm_apply, map_one] at h1
    revert h1
    decide
  have hrr2 : (r * r) * (r * r) = 1 := by
    apply e.injective
    rw [hr, map_mul, map_mul, MulEquiv.apply_symm_apply, map_one]
    decide
  refine ⟨R₀, hR₀, (r : T), r.2, by rw [Subgroup.orderOf_coe]; exact hr4, ?_⟩
  rcases hd.unique.unique _ (hR₀.1 (r * r).2) (congrArg Subtype.val hrr2) with h | h
  · exact absurd (Subtype.ext h) hrr1
  · simpa using h

namespace FrameCfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {S : Subgroup T}

theorem mem_sigmaNorm_of_cent (cfg : FrameCfg K z J zJ S) {y : T} {M' : Subgroup T}
    (hM' : M' ∈ sigmaOf K) {X' : Subgroup T} (hX' : X' ∈ USet (CoreAssembly.conjClass K))
    (hX'M' : X' ≤ M') (hc : X' ≤ Subgroup.centralizer ({y⁻¹ * z * y} : Set T)) :
    y ∈ sigmaNorm K := by
  have hΩ := cfg.datum.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKu : IsUniqueInvolution (conjSub y⁻¹ K) (y⁻¹ * z * y) := by
    have := cfg.datum.unique.conj y⁻¹
    rwa [inv_inv] at this
  have hKuΩ : conjSub y⁻¹ K ∈ CoreAssembly.conjClass K := hΩ.conjInvariant _ K hKΩ
  have hM'd : M' ∈ dstarComp (CoreAssembly.conjClass K) K := hM'
  have hM'Ω : M' ∈ CoreAssembly.conjClass K := (mem_dstarComp_symm hKΩ hM'd).1
  have h1 : M' ∈ dstarComp (CoreAssembly.conjClass K) (conjSub y⁻¹ K) :=
    dstarComp_of_centralizes hΩ hM'Ω hKuΩ hKu hX' hX'M' hc
  have h2 : conjSub y⁻¹ K ∈ dstarComp (CoreAssembly.conjClass K) M' :=
    (mem_dstarComp_symm hKuΩ h1).2
  have h3 : conjSub y⁻¹ K ∈ dstarComp (CoreAssembly.conjClass K) K := hM'd.trans h2
  have h4 : y⁻¹ ∈ sigmaStarNorm (CoreAssembly.conjClass K) K :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hKΩ h3
  have h5 : y ∈ sigmaStarNorm (CoreAssembly.conjClass K) K := by
    simpa using (sigmaStarNorm (CoreAssembly.conjClass K) K).inv_mem h4
  exact sigmaStarNorm_le_sigmaNorm K h5

end FrameCfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
