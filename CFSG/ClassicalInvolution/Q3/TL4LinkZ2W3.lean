module

public import CFSG.ClassicalInvolution.Q3.TL4LinkLie
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W1
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4Y

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

section Act

variable {G : Type} [Group G]

private theorem eq_one_of_mem_oddCoreOf [Finite G] {Λ : Subgroup G} {y : G}
    (hy : y ∈ oddCoreOf Λ) {k : ℕ} (hk : y ^ 2 ^ k = 1) : y = 1 := by
  obtain ⟨hyΛ, hyO⟩ := mem_oddCoreOf_iff.mp hy
  have hodd : Odd (orderOf y) := by
    have h1 := orderOf_dvd_natCard (⟨⟨y, hyΛ⟩, hyO⟩ : ↥(classicalInvolutionOddCore ↥Λ))
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h1
    exact (CFSG.ComponentClassification.OddCore.odd_card ↥Λ).of_dvd_nat h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have hj0 : j = 0 := by
    by_contra h
    rw [hj] at hodd
    exact Nat.not_even_iff_odd.2 hodd (Nat.even_pow.2 ⟨even_two, h⟩)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact hj

private theorem eq_one_of_mem_oddCoreOf_of_mul_self [Finite G] {Λ : Subgroup G} {y : G}
    (hy : y ∈ oddCoreOf Λ) (hy2 : y * y = 1) : y = 1 :=
  eq_one_of_mem_oddCoreOf hy (k := 1) (by rw [pow_one, pow_two]; exact hy2)

private theorem exists_pow_two_pow_eq_one {P : Sylow 2 G} {y : G} (hy : y ∈ (P : Subgroup G)) :
    ∃ k : ℕ, y ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨y, hy⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem exists_pow_involution {x : G} {k : ℕ} (hk : x ^ 2 ^ k = 1) (hx : x ≠ 1) :
    ∃ m : ℕ, x ^ m * x ^ m = 1 ∧ x ^ m ≠ 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hx hj
  refine ⟨2 ^ (j - 1), ?_, pow_ne_one_of_lt_orderOf (by positivity)
    (by rw [hj]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))⟩
  rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0),
    ← hj, pow_orderOf_eq_one]

private theorem comm_of_actsTriv [Finite G] {P : Sylow 2 G} {Λ : Subgroup G} {x r : G}
    (hx : x ∈ (P : Subgroup G)) (hr : r ∈ (P : Subgroup G)) (hrΛ : r ∈ Λ) (h : ActsTriv Λ x) :
    x * r = r * x := by
  have hc : x * r * x⁻¹ * r⁻¹ ∈ (P : Subgroup G) :=
    (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hx hr)
      ((P : Subgroup G).inv_mem hx)) ((P : Subgroup G).inv_mem hr)
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one hc
  have h1 : x * r * x⁻¹ * r⁻¹ = 1 := eq_one_of_mem_oddCoreOf (h r hrΛ) hk
  calc x * r = x * r * x⁻¹ * r⁻¹ * (r * x) := by group
    _ = r * x := by rw [h1, one_mul]

private theorem actsTriv_mul {Λ : Subgroup G} {x y : G}
    (hxN : x ∈ Subgroup.normalizer (Λ : Set G)) (hx : ActsTriv Λ x) (hy : ActsTriv Λ y) :
    ActsTriv Λ (x * y) := by
  intro z hz
  have hxO := mem_normalizer_oddCore_of_mem_normalizer hxN
  have h1 : x * (y * z * y⁻¹ * z⁻¹) * x⁻¹ ∈ oddCoreOf Λ :=
    (Subgroup.mem_normalizer_iff.mp hxO _).mp (hy z hz)
  have h2 := (oddCoreOf Λ).mul_mem h1 (hx z hz)
  have e : x * (y * z * y⁻¹ * z⁻¹) * x⁻¹ * (x * z * x⁻¹ * z⁻¹) =
      x * y * z * (x * y)⁻¹ * z⁻¹ := by
    group
  rwa [e] at h2

private theorem actsTriv_pow {Λ : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (Λ : Set G))
    (hx : ActsTriv Λ x) (m : ℕ) : ActsTriv Λ (x ^ m) := by
  induction m with
  | zero =>
    intro z _
    simp
  | succ m ih =>
    rw [pow_succ]
    exact actsTriv_mul (Subgroup.pow_mem _ hxN m) ih hx

private theorem actsTriv_mul_of_comm {Λ : Subgroup G} {x c : G} (hc : ∀ y ∈ Λ, c * y = y * c)
    (h : ActsTriv Λ x) : ActsTriv Λ (x * c) := by
  intro y hy
  have e : x * c * y * (x * c)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
    calc x * c * y * (x * c)⁻¹ * y⁻¹ = x * (c * y) * c⁻¹ * x⁻¹ * y⁻¹ := by group
      _ = x * (y * c) * c⁻¹ * x⁻¹ * y⁻¹ := by rw [hc y hy]
      _ = x * y * x⁻¹ * y⁻¹ := by group
  rw [e]
  exact h y hy

private theorem actsTriv_mul_of_actsLike {Λ : Subgroup G} {x w : G} (hwΛ : w ∈ Λ)
    (hw2 : w * w = 1) (h : ActsLike Λ x w) : ActsTriv Λ (x * w) := by
  intro y hy
  have h1 := h _ (Λ.mul_mem (Λ.mul_mem hwΛ hy) (Λ.inv_mem hwΛ))
  have e1 : w * (w * y * w⁻¹) * w⁻¹ = y := by
    calc w * (w * y * w⁻¹) * w⁻¹ = (w * w) * y * (w * w)⁻¹ := by group
      _ = y := by rw [hw2]; group
  rw [e1] at h1
  have e2 : x * (w * y * w⁻¹) * x⁻¹ * y⁻¹ = x * w * y * (x * w)⁻¹ * y⁻¹ := by group
  rwa [e2] at h1

private theorem actsTriv_conjSub_iff {Λ : Subgroup G} {g y : G} :
    ActsTriv (conjSub g Λ) y ↔ ActsTriv Λ (g⁻¹ * y * g) := by
  constructor
  · intro h z hz
    have h1 := h _ (Generic.conj_mem_conjSub (n := g) hz)
    rw [Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff] at h1
    have e : g⁻¹ * (y * (g * z * g⁻¹) * y⁻¹ * (g * z * g⁻¹)⁻¹) * g =
        g⁻¹ * y * g * z * (g⁻¹ * y * g)⁻¹ * z⁻¹ := by
      group
    rwa [e] at h1
  · intro h z hz
    rw [mem_conjSub_iff] at hz
    rw [Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff]
    have e : g⁻¹ * (y * z * y⁻¹ * z⁻¹) * g =
        g⁻¹ * y * g * (g⁻¹ * z * g) * (g⁻¹ * y * g)⁻¹ * (g⁻¹ * z * g)⁻¹ := by
      group
    rw [e]
    exact h _ hz

private theorem actsLike_conjSub_of {Λ : Subgroup G} {g y w : G}
    (h : ActsLike Λ (g⁻¹ * y * g) (g⁻¹ * w * g)) : ActsLike (conjSub g Λ) y w := by
  intro z hz
  rw [mem_conjSub_iff] at hz
  rw [Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff]
  have e : g⁻¹ * (y * z * y⁻¹ * (w * z * w⁻¹)⁻¹) * g =
      g⁻¹ * y * g * (g⁻¹ * z * g) * (g⁻¹ * y * g)⁻¹ *
        (g⁻¹ * w * g * (g⁻¹ * z * g) * (g⁻¹ * w * g)⁻¹)⁻¹ := by
    group
  rw [e]
  exact h _ hz

private theorem mem_normalizer_of_conj {H Λ : Subgroup G}
    (h : ∀ c ∈ H, ∀ y ∈ Λ, c * y * c⁻¹ ∈ Λ) {x : G} (hx : x ∈ H) :
    x ∈ Subgroup.normalizer (Λ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h x hx y hy, fun hy => ?_⟩
  have h1 := h x⁻¹ (H.inv_mem hx) _ hy
  rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1

private theorem coe_symm_a_two_eq {L Q : Subgroup G} {z : G} (hz : IsUniqueInvolution L z)
    (hQL : Q ≤ L) (e : ↥Q ≃* QuaternionGroup 2) :
    ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) = z := by
  have hsq : ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) *
      (e.symm (QuaternionGroup.a 2) : G) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, show QuaternionGroup.a 2 * QuaternionGroup.a 2 =
      (1 : QuaternionGroup 2) by decide, map_one, Subgroup.coe_one]
  rcases hz.unique _ (hQL (e.symm _).2) hsq with h | h
  · exfalso
    have h1 : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h
    rw [map_eq_one_iff _ e.symm.injective] at h1
    exact absurd h1 (by decide)
  · exact h

private theorem mul_inv_mem_oddCoreOf_of_mk_eq {Λ : Subgroup G} {a b : G} (ha : a ∈ Λ)
    (hb : b ∈ Λ) (h : (QuotientGroup.mk ⟨a, ha⟩ : ↥Λ ⧸ classicalInvolutionOddCore ↥Λ) =
      QuotientGroup.mk ⟨b, hb⟩) : a * b⁻¹ ∈ oddCoreOf Λ := by
  rw [QuotientGroup.eq] at h
  have h1 := Subgroup.inv_mem _ h
  rw [mul_inv_rev, inv_inv] at h1
  have h2 := Subgroup.Normal.conj_mem inferInstance _ h1 ⟨b, hb⟩
  rw [show (⟨b, hb⟩ : ↥Λ) * ((⟨b, hb⟩ : ↥Λ)⁻¹ * ⟨a, ha⟩) * (⟨b, hb⟩ : ↥Λ)⁻¹ =
    ⟨a, ha⟩ * (⟨b, hb⟩ : ↥Λ)⁻¹ by group] at h2
  exact ⟨_, h2, rfl⟩

private def PiConcl (A : Type) [Group A] : Prop :=
  ∀ (P : Subgroup A) (e : ↥P ≃* QuaternionGroup 2) (β : MulAut A), (∀ x ∈ P, β x ∈ P) →
    (∃ k : ℕ, β ^ 2 ^ k = 1) →
      β ^ 8 = 1 ∧ (β ^ 4 = 1 →
        β ^ 2 = 1 ∨ β ^ 2 = MulAut.conj ((e.symm (QuaternionGroup.a 2) : ↥P) : A))

private theorem piConcl_congr {A B : Type} [Group A] [Group B] (f : A ≃* B) (hB : PiConcl B) :
    PiConcl A := by
  intro P e β hβP hβ2
  have hc : ∀ m : A, MulAut.congr f (MulAut.conj m) = MulAut.conj (f m) := fun m => by
    ext x
    change f (m * f.symm x * m⁻¹) = f m * x * (f m)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  let fP : ↥P ≃* ↥(P.map f.toMonoidHom) := P.equivMapOfInjective f.toMonoidHom f.injective
  have hnorm : ∀ x ∈ P.map f.toMonoidHom, MulAut.congr f β x ∈ P.map f.toMonoidHom := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨β y, hβP y hy, ?_⟩
    change f (β y) = f (β (f.symm (f y)))
    rw [MulEquiv.symm_apply_apply]
  have h2 : ∃ k : ℕ, MulAut.congr f β ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hβ2
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨h8, h4⟩ := hB _ (fP.symm.trans e) _ hnorm h2
  refine ⟨(MulAut.congr f).injective (by rw [map_pow, h8, map_one]), fun hβ4 => ?_⟩
  rcases h4 (by rw [← map_pow, hβ4, map_one]) with h | h
  · left
    exact (MulAut.congr f).injective (by rw [map_pow, h, map_one])
  · right
    apply (MulAut.congr f).injective
    rw [map_pow, h, hc]
    rfl

private theorem pi_of_quat [Finite G] {Λ Q : Subgroup G} {x d : G}
    (hxN : x ∈ Subgroup.normalizer (Λ : Set G)) {k : ℕ} (hxk : x ^ 2 ^ k = 1) (hQΛ : Q ≤ Λ)
    (hQ2 : IsPGroup 2 Q) (e : ↥Q ≃* QuaternionGroup 2)
    (hd : ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) = d) (hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q)
    (hPi : PiConcl (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) :
    ActsTriv Λ (x ^ 8) ∧ (x ^ 4 = 1 → ActsTriv Λ (x ^ 2) ∨ ActsLike Λ (x ^ 2) d) := by
  have hxΛ : ∀ m : ℕ, ∀ y ∈ Λ, x ^ m * y * (x ^ m)⁻¹ ∈ Λ := fun m y hy =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hxN m) y).mp hy
  have hx1 : ∀ y ∈ Λ, x * y * x⁻¹ ∈ Λ := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hxN y).mp hy
  have hx1' : ∀ y ∈ Λ, x⁻¹ * y * x⁻¹⁻¹ ∈ Λ := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) y).mp hy
  let γ : MulAut ↥Λ :=
    { toFun := fun y => ⟨x * y * x⁻¹, hx1 y y.2⟩
      invFun := fun y => ⟨x⁻¹ * y * x⁻¹⁻¹, hx1' y y.2⟩
      left_inv := fun y => Subtype.ext (by
        show x⁻¹ * (x * (y : G) * x⁻¹) * x⁻¹⁻¹ = y
        group)
      right_inv := fun y => Subtype.ext (by
        show x * (x⁻¹ * (y : G) * x⁻¹⁻¹) * x⁻¹ = y
        group)
      map_mul' := fun a b => Subtype.ext (by
        show x * ((a : G) * b) * x⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹)
        group) }
  have hγ : ∀ y : ↥Λ, ((γ y : ↥Λ) : G) = x * y * x⁻¹ := fun _ => rfl
  have hO : (classicalInvolutionOddCore ↥Λ).map γ.toMonoidHom = classicalInvolutionOddCore ↥Λ :=
    CFSG.ComponentClassification.OddCore.char_invariant γ
  set O := classicalInvolutionOddCore ↥Λ with hOdef
  let β : MulAut (↥Λ ⧸ O) := QuotientGroup.congr O O γ hO
  have hβ : ∀ y : ↥Λ, β (QuotientGroup.mk y) = QuotientGroup.mk (γ y) := fun _ => rfl
  have hβm : ∀ (m : ℕ) (y : ↥Λ), (β ^ m) (QuotientGroup.mk y) =
      QuotientGroup.mk (⟨x ^ m * y * (x ^ m)⁻¹, hxΛ m y y.2⟩ : ↥Λ) := by
    intro m
    induction m with
    | zero =>
      intro y
      rw [pow_zero, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      simp
    | succ m ih =>
      intro y
      rw [pow_succ' β m, MulAut.mul_apply, ih, hβ]
      congr 1
      apply Subtype.ext
      rw [hγ]
      show x * (x ^ m * (y : G) * (x ^ m)⁻¹) * x⁻¹ = x ^ (m + 1) * y * (x ^ (m + 1))⁻¹
      rw [pow_succ' x m]
      group
  have hβone : ∀ m : ℕ, x ^ m = 1 → β ^ m = 1 := by
    intro m hm
    refine MulEquiv.ext fun q => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hβm, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show x ^ m * (y : G) * (x ^ m)⁻¹ = y
    rw [hm]
    group
  let ι : ↥(Q.subgroupOf Λ) →* ↥Λ ⧸ O := (QuotientGroup.mk' O).comp (Q.subgroupOf Λ).subtype
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyO : (y : ↥Λ) ∈ O := (QuotientGroup.eq_one_iff _).mp hy
    have hyQ : (((y : ↥Λ) : G)) ∈ Q := Subgroup.mem_subgroupOf.mp y.2
    obtain ⟨j, hj⟩ := hQ2 ⟨_, hyQ⟩
    have hj' : ((y : ↥Λ) : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have h1 : ((y : ↥Λ) : G) = 1 := eq_one_of_mem_oddCoreOf ⟨_, hyO, rfl⟩ hj'
    exact Subtype.ext (Subtype.ext h1)
  let eP : ↥ι.range ≃* QuaternionGroup 2 :=
    (MonoidHom.ofInjective hι).symm.trans ((Subgroup.subgroupOfEquivOfLe hQΛ).trans e)
  have hnorm : ∀ q ∈ ι.range, β q ∈ ι.range := by
    rintro _ ⟨q, rfl⟩
    have hqQ : ((q : ↥Λ) : G) ∈ Q := Subgroup.mem_subgroupOf.mp q.2
    refine ⟨⟨⟨x * (q : ↥Λ) * x⁻¹, hx1 _ (q : ↥Λ).2⟩, Subgroup.mem_subgroupOf.mpr
      (hxQ _ hqQ)⟩, ?_⟩
    change QuotientGroup.mk _ = β (QuotientGroup.mk (q : ↥Λ))
    rw [hβ]
    rfl
  obtain ⟨h8, h4⟩ := hPi _ eP β hnorm ⟨k, hβone _ hxk⟩
  have hdΛ : d ∈ Λ := hd ▸ hQΛ (e.symm (QuaternionGroup.a 2)).2
  have hzP : ((eP.symm (QuaternionGroup.a 2) : ↥ι.range) : ↥Λ ⧸ O) =
      QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ) := by
    change ι ((Subgroup.subgroupOfEquivOfLe hQΛ).symm (e.symm (QuaternionGroup.a 2))) = _
    change QuotientGroup.mk _ = _
    congr 1
    exact Subtype.ext hd
  have htriv : ∀ m : ℕ, β ^ m = 1 → ActsTriv Λ (x ^ m) := by
    intro m hm y hy
    have h1 : (β ^ m) (QuotientGroup.mk ⟨y, hy⟩) = QuotientGroup.mk ⟨y, hy⟩ := by
      rw [hm]
      rfl
    rw [hβm] at h1
    exact mul_inv_mem_oddCoreOf_of_mk_eq (hxΛ m y hy) hy h1
  refine ⟨htriv 8 h8, fun hx4 => ?_⟩
  rcases h4 (hβone 4 hx4) with h | h
  · exact Or.inl (htriv 2 h)
  · right
    intro y hy
    have hdy : d * y * d⁻¹ ∈ Λ := Λ.mul_mem (Λ.mul_mem hdΛ hy) (Λ.inv_mem hdΛ)
    have h1 : (β ^ 2) (QuotientGroup.mk ⟨y, hy⟩) =
        QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ) * QuotientGroup.mk ⟨y, hy⟩ *
          (QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ))⁻¹ := by
      rw [h, MulAut.conj_apply, hzP]
    rw [hβm, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at h1
    have e1 : (⟨d, hdΛ⟩ : ↥Λ) * ⟨y, hy⟩ * (⟨d, hdΛ⟩ : ↥Λ)⁻¹ = ⟨d * y * d⁻¹, hdy⟩ :=
      Subtype.ext rfl
    rw [e1] at h1
    exact mul_inv_mem_oddCoreOf_of_mk_eq (hxΛ 2 y hy) hdy h1

end Act

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

private theorem Z2Set.comm_t_u (hs : Z2Set n R S t J u R₀ T₀ P) : t * u = u * t :=
  Q3CL.T8.mul_comm_of_mem_omegaNbr hs.large.datum.hypOmegaGen
    hs.large.datum.isUniqueInvolution_core hs.hJ hs.hu

private theorem Z2Set.T₀_le_cent_t (hs : Z2Set n R S t J u R₀ T₀ P) :
    T₀ ≤ Subgroup.centralizer ({t} : Set Y) := fun _ hx =>
  S1916.normalizer_le_centralizer_of_isUniqueInvolution hs.large.datum.isUniqueInvolution_core
    (hs.hT₀N hx)

private theorem Z2Set.T₀_le_linkLayer (hs : Z2Set n R S t J u R₀ T₀ P) : T₀ ≤ linkLayer R t :=
  (le_coreAt t hs.hT₀.2.1 hs.hT₀.1 hs.T₀_le_cent_t).trans (coreAt_le_linkLayerAt hs.hJ)

private theorem Z2Set.R₀_le_linkLayerAt (hs : Z2Set n R S t J u R₀ T₀ P) :
    R₀ ≤ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u := by
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hs.large.datum.hypOmegaGen hK hs.hJ.1 hs.hJ
  exact (le_coreAt u hs.hR₀.2.1 hs.hR₀.1 hs.hR₀u).trans (coreAt_le_linkLayerAt hKJ)

private theorem Z2Set.t_mem_R₀ (hs : Z2Set n R S t J u R₀ T₀ P) : t ∈ R₀ := by
  obtain ⟨e⟩ := (TightLargeHypR.typeRFam hs.large).quat (tightCore R) ⟨1, conjSub_one _⟩ R₀
    hs.hR₀
  rw [← coe_symm_a_two_eq hs.large.datum.isUniqueInvolution_core hs.hR₀.1 e]
  exact (e.symm (QuaternionGroup.a 2)).2

private theorem Z2Set.u_mem_T₀ (hs : Z2Set n R S t J u R₀ T₀ P) : u ∈ T₀ := by
  obtain ⟨e⟩ := (TightLargeHypR.typeRFam hs.large).quat J hs.hJ.1 T₀ hs.hT₀
  rw [← coe_symm_a_two_eq hs.hu hs.hT₀.1 e]
  exact (e.symm (QuaternionGroup.a 2)).2

private theorem Z2Set.conj_mem_T₀ (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hxP : x ∈ (P : Subgroup Y)) (hxu : x ∈ Subgroup.centralizer ({u} : Set Y)) {y : Y}
    (hy : y ∈ T₀) : x * y * x⁻¹ ∈ T₀ := by
  have hT : J ⊓ (P : Subgroup Y) = T₀ := hs.hT₀.2.2 _ inf_le_left
    (P.isPGroup'.to_le inf_le_right) (le_inf hs.hT₀.1 hs.hT₀P)
  have hxN : x ∈ Subgroup.normalizer (J : Set Y) :=
    (TightLargeHypR.typeRFam hs.large).tight J hs.hJ.1 u hs.hu hxu
  rw [← hT] at hy ⊢
  exact ⟨(Subgroup.mem_normalizer_iff.mp hxN y).mp hy.1,
    (P : Subgroup Y).mul_mem ((P : Subgroup Y).mul_mem hxP hy.2) ((P : Subgroup Y).inv_mem hxP)⟩

private theorem Z2Set.conj_mem_R₀ (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hxP : x ∈ (P : Subgroup Y)) (hxt : x ∈ Subgroup.centralizer ({t} : Set Y)) {y : Y}
    (hy : y ∈ R₀) : x * y * x⁻¹ ∈ R₀ := by
  have hR : tightCore R ⊓ (P : Subgroup Y) = R₀ := hs.hR₀.2.2 _ inf_le_left
    (P.isPGroup'.to_le inf_le_right) (le_inf hs.hR₀.1 hs.hR₀P)
  have hxN : x ∈ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) :=
    (TightLargeHypR.typeRFam hs.large).tight (tightCore R) ⟨1, conjSub_one _⟩ t
      hs.large.datum.isUniqueInvolution_core hxt
  rw [← hR] at hy ⊢
  exact ⟨(Subgroup.mem_normalizer_iff.mp hxN y).mp hy.1,
    (P : Subgroup Y).mul_mem ((P : Subgroup Y).mul_mem hxP hy.2) ((P : Subgroup Y).inv_mem hxP)⟩

private theorem Z2Set.mem_normalizer_linkLayer (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ Subgroup.centralizer ({t} : Set Y)) :
    x ∈ Subgroup.normalizer (linkLayer R t : Set Y) :=
  mem_normalizer_of_conj (H := Subgroup.centralizer ({t} : Set Y))
    (fun _ hc _ hy => conj_mem_linkLayer hs.large hc hy) hx

private theorem Z2Set.mem_normalizer_linkLayerAt (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ Subgroup.centralizer ({u} : Set Y)) :
    x ∈ Subgroup.normalizer
      (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u : Set Y) := by
  refine mem_normalizer_of_conj (H := Subgroup.centralizer ({u} : Set Y)) (fun c hc y hy => ?_) hx
  have hcJ : conjSub c J = J := mem_normalizer_iff_conjSub_eq.mp
    ((TightLargeHypR.typeRFam hs.large).tight J hs.hJ.1 u hs.hu hc)
  exact conj_mem_linkLayerAt hs.large.datum.hypOmegaGen.conjInvariant hc hcJ hy

private theorem Z2Set.exists_linkLayerAt_eq (hs : Z2Set n R S t J u R₀ T₀ P) :
    ∃ g : Y, conjSub g (tightCore R) = J ∧ u = g * t * g⁻¹ ∧
      linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u = conjSub g (linkLayer R t) := by
  obtain ⟨g, hg⟩ := hs.hJ.1
  have hg' : conjSub g (tightCore R) = J := hg
  have hug : u = g * t * g⁻¹ := by
    have h1 := hs.large.datum.isUniqueInvolution_core.conj g
    rw [hg'] at h1
    exact hs.hu.eq h1
  refine ⟨g, hg', hug, ?_⟩
  show _ = conjSub g (linkLayerAt (CoreAssembly.conjClass (tightCore R)) (tightCore R) t)
  rw [conjSub_linkLayerAt hs.large.datum.hypOmegaGen.conjInvariant g, hg', ← hug]

private theorem Z2Set.mem_oddCoreOf_of_actsTriv (hs : Z2Set n R S t J u R₀ T₀ P) {w : Y}
    (hw : w ∈ linkLayer R t) (h : ActsTriv (linkLayer R t) w) :
    w ∈ oddCoreOf (linkLayer R t) := by
  obtain ⟨p, f, -, -, -, -, hk⟩ := hs.model
  have hZ : Subgroup.center ↥(linkGrp R t) = ⊥ := by
    haveI := hs.simple
    obtain ⟨-, h4, F, _, _, hFcard, ⟨e⟩⟩ := MF163.psl2_of_lieModel hk
    have hnab : ∃ a b : ↥(genFittingFStar ↥(linkGrp R t)), a * b ≠ b * a := by
      obtain ⟨x, y, hxy⟩ :=
        ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian F
          (by omega) (by omega)
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm x)
      obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (e.symm y)
      refine ⟨a, b, fun hab => hxy ?_⟩
      have := congrArg (fun g => e (QuotientGroup.mk g : FStarQuot ↥(linkGrp R t))) hab
      simp only [QuotientGroup.mk_mul, map_mul] at this
      rwa [ha, hb, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
    exact le_bot_iff.mp ((centralizer_genFittingFStar_eq_bot hnab) ▸
      Subgroup.center_le_centralizer (genFittingFStar ↥(linkGrp R t) : Set ↥(linkGrp R t)))
  have hc : linkLayerEquiv hs.large (QuotientGroup.mk ⟨w, hw⟩) ∈
      Subgroup.center ↥(linkGrp R t) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨q, rfl⟩ := (linkLayerEquiv hs.large).surjective g
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← map_mul, ← map_mul]
    congr 1
    obtain ⟨_, hO⟩ := mem_oddCoreOf_iff.mp (h z hz)
    have h2 : (QuotientGroup.mk ((⟨w, hw⟩ : ↥(linkLayer R t)) * ⟨z, hz⟩ *
        (⟨w, hw⟩ : ↥(linkLayer R t))⁻¹ * (⟨z, hz⟩ : ↥(linkLayer R t))⁻¹) :
        ↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hO
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
    calc (QuotientGroup.mk ⟨z, hz⟩ : ↥(linkLayer R t) ⧸
          classicalInvolutionOddCore ↥(linkLayer R t)) * QuotientGroup.mk ⟨w, hw⟩ =
        (QuotientGroup.mk ⟨w, hw⟩ * QuotientGroup.mk ⟨z, hz⟩ *
          (QuotientGroup.mk ⟨w, hw⟩)⁻¹ * (QuotientGroup.mk ⟨z, hz⟩)⁻¹)⁻¹ *
            (QuotientGroup.mk ⟨w, hw⟩ * QuotientGroup.mk ⟨z, hz⟩) := by group
      _ = QuotientGroup.mk ⟨w, hw⟩ * QuotientGroup.mk ⟨z, hz⟩ := by rw [h2, inv_one, one_mul]
  rw [hZ, Subgroup.mem_bot, map_eq_one_iff _ (linkLayerEquiv hs.large).injective,
    QuotientGroup.eq_one_iff] at hc
  exact ⟨_, hc, rfl⟩

private theorem Z2Set.not_actsTriv_u (hs : Z2Set n R S t J u R₀ T₀ P) :
    ¬ ActsTriv (linkLayer R t) u := by
  intro h
  exact hs.hu.ne_one (eq_one_of_mem_oddCoreOf_of_mul_self
    (hs.mem_oddCoreOf_of_actsTriv (hs.T₀_le_linkLayer hs.u_mem_T₀) h) hs.hu.sq)

private theorem Z2Set.not_actsTriv_t (hs : Z2Set n R S t J u R₀ T₀ P) :
    ¬ ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) t := by
  intro h
  have ht := hs.large.datum.isUniqueInvolution_core
  obtain ⟨g, -, -, hΛ⟩ := hs.exists_linkLayerAt_eq
  have htΛ := hs.R₀_le_linkLayerAt hs.t_mem_R₀
  rw [hΛ, mem_conjSub_iff] at htΛ
  rw [hΛ, actsTriv_conjSub_iff] at h
  have h2 : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht.sq]; group
  have h3 := eq_one_of_mem_oddCoreOf_of_mul_self (hs.mem_oddCoreOf_of_actsTriv htΛ h) h2
  apply ht.ne_one
  calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    _ = 1 := by rw [h3]; group

theorem Z2Set.eq_one_of_actsTriv (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) (htx : ActsTriv (linkLayer R t) x)
    (hux : ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x) : x = 1 := by
  obtain ⟨⟨hxP, hxt⟩, hxu⟩ := hx
  have ht := hs.large.datum.isUniqueInvolution_core
  have hxT₀ : ∀ r ∈ T₀, x * r = r * x := fun r hr =>
    comm_of_actsTriv hxP (hs.hT₀P hr) (hs.T₀_le_linkLayer hr) htx
  have hxR₀ : ∀ r ∈ R₀, x * r = r * x := fun r hr =>
    comm_of_actsTriv hxP (hs.hR₀P hr) (hs.R₀_le_linkLayerAt hr) hux
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one hxP
  by_contra hx1
  obtain ⟨m, hm2, hm1⟩ := exists_pow_involution hk hx1
  have hwt : x ^ m * t = t * x ^ m :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.pow_mem _ hxt m)
  have hwu : x ^ m * u = u * x ^ m :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.pow_mem _ hxu m)
  have hwE : x ^ m ∈ Subgroup.closure ({t, u} : Set Y) := by
    by_contra hwE
    exact hs.noA1 ⟨x ^ m, hm2, hwt, hwu, hwE,
      fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr
        ((Commute.pow_right (hxR₀ r hr).symm m).eq),
      fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr
        ((Commute.pow_right (hxT₀ r hr).symm m).eq)⟩
  have hwΛt : ActsTriv (linkLayer R t) (x ^ m) :=
    actsTriv_pow (hs.mem_normalizer_linkLayer hxt) htx m
  have hwΛu : ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (x ^ m) :=
    actsTriv_pow (hs.mem_normalizer_linkLayerAt hxu) hux m
  rcases Asc77.T8.mem_closure_pair_involutions ht.sq hs.hu.sq hs.comm_t_u hwE with h | h | h | h
  · exact hm1 h
  · rw [h] at hwΛu
    exact hs.not_actsTriv_t hwΛu
  · rw [h] at hwΛt
    exact hs.not_actsTriv_u hwΛt
  ·
    rw [h, hs.comm_t_u] at hwΛt
    have htΛ : ∀ y ∈ linkLayer R t, t⁻¹ * y = y * t⁻¹ := fun y hy => by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)
      calc t⁻¹ * y = t⁻¹ * (y * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * y) * t⁻¹ := by rw [h1]
        _ = y * t⁻¹ := by group
    have h1 := actsTriv_mul_of_comm htΛ hwΛt
    rw [mul_inv_cancel_right] at h1
    exact hs.not_actsTriv_u h1

theorem Z2Set.mod16 (hs : Z2Set n R S t J u R₀ T₀ P) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ p ^ f % 16 = 9 ∧
      LieModel (FStarQuot ↥(linkGrp R t)) .PSL 2 p f := by
  obtain ⟨p, f, hp, hp2, hf, -, hk⟩ := hs.model
  exact ⟨p, f, hp, hp2, hf, modelL2Q8Mod16_proved _ (linkFam R t)
    (lieLinkSection_of hs.large hs.z2.1) hs.simple hs.index p f hp hp2 hf hk, hk⟩

private theorem Z2Set.piConcl_linkLayer (hs : Z2Set n R S t J u R₀ T₀ P) :
    PiConcl (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) := by
  obtain ⟨p, f, hp, hp2, hf, h16, hk⟩ := hs.mod16
  exact piConcl_congr (linkLayerEquiv hs.large) fun Q e β hQ h2 =>
    modelPiL2_proved _ hs.simple hs.index p f hp hp2 hf h16 hk Q e β hQ h2

theorem Z2Set.pi_t (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) :
    ActsTriv (linkLayer R t) (x ^ 8) ∧
      (x ^ 4 = 1 → ActsTriv (linkLayer R t) (x ^ 2) ∨ ActsLike (linkLayer R t) (x ^ 2) u) := by
  obtain ⟨⟨hxP, hxt⟩, hxu⟩ := hx
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one hxP
  obtain ⟨e⟩ := (TightLargeHypR.typeRFam hs.large).quat J hs.hJ.1 T₀ hs.hT₀
  exact pi_of_quat (hs.mem_normalizer_linkLayer hxt) hk hs.T₀_le_linkLayer hs.hT₀.2.1 e
    (coe_symm_a_two_eq hs.hu hs.hT₀.1 e) (fun _ hy => hs.conj_mem_T₀ hxP hxu hy)
    hs.piConcl_linkLayer

theorem Z2Set.pi_u (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) :
    ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (x ^ 8) ∧
      (x ^ 4 = 1 → ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (x ^ 2) ∨
        ActsLike (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (x ^ 2) t) := by
  obtain ⟨⟨hxP, hxt⟩, hxu⟩ := hx
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one hxP
  have hΩ := hs.large.datum.hypOmegaGen
  have ht := hs.large.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  obtain ⟨g, hg', hug, hΛ⟩ := hs.exists_linkLayerAt_eq
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hs.hJ.1 hs.hJ
  have hM : conjSub g⁻¹ (tightCore R) ∈
      omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    have h1 := omegaNbr_conj hΩ.conjInvariant hKJ g⁻¹
    rwa [← hg', conjSub_inv_conjSub] at h1
  have hconj : ∀ m : ℕ, (g⁻¹ * x * g) ^ m = g⁻¹ * x ^ m * g := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, pow_succ]; group
  have hx't : g⁻¹ * x * g ∈ Subgroup.centralizer ({t} : Set Y) := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hxu
    rw [hug] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [h1]
      _ = t * (g⁻¹ * x * g) := by group
  have hx'k : (g⁻¹ * x * g) ^ 2 ^ k = 1 := by
    rw [hconj, hk]
    group
  have hQt : conjSub g⁻¹ R₀ ≤ Subgroup.centralizer ({t} : Set Y) := by
    intro y hy
    rw [mem_conjSub_iff, inv_inv] at hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hs.hR₀u hy)
    rw [hug] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : g * (y * t) * g⁻¹ = g * (t * y) * g⁻¹ := by
      calc g * (y * t) * g⁻¹ = g * y * g⁻¹ * (g * t * g⁻¹) := by group
        _ = g * t * g⁻¹ * (g * y * g⁻¹) := h1
        _ = g * (t * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hQ2 : IsPGroup 2 ↥(conjSub g⁻¹ R₀) := hs.hR₀.2.1.map _
  have hQΛ : conjSub g⁻¹ R₀ ≤ linkLayer R t :=
    (le_coreAt t hQ2 (conjSub_mono hs.hR₀.1) hQt).trans (coreAt_le_linkLayerAt hM)
  obtain ⟨eR⟩ := (TightLargeHypR.typeRFam hs.large).quat (tightCore R) hK R₀ hs.hR₀
  let cQ : ↥R₀ ≃* ↥(conjSub g⁻¹ R₀) :=
    R₀.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have hdQ : (((cQ.symm.trans eR).symm (QuaternionGroup.a 2) : ↥(conjSub g⁻¹ R₀)) : Y) =
      g⁻¹ * t * g := by
    change g⁻¹ * ((eR.symm (QuaternionGroup.a 2) : ↥R₀) : Y) * g⁻¹⁻¹ = _
    rw [coe_symm_a_two_eq ht hs.hR₀.1 eR, inv_inv]
  have hx'Q : ∀ y ∈ conjSub g⁻¹ R₀, g⁻¹ * x * g * y * (g⁻¹ * x * g)⁻¹ ∈ conjSub g⁻¹ R₀ := by
    intro y hy
    rw [mem_conjSub_iff, inv_inv] at hy ⊢
    have h1 := hs.conj_mem_R₀ hxP hxt hy
    rwa [show g * (g⁻¹ * x * g * y * (g⁻¹ * x * g)⁻¹) * g⁻¹ = x * (g * y * g⁻¹) * x⁻¹ by group]
  obtain ⟨h8, h4⟩ := pi_of_quat (hs.mem_normalizer_linkLayer hx't) hx'k hQΛ hQ2
    (cQ.symm.trans eR) hdQ hx'Q hs.piConcl_linkLayer
  rw [hΛ]
  refine ⟨actsTriv_conjSub_iff.mpr (by rw [← hconj]; exact h8), fun hx4 => ?_⟩
  have hx'4 : (g⁻¹ * x * g) ^ 4 = 1 := by
    rw [hconj, hx4]
    group
  rcases h4 hx'4 with h | h
  · left
    exact actsTriv_conjSub_iff.mpr (by rw [← hconj]; exact h)
  · right
    apply actsLike_conjSub_of
    rw [← hconj]
    exact h

theorem Z2Set.sq_mem_E (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) (h4 : x ^ 4 = 1) :
    x ^ 2 ∈ Subgroup.closure ({t, u} : Set Y) := by
  have ht := hs.large.datum.isUniqueInvolution_core
  have ctu := hs.comm_t_u
  have htP : t ∈ (P : Subgroup Y) := hs.hR₀P hs.t_mem_R₀
  have huP : u ∈ (P : Subgroup Y) := hs.hT₀P hs.u_mem_T₀
  have htA : t ∈ edgeCent (P : Subgroup Y) t u :=
    ⟨⟨htP, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr ctu⟩
  have huA : u ∈ edgeCent (P : Subgroup Y) t u :=
    ⟨⟨huP, Subgroup.mem_centralizer_singleton_iff.mpr ctu.symm⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hEA : Subgroup.closure ({t, u} : Set Y) ≤ edgeCent (P : Subgroup Y) t u :=
    Subgroup.closure_le _ |>.mpr (Set.insert_subset_iff.mpr ⟨htA, Set.singleton_subset_iff.mpr huA⟩)
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have htΛ : t ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
    hs.R₀_le_linkLayerAt hs.t_mem_R₀
  have huΛ : u ∈ linkLayer R t := hs.T₀_le_linkLayer hs.u_mem_T₀
  have hΛt : ∀ y ∈ linkLayer R t, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)).symm
  have hΛu : ∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u, u * y = y * u :=
    fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)).symm
  have key : ∀ e ∈ Subgroup.closure ({t, u} : Set Y), ActsTriv (linkLayer R t) (x ^ 2 * e) →
      ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (x ^ 2 * e) →
        x ^ 2 ∈ Subgroup.closure ({t, u} : Set Y) := by
    intro e he h1 h2
    have h3 := hs.eq_one_of_actsTriv
      ((edgeCent (P : Subgroup Y) t u).mul_mem ((edgeCent (P : Subgroup Y) t u).pow_mem hx 2)
        (hEA he)) h1 h2
    rw [eq_inv_of_mul_eq_one_left h3]
    exact Subgroup.inv_mem _ he
  rcases (hs.pi_t hx).2 h4 with ht' | ht' <;> rcases (hs.pi_u hx).2 h4 with hu' | hu'
  · exact key 1 (Subgroup.one_mem _) (by rw [mul_one]; exact ht') (by rw [mul_one]; exact hu')
  · exact key t htE (actsTriv_mul_of_comm hΛt ht') (actsTriv_mul_of_actsLike htΛ ht.sq hu')
  · exact key u huE (actsTriv_mul_of_actsLike huΛ hs.hu.sq ht') (actsTriv_mul_of_comm hΛu hu')
  · refine key (u * t) (Subgroup.mul_mem _ huE htE) ?_ ?_
    · rw [← mul_assoc]
      exact actsTriv_mul_of_comm hΛt (actsTriv_mul_of_actsLike huΛ hs.hu.sq ht')
    · rw [← ctu, ← mul_assoc]
      exact actsTriv_mul_of_comm hΛu (actsTriv_mul_of_actsLike htΛ ht.sq hu')

theorem Z2Set.pow_eight (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) : x ^ 8 = 1 :=
  hs.eq_one_of_actsTriv ((edgeCent (P : Subgroup Y) t u).pow_mem hx 8) (hs.pi_t hx).1
    (hs.pi_u hx).1

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
