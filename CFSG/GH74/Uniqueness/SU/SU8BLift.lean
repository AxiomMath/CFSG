module

public import CFSG.GH74.Uniqueness.SU.SU8BDefs
public import CFSG.GH74.Uniqueness.SU.SU8LocA
public import CFSG.GH74.Uniqueness.SU.SU8UAbs

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.SU.SU8.Setup CFSG.GH74.Uniqueness.SU.SU8.LocA
open scoped commutatorElement

namespace BLift

theorem exists_ppart {M N : Type*} [Group M] [Finite M] [Group N] (f : M →* N) {p : ℕ}
    (hp : p.Prime) {m : M} {s : ℕ} (hs : f m ^ (p ^ s) = 1) :
    ∃ g ∈ Subgroup.zpowers m, (∃ e : ℕ, g ^ (p ^ e) = 1) ∧ f g = f m := by
  have hn : orderOf m ≠ 0 := (orderOf_pos m).ne'
  obtain ⟨e, b, hpb, hnb⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hcop : Nat.Coprime b (p ^ s) :=
    Nat.Coprime.pow_right s ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb).symm
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 0 1
  refine ⟨m ^ k, Subgroup.pow_mem _ (Subgroup.mem_zpowers m) k, ⟨e, ?_⟩, ?_⟩
  · have hb : b ∣ k := (Nat.modEq_zero_iff_dvd.mp hk1)
    obtain ⟨c, hc⟩ := hb
    rw [← pow_mul, hc]
    have : m ^ (b * c * p ^ e) = (m ^ (orderOf m)) ^ c := by
      rw [← pow_mul]
      congr 1
      rw [hnb]; ring
    rw [this, pow_orderOf_eq_one, one_pow]
  · rw [map_pow]
    have h1 : orderOf (f m) ∣ p ^ s := orderOf_dvd_of_pow_eq_one hs
    have h2 : k ≡ 1 [MOD orderOf (f m)] := Nat.ModEq.of_dvd h1 hk2
    have := (pow_eq_pow_iff_modEq (x := f m) (n := k) (m := 1)).mpr h2
    rw [this, pow_one]

theorem conj_split {Y : Type*} [Group Y] {e w c : Y} (hc : c * e⁻¹ = e⁻¹ * c) :
    e * (w * c) * e⁻¹ * (w * c)⁻¹ = e * w * e⁻¹ * w⁻¹ := by
  calc e * (w * c) * e⁻¹ * (w * c)⁻¹ = e * w * (c * e⁻¹) * c⁻¹ * w⁻¹ := by group
    _ = e * w * (e⁻¹ * c) * c⁻¹ * w⁻¹ := by rw [hc]
    _ = e * w * e⁻¹ * w⁻¹ := by group

theorem exists_pow_eq {Y : Type*} [Group Y] [Finite Y] {yh y : Y} (hy' : y ∈ Subgroup.zpowers yh) :
    ∃ j : ℕ, yh ^ j = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
  refine ⟨(k % (orderOf yh : ℤ)).toNat, ?_⟩
  have hnn : 0 ≤ k % (orderOf yh : ℤ) := Int.emod_nonneg _ (by
    have := orderOf_pos yh
    exact_mod_cast this.ne')
  rw [← zpow_natCast, Int.toNat_of_nonneg hnn, zpow_mod_orderOf]

variable {X Y : Type} [Group X] [Group Y] {O L A : Subgroup X} [O.Normal] [L.Normal]

@[expose] def ACx (O L A : Subgroup X) [O.Normal] : Subgroup X where
  carrier := {a | a ∈ A ∧ ∀ m ∈ L, ⁅a, m⁆ ∈ O}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨A.mul_mem ha hb, fun m hm => ?_⟩
    have key : ⁅a * b, m⁆ = a * ⁅b, m⁆ * a⁻¹ * ⁅a, m⁆ := by
      simp only [commutatorElement_def]; group
    rw [key]
    exact O.mul_mem (by
      have := (inferInstance : O.Normal).conj_mem _ (hb' m hm) a
      simpa [mul_assoc] using this) (ha' m hm)
  one_mem' := ⟨A.one_mem, fun m _ => by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨A.inv_mem ha, fun m hm => ?_⟩
    have key : ⁅a⁻¹, m⁆ = a⁻¹ * ⁅a, m⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [key]
    have := (inferInstance : O.Normal).conj_mem _ (O.inv_mem (ha' m hm)) a⁻¹
    simpa using this

omit [L.Normal] in
theorem mem_ACx {a : X} : a ∈ ACx O L A ↔ a ∈ A ∧ ∀ m ∈ L, ⁅a, m⁆ ∈ O := Iff.rfl

omit [L.Normal] in
theorem ACx_le : ACx O L A ≤ A := fun _ h => h.1

structure BHyp (θ : X →* Y) (O L A : Subgroup X) [O.Normal] [L.Normal] : Prop where
  odd : Odd (Nat.card O)
  exp : ∀ a ∈ A, a * a = 1
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  dec0 : ∀ a ∈ A, ∃ l ∈ L, ∃ c : X, (∀ m ∈ L, ⁅c, m⁆ ∈ O) ∧ a = l * c
  OM : ∀ o ∈ O, θ o = 1
  M2 : ∀ x : X, θ x = 1 → ∃ l ∈ L, x * l⁻¹ ∈ O
  M3 : ∀ x : X, θ x = 1 → ∀ m ∈ L, ⁅x, m⁆ ∈ O
  M5 : ∀ x : X, θ x = 1 → ∃ a ∈ A, x * a⁻¹ ∈ O
  perf : ∀ x : X, (∀ m ∈ L, θ x * θ m = θ m * θ x) → ∀ m ∈ L, ⁅x, m⁆ ∈ O
  center : ∀ a ∈ L, (∀ m ∈ L, ⁅a, m⁆ ∈ O) → θ a = 1
  KC : ∀ x ∈ L.map θ, (∀ k ∈ L.map θ, x * k = k * x) → x = 1
  Z2 : 2 ≤ Nat.card ↥(A ⊓ θ.ker)
  Z4 : Nat.card ↥(A ⊓ θ.ker) ≤ 4

namespace BHyp

variable {θ : X →* Y} (h : BHyp θ O L A)
include h

theorem inj_A {a b : X} (ha : a ∈ A) (hb : b ∈ A) (hab : a⁻¹ * b ∈ O) : a = b := by
  have h1 : (a⁻¹ * b) ^ (2 ^ 1) = 1 := by
    have := h.exp _ (A.mul_mem (A.inv_mem ha) hb)
    simpa [pow_one, sq] using this
  exact inv_mul_eq_one.mp (eq_one_of_mem_odd h.odd hab h1)

theorem ker_le_ACx {a : X} (ha : a ∈ A) (h1 : θ a = 1) : a ∈ ACx O L A :=
  ⟨ha, h.M3 a h1⟩

theorem mem_ACx_of_theta {a : X} (ha : a ∈ A) (hc : ∀ m ∈ L, θ a * θ m = θ m * θ a) :
    a ∈ ACx O L A := ⟨ha, h.perf a hc⟩

theorem theta_comm_of_ACx {a : X} (ha : a ∈ ACx O L A) :
    ∀ m ∈ L, θ a * θ m = θ m * θ a := by
  intro m hm
  have h1 : θ ⁅a, m⁆ = 1 := h.OM _ (ha.2 m hm)
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

variable [Finite X]

theorem mem_L_of_theta {a : X} (ha : a ∈ A) (hm : θ a ∈ L.map θ) : a ∈ L := by
  obtain ⟨l₁, hl₁, hl₁a⟩ := hm
  have hker : θ (l₁⁻¹ * a) = 1 := by rw [map_mul, map_inv, hl₁a, inv_mul_cancel]
  obtain ⟨l, hl, hxl⟩ := h.M2 _ hker
  have ho : l⁻¹ * (l₁⁻¹ * a * l⁻¹) * l ∈ O :=
    (inferInstance : O.Normal).conj_mem _ hxl l⁻¹ |> fun h' => by simpa using h'
  refine mem_of_mul_odd (O := O) h.odd (L.mul_mem hl₁ hl) ho (by group) (k := 1) ?_
  simpa [pow_one, sq] using h.exp a ha

theorem inf_L_eq : ACx O L A ⊓ L = A ⊓ θ.ker := by
  ext a
  constructor
  · rintro ⟨⟨haA, ha⟩, haL⟩
    exact ⟨haA, MonoidHom.mem_ker.mpr (h.center a haL ha)⟩
  · rintro ⟨haA, hk⟩
    have hk' := MonoidHom.mem_ker.mp hk
    exact ⟨h.ker_le_ACx haA hk',
      h.mem_L_of_theta haA ⟨1, L.one_mem, by rw [hk', map_one]⟩⟩

omit [Finite X] in
theorem act_C {g : X} (hgL : g ∈ L) (hgN : g ∈ normalizer (A : Set X)) {c : X}
    (hc : c ∈ ACx O L A) : g * c * g⁻¹ = c := by
  have hd : g * c * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgN c).mp hc.1
  have h1 : ⁅c, g⁆ ∈ O := hc.2 g hgL
  have h2 : (g * c * g⁻¹) * c⁻¹ ∈ O := by
    have : (g * c * g⁻¹) * c⁻¹ = ⁅g, c⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [this, ← commutatorElement_inv]
    exact O.inv_mem h1
  have h3 : (g * c * g⁻¹) * c⁻¹ = 1 := by
    refine eq_one_of_mem_odd h.odd h2 (k := 1) ?_
    have hm : (g * c * g⁻¹) * c⁻¹ ∈ A := A.mul_mem hd (A.inv_mem hc.1)
    simpa [pow_one, sq] using h.exp _ hm
  exact mul_inv_eq_one.mp h3

variable {Yh : Subgroup Y}

omit [Finite X] in
theorem theta_dec (hLoc : LocOut (L.map θ) (A.map θ) Yh 3) {a : X} (ha : a ∈ A) :
    ∃ w ∈ A.map θ ⊓ L.map θ, ∃ c ∈ A.map θ ⊓ centralizer ((L.map θ : Subgroup Y) : Set Y),
      θ a = w * c ∧ (a ∈ ACx O L A ↔ w = 1) := by
  obtain ⟨w, hw, c, hc, hθa⟩ := hLoc.split (θ a) ⟨a, ha, rfl⟩
  refine ⟨w, hw, c, hc, hθa, ⟨fun haC => ?_, fun hw1 => ?_⟩⟩
  · have hcen : θ a ∈ centralizer ((L.map θ : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨m, hm, rfl⟩
      exact (h.theta_comm_of_ACx haC m hm).symm
    have hw' : w ∈ centralizer ((L.map θ : Subgroup Y) : Set Y) := by
      have : w = θ a * c⁻¹ := by rw [hθa]; group
      rw [this]
      exact (centralizer _).mul_mem hcen ((centralizer _).inv_mem hc.2)
    exact h.KC w hw.2 (fun k hk => (Subgroup.mem_centralizer_iff.mp hw' k hk).symm)
  · apply h.mem_ACx_of_theta ha
    intro m hm
    rw [hθa, hw1, one_mul]
    exact (Subgroup.mem_centralizer_iff.mp hc.2 (θ m) ⟨m, hm, rfl⟩).symm

theorem dec (hLoc : LocOut (L.map θ) (A.map θ) Yh 3) :
    ∀ a ∈ A, ∃ l ∈ A ⊓ L, ∃ c ∈ A, (∀ m ∈ L, ⁅c, m⁆ ∈ O) ∧ a = l * c := by
  intro a ha
  obtain ⟨w, hw, c, hc, hθa, -⟩ := h.theta_dec hLoc ha
  obtain ⟨⟨u₀, hu₀A, rfl⟩, hwK⟩ := hw
  obtain ⟨⟨c₀, hc₀A, rfl⟩, hcC⟩ := hc
  have hu₀L : u₀ ∈ L := h.mem_L_of_theta hu₀A hwK
  have hc₀C : c₀ ∈ ACx O L A := h.mem_ACx_of_theta hc₀A (fun m hm =>
    (Subgroup.mem_centralizer_iff.mp hcC (θ m) ⟨m, hm, rfl⟩).symm)
  have hρA : (u₀ * c₀)⁻¹ * a ∈ A := A.mul_mem (A.inv_mem (A.mul_mem hu₀A hc₀A)) ha
  have hρ : θ ((u₀ * c₀)⁻¹ * a) = 1 := by
    rw [map_mul, map_inv, map_mul, hθa, inv_mul_cancel]
  have hρC : (u₀ * c₀)⁻¹ * a ∈ ACx O L A := h.ker_le_ACx hρA hρ
  refine ⟨u₀, ⟨hu₀A, hu₀L⟩, c₀ * ((u₀ * c₀)⁻¹ * a), A.mul_mem hc₀A hρA, ?_, ?_⟩
  · exact ((ACx O L A).mul_mem hc₀C hρC).2
  · group

omit [Finite X] in
theorem card_A (hLoc : LocOut (L.map θ) (A.map θ) Yh 3) :
    Nat.card A = 8 * Nat.card (ACx O L A) := by
  classical
  set Ah : Subgroup Y := A.map θ with hAh
  set Kh : Subgroup Y := L.map θ with hKh
  let θA : ↥A →* Y := θ.comp A.subtype
  let θC : ↥(ACx O L A) →* Y := θ.comp (ACx O L A).subtype
  have hθA_range : θA.range = Ah := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hθC_range : θC.range = Ah ⊓ centralizer (Kh : Set Y) := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      have hcc : θ (c : X) ∈ centralizer (Kh : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨m, hm, rfl⟩
        exact (h.theta_comm_of_ACx c.2 m hm).symm
      exact ⟨⟨c.1, c.2.1, rfl⟩, hcc⟩
    · rintro y ⟨⟨a, ha, rfl⟩, hy⟩
      have hc : ∀ m ∈ L, θ a * θ m = θ m * θ a := by
        intro m hm
        exact (Subgroup.mem_centralizer_iff.mp hy (θ m) ⟨m, hm, rfl⟩).symm
      exact ⟨⟨a, h.mem_ACx_of_theta ha hc⟩, rfl⟩
  have hkA : θA.ker = (A ⊓ θ.ker).subgroupOf A := by
    ext a
    simp [θA, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  have hkC : θC.ker = (A ⊓ θ.ker).subgroupOf (ACx O L A) := by
    ext a
    simp only [θC, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply,
      Subgroup.subtype_apply, Subgroup.mem_inf]
    exact ⟨fun h1 => ⟨a.2.1, h1⟩, fun h1 => h1.2⟩
  have hleC : A ⊓ θ.ker ≤ ACx O L A := fun a ha => h.ker_le_ACx ha.1 (MonoidHom.mem_ker.mp ha.2)
  have hAcard : Nat.card A = Nat.card Ah * Nat.card ↥(A ⊓ θ.ker) := by
    have := UAbs.card_eq_range_mul_ker θA
    rw [hθA_range, hkA,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ θ.ker ≤ A)).toEquiv] at this
    exact this
  have hCcard : Nat.card (ACx O L A) =
      Nat.card ↥(Ah ⊓ centralizer (Kh : Set Y)) * Nat.card ↥(A ⊓ θ.ker) := by
    have := UAbs.card_eq_range_mul_ker θC
    rw [hθC_range, hkC, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleC).toEquiv] at this
    exact this
  have hAhcard : Nat.card Ah = 8 * Nat.card ↥(Ah ⊓ centralizer (Kh : Set Y)) := by
    let f : ↥(Ah ⊓ Kh) × ↥(Ah ⊓ centralizer (Kh : Set Y)) → ↥Ah := fun p =>
      ⟨p.1 * p.2, Ah.mul_mem p.1.2.1 p.2.2.1⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨⟨w, hw⟩, ⟨c, hc⟩⟩ ⟨⟨w', hw'⟩, ⟨c', hc'⟩⟩ hh
        have h1 : w * c = w' * c' := congrArg Subtype.val hh
        have h2 : w'⁻¹ * w = c' * c⁻¹ := by
          calc w'⁻¹ * w = w'⁻¹ * (w * c) * c⁻¹ := by group
            _ = w'⁻¹ * (w' * c') * c⁻¹ := by rw [h1]
            _ = c' * c⁻¹ := by group
        have hmemK : w'⁻¹ * w ∈ Kh := Kh.mul_mem (Kh.inv_mem hw'.2) hw.2
        have hmemC : w'⁻¹ * w ∈ centralizer (Kh : Set Y) := by
          rw [h2]
          exact (centralizer (Kh : Set Y)).mul_mem hc'.2
            ((centralizer (Kh : Set Y)).inv_mem hc.2)
        have h3 : w'⁻¹ * w = 1 :=
          h.KC _ hmemK (fun k hk => (Subgroup.mem_centralizer_iff.mp hmemC k hk).symm)
        have hww : w = w' := (inv_mul_eq_one.mp h3).symm
        subst hww
        have hcc : c = c' := mul_left_cancel h1
        subst hcc
        rfl
      · rintro ⟨a, ha⟩
        obtain ⟨u, hu, c, hc, rfl⟩ := hLoc.split a ha
        exact ⟨(⟨u, hu⟩, ⟨c, hc⟩), rfl⟩
    have := Nat.card_congr (Equiv.ofBijective f hf)
    rw [Nat.card_prod, hLoc.card_Z] at this
    rw [← this]; norm_num
  rw [hAcard, hAhcard, hCcard]
  ring

variable [Finite Y] in
theorem gen (hLoc : LocOut (L.map θ) (A.map θ) Yh 3) :
    ∃ g₀ ∈ L ⊓ normalizer (A : Set X), (∃ e : ℕ, g₀ ^ (7 ^ e) = 1) ∧
      (∀ a ∈ A, g₀ ^ 7 * a * (g₀ ^ 7)⁻¹ = a) ∧
      (∀ a ∈ A, a ∉ ACx O L A → ∀ j : ℕ, 0 < j → j < 7 →
        g₀ ^ j * a * (g₀ ^ j)⁻¹ * a⁻¹ ∉ ACx O L A) ∧
      (∀ a ∈ A, a ∉ ACx O L A → ∀ b ∈ A, b ∉ ACx O L A →
        ∃ j : ℕ, g₀ ^ j * a * (g₀ ^ j)⁻¹ * b⁻¹ ∈ ACx O L A) ∧
      (∀ m ∈ L ⊓ normalizer (A : Set X), ∃ j : ℕ,
        ∀ a ∈ A, m * a * m⁻¹ * (g₀ ^ j * a * (g₀ ^ j)⁻¹)⁻¹ ∈ ACx O L A) := by
  classical
  set Ah : Subgroup Y := A.map θ with hAh
  set Kh : Subgroup Y := L.map θ with hKh
  have hcyc : IsCyclic ↥Yh := hLoc.cyclic
  obtain ⟨y₀, hy₀⟩ := IsCyclic.exists_generator (α := ↥Yh)
  set yh : Y := (y₀ : Y) with hyh
  have hYcard : Nat.card Yh = 7 := by
    have := hLoc.card_Y
    norm_num at this
    omega
  have hord : orderOf yh = 7 := by
    rw [hyh, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy₀, hYcard]
  have hyh7 : yh ^ 7 = 1 := by rw [← hord]; exact pow_orderOf_eq_one yh
  have hyhY : yh ∈ Yh := y₀.2
  have hyhK : yh ∈ Kh := hLoc.le hyhY
  have hne : ∀ j : ℕ, 0 < j → j < 7 → yh ^ j ≠ 1 := fun j hj0 hj7 =>
    pow_ne_one_of_lt_orderOf hj0.ne' (by rw [hord]; exact hj7)
  have hpow : ∀ y ∈ Yh, ∃ j : ℕ, yh ^ j = y := by
    intro y hy
    have : (⟨y, hy⟩ : ↥Yh) ∈ Subgroup.zpowers y₀ := hy₀ _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp this
    exact exists_pow_eq (Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩)
  obtain ⟨y₁, hy₁L, hy₁⟩ : ∃ y₁ ∈ L, θ y₁ = yh := id hyhK
  have hdec := h.dec hLoc
  have hyhN : yh ∈ normalizer (Ah : Set Y) := hLoc.norm hyhY
  have hmA : ∀ a ∈ A, y₁⁻¹ * a * y₁ ∈ A ⊔ O := by
    intro a ha
    have h1 : θ (y₁⁻¹ * a * y₁) ∈ Ah := by
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer (Ah : Set Y)).inv_mem hyhN)
        (θ a)).mp ⟨a, ha, rfl⟩
      rw [map_mul, map_mul, map_inv, hy₁]
      simpa using this
    obtain ⟨a', ha', ha'e⟩ := h1
    have hker : θ (a'⁻¹ * (y₁⁻¹ * a * y₁)) = 1 := by rw [map_mul, map_inv, ha'e, inv_mul_cancel]
    obtain ⟨a'', ha'', ho⟩ := h.M5 _ hker
    have e : y₁⁻¹ * a * y₁ = (a' * (a'⁻¹ * (y₁⁻¹ * a * y₁) * a''⁻¹) * a'⁻¹) * (a' * a'') := by
      group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_)
      (Subgroup.mem_sup_left (A.mul_mem ha' ha''))
    exact (inferInstance : O.Normal).conj_mem _ ho a'
  obtain ⟨r, hr, hg₁N⟩ := exists_mul_mem_normalizer h.odd h.exp hdec hy₁L hmA
  set g₁ : X := y₁ * r with hg₁
  have hg₁L : g₁ ∈ L := L.mul_mem hy₁L hr.1
  have hθg₁ : θ g₁ = yh := by rw [hg₁, map_mul, hy₁, h.OM r hr.2, mul_one]
  obtain ⟨g₀, hg₀mem, ⟨e, he⟩, hθg₀⟩ := exists_ppart θ (p := 7) (by norm_num) (m := g₁) (s := 1)
    (by rw [hθg₁]; simpa using hyh7)
  have hg₀LN : g₀ ∈ L ⊓ normalizer (A : Set X) :=
    (Subgroup.zpowers_le.mpr ⟨hg₁L, hg₁N⟩ :
      Subgroup.zpowers g₁ ≤ L ⊓ normalizer (A : Set X)) hg₀mem
  have hθg₀' : θ g₀ = yh := by rw [hθg₀, hθg₁]
  have hg₀N : g₀ ∈ normalizer (A : Set X) := hg₀LN.2
  have hpowN : ∀ i : ℕ, g₀ ^ i ∈ normalizer (A : Set X) := fun i => pow_mem hg₀N i
  have hcomm' : ∀ c ∈ centralizer (Kh : Set Y), ∀ k ∈ Kh, k * c = c * k := fun c hc k hk =>
    Subgroup.mem_centralizer_iff.mp hc k hk
  have hpowK : ∀ i : ℕ, yh ^ i ∈ Kh := fun i => Kh.pow_mem hyhK i
  refine ⟨g₀, hg₀LN, ⟨e, he⟩, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have hθ7 : θ (g₀ ^ 7) = 1 := by rw [map_pow, hθg₀', hyh7]
    obtain ⟨a'', ha'', ho⟩ := h.M5 _ hθ7
    have hcomm := h.comm a'' ha'' a ha
    have e1 : g₀ ^ 7 * a * (g₀ ^ 7)⁻¹ =
        (g₀ ^ 7 * a''⁻¹) * a * (g₀ ^ 7 * a''⁻¹)⁻¹ := by
      calc g₀ ^ 7 * a * (g₀ ^ 7)⁻¹
          = (g₀ ^ 7 * a''⁻¹) * (a'' * a * a''⁻¹) * (g₀ ^ 7 * a''⁻¹)⁻¹ := by group
        _ = (g₀ ^ 7 * a''⁻¹) * a * (g₀ ^ 7 * a''⁻¹)⁻¹ := by rw [hcomm]; group
    have hxA : g₀ ^ 7 * a * (g₀ ^ 7)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hpowN 7) a).mp ha
    refine (h.inj_A ha hxA ?_).symm
    rw [e1]
    have e2 : a⁻¹ * ((g₀ ^ 7 * a''⁻¹) * a * (g₀ ^ 7 * a''⁻¹)⁻¹) =
        (a⁻¹ * (g₀ ^ 7 * a''⁻¹) * a) * (g₀ ^ 7 * a''⁻¹)⁻¹ := by group
    rw [e2]
    refine O.mul_mem ?_ (O.inv_mem ho)
    have := (inferInstance : O.Normal).conj_mem _ ho a⁻¹
    simpa using this
  · intro a ha haC j hj0 hj7 hmem
    obtain ⟨w, hw, c, hc, hθa, hwiff⟩ := h.theta_dec hLoc ha
    have hw1 : w ≠ 1 := fun h1 => haC (hwiff.mpr h1)
    have hθx : θ (g₀ ^ j * a * (g₀ ^ j)⁻¹ * a⁻¹) =
        yh ^ j * (w * c) * (yh ^ j)⁻¹ * (w * c)⁻¹ := by
      simp only [map_mul, map_inv, map_pow, hθg₀', hθa]
    have hc' : c * (yh ^ j)⁻¹ = (yh ^ j)⁻¹ * c :=
      (hcomm' c hc.2 _ (Kh.inv_mem (hpowK j))).symm
    rw [conj_split hc'] at hθx
    have hcentral := h.theta_comm_of_ACx hmem
    have hKmem : yh ^ j * w * (yh ^ j)⁻¹ * w⁻¹ ∈ Kh :=
      Kh.mul_mem (Kh.mul_mem (Kh.mul_mem (hpowK j) hw.2) (Kh.inv_mem (hpowK j)))
        (Kh.inv_mem hw.2)
    have h1 : yh ^ j * w * (yh ^ j)⁻¹ * w⁻¹ = 1 := by
      apply h.KC _ hKmem
      rintro _ ⟨m, hm, rfl⟩
      rw [← hθx]
      exact hcentral m hm
    have h2 : yh ^ j * w * (yh ^ j)⁻¹ = w := mul_inv_eq_one.mp h1
    exact hLoc.free (yh ^ j) (Yh.pow_mem hyhY j) (hne j hj0 hj7) w hw hw1 h2
  · intro a ha haC b hb hbC
    obtain ⟨wa, hwa, ca, hca, hθa, hwiffa⟩ := h.theta_dec hLoc ha
    obtain ⟨wb, hwb, cb, hcb, hθb, hwiffb⟩ := h.theta_dec hLoc hb
    have hwa1 : wa ≠ 1 := fun h1 => haC (hwiffa.mpr h1)
    have hwb1 : wb ≠ 1 := fun h1 => hbC (hwiffb.mpr h1)
    obtain ⟨y, hyY, hy⟩ := hLoc.trans wa hwa hwa1 wb hwb hwb1
    obtain ⟨j, hj⟩ := hpow y hyY
    refine ⟨j, ?_⟩
    have hyK : y ∈ Kh := by rw [← hj]; exact hpowK j
    have hcacb : ca * cb⁻¹ ∈ centralizer (Kh : Set Y) :=
      (centralizer (Kh : Set Y)).mul_mem hca.2 ((centralizer (Kh : Set Y)).inv_mem hcb.2)
    have hθx : θ (g₀ ^ j * a * (g₀ ^ j)⁻¹ * b⁻¹) = ca * cb⁻¹ := by
      simp only [map_mul, map_inv, map_pow, hθg₀', hθa, hθb, hj]
      have hyca : y * ca * y⁻¹ = ca := by
        have := hcomm' ca hca.2 y hyK
        rw [this]; group
      have hcc : wb * (ca * cb⁻¹) = (ca * cb⁻¹) * wb := hcomm' _ hcacb wb hwb.2
      calc y * (wa * ca) * y⁻¹ * (wb * cb)⁻¹
          = (y * wa * y⁻¹) * (y * ca * y⁻¹) * cb⁻¹ * wb⁻¹ := by group
        _ = wb * ca * cb⁻¹ * wb⁻¹ := by rw [hy, hyca]
        _ = wb * (ca * cb⁻¹) * wb⁻¹ := by group
        _ = (ca * cb⁻¹) * wb * wb⁻¹ := by rw [hcc]
        _ = ca * cb⁻¹ := by group
    have hxA : g₀ ^ j * a * (g₀ ^ j)⁻¹ * b⁻¹ ∈ A :=
      A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hpowN j) a).mp ha) (A.inv_mem hb)
    apply h.mem_ACx_of_theta hxA
    intro m hm
    rw [hθx]
    exact (hcomm' _ hcacb (θ m) ⟨m, hm, rfl⟩).symm
  · intro m hm
    have hmθK : θ m ∈ Kh := ⟨m, hm.1, rfl⟩
    have hmθN : θ m ∈ normalizer (Ah : Set Y) := mem_normalizer_of_conj_le (fun x hx => by
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨m * a * m⁻¹, (Subgroup.mem_normalizer_iff.mp hm.2 a).mp ha, by simp [map_mul]⟩)
    obtain ⟨y, hyY, hy⟩ := hLoc.action (θ m) hmθK hmθN
    obtain ⟨j, hj⟩ := hpow y hyY
    refine ⟨j, fun a ha => ?_⟩
    have hxA : m * a * m⁻¹ * (g₀ ^ j * a * (g₀ ^ j)⁻¹)⁻¹ ∈ A :=
      A.mul_mem ((Subgroup.mem_normalizer_iff.mp hm.2 a).mp ha)
        (A.inv_mem ((Subgroup.mem_normalizer_iff.mp (hpowN j) a).mp ha))
    apply h.ker_le_ACx hxA
    have h1 := hy (θ a) ⟨a, ha, rfl⟩
    simp only [map_mul, map_inv, map_pow, hθg₀']
    rw [h1, hj]
    group

theorem two_elt_X (hLoc : LocOut (L.map θ) (A.map θ) Yh 3)
    (htwo : ∃ p ∈ L, (∃ s : ℕ, p ^ (2 ^ s) ∈ O) ∧ (∀ a ∈ A, p⁻¹ * a * p ∈ A ⊔ O) ∧
      ∃ a ∈ A, p * a * p⁻¹ * a⁻¹ ∉ O) :
    ∃ t ∈ L ⊓ normalizer (A : Set X), (∃ k : ℕ, t ^ (2 ^ k) = 1) ∧ ∃ a ∈ A, t * a * t⁻¹ ≠ a := by
  obtain ⟨p, hpL, ⟨s, hs⟩, hpA, a₀, ha₀, hna⟩ := htwo
  obtain ⟨r, hr, hm₁N⟩ := exists_mul_mem_normalizer h.odd h.exp (h.dec hLoc) hpL hpA
  let bar : X →* X ⧸ O := QuotientGroup.mk' O
  have hbarr : bar r = 1 := (QuotientGroup.eq_one_iff r).mpr hr.2
  have hbs : bar (p * r) ^ (2 ^ s) = 1 := by
    rw [map_mul, hbarr, mul_one, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hs
  obtain ⟨t, htmem, ⟨e, he⟩, hbt⟩ := exists_ppart bar Nat.prime_two hbs
  have htLN : t ∈ L ⊓ normalizer (A : Set X) :=
    (Subgroup.zpowers_le.mpr ⟨L.mul_mem hpL hr.1, hm₁N⟩ :
      Subgroup.zpowers (p * r) ≤ L ⊓ normalizer (A : Set X)) htmem
  refine ⟨t, htLN, ⟨e, he⟩, a₀, ha₀, fun hta => hna ?_⟩
  have hbt' : bar t = bar p := by rw [hbt, map_mul, hbarr, mul_one]
  have ho : t⁻¹ * p ∈ O := QuotientGroup.eq.mp hbt'
  have e1 : p * a₀ * p⁻¹ * a₀⁻¹ = t * ((t⁻¹ * p) * a₀ * (t⁻¹ * p)⁻¹ * a₀⁻¹) * t⁻¹ := by
    have : t * a₀ * t⁻¹ = a₀ := hta
    calc p * a₀ * p⁻¹ * a₀⁻¹
        = t * ((t⁻¹ * p) * a₀ * (t⁻¹ * p)⁻¹) * t⁻¹ * a₀⁻¹ := by group
      _ = t * ((t⁻¹ * p) * a₀ * (t⁻¹ * p)⁻¹ * a₀⁻¹) * t⁻¹ * (t * a₀ * t⁻¹) * a₀⁻¹ := by group
      _ = t * ((t⁻¹ * p) * a₀ * (t⁻¹ * p)⁻¹ * a₀⁻¹) * t⁻¹ := by rw [this]; group
  rw [e1]
  have hO' : (t⁻¹ * p) * a₀ * (t⁻¹ * p)⁻¹ * a₀⁻¹ ∈ O := by
    have h1 : (t⁻¹ * p) * (a₀ * (t⁻¹ * p)⁻¹ * a₀⁻¹) ∈ O :=
      O.mul_mem ho ((inferInstance : O.Normal).conj_mem _ (O.inv_mem ho) a₀)
    simpa [mul_assoc] using h1
  have := (inferInstance : O.Normal).conj_mem _ hO' t
  simpa [mul_assoc] using this

theorem card_ker_eq_two (hV : Nat.card (ACx O L A) = 2) : Nat.card ↥(A ⊓ θ.ker) = 2 := by
  have h1 := Subgroup.card_le_of_le (inf_le_left : ACx O L A ⊓ L ≤ ACx O L A)
  rw [h.inf_L_eq] at h1
  have := h.Z2
  omega

theorem le_L_of_card (hLoc : LocOut (L.map θ) (A.map θ) Yh 3) (hV : Nat.card (ACx O L A) = 2) :
    A ≤ L := by
  have hc1 : Nat.card ↥(ACx O L A ⊓ L) = 2 := by
    have h1 := Subgroup.card_le_of_le (inf_le_left : ACx O L A ⊓ L ≤ ACx O L A)
    have h2 := h.card_ker_eq_two hV
    rw [← h.inf_L_eq] at h2
    omega
  have heq : ACx O L A ⊓ L = ACx O L A :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hV, hc1])
  have hACL : ∀ c ∈ ACx O L A, c ∈ L := fun c hc => by
    have : c ∈ ACx O L A ⊓ L := by rw [heq]; exact hc
    exact this.2
  intro a ha
  obtain ⟨l, hl, c, hcA, hc, rfl⟩ := h.dec hLoc a ha
  exact L.mul_mem hl.2 (hACL c ⟨hcA, hc⟩)

theorem cent_X (hLoc : LocOut (L.map θ) (A.map θ) Yh 3) (hV : Nat.card (ACx O L A) = 2)
    (hInn : ∀ g : X, ∃ m ∈ L, ∀ l ∈ L,
      (QuotientGroup.mk' O) (g * l * g⁻¹) = (QuotientGroup.mk' O) (m * l * m⁻¹))
    {g : X} (hg : g ∈ normalizer (A : Set X)) :
    ∃ m ∈ L ⊓ normalizer (A : Set X), ∀ a ∈ A, g * a * g⁻¹ = m * a * m⁻¹ := by
  have hAL := h.le_L_of_card hLoc hV
  obtain ⟨m₀, hm₀L, hm₀⟩ := hInn g
  have hgA : ∀ a ∈ A, g⁻¹ * a * g ∈ A := fun a ha => by
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (A : Set X)).inv_mem hg) a).mp ha
    simpa using this
  have hmA : ∀ a ∈ A, m₀⁻¹ * a * m₀ ∈ A ⊔ O := by
    intro a ha
    have hl : m₀⁻¹ * a * m₀ ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hm₀L) (hAL ha)) hm₀L
    have h1 := hm₀ _ hl
    have e : m₀ * (m₀⁻¹ * a * m₀) * m₀⁻¹ = a := by group
    rw [e] at h1
    have h1' : (g * (m₀⁻¹ * a * m₀) * g⁻¹)⁻¹ * a ∈ O := QuotientGroup.eq.mp h1
    have h2 : (g⁻¹ * a * g)⁻¹ * (m₀⁻¹ * a * m₀) ∈ O := by
      have := (inferInstance : O.Normal).conj_mem _ (O.inv_mem h1') g⁻¹
      have e2 : g⁻¹ * ((g * (m₀⁻¹ * a * m₀) * g⁻¹)⁻¹ * a)⁻¹ * g⁻¹⁻¹ =
          (g⁻¹ * a * g)⁻¹ * (m₀⁻¹ * a * m₀) := by group
      rwa [e2] at this
    have e3 : m₀⁻¹ * a * m₀ = (g⁻¹ * a * g) * ((g⁻¹ * a * g)⁻¹ * (m₀⁻¹ * a * m₀)) := by group
    rw [e3]
    exact Subgroup.mul_mem_sup (hgA a ha) h2
  obtain ⟨r, hr, hrN⟩ := exists_mul_mem_normalizer h.odd h.exp (h.dec hLoc) hm₀L hmA
  refine ⟨m₀ * r, ⟨L.mul_mem hm₀L hr.1, hrN⟩, fun a ha => ?_⟩
  have hqr : (QuotientGroup.mk' O) r = 1 := (QuotientGroup.eq_one_iff r).mpr hr.2
  have hgA' : g * a * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  have hmA' : (m₀ * r) * a * (m₀ * r)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hrN a).mp ha
  have h1 := hm₀ a (hAL ha)
  have h2 : (QuotientGroup.mk' O) ((m₀ * r) * a * (m₀ * r)⁻¹) =
      (QuotientGroup.mk' O) (m₀ * a * m₀⁻¹) := by
    simp only [map_mul, map_inv, hqr, mul_one]
  exact h.inj_A hgA' hmA' (QuotientGroup.eq.mp (h1.trans h2.symm))

variable [Finite Y] in
theorem caseB (hLoc : LocOut (L.map θ) (A.map θ) Yh 3) {z : X} (hzA : z ∈ ACx O L A) (hz1 : z ≠ 1)
    (htwo : Nat.card ↥(A ⊓ θ.ker) = 2 → A ≤ L → ∃ p ∈ L, (∃ s : ℕ, p ^ (2 ^ s) ∈ O) ∧
      (∀ a ∈ A, p⁻¹ * a * p ∈ A ⊔ O) ∧ ∃ a ∈ A, p * a * p⁻¹ * a⁻¹ ∉ O)
    (hInn : Nat.card ↥(A ⊓ θ.ker) = 2 → ∀ g : X, ∃ m ∈ L, ∀ l ∈ L,
      (QuotientGroup.mk' O) (g * l * g⁻¹) = (QuotientGroup.mk' O) (m * l * m⁻¹)) :
    CaseB L A (ACx O L A) z where
  A_exp := h.exp
  A_comm := h.comm
  V₀_le := ACx_le
  z_mem := hzA
  z_ne := hz1
  card_A := h.card_A hLoc
  act_C := fun g hg c hc => h.act_C hg.1 hg.2 hc
  inf_gt := by
    rw [h.inf_L_eq]
    have := h.Z2
    omega
  inf_le := by
    rw [h.inf_L_eq]
    exact h.Z4
  gen := h.gen hLoc
  two_elt := fun hV =>
    h.two_elt_X hLoc (htwo (h.card_ker_eq_two hV) (h.le_L_of_card hLoc hV))
  cent := fun hV g hg _ => h.cent_X hLoc hV (hInn (h.card_ker_eq_two hV)) hg

end BHyp

end BLift

end CFSG.GH74.Uniqueness.SU.SU8
