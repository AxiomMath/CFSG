module

public import CFSG.Open.LocalVocabulary

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator

open Subgroup CFSG.Open
open scoped Pointwise

section Basic

variable {Y : Type*} [Group Y]

@[expose] def centerIn (K : Subgroup Y) : Subgroup Y := (Subgroup.center K).map K.subtype

theorem mem_centerIn_iff {K : Subgroup Y} {x : Y} :
    x ∈ centerIn K ↔ x ∈ K ∧ ∀ k ∈ K, k * x = x * k := by
  constructor
  · rintro ⟨⟨x', hx'⟩, hz, rfl⟩
    refine ⟨hx', fun k hk => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨k, hk⟩)
  · rintro ⟨hxK, hx⟩
    exact ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hx g g.2), rfl⟩

theorem centerIn_le {K : Subgroup Y} : centerIn K ≤ K := fun _ hx => (mem_centerIn_iff.1 hx).1

theorem centerIn_le_centralizer (K : Subgroup Y) : centerIn K ≤ centralizer (K : Set Y) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  exact fun k hk => (mem_centerIn_iff.1 hx).2 k hk

theorem mem_centerIn_of_mem_centralizer {K : Subgroup Y} {x : Y} (hK : x ∈ K)
    (hC : x ∈ centralizer (K : Set Y)) : x ∈ centerIn K :=
  mem_centerIn_iff.2 ⟨hK, fun k hk => Subgroup.mem_centralizer_iff.1 hC k hk⟩

theorem centerIn_normal {K : Subgroup Y} (hK : K.Normal) : (centerIn K).Normal := by
  refine ⟨fun x hx y => ?_⟩
  rw [mem_centerIn_iff] at hx ⊢
  refine ⟨hK.conj_mem x hx.1 y, fun k hk => ?_⟩
  have h := hx.2 _ (hK.conj_mem k hk y⁻¹)
  calc k * (y * x * y⁻¹) = y * ((y⁻¹ * k * y) * x) * y⁻¹ := by group
    _ = y * (x * (y⁻¹ * k * y)) * y⁻¹ := by
      rw [show y⁻¹ * k * y = y⁻¹ * k * y⁻¹⁻¹ by simp, h]
    _ = y * x * y⁻¹ * k := by group

theorem centralizer_normal {K : Subgroup Y} (hK : K.Normal) :
    (centralizer (K : Set Y)).Normal := by
  refine ⟨fun x hx y => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro k hk
  have h := hx _ (hK.conj_mem k hk y⁻¹)
  calc k * (y * x * y⁻¹) = y * ((y⁻¹ * k * y) * x) * y⁻¹ := by group
    _ = y * (x * (y⁻¹ * k * y)) * y⁻¹ := by
      rw [show y⁻¹ * k * y = y⁻¹ * k * y⁻¹⁻¹ by simp, h]
    _ = y * x * y⁻¹ * k := by group

theorem mem_centerIn_of_orderOf_eq_three [Finite Y] (Rb : Sylow 3 Y) {K : Subgroup Y}
    (hK : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ centralizer (K : Set Y), orderOf c = 3 → c ∈ centerIn K)
    {c : Y} (hc : c ∈ centralizer (K : Set Y)) (h3 : orderOf c = 3) : c ∈ centerIn K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3]; simp)
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S Rb
  have hcS : c ∈ (S : Subgroup Y) := hS (mem_zpowers c)
  have hgS : g * c * g⁻¹ ∈ (Rb : Subgroup Y) := by
    have h1 := Subgroup.smul_mem_pointwise_smul c (MulAut.conj g) (S : Subgroup Y) hcS
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    simpa [MulAut.smul_def] using h1
  have hcc : g * c * g⁻¹ ∈ centralizer (K : Set Y) := (centralizer_normal hK).conj_mem c hc g
  have hord : orderOf (g * c * g⁻¹) = 3 := by
    have := (MulAut.conj g).orderOf_eq c
    rw [MulAut.conj_apply] at this
    rw [this, h3]
  have := hcent _ ⟨hgS, hcc⟩ hord
  have h2 := (centerIn_normal hK).conj_mem _ this g⁻¹
  simpa [mul_assoc] using h2

end Basic

section ThreePart

theorem exists_unique_three_part {A : Type*} [CommGroup A] [Finite A]
    (hA : (Nat.card A).factorization 3 = 1) :
    ∃ z : A, orderOf z = 3 ∧ ∀ w : A, (∃ n : ℕ, w ^ 3 ^ n = 1) → w ∈ zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ := Sylow.nonempty (G := A) (p := 3)
  have hS : Nat.card S = 3 := by rw [Sylow.card_eq_multiplicity, hA]; simp
  have hnt : ∃ z ∈ (S : Subgroup A), z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : (S : Subgroup A) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [this] at hS
    simp at hS
  obtain ⟨z, hzS, hz1⟩ := hnt
  have hord : orderOf z = 3 := by
    have h1 : orderOf z ∣ 3 := by
      have h0 : orderOf (⟨z, hzS⟩ : (S : Subgroup A)) = orderOf z := Subgroup.orderOf_mk z hzS
      have := orderOf_dvd_natCard (⟨z, hzS⟩ : (S : Subgroup A))
      rwa [h0, hS] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  refine ⟨z, hord, fun w ⟨n, hn⟩ => ?_⟩
  have hp : IsPGroup 3 (zpowers w) := by
    refine fun g => ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨n, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]
  have hwS : w ∈ (S : Subgroup A) := hp.le_sylow_of_normal S (mem_zpowers w)
  have hcard : Nat.card (zpowers z) = Nat.card (S : Subgroup A) := by
    rw [Nat.card_zpowers, hord, hS]
  have hle : zpowers z ≤ (S : Subgroup A) := (zpowers_le).2 hzS
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [heq]
  exact hwS

end ThreePart

section ClassTwo

variable {G : Type*} [Group G]

theorem pow_mul_right_of_rel {a b t : G} (hba : b * a = a * b * t) (htb : Commute t b) (m : ℕ) :
    b ^ m * a = a * b ^ m * t ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : t * b ^ m = b ^ m * t := (htb.pow_right m).eq
    calc b ^ (m + 1) * a = b * (b ^ m * a) := by rw [pow_succ', mul_assoc]
      _ = b * (a * b ^ m * t ^ m) := by rw [ih]
      _ = (b * a) * b ^ m * t ^ m := by group
      _ = a * b * t * b ^ m * t ^ m := by rw [hba]
      _ = a * b * (t * b ^ m) * t ^ m := by group
      _ = a * b * (b ^ m * t) * t ^ m := by rw [h2]
      _ = a * (b * b ^ m) * (t * t ^ m) := by group
      _ = a * b ^ (m + 1) * t ^ (m + 1) := by rw [← pow_succ', ← pow_succ']

theorem mul_pow_of_rel {a b t : G} (hba : b * a = a * b * t) (hta : Commute t a)
    (htb : Commute t b) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n * t ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc1 : t ^ n.choose 2 * a = a * t ^ n.choose 2 := (hta.pow_left _).eq
    have hc2 : (t ^ n * t ^ n.choose 2) * b = b * (t ^ n * t ^ n.choose 2) :=
      ((htb.pow_left n).mul_left (htb.pow_left _)).eq
    have hch : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    calc (a * b) ^ (n + 1) = (a * b) ^ n * (a * b) := by rw [pow_succ]
      _ = a ^ n * b ^ n * t ^ n.choose 2 * (a * b) := by rw [ih]
      _ = a ^ n * b ^ n * (t ^ n.choose 2 * a) * b := by group
      _ = a ^ n * (b ^ n * a) * t ^ n.choose 2 * b := by rw [hc1]; group
      _ = a ^ n * (a * b ^ n * t ^ n) * t ^ n.choose 2 * b := by rw [pow_mul_right_of_rel hba htb]
      _ = a ^ n * a * b ^ n * ((t ^ n * t ^ n.choose 2) * b) := by group
      _ = a ^ n * a * b ^ n * (b * (t ^ n * t ^ n.choose 2)) := by rw [hc2]
      _ = a ^ (n + 1) * b ^ (n + 1) * t ^ (n + 1).choose 2 := by
        rw [hch, pow_add, pow_succ, pow_succ]; group

theorem exists_cube_eq_one_of_class_two {a b t z : G}
    (hba : b * a = a * b * t) (hta : Commute t a) (htb : Commute t b)
    (hz3 : z ^ 3 = 1) (ht : t ∈ zpowers z)
    (ha3 : a ^ 3 ∈ zpowers z) (hb3 : b ^ 3 ∈ zpowers z) :
    a ^ 3 = 1 ∨ b ^ 3 = 1 ∨ (a * b) ^ 3 = 1 ∨ (a * b⁻¹) ^ 3 = 1 := by
  obtain ⟨γ, hγ⟩ := Subgroup.mem_zpowers_iff.1 ht
  obtain ⟨α, hα⟩ := Subgroup.mem_zpowers_iff.1 ha3
  obtain ⟨β, hβ⟩ := Subgroup.mem_zpowers_iff.1 hb3
  have hzk : ∀ k : ℤ, 3 ∣ k → z ^ k = 1 := by
    rintro k ⟨j, rfl⟩
    have h3z : z ^ (3 : ℤ) = 1 := by simpa using hz3
    rw [zpow_mul, h3z, one_zpow]
  have ht3 : t ^ 3 = 1 := by
    have e : t ^ 3 = z ^ (3 * γ) := by
      rw [← hγ, ← zpow_natCast, ← zpow_mul, mul_comm]
      norm_cast
    rw [e]
    exact hzk _ ⟨γ, rfl⟩
  have hch : Nat.choose 3 2 = 3 := by decide
  by_cases h1 : 3 ∣ α
  · left
    rw [← hα]
    exact hzk α h1
  by_cases h2 : 3 ∣ β
  · right; left
    rw [← hβ]
    exact hzk β h2
  have h3 : 3 ∣ α + β ∨ 3 ∣ α - β := by
    have e1 : α % 3 = 1 ∨ α % 3 = 2 := by omega
    have e2 : β % 3 = 1 ∨ β % 3 = 2 := by omega
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> omega
  rcases h3 with h | h
  · right; right; left
    rw [mul_pow_of_rel hba hta htb 3, hch, ht3, mul_one, ← hα, ← hβ, ← zpow_add]
    exact hzk _ h
  · right; right; right
    have hab : a * b = b * a * t⁻¹ := by rw [hba]; group
    have hba' : b⁻¹ * a = a * b⁻¹ * t⁻¹ := by
      calc b⁻¹ * a = b⁻¹ * (a * b) * b⁻¹ := by group
        _ = b⁻¹ * (b * a * t⁻¹) * b⁻¹ := by rw [hab]
        _ = a * (t⁻¹ * b⁻¹) := by group
        _ = a * b⁻¹ * t⁻¹ := by rw [htb.inv_inv.eq]; group
    rw [mul_pow_of_rel hba' hta.inv_left htb.inv_inv 3, hch]
    simp only [inv_pow, ht3, inv_one, mul_one]
    rw [← hα, ← hβ, ← zpow_sub]
    exact hzk _ h

end ClassTwo

section CenterPart

variable {Y : Type*} [Group Y]

theorem isMulCommutative_centerIn (K : Subgroup Y) : IsMulCommutative (centerIn K) :=
  ⟨⟨fun a b => Subtype.ext ((mem_centerIn_iff.1 b.2).2 a (centerIn_le a.2))⟩⟩

theorem card_centerIn (K : Subgroup Y) : Nat.card (centerIn K) = Nat.card (Subgroup.center K) :=
  (Subgroup.card_map_of_injective K.subtype_injective)

theorem exists_z_of_center_three [Finite Y] {K : Subgroup Y}
    (hZ3 : (Nat.card (Subgroup.center K)).factorization 3 = 1) :
    ∃ z ∈ centerIn K, orderOf z = 3 ∧
      ∀ w ∈ centerIn K, (∃ n : ℕ, w ^ 3 ^ n = 1) → w ∈ zpowers z := by
  let _ : CommGroup (centerIn K) :=
    { (inferInstance : Group (centerIn K)) with
      mul_comm := fun a b => (isMulCommutative_centerIn K).is_comm.comm a b }
  obtain ⟨z, hz, h⟩ := exists_unique_three_part (A := centerIn K) (by rwa [card_centerIn])
  refine ⟨z.1, z.2, by rwa [Subgroup.orderOf_coe], fun w hw ⟨n, hn⟩ => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (h ⟨w, hw⟩ ⟨n, Subtype.ext (by simpa using hn)⟩)
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem mem_center_of_coe_mem_centerIn {K : Subgroup Y} {g : K} (hg : (g : Y) ∈ centerIn K) :
    g ∈ Subgroup.center K := by
  obtain ⟨g', hg', h⟩ := hg
  have : g' = g := K.subtype_injective h
  rwa [← this]

theorem exists_elemAbelian_card_eq {K : Subgroup Y} [Finite Y] {H₀ : Subgroup Y} (hHK : H₀ ≤ K)
    (hZH : centerIn K ≤ H₀)
    (hcomm : ∀ h ∈ H₀, ∀ h' ∈ H₀, h * h' * h⁻¹ * h'⁻¹ ∈ centerIn K)
    (hcube : ∀ h ∈ H₀, h ^ 3 ∈ centerIn K) :
    ∃ A : Subgroup (K ⧸ Subgroup.center K), IsElemAbelian 3 A ∧
      Nat.card H₀ = Nat.card A * Nat.card (Subgroup.center K) := by
  let Hk : Subgroup K := H₀.subgroupOf K
  let φ : Hk →* K ⧸ Subgroup.center K := (QuotientGroup.mk' (Subgroup.center K)).comp Hk.subtype
  have hker : ∀ x : Hk, φ x = 1 ↔ (x : K) ∈ Subgroup.center K := fun x =>
    QuotientGroup.eq_one_iff _
  have hcommK : ∀ x y : Hk, ((x : K) * y * (x : K)⁻¹ * (y : K)⁻¹) ∈ Subgroup.center K := by
    intro x y
    apply mem_center_of_coe_mem_centerIn
    simpa using hcomm x.1.1 x.2 y.1.1 y.2
  have hcubeK : ∀ x : Hk, (x : K) ^ 3 ∈ Subgroup.center K := by
    intro x
    apply mem_center_of_coe_mem_centerIn
    simpa using hcube x.1.1 x.2
  refine ⟨φ.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    show (a : K ⧸ Subgroup.center K) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    have := (hker (x * y * x⁻¹ * y⁻¹)).2 (by simpa using hcommK x y)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at this
    exact mul_inv_eq_one.1 (by simpa [mul_assoc] using this)
  · obtain ⟨x, hx⟩ := ha
    rw [← hx, ← map_pow]
    exact (hker (x ^ 3)).2 (by simpa using hcubeK x)
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have h2 : Nat.card (Hk ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have h3 : Nat.card φ.ker = Nat.card (Subgroup.center K) := by
      refine Nat.card_congr
        { toFun := fun x => ⟨(x.1 : K), (hker x.1).1 x.2⟩
          invFun := fun y => ⟨⟨(y : K), ?_⟩, (hker _).2 y.2⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
      show ((y : K) : Y) ∈ H₀
      exact hZH ⟨y, y.2, rfl⟩
    have h4 : Nat.card H₀ = Nat.card Hk :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv).symm
    rw [h4, h1, h2, h3]

@[expose] def hullIn (K E : Subgroup Y) : Subgroup Y := K ⊓ (E ⊔ centralizer (K : Set Y))

theorem hull_le {K E : Subgroup Y} : hullIn K E ≤ K := inf_le_left

theorem centerIn_le_hull {K E : Subgroup Y} : centerIn K ≤ hullIn K E :=
  le_inf centerIn_le ((centerIn_le_centralizer K).trans le_sup_right)

theorem hull_sup_eq {K E : Subgroup Y} (hK : K.Normal) (hE : E ≤ K ⊔ centralizer (K : Set Y)) :
    hullIn K E ⊔ centralizer (K : Set Y) = E ⊔ centralizer (K : Set Y) := by
  have := centralizer_normal hK
  refine le_antisymm (sup_le (inf_le_right) le_sup_right) (sup_le ?_ le_sup_right)
  intro e he
  obtain ⟨k, hk, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hE he)
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hc)
  refine ⟨hk, ?_⟩
  have : k = k * c * c⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (Subgroup.inv_mem _ (Subgroup.mem_sup_right hc))

theorem card_hull_mul_card {K E : Subgroup Y} [Finite Y] (hK : K.Normal)
    (hE : E ≤ K ⊔ centralizer (K : Set Y)) :
    Nat.card (hullIn K E) * Nat.card (centralizer (K : Set Y) ⊓ E : Subgroup Y) =
      Nat.card E * Nat.card (centerIn K) := by
  have := centralizer_normal hK
  have h1 : (centralizer (K : Set Y)).relIndex (hullIn K E) =
      (centralizer (K : Set Y)).relIndex E := by
    rw [← Subgroup.relIndex_sup_right (H := hullIn K E) (K := centralizer (K : Set Y)),
      hull_sup_eq hK hE, Subgroup.relIndex_sup_right]
  have h2 := Subgroup.relIndex_mul_card (H := centralizer (K : Set Y)) (K := hullIn K E)
  have h3 := Subgroup.relIndex_mul_card (H := centralizer (K : Set Y)) (K := E)
  have h4 : centralizer (K : Set Y) ⊓ hullIn K E = centerIn K := by
    ext x
    constructor
    · rintro ⟨hxC, hxH⟩
      exact mem_centerIn_of_mem_centralizer hxH.1 hxC
    · intro hx
      exact ⟨centerIn_le_centralizer K hx, centerIn_le_hull hx⟩
  rw [h4, h1] at h2
  rw [← h2, ← h3]
  ring

theorem commute_of_mem_centralizer {K : Subgroup Y} {c x : Y} (hc : c ∈ centralizer (K : Set Y))
    (hx : x ∈ K) : Commute c x :=
  (Subgroup.mem_centralizer_iff.1 hc x hx).symm

theorem exists_mul_of_mem_hull {K E : Subgroup Y} (hK : K.Normal) {h : Y} (hh : h ∈ hullIn K E) :
    ∃ e ∈ E, ∃ c ∈ centralizer (K : Set Y), e * c = h := by
  have := centralizer_normal hK
  exact Subgroup.mem_sup_of_normal_right.1 hh.2

theorem hull_comm {K E : Subgroup Y} (hK : K.Normal) (hEc : IsMulCommutative E) {h h' : Y}
    (hh : h ∈ hullIn K E) (hh' : h' ∈ hullIn K E) : h * h' * h⁻¹ * h'⁻¹ ∈ centerIn K := by
  obtain ⟨e, he, c, hc, hec⟩ := exists_mul_of_mem_hull hK hh
  obtain ⟨e', he', c', hc', hec'⟩ := exists_mul_of_mem_hull hK hh'
  have hee : e * e' = e' * e := congrArg Subtype.val (hEc.is_comm.comm ⟨e, he⟩ ⟨e', he'⟩)
  have e1 : e = h * c⁻¹ := by rw [← hec]; group
  have e2 : e' = h' * c'⁻¹ := by rw [← hec']; group
  have k1 : Commute c⁻¹ h' := (commute_of_mem_centralizer hc hh'.1).inv_left
  have k2 : Commute c'⁻¹ h := (commute_of_mem_centralizer hc' hh.1).inv_left
  set u := c'⁻¹ * c⁻¹ * c' * c with hu
  have huC : u ∈ centralizer (K : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc')
      (Subgroup.inv_mem _ hc)) hc') hc
  have key : h * h' * (c⁻¹ * c'⁻¹) = h' * h * (c'⁻¹ * c⁻¹) := by
    have h3 : (h * c⁻¹) * (h' * c'⁻¹) = (h' * c'⁻¹) * (h * c⁻¹) := by rw [← e1, ← e2]; exact hee
    calc h * h' * (c⁻¹ * c'⁻¹) = h * (h' * c⁻¹) * c'⁻¹ := by group
      _ = h * (c⁻¹ * h') * c'⁻¹ := by rw [k1.eq]
      _ = (h * c⁻¹) * (h' * c'⁻¹) := by group
      _ = (h' * c'⁻¹) * (h * c⁻¹) := h3
      _ = h' * (c'⁻¹ * h) * c⁻¹ := by group
      _ = h' * (h * c'⁻¹) * c⁻¹ := by rw [k2.eq]
      _ = h' * h * (c'⁻¹ * c⁻¹) := by group
  have hhh : h * h' = h' * h * u := by
    have : h * h' = h' * h * (c'⁻¹ * c⁻¹) * (c⁻¹ * c'⁻¹)⁻¹ := by
      rw [← key]; group
    rw [this, hu]; group
  have hut : h * h' * h⁻¹ * h'⁻¹ = u := by
    have hu1 : Commute u h := (commute_of_mem_centralizer huC hh.1)
    have hu2 : Commute u h' := (commute_of_mem_centralizer huC hh'.1)
    calc h * h' * h⁻¹ * h'⁻¹ = h' * h * u * h⁻¹ * h'⁻¹ := by rw [hhh]
      _ = h' * (h * (u * h⁻¹)) * h'⁻¹ := by group
      _ = h' * (h * (h⁻¹ * u)) * h'⁻¹ := by rw [(hu1.inv_right).eq]
      _ = (h' * u) * h'⁻¹ := by group
      _ = u := by rw [← hu2.eq]; group
  rw [hut]
  refine mem_centerIn_of_mem_centralizer ?_ huC
  rw [← hut]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hh.1 hh'.1)
    (Subgroup.inv_mem _ hh.1)) (Subgroup.inv_mem _ hh'.1)

theorem hull_cube {K E : Subgroup Y} (hK : K.Normal) (hE3 : ∀ x ∈ E, x ^ 3 = 1) {h : Y}
    (hh : h ∈ hullIn K E) : h ^ 3 ∈ centerIn K := by
  obtain ⟨e, he, c, hc, hec⟩ := exists_mul_of_mem_hull hK hh
  have e1 : e = h * c⁻¹ := by rw [← hec]; group
  have hcomm : Commute h c⁻¹ := ((commute_of_mem_centralizer hc hh.1).inv_left).symm
  have h1 : h ^ 3 * (c ^ 3)⁻¹ = 1 := by
    have := hE3 e he
    rw [e1, hcomm.mul_pow, inv_pow] at this
    exact this
  have h2 : h ^ 3 = c ^ 3 := mul_inv_eq_one.1 h1
  refine mem_centerIn_of_mem_centralizer (Subgroup.pow_mem _ hh.1 3) ?_
  rw [h2]
  exact Subgroup.pow_mem _ hc 3

theorem mem_centerIn_of_cube_eq_one [Finite Y] (Rb : Sylow 3 Y) {K : Subgroup Y} (hK : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ centralizer (K : Set Y), orderOf c = 3 → c ∈ centerIn K)
    {x : Y} (hx : x ∈ centralizer (K : Set Y)) (h3 : x ^ 3 = 1) : x ∈ centerIn K := by
  by_cases h1 : x = 1
  · rw [h1]; exact Subgroup.one_mem _
  · exact mem_centerIn_of_orderOf_eq_three Rb hK hcent hx (orderOf_eq_prime h3 h1)

theorem hull_counts [Finite Y] (Rb : Sylow 3 Y) {K E : Subgroup Y} (hK : K.Normal)
    (hZ3 : (Nat.card (Subgroup.center K)).factorization 3 = 1)
    (hm3 : ∀ A : Subgroup (K ⧸ Subgroup.center K), IsElemAbelian 3 A → Nat.card A ≤ 9)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ centralizer (K : Set Y), orderOf c = 3 → c ∈ centerIn K)
    (hEa : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3)
    (hEKC : E ≤ K ⊔ centralizer (K : Set Y)) :
    ∃ z ∈ centerIn K, orderOf z = 3 ∧ (∀ w ∈ centerIn K, (∃ n : ℕ, w ^ 3 ^ n = 1) → w ∈ zpowers z) ∧
      centralizer (K : Set Y) ⊓ E = zpowers z ∧
      Nat.card (hullIn K E) = 9 * Nat.card (Subgroup.center K) := by
  obtain ⟨z, hzZ, hzo, hzp⟩ := exists_z_of_center_three hZ3
  have hle : centralizer (K : Set Y) ⊓ E ≤ zpowers z := fun x ⟨hxC, hxE⟩ =>
    hzp x (mem_centerIn_of_cube_eq_one Rb hK hcent hxC (hEa.2 x hxE)) ⟨1, by simpa using hEa.2 x hxE⟩
  have hcardz : Nat.card (zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
  have hn : Nat.card (centralizer (K : Set Y) ⊓ E : Subgroup Y) ≤ 3 :=
    hcardz ▸ Subgroup.card_le_of_le hle
  have hcard := card_hull_mul_card (E := E) hK hEKC
  rw [hEc, card_centerIn] at hcard
  obtain ⟨A, hA, hHA⟩ := exists_elemAbelian_card_eq (H₀ := hullIn K E) hull_le centerIn_le_hull
    (fun h hh h' hh' => hull_comm hK hEa.1 hh hh') (fun h hh => hull_cube hK hEa.2 hh)
  have hbound : Nat.card (hullIn K E) ≤ 9 * Nat.card (Subgroup.center K) := by
    rw [hHA]
    exact Nat.mul_le_mul_right _ (hm3 A hA) |>.trans_eq (by ring)
  have hZpos : 0 < Nat.card (Subgroup.center K) := Nat.card_pos
  have hnpos : 0 < Nat.card (centralizer (K : Set Y) ⊓ E : Subgroup Y) := Nat.card_pos
  have hn3 : Nat.card (centralizer (K : Set Y) ⊓ E : Subgroup Y) = 3 := by
    by_contra hne
    have hlt : Nat.card (centralizer (K : Set Y) ⊓ E : Subgroup Y) ≤ 2 := by omega
    have : Nat.card (hullIn K E) * Nat.card (centralizer (K : Set Y) ⊓ E : Subgroup Y) ≤
        (9 * Nat.card (Subgroup.center K)) * 2 :=
      Nat.mul_le_mul hbound hlt
    nlinarith
  refine ⟨z, hzZ, hzo, hzp, ?_, ?_⟩
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardz, hn3])
  · rw [hn3] at hcard
    nlinarith

theorem factorization_nine_mul {N : ℕ} (hN : N ≠ 0) (h : N.factorization 3 = 1) :
    (9 * N).factorization 3 = 3 := by
  rw [Nat.factorization_mul (by norm_num) hN]
  have : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [this, Nat.factorization_pow]
  simp [h, Nat.Prime.factorization_self Nat.prime_three]

theorem exists_sylow_P [Finite Y] {K E : Subgroup Y}
    (hZ3 : (Nat.card (Subgroup.center K)).factorization 3 = 1) {z : Y} (hzZ : z ∈ centerIn K)
    (hzo : orderOf z = 3)
    (hzp : ∀ w ∈ centerIn K, (∃ n : ℕ, w ^ 3 ^ n = 1) → w ∈ zpowers z)
    (hHcard : Nat.card (hullIn K E) = 9 * Nat.card (Subgroup.center K)) :
    ∃ P : Subgroup Y, P ≤ hullIn K E ∧ Nat.card P = 3 ^ 3 ∧ z ∈ P ∧
      P ⊓ centerIn K = zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ := Sylow.nonempty (G := hullIn K E) (p := 3)
  have hf : (Nat.card (hullIn K E)).factorization 3 = 3 := by
    rw [hHcard]
    exact factorization_nine_mul Nat.card_pos.ne' hZ3
  have hS : Nat.card S = 3 ^ 3 := by rw [Sylow.card_eq_multiplicity, hf]
  have hzH : z ∈ hullIn K E := centerIn_le_hull hzZ
  have hzc : (⟨z, hzH⟩ : hullIn K E) ∈ Subgroup.center (hullIn K E) :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext ((mem_centerIn_iff.1 hzZ).2 g (hull_le g.2))
  have hnorm : (zpowers (⟨z, hzH⟩ : hullIn K E)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hk : (⟨z, hzH⟩ ^ k : hullIn K E) ∈ Subgroup.center (hullIn K E) :=
      zpow_mem hzc k
    rw [Subgroup.mem_center_iff.1 hk g, mul_inv_cancel_right]
    exact mem_zpowers_iff.2 ⟨k, rfl⟩
  have hpg : IsPGroup 3 (zpowers (⟨z, hzH⟩ : hullIn K E)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers]
      have : orderOf (⟨z, hzH⟩ : hullIn K E) = orderOf z := Subgroup.orderOf_mk z hzH
      rw [this, hzo]; simp)
  have hzS : (⟨z, hzH⟩ : hullIn K E) ∈ (S : Subgroup (hullIn K E)) :=
    hpg.le_sylow_of_normal S (mem_zpowers _)
  have hzP : z ∈ (S : Subgroup (hullIn K E)).map (hullIn K E).subtype := ⟨⟨z, hzH⟩, hzS, rfl⟩
  refine ⟨(S : Subgroup (hullIn K E)).map (hullIn K E).subtype, ?_, ?_, hzP, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective (hullIn K E).subtype_injective]
    exact hS
  · ext w
    constructor
    · rintro ⟨⟨x, hxS, rfl⟩, hwZ⟩
      refine hzp _ hwZ ⟨3, ?_⟩
      have h27 : x ^ Nat.card S = 1 := by
        have := pow_card_eq_one' (x := (⟨x, hxS⟩ : (S : Subgroup (hullIn K E))))
        exact congrArg Subtype.val this
      rw [hS] at h27
      simpa using congrArg Subtype.val h27
    · intro hw
      exact ⟨(zpowers_le.2 hzP) hw, (zpowers_le.2 hzZ) hw⟩

theorem commute_of_cube_central {K : Subgroup Y} {z c₁ c₂ t : Y} (hz3 : z ^ 3 = 1)
    (hcent3 : ∀ x ∈ centralizer (K : Set Y), x ^ 3 = 1 → x ∈ centerIn K)
    (hc₁ : c₁ ∈ centralizer (K : Set Y)) (hc₂ : c₂ ∈ centralizer (K : Set Y))
    (htK : t ∈ centerIn K) (hrel : c₂ * c₁ = c₁ * c₂ * t) (ht : t ∈ zpowers z)
    (h1 : c₁ ^ 3 ∈ zpowers z) (h2 : c₂ ^ 3 ∈ zpowers z) : c₁ * c₂ = c₂ * c₁ := by
  have hta : Commute t c₁ := (commute_of_mem_centralizer hc₁ (centerIn_le htK)).symm
  have htb : Commute t c₂ := (commute_of_mem_centralizer hc₂ (centerIn_le htK)).symm
  have hcomm : ∀ x ∈ centerIn K, ∀ c ∈ centralizer (K : Set Y), x * c = c * x := fun x hx c hc =>
    (commute_of_mem_centralizer hc (centerIn_le hx)).symm.eq
  rcases exists_cube_eq_one_of_class_two hrel hta htb hz3 ht h1 h2 with h | h | h | h
  · have hx := hcent3 c₁ hc₁ h
    exact hcomm c₁ hx c₂ hc₂
  · have hx := hcent3 c₂ hc₂ h
    exact (hcomm c₂ hx c₁ hc₁).symm
  · have hx := hcent3 (c₁ * c₂) (Subgroup.mul_mem _ hc₁ hc₂) h
    have := hcomm _ hx c₂ hc₂
    exact mul_right_cancel (this.trans (mul_assoc c₂ c₁ c₂).symm)
  · have hx := hcent3 (c₁ * c₂⁻¹) (Subgroup.mul_mem _ hc₁ (Subgroup.inv_mem _ hc₂)) h
    have := hcomm _ hx c₂ hc₂
    have h5 : c₁ = c₂ * c₁ * c₂⁻¹ := by simpa [mul_assoc] using this
    calc c₁ * c₂ = c₂ * c₁ * c₂⁻¹ * c₂ := by rw [← h5]
      _ = c₂ * c₁ := by group

theorem sylow_P_comm {K E : Subgroup Y} (hK : K.Normal) (hEa : IsElemAbelian 3 E) {z : Y}
    (hzo : orderOf z = 3)
    (hcent3 : ∀ x ∈ centralizer (K : Set Y), x ^ 3 = 1 → x ∈ centerIn K)
    {P : Subgroup Y} (hPH : P ≤ hullIn K E) (hPZ : P ⊓ centerIn K = zpowers z) :
    IsMulCommutative P := by
  have hz3 : z ^ 3 = 1 := hzo ▸ pow_orderOf_eq_one z
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  show (a : Y) * b = b * a
  obtain ⟨e₁, he₁, c₁, hc₁, h₁⟩ := exists_mul_of_mem_hull hK (hPH a.2)
  obtain ⟨e₂, he₂, c₂, hc₂, h₂⟩ := exists_mul_of_mem_hull hK (hPH b.2)
  have hee : e₁ * e₂ = e₂ * e₁ := congrArg Subtype.val (hEa.1.is_comm.comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩)
  have ha := hull_le (hPH a.2)
  have hb := hull_le (hPH b.2)
  have k1 : c₁ * (b : Y) = b * c₁ := (commute_of_mem_centralizer hc₁ hb).eq
  have k2 : c₂ * (a : Y) = a * c₂ := (commute_of_mem_centralizer hc₂ ha).eq
  have hp12 : (a : Y) * b = e₁ * e₂ * (c₂ * c₁) := by
    calc (a : Y) * b = e₁ * (c₁ * b) := by rw [← h₁]; group
      _ = e₁ * (b * c₁) := by rw [k1]
      _ = e₁ * (e₂ * c₂) * c₁ := by rw [h₂]; group
      _ = e₁ * e₂ * (c₂ * c₁) := by group
  have hp21 : (b : Y) * a = e₂ * e₁ * (c₁ * c₂) := by
    calc (b : Y) * a = e₂ * (c₂ * a) := by rw [← h₂]; group
      _ = e₂ * (a * c₂) := by rw [k2]
      _ = e₂ * (e₁ * c₁) * c₂ := by rw [h₁]; group
      _ = e₂ * e₁ * (c₁ * c₂) := by group
  set t := (c₁ * c₂)⁻¹ * (c₂ * c₁) with ht
  have hrel : c₂ * c₁ = c₁ * c₂ * t := by rw [ht]; group
  have htC : t ∈ centralizer (K : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hc₁ hc₂))
      (Subgroup.mul_mem _ hc₂ hc₁)
  have hteq : (a : Y) * b = b * a * t := by
    rw [hp12, hp21, ht]
    calc e₁ * e₂ * (c₂ * c₁) = e₂ * e₁ * (c₁ * c₂) * ((c₁ * c₂)⁻¹ * (c₂ * c₁)) := by
          rw [hee]; group
      _ = _ := rfl
  have htP : t ∈ P := by
    have : t = ((b : Y) * a)⁻¹ * ((a : Y) * b) := by
      rw [hteq]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ b.2 a.2))
      (Subgroup.mul_mem _ a.2 b.2)
  have htK : t ∈ K := by
    have : t = ((b : Y) * a)⁻¹ * ((a : Y) * b) := by rw [hteq]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hb ha))
      (Subgroup.mul_mem _ ha hb)
  have htZ : t ∈ centerIn K := mem_centerIn_of_mem_centralizer htK htC
  have htz : t ∈ zpowers z := hPZ ▸ ⟨htP, htZ⟩
  have hcube : ∀ (p e c : Y), p ∈ P → p ∈ K → e ∈ E → c ∈ centralizer (K : Set Y) → e * c = p →
      c ^ 3 ∈ zpowers z := by
    intro p e c hpP hpK heE hcC hec
    have e1 : e = p * c⁻¹ := by rw [← hec]; group
    have hcomm : Commute p c⁻¹ := ((commute_of_mem_centralizer hcC hpK).inv_left).symm
    have h3 : e ^ 3 = 1 := hEa.2 e heE
    have h4 : p ^ 3 = c ^ 3 := by
      rw [e1, hcomm.mul_pow, inv_pow] at h3
      exact mul_inv_eq_one.1 h3
    rw [← h4]
    have hpZ : p ^ 3 ∈ centerIn K := mem_centerIn_of_mem_centralizer (Subgroup.pow_mem _ hpK 3)
      (by rw [h4]; exact Subgroup.pow_mem _ hcC 3)
    rw [← hPZ]
    exact ⟨Subgroup.pow_mem _ hpP 3, hpZ⟩
  have hcc := commute_of_cube_central hz3 hcent3 hc₁ hc₂ htZ hrel htz
    (hcube _ _ _ a.2 ha he₁ hc₁ h₁) (hcube _ _ _ b.2 hb he₂ hc₂ h₂)
  rw [hp12, hp21, hee, hcc]

theorem zpowers_normal {K : Subgroup Y} (hK : K.Normal) {z : Y} (hzZ : z ∈ centerIn K)
    (hz3 : z ^ 3 = 1)
    (hzp : ∀ w ∈ centerIn K, (∃ n : ℕ, w ^ 3 ^ n = 1) → w ∈ zpowers z) :
    (zpowers z).Normal := by
  refine ⟨fun n hn y => ?_⟩
  have hc : y * n * y⁻¹ ∈ centerIn K := (centerIn_normal hK).conj_mem n (zpowers_le.2 hzZ hn) y
  refine hzp _ hc ⟨1, ?_⟩
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hn
  have h1 : (y * z ^ j * y⁻¹) ^ 3 = y * (z ^ j) ^ 3 * y⁻¹ := by
    exact conj_pow
  rw [pow_one, h1, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  group

theorem exists_hyperplane [Finite Y] {K E : Subgroup Y} (hK : K.Normal) (hEa : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) {z : Y} (hzZ : z ∈ centerIn K) (hzo : orderOf z = 3)
    (hzp : ∀ w ∈ centerIn K, (∃ n : ℕ, w ^ 3 ^ n = 1) → w ∈ zpowers z)
    (hCE : centralizer (K : Set Y) ⊓ E = zpowers z) {x : Y} (hxH : x ∈ hullIn K E)
    (hx : x ∉ centerIn K) :
    ∃ F : Subgroup Y, F ≤ E ∧ F.relIndex E = 3 ∧
      ∀ k ∈ K, k * x = x * k → ∀ f ∈ F, f * k = k * f := by
  have hz3 : z ^ 3 = 1 := hzo ▸ pow_orderOf_eq_one z
  have hzE : z ∈ E := (hCE ▸ mem_zpowers z : z ∈ centralizer (K : Set Y) ⊓ E).2
  obtain ⟨e, he, c, hc, hec⟩ := exists_mul_of_mem_hull hK hxH
  have hxK : x ∈ K := hull_le hxH
  have hnot : e ∉ zpowers z := by
    intro hez
    have heZ : e ∈ centerIn K := zpowers_le.2 hzZ hez
    have hcK : c ∈ K := by
      have : c = e⁻¹ * x := by rw [← hec]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (centerIn_le heZ)) hxK
    have hcZ : c ∈ centerIn K := mem_centerIn_of_mem_centralizer hcK hc
    exact hx (hec ▸ Subgroup.mul_mem _ heZ hcZ)
  have he3 : e ^ 3 = 1 := hEa.2 e he
  have he1 : e ≠ 1 := fun h => hnot (h ▸ Subgroup.one_mem _)
  have heo : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hnormZ := zpowers_normal hK hzZ hz3 hzp
  have hZcard : Nat.card (zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
  have hEcard : Nat.card (zpowers e) = 3 := by rw [Nat.card_zpowers, heo]
  have hbot : zpowers z ⊓ zpowers e = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun w ⟨hwz, hwe⟩ => ?_
    by_contra hw1
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hwz
    have hw3 : (z ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
    have hwo : orderOf (z ^ j) = 3 := orderOf_eq_prime hw3 hw1
    have hcw : Nat.card (zpowers (z ^ j)) = 3 := by rw [Nat.card_zpowers, hwo]
    have h1 : zpowers (z ^ j) = zpowers e :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hwe) (by rw [hcw, hEcard])
    have h2 : zpowers (z ^ j) = zpowers z :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hwz) (by rw [hcw, hZcard])
    exact hnot (h2 ▸ h1 ▸ mem_zpowers e)
  have hF9 : Nat.card (zpowers e ⊔ zpowers z : Subgroup Y) = 9 := by
    have r1 := Subgroup.relIndex_sup_right (H := zpowers e) (K := zpowers z)
    have r2 := Subgroup.relIndex_mul_card (H := zpowers z) (K := zpowers e)
    have r3 := Subgroup.relIndex_mul_card (H := zpowers z) (K := zpowers e ⊔ zpowers z)
    rw [hbot, Subgroup.card_bot, mul_one, hEcard] at r2
    rw [inf_of_le_left le_sup_right, hZcard, r1, r2] at r3
    omega
  have hFE : zpowers e ⊔ zpowers z ≤ E := sup_le (zpowers_le.2 he) (zpowers_le.2 hzE)
  refine ⟨zpowers e ⊔ zpowers z, hFE, ?_, ?_⟩
  · have r := Subgroup.relIndex_mul_card (H := zpowers e ⊔ zpowers z) (K := E)
    rw [inf_of_le_left hFE, hF9, hEc] at r
    omega
  · intro k hk hkx f hf
    have hke : k * e = e * k := by
      have e1 : e = x * c⁻¹ := by rw [← hec]; group
      have hkc : k * c⁻¹ = c⁻¹ * k := ((commute_of_mem_centralizer hc hk).inv_left).symm.eq
      rw [e1]
      calc k * (x * c⁻¹) = (k * x) * c⁻¹ := by group
        _ = x * (k * c⁻¹) := by rw [hkx]; group
        _ = x * (c⁻¹ * k) := by rw [hkc]
        _ = x * c⁻¹ * k := by group
    have hkz : k * z = z * k := (mem_centerIn_iff.1 hzZ).2 k hk
    have hle : zpowers e ⊔ zpowers z ≤ centralizer ({k} : Set Y) := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]; exact hke
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]; exact hkz
    exact (Subgroup.mem_centralizer_iff.1 (hle hf) k (Set.mem_singleton k)).symm

theorem coverThree_reduction [Finite Y] (Rb : Sylow 3 Y) {K E : Subgroup Y}
    (hKn : K.Normal) (hZ3 : (Nat.card (Subgroup.center K)).factorization 3 = 1)
    (hm3 : ∀ A : Subgroup (K ⧸ Subgroup.center K), IsElemAbelian 3 A → Nat.card A ≤ 9)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
      c ∈ (Subgroup.center K).map K.subtype)
    (hEa : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3)
    (hEKC : E ≤ K ⊔ Subgroup.centralizer (K : Set Y)) :
    ∃ P : Subgroup K, IsMulCommutative P ∧ Nat.card P = 3 ^ 3 ∧
      Nat.card (P ⊓ Subgroup.center K : Subgroup K) = 3 ∧
      (∀ x ∈ P, x ^ 3 ∈ Subgroup.center K) ∧
      ∀ x ∈ P, x ∉ Subgroup.center K →
        ∃ F : Subgroup Y, F ≤ E ∧ F.relIndex E = 3 ∧
          ∀ k : K, k * x = x * k → ∀ f ∈ F, f * (k : Y) = (k : Y) * f := by
  have hcent' : ∀ c ∈ (Rb : Subgroup Y) ⊓ centralizer (K : Set Y), orderOf c = 3 →
      c ∈ centerIn K := hcent
  obtain ⟨z, hzZ, hzo, hzp, hCE, hHcard⟩ := hull_counts Rb hKn hZ3 hm3 hcent' hEa hEc hEKC
  have hcent3 : ∀ x ∈ centralizer (K : Set Y), x ^ 3 = 1 → x ∈ centerIn K :=
    fun x hx h3 => mem_centerIn_of_cube_eq_one Rb hKn hcent' hx h3
  obtain ⟨P, hPH, hP27, hzP, hPZ⟩ := exists_sylow_P hZ3 hzZ hzo hzp hHcard
  have hPcomm := sylow_P_comm hKn hEa hzo hcent3 hPH hPZ
  have hPK : P ≤ K := hPH.trans hull_le
  refine ⟨P.subgroupOf K, ⟨⟨fun a b => ?_⟩⟩, ?_, ?_, ?_, ?_⟩
  · refine Subtype.ext (Subtype.ext ?_)
    show (a.1.1 : Y) * b.1.1 = b.1.1 * a.1.1
    exact congrArg Subtype.val (hPcomm.is_comm.comm ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hP27]
  · have hz3 : Nat.card (zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
    rw [← hz3, ← hPZ]
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : Y), x.2.1, ⟨x.1, x.2.2, rfl⟩⟩
        invFun := fun y => ⟨⟨(y : Y), hPK y.2.1⟩, y.2.1,
          mem_center_of_coe_mem_centerIn (g := ⟨(y : Y), hPK y.2.1⟩) y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  · intro x hx
    exact mem_center_of_coe_mem_centerIn (g := x ^ 3)
      (by simpa using hull_cube hKn hEa.2 (hPH hx))
  · intro x hxP hxc
    have hxP' : (x : Y) ∈ P := hxP
    have hxZ : (x : Y) ∉ centerIn K := fun h => hxc (mem_center_of_coe_mem_centerIn h)
    obtain ⟨F, hFE, hFi, hF⟩ := exists_hyperplane hKn hEa hEc hzZ hzo hzp hCE (hPH hxP') hxZ
    refine ⟨F, hFE, hFi, fun k hk f hf => hF k k.2 ?_ f hf⟩
    exact congrArg Subtype.val hk

end CenterPart

end CFSG.HardMathSupport.Foote.Coordinator
