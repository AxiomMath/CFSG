module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.AGLEmbedding.KFactProofs.J3Cover

open scoped commutatorElement

section Lift

variable {X J : Type*} [Group X] [Group J]

theorem exists_lift_pow_three {π : X →* J} (hker : π.ker ≤ Subgroup.center X) {y w : X}
    (hy : y ^ 3 ∈ π.ker) (hw : π (w * y * w⁻¹) = (π y)⁻¹) :
    ∃ c ∈ π.ker, (y * c) ^ 3 = 1 := by
  have hcomm : ∀ a ∈ π.ker, ∀ b : X, Commute a b := fun a ha b =>
    (Subgroup.mem_center_iff.1 (hker ha) b).symm
  have hζ : w * y * w⁻¹ * y ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, hw, inv_mul_cancel]
  have h1 : w * y * w⁻¹ = (w * y * w⁻¹ * y) * y⁻¹ := by group
  have h2 : w * y ^ 3 * w⁻¹ = (w * y * w⁻¹ * y) ^ 3 * (y ^ 3)⁻¹ :=
    calc w * y ^ 3 * w⁻¹ = (w * y * w⁻¹) ^ 3 := conj_pow.symm
      _ = ((w * y * w⁻¹ * y) * y⁻¹) ^ 3 := by rw [← h1]
      _ = (w * y * w⁻¹ * y) ^ 3 * (y⁻¹) ^ 3 := (hcomm _ hζ y⁻¹).mul_pow 3
      _ = _ := by rw [inv_pow]
  have h3 : w * y ^ 3 * w⁻¹ = y ^ 3 := by
    rw [← (hcomm _ hy w).eq, mul_inv_cancel_right]
  have h4 : y ^ 3 * y ^ 3 = (w * y * w⁻¹ * y) ^ 3 := by
    rw [h3] at h2
    exact eq_mul_inv_iff_mul_eq.1 h2
  have hc : (y ^ 3)⁻¹ * (w * y * w⁻¹ * y) ∈ π.ker := mul_mem (inv_mem hy) hζ
  refine ⟨_, hc, ?_⟩
  rw [(hcomm _ hc y).symm.mul_pow,
    (hcomm _ (inv_mem hy) _).mul_pow, ← h4]
  group

end Lift

section Perfect

variable {J : Type*} [Group J]

theorem commutator_eq_top_of_relators {d₁ d₂ : J} (h1 : d₁ ^ 2 = 1) (h2 : d₂ ^ 4 = 1)
    (h3 : (d₁ * d₂) ^ 5 = 1) (h4 : (d₁ * d₂ ^ 2) ^ 5 = 1) :
    commutator (Subgroup.closure ({d₁, d₂} : Set J)) = ⊤ := by
  set D := Subgroup.closure ({d₁, d₂} : Set J) with hD
  let a : D := ⟨d₁, Subgroup.subset_closure (by simp)⟩
  let b : D := ⟨d₂, Subgroup.subset_closure (by simp)⟩
  have ha2 : a ^ 2 = 1 := Subtype.ext (by simpa [a] using h1)
  have hb4 : b ^ 4 = 1 := Subtype.ext (by simpa [b] using h2)
  have hab5 : (a * b) ^ 5 = 1 := Subtype.ext (by simpa [a, b] using h3)
  have hab25 : (a * b ^ 2) ^ 5 = 1 := Subtype.ext (by simpa [a, b] using h4)
  let φ : D →* Abelianization D := Abelianization.of
  have e2 : φ a ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
  have e4 : φ b ^ 4 = 1 := by rw [← map_pow, hb4, map_one]
  have e5 : φ a ^ 5 * φ b ^ 5 = 1 := by
    rw [← mul_pow, ← map_mul, ← map_pow, hab5, map_one]
  have e5' : φ a ^ 5 * (φ b ^ 2) ^ 5 = 1 := by
    rw [← mul_pow, ← map_pow, ← map_mul, ← map_pow, hab25, map_one]
  have hb5 : φ b ^ 5 = 1 :=
    calc φ b ^ 5 = (φ a ^ 5 * φ b ^ 5) * φ b ^ 5 := by rw [e5, one_mul]
      _ = φ a ^ 5 * (φ b ^ 2) ^ 5 := by rw [mul_assoc, ← pow_add, ← pow_mul]
      _ = 1 := e5'
  have hb : φ b = 1 :=
    calc φ b = φ b * φ b ^ 4 := by rw [e4, mul_one]
      _ = φ b ^ 5 := (pow_succ' _ 4).symm
      _ = 1 := hb5
  have ha5 : φ a ^ 5 = 1 := by rw [hb, one_pow, mul_one] at e5; exact e5
  have ha : φ a = 1 :=
    calc φ a = φ a * (φ a ^ 2) ^ 2 := by rw [e2]; simp
      _ = φ a ^ 5 := by rw [← pow_mul, ← pow_succ']
      _ = 1 := ha5
  have hφ : φ = 1 := by
    refine MonoidHom.eq_of_eqOn_dense (Subgroup.closure_closure_coe_preimage (k := {d₁, d₂}))
      fun g hg => ?_
    rcases hg with hg | hg
    · have : g = a := Subtype.ext hg
      rw [this, ha]; rfl
    · have : g = b := Subtype.ext hg
      rw [this, hb]; rfl
  rw [eq_top_iff]
  intro g _
  rw [← Abelianization.ker_of, MonoidHom.mem_ker, show Abelianization.of g = φ g from rfl, hφ]
  rfl

theorem commutator_self_eq {d₁ d₂ : J} (h1 : d₁ ^ 2 = 1) (h2 : d₂ ^ 4 = 1)
    (h3 : (d₁ * d₂) ^ 5 = 1) (h4 : (d₁ * d₂ ^ 2) ^ 5 = 1) :
    ⁅Subgroup.closure ({d₁, d₂} : Set J), Subgroup.closure ({d₁, d₂} : Set J)⁆ =
      Subgroup.closure ({d₁, d₂} : Set J) := by
  rw [← Subgroup.map_subtype_commutator, commutator_eq_top_of_relators h1 h2 h3 h4,
    Subgroup.map_top, Subgroup.range_subtype]

theorem not_isSolvable_of_perfect {D K : Subgroup J} (hD : ⁅D, D⁆ = D) (hne : ∃ u ∈ D, u ≠ 1)
    (hDK : D ≤ K) : ¬ Group.IsSolvable K := by
  intro hK
  have hsolv : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hDK)
  have hperf : commutator D = ⊤ := by
    have : (commutator D).map D.subtype = D := by rw [Subgroup.map_subtype_commutator, hD]
    rw [eq_top_iff]
    intro g _
    have hg : (g : J) ∈ (commutator D).map D.subtype := by rw [this]; exact g.2
    obtain ⟨c, hc, hcg⟩ := hg
    have : c = g := Subtype.ext hcg
    exact this ▸ hc
  obtain ⟨u, huD, hu1⟩ := hne
  have : Nontrivial D := ⟨⟨⟨u, huD⟩, 1, fun h => hu1 (congrArg Subtype.val h)⟩⟩
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial D).ne hperf

end Perfect

section Nine

variable {G : Type*} [Group G]

theorem exists_nine {a b : G} (hab : Commute a b) (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hdisj : Disjoint (Subgroup.zpowers a) (Subgroup.zpowers b)) :
    ∃ U : Subgroup G, IsMulCommutative U ∧ (∀ x ∈ U, x ^ 3 = 1) ∧ Nat.card U = 9 ∧ a ∈ U ∧
      b ∈ U ∧ ∀ x ∈ U, ∃ i j : ℤ, x = a ^ i * b ^ j := by
  have ha3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := hb ▸ pow_orderOf_eq_one b
  have hcomm : ∀ (m : Subgroup.zpowers a) (n : Subgroup.zpowers b),
      Commute ((Subgroup.zpowers a).subtype m) ((Subgroup.zpowers b).subtype n) := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    exact hab.zpow_zpow i j
  let φ := MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype (Subgroup.zpowers b).subtype hcomm
  have hinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨Subtype.val_injective, Subtype.val_injective, by
      simpa [Subgroup.range_subtype] using hdisj⟩
  have hdesc : ∀ x ∈ φ.range, ∃ i j : ℤ, x = a ^ i * b ^ j := by
    rintro _ ⟨⟨⟨_, i, rfl⟩, ⟨_, j, rfl⟩⟩, rfl⟩
    exact ⟨i, j, by simp [φ]⟩
  have hc : ∀ i j k l : ℤ, Commute (a ^ i * b ^ j) (a ^ k * b ^ l) := fun i j k l =>
    Commute.mul_left (Commute.mul_right ((Commute.refl a).zpow_zpow i k) (hab.zpow_zpow i l))
      (Commute.mul_right (hab.symm.zpow_zpow j k) ((Commute.refl b).zpow_zpow j l))
  have hpow : ∀ (c : G) (i : ℤ), c ^ 3 = 1 → (c ^ i) ^ 3 = 1 := fun c i h => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]
  refine ⟨φ.range, ⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_, ?_, ?_, ?_, hdesc⟩
  · obtain ⟨i, j, hx⟩ := hdesc x.1 x.2
    obtain ⟨k, l, hy⟩ := hdesc y.1 y.2
    apply Subtype.ext
    change (x : G) * y = y * x
    rw [hx, hy]
    exact (hc i j k l).eq
  · obtain ⟨i, j, rfl⟩ := hdesc x hx
    rw [(hab.zpow_zpow i j).mul_pow, hpow a i ha3, hpow b j hb3, one_mul]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, ha, hb]
  · exact ⟨(⟨a, Subgroup.mem_zpowers a⟩, 1), by simp [φ]⟩
  · exact ⟨(1, ⟨b, Subgroup.mem_zpowers b⟩), by simp [φ]⟩

end Nine

structure CoverData {J : Type*} [Group J] (x d₁ d₂ g u : J) : Prop where
  x_cube : x ^ 3 = 1
  x_ne : x ≠ 1
  comm₁ : d₁ * x = x * d₁
  comm₂ : d₂ * x = x * d₂
  inv_x : g * x * g⁻¹ = x⁻¹
  rel₁ : d₁ ^ 2 = 1
  rel₂ : d₂ ^ 4 = 1
  rel₃ : (d₁ * d₂) ^ 5 = 1
  rel₄ : (d₁ * d₂ ^ 2) ^ 5 = 1
  u_mem : u ∈ Subgroup.closure ({d₁, d₂} : Set J)
  u_cube : u ^ 3 = 1
  u_ne_one : u ≠ 1
  u_ne_x : u ≠ x
  u_ne_x_sq : u ≠ x ^ 2
  inv_u : d₁ * u * d₁⁻¹ = u⁻¹

section Cover

variable {X J : Type*} [Group X] [Group J]

theorem zpow_eq_cases {x : J} (hx : x ^ 3 = 1) (j : ℤ) :
    x ^ j = 1 ∨ x ^ j = x ∨ x ^ j = x ^ 2 := by
  have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx
  have hj : x ^ j = x ^ (j % 3) :=
    calc x ^ j = x ^ (j % 3 + 3 * (j / 3)) := by rw [Int.emod_add_mul_ediv]
      _ = x ^ (j % 3) := by rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
  have hr : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hr with h | h | h
  · left; rw [hj, h, zpow_zero]
  · right; left; rw [hj, h, zpow_one]
  · right; right; rw [hj, h]; exact_mod_cast rfl

theorem commute_of_mem_ker {π : X →* J} (hker : π.ker ≤ Subgroup.center X) {c : X}
    (hc : c ∈ π.ker) (b : X) : Commute c b :=
  (Subgroup.mem_center_iff.1 (hker hc) b).symm

theorem exists_cover_subgroups (π : X →* J) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) {x d₁ d₂ g u : J} (hd : CoverData x d₁ d₂ g u) {z : X}
    (hz : z ∈ π.ker) (hzo : orderOf z = 3) :
    ∃ U B : Subgroup X, IsMulCommutative U ∧ (∀ a ∈ U, a ^ 3 = 1) ∧ Nat.card U = 9 ∧ z ∈ U ∧
      B ≤ Subgroup.centralizer (U : Set X) ∧ (∃ t ∈ B, orderOf t = 3 ∧ t ∉ U) ∧
      Subgroup.closure ({d₁, d₂} : Set J) ≤ B.map π := by
  have hxo : orderOf x = 3 := orderOf_eq_prime hd.x_cube hd.x_ne
  obtain ⟨xt, hxt⟩ := hπ x
  obtain ⟨wt, hwt⟩ := hπ g
  have hxt3 : xt ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hxt, hd.x_cube]
  have hw : π (wt * xt * wt⁻¹) = (π xt)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hwt, hxt, hd.inv_x]
  obtain ⟨c, hc, hc3⟩ := exists_lift_pow_three hker hxt3 hw
  have hut : π (xt * c) = x := by rw [map_mul, hxt, MonoidHom.mem_ker.1 hc, mul_one]
  generalize xt * c = ut at hut hc3
  have hut1 : ut ≠ 1 := fun h => hd.x_ne (by rw [← hut, h, map_one])
  have huto : orderOf ut = 3 := orderOf_eq_prime hc3 hut1
  have hdisj : Disjoint (Subgroup.zpowers z) (Subgroup.zpowers ut) := by
    rw [Subgroup.disjoint_def]
    intro y hyz hyu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyz
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hyu
    have hxj : x ^ j = 1 := by
      have := congrArg π hj
      rwa [map_zpow, map_zpow, hut, MonoidHom.mem_ker.1 hz, one_zpow] at this
    have h3 : (3 : ℤ) ∣ j := by
      have := orderOf_dvd_iff_zpow_eq_one.2 hxj
      rw [hxo] at this
      exact_mod_cast this
    obtain ⟨m, rfl⟩ := h3
    rw [← hj, zpow_mul]
    have : ut ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
    rw [this, one_zpow]
  obtain ⟨U, hUc, hU3, hUcard, hzU, hutU, hUdesc⟩ :=
    exists_nine (commute_of_mem_ker hker hz ut) hzo huto hdisj
  set D := Subgroup.closure ({d₁, d₂} : Set J) with hD
  have hDperf : ⁅D, D⁆ = D := commutator_self_eq hd.rel₁ hd.rel₂ hd.rel₃ hd.rel₄
  set Dt := D.comap π with hDt
  have hDtmap : Dt.map π = D := Subgroup.map_comap_eq_self_of_surjective hπ D
  have hDx : D ≤ Subgroup.centralizer ({x} : Set J) := by
    rw [hD, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hd.comm₁
    · exact Subgroup.mem_centralizer_singleton_iff.2 hd.comm₂
  have hDzx : D ≤ Subgroup.centralizer (Subgroup.zpowers x : Set J) := by
    intro d hd'
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have : Commute x d := (Subgroup.mem_centralizer_singleton_iff.1 (hDx hd')).symm
    exact (this.zpow_left k).eq
  have hcomm_ker : ⁅Dt, Subgroup.zpowers ut⁆ ≤ π.ker := by
    rw [← Subgroup.map_eq_bot_iff, Subgroup.map_commutator, hDtmap, MonoidHom.map_zpowers, hut,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hDzx
  set B₀ := ⁅Dt, Dt⁆ with hB₀
  have hB₀ut : B₀ ≤ Subgroup.centralizer (Subgroup.zpowers ut : Set X) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    have h1 : ⁅⁅Dt, Subgroup.zpowers ut⁆, Dt⁆ = ⊥ :=
      le_bot_iff.1 ((Subgroup.commutator_mono (hcomm_ker.trans hker) le_rfl).trans_eq
        (Subgroup.commutator_center_left Dt))
    refine Subgroup.commutator_commutator_eq_bot_of_rotate h1 ?_
    rw [Subgroup.commutator_comm (Subgroup.zpowers ut) Dt]
    exact h1
  have hB₀U : B₀ ≤ Subgroup.centralizer (U : Set X) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨i, j, rfl⟩ := hUdesc y hy
    have h1 : Commute ut b :=
      Subgroup.mem_centralizer_iff.1 (hB₀ut hb) ut (Subgroup.mem_zpowers ut)
    exact Commute.mul_left (((commute_of_mem_ker hker hz b).zpow_left i))
      (h1.zpow_left j)
  have hB₀map : B₀.map π = D := by
    rw [hB₀, Subgroup.map_commutator, hDtmap, hDperf]
  have hB₀B : B₀ ≤ Dt ⊓ Subgroup.centralizer (U : Set X) :=
    le_inf (Subgroup.commutator_le_self Dt) hB₀U
  obtain ⟨p, hpB₀, hpu⟩ := Subgroup.mem_map.1 (hB₀map ▸ hd.u_mem : u ∈ B₀.map π)
  have hp3 : p ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hpu, hd.u_cube]
  obtain ⟨w₁, hw₁⟩ := hπ d₁
  have hw' : π (w₁ * p * w₁⁻¹) = (π p)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hw₁, hpu, hd.inv_u]
  obtain ⟨c', hc', hpc'⟩ := exists_lift_pow_three hker hp3 hw'
  have hπt : π (p * c') = u := by rw [map_mul, hpu, MonoidHom.mem_ker.1 hc', mul_one]
  have htB : p * c' ∈ Dt ⊓ Subgroup.centralizer (U : Set X) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.2 (by rw [hπt]; exact hd.u_mem),
      mul_mem (hB₀U hpB₀) (Subgroup.center_le_centralizer _ (hker hc'))⟩
  have ht1 : p * c' ≠ 1 := fun h => hd.u_ne_one (by rw [← hπt, h, map_one])
  have htU : p * c' ∉ U := by
    intro htU
    obtain ⟨i, j, hij⟩ := hUdesc _ htU
    have := congrArg π hij
    rw [hπt, map_mul, map_zpow, map_zpow, hut, MonoidHom.mem_ker.1 hz, one_zpow, one_mul] at this
    rcases zpow_eq_cases hd.x_cube j with h | h | h
    · exact hd.u_ne_one (this.trans h)
    · exact hd.u_ne_x (this.trans h)
    · exact hd.u_ne_x_sq (this.trans h)
  exact ⟨U, Dt ⊓ Subgroup.centralizer (U : Set X), hUc, hU3, hUcard, hzU, inf_le_right,
    ⟨p * c', htB, orderOf_eq_prime hpc' ht1, htU⟩,
    hB₀map ▸ Subgroup.map_mono hB₀B⟩

theorem eq_top_of_map_eq_top {π : X →* J} (hker : π.ker ≤ Subgroup.center X)
    (hperf : commutator X = ⊤) {Y : Subgroup X} (h : Y.map π = ⊤) : Y = ⊤ := by
  have hconj : ∀ c ∈ Subgroup.center X, ∀ g : X, c * g * c⁻¹ = g := fun c hc g => by
    rw [(Subgroup.mem_center_iff.1 hc g).symm, mul_inv_cancel_right]
  have hsplit : ∀ a : X, ∃ y ∈ Y, y⁻¹ * a ∈ π.ker := fun a => by
    obtain ⟨y, hy, e⟩ := Subgroup.mem_map.1 (h ▸ Subgroup.mem_top (π a))
    exact ⟨y, hy, by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]⟩
  have hle : commutator X ≤ Y := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨y₁, hy₁, hc₁⟩ := hsplit a
    obtain ⟨y₂, hy₂, hc₂⟩ := hsplit b
    have ea : a = y₁ * (y₁⁻¹ * a) := by group
    have eb : b = y₂ * (y₂⁻¹ * b) := by group
    generalize y₁⁻¹ * a = c₁ at ea hc₁
    generalize y₂⁻¹ * b = c₂ at eb hc₂
    have e : ⁅a, b⁆ = ⁅y₁, y₂⁆ := by
      rw [ea, eb]
      calc ⁅y₁ * c₁, y₂ * c₂⁆ = y₁ * (c₁ * (y₂ * c₂) * c₁⁻¹) * y₁⁻¹ * (c₂⁻¹ * y₂⁻¹) := by
            simp only [commutatorElement_def]; group
        _ = y₁ * (y₂ * c₂) * y₁⁻¹ * (c₂⁻¹ * y₂⁻¹) := by rw [hconj c₁ (hker hc₁)]
        _ = y₁ * y₂ * (c₂ * y₁⁻¹ * c₂⁻¹) * y₂⁻¹ := by group
        _ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by rw [hconj c₂ (hker hc₂)]
        _ = ⁅y₁, y₂⁆ := by simp only [commutatorElement_def]
    rw [e]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy₁ hy₂) (Y.inv_mem hy₁)) (Y.inv_mem hy₂)
  exact top_le_iff.1 (hperf ▸ hle)

end Cover

end CFSG.AGLEmbedding.KFactProofs.J3Cover
