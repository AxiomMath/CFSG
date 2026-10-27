module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Defs
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveGeneral

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Blueprint

variable {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N}

namespace Local27

theorem t_mul_t (c : Local27 N X t) : t * t = 1 := by
  rw [← sq, ← c.t_order, pow_orderOf_eq_one]

theorem t_mem_centralizer_X (c : Local27 N X t) : t ∈ centralizer (X : Set N) :=
  mem_centralizer_iff.2 fun x hx => c.t_cent x hx

theorem X_le_centralizer_t (c : Local27 N X t) : X ≤ centralizer ({t} : Set N) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  exact c.t_cent x hx

theorem t_mem_R (c : Local27 N X t) :
    t ∈ centralizer ({t} : Set N) ⊓ centralizer (X : Set N) :=
  ⟨mem_centralizer_singleton_iff.2 rfl, c.t_mem_centralizer_X⟩

theorem centralizer_t_le_normalizer (c : Local27 N X t) :
    centralizer ({t} : Set N) ≤ normalizer (X : Set N) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := c.X_normal g hg x hx
    simpa [mul_assoc] using this
  · intro hx
    have := c.X_normal g⁻¹ (Subgroup.inv_mem _ hg) (g * x * g⁻¹) hx
    simpa [mul_assoc] using this

theorem exists_equiv_alt (c : Local27 N X t) :
    Nonempty (↥X ≃* alternatingGroup (Fin 5)) :=
  CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model ↥X c.model

theorem card_eq_sixty (c : Local27 N X t) : Nat.card X = 60 := by
  obtain ⟨e⟩ := c.exists_equiv_alt
  rw [Nat.card_congr e.toEquiv]
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin 5)
  simp only [Nat.card_perm, Nat.card_fin] at h2
  have h5 : Nat.factorial 5 = 120 := by decide
  omega

theorem X_inf_centralizer_X (c : Local27 N X t) :
    X ⊓ centralizer (X : Set N) = ⊥ := by
  obtain ⟨e⟩ := c.exists_equiv_alt
  rw [eq_bot_iff]
  intro x ⟨hx, hxc⟩
  have hz : (⟨x, hx⟩ : X) ∈ center X := by
    rw [mem_center_iff]
    intro g
    have := mem_centralizer_iff.1 hxc g g.2
    exact Subtype.ext this
  have hcen : center (alternatingGroup (Fin 5)) = ⊥ := alternatingGroup.center_eq_bot (by simp)
  have : e ⟨x, hx⟩ ∈ center (alternatingGroup (Fin 5)) := by
    rw [mem_center_iff]
    intro g
    have h1 := (mem_center_iff.1 hz) (e.symm g)
    have h2 := congrArg e h1
    simpa using h2
  rw [hcen, mem_bot] at this
  have : (⟨x, hx⟩ : X) = 1 := e.injective (by simpa using this)
  simpa using congrArg Subtype.val this

theorem t_not_mem_X (c : Local27 N X t) : t ∉ X := by
  intro h
  have : t ∈ X ⊓ centralizer (X : Set N) := ⟨h, c.t_mem_centralizer_X⟩
  rw [c.X_inf_centralizer_X, mem_bot] at this
  have h1 := c.t_order
  rw [this, orderOf_one] at h1
  omega

theorem mem_zpowers_of_isPGroup (c : Local27 N X t) {g : N}
    (hg : g ∈ centralizer ({t} : Set N) ⊓ centralizer (X : Set N))
    (h2 : IsPGroup 2 (zpowers g)) : g ∈ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := c.t_mul_t
  have hzt : IsPGroup 2 (zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, c.t_order, pow_one]
  have hcomm : g * t = t * g := mem_centralizer_singleton_iff.1 hg.1
  have hnorm : zpowers g ≤ normalizer ((zpowers t : Subgroup N) : Set N) := by
    have hgc : g ∈ centralizer ((zpowers t : Subgroup N) : Set N) := by
      rw [mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
      exact ((Commute.zpow_right (show Commute g t from hcomm) k).eq).symm
    rw [zpowers_le]
    exact centralizer_le_normalizer _ hgc
  have hP : IsPGroup 2 ↥(zpowers g ⊔ zpowers t) := h2.to_sup_of_normal_right' hzt hnorm
  have hPR : zpowers g ⊔ zpowers t ≤ centralizer ({t} : Set N) ⊓ centralizer (X : Set N) :=
    sup_le (zpowers_le.2 hg) (zpowers_le.2 c.t_mem_R)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : Nat.card ↥(zpowers g ⊔ zpowers t) ∣
      Nat.card ↥(centralizer ({t} : Set N) ⊓ centralizer (X : Set N)) :=
    Subgroup.card_dvd_of_le hPR
  rw [hk] at hdvd
  have hne : Nat.card ↥(centralizer ({t} : Set N) ⊓ centralizer (X : Set N)) ≠ 0 :=
    Nat.card_pos.ne'
  have hk1 : k ≤ 1 := by
    have := (padicValNat_dvd_iff_le (p := 2) hne).1 hdvd
    rwa [c.cent_two] at this
  have hle : zpowers t ≤ zpowers g ⊔ zpowers t := le_sup_right
  have hcard : Nat.card ↥(zpowers g ⊔ zpowers t) ≤ Nat.card ↥(zpowers t) := by
    rw [hk, Nat.card_zpowers, c.t_order]
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 2 := by norm_num
  have heq : zpowers t = zpowers g ⊔ zpowers t :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  exact mem_sup_left (mem_zpowers g)

private def conjAct (K D : Subgroup N) (h : ∀ g ∈ D, ∀ x ∈ K, g * x * g⁻¹ ∈ K) :
    ↥D →* MulAut ↥K where
  toFun g :=
    { toFun := fun x => ⟨(g : N) * x * (g : N)⁻¹, h g g.2 x x.2⟩
      invFun := fun x => ⟨(g : N)⁻¹ * x * (g : N), by
        simpa using h (g : N)⁻¹ (D.inv_mem g.2) x x.2⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun x => by ext; simp [mul_assoc]
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun g h' => by ext; simp [mul_assoc]

theorem card_mulAut_X (c : Local27 N X t) :
    Nat.card (MulAut ↥X) = 120 := by
  obtain ⟨e⟩ := c.exists_equiv_alt
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)
  rw [Nat.card_congr (MulAut.congr e).toEquiv,
    ← Nat.card_congr (Equiv.ofBijective _ hb), Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [Nat.factorial]

theorem card_D_dvd (c : Local27 N X t) :
    120 ∣ Nat.card ↥(centralizer ({t} : Set N)) := by
  have htt := c.t_mul_t
  have hcomm : ∀ a ∈ X, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact ((Commute.zpow_right (c.t_cent a ha) k).eq)
  have hdisj : X ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy, hyt⟩
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self htt hyt with rfl | rfl
    · exact one_mem _
    · exact absurd hy c.t_not_mem_X
  have hcard := CFSG.OddStandard.card_sup_of_commute hcomm hdisj
  rw [c.card_eq_sixty, Nat.card_zpowers, c.t_order] at hcard
  have hle : X ⊔ zpowers t ≤ centralizer ({t} : Set N) :=
    sup_le c.X_le_centralizer_t (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have := Subgroup.card_dvd_of_le hle
  rw [hcard] at this
  simpa using this

theorem padicValNat_D_le (c : Local27 N X t) :
    padicValNat 2 (Nat.card ↥(centralizer ({t} : Set N))) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := centralizer ({t} : Set N) with hD
  set R := centralizer ({t} : Set N) ⊓ centralizer (X : Set N) with hR
  let φ : ↥D →* MulAut ↥X := conjAct X D c.X_normal
  have hker : φ.ker = R.subgroupOf D := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      refine ⟨g.2, mem_centralizer_iff.2 fun x hx => ?_⟩
      have := congrArg (fun a : MulAut ↥X => ((a ⟨x, hx⟩ : X) : N)) h
      simp only [MulAut.one_apply] at this
      change (g : N) * x * (g : N)⁻¹ = x at this
      calc x * (g : N) = ((g : N) * x * (g : N)⁻¹) * g := by rw [this]
        _ = g * x := by group
    · rintro ⟨-, hg⟩
      ext x
      change (g : N) * x * (g : N)⁻¹ = x
      have := mem_centralizer_iff.1 hg x x.2
      calc (g : N) * x * (g : N)⁻¹ = x * g * (g : N)⁻¹ := by rw [← this]
        _ = x := by group
  have hcard := card_eq_card_range_mul_card_ker φ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : R ≤ D)).toEquiv] at hcard
  have hrange : Nat.card φ.range ∣ 120 := by
    rw [← c.card_mulAut_X]
    exact Subgroup.card_subgroup_dvd_card _
  have hr0 : Nat.card φ.range ≠ 0 := Nat.card_pos.ne'
  have hR0 : Nat.card R ≠ 0 := Nat.card_pos.ne'
  have h1 : padicValNat 2 (Nat.card φ.range) ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have h2 : 2 ^ 4 ∣ Nat.card φ.range := (padicValNat_dvd_iff_le (p := 2) hr0).2 (by omega)
    have h3 : 2 ^ 4 ∣ 120 := h2.trans hrange
    omega
  have hD' : Nat.card ↥D = Nat.card φ.range * Nat.card R := by
    rw [hcard]
  rw [hD', padicValNat.mul hr0 hR0, c.cent_two]
  omega

end Local27

omit [Finite N] in
theorem isPGroup_zpowers_mul_of_commute {a b : N} (hab : a * b = b * a)
    (ha : IsPGroup 2 (zpowers a)) (hb : IsPGroup 2 (zpowers b)) :
    IsPGroup 2 (zpowers (a * b)) := by
  have hnorm : zpowers a ≤ normalizer ((zpowers b : Subgroup N) : Set N) := by
    have hac : a ∈ centralizer ((zpowers b : Subgroup N) : Set N) := by
      rw [mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
      exact ((Commute.zpow_right (show Commute a b from hab) k).eq).symm
    rw [zpowers_le]
    exact centralizer_le_normalizer _ hac
  have hP : IsPGroup 2 ↥(zpowers a ⊔ zpowers b) := ha.to_sup_of_normal_right' hb hnorm
  have hle : zpowers (a * b) ≤ zpowers a ⊔ zpowers b :=
    zpowers_le.2 (Subgroup.mul_mem _ (mem_sup_left (mem_zpowers a)) (mem_sup_right (mem_zpowers b)))
  exact hP.to_le hle

omit [Finite N] in
theorem isPGroup_zpowers_of_mul_self {v : N} (h : v * v = 1) : IsPGroup 2 (zpowers v) := by
  have h2 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h1
  · refine IsPGroup.of_card (n := 0) ?_
    rw [Nat.card_zpowers, h1, pow_zero]
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, h1, pow_one]


end CFSG.OddStandard.Seitz77
