module

public import CFSG.GH74.Uniqueness.Section12Stmts
public import CFSG.GH74.Uniqueness.Theorem1Final

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Basic

variable {X : Type} [Group X] {Z : Set X} {M : Subgroup X}

theorem sec126_exists_mem_ne_of_two_lt_card (A : Subgroup X) (a b : X) (h : 2 < Nat.card A) :
    ∃ x ∈ A, x ≠ a ∧ x ≠ b := by
  by_contra hcon
  push Not at hcon
  have hsub : (A : Set X) ⊆ {a, b} := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (hcon x hx hxa)
  have h2 : Set.ncard (A : Set X) ≤ 2 := by
    calc Set.ncard (A : Set X) ≤ Set.ncard ({a, b} : Set X) :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ Set.ncard ({b} : Set X) + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have h3 : Nat.card A = Set.ncard (A : Set X) := Nat.card_coe_set_eq (A : Set X)
  omega

theorem sec126_involution_mul_self {u : X} (hu : orderOf u = 2) : u * u = 1 := by
  have := pow_orderOf_eq_one u
  rwa [hu, pow_two] at this

theorem sec126_orderOf_mul_eq_two_of_commute {u z : X} (hu : u * u = 1) (hz : z * z = 1)
    (hcomm : u * z = z * u) (hne : u ≠ z) : orderOf (u * z) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two]
    calc u * z * (u * z) = u * (z * u) * z := by group
      _ = u * (u * z) * z := by rw [hcomm]
      _ = (u * u) * (z * z) := by group
      _ = 1 := by rw [hu, hz, one_mul]
  · intro h1
    apply hne
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
    calc u = u * z * z⁻¹ := by group
      _ = z := by rw [h1, hzi, one_mul]

theorem sec126_orderOf_conj_inv_eq (a g : X) : orderOf (g⁻¹ * a * g) = orderOf a := by
  have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective a
  simpa [MulAut.conj_apply] using h

theorem sec126_orderOf_conj_eq_two {u : X} (hu : orderOf u = 2) (g : X) :
    orderOf (g⁻¹ * u * g) = 2 := by
  rw [sec126_orderOf_conj_inv_eq, hu]

theorem sec126_mem_zpowers_conj {a w : X} (g : X) (hw : w ∈ zpowers a) :
    g⁻¹ * w * g ∈ zpowers (g⁻¹ * a * g) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have := conj_zpow (a := g⁻¹) (b := a) (i := k)
  simpa [mul_assoc] using this

theorem sec126_isPGroup_zpowers_of_orderOf_eq_two {u : X} (hu : orderOf u = 2) :
    IsPGroup 2 (zpowers u) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, hu, pow_one]

end Basic

section Setup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.sec126_centralizer_singleton_ne_top
    (S : ZDSetup X Z M) {v : X} (hv : v ≠ 1) :
    centralizer ({v} : Set X) ≠ ⊤ := by
  intro htop
  have hsimple : IsSimpleGroup X := S.theorem1_unconditional.1
  have hvc : v ∈ center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer ({v} : Set X) := htop ▸ mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  rcases hsimple.eq_bot_or_eq_top_of_normal (center X) with hb | ht
  · exact hv (by simpa [hb] using hvc)
  · obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
    have hzc : z ∈ center X := ht ▸ mem_top z
    have hcz : centralizer ({z} : Set X) = ⊤ := by
      refine eq_top_iff.mpr fun g _ => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_center_iff.mp hzc g
    have hle := S.prodDisc.centralizer_le_of_mem hz hzM
    rw [hcz] at hle
    exact S.prodDisc.ne_top (top_le_iff.mp hle)

theorem ZDSetup.sec126_not_mem_of_mem_dGrp (S : ZDSetup X Z M) {t : X} (htM : t ∉ M) {u : X}
    (hu : u ∈ M ⊓ conjugate M t) : u ∉ Z := by
  intro huZ
  obtain ⟨β, -, huniq⟩ := S.prodDisc.existsUnique_fixed_point S.invariant huZ
  have hMω : M ∈ omega M := self_mem_omega M
  have hCω : conjugate M t ∈ omega M := ⟨t, rfl⟩
  have h1 := huniq M ⟨hMω, (S.prodDisc.conjugate_eq_iff_mem hMω).mpr (Subgroup.mem_inf.mp hu).1⟩
  have h2 := huniq (conjugate M t)
    ⟨hCω, (S.prodDisc.conjugate_eq_iff_mem hCω).mpr (Subgroup.mem_inf.mp hu).2⟩
  have h3 : conjugate M t = M := h2.trans h1.symm
  apply htM
  rw [← S.prodDisc.normalizer_eq_self]
  exact conjugate_eq_iff_mem_normalizer.mp h3

theorem ZDSetup.sec126_exists_conj_of_isConj (S : ZDSetup X Z M) {u u' : X} (huM : u ∈ M)
    (hu2 : orderOf u = 2) (hu'M : u' ∈ M) (h : IsConj u u') : ∃ m ∈ M, m⁻¹ * u * m = u' := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have hg' : g⁻¹⁻¹ * u * g⁻¹ ∈ M := by rw [inv_inv, hg]; exact hu'M
  obtain ⟨m, hm, hmu⟩ := S.exists_mem_conj_of_isPGroup huM
    (sec126_isPGroup_zpowers_of_orderOf_eq_two hu2) hg'
  exact ⟨m, hm, by rw [hmu, inv_inv, hg]⟩

end Setup

section LDataFacts

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X} {c : Ctx12 Z M} {n i : ℕ}

namespace LData

theorem sec126_zHull_comm (h : LData c n i) {x y : X} (hx : x ∈ zHull Z M) (hy : y ∈ zHull Z M) :
    x * y = y * x :=
  congrArg Subtype.val (h.m_abelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem sec126_zHull_sq (h : LData c n i) {x : X} (hx : x ∈ zHull Z M) : x * x = 1 := by
  have := h.m_abelian.2 x hx
  rwa [pow_two] at this

theorem sec126_conj_mem_zHull (h : LData c n i) {m : X} (hm : m ∈ M) {x : X} (hx : x ∈ zHull Z M) :
    m⁻¹ * x * m ∈ zHull Z M := by
  have := h.m_normal m⁻¹ (M.inv_mem hm) x hx
  simpa using this

theorem sec126_conj_mem_zHull' (h : LData c n i) {m : X} (hm : m ∈ M) {x : X} (hx : x ∈ zHull Z M) :
    m * x * m⁻¹ ∈ zHull Z M :=
  h.m_normal m hm x hx

theorem sec126_mem_Z_of_mem_zHull (h : LData c n i) {y : X} (hy : y ∈ zHull Z M) (hy1 : y ≠ 1) :
    y ∈ Z ∧ y ∈ M := by
  have : y ∈ zM Z M := by
    rw [h.zM_eq]
    exact ⟨hy, hy1⟩
  exact this

theorem sec126_exists_ne (h : LData c n i) (a b : X) : ∃ x ∈ zHull Z M, x ≠ a ∧ x ≠ b := by
  refine sec126_exists_mem_ne_of_two_lt_card _ a b ?_
  rw [h.m_card]
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.hn
  omega

theorem sec126_not_mem_zHull (S : ZDSetup X Z M) (h : LData c n i) {u : X} (hu : u ∈ c.D)
    (hu2 : orderOf u = 2) : u ∉ zHull Z M := fun h' =>
  S.sec126_not_mem_of_mem_dGrp c.htM hu (h.invol u (h.m_le h') hu2)

theorem sec126_centralizes_conj (h : LData c n i) {u m : X} (hm : m ∈ M)
    (hu : ∀ x ∈ zHull Z M, x * u = u * x) :
    ∀ x ∈ zHull Z M, x * (m⁻¹ * u * m) = (m⁻¹ * u * m) * x := by
  intro x hx
  have h1 := hu _ (h.sec126_conj_mem_zHull' hm hx)
  calc x * (m⁻¹ * u * m) = m⁻¹ * ((m * x * m⁻¹) * u) * m := by group
    _ = m⁻¹ * (u * (m * x * m⁻¹)) * m := by rw [h1]
    _ = (m⁻¹ * u * m) * x := by group

end LData

omit [Finite X] in
theorem sec126_mem_deltaSet_iff_of_le {u x : X} (ha : zHull Z M ≤ centralizer ({u} : Set X)) :
    x ∈ deltaSet Z M u ↔ ∃ y ∈ zHull Z M, x = y * u := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, (Subgroup.mem_inf.mp hy).2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_inf.mpr ⟨ha hy, hy⟩, rfl⟩

theorem Shears.sec126_all_conj (h124 : Lemma124Stmt Z M) (h : LData c n i) {u : X} (hu : u ∈ c.D)
    (hu2 : orderOf u = 2) (hsh : Shears Z M u) :
    ∀ x ∈ deltaSet Z M u, x ≠ u → IsConj u x := by
  obtain ⟨x₀, hx₀, hx₀ne, hx₀c⟩ := hsh
  intro x hx hxne
  obtain ⟨g, -, hg⟩ := (h124 c n i h u hu hu2).2.2.2.1 x₀ hx₀ x hx hx₀ne hxne
  exact hx₀c.trans (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv, hg]⟩)

theorem Shears.sec126_of_conj (h : LData c n i) {u m : X} (hm : m ∈ M)
    (hs : Shears Z M (m⁻¹ * u * m)) : Shears Z M u := by
  obtain ⟨x₁, ⟨y₁, hy₁, rfl⟩, hne, hconj⟩ := hs
  have hy₁H : y₁ ∈ zHull Z M := (Subgroup.mem_inf.mp hy₁).2
  have hy₁c : y₁ * (m⁻¹ * u * m) = (m⁻¹ * u * m) * y₁ :=
    Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.mem_inf.mp hy₁).1)
  have hcomm : (m * y₁ * m⁻¹) * u = u * (m * y₁ * m⁻¹) := by
    calc (m * y₁ * m⁻¹) * u = m * (y₁ * (m⁻¹ * u * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * u * m) * y₁) * m⁻¹ := by rw [hy₁c]
      _ = u * (m * y₁ * m⁻¹) := by group
  refine ⟨m * (y₁ * (m⁻¹ * u * m)) * m⁻¹, ⟨m * y₁ * m⁻¹, ?_, ?_⟩, ?_, ?_⟩
  · exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcomm, h.sec126_conj_mem_zHull' hm hy₁H⟩
  · group
  · intro heq
    apply hne
    calc y₁ * (m⁻¹ * u * m) = m⁻¹ * (m * (y₁ * (m⁻¹ * u * m)) * m⁻¹) * m := by group
      _ = m⁻¹ * u * m := by rw [heq]
  · obtain ⟨c', hc'⟩ := isConj_iff.mp hconj
    refine isConj_iff.mpr ⟨m * c' * m⁻¹, ?_⟩
    calc m * c' * m⁻¹ * u * (m * c' * m⁻¹)⁻¹
        = m * (c' * (m⁻¹ * u * m) * c'⁻¹) * m⁻¹ := by group
      _ = m * (y₁ * (m⁻¹ * u * m)) * m⁻¹ := by rw [hc']

end LDataFacts

end CFSG.GH74.Uniqueness
