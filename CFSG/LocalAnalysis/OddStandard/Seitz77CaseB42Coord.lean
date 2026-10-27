module

public import CFSG.LocalAnalysis.OddStandard.Seitz77UElem
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseGen
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB41Mod
public import CFSG.LocalAnalysis.OddStandard.Seitz77U

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped commutatorElement

theorem charP_two_of_card_four_B42 {F : Type} [Field F] (hF : Nat.card F = 4) : CharP F 2 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)

section Radicals

variable {G : Type} [Group G]

theorem map_radical_eq {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4) {V X : Subgroup G}
    (φ : ↥V ≃* ↥(unipAll k)) (hX : X ≤ V) (hXe : IsElemAbelian 2 X) (hXc : Nat.card X = 16) :
    (X.subgroupOf V).map φ.toMonoidHom = radOne k ∨
      (X.subgroupOf V).map φ.toMonoidHom = radTwo k := by
  have := charP_two_of_card_four_B42 hk
  refine eq_radOne_or_radTwo_of_card (fun g hg => ?_) ?_
  · obtain ⟨y, hy, rfl⟩ := hg
    have h2 := mul_self_of_isElemAbelian_two hXe (mem_subgroupOf.mp hy)
    show φ y * φ y = 1
    rw [← map_mul]
    have : y * y = 1 := Subtype.ext h2
    rw [this, map_one]
  · rw [Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv, hXc, hk]
    norm_num

theorem map_graphAut_radTwo {k : Type} [Field k] [CharP k 2] :
    (radTwo k).map (graphAut : MulAut (unipAll k)).toMonoidHom = radOne k := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (graphAut_mem_radOne_iff x).2 hx
  · intro hg
    exact ⟨graphAut g, (graphAut_mem_radTwo_iff g).2 hg, graphAut_graphAut g⟩

theorem exists_equiv_radicals {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4)
    {V R R' : Subgroup G} (φ : ↥V ≃* ↥(unipAll k)) (hR : R ≤ V) (hR' : R' ≤ V)
    (hRe : IsElemAbelian 2 R) (hRe' : IsElemAbelian 2 R') (hRc : Nat.card R = 16)
    (hRc' : Nat.card R' = 16) (hne : R ≠ R') :
    ∃ φ' : ↥V ≃* ↥(unipAll k), (R.subgroupOf V).map φ'.toMonoidHom = radOne k ∧
      (R'.subgroupOf V).map φ'.toMonoidHom = radTwo k := by
  have := charP_two_of_card_four_B42 hk
  have hdiff : (R.subgroupOf V).map φ.toMonoidHom ≠ (R'.subgroupOf V).map φ.toMonoidHom := by
    intro h
    apply hne
    have h1 := Subgroup.map_injective φ.injective h
    ext x
    constructor
    · intro hx
      have : (⟨x, hR hx⟩ : ↥V) ∈ R'.subgroupOf V := h1 ▸ mem_subgroupOf.mpr hx
      exact mem_subgroupOf.mp this
    · intro hx
      have : (⟨x, hR' hx⟩ : ↥V) ∈ R.subgroupOf V := h1.symm ▸ mem_subgroupOf.mpr hx
      exact mem_subgroupOf.mp this
  have hcomp : ∀ X : Subgroup ↥V,
      X.map (φ.trans (graphAut : MulAut (unipAll k))).toMonoidHom =
        (X.map φ.toMonoidHom).map (graphAut : MulAut (unipAll k)).toMonoidHom :=
    fun X => by rw [Subgroup.map_map]; rfl
  rcases map_radical_eq hk φ hR hRe hRc with h1 | h1
  · rcases map_radical_eq hk φ hR' hRe' hRc' with h2 | h2
    · exact absurd (h1.trans h2.symm) hdiff
    · exact ⟨φ, h1, h2⟩
  · rcases map_radical_eq hk φ hR' hRe' hRc' with h2 | h2
    · refine ⟨φ.trans (graphAut : MulAut (unipAll k)), ?_, ?_⟩
      · rw [hcomp, h1, map_graphAut_radTwo]
      · rw [hcomp, h2, map_graphAut_radOne]
    · exact absurd (h1.trans h2.symm) hdiff

end Radicals

section RadIn

variable {G : Type} [Group G] {k : Type} [Field k]

@[expose] def radIn (A₁ : Subgroup G) (e : ↥A₁ ≃* ↥(unipAll k)) (E₀ : Subgroup ↥(unipAll k)) :
    Subgroup G :=
  E₀.map (A₁.subtype.comp e.symm.toMonoidHom)

variable {A₁ : Subgroup G} {e : ↥A₁ ≃* ↥(unipAll k)} {E₀ : Subgroup ↥(unipAll k)}

theorem mem_radIn {x : G} : x ∈ radIn A₁ e E₀ ↔ ∃ a : ↥A₁, e a ∈ E₀ ∧ (a : G) = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨e.symm y, by simpa using hy, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨e a, ha, by simp⟩

theorem radIn_le : radIn A₁ e E₀ ≤ A₁ := by
  rintro x hx
  obtain ⟨a, -, rfl⟩ := mem_radIn.mp hx
  exact a.2

theorem card_radIn : Nat.card ↥(radIn A₁ e E₀) = Nat.card ↥E₀ :=
  Subgroup.card_map_of_injective (A₁.subtype_injective.comp e.symm.injective)

theorem mem_radIn_of_mem {a : G} (ha : a ∈ A₁) (h : e ⟨a, ha⟩ ∈ E₀) : a ∈ radIn A₁ e E₀ :=
  mem_radIn.mpr ⟨⟨a, ha⟩, h, rfl⟩

theorem radIn_mul_self (h : ∀ g ∈ E₀, g * g = 1) {x : G} (hx : x ∈ radIn A₁ e E₀) :
    x * x = 1 := by
  obtain ⟨a, ha, rfl⟩ := mem_radIn.mp hx
  have : a * a = 1 := e.injective (by rw [map_mul, h _ ha, map_one])
  exact congrArg Subtype.val this

theorem radIn_comm (h : ∀ g ∈ E₀, ∀ g' ∈ E₀, g * g' = g' * g) {x y : G}
    (hx : x ∈ radIn A₁ e E₀) (hy : y ∈ radIn A₁ e E₀) : x * y = y * x := by
  obtain ⟨a, ha, rfl⟩ := mem_radIn.mp hx
  obtain ⟨b, hb, rfl⟩ := mem_radIn.mp hy
  have : a * b = b * a := e.injective (by rw [map_mul, map_mul, h _ ha _ hb])
  exact congrArg Subtype.val this

end RadIn

section Rad256

variable {G : Type} [Group G]

theorem rad_facts {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4)
    {E₀ : Subgroup ↥(unipAll k)} (h : E₀ = radOne k ∨ E₀ = radTwo k) :
    (∀ g ∈ E₀, g * g = 1) ∧ (∀ g ∈ E₀, ∀ g' ∈ E₀, g * g' = g' * g) ∧ Nat.card ↥E₀ = 16 := by
  have := charP_two_of_card_four_B42 hk
  rcases h with rfl | rfl
  · exact ⟨fun g hg => mul_self_of_mem_radOne hg, fun g hg g' hg' => mul_comm_of_mem_radOne hg hg',
      by rw [card_radOne, hk]; norm_num⟩
  · exact ⟨fun g hg => mul_self_of_mem_radTwo hg, fun g hg g' hg' => mul_comm_of_mem_radTwo hg hg',
      by rw [card_radTwo, hk]; norm_num⟩

theorem exists_rad256 {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4)
    {A₁ B₁ : Subgroup G} {t : G} (ht : t * t = 1)
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ B₁, a * b = b * a) (hdisj : A₁ ⊓ B₁ = ⊥)
    (hsw₁ : ∀ x ∈ A₁, t * x * t⁻¹ ∈ B₁) (hsw₂ : ∀ x ∈ B₁, t * x * t⁻¹ ∈ A₁)
    (e : ↥A₁ ≃* ↥(unipAll k)) {s : G} (hs : s ∈ A₁ ⊔ B₁) (hs2 : s * s = 1) :
    ∃ D : Subgroup G, D ≤ A₁ ⊔ B₁ ∧ (∀ x ∈ D, x * s = s * x) ∧
      (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) ∧ (∀ x ∈ D, x * x = 1) ∧ Nat.card ↥D = 256 := by
  have := charP_two_of_card_four_B42 hk
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_forall_comm hcomm hs
  have hab2 : (a * a) * (b * b) = 1 := by
    calc (a * a) * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hcomm a ha b hb]
      _ = (a * b) * (a * b) := by group
      _ = s * s := by rw [hab]
      _ = 1 := hs2
  have haa : a * a = 1 := by
    have hm : a * a ∈ A₁ ⊓ B₁ := by
      refine ⟨A₁.mul_mem ha ha, ?_⟩
      have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hab2
      rw [this]
      exact B₁.inv_mem (B₁.mul_mem hb hb)
    rw [hdisj, Subgroup.mem_bot] at hm
    exact hm
  have hbb : b * b = 1 := by
    rw [haa, one_mul] at hab2
    exact hab2
  have hb' : t * b * t⁻¹ ∈ A₁ := hsw₂ b hb
  have hb'2 : (t * b * t⁻¹) * (t * b * t⁻¹) = 1 := by
    calc (t * b * t⁻¹) * (t * b * t⁻¹) = t * (b * b) * t⁻¹ := by group
      _ = 1 := by rw [hbb]; group
  have hsq : ∀ g : ↥(unipAll k), g * g = 1 → ∃ E₀ : Subgroup ↥(unipAll k),
      (E₀ = radOne k ∨ E₀ = radTwo k) ∧ g ∈ E₀ := by
    intro g hg
    rcases (sq_eq_one_iff g).mp hg with h | h
    · exact ⟨radOne k, Or.inl rfl, h⟩
    · exact ⟨radTwo k, Or.inr rfl, h⟩
  have hea2 : e ⟨a, ha⟩ * e ⟨a, ha⟩ = 1 := by
    rw [← map_mul, show (⟨a, ha⟩ * ⟨a, ha⟩ : ↥A₁) = 1 from Subtype.ext haa, map_one]
  have heb2 : e ⟨t * b * t⁻¹, hb'⟩ * e ⟨t * b * t⁻¹, hb'⟩ = 1 := by
    rw [← map_mul, show (⟨t * b * t⁻¹, hb'⟩ * ⟨t * b * t⁻¹, hb'⟩ : ↥A₁) = 1 from
      Subtype.ext hb'2, map_one]
  obtain ⟨Ea, hEa, heaE⟩ := hsq _ hea2
  obtain ⟨Eb, hEb, hebE⟩ := hsq _ heb2
  obtain ⟨hEa_sq, hEa_comm, hEa_card⟩ := rad_facts hk hEa
  obtain ⟨hEb_sq, hEb_comm, hEb_card⟩ := rad_facts hk hEb
  set Da : Subgroup G := radIn A₁ e Ea with hDa
  set Db' : Subgroup G := radIn A₁ e Eb with hDb'
  set Db : Subgroup G := Db'.map (MulAut.conj t).toMonoidHom with hDb
  have hDa_le : Da ≤ A₁ := radIn_le
  have hDb_le : Db ≤ B₁ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hsw₁ y (radIn_le hy)
  have hDa_sq : ∀ x ∈ Da, x * x = 1 := fun x hx => radIn_mul_self hEa_sq hx
  have hDa_comm : ∀ x ∈ Da, ∀ y ∈ Da, x * y = y * x := fun x hx y hy => radIn_comm hEa_comm hx hy
  have hDb'_sq : ∀ x ∈ Db', x * x = 1 := fun x hx => radIn_mul_self hEb_sq hx
  have hDb'_comm : ∀ x ∈ Db', ∀ y ∈ Db', x * y = y * x :=
    fun x hx y hy => radIn_comm hEb_comm hx hy
  obtain ⟨hDb_comm, hDb_sq⟩ := isElemAbelian_map_conj hDb'_comm hDb'_sq t
  have hDaDb : ∀ u ∈ Da, ∀ w ∈ Db, u * w = w * u :=
    fun u hu w hw => hcomm u (hDa_le hu) w (hDb_le hw)
  have hD_sq : ∀ x ∈ Da ⊔ Db, x * x = 1 := by
    intro x hx
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_sup_of_forall_comm hDaDb hx
    calc u * w * (u * w) = u * (w * u) * w := by group
      _ = u * (u * w) * w := by rw [← hDaDb u hu w hw]
      _ = (u * u) * (w * w) := by group
      _ = 1 := by rw [hDa_sq u hu, hDb_sq w hw, one_mul]
  have hD_comm : ∀ x ∈ Da ⊔ Db, ∀ y ∈ Da ⊔ Db, x * y = y * x := by
    intro x hx y hy
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_sup_of_forall_comm hDaDb hx
    obtain ⟨u', hu', w', hw', rfl⟩ := mem_sup_of_forall_comm hDaDb hy
    calc u * w * (u' * w') = u * (w * u') * w' := by group
      _ = u * (u' * w) * w' := by rw [← hDaDb u' hu' w hw]
      _ = (u * u') * (w * w') := by group
      _ = (u' * u) * (w' * w) := by rw [hDa_comm u hu u' hu', hDb_comm w hw w' hw']
      _ = u' * (u * w') * w := by group
      _ = u' * (w' * u) * w := by rw [hDaDb u hu w' hw']
      _ = u' * w' * (u * w) := by group
  have haDa : a ∈ Da := mem_radIn_of_mem ha heaE
  have hbDb : b ∈ Db := by
    refine ⟨t * b * t⁻¹, mem_radIn_of_mem hb' hebE, ?_⟩
    show t * (t * b * t⁻¹) * t⁻¹ = b
    rw [htinv]
    calc t * (t * b * t) * t = (t * t) * b * (t * t) := by group
      _ = b := by rw [ht]; group
  have hsD : s ∈ Da ⊔ Db := by
    rw [hab]
    exact Subgroup.mul_mem_sup haDa hbDb
  refine ⟨Da ⊔ Db, sup_le_sup hDa_le hDb_le, fun x hx => hD_comm x hx s hsD, hD_comm, hD_sq, ?_⟩
  have hdis : Disjoint Da Db :=
    Disjoint.mono hDa_le hDb_le (disjoint_iff.mpr hdisj)
  have e' := supEquivProd Da Db hDaDb hdis
  rw [Nat.card_congr e'.toEquiv, Nat.card_prod, hDa, card_radIn, hEa_card, hDb, card_map_conj,
    hDb', card_radIn, hEb_card]

end Rad256

end CFSG.OddStandard.Seitz77
