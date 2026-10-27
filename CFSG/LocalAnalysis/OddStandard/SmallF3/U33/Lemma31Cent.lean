module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.M12Model

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped commutatorElement Pointwise

private instance instDecEqM12 : DecidableEq M12Mod := fun a b =>
  if h : M12Mod.equivProd a = M12Mod.equivProd b then isTrue (M12Mod.equivProd.injective h)
  else isFalse (fun hab => h (by rw [hab]))

private def m1 : M12Mod := M12Mod.mx₁ * M12Mod.mx₂
private def y : M12Mod := M12Mod.mx₁ ^ 2
private def z : M12Mod := (M12Mod.mx₁ * M12Mod.mx₂) ^ 2

private def zp1 : Finset M12Mod := {1, m1, m1 ^ 2, m1 ^ 3}
private def zpy : Finset M12Mod := {1, y}
private def zpz : Finset M12Mod := {1, z}

private lemma isOfFinOrder_of_orderOf_eq {g : M12Mod} {n : ℕ} (hn : 0 < n)
    (h : orderOf g = n) : IsOfFinOrder g :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, by rw [← h]; exact pow_orderOf_eq_one g⟩

private lemma hord_m1 : orderOf m1 = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)

private lemma hord_y : orderOf y = 2 :=
  orderOf_eq_prime (by decide) (by decide)

private lemma hord_z : orderOf z = 2 :=
  orderOf_eq_prime (by decide) (by decide)

private lemma image_m1 : (Finset.range 4).image (m1 ^ ·) = zp1 := by decide
private lemma image_y : (Finset.range 2).image (y ^ ·) = zpy := by decide
private lemma image_z : (Finset.range 2).image (z ^ ·) = zpz := by decide

private lemma mem_zpowers_m1 (x : M12Mod) : x ∈ zpowers m1 ↔ x ∈ zp1 := by
  rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf
    (isOfFinOrder_of_orderOf_eq (by norm_num) hord_m1), hord_m1, image_m1]

private lemma mem_zpowers_y (x : M12Mod) : x ∈ zpowers y ↔ x ∈ zpy := by
  rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf
    (isOfFinOrder_of_orderOf_eq (by norm_num) hord_y), hord_y, image_y]

private lemma mem_zpowers_z (x : M12Mod) : x ∈ zpowers z ↔ x ∈ zpz := by
  rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf
    (isOfFinOrder_of_orderOf_eq (by norm_num) hord_z), hord_z, image_z]

private lemma one_comm : (1 : M12Mod) ∈ zp1 * zpy := by decide

private lemma mul_comm_check : ∀ (a1 a2 : Fin 4) (a3 a4 : Fin 2) (b1 b2 : Fin 4) (b3 b4 : Fin 2),
    (⟨a1, a2, a3, a4⟩ : M12Mod) ∈ zp1 * zpy → (⟨b1, b2, b3, b4⟩ : M12Mod) ∈ zp1 * zpy →
      (⟨a1, a2, a3, a4⟩ : M12Mod) * ⟨b1, b2, b3, b4⟩ ∈ zp1 * zpy := by decide

private lemma mul_comm_mem : ∀ (a b : M12Mod), a ∈ zp1 * zpy → b ∈ zp1 * zpy →
    a * b ∈ zp1 * zpy := by
  intro a b ha hb
  obtain ⟨a1, a2, a3, a4⟩ := a
  obtain ⟨b1, b2, b3, b4⟩ := b
  exact mul_comm_check a1 a2 a3 a4 b1 b2 b3 b4 ha hb

private lemma inv_comm_check : ∀ (a1 a2 : Fin 4) (a3 a4 : Fin 2),
    (⟨a1, a2, a3, a4⟩ : M12Mod) ∈ zp1 * zpy →
      (⟨a1, a2, a3, a4⟩ : M12Mod)⁻¹ ∈ zp1 * zpy := by decide

private lemma inv_comm_mem : ∀ (a : M12Mod), a ∈ zp1 * zpy → a⁻¹ ∈ zp1 * zpy := by
  intro a ha
  obtain ⟨a1, a2, a3, a4⟩ := a
  exact inv_comm_check a1 a2 a3 a4 ha

private def Scomm : Subgroup M12Mod where
  carrier := {x | x ∈ zp1 * zpy}
  one_mem' := one_comm
  mul_mem' := fun {a b} ha hb => mul_comm_mem a b ha hb
  inv_mem' := fun {a} ha => inv_comm_mem a ha

private lemma mem_Scomm (x : M12Mod) : x ∈ Scomm ↔ x ∈ zp1 * zpy := Iff.rfl

private lemma mem_Scomm_m1 : m1 ∈ Scomm := (mem_Scomm m1).mpr (by decide)
private lemma mem_Scomm_y : y ∈ Scomm := (mem_Scomm y).mpr (by decide)

private lemma mem_sup_comm (x : M12Mod) :
    x ∈ (zpowers m1 ⊔ zpowers y : Subgroup M12Mod) ↔ x ∈ zp1 * zpy := by
  constructor
  · intro hx
    have hle : (zpowers m1 ⊔ zpowers y : Subgroup M12Mod) ≤ Scomm := by
      apply sup_le
      · rw [Subgroup.zpowers_le]; exact mem_Scomm_m1
      · rw [Subgroup.zpowers_le]; exact mem_Scomm_y
    exact (mem_Scomm x).mp (hle hx)
  · intro hx
    rw [Finset.mem_mul] at hx
    obtain ⟨p, hp, q, hq, rfl⟩ := hx
    exact mul_mem (Subgroup.mem_sup_left ((mem_zpowers_m1 p).mpr hp))
      (Subgroup.mem_sup_right ((mem_zpowers_y q).mpr hq))

private instance instFintypeSup : Fintype (↥(zpowers m1 ⊔ zpowers y)) :=
  Fintype.subtype (zp1 * zpy) (fun x => (mem_sup_comm x).symm)

private lemma center1_check : ∀ (a b : Fin 4) (i j : Fin 2),
    (∀ (c d : Fin 4) (k l : Fin 2),
      (⟨c, d, k, l⟩ : M12Mod) * ⟨a, b, i, j⟩ = ⟨a, b, i, j⟩ * ⟨c, d, k, l⟩) →
    (⟨a, b, i, j⟩ : M12Mod) ∈ zpz := by decide
private lemma center2_check : ∀ (a b : Fin 4) (i j : Fin 2),
    (⟨a, b, i, j⟩ : M12Mod) ∈ zpz →
    (∀ (c d : Fin 4) (k l : Fin 2),
      (⟨c, d, k, l⟩ : M12Mod) * ⟨a, b, i, j⟩ = ⟨a, b, i, j⟩ * ⟨c, d, k, l⟩) := by decide

private lemma center_model :
    (⊤ : Subgroup M12Mod) ⊓ Subgroup.centralizer (⊤ : Set M12Mod) = zpowers z := by
  rw [top_inf_eq]
  apply le_antisymm
  · intro x hx
    rw [mem_zpowers_z]
    have hx' : ∀ h : M12Mod, h * x = x * h := fun h => hx h trivial
    exact center1_check x.a x.b x.i x.j (fun c d k l => hx' ⟨c, d, k, l⟩)
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rw [mem_zpowers_z] at hx
    intro h _
    exact center2_check x.a x.b x.i x.j hx h.a h.b h.i h.j

private lemma cent8_incl : ∀ (a b : Fin 4) (i j : Fin 2),
    (⟨a, b, i, j⟩ : M12Mod) ^ 8 = 1 → (⟨a, b, i, j⟩ : M12Mod) ^ 4 ≠ 1 →
    ∀ (c d : Fin 4) (k l : Fin 2),
      (⟨c, d, k, l⟩ : M12Mod) * ⟨a, b, i, j⟩ = ⟨a, b, i, j⟩ * ⟨c, d, k, l⟩ →
      (⟨c, d, k, l⟩ : M12Mod) ∈ (Finset.range 8).image ((⟨a, b, i, j⟩ : M12Mod) ^ ·) := by
  decide

private lemma cent8_model (m : M12Mod) (hord : orderOf m = 8) :
    Subgroup.centralizer ({m} : Set M12Mod) = zpowers m := by
  have h8 : m ^ 8 = 1 := by rw [← hord]; exact pow_orderOf_eq_one m
  have h4 : m ^ 4 ≠ 1 := by
    intro hh
    have hdvd : orderOf m ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hh
    rw [hord] at hdvd
    norm_num at hdvd
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    simp only [Set.mem_singleton_iff, forall_eq] at hx
    rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf
      (isOfFinOrder_of_orderOf_eq (by norm_num) hord), hord]
    exact cent8_incl m.a m.b m.i m.j h8 h4 x.a x.b x.i x.j hx.symm
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]

private lemma range_inf_eq_map_comap {M G : Type*} [Group M] [Group G]
    (φ : M →* G) (K : Subgroup G) : φ.range ⊓ K = (K.comap φ).map φ := by
  rw [← Subgroup.map_comap_eq_self (f := φ) (H := φ.range ⊓ K) inf_le_left]
  rw [Subgroup.comap_inf, MonoidHom.comap_range_self, top_inf_eq]

private lemma comap_centralizer_singleton {M G : Type*} [Group M] [Group G]
    (φ : M →* G) (hφ : Function.Injective φ) (m : M) :
    (Subgroup.centralizer ({φ m} : Set G)).comap φ = Subgroup.centralizer ({m} : Set M) := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    apply hφ
    rw [map_mul, map_mul]
    exact h
  · intro h
    rw [← map_mul, ← map_mul, h]

private lemma centralizer_range_inf {M G : Type*} [Group M] [Group G]
    (φ : M →* G) (hφ : Function.Injective φ) (m : M) :
    φ.range ⊓ Subgroup.centralizer ({φ m} : Set G) =
      (Subgroup.centralizer ({m} : Set M)).map φ := by
  rw [range_inf_eq_map_comap, comap_centralizer_singleton φ hφ]

private lemma comap_centralizer_range {M G : Type*} [Group M] [Group G]
    (φ : M →* G) (hφ : Function.Injective φ) :
    (Subgroup.centralizer (φ.range : Set G)).comap φ = Subgroup.centralizer (⊤ : Set M) := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y _
    apply hφ
    rw [map_mul, map_mul]
    exact h (φ y) ⟨y, rfl⟩
  · intro h g hg
    obtain ⟨y, rfl⟩ := hg
    rw [← map_mul, ← map_mul, h y trivial]

variable {G : Type*} [Group G] {x₁ x₂ lam tau : G}

private lemma map_z (φ : M12Mod →* G) (h1 : φ M12Mod.mx₁ = x₁) (h2 : φ M12Mod.mx₂ = x₂) :
    φ z = (x₁ * x₂) ^ 2 := by
  rw [show z = (M12Mod.mx₁ * M12Mod.mx₂) ^ 2 from rfl, map_pow, map_mul, h1, h2]

theorem M12Rel.center_eq (h : M12Rel x₁ x₂ lam tau) :
    m12Grp x₁ x₂ lam tau ⊓ centralizer (m12Grp x₁ x₂ lam tau : Set G) =
      zpowers ((x₁ * x₂) ^ 2) := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3, h4⟩ := h.exists_embedding
  have hcen : m12Grp x₁ x₂ lam tau ⊓ centralizer (m12Grp x₁ x₂ lam tau : Set G) =
      (zpowers z).map φ := by
    rw [← hrange]
    rw [range_inf_eq_map_comap φ (Subgroup.centralizer (φ.range : Set G)),
      comap_centralizer_range φ hinj]
    rw [← center_model, top_inf_eq]
  rw [hcen, MonoidHom.map_zpowers, map_z φ h1 h2]
theorem M12Rel.centralizer_eq_zpowers_of_orderOf_eq_eight (h : M12Rel x₁ x₂ lam tau) {w : G}
    (hw : w ∈ m12Grp x₁ x₂ lam tau) (h8 : orderOf w = 8) :
    m12Grp x₁ x₂ lam tau ⊓ centralizer ({w} : Set G) = zpowers w := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3, h4⟩ := h.exists_embedding
  rw [← hrange] at hw
  obtain ⟨m, rfl⟩ := hw
  have hord : orderOf m = 8 := by
    rw [← orderOf_injective φ hinj m, h8]
  have hL : m12Grp x₁ x₂ lam tau ⊓ centralizer ({φ m} : Set G) =
      (Subgroup.centralizer ({m} : Set M12Mod)).map φ := by
    rw [← hrange]
    exact centralizer_range_inf φ hinj m
  rw [hL, cent8_model m hord, MonoidHom.map_zpowers]
end CFSG.OddStandard.SmallF3.HarrisU33
