module

public import CFSG.GH74.GLS.IVK.Prod32.LangDefs
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GH74.GLS.IVK.Statements.Sec32

public section

namespace CFSG.GH74.GLS.IVK.Prod3.LangF

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter
open scoped commutatorElement

section Generic

theorem mem_sup_iff_of_comm {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {g : G} :
    g ∈ A ⊔ B ↔ ∃ x ∈ A, ∃ y ∈ B, x * y = g := by
  constructor
  · intro hg
    let S : Subgroup G :=
      { carrier := {g | ∃ x ∈ A, ∃ y ∈ B, x * y = g}
        mul_mem' := by
          rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
          refine ⟨x * x', mul_mem hx hx', y * y', mul_mem hy hy', ?_⟩
          have := h x' hx' y hy
          calc x * x' * (y * y') = x * (x' * y) * y' := by simp only [mul_assoc]
            _ = x * (y * x') * y' := by rw [this]
            _ = x * y * (x' * y') := by simp only [mul_assoc]
        one_mem' := ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
        inv_mem' := by
          rintro _ ⟨x, hx, y, hy, rfl⟩
          refine ⟨x⁻¹, inv_mem hx, y⁻¹, inv_mem hy, ?_⟩
          have := h x⁻¹ (inv_mem hx) y⁻¹ (inv_mem hy)
          rw [mul_inv_rev, this] }
    have hle : A ⊔ B ≤ S := sup_le (fun x hx => ⟨x, hx, 1, one_mem _, mul_one x⟩)
      (fun y hy => ⟨1, one_mem _, y, hy, one_mul y⟩)
    exact hle hg
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact mul_mem (mem_sup_left hx) (mem_sup_right hy)

theorem commutatorElement_mul_mul {G : Type*} [Group G] {k l u v : G}
    (hu' : Commute u l) (hv : Commute v k) (huv : Commute u v) :
    ⁅k * u, l * v⁆ = ⁅k, l⁆ := by
  have h1 : u * l = l * u := hu'.eq
  have h2 : v * k⁻¹ = k⁻¹ * v := (hv.inv_right).eq
  have h3 : u * l * v * u⁻¹ = l * v := by
    rw [h1, mul_assoc l u v, huv.eq, ← mul_assoc l v u, mul_assoc (l * v) u u⁻¹, mul_inv_cancel,
      mul_one]
  simp only [commutatorElement_def, mul_inv_rev]
  calc k * u * (l * v) * (u⁻¹ * k⁻¹) * (v⁻¹ * l⁻¹)
      = k * (u * l * v * u⁻¹) * k⁻¹ * v⁻¹ * l⁻¹ := by simp only [mul_assoc]
    _ = k * (l * v) * k⁻¹ * v⁻¹ * l⁻¹ := by rw [h3]
    _ = k * l * (v * k⁻¹) * v⁻¹ * l⁻¹ := by simp only [mul_assoc]
    _ = k * l * (k⁻¹ * v) * v⁻¹ * l⁻¹ := by rw [h2]
    _ = k * l * k⁻¹ * l⁻¹ := by simp only [mul_assoc, mul_inv_cancel_left]

theorem layer_eq_top {M : Type*} [Group M] (hM : IsQuasisimple M) : layer M = ⊤ :=
  eq_top_iff.mpr (CFSG.LocalCores.component_le_layer
    (K := (⊤ : Subgroup M))
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hM,
      Subgroup.IsSubnormal.top⟩)

end Generic

section SL2

variable {F : Type} [Field F]

theorem mem_statedSL_iff_det (A : GL (Fin 2) F) :
    A ∈ StatedSL 2 F ↔ (A : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem det_eq_one (y : SL2 F) :
    ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  (mem_statedSL_iff_det _).1 y.2

theorem central_smul (y : SL2 F) (hy : ∀ x : SL2 F, x * y = y * x) :
    ∃ μ : F, μ * μ = 1 ∧
      ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = μ • (1 : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨μ, hμ⟩ := exists_smul_one_of_commute_sl ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    (fun b => by
      have := congrArg (fun w : SL2 F => ((w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
        (hy (specialLinearGroupEquivStatedSL 2 F b))
      simpa [specialLinearGroupEquivStatedSL_coe] using this.symm)
  refine ⟨μ, ?_, hμ⟩
  have hdet := det_eq_one y
  rw [hμ, Matrix.det_smul, Matrix.det_one] at hdet
  simpa [sq] using hdet

theorem central_cases (y : SL2 F) (hy : ∀ x : SL2 F, x * y = y * x) :
    ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 ∨
      ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
  obtain ⟨μ, hμ, hy'⟩ := central_smul y hy
  rcases mul_self_eq_one_iff.1 hμ with rfl | rfl
  · left
    simpa using hy'
  · right
    simpa using hy'

theorem central_mem_center (y : SL2 F) (hy : ∀ x : SL2 F, x * y = y * x) :
    (y : GL (Fin 2) F) ∈ Subgroup.center (GL (Fin 2) F) := by
  obtain ⟨μ, -, hy'⟩ := central_smul y hy
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hy', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

theorem mk_mul_of_mem_center (g s : GL (Fin 2) F) (hs : s ∈ Subgroup.center (GL (Fin 2) F)) :
    Matrix.ProjGenLinGroup.mk (g * s) = Matrix.ProjGenLinGroup.mk g := by
  rw [map_mul, (Matrix.ProjGenLinGroup.mk_eq_one).2 hs, mul_one]

theorem mem_slFixed_iff (σ : F ≃+* F) (y : SL2 F) :
    y ∈ slFixed σ ↔ stableAut (StatedSL 2 F) (fieldStable_statedSL 2) σ y = y := by
  constructor
  · intro hy
    exact Subtype.ext (show glAut σ (y : GL (Fin 2) F) = (y : GL (Fin 2) F) from hy)
  · intro hy
    exact (show Matrix.GeneralLinearGroup.map σ.toRingHom (y : GL (Fin 2) F) = (y : GL (Fin 2) F) from
      congrArg Subtype.val hy)

end SL2

section Basic

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

abbrev cen (K : Subgroup H) (a : H) : Subgroup H := K ⊓ centralizer ({a} : Set H)

theorem mem_cen {K : Subgroup H} {a x : H} : x ∈ cen K a ↔ x ∈ K ∧ x * a = a * x := by
  rw [cen, mem_inf, mem_centralizer_singleton_iff]

theorem cen_le_cen_sup₁ (K₁ K₂ : Subgroup H) (a : H) : cen K₁ a ≤ cen (K₁ ⊔ K₂) a :=
  inf_le_inf_right _ le_sup_left

theorem cen_le_cen_sup₂ (K₁ K₂ : Subgroup H) (a : H) : cen K₂ a ≤ cen (K₁ ⊔ K₂) a :=
  inf_le_inf_right _ le_sup_right

theorem conj_comm_a {c x : H} (hc : c * a = a * c) (hx : x * a = a * x) :
    (c * x * c⁻¹) * a = a * (c * x * c⁻¹) := by
  have hac : Commute a c := hc.symm
  have hax : Commute a x := hx.symm
  exact (Commute.mul_right (Commute.mul_right hac hax) (Commute.inv_right hac)).symm.eq

theorem symm (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) : LangHyp K₂ K₁ z a e₂ e₁ σ₂ σ₁ where
  comm x hx y hy := (h.comm y hy x hx).symm
  inter := by rw [inf_comm]; exact h.inter
  z_ord := h.z_ord
  a_sq := h.a_sq
  norm₁ := h.norm₂
  norm₂ := h.norm₁
  odd₁ := h.odd₂
  odd₂ := h.odd₁
  σ₁_ord := h.σ₂_ord
  σ₂_ord := h.σ₁_ord
  act₁ := h.act₂
  act₂ := h.act₁

section WithHyp

variable (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂)
include h

theorem z_mem : z ∈ K₁ ⊓ K₂ := by
  rw [h.inter]
  exact mem_zpowers z

theorem z_mem₁ : z ∈ K₁ := (z_mem h).1

theorem z_mem₂ : z ∈ K₂ := (z_mem h).2

theorem z_sq : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [h.z_ord, pow_two] at this

theorem z_ne_one : z ≠ 1 := by
  intro h1
  have := h.z_ord
  rw [h1, orderOf_one] at this
  omega

theorem mem_sup_iff {x : H} : x ∈ K₁ ⊔ K₂ ↔ ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, k₁ * k₂ = x :=
  mem_sup_iff_of_comm h.comm

theorem e₁_central {k : H} (hk₁ : k ∈ K₁) (hk₂ : k ∈ K₂) :
    ∀ x : SL2 F₁, x * e₁ ⟨k, hk₁⟩ = e₁ ⟨k, hk₁⟩ * x := by
  intro x
  obtain ⟨x', rfl⟩ := e₁.surjective x
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact h.comm x' x'.2 k hk₂

theorem e₁_z_central :
    ∀ x : SL2 F₁, x * e₁ ⟨z, z_mem₁ h⟩ = e₁ ⟨z, z_mem₁ h⟩ * x :=
  e₁_central h (z_mem₁ h) (z_mem₂ h)

theorem e₁_z_matrix :
    (((e₁ ⟨z, z_mem₁ h⟩ : SL2 F₁) : GL (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁) = -1 := by
  rcases central_cases _ (e₁_z_central h) with h1 | h1
  · exfalso
    have h2 : e₁ ⟨z, z_mem₁ h⟩ = 1 := Subtype.ext (Units.ext (by simpa using h1))
    have h3 := e₁.injective (h2.trans (map_one e₁).symm)
    exact z_ne_one h (congrArg Subtype.val h3)
  · exact h1

end WithHyp

end Basic

section Conj

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

variable (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂)
include h

theorem exists_twist_of_fixed {k₁ k₂ : H} (hk₁ : k₁ ∈ K₁) (hk₂ : k₂ ∈ K₂)
    (hc : k₁ * k₂ * a = a * (k₁ * k₂)) :
    ∃ u ∈ K₁ ⊓ K₂, a * k₁ * a⁻¹ = k₁ * u ∧ a * k₂ * a⁻¹ = k₂ * u⁻¹ := by
  have hp : a * k₁ * a⁻¹ ∈ K₁ := h.norm₁ k₁ hk₁
  have hq : a * k₂ * a⁻¹ ∈ K₂ := h.norm₂ k₂ hk₂
  have hpq : (a * k₁ * a⁻¹) * (a * k₂ * a⁻¹) = k₁ * k₂ := by
    have : a * (k₁ * k₂) * a⁻¹ = k₁ * k₂ := by
      rw [← hc, mul_inv_cancel_right]
    rw [← this]
    group
  set p := a * k₁ * a⁻¹ with hpdef
  set q := a * k₂ * a⁻¹ with hqdef
  have hu2 : k₁⁻¹ * p = k₂ * q⁻¹ := by
    calc k₁⁻¹ * p = k₁⁻¹ * (p * q) * q⁻¹ := by group
      _ = k₁⁻¹ * (k₁ * k₂) * q⁻¹ := by rw [hpq]
      _ = k₂ * q⁻¹ := by group
  have hu₁ : k₁⁻¹ * p ∈ K₁ := mul_mem (inv_mem hk₁) hp
  have hu₂ : k₁⁻¹ * p ∈ K₂ := by
    rw [hu2]
    exact mul_mem hk₂ (inv_mem hq)
  refine ⟨k₁⁻¹ * p, ⟨hu₁, hu₂⟩, by rw [mul_inv_cancel_left], ?_⟩
  have h3 : q = (k₁⁻¹ * p)⁻¹ * k₂ := by
    rw [hu2]
    group
  rw [h3]
  exact (h.comm _ (inv_mem hu₁) k₂ hk₂)

end Conj

section Model

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

variable (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂)
include h

theorem fix_iff₁ (x : ↥K₁) : (x : H) * a = a * x ↔ e₁ x ∈ slFixed σ₁ := by
  rw [mem_slFixed_iff, ← h.act₁ x (h.norm₁ x x.2)]
  constructor
  · intro hx
    have : a * x * a⁻¹ = x := by rw [← hx, mul_inv_cancel_right]
    congr 1
    exact Subtype.ext this
  · intro hx
    have h2 := congrArg Subtype.val (e₁.injective hx)
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm

noncomputable def jEquiv₁ : ↥(cen K₁ a) ≃* ↥(slFixed σ₁) where
  toFun x := ⟨e₁ ⟨x, (mem_cen.1 x.2).1⟩,
    (fix_iff₁ h ⟨x, (mem_cen.1 x.2).1⟩).1 (mem_cen.1 x.2).2⟩
  invFun y := ⟨(e₁.symm y : H), mem_cen.2 ⟨(e₁.symm y).2,
    (fix_iff₁ h (e₁.symm y)).2 (by simp)⟩⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    show e₁ ⟨((x : H) * y : H), _⟩ = e₁ ⟨x, _⟩ * e₁ ⟨y, _⟩
    rw [← map_mul]
    rfl

end Model

section S1

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

variable (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂)
include h

theorem exists_jModel {r : ℕ} (hF₁ : Nat.card F₁ = r ^ 4) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = r ^ 2 ∧
      Nonempty (↥(cen K₁ a) ≃* SL2 F₀) := by
  obtain ⟨F₀, hF₀, hfin, hcard, ⟨e⟩⟩ := hasSL2Model_slFixed σ₁
  refine ⟨F₀, hF₀, hfin, ?_, ⟨(jEquiv₁ h).trans e⟩⟩
  rw [h.σ₁_ord, hF₁] at hcard
  have h2 : (Nat.card F₀) ^ 2 = (r ^ 2) ^ 2 := by rw [hcard]; ring
  exact Nat.pow_left_injective (by norm_num) h2

theorem isQuasisimple_cen₁ {r : ℕ} (hr : 3 ≤ r) (hF₁ : Nat.card F₁ = r ^ 4) :
    IsQuasisimple ↥(cen K₁ a) := by
  obtain ⟨F₀, hF₀, hfin, hcard, ⟨e⟩⟩ := exists_jModel h hF₁
  have h4 : 4 ≤ Nat.card F₀ := by
    rw [hcard]
    nlinarith
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((specialLinearGroupEquivStatedSL 2 F₀).trans e.symm)
    (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4)

theorem eLayer_cen₁ {r : ℕ} (hr : 3 ≤ r) (hF₁ : Nat.card F₁ = r ^ 4) :
    ELayer (cen K₁ a) = cen K₁ a := by
  rw [ELayer, layer_eq_top (isQuasisimple_cen₁ h hr hF₁), Subgroup.map_top,
    Subgroup.range_subtype]

theorem hasSL2Model_cen₁ {r : ℕ} (hF₁ : Nat.card F₁ = r ^ 4) :
    HasSL2Model ↥(cen K₁ a) (fun q => q = r ^ 2) := by
  obtain ⟨F₀, hF₀, hfin, hcard, ⟨e⟩⟩ := exists_jModel h hF₁
  exact ⟨F₀, hF₀, hfin, hcard, ⟨e⟩⟩

end S1

section Comm

variable {H : Type} [Group H] {K₁ K₂ : Subgroup H}

@[expose] def mulHom (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) : ↥K₁ × ↥K₂ →* H where
  toFun p := (p.1 : H) * p.2
  map_one' := by simp
  map_mul' p q := by
    have := hc q.1 q.1.2 p.2 p.2.2
    show (p.1 : H) * q.1 * ((p.2 : H) * q.2) = (p.1 * p.2) * (q.1 * q.2)
    calc (p.1 : H) * q.1 * ((p.2 : H) * q.2) = p.1 * ((q.1 : H) * p.2) * q.2 := by
          simp only [mul_assoc]
      _ = p.1 * ((p.2 : H) * q.1) * q.2 := by rw [this]
      _ = (p.1 * p.2) * (q.1 * q.2) := by simp only [mul_assoc]

theorem commutator_split (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) {k₁ l₁ k₂ l₂ : H}
    (hk₁ : k₁ ∈ K₁) (hl₁ : l₁ ∈ K₁) (hk₂ : k₂ ∈ K₂) (hl₂ : l₂ ∈ K₂) :
    ⁅k₁ * k₂, l₁ * l₂⁆ = ⁅k₁, l₁⁆ * ⁅k₂, l₂⁆ := by
  have h1 := map_commutatorElement (mulHom hc) (⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩) (⟨l₁, hl₁⟩, ⟨l₂, hl₂⟩)
  have h2 : ⁅((⟨k₁, hk₁⟩ : ↥K₁), (⟨k₂, hk₂⟩ : ↥K₂)), ((⟨l₁, hl₁⟩ : ↥K₁), (⟨l₂, hl₂⟩ : ↥K₂))⁆ =
      (⁅(⟨k₁, hk₁⟩ : ↥K₁), ⟨l₁, hl₁⟩⁆, ⁅(⟨k₂, hk₂⟩ : ↥K₂), ⟨l₂, hl₂⟩⁆) := by
    simp [commutatorElement_def]
  rw [h2] at h1
  exact h1.symm

end Comm

end CFSG.GH74.GLS.IVK.Prod3.LangF
