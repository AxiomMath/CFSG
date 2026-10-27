module

public import CFSG.HardMathSupport.RichardWeiss.Proving.ShortQuotient
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderGlue
public import CFSG.HardMathSupport.RichardWeiss.Proving.HeartCohomology

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] {N : ℕ}

theorem conj_mem_commutator_VL {V L : Subgroup G} {m : G} (hmV : ∀ v ∈ V, m * v * m⁻¹ ∈ V)
    (hmL : ∀ l ∈ L, m * l * m⁻¹ ∈ L) {x : G} (hx : x ∈ ⁅V, L⁆) : m * x * m⁻¹ ∈ ⁅V, L⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  refine Subgroup.closure_induction (p := fun x _ => m * x * m⁻¹ ∈
    Subgroup.closure {g | ∃ g₁ ∈ V, ∃ g₂ ∈ L, ⁅g₁, g₂⁆ = g}) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨v, hv, l, hl, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨m * v * m⁻¹, hmV v hv, m * l * m⁻¹, hmL l hl, ?_⟩
    simp only [commutatorElement_def]; group
  · simp
  · intro x y _ _ hx hy
    have : m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have : m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ hx

@[expose] noncomputable def piA {U : Subgroup G} (π : ↥U →* Multiplicative (altHeart N)) (g : G) :
    altHeart N :=
  open Classical in if h : g ∈ U then Multiplicative.toAdd (π ⟨g, h⟩) else 0

@[expose] noncomputable def thetaA {M : Subgroup G} (θ : ↥M →* Perm (Fin N)) (g : G) :
    Perm (Fin N) :=
  open Classical in if h : g ∈ M then θ ⟨g, h⟩ else 1

variable {U M : Subgroup G} {π : ↥U →* Multiplicative (altHeart N)} {θ : ↥M →* Perm (Fin N)}

theorem piA_of_mem {g : G} (h : g ∈ U) :
    piA π g = Multiplicative.toAdd (π ⟨g, h⟩) := by
  classical
  simp [piA, h]

theorem thetaA_of_mem {g : G} (h : g ∈ M) : thetaA θ g = θ ⟨g, h⟩ := by
  classical
  simp [thetaA, h]

theorem piA_mul {u v : G} (hu : u ∈ U) (hv : v ∈ U) : piA π (u * v) = piA π u + piA π v := by
  rw [piA_of_mem (U.mul_mem hu hv), piA_of_mem hu, piA_of_mem hv]
  have : (⟨u * v, U.mul_mem hu hv⟩ : ↥U) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
  rw [this, map_mul]; rfl

theorem piA_one : piA π (1 : G) = 0 := by
  rw [piA_of_mem U.one_mem]
  have : (⟨(1 : G), U.one_mem⟩ : ↥U) = 1 := rfl
  rw [this, map_one]; rfl

theorem piA_inv {u : G} (hu : u ∈ U) : piA π u⁻¹ = - piA π u := by
  have h := piA_mul (π := π) hu (U.inv_mem hu)
  rw [mul_inv_cancel, piA_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem piA_conj (hequiv : SectionEquiv U M π θ) {m u : G} (hm : m ∈ M) (hu : u ∈ U)
    (hmu : m * u * m⁻¹ ∈ U) :
    piA π (m * u * m⁻¹) = altAct (thetaA θ m) (piA π u) := by
  rw [piA_of_mem hmu, piA_of_mem hu, thetaA_of_mem hm]
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π ⟨u, hu⟩))
  have h1 := hequiv ⟨m, hm⟩ ⟨u, hu⟩ ⟨m * u * m⁻¹, hmu⟩ rfl x hx.symm
  rw [h1, ← hx, altAct_mk]

theorem perfect_hom_trivial {L : Subgroup G} (hperf : ⁅L, L⁆ = L) {A : Type*} [CommGroup A]
    (φ : ↥L →* A) (l : ↥L) : φ l = 1 := by
  have hker : ⁅L, L⁆ ≤ φ.ker.map L.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine Subgroup.mem_map.2 ⟨⁅(⟨x, hx⟩ : L), (⟨y, hy⟩ : L)⁆, ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  rw [hperf] at hker
  obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.1 (hker l.2)
  have hk' : k = l := Subtype.ext hkl
  rw [hk'] at hk
  exact hk

namespace ShortData

variable {Q L V S : Subgroup G} (D : ShortData Q L V S)
include D

theorem isMulCommutative : IsMulCommutative ↥V :=
  ⟨⟨fun a b => Subtype.ext (D.hQV a (D.hVQ a.2) b b.2)⟩⟩

theorem commutator_le : ⁅V, L⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have h1 := D.hMV l (Subgroup.mem_sup_left hl) v⁻¹ (V.inv_mem hv)
  have : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [this]
  exact V.mul_mem hv h1

theorem comm_mem_U {y : G} (hy : y ∈ Q) {l : G} (hl : l ∈ L) : ⁅l, y⁆ ∈ ⁅V, L⁆ := by
  have := D.isMulCommutative
  have h := commutator_le_commutator_of_perfect D.hperf D.hshort
  have := Subgroup.commutator_mem_commutator hl hy
  rw [Subgroup.commutator_comm] at this
  exact h this

end ShortData

structure ShortSection (Q L V S : Subgroup G) (π : ↥⁅V, L⁆ →* Multiplicative (altHeart N))
    (θ : ↥(L ⊔ S) →* Perm (Fin N)) : Prop where
  hequiv : SectionEquiv ⁅V, L⁆ (L ⊔ S) π θ
  hπker : π.ker = (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅V, L⁆
  hπ : Function.Surjective π
  hAθ : ∀ σ ∈ alternatingGroup (Fin N),
    ∃ l : ↥L, θ ⟨(l : G), Subgroup.mem_sup_left l.2⟩ = σ
  hker : ∀ m : ↥(L ⊔ S), θ m = 1 → ∀ q ∈ Q,
    ⁅(m : G), q⁆ ∈ Q ⊓ Subgroup.centralizer (L : Set G)

theorem ShortData.hker_of_hθQ {Q L V S : Subgroup G} (D : ShortData Q L V S)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hθQ : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Q) :
    ∀ m : ↥(L ⊔ S), θ m = 1 → ∀ q ∈ Q,
      ⁅(m : G), q⁆ ∈ Q ⊓ Subgroup.centralizer (L : Set G) := by
  intro m hm q hq
  have hmQ := hθQ m hm
  rw [Subgroup.mem_inf]
  refine ⟨Q.mul_mem (Q.mul_mem (Q.mul_mem hmQ hq) (Q.inv_mem hmQ)) (Q.inv_mem hq), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have := D.conj_commutator hmQ hq hl
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

@[expose] noncomputable def Fy {V L : Subgroup G} (π : ↥⁅V, L⁆ →* Multiplicative (altHeart N))
    (y l : G) : altHeart N := piA π ⁅l, y⁆

namespace ShortData

variable {Q L V S : Subgroup G} (D : ShortData Q L V S)
  {π : ↥⁅V, L⁆ →* Multiplicative (altHeart N)} {θ : ↥(L ⊔ S) →* Perm (Fin N)}
  (H : ShortSection Q L V S π θ)
include D H

theorem conj_mem_U {m : G} (hm : m ∈ L ⊔ S) {u : G} (hu : u ∈ ⁅V, L⁆) : m * u * m⁻¹ ∈ ⁅V, L⁆ :=
  conj_mem_commutator_VL (D.hMV m hm) (D.hML m hm) hu

theorem Fy_mul {y : G} (hy : y ∈ Q) {l₁ l₂ : G} (h₁ : l₁ ∈ L) (h₂ : l₂ ∈ L) :
    Fy π y (l₁ * l₂) = Fy π y l₁ + altAct (thetaA θ l₁) (Fy π y l₂) := by
  have hm₁ : l₁ ∈ L ⊔ S := Subgroup.mem_sup_left h₁
  have e : ⁅l₁ * l₂, y⁆ = (l₁ * ⁅l₂, y⁆ * l₁⁻¹) * ⁅l₁, y⁆ := by
    simp only [commutatorElement_def]; group
  have hU₂ := D.comm_mem_U hy h₂
  have hU₁ := D.comm_mem_U hy h₁
  have hc := D.conj_mem_U H hm₁ hU₂
  show piA π ⁅l₁ * l₂, y⁆ = piA π ⁅l₁, y⁆ + altAct (thetaA θ l₁) (piA π ⁅l₂, y⁆)
  rw [e, piA_mul hc hU₁, piA_conj H.hequiv hm₁ hU₂ hc]
  exact altHeart_add_comm _ _

theorem Fy_ker {y : G} (hy : y ∈ Q) {r : G} (hr : r ∈ L)
    (hθr : θ ⟨r, Subgroup.mem_sup_left hr⟩ = 1) : Fy π y r = 0 := by
  have hc : ⁅r, y⁆ ∈ Subgroup.centralizer (L : Set G) :=
    (H.hker ⟨r, Subgroup.mem_sup_left hr⟩ hθr y hy).2
  have hU := D.comm_mem_U hy hr
  have hker : (⟨⁅r, y⁆, hU⟩ : ↥⁅V, L⁆) ∈ π.ker := by
    rw [H.hπker, Subgroup.mem_subgroupOf]
    exact ⟨hU, hc⟩
  show piA π ⁅r, y⁆ = 0
  rw [piA_of_mem hU]
  have : π ⟨⁅r, y⁆, hU⟩ = 1 := hker
  rw [this]; rfl

theorem Fy_twist {y : G} (hy : y ∈ Q) {m : G} (hm : m ∈ L ⊔ S) {l : G} (hl : l ∈ L) :
    Fy π (m * y * m⁻¹) l = altAct (thetaA θ m) (Fy π y (m⁻¹ * l * m)) := by
  have hl' : m⁻¹ * l * m ∈ L := by
    have := D.hML m⁻¹ (Subgroup.inv_mem _ hm) l hl
    simpa using this
  have hU := D.comm_mem_U hy hl'
  have e : ⁅l, m * y * m⁻¹⁆ = m * ⁅m⁻¹ * l * m, y⁆ * m⁻¹ := by
    simp only [commutatorElement_def]; group
  show piA π ⁅l, m * y * m⁻¹⁆ = altAct (thetaA θ m) (piA π ⁅m⁻¹ * l * m, y⁆)
  rw [e]
  exact piA_conj H.hequiv hm hU (D.conj_mem_U H hm hU)

theorem Fy_yMul {y₁ y₂ : G} (hy₁ : y₁ ∈ Q) (hy₂ : y₂ ∈ Q) {l : G} (hl : l ∈ L) :
    Fy π (y₁ * y₂) l = Fy π y₁ l + Fy π y₂ l := by
  have hU₁ := D.comm_mem_U hy₁ hl
  have hU₂ := D.comm_mem_U hy₂ hl
  have hV₂ : ⁅l, y₂⁆ ∈ V := D.commutator_le hU₂
  have hc : y₁ * ⁅l, y₂⁆ * y₁⁻¹ = ⁅l, y₂⁆ := by
    have := D.hQV y₁ hy₁ _ hV₂
    rw [this]; group
  have e : ⁅l, y₁ * y₂⁆ = ⁅l, y₁⁆ * (y₁ * ⁅l, y₂⁆ * y₁⁻¹) := by
    simp only [commutatorElement_def]; group
  show piA π ⁅l, y₁ * y₂⁆ = piA π ⁅l, y₁⁆ + piA π ⁅l, y₂⁆
  rw [e, hc]
  exact piA_mul hU₁ hU₂

theorem Fy_one {l : G} : Fy π (1 : G) l = 0 := by
  show piA π ⁅l, (1 : G)⁆ = 0
  have : ⁅l, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
  rw [this]; exact piA_one

theorem Fy_yInv {y : G} (hy : y ∈ Q) {l : G} (hl : l ∈ L) : Fy π y⁻¹ l = - Fy π y l := by
  have h := D.Fy_yMul H (Q.inv_mem hy) hy hl
  rw [inv_mul_cancel, D.Fy_one H] at h
  exact eq_neg_of_add_eq_zero_left h.symm

end ShortData

end CFSG.HardMathSupport.RichardWeiss.Proving
