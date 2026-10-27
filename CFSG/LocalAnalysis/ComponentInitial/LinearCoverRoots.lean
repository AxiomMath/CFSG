module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourSplitting
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Subgroup Matrix LinearFlag LinearFieldFour CFSG.ComponentClassification
open scoped commutatorElement

section Commutators

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left_eq (a b c : G) : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_right_eq (a b c : G) : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_left_of_commute {a b c : G} (h₁ : a * ⁅b, c⁆ = ⁅b, c⁆ * a)
    (h₂ : ⁅a, c⁆ * ⁅b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆) : ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left_eq, h₁, mul_inv_cancel_right, h₂]

theorem commutatorElement_mul_right_of_commute {a b c : G} (h : b * ⁅a, c⁆ = ⁅a, c⁆ * b) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq, h, mul_inv_cancel_right]

theorem commutatorElement_commutatorElement_eq_sq {x y : G} (hx : x * x * y = y * (x * x))
    (hy : y * y * x = x * (y * y)) :
    ⁅⁅x, y⁆, x⁆ = ⁅x, y⁆ ^ 2 ∧ ⁅⁅x, y⁆, y⁆ = ⁅x, y⁆ ^ 2 := by
  have h1 : x * ⁅x, y⁆ * x⁻¹ = ⁅x, y⁆⁻¹ := by
    have h := commutatorElement_mul_left_eq x x y
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hx] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have h2 : y * ⁅x, y⁆ * y⁻¹ = ⁅x, y⁆⁻¹ := by
    have h := commutatorElement_mul_right_eq x y y
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hy.symm] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  constructor
  · calc ⁅⁅x, y⁆, x⁆ = ⁅x, y⁆ * (x * ⁅x, y⁆ * x⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = ⁅x, y⁆ ^ 2 := by rw [h1, inv_inv, sq]
  · calc ⁅⁅x, y⁆, y⁆ = ⁅x, y⁆ * (y * ⁅x, y⁆ * y⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = ⁅x, y⁆ ^ 2 := by rw [h2, inv_inv, sq]

theorem commutatorElement_mem_of_mem_closure {X : Set G} {R : Subgroup G}
    (hnorm : ∀ g ∈ closure X, ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (hX : ∀ s ∈ X, ∀ s' ∈ X, ⁅s, s'⁆ ∈ R) {g h : G} (hg : g ∈ closure X) (hh : h ∈ closure X) :
    ⁅g, h⁆ ∈ R := by
  have hleft : ∀ s ∈ X, ∀ h ∈ closure X, ⁅s, h⁆ ∈ R := by
    intro s hs h hh
    induction hh using Subgroup.closure_induction with
    | mem t ht => exact hX s hs t ht
    | one => rw [commutatorElement_one_right]; exact R.one_mem
    | mul t₁ t₂ ht₁ ht₂ ih₁ ih₂ =>
      rw [commutatorElement_mul_right_eq]
      exact R.mul_mem ih₁ (hnorm t₁ ht₁ _ ih₂)
    | inv t ht ih =>
      have h' : ⁅s, t⁻¹⁆ = t⁻¹ * ⁅s, t⁆⁻¹ * t⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [h']
      exact hnorm t⁻¹ (inv_mem ht) _ (R.inv_mem ih)
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact hleft s hs h hh
  | one => rw [commutatorElement_one_left]; exact R.one_mem
  | mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
    rw [commutatorElement_mul_left_eq]
    exact R.mul_mem (hnorm g₁ hg₁ _ ih₂) ih₁
  | inv t ht ih =>
    have h' : ⁅t⁻¹, h⁆ = t⁻¹ * ⁅t, h⁆⁻¹ * t⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h']
    exact hnorm t⁻¹ (inv_mem ht) _ (R.inv_mem ih)

end Commutators

section TwoPart

variable {E : Type*} [Group E]

@[expose] def twoPart (N : Subgroup E) (hN : N ≤ center E) : Subgroup E where
  carrier := {z | z ∈ N ∧ ∃ n : ℕ, z ^ 2 ^ n = 1}
  one_mem' := ⟨N.one_mem, 0, by rw [one_pow]⟩
  mul_mem' := by
    rintro a b ⟨ha, m, hm⟩ ⟨hb, n, hn⟩
    refine ⟨N.mul_mem ha hb, m + n, ?_⟩
    have hab : Commute a b := (mem_center_iff.mp (hN hb) a)
    rw [hab.mul_pow, pow_add, pow_mul, hm, one_pow, one_mul, mul_comm, pow_mul, hn, one_pow]
  inv_mem' := by
    rintro a ⟨ha, n, hn⟩
    exact ⟨N.inv_mem ha, n, by rw [inv_pow, hn, inv_one]⟩

variable {N : Subgroup E} {hN : N ≤ center E}

theorem mem_twoPart {z : E} : z ∈ twoPart N hN ↔ z ∈ N ∧ ∃ n : ℕ, z ^ 2 ^ n = 1 :=
  Iff.rfl

theorem twoPart_le : twoPart N hN ≤ N := fun _ hz => hz.1

theorem twoPart_le_center : twoPart N hN ≤ center E := twoPart_le.trans hN

theorem isPGroup_twoPart : IsPGroup 2 (twoPart N hN) := fun z => by
  obtain ⟨n, hn⟩ := z.2.2
  exact ⟨n, Subtype.ext (by rw [SubgroupClass.coe_pow, hn]; rfl)⟩

theorem exists_sylow_map_eq_twoPart_le {G : Type*} [Group G] [Finite E] [Group.IsPerfect E]
    (η : E →* G) (hη : Function.Surjective η) (hker : η.ker ≤ center E) (S : Sylow 2 G) :
    ∃ P : Sylow 2 E, (P : Subgroup E).map η = S ∧
      ∀ z ∈ η.ker, (∃ n : ℕ, z ^ 2 ^ n = 1) → z ∈ ⁅(P : Subgroup E), (P : Subgroup E)⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hη 2 S
  refine ⟨P, by rw [← Sylow.coe_mapSurjective hη P, hP], fun z hz hn => ?_⟩
  have h := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P
    (twoPart η.ker hker) twoPart_le_center isPGroup_twoPart
  rw [map_subtype_commutator] at h
  exact h ⟨hz, hn⟩

end TwoPart

structure HeisenbergRoots (K G : Type*) [Field K] [Group G] where
  x : K → G
  y : K → G
  w : K → G
  x_add : ∀ a b, x (a + b) = x a * x b
  y_add : ∀ a b, y (a + b) = y a * y b
  w_add : ∀ a b, w (a + b) = w a * w b
  w_mul_x : ∀ c a, w c * x a = x a * w c
  w_mul_y : ∀ c b, w c * y b = y b * w c
  x_mul_y : ∀ a b, x a * y b = w (a * b) * y b * x a
  gx : G
  gy : G
  gx_conj : ∀ a, gx⁻¹ * x a * gx = w a
  gy_conj : ∀ b, gy⁻¹ * y b * gy = w b
  S : Subgroup G
  x_mem : ∀ a, x a ∈ S
  y_mem : ∀ b, y b ∈ S
  w_mem : ∀ c, w c ∈ S
  mem_S : ∀ s ∈ S, ∃ a b c, s = w c * x a * y b

namespace HeisenbergRoots

variable {K G : Type*} [Field K] [Group G] (R : HeisenbergRoots K G)

theorem x_zero : R.x 0 = 1 := by
  have h := R.x_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem y_zero : R.y 0 = 1 := by
  have h := R.y_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem w_zero : R.w 0 = 1 := by
  have h := R.w_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem w_comm (c c' : K) : R.w c * R.w c' = R.w c' * R.w c := by
  rw [← R.w_add, ← R.w_add, add_comm]

theorem commutatorElement_x_y (a b : K) : ⁅R.x a, R.y b⁆ = R.w (a * b) := by
  rw [commutatorElement_def, R.x_mul_y]
  group

theorem commutatorElement_w_x (c a : K) : ⁅R.w c, R.x a⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (R.w_mul_x c a)

theorem commutatorElement_w_y (c b : K) : ⁅R.w c, R.y b⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (R.w_mul_y c b)

variable {E : Type*} [Group E] (η : E →* G) (hker : ∀ z, η z = 1 → z ∈ center E)
include hker

theorem commutatorElement_eq_of_map_eq {x x' y y' : E} (hx : η x = η x') (hy : η y = η y') :
    ⁅x, y⁆ = ⁅x', y'⁆ := by
  have hcx : x⁻¹ * x' ∈ center E := hker _ (by rw [map_mul, map_inv, hx, inv_mul_cancel])
  have hcy : y⁻¹ * y' ∈ center E := hker _ (by rw [map_mul, map_inv, hy, inv_mul_cancel])
  calc ⁅x, y⁆ = ⁅x * (x⁻¹ * x'), y * (y⁻¹ * y')⁆ := by
        rw [CentralExtensions.commutator_mul_center_left _ _ _ hcx,
          CentralExtensions.commutator_mul_center_right _ _ _ hcy]
    _ = ⁅x', y'⁆ := by rw [mul_inv_cancel_left, mul_inv_cancel_left]

omit hker in
theorem commutatorElement_mem_center_of_w_x (hker : ∀ z, η z = 1 → z ∈ center E) {z x₀ : E}
    {c a : K} (hz : η z = R.w c) (hx : η x₀ = R.x a) : ⁅z, x₀⁆ ∈ center E :=
  hker _ (by rw [map_commutatorElement, hz, hx, R.commutatorElement_w_x])

omit hker in
theorem commutatorElement_mem_center_of_w_y (hker : ∀ z, η z = 1 → z ∈ center E) {z y₀ : E}
    {c b : K} (hz : η z = R.w c) (hy : η y₀ = R.y b) : ⁅z, y₀⁆ ∈ center E :=
  hker _ (by rw [map_commutatorElement, hz, hy, R.commutatorElement_w_y])

variable (hη : Function.Surjective η)
include hη

theorem preimage_w_comm (z₁ z₂ : E) (h₁ : ∃ c, η z₁ = R.w c) (h₂ : ∃ c, η z₂ = R.w c) :
    z₁ * z₂ = z₂ * z₁ := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  obtain ⟨x₀, hx₀⟩ := hη (R.x c₂)
  obtain ⟨y₀, hy₀⟩ := hη (R.y 1)
  have hz : η (⁅x₀, y₀⁆⁻¹ * z₂) = 1 := by
    rw [map_mul, map_inv, map_commutatorElement, hx₀, hy₀, R.commutatorElement_x_y, mul_one, h₂,
      inv_mul_cancel]
  have hζ := hker _ hz
  have h1 := commute_commutatorElement_of_mem_center
    (R.commutatorElement_mem_center_of_w_x η hker h₁ hx₀)
    (R.commutatorElement_mem_center_of_w_y η hker h₁ hy₀)
  calc z₁ * z₂ = z₁ * ⁅x₀, y₀⁆ * (⁅x₀, y₀⁆⁻¹ * z₂) := by group
    _ = ⁅x₀, y₀⁆ * (z₁ * (⁅x₀, y₀⁆⁻¹ * z₂)) := by rw [h1, mul_assoc]
    _ = ⁅x₀, y₀⁆ * ((⁅x₀, y₀⁆⁻¹ * z₂) * z₁) := by rw [mem_center_iff.mp hζ z₁]
    _ = z₂ * z₁ := by group

theorem preimage_x_comm (z₁ z₂ : E) (h₁ : ∃ a, η z₁ = R.x a) (h₂ : ∃ a, η z₂ = R.x a) :
    z₁ * z₂ = z₂ * z₁ := by
  obtain ⟨g, hg⟩ := hη R.gx
  obtain ⟨a₁, ha₁⟩ := h₁
  obtain ⟨a₂, ha₂⟩ := h₂
  have h := R.preimage_w_comm η hker hη (g⁻¹ * z₁ * g) (g⁻¹ * z₂ * g)
    ⟨a₁, by rw [map_mul, map_mul, map_inv, ha₁, hg, R.gx_conj]⟩
    ⟨a₂, by rw [map_mul, map_mul, map_inv, ha₂, hg, R.gx_conj]⟩
  have h' : g⁻¹ * (z₁ * z₂) * g = g⁻¹ * (z₂ * z₁) * g := by
    calc g⁻¹ * (z₁ * z₂) * g = (g⁻¹ * z₁ * g) * (g⁻¹ * z₂ * g) := by group
      _ = (g⁻¹ * z₂ * g) * (g⁻¹ * z₁ * g) := h
      _ = g⁻¹ * (z₂ * z₁) * g := by group
  simpa using h'

theorem preimage_y_comm (z₁ z₂ : E) (h₁ : ∃ b, η z₁ = R.y b) (h₂ : ∃ b, η z₂ = R.y b) :
    z₁ * z₂ = z₂ * z₁ := by
  obtain ⟨g, hg⟩ := hη R.gy
  obtain ⟨b₁, hb₁⟩ := h₁
  obtain ⟨b₂, hb₂⟩ := h₂
  have h := R.preimage_w_comm η hker hη (g⁻¹ * z₁ * g) (g⁻¹ * z₂ * g)
    ⟨b₁, by rw [map_mul, map_mul, map_inv, hb₁, hg, R.gy_conj]⟩
    ⟨b₂, by rw [map_mul, map_mul, map_inv, hb₂, hg, R.gy_conj]⟩
  have h' : g⁻¹ * (z₁ * z₂) * g = g⁻¹ * (z₂ * z₁) * g := by
    calc g⁻¹ * (z₁ * z₂) * g = (g⁻¹ * z₁ * g) * (g⁻¹ * z₂ * g) := by group
      _ = (g⁻¹ * z₂ * g) * (g⁻¹ * z₁ * g) := h
      _ = g⁻¹ * (z₂ * z₁) * g := by group
  simpa using h'

omit hker hη in
theorem comap_S_le_closure (lx ly lw : K → E) (hlx : ∀ a, η (lx a) = R.x a)
    (hly : ∀ b, η (ly b) = R.y b) (hlw : ∀ c, η (lw c) = R.w c) :
    R.S.comap η ≤ closure ((η.ker : Set E) ∪ Set.range lx ∪ Set.range ly ∪ Set.range lw) := by
  intro t ht
  obtain ⟨a, b, c, hs⟩ := R.mem_S (η t) ht
  have hζ : (lw c * lx a * ly b)⁻¹ * t ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hlx, hly, hlw, hs, inv_mul_cancel]
  have ht' : t = lw c * lx a * ly b * ((lw c * lx a * ly b)⁻¹ * t) := by group
  rw [ht']
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
  · exact subset_closure (Or.inr ⟨c, rfl⟩)
  · exact subset_closure (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩)))
  · exact subset_closure (Or.inl (Or.inr ⟨b, rfl⟩))
  · exact subset_closure (Or.inl (Or.inl (Or.inl hζ)))

end HeisenbergRoots

section Instances

variable {K : Type*} [Field K]

theorem eq_wMat_mul_xMat_mul_yMat {u : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) :
    u = wMat ((u : Matrix (Fin 3) (Fin 3) K) 0 2 -
        (u : Matrix (Fin 3) (Fin 3) K) 0 1 * (u : Matrix (Fin 3) (Fin 3) K) 1 2) *
      xMat ((u : Matrix (Fin 3) (Fin 3) K) 0 1) * yMat ((u : Matrix (Fin 3) (Fin 3) K) 1 2) := by
  obtain ⟨hl, hd⟩ := mem_unitriangular.mp hu
  apply Subtype.ext
  change (u : Matrix (Fin 3) (Fin 3) K) = wM _ * xM _ * yM _
  simp only [wM, xM, yM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hd, hl 1 0 (by decide), hl 2 0 (by decide),
    hl 2 1 (by decide)]

theorem xMat_mem_unitriangular (a : K) : xMat a ∈ unitriangular 3 K := by
  refine mem_unitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
  · change xM a i j = 0
    fin_cases i <;> fin_cases j <;> simp_all [xM]
  · change xM a i i = 1
    fin_cases i <;> simp [xM]

theorem yMat_mem_unitriangular (b : K) : yMat b ∈ unitriangular 3 K := by
  refine mem_unitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
  · change yM b i j = 0
    fin_cases i <;> fin_cases j <;> simp_all [yM]
  · change yM b i i = 1
    fin_cases i <;> simp [yM]

theorem wMat_mem_unitriangular (c : K) : wMat c ∈ unitriangular 3 K := by
  refine mem_unitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
  · change wM c i j = 0
    fin_cases i <;> fin_cases j <;> simp_all [wM]
  · change wM c i i = 1
    fin_cases i <;> simp [wM]

variable [CharP K 2]

@[expose] def slRoots : HeisenbergRoots K (SpecialLinearGroup (Fin 3) K) where
  x := xMat
  y := yMat
  w := wMat
  x_add := xMat_add
  y_add := yMat_add
  w_add := wMat_add
  w_mul_x := wMat_mul_xMat
  w_mul_y := wMat_mul_yMat
  x_mul_y := xMat_mul_yMat
  gx := s₂₃Mat
  gy := s₁₂Mat
  gx_conj a := by
    rw [inv_eq_of_mul_eq_one_right s₂₃Mat_mul_self, s₂₃Mat_mul_xMat_mul_s₂₃Mat]
  gy_conj b := by
    rw [inv_eq_of_mul_eq_one_right s₁₂Mat_mul_self, s₁₂Mat_mul_yMat_mul_s₁₂Mat]
  S := unitriangular 3 K
  x_mem := xMat_mem_unitriangular
  y_mem := yMat_mem_unitriangular
  w_mem := wMat_mem_unitriangular
  mem_S s hs := ⟨_, _, _, eq_wMat_mul_xMat_mul_yMat hs⟩

@[expose] def projRoots : HeisenbergRoots K (projectiveSL 3 K) where
  x := xP
  y := yP
  w := wP
  x_add := xP_add
  y_add := yP_add
  w_add := wP_add
  w_mul_x := wP_mul_xP
  w_mul_y := wP_mul_yP
  x_mul_y a b := by
    rw [xP, yP, wP, ← map_mul, ← map_mul, ← map_mul, xMat_mul_yMat]
  gx := s₂₃P
  gy := s₁₂P
  gx_conj := s₂₃P_conj_xP
  gy_conj := s₁₂P_conj_yP
  S := projUnitriangular 3 K
  x_mem a := mem_map_of_mem _ (xMat_mem_unitriangular a)
  y_mem b := mem_map_of_mem _ (yMat_mem_unitriangular b)
  w_mem c := mem_map_of_mem _ (wMat_mem_unitriangular c)
  mem_S s hs := by
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hs
    refine ⟨(u : Matrix (Fin 3) (Fin 3) K) 0 1, (u : Matrix (Fin 3) (Fin 3) K) 1 2,
      (u : Matrix (Fin 3) (Fin 3) K) 0 2 -
        (u : Matrix (Fin 3) (Fin 3) K) 0 1 * (u : Matrix (Fin 3) (Fin 3) K) 1 2, ?_⟩
    conv_lhs => rw [eq_wMat_mul_xMat_mul_yMat hu]
    rw [map_mul, map_mul]
    rfl

@[simp] theorem slRoots_x : (slRoots : HeisenbergRoots K _).x = xMat := rfl
@[simp] theorem slRoots_y : (slRoots : HeisenbergRoots K _).y = yMat := rfl
@[simp] theorem slRoots_w : (slRoots : HeisenbergRoots K _).w = wMat := rfl
@[simp] theorem slRoots_S : (slRoots : HeisenbergRoots K _).S = unitriangular 3 K := rfl
@[simp] theorem projRoots_x : (projRoots : HeisenbergRoots K _).x = xP := rfl
@[simp] theorem projRoots_y : (projRoots : HeisenbergRoots K _).y = yP := rfl
@[simp] theorem projRoots_w : (projRoots : HeisenbergRoots K _).w = wP := rfl
@[simp] theorem projRoots_S : (projRoots : HeisenbergRoots K _).S = projUnitriangular 3 K := rfl

end Instances

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial
