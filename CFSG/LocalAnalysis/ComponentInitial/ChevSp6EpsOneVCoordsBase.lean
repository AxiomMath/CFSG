module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneJhatComm
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneCoordsDefs
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneVCoordsExt

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.Jhat

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)
local notation "𝕊" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}

variable {G : Type} [Group G]

def vcSec (y : Fin 3 → G) (q : Fin 3 → ZMod 2) : G :=
  y 0 ^ (q 0).val * y 1 ^ (q 1).val * y 2 ^ (q 2).val

def vcW (z : G) (ν : G → 𝕊) (y : Fin 3 → G) (x : G) : Fin 3 → ZMod 2 :=
  symThreeDiag (ν (x * (vcSec y (wvec z ν x))⁻¹) : M₃)

def vcGam (z : G) (ν : G → 𝕊) (y : Fin 3 → G) (lev : GL (Fin 3) (ZMod 2) →* G)
    (g : GL (Fin 3) (ZMod 2)) : M₃ :=
  Matrix.of fun i j => vcW z ν y (lev g * y j * (lev g)⁻¹) i

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

namespace JBase

variable {τ : Multiplicative 𝕊 →* G} {lev : GL (Fin 3) (ZMod 2) →* G} {z : G} {ν : G → 𝕊}
  {A D C E Dh : Subgroup G}

theorem vc_sec_mem {y : Fin 3 → G} (hy : ∀ i, y i ∈ Dh ⊓ centralizer (E : Set G))
    (q : Fin 3 → ZMod 2) : vcSec y q ∈ Dh ⊓ centralizer (E : Set G) :=
  mul_mem (mul_mem (pow_mem (hy 0) _) (pow_mem (hy 1) _)) (pow_mem (hy 2) _)

theorem vc_sec_zero (y : Fin 3 → G) : vcSec y 0 = 1 := by
  simp [vcSec]

theorem vc_wvec_pow (h : JBase τ lev z ν A D C E Dh) (x : G) (a : ZMod 2) :
    wvec z ν (x ^ a.val) = a • wvec z ν x := by
  rcases zmod2_cases a with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, h.wvec_one, zero_smul]
  · rw [show (1 : ZMod 2).val = 1 from rfl, pow_one, one_smul]

theorem vc_wvec_sec (h : JBase τ lev z ν A D C E Dh) {y : Fin 3 → G}
    (hy : ∀ i, y i ∈ Dh ⊓ centralizer (E : Set G) ∧ wvec z ν (y i) = Pi.single i 1)
    (q : Fin 3 → ZMod 2) : wvec z ν (vcSec y q) = q := by
  have hD : ∀ i (n : ℕ), y i ^ n ∈ Dh := fun i n => pow_mem (mem_Dh_of_J (hy i).1) n
  rw [vcSec, h.wvec_mul (mul_mem (hD 0 _) (hD 1 _)) (hD 2 _), h.wvec_mul (hD 0 _) (hD 1 _),
    h.vc_wvec_pow, h.vc_wvec_pow, h.vc_wvec_pow, (hy 0).2, (hy 1).2, (hy 2).2]
  funext i
  fin_cases i <;> simp

theorem vc_conj_inv_mem_C (h : JBase τ lev z ν A D C E Dh) {t k : G} (ht : t ∈ Dh)
    (hk : k ∈ C) : t⁻¹ * k * t ∈ C := by
  have he := h.C_Dh k hk t ht
  have e : t⁻¹ * k * t = k * (k⁻¹ * t⁻¹ * k * t) := by group
  rw [e]
  exact mul_mem hk (h.E_C he)

theorem vc_pow_add (h : JBase τ lev z ν A D C E Dh) {t : G}
    (ht : t ∈ Dh ⊓ centralizer (E : Set G)) (a b : ZMod 2) :
    (t ^ (a + b).val)⁻¹ * (t ^ a.val * t ^ b.val) ∈ E := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, ZMod.val_zero, show (1 : ZMod 2).val = 1 from rfl,
      pow_zero, inv_one, one_mul, pow_one]
    exact h.sq_mem_E ht

theorem vc_shuffle (h : JBase τ lev z ν A D C E Dh) {a₀ a₁ a₂ b₀ b₁ b₂ : G}
    (ha₁ : a₁ ∈ Dh ⊓ centralizer (E : Set G)) (ha₂ : a₂ ∈ Dh ⊓ centralizer (E : Set G))
    (hb₀ : b₀ ∈ Dh ⊓ centralizer (E : Set G)) (hb₁ : b₁ ∈ Dh ⊓ centralizer (E : Set G))
    (hb₂ : b₂ ∈ Dh ⊓ centralizer (E : Set G)) :
    (a₀ * b₀ * (a₁ * b₁) * (a₂ * b₂))⁻¹ * (a₀ * a₁ * a₂ * (b₀ * b₁ * b₂)) ∈ E := by
  have k₁ := h.comm_mem_E ha₂ hb₀
  have k₂ := h.comm_mem_E ha₁ hb₀
  have k₃ := h.comm_mem_E ha₂ hb₁
  have D₂ := mem_Dh_of_J hb₂
  have D₁₂ := mul_mem (mem_Dh_of_J hb₁) D₂
  have D₂₁₂ := mul_mem (mem_Dh_of_J ha₂) D₁₂
  have e : (a₀ * b₀ * (a₁ * b₁) * (a₂ * b₂))⁻¹ * (a₀ * a₁ * a₂ * (b₀ * b₁ * b₂)) =
      (b₂⁻¹ * (a₂⁻¹ * b₁⁻¹ * a₂ * b₁) * b₂) *
      ((a₂ * (b₁ * b₂))⁻¹ * (a₁⁻¹ * b₀⁻¹ * a₁ * b₀) * (a₂ * (b₁ * b₂))) *
      ((b₁ * b₂)⁻¹ * (a₂⁻¹ * b₀⁻¹ * a₂ * b₀) * (b₁ * b₂)) := by
    group
  rw [e]
  exact mul_mem (mul_mem (h.conj_inv_mem_E D₂ k₃) (h.conj_inv_mem_E D₂₁₂ k₂))
    (h.conj_inv_mem_E D₁₂ k₁)

theorem vc_collect (h : JBase τ lev z ν A D C E Dh) {c₀ c₁ c₂ x₀ x₁ x₂ : G}
    (hc₁ : c₁ ∈ Dh) (hc₂ : c₂ ∈ Dh) (h₀ : c₀⁻¹ * x₀ ∈ E) (h₁ : c₁⁻¹ * x₁ ∈ E)
    (h₂ : c₂⁻¹ * x₂ ∈ E) : (c₀ * c₁ * c₂)⁻¹ * (x₀ * x₁ * x₂) ∈ E := by
  have e : (c₀ * c₁ * c₂)⁻¹ * (x₀ * x₁ * x₂) =
      (c₂⁻¹ * (c₁⁻¹ * (c₀⁻¹ * x₀) * c₁) * c₂) * (c₂⁻¹ * (c₁⁻¹ * x₁) * c₂) * (c₂⁻¹ * x₂) := by
    group
  rw [e]
  exact mul_mem (mul_mem (h.conj_inv_mem_E hc₂ (h.conj_inv_mem_E hc₁ h₀))
    (h.conj_inv_mem_E hc₂ h₁)) h₂

theorem vc_sec_add (h : JBase τ lev z ν A D C E Dh) {y : Fin 3 → G}
    (hy : ∀ i, y i ∈ Dh ⊓ centralizer (E : Set G)) (q q' : Fin 3 → ZMod 2) :
    (vcSec y (q + q'))⁻¹ * (vcSec y q * vcSec y q') ∈ E := by
  have hs := h.vc_shuffle (a₀ := y 0 ^ (q 0).val) (pow_mem (hy 1) (q 1).val)
    (pow_mem (hy 2) (q 2).val) (pow_mem (hy 0) (q' 0).val) (pow_mem (hy 1) (q' 1).val)
    (pow_mem (hy 2) (q' 2).val)
  have hc := h.vc_collect (c₀ := y 0 ^ (q 0 + q' 0).val)
    (pow_mem (mem_Dh_of_J (hy 1)) (q 1 + q' 1).val) (pow_mem (mem_Dh_of_J (hy 2)) (q 2 + q' 2).val)
    (h.vc_pow_add (hy 0) (q 0) (q' 0)) (h.vc_pow_add (hy 1) (q 1) (q' 1))
    (h.vc_pow_add (hy 2) (q 2) (q' 2))
  have e : (vcSec y (q + q'))⁻¹ * (vcSec y q * vcSec y q') =
      ((y 0 ^ (q 0 + q' 0).val * y 1 ^ (q 1 + q' 1).val * y 2 ^ (q 2 + q' 2).val)⁻¹ *
        (y 0 ^ (q 0).val * y 0 ^ (q' 0).val * (y 1 ^ (q 1).val * y 1 ^ (q' 1).val) *
          (y 2 ^ (q 2).val * y 2 ^ (q' 2).val))) *
      ((y 0 ^ (q 0).val * y 0 ^ (q' 0).val * (y 1 ^ (q 1).val * y 1 ^ (q' 1).val) *
          (y 2 ^ (q 2).val * y 2 ^ (q' 2).val))⁻¹ * (vcSec y q * vcSec y q')) := by
    rw [mul_assoc, mul_inv_cancel_left]
    rfl
  rw [e]
  exact mul_mem hc hs

theorem vc_mul_sec_inv_mem_C (h : JBase τ lev z ν A D C E Dh) {y : Fin 3 → G}
    (hy : ∀ i, y i ∈ Dh ⊓ centralizer (E : Set G) ∧ wvec z ν (y i) = Pi.single i 1) {x : G}
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) : x * (vcSec y (wvec z ν x))⁻¹ ∈ C :=
  h.mul_inv_mem_C hx (vc_sec_mem (fun i => (hy i).1) _) (h.vc_wvec_sec hy _).symm

theorem vc_W_mul (h : JBase τ lev z ν A D C E Dh) {y : Fin 3 → G}
    (hy : ∀ i, y i ∈ Dh ⊓ centralizer (E : Set G) ∧ wvec z ν (y i) = Pi.single i 1) {x x' : G}
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) (hx' : x' ∈ Dh ⊓ centralizer (E : Set G)) :
    vcW z ν y (x * x') = vcW z ν y x + vcW z ν y x' := by
  have hyJ : ∀ i, y i ∈ Dh ⊓ centralizer (E : Set G) := fun i => (hy i).1
  have hq : wvec z ν (x * x') = wvec z ν x + wvec z ν x' :=
    h.wvec_mul (mem_Dh_of_J hx) (mem_Dh_of_J hx')
  have hk := h.vc_mul_sec_inv_mem_C hy hx
  have hk' := h.vc_mul_sec_inv_mem_C hy hx'
  have hsD := mem_Dh_of_J (vc_sec_mem hyJ (wvec z ν x))
  have hSD := mem_Dh_of_J (vc_sec_mem hyJ (wvec z ν x + wvec z ν x'))
  have hσ := h.vc_sec_add hyJ (wvec z ν x) (wvec z ν x')
  set s := vcSec y (wvec z ν x)
  set s' := vcSec y (wvec z ν x')
  set S := vcSec y (wvec z ν x + wvec z ν x')
  have h2 : (s⁻¹)⁻¹ * (x' * s'⁻¹) * s⁻¹ ∈ C := h.vc_conj_inv_mem_C (inv_mem hsD) hk'
  have h3 : (S⁻¹)⁻¹ * (S⁻¹ * (s * s')) * S⁻¹ ∈ E := h.conj_inv_mem_E (inv_mem hSD) hσ
  have e : x * x' * S⁻¹ = (x * s⁻¹) * ((s⁻¹)⁻¹ * (x' * s'⁻¹) * s⁻¹) *
      ((S⁻¹)⁻¹ * (S⁻¹ * (s * s')) * S⁻¹) := by
    group
  unfold vcW
  rw [hq, e, h.dν_mul (mul_mem hk h2) (h.E_C h3), h.dν_mul hk h2, h.dν_E h3, add_zero,
    h.dν_conj hk' (inv_mem hsD)]

theorem vc_W_C (h : JBase τ lev z ν A D C E Dh) (y : Fin 3 → G) {c : G} (hc : c ∈ C) :
    vcW z ν y c = symThreeDiag (ν c : M₃) := by
  unfold vcW
  rw [(h.wvec_eq_zero_iff (h.C_le_Dh hc)).2 (h.C_D hc), vc_sec_zero, inv_one, mul_one]

theorem vc_W_sec (h : JBase τ lev z ν A D C E Dh) {y : Fin 3 → G}
    (hy : ∀ i, y i ∈ Dh ⊓ centralizer (E : Set G) ∧ wvec z ν (y i) = Pi.single i 1)
    (q : Fin 3 → ZMod 2) : vcW z ν y (vcSec y q) = 0 := by
  unfold vcW
  rw [h.vc_wvec_sec hy, mul_inv_cancel]
  exact h.dν_E (one_mem E)

theorem vc_W_pow (h : JBase τ lev z ν A D C E Dh) (y : Fin 3 → G) (x : G) (a : ZMod 2) :
    vcW z ν y (x ^ a.val) = a • vcW z ν y x := by
  rcases zmod2_cases a with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, zero_smul, h.vc_W_C y (one_mem C)]
    exact h.dν_E (one_mem E)
  · rw [show (1 : ZMod 2).val = 1 from rfl, pow_one, one_smul]

theorem vc_formula (h : JBase τ lev z ν A D C E Dh) {y : Fin 3 → G}
    (hy : ∀ i, y i ∈ Dh ⊓ centralizer (E : Set G) ∧ wvec z ν (y i) = Pi.single i 1)
    (g : GL (Fin 3) (ZMod 2)) {x : G} (hx : x ∈ Dh ⊓ centralizer (E : Set G)) :
    vcW z ν y (lev g * x * (lev g)⁻¹) =
      (g : M₃) *ᵥ vcW z ν y x + vcGam z ν y lev g *ᵥ wvec z ν x := by
  have hyJ : ∀ i, y i ∈ Dh ⊓ centralizer (E : Set G) := fun i => (hy i).1
  have hk := h.vc_mul_sec_inv_mem_C hy hx
  set q := wvec z ν x
  set k := x * (vcSec y q)⁻¹
  have hkJ := h.C_le_J hk
  have hY : ∀ i, lev g * y i * (lev g)⁻¹ ∈ Dh ⊓ centralizer (E : Set G) :=
    fun i => h.lev_conj_mem_J g (hyJ i)
  have hxk : x = k * vcSec y q := by simp [k]
  have hconj : lev g * x * (lev g)⁻¹ = (lev g * k * (lev g)⁻¹) *
      ((lev g * y 0 * (lev g)⁻¹) ^ (q 0).val * (lev g * y 1 * (lev g)⁻¹) ^ (q 1).val *
        (lev g * y 2 * (lev g)⁻¹) ^ (q 2).val) := by
    rw [conj_pow, conj_pow, conj_pow]
    conv_lhs => rw [hxk]
    simp only [vcSec]
    group
  have hW : vcW z ν y x = symThreeDiag (ν k : M₃) := by
    conv_lhs => rw [hxk]
    rw [h.vc_W_mul hy hkJ (vc_sec_mem hyJ q), h.vc_W_sec hy, add_zero, h.vc_W_C y hk]
  rw [hconj, h.vc_W_mul hy (h.lev_conj_mem_J g hkJ)
      (mul_mem (mul_mem (pow_mem (hY 0) _) (pow_mem (hY 1) _)) (pow_mem (hY 2) _)),
    h.vc_W_mul hy (mul_mem (pow_mem (hY 0) _) (pow_mem (hY 1) _)) (pow_mem (hY 2) _),
    h.vc_W_mul hy (pow_mem (hY 0) _) (pow_mem (hY 1) _), h.vc_W_pow, h.vc_W_pow, h.vc_W_pow,
    h.vc_W_C y (h.ν_lev g k hk).1, h.dν_lev g hk, hW]
  congr 1
  funext i
  simp [vcGam, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]

theorem vc_gam_mul (h : JBase τ lev z ν A D C E Dh) {y : Fin 3 → G}
    (hy : ∀ i, y i ∈ Dh ⊓ centralizer (E : Set G) ∧ wvec z ν (y i) = Pi.single i 1)
    (g g' : GL (Fin 3) (ZMod 2)) :
    vcGam z ν y lev (g * g') = (g : M₃) * vcGam z ν y lev g' + vcGam z ν y lev g * (g' : M₃) := by
  ext i j
  have hj := h.vc_formula hy g (h.lev_conj_mem_J g' (hy j).1)
  rw [h.wvec_lev g' (mem_Dh_of_J (hy j).1), (hy j).2, mulVec_single_one] at hj
  have e : lev (g * g') * y j * (lev (g * g'))⁻¹ =
      lev g * (lev g' * y j * (lev g')⁻¹) * (lev g)⁻¹ := by
    rw [map_mul]
    group
  simp only [vcGam, Matrix.of_apply] at hj ⊢
  rw [e, hj]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem vc_diag_section (w : Fin 3 → ZMod 2) :
    symThreeDiag ((symThreeDiagSection w : 𝕊) : M₃) = w := by
  funext k
  simp [symThreeDiag, symThreeDiagSection]

theorem vc_exists (h : JBase τ lev z ν A D C E Dh) :
    ∃ cV, EpsOneVCoords (Dh ⊓ centralizer (E : Set G)) E C z lev
      (fun c => symThreeDiag (ν c : M₃)) cV := by
  choose y hy using fun i : Fin 3 => h.exists_J_wvec (Pi.single i 1)
  obtain ⟨m, hm⟩ := ChevSp6EpsOne.ExtOne.exists_coboundary (vcGam z ν y lev) (h.vc_gam_mul hy)
  have hC0 : ∀ {c : G}, c ∈ C → wvec z ν c = 0 := fun hc =>
    (h.wvec_eq_zero_iff (h.C_le_Dh hc)).2 (h.C_D hc)
  refine ⟨fun x => (vcW z ν y x + m *ᵥ wvec z ν x, wvec z ν x), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx'
    rw [Prod.mk_add_mk, h.vc_W_mul hy hx hx', h.wvec_mul (mem_Dh_of_J hx) (mem_Dh_of_J hx'),
      mulVec_add, add_add_add_comm]
  · intro x hx
    constructor
    · intro h0
      have h1 : wvec z ν x = 0 := congrArg Prod.snd h0
      have h2 : vcW z ν y x + m *ᵥ wvec z ν x = 0 := congrArg Prod.fst h0
      have hc := h.mem_C_of_J hx h1
      rw [h1, mulVec_zero, add_zero, h.vc_W_C y hc] at h2
      exact (h.ν_E x hc).1 h2
    · intro he
      have hc := h.E_C he
      simp only [hC0 hc, mulVec_zero, add_zero, h.vc_W_C y hc, h.dν_E he]
      rfl
  · rintro ⟨p₁, p₂⟩
    obtain ⟨x, hx, hxp⟩ := h.exists_J_wvec p₂
    obtain ⟨c, hc, hcv⟩ := h.ν_surj (symThreeDiagSection (p₁ + (vcW z ν y x + m *ᵥ p₂)))
    refine ⟨c * x, mul_mem (h.C_le_J hc) hx, ?_⟩
    rw [h.vc_W_mul hy (h.C_le_J hc) hx, h.wvec_mul (h.C_le_Dh hc) (mem_Dh_of_J hx), hC0 hc,
      zero_add, hxp, h.vc_W_C y hc, hcv, vc_diag_section, add_assoc, add_assoc, vec_add_self,
      add_zero]
  · intro c hc
    simp only [hC0 hc, mulVec_zero, add_zero, h.vc_W_C y hc]
  · intro x hx
    have ht := h.zt_C x (mem_Dh_of_J hx)
    have e1 : z * x * z⁻¹ = z⁻¹ * x * z := by rw [h.z_inv]
    have e : z * x * z⁻¹ = x * (z⁻¹ * (x⁻¹ * z * x))⁻¹ := by
      rw [e1]
      group
    have hW : vcW z ν y (z * x * z⁻¹) = vcW z ν y x + wvec z ν x := by
      rw [e, h.vc_W_mul hy hx (h.C_le_J (inv_mem ht)), h.vc_W_C y (inv_mem ht), h.ν_inv ht,
        wvec_def]
    have hw : wvec z ν (z * x * z⁻¹) = wvec z ν x := by
      rw [e, h.wvec_mul (mem_Dh_of_J hx) (h.C_le_Dh (inv_mem ht)), hC0 (inv_mem ht), add_zero]
    simp only [hW, hw]
    rw [add_right_comm]
  · intro g
    rw [mem_normalizer_iff]
    intro n
    constructor
    · exact h.lev_conj_mem_J g
    · intro hn
      have h1 := h.lev_conj_mem_J g⁻¹ hn
      have e : (lev g)⁻¹ * (lev g * n * (lev g)⁻¹) * ((lev g)⁻¹)⁻¹ = n := by group
      rwa [map_inv, e] at h1
  · intro g x hx
    simp only
    rw [h.vc_formula hy g hx, h.wvec_lev g (mem_Dh_of_J hx), hm g, add_mulVec, mulVec_mulVec,
      mulVec_add, mulVec_mulVec]
    simp only [add_assoc, vec_add_self, add_zero]

end JBase

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.Jhat
