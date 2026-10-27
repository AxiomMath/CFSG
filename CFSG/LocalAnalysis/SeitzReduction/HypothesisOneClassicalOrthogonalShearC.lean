module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonalShearCSupply
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Tactic.Module
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.SeitzReduction

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

namespace OrthogonalShearC

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

local macro "char_two_module" : tactic =>
  `(tactic| (match_scalars <;> (try simp only [CharTwo.neg_eq, CharTwo.sub_eq_add]) <;>
    (try ring_nf) <;> (try reduce_mod_char!) <;> (try ring_nf)))

local macro "char_two_ring" : tactic =>
  `(tactic| ((try simp only [CharTwo.neg_eq, CharTwo.sub_eq_add]) <;>
    (try ring_nf) <;> (try reduce_mod_char!) <;> (try ring_nf)))

abbrev Comm {F : Type*} [FunLike F V V] (T : F) (g : V ≃ₗ[K] V) : Prop :=
  ∀ v, T (g v) = g (T v)

theorem Comm.mul {F : Type*} [FunLike F V V] {T : F} {g g' : V ≃ₗ[K] V} (h : Comm T g)
    (h' : Comm T g') : Comm T (g * g') := fun v => by
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h, h']

theorem Comm.inv {F : Type*} [FunLike F V V] {T : F} {g : V ≃ₗ[K] V} (h : Comm T g) :
    Comm T g⁻¹ := fun v => by
  have e := h (g⁻¹ v)
  rw [LinearEquiv.apply_inv_apply'] at e
  rw [e, LinearEquiv.inv_apply_apply']

section Involution

variable {Q : QuadraticForm K V} {s : V ≃ₗ[K] V}

theorem polar_sub_left_eq (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hs2 : ∀ v, s (s v) = v) (x y : V) : polar Q (s x - x) y = polar Q x (s y - y) := by
  have h : polar Q (s x) y = polar Q x (s y) := by
    rw [← polar_map_of_mem hs x (s y), hs2]
  rw [polar_sub_left, polar_sub_right, h]

variable [CharP K 2]

theorem sub_sub_eq_zero (hs2 : ∀ v, s (s v) = v) (x : V) : s (s x - x) - (s x - x) = 0 :=
  calc s (s x - x) - (s x - x) = (2 : K) • (x - s x) := by
        rw [map_sub, hs2]
        module
    _ = 0 := by rw [CharTwo.two_eq_zero, zero_smul]

theorem map_sub_eq_polar (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (x : V) :
    Q (s x - x) = polar Q x (s x - x) := by
  rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, map_of_mem hs, polar_neg_right,
    polar_add_right, polar_neg_right, polar_self_charTwo, polar_comm]
  char_two_ring

end Involution

section Setting

variable [CharP K 2] {Q : QuadraticForm K V} {s : V ≃ₗ[K] V} {W L : Submodule K V}

omit [CharP K 2] in
theorem mem_L_iff (hQ : (polarBilin Q).Nondegenerate)
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs2 : ∀ v, s (s v) = v)
    (hW : ∀ v, v ∈ W ↔ ∃ x, s x - x = v) (hL : ∀ v, v ∈ L ↔ s v = v) (v : V) :
    v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0 := by
  rw [hL]
  constructor
  · rintro hv w hw
    obtain ⟨x, rfl⟩ := (hW w).1 hw
    rw [polar_sub_left_eq hs hs2, hv, sub_self, polar_zero_right]
  · intro h
    have h0 : s v - v = 0 := hQ.1 _ fun y => by
      change polar Q (s v - v) y = 0
      rw [polar_comm, ← polar_sub_left_eq hs hs2]
      exact h _ ((hW _).2 ⟨y, rfl⟩)
    exact sub_eq_zero.1 h0

theorem W_le_L (hs2 : ∀ v, s (s v) = v) (hW : ∀ v, v ∈ W ↔ ∃ x, s x - x = v)
    (hL : ∀ v, v ∈ L ↔ s v = v) : W ≤ L := fun v hv => by
  obtain ⟨x, rfl⟩ := (hW v).1 hv
  exact (hL _).2 (sub_eq_zero.1 (sub_sub_eq_zero hs2 x))

theorem W_iso (hQ : (polarBilin Q).Nondegenerate)
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs2 : ∀ v, s (s v) = v)
    (hW : ∀ v, v ∈ W ↔ ∃ x, s x - x = v) (hL : ∀ v, v ∈ L ↔ s v = v) :
    ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0 := fun x hx y hy =>
  (mem_L_iff hQ hs hs2 hW hL y).1 (W_le_L hs2 hW hL hy) x hx

theorem mem_W_iff [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs2 : ∀ v, s (s v) = v)
    (hW : ∀ v, v ∈ W ↔ ∃ x, s x - x = v) (hL : ∀ v, v ∈ L ↔ s v = v) (v : V) :
    v ∈ W ↔ ∀ l ∈ L, polar Q l v = 0 :=
  ShearRigidity.mem_iff_forall_of_perp (B := polarBilin Q) hQ.2 (polarBilin_isAlt Q)
    (mem_L_iff hQ hs hs2 hW hL) v

theorem exists_adjust [Finite K] (hLperp : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0) {h₀ : V}
    (hh₀ : h₀ ∈ W) (hQh₀ : Q h₀ ≠ 0) {p : V} (hp : p ∈ L) (c : K) :
    ∃ t : K, Q (p + t • h₀) = c := by
  obtain ⟨t, ht⟩ := isSquare_of_charTwo' ((c - Q p) / Q h₀)
  refine ⟨t, ?_⟩
  have hph : polar Q p h₀ = 0 := by
    rw [polar_comm]
    exact (hLperp p).1 hp h₀ hh₀
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right, hph, smul_zero, add_zero,
    smul_eq_mul, ← ht, div_mul_cancel₀ _ hQh₀]
  ring

theorem exists_rotPair [Finite K] (hWL : W ≤ L)
    (hLperp : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0)
    (hWperp : ∀ v, v ∈ W ↔ ∀ l ∈ L, polar Q l v = 0) {h₀ : V} (hh₀ : h₀ ∈ W) (hQh₀ : Q h₀ ≠ 0)
    {p : V} (hp : p ∈ L) (hpW : p ∉ W) (hQp : Q p = 1) :
    ∃ p₂ ∈ L, IsRotPair Q p p₂ := by
  obtain ⟨l, hl, hlp⟩ : ∃ l ∈ L, polar Q l p ≠ 0 := by
    by_contra! h
    exact hpW ((hWperp p).2 h)
  have hpl : polar Q p l ≠ 0 := by rwa [polar_comm]
  obtain ⟨y₁, hy₁L, hpy₁⟩ : ∃ y₁ ∈ L, polar Q p y₁ = 1 :=
    ⟨(polar Q p l)⁻¹ • l, L.smul_mem _ hl, by
      rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hpl]⟩
  obtain ⟨t, ht⟩ := exists_adjust hLperp hh₀ hQh₀ hy₁L 1
  have hph₀ : polar Q p h₀ = 0 := by
    rw [polar_comm]
    exact (hLperp p).1 hp h₀ hh₀
  refine ⟨y₁ + t • h₀, L.add_mem hy₁L (L.smul_mem _ (hWL hh₀)), hQp, ht, ?_⟩
  rw [polar_add_right, polar_smul_right, hph₀, smul_zero, add_zero, hpy₁]

end Setting

section Commute

variable {Q : QuadraticForm K V} {s : V ≃ₗ[K] V} {T : V ≃+ V}

theorem conj_mul_comm {E ρ : V ≃ₗ[K] V} (hE : E * s = s * E) (hρ : ρ * s = s * ρ) :
    E * ρ * E⁻¹ * s = s * (E * ρ * E⁻¹) := by
  have hc : Commute (E * ρ * E⁻¹) s :=
    ((Commute.mul_left hE hρ).mul_left (Commute.inv_left hE))
  exact hc

theorem comm_of_pow_three
    (hodd : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * s = s * g → Odd (orderOf g) →
      ∀ v, T (g v) = g (T v))
    {E ρ : V ≃ₗ[K] V} (hEQ : E ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hE : E * s = s * E)
    (hρQ : ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hρ : ρ * s = s * ρ) (hρ3 : ρ ^ 3 = 1) :
    Comm T (E * ρ * E⁻¹ * ρ⁻¹) := by
  have hodd3 : Odd (orderOf ρ) := odd_orderOf_of_pow_three hρ3
  have h1 : Comm T (E * ρ * E⁻¹) := hodd _ (mul_mem (mul_mem hEQ hρQ) (inv_mem hEQ))
    (conj_mul_comm hE hρ) (by
      rw [show E * ρ * E⁻¹ = MulAut.conj E ρ from rfl, MulEquiv.orderOf_eq]
      exact hodd3)
  have h2 : Comm T ρ := hodd ρ hρQ hρ hodd3
  exact h1.mul h2.inv

end Commute

section Shears

variable [Finite K] [CharP K 2] {Q : QuadraticForm K V} {s : V ≃ₗ[K] V}
  {W L : Submodule K V} {T : V ≃+ V}

theorem exists_comm_eichler (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hWL : W ≤ L) (hL : ∀ v, v ∈ L ↔ s v = v)
    (hLperp : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0)
    (hWperp : ∀ v, v ∈ W ↔ ∀ l ∈ L, polar Q l v = 0) {h₀ : V} (hh₀ : h₀ ∈ W) (hQh₀ : Q h₀ ≠ 0)
    (hodd : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * s = s * g → Odd (orderOf g) →
      ∀ v, T (g v) = g (T v))
    {w : V} (hw : w ∈ W) {x : V} (hx : x ∈ L) :
    ∃ u' ∈ L, x - u' ∈ W ∧ Comm T (eichler Q w u') := by
  by_cases hxW : x ∈ W
  · refine ⟨0, L.zero_mem, by rwa [sub_zero], ?_⟩
    rw [eichler_zero_right]
    intro v
    rfl
  obtain ⟨t, ht⟩ := exists_adjust hLperp hh₀ hQh₀ hx 1
  have hp₁L : x + t • h₀ ∈ L := L.add_mem hx (L.smul_mem _ (hWL hh₀))
  have hp₁W : x + t • h₀ ∉ W := fun h => hxW (by
    have := W.sub_mem h (W.smul_mem t hh₀)
    rwa [add_sub_cancel_right] at this)
  obtain ⟨p₂, hp₂L, hrot⟩ := exists_rotPair hWL hLperp hWperp hh₀ hQh₀ hp₁L hp₁W ht
  have hwL : w ∈ L := hWL hw
  have hsw : s w = w := (hL w).1 hwL
  have hwp₁ : polar Q w (x + t • h₀) = 0 := (hLperp _).1 hp₁L w hw
  have hwp₂ : polar Q w p₂ = 0 := (hLperp _).1 hp₂L w hw
  have hρw : rot hrot w = w := by
    rw [rot_apply]
    exact rotLin_apply_of_polar_eq_zero hwp₁ hwp₂
  have hρs : rot hrot * s = s * rot hrot :=
    rot_mul_comm hs hrot ((hL _).1 hp₁L) ((hL _).1 hp₂L)
  have hc := comm_of_pow_three hodd (eichler_mem_orthogonalGroup Q w p₂)
    (eichler_mul_comm hs hsw ((hL _).1 hp₂L)) (rot_mem_orthogonalGroup hrot) hρs
    (rot_pow_three hrot)
  rw [eichler_commutator (rot_mem_orthogonalGroup hrot) hwp₂ hρw, rot_apply,
    rotLin_apply_right hrot, sub_add_cancel_right] at hc
  refine ⟨-(x + t • h₀), L.neg_mem hp₁L, ?_, hc⟩
  rw [sub_neg_eq_add, ← add_assoc, ShearRigidity.add_self_eq_zero K x, zero_add]
  exact W.smul_mem t hh₀

theorem exists_shear (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hWL : W ≤ L) (hL : ∀ v, v ∈ L ↔ s v = v)
    (hLperp : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0)
    (hWperp : ∀ v, v ∈ W ↔ ∀ l ∈ L, polar Q l v = 0) {h₀ : V} (hh₀ : h₀ ∈ W) (hQh₀ : Q h₀ ≠ 0)
    (hodd : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * s = s * g → Odd (orderOf g) →
      ∀ v, T (g v) = g (T v))
    {w : V} (hw : w ∈ W) (hQw : Q w = 0) {u : V} (hu : u ∈ L) :
    ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧ (∀ v ∈ L, g v = v + polar Q v u • w) ∧
      ∀ v, g v - v - polar Q v w • u ∈ W := by
  obtain ⟨u', hu'L, huu', hc⟩ :=
    exists_comm_eichler hs hWL hL hLperp hWperp hh₀ hQh₀ hodd hw hu
  obtain ⟨hS1, hS2⟩ := eichler_shear hLperp hw hQw hu'L
  refine ⟨(eichler Q w u').toLinearMap.toAddMonoidHom, hc, fun v hv => ?_, fun v => ?_⟩
  · change eichler Q w u' v = v + polar Q v u • w
    have h0 : polar Q v (u - u') = 0 := by
      rw [polar_comm]
      exact (hLperp v).1 hv _ huu'
    rw [hS1 v hv, polar_sub_right, sub_eq_zero] at *
    rw [h0]
  · change eichler Q w u' v - v - polar Q v w • u ∈ W
    rw [show eichler Q w u' v - v - polar Q v w • u =
      (eichler Q w u' v - v - polar Q v w • u') - polar Q v w • (u - u') by
        rw [smul_sub]; abel]
    exact W.sub_mem (hS2 v) (W.smul_mem _ huu')

end Shears


section WRoute

variable {Q : QuadraticForm K V}

theorem eichler_commutator_of_fix {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {w h : V} (hgh : g h = h) :
    eichler Q w h * g * (eichler Q w h)⁻¹ * g⁻¹ = eichler Q w h * (eichler Q (g w) h)⁻¹ := by
  have h1 : eichler Q w h * g * (eichler Q w h)⁻¹ * g⁻¹ =
      eichler Q w h * (g * eichler Q w h * g⁻¹)⁻¹ := by group
  rw [h1, eichler_conj hg, hgh]

theorem eichler_eq_of_comm {T : V ≃ₗ[K] V} (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {a b h z : V} (hTa : T a = a) (hTb : T b = b) (hTh : T h = h + z)
    (hah : polar Q a h = 0) (hbh : polar Q b h = 0) (haz : polar Q a z = 0)
    (hbz : polar Q b z = 0)
    (hc : T * (eichler Q a h * (eichler Q b h)⁻¹) = eichler Q a h * (eichler Q b h)⁻¹ * T) :
    eichler Q a z = eichler Q b z := by
  have h1 : T * (eichler Q a h * (eichler Q b h)⁻¹) * T⁻¹ =
      eichler Q a h * (eichler Q b h)⁻¹ := by rw [hc, mul_inv_cancel_right]
  have h2 : T * (eichler Q a h * (eichler Q b h)⁻¹) * T⁻¹ =
      (T * eichler Q a h * T⁻¹) * (T * eichler Q b h * T⁻¹)⁻¹ := by group
  rw [h2, eichler_conj hT, eichler_conj hT, hTa, hTb, hTh, ← eichler_mul hah haz,
    ← eichler_mul hbh hbz, mul_inv_rev] at h1
  have h3 : eichler Q a z * (eichler Q b z)⁻¹ = 1 :=
    calc eichler Q a z * (eichler Q b z)⁻¹ = (eichler Q a h)⁻¹ *
          (eichler Q a h * eichler Q a z * ((eichler Q b z)⁻¹ * (eichler Q b h)⁻¹)) *
            eichler Q b h := by group
      _ = (eichler Q a h)⁻¹ * (eichler Q a h * (eichler Q b h)⁻¹) * eichler Q b h := by rw [h1]
      _ = 1 := by group
  exact mul_inv_eq_one.1 h3

theorem exists_eq_smul_sub_of_eichler_eq [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {a b z : V} (hind : LinearIndependent K ![a, b])
    (hQa : Q a = 0) (hQb : Q b = 0) (hQz : Q z = 0) (haz : polar Q a z = 0)
    (hbz : polar Q b z = 0) (he : eichler Q a z = eichler Q b z) :
    ∃ c : K, z = c • (a - b) := by
  obtain ⟨g, hg⟩ := exists_dual_family hQ hind
  have h00 : polar Q a (g 0) = 1 := by simpa using hg 0 0
  have h10 : polar Q b (g 0) = 0 := by simpa using hg 1 0
  have e := LinearEquiv.congr_fun he (g 0)
  rw [eichler_apply hQa haz, eichler_apply hQb hbz, polar_comm Q (g 0) a, h00,
    polar_comm Q (g 0) b, h10, hQz] at e
  exact ⟨polar Q (g 0) z, by linear_combination (norm := module) e⟩

variable [CharP K 2]

theorem fix_of_comm_wLevi [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {T : V ≃ₗ[K] V} (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {w₁ w₂ w₁' w₂' h z : V} (hf : IsHypFrame Q w₁ w₂ w₁' w₂') (hh : wLevi hf h = h)
    (hTw₁ : T w₁ = w₁) (hTw₂ : T w₂ = w₂) (hTh : T h = h + z) (hQz : Q z = 0)
    (h₁h : polar Q w₁ h = 0) (h₂h : polar Q w₂ h = 0) (h₁z : polar Q w₁ z = 0)
    (h₂z : polar Q w₂ z = 0)
    (hc₁ : T * (eichler Q w₁ h * wLevi hf * (eichler Q w₁ h)⁻¹ * (wLevi hf)⁻¹) =
      eichler Q w₁ h * wLevi hf * (eichler Q w₁ h)⁻¹ * (wLevi hf)⁻¹ * T)
    (hc₂ : T * (eichler Q w₂ h * wLevi hf * (eichler Q w₂ h)⁻¹ * (wLevi hf)⁻¹) =
      eichler Q w₂ h * wLevi hf * (eichler Q w₂ h)⁻¹ * (wLevi hf)⁻¹ * T) :
    z = 0 := by
  have hy₁ : wLevi hf w₁ = w₂ := wLeviLin_apply_w₁ hf
  have hy₂ : wLevi hf w₂ = w₁ + w₂ := wLeviLin_apply_w₂ hf
  obtain ⟨hq₁, hq₂, -, -, h12, -, h11, h22, h12x, h21x⟩ := id hf
  have hind : LinearIndependent K ![w₁, w₂] := LinearIndependent.pair_iff.2 fun a b hab => by
    have e₁ := congrArg (fun v => polar Q v w₁') hab
    have e₂ := congrArg (fun v => polar Q v w₂') hab
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_zero_left, h11, h21x, h22,
      h12x] at e₁ e₂
    exact ⟨by linear_combination e₁, by linear_combination e₂⟩
  have hind' : LinearIndependent K ![w₂, w₁ + w₂] := LinearIndependent.pair_iff.2 fun a b hab => by
    have h' : b • w₁ + (a + b) • w₂ = 0 := by rw [← hab]; module
    obtain ⟨hb, hab'⟩ := LinearIndependent.pair_iff.1 hind _ _ h'
    exact ⟨by linear_combination hab' - hb, hb⟩
  rw [eichler_commutator_of_fix (wLevi_mem_orthogonalGroup _) hh, hy₁] at hc₁
  rw [eichler_commutator_of_fix (wLevi_mem_orthogonalGroup _) hh, hy₂] at hc₂
  have e₁ := eichler_eq_of_comm hT hTw₁ hTw₂ hTh h₁h h₂h h₁z h₂z hc₁
  have h₁₂h : polar Q (w₁ + w₂) h = 0 := by rw [polar_add_left, h₁h, h₂h, add_zero]
  have h₁₂z : polar Q (w₁ + w₂) z = 0 := by rw [polar_add_left, h₁z, h₂z, add_zero]
  have hTw₁₂ : T (w₁ + w₂) = w₁ + w₂ := by rw [map_add, hTw₁, hTw₂]
  have e₂ := eichler_eq_of_comm hT hTw₂ hTw₁₂ hTh h₂h h₁₂h h₂z h₁₂z hc₂
  have hq₁₂ : Q (w₁ + w₂) = 0 := by rw [QuadraticMap.map_add Q, hq₁, hq₂, h12, add_zero, add_zero]
  obtain ⟨c, hc⟩ := exists_eq_smul_sub_of_eichler_eq hQ hind hq₁ hq₂ hQz h₁z h₂z e₁
  obtain ⟨c', hc'⟩ := exists_eq_smul_sub_of_eichler_eq hQ hind' hq₂ hq₁₂ hQz h₂z h₁₂z e₂
  have h3 : (c + c') • w₁ + (-c) • w₂ = 0 := by
    have := hc.symm.trans hc'
    linear_combination (norm := module) this
  obtain ⟨-, hc0⟩ := LinearIndependent.pair_iff.1 hind _ _ h3
  rw [hc, neg_eq_zero.1 hc0, zero_smul]

end WRoute

section Frame

variable [CharP K 2] {Q : QuadraticForm K V}

theorem isHypFrame_of {x₁ x₂ n₁ n₂ : V} (hq₁ : Q n₁ = 0) (hq₂ : Q n₂ = 0) (h12 : polar Q n₁ n₂ = 0)
    (h₁ : polar Q x₁ n₁ = 0) (h₂ : polar Q x₂ n₂ = 0) (h₁₂ : polar Q x₁ n₂ = 1)
    (h₂₁ : polar Q x₂ n₁ = 1) :
    IsHypFrame Q n₂ n₁ (x₁ + Q x₁ • n₂) (x₂ + polar Q x₁ x₂ • n₂ + Q x₂ • n₁) := by
  have h21 : polar Q n₂ n₁ = 0 := by rw [polar_comm, h12]
  have h₁' : polar Q n₁ x₁ = 0 := by rw [polar_comm, h₁]
  have h₂' : polar Q n₂ x₂ = 0 := by rw [polar_comm, h₂]
  have h₁₂' : polar Q n₂ x₁ = 1 := by rw [polar_comm, h₁₂]
  have h₂₁' : polar Q n₁ x₂ = 1 := by rw [polar_comm, h₂₁]
  have s₁ := polar_self_charTwo Q n₁
  have s₂ := polar_self_charTwo Q n₂
  refine ⟨hq₂, hq₁, ?_, ?_, h21, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_add_left, polar_add_right,
      polar_smul_left, polar_smul_right, smul_eq_mul, hq₁, hq₂, h12, h21, h₁, h₂, h₁₂, h₂₁, h₁',
      h₂', h₁₂', h₂₁', s₁, s₂] <;>
    char_two_ring

@[expose] def subOne (s : V ≃ₗ[K] V) : V →ₗ[K] V :=
  s.toLinearMap - LinearMap.id

omit [CharP K 2] in
theorem subOne_apply (s : V ≃ₗ[K] V) (v : V) : subOne s v = s v - v :=
  rfl

variable {s : V ≃ₗ[K] V}

theorem exists_wLevi (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs2 : ∀ v, s (s v) = v)
    {x₁ x₂ : V} (h₁ : polar Q x₁ (s x₁ - x₁) = 0) (h₂ : polar Q x₂ (s x₂ - x₂) = 0)
    (h₁₂ : polar Q x₁ (s x₂ - x₂) = 1) :
    ∃ w₁' w₂' : V, ∃ hf : IsHypFrame Q (s x₂ - x₂) (s x₁ - x₁) w₁' w₂',
      wLevi hf * s = s * wLevi hf ∧
      ∀ y, polar Q y (s x₁ - x₁) = 0 → polar Q y (s x₂ - x₂) = 0 →
        wLevi hf (s y - y) = s y - y := by
  have hadj := polar_sub_left_eq hs hs2
  have hNN : ∀ x y, polar Q (s x - x) (s y - y) = 0 := fun x y => by
    rw [hadj, sub_sub_eq_zero hs2, polar_zero_right]
  have hq : ∀ x, polar Q x (s x - x) = 0 → Q (s x - x) = 0 := fun x hx => by
    rw [map_sub_eq_polar hs, hx]
  have h₂₁ : polar Q x₂ (s x₁ - x₁) = 1 := by
    rw [← hadj, polar_comm, h₁₂]
  have hf := isHypFrame_of (hq x₁ h₁) (hq x₂ h₂) (hNN x₁ x₂) h₁ h₂ h₁₂ h₂₁
  have hN₂₂ := sub_sub_eq_zero hs2 x₂
  have hN₁₁ := sub_sub_eq_zero hs2 x₁
  refine ⟨_, _, hf, ?_, fun y hy₁ hy₂ => ?_⟩
  · have hN₁' : subOne s (x₁ + Q x₁ • (s x₂ - x₂)) = s x₁ - x₁ := by
      rw [subOne_apply, map_add, map_smul]
      linear_combination (norm := module) Q x₁ • hN₂₂
    have hN₂' : subOne s (x₂ + polar Q x₁ x₂ • (s x₂ - x₂) + Q x₂ • (s x₁ - x₁)) =
        s x₂ - x₂ := by
      rw [subOne_apply, map_add, map_add, map_smul, map_smul]
      linear_combination (norm := module) polar Q x₁ x₂ • hN₂₂ + Q x₂ • hN₁₁
    have hN := wLeviLin_comm_N (Q := Q) (N := subOne s) (fun x y => hadj x y) hN₂₂ hN₁₁ hN₁' hN₂'
    refine LinearEquiv.ext fun x => ?_
    have e := hN x
    rw [subOne_apply, subOne_apply, map_sub] at e
    exact (sub_left_inj.1 e).symm
  · have e₁ : polar Q (s y - y) (x₁ + Q x₁ • (s x₂ - x₂)) = 0 := by
      rw [polar_add_right, polar_smul_right, hNN, smul_zero, add_zero, hadj, hy₁]
    have e₂ : polar Q (s y - y) (x₂ + polar Q x₁ x₂ • (s x₂ - x₂) + Q x₂ • (s x₁ - x₁)) = 0 := by
      rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right, hNN, hNN,
        smul_zero, smul_zero, add_zero, add_zero, hadj, hy₂]
    change wLeviLin Q _ _ _ _ (s y - y) = s y - y
    rw [wLeviLin_apply, e₁, e₂, hNN, hNN]
    simp

theorem exists_wRoute [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs2 : ∀ v, s (s v) = v)
    {W : Submodule K V} (hW : ∀ v, v ∈ W ↔ ∃ x, s x - x = v)
    (hW2 : ∃ w₁ ∈ W, ∃ w₂ ∈ W, Q w₁ = 0 ∧ Q w₂ = 0 ∧ LinearIndependent K ![w₁, w₂])
    (hb : ∃ h ∈ W, Q h ≠ 0) :
    ∃ x₁ x₂ y₀ : V, polar Q x₁ (s x₁ - x₁) = 0 ∧ polar Q x₂ (s x₂ - x₂) = 0 ∧
      polar Q x₁ (s x₂ - x₂) = 1 ∧ polar Q y₀ (s x₁ - x₁) = 0 ∧ polar Q y₀ (s x₂ - x₂) = 0 ∧
      Q (s y₀ - y₀) ≠ 0 := by
  have hadj := polar_sub_left_eq hs hs2
  have hNN : ∀ x y, polar Q (s x - x) (s y - y) = 0 := fun x y => by
    rw [hadj, sub_sub_eq_zero hs2, polar_zero_right]
  have hq : ∀ x, Q (s x - x) = polar Q x (s x - x) := map_sub_eq_polar hs
  have hNsmul : ∀ (c : K) x, s (c • x) - c • x = c • (s x - x) := fun c x => by
    rw [map_smul, smul_sub]
  obtain ⟨w₁, hw₁, w₂, hw₂, hq₁, hq₂, hind⟩ := hW2
  obtain ⟨a, rfl⟩ := (hW w₁).1 hw₁
  obtain ⟨a', rfl⟩ := (hW w₂).1 hw₂
  obtain ⟨h, hh, hQh⟩ := hb
  obtain ⟨y, rfl⟩ := (hW h).1 hh
  obtain ⟨x₁, x₂, h₁, h₂, h₁₂⟩ : ∃ x₁ x₂ : V, Q (s x₁ - x₁) = 0 ∧ Q (s x₂ - x₂) = 0 ∧
      polar Q x₁ (s x₂ - x₂) ≠ 0 := by
    by_contra! hall
    have key : ∀ v, ∃ t : K, Q (s (v - t • y) - (v - t • y)) = 0 := by
      intro v
      obtain ⟨t, ht⟩ := isSquare_of_charTwo' (Q (s v - v) / Q (s y - y))
      refine ⟨t, ?_⟩
      have e : s (v - t • y) - (v - t • y) = (s v - v) + t • (s y - y) := by
        rw [map_sub, map_smul]
        linear_combination (norm := module) (CharTwo.two_eq_zero : (2 : K) = 0) • (t • y - t • s y)
      rw [e, QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right, hNN, smul_zero,
        add_zero, smul_eq_mul, ← ht, div_mul_cancel₀ _ hQh]
      exact CharTwo.add_self_eq_zero _
    have hlin : ∀ b, Q (s b - b) = 0 → ∀ v, ∃ t : K,
        polar Q (s b - b) v = t * polar Q (s b - b) y := by
      intro b hb v
      obtain ⟨t, ht⟩ := key v
      refine ⟨t, ?_⟩
      have h0 : polar Q (s b - b) (v - t • y) = 0 := by
        rw [hadj]
        exact hall b _ hb ht
      rw [polar_sub_right, polar_smul_right, smul_eq_mul, sub_eq_zero] at h0
      exact h0
    set c := polar Q (s a - a) y
    set c' := polar Q (s a' - a') y
    have hzero : c' • (s a - a) - c • (s a' - a') = 0 := hQ.1 _ fun v => by
      change polar Q (c' • (s a - a) - c • (s a' - a')) v = 0
      obtain ⟨t, ht⟩ := key v
      have h1 : polar Q (s a - a) v = t * c := by
        have h0 : polar Q (s a - a) (v - t • y) = 0 := by rw [hadj]; exact hall a _ hq₁ ht
        rw [polar_sub_right, polar_smul_right, smul_eq_mul, sub_eq_zero] at h0
        exact h0
      have h2 : polar Q (s a' - a') v = t * c' := by
        have h0 : polar Q (s a' - a') (v - t • y) = 0 := by rw [hadj]; exact hall a' _ hq₂ ht
        rw [polar_sub_right, polar_smul_right, smul_eq_mul, sub_eq_zero] at h0
        exact h0
      rw [polar_sub_left, polar_smul_left, polar_smul_left, h1, h2, smul_eq_mul, smul_eq_mul]
      ring
    obtain ⟨hc', hc⟩ := LinearIndependent.pair_iff.1 hind c' (-c) (by
      rw [neg_smul, ← sub_eq_add_neg]
      exact hzero)
    have hc0 : c = 0 := neg_eq_zero.1 hc
    apply hind.ne_zero 0
    change s a - a = 0
    refine hQ.1 _ fun v => ?_
    change polar Q (s a - a) v = 0
    obtain ⟨t, ht⟩ := hlin a hq₁ v
    rw [ht]
    change t * c = 0
    rw [hc0, mul_zero]
  set c := polar Q x₁ (s x₂ - x₂) with hc
  refine ⟨x₁, c⁻¹ • x₂, y + polar Q y (s (c⁻¹ • x₂) - c⁻¹ • x₂) • x₁ +
    polar Q y (s x₁ - x₁) • (c⁻¹ • x₂), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hq, h₁]
  · rw [← hq, hNsmul, QuadraticMap.map_smul, h₂, smul_zero]
  · rw [hNsmul, polar_smul_right, smul_eq_mul, inv_mul_cancel₀ h₁₂]
  · have e : polar Q (c⁻¹ • x₂) (s x₁ - x₁) = 1 := by
      rw [← hadj, polar_comm, hNsmul, polar_smul_right, smul_eq_mul, inv_mul_cancel₀ h₁₂]
    rw [polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, e, ← hq, h₁,
      smul_eq_mul, smul_eq_mul]
    char_two_ring
  · have e : polar Q x₁ (s (c⁻¹ • x₂) - c⁻¹ • x₂) = 1 := by
      rw [hNsmul, polar_smul_right, smul_eq_mul, inv_mul_cancel₀ h₁₂]
    rw [polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, e, ← hq, hNsmul,
      QuadraticMap.map_smul, h₂, smul_zero, smul_eq_mul, smul_eq_mul]
    char_two_ring
  · have e : s (y + polar Q y (s (c⁻¹ • x₂) - c⁻¹ • x₂) • x₁ +
        polar Q y (s x₁ - x₁) • (c⁻¹ • x₂)) - (y + polar Q y (s (c⁻¹ • x₂) - c⁻¹ • x₂) • x₁ +
        polar Q y (s x₁ - x₁) • (c⁻¹ • x₂)) = (s y - y) +
          (polar Q y (s (c⁻¹ • x₂) - c⁻¹ • x₂) • (s x₁ - x₁) +
            (polar Q y (s x₁ - x₁) * c⁻¹) • (s x₂ - x₂)) := by
      simp only [map_add, map_smul]
      module
    rw [e, QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_smul,
      QuadraticMap.map_smul, h₁, h₂, polar_smul_left, polar_smul_right, hNN, polar_add_right,
      polar_smul_right, polar_smul_right, hNN, hNN]
    simpa using hQh

end Frame

section MRoute

variable [CharP K 2] {Q : QuadraticForm K V} {W L : Submodule K V}

theorem fix_of_comm_rot {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] {T : F}
    (hLperp : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0) {p p₂ : V} (h : IsRotPair Q p p₂)
    (hp : p ∈ L) (hp₂ : p₂ ∈ L) (hc : Comm T (rot h)) (hTp₂ : T p₂ - p₂ ∈ W) : T p = p := by
  have e := hc p₂
  have hfix : rot h (T p₂ - p₂) = T p₂ - p₂ := by
    rw [rot_apply]
    exact rotLin_apply_of_polar_eq_zero ((hLperp p).1 hp _ hTp₂) ((hLperp p₂).1 hp₂ _ hTp₂)
  have e2 : rot h (T p₂) = p + p₂ + (T p₂ - p₂) := by
    rw [show T p₂ = p₂ + (T p₂ - p₂) by abel, map_add, hfix, rot_apply, rotLin_apply_right h]
    abel
  rw [rot_apply, rotLin_apply_right h, e2, map_add] at e
  have : T p = p + p₂ + (T p₂ - p₂) - T p₂ := by rw [← e]; abel
  rw [this]
  abel

variable [Finite K]

theorem fix_L_of_mRoute (hWL : W ≤ L) (hLperp : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0)
    (hWperp : ∀ v, v ∈ W ↔ ∀ l ∈ L, polar Q l v = 0) {h₀ : V} (hh₀ : h₀ ∈ W) (hQh₀ : Q h₀ ≠ 0)
    {T : V ≃+ V} (hTlin : ∀ (a : K) v, T (a • v) = a • T v)
    (hTLW : ∀ v ∈ L, T v - v ∈ W) (hTW₀ : ∀ w ∈ W, Q w = 0 → T w = w)
    (hrot : ∀ p ∈ L, ∀ p₂ ∈ L, ∀ h : IsRotPair Q p p₂, Comm T (rot h))
    {x y : V} (hx : x ∈ L) (hy : y ∈ L) (hxy : polar Q x y = 0)
    (hind : ∀ a b : K, a • x + b • y ∈ W → a = 0 ∧ b = 0) :
    ∀ v ∈ L, T v = v := by
  have hgood : ∀ p ∈ L, p ∉ W → Q p = 1 → T p = p := fun p hp hpW hQp => by
    obtain ⟨p₂, hp₂, hpair⟩ := exists_rotPair hWL hLperp hWperp hh₀ hQh₀ hp hpW hQp
    exact fix_of_comm_rot hLperp hpair hp hp₂ (hrot p hp p₂ hp₂ hpair) (hTLW p₂ hp₂)
  have hadj : ∀ p ∈ L, p ∉ W → ∃ t : K, Q (p + t • h₀) = 1 ∧ T (p + t • h₀) = p + t • h₀ := by
    intro p hp hpW
    obtain ⟨t, ht⟩ := exists_adjust hLperp hh₀ hQh₀ hp 1
    refine ⟨t, ht, hgood _ (L.add_mem hp (L.smul_mem _ (hWL hh₀))) (fun h => hpW ?_) ht⟩
    have := W.sub_mem h (W.smul_mem t hh₀)
    rwa [add_sub_cancel_right] at this
  have hxW : x ∉ W := fun h => one_ne_zero (hind 1 0 (by simpa using h)).1
  have hyW : y ∉ W := fun h => one_ne_zero (hind 0 1 (by simpa using h)).2
  have hxyW : x + y ∉ W := fun h => one_ne_zero (hind 1 1 (by simpa using h)).1
  obtain ⟨a, ha, hTa⟩ := hadj x hx hxW
  obtain ⟨b, hb, hTb⟩ := hadj y hy hyW
  obtain ⟨c, hc, hTc⟩ := hadj (x + y) (L.add_mem hx hy) hxyW
  have hpol : ∀ p ∈ L, polar Q p h₀ = 0 := fun p hp => by
    rw [polar_comm]
    exact (hLperp p).1 hp h₀ hh₀
  have hQadj : ∀ p ∈ L, ∀ t : K, Q (p + t • h₀) = Q p + t * t * Q h₀ := fun p hp t => by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right, hpol p hp, smul_zero,
      add_zero, smul_eq_mul]
  rw [hQadj x hx] at ha
  rw [hQadj y hy] at hb
  rw [hQadj _ (L.add_mem hx hy), QuadraticMap.map_add Q, hxy, add_zero] at hc
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have habc : (a + b + c) * (a + b + c) * Q h₀ = 1 := by
    linear_combination ha + hb + hc + ((a * b + a * c + b * c) * Q h₀ + 1 - Q x - Q y) * h2
  have habc0 : a + b + c ≠ 0 := fun h0 => by
    rw [h0, zero_mul, zero_mul] at habc
    exact zero_ne_one habc
  have hsum : (a + b + c) • h₀ = (x + a • h₀) + (y + b • h₀) + (x + y + c • h₀) := by
    have hxx := ShearRigidity.add_self_eq_zero K x
    have hyy := ShearRigidity.add_self_eq_zero K y
    linear_combination (norm := module) -hxx - hyy
  have hTh₀ : T h₀ = h₀ := by
    have e : T ((a + b + c) • h₀) = (a + b + c) • h₀ := by
      rw [hsum, map_add, map_add, hTa, hTb, hTc]
    rw [hTlin] at e
    exact smul_right_injective V habc0 e
  have hTW : ∀ w ∈ W, T w = w := fun w hw => by
    obtain ⟨t, ht⟩ := exists_adjust hLperp hh₀ hQh₀ (hWL hw) 0
    have e := hTW₀ _ (W.add_mem hw (W.smul_mem t hh₀)) ht
    rw [map_add, hTlin, hTh₀, add_left_inj] at e
    exact e
  intro v hv
  by_cases hvW : v ∈ W
  · exact hTW v hvW
  · obtain ⟨t, -, ht⟩ := hadj v hv hvW
    rw [map_add, hTlin, hTh₀, add_left_inj] at ht
    exact ht

omit [Finite K] in
theorem sq_eq_one_of_fix_L {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] {T : F}
    (hWL : W ≤ L) (hWperp : ∀ v, v ∈ W ↔ ∀ l ∈ L, polar Q l v = 0)
    (hTB : ∀ x y, polar Q (T x) (T y) = polar Q x y) (hTL : ∀ v ∈ L, T v = v) (v : V) :
    T (T v) = v := by
  have h : ∀ v, T v - v ∈ W := fun v => (hWperp _).2 fun l hl => by
    rw [polar_sub_right, ← hTL l hl, hTB, hTL l hl, sub_self]
  exact apply_apply_eq_of_apply_sub K (fun v => hTL _ (hWL (h v))) v

omit [Finite K] in
theorem exists_mRoute [FiniteDimensional K V] (hLperp : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0)
    {x₀ u₀ : V} (hx₀ : x₀ ∈ L) (hu₀ : u₀ ∈ L) (h₀₁ : polar Q x₀ u₀ = 1)
    (hdim : Module.finrank K W + 3 ≤ Module.finrank K L) :
    ∃ x ∈ L, ∃ y ∈ L, polar Q x y = 0 ∧ ∀ a b : K, a • x + b • y ∈ W → a = 0 ∧ b = 0 := by
  classical
  by_cases hex : ∃ y ∈ L, polar Q x₀ y = 0 ∧ polar Q u₀ y = 0 ∧ y ∉ W
  · obtain ⟨y, hy, hxy, huy, hyW⟩ := hex
    refine ⟨x₀, hx₀, y, hy, hxy, fun a b hab => ?_⟩
    have hu := (hLperp u₀).1 hu₀ _ hab
    rw [polar_add_left, polar_smul_left, polar_smul_left, h₀₁, polar_comm, huy, smul_eq_mul,
      smul_eq_mul, mul_one, mul_zero, add_zero] at hu
    rw [hu, zero_smul, zero_add] at hab
    refine ⟨hu, ?_⟩
    by_contra hb
    apply hyW
    have := W.smul_mem b⁻¹ hab
    rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at this
  · exfalso
    push Not at hex
    have hle : L ≤ W ⊔ Submodule.span K ({x₀, u₀} : Set V) := by
      intro l hl
      have hu₀x₀ : polar Q u₀ x₀ = 1 := by rw [polar_comm, h₀₁]
      have hl' := hex (l + polar Q u₀ l • x₀ + polar Q x₀ l • u₀)
        (L.add_mem (L.add_mem hl (L.smul_mem _ hx₀)) (L.smul_mem _ hu₀))
        (by
          rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right,
            polar_self_charTwo, h₀₁, smul_eq_mul, smul_eq_mul]
          char_two_ring)
        (by
          rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right,
            polar_self_charTwo, hu₀x₀, smul_eq_mul, smul_eq_mul]
          char_two_ring)
      have hspan : polar Q u₀ l • x₀ + polar Q x₀ l • u₀ ∈ Submodule.span K ({x₀, u₀} : Set V) :=
        Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      have e : l = (l + polar Q u₀ l • x₀ + polar Q x₀ l • u₀) -
          (polar Q u₀ l • x₀ + polar Q x₀ l • u₀) := by abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hl') (Submodule.mem_sup_right hspan)
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_add_le_finrank_add_finrank W
      (Submodule.span K ({x₀, u₀} : Set V))
    have h3 : Module.finrank K (Submodule.span K ({x₀, u₀} : Set V)) ≤ 2 := by
      have := finrank_span_finset_le_card (R := K) ({x₀, u₀} : Finset V)
      rw [Finset.coe_insert, Finset.coe_singleton] at this
      exact this.trans Finset.card_le_two
    omega

end MRoute

section Main

variable [Finite K] [CharP K 2] [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem sq_eq_one_of_commute_odd (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs2 : ∀ v, s (s v) = v)
    {W L : Submodule K V} (hW : ∀ v, v ∈ W ↔ ∃ x, s x - x = v) (hL : ∀ v, v ∈ L ↔ s v = v)
    (hb : ∃ h ∈ W, Q h ≠ 0) (hW₀ : ∃ w ∈ W, w ≠ 0 ∧ Q w = 0)
    (hLW : ∃ x ∈ L, ∃ u ∈ L, polar Q x u = 1)
    (hroute : (∃ w₁ ∈ W, ∃ w₂ ∈ W, Q w₁ = 0 ∧ Q w₂ = 0 ∧ LinearIndependent K ![w₁, w₂]) ∨
      Module.finrank K W + 3 ≤ Module.finrank K L)
    {φ : K ≃+* K} (T : V ≃+ V) (hT : ∀ (a : K) v, T (a • v) = φ a • T v)
    (hTQ : ∀ v, Q (T v) = φ (Q v)) (hTs : ∀ v, T (s v) = s (T v))
    (hodd : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * s = s * g → Odd (orderOf g) →
      ∀ v, T (g v) = g (T v)) :
    (∀ a, φ a = a) ∧ ∀ v, T (T v) = v := by
  have hLperp := mem_L_iff hQ hs hs2 hW hL
  have hWperp := mem_W_iff hQ hs hs2 hW hL
  have hWL := W_le_L hs2 hW hL
  have hWiso := W_iso hQ hs hs2 hW hL
  obtain ⟨h₀, hh₀, hQh₀⟩ := hb
  have hW₀mem : ∀ v, v ∈ singularSubspace Q W hWiso ↔ v ∈ W ∧ Q v = 0 := fun v =>
    mem_singularSubspace
  have hW₀0 : singularSubspace Q W hWiso ≠ ⊥ := by
    obtain ⟨w, hw, hw0, hQw⟩ := hW₀
    exact (Submodule.ne_bot_iff _).2 ⟨w, (hW₀mem w).2 ⟨hw, hQw⟩, hw0⟩
  have hTL : ∀ v ∈ L, T v ∈ L := fun v hv => (hL _).2 (by rw [← hTs, (hL v).1 hv])
  have hTW : ∀ v ∈ W, T v ∈ W := fun v hv => by
    obtain ⟨x, rfl⟩ := (hW v).1 hv
    exact (hW _).2 ⟨T x, by rw [map_sub, hTs]⟩
  have hsh : ∀ w ∈ singularSubspace Q W hWiso, ∀ u ∈ L, ∃ g : V →+ V,
      (∀ v, T (g v) = g (T v)) ∧ (∀ v ∈ L, g v = v + polar Q v u • w) ∧
        ∀ v, g v - v - polar Q v w • u ∈ W := fun w hw u hu =>
    exists_shear hs hWL hL hLperp hWperp hh₀ hQh₀ hodd ((hW₀mem w).1 hw).1 ((hW₀mem w).1 hw).2 hu
  obtain ⟨hφ, hTW₀, hTWW₀, hTLL, -⟩ := semilinear_shear_rigidity_quadratic Q hWiso hW₀mem hW₀0
    hLW T hT hTQ hTL hTW fun w hw u hu => (hsh w hw u hu).imp fun _ hg => ⟨hg.1, hg.2.1⟩
  have hTlin : ∀ (a : K) v, T (a • v) = a • T v := fun a v => by rw [hT, hφ]
  have hTQ' : ∀ v, Q (T v) = Q v := fun v => by rw [hTQ, hφ]
  have hTB : ∀ x y, polar Q (T x) (T y) = polar Q x y := fun x y => by
    rw [polar, polar, ← map_add, hTQ', hTQ', hTQ']
  refine ⟨hφ, ?_⟩
  have hTLW : ∀ v ∈ L, T v - v ∈ W := fun v hv => (hWperp _).2 fun l hl => by
    rw [polar_sub_right, polar_comm Q l (T v), hTLL v hv l hl, polar_comm, sub_self]
  have hTW₀' : ∀ w ∈ W, Q w = 0 → T w = w := fun w hw hQw => hTW₀ w ((hW₀mem w).2 ⟨hw, hQw⟩)
  rcases hroute with ⟨w₁, hw₁, w₂, hw₂, hq₁, hq₂, hind⟩ | hdim
  ·
    obtain ⟨x₁, x₂, y₀, h₁, h₂, h₁₂, hy₁, hy₂, hQy⟩ :=
      exists_wRoute hQ hs hs2 hW ⟨w₁, hw₁, w₂, hw₂, hq₁, hq₂, hind⟩ ⟨h₀, hh₀, hQh₀⟩
    obtain ⟨w₁', w₂', hf, hys, hyfix⟩ := exists_wLevi hs hs2 h₁ h₂ h₁₂
    have hhW : s y₀ - y₀ ∈ W := (hW _).2 ⟨y₀, rfl⟩
    have hh : wLevi hf (s y₀ - y₀) = s y₀ - y₀ := hyfix y₀ hy₁ hy₂
    have hn₁W : s x₂ - x₂ ∈ W := (hW _).2 ⟨x₂, rfl⟩
    have hn₂W : s x₁ - x₁ ∈ W := (hW _).2 ⟨x₁, rfl⟩
    obtain ⟨hq₁', hq₂', -, -, -, -, -, -, -, -⟩ := id hf
    have hTn₁ : T (s x₂ - x₂) = s x₂ - x₂ := hTW₀' _ hn₁W hq₁'
    have hTn₂ : T (s x₁ - x₁) = s x₁ - x₁ := hTW₀' _ hn₂W hq₂'
    obtain ⟨hzW, hQz⟩ := (hW₀mem _).1 (hTWW₀ _ hhW)
    let T' : V ≃ₗ[K] V := T.toLinearEquiv hTlin
    have hT'Q : T' ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 hTQ'
    have hc : ∀ w ∈ W, T' * (eichler Q w (s y₀ - y₀) * wLevi hf * (eichler Q w (s y₀ - y₀))⁻¹ *
        (wLevi hf)⁻¹) = eichler Q w (s y₀ - y₀) * wLevi hf * (eichler Q w (s y₀ - y₀))⁻¹ *
          (wLevi hf)⁻¹ * T' := fun w hw => LinearEquiv.ext fun v =>
      comm_of_pow_three hodd (eichler_mem_orthogonalGroup Q w _)
        (eichler_mul_comm hs ((hL w).1 (hWL hw)) ((hL _).1 (hWL hhW)))
        (wLevi_mem_orthogonalGroup hf) hys (wLevi_pow_three hf) v
    have hz0 := fix_of_comm_wLevi hQ hT'Q hf hh hTn₁ hTn₂
      (show T (s y₀ - y₀) = s y₀ - y₀ + (T (s y₀ - y₀) - (s y₀ - y₀)) by abel) hQz
      (hWiso _ hn₁W _ hhW) (hWiso _ hn₂W _ hhW) (hWiso _ hn₁W _ hzW) (hWiso _ hn₂W _ hzW)
      (hc _ hn₁W) (hc _ hn₂W)
    have hTh : T (s y₀ - y₀) = s y₀ - y₀ := sub_eq_zero.1 hz0
    have hTWfix : ∀ w ∈ W, T w = w := fun w hw => by
      obtain ⟨t, ht⟩ := exists_adjust hLperp hhW hQy (hWL hw) 0
      have e := hTW₀' _ (W.add_mem hw (W.smul_mem t hhW)) ht
      rw [map_add, hTlin, hTh, add_left_inj] at e
      exact e
    exact (semilinear_shear_rigidity_quadratic_of_fix Q hQ.2 hLperp
      ⟨w₁, (hW₀mem _).2 ⟨hw₁, hq₁⟩, w₂, (hW₀mem _).2 ⟨hw₂, hq₂⟩, hind⟩ T hTQ' hTWfix hsh).2.2
  ·
    obtain ⟨x₀, hx₀, u₀, hu₀, h₀₁⟩ := hLW
    obtain ⟨x, hx, y, hy, hxy, hind⟩ := exists_mRoute hLperp hx₀ hu₀ h₀₁ hdim
    have hrot : ∀ p ∈ L, ∀ p₂ ∈ L, ∀ h : IsRotPair Q p p₂, Comm T (rot h) :=
      fun p hp p₂ hp₂ h => hodd _ (rot_mem_orthogonalGroup h)
        (rot_mul_comm hs h ((hL p).1 hp) ((hL p₂).1 hp₂))
        (odd_orderOf_of_pow_three (rot_pow_three h))
    exact sq_eq_one_of_fix_L hWL hWperp hTB
      (fix_L_of_mRoute hWL hLperp hWperp hh₀ hQh₀ hTlin hTLW hTW₀' hrot hx hy hxy hind)

theorem hyps_of_finrank (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs2 : ∀ v, s (s v) = v)
    {W L : Submodule K V} (hW : ∀ v, v ∈ W ↔ ∃ x, s x - x = v) (hL : ∀ v, v ∈ L ↔ s v = v)
    (hb : ∃ h ∈ W, Q h ≠ 0) (hW2 : 2 ≤ Module.finrank K W) (hWL : W ≠ L)
    (hV : 7 ≤ Module.finrank K V) :
    (∃ w ∈ W, w ≠ 0 ∧ Q w = 0) ∧ (∃ x ∈ L, ∃ u ∈ L, polar Q x u = 1) ∧
      ((∃ w₁ ∈ W, ∃ w₂ ∈ W, Q w₁ = 0 ∧ Q w₂ = 0 ∧ LinearIndependent K ![w₁, w₂]) ∨
        Module.finrank K W + 3 ≤ Module.finrank K L) := by
  classical
  have hLperp := mem_L_iff hQ hs hs2 hW hL
  have hWperp := mem_W_iff hQ hs hs2 hW hL
  have hWleL := W_le_L hs2 hW hL
  have hWiso := W_iso hQ hs hs2 hW hL
  obtain ⟨h₀, hh₀, hQh₀⟩ := hb
  have hspan1 : ∀ v : V, Module.finrank K (K ∙ v) ≤ 1 := fun v => by
    have := finrank_span_finset_le_card (R := K) ({v} : Finset V)
    rwa [Finset.coe_singleton, Finset.card_singleton] at this
  have hW0 : W ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hW2
    omega
  obtain ⟨w₁, hw₁, w₂, hw₂, hind⟩ : ∃ w₁ ∈ W, ∃ w₂ ∈ W, LinearIndependent K ![w₁, w₂] := by
    rcases ShearRigidity.exists_pair_or_eq_span hW0 with h | ⟨w₀, -, hW1⟩
    · exact h
    · have := hspan1 w₀
      rw [← hW1] at this
      omega
  have hsing : ∃ w ∈ W, w ≠ 0 ∧ Q w = 0 := by
    by_cases hq₁ : Q w₁ = 0
    · exact ⟨w₁, hw₁, by simpa using hind.ne_zero 0, hq₁⟩
    · obtain ⟨c, hc⟩ := isSquare_of_charTwo' (Q w₂ / Q w₁)
      refine ⟨w₂ + c • w₁, W.add_mem hw₂ (W.smul_mem c hw₁), fun h => ?_, ?_⟩
      · have := (LinearIndependent.pair_iff.1 hind c 1 (by rw [one_smul, add_comm]; exact h)).2
        exact one_ne_zero this
      · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right,
          hWiso w₂ hw₂ w₁ hw₁, smul_zero, add_zero, smul_eq_mul, ← hc,
          div_mul_cancel₀ _ hq₁]
        exact CharTwo.add_self_eq_zero _
  refine ⟨hsing, ?_, ?_⟩
  ·
    obtain ⟨x, hxL, hxW⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hWleL hWL)
    obtain ⟨l, hl, hlx⟩ : ∃ l ∈ L, polar Q l x ≠ 0 := by
      by_contra! h
      exact hxW ((hWperp x).2 h)
    have hxl : polar Q x l ≠ 0 := by rwa [polar_comm]
    exact ⟨x, hxL, (polar Q x l)⁻¹ • l, L.smul_mem _ hl, by
      rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hxl]⟩
  · by_cases h2 : ∃ w₁ ∈ W, ∃ w₂ ∈ W, Q w₁ = 0 ∧ Q w₂ = 0 ∧ LinearIndependent K ![w₁, w₂]
    · exact Or.inl h2
    · right
      have hW₀mem : ∀ v, v ∈ singularSubspace Q W hWiso ↔ v ∈ W ∧ Q v = 0 := fun v =>
        mem_singularSubspace
      have hW₀0 : singularSubspace Q W hWiso ≠ ⊥ := by
        obtain ⟨w, hw, hw0, hQw⟩ := hsing
        exact (Submodule.ne_bot_iff _).2 ⟨w, (hW₀mem w).2 ⟨hw, hQw⟩, hw0⟩
      rcases ShearRigidity.exists_pair_or_eq_span hW₀0 with
        ⟨a, ha, b, hb', hab⟩ | ⟨w₀, -, hW₀1⟩
      · exact absurd ⟨a, ((hW₀mem a).1 ha).1, b, ((hW₀mem b).1 hb').1, ((hW₀mem a).1 ha).2,
          ((hW₀mem b).1 hb').2, hab⟩ h2
      · have hle : W ≤ (K ∙ w₀) ⊔ (K ∙ h₀) := fun w hw => by
          obtain ⟨t, ht⟩ := exists_adjust hLperp hh₀ hQh₀ (hWleL hw) 0
          have hmem : w + t • h₀ ∈ K ∙ w₀ := by
            rw [← hW₀1]
            exact (hW₀mem _).2 ⟨W.add_mem hw (W.smul_mem t hh₀), ht⟩
          have e : w = (w + t • h₀) - t • h₀ := by abel
          rw [e]
          exact Submodule.sub_mem _ (Submodule.mem_sup_left hmem) (Submodule.mem_sup_right
            (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self h₀)))
        have h1 := Submodule.finrank_mono hle
        have h3 := Submodule.finrank_add_le_finrank_add_finrank (K ∙ w₀) (K ∙ h₀)
        have h4 := hspan1 w₀
        have h5 := hspan1 h₀
        have hLeq : L = LinearMap.BilinForm.orthogonal (polarBilin Q) W := Submodule.ext fun v => by
          rw [LinearMap.BilinForm.mem_orthogonal_iff, hLperp]
          rfl
        have h6 : Module.finrank K L = Module.finrank K V - Module.finrank K W := by
          rw [hLeq]
          exact LinearMap.BilinForm.finrank_orthogonal hQ W
        omega

end Main

end OrthogonalShearC

end CFSG.SeitzReduction
