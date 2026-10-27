module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafPure
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue77a

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf

variable {G : Type*} [Group G]

structure PairCtx (z t : G) (S P₁ P₂ : Subgroup G) : Prop where
  z_sq : z * z = 1
  t_sq : t * t = 1
  zS : ∀ s ∈ S, s * z = z * s
  tS : t ∈ S
  P₁S : P₁ ≤ S
  P₂S : P₂ ≤ S
  zP₁ : z ∈ P₁
  zP₂ : z ∈ P₂
  comm : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a
  inf : P₁ ⊓ P₂ ≤ zpowers z
  tP₁ : ∀ x ∈ P₁, t * x * t⁻¹ ∈ P₂
  tP₂ : ∀ x ∈ P₂, t * x * t⁻¹ ∈ P₁

namespace PairCtx

variable {z t : G} {S P₁ P₂ : Subgroup G} (c : PairCtx z t S P₁ P₂)

include c

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right c.t_sq

theorem tt_conj (x : G) : t * (t * x * t⁻¹) * t⁻¹ = x := by
  have h1 : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, c.t_sq, inv_one]
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
    _ = x := by rw [c.t_sq, h1]; group

theorem eps_cases {ε : G} (hε : ε ∈ zpowers z) : ε = 1 ∨ ε = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hε
  exact B.zpow_of_sq_eq_one c.z_sq k

theorem eps_comm {ε : G} (hε : ε ∈ zpowers z) {s : G} (hs : s ∈ S) : s * ε = ε * s := by
  rcases c.eps_cases hε with rfl | rfl
  · simp
  · exact c.zS s hs

theorem eps_sq {ε : G} (hε : ε ∈ zpowers z) : ε * ε = 1 := by
  rcases c.eps_cases hε with rfl | rfl
  · simp
  · exact c.z_sq

theorem t_eps {ε : G} (hε : ε ∈ zpowers z) : t * ε * t⁻¹ = ε := by
  rw [c.eps_comm hε c.tS]; group

theorem mem_zpowers_of_mul_conj {p : G} (hp : p ∈ P₁) (h : p * (t * p * t⁻¹) = 1) : p ∈ zpowers z := by
  have h2 : t * p * t⁻¹ ∈ P₂ := c.tP₁ p hp
  have h3 : p = (t * p * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h
  have h4 : p ∈ P₂ := by rw [h3]; exact P₂.inv_mem h2
  exact c.inf ⟨hp, h4⟩

theorem CPt_form {x : G} (hx : x ∈ P₁ ⊔ P₂) (hxt : t * x * t⁻¹ = x) :
    ∃ a ∈ P₁, ∃ ε ∈ zpowers z, x = a * (t * a * t⁻¹) * ε := by
  obtain ⟨a, ha, b, hb, hab⟩ := A.mem_sup_of_commute c.comm hx
  have ha' : t * a * t⁻¹ ∈ P₂ := c.tP₁ a ha
  have hb' : t * b * t⁻¹ ∈ P₁ := c.tP₂ b hb
  have h1 : (t * a * t⁻¹) * (t * b * t⁻¹) = a * b := by
    have : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
    rw [← this, ← hab]; exact hxt
  have h2 : (t * b * t⁻¹) * (t * a * t⁻¹) = a * b :=
    (c.comm _ hb' _ ha').trans h1
  have h3 : a⁻¹ * (t * b * t⁻¹) = b * (t * a * t⁻¹)⁻¹ := by
    calc a⁻¹ * (t * b * t⁻¹) = a⁻¹ * ((t * b * t⁻¹) * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by group
      _ = a⁻¹ * (a * b) * (t * a * t⁻¹)⁻¹ := by rw [h2]
      _ = b * (t * a * t⁻¹)⁻¹ := by group
  have hε₁ : a⁻¹ * (t * b * t⁻¹) ∈ P₁ := P₁.mul_mem (P₁.inv_mem ha) hb'
  have hε₂ : a⁻¹ * (t * b * t⁻¹) ∈ P₂ := by rw [h3]; exact P₂.mul_mem hb (P₂.inv_mem ha')
  have hε : a⁻¹ * (t * b * t⁻¹) ∈ zpowers z := c.inf ⟨hε₁, hε₂⟩
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = a⁻¹ * (t * b * t⁻¹) := ⟨_, rfl⟩
  rw [← hεdef] at hε
  refine ⟨a, ha, ε, hε, ?_⟩
  have hb2 : b = t * (t * b * t⁻¹) * t⁻¹ := (c.tt_conj b).symm
  have e1 : t * b * t⁻¹ = a * ε := by rw [hεdef]; group
  have e2 : b = (t * a * t⁻¹) * ε := by
    calc b = t * (t * b * t⁻¹) * t⁻¹ := hb2
      _ = t * (a * ε) * t⁻¹ := by rw [e1]
      _ = (t * a * t⁻¹) * (t * ε * t⁻¹) := by group
      _ = (t * a * t⁻¹) * ε := by rw [c.t_eps hε]
  rw [hab, e2]
  group

theorem u1_of_c (hinv : ∀ x ∈ P₁, x * x = 1 → x ≠ 1 → x = z) {a ε : G} (ha : a ∈ P₁)
    (hε : ε ∈ zpowers z) (hc2 : (a * (t * a * t⁻¹) * ε) * (a * (t * a * t⁻¹) * ε) ≠ 1)
    (hc4 : ((a * (t * a * t⁻¹) * ε) * (a * (t * a * t⁻¹) * ε)) *
      ((a * (t * a * t⁻¹) * ε) * (a * (t * a * t⁻¹) * ε)) = 1) :
    (a * a) * (a * a) = z ∧
      (a * (t * a * t⁻¹) * ε) * (a * (t * a * t⁻¹) * ε) = (a * a) * (t * (a * a) * t⁻¹) := by
  have haS : a ∈ S := c.P₁S ha
  have ha' : t * a * t⁻¹ ∈ P₂ := c.tP₁ a ha
  have ha'S : t * a * t⁻¹ ∈ S := c.P₂S ha'
  have hcomm : Commute a (t * a * t⁻¹) := c.comm a ha _ ha'
  have hae : Commute a ε := c.eps_comm hε haS
  have ha'e : Commute (t * a * t⁻¹) ε := c.eps_comm hε ha'S
  have hεε := c.eps_sq hε
  have hXε : Commute ε (a * (t * a * t⁻¹)) := (hae.mul_left ha'e).symm
  have e1 : (a * (t * a * t⁻¹) * ε) * (a * (t * a * t⁻¹) * ε) =
      (a * a) * ((t * a * t⁻¹) * (t * a * t⁻¹)) := by
    rw [Commute.mul_mul_mul_comm hXε, Commute.mul_mul_mul_comm hcomm.symm, hεε, mul_one]
  have e2 : (a * a) * ((t * a * t⁻¹) * (t * a * t⁻¹)) = (a * a) * (t * (a * a) * t⁻¹) := by
    congr 1; group
  rw [e1, e2] at hc2 hc4 ⊢
  refine ⟨?_, rfl⟩
  have huP : a * a ∈ P₁ := P₁.mul_mem ha ha
  have hu' : t * (a * a) * t⁻¹ ∈ P₂ := c.tP₁ _ huP
  have hcomm2 : Commute (a * a) (t * (a * a) * t⁻¹) := c.comm _ huP _ hu'
  have hnz : a * a ∉ zpowers z := by
    intro hz
    apply hc2
    rw [c.t_eps hz]
    exact c.eps_sq hz
  have hw : (a * a) * (a * a) ∈ P₁ := P₁.mul_mem huP huP
  have hw1 : ((a * a) * (a * a)) * (t * ((a * a) * (a * a)) * t⁻¹) = 1 := by
    rw [show t * ((a * a) * (a * a)) * t⁻¹ = (t * (a * a) * t⁻¹) * (t * (a * a) * t⁻¹) by group]
    rw [← hc4]
    rw [Commute.mul_mul_mul_comm hcomm2.symm]
  have hwz : (a * a) * (a * a) ∈ zpowers z := c.mem_zpowers_of_mul_conj hw hw1
  rcases c.eps_cases hwz with h0 | h0
  · exfalso
    have : a * a = z := hinv _ huP h0 (fun h1 => hnz (by rw [h1]; exact one_mem _))
    exact hnz (by rw [this]; exact mem_zpowers z)
  · exact h0

theorem inv_of_conj {y a ε : G} (ha : a ∈ P₁) (hε : ε ∈ zpowers z) (hyS : y ∈ S)
    (hyP : ∀ p ∈ P₁, y * p * y⁻¹ ∈ P₁) (hyt : y * t = t * y)
    (hyc : y * (a * (t * a * t⁻¹) * ε) * y⁻¹ = (a * (t * a * t⁻¹) * ε)⁻¹) :
    y * (a * a) * y⁻¹ = (a * a)⁻¹ := by
  have haS : a ∈ S := c.P₁S ha
  have ha' : y * a * y⁻¹ ∈ P₁ := hyP a ha
  have hb : t * a * t⁻¹ ∈ P₂ := c.tP₁ a ha
  have hb' : t * (y * a * y⁻¹) * t⁻¹ ∈ P₂ := c.tP₁ _ ha'
  have hbS : t * a * t⁻¹ ∈ S := c.P₂S hb
  have hyty : y * t * y⁻¹ = t := by rw [hyt]; group
  have hyty' : y * t⁻¹ * y⁻¹ = t⁻¹ := by
    calc y * t⁻¹ * y⁻¹ = (y * t * y⁻¹)⁻¹ := by group
      _ = t⁻¹ := by rw [hyty]
  have hyb : y * (t * a * t⁻¹) * y⁻¹ = t * (y * a * y⁻¹) * t⁻¹ := by
    calc y * (t * a * t⁻¹) * y⁻¹ = (y * t * y⁻¹) * (y * a * y⁻¹) * (y * t⁻¹ * y⁻¹) := by group
      _ = t * (y * a * y⁻¹) * t⁻¹ := by rw [hyty, hyty']
  have hyε : y * ε * y⁻¹ = ε := by rw [c.eps_comm hε hyS]; group
  have hyc' : y * (a * (t * a * t⁻¹) * ε) * y⁻¹ =
      (y * a * y⁻¹) * (t * (y * a * y⁻¹) * t⁻¹) * ε := by
    calc y * (a * (t * a * t⁻¹) * ε) * y⁻¹
        = (y * a * y⁻¹) * (y * (t * a * t⁻¹) * y⁻¹) * (y * ε * y⁻¹) := by group
      _ = (y * a * y⁻¹) * (t * (y * a * y⁻¹) * t⁻¹) * ε := by rw [hyb, hyε]
  set a' := y * a * y⁻¹ with ha'def
  set b := t * a * t⁻¹ with hbdef
  set b' := t * a' * t⁻¹ with hb'def
  have hone : (a' * b' * ε) * (a * b * ε) = 1 := by
    have h1 : (y * (a * b * ε) * y⁻¹) * (a * b * ε) = 1 := by rw [hyc]; group
    rw [hyc'] at h1
    exact h1
  have hεab : Commute ε (a * b) :=
    ((show Commute a ε from c.eps_comm hε haS).mul_left
      (show Commute b ε from c.eps_comm hε hbS)).symm
  have hone2 : (a' * b') * (a * b) = 1 := by
    have := hone
    rw [Commute.mul_mul_mul_comm hεab, c.eps_sq hε, mul_one] at this
    exact this
  have hab' : a * b' = b' * a := c.comm a ha b' hb'
  have hXX : (a' * a) * (t * (a' * a) * t⁻¹) = 1 := by
    have e1 : t * (a' * a) * t⁻¹ = b' * b := by simp only [hb'def, hbdef]; group
    rw [e1]
    calc (a' * a) * (b' * b) = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hab']
      _ = (a' * b') * (a * b) := by group
      _ = 1 := hone2
  have hXz : a' * a ∈ zpowers z := c.mem_zpowers_of_mul_conj (P₁.mul_mem ha' ha) hXX
  have hXc : (a' * a) * a⁻¹ = a⁻¹ * (a' * a) := c.eps_comm hXz (S.inv_mem haS) |>.symm
  have hXX2 := c.eps_sq hXz
  calc y * (a * a) * y⁻¹ = a' * a' := by simp only [ha'def]; group
    _ = ((a' * a) * a⁻¹) * ((a' * a) * a⁻¹) := by group
    _ = (a' * a) * ((a⁻¹ * (a' * a)) * a⁻¹) := by group
    _ = (a' * a) * (((a' * a) * a⁻¹) * a⁻¹) := by rw [← hXc]
    _ = ((a' * a) * (a' * a)) * (a⁻¹ * a⁻¹) := by group
    _ = (a * a)⁻¹ := by rw [hXX2, one_mul]; group

theorem no_invol_coset (hz1 : z ≠ 1) {x v : G} (hxS : x ∈ S) (hx2 : x * x = z)
    (hx₁ : ∀ p ∈ P₁, x * p * x⁻¹ ∈ P₂) (hx₂ : ∀ p ∈ P₂, x * p * x⁻¹ ∈ P₁)
    (hv : v * x⁻¹ ∈ P₁ ⊔ P₂) (hv2 : v * v = 1) : False := by
  obtain ⟨p₁, hp₁, p₂, hp₂, hvp⟩ := A.mem_sup_of_commute c.comm hv
  have hp₁S : p₁ ∈ S := c.P₁S hp₁
  have hv' : v = p₁ * p₂ * x := by
    have : v = v * x⁻¹ * x := by group
    rw [this, hvp]
  obtain ⟨a, ha⟩ : ∃ a, a = x * p₂ * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = x * p₁ * x⁻¹ := ⟨_, rfl⟩
  have haP : a ∈ P₁ := ha ▸ hx₂ p₂ hp₂
  have hbP : b ∈ P₂ := hb ▸ hx₁ p₁ hp₁
  have h1 : p₁ * p₂ * b * a * z = 1 := by
    have e : v * v = p₁ * p₂ * b * a * (x * x) := by
      rw [hv', ha, hb]; group
    rw [hx2] at e
    rw [← e]; exact hv2
  have hzz := c.z_sq
  have hxinv : x⁻¹ = x * z := by
    refine (eq_inv_of_mul_eq_one_right (a := x) ?_).symm
    calc x * (x * z) = (x * x) * z := by group
      _ = 1 := by rw [hx2]; exact hzz
  have h2 : (p₁ * a) * (p₂ * b) = z := by
    have e : (p₁ * a) * (p₂ * b) = p₁ * p₂ * b * a := by
      calc (p₁ * a) * (p₂ * b) = p₁ * (a * p₂) * b := by group
        _ = p₁ * (p₂ * a) * b := by rw [c.comm a haP p₂ hp₂]
        _ = p₁ * p₂ * (a * b) := by group
        _ = p₁ * p₂ * (b * a) := by rw [c.comm a haP b hbP]
        _ = p₁ * p₂ * b * a := by group
    rw [e]
    have : p₁ * p₂ * b * a = z⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_eq_of_mul_eq_one_right hzz
  have hε₁ : p₁ * a ∈ P₁ := P₁.mul_mem hp₁ haP
  have hε₂ : p₁ * a ∈ P₂ := by
    have : p₁ * a = z * (p₂ * b)⁻¹ := by
      rw [← h2]; group
    rw [this]
    exact P₂.mul_mem c.zP₂ (P₂.inv_mem (P₂.mul_mem hp₂ hbP))
  have hεz : p₁ * a ∈ zpowers z := c.inf ⟨hε₁, hε₂⟩
  have hp₂' : p₂ = x⁻¹ * (p₁⁻¹ * (p₁ * a)) * x := by rw [ha]; group
  have hvε : v = p₁ * x * p₁⁻¹ * (p₁ * a) := by
    have hWS : p₁⁻¹ * (p₁ * a) ∈ S := S.mul_mem (S.inv_mem hp₁S) (c.P₁S (P₁.mul_mem hp₁ haP))
    have hzW : z * (p₁⁻¹ * (p₁ * a)) = (p₁⁻¹ * (p₁ * a)) * z := (c.zS _ hWS).symm
    calc v = p₁ * (x⁻¹ * (p₁⁻¹ * (p₁ * a)) * x) * x := by rw [hv', ← hp₂']
      _ = p₁ * x⁻¹ * (p₁⁻¹ * (p₁ * a)) * (x * x) := by group
      _ = p₁ * (x * z) * (p₁⁻¹ * (p₁ * a)) * z := by rw [hxinv, hx2]
      _ = p₁ * x * (z * (p₁⁻¹ * (p₁ * a)) * z) := by group
      _ = p₁ * x * ((p₁⁻¹ * (p₁ * a)) * z * z) := by rw [hzW]
      _ = p₁ * x * (p₁⁻¹ * (p₁ * a)) := by rw [mul_assoc _ z z, hzz, mul_one]
      _ = p₁ * x * p₁⁻¹ * (p₁ * a) := by group
  have hwS : p₁ * x * p₁⁻¹ ∈ S := S.mul_mem (S.mul_mem hp₁S hxS) (S.inv_mem hp₁S)
  have hww : (p₁ * x * p₁⁻¹) * (p₁ * x * p₁⁻¹) = z := by
    have hzp : p₁ * z * p₁⁻¹ = z := by
      calc p₁ * z * p₁⁻¹ = (z * p₁) * p₁⁻¹ := by rw [c.zS p₁ hp₁S]
        _ = z := by group
    calc (p₁ * x * p₁⁻¹) * (p₁ * x * p₁⁻¹) = p₁ * (x * x) * p₁⁻¹ := by group
      _ = z := by rw [hx2, hzp]
  have hvv : v * v = z := by
    have hεw : Commute (p₁ * a) (p₁ * x * p₁⁻¹) :=
      (show Commute (p₁ * x * p₁⁻¹) (p₁ * a) from c.eps_comm hεz hwS).symm
    rw [hvε, Commute.mul_mul_mul_comm hεw, hww, c.eps_sq hεz, mul_one]
  apply hz1
  rw [← hvv]; exact hv2

end PairCtx

section QuatSub

variable {P : Subgroup G} {N : ℕ} [NeZero N] (e : ↥P ≃* QuaternionGroup N)

include e

theorem quat_sub_invol {z : G} (hzP : z ∈ P) (hz2 : z * z = 1) (hz1 : z ≠ 1) {x : G} (hxP : x ∈ P)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : x = z := by
  have hsq : ∀ {w : G} (hw : w ∈ P), w * w = 1 → e ⟨w, hw⟩ * e ⟨w, hw⟩ = 1 := by
    intro w hw hw2
    rw [← map_mul]
    have : (⟨w, hw⟩ : ↥P) * ⟨w, hw⟩ = 1 := Subtype.ext (by simpa using hw2)
    rw [this, map_one]
  have hne : ∀ {w : G} (hw : w ∈ P), w ≠ 1 → e ⟨w, hw⟩ ≠ 1 := by
    intro w hw hw1 h
    apply hw1
    have := e.injective (h.trans (map_one e).symm)
    simpa using congrArg Subtype.val this
  have e1 := quat_invol_unique (hsq hxP hx2) (hne hxP hx1)
  have e2 := quat_invol_unique (hsq hzP hz2) (hne hzP hz1)
  have := e.injective (e1.trans e2.symm)
  simpa using congrArg Subtype.val this

theorem quat_sub_sq {z : G} (hzP : z ∈ P) (hz2 : z * z = 1) (hz1 : z ≠ 1) {w w' : G} (hw : w ∈ P)
    (hw' : w' ∈ P) (h : (w * w) * (w * w) = z) (h' : (w' * w') * (w' * w') = z) :
    w' * w' = w * w ∨ w' * w' = (w * w)⁻¹ := by
  have hsq : ∀ {w : G} (hw : w ∈ P), w * w ∈ P := fun hw => P.mul_mem hw hw
  have hz : ∀ {w : G} (hw : w ∈ P), (w * w) * (w * w) = z →
      (e ⟨w, hw⟩ * e ⟨w, hw⟩) * (e ⟨w, hw⟩ * e ⟨w, hw⟩) = QuaternionGroup.a N := by
    intro w hw hww
    have h1 : e ⟨z, hzP⟩ = QuaternionGroup.a N := by
      have hsq' : e ⟨z, hzP⟩ * e ⟨z, hzP⟩ = 1 := by
        rw [← map_mul]
        have : (⟨z, hzP⟩ : ↥P) * ⟨z, hzP⟩ = 1 := Subtype.ext (by simpa using hz2)
        rw [this, map_one]
      refine quat_invol_unique hsq' ?_
      intro h0
      apply hz1
      have := e.injective (h0.trans (map_one e).symm)
      simpa using congrArg Subtype.val this
    rw [← h1, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hww)
  rcases quat_sq_sq (hz hw h) (hz hw' h') with h1 | h1
  · left
    rw [← map_mul, ← map_mul] at h1
    have := e.injective h1
    simpa using congrArg Subtype.val this
  · right
    rw [← map_mul, ← map_mul, ← map_inv] at h1
    have := e.injective h1
    simpa using congrArg Subtype.val this

end QuatSub

section Cfg

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

theorem pairCtx_of_cfg7 (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    PairCtx z t S (Pof S K₁) (Pof S K₂) where
  z_sq := h.z_sq
  t_sq := h.t_sq
  zS := fun _ hs => Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_C hII hs)
  tS := h.ch.t_mem
  P₁S := inf_le_left
  P₂S := inf_le_left
  zP₁ := h.z_mem_P hII (Or.inl rfl)
  zP₂ := h.z_mem_P hII (Or.inr rfl)
  comm := h.P_comm hII
  inf := (h.P_inf hII).le
  tP₁ := h.tP₁
  tP₂ := h.tP₂

theorem S1_normalizes_P₂ (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {y : G}
    (hy : y ∈ S1 S K₁) : ∀ p ∈ Pof S K₂, y * p * y⁻¹ ∈ Pof S K₂ := fun p hp =>
  ⟨S.mul_mem (S.mul_mem hy.1 hp.1) (S.inv_mem hy.1),
    (Subgroup.mem_normalizer_iff.1 (h.S1_norm₂ hII hy) p).1 hp.2⟩

theorem S1_invol_mem (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {D : Subgroup G}
    (hD : Data74 z S K₁ K₂ t D) (hDinv : ∀ x ∈ D, x * x = 1 → x ∈ Pz S z) {x : G}
    (hx : x ∈ S1 S K₁) (hx2 : x * x = 1) : x ∈ Pz S z := by
  obtain ⟨hN, ⟨ι⟩⟩ := hD.quot
  have hC := pairCtx_of_cfg7 hII h
  have hDE : D ≤ S ⊓ centralizer ({t} : Set G) := le_sup_right.trans hD.prod.1.le
  have hPD : ∀ d ∈ D, d ∈ Pof S K₁ → d = 1 := by
    intro d hd hdP
    have hdt : d * t = t * d := Subgroup.mem_centralizer_singleton_iff.1 (hDE hd).2
    have hd2 : d ∈ Pof S K₂ := by
      have := h.tP₁ d hdP
      have e : t * d * t⁻¹ = d := by rw [← hdt]; group
      rwa [e] at this
    have hdz : d ∈ zpowers z := (h.P_inf hII).le ⟨hdP, hd2⟩
    rcases hC.eps_cases hdz with h1 | h1
    · exact h1
    · exfalso
      have hz : z ∈ zpowers z ⊔ zpowers t := mem_sup_left (mem_zpowers z)
      have : z ∈ (zpowers z ⊔ zpowers t) ⊓ D := ⟨hz, h1 ▸ hd⟩
      rw [hD.prod.2.2] at this
      exact h.z_ne (Subgroup.mem_bot.1 this)
  let π : ↥(S1 S K₁) →* ↥(S1 S K₁) ⧸ (Pof S K₁).subgroupOf (S1 S K₁) := QuotientGroup.mk' _
  let ρ : ↥(S1 S K₁) →* ↥D := ι.toMonoidHom.comp π
  let r : ↥D →* ↥D := ρ.comp (Subgroup.inclusion hD.le)
  have hinj : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : ρ ⟨(d : G), hD.le d.2⟩ = 1 := hd
    have h2 : π ⟨(d : G), hD.le d.2⟩ = 1 := by
      apply ι.injective
      rw [map_one]; exact h1
    have h3 : (⟨(d : G), hD.le d.2⟩ : ↥(S1 S K₁)) ∈ (Pof S K₁).subgroupOf (S1 S K₁) :=
      (QuotientGroup.eq_one_iff _).1 h2
    exact Subtype.ext (hPD d d.2 h3)
  have hsurj : Function.Surjective r := Finite.injective_iff_surjective.1 hinj
  obtain ⟨d, hd⟩ := hsurj (ρ ⟨x, hx⟩)
  have hd1 : π ⟨(d : G), hD.le d.2⟩ = π ⟨x, hx⟩ := by
    apply ι.injective
    exact hd
  have hdd : d * d = 1 := by
    apply hinj
    rw [map_mul, hd, ← map_mul, map_one]
    have : (⟨x, hx⟩ : ↥(S1 S K₁)) * ⟨x, hx⟩ = 1 := Subtype.ext (by simpa using hx2)
    rw [this, map_one]
  have hdd' : (d : G) * d = 1 := by simpa using congrArg Subtype.val hdd
  have hdP : (d : G) ∈ Pz S z := hDinv d d.2 hdd'
  have h4 : (d : G)⁻¹ * x ∈ Pof S K₁ := by
    have := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hd1)
    simpa using this
  have h5 : x = (d : G) * ((d : G)⁻¹ * x) := by group
  rw [h5]
  refine (Pz S z).mul_mem hdP ?_
  rw [h.Pz_eq_sup hII]
  exact mem_sup_left h4

theorem invols_of_S (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q)
    (hidx : (Pz S z).relIndex (S1 S K₁) = 2) {D : Subgroup G} (hD : Data74 z S K₁ K₂ t D)
    (hDinv : ∀ x ∈ D, x * x = 1 → x ∈ Pz S z) {u₁ y : G} (hu₁ : u₁ ∈ Pof S K₁)
    (hu₁sq : u₁ * u₁ = z) (hyD : y ∈ D) (hyP : y ∉ Pz S z)
    (hyy : y * y = u₁ * (t * u₁ * t⁻¹)) (hyi : y * u₁ * y⁻¹ = u₁⁻¹) :
    ∀ x ∈ S, orderOf x = 2 → x ∈ Pz S z ⊔ zpowers t := by
  have hC := pairCtx_of_cfg7 hII h
  have hzz := h.z_sq
  have hDE : D ≤ S ⊓ centralizer ({t} : Set G) := le_sup_right.trans hD.prod.1.le
  have hyS1 : y ∈ S1 S K₁ := hD.le hyD
  have hyS : y ∈ S := hyS1.1
  have htS : t ∈ S := h.ch.t_mem
  have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.1 (hDE hyD).2
  have hPeq := h.Pz_eq_sup hII
  have hu₂ : t * u₁ * t⁻¹ ∈ Pof S K₂ := h.tP₁ u₁ hu₁
  have hyu₂ : y * (t * u₁ * t⁻¹) * y⁻¹ = (t * u₁ * t⁻¹)⁻¹ := by
    have hyty : y * t * y⁻¹ = t := by rw [hyt]; group
    have hyty' : y * t⁻¹ * y⁻¹ = t⁻¹ := by
      calc y * t⁻¹ * y⁻¹ = (y * t * y⁻¹)⁻¹ := by group
        _ = t⁻¹ := by rw [hyty]
    calc y * (t * u₁ * t⁻¹) * y⁻¹ = (y * t * y⁻¹) * (y * u₁ * y⁻¹) * (y * t⁻¹ * y⁻¹) := by group
      _ = t * u₁⁻¹ * t⁻¹ := by rw [hyty, hyi, hyty']
      _ = (t * u₁ * t⁻¹)⁻¹ := by group
  have hu₁t : u₁ * t = t * (t * u₁ * t⁻¹) := by
    calc u₁ * t = u₁ * t⁻¹ := by rw [hC.t_inv]
      _ = (t * t) * u₁ * t⁻¹ := by rw [hC.t_sq]; group
      _ = t * (t * u₁ * t⁻¹) := by group
  have hv'sq : (t * y * u₁) * (t * y * u₁) = z := by
    calc (t * y * u₁) * (t * y * u₁) = t * y * (u₁ * t) * y * u₁ := by group
      _ = t * y * (t * (t * u₁ * t⁻¹)) * y * u₁ := by rw [hu₁t]
      _ = t * (y * t) * (t * u₁ * t⁻¹) * y * u₁ := by group
      _ = t * (t * y) * (t * u₁ * t⁻¹) * y * u₁ := by rw [hyt]
      _ = (t * t) * y * (t * u₁ * t⁻¹) * y * u₁ := by group
      _ = y * (t * u₁ * t⁻¹) * y * u₁ := by rw [hC.t_sq]; group
      _ = (y * (t * u₁ * t⁻¹) * y⁻¹) * (y * y) * u₁ := by group
      _ = (t * u₁ * t⁻¹)⁻¹ * (u₁ * (t * u₁ * t⁻¹)) * u₁ := by rw [hyu₂, hyy]
      _ = (t * u₁ * t⁻¹)⁻¹ * ((t * u₁ * t⁻¹) * u₁) * u₁ := by
          rw [hC.comm u₁ hu₁ _ hu₂]
      _ = u₁ * u₁ := by group
      _ = z := hu₁sq
  have hv'S : t * y * u₁ ∈ S := S.mul_mem (S.mul_mem htS hyS) (hC.P₁S hu₁)
  have hx₁ : ∀ p ∈ Pof S K₁, (t * y * u₁) * p * (t * y * u₁)⁻¹ ∈ Pof S K₂ := by
    intro p hp
    have h1 : u₁ * p * u₁⁻¹ ∈ Pof S K₁ :=
      (Pof S K₁).mul_mem ((Pof S K₁).mul_mem hu₁ hp) ((Pof S K₁).inv_mem hu₁)
    have h2 := h.S1_normalizes_P₁ y hyS1 _ h1
    have h3 := h.tP₁ _ h2
    have e : (t * y * u₁) * p * (t * y * u₁)⁻¹ = t * (y * (u₁ * p * u₁⁻¹) * y⁻¹) * t⁻¹ := by group
    rw [e]; exact h3
  have hx₂ : ∀ p ∈ Pof S K₂, (t * y * u₁) * p * (t * y * u₁)⁻¹ ∈ Pof S K₁ := by
    intro p hp
    have h1 : u₁ * p * u₁⁻¹ = p := by
      rw [hC.comm u₁ hu₁ p hp]; group
    have h2 := S1_normalizes_P₂ hII h hyS1 p hp
    have h3 := h.tP₂ _ h2
    have e : (t * y * u₁) * p * (t * y * u₁)⁻¹ = t * (y * (u₁ * p * u₁⁻¹) * y⁻¹) * t⁻¹ := by group
    rw [e, h1]; exact h3
  intro x hxS hx2o
  have hx2 : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hx2o
  by_cases hxS₁ : x ∈ S1 S K₁
  · exact mem_sup_left (S1_invol_mem hII h hD hDinv hxS₁ hx2)
  · rcases A.relIndex_two_pigeon h.S1_relIndex hxS htS with h1 | h1 | h1
    · exact absurd h1 hxS₁
    · exact absurd h1 h.t_nS1
    ·
      have hs' : t⁻¹ * x ∈ S1 S K₁ := by
        have := (S1 S K₁).inv_mem h1
        simpa using this
      have hxe : x = t * (t⁻¹ * x) := by group
      rcases A.relIndex_two_pigeon hidx hs' hyS1 with h2 | h2 | h2
      ·
        have hx' : x = (t * (t⁻¹ * x) * t⁻¹) * t := by group
        rw [hx']
        exact (Pz S z ⊔ zpowers t).mul_mem
          (mem_sup_left (h.normP hII t htS _ h2)) (mem_sup_right (mem_zpowers t))
      · exact absurd h2 hyP
      · exfalso
        have hpP : (t⁻¹ * x)⁻¹ * y ∈ Pz S z := h2
        have hxp : x = t * y * ((t⁻¹ * x)⁻¹ * y)⁻¹ := by group
        have hu₁P : u₁ ∈ Pz S z := by rw [hPeq]; exact mem_sup_left hu₁
        have hcoset : x * (t * y * u₁)⁻¹ ∈ Pof S K₁ ⊔ Pof S K₂ := by
          rw [← hPeq]
          have e : x * (t * y * u₁)⁻¹ =
              (t * y) * (((t⁻¹ * x)⁻¹ * y)⁻¹ * u₁⁻¹) * (t * y)⁻¹ := by
            conv_lhs => rw [hxp]
            group
          rw [e]
          exact h.normP hII (t * y) (S.mul_mem htS hyS) _
            ((Pz S z).mul_mem ((Pz S z).inv_mem hpP) ((Pz S z).inv_mem hu₁P))
        exact hC.no_invol_coset h.z_ne hv'S hv'sq hx₁ hx₂ hcoset hx2

theorem l76_struct (hII : II4_4_4_center) (hq : II4_4_quat) : L76_struct := by
  intro G _ _ z S K₁ K₂ t u q h hidx D hD hsd _h16
  have hC := pairCtx_of_cfg7 hII h
  have hzz := h.z_sq
  have hz1 := h.z_ne
  have hDE : D ≤ S ⊓ centralizer ({t} : Set G) := le_sup_right.trans hD.prod.1.le
  obtain ⟨n, hn3, ⟨e⟩⟩ := hq G h.std.std.simple z h.std.std.orderOf_z S K₁ h.std.std.sylow
    (h.std.std.comp_isPCompIn (Or.inl rfl)) (h.std.std.comp_pRank (Or.inl rfl))
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hzP₁ : z ∈ Pof S K₁ := hC.zP₁
  have hinv : ∀ x ∈ Pof S K₁, x * x = 1 → x ≠ 1 → x = z := fun x hx h2 h1 =>
    quat_sub_invol e hzP₁ hzz hz1 hx h2 h1
  obtain ⟨nD, hnD, ⟨eD⟩⟩ := hsd
  obtain ⟨m, k, hmk, hk2, ⟨f⟩⟩ := hD.inter_dih
  have : NeZero k := ⟨by omega⟩
  have : Fact (1 < k) := ⟨by omega⟩
  have hidxM : (D ⊓ Pz S z).relIndex D = 2 := hD.index_eq.trans hidx
  have hsr : ∀ i : ZMod k, ((f.symm (DihedralGroup.sr i) : ↥(D ⊓ Pz S z)) : G) *
      ((f.symm (DihedralGroup.sr i) : ↥(D ⊓ Pz S z)) : G) = 1 ∧
      ((f.symm (DihedralGroup.sr i) : ↥(D ⊓ Pz S z)) : G) ≠ 1 := by
    intro i
    refine ⟨?_, ?_⟩
    · have : f.symm (DihedralGroup.sr i) * f.symm (DihedralGroup.sr i) = 1 := by
        rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
      simpa using congrArg Subtype.val this
    · intro h1
      have : f.symm (DihedralGroup.sr i) = 1 := Subtype.ext (by simpa using h1)
      have h2 := congrArg f this
      rw [MulEquiv.apply_symm_apply, map_one, DihedralGroup.one_def] at h2
      cases h2
  obtain ⟨c, y, hcM, hyD, hyM, hcy, hyy, hc2, hc4, hcen, hDinv⟩ :=
    sd_data eD hnD inf_le_left hidxM (a := ((f.symm (DihedralGroup.sr 0) : ↥(D ⊓ Pz S z)) : G))
      (b := ((f.symm (DihedralGroup.sr 1) : ↥(D ⊓ Pz S z)) : G))
      (f.symm (DihedralGroup.sr 0)).2 (f.symm (DihedralGroup.sr 1)).2 (hsr 0).1 (hsr 1).1
      (hsr 0).2 (hsr 1).2 (by
        intro h1
        have := f.symm.injective (Subtype.ext h1)
        have h2 := DihedralGroup.sr.inj this
        exact zero_ne_one h2)
  have hcD : c ∈ D := hcM.1
  have hct : t * c * t⁻¹ = c := by
    have : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.1 (hDE hcD).2
    rw [← this]; group
  have hcP : c ∈ Pof S K₁ ⊔ Pof S K₂ := by rw [← h.Pz_eq_sup hII]; exact hcM.2
  obtain ⟨a, ha, ε, hε, hca⟩ := hC.CPt_form hcP hct
  subst hca
  obtain ⟨hu4, hcc⟩ := hC.u1_of_c hinv ha hε hc2 hc4
  have hyS1 : y ∈ S1 S K₁ := hD.le hyD
  have hyS : y ∈ S := hyS1.1
  have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.1 (hDE hyD).2
  have hyi : y * (a * a) * y⁻¹ = (a * a)⁻¹ :=
    hC.inv_of_conj ha hε hyS (h.S1_normalizes_P₁ y hyS1) hyt hcy
  have huP : a * a ∈ Pof S K₁ := (Pof S K₁).mul_mem ha ha
  have hyP : y ∉ Pz S z := fun hP => hyM ⟨hyD, hP⟩
  have hyy' : y * y = (a * a) * (t * (a * a) * t⁻¹) := hyy.trans hcc
  refine ⟨a * a, huP, hu4, ?_, hcen.trans (by rw [hcc]), ⟨y, hyD, hyP, hyy', hyi⟩, ?_⟩
  · intro s hs
    have hsa : s * a * s⁻¹ ∈ Pof S K₁ := h.S1_normalizes_P₁ s hs a ha
    have hsz : s * z * s⁻¹ = z := by
      have := hC.zS s hs.1
      rw [this]; group
    have h1 : ((s * a * s⁻¹) * (s * a * s⁻¹)) * ((s * a * s⁻¹) * (s * a * s⁻¹)) = z := by
      calc ((s * a * s⁻¹) * (s * a * s⁻¹)) * ((s * a * s⁻¹) * (s * a * s⁻¹))
          = s * ((a * a) * (a * a)) * s⁻¹ := by group
        _ = z := by rw [hu4, hsz]
    have h2 := quat_sub_sq e hzP₁ hzz hz1 ha hsa hu4 h1
    have e1 : (s * a * s⁻¹) * (s * a * s⁻¹) = s * (a * a) * s⁻¹ := by group
    rw [e1] at h2
    exact h2
  · exact invols_of_S hII h hidx hD (fun x hx hx2 => (hDinv x hx hx2).2) huP hu4 hyD hyP hyy' hyi

end Cfg

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf
