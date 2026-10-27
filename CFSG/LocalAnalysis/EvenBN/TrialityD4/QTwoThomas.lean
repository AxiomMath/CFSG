module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Invariants
import CFSG.LocalAnalysis.EvenBN.TrialityD4.Levi
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped commutatorElement

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem tr_coe (l : d.Γ₀) : d.tr (l : d.Γ) = l := by
  apply Subtype.ext
  rw [coe_fixedTrace, apply_coe_fixedSubfield, apply_coe_fixedSubfield, CharTwo.add_self_eq_zero,
    zero_add]

theorem tr_zero : d.tr 0 = 0 := by
  have h := d.tr_coe 0
  rwa [ZeroMemClass.coe_zero] at h

theorem exists_σ_mul_σσ_eq {γ : d.Γ} (hγ : γ ≠ 0) : ∃ β : d.Γ, d.σ β * d.σ (d.σ β) = γ := by
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (d.nm γ)
  refine ⟨(s : d.Γ) / γ, ?_⟩
  have hs' : (s : d.Γ) * s = γ * d.σ γ * d.σ (d.σ γ) := by
    rw [← Subfield.coe_mul, ← hs, coe_fixedNorm]
  have h1 : d.σ γ ≠ 0 := (map_ne_zero d.σ).2 hγ
  have h2 : d.σ (d.σ γ) ≠ 0 := (map_ne_zero d.σ).2 h1
  simp only [map_div₀, apply_coe_fixedSubfield]
  field_simp
  rw [sq, hs']
  ring

theorem σ_twist_eq {c e : d.Γ} (he : e ≠ 0) (hce : d.tr (c * e) = 0) :
    d.σ (c * e / (d.σ e * d.σ (d.σ e))) * d.σ (d.σ e) +
      d.σ (d.σ (c * e / (d.σ e * d.σ (d.σ e)))) * d.σ e = c := by
  have h1 : d.σ e ≠ 0 := (map_ne_zero d.σ).2 he
  have h2 : d.σ (d.σ e) ≠ 0 := (map_ne_zero d.σ).2 h1
  have hrel : c * e + d.σ c * d.σ e + d.σ (d.σ c) * d.σ (d.σ e) = 0 := by
    have h := congrArg Subtype.val hce
    rw [coe_fixedTrace, map_mul, map_mul] at h
    exact h
  have hsum : d.σ c * d.σ e + d.σ (d.σ c) * d.σ (d.σ e) = c * e := by
    rw [← CharTwo.neg_eq (c * e)]
    linear_combination hrel
  have key : d.σ (c * e / (d.σ e * d.σ (d.σ e))) * d.σ (d.σ e) +
      d.σ (d.σ (c * e / (d.σ e * d.σ (d.σ e)))) * d.σ e =
        (d.σ c * d.σ e + d.σ (d.σ c) * d.σ (d.σ e)) / e := by
    simp only [map_div₀, map_mul, d.σ_cube]
    field_simp
  rw [key, hsum, mul_div_assoc, div_self he, mul_one]

@[expose] noncomputable def dvc (g : X) : d.Γ₀ × d.Γ × d.Γ × d.Γ₀ :=
  ((d.nfc g).2.1, (d.nfc g).2.2.1, (d.nfc g).2.2.2.1, (d.nfc g).2.2.2.2.1)

theorem dvc_nf (b : d.Γ₀) (c e : d.Γ) (g h : d.Γ₀) :
    d.dvc (d.nf (0, b, c, e, g, h)) = (b, c, e, g) := by
  simp only [dvc, nfc_nf]

theorem nf_eq (b : d.Γ₀) (c e : d.Γ) (g h : d.Γ₀) :
    d.nf (0, b, c, e, g, h) = d.x₂ b * d.x₃ c * d.x₄ e * d.x₅ g * d.x₆ h := by
  simp only [nf_apply, d.x₁_zero, one_mul]

theorem x₃_mem_D (c : d.Γ) : d.x₃ c ∈ d.D := d.F_le_D (d.x₃_mem_F c)

theorem x₄_mem_D (e : d.Γ) : d.x₄ e ∈ d.D := d.F_le_D (d.W_le_F (d.x₄_mem_W e))

theorem x₅_mem_D (g : d.Γ₀) : d.x₅ g ∈ d.D := d.F_le_D (d.W_le_F (d.x₅_mem_W g))

theorem x₆_mem_D (h : d.Γ₀) : d.x₆ h ∈ d.D := d.F_le_D (d.W_le_F (d.x₆_mem_W h))

theorem dvc_x₂ (b : d.Γ₀) : d.dvc (d.x₂ b) = (b, 0, 0, 0) := by
  rw [← d.nf_x₂, dvc_nf]

theorem dvc_x₃ (c : d.Γ) : d.dvc (d.x₃ c) = (0, c, 0, 0) := by
  rw [← d.nf_x₃, dvc_nf]

theorem dvc_x₄ (e : d.Γ) : d.dvc (d.x₄ e) = (0, 0, e, 0) := by
  rw [← d.nf_x₄, dvc_nf]

theorem dvc_x₅ (g : d.Γ₀) : d.dvc (d.x₅ g) = (0, 0, 0, g) := by
  rw [← d.nf_x₅, dvc_nf]

theorem dvc_x₆ (h : d.Γ₀) : d.dvc (d.x₆ h) = 0 := by
  rw [show d.x₆ h = d.nf (0, 0, 0, 0, 0, h) by
    simp only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero, d.x₅_zero, one_mul],
    dvc_nf]
  rfl

theorem dvc_bc_mul {y y' : X} (hy : y ∈ d.D) (hy' : y' ∈ d.D) :
    ((d.dvc (y * y')).1, (d.dvc (y * y')).2.1) =
      ((d.dvc y).1, (d.dvc y).2.1) + ((d.dvc y').1, (d.dvc y').2.1) :=
  d.nfc_bc_mul hy hy'

theorem mem_W_of_dvc {y : X} (hy : y ∈ d.D) (h1 : (d.dvc y).1 = 0) (h2 : (d.dvc y).2.1 = 0) :
    y ∈ d.W := by
  obtain ⟨b, c, w, hw, rfl⟩ := d.mem_D_iff_x₂_x₃.1 hy
  obtain ⟨hb, hc⟩ := d.nfc_x₂_x₃_mul (b := b) (c := c) hw
  have hb' : b = 0 := hb.symm.trans h1
  have hc' : c = 0 := hc.symm.trans h2
  rw [hb', hc', d.x₂_zero, d.x₃_zero, one_mul, one_mul]
  exact hw

theorem u_conj_mem_D {y : X} (hy : y ∈ d.D) : d.u * y * d.u⁻¹ ∈ d.D :=
  (mem_normalizer_iff.1 d.u_mem_normalizer_D y).1 hy

theorem x₁_conj_mem_D (β : d.Γ) {y : X} (hy : y ∈ d.D) : d.x₁ β * y * (d.x₁ β)⁻¹ ∈ d.D :=
  (mem_normalizer_iff.1 (d.S_le_normalizer_D (d.U₁_le_S (d.x₁_mem_U₁ β))) y).1 hy

theorem dvc_conj_u_bc {y : X} (hy : y ∈ d.D) :
    (d.dvc (d.u * y * d.u⁻¹)).1 = (d.dvc y).2.2.2 ∧
      (d.dvc (d.u * y * d.u⁻¹)).2.1 = (d.dvc y).2.2.1 := by
  obtain ⟨b, c, e, g, h, rfl⟩ := d.mem_D_coords hy
  have hz : d.u * d.nf (0, b, c, e, g, h) * d.u⁻¹ =
      d.x₅ b * d.x₄ c * d.x₃ e * d.x₂ g * d.x₆ h := by
    rw [d.nf_eq]
    calc d.u * (d.x₂ b * d.x₃ c * d.x₄ e * d.x₅ g * d.x₆ h) * d.u⁻¹ =
        (d.u * d.x₂ b * d.u⁻¹) * (d.u * d.x₃ c * d.u⁻¹) * (d.u * d.x₄ e * d.u⁻¹) *
          (d.u * d.x₅ g * d.u⁻¹) * (d.u * d.x₆ h * d.u⁻¹) := by group
      _ = d.x₅ b * d.x₄ c * d.x₃ e * d.x₂ g * d.x₆ h := by
        rw [d.u_conj_x₂, d.u_conj_x₃_eq_x₄, d.u_conj_x₄_eq_x₃, d.u_conj_x₅, d.u_conj_x₆]
  have key := d.dvc_bc_mul (mul_mem (mul_mem (mul_mem (d.x₅_mem_D b) (d.x₄_mem_D c))
    (d.x₃_mem_D e)) (d.x₂_mem_D g)) (d.x₆_mem_D h)
  rw [d.dvc_bc_mul (mul_mem (mul_mem (d.x₅_mem_D b) (d.x₄_mem_D c)) (d.x₃_mem_D e))
      (d.x₂_mem_D g),
    d.dvc_bc_mul (mul_mem (d.x₅_mem_D b) (d.x₄_mem_D c)) (d.x₃_mem_D e),
    d.dvc_bc_mul (d.x₅_mem_D b) (d.x₄_mem_D c), dvc_x₂, dvc_x₃, dvc_x₄, dvc_x₅, dvc_x₆] at key
  rw [hz, dvc_nf]
  simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.fst_zero, Prod.snd_zero,
    Prod.mk.injEq] at key
  exact key

theorem dvc_conj_u {y : X} (hy : y ∈ d.D) :
    d.dvc (d.u * y * d.u⁻¹) =
      ((d.dvc y).2.2.2, (d.dvc y).2.2.1, (d.dvc y).2.1, (d.dvc y).1) := by
  obtain ⟨h1, h2⟩ := d.dvc_conj_u_bc hy
  obtain ⟨h3, h4⟩ := d.dvc_conj_u_bc (d.u_conj_mem_D hy)
  have hyy : d.u * (d.u * y * d.u⁻¹) * d.u⁻¹ = y := by
    rw [d.u_inv]
    calc d.u * (d.u * y * d.u) * d.u = (d.u * d.u) * y * (d.u * d.u) := by group
      _ = y := by rw [d.u_mul_self, one_mul, mul_one]
  rw [hyy] at h3 h4
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h4.symm h3.symm))

theorem dvc_mul {y y' : X} (hy : y ∈ d.D) (hy' : y' ∈ d.D) :
    d.dvc (y * y') = d.dvc y + d.dvc y' := by
  have h1 := d.dvc_bc_mul hy hy'
  have h2 := d.dvc_bc_mul (d.u_conj_mem_D hy) (d.u_conj_mem_D hy')
  rw [show d.u * y * d.u⁻¹ * (d.u * y' * d.u⁻¹) = d.u * (y * y') * d.u⁻¹ by group,
    d.dvc_conj_u (mul_mem hy hy'), d.dvc_conj_u hy, d.dvc_conj_u hy'] at h2
  simp only [Prod.mk_add_mk, Prod.mk.injEq] at h1 h2
  exact Prod.ext h1.1 (Prod.ext h1.2 (Prod.ext h2.2 h2.1))

theorem dvc_conj_x₁ (β : d.Γ) {y : X} (hy : y ∈ d.D) :
    d.dvc (d.x₁ β * y * (d.x₁ β)⁻¹) =
      ((d.dvc y).1, (d.dvc y).2.1 + β * ((d.dvc y).1 : d.Γ),
        (d.dvc y).2.2.1 + d.σ β * d.σ (d.σ β) * ((d.dvc y).1 : d.Γ) +
          (d.σ β * d.σ (d.σ (d.dvc y).2.1) + d.σ (d.σ β) * d.σ (d.dvc y).2.1),
        (d.dvc y).2.2.2 + d.nm β * (d.dvc y).1 + d.tr (β * d.σ β * d.σ (d.σ (d.dvc y).2.1)) +
          d.tr (β * (d.dvc y).2.2.1)) := by
  obtain ⟨b, c, e, g, h, rfl⟩ := d.mem_D_coords hy
  rw [dvc_nf]
  have e5 : d.x₁ β * d.x₅ g * (d.x₁ β)⁻¹ = d.x₅ g := mul_mul_inv_eq_of_commute (d.commute₁₅ β g)
  have e6 : d.x₁ β * d.x₆ h * (d.x₁ β)⁻¹ = d.x₆ h := mul_mul_inv_eq_of_commute (d.commute₁₆ β h)
  have ec : ∀ z : X, d.x₁ β * z * (d.x₁ β)⁻¹ = ⁅d.x₁ β, z⁆ * z := fun z => by
    rw [commutatorElement_def]
    group
  have hconj : d.x₁ β * d.nf (0, b, c, e, g, h) * (d.x₁ β)⁻¹ =
      (⁅d.x₁ β, d.x₂ b⁆ * d.x₂ b) * (⁅d.x₁ β, d.x₃ c⁆ * d.x₃ c) * (⁅d.x₁ β, d.x₄ e⁆ * d.x₄ e) *
        d.x₅ g * d.x₆ h := by
    rw [← ec, ← ec, ← ec, ← e5, ← e6, d.nf_eq]
    group
  rw [hconj, d.comm₁₂, d.comm₁₃, d.comm₁₄]
  simp (disch := apply_rules [mul_mem, d.x₂_mem_D, d.x₃_mem_D, d.x₄_mem_D, d.x₅_mem_D,
    d.x₆_mem_D]) only [d.dvc_mul]
  simp only [dvc_x₂, dvc_x₃, dvc_x₄, dvc_x₅, dvc_x₆]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] <;> ring

theorem mul_add_tr_eq_zero_of_mul_self {y : X} (hy : y ∈ d.D) (hy2 : y * y = 1) :
    (d.dvc y).1 * (d.dvc y).2.2.2 + d.tr ((d.dvc y).2.1 * (d.dvc y).2.2.1) = 0 := by
  obtain ⟨b, c, e, g, h, rfl⟩ := d.mem_D_coords hy
  rw [dvc_nf]
  set A := d.x₂ b * d.x₅ g with hA
  set B := d.x₃ c * d.x₄ e with hB
  have hA2 : A * A = d.x₆ (b * g) := by
    rw [hA, ← d.comm₂₅, commutatorElement_def, d.x₂_inv, d.x₅_inv]
    group
  have hB2 : B * B = d.x₆ (d.tr (c * e)) := by
    rw [hB, ← d.comm₃₄, commutatorElement_def, d.x₃_inv, d.x₄_inv]
    group
  have hy' : d.nf (0, b, c, e, g, h) = A * B * d.x₆ h := by
    rw [d.nf_eq, hA, hB]
    calc d.x₂ b * d.x₃ c * d.x₄ e * d.x₅ g * d.x₆ h =
        d.x₂ b * d.x₃ c * (d.x₄ e * d.x₅ g) * d.x₆ h := by group
      _ = d.x₂ b * (d.x₃ c * d.x₅ g) * d.x₄ e * d.x₆ h := by rw [(d.commute₄₅ e g).eq]; group
      _ = d.x₂ b * d.x₅ g * (d.x₃ c * d.x₄ e) * d.x₆ h := by rw [(d.commute₃₅ c g).eq]; group
  have hAB : A * B = B * A := by
    rw [hA, hB]
    exact (((d.commute₂₃ b c).mul_right (d.commute₂₄ b e)).mul_left
      (((d.commute₃₅ c g).symm).mul_right ((d.commute₄₅ e g).symm))).eq
  have hZA : d.x₆ h * A = A * d.x₆ h := by
    rw [hA]
    exact (((d.commute₂₆ b h).symm).mul_right ((d.commute₅₆ g h).symm)).eq
  have hZB : d.x₆ h * B = B * d.x₆ h := by
    rw [hB]
    exact (((d.commute₃₆ c h).symm).mul_right ((d.commute₄₆ e h).symm)).eq
  have hZ : Commute (d.x₆ h) (A * B) := Commute.mul_right hZA hZB
  have hBA : Commute B A := hAB.symm
  have hsq : d.nf (0, b, c, e, g, h) * d.nf (0, b, c, e, g, h) =
      d.x₆ (b * g + d.tr (c * e)) := by
    calc d.nf (0, b, c, e, g, h) * d.nf (0, b, c, e, g, h) =
        A * B * d.x₆ h * (A * B * d.x₆ h) := by rw [hy']
      _ = A * B * (A * B) * (d.x₆ h * d.x₆ h) := hZ.mul_mul_mul_comm (A * B) (d.x₆ h)
      _ = A * A * (B * B) * (d.x₆ h * d.x₆ h) := by rw [hBA.mul_mul_mul_comm A B]
      _ = d.x₆ (b * g + d.tr (c * e)) := by rw [hA2, hB2, d.x₆_mul_self, mul_one, ← d.x₆_add]
  rw [hsq] at hy2
  exact d.x₆_injective (hy2.trans d.x₆_zero.symm)

theorem exists_conj_mem_W_of_dvc_eq {y : X} (hy : y ∈ d.D) {c : d.Γ} {g : d.Γ₀} (hg : g ≠ 0)
    (hdy : d.dvc y = (0, c, 0, g)) :
    ∃ n ∈ normalizer (d.V : Set X), n * y * n⁻¹ ∈ d.W := by
  by_cases hc : c = 0
  · refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact d.mem_W_of_dvc hy (by rw [hdy]) (by rw [hdy, hc])
  have hg' : (g : d.Γ) ≠ 0 := fun h0 => hg (Subtype.ext h0)
  obtain ⟨β, hβ⟩ := d.exists_σ_mul_σσ_eq (div_ne_zero hc hg')
  have hu := d.u_mem_normalizer_V
  have hx := d.S_le_normalizer_V (d.U₁_le_S (d.x₁_mem_U₁ β))
  refine ⟨d.u * d.x₁ β * d.u⁻¹, mul_mem (mul_mem hu hx) (inv_mem hu), ?_⟩
  have e : d.u * d.x₁ β * d.u⁻¹ * y * (d.u * d.x₁ β * d.u⁻¹)⁻¹ =
      d.u * (d.x₁ β * (d.u * y * d.u⁻¹) * (d.x₁ β)⁻¹) * d.u⁻¹ := by
    simp only [mul_inv_rev, d.u_inv]
    group
  have hy₁ := d.u_conj_mem_D hy
  have hy₂ := d.x₁_conj_mem_D β hy₁
  rw [e]
  refine d.mem_W_of_dvc (d.u_conj_mem_D hy₂) ?_ ?_
  · rw [d.dvc_conj_u hy₂, d.dvc_conj_x₁ β hy₁, d.dvc_conj_u hy, hdy]
    simp only [map_zero, mul_zero, d.tr_zero, zero_add, add_zero]
    have hβc : β * c = ((d.nm β * g : d.Γ₀) : d.Γ) := by
      rw [Subfield.coe_mul, coe_fixedNorm, mul_assoc β, hβ]
      field_simp
    rw [hβc, d.tr_coe, add_self_Γ₀]
  · rw [d.dvc_conj_u hy₂, d.dvc_conj_x₁ β hy₁, d.dvc_conj_u hy, hdy]
    simp only [map_zero, mul_zero, add_zero]
    rw [hβ, div_mul_cancel₀ c hg', CharTwo.add_self_eq_zero]

theorem exists_conj_mem_W_of_fst_ne_zero {y : X} (hy : y ∈ d.D) (hy2 : y * y = 1)
    (hb : (d.dvc y).1 ≠ 0) : ∃ n ∈ normalizer (d.V : Set X), n * y * n⁻¹ ∈ d.W := by
  have hb' : ((d.dvc y).1 : d.Γ) ≠ 0 := fun h0 => hb (Subtype.ext h0)
  set β : d.Γ := (d.dvc y).2.1 / ((d.dvc y).1 : d.Γ) with hβ
  set y₁ := d.x₁ β * y * (d.x₁ β)⁻¹ with hy₁
  have hy₁D : y₁ ∈ d.D := d.x₁_conj_mem_D β hy
  have hy₁2 : y₁ * y₁ = 1 := by
    rw [hy₁, show d.x₁ β * y * (d.x₁ β)⁻¹ * (d.x₁ β * y * (d.x₁ β)⁻¹) =
      d.x₁ β * (y * y) * (d.x₁ β)⁻¹ by group, hy2, mul_one, mul_inv_cancel]
  have hd₁ := d.dvc_conj_x₁ β hy
  rw [← hy₁] at hd₁
  have hc₁ : (d.dvc y₁).2.1 = 0 := by
    rw [hd₁, hβ, div_mul_cancel₀ _ hb', CharTwo.add_self_eq_zero]
  have hb₁ : (d.dvc y₁).1 = (d.dvc y).1 := by rw [hd₁]
  have hg₁ : (d.dvc y₁).2.2.2 = 0 := by
    have h := d.mul_add_tr_eq_zero_of_mul_self hy₁D hy₁2
    rw [hc₁, zero_mul, d.tr_zero, add_zero, hb₁] at h
    exact (mul_eq_zero.1 h).resolve_left hb
  set y₂ := d.u * y₁ * d.u⁻¹ with hy₂
  have hy₂D : y₂ ∈ d.D := d.u_conj_mem_D hy₁D
  have hd₂ : d.dvc y₂ = (0, (d.dvc y₁).2.2.1, 0, (d.dvc y).1) := by
    rw [hy₂, d.dvc_conj_u hy₁D, hg₁, hc₁, hb₁]
  obtain ⟨n, hn, hny⟩ := d.exists_conj_mem_W_of_dvc_eq hy₂D hb hd₂
  have hu := d.u_mem_normalizer_V
  have hx := d.S_le_normalizer_V (d.U₁_le_S (d.x₁_mem_U₁ β))
  refine ⟨n * d.u * d.x₁ β, mul_mem (mul_mem hn hu) hx, ?_⟩
  rw [show n * d.u * d.x₁ β * y * (n * d.u * d.x₁ β)⁻¹ = n * y₂ * n⁻¹ by
    rw [hy₂, hy₁]; group]
  exact hny

theorem exists_conj_mem_W_of_mem_D {y : X} (hy : y ∈ d.D) (hy2 : y * y = 1) :
    ∃ n ∈ normalizer (d.V : Set X), n * y * n⁻¹ ∈ d.W := by
  have hu := d.u_mem_normalizer_V
  have hrel := d.mul_add_tr_eq_zero_of_mul_self hy hy2
  by_cases hb : (d.dvc y).1 ≠ 0
  · exact d.exists_conj_mem_W_of_fst_ne_zero hy hy2 hb
  rw [not_not] at hb
  by_cases hc : (d.dvc y).2.1 = 0
  · exact ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]; exact d.mem_W_of_dvc hy hb hc⟩
  have hyu : d.u * y * d.u⁻¹ ∈ d.D := d.u_conj_mem_D hy
  have hyu2 : d.u * y * d.u⁻¹ * (d.u * y * d.u⁻¹) = 1 := by
    rw [show d.u * y * d.u⁻¹ * (d.u * y * d.u⁻¹) = d.u * (y * y) * d.u⁻¹ by group, hy2,
      mul_one, mul_inv_cancel]
  by_cases hg : (d.dvc y).2.2.2 ≠ 0
  ·
    obtain ⟨n, hn, hny⟩ := d.exists_conj_mem_W_of_fst_ne_zero hyu hyu2
      (by rw [d.dvc_conj_u hy]; exact hg)
    refine ⟨n * d.u, mul_mem hn hu, ?_⟩
    rw [show n * d.u * y * (n * d.u)⁻¹ = n * (d.u * y * d.u⁻¹) * n⁻¹ by group]
    exact hny
  rw [not_not] at hg
  by_cases he : (d.dvc y).2.2.1 = 0
  ·
    refine ⟨d.u, hu, d.mem_W_of_dvc hyu ?_ ?_⟩
    · rw [d.dvc_conj_u hy]
      exact hg
    · rw [d.dvc_conj_u hy]
      exact he
  rw [hb, hg, mul_zero, zero_add] at hrel
  set c := (d.dvc y).2.1 with hcdef
  set e := (d.dvc y).2.2.1 with hedef
  set β : d.Γ := c * e / (d.σ e * d.σ (d.σ e)) with hβ
  have hx := d.S_le_normalizer_V (d.U₁_le_S (d.x₁_mem_U₁ β))
  set m := d.u * d.x₁ β * d.u⁻¹ with hm
  have hmN : m ∈ normalizer (d.V : Set X) := mul_mem (mul_mem hu hx) (inv_mem hu)
  have hz₁ := d.x₁_conj_mem_D β hyu
  have em : m * y * m⁻¹ = d.u * (d.x₁ β * (d.u * y * d.u⁻¹) * (d.x₁ β)⁻¹) * d.u⁻¹ := by
    rw [hm]
    simp only [mul_inv_rev, d.u_inv]
    group
  have hmyD : m * y * m⁻¹ ∈ d.D := by
    rw [em]
    exact d.u_conj_mem_D hz₁
  have hmy2 : m * y * m⁻¹ * (m * y * m⁻¹) = 1 := by
    rw [show m * y * m⁻¹ * (m * y * m⁻¹) = m * (y * y) * m⁻¹ by group, hy2, mul_one,
      mul_inv_cancel]
  have hd : (d.dvc (m * y * m⁻¹)).2.1 = 0 := by
    rw [em, d.dvc_conj_u hz₁, d.dvc_conj_x₁ β hyu, d.dvc_conj_u hy, hb, hg]
    simp only [ZeroMemClass.coe_zero, mul_zero, add_zero]
    rw [show d.σ β * d.σ (d.σ e) + d.σ (d.σ β) * d.σ e = c from d.σ_twist_eq he hrel,
      CharTwo.add_self_eq_zero]
  by_cases hb₂ : (d.dvc (m * y * m⁻¹)).1 = 0
  · exact ⟨m, hmN, d.mem_W_of_dvc hmyD hb₂ hd⟩
  obtain ⟨n, hn, hny⟩ := d.exists_conj_mem_W_of_fst_ne_zero hmyD hmy2 hb₂
  refine ⟨n * m, mul_mem hn hmN, ?_⟩
  rw [show n * m * y * (n * m)⁻¹ = n * (m * y * m⁻¹) * n⁻¹ by group]
  exact hny

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
