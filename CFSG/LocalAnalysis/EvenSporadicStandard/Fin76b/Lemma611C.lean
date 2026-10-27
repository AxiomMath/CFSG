module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611B

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem cmt_lifts_const {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    {ζ₁ ζ₂ x₀ y₀ x y w₀ w₀' w w' : G} (hx₀ : x₀ ∈ E2 E t) (hy₀ : y₀ ∈ E2 E t)
    (hxy₀ : x₀ * y₀ ≠ y₀ * x₀) (hx : x ∈ E2 E t) (hy : y ∈ E2 E t) (hxy : x * y ≠ y * x)
    (hw₀ : IsLift h hα ζ₁ x₀ w₀) (hw₀' : IsLift h hα ζ₂ y₀ w₀') (hw : IsLift h hα ζ₁ x w)
    (hw' : IsLift h hα ζ₂ y w') : w * w' * w⁻¹ * w'⁻¹ = w₀ * w₀' * w₀⁻¹ * w₀'⁻¹ := by
  obtain ⟨φ, hφ, hφx, hφy⟩ := hF.orbit_pairs (actW h).range h.index_range_le_two ⟨x₀, hx₀.1⟩
    ⟨y₀, hy₀.1⟩ ⟨x, hx.1⟩ ⟨y, hy.1⟩ hx₀.2.1 hx₀.2.2.1 hx₀.2.2.2 hy₀.2.1 hy₀.2.2.1 hy₀.2.2.2
    hxy₀ hx.2.1 hx.2.2.1 hx.2.2.2 hy.2.1 hy.2.2.1 hy.2.2.2 hxy
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hφ
  have hbx : (b : G) * x₀ * (b : G)⁻¹ = x := congrArg Subtype.val hφx
  have hby : (b : G) * y₀ * (b : G)⁻¹ = y := congrArg Subtype.val hφy
  have hb : (b : G) ∈ L ⊓ centralizer ({t} : Set G) := b.2
  have h1 := h.isLift_conj_W hα hb hx₀.1 hw₀
  have h2 := h.isLift_conj_W hα hb hy₀.1 hw₀'
  rw [hbx] at h1
  rw [hby] at h2
  have hu₁ := h.isLift_unique hα h1 hw
  have hu₂ := h.isLift_unique hα h2 hw'
  have e1 : w = ((b : G) * w₀ * (b : G)⁻¹) * (((b : G) * w₀ * (b : G)⁻¹)⁻¹ * w) := by group
  have e2 : w' = ((b : G) * w₀' * (b : G)⁻¹) * (((b : G) * w₀' * (b : G)⁻¹)⁻¹ * w') := by group
  rw [e1, e2, h.cmt_mul_central hα (h.W_norm_Qs hα hb hw₀.1) (h.W_norm_Qs hα hb hw₀'.1) hu₁ hu₂]
  have hc := h.cmt_mem hα hw₀.1 hw₀'.1
  have hbc := h.W_cent_Z hα hb hc
  calc (b : G) * w₀ * (b : G)⁻¹ * ((b : G) * w₀' * (b : G)⁻¹) * ((b : G) * w₀ * (b : G)⁻¹)⁻¹ *
        ((b : G) * w₀' * (b : G)⁻¹)⁻¹
      = (b : G) * (w₀ * w₀' * w₀⁻¹ * w₀'⁻¹) * (b : G)⁻¹ := by group
    _ = w₀ * w₀' * w₀⁻¹ * w₀'⁻¹ := by rw [hbc]; group

theorem pairing_gen {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t) {ζ₁ ζ₂ : G}
    (h₁ : ZInv hα ζ₁) (h₂ : ZInv hα ζ₂)
    (hcomm : ∀ x ∈ E2 E t, ∀ w w'', IsLift h hα ζ₁ x w → IsLift h hα ζ₂ x w'' →
      w * w'' = w'' * w) :
    ∃ ζ : G, ζ ∈ (zpowers α ⊔ zpowers t : Subgroup G) ∧ ζ * ζ = 1 ∧
      ∀ x ∈ E, ∀ y ∈ E, ∀ w w'', IsLift h hα ζ₁ x w → IsLift h hα ζ₂ y w'' →
        w * w'' * w⁻¹ * w''⁻¹ = iota ζ (x * y * x⁻¹ * y⁻¹) := by
  obtain ⟨a, b, c, d, hE⟩ := hF.gen_four
  have hgen : ∀ g ∈ ({a, b, c, d} : Set G), g ∈ E := fun g hg =>
    hE ▸ Subgroup.subset_closure hg
  have ha : a ∈ E := hgen a (by simp)
  have hb : b ∈ E := hgen b (by simp)
  have hc : c ∈ E := hgen c (by simp)
  have hd : d ∈ E := hgen d (by simp)
  choose! l₁ hl₁ using fun x (hx : x ∈ E) => h.exists_isLift hα h₁ hE ha hb hc hd hx
  choose! l₂ hl₂ using fun x (hx : x ∈ E) => h.exists_isLift hα h₂ hE ha hb hc hd hx
  have indep : ∀ x ∈ E, ∀ y ∈ E, ∀ w w'', IsLift h hα ζ₁ x w → IsLift h hα ζ₂ y w'' →
      w * w'' * w⁻¹ * w''⁻¹ = l₁ x * l₂ y * (l₁ x)⁻¹ * (l₂ y)⁻¹ := by
    intro x hx y hy w w'' hw hw''
    have hu := h.isLift_unique hα (hl₁ x hx) hw
    have hu' := h.isLift_unique hα (hl₂ y hy) hw''
    have := h.cmt_mul_central hα (hl₁ x hx).1 (hl₂ y hy).1 hu hu'
    simpa only [mul_inv_cancel_left] using this
  have hκ : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = t :=
    fun x hx y hy => h.conf.econfig.comm x hx y hy
  have hκL : ∀ x ∈ E, ∀ x' ∈ E, ∀ y ∈ E, (x * x') * y * (x * x')⁻¹ * y⁻¹ =
      (x * y * x⁻¹ * y⁻¹) * (x' * y * x'⁻¹ * y⁻¹) := fun x hx x' hx' y hy =>
    h.cmt_mul_left hα (h.E_le_Qs hα hx) (h.E_le_Qs hα hx') (h.E_le_Qs hα hy)
  have hκR : ∀ x ∈ E, ∀ y ∈ E, ∀ y' ∈ E, x * (y * y') * x⁻¹ * (y * y')⁻¹ =
      (x * y * x⁻¹ * y⁻¹) * (x * y' * x⁻¹ * y'⁻¹) := fun x hx y hy y' hy' =>
    h.cmt_mul_right hα (h.E_le_Qs hα hx) (h.E_le_Qs hα hy) (h.E_le_Qs hα hy')
  have hPL : ∀ x ∈ E, ∀ x' ∈ E, ∀ y ∈ E,
      l₁ (x * x') * l₂ y * (l₁ (x * x'))⁻¹ * (l₂ y)⁻¹ =
        (l₁ x * l₂ y * (l₁ x)⁻¹ * (l₂ y)⁻¹) * (l₁ x' * l₂ y * (l₁ x')⁻¹ * (l₂ y)⁻¹) := by
    intro x hx x' hx' y hy
    have hlift : IsLift h hα ζ₁ (x * x') (l₁ x * l₁ x') :=
      h.isLift_mul hα h₁.sq hx hx' (hl₁ x hx) (hl₁ x' hx')
    rw [← indep (x * x') (mul_mem hx hx') y hy _ _ hlift (hl₂ y hy)]
    exact h.cmt_mul_left hα (hl₁ x hx).1 (hl₁ x' hx').1 (hl₂ y hy).1
  have hPR : ∀ x ∈ E, ∀ y ∈ E, ∀ y' ∈ E,
      l₁ x * l₂ (y * y') * (l₁ x)⁻¹ * (l₂ (y * y'))⁻¹ =
        (l₁ x * l₂ y * (l₁ x)⁻¹ * (l₂ y)⁻¹) * (l₁ x * l₂ y' * (l₁ x)⁻¹ * (l₂ y')⁻¹) := by
    intro x hx y hy y' hy'
    have hlift : IsLift h hα ζ₂ (y * y') (l₂ y * l₂ y') :=
      h.isLift_mul hα h₂.sq hy hy' (hl₂ y hy) (hl₂ y' hy')
    rw [← indep x hx (y * y') (mul_mem hy hy') _ _ (hl₁ x hx) hlift]
    exact h.cmt_mul_right hα (hl₁ x hx).1 (hl₂ y hy).1 (hl₂ y' hy').1
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := h.exists_anticomm_E2
  set ζ : G := l₁ x₀ * l₂ y₀ * (l₁ x₀)⁻¹ * (l₂ y₀)⁻¹ with hζ
  have hζZ : ζ ∈ (zpowers α ⊔ zpowers t : Subgroup G) :=
    h.cmt_mem hα (hl₁ x₀ hx₀.1).1 (hl₂ y₀ hy₀.1).1
  have hζ2 : ζ * ζ = 1 := h.Zg_sq hα hζZ |> fun h1 => by simpa using h1
  have hbase : ∀ x ∈ E2 E t, ∀ y ∈ E2 E t,
      l₁ x * l₂ y * (l₁ x)⁻¹ * (l₂ y)⁻¹ = iota ζ (x * y * x⁻¹ * y⁻¹) := by
    intro x hx y hy
    by_cases hcm : x * y = y * x
    · rw [cmt_eq_one_iff.2 hcm, iota_one]
      have hl : IsLift h hα ζ₂ x (l₂ y) := by
        rcases h.E2_comm_cases hx hy hcm with rfl | rfl
        · exact hl₂ _ hy.1
        · exact h.isLift_of_mul_t hα hx.1 (hl₂ _ hy.1)
      exact cmt_eq_one_iff.2 (hcomm x hx _ _ (hl₁ x hx.1) hl)
    · have hne : x * y * x⁻¹ * y⁻¹ ≠ 1 := fun h1 => hcm (cmt_eq_one_iff.1 h1)
      rw [iota_of_ne hne]
      exact h.cmt_lifts_const hα hF hx₀ hy₀ hxy₀ hx hy hcm (hl₁ x₀ hx₀.1) (hl₂ y₀ hy₀.1)
        (hl₁ x hx.1) (hl₂ y hy.1)
  have hmain := bilin_ext (E := E) (E2 := E2 E t) (κ := fun x y => x * y * x⁻¹ * y⁻¹)
    (P := fun x y => l₁ x * l₂ y * (l₁ x)⁻¹ * (l₂ y)⁻¹) h.closure_E2_eq h.t_ne h.t_sq hζ2 hκ hκL
    hκR hPL hPR hbase
  refine ⟨ζ, hζZ, hζ2, fun x hx y hy w w'' hw hw'' => ?_⟩
  rw [indep x hx y hy w w'' hw hw'']
  exact hmain x hx y hy

theorem zinv_alpha {α : G} (hα : AlphaSpec S z t α) : ZInv hα α :=
  ⟨h.alpha_mem_Zg hα, hα.sq, hα.ne_one⟩

theorem zinv_alpha_t {α : G} (hα : AlphaSpec S z t α) : ZInv hα (α * t) := by
  have hαt : α * t = t * α := h.t_comm_S α hα.mem
  refine ⟨mul_mem (h.alpha_mem_Zg hα) (h.t_mem_Zg hα), ?_, ?_⟩
  · calc α * t * (α * t) = α * (t * α) * t := by group
      _ = α * (α * t) * t := by rw [← hαt]
      _ = (α * α) * (t * t) := by group
      _ = 1 := by rw [hα.sq, h.t_sq, one_mul]
  · intro h1
    apply hα.ne_t
    have := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_eq_of_mul_eq_one_right h.t_sq

theorem isLift_conj_z {α : G} (hα : AlphaSpec S z t α) {ζ₀ x w : G} (_hx : x ∈ E)
    (hw : IsLift h hα ζ₀ x w) : IsLift h hα (z * ζ₀ * z⁻¹) x (z * w * z⁻¹) := by
  refine ⟨h.z_norm_Qs hα hw.1, fun e he => ?_⟩
  rw [h.chi_conj_z he, hw.2 e he]
  by_cases hc : x * e * x⁻¹ * e⁻¹ = 1
  · simp [hc, iota_one]
  · rw [iota_of_ne hc, iota_of_ne hc]

theorem rel_d {α : G} (hα : AlphaSpec S z t α) {x w : G} (hx : x ∈ E)
    (hw : IsLift h hα α x w) :
    ∃ a ∈ (zpowers α ⊔ zpowers t : Subgroup G), x = w * (z * w * z⁻¹) * a ∧
      w * (z * w * z⁻¹) = (z * w * z⁻¹) * w := by
  have hxQ := h.E_le_Qs hα hx
  have hwz : z * w * z⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := h.z_norm_Qs hα hw.1
  have hu : x⁻¹ * (w * (z * w * z⁻¹)) ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
    have huQ : x⁻¹ * (w * (z * w * z⁻¹)) ∈ Fsub h hα ⊓ centralizer ({α} : Set G) :=
      mul_mem (inv_mem hxQ) (mul_mem hw.1 hwz)
    have hcomm : ∀ e ∈ E, (x⁻¹ * (w * (z * w * z⁻¹))) * e = e * (x⁻¹ * (w * (z * w * z⁻¹))) := by
      intro e he
      apply cmt_eq_one_iff.1
      rw [h.cmt_mul_left hα (inv_mem hxQ) (mul_mem hw.1 hwz) (h.E_le_Qs hα he),
        h.cmt_mul_left hα hw.1 hwz (h.E_le_Qs hα he), h.cmt_inv_left hα hxQ (h.E_le_Qs hα he),
        h.chi_conj_z he, hw.2 e he]
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
      rcases h.conf.econfig.comm x hx e he with h1 | h1
      · rw [h1]; simp [iota_one]
      · rw [h1, hti, iota_of_ne h.t_ne, h.z_conj_alpha hα]
        calc t * (α * (α * t)) = t * (α * α) * t := by group
          _ = 1 := by rw [hα.sq, mul_one, h.t_sq]
    exact (h.mem_Zg hα).2 (h.QF_cent_E hα huQ hcomm)
  refine ⟨(x⁻¹ * (w * (z * w * z⁻¹)))⁻¹, inv_mem hu, by group, ?_⟩
  have ha := inv_mem hu
  have hwx : w * x = x * w := by
    apply cmt_eq_one_iff.1
    rw [hw.2 x hx]
    have : x * x * x⁻¹ * x⁻¹ = 1 := by group
    rw [this, iota_one]
  have hx' : x = w * (z * w * z⁻¹) * (x⁻¹ * (w * (z * w * z⁻¹)))⁻¹ := by group
  set a := (x⁻¹ * (w * (z * w * z⁻¹)))⁻¹ with ha_def
  have h2 : a * w = w * a := (h.Zg_cent_Q hα ha).2 w hw.1
  have h1 : w * (w * (z * w * z⁻¹) * a) = (w * (z * w * z⁻¹) * a) * w := by
    rw [← hx']; exact hwx
  calc w * (z * w * z⁻¹) = w⁻¹ * (w * (w * (z * w * z⁻¹) * a)) * a⁻¹ := by group
    _ = w⁻¹ * ((w * (z * w * z⁻¹) * a) * w) * a⁻¹ := by rw [h1]
    _ = w⁻¹ * (w * (z * w * z⁻¹) * (a * w)) * a⁻¹ := by group
    _ = w⁻¹ * (w * (z * w * z⁻¹) * (w * a)) * a⁻¹ := by rw [h2]
    _ = (z * w * z⁻¹) * w := by group

theorem pairing_structure {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t) :
    ∃ ε : G, (ε = 1 ∨ ε = t) ∧
      ∀ x ∈ E, ∀ y ∈ E, ∀ w w', IsLift h hα α x w → IsLift h hα α y w' →
        w * w' * w⁻¹ * w'⁻¹ = iota (α * ε) (x * y * x⁻¹ * y⁻¹) ∧
        w * (z * w' * z⁻¹) * w⁻¹ * (z * w' * z⁻¹)⁻¹ = iota ε (x * y * x⁻¹ * y⁻¹) := by
  have hz₁ := h.zinv_alpha hα
  have hz₂ := h.zinv_alpha_t hα
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  obtain ⟨ζ, hζZ, hζ2, hζ⟩ := h.pairing_gen hα hF hz₁ hz₁ (by
    intro x hx w w'' hw hw''
    have hu := h.isLift_unique hα hw hw''
    have e1 : w'' = w * (w⁻¹ * w'') := by group
    have h2 : (w⁻¹ * w'') * w = w * (w⁻¹ * w'') := (h.Zg_cent_Q hα hu).2 w hw.1
    calc w * w'' = w * (w * (w⁻¹ * w'')) := by rw [← e1]
      _ = w * ((w⁻¹ * w'') * w) := by rw [h2]
      _ = (w * (w⁻¹ * w'')) * w := by group
      _ = w'' * w := by rw [← e1])
  obtain ⟨ζ', hζ'Z, hζ'2, hζ'⟩ := h.pairing_gen hα hF hz₁ hz₂ (by
    intro x hx w w'' hw hw''
    have hzw : IsLift h hα (α * t) x (z * w * z⁻¹) := by
      have := h.isLift_conj_z hα hx.1 hw
      rwa [h.z_conj_alpha hα] at this
    have hu := h.isLift_unique hα hzw hw''
    obtain ⟨a, ha, -, hcom⟩ := h.rel_d hα hx.1 hw
    have e1 : w'' = (z * w * z⁻¹) * ((z * w * z⁻¹)⁻¹ * w'') := by group
    have h2 : ((z * w * z⁻¹)⁻¹ * w'') * w = w * ((z * w * z⁻¹)⁻¹ * w'') :=
      (h.Zg_cent_Q hα hu).2 w hw.1
    calc w * w'' = w * ((z * w * z⁻¹) * ((z * w * z⁻¹)⁻¹ * w'')) := by rw [← e1]
      _ = (w * (z * w * z⁻¹)) * ((z * w * z⁻¹)⁻¹ * w'') := by group
      _ = ((z * w * z⁻¹) * w) * ((z * w * z⁻¹)⁻¹ * w'') := by rw [hcom]
      _ = (z * w * z⁻¹) * (w * ((z * w * z⁻¹)⁻¹ * w'')) := by group
      _ = (z * w * z⁻¹) * (((z * w * z⁻¹)⁻¹ * w'') * w) := by rw [h2]
      _ = ((z * w * z⁻¹) * ((z * w * z⁻¹)⁻¹ * w'')) * w := by group
      _ = w'' * w := by rw [← e1])
  obtain ⟨a, b, c, d, hE⟩ := hF.gen_four
  have hgen : ∀ g ∈ ({a, b, c, d} : Set G), g ∈ E := fun g hg =>
    hE ▸ Subgroup.subset_closure hg
  have ha : a ∈ E := hgen a (by simp)
  have hb : b ∈ E := hgen b (by simp)
  have hc : c ∈ E := hgen c (by simp)
  have hd : d ∈ E := hgen d (by simp)
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := h.exists_anticomm_E2
  have hct : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ = t := by
    have h1 : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ ≠ 1 := fun h1 => hxy₀ (cmt_eq_one_iff.1 h1)
    exact (h.conf.econfig.comm x₀ hx₀.1 y₀ hy₀.1).resolve_left h1
  have hct' : y₀ * x₀ * y₀⁻¹ * x₀⁻¹ = t := by
    have : y₀ * x₀ * y₀⁻¹ * x₀⁻¹ = (x₀ * y₀ * x₀⁻¹ * y₀⁻¹)⁻¹ := by group
    rw [this, hct, hti]
  obtain ⟨w₀, hw₀⟩ := h.exists_isLift hα hz₁ hE ha hb hc hd hx₀.1
  obtain ⟨w₀', hw₀'⟩ := h.exists_isLift hα hz₁ hE ha hb hc hd hy₀.1
  have hw₀z : IsLift h hα (α * t) x₀ (z * w₀ * z⁻¹) := by
    have := h.isLift_conj_z hα hx₀.1 hw₀
    rwa [h.z_conj_alpha hα] at this
  have hw₀'z : IsLift h hα (α * t) y₀ (z * w₀' * z⁻¹) := by
    have := h.isLift_conj_z hα hy₀.1 hw₀'
    rwa [h.z_conj_alpha hα] at this
  have v1 : w₀ * w₀' * w₀⁻¹ * w₀'⁻¹ = ζ := by
    rw [hζ x₀ hx₀.1 y₀ hy₀.1 w₀ w₀' hw₀ hw₀', hct, iota_of_ne h.t_ne]
  have v2 : w₀ * (z * w₀' * z⁻¹) * w₀⁻¹ * (z * w₀' * z⁻¹)⁻¹ = ζ' := by
    rw [hζ' x₀ hx₀.1 y₀ hy₀.1 w₀ (z * w₀' * z⁻¹) hw₀ hw₀'z, hct, iota_of_ne h.t_ne]
  have v3 : w₀' * (z * w₀ * z⁻¹) * w₀'⁻¹ * (z * w₀ * z⁻¹)⁻¹ = ζ' := by
    rw [hζ' y₀ hy₀.1 x₀ hx₀.1 w₀' (z * w₀ * z⁻¹) hw₀' hw₀z, hct', iota_of_ne h.t_ne]
  have hw₀Q := hw₀.1
  have hw₀'Q := hw₀'.1
  have hw₀zQ : z * w₀ * z⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := h.z_norm_Qs hα hw₀Q
  have hw₀'zQ : z * w₀' * z⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := h.z_norm_Qs hα hw₀'Q
  have v4 : (z * w₀ * z⁻¹) * (z * w₀' * z⁻¹) * (z * w₀ * z⁻¹)⁻¹ * (z * w₀' * z⁻¹)⁻¹ =
      z * ζ * z⁻¹ := by
    rw [← v1]
    group
  have v3' : (z * w₀ * z⁻¹) * w₀' * (z * w₀ * z⁻¹)⁻¹ * w₀'⁻¹ = ζ' := by
    have : (z * w₀ * z⁻¹) * w₀' * (z * w₀ * z⁻¹)⁻¹ * w₀'⁻¹ =
        (w₀' * (z * w₀ * z⁻¹) * w₀'⁻¹ * (z * w₀ * z⁻¹)⁻¹)⁻¹ := by group
    rw [this, v3]
    exact inv_eq_of_mul_eq_one_right hζ'2
  obtain ⟨a₁, ha₁, hxa, -⟩ := h.rel_d hα hx₀.1 hw₀
  obtain ⟨a₂, ha₂, hya, -⟩ := h.rel_d hα hy₀.1 hw₀'
  have R1 : t = ζ * (z * ζ * z⁻¹) := by
    have e0 : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ =
        (w₀ * (z * w₀ * z⁻¹) * a₁) * (w₀' * (z * w₀' * z⁻¹) * a₂) *
          (w₀ * (z * w₀ * z⁻¹) * a₁)⁻¹ * (w₀' * (z * w₀' * z⁻¹) * a₂)⁻¹ := by
      rw [← hxa, ← hya]
    rw [hct, h.cmt_mul_central hα (mul_mem hw₀Q hw₀zQ) (mul_mem hw₀'Q hw₀'zQ) ha₁ ha₂,
      h.cmt_mul_left hα hw₀Q hw₀zQ (mul_mem hw₀'Q hw₀'zQ),
      h.cmt_mul_right hα hw₀Q hw₀'Q hw₀'zQ, h.cmt_mul_right hα hw₀zQ hw₀'Q hw₀'zQ, v1, v2, v3',
      v4] at e0
    calc t = ζ * ζ' * (ζ' * (z * ζ * z⁻¹)) := e0
      _ = ζ * (ζ' * ζ') * (z * ζ * z⁻¹) := by group
      _ = ζ * (z * ζ * z⁻¹) := by rw [hζ'2, mul_one]
  have R2 : α = ζ * ζ' := by
    have e1 : w₀ * y₀ * w₀⁻¹ * y₀⁻¹ = α := by
      rw [hw₀.2 y₀ hy₀.1, hct, iota_of_ne h.t_ne]
    have e2 : w₀ * y₀ * w₀⁻¹ * y₀⁻¹ =
        w₀ * (w₀' * (z * w₀' * z⁻¹) * a₂) * w₀⁻¹ * (w₀' * (z * w₀' * z⁻¹) * a₂)⁻¹ := by
      rw [← hya]
    rw [e2, h.cmt_mul_right hα hw₀Q (mul_mem hw₀'Q hw₀'zQ) (h.Zg_cent_Q hα ha₂).1,
      h.cmt_mul_right hα hw₀Q hw₀'Q hw₀'zQ, v1, v2,
      cmt_eq_one_iff.2 ((h.Zg_cent_Q hα ha₂).2 w₀ hw₀Q).symm, mul_one] at e1
    exact e1.symm
  have hζ_eq_hε : ζ = α * ζ' ∧ (ζ' = 1 ∨ ζ' = t) := by
    rcases (h.mem_Zg hα).1 hζZ with h1 | h1 | h1 | h1
    · exfalso
      rw [h1] at R1
      apply h.t_ne
      calc t = 1 * (z * 1 * z⁻¹) := R1
        _ = 1 := by group
    · exfalso
      rw [h1, h.z_conj_t, h.t_sq] at R1
      exact h.t_ne R1
    · have h3 : ζ' = 1 := mul_eq_left.1 (by rw [h1] at R2; exact R2.symm)
      exact ⟨by rw [h1, h3, mul_one], Or.inl h3⟩
    · have h3 : ζ' = t := by
        rw [h1] at R2
        calc ζ' = (α * t)⁻¹ * (α * t * ζ') := by group
          _ = (α * t)⁻¹ * α := by rw [← R2]
          _ = t⁻¹ := by group
          _ = t := hti
      exact ⟨by rw [h1, h3], Or.inr h3⟩
  obtain ⟨hζε, hε⟩ := hζ_eq_hε
  refine ⟨ζ', hε, fun x hx y hy w w' hw hw' => ⟨?_, ?_⟩⟩
  · rw [← hζε]
    exact hζ x hx y hy w w' hw hw'
  · have hw'z : IsLift h hα (α * t) y (z * w' * z⁻¹) := by
      have := h.isLift_conj_z hα hy hw'
      rwa [h.z_conj_alpha hα] at this
    exact hζ' x hx y hy w (z * w' * z⁻¹) hw hw'z

end Hyp69

end CFSG.EvenSporadicStandard.Fin76b
