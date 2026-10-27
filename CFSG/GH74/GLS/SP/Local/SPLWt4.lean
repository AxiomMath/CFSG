module

public import CFSG.GH74.GLS.SP.Local.SPLWt3

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

section Generic2

omit [Group G] in
theorem inf_irred {G : Type} [Group G] {H A Z : Subgroup G} (hirr : IrredUnder H A)
    (hZ : Normalizes H Z) (hA : Normalizes H A) : Z ⊓ A = ⊥ ∨ A ≤ Z := by
  have hle : Z ⊓ A ≤ A := inf_le_right
  have hN : Normalizes H (Z ⊓ A) := fun h hh x hx => ⟨hZ h hh x hx.1, hA h hh x hx.2⟩
  rcases hirr _ hle hN with h | h
  · left; exact h
  · right
    calc A = Z ⊓ A := h.symm
      _ ≤ Z := inf_le_left

omit [Group G] in
theorem fixed_free_of_irred {G : Type} [Group G] {H A E : Subgroup G}
    (hHab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hE : E ≤ H) (hA : Normalizes H A)
    (hirr : IrredUnder H A) (hne : ¬ E ≤ kernelOf H A) :
    ∀ x ∈ A, (∀ e ∈ E, e * x = x * e) → x = 1 := by
  intro x hx hfix
  let F : Subgroup G := A ⊓ centralizer (E : Set G)
  have hFA : F ≤ A := inf_le_left
  have hFN : Normalizes H F := by
    intro h hh f hf
    refine ⟨hA h hh f hf.1, mem_centralizer_iff.mpr fun e he => ?_⟩
    have hef : e * f = f * e := mem_centralizer_iff.mp hf.2 e he
    have heh : e * h = h * e := hHab e (hE he) h hh
    calc e * (h * f * h⁻¹) = (e * h) * f * h⁻¹ := by group
      _ = (h * e) * f * h⁻¹ := by rw [heh]
      _ = h * (e * f) * h⁻¹ := by group
      _ = h * (f * e) * h⁻¹ := by rw [hef]
      _ = h * f * h⁻¹ * e := by
          calc h * (f * e) * h⁻¹ = h * f * (e * h⁻¹) := by group
            _ = h * f * h⁻¹ * e := by
                have : e * h⁻¹ = h⁻¹ * e := by
                  have := hHab e (hE he) h⁻¹ (H.inv_mem hh)
                  exact this
                rw [this]; group
  rcases hirr F hFA hFN with h | h
  · have hxF : x ∈ F := ⟨hx, mem_centralizer_iff.mpr fun e he => hfix e he⟩
    rw [h] at hxF
    exact Subgroup.mem_bot.mp hxF
  · exfalso
    apply hne
    intro e he
    refine mem_kernelOf_iff.mpr ⟨hE he, fun a ha => ?_⟩
    have haF : a ∈ F := by rw [h]; exact ha
    exact mem_centralizer_iff.mp haF.2 e he

end Generic2

section Structure

variable [Finite G] (D : SPLNot3 G)

theorem H_R₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    Normalizes D.H D.R₁ :=
  normalizes_sup (normalizes_sup h3.H_X₁ (H_X₂ D hs h1 h3.toSPL3X)) h3.H_X₃

theorem weight_N (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) {Z : Subgroup G} (hZ : Normalizes D.H Z) :
    ∀ x₁ ∈ D.X₁, ∀ x₂ ∈ D.X₂, ∀ x₃ ∈ D.X₃, x₁ * x₂ * x₃ ∈ Z → x₁ ∈ Z ∧ x₂ ∈ Z ∧ x₃ ∈ Z := by
  refine WeightDecomp.weight_decomp_core (H := D.H) (X₁ := D.X₁) (X₂ := D.X₂) (X₃ := D.X₃)
    (W := Z) (H_comm D hs h1)
    (fun a ha b hb => hR.comm a (D.X₁_le_R₁ ha) b (D.X₂_le_R₁ hb))
    (fun a ha b hb => hR.comm a (D.X₁_le_R₁ ha) b (D.X₃_le_R₁ hb))
    (fun a ha b hb => hR.comm a (D.X₂_le_R₁ ha) b (D.X₃_le_R₁ hb))
    h3.H_X₁ (H_X₂ D hs h1 h3.toSPL3X) h3.H_X₃
    (irred_X₁ D hs h1 h3) (irred_X₂ D hs h1 h3) (irred_X₃ D hs h1 h3) ?_ ?_ ?_ hZ
  · intro heq
    have h' : D.h₁ ∈ centralizer (D.X₂ : Set G) ⊓ D.H := h₁_mem_ker₂ D hs h1 h3
    rw [← heq] at h'
    exact h₁_not_mem_ker₁ D hs h1 h3 h'
  · intro heq
    have h' : D.z ∈ centralizer (D.X₁ : Set G) ⊓ D.H := z_mem_ker₁ D hs h1 h3
    rw [heq] at h'
    exact z_not_mem_ker₃ D hs h3 h'
  · intro heq
    have h' : D.z ∈ centralizer (D.X₂ : Set G) ⊓ D.H := z_mem_ker₂ D hs h1 h3
    rw [heq] at h'
    exact z_not_mem_ker₃ D hs h3 h'


theorem comm_X₃_X₄ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    ⁅D.X₃, D.X₄⁆ = D.X₂ := by
  have hle : ⁅D.X₃, D.X₄⁆ ≤ D.X₂ := by
    rw [← h3.R₂_comm]
    exact Subgroup.commutator_mono (X₃_le_R₂ D) (le_sup_right : D.X₄ ≤ D.X₂ ⊔ D.X₃ ⊔ D.X₄)
  have hN : Normalizes D.H ⁅D.X₃, D.X₄⁆ := h3.H_X₃.commutator (H_X₄ D hs h1 h3)
  rcases irred_X₂ D hs h1 h3 _ hle hN with h | h
  · exfalso
    have hc : ∀ b ∈ D.X₃, ∀ c ∈ D.X₄, b * c = c * b := by
      intro b hb c hc
      have hm : ⁅b, c⁆ ∈ ⁅D.X₃, D.X₄⁆ := Subgroup.commutator_mem_commutator hb hc
      rw [h] at hm
      have h1' : ⁅b, c⁆ = 1 := Subgroup.mem_bot.mp hm
      rw [commutatorElement_def] at h1'
      calc b * c = (b * c * b⁻¹ * c⁻¹) * (c * b) := by group
        _ = c * b := by rw [h1', one_mul]
    have hcen : ∀ u ∈ D.X₂, ∀ r ∈ D.R₂, u * r = r * u := by
      intro u hu r hr
      have hu' : u ∈ (center ↥D.R₂).map D.R₂.subtype := by rw [h3.R₂_center]; exact hu
      obtain ⟨u', hu'c, rfl⟩ := hu'
      have := Subgroup.mem_center_iff.mp hu'c ⟨r, hr⟩
      exact congrArg Subtype.val this.symm
    have hX₂R : D.X₂ ≤ D.R₂ := le_sup_left.trans le_sup_left
    have hX₄R : D.X₄ ≤ D.R₂ := le_sup_right
    obtain ⟨x, hx, y, hy, hxy⟩ := h3.R₂_nonab
    apply hxy
    rw [← SetLike.mem_coe, h3.R₂_prod] at hx hy
    obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc', rfl⟩ := hx
    obtain ⟨_, ⟨a', ha', b', hb', rfl⟩, c', hc'', rfl⟩ := hy
    have hbR := X₃_le_R₂ D hb
    have hb'R := X₃_le_R₂ D hb'
    have hcR := hX₄R hc'
    have hc'R := hX₄R hc''
    have haR := hX₂R ha
    have ha'R := hX₂R ha'
    have hY : a' * b' * c' ∈ D.R₂ := D.R₂.mul_mem (D.R₂.mul_mem ha'R hb'R) hc'R
    have hab : ∀ u ∈ D.X₂, ∀ v ∈ D.R₂, Commute u v := fun u hu v hv => hcen u hu v hv
    have key : Commute (a * b * c) (a' * b' * c') := by
      refine Commute.mul_left (Commute.mul_left (hab a ha _ hY) ?_) ?_
      · refine Commute.mul_right (Commute.mul_right ?_ ?_) ?_
        · exact (hab a' ha' b hbR).symm
        · exact (X₃_eab D h3).1 b hb b' hb'
        · exact hc b hb c' hc''
      · refine Commute.mul_right (Commute.mul_right ?_ ?_) ?_
        · exact (hab a' ha' c hcR).symm
        · exact (hc b' hb' c hc').symm
        · exact (X₄_eab D h3).1 c hc' c' hc''
    exact key.eq
  · exact h


theorem H_R₂ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    Normalizes D.H D.R₂ :=
  normalizes_sup (normalizes_sup (H_X₂ D hs h1 h3.toSPL3X) h3.H_X₃) (H_X₄ D hs h1 h3)

omit [Finite G] in
theorem X₄_normalizes_R₁ (hR : SPLR₁ D) : D.X₄ ≤ normalizer (D.R₁ : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro r
  constructor
  · intro hr; exact hR.normal x (D.X₄_le_P hx) r hr
  · intro hr
    have := hR.normal x⁻¹ (Subgroup.inv_mem _ (D.X₄_le_P hx)) _ hr
    simpa [mul_assoc] using this

omit [Finite G] in
theorem P_decomp (hR : SPLR₁ D) : ∀ p ∈ D.P, ∃ x ∈ D.X₄, ∃ r ∈ D.R₁, p = x * r := by
  intro p hp
  rw [D.P_eq_R₁_sup_X₄, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left D.R₁ D.X₄ (X₄_normalizes_R₁ D hR)] at hp
  obtain ⟨r', hr', x, hx, rfl⟩ := hp
  refine ⟨x, hx, x⁻¹ * r' * x, ?_, by group⟩
  have := hR.normal x⁻¹ (D.P.inv_mem (D.X₄_le_P hx)) r' hr'
  simpa using this

omit [Finite G] in
theorem comp_mem {H A E Z : Subgroup G} (hHab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hE : E ≤ H)
    (hA : Normalizes H A) (hirr : IrredUnder H A) (hne : ¬ E ≤ kernelOf H A)
    (hZ : Normalizes H Z) {ri : G} (hri : ri ∈ A)
    (h : ∀ e ∈ E, e * ri * e⁻¹ * ri⁻¹ ∈ Z) : ri ∈ Z := by
  rcases inf_irred hirr hZ hA with hbot | hle
  · have : ∀ e ∈ E, e * ri = ri * e := by
      intro e he
      have hm : e * ri * e⁻¹ * ri⁻¹ ∈ Z ⊓ A := ⟨h e he, A.mul_mem (hA e (hE he) ri hri) (A.inv_mem hri)⟩
      rw [hbot] at hm
      have h1' : e * ri * e⁻¹ * ri⁻¹ = 1 := Subgroup.mem_bot.mp hm
      calc e * ri = (e * ri * e⁻¹ * ri⁻¹) * (ri * e) := by group
        _ = ri * e := by rw [h1', one_mul]
    have := fixed_free_of_irred hHab hE hA hirr hne ri hri this
    rw [this]; exact Z.one_mem
  · exact hle hri

theorem decomp_Z (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) {Z : Subgroup G} (hZP : Z ≤ D.P) (hZH : Normalizes D.H Z) :
    ∀ z ∈ Z, ∃ x ∈ D.X₄, ∃ r ∈ D.R₁, z = x * r ∧ x ∈ Z ∧ r ∈ Z := by
  intro z hz
  obtain ⟨x, hx, r, hr, hzxr⟩ := P_decomp D hR z (hZP hz)
  have hHR := H_R₁ D hs h1 h3
  have hkey : ∀ e ∈ kernelOf D.H D.X₄, e * r * e⁻¹ * r⁻¹ ∈ Z := by
    intro e he
    obtain ⟨heH, hex'⟩ := mem_kernelOf_iff.mp he
    have hex : e * x = x * e := hex' x hx
    have hezZ : e * z * e⁻¹ ∈ Z := hZH e heH z hz
    have hcR : e * r * e⁻¹ * r⁻¹ ∈ D.R₁ := D.R₁.mul_mem (hHR e heH r hr) (D.R₁.inv_mem hr)
    have hxP : x ∈ D.P := D.X₄_le_P hx
    have h1' : e * z * e⁻¹ * z⁻¹ = x * (e * r * e⁻¹ * r⁻¹) * x⁻¹ := by
      rw [hzxr]
      have hxe : e * x * e⁻¹ = x := by rw [hex]; group
      calc e * (x * r) * e⁻¹ * (x * r)⁻¹ = (e * x * e⁻¹) * (e * r * e⁻¹) * r⁻¹ * x⁻¹ := by group
        _ = x * (e * r * e⁻¹) * r⁻¹ * x⁻¹ := by rw [hxe]
        _ = _ := by group
    have hn'Z : x * (e * r * e⁻¹ * r⁻¹) * x⁻¹ ∈ Z := by
      rw [← h1']; exact Z.mul_mem hezZ (Z.inv_mem hz)
    have hcr : r⁻¹ * (e * r * e⁻¹ * r⁻¹) * r = e * r * e⁻¹ * r⁻¹ := by
      have := hR.comm _ (D.R₁.inv_mem hr) _ hcR
      calc r⁻¹ * (e * r * e⁻¹ * r⁻¹) * r = ((e * r * e⁻¹ * r⁻¹) * r⁻¹) * r := by rw [this]
        _ = e * r * e⁻¹ * r⁻¹ := by group
    have hc : e * r * e⁻¹ * r⁻¹ = z⁻¹ * (x * (e * r * e⁻¹ * r⁻¹) * x⁻¹) * z := by
      rw [hzxr]
      calc e * r * e⁻¹ * r⁻¹ = r⁻¹ * (e * r * e⁻¹ * r⁻¹) * r := hcr.symm
        _ = (x * r)⁻¹ * (x * (e * r * e⁻¹ * r⁻¹) * x⁻¹) * (x * r) := by group
    rw [hc]
    exact Z.mul_mem (Z.mul_mem (Z.inv_mem hz) hn'Z) hz
  obtain ⟨r₁, hr₁, r₂, hr₂, r₃, hr₃, hr_eq⟩ := (R₁_decomp D h3 hR).1 r hr
  have hs₁ : ∀ e ∈ D.H, e * r₁ * e⁻¹ ∈ D.X₁ := fun e he => h3.H_X₁ e he r₁ hr₁
  have hs₂ : ∀ e ∈ D.H, e * r₂ * e⁻¹ ∈ D.X₂ := fun e he => H_X₂ D hs h1 h3.toSPL3X e he r₂ hr₂
  have hs₃ : ∀ e ∈ D.H, e * r₃ * e⁻¹ ∈ D.X₃ := fun e he => h3.H_X₃ e he r₃ hr₃
  have hsplit : ∀ e ∈ D.H, e * r * e⁻¹ * r⁻¹ = (e * r₁ * e⁻¹ * r₁⁻¹) * (e * r₂ * e⁻¹ * r₂⁻¹) *
      (e * r₃ * e⁻¹ * r₃⁻¹) := by
    intro e he
    have hS₁ := D.X₁_le_R₁ (hs₁ e he)
    have hS₂ := D.X₂_le_R₁ (hs₂ e he)
    have hS₃ := D.X₃_le_R₁ (hs₃ e he)
    have hR₁ := D.X₁_le_R₁ hr₁
    have hR₂ := D.X₂_le_R₁ hr₂
    have hR₃ := D.X₃_le_R₁ hr₃
    have hA : ((e * r₃ * e⁻¹) * r₃⁻¹) * r₂⁻¹ = r₂⁻¹ * ((e * r₃ * e⁻¹) * r₃⁻¹) :=
      hR.comm _ (D.R₁.mul_mem hS₃ (D.R₁.inv_mem hR₃)) _ (D.R₁.inv_mem hR₂)
    have hB : (((e * r₂ * e⁻¹) * r₂⁻¹) * ((e * r₃ * e⁻¹) * r₃⁻¹)) * r₁⁻¹ =
        r₁⁻¹ * (((e * r₂ * e⁻¹) * r₂⁻¹) * ((e * r₃ * e⁻¹) * r₃⁻¹)) :=
      hR.comm _ (D.R₁.mul_mem (D.R₁.mul_mem hS₂ (D.R₁.inv_mem hR₂))
        (D.R₁.mul_mem hS₃ (D.R₁.inv_mem hR₃))) _ (D.R₁.inv_mem hR₁)
    rw [hr_eq]
    calc e * (r₁ * r₂ * r₃) * e⁻¹ * (r₁ * r₂ * r₃)⁻¹
        = (e * r₁ * e⁻¹) * (e * r₂ * e⁻¹) * (((e * r₃ * e⁻¹) * r₃⁻¹) * r₂⁻¹) * r₁⁻¹ := by group
      _ = (e * r₁ * e⁻¹) * (e * r₂ * e⁻¹) * (r₂⁻¹ * ((e * r₃ * e⁻¹) * r₃⁻¹)) * r₁⁻¹ := by rw [hA]
      _ = (e * r₁ * e⁻¹) * (((e * r₂ * e⁻¹) * r₂⁻¹) * ((e * r₃ * e⁻¹) * r₃⁻¹) * r₁⁻¹) := by group
      _ = (e * r₁ * e⁻¹) * (r₁⁻¹ * (((e * r₂ * e⁻¹) * r₂⁻¹) * ((e * r₃ * e⁻¹) * r₃⁻¹))) := by
          rw [hB]
      _ = _ := by group
  have hcomp : ∀ e ∈ kernelOf D.H D.X₄, (e * r₁ * e⁻¹ * r₁⁻¹ ∈ Z) ∧ (e * r₂ * e⁻¹ * r₂⁻¹ ∈ Z) ∧
      (e * r₃ * e⁻¹ * r₃⁻¹ ∈ Z) := by
    intro e he
    have heH := (mem_kernelOf_iff.mp he).1
    have := hkey e he
    rw [hsplit e heH] at this
    exact weight_N D hs h1 h3 hR hZH _ (D.X₁.mul_mem (hs₁ e heH) (D.X₁.inv_mem hr₁)) _
      (D.X₂.mul_mem (hs₂ e heH) (D.X₂.inv_mem hr₂)) _
      (D.X₃.mul_mem (hs₃ e heH) (D.X₃.inv_mem hr₃)) this
  have hHab := H_comm D hs h1
  have hE : kernelOf D.H D.X₄ ≤ D.H := fun e he => (mem_kernelOf_iff.mp he).1
  have hrZ₁ : r₁ ∈ Z := comp_mem hHab hE h3.H_X₁ (irred_X₁ D hs h1 h3)
    (ker₄_not_le_ker₁ D hs h1 h3) hZH hr₁ (fun e he => (hcomp e he).1)
  have hrZ₂ : r₂ ∈ Z := comp_mem hHab hE (H_X₂ D hs h1 h3.toSPL3X) (irred_X₂ D hs h1 h3)
    (ker₄_not_le_ker₂ D hs h1 h3) hZH hr₂ (fun e he => (hcomp e he).2.1)
  have hrZ₃ : r₃ ∈ Z := comp_mem hHab hE h3.H_X₃ (irred_X₃ D hs h1 h3)
    (ker₄_not_le_ker₃ D hs h1 h3 hR) hZH hr₃ (fun e he => (hcomp e he).2.2)
  have hrZ : r ∈ Z := by
    rw [hr_eq]; exact Z.mul_mem (Z.mul_mem hrZ₁ hrZ₂) hrZ₃
  refine ⟨x, hx, r, hr, hzxr, ?_, hrZ⟩
  have : x = z * r⁻¹ := by rw [hzxr]; group
  rw [this]
  exact Z.mul_mem hz (Z.inv_mem hrZ)


theorem R₁_cancel (h3 : SPL3M2 D) (hR : SPLR₁ D)
    {x₁ x₁' : G} (h₁ : x₁ ∈ D.X₁) (h₁' : x₁' ∈ D.X₁) {x₂ x₂' : G} (h₂ : x₂ ∈ D.X₂)
    (h₂' : x₂' ∈ D.X₂) {x₃ x₃' : G} (h₃ : x₃ ∈ D.X₃) (h₃' : x₃' ∈ D.X₃)
    (h : x₁ * x₂ * x₃ = x₁' * x₂' * x₃') : x₁ = x₁' ∧ x₂ = x₂' ∧ x₃ = x₃' := by
  let _ : CommGroup ↥D.R₁ :=
    { (inferInstance : Group ↥D.R₁) with mul_comm := fun a b => Subtype.ext (hR.comm a a.2 b b.2) }
  let a : ↥D.R₁ := ⟨x₁, D.X₁_le_R₁ h₁⟩
  let a' : ↥D.R₁ := ⟨x₁', D.X₁_le_R₁ h₁'⟩
  let b : ↥D.R₁ := ⟨x₂, D.X₂_le_R₁ h₂⟩
  let b' : ↥D.R₁ := ⟨x₂', D.X₂_le_R₁ h₂'⟩
  let c : ↥D.R₁ := ⟨x₃, D.X₃_le_R₁ h₃⟩
  let c' : ↥D.R₁ := ⟨x₃', D.X₃_le_R₁ h₃'⟩
  have hab : a * b * c = a' * b' * c' := Subtype.ext h
  have key : (a'⁻¹ * a) * (b'⁻¹ * b) * (c'⁻¹ * c) = 1 := by
    have e : (a'⁻¹ * a) * (b'⁻¹ * b) * (c'⁻¹ * c) = (a' * b' * c')⁻¹ * (a * b * c) := by
      rw [mul_inv_rev, mul_inv_rev]; ac_rfl
    rw [e, hab]; exact inv_mul_cancel _
  have key' : (x₁'⁻¹ * x₁) * (x₂'⁻¹ * x₂) * (x₃'⁻¹ * x₃) = 1 := congrArg Subtype.val key
  obtain ⟨k1, k2, k3⟩ := (R₁_decomp D h3 hR).2 _ (D.X₁.mul_mem (D.X₁.inv_mem h₁') h₁) _
    (D.X₂.mul_mem (D.X₂.inv_mem h₂') h₂) _ (D.X₃.mul_mem (D.X₃.inv_mem h₃') h₃) key'
  refine ⟨?_, ?_, ?_⟩
  · calc x₁ = x₁' * (x₁'⁻¹ * x₁) := by group
      _ = x₁' := by rw [k1, mul_one]
  · calc x₂ = x₂' * (x₂'⁻¹ * x₂) := by group
      _ = x₂' := by rw [k2, mul_one]
  · calc x₃ = x₃' * (x₃'⁻¹ * x₃) := by group
      _ = x₃' := by rw [k3, mul_one]


theorem Z_eq_prod (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) {Z : Subgroup G} (hZP : Z ≤ D.P) (hZH : Normalizes D.H Z) :
    (Z : Set G) = (↑(Z ⊓ D.X₄) : Set G) * ↑(Z ⊓ D.X₂) * ↑(Z ⊓ D.X₃) * ↑(Z ⊓ D.X₁) := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, r, hr, hzxr, hxZ, hrZ⟩ := decomp_Z D hs h1 h3 hR hZP hZH z hz
    obtain ⟨r₁, hr₁, r₂, hr₂, r₃, hr₃, hr_eq⟩ := (R₁_decomp D h3 hR).1 r hr
    have hrZ' : r₁ * r₂ * r₃ ∈ Z := hr_eq ▸ hrZ
    obtain ⟨hZ₁, hZ₂, hZ₃⟩ := weight_N D hs h1 h3 hR hZH r₁ hr₁ r₂ hr₂ r₃ hr₃ hrZ'
    have hcomm : r₁ * (r₂ * r₃) = (r₂ * r₃) * r₁ :=
      hR.comm _ (D.X₁_le_R₁ hr₁) _ (D.R₁.mul_mem (D.X₂_le_R₁ hr₂) (D.X₃_le_R₁ hr₃))
    have hz_eq : z = x * r₂ * r₃ * r₁ := by
      rw [hzxr, hr_eq]
      calc x * (r₁ * r₂ * r₃) = x * (r₁ * (r₂ * r₃)) := by group
        _ = x * ((r₂ * r₃) * r₁) := by rw [hcomm]
        _ = x * r₂ * r₃ * r₁ := by group
    rw [hz_eq]
    exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul ⟨hxZ, hx⟩ ⟨hZ₂, hr₂⟩) ⟨hZ₃, hr₃⟩)
      ⟨hZ₁, hr₁⟩
  · rintro _ ⟨_, ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩, d, hd, rfl⟩
    exact Z.mul_mem (Z.mul_mem (Z.mul_mem ha.1 hb.1) hc.1) hd.1

theorem Z_card (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) {Z : Subgroup G} (hZP : Z ≤ D.P) (hZH : Normalizes D.H Z) :
    Nat.card ↥Z = Nat.card ↥(Z ⊓ D.X₄) * (Nat.card ↥(Z ⊓ D.X₂) *
      (Nat.card ↥(Z ⊓ D.X₃) * Nat.card ↥(Z ⊓ D.X₁))) := by
  let f : ↥(Z ⊓ D.X₄) × (↥(Z ⊓ D.X₂) × (↥(Z ⊓ D.X₃) × ↥(Z ⊓ D.X₁))) → ↥Z := fun t =>
    ⟨(t.1 : G) * t.2.1 * t.2.2.1 * t.2.2.2,
      Z.mul_mem (Z.mul_mem (Z.mul_mem t.1.2.1 t.2.1.2.1) t.2.2.1.2.1) t.2.2.2.2.1⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
    have h' : (a : G) * b * c * d = a' * b' * c' * d' := congrArg Subtype.val h
    have hbR : (b : G) ∈ D.R₁ := D.X₂_le_R₁ b.2.2
    have hcR : (c : G) ∈ D.R₁ := D.X₃_le_R₁ c.2.2
    have hdR : (d : G) ∈ D.R₁ := D.X₁_le_R₁ d.2.2
    have hb'R : (b' : G) ∈ D.R₁ := D.X₂_le_R₁ b'.2.2
    have hc'R : (c' : G) ∈ D.R₁ := D.X₃_le_R₁ c'.2.2
    have hd'R : (d' : G) ∈ D.R₁ := D.X₁_le_R₁ d'.2.2
    have hxa : (a : G)⁻¹ * (a' : G) ∈ D.X₄ ⊓ D.R₁ := by
      refine ⟨D.X₄.mul_mem (D.X₄.inv_mem a.2.2) a'.2.2, ?_⟩
      have e : (a : G)⁻¹ * (a' : G) = ((b : G) * c * d) * ((b' : G) * c' * d')⁻¹ := by
        have h'' : (a : G) * ((b : G) * c * d) = (a' : G) * ((b' : G) * c' * d') := by
          calc (a : G) * ((b : G) * c * d) = (a : G) * b * c * d := by group
            _ = (a' : G) * b' * c' * d' := h'
            _ = (a' : G) * ((b' : G) * c' * d') := by group
        calc (a : G)⁻¹ * (a' : G)
            = (a : G)⁻¹ * ((a' : G) * ((b' : G) * c' * d')) * ((b' : G) * c' * d')⁻¹ := by
              group
          _ = (a : G)⁻¹ * ((a : G) * ((b : G) * c * d)) * ((b' : G) * c' * d')⁻¹ := by rw [h'']
          _ = _ := by group
      rw [e]
      exact D.R₁.mul_mem (D.R₁.mul_mem (D.R₁.mul_mem hbR hcR) hdR)
        (D.R₁.inv_mem (D.R₁.mul_mem (D.R₁.mul_mem hb'R hc'R) hd'R))
    rw [X₄_inf_R₁ D h3 hR] at hxa
    have hxa1 : (a : G)⁻¹ * (a' : G) = 1 := Subgroup.mem_bot.mp hxa
    have haa : (a : G) = (a' : G) := inv_mul_eq_one.mp hxa1
    have hrest : (d : G) * (b : G) * (c : G) = (d' : G) * (b' : G) * (c' : G) := by
      have h2 : (a : G) * ((b : G) * c * d) = (a : G) * ((b' : G) * c' * d') := by
        calc (a : G) * ((b : G) * c * d) = (a : G) * b * c * d := by group
          _ = (a' : G) * b' * c' * d' := h'
          _ = (a : G) * ((b' : G) * c' * d') := by rw [← haa]; group
      have h3' := mul_left_cancel h2
      have hc1 : (d : G) * ((b : G) * c) = ((b : G) * c) * d :=
        hR.comm _ hdR _ (D.R₁.mul_mem hbR hcR)
      have hc2 : (d' : G) * ((b' : G) * c') = ((b' : G) * c') * d' :=
        hR.comm _ hd'R _ (D.R₁.mul_mem hb'R hc'R)
      calc (d : G) * b * c = (d : G) * ((b : G) * c) := by group
        _ = ((b : G) * c) * d := hc1
        _ = (b : G) * c * d := by group
        _ = (b' : G) * c' * d' := h3'
        _ = ((b' : G) * c') * d' := by group
        _ = (d' : G) * ((b' : G) * c') := hc2.symm
        _ = (d' : G) * b' * c' := by group
    obtain ⟨k1, k2, k3⟩ := R₁_cancel D h3 hR d.2.2 d'.2.2 b.2.2 b'.2.2 c.2.2 c'.2.2 hrest
    have : a = a' := Subtype.ext haa
    have : b = b' := Subtype.ext k2
    have : c = c' := Subtype.ext k3
    have : d = d' := Subtype.ext k1
    subst_vars
    rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ (↑(Z ⊓ D.X₄) : Set G) * ↑(Z ⊓ D.X₂) * ↑(Z ⊓ D.X₃) * ↑(Z ⊓ D.X₁) := by
      rw [← Z_eq_prod D hs h1 h3 hR hZP hZH]; exact hz
    obtain ⟨_, ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩, d, hd, rfl⟩ := hz'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩), rfl⟩
  rw [← Nat.card_prod, ← Nat.card_prod, ← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

end Structure

end CFSG.GH74.GLS.SP.Local
