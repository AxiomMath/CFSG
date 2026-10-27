module

public import CFSG.Quasithin.Background.CommVCommute
public import CFSG.Quasithin.Background.B1NaturalL2

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin Matrix

variable {V : Type*} [CommGroup V]

theorem mem_commV_of_mem {X : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ X) (v : V) :
    x v * v⁻¹ ∈ commV X :=
  Subgroup.subset_closure ⟨x, hx, v, rfl⟩

theorem commV_invariant_of_mem {X : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ X) {u : V}
    (hu : u ∈ commV X) : g u ∈ commV X :=
  CFSG.Quasithin.commV_apply_mem_of_mem hg hu

theorem commV_invariant_of_commute {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ x ∈ X, g * x = x * g) {u : V} (hu : u ∈ commV X) : g u ∈ commV X :=
  CFSG.Quasithin.apply_mem_commV_of_forall_commute hg hu

theorem fixes_commV_of_inter_bot {L L' : Subgroup (MulAut V)} (hinter : commV L ⊓ commV L' = ⊥)
    {a : MulAut V} (ha : a ∈ L') (hcomm : ∀ x ∈ L, a * x = x * a) {u : V} (hu : u ∈ commV L) :
    a u = u := by
  have h1 : a u * u⁻¹ ∈ commV L := (commV L).mul_mem (commV_invariant_of_commute hcomm hu)
    ((commV L).inv_mem hu)
  have h2 : a u * u⁻¹ ∈ commV L' := mem_commV_of_mem ha u
  have : a u * u⁻¹ ∈ commV L ⊓ commV L' := ⟨h1, h2⟩
  rw [hinter, Subgroup.mem_bot, mul_inv_eq_one] at this
  exact this

theorem sl2_fixed_of_order_three (M : SpecialLinearGroup (Fin 2) (ZMod 2)) (h3 : M ^ 3 = 1)
    (h1 : M ≠ 1) (x : Fin 2 → ZMod 2) (hx : (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ x = x) :
    x = 0 := by
  revert M h3 h1 x hx
  decide +revert

theorem eq_one_of_fixed_of_actsAsNaturalL2 {L : Subgroup (MulAut V)} {U : Subgroup V}
    (hnat : ActsAsNaturalL2 L U) {g : MulAut V} (hg : g ∈ L) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    {u : V} (hu : u ∈ U) (hfix : g u = u) : u = 1 := by
  obtain ⟨e, φ, hact⟩ := hnat
  have h := hact ⟨g, hg⟩ ⟨u, hu⟩ (by simpa [hfix] using hu)
  have hfix' : (⟨g u, by simpa [hfix] using hu⟩ : ↥U) = ⟨u, hu⟩ := Subtype.ext hfix
  rw [hfix'] at h
  have hM3 : (e ⟨g, hg⟩) ^ 3 = 1 := by
    rw [← map_pow, show (⟨g, hg⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using hg3), map_one]
  have hM1 : e ⟨g, hg⟩ ≠ 1 := fun h1 => hg1 (by
    have := e.injective (h1.trans (map_one e).symm)
    simpa using congrArg Subtype.val this)
  have hx : (e ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ Multiplicative.toAdd (φ ⟨u, hu⟩) =
      Multiplicative.toAdd (φ ⟨u, hu⟩) := by
    have := congrArg Multiplicative.toAdd h
    simpa using this.symm
  have h0 := sl2_fixed_of_order_three _ hM3 hM1 _ hx
  have : φ ⟨u, hu⟩ = 1 := by
    rw [← ofAdd_toAdd (φ ⟨u, hu⟩), h0]; rfl
  have := φ.injective (this.trans (map_one φ).symm)
  simpa using congrArg Subtype.val this

theorem exists_ne_one_of_actsAsNaturalL2 {L : Subgroup (MulAut V)} {U : Subgroup V}
    (hnat : ActsAsNaturalL2 L U) : ∃ u ∈ U, u ≠ 1 := by
  obtain ⟨e, φ, -⟩ := hnat
  by_contra hcon
  push Not at hcon
  have hall : ∀ w : Multiplicative (Fin 2 → ZMod 2), w = 1 := fun w => by
    obtain ⟨u, rfl⟩ := φ.surjective w
    have : u = 1 := Subtype.ext (hcon u u.2)
    rw [this, map_one]
  have h0 := hall (Multiplicative.ofAdd (Pi.single 0 1))
  have h1 : (Pi.single 0 1 : Fin 2 → ZMod 2) = 0 := h0
  have := congrFun h1 0
  simp at this

def fixedBy (g : MulAut V) : Subgroup V where
  carrier := {v | g v = v}
  one_mem' := map_one g
  mul_mem' := fun {a b} (ha : g a = a) (hb : g b = b) => by
    show g (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} (ha : g a = a) => by
    show g a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixedBy {g : MulAut V} {v : V} : v ∈ fixedBy g ↔ g v = v := Iff.rfl

structure S3Family (I : Finset (Subgroup (MulAut V))) : Prop where
  comm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a
  inter : ∀ L ∈ I, commV L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L' = ⊥
  top : fixV (⨆ L ∈ I, L) ⊔ ⨆ L ∈ I, commV L = ⊤
  nat : ∀ L ∈ I, ActsAsNaturalL2 L (commV L)

namespace S3Family

variable {I : Finset (Subgroup (MulAut V))} (hI : S3Family I)
include hI

theorem commV_inf_commV {L L' : Subgroup (MulAut V)} (hL : L ∈ I) (hL' : L' ∈ I) (hne : L ≠ L') :
    commV L ⊓ commV L' = ⊥ := by
  refine eq_bot_iff.2 ?_
  have h := hI.inter L hL
  rw [eq_bot_iff] at h
  refine le_trans (inf_le_inf_left _ ?_) h
  exact le_iSup₂_of_le L' hL' (le_iSup (fun _ : L' ≠ L => commV L') hne.symm)

theorem fixes_commV {L L' : Subgroup (MulAut V)} (hL : L ∈ I) (hL' : L' ∈ I) (hne : L ≠ L')
    {a : MulAut V} (ha : a ∈ L') {u : V} (hu : u ∈ commV L) : a u = u :=
  fixes_commV_of_inter_bot (hI.commV_inf_commV hL hL' hne) ha
    (fun x hx => hI.comm L' hL' L hL hne.symm a ha x hx) hu

end S3Family

theorem fixes_fixV {I : Finset (Subgroup (MulAut V))} {L : Subgroup (MulAut V)} (hL : L ∈ I)
    {a : MulAut V} (ha : a ∈ L) {f : V} (hf : f ∈ fixV (⨆ L ∈ I, L)) : a f = f :=
  hf a (Subgroup.mem_iSup_of_mem L (Subgroup.mem_iSup_of_mem hL ha))

namespace S3Family

variable {I : Finset (Subgroup (MulAut V))} (hI : S3Family I)
include hI

theorem exists_decomp {L₁ L₂ : Subgroup (MulAut V)} (v : V) :
    ∃ f ∈ fixV (⨆ L ∈ I, L), ∃ a₁ ∈ commV L₁, ∃ a₂ ∈ commV L₂,
      ∃ r ∈ (⨆ L ∈ I, ⨆ (_ : L ≠ L₁ ∧ L ≠ L₂), commV L), v = f * (a₁ * a₂ * r) := by
  have hv : v ∈ fixV (⨆ L ∈ I, L) ⊔ ⨆ L ∈ I, commV L := by rw [hI.top]; exact Subgroup.mem_top v
  obtain ⟨f, hf, s, hs, rfl⟩ := Subgroup.mem_sup.1 hv
  have hle : (⨆ L ∈ I, commV L) ≤
      commV L₁ ⊔ commV L₂ ⊔ ⨆ L ∈ I, ⨆ (_ : L ≠ L₁ ∧ L ≠ L₂), commV L := by
    refine iSup₂_le fun L hL => ?_
    by_cases h1 : L = L₁
    · subst h1; exact le_sup_of_le_left le_sup_left
    by_cases h2 : L = L₂
    · subst h2; exact le_sup_of_le_left le_sup_right
    exact le_sup_of_le_right
      (le_iSup₂_of_le L hL (le_iSup (fun _ : L ≠ L₁ ∧ L ≠ L₂ => commV L) ⟨h1, h2⟩))
  obtain ⟨b, hb, r, hr, rfl⟩ := Subgroup.mem_sup.1 (hle hs)
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Subgroup.mem_sup.1 hb
  exact ⟨f, hf, a₁, ha₁, a₂, ha₂, r, hr, rfl⟩

theorem fixedBy_mul_le {L₁ L₂ : Subgroup (MulAut V)} (h₁ : L₁ ∈ I) (h₂ : L₂ ∈ I) (hne : L₁ ≠ L₂)
    {g₁ g₂ : MulAut V} (hg₁ : g₁ ∈ L₁) (hg₂ : g₂ ∈ L₂) :
    fixedBy (g₁ * g₂) ≤ fixedBy g₁ := by
  intro v hv
  obtain ⟨f, hf, a₁, ha₁, a₂, ha₂, r, hr, rfl⟩ := hI.exists_decomp (L₁ := L₁) (L₂ := L₂) v
  have hR : ∀ {g : MulAut V} {L : Subgroup (MulAut V)}, L ∈ I → g ∈ L → (L = L₁ ∨ L = L₂) →
      ∀ x ∈ (⨆ L ∈ I, ⨆ (_ : L ≠ L₁ ∧ L ≠ L₂), commV L), g x = x := by
    intro g L hL hg hLe x hx
    have hle : (⨆ L ∈ I, ⨆ (_ : L ≠ L₁ ∧ L ≠ L₂), commV L) ≤ fixedBy g := by
      refine iSup₂_le fun L' hL' => iSup_le fun hL'ne => fun u hu => ?_
      have hL'L : L' ≠ L := by
        rcases hLe with rfl | rfl
        · exact hL'ne.1
        · exact hL'ne.2
      exact hI.fixes_commV hL' hL hL'L hg hu
    exact hle hx
  have hr1 : g₁ r = r := hR h₁ hg₁ (Or.inl rfl) r hr
  have hr2 : g₂ r = r := hR h₂ hg₂ (Or.inr rfl) r hr
  have hf1 : g₁ f = f := fixes_fixV h₁ hg₁ hf
  have hf2 : g₂ f = f := fixes_fixV h₂ hg₂ hf
  have ha₁2 : g₂ a₁ = a₁ := hI.fixes_commV h₁ h₂ hne hg₂ ha₁
  have ha₂1 : g₁ a₂ = a₂ := hI.fixes_commV h₂ h₁ hne.symm hg₁ ha₂
  have hg₂a₂ : g₂ a₂ ∈ commV L₂ := commV_invariant_of_mem hg₂ ha₂
  have hg₂a₂' : g₁ (g₂ a₂) = g₂ a₂ := hI.fixes_commV h₂ h₁ hne.symm hg₁ hg₂a₂
  have hkey : g₁ a₁ * g₂ a₂ = a₁ * a₂ := by
    have h := (mem_fixedBy.1 hv)
    simp only [MulAut.mul_apply, map_mul, hf1, hf2, hr1, hr2, ha₁2, hg₂a₂'] at h
    exact mul_right_cancel (mul_left_cancel h)
  have hprod : (g₁ a₁ * a₁⁻¹) * (g₂ a₂ * a₂⁻¹) = 1 := by
    have : (g₁ a₁ * a₁⁻¹) * (g₂ a₂ * a₂⁻¹) = (g₁ a₁ * g₂ a₂) * (a₁ * a₂)⁻¹ := by
      rw [mul_inv]; ac_rfl
    rw [this, hkey, mul_inv_cancel]
  have hx₁ : g₁ a₁ * a₁⁻¹ ∈ commV L₁ := mem_commV_of_mem hg₁ a₁
  have hx₂ : g₁ a₁ * a₁⁻¹ ∈ commV L₂ := by
    have hy : g₂ a₂ * a₂⁻¹ ∈ commV L₂ := mem_commV_of_mem hg₂ a₂
    have : g₁ a₁ * a₁⁻¹ = (g₂ a₂ * a₂⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hprod
    rw [this]; exact (commV L₂).inv_mem hy
  have hbot := hI.commV_inf_commV h₁ h₂ hne
  have hx : g₁ a₁ * a₁⁻¹ ∈ commV L₁ ⊓ commV L₂ := ⟨hx₁, hx₂⟩
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hx
  show g₁ _ = _
  simp [map_mul, hf1, hx, ha₂1, hr1]

theorem not_conj_of_distinct_factors [Finite V] {L₁ L₂ : Subgroup (MulAut V)} (h₁ : L₁ ∈ I)
    (h₂ : L₂ ∈ I) (hne : L₁ ≠ L₂) {g₁ g₂ : MulAut V} (hg₁ : g₁ ∈ L₁) (hg₂ : g₂ ∈ L₂)
    (hg₂3 : g₂ ^ 3 = 1) (hg₂1 : g₂ ≠ 1) (m : MulAut V) (hm : m * g₁ * m⁻¹ = g₁ * g₂) : False := by
  have hle := hI.fixedBy_mul_le h₁ h₂ hne hg₁ hg₂
  have hcard : Nat.card (fixedBy g₁) ≤ Nat.card (fixedBy (g₁ * g₂)) := by
    have hmap : fixedBy (m * g₁ * m⁻¹) = (fixedBy g₁).map m.toMonoidHom := by
      ext v
      simp only [mem_fixedBy, Subgroup.mem_map, MulAut.mul_apply]
      constructor
      · intro h
        refine ⟨m⁻¹ v, ?_, by simp⟩
        have := congrArg (fun x => m⁻¹ x) h
        simpa using this
      · rintro ⟨w, hw, rfl⟩
        have : g₁ w = w := hw
        simp [this]
    rw [← hm, hmap, Subgroup.card_map_of_injective m.injective]
  have heq : fixedBy (g₁ * g₂) = fixedBy g₁ := Subgroup.eq_of_le_of_card_ge hle hcard
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_actsAsNaturalL2 (hI.nat L₂ h₂)
  have hu₁ : u ∈ fixedBy g₁ := hI.fixes_commV h₂ h₁ hne.symm hg₁ hu
  rw [← heq, mem_fixedBy] at hu₁
  have hg₂u : g₂ u ∈ commV L₂ := commV_invariant_of_mem hg₂ hu
  have : g₂ u = u := by
    have h := hI.fixes_commV h₂ h₁ hne.symm hg₁ hg₂u
    simpa [MulAut.mul_apply, h] using hu₁
  exact hu1 (eq_one_of_fixed_of_actsAsNaturalL2 (hI.nat L₂ h₂) hg₂ hg₂3 hg₂1 hu this)

end S3Family

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
