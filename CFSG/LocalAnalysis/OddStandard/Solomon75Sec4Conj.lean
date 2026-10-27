module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Layer
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Order

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem exists_four_distinct {α : Type*} [DecidableEq α] (F : Finset α) (hF : 4 ≤ F.card) :
    ∃ a b c d, a ∈ F ∧ b ∈ F ∧ c ∈ F ∧ d ∈ F ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      c ≠ d := by
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (by omega : 0 < F.card)
  have h1 : 3 ≤ (F.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, hb⟩ := Finset.card_pos.1 (by omega : 0 < (F.erase a).card)
  have h2 : 2 ≤ ((F.erase a).erase b).card := by rw [Finset.card_erase_of_mem hb]; omega
  obtain ⟨c, hc⟩ := Finset.card_pos.1 (by omega : 0 < ((F.erase a).erase b).card)
  have h3 : 1 ≤ (((F.erase a).erase b).erase c).card := by
    rw [Finset.card_erase_of_mem hc]; omega
  obtain ⟨d, hd⟩ := Finset.card_pos.1 (by omega : 0 < (((F.erase a).erase b).erase c).card)
  simp only [Finset.mem_erase] at ha hb hc hd
  exact ⟨a, b, c, d, ha, hb.2, hc.2.2, hd.2.2.2, fun e => hb.1 e.symm,
    fun e => hc.2.1 e.symm, fun e => hd.2.2.1 e.symm, fun e => hc.1 e.symm,
    fun e => hd.2.1 e.symm, fun e => hd.1 e.symm⟩

namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

@[expose] noncomputable def CoverSetup.conjPerm (C : CoverSetup n K) (g : Perm (Fin n)) :
    CoverSetup n K where
  π := (MulAut.conjNormal (H := alternatingGroup (Fin n)) g).toMonoidHom.comp C.π
  surj := (MulAut.conjNormal (H := alternatingGroup (Fin n)) g).surjective.comp C.surj
  ker := by
    rw [← C.ker]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact map_eq_one_iff _ (MulAut.conjNormal (H := alternatingGroup (Fin n)) g).injective
  hX := C.hX

theorem CoverSetup.ρ_conjPerm (C : CoverSetup n K) (g : Perm (Fin n)) (x : K) :
    (C.conjPerm g).ρ x = g * C.ρ x * g⁻¹ := by
  show ((MulAut.conjNormal (H := alternatingGroup (Fin n)) g (C.π x) :
    alternatingGroup (Fin n)) : Perm (Fin n)) = g * ((C.π x : alternatingGroup (Fin n)) :
    Perm (Fin n)) * g⁻¹
  rw [MulAut.conjNormal_apply]

theorem CoverSetup.Induces.conjPerm {C : CoverSetup n K} {α : MulAut K} {σ : Perm (Fin n)}
    (h : C.Induces α σ) (g : Perm (Fin n)) : (C.conjPerm g).Induces α (g * σ * g⁻¹) :=
  ⟨fun x => by
    rw [C.ρ_conjPerm, C.ρ_conjPerm, h.map_ρ]
    group⟩

theorem CoverSetup.mem_map_ρ_iff (C : CoverSetup n K) (g : Perm (Fin n)) (L : Subgroup K)
    (τ : Perm (Fin n)) : τ ∈ L.map C.ρ ↔ g * τ * g⁻¹ ∈ L.map (C.conjPerm g).ρ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, C.ρ_conjPerm g x⟩
  · rintro ⟨x, hx, hxτ⟩
    refine ⟨x, hx, ?_⟩
    rw [C.ρ_conjPerm] at hxτ
    exact mul_right_cancel (mul_left_cancel hxτ)

@[expose] def altFixOf (σ : Perm (Fin n)) : Subgroup (Perm (Fin n)) where
  carrier := {g | (∀ x, σ x ≠ x → g x = x) ∧ sign g = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [Perm.mul_apply, hb x hx, ha x hx]
    · rw [Perm.sign_mul, ha', hb', mul_one]
  one_mem' := ⟨fun x _ => rfl, Perm.sign_one⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · have := ha x hx
      rw [Perm.inv_eq_iff_eq]
      exact this.symm
    · rw [Perm.sign_inv, ha']

theorem mem_altFixOf {σ g : Perm (Fin n)} :
    g ∈ altFixOf σ ↔ (∀ x, σ x ≠ x → g x = x) ∧ sign g = 1 := Iff.rfl

theorem altFix_eq_altFixOf (k : ℕ) (h : 2 * k ≤ n) : altFix n k h = altFixOf (stdInv n k h) := by
  ext g
  constructor
  · rintro ⟨hfix, hs⟩
    exact ⟨fun x hx => hfix x ((stdInv_ne_self_iff x).1 hx), hs⟩
  · rintro ⟨hfix, hs⟩
    exact ⟨fun x hx => hfix x ((stdInv_ne_self_iff x).2 hx), hs⟩

theorem mem_altFixOf_conj (σ τ g : Perm (Fin n)) :
    τ ∈ altFixOf (g * σ * g⁻¹) ↔ g⁻¹ * τ * g ∈ altFixOf σ := by
  constructor
  · rintro ⟨hfix, hs⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · have h1 : (g * σ * g⁻¹) (g x) ≠ g x := by
        intro e
        apply hx
        apply g.injective
        simpa [Perm.mul_apply] using e
      have h2 := hfix (g x) h1
      simp only [Perm.mul_apply, h2]
      exact g.symm_apply_apply x
    · rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hs, mul_one, Int.units_mul_self]
  · rintro ⟨hfix, hs⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · have h1 : σ (g⁻¹ x) ≠ g⁻¹ x := by
        intro e
        apply hx
        have : g (σ (g⁻¹ x)) = g (g⁻¹ x) := by rw [e]
        simpa [Perm.mul_apply] using this
      have h2 := hfix (g⁻¹ x) h1
      have h3 : g⁻¹ (τ (g (g⁻¹ x))) = g⁻¹ x := by simpa [Perm.mul_apply] using h2
      have h4 : τ (g (g⁻¹ x)) = x := by
        have := congrArg g h3
        simpa using this
      simpa using h4
    · have h5 : sign (g * (g⁻¹ * τ * g) * g⁻¹) = 1 := by
        rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hs, mul_one, Int.units_mul_self]
      have h6 : g * (g⁻¹ * τ * g) * g⁻¹ = τ := by group
      rwa [h6] at h5

@[expose] def CoverSetup.fixedCompOf (C : CoverSetup n K) (σ : Perm (Fin n)) : Subgroup K :=
  ⁅(altFixOf σ).comap C.ρ, (altFixOf σ).comap C.ρ⁆

theorem CoverSetup.Induces.exists_std {C : CoverSetup n K} {α : MulAut K} {σ : Perm (Fin n)}
    (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ} (hk : σ.support.card = 2 * k) :
    ∃ (hkn : 2 * k ≤ n) (g : Perm (Fin n)), g * σ * g⁻¹ = stdInv n k hkn ∧
      (C.conjPerm g).Induces α (stdInv n k hkn) := by
  have hkn : 2 * k ≤ n := by
    have := Finset.card_le_univ σ.support
    simpa [hk] using this
  obtain ⟨g, hg⟩ := exists_conj_stdInv (h := hkn) hσ hk
  exact ⟨hkn, g, hg, hg ▸ h.conjPerm g⟩

theorem CoverSetup.fixedCompOf_eq (C : CoverSetup n K) {σ : Perm (Fin n)} {k : ℕ}
    (hkn : 2 * k ≤ n) {g : Perm (Fin n)} (hg : g * σ * g⁻¹ = stdInv n k hkn) :
    C.fixedCompOf σ = (C.conjPerm g).fixedComp k hkn := by
  have hcomap : (altFix n k hkn).comap (C.conjPerm g).ρ = (altFixOf σ).comap C.ρ := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, altFix_eq_altFixOf, ← hg, C.ρ_conjPerm,
      mem_altFixOf_conj]
    have : g⁻¹ * (g * C.ρ x * g⁻¹) * g = C.ρ x := by group
    rw [this]
  unfold CoverSetup.fixedCompOf CoverSetup.fixedComp
  rw [hcomap]

theorem CoverSetup.Induces.fixedCompOf_isDoubleCover (C : CoverSetup n K) (hn : 8 ≤ n)
    {α : MulAut K} {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) (hm : 5 ≤ n - 2 * k) :
    C.fixedCompOf σ ≤ fixSub α ∧ IsDoubleCoverOfAlt ↥(C.fixedCompOf σ) (n - 2 * k) ∧
      (C.fixedCompOf σ).map C.ρ = altFixOf σ := by
  obtain ⟨hkn, g, hg, h'⟩ := h.exists_std hσ hk
  have hcomp := C.fixedCompOf_eq hkn hg
  obtain ⟨h1, h2, h3⟩ := h'.fixedComp_isDoubleCover (C.conjPerm g) hn hm
  rw [hcomp]
  refine ⟨h1, h2, ?_⟩
  ext τ
  rw [C.mem_map_ρ_iff g, h3, altFix_eq_altFixOf, ← hg, mem_altFixOf_conj]
  have : g⁻¹ * (g * τ * g⁻¹) * g = τ := by group
  rw [this]

theorem CoverSetup.Induces.layer_fixSub_map_eq_of [Finite K] (C : CoverSetup n K) (hn : 8 ≤ n)
    {α : MulAut K} {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) (hm : 5 ≤ n - 2 * k) :
    (layer ↥(fixSub α)).map (fixSub α).subtype = C.fixedCompOf σ := by
  obtain ⟨hkn, g, hg, h'⟩ := h.exists_std hσ hk
  rw [C.fixedCompOf_eq hkn hg]
  exact h'.layer_fixSub_map_eq (C.conjPerm g) hn hm

theorem CoverSetup.Induces.exists_mem_fixSub_sq_ne_one {C : CoverSetup n K} (hn : 8 ≤ n)
    {α : MulAut K} {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) (hk1 : 1 ≤ k) :
    ∃ t ∈ fixSub α, t * t ≠ 1 ∧ t * t ∈ center K := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1' : k = 1 := by omega
    subst hk1'
    have hF : 4 ≤ (σ.support)ᶜ.card := by
      rw [Finset.card_compl, hk, Fintype.card_fin]
      omega
    obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
      exists_four_distinct _ hF
    have hfx : ∀ x ∈ (σ.support)ᶜ, σ x = x := fun x hx => by
      simpa [Perm.notMem_support] using hx
    have hsign : sign (swap a b * swap c d) = 1 := by
      rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
      decide
    obtain ⟨x, hx⟩ := C.exists_ρ_eq hsign
    refine ⟨x, h.apply_eq_of_dbl_fixed hab hac had hbc hbd hcd (hfx a ha) (hfx b hb) (hfx c hc)
      (hfx d hd) hx, C.sq_dbl_ne_one hn hab hac had hbc hbd hcd hx, C.sq_mem_center ?_⟩
    rw [hx]
    exact dbl_mul_self hab hac had hbc hbd hcd
  · obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ha, hb, hc, hd⟩ :=
      exists_two_pairs hσ hk hk2
    have hsign : sign (swap a b * swap c d) = 1 := by
      rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
      decide
    obtain ⟨x, hx⟩ := C.exists_ρ_eq hsign
    refine ⟨x, h.apply_eq_of_dbl_swapped hab hac had hbc hbd hcd ha hb hc hd hx,
      C.sq_dbl_ne_one hn hab hac had hbc hbd hcd hx, C.sq_mem_center ?_⟩
    rw [hx]
    exact dbl_mul_self hab hac had hbc hbd hcd

end AhatData

end CFSG.OddStandard.Solomon75
