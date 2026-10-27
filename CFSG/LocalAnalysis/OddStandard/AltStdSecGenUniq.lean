module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenDichAll

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section GlobalLift

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {z : G}

theorem exists_global_lift {H : Subgroup G} (hH : WreathPair L z n H) (hn : 4 ≤ n) :
    ∃ Ψ : ↥L →* G, (∀ x, Ψ x ∈ H) ∧ (∀ x, Ψ x * (z * Ψ x * z⁻¹) = x) ∧
      (∀ x y, Ψ x * (z * Ψ y * z⁻¹) = (z * Ψ y * z⁻¹) * Ψ x) ∧ Function.Injective Ψ ∧
      (∀ a ∈ H, ∃ x, Ψ x = a) ∧ (∀ x, Ψ x = z * Ψ x * z⁻¹ → x = 1) := by
  obtain ⟨eH⟩ := hH.iso
  have hcen : Subgroup.center ↥H = ⊥ := center_eq_bot_of_alt hn eH
  have hcomm : ∀ a b : ↥H, (a : G) * (z * (b : G) * z⁻¹) = (z * (b : G) * z⁻¹) * (a : G) :=
    fun a b => hH.comm a a.2 _ ⟨b, b.2, rfl⟩
  let θ : ↥H →* G := MonoidHom.mk' (fun a => (a : G) * (z * (a : G) * z⁻¹)) (fun a b => by
    have hc := hcomm b a
    show ((a * b : ↥H) : G) * (z * ((a * b : ↥H) : G) * z⁻¹) =
      ((a : G) * (z * (a : G) * z⁻¹)) * ((b : G) * (z * (b : G) * z⁻¹))
    simp only [Subgroup.coe_mul]
    calc (a : G) * b * (z * ((a : G) * b) * z⁻¹)
        = (a : G) * ((b : G) * (z * (a : G) * z⁻¹)) * (z * (b : G) * z⁻¹) := by group
      _ = (a : G) * ((z * (a : G) * z⁻¹) * (b : G)) * (z * (b : G) * z⁻¹) := by rw [hc]
      _ = ((a : G) * (z * (a : G) * z⁻¹)) * ((b : G) * (z * (b : G) * z⁻¹)) := by group)
  have hθ : ∀ a : ↥H, θ a = (a : G) * (z * (a : G) * z⁻¹) := fun a => rfl
  have hθL : ∀ a : ↥H, θ a ∈ L := fun a => by
    have : θ a ∈ (L : Set G) := by rw [hH.diag]; exact ⟨a, a.2, rfl⟩
    exact this
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [hθ] at ha
    have h1 : z * (a : G) * z⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right ha
    have hinv : ((a : G)⁻¹) ∈ H := H.inv_mem a.2
    have hcen' : (⟨(a : G)⁻¹, hinv⟩ : ↥H) ∈ Subgroup.center ↥H := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have := hcomm g a
      rw [h1] at this
      exact this
    rw [hcen] at hcen'
    have : (a : G)⁻¹ = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hcen')
    exact Subtype.ext (inv_eq_one.1 this)
  have hθsurj : ∀ x : ↥L, ∃ a : ↥H, θ a = (x : G) := by
    intro x
    have : (x : G) ∈ (L : Set G) := x.2
    rw [hH.diag] at this
    obtain ⟨a, ha, hax⟩ := this
    exact ⟨⟨a, ha⟩, hax.symm⟩
  let Θ : ↥H →* ↥L := θ.codRestrict L hθL
  have hΘ : Function.Bijective Θ := by
    refine ⟨fun a b hab => hθinj (congrArg Subtype.val hab), fun x => ?_⟩
    obtain ⟨a, ha⟩ := hθsurj x
    exact ⟨a, Subtype.ext ha⟩
  let eΘ : ↥H ≃* ↥L := MulEquiv.ofBijective Θ hΘ
  let Ψ : ↥L →* G := H.subtype.comp eΘ.symm.toMonoidHom
  have hΨ : ∀ x, Ψ x = ((eΘ.symm x : ↥H) : G) := fun x => rfl
  have hΨ2 : ∀ x : ↥L, Ψ x * (z * Ψ x * z⁻¹) = x := by
    intro x
    have h1 : (θ (eΘ.symm x) : G) = (x : G) := congrArg Subtype.val (eΘ.apply_symm_apply x)
    rw [hΨ]
    exact h1
  have hΨH : ∀ x, Ψ x ∈ H := fun x => (eΘ.symm x).2
  have hΨ3 : ∀ x y, Ψ x * (z * Ψ y * z⁻¹) = (z * Ψ y * z⁻¹) * Ψ x := fun x y =>
    hcomm (eΘ.symm x) (eΘ.symm y)
  have hΨinj : Function.Injective Ψ := fun x y hxy =>
    eΘ.symm.injective (Subtype.ext hxy)
  refine ⟨Ψ, hΨH, hΨ2, hΨ3, hΨinj, fun a ha => ⟨eΘ ⟨a, ha⟩, ?_⟩, fun x hx => ?_⟩
  · rw [hΨ]; simp
  · have hxH : (eΘ.symm x : ↥H) ∈ Subgroup.center ↥H := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 := hH.comm g g.2 (z * Ψ x * z⁻¹) ⟨Ψ x, hΨH x, rfl⟩
      rw [← hx] at h1
      show (g : G) * (eΘ.symm x : G) = (eΘ.symm x : G) * g
      rw [← hΨ]
      exact h1
    rw [hcen] at hxH
    have h2 : eΘ.symm x = 1 := Subgroup.mem_bot.1 hxH
    have h3 := congrArg eΘ h2
    simpa using h3

end GlobalLift

section Unique

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {z : G}
  {e : L ≃* alternatingGroup (Fin n)}

theorem isRootLift_of_global (S : Finset (Fin n)) {Ψ : ↥L →* G}
    (h2 : ∀ x, Ψ x * (z * Ψ x * z⁻¹) = x)
    (h3 : ∀ x y, Ψ x * (z * Ψ y * z⁻¹) = (z * Ψ y * z⁻¹) * Ψ x) (hinj : Function.Injective Ψ)
    (hrig : ∀ x, Ψ x = z * Ψ x * z⁻¹ → x = 1) :
    IsRootLift e z S (Ψ.comp (Subgroup.inclusion (corr_le (X := G) e (altSub Sᶜ)))) where
  inj := hinj.comp (Subgroup.inclusion_injective _)
  diag b := h2 (Subgroup.inclusion (corr_le (X := G) e (altSub Sᶜ)) b)
  comm a b := h3 _ _
  rigid x hx := Subgroup.inclusion_injective _ ((hrig _ hx).trans (map_one _).symm)
  cent b := by
    rw [mem_centralizer_iff]
    intro r hr
    set b' : ↥L := Subgroup.inclusion (corr_le (X := G) e (altSub Sᶜ)) b with hb'
    set r' : ↥L := ⟨r, corr_le (X := G) e (altSub S) hr⟩ with hr'
    have hbr : r' * b' = b' * r' :=
      Subtype.ext (corr_comm e (T₁ := altSub S) (T₂ := altSub Sᶜ)
        (fun g hg g' hg' => comm_of_altSub_disjoint disjoint_compl_right hg hg') r hr b b.2)
    have hΨbr : Ψ r' * Ψ b' = Ψ b' * Ψ r' := by rw [← map_mul, ← map_mul, hbr]
    have hr2 : r = Ψ r' * (z * Ψ r' * z⁻¹) := (h2 r').symm
    show r * Ψ b' = Ψ b' * r
    calc r * Ψ b' = (Ψ r' * (z * Ψ r' * z⁻¹)) * Ψ b' := by rw [← hr2]
      _ = Ψ r' * ((z * Ψ r' * z⁻¹) * Ψ b') := by group
      _ = Ψ r' * (Ψ b' * (z * Ψ r' * z⁻¹)) := by rw [h3 b' r']
      _ = (Ψ r' * Ψ b') * (z * Ψ r' * z⁻¹) := by group
      _ = (Ψ b' * Ψ r') * (z * Ψ r' * z⁻¹) := by rw [hΨbr]
      _ = Ψ b' * (Ψ r' * (z * Ψ r' * z⁻¹)) := by group
      _ = Ψ b' * r := by rw [← hr2]

theorem wreath_unique [Finite G] (h : ExactShape z L n) (hn : 11 ≤ n)
    (hIII : ∀ S : Finset (Fin n), S.card = 3 → CaseIIIAt e z S) {H₁ H₂ : Subgroup G}
    (h₁ : WreathPair L z n H₁) (h₂ : WreathPair L z n H₂) :
    H₂ = H₁ ∨ H₂ = H₁.map (MulAut.conj z).toMonoidHom := by
  classical
  have hz := sq_of_exactShape h
  obtain ⟨Ψ₁, hΨ₁H, hΨ₁2, hΨ₁3, hΨ₁inj, hΨ₁surj, hΨ₁rig⟩ := exists_global_lift h₁ (by omega)
  obtain ⟨Ψ₂, hΨ₂H, hΨ₂2, hΨ₂3, hΨ₂inj, hΨ₂surj, hΨ₂rig⟩ := exists_global_lift h₂ (by omega)
  let φ : ↥(altSub (Finset.univ : Finset (Fin n))) →*
      ↥(corr (X := G) e (altSub (Finset.univ : Finset (Fin n)))) :=
    corrIn (X := G) e (altSub_le_alternatingGroup _)
  let ι : ↥(corr (X := G) e (altSub (Finset.univ : Finset (Fin n)))) →* ↥L :=
    Subgroup.inclusion (corr_le (X := G) e _)
  let F : ↥(altSub (Finset.univ : Finset (Fin n))) →* G := Ψ₁.comp (ι.comp φ)
  let F' : ↥(altSub (Finset.univ : Finset (Fin n))) →* G := Ψ₂.comp (ι.comp φ)
  have hFinj : Function.Injective F :=
    hΨ₁inj.comp ((Subgroup.inclusion_injective (corr_le (X := G) e
      (altSub (Finset.univ : Finset (Fin n))))).comp (corrIn_injective (X := G) e _))
  obtain ⟨c, hc⟩ := exists_rel_of_cyc3 (z := z) (by simp; omega) (F := F) (F' := F') hFinj
    (fun x y => hΨ₂3 _ _) (fun a b c' ha hb hc' hab hbc hac hmem => by
      obtain ⟨S, hS, hdisj⟩ := exists_root_disjoint ({a, b, c'} : Finset (Fin n)) (by
        have := Finset.card_le_three (a := a) (b := b) (c := c')
        omega)
      have hTS : ({a, b, c'} : Finset (Fin n)) ⊆ Sᶜ := fun i hi => by
        simp only [Finset.mem_compl]
        exact fun hiS => Finset.disjoint_left.1 hdisj hiS hi
      have hxT : ((φ ⟨cyc3 a b c', hmem⟩ : ↥(corr (X := G) e (altSub Finset.univ))) : G) ∈
          corr (X := G) e (altSub ({a, b, c'} : Finset (Fin n))) := by
        show ((e.symm ⟨cyc3 a b c', altSub_le_alternatingGroup _ hmem⟩ : L) : G) ∈ _
        apply mem_corr_of_mem
        simp only [MulEquiv.apply_symm_apply]
        exact cyc3_mem_altSub (by simp) (by simp) (by simp) hab hbc hac
      have hxS : ((φ ⟨cyc3 a b c', hmem⟩ : ↥(corr (X := G) e (altSub Finset.univ))) : G) ∈
          corr (X := G) e (altSub Sᶜ) := corr_mono e (altSub_mono hTS) hxT
      exact rootLift_rel_local h hn hIII hS hS
        (isRootLift_of_global (e := e) S hΨ₁2 hΨ₁3 hΨ₁inj hΨ₁rig)
        (isRootLift_of_global (e := e) S hΨ₂2 hΨ₂3 hΨ₂inj hΨ₂rig) Finset.card_le_three hxS hxS hxT)
  have hall : ∀ x : ↥L, Ψ₁ x = cjHom z c (Ψ₂ x) := by
    intro x
    have hmem : ((e x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈
        altSub (Finset.univ : Finset (Fin n)) :=
      mem_altSub.2 ⟨Equiv.Perm.mem_alternatingGroup.1 (e x).2,
        fun i hi => absurd (Finset.mem_univ i) hi⟩
    have hφx : ι (φ ⟨(e x : Equiv.Perm (Fin n)), hmem⟩) = x := by
      apply Subtype.ext
      show ((e.symm ⟨(e x : Equiv.Perm (Fin n)), _⟩ : L) : G) = x
      simp
    have := hc ⟨(e x : Equiv.Perm (Fin n)), hmem⟩
    simp only [F, F', MonoidHom.comp_apply, hφx] at this
    exact this
  have hpow : z * z = 1 := hz
  cases c
  · left
    ext a
    constructor
    · intro ha
      obtain ⟨x, rfl⟩ := hΨ₂surj a ha
      have := hall x
      rw [cjHom_false] at this
      rw [← this]
      exact hΨ₁H x
    · intro ha
      obtain ⟨x, rfl⟩ := hΨ₁surj a ha
      have := hall x
      rw [cjHom_false] at this
      rw [this]
      exact hΨ₂H x
  · right
    ext a
    constructor
    · intro ha
      obtain ⟨x, rfl⟩ := hΨ₂surj a ha
      have := hall x
      rw [cjHom_true] at this
      refine ⟨z * Ψ₂ x * z⁻¹, ?_, ?_⟩
      · rw [← this]; exact hΨ₁H x
      · show z * (z * Ψ₂ x * z⁻¹) * z⁻¹ = Ψ₂ x
        exact conj_conj_of_sq hz _
    · rintro ⟨a', ha', rfl⟩
      obtain ⟨x, rfl⟩ := hΨ₁surj a' ha'
      have := hall x
      rw [cjHom_true] at this
      have h4 : z * Ψ₁ x * z⁻¹ = Ψ₂ x := by
        rw [this]; exact conj_conj_of_sq hz _
      show z * Ψ₁ x * z⁻¹ ∈ H₂
      rw [h4]; exact hΨ₂H x

end Unique

end CFSG.OddStandard.AltStdSec
