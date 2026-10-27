module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootAut
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseOpen
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPermCent

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal Equiv

section Fix

variable {n : ℕ}

@[expose] def fixFin (σ : Perm (Fin n)) : Finset (Fin n) := Finset.univ.filter fun i => σ i = i

theorem mem_fixFin {σ : Perm (Fin n)} {i : Fin n} : i ∈ fixFin σ ↔ σ i = i := by
  simp [fixFin]

theorem card_fixedPoints_eq (σ : Perm (Fin n)) :
    Nat.card (Function.fixedPoints σ) = (fixFin σ).card := by
  have : Function.fixedPoints σ = ((fixFin σ : Finset (Fin n)) : Set (Fin n)) := by
    ext i
    simp [mem_fixFin, Function.fixedPoints, Function.IsFixedPt]
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem altSub_mono_fin {S T : Finset (Fin n)} (h : S ⊆ T) : altSub S ≤ altSub T := by
  intro σ hσ
  obtain ⟨hs, hfix⟩ := mem_altSub.1 hσ
  exact mem_altSub.2 ⟨hs, fun i hi => hfix i (fun hiS => hi (h hiS))⟩

end Fix

section Corr

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (e : L ≃* alternatingGroup (Fin n))

theorem mem_normalizer_corr_of_mem {T : Subgroup (Perm (Fin n))} {c : G} (hc : c ∈ L)
    (hT : ((e ⟨c, hc⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) ∈
      normalizer (T : Set (Perm (Fin n)))) : c ∈ normalizer (corr (X := G) e T : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  have hconj : ∀ (hx : x ∈ L) (hcx : c * x * c⁻¹ ∈ L),
      ((e ⟨c * x * c⁻¹, hcx⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) =
        ((e ⟨c, hc⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) *
          ((e ⟨x, hx⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) *
          ((e ⟨c, hc⟩ : alternatingGroup (Fin n)) : Perm (Fin n))⁻¹ := by
    intro hx hcx
    have h1 : (⟨c * x * c⁻¹, hcx⟩ : L) = ⟨c, hc⟩ * ⟨x, hx⟩ * ⟨c, hc⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
    simp
  constructor
  · intro hx
    obtain ⟨hxL, hxT⟩ := mem_corr.1 hx
    have hcx : c * x * c⁻¹ ∈ L := mul_mem (mul_mem hc hxL) (inv_mem hc)
    refine mem_corr.2 ⟨hcx, ?_⟩
    rw [hconj hxL hcx]
    exact (mem_normalizer_iff.1 hT _).1 hxT
  · intro hx
    obtain ⟨hcx, hcxT⟩ := mem_corr.1 hx
    have hxL : x ∈ L := by
      have := mul_mem (mul_mem (inv_mem hc) hcx) hc
      simpa [mul_assoc] using this
    refine mem_corr.2 ⟨hxL, ?_⟩
    rw [hconj hxL hcx] at hcxT
    exact (mem_normalizer_iff.1 hT _).2 hcxT

variable {y : G} (hy : y ∈ L)

theorem comm_of_mem_corr_of_fix {F : Finset (Fin n)}
    (hfix : ∀ i ∈ F, ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i = i) {w : G}
    (hw : w ∈ corr (X := G) e (altSub F)) : w * y = y * w := by
  obtain ⟨hwL, hT⟩ := mem_corr.1 hw
  have hye : ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ fixSub F := hfix
  have h1 := comm_altSub_fixSub hT hye
  have h2 : e (⟨w, hwL⟩ * ⟨y, hy⟩) = e (⟨y, hy⟩ * ⟨w, hwL⟩) := by
    rw [map_mul, map_mul]
    exact Subtype.ext h1
  have h3 := congrArg Subtype.val (e.injective h2)
  exact h3

theorem mem_normalizer_corr_fix {c : G} (hc : c ∈ L) (hcy : c * y = y * c) :
    c ∈ normalizer (corr (X := G) e
      (altSub (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)))) : Set G) := by
  refine mem_normalizer_corr_of_mem e hc (mem_normalizer_altSub fun i => ?_)
  have hcomm : ((e ⟨c, hc⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) *
      ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) =
        ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) *
          ((e ⟨c, hc⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    have h1 : e (⟨c, hc⟩ * ⟨y, hy⟩) = e (⟨y, hy⟩ * ⟨c, hc⟩) :=
      congrArg e (Subtype.ext hcy)
    rw [map_mul, map_mul] at h1
    exact congrArg Subtype.val h1
  rw [mem_fixFin, mem_fixFin]
  have h2 := congrArg (fun f : Perm (Fin n) => f i) hcomm
  simp only [Perm.mul_apply] at h2
  constructor
  · intro hi
    rw [← h2, hi]
  · intro hi
    have h3 : ((e ⟨c, hc⟩ : alternatingGroup (Fin n)) : Perm (Fin n))
        (((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i) =
          ((e ⟨c, hc⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i := by rw [h2, hi]
    exact ((e ⟨c, hc⟩ : alternatingGroup (Fin n)) : Perm (Fin n)).injective h3

end Corr

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (e : L ≃* alternatingGroup (Fin n))

noncomputable def altPre {F : Finset (Fin n)} (σ : ↥(altSub F)) : G :=
  ((e.symm ⟨σ.1, altSub_le_alternatingGroup F σ.2⟩ : L) : G)

theorem altPre_mem {F : Finset (Fin n)} (σ : ↥(altSub F)) :
    altPre e σ ∈ corr (X := G) e (altSub F) :=
  mem_corr_of_mem (a := e.symm ⟨σ.1, altSub_le_alternatingGroup F σ.2⟩) (by simp)

theorem altPre_mul {F : Finset (Fin n)} (σ τ : ↥(altSub F)) :
    altPre e (σ * τ) = altPre e σ * altPre e τ := by
  have : (⟨(σ * τ : ↥(altSub F)).1, altSub_le_alternatingGroup F (σ * τ).2⟩ :
      alternatingGroup (Fin n)) = ⟨σ.1, altSub_le_alternatingGroup F σ.2⟩ *
        ⟨τ.1, altSub_le_alternatingGroup F τ.2⟩ := rfl
  unfold altPre
  rw [this, map_mul]
  rfl

theorem altPre_one {F : Finset (Fin n)} : altPre e (1 : ↥(altSub F)) = 1 := by
  have : (⟨(1 : ↥(altSub F)).1, altSub_le_alternatingGroup F (1 : ↥(altSub F)).2⟩ :
      alternatingGroup (Fin n)) = 1 := rfl
  unfold altPre
  rw [this, map_one]
  rfl

theorem altPre_injective {F : Finset (Fin n)} :
    Function.Injective (altPre (G := G) e (F := F)) := by
  intro σ τ h
  have h1 : (e.symm ⟨σ.1, altSub_le_alternatingGroup F σ.2⟩ : L) =
      e.symm ⟨τ.1, altSub_le_alternatingGroup F τ.2⟩ := Subtype.ext h
  have h2 := e.symm.injective h1
  exact Subtype.ext (Subtype.mk.inj h2)

theorem altPre_e {F : Finset (Fin n)} {w : G} (hw : w ∈ corr (X := G) e (altSub F)) :
    altPre e ⟨((e ⟨w, corr_le e _ hw⟩ : alternatingGroup (Fin n)) : Perm (Fin n)),
      (mem_corr.1 hw).2⟩ = w := by
  unfold altPre
  simp

noncomputable def conjHom (g : G) {F F' : Finset (Fin n)}
    (hFF' : ∀ x ∈ corr (X := G) e (altSub F), g⁻¹ * x * g ∈ corr (X := G) e (altSub F')) :
    ↥(altSub F) →* ↥(altSub F') where
  toFun σ := ⟨((e ⟨g⁻¹ * altPre e σ * g, corr_le e _ (hFF' _ (altPre_mem e σ))⟩ :
      alternatingGroup (Fin n)) : Perm (Fin n)), (mem_corr.1 (hFF' _ (altPre_mem e σ))).2⟩
  map_one' := by
    apply Subtype.ext
    have : (⟨g⁻¹ * altPre e (1 : ↥(altSub F)) * g, corr_le e _ (hFF' _ (altPre_mem e 1))⟩ : L) =
        1 := Subtype.ext (by
          show g⁻¹ * altPre e (1 : ↥(altSub F)) * g = 1
          rw [altPre_one]
          group)
    show ((e ⟨g⁻¹ * altPre e (1 : ↥(altSub F)) * g, _⟩ : alternatingGroup (Fin n)) :
      Perm (Fin n)) = 1
    rw [this, map_one]
    rfl
  map_mul' σ τ := by
    apply Subtype.ext
    have : (⟨g⁻¹ * altPre e (σ * τ) * g, corr_le e _ (hFF' _ (altPre_mem e (σ * τ)))⟩ : L) =
        ⟨g⁻¹ * altPre e σ * g, corr_le e _ (hFF' _ (altPre_mem e σ))⟩ *
          ⟨g⁻¹ * altPre e τ * g, corr_le e _ (hFF' _ (altPre_mem e τ))⟩ :=
      Subtype.ext (by
        show g⁻¹ * altPre e (σ * τ) * g = (g⁻¹ * altPre e σ * g) * (g⁻¹ * altPre e τ * g)
        rw [altPre_mul]
        group)
    show ((e ⟨g⁻¹ * altPre e (σ * τ) * g, _⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) = _
    rw [this, map_mul]
    rfl

theorem exists_conj_intertwining {F F' : Finset (Fin n)} (g : G) (hcard : F.card = F'.card)
    (hf : (5 ≤ F.card ∧ F.card ≠ 6) ∨ F.card = 4)
    (hFF' : ∀ x ∈ corr (X := G) e (altSub F), g⁻¹ * x * g ∈ corr (X := G) e (altSub F'))
    (hF'F : ∀ x ∈ corr (X := G) e (altSub F'), g * x * g⁻¹ ∈ corr (X := G) e (altSub F)) :
    ∃ β : Fin n → Fin n, (∀ i ∈ F, β i ∈ F') ∧ (∀ i ∈ F, ∀ j ∈ F, β i = β j → i = j) ∧
      (∀ j ∈ F', ∃ i ∈ F, β i = j) ∧
      ∀ (w : G) (hw : w ∈ corr (X := G) e (altSub F)), ∀ i ∈ F,
        ((e ⟨g⁻¹ * w * g, corr_le e _ (hFF' w hw)⟩ : alternatingGroup (Fin n)) : Perm (Fin n))
            (β i) =
          β (((e ⟨w, corr_le e _ hw⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i) := by
  have hinj : Function.Injective (conjHom e g hFF') := by
    intro σ τ h
    have h1 : ((conjHom e g hFF' σ : ↥(altSub F')) : Perm (Fin n)) =
        ((conjHom e g hFF' τ : ↥(altSub F')) : Perm (Fin n)) := congrArg Subtype.val h
    have h2 := e.injective (Subtype.ext h1)
    have h3 : g⁻¹ * altPre e σ * g = g⁻¹ * altPre e τ * g := congrArg Subtype.val h2
    have h4 : altPre e σ = altPre e τ := by
      have := mul_right_cancel h3
      exact mul_left_cancel this
    exact altPre_injective e h4
  have hsurj : Function.Surjective (conjHom e g hFF') := by
    intro τ'
    have hx' := altPre_mem e τ'
    have hx := hF'F _ hx'
    refine ⟨⟨((e ⟨g * altPre e τ' * g⁻¹, corr_le e _ hx⟩ : alternatingGroup (Fin n)) :
      Perm (Fin n)), (mem_corr.1 hx).2⟩, ?_⟩
    apply Subtype.ext
    have h1 : (⟨g⁻¹ * altPre e ⟨((e ⟨g * altPre e τ' * g⁻¹, corr_le e _ hx⟩ :
        alternatingGroup (Fin n)) : Perm (Fin n)), (mem_corr.1 hx).2⟩ * g,
          corr_le e _ (hFF' _ (altPre_mem e _))⟩ : L) =
        ⟨altPre e τ', corr_le e _ hx'⟩ := Subtype.ext (by
      show g⁻¹ * altPre e _ * g = altPre e τ'
      rw [altPre_e e hx]
      group)
    show ((e ⟨g⁻¹ * altPre e ⟨((e ⟨g * altPre e τ' * g⁻¹, corr_le e _ hx⟩ :
        alternatingGroup (Fin n)) : Perm (Fin n)), (mem_corr.1 hx).2⟩ * g, _⟩ :
          alternatingGroup (Fin n)) : Perm (Fin n)) = τ'.1
    rw [h1]
    have : e ⟨altPre e τ', corr_le e _ hx'⟩ = ⟨τ'.1, altSub_le_alternatingGroup F' τ'.2⟩ := by
      have h2 : (⟨altPre e τ', corr_le e _ hx'⟩ : L) =
          e.symm ⟨τ'.1, altSub_le_alternatingGroup F' τ'.2⟩ := rfl
      rw [h2, MulEquiv.apply_symm_apply]
    rw [this]
  obtain ⟨β, h1, h2, h3, h4⟩ := exists_intertwining_bijection hcard hf
    (MulEquiv.ofBijective (conjHom e g hFF') ⟨hinj, hsurj⟩)
  refine ⟨β, h1, h2, h3, fun w hw i hi => ?_⟩
  have h5 := h4 ((e ⟨w, corr_le e _ hw⟩ : alternatingGroup (Fin n)) : Perm (Fin n))
    (mem_corr.1 hw).2 i hi
  have h6 : (⟨g⁻¹ * altPre e ⟨((e ⟨w, corr_le e _ hw⟩ : alternatingGroup (Fin n)) :
      Perm (Fin n)), (mem_corr.1 hw).2⟩ * g, corr_le e _ (hFF' _ (altPre_mem e _))⟩ : L) =
      ⟨g⁻¹ * w * g, corr_le e _ (hFF' w hw)⟩ := Subtype.ext (by
    show g⁻¹ * altPre e _ * g = g⁻¹ * w * g
    rw [altPre_e e hw])
  have h7 : ((MulEquiv.ofBijective (conjHom e g hFF') ⟨hinj, hsurj⟩
      ⟨((e ⟨w, corr_le e _ hw⟩ : alternatingGroup (Fin n)) : Perm (Fin n)), (mem_corr.1 hw).2⟩ :
        ↥(altSub F')) : Perm (Fin n)) =
      ((e ⟨g⁻¹ * w * g, corr_le e _ (hFF' w hw)⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    show ((e ⟨g⁻¹ * altPre e ⟨((e ⟨w, corr_le e _ hw⟩ : alternatingGroup (Fin n)) :
      Perm (Fin n)), (mem_corr.1 hw).2⟩ * g, _⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) = _
    rw [h6]
  rw [← h7]
  exact h5

end Transport

section Final

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (e : L ≃* alternatingGroup (Fin n))

theorem rootGroup_eq_conjSub_image {F F' : Finset (Fin n)} (g : G)
    (hFF' : ∀ x ∈ corr (X := G) e (altSub F), g⁻¹ * x * g ∈ corr (X := G) e (altSub F'))
    (hF'F : ∀ x ∈ corr (X := G) e (altSub F'), g * x * g⁻¹ ∈ corr (X := G) e (altSub F))
    {β : Fin n → Fin n} (hβ1 : ∀ i ∈ F, β i ∈ F') (hβ2 : ∀ i ∈ F, ∀ j ∈ F, β i = β j → i = j)
    (hβ3 : ∀ j ∈ F', ∃ i ∈ F, β i = j)
    (hβ4 : ∀ (w : G) (hw : w ∈ corr (X := G) e (altSub F)), ∀ i ∈ F,
      ((e ⟨g⁻¹ * w * g, corr_le e _ (hFF' w hw)⟩ : alternatingGroup (Fin n)) : Perm (Fin n))
          (β i) =
        β (((e ⟨w, corr_le e _ hw⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i))
    {S : Finset (Fin n)} (hS : S ⊆ F) :
    rootGroup (G := G) e S = conjSub g (rootGroup e (S.image β)) := by
  have hSβ : S.image β ⊆ F' := fun j hj => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    exact hβ1 i (hS hi)
  ext x
  rw [mem_conjSub_iff]
  show x ∈ corr (X := G) e (altSub S) ↔ g⁻¹ * x * g ∈ corr (X := G) e (altSub (S.image β))
  constructor
  · intro hx
    obtain ⟨hxL, hxS⟩ := mem_corr.1 hx
    have hxF : x ∈ corr (X := G) e (altSub F) := mem_corr.2 ⟨hxL, altSub_mono_fin hS hxS⟩
    have hy' := hFF' x hxF
    obtain ⟨hyL, hρ⟩ := mem_corr.1 hy'
    refine mem_corr.2 ⟨hyL, mem_altSub.2 ⟨(mem_altSub.1 hρ).1, fun j hj => ?_⟩⟩
    by_cases hjF' : j ∈ F'
    · obtain ⟨i, hiF, rfl⟩ := hβ3 j hjF'
      have hiS : i ∉ S := fun hiS => hj (Finset.mem_image.2 ⟨i, hiS, rfl⟩)
      have h1 := hβ4 x hxF i hiF
      have h2 : ((e ⟨x, hxL⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i = i :=
        (mem_altSub.1 hxS).2 i hiS
      rw [h2] at h1
      exact h1
    · exact (mem_altSub.1 hρ).2 j hjF'
  · intro hx
    obtain ⟨hyL, hρS⟩ := mem_corr.1 hx
    have hρF' := altSub_mono_fin hSβ hρS
    have hx' : g⁻¹ * x * g ∈ corr (X := G) e (altSub F') := mem_corr.2 ⟨hyL, hρF'⟩
    have hxF : x ∈ corr (X := G) e (altSub F) := by
      have := hF'F _ hx'
      simpa [mul_assoc] using this
    obtain ⟨hxL, hσF⟩ := mem_corr.1 hxF
    refine mem_corr.2 ⟨hxL, mem_altSub.2 ⟨(mem_altSub.1 hσF).1, fun i hi => ?_⟩⟩
    by_cases hiF : i ∈ F
    · have h1 := hβ4 x hxF i hiF
      have hβi : β i ∉ S.image β := fun hmem => by
        obtain ⟨s, hs, hsi⟩ := Finset.mem_image.1 hmem
        exact hi (hβ2 s (hS hs) i hiF hsi ▸ hs)
      have h2 : ((e ⟨g⁻¹ * x * g, corr_le e _ (hFF' x hxF)⟩ : alternatingGroup (Fin n)) :
          Perm (Fin n)) (β i) = β i := (mem_altSub.1 hρS).2 _ hβi
      rw [h2] at h1
      have hσi : ((e ⟨x, hxL⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i ∈ F :=
        (rootAut_mem_iff_of_fix (mem_altSub.1 hσF).2 i).2 hiF
      exact (hβ2 _ hσi i hiF h1.symm)
    · exact (mem_altSub.1 hσF).2 i hiF

end Final

end CFSG.OddStandard.AltStdSec
