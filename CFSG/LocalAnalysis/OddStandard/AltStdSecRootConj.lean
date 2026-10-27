module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseOpen
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootOdd

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal Equiv

section PermPart

variable {n : ℕ}

theorem altSub_map_conj (σ : Perm (Fin n)) (S : Finset (Fin n)) :
    (altSub S).map (MulAut.conj σ).toMonoidHom = altSub (S.image σ) := by
  ext x
  rw [mem_map_conj_iff, mem_altSub, mem_altSub]
  constructor
  · rintro ⟨hs, hfix⟩
    refine ⟨?_, fun j hj => ?_⟩
    · have : Perm.sign (σ⁻¹ * x * σ) = Perm.sign x := by
        rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_right_comm, Int.units_mul_self,
          one_mul]
      rw [← this]
      exact hs
    · have hj' : σ⁻¹ j ∉ S := fun hmem => hj (Finset.mem_image.2 ⟨σ⁻¹ j, hmem, by simp⟩)
      have := hfix _ hj'
      simpa [Perm.mul_apply] using this
  · rintro ⟨hs, hfix⟩
    refine ⟨?_, fun i hi => ?_⟩
    · have : Perm.sign (σ⁻¹ * x * σ) = Perm.sign x := by
        rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_right_comm, Int.units_mul_self,
          one_mul]
      rw [this]
      exact hs
    · have hi' : σ i ∉ S.image σ := fun hmem => by
        obtain ⟨i', hi'S, hi'e⟩ := Finset.mem_image.1 hmem
        exact hi (σ.injective hi'e ▸ hi'S)
      simp only [Perm.mul_apply]
      rw [hfix _ hi']
      simp

theorem exists_even_perm_image_eq {S S' : Finset (Fin n)} (hcard : S.card = S'.card)
    (h2 : 2 ≤ S.card) : ∃ σ : Perm (Fin n), Perm.sign σ = 1 ∧ S.image σ = S' := by
  classical
  let e₀ : S ≃ S' := Finset.equivOfCardEq hcard
  let σ₀ : Perm (Fin n) :=
    Equiv.extendSubtype (p := fun x => x ∈ S) (q := fun x => x ∈ S') e₀
  have hσ₀ : ∀ x, σ₀ x ∈ S' ↔ x ∈ S := fun x => by
    constructor
    · intro hx
      by_contra hxS
      exact Equiv.extendSubtype_not_mem e₀ x hxS hx
    · exact fun hx => Equiv.extendSubtype_mem e₀ x hx
  have himg : ∀ ρ : Perm (Fin n), (∀ x, ρ x ∈ S' ↔ x ∈ S) → S.image ρ = S' := by
    intro ρ hρ
    ext j
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hρ x).2 hx
    · intro hj
      refine ⟨ρ⁻¹ j, (hρ _).1 (by simpa using hj), by simp⟩
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (by omega : 1 < S'.card)
  have hτ : ∀ x, (Equiv.swap u v) x ∈ S' ↔ x ∈ S' := fun x => by
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; exact ⟨fun _ => hu, fun _ => hv⟩
    · subst h2; exact ⟨fun _ => hv, fun _ => hu⟩
    · exact Iff.rfl
  by_cases hs : Perm.sign σ₀ = 1
  · exact ⟨σ₀, hs, himg σ₀ hσ₀⟩
  · refine ⟨Equiv.swap u v * σ₀, ?_, himg _ fun x => ?_⟩
    · have hs' : Perm.sign σ₀ = -1 := by
        rcases Int.units_eq_one_or (Perm.sign σ₀) with h1 | h1
        · exact absurd h1 hs
        · exact h1
      rw [Perm.sign_mul, hs', Perm.sign_swap huv]
      decide
    · rw [Perm.mul_apply, hτ, hσ₀]

end PermPart

section Corr

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (e : L ≃* alternatingGroup (Fin n))

theorem conjSub_corr (l : L) (T : Subgroup (Perm (Fin n))) :
    conjSub (l : G) (corr (X := G) e T) =
      corr e (T.map
        (MulAut.conj ((e l : alternatingGroup (Fin n)) : Perm (Fin n))).toMonoidHom) := by
  ext x
  rw [mem_conjSub_iff, mem_corr, mem_corr]
  constructor
  · rintro ⟨ha, hT⟩
    have hx : x ∈ L := by
      have := mul_mem (mul_mem l.2 ha) (inv_mem l.2)
      simpa [mul_assoc] using this
    refine ⟨hx, ?_⟩
    rw [mem_map_conj_iff]
    have h1 : (⟨(l : G)⁻¹ * x * l, ha⟩ : L) = l⁻¹ * ⟨x, hx⟩ * l := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv] at hT
    simpa using hT
  · rintro ⟨hx, hT⟩
    have ha : (l : G)⁻¹ * x * l ∈ L := mul_mem (mul_mem (inv_mem l.2) hx) l.2
    refine ⟨ha, ?_⟩
    rw [mem_map_conj_iff] at hT
    have h1 : (⟨(l : G)⁻¹ * x * l, ha⟩ : L) = l⁻¹ * ⟨x, hx⟩ * l := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
    simpa using hT

theorem rootGroup_eq_conjSub {σ : Perm (Fin n)} (hσ : Perm.sign σ = 1) {S S' : Finset (Fin n)}
    (h : S.image σ = S') :
    rootGroup (G := G) e S' =
      conjSub ((e.symm ⟨σ, Perm.mem_alternatingGroup.2 hσ⟩ : L) : G) (rootGroup e S) := by
  unfold rootGroup
  rw [conjSub_corr e, e.apply_symm_apply, altSub_map_conj, h]

end Corr

section ZStar

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem isZStar_rootGroup_of_card_eq (h : Setting G L n) (d : Cyc L Q z)
    (e : L ≃* alternatingGroup (Fin n)) {S S' : Finset (Fin n)} (hS : S.card = S'.card)
    (h2 : 2 ≤ S.card) (hz : IsZStar (rootGroup e S) z) : IsZStar (rootGroup e S') z := by
  obtain ⟨σ, hσ, himg⟩ := exists_even_perm_image_eq hS h2
  set l : L := e.symm ⟨σ, Perm.mem_alternatingGroup.2 hσ⟩ with hl
  have hlz : (l : G) * z * (l : G)⁻¹ = z := by
    have := mem_centralizer_singleton_iff.1 (le_centralizer_single h d l.2)
    rw [this]
    group
  have := hz.conj (l : G)
  rw [hlz, ← rootGroup_eq_conjSub e hσ himg] at this
  exact this

theorem isZStar_rootGroup_iff (h : Setting G L n) (d : Cyc L Q z)
    (e : L ≃* alternatingGroup (Fin n)) {S S' : Finset (Fin n)} (hS : S.card = S'.card)
    (h2 : 2 ≤ S.card) : IsZStar (rootGroup e S) z ↔ IsZStar (rootGroup e S') z :=
  ⟨isZStar_rootGroup_of_card_eq h d e hS h2,
    isZStar_rootGroup_of_card_eq h d e hS.symm (hS ▸ h2)⟩

end ZStar

end CFSG.OddStandard.AltStdSec
