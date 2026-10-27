module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecPerm
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AutAlternatingFour

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Subgroup

section Hom

variable {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ} {F : Finset α}

omit [Fintype α] in
theorem rootAut_mem_iff_of_fix {g : Perm α} (hg : ∀ i, i ∉ F → g i = i) (x : α) :
    g x ∈ F ↔ x ∈ F := by
  constructor
  · intro hx
    by_contra hxF
    rw [hg x hxF] at hx
    exact hxF hx
  · intro hx
    by_contra hgx
    have h2 : g x = x := g.injective (hg (g x) hgx)
    rw [h2] at hgx
    exact hgx hx

noncomputable def rootAutHom (u : Fin m ≃ {x // x ∈ F}) :
    alternatingGroup (Fin m) →* altSub F :=
  ((Perm.extendDomainHom u).comp (alternatingGroup (Fin m)).subtype).codRestrict (altSub F)
    (fun σ₀ => mem_altSub.2
      ⟨by simpa using Perm.mem_alternatingGroup.1 σ₀.2,
        fun i hi => Perm.extendDomain_apply_not_subtype _ _ hi⟩)

theorem rootAutHom_apply_coe (u : Fin m ≃ {x // x ∈ F}) (σ₀ : alternatingGroup (Fin m)) :
    ((rootAutHom u σ₀ : altSub F) : Perm α) = (σ₀ : Perm (Fin m)).extendDomain u := by
  simp [rootAutHom]

theorem rootAutHom_injective (u : Fin m ≃ {x // x ∈ F}) : Function.Injective (rootAutHom u) := by
  intro a b hab
  have h1 : (a : Perm (Fin m)).extendDomain u = (b : Perm (Fin m)).extendDomain u := by
    rw [← rootAutHom_apply_coe, ← rootAutHom_apply_coe, hab]
  exact Subtype.ext (Perm.extendDomainHom_injective u h1)

theorem rootAutHom_surjective (u : Fin m ≃ {x // x ∈ F}) : Function.Surjective (rootAutHom u) := by
  rintro ⟨g, hg⟩
  obtain ⟨hs, hfix⟩ := mem_altSub.1 hg
  have hpres : ∀ x, g x ∈ F ↔ x ∈ F := rootAut_mem_iff_of_fix hfix
  set σ₀ : Perm (Fin m) := (Equiv.permCongr u.symm) (g.subtypePerm hpres) with hσ₀
  have hext : σ₀.extendDomain u = g := by
    ext x
    by_cases hx : x ∈ F
    · rw [Perm.extendDomain_apply_subtype σ₀ u hx]
      simp [hσ₀]
    · rw [Perm.extendDomain_apply_not_subtype σ₀ u hx, hfix x hx]
  have hsign : Perm.sign σ₀ = 1 := by
    rw [← Perm.sign_extendDomain σ₀ u, hext, hs]
  exact ⟨⟨σ₀, Perm.mem_alternatingGroup.2 hsign⟩, Subtype.ext hext⟩

noncomputable def rootAutEquiv (u : Fin m ≃ {x // x ∈ F}) :
    alternatingGroup (Fin m) ≃* altSub F :=
  MulEquiv.ofBijective (rootAutHom u) ⟨rootAutHom_injective u, rootAutHom_surjective u⟩

theorem rootAutEquiv_apply (u : Fin m ≃ {x // x ∈ F}) (σ₀ : alternatingGroup (Fin m))
    (j : Fin m) :
    ((rootAutEquiv u σ₀ : altSub F) : Perm α) (u j) = u ((σ₀ : Perm (Fin m)) j) :=
  Perm.extendDomain_apply_image (σ₀ : Perm (Fin m)) u j

end Hom

section Aut

theorem rootAut_exists_conj {m : ℕ} (hm : (5 ≤ m ∧ m ≠ 6) ∨ m = 4)
    (φ : MulAut (alternatingGroup (Fin m))) :
    ∃ π : Perm (Fin m), MulAut.conjNormal (H := alternatingGroup (Fin m)) π = φ := by
  rcases hm with ⟨h5, h6⟩ | rfl
  · exact (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m h5 h6).2 φ
  · exact CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj.2 φ

variable {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ} {F F' : Finset α}

theorem rootAut_exists_perm (hm : (5 ≤ m ∧ m ≠ 6) ∨ m = 4) (u : Fin m ≃ {x // x ∈ F})
    (u' : Fin m ≃ {x // x ∈ F'}) (θ : altSub F ≃* altSub F') :
    ∃ π : Perm (Fin m), ∀ (σ₀ : alternatingGroup (Fin m)) (j : Fin m),
      ((θ (rootAutEquiv u σ₀) : altSub F') : Perm α) (u' (π j)) =
        u' (π ((σ₀ : Perm (Fin m)) j)) := by
  obtain ⟨π, hπ⟩ := rootAut_exists_conj hm
    ((rootAutEquiv u).trans (θ.trans (rootAutEquiv u').symm))
  refine ⟨π, fun σ₀ j => ?_⟩
  have h1 : rootAutEquiv u' (MulAut.conjNormal (H := alternatingGroup (Fin m)) π σ₀) =
      θ (rootAutEquiv u σ₀) := by
    rw [hπ]
    simp
  rw [← h1, rootAutEquiv_apply]
  congr 1
  rw [MulAut.conjNormal_apply]
  simp

end Aut

section Main

variable {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ} {F F' : Finset α}

theorem rootAut_exists_bijection (hm : (5 ≤ m ∧ m ≠ 6) ∨ m = 4) (u : Fin m ≃ {x // x ∈ F})
    (u' : Fin m ≃ {x // x ∈ F'}) (θ : altSub F ≃* altSub F') :
    ∃ β : α → α, (∀ i ∈ F, β i ∈ F') ∧ (∀ i ∈ F, ∀ j ∈ F, β i = β j → i = j) ∧
      (∀ j ∈ F', ∃ i ∈ F, β i = j) ∧
      ∀ (σ : Perm α) (hσ : σ ∈ altSub F), ∀ i ∈ F,
        ((θ ⟨σ, hσ⟩ : altSub F') : Perm α) (β i) = β (σ i) := by
  obtain ⟨π, hπ⟩ := rootAut_exists_perm hm u u' θ
  let e : {x // x ∈ F} ≃ {x // x ∈ F'} := (u.symm.trans π).trans u'
  refine ⟨fun i => if h : i ∈ F then ((e ⟨i, h⟩ : {x // x ∈ F'}) : α) else i, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [hi, dite_true]
    exact (e ⟨i, hi⟩).2
  · intro i hi j hj hij
    simp only [hi, hj, dite_true] at hij
    exact congrArg Subtype.val (e.injective (Subtype.ext hij))
  · intro j hj
    refine ⟨(e.symm ⟨j, hj⟩ : α), (e.symm ⟨j, hj⟩).2, ?_⟩
    simp only [(e.symm ⟨j, hj⟩).2, dite_true]
    simp
  · intro σ hσ i hi
    obtain ⟨σ₀, hσσ⟩ := (rootAutEquiv u).surjective ⟨σ, hσ⟩
    set j := u.symm ⟨i, hi⟩ with hj
    have hij : (u j : α) = i := by simp [hj]
    have h1 : σ i = ((u ((σ₀ : Perm (Fin m)) j) : {x // x ∈ F}) : α) := by
      rw [← hij]
      have := rootAutEquiv_apply u σ₀ j
      rw [hσσ] at this
      exact this
    have hmem : σ i ∈ F := by rw [h1]; exact (u _).2
    have h2 : (⟨σ i, hmem⟩ : {x // x ∈ F}) = u ((σ₀ : Perm (Fin m)) j) := Subtype.ext h1
    have he1 : e ⟨i, hi⟩ = u' (π j) := rfl
    have he2 : e ⟨σ i, hmem⟩ = u' (π ((σ₀ : Perm (Fin m)) j)) := by
      show u' (π (u.symm ⟨σ i, hmem⟩)) = _
      rw [h2, Equiv.symm_apply_apply]
    simp only [hi, hmem, dite_true]
    rw [he1, he2]
    have := hπ σ₀ j
    rw [hσσ] at this
    exact this

end Main

theorem exists_intertwining_bijection {n : ℕ} {F F' : Finset (Fin n)} (hcard : F.card = F'.card)
    (hf : (5 ≤ F.card ∧ F.card ≠ 6) ∨ F.card = 4) (θ : altSub F ≃* altSub F') :
    ∃ β : Fin n → Fin n, (∀ i ∈ F, β i ∈ F') ∧ (∀ i ∈ F, ∀ j ∈ F, β i = β j → i = j) ∧
      (∀ j ∈ F', ∃ i ∈ F, β i = j) ∧
      ∀ (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ altSub F), ∀ i ∈ F,
        ((θ ⟨σ, hσ⟩ : altSub F') : Equiv.Perm (Fin n)) (β i) = β (σ i) :=
  rootAut_exists_bijection hf F.equivFin.symm ((finCongr hcard).trans F'.equivFin.symm) θ

end CFSG.OddStandard.AltStdSec
