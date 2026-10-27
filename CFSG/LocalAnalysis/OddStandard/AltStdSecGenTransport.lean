module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenCase
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreSubgroup
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Subgroup

section EvenPerm

variable {n : ℕ}

theorem exists_even_perm_of_card_eq {S S' : Finset (Fin n)} (hS : S.card = S'.card)
    (hSc : 2 ≤ Sᶜ.card) :
    ∃ π : Perm (Fin n), Perm.sign π = 1 ∧ ∀ x, x ∈ S ↔ π x ∈ S' := by
  classical
  let e₀ : {x // x ∈ S} ≃ {x // x ∈ S'} := Finset.equivOfCardEq hS
  let σ : Perm (Fin n) := e₀.extendSubtype
  have hσ : ∀ x, x ∈ S ↔ σ x ∈ S' := fun x => by
    constructor
    · intro hx
      exact e₀.extendSubtype_mem x hx
    · intro hx
      by_contra hxS
      exact e₀.extendSubtype_not_mem x hxS hx
  by_cases hs : Perm.sign σ = 1
  · exact ⟨σ, hs, hσ⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hSc
    have haS : a ∉ S := by simpa using ha
    have hbS : b ∉ S := by simpa using hb
    refine ⟨σ * swap a b, ?_, fun x => ?_⟩
    · rw [Perm.sign_mul, Perm.sign_swap hab]
      have : Perm.sign σ = -1 := by
        rcases Int.units_eq_one_or (Perm.sign σ) with h | h
        · exact absurd h hs
        · exact h
      rw [this]; rfl
    · have hsw : swap a b x ∈ S ↔ x ∈ S := by
        by_cases hxa : x = a
        · subst hxa; simp [swap_apply_left, haS, hbS]
        · by_cases hxb : x = b
          · subst hxb; simp [swap_apply_right, haS, hbS]
          · rw [swap_apply_of_ne_of_ne hxa hxb]
      rw [Perm.mul_apply, ← hσ, hsw]

end EvenPerm

section Conj

variable {n : ℕ}

theorem altSub_conj_iff {π : Perm (Fin n)} {T T' : Finset (Fin n)}
    (hT : ∀ x, x ∈ T ↔ π x ∈ T') (g : Perm (Fin n)) :
    g ∈ altSub T ↔ π * g * π⁻¹ ∈ altSub T' := by
  have hsign : Perm.sign (π * g * π⁻¹) = Perm.sign g := by
    simp only [Perm.sign_mul, Perm.sign_inv]
    rw [mul_right_comm, Int.units_mul_self, one_mul]
  rw [mem_altSub, mem_altSub, hsign]
  refine and_congr_right fun _ => ⟨fun h i hi => ?_, fun h j hj => ?_⟩
  · have hj : π⁻¹ i ∉ T := fun hj' => hi (by simpa using (hT _).1 hj')
    show π (g (π⁻¹ i)) = i
    rw [h _ hj]; simp
  · have hj' : π j ∉ T' := fun h' => hj ((hT j).2 h')
    have := h (π j) hj'
    simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply] at this
    exact π.injective this

variable {G : Type} [Group G] {L : Subgroup G}

theorem corr_conj_iff (e : L ≃* alternatingGroup (Fin n)) {π : Perm (Fin n)}
    (hπ : π ∈ alternatingGroup (Fin n)) {T T' : Finset (Fin n)}
    (hT : ∀ x, x ∈ T ↔ π x ∈ T') (x : G) :
    x ∈ corr (X := G) e (altSub T) ↔
      ((e.symm ⟨π, hπ⟩ : L) : G) * x * ((e.symm ⟨π, hπ⟩ : L) : G)⁻¹ ∈
        corr (X := G) e (altSub T') := by
  set l : L := e.symm ⟨π, hπ⟩ with hl
  have hel : e l = ⟨π, hπ⟩ := by simp [hl]
  rw [mem_corr, mem_corr]
  constructor
  · rintro ⟨hxA, hx⟩
    have hy : (l : G) * x * (l : G)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem l.2 hxA) (L.inv_mem l.2)
    refine ⟨hy, ?_⟩
    have h1 : (⟨(l : G) * x * (l : G)⁻¹, hy⟩ : L) = l * ⟨x, hxA⟩ * l⁻¹ := rfl
    rw [h1, map_mul, map_mul, hel, map_inv, hel]
    exact (altSub_conj_iff hT _).1 hx
  · rintro ⟨hyA, hy⟩
    have hxA : x ∈ L := by
      have := L.mul_mem (L.mul_mem (L.inv_mem l.2) hyA) l.2
      simpa [mul_assoc] using this
    refine ⟨hxA, ?_⟩
    have h1 : (⟨(l : G) * x * (l : G)⁻¹, hyA⟩ : L) = l * ⟨x, hxA⟩ * l⁻¹ := rfl
    rw [h1, map_mul, map_mul, hel, map_inv, hel] at hy
    exact (altSub_conj_iff hT _).2 hy

end Conj

section Transport

theorem layer_map_mulEquiv {X X' : Type*} [Group X] [Group X'] (Φ : X ≃* X') :
    (CFSG.layer X).map Φ.toMonoidHom = CFSG.layer X' :=
  CFSG.WholeGroup.layer_map_mulEquiv Φ

theorem WreathOutcome.map {X X' : Type} [Group X] [Group X'] (Φ : X ≃* X') {t : X}
    {A : Subgroup X} {m : ℕ} (h : WreathOutcome t A m) :
    WreathOutcome (Φ t) (A.map Φ.toMonoidHom) m := by
  obtain ⟨K, hKc, hKne, hlayer, ⟨eK⟩, hA⟩ := h
  have hconj : (K.map Φ.toMonoidHom).map (MulAut.conj (Φ t)).toMonoidHom =
      (K.map (MulAut.conj t).toMonoidHom).map Φ.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  refine ⟨K.map Φ.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv Φ hKc, ?_, ?_,
    ⟨(K.equivMapOfInjective Φ.toMonoidHom Φ.injective).symm.trans eK⟩, ?_⟩
  · intro hcon
    apply hKne
    rw [hconj] at hcon
    exact Subgroup.map_injective Φ.injective hcon
  · rw [← layer_map_mulEquiv Φ, hlayer, Subgroup.map_sup, hconj]
  · ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ha' : a ∈ (A : Set X) := ha
      rw [hA] at ha'
      obtain ⟨k, hk, rfl⟩ := ha'
      exact ⟨Φ k, ⟨k, hk, rfl⟩, by simp [map_mul, map_inv]⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨k * (t * k * t⁻¹), ?_, by simp [map_mul, map_inv]⟩
      have : k * (t * k * t⁻¹) ∈ (A : Set X) := by rw [hA]; exact ⟨k, hk, rfl⟩
      exact this

end Transport

section CaseIIITransport

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}

theorem caseIIIAt_transport (h : ExactShape z L n) (e : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) {S S' : Finset (Fin n)} (hS : S.card = 3) (hS' : S'.card = 3)
    (hIII : CaseIIIAt e z S) : CaseIIIAt e z S' := by
  obtain ⟨ht, hW⟩ := hIII
  have ht' : z ∈ centralizer (corr (X := G) e (altSub S') : Set G) :=
    t_mem_centralizer_corr (X := G) e h (altSub S')
  obtain ⟨π, hsign, hπ⟩ := exists_even_perm_of_card_eq (hS.trans hS'.symm)
    (by rw [card_compl_fin, hS]; omega)
  have hπA : π ∈ alternatingGroup (Fin n) := Perm.mem_alternatingGroup.2 hsign
  have hπc : ∀ x, x ∈ Sᶜ ↔ π x ∈ S'ᶜ := fun x => by simp [hπ x]
  set lg : G := ((e.symm ⟨π, hπA⟩ : L) : G) with hlg
  have hlgL : lg ∈ L := (e.symm ⟨π, hπA⟩ : L).2
  have hlz : lg * z * lg⁻¹ = z := by
    have := mem_centralizer_singleton_iff.1 (h.le_cent hlgL)
    rw [this]; group
  have hRS := corr_conj_iff (G := G) e hπA hπ
  have hBS := corr_conj_iff (G := G) e hπA hπc
  have hCC : ∀ x : G, x ∈ centralizer (corr (X := G) e (altSub S) : Set G) ↔
      lg * x * lg⁻¹ ∈ centralizer (corr (X := G) e (altSub S') : Set G) := by
    intro x
    rw [mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro hx r' hr'
      have hr : lg⁻¹ * r' * lg ∈ corr (X := G) e (altSub S) := by
        refine (hRS _).2 ?_
        have h3 : lg * (lg⁻¹ * r' * lg) * lg⁻¹ = r' := by group
        rw [h3]; exact hr'
      have := hx _ hr
      calc r' * (lg * x * lg⁻¹) = lg * ((lg⁻¹ * r' * lg) * x) * lg⁻¹ := by group
        _ = lg * (x * (lg⁻¹ * r' * lg)) * lg⁻¹ := by rw [this]
        _ = (lg * x * lg⁻¹) * r' := by group
    · intro hx r hr
      have := hx (lg * r * lg⁻¹) ((hRS r).1 hr)
      have h2 : lg * (r * x) * lg⁻¹ = lg * (x * r) * lg⁻¹ := by
        calc lg * (r * x) * lg⁻¹ = (lg * r * lg⁻¹) * (lg * x * lg⁻¹) := by group
          _ = (lg * x * lg⁻¹) * (lg * r * lg⁻¹) := this
          _ = lg * (x * r) * lg⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
  let cC : ↥(centralizer (corr (X := G) e (altSub S) : Set G)) ≃*
      ↥(centralizer (corr (X := G) e (altSub S') : Set G)) :=
    { toFun := fun x => ⟨lg * (x : G) * lg⁻¹, (hCC x).1 x.2⟩
      invFun := fun y => ⟨lg⁻¹ * (y : G) * lg, (hCC _).2 (by simp [mul_assoc])⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hcC : ∀ x, ((cC x : ↥(centralizer (corr (X := G) e (altSub S') : Set G))) : G) =
      lg * (x : G) * lg⁻¹ := fun x => rfl
  have hodd := ClassicalInvolution.QuaternionStructure.oddCore_map_mulEquiv cC
  let Φ : Sec G (corr (X := G) e (altSub S)) ≃* Sec G (corr (X := G) e (altSub S')) :=
    QuotientGroup.congr _ _ cC hodd
  have hΦmk : ∀ x, Φ (QuotientGroup.mk x) = QuotientGroup.mk (cC x) := fun x => rfl
  have hΦz : Φ (QuotientGroup.mk ⟨z, ht⟩) = QuotientGroup.mk ⟨z, ht'⟩ := by
    rw [hΦmk]
    congr 1
    exact Subtype.ext hlz
  have hBsub : ((corr (X := G) e (altSub Sᶜ)).subgroupOf
        (centralizer (corr (X := G) e (altSub S) : Set G))).map cC.toMonoidHom =
      (corr (X := G) e (altSub S'ᶜ)).subgroupOf
        (centralizer (corr (X := G) e (altSub S') : Set G)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show lg * (x : G) * lg⁻¹ ∈ corr (X := G) e (altSub S'ᶜ)
      exact (hBS x).1 hx
    · intro hy
      refine ⟨cC.symm y, ?_, cC.apply_symm_apply y⟩
      show lg⁻¹ * (y : G) * lg ∈ corr (X := G) e (altSub Sᶜ)
      refine (hBS _).2 ?_
      have h3 : lg * (lg⁻¹ * (y : G) * lg) * lg⁻¹ = (y : G) := by group
      rw [h3]; exact hy
  have hΦA : (secComp e S).map Φ.toMonoidHom = secComp e S' := by
    unfold secComp
    rw [Subgroup.map_map, ← hBsub, Subgroup.map_map]
    congr 1
  have hmap := hW.map Φ
  rw [hΦz, hΦA] at hmap
  refine ⟨ht', ?_⟩
  have hc : n - S.card = n - S'.card := by rw [hS, hS']
  rw [← hc]
  exact hmap

end CaseIIITransport

end CFSG.OddStandard.AltStdSec
