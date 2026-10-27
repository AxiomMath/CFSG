module

public import CFSG.CGT.T75I.NSixA
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Equiv Equiv.Perm Subgroup

abbrev OtherPts (p q : Fin 8) : Type := {x : Fin 8 // x ≠ p ∧ x ≠ q}

theorem card_otherPts {p q : Fin 8} (hpq : p ≠ q) : Fintype.card (OtherPts p q) = 6 := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun x : Fin 8 => x ≠ p ∧ x ≠ q) = ({p, q} : Finset (Fin 8))ᶜ := by
    ext x
    simp
  rw [this, Finset.card_compl, Finset.card_pair hpq]
  simp

theorem otherPts_iff {g : Perm (Fin 8)} {p q : Fin 8}
    (h : (g p = p ∧ g q = q) ∨ (g p = q ∧ g q = p)) (x : Fin 8) :
    (x ≠ p ∧ x ≠ q) ↔ (g x ≠ p ∧ g x ≠ q) := by
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · refine ⟨fun ⟨h1, h2⟩ => ⟨fun h => h1 (g.injective (h.trans hp.symm)),
      fun h => h2 (g.injective (h.trans hq.symm))⟩, fun ⟨h1, h2⟩ => ⟨fun h => h1 ?_, fun h => h2 ?_⟩⟩
    · rw [h]; exact hp
    · rw [h]; exact hq
  · refine ⟨fun ⟨h1, h2⟩ => ⟨fun h => h2 (g.injective (h.trans hq.symm)),
      fun h => h1 (g.injective (h.trans hp.symm))⟩, fun ⟨h1, h2⟩ => ⟨fun h => h2 ?_, fun h => h1 ?_⟩⟩
    · rw [h]; exact hp
    · rw [h]; exact hq

def restrictOther {p q : Fin 8} (g : Perm (Fin 8))
    (h : (g p = p ∧ g q = q) ∨ (g p = q ∧ g q = p)) : Perm (OtherPts p q) :=
  g.subtypePerm fun x => (otherPts_iff h x).symm

theorem pair_preserved (K : Subgroup (alternatingGroup (Fin 8))) {p q : Fin 8} (hpq : p ≠ q)
    (hfixK : ∀ k ∈ K, (k : Perm (Fin 8)) p = p ∧ (k : Perm (Fin 8)) q = q)
    (hfixonly : ∀ ω : Fin 8, (∀ k ∈ K, (k : Perm (Fin 8)) ω = ω) → ω = p ∨ ω = q)
    (n : alternatingGroup (Fin 8)) (hn : ∀ k ∈ K, n⁻¹ * k * n ∈ K) :
    ((n : Perm (Fin 8)) p = p ∧ (n : Perm (Fin 8)) q = q) ∨
      ((n : Perm (Fin 8)) p = q ∧ (n : Perm (Fin 8)) q = p) := by
  have hmoves : ∀ x : Fin 8, (∀ k ∈ K, (k : Perm (Fin 8)) x = x) →
      ∀ k ∈ K, (k : Perm (Fin 8)) ((n : Perm (Fin 8)) x) = (n : Perm (Fin 8)) x := by
    intro x hx k hk
    have h2 : (n : Perm (Fin 8))⁻¹ ((k : Perm (Fin 8)) ((n : Perm (Fin 8)) x)) = x :=
      hx _ (hn k hk)
    have h3 := congrArg (n : Perm (Fin 8)) h2
    simpa using h3
  have h1 := hfixonly _ (hmoves p (fun k hk => (hfixK k hk).1))
  have h2 := hfixonly _ (hmoves q (fun k hk => (hfixK k hk).2))
  have hinj := (n : Perm (Fin 8)).injective
  rcases h1 with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact absurd (hinj (h2.trans h1.symm)).symm hpq
    · exact h2
  · right
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact h2
    · exact absurd (hinj (h2.trans h1.symm)) hpq.symm

theorem eq_one_of_fix_other {p q : Fin 8} (hpq : p ≠ q) (n : alternatingGroup (Fin 8))
    (hn : ((n : Perm (Fin 8)) p = p ∧ (n : Perm (Fin 8)) q = q) ∨
      ((n : Perm (Fin 8)) p = q ∧ (n : Perm (Fin 8)) q = p))
    (hx : ∀ x : Fin 8, x ≠ p → x ≠ q → (n : Perm (Fin 8)) x = x) : n = 1 := by
  rcases hn with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hxp : x = p
    · rw [hxp, hp]; rfl
    by_cases hxq : x = q
    · rw [hxq, hq]; rfl
    exact hx x hxp hxq
  · exfalso
    have hswap : (n : Perm (Fin 8)) = swap p q := by
      apply Equiv.ext
      intro x
      by_cases hxp : x = p
      · rw [hxp, hp, swap_apply_left]
      by_cases hxq : x = q
      · rw [hxq, hq, swap_apply_right]
      rw [hx x hxp hxq, swap_apply_of_ne_of_ne hxp hxq]
    have h1 := mem_alternatingGroup.1 n.2
    rw [hswap, sign_swap hpq] at h1
    exact absurd h1 (by decide)

theorem eq_one_of_comm_stab (K : Subgroup (alternatingGroup (Fin 8)))
    (eK : K ≃* alternatingGroup (Fin 6)) (n : alternatingGroup (Fin 8))
    (hn : ∀ k ∈ K, k * n = n * k) : n = 1 := by
  classical
  obtain ⟨p, q, hpq, hfixK, hfixonly⟩ := CFSG.CGT.T75I.exists_two_fixed K eK
  have hP := CFSG.CGT.T75I.mem_of_fix K eK hpq hfixK
  have hpres := pair_preserved K hpq hfixK hfixonly n (fun k hk => by
    rw [mul_assoc, hn k hk, inv_mul_cancel_left]; exact hk)
  have hcard : 4 ≤ Nat.card (OtherPts p q) := by
    rw [Nat.card_eq_fintype_card, card_otherPts hpq]; norm_num
  have hres : restrictOther (n : Perm (Fin 8)) hpres ∈
      Subgroup.centralizer (alternatingGroup (OtherPts p q) : Set (Perm (OtherPts p q))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hsign : sign (Equiv.Perm.ofSubtype t : Perm (Fin 8)) = 1 := by
      rw [sign_ofSubtype]; exact mem_alternatingGroup.1 ht
    let t' : alternatingGroup (Fin 8) := ⟨Equiv.Perm.ofSubtype t, mem_alternatingGroup.2 hsign⟩
    have ht'p : (t' : Perm (Fin 8)) p = p :=
      Equiv.Perm.ofSubtype_apply_of_not_mem t (by simp)
    have ht'q : (t' : Perm (Fin 8)) q = q :=
      Equiv.Perm.ofSubtype_apply_of_not_mem t (by simp)
    have htK : t' ∈ K := hP t' ht'p ht'q
    have hc := hn t' htK
    apply Equiv.ext
    intro y
    apply Subtype.ext
    have h1 := congrArg (fun m : alternatingGroup (Fin 8) => (m : Perm (Fin 8)) (y : Fin 8)) hc
    have hny : (n : Perm (Fin 8)) y ≠ p ∧ (n : Perm (Fin 8)) y ≠ q :=
      (otherPts_iff hpres y).1 y.2
    have e1 : ((t' * n : alternatingGroup (Fin 8)) : Perm (Fin 8)) y =
        ((t * restrictOther (n : Perm (Fin 8)) hpres) y : OtherPts p q) := by
      show (Equiv.Perm.ofSubtype t) ((n : Perm (Fin 8)) y) = _
      rw [Equiv.Perm.ofSubtype_apply_of_mem t hny]
      rfl
    have e2 : ((n * t' : alternatingGroup (Fin 8)) : Perm (Fin 8)) y =
        ((restrictOther (n : Perm (Fin 8)) hpres * t) y : OtherPts p q) := by
      show (n : Perm (Fin 8)) ((Equiv.Perm.ofSubtype t) y) = _
      rw [Equiv.Perm.ofSubtype_apply_of_mem t y.2]
      rfl
    exact e1.symm.trans (h1.trans e2)
  rw [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot hcard,
    Subgroup.mem_bot] at hres
  refine eq_one_of_fix_other hpq n hpres fun x hxp hxq => ?_
  exact congrArg (fun m : Perm (OtherPts p q) => (m ⟨x, hxp, hxq⟩ : Fin 8)) hres

theorem exists_alt8_normalizer_hom (K : Subgroup (alternatingGroup (Fin 8)))
    (eK : K ≃* alternatingGroup (Fin 6)) :
    ∃ σ : ↥(normalizer (K : Set (alternatingGroup (Fin 8)))) →* Perm (Fin 6),
      Function.Injective σ := by
  classical
  obtain ⟨p, q, hpq, hfixK, hfixonly⟩ := CFSG.CGT.T75I.exists_two_fixed K eK
  have hpres : ∀ n : ↥(normalizer (K : Set (alternatingGroup (Fin 8)))),
      (((n : alternatingGroup (Fin 8)) : Perm (Fin 8)) p = p ∧
        ((n : alternatingGroup (Fin 8)) : Perm (Fin 8)) q = q) ∨
      (((n : alternatingGroup (Fin 8)) : Perm (Fin 8)) p = q ∧
        ((n : alternatingGroup (Fin 8)) : Perm (Fin 8)) q = p) := fun n =>
    pair_preserved K hpq hfixK hfixonly n (fun k hk =>
      (mem_set_normalizer_iff''.1 n.2 k).1 hk)
  let σ₀ : ↥(normalizer (K : Set (alternatingGroup (Fin 8)))) →* Perm (OtherPts p q) :=
    { toFun := fun n => restrictOther ((n : alternatingGroup (Fin 8)) : Perm (Fin 8)) (hpres n)
      map_one' := by
        apply Equiv.ext
        intro y
        rfl
      map_mul' := fun n₁ n₂ => by
        apply Equiv.ext
        intro y
        rfl }
  have hσ₀ : Function.Injective σ₀ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    apply Subtype.ext
    refine eq_one_of_fix_other hpq _ (hpres n) fun x hxp hxq => ?_
    exact congrArg (fun m : Perm (OtherPts p q) => (m ⟨x, hxp, hxq⟩ : Fin 8)) hn
  let e : OtherPts p q ≃ Fin 6 := Fintype.equivFinOfCardEq (card_otherPts hpq)
  exact ⟨e.permCongrHom.toMonoidHom.comp σ₀, e.permCongrHom.injective.comp hσ₀⟩

section Transport

variable {W : Type*} [Group W]

theorem nonempty_mulAut_alt8 [Finite W] (hc : ∀ x y : W, x * y = y * x)
    (hs : ∀ x : W, x * x = 1) (hW : Nat.card W = 16) :
    Nonempty (MulAut W ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (n := 4) hc
    (fun a => by rw [pow_two]; exact hs a) (by rw [hW]; norm_num)
  exact ⟨(CFSG.SectionRank.Ccomm.elemAutEquivGL e).trans
    CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm⟩

theorem eq_one_of_comm_alt6 [Finite W] (hc : ∀ x y : W, x * y = y * x)
    (hs : ∀ x : W, x * x = 1) (hW : Nat.card W = 16) (A : Subgroup (MulAut W))
    (eA : A ≃* alternatingGroup (Fin 6)) (g : MulAut W) (hg : ∀ x ∈ A, g * x = x * g) :
    g = 1 := by
  obtain ⟨Φ⟩ := nonempty_mulAut_alt8 hc hs hW
  let K : Subgroup (alternatingGroup (Fin 8)) := A.map Φ.toMonoidHom
  let eK : K ≃* alternatingGroup (Fin 6) :=
    (A.equivMapOfInjective Φ.toMonoidHom Φ.injective).symm.trans eA
  have h1 : Φ g = 1 := by
    refine eq_one_of_comm_stab K eK (Φ g) fun k hk => ?_
    obtain ⟨x, hx, rfl⟩ := hk
    show Φ x * Φ g = Φ g * Φ x
    rw [← map_mul, ← map_mul, ← hg x hx]
  exact Φ.map_eq_one_iff.1 h1

theorem exists_normalizer_hom [Finite W] (hc : ∀ x y : W, x * y = y * x)
    (hs : ∀ x : W, x * x = 1) (hW : Nat.card W = 16) (A : Subgroup (MulAut W))
    (eA : A ≃* alternatingGroup (Fin 6)) :
    ∃ σ : ↥(normalizer (A : Set (MulAut W))) →* Equiv.Perm (Fin 6), Function.Injective σ := by
  obtain ⟨Φ⟩ := nonempty_mulAut_alt8 hc hs hW
  let K : Subgroup (alternatingGroup (Fin 8)) := A.map Φ.toMonoidHom
  let eK : K ≃* alternatingGroup (Fin 6) :=
    (A.equivMapOfInjective Φ.toMonoidHom Φ.injective).symm.trans eA
  obtain ⟨σ, hσ⟩ := exists_alt8_normalizer_hom K eK
  have hmem : ∀ x : ↥(normalizer (A : Set (MulAut W))),
      Φ (x : MulAut W) ∈ normalizer (K : Set (alternatingGroup (Fin 8))) := by
    intro x
    rw [mem_set_normalizer_iff'']
    intro h
    have hx := mem_set_normalizer_iff''.1 x.2 (Φ.symm h)
    have e1 : (Φ (x : MulAut W))⁻¹ * h * Φ (x : MulAut W) = Φ ((x : MulAut W)⁻¹ * Φ.symm h * x) := by
      simp
    show h ∈ K ↔ (Φ (x : MulAut W))⁻¹ * h * Φ (x : MulAut W) ∈ K
    rw [e1]
    have e2 : ∀ y : alternatingGroup (Fin 8), y ∈ K ↔ Φ.symm y ∈ A := fun y =>
      Subgroup.mem_map_equiv
    rw [e2, e2, MulEquiv.symm_apply_apply]
    exact hx
  let ψ : ↥(normalizer (A : Set (MulAut W))) →*
      ↥(normalizer (K : Set (alternatingGroup (Fin 8)))) :=
    { toFun := fun x => ⟨Φ (x : MulAut W), hmem x⟩
      map_one' := Subtype.ext (map_one Φ)
      map_mul' := fun x y => Subtype.ext (map_mul Φ (x : MulAut W) (y : MulAut W)) }
  have hψ : Function.Injective ψ := fun x y h =>
    Subtype.ext (Φ.injective (congrArg Subtype.val h))
  exact ⟨σ.comp ψ, hσ.comp hψ⟩

end Transport

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
