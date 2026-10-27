module

public import CFSG.Yardstones.Md42047359a2a.Definitions

public section

namespace CFSG.HardMathSupport.Dickson.ElementCaseBp

open CFSG.HardMathSupport.Solomon.Coordinator

private theorem exists_conj_aut {Q A : Type} [Group Q] [Group A] [Finite Q] (ι : Q →* A)
    (hι : Function.Injective ι) (b : A) (hb : ∀ q : Q, b * ι q * b⁻¹ ∈ ι.range) :
    ∃ β : MulAut Q, ∀ q, ι (β q) = b * ι q * b⁻¹ := by
  have hb' : ∀ q : Q, ∃ y : Q, ι y = b * ι q * b⁻¹ := hb
  choose f hf using hb'
  have hmul : ∀ x y : Q, f (x * y) = f x * f y := fun x y => hι (by
    rw [hf, map_mul, map_mul, hf, hf]
    group)
  have hinj : Function.Injective f := fun x y h => hι (by
    have h' := congrArg ι h
    rw [hf, hf] at h'
    simpa using h')
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' f hmul)
    ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩, fun q => hf q⟩

private theorem conj_aut_pow {Q A : Type} [Group Q] [Group A] (ι : Q →* A) (b : A)
    (β : MulAut Q) (hβ : ∀ q, ι (β q) = b * ι q * b⁻¹) (n : ℕ) (q : Q) :
    ι ((β ^ n) q) = b ^ n * ι q * (b ^ n)⁻¹ := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' β n, MulAut.mul_apply, hβ, ih, pow_succ' b n]
    group

private theorem pLayer_map_mulEquiv {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]
    (p : ℕ) (hp : p.Prime) (ψ : H ≃* K) :
    (CFSG.pLayer H p).map ψ.toMonoidHom = CFSG.pLayer K p := by
  have hT := CFSG.LocalAnalysis.ComponentInitial.p_component_isomorphism_transport p hp ψ
  have hT' := CFSG.LocalAnalysis.ComponentInitial.p_component_isomorphism_transport p hp ψ.symm
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ((hT.1 L).1 hL)
  · refine sSup_le fun L hL => ?_
    have h1 : (L.map ψ.symm.toMonoidHom).map ψ.toMonoidHom = L := by
      rw [Subgroup.map_map]
      convert L.map_id
      ext x
      simp
    rw [← h1]
    exact Subgroup.map_mono (le_sSup ((hT'.1 L).1 hL))

private theorem map_layer_core_eq {Q A : Type} [Group Q] [Group A] [Finite Q] (ι : Q →* A)
    (hι : Function.Injective ι) (F : Subgroup Q) (D : Subgroup A) (hFD : F.map ι = D) {p : ℕ}
    (hp : p.Prime) :
    ((CFSG.pLayer ↥F p).map F.subtype).map ι = (CFSG.pLayer ↥D p).map D.subtype ∧
      ((CFSG.pPrimeCore p ↥F).map F.subtype).map ι = (CFSG.pPrimeCore p ↥D).map D.subtype := by
  set ψ : ↥F ≃* ↥D := (F.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hFD)
  have hcomp : ι.comp F.subtype = D.subtype.comp ψ.toMonoidHom := by
    ext x
    rfl
  haveI : Finite ↥D := Finite.of_equiv _ ψ.toEquiv
  constructor
  · rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, pLayer_map_mulEquiv p hp ψ]
  · rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, CFSG.pPrimeCore_map_iso p ψ]

theorem commutator_pLayer_pPrimeCore_eq_bot_of_simpleBp {Q A : Type} [Group Q] [Group A]
    [Finite Q] {p : ℕ} (hp : p.Prime) (hB : CFSG.Yardstones.Md42047359a2a.SimpleBp p Q)
    (ι : Q →* A) (hι : Function.Injective ι) (b : A)
    (hb : ∀ q : Q, b * ι q * b⁻¹ ∈ ι.range) (hbp : b ^ p = 1) :
    ⁅(CFSG.pLayer ↥(ι.range ⊓ Subgroup.centralizer ({b} : Set A)) p).map
        (ι.range ⊓ Subgroup.centralizer ({b} : Set A)).subtype,
      (CFSG.pPrimeCore p ↥(ι.range ⊓ Subgroup.centralizer ({b} : Set A))).map
        (ι.range ⊓ Subgroup.centralizer ({b} : Set A)).subtype⁆ = ⊥ := by
  obtain ⟨β, hβ⟩ := exists_conj_aut ι hι b hb
  have hβp : β ^ p = 1 := by
    refine MulEquiv.ext fun q => hι ?_
    rw [conj_aut_pow ι b β hβ p q, hbp]
    simp
  have hmem : ∀ q : Q, q ∈ fixSubgroup β ↔ ι q ∈ Subgroup.centralizer ({b} : Set A) := by
    intro q
    rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, ← hι.eq_iff, hβ,
      mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have hFD : (fixSubgroup β).map ι = ι.range ⊓ Subgroup.centralizer ({b} : Set A) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, rfl⟩, (hmem q).1 hq⟩
    · rintro ⟨⟨q, rfl⟩, hx⟩
      exact ⟨q, (hmem q).2 hx, rfl⟩
  have hcomm : ⁅(CFSG.pLayer ↥(fixSubgroup β) p).map (fixSubgroup β).subtype,
      (CFSG.pPrimeCore p ↥(fixSubgroup β)).map (fixSubgroup β).subtype⁆ = ⊥ := by
    have h := hB β hβp
    rw [i183_glaPLayer_eq_map hp] at h
    exact h
  have hmap := congrArg (Subgroup.map ι) hcomm
  rw [Subgroup.map_commutator, Subgroup.map_bot] at hmap
  obtain ⟨h1, h2⟩ := map_layer_core_eq ι hι (fixSubgroup β) _ hFD hp
  rw [h1, h2] at hmap
  exact hmap

end CFSG.HardMathSupport.Dickson.ElementCaseBp
