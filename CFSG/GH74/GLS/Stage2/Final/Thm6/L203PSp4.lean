module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203Main
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Outer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly

public section

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Local.P27
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L203

section Transport

variable {G P : Type} [Group G] [Group P]

theorem exists_image (E : Subgroup G) (e : ↥E ≃* P) {t : G} (htE : t ∈ E) {u : P}
    (hu : e ⟨t, htE⟩ = u) (L : Subgroup P) (hLD : L ≤ centralizer ({u} : Set P)) :
    ∃ I : Subgroup G, I ≤ E ⊓ centralizer ({t} : Set G) ∧ Nonempty (↥I ≃* ↥L) ∧
      ∀ n : G, n ∈ I ↔ ∃ h : n ∈ E, e ⟨n, h⟩ ∈ L := by
  refine ⟨(L.map e.symm.toMonoidHom).map E.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, ⟨l, hl, rfl⟩, rfl⟩
    refine Subgroup.mem_inf.2 ⟨(e.symm l).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hl' : (l : P) * u = u * l := Subgroup.mem_centralizer_singleton_iff.1 (hLD hl)
    have : e.symm l * ⟨t, htE⟩ = ⟨t, htE⟩ * e.symm l := by
      apply e.injective
      rw [map_mul, map_mul, hu]
      simpa using hl'
    exact congrArg Subtype.val this
  · exact ⟨((Subgroup.equivMapOfInjective L e.symm.toMonoidHom e.symm.injective).trans
      (Subgroup.equivMapOfInjective (L.map e.symm.toMonoidHom) E.subtype E.subtype_injective)).symm⟩
  · intro n
    constructor
    · rintro ⟨x, ⟨l, hl, rfl⟩, rfl⟩
      refine ⟨(e.symm l).2, ?_⟩
      simpa using hl
    · rintro ⟨h, hmem⟩
      exact ⟨⟨n, h⟩, ⟨e ⟨n, h⟩, hmem, by simp⟩, rfl⟩

theorem exists_container (E : Subgroup G) (e : ↥E ≃* P) {t : G} (htE : t ∈ E) {u : P}
    (hu : e ⟨t, htE⟩ = u) (L : Subgroup P) (hLD : L ≤ centralizer ({u} : Set P))
    (hL : ∀ N : Subgroup P, N ≤ centralizer ({u} : Set P) → ⁅N, N⁆ = N → N ≤ L) :
    ∃ I : Subgroup G, I ≤ E ⊓ centralizer ({t} : Set G) ∧ Nonempty (↥I ≃* ↥L) ∧
      ∀ N : Subgroup G, N ≤ E ⊓ centralizer ({t} : Set G) → ⁅N, N⁆ = N → N ≤ I := by
  obtain ⟨I, hIle, hIL, hmem⟩ := exists_image E e htE hu L hLD
  refine ⟨I, hIle, hIL, ?_⟩
  intro N hN hperf
  have hNE : N ≤ E := fun n hn => (Subgroup.mem_inf.1 (hN hn)).1
  obtain ⟨NE, hNE'⟩ : ∃ NE : Subgroup ↥E, NE = N.subgroupOf E := ⟨_, rfl⟩
  have hmapNE : NE.map E.subtype = N := by rw [hNE']; exact Subgroup.map_subgroupOf_eq_of_le hNE
  have hNEperf : ⁅NE, NE⁆ = NE := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_commutator, hmapNE, hperf]
  obtain ⟨NP, hNP⟩ : ∃ NP : Subgroup P, NP = NE.map e.toMonoidHom := ⟨_, rfl⟩
  have hNPD : NP ≤ centralizer ({u} : Set P) := by
    rw [hNP]
    rintro _ ⟨x, hx, rfl⟩
    have hxN : (x : G) ∈ N := by rw [← hmapNE]; exact ⟨x, hx, rfl⟩
    have hxC : (x : G) * t = t * (x : G) := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hN hxN)).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : x * ⟨t, htE⟩ = ⟨t, htE⟩ * x := Subtype.ext hxC
    have h2 := congrArg e this
    rw [map_mul, map_mul, hu] at h2
    exact h2
  have hNPperf : ⁅NP, NP⁆ = NP := by
    rw [hNP, ← Subgroup.map_commutator, hNEperf]
  have hNPL := hL NP hNPD hNPperf
  intro n hn
  have hnN : n ∈ E := hNE hn
  rw [hmem]
  refine ⟨hnN, hNPL ?_⟩
  rw [hNP]
  refine ⟨⟨n, hnN⟩, ?_, rfl⟩
  rw [hNE']
  exact hn

end Transport

section Main

open CFSG.ComponentClassification.CatFactsSp4

theorem psp4Facts : PSp4Facts := by
  intro G _ _ E q hq hq5 hE
  obtain ⟨F, hF, hfin, hqF, ⟨e⟩⟩ := hE
  have hFodd : Odd (Nat.card F) := hqF ▸ hq
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hFodd
  have h4 : 4 ≤ Nat.card F := by omega
  refine ⟨?_, ?_⟩
  ·
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff _).mp (show IsPrimePow (Nat.card F) by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.isPrimePow_card F)
    have hadm : StatedLieAdmissible .PSp 2 p k := by
      refine ⟨hp, hk, le_rfl, ?_⟩
      intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
    exact CFSG.ComponentClassification.CatalogueSchreierAssembly.classical_model_outer_solvable (S := ↥E) (t := .PSp) (n := 2) (p := p) (f := k)
      ⟨hadm, F, hF, hfin, hpk.symm, ⟨e⟩⟩
  · intro t htE ht2
    have hu : orderOf (e ⟨t, htE⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact ht2
    obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hFodd hu
    let e' : ↥E ≃* StatedProj (StatedSp 2 F) := e.trans (MulAut.conj g⁻¹)
    have he' : e' ⟨t, htE⟩ = g⁻¹ * e ⟨t, htE⟩ * g := by
      simp [e']
    rcases hg with hg1 | hg2
    · left
      have hu1 : e' ⟨t, htE⟩ = u1 F := by rw [he']; exact hg1
      obtain ⟨H, hHle, ⟨fH⟩, -⟩ := exists_image E e' htE hu1 (E1 F)
        ((E1_le_X0 h2).trans X0_le_centralizer)
      have hperf : Group.IsPerfect ↥H := isPerfect_of_equiv fH.symm (isQuasisimple_E1 h2 h4).1
      have hpH : pPrimeCore 2 ↥H = ⊥ := by
        apply Subgroup.map_injective (f := fH.toMonoidHom) fH.injective
        rw [Subgroup.map_bot]
        exact (CFSG.pPrimeCore_map_iso 2 fH).trans (pPrimeCore_E1 h2 h4)
      have hchar : ringChar F ≠ 2 := by
        intro h
        apply h2
        have := ringChar.Nat.cast_ringChar (R := F)
        rw [h] at this
        simpa using this
      obtain ⟨hex, hQ⟩ := LocalAnalysis.ComponentInitial.QuaternionMatrices.odd_field_two_dimensional_quaternion_matrices
        (K := F) hchar
      obtain ⟨a, b, hab⟩ := hex
      obtain ⟨-, -, -, -, -, Q, -, -, ⟨fQ⟩, -⟩ := hQ a b hab
      let Q8E : Subgroup ↥(E1 F) := Q.map (E1Equiv h2).toMonoidHom
      let Q8H : Subgroup ↥H := Q8E.map fH.symm.toMonoidHom
      refine ⟨H, Q8H.map H.subtype, hHle, hperf, hpH, Subgroup.map_subtype_le _, ?_⟩
      exact ⟨((Subgroup.equivMapOfInjective Q (E1Equiv h2).toMonoidHom (E1Equiv h2).injective).trans
        ((Subgroup.equivMapOfInjective Q8E fH.symm.toMonoidHom fH.symm.injective).trans
          (Subgroup.equivMapOfInjective Q8H H.subtype H.subtype_injective))).symm.trans fQ⟩
    · right
      have hu2 : e' ⟨t, htE⟩ = u2 F := by rw [he']; exact hg2
      obtain ⟨I, hIle, ⟨fI⟩, hcont⟩ := exists_container E e' htE hu2 (Lsub F) Lsub_le_centralizer
        (fun N hN hperf => perfect_le_L h2 hN hperf)
      exact ⟨I, hIle, ⟨F, hF, hfin, hqF, ⟨fI.trans (LtoStated F)⟩⟩, hcont⟩

end Main

theorem lemma20_3_of_prop27
    (h34 : Leaf_Prop34) (h27 : L203Prop27) : Lemma20_3 :=
  lemma20_3_of_parts h34 h27 psp4Facts

end CFSG.GH74.GLS.Stage2.Final.Thm6.L203
