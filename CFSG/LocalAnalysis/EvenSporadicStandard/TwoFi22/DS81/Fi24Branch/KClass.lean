module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.KConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.KClassModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.OfModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueCard
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi22

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup CFSG.Sporadic.Fi23 CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus (fixP fixP_conj)
open CFSG.Sporadic.FischerOddCore (fi22ExtRep)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Aut

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}


theorem exists_conj_piR (hH : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (e e' : (L ⧸ center L) ≃* fi22P) :
    ∃ r : fi22R, ∀ g, piR hH e g = r * piR hH e' g * r⁻¹ := by
  obtain ⟨r, hr⟩ := fi22RAut.surjective (e'.symm.trans e)
  refine ⟨r, fun g => fi22RAut.injective ?_⟩
  rw [map_mul, map_mul, map_inv, fi22RAut_piR, fi22RAut_piR, hr]
  refine MulEquiv.ext fun p => ?_
  simp only [MulAut.congr_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.trans_apply,
    MulEquiv.symm_trans_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

end Aut

private theorem mulEquiv_mem_center_iff {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) (x : A) :
    ψ x ∈ center B ↔ x ∈ center A := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro hx g
    apply ψ.injective
    rw [map_mul, map_mul]
    exact hx (ψ g)
  · intro hx g
    obtain ⟨g', rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul, hx g']

section Model

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G}


theorem Std.exists_modelIso (h : Std G L E t) :
    ∃ (ψ : ↥L ≃* Cd) (τ : ↥L), (τ : G) = t ∧ ψ τ = dCd ∧
      ∀ x : ↥L, ψ x ∈ E0 ↔ (x : G) ∈ E := by
  have htz : t ∈ (center L).map L.subtype := by
    rw [h.center_eq]
    exact mem_zpowers t
  obtain ⟨τ, hτ, hτt⟩ := htz
  have hτt' : (τ : G) = t := hτt
  have hτ1 : τ ≠ 1 := fun h1 => h.m24.t_ne_one (by rw [← hτt', h1]; rfl)
  obtain ⟨ψ₀, hψ₀⟩ := CFSG.EvenSporadicStandard.TwoFi22.exists_iso_Cd h.std.standard.1
    h.card_center h.quo hτ hτ1
  set B : Subgroup G := (E0.map (ψ₀.symm : ↥Cd →* ↥L)).map L.subtype with hB
  have hBL : B ≤ L := Subgroup.map_subtype_le _
  have hBsq : ∀ b ∈ B, b ^ 2 = 1 := by
    rintro _ ⟨x, ⟨e, he, rfl⟩, rfl⟩
    have h2 : (ψ₀.symm e) ^ 2 = 1 := by
      rw [← map_pow, E0_sq e he, map_one]
    have := congrArg (fun u : ↥L => (u : G)) h2
    simpa using this
  have hBc : Nat.card B = 2 ^ 11 := by
    rw [hB, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective (f := (ψ₀.symm : ↥Cd →* ↥L)) ψ₀.symm.injective]
    exact E0_card
  obtain ⟨l, hlL, hBl⟩ := h.facts.conj_class B hBL hBsq hBc
  have hmem : ∀ x : ↥L, ψ₀ x ∈ E0 ↔ (l : G) * (x : G) * (l : G)⁻¹ ∈ E := by
    intro x
    rw [← CFSG.Quasithin.mem_conjSubgroup_iff, ← hBl]
    have h1 : (x : G) ∈ B ↔ x ∈ E0.map (ψ₀.symm : ↥Cd →* ↥L) := mem_map_subtype_iff x
    rw [h1]
    constructor
    · intro hx
      exact ⟨ψ₀ x, hx, ψ₀.symm_apply_apply x⟩
    · rintro ⟨e, he, rfl⟩
      simpa using he
  set l' : ↥L := ⟨l, hlL⟩ with hl'
  refine ⟨(MulAut.conj l'⁻¹).trans ψ₀, τ, hτt', ?_, ?_⟩
  · have hc : l'⁻¹ * τ * l'⁻¹⁻¹ = τ := by
      have := Subgroup.mem_center_iff.1 hτ l'⁻¹
      rw [inv_inv, this, mul_assoc, inv_mul_cancel, mul_one]
    show ψ₀ (l'⁻¹ * τ * l'⁻¹⁻¹) = dCd
    rw [hc]
    exact Subtype.ext hψ₀
  · intro x
    show ψ₀ (l'⁻¹ * x * l'⁻¹⁻¹) ∈ E0 ↔ (x : G) ∈ E
    rw [hmem]
    have : (l : G) * ((l'⁻¹ * x * l'⁻¹⁻¹ : ↥L) : G) * (l : G)⁻¹ = (x : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      show (l : G) * ((l : G)⁻¹ * (x : G) * (l : G)) * (l : G)⁻¹ = x
      group
    rw [this]

end Model

section Quotient

variable {G : Type} [Group G] {L : Subgroup G}


theorem exists_e0 (ψ : ↥L ≃* Cd) :
    ∃ e0 : (L ⧸ center L) ≃* fi22P, ∀ x : ↥L, e0 (x : L ⧸ center L) = piP (ψ x) := by
  let f : ↥L →* fi22P := piP.comp (ψ : ↥L →* ↥Cd)
  have hf : Function.Surjective f := piP_surjective.comp ψ.surjective
  have hker : f.ker = center ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    show piP (ψ x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, ker_piP, mulEquiv_mem_center_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf), fun x => rfl⟩

end Quotient

section Stable

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G}

theorem Std.normClass_sub (h : Std G L E t) : normClass E t ⊆ E := by
  rintro _ ⟨n, hn, rfl⟩
  exact (mem_normalizer_iff.1 hn t).1 h.t_mem_E


theorem Std.mem_normalizer_of_iso (h : Std G L E t) {ψ : ↥L ≃* Cd}
    (hψE : ∀ x : ↥L, ψ x ∈ E0 ↔ (x : G) ∈ E) {n : Cd} (hn : n ∈ normalizer (E0 : Set Cd)) :
    ((ψ.symm n : ↥L) : G) ∈ normalizer (E : Set G) := by
  have h1 : ψ.symm n ∈ normalizer ((E.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [mem_normalizer_iff]
    intro y
    have e1 : y ∈ E.subgroupOf L ↔ ψ y ∈ E0 := Subgroup.mem_subgroupOf.trans (hψE y).symm
    have e2 : ψ.symm n * y * (ψ.symm n)⁻¹ ∈ E.subgroupOf L ↔
        ψ (ψ.symm n * y * (ψ.symm n)⁻¹) ∈ E0 :=
      Subgroup.mem_subgroupOf.trans (hψE _).symm
    rw [e1, e2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact mem_normalizer_iff.1 hn (ψ y)
  have h2 := (mem_normalizer_map_subtype_iff (E' := E.subgroupOf L) (ψ.symm n)).2 h1
  rwa [Subgroup.map_subgroupOf_eq_of_le h.E_le] at h2

end Stable

section Main

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G}


theorem Std.fixP_piR_z_aux (h : Std G L E t) {z : G} (hz : IsZ E t z) :
    ∃ e0 : (L ⧸ center L) ≃* fi22P,
      fixP ((piR h.H_le_normalizer e0 ⟨z, h.E_le_H hz.1⟩ : fi22R) : Equiv.Perm (Fin 3510)) =
        182 := by
  obtain ⟨ψ, τ, hτt, hψτ, hψE⟩ := h.exists_modelIso
  obtain ⟨e0, he0⟩ := exists_e0 ψ
  refine ⟨e0, ?_⟩
  have hzL : z ∈ L := h.E_le hz.1
  set zL : ↥L := ⟨z, hzL⟩ with hzLdef
  set T : Set Cd := ψ '' {x : ↥L | (x : G) ∈ normClass E t} with hT
  have hTE : ∀ y ∈ T, y ∈ E0 ∧ y ≠ 1 := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(hψE x).2 (h.normClass_sub hx), fun h1 => ?_⟩
    have hx1 : x = 1 := ψ.injective (by rw [h1, map_one])
    obtain ⟨m, -, hmx⟩ := hx
    apply h.m24.t_ne_one
    have hx1' : m * t * m⁻¹ = 1 := by rw [hmx, hx1]; rfl
    calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
      _ = 1 := by rw [hx1']; group
  have hTN : ∀ n ∈ normalizer (E0 : Set Cd), ∀ y ∈ T, n * y * n⁻¹ ∈ T := by
    rintro n hn _ ⟨x, ⟨m, hm, hmx⟩, rfl⟩
    have hu := h.mem_normalizer_of_iso hψE hn
    refine ⟨ψ.symm n * x * (ψ.symm n)⁻¹, ⟨((ψ.symm n : ↥L) : G) * m, mul_mem hu hm, ?_⟩, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hmx]
      group
    · rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hd : dCd ∈ T :=
    ⟨τ, ⟨1, one_mem _, by rw [hτt]; group⟩, hψτ⟩
  have hcard : T.ncard = 276 := by
    have hsub : normClass E t ⊆ Set.range ((↑) : ↥L → G) := fun g hg =>
      ⟨⟨g, h.E_le (h.normClass_sub hg)⟩, rfl⟩
    rw [hT, Set.ncard_image_of_injective _ ψ.injective]
    exact (Set.ncard_preimage_of_injective_subset_range (f := ((↑) : ↥L → G))
      Subtype.val_injective hsub).trans h.m24.ncard_t
  have hyE : ψ zL ∈ E0 := (hψE zL).2 hz.1
  have hy1 : ψ zL ≠ 1 := fun h1 => hz.2.1 (by
    have : zL = 1 := ψ.injective (by rw [h1, map_one])
    exact congrArg (fun u : ↥L => (u : G)) this)
  have hyT : ψ zL ∉ T := by
    rintro ⟨x, hx, hxy⟩
    have : x = zL := ψ.injective hxy
    rw [this] at hx
    exact hz.2.2.1 hx
  have hdy : dCd * ψ zL ∈ T := by
    refine ⟨τ * zL, ?_, by rw [map_mul, hψτ]⟩
    show (((τ * zL : ↥L)) : G) ∈ normClass E t
    rw [Subgroup.coe_mul, hτt]
    exact hz.2.2.2
  have h1 := fixP_piP_of_stable hTE hTN hd hcard hyE hy1 hyT hdy
  have h2 : ((piR h.H_le_normalizer e0 ⟨z, h.E_le_H hz.1⟩ : fi22R) : Equiv.Perm (Fin 3510)) =
      ((e0 (zL : L ⧸ center L) : fi22P) : Equiv.Perm (Fin 3510)) :=
    piR_apply_of_mem_L h.H_le_normalizer e0 zL (h.E_le_H hz.1)
  rw [h2, he0]
  exact h1

theorem Std.fixP_piR_z (h : Std G L E t) {z : G} (hz : IsZ E t z)
    (e : (L ⧸ center L) ≃* fi22P) :
    fixP ((piR h.H_le_normalizer e ⟨z, h.E_le_H hz.1⟩ : fi22R) : Equiv.Perm (Fin 3510)) = 182 := by
  obtain ⟨e0, he0⟩ := h.fixP_piR_z_aux hz
  obtain ⟨r, hr⟩ := exists_conj_piR h.H_le_normalizer e e0
  rw [hr]
  have h1 : (((r * piR h.H_le_normalizer e0 ⟨z, h.E_le_H hz.1⟩ * r⁻¹ : fi22R)) :
      Equiv.Perm (Fin 3510)) = (r : Equiv.Perm (Fin 3510)) *
        (piR h.H_le_normalizer e0 ⟨z, h.E_le_H hz.1⟩ : fi22R) * (r : Equiv.Perm (Fin 3510))⁻¹ :=
    rfl
  rw [h1, fixP_conj]
  exact he0

end Main

section Final

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G}


theorem Std.exists_conj_fi22ExtRep (h : Std G L E t) {z : G} (hz : IsZ E t z)
    (e : (L ⧸ center L) ≃* fi22P) :
    ∃ w ∈ fi22R, w * ((piR h.H_le_normalizer e ⟨z, h.E_le_H hz.1⟩ : fi22R) :
      Equiv.Perm (Fin 3510)) * w⁻¹ = fi22ExtRep 1 := by
  set g : fi22R := piR h.H_le_normalizer e ⟨z, h.E_le_H hz.1⟩ with hg
  have hfix' : fixP (g : Equiv.Perm (Fin 3510)) = 182 := h.fixP_piR_z hz e
  have hfix : fixP (g : Equiv.Perm (Fin 3510)) = fixP (fi22ExtRep 1) := by
    rw [hfix', CFSG.ComponentClassification.RankTwoSporadic.Fi22.fixP_fi22ExtRep 1 (by norm_num)]
    rfl
  have hg2 : (g : Equiv.Perm (Fin 3510)) ^ 2 = 1 := by
    have h1 : (⟨z, h.E_le_H hz.1⟩ : centralizer ({t} : Set G)) ^ 2 = 1 :=
      Subtype.ext (h.m24.E_sq z hz.1)
    have h2 : g ^ 2 = 1 := by rw [hg, ← map_pow, h1, map_one]
    exact congrArg (fun u : fi22R => (u : Equiv.Perm (Fin 3510))) h2
  have hg1 : (g : Equiv.Perm (Fin 3510)) ≠ 1 := by
    intro h1
    rw [h1] at hfix'
    have h3 : fixP (1 : Equiv.Perm (Fin 3510)) = 3510 := by simp [fixP]
    omega
  exact CFSG.ComponentClassification.RankTwoSporadic.Fi22.fi22_conj_of_fix _ g.2 hg2 hg1
    (k := 1) (by norm_num) hfix

theorem Std.exists_piR_z (h : Std G L E t) {z : G} (hz : IsZ E t z) :
    ∃ π : centralizer ({t} : Set G) →* fi22R, Function.Surjective π ∧
      π.ker = (zpowers t).subgroupOf (centralizer ({t} : Set G)) ∧
      ((π ⟨z, h.E_le_H hz.1⟩ : fi22R) : Equiv.Perm (Fin 3510)) = fi22ExtRep 1 := by
  obtain ⟨e0⟩ := h.quo
  set e : (L ⧸ center L) ≃* fi22P := e0.trans fi22PermEquiv with he
  obtain ⟨w, hw, hwz⟩ := h.exists_conj_fi22ExtRep hz e
  set c : fi22R ≃* fi22R := MulAut.conj (⟨w, hw⟩ : fi22R) with hc
  refine ⟨(c : fi22R →* fi22R).comp (piR h.H_le_normalizer e),
    c.surjective.comp (h.piR_surjective e), ?_, ?_⟩
  · rw [← h.ker_piR e]
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact MulEquiv.map_eq_one_iff c
  · show ((c (piR h.H_le_normalizer e ⟨z, h.E_le_H hz.1⟩) : fi22R) : Equiv.Perm (Fin 3510)) =
      fi22ExtRep 1
    rw [hc, MulAut.conj_apply]
    exact hwz

end Final

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
