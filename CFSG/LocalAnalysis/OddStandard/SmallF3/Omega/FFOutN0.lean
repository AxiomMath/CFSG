module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutSimTab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffSimInGStar_mul {x y : ProjSim Q} (hx : SimInGStar x) (hy : SimInGStar y) :
    SimInGStar (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a * b, by rw [map_mul, ha, hb]⟩

theorem ffSimInGStar_inv {x : ProjSim Q} (hx : SimInGStar x) : SimInGStar x⁻¹ := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨a⁻¹, by rw [map_inv, ha]⟩

private lemma ffOutN0_map_inv_map {H : Type} [Group H] (c : MulAut H) (U : Subgroup H) :
    (U.map c.toMonoidHom).map c⁻¹.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have h : (c⁻¹).toMonoidHom.comp c.toMonoidHom = MonoidHom.id H := by
    ext x
    exact MulEquiv.symm_apply_apply c x
  rw [h, Subgroup.map_id]

private lemma ffOutN0_map_mul {H : Type} [Group H] (c d : MulAut H) (U : Subgroup H) :
    U.map (c * d).toMonoidHom = (U.map d.toMonoidHom).map c.toMonoidHom := by
  rw [show (c * d).toMonoidHom = c.toMonoidHom.comp d.toMonoidHom from rfl, ← Subgroup.map_map]

private lemma ffOutN0_isElemAb2_map_mulEquiv {H : Type} [Group H] (f : H ≃* H) {U : Subgroup H}
    {k : ℕ} (h : IsElemAb2 U k) : IsElemAb2 (U.map f.toMonoidHom) k := by
  haveI : IsMulCommutative U := h.1.1
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, h.1.2 u hu, map_one]
  · rw [Nat.card_congr (U.equivMapOfInjective f.toMonoidHom f.injective).toEquiv.symm, h.2]

theorem ffSimInGStar_inv_mul_of_not {u v : ProjSim Q} (hu : ¬ SimInGStar u) (hv : ¬ SimInGStar v) :
    SimInGStar (u⁻¹ * v) := by
  obtain ⟨γu, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨γv, rfl⟩ := QuotientGroup.mk_surjective v
  have hcu : Classical.choose γu.2 = -1 := by
    rcases aux_unit_eq_one_or_neg_one (Classical.choose γu.2) with h | h
    · exfalso
      have hmem : (γu : V ≃ₗ[ZMod 3] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
        isSimilitude_one_iff.mp (h ▸ Classical.choose_spec γu.2)
      refine hu ⟨toProj Q ⟨(γu : V ≃ₗ[ZMod 3] V), hmem⟩, ?_⟩
      rw [projOrthToProjSim_toProj]
      exact congrArg QuotientGroup.mk (Subtype.ext rfl)
    · exact h
  have hcv : Classical.choose γv.2 = -1 := by
    rcases aux_unit_eq_one_or_neg_one (Classical.choose γv.2) with h | h
    · exfalso
      have hmem : (γv : V ≃ₗ[ZMod 3] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
        isSimilitude_one_iff.mp (h ▸ Classical.choose_spec γv.2)
      refine hv ⟨toProj Q ⟨(γv : V ≃ₗ[ZMod 3] V), hmem⟩, ?_⟩
      rw [projOrthToProjSim_toProj]
      exact congrArg QuotientGroup.mk (Subtype.ext rfl)
    · exact h
  have hmult : IsSimilitude Q (((γu⁻¹ * γv : simGroup Q) : V ≃ₗ[ZMod 3] V)) 1 := by
    have h := aux_isSimilitude_mul (aux_isSimilitude_inv (Classical.choose_spec γu.2))
      (Classical.choose_spec γv.2)
    rw [hcu, hcv] at h
    have hunit : (-1 : (ZMod 3)ˣ)⁻¹ * (-1) = 1 := by decide
    rw [hunit] at h
    simpa using h
  have hmem : ((γu⁻¹ * γv : simGroup Q) : V ≃ₗ[ZMod 3] V) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := isSimilitude_one_iff.mp hmult
  refine ⟨toProj Q ⟨((γu⁻¹ * γv : simGroup Q) : V ≃ₗ[ZMod 3] V), hmem⟩, ?_⟩
  rw [projOrthToProjSim_toProj]
  exact (congrArg QuotientGroup.mk (Subtype.ext (by simp))).trans
    ((QuotientGroup.mk_mul (N := piSim Q) γu⁻¹ γv).trans
      (by rw [QuotientGroup.mk_inv (N := piSim Q) γu]))

private lemma ffOutN0_even_conj_symmDiff (σ τ : Equiv.Perm (Fin 6)) (K J : Finset (Fin 6)) :
    Even (symmDiff ((symmDiff (K.map τ⁻¹.toEmbedding) J).map σ.toEmbedding)
      (K.map σ.toEmbedding)).card ↔ Even J.card := by
  rw [ffOut_even_symmDiff_iff, Finset.card_map, ffOut_even_symmDiff_iff, Finset.card_map,
    Finset.card_map]
  tauto

private lemma ffOutN0_conj_mem (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    {σ : Equiv.Perm (Fin 6)} (hσ : ∀ τ ∈ monoD, σ * τ * σ⁻¹ ∈ monoD)
    (K : Finset (Fin 6)) {g : ProjSim Q} (hg : g ∈ ffPS hQ fr) :
    ffM fr σ K * g * (ffM fr σ K)⁻¹ ∈ ffPS hQ fr := by
  obtain ⟨τ, hτ, J, hJ, rfl⟩ := (mem_ffPS_iff hQ fr).mp hg
  rw [ffM_mul, ffM_inv, ffM_mul, ffM_mem_ffPS_iff]
  exact ⟨hσ τ hτ, (ffOutN0_even_conj_symmDiff σ τ K J).mpr hJ⟩

theorem ffM_mem_normalizer_ffPS (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    {σ : Equiv.Perm (Fin 6)} (hσ : ∀ τ ∈ monoD, σ * τ * σ⁻¹ ∈ monoD) (K : Finset (Fin 6)) :
    ffM fr σ K ∈ normalizer (ffPS hQ fr : Set (ProjSim Q)) := by
  have hσinv : ∀ τ ∈ monoD, σ⁻¹ * τ * σ ∈ monoD := by
    have hnorm : σ ∈ normalizer (monoD : Set (Equiv.Perm (Fin 6))) :=
      Subgroup.mem_normalizer_fintype fun n hn => hσ n hn
    intro τ hτ
    exact (Subgroup.mem_normalizer_iff''.mp hnorm τ).mp hτ
  refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => ?_, fun hg => ?_⟩
  · exact ffOutN0_conj_mem hQ fr hσ K hg
  · have h1 := ffOutN0_conj_mem hQ fr hσinv (K.map σ.toEmbedding) hg
    rw [show ffM fr σ⁻¹ (K.map σ.toEmbedding) = (ffM fr σ K)⁻¹ from
      (ffM_inv fr σ K).symm] at h1
    have hg_eq : (ffM fr σ K)⁻¹ * (ffM fr σ K * g * (ffM fr σ K)⁻¹) *
        ((ffM fr σ K)⁻¹)⁻¹ = g := by group
    rwa [hg_eq] at h1

theorem ff_N0_monomial (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) {q : ProjSim Q}
    (hqN : q ∈ normalizer (ffPS hQ fr : Set (ProjSim Q))) (hqG : SimInGStar q) :
    ∃ (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)),
      q = ffM fr σ K ∧ ∀ τ ∈ monoD, σ * τ * σ⁻¹ ∈ monoD := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hξN : ffX0 fr ∈ normalizer (ffPS hQ fr : Set (ProjSim Q)) :=
    ffX0_mem_normalizer_ffPS hQ fr
  have hξnot : ¬ SimInGStar (ffX0 fr) := ffX0_not_simInGStar fr
  have hUle : ∀ x : ProjSim Q, x ∈ normalizer (ffPS hQ fr : Set (ProjSim Q)) →
      (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom ≤ ffP1 hQ fr := by
    intro x hxN y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have hib : ffOmegaToSim hQ b ∈ ffPS hQ fr :=
      Subgroup.mem_map_of_mem (ffOmegaToSim hQ) (ffB1_le_ffP1 hQ fr hb)
    have hxib : x * ffOmegaToSim hQ b * x⁻¹ ∈ ffPS hQ fr :=
      (Subgroup.mem_normalizer_iff.mp hxN (ffOmegaToSim hQ b)).mp hib
    have hι : ffOmegaToSim hQ (ffSimOmegaAct hQ h2 x b) ∈
        (ffP1 hQ fr).map (ffOmegaToSim hQ) := by
      rw [ff_omegaToSim_act]
      exact hxib
    obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.mp hι
    have hp' : p = ffSimOmegaAct hQ h2 x b := ffOmegaToSim_injective hQ hpe
    rwa [hp'] at hp
  have hUe : ∀ x : ProjSim Q,
      IsElemAb2 ((ffB1 hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom) 4 := fun x =>
    ffOutN0_isElemAb2_map_mulEquiv (ffSimOmegaAct hQ h2 x) (ffB1_elemAb2 hQ hdim hsgn fr)
  have hneξ : (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 (ffX0 fr)).toMonoidHom ≠ ffB1 hQ fr :=
    fun h => hξnot (ff_star_normalizes_simInGStar hQ h2 fr h)
  have hUqB : (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 q).toMonoidHom = ffB1 hQ fr := by
    by_contra hne
    have heq : (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 q).toMonoidHom =
        (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 (ffX0 fr)).toMonoidHom :=
      ffP1_E16_unique hQ hdim hsgn fr (hUle q hqN) (hUe q) (hUle (ffX0 fr) hξN)
        (hUe (ffX0 fr)) hne hneξ
    let q' : ProjSim Q := (ffX0 fr)⁻¹ * q
    have hUq' : (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 q').toMonoidHom = ffB1 hQ fr := by
      have h1 : ffSimOmegaAct hQ h2 q' =
          (ffSimOmegaAct hQ h2 (ffX0 fr))⁻¹ * ffSimOmegaAct hQ h2 q := by
        dsimp only [q']
        rw [map_mul, map_inv]
      rw [h1, ffOutN0_map_mul, heq]
      exact ffOutN0_map_inv_map (ffSimOmegaAct hQ h2 (ffX0 fr)) (ffB1 hQ fr)
    have hq'G : SimInGStar q' := ff_star_normalizes_simInGStar hQ h2 fr hUq'
    have hξG : SimInGStar (ffX0 fr) := by
      have h := ffSimInGStar_mul hqG (ffSimInGStar_inv hq'G)
      have hq : q * q'⁻¹ = ffX0 fr := by
        dsimp only [q']
        group
      rwa [hq] at h
    exact hξnot hξG
  obtain ⟨σ, K, hq_mono⟩ := ff_star_normalizes hQ h2 fr hUqB
  refine ⟨σ, K, hq_mono, ?_⟩
  intro τ hτ
  have hmemPS : ffM fr τ ∅ ∈ ffPS hQ fr :=
    (ffM_mem_ffPS_iff hQ fr τ ∅).mpr ⟨hτ, by simp⟩
  have hconj : q * ffM fr τ ∅ * q⁻¹ ∈ ffPS hQ fr :=
    (Subgroup.mem_normalizer_iff.mp hqN (ffM fr τ ∅)).mp hmemPS
  have hq_eq : q = ffM fr σ K := hq_mono
  rw [hq_eq] at hconj
  obtain ⟨K', hK'⟩ := ffM_conj_perm fr σ τ K ∅
  rw [hK'] at hconj
  exact ((ffM_mem_ffPS_iff hQ fr (σ * τ * σ⁻¹) K').mp hconj).1

end CFSG.OddStandard.SmallF3.Omega
