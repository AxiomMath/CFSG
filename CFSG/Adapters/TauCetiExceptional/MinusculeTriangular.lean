module

public import CFSG.Adapters.TauCetiExceptional.MinusculeGenPoint
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.LieType.Steinberg.Minuscule.Datum

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg
  CFSG.TauCetiBridge.BigCell CFSG.LieType.Universal CFSG.LieType.RootSystem MinData
  CFSG.LieType.Chevalley

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (hA : TauCeti.IsFiniteType τ.cartan)
  (K : Type*) [Field K]

@[expose] def upperUniSubgroup :
    Subgroup (hV.minGroup K) where
  carrier := {g | IsUpperUni (natMat K (hV.endo K g)) ∧ IsUpperUni (natMat K (hV.endo K g⁻¹))}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, inv_one, hV.endo_one, map_one]
    exact ⟨isUpperUni_one, isUpperUni_one⟩
  mul_mem' := fun {g h} hg hh => by
    simp only [Set.mem_ofPred_eq, mul_inv_rev, hV.endo_mul, map_mul] at hg hh ⊢
    exact ⟨hg.1.mul hh.1, hh.2.mul hg.2⟩
  inv_mem' := fun {g} hg => by
    simp only [Set.mem_ofPred_eq, inv_inv] at hg ⊢
    exact ⟨hg.2, hg.1⟩

@[expose] def lowerUniSubgroup :
    Subgroup (hV.minGroup K) where
  carrier := {g | IsLowerUni (natMat K (hV.endo K g)) ∧ IsLowerUni (natMat K (hV.endo K g⁻¹))}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, inv_one, hV.endo_one, map_one]
    exact ⟨isLowerUni_one, isLowerUni_one⟩
  mul_mem' := fun {g h} hg hh => by
    simp only [Set.mem_ofPred_eq, mul_inv_rev, hV.endo_mul, map_mul] at hg hh ⊢
    exact ⟨hg.1.mul hh.1, hh.2.mul hg.2⟩
  inv_mem' := fun {g} hg => by
    simp only [Set.mem_ofPred_eq, inv_inv] at hg ⊢
    exact ⟨hg.2, hg.1⟩

theorem natMat_endo_xm
    (γ : Fin τ.rank → ℤ) (c : K) :
    natMat K (hV.endo K (hV.xm K γ c)) =
      natMat K (rootUnit hV K γ c : Module.End K (Fin D.d →₀ K)) := by
  rw [rootUnit_eq_xu]
  rfl

theorem posUnipotent_le_upperUniSubgroup
    (hord : DegOrdered D) :
    posUnipotent (hV.minDatum hA K) ≤ upperUniSubgroup hV K := by
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨hγ, hpos⟩ := hγ
  have hγ' := (hV.mem_minDatum_roots hA K).1 hγ
  rintro _ ⟨c, rfl⟩
  refine ⟨?_, ?_⟩
  · change IsUpperUni (natMat K (hV.endo K (hV.xm K γ (Multiplicative.toAdd c))))
    rw [natMat_endo_xm]
    exact isUpperUni_natMat_rootUnit hV hord K hγ' hpos _
  · change IsUpperUni (natMat K (hV.endo K (hV.xm K γ (Multiplicative.toAdd c))⁻¹))
    rw [hV.xm_neg, natMat_endo_xm]
    exact isUpperUni_natMat_rootUnit hV hord K hγ' hpos _

theorem negUnipotent_le_lowerUniSubgroup
    (hord : DegOrdered D) :
    negUnipotent (hV.minDatum hA K) ≤ lowerUniSubgroup hV K := by
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨hγ, hneg⟩ := hγ
  have hγ' := (hV.mem_minDatum_roots hA K).1 hγ
  rintro _ ⟨c, rfl⟩
  refine ⟨?_, ?_⟩
  · change IsLowerUni (natMat K (hV.endo K (hV.xm K γ (Multiplicative.toAdd c))))
    rw [natMat_endo_xm]
    exact isLowerUni_natMat_rootUnit hV hord K hγ' hneg _
  · change IsLowerUni (natMat K (hV.endo K (hV.xm K γ (Multiplicative.toAdd c))⁻¹))
    rw [hV.xm_neg, natMat_endo_xm]
    exact isLowerUni_natMat_rootUnit hV hord K hγ' hneg _

theorem natMat_torus
    {t : hV.minGroup K} (ht : t ∈ ⨆ i, hV.torus K i) {r s : Fin D.d}
    (hrs : r ≠ s) : natMat K (hV.endo K t) r s = 0 := by
  obtain ⟨μ, hμ⟩ := hV.exists_diagOp_of_mem_iSup_torus K ht
  rw [hμ, natMat_apply, diagOp_single, Finsupp.smul_apply, Finsupp.single_eq_of_ne hrs,
    smul_zero]

theorem exists_torusElt_eq
    {t : hV.minGroup K} (ht : t ∈ ⨆ i, hV.torus K i) :
    ∃ s : Fin τ.rank → Kˣ, torusElt hV K s = t := by
  have hendo : ∀ s s', torusElt hV K (s * s') = torusElt hV K s * torusElt hV K s' := by
    intro s s'
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, coe_torusElt, coe_torusElt, coe_torusElt, ← diagUnit_mul]
    congr 1
    funext a
    rw [Pi.mul_apply, TauCeti.torusCharacter_mul]
  refine Subgroup.iSup_induction _ (C := fun x => ∃ s, torusElt hV K s = x) ht
    (fun i x hx => ?_) ⟨1, ?_⟩ (fun x y ⟨s, hs⟩ ⟨s', hs'⟩ => ⟨s * s', by rw [hendo, hs, hs']⟩)
  · obtain ⟨u, rfl⟩ := (hV.mem_torus K).1 hx
    refine ⟨Pi.mulSingle i u, hV.endo_injective K ?_⟩
    have h1 := coe_torusElt hV K (Pi.mulSingle i u)
    change ((torusElt hV K (Pi.mulSingle i u) : hV.minGroup K) :
      (Module.End K (Fin D.d →₀ K))ˣ).val = _
    rw [h1, hV.endo_hm]
    refine ext_single fun a => ?_
    rw [diagUnit_single, MinData.hDiag_single, TauCeti.torusCharacter_mulSingle]
  · refine Subtype.ext ?_
    rw [coe_torusElt, OneMemClass.coe_one]
    refine Units.ext (ext_single fun a => ?_)
    rw [diagUnit_single, TauCeti.torusCharacter_one, Units.val_one, one_smul, Units.val_one,
      Module.End.one_apply]

theorem torus_conj_mem_negUnipotent
    {t : hV.minGroup K} (htT : t ∈ ⨆ i, hV.torus K i)
    {u : hV.minGroup K} (hu : u ∈ negUnipotent (hV.minDatum hA K)) :
    t * u * t⁻¹ ∈ negUnipotent (hV.minDatum hA K) := by
  set hct := hV.minDatum_isCTGroupDatum hA K
  have hle : negUnipotent (hV.minDatum hA K) ≤
      (negUnipotent (hV.minDatum hA K)).comap (MulAut.conj t).toMonoidHom := by
    refine iSup₂_le fun γ hγ => fun x hx => ?_
    have hn := iSup_le_normalizer_rootGroup hct hγ.1 htT
    have hx' := (Subgroup.mem_normalizer_iff.1 hn x).1 hx
    exact (le_iSup₂ (f := fun γ (_ : γ ∈ {γ | γ ∈ (hV.minDatum hA K).roots ∧ ht γ < 0}) =>
      (hV.minDatum hA K).rootGroup γ) γ hγ) hx'
  exact hle hu

theorem conj_mem_negUnipotent
    {w : (coxeterMatrix hA).Group}
    (hw : ∀ γ, IsRoot τ γ → 0 < ht γ → ht (weylAction hA w⁻¹ γ) < 0)
    {u : hV.minGroup K} (hu : u ∈ posUnipotent (hV.minDatum hA K)) :
    (nrep (hV.minDatum_isCTGroupDatum hA K) w)⁻¹ * u * nrep (hV.minDatum_isCTGroupDatum hA K) w ∈
      negUnipotent (hV.minDatum hA K) := by
  set hct := hV.minDatum_isCTGroupDatum hA K
  have hle : posUnipotent (hV.minDatum hA K) ≤
      (negUnipotent (hV.minDatum hA K)).comap (MulAut.conj (nrep hct w)⁻¹).toMonoidHom := by
    refine iSup₂_le fun γ hγ => fun x hx => ?_
    have h1 := nrep_inv_conj_mem hct w hγ.1 hx
    have hγ' := (hV.mem_minDatum_roots hA K).1 hγ.1
    have hmem : weylAction hA w⁻¹ γ ∈ {γ | γ ∈ (hV.minDatum hA K).roots ∧ ht γ < 0} :=
      ⟨weylAction_mem_roots hA w⁻¹ hγ.1, hw γ hγ' hγ.2⟩
    have h2 := (le_iSup₂ (f := fun γ (_ : γ ∈ {γ | γ ∈ (hV.minDatum hA K).roots ∧ ht γ < 0}) =>
      (hV.minDatum hA K).rootGroup γ) _ hmem) h1
    change (nrep hct w)⁻¹ * x * (nrep hct w)⁻¹⁻¹ ∈ negUnipotent (hV.minDatum hA K)
    rw [inv_inv]
    exact h2
  exact hle hu

theorem list_prod_xm_coe
    (γ : Fin (nPos τ) → Fin τ.rank → ℤ) (c : Fin (nPos τ) → K) :
    ((((posList τ).map fun j => hV.xm K (γ j) (c j)).prod : hV.minGroup K) :
      (Module.End K (Fin D.d →₀ K))ˣ) =
        ((posList τ).map fun j => rootUnit hV K (γ j) (c j)).prod := by
  rw [SubmonoidClass.coe_list_prod, List.map_map]
  rfl

theorem exists_list_prod_xm_eq
    (φ : (Fin τ.rank → ℤ) →+ ℤ) (γ : Fin (nPos τ) → Fin τ.rank → ℤ)
    (hγ : ∀ j, IsRoot τ (γ j) ∧ 0 < φ (γ j)) (hinj : Function.Injective γ)
    (hclosed : ∀ j j', IsRoot τ (γ j + γ j') → ∃ k, γ k = γ j + γ j')
    (hsort : (posList τ).Pairwise fun j j' => φ (γ j) ≤ φ (γ j'))
    {g : hV.minGroup K} (hg : g ∈ ⨆ v ∈ (posList τ).map γ, hV.rootGroup K v) :
    ∃ c : Fin (nPos τ) → K, ((posList τ).map fun j => hV.xm K (γ j) (c j)).prod = g := by
  have hsort' : ((posList τ).map γ).Pairwise fun a b => φ a ≤ φ b := List.pairwise_map.2 hsort
  obtain ⟨f, hf, rfl⟩ := exists_prod_eq_of_commutator_mem (hV.rootGroup K) (fun v => φ v)
    ((posList_nodup τ).map hinj) hsort' (fun a ha b hb hab x hx y hy => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
      obtain ⟨j', -, rfl⟩ := List.mem_map.1 hb
      obtain ⟨c, rfl⟩ := (hV.mem_rootGroup K).1 hx
      obtain ⟨c', rfl⟩ := (hV.mem_rootGroup K).1 hy
      have hne : γ j + γ j' ≠ 0 := fun h => by
        have := congrArg φ h
        rw [map_add, map_zero] at this
        have := (hγ j).2
        have := (hγ j').2
        omega
      obtain ⟨hr, hnr⟩ := hV.commutator_xm K (hγ j).1 (hγ j').1 hne
      by_cases hroot : IsRoot τ (γ j + γ j')
      · obtain ⟨σ, -, hσ⟩ := hr hroot
        rw [hσ]
        obtain ⟨k, hk⟩ := hclosed j j' hroot
        refine (le_iSup₂ (f := fun v (_ : v ∈ (posList τ).map γ) =>
          ⨆ (_ : min (φ (γ j)) (φ (γ j')) < φ v), hV.rootGroup K v) (γ k)
          (List.mem_map_of_mem (mem_posList τ k))) ?_
        refine (le_iSup (fun (_ : min (φ (γ j)) (φ (γ j')) < φ (γ k)) =>
          hV.rootGroup K (γ k)) ?_) ?_
        · rw [hk, map_add]
          have := (hγ j).2
          have := (hγ j').2
          omega
        · rw [hk]
          exact hV.xm_mem_rootGroup K _ _
      · rw [hnr hroot]
        exact one_mem _) g hg
  choose c hc using fun j => (hV.mem_rootGroup K).1 (hf (γ j)
    (List.mem_map_of_mem (mem_posList τ j)))
  refine ⟨c, ?_⟩
  rw [List.map_map]
  exact congrArg List.prod (List.map_congr_left fun j _ => hc j)

end CFSG.TauCetiBridge.Minuscule
