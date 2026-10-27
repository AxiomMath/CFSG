module

public import CFSG.Adapters.TauCetiExceptional.MinusculeTriangular
public import CFSG.Adapters.TauCetiExceptional.BigCellBruhat
public import CFSG.Adapters.TauCetiExceptional.MinusculeMono

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg
  CFSG.TauCetiBridge.BigCell CFSG.LieType.Universal CFSG.LieType.RootSystem MinData
  CFSG.LieType.Chevalley

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (hA : TauCeti.IsFiniteType τ.cartan)
  (K : Type*) [Field K]

theorem exists_uPos_eq
    {u : hV.minGroup K} (hu : u ∈ posUnipotent (hV.minDatum hA K)) :
    ∃ c, uPos hV K c = (u : (Module.End K (Fin D.d →₀ K))ˣ) := by
  have hle : posUnipotent (hV.minDatum hA K) ≤
      ⨆ v ∈ (posList τ).map (posRootEnum τ), hV.rootGroup K v := by
    refine iSup₂_le fun γ hγ => ?_
    have hγ' : γ ∈ posRoots τ := ⟨(hV.mem_minDatum_roots hA K).1 hγ.1, hγ.2⟩
    rw [← range_posRootEnum] at hγ'
    obtain ⟨j, rfl⟩ := hγ'
    exact le_iSup₂ (f := fun v (_ : v ∈ (posList τ).map (posRootEnum τ)) => hV.rootGroup K v) _
      (List.mem_map_of_mem (mem_posList τ j))
  obtain ⟨c, hc⟩ := exists_list_prod_xm_eq hV K htHom (posRootEnum τ) (posRootEnum_pos τ)
    (posRootEnum_injective τ) (fun j j' hr => by
      have hpos : posRootEnum τ j + posRootEnum τ j' ∈ posRoots τ := by
        refine ⟨hr, ?_⟩
        have h1 := (posRootEnum_pos τ j).2
        have h2 := (posRootEnum_pos τ j').2
        simp only [height, Pi.add_apply, Finset.sum_add_distrib] at h1 h2 ⊢
        omega
      rw [← range_posRootEnum] at hpos
      exact hpos) (posList_sorted τ) (hle hu)
  exact ⟨c, by rw [uPos, ← list_prod_xm_coe, hc]⟩

theorem exists_uNeg_eq
    {u : hV.minGroup K} (hu : u ∈ negUnipotent (hV.minDatum hA K)) :
    ∃ c, uNeg hV K c = (u : (Module.End K (Fin D.d →₀ K))ˣ) := by
  have hle : negUnipotent (hV.minDatum hA K) ≤
      ⨆ v ∈ (posList τ).map (fun j => -posRootEnum τ j), hV.rootGroup K v := by
    refine iSup₂_le fun γ hγ => ?_
    have hγ' : -γ ∈ posRoots τ := by
      refine ⟨IsRoot.neg ((hV.mem_minDatum_roots hA K).1 hγ.1), ?_⟩
      have := hγ.2
      simp only [ht, height, Pi.neg_apply, Finset.sum_neg_distrib] at this ⊢
      omega
    rw [← range_posRootEnum] at hγ'
    obtain ⟨j, hj⟩ := hγ'
    have hγj : γ = -posRootEnum τ j := by rw [hj, neg_neg]
    subst hγj
    exact le_iSup₂ (f := fun v (_ : v ∈ (posList τ).map (fun j => -posRootEnum τ j)) =>
      hV.rootGroup K v) _ (List.mem_map_of_mem (f := fun j => -posRootEnum τ j) (mem_posList τ j))
  obtain ⟨c, hc⟩ := exists_list_prod_xm_eq hV K (-htHom) (fun j => -posRootEnum τ j)
    (fun j => ⟨IsRoot.neg (posRootEnum_pos τ j).1, by
      rw [AddMonoidHom.neg_apply, map_neg, neg_neg]
      exact (posRootEnum_pos τ j).2⟩)
    (neg_injective.comp (posRootEnum_injective τ)) (fun j j' hr => by
      have hpos : posRootEnum τ j + posRootEnum τ j' ∈ posRoots τ := by
        refine ⟨by simpa [neg_add, add_comm] using IsRoot.neg hr, ?_⟩
        have h1 := (posRootEnum_pos τ j).2
        have h2 := (posRootEnum_pos τ j').2
        simp only [height, Pi.add_apply, Finset.sum_add_distrib] at h1 h2 ⊢
        omega
      rw [← range_posRootEnum] at hpos
      obtain ⟨k, hk⟩ := hpos
      exact ⟨k, by rw [hk, neg_add]⟩)
    ((posList_sorted τ).imp fun h => by
      rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, map_neg, map_neg, neg_neg, neg_neg]
      exact h) (hle hu)
  exact ⟨c, by rw [uNeg, ← list_prod_xm_coe, hc]⟩

theorem upper_diag_mul {n : ℕ} {M N : Matrix (Fin n) (Fin n) K} (hM : ∀ i j, i ≠ j → M i j = 0)
    (hN : ∀ i j, j < i → N i j = 0) (i j : Fin n) (hji : j < i) : (M * N) i j = 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hM i k hk.symm, zero_mul])
    (fun hi => absurd (Finset.mem_univ i) hi), hN i j hji, mul_zero]

include hA in
theorem exists_bigCellUnit_eq
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (hord : DegOrdered D) (h : hV.minGroup K)
    (hΔ : bigCellDet (natMat K (hV.endo K h)) ≠ 0) :
    ∃ (cm : Fin (nPos τ) → K) (t : Fin τ.rank → Kˣ) (cp : Fin (nPos τ) → K),
      bigCellUnit hV K cm t cp = (h : (Module.End K (Fin D.d →₀ K))ˣ) := by
  set hct := hV.minDatum_isCTGroupDatum hA K
  have hext := hV.minDatum_steinbergExtras hA K hpd
  set n₀ : hV.minGroup K := nrep hct (longest τ)
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell hct hext (n₀ * h)
  obtain ⟨b₁, hb₁, b₂, hb₂, hbb⟩ := hw
  have hTU : ∀ x ∈ borel (hV.minDatum hA K) (hV.torus K), ∃ t ∈ ⨆ i, hV.torus K i,
      ∃ u ∈ posUnipotent (hV.minDatum hA K), t * u = x := by
    intro x hx
    have hx' : x ∈ (borel (hV.minDatum hA K) (hV.torus K) : Set (hV.minGroup K)) := hx
    rw [coe_borel hct] at hx'
    obtain ⟨t, ht, u, hu, e⟩ := Set.mem_mul.1 hx'
    exact ⟨t, ht, u, hu, e⟩
  obtain ⟨t₁, ht₁, u₁, hu₁, rfl⟩ := hTU b₁ hb₁
  obtain ⟨t₂, ht₂, u₂, hu₂, rfl⟩ := hTU b₂ hb₂
  set X := n₀⁻¹ * t₁ * n₀ with hXdef
  set Y := n₀⁻¹ * u₁ * n₀ with hYdef
  set m := n₀⁻¹ * nrep hct w with hmdef
  have hh : h = X * Y * m * (t₂ * u₂) := by
    have e : h = n₀⁻¹ * (n₀ * h) := by group
    rw [e, hbb, hXdef, hYdef, hmdef]
    group
  have hX : X ∈ ⨆ i, hV.torus K i := nrep_inv_conj_mem_iSup hct _ ht₁
  have hY : Y ∈ negUnipotent (hV.minDatum hA K) :=
    conj_mem_negUnipotent hV hA K (fun γ hγ hpos => (reversesSigns_longest τ).inv γ hγ hpos) hu₁
  have hm : m ∈ weylN (hV.nm K) (hV.torus K) :=
    mul_mem (inv_mem (nrep_mem_weylN hct _)) (nrep_mem_weylN hct w)
  have hL : ∀ i j, i < j → natMat K (hV.endo K (X * Y)) i j = 0 := by
    rw [hV.endo_mul, map_mul]
    exact lower_diag_mul (fun i j hij => natMat_torus hV K hX hij)
      (negUnipotent_le_lowerUniSubgroup hV hA K hord hY).1.upper
  have hU : ∀ i j, j < i → natMat K (hV.endo K (t₂ * u₂)) i j = 0 := by
    rw [hV.endo_mul, map_mul]
    exact upper_diag_mul K (fun i j hij => natMat_torus hV K ht₂ hij)
      (posUnipotent_le_upperUniSubgroup hV hA K hord hu₂).1.lower
  have hdet : bigCellDet (natMat K (hV.endo K m)) ≠ 0 := by
    intro h0
    apply hΔ
    rw [hh, hV.endo_mul K (X * Y * m), hV.endo_mul K (X * Y) m, map_mul, map_mul, bigCellDet]
    rw [bigCellDet] at h0
    simp only [leadMinor_mul_mul hL hU, Finset.prod_mul_distrib, h0, mul_zero, zero_mul]
  have hdiag : ∀ r s, r ≠ s → natMat K (hV.endo K m) r s = 0 := fun r s hrs =>
    natMat_eq_zero_of_isMono (f := (m : (Module.End K (Fin D.d →₀ K))ˣ))
      (isMono_of_mem_weylN hV hA K hm) hdet hrs
  have hmT : m ∈ ⨆ i, hV.torus K i := mem_iSup_torus_of_diag hV hA K hpd hm hdiag
  have huM : X * Y * X⁻¹ ∈ negUnipotent (hV.minDatum hA K) :=
    torus_conj_mem_negUnipotent hV hA K hX hY
  have htT : X * m * t₂ ∈ ⨆ i, hV.torus K i := mul_mem (mul_mem hX hmT) ht₂
  have hh' : h = X * Y * X⁻¹ * (X * m * t₂) * u₂ := by
    rw [hh]
    group
  obtain ⟨cm, hcm⟩ := exists_uNeg_eq hV hA K huM
  obtain ⟨s, hs⟩ := exists_torusElt_eq hV K htT
  obtain ⟨cp, hcp⟩ := exists_uPos_eq hV hA K hu₂
  refine ⟨cm, s, cp, ?_⟩
  rw [bigCellUnit, hcm, hcp, dT, ← coe_torusElt hV K s, hs, hh']
  rfl

end CFSG.TauCetiBridge.Minuscule
