module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Defs
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrTNormal
public import CFSG.ClassicalInvolution.Q3.TL4SepSub

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

variable {Y : Type} [Group Y] {Φ Δ : Set (Subgroup Y)} {K : Subgroup Y}

theorem le_normalizer_omegaGen {S : Set (Subgroup Y)} {M : Subgroup Y}
    (h : ∀ N ∈ S, M ≤ Subgroup.normalizer (N : Set Y)) :
    M ≤ Subgroup.normalizer (omegaGen S : Set Y) := by
  intro m hm
  refine T3Core.conjStab_le_normalizer_omegaGen S (mem_conjStab_iff.mpr fun N => ⟨fun hN => ?_,
    fun hN => ?_⟩)
  · have h1 : conjSub m (conjSub m N) = conjSub m N :=
      mem_normalizer_iff_conjSub_eq.mp (h _ hN hm)
    rwa [conjSub_injective m h1] at hN
  · rw [mem_normalizer_iff_conjSub_eq.mp (h N hN hm)]
    exact hN

theorem typeRHyp_of_subset (hΦ : TypeRHyp Φ) (hsub : Δ ⊆ Φ) (hc : ConjInvariant Δ) :
    TypeRHyp Δ where
  hyp := TL4.hypOmegaGen_sub hΦ.hyp hsub hc
  twoGroup := fun J hJ => hΦ.twoGroup J (hsub hJ)
  sylow := fun J hJ => hΦ.sylow J (hsub hJ)

theorem rSet_subset (hsub : Δ ⊆ Φ) : RSet Δ ⊆ RSet Φ := by
  rintro R ⟨J, hJ, P, rfl⟩
  exact ⟨J, hsub hJ, P, rfl⟩

theorem uSet_subset (hsub : Δ ⊆ Φ) : USet Δ ⊆ USet Φ := by
  rintro U ⟨R, hR, hUR, hc, hidx⟩
  exact ⟨R, rSet_subset hsub hR, hUR, hc, hidx⟩

theorem mem_omegaNbr_sub_iff [Finite Y] (hΦ : HypOmegaGen Φ) (hsub : Δ ⊆ Φ) {M J : Subgroup Y}
    (hJ : J ∈ Δ) : J ∈ omegaNbr Δ M ↔ J ∈ omegaNbr Φ M := by
  constructor
  · rintro ⟨-, hne, R, hR, hRJ, hRN⟩
    exact ⟨hsub hJ, hne, R, rSet_subset hsub hR, hRJ, hRN⟩
  · rintro ⟨-, hne, R, hR, hRJ, hRN⟩
    exact ⟨hJ, hne, R, mem_RSet_of_isSylow2In hJ
      (Sec6Gen.isSylow2In_of_mem_RSet_of_le hΦ (hsub hJ) hR hRJ), hRJ, hRN⟩

theorem mem_omegaStarNbr_sub_iff [Finite Y] (hΦ : HypOmegaGen Φ) (hsub : Δ ⊆ Φ)
    {M J : Subgroup Y} (hJ : J ∈ Δ) : J ∈ omegaStarNbr Δ M ↔ J ∈ omegaStarNbr Φ M := by
  constructor
  · rintro ⟨-, hne, U, hU, hUJ, hUN⟩
    exact ⟨hsub hJ, hne, U, uSet_subset hsub hU, hUJ, hUN⟩
  · rintro ⟨-, hne, U, hU, hUJ, hUN⟩
    refine ⟨hJ, hne, U, ?_, hUJ, hUN⟩
    obtain ⟨R, -, J', hJ', hRJ', hUR, hcyc, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΦ hU
    obtain ⟨R', hR', hUR'⟩ := IsSylow2In.exists_ge (hRJ'.2.1.to_le hUR) hUJ
    have hRR' : Nat.card R' = Nat.card R := hΦ.omega3 J (hsub hJ) J' hJ' R' R hR' hRJ'
    exact mem_USet_of_natCard hJ hR' hUR' hcyc (by rw [hRR', hcard])

theorem aViol_sub_iff [Finite Y] (hΦ : HypOmegaGen Φ) (hsub : Δ ⊆ Φ) {M J : Subgroup Y}
    {zM zJ : Y} (hJ : J ∈ Δ) : AViol Δ M J zM zJ ↔ AViol Φ M J zM zJ := by
  constructor
  · intro h
    exact ⟨(mem_omegaStarNbr_sub_iff hΦ hsub hJ).mp h.star,
      fun hn => h.not_nbr ((mem_omegaNbr_sub_iff hΦ hsub hJ).mpr hn), h.hzK, h.hzJ, h.no_conj⟩
  · intro h
    exact ⟨(mem_omegaStarNbr_sub_iff hΦ hsub hJ).mpr h.star,
      fun hn => h.not_nbr ((mem_omegaNbr_sub_iff hΦ hsub hJ).mp hn), h.hzK, h.hzJ, h.no_conj⟩

theorem aGraphAdj_sub_iff [Finite Y] (hΦ : HypOmegaGen Φ) (hsub : Δ ⊆ Φ) {M N : Subgroup Y}
    (hM : M ∈ Δ) (hN : N ∈ Δ) : aGraphAdj Δ M N ↔ aGraphAdj Φ M N := by
  constructor
  · rintro ⟨-, ⟨zM, zN, hv⟩ | ⟨zN, zM, hv⟩ | ⟨⟨-, w, h1, h2⟩, hne⟩⟩
    · exact ⟨hsub hN, Or.inl ⟨zM, zN, (aViol_sub_iff hΦ hsub hN).mp hv⟩⟩
    · exact ⟨hsub hN, Or.inr (Or.inl ⟨zN, zM, (aViol_sub_iff hΦ hsub hM).mp hv⟩)⟩
    · exact ⟨hsub hN, Or.inr (Or.inr ⟨⟨hsub hN, w, h1, h2⟩, hne⟩)⟩
  · rintro ⟨-, ⟨zM, zN, hv⟩ | ⟨zN, zM, hv⟩ | ⟨⟨-, w, h1, h2⟩, hne⟩⟩
    · exact ⟨hN, Or.inl ⟨zM, zN, (aViol_sub_iff hΦ hsub hN).mpr hv⟩⟩
    · exact ⟨hN, Or.inr (Or.inl ⟨zN, zM, (aViol_sub_iff hΦ hsub hM).mpr hv⟩)⟩
    · exact ⟨hN, Or.inr (Or.inr ⟨⟨hN, w, h1, h2⟩, hne⟩)⟩

theorem aStar_sub_eq [Finite Y] (hΦ : HypOmegaGen Φ) (hsub : Δ ⊆ Φ)
    (hcl : ∀ L ∈ Δ, ∀ N, aGraphAdj Φ L N → N ∈ Δ) {M : Subgroup Y} (hM : M ∈ Δ) :
    aStar Δ M = aStar Φ M := by
  ext N
  constructor
  · intro hN
    have key : N ∈ Δ ∧ N ∈ aStar Φ M := by
      induction hN with
      | refl => exact ⟨hM, Relation.ReflTransGen.refl⟩
      | @tail L N' _ hLN ih =>
        exact ⟨hLN.1, ih.2.tail ((aGraphAdj_sub_iff hΦ hsub ih.1 hLN.1).mp hLN)⟩
    exact key.2
  · intro hN
    have key : N ∈ Δ ∧ N ∈ aStar Δ M := by
      induction hN with
      | refl => exact ⟨hM, Relation.ReflTransGen.refl⟩
      | @tail L N' _ hLN ih =>
        have hN' := hcl L ih.1 N' hLN
        exact ⟨hN', ih.2.tail ((aGraphAdj_sub_iff hΦ hsub ih.1 hN').mpr hLN)⟩
    exact key.2

theorem twinSet_sub_eq (hsub : Δ ⊆ Φ) {L : Subgroup Y} (htw : twinSet Φ L ⊆ Δ) :
    twinSet Δ L = twinSet Φ L := by
  ext N
  constructor
  · rintro ⟨hN, w, h1, h2⟩
    exact ⟨hsub hN, w, h1, h2⟩
  · intro hN
    exact ⟨htw hN, hN.2⟩

theorem mem_omegaOfSet_sub_iff [Finite Y] (hΦ : HypOmegaGen Φ) (hsub : Δ ⊆ Φ)
    {V : Set (Subgroup Y)} {P : Subgroup Y} (hP : P ∈ Δ) :
    P ∈ omegaOfSet Δ V ↔ P ∈ omegaOfSet Φ V := by
  constructor
  · rintro ⟨-, h⟩
    exact ⟨hsub hP, fun N hN => (mem_omegaNbr_sub_iff hΦ hsub hP).mp (h N hN)⟩
  · rintro ⟨-, h⟩
    exact ⟨hP, fun N hN => (mem_omegaNbr_sub_iff hΦ hsub hP).mpr (h N hN)⟩

theorem thm3RowsG_congr {P : Subgroup Y} (h : restrictFamily Φ P = restrictFamily Δ P) :
    Thm3RowsG Φ P ↔ Thm3RowsG Δ P := by
  unfold Thm3RowsG Thm3RowsA Thm3RowW
  rw [h]

@[expose] def twinOrbit (Φ : Set (Subgroup Y)) (K : Subgroup Y) : Set (Subgroup Y) :=
  {L | ∃ g : Y, ∃ J ∈ twinSet Φ K, conjSub g J = L}

theorem twinOrbit_conjInvariant : ConjInvariant (twinOrbit Φ K) := by
  rintro g _ ⟨h, J, hJ, rfl⟩
  exact ⟨g * h, J, hJ, conjSub_mul g h J⟩

theorem twinOrbit_subset (hΦ : ConjInvariant Φ) : twinOrbit Φ K ⊆ Φ := by
  rintro _ ⟨g, J, hJ, rfl⟩
  exact hΦ g J hJ.1

theorem mem_twinOrbit_of_mem_twinSet {J : Subgroup Y} (hJ : J ∈ twinSet Φ K) :
    J ∈ twinOrbit Φ K :=
  ⟨1, J, hJ, conjSub_one J⟩

theorem mem_twinOrbit_self (hK : K ∈ Φ) {z : Y} (hz : IsUniqueInvolution K z) :
    K ∈ twinOrbit Φ K :=
  mem_twinOrbit_of_mem_twinSet ⟨hK, z, hz, hz⟩

theorem twinSet_subset_twinOrbit (hΦ : ConjInvariant Φ) {M : Subgroup Y}
    (hM : M ∈ twinOrbit Φ K) : twinSet Φ M ⊆ twinOrbit Φ K := by
  obtain ⟨g, J, ⟨-, z, hzK, hzJ⟩, rfl⟩ := hM
  rintro N ⟨hN, w, hwM, hwN⟩
  have hw : g * z * g⁻¹ = w := (hzJ.conj g).eq hwM
  refine ⟨g, conjSub g⁻¹ N, ⟨hΦ g⁻¹ N hN, z, hzK, ?_⟩, conjSub_conjSub_inv g N⟩
  have h1 := hwN.conj g⁻¹
  rwa [← hw, show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h1

theorem ncard_twinOrbit_lt [Finite Y] (hΦ : ConjInvariant Φ) (htw : ¬ TwinOrbits Φ K) :
    (twinOrbit Φ K).ncard < Φ.ncard := by
  refine Set.ncard_lt_ncard ⟨twinOrbit_subset hΦ, fun hsub => htw fun L hL => ?_⟩
    (Set.toFinite Φ)
  exact hsub hL

theorem mem_twinOrbit_of_aViol [Finite Y] (hΦ : HypOmegaGen Φ) {M J : Subgroup Y} {zM zJ : Y}
    (hM : M ∈ twinOrbit Φ K) (hv : AViol Φ M J zM zJ) : J ∈ twinOrbit Φ K := by
  have hMΦ : M ∈ Φ := twinOrbit_subset hΦ.conjInvariant hM
  obtain ⟨a, -, -, haΦ, haz, -⟩ := Q3T6D.AViol.exists_twin hΦ hMΦ hv
  have htw : conjSub a J ∈ twinOrbit Φ K :=
    twinSet_subset_twinOrbit hΦ.conjInvariant hM ⟨haΦ, zM, hv.hzK, haz⟩
  have h1 := twinOrbit_conjInvariant a⁻¹ _ htw
  rwa [conjSub_inv_conjSub] at h1

theorem mem_twinOrbit_of_aGraphAdj [Finite Y] (hΦ : HypOmegaGen Φ) {M N : Subgroup Y}
    (hM : M ∈ twinOrbit Φ K) (h : aGraphAdj Φ M N) : N ∈ twinOrbit Φ K := by
  obtain ⟨hN, ⟨zM, zN, hv⟩ | ⟨zN, zM, hv⟩ | ⟨htw, -⟩⟩ := h
  · exact mem_twinOrbit_of_aViol hΦ hM hv
  · exact mem_twinOrbit_of_aViol hΦ hM (aviol_symm_of_hypOmegaGen hΦ hN hv)
  · exact twinSet_subset_twinOrbit hΦ.conjInvariant hM htw

theorem aStar_subset_twinOrbit [Finite Y] (hΦ : HypOmegaGen Φ) {M : Subgroup Y}
    (hM : M ∈ twinOrbit Φ K) : aStar Φ M ⊆ twinOrbit Φ K := by
  intro N hN
  induction hN with
  | refl => exact hM
  | tail _ hLN ih => exact mem_twinOrbit_of_aGraphAdj hΦ ih hLN

theorem aStar_twinOrbit [Finite Y] (hΦ : HypOmegaGen Φ) {M : Subgroup Y}
    (hM : M ∈ twinOrbit Φ K) : aStar (twinOrbit Φ K) M = aStar Φ M :=
  aStar_sub_eq hΦ (twinOrbit_subset hΦ.conjInvariant)
    (fun _ hL _ h => mem_twinOrbit_of_aGraphAdj hΦ hL h) hM

theorem not_aEmpty_twinOrbit [Finite Y] (hΦ : HypOmegaGen Φ) (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    (g : Y) : ¬ AEmpty (twinOrbit Φ K) (conjSub g K) := by
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hA
  have hKΔ : K ∈ twinOrbit Φ K := mem_twinOrbit_self hK hv.hzK
  have hJΔ : J ∈ twinOrbit Φ K := mem_twinOrbit_of_aViol hΦ hKΔ hv
  have hvΔ : AViol (twinOrbit Φ K) K J zK zJ :=
    (aViol_sub_iff hΦ (twinOrbit_subset hΦ.conjInvariant) hJΔ).mpr hv
  exact not_aEmpty_iff.mpr ⟨_, _, _, hvΔ.conj twinOrbit_conjInvariant g⟩

theorem thm3RConclG_of_twinOrbit [Finite Y] (hΦ : TypeRHyp Φ) (hK : K ∈ Φ)
    (hC : Thm3RConclG (twinOrbit Φ K) K)
    (hcomm : ∀ L ∈ Φ, L ∉ twinOrbit Φ K → ∀ M ∈ twinOrbit Φ K, ⁅L, M⁆ = ⊥) :
    Thm3RConclG Φ K := by
  have hΩ := hΦ.hyp
  have hsub : twinOrbit Φ K ⊆ Φ := twinOrbit_subset hΩ.conjInvariant
  obtain ⟨z, hz⟩ := (hΩ.omega1 K hK).1
  have hKΔ : K ∈ twinOrbit Φ K := mem_twinOrbit_self hK hz
  have hcent : ∀ L ∈ Φ, L ∉ twinOrbit Φ K → ∀ N ∈ twinOrbit Φ K,
      N ≤ Subgroup.centralizer (L : Set Y) := fun L hL hLΔ N hN =>
    Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm L hL hLΔ N hN))
  have hnbr : ∀ L ∈ Φ, ∀ N : Subgroup Y, L ≠ N → L ≤ Subgroup.normalizer (N : Set Y) →
      L ∈ omegaNbr Φ N := by
    intro L hL N hLN hLn
    obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := L) IsPGroup.of_bot bot_le
    exact ⟨hL, hLN, R, mem_RSet_of_isSylow2In hL hR, hR.1, hR.1.trans hLn⟩
  have hout : ∀ L ∈ Φ, L ∉ twinOrbit Φ K → ∀ N ∈ twinOrbit Φ K, L ∈ omegaNbr Φ N := by
    intro L hL hLΔ N hN
    refine hnbr L hL N (fun h => hLΔ (h ▸ hN)) ?_
    have hLC : L ≤ Subgroup.centralizer (N : Set Y) := Subgroup.le_centralizer_iff.mp
      (hcent L hL hLΔ N hN)
    exact hLC.trans (Subgroup.centralizer_le_normalizer _)
  have hkey : ∀ J ∈ twinOrbit Φ K, ∀ N : Subgroup Y,
      N ∈ omegaOfSet Φ (twinSet Φ J) ↔
        N ∈ omegaOfSet (twinOrbit Φ K) (twinSet (twinOrbit Φ K) J) ∨
          (N ∈ Φ ∧ N ∉ twinOrbit Φ K) := by
    intro J hJ N
    rw [twinSet_sub_eq hsub (twinSet_subset_twinOrbit hΩ.conjInvariant hJ)]
    constructor
    · intro hN
      by_cases hNΔ : N ∈ twinOrbit Φ K
      · exact Or.inl ((mem_omegaOfSet_sub_iff hΩ hsub hNΔ).mpr hN)
      · exact Or.inr ⟨hN.1, hNΔ⟩
    · rintro (hN | ⟨hNΦ, hNΔ⟩)
      · exact (mem_omegaOfSet_sub_iff hΩ hsub hN.1).mp hN
      · exact ⟨hNΦ, fun T hT =>
          hout N hNΦ hNΔ T (twinSet_subset_twinOrbit hΩ.conjInvariant hJ hT)⟩
  have hvStar : vStar Φ K = vStar (twinOrbit Φ K) K := by
    ext J
    constructor
    · rintro ⟨hJΦ, heq⟩
      by_cases hJΔ : J ∈ twinOrbit Φ K
      · refine ⟨hJΔ, ?_⟩
        ext N
        have h1 := hkey K hKΔ N
        have h2 := hkey J hJΔ N
        rw [heq] at h1
        constructor
        · intro hN
          rcases h2.mp (h1.mpr (Or.inl hN)) with h | ⟨-, hNΔ⟩
          · exact h
          · exact absurd hN.1 hNΔ
        · intro hN
          rcases h1.mp (h2.mpr (Or.inl hN)) with h | ⟨-, hNΔ⟩
          · exact h
          · exact absurd hN.1 hNΔ
      · exfalso
        have hK1 : K ∈ omegaOfSet Φ (twinSet Φ J) := by
          refine ⟨hK, fun N hN => ?_⟩
          have hNΔ : N ∉ twinOrbit Φ K := by
            intro h
            obtain ⟨hNΦ, w, hwJ, hwN⟩ := hN
            exact hJΔ (twinSet_subset_twinOrbit hΩ.conjInvariant h ⟨hJΦ, w, hwN, hwJ⟩)
          exact hnbr K hK N (fun h => hNΔ (h ▸ hKΔ))
            ((hcent N hN.1 hNΔ K hKΔ).trans (Subgroup.centralizer_le_normalizer _))
        rw [← heq] at hK1
        exact (hK1.2 K ⟨hK, z, hz, hz⟩).2.1 rfl
    · rintro ⟨hJΔ, heq⟩
      refine ⟨hsub hJΔ, ?_⟩
      ext N
      rw [hkey K hKΔ N, hkey J hJΔ N, heq]
  have hst : aStar (twinOrbit Φ K) K = aStar Φ K := aStar_twinOrbit hΩ hKΔ
  have hres : restrictFamily Φ (omegaGen (aStar Φ K)) =
      restrictFamily (twinOrbit Φ K) (omegaGen (aStar Φ K)) := by
    ext L'
    constructor
    · rintro ⟨L, hL, hLP, rfl⟩
      refine ⟨L, ?_, hLP, rfl⟩
      by_contra hLΔ
      have hPC : omegaGen (aStar Φ K) ≤ Subgroup.centralizer (L : Set Y) :=
        iSup₂_le fun M hM => hcent L hL hLΔ M (aStar_subset_twinOrbit hΩ hKΔ hM)
      obtain ⟨-, Q, hQ, hQnc⟩ := hΩ.omega1 L hL
      refine hQnc ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      exact Subgroup.mem_centralizer_iff.mp (hPC (hLP (hQ.1 b.2))) a (hQ.1 a.2)
    · rintro ⟨L, hL, hLP, rfl⟩
      exact ⟨L, hsub hL, hLP, rfl⟩
  obtain ⟨⟨heqΔ, hcommΔ⟩, hrowsΔ⟩ := hC
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← hst, heqΔ, hvStar]
  · intro L hL hLv M hM
    rw [hvStar] at hLv hM
    by_cases hLΔ : L ∈ twinOrbit Φ K
    · exact hcommΔ L hLΔ hLv M hM
    · rw [hcomm L hL hLΔ M hM.1]
      exact bot_le
  · rw [hst] at hrowsΔ
    exact (thm3RowsG_congr hres).mpr hrowsΔ

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step
