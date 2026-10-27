module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
import CFSG.LocalAnalysis.AGLEmbedding.OneLieTorus

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem centralizer_le_sup_of_l34 {Y : Type} [Group Y] [Finite Y] {K X₀ : Subgroup Y}
    [K.Normal] (hK5 : KFactL34Local) (hL34 : IsLinThreeFour K) (T₁ : Sylow 3 K)
    (hY : X₀.subgroupOf K = GLBCore 3 1 (T₁ : Subgroup K))
    (hU2 : ∀ w ∈ Subgroup.normalizer (K : Set Y),
      w ∈ Subgroup.centralizer ((X₀ ⊓ K : Subgroup Y) : Set Y) →
        w ∈ Subgroup.centralizer (K : Set Y))
    {V : Subgroup Y} (hVT : V ≤ (T₁ : Subgroup K).map K.subtype) (hV : V ≠ ⊥)
    (hNV : K ⊓ Subgroup.normalizer (((T₁ : Subgroup K).map K.subtype : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer (V : Set Y)) :
    Subgroup.centralizer (V : Set Y) ≤
      (T₁ : Subgroup K).map K.subtype ⊔ Subgroup.centralizer (K : Set Y) := by
  intro y hy
  have hVK : V ≤ K := hVT.trans (Subgroup.map_subtype_le _)
  have hVmap : (V.subgroupOf K).map K.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVK
  have hV'T : V.subgroupOf K ≤ T₁ := by
    intro v hv
    obtain ⟨t, ht, htv⟩ := hVT (Subgroup.mem_subgroupOf.mp hv)
    rwa [← Subtype.ext htv]
  have hV'1 : V.subgroupOf K ≠ ⊥ := by
    intro hbot
    apply hV
    rw [← hVmap, hbot, Subgroup.map_bot]
  have hNV' : Subgroup.normalizer ((T₁ : Subgroup K) : Set K) ≤
      Subgroup.normalizer ((V.subgroupOf K : Subgroup K) : Set K) := fun n hn =>
    Subgroup.le_normalizer_comap K.subtype (hNV (coe_mem_normalizer_map hn))
  obtain ⟨-, hcen⟩ := hK5 K hL34 T₁
  obtain ⟨t, ht, hft⟩ := hcen _ hV'T hV'1 hNV' (MulAut.conjNormal y) fun v hv => by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply,
      ← Subgroup.mem_centralizer_iff.mp hy (v : Y) (Subgroup.mem_subgroupOf.mp hv)]
    group
  have hw : (t : Y)⁻¹ * y ∈ Subgroup.centralizer ((X₀ ⊓ K : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro x ⟨hxX, hxK⟩
    have hxΓ : (⟨x, hxK⟩ : K) ∈ GLBCore 3 1 (T₁ : Subgroup K) :=
      hY ▸ Subgroup.mem_subgroupOf.mpr hxX
    have h2 : y * x * y⁻¹ = (t : Y) * x * (t : Y)⁻¹ := by
      have := congrArg Subtype.val (hft _ hxΓ)
      simpa [MulAut.conjNormal_apply] using this
    calc x * ((t : Y)⁻¹ * y) = (t : Y)⁻¹ * ((t : Y) * x * (t : Y)⁻¹) * y := by group
      _ = (t : Y)⁻¹ * (y * x * y⁻¹) * y := by rw [h2]
      _ = (t : Y)⁻¹ * y * x := by group
  have hwN : (t : Y)⁻¹ * y ∈ Subgroup.normalizer (K : Set Y) := by
    rw [Subgroup.normalizer_eq_top K]
    exact Subgroup.mem_top _
  have e : y = (t : Y) * ((t : Y)⁻¹ * y) := by group
  rw [e]
  exact Subgroup.mul_mem_sup ⟨t, ht, rfl⟩ (hU2 _ hwN hw)

section PosA

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_centralizer_inf_le (h3 : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K)
    (huniq : D1UniqueOver H R (nclIn H (d1LiftX p H R K)))
    (hVT : d1MapPCore p M H ⊓
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ≠ ⊥)
    (hVC : d1MapPCore p M H ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ≠ ⊥)
    (hcent : Subgroup.centralizer ((d1MapPCore p M H ⊓
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) p)) ≤
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) : False := by
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨hWp, -, -, hWnC, hWiff⟩ := hd.d1MapPCore_facts h3 h84 hD2
  obtain ⟨hDM, hMD, hQD, -⟩ := pCoreCentralizerPreimage_facts p M
  have hCR := hd.cfg.red.centralizer_le_of_inf_ne_bot hd.comp hd.center hd.noncyclic hd.z hWp
    hWnC hVC ((Subgroup.centralizer_le inf_le_left).trans hcent)
  exact h3.false_of_normal_of_unique hDM hMD hQD
    (h3.glbPrimeCore_le_pCoreCentralizerPreimage h84 hD2) (hd.inf_le_sup_glbPrimeCore h3 hCR)
    (hd.commutator_nclIn_le h3 h84 hD2 (hWiff.mpr hVT)) huniq hCGT hD2

theorem D1OneSmallData.inf_ne_bot_and_normalizer_le (h3 : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K)
    (hVK : d1MapPCore p M H ⊓ K ≠ ⊥) :
    d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ≠ ⊥ ∧
      K ⊓ Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
          Subgroup _) : Set (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer ((d1MapPCore p M H ⊓
          ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) : Subgroup _) :
            Set (H ⧸ primeComplementCore (G := H) p)) := by
  obtain ⟨-, hWR, hWn, -, -⟩ := hd.d1MapPCore_facts h3 h84 hD2
  refine ⟨by rwa [← inf_assoc, inf_eq_left.mpr hWR], ?_⟩
  exact (le_inf hWn inf_le_right).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem D1OneSmallData.false_of_posA (hUP : KFactUPrimeSmall) (hKS : KFactOneSmall)
    (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K)
    (huniq : D1UniqueOver H R (nclIn H (d1LiftX p H R K))) (hL : ¬ (p = 3 ∧ IsLinThreeFour K))
    (hF : ¬ (p = 5 ∧ IsFi22 K)) (hVK : d1MapPCore p M H ⊓ K ≠ ⊥)
    (hVC : d1MapPCore p M H ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ≠ ⊥)
    (hZ : ¬ D1SmallPosZ p M H Rbar K) : False := by
  have h3 := hd.toPhaseThree hUP hL hF
  obtain ⟨T₁, hT₁, hF'⟩ := hd.oneSmallFacts hKS hL hF
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨hVT, hNV⟩ := hd.inf_ne_bot_and_normalizer_le h3 h84 hD2 hVK
  refine hd.false_of_centralizer_inf_le h3 h84 hCGT hD2 huniq hVT hVC ?_
  rcases centralizer_le_sup_of_oneSmallFacts T₁ hF' (hT₁ ▸ inf_le_right) hVT (hT₁ ▸ hNV) with
    h | ⟨h1, h2⟩
  · rwa [hT₁] at h
  · exact absurd ⟨by rw [h1, hT₁], by rwa [hT₁] at h2⟩ hZ

theorem D1OneSmallData.false_of_posA_l34 (hUE : KFactUPrimeExc) (hK5 : KFactL34Local)
    (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K)
    (huniq : D1UniqueOver H R (nclIn H (d1LiftX p H R K))) (hL34 : p = 3 ∧ IsLinThreeFour K)
    (hU2 : ¬ D1SmallU2Fails p M H K) (hVK : d1MapPCore p M H ⊓ K ≠ ⊥)
    (hVC : d1MapPCore p M H ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ≠ ⊥) : False := by
  have h3 := hd.toPhaseThree_of_exc hUE (Or.inl hL34) hU2
  obtain ⟨T₁, hT₁, hY, -⟩ := hd.inf_eq_glbCore_of_exc hUE (Or.inl hL34)
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨hVT, hNV⟩ := hd.inf_ne_bot_and_normalizer_le h3 h84 hD2 hVK
  refine hd.false_of_centralizer_inf_le h3 h84 hCGT hD2 huniq hVT hVC ?_
  have hU2' : ∀ w ∈ Subgroup.normalizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      w ∈ Subgroup.centralizer ((d1X0 p M H ⊓ K : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) p)) →
      w ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) :=
    fun w hwN hwC => by_contra fun hwK => hU2 ⟨w, hwN, hwC, hwK⟩
  obtain ⟨hp3, hL⟩ := hL34
  subst hp3
  have hcent := centralizer_le_sup_of_l34 hK5 hL T₁ hY hU2' (hT₁ ▸ inf_le_right) hVT
    (hT₁ ▸ hNV)
  rwa [hT₁] at hcent

end PosA

theorem stmtSmallPosA_of (hUP : KFactUPrimeSmall) (hUE : KFactUPrimeExc) (hKS : KFactOneSmall)
    (hK5 : KFactL34Local) (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) : StmtSmallPosA := by
  intro G _ _ p P M H R Rbar K hd huniq hLa hF hVK hVC hZ
  by_cases hL : p = 3 ∧ IsLinThreeFour K
  · exact hd.false_of_posA_l34 hUE hK5 h84 hCGT hD2 huniq hL (hLa hL.1 hL.2).2 hVK hVC
  · exact hd.false_of_posA hUP hKS h84 hCGT hD2 huniq hL hF hVK hVC hZ

end CFSG.AGLEmbedding
