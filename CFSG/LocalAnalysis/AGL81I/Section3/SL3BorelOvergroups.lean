module

public import CFSG.LocalAnalysis.AGL81I.Section3.SL3Parabolic
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer
open Matrix
open scoped MatrixGroups

variable {K : Type*} [Field K]

theorem reflection_not_mem_upperTriangular_sl3 {d : ℕ} (hd : 1 ≤ d) (hdn : d < 3) :
    reflection 3 K d hd hdn ∉ upperTriangular 3 K :=
  fun h => reflection_notMem_stabilizer (n := 3) hd hdn
    (upperTriangular_le_stabilizer_flagSpace (n := 3) d h)

theorem flagStabilizer_sl3_borel :
    flagStabilizer 3 K ({1, 2} : Set ℕ) = upperTriangular 3 K := by
  have hcuts : borelOvergroupCuts (upperTriangular 3 K) = ({1, 2} : Set ℕ) := by
    ext i
    constructor
    · rintro ⟨h1, h2, -⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    · intro hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with rfl | rfl
      · exact ⟨le_rfl, by norm_num,
          reflection_not_mem_upperTriangular_sl3 le_rfl (by norm_num)⟩
      · exact ⟨by norm_num, by norm_num,
          reflection_not_mem_upperTriangular_sl3 (by norm_num) (by norm_num)⟩
  have h := (borel_overgroups (upperTriangular 3 K) le_rfl).1
  rw [hcuts] at h
  exact h.symm

theorem borel_overgroups_sl3 (A : Subgroup (SpecialLinearGroup (Fin 3) K))
    (hA : upperTriangular 3 K ≤ A) :
    A = ⊤ ∨ A = flagStabilizer 3 K ({1} : Set ℕ) ∨
      A = flagStabilizer 3 K ({2} : Set ℕ) ∨ A = upperTriangular 3 K := by
  classical
  obtain ⟨hAeq, -⟩ := borel_overgroups A hA
  set I := borelOvergroupCuts A with hIdef
  have hsub : ∀ i ∈ I, i = 1 ∨ i = 2 := by
    rintro i ⟨h1, h2, -⟩
    omega
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · refine Or.inr (Or.inr (Or.inr ?_))
    have hI : I = ({1, 2} : Set ℕ) := by
      ext i
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨fun hi => hsub i hi, fun hi => hi.elim (fun e => e ▸ h1) (fun e => e ▸ h2)⟩
    rw [hAeq, hI, flagStabilizer_sl3_borel]
  · refine Or.inr (Or.inl ?_)
    have hI : I = ({1} : Set ℕ) := by
      ext i
      simp only [Set.mem_singleton_iff]
      exact ⟨fun hi => (hsub i hi).elim id fun e => absurd (e ▸ hi) h2, fun hi => hi ▸ h1⟩
    rw [hAeq, hI]
  · refine Or.inr (Or.inr (Or.inl ?_))
    have hI : I = ({2} : Set ℕ) := by
      ext i
      simp only [Set.mem_singleton_iff]
      exact ⟨fun hi => (hsub i hi).elim (fun e => absurd (e ▸ hi) h1) id, fun hi => hi ▸ h2⟩
    rw [hAeq, hI]
  · refine Or.inl ?_
    have hI : I = ∅ := by
      ext i
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hi
      exact (hsub i hi).elim (fun e => h1 (e ▸ hi)) (fun e => h2 (e ▸ hi))
    rw [hAeq, hI, flagStabilizer_empty]

section SL3ModP

variable {p : ℕ} [Fact p.Prime]

theorem isSylowOf_unitriangular_sl3 :
    CFSG.ABGLocalTools.IsSylowOf p (unitriangular 3 (ZMod p))
      (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p))) := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod p) p (n := 3) (by norm_num)
  rw [← hP, CFSG.ABGLocalTools.isSylowOf_iff]
  exact ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩

theorem exists_conj_borel_eq_normalizer
    (P : Sylow p (SpecialLinearGroup (Fin 3) (ZMod p))) :
    ∃ g : SpecialLinearGroup (Fin 3) (ZMod p),
      Subgroup.normalizer (P : Set (SpecialLinearGroup (Fin 3) (ZMod p))) =
        (upperTriangular 3 (ZMod p)).map
          (MulAut.conj g : SpecialLinearGroup (Fin 3) (ZMod p) →* _) := by
  obtain ⟨PU, hPU⟩ := exists_sylow_unitriangular (K := ZMod p) p (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) (ZMod p)) PU P
  refine ⟨g, ?_⟩
  have hPcoe : (P : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p))) =
      (PU : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p))).map
        (MulAut.conj g : SpecialLinearGroup (Fin 3) (ZMod p) →* _) := by
    rw [← hg]
    exact coe_sylow_smul g PU
  change Subgroup.normalizer ((P : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p))) :
    Set (SpecialLinearGroup (Fin 3) (ZMod p))) = _
  rw [hPcoe, normalizer_map_conj, hPU, normalizer_unitriangular]

theorem isMaxParabolicP_sl3_zmod_singleton {d : ℕ} (hd : 1 ≤ d) (hdn : d < 3) :
    IsMaxParabolicP p (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)))
      (flagStabilizer 3 (ZMod p) ({d} : Set ℕ)) := by
  have hcard : Nat.card (ZMod p) = p := Nat.card_zmod p
  rw [isMaxParabolicP_sl3_iff (F := ZMod p) (p := p) hcard]
  have hfin : Module.finrank (ZMod p) (flagSpace 3 (ZMod p) d) = d :=
    finrank_flagSpace (K := ZMod p) (n := 3) hdn.le
  refine ⟨flagSpace 3 (ZMod p) d, ?_, ?_, ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro hbot
    rw [hbot, finrank_bot] at hfin
    omega
  · rw [lt_top_iff_ne_top]
    intro htop
    rw [htop, finrank_top, Module.finrank_fin_fun] at hfin
    omega
  · rw [comap_projStabilizer, ← flagStabilizer_singleton (K := ZMod p) (n := 3) d]

theorem isMaxParabolicP_sl3_zmod_one :
    IsMaxParabolicP p (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)))
      (flagStabilizer 3 (ZMod p) ({1} : Set ℕ)) :=
  isMaxParabolicP_sl3_zmod_singleton (by norm_num) (by norm_num)

theorem isMaxParabolicP_sl3_zmod_two :
    IsMaxParabolicP p (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)))
      (flagStabilizer 3 (ZMod p) ({2} : Set ℕ)) :=
  isMaxParabolicP_sl3_zmod_singleton (by norm_num) (by norm_num)

theorem flagStabilizer_singleton_ne_upperTriangular_sl3 {d e : ℕ} (hd : 1 ≤ d) (hdn : d < 3)
    (he : 1 ≤ e) (hen : e < 3) (hed : d ≠ e) :
    flagStabilizer 3 (ZMod p) ({d} : Set ℕ) ≠ upperTriangular 3 (ZMod p) := by
  intro h
  have hmem : reflection 3 (ZMod p) e he hen ∈ flagStabilizer 3 (ZMod p) ({d} : Set ℕ) := by
    rw [flagStabilizer_singleton]
    exact reflection_mem_stabilizer_of_ne (K := ZMod p) he hen hed
  rw [h] at hmem
  exact reflection_not_mem_upperTriangular_sl3 (K := ZMod p) he hen hmem

theorem isMaxParabolicP_sl3_zmod_iff {Y : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p))}
    (hB : upperTriangular 3 (ZMod p) ≤ Y) :
    IsMaxParabolicP p (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p))) Y ↔
      Y = flagStabilizer 3 (ZMod p) ({1} : Set ℕ) ∨
        Y = flagStabilizer 3 (ZMod p) ({2} : Set ℕ) := by
  constructor
  · intro hmax
    rcases borel_overgroups_sl3 Y hB with h | h | h | h
    · exact absurd h hmax.2.1
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hQ1 := hmax.2.2 (flagStabilizer 3 (ZMod p) ({1} : Set ℕ))
        isMaxParabolicP_sl3_zmod_one.1 isMaxParabolicP_sl3_zmod_one.2.1
        (by rw [h]; exact upperTriangular_le_flagStabilizer ({1} : Set ℕ))
      rw [h] at hQ1
      exact flagStabilizer_singleton_ne_upperTriangular_sl3 (d := 1) (e := 2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hQ1
  · rintro (rfl | rfl)
    · exact isMaxParabolicP_sl3_zmod_one
    · exact isMaxParabolicP_sl3_zmod_two

end SL3ModP

section SubgroupOf

variable {A : Type} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]

theorem isParabolicP_subgroupOf_iff {K P : Subgroup A} (hPK : P ≤ K) :
    IsParabolicP p K P ↔ IsParabolicP p (⊤ : Subgroup ↥K) (P.subgroupOf K) := by
  have hmapK : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  constructor
  · rintro ⟨-, U, hU, hNU⟩
    refine ⟨le_top, U.subgroupOf K, ?_, ?_⟩
    · rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := p) K
        (A := U.subgroupOf K) (B := ⊤), Subgroup.map_subgroupOf_eq_of_le hU.le, hmapK]
      exact hU
    · rw [top_inf_eq, ← Subgroup.subgroupOf_normalizer_eq hU.le,
        ← Subgroup.inf_subgroupOf_left]
      exact Subgroup.subgroupOf_mono K hNU
  · rintro ⟨-, U', hU', hNU'⟩
    refine ⟨hPK, U'.map K.subtype, ?_, ?_⟩
    · have h := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := p) K
        (A := U') (B := ⊤)).mpr hU'
      rwa [hmapK] at h
    · intro x hx
      have hxN : (⟨x, hx.1⟩ : ↥K) ∈ Subgroup.normalizer (U' : Set ↥K) := by
        have hHsub : (U'.map K.subtype).subgroupOf K = U' :=
          Subgroup.comap_map_eq_self_of_injective K.subtype_injective U'
        have hx2 : (⟨x, hx.1⟩ : ↥K) ∈
            (Subgroup.normalizer (U'.map K.subtype)).subgroupOf K :=
          Subgroup.mem_subgroupOf.mpr hx.2
        rwa [Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le U'), hHsub] at hx2
      exact Subgroup.mem_subgroupOf.mp (hNU' ⟨Subgroup.mem_top _, hxN⟩)

theorem isMaxParabolicP_subgroupOf_iff {K P : Subgroup A} (hPK : P ≤ K) :
    IsMaxParabolicP p K P ↔ IsMaxParabolicP p (⊤ : Subgroup ↥K) (P.subgroupOf K) := by
  have hmapP : (P.subgroupOf K).map K.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPK
  have hpar : IsParabolicP p K P ↔ IsParabolicP p (⊤ : Subgroup ↥K) (P.subgroupOf K) :=
    isParabolicP_subgroupOf_iff (p := p) hPK
  constructor
  · intro hmax
    refine ⟨hpar.mp hmax.1, ?_, ?_⟩
    · intro htop
      exact hmax.2.1 (le_antisymm hPK (Subgroup.subgroupOf_eq_top.mp htop))
    · intro Q hQpar hQne hle
      have hQ'sub : (Q.map K.subtype).subgroupOf K = Q :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q
      have hQ'par : IsParabolicP p K (Q.map K.subtype) :=
        (isParabolicP_subgroupOf_iff (p := p) (Subgroup.map_subtype_le Q)).mpr
          (hQ'sub.symm ▸ hQpar)
      have hQ'ne : Q.map K.subtype ≠ K := by
        intro h
        exact hQne (by rw [← hQ'sub, h, Subgroup.subgroupOf_self])
      have hPQ' : P ≤ Q.map K.subtype := by
        intro x hx
        exact Subgroup.mem_map.mpr
          ⟨⟨x, hPK hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
      rw [← hQ'sub, hmax.2.2 (Q.map K.subtype) hQ'par hQ'ne hPQ']
  · intro hmax
    refine ⟨hpar.mpr hmax.1, ?_, ?_⟩
    · intro htop
      exact hmax.2.1 (by rw [htop, Subgroup.subgroupOf_self])
    · intro Q hQpar hQne hle
      have hQK : Q ≤ K := hQpar.1
      have hQ'par : IsParabolicP p (⊤ : Subgroup ↥K) (Q.subgroupOf K) :=
        (isParabolicP_subgroupOf_iff (p := p) hQK).mp hQpar
      have hQ'ne : Q.subgroupOf K ≠ ⊤ := by
        intro h
        exact hQne (le_antisymm hQK (Subgroup.subgroupOf_eq_top.mp h))
      have hle' : P.subgroupOf K ≤ Q.subgroupOf K := Subgroup.subgroupOf_mono K hle
      calc Q = (Q.subgroupOf K).map K.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hQK).symm
        _ = (P.subgroupOf K).map K.subtype := by
            rw [hmax.2.2 (Q.subgroupOf K) hQ'par hQ'ne hle']
        _ = P := hmapP

end SubgroupOf

section IsSLType

variable {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem isMaxParabolicP_of_isSLType_borel {I Y : Subgroup H}
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (hYI : Y ≤ I) (hne : Y ≠ I)
    (hBlt : (upperTriangular 3 (ZMod p)).comap e.toMonoidHom < Y.subgroupOf I) :
    IsMaxParabolicP p I Y := by
  rw [isMaxParabolicP_subgroupOf_iff hYI]
  rw [isMaxParabolicP_of_mulEquiv e (Y.subgroupOf I)]
  set Y' := (Y.subgroupOf I).map e.toMonoidHom with hY'
  have hB : upperTriangular 3 (ZMod p) ≤ Y' := by
    calc upperTriangular 3 (ZMod p)
        = ((upperTriangular 3 (ZMod p)).comap e.toMonoidHom).map e.toMonoidHom :=
          (Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective _).symm
      _ ≤ (Y.subgroupOf I).map e.toMonoidHom :=
          Subgroup.map_mono (f := e.toMonoidHom) hBlt.le
  have hY'ne : Y' ≠ ⊤ := by
    intro h
    have h' : Subgroup.comap e.toMonoidHom
        (Subgroup.map e.toMonoidHom (Y.subgroupOf I)) = ⊤ := by
      rw [← hY', h]
      exact Subgroup.comap_top e.toMonoidHom
    rw [Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective] at h'
    exact hne (le_antisymm hYI (Subgroup.subgroupOf_eq_top.mp h'))
  have hY'neB : Y' ≠ upperTriangular 3 (ZMod p) := by
    intro h
    have h' : Subgroup.comap e.toMonoidHom
        (Subgroup.map e.toMonoidHom (Y.subgroupOf I)) =
          Subgroup.comap e.toMonoidHom (upperTriangular 3 (ZMod p)) := by
      rw [← hY', h]
    rw [Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective] at h'
    exact (ne_of_gt hBlt) h'
  rcases borel_overgroups_sl3 Y' hB with h | h | h | h
  · exact absurd h hY'ne
  · exact (isMaxParabolicP_sl3_zmod_iff hB).mpr (Or.inl h)
  · exact (isMaxParabolicP_sl3_zmod_iff hB).mpr (Or.inr h)
  · exact absurd h hY'neB

theorem isMaxParabolicP_of_isSLType_conjBorel {I Y : Subgroup H}
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (hYI : Y ≤ I) (hne : Y ≠ I) (x : ↥I)
    (hBlt : ((upperTriangular 3 (ZMod p)).comap e.toMonoidHom).map
        (MulAut.conj x : ↥I →* ↥I) < Y.subgroupOf I) :
    IsMaxParabolicP p I Y := by
  have key : ∀ y : ↥I, (e.trans (MulAut.conj (e x⁻¹))) y = e (x⁻¹ * y * x) := by
    intro y
    rw [MulEquiv.trans_apply, MulAut.conj_apply]
    conv_rhs => rw [map_mul, map_mul]
    rw [map_inv e x, inv_inv]
  have hcomap : (upperTriangular 3 (ZMod p)).comap
      (e.trans (MulAut.conj (e x⁻¹))).toMonoidHom =
      ((upperTriangular 3 (ZMod p)).comap e.toMonoidHom).map
        (MulAut.conj x : ↥I →* ↥I) := by
    ext y
    rw [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · intro hy
      change (e.trans (MulAut.conj (e x⁻¹))) y ∈ upperTriangular 3 (ZMod p) at hy
      rw [key y] at hy
      refine ⟨x⁻¹ * y * x, Subgroup.mem_comap.mpr hy, ?_⟩
      show x * (x⁻¹ * y * x) * x⁻¹ = y
      group
    · rintro ⟨z, hz, hzy⟩
      change (e.trans (MulAut.conj (e x⁻¹))) y ∈ upperTriangular 3 (ZMod p)
      rw [key y]
      have hzy' : x⁻¹ * y * x = z := by
        rw [← hzy]
        show x⁻¹ * (x * z * x⁻¹) * x = z
        group
      rw [hzy']
      exact Subgroup.mem_comap.mp hz
  refine isMaxParabolicP_of_isSLType_borel
    (e := e.trans (MulAut.conj (e x⁻¹))) hYI hne ?_
  rwa [hcomap]

theorem isMaxParabolicP_of_isSLType_sylowNormalizer {I Y : Subgroup H}
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (hYI : Y ≤ I) (hne : Y ≠ I)
    {U : Subgroup H} (hU : CFSG.ABGLocalTools.IsSylowOf p U I)
    (hN : Subgroup.normalizer (U : Set H) ⊓ I < Y) :
    IsMaxParabolicP p I Y := by
  obtain ⟨Q, hQ⟩ := hU.exists_sylow_eq_subgroupOf
  have hN' : (Subgroup.normalizer (U : Set H) ⊓ I).subgroupOf I < Y.subgroupOf I := by
    refine lt_of_le_of_ne (Subgroup.subgroupOf_mono I hN.le) ?_
    intro heq
    have hinf : (Subgroup.normalizer (U : Set H) ⊓ I) ⊓ I = Y ⊓ I :=
      (Subgroup.subgroupOf_inj (K := I)).mp heq
    rw [inf_assoc, inf_idem, inf_eq_left.mpr hYI] at hinf
    exact hN.ne hinf
  have hNQ : Subgroup.normalizer (Q : Set ↥I) < Y.subgroupOf I := by
    rwa [Subgroup.inf_subgroupOf_right, Subgroup.subgroupOf_normalizer_eq hU.le, ← hQ] at hN'
  obtain ⟨g, hg⟩ := exists_conj_borel_eq_normalizer (Q.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hcoe : ((Q.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow p
      (SpecialLinearGroup (Fin 3) (ZMod p))) :
      Subgroup (SpecialLinearGroup (Fin 3) (ZMod p))) =
      (Q : Subgroup ↥I).map e.toMonoidHom := rfl
  have heN : (Subgroup.normalizer (Q : Set ↥I)).map e.toMonoidHom =
      (upperTriangular 3 (ZMod p)).map
        (MulAut.conj g : SpecialLinearGroup (Fin 3) (ZMod p) →* _) := by
    change (Subgroup.normalizer (Q : Subgroup ↥I)).map e.toMonoidHom =
      (upperTriangular 3 (ZMod p)).map
        (MulAut.conj g : SpecialLinearGroup (Fin 3) (ZMod p) →* _)
    rw [Subgroup.map_equiv_normalizer_eq (Q : Subgroup ↥I) e, ← hcoe]
    exact hg
  have hNQe : (upperTriangular 3 (ZMod p)).map
      (MulAut.conj g : SpecialLinearGroup (Fin 3) (ZMod p) →* _) <
      (Y.subgroupOf I).map e.toMonoidHom := by
    rw [← heN]
    exact (Subgroup.map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr hNQ
  set x : ↥I := e.symm g with hxdef
  have hx : e x = g := e.apply_symm_apply g
  have hcompe : (((upperTriangular 3 (ZMod p)).comap e.toMonoidHom).map
      (MulAut.conj x : ↥I →* ↥I)).map e.toMonoidHom =
      (upperTriangular 3 (ZMod p)).map
        (MulAut.conj g : SpecialLinearGroup (Fin 3) (ZMod p) →* _) := by
    rw [Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp (MulAut.conj x : ↥I →* ↥I) =
        (MulAut.conj g : SpecialLinearGroup (Fin 3) (ZMod p) →* _).comp e.toMonoidHom := by
      refine MonoidHom.ext (fun y => ?_)
      change e (x * y * x⁻¹) = g * e y * g⁻¹
      rw [map_mul, map_mul, map_inv, hx]
    rw [hcomp, ← Subgroup.map_map]
    rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective]
  have hBlt : ((upperTriangular 3 (ZMod p)).comap e.toMonoidHom).map
      (MulAut.conj x : ↥I →* ↥I) < Y.subgroupOf I := by
    refine (Subgroup.map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp ?_
    rw [hcompe]
    exact hNQe
  exact isMaxParabolicP_of_isSLType_conjBorel e hYI hne x hBlt

theorem isMaxParabolicP_of_isSLType_sylowNormalizer_le {I Y : Subgroup H}
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (hYI : Y ≤ I) (hne : Y ≠ I)
    {U : Subgroup H} (hU : CFSG.ABGLocalTools.IsSylowOf p U I)
    (hN : Subgroup.normalizer (U : Set H) ⊓ I ≤ Y)
    (hNne : Y ≠ Subgroup.normalizer (U : Set H) ⊓ I) :
    IsMaxParabolicP p I Y :=
  isMaxParabolicP_of_isSLType_sylowNormalizer e hYI hne hU
    (lt_of_le_of_ne hN (Ne.symm hNne))

end IsSLType

end CFSG.LocalAnalysis.AGL81I.Section3
