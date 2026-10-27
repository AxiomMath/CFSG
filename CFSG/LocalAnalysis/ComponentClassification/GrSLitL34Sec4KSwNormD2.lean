module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormD1
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43H
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNConn
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem false_of_diag
    (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog) {a x : G} {J S A : Subgroup G}
    (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s)
    (hrun : L34Sec4Running J A) (h3 : IsThreeConnected (S ⊓ withKernel J))
    (hZ1 : S ⊓ zStarIn J = ⊥) {W : Subgroup G} (hW : W ≠ ⊥) (hWodd : Odd (Nat.card W))
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G)) {K : Subgroup G}
    (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hKL : IsL34Type (K ⧸ Open.fusionZStar K)) (hKa : conjugate K a ≠ K)
    (hJKK : J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set G))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, hU3, hL34, hmax, hSsyl, haS, -⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := id hbase
  have : IsSimpleGroup G := hsimple
  have ha2 : orderOf a = 2 := hU3.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc, hmax,
    GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  have hCaM : centralizer ({a} : Set G) ≤ M :=
    (GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hgs).trans hNJ
  have haM : a ∈ M := hCaM (mem_centralizer_singleton_iff.mpr rfl)
  set K' : Subgroup G := conjugate K a with hK'
  have hK'M : K' ≤ M := conjugate_le_of_mem hKM haM
  have hK'c : IsPComponent 2 (K'.subgroupOf M) := isPComponent_conjugate_subgroupOf haM hKc
  have hne : K ≠ K' := fun e => hKa e.symm
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have haK : a ∉ normalizer (K : Set G) := fun h => hKa (conjugate_eq_of_mem_normalizer h)
  have hKK' : K ≤ normalizer (K' : Set G) :=
    (GrS5.commutator_le_of_ne hK'M hKM hK'c hKc hne.symm).2
  obtain ⟨T, hTsyl, hST⟩ := GrS4.exists_isSylowTwoIn_le' (hSsyl.1.trans hNJ)
    (GrS4.isPGroup_of_isSylowTwoIn hSsyl)
  have hT2 := GrS4.isPGroup_of_isSylowTwoIn hTsyl
  have hTM := hTsyl.1
  have haT : a ∈ T := hST haS
  set D : Subgroup G := T ⊓ normalizer (K : Set G) ⊓ normalizer (K' : Set G) with hD
  set T₂ : Subgroup G := D ⊔ zpowers a with hT₂
  set R : Subgroup G := T₂ ⊓ coreActionKernel K ⊓ coreActionKernel K' with hR
  have hT₂T : T₂ ≤ T := sup_le (inf_le_left.trans inf_le_left) (zpowers_le.mpr haT)
  have hRT₂ : R ≤ T₂ := inf_le_left.trans inf_le_left
  have haT₂ : a ∈ T₂ := mem_sup_right (mem_zpowers a)
  have hT₂n : T₂ ≤ normalizer (R : Set G) := by
    refine sup_le (fun g hg => ?_) (zpowers_le.mpr ?_)
    · refine GrS4.mem_normalizer_of_map_le_self ?_
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨⟨hyT₂, hyK⟩, hyK'⟩ := And.intro (mem_inf.mp (mem_inf.mp hy).1) (mem_inf.mp hy).2
      have hgT₂ : g ∈ T₂ := mem_sup_left hg
      obtain ⟨⟨-, hgK⟩, hgK'⟩ := And.intro (mem_inf.mp (mem_inf.mp hg).1) (mem_inf.mp hg).2
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨mul_mem (mul_mem hgT₂ hyT₂) (inv_mem hgT₂),
        UnbalancedLayer.conj_mem_coreActionKernel hgK hyK⟩,
        UnbalancedLayer.conj_mem_coreActionKernel hgK' hyK'⟩
    · refine GrS4.mem_normalizer_of_map_le_self ?_
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨⟨hyT₂, hyK⟩, hyK'⟩ := And.intro (mem_inf.mp (mem_inf.mp hy).1) (mem_inf.mp hy).2
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨mul_mem (mul_mem haT₂ hyT₂) (inv_mem haT₂),
        FooteLit.mem_coreActionKernel_conjugate_iff.mp hyK'⟩,
        FooteLit.mem_coreActionKernel_conjugate_iff.mpr ?_⟩
      rwa [show a * (a * y * a⁻¹) * a⁻¹ = a * a * y * (a * a)⁻¹ by group, haa, inv_one,
        one_mul, mul_one]
  have hRbot : R = ⊥ := by
    by_contra hRne
    obtain ⟨s, hsR, hs2, hsc⟩ :=
      GrS4.exists_center_involution_of_normal (hT2.to_le hT₂T) hRT₂ hT₂n hRne
    exact false_of_diag_kernel hMax hS hbase hgs hL34 hNJ hKM hKc hKa hJKK hs2 (hsc a haT₂)
      (mem_inf.mp (mem_inf.mp hsR).1).2 (mem_inf.mp hsR).2
  have hr2 : ∀ m ∈ M, conjugate K m = K ∨ conjugate K m = K' := by
    intro m hm
    by_contra hne2
    push Not at hne2
    obtain ⟨hne1, hne2⟩ := hne2
    have hK₃M := conjugate_le_of_mem hKM hm
    have hK₃c := isPComponent_conjugate_subgroupOf hm hKc
    apply inf_conjugate_ne_bot hKM hKc hTsyl hm
    rw [eq_bot_iff, ← hRbot]
    intro y hy
    obtain ⟨hyT, hyK₃⟩ := mem_inf.mp hy
    have hyK : y ∈ normalizer (K : Set G) :=
      (GrS5.commutator_le_of_ne hKM hK₃M hKc hK₃c (Ne.symm hne1)).2 hyK₃
    have hyK' : y ∈ normalizer (K' : Set G) :=
      (GrS5.commutator_le_of_ne hK'M hK₃M hK'c hK₃c (Ne.symm hne2)).2 hyK₃
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨mem_sup_left (mem_inf.mpr ⟨mem_inf.mpr ⟨hyT, hyK⟩, hyK'⟩),
      HeSN.le_coreActionKernel_of_ne hKM hK₃M hKc hK₃c (Ne.symm hne1) hyK₃⟩,
      HeSN.le_coreActionKernel_of_ne hK'M hK₃M hK'c hK₃c (Ne.symm hne2) hyK₃⟩
  have hTZ : T ⊓ zStarIn K = ⊥ := by
    rw [eq_bot_iff, ← hRbot]
    intro y hy
    obtain ⟨hyT, hyZ⟩ := mem_inf.mp hy
    have hyK : y ∈ K := map_subtype_le _ hyZ
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨mem_sup_left (mem_inf.mpr ⟨mem_inf.mpr ⟨hyT,
      le_normalizer hyK⟩, hKK' hyK⟩), GrS5.zStarIn_le_coreActionKernel K hyZ⟩,
      HeSN.le_coreActionKernel_of_ne hK'M hKM hK'c hKc hne.symm hyK⟩
  have hH1 : ∀ e ∈ T, ∀ e' ∈ T, conjugate K e = K ∨ conjugate K e' = K ∨
      conjugate K e = conjugate K e' := by
    intro e he e' he'
    rcases hr2 e (hTM he) with h1 | h1
    · exact Or.inl h1
    · rcases hr2 e' (hTM he') with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (h1.trans h2.symm))
  have hWT := GrS5S.l34TSylowWStep_of_certs hMax G a x J S A hset hcent
    (fun h => (h hZ1).elim) hrun h3 W hW hWodd hWB hNJ K hKM hKc hKL (Or.inr ⟨hKa, hJKK⟩) T hTsyl
    hST hH1 (Or.inl hTZ)
  obtain ⟨F, hFP, hF, s, hsS, hss, hsF, hsn⟩ := GrS5S.exists_eight_not_isolated hset h3
  obtain ⟨P₀, hP₀⟩ := exists_sylow_of_wT hTsyl hWT (hFP.trans (inf_le_left.trans hST)) hF
    (hST (mem_inf.mp hsS).1) hss hsF hsn
  set M₀ : Subgroup G := M ⊓ normalizer (K : Set G) with hM₀
  have hidx := HeSN.relIndex_eq_two haM haK (by rw [haa]; exact one_mem _) hr2
  have hidx' : (M₀.subgroupOf M).index = 2 := hidx
  have hmul : ∀ x ∈ M, ∀ y ∈ M, (x * y ∈ M₀ ↔ (x ∈ M₀ ↔ y ∈ M₀)) := fun x hx y hy => by
    have h1 := Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
    simpa [mem_subgroupOf] using h1
  have hconj : ∀ m ∈ M, ∀ x ∈ M₀, m * x * m⁻¹ ∈ M₀ := by
    intro m hm x hx
    have hxM := (mem_inf.mp hx).1
    rw [hmul _ (mul_mem hm hxM) _ (inv_mem hm), hmul _ hm _ hxM]
    have h1 := hmul m hm m⁻¹ (inv_mem hm)
    rw [mul_inv_cancel] at h1
    have h2 := h1.mp (one_mem _)
    exact ⟨fun h3 => h2.mp (h3.mpr hx), fun h3 => ⟨fun _ => hx, fun _ => h2.mpr h3⟩⟩
  have haM₀ : a ∉ M₀ := fun h => haK (mem_inf.mp h).2
  have hU : (T ⊓ M₀).relIndex T = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨a, haT, fun b hb => ?_⟩
    have h1 := hmul b (hTM hb) a haM
    simp only [mem_inf, hb, mul_mem hb haT, true_and]
    by_cases hbM : b ∈ M₀
    · exact Or.inr ⟨hbM, fun h2 => haM₀ ((h1.mp h2).mp hbM)⟩
    · exact Or.inl ⟨h1.mpr ⟨fun h2 => absurd h2 hbM, fun h2 => absurd h2 haM₀⟩, hbM⟩
  rcases goldschmidtTransferInput_holds G P₀ a (hP₀ ▸ haT) ha2 with hall | hres
  · obtain ⟨g, hgU, hgext⟩ := hall (T ⊓ M₀) (by rw [hP₀]; exact inf_le_left)
      (by rw [hP₀]; exact hU)
    rw [hP₀] at hgext
    have hFa : F ≤ T ⊓ centralizer ({a} : Set G) := fun y hy =>
      mem_inf.mpr ⟨hST (mem_inf.mp (hFP hy)).1,
        mem_centralizer_singleton_iff.mpr (hcent y (mem_inf.mp (hFP hy)).1)⟩
    have hsa : s ∈ T ⊓ centralizer ({a} : Set G) := mem_inf.mpr ⟨hST (mem_inf.mp hsS).1,
      mem_centralizer_singleton_iff.mpr (hcent s (mem_inf.mp hsS).1)⟩
    obtain ⟨m, hmM, hm⟩ := exists_conj_of_witness hT2 hWT hgext hFa hF hsa hss hsF hsn
    apply haM₀
    have h1 := hconj m hmM _ (mem_inf.mp hgU).2
    rwa [hm, show m * (m⁻¹ * a * m) * m⁻¹ = a by group] at h1
  · exact hres (HeSN.mem_twoResidualOf_top' hnab a)

end CFSG.ComponentClassification.GrSLit.KSw
