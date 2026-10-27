module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpHat
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferS3
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
open SymplecticHigher (flagStabilizer)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
  (range_le_wSup isQuasisimple_or_perm_three nonempty_mulEquiv_perm_three_of_card_two)

section LeviElements

variable {r : ℕ} {K : Type} [Field K] {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {t : ℕ}

@[expose] noncomputable def cutLevi {b : ℕ} (hb : b ∈ I) :
    GL (Fin (b - spFlagPrev I b)) K →* flagStabilizer r K I :=
  (spFlagCutEmb (spFlagPrev I b) b (hI b hb)).codRestrict _ fun A =>
    spFlagCutEmb_mem hI _ (fun _ hc => le_spFlagPrev_or_le hc) A

@[expose] noncomputable def resLevi (hmax : ∀ c ∈ I, c ≤ t) :
    StatedSp (r - t) K →* flagStabilizer r K I :=
  (spFlagResEmb t).codRestrict _ fun c => spFlagResEmb_mem hI hmax c

theorem cutHom_cutLevi {b : ℕ} (hb : b ∈ I) (A : GL (Fin (b - spFlagPrev I b)) K) :
    spFlagCutHom hI (spFlagPrev_mem I b) hb (cutLevi hI hb A) = A :=
  cutHom_cutEmb hI hb A

theorem cutHom_cutLevi_of_ne {b b' : ℕ} (hb : b ∈ I) (hb' : b' ∈ I) (hne : b' ≠ b)
    (A : GL (Fin (b - spFlagPrev I b)) K) :
    spFlagCutHom hI (spFlagPrev_mem I b') hb' (cutLevi hI hb A) = 1 := by
  have hd : b' ≤ spFlagPrev I b ∨ b ≤ spFlagPrev I b' := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (le_spFlagPrev hb' h)
    · exact Or.inr (le_spFlagPrev hb h)
  exact Units.ext (by
    rw [coe_spFlagCutHom, Units.val_one]
    exact spFlagCutMat_spFlagCutEmb_of_disjoint _ _ hd A)

include hI in
theorem resHom_cutLevi (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t) {b : ℕ} (hb : b ∈ I)
    (A : GL (Fin (b - spFlagPrev I b)) K) :
    spFlagResHom hI htI (cutLevi hI hb A) = 1 := by
  refine mat_injective ?_
  rw [mat_spFlagResHom, map_one]
  exact spFlagResMat_spFlagCutEmb _ (hmax b hb) A

theorem cutHom_resLevi (hmax : ∀ c ∈ I, c ≤ t) {b : ℕ} (hb : b ∈ I) (c : StatedSp (r - t) K) :
    spFlagCutHom hI (spFlagPrev_mem I b) hb (resLevi hI hmax c) = 1 :=
  Units.ext (by
    rw [coe_spFlagCutHom, Units.val_one]
    exact spFlagCutMat_spFlagResEmb _ (hmax b hb) c)

include hI in
theorem resHom_resLevi (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t) (c : StatedSp (r - t) K) :
    spFlagResHom hI htI (resLevi hI hmax c) = c :=
  resHom_resEmb hI htI hmax c

variable (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)

include hI htI hmax in
theorem leviHom_conj_cut {b : ℕ} (hb : b ∈ I) (q : flagStabilizer r K I)
    (A : GL (Fin (b - spFlagPrev I b)) K) :
    spFlagLeviHom hI htI (q * cutLevi hI hb A * q⁻¹) =
      spFlagLeviHom hI htI (cutLevi hI hb (spFlagCutHom hI (spFlagPrev_mem I b) hb q * A *
        (spFlagCutHom hI (spFlagPrev_mem I b) hb q)⁻¹)) := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
  refine leviHom_eq_one_of_blocks hI htI (fun b' hb' => ?_) ?_
  · by_cases hbb : b' = b
    · subst hbb
      simp only [map_mul, map_inv, cutHom_cutLevi]
      group
    · simp only [map_mul, map_inv, cutHom_cutLevi_of_ne hI hb hb' hbb, map_one]
      group
  · simp only [map_mul, map_inv, resHom_cutLevi hI htI hmax hb, map_one]
    group

include hI htI hmax in
theorem leviHom_conj_res (q : flagStabilizer r K I) (c : StatedSp (r - t) K) :
    spFlagLeviHom hI htI (q * resLevi hI hmax c * q⁻¹) =
      spFlagLeviHom hI htI (resLevi hI hmax (spFlagResHom hI htI q * c *
        (spFlagResHom hI htI q)⁻¹)) := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
  refine leviHom_eq_one_of_blocks hI htI (fun b' hb' => ?_) ?_
  · simp only [map_mul, map_inv, cutHom_resLevi hI hmax hb', map_one]
    group
  · simp only [map_mul, map_inv, resHom_resLevi hI htI hmax]
    group

end LeviElements

section ResBlock

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem spResBlock_normal (m : ℕ) : (spResBlock K m).Normal := by
  classical
  unfold spResBlock
  split_ifs
  · infer_instance
  · infer_instance

theorem spResBlock_cases (m : ℕ) :
    Subsingleton ↥(spResBlock K m) ∨ CFSG.Open.IsQuasisimple ↥(spResBlock K m) ∨
      Nonempty (↥(spResBlock K m) ≃* Equiv.Perm (Fin 3)) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · haveI := subsingleton_statedSp_zero (K := K)
    exact Or.inl inferInstance
  by_cases hs : m = 1 ∧ Nat.card K = 2
  · obtain ⟨rfl, hK⟩ := hs
    have hres : spResBlock K 1 = ⊤ := by rw [spResBlock, if_pos ⟨rfl, hK⟩]
    obtain ⟨f⟩ := nonempty_mulEquiv_perm_three_of_card_two hK
    exact Or.inr (Or.inr ⟨(((MulEquiv.subgroupCongr hres).trans Subgroup.topEquiv).trans
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm).trans f⟩)
  have hres : spResBlock K m = commutator (StatedSp m K) := by rw [spResBlock, if_neg hs]
  by_cases h22 : m = 2 ∧ Nat.card K = 2
  · obtain ⟨rfl, hK⟩ := h22
    exact Or.inr (Or.inl (CFSG.Open.IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr hres)
      (spFlag_spFour_comm (K := K) hK).1))
  · have hq := isQuasisimple_statedSp_of_not_small (K := K) hm hs h22
    have htop : spResBlock K m = ⊤ := by rw [hres]; exact hq.1
    exact Or.inr (Or.inl (CFSG.Open.IsQuasisimple.of_mulEquiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) hq))

end ResBlock

section WSup

variable {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {r : ℕ} {K : Type} [Field K]
  [Finite K] [CharP K 2] {I : Set ℕ} (C : SpCover Y P r K I) (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r)
  {t : ℕ} (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t) (hPY : P ≤ Y)

include hI htI hmax hPY in
theorem toHat_range_normal {D : Type} [Group D] (ψ : D →* flagStabilizer r K I)
    (h : ∀ (q : flagStabilizer r K I) (d : D), ∃ d' : D,
      spFlagLeviHom (fun i hi => (hI i hi).2) htI (q * ψ d * q⁻¹) =
        spFlagLeviHom (fun i hi => (hI i hi).2) htI (ψ d')) :
    (C.toHat.comp ψ).range.Normal := by
  refine ⟨?_⟩
  rintro _ ⟨d, rfl⟩ g
  obtain ⟨q, rfl⟩ := C.toHat_surjective hPY g
  obtain ⟨d', hd'⟩ := h q d
  refine ⟨d', ?_⟩
  have hker : q * ψ d * q⁻¹ * (ψ d')⁻¹ ∈ C.toHat.ker := by
    rw [C.ker_toHat hI htI hmax hPY, MonoidHom.mem_ker, map_mul, map_inv, hd', mul_inv_cancel]
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hker
  simp only [MonoidHom.comp_apply, map_mul, map_inv] at hker ⊢
  rw [← hker]

include hI htI hmax hPY in
theorem toHat_cutLevi_mem_wSup {b : ℕ} (hb : b ∈ I)
    (s : Matrix.SpecialLinearGroup (Fin (b - spFlagPrev I b)) K) :
    C.toHat (cutLevi (fun i hi => (hI i hi).2) hb (Matrix.SpecialLinearGroup.toGL s)) ∈
      wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
  have hI₀ : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  by_cases hk : 2 ≤ b - spFlagPrev I b
  · set ψ : Matrix.SpecialLinearGroup (Fin (b - spFlagPrev I b)) K →* flagStabilizer r K I :=
      (cutLevi hI₀ hb).comp Matrix.SpecialLinearGroup.toGL with hψ
    have hnorm : (C.toHat.comp ψ).range.Normal := by
      refine toHat_range_normal C hI htI hmax hPY ψ (fun q s => ?_)
      obtain ⟨s', hs'⟩ := conj_mem_range_toGL (spFlagCutHom hI₀ (spFlagPrev_mem I b) hb q)
        (⟨s, rfl⟩ : Matrix.SpecialLinearGroup.toGL s ∈
          (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup
            (Fin (b - spFlagPrev I b)) K →* GL (Fin (b - spFlagPrev I b)) K).range)
      refine ⟨s', ?_⟩
      simp only [hψ, MonoidHom.comp_apply]
      rw [leviHom_conj_cut hI₀ htI hmax hb q, hs']
    have h := range_le_wSup (CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' (X := ↥P) 2)
      (MonoidHom.id (Matrix.SpecialLinearGroup (Fin (b - spFlagPrev I b)) K))
      Function.surjective_id (C.toHat.comp ψ) (by rw [MonoidHom.ker_id]; exact bot_le) hnorm
      (isQuasisimple_or_perm_three hk (MulEquiv.refl _))
    exact h ⟨s, rfl⟩
  · haveI := subsingleton_specialLinear_of_lt_two (K := K) (m := b - spFlagPrev I b)
      (by omega)
    rw [Subsingleton.elim s 1, map_one, map_one, map_one]
    exact one_mem _

include hI htI hmax hPY in
theorem toHat_resLevi_mem_wSup {c : StatedSp (r - t) K} (hc : c ∈ spResBlock K (r - t)) :
    C.toHat (resLevi (fun i hi => (hI i hi).2) hmax c) ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
  have hI₀ : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  set ψ : ↥(spResBlock K (r - t)) →* flagStabilizer r K I :=
    (resLevi hI₀ hmax).comp (spResBlock K (r - t)).subtype with hψ
  rcases spResBlock_cases (K := K) (r - t) with hsub | hS
  · have h1 : (⟨c, hc⟩ : ↥(spResBlock K (r - t))) = 1 := Subsingleton.elim _ _
    have h2 : c = 1 := congrArg Subtype.val h1
    rw [h2, map_one, map_one]
    exact one_mem _
  · have hnorm : (C.toHat.comp ψ).range.Normal := by
      refine toHat_range_normal C hI htI hmax hPY ψ (fun q d => ?_)
      refine ⟨⟨spFlagResHom hI₀ htI q * (d : StatedSp (r - t) K) * (spFlagResHom hI₀ htI q)⁻¹,
        (spResBlock_normal (K := K) (r - t)).conj_mem _ d.2 _⟩, ?_⟩
      simp only [hψ, MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [leviHom_conj_res hI₀ htI hmax]
    have h := range_le_wSup (CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' (X := ↥P) 2)
      (MonoidHom.id ↥(spResBlock K (r - t))) Function.surjective_id (C.toHat.comp ψ)
      (by rw [MonoidHom.ker_id]; exact bot_le) hnorm hS
    exact h ⟨⟨c, hc⟩, rfl⟩

end WSup

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
