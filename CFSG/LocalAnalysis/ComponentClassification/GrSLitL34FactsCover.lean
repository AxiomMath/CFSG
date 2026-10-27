
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverBase
import all CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel
public import CFSG.LieType.Multipliers.L34Upper
public import Certificates.Certificate22201
import all CFSG.LieType.Multipliers.L34

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable Subgroup
open scoped commutatorElement

theorem coverParts : CoverParts := by
  obtain ⟨h, hs⟩ := Certificates.certificate22201
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
    allBelow_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h20, h21, h22, h23, h24, h25, h26⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun e => by simp [e] at h7, h8, h9, h10, ⟨h11, h12⟩, ⟨h13, h14⟩,
    ⟨h15, h16⟩, h17, fun k hk l hl => by simpa using h18 k hk l hl, hs, h20, h21, h22, h23,
    h24, h25, h26⟩

theorem tabRep_letTab (l : Fin 2 × Bool) :
    TabRep (letTab l) (FreeGroup.lift genAB (FreeGroup.mk [l])) := by
  have hinv := coverParts.invs
  obtain ⟨i, b⟩ := l
  rw [lift_genAB_single]
  unfold letTab genAB
  dsimp only
  split_ifs
  · exact tabRep_aS
  · exact invsOK_spec hinv (k := 0) (by decide) tabRep_aS
  · exact tabRep_bS
  · exact invsOK_spec hinv (k := 1) (by decide) tabRep_bS

theorem tabRep_abTab_aux (w : List (Fin 2 × Bool)) {t : Tab}
    {g : Equiv.Perm (Fin 42)} (ht : TabRep t g) :
    TabRep (w.foldl (fun t l => comp 42 t (letTab l)) t) (g * abPerm w) := by
  induction w generalizing t g with
  | nil => simpa [abPerm] using ht
  | cons l w ih =>
    rw [List.foldl_cons]
    have h := ih (ht.comp (tabRep_letTab l))
    rwa [abPerm, ← List.singleton_append, ← FreeGroup.mul_mk, map_mul, ← mul_assoc]

theorem tabRep_abTab (w : List (Fin 2 × Bool)) :
    TabRep (abTab w) (abPerm w) := by
  have h := tabRep_abTab_aux w (TabRep.idTab (n := 42))
  rwa [one_mul] at h

theorem abPerm_eq_one {w : List (Fin 2 × Bool)}
    (h : abTab w = idTab 42) : abPerm w = 1 :=
  ((tabRep_abTab w).eq_iff TabRep.idTab).1 h

theorem lift_genAB_coverWs :
    ∀ r ∈ CFSG.LieType.Multipliers.wordSet coverWs, FreeGroup.lift genAB r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  exact abPerm_eq_one (coverParts.coverWsOK w hw)

@[expose] noncomputable def sigma : Cover →* Equiv.Perm (Fin 42) :=
  PresentedGroup.toGroup lift_genAB_coverWs

theorem sigma_cv (w : List (Fin 2 × Bool)) :
    sigma (cv w) = abPerm w := rfl

theorem range_sigma :
    sigma.range = S := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨c, rfl⟩
    obtain ⟨f, rfl⟩ := PresentedGroup.mk_surjective _ c
    exact lift_genAB_mem_S f
  · rw [S, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · refine ⟨cv (genABWords.getD 0 []), ?_⟩
      rw [sigma_cv]
      exact ((tabRep_abTab _).eq_iff tabRep_g₁).1 coverParts.gen₁
    · refine ⟨cv (genABWords.getD 1 []), ?_⟩
      rw [sigma_cv]
      exact ((tabRep_abTab _).eq_iff tabRep_g₂).1 coverParts.gen₂
    · refine ⟨cv (genABWords.getD 2 []), ?_⟩
      rw [sigma_cv]
      exact ((tabRep_abTab _).eq_iff tabRep_g₃).1 coverParts.gen₃

theorem abPerm_zword (p q r : ℕ) : abPerm (zword p q r) = 1 := by
  have h1 := abPerm_eq_one coverParts.zOne
  have h2 := abPerm_eq_one coverParts.zTwo
  have h3 := abPerm_eq_one coverParts.zThree
  simp only [abPerm, zword, ← FreeGroup.mul_mk, map_mul, mk_wpow, map_pow] at h1 h2 h3 ⊢
  rw [h1, h2, h3, one_pow, one_pow, one_pow, one_mul, one_mul]

theorem cv_spec {s : List (Fin 2 × Bool) × ℕ × ℕ × ℕ}
    (hs : s ∈ coverSpecs) : cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2) :=
  coverParts.specs s hs

section Lift

variable {E Q : Type*} [Group E] [Group Q]

theorem lift_genAB_commWords (i : Fin 2) :
    FreeGroup.lift genAB (FreeGroup.mk (commWords (coverPairs i))) = genAB i := by
  have h := abPerm_eq_one (coverParts.coverWsOK _ (inv_cons_mem_coverWs i))
  rw [abPerm, ← List.singleton_append, ← FreeGroup.mul_mk, map_mul, lift_genAB_single] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  exact (inv_mul_eq_one.mp h).symm

theorem exists_coverLift
    (q : E →* Equiv.Perm (Fin 42)) (hC : q.ker ≤ center E) (y : Fin 2 → E)
    (hy : ∀ i, q (y i) = genAB i) :
    ∃ l : Cover →* E, q.comp l = sigma ∧
      ∀ i, l (PresentedGroup.of i) =
        FreeGroup.lift y (FreeGroup.mk (commWords (coverPairs i))) := by
  set x : Fin 2 → E := fun i => FreeGroup.lift y (FreeGroup.mk (commWords (coverPairs i))) with hxd
  have hqy : q.comp (FreeGroup.lift y) = FreeGroup.lift genAB :=
    FreeGroup.ext_hom _ _ fun i => by rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, hy]
  have hx : ∀ i, q (x i) = genAB i := fun i => by
    rw [hxd, ← MonoidHom.comp_apply, hqy, lift_genAB_commWords]
  have hqx : q.comp (FreeGroup.lift x) = FreeGroup.lift genAB :=
    FreeGroup.ext_hom _ _ fun i => by rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, hx]
  have hcov : ∀ r ∈ coverRelators (CFSG.LieType.Multipliers.wordSet rels)
      (fun i => FreeGroup.mk (commWords (coverPairs i))), FreeGroup.lift x r = 1 := by
    refine lift_coverRelators_eq_one_iff.mpr ⟨fun i r hr => ?_, fun i => ?_⟩
    · have hk : FreeGroup.lift x r ∈ q.ker := by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
        rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hqx]
        exact abPerm_eq_one (coverParts.relsOK w hw)
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hC hk) _)
    · exact eq_of_mem_commutator_of_central q hC _ _ (hqx.trans hqy.symm)
        (mk_commWords_mem_commutator _)
  have hhopf : ∀ r ∈ CFSG.LieType.Multipliers.wordSet L34Upper.hopfWs,
      FreeGroup.lift x r = 1 := by
    rw [L34Upper.hopfWs, ← coverRelators_wordSet]
    exact hcov
  have hall : ∀ r ∈ CFSG.LieType.Multipliers.wordSet coverWs, FreeGroup.lift x r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rcases List.mem_append.mp hw with hw | hw
    · exact hhopf _ (List.mem_map_of_mem hw)
    · have h := congrArg (PresentedGroup.toGroup hhopf) (L34Upper.extraWs_eq_one w hw)
      rw [map_one] at h
      exact h
  refine ⟨PresentedGroup.toGroup hall, PresentedGroup.ext fun i => ?_, fun i =>
    PresentedGroup.toGroup.of hall⟩
  rw [MonoidHom.comp_apply, PresentedGroup.toGroup.of, hx]
  exact (PresentedGroup.toGroup.of _).symm

end Lift

section Kernel

theorem sigma_z₁ : sigma z₁ = 1 :=
  abPerm_eq_one coverParts.zOne

theorem sigma_z₂ : sigma z₂ = 1 :=
  abPerm_eq_one coverParts.zTwo

theorem sigma_z₃ : sigma z₃ = 1 :=
  abPerm_eq_one coverParts.zThree

theorem card_ker_sigma_le :
    Nat.card sigma.ker ≤ 48 := by
  obtain ⟨hfin, hle⟩ := finite_card_cover_le
  have h := Subgroup.card_ker_mul_card_range sigma
  rw [range_sigma, card_S] at h
  omega

theorem range_zHom :
    zHom.range = sigma.ker := by
  have hle : zHom.range ≤ sigma.ker := by
    rintro _ ⟨d, rfl⟩
    rw [MonoidHom.mem_ker, zHom_apply, map_mul, map_mul, map_pow, map_pow, map_pow, sigma_z₁,
      sigma_z₂, sigma_z₃]
    simp
  have : Finite Cover := finite_card_cover_le.1
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [← Nat.card_congr (MonoidHom.ofInjective zHom_injective).toEquiv]
  have hcard : Nat.card Z443 = 48 := by simp
  rw [hcard]
  exact card_ker_sigma_le

theorem ker_sigma_le_center :
    sigma.ker ≤ center Cover := by
  rw [← range_zHom]
  rintro _ ⟨d, rfl⟩
  rw [zHom_apply]
  exact mul_mem (pow_mem z₁_mem_center _) (mul_mem (pow_mem z₂_mem_center _)
    (pow_mem z₃_mem_center _))

end Kernel

section Elements

theorem sigma_tw (k : ℕ) (hk : k < 64) : sigma (cv (tw k)) = wordPerm (tg k) :=
  (tabRep_abTab (tw k)).perm_eq ((coverParts.tw k hk).1 ▸ tabRep_wordTab (tg k))

theorem tg_mem_T0 (k : ℕ) (hk : k < 64) : wordPerm (tg k) ∈ T0 :=
  mem_of_found_enum enumerates_T0 (tabRep_wordTab (tg k)) (coverParts.tw k hk).2

theorem exists_tg {t : Equiv.Perm (Fin 42)} (ht : t ∈ T0) :
    ∃ k < 64, wordPerm (tg k) = t := by
  set ET := (enumBFS 42 (wordTabs wT₀) 64).tabs with hET
  have hsize : ET.size = 64 := parabolicParts.sizeT
  have hpos : ∀ k < 64, ∃ i < 64, TabRep ET[i]! (wordPerm (tg k)) := fun k hk => by
    obtain ⟨i, hi, hr⟩ := enumerates_T0.exists_pos (tg_mem_T0 k hk)
    exact ⟨i, hsize ▸ hi, hr⟩
  choose! f hf hfr using hpos
  let F : Fin 64 → Fin 64 := fun k => ⟨f k, hf k k.2⟩
  have hinj : Function.Injective F := by
    intro k l hkl
    have he : f k = f l := congrArg Fin.val hkl
    have h1 := hfr k k.2
    have h2 := hfr l l.2
    rw [he] at h1
    have heq : wordPerm (tg k) = wordPerm (tg l) := h1.perm_eq h2
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_iff.mpr hne) with h | h
    · exact coverParts.distinct l l.2 k h
        ((tabRep_wordTab _).tab_eq (heq ▸ tabRep_wordTab (tg l))).symm
    · exact coverParts.distinct k k.2 l h
        ((tabRep_wordTab _).tab_eq (heq ▸ tabRep_wordTab (tg l)))
  obtain ⟨i, hi, hrep⟩ := enumerates_T0.exists_pos ht
  obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨i, hsize ▸ hi⟩
  refine ⟨k, k.2, ?_⟩
  have h1 := hfr k k.2
  have : f k = i := congrArg Fin.val hk
  rw [this] at h1
  exact h1.perm_eq hrep

end Elements

section Specs

theorem sq_spec {d : ℕ × ℕ × ℕ × ℕ} (hd : d ∈ sqData) :
    cv (tw d.1) ^ 2 = z₁ ^ (2 * d.2.1) * z₂ ^ (2 * d.2.2.1) * z₃ ^ d.2.2.2 := by
  have hs : (wpow (tw d.1) 2, 2 * d.2.1, 2 * d.2.2.1, d.2.2.2) ∈ coverSpecs := by
    unfold coverSpecs
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem hd)))))
  have h := cv_spec hs
  rw [cv_wpow, cv_zword] at h
  exact h

theorem comm_spec {d : ℕ × ℕ × ℕ × ℕ × ℕ} (hd : d ∈ commData) :
    cv (tw d.1) * cv (tw d.2.1) * (cv (tw d.1))⁻¹ * (cv (tw d.2.1))⁻¹ =
      z₁ ^ d.2.2.1 * z₂ ^ d.2.2.2.1 * z₃ ^ d.2.2.2.2 := by
  have hs : (commWord (tw d.1) (tw d.2.1), d.2.2.1, d.2.2.2.1, d.2.2.2.2) ∈ coverSpecs := by
    unfold coverSpecs
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem hd))))
  have h := cv_spec hs
  rw [commWord, cv_append, cv_append, cv_append, cv_invRev, cv_invRev, cv_zword] at h
  exact h

theorem unit_spec {d : ℕ × ℕ × ℕ × ℕ} (hd : d ∈ unitData) :
    (cv (tw d.1))⁻¹ * cv (alphaU (tw d.1)) = z₁ ^ d.2.1 * z₂ ^ d.2.2.1 * z₃ ^ d.2.2.2 := by
  have hs : (FreeGroup.invRev (tw d.1) ++ alphaU (tw d.1), d.2.1, d.2.2.1, d.2.2.2) ∈
      coverSpecs := by
    unfold coverSpecs
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr (List.mem_map_of_mem hd)))
  have h := cv_spec hs
  rw [cv_append, cv_invRev, cv_zword] at h
  exact h

theorem fourth_spec {d : List ℕ × ℕ × ℕ × ℕ} (hd : d ∈ fourthData) :
    cv (twl d.1) ^ 4 = z₁ ^ d.2.1 * z₂ ^ d.2.2.1 * z₃ ^ d.2.2.2 := by
  have hs : (wpow (twl d.1) 4, d.2.1, d.2.2.1, d.2.2.2) ∈ coverSpecs := by
    unfold coverSpecs
    simp only [List.mem_append]
    exact Or.inl (Or.inr (List.mem_map_of_mem hd))
  have h := cv_spec hs
  rw [cv_wpow, cv_zword] at h
  exact h

theorem alphaU_z_spec : cv (alphaU zOne ++ zOne) = 1 ∧ cv (alphaU zTwo ++ zTwo) = 1 := by
  have h1 := cv_spec (s := (alphaU zOne ++ zOne, 0, 0, 0)) (by unfold coverSpecs; simp)
  have h2 := cv_spec (s := (alphaU zTwo ++ zTwo, 0, 0, 0)) (by unfold coverSpecs; simp)
  rw [cv_zword] at h1 h2
  simp only [pow_zero, mul_one] at h1 h2
  exact ⟨h1, h2⟩

end Specs

end CFSG.ComponentClassification.GrSLit.L34Facts
