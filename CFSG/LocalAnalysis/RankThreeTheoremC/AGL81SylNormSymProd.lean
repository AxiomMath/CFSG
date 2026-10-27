module

public import CFSG.Permutation.SylowTwoNormalizer.ProdAut
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Fac
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteen
public import CFSG.HardMathSupport.Cooperstein.Proving.QuotientPCoreRigid
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SylNormReduce
public import CFSG.Permutation.SylowTwoNormalizer.Aut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup Equiv

theorem alternatingGroup_prod_bot_le_wSup {k l : ℕ} (hk : 5 ≤ k) :
    (alternatingGroup (Fin k)).prod (⊥ : Subgroup (Perm (Fin l))) ≤
      wSup (Perm (Fin k) × Perm (Fin l)) := by
  haveI : (alternatingGroup (Fin k)).Normal := alternatingGroup.normal
  refine le_wSup_of_normal_of_isQuasisimple (Subgroup.prod_normal _ _) ?_
  have hAq : CFSG.IsQuasisimple ↥(alternatingGroup (Fin k)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
        (CFSG.CGT.PushingUpLit.BHS.isQuasisimple_alternatingGroup hk))
  exact CFSG.IsQuasisimple.of_mulEquiv
    ((Subgroup.prodEquiv (alternatingGroup (Fin k)) (⊥ : Subgroup (Perm (Fin l)))).trans
      MulEquiv.prodUnique) hAq

theorem bot_prod_alternatingGroup_le_wSup {k l : ℕ} (hl : 5 ≤ l) :
    ((⊥ : Subgroup (Perm (Fin k))).prod (alternatingGroup (Fin l))) ≤
      wSup (Perm (Fin k) × Perm (Fin l)) := by
  haveI : (alternatingGroup (Fin l)).Normal := alternatingGroup.normal
  refine le_wSup_of_normal_of_isQuasisimple (Subgroup.prod_normal _ _) ?_
  have hAq : CFSG.IsQuasisimple ↥(alternatingGroup (Fin l)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
        (CFSG.CGT.PushingUpLit.BHS.isQuasisimple_alternatingGroup hl))
  exact CFSG.IsQuasisimple.of_mulEquiv
    ((Subgroup.prodEquiv (⊥ : Subgroup (Perm (Fin k))) (alternatingGroup (Fin l))).trans
      MulEquiv.uniqueProd) hAq

theorem perm_three_prod_bot_le_wSup {l : ℕ} :
    (⊤ : Subgroup (Perm (Fin 3))).prod (⊥ : Subgroup (Perm (Fin l))) ≤
      wSup (Perm (Fin 3) × Perm (Fin l)) :=
  le_wSup_of_normal_of_mulEquiv (Subgroup.prod_normal _ _)
    ((Subgroup.prodEquiv (⊤ : Subgroup (Perm (Fin 3))) (⊥ : Subgroup (Perm (Fin l)))).trans
      (MulEquiv.prodUnique.trans Subgroup.topEquiv))

theorem bot_prod_perm_three_le_wSup {k : ℕ} :
    ((⊥ : Subgroup (Perm (Fin k))).prod (⊤ : Subgroup (Perm (Fin 3)))) ≤
      wSup (Perm (Fin k) × Perm (Fin 3)) :=
  le_wSup_of_normal_of_mulEquiv (Subgroup.prod_normal _ _)
    ((Subgroup.prodEquiv (⊥ : Subgroup (Perm (Fin k))) (⊤ : Subgroup (Perm (Fin 3)))).trans
      (MulEquiv.uniqueProd.trans Subgroup.topEquiv))

open CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8 in
theorem map_prod_bot_eq {k l : ℕ} (α : MulAut (Perm (Fin k) × Perm (Fin l)))
    (α₁ : MulAut (Perm (Fin k))) (α₂ : MulAut (Perm (Fin l)))
    (hα : ∀ x y, α (x, y) = (α₁ x, α₂ y)) (E : Subgroup (Perm (Fin k))) :
    (E.prod (⊥ : Subgroup (Perm (Fin l)))).map α.toMonoidHom =
      (E.map α₁.toMonoidHom).prod ⊥ := by
  have hcomp : α.toMonoidHom.comp (MonoidHom.inl (Perm (Fin k)) (Perm (Fin l))) =
      (MonoidHom.inl (Perm (Fin k)) (Perm (Fin l))).comp α₁.toMonoidHom := by
    refine MonoidHom.ext fun x => ?_
    simp [hα x 1]
  rw [← map_inl_eq_prod_bot E, Subgroup.map_map,
    ← map_inl_eq_prod_bot (E.map α₁.toMonoidHom), Subgroup.map_map, hcomp]

open CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8 in
theorem map_bot_prod_eq {k l : ℕ} (α : MulAut (Perm (Fin k) × Perm (Fin l)))
    (α₁ : MulAut (Perm (Fin k))) (α₂ : MulAut (Perm (Fin l)))
    (hα : ∀ x y, α (x, y) = (α₁ x, α₂ y)) (E : Subgroup (Perm (Fin l))) :
    ((⊥ : Subgroup (Perm (Fin k))).prod E).map α.toMonoidHom =
      (⊥ : Subgroup (Perm (Fin k))).prod (E.map α₂.toMonoidHom) := by
  have hcomp : α.toMonoidHom.comp (MonoidHom.inr (Perm (Fin k)) (Perm (Fin l))) =
      (MonoidHom.inr (Perm (Fin k)) (Perm (Fin l))).comp α₂.toMonoidHom := by
    refine MonoidHom.ext fun y => ?_
    simp [hα 1 y]
  rw [← map_inr_eq_bot_prod E, Subgroup.map_map,
    ← map_inr_eq_bot_prod (E.map α₂.toMonoidHom), Subgroup.map_map, hcomp]

theorem exists_sylow_in_factor {Q K : Type} [Group Q] [Finite Q] [Group K] (α : MulAut Q)
    {S : Subgroup Q} (hSW : S ≤ wSup Q) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex (wSup Q)) (hαS : S.map α.toMonoidHom = S)
    {E : Subgroup K} (ι : K →* Q) (π : Q →* K) (hι : Function.Injective ι)
    (hπ : π.comp ι = MonoidHom.id K) (hDn : (E.map ι).Normal)
    (hDW : E.map ι ≤ wSup Q) (hDα : (E.map ι).map α.toMonoidHom = E.map ι)
    (α₁ : MulAut K) (hα₁ : ∀ x : K, α (ι x) = ι (α₁ x)) :
    ∃ U₁ : Subgroup K, U₁ ≤ E ∧ IsPGroup 2 U₁ ∧ ¬ 2 ∣ U₁.relIndex E ∧
      U₁.map α₁.toMonoidHom = U₁ := by
  classical
  have hπι : ∀ x : K, π (ι x) = x := fun x => by simpa using congrArg (fun f : K →* K => f x) hπ
  have hfix : ∀ q ∈ E.map ι, ι (π q) = q := by
    intro q hq
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hq
    simpa using congrArg ι (hπι e)
  have hDn' : S ≤ Subgroup.normalizer (E.map ι : Set Q) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hUi : ¬ 2 ∣ (S ⊓ E.map ι).relIndex (E.map ι) :=
    CFSG.Quasithin.not_two_dvd_relIndex_inf_of_normalizer hSW hDW hSi hDn'
  have hUmap : (S ⊓ E.map ι).map α.toMonoidHom = S ⊓ E.map ι := by
    rw [Subgroup.map_inf_eq _ _ _ α.injective, hαS, hDα]
  have hfixS : ∀ q ∈ S ⊓ E.map ι, ι (π q) = q := fun q hq => hfix q hq.2
  have hproj : ((S ⊓ E.map ι).map π).map ι = S ⊓ E.map ι := by
    ext q
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
      rw [hfixS v hv]
      exact hv
    · intro hq
      exact ⟨π q, Subgroup.mem_map.mpr ⟨q, hq, rfl⟩, hfixS q hq⟩
  refine ⟨(S ⊓ E.map ι).map π, ?_, ?_, ?_, ?_⟩
  · calc (S ⊓ E.map ι).map π ≤ (E.map ι).map π := Subgroup.map_mono inf_le_right
      _ = E := by
        ext x
        constructor
        · rintro ⟨q, hq, rfl⟩
          obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hq
          rwa [hπι e]
        · intro hx
          exact ⟨ι x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, hπι x⟩
  · exact (hS.to_le inf_le_left).map π
  · rw [← Subgroup.relIndex_map_map_of_injective ((S ⊓ E.map ι).map π) E hι, hproj]
    exact hUi
  ·
    have hLHS : (S ⊓ E.map ι).map ((ι.comp α₁.toMonoidHom).comp π) = S ⊓ E.map ι := by
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : ι (α₁ (π x)) = α x := by rw [← hα₁ (π x), hfixS x hx]
        change ι (α₁ (π x)) ∈ S ⊓ E.map ι
        rw [hx', ← hUmap]
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      · intro hq
        have hq' : q ∈ (S ⊓ E.map ι).map α.toMonoidHom := by rw [hUmap]; exact hq
        obtain ⟨q', hq'D, hq'eq⟩ := Subgroup.mem_map.mp hq'
        exact ⟨q', hq'D, by
          change ι (α₁ (π q')) = q
          rw [← hα₁ (π q'), hfixS q' hq'D]
          exact hq'eq⟩
    have hRHS : (S ⊓ E.map ι).map (ι.comp π) = S ⊓ E.map ι := by
      rw [← Subgroup.map_map, hproj]
    have hgoal : (((S ⊓ E.map ι).map π).map α₁.toMonoidHom).map ι =
        ((S ⊓ E.map ι).map π).map ι := by
      rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map, hLHS, hRHS]
    exact Subgroup.map_injective hι hgoal

open CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8 in
theorem mulAut_fst_eq_one_or_of_wSup {r m : ℕ} (hr2 : r ≠ 2) (hr4 : r ≠ 4)
    (α : MulAut (Perm (Fin r) × Perm (Fin m))) (α₁ : MulAut (Perm (Fin r)))
    (α₂ : MulAut (Perm (Fin m))) (hα : ∀ x y, α (x, y) = (α₁ x, α₂ y))
    (hα₁ : Odd (orderOf α₁)) {S : Subgroup (Perm (Fin r) × Perm (Fin m))}
    (hSW : S ≤ wSup (Perm (Fin r) × Perm (Fin m))) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex (wSup (Perm (Fin r) × Perm (Fin m))))
    (hαS : S.map α.toMonoidHom = S) :
    α₁ = 1 ∨ (r = 5 ∧ 3 ∣ orderOf α₁) := by
  classical
  have hι : Function.Injective (MonoidHom.inl (Perm (Fin r)) (Perm (Fin m))) :=
    fun a b h => by simpa using h
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  ·
    have hr1 : r ≤ 1 := by omega
    haveI : Subsingleton (Fin r) := Fintype.card_le_one_iff_subsingleton.mp (by simpa using hr1)
    exact Or.inl (Subsingleton.elim α₁ 1)
  · rcases Nat.lt_or_ge r 5 with hr5 | hr5
    ·
      obtain rfl : r = 3 := by omega
      have hDn : ((⊤ : Subgroup (Perm (Fin 3))).map
          (MonoidHom.inl (Perm (Fin 3)) (Perm (Fin m)))).Normal := by
        rw [map_inl_eq_prod_bot]
        exact Subgroup.prod_normal _ _
      have hDW : (⊤ : Subgroup (Perm (Fin 3))).map
            (MonoidHom.inl (Perm (Fin 3)) (Perm (Fin m))) ≤
          wSup (Perm (Fin 3) × Perm (Fin m)) := by
        rw [map_inl_eq_prod_bot]
        exact perm_three_prod_bot_le_wSup
      have hDα : ((⊤ : Subgroup (Perm (Fin 3))).map
            (MonoidHom.inl (Perm (Fin 3)) (Perm (Fin m)))).map α.toMonoidHom =
          (⊤ : Subgroup (Perm (Fin 3))).map (MonoidHom.inl (Perm (Fin 3)) (Perm (Fin m))) := by
        rw [map_inl_eq_prod_bot]
        rw [map_prod_bot_eq α α₁ α₂ hα ⊤, Subgroup.map_top_of_surjective _ α₁.surjective]
      obtain ⟨U₁, -, hU2, hUi, hUmap⟩ :=
        exists_sylow_in_factor (E := ⊤) α hSW hS hSi hαS (MonoidHom.inl _ _)
          (MonoidHom.fst _ _) hι MonoidHom.fst_comp_inl hDn hDW hDα α₁
          (fun x => by simp [hα x 1])
      have hUi' : ¬ 2 ∣ U₁.index := by
        simpa [Subgroup.relIndex_top_right] using hUi
      exact Or.inl
        (CFSG.Permutation.SylowTwoNormalizer.mulAut_perm_three_eq_one α₁ hα₁ hU2 hUi' hUmap)
    ·
      haveI : (alternatingGroup (Fin r)).Normal := alternatingGroup.normal
      have hDn : ((alternatingGroup (Fin r)).map
          (MonoidHom.inl (Perm (Fin r)) (Perm (Fin m)))).Normal := by
        rw [map_inl_eq_prod_bot]
        exact Subgroup.prod_normal _ _
      have hDW : (alternatingGroup (Fin r)).map
            (MonoidHom.inl (Perm (Fin r)) (Perm (Fin m))) ≤
          wSup (Perm (Fin r) × Perm (Fin m)) := by
        rw [map_inl_eq_prod_bot]
        exact alternatingGroup_prod_bot_le_wSup hr5
      have hfix : (alternatingGroup (Fin r)).map α₁.toMonoidHom = alternatingGroup (Fin r) :=
        Subgroup.characteristic_iff_map_eq.mp instCharacteristicPermAlternatingGroup α₁
      have hDα : ((alternatingGroup (Fin r)).map
            (MonoidHom.inl (Perm (Fin r)) (Perm (Fin m)))).map α.toMonoidHom =
          (alternatingGroup (Fin r)).map (MonoidHom.inl (Perm (Fin r)) (Perm (Fin m))) := by
        rw [map_inl_eq_prod_bot]
        rw [map_prod_bot_eq α α₁ α₂ hα (alternatingGroup (Fin r)), hfix]
      obtain ⟨U₁, hUE, hU2, hUi, hUmap⟩ :=
        exists_sylow_in_factor (E := alternatingGroup (Fin r)) α hSW hS hSi hαS
          (MonoidHom.inl _ _) (MonoidHom.fst _ _) hι MonoidHom.fst_comp_inl hDn hDW hDα α₁
          (fun x => by simp [hα x 1])
      exact CFSG.Permutation.SylowTwoNormalizer.mulAut_perm_eq_one_or hr5 α₁ hα₁ hUE hU2 hUi hUmap

open CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8 in
theorem mulAut_snd_eq_one_or_of_wSup {r m : ℕ} (hm2 : m ≠ 2) (hm4 : m ≠ 4)
    (α : MulAut (Perm (Fin r) × Perm (Fin m))) (α₁ : MulAut (Perm (Fin r)))
    (α₂ : MulAut (Perm (Fin m))) (hα : ∀ x y, α (x, y) = (α₁ x, α₂ y))
    (hα₂ : Odd (orderOf α₂)) {S : Subgroup (Perm (Fin r) × Perm (Fin m))}
    (hSW : S ≤ wSup (Perm (Fin r) × Perm (Fin m))) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex (wSup (Perm (Fin r) × Perm (Fin m))))
    (hαS : S.map α.toMonoidHom = S) :
    α₂ = 1 ∨ (m = 5 ∧ 3 ∣ orderOf α₂) := by
  classical
  have hι : Function.Injective (MonoidHom.inr (Perm (Fin r)) (Perm (Fin m))) :=
    fun a b h => by simpa using h
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  ·
    have hm1 : m ≤ 1 := by omega
    haveI : Subsingleton (Fin m) := Fintype.card_le_one_iff_subsingleton.mp (by simpa using hm1)
    exact Or.inl (Subsingleton.elim α₂ 1)
  · rcases Nat.lt_or_ge m 5 with hm5 | hm5
    ·
      obtain rfl : m = 3 := by omega
      have hDn : ((⊤ : Subgroup (Perm (Fin 3))).map
          (MonoidHom.inr (Perm (Fin r)) (Perm (Fin 3)))).Normal := by
        rw [map_inr_eq_bot_prod]
        exact Subgroup.prod_normal _ _
      have hDW : (⊤ : Subgroup (Perm (Fin 3))).map
            (MonoidHom.inr (Perm (Fin r)) (Perm (Fin 3))) ≤
          wSup (Perm (Fin r) × Perm (Fin 3)) := by
        rw [map_inr_eq_bot_prod]
        exact bot_prod_perm_three_le_wSup
      have hDα : ((⊤ : Subgroup (Perm (Fin 3))).map
            (MonoidHom.inr (Perm (Fin r)) (Perm (Fin 3)))).map α.toMonoidHom =
          (⊤ : Subgroup (Perm (Fin 3))).map (MonoidHom.inr (Perm (Fin r)) (Perm (Fin 3))) := by
        rw [map_inr_eq_bot_prod]
        rw [map_bot_prod_eq α α₁ α₂ hα ⊤, Subgroup.map_top_of_surjective _ α₂.surjective]
      obtain ⟨U₁, -, hU2, hUi, hUmap⟩ :=
        exists_sylow_in_factor (E := ⊤) α hSW hS hSi hαS (MonoidHom.inr _ _)
          (MonoidHom.snd _ _) hι MonoidHom.snd_comp_inr hDn hDW hDα α₂
          (fun x => by simp [hα 1 x])
      have hUi' : ¬ 2 ∣ U₁.index := by
        simpa [Subgroup.relIndex_top_right] using hUi
      exact Or.inl
        (CFSG.Permutation.SylowTwoNormalizer.mulAut_perm_three_eq_one α₂ hα₂ hU2 hUi' hUmap)
    ·
      haveI : (alternatingGroup (Fin m)).Normal := alternatingGroup.normal
      have hDn : ((alternatingGroup (Fin m)).map
          (MonoidHom.inr (Perm (Fin r)) (Perm (Fin m)))).Normal := by
        rw [map_inr_eq_bot_prod]
        exact Subgroup.prod_normal _ _
      have hDW : (alternatingGroup (Fin m)).map
            (MonoidHom.inr (Perm (Fin r)) (Perm (Fin m))) ≤
          wSup (Perm (Fin r) × Perm (Fin m)) := by
        rw [map_inr_eq_bot_prod]
        exact bot_prod_alternatingGroup_le_wSup hm5
      have hfix : (alternatingGroup (Fin m)).map α₂.toMonoidHom = alternatingGroup (Fin m) :=
        Subgroup.characteristic_iff_map_eq.mp instCharacteristicPermAlternatingGroup α₂
      have hDα : ((alternatingGroup (Fin m)).map
            (MonoidHom.inr (Perm (Fin r)) (Perm (Fin m)))).map α.toMonoidHom =
          (alternatingGroup (Fin m)).map (MonoidHom.inr (Perm (Fin r)) (Perm (Fin m))) := by
        rw [map_inr_eq_bot_prod]
        rw [map_bot_prod_eq α α₁ α₂ hα (alternatingGroup (Fin m)), hfix]
      obtain ⟨U₁, hUE, hU2, hUi, hUmap⟩ :=
        exists_sylow_in_factor (E := alternatingGroup (Fin m)) α hSW hS hSi hαS
          (MonoidHom.inr _ _) (MonoidHom.snd _ _) hι MonoidHom.snd_comp_inr hDn hDW hDα α₂
          (fun x => by simp [hα 1 x])
      exact CFSG.Permutation.SylowTwoNormalizer.mulAut_perm_eq_one_or hm5 α₂ hα₂ hUE hU2 hUi hUmap

theorem mulAut_prod_eq_one_of_wSup {r m : ℕ}
    (h2 : CFSG.pCore 2 (Perm (Fin r) × Perm (Fin m)) = ⊥)
    (α : MulAut (Perm (Fin r) × Perm (Fin m))) (hα : Odd (orderOf α))
    {S : Subgroup (Perm (Fin r) × Perm (Fin m))}
    (hSW : S ≤ wSup (Perm (Fin r) × Perm (Fin m))) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex (wSup (Perm (Fin r) × Perm (Fin m))))
    (hαS : S.map α.toMonoidHom = S) :
    α = 1 ∨ ((r = 5 ∨ m = 5) ∧ 3 ∣ orderOf α) := by
  classical
  have hcomm : CFSG.pCore 2 (Perm (Fin m) × Perm (Fin r)) = ⊥ := by
    have h := CFSG.pCore_map_iso 2 (MulEquiv.prodComm :
      Perm (Fin r) × Perm (Fin m) ≃* Perm (Fin m) × Perm (Fin r))
    rw [h2, Subgroup.map_bot] at h
    exact h.symm
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact CFSG.HardMathSupport.Cooperstein.Proving.pCore_two_perm_prod_ne_bot
      (s := m) (Or.inl rfl) h2
  have hr4 : r ≠ 4 := by
    rintro rfl
    exact CFSG.HardMathSupport.Cooperstein.Proving.pCore_two_perm_prod_ne_bot
      (s := m) (Or.inr rfl) h2
  have hm2 : m ≠ 2 := by
    rintro rfl
    exact CFSG.HardMathSupport.Cooperstein.Proving.pCore_two_perm_prod_ne_bot
      (r := 2) (s := r) (Or.inl rfl) hcomm
  have hm4 : m ≠ 4 := by
    rintro rfl
    exact CFSG.HardMathSupport.Cooperstein.Proving.pCore_two_perm_prod_ne_bot
      (r := 4) (s := r) (Or.inr rfl) hcomm
  obtain ⟨α₁, α₂, hαprod, hdvd1, hdvd2⟩ :=
    CFSG.Permutation.SylowTwoNormalizer.exists_mulAut_eq_prod hr2 hr4 hm2 hm4 α hα
  have hodd1 : Odd (orderOf α₁) := Odd.of_dvd_nat hα hdvd1
  have hodd2 : Odd (orderOf α₂) := Odd.of_dvd_nat hα hdvd2
  have h1 := mulAut_fst_eq_one_or_of_wSup hr2 hr4 α α₁ α₂ hαprod hodd1 hSW hS hSi hαS
  have h2' := mulAut_snd_eq_one_or_of_wSup hm2 hm4 α α₁ α₂ hαprod hodd2 hSW hS hSi hαS
  rcases h1 with h1 | ⟨hr5, h3r⟩
  · rcases h2' with h2'' | ⟨hm5, h3m⟩
    · left
      refine MulEquiv.ext fun x => ?_
      obtain ⟨a, b⟩ := x
      have h := hαprod a b
      rw [h1, h2''] at h
      simpa using h
    · exact Or.inr ⟨Or.inr hm5, Nat.dvd_trans h3m hdvd2⟩
  · exact Or.inr ⟨Or.inl hr5, Nat.dvd_trans h3r hdvd1⟩

theorem kFactSylNormSymProd : KFactSylNormSymProd := by
  intro A _ _ P b r m he hb hW
  obtain ⟨e⟩ := he
  obtain ⟨α, hαdvd, -, ⟨S, hSW, hS2, hSi, hαS⟩, w, -, hαw⟩ :=
    exists_mulAut_of_sylAct (Q := Perm (Fin r) × Perm (Fin m)) e hb hW
  have hodd : Odd (orderOf α) := Odd.of_dvd_nat hb.1 hαdvd
  have h2 : CFSG.pCore 2 (Perm (Fin r) × Perm (Fin m)) = ⊥ := pCore_two_eq_bot_of_mulEquiv e
  have hne : α ≠ 1 := by
    intro h
    rw [h] at hαw
    exact hαw rfl
  rcases mulAut_prod_eq_one_of_wSup h2 α hodd hSW hS2 hSi hαS with h | ⟨hr5, h3⟩
  · exact absurd h hne
  · exact ⟨Nat.dvd_trans h3 hαdvd, hr5⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
