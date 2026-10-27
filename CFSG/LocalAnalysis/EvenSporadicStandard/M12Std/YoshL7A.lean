module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelWord

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

section Bad

variable {G : Type} [Group G] {e : G}
variable {e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12}


set_option linter.unusedSectionVars false

variable {d : G} {α k : ℕ}

theorem cG_isSq (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12) :
    ∃ z : G, z * z = cG e₀ := by
  obtain ⟨z, hz⟩ := isSq_ιH e₀ Jelt_mem_Wsub
  exact ⟨z, by rw [cG_def]; exact hz⟩

theorem ψ_d (E : NEmb e₀ d α k) : ψ E (pw α k [5]) = d := by
  rw [ψ_pw, show swN [5] = [((4 : Fin 9), true)] by decide, val, lift_mk_single, gen5_d]

@[expose] noncomputable def v1G (E : NEmb e₀ d α k) : G := ψ E (pw α k [1, 3])

@[expose] noncomputable def v2G (E : NEmb e₀ d α k) : G := ψ E (pw α k [2, 4])

theorem badReps_isConj_c (D : FusionData α k) (E : NEmb e₀ d α k)
    (hbad : ∀ c ∈ badChains α k, c.1 = [1, 1]) {w' : List (Fin 9 × Bool)}
    (hw' : w' ∈ badReps α k) : IsConj (cG e₀) (val e₀ d α w') := by
  obtain ⟨c, hc, hrun⟩ := List.mem_filterMap.1 hw'
  have h2 := chainRun_sound D E c.2 _ _ hrun
  rw [hbad c hc, show swN [1, 1] = swN cWord from rfl, val_c] at h2
  exact h2

theorem badTabs_isConj_c (D : FusionData α k) (E : NEmb e₀ d α k)
    (hbad : ∀ c ∈ badChains α k, c.1 = [1, 1]) {T : Table} (hT : T ∈ badTabs α k)
    {s : Equiv.Perm (Fin 16)} (hs : Rep 16 T s) :
    ∃ hs' : s ∈ NG α k, IsConj (cG e₀) (E.Ψ ⟨s, hs'⟩) := by
  unfold badTabs at hT
  obtain ⟨w, hw, hTw⟩ := List.mem_flatMap.1 hT
  obtain ⟨hs', hc⟩ := classTabs_conj D E hTw hs
  exact ⟨hs', (badReps_isConj_c D E hbad hw).trans hc⟩

theorem memTab_bad_iff (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    (hbad : ∀ c ∈ badChains α k, c.1 = [1, 1]) {T : Table} {g : Equiv.Perm (Fin 16)}
    (hT : Rep 16 T g) (hg : g ∈ NG α k) :
    memTab 16 (badTabs α k) T = true ↔ IsConj (cG e₀) (E.Ψ ⟨g, hg⟩) := by
  constructor
  · intro h
    obtain ⟨S, hS, s, hr, rfl⟩ := (memTab_iff hT (fun S hS => rep_of_mem_badTabs D hS)).1 h
    obtain ⟨_, hc⟩ := badTabs_isConj_c D E hbad hS hr
    exact hc
  · intro hconj
    have hord : orderOf g = 2 :=
      calc orderOf g = orderOf (⟨g, hg⟩ : ↥(NG α k)) := Subgroup.orderOf_coe ⟨g, hg⟩
        _ = orderOf (E.Ψ ⟨g, hg⟩) := (orderOf_injective E.Ψ E.inj _).symm
        _ = orderOf (cG e₀) := orderOf_isConj hconj
        _ = 2 := orderOf_cG e₀
    obtain ⟨T', hT', hrep'⟩ := (nEnum_spec D.hnC).exists_entry (g := g)
      (by rw [closure_nGens_eq D.hsz]; exact hg)
    have hinv := involOK_of_orderOf (by norm_num) hrep' hord
    obtain ⟨hcov, -⟩ := cover_parts D.hcover
    rcases hcov T' hT' hinv with hgood | hbadT
    · exfalso
      obtain ⟨S, hS, s, hr, rfl⟩ :=
        (memTab_iff hrep' (fun S hS => rep_of_mem_goodTabs D hS)).1 hgood
      obtain ⟨_, hc⟩ := goodTabs_spec D E he2 hS hr
      exact not_isConj_e_of_isSq e₀ he2 (cG_isSq e₀) (hc.trans hconj.symm)
    · obtain ⟨S, hS, s, hr, hsg⟩ :=
        (memTab_iff hrep' (fun S hS => rep_of_mem_badTabs D hS)).1 hbadT
      exact (memTab_iff hT (fun S hS => rep_of_mem_badTabs D hS)).2 ⟨S, hS, s, hr, hsg⟩

end Bad

section A

variable {G : Type} [Group G] {e : G}
variable {e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12}


set_option linter.unusedSectionVars false

variable {d : G} {α k : ℕ}

noncomputable abbrev AG (E : NEmb e₀ d α k) : Subgroup G :=
  img E (tsub (wgens α k aWords))

structure L7A (E : NEmb e₀ d α k) : Prop where
  card : Nat.card (AG E) = 16
  eq : AG E = Subgroup.closure ({cG e₀, v1G E, v2G E, d} : Set G)
  le : AG E ≤ EG E
  comm : ∀ a ∈ AG E, ∀ b ∈ AG E, a * b = b * a
  sq : ∀ a ∈ AG E, a * a = 1
  gens : IsConj (cG e₀) (cG e₀) ∧ IsConj (cG e₀) (v1G E) ∧ IsConj (cG e₀) (v2G E) ∧
    IsConj (cG e₀) d
  cls : ∀ y ∈ EG E, IsConj (cG e₀) y → y ∈ AG E
  hSA : ∀ y ∈ SG E, (∀ a ∈ AG E, ⁅y, a⁆ = 1 ∨ ⁅y, a⁆ = cG e₀) → y ∈ EG E
  hCS : ∀ y ∈ SG E, (∀ a ∈ AG E, y * a = a * y) → y ∈ AG E

theorem l7A_spec (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    (hue : ueCheck α k = true) (hbad : ∀ c ∈ badChains α k, c.1 = [1, 1])
    (h : l7A (badTabs α k) (nwT α k cWord) (wgens α k aWords)
      (tenum (wgens α k eWords)).toList (tenum (wgens α k sWords)).toList = true) :
    L7A E := by
  obtain ⟨hEs, hSs⟩ := ueCheck_enum hue
  have hELe : tsub (wgens α k eWords) ≤ NG α k := tsub_wgens_le D hEs.perm
  have hSLe : tsub (wgens α k sWords) ≤ NG α k := tsub_wgens_le D hSs.perm
  have hrc : Rep 16 (nwT α k cWord) (pw α k cWord) := rep_pw D cWord
  have hpc := pw_mem α k cWord
  have hψc : ψ E (pw α k cWord) = cG e₀ := ψ_c E
  unfold l7A at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hA16, hcomm⟩, hsq⟩, hgE⟩, hgbad⟩, hcls⟩, hSA⟩, hCS⟩ := h
  obtain ⟨hAs, -⟩ := tsub_spec hA16
  have hALe : tsub (wgens α k aWords) ≤ NG α k := tsub_wgens_le D hAs.perm
  have hgenmem : ∀ W ∈ aWords, nwT α k W ∈ wgens α k aWords := fun W hW =>
    mem_wgens.2 ⟨W, hW, rfl⟩
  have hv1 : v1G E = ψ E (pw α k [1, 3]) := rfl
  have hv2 : v2G E = ψ E (pw α k [2, 4]) := rfl
  have hψd : ψ E (pw α k [5]) = d := ψ_d E
  have hAeq : AG E = Subgroup.closure ({cG e₀, v1G E, v2G E, d} : Set G) := by
    have hP : (tp 16 '' {x | x ∈ wgens α k aWords}) ⊆ NG α k := by
      rintro _ ⟨T, hT, rfl⟩
      obtain ⟨W, -, rfl⟩ := mem_wgens.1 hT
      rw [tp_nwT D (hAs.perm _ hT)]
      exact wp_mem α k _
    have hset : ψ E '' (tp 16 '' {x | x ∈ wgens α k aWords}) =
        ({cG e₀, v1G E, v2G E, d} : Set G) := by
      ext y
      constructor
      · rintro ⟨_, ⟨T, hT, rfl⟩, rfl⟩
        obtain ⟨W, hW, rfl⟩ := mem_wgens.1 hT
        rw [tp_nwT D (hAs.perm _ hT)]
        simp only [aWords, List.mem_cons, List.mem_nil_iff, or_false] at hW
        rcases hW with rfl | rfl | rfl | rfl
        · exact Or.inl hψc
        · exact Or.inr (Or.inl hv1.symm)
        · exact Or.inr (Or.inr (Or.inl hv2.symm))
        · exact Or.inr (Or.inr (Or.inr hψd))
      · intro hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact ⟨_, ⟨nwT α k cWord, hgenmem cWord (by simp [aWords]), rfl⟩, by
            rw [tp_nwT D (hAs.perm _ (hgenmem cWord (by simp [aWords])))]; exact hψc⟩
        · exact ⟨_, ⟨nwT α k [1, 3], hgenmem [1, 3] (by simp [aWords]), rfl⟩, by
            rw [tp_nwT D (hAs.perm _ (hgenmem [1, 3] (by simp [aWords])))]; exact hv1.symm⟩
        · exact ⟨_, ⟨nwT α k [2, 4], hgenmem [2, 4] (by simp [aWords]), rfl⟩, by
            rw [tp_nwT D (hAs.perm _ (hgenmem [2, 4] (by simp [aWords])))]; exact hv2.symm⟩
        · exact ⟨_, ⟨nwT α k [5], hgenmem [5] (by simp [aWords]), rfl⟩, by
            rw [tp_nwT D (hAs.perm _ (hgenmem [5] (by simp [aWords])))]; exact hψd⟩
    rw [← hset]
    exact img_closure E hP
  have hconjgen : ∀ W ∈ aWords, IsConj (cG e₀) (ψ E (pw α k W)) := by
    intro W hW
    have hmem := Array.all_eq_true'.1 hgbad _ (hgenmem W hW)
    rw [ψ_of_mem E (pw_mem α k W)]
    exact (memTab_bad_iff D E he2 hbad (rep_pw D W) (pw_mem α k W)).1 hmem
  have hmemE : ∀ W ∈ aWords, ψ E (pw α k W) ∈ EG E := by
    intro W hW
    have hmem := Array.all_eq_true'.1 hgE _ (hgenmem W hW)
    exact (memTab_iff_mem_img E hEs (rep_pw D W) (pw_mem α k W)).1 hmem
  have hle : AG E ≤ EG E := by
    rw [hAeq, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · have := hmemE cWord (by simp [aWords])
      rwa [hψc] at this
    · exact hmemE [1, 3] (by simp [aWords])
    · exact hmemE [2, 4] (by simp [aWords])
    · have := hmemE [5] (by simp [aWords])
      rwa [hψd] at this
  have hcardA : Nat.card (AG E) = 16 := (card_img E hALe).trans (card_tsub hA16)
  refine ⟨hcardA, hAeq, hle, ?_, ?_, ⟨IsConj.refl _, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  ·
    refine forall_mem_img_enum E hAs (φ := fun a => ∀ b ∈ AG E, a * b = b * a) ?_
    intro T hT
    refine forall_mem_img_enum E hAs ?_
    intro T' hT'
    obtain ⟨hrep, hmem⟩ := hAs.rep_mem hT
    obtain ⟨hrep', hmem'⟩ := hAs.rep_mem hT'
    have := hcomm T (Array.mem_toList_iff.2 hT) T' (Array.mem_toList_iff.2 hT')
    exact (commTT_ψ E hrep hrep' (hALe hmem) (hALe hmem')).1 this
  ·
    refine forall_mem_img_enum E hAs ?_
    intro T hT
    obtain ⟨hrep, hmem⟩ := hAs.rep_mem hT
    have := hsq T (Array.mem_toList_iff.2 hT)
    have h2 := (tblEq_ψ E (hrep.compT hrep) (Rep.idT (by norm_num)) ((NG α k).mul_mem (hALe hmem)
      (hALe hmem)) (NG α k).one_mem).1 this
    rw [ψ_one, ψ_mul E (hALe hmem) (hALe hmem)] at h2
    exact h2
  · exact hconjgen [1, 3] (by simp [aWords])
  · exact hconjgen [2, 4] (by simp [aWords])
  · have := hconjgen [5] (by simp [aWords])
    rwa [hψd] at this
  ·
    intro y hy hconj
    obtain ⟨T, hT, rfl, hrepT, hgT⟩ := exists_entry_of_mem_img E hEs hELe hy
    have hbadT : memTab 16 (badTabs α k) T = true := by
      refine (memTab_bad_iff D E he2 hbad hrepT hgT).2 ?_
      rw [← ψ_of_mem E hgT]
      exact hconj
    have h1 := hcls T (Array.mem_toList_iff.2 hT)
    rw [hbadT] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    exact (memTab_iff_mem_img E hAs hrepT hgT).1 h1
  ·
    intro y hy hcomm'
    obtain ⟨T, hT, rfl, hrepT, hgT⟩ := exists_entry_of_mem_img E hSs hSLe hy
    have h1 := hSA T (Array.mem_toList_iff.2 hT)
    have hall : (tenum (wgens α k aWords)).toList.all (commIn 16 (nwT α k cWord) T) = true := by
      rw [List.all_eq_true]
      intro T' hT'
      obtain ⟨hrep', hmem'⟩ := hAs.rep_mem (Array.mem_toList_iff.1 hT')
      have ha := ψ_mem_img_enum E hAs hALe (Array.mem_toList_iff.1 hT')
      have := hcomm' _ ha
      rw [← hψc] at this
      exact (commIn_ψ E hrc hrepT hrep' hpc hgT (hALe hmem')).2 this
    rw [hall] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    exact (memTab_iff_mem_img E hEs hrepT hgT).1 h1
  ·
    intro y hy hcen
    obtain ⟨T, hT, rfl, hrepT, hgT⟩ := exists_entry_of_mem_img E hSs hSLe hy
    have h1 := hCS T (Array.mem_toList_iff.2 hT)
    have hall : (tenum (wgens α k aWords)).toList.all (commTT 16 T) = true := by
      rw [List.all_eq_true]
      intro T' hT'
      obtain ⟨hrep', hmem'⟩ := hAs.rep_mem (Array.mem_toList_iff.1 hT')
      have ha := ψ_mem_img_enum E hAs hALe (Array.mem_toList_iff.1 hT')
      exact (commTT_ψ E hrepT hrep' hgT (hALe hmem')).2 (hcen _ ha)
    rw [hall] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    exact (memTab_iff_mem_img E hAs hrepT hgT).1 h1

end A

section V

variable {G : Type} [Group G] {e : G}
variable {e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12}


set_option linter.unusedSectionVars false

variable {d : G} {α k : ℕ}

theorem l7V_spec (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    (h : l7V (nEnum α k) (wgens α k vWords) = true) {y : G} (hy : y ∈ Nn e₀)
    (hc : y * cG e₀ = cG e₀ * y) (h1 : y * v1G E = v1G E * y) (h2 : y * v2G E = v2G E * y)
    (he : y * e = e * y) : y * y = 1 := by
  obtain ⟨g, hg, rfl⟩ := exists_ψ E hy
  obtain ⟨T, hT, hrep⟩ := (nEnum_spec D.hnC).exists_entry (g := g)
    (by rw [closure_nGens_eq D.hsz]; exact hg)
  unfold l7V at h
  have hb := Array.all_eq_true'.1 h T hT
  have hall : (wgens α k vWords).all (commTT 16 T) = true := by
    rw [Array.all_eq_true']
    intro T' hT'
    obtain ⟨W, hW, rfl⟩ := mem_wgens.1 hT'
    have hr := rep_pw D W
    have hp := pw_mem α k W
    refine (commTT_ψ E hrep hr hg hp).2 ?_
    simp only [vWords, List.mem_cons, List.mem_nil_iff, or_false] at hW
    rcases hW with rfl | rfl | rfl | rfl
    · rw [show ψ E (pw α k cWord) = cG e₀ from ψ_c E]; exact hc
    · exact h1
    · exact h2
    · rw [show ψ E (pw α k [6]) = e from ψ_e E he2]; exact he
  rw [hall] at hb
  simp only [Bool.not_true, Bool.false_or] at hb
  have h3 := (tblEq_idT_ψ E (hrep.compT hrep) ((NG α k).mul_mem hg hg)).1 hb
  rwa [ψ_mul E hg hg] at h3

end V

end CFSG.EvenSporadicStandard.M12Std.Yosh
