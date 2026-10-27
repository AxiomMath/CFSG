module

public import CFSG.CGT.T75JM.M22PDInputs
public import CFSG.CGT.T75JM.M22PresTables
public import Certificates.Certificate14984
public import CFSG.Certificates.CosetTableColumns

public section

namespace CFSG.CGT.T75JM

open CFSG.CosetTable CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

abbrev m22PDPresented : Type := PG 7 m22RelsPD

abbrev m22RelsPD6 : List (List (Fin 6 × Bool)) :=
  restrictWords (subsetOf 7 [0, 1, 2, 3, 4, 5]) m22RelsPD

theorem rels6_subset_m22RelsPD6 : ∀ r ∈ rels6, r ∈ m22RelsPD6 := by
  decide +kernel

theorem pRels_eq_m22RelsP : pRels = m22RelsP := by
  decide +kernel

theorem m22PD6_card_le :
    Finite (PG 6 m22RelsPD6) ∧ Nat.card (PG 6 m22RelsPD6) ≤ 5760 := by
  obtain ⟨hfin, hle⟩ := Certificates.certificate14984.2.2.1
  let f : PG 6 rels6 →* PG 6 m22RelsPD6 :=
    PresentedGroup.toGroup (f := PresentedGroup.of) fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
      have h1 : FreeGroup.lift (PresentedGroup.of : Fin 6 → PG 6 m22RelsPD6) (FreeGroup.mk w) =
          PresentedGroup.mk _ (FreeGroup.mk w) := by
        have : (FreeGroup.lift (PresentedGroup.of : Fin 6 → PG 6 m22RelsPD6)) =
            PresentedGroup.mk _ := by
          apply FreeGroup.ext_hom
          intro i
          rw [FreeGroup.lift_apply_of]
          rfl
        rw [this]
      rw [h1]
      exact PresentedGroup.one_of_mem (List.mem_map.2 ⟨w, rels6_subset_m22RelsPD6 w hw, rfl⟩)
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
      Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩
  have := hfin
  exact ⟨Finite.of_surjective f hsurj, (Nat.card_le_card_of_surjective f hsurj).trans hle⟩

@[expose] abbrev M22PDIndex : Prop :=
  (genSub {r : FreeGroup (Fin 7) | r ∈ m22RelsPD.map FreeGroup.mk}
      (subsetOf 7 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 7) | r ∈ m22RelsPD.map FreeGroup.mk}
      (subsetOf 7 [0, 1, 2, 3, 4, 5])).index ≤ 77

theorem m22PDPresented_card_le (h : M22PDIndex) :
    Finite m22PDPresented ∧ Nat.card m22PDPresented ≤ 443520 := by
  obtain ⟨hfin6, hle6⟩ := m22PD6_card_le
  have : Finite (PG (subsetOf 7 [0, 1, 2, 3, 4, 5]).length
      (restrictWords (subsetOf 7 [0, 1, 2, 3, 4, 5]) m22RelsPD)) := hfin6
  obtain ⟨hfin, hc⟩ := card_le_of_genSub_index m22RelsPD (subsetOf 7 [0, 1, 2, 3, 4, 5]) h.1 h.2
  refine ⟨hfin, hc.trans ?_⟩
  have h2 := Nat.mul_le_mul_left 77 hle6
  exact h2.trans (by norm_num)

theorem thetaTab_facts (h : thetaTabCheck = true) :
    ∀ r ∈ thetaRels, wordT 22 m22L (r.map m22LetterZ) = idT 22 := by
  unfold thetaTabCheck at h
  simp only [List.all_eq_true, beq_iff_eq] at h
  exact h

theorem lift_m22Gen_eq_one_PD (h : m22TabCheck = true) (hθ : thetaTabCheck = true)
    {w : List (Fin 7 × Bool)} (hw : w ∈ m22RelsPD) :
    FreeGroup.lift m22Gen (FreeGroup.mk w) = 1 := by
  simp only [m22RelsPD, List.mem_append] at hw
  rcases hw with (hw | hw) | hw
  · exact lift_m22Gen_eq_one h (by simp [m22Rels, hw])
  · have h1 := thetaTab_facts hθ w hw
    have hr := rep_wordG_m22ImgG h w
    rw [h1] at hr
    rw [← wordG_m22ImgG_map_letterZ]
    exact eq_of_rep_eq hr (Rep.idT (by norm_num))
  · rw [pRels_eq_m22RelsP] at hw
    exact lift_m22Gen_eq_one h (by simp [m22Rels, hw])

noncomputable def m22PhiPD (h : m22TabCheck = true) (hθ : thetaTabCheck = true) :
    m22PDPresented →* NativeSporadic.M22 :=
  PresentedGroup.toGroup (f := m22Gen) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact lift_m22Gen_eq_one_PD h hθ hw

theorem m22PhiPD_of (h : m22TabCheck = true) (hθ : thetaTabCheck = true) (i : Fin 7) :
    m22PhiPD h hθ (PresentedGroup.of i) = m22Gen i :=
  PresentedGroup.toGroup.of _

theorem m22PhiPD_surjective (h : m22TabCheck = true) (hθ : thetaTabCheck = true) :
    Function.Surjective (m22PhiPD h hθ) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_m22Gen h, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, m22PhiPD_of h hθ i⟩


theorem m22PhiPD_bijective (h : m22TabCheck = true) (hθ : thetaTabCheck = true)
    (hE : M22PDIndex) : Function.Bijective (m22PhiPD h hθ) := by
  obtain ⟨hfin, hcard⟩ := m22PDPresented_card_le hE
  have := hfin
  refine (m22PhiPD_surjective h hθ).bijective_of_nat_card_le ?_
  rw [card_M22]
  exact hcard

noncomputable def m22PDPresentedEquiv (h : m22TabCheck = true) (hθ : thetaTabCheck = true)
    (hE : M22PDIndex) : m22PDPresented ≃* NativeSporadic.M22 :=
  MulEquiv.ofBijective _ (m22PhiPD_bijective h hθ hE)

theorem isSimpleGroup_m22PDPresented (h : m22TabCheck = true) (hθ : thetaTabCheck = true)
    (hE : M22PDIndex) : IsSimpleGroup m22PDPresented :=
  @MulEquiv.isSimpleGroup m22PDPresented _ NativeSporadic.M22 _ fam_m22_simplicity.2.2
    (m22PDPresentedEquiv h hθ hE)

theorem exists_mulEquiv_m22PD_of_relations {G : Type*} [Group G] (e : Fin 7 → G)
    (h : m22TabCheck = true) (hθ : thetaTabCheck = true) (hE : M22PDIndex)
    (hp : ∀ r ∈ m22RelsPD, FreeGroup.lift e (FreeGroup.mk r) = 1)
    (hK : Subgroup.closure (Set.range e) ≠ ⊥) :
    Nonempty (Subgroup.closure (Set.range e) ≃* NativeSporadic.M22) := by
  have hsimple := isSimpleGroup_m22PDPresented h hθ hE
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 7) | r ∈ m22RelsPD.map FreeGroup.mk},
      FreeGroup.lift e r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact hp w hw
  let ψ : m22PDPresented →* G := PresentedGroup.toGroup hrel
  have hrange : ψ.range = Subgroup.closure (Set.range e) := by
    have hcomp : (ψ ∘ PresentedGroup.of) = e := funext fun i => PresentedGroup.toGroup.of _
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp, hcomp]
  have hker : ψ.ker = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ψ.ker with h0 | h0
    · exact h0
    · exfalso
      apply hK
      rw [← hrange, MonoidHom.range_eq_bot_iff]
      exact MonoidHom.ker_eq_top_iff.1 h0
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hker
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans
    (m22PDPresentedEquiv h hθ hE)⟩

end CFSG.CGT.T75JM
