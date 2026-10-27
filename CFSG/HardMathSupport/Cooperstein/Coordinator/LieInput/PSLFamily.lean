module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Simple
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLOb
public import CFSG.Quasithin.Vol2.Ch10SecA312AD

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.AGLEmbedding CFSG.LieType.BorelTits CFSG.Quasithin.SmithC27
  CFSG.LieType.Universal.SpecialLinear CFSG.Assembly.LowTwoRank

theorem exists_sylow_of_isSylowTwoOf' {X : Type} [Group X] {S : Subgroup X}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  exact ⟨hS.2.1.toSylow hi, rfl⟩

section Main


theorem simpleStmt_of_psl {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y CFSG.Assembly.LowTwoRank.StatedLieTag.PSL n 2 f) : SimpleStmt Y := by
  have hsimple : IsSimpleGroup Y := CFSG.Quasithin.Vol2.Ch10.A312A.isSimpleGroup_of_stated h
  obtain ⟨F, hF, hFfin, hcard, ⟨e⟩⟩ := h.2
  let _ := hF
  let _ := hFfin
  have hp : (2 : ℕ).Prime := h.1.1
  have hf : 1 ≤ f := h.1.2.1
  have hn : 2 ≤ n := h.1.2.2.1
  have h22 : (n, 2 ^ f) ≠ (2, 2) := h.1.2.2.2.1
  have h23 : (n, 2 ^ f) ≠ (2, 3) := h.1.2.2.2.2
  have hcharP : CharP F 2 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hk : 3 ≤ n ∨ (n = 2 ∧ 4 ≤ Nat.card F) := by
    by_cases h3 : 3 ≤ n
    · exact Or.inl h3
    · have hn2 : n = 2 := by omega
      refine Or.inr ⟨hn2, ?_⟩
      rw [hcard]
      by_cases hf1 : f = 1
      · exfalso; apply h22; rw [hn2, hf1]; norm_num
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let e' : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y :=
    (projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm
  obtain ⟨hqPSL, -⟩ := isQuasisimple_of_central_quotient
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    (isChevComponent_sl (F := F) hk).1
  have hq : CFSG.IsQuasisimple Y := isQuasisimple_of_mulEquiv e' hqPSL
  have hZ : Subgroup.center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hq.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have ha' : a' ∈ Subgroup.center Y := by rw [h1]; trivial
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp ha' b']
  have hcl : IsClassicalTwoOrG2 Y := isClassicalTwoOrG2_of_statedPSL h
  have hb := CFSG.AGLEmbedding.ParabHub.borelQuotient_sl (m := m) (F := F) e'
  intro R hR
  by_cases hne : (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) = ⊤
  · exact ⟨leviStructure_improper hq hZ hcl hR hne, fun h' => absurd hne h'⟩
  have hR2 : IsPGroup 2 R := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hR]; exact pCoreOf_isPGroup 2 _
  have hRbot : R ≠ ⊥ := by
    rintro rfl
    apply hne
    rw [eq_top_iff]
    intro x _
    exact ⟨trivial, Subgroup.mem_normalizer_iff.mpr fun y => by simp⟩
  have hEven : CFSG.Blueprint.EvenLieType Y :=
    CFSG.HardMathSupport.Cooperstein.StructureLie.evenLieType_of_classicalTag (Or.inl rfl) h
  have hrad := CFSG.Quasithin.C22Pf.isRadicalParabolic_c224_holds Y (Or.inl hEven) R le_top hRbot
    hR2 hR.symm
  obtain ⟨-, S, hS, hSN⟩ := hrad
  obtain ⟨T, hT⟩ := exists_sylow_of_isSylowTwoOf' hS
  have hpar : ∃ T : Sylow 2 Y, Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤
      (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) :=
    ⟨T, by rw [hT]; simpa using hSN⟩
  have hOb : ∀ π' : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* Y,
      CFSG.AGLEmbedding.ParabHub.BorelQuotient (rootDatum m F) (weylRep m F) (torus m F) π'
        (Nat.card F - 1) → ∀ I : Set (Fin m), I ≠ Set.univ →
          LeviOb (rootDatum m F) (torus m F) π' I :=
    fun π' hπ' I hI => leviOb_sl π' (fun z hz => hπ'.ker_central z hz) hI
  refine ⟨leviStructure_of_borelQuotient hb hR hne hpar hOb,
    fun _ => centralizer_of_borelQuotient hb hR hne hpar hZ (fun I hI => centOb_sl hI)⟩

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
