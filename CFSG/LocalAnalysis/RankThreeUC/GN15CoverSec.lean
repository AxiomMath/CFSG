module

public import CFSG.LocalAnalysis.RankThreeUC.GN15CoverStep
public import CFSG.LocalAnalysis.RankThreeUC.GN15CoverSecL1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
  CFSG.AGLEmbeddingD2.GN CFSG.AGLEmbedding CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

private def SecConcl (T T₁ T₂ : Subgroup X) (S : Type) [Group S] : Prop :=
  (∃ (A : Subgroup X) (f : ↥A →* S),
      A ≤ Subgroup.normalizer (T₁ : Set X) ∧ Function.Surjective f) ∨
    (∃ (A : Subgroup X) (f : ↥A →* S),
      A ≤ Subgroup.normalizer (T₂ : Set X) ∧ Function.Surjective f) ∨
    ∃ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls ∧
      ∃ (A : Subgroup (X ⧸ gnC T)) (f : ↥A →* S), A ≤ Ls ∧ Function.Surjective f

private theorem secStep (hI59 : AGL81I59) (hJ3 : ThreePrimeJCentral) (hJ : JOutCentralAt T)
    (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂) {A B : Subgroup X} (hA : A.Normal)
    (hB : B.Normal) (hBA : B ≤ A) (hCB : gnC T ≤ B)
    (hchief : ∀ D : Subgroup X, D.Normal → B ≤ D → D ≤ A → D = B ∨ D = A)
    (hBP : ∀ (S : Type) [Group S], E1.IsCompositionFactor ↥B S → ¬ Group.IsSolvable S →
      SecConcl T T₁ T₂ S)
    (S : Type) [Group S] (hSA : E1.IsCompositionFactor ↥A S) (hnS : ¬ Group.IsSolvable S) :
    SecConcl T T₁ T₂ S := by
  have := hA
  have := hB
  have : (B.subgroupOf A).Normal := hB.subgroupOf A
  rcases isCompositionFactor_of_normal (B.subgroupOf A) hSA with h1 | h2
  · have : E1.IsCompositionFactor ↥B S :=
      (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
        (Subgroup.subgroupOfEquivOfLe hBA)).1 h1
    exact hBP S this hnS
  · have := isSimpleGroup_of_isCompositionFactor hSA
    by_cases hAD : A ⊓ gnDPre T ≤ B
    · rcases cover_cases_of_chief hI59 hJ3 hJ hX hP hA hB hBA hCB hAD hchief with h | h | ⟨h3, -⟩
      · obtain ⟨A'', f, hA'', hf, -⟩ := exists_sec_of_cover hB h h2
        exact Or.inl ⟨A'', f, (hA''.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _),
          hf⟩
      · obtain ⟨A'', f, hA'', hf, -⟩ := exists_sec_of_cover hB h h2
        exact Or.inr (Or.inl ⟨A'', f, hA''.trans inf_le_right, hf⟩)
      · exfalso
        apply hnS
        refine isSolvable_of_isCompositionFactor_of_pow h2 ?_
        intro q
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨k, hk⟩ := h3 a.1 a.2
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hk
    · have hDn : (gnDPre T).Normal := gnDPre_normal hX
      have hBD : B ⊔ (A ⊓ gnDPre T) = A := by
        rcases hchief (B ⊔ (A ⊓ gnDPre T)) inferInstance le_sup_left (sup_le hBA inf_le_left) with h | h
        · exact absurd (le_sup_right.trans h.le) hAD
        · exact h
      obtain ⟨A'', f, hA'', hf, hker⟩ := exists_sec_of_cover hB hBD.ge h2
      set φ : X →* X ⧸ gnC T := toStar T with hφ
      have hσ : Function.Surjective (φ.subgroupMap A'') := MonoidHom.subgroupMap_surjective φ A''
      have hkerφ : (φ.subgroupMap A'').ker ≤ f.ker := by
        intro x hx
        have h0 : φ x = 1 := by
          have := congrArg Subtype.val ((MonoidHom.mem_ker).1 hx)
          simpa using this
        have hxC : (x : X) ∈ gnC T := (QuotientGroup.eq_one_iff _).1 h0
        exact hker x (hCB hxC)
      obtain ⟨g, -, hgs, -⟩ := exists_surjective_comp_eq (φ.subgroupMap A'') hσ f hf hkerφ
      set Sset : Set (Subgroup (X ⧸ gnC T)) :=
        {L | IsComponentOf L ⊤ ∧ ⁅L, gnImg T (thompsonJ T)⁆ ≠ ⊥} with hSset
      have hfin : Sset.Finite := Set.toFinite Sset
      have hDst : (⨆ L ∈ hfin.toFinset, L : Subgroup (X ⧸ gnC T)) = gnDStar T :=
        le_antisymm
          (iSup₂_le fun L hL => le_iSup₂_of_le L (hfin.mem_toFinset.1 hL) le_rfl)
          (iSup₂_le fun L hL => le_iSup₂_of_le L (hfin.mem_toFinset.2 hL) le_rfl)
      have hle : A''.map φ ≤ ⨆ L ∈ hfin.toFinset, L := by
        rw [hDst]
        rintro _ ⟨x, hx, rfl⟩
        exact Subgroup.mem_comap.1 (hA'' hx).2
      have hcomm : ∀ L ∈ hfin.toFinset, ∀ L' ∈ hfin.toFinset, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L',
          a * b = b * a := by
        intro L hL L' hL' hne a ha b hb
        rcases CFSG.LocalCores.distinct_components_commute
          ((CFSG.isComponent_iff_open L).2 (hfin.mem_toFinset.1 hL).1)
          ((CFSG.isComponent_iff_open L').2 (hfin.mem_toFinset.1 hL').1) with h | h
        · exact absurd h hne
        · exact (Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h ha) b hb).symm
      obtain ⟨L, hL, A', f', hA'L, hf'⟩ :=
        exists_sec_of_le_iSup hfin.toFinset hcomm (A''.map φ) hle g hgs
      have hLS := hfin.mem_toFinset.1 hL
      by_cases hY : GNYComponent T T₁ T₂ L
      · exact Or.inr (Or.inr ⟨L, hY, A', f', hA'L, hf'⟩)
      · rcases le_or_le_of_not_gnYComponent hLS.1 hY with hc | hn
        · obtain ⟨Ã, g', hÃ, hg'⟩ := exists_sec_lift_of_le_image φ (hA'L.trans hc) f' hf'
          exact Or.inl ⟨Ã, g', hÃ.trans (Subgroup.centralizer_le_normalizer _), hg'⟩
        · obtain ⟨Ã, g', hÃ, hg'⟩ := exists_sec_lift_of_le_image φ (hA'L.trans hn) f' hf'
          exact Or.inr (Or.inl ⟨Ã, g', hÃ, hg'⟩)

theorem gnCoverSec_of_JOutCentralAt (hI59 : AGL81I59) (hJ3 : ThreePrimeJCentral)
    (hJ : JOutCentralAt T) (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂) :
    GNCoverSec T T₁ T₂ := by
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hP
  set P : Subgroup X → Prop := fun Y => gnC T ≤ Y ∧ ∀ (S : Type) [Group S],
    E1.IsCompositionFactor ↥Y S → ¬ Group.IsSolvable S → SecConcl T T₁ T₂ S with hPdef
  have hC1 : gnC T ≤ Subgroup.centralizer (T₁ : Set X) :=
    Subgroup.centralizer_le (fun x hx => Subgroup.subset_normalClosure (h1Z hx))
  have hbase : P (gnC T) := by
    refine ⟨le_rfl, fun S _ hS hnS => ?_⟩
    obtain ⟨A, f, hA, hf⟩ := exists_sec_of_isCompositionFactor_of_le hS le_rfl
    exact Or.inl ⟨A, f, hA.trans (hC1.trans (Subgroup.centralizer_le_normalizer _)), hf⟩
  have hstep : ∀ A B : Subgroup X, A.Normal → B.Normal → B ≤ A →
      (∀ D : Subgroup X, D.Normal → B ≤ D → D ≤ A → D = B ∨ D = A) → A ≤ B ⊔ ⊤ → P B → P A := by
    intro A B hA hB hBA hchief _ hPB
    exact ⟨hPB.1.trans hBA, fun S _ hSA hnS =>
      secStep hI59 hJ3 hJ hX hP hA hB hBA hPB.1 hchief hPB.2 S hSA hnS⟩
  have hall := climb_of_chief_factor_step (P := P) (N := ⊤) hstep (gnC_normal T) hbase ⊤
    inferInstance le_top (by simp)
  intro S _ hS hnS
  exact hall.2 S ((CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
    (Subgroup.topEquiv (G := X)).symm).1 hS) hnS

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
