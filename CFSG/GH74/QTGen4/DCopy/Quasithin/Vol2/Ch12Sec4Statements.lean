module

public import CFSG.Quasithin.Vol2.Ch12Sec4Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Stmt12_3_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    ¬ Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7))

@[expose] def Cor12_3_2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Hyp1223 G T L V →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Subgroup.normalizer (L : Set G) →
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
      Group.IsSolvable ↥H ∨
        (LieModel (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) .PSL 2 2 2 ∧
          quasithinIsMaximalLocal T (oTwoUpper H) ∧ quasithinIsFaithfulLocal T (oTwoUpper H) ∧
          IsA5ModuleSum (oTwoUpper H) ⁅VZ T (oTwoUpper H), oTwoUpper H⁆)

variable {G : Type} [Group G]

theorem cor12_3_2_of_stmt12_3_1_F4 (h1231 : Stmt12_3_1_F4) (h1227 : Stmt12_2_7_F4) (h1222 : Stmt12_2_2_F4) :
    Cor12_3_2_F4 := by
  intro G _ _ T L V H hyp hCZ hH
  by_cases hsol : Group.IsSolvable ↥H
  · exact Or.inl hsol
  right
  obtain ⟨h2, Y, hKY, hYmax, hYf, hcase⟩ := (h1227 G T L V H hyp hCZ hH).2 hsol
  have hTH : T ≤ H := hH.1.1
  have hsyl : QuasithinUnique.IsSylowTwoOf T H :=
    ⟨hTH, hyp.sylow.1, fun h => hyp.sylow.2 (h.trans (by
      simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTH))⟩
  rcases hcase with ⟨hYK, hA5⟩ | ⟨hA7, hYq, hTY, -⟩
  · subst hYK
    refine ⟨h2, hYmax, hYf, ?_⟩
    rwa [VZ_eq_VZ_oTwoUpper hsyl] at hA5
  · exfalso
    rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
    · exact hyp.notAlt hAlt
    obtain ⟨-, ⟨VY, hVY⟩, -⟩ := h3 Y hYmax hYf hYq
    exact h1231 G T Y VY ⟨hyp.simple, hyp.nonabelian, hyp.qtke, hyp.sylow, hyp.notAlt, hYmax,
      hYf, hYq, hTY, hVY⟩ hA7

@[expose] def Lemma12_4_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Subgroup.normalizer (L : Set G) →
    ∀ hV : IsElemAbelian 2 V, 1 < E3.sParam hV →
      ∃ g : G, ⁅V, CFSG.conjugate V g⁆ ≠ ⊥ ∧
        ⁅V, CFSG.conjugate V g⁆ ≤ V ⊓ CFSG.conjugate V g

theorem stmt12_4_2_iff_forall_not_cx_F4 :
    Stmt12_4_2_F4 ↔ ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), ¬ Cx1242 G T L V := by
  rw [stmt12_4_2_iff_F4]
  constructor
  · intro h G _ _ T L V hcx
    obtain ⟨h1, h2⟩ := h G T L V hcx.hyp
    rcases hcx.cx with ⟨hq, hne⟩ | ⟨hq, hcard, hle⟩
    · exact hne (h1 hq)
    · exact h2 hq hcard hle
  · intro h G _ _ T L V hyp
    refine ⟨fun hq => ?_, fun hq hcard hle => h G T L V ⟨hyp, Or.inr ⟨hq, hcard, hle⟩⟩⟩
    by_contra hne
    exact h G T L V ⟨hyp, Or.inl ⟨hq, hne⟩⟩

@[expose] def Pre1242_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1242 G T L V →
    ∃ z : G, z ∈ V ⊓ quasithinOmegaOneCenter T ∧ orderOf z = 2 ∧
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
      ((Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
          LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
        V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers z) ∧
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
        V ⊓ quasithinOmegaOneCenter T = Subgroup.zpowers z)

@[expose] def Lemma12_4_3_one_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1242 G T L V →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma12_4_3_two_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1242 G T L V →
    L = ⁅L, thompsonJ T⁆

theorem lemma12_4_3_one_of_pre_F4 (hpre : Pre1242_F4) : Lemma12_4_3_one_F4 := by
  intro G _ _ T L V hcx
  obtain ⟨z, hz, -, hGz, -⟩ := hpre G T L V hcx
  refine le_trans (Subgroup.centralizer_le ?_) hGz
  rintro _ rfl
  exact hz.2

@[expose] def Lemma12_4_4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1242 G T L V →
    ¬ Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))

@[expose] def Post1244_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1242 G T L V →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      ∃ z : G, orderOf z = 2 ∧ V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers z ∧
        Subgroup.normalizer (L : Set G) = Subgroup.centralizer ({z} : Set G) ∧
        Subgroup.normalizer (L : Set G) = Subgroup.normalizer (V : Set G) ∧
        ∃ hV : IsElemAbelian 2 V, E3.mParam (autI hV ⊤) = 2

@[expose] def Lemma12_4_6_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1242 G T L V →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ E : Subgroup G, E ≤ V → Nat.card E = 4 → T ≤ Subgroup.normalizer (E : Set G) →
      ∀ v ∈ E, v ∉ Subgroup.centralizer (L : Set G) →
        QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer (E : Set G))
          (Subgroup.centralizer ({v} : Set G)) ∧
        (T ⊓ Subgroup.centralizer (E : Set G)).relIndex T = 2

@[expose] def Lemma12_4_7_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1242 G T L V →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      ∀ v ∈ V, ∀ g : G, g⁻¹ * v * g ∈ V → ∃ l ∈ L, l⁻¹ * v * l = g⁻¹ * v * g

@[expose] def Lemma12_4_8_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1242 G T L V →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      1 < E3.rParam V

@[expose] def Lemma12_4_9_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1242 G T L V →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      ∀ g : G, CFSG.conjugate V g ≤ Subgroup.normalizer (V : Set G) →
        ⁅CFSG.conjugate V g, V⁆ ≠ ⊥ →
          ¬ V ≤ Subgroup.normalizer (CFSG.conjugate V g : Set G)

theorem stmt12_4_2_of_lemmas_F4 (h1241 : Lemma12_4_1_F4) (h1243 : Lemma12_4_3_one_F4)
    (h1244 : Lemma12_4_4_F4) (hpost : Post1244_F4) (h1248 : Lemma12_4_8_F4) (h1249 : Lemma12_4_9_F4) :
    Stmt12_4_2_F4 := by
  rw [stmt12_4_2_iff_forall_not_cx_F4]
  intro G _ _ T L V hcx
  have hq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 := by
    rcases hcx.cx with ⟨hq, -⟩ | ⟨hq, -⟩
    · exact hq
    · exact absurd hq (h1244 G T L V hcx)
  obtain ⟨-, -, -, -, -, hV, hm⟩ := hpost G T L V hcx hq
  have hr := h1248 G T L V hcx hq
  have hs : 1 < E3.sParam hV := by
    unfold E3.sParam
    rw [hm]
    have h2 : (2 : ℕ∞) ≤ E3.rParam V := by
      have := Order.add_one_le_of_lt hr
      rwa [one_add_one_eq_two] at this
    rw [min_eq_right (by exact_mod_cast h2)]
    simp
  obtain ⟨g, hne, hle⟩ := h1241 G T L V hcx.hyp (h1243 G T L V hcx) hV hs
  obtain ⟨hAV, hVA⟩ := le_normalizer_of_commutator_le hle
  have hne' : ⁅CFSG.conjugate V g, V⁆ ≠ ⊥ := by
    rwa [Subgroup.commutator_comm]
  exact h1249 G T L V hcx hq g hAV hne' hVA

end CFSG.Quasithin.H13
