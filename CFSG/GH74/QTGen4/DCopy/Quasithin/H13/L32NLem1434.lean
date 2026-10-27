module

public import CFSG.Quasithin.H13.L32NLem1434
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem143
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def Lemma1434One_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), Hyp14_3_1One G T L →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
        LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1

theorem lemma1434One_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1352 : A6.Stmt13_5_2_F4)
    (h1381 : Stmt13_8_1_F4) : Lemma1434One_F4 := by
  intro G _ _ T L h K hK
  have hK13 : ¬ Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) →
      QTH13 G T K := fun hn =>
    (h1332 G T L h.h13 K hK).2.2.2 (Or.inl fun h5 =>
      hn ((quasithinO2QuotientIso_iff K _).mp h5))
  have hexcl : ∀ K' : Subgroup G, QTH13 G T K' →
      Nonempty ((↥K' ⧸ CFSG.pCore 2 ↥K') ⧸ Subgroup.center (↥K' ⧸ CFSG.pCore 2 ↥K') ≃*
        alternatingGroup (Fin 6)) → False := by
    intro K' hK' he
    rcases h1381 G T K' hK' he with hs | hu
    · exact h.not_sp62 hs
    · exact h.not_u43 hu
  rcases (h1352 G T L h.h13 h.not_sp62 K hK).1 with h5 | h3 | he6 | ⟨-, hc3, he⟩
  · exact Or.inl h5
  · exact Or.inr h3
  · exfalso
    obtain ⟨e⟩ := he6
    have hc : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
      center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot (by norm_num))
    refine hexcl K (hK13 (not_iso_five_of_iso_six e)) ⟨?_⟩
    exact (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot.trans e)
  · exfalso
    refine hexcl K (hK13 fun ⟨f⟩ => ?_) he
    have hc : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
      center_eq_bot_of_mulEquiv f (alternatingGroup.center_eq_bot (by norm_num))
    rw [hc, Subgroup.card_bot] at hc3
    omega

theorem lemma1433Six_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14_3_1One G T L → FSU G T L V →
      ∀ U₀ H : Subgroup G, U₀ ≤ V → U₀ ≠ ⊥ → H ≤ Subgroup.normalizer (U₀ : Set G) →
        H ⊓ Subgroup.normalizer (L : Set G) = H ⊓ Subgroup.normalizer (V : Set G) := by
  intro G _ _ T L V h hF U₀ H hU₀ hU₀1 hH
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have h1433 := lemma1433Five_of_inputs_F4 h1332 h1334 G T L V h hF
  have hmem : ∀ {x m : G}, x ∈ CFSG.conjugate V m ↔ m * x * m⁻¹ ∈ V := fun {x m} => by
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hv
    · intro hx
      exact ⟨m * x * m⁻¹, hx, by simp [mul_assoc]⟩
  apply le_antisymm
  · intro m hm
    refine ⟨hm.1, ?_⟩

    have hTL := (h13322 G T L h.h13 L h.h13.faithful).1
    have hirr : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V := by
      have := hF.irrPlus
      have hcl : conjClosure L T = L :=
        le_antisymm (conjClosure_le fun _ ht l hl =>
          (Subgroup.mem_normalizer_iff.1 (hTL ht) l).1 hl) (le_conjClosure L T)
      rwa [hcl] at this
    rcases h1222 G T hF.simple hF.nonabelian hF.qtke hF.sylow with hA | hall
    · exact (h.h13.not_excluded (Hyp14310One.qt13Excluded_of_alt hA)).elim
    obtain ⟨-, -, hV⟩ := hall L hF.maximal hF.faithful hF.quasisimple
    obtain ⟨-, hTI, -, -⟩ := hV V hirr
    rcases hTI m hm.2 with he | he
    · show m ∈ Subgroup.normalizer (V : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [← he] at hx
        exact hmem.mp hx
      · intro hx
        rw [← he]
        exact hmem.mpr hx
    · exfalso
      apply hU₀1
      rw [eq_bot_iff, ← he]
      intro u hu
      refine ⟨hU₀ hu, hmem.mpr (hU₀ ?_)⟩
      exact (Subgroup.mem_normalizer_iff.mp (hH hm.1) u).mp hu
  · intro m hm
    refine ⟨hm.1, ?_⟩
    have h2 : m ∈ Subgroup.normalizer (V : Set G) := hm.2
    rw [h1433] at h2
    exact h2.1

end CFSG.Quasithin.H13
