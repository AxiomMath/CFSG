module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3327

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem stmt3_3_27_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14_F4)
    (h25 : Stmt3_3_25_F4) (hL32 : FactL32CentralInv) (hInsp : Insp3_3_27) : Stmt3_3_27_F4 := by
  intro G _ _ T M L D h d hdD hdM _ hTC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hblock := (h25 G T M L D h).1
  have hshort : IsShort2 L := by
    rcases hblock with hb | hb | hb
    · exact hb.1
    · exact hb.1
    · exact hb.1
  have hdM' : d⁻¹ ∉ M := fun hm => hdM (by simpa using M.inv_mem hm)
  have h1 := h.tC_inf_conjugate_eq_bot h38 h39 hTL hdD hdM
  have h1' := h.tC_inf_conjugate_eq_bot h38 h39 hTL (D.inv_mem hdD) hdM'
  have hMp := Hyp331.mPlus_eq_of_le hTL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hO2 : pCoreOf 2 (autOn (L ⊔ T) (vPlus L T)) = ⊥ :=
    CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred.2.2
  obtain ⟨hKX, hXK, h2X, hSyl⟩ := h.autOn_data
  rw [hMp] at hKX hXK h2X
  have h3 : CFSG.conjugate (tC L T) d ≤ qL L T ∨ tC L T ≤ CFSG.conjugate (qL L T) d := by
    by_cases hP : IsPSL 3 2 1 ↥(autOn L (vPlus L T))
    · refine h.three_of_uniq h38 h39 hTL hdD hdM (Y := ⊥) (fun x _ y hy => ?_)
        (fun x _ y hy => ?_) ?_
      · rw [Subgroup.mem_bot] at hy
        rw [hy, one_mul, mul_one]
      · rw [Subgroup.mem_bot] at hy
        rw [hy, one_mul, mul_one]
      · intro z₁ hz₁ z₂ hz₂ hc₁ hc₂ h2₁ h2₂ hn₁ hn₂ _ _
        exact hL32 (MulAut ↥(vPlus L T)) (autOn (L ⊔ T) (vPlus L T)) (autOn L (vPlus L T))
          (autOn T (vPlus L T)) hKX hXK hP h2X hO2 hSyl z₁ hz₁ z₂ hz₂ hc₁ hc₂ h2₁ h2₂ hn₁ hn₂
    · obtain ⟨hDX, -, -⟩ := (h25 G T M L D h).2.1 hTC hP
      have hXL : oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤ L :=
        (oTwoUpper_le _).trans inf_le_left
      have hcomm : ∀ g : G, g ∈ Subgroup.normalizer
          (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) : Set G) →
          ∀ x ∈ (tC L T).map (MulAut.conj g⁻¹).toMonoidHom,
          ∀ y ∈ oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)),
            x * y = y * x := by
        intro g hg x hx y hy
        rw [A38.mem_map_conj, inv_inv] at hx
        have hy' := (Subgroup.mem_normalizer_iff.mp hg y).mp hy
        have hc : g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹) :=
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 _ (hXL hy')
        calc x * y = g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g := by group
          _ = g⁻¹ * (g * y * g⁻¹ * (g * x * g⁻¹)) * g := by rw [hc]
          _ = y * x := by group
      refine h.three_of_uniq h38 h39 hTL hdD hdM (Y := oTwoUpper (L ⊓ Subgroup.centralizer
        (quasithinOmegaOneCenter T : Set G))) (hcomm d (hDX hdD)) ?_ ?_
      · intro x hx y hy
        exact hcomm d⁻¹ (inv_mem (hDX hdD)) x hx y hy
      · intro z₁ hz₁ z₂ hz₂ hc₁ hc₂ h2₁ h2₂ hn₁ hn₂ hy₁ hy₂
        exact hInsp G T M L D h hTL hblock hP z₁ hz₁ z₂ hz₂ hc₁ hc₂ h2₁ h2₂ hn₁ hn₂ hy₁ hy₂
  refine ⟨h1, ?_, h3⟩
  by_contra hΦ
  have : Fact (IsPGroup 2 ↥(qL L T)) := ⟨CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _⟩
  have hQ2 : IsPGroup 2 ↥(qL L T) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hF := h.frattini_qL_le_tC h38 h39 hshort hTL
  have hcase : ∀ g : G, (tC L T).map (MulAut.conj g).toMonoidHom ≤ qL L T →
      tC L T ⊓ (tC L T).map (MulAut.conj g).toMonoidHom = ⊥ → False := by
    intro g hle hinf
    apply hΦ
    rw [← frattini_map_conj_eq_bot_iff g]
    have hle' : (frattini ↥((tC L T).map (MulAut.conj g).toMonoidHom)).map
        ((tC L T).map (MulAut.conj g).toMonoidHom).subtype ≤ ⊥ := by
      rw [← hinf]
      exact le_inf ((frattini_map_mono hQ2 hle).trans hF) (Subgroup.map_subtype_le _)
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp
      (le_bot_iff.mp hle')
  rcases h3 with h3 | h3
  · exact hcase d⁻¹ h3 h1
  · refine hcase d⁻¹⁻¹ ?_ h1'
    intro x hx
    rw [A38.mem_map_conj, inv_inv] at hx
    have := h3 hx
    rw [CFSG.conjugate, A38.mem_map_conj, inv_inv] at this
    simpa [mul_assoc] using this

end CFSG.Quasithin.H13
