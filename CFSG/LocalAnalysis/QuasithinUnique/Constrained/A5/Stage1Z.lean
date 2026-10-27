module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage1P

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split
open scoped commutatorElement

theorem g1_comm_z0 : g1 + pact sc g1 = z0 := by decide +kernel

theorem z0_E8 : (StdCfg.z0V).1 4 = 0 := by decide +kernel

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem zU_mul_self (C : StdCfg T M H S L) : C.zU * C.zU = 1 := by
  rw [← pow_two]
  exact C.zU_sq

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem iV_mem_P {e : evenWeight 5} (he : e.1 4 = 0) : ((C.iV e : ↥H) : G) ∈ borelP M L := by
  rw [X.borelP_eq]
  exact ⟨e, 1, one_mem _, he, congrArg Subtype.val (by rw [Sec.emb, map_one, mul_one])⟩

theorem s_mem_P {τ : Equiv.Perm (Fin 5)} (hτ : τ ∈ Vset) : ((X.s τ : ↥H) : G) ∈ borelP M L := by
  rw [X.borelP_eq]
  exact ⟨0, τ, hτ, rfl, congrArg Subtype.val (by rw [Sec.emb, C.iV_zero, one_mul])⟩

theorem centerOf_P_iff (x : G) : x ∈ centerOf (borelP M L) ↔ x = 1 ∨ x = C.zU := by
  constructor
  · intro hx
    obtain ⟨hxP, hxc⟩ := Subgroup.mem_inf.mp hx
    have hcomm : ∀ p ∈ borelP M L, p * x = x * p := fun p hp =>
      Subgroup.mem_centralizer_iff.mp hxc p hp
    have hxP' := hxP
    rw [X.borelP_eq] at hxP'
    obtain ⟨w, σ, hσ, hw, rfl⟩ := hxP'
    have hσ1 : σ = 1 := by
      apply V_faithful_E8 σ hσ
      intro v hv
      have hc : X.emb w σ * C.iV ⟨v, hv.1⟩ = C.iV ⟨v, hv.1⟩ * X.emb w σ :=
        Subtype.ext (hcomm _ (X.iV_mem_P (e := ⟨v, hv.1⟩) hv.2)).symm
      have := X.vact_fixed_of_comm (X.emb w σ) ⟨v, hv.1⟩ hc
      rw [X.pi_emb] at this
      exact congrArg Subtype.val this
    subst hσ1
    have hspec : X.emb w 1 = C.iV w := by rw [Sec.emb, map_one, mul_one]
    have hfix : ∀ τ ∈ Vset, vact τ w = w := by
      intro τ hτ
      have hc : X.s τ * C.iV w = C.iV w * X.s τ := by
        rw [← hspec]
        exact Subtype.ext (hcomm _ (X.s_mem_P hτ))
      have h1 := C.conj_iV X.hTC (X.s τ) w
      rw [X.hs] at h1
      have h2 : X.s τ * C.iV w * (X.s τ)⁻¹ = C.iV w := by rw [hc]; group
      rw [h2] at h1
      exact C.iV_inj X.hTC h1.symm
    rcases E8_fixed_V w.1 ⟨w.2, hw⟩ (fun τ hτ => congrArg Subtype.val (hfix τ hτ)) with h0 | h0
    · left
      have h0' : w = 0 := Subtype.ext h0
      subst h0'
      rw [hspec, C.iV_zero]
      rfl
    · right
      have h0' : w = StdCfg.z0V := Subtype.ext h0
      subst h0'
      rw [hspec]
      exact C.zU_eq_iV.symm
  · rintro (rfl | rfl)
    · exact one_mem _
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [C.zU_eq_iV]
        exact X.iV_mem_P z0_E8
      · rw [Subgroup.mem_centralizer_iff]
        intro p hp
        rw [X.borelP_eq] at hp
        obtain ⟨w, σ, hσ, hw, rfl⟩ := hp
        have h4 : C.D.π (X.emb w σ) 4 = 4 := by
          rw [X.pi_emb]
          exact V_fix4 σ hσ
        exact C.zU_comm (X.emb w σ) h4

theorem centerOf_P_eq : centerOf (borelP M L) = Subgroup.zpowers C.zU := by
  ext x
  rw [X.centerOf_P_iff, mem_zpowers_two C.zU_mul_self x]

theorem centerOf_S_eq : centerOf S = Subgroup.zpowers C.zU := by
  ext x
  rw [X.centerOf_S_iff, mem_zpowers_two C.zU_mul_self x]

theorem Z_card : Nat.card ↥(centerOf (borelP M L)) = 2 := by
  rw [X.centerOf_P_eq, Nat.card_zpowers]
  exact orderOf_eq_prime C.zU_sq C.zU_ne_one

theorem iV_comm_key (a : Equiv.Perm (Fin 5)) (w : evenWeight 5) :
    C.iV w * X.s a * (C.iV w)⁻¹ * (X.s a)⁻¹ = C.iV (w + vact a w) := by
  have hconj := C.conj_iV X.hTC (X.s a) w
  rw [X.hs] at hconj
  have hinv : (C.iV w)⁻¹ = C.iV w := inv_eq_of_mul_eq_one_right (C.iV_self w)
  calc C.iV w * X.s a * (C.iV w)⁻¹ * (X.s a)⁻¹
      = C.iV w * (X.s a * C.iV w * (X.s a)⁻¹) := by rw [hinv]; group
    _ = C.iV w * C.iV (vact a w) := by rw [hconj]
    _ = C.iV (w + vact a w) := by rw [C.iV_add]

theorem zU_mem_frattini : C.zU ∈ (frattini ↥S).map S.subtype := by
  have : Fact (IsPGroup 2 ↥S) := ⟨C.hcs.sylow.2.1⟩
  let g1w : evenWeight 5 := ⟨g1, g1_even⟩
  let a : ↥S := ⟨((C.iV g1w : ↥H) : G), C.iV_mem_S g1w⟩
  let b : ↥S := ⟨((X.s sc : ↥H) : G), X.s_mem_S sc_mem⟩
  have hcomm : ⁅a, b⁆ ∈ _root_.commutator ↥S := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  have hfr : ⁅a, b⁆ ∈ frattini ↥S :=
    CFSG.commutator_le_frattini_of_isPGroup (R := ↥S) (p := 2) hcomm
  refine ⟨⁅a, b⁆, hfr, ?_⟩
  have hz : g1w + vact sc g1w = StdCfg.z0V := Subtype.ext g1_comm_z0
  have key := X.iV_comm_key sc g1w
  rw [hz] at key
  exact congrArg Subtype.val key

theorem Z_eq : centerOf (borelP M L) = (frattini ↥S).map S.subtype ⊓ centerOf S := by
  rw [X.centerOf_P_eq, X.centerOf_S_eq]
  exact le_antisymm (le_inf (Subgroup.zpowers_le.mpr X.zU_mem_frattini) le_rfl) inf_le_right

theorem Z_le : centerOf (borelP M L) ≤ centerOf T := by
  rw [X.centerOf_P_eq, Subgroup.zpowers_le]
  refine Subgroup.mem_inf.mpr ⟨C.hcs.le_T (blockU_le_S C.hcs C.hj C.zU_mem), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyn : y ∈ Subgroup.normalizer (S : Set G) := C.T_le_normalizer_S hy
  have hyn' : y⁻¹ ∈ Subgroup.normalizer (S : Set G) := inv_mem hyn
  have hzS : C.zU ∈ centerOf S := (X.centerOf_S_iff _).mpr (Or.inr rfl)
  obtain ⟨hzS1, hzSc⟩ := Subgroup.mem_inf.mp hzS
  have hconj : y * C.zU * y⁻¹ ∈ centerOf S := by
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hyn C.zU).mp hzS1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : y⁻¹ * s * y⁻¹⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hyn' s).mp hs
    have hc := Subgroup.mem_centralizer_iff.mp hzSc _ hs'
    calc s * (y * C.zU * y⁻¹) = y * ((y⁻¹ * s * y⁻¹⁻¹) * C.zU) * y⁻¹ := by group
      _ = y * (C.zU * (y⁻¹ * s * y⁻¹⁻¹)) * y⁻¹ := by rw [hc]
      _ = (y * C.zU * y⁻¹) * s := by group
  rcases (X.centerOf_S_iff _).mp hconj with h1 | h1
  · exfalso
    apply C.zU_ne_one
    calc C.zU = y⁻¹ * (y * C.zU * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  · calc y * C.zU = (y * C.zU * y⁻¹) * y := by group
      _ = C.zU * y := by rw [h1]

end Sec

end CFSG.QuasithinUnique.A5
