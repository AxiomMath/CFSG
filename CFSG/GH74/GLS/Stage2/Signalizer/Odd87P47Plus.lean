module

public import CFSG.GH74.GLS.Stage2.Signalizer.L199
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4C
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4D
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Sl2Fin

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

section Plus

variable {G : Type} [Group G] {z : G} {k : Kind}
variable {A : Type} [Group A] [Finite A] {a : A} {p : ℕ} {X J : Subgroup A}

@[expose] def C43cPlus (p : ℕ) (X : Subgroup A) : Prop :=
  IsComponent (ncl X) ∧
    (∀ c : A, orderOf c = 2 → c ∈ centralizer ((ncl X : Subgroup A) : Set A) → False) ∧
    ∃ n : ℕ, 1 ≤ n ∧ LieModel (Hat (ncl X)) .PSL 3 p n

theorem case_c_plus (F : E4Hyp G z k) {c : E4Ctx G z A a p X} (d : SubData c J)
    (hc : C42c p (secZ a X J) (secX a X J) (secJ a X J)) : C43c a p X ∧ C43cPlus p X := by
  have : Fact p.Prime := ⟨c.A4.prime⟩
  refine ⟨case_c F d hc, ?_⟩
  obtain ⟨n, hn1, hLie, hzK, hEA, hcard, P', hP', hXOp, hPeq⟩ := hc
  have hLieHat : LieModel (Hat J) .PSL 3 p n :=
    Transport.lieModel_of_mulEquiv (secJ_equiv d.hyp).some hLie
  have hodd : Odd (p ^ n) := (c.A4.prime.odd_of_ne_two c.A4.odd).pow
  have hf : ∀ c' : A, orderOf c' = 2 → c' ∈ centralizer (J : Set A) → False :=
    fun c' h1 h2 => F.f3 A a c.sec J d.comp p n c.A4.prime hn1 (Or.inl hodd) hLieHat c' h1 h2
  have hcomp1 : ∀ J' : Subgroup A, IsComponent J' → J' = J := fun J' hJ' =>
    comp_eq_of_no_invol d.comp hf hJ'
  have hcomp : ∀ J' : Subgroup A, IsComponent J' → J' ≤ ncl X → J' = J := fun J' hJ' _ => hcomp1 J' hJ'
  have hJn : J.Normal := normal_of_unique d.comp hcomp1
  have hR2 : pCore 2 A = ⊥ := pCore_two_eq_bot_of_no_invol d.comp hf
  have hF : ∀ q : ℕ, q.Prime → X ≤ centralizer ((pCore q A : Subgroup A) : Set A) := by
    intro q hq
    by_cases hq2 : q = 2
    · subst hq2
      rw [hR2]
      intro x _ y hy
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      subst hy
      simp
    · exact c.a41 q hq hq2
  have hXK : secX a X J ≤ secJ a X J := by
    rw [hXOp]
    exact (Subgroup.map_subtype_le _).trans hP'.1.1
  have hXJC : X ≤ J ⊔ centralizer (J : Set A) := d.X_le_sup_of_le hXK
  have hJK : J ≤ ncl X := comp_le_ncl d.comp d.JX
  have hncl : ncl X = J :=
    ncl_eq_of_single_comp c.A4.prime c.A4.pgroup c.op d.comp hJn hJK hXJC hcomp hF
  unfold C43cPlus
  subst hncl
  exact ⟨d.comp, hf, n, hn1, hLieHat⟩

@[expose] def Concl43Ep (k : Kind) (z : A) (p : ℕ) (X : Subgroup A) : Prop :=
  C43b p X ∨ (C43c z p X ∧ C43cPlus p X) ∨ C43d1 k z X ∨ C43e X

theorem prop4_3Ep_core (F : E4Hyp G z k) (hOut : L34DiagClosure) {c : E4Ctx G z A a p X}
    (hN : ⁅layer A, X⁆ ≠ ⊥) : Concl43Ep k a p X := by
  obtain ⟨J, hJ, hJX⟩ := exists_comp_comm_ne hN
  have hX : ∀ J' : Subgroup A, IsComponent J' → X ≤ normalizer (J' : Set A) := fun J' hJ' =>
    X_le_normalizer_comp c.A4.prime c.A4.odd c.A4.pgroup hJ'
      (fun J₁ J₂ J₃ => F.two A a c.sec J₁ J₂ J₃)
  have hXJ : X ≤ normalizer (J : Set A) := hX J hJ
  have haJ : a ∈ normalizer (J : Set A) := by
    by_contra hna
    have hJ₂ : IsComponent (J.map (MulAut.conj a).toMonoidHom) := isComponent_conj hJ a
    have hne : J ≠ J.map (MulAut.conj a).toMonoidHom := fun h =>
      hna (mem_normalizer_of_map_conj_eq' h.symm)
    have hcomp2 : ∀ J₃ : Subgroup A, IsComponent J₃ →
        J₃ = J ∨ J₃ = J.map (MulAut.conj a).toMonoidHom := by
      intro J₃ h3
      by_contra hcon
      push Not at hcon
      exact F.two A a c.sec J (J.map (MulAut.conj a).toMonoidHom) J₃ hJ hJ₂ h3 hne hcon.1.symm
        hcon.2.symm
    have hlayer : layer A = J ⊔ J.map (MulAut.conj a).toMonoidHom := by
      apply le_antisymm
      · refine sSup_le fun J₃ h3 => ?_
        rcases hcomp2 J₃ h3 with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      · exact sup_le (le_sSup hJ) (le_sSup hJ₂)
    have hnorm : (J ⊔ J.map (MulAut.conj a).toMonoidHom).Normal := by
      have hc := CFSG.LocalCores.layer_characteristic (G := A)
      rw [← hlayer]
      infer_instance
    exact swap_false c.A4.prime c.A4.odd c.A4.pgroup c.z2 (fun g hg => c.inv g hg) c.op hJ hJ₂ hne
      hnorm hXJ (hX _ hJ₂) rfl hJX
  let d : SubData c J := ⟨hJ, hXJ, haJ, hJX⟩
  have hcompSl : Sl2Cl p (secZ a X J) (secX a X J) (secJ a X J) →
      ∀ J' : Subgroup A, IsComponent J' → J' ≤ ncl X → J' = J := by
    intro hsl J' hJ' hJ'K
    by_contra hne
    exact sl2_two F d hsl hJ' (Ne.symm hne) hJ'K
  rcases d.cases F with ha | hb | hc' | hd
  · rcases sl2_final F d (Or.inl ha) (hcompSl (Or.inl ha)) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases sl2_final F d (Or.inr hb) (hcompSl (Or.inr hb)) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inl (case_c_plus F d hc'))
  · exact Or.inr (Or.inr (Or.inl (case_d F hOut d hd)))

end Plus

@[expose] def Prop4_3Ep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X →
      ⁅layer (Sec H₀ H₁), X⁆ ≠ ⊥ →
      Concl43Ep k (zSec z H₀ hz H₁) p X

theorem prop_4_3Ep_of_hyp (hOut : L34DiagClosure)
    (hHyp : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → E4Hyp G z k) : Prop4_3Ep := by
  intro G _ _ z k S ctx H₀ H₁ _ hz p X sig hN
  have ha := prop_4_1a_of L199.ig_19_9 G z k S ctx H₀ H₁ hz p X sig
  have hb := prop_4_1b_of L199.ig_19_9 G z k S ctx H₀ H₁ hz p X sig
  have hz2 : zSec z H₀ hz H₁ * zSec z H₀ hz H₁ = 1 := by
    have h := orderOf_zSec ctx.orderOf_z hz H₁ sig.odd
    have h1 := pow_orderOf_eq_one (zSec z H₀ hz H₁)
    rw [h, pow_two] at h1
    exact h1
  exact prop4_3Ep_core (hHyp G z k S ctx) hOut
    (c := { sec := SecOfG.of_sig4B sig, A4 := sig.A, z2 := hz2, op := sig.op, a41 := ha, b41 := hb }) hN

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
