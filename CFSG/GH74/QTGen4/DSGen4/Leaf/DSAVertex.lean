module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Surv10

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private theorem dsa_le_normalizer_of_conj_mem {G : Type} [Group G] {H X : Subgroup G}
    (h : ∀ g ∈ H, ∀ x ∈ X, g * x * g⁻¹ ∈ X) : H ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (H.inv_mem hg) (g * x * g⁻¹) hx
  simpa [mul_assoc] using this

private theorem dsa_le_normalizer_commutator {G : Type} [Group G] {P Q L : Subgroup G}
    (hQ : P ≤ Subgroup.normalizer (Q : Set G)) (hL : P ≤ Subgroup.normalizer (L : Set G)) :
    P ≤ Subgroup.normalizer ((⁅Q, L⁆ : Subgroup G) : Set G) := by
  have key : ∀ g ∈ P, ∀ x ∈ ⁅Q, L⁆, g * x * g⁻¹ ∈ ⁅Q, L⁆ := by
    intro g hg
    have hle : ⁅Q, L⁆ ≤ (⁅Q, L⁆).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro q hq l hl
      rw [Subgroup.mem_comap]
      have h1 : g * q * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQ hg) q).mp hq
      have h2 : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hL hg) l).mp hl
      have e : (MulAut.conj g).toMonoidHom ⁅q, l⁆ = ⁅g * q * g⁻¹, g * l * g⁻¹⁆ :=
        map_commutatorElement (MulAut.conj g).toMonoidHom q l
      rw [e]
      exact Subgroup.commutator_mem_commutator h1 h2
    intro x hx
    exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have h := key g⁻¹ (P.inv_mem hg) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h

private theorem dsa_commutator_eq_top_of_quotient {H : Type} [Group H] (N : Subgroup H) [N.Normal]
    (hN : N ≤ commutator H) (hq : commutator (H ⧸ N) = ⊤) : commutator H = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hmap : (commutator H).map (QuotientGroup.mk' N) = commutator (H ⧸ N) := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have hx : QuotientGroup.mk' N x ∈ (commutator H).map (QuotientGroup.mk' N) := by
    rw [hmap, hq]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hyN : y⁻¹ * x ∈ N := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
    exact hyx
  simpa using (commutator H).mul_mem hy (hN hyN)

theorem leafDSAVertex [DSLeaf LeafDSANoField] [DSLeaf LeafDSACaseIOffender] [DSLeaf LeafDSACaseIFrattini] [DSLeaf LeafZiStructure] [DSLeaf LeafZiChief] [DSLeaf LeafFrattiniChief] [DSLeaf LeafShort2OfA5] [DSLeaf LeafLin2OfNatural] [DSLeaf LeafSylowS] : LeafDSAVertex := by
  intro G _ _ L1 L2 S h c1 c2
  obtain ⟨hS1, -, hBS⟩ := dsa_no_field h
  have hQE : dsQ L1 L2 S = dsZi L1 S := (dsa_case_i_frattini h c1 c2).1
  have hnat0 : NatSec L1 ⊥ (dsZi L1 S) := (dsa_case_i_offender h c1 c2).2.2.1
  have hZS : ZSetting L1 L2 S := ⟨h.hyp, hBS⟩
  obtain ⟨hZ0, hZZ, -, -, -, -, -⟩ := zi_structure hZS
  have hq : IsL2Quot 2 (oTwoQuot ↥L1) := (A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1).quot
  obtain ⟨hA, -, -, -⟩ := zi_chief hZS hq c1
  have hle : ⁅dsZi L1 S, L1⁆ ≤ dsZi L1 S ⊓ L1 :=
    CFSG.Quasithin.F7.commutator_le_inf_of_normalizes
      (fun e he => hA.norm_L (hA.E_le he)) (fun l hl => hA.norm_E (hA.le hl))
  have hEL : ⁅dsZi L1 S, L1⁆ = dsZi L1 S := by
    rcases hA.irred ⁅dsZi L1 S, L1⁆ bot_le (hle.trans inf_le_left)
        (dsa_le_normalizer_commutator hA.norm_E hA.norm_L) with h0 | h0
    · exact absurd h0 c1
    · exact h0
  have hEle : dsZi L1 S ≤ L1 := by
    have h1 := hle.trans inf_le_right
    rwa [hEL] at h1
  have hpc : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = dsZi L1 S := hQE
  have hpc1 : pCoreOf 2 L1 = dsZi L1 S := by
    have h1 := F1.inf_pCoreOf_parabolic_eq h.hyp
    rw [hpc, inf_eq_left.mpr hEle] at h1
    exact h1.symm
  have hcardE : Nat.card (pCoreOf 2 L1) = 16 := by
    rw [hpc1, ← Subgroup.relIndex_bot_left]
    exact hA.card
  have hEab : IsElemAbelian 2 (pCoreOf 2 L1) := by
    rw [hpc1]
    obtain ⟨-, hcc, hsq⟩ := hA.sec
    have hcomm : ∀ a ∈ dsZi L1 S, ∀ b ∈ dsZi L1 S, a * b = b * a := by
      intro a ha b hb
      have h1 : ⁅a, b⁆ ∈ (⊥ : Subgroup G) := hcc (Subgroup.commutator_mem_commutator ha hb)
      rw [Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    refine ⟨isMulCommutative_iff.2 fun a b => Subtype.ext (hcomm a a.2 b b.2), fun x hx => ?_⟩
    have h2 := hsq x hx
    rwa [Subgroup.mem_bot] at h2
  have hCh : CharTwo (L1 ⊔ bigB L1 L2 S) := F1.parabolic_charTwo h.hyp
  have hCh1 : CharTwo L1 := by
    have hC := hCh
    unfold CharTwo at hC ⊢
    rw [hpc] at hC
    rw [hpc1]
    intro x hx
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
    have hLP : L1 ≤ L1 ⊔ bigB L1 L2 S := le_sup_left
    exact hC (Subgroup.mem_inf.mpr ⟨hLP hxL, hxC⟩)
  have hShort : IsShort2 L1 := short2_of_a5 hq hCh1 hEab hcardE
  have hNat : NatSec L1 ⊥ (pCoreOf 2 L1) := by
    rw [hpc1]
    exact hnat0
  have hLin : IsLin2Type L1 2 := lin2_of_natural hq hCh1 hEab hcardE hNat
  have hL1top : (⊤ : Subgroup ↥L1).map L1.subtype = L1 := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmapL : (commutator ↥L1).map L1.subtype = ⁅L1, L1⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, hL1top]
  have hEsub : dsZi L1 S ≤ ⁅L1, L1⁆ := by
    have h1 := Subgroup.commutator_mono hEle (le_refl L1)
    rwa [hEL] at h1
  have hN : pCore 2 ↥L1 ≤ commutator ↥L1 := by
    intro n hn
    have hnE : (n : G) ∈ dsZi L1 S := by
      have h1 : (n : G) ∈ pCoreOf 2 L1 := Subgroup.mem_map_of_mem L1.subtype hn
      rwa [hpc1] at h1
    have h2 : (n : G) ∈ (commutator ↥L1).map L1.subtype := by
      rw [hmapL]
      exact hEsub hnE
    obtain ⟨c, hc, hcn⟩ := Subgroup.mem_map.mp h2
    have hcn' : c = n := Subtype.ext hcn
    rw [← hcn']
    exact hc
  obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
  haveI hA5 : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  haveI hQp : Group.IsPerfect (oTwoQuot ↥L1) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcommL1 : commutator ↥L1 = ⊤ :=
    dsa_commutator_eq_top_of_quotient (pCore 2 ↥L1) hN (Group.isPerfect_def.mp hQp)
  have hperf : perfectCore L1 = L1 := by
    apply perfectCore_eq_self_of_perfect
    rw [← hmapL, hcommL1, hL1top]
  have hSL : S ≤ L1 := by
    calc S = (S ⊓ L1) ⊔ dsQ L1 L2 S := hS1
      _ ≤ L1 := sup_le inf_le_right (by rw [hQE]; exact hEle)
  have hWP : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer
      ((dsZi L1 S ⊓ Subgroup.centralizer (L1 : Set G) : Subgroup G) : Set G) := by
    refine dsa_le_normalizer_of_conj_mem fun g hg x hx => ?_
    obtain ⟨hxE, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hA.norm_E hg) x).mp hxE, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L1 := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hA.norm_L ((L1 ⊔ bigB L1 L2 S).inv_mem hg)) l).mp hl
      simpa [mul_assoc] using h1
    have hc := Subgroup.mem_centralizer_iff.mp hxC (g⁻¹ * l * g) hl'
    calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * l := by group
  have hZ : ¬ centerOf S ≤ Subgroup.centralizer (L1 : Set G) := by
    intro hcen
    rcases hA.irred (dsZi L1 S ⊓ Subgroup.centralizer (L1 : Set G)) bot_le inf_le_left hWP with hW | hW
    · have h1 : dsZ S ≤ dsZi L1 S ⊓ Subgroup.centralizer (L1 : Set G) :=
        le_inf hZZ ((dsZ_le_center S).trans hcen)
      rw [hW] at h1
      exact hZ0 (le_bot_iff.mp h1)
    · have hEC : dsZi L1 S ≤ Subgroup.centralizer (L1 : Set G) :=
        (le_of_eq hW.symm).trans inf_le_right
      exact c1 (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hEC)
  exact ⟨hShort, hLin, hperf, hSL, hZ⟩

end CFSG.GH74.QTGen4.DSGen4
