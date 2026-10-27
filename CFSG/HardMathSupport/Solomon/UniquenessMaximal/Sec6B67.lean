module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.LocalAnalysis.GLTheoremB.Lemma23Proof
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def InputL34Cover : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    IsLThreeFour (Y ⧸ CFSG.pCore 3 Y) → IsLThreeFour Y ∨ IsSLThreeFour Y

theorem isQuasisimple_of_mulEquiv' {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (h : CFSG.Open.IsQuasisimple H) : CFSG.Open.IsQuasisimple K := by
  obtain ⟨hc, hs⟩ := h
  refine ⟨?_, ?_⟩
  · have : (commutator H).map e.toMonoidHom = commutator K := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]
    rw [← this, hc, Subgroup.map_top_of_surjective _ e.surjective]
  · exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (Subgroup.center H) (Subgroup.center K) e
        (Subgroup.map_center_eq e))).mp hs

section Quasisimple

variable {G : Type*} [Group G] [Finite G]

theorem isQuasisimple_quotient_of_glaPComponent {p : ℕ} (hp : p.Prime) {X K : Subgroup G}
    (hK : GLAPComponent p X K) :
    CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore p ↥K) := by
  set φ : ↥K →* ↥X ⧸ GLAPPrimeCore p ↥X :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X)).comp (Subgroup.inclusion hK.1) with hφ
  have hinf := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hK.2.1
  have hker : φ.ker = GLAPPrimeCore p ↥K := by
    ext k
    have h1 : k ∈ GLAPPrimeCore p ↥K ↔ (k : G) ∈ GLAPPrimeCoreOf p K := by
      unfold GLAPPrimeCoreOf
      constructor
      · intro h
        exact Subgroup.mem_map.2 ⟨k, h, rfl⟩
      · intro h
        obtain ⟨k', hk', hkk⟩ := Subgroup.mem_map.1 h
        have : k' = k := Subtype.ext hkk
        exact this ▸ hk'
    have h2 : (k : G) ∈ GLAPPrimeCoreOf p K ↔ (k : G) ∈ GLAPPrimeCoreOf p X := by
      rw [← hinf]
      exact ⟨fun h => ((Subgroup.mem_inf.1 h).2), fun h => Subgroup.mem_inf.2 ⟨k.2, h⟩⟩
    have h3 : (k : G) ∈ GLAPPrimeCoreOf p X ↔ Subgroup.inclusion hK.1 k ∈ GLAPPrimeCore p ↥X := by
      unfold GLAPPrimeCoreOf
      constructor
      · intro h
        obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.1 h
        have : x = Subgroup.inclusion hK.1 k := Subtype.ext hxk
        exact this ▸ hx
      · intro h
        exact Subgroup.mem_map.2 ⟨_, h, rfl⟩
    rw [h1, h2, h3, MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hrange : φ.range = (K.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hq : CFSG.Open.IsQuasisimple ↥φ.range := by
    have := hK.2.2.1.2.2
    rw [← hrange] at this
    exact this
  have e : (↥K ⧸ GLAPPrimeCore p ↥K) ≃* ↥φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  exact isQuasisimple_of_mulEquiv' e.symm hq

end Quasisimple

section Main

variable {G : Type} [Group G] [Finite G]

theorem le_glbCore_of_isInGOne {B K : Subgroup G} (h : IsInGOne 3 B K) : K ≤ GLBCore 3 3 B := by
  have hK : K ≤ bClosure B K := by
    refine le_trans ?_ (le_iSup₂ (f := fun (b : G) (_ : b ∈ B) => GLBConj b K) 1 B.one_mem)
    simp only [GLBConj, inv_one, map_one]
    exact fun x hx => ⟨x, hx, rfl⟩
  have hcore : coreIn 3 3 B (bClosure B K) ≤ GLBCore 3 3 B := by
    refine iSup₂_le fun Q hQ => ?_
    exact inf_le_right.trans (le_sSup ⟨Q, hQ.1, hQ.2, rfl⟩)
  exact hK.trans (h ▸ hcore)

omit [Finite G] in
theorem isLThreeFour_quotient_of_oPrimeP {K : Subgroup G}
    (h : IsLThreeFour (↥K ⧸ CFSG.HardMathSupport.Solomon.LocalBalance.oPrimeP 3 ↥K)) :
    IsLThreeFour ((↥K ⧸ GLAPPrimeCore 3 ↥K) ⧸ CFSG.pCore 3 (↥K ⧸ GLAPPrimeCore 3 ↥K)) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  refine ⟨F, hF, hfin, hcard, ⟨?_⟩⟩
  set N := GLAPPrimeCore 3 ↥K
  set M := CFSG.HardMathSupport.Solomon.LocalBalance.oPrimeP 3 ↥K with hM
  have hNM : N ≤ M := by
    intro n hn
    show QuotientGroup.mk' N n ∈ CFSG.pCore 3 (↥K ⧸ N)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).2 hn]
    exact one_mem _
  have hmap : M.map (QuotientGroup.mk' N) = CFSG.pCore 3 (↥K ⧸ N) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _
  exact ((QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient N M hNM)).trans e

open CFSG.HardMathSupport.Solomon.LocalBalance in
theorem prop67_of_lemma31 (h31 : Lemma31) (hL34 : InputL34Cover) (_hON : InputONGroup)
    (hS : GLStanding G 4 3) {B : Subgroup G} (hB : IsBOneMax 3 B) : Prop67Out B := by
  intro x hxB hx1 K hK hnslob hKM
  have hsc : IsSCp 3 ⊤ B := lemma23_proved G 4 3 hS B hB
  refine ⟨⟨x, hxB, hx1, hK⟩, ?_, hKM⟩
  have hq := isQuasisimple_quotient_of_glaPComponent Nat.prime_three hK
  rcases h31 G 4 3 hS B hB.1 hsc x hxB hx1 K hK with h | h | h | h | h
  · exact absurd h hnslob
  · exact absurd (le_glbCore_of_isInGOne h) hKM
  · have h3 := isLThreeFour_quotient_of_oPrimeP h.2.2.1
    rcases hL34 _ hq h3 with h4 | h4
    · exact Or.inl h4
    · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr (h.2.2.1))
  · exact absurd h.1 (by norm_num)

end Main

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
