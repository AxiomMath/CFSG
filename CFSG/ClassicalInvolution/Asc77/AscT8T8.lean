module

public import CFSG.ClassicalInvolution.Asc77.AscT8T7
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHFinal3
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore IsSubnormal)
open scoped commutatorElement MatrixGroups

namespace T8T

section Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)}


theorem hyp51At_of_nonTwin_pair {K₀ : Subgroup G} (hst : AscStand p f Ω K₀) {B : Subgroup G}
    (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8) {c b b' : G}
    (hBgen : B = Subgroup.closure ({b, b', c} : Set G)) (hc1 : c ≠ 1) (hb1 : b ≠ 1)
    (hb'1 : b' ≠ 1) (hbb' : b ≠ b') {M M' : Subgroup G} (hM : M ∈ tqMembers Ω c)
    (hM' : M' ∈ tqMembers Ω c) (hMb : IsClassicalMember p f M b)
    (hM'b : IsClassicalMember p f M' b') {R' : Subgroup G} (hR' : IsSylow2In R' M')
    (hR'c : R' ≤ Subgroup.centralizer ({c} : Set G))
    (hR'N : R' ≤ Subgroup.normalizer (M : Set G)) : Hyp51At B c := by
  classical
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hbB : b ∈ B := hBgen ▸ Subgroup.subset_closure (by simp)
  have hb'B : b' ∈ B := hBgen ▸ Subgroup.subset_closure (by simp)
  have hcB : c ∈ B := hBgen ▸ Subgroup.subset_closure (by simp)
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    DeltaClosure.comm_of_mem_elemAbelian hB hx hy
  have hb2 : b * b = 1 := Lemma52Proof.mul_self_eq_one_of_mem hB hbB
  have hb'2 : b' * b' = 1 := Lemma52Proof.mul_self_eq_one_of_mem hB hb'B
  have hc2' : c * c = 1 := Lemma52Proof.mul_self_eq_one_of_mem hB hcB
  have hbb'c : b * b' = b' * b := hcomm b hbB b' hb'B
  have hD : IsElemAbelian2 (Subgroup.closure ({b, b'} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hb2 hb'2 hb1 hb'1 hbb' hbb'c
  have hcn : c ∉ Subgroup.closure ({b, b'} : Set G) := by
    intro h
    have hle : B ≤ Subgroup.closure ({b, b'} : Set G) := by
      rw [hBgen, Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact h
    have hge : Subgroup.closure ({b, b'} : Set G) ≤ B := by
      rw [hBgen]
      exact Subgroup.closure_mono (by intro v hv; rcases hv with rfl | rfl <;> simp)
    have h4 := hD.1
    rw [← le_antisymm hle hge, hB8] at h4
    omega
  have hbc : b ≠ c := fun h => hcn (h ▸ Subgroup.subset_closure (by simp))
  have hb'c : b' ≠ c := fun h => hcn (h ▸ Subgroup.subset_closure (by simp))
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hc2'
  have hnonab : ∃ x y : G, x * y ≠ y * x := exists_noncomm_of_isClassicalMember hMb
  have hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G := Balance.not_subset_center_of_ne_one hnonab hc1
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) := Lemma52Proof.le_centralizer_of_mem hB hcB hbB
  have hb'C : b' ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB hb'B
  refine FrameVertex.hyp51At_of_witness_alpha hp hq hΩ.conjInvariant hΩ.classical
    (hst.below f hq) hc2 hnc hB hcB hc1 hbB hb1 hbc hM hMb ?_
  intro D j hMj hmov
  have hs' : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨M, hM⟩
  have hmem : ∀ N ∈ tqMembers Ω c, exactCore c N ∈ centMembers (exactFamily Ω c) c :=
    fun N hN => ⟨exactCore_mem_exactFamily hN, exactCore_le_centralizer c N⟩
  have hM'j := vertexTwin_mem hΩ hc2 hB hcB hc1 hb'B hb'1 hb'c hM hM' hM'b D j hmov
  obtain ⟨R₁, hR₁, hR₁M⟩ := exists_fundamental_of_modOdd_le_sec hs' D j (hmem M hM) hMj
  obtain ⟨R₂, hR₂, hR₂M⟩ := exists_fundamental_of_modOdd_le_sec hs' D j (hmem M' hM') hM'j
  have hnbr := secFam_nbr hp hq hΩ hc2 hM hM' hMb hM'b hbb' hR' hR'c hR'N
  have hcommL := commutes_modOdd_of_nbr hp hq hΩ hc2 hs' D hM hM' hnbr
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j with hψ
  have hbE : b ∈ exactCore c M := mem_exactCore hMb hc2 hM.2
  have hb'E : b' ∈ exactCore c M' := mem_exactCore hM'b hc2 hM'.2
  have hU := TwinVertex.isUniqueInvolution_exactCore hp hq hMb hc2 hM.2
  have hU' := TwinVertex.isUniqueInvolution_exactCore hp hq hM'b hc2 hM'.2
  set z : OddQuot c := oddQuotMk c ⟨b, hbC⟩ with hzdef
  set z' : OddQuot c := oddQuotMk c ⟨b', hb'C⟩ with hz'def
  have hUz : IsUniqueInvolution (modOdd c (exactCore c M)) z :=
    TwinVertex.isUniqueInvolution_modOdd hU hbC
  have hUz' : IsUniqueInvolution (modOdd c (exactCore c M')) z' :=
    TwinVertex.isUniqueInvolution_modOdd hU' hb'C
  have hzR : z ∈ modOdd c (exactCore c M) := oddQuotMk_mem_modOdd hbE hbC
  have hz'R : z' ∈ modOdd c (exactCore c M') := oddQuotMk_mem_modOdd hb'E hb'C
  have hzz' : z ≠ z' := fun h => hbb' (eq_of_oddQuotMk_eq hB hbB hb'B hbC hb'C h)
  have hne : R₁.map ψ ≠ R₂.map ψ := by
    rw [hR₁M, hR₂M]
    intro h
    have hz'mem : z' ∈ modOdd c (exactCore c M) := h ▸ hz'R
    rcases hUz.unique z' hz'mem hUz'.sq with h1 | h1
    · exact hUz'.ne_one h1
    · exact hzz' h1.symm
  have hnot : ¬ z ∈ R₂.map ψ := by
    rw [hR₂M]
    intro h
    rcases hUz'.unique z h hUz.sq with h1 | h1
    · exact hUz.ne_one h1
    · exact hzz' h1
  have hcl : IsClassicalMember p f (R₁.map ψ) z := by
    rw [hR₁M]
    exact (isClassicalMember_exactCore_subgroupOf hMb hc2 hM.2
      (exactCore_le_centralizer c M) le_rfl).map_oddQuotient
  have hΦ : HypOmega p f (secFam Ω c) := hypOmega_secFam hp hq hΩ hc2 hs' D
  have hσ := sectionQuotientHom_injective hs'.normalizes
  have sl2 : ∀ N ∈ tqMembers Ω c,
      Nonempty (↥(modOdd c (exactCore c N)) ≃* SL(2, GaloisField p f)) := by
    intro N hN
    have hNc := hmem N hN
    have hNY : exactCore c N ≤ centralizingLayer (exactFamily Ω c) {c} := le_centLayer hNc
    have hK : modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c N) ∈
        secFam Ω c := ⟨_, ⟨exactCore c N, hNc, hNY, rfl⟩, rfl⟩
    obtain ⟨z₀, hz₀⟩ := hΦ.classical _ hK
    obtain ⟨e⟩ := hz₀.nonempty_equiv_sl2 (hΦ.exact _ hK)
    rw [← map_sectionQuotientHom_modOddIn hs'.normalizes hNc]
    exact ⟨((modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c N)).equivMapOfInjective
      _ hσ).symm.trans e⟩
  have heK : Nonempty (↥(R₁.map ψ) ≃* SL(2, GaloisField p f)) := by
    rw [hR₁M]
    exact sl2 M hM
  have heK' : Nonempty (↥(R₂.map ψ) ≃* SL(2, GaloisField p f)) := by
    rw [hR₂M]
    exact sl2 M' hM'
  have hcommL' : Commutes (R₁.map ψ) (R₂.map ψ) := by
    rw [hR₁M, hR₂M]
    exact hcommL
  have hUz1 : IsUniqueInvolution (R₁.map ψ) z := by
    rw [hR₁M]
    exact hUz
  have hz2 : z * z = 1 := hUz.sq
  have hz'2 : z' * z' = 1 := hUz'.sq
  have hzz'comm : z * z' = z' * z := by
    rw [hzdef, hz'def, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hcomm b hbB b' hb'B))
  set A : Subgroup (OddQuot c) := Subgroup.closure ({z, z'} : Set (OddQuot c)) with hA
  have hAel : IsElemAbelian2 A 2 :=
    T7A.isElemAbelian2_closure_pair hz2 hz'2 hUz.ne_one hUz'.ne_one hzz' hzz'comm
  have hAle : A ≤ R₁.map ψ ⊔ R₂.map ψ := by
    rw [hA, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact Subgroup.mem_sup_left (hR₁M ▸ hzR)
    · exact Subgroup.mem_sup_right (hR₂M ▸ hz'R)
  have hzA : z ∈ A := Subgroup.subset_closure (by simp)
  have hAB : A ≤ modOdd c B := by
    rw [hA, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact oddQuotMk_mem_modOdd hbB hbC
    · exact oddQuotMk_mem_modOdd hb'B hb'C
  have hbb'B : b * b' ∈ B := B.mul_mem hbB hb'B
  have hbb'C : b * b' ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB hbb'B
  have hbb'1 : b * b' ≠ 1 := by
    intro h
    have : b' = b⁻¹ := by
      have := eq_inv_of_mul_eq_one_right h
      exact this
    rw [this, inv_eq_of_mul_eq_one_right hb2] at hbb'
    exact hbb' rfl
  have hbb'c : b * b' ≠ c := fun h =>
    hcn (h ▸ Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have hAmov : ∀ a ∈ A, a ≠ 1 → ¬ ∀ x ∈ ψ.range, a * x = x * a := by
    intro a ha ha1 hall
    have haB : a ∈ modOdd c B := hAB ha
    have hnotzp : a ∉ modOdd c (Subgroup.zpowers c) := by
      rcases T8.mem_closure_pair_involutions hz2 hz'2 hzz'comm ha with h | h | h | h
      · exact absurd h ha1
      · rw [h]
        exact Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hbB hb1 hbc hbC
      · rw [h]
        exact Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hb'B hb'1 hb'c hb'C
      · have hmul : z * z' = oddQuotMk c ⟨b * b', hbb'C⟩ := by
          rw [hzdef, hz'def, ← map_mul]
          rfl
        rw [h, hmul]
        exact Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hbb'B hbb'1 hbb'c hbb'C
    obtain ⟨y, hy, hxy⟩ := hmov a haB hnotzp
    exact hxy (hall y hy)
  have key := t5BaseAtC_nt_all (p := p) (f := f) (D.tag j) (D.rank j) (D.exp j) hp hq
    (D.isFundTag j) (D.admissible j) (D.exp_eq j) (OddQuot c) ψ
    (secComponentHom_ker_le_center _ D j) R₁ hR₁ R₂ hR₂ heK heK' hne hcommL' z hUz1 hcl hnot A
    hAel hAle hzA hAmov
  have hzrange : z ∈ ψ.range := by
    obtain ⟨x, -, hx⟩ := (hR₁M ▸ hzR : z ∈ R₁.map ψ)
    exact ⟨x, hx⟩
  have hz'range : z' ∈ ψ.range := by
    obtain ⟨x, -, hx⟩ := (hR₂M ▸ hz'R : z' ∈ R₂.map ψ)
    exact ⟨x, hx⟩
  have hS : ({b, b', c} : Set G) ⊆ Subgroup.centralizer ({c} : Set G) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact hbC
    · exact hb'C
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hz'A : z' ∈ A := Subgroup.subset_closure (by simp)
  have hgen : ∀ (s : G) (hs : s ∈ ({b, b', c} : Set G)),
      ∃ hn : oddQuotMk c ⟨s, hS hs⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)),
        toInducedAutOn ψ.range ⟨oddQuotMk c ⟨s, hS hs⟩, hn⟩ ∈ inducedImage ψ.range A := by
    intro s hs0
    have hs := hs0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with h | h | h
    · have e : (⟨s, hS hs0⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = ⟨b, hbC⟩ :=
        Subtype.ext h
      have hn : oddQuotMk c ⟨s, hS hs0⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := by
        rw [e]
        exact Subgroup.le_normalizer hzrange
      refine ⟨hn, ⟨⟨_, hn⟩, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩⟩
      show oddQuotMk c ⟨s, hS hs0⟩ ∈ A
      rw [e]
      exact hzA
    · have e : (⟨s, hS hs0⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = ⟨b', hb'C⟩ :=
        Subtype.ext h
      have hn : oddQuotMk c ⟨s, hS hs0⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := by
        rw [e]
        exact Subgroup.le_normalizer hz'range
      refine ⟨hn, ⟨⟨_, hn⟩, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩⟩
      show oddQuotMk c ⟨s, hS hs0⟩ ∈ A
      rw [e]
      exact hz'A
    · obtain ⟨hcn', hc1'⟩ := oddQuotSelf_induced c ψ.range
      have e : (⟨s, hS hs0⟩ : ↥(Subgroup.centralizer ({c} : Set G))) =
          ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := Subtype.ext h
      have h1 : oddQuotMk c ⟨s, hS hs0⟩ = Lemma52Proof.oddQuotSelf c := by
        rw [e]
        rfl
      refine ⟨by rw [h1]; exact hcn', ?_⟩
      have h2 : (⟨oddQuotMk c ⟨s, hS hs0⟩, by rw [h1]; exact hcn'⟩ :
          ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) =
            ⟨Lemma52Proof.oddQuotSelf c, hcn'⟩ := Subtype.ext h1
      rw [h2, hc1']
      exact (inducedImage ψ.range A).one_mem
  have hle1 : inducedImage ψ.range (modOdd c B) ≤ inducedImage ψ.range A := by
    rw [hBgen]
    exact inducedImage_modOdd_closure_le hS ψ.range _ hgen
  have hle2 : inducedImage ψ.range A ≤ inducedImage ψ.range (modOdd c B) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ hAB)
  rw [le_antisymm hle1 hle2]
  exact key

end Vertex

end T8T

end CFSG.ClassicalInvolution.Asc77
