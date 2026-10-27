module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinT
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChain
public import CFSG.ClassicalInvolution.Asc77.AscT7S22Z
public import CFSG.ClassicalInvolution.Asc77.AscE187Img

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore IsSubnormal)
open scoped commutatorElement

namespace T7K

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)}

theorem hyp51At_of_twin_inner (hres : TwinSmallInner p) (hex : G2D4VertexExcl p f)
    {K₀ : Subgroup G} (hst : AscStand p f Ω K₀) {K K' : Subgroup G} {b d c : G}
    (hKΩ : K ∈ Ω) (hK'Ω : K' ∈ Ω) (hne : K' ≠ K)
    (hbK : IsUniqueInvolution K b) (hbK' : IsUniqueInvolution K' b)
    (hMK : K ∈ tqMembers Ω c) (hMK' : K' ∈ tqMembers Ω c)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hbB : b ∈ B) (hdB : d ∈ B) (hcB : c ∈ B)
    (hBgen : B = Subgroup.closure ({b, d, c} : Set G))
    (hc1 : c ≠ 1) (hbc : b ≠ c) (hd1 : d ≠ 1) (hdb : d ≠ b) (hd2 : d * d = 1)
    (hdsup : d ∈ exactCore c K ⊔ exactCore c K') :
    Hyp51At B c := by
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hcK : IsClassicalMember p f K b := isClassicalMember_of_twin hΩ hKΩ hbK
  have hcK' : IsClassicalMember p f K' b := isClassicalMember_of_twin hΩ hK'Ω hbK'
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) :=
    isPGroup_zpowers_of_sq_eq_one (by simpa only [pow_two] using hB.2 c hcB)
  have hnonab : ∃ x y : G, x * y ≠ y * x := exists_noncomm_of_isClassicalMember hcK
  have hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hnonab hc1
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    DeltaClosure.comm_of_mem_elemAbelian hB hx hy
  refine FrameVertex.hyp51At_of_witness_alpha hp hq hΩ.conjInvariant hΩ.classical
    (hst.below f hq) hc2 hnc hB hcB hc1 hbB hbK.ne_one hbc hMK hcK ?_
  intro D j hMj hmov
  have hM'j := vertexTwin_mem hΩ hc2 hB hcB hc1 hbB hbK.ne_one hbc hMK hMK' hcK' D j hmov
  have hG2 : D.tag j ≠ .G2 := fun h =>
    hex G Ω hΩ hst.aEmpty c hc2 D j (Or.inl h) K K' b hMK hMK' hcK hcK' hne hMj hM'j
  have hD4 : D.tag j ≠ .trialityD4 := fun h =>
    hex G Ω hΩ hst.aEmpty c hc2 D j (Or.inr h) K K' b hMK hMK' hcK hcK' hne hMj hM'j
  obtain ⟨hzC, R, R', x, x', hpair, hshape, hRM, hR'M, hψx⟩ := vertexTwin hp hq hΩ hc2 hB
    hcB hc1 hbB hbK.ne_one hbc hMK hMK' hcK hcK' hne D j hMj hmov hG2 hD4
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j with hψdef
  have hexp : D.exp j = f := (D.exp_eq j).resolve_right fun h => hD4 h.1
  have hq' : 5 ≤ p ^ D.exp j := by rw [hexp]; exact hq
  have hTI : TwinInnerAlpha p (D.exp j) (D.tag j) (D.rank j) :=
    twinInnerAlpha_of_shape hres hp hq' (D.admissible j) hshape
  have huC : d ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm d hdB c hcB)
  have hsup : oddQuotMk c ⟨d, huC⟩ ∈ R.map ψ ⊔ R'.map ψ := by
    rw [hRM, hR'M]
    exact TwinVertex.oddQuotMk_mem_sup (exactCore_le_centralizer c K)
      (exactCore_le_centralizer c K') hdsup huC
  have hun : oddQuotMk c ⟨d, huC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
    Subgroup.le_normalizer (sup_le (Subgroup.map_le_range ψ R) (Subgroup.map_le_range ψ R') hsup)
  have hu2 : oddQuotMk c ⟨d, huC⟩ * oddQuotMk c ⟨d, huC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨d, huC⟩ * ⟨d, huC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 := Subtype.ext hd2
    rw [this, map_one]
  have hu1 : oddQuotMk c ⟨d, huC⟩ ≠ 1 := by
    intro h
    have h' : oddQuotMk c ⟨d, huC⟩ = oddQuotMk c ⟨1, Subgroup.one_mem _⟩ := by
      rw [h]
      exact (map_one _).symm
    exact hd1 (eq_of_oddQuotMk_eq hB hdB (Subgroup.one_mem _) huC (Subgroup.one_mem _) h')
  have huz : oddQuotMk c ⟨d, huC⟩ ≠ ψ x := by
    rw [hψx]
    intro h
    exact hdb (eq_of_oddQuotMk_eq hB hdB hbB huC hzC h)
  have key := hTI (OddQuot c) ψ R R' x x' hpair (oddQuotMk c ⟨d, huC⟩) hun hsup hu2 hu1 huz
  have hψnorm : ∀ y : (compModel D j).K, ψ y ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
    FrameVertex.mem_normalizer_range ψ
  set T : Subgroup ↥(inducedAutOn ψ.range) := Subgroup.closure
    ({toInducedAutOn ψ.range ⟨oddQuotMk c ⟨d, huC⟩, hun⟩,
      toInducedAutOn ψ.range ⟨ψ x, hψnorm x⟩} : Set ↥(inducedAutOn ψ.range)) with hT
  have hS : ({b, d, c} : Set G) ⊆ Subgroup.centralizer ({c} : Set G) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg
    · rw [hg]; exact hzC
    · rw [hg]; exact huC
    · rw [hg]; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hbbar : oddQuotMk c ⟨b, hzC⟩ = ψ x := hψx.symm
  have hgen : ∀ s : G, s ∈ ({b, d, c} : Set G) → ∀ hs' : s ∈ Subgroup.centralizer ({c} : Set G),
      ∃ hn : oddQuotMk c ⟨s, hs'⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)),
        toInducedAutOn ψ.range ⟨oddQuotMk c ⟨s, hs'⟩, hn⟩ ∈ T := by
    intro s hs hs'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with hs | hs | hs
    · subst s
      refine ⟨by rw [hbbar]; exact hψnorm x, ?_⟩
      have h2 : (⟨oddQuotMk c ⟨b, hs'⟩, by rw [hbbar]; exact hψnorm x⟩ :
          ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) = ⟨ψ x, hψnorm x⟩ :=
        Subtype.ext hbbar
      rw [h2]
      exact Subgroup.subset_closure (by simp)
    · subst s
      exact ⟨hun, Subgroup.subset_closure (by simp)⟩
    · subst s
      obtain ⟨hcn, hc1'⟩ := oddQuotSelf_induced c ψ.range
      have h1 : oddQuotMk c ⟨c, hs'⟩ = Lemma52Proof.oddQuotSelf c := rfl
      refine ⟨by rw [h1]; exact hcn, ?_⟩
      have h2 : (⟨oddQuotMk c ⟨c, hs'⟩, by rw [h1]; exact hcn⟩ :
          ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) =
            ⟨Lemma52Proof.oddQuotSelf c, hcn⟩ := Subtype.ext h1
      rw [h2, hc1']
      exact T.one_mem
  have hψxB : ψ x ∈ modOdd c B := by
    rw [hψx]
    exact oddQuotMk_mem_modOdd hbB hzC
  rw [hBgen] at hψxB
  refine (congrArg alphaOf (le_antisymm ?_ ?_)).trans key
  · rw [hBgen]
    exact inducedImage_modOdd_closure_le hS ψ.range T (fun s hs => hgen s hs (hS hs))
  · refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact ⟨⟨oddQuotMk c ⟨d, huC⟩, hun⟩,
        Subgroup.mem_subgroupOf.mpr (oddQuotMk_mem_modOdd hdB huC), rfl⟩
    · rw [hg]
      exact ⟨⟨ψ x, hψnorm x⟩, Subgroup.mem_subgroupOf.mpr (by rw [hBgen] at *; exact hψxB), rfl⟩


omit [IsSimpleGroup G] in
theorem oddQuotMk_comm_of_trivialOnQuot {z a : G} {K : Subgroup G}
    (haz : a ∈ Subgroup.centralizer ({z} : Set G))
    (hat : a ∈ trivialOnQuot K) (hKC : IsSubnormal K (Subgroup.centralizer ({z} : Set G)))
    {y : OddQuot z} (hy : y ∈ modOdd z K) :
    oddQuotMk z ⟨a, haz⟩ * y = y * oddQuotMk z ⟨a, haz⟩ := by
  obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy
  have hkK : (k : G) ∈ K := hk
  have hcomm : ⁅a, (k : G)⁆ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
    oddCoreIn_le_of_isSubnormal hKC ((mem_trivialOnQuot_iff.mp hat).2 _ hkK)
  have hC : ⁅a, (k : G)⁆ ∈ Subgroup.centralizer ({z} : Set G) :=
    oddCoreIn_le _ hcomm
  have h1 := oddQuotMk_eq_one_of_mem_oddCoreIn hcomm hC
  have h2 : oddQuotMk z ⟨⁅a, (k : G)⁆, hC⟩ =
      oddQuotMk z ⟨a, haz⟩ * oddQuotMk z k * (oddQuotMk z ⟨a, haz⟩)⁻¹ * (oddQuotMk z k)⁻¹ := by
    have : (⟨⁅a, (k : G)⁆, hC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨a, haz⟩ * k * ⟨a, haz⟩⁻¹ * k⁻¹ := by
      apply Subtype.ext
      simp [commutatorElement_def]
    rw [this]
    simp only [map_mul, map_inv]
  rw [h2] at h1
  have h3 : ⁅oddQuotMk z ⟨a, haz⟩, oddQuotMk z k⁆ = 1 := by
    rw [commutatorElement_def]
    exact h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h3


omit [IsSimpleGroup G] in
theorem hyp51At_of_twin_vertex_z {K₀ : Subgroup G} (hst : AscStand p f Ω K₀)
    {K K' : Subgroup G} {z x y e₁ : G} (hKΩ : K ∈ Ω) (hK'Ω : K' ∈ Ω)
    (hzK : IsUniqueInvolution K z) (hzK' : IsUniqueInvolution K' z)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hzB : z ∈ B)
    (hxK : x ∈ K) (hyK' : y ∈ K') (hxyB : x * y ∈ B) (hxy1 : x * y ≠ 1) (hxyz : x * y ≠ z)
    (he₁B : e₁ ∈ B) (he₁1 : e₁ ≠ 1) (he₁z : e₁ ≠ z)
    (he₁K : e₁ ∈ trivialOnQuot K) (he₁K' : e₁ ∈ trivialOnQuot K') :
    Hyp51At B z := by
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hc₁ : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hKΩ hzK
  have hc₂ : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ hK'Ω hzK'
  have hz1 : z ≠ 1 := hzK.ne_one
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := T7S22.le_centralizer_of_classical hc₁
  have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := T7S22.le_centralizer_of_classical hc₂
  have hxC : x * y ∈ Subgroup.centralizer ({z} : Set G) :=
    (Subgroup.centralizer ({z} : Set G)).mul_mem (hKz hxK) (hK'z hyK')
  have he₁C : e₁ ∈ Subgroup.centralizer ({z} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hzB he₁B
  have key : ∀ M : Subgroup G, IsSubnormal M (Subgroup.centralizer ({z} : Set G)) →
      e₁ ∈ trivialOnQuot M → ¬ MovedByAll B z (modOdd z M) := by
    intro M hMs hmt hmov
    have hxm : oddQuotMk z ⟨e₁, he₁C⟩ ∈ modOdd z B := oddQuotMk_mem_modOdd he₁B he₁C
    have hnot := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hz1 he₁B he₁1 he₁z he₁C
    obtain ⟨w, hw, hwne⟩ := hmov _ hxm hnot
    exact hwne (oddQuotMk_comm_of_trivialOnQuot he₁C hmt hMs hw)
  have hno : ∀ L : Subgroup (OddQuot z), CFSG.IsComponent L → MovedByAll B z L → False := by
    intro L hL hmov
    rcases T7S22.eq_or_eq_of_movedByAll hq hc₁ hc₂ hB hzB hz1 hxK hyK' hxyB hxy1 hxyz hxC hL
      hmov with rfl | rfl
    · exact key K hc₁.subnormal he₁K hmov
    · exact key K' hc₂.subnormal he₁K' hmov
  exact ⟨fun L₁ L₂ h1 _ m1 _ => (hno L₁ h1 m1).elim, fun L hL hm => (hno L hL hm).elim⟩

end T7K

end CFSG.ClassicalInvolution.Asc77
