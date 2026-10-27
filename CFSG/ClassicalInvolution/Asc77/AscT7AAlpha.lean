module

public import CFSG.ClassicalInvolution.Asc77.AscT7AFrame
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
public import CFSG.ClassicalInvolution.Asc77.AscT3Sym

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace T7A

omit [Finite G] in
theorem conjSub_closure_pair (g a b : G) :
    conjSub g (Subgroup.closure ({a, b} : Set G)) =
      Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹} : Set G) := by
  unfold conjSub
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem mem_omegaOfSet_of_mem_kPerp (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ KPerp Ω K) (hJnot : J ∉ twinSet Ω K) :
    J ∈ omegaOfSet Ω (twinSet Ω K) := by
  have hJΩ : J ∈ Ω := by
    rcases Set.mem_insert_iff.mp hJ with h | h
    · exact h ▸ hK
    · exact h.1
  refine ⟨hJΩ, fun L hL => ?_⟩
  have hKL := (l6_3 p f hp hq G Ω hΩ K hK L hL).1
  have hJL : J ∈ KPerp Ω L := hKL ▸ hJ
  rcases Set.mem_insert_iff.mp hJL with h | h
  · exact absurd (h ▸ hL) hJnot
  · exact h

omit [Finite G] in
theorem mem_dComp_of_mem_omegaNbr {K J : Subgroup G} (hJ : J ∈ omegaNbr Ω K) :
    J ∈ dComp Ω K :=
  Relation.ReflTransGen.single ⟨hJ.1, Or.inl hJ⟩

omit [Finite G] in
theorem mem_dComp_of_mem_kPerp {K J : Subgroup G} (hJ : J ∈ KPerp Ω K) : J ∈ dComp Ω K := by
  rcases Set.mem_insert_iff.mp hJ with h | h
  · rw [h]
    exact Relation.ReflTransGen.refl
  · exact mem_dComp_of_mem_omegaNbr h

omit [Finite G] in
theorem mem_of_mem_dComp {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ dComp Ω K) : J ∈ Ω := by
  induction hJ with
  | refl => exact hK
  | tail _ hbc _ => exact hbc.1

omit [Finite G] in
theorem dAdj_conjSub (hΩ : ConjInvariant Ω) {M N : Subgroup G} (h : dAdj Ω M N) (g : G) :
    dAdj Ω (conjSub g M) (conjSub g N) := by
  rcases h with h | h
  · exact Or.inl (omegaNbr_conj hΩ h g)
  · exact Or.inr (omegaNbr_conj hΩ h g)

end T7A

section Alpha

variable [IsSimpleGroup G] (p f)

@[expose] def TwinNormAlpha : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      ∀ L ∈ twinSet Ω K, L ≤ Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

structure AlphaSteps : Prop where
  h3 : C21_3 p f
  h4 : TwinNormAlpha p f

variable {p f}

theorem AlphaSteps.alpha_zt (hs : AlphaSteps p f) {K K' J W : Subgroup G} {z u t : G}
    (h : Hyp21 p f Ω K K' z u J t W) :
    alphaOf (Subgroup.closure ({z, t} : Set G)) = alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hfr := h.twinFrameData
  have hz2 : z * z = 1 := h.std.hz.sq
  have hA : IsElemAbelian2 (Subgroup.closure ({z, t} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hz2 h.ht.sq h.std.hz.ne_one h.ht.ne_one hfr.t_ne_z.symm
      (hfr.comm_zt hp hΩ)
  have hle : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  exact (hs.h3 G Ω K K' z u J t W h).2 _ hle hA

theorem AlphaSteps.sup_le_normalizer (hs : AlphaSteps p f) {K K' J W : Subgroup G} {z u t : G}
    (h : Hyp21 p f Ω K K' z u J t W) :
    ∀ g ∈ K ⊔ K', conjSub g (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hK : K ∈ Ω := h.std.stand.mem
  have h1 := hs.h4 G Ω K K' z u J t W h
  have hKn : K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    h1 K (mem_twinSet_self hK h.std.hz)
  have hK'n : K' ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    h1 K' h.std.hK'
  intro g hg
  exact mem_normalizer_iff_conjSub_eq.mp ((sup_le hKn hK'n) hg)

theorem AlphaSteps.alpha_eq (hs : AlphaSteps p f) {K K' J W J' : Subgroup G} {z u t t' : G}
    (h : Hyp21 p f Ω K K' z u J t W) (hJ' : J' ∈ omegaOfSet Ω (twinSet Ω K))
    (ht' : IsUniqueInvolution J' t') :
    alphaOf (Subgroup.closure ({z, t'} : Set G)) = alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  obtain ⟨g, hgQ, W'', hfr, hW'', hzW'', htW''⟩ :=
    exists_twinFrameData_at hp hq hΩ h.std.stand.mem h.std.hz h.std.hK' h.std.hne h.hu h.hu2
      h.hu1 h.huz hJ' ht'
  have h' : Hyp21 p f Ω K K' z u (conjSub g J') (g * t' * g⁻¹) W'' :=
    Hyp21.of_twinFrameData h.std hfr hW'' hzW'' htW''
  have h1 := hs.alpha_zt h'
  have hgz : g * z * g⁻¹ = z := by
    have := T7A.z_comm_of_mem_sup h.std.hz (isUniqueInvolution_of_mem_twinSet h.std.hz h.std.hK')
      hgQ
    calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
      _ = (z * g) * g⁻¹ := by rw [← this]
      _ = z := by group
  have h2 : conjSub g (Subgroup.closure ({z, t'} : Set G)) =
      Subgroup.closure ({z, g * t' * g⁻¹} : Set G) := by
    rw [T7A.conjSub_closure_pair, hgz]
  have h3 : alphaOf (Subgroup.closure ({z, g * t' * g⁻¹} : Set G)) =
      conjSub g (alphaOf (Subgroup.closure ({z, t'} : Set G))) := by
    rw [← h2, alphaOf_conjSub]
  have hgi := hs.sup_le_normalizer h g⁻¹ (Subgroup.inv_mem _ hgQ)
  have : conjSub g (alphaOf (Subgroup.closure ({z, t'} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := h3 ▸ h1
  calc alphaOf (Subgroup.closure ({z, t'} : Set G))
      = conjSub g⁻¹ (conjSub g (alphaOf (Subgroup.closure ({z, t'} : Set G)))) :=
        (conjSub_inv_conjSub g _).symm
    _ = conjSub g⁻¹ (alphaOf (Subgroup.closure ({u, z} : Set G))) := by rw [this]
    _ = alphaOf (Subgroup.closure ({u, z} : Set G)) := hgi

omit [IsSimpleGroup G] [Finite G] in
theorem T7A.mem_centralizer_of_conj_eq {z x : G} (hxz : x * z * x⁻¹ = z) :
    x ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * z = (x * z * x⁻¹) * x := by group
    _ = z * x := by rw [hxz]

theorem AlphaSteps.conj_alpha_of_mem_centralizer (hs : AlphaSteps p f) {K K' J W : Subgroup G}
    {z u t : G} (h : Hyp21 p f Ω K K' z u J t W) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub c (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have hL : conjSub c K ∈ twinSet Ω K :=
    ⟨hΩ.conjInvariant c K hK, z, h.std.hz, hcz ▸ h.std.hz.conj c⟩
  have hc' := h.conj c
  have hJc : conjSub c J ∈ omegaOfSet Ω (twinSet Ω K) := by
    have := hc'.hJ
    rwa [twinSet_eq_of_mem_twinSet h.std.hz hL] at this
  have hB := hs.alpha_zt hc'
  rw [hcz] at hB
  have hD := hs.alpha_eq h hJc (hc'.ht)
  have hA : conjSub c (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({c * u * c⁻¹, z} : Set G)) := by
    rw [← hcz, ← T7A.conjSub_closure_pair, ← alphaOf_conjSub]
    rw [hcz]
  exact hA.trans (hB.symm.trans hD)

theorem AlphaSteps.conj_alpha_of_omegaNbr (hs : AlphaSteps p f) {K K' J W L : Subgroup G}
    {z u t : G} (h : Hyp21 p f Ω K K' z u J t W) (hL : L ∈ omegaNbr Ω K) {y : G}
    (hy : conjSub y K = L) :
    conjSub y (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hLΩ : L ∈ Ω := hL.1
  have htL : IsUniqueInvolution L (y * z * y⁻¹) := hy ▸ h.std.hz.conj y
  by_cases htw : L ∈ twinSet Ω K
  · have hzL := isUniqueInvolution_of_mem_twinSet h.std.hz htw
    have : y * z * y⁻¹ = z := (htL.eq hzL).symm ▸ rfl
    exact hs.conj_alpha_of_mem_centralizer h (T7A.mem_centralizer_of_conj_eq this)
  · have hLmem : L ∈ omegaOfSet Ω (twinSet Ω K) :=
      T7A.mem_omegaOfSet_of_mem_kPerp hp hq hΩ hK (Set.mem_insert_of_mem _ hL) htw
    have hD := hs.alpha_eq h hLmem htL
    have hy' := h.conj y
    rw [hy] at hy'
    have hKL : K ∈ omegaNbr Ω L := T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hK hLΩ hL
    have hKnot : K ∉ twinSet Ω L := by
      rintro ⟨-, z₀, hz₀L, hz₀K⟩
      exact htw ⟨hLΩ, z₀, hz₀K, hz₀L⟩
    have hKmem : K ∈ omegaOfSet Ω (twinSet Ω L) :=
      T7A.mem_omegaOfSet_of_mem_kPerp hp hq hΩ hLΩ (Set.mem_insert_of_mem _ hKL) hKnot
    have hC := hs.alpha_eq hy' hKmem h.std.hz
    have hA : conjSub y (alphaOf (Subgroup.closure ({u, z} : Set G))) =
        alphaOf (Subgroup.closure ({y * u * y⁻¹, y * z * y⁻¹} : Set G)) := by
      rw [← T7A.conjSub_closure_pair, ← alphaOf_conjSub]
    calc conjSub y (alphaOf (Subgroup.closure ({u, z} : Set G)))
        = alphaOf (Subgroup.closure ({y * u * y⁻¹, y * z * y⁻¹} : Set G)) := hA
      _ = alphaOf (Subgroup.closure ({y * z * y⁻¹, z} : Set G)) := hC.symm
      _ = alphaOf (Subgroup.closure ({z, y * z * y⁻¹} : Set G)) := by rw [Set.pair_comm]
      _ = alphaOf (Subgroup.closure ({u, z} : Set G)) := hD

theorem AlphaSteps.conj_alpha_of_mem_dComp (hs : AlphaSteps p f) {K K' J W : Subgroup G}
    {z u t : G} (h : Hyp21 p f Ω K K' z u J t W) :
    ∀ M ∈ dComp Ω K, ∀ x : G, conjSub x K = M →
      conjSub x (alphaOf (Subgroup.closure ({u, z} : Set G))) =
        alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hΩc : ConjInvariant Ω := hΩ.conjInvariant
  have hbase : ∀ n : G, conjSub n K = K →
      conjSub n (alphaOf (Subgroup.closure ({u, z} : Set G))) =
        alphaOf (Subgroup.closure ({u, z} : Set G)) := fun n hn =>
    hs.conj_alpha_of_mem_centralizer h (T7A.mem_centralizer_of_conj_eq (h.std.hz.conj_eq hn))
  intro M hM
  induction hM with
  | refl => exact fun x hx => hbase x hx
  | @tail b c hab hbc ih =>
    intro x' hx'
    have hbΩ : b ∈ Ω := T7A.mem_of_mem_dComp hK hab
    obtain ⟨x₀, hx₀⟩ := h.std.stand.trans b hbΩ
    have hcΩ : c ∈ Ω := hbc.1
    have hLΩ : conjSub x₀⁻¹ c ∈ Ω := hΩc _ _ hcΩ
    have hadj : dAdj Ω K (conjSub x₀⁻¹ c) := by
      have := T7A.dAdj_conjSub hΩc hbc.2 x₀⁻¹
      rwa [← hx₀, conjSub_inv_conjSub] at this
    have hLnbr : conjSub x₀⁻¹ c ∈ omegaNbr Ω K := by
      rcases hadj with h1 | h1
      · exact h1
      · exact T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hLΩ hK h1
    obtain ⟨y, hy⟩ := h.std.stand.trans _ hLΩ
    have hyα := hs.conj_alpha_of_omegaNbr h hLnbr hy
    have hxy : conjSub (x₀ * y) K = c := by
      rw [conjSub_mul, hy, conjSub_conjSub_inv]
    have hn : conjSub ((x₀ * y)⁻¹ * x') K = K := by
      rw [conjSub_mul, hx', ← hxy, conjSub_inv_conjSub]
    have hnα := hbase _ hn
    have hx'eq : x' = x₀ * y * ((x₀ * y)⁻¹ * x') := by group
    rw [hx'eq, conjSub_mul, conjSub_mul, hnα, hyα, ih x₀ hx₀]

theorem AlphaSteps.exists_mem_normalizer (hs : AlphaSteps p f) {K K' J W : Subgroup G}
    {z u t : G} (h : Hyp21 p f Ω K K' z u J t W) {M : Subgroup G} (hM : M ∈ dComp Ω K) :
    ∃ x ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G), conjSub x K = M := by
  obtain ⟨x, hx⟩ := h.std.stand.trans M (T7A.mem_of_mem_dComp h.std.stand.mem hM)
  exact ⟨x, mem_normalizer_iff_conjSub_eq.mpr (hs.conj_alpha_of_mem_dComp h M hM x hx), hx⟩

end Alpha

end CFSG.ClassicalInvolution.Asc77
