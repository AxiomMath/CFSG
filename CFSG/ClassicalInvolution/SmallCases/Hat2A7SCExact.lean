module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCBasic
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Alpha

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Exact

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def OddCentralAt (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) : Prop :=
  ∀ J ∈ omegaNbr Ω K, ∀ t : G, IsUniqueInvolution J t →
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤ Subgroup.centralizer ({t} : Set G)

theorem kPerp_subset {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ KPerp Ω K) : L ∈ Ω := by
  rcases hL with h | h
  · rw [h]
    exact hK
  · exact h.1

theorem kPerp_eq_of_twin (hΩ : HypOmegaGen Ω)
    (hcl : ∀ L ∈ Ω, ∃ z : G, Hat2A7.IsClassical2A7 ⊤ L z) {J J' : Subgroup G} (hJ : J ∈ Ω)
    (hJ' : J' ∈ twinSet Ω J) : KPerp Ω J = KPerp Ω J' := by
  obtain ⟨hJ'Ω, t, ht, ht'⟩ := hJ'
  ext L
  constructor
  · intro hL
    have hLΩ : L ∈ Ω := kPerp_subset hJ hL
    obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hLΩ
    exact (mem_kPerp_iff_normalizes_a7 hΩ hcl hJ'Ω hLΩ ht' hu).mpr
      ((mem_kPerp_iff_normalizes_a7 hΩ hcl hJ hLΩ ht hu).mp hL)
  · intro hL
    have hLΩ : L ∈ Ω := kPerp_subset hJ'Ω hL
    obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hLΩ
    exact (mem_kPerp_iff_normalizes_a7 hΩ hcl hJ hLΩ ht hu).mpr
      ((mem_kPerp_iff_normalizes_a7 hΩ hcl hJ'Ω hLΩ ht' hu).mp hL)

variable [IsSimpleGroup G] {K₀ : Subgroup G}

theorem mem_kPerp_of_oddCentral (hs : Pre2A7 Ω K₀) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) (hoc : OddCentralAt Ω K z) {J M : Subgroup G}
    (hJ : J ∈ KPerp Ω K) (hM : M ∈ KPerp Ω K) : M ∈ KPerp Ω J := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hw : ∀ L ∈ Ω, A7Witness L := Hat2A7S8.witness_of_pre hs
  have hL : Hat2A7S8.Asc77.T8.LayerHyp Ω z := Hat2A7S8.layerHyp_of_pre hs hz.sq hz.ne_one
  have hJΩ : J ∈ Ω := kPerp_subset hK hJ
  have hMΩ : M ∈ Ω := kPerp_subset hK hM
  have hxm : ∀ X ∈ KPerp Ω K, T8.XMem Ω z X := by
    intro X hX
    rcases hX with h | h
    · rw [h]
      exact Hat2A7S8.xMem_self hK hz
    · exact Hat2A7S8.xMem_of_mem_omegaNbr hΩ hw hK hz h
  have hJx : T8.XMem Ω z J := hxm J hJ
  have hMx : T8.XMem Ω z M := hxm M hM
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJΩ
  have hct : oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.centralizer ({t} : Set G) := by
    rcases hJ with h | h
    · have htz : t = z := by
        rw [h] at ht
        exact ht.eq hz
      rw [htz]
      exact oddCoreOf_le_self _
    · exact hoc J h t ht
  have hOt : ∀ n ∈ oddCoreOf (T8.layerJoin Ω z), conjSub n J ∈ twinSet Ω J := by
    intro n hn
    have h1 : n ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
      Hat2A7S8.oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ z hn
    have h2 : n * t = t * n := Subgroup.mem_centralizer_singleton_iff.mp (hct h1)
    have h3 : n * t * n⁻¹ = t := by
      rw [h2]
      group
    refine ⟨hΩ.conjInvariant n J hJΩ, t, ht, ?_⟩
    have h4 := ht.conj n
    rwa [h3] at h4
  by_cases heq : T8.layerImg Ω z J = T8.layerImg Ω z M
  ·
    obtain ⟨n, hn, hnJ⟩ := Hat2A7S8.Asc77.T8.exists_oddCore_conj_of_layerImg_eq hL hJx hMx heq
    have hMt : M ∈ twinSet Ω J := hnJ ▸ hOt n hn
    by_cases hMJ : M = J
    · exact Or.inl hMJ
    · obtain ⟨-, u, hu, hu'⟩ := hMt
      exact Or.inr (Q3.Q3CL.T3.twin_mem_omegaNbr hΩ hJΩ hMΩ hMJ hu hu')
  · have hF := Hat2A7S8.Asc77.T8.LayerFam.layerSet hΩ hJx
    rcases hF.images_eq_or_commute hL ⟨J, hJx, rfl⟩ ⟨M, hMx, rfl⟩ with h | hcomm
    · exact absurd h heq
    · obtain ⟨n, hn, hnb⟩ :=
        Hat2A7S8.Asc77.T8.exists_oddCore_conj_omegaNbr_of_commute hL hJx hMx heq hcomm
      have hP : M ∈ KPerp Ω (conjSub n J) := Or.inr hnb
      rw [← kPerp_eq_of_twin hΩ hs.classical hJΩ (hOt n hn)] at hP
      exact hP

theorem mem_kPerp_of_mem_omegaNbr_of_oddCentral (hs : Pre2A7 Ω K₀)
    (hOC : ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z → OddCentralAt Ω K z)
    {K L L' : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ KPerp Ω K) (hL' : L' ∈ omegaNbr Ω L) :
    L' ∈ KPerp Ω K := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hLΩ : L ∈ Ω := kPerp_subset hK hL
  obtain ⟨zL, hzL⟩ := Sec6Gen.exists_uniqueInvolution hΩ hLΩ
  have hKL : K ∈ KPerp Ω L := by
    rcases hL with h | h
    · exact Or.inl h.symm
    · exact Or.inr (Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hLΩ h)
  exact mem_kPerp_of_oddCentral hs hLΩ hzL (hOC L hLΩ zL hzL) hKL (Or.inr hL')

theorem false_of_oddCentral (hs : Pre2A7 Ω K₀) (hedge : ¬ DEdgeless Ω) (hconn : DConnected Ω)
    (hOC : ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z → OddCentralAt Ω K z) : False := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K₀ ∈ Ω := hs.mem
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  have hall : ∀ L, Relation.ReflTransGen (fun M N => N ∈ Ω ∧ dAdj Ω M N) K₀ L →
      L ∈ KPerp Ω K₀ := by
    intro L h
    induction h with
    | refl => exact Set.mem_insert _ _
    | @tail b c _ hbc ih =>
      obtain ⟨hcΩ, hadj⟩ := hbc
      have hbΩ : b ∈ Ω := kPerp_subset hK ih
      have hcb : c ∈ omegaNbr Ω b := by
        rcases hadj with h | h
        · exact h
        · exact Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hcΩ hbΩ h
      exact mem_kPerp_of_mem_omegaNbr_of_oddCentral hs hOC hK ih hcb
  have hzN : ∀ L ∈ Ω, z ∈ Subgroup.normalizer (L : Set G) := by
    intro L hL
    obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hL
    exact (mem_kPerp_iff_normalizes_a7 hΩ hs.classical hK hL hz hu).mp
      (hall L (hconn K₀ hK L hL))
  have hgen : ∀ g : G, g * z * g⁻¹ ∈ Subgroup.normalizer (K₀ : Set G) := by
    intro g
    have hL : conjSub g⁻¹ K₀ ∈ Ω := hΩ.conjInvariant g⁻¹ K₀ hK
    have h1 : z ∈ Subgroup.normalizer ((conjSub g⁻¹ K₀ : Subgroup G) : Set G) := hzN _ hL
    rw [mem_normalizer_iff_conjSub_eq] at h1 ⊢
    calc conjSub (g * z * g⁻¹) K₀ = conjSub g (conjSub z (conjSub g⁻¹ K₀)) := by
          rw [conjSub_mul, conjSub_mul]
      _ = conjSub g (conjSub g⁻¹ K₀) := by rw [h1]
      _ = K₀ := conjSub_conjSub_inv g K₀
  have hT : Subgroup.normalClosure ({z} : Set G) = ⊤ := by
    rcases (Subgroup.normalClosure_normal (s := ({z} : Set G))).eq_bot_or_eq_top with h | h
    · exfalso
      apply hz.ne_one
      have hzmem : z ∈ Subgroup.normalClosure ({z} : Set G) := Subgroup.subset_normalClosure rfl
      rw [h] at hzmem
      simpa using hzmem
    · exact h
  have hle : Subgroup.normalClosure ({z} : Set G) ≤ Subgroup.normalizer (K₀ : Set G) := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    have haz : a = z := ha
    subst haz
    exact hgen c
  rw [hT, top_le_iff] at hle
  have hKn : K₀.Normal := Subgroup.normalizer_eq_top_iff.mp hle
  rcases hKn.eq_bot_or_eq_top with h | h
  · exact hz.ne_one (by
      have hzK : z ∈ K₀ := hz.mem
      rw [h] at hzK
      simpa using hzK)
  ·
    have hΩtop : ∀ A ∈ Ω, A = ⊤ := by
      intro A hA
      obtain ⟨g, hg⟩ := hs.trans A hA
      rw [← hg, h]
      exact eq_top_iff.mpr fun x _ => mem_conjSub_iff.mpr (Subgroup.mem_top _)
    unfold DEdgeless at hedge
    push Not at hedge
    obtain ⟨A, hA, B, hB, hadj⟩ := hedge
    have hAB : A = B := (hΩtop A hA).trans (hΩtop B hB).symm
    rcases hadj with hadj | hadj
    · exact hadj.2.1 hAB.symm
    · exact hadj.2.1 hAB

theorem oddCentralAt_of_alphaOf_bot {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hα : ∀ J ∈ omegaNbr Ω K, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
      alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) : OddCentralAt Ω K z := by
  intro J hJ t ht x hx
  by_cases htz : t = z
  · rw [htz]
    exact oddCoreOf_le_self _ hx
  · have hzA : z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
    have htA : t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (T8.oddCoreOf_centralizer_commutes (hα J hJ t ht htz) hzA hz.ne_one htA x hx)

theorem oddCentralAt_of_kPerp_eq_twinSet {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (h : KPerp Ω K = twinSet Ω K) : OddCentralAt Ω K z := by
  intro J hJ t ht x hx
  have hJt : J ∈ twinSet Ω K := h ▸ (Or.inr hJ : J ∈ KPerp Ω K)
  obtain ⟨-, w, hw, hw'⟩ := hJt
  have hwz : w = z := (hz.eq hw).symm
  have htw : t = w := ht.eq hw'
  rw [htw, hwz]
  exact oddCoreOf_le_self _ hx

end Exact

end CFSG.ClassicalInvolution.Hat2A7S
