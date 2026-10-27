module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

namespace TwinDisc

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem conn_of_mem_dComp (hΩ : HypOmegaGen Ω)
    (htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : G, conjSub g M = N) {K₀ K₀' J₀ : Subgroup G}
    {z₀ u₀ t₀ : G} (h₀ : TwinFrameData Ω K₀ K₀' z₀ u₀ J₀ t₀) {K₁ K₁' J₁ : Subgroup G}
    {z₁ u₁ t₁ : G} (h₁ : TwinFrameData Ω K₁ K₁' z₁ u₁ J₁ t₁) (hK₁ : K₁ ∈ dComp Ω K₀) :
    Conn Ω (Subgroup.closure ({z₀, u₀, t₀} : Set G)) (Subgroup.closure ({z₁, u₁, t₁} : Set G)) := by
  let P : Subgroup G → Prop := fun M => ∃ (M' J : Subgroup G) (z u t : G),
    TwinFrameData Ω M M' z u J t ∧
      Conn Ω (Subgroup.closure ({z₀, u₀, t₀} : Set G)) (Subgroup.closure ({z, u, t} : Set G))
  have hP₀ : P K₀ := ⟨K₀', J₀, z₀, u₀, t₀, h₀, Relation.ReflTransGen.refl⟩
  have step : ∀ M N : Subgroup G, P M → N ∈ omegaNbr Ω M → P N := by
    rintro M N ⟨M', J, z, u, t, h, hc⟩ hNn
    have hNΩ : N ∈ Ω := hNn.1
    by_cases hNt : N ∈ twinSet Ω M
    · have hzN := isUniqueInvolution_of_mem_twinSet h.hz hNt
      have hMN : M ∈ twinSet Ω N := ⟨h.mem, z, hzN, h.hz⟩
      have hMne : M ≠ N := fun e => hNn.2.1 e.symm
      have hJt : J ∉ twinSet Ω N := by
        intro hJt
        rw [twinSet_eq_of_mem_twinSet h.hz hNt] at hJt
        exact (h.hJ.2 J hJt).2.1 rfl
      have hJperp : J ∈ KPerp Ω N := by
        rw [← A7Q.Gen.kPerp_eq_of_twin hΩ h.mem hNt]
        exact Set.mem_insert_of_mem _ (h.hJ.2 M (mem_twinSet_self h.mem h.hz))
      have hperp : KPerp Ω N ≠ twinSet Ω N := fun e => hJt (e ▸ hJperp)
      obtain ⟨u'', J'', t'', h''⟩ := A7Q.Gen.exists_twinFrameData hΩ hNΩ hzN hMN hMne hperp
      exact ⟨M, J'', z, u'', t'', h'', hc.trans (conn_of_same_z hΩ h h'')⟩
    · have hNo : N ∈ omegaOfSet Ω (twinSet Ω M) :=
        A7Q.Gen.mem_omegaOfSet_of_mem_kPerp hΩ h.mem (Set.mem_insert_of_mem _ hNn) hNt
      obtain ⟨tN, htN⟩ := Sec6Gen.exists_uniqueInvolution hΩ hNΩ
      obtain ⟨u', h', hcc⟩ := exists_frame_at_J hΩ h hNo htN
      obtain ⟨N', hN'tw, hN'ne⟩ := exists_twin_of_trans hΩ htr h.mem h.hK' h.hne hNΩ
      obtain ⟨v, hv⟩ := exists_frame_swap hΩ h' hN'tw hN'ne
      exact ⟨N', M, tN, v, z, hv, hc.trans (hcc.trans (conn_swap hΩ h' hv))⟩
  have all' : ∀ M : Subgroup G,
      Relation.ReflTransGen (fun X Y : Subgroup G => Y ∈ Ω ∧ dAdj Ω X Y) K₀ M → M ∈ Ω ∧ P M := by
    intro M hpath
    induction hpath with
    | refl => exact ⟨h₀.mem, hP₀⟩
    | @tail b c _ hstep ih =>
      obtain ⟨hcΩ, hadj⟩ := hstep
      refine ⟨hcΩ, ?_⟩
      rcases hadj with hbc | hcb
      · exact step b c ih.2 hbc
      · exact step b c ih.2 (Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hcΩ ih.1 hcb)
  obtain ⟨M', J, z, u, t, h, hc⟩ := (all' K₁ hK₁).2
  have hzz : z = z₁ := h.hz.eq h₁.hz
  subst hzz
  exact hc.trans (conn_of_same_z hΩ h h₁)

theorem isElemAbelian2_of_mem_signalizer {B F : Subgroup G} (hB : IsElemAbelian 2 B)
    (hF : F ∈ signalizerFunctorEk 2 2 B) : IsElemAbelian2 F 2 := by
  obtain ⟨hFB, hcard⟩ := hF
  exact ⟨by simpa using hcard, fun x hx => by
    have := hB.2 x (hFB hx)
    simpa [pow_two] using this⟩

theorem alphaOf_eq_of_conn (hhyp : ∀ A ∈ frameSet Ω, Hyp51 A) {B B' : Subgroup G}
    (hB : B ∈ frameSet Ω) (h : Conn Ω B B') {F F' : Subgroup G} (hF : F ≤ B)
    (hF2 : IsElemAbelian2 F 2) (hF' : F' ≤ B') (hF'2 : IsElemAbelian2 F' 2) :
    alphaOf F = alphaOf F' := by
  induction h generalizing F' with
  | refl => exact (lemma54 G _ (hhyp _ hB) F F' hF hF' hF2 hF'2).1
  | @tail b c _ hbc ih =>
    obtain ⟨hbF, hcF, F₀, hF₀b, hF₀c⟩ := hbc
    have hF₀2 : IsElemAbelian2 F₀ 2 := isElemAbelian2_of_mem_signalizer (hhyp _ hbF).1 hF₀b
    have h1 := ih hF₀b.1 hF₀2
    have h2 := (lemma54 G _ (hhyp _ hcF) F₀ F' hF₀c.1 hF' hF₀2 hF'2).1
    exact h1.trans h2

theorem mem_normalizer_alpha_of_mem_dComp (hΩ : HypOmegaGen Ω)
    (htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : G, conjSub g M = N) (hhyp : ∀ A ∈ frameSet Ω, Hyp51 A)
    {K K' J : Subgroup G} {z u t : G} (h : TwinFrameData Ω K K' z u J t) {g : G}
    (hg : conjSub g K ∈ dComp Ω K) :
    g ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hc := frameData_conj hΩ.conjInvariant h g
  have hconn := conn_of_mem_dComp hΩ htr h hc hg
  have hF : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) :=
    Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp)
  have hF' : Subgroup.closure ({g * u * g⁻¹, g * z * g⁻¹} : Set G) ≤
      Subgroup.closure ({g * z * g⁻¹, g * u * g⁻¹, g * t * g⁻¹} : Set G) :=
    Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp)
  have heq := alphaOf_eq_of_conn hhyp (closure_mem_frameSet h) hconn hF
    (isElemAbelian2_closure_uz hΩ h) hF' (isElemAbelian2_closure_uz hΩ hc)
  have hmap : conjSub g (Subgroup.closure ({u, z} : Set G)) =
      Subgroup.closure ({g * u * g⁻¹, g * z * g⁻¹} : Set G) := by
    unfold conjSub
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, Set.image_singleton]
  have h2 := alphaOf_conjSub g (Subgroup.closure ({u, z} : Set G))
  rw [hmap] at h2
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  rw [← h2]
  exact heq.symm

theorem mem_of_mem_dComp {K M : Subgroup G} (hK : K ∈ Ω) (hM : M ∈ dComp Ω K) : M ∈ Ω := by
  induction hM with
  | refl => exact hK
  | tail _ hbc => exact hbc.1

theorem dComp_le_normalizer_alpha (hΩ : HypOmegaGen Ω)
    (htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : G, conjSub g M = N) (hhyp : ∀ A ∈ frameSet Ω, Hyp51 A)
    {K K' J : Subgroup G} {z u t : G} (h : TwinFrameData Ω K K' z u J t)
    (hα : ∀ A : Subgroup G, A ≤ Subgroup.closure ({z, u, t} : Set G) → IsElemAbelian2 A 2 →
      alphaOf A = alphaOf (Subgroup.closure ({u, z} : Set G)))
    {M : Subgroup G} (hM : M ∈ dComp Ω K) :
    M ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  obtain ⟨g, rfl⟩ := htr K h.mem M (mem_of_mem_dComp h.mem hM)
  have hg := mem_normalizer_alpha_of_mem_dComp hΩ htr hhyp h hM
  have hK := twin_le_normalizer_alpha hΩ h hα (mem_twinSet_self h.mem h.hz)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' := hK hy
  show g * y * g⁻¹ ∈ _
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hy') (Subgroup.inv_mem _ hg)

theorem centralizer_le_normalizer_alpha (hΩ : HypOmegaGen Ω)
    (htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : G, conjSub g M = N) (hhyp : ∀ A ∈ frameSet Ω, Hyp51 A)
    {K K' J : Subgroup G} {z u t : G} (h : TwinFrameData Ω K K' z u J t) :
    Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  intro c hc
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  apply mem_normalizer_alpha_of_mem_dComp hΩ htr hhyp h
  by_cases hne : conjSub c K = K
  · rw [hne]; exact Relation.ReflTransGen.refl
  · have hL : conjSub c K ∈ Ω := hΩ.conjInvariant c K h.mem
    have hzc : IsUniqueInvolution (conjSub c K) z := hcz ▸ h.hz.conj c
    exact Relation.ReflTransGen.single ⟨hL, Or.inl
      (Q3.Q3CL.T3.twin_mem_omegaNbr hΩ h.mem hL hne h.hz hzc)⟩

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
