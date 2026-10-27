module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248L227

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

theorem map_coreIn_subtype_le {G : Type*} [Group G] [Finite G] {p k : ℕ} (hp : 1 < p)
    {K Q : Subgroup G} :
    (coreIn p k (Q.subgroupOf K) (⊤ : Subgroup ↥K)).map K.subtype ≤ coreIn p k Q K := by
  unfold coreIn
  rw [Subgroup.map_iSup]
  refine iSup_le fun R' => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hR' => ?_
  obtain ⟨hRQ, hk⟩ := hR'
  set E : Subgroup G := R'.map K.subtype with hE
  have hEK : E ≤ K := fun x ⟨y, _, hy⟩ => hy ▸ y.2
  have hEsub : E.subgroupOf K = R' :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective R'
  have hEQ : E ≤ Q := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_subgroupOf).1 (hRQ hy)
  have hrE : CFSG.Open.pRank p E = CFSG.Open.pRank p R' :=
    pRank_map_eq_of_injective hp K.subtype K.subtype_injective R'
  refine le_iSup_of_le E (le_iSup_of_le ⟨hEQ, hrE ▸ hk⟩ ?_)
  rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
  refine ⟨x.2, ?_⟩
  have h1 : x ∈ Subgroup.normalizer ((E.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [hEsub]
    exact hx
  rw [normalizer_subgroupOf_eq hEK] at h1
  exact h1

theorem coreIn_eq_of_subtype {G : Type*} [Group G] [Finite G] {p k : ℕ} (hp : 1 < p)
    {K Q : Subgroup G} (h : coreIn p k (Q.subgroupOf K) (⊤ : Subgroup ↥K) = ⊤) :
    coreIn p k Q K = K := by
  refine le_antisymm (iSup₂_le fun _ _ => inf_le_left) ?_
  have h1 := map_coreIn_subtype_le (k := k) hp (K := K) (Q := Q)
  rw [h, Subgroup.map_top, Subgroup.range_subtype] at h1
  exact h1

theorem perfect_of_layer {G : Type*} [Group G] [Finite G] {p : ℕ} {K : Subgroup G}
    (h : GLAPLayer p K = K) : commutator ↥K = ⊤ := by
  have h1 : K ≤ ⁅K, K⁆ := by
    conv_lhs => rw [← h]
    refine sSup_le fun J hJ => ?_
    have := glaPComponent_perfect hJ
    calc J = ⁅J, J⁆ := this.symm
      _ ≤ ⁅K, K⁆ := Subgroup.commutator_mono hJ.1 hJ.1
  rw [commutator_def, eq_top_iff]
  intro x _
  have hx : (x : G) ∈ ⁅K, K⁆ := h1 x.2
  have h2 : ⁅K, K⁆ = (⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ : Subgroup ↥K).map K.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [h2] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

theorem cover_eq_top {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hlayer : GLAPLayer p (⊤ : Subgroup X) = ⊤)
    (hqs : CFSG.Open.IsQuasisimple (X ⧸ GLAPPrimeCore p X)) (C : Subgroup X) [C.Normal]
    (hC : C ⊔ GLAPPrimeCore p X = ⊤) : C = ⊤ := by
  set T : Subgroup X := ⊤ with hT
  let e : ↥T ≃* X := Subgroup.topEquiv
  have hR : (GLAPPrimeCore p ↥T).map e.toMonoidHom = GLAPPrimeCore p X :=
    glaPPrimeCore_map_iso p e
  let q : (↥T ⧸ GLAPPrimeCore p ↥T) ≃* (X ⧸ GLAPPrimeCore p X) :=
    QuotientGroup.congr _ _ e hR
  have hq : CFSG.Open.IsQuasisimple (barOf p T) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv q.symm hqs
  obtain ⟨K0, hK0, hlay, -⟩ := exists_layer_eq_component hp hq
  have hK0top : K0 = ⊤ := by rw [← hlay]; exact hlayer
  subst hK0top
  by_contra hne
  have hlt : C < ⊤ := lt_top_iff_ne_top.2 hne
  refine hK0.2.2.2 C hlt (isSubnormal_of_normal inferInstance) ?_
  rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    eq_top_iff]
  rintro z -
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective _ z
  have ht : (t : X) ∈ C ⊔ GLAPPrimeCore p X := by rw [hC]; exact Subgroup.mem_top _
  obtain ⟨c, hc, r, hr, hcr⟩ := Subgroup.mem_sup_of_normal_left.1 ht
  have hr' : (⟨r, Subgroup.mem_top r⟩ : ↥T) ∈ GLAPPrimeCore p ↥T := by
    rw [← hR] at hr
    obtain ⟨r0, hr0, hr0e⟩ := hr
    have : r0 = ⟨r, Subgroup.mem_top r⟩ := Subtype.ext hr0e
    rwa [this] at hr0
  refine ⟨⟨c, Subgroup.mem_top c⟩, Subgroup.mem_subgroupOf.2 hc, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have : (⟨c, Subgroup.mem_top c⟩ : ↥T)⁻¹ * t = ⟨r, Subgroup.mem_top r⟩ := by
    apply Subtype.ext
    simp [← hcr]
  rw [this]
  exact hr'

private theorem commutatorElement_mul_central' {K : Type*} [Group K] {a b z : K}
    (hz : z ∈ Subgroup.center K) :
    a * z * b * (a * z)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hz' := Subgroup.mem_center_iff.mp hz b
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hz']; group
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem commutatorElement_mul_central_right' {K : Type*} [Group K] {a b z : K}
    (hz : z ∈ Subgroup.center K) :
    a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hz' := Subgroup.mem_center_iff.mp hz a⁻¹
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [hz']; group
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem le_center_of_quasisimple {K : Type*} [Group K] (hq : CFSG.Open.IsQuasisimple K)
    {N : Subgroup K} [hN : N.Normal] (hne : N ≠ ⊤) : N ≤ Subgroup.center K := by
  obtain ⟨hK, hs⟩ := hq
  have hmapN : (N.map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hmapN with h | h
  · intro x hx
    have hx' : QuotientGroup.mk' (Subgroup.center K) x ∈
        N.map (QuotientGroup.mk' (Subgroup.center K)) := ⟨x, hx, rfl⟩
    rw [h] at hx'
    exact (QuotientGroup.eq_one_iff x).mp ((Subgroup.mem_bot).mp hx')
  · exfalso
    apply hne
    have hsup : N ⊔ Subgroup.center K = ⊤ := by
      have := congrArg (Subgroup.comap (QuotientGroup.mk' (Subgroup.center K))) h
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at this
    have hdec : ∀ a : K, ∃ n ∈ N, ∃ z ∈ Subgroup.center K, n * z = a := fun a => by
      have ha : a ∈ ((N ⊔ Subgroup.center K : Subgroup K) : Set K) := by rw [hsup]; trivial
      rw [Subgroup.mul_normal] at ha
      exact Set.mem_mul.mp ha
    refine eq_top_iff.mpr (hK ▸ ?_)
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdec a
    obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdec b
    rw [commutatorElement_def, commutatorElement_mul_central' hz₁,
      commutatorElement_mul_central_right' hz₂]
    exact mul_mem (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁)) (inv_mem hn₂)

theorem le_comap_center_of_normal {X : Type*} [Group X] {R : Subgroup X} [R.Normal]
    (hqs : CFSG.Open.IsQuasisimple (X ⧸ R))
    (hcov : ∀ C : Subgroup X, C.Normal → C ⊔ R = ⊤ → C = ⊤) (N : Subgroup X) [N.Normal]
    (hN : N ≠ ⊤) : N ≤ (Subgroup.center (X ⧸ R)).comap (QuotientGroup.mk' R) := by
  have hmapN : (N.map (QuotientGroup.mk' R)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hne : N.map (QuotientGroup.mk' R) ≠ ⊤ := by
    intro htop
    apply hN
    refine hcov N inferInstance ?_
    have := congrArg (Subgroup.comap (QuotientGroup.mk' R)) htop
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at this
  have h := le_center_of_quasisimple hqs hne
  rw [← Subgroup.map_le_iff_le_comap]
  exact h

end CFSG.LocalAnalysis.GLTheoremA.H248L227
