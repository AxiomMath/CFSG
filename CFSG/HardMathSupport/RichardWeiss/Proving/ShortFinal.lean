module

public import CFSG.HardMathSupport.RichardWeiss.Proving.ShortFrame
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.ThreeCycle
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Central
public import CFSG.HardMathSupport.RichardWeiss.Proving.NoCharNormal
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
public import CFSG.HardMathSupport.RichardWeiss.Proving.ShortAux
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Faithful
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockBridge
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaShapes

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
  CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0 Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G]

theorem shortData_of_setting [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hshort : ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L) :
    ShortData (pCoreOf 2 (L ⊔ S)) L (blockV S L) S := by
  have hQS : pCoreOf 2 (L ⊔ S) ≤ S := twoCore_sup_le hA hL hSL
  have hMQ : L ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ S) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ S)
  have hQC : pCoreOf 2 (L ⊔ S) ≤ Subgroup.centralizer (blockV S L : Set G) :=
    AscTenThree.le_centralizer_omegaOneCenterOf_self (pCoreOf 2 (L ⊔ S))
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) := sup_le_normalizer_blockV S L
  have hVel : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  refine ⟨hQS.trans le_sup_right, hQS, ?_, ?_, ?_, ?_, ?_, ?_, hL.toIsTwoPrimeComponent.perfect,
    hshort⟩
  · intro m hm q hq
    exact (Subgroup.mem_normalizer_iff.1 (hMQ hm) q).1 hq
  · intro m hm l hl
    have hmN : m ∈ Subgroup.normalizer (L : Set G) :=
      (sup_le (Subgroup.le_normalizer) hSL) hm
    exact (Subgroup.mem_normalizer_iff.1 hmN l).1 hl
  · intro m hm v hv
    exact (Subgroup.mem_normalizer_iff.1 (hMV hm) v).1 hv
  · exact CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _
  · intro q hq v hv
    exact (Subgroup.mem_centralizer_iff.1 (hQC hq) v hv).symm
  · intro v hv
    have := hVel.2 v hv
    rwa [pow_two] at this

theorem false_of_E0_short [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} (hN : 10 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    {Δ₀ : Finset (Fin N)} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
    (hshape : E0Shape P ω Δ₀)
    (hθ : (S.subgroupOf (L ⊔ S)).map θ =
      P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)})
    (hshort : ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L) : False := by
  classical
  have hA' : Asc81bHyp (L ⊔ S) S := asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have D := shortData_of_setting hA hL hSL hshort
  have hQ2 : IsPGroup 2 (pCoreOf 2 (L ⊔ S)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  obtain ⟨π, hπ, hπker, hAθ, hequiv, hf⟩ := hNS
  have hθQ : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ pCoreOf 2 (L ⊔ S) := fun m hm =>
    inf_centralizer_blockV_le_twoCore hA hL hSL ⟨hθS m hm, hf m hm⟩
  generalize pCoreOf 2 (L ⊔ S) = Q at D hQ2 hθQ
  haveI := D.shortCtx
  have H : ShortSection Q L (blockV S L) S π θ := ⟨hequiv, hπker, hπ, hAθ, D.hker_of_hθQ hθQ⟩
  have E := e0Frame_of_short hN D H hshape hθS hθ
  have hcommS : ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ S := fun a ha b hb =>
    S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
  have hSSS : ⁅S, S⁆ ≤ S := by
    rw [Subgroup.commutator_le]; exact hcommS
  have hSSQ : ⁅S, S⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro s hs s' hs'
    have hsM : s ∈ L ⊔ S := Subgroup.mem_sup_right hs
    have hsM' : s' ∈ L ⊔ S := Subgroup.mem_sup_right hs'
    have hcM : ⁅s, s'⁆ ∈ L ⊔ S := Subgroup.mem_sup_right (hcommS s hs s' hs')
    refine hθQ ⟨⁅s, s'⁆, hcM⟩ ?_
    have e : (⟨⁅s, s'⁆, hcM⟩ : ↥(L ⊔ S)) = ⁅(⟨s, hsM⟩ : ↥(L ⊔ S)), ⟨s', hsM'⟩⁆ := rfl
    rw [e, map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.2
    have h1 := E0Shape.mem_E0grp_prop hshape
      ((E.img _).1 ⟨⟨s, hsM⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩)
    have h2 := E0Shape.mem_E0grp_prop hshape
      ((E.img _).1 ⟨⟨s', hsM'⟩, Subgroup.mem_subgroupOf.2 hs', rfl⟩)
    exact e0_eprop_comm hshape h1 h2
  obtain ⟨x₁, x₂, x₃, r, h1, h2, h3, hr, h12, h12', h13, h13', h23, h23', hr1, hr2, hr3⟩ :=
    E.exists_three_pts
  have hσeven : (swap x₁ x₂ * swap x₁ x₃) ∈ alternatingGroup (Fin N) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (Ne.symm h12),
      Perm.sign_swap (Ne.symm h13)]
    decide
  obtain ⟨l, hl⟩ := H.hAθ _ hσeven
  have hcyc : (swap x₁ x₂ * swap x₁ x₃).IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same (Ne.symm h12) (Ne.symm h13) (Ne.symm h23)
  obtain ⟨n, hodd, hθg⟩ := exists_odd_lift θ hl hcyc.orderOf
  set g : ↥(L ⊔ S) := (⟨(l : G), Subgroup.mem_sup_left l.2⟩ : ↥(L ⊔ S)) ^ n with hgdef
  have hgL : (g : G) ∈ L := by
    have := L.pow_mem l.2 n
    simpa [hgdef] using this
  have hgMmem : (g : G) ∈ L ⊔ S := g.2
  have hgM : g ∈ L.subgroupOf (L ⊔ S) := Subgroup.mem_subgroupOf.2 hgL
  have hgodd : Odd (orderOf (g : G)) := by
    rw [Subgroup.orderOf_coe]; exact hodd
  have hnotnorm : ¬ Subgroup.zpowers (g : G) ≤ Subgroup.normalizer (S : Set G) := by
    intro hle
    obtain ⟨s, hs, hns⟩ := E.three_cycle_not_normalize h1 h3 h12' h13 h13' h23 (g := g) hθg
    apply hns
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    have := (Subgroup.mem_normalizer_iff.1 (hle (Subgroup.mem_zpowers (g : G))) (s : G)).1 hsS
    exact Subgroup.mem_subgroupOf.2 this
  have hYX : Subgroup.zpowers (g : G) ≤ L ⊔ S := by
    rw [Subgroup.zpowers_le]; exact hgMmem
  have hrho : ∀ (m : ↥(L ⊔ S)) (q : ↥Q),
      rhoQ D.hMQ D.hML m (Additive.ofMul (QuotientGroup.mk q : ↥Q ⧸ CQ Q L)) =
        Additive.ofMul (QuotientGroup.mk (conjQ D.hMQ m q)) := fun m q => rfl
  have hS_char : ((⁅S, S⁆).subgroupOf S).Characteristic :=
    commutator_characteristic le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance)
  by_cases hD : ∃ y₀ ∈ YW Q L S, ∃ x₀, x₀ ∉ Δ₀ ∧ E.Det y₀ x₀
  ·
    have hfaith := E.faithful_of_det hD
    set R₀ : Subgroup G := S ⊓ Subgroup.centralizer ((⁅S, S⁆ : Subgroup G) : Set G) with hR₀
    have hR₀Q : R₀ ≤ Q := by
      intro x hx
      have hxS : x ∈ S := hx.1
      have hxM : x ∈ L ⊔ S := Subgroup.mem_sup_right hxS
      have h1' : θ ⟨x, hxM⟩ = 1 := by
        apply hfaith ⟨x, hxM⟩ (Subgroup.mem_subgroupOf.2 hxS)
        intro y hy
        obtain ⟨u, hu, hmk⟩ := mem_YW.1 hy
        have hy' : y = Additive.ofMul (QuotientGroup.mk u : ↥Q ⧸ CQ Q L) := by rw [hmk]; rfl
        rw [hy', hrho]
        congr 2
        apply Subtype.ext
        show x * (u : G) * x⁻¹ = u
        have := Subgroup.mem_centralizer_iff.1 hx.2 u hu
        rw [mul_inv_eq_iff_eq_mul]; exact this.symm
      exact hθQ _ h1'
    have hVR : blockV S L ≤ R₀ := fun v hv =>
      ⟨D.hVQ.trans D.hQS hv, Subgroup.mem_centralizer_iff.2 fun u hu =>
        D.hQV u (hSSQ hu) v hv⟩
    have hconj : ∀ m ∈ L, ∀ x ∈ R₀, m * x * m⁻¹ ∈ R₀ := by
      intro m hm x hx
      obtain ⟨v, hv, e⟩ := D.conj_eq x (hR₀Q hx) m hm
      rw [e]
      exact R₀.mul_mem (hVR hv) hx
    have hgN : (g : G) ∈ Subgroup.normalizer (R₀ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact fun hx => hconj _ hgL x hx
      · intro hx
        have := hconj _ (L.inv_mem hgL) _ hx
        simpa [mul_assoc] using this
    have hYC : Subgroup.zpowers (g : G) ≤ Subgroup.normalizer (R₀ : Set G) := by
      rw [Subgroup.zpowers_le]; exact hgN
    have hR₀bot : R₀ ≠ ⊥ := by
      intro hbot
      obtain ⟨v, hv⟩ := hπ (Multiplicative.ofAdd (pairEW x₁ x₂ : altHeart N))
      have hv1 : v ≠ 1 := by
        intro h
        rw [h, map_one] at hv
        have h0 : (pairEW x₁ x₂ : altHeart N) = 0 := by
          have := congrArg Multiplicative.toAdd hv
          simpa using this.symm
        exact mk_pairEW_ne_zero (Ne.symm h12) h13 h23 h0
      have hvV : (v : G) ∈ blockV S L := D.commutator_le v.2
      have hvR : (v : G) ∈ R₀ := hVR hvV
      rw [hbot] at hvR
      exact hv1 (Subtype.ext (Subgroup.mem_bot.1 hvR))
    have hchar : (R₀.subgroupOf S).Characteristic :=
      centralizer_characteristic hSSS hS_char
    have hR₀top : (R₀.subgroupOf R₀).Characteristic := by
      rw [Subgroup.subgroupOf_self]; infer_instance
    exact noCharNormal_of_asc81bHyp hA' hYX (inf_le_left : R₀ ≤ S) hchar hnotnorm R₀ le_rfl
      hR₀bot hR₀top hYC
  ·
    have hD' : ∀ y ∈ YW Q L S, ∀ x, x ∉ Δ₀ → ¬ E.Det y x := by
      intro y hy x hx hdet
      exact hD ⟨y, hy, x, hx, hdet⟩
    have hgQ : ∀ q ∈ Q, (g : G) * q * (g : G)⁻¹ ∈ Q := fun q hq => D.hMQ g hgMmem q hq
    have hcomm : ∀ u ∈ ⁅S, S⁆, ∀ s ∈ S, (g : G) * (s * u * s⁻¹ * u⁻¹) =
        (s * u * s⁻¹ * u⁻¹) * (g : G) := by
      intro u hu s hs
      have hsM : s ∈ L ⊔ S := Subgroup.mem_sup_right hs
      have huQ : u ∈ Q := hSSQ hu
      have hcQ : s * u * s⁻¹ * u⁻¹ ∈ Q := Q.mul_mem (D.hMQ s hsM u huQ) (Q.inv_mem huQ)
      have hy : Additive.ofMul (QuotientGroup.mk (⟨u, huQ⟩ : ↥Q) : ↥Q ⧸ CQ Q L) ∈ YW Q L S :=
        mem_YW.2 ⟨⟨u, huQ⟩, hu, rfl⟩
      have hcen := E.central_of_noDet hD' h1 h2 h3 hr h12 h13 h23 hr1 hr2 hr3 hgM hθg
        (s := ⟨s, hsM⟩) (Subgroup.mem_subgroupOf.2 hs) hy
      have hz : rhoQ D.hMQ D.hML ⟨s, hsM⟩ (Additive.ofMul (QuotientGroup.mk (⟨u, huQ⟩ : ↥Q) :
            ↥Q ⧸ CQ Q L)) - Additive.ofMul (QuotientGroup.mk (⟨u, huQ⟩ : ↥Q) : ↥Q ⧸ CQ Q L) =
          Additive.ofMul (QuotientGroup.mk (⟨s * u * s⁻¹ * u⁻¹, hcQ⟩ : ↥Q) : ↥Q ⧸ CQ Q L) := by
        apply Additive.toMul.injective
        rw [toMul_sub, toMul_rhoQ D]
        simp only [toMul_ofMul]
        rw [convQ_mk, div_eq_mul_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        rfl
      rw [hz, hrho] at hcen
      have hmk := Additive.ofMul.injective hcen
      have hcq := QuotientGroup.eq.1 hmk
      have hcq' := mem_CQ.1 hcq
      have hgd := hcq' (g : G) hgL
      have hfix : (g : G) * (s * u * s⁻¹ * u⁻¹) * (g : G)⁻¹ = s * u * s⁻¹ * u⁻¹ :=
        conj_eq_of_odd hQ2 hgQ hcQ hgodd
          (d := ((conjQ D.hMQ g ⟨s * u * s⁻¹ * u⁻¹, hcQ⟩)⁻¹ * ⟨s * u * s⁻¹ * u⁻¹, hcQ⟩ : ↥Q))
          rfl hgd
      exact mul_inv_eq_iff_eq_mul.1 hfix
    have hCS : ⁅⁅S, S⁆, S⁆ ≤ S := by
      rw [Subgroup.commutator_le]
      intro y hy s hs
      exact hcommS y (hSSS hy) s hs
    have hCcen : ⁅⁅S, S⁆, S⁆ ≤ Subgroup.centralizer (({(g : G)} : Set G)) := by
      rw [Subgroup.commutator_le]
      intro u hu s hs
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      have hc : Commute (g : G) (s * u * s⁻¹ * u⁻¹) := hcomm u hu s hs
      have e : ⁅u, s⁆ = (s * u * s⁻¹ * u⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hc.inv_right.eq
    have hgN : (g : G) ∈ Subgroup.normalizer ((⁅⁅S, S⁆, S⁆ : Subgroup G) : Set G) := by
      have : (g : G) ∈ Subgroup.centralizer ((⁅⁅S, S⁆, S⁆ : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have := Subgroup.mem_centralizer_iff.1 (hCcen hx) (g : G) (Set.mem_singleton _)
        exact this.symm
      exact Subgroup.centralizer_le_normalizer _ this
    have hCbot : ⁅⁅S, S⁆, S⁆ ≠ ⊥ := by
      obtain ⟨u, huY, s, hs, hne⟩ := E.comm_nonzero
      obtain ⟨q, hq, hmk⟩ := mem_YW.1 huY
      intro hbot
      have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
      have hmem : ⁅(q : G), (s : G)⁆ ∈ ⁅⁅S, S⁆, S⁆ := Subgroup.commutator_mem_commutator hq hsS
      rw [hbot, Subgroup.mem_bot] at hmem
      apply hne
      have hu' : u = Additive.ofMul (QuotientGroup.mk q : ↥Q ⧸ CQ Q L) := by rw [hmk]; rfl
      rw [hu', hrho]
      congr 2
      apply Subtype.ext
      show (s : G) * (q : G) * (s : G)⁻¹ = q
      have : (q : G) * s = s * q := by
        have := commutatorElement_eq_one_iff_mul_comm.1 hmem
        exact this
      rw [mul_inv_eq_iff_eq_mul]; exact this.symm
    have hchar : ((⁅⁅S, S⁆, S⁆).subgroupOf S).Characteristic :=
      commutator_characteristic hSSS hS_char
    have hCtop : ((⁅⁅S, S⁆, S⁆ : Subgroup G).subgroupOf (⁅⁅S, S⁆, S⁆ : Subgroup G)).Characteristic := by
      rw [Subgroup.subgroupOf_self]; infer_instance
    exact noCharNormal_of_asc81bHyp hA' hYX hCS hchar hnotnorm _ le_rfl hCbot hCtop
      (Subgroup.zpowers_le.2 hgN)

end CFSG.HardMathSupport.RichardWeiss.Proving
