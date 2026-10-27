module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.CharHelpers
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.ThreeCycle
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClLambda
public import CFSG.HardMathSupport.RichardWeiss.Proving.NoCharNormal
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Central
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Faithful

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open
  CFSG.HardMathSupport.RichardWeiss.Proving Equiv Equiv.Perm
open scoped commutatorElement

attribute [local instance] IsMulCommutative.instCommGroup

variable {G : Type} [Group G]

theorem false_of_E0 [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} (hN : 10 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    {Δ₀ : Finset (Fin N)} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
    (hshape : E0Shape P ω Δ₀)
    (hθ : (S.subgroupOf (L ⊔ S)).map θ =
      P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)})
    (hJ : (S.subgroupOf (L ⊔ S)).map θ ≤ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ)
    (hY : ∀ y ∈ Phi S, y ^ 2 = 1 → y ∈ blockV S L) : False := by
  classical
  have hA' : Asc81bHyp (L ⊔ S) S := asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hVel : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) := sup_le_normalizer_blockV S L
  have hVn : ∀ m ∈ L ⊔ S, ∀ v ∈ blockV S L, m * v * m⁻¹ ∈ blockV S L := fun m hm v hv =>
    (Subgroup.mem_normalizer_iff.1 (hMV hm) v).1 hv
  have hVS : blockV S L ≤ S := (omegaOneCenterOf_le _).trans hA'.twoCore_le
  have hML : ∀ m ∈ L ⊔ S, ∀ l ∈ L, m * l * m⁻¹ ∈ L := by
    intro m hm l hl
    have hmN : m ∈ Subgroup.normalizer (L : Set G) :=
      (sup_le (Subgroup.le_normalizer) hSL) hm
    exact (Subgroup.mem_normalizer_iff.1 hmN l).1 hl
  have hV2 : ∀ v ∈ blockV S L, v * v = 1 := fun v hv => by
    have := hVel.2 v hv
    rwa [pow_two] at this
  have hV2' : ∀ v ∈ blockV S L, v ^ 2 = 1 := hVel.2
  have : IsMulCommutative ↥(blockV S L) := hVel.1
  obtain ⟨π, hπ, hπker, hAθ, hequiv, hf⟩ := hNS
  have hKV : (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)) ≤ blockV S L :=
    inf_le_left.trans (commutator_le_of_normalizes hVn)
  have hMU : L ⊔ S ≤ Subgroup.normalizer ((⁅blockV S L, L⁆ : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact fun h => conj_mem_commutator (V := blockV S L) (L := L) (hVn m hm) (hML m hm) u h
    · intro h
      have := conj_mem_commutator (V := blockV S L) (L := L) (g := m⁻¹)
        (hVn m⁻¹ (inv_mem hm)) (hML m⁻¹ (inv_mem hm)) _ h
      simpa [mul_assoc] using this
  obtain ⟨a, ha⟩ : ∃ a, a ∈ Δ₀ := Finset.card_pos.1 (by rw [hshape.card]; omega)
  have hz : ∃ z : Fin N, ∀ y, z ≠ y →
      swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin N))) := by
    refine ⟨a, fun y hay hmem => ?_⟩
    have hmem' : swap a y ∈ (S.subgroupOf (L ⊔ S)).map θ :=
      Subgroup.map_mono (Subgroup.comap_mono (thompsonJ_le_self S)) hmem
    rw [hθ] at hmem'
    obtain ⟨⟨p, hp, hpx⟩, -⟩ := E0Shape.mem_E0grp_prop hshape hmem'
    have hya : swap a y a = p a := hpx a ha
    rw [swap_apply_left] at hya
    have hyΔ : y ∈ Δ₀ := by rw [hya]; exact hshape.P_mem hp ha
    obtain ⟨w, hw, hwa, hwy⟩ : ∃ w ∈ Δ₀, w ≠ a ∧ w ≠ y := by
      by_contra hcon
      push Not at hcon
      have hsub : Δ₀ ⊆ {a, y} := by
        intro w hw
        by_cases h1 : w = a
        · simp [h1]
        · simp [hcon w hw h1]
      have h1 := Finset.card_le_card hsub
      have h2 : ({a, y} : Finset (Fin N)).card ≤ 2 := Finset.card_le_two
      rw [hshape.card] at h1
      omega
    have hwp : swap a y w = p w := hpx w hw
    rw [swap_apply_of_ne_of_ne hwa hwy] at hwp
    have hp1 : p = 1 := hshape.reg hp hw hwp.symm
    rw [hp1] at hya
    exact hay hya.symm
  have hnf := hnf_of_unmatched θ hz
  have hlay := isMax_le_layerTriv hA' hSL (Or.inr (by omega)) π θ hπ hequiv hπker hf hnf
  have hSlay := le_layerTriv_of_thompsonJ hKV hMV hMU le_sup_right θ hf hJ hlay
  have E := e0Frame_of_group hVn hML hV2 hVS π θ hπ hequiv hAθ hf hπker hSlay hshape hN hθS hθ
  obtain ⟨x₁, x₂, x₃, r, h1, h2, h3, hr, h12, h12', h13, h13', h23, h23', hr1, hr2, hr3⟩ :=
    E.exists_three_pts
  have hσeven : (swap x₁ x₂ * swap x₁ x₃) ∈ alternatingGroup (Fin N) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (Ne.symm h12),
      Perm.sign_swap (Ne.symm h13)]
    decide
  obtain ⟨l, hl⟩ := hAθ _ hσeven
  have hgL : (l : G) ∈ L := l.2
  have hgMmem : (l : G) ∈ L ⊔ S := Subgroup.mem_sup_left l.2
  have hgM : (⟨(l : G), hgMmem⟩ : ↥(L ⊔ S)) ∈ L.subgroupOf (L ⊔ S) := Subgroup.mem_subgroupOf.2 hgL
  have hnotnorm : ¬ Subgroup.zpowers (l : G) ≤ Subgroup.normalizer (S : Set G) := by
    intro hle
    obtain ⟨s, hs, hns⟩ := E.three_cycle_not_normalize h1 h3 h12' h13 h13' h23
      (g := ⟨(l : G), hgMmem⟩) hl
    apply hns
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    have := (Subgroup.mem_normalizer_iff.1 (hle (Subgroup.mem_zpowers (l : G))) (s : G)).1 hsS
    exact Subgroup.mem_subgroupOf.2 this
  have hYX : Subgroup.zpowers (l : G) ≤ L ⊔ S := by
    rw [Subgroup.zpowers_le]; exact hgMmem
  have hYsub : blockV S L ⊓ Phi S ≤ S := inf_le_left.trans hVS
  by_cases hD : ∃ y₀ ∈ Yadd (blockV S L) S, ∃ x₀, x₀ ∉ Δ₀ ∧ E.Det y₀ x₀
  ·
    have hfaith := E.faithful_of_det hD
    have hchar := centralizer_Y_characteristic hVS hV2' hY
    set R₀ : Subgroup G :=
      S ⊓ Subgroup.centralizer ((blockV S L ⊓ Phi S : Subgroup G) : Set G) with hR₀
    have hconj : ∀ m ∈ L ⊔ S, ∀ x ∈ R₀, m * x * m⁻¹ ∈ R₀ := by
      intro m hm x hx
      have hxS : x ∈ S := hx.1
      have hxM : x ∈ L ⊔ S := Subgroup.mem_sup_right hxS
      have hθx : θ ⟨x, hxM⟩ = 1 := by
        apply hfaith ⟨x, hxM⟩ (Subgroup.mem_subgroupOf.2 hxS)
        intro y hy
        apply Additive.toMul.injective
        apply Subtype.ext
        show x * ((Additive.toMul y : blockV S L) : G) * x⁻¹ = ((Additive.toMul y : blockV S L) : G)
        have hyY : ((Additive.toMul y : blockV S L) : G) ∈ blockV S L ⊓ Phi S :=
          ⟨(Additive.toMul y).2, mem_Yadd.1 hy⟩
        have := Subgroup.mem_centralizer_iff.1 hx.2 _ hyY
        rw [mul_inv_eq_iff_eq_mul]
        exact this.symm
      have hθ' : θ ((⟨m, hm⟩ : ↥(L ⊔ S)) * ⟨x, hxM⟩ * (⟨m, hm⟩ : ↥(L ⊔ S))⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, hθx]; simp
      refine ⟨hθS _ hθ', ?_⟩
      have hcV := hf _ hθ'
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      exact Subgroup.mem_centralizer_iff.1 hcV y hy.1
    have hgN : (l : G) ∈ Subgroup.normalizer (R₀ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact fun hx => hconj _ hgMmem x hx
      · intro hx
        have := hconj _ (inv_mem hgMmem) _ hx
        simpa [mul_assoc] using this
    have hYC : Subgroup.zpowers (l : G) ≤ Subgroup.normalizer (R₀ : Set G) := by
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
      have hvV : (v : G) ∈ blockV S L := commutator_le_of_normalizes hVn v.2
      have hvR : (v : G) ∈ R₀ := ⟨hVS hvV, Subgroup.mem_centralizer_iff.2 fun y hy =>
        mul_comm_of_mem_isMulCommutative hVel.1 hy.1 hvV⟩
      rw [hbot] at hvR
      exact hv1 (Subtype.ext (Subgroup.mem_bot.1 hvR))
    have hR₀top : (R₀.subgroupOf R₀).Characteristic := by
      rw [Subgroup.subgroupOf_self]; infer_instance
    exact noCharNormal_of_asc81bHyp hA' hYX (inf_le_left : R₀ ≤ S) hchar hnotnorm R₀ le_rfl
      hR₀bot hR₀top hYC
  ·
    have hD' : ∀ y ∈ Yadd (blockV S L) S, ∀ x, x ∉ Δ₀ → ¬ E.Det y x := by
      intro y hy x hx hdet
      exact hD ⟨y, hy, x, hx, hdet⟩
    have hcomm : ∀ y ∈ blockV S L ⊓ Phi S, ∀ s ∈ S, (l : G) * ⁅y, s⁆ = ⁅y, s⁆ * (l : G) := by
      intro y hy s hs
      have hsM : s ∈ L ⊔ S := Subgroup.mem_sup_right hs
      have hcen := E.central_of_noDet hD' h1 h2 h3 hr h12 h13 h23 hr1 hr2 hr3
        (g := ⟨(l : G), hgMmem⟩) hgM hl (s := ⟨s, hsM⟩) (Subgroup.mem_subgroupOf.2 hs)
        (y := Additive.ofMul ⟨y, hy.1⟩) (mem_Yadd.2 hy.2)
      have hz : ((Additive.toMul ((conjEnd hVn ⟨s, hsM⟩) (Additive.ofMul ⟨y, hy.1⟩) -
          Additive.ofMul ⟨y, hy.1⟩) : blockV S L) : G) = s * y * s⁻¹ * y⁻¹ :=
        conj_sub_coe hVn ⟨s, hsM⟩ (Additive.ofMul ⟨y, hy.1⟩)
      have hcen' := congrArg (fun w : Additive (blockV S L) =>
        ((Additive.toMul w : blockV S L) : G)) hcen
      beta_reduce at hcen'
      have hg : ∀ w : Additive (blockV S L),
          ((Additive.toMul ((conjEnd hVn ⟨(l : G), hgMmem⟩) w) : blockV S L) : G) =
            (l : G) * ((Additive.toMul w : blockV S L) : G) * (l : G)⁻¹ := fun w => rfl
      rw [hg, hz] at hcen'
      have e : ⁅y, s⁆ = (s * y * s⁻¹ * y⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      have h' : (l : G) * (s * y * s⁻¹ * y⁻¹)⁻¹ * (l : G)⁻¹ = (s * y * s⁻¹ * y⁻¹)⁻¹ := by
        have := congrArg (fun t => t⁻¹) hcen'
        simpa [mul_assoc] using this
      rw [mul_inv_eq_iff_eq_mul] at h'
      exact h'
    have hCcen : ⁅blockV S L ⊓ Phi S, S⁆ ≤ Subgroup.centralizer (({(l : G)} : Set G)) := by
      rw [Subgroup.commutator_le]
      intro y hy s hs
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact hcomm y hy s hs
    have hconjC : ∀ x ∈ ⁅blockV S L ⊓ Phi S, S⁆, (l : G) * x * (l : G)⁻¹ = x := by
      intro x hx
      have := Subgroup.mem_centralizer_iff.1 (hCcen hx) (l : G) (Set.mem_singleton _)
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have hgN : (l : G) ∈ Subgroup.normalizer ((⁅blockV S L ⊓ Phi S, S⁆ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [hconjC x hx]; exact hx
      · intro hx
        have h1' := hconjC _ hx
        have hxx : (l : G) * x * (l : G)⁻¹ = x := by
          have h2 : (l : G) * ((l : G) * x * (l : G)⁻¹) = (l : G) * x := by
            calc (l : G) * ((l : G) * x * (l : G)⁻¹)
                = ((l : G) * ((l : G) * x * (l : G)⁻¹) * (l : G)⁻¹) * (l : G) := by group
              _ = ((l : G) * x * (l : G)⁻¹) * (l : G) := by rw [h1']
              _ = (l : G) * x := by group
          exact mul_left_cancel h2
        exact hxx ▸ hx
    have hCS : ⁅blockV S L ⊓ Phi S, S⁆ ≤ S := by
      rw [Subgroup.commutator_le]
      intro y hy s hs
      exact S.mul_mem (S.mul_mem (S.mul_mem (hYsub hy) hs) (S.inv_mem (hYsub hy))) (S.inv_mem hs)
    have hCbot : ⁅blockV S L ⊓ Phi S, S⁆ ≠ ⊥ := by
      obtain ⟨u, huY, s, hs, hne⟩ := E.comm_nonzero
      intro hbot
      have hu : ((Additive.toMul u : blockV S L) : G) ∈ blockV S L ⊓ Phi S :=
        ⟨(Additive.toMul u).2, mem_Yadd.1 huY⟩
      have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
      have hmem : ⁅(s : G), ((Additive.toMul u : blockV S L) : G)⁆ ∈ ⁅blockV S L ⊓ Phi S, S⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hsS hu
      rw [hbot, Subgroup.mem_bot] at hmem
      apply hne
      apply Additive.toMul.injective
      apply Subtype.ext
      show (s : G) * ((Additive.toMul u : blockV S L) : G) * (s : G)⁻¹ =
        ((Additive.toMul u : blockV S L) : G)
      exact mul_inv_eq_one.1 hmem
    have hchar := commutator_Y_characteristic hVS hV2' hY
    have hCtop : ((⁅blockV S L ⊓ Phi S, S⁆ : Subgroup G).subgroupOf
        (⁅blockV S L ⊓ Phi S, S⁆ : Subgroup G)).Characteristic := by
      rw [Subgroup.subgroupOf_self]; infer_instance
    exact noCharNormal_of_asc81bHyp hA' hYX hCS hchar hnotnorm _ le_rfl hCbot hCtop
      (Subgroup.zpowers_le.2 hgN)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
