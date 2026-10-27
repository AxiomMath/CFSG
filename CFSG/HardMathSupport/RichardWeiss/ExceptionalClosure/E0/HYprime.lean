module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.OmPhi
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClLambda
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Central
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Faithful
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.ThreeCycle
public import CFSG.HardMathSupport.RichardWeiss.Proving.NoCharNormal

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open
  CFSG.HardMathSupport.RichardWeiss.Proving Equiv Equiv.Perm
open scoped commutatorElement

attribute [local instance] IsMulCommutative.instCommGroup

variable {G : Type} [Group G]

section Frame

variable {V L S : Subgroup G} {N : ℕ} [IsMulCommutative V]

theorem e0Frame_of_group_gen
    (hMV : ∀ m ∈ L ⊔ S, ∀ v ∈ V, m * v * m⁻¹ ∈ V)
    (hML : ∀ m ∈ L ⊔ S, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hV2 : ∀ v ∈ V, v * v = 1) 
    (π : ↥⁅V, L⁆ →* Multiplicative (altHeart N)) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (hπ : Function.Surjective π) (hequiv : SectionEquiv ⁅V, L⁆ (L ⊔ S) π θ)
    (hAθ : ∀ σ ∈ alternatingGroup (Fin N), ∃ l : ↥L, θ ⟨(l : G), Subgroup.mem_sup_left l.2⟩ = σ)
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (V : Set G))
    (hπker : π.ker = (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅V, L⁆)
    (hSlay : S ≤ layerTriv V ⁅V, L⁆ (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)))
    {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)} {Δ₀ : Finset (Fin N)}
    (hshape : E0Shape P ω Δ₀) (hN : 10 ≤ N)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hθ : (S.subgroupOf (L ⊔ S)).map θ =
      P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)})
    (Y : AddSubgroup (Additive V))
    (hY1 : ∀ s ∈ S.subgroupOf (L ⊔ S), ∀ w : Additive V, conjEnd hMV s w - w ∈ Y)
    (hY2 : ∀ m : ↥(L ⊔ S), (∀ s ∈ S.subgroupOf (L ⊔ S), m * s * m⁻¹ ∈ S.subgroupOf (L ⊔ S)) →
      ∀ y ∈ Y, conjEnd hMV m y ∈ Y) :
    E0Frame (W := Additive V) θ (conjEnd hMV) (Uadd V L) (piAdd π) (L.subgroupOf (L ⊔ S))
      (S.subgroupOf (L ⊔ S)) P ω Δ₀ Y := by
  refine ⟨piFrame_of_group hMV hML hV2 π θ hπ hequiv hAθ hker hπker hSlay, hshape, hN,
    hshape.even_card, ?_, ?_, ?_, fun s hs u => hY1 s hs u, hY2⟩
  · intro σ
    have : σ ∈ (S.subgroupOf (L ⊔ S)).map θ ↔ σ ∈ E0grp P ω Δ₀ := by rw [hθ]; rfl
    rw [← this, Subgroup.mem_map]
  · intro m hm
    exact Subgroup.mem_subgroupOf.2 (hθS m hm)
  · intro l hl u hu
    have hl' : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
    have hπ1 : π ⟨((Additive.toMul (u : Additive V) : V) : G), u.2⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      exact hu
    have hmem : (⟨((Additive.toMul (u : Additive V) : V) : G), u.2⟩ : ↥⁅V, L⁆) ∈ π.ker :=
      MonoidHom.mem_ker.2 hπ1
    rw [hπker, Subgroup.mem_subgroupOf] at hmem
    have hc := Subgroup.mem_centralizer_iff.mp hmem.2 (l : G) hl'
    apply Additive.toMul.injective
    apply Subtype.ext
    show (l : G) * ((Additive.toMul (u : Additive V) : V) : G) * (l : G)⁻¹ =
      ((Additive.toMul (u : Additive V) : V) : G)
    rw [mul_inv_eq_iff_eq_mul]
    exact hc

omit [IsMulCommutative V] in
theorem piAdd_eq_zero_of_mem_centralizer
    (π : ↥⁅V, L⁆ →* Multiplicative (altHeart N))
    (hπker : π.ker = (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅V, L⁆)
    (u : ↥(Uadd V L))
    (hc : ((Additive.toMul (u : Additive V) : V) : G) ∈ Subgroup.centralizer (L : Set G)) :
    piAdd π u = 0 := by
  have hmem : (⟨((Additive.toMul (u : Additive V) : V) : G), u.2⟩ : ↥⁅V, L⁆) ∈ π.ker := by
    rw [hπker, Subgroup.mem_subgroupOf]
    exact ⟨u.2, hc⟩
  have h1 := MonoidHom.mem_ker.1 hmem
  show Multiplicative.toAdd (π ⟨_, _⟩) = 0
  rw [h1]; rfl

end Frame

@[expose] def YV (V C S : Subgroup G) (hVC : ∀ c ∈ C, ∀ v ∈ V, c * v = v * c) :
    AddSubgroup (Additive V) where
  carrier := {w | ∃ c ∈ C, ∃ y ∈ OmPhi S, ((Additive.toMul w : V) : G) * c = y}
  zero_mem' := ⟨1, C.one_mem, 1, (OmPhi S).one_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨c₁, hc₁, y₁, hy₁, h₁⟩ ⟨c₂, hc₂, y₂, hy₂, h₂⟩
    refine ⟨c₁ * c₂, C.mul_mem hc₁ hc₂, y₁ * y₂, (OmPhi S).mul_mem hy₁ hy₂, ?_⟩
    have hc : c₁ * ((Additive.toMul b : V) : G) = ((Additive.toMul b : V) : G) * c₁ :=
      hVC c₁ hc₁ _ (Additive.toMul b).2
    rw [← h₁, ← h₂]
    show ((Additive.toMul a : V) : G) * ((Additive.toMul b : V) : G) * (c₁ * c₂) = _
    calc ((Additive.toMul a : V) : G) * ((Additive.toMul b : V) : G) * (c₁ * c₂)
        = ((Additive.toMul a : V) : G) * (((Additive.toMul b : V) : G) * c₁) * c₂ := by group
      _ = ((Additive.toMul a : V) : G) * (c₁ * ((Additive.toMul b : V) : G)) * c₂ := by rw [hc]
      _ = _ := by group
  neg_mem' := by
    rintro a ⟨c, hc, y, hy, h⟩
    refine ⟨c⁻¹, C.inv_mem hc, y⁻¹, (OmPhi S).inv_mem hy, ?_⟩
    have hcv : c * ((Additive.toMul a : V) : G) = ((Additive.toMul a : V) : G) * c :=
      hVC c hc _ (Additive.toMul a).2
    rw [← h]
    show ((Additive.toMul a : V) : G)⁻¹ * c⁻¹ = _
    rw [← mul_inv_rev, hcv]

theorem false_of_E0_HYp [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} (hN : 10 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    {Δ₀ : Finset (Fin N)} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
    (hshape : E0Shape P ω Δ₀)
    (hθ : (S.subgroupOf (L ⊔ S)).map θ =
      P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)})
    (hJ : (S.subgroupOf (L ⊔ S)).map θ ≤ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ)
    (hY : ∀ y ∈ Phi S, y ^ 2 = 1 → ∃ v ∈ blockV S L,
      ∃ c ∈ pCoreOf 2 (L ⊔ S) ⊓ Subgroup.centralizer (L : Set G), y = v * c) : False := by
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

  have hQV : ∀ q ∈ pCoreOf 2 (L ⊔ S), ∀ v ∈ blockV S L, q * v = v * q := by
    intro q hq v hv
    exact (Subgroup.mem_centralizer_iff.mp
      (CFSG.AGLEmbedding.AscTenThree.le_centralizer_omegaOneCenterOf_self
        (pCoreOf 2 (L ⊔ S)) hq) v hv).symm
  have hQn : ∀ m ∈ L ⊔ S, ∀ q ∈ pCoreOf 2 (L ⊔ S), m * q * m⁻¹ ∈ pCoreOf 2 (L ⊔ S) :=
    fun m hm q hq =>
      (Subgroup.mem_normalizer_iff.1
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ S) hm) q).1 hq
  set Cs : Subgroup G := pCoreOf 2 (L ⊔ S) ⊓ Subgroup.centralizer (L : Set G) with hCs
  have hCV : ∀ c ∈ Cs, ∀ v ∈ blockV S L, c * v = v * c := fun c hc v hv => hQV c hc.1 v hv
  have hCn : ∀ m ∈ L ⊔ S, ∀ c ∈ Cs, m * c * m⁻¹ ∈ Cs := by
    intro m hm c hc
    refine ⟨hQn m hm c hc.1, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have hl' : m⁻¹ * l * m ∈ L := by
      have := hML m⁻¹ (inv_mem hm) l hl
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hc.2 _ hl'
    calc l * (m * c * m⁻¹) = m * ((m⁻¹ * l * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * l * m)) * m⁻¹ := by rw [h1]
      _ = (m * c * m⁻¹) * l := by group
  have hOm : ∀ y ∈ OmPhi S, ∃ v ∈ blockV S L, ∃ c ∈ Cs, y = v * c := by
    intro y hy
    rw [OmPhi_eq_closure] at hy
    induction hy using Subgroup.closure_induction with
    | mem z hz => exact hY z hz.1 hz.2
    | one => exact ⟨1, (blockV S L).one_mem, 1, Cs.one_mem, by simp⟩
    | mul a b ha hb iha ihb =>
      obtain ⟨v₁, hv₁, c₁, hc₁, rfl⟩ := iha
      obtain ⟨v₂, hv₂, c₂, hc₂, rfl⟩ := ihb
      refine ⟨v₁ * v₂, (blockV S L).mul_mem hv₁ hv₂, c₁ * c₂, Cs.mul_mem hc₁ hc₂, ?_⟩
      have h := hCV c₁ hc₁ v₂ hv₂
      calc v₁ * c₁ * (v₂ * c₂) = v₁ * (c₁ * v₂) * c₂ := by group
        _ = v₁ * (v₂ * c₁) * c₂ := by rw [h]
        _ = v₁ * v₂ * (c₁ * c₂) := by group
    | inv a ha iha =>
      obtain ⟨v, hv, c, hc, rfl⟩ := iha
      refine ⟨v⁻¹, (blockV S L).inv_mem hv, c⁻¹, Cs.inv_mem hc, ?_⟩
      have h := hCV c hc v hv
      rw [← mul_inv_rev, h]
  have hYV1 : ∀ s ∈ S.subgroupOf (L ⊔ S), ∀ w : Additive (blockV S L),
      conjEnd hVn s w - w ∈ YV (blockV S L) Cs S hCV := by
    intro s hs w
    refine ⟨1, Cs.one_mem, ((Additive.toMul (conjEnd hVn s w - w) : blockV S L) : G), ?_, by simp⟩
    · have hs' : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
      have hmemV : ((Additive.toMul (conjEnd hVn s w - w) : blockV S L) : G) ∈ blockV S L :=
        (Additive.toMul (conjEnd hVn s w - w)).2
      refine mem_OmPhi_of_involution ?_ (hV2' _ hmemV)
      rw [conj_sub_coe]
      exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hs'
        (hVS (Additive.toMul w).2))
  have hYV2 : ∀ m : ↥(L ⊔ S), (∀ s ∈ S.subgroupOf (L ⊔ S), m * s * m⁻¹ ∈ S.subgroupOf (L ⊔ S)) →
      ∀ y ∈ YV (blockV S L) Cs S hCV, conjEnd hVn m y ∈ YV (blockV S L) Cs S hCV := by
    intro m hm y ⟨c, hc, y', hy', hvc⟩
    have hm' : ∀ s ∈ S, (m : G) * s * (m : G)⁻¹ ∈ S := fun s hs => by
      have := hm ⟨s, Subgroup.mem_sup_right hs⟩ (Subgroup.mem_subgroupOf.2 hs)
      exact Subgroup.mem_subgroupOf.1 this
    refine ⟨(m : G) * c * (m : G)⁻¹, hCn _ m.2 c hc, (m : G) * y' * (m : G)⁻¹,
      conj_mem_OmPhi hm' _ hy', ?_⟩
    rw [← hvc]
    show (m : G) * ((Additive.toMul y : blockV S L) : G) * (m : G)⁻¹ * ((m : G) * c * (m : G)⁻¹) = _
    group
  have E := e0Frame_of_group_gen hVn hML hV2 π θ hπ hequiv hAθ hf hπker hSlay hshape hN hθS hθ
    (YV (blockV S L) Cs S hCV) hYV1 hYV2
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
  by_cases hD : ∃ y₀ ∈ YV (blockV S L) Cs S hCV, ∃ x₀, x₀ ∉ Δ₀ ∧ E.Det y₀ x₀
  ·
    have hchar := centralizer_OmPhi_characteristic S
    set R₀ : Subgroup G := S ⊓ Subgroup.centralizer ((OmPhi S : Subgroup G) : Set G) with hR₀
    have hθx : ∀ x ∈ R₀, ∃ hxM : x ∈ L ⊔ S, θ ⟨x, hxM⟩ = 1 := by
      intro x hx
      have hxS : x ∈ S := hx.1
      have hxM : x ∈ L ⊔ S := Subgroup.mem_sup_right hxS
      refine ⟨hxM, E.faithful_of_det_pi hD ⟨x, hxM⟩ (Subgroup.mem_subgroupOf.2 hxS) ?_⟩
      intro w hw
      obtain ⟨c, hc, y, hy, hvc⟩ := hw
      have hxy : y * x = x * y := Subgroup.mem_centralizer_iff.1 hx.2 y hy
      have hv : ((Additive.toMul w : blockV S L) : G) ∈ blockV S L := (Additive.toMul w).2
      set v : G := ((Additive.toMul w : blockV S L) : G) with hvdef
      have h1 : x * (v * c) * x⁻¹ = v * c := by
        rw [hvc, ← hxy]; simp
      have key : x * v * x⁻¹ = v * c * (x * c * x⁻¹)⁻¹ :=
        calc x * v * x⁻¹ = (x * (v * c) * x⁻¹) * (x * c⁻¹ * x⁻¹) := by group
          _ = (v * c) * (x * c⁻¹ * x⁻¹) := by rw [h1]
          _ = v * c * (x * c * x⁻¹)⁻¹ := by group
      have hz : c * (x * c * x⁻¹)⁻¹ ∈ Cs :=
        Cs.mul_mem hc (Cs.inv_mem (hCn x hxM c hc))
      have hzv := hCV _ hz v hv
      have hcc : ((Additive.toMul ((conjEnd hVn ⟨x, hxM⟩) w - w) : blockV S L) : G) ∈
          Subgroup.centralizer (L : Set G) := by
        rw [conj_sub_coe]
        show x * v * x⁻¹ * v⁻¹ ∈ _
        have : x * v * x⁻¹ * v⁻¹ = c * (x * c * x⁻¹)⁻¹ := by
          rw [key]
          have hconjz : v * (c * (x * c * x⁻¹)⁻¹) * v⁻¹ = c * (x * c * x⁻¹)⁻¹ := by
            rw [mul_inv_eq_iff_eq_mul]; exact hzv.symm
          calc v * c * (x * c * x⁻¹)⁻¹ * v⁻¹ = v * (c * (x * c * x⁻¹)⁻¹) * v⁻¹ := by group
            _ = c * (x * c * x⁻¹)⁻¹ := hconjz
        rw [this]
        exact hz.2
      exact piAdd_eq_zero_of_mem_centralizer π hπker _ hcc
    have hconj : ∀ m ∈ L, ∀ x ∈ R₀, m * x * m⁻¹ ∈ R₀ := by
      intro m hmL x hx
      have hmM : m ∈ L ⊔ S := Subgroup.mem_sup_left hmL
      have hxS : x ∈ S := hx.1
      obtain ⟨hxM, hθ1⟩ := hθx x hx
      have hθ' : θ ((⟨m, hmM⟩ : ↥(L ⊔ S)) * ⟨x, hxM⟩ * (⟨m, hmM⟩ : ↥(L ⊔ S))⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, hθ1]; simp
      refine ⟨hθS _ hθ', Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      obtain ⟨v, hv, c, hc, rfl⟩ := hOm h hh
      have hxV : ∀ u ∈ blockV S L, u * x = x * u := fun u hu =>
        Subgroup.mem_centralizer_iff.1 (hf _ hθ1) u hu
      have hxh : (v * c) * x = x * (v * c) := Subgroup.mem_centralizer_iff.1 hx.2 _ hh
      have hxc : c * x = x * c := by
        have h2 : v * (c * x) = v * (x * c) := by
          calc v * (c * x) = v * c * x := by group
            _ = x * (v * c) := hxh
            _ = (x * v) * c := by group
            _ = (v * x) * c := by rw [(hxV v hv).symm]
            _ = v * (x * c) := by group
        exact mul_left_cancel h2
      have hv' : m⁻¹ * v * m ∈ blockV S L := by
        have := hVn m⁻¹ (inv_mem hmM) v hv
        simpa using this
      have hcm : m⁻¹ * c * m = c := by
        have := Subgroup.mem_centralizer_iff.1 hc.2 m⁻¹ (inv_mem hmL)
        rw [this]; group
      have hx' : (m⁻¹ * v * m * c) * x = x * (m⁻¹ * v * m * c) := by
        calc m⁻¹ * v * m * c * x = (m⁻¹ * v * m) * (c * x) := by group
          _ = (m⁻¹ * v * m) * (x * c) := by rw [hxc]
          _ = ((m⁻¹ * v * m) * x) * c := by group
          _ = (x * (m⁻¹ * v * m)) * c := by rw [hxV _ hv']
          _ = x * (m⁻¹ * v * m * c) := by group
      calc v * c * (m * x * m⁻¹) = m * ((m⁻¹ * v * m * c) * x) * m⁻¹ := by
            have : m * (m⁻¹ * v * m * c) = v * c * m := by
              calc m * (m⁻¹ * v * m * c) = v * (m * c) := by group
                _ = v * (c * m) := by
                    have := Subgroup.mem_centralizer_iff.1 hc.2 m hmL
                    rw [this]
                _ = v * c * m := by group
            calc v * c * (m * x * m⁻¹) = (v * c * m) * x * m⁻¹ := by group
              _ = (m * (m⁻¹ * v * m * c)) * x * m⁻¹ := by rw [this]
              _ = m * ((m⁻¹ * v * m * c) * x) * m⁻¹ := by group
        _ = m * (x * (m⁻¹ * v * m * c)) * m⁻¹ := by rw [hx']
        _ = (m * x * m⁻¹) * (v * c) := by
            have : m * (m⁻¹ * v * m * c) * m⁻¹ = v * c := by
              have h2 : (m * c * m⁻¹) = c := by
                have := Subgroup.mem_centralizer_iff.1 hc.2 m hmL
                exact mul_inv_eq_iff_eq_mul.2 this
              calc m * (m⁻¹ * v * m * c) * m⁻¹ = v * (m * c * m⁻¹) := by group
                _ = v * c := by rw [h2]
            calc m * (x * (m⁻¹ * v * m * c)) * m⁻¹
                = (m * x * m⁻¹) * (m * (m⁻¹ * v * m * c) * m⁻¹) := by group
              _ = (m * x * m⁻¹) * (v * c) := by rw [this]
    have hgN : (l : G) ∈ Subgroup.normalizer (R₀ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact fun hx => hconj _ hgL x hx
      · intro hx
        have := hconj _ (inv_mem hgL) _ hx
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
      have hvR : (v : G) ∈ R₀ := by
        refine ⟨hVS hvV, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        obtain ⟨v', hv', c, hc, rfl⟩ := hOm y hy
        have h1 : (v : G) * v' = v' * v := mul_comm_of_mem_isMulCommutative hVel.1 hvV hv'
        have h2 : (v : G) * c = c * v := (hCV c hc _ hvV).symm
        calc v' * c * (v : G) = v' * (c * (v : G)) := by group
          _ = v' * ((v : G) * c) := by rw [h2]
          _ = (v' * (v : G)) * c := by group
          _ = ((v : G) * v') * c := by rw [h1]
          _ = (v : G) * (v' * c) := by group
      rw [hbot] at hvR
      exact hv1 (Subtype.ext (Subgroup.mem_bot.1 hvR))
    have hR₀top : (R₀.subgroupOf R₀).Characteristic := by
      rw [Subgroup.subgroupOf_self]; infer_instance
    exact noCharNormal_of_asc81bHyp hA' hYX (inf_le_left : R₀ ≤ S) hchar hnotnorm R₀ le_rfl
      hR₀bot hR₀top hYC
  ·
    have hD' : ∀ y ∈ YV (blockV S L) Cs S hCV, ∀ x, x ∉ Δ₀ → ¬ E.Det y x := by
      intro y hy x hx hdet
      exact hD ⟨y, hy, x, hx, hdet⟩
    have hdecomp : ∀ (v c s : G), v ∈ blockV S L → c ∈ Cs → s ∈ L ⊔ S →
        s * (v * c) * s⁻¹ * (v * c)⁻¹ =
          (s * v * s⁻¹ * v⁻¹) * (s * c * s⁻¹ * c⁻¹) := by
      intro v c s hv hc hs
      have hE : s * c * s⁻¹ * c⁻¹ ∈ Cs := Cs.mul_mem (hCn s hs c hc) (Cs.inv_mem hc)
      have he := hCV _ hE v⁻¹ ((blockV S L).inv_mem hv)
      calc s * (v * c) * s⁻¹ * (v * c)⁻¹
          = (s * v * s⁻¹) * ((s * c * s⁻¹ * c⁻¹) * v⁻¹) := by group
        _ = (s * v * s⁻¹) * (v⁻¹ * (s * c * s⁻¹ * c⁻¹)) := by rw [he]
        _ = (s * v * s⁻¹ * v⁻¹) * (s * c * s⁻¹ * c⁻¹) := by group
    have hcomm : ∀ y ∈ OmPhi S, ∀ s ∈ S, (l : G) * ⁅y, s⁆ = ⁅y, s⁆ * (l : G) := by
      intro y hy s hs
      have hsM : s ∈ L ⊔ S := Subgroup.mem_sup_right hs
      obtain ⟨v, hv, c, hc, rfl⟩ := hOm y hy
      have hw : (Additive.ofMul (⟨v, hv⟩ : blockV S L) : Additive (blockV S L)) ∈
          YV (blockV S L) Cs S hCV := ⟨c, hc, v * c, hy, rfl⟩
      have hcen := E.central_of_noDet hD' h1 h2 h3 hr h12 h13 h23 hr1 hr2 hr3
        (g := ⟨(l : G), hgMmem⟩) hgM hl (s := ⟨s, hsM⟩) (Subgroup.mem_subgroupOf.2 hs)
        (y := Additive.ofMul ⟨v, hv⟩) hw
      have hz : ((Additive.toMul ((conjEnd hVn ⟨s, hsM⟩) (Additive.ofMul ⟨v, hv⟩) -
          Additive.ofMul ⟨v, hv⟩) : blockV S L) : G) = s * v * s⁻¹ * v⁻¹ :=
        conj_sub_coe hVn ⟨s, hsM⟩ (Additive.ofMul ⟨v, hv⟩)
      have hcen' := congrArg (fun w : Additive (blockV S L) =>
        ((Additive.toMul w : blockV S L) : G)) hcen
      beta_reduce at hcen'
      have hg : ∀ w : Additive (blockV S L),
          ((Additive.toMul ((conjEnd hVn ⟨(l : G), hgMmem⟩) w) : blockV S L) : G) =
            (l : G) * ((Additive.toMul w : blockV S L) : G) * (l : G)⁻¹ := fun w => rfl
      rw [hg, hz] at hcen'
      have ha : (l : G) * (s * v * s⁻¹ * v⁻¹) = (s * v * s⁻¹ * v⁻¹) * (l : G) := by
        rw [← mul_inv_eq_iff_eq_mul]; exact hcen'
      have hE : s * c * s⁻¹ * c⁻¹ ∈ Cs := Cs.mul_mem (hCn s hsM c hc) (Cs.inv_mem hc)
      have hb : (l : G) * (s * c * s⁻¹ * c⁻¹) = (s * c * s⁻¹ * c⁻¹) * (l : G) :=
        Subgroup.mem_centralizer_iff.1 hE.2 (l : G) hgL
      have hab : (l : G) * ((s * v * s⁻¹ * v⁻¹) * (s * c * s⁻¹ * c⁻¹)) =
          ((s * v * s⁻¹ * v⁻¹) * (s * c * s⁻¹ * c⁻¹)) * (l : G) := by
        calc (l : G) * ((s * v * s⁻¹ * v⁻¹) * (s * c * s⁻¹ * c⁻¹))
            = ((l : G) * (s * v * s⁻¹ * v⁻¹)) * (s * c * s⁻¹ * c⁻¹) := by group
          _ = ((s * v * s⁻¹ * v⁻¹) * (l : G)) * (s * c * s⁻¹ * c⁻¹) := by rw [ha]
          _ = (s * v * s⁻¹ * v⁻¹) * ((l : G) * (s * c * s⁻¹ * c⁻¹)) := by group
          _ = (s * v * s⁻¹ * v⁻¹) * ((s * c * s⁻¹ * c⁻¹) * (l : G)) := by rw [hb]
          _ = _ := by group
      have e : ⁅v * c, s⁆ = (s * (v * c) * s⁻¹ * (v * c)⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e, hdecomp v c s hv hc hsM]
      exact Commute.inv_right hab
    have hCcen : ⁅OmPhi S, S⁆ ≤ Subgroup.centralizer (({(l : G)} : Set G)) := by
      rw [Subgroup.commutator_le]
      intro y hy s hs
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact hcomm y hy s hs
    have hconjC : ∀ x ∈ ⁅OmPhi S, S⁆, (l : G) * x * (l : G)⁻¹ = x := by
      intro x hx
      have := Subgroup.mem_centralizer_iff.1 (hCcen hx) (l : G) (Set.mem_singleton _)
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have hgN : (l : G) ∈ Subgroup.normalizer ((⁅OmPhi S, S⁆ : Subgroup G) : Set G) := by
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
    have hCS : ⁅OmPhi S, S⁆ ≤ S := by
      rw [Subgroup.commutator_le]
      intro y hy s hs
      exact S.mul_mem (S.mul_mem (S.mul_mem (OmPhi_le_S S hy) hs) (S.inv_mem (OmPhi_le_S S hy)))
        (S.inv_mem hs)
    have hCbot : ⁅OmPhi S, S⁆ ≠ ⊥ := by
      obtain ⟨u, ⟨c, hc, y, hy, hvc⟩, s, hs, hne⟩ := E.comm_nonzero_pi
      intro hbot
      have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
      have hsM : (s : G) ∈ L ⊔ S := (s : ↥(L ⊔ S)).2
      have hmem : ⁅(s : G), y⁆ ∈ ⁅OmPhi S, S⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hsS hy
      rw [hbot, Subgroup.mem_bot] at hmem
      have hmem' : (s : G) * y * (s : G)⁻¹ * y⁻¹ = 1 := by
        simpa [commutatorElement_def] using hmem
      have hv : ((Additive.toMul u : blockV S L) : G) ∈ blockV S L := (Additive.toMul u).2
      rw [← hvc, hdecomp _ _ _ hv hc hsM] at hmem'
      have hE : (s : G) * c * (s : G)⁻¹ * c⁻¹ ∈ Cs :=
        Cs.mul_mem (hCn _ hsM c hc) (Cs.inv_mem hc)
      have hmem'' : (s : G) * ((Additive.toMul u : blockV S L) : G) * (s : G)⁻¹ *
          ((Additive.toMul u : blockV S L) : G)⁻¹ ∈ Cs := by
        have : (s : G) * ((Additive.toMul u : blockV S L) : G) * (s : G)⁻¹ *
            ((Additive.toMul u : blockV S L) : G)⁻¹ = ((s : G) * c * (s : G)⁻¹ * c⁻¹)⁻¹ :=
          eq_inv_of_mul_eq_one_left hmem'
        rw [this]; exact Cs.inv_mem hE
      apply hne
      have hcc : ((Additive.toMul ((conjEnd hVn s) u - u) : blockV S L) : G) ∈
          Subgroup.centralizer (L : Set G) := by
        rw [conj_sub_coe]; exact hmem''.2
      exact piAdd_eq_zero_of_mem_centralizer π hπker _ hcc
    have hCtop : ((⁅OmPhi S, S⁆ : Subgroup G).subgroupOf
        (⁅OmPhi S, S⁆ : Subgroup G)).Characteristic := by
      rw [Subgroup.subgroupOf_self]; infer_instance
    exact noCharNormal_of_asc81bHyp hA' hYX hCS (commutator_OmPhi_characteristic S) hnotnorm _
      le_rfl hCbot hCtop (Subgroup.zpowers_le.2 hgN)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
