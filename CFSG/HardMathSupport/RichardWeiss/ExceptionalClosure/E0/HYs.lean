module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.OmZPhi
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaShapes
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Central
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Faithful
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.ThreeCycle
public import CFSG.HardMathSupport.RichardWeiss.Proving.NoCharNormal
public import CFSG.HardMathSupport.RichardWeiss.Proving.ShortAux
public import CFSG.HardMathSupport.RichardWeiss.Proving.ShortFrame

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
  CFSG.HardMathSupport.RichardWeiss.Proving Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G]

theorem blockV_comm (S L : Subgroup G) {q v : G} (hq : q ∈ pCoreOf 2 (L ⊔ S))
    (hv : v ∈ blockV S L) : q * v = v * q :=
  (Subgroup.mem_centralizer_iff.1
    (AscTenThree.le_centralizer_omegaOneCenterOf_self (pCoreOf 2 (L ⊔ S)) hq) v hv).symm

@[expose] def Qs (S L : Subgroup G) : Subgroup G where
  carrier := {q | q ∈ pCoreOf 2 (L ⊔ S) ∧ ∀ l ∈ L, ⁅q, l⁆ ∈ blockV S L}
  one_mem' := ⟨(pCoreOf 2 (L ⊔ S)).one_mem, fun l _ => by simp [commutatorElement_def]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(pCoreOf 2 (L ⊔ S)).mul_mem ha hb, fun l hl => ?_⟩
    have e : ⁅a * b, l⁆ = ⁅b, l⁆ * ⁅a, l⁆ := by
      have h := blockV_comm S L ha (hb' l hl)
      calc ⁅a * b, l⁆ = a * ⁅b, l⁆ * a⁻¹ * ⁅a, l⁆ := by
            simp only [commutatorElement_def]; group
        _ = ⁅b, l⁆ * a * a⁻¹ * ⁅a, l⁆ := by rw [h]
        _ = ⁅b, l⁆ * ⁅a, l⁆ := by group
    rw [e]
    exact (blockV S L).mul_mem (hb' l hl) (ha' l hl)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(pCoreOf 2 (L ⊔ S)).inv_mem ha, fun l hl => ?_⟩
    have h := blockV_comm S L ha ((blockV S L).inv_mem (ha' l hl))
    have e : ⁅a⁻¹, l⁆ = ⁅a, l⁆⁻¹ := by
      calc ⁅a⁻¹, l⁆ = a⁻¹ * ⁅a, l⁆⁻¹ * a := by simp only [commutatorElement_def]; group
        _ = a⁻¹ * (⁅a, l⁆⁻¹ * a) := by group
        _ = a⁻¹ * (a * ⁅a, l⁆⁻¹) := by rw [← h]
        _ = ⁅a, l⁆⁻¹ := by group
    rw [e]
    exact (blockV S L).inv_mem (ha' l hl)

theorem shortData_Qs [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    ShortData (Qs S L) L (blockV S L) S := by
  have hQS : pCoreOf 2 (L ⊔ S) ≤ S := twoCore_sup_le hA hL hSL
  have hMQ : L ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ S) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ S)
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) := sup_le_normalizer_blockV S L
  have hVel : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hVn : ∀ m ∈ L ⊔ S, ∀ v ∈ blockV S L, m * v * m⁻¹ ∈ blockV S L := fun m hm v hv =>
    (Subgroup.mem_normalizer_iff.1 (hMV hm) v).1 hv
  have hML : ∀ m ∈ L ⊔ S, ∀ l ∈ L, m * l * m⁻¹ ∈ L := by
    intro m hm l hl
    have hmN : m ∈ Subgroup.normalizer (L : Set G) :=
      (sup_le (Subgroup.le_normalizer) hSL) hm
    exact (Subgroup.mem_normalizer_iff.1 hmN l).1 hl
  have hVQ : blockV S L ≤ pCoreOf 2 (L ⊔ S) := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _
  refine ⟨fun q hq => Subgroup.mem_sup_right (hQS hq.1), fun q hq => hQS hq.1, ?_, hML, hVn, ?_, ?_, ?_,
    hL.toIsTwoPrimeComponent.perfect, ?_⟩
  · intro m hm q hq
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hMQ hm) q).1 hq.1, fun l hl => ?_⟩
    have hl' : m⁻¹ * l * m ∈ L := by
      have := hML m⁻¹ (Subgroup.inv_mem _ hm) l hl
      simpa using this
    have e : ⁅m * q * m⁻¹, l⁆ = m * ⁅q, m⁻¹ * l * m⁆ * m⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hVn m hm _ (hq.2 _ hl')
  · intro v hv
    refine ⟨hVQ hv, fun l hl => ?_⟩
    have h1 := hVn l (Subgroup.mem_sup_left hl) v⁻¹ ((blockV S L).inv_mem hv)
    have : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact (blockV S L).mul_mem hv h1
  · intro q hq v hv
    exact blockV_comm S L hq.1 hv
  · intro v hv
    have := hVel.2 v hv
    rwa [pow_two] at this
  · rw [Subgroup.commutator_le]
    intro q hq l hl
    exact hq.2 l hl

section FrameGen

variable {Q L V S : Subgroup G}

@[expose] def YY (Q L Y : Subgroup G) [ShortCtx Q L] : AddSubgroup (Additive (↥Q ⧸ CQ Q L)) :=
  Subgroup.toAddSubgroup ((Y.subgroupOf Q).map (QuotientGroup.mk' (CQ Q L)))

theorem mem_YY [ShortCtx Q L] {Y : Subgroup G} {x : Additive (↥Q ⧸ CQ Q L)} :
    x ∈ YY Q L Y ↔ ∃ u : ↥Q, (u : G) ∈ Y ∧ QuotientGroup.mk u = Additive.toMul x := by
  show Additive.toMul x ∈ (Y.subgroupOf Q).map (QuotientGroup.mk' (CQ Q L)) ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, h⟩
    exact ⟨u, Subgroup.mem_subgroupOf.1 hu, h⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨u, Subgroup.mem_subgroupOf.2 hu, h⟩

variable {N : ℕ} [ShortCtx Q L] {π : ↥⁅V, L⁆ →* Multiplicative (altHeart N)}
  {θ : ↥(L ⊔ S) →* Perm (Fin N)}

theorem e0Frame_of_short_gen (hN : 10 ≤ N) (D : ShortData Q L V S)
    (H : ShortSection Q L V S π θ)
    {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)} {Δ₀ : Finset (Fin N)}
    (hshape : E0Shape P ω Δ₀)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hθ : (S.subgroupOf (L ⊔ S)).map θ =
      P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)})
    (Y : AddSubgroup (Additive (↥Q ⧸ CQ Q L)))
    (hY1 : ∀ s ∈ S.subgroupOf (L ⊔ S), ∀ u : ↥(UW Q V L),
      rhoQ D.hMQ D.hML s u - u ∈ Y)
    (hY2 : ∀ m : ↥(L ⊔ S), (∀ s ∈ S.subgroupOf (L ⊔ S), m * s * m⁻¹ ∈ S.subgroupOf (L ⊔ S)) →
      ∀ y ∈ Y, rhoQ D.hMQ D.hML m y ∈ Y) :
    E0Frame (W := Additive (↥Q ⧸ CQ Q L)) θ (rhoQ D.hMQ D.hML) (UW Q V L) (piW H)
      (L.subgroupOf (L ⊔ S)) (S.subgroupOf (L ⊔ S)) P ω Δ₀ Y := by
  have hev : Even N := hshape.even_card
  refine ⟨piFrame_of_short (by omega) hev D H, hshape, hN, hev, ?_, ?_, ?_, hY1, hY2⟩
  · intro σ
    have : σ ∈ (S.subgroupOf (L ⊔ S)).map θ ↔ σ ∈ E0grp P ω Δ₀ := by rw [hθ]; rfl
    rw [← this, Subgroup.mem_map]
  · intro m hm
    exact Subgroup.mem_subgroupOf.2 (hθS m hm)
  · intro l hl u hu
    have h0 := piW_zero_iff D H u hu
    rw [h0, map_zero]

end FrameGen

theorem comm_blockV_mem_OmPhi [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {s v : G} (hs : s ∈ S)
    (hv : v ∈ blockV S L) : s * v * s⁻¹ * v⁻¹ ∈ OmPhi S := by
  have D := shortData_Qs hA hL hSL
  have hVel : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hVS : blockV S L ≤ S := D.hVQ.trans D.hQS
  have hcV : s * v * s⁻¹ * v⁻¹ ∈ blockV S L :=
    (blockV S L).mul_mem (D.hMV s (Subgroup.mem_sup_right hs) v hv) ((blockV S L).inv_mem hv)
  exact mem_OmPhi_of_involution
    (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hs (hVS hv))) (hVel.2 _ hcV)

theorem false_of_E0_core [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} (hN : 10 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    {Δ₀ : Finset (Fin N)} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
    (hshape : E0Shape P ω Δ₀)
    (hθ : (S.subgroupOf (L ⊔ S)).map θ =
      P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)})
    (Qx : Subgroup G) (D : ShortData Qx L (blockV S L) S) (hQxs : Qx ≤ Qs S L)
    (Y : Subgroup G) (hYS : Y ≤ S) (hYch : (Y.subgroupOf S).Characteristic)
    (hYcomm : ∀ s ∈ S, ∀ v ∈ ⁅blockV S L, L⁆, s * v * s⁻¹ * v⁻¹ ∈ Y) (hOQ : Y ≤ Qx)
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 → ∀ y ∈ Qx,
      ⁅(m : G), y⁆ ∈ Qx ⊓ Subgroup.centralizer (L : Set G)) : False := by
  classical
  have hA' : Asc81bHyp (L ⊔ S) S := asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hQ2full : IsPGroup 2 (pCoreOf 2 (L ⊔ S)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQsle : Qx ≤ pCoreOf 2 (L ⊔ S) := fun q hq => (hQxs hq).1
  have hQ2 : IsPGroup 2 Qx := hQ2full.to_le hQsle
  have hVn : ∀ m ∈ L ⊔ S, ∀ v ∈ blockV S L, m * v * m⁻¹ ∈ blockV S L := D.hMV
  have hVel : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hV2 : ∀ v ∈ blockV S L, v * v = 1 := D.hV2
  have hVS : blockV S L ≤ S := (D.hVQ.trans D.hQS)
  obtain ⟨π, hπ, hπker, hAθ, hequiv, hf⟩ := hNS
  have H : ShortSection Qx L (blockV S L) S π θ := ⟨hequiv, hπker, hπ, hAθ, hker⟩
  have := D.shortCtx
  have hY1 : ∀ s ∈ S.subgroupOf (L ⊔ S), ∀ u : ↥(UW (Qx) (blockV S L) L),
      rhoQ D.hMQ D.hML s u - u ∈ YY Qx L Y := by
    intro s hs u
    have hs' : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    obtain ⟨q, hqU, hq⟩ := mem_UW.1 u.2
    have hqV : (q : G) ∈ blockV S L := D.commutator_le hqU
    have hcq : (s : G) * q * (s : G)⁻¹ * (q : G)⁻¹ ∈ Qx :=
      (Qx).mul_mem (D.hMQ s s.2 q q.2) ((Qx).inv_mem q.2)
    have hcV : (s : G) * q * (s : G)⁻¹ * (q : G)⁻¹ ∈ blockV S L :=
      (blockV S L).mul_mem (hVn s s.2 q hqV) ((blockV S L).inv_mem hqV)
    have hmem : (s : G) * q * (s : G)⁻¹ * (q : G)⁻¹ ∈ Y := hYcomm s hs' q hqU
    refine mem_YY.2 ⟨⟨_, hcq⟩, hmem, ?_⟩
    rw [toMul_sub, toMul_rhoQ D, ← hq, convQ_mk]
    show (QuotientGroup.mk _ : ↥(Qx) ⧸ CQ (Qx) L) =
      QuotientGroup.mk (conjQ D.hMQ s q) / QuotientGroup.mk q
    rw [div_eq_mul_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
  have hY2 : ∀ m : ↥(L ⊔ S), (∀ s ∈ S.subgroupOf (L ⊔ S), m * s * m⁻¹ ∈ S.subgroupOf (L ⊔ S)) →
      ∀ y ∈ YY Qx L Y, rhoQ D.hMQ D.hML m y ∈ YY Qx L Y := by
    intro m hm y hy
    obtain ⟨q, hqS, hq⟩ := mem_YY.1 hy
    have hm' : ∀ s ∈ S, (m : G) * s * (m : G)⁻¹ ∈ S := fun s hs => by
      have := hm ⟨s, Subgroup.mem_sup_right hs⟩ (Subgroup.mem_subgroupOf.2 hs)
      exact Subgroup.mem_subgroupOf.1 this
    refine mem_YY.2 ⟨conjQ D.hMQ m q, conj_mem_of_char hYS hYch hm' _ hqS, ?_⟩
    rw [toMul_rhoQ D, ← hq, convQ_mk]
  have E := e0Frame_of_short_gen hN D H hshape hθS hθ (YY Qx L Y) hY1 hY2
  have hcommS : ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ S := fun a ha b hb =>
    S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
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
  have hrho : ∀ (m : ↥(L ⊔ S)) (q : ↥(Qx)),
      rhoQ D.hMQ D.hML m (Additive.ofMul (QuotientGroup.mk q : ↥(Qx) ⧸ CQ (Qx) L)) =
        Additive.ofMul (QuotientGroup.mk (conjQ D.hMQ m q)) := fun m q => rfl
  by_cases hD : ∃ y₀ ∈ YY Qx L Y, ∃ x₀, x₀ ∉ Δ₀ ∧ E.Det y₀ x₀
  ·
    have hfaith := E.faithful_of_det hD
    have hchar := centralizer_characteristic hYS hYch
    set R₀ : Subgroup G := S ⊓ Subgroup.centralizer ((Y : Subgroup G) : Set G) with hR₀
    have hθx : ∀ x ∈ R₀, ∃ hxM : x ∈ L ⊔ S, θ ⟨x, hxM⟩ = 1 := by
      intro x hx
      have hxS : x ∈ S := hx.1
      have hxM : x ∈ L ⊔ S := Subgroup.mem_sup_right hxS
      refine ⟨hxM, ?_⟩
      apply hfaith ⟨x, hxM⟩ (Subgroup.mem_subgroupOf.2 hxS)
      intro y hy
      obtain ⟨u, hu, hmk⟩ := mem_YY.1 hy
      have hy' : y = Additive.ofMul (QuotientGroup.mk u : ↥(Qx) ⧸ CQ (Qx) L) := by
        rw [hmk]; rfl
      rw [hy', hrho]
      congr 2
      apply Subtype.ext
      show x * (u : G) * x⁻¹ = u
      have := Subgroup.mem_centralizer_iff.1 hx.2 u hu
      rw [mul_inv_eq_iff_eq_mul]; exact this.symm
    have hconj : ∀ m ∈ L, ∀ x ∈ R₀, m * x * m⁻¹ ∈ R₀ := by
      intro m hmL x hx
      have hmM : m ∈ L ⊔ S := Subgroup.mem_sup_left hmL
      have hxS : x ∈ S := hx.1
      obtain ⟨hxM, hθ1⟩ := hθx x hx
      have hθ' : θ ((⟨m, hmM⟩ : ↥(L ⊔ S)) * ⟨x, hxM⟩ * (⟨m, hmM⟩ : ↥(L ⊔ S))⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, hθ1]; simp
      refine ⟨hθS _ hθ', Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      have hxV : ∀ u ∈ blockV S L, u * x = x * u := fun u hu =>
        Subgroup.mem_centralizer_iff.1 (hf _ hθ1) u hu
      have hxh : h * x = x * h := Subgroup.mem_centralizer_iff.1 hx.2 h hh
      obtain ⟨v₀, hv₀, hv₀e⟩ : ∃ v₀ ∈ blockV S L, h * m * h⁻¹ * m⁻¹ = v₀ :=
        ⟨⁅h, m⁆, (hQxs (hOQ hh)).2 m hmL, rfl⟩
      have hv₁ : m⁻¹ * v₀ * m ∈ blockV S L := by
        have := hVn m⁻¹ (Subgroup.inv_mem _ hmM) v₀ hv₀
        simpa using this
      have hconj1 : m⁻¹ * h * m = (m⁻¹ * v₀ * m) * h := by
        have e1 : h * m = v₀ * m * h := by
          calc h * m = (h * m * h⁻¹ * m⁻¹) * m * h := by group
            _ = v₀ * m * h := by rw [hv₀e]
        calc m⁻¹ * h * m = m⁻¹ * (h * m) := by group
          _ = m⁻¹ * (v₀ * m * h) := by rw [e1]
          _ = (m⁻¹ * v₀ * m) * h := by group
      have hx1 : ((m⁻¹ * v₀ * m) * h) * x = x * ((m⁻¹ * v₀ * m) * h) := by
        calc ((m⁻¹ * v₀ * m) * h) * x = (m⁻¹ * v₀ * m) * (h * x) := by group
          _ = (m⁻¹ * v₀ * m) * (x * h) := by rw [hxh]
          _ = ((m⁻¹ * v₀ * m) * x) * h := by group
          _ = (x * (m⁻¹ * v₀ * m)) * h := by rw [hxV _ hv₁]
          _ = x * ((m⁻¹ * v₀ * m) * h) := by group
      rw [← hconj1] at hx1
      calc h * (m * x * m⁻¹) = m * ((m⁻¹ * h * m) * x) * m⁻¹ := by group
        _ = m * (x * (m⁻¹ * h * m)) * m⁻¹ := by rw [hx1]
        _ = (m * x * m⁻¹) * h := by group
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
      have hvR : (v : G) ∈ R₀ := by
        refine ⟨hVS hvV, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        exact blockV_comm S L (hQxs (hOQ hy)).1 hvV
      rw [hbot] at hvR
      exact hv1 (Subtype.ext (Subgroup.mem_bot.1 hvR))
    have hR₀top : (R₀.subgroupOf R₀).Characteristic := by
      rw [Subgroup.subgroupOf_self]; infer_instance
    exact noCharNormal_of_asc81bHyp hA' hYX (inf_le_left : R₀ ≤ S) hchar hnotnorm R₀ le_rfl
      hR₀bot hR₀top hYC
  ·
    have hD' : ∀ y ∈ YY Qx L Y, ∀ x, x ∉ Δ₀ → ¬ E.Det y x := by
      intro y hy x hx hdet
      exact hD ⟨y, hy, x, hx, hdet⟩
    have hgQ : ∀ q ∈ Qx, (g : G) * q * (g : G)⁻¹ ∈ Qx := fun q hq =>
      D.hMQ g hgMmem q hq
    have hcomm : ∀ u ∈ Y, ∀ s ∈ S, (g : G) * (s * u * s⁻¹ * u⁻¹) =
        (s * u * s⁻¹ * u⁻¹) * (g : G) := by
      intro u hu s hs
      have hsM : s ∈ L ⊔ S := Subgroup.mem_sup_right hs
      have huQ : u ∈ Qx := hOQ hu
      have hcQ : s * u * s⁻¹ * u⁻¹ ∈ Qx :=
        (Qx).mul_mem (D.hMQ s hsM u huQ) ((Qx).inv_mem huQ)
      have hy : Additive.ofMul (QuotientGroup.mk (⟨u, huQ⟩ : ↥(Qx)) :
          ↥(Qx) ⧸ CQ (Qx) L) ∈ YY Qx L Y :=
        mem_YY.2 ⟨⟨u, huQ⟩, hu, rfl⟩
      have hcen := E.central_of_noDet hD' h1 h2 h3 hr h12 h13 h23 hr1 hr2 hr3 hgM hθg
        (s := ⟨s, hsM⟩) (Subgroup.mem_subgroupOf.2 hs) hy
      have hz : rhoQ D.hMQ D.hML ⟨s, hsM⟩ (Additive.ofMul (QuotientGroup.mk
            (⟨u, huQ⟩ : ↥(Qx)) : ↥(Qx) ⧸ CQ (Qx) L)) -
            Additive.ofMul (QuotientGroup.mk (⟨u, huQ⟩ : ↥(Qx)) :
              ↥(Qx) ⧸ CQ (Qx) L) =
          Additive.ofMul (QuotientGroup.mk (⟨s * u * s⁻¹ * u⁻¹, hcQ⟩ : ↥(Qx)) :
            ↥(Qx) ⧸ CQ (Qx) L) := by
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
          (d := ((conjQ D.hMQ g ⟨s * u * s⁻¹ * u⁻¹, hcQ⟩)⁻¹ *
            ⟨s * u * s⁻¹ * u⁻¹, hcQ⟩ : ↥(Qx)))
          rfl hgd
      exact mul_inv_eq_iff_eq_mul.1 hfix
    have hCS : ⁅Y, S⁆ ≤ S := by
      rw [Subgroup.commutator_le]
      intro y hy s hs
      exact hcommS y (hYS hy) s hs
    have hCcen : ⁅Y, S⁆ ≤ Subgroup.centralizer (({(g : G)} : Set G)) := by
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
    have hgN : (g : G) ∈ Subgroup.normalizer ((⁅Y, S⁆ : Subgroup G) : Set G) := by
      have : (g : G) ∈ Subgroup.centralizer ((⁅Y, S⁆ : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have := Subgroup.mem_centralizer_iff.1 (hCcen hx) (g : G) (Set.mem_singleton _)
        exact this.symm
      exact Subgroup.centralizer_le_normalizer _ this
    have hCbot : ⁅Y, S⁆ ≠ ⊥ := by
      obtain ⟨u, huY, s, hs, hne⟩ := E.comm_nonzero
      obtain ⟨q, hq, hmk⟩ := mem_YY.1 huY
      intro hbot
      have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
      have hmem : ⁅(q : G), (s : G)⁆ ∈ ⁅Y, S⁆ := Subgroup.commutator_mem_commutator hq hsS
      rw [hbot, Subgroup.mem_bot] at hmem
      apply hne
      have hu' : u = Additive.ofMul (QuotientGroup.mk q : ↥(Qx) ⧸ CQ (Qx) L) := by
        rw [hmk]; rfl
      rw [hu', hrho]
      congr 2
      apply Subtype.ext
      show (s : G) * (q : G) * (s : G)⁻¹ = q
      have : (q : G) * s = s * q := by
        have := commutatorElement_eq_one_iff_mul_comm.1 hmem
        exact this
      rw [mul_inv_eq_iff_eq_mul]; exact this.symm
    have hCtop : ((⁅Y, S⁆ : Subgroup G).subgroupOf (⁅Y, S⁆ : Subgroup G)).Characteristic := by
      rw [Subgroup.subgroupOf_self]; infer_instance
    exact noCharNormal_of_asc81bHyp hA' hYX hCS (commutator_characteristic hYS hYch) hnotnorm _
      le_rfl hCbot hCtop (Subgroup.zpowers_le.2 hgN)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
