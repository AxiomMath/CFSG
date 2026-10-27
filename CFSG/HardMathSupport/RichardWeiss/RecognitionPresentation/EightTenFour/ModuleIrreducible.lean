module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.ActionTrivial
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.ShortBlockCommutator
public import CFSG.HardMathSupport.Cooperstein.Proving.BarTransport

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open Subgroup CFSG.AGLEmbedding
open CFSG.HardMathSupport.Cooperstein.Proving (barMHomSub barMHomSub_surjective ker_barMHomSub)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def conjActHom (L A : Subgroup G) (h : L ≤ Subgroup.normalizer (A : Set G)) :
    ↥L →* MulAut ↥A :=
  A.normalizerMonoidHom.comp (Subgroup.inclusion h)

omit [Finite G] in
theorem coe_conjActHom (L A : Subgroup G) (h : L ≤ Subgroup.normalizer (A : Set G)) (l : ↥L)
    (a : ↥A) : ((conjActHom L A h l a : ↥A) : G) = (l : G) * a * (l : G)⁻¹ := rfl

omit [Finite G] in
theorem map_conjActHom_subgroupOf (L W N : Subgroup G) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) (l : ↥L) :
    (N.subgroupOf W).map (conjActHom L W hLW l).toMonoidHom = N.subgroupOf W := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hn' : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
    show (l : G) * (n : G) * (l : G)⁻¹ ∈ N
    exact (Subgroup.mem_normalizer_iff.mp (hLN l.2) n).mp hn'
  · intro hx
    have hx' : (x : G) ∈ N := Subgroup.mem_subgroupOf.mp hx
    refine ⟨(conjActHom L W hLW l)⁻¹ x, ?_, by simp⟩
    show (((conjActHom L W hLW l)⁻¹ x : ↥W) : G) ∈ N
    have hinv : (((conjActHom L W hLW l)⁻¹ x : ↥W) : G) = (l : G)⁻¹ * x * (l : G) := by
      have h1 : conjActHom L W hLW l ((conjActHom L W hLW l)⁻¹ x) = x := by simp
      have h2 := congrArg Subtype.val h1
      rw [coe_conjActHom] at h2
      calc (((conjActHom L W hLW l)⁻¹ x : ↥W) : G)
          = (l : G)⁻¹ * ((l : G) * (((conjActHom L W hLW l)⁻¹ x : ↥W) : G) * (l : G)⁻¹) *
            (l : G) := by group
        _ = (l : G)⁻¹ * x * (l : G) := by rw [h2]
    rw [hinv]
    have := (Subgroup.mem_normalizer_iff.mp (hLN (L.inv_mem l.2)) (x : G)).mp hx'
    simpa using this

omit [Finite G] in
@[expose] noncomputable def quotActFun (L W N : Subgroup G)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hLN : L ≤ Subgroup.normalizer (N : Set G))
    [(N.subgroupOf W).Normal] (l : ↥L) : MulAut (↥W ⧸ N.subgroupOf W) :=
  QuotientGroup.congr (N.subgroupOf W) (N.subgroupOf W) (conjActHom L W hLW l)
    (map_conjActHom_subgroupOf L W N hLW hLN l)

omit [Finite G] in
theorem quotActFun_mk (L W N : Subgroup G) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) [(N.subgroupOf W).Normal] (l : ↥L) (w : ↥W) :
    quotActFun L W N hLW hLN l (QuotientGroup.mk w) =
      QuotientGroup.mk (conjActHom L W hLW l w) :=
  QuotientGroup.congr_mk _ _ _ _ _

@[expose] noncomputable def quotAct (L W N : Subgroup G) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) [(N.subgroupOf W).Normal] :
    ↥L →* MulAut (↥W ⧸ N.subgroupOf W) where
  toFun := quotActFun L W N hLW hLN
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [quotActFun_mk, map_one]
      rfl
  map_mul' l₁ l₂ := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [MulAut.mul_apply, quotActFun_mk, quotActFun_mk, quotActFun_mk, map_mul]
      rfl

omit [Finite G] in
theorem quotAct_mk (L W N : Subgroup G) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) [(N.subgroupOf W).Normal] (l : ↥L) (w : ↥W) :
    quotAct L W N hLW hLN l (QuotientGroup.mk w) =
      QuotientGroup.mk (conjActHom L W hLW l w) :=
  quotActFun_mk L W N hLW hLN l w

omit [Finite G] in
theorem isPGroup_ker_barMHomSub {M L : Subgroup G} (hLM : L ≤ M) :
    IsPGroup 2 (barMHomSub hLM).ker := by
  rw [ker_barMHomSub hLM]
  intro x
  have hQ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
  have hx : ((x : ↥L) : G) ∈ CFSG.Open.pCoreOf 2 M := x.2
  obtain ⟨k, hk⟩ := hQ ⟨((x : ↥L) : G), hx⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have := congrArg Subtype.val hk
  simpa using this

theorem eq_of_invariant {M L W N : Subgroup G} (hLs : IsTwoPrimeComponent M L)
    (hidx : 2520 ≤ (Subgroup.center ↥(barM M L)).index)
    (hWL : L ≤ Subgroup.normalizer (W : Set G)) (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hW2 : ∀ a ∈ W, a ^ 2 = 1) (hWcard : Nat.card ↥W ≤ 16) (hWW : ⁅W, L⁆ = W)
    (hNW : N ≤ W) (hLN : L ≤ Subgroup.normalizer (N : Set G)) (hN : N ≠ ⊥) : N = W := by
  have hNn : (N.subgroupOf W).Normal := ⟨fun n hn g => by
    have h1 : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
      rw [hWc g g.2 n n.2]; group
    have : g * n * g⁻¹ = n := Subtype.ext h1
    rw [this]; exact hn⟩
  set N' := N.subgroupOf W with hN'
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLs.perfect
  have hq := hLs.component.2.2
  have hcN : 2 ≤ Nat.card ↥N' := by
    have h1 : Nat.card ↥N' = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv
    rw [h1]
    by_contra h
    have : Nat.card ↥N = 1 := by
      have := Nat.card_pos (α := ↥N)
      omega
    exact hN (Subgroup.eq_bot_of_card_eq _ this)
  have hidxQ : Nat.card (↥W ⧸ N') ≤ 8 := by
    have h1 : Nat.card ↥N' * N'.index = Nat.card ↥W := Subgroup.card_mul_index N'
    have h2 : N'.index * 2 ≤ N'.index * Nat.card ↥N' := Nat.mul_le_mul_left _ hcN
    have h3 : N'.index * Nat.card ↥N' = Nat.card ↥W := by rw [mul_comm]; exact h1
    have h4 : N'.index * 2 ≤ 16 := h2.trans (h3.le.trans hWcard)
    have h5 : Nat.card (↥W ⧸ N') = N'.index := rfl
    omega
  have hcomm : ∀ a b : ↥W ⧸ N', a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (hWc a a.2 b b.2)
  have hpow : ∀ a : ↥W ⧸ N', a ^ 2 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H a =>
      rw [← QuotientGroup.mk_pow]
      have : a ^ 2 = 1 := Subtype.ext (hW2 a a.2)
      rw [this]; rfl
  have hA168 : Nat.card (MulAut (↥W ⧸ N')) ≤ 168 := card_mulAut_le_168 hcomm hpow hidxQ
  have htriv := eq_one_of_card_mulAut_lt hperf (barMHomSub hLs.le) (barMHomSub_surjective hLs.le)
    (isPGroup_ker_barMHomSub hLs.le) hq hidx (quotAct L W N hWL hLN)
    (lt_of_le_of_lt hA168 (by norm_num))
  have hcommN : ⁅W, L⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro w hw l hl
    have h1 : quotAct L W N hWL hLN ⟨l, hl⟩ (QuotientGroup.mk (⟨w, hw⟩ : ↥W)) =
        QuotientGroup.mk (⟨w, hw⟩ : ↥W) := by
      rw [htriv]; rfl
    rw [quotAct_mk] at h1
    have h2 : (QuotientGroup.mk (conjActHom L W hWL ⟨l, hl⟩ ⟨w, hw⟩) : ↥W ⧸ N') =
        QuotientGroup.mk ⟨w, hw⟩ := h1
    rw [QuotientGroup.eq] at h2
    have h3 : ((((conjActHom L W hWL ⟨l, hl⟩ ⟨w, hw⟩)⁻¹ * ⟨w, hw⟩ : ↥W)) : G) ∈ N := h2
    have e : ((((conjActHom L W hWL ⟨l, hl⟩ ⟨w, hw⟩)⁻¹ * ⟨w, hw⟩ : ↥W)) : G) =
        (l * w * l⁻¹)⁻¹ * w := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjActHom]
    rw [e] at h3
    have hxW : l * w * l⁻¹ ∈ W := by
      have := (conjActHom L W hWL ⟨l, hl⟩ ⟨w, hw⟩).2
      rwa [show (((conjActHom L W hWL ⟨l, hl⟩ ⟨w, hw⟩ : ↥W)) : G) = l * w * l⁻¹ from
        coe_conjActHom L W hWL ⟨l, hl⟩ ⟨w, hw⟩] at this
    have hc := hWc w hw _ (W.inv_mem hxW)
    have : ⁅w, l⁆ = w * (l * w * l⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [this, hc]
    exact h3
  rw [hWW] at hcommN
  exact le_antisymm hNW hcommN

omit [Finite G] in
theorem elemAbelian_comm' {E : Subgroup G} (h : CFSG.Open.IsElemAbelian 2 E) :
    ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.1.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)

theorem hasIrr_of_card_sixteen {M L V : Subgroup G} (hLs : IsTwoPrimeComponent M L)
    (hidx : 2520 ≤ (Subgroup.center ↥(barM M L)).index) (hV : CFSG.Open.IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : V ≤ Subgroup.normalizer (L : Set G))
    (h16 : Nat.card ↥⁅V, L⁆ = 2 ^ 4) :
    ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧ HasIrreducibleCommutatorQuotient L V := by
  set W : Subgroup G := ⁅V, L⁆ with hWdef
  have hWV : W ≤ V := by
    rw [hWdef, Subgroup.commutator_le]
    intro v hv l hl
    have h1 : l * v⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv)
    have : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
    rw [this]; exact V.mul_mem hv h1
  have hWL : L ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_commutator' hLV Subgroup.le_normalizer
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    elemAbelian_comm' hV a (hWV ha) b (hWV hb)
  have hW2 : ∀ a ∈ W, a ^ 2 = 1 := fun a ha => hV.2 a (hWV ha)
  have hWW : ⁅W, L⁆ = W := commutator_commutator_eq_of_perfect' hLs.perfect hLV hVL
  have hWne : W ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥W = 1 := by rw [h]; exact Subgroup.card_bot
    rw [h16] at h1
    norm_num at h1
  have hcard : Nat.card ↥W ≤ 16 := by rw [h16]; norm_num
  have hirr : ∀ N : Subgroup G, N ≤ W → L ≤ Subgroup.normalizer (N : Set G) → N = ⊥ ∨ N = W := by
    intro N hNW hLN
    by_cases hN : N = ⊥
    · exact Or.inl hN
    · exact Or.inr (eq_of_invariant hLs hidx hWL hWc hW2 hcard hWW hNW hLN hN)
  have hCbot : W ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rcases hirr (W ⊓ Subgroup.centralizer (L : Set G)) inf_le_left (by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hcen : ∀ x ∈ W ⊓ Subgroup.centralizer (L : Set G), g * x * g⁻¹ = x := by
        intro x hx
        have := Subgroup.mem_centralizer_iff.mp hx.2 g hg
        rw [this]; group
      constructor
      · intro hh; rw [hcen h hh]; exact hh
      · intro hh
        have := hcen _ hh
        have e : g * (g * h * g⁻¹) * g⁻¹ = h → True := fun _ => trivial
        have h2 : (g⁻¹ : G) * (g * h * g⁻¹) * (g⁻¹)⁻¹ = g * h * g⁻¹ := by
          have hg' : g⁻¹ ∈ L := L.inv_mem hg
          have := Subgroup.mem_centralizer_iff.mp hh.2 g⁻¹ hg'
          rw [this]; group
        have h3 : (g⁻¹ : G) * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h := by group
        rw [h3] at h2
        rw [h2]; exact hh) with h | h
    · exact h
    · exfalso
      have hWC : W ≤ Subgroup.centralizer (L : Set G) := by
        rw [← h]; exact inf_le_right
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hWC
      rw [hWW] at this
      exact hWne this
  refine ⟨hCbot, ?_, ?_⟩
  · rw [hCbot]; exact bot_lt_iff_ne_bot.mpr hWne
  · intro W' hW'1 hW'2 hW'L
    rw [hCbot] at hW'1 ⊢
    rcases hirr W' hW'2 hW'L with h | h
    · exact Or.inl h
    · exact Or.inr h

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
