module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.MinPar
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockExclusion
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BaumFactors
import CFSG.Quasithin.Background.C126NatDMin
import CFSG.Quasithin.Background.C126NatBlock
import CFSG.Quasithin.EmptyFaithful.R3c21B
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Elementary

theorem false_of_isPGroup_of_perfect {G : Type} [Group G] [Finite G] [Nontrivial G]
    (h : IsPGroup 2 G) (hp : commutator G = ⊤) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent G := h.isNilpotent
  have : Group.IsSolvable G := inferInstance
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne hp

variable {Q : Type} [Group Q]

theorem not_le_centerOf_of_isQuasisimple {L : Subgroup Q} (hL : Open.IsQuasisimple ↥L) :
    ¬ L ≤ centerOf L := by
  intro h
  obtain ⟨-, hsimp⟩ := hL
  have := hsimp
  obtain ⟨q, hq⟩ := exists_ne (1 : ↥L ⧸ Subgroup.center ↥L)
  induction q using QuotientGroup.induction_on with
  | H x =>
    apply hq
    rw [QuotientGroup.eq_one_iff]
    refine Subgroup.mem_center_iff.2 fun g => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (h x.2).2 g g.2)

theorem nontrivial_of_isQuasisimple {L : Subgroup Q} (hL : Open.IsQuasisimple ↥L) : Nontrivial ↥L := by
  by_contra hn
  have : Subsingleton ↥L := not_nontrivial_iff_subsingleton.1 hn
  refine not_le_centerOf_of_isQuasisimple hL fun x hx => ?_
  have : (⟨x, hx⟩ : ↥L) = 1 := Subsingleton.elim _ _
  have hx1 : x = 1 := congrArg Subtype.val this
  rw [hx1]
  exact (centerOf L).one_mem

theorem not_isPGroup_of_isQuasisimple [Finite Q] {L : Subgroup Q} (hL : Open.IsQuasisimple ↥L) :
    ¬ IsPGroup 2 ↥L := by
  intro h
  have := nontrivial_of_isQuasisimple hL
  exact false_of_isPGroup_of_perfect h hL.1

theorem commutator_eq_self_of_isQuasisimple {L : Subgroup Q} (hL : Open.IsQuasisimple ↥L) :
    ⁅L, L⁆ = L := by
  rw [← Subgroup.map_subtype_commutator, hL.1, Subgroup.map_top, Subgroup.range_subtype]

theorem le_centerOf_or_eq_of_isQuasisimple {L N : Subgroup Q} (hL : Open.IsQuasisimple ↥L)
    (hNL : N ≤ L) (hN : L ≤ Subgroup.normalizer (N : Set Q)) : N ≤ centerOf L ∨ N = L := by
  obtain ⟨hperf, hsimp⟩ := hL
  have := hsimp
  have hnorm : (N.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).2 hN
  set Z := Subgroup.center ↥L with hZ
  have hmapn : ((N.subgroupOf L).map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map hnorm _ (QuotientGroup.mk'_surjective Z)
  have := hmapn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((N.subgroupOf L).map (QuotientGroup.mk' Z)) with h | h
  · left
    intro x hx
    have hxL : x ∈ L := hNL hx
    have h1 : QuotientGroup.mk' Z ⟨x, hxL⟩ ∈ (N.subgroupOf L).map (QuotientGroup.mk' Z) :=
      ⟨⟨x, hxL⟩, hx, rfl⟩
    rw [h] at h1
    have h2 : (⟨x, hxL⟩ : ↥L) ∈ Z := (QuotientGroup.eq_one_iff _).1 (Subgroup.mem_bot.1 h1)
    refine ⟨hxL, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 h2 ⟨y, hy⟩)
  · right
    refine le_antisymm hNL fun x hxL => ?_
    set N0 := N.subgroupOf L with hN0
    have hdec : ∀ y : ↥L, ∃ n ∈ N0, ∃ z ∈ Z, y = n * z := by
      intro y
      have hy : QuotientGroup.mk' Z y ∈ (N0.map (QuotientGroup.mk' Z)) := by
        rw [h]; trivial
      obtain ⟨n, hn, hny⟩ := hy
      refine ⟨n, hn, n⁻¹ * y, ?_, by group⟩
      have : QuotientGroup.mk' Z (n⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, hny]; group
      exact (QuotientGroup.eq_one_iff _).1 this
    have hcomm : commutator ↥L ≤ N0 := by
      rw [commutator_eq_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨a, b, rfl⟩
      obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdec a
      obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdec b
      have c1 : ∀ g : ↥L, z₁ * g = g * z₁ := fun g => (Subgroup.mem_center_iff.1 hz₁ g).symm
      have c2 : ∀ g : ↥L, z₂ * g = g * z₂ := fun g => (Subgroup.mem_center_iff.1 hz₂ g).symm
      have e : ⁅n₁ * z₁, n₂ * z₂⁆ = ⁅n₁, n₂⁆ := by
        simp only [commutatorElement_def]
        calc n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹
            = n₁ * (z₁ * n₂) * (z₂ * z₁⁻¹) * n₁⁻¹ * z₂⁻¹ * n₂⁻¹ := by group
          _ = n₁ * (n₂ * z₁) * (z₂ * z₁⁻¹) * n₁⁻¹ * z₂⁻¹ * n₂⁻¹ := by rw [c1 n₂]
          _ = n₁ * n₂ * (z₁ * (z₂ * z₁⁻¹)) * n₁⁻¹ * z₂⁻¹ * n₂⁻¹ := by group
          _ = n₁ * n₂ * (z₂ * (z₁ * z₁⁻¹)) * n₁⁻¹ * z₂⁻¹ * n₂⁻¹ := by rw [← mul_assoc z₁, c1 z₂]; group
          _ = n₁ * n₂ * (z₂ * n₁⁻¹) * z₂⁻¹ * n₂⁻¹ := by group
          _ = n₁ * n₂ * (n₁⁻¹ * z₂) * z₂⁻¹ * n₂⁻¹ := by rw [c2 n₁⁻¹]
          _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by group
      rw [e]
      exact N0.mul_mem (N0.mul_mem (N0.mul_mem hn₁ hn₂) (N0.inv_mem hn₁)) (N0.inv_mem hn₂)
    have htop : (⊤ : Subgroup ↥L) ≤ N0 := hperf ▸ hcomm
    exact (Subgroup.mem_subgroupOf).1 (htop (Subgroup.mem_top (⟨x, hxL⟩ : ↥L)))

end Elementary

section Normalizer

theorem mem_normalizer_map_of_mem {K P : Type*} [Group K] [Group P] (f : K →* P)
    {N : Subgroup K} {k : K} (hk : k ∈ Subgroup.normalizer (N : Set K)) :
    f k ∈ Subgroup.normalizer ((N.map f : Subgroup P) : Set P) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨k * n * k⁻¹, (Subgroup.mem_normalizer_iff.1 hk n).1 hn, by simp⟩
  · rintro ⟨n, hn, e⟩
    refine ⟨k⁻¹ * n * k, ?_, ?_⟩
    · refine (Subgroup.mem_normalizer_iff.1 hk (k⁻¹ * n * k)).2 ?_
      rw [show k * (k⁻¹ * n * k) * k⁻¹ = n by group]
      exact hn
    · rw [map_mul, map_mul, map_inv, e]
      group

theorem mem_normalizer_sup {G : Type*} [Group G] {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hA' : x⁻¹ ∈ Subgroup.normalizer (A : Set G) := (Subgroup.normalizer (A : Set G)).inv_mem hA
  have hB' : x⁻¹ ∈ Subgroup.normalizer (B : Set G) := (Subgroup.normalizer (B : Set G)).inv_mem hB
  refine B6.mem_normalizer_of_conjSub_le ?_ ?_
  · rw [map_sup, B6.conjSub_eq_self hA, B6.conjSub_eq_self hB]
  · rw [map_sup, B6.conjSub_eq_self hA', B6.conjSub_eq_self hB']

theorem conj_mem_centerOf {Q : Type*} [Group Q] {L : Subgroup Q} {y : Q}
    (hy : y ∈ Subgroup.normalizer (L : Set Q)) {z : Q} (hz : z ∈ centerOf L) :
    y * z * y⁻¹ ∈ centerOf L := by
  refine ⟨(Subgroup.mem_normalizer_iff.1 hy z).1 hz.1,
    Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
  have hl' : y⁻¹ * l * y ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (L : Set Q)).inv_mem hy) l).1 hl
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.1 hz.2 _ hl'
  calc l * (y * z * y⁻¹) = y * ((y⁻¹ * l * y) * z) * y⁻¹ := by group
    _ = y * (z * (y⁻¹ * l * y)) * y⁻¹ := by rw [hc]
    _ = y * z * y⁻¹ * l := by group

theorem mem_normalizer_centerOf {Q : Type*} [Group Q] {L : Subgroup Q} {y : Q}
    (hy : y ∈ Subgroup.normalizer (L : Set Q)) :
    y ∈ Subgroup.normalizer ((centerOf L : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => conj_mem_centerOf hy hz, fun hz => ?_⟩
  have := conj_mem_centerOf ((Subgroup.normalizer (L : Set Q)).inv_mem hy) hz
  simpa [mul_assoc] using this

end Normalizer

section Quotient

theorem commutator_mem_of_sup_eq_top {G : Type*} [Group G] {N A B : Subgroup G} [N.Normal]
    (hA : A ⊔ N = ⊤) (hB : B ⊔ N = ⊤) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (x y : G) :
    ⁅x, y⁆ ∈ N := by
  have hdec : ∀ (C : Subgroup G), C ⊔ N = ⊤ → ∀ w : G, ∃ c ∈ C,
      QuotientGroup.mk' N c = QuotientGroup.mk' N w := by
    intro C hC w
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' N)) hC
    have hN : N.map (QuotientGroup.mk' N) = ⊥ :=
      (Subgroup.map_eq_bot_iff _).2 (by rw [QuotientGroup.ker_mk'])
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), hN,
      sup_bot_eq] at h1
    have : QuotientGroup.mk' N w ∈ C.map (QuotientGroup.mk' N) := by rw [h1]; trivial
    obtain ⟨c, hc, e⟩ := this
    exact ⟨c, hc, e⟩
  obtain ⟨a, ha, hax⟩ := hdec A hA x
  obtain ⟨b, hb, hby⟩ := hdec B hB y
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement, ← hax, ← hby,
    ← map_commutatorElement]
  have : ⁅a, b⁆ = 1 := by
    rw [commutatorElement_def, hAB a ha b hb]; group
  rw [this, map_one]

end Quotient

section TwoFactors

variable {K : Type} [Group K] [Finite K]

theorem false_of_two_factors {S M : Subgroup K} (hmin : MinParabolic (⊤ : Subgroup K) S M)
    {Q : Type} [Group Q] [Finite Q] (f : K →* Q) {Lq : Subgroup Q}
    (hL : Open.IsQuasisimple ↥Lq) (hfA : (twoResidual (⊤ : Subgroup K)).map f = Lq)
    (hfN : f.range ≤ Subgroup.normalizer (Lq : Set Q))
    {W : Type} [Group W] [Finite W] (g : K →* W) {I : Finset (Subgroup W)} (hI : 2 ≤ I.card)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (htr : ∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ S.map g, ∀ x, x ∈ L' ↔ t⁻¹ * x * t ∈ L)
    (hperf : ∀ L ∈ I, Group.IsPerfect ↥L) (hnt : ∀ L ∈ I, Nontrivial ↥L)
    (hgA : (twoResidual (⊤ : Subgroup K)).map g = ⨆ L ∈ I, L) : False := by
  classical
  set A : Subgroup K := twoResidual (⊤ : Subgroup K) with hAdef
  have hAn : A.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have nrm : ∀ (N : Subgroup K) [N.Normal] (k : K), k ∈ Subgroup.normalizer (N : Set K) := by
    intro N _ k
    rw [Subgroup.normalizer_eq_top_iff.mpr ‹N.Normal›]
    exact Subgroup.mem_top k
  have hSA : S ⊔ A = ⊤ := sup_twoResidual_eq hmin.isSylow
  have hSM : S ≤ M := hmin.le
  have hMtop : M < ⊤ := ((isUniqueMaxOver_iff.1 hmin.uniqueMax).1).1
  have hSp : IsPGroup 2 ↥S := hmin.isSylow.2.1
  set Pi : Subgroup W := ⨆ L ∈ I, L with hPi
  have hLP : ∀ L ∈ I, L ≤ Pi := fun L hL => le_iSup₂ (f := fun L _ => L) L hL
  have hPig : Pi ≤ g.range := by
    rw [← hgA]; exact Subgroup.map_le_range g A
  have hrange2 : ∀ {P : Type} [Group P] (φ : K →* P) (N : Subgroup K), N ≤ φ.ker →
      N ⊔ S = ⊤ → IsPGroup 2 ↥φ.range := by
    intro P _ φ N hN hNS
    have h1 : φ.range = S.map φ := by
      rw [MonoidHom.range_eq_map, ← hNS, Subgroup.map_sup,
        (Subgroup.map_eq_bot_iff _).2 hN, bot_sup_eq]
    rw [h1]
    exact hSp.map φ
  set NX : Subgroup K := A ⊓ f.ker with hNX
  set NV : Subgroup K := A ⊓ g.ker with hNV
  have hNXn : NX.Normal := inferInstance
  have hNVn : NV.Normal := inferInstance
  have hNXS : NX ⊔ S ≠ ⊤ := by
    intro h
    have h2 := hrange2 f NX inf_le_right h
    exact not_isPGroup_of_isQuasisimple hL (h2.to_le (hfA ▸ Subgroup.map_le_range f A))
  have hNVS : NV ⊔ S ≠ ⊤ := by
    intro h
    have h2 := hrange2 g NV inf_le_right h
    obtain ⟨L₀, hL₀⟩ := Finset.card_pos.1 (by omega : 0 < I.card)
    have hp : IsPGroup 2 ↥L₀ := h2.to_le ((hLP L₀ hL₀).trans hPig)
    have := hnt L₀ hL₀
    exact false_of_isPGroup_of_perfect hp (hperf L₀ hL₀).1
  have hNXM : NX ⊔ S ≤ M :=
    GN.le_of_isUniqueMaxOver hmin.uniqueMax le_sup_right le_top hNXS
  have hNVM : NV ⊔ S ≤ M :=
    GN.le_of_isUniqueMaxOver hmin.uniqueMax le_sup_right le_top hNVS
  have hAM : ¬ A ≤ M := fun h => hMtop.ne (top_le_iff.1 (hSA ▸ sup_le hSM h))
  have hAY : ¬ A ≤ NX ⊔ NV := fun h =>
    hAM (h.trans (sup_le ((le_sup_left : NX ≤ NX ⊔ S).trans hNXM)
      ((le_sup_left : NV ≤ NV ⊔ S).trans hNVM)))
  have hLnorm : ∀ {N : Subgroup K}, (∀ k ∈ A, k ∈ Subgroup.normalizer (N : Set K)) →
      Lq ≤ Subgroup.normalizer ((N.map f : Subgroup Q) : Set Q) := by
    intro N hN l hl
    have : l ∈ A.map f := hfA ▸ hl
    obtain ⟨k, hk, rfl⟩ := this
    exact mem_normalizer_map_of_mem f (hN k hk)
  have hfNV : NV.map f ≤ centerOf Lq := by
    have hle : NV.map f ≤ Lq := hfA ▸ Subgroup.map_mono inf_le_left
    rcases le_centerOf_or_eq_of_isQuasisimple hL hle (hLnorm fun k _ => nrm NV k) with h | h
    · exact h
    · exfalso
      apply hAY
      intro a ha
      have hfa : f a ∈ NV.map f := by
        rw [h]; exact hfA ▸ ⟨a, ha, rfl⟩
      obtain ⟨n, hn, hna⟩ := hfa
      have e : a = (a * n⁻¹) * n := by group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨A.mul_mem ha (A.inv_mem hn.1), ?_⟩)
        (Subgroup.mem_sup_right hn)
      refine MonoidHom.mem_ker.2 ?_
      rw [map_mul, map_inv, hna]
      group
  have hZn : ∀ k : K, f k ∈ Subgroup.normalizer ((centerOf Lq : Subgroup Q) : Set Q) := by
    intro k
    exact mem_normalizer_centerOf (hfN ⟨k, rfl⟩)
  set Y' : Subgroup K := A ⊓ (centerOf Lq).comap f with hY'
  have hY'n : Y'.Normal := by
    refine ⟨fun x hx k => ⟨hAn.conj_mem x hx.1 k, ?_⟩⟩
    show f (k * x * k⁻¹) ∈ centerOf Lq
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hZn k) _).1 hx.2
  have hNXY : NX ≤ Y' := fun x hx => ⟨hx.1, by
    show f x ∈ centerOf Lq
    rw [MonoidHom.mem_ker.1 hx.2]
    exact (centerOf Lq).one_mem⟩
  have hNVY : NV ≤ Y' := fun x hx => ⟨hx.1, hfNV ⟨x, hx, rfl⟩⟩
  have hAY' : ¬ A ≤ Y' := by
    intro h
    refine not_le_centerOf_of_isQuasisimple hL ?_
    have h1 : A.map f ≤ centerOf Lq := by
      rintro _ ⟨a, ha, rfl⟩
      exact (h ha).2
    calc Lq = A.map f := hfA.symm
      _ ≤ centerOf Lq := h1
  have hY''le : Y'.map g ≤ Pi := by
    rw [← hgA]; exact Subgroup.map_mono inf_le_left
  have hY''n : g.range ≤ Subgroup.normalizer ((Y'.map g : Subgroup W) : Set W) := by
    rintro _ ⟨k, rfl⟩
    exact mem_normalizer_map_of_mem g (nrm Y' k)
  have hgA' : ∀ a ∈ A, g a ∈ Pi := fun a ha => by
    rw [← hgA]; exact ⟨a, ha, rfl⟩
  have hY''ne : Y'.map g ≠ Pi := by
    intro h
    apply hAY'
    intro a ha
    have : g a ∈ Y'.map g := by rw [h]; exact hgA' a ha
    obtain ⟨y, hy, hya⟩ := this
    have e : a = (a * y⁻¹) * y := by group
    rw [e]
    refine Y'.mul_mem (hNVY ⟨A.mul_mem ha (A.inv_mem hy.1), MonoidHom.mem_ker.2 ?_⟩) hy
    rw [map_mul, map_inv, hya]
    group
  have hmax : ∀ N : Subgroup W, Y'.map g ≤ N → N ≤ Pi → Pi ≤ Subgroup.normalizer (N : Set W) →
      N = Y'.map g ∨ N = Pi := by
    intro N hYN hNP hPN
    set N' : Subgroup K := A ⊓ N.comap g with hN'
    have hN'A : N' ≤ A := inf_le_left
    have key : ∀ x ∈ N', ∀ k ∈ A, k * x * k⁻¹ ∈ N' := by
      intro x hx k hk
      refine ⟨A.mul_mem (A.mul_mem hk hx.1) (A.inv_mem hk), ?_⟩
      show g (k * x * k⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hPN (hgA' k hk)) _).1 hx.2
    have hnorm : ∀ k ∈ A, k ∈ Subgroup.normalizer (N' : Set K) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => key x hx k hk, fun hx => ?_⟩
      have := key _ hx k⁻¹ (A.inv_mem hk)
      simpa [mul_assoc] using this
    rcases le_centerOf_or_eq_of_isQuasisimple hL
      (hfA ▸ Subgroup.map_mono hN'A : N'.map f ≤ Lq) (hLnorm hnorm) with h | h
    · left
      refine le_antisymm (fun x hx => ?_) hYN
      have hxP : x ∈ A.map g := hgA ▸ hNP hx
      obtain ⟨a, ha, rfl⟩ := hxP
      exact ⟨a, ⟨ha, h ⟨a, ⟨ha, hx⟩, rfl⟩⟩, rfl⟩
    · right
      refine le_antisymm hNP fun x hx => ?_
      have hxP : x ∈ A.map g := hgA ▸ hx
      obtain ⟨a, ha, rfl⟩ := hxP
      have hfa : f a ∈ N'.map f := by rw [h]; exact hfA ▸ ⟨a, ha, rfl⟩
      obtain ⟨n, hn, hna⟩ := hfa
      have h1 : a * n⁻¹ ∈ NX := ⟨A.mul_mem ha (A.inv_mem hn.1), MonoidHom.mem_ker.2 (by
        rw [map_mul, map_inv, hna]; group)⟩
      have h2 : g (a * n⁻¹) ∈ N := hYN ⟨a * n⁻¹, hNXY h1, rfl⟩
      have h3 : g n ∈ N := hn.2
      have e : g a = g (a * n⁻¹) * g n := by rw [← map_mul]; group
      rw [e]
      exact N.mul_mem h2 h3
  have hfactor : ∀ L ∈ I, L ≤ Y'.map g ∨ L ⊔ Y'.map g = Pi := by
    intro L hL'
    have hn1 : Pi ≤ Subgroup.normalizer (L : Set W) := iSup_le_normalizer_of_commuting hcomm hL'
    have hn2 : Pi ≤ Subgroup.normalizer ((Y'.map g : Subgroup W) : Set W) :=
      fun x hx => hY''n (hPig hx)
    have hn : Pi ≤ Subgroup.normalizer ((L ⊔ Y'.map g : Subgroup W) : Set W) :=
      fun x hx => mem_normalizer_sup (hn1 hx) (hn2 hx)
    rcases hmax (L ⊔ Y'.map g) le_sup_right (sup_le (hLP L hL') hY''le) hn with h | h
    · exact Or.inl (le_sup_left.trans h.le)
    · exact Or.inr h
  have hnotTwo : ∀ L₁ ∈ I, ∀ L₂ ∈ I, L₁ ≠ L₂ → L₁ ⊔ Y'.map g = Pi → L₂ ⊔ Y'.map g = Pi →
      False := by
    intro L₁ h₁ L₂ h₂ hne e₁ e₂
    have hnormPi : ((Y'.map g).subgroupOf Pi).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hY''le).2 fun x hx => hY''n (hPig hx)
    have hA1 : L₁.subgroupOf Pi ⊔ (Y'.map g).subgroupOf Pi = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (hLP L₁ h₁) hY''le, e₁,
        Subgroup.subgroupOf_self]
    have hB1 : L₂.subgroupOf Pi ⊔ (Y'.map g).subgroupOf Pi = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (hLP L₂ h₂) hY''le, e₂,
        Subgroup.subgroupOf_self]
    have hAB : ∀ a ∈ L₁.subgroupOf Pi, ∀ b ∈ L₂.subgroupOf Pi, a * b = b * a :=
      fun a ha b hb => Subtype.ext (hcomm L₁ h₁ L₂ h₂ hne a ha b hb)
    have hcommA : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ Y' := by
      intro a ha b hb
      have h1 : ⁅g a, g b⁆ ∈ Y'.map g :=
        commutator_mem_of_sup_eq_top hA1 hB1 hAB ⟨g a, hgA' a ha⟩ ⟨g b, hgA' b hb⟩
      obtain ⟨y, hy, hyc⟩ := h1
      have hab : ⁅a, b⁆ ∈ A :=
        A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
      have e : ⁅a, b⁆ = (⁅a, b⁆ * y⁻¹) * y := by group
      rw [e]
      refine Y'.mul_mem (hNVY ⟨A.mul_mem hab (A.inv_mem hy.1), MonoidHom.mem_ker.2 ?_⟩) hy
      rw [map_mul, map_inv, hyc, map_commutatorElement]
      group
    have hc : commutator ↥Lq ≤ (centerOf Lq).subgroupOf Lq := by
      rw [commutator_eq_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, y, rfl⟩
      have hxa : (x : Q) ∈ A.map f := hfA ▸ x.2
      have hya : (y : Q) ∈ A.map f := hfA ▸ y.2
      obtain ⟨a, ha, hax⟩ := hxa
      obtain ⟨b, hb, hby⟩ := hya
      show ((⁅x, y⁆ : ↥Lq) : Q) ∈ centerOf Lq
      have e : ((⁅x, y⁆ : ↥Lq) : Q) = f ⁅a, b⁆ := by
        rw [map_commutatorElement, hax, hby]; rfl
      rw [e]
      exact (hcommA a ha b hb).2
    refine not_le_centerOf_of_isQuasisimple hL fun z hz => ?_
    have hz' : (⟨z, hz⟩ : ↥Lq) ∈ commutator ↥Lq := by
      rw [hL.1]; exact Subgroup.mem_top _
    exact hc hz'
  have hex : ∃ L₀ ∈ I, L₀ ≤ Y'.map g := by
    by_contra hcon
    have hcon' : ∀ L ∈ I, ¬ L ≤ Y'.map g := fun L hL h => hcon ⟨L, hL, h⟩
    obtain ⟨L₁, h₁, L₂, h₂, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < I.card)
    exact hnotTwo L₁ h₁ L₂ h₂ hne ((hfactor L₁ h₁).resolve_left (hcon' L₁ h₁))
      ((hfactor L₂ h₂).resolve_left (hcon' L₂ h₂))
  obtain ⟨L₀, h₀, hL₀Y⟩ := hex
  have hall : Pi ≤ Y'.map g := by
    refine iSup₂_le fun L' hL' => ?_
    obtain ⟨t, ht, hconj⟩ := htr L₀ h₀ L' hL'
    have htn := hY''n (Subgroup.map_le_range g S ht)
    intro x hx
    have h1 : t⁻¹ * x * t ∈ Y'.map g := hL₀Y ((hconj x).1 hx)
    have h2 := (Subgroup.mem_normalizer_iff.1 htn _).1 h1
    simpa [mul_assoc] using h2
  exact hY''ne (le_antisymm hY''le hall)

end TwoFactors

section Glue

open CFSG.Quasithin.B2F CFSG.Quasithin.E2 CFSG.AGLEmbeddingD2.GN

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem autI_eq_map {V : Subgroup G} (hV : IsElemAbelian 2 V) {K : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) {P : Subgroup G} (hPK : P ≤ K) :
    autI hV P = (P.subgroupOf K).map ((convI hV).comp (Subgroup.inclusion hKN)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨s, hsP, rfl⟩ := (mem_autI hV).1 ht
    exact ⟨⟨s.1, hPK hsP⟩, hsP, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨Subgroup.inclusion hKN k, hk, rfl⟩

theorem card_lt_two_of_quasisimple_image {K S M : Subgroup G} (hmin : MinParabolic K S M)
    (hF : CharTwo K) {Q : Type} [Group Q] [Finite Q] (f : ↥K →* Q) {Lq : Subgroup Q}
    (hL : Open.IsQuasisimple ↥Lq) (hfA : (twoResidual (⊤ : Subgroup ↥K)).map f = Lq)
    (hfN : f.range ≤ Subgroup.normalizer (Lq : Set Q))
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (hVZ : V = VZ S K)
    {I : Finset (Subgroup (MulAut (IntMod V hV)))} (hFam : E23FamGen K S V hV I)
    (hnat : ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual K))) n)
    (hJ : twoResidual K ≤ thompsonJ K) : I.card < 2 := by
  by_contra hcon
  have hI : 2 ≤ I.card := not_lt.1 hcon
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := by
    subst hVZ
    exact (conjClosure_isTwoReducedIn_of_charTwo hmin.isSylow hF (le_refl _)).2.2.2.1
  have : Finite (MulAut (IntMod V hV)) := MulEquiv.finite_left
  set g : ↥K →* MulAut (IntMod V hV) := (convI hV).comp (Subgroup.inclusion hKN) with hg
  have hSK : S ≤ K := hmin.isSylow.1
  have hperf : ∀ L ∈ I, Group.IsPerfect ↥L := fun L hL' => by
    obtain ⟨n, hn2, hn⟩ := hnat L hL'
    exact R3c21.isPerfect_of_isL2Natural hn hn2
  have hnt : ∀ L ∈ I, Nontrivial ↥L := fun L hL' => by
    obtain ⟨n, hn2, hn⟩ := hnat L hL'
    have h6 := C126.Nat.six_le_card_of_type (Or.inl ⟨n, hn⟩)
    have : Finite ↥L := inferInstance
    exact Finite.one_lt_card_iff_nontrivial.1 (by omega)
  have hA : twoResidual (⊤ : Subgroup ↥K) = (twoResidual K).subgroupOf K :=
    B6.twoResidual_top_eq_subgroupOf K
  have hgrange : g.range = autI hV K := by
    rw [autI_eq_map hV hKN le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  have hAmap : (twoResidual (⊤ : Subgroup ↥K)).map g = autI hV (twoResidual K) := by
    rw [hA, ← autI_eq_map hV hKN (twoResidual_le K)]
  have hPiperf : ⁅(⨆ L ∈ I, L), (⨆ L ∈ I, L)⁆ = ⨆ L ∈ I, L := by
    refine le_antisymm (Subgroup.commutator_le.2 fun x hx y hy =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx))
        (Subgroup.inv_mem _ hy)) ?_
    refine iSup₂_le fun L hL' => ?_
    have hLL : ⁅L, L⁆ = L := by
      rw [← Subgroup.map_subtype_commutator, (hperf L hL').1, Subgroup.map_top,
        Subgroup.range_subtype]
    calc L = ⁅L, L⁆ := hLL.symm
      _ ≤ ⁅(⨆ L ∈ I, L), (⨆ L ∈ I, L)⁆ :=
        Subgroup.commutator_mono (le_iSup₂ (f := fun L _ => L) L hL')
          (le_iSup₂ (f := fun L _ => L) L hL')
  have hgA : (twoResidual (⊤ : Subgroup ↥K)).map g = ⨆ L ∈ I, L := by
    rw [hAmap]
    apply le_antisymm
    · rw [← hFam.2.1]
      exact autI_mono hV hJ
    · have h1 : (⨆ L ∈ I, L) ≤ g.range := by
        rw [hgrange, ← hFam.2.1]
        exact autI_mono hV (thompsonJ_le_self K)
      have h2 := C126.Nat.le_twoResidual_of_perfect h1 hPiperf
      rw [← hAmap, E1.map_twoResidual g ⊤, ← MonoidHom.range_eq_map]
      exact h2
  have htr : ∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ (S.subgroupOf K).map g,
      ∀ x, x ∈ L' ↔ t⁻¹ * x * t ∈ L := by
    intro L hL' L'' hL''
    obtain ⟨t, ht, hc⟩ := hFam.2.2.2.1 L hL' L'' hL''
    rw [autI_eq_map hV hKN hSK] at ht
    exact ⟨t, ht, fun x => by rw [← hc, B1.mem_conjAut]⟩
  exact false_of_two_factors hmin.subgroupOf f hL hfA hfN g hI hFam.2.2.1 htr hperf hnt hgA

end Glue

section ImageShape

open CFSG.Quasithin.B2F CFSG.Quasithin.E2 CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem map_twoResidual_eq_of_range {K : Type} [Group K] [Finite K] {Q : Type} [Group Q] [Finite Q]
    (f : K →* Q) {Lq Rq : Subgroup Q} (hL : Open.IsQuasisimple ↥Lq) (hR : IsPGroup 2 ↥Rq)
    (hRN : Rq ≤ Subgroup.normalizer (Lq : Set Q)) (hfK : f.range = Lq ⊔ Rq) :
    (twoResidual (⊤ : Subgroup K)).map f = Lq := by
  have h1 : (twoResidual (⊤ : Subgroup K)).map f = twoResidual f.range := by
    rw [E1.map_twoResidual f ⊤, ← MonoidHom.range_eq_map]
  rw [h1, hfK]
  exact le_antisymm (twoResidual_sup_le_of_pGroup hR hRN)
    (C126.Nat.le_twoResidual_of_perfect le_sup_left (commutator_eq_self_of_isQuasisimple hL))

variable {G : Type} [Group G] [Finite G]

theorem card_lt_two_of_sup_image {K S M : Subgroup G} (hmin : MinParabolic K S M)
    (hF : CharTwo K) {Q : Type} [Group Q] [Finite Q] (π : G →* Q) {Lq Rq : Subgroup Q}
    (hL : Open.IsQuasisimple ↥Lq) (hR : IsPGroup 2 ↥Rq)
    (hRN : Rq ≤ Subgroup.normalizer (Lq : Set Q)) (hπK : K.map π = Lq ⊔ Rq)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (hVZ : V = VZ S K)
    {I : Finset (Subgroup (MulAut (IntMod V hV)))} (hFam : E23FamGen K S V hV I)
    (hnat : ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual K))) n)
    (hJ : twoResidual K ≤ thompsonJ K) : I.card < 2 := by
  have hfK : (π.comp K.subtype).range = Lq ⊔ Rq := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hπK
  exact card_lt_two_of_quasisimple_image hmin hF (π.comp K.subtype) hL
    (map_twoResidual_eq_of_range _ hL hR hRN hfK)
    (hfK ▸ sup_le Subgroup.le_normalizer hRN) hV hVZ hFam hnat hJ

theorem pElementSubgroup_eq_of_isMinOverBorel_self {Y : Type} [Group Y] {L S₀ : Subgroup Y}
    (hL : Open.IsQuasisimple ↥L) (hS : S₀ ≤ L) (hS2 : IsPGroup 2 ↥S₀)
    (hP : IsMinOverBorel L S₀ L) : pElementSubgroup 2 L = L := by
  have hWL : pElementSubgroup 2 L ≤ L := pElementSubgroup_le L
  have hn : L ≤ Subgroup.normalizer ((pElementSubgroup 2 L : Subgroup Y) : Set Y) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_pElementSubgroup 2 L)
  rcases le_centerOf_or_eq_of_isQuasisimple hL hWL hn with h | h
  · exfalso
    have hSW : S₀ ≤ pElementSubgroup 2 L := fun x hx => by
      refine Subgroup.subset_closure ⟨hS hx, ?_⟩
      have := (IsPGroup.iff_orderOf.1 hS2) ⟨x, hx⟩
      simpa using this
    have hc : S₀ ≤ centerOf L := hSW.trans h
    have hLN : L ≤ Subgroup.normalizer (S₀ : Set Y) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hcomm : ∀ s ∈ S₀, l * s * l⁻¹ = s := fun s hs => by
        have := Subgroup.mem_centralizer_iff.1 (hc hs).2 l hl
        rw [this]; group
      constructor
      · intro hx
        rw [hcomm x hx]; exact hx
      · intro hx
        have hcl : l * (l * x * l⁻¹) = (l * x * l⁻¹) * l :=
          Subgroup.mem_centralizer_iff.1 (hc hx).2 l hl
        have h3 : x = l * x * l⁻¹ := by
          calc x = l⁻¹ * (l * x * l⁻¹) * l := by group
            _ = l⁻¹ * ((l * x * l⁻¹) * l) := by rw [mul_assoc]
            _ = l⁻¹ * (l * (l * x * l⁻¹)) := by rw [hcl]
            _ = l * x * l⁻¹ := by group
        rwa [h3]
    exact absurd (inf_eq_left.2 hLN) hP.2.1.ne
  · exact h

end ImageShape

end CFSG.AGLEmbeddingD2.Tits.GN516
