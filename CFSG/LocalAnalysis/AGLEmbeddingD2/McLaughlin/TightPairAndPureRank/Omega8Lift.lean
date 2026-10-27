module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRBridge
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem isLinTwoIndex_seven_one {d : TauCeti.ValidLieTypeIndex}
    (h : ∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) : IsLinTwoIndex 7 1 d := by
  obtain ⟨q, hq, hd⟩ := h
  have hp : q.p ∣ 7 := by
    rw [← hq, TauCeti.PrimePower.card_def]
    exact dvd_pow_self _ (Nat.pos_iff_ne_zero.mp q.exponent_pos)
  have hp7 : q.p = 7 := (Nat.prime_dvd_prime_iff_eq q.prime_p (by norm_num)).mp hp
  have he : q.exponent = 1 := by
    have h7 : 7 ^ q.exponent = 7 ^ 1 := by
      have := hq
      rw [TauCeti.PrimePower.card_def, hp7] at this
      simpa using this
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 7) h7
  exact ⟨q, hd, hp7, he⟩

theorem isLThreeTwo_simple {X : Type} [Group X] (h : IsLThreeTwo X) : IsSimpleGroup X := by
  obtain ⟨d, hd, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨e2⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (isLinTwoIndex_seven_one hd)
  have : IsSimpleGroup (PSL2GF 7 1) := isSimpleGroup_psl2GF (by norm_num)
  exact MulEquiv.isSimpleGroup (e.trans e2)

theorem isLThreeTwo_card_eq {X : Type} [Group X] (h : IsLThreeTwo X) : Nat.card X = 168 := by
  obtain ⟨d, hd, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h1 := card_catGroup_linTwo (p := 7) (n := 1) (by norm_num) one_ne_zero
    (isLinTwoIndex_seven_one hd)
  rw [Nat.card_congr e.toEquiv]
  simpa using h1

theorem isLThreeTwo_three_dvd_card {X : Type} [Group X] (h : IsLThreeTwo X) : 3 ∣ Nat.card X := by
  rw [isLThreeTwo_card_eq h]
  norm_num

theorem isLThreeTwo_quot_pCore_of_surj {Y₂ S : Type} [Group Y₂] [Finite Y₂] [Group S]
    (hS : IsLThreeTwo S) (ψ : Y₂ →* S) (hψ : Function.Surjective ψ)
    (hk : ∀ y ∈ ψ.ker, ∃ k : ℕ, y ^ 2 ^ k = 1) :
    IsLThreeTwo (Y₂ ⧸ CFSG.pCore 2 Y₂) := by
  have : Finite S := Finite.of_surjective ψ hψ
  have hsimple := isLThreeTwo_simple hS
  have h3 := isLThreeTwo_three_dvd_card hS
  have h1 : ψ.ker ≤ CFSG.pCore 2 Y₂ := by
    unfold CFSG.pCore
    refine le_sSup ⟨ψ.normal_ker, ?_⟩
    intro g
    obtain ⟨k, hk'⟩ := hk g g.2
    exact ⟨k, Subtype.ext (by simpa using hk')⟩
  have h2 : CFSG.pCore 2 Y₂ ≤ ψ.ker := by
    set P := (CFSG.pCore 2 Y₂).map ψ with hP
    have hPn : P.Normal := Subgroup.Normal.map CFSG.pCore_normal ψ hψ
    haveI := hPn
    have hP2 : IsPGroup 2 P := IsPGroup.map CFSG.pCore_isPGroup ψ
    rcases hsimple.eq_bot_or_eq_top_of_normal P with h | h
    · intro y hy
      rw [MonoidHom.mem_ker]
      have : ψ y ∈ P := ⟨y, hy, rfl⟩
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    · exfalso
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 3 h3
      have hsP : s ∈ P := by rw [h]; exact Subgroup.mem_top s
      obtain ⟨k, hk'⟩ := hP2 ⟨s, hsP⟩
      have : orderOf s ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk')
      rw [hs] at this
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
      omega
  have heq : ψ.ker = CFSG.pCore 2 Y₂ := le_antisymm h1 h2
  exact IsLThreeTwo.of_mulEquiv
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq heq)) hS


theorem lift_isLThreeTwo {Xg Xs : Type} [Group Xg] [Finite Xg] [Group Xs]
    (f : Xg →* Xs) (hC : ¬ 3 ∣ Nat.card f.ker) (Jg N : Subgroup Xg) (hJ : Jg.Normal)
    (hJ2 : ∀ x ∈ Jg, x ∈ f.ker → ∃ k : ℕ, x ^ 2 ^ k = 1)
    (Y : Subgroup Xs) (hYN : Y ≤ N.map f) (hYJ : Y ≤ Jg.map f)
    (hYn : (Y.subgroupOf (N.map f ⊓ Jg.map f)).Normal)
    (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    ((N ⊓ Jg ⊓ Y.comap f).subgroupOf (N ⊓ Jg)).Normal ∧
      IsLThreeTwo (↥(N ⊓ Jg ⊓ Y.comap f) ⧸ CFSG.pCore 2 ↥(N ⊓ Jg ⊓ Y.comap f)) := by
  set D₀ : Subgroup Xg := N ⊓ Y.comap f with hD₀
  set Y₂ : Subgroup Xg := N ⊓ Jg ⊓ Y.comap f with hY₂
  have hY₂D : Y₂ ≤ D₀ := fun x hx => ⟨hx.1.1, hx.2⟩
  have hY₂J : Y₂ ≤ Jg := fun x hx => hx.1.2
  have hnorm : (Y₂.subgroupOf (N ⊓ Jg)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨⟨hxN, hxJ⟩, hxY⟩ := hx
    have hxY' : f x ∈ Y := hxY
    have hgA : f (g : Xg) ∈ N.map f ⊓ Jg.map f :=
      ⟨⟨g, g.2.1, rfl⟩, ⟨g, g.2.2, rfl⟩⟩
    have hxA : f x ∈ N.map f ⊓ Jg.map f := ⟨hYN hxY', hYJ hxY'⟩
    have h1 := hYn.conj_mem ⟨f x, hxA⟩ (Subgroup.mem_subgroupOf.mpr hxY') ⟨f g, hgA⟩
    have h2 : f ((g : Xg) * x * (g : Xg)⁻¹) ∈ Y := by
      have := Subgroup.mem_subgroupOf.mp h1
      simpa [map_mul, map_inv] using this
    refine ⟨⟨?_, ?_⟩, h2⟩
    · exact N.mul_mem (N.mul_mem g.2.1 hxN) (N.inv_mem g.2.1)
    · exact Jg.mul_mem (Jg.mul_mem g.2.2 hxJ) (Jg.inv_mem g.2.2)
  refine ⟨hnorm, ?_⟩
  let g₀ : ↥D₀ →* ↥Y := (f.comp D₀.subtype).codRestrict Y (fun d => d.2.2)
  have hg₀ : Function.Surjective g₀ := by
    intro y
    obtain ⟨n, hn, hny⟩ := hYN y.2
    exact ⟨⟨n, hn, by show f n ∈ Y; rw [hny]; exact y.2⟩, Subtype.ext hny⟩
  set Y₂' : Subgroup ↥D₀ := Y₂.subgroupOf D₀ with hY₂'
  have hY₂'n : Y₂'.Normal := ⟨fun x hx g => by
    rw [hY₂', Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨⟨hxN, hxJ⟩, hxY⟩ := hx
    have hgN : (g : Xg) ∈ N := g.2.1
    have hgY : f (g : Xg) ∈ Y := g.2.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact N.mul_mem (N.mul_mem hgN hxN) (N.inv_mem hgN)
    · exact hJ.conj_mem _ hxJ _
    · have hxY' : f (x : Xg) ∈ Y := hxY
      show f ((g : Xg) * (x : Xg) * (g : Xg)⁻¹) ∈ Y
      rw [map_mul, map_mul, map_inv]
      exact Y.mul_mem (Y.mul_mem hgY hxY') (Y.inv_mem hgY)⟩
  let θ : ↥D₀ →* Xg ⧸ Jg := (QuotientGroup.mk' Jg).comp D₀.subtype
  have hθker : θ.ker = Y₂' := by
    ext d
    rw [MonoidHom.mem_ker, hY₂', Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk' Jg) (d : Xg) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨⟨d.2.1, h⟩, d.2.2⟩
    · intro h
      exact h.1.2
  have hθrange : θ.range ≤ f.ker.map (QuotientGroup.mk' Jg) := by
    rintro _ ⟨d, rfl⟩
    obtain ⟨j, hj, hjd⟩ := hYJ d.2.2
    refine ⟨(j : Xg)⁻¹ * (d : Xg), ?_, ?_⟩
    · exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hjd, inv_mul_cancel])
    · show (QuotientGroup.mk' Jg) ((j : Xg)⁻¹ * (d : Xg)) = (QuotientGroup.mk' Jg) (d : Xg)
      have hj1 : (QuotientGroup.mk' Jg) j = 1 := (QuotientGroup.eq_one_iff j).mpr hj
      rw [map_mul, map_inv, hj1, inv_one, one_mul]
  have hidx : ¬ 3 ∣ Y₂'.index := by
    rw [← hθker, Subgroup.index_ker]
    intro h3
    exact hC (h3.trans ((Subgroup.card_dvd_of_le hθrange).trans (Subgroup.card_map_dvd _ _)))
  set Y₃ : Subgroup ↥Y := Y₂'.map g₀ with hY₃
  have hY₃n : Y₃.Normal := Subgroup.Normal.map hY₂'n g₀ hg₀
  have hY₃idx : ¬ 3 ∣ Y₃.index := fun h =>
    hidx (h.trans (Subgroup.index_map_dvd _ hg₀))
  have hsimple := isLThreeTwo_simple hY
  have h3S := isLThreeTwo_three_dvd_card hY
  set π : ↥Y →* ↥Y ⧸ CFSG.pCore 2 ↥Y := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set NS : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := Y₃.map π with hNS
  have hNSn : NS.Normal := Subgroup.Normal.map hY₃n π hπs
  haveI := hNSn
  have hNSidx : ¬ 3 ∣ NS.index := fun h => hY₃idx (h.trans (Subgroup.index_map_dvd _ hπs))
  have hNStop : NS = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal NS with h | h
    · exfalso
      apply hNSidx
      rw [h, Subgroup.index_bot]
      exact h3S
    · exact h
  let ψ : ↥Y₂ →* ↥Y ⧸ CFSG.pCore 2 ↥Y := π.comp (g₀.comp (Subgroup.inclusion hY₂D))
  have hψ : Function.Surjective ψ := by
    intro s
    have hs : s ∈ NS := by rw [hNStop]; exact Subgroup.mem_top s
    obtain ⟨y₃, hy₃, rfl⟩ := hs
    obtain ⟨d', hd', rfl⟩ := hy₃
    exact ⟨⟨(d' : Xg), hd'⟩, rfl⟩
  have hk : ∀ x ∈ ψ.ker, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hxk
    have hx1 : g₀ (Subgroup.inclusion hY₂D x) ∈ CFSG.pCore 2 ↥Y := by
      have := (MonoidHom.mem_ker).mp hxk
      exact (QuotientGroup.eq_one_iff _).mp this
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨_, hx1⟩
    have h3 : (g₀ (Subgroup.inclusion hY₂D x)) ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hf1 : f ((x : Xg) ^ 2 ^ a) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val h3
    obtain ⟨b, hb⟩ := hJ2 ((x : Xg) ^ 2 ^ a) (Jg.pow_mem (hY₂J x.2) _) hf1
    refine ⟨a + b, Subtype.ext ?_⟩
    simpa [pow_add, pow_mul] using hb
  exact isLThreeTwo_quot_pCore_of_surj hY ψ hψ hk

end CFSG.AGLEmbeddingD2.McLaughlin
