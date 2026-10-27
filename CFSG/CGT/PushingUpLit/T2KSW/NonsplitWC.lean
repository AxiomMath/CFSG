module

public import CFSG.CGT.PushingUpLit.T2KSW.WCover
public import CFSG.CGT.PushingUpLit.T2KSW.ZStarE
public import CFSG.CGT.PushingUpLit.T2KSW.Prop28
import CFSG.CGT.PushingUpLit.T2KSW.Coord
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)
open scoped commutatorElement
open Aux

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

namespace NonsplitWC

omit [Finite G] in
theorem comm_of_isElemAbelian {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

omit [Finite G] in
theorem isPGroup_of_isElemAbelian {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) :
    IsPGroup 2 ↥E := CFSG.Open.IsElemAbelian.isPGroup hE

omit [Finite G] in
theorem map_conj_map_conj (B : Subgroup G) (k m : G) :
    (B.map (MulAut.conj k).toMonoidHom).map (MulAut.conj m).toMonoidHom =
      B.map (MulAut.conj (m * k)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem mul_comm_of_sup {A B : Subgroup G} (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hn : A ≤ Subgroup.normalizer (B : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer (B : Set G) (Subgroup.mem_centralizer_iff.2 fun b hb =>
      (hAB a ha b hb).symm)
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_mul hn).1 hx
  obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_iff_mul hn).1 hy
  have c1 : Commute a a' := hA a ha a' ha'
  have c2 : Commute a b' := hAB a ha b' hb'
  have c3 : Commute b a' := (hAB a' ha' b hb).symm
  have c4 : Commute b b' := hB b hb b' hb'
  exact (c1.mul_right c2).mul_left (c3.mul_right c4)

theorem two_mul_card_le_of_lt {H K : Subgroup G} (h : H < K) : 2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le h.le
  have hlt := Subgroup.card_lt_of_lt h
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hKpos : 0 < Nat.card K := Nat.card_pos
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · omega
    · omega
  · calc 2 * Nat.card H ≤ k * Nat.card H := Nat.mul_le_mul_right _ hk2
      _ = Nat.card K := by rw [hk, mul_comm]

omit [Finite G] in
theorem three_le_card {E : Subgroup G} [Finite E] {a b : G} (ha : a ∈ E) (hb : b ∈ E)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) : 3 ≤ Nat.card E := by
  have h3 : ({1, a, b} : Set G).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨1, a, b, ha1.symm, hb1.symm, hab, rfl⟩
  have hsub : ({1, a, b} : Set G) ⊆ (E : Set G) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact E.one_mem
    · exact ha
    · exact hb
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3] at h
  have e : (E : Set G).ncard = Nat.card E := (Nat.card_coe_set_eq (E : Set G)).symm
  omega

theorem eq_bot_of_isPGroup_of_le_of_odd {P Q : Subgroup G} (hP : IsPGroup 2 ↥P)
    (hPQ : P ≤ Q) (hQ : Odd (Nat.card ↥Q)) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hP
  have hdvd : Nat.card ↥P ∣ Nat.card ↥Q := Subgroup.card_dvd_of_le hPQ
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ Nat.card ↥P := by
      rw [hk]
      exact dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.2 hQ) (even_iff_two_dvd.2 (h2.trans hdvd))
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem ne_bot_of_natBlock {L : Subgroup G} (h : NatBlock L n) : L ≠ ⊥ := by
  intro hL
  have := h.sixty_le_card
  rw [hL, Subgroup.card_bot] at this
  omega

theorem exists_noncomm_of_natBlock {L : Subgroup G} (h : NatBlock L n) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  exact ne_bot_of_natBlock h
    (eq_bot_of_perfect_of_pairwise_comm h.perfect fun x _ y _ => hcomm x y)

omit [Finite G] in
theorem le_normalizer_oTwoIn (hMN : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer (oTwoIn L : Set G) := fun m hm => by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_oTwoIn (hMN hm) hy, fun hy => ?_⟩
  have := conj_mem_oTwoIn (Subgroup.inv_mem _ (hMN hm)) hy
  simpa [mul_assoc] using this

omit [Finite G] in
theorem blockU_le_centralizer_Ec : blockU L ≤ Subgroup.centralizer (Ec L T : Set G) := fun v hv =>
  Subgroup.mem_centralizer_iff.2 fun _ he =>
    (Subgroup.mem_centralizer_iff.1 he.2 v (blockU_le L hv)).symm

theorem relIndex_ne_zero' (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem le_sup_zpowers_of_relIndex_le_two {X D : Subgroup G} (hXD : X ≤ D)
    (h2 : X.relIndex D ≤ 2) {i : G} (hiD : i ∈ D) (hiX : i ∉ X) :
    D ≤ X ⊔ Subgroup.zpowers i := by
  have hKD : X ⊔ Subgroup.zpowers i ≤ D := sup_le hXD (Subgroup.zpowers_le.2 hiD)
  have hXK : X ≤ X ⊔ Subgroup.zpowers i := le_sup_left
  have hmul := Subgroup.relIndex_mul_relIndex X (X ⊔ Subgroup.zpowers i) D hXK hKD
  have h1 : X.relIndex (X ⊔ Subgroup.zpowers i) ≠ 1 := fun h =>
    hiX ((Subgroup.relIndex_eq_one.1 h) (Subgroup.mem_sup_right (Subgroup.mem_zpowers i)))
  have h0 : X.relIndex (X ⊔ Subgroup.zpowers i) ≠ 0 := relIndex_ne_zero' _ _
  have h3 : (X ⊔ Subgroup.zpowers i).relIndex D ≠ 0 := relIndex_ne_zero' _ _
  have hK1 : (X ⊔ Subgroup.zpowers i).relIndex D = 1 := by
    by_contra hne
    have h4 : 2 ≤ X.relIndex (X ⊔ Subgroup.zpowers i) := by omega
    have h5 : 2 ≤ (X ⊔ Subgroup.zpowers i).relIndex D := by omega
    nlinarith
  exact Subgroup.relIndex_eq_one.1 hK1

omit [Finite G] in
@[expose] def omegaOne (X : Subgroup G) (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : Subgroup G where
  carrier := {x | x ∈ X ∧ x ^ 2 = 1}
  mul_mem' {x y} hx hy := ⟨X.mul_mem hx.1 hy.1, by
    rw [Commute.mul_pow (show Commute x y from hX x hx.1 y hy.1), hx.2, hy.2, one_mul]⟩
  one_mem' := ⟨X.one_mem, one_pow 2⟩
  inv_mem' {x} hx := ⟨X.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

omit [Finite G] in
theorem omegaOne_le (X : Subgroup G) (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : omegaOne X hX ≤ X :=
  fun _ hx => hx.1

omit [Finite G] in
theorem isElemAbelian_omegaOne (X : Subgroup G) (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    CFSG.Open.IsElemAbelian 2 (omegaOne X hX) :=
  CFSG.CGT.PushingUpLit.BHS.isElemAbelian_of_forall' (fun x hx y hy => hX x hx.1 y hy.1)
    fun _ hx => hx.2

omit [Finite G] in
theorem le_omegaOne {X B : Subgroup G} (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hB : CFSG.Open.IsElemAbelian 2 B) (hBX : B ≤ X) : B ≤ omegaOne X hX :=
  fun b hb => ⟨hBX hb, hB.2 b hb⟩

omit [Finite G] in
theorem le_normalizer_omegaOne {X K : Subgroup G} (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hK : K ≤ Subgroup.normalizer (X : Set G)) :
    K ≤ Subgroup.normalizer (omegaOne X hX : Set G) := by
  have key : ∀ m ∈ K, ∀ x ∈ omegaOne X hX, m * x * m⁻¹ ∈ omegaOne X hX := fun m hm x hx =>
    ⟨(Subgroup.mem_normalizer_iff.1 (hK hm) x).1 hx.1, by rw [conj_pow, hx.2]; group⟩
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key m hm y, fun hy => ?_⟩
  have := key m⁻¹ (K.inv_mem hm) _ hy
  simpa [mul_assoc] using this

end NonsplitWC

open NonsplitWC

structure NonsplitSetup (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) : Prop where
  sec4 : Sec4 G L M T n
  MN : M ≤ Subgroup.normalizer (L : Set G)
  ME : M ≤ Subgroup.normalizer (Ec L T : Set G)
  ne_bot : Ec L T ≠ ⊥
  not_wleVE : ¬ oTwoIn L ≤ blockU L ⊔ Ec L T
  hZ : L ⊓ Subgroup.centralizer (L : Set G) ≤ blockU L
  RD : T ≤ Rl L T ⊔ Dc L T

namespace NonsplitSetup

variable (hc : NonsplitSetup G L M T n)
include hc

theorem normalizer_Ec_eq : Subgroup.normalizer (Ec L T : Set G) = M := by
  by_contra hne
  have hlt : M < Subgroup.normalizer (Ec L T : Set G) := lt_of_le_of_ne hc.ME (Ne.symm hne)
  exact hc.sec4.hyp.maxLocal.2 _ hlt
    ⟨Ec L T, hc.ne_bot, hc.sec4.sylow.isPGroup.to_le inf_le_left, rfl⟩

theorem Ec_inf_conj_eq_bot {g : G} (hg : g ∉ M) :
    Ec L T ⊓ (Ec L T).map (MulAut.conj g).toMonoidHom = ⊥ :=
  eq_bot_of_isPGroup_of_le_of_odd (hc.sec4.sylow.isPGroup.to_le (inf_le_left.trans inf_le_left))
    (inf_le_inf inf_le_right (Subgroup.map_mono inf_le_right)) (hc.sec4.hyp.odd_inf_conj hg)

theorem centralizer_le_M {x : G} (hx : x ∈ Ec L T) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  have hsq : x ^ 2 = 1 := hc.sec4.S_elem.2 x hx
  obtain ⟨N, hCN, hNmax⟩ :=
    RankThree.PartOne.Sec15Final.exists_isMaximalTwoLocal_ge (isPLocal_centralizer_of_sq hsq hx1)
  have hLC : L ≤ Subgroup.centralizer ({x} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hx.2 l hl)
  have hNM : N = M := by
    have : N ∈ maximalTwoLocalsContaining (L : Set G) := ⟨hNmax, fun y hy => hCN (hLC hy)⟩
    rw [hc.sec4.hyp.unique] at this
    exact this
  rw [← hNM]
  exact hCN

theorem ne : oTwoIn L ≠ blockU L := fun h => hc.not_wleVE (h.le.trans le_sup_left)

theorem n_eq_two : n = 2 := by
  have h2 := hc.sec4.hyp.two_le
  by_contra hn
  exact hc.ne (hc.sec4.hyp.natBlock.oTwoIn_eq_blockU_of_three_le (by omega))

theorem Ec_inf_oTwoIn_le : Ec L T ⊓ oTwoIn L ≤ blockU L := fun _ he =>
  hc.hZ ⟨oTwoIn_le L he.2, he.1.2⟩

theorem oTwoIn_inf_sup_le : oTwoIn L ⊓ (blockU L ⊔ Ec L T) ≤ blockU L := by
  rintro x ⟨hxW, hx⟩
  have hn : blockU L ≤ Subgroup.normalizer (Ec L T : Set G) :=
    blockU_le_centralizer_Ec.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨v, hv, e, he, rfl⟩ := (mem_sup_iff_mul hn).1 hx
  have heW : e ∈ oTwoIn L := by
    have := (oTwoIn L).mul_mem ((oTwoIn L).inv_mem (blockU_le_oTwoIn L hv)) hxW
    simpa using this
  exact mul_mem hv (hc.Ec_inf_oTwoIn_le ⟨he, heW⟩)

theorem WE_le_Dc : oTwoIn L ⊔ Ec L T ≤ Dc L T :=
  sup_le (oTwoIn_le_Dc hc.sec4.hyp.natBlock hc.sec4.hyp.le hc.MN hc.sec4.sylow) Ec_le_Dc

theorem WE_comm : ∀ x ∈ oTwoIn L ⊔ Ec L T, ∀ y ∈ oTwoIn L ⊔ Ec L T, x * y = y * x :=
  mul_comm_of_sup (fun _ ha _ ha' => oTwoIn_comm hc.sec4.hyp.natBlock ha ha')
    (fun _ hb _ hb' => comm_of_isElemAbelian hc.sec4.S_elem hb hb')
    (fun a ha _ hb => Subgroup.mem_centralizer_iff.1 hb.2 a (oTwoIn_le L ha))

theorem two_mul_card_le :
    2 * Nat.card (Ec L T ⊔ blockU L : Subgroup G) ≤ Nat.card (oTwoIn L ⊔ Ec L T : Subgroup G) := by
  have hle : Ec L T ⊔ blockU L ≤ oTwoIn L ⊔ Ec L T :=
    sup_le le_sup_right ((blockU_le_oTwoIn L).trans le_sup_left)
  have hlt : Ec L T ⊔ blockU L < oTwoIn L ⊔ Ec L T := by
    refine lt_of_le_of_ne hle fun h => hc.not_wleVE ?_
    rw [sup_comm] at h
    exact le_sup_left.trans h.ge
  exact two_mul_card_le_of_lt hlt

theorem card_Dc_le_two_mul :
    Nat.card (Dc L T) ≤ 2 * Nat.card (oTwoIn L ⊔ Ec L T : Subgroup G) := by
  have h1 := card_Dc_le hc.sec4.hyp.natBlock hc.sec4.hyp.le hc.MN hc.sec4.sylow
  rw [hc.n_eq_two] at h1
  have h2 := hc.two_mul_card_le
  have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [h4] at h1
  omega

theorem relIndex_WE_le_two : (oTwoIn L ⊔ Ec L T).relIndex (Dc L T) ≤ 2 := by
  have h1 := Subgroup.relIndex_mul_card (H := oTwoIn L ⊔ Ec L T) (K := Dc L T)
  rw [inf_of_le_left hc.WE_le_Dc] at h1
  have h2 := hc.card_Dc_le_two_mul
  have hpos : 0 < Nat.card (oTwoIn L ⊔ Ec L T : Subgroup G) := Nat.card_pos
  by_contra hgt
  push Not at hgt
  nlinarith

theorem sq_ne_one_of_not_mem_Dc {a : G} (haT : a ∈ T) (haD : a ∉ Dc L T) : a ^ 2 ≠ 1 := by
  have hs := hc.sec4
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN := hc.MN
  have hT : IsSylowOf 2 T M := hs.sylow
  have hRn : Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
    Rl_le_T.trans (le_normalizer_Dc hMN hT.le)
  obtain ⟨l, hl, d, hd, rfl⟩ := (mem_sup_iff_mul hRn).1 (hc.RD haT)
  have hlW : l ∉ oTwoIn L := fun hlW => haD (mul_mem (oTwoIn_le_Dc h hLM hMN hT hlW) hd)
  obtain ⟨H, hA⟩ := exists_utri_coord h hLM hMN hT
  have hl2W : l ^ 2 ∈ oTwoIn L := by
    obtain ⟨s, hs'⟩ := hA l hl.2 hl.1
    exact H.sq_mem_oTwoIn_of_utri hl.2 hs'
  have hl2V : l ^ 2 ∉ blockU L := fun h2 => hc.ne (h.oTwoIn_eq_blockU_of_sq_mem hl.2 hlW h2)
  have hdQ : d ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨hT.le hd.1, hd.2⟩
  have hv₁ : l⁻¹ * d * l * d⁻¹ ∈ blockU L := by
    have h1 := (blockU L).inv_mem (h.comm_centralizer_mem_blockU hMN hdQ l⁻¹ (L.inv_mem hl.2))
    have e : (⁅d, l⁻¹⁆)⁻¹ = l⁻¹ * d * l * d⁻¹ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h1
  have e : (l * d) ^ 2 = l ^ 2 * (l⁻¹ * d * l * d⁻¹) * d ^ 2 := by
    simp only [pow_two]
    group
  intro hsq
  rw [e] at hsq
  have hmem : l ^ 2 ∈ blockU L ⊔ Ec L T := by
    have hx : l ^ 2 = ((l⁻¹ * d * l * d⁻¹) * d ^ 2)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
      exact hsq
    rw [hx]
    exact inv_mem (mul_mem (Subgroup.mem_sup_left hv₁)
      (Subgroup.mem_sup_right (Dc_sq_mem_Ec h hMN hT hd)))
  exact hl2V (hc.oTwoIn_inf_sup_le ⟨hl2W, hmem⟩)

theorem mem_Dc_of_sq_eq_one {a : G} (haT : a ∈ T) (ha2 : a ^ 2 = 1) : a ∈ Dc L T := by
  by_contra h
  exact hc.sq_ne_one_of_not_mem_Dc haT h ha2

theorem le_Dc_of_isElemAbelian {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 2 B) (hBT : B ≤ T) :
    B ≤ Dc L T := fun b hb => hc.mem_Dc_of_sq_eq_one (hBT hb) (hB.2 b hb)

theorem le_normalizer_of_between {B : Subgroup G} (hVB : blockU L ≤ B) (hBD : B ≤ Dc L T) :
    L ≤ Subgroup.normalizer (B : Set G) := by
  have h := hc.sec4.hyp.natBlock
  have key : ∀ l ∈ L, ∀ y ∈ B, l * y * l⁻¹ ∈ B := by
    intro l hl y hy
    have hyD := hBD hy
    have hyQ : y ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) :=
      ⟨hc.sec4.sylow.le hyD.1, hyD.2⟩
    have h1 : ⁅y, l⁆ ∈ blockU L := h.comm_centralizer_mem_blockU hc.MN hyQ l hl
    have e : l * y * l⁻¹ = (⁅y, l⁆)⁻¹ * y := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (inv_mem (hVB h1)) hy
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key l hl y, fun hy => ?_⟩
  have := key l⁻¹ (L.inv_mem hl) _ hy
  simpa [mul_assoc] using this

theorem normalizer_le_M_of_between {B : Subgroup G} (hVB : blockU L ≤ B) (hBD : B ≤ Dc L T)
    (hB2 : IsPGroup 2 ↥B) : Subgroup.normalizer (B : Set G) ≤ M := by
  have hB : B ≠ ⊥ := fun h => hc.sec4.hyp.blockU_ne_bot (le_bot_iff.1 (h ▸ hVB))
  obtain ⟨N, hle, hNmax⟩ := RankThree.PartOne.Sec15Final.exists_isMaximalTwoLocal_ge
    (show IsPLocal 2 (Subgroup.normalizer (B : Set G)) from ⟨B, hB, hB2, rfl⟩)
  have hNM : N = M := by
    have : N ∈ maximalTwoLocalsContaining (L : Set G) :=
      ⟨hNmax, fun x hx => hle (hc.le_normalizer_of_between hVB hBD hx)⟩
    rw [hc.sec4.hyp.unique] at this
    exact this
  rw [← hNM]
  exact hle

theorem blockU_le_of_max {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 2 B) (hBD : B ≤ Dc L T)
    (hmax : ∀ B' : Subgroup G, CFSG.Open.IsElemAbelian 2 B' → B' ≤ Dc L T →
      Nat.card B' ≤ Nat.card B) : blockU L ≤ B := by
  have h := hc.sec4.hyp.natBlock
  have hVD : blockU L ≤ Dc L T := blockU_le_Dc h hc.sec4.hyp.le hc.MN hc.sec4.sylow
  have hVel : CFSG.Open.IsElemAbelian 2 (blockU L) :=
    CFSG.CGT.PushingUpLit.BHS.isElemAbelian_of_forall' (fun x hx y hy => h.blockU_comm x hx y hy)
      fun x hx => h.sq_eq_one_of_mem_blockU hx
  have hsup : CFSG.Open.IsElemAbelian 2 (B ⊔ blockU L) :=
    CFSG.CGT.PushingUpLit.BHS.isElemAbelian_sup' hB hVel fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.1 (hBD hx).2 y hy).symm
  have hle := hmax _ hsup (sup_le hBD hVD)
  have heq : B = B ⊔ blockU L := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  rw [heq]
  exact le_sup_right

theorem exists_family_of_abelian (hDab : ∀ x ∈ Dc L T, ∀ y ∈ Dc L T, x * y = y * x) :
    ∃ B : Subgroup G, CFSG.Open.IsElemAbelian 2 B ∧ blockU L ≤ B ∧ B ≤ Dc L T ∧
      (∀ g : G, (Ec L T).map (MulAut.conj g).toMonoidHom ≤ T →
        ∃ y ∈ (Ec L T).map (MulAut.conj g).toMonoidHom, y ∈ B ∧ y ≠ 1) ∧
      ∀ k : G, B.map (MulAut.conj k).toMonoidHom ≤ Dc L T → k ∈ M := by
  have hs := hc.sec4
  have h : NatBlock L n := hs.hyp.natBlock
  have hVD : blockU L ≤ Dc L T := blockU_le_Dc h hs.hyp.le hc.MN hs.sylow
  have hVB : blockU L ≤ omegaOne (Dc L T) hDab := fun v hv =>
    ⟨hVD hv, h.sq_eq_one_of_mem_blockU hv⟩
  have hBab := isElemAbelian_omegaOne (Dc L T) hDab
  refine ⟨omegaOne (Dc L T) hDab, hBab, hVB, omegaOne_le _ _, fun g hg => ?_, fun k hk => ?_⟩
  · have hYab := isElemAbelian_map_conj hs.S_elem g
    have hYB : (Ec L T).map (MulAut.conj g).toMonoidHom ≤ omegaOne (Dc L T) hDab :=
      le_omegaOne hDab hYab (hc.le_Dc_of_isElemAbelian hYab hg)
    obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ne_bot
    have hy : g * e * g⁻¹ ∈ (Ec L T).map (MulAut.conj g).toMonoidHom :=
      ⟨e, he, by simp [MulAut.conj_apply]⟩
    refine ⟨g * e * g⁻¹, hy, hYB hy, fun h1 => he1 (Subtype.ext ?_)⟩
    show e = 1
    calc e = g⁻¹ * (g * e * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · have hB2 : CFSG.Open.IsElemAbelian 2
        ((omegaOne (Dc L T) hDab).map (MulAut.conj k).toMonoidHom) :=
      isElemAbelian_map_conj hBab k
    have hle := le_omegaOne hDab hB2 hk
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_conj])
    exact hc.normalizer_le_M_of_between hVB (omegaOne_le _ _) (isPGroup_of_isElemAbelian hBab)
      (mem_normalizer_of_map_conj_eq heq)

theorem exists_not_mem_WE (hDab : ¬ ∀ x ∈ Dc L T, ∀ y ∈ Dc L T, x * y = y * x) :
    ∃ i ∈ Dc L T, i ∉ oTwoIn L ⊔ Ec L T := by
  by_contra hcon
  push Not at hcon
  exact hDab fun x hx y hy => hc.WE_comm x (hcon x hx) y (hcon y hy)

theorem exists_not_comm (hDab : ¬ ∀ x ∈ Dc L T, ∀ y ∈ Dc L T, x * y = y * x) {i : G}
    (hiD : i ∈ Dc L T) (hiX : i ∉ oTwoIn L ⊔ Ec L T) : ∃ e ∈ Ec L T, i * e ≠ e * i := by
  by_contra hcon
  push Not at hcon
  apply hDab
  have hle := le_sup_zpowers_of_relIndex_le_two hc.WE_le_Dc hc.relIndex_WE_le_two hiD hiX
  have hXi : ∀ x ∈ oTwoIn L ⊔ Ec L T, x * i = i * x := by
    have hX : oTwoIn L ⊔ Ec L T ≤ Subgroup.centralizer ({i} : Set G) := by
      refine sup_le (fun w hw => ?_) (fun e he => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Dc_centralizes_oTwoIn_of_sylow hc.sec4.hyp.natBlock hc.sec4.hyp.le hc.MN
          hc.sec4.sylow w hw i hiD
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hcon e he).symm
    exact fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (hX hx)
  have hcomm := mul_comm_of_sup (A := oTwoIn L ⊔ Ec L T) (B := Subgroup.zpowers i) hc.WE_comm
    (fun b hb b' hb' => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
      exact ((Commute.refl i).zpow_zpow k k').eq)
    (fun a ha b hb => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact ((show Commute a i from hXi a ha).zpow_right k).eq)
  exact fun x hx y hy => hcomm x (hle hx) y (hle hy)

theorem card_le_card_omegaOne (hDab : ¬ ∀ x ∈ Dc L T, ∀ y ∈ Dc L T, x * y = y * x)
    {B' : Subgroup G} (hB' : CFSG.Open.IsElemAbelian 2 B') (hB'D : B' ≤ Dc L T) :
    Nat.card B' ≤ Nat.card (omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm) := by
  by_cases hB'X : B' ≤ oTwoIn L ⊔ Ec L T
  · exact Subgroup.card_le_of_le (le_omegaOne hc.WE_comm hB' hB'X)
  · obtain ⟨i, hiB', hiX⟩ := Set.not_subset.1 hB'X
    obtain ⟨e, he, hie⟩ := hc.exists_not_comm hDab (hB'D hiB') hiX
    have hC : Nat.card B' ≤ 2 * Nat.card ↥((oTwoIn L ⊔ Ec L T) ⊓ B') := by
      have h1 := Subgroup.relIndex_mul_card (H := oTwoIn L ⊔ Ec L T) (K := B')
      have h2 : (oTwoIn L ⊔ Ec L T).relIndex B' ≤ 2 :=
        (Subgroup.relIndex_le_of_le_right hB'D (relIndex_ne_zero' _ _)).trans
          hc.relIndex_WE_le_two
      calc Nat.card B' = (oTwoIn L ⊔ Ec L T).relIndex B' * Nat.card ↥((oTwoIn L ⊔ Ec L T) ⊓ B') :=
            h1.symm
        _ ≤ 2 * Nat.card ↥((oTwoIn L ⊔ Ec L T) ⊓ B') := Nat.mul_le_mul_right _ h2
    have hCA : (oTwoIn L ⊔ Ec L T) ⊓ B' ≤
        omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm ⊓ Subgroup.centralizer ({i} : Set G) :=
      fun x hx => ⟨⟨hx.1, hB'.2 x hx.2⟩, Subgroup.mem_centralizer_singleton_iff.2
        (comm_of_isElemAbelian hB' hx.2 hiB')⟩
    have heA : e ∈ omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm :=
      ⟨Subgroup.mem_sup_right he, hc.sec4.S_elem.2 e he⟩
    have hlt : omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm ⊓ Subgroup.centralizer ({i} : Set G) <
        omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm :=
      inf_lt_left.2 fun h => hie (Subgroup.mem_centralizer_singleton_iff.1 (h heA)).symm
    calc Nat.card B' ≤ 2 * Nat.card ↥((oTwoIn L ⊔ Ec L T) ⊓ B') := hC
      _ ≤ 2 * Nat.card ↥(omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm ⊓
            Subgroup.centralizer ({i} : Set G)) :=
          Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hCA)
      _ ≤ Nat.card (omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm) := two_mul_card_le_of_lt hlt

theorem three_le_card_Ec (hDab : ¬ ∀ x ∈ Dc L T, ∀ y ∈ Dc L T, x * y = y * x) :
    3 ≤ Nat.card (Ec L T) := by
  obtain ⟨i, hiD, hiX⟩ := hc.exists_not_mem_WE hDab
  obtain ⟨e, he, hie⟩ := hc.exists_not_comm hDab hiD hiX
  have hTE : T ≤ Subgroup.normalizer (Ec L T : Set G) := hc.sec4.sylow.le.trans hc.ME
  have he' : i * e * i⁻¹ ∈ Ec L T := (Subgroup.mem_normalizer_iff.1 (hTE hiD.1) e).1 he
  have he1 : e ≠ 1 := fun h1 => hie (by rw [h1]; simp)
  have he1' : i * e * i⁻¹ ≠ 1 := fun h1 => he1 (by
    calc e = i⁻¹ * (i * e * i⁻¹) * i := by group
      _ = 1 := by rw [h1]; group)
  have hne : e ≠ i * e * i⁻¹ := fun h1 => hie (by
    calc i * e = (i * e * i⁻¹) * i := by group
      _ = e * i := by rw [← h1])
  exact three_le_card he he' he1 he1' hne

theorem exists_mem_conj_inf (hDab : ¬ ∀ x ∈ Dc L T, ∀ y ∈ Dc L T, x * y = y * x) {g : G}
    (hg : (Ec L T).map (MulAut.conj g).toMonoidHom ≤ T) :
    ∃ y ∈ (Ec L T).map (MulAut.conj g).toMonoidHom,
      y ∈ omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm ∧ y ≠ 1 := by
  have hYab := isElemAbelian_map_conj hc.sec4.S_elem g
  have hYD : (Ec L T).map (MulAut.conj g).toMonoidHom ≤ Dc L T :=
    hc.le_Dc_of_isElemAbelian hYab hg
  by_contra hcon
  push Not at hcon
  have hbot : (oTwoIn L ⊔ Ec L T) ⊓ (Ec L T).map (MulAut.conj g).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    exact Subgroup.mem_bot.2 (hcon y hy.2 ⟨hy.1, hYab.2 y hy.2⟩)
  have h1 := Subgroup.relIndex_mul_card (H := oTwoIn L ⊔ Ec L T)
    (K := (Ec L T).map (MulAut.conj g).toMonoidHom)
  rw [hbot, Subgroup.card_bot, mul_one, card_map_conj] at h1
  have h2 : (oTwoIn L ⊔ Ec L T).relIndex ((Ec L T).map (MulAut.conj g).toMonoidHom) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hYD (relIndex_ne_zero' _ _)).trans hc.relIndex_WE_le_two
  have h3 := hc.three_le_card_Ec hDab
  omega

theorem exists_family_of_nonabelian (hDab : ¬ ∀ x ∈ Dc L T, ∀ y ∈ Dc L T, x * y = y * x) :
    ∃ B : Subgroup G, CFSG.Open.IsElemAbelian 2 B ∧ blockU L ≤ B ∧ B ≤ Dc L T ∧
      (∀ g : G, (Ec L T).map (MulAut.conj g).toMonoidHom ≤ T →
        ∃ y ∈ (Ec L T).map (MulAut.conj g).toMonoidHom, y ∈ B ∧ y ≠ 1) ∧
      ∀ k : G, B.map (MulAut.conj k).toMonoidHom ≤ Dc L T → k ∈ M := by
  have hs := hc.sec4
  have h : NatBlock L n := hs.hyp.natBlock
  have hVA : blockU L ≤ omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm := fun v hv =>
    ⟨(blockU_le_oTwoIn L).trans le_sup_left hv, h.sq_eq_one_of_mem_blockU hv⟩
  have hAab := isElemAbelian_omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm
  have hAD : omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm ≤ Dc L T :=
    (omegaOne_le _ _).trans hc.WE_le_Dc
  have hMA : M ≤ Subgroup.normalizer (omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm : Set G) :=
    le_normalizer_omegaOne hc.WE_comm fun m hm =>
      mem_normalizer_sup (le_normalizer_oTwoIn hc.MN hm) (hc.ME hm)
  refine ⟨omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm, hAab, hVA, hAD,
    fun g hg => hc.exists_mem_conj_inf hDab hg, fun k hk => ?_⟩
  have hB₂ab : CFSG.Open.IsElemAbelian 2
      ((omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm).map (MulAut.conj k).toMonoidHom) :=
    isElemAbelian_map_conj hAab k
  have hmax : ∀ B' : Subgroup G, CFSG.Open.IsElemAbelian 2 B' → B' ≤ Dc L T →
      Nat.card B' ≤
        Nat.card ((omegaOne (oTwoIn L ⊔ Ec L T) hc.WE_comm).map (MulAut.conj k).toMonoidHom) :=
    fun B' hB' hB'D => by
      rw [card_map_conj]
      exact hc.card_le_card_omegaOne hDab hB' hB'D
  have hVB₂ := hc.blockU_le_of_max hB₂ab hk hmax
  have hN₂ := hc.normalizer_le_M_of_between hVB₂ hk (isPGroup_of_isElemAbelian hB₂ab)
  have hMk : M.map (MulAut.conj k).toMonoidHom ≤ M := by
    rintro _ ⟨m, hm, rfl⟩
    apply hN₂
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_map_conj_iff, mem_map_conj_iff]
    have e : k⁻¹ * ((MulAut.conj k).toMonoidHom m * y * ((MulAut.conj k).toMonoidHom m)⁻¹) * k =
        m * (k⁻¹ * y * k) * m⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact Subgroup.mem_normalizer_iff.1 (hMA hm) _
  have hMeq : M.map (MulAut.conj k).toMonoidHom = M :=
    Subgroup.eq_of_le_of_card_ge hMk (by rw [card_map_conj])
  have hkN : k ∈ Subgroup.normalizer (M : Set G) := mem_normalizer_of_map_conj_eq hMeq
  rwa [RankThree.PartTwo.Late.normalizer_self_of_isMaximalTwoLocal hs.hyp.maxLocal] at hkN

theorem exists_family :
    ∃ B : Subgroup G, CFSG.Open.IsElemAbelian 2 B ∧ blockU L ≤ B ∧ B ≤ Dc L T ∧
      (∀ g : G, (Ec L T).map (MulAut.conj g).toMonoidHom ≤ T →
        ∃ y ∈ (Ec L T).map (MulAut.conj g).toMonoidHom, y ∈ B ∧ y ≠ 1) ∧
      ∀ k : G, B.map (MulAut.conj k).toMonoidHom ≤ Dc L T → k ∈ M := by
  by_cases hDab : ∀ x ∈ Dc L T, ∀ y ∈ Dc L T, x * y = y * x
  · exact hc.exists_family_of_abelian hDab
  · exact hc.exists_family_of_nonabelian hDab

theorem mem_M_of_conj_Ec_le {g : G} (hg : (Ec L T).map (MulAut.conj g).toMonoidHom ≤ T) :
    g ∈ M := by
  obtain ⟨B, hBab, -, -, hy, hrig⟩ := hc.exists_family
  obtain ⟨y, hyY, hyB, hy1⟩ := hy g hg
  have he : g⁻¹ * y * g ∈ Ec L T := (mem_map_conj_iff g _ y).1 hyY
  have he1 : g⁻¹ * y * g ≠ 1 := fun h1 => hy1 (by
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  have hCe := hc.centralizer_le_M he he1
  have hB1 : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
    rintro _ ⟨b, hb, rfl⟩
    apply hCe
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hby : b * y = y * b := comm_of_isElemAbelian hBab hb hyB
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * b * g * (g⁻¹ * y * g) = g⁻¹ * (b * y) * g := by group
      _ = g⁻¹ * (y * b) * g := by rw [hby]
      _ = g⁻¹ * y * g * (g⁻¹ * b * g) := by group
  obtain ⟨m, hm, hmT⟩ := exists_conj_le_of_isPGroup hc.sec4.sylow
    ((isPGroup_of_isElemAbelian hBab).map _) hB1
  rw [map_conj_map_conj] at hmT
  have hD := hc.le_Dc_of_isElemAbelian (isElemAbelian_map_conj hBab _) hmT
  have hmg := hrig _ hD
  have hginv : g⁻¹ ∈ M := by
    have := M.mul_mem (M.inv_mem hm) hmg
    simpa using this
  simpa using M.inv_mem hginv

theorem weaklyClosed_Ec (g : G) (hg : (Ec L T).map (MulAut.conj g).toMonoidHom ≤ T) :
    (Ec L T).map (MulAut.conj g).toMonoidHom = Ec L T :=
  map_conj_eq_of_mem_normalizer (hc.ME (hc.mem_M_of_conj_Ec_le hg))

theorem card_Ec_lt_card_T : 2 ^ (3 * n) * Nat.card (Ec L T) < Nat.card T := by
  have hs := hc.sec4
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hTRD : Rl L T ⊔ Dc L T = T := le_antisymm (sup_le Rl_le_T Dc_le_T) hc.RD
  have hT : Nat.card T = 2 ^ n * Nat.card (Dc L T) := by
    have := card_Rl_sup_Dc h hLM hc.MN hs.sylow
    rwa [hTRD] at this
  have hVT : blockU L ≤ T := NatBlock.blockU_le_sylow hLM hc.MN hs.sylow
  have hVn : blockU L ≤ Subgroup.normalizer (Ec L T : Set G) :=
    blockU_le_centralizer_Ec.trans (Subgroup.centralizer_le_normalizer _)
  have hEV := card_sup_mul_card_inf_of_le_normalizer hVn
  have hEVcap : Ec L T ⊓ blockU L = blockZ L := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hVT hx.1, hx.2⟩, hx.1⟩⟩
  rw [hEVcap, h.card_blockU] at hEV
  have hZpos : 0 < Nat.card (blockZ L) := Nat.card_pos
  have hEVcard : Nat.card (Ec L T ⊔ blockU L : Subgroup G) = (2 ^ n) ^ 2 * Nat.card (Ec L T) := by
    apply Nat.eq_of_mul_eq_mul_right hZpos
    rw [hEV]
    ring
  have hD : 2 * ((2 ^ n) ^ 2 * Nat.card (Ec L T)) ≤ Nat.card (Dc L T) :=
    calc 2 * ((2 ^ n) ^ 2 * Nat.card (Ec L T)) = 2 * Nat.card (Ec L T ⊔ blockU L : Subgroup G) :=
          by rw [hEVcard]
      _ ≤ Nat.card (oTwoIn L ⊔ Ec L T : Subgroup G) := hc.two_mul_card_le
      _ ≤ Nat.card (Dc L T) := Subgroup.card_le_of_le hc.WE_le_Dc
  have h2n : 2 ^ (3 * n) = 2 ^ n * (2 ^ n) ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have hEpos : 0 < Nat.card (Ec L T) := Nat.card_pos
  have hpos : 0 < 2 ^ n := by positivity
  rw [hT, h2n]
  have hq : 0 < (2 ^ n) ^ 2 * Nat.card (Ec L T) := by positivity
  calc 2 ^ n * (2 ^ n) ^ 2 * Nat.card (Ec L T) = 2 ^ n * ((2 ^ n) ^ 2 * Nat.card (Ec L T)) := by
        ring
    _ < 2 ^ n * (2 * ((2 ^ n) ^ 2 * Nat.card (Ec L T))) :=
        Nat.mul_lt_mul_of_pos_left (by omega) hpos
    _ ≤ 2 ^ n * Nat.card (Dc L T) := Nat.mul_le_mul_left _ hD

end NonsplitSetup

theorem NonsplitSetup.of_hyps (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight)
    (h25 : Asc76Lemma25) (hs : Sec4 G L M T n) (hE : Ec L T ≠ ⊥)
    (hNS : ¬ oTwoIn L ≤ blockU L ⊔ Ec L T) (hRD : T ≤ Rl L T ⊔ Dc L T) :
    NonsplitSetup G L M T n := by
  have hne : oTwoIn L ≠ blockU L := fun h => hNS (h.le.trans le_sup_left)
  have hZ : L ⊓ Subgroup.centralizer (L : Set G) ≤ blockU L := by
    by_contra hcon
    exact hNS ((wleVE_iff hs hE1 hne).2 hcon)
  obtain ⟨-, -, hME⟩ := hs.hyp.four_four hE1 hE8 h25 hs.sylow
  exact ⟨hs, hs.hyp.normal hE1, hME, hE, hNS, hZ, hRD⟩

theorem false_of_nonsplit
    (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight) (h25 : Asc76Lemma25)
    (hSCL : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (hList : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ} (hs : Sec4 G L M T n)
    (hE : Ec L T ≠ ⊥) (hNS : ¬ oTwoIn L ≤ blockU L ⊔ Ec L T)
    (hRD : T ≤ Rl L T ⊔ Dc L T) : False := by
  have hc : NonsplitSetup G L M T n := NonsplitSetup.of_hyps hE1 hE8 h25 hs hE hNS hRD
  have : IsSimpleGroup G := hs.hyp.simple
  have hstd : CFSG.CGT.Timmesfeld75.StdPair G (Ec L T) :=
    stdPair_of_weaklyClosed hSCL hList (exists_noncomm_of_natBlock hs.hyp.natBlock)
      Ec_le_T hE hs.S_elem hc.normalizer_Ec_eq hs.sylow hs.sylowG
      (fun g hg => hc.Ec_inf_conj_eq_bot hg) (fun g hg => hc.weaklyClosed_Ec g hg)
  exact list_false hs.hyp.two_le hs.hyp.natBlock.perfect (ne_bot_of_natBlock hs.hyp.natBlock)
    hs.sylowG (le_centralizer_inf_centralizer L T) hc.card_Ec_lt_card_T hstd

theorem wleVE_of_Rl_sup_Dc
    (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight) (h25 : Asc76Lemma25)
    (hSCL : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (hList : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ} (hs : Sec4 G L M T n)
    (hE : Ec L T ≠ ⊥) (hRD : T ≤ Rl L T ⊔ Dc L T) : oTwoIn L ≤ blockU L ⊔ Ec L T :=
  by_contra fun hNS => false_of_nonsplit hE1 hE8 h25 hSCL hList hs hE hNS hRD

end CFSG.CGT.PushingUpLit.T2KSW
