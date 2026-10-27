module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CC1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265DL28T171
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShLowerTwE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265C.C2D

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

section Plain

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem c2d_twE6_data {X : Type} [Group X] (h : catalogIs X S9.isTE6two) :
    catalogIs X (S10.isTE6n 1) ∧
      catalogIs X (onLie fun i => ∃ q, i = .twistedE6 q ∧ q.p = 2 ∧ 3 ∣ q.card + 1) := by
  obtain ⟨i, hi, he⟩ := h
  cases i with
  | lie d' =>
    obtain ⟨d, hv⟩ := d'
    cases d with
    | twistedE6 q =>
      have hq2 : q.card = 2 := by simpa [S9.isTE6two, onLie] using hi
      obtain ⟨hp, he1⟩ := HDesc.pp_eq_of_card Nat.prime_two one_ne_zero
        (hq2.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
      refine ⟨⟨_, ?_, he⟩, ⟨_, ?_, he⟩⟩
      · simpa [S10.isTE6n, onLie] using And.intro hp he1
      · exact ⟨q, rfl, hp, by rw [hq2]⟩
    | _ => simp [S9.isTE6two, onLie] at hi
  | _ => simp [S9.isTE6two, onLie] at hi

private theorem c2d_td4_data {X : Type} [Group X] (h : catalogIs X S9.isTD4two) :
    IsChevSimple 2 X ∧ catalogIs X (onLie fun | .trialityD4 _ => True | _ => False) := by
  obtain ⟨i, hi, he⟩ := h
  cases i with
  | lie d' =>
    obtain ⟨d, hv⟩ := d'
    cases d with
    | trialityD4 q =>
      have hq2 : q.card = 2 := by simpa [S9.isTD4two, onLie] using hi
      obtain ⟨hp, -⟩ := HDesc.pp_eq_of_card Nat.prime_two one_ne_zero
        (hq2.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
      refine ⟨Or.inl ⟨_, ?_, he⟩, ⟨.lie ⟨.trialityD4 q, hv⟩, trivial, he⟩⟩
      change (TauCeti.LieTypeIndex.trialityD4 q).characteristic = 2
      rw [TauCeti.LieTypeIndex.characteristic_trialityD4]
      exact hp
    | _ => simp [S9.isTD4two, onLie] at hi
  | _ => simp [S9.isTD4two, onLie] at hi

private theorem c2d_eq_bot_of_central_two {S C : Subgroup Ω} (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hCS : C ≤ S) (hCc : C ≤ Subgroup.centralizer (S : Set Ω)) (hC2 : IsPGroup 2 C) : C = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (C.subgroupOf S).Normal := ⟨fun c hc s => by
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    have hcs : (s : Ω) * c = c * s := Subgroup.mem_centralizer_iff.1 (hCc hc) s s.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcs, mul_inv_cancel_right]
    exact hc⟩
  have hcop : Nat.Coprime 3 (Nat.card (C.subgroupOf S)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCS).toEquiv]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hC2
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hle : C.subgroupOf S ≤ GLAPPrimeCore 3 ↥S := le_sSup ⟨hnorm, hcop⟩
  rw [hcore] at hle
  rw [eq_bot_iff]
  intro c hc
  have h1 := hle (Subgroup.mem_subgroupOf.2 hc : (⟨c, hCS hc⟩ : ↥S) ∈ C.subgroupOf S)
  rw [Subgroup.mem_bot] at h1 ⊢
  exact congrArg Subtype.val h1

private theorem c2d_big_elem_abelian {S E₀ U : Subgroup Ω} {x : Ω} (hE₀ : IsElemAbelian 3 E₀)
    (hE₀U : E₀ ≤ Subgroup.normalizer (U : Set Ω)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxc : ∀ g : Ω, g * x = x * g)
    (hE : 3 ^ 4 * Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω)) ≤ Nat.card E₀) :
    IsElemAbelian 3 (E₀ ⊔ Subgroup.zpowers x) ∧
      E₀ ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set Ω) ∧
      3 ^ 5 ≤ Nat.card ↥(E₀ ⊔ Subgroup.zpowers x) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCz : Subgroup.zpowers x ≤ Subgroup.center Ω :=
    Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 hxc)
  have hCN : Subgroup.zpowers x ≤ Subgroup.normalizer (E₀ : Set Ω) :=
    hCz.trans (Subgroup.center_le_normalizer _)
  have hCS : Subgroup.zpowers x ≤ Subgroup.centralizer (S : Set Ω) :=
    hCz.trans (Subgroup.center_le_centralizer _)
  have hC3 : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  refine ⟨IsElemAbelian.sup_of_commute hE₀ (isElemAbelian_zpowers hx3)
      (fun a _ b hb => Subgroup.mem_center_iff.1 (hCz hb) a),
    sup_le hE₀U (hCz.trans (Subgroup.center_le_normalizer _)), ?_⟩
  have h2 := card_sup_mul_card_inf_of_le_normalizer hCN
  rw [hC3] at h2
  have h3 : Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) ≤
      Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω)) :=
    Subgroup.card_le_of_le (inf_le_inf_left E₀ hCS)
  have hz : 0 < Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) := Nat.card_pos
  have h4 : 3 ^ 5 * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) ≤
      Nat.card ↥(E₀ ⊔ Subgroup.zpowers x) * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) := by
    calc 3 ^ 5 * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x)
        = 3 * (3 ^ 4 * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x)) := by ring
      _ ≤ 3 * (3 ^ 4 * Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ ≤ 3 * Nat.card E₀ := Nat.mul_le_mul_left _ hE
      _ = Nat.card ↥(E₀ ⊔ Subgroup.zpowers x) * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) := by
        rw [h2, mul_comm]
  exact Nat.le_of_mul_le_mul_right h4 hz

end Plain

section Lower

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem three_pow_five_le_card_of_twE6two {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL 3 S B T x D K) (hS : catalogIs (PSimple 3 S) S9.isTE6two) : 3 ^ 5 ≤ Nat.card B := by
  have cfg := h.cfg
  obtain ⟨E₀, U, -, -, hE₀, hU2, hU1, hE₀U, hE₀c⟩ :=
    T158.lowerTwE6_holds Ω S cfg.quasi (c2d_twE6_data hS).2
  obtain ⟨hE, hEU, hE5⟩ :=
    c2d_big_elem_abelian hE₀ hE₀U (cfg.elem.2 x cfg.xB) cfg.x1 cfg.xcen hE₀c
  exact hE5.trans (S265D.maxG_of_qsnl h _ U hE hU2 hU1 hEU)

end Lower

section Rank

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem c2d_card_le_of_le_inner {Q : Type} [Group Q] [Finite Q]
    (hQ : catalogIs Q S9.isTD4two) (hZ : Subgroup.center Q = ⊥) (A : Subgroup (MulAut Q))
    (hA : IsElemAbelian 3 A) (hAI : A ≤ inner Q) : Nat.card A ≤ 3 ^ 2 := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CatB.lieIndex_isTD4two hQ
  obtain ⟨hq2, hq1⟩ := HDesc.pp_eq_of_card Nat.prime_two one_ne_zero
    (hq.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
  have hinj := mulAutConj_injective_of_center_eq_bot hZ
  have hF : IsElemAbelian 3 (A.comap (MulAut.conj : Q →* MulAut Q)) :=
    isElemAbelian_comap_of_injective _ hinj hA
  have hmap : (A.comap (MulAut.conj : Q →* MulAut Q)).map (MulAut.conj : Q →* MulAut Q) = A :=
    Subgroup.map_comap_eq_self hAI
  have hFc : Nat.card ↥(A.comap (MulAut.conj : Q →* MulAut Q)) = Nat.card A := by
    have h1 := Subgroup.card_map_of_injective (K := A.comap (MulAut.conj : Q →* MulAut Q)) hinj
    rw [hmap] at h1
    exact h1.symm
  rw [← hFc]
  exact CFSG.AGLEmbedding.d4TwoRankTwo Q ⟨.trialityD4 q, hv⟩ q hq2 hq1 rfl ⟨e⟩ _ hF

private theorem c2d_three_dvd_card {K : Subgroup Ω} (hK : catalogIs (PSimple 3 K) S9.isTD4two) :
    3 ∣ Nat.card K := by
  have h1 := S265C.card_pSimple_dvd 3 K
  rw [card_fTD42 hK] at h1
  exact (by norm_num : 3 ∣ 211341312).trans h1

theorem exists_noninner_of_td4two {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL 3 S B T x D K) (hK : catalogIs (PSimple 3 K) S9.isTD4two) (hB : 3 ^ 5 ≤ Nat.card B) :
    ∃ β ∈ B, ∃ hβ : β ∈ Subgroup.normalizer (K : Set Ω), β ∉ D ∧
      chevAut 3 K ⟨β, hβ⟩ ∉ inner (PSimple 3 K) := by
  have cfg := h.cfg
  obtain ⟨hDB, -, hDcard, -, -, -, -⟩ := cfg.std
  have hNA := h.nlAct (c2d_three_dvd_card hK)
  have hBN : B ≤ Subgroup.normalizer (K : Set Ω) := hNA.norm
  by_contra hcon
  push Not at hcon
  let φ : ↥B →* MulAut (PSimple 3 K) := (chevAut 3 K).comp (Subgroup.inclusion hBN)
  have hφ1 : ∀ b : ↥B, φ b = 1 ↔ (b : Ω) ∈ D := fun b => hNA.ker b b.2 (hBN b.2)
  have hker : φ.ker = D.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, hφ1, Subgroup.mem_subgroupOf]
  have hkc : Nat.card φ.ker = 3 ^ 2 := by
    rw [hker, ← hDcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv
  have hinn : φ.range ≤ inner (PSimple 3 K) := by
    rintro _ ⟨b, rfl⟩
    by_cases hbD : (b : Ω) ∈ D
    · rw [(hφ1 b).2 hbD]
      exact Subgroup.one_mem _
    · exact hcon b b.2 (hBN b.2) hbD
  have hZ : Subgroup.center (PSimple 3 K) = ⊥ :=
    (S9.pComponent_basic Nat.prime_three hNA.comp).2.2.2
  have hle := c2d_card_le_of_le_inner hK hZ φ.range (range_isElemAbelian_of_subgroup cfg.elem φ) hinn
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hkc] at hmul
  norm_num at hle hmul hB
  omega

end Rank

section Main

theorem exists_not_innDiagOn_of_td4two {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hK : catalogIs (PSimple 3 K) S9.isTD4two)
    (hB : 3 ^ 5 ≤ Nat.card B) :
    ∃ β ∈ B, β ∉ D ∧ ¬ InnDiagOn 3 (Subgroup.zpowers β) K := by
  obtain ⟨β, hβB, hβ, hβD, hni⟩ := exists_noninner_of_td4two h hK hB
  have hKc := (h.nlAct (c2d_three_dvd_card hK)).comp
  have hNI : NonInner 3 β K :=
    ⟨hβ, fun hin => hni ((chevAut_mem_inner_iff Nat.prime_three hKc hβ).2 hin)⟩
  exact ⟨β, hβB, hβD, (MI.td4_nonInnDiag_holds Nat.prime_three hKc (c2d_td4_data hK).2 hNI).2⟩

theorem qSFamCTD4C2_of_noAct (hNoAct : T171Sh.TwE6NoAct) : S265C.C1.QSFamCTD4C2 := by
  intro Ω _ _ S B T x D K h hK hS hT₀
  exfalso
  obtain ⟨T₀, hT₀S, hT₀2, hBT₀, hne⟩ := hT₀
  have cfg := h.cfg
  have hTE6 : catalogIs (PSimple 3 S) (S10.isTE6n 1) := (c2d_twE6_data hS).1
  have hext : S171.ExtremalType 3 S := ⟨rfl, 1, odd_one, Or.inr hTE6⟩
  obtain ⟨β, hβB, hβD, hni⟩ :=
    exists_not_innDiagOn_of_td4two h hK (three_pow_five_le_card_of_twE6two h hS)
  have hKc := (h.nlAct (c2d_three_dvd_card hK)).comp
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 cfg.normal) ▸ Subgroup.mem_top g
  have hTB := hNoAct 3 Ω B x S D K β 1 cfg.kgroup (S265D.cfg_of_qsnl h) (S265D.maxG_of_qsnl h)
    cfg.normal cfg.std hKc (c2d_td4_data hK).1 hβB hβD hni hext hTE6 odd_one T₀
    (fun g _ => hSN g) (fun g _ => Subgroup.mem_centralizer_singleton_iff.2 (cfg.xcen g)) hT₀2 hBT₀
  have hle : (⁅T₀, B⁆ : Subgroup Ω) ≤ T₀ := S12.comm_le_left hBT₀
  exact hne (c2d_eq_bot_of_central_two cfg.core (hle.trans hT₀S) hTB (hT₀2.to_le hle))

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265C.C2D

end
