module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeAbs
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenHypAux
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SylowU43
import CFSG.GroupTheory.ElementaryAbelianTransport
import TauCeti.Algebra.Group.Coprime
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44ReifartTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.EvenSporadicStandard.TwoFi22.DS81
open CFSG.LieType.Multipliers.U43 (X₀ xElt card_X₀)
open CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv (u43_isConj_xElt hSub_eq_centralizer
  card_hSub)
open scoped commutatorElement


private theorem eq_bot_of_elemAbelian81_le_normalizer {E T : Subgroup X₀}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 81) (hT : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set X₀)) : T = ⊥ := by
  haveI : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hc
    omega
  refine eq_bot_iff.2 (le_of_hyperplane_centralizers Nat.prime_three hE hE1 hET
    (coprime_card_of_le_isPGroup_two Nat.prime_three (by norm_num) hT le_rfl) fun H hHE hHc => ?_)
  have hH : Nat.card H = 27 := by omega
  by_contra hne
  obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 fun h => hne h.le
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2
    (((hT.to_le inf_le_left).dvd_orderOf hg1).trans (orderOf_dvd_natCard g))
  obtain ⟨c, hcu⟩ := isConj_iff.1 (u43_isConj_xElt ((Subgroup.orderOf_coe u).trans hu))
  have huH := (Subgroup.mem_inf.1 u.2).2
  have hx : xElt = c⁻¹ * (u : X₀) * c := by
    rw [← hcu]
    group
  have hle : H.map (MulAut.conj c⁻¹).toMonoidHom ≤ Subgroup.centralizer ({xElt} : Set X₀) := by
    rintro _ ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hx]
    have e1 : c⁻¹ * h * c⁻¹⁻¹ * (c⁻¹ * (u : X₀) * c) = c⁻¹ * (h * u) * c := by group
    have e2 : c⁻¹ * (u : X₀) * c * (c⁻¹ * h * c⁻¹⁻¹) = c⁻¹ * (u * h) * c := by group
    rw [e1, e2, Subgroup.mem_centralizer_iff.1 huH h hh]
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hH, ← hSub_eq_centralizer,
    card_hSub] at hdvd
  norm_num at hdvd

theorem le_of_parrottData_elemAbelian {C : Type} [Group C] [Finite C] {Q Nt K₁ : Subgroup C}
    (hd : ParrottData C X₀ Q Nt K₁) {B T : Subgroup C} (hB : IsElemAbelian 3 B)
    (hc : Nat.card B = 243) (hT : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set C)) : T ≤ Q := by
  haveI := hd.normal_Q
  obtain ⟨π, -, hπk⟩ := hd.hom
  have hQ0 : 0 < Nat.card Q := by rw [hd.card_Q]; norm_num
  have hBK : B ≤ K₁ := fun b hb => by
    have h := Subgroup.sq_mem_of_index_two hd.index_K (b ^ 2)
    rwa [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hB.2 b hb, one_mul] at h
  have hBN : Nat.card ↥(B ⊓ Nt) ∣ 3 := by
    have h1 := Subgroup.card_dvd_of_le (inf_le_left : B ⊓ Nt ≤ B)
    have h2 := Subgroup.card_dvd_of_le (inf_le_right : B ⊓ Nt ≤ Nt)
    rw [hc] at h1
    rw [hd.card_Nt, hd.card_Q] at h2
    exact (Nat.Coprime.coprime_dvd_left h1 (by norm_num)).dvd_of_dvd_mul_right h2
  have hker : Nat.card (π.comp (B.subgroupOf K₁).subtype).ker ≤ Nat.card ↥(B ⊓ Nt) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨(((k : B.subgroupOf K₁) : K₁) : C),
      Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 (k : B.subgroupOf K₁).2, ?_⟩⟩)
      fun a b hab => by
        have e := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext (Subtype.ext e))
    have hk : π ((k : B.subgroupOf K₁) : K₁) = 1 := MonoidHom.mem_ker.1 k.2
    have hk' : ((k : B.subgroupOf K₁) : K₁) ∈ Nt.subgroupOf K₁ := by
      rw [← hπk]
      exact MonoidHom.mem_ker.2 hk
    exact Subgroup.mem_subgroupOf.1 hk'
  have hE : IsElemAbelian 3 ((B.subgroupOf K₁).map π) := (hB.subgroupOf K₁).map π
  have hEle : Nat.card ((B.subgroupOf K₁).map π) ≤ 81 :=
    (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.card_elemAbelian_le_X₀ hE).trans
      (by norm_num)
  have hmul := Subgroup.card_ker_mul_card_range (π.comp (B.subgroupOf K₁).subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv, hc] at hmul
  have hBN3 := Nat.le_of_dvd (by norm_num) hBN
  have hEc : Nat.card ((B.subgroupOf K₁).map π) = 81 := by
    refine le_antisymm hEle ?_
    by_contra hlt
    have := Nat.mul_le_mul (hker.trans hBN3) (Nat.le_of_lt_succ (not_le.1 hlt))
    linarith
  have hk3 : 3 ≤ Nat.card ↥(B ⊓ Nt) := by
    refine le_trans ?_ hker
    by_contra hlt
    have := Nat.mul_le_mul (Nat.le_of_lt_succ (not_le.1 hlt)) hEle
    linarith
  obtain ⟨n₀, hn₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 fun h : B ⊓ Nt = ⊥ => by
    rw [h, Subgroup.card_bot] at hk3
    omega
  have hn₀B := (Subgroup.mem_inf.1 n₀.2).1
  have hn₀N := (Subgroup.mem_inf.1 n₀.2).2
  have hn₀Q : (n₀ : C) ∉ Q := fun h => by
    have h13 : (n₀ : C) ^ 2 ^ 13 = 1 := by
      have := pow_card_eq_one' (G := Q) (x := ⟨(n₀ : C), h⟩)
      rw [hd.card_Q] at this
      simpa using congrArg Subtype.val this
    exact hn₀1 (Subtype.ext ((pow_eq_one_iff_of_coprime (by norm_num : Nat.Coprime 3 (2 ^ 13))).1
      ⟨hB.2 _ hn₀B, h13⟩))
  have hT₁K : T ⊓ K₁ ≤ K₁ := inf_le_right
  have hT₁ : IsPGroup 2 ↥(T ⊓ K₁) := hT.to_le inf_le_left
  have hBT₁ : B ≤ Subgroup.normalizer ((T ⊓ K₁ : Subgroup C) : Set C) :=
    (le_inf hBT (hBK.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hπT : ((T ⊓ K₁).subgroupOf K₁).map π = ⊥ := by
    refine eq_bot_of_elemAbelian81_le_normalizer hE hEc
      ((hT₁.comap_subtype (K := K₁)).map π) ((Subgroup.map_mono ?_).trans
        (Subgroup.le_normalizer_map π))
    rw [← Subgroup.subgroupOf_normalizer_eq hT₁K]
    exact Subgroup.subgroupOf_mono K₁ hBT₁
  have hrel : Q.relIndex Nt = 3 := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := Nt)
    rw [inf_of_le_left hd.Q_le, hd.card_Nt] at h
    exact Nat.eq_of_mul_eq_mul_right hQ0 h
  have hTQ : T ⊓ K₁ ≤ Q := fun x hx => by
    have h1 : π ⟨x, hT₁K hx⟩ = 1 := by
      have h : π ⟨x, hT₁K hx⟩ ∈ ((T ⊓ K₁).subgroupOf K₁).map π :=
        ⟨⟨x, hT₁K hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      rwa [hπT, Subgroup.mem_bot] at h
    have h2 : (⟨x, hT₁K hx⟩ : K₁) ∈ Nt.subgroupOf K₁ := by
      rw [← hπk]
      exact MonoidHom.mem_ker.2 h1
    have h3 : x ^ 3 ∈ Q := by
      have h := Subgroup.pow_relIndex_mem Q (Subgroup.mem_subgroupOf.1 h2)
      rwa [hrel] at h
    obtain ⟨k, hk⟩ := hT₁ ⟨x, hx⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨i, j, hij⟩ := TauCeti.exists_zpow_mul_zpow_eq_of_coprime (G := C)
      (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
    rw [← hij x, hk', one_zpow, mul_one]
    exact Q.zpow_mem h3 i
  have hTK : T ≤ K₁ := by
    intro t ht
    by_contra htK
    have hinv : t⁻¹ ∉ K₁ := fun h => htK (by simpa using K₁.inv_mem h)
    have hcomm : ∀ b ∈ B, ⁅t⁻¹, b⁆ ∈ Q := fun b hb => by
      have hbt : b * t * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hBT hb) t).1 ht
      have hbtK : b * t * b⁻¹ ∉ K₁ := fun h => htK (by
        have h' := K₁.mul_mem (K₁.mul_mem (K₁.inv_mem (hBK hb)) h) (hBK hb)
        rwa [show b⁻¹ * (b * t * b⁻¹) * b = t by group] at h')
      have he : ⁅t⁻¹, b⁆ = t⁻¹ * (b * t * b⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [he]
      exact hTQ (Subgroup.mem_inf.2 ⟨T.mul_mem (T.inv_mem ht) hbt,
        (Subgroup.mul_mem_iff_of_index_two hd.index_K).2 (iff_of_false hinv hbtK)⟩)
    set q := QuotientGroup.mk' Q with hq
    set S := (Subgroup.centralizer ({q t⁻¹} : Set (C ⧸ Q))).comap q ⊓ Nt with hS
    have hmemS : ∀ n ∈ S, ⁅t⁻¹, n⁆ ∈ Q := fun n hn => by
      have h1 : q n * q t⁻¹ = q t⁻¹ * q n :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hn).1)
      have h2 : q ⁅t⁻¹, n⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact h1.symm
      rwa [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have hQS : Q ≤ S := fun x hx => Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.2
      (Subgroup.mem_centralizer_singleton_iff.2 (by
        rw [show q x = 1 from (QuotientGroup.eq_one_iff x).2 hx, one_mul, mul_one])), hd.Q_le hx⟩
    have hn₀S : (n₀ : C) ∈ S := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.2
        (Subgroup.mem_centralizer_singleton_iff.2 ?_), hn₀N⟩
      have h1 : q ⁅t⁻¹, (n₀ : C)⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (hcomm _ hn₀B)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    have hSN : S = Nt := by
      obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hQS
      obtain ⟨l, hl⟩ := Subgroup.card_dvd_of_le (inf_le_right : S ≤ Nt)
      rw [hd.card_Nt, hm] at hl
      have h3 : m * l = 3 := by
        refine Nat.eq_of_mul_eq_mul_left hQ0 ?_
        rw [← mul_assoc, ← hl, mul_comm]
      rcases Nat.prime_three.eq_one_or_self_of_dvd m ⟨l, h3.symm⟩ with rfl | rfl
      · refine absurd ?_ hn₀Q
        rw [Subgroup.eq_of_le_of_card_ge hQS (hm.trans (mul_one _)).le]
        exact hn₀S
      · refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
        rw [hd.card_Nt, hm]
        omega
    obtain ⟨n, hn, hnQ⟩ := hd.noncentral t⁻¹ hinv
    exact hnQ (hmemS n (by rw [hSN]; exact hn))
  exact fun t ht => hTQ (Subgroup.mem_inf.2 ⟨ht, hTK ht⟩)

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
