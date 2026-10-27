module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.AutAFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.SylowCard

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThLocalIn2.b_mem_closure_odd (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (F : SylowFacts L S B Aa) :
    b ∈ closure {x : G | x ∈ L ⊓ normalizer (A : Set G) ∧ Odd (orderOf x)} := by
  classical
  let Hn : Subgroup G := L ⊓ normalizer (A : Set G)
  let O : Subgroup G := closure {x : G | x ∈ Hn ∧ Odd (orderOf x)}
  change b ∈ O
  obtain ⟨k, c, j, hkL, hkA, hkodd, hkfix, hj, hcmul, hcinj, hconto, hcrep⟩ :=
    exists_singer_coord W.A_comm W.A_sq W.A_card W.surj
  have hkNorm : k ∈ normalizer (A : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 <|
      Subgroup.eq_of_le_of_card_ge
        (by
          rintro _ ⟨y, hy, rfl⟩
          simpa [MulAut.conj_apply] using hkA y hy)
        (by simpa using (Subgroup.card_map_of_injective (K := A)
          (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective).ge)
  have hkHn : k ∈ Hn := ⟨hkL, hkNorm⟩
  have hkO : k ∈ O := Subgroup.subset_closure ⟨hkHn, hkodd⟩
  have hk_not_B : k ∉ B := by
    intro hkB
    have hA_ne_bot : A ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card A = 1 := by
        rw [hbot]
        exact Subgroup.card_bot
      rw [W.A_card] at hcard
      norm_num at hcard
    obtain ⟨a, ha, ha1⟩ := (Subgroup.bot_or_exists_ne_one A).resolve_left hA_ne_bot
    have hka : k * a * k⁻¹ = a := by
      have hc := (W.mem_B_iff k hkL).1 hkB a ha
      calc k * a * k⁻¹ = (a * k) * k⁻¹ := by rw [← hc]
        _ = a := by group
    exact ha1 (hkfix a ha hka)
  have hOconj : ∀ h ∈ Hn, ∀ x ∈ O, h * x * h⁻¹ ∈ O := by
    intro h hh
    refine fun x hx =>
      Subgroup.closure_induction (p := fun y _ => h * y * h⁻¹ ∈ O) ?_ ?_ ?_ ?_ hx
    · intro y hy
      have hmem : h * y * h⁻¹ ∈ Hn := Hn.mul_mem (Hn.mul_mem hh hy.1) (Hn.inv_mem hh)
      have hodd : Odd (orderOf (h * y * h⁻¹)) := by
        have hconj : orderOf (h * y * h⁻¹) = orderOf y := by
          simpa [MulAut.conj_apply] using
            orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective y
        rw [hconj]
        exact hy.2
      exact Subgroup.subset_closure ⟨hmem, hodd⟩
    · simpa using O.one_mem
    · intro y z hy hz hyO hzO
      rw [show h * (y * z) * h⁻¹ = (h * y * h⁻¹) * (h * z * h⁻¹) by group]
      exact O.mul_mem hyO hzO
    · intro y hy hyO
      rw [show h * y⁻¹ * h⁻¹ = (h * y * h⁻¹)⁻¹ by group]
      exact O.inv_mem hyO
  have hOnormal : (O.subgroupOf Hn).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simpa using hOconj (g : G) g.2 (x : G) hx⟩
  have hOleHn : O ≤ Hn := (Subgroup.closure_le Hn).2 fun x hx => hx.1
  have hBleHn : B ≤ Hn := by
    intro x hx
    refine ⟨W.B_le hx, ?_⟩
    exact Subgroup.centralizer_le_normalizer (A : Set G)
      (mem_centralizer_iff.2 fun a ha => ((W.mem_B_iff x (W.B_le hx)).1 hx a ha).symm)
  have hBconj : ∀ h ∈ Hn, ∀ x ∈ B, h * x * h⁻¹ ∈ B := by
    intro h hh x hx
    refine W.conj_mem_B ?_ ?_ x hx
    · intro a ha
      simpa using (Subgroup.mem_normalizer_iff.1 (Hn.inv_mem hh).2 a).1 ha
    · intro y hy
      exact L.mul_mem (L.mul_mem hh.1 (W.B_le hy)) (L.inv_mem hh.1)
  have hAa_le_B : Aa ≤ B := W2.Aa_le
  have hAa_le_Hn : Aa ≤ Hn := le_trans hAa_le_B hBleHn
  have hAa_le_S : Aa ≤ S := fun x hx => W.B_le_S (hAa_le_B hx)
  have hAa_le_O : Aa ≤ O := by
    let φ : ↥Aa → ↥Aa := fun a =>
      ⟨(a : G)⁻¹ * (k * (a : G) * k⁻¹),
        Aa.mul_mem (Aa.inv_mem a.2) (W2.conj_mem_of_mem_L W hkL hkA (a : G) a.2)⟩
    have hφinj : Function.Injective φ := by
      intro a b hab
      have h : (a : G)⁻¹ * (k * (a : G) * k⁻¹) = (b : G)⁻¹ * (k * (b : G) * k⁻¹) := by
        simpa [φ] using congrArg Subtype.val hab
      have h2 : (b : G) * (a : G)⁻¹ * k * (a : G) = k * (b : G) := by
        calc (b : G) * (a : G)⁻¹ * k * (a : G)
            = (b : G) * ((a : G)⁻¹ * (k * (a : G) * k⁻¹)) * k := by group
          _ = (b : G) * ((b : G)⁻¹ * (k * (b : G) * k⁻¹)) * k := by rw [h]
          _ = k * (b : G) := by group
      have hcomm : k * ((b : G) * (a : G)⁻¹) = ((b : G) * (a : G)⁻¹) * k := by
        have h3 : ((b : G) * (a : G)⁻¹) * k = k * (b : G) * (a : G)⁻¹ := by
          calc ((b : G) * (a : G)⁻¹) * k
              = ((b : G) * (a : G)⁻¹) * k * (a : G) * (a : G)⁻¹ := by group
            _ = (k * (b : G)) * (a : G)⁻¹ := by rw [h2]
        rw [h3]
        group
      have hmem : (b : G) * (a : G)⁻¹ ∈ Aa := Aa.mul_mem b.2 (Aa.inv_mem a.2)
      have hfix : k * ((b : G) * (a : G)⁻¹) * k⁻¹ = (b : G) * (a : G)⁻¹ := by
        rw [hcomm]
        group
      have hu : (b : G) * (a : G)⁻¹ = 1 := W2.eq_one_of_fixed W hkfix hmem hfix
      have hb : (b : G) = (a : G) := by
        calc (b : G) = ((b : G) * (a : G)⁻¹) * (a : G) := by group
          _ = 1 * (a : G) := by rw [hu]
          _ = (a : G) := one_mul _
      apply Subtype.ext
      exact hb.symm
    haveI : Fintype ↥Aa := Fintype.ofFinite ↥Aa
    have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
    intro x hx
    obtain ⟨a, ha⟩ := hφsurj ⟨x, hx⟩
    have ha' : (a : G)⁻¹ * (k * (a : G) * k⁻¹) = x := by
      simpa [φ] using congrArg Subtype.val ha
    have haHn : (a : G) ∈ Hn := hBleHn (hAa_le_B a.2)
    have h1 : (a : G)⁻¹ * k * (a : G) ∈ O := by
      have := hOconj (a : G)⁻¹ (Hn.inv_mem haHn) k hkO
      simpa using this
    have h2 : (a : G)⁻¹ * k * (a : G) * k⁻¹ ∈ O := O.mul_mem h1 (O.inv_mem hkO)
    have hxeq : x = (a : G)⁻¹ * k * (a : G) * k⁻¹ := by
      rw [← ha']
      group
    rw [hxeq]
    exact h2
  have hOsupB : O ⊔ B = Hn := by
    have hle : O ⊔ B ≤ Hn := sup_le hOleHn hBleHn
    have hnormal : ∀ h ∈ Hn, ∀ x ∈ O ⊔ B, h * x * h⁻¹ ∈ O ⊔ B := by
      intro h hh x hx
      have hx' : x ∈ Subgroup.closure ((O : Set G) ∪ (B : Set G)) := by
        rwa [← Subgroup.sup_eq_closure]
      refine Subgroup.closure_induction (p := fun y _ => h * y * h⁻¹ ∈ O ⊔ B) ?_ ?_ ?_ ?_ hx'
      · rintro y (hyO | hyB)
        · exact Subgroup.mem_sup_left (hOconj h hh y hyO)
        · exact Subgroup.mem_sup_right (hBconj h hh y hyB)
      · simpa using (O ⊔ B).one_mem
      · intro y z hy hz hyO hzO
        rw [show h * (y * z) * h⁻¹ = (h * y * h⁻¹) * (h * z * h⁻¹) by group]
        exact (O ⊔ B).mul_mem hyO hzO
      · intro y hy hyO
        rw [show h * y⁻¹ * h⁻¹ = (h * y * h⁻¹)⁻¹ by group]
        exact (O ⊔ B).inv_mem hyO
    rcases W.eq_B_or_eq_of_normal hle le_sup_right hnormal with h | h
    · exfalso
      exact hk_not_B (h ▸ Subgroup.mem_sup_left hkO)
    · exact h
  by_contra hbO
  have hBinfO : B ⊓ O = Aa := by
    refine le_antisymm ?_ (le_inf hAa_le_B hAa_le_O)
    intro x hx
    rcases W2.mem_Aa_or_mul_b W hx.1 with h | h
    · exact h
    · exfalso
      have hxbO : x * b ∈ O := hAa_le_O h
      have : b ∈ O := by
        have := O.mul_mem (O.inv_mem hx.2) hxbO
        simpa using this
      exact hbO this
  have hSleHn : S ≤ Hn := by
    intro s hs
    refine ⟨W.S_le hs, ?_⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 <|
      Subgroup.eq_of_le_of_card_ge
        (by
          rintro _ ⟨y, hy, rfl⟩
          simpa [MulAut.conj_apply] using W.conj_mem_A_of_mem_S hs hy)
        (by simpa using (Subgroup.card_map_of_injective (K := A)
          (f := (MulAut.conj s).toMonoidHom) (MulAut.conj s).injective).ge)
  let O' : Subgroup ↥Hn := O.subgroupOf Hn
  let B' : Subgroup ↥Hn := B.subgroupOf Hn
  let S' : Subgroup ↥Hn := S.subgroupOf Hn
  have hO'normal : O'.Normal := hOnormal
  letI : O'.Normal := hO'normal
  have hsup : O' ⊔ B' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hOleHn hBleHn, hOsupB, Subgroup.subgroupOf_self]
  have hrelO' : O'.relIndex B' = O'.index := by
    have h := Subgroup.relIndex_sup_right (H := B') (K := O')
    rw [sup_comm, hsup, Subgroup.relIndex_top_right] at h
    exact h.symm
  have hinf : O' ⊓ B' = Aa.subgroupOf Hn := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨hxO, hxB⟩
      have hmem : (x : G) ∈ B ⊓ O := ⟨hxB, hxO⟩
      rwa [hBinfO] at hmem
    · intro hx
      have hmem : (x : G) ∈ B ⊓ O := hBinfO ▸ hx
      exact ⟨hmem.2, hmem.1⟩
  have hcardB' : Nat.card B' = 2 ^ 9 := by
    rw [show Nat.card B' = Nat.card B from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBleHn).toEquiv, W.B_card]
  have hcardInf : Nat.card ↥(O' ⊓ B') = 2 ^ 8 := by
    rw [hinf]
    rw [show Nat.card (Aa.subgroupOf Hn) = Nat.card Aa from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAa_le_Hn).toEquiv, W2.Aa_card]
  have hOIndex : O'.index = 2 := by
    have h := Subgroup.relIndex_mul_card (H := O') (K := B')
    rw [hcardInf, hcardB', hrelO'] at h
    norm_num at h
    omega
  have hrel_le : O'.relIndex S' ≤ O'.index := by
    have h := Subgroup.relIndex_le_of_le_right (H := O') (K := S') (L := ⊤) le_top
      (by rw [Subgroup.relIndex_top_right, hOIndex]; norm_num)
    simpa [Subgroup.relIndex_top_right] using h
  have hOSle : O.relIndex S ≤ 2 := by
    have h := hrel_le
    rw [show O'.relIndex S' = O.relIndex S from
      Subgroup.relIndex_subgroupOf (H := O) (K := S) hSleHn] at h
    omega
  have hcardSO : 2 ^ 14 ≤ Nat.card ↥(S ⊓ O) := by
    have h := Subgroup.relIndex_mul_card (H := O) (K := S)
    rw [inf_comm, W.card_S] at h
    have hpos : 0 < O.relIndex S := by
      by_contra hzero
      have hzero' : O.relIndex S = 0 := Nat.eq_zero_of_not_pos hzero
      rw [hzero', zero_mul] at h
      omega
    have hr : O.relIndex S = 1 ∨ O.relIndex S = 2 := by omega
    rcases hr with hr | hr <;> rw [hr] at h <;> norm_num at h ⊢ <;> omega
  have hAa_le_SO : Aa ≤ S ⊓ O := le_inf hAa_le_S hAa_le_O
  have hSO_gt : Aa < S ⊓ O := by
    refine lt_of_le_of_ne hAa_le_SO ?_
    intro hEq
    have hc : Nat.card Aa = Nat.card ↥(S ⊓ O) := by rw [hEq]
    rw [W2.Aa_card] at hc
    omega
  obtain ⟨x, hxSO, hxAa⟩ := (SetLike.lt_iff_le_and_exists.mp hSO_gt).2
  have hAaSnormal : (Aa.subgroupOf S).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using W2.conj_mem_of_mem_L W (W.S_le g.2)
      (fun y hy => W.conj_mem_A_of_mem_S g.2 hy) (a : G) ha
  letI : (Aa.subgroupOf S).Normal := hAaSnormal
  let Q : Type := ↥S ⧸ Aa.subgroupOf S
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 Q := W.pgroup.to_quotient (Aa.subgroupOf S)
  haveI : Group.IsNilpotent Q := hQp.isNilpotent
  let q : ↥S →* Q := QuotientGroup.mk' (Aa.subgroupOf S)
  let K : Subgroup ↥S := (S ⊓ O).subgroupOf S
  have hKnormal : K.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    refine ⟨S.mul_mem (S.mul_mem g.2 ha.1) (S.inv_mem g.2), ?_⟩
    simpa using hOconj (g : G) (hSleHn g.2) (a : G) ha.2
  letI : K.Normal := hKnormal
  let Kbar : Subgroup Q := K.map q
  have hKbarNormal : Kbar.Normal := hKnormal.map q (QuotientGroup.mk'_surjective _)
  have hxK : (⟨x, hxSO.1⟩ : ↥S) ∈ K := by
    rw [Subgroup.mem_subgroupOf]
    exact hxSO
  have hxq : q ⟨x, hxSO.1⟩ ∈ Kbar := Subgroup.mem_map.mpr ⟨_, hxK, rfl⟩
  have hKbar_ne_bot : Kbar ≠ ⊥ := by
    intro hbot
    rw [hbot] at hxq
    have hq1 : q ⟨x, hxSO.1⟩ = 1 := Subgroup.mem_bot.mp hxq
    have hxker' : (⟨x, hxSO.1⟩ : ↥S) ∈ (QuotientGroup.mk' (Aa.subgroupOf S)).ker :=
      MonoidHom.mem_ker.mpr hq1
    have hxker : (⟨x, hxSO.1⟩ : ↥S) ∈ Aa.subgroupOf S := by
      rwa [QuotientGroup.ker_mk'] at hxker'
    exact hxAa (Subgroup.mem_subgroupOf.mp hxker)
  haveI : Kbar.Normal := hKbarNormal
  have hcenter : Kbar ⊓ Subgroup.center Q ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hKbar_ne_bot
  rcases Subgroup.bot_or_exists_ne_one (Kbar ⊓ Subgroup.center Q) with hbot | ⟨y, hy, hyne⟩
  · exact absurd hbot hcenter
  · obtain ⟨s, hsK, hqs⟩ := Subgroup.mem_map.mp hy.1
    have hsSO : (s : G) ∈ S ⊓ O := Subgroup.mem_subgroupOf.mp hsK
    have hs_not_Aa : (s : G) ∉ Aa := by
      intro hsAa
      have hsA : s ∈ Aa.subgroupOf S := by
        rw [Subgroup.mem_subgroupOf]
        exact hsAa
      have hq1 : q s = 1 := by
        have hmem : s ∈ (QuotientGroup.mk' (Aa.subgroupOf S)).ker := by
          rwa [QuotientGroup.ker_mk']
        exact MonoidHom.mem_ker.mp hmem
      rw [hqs] at hq1
      exact hyne hq1
    have hcommAa : ∀ u ∈ S, (s : G) * u * (s : G)⁻¹ * u⁻¹ ∈ Aa := by
      intro u hu
      have hct : q ⟨u, hu⟩ * q s = q s * q ⟨u, hu⟩ := by
        have := (Subgroup.mem_center_iff.mp hy.2) (q ⟨u, hu⟩)
        rwa [← hqs] at this
      have hq : q (⟨u, hu⟩ * s) = q (s * ⟨u, hu⟩) := by
        rw [map_mul, map_mul, hct]
      have hker' : (⟨u, hu⟩ * s) * (s * ⟨u, hu⟩)⁻¹ ∈
          (QuotientGroup.mk' (Aa.subgroupOf S)).ker := by
        rw [MonoidHom.mem_ker]
        rw [map_mul, map_inv, hq, mul_inv_cancel]
      have hker : (⟨u, hu⟩ * s) * (s * ⟨u, hu⟩)⁻¹ ∈ Aa.subgroupOf S := by
        rwa [QuotientGroup.ker_mk'] at hker'
      rw [Subgroup.mem_subgroupOf] at hker
      have hg : (((⟨u, hu⟩ * s) * (s * ⟨u, hu⟩)⁻¹ : ↥S) : G) =
          u * (s : G) * u⁻¹ * (s : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hg] at hker
      have hinv : (u * (s : G) * u⁻¹ * (s : G)⁻¹)⁻¹ = (s : G) * u * (s : G)⁻¹ * u⁻¹ := by
        group
      rw [← hinv]
      exact Aa.inv_mem hker
    have hsB : (s : G) ∈ B := F.center_quotient (s : G) hsSO.1 hcommAa
    have hsAa : (s : G) ∈ Aa := by
      have hmem : (s : G) ∈ B ⊓ O := ⟨hsB, hsSO.2⟩
      rwa [hBinfO] at hmem
    exact hs_not_Aa hsAa

end CFSG.EvenSporadicStandard.ThStd
