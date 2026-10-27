module

public import CFSG.ClassicalInvolution.Q3.TL4Thm6Desc
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Exit
public import CFSG.ClassicalInvolution.Q3.TL4MF163L33
public import CFSG.ClassicalInvolution.Q3.TL3TwistStep
public import CFSG.ClassicalInvolution.Q3.TL4E3Norm
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0A
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0B
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint
open scoped commutatorElement

section Lift

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {N : Subgroup Y} [N.Normal]

theorem acts3_of_map (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) (hnt : ∀ y : Y, ∀ n ∈ N, y * t * y⁻¹ = t * n → n = 1)
    (h : TightActs3 (R.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N t)) :
    TightActs3 R t := by
  classical
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  have hCbar := TwistQ.centralizer_mk_eq (N := N) hnt
  obtain ⟨xb, k, hxbC, hxb3, rb, hrb, hxr⟩ := h
  rw [hCbar] at hxbC
  obtain ⟨x, hxC, rfl⟩ := hxbC
  have hxN : x ^ 3 ^ k ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    rw [← map_pow] at hxb3
    exact hxb3
  obtain ⟨n, hnN, hn⟩ : ∃ n ∈ N, n ^ 3 ^ k = (x ^ 3 ^ k)⁻¹ := by
    have hcop : (Nat.card ↥N).Coprime (3 ^ k) := by
      obtain ⟨a, ha⟩ := hN2.exists_card_eq
      rw [ha]
      exact Nat.Coprime.pow _ _ (by norm_num)
    obtain ⟨m, hm⟩ := (powCoprime hcop).surjective ⟨(x ^ 3 ^ k)⁻¹, N.inv_mem hxN⟩
    exact ⟨m, m.2, congrArg Subtype.val hm⟩
  have hnZ : ∀ a : Y, a * n = n * a := Subgroup.mem_center_iff.mp (hNc hnN)
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hNC : N ≤ C := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_center_iff.mp (hNc hm)) t).symm
  set x' := x * n with hx'
  have hx'C : x' ∈ C := C.mul_mem hxC (hNC hnN)
  have hx'3 : x' ^ 3 ^ k = 1 := by
    rw [hx', (show Commute x n from hnZ x).mul_pow, hn, mul_inv_cancel]
  have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hnN
  have hmk : QuotientGroup.mk' N x' = QuotientGroup.mk' N x := by
    rw [hx', map_mul, hn1, mul_one]
  refine ⟨x', k, hx'C, hx'3, ?_⟩
  obtain ⟨r, hr, rfl⟩ := hrb
  refine ⟨r, hr, fun hmem => hxr ?_⟩
  have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hmem
  rwa [TwistQ.oddCoreImg_map hRN, map_commutatorElement, hmk] at h1

end Lift

theorem isQuasisimple_open_of_simple {F : Type} [Group F] [IsSimpleGroup F]
    (hnab : ∃ a b : F, a * b ≠ b * a) : CFSG.Open.IsQuasisimple F := by
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator F) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hc : ⁅a, b⁆ ∈ commutator F :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hab hc
    · exact h
  · have hZ := center_eq_bot_of_isSimpleGroup hnab
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

noncomputable def centerQuotEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem pos_of_lieModel {X : Type} [Group X] {t : Assembly.LowTwoRank.StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (h : LieModel X t 3 p f) : 0 < f := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · exfalso
    rcases ht with rfl | rfl
    · rcases h with ⟨-, -, K, _, _, hK, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · rw [pow_zero] at hK
        exact absurd hK (Finite.one_lt_card (α := K)).ne'
      all_goals exact absurd h0 (by norm_num)
    · rcases h with ⟨-, -, K, _, _, hK, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · rw [pow_zero, one_pow] at hK
        exact absurd hK (Finite.one_lt_card (α := K)).ne'
      all_goals exact absurd h0 (by norm_num)
  · exact hf

variable {G : Type} [Group G] [Finite G] {J L L₀ : Subgroup G}

theorem socleType_of_e3a {n : ℕ} (h6 : Thm6RBelow 3 n) (hG : Nat.card G < n)
    (hc : F2CoreConfig J L L₀) {W : Subgroup G} (hLW : L₀ ≤ W) {R : Subgroup ↥W}
    {S : Sylow 2 R} {t : ↥W} (hd : TightDatum R S t) (hcl : TightCls ↥W R S t)
    (hE2 : ¬ TightInO2 t) (he : TightEdgeless R) (h3 : ¬ TightActs3 R t) :
    SocleType (↥L₀ ⧸ Subgroup.center ↥L₀) := by
  obtain ⟨-, -, -, -, -, hL₀, hn, -, -, -, hC, -⟩ := id hc
  set N := Subgroup.center ↥W with hNdef
  have hNc : N ≤ Subgroup.center ↥W := le_rfl
  have hN2 : IsPGroup 2 ↥N := isPGroup_center hc hLW
  have htN : t ∉ N := fun htZ => hE2 ⟨N, inferInstance, hN2, htZ⟩
  have hnt : ∀ y : ↥W, ∀ m ∈ N, y * t * y⁻¹ = t * m → m = 1 := by
    intro y m hm hy
    by_contra hm1
    exact TightDatum.not_edgeless_of_twin hd hm hm1 hy he
  have hd' := TwistQ.datum hd hN2 htN hnt
  have hc' := TwistQ.cls hd hNc hN2 htN hcl
  have he' := Thm6.edgeless_map hd hNc hN2 htN hnt he
  have hMq := isQuasisimple_subgroupOf hL₀ hLW
  have hCM := centralizer_subgroupOf hC hLW
  have hMn : (L₀.subgroupOf W).Normal := Subgroup.normal_subgroupOf
  set Mb : Subgroup (↥W ⧸ N) := (L₀.subgroupOf W).map (QuotientGroup.mk' N) with hMbdef
  have hMbn : Mb.Normal := hMn.map _ (QuotientGroup.mk'_surjective N)
  have hMbs : IsSimpleGroup ↥Mb := isSimpleGroup_bar hMq hNc hCM
  have hMbnab := exists_ne_comm_bar hMq hNc hCM
  have hMbC := centralizer_bar_eq_bot hMq hNc hCM
  have hF : genFittingFStar (↥W ⧸ N) = Mb := genFittingFStar_eq_of_normal_simple Mb hMbnab hMbC
  have hFs : IsSimpleGroup ↥(genFittingFStar (↥W ⧸ N)) := (MulEquiv.subgroupCongr hF).isSimpleGroup
  have hFnab : ∃ a b : ↥(genFittingFStar (↥W ⧸ N)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hMbnab
    refine ⟨(MulEquiv.subgroupCongr hF).symm a, (MulEquiv.subgroupCongr hF).symm b, fun h => ?_⟩
    exact hab (by simpa using congrArg (MulEquiv.subgroupCongr hF) h)
  have hq : TightFStarQuasisimple (↥W ⧸ N) := isQuasisimple_open_of_simple hFnab
  have hlt : Nat.card (↥W ⧸ N) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective N))
      (lt_of_le_of_lt (Subgroup.card_le_card_group W) hG)
  have hE2' : ¬ TightInO2 (QuotientGroup.mk' N t) := fun h => hE2 (TwistQ.inO2_of hN2 h)
  rcases h6 (↥W ⧸ N) hlt _ _ _ hd' (tightClsR_three_iff.mpr hc') hE2' hq he' with hg | hx
  · exact absurd (acts3_of_good (TwistQ.good_of hd hNc hN2 htN hnt hg)) h3
  let eFS : FStarQuot (↥W ⧸ N) ≃* ↥L₀ ⧸ Subgroup.center ↥L₀ :=
    (Thm6.fstarQuotEquiv hFnab).trans ((MulEquiv.subgroupCongr hF).trans
      ((barEquiv hNc hCM).trans (centerQuotEquiv (Subgroup.subgroupOfEquivOfLe hLW))))
  rcases hx with ⟨p, f, hp, hp2, ⟨hfe, hl, -⟩ | ⟨hl, -⟩⟩ | ⟨hm, -⟩
  · exact Or.inl ⟨p, f, hp, hp2, hfe, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eFS hl⟩
  · have hf : 0 < f := by
      rcases hl with hl | hl
      · exact pos_of_lieModel (Or.inl rfl) hl
      · exact pos_of_lieModel (Or.inr rfl) hl
    by_cases hq3 : p ^ f = 3
    · obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three hq3
      rcases hl with hl | hl
      · exfalso
        obtain ⟨eQ⟩ := GH74.KGroups.L33.equiv_of_lieModel hl
        have hCF : Subgroup.centralizer ((genFittingFStar (↥W ⧸ N) : Subgroup (↥W ⧸ N)) :
            Set (↥W ⧸ N)) = ⊥ := by
          rw [hF]
          exact hMbC
        have := genFittingFStar_normal (↥W ⧸ N)
        exact h3 (acts3_of_map hd hNc hN2 htN hnt (MF163.tightActs3_of_l33 hCF
          ((Thm6.fstarQuotEquiv hFnab).symm.trans eQ) hd' hc'))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eFS hl))))
    · have h5 : 5 ≤ p ^ f := by
        have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
        obtain ⟨k, hk⟩ := hodd
        omega
      rcases hl with hl | hl
      · exact Or.inr (Or.inl ⟨p, f, hp, hp2, h5,
          CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eFS hl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, h5,
          CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eFS hl⟩))
  · obtain ⟨e⟩ := hm
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eFS.symm.trans e⟩))))

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
