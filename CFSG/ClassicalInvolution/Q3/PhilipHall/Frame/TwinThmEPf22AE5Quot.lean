module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf22AE5Core

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TC.Thin

namespace TwinThmEW

namespace Ae5Q8

open CFSG.ClassicalInvolution.Q3.AE

section Psi

variable {Yt : Type} [Group Yt] {Λ : Set (Subgroup Yt)}

@[expose] noncomputable def psiY (hgen : pSpan Λ = ⊤) (I : AEIdent Λ 5) : Yt →* AEQ 5 where
  toFun y := I.φ ⟨y, hgen ▸ Subgroup.mem_top y⟩
  map_one' := by
    rw [show (⟨1, hgen ▸ Subgroup.mem_top 1⟩ : ↥(pSpan Λ)) = 1 from rfl, map_one]
  map_mul' := fun a b => by
    rw [show (⟨a * b, hgen ▸ Subgroup.mem_top (a * b)⟩ : ↥(pSpan Λ)) =
      ⟨a, hgen ▸ Subgroup.mem_top a⟩ * ⟨b, hgen ▸ Subgroup.mem_top b⟩ from rfl, map_mul]

theorem psiY_map (hgen : pSpan Λ = ⊤) (I : AEIdent Λ 5) (L : Subgroup Yt) :
    L.map (psiY hgen I) = (L.subgroupOf (pSpan Λ)).map I.φ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hgen ▸ Subgroup.mem_top y⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  · rintro ⟨⟨y, hy'⟩, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩

theorem psiY_range (hgen : pSpan Λ = ⊤) (I : AEIdent Λ 5) :
    (psiY hgen I).range = I.φ.range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩
    exact ⟨y, rfl⟩

theorem psiY_ker_central (hgen : pSpan Λ = ⊤) (I : AEIdent Λ 5) :
    (psiY hgen I).ker ≤ Subgroup.center Yt := by
  intro g hg
  have hg' : (⟨g, hgen ▸ Subgroup.mem_top g⟩ : ↥(pSpan Λ)) ∈ I.φ.ker := hg
  rw [Subgroup.mem_center_iff]
  intro w
  have := Subgroup.mem_center_iff.mp (I.ker_le hg') ⟨w, hgen ▸ Subgroup.mem_top w⟩
  exact congrArg Subtype.val this

theorem oddNormal_le_ker_psiY [Finite Yt] (hgen : pSpan Λ = ⊤) (I : AEIdent Λ 5)
    {N : Subgroup Yt} [N.Normal] (hN : Odd (Nat.card N)) : N ≤ (psiY hgen I).ker := by
  set ψ := psiY hgen I with hψ
  have hrange : ∀ y : Yt, ∃ a : Wr 5, a ∈ aeSub 5 ∧ mkQ 5 a = ψ y := by
    intro y
    have : ψ y ∈ I.φ.range := ⟨_, rfl⟩
    rw [I.range_eq] at this
    exact this
  set ρ : Yt →* Equiv.Perm (Fin 5) := (permQ 5).comp ψ with hρ
  have hρalt : ∀ y, ρ y ∈ alternatingGroup (Fin 5) := by
    intro y
    obtain ⟨a, ha, hay⟩ := hrange y
    rw [Equiv.Perm.mem_alternatingGroup]
    show Equiv.Perm.sign (permQ 5 (ψ y)) = 1
    rw [← hay, permQ_mkQ]
    exact ha.2
  let ρ' : Yt →* ↥(alternatingGroup (Fin 5)) := ρ.codRestrict _ hρalt
  have hρ'surj : Function.Surjective ρ' := by
    rintro ⟨σ, hσ⟩
    have hσ' : Equiv.Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup.mp hσ
    have hmem : mkQ 5 (Wr.ofPerm σ) ∈ I.φ.range := by
      rw [I.range_eq]
      exact ⟨Wr.ofPerm σ, ⟨by unfold Wr.wsum; simp [Wr.ofPerm], hσ'⟩, rfl⟩
    have hmem' : mkQ 5 (Wr.ofPerm σ) ∈ ψ.range := by
      rw [hψ, psiY_range]; exact hmem
    obtain ⟨y, hy⟩ := hmem'
    refine ⟨y, Subtype.ext ?_⟩
    show permQ 5 (ψ y) = σ
    rw [hy, permQ_mkQ]
    rfl
  haveI : (N.map ρ').Normal := Subgroup.Normal.map inferInstance ρ' hρ'surj
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  rcases Subgroup.Normal.eq_bot_or_eq_top (N.map ρ') with hbot | htop
  · intro n hn
    have h1 : ρ' n = 1 := by
      have : ρ' n ∈ N.map ρ' := Subgroup.mem_map_of_mem _ hn
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    have h2 : permQ 5 (ψ n) = 1 := congrArg Subtype.val h1
    have h3 : ψ n * ψ n = 1 := mul_self_of_mem_ker_permQ (MonoidHom.mem_ker.mpr h2)
    have h4 : orderOf (ψ n) ∣ orderOf n := orderOf_map_dvd ψ n
    have h5 : orderOf n ∣ Nat.card N := by
      have := Subgroup.orderOf_dvd_natCard N hn
      simpa using this
    have h6 : orderOf (ψ n) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
    have h7 : Odd (orderOf (ψ n)) := (hN.of_dvd_nat (h4.trans h5))
    have h8 : orderOf (ψ n) = 1 := by
      have := Nat.le_of_dvd (by norm_num) h6
      rcases h7 with ⟨k, hk⟩
      have : orderOf (ψ n) ≠ 0 := by omega
      omega
    exact MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h8)
  · exfalso
    have hcard : Nat.card (N.map ρ') ∣ Nat.card N := Subgroup.card_map_dvd N ρ'
    rw [htop, Subgroup.card_top] at hcard
    have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    rw [h60] at hcard
    have := hN.of_dvd_nat hcard
    exact absurd this (by decide)

end Psi

section Quot

variable {Yt : Type} [Group Yt] {Λ : Set (Subgroup Yt)}

theorem map_subgroupOf_comp {G H : Type*} [Group G] [Group H] (S : Subgroup G) (f : G →* H)
    {L : Subgroup G} (hL : L ≤ S) : (L.subgroupOf S).map (f.comp S.subtype) = L.map f := by
  rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hL]

theorem aeIdentQuot_map (hgen : pSpan Λ = ⊤) (I : AEIdent Λ 5) (N : Subgroup Yt) [N.Normal]
    (hN : N ≤ (psiY hgen I).ker) {L₀ : Subgroup Yt} (hL₀ : L₀ ∈ Λ) :
    ((L₀.map (QuotientGroup.mk' N)).subgroupOf (pSpan (quotFamily Λ N))).map
      ((QuotientGroup.lift N (psiY hgen I) hN).comp (pSpan (quotFamily Λ N)).subtype) =
      L₀.map (psiY hgen I) := by
  rw [map_subgroupOf_comp _ _ (le_pSpan (map_mem_quotFamily (N := N) hL₀)), Subgroup.map_map]
  rfl

@[expose] noncomputable def aeIdentQuot (hgen : pSpan Λ = ⊤) (I : AEIdent Λ 5) (N : Subgroup Yt)
    [N.Normal] (hN : N ≤ (psiY hgen I).ker) (hgenΦ : pSpan (quotFamily Λ N) = ⊤) :
    AEIdent (quotFamily Λ N) 5 where
  φ := (QuotientGroup.lift N (psiY hgen I) hN).comp (pSpan (quotFamily Λ N)).subtype
  range_eq := by
    have h1 : ((QuotientGroup.lift N (psiY hgen I) hN).comp
        (pSpan (quotFamily Λ N)).subtype).range = (QuotientGroup.lift N (psiY hgen I) hN).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hgenΦ, ← MonoidHom.range_eq_map]
    rw [h1, ← I.range_eq, ← psiY_range hgen I]
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨(y : Yt ⧸ N), rfl⟩
  ker_le := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (x : Yt ⧸ N)
    have hxk : (psiY hgen I) y = 1 := by
      have : (QuotientGroup.lift N (psiY hgen I) hN) (x : Yt ⧸ N) = 1 := hx
      rw [← hy] at this
      simpa using this
    have hyc : y ∈ Subgroup.center Yt := psiY_ker_central hgen I hxk
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (w : Yt ⧸ N)
    apply Subtype.ext
    show (w : Yt ⧸ N) * (x : Yt ⧸ N) = (x : Yt ⧸ N) * (w : Yt ⧸ N)
    rw [← hy, ← hu, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp hyc u
  label := by
    rintro _ ⟨L₀, hL₀, rfl⟩
    obtain ⟨α, h, b, hl⟩ := I.label L₀ hL₀
    exact ⟨α, h, b, (aeIdentQuot_map hgen I N hN hL₀).trans ((psiY_map hgen I L₀).trans hl)⟩
  label_surj := by
    intro α h b
    obtain ⟨L₀, hL₀, hl⟩ := I.label_surj α h b
    exact ⟨L₀.map (QuotientGroup.mk' N), map_mem_quotFamily hL₀,
      (aeIdentQuot_map hgen I N hN hL₀).trans ((psiY_map hgen I L₀).trans hl)⟩

end Quot

section Main

theorem eq_one_of_odd_orderOf {G : Type*} [Group G] {x : G} (h2 : x * x = 1)
    (hodd : Odd (orderOf x)) : x = 1 := by
  have h6 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp h6 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

variable {Yt : Type} [Group Yt] [Finite Yt] {Λ : Set (Subgroup Yt)}

theorem inj_map_mk (hΛ : HypOmegaGen Λ)
    (hq8 : ∀ L ∈ Λ, ∃ P : Subgroup Yt, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    {N : Subgroup Yt} [N.Normal] (hNc : N ≤ Subgroup.center Yt) (hNodd : Odd (Nat.card N))
    {L M : Subgroup Yt} (hL : L ∈ Λ) (hM : M ∈ Λ)
    (h : L.map (QuotientGroup.mk' N) = M.map (QuotientGroup.mk' N)) : L = M := by
  by_contra hLM
  obtain ⟨P, hP, ⟨e⟩⟩ := hq8 L hL
  have hP8 : Nat.card P = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hPM : P ≤ M := by
    intro x hx
    have hxL : x ∈ L := hP.1 hx
    have hmem : QuotientGroup.mk' N x ∈ M.map (QuotientGroup.mk' N) := h ▸ ⟨x, hxL, rfl⟩
    obtain ⟨m, hmM, hmx⟩ := hmem
    have hn : x⁻¹ * m ∈ N := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      show QuotientGroup.mk' N (x⁻¹ * m) = 1
      rw [map_mul, map_inv, hmx, inv_mul_cancel]
    obtain ⟨n, hnN, hmn⟩ : ∃ n ∈ N, m = x * n := ⟨x⁻¹ * m, hn, by group⟩
    have hcomm : Commute x n := Subgroup.mem_center_iff.mp (hNc hnN) x
    have hnd : n ^ Nat.card N = 1 := by
      have h' := congrArg Subtype.val (pow_card_eq_one' (G := N) (x := ⟨n, hnN⟩))
      rw [Subgroup.coe_pow] at h'
      exact h'
    have hmd : m ^ Nat.card N = x ^ Nat.card N := by
      rw [hmn, hcomm.mul_pow, hnd, mul_one]
    have hxdM : x ^ Nat.card N ∈ M := hmd ▸ M.pow_mem hmM _
    obtain ⟨j, hj⟩ := hP.2.1 ⟨x, hx⟩
    have hxj : x ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    have hcop : Nat.Coprime (Nat.card N) (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hNodd)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hx_eq : x = (x ^ Nat.card N) ^ a := by
      have h1 : x ^ (a * (Nat.card N : ℤ) + b * ((2 ^ j : ℕ) : ℤ)) = x := by rw [hab, zpow_one]
      rw [zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hxj,
        one_zpow, mul_one] at h1
      exact h1.symm
    rw [hx_eq]
    exact M.zpow_mem hxdM a
  have hPLM : P ≤ L ⊓ M := le_inf hP.1 hPM
  have hdvd : 8 ∣ Nat.card ↥(L ⊓ M) := hP8 ▸ Subgroup.card_dvd_of_le hPLM
  have h3 : 3 ≤ padicValNat 2 (Nat.card ↥(L ⊓ M)) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (by simpa using hdvd)
  have h4 := (hΛ.omega4 L hL M hM hLM).1
  omega

theorem ae5_sect_main (hΛ : HypOmegaGen Λ)
    (hΛ2 : ∀ L ∈ Λ, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hΛq8 : ∀ L ∈ Λ, ∃ P : Subgroup Yt, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (hΛA : ∀ L ∈ Λ, AEmpty Λ L) (hgen : pSpan Λ = ⊤) (I : AEIdent Λ 5)
    {K K' : Subgroup Yt} (hK : K ∈ Λ) (hK' : K' ∈ Λ) (hne : K' ≠ K) {z : Yt}
    (hzK : IsUniqueInvolution K z) (hzK' : IsUniqueInvolution K' z)
    {J : Subgroup Yt} (hJ : J ∈ Λ) {t : Yt} (htJ : IsUniqueInvolution J t)
    (hzt : z * t ≠ 1) (hztc : z * t = t * z) (P : Sylow 2 Yt) :
    ∃ s ∈ (P : Subgroup Yt), conjSub s K = K' ∧
      ∀ x₀ ∈ K, x₀ * x₀ = z → ∃ g n : Yt, n ∈ Subgroup.center Yt ∧ Odd (orderOf n) ∧
        g * (z * t) * g⁻¹ = x₀ * (s * x₀ * s⁻¹) * n := by
  classical
  set N : Subgroup Yt := classicalInvolutionOddCore Yt with hNdef
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card Yt
  have hNker : N ≤ (psiY hgen I).ker := oddNormal_le_ker_psiY hgen I hNodd
  have hNc : N ≤ Subgroup.center Yt := hNker.trans (psiY_ker_central hgen I)
  have hΦ : HypOmegaGen (quotFamily Λ N) := TwinEdge.hypOmegaGen_quotFamily_odd hΛ hNodd
  have hgenΦ : pSpan (quotFamily Λ N) = ⊤ := by
    have hgen' : (⨆ L ∈ Λ, L) = ⊤ := hgen
    have h1 : (⨆ L ∈ Λ, L).map (QuotientGroup.mk' N) = ⨆ L ∈ Λ, L.map (QuotientGroup.mk' N) := by
      rw [Subgroup.map_iSup]
      congr 1
      funext L
      rw [Subgroup.map_iSup]
    have h2 : (⊤ : Subgroup Yt).map (QuotientGroup.mk' N) = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)
    apply top_le_iff.mp
    rw [← h2, ← hgen', h1]
    exact iSup₂_le fun L hL => le_iSup₂ (f := fun L' (_ : L' ∈ quotFamily Λ N) => L')
      (L.map (QuotientGroup.mk' N)) (map_mem_quotFamily hL)
  have hS : TwinDisc.Q8Section (Yt ⧸ N) (quotFamily Λ N) :=
    ⟨hΦ, TwinThmE.two_quot_odd hΛ2 hNodd,
      fun J hJ => TwinDisc.forall_sylow_iso_of_exists (TwinThmE.q8_quot_odd hNodd hΛq8 J hJ),
      CFSG.ComponentClassification.OddCore.quotient_corefree Yt,
      TwinThmE.aEmpty_quot_odd hΛ hNodd hΛA, hgenΦ⟩
  let I' : AEIdent (quotFamily Λ N) 5 := aeIdentQuot hgen I N hNker hgenΦ
  have hz' := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hNodd K) hzK
  have hz'' := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hNodd K') hzK'
  have ht' := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hNodd J) htJ
  have hne' : K'.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) := fun h =>
    hne (inj_map_mk hΛ hΛq8 hNc hNodd hK' hK h)
  have hzt' : QuotientGroup.mk' N z * QuotientGroup.mk' N t ≠ 1 := by
    intro h
    rw [← map_mul] at h
    have hmem : z * t ∈ N := (QuotientGroup.eq_one_iff _).mp h
    have hsq : (z * t) * (z * t) = 1 := by
      calc (z * t) * (z * t) = z * (t * z) * t := by group
        _ = z * (z * t) * t := by rw [← hztc]
        _ = (z * z) * (t * t) := by group
        _ = 1 := by rw [hzK.sq, htJ.sq, one_mul]
    have h3 : orderOf (z * t) ∣ Nat.card N := by
      simpa using Subgroup.orderOf_dvd_natCard N hmem
    exact hzt (eq_one_of_odd_orderOf hsq (hNodd.of_dvd_nat h3))
  obtain ⟨ŝ, hŝP, hŝK, hŝ⟩ := ae5_core hS I' (map_mem_quotFamily hK) (map_mem_quotFamily hK') hne'
    hz' hz'' (map_mem_quotFamily hJ) ht' hzt' (Sylow.mapSurjective (QuotientGroup.mk'_surjective N) P)
  rw [Sylow.coe_mapSurjective] at hŝP
  obtain ⟨s, hsP, rfl⟩ := hŝP
  refine ⟨s, hsP, ?_, ?_⟩
  · refine inj_map_mk hΛ hΛq8 hNc hNodd (hΛ.conjInvariant s K hK) hK' ?_
    rw [AscQuot.map_conjSub]
    exact hŝK
  · intro x₀ hx₀K hx₀sq
    obtain ⟨g', hg'⟩ := hŝ (QuotientGroup.mk' N x₀) (Subgroup.mem_map_of_mem _ hx₀K)
      (by rw [← map_mul, hx₀sq])
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g'
    have hmk : QuotientGroup.mk' N (x₀ * (s * x₀ * s⁻¹)) = QuotientGroup.mk' N (g * (z * t) * g⁻¹) := by
      simp only [map_mul, map_inv]
      exact hg'.symm
    have hnN : (x₀ * (s * x₀ * s⁻¹))⁻¹ * (g * (z * t) * g⁻¹) ∈ N := QuotientGroup.eq.mp hmk
    refine ⟨g, (x₀ * (s * x₀ * s⁻¹))⁻¹ * (g * (z * t) * g⁻¹), hNc hnN, ?_, by group⟩
    exact hNodd.of_dvd_nat (by simpa using Subgroup.orderOf_dvd_natCard N hnN)

end Main

end Ae5Q8

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
