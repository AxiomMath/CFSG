module

public import CFSG.LargeExtraspecial.S14C8Cases
public import CFSG.LargeExtraspecial.S14C8Mod
public import CFSG.LargeExtraspecial.S14W4SetNQ
public import CFSG.LargeExtraspecial.S14C8Norm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem false_of_comm (hCorB : S8.TimmesfeldCorBInput) (hFacts : S8.CorBListFacts)
    (hCE : CentralExtInput.{0}) {t : S.O} (hSt : Stage S g t)
    (hΩ : ∃ d, 6 ≤ d ∧ RNOmega S g t d) (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (h7 : Concl14_7 S g t)
    (hτ : ∀ τ ∈ S8.conjCentM S t, ∀ n ∈ Nbar S g t, n * τ * n⁻¹ * τ⁻¹ ∈ zpowers t) : False := by
  obtain ⟨d, hd, H, C, ht, ht1, hVQ, hΩ, hdim⟩ := hΩ
  have haQ := H.conj_mem
  have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
  have htN : t ∈ Nbar S g t := S6.self_mem_Nbar H ht
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have htc : ∀ y ∈ Nbar S g t, y * t = t * y := fun y hy =>
    commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)
  obtain ⟨hs, hnab⟩ := (S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ (by omega)
  have hin : S8.conjCentM S t ⊆ Nbar S g t := by
    intro τ hτm
    obtain ⟨hτM, -⟩ := id hτm
    refine h7.1 τ hτM fun y hy => ?_
    have e : τ * y * τ⁻¹ * y⁻¹ = (y * τ * y⁻¹ * τ⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (hτ τ hτm y hy)
  have h2 : ∀ τ ∈ S8.conjCentM S t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t := by
    intro τ hτm hne
    have hτN := hin hτm
    obtain ⟨-, hτt, x, -, hx⟩ := hτm
    have hτ1 : τ ≠ 1 := fun h => ht1 (by
      rw [hx] at h
      calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group)
    by_cases hc : ∀ n ∈ Nbar S g t, n * τ = τ * n
    · exfalso
      have htc' : (⟨t, htN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
        rw [mem_center_iff]
        intro v
        exact Subtype.ext (htc v v.2)
      have hτc : (⟨τ, hτN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
        rw [mem_center_iff]
        intro v
        exact Subtype.ext (hc v v.2)
      exact hne (congrArg Subtype.val (CFSG.RankThree.Literature.FSmith.eq_of_mem_center hext
        hτc htc' (fun h => hτ1 (congrArg Subtype.val h)) (fun h => ht1 (congrArg Subtype.val h))))
    · push Not at hc
      obtain ⟨n, hn, hnτ⟩ := hc
      have hcm := comm_mem_zpowers_of_extraspecial hext htN ht1 htc hn hτN
      rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hcm with h | h
      · exact absurd (by calc n * τ = (n * τ * n⁻¹ * τ⁻¹) * τ * n := by group
          _ = τ * n := by rw [h, one_mul]) hnτ
      · refine ⟨n, Rbar_le_Mbar (Nbar_le_Rbar hn), ?_⟩
        calc n * τ * n⁻¹ = (n * τ * n⁻¹ * τ⁻¹) * τ := by group
          _ = τ * t := by rw [h, hτt]
  have hle := S8.Nbar_le_zpowers_of_corB_of_subset hCorB hFacts hCE
    (irr_of_not_isReducible hSt.irr) H hNo C (by have := hSt.six_le_width; omega) ht ht1 hext.1
    le_rfl hs hnab hin hτ h2
  obtain ⟨a, ha, b, hb, hab⟩ := exists_comm_eq_of_extraspecial hext htN ht1 fun y hy =>
    (htc y hy).symm
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hle ha)
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hle hb)
  apply ht1
  rw [← hab, (Commute.zpow_zpow_self t i j).eq]
  group

theorem comm_mem_of_conjCent (hirr : NQIrredStmt) (h6 : NQPlus6Stmt) [IsSimpleGroup G]
    {t : S.O} {c : Config} (hSt : Stage S g t) (hocc : c.Occurs S g t)
    (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (hc : c = .omegaMinus6 ∨ c = .omegaPlus8a ∨ c = .omegaPlus6)
    (hK : Rbar S g t ⊓ (Mbar0 S).map S.Mbar.subtype ≤ Nbar S g t)
    (htM0 : t ∈ (Mbar0 S).map S.Mbar.subtype) :
    ∀ τ ∈ S8.conjCentM S t, ∀ n ∈ Nbar S g t, n * τ * n⁻¹ * τ⁻¹ ∈ zpowers t := by
  rintro τ ⟨hτM, hτt, x, hxM, hx⟩ n hn
  have haQ := hSt.hyp4.conj_mem
  have htN : t ∈ Nbar S g t := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ hSt.mem
  have htc : ∀ y ∈ Nbar S g t, y * t = t * y := fun y hy =>
    commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)
  have hτCt : τ ∈ Ct S t := ⟨hτM, mem_centralizer_singleton_iff.mpr hτt⟩
  have hτM0 : τ ∈ (Mbar0 S).map S.Mbar.subtype := hx ▸ conj_mem_Mbar0 hxM htM0
  have hs : InvolSetup (Nbar S g t) (Rbar S g t) t τ :=
    { t_mem := htN
      t_comm := htc
      comm_mem := fun a ha b hb =>
        comm_mem_zpowers_of_extraspecial hext htN hSt.ne_one htc ha hb
      sq_mem := fun a ha => sq_mem_zpowers_of_extraspecial hext htN hSt.ne_one htc ha
      conj_R := fun r hr m hm => conj_mem_Nbar_of_mem_Rbar haQ hr hm
      R_comm := fun r hr => commute_of_mem_Rbar haQ hr
      conj_τ := fun m hm => conj_mem_Nbar_of_mem_Ct haQ hτCt hm
      τ_comm := hτt
      τ_sq := by
        rw [hx]
        calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
          _ = 1 := by rw [htt]; group
      comm_τ := fun r hr => hK (Subgroup.mem_inf.mpr ⟨by
          have e : r * τ * r⁻¹ * τ⁻¹ = r * (τ * r⁻¹ * τ⁻¹) := by group
          rw [e]
          exact mul_mem hr (conj_Rbar_of_mem_Ct hτCt (inv_mem hr)),
        mul_mem (conj_mem_Mbar0 (Rbar_le_Mbar hr) hτM0) (inv_mem hτM0)⟩) }
  rcases hc with rfl | rfl | rfl
  · exact hs.comm_mem_of_irred (hirr G S g t _ hSt hocc hext (by intro h; cases h)
      (by intro h; cases h)) hn
  · exact hs.comm_mem_of_irred (hirr G S g t _ hSt hocc hext (by intro h; cases h)
      (by intro h; cases h)) hn
  · obtain ⟨U₁, U₂, h1t, h1N, h2t, h2N, h1R, h2R, hinf, hc1, hc2, hlat⟩ := h6 G S g t hSt hocc hext
    have hct : Nat.card (zpowers t) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact htt) hSt.ne_one
    have hcN : Nat.card (Nbar S g t) ≠ 2 ^ 5 := by
      rw [hocc.2.2]
      show 2 ^ 9 ≠ 2 ^ 5
      norm_num
    exact hs.comm_mem_of_two h1t h1N h2t h2N h1R h2R hinf hc1 hc2 hct hcN hlat hn

theorem claim14_8_of (hCorB : S8.TimmesfeldCorBInput) (hFacts : S8.CorBListFacts)
    (hCE : CentralExtInput.{0}) (h83 : S8_3Stmt) (hirr : NQIrredStmt) (h6 : NQPlus6Stmt) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O)
      (c : Config), Stage S g t → c.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
        IsSimpleGroup (Mbar0 S) → Concl14_7 S g t → Rbar S g t ≤ (Mbar0 S).map S.Mbar.subtype := by
  intro G _ _ _ S g t c hSt hocc hext hsim h7
  have haQ := hSt.hyp4.conj_mem
  have hRp := rbarPerfectStmt_of hCE G S g t c hSt hocc hext
  by_contra hR
  have hK : Rbar S g t ⊓ (Mbar0 S).map S.Mbar.subtype ≤ Nbar S g t := by
    rcases le_Nbar_or_le_of_normal (K := Rbar S g t ⊓ (Mbar0 S).map S.Mbar.subtype) haQ
        (isSimpleGroup_RmodN_of_occurs hocc) hRp hext.1 inf_le_left
        (fun r hr k hk => Subgroup.mem_inf.mpr
          ⟨mul_mem (mul_mem hr (Subgroup.mem_inf.mp hk).1) (inv_mem hr),
            conj_mem_Mbar0 (Rbar_le_Mbar hr) (Subgroup.mem_inf.mp hk).2⟩) with h | h
    · exact h
    · exact absurd (h.trans inf_le_right) hR
  have htM0 := mem_Mbar0_of_le_Nbar hSt hRp hext hsim h7 hK
  have hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t := fun x hx hL =>
    hK (Subgroup.mem_inf.mpr ⟨Lbar_le_Rbar hSt.mem hL, conj_mem_Mbar0 hx htM0⟩)
  have hc := config_of_sub hCorB hFacts hCE h83 hSt hocc hsub
  have hΩ : ∃ d, 6 ≤ d ∧ RNOmega S g t d := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨6, le_rfl, hocc.1.1⟩
    · exact ⟨8, by norm_num, hocc.1.1⟩
    · exact ⟨6, le_rfl, hocc.1.1⟩
  exact false_of_comm hCorB hFacts hCE hSt hΩ hext h7
    (comm_mem_of_conjCent hirr h6 hSt hocc hext hc hK htM0)

end CFSG.LargeExtraspecial.S14
