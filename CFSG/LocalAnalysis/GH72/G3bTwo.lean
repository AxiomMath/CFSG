module

public import CFSG.LocalAnalysis.GH72.G3bFour
public import CFSG.LocalAnalysis.GH72.G3bSix
public import CFSG.LocalAnalysis.GH72.G3aThreeFinal

public section

namespace CFSG.GH72

open Subgroup
open CFSG.CGT.Foote81L6.TStruct (IsFourIn)

theorem isKleinFour_of_isDih_of_three_pow_mem_normalizer {G : Type*} [Group G]
    {D : Subgroup G} (hD : IsDih D) {u : G}
    (huN : u ∈ normalizer (D : Set G)) (hord : ∃ n : ℕ, orderOf u = 3 ^ n)
    (huC : u ∉ centralizer (D : Set G)) : IsKleinFour D := by
  classical
  rcases hD.isKleinFour_or_isDihNonab with hK | hN
  · exact hK
  · exfalso
    obtain ⟨k, hk2, ⟨e⟩⟩ := hN
    have hAut : IsPGroup 2 (MulAut ↥D) :=
      (CFSG.GorensteinWalter.dihedral_mulAut_is_twoGroup hk2).of_equiv
        (MulAut.congr e).symm
    let σ : MulAut ↥D := D.normalizerMonoidHom ⟨u, huN⟩
    obtain ⟨n, hn⟩ := hord
    have hdvd3 : orderOf σ ∣ 3 ^ n := by
      rw [← hn]
      have h := orderOf_map_dvd D.normalizerMonoidHom ⟨u, huN⟩
      rwa [Subgroup.orderOf_mk] at h
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hAut σ
    have hj0 : j = 0 := by
      by_contra hj0
      have h2dvd : 2 ∣ 2 ^ j := dvd_pow_self 2 hj0
      have h23 : 2 ∣ 3 ^ n := by
        rw [hj] at hdvd3
        exact h2dvd.trans hdvd3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h23) (by norm_num)
    have hσ1 : orderOf σ = 1 := by rw [hj, hj0, pow_zero]
    exact huC ((CFSG.GH72.normalizerMonoidHom_eq_one_iff huN).mp
      (orderOf_eq_one_iff.mp hσ1))

theorem isConj_of_isKleinFour_of_three_pow_mem_normalizer {G : Type*} [Group G]
    {D : Subgroup G} (hD : IsKleinFour D) {u : G}
    (huN : u ∈ normalizer (D : Set G)) (hord : ∃ n : ℕ, orderOf u = 3 ^ n)
    (huC : u ∉ centralizer (D : Set G)) :
    ∀ x ∈ D, ∀ y ∈ D, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  classical
  let σ : MulAut ↥D := D.normalizerMonoidHom ⟨u, huN⟩
  have hσne : σ ≠ 1 := by
    intro h
    exact huC ((CFSG.GH72.normalizerMonoidHom_eq_one_iff huN).mp h)
  obtain ⟨n, hn⟩ := hord
  have hσodd : Odd (orderOf σ) := by
    have hdvd : orderOf σ ∣ 3 ^ n := by
      rw [← hn]
      have h := orderOf_map_dvd D.normalizerMonoidHom ⟨u, huN⟩
      rwa [Subgroup.orderOf_mk] at h
    exact (show Odd (3 : ℕ) by decide).pow |>.of_dvd_nat hdvd
  have hσ2ne : σ ^ 2 ≠ 1 := by
    intro h
    have hdvd2 : orderOf σ ∣ 2 := (orderOf_dvd_iff_pow_eq_one (x := σ) (n := 2)).mpr h
    have h1 : orderOf σ = 1 :=
      Nat.eq_one_of_dvd_coprimes hσodd.coprime_two_right dvd_rfl hdvd2
    exact hσne (orderOf_eq_one_iff.mp h1)
  have hfix : ∀ z : ↥D, z ≠ 1 → σ z ≠ z := by
    intro z hz1 hzfix
    exact hσne (kleinFour_mulAut_eq_one_of_odd σ hz1 hzfix hσodd)
  have hfix2 : ∀ z : ↥D, z ≠ 1 → (σ ^ 2) z ≠ z := by
    intro z hz1 hzfix
    have hσ2odd : Odd (orderOf (σ ^ 2)) :=
      hσodd.of_dvd_nat (orderOf_pow_dvd (x := σ) 2)
    exact hσ2ne (kleinFour_mulAut_eq_one_of_odd (σ ^ 2) hz1 hzfix hσ2odd)
  intro x hx y hy hx2 hy2
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    omega
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy2
    omega
  let sx : ↥D := ⟨x, hx⟩
  have hsx1 : sx ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hσx_ne : σ sx ≠ sx := hfix sx hsx1
  have hσ2x_ne : (σ ^ 2) sx ≠ sx := hfix2 sx hsx1
  have hσx_ne1 : σ sx ≠ 1 := by
    intro h
    have h1 : sx = 1 := by
      have := congrArg (fun t : ↥D => (σ⁻¹) t) h
      simpa [MulAut.inv_apply] using this
    exact hsx1 h1
  have hσ2x_ne1 : (σ ^ 2) sx ≠ 1 := by
    intro h
    have h1 : sx = 1 := by
      have := congrArg (fun t : ↥D => ((σ ^ 2)⁻¹) t) h
      simpa [MulAut.inv_apply] using this
    exact hsx1 h1
  have hσ2x_ne_σx : (σ ^ 2) sx ≠ σ sx := by
    intro h
    have h1 : σ sx = sx := by
      have := congrArg (fun t => (σ⁻¹) t) h
      simpa [pow_two, MulAut.mul_apply] using this
    exact hσx_ne h1
  have hmul : x * ((σ sx : ↥D) : G) = (((σ ^ 2) sx : ↥D) : G) := by
    rcases mem_kleinFour_cases hD hx (σ sx).2 hx1 (by
        intro h; exact hσx_ne1 (Subtype.ext h)) (by
        intro h; exact hσx_ne (Subtype.ext h.symm))
      ((σ ^ 2) sx).2 with h | h | h | h
    · exact absurd (Subtype.ext h) hσ2x_ne1
    · exact absurd (Subtype.ext h) hσ2x_ne
    · exact absurd (Subtype.ext h) hσ2x_ne_σx
    · exact h.symm
  have hcover : ∀ z ∈ D, z ≠ 1 → z = x ∨ z = ((σ sx : ↥D) : G) ∨ z = (((σ ^ 2) sx : ↥D) : G) := by
    intro z hz hz1
    rcases mem_kleinFour_cases hD hx (σ sx).2 hx1 (by
        intro h; exact hσx_ne1 (Subtype.ext h)) (by
        intro h; exact hσx_ne (Subtype.ext h.symm)) hz with h | h | h | h
    · exact absurd h hz1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (h.trans hmul))
  have step : ∀ z : ↥D, IsConj ((z : ↥D) : G) (((σ z : ↥D) : G)) := by
    intro z
    exact isConj_iff.mpr ⟨u, rfl⟩
  rcases hcover y hy hy1 with h | h | h
  · rw [h]
  · rw [h]
    exact step sx
  · rw [h]
    exact (step sx).trans (by
      have hσ2 : σ (σ sx) = (σ ^ 2) sx := by simp [pow_two, MulAut.mul_apply]
      rw [← hσ2]
      exact step (σ sx))

theorem exists_central_involution_sq_mul_self {G : Type*} [Group G]
    {D : Subgroup G} (hD : IsDihNonab D) :
    ∃ z ∈ D, orderOf z = 2 ∧ D ⊓ centralizer (D : Set G) = zpowers z ∧
      ∃ b ∈ D, b * b = z := by
  classical
  obtain ⟨z, hzD, hzord, hZ⟩ := hD.exists_inf_centralizer_self_eq
  obtain ⟨k, hk2, ⟨e⟩⟩ := hD
  have hk1 : 1 ≤ k := by omega
  have hzc_mem : ((e.symm (CFSG.CGT.Foote81L6.zc k) : ↥D) : G) ∈
      D ⊓ centralizer (D : Set G) := by
    refine mem_inf.mpr ⟨(e.symm (CFSG.CGT.Foote81L6.zc k)).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcomm :=
      Subgroup.mem_center_iff.mp (dih_symm_zc_mem_center e hk1) (⟨y, hy⟩ : ↥D)
    exact congrArg Subtype.val hcomm
  rw [hZ] at hzc_mem
  have hzc_ne1 : ((e.symm (CFSG.CGT.Foote81L6.zc k) : ↥D) : G) ≠ 1 := by
    intro h
    exact dih_symm_zc_ne_one e hk1 (Subtype.ext h)
  have heq : ((e.symm (CFSG.CGT.Foote81L6.zc k) : ↥D) : G) = z := by
    rcases (CFSG.Timmesfeld.Bridge.mem_zpowers_iff_of_orderOf_eq_two hzord).mp hzc_mem with
      h | h
    · exact absurd h hzc_ne1
    · exact h
  obtain ⟨b, hb⟩ := CFSG.GH72.dih_exists_mul_self_eq_symm_zc e hk2
  refine ⟨z, hzD, hzord, hZ, (b : G), b.2, ?_⟩
  have hb' : ((b : ↥D) : G) * ((b : ↥D) : G) =
      ((e.symm (CFSG.CGT.Foote81L6.zc k) : ↥D) : G) := by
    have h := congrArg Subtype.val hb
    simpa using h
  rw [hb', heq]

namespace Sec3Setting

variable {G : Type*} [Group G] [Finite G]

theorem prop_3_2_of_h34 (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁)
    (h₃ : ∃ S₁' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' 𝔖.S₂ ∧
      ∃ n : ℕ, ∃ u ∈ normalizer ((𝔖.S : Subgroup G) : Set G), orderOf u = 3 ^ n ∧
        u ∈ normalizer (S₁' : Set G) ∧ u ∉ centralizer (S₁' : Set G)) :
    ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧ HasProductFusion S₁' S₂' := by
  classical
  obtain ⟨S₁', hdd', n, u, huN, huord, huNW, huCW⟩ := h₃
  have h₁' : IsKleinFour ↥S₁' :=
    isKleinFour_of_isDih_of_three_pow_mem_normalizer hdd'.dih₁ huNW ⟨n, huord⟩ huCW
  have hodd : Odd (orderOf u) := by
    rw [huord]
    exact (show Odd (3 : ℕ) by decide).pow
  obtain ⟨z₂, hz₂S₂, hz₂ord, hZ₂⟩ := exists_central_involution_S₂ 𝔖
  have hz₂sq : z₂ * z₂ = 1 := by
    rw [← pow_two, ← hz₂ord]
    exact pow_orderOf_eq_one z₂
  have hz₂_ne1 : z₂ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₂ord
    omega
  haveI hcomm₁' : IsMulCommutative ↥S₁' := IsKleinFour.isMulCommutative
  have hZ₁' : S₁' ⊓ centralizer (S₁' : Set G) = S₁' :=
    inf_of_le_left (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hcenter : (𝔖.S : Subgroup G) ⊓ centralizer ((𝔖.S : Subgroup G) : Set G) =
      S₁' ⊔ zpowers z₂ := by
    calc (𝔖.S : Subgroup G) ⊓ centralizer ((𝔖.S : Subgroup G) : Set G)
        = (S₁' ⊓ centralizer (S₁' : Set G)) ⊔
            (𝔖.S₂ ⊓ centralizer (𝔖.S₂ : Set G)) := hdd'.inf_centralizer_self
      _ = S₁' ⊔ zpowers z₂ := by rw [hZ₁', hZ₂]
  have hz₂_notS₁' : z₂ ∉ S₁' := by
    intro h
    have hmem : z₂ ∈ S₁' ⊓ 𝔖.S₂ := mem_inf.mpr ⟨h, hz₂S₂⟩
    rw [hdd'.inf_eq] at hmem
    exact hz₂_ne1 (Subgroup.mem_bot.mp hmem)
  obtain ⟨S₂star, hdd₂, h₂S⟩ := lemma_3_3 𝔖 h₁
  obtain ⟨zB, hzBS₂, hzBord, hZBS₂, b, hbS₂, hbsq⟩ :=
    exists_central_involution_sq_mul_self hdd₂.dih₂
  have hzB_ne1 : zB ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzBord
    omega
  have hzB_centerS : zB ∈ (𝔖.S : Subgroup G) ⊓
      centralizer ((𝔖.S : Subgroup G) : Set G) := by
    refine mem_inf.mpr ⟨hdd₂.le_right hzBS₂, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨x, hxX, s, hsB, rfl⟩ := hdd₂.mem_iff.mp hy
    have hxcomm : x * zB = zB * x := hdd₂.comm hxX hzBS₂
    have hzBcentB : zB ∈ centralizer (S₂star : Set G) := by
      have hmem : zB ∈ S₂star ⊓ centralizer (S₂star : Set G) := by
        rw [hZBS₂]
        exact Subgroup.mem_zpowers zB
      exact (mem_inf.mp hmem).2
    have hscomm : s * zB = zB * s :=
      Subgroup.mem_centralizer_iff.mp hzBcentB s hsB
    calc (x * s) * zB = x * (s * zB) := by group
      _ = x * (zB * s) := by rw [hscomm]
      _ = (x * zB) * s := by group
      _ = (zB * x) * s := by rw [hxcomm]
      _ = zB * (x * s) := by group
  have hzB_inS₂ : zB ∈ 𝔖.S₂ := by
    have hbS : b ∈ (𝔖.S : Subgroup G) := hdd₂.le_right hbS₂
    obtain ⟨x, hxX, d, hdD, hbd⟩ := 𝔖.decomp.mem_iff.mp hbS
    have hbd_sq : zB = d * d := by
      calc zB = b * b := hbsq.symm
        _ = (x * d) * (x * d) := by rw [hbd]
        _ = (x * x) * (d * d) := by
            have hdx : d * x = x * d := (𝔖.decomp.comm hxX hdD).symm
            calc (x * d) * (x * d) = x * (d * (x * d)) := by group
              _ = x * ((d * x) * d) := by group
              _ = x * ((x * d) * d) := by rw [hdx]
              _ = (x * x) * (d * d) := by group
        _ = d * d := by
            have hx2 : x * x = 1 := by
              have := CFSG.GH72.sq_eq_one_of_mem_kleinFour h₁ hxX
              simpa [pow_two] using this
            rw [hx2, one_mul]
    rw [hbd_sq]
    exact Subgroup.mul_mem 𝔖.S₂ hdD hdD
  have hzB_in_zp : zB ∈ zpowers z₂ := by
    have hmem : zB ∈ 𝔖.S₂ ⊓
        ((𝔖.S : Subgroup G) ⊓ centralizer ((𝔖.S : Subgroup G) : Set G)) :=
      mem_inf.mpr ⟨hzB_inS₂, hzB_centerS⟩
    have hS₂_inf_center : 𝔖.S₂ ⊓
        ((𝔖.S : Subgroup G) ⊓ centralizer ((𝔖.S : Subgroup G) : Set G)) =
        zpowers z₂ := by
      rw [hcenter, inf_comm]
      exact hdd'.sup_inf_right le_rfl (Subgroup.zpowers_le.mpr hz₂S₂)
    rwa [hS₂_inf_center] at hmem
  have hzB_eq_z₂ : zB = z₂ := by
    rcases (CFSG.Timmesfeld.Bridge.mem_zpowers_iff_of_orderOf_eq_two hz₂ord).mp
      hzB_in_zp with h | h
    · exact absurd h hzB_ne1
    · exact h
  have hz₂S₂star : z₂ ∈ S₂star := by
    rw [← hzB_eq_z₂]
    exact hzBS₂
  have hZ₂star : S₂star ⊓ centralizer (S₂star : Set G) = zpowers z₂ := by
    rw [← hzB_eq_z₂]
    exact hZBS₂
  let 𝔖' : Sec3Setting G :=
    { S := 𝔖.S
      S₁ := 𝔖.S₁
      S₂ := S₂star
      decomp := hdd₂
      noIndexTwo := 𝔖.noIndexTwo }
  have hS₁'_le_center : S₁' ≤ (𝔖.S : Subgroup G) ⊓
      centralizer ((𝔖.S : Subgroup G) : Set G) := by
    rw [hcenter]
    exact le_sup_left
  have hIn : Lemma34OddInput 𝔖' := by
    refine ⟨z₂, u, S₁', hz₂S₂star, hz₂ord, hZ₂star, huN, hodd, ?_,
      hS₁'_le_center, ?_, hz₂_notS₁', huNW, huCW, ?_, ?_⟩
    · intro hC
      apply huCW
      rw [Subgroup.mem_centralizer_iff] at hC ⊢
      intro x hx
      exact hC x (hdd'.le_left hx)
    · exact h₁'.card_four
    · apply le_antisymm _ bot_le
      intro x hx
      obtain ⟨hxS₁, hxz⟩ := mem_inf.mp hx
      rcases (CFSG.Timmesfeld.Bridge.mem_zpowers_iff_of_orderOf_eq_two hz₂ord).mp
        hxz with h | h
      · rw [Subgroup.mem_bot]
        exact h
      · exact absurd (h ▸ hxS₁) hz₂_notS₁'
    · exact hcenter.symm
  obtain ⟨S₁'', hdd'', m, u'', hu''N, hu''ord, hu''NW, hu''CW⟩ :=
    lemma_3_4_of_oddInput 𝔖' h₁ h₂S hIn
  have h₁'' : IsKleinFour ↥S₁'' :=
    isKleinFour_of_isDih_of_three_pow_mem_normalizer hdd''.dih₁ hu''NW ⟨m, hu''ord⟩ hu''CW
  have hconj₁ : ∀ x ∈ S₁'', ∀ y ∈ S₁'', orderOf x = 2 → orderOf y = 2 → IsConj x y :=
    isConj_of_isKleinFour_of_three_pow_mem_normalizer h₁'' hu''NW ⟨m, hu''ord⟩ hu''CW
  let 𝔖'' : Sec3Setting G :=
    { S := 𝔖.S
      S₁ := S₁''
      S₂ := S₂star
      decomp := hdd''
      noIndexTwo := 𝔖.noIndexTwo }
  have h₃'' : ∃ k : ℕ, ∃ v ∈ normalizer ((𝔖''.S : Subgroup G) : Set G),
      orderOf v = 3 ^ k ∧ v ∈ normalizer (S₁'' : Set G) ∧
      v ∉ centralizer (S₁'' : Set G) :=
    ⟨m, u'', hu''N, hu''ord, hu''NW, hu''CW⟩
  have hconj₃ : ∀ x ∈ (𝔖.S : Subgroup G), ∀ y ∈ (𝔖.S : Subgroup G), x ∉ S₁'' →
      x ∉ S₂star → y ∉ S₁'' → y ∉ S₂star → orderOf x = 2 → orderOf y = 2 → IsConj x y :=
    lemma_3_6 𝔖'' h₁'' h₂S h₃''
  obtain ⟨z₁, hz₁S'', hz₁1, _⟩ :=
    CFSG.GH72.exists_mem_kleinFour_ne h₁'' (Subgroup.one_mem S₁'')
  have hz₁sq : z₁ * z₁ = 1 := by
    have := CFSG.GH72.sq_eq_one_of_mem_kleinFour h₁'' hz₁S''
    simpa [pow_two] using this
  have hz₁ord : orderOf z₁ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hz₁sq) hz₁1
  have hz₁_notS₂ : z₁ ∉ S₂star := by
    intro h
    have hmem : z₁ ∈ S₁'' ⊓ S₂star := mem_inf.mpr ⟨hz₁S'', h⟩
    rw [hdd''.inf_eq] at hmem
    exact hz₁1 (Subgroup.mem_bot.mp hmem)
  have hz₂_notS₁'' : z₂ ∉ S₁'' := by
    intro h
    have hmem : z₂ ∈ S₁'' ⊓ S₂star := mem_inf.mpr ⟨h, hz₂S₂star⟩
    rw [hdd''.inf_eq] at hmem
    exact hz₂_ne1 (Subgroup.mem_bot.mp hmem)
  have hS₁''_le_center : S₁'' ≤ (𝔖.S : Subgroup G) ⊓
      centralizer ((𝔖.S : Subgroup G) : Set G) := by
    have hS_le_CS₁'' : (𝔖.S : Subgroup G) ≤ centralizer (S₁'' : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨a, ha, bb, hbb, rfl⟩ := hdd''.mem_iff.mp hy
      haveI : IsMulCommutative ↥S₁'' := IsKleinFour.isMulCommutative
      have hx_a : a * x = x * a := by
        exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
          (⟨a, ha⟩ : ↥S₁'') ⟨x, hx⟩)
      have hbb_x : bb * x = x * bb := (hdd''.comm hx hbb).symm
      calc x * (a * bb) = (x * a) * bb := by group
        _ = (a * x) * bb := by rw [← hx_a]
        _ = a * (x * bb) := by group
        _ = a * (bb * x) := by rw [← hbb_x]
        _ = (a * bb) * x := by group
    exact le_inf hdd''.le_left ((Subgroup.le_centralizer_iff).mpr hS_le_CS₁'')
  have hz₁cent : z₁ ∈ centralizer ((𝔖.S : Subgroup G) : Set G) :=
    (mem_inf.mp (hS₁''_le_center hz₁S'')).2
  have hz₂_centerS : z₂ ∈ (𝔖.S : Subgroup G) ⊓
      centralizer ((𝔖.S : Subgroup G) : Set G) := by
    rw [hcenter]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₂)
  have hz₂cent : z₂ ∈ centralizer ((𝔖.S : Subgroup G) : Set G) :=
    (mem_inf.mp hz₂_centerS).2
  have hz₂centS : (𝔖.S : Subgroup G) ≤ centralizer ({z₂} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hz₂cent s hs
  have hz₁S : z₁ ∈ (𝔖.S : Subgroup G) := hdd''.le_left hz₁S''
  have hzprodS : z₁ * z₂ ∈ (𝔖.S : Subgroup G) := by
    rw [← hdd''.sup_eq]
    exact Subgroup.mul_mem_sup hz₁S'' hz₂S₂star
  have hzprod_comm : z₁ * z₂ = z₂ * z₁ := hdd''.comm hz₁S'' hz₂S₂star
  have hzprod_sq : (z₁ * z₂) * (z₁ * z₂) = 1 := by
    calc (z₁ * z₂) * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
      _ = z₁ * (z₁ * z₂) * z₂ := by rw [← hzprod_comm]
      _ = (z₁ * z₁) * (z₂ * z₂) := by group
      _ = 1 := by rw [hz₁sq, hz₂sq, one_mul]
  have hzprod_ne1 : z₁ * z₂ ≠ 1 := by
    intro h
    have hz₂S₁ : z₂ ∈ S₁'' := by
      have hz₂eq : z₂ = z₁ * (z₁ * z₂) := by
        calc z₂ = 1 * z₂ := (one_mul z₂).symm
          _ = (z₁ * z₁) * z₂ := by rw [hz₁sq]
          _ = z₁ * (z₁ * z₂) := by group
      rw [hz₂eq, h, mul_one]
      exact hz₁S''
    exact hz₂_notS₁'' hz₂S₁
  have hzprod_ord : orderOf (z₁ * z₂) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hzprod_sq) hzprod_ne1
  have hzprod_notS₁ : z₁ * z₂ ∉ S₁'' := by
    intro h
    have hz₂S₁ : z₂ ∈ S₁'' := by
      have hz₂eq : z₂ = z₁ * (z₁ * z₂) := by
        calc z₂ = 1 * z₂ := (one_mul z₂).symm
          _ = (z₁ * z₁) * z₂ := by rw [hz₁sq]
          _ = z₁ * (z₁ * z₂) := by group
      rw [hz₂eq]
      exact Subgroup.mul_mem S₁'' hz₁S'' h
    exact hz₂_notS₁'' hz₂S₁
  have hzprod_notS₂ : z₁ * z₂ ∉ S₂star := by
    intro h
    have hz₁S₂ : z₁ ∈ S₂star := by
      have hz₁eq : z₁ = (z₁ * z₂) * z₂ := by
        calc z₁ = z₁ * 1 := (mul_one z₁).symm
          _ = z₁ * (z₂ * z₂) := by rw [hz₂sq]
          _ = (z₁ * z₂) * z₂ := by group
      rw [hz₁eq]
      exact Subgroup.mul_mem S₂star h hz₂S₂star
    exact hz₁_notS₂ hz₁S₂
  have hzprodcent : z₁ * z₂ ∈ centralizer ((𝔖.S : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ hz₁cent hz₂cent
  have hzprodcentS : (𝔖.S : Subgroup G) ≤ centralizer ({z₁ * z₂} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzprodcent s hs
  have hnot₁₂ : ∀ x ∈ S₁'', ∀ y ∈ S₂star, orderOf x = 2 → orderOf y = 2 →
      ¬ IsConj x y := by
    intro x hx y hy hx2 hy2 hconj
    have hxz : IsConj x z₁ := hconj₁ x hx z₁ hz₁S'' hx2 hz₁ord
    have hyz : IsConj y z₂ := h₂S y hy z₂ hz₂S₂star hy2 hz₂ord
    have hzz : IsConj z₁ z₂ := hxz.symm.trans (hconj.trans hyz)
    obtain ⟨V₂, hV₂, hz₂V₂⟩ := hdd''.isDih₂.exists_four_mem hz₂S₂star hz₂sq
    let A : Subgroup G := S₁'' ⊔ V₂
    have hA : IsE16 A :=
      hdd''.isE16_sup (CFSG.GH72.IsDih.isFourIn_self_of_isKleinFour h₁'') hV₂
    have hAS : A ≤ (𝔖.S : Subgroup G) :=
      sup_le hdd''.le_left (hV₂.1.trans hdd''.le_right)
    have hz₁A : z₁ ∈ A := Subgroup.mem_sup_left hz₁S''
    have hz₂A : z₂ ∈ A := Subgroup.mem_sup_right hz₂V₂
    obtain ⟨g, hgA, hgz⟩ :=
      exists_conj_mem_normalizer_of_isConj_center 𝔖'' hAS hA hz₁A hz₂A hz₂centS
        hz₁ord hz₂ord hzz
    have hN₁ : normalizer (A : Set G) ≤ normalizer (S₁'' : Set G) :=
      (lemma_3_5 𝔖'' h₁'' h₂S h₃'' A hAS hA).2.1
    have hgz_mem : g * z₁ * g⁻¹ ∈ S₁'' :=
      (Subgroup.mem_normalizer_iff.mp (hN₁ hgA) z₁).mp hz₁S''
    rw [hgz] at hgz_mem
    exact hz₂_notS₁'' hgz_mem
  have hnot₁off : ∀ x ∈ S₁'', ∀ y ∈ (𝔖.S : Subgroup G), orderOf x = 2 →
      orderOf y = 2 → y ∉ S₁'' → y ∉ S₂star → ¬ IsConj x y := by
    intro x hx y hyS hx2 hy2 hy1 hy2' hconj
    obtain ⟨y₁, hy₁S, y₂, hy₂S, hy_eq⟩ := hdd''.mem_iff.mp hyS
    have hy_sq : y * y = 1 := by
      rw [← pow_two, ← hy2]
      exact pow_orderOf_eq_one y
    have hy_sq' : (y₁ * y₂) * (y₁ * y₂) = 1 := by rw [← hy_eq]; exact hy_sq
    have hy₂_sq : y₂ * y₂ = 1 := ((hdd''.mul_self_iff hy₁S hy₂S).mp hy_sq').2
    have hy₂1 : y₂ ≠ 1 := by
      intro h
      apply hy1
      rw [hy_eq, h, mul_one]
      exact hy₁S
    obtain ⟨V₂, hV₂, hy₂V₂⟩ := hdd''.isDih₂.exists_four_mem hy₂S hy₂_sq
    have hz₂V₂ : z₂ ∈ V₂ := by
      refine hdd''.isDih₂.mem_four_of_central hV₂ hz₂S₂star fun g hg => ?_
      have hmem : z₂ ∈ S₂star ⊓ centralizer (S₂star : Set G) := by
        rw [hZ₂star]
        exact Subgroup.mem_zpowers z₂
      exact Subgroup.mem_centralizer_iff.mp (mem_inf.mp hmem).2 g hg
    let A : Subgroup G := S₁'' ⊔ V₂
    have hA : IsE16 A :=
      hdd''.isE16_sup (CFSG.GH72.IsDih.isFourIn_self_of_isKleinFour h₁'') hV₂
    have hAS : A ≤ (𝔖.S : Subgroup G) :=
      sup_le hdd''.le_left (hV₂.1.trans hdd''.le_right)
    have hz₁A : z₁ ∈ A := Subgroup.mem_sup_left hz₁S''
    have hyA : y ∈ A := by
      rw [hy_eq]
      exact Subgroup.mul_mem_sup hy₁S hy₂V₂
    have hzprodA : z₁ * z₂ ∈ A :=
      Subgroup.mul_mem_sup hz₁S'' hz₂V₂
    have hzz : IsConj z₁ (z₁ * z₂) :=
      (hconj₁ x hx z₁ hz₁S'' hx2 hz₁ord).symm.trans
        (hconj.trans (hconj₃ y hyS (z₁ * z₂) hzprodS hy1 hy2' hzprod_notS₁
          hzprod_notS₂ hy2 hzprod_ord))
    obtain ⟨g, hgA, hgz⟩ :=
      exists_conj_mem_normalizer_of_isConj_center 𝔖'' hAS hA hz₁A hzprodA hzprodcentS
        hz₁ord hzprod_ord hzz
    have hN₁ : normalizer (A : Set G) ≤ normalizer (S₁'' : Set G) :=
      (lemma_3_5 𝔖'' h₁'' h₂S h₃'' A hAS hA).2.1
    have hgz_mem : g * z₁ * g⁻¹ ∈ S₁'' :=
      (Subgroup.mem_normalizer_iff.mp (hN₁ hgA) z₁).mp hz₁S''
    rw [hgz] at hgz_mem
    exact hzprod_notS₁ hgz_mem
  have hnot₂off : ∀ x ∈ S₂star, ∀ y ∈ (𝔖.S : Subgroup G), orderOf x = 2 →
      orderOf y = 2 → y ∉ S₁'' → y ∉ S₂star → ¬ IsConj x y := by
    intro x hx y hyS hx2 hy2 hy1 hy2' hconj
    obtain ⟨y₁, hy₁S, y₂, hy₂S, hy_eq⟩ := hdd''.mem_iff.mp hyS
    have hy_sq : y * y = 1 := by
      rw [← pow_two, ← hy2]
      exact pow_orderOf_eq_one y
    have hy_sq' : (y₁ * y₂) * (y₁ * y₂) = 1 := by rw [← hy_eq]; exact hy_sq
    have hy₂_sq : y₂ * y₂ = 1 := ((hdd''.mul_self_iff hy₁S hy₂S).mp hy_sq').2
    obtain ⟨V₂, hV₂, hy₂V₂⟩ := hdd''.isDih₂.exists_four_mem hy₂S hy₂_sq
    have hz₂V₂ : z₂ ∈ V₂ := by
      refine hdd''.isDih₂.mem_four_of_central hV₂ hz₂S₂star fun g hg => ?_
      have hmem : z₂ ∈ S₂star ⊓ centralizer (S₂star : Set G) := by
        rw [hZ₂star]
        exact Subgroup.mem_zpowers z₂
      exact Subgroup.mem_centralizer_iff.mp (mem_inf.mp hmem).2 g hg
    let A : Subgroup G := S₁'' ⊔ V₂
    have hA : IsE16 A :=
      hdd''.isE16_sup (CFSG.GH72.IsDih.isFourIn_self_of_isKleinFour h₁'') hV₂
    have hAS : A ≤ (𝔖.S : Subgroup G) :=
      sup_le hdd''.le_left (hV₂.1.trans hdd''.le_right)
    have hz₁A : z₁ ∈ A := Subgroup.mem_sup_left hz₁S''
    have hzprodA : z₁ * z₂ ∈ A :=
      Subgroup.mul_mem_sup hz₁S'' hz₂V₂
    have hz₂A : z₂ ∈ A := Subgroup.mem_sup_right hz₂V₂
    have hz₂x : IsConj z₂ x := (h₂S x hx z₂ hz₂S₂star hx2 hz₂ord).symm
    have hyz : IsConj y (z₁ * z₂) :=
      hconj₃ y hyS (z₁ * z₂) hzprodS hy1 hy2' hzprod_notS₁ hzprod_notS₂
        hy2 hzprod_ord
    have hzz : IsConj (z₁ * z₂) z₂ := (hz₂x.trans (hconj.trans hyz)).symm
    obtain ⟨g, hgA, hgz⟩ :=
      exists_conj_mem_normalizer_of_isConj_center 𝔖'' hAS hA hzprodA hz₂A hz₂centS
        hzprod_ord hz₂ord hzz
    have hNH : normalizer (A : Set G) ≤ normalizer ((S₂star ⊓ A : Subgroup G) : Set G) :=
      (lemma_3_5 𝔖'' h₁'' h₂S h₃'' A hAS hA).2.2.1
    have hz₂H : z₂ ∈ S₂star ⊓ A := mem_inf.mpr ⟨hz₂S₂star, hz₂A⟩
    have hmem : g * (z₁ * z₂) * g⁻¹ ∈ S₂star ⊓ A := by
      rw [hgz]
      exact hz₂H
    have hzprodH : z₁ * z₂ ∈ S₂star ⊓ A :=
      (Subgroup.mem_normalizer_iff.mp (hNH hgA) (z₁ * z₂)).mpr hmem
    exact hzprod_notS₂ (mem_inf.mp hzprodH).1
  refine ⟨S₁'', S₂star, hdd'', ?_⟩
  refine
    { conj₁ := hconj₁
      conj₂ := h₂S
      conj₃ := fun x hx y hy => hconj₃ x (hdd''.sup_eq ▸ hx) y (hdd''.sup_eq ▸ hy)
      separate := ?_ }
  intro x hx y hy hx2 hconj
  have hy2 : orderOf y = 2 := hconj.orderOf_eq.symm.trans hx2
  have hxS : x ∈ (𝔖.S : Subgroup G) := hdd''.sup_eq ▸ hx
  have hyS : y ∈ (𝔖.S : Subgroup G) := hdd''.sup_eq ▸ hy
  by_cases hx1 : x ∈ S₁''
  · have hx_notS₂ : x ∉ S₂star := by
      intro h
      have hmem : x ∈ S₁'' ⊓ S₂star := mem_inf.mpr ⟨hx1, h⟩
      rw [hdd''.inf_eq] at hmem
      have hx_ne1 : x ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hx2
        omega
      exact hx_ne1 (Subgroup.mem_bot.mp hmem)
    have hy_notS₂ : y ∉ S₂star :=
      fun h => hnot₁₂ x hx1 y h hx2 hy2 hconj
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro _
      by_contra hy1
      by_cases hy2' : y ∈ S₂star
      · exact hnot₁₂ x hx1 y hy2' hx2 hy2 hconj
      · exact hnot₁off x hx1 y hyS hx2 hy2 hy1 hy2' hconj
    · intro hy1
      exact hx1
    · intro h
      exact absurd h hx_notS₂
    · intro h
      exact absurd h hy_notS₂
  · by_cases hx2mem : x ∈ S₂star
    · have hy1 : y ∉ S₁'' :=
        fun h => hnot₁₂ y h x hx2mem hy2 hx2 hconj.symm
      have hy2' : y ∈ S₂star := by
        by_contra hy2''
        exact hnot₂off x hx2mem y hyS hx2 hy2 hy1 hy2'' hconj
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · intro h
        exact absurd h hx1
      · intro h
        exact absurd h hy1
      · intro _
        exact hy2'
      · intro _
        exact hx2mem
    · have hy1 : y ∉ S₁'' :=
        fun h => hnot₁off y h x hxS hy2 hx2 hx1 hx2mem hconj.symm
      have hy2' : y ∉ S₂star :=
        fun h => hnot₂off y h x hxS hy2 hx2 hx1 hx2mem hconj.symm
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · intro h
        exact absurd h hx1
      · intro h
        exact absurd h hy1
      · intro h
        exact absurd h hx2mem
      · intro h
        exact absurd h hy2'

end Sec3Setting

end CFSG.GH72
