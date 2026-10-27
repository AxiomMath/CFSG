module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbStep5CaseA
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveAlpha
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbGold
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbGens

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

namespace IIbSyl

theorem rt_conj : ∀ y : ZMod 2 × ZMod 2, (vElt 0 y * t) * (vElt 0 y * t) = 1 →
    ∃ h : IIbSyl, h⁻¹ * t * h = vElt 0 y * t := by decide +kernel

theorem t_conj_right : ∀ h : IIbSyl, (h⁻¹ * t * h).right ≠ 1 := by decide +kernel

theorem card_P : Nat.card P = 64 := by
  rw [P, ← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv,
    Nat.card_eq_fintype_card]
  rfl

end IIbSyl

namespace IIbData

variable {G : Type} [Group G] [Finite G] {A R T V₀ P : Subgroup G} {g t z₀ a σ c₁ : G}

theorem perm5_odd_invol : ∀ p : Equiv.Perm (Fin 5), p * p = 1 → Equiv.Perm.sign p ≠ 1 →
    ∃ r : Equiv.Perm (Fin 5), Equiv.Perm.sign r = 1 ∧ r * p * r⁻¹ = Equiv.swap 0 1 := by
  decide +kernel

theorem mem_A_of_isConj (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    {w : G} (hwN : w ∈ normalizer (A : Set G)) (hw2 : w * w = 1) (hwz : IsConj z₀ w) :
    w ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eA⟩ := hS.equiv
  have hz₀ : z₀ ∈ V₀ := hD.outer.z_mem
  have hz₀1 : z₀ ≠ 1 := hD.outer.z_ne
  by_cases hin : w ∈ A ⊔ centralizer (A : Set G)
  · obtain ⟨a', ha', k, hk, hak⟩ := exists_mul_of_mem_sup hin
    rw [← hak] at hwz hw2 ⊢
    have hka : k * a' = a' * k := (mem_centralizer_iff.mp hk a' ha').symm
    have hsq : a' * a' * (k * k) = 1 := by
      calc a' * a' * (k * k) = a' * k * (a' * k) := by
            calc a' * a' * (k * k) = a' * (a' * k) * k := by group
              _ = a' * (k * a') * k := by rw [hka]
              _ = a' * k * (a' * k) := by group
        _ = 1 := hw2
    have haa : a' * a' ∈ A ⊓ centralizer (A : Set G) := by
      refine mem_inf.mpr ⟨mul_mem ha' ha', ?_⟩
      have : a' * a' = (k * k)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]
      exact inv_mem (mul_mem hk hk)
    rw [inf_centralizer_eq_bot eA, mem_bot] at haa
    have hkk : k * k = 1 := by rw [haa, one_mul] at hsq; exact hsq
    by_cases hk1 : k = 1
    · rw [hk1, mul_one]
      exact ha'
    exfalso
    obtain ⟨κ, hκ, hκk⟩ := exists_conj_mem_of_isSylowOf hS.sylowR hk (n := 1)
      (by rw [pow_one, sq]; exact hkk)
    have hκk1 : κ * k * κ⁻¹ ≠ 1 := fun he => hk1 (by
      calc k = κ⁻¹ * (κ * k * κ⁻¹) * κ := by group
        _ = 1 := by rw [he]; group)
    by_cases ha1 : a' = 1
    · rw [ha1, one_mul] at hwz
      exact hS.not_isConj_of_mem_R hz₀ hz₀1 hκk hκk1 (hwz.trans (isConj_iff.mpr ⟨κ, rfl⟩))
    obtain ⟨α, hα, hαa⟩ := exists_conj_mem_of_isSylowOf hS.loc.sylowV₀ ha' (n := 1)
      (by rw [pow_one, sq]; exact haa)
    have hκK' : κ * k * κ⁻¹ ∈ centralizer (A : Set G) :=
      mul_mem (mul_mem hκ hk) (inv_mem hκ)
    have hconj : α * κ * (a' * k) * (α * κ)⁻¹ = α * a' * α⁻¹ * (κ * k * κ⁻¹) := by
      have h1 : κ * a' = a' * κ := (mem_centralizer_iff.mp hκ a' ha').symm
      have h2 : κ * k * κ⁻¹ * α⁻¹ = α⁻¹ * (κ * k * κ⁻¹) :=
        (mem_centralizer_iff.mp hκK' α⁻¹ (inv_mem hα)).symm
      calc α * κ * (a' * k) * (α * κ)⁻¹ = α * (κ * a') * k * κ⁻¹ * α⁻¹ := by group
        _ = α * (a' * κ) * k * κ⁻¹ * α⁻¹ := by rw [h1]
        _ = α * a' * (κ * k * κ⁻¹ * α⁻¹) := by group
        _ = α * a' * (α⁻¹ * (κ * k * κ⁻¹)) := by rw [h2]
        _ = α * a' * α⁻¹ * (κ * k * κ⁻¹) := by group
    have hvV : α * a' * α⁻¹ * (κ * k * κ⁻¹) ∈ R ⊔ T :=
      mul_mem (hS.V₀_le hαa) (mem_sup_left hκk)
    have hv0 : α * a' * α⁻¹ * (κ * k * κ⁻¹) ∉ V₀ := by
      intro hv
      have h1 : κ * k * κ⁻¹ ∈ R ⊓ V₀ := by
        refine mem_inf.mpr ⟨hκk, ?_⟩
        have h2 := mul_mem (inv_mem hαa) hv
        have e : (α * a' * α⁻¹)⁻¹ * (α * a' * α⁻¹ * (κ * k * κ⁻¹)) = κ * k * κ⁻¹ := by group
        rwa [e] at h2
      rw [hS.inf_R_V₀, mem_bot] at h1
      exact hκk1 h1
    exact hS.not_isConj_of_mem_V₀ hz₀ hz₀1 hvV hv0
      (hwz.trans (isConj_iff.mpr ⟨α * κ, hconj⟩))
  ·
    exfalso
    have htN : t ∈ normalizer (A : Set G) := hS.outer_mem_normalizer_A hD.outer
    have htout : t ∉ A ⊔ centralizer (A : Set G) := by
      intro ht
      obtain ⟨a', ha', k, hk, hak⟩ := exists_mul_of_mem_sup ht
      apply hS.outer_not_inner hD.outer
      refine ⟨a', ha', fun y hy => ?_⟩
      rw [← hak]
      have hky : k * y = y * k := (mem_centralizer_iff.mp hk y hy).symm
      calc a' * k * y * (a' * k)⁻¹ = a' * (k * y) * k⁻¹ * a'⁻¹ := by group
        _ = a' * (y * k) * k⁻¹ * a'⁻¹ := by rw [hky]
        _ = a' * y * a'⁻¹ := by group
    set wN : ↥(normalizer (A : Set G)) := ⟨w, hwN⟩
    set tN : ↥(normalizer (A : Set G)) := ⟨t, htN⟩
    have hw2' : wN * wN = 1 := Subtype.ext hw2
    have ht2' : tN * tN = 1 := Subtype.ext hD.outer.sq
    have hpw : autPerm eA wN * autPerm eA wN = 1 := by rw [← map_mul, hw2', map_one]
    have hpt : autPerm eA tN * autPerm eA tN = 1 := by rw [← map_mul, ht2', map_one]
    have hsw : Equiv.Perm.sign (autPerm eA wN) ≠ 1 := fun h1 =>
      hin ((mem_sup_iff_sign eA wN).mpr h1)
    have hst : Equiv.Perm.sign (autPerm eA tN) ≠ 1 := fun h1 =>
      htout ((mem_sup_iff_sign eA tN).mpr h1)
    obtain ⟨r, hr, hrw⟩ := perm5_odd_invol _ hpw hsw
    obtain ⟨r', hr', hrt⟩ := perm5_odd_invol _ hpt hst
    obtain ⟨α, hα⟩ := eA.surjective ⟨r, (Equiv.Perm.mem_alternatingGroup).mpr hr⟩
    obtain ⟨α', hα'⟩ := eA.surjective ⟨r', (Equiv.Perm.mem_alternatingGroup).mpr hr'⟩
    have hαN : (α : G) ∈ normalizer (A : Set G) := le_normalizer α.2
    have hα'N : (α' : G) ∈ normalizer (A : Set G) := le_normalizer α'.2
    have hPα : autPerm eA ⟨α, hαN⟩ = r := by
      rw [autPerm_of_mem eA α.2]
      simp [hα]
    have hPα' : autPerm eA ⟨α', hα'N⟩ = r' := by
      rw [autPerm_of_mem eA α'.2]
      simp [hα']
    set β : ↥(normalizer (A : Set G)) := (⟨α', hα'N⟩ : ↥(normalizer (A : Set G)))⁻¹ * ⟨α, hαN⟩
      with hβ
    set w' : G := (β : G) * w * (β : G)⁻¹ with hw'
    have hβw : autPerm eA (β * wN * β⁻¹) = autPerm eA tN := by
      simp only [hβ, map_mul, map_inv, hPα, hPα']
      calc r'⁻¹ * r * autPerm eA wN * (r'⁻¹ * r)⁻¹ = r'⁻¹ * (r * autPerm eA wN * r⁻¹) * r' := by
            group
        _ = r'⁻¹ * (r' * autPerm eA tN * r'⁻¹) * r' := by rw [hrw, hrt]
        _ = autPerm eA tN := by group
    have hk₀ : t⁻¹ * w' ∈ centralizer (A : Set G) := by
      have h1 : autPerm eA (tN⁻¹ * (β * wN * β⁻¹)) = 1 := by
        rw [map_mul, hβw, map_inv, inv_mul_cancel]
      have h2 := (autPerm_eq_one_iff eA _).mp h1
      simpa [hw'] using h2
    have hw'2 : w' * w' = 1 := by
      rw [hw']
      calc (β : G) * w * (β : G)⁻¹ * ((β : G) * w * (β : G)⁻¹) = (β : G) * (w * w) * (β : G)⁻¹ := by
            group
        _ = 1 := by rw [hw2]; group
    have hw'z : IsConj z₀ w' := hwz.trans (isConj_iff.mpr ⟨β, rfl⟩)
    set K := centralizer (A : Set G) with hK
    have htK : t ∈ normalizer (K : Set G) := by
      rw [hK, normalizer_centralizer_eq hS.hyp.standard]
      exact htN
    have htK1 : t ∉ K := fun h1 => htout (mem_sup_right h1)
    have ht2 : t * t = 1 := hD.outer.sq
    have hto : orderOf t = 2 :=
      orderOf_eq_prime (by rw [sq]; exact ht2) (fun h1 => htK1 (h1 ▸ one_mem K))
    have htz : ∀ y ∈ zpowers t, y = 1 ∨ y = t := fun y hy =>
      eq_one_or_eq_of_mem_zpowers_of_sq ht2 hy
    have hKt_le : zpowers t ≤ normalizer (K : Set G) := zpowers_le.mpr htK
    have htR : zpowers t ≤ normalizer (R : Set G) := zpowers_le.mpr hD.outer.normR
    have hRK : R ≤ K := hS.sylowR.le
    have hdisjK : K ⊓ zpowers t = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rcases htz y hy.2 with h1 | h1
      · exact h1 ▸ one_mem _
      · exact absurd (h1 ▸ hy.1) htK1
    have hdisjR : R ⊓ zpowers t = ⊥ := eq_bot_iff.mpr fun y hy => by
      rw [← hdisjK]
      exact ⟨hRK hy.1, hy.2⟩
    have hct : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, hto]
    have hcKt : Nat.card (K ⊔ zpowers t : Subgroup G) = Nat.card K * 2 := by
      rw [AS76b.card_sup_eq_mul hKt_le hdisjK, hct]
    have hcRt : Nat.card (R ⊔ zpowers t : Subgroup G) = 4 * 2 := by
      rw [AS76b.card_sup_eq_mul htR hdisjR, hct, hS.cardR]
    have hRtKt : R ⊔ zpowers t ≤ K ⊔ zpowers t := sup_le_sup_right hRK _
    have hsyl : IsSylowOf 2 (R ⊔ zpowers t) (K ⊔ zpowers t) := by
      obtain ⟨-, -, hodd⟩ := isSylowOf_iff.mp hS.sylowR
      refine isSylowOf_iff.mpr ⟨hRtKt, IsPGroup.of_card (n := 3) (by rw [hcRt]; norm_num),
        fun h2 => hodd ?_⟩
      have e1 := Subgroup.relIndex_mul_card (R ⊔ zpowers t) (K ⊔ zpowers t)
      have e2 := Subgroup.relIndex_mul_card R K
      rw [inf_eq_left.mpr hRtKt, hcKt, hcRt] at e1
      rw [inf_eq_left.mpr hRK, hS.cardR] at e2
      have : (R ⊔ zpowers t).relIndex (K ⊔ zpowers t) = R.relIndex K := by
        have := congrArg (· * 2) e2
        omega
      rwa [← this]
    have hw'Kt : w' ∈ K ⊔ zpowers t := by
      have : w' = t * (t⁻¹ * w') := by group
      rw [this]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hk₀)
    obtain ⟨c, hc, hcw⟩ := exists_conj_mem_of_isSylowOf hsyl hw'Kt (n := 1)
      (by rw [pow_one, sq]; exact hw'2)
    have hcN : c ∈ normalizer (K : Set G) := (sup_le le_normalizer hKt_le) hc
    have hcwK : c * w' * c⁻¹ ∉ K := by
      intro h1
      have h2 : w' ∈ K := by
        have := (mem_normalizer_iff.mp hcN w').mpr h1
        exact this
      apply htK1
      have := mul_mem h2 (inv_mem hk₀)
      rwa [show w' * (t⁻¹ * w')⁻¹ = t by group] at this
    obtain ⟨r, hr, b, hb, hrb⟩ := exists_mul_of_mem_sup_of_le_normalizer htR hcw
    rcases htz b hb with hb1 | hb1 <;> rw [hb1] at hrb
    · exact hcwK (by rw [hrb, mul_one]; exact hRK hr)
    obtain ⟨f, hfinj, -, -, -, -, hfR, hft, -, -, -, -⟩ := hD.emb
    obtain ⟨y, rfl⟩ : ∃ y : ZMod 2 × ZMod 2, f (IIbSyl.vElt 0 y) = r := by
      rw [← hfR] at hr
      obtain ⟨_, ⟨w₀, rfl⟩, rfl⟩ := hr
      exact ⟨Multiplicative.toAdd w₀, rfl⟩
    have hrt2 : (IIbSyl.vElt 0 y * IIbSyl.t) * (IIbSyl.vElt 0 y * IIbSyl.t) = 1 := by
      apply hfinj
      rw [map_mul, map_mul, hft, map_one, ← hrb]
      calc c * w' * c⁻¹ * (c * w' * c⁻¹) = c * (w' * w') * c⁻¹ := by group
        _ = 1 := by rw [hw'2]; group
    obtain ⟨hh, hhe⟩ := IIbSyl.rt_conj y hrt2
    apply hD.not_conj
    have h1 : IsConj t (c * w' * c⁻¹) := isConj_iff.mpr ⟨(f hh)⁻¹, by
      rw [inv_inv, hrb, ← hft, ← map_inv, ← map_mul, ← map_mul, hhe, map_mul]⟩
    exact h1.trans ((hw'z.trans (isConj_iff.mpr ⟨c, rfl⟩))).symm

omit [Finite G] in
theorem relIndex_P (hD : IIbData A R T V₀ P t z₀ a σ c₁) : P.relIndex (P ⊔ zpowers t) = 2 := by
  obtain ⟨f, hfinj, hfrange, -, hfP, -⟩ := hD.emb
  have h1 : Nat.card (P ⊔ zpowers t : Subgroup G) = 128 := by
    rw [← hfrange, ← IIbSyl.card_IIbSyl]
    exact (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
  have h2 : Nat.card P = 64 := by
    rw [← hfP, card_map_of_injective hfinj, IIbSyl.card_P]
  have e := Subgroup.relIndex_mul_card P (P ⊔ zpowers t)
  rw [inf_eq_left.mpr le_sup_left, h1, h2] at e
  omega

theorem exists_root_t (hS : Setting310 A R g T V₀)
    (hD : IIbData A R T V₀ P t z₀ a σ c₁) (hc : IsConj z₀ c₁) :
    ∃ y : G, t ∈ centralizer (rightConjugate A y : Set G) := by
  obtain ⟨f, hfinj, hfrange, hfS0, hfP, hfV0, hfR, hft, hfz, hfa, -, hfc⟩ := hD.emb
  have htS : t ∈ P ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have htX : t ∈ rankTwoX A := by
    have h1 : t ∈ (P ⊔ zpowers t) ⊓ rankTwoX A := by
      rw [← hfS0, ← hft]
      exact mem_map_of_mem f (MonoidHom.mem_ker.mpr IIbSyl.chi_eq_one.2.2.2.2.1)
    exact h1.2
  have ht2 : t * t = 1 := hD.outer.sq
  obtain ⟨y, hyP, -, -⟩ := hS.exists_conj_mem_of_thompson_X hD.sylow le_sup_left (relIndex_P hD)
    htS hD.outer.not_mem htX (fun g k _ => by
      rw [pow_mul, sq, ht2, one_pow, mul_one, inv_mul_cancel]
      exact one_mem P)
  set p := y⁻¹ * t * y with hp
  have hp2 : p * p = 1 := by
    calc p * p = y⁻¹ * (t * t) * y := by rw [hp]; group
      _ = 1 := by rw [ht2]; group
  have htp : IsConj t p := isConj_iff.mpr ⟨y⁻¹, by rw [hp, inv_inv]⟩
  have hpz : ¬ IsConj z₀ p := fun h1 => hD.not_conj (htp.trans h1.symm)
  obtain ⟨m, hm⟩ : p ∈ f.range := hfrange ▸ mem_sup_left hyP
  have hmP : m ∈ IIbSyl.P := by
    have h1 : f m ∈ IIbSyl.P.map f := by rw [hfP, hm]; exact hyP
    obtain ⟨m', hm', he⟩ := h1
    exact hfinj he ▸ hm'
  have hm2 : m * m = 1 := hfinj (by rw [map_mul, hm, hp2, map_one])
  have hp1 : p ≠ 1 := fun h1 => by
    have : t = 1 := by
      calc t = y * p * y⁻¹ := by rw [hp]; group
        _ = 1 := by rw [h1]; group
    exact hD.outer.not_mem (this ▸ one_mem P)
  rcases IIbSyl.invol_cases m hm2 with ⟨x, rfl⟩ | ⟨x, r, hr, rfl⟩ | ⟨x, r, hxr⟩ | ⟨x, r, hxr⟩ |
    ⟨x, r, hxr⟩
  · exfalso
    have hpV : p ∈ V₀ := by rw [← hm, ← hfV0]; exact mem_map_of_mem f ⟨Multiplicative.ofAdd x, rfl⟩
    exact hpz (hS.isConj_of_mem_V₀ hD.outer.z_mem hD.outer.z_ne hpV hp1)
  ·
    have hpV : p ∈ R ⊔ T := hm ▸ f_vElt_mem hS hfV0 hfR x r
    have hpV₀ : p ∉ V₀ := fun h1 => hpz (hS.isConj_of_mem_V₀ hD.outer.z_mem hD.outer.z_ne h1 hp1)
    obtain ⟨x₁, -, hx₁⟩ := hS.loc.cover p hpV hpV₀
    refine ⟨x₁ * y⁻¹, ?_⟩
    rw [centralizer_rightConjugate, mem_rightConjugate_iff]
    have h1 := (mem_rightConjugate_iff R x₁ p).mp hx₁
    have h2 : x₁ * p * x₁⁻¹ ∈ centralizer (A : Set G) := hS.sylowR.le h1
    rw [show x₁ * y⁻¹ * t * (x₁ * y⁻¹)⁻¹ = x₁ * p * x₁⁻¹ by rw [hp]; group]
    exact h2
  · exfalso
    apply hpz
    refine hc.trans (isConj_iff.mpr ⟨(f (IIbSyl.vElt x r))⁻¹, ?_⟩)
    rw [← hfc, ← hxr, ← hm]
    simp only [map_mul, map_inv]
    group
  · exfalso
    apply hpz
    have h1 : IsConj (f m) (f IIbSyl.ss) := by
      rcases hxr with hxr | hxr
      · exact isConj_iff.mpr ⟨f (IIbSyl.vElt x r), by rw [← hxr]; simp only [map_mul, map_inv]⟩
      · exact isConj_iff.mpr ⟨f (IIbSyl.t * IIbSyl.vElt x r), by
          rw [← hxr]; simp only [map_mul, map_inv]⟩
    rw [← hm]
    exact hc.trans ((isConj_ss_c₁ hS hD hfinj hfrange hfP hfV0 hfR hfz hfa hfc).symm.trans h1.symm)
  · exfalso
    have hright := IIbSyl.right_eq_one_of_mem_P hmP
    rcases hxr with hxr | hxr
    · exact IIbSyl.t_conj_right _ (hxr ▸ hright)
    · exact IIbSyl.t_conj_right _ (hxr ▸ hright)

theorem oddCoreIn_centralizer_eq_bot
    (hGold : Asc76X.GoldschmidtTheoremA) (hS : Setting310 A R g T V₀)
    (hD : IIbData A R T V₀ P t z₀ a σ c₁) :
    oddCoreIn (centralizer ({z₀} : Set G)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eA⟩ := hS.equiv
  have hc := isConj_z₀_c₁ hGold hS hD
  obtain ⟨x₀, hx₀⟩ := conj_ptOf_of_isConj hS hD hc
  obtain ⟨f, hfinj, hfrange, -, hfP, hfV0, hfR, hft, hfz, hfa, -, hfc⟩ := hD.emb
  obtain ⟨S, hS₁⟩ := Asc76X.exists_sylow_eq_of_isSylowOf_top hD.sylow
  have hzV₀ : z₀ ∈ V₀ := hD.outer.z_mem
  have hz1 : z₀ ≠ 1 := hD.outer.z_ne
  have hz2 : z₀ * z₀ = 1 := hS.mul_self (hS.V₀_le hzV₀)
  have hzA : z₀ ∈ A := hS.V₀_le_A hzV₀
  have hsq : ∀ (c w : G), w * w = 1 → c * w * c⁻¹ * (c * w * c⁻¹) = 1 := fun c w hw => by
    calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
      _ = 1 := by rw [hw]; group
  have hne : ∀ (c w : G), w ≠ 1 → c * w * c⁻¹ ≠ 1 := fun c w hw he => hw (by
    calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
      _ = 1 := by rw [he]; group)
  have hcoA : ∀ {w : G}, w ∈ A → w * w = 1 → w ≠ 1 → CoA A w z₀ := fun hw hw2 hw1 =>
    ⟨hw2, hw1, hz2, hz1, 1, by rw [rightConjugate_one]; exact hw,
      by rw [rightConjugate_one]; exact hzA⟩
  have hS₁z : ∀ s ∈ P ⊔ zpowers t, s * z₀ * s⁻¹ = z₀ := fun s hs => by
    have := mem_centralizer_singleton_iff.mp (hD.S₁_le hS hs).2
    rw [this, mul_inv_cancel_right]
  have hCconn : ∀ u : G, Relation.EqvGen (CoA A) u z₀ →
      centralizer ({u} : Set G) ≤ compStabA A z₀ := by
    intro u hu c hc'
    rw [mem_compStabA]
    have h1 := eqvGen_coA_conj hu c
    rw [mem_centralizer_singleton_iff] at hc'
    rw [show c * u * c⁻¹ = u by rw [hc']; group] at h1
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h1) hu
  have hCroot : ∀ (x u : G), u ∈ centralizer (rightConjugate A x : Set G) → u ≠ 1 →
      u * u = 1 → z₀ ∈ rightConjugate A x → centralizer ({u} : Set G) ≤ compStabA A z₀ := by
    intro x u hu hu1 hu2 hzx c hc'
    have hcN := centralizer_le_normalizer_conj hS.hyp.standard x hu hu1 hu2 hc'
    have hczA : c * z₀ * c⁻¹ ∈ rightConjugate A x := (mem_normalizer_iff.mp hcN z₀).mp hzx
    rw [mem_compStabA]
    exact Relation.EqvGen.rel _ _ ⟨hsq c z₀ hz2, hne c z₀ hz1, hz2, hz1, x, hczA, hzx⟩
  have hF2 : ∀ (x u : G), u ∈ centralizer (rightConjugate A x : Set G) → u ≠ 1 →
      u * u = 1 → u * z₀ = z₀ * u → z₀ ∈ rightConjugate A x := by
    intro x u hu hu1 hu2 huz
    have hzN := centralizer_le_normalizer_conj hS.hyp.standard x hu hu1 hu2
      (mem_centralizer_singleton_iff.mpr huz.symm)
    rw [mem_normalizer_rightConjugate_iff] at hzN
    rw [mem_rightConjugate_iff]
    exact mem_A_of_isConj hS hD hzN (hsq x z₀ hz2) (isConj_iff.mpr ⟨x, rfl⟩)
  have hc₁conn : Relation.EqvGen (CoA A) c₁ z₀ := by
    have hW : ptOf z₀ c₁ ≤ rightConjugate A x₀ := by
      rw [← hx₀]
      exact map_mono hS.V₀_le_A
    have hc2 : c₁ * c₁ = 1 := by rw [← hfc, ← map_mul, IIbSyl.c1_facts.2.1, map_one]
    have hc1 : c₁ ≠ 1 := fun h1 => IIbSyl.c1_facts.2.2.1 (hfinj (by rw [hfc, h1, map_one]))
    exact Relation.EqvGen.rel _ _ ⟨hc2, hc1, hz2, hz1, x₀, hW (mem_sup_right (mem_zpowers c₁)),
      hW (mem_sup_left (mem_zpowers z₀))⟩
  have hV₀conn : ∀ w ∈ V₀, w ≠ 1 → Relation.EqvGen (CoA A) w z₀ := fun w hw hw1 =>
    Relation.EqvGen.rel _ _ (hcoA (hS.V₀_le_A hw) (hS.mul_self (hS.V₀_le hw)) hw1)
  have hNconn : ∀ k ∈ normalizer (V₀ : Set G), ∀ u : G, Relation.EqvGen (CoA A) u z₀ →
      Relation.EqvGen (CoA A) (k * u * k⁻¹) z₀ := by
    intro k hk u hu
    have h1 := eqvGen_coA_conj hu k
    have hkz : k * z₀ * k⁻¹ ∈ V₀ := (mem_normalizer_iff.mp hk z₀).mp hzV₀
    exact Relation.EqvGen.trans _ _ _ h1 (hV₀conn _ hkz (hne k z₀ hz1))
  have hssconn : Relation.EqvGen (CoA A) (f IIbSyl.ss) z₀ := by
    obtain ⟨k, hk, hke⟩ := exists_conj_ss_c₁ hS hD hfinj hfrange hfP hfV0 hfR hfz hfa hfc
    rw [← hke]
    exact hNconn k hk c₁ hc₁conn
  have hS₁N : ∀ s ∈ P ⊔ zpowers t, s ∈ normalizer (V₀ : Set G) := fun s hs => (hD.S₁_le hS hs).1
  have hfS : ∀ y : IIbSyl, f y ∈ P ⊔ zpowers t := fun y => hfrange ▸ ⟨y, rfl⟩
  have hSM : (S : Subgroup G) ≤ compStabA A z₀ := fun s hs => by
    rw [mem_compStabA, hS₁z s (hS₁ ▸ hs)]
    exact Relation.EqvGen.refl z₀
  have hNS : normalizer ((S : Subgroup G) : Set G) ≤ compStabA A z₀ := by
    intro n hn
    have h1 : n * z₀ * n⁻¹ ∈ P ⊔ zpowers t := by
      rw [← hS₁]
      exact (mem_normalizer_iff.mp hn z₀).mp (hS₁ ▸ hD.z₀_mem_S₁)
    obtain ⟨m, hm⟩ : n * z₀ * n⁻¹ ∈ f.range := hfrange ▸ h1
    have hmc : ∀ u : IIbSyl, m * u = u * m := by
      intro u
      apply hfinj
      rw [map_mul, map_mul, hm]
      have hu : n⁻¹ * f u * n ∈ P ⊔ zpowers t := by
        rw [← hS₁]
        have := (mem_normalizer_iff.mp (inv_mem hn) (f u)).mp (hS₁ ▸ hfS u)
        simpa using this
      have e := (mem_centralizer_singleton_iff.mp (hD.S₁_le hS hu).2)
      calc n * z₀ * n⁻¹ * f u = n * (z₀ * (n⁻¹ * f u * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * f u * n) * z₀) * n⁻¹ := by rw [e]
        _ = f u * (n * z₀ * n⁻¹) := by group
    rw [mem_compStabA]
    rcases IIbSyl.center_IIbSyl m hmc with h1 | h1
    · exact absurd (by rw [← hm, h1, map_one]) (hne n z₀ hz1)
    · rw [← hm, h1, hfz]
      exact Relation.EqvGen.refl z₀
  have hCS : ∀ u ∈ (S : Subgroup G), orderOf u = 2 →
      centralizer ({u} : Set G) ≤ compStabA A z₀ := by
    intro u hu hu2
    have huS : u ∈ P ⊔ zpowers t := hS₁ ▸ hu
    have huu : u * u = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
    have hu1 : u ≠ 1 := fun he => by rw [he, orderOf_one] at hu2; exact absurd hu2 (by decide)
    have huz : u * z₀ = z₀ * u := by
      have := mem_centralizer_singleton_iff.mp (hD.S₁_le hS huS).2
      exact this
    obtain ⟨m, rfl⟩ : u ∈ f.range := hfrange ▸ huS
    have hm2 : m * m = 1 := hfinj (by rw [map_mul, huu, map_one])
    rcases IIbSyl.invol_cases m hm2 with ⟨x, rfl⟩ | ⟨x, r, hr, rfl⟩ | ⟨x, r, hxr⟩ |
      ⟨x, r, hxr⟩ | ⟨x, r, hxr⟩
    · apply hCconn
      refine hV₀conn _ ?_ hu1
      rw [← hfV0]
      exact mem_map_of_mem f ⟨Multiplicative.ofAdd x, rfl⟩
    ·
      have hpV : f (IIbSyl.vElt x r) ∈ R ⊔ T := f_vElt_mem hS hfV0 hfR x r
      have hpV₀ : f (IIbSyl.vElt x r) ∉ V₀ := by
        intro hm
        rw [← hfV0] at hm
        obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hm
        exact IIbSyl.vElt_ne x r _ hr (hfinj hw).symm
      obtain ⟨x₁, -, hx₁⟩ := hS.loc.cover _ hpV hpV₀
      have huK : f (IIbSyl.vElt x r) ∈ centralizer (rightConjugate A x₁ : Set G) := by
        rw [centralizer_rightConjugate]
        exact map_mono hS.sylowR.le hx₁
      exact hCroot x₁ _ huK hu1 huu (hF2 x₁ _ huK hu1 huu huz)
    ·
      apply hCconn
      have e : f m = (f (IIbSyl.vElt x r))⁻¹ * c₁ * f (IIbSyl.vElt x r) := by
        rw [← hfc, ← hxr]
        simp only [map_mul, map_inv]
        group
      rw [e]
      have := hNconn (f (IIbSyl.vElt x r))⁻¹ (inv_mem (hS₁N _ (hfS (IIbSyl.vElt x r)))) c₁
        hc₁conn
      simpa using this
    ·
      apply hCconn
      have key : ∀ y : IIbSyl, y * m * y⁻¹ = IIbSyl.ss → Relation.EqvGen (CoA A) (f m) z₀ := by
        intro y hy
        have e : f m = (f y)⁻¹ * f IIbSyl.ss * f y := by
          rw [← hy]
          simp only [map_mul, map_inv]
          group
        rw [e]
        have := hNconn (f y)⁻¹ (inv_mem (hS₁N _ (hfS y))) _ hssconn
        simpa using this
      rcases hxr with hxr | hxr
      · exact key _ hxr
      · exact key _ hxr
    ·
      obtain ⟨y, hy⟩ := exists_root_t hS hD hc
      have key : ∀ h' : IIbSyl, h'⁻¹ * IIbSyl.t * h' = m →
          centralizer ({f m} : Set G) ≤ compStabA A z₀ := by
        intro h' hh'
        have e : f m = (f h')⁻¹ * t * f h' := by rw [← hh', ← hft]; simp only [map_mul, map_inv]
        have huK : f m ∈ centralizer (rightConjugate A (y * f h') : Set G) := by
          rw [e, centralizer_rightConjugate, mem_rightConjugate_iff]
          rw [centralizer_rightConjugate, mem_rightConjugate_iff] at hy
          rw [show y * f h' * ((f h')⁻¹ * t * f h') * (y * f h')⁻¹ = y * t * y⁻¹ by group]
          exact hy
        exact hCroot _ _ huK hu1 huu (hF2 _ _ huK hu1 huu huz)
      rcases hxr with hxr | hxr
      · exact key _ hxr
      · exact key _ hxr
  have hMtop : compStabA A z₀ = ⊤ := by
    by_contra hMne
    have heven : Even (Nat.card (compStabA A z₀)) := by
      have hzo : orderOf z₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
      rw [even_iff_two_dvd, ← hzo,
        ← Subgroup.orderOf_mk z₀ (hSM (hS₁ ▸ hD.z₀_mem_S₁))]
      exact orderOf_dvd_natCard _
    have hSE := CFSG.ProperTwoGeneratedCore.sylow_normalizer_involution_centralizer_strong_embedding
      (compStabA A z₀) hMne heven S hSM hNS (centralizer_le_of_sylow S hSM hCS)
    have hc2 : c₁ * c₁ = 1 := by rw [← hfc, ← map_mul, IIbSyl.c1_facts.2.1, map_one]
    have hc1 : c₁ ≠ 1 := fun h1 => IIbSyl.c1_facts.2.2.1 (hfinj (by rw [hfc, h1, map_one]))
    have hco : orderOf c₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hc2) hc1
    have hcomm := CFSG.StronglyEmbedded.commute_of_mem_sylow_of_fusionStronglyEmbedded hSE S
      (hS₁ ▸ hD.c₁_mem_S₁) hco (hS₁ ▸ (mem_sup_right (mem_zpowers t)))
    apply IIbSyl.t_facts.2
    apply hfinj
    rw [map_mul, map_mul, hfc, hft]
    exact hcomm.eq.symm
  have hLn : (conjSupThrough A z₀).Normal := ⟨fun u hu x => by
    have h1 := conj_mem_conjSupThrough x hu
    have h2 : x ∈ compStabA A z₀ := hMtop ▸ mem_top x
    rw [mem_compStabA] at h2
    rwa [conjSupThrough_eq_of_eqvGen eA h2] at h1⟩
  have hAL : A ≤ conjSupThrough A z₀ := by
    have := le_conjSupThrough (A := A) (w := z₀) (x := 1) (by rw [rightConjugate_one]; exact hzA)
    rwa [rightConjugate_one] at this
  have hXL : rankTwoX A ≤ conjSupThrough A z₀ := normalClosure_le_normal hAL
  have hO := oddCoreIn_centralizer_le_centralizer_conjSupThrough hS.hyp.standard eA hS.sylowR.le
    hS.elemR hS.cardR hz2 hz1
  have hOX : oddCoreIn (centralizer ({z₀} : Set G)) ≤ centralizer (rankTwoX A : Set G) :=
    hO.trans (centralizer_le hXL)
  rw [eq_bot_iff]
  intro y hy
  have h1 := hOX hy
  rw [hS.centralizer_X_eq_bot, mem_bot] at h1
  exact h1

end IIbData

end CFSG.ComponentClassification.RankTwoAltFive
