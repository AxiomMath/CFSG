module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.ChevalleyBinomial
public import CFSG.GH74.Uniqueness.SU.KI1r3Y
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG CFSG.Blueprint
open scoped Pointwise

variable {H : Type} [Group H]

theorem exists_involution_sup_zpowers {y x t : H}
    (ht : t * t = 1) (hy4 : orderOf y = 4) (hyt : y * y = t)
    (hcomm : y * x = x * y) (hx : x ∉ zpowers t) (hx2 : ∃ n : ℕ, x ^ (2 ^ n) = 1)
    (hint : ∀ g : H, g ∈ zpowers y → g ∈ zpowers x → g ∈ zpowers t) :
    ∃ v : H, v * v = 1 ∧ v ≠ 1 ∧ v ≠ t ∧ v ∈ zpowers y ⊔ zpowers x := by
  classical
  have hex : ∃ k : ℕ, x ^ (2 ^ k) ∈ zpowers t := by
    obtain ⟨n, hn⟩ := hx2
    exact ⟨n, by rw [hn]; exact one_mem _⟩
  let k := Nat.find hex
  have hk : x ^ (2 ^ k) ∈ zpowers t := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    apply hx
    have := hk
    rw [h0] at this
    simpa using this
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hjmin : x ^ (2 ^ j) ∉ zpowers t := Nat.find_min hex (by omega : j < k)
  set w := x ^ (2 ^ j) with hw
  have hww : w * w ∈ zpowers t := by
    have : w * w = x ^ (2 ^ k) := by
      rw [hw, ← pow_add, hj, pow_succ, mul_two]
    rw [this]; exact hk
  have hwx : w ∈ zpowers x := Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _
  have hwy : y * w = w * y := by
    rw [hw]
    exact (Commute.pow_right (show Commute y x from hcomm) _).eq
  have hy_not : y ∉ zpowers t := by
    intro hyt'
    rcases CFSG.GH74.Uniqueness.SU.K.R3.LemmaYAux.eq_one_or_eq_of_mem_zpowers ht hyt' with h1 | h1
    · rw [h1, orderOf_one] at hy4; omega
    · have hy2 : y * y = 1 := by rw [h1]; exact ht
      have : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
      rw [hy4] at this
      omega
  rcases CFSG.GH74.Uniqueness.SU.K.R3.LemmaYAux.eq_one_or_eq_of_mem_zpowers ht hww with h1 | h1
  · refine ⟨w, h1, ?_, ?_, Subgroup.mem_sup_right hwx⟩
    · intro h; exact hjmin (h ▸ one_mem _)
    · intro h; exact hjmin (h ▸ Subgroup.mem_zpowers t)
  · have hty : t ∈ zpowers y :=
      Subgroup.mem_zpowers_iff.mpr ⟨2, by show y ^ (2:ℤ) = t; rw [zpow_two]; exact hyt⟩
    have hwinv : w⁻¹ ∈ zpowers x := Subgroup.inv_mem _ hwx
    have hcomm' : y * w⁻¹ = w⁻¹ * y := by
      have := (Commute.inv_right (show Commute y w from hwy)).eq
      exact this
    have hsq : (y * w⁻¹) * (y * w⁻¹) = 1 := by
      calc (y * w⁻¹) * (y * w⁻¹) = y * (w⁻¹ * y) * w⁻¹ := by group
        _ = y * (y * w⁻¹) * w⁻¹ := by rw [← hcomm']
        _ = (y * y) * (w⁻¹ * w⁻¹) := by group
        _ = t * (w * w)⁻¹ := by rw [hyt, mul_inv_rev]
        _ = 1 := by
            have : (t : H)⁻¹ = t := inv_eq_of_mul_eq_one_right ht
            rw [h1, this, ht]
    refine ⟨y * w⁻¹, hsq, ?_, ?_,
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
        (Subgroup.mem_sup_right hwinv)⟩
    · intro h
      have hyw : y = w := by
        have : y = w := by
          have h2 : y * w⁻¹ * w = 1 * w := by rw [h]
          simpa using h2
        exact this
      apply hy_not
      apply hint
      · exact Subgroup.mem_zpowers y
      · rw [hyw]; exact hwx
    · intro h
      apply hjmin
      have hwt : w = t * y := by
        have h2 : y * w⁻¹ = t := h
        have h3 : w⁻¹ = y⁻¹ * t := by
          have := congrArg (fun z => y⁻¹ * z) h2
          simpa using this
        have h4 : w = (y⁻¹ * t)⁻¹ := by rw [← h3]; simp
        rw [h4, mul_inv_rev, inv_inv]
        have : (t : H)⁻¹ = t := inv_eq_of_mul_eq_one_right ht
        rw [this]
      apply hint
      · rw [hwt]; exact Subgroup.mul_mem _ hty (Subgroup.mem_zpowers y)
      · exact hwx

theorem two_le_pRank_sup_zpowers [Finite H] {y x t : H}
    (ht : t * t = 1) (hy4 : orderOf y = 4) (hyt : y * y = t)
    (hcomm : y * x = x * y) (hx : x ∉ zpowers t) (hx2 : ∃ n : ℕ, x ^ (2 ^ n) = 1)
    (hint : ∀ g : H, g ∈ zpowers y → g ∈ zpowers x → g ∈ zpowers t) :
    2 ≤ Open.pRank 2 (zpowers y ⊔ zpowers x) := by
  obtain ⟨v, hv2, hv1, hvt, hvmem⟩ := exists_involution_sup_zpowers ht hy4 hyt hcomm hx hx2 hint
  have hcommA : ∀ a ∈ zpowers y, ∀ b ∈ zpowers x, a * b = b * a := by
    rintro a ⟨m, rfl⟩ b ⟨n, rfl⟩
    exact (Commute.zpow_zpow (show Commute y x from hcomm) m n).eq
  have hty : t ∈ zpowers y :=
    Subgroup.mem_zpowers_iff.mpr ⟨2, by show y ^ (2:ℤ) = t; rw [zpow_two]; exact hyt⟩
  have ht1 : t ≠ 1 := by
    intro h
    have hy2 : y * y = 1 := by rw [hyt, h]
    have : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
    rw [hy4] at this
    omega
  have hvt' : v ∉ zpowers t := by
    intro hmem
    rcases CFSG.GH74.Uniqueness.SU.K.R3.LemmaYAux.eq_one_or_eq_of_mem_zpowers ht hmem with h | h
    · exact hv1 h
    · exact hvt h
  have hcomm_tv : t * v = v * t := by
    obtain ⟨a, ha, b, hb, rfl⟩ := SU1.mem_sup_of_commute hcommA hvmem
    have hta : t * a = a * t := by
      obtain ⟨m, rfl⟩ := ha
      obtain ⟨n, hn⟩ := hty
      rw [← hn]
      exact (Commute.zpow_zpow_self y n m).eq
    have htb : t * b = b * t := by
      have : Commute y b := by
        obtain ⟨n, rfl⟩ := hb
        exact Commute.zpow_right (show Commute y x from hcomm) n
      have h2 : Commute (y * y) b := this.mul_left this
      rw [hyt] at h2
      exact h2.eq
    calc t * (a * b) = (t * a) * b := by rw [mul_assoc]
      _ = (a * t) * b := by rw [hta]
      _ = a * (t * b) := by rw [mul_assoc]
      _ = a * (b * t) := by rw [htb]
      _ = (a * b) * t := by rw [mul_assoc]
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := t) (y := v)
    (by rw [pow_two]; exact ht) (by rw [pow_two]; exact hv2) ht1 hvt' hcomm_tv
  exact SU1.le_pRank (p := 2) (by norm_num)
    (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hty)) (Subgroup.zpowers_le.mpr hvmem))
    hel hcard

theorem exists_four_group_inf_eq_bot [Finite H] (N : Subgroup H) (h3 : 3 ≤ Open.twoRank H)
    (hN : Open.pRank 2 N ≤ 1) :
    ∃ U : Subgroup H, Nat.card U = 4 ∧ (∀ u ∈ U, u * u = 1) ∧ U ⊓ N = ⊥ := by
  obtain ⟨E, -, hE, hEcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two
    (H := (⊤ : Subgroup H)) (k := 3) h3
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by
    have := (SU1.isElemAbelian_iff.mp hE).2 x hx
    rwa [pow_two] at this
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := (SU1.isElemAbelian_iff.mp hE).1
  have hA : Open.IsElemAbelian 2 (E ⊓ N) := SU1.IsElemAbelian.mono inf_le_left hE
  obtain ⟨k, hk⟩ := SU1.IsElemAbelian.exists_card Nat.prime_two hA
  have hk1 : k ≤ 1 := (SU1.le_pRank (by norm_num) inf_le_right hA hk).trans hN
  have hfour : ∀ (b c : H), b ∈ E → c ∈ E → b ≠ 1 → c ∉ zpowers b →
      Nat.card (zpowers b ⊔ zpowers c : Subgroup H) = 4 ∧
        ∀ u ∈ (zpowers b ⊔ zpowers c : Subgroup H), u * u = 1 := by
    intro b c hb hc hb1 hcb
    obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := b) (y := c)
      (by rw [pow_two]; exact hEsq b hb) (by rw [pow_two]; exact hEsq c hc) hb1 hcb
      (hEcomm b hb c hc)
    refine ⟨by rw [hcard]; norm_num, fun u hu => ?_⟩
    have := (SU1.isElemAbelian_iff.mp hel).2 u hu
    rwa [pow_two] at this
  have hzp : ∀ {a : H}, a * a = 1 → ∀ g ∈ zpowers a, g = 1 ∨ g = a := fun {a} ha g hg =>
    CFSG.GH74.Uniqueness.SU.K.R3.LemmaYAux.eq_one_or_eq_of_mem_zpowers ha hg
  rcases Nat.lt_or_ge k 1 with hk0 | hk1'
  ·
    have hk0' : k = 0 := by omega
    have hbot : E ⊓ N = ⊥ := by
      apply Subgroup.card_eq_one.mp
      rw [hk, hk0', pow_zero]
    obtain ⟨F, hFE, hF, hFcard⟩ := SU1.exists_subgroup_card Nat.prime_two hE
      (j := 2) (k := 3) (by norm_num) hEcard
    refine ⟨F, by rw [hFcard]; norm_num, fun u hu => ?_, ?_⟩
    · exact hEsq u (hFE hu)
    · apply eq_bot_iff.mpr
      intro x hx
      have : x ∈ E ⊓ N := ⟨hFE hx.1, hx.2⟩
      rw [hbot] at this
      exact this
  ·
    have hk1'' : k = 1 := by omega
    have hAcard : Nat.card (E ⊓ N : Subgroup H) = 2 := by rw [hk, hk1'', pow_one]
    obtain ⟨n, hnA, hn1⟩ : ∃ n ∈ (E ⊓ N : Subgroup H), n ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : (E ⊓ N : Subgroup H) = ⊥ := eq_bot_iff.mpr fun x hx => hcon x hx
      rw [this, Subgroup.card_bot] at hAcard
      omega
    have hnE : n ∈ E := hnA.1
    have hAeq : ∀ x ∈ (E ⊓ N : Subgroup H), x = 1 ∨ x = n := by
      intro x hx
      by_contra hcon
      push Not at hcon
      have hsub : (zpowers n ⊔ zpowers x : Subgroup H) ≤ E ⊓ N :=
        sup_le (Subgroup.zpowers_le.mpr hnA) (Subgroup.zpowers_le.mpr hx)
      obtain ⟨hel2, hcard2⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := n) (y := x)
        (by rw [pow_two]; exact hEsq n hnE) (by rw [pow_two]; exact hEsq x hx.1) hn1
        (fun hmem => by
          rcases hzp (hEsq n hnE) x hmem with h | h
          · exact hcon.1 h
          · exact hcon.2 h)
        (hEcomm n hnE x hx.1)
      have := Subgroup.card_le_of_le hsub
      rw [hcard2, hAcard] at this
      omega
    obtain ⟨b, hbE, hbA⟩ : ∃ b ∈ E, b ∉ (E ⊓ N : Subgroup H) := by
      by_contra hcon
      push Not at hcon
      have hle : E ≤ E ⊓ N := fun x hx => hcon x hx
      have := Subgroup.card_le_of_le hle
      rw [hEcard, hAcard] at this
      omega
    have hb1 : b ≠ 1 := fun h => hbA (h ▸ (E ⊓ N).one_mem)
    have hbn : n ∉ zpowers b := by
      intro hmem
      rcases hzp (hEsq b hbE) n hmem with h | h
      · exact hn1 h
      · exact hbA (h ▸ hnA)
    obtain ⟨hel4, hcard4⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := b) (y := n)
      (by rw [pow_two]; exact hEsq b hbE) (by rw [pow_two]; exact hEsq n hnE) hb1 hbn
      (hEcomm b hbE n hnE)
    obtain ⟨c, hcE, hcB⟩ : ∃ c ∈ E, c ∉ (zpowers b ⊔ zpowers n : Subgroup H) := by
      by_contra hcon
      push Not at hcon
      have hle : E ≤ (zpowers b ⊔ zpowers n : Subgroup H) := fun x hx => hcon x hx
      have := Subgroup.card_le_of_le hle
      rw [hEcard, hcard4] at this
      omega
    have hcb : c ∉ zpowers b := fun h => hcB (Subgroup.mem_sup_left h)
    obtain ⟨hcardU, hsqU⟩ := hfour b c hbE hcE hb1 hcb
    refine ⟨zpowers b ⊔ zpowers c, hcardU, hsqU, ?_⟩
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨hxU, hxN⟩ := hx
    have hUE : (zpowers b ⊔ zpowers c : Subgroup H) ≤ E :=
      sup_le (Subgroup.zpowers_le.mpr hbE) (Subgroup.zpowers_le.mpr hcE)
    have hxA : x ∈ (E ⊓ N : Subgroup H) := ⟨hUE hxU, hxN⟩
    rcases hAeq x hxA with h | h
    · exact h ▸ (⊥ : Subgroup H).one_mem
    · exfalso
      subst h
      have hcommbc : ∀ a ∈ zpowers b, ∀ d ∈ zpowers c, a * d = d * a := by
        rintro a ⟨m, rfl⟩ d ⟨l, rfl⟩
        exact (Commute.zpow_zpow (show Commute b c from hEcomm b hbE c hcE) m l).eq
      obtain ⟨a', ha', c', hc', hac⟩ := SU1.mem_sup_of_commute hcommbc hxU
      rcases hzp (hEsq c hcE) c' hc' with h1 | h1
      ·
        rw [h1, mul_one] at hac
        exact hbn (hac ▸ ha')
      ·
        rw [h1] at hac
        apply hcB
        have : c = a'⁻¹ * x := by
          have := congrArg (fun z => a'⁻¹ * z) hac
          simpa using this
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left ha'))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

theorem exists_conj_mem_sylow [Finite H] (S : Sylow 2 H) (y : H) (hy : IsPGroup 2 (zpowers y)) :
    ∃ g : H, g * y * g⁻¹ ∈ (S : Subgroup H) := by
  obtain ⟨Q, hQ⟩ := hy.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q S
  refine ⟨g, ?_⟩
  have hyQ : y ∈ (Q : Subgroup H) := hQ (Subgroup.mem_zpowers y)
  have hmem : MulAut.conj g • y ∈ MulAut.conj g • ((Q : Subgroup H) : Set H) :=
    Set.smul_mem_smul_set hyQ
  have hcoe : ((g • Q : Sylow 2 H) : Set H) = MulAut.conj g • ((Q : Subgroup H) : Set H) :=
    Sylow.coe_smul
  rw [← hcoe, hg] at hmem
  have h3 : g * y * g⁻¹ ∈ ((S : Subgroup H) : Set H) := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using hmem
  exact h3

theorem quasisimple_le_of_conj_mem (K X : Subgroup H) (hK : CFSG.IsQuasisimple ↥K) (y : H)
    (hyK : y ∈ K) (hyc : ∃ k ∈ K, k * y ≠ y * k) (hX : ∀ k ∈ K, k * y * k⁻¹ ∈ X) : K ≤ X := by
  set y' : ↥K := ⟨y, hyK⟩ with hy'
  have hN : (Subgroup.normalClosure ({y'} : Set ↥K)).Normal := inferInstance
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK hN with htop | hcen
  · intro k hk
    have hk' : (⟨k, hk⟩ : ↥K) ∈ Subgroup.normalClosure ({y'} : Set ↥K) := by rw [htop]; trivial
    have hle : Subgroup.normalClosure ({y'} : Set ↥K) ≤ X.subgroupOf K := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro g hg
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hg
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      have : (g : H) = (c : H) * y * (c : H)⁻¹ := by
        have := congrArg Subtype.val hc.symm
        simpa using this
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, this]
      exact hX _ c.2
    exact hle hk'
  · exfalso
    obtain ⟨k, hk, hne⟩ := hyc
    have hy'N : y' ∈ Subgroup.normalClosure ({y'} : Set ↥K) := Subgroup.subset_normalClosure rfl
    have := Subgroup.mem_center_iff.mp (hcen hy'N) ⟨k, hk⟩
    exact hne (congrArg Subtype.val this)

end CFSG.GH74.Uniqueness.SU.K.R6
