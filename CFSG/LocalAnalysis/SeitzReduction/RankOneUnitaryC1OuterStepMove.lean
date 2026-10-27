module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1PushUpStep
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1PushUpCent
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1PushUpMove

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem outerStep_mem_normalizer_szT₁ (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) {C : Subgroup G}
    (hT₁C : szT₁ L T ≤ C) (hCT : C ≤ T) (hsq : ∀ c ∈ C, c ^ 2 ∈ szT₁ L T ⊔ zpowers t)
    (hCK : ∀ c ∈ C, c ∈ szT₁ L T ⊔ zpowers t → c ∈ szT₁ L T) {g : G}
    (hg : g ∈ normalizer (C : Set G)) : g ∈ normalizer (szT₁ L T : Set G) := by
  by_cases hC : C ≤ szT₁ L T
  · have hCeq : C = szT₁ L T := le_antisymm hC hT₁C
    rw [← hCeq]
    exact hg
  · obtain ⟨c, hcC, hcT₁⟩ := Set.not_subset.mp hC
    have hcK : c ∉ szT₁ L T ⊔ zpowers t := fun h1 => hcT₁ (hCK c hcC h1)
    obtain ⟨v, hvT, hv2, hvS⟩ := hv
    have h1K : (1 : G) ∈ szT₁ L T ⊔ zpowers t := one_mem _
    have hcv := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 (hCT hcC) hvT (hsq c hcC)
      (by rw [hv2]; exact h1K) hcK hvS
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hcv
    have htT : t ∈ T := (h.start_of_card_sylow hS2).1
    have hzT : z ∈ T := zpowers_le.mpr htT hz
    have hzv : z * v = v * z := (commute_of_mem_zpowers hz
      (mem_centralizer_singleton_iff.mp (h.le hvT))).symm
    set w := z * v with hwdef
    have hwT : w ∈ T := mul_mem hzT hvT
    have hw2 : w ^ 2 = 1 := by
      have hz2 : z ^ 2 = 1 := by
        rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
        · exact one_pow 2
        · exact h.sq_eq_one
      rw [hwdef, (show Commute z v from hzv).mul_pow, hz2, hv2, one_mul]
    have hwS : w ∉ szT₁ L T ⊔ zpowers t := by
      intro hwS'
      apply hvS
      rw [show v = z⁻¹ * w by rw [hwdef]; group]
      exact mul_mem (mem_sup_right (inv_mem hz)) hwS'
    have hcw : c = y * w := by
      rw [hwdef, ← mul_assoc, hyz]
      group
    have hwC : w ∈ C := by
      rw [show w = y⁻¹ * c by rw [hcw]; group]
      exact mul_mem (inv_mem (hT₁C hy)) hcC
    have hCeq : C = szT₁ L T ⊔ zpowers w := by
      refine le_antisymm (fun c' hc' => ?_) (sup_le hT₁C (zpowers_le.mpr hwC))
      by_cases hc'K : c' ∈ szT₁ L T ⊔ zpowers t
      · exact mem_sup_left (hCK c' hc' hc'K)
      · have hc'w := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 (hCT hc') hwT (hsq c' hc')
          (by rw [hw2]; exact h1K) hc'K hwS
        have hc'wT₁ : c' * w⁻¹ ∈ szT₁ L T := hCK _ (mul_mem hc' (inv_mem hwC)) hc'w
        rw [show c' = (c' * w⁻¹) * w by group]
        exact mul_mem (mem_sup_left hc'wT₁) (mem_sup_right (mem_zpowers w))
    rw [hCeq] at hg
    exact h.pushUp_mem_normalizer_szT₁_of_mem_normalizer hS2 hwT hw2 hwS hg

theorem outerStep_exists_eq_of_centralizer (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) {s : G} (hsT : s ∈ T)
    (hs : ∀ y ∈ szT₁ L T, s * y = y * s) :
    ∃ a ∈ szA₁ (szT₁ L T), ∃ z ∈ zpowers t, s = a * z := by
  obtain ⟨hT₁card, -, hA₁comm, -, -, -, -⟩ := h.facts_of_card_sylow hS2
  have hsA : ∀ a ∈ szA₁ (szT₁ L T), s * a = a * s := fun a ha => hs a (szA₁_le _ ha)
  have hs2 := h.pushUp_sq_mem_of_conj_szA₁ hS2 hsT hsA
  have htC := h.mem_centralizer_szT₁
  by_cases hsK : s ∈ szT₁ L T ⊔ zpowers t
  · obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers htC hsK
    refine ⟨y, mem_szA₁.mpr ⟨hy, mem_centralizer_iff.mpr fun y' hy' => ?_⟩, z, hz, hyz.symm⟩
    have hzy' : y' * z = z * y' :=
      commute_of_mem_zpowers hz (mem_centralizer_iff.mp htC y' hy')
    have hy_eq : y = s * z⁻¹ := by rw [← hyz]; group
    have hzy'' : z⁻¹ * y' = y' * z⁻¹ := by
      calc z⁻¹ * y' = z⁻¹ * (y' * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * y') * z⁻¹ := by rw [hzy']
        _ = y' * z⁻¹ := by group
    rw [hy_eq]
    calc y' * (s * z⁻¹) = (y' * s) * z⁻¹ := by group
      _ = (s * y') * z⁻¹ := by rw [hs y' hy']
      _ = s * (y' * z⁻¹) := by group
      _ = s * (z⁻¹ * y') := by rw [hzy'']
      _ = s * z⁻¹ * y' := by group
  · exfalso
    obtain ⟨v, hvT, hv2, hvS⟩ := hv
    have h1K : (1 : G) ∈ szT₁ L T ⊔ zpowers t := one_mem _
    have hsv := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hsT hvT hs2
      (by rw [hv2]; exact h1K) hsK hvS
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers htC hsv
    have htT : t ∈ T := (h.start_of_card_sylow hS2).1
    have hzT : z ∈ T := zpowers_le.mpr htT hz
    have hzv : z * v = v * z := (commute_of_mem_zpowers hz
      (mem_centralizer_singleton_iff.mp (h.le hvT))).symm
    set w := z * v with hwdef
    have hwT : w ∈ T := mul_mem hzT hvT
    have hw2 : w ^ 2 = 1 := by
      have hz2 : z ^ 2 = 1 := by
        rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
        · exact one_pow 2
        · exact h.sq_eq_one
      rw [hwdef, (show Commute z v from hzv).mul_pow, hz2, hv2, one_mul]
    have hwS : w ∉ szT₁ L T ⊔ zpowers t := by
      intro hwS'
      apply hvS
      rw [show v = z⁻¹ * w by rw [hwdef]; group]
      exact mul_mem (mem_sup_right (inv_mem hz)) hwS'
    have hsw : s = y * w := by
      rw [hwdef, ← mul_assoc, hyz]
      group
    obtain ⟨W, -, -, hWcard, -, -, -, hWiff⟩ := h.exists_W_of_card_sylow hS2 hwT hw2 hwS
    have hT₁W : szT₁ L T ≤ W := by
      intro y' hy'
      refine (hWiff y' hy').mp ?_
      have hconj : w * y' * w⁻¹ = y⁻¹ * y' * y := by
        have e1 : w = y⁻¹ * s := by rw [hsw]; group
        rw [e1]
        calc y⁻¹ * s * y' * (y⁻¹ * s)⁻¹ = y⁻¹ * (s * y') * s⁻¹ * y := by group
          _ = y⁻¹ * (y' * s) * s⁻¹ * y := by rw [hs y' hy']
          _ = y⁻¹ * y' * y := by group
      rw [hconj, hA₁comm]
      have := commutator_mem_commutator (inv_mem hy') (inv_mem hy)
      rw [commutatorElement_def, inv_inv, inv_inv] at this
      rw [show y'⁻¹ * (y⁻¹ * y' * y) = y'⁻¹ * y⁻¹ * y' * y by group]
      exact this
    have hle := card_le_of_le hT₁W
    rw [hT₁card, hWcard] at hle
    have h4 : 4 ≤ 2 ^ f :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
    have : (2 ^ f) ^ 2 < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

theorem outerStep_mem_normalizer_of_normalizer
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) {V : Subgroup G}
    (hVc : ∀ y ∈ szT₁ L T, ∀ u ∈ V, y * u = u * y) (hVab : ∀ u ∈ V, ∀ u' ∈ V, u * u' = u' * u)
    (hVA : szA₁ (szT₁ L T) ≤ V) (hVinv : ∀ u ∈ V, t * u * t⁻¹ = u⁻¹)
    (hTV : T ≤ normalizer (V : Set G)) (hb : ∃ b ∈ V, b ^ 2 ≠ 1) {g : G}
    (hgP : g ∈ normalizer ((T ⊔ V : Subgroup G) : Set G))
    (hgT₁ : g ∈ normalizer (szT₁ L T : Set G)) : g ∈ normalizer (V : Set G) := by
  have htC := h.mem_centralizer_szT₁
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have key : ∀ g' ∈ normalizer ((T ⊔ V : Subgroup G) : Set G),
      g' ∈ normalizer (szT₁ L T : Set G) → ∀ x ∈ V, g' * x * g'⁻¹ ∈ V := by
    intro g' hg'P hg'T
    have main : ∀ x ∈ V, x ^ 2 ≠ 1 → g' * x * g'⁻¹ ∈ V := by
      intro x hx hx2
      have hxP : g' * x * g'⁻¹ ∈ T ⊔ V := (mem_normalizer_iff.mp hg'P x).mp (mem_sup_right hx)
      obtain ⟨s, hs, u, hu, hsu⟩ := ncyc_exists_mul_of_mem_sup hTV hxP
      have hxc : ∀ y ∈ szT₁ L T, (g' * x * g'⁻¹) * y = y * (g' * x * g'⁻¹) := by
        intro y hy
        have hy' : g'⁻¹ * y * g' ∈ szT₁ L T := (mem_normalizer_iff''.mp hg'T y).mp hy
        have h1 := hVc _ hy' x hx
        calc (g' * x * g'⁻¹) * y = g' * (x * (g'⁻¹ * y * g')) * g'⁻¹ := by group
          _ = g' * ((g'⁻¹ * y * g') * x) * g'⁻¹ := by rw [h1]
          _ = y * (g' * x * g'⁻¹) := by group
      have hsc : ∀ y ∈ szT₁ L T, s * y = y * s := by
        intro y hy
        have hs_eq : s = (g' * x * g'⁻¹) * u⁻¹ := by rw [← hsu]; group
        have hu' : u⁻¹ * y = y * u⁻¹ := by
          have h1 := hVc y hy u hu
          calc u⁻¹ * y = u⁻¹ * (y * u) * u⁻¹ := by group
            _ = u⁻¹ * (u * y) * u⁻¹ := by rw [h1]
            _ = y * u⁻¹ := by group
        rw [hs_eq]
        calc g' * x * g'⁻¹ * u⁻¹ * y = (g' * x * g'⁻¹) * (u⁻¹ * y) := by group
          _ = (g' * x * g'⁻¹) * (y * u⁻¹) := by rw [hu']
          _ = ((g' * x * g'⁻¹) * y) * u⁻¹ := by group
          _ = (y * (g' * x * g'⁻¹)) * u⁻¹ := by rw [hxc y hy]
          _ = y * (g' * x * g'⁻¹ * u⁻¹) := by group
      obtain ⟨a, ha, z, hz, hsaz⟩ := h.outerStep_exists_eq_of_centralizer hS2 hv hs hsc
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
      · rw [← hsu, hsaz, hz1, mul_one]
        exact mul_mem (hVA ha) hu
      · rw [hz1] at hsaz
        exfalso
        apply hx2
        have hat : a * t = t * a := (mem_centralizer_iff.mp htC a (szA₁_le _ ha))
        set m := a * u with hm
        have hmV : m ∈ V := mul_mem (hVA ha) hu
        have hxm : g' * x * g'⁻¹ = t * m := by
          rw [← hsu, hsaz, hm, hat, mul_assoc]
        have hsq : (g' * x * g'⁻¹) ^ 2 = 1 := by
          rw [hxm, sq]
          calc t * m * (t * m) = (t * m * t⁻¹) * (t * t) * m := by group
            _ = 1 := by rw [hVinv m hmV, ht2, mul_one, inv_mul_cancel]
        rw [conj_pow] at hsq
        have := congrArg (fun w => g'⁻¹ * w * g') hsq
        simpa [mul_assoc] using this
    intro x hx
    by_cases hx2 : x ^ 2 = 1
    · obtain ⟨b, hbV, hb2⟩ := hb
      have hxb : (x * b) ^ 2 ≠ 1 := by
        rw [sq, show x * b * (x * b) = (x * x) * (b * b) by
          rw [mul_assoc, ← mul_assoc b x b, ← hVab x hx b hbV]; group, ← sq, ← sq, hx2,
          one_mul]
        exact hb2
      have e : g' * x * g'⁻¹ = (g' * (x * b) * g'⁻¹) * (g' * b * g'⁻¹)⁻¹ := by group
      rw [e]
      exact mul_mem (main _ (mul_mem hx hbV) hxb) (inv_mem (main b hbV hb2))
    · exact main x hx hx2
  refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_
  have := key g⁻¹ (inv_mem hgP) (inv_mem hgT₁) x hx
  rwa [inv_inv] at this

end U3Start

theorem u3C1OuterMoveInput_holds : U3C1OuterMoveInput := by
  intro G _ _ L f t T R₂ D d V k h hS2 hR hinv hne hv hC hc hk hnS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hA₁card, -, -, -, hA₁sq, -⟩ := h.facts_of_card_sylow hS2
  have hT₁T : szT₁ L T ≤ T := szT₁_le_left L T
  have hVc : ∀ y ∈ szT₁ L T, ∀ u ∈ V, y * u = u * y := fun y hy u hu =>
    mem_centralizer_iff.mp (hc.le_centralizer hu) y hy
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := f * (k + 1)) (by rw [hc.card, ← pow_mul])
  have hP2 : IsPGroup 2 (T ⊔ V : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' h.isPGroup hV2 hc.T_le
  obtain ⟨z, hzN, hzP, P', hP'2, hPP', hzP'⟩ := exists_normalizer_not_mem_of_not_isSylow hP2 hnS
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup G, N = (T ⊔ V) ⊔ zpowers z := ⟨_, rfl⟩
  have hN2 : IsPGroup 2 N := hNdef ▸ hP'2.to_le (sup_le hPP' (zpowers_le.mpr hzP'))
  have hNP : N ≤ normalizer ((T ⊔ V : Subgroup G) : Set G) :=
    hNdef ▸ sup_le le_normalizer (zpowers_le.mpr hzN)
  have hPN : T ⊔ V ≤ N := hNdef ▸ le_sup_left
  have hzNN : z ∈ N := hNdef ▸ mem_sup_right (mem_zpowers z)
  have hVN : V ≤ N := le_sup_right.trans hPN
  have hU8 := hc.exists_pow_four_ne h hS2 hk
  have hconj : ∀ g ∈ normalizer ((T ⊔ V : Subgroup G) : Set G), ∃ u ∈ V, g⁻¹ * t * g = u * t :=
    fun g hg => (h.pushUp_exists_mul_t_of_conj_normalizer hS2 hVc hc.comm hc.le
      (fun u hu htu => hc.mem_szA₁_of_conj_eq hu htu) hc.T_le hU8 (hc.sign h hS2 hC) hv hP2
      hg).2 hc.inv
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({t} : Set G)) := by
    obtain ⟨P₀, hP₀⟩ := h.sylow
    exact ⟨P₀, by rw [hP₀, subgroupOf_map_subtype, inf_eq_left.mpr h.le]⟩
  obtain ⟨J, hJdef⟩ : ∃ J : Set G, J = {x | ∃ g ∈ N, x = g⁻¹ * t * g} := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = (T ⊔ V) ⊓ centralizer J := ⟨_, rfl⟩
  have hmemJ : ∀ x, x ∈ J ↔ ∃ g ∈ N, x = g⁻¹ * t * g := fun x => by rw [hJdef]; rfl
  have hmemC : ∀ c, c ∈ C ↔ c ∈ T ⊔ V ∧ ∀ x ∈ J, x * c = c * x := fun c => by
    rw [hCdef, mem_inf, mem_centralizer_iff]
  have htJ : t ∈ J := (hmemJ t).mpr ⟨1, one_mem _, by group⟩
  have hJN : ∀ n ∈ N, ∀ x ∈ J, n⁻¹ * x * n ∈ J := by
    intro n hn x hx
    obtain ⟨g, hg, rfl⟩ := (hmemJ x).mp hx
    exact (hmemJ _).mpr ⟨g * n, mul_mem hg hn, by group⟩
  have hCN : ∀ n ∈ N, n ∈ normalizer (C : Set G) := by
    have key : ∀ n' ∈ N, ∀ c ∈ C, n' * c * n'⁻¹ ∈ C := by
      intro n' hn' c hc'
      obtain ⟨hcP, hcJ⟩ := (hmemC c).mp hc'
      refine (hmemC _).mpr ⟨(mem_normalizer_iff.mp (hNP hn') c).mp hcP, fun x hx => ?_⟩
      have h1 := hcJ _ (hJN n' hn' x hx)
      calc x * (n' * c * n'⁻¹) = n' * ((n'⁻¹ * x * n') * c) * n'⁻¹ := by group
        _ = n' * (c * (n'⁻¹ * x * n')) * n'⁻¹ := by rw [h1]
        _ = n' * c * n'⁻¹ * x := by group
    intro n hn
    refine mem_normalizer_iff.mpr fun c => ⟨fun hc' => key n hn c hc', fun hc' => ?_⟩
    have := key n⁻¹ (inv_mem hn) _ hc'
    rwa [show n⁻¹ * (n * c * n⁻¹) * n⁻¹⁻¹ = c by group] at this
  have hCt : C ≤ centralizer ({t} : Set G) := fun c hc' =>
    mem_centralizer_singleton_iff.mpr (((hmemC c).mp hc').2 t htJ).symm
  have hCP : C ≤ T ⊔ V := fun c hc' => ((hmemC c).mp hc').1
  have hCT : C ≤ T := by
    have heq := hTsyl.eq_of_le (le_sup_left : T ≤ T ⊔ C) (sup_le h.le hCt)
      (hP2.to_le (sup_le le_sup_left hCP))
    rw [← heq]
    exact le_sup_right
  have hT₁C : szT₁ L T ≤ C := by
    intro y hy
    refine (hmemC y).mpr ⟨mem_sup_left (hT₁T hy), fun x hx => ?_⟩
    obtain ⟨g, hg, rfl⟩ := (hmemJ x).mp hx
    obtain ⟨u, hu, hgu⟩ := hconj g (hNP hg)
    rw [hgu]
    have hyt : y * t = t * y := mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy
    calc u * t * y = u * (t * y) := by group
      _ = u * (y * t) := by rw [hyt]
      _ = (u * y) * t := by group
      _ = (y * u) * t := by rw [hVc y hy u hu]
      _ = y * (u * t) := by group
  have hCsq : ∀ c ∈ C, ∀ x ∈ V, c * x ^ 2 = x ^ 2 * c := by
    intro c hc' x hx
    have hcJ := ((hmemC c).mp hc').2
    have h1 : t * c = c * t := hcJ t htJ
    have hxJ : x⁻¹ * t * x ∈ J := (hmemJ _).mpr ⟨x, hVN hx, rfl⟩
    have h2 := hcJ _ hxJ
    have htx : t * x = x⁻¹ * t := by
      have := hc.inv x hx
      calc t * x = t * x * t⁻¹ * t := by group
        _ = x⁻¹ * t := by rw [this]
    have h3 : x⁻¹ * t * x = (x ^ 2)⁻¹ * t := by
      rw [mul_assoc, htx]
      group
    rw [h3] at h2
    have h4 : (x ^ 2)⁻¹ * c = c * (x ^ 2)⁻¹ := by
      calc (x ^ 2)⁻¹ * c = (x ^ 2)⁻¹ * (c * t) * t⁻¹ := by group
        _ = (x ^ 2)⁻¹ * (t * c) * t⁻¹ := by rw [h1]
        _ = ((x ^ 2)⁻¹ * t * c) * t⁻¹ := by group
        _ = (c * ((x ^ 2)⁻¹ * t)) * t⁻¹ := by rw [h2]
        _ = c * (x ^ 2)⁻¹ := by group
    calc c * x ^ 2 = x ^ 2 * ((x ^ 2)⁻¹ * c) * x ^ 2 := by group
      _ = x ^ 2 * (c * (x ^ 2)⁻¹) * x ^ 2 := by rw [h4]
      _ = x ^ 2 * c := by group
  have hq0 : 0 < 2 ^ f := by positivity
  have hA₁V2 : ∀ a ∈ szA₁ (szT₁ L T), ∃ x ∈ V, x ^ 2 = a := by
    intro a ha
    obtain ⟨z', hz'V, hz'⟩ := pushUp_exists_pow_eq hc.comm hq0 hc.card hc.pow hc.omega
      (le_of_eq hA₁card) (show 1 ≤ k + 1 by omega) (hc.le ha)
      (by rw [pow_one]; exact hA₁sq a ha)
    refine ⟨z' ^ 2 ^ (k - 1), pow_mem hz'V _, ?_⟩
    have e : 2 ^ (k - 1) * 2 = 2 ^ (k + 1 - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [← hz', ← pow_mul, e]
  have hCA₁ : ∀ c ∈ C, ∀ a ∈ szA₁ (szT₁ L T), c * a = a * c := by
    intro c hc' a ha
    obtain ⟨x, hx, rfl⟩ := hA₁V2 a ha
    exact hCsq c hc' x hx
  have hCsq' : ∀ c ∈ C, c ^ 2 ∈ szT₁ L T ⊔ zpowers t := fun c hc' =>
    h.pushUp_sq_mem_of_conj_szA₁ hS2 (hCT hc') (hCA₁ c hc')
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := hU8
  have hb₀4 : b₀ ^ 4 ≠ 1 := by
    have := (hab₀ 0).1
    rwa [zpow_zero, one_mul] at this
  have hCK : ∀ c ∈ C, c ∈ szT₁ L T ⊔ zpowers t → c ∈ szT₁ L T := by
    intro c hc' hcK
    obtain ⟨y, hy, z', hz', hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hcK
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz' with hz1 | hz1
    · rw [← hyz, hz1, mul_one]
      exact hy
    · exfalso
      apply hb₀4
      have h1 := hCsq c hc' b₀ hb₀
      rw [← hyz, hz1] at h1
      have hti : t * b₀ ^ 2 * t⁻¹ = (b₀ ^ 2)⁻¹ := hc.inv _ (pow_mem hb₀ 2)
      have hyc : y * (b₀ ^ 2)⁻¹ = (b₀ ^ 2)⁻¹ * y := hVc y hy _ (inv_mem (pow_mem hb₀ 2))
      have h2 : (b₀ ^ 2)⁻¹ = b₀ ^ 2 := by
        calc (b₀ ^ 2)⁻¹ = (b₀ ^ 2)⁻¹ * y * y⁻¹ := by group
          _ = y * (b₀ ^ 2)⁻¹ * y⁻¹ := by rw [hyc]
          _ = y * (t * b₀ ^ 2 * t⁻¹) * y⁻¹ := by rw [hti]
          _ = (y * t * b₀ ^ 2) * (y * t)⁻¹ := by group
          _ = (b₀ ^ 2 * (y * t)) * (y * t)⁻¹ := by rw [h1]
          _ = b₀ ^ 2 := by group
      calc b₀ ^ 4 = b₀ ^ 2 * b₀ ^ 2 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
        _ = b₀ ^ 2 * (b₀ ^ 2)⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel _
  have hNT₁ : ∀ n ∈ N, n ∈ normalizer (szT₁ L T : Set G) := fun n hn =>
    h.outerStep_mem_normalizer_szT₁ hS2 hv hT₁C hCT hCsq' hCK (hCN n hn)
  have hb : ∃ b ∈ V, b ^ 2 ≠ 1 := ⟨b₀, hb₀, fun h2 => hb₀4 (by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, one_pow])⟩
  have hNV : ∀ n ∈ N, n ∈ normalizer (V : Set G) := fun n hn =>
    h.outerStep_mem_normalizer_of_normalizer hS2 hv hVc hc.comm hc.le hc.inv hc.T_le hb (hNP hn)
      (hNT₁ n hn)
  have hNR : ∀ n ∈ N, n ∈ normalizer (szR (szT₁ L T) V t : Set G) := by
    intro n hn
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => ?_
    have hle : szR (szT₁ L T) V t ≤
        (szR (szT₁ L T) V t).comap (MulAut.conj n⁻¹).toMonoidHom := by
      refine sup_le (sup_le (fun y hy => ?_) (fun u hu => ?_)) (zpowers_le.mpr ?_)
      · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        exact le_szR_left _ _ _ ((mem_normalizer_iff''.mp (hNT₁ n hn) y).mp hy)
      · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        exact le_szR_mid _ _ _ ((mem_normalizer_iff''.mp (hNV n hn) u).mp hu)
      · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        obtain ⟨u, hu, hnu⟩ := hconj n (hNP hn)
        rw [hnu]
        exact mul_mem (le_szR_mid _ _ _ hu) (mem_szR_right _ _ _)
    have := hle hr
    simpa using this
  obtain ⟨u, hu, hzu⟩ := hconj z⁻¹ (inv_mem hzN)
  rw [inv_inv] at hzu
  refine ⟨z, hNR z hzNN, u, hu, fun x hx hxu => hzP ?_, hzu⟩
  have htx' : t * x⁻¹ = x * t := by
    have := hc.inv x⁻¹ (inv_mem hx)
    rw [inv_inv] at this
    calc t * x⁻¹ = t * x⁻¹ * t⁻¹ * t := by group
      _ = x * t := by rw [this]
  have hzt : z * t = x ^ 2 * t * z := by
    calc z * t = (z * t * z⁻¹) * z := by group
      _ = u * t * z := by rw [hzu]
      _ = x ^ 2 * t * z := by rw [← hxu]
  have hc' : (x⁻¹ * z) * t = t * (x⁻¹ * z) := by
    calc (x⁻¹ * z) * t = x⁻¹ * (z * t) := by group
      _ = x⁻¹ * (x ^ 2 * t * z) := by rw [hzt]
      _ = x * t * z := by group
      _ = (t * x⁻¹) * z := by rw [htx']
      _ = t * (x⁻¹ * z) := by group
  have hH : T ⊔ zpowers (x⁻¹ * z) ≤ centralizer ({t} : Set G) :=
    sup_le h.le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hc'))
  have hHN : T ⊔ zpowers (x⁻¹ * z) ≤ N :=
    sup_le (le_sup_left.trans hPN) (zpowers_le.mpr (mul_mem (inv_mem (hVN hx)) hzNN))
  have heq := hTsyl.eq_of_le le_sup_left hH (hN2.to_le hHN)
  have hxzT : x⁻¹ * z ∈ T := by
    rw [← heq]
    exact mem_sup_right (mem_zpowers _)
  rw [show z = x * (x⁻¹ * z) by group]
  exact mul_mem (mem_sup_right hx) (mem_sup_left hxzT)

end CFSG.SeitzReduction.RankOne
