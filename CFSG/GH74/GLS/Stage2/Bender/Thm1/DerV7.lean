module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.ConjV7
public import CFSG.GH74.GLS.Stage2.Local.Closed
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.Lemma23d
public import CFSG.GH74.GLS.Stage2.Local.Lemma23e

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Three

variable {G : Type} [Group G] [Finite G]

theorem exists_order_three_conj {z : G} {V : Subgroup G} (h3 : 3 ∣ AutOrd (Cen z) V) :
    ∃ g ∈ Cen z, ∃ σ : MulAut ↥V, orderOf σ = 3 ∧ ∀ v : ↥V, ((σ v : ↥V) : G) = g * v * g⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup G := normalizer (V : Set G) ⊓ Cen z
  have hNle : N ≤ normalizer (V : Set G) := inf_le_left
  let α : ↥N →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hNle)
  have hker : α.ker = (centralizer (V : Set G) ⊓ Cen z).subgroupOf N := by
    ext ⟨g, hg⟩
    have h1 : α ⟨g, hg⟩ = 1 ↔ g ∈ centralizer (V : Set G) := by
      have := Subgroup.normalizerMonoidHom_ker V
      have h2 : (⟨g, hNle hg⟩ : ↥(normalizer (V : Set G))) ∈ V.normalizerMonoidHom.ker ↔
          g ∈ centralizer (V : Set G) := by
        rw [this]; exact Iff.rfl
      rw [← h2]; exact Iff.rfl
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, h1]
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, hg.2⟩, fun h => h.1⟩
  have hcard : Nat.card α.range = AutOrd (Cen z) V := by
    rw [← Subgroup.index_ker, hker]; rfl
  have h3dvd : 3 ∣ Nat.card α.range := by rw [hcard]; exact h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hσ : orderOf (x : MulAut ↥V) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨g, hg⟩ := x.2
  refine ⟨(g : G), g.2.2, (x : MulAut ↥V), hσ, fun v => ?_⟩
  rw [← hg]
  rfl

theorem conj_of_three_dvd {z : G} {V : Subgroup G} (h4 : IVK.IsFourSubgroup V)
    (h3 : 3 ∣ AutOrd (Cen z) V) :
    ∀ v ∈ V, v ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ c ∈ Cen z, c * v * c⁻¹ = w := by
  have hEA : IsElementaryAbelian 2 ↥V := h4.1
  have hcardV : Nat.card ↥V = 4 := h4.2
  have : IsKleinFour ↥V := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hVne : V ≠ ⊥ := by
      intro hb
      rw [hb] at hcardV
      simp at hcardV
    have : Nontrivial ↥V := (Subgroup.nontrivial_iff_ne_bot V).mpr hVne
    exact ⟨hcardV, hEA.exponent_eq_prime⟩
  obtain ⟨g, hgC, σ, hσ, hσg⟩ := exists_order_three_conj h3
  have hfix : ∀ u : ↥V, σ u = u → u = 1 := fun u hu => klein_aut_order_three_fixed_free σ hσ hu
  have hσ3 : σ * σ * σ = 1 := by
    have : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    simpa [pow_succ] using this
  intro v hv hv1 w hw hw1
  set v' : ↥V := ⟨v, hv⟩ with hv'
  set w' : ↥V := ⟨w, hw⟩ with hw'
  have hv'1 : v' ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  have hw'1 : w' ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  have hs1 : σ v' ≠ 1 := fun h => hv'1 (σ.injective (by rw [h, map_one]))
  have hsv : σ v' ≠ v' := fun h => hv'1 (hfix v' h)
  have hs2_1 : σ (σ v') ≠ 1 := fun h => hs1 (σ.injective (by rw [h, map_one]))
  have hs2_s : σ (σ v') ≠ σ v' := fun h => hsv (σ.injective h)
  have hs2_v : σ (σ v') ≠ v' := by
    intro h
    apply hsv
    have h1 : σ (σ (σ v')) = σ v' := by rw [h]
    have h2 : σ (σ (σ v')) = v' := by
      have := congrArg (fun m : MulAut ↥V => m v') hσ3
      simpa using this
    exact h1.symm.trans h2
  have hs2 : σ (σ v') = v' * σ v' :=
    IsKleinFour.eq_mul_of_ne_all hv'1 hs1 (Ne.symm hsv) hs2_1 hs2_v hs2_s
  have hcases : w' = v' ∨ w' = σ v' ∨ w' = σ (σ v') := by
    by_cases h1 : w' = v'
    · exact Or.inl h1
    by_cases h2 : w' = σ v'
    · exact Or.inr (Or.inl h2)
    right; right
    rw [hs2]
    exact IsKleinFour.eq_mul_of_ne_all hv'1 hs1 (Ne.symm hsv) hw'1 h1 h2
  have hgcon : ∀ u : ↥V, ((σ u : ↥V) : G) = g * u * g⁻¹ := hσg
  rcases hcases with h | h | h
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    calc 1 * v * (1 : G)⁻¹ = v := by group
      _ = w := (congrArg Subtype.val h).symm
  · refine ⟨g, hgC, ?_⟩
    have := congrArg Subtype.val h
    rw [hgcon] at this
    exact this.symm
  · refine ⟨g * g, Subgroup.mul_mem _ hgC hgC, ?_⟩
    have := congrArg Subtype.val h
    rw [hgcon, hgcon] at this
    calc g * g * v * (g * g)⁻¹ = g * (g * v * g⁻¹) * g⁻¹ := by group
      _ = w := this.symm

end Three

section Main7

variable {G : Type} [Group G]

theorem isCentralInvolution_of_isConj' {z x : G} (hz : IsCentralInvolution z) (h : IsConj z x) :
    IsCentralInvolution x := by
  obtain ⟨hord, S₀, hzS, hzc⟩ := hz
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨?_, c • S₀, ?_, ?_⟩
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z
    rw [MulAut.conj_apply] at h1
    rw [← hc, h1]
    exact hord
  · rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨z, hzS, by rw [← hc]; rfl⟩
  · intro s hs
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have := hzc s' hs'
    rw [← hc]
    show (c * s' * c⁻¹) * (c * z * c⁻¹) = (c * z * c⁻¹) * (c * s' * c⁻¹)
    calc (c * s' * c⁻¹) * (c * z * c⁻¹) = c * (s' * z) * c⁻¹ := by group
      _ = c * (z * s') * c⁻¹ := by rw [this]
      _ = (c * z * c⁻¹) * (c * s' * c⁻¹) := by group

theorem conjugate_of_center {c : G} (hc : c ∈ Subgroup.center G) (L : Subgroup G) :
    conjugate L c = L := by
  ext x
  rw [mem_conjugate_iff]
  have : c * x * c⁻¹ = x := by
    have h := Subgroup.mem_center_iff.mp hc x
    calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [← h]
      _ = x := by group
  rw [this]

end Main7

section V7Exists

variable {G : Type} [Group G] [Finite G]

theorem v7_exists_of (h33 : IVK_3_3_lift) : V7_exists := by
  intro G _ _ z k S ctx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z) := ctx.sylow
  have hSC : S ≤ Cen z := hSsyl.le
  obtain ⟨V₀, t₀, hV₀L, hV₀4, hV₀3, ht₀S, ht₀c, ht₀C⟩ : ∃ (V₀ : Subgroup G) (t₀ : G),
      V₀ ≤ LC z ∧ IVK.IsFourSubgroup V₀ ∧ (AutOrd (Cen z) V₀ = 3 ∨ AutOrd (Cen z) V₀ = 6) ∧
      t₀ ∈ S ∧ (∀ v ∈ V₀, t₀ * v = v * t₀) ∧ (CaseC z S → IsConj z t₀ ∧ t₀ ≠ z) := by
    by_cases hC : CaseC z S
    · obtain ⟨q, L₁, L₂, x, hpair, htwo⟩ := hC
      obtain ⟨t, htS, htconj, hswap⟩ := htwo.swap_exists
      obtain ⟨-, -, -, V, hVL, hV4, hV3, hVt⟩ := htwo.swap_conseq t htS htconj hswap
      refine ⟨V, t, hVL, hV4, hV3, htS, hVt, fun _ => ⟨htconj, ?_⟩⟩
      intro htz
      apply hpair.ne
      obtain ⟨ht, h1, h2⟩ := hswap
      have hcen : toBar z ⟨t, ht⟩ ∈ Subgroup.center (CentralizerBar z) := by
        have : (⟨t, ht⟩ : ↥(Cen z)) = ⟨z, mem_Cen_self z⟩ := Subtype.ext htz
        rw [this]
        exact toBar_z_mem_center z
      exact (h1.symm.trans (conjugate_of_center hcen L₁)).symm
    · obtain ⟨V, hVL, hV4, hV3⟩ := h33 G z k S ctx
      exact ⟨V, 1, hVL, hV4, hV3, S.one_mem, fun v _ => by simp, fun h => absurd h hC⟩
  have hV₀C : V₀ ≤ Cen z := hV₀L.trans (LC_le_Cen z)
  have ht₀C' : t₀ ∈ Cen z := hSC ht₀S
  have hWC : V₀ ⊔ zpowers t₀ ≤ Cen z := sup_le hV₀C (Subgroup.zpowers_le.mpr ht₀C')
  have hcomm : ∀ a ∈ V₀, ∀ b ∈ zpowers t₀, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a t₀ from (ht₀c a ha).symm) n).eq
  have hW2 : IsPGroup 2 ↥(V₀ ⊔ zpowers t₀) := by
    obtain ⟨a, ha⟩ := orderOf_mem_S ctx ht₀S
    have : IsElementaryAbelian 2 ↥V₀ := hV₀4.1
    intro w
    obtain ⟨v, hv, u, hu, hwvu⟩ := exists_mul_of_mem_sup_of_commute hcomm w.2
    refine ⟨a + 1, ?_⟩
    apply Subtype.ext
    have hv2 : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have ht0 : t₀ ^ (2 ^ a) = 1 := by rw [← ha]; exact pow_orderOf_eq_one t₀
    have hu1 : (t₀ ^ m) ^ (2 ^ a) = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht0, one_zpow]
    have hc : Commute v (t₀ ^ m) := hcomm v hv _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers t₀) m)
    have hv' : v ^ 2 ^ (a + 1) = 1 := by rw [pow_succ', pow_mul, hv2, one_pow]
    have hu' : (t₀ ^ m) ^ 2 ^ (a + 1) = 1 := by rw [pow_succ, pow_mul, hu1, one_pow]
    show ((w : G)) ^ (2 ^ (a + 1)) = 1
    rw [hwvu, hc.mul_pow, hv', hu', one_mul]
  have hW' : IsPGroup 2 ↥((V₀ ⊔ zpowers t₀).subgroupOf (Cen z)) := hW2.comap_subtype
  obtain ⟨Q, hWQ⟩ := hW'.exists_le_sylow
  have hP' : CFSG.ABGLocalTools.IsSylowOf 2 ((Q : Subgroup ↥(Cen z)).map (Cen z).subtype) (Cen z) :=
    ⟨Q, rfl⟩
  obtain ⟨kk, hkk, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hSsyl hP'
  have hWP' : ∀ w ∈ V₀ ⊔ zpowers t₀, kk⁻¹ * w * kk ∈ S := fun w hw =>
    (hconj w).mp ⟨⟨w, hWC hw⟩, hWQ (Subgroup.mem_subgroupOf.mpr hw), rfl⟩
  have hV₀W : V₀ ≤ V₀ ⊔ zpowers t₀ := le_sup_left
  have ht₀W : t₀ ∈ V₀ ⊔ zpowers t₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀)
  have hV4 : IVK.IsFourSubgroup (conjugate V₀ kk) := isFour_conjugate kk hV₀4
  have hV3 : 3 ∣ AutOrd (Cen z) (conjugate V₀ kk) := by
    rw [autOrd_conjugate hkk]
    rcases hV₀3 with h | h
    · rw [h]
    · rw [h]; decide
  have hVL : conjugate V₀ kk ≤ LC z := conjugate_le_LC hkk hV₀L
  have hconjV := conj_of_three_dvd hV4 hV3
  refine ⟨conjugate V₀ kk, ?_, hVL, hV4, hV3, hconjV, ?_⟩
  · intro v hv
    rw [mem_conjugate_iff] at hv
    have h1 := hWP' (kk * v * kk⁻¹) (hV₀W hv)
    have e : kk⁻¹ * (kk * v * kk⁻¹) * kk = v := by group
    rwa [e] at h1
  · intro hC
    obtain ⟨hconjz, hz'ne⟩ := ht₀C hC
    obtain ⟨q, L₁, L₂, x, hpair, htwo⟩ := hC
    refine ⟨?_, kk⁻¹ * t₀ * kk, hWP' t₀ ht₀W, ?_, ?_, ?_⟩
    · intro v hv hv2 hvz
      have hvL : v ∈ LC z := hVL hv
      have hvne : v ≠ z := by
        intro hvz'
        have hzV : z ∈ conjugate V₀ kk := hvz' ▸ hv
        have hz1 : z ≠ 1 := by
          intro h
          have := ctx.orderOf_z
          rw [h, orderOf_one] at this
          omega
        obtain ⟨x1, hx1, y1, hy1, hx1o, hy1o, hxy⟩ := exists_two_involutions_of_isFour hV4
        have hx1z : x1 = z := by
          obtain ⟨c, hc, hcz⟩ := hconjV z hzV hz1 x1 hx1 (fun h => by rw [h, orderOf_one] at hx1o; omega)
          have := Subgroup.mem_centralizer_singleton_iff.mp hc
          rw [← hcz, this]; group
        have hy1z : y1 = z := by
          obtain ⟨c, hc, hcz⟩ := hconjV z hzV hz1 y1 hy1 (fun h => by rw [h, orderOf_one] at hy1o; omega)
          have := Subgroup.mem_centralizer_singleton_iff.mp hc
          rw [← hcz, this]; group
        exact hxy (hx1z.trans hy1z.symm)
      have hxv : IsConj x v := (htwo.invol_L v hvL hv2 hvne).1
      have hzx : IsConj z x := hvz.trans hxv.symm
      exact htwo.x_nonCentral (isCentralInvolution_of_isConj' ctx.central hzx)
    · obtain ⟨c, hc⟩ := isConj_iff.1 hconjz
      refine isConj_iff.2 ⟨kk⁻¹ * c, ?_⟩
      calc kk⁻¹ * c * z * (kk⁻¹ * c)⁻¹ = kk⁻¹ * (c * z * c⁻¹) * kk := by group
        _ = kk⁻¹ * t₀ * kk := by rw [hc]
    · intro h
      apply hz'ne
      have hkz : kk * z * kk⁻¹ = z := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hkk
        rw [this]; group
      calc t₀ = kk * (kk⁻¹ * t₀ * kk) * kk⁻¹ := by group
        _ = z := by rw [h, hkz]
    · intro v hv
      rw [mem_conjugate_iff] at hv
      have h1 := ht₀c _ hv
      calc kk⁻¹ * t₀ * kk * v = kk⁻¹ * (t₀ * (kk * v * kk⁻¹)) * kk := by group
        _ = kk⁻¹ * ((kk * v * kk⁻¹) * t₀) * kk := by rw [h1]
        _ = v * (kk⁻¹ * t₀ * kk) := by group

end V7Exists

end CFSG.GH74.GLS.Stage2.Bender.Thm1
