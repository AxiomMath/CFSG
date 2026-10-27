module

public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoPat
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoFus
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoCent
public import CFSG.GH74.GLS.Stage2.Local.P27.P1Main
public import CFSG.GH74.GLS.Stage1.Main.BridgeField
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P27 CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Main

section Small

variable {G : Type} [Group G]

theorem U4_eq_of_isFourSubgroup {z t : G} (hu : UData z t) {U : Subgroup G}
    (hU4 : IVK.IsFourSubgroup U) (hzU : z ∈ U) (htU : t ∈ U) : U = U4 z t := by
  have hle : U4 z t ≤ U := sup_le ((Subgroup.zpowers_le).2 hzU) ((Subgroup.zpowers_le).2 htU)
  have hV := CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions z t hu.z_sq hu.t_sq
    hu.z_ne hu.t_ne hu.zt_ne hu.comm
  have hEq : U4 z t =
      CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions z t hu.z_sq hu.t_sq hu.comm := by
    ext a
    rw [mem_U4_iff hu]
    show _ ↔ a ∈ ({z * t, z, t, 1} : Set G)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hc : Nat.card ↥(U4 z t) = 4 := by rw [hEq]; exact hV.card_four
  have : Finite ↥U := Nat.finite_of_card_ne_zero (by rw [hU4.2]; norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hU4.2, hc])).symm

theorem not_swaps_self {z : G} {L₁ L₂ : Subgroup (CentralizerBar z)} (hne : L₁ ≠ L₂) :
    ¬ Swaps z z L₁ L₂ := by
  rintro ⟨hzC, hc1, -⟩
  have hcen : ∀ y : CentralizerBar z, toBar z ⟨z, hzC⟩ * y = y * toBar z ⟨z, hzC⟩ := by
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
    show toBar z ⟨z, hzC⟩ * toBar z w = toBar z w * toBar z ⟨z, hzC⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 w.2).symm
  have hid : (MulAut.conj (toBar z ⟨z, hzC⟩)⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext x
    show (toBar z ⟨z, hzC⟩)⁻¹ * x * ((toBar z ⟨z, hzC⟩)⁻¹)⁻¹ = x
    rw [inv_inv]
    calc (toBar z ⟨z, hzC⟩)⁻¹ * x * toBar z ⟨z, hzC⟩
        = (toBar z ⟨z, hzC⟩)⁻¹ * (x * toBar z ⟨z, hzC⟩) := by group
      _ = (toBar z ⟨z, hzC⟩)⁻¹ * (toBar z ⟨z, hzC⟩ * x) := by rw [hcen x]
      _ = x := by group
  have h1 : conjugate L₁ (toBar z ⟨z, hzC⟩) = L₁ := by
    unfold conjugate
    rw [hid, Subgroup.map_id]
  exact hne (h1.symm.trans hc1)

theorem centralizer_U4_eq {z t : G} (hzz : z * z = 1) :
    centralizer ((U4 z t : Subgroup G) : Set G) = centralizer ({t * z, z} : Set G) := by
  ext c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    rcases hg with rfl | hg
    · exact h _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)))
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact h _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  · intro h g hg
    have hz : z * c = c * z := h z (Set.mem_insert_of_mem _ rfl)
    have htz : t * z * c = c * (t * z) := h (t * z) (Set.mem_insert _ _)
    have ht : t * c = c * t := by
      calc t * c = t * (z * z) * c := by rw [hzz, mul_one]
        _ = (t * z) * (z * c) := by group
        _ = (t * z) * (c * z) := by rw [hz]
        _ = ((t * z) * c) * z := by group
        _ = (c * (t * z)) * z := by rw [htz]
        _ = c * (t * (z * z)) := by group
        _ = c * t := by rw [hzz, mul_one]
    have hle : U4 z t ≤ centralizer ({c} : Set G) :=
      sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 hz))
        ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 ht))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

theorem swaps_transport {z t : G} {L₁ L₂ L₁' L₂' : Subgroup (CentralizerBar z)} (hne : L₁ ≠ L₂)
    (hset : ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) = {L₁', L₂'}) (hsw : Swaps z t L₁ L₂) :
    Swaps z t L₁' L₂' := by
  have h1 : L₁ ∈ ({L₁', L₂'} : Set (Subgroup (CentralizerBar z))) := hset ▸ Set.mem_insert _ _
  have h2 : L₂ ∈ ({L₁', L₂'} : Set (Subgroup (CentralizerBar z))) :=
    hset ▸ Set.mem_insert_of_mem _ rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  obtain ⟨htC, hc1, hc2⟩ := hsw
  rcases h1 with rfl | rfl
  · rcases h2 with rfl | rfl
    · exact absurd rfl hne
    · exact ⟨htC, hc1, hc2⟩
  · rcases h2 with rfl | rfl
    · exact ⟨htC, hc2, hc1⟩
    · exact absurd rfl hne

theorem le_of_isSylowOf_centralizer {U T : Subgroup G} (hU2 : IsPGroup 2 ↥U)
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hT : IsSylowOf 2 T (centralizer (U : Set G))) : U ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hT
  have hUC : U ≤ centralizer (U : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun v hv => hUc v hv u hu
  have hn : (U.subgroupOf (centralizer (U : Set G))).Normal := ⟨fun n hn g => by
    have hnU : (n : G) ∈ U := hn
    have hg : (n : G) * (g : G) = (g : G) * (n : G) :=
      Subgroup.mem_centralizer_iff.1 g.2 (n : G) hnU
    show ((g * n * g⁻¹ : ↥(centralizer (U : Set G))) : G) ∈ U
    have : ((g * n * g⁻¹ : ↥(centralizer (U : Set G))) : G) = n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (g : G) * n * (g : G)⁻¹ = n * g * (g : G)⁻¹ := by rw [← hg]
        _ = n := by group
    rw [this]
    exact hnU⟩
  have hN2 : IsPGroup 2 ↥(U.subgroupOf (centralizer (U : Set G))) := hU2.comap_subtype
  have hle := hN2.le_sylow_of_normal Q
  intro u hu
  rw [← hQ]
  exact ⟨⟨u, hUC hu⟩, hle (Subgroup.mem_subgroupOf.2 hu), rfl⟩

end Small

section Rank

variable {G : Type} [Group G] [Finite G]

theorem noE32_of_pRank_le_four (h : pRank 2 G ≤ 4) : NoE32 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E hcomm hsq
  have hel : IsElementaryAbelian 2 ↥E := isElementaryAbelian_two_of hcomm hsq
  have hE2 : IsPGroup 2 ↥E := fun g => ⟨1, by
    have := hsq g g.2
    simpa [pow_two] using Subtype.ext this⟩
  obtain ⟨n, hn⟩ := hE2.exists_card_eq
  have hn4 : n ≤ 4 :=
    (CFSG.LieType.SteinbergBR.le_pRank_of_card (by norm_num) E hel hn).trans h
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn4
    _ = 16 := by norm_num

end Rank

section Main

variable {G : Type} [Group G] [Finite G]

theorem data52_of_pattern {z : G} {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    {x₀ : G} (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z))
    (hP : Stage1Pair G z S q L₁ L₂) (hx : TwoClassData G z S L₁ L₂ q x₀)
    (hpat : ∀ t' ∈ S, t' * t' = 1 → Swaps z t' L₁ L₂ →
      (IsConj z t' ∧ ¬ IsConj z (z * t')) ∨ (IsConj z (z * t') ∧ ¬ IsConj z t'))
    {U : Subgroup G} (hUS : U ≤ S) (hU4 : IVK.IsFourSubgroup U) (hzU : z ∈ U) {t₁ : G}
    (ht₁U : t₁ ∈ U) (hsw₁ : Swaps z t₁ L₁ L₂) :
    ∃ t : G, t ∈ S ∧ UData z t ∧ U = U4 z t ∧
      (∃ D : Subgroup G, IsInternalDirectProduct (zpowers z ⊔ zpowers t) D
        (S ⊓ centralizer ({t} : Set G)) ∧ IsDihedral ↥D) ∧
      (∃ q' : ℕ, Odd q' ∧ 3 < q' ∧
        IVK.IsL2 (↥(pLayerOf 2 (centralizer ((U4 z t : Subgroup G) : Set G))) ⧸
          pPrimeCore 2 ↥(pLayerOf 2 (centralizer ((U4 z t : Subgroup G) : Set G))))
          (fun r => r = q')) ∧
      (∀ x₁ : G, IsNonCentralInvolution x₁ → IsConj x₁ (z * t)) := by
  obtain ⟨hU1, hU2⟩ := IVK.isFourSubgroup_props hU4
  have hzz : z * z = 1 := hU2 z hzU
  have hzS : z ∈ S := hUS hzU
  have ht₁S : t₁ ∈ S := hUS ht₁U
  have ht₁2 : t₁ * t₁ = 1 := hU2 t₁ ht₁U
  have hzt₁S : z * t₁ ∈ S := S.mul_mem hzS ht₁S
  obtain ⟨t, htU, htS, htsw, htc, hnc⟩ :
      ∃ t ∈ U, t ∈ S ∧ Swaps z t L₁ L₂ ∧ IsConj z t ∧ ¬ IsConj z (z * t) := by
    rcases hpat t₁ ht₁S ht₁2 hsw₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨t₁, ht₁U, ht₁S, hsw₁, h1, h2⟩
    · refine ⟨z * t₁, U.mul_mem hzU ht₁U, hzt₁S, swaps_mul_z hsw₁, h1, ?_⟩
      rw [← mul_assoc, hzz, one_mul]
      exact h2
  have hz1 : z ≠ 1 := by
    intro h
    have := hz.1
    rw [h, orderOf_one] at this
    omega
  have ht1 : t ≠ 1 := by
    intro h
    rw [h] at htc
    exact hz1 (isConj_one_left.1 htc)
  have hzt : z ≠ t := by
    intro h
    rw [← h] at htsw
    exact not_swaps_self hP.ne htsw
  have hu : UData z t :=
    { z_sq := hzz
      t_sq := hU2 t htU
      comm := hU1 z hzU t htU
      z_ne := hz1
      t_ne := ht1
      zt_ne := hzt
      conj_zt := htc
      not_conj := hnc }
  refine ⟨t, htS, hu, U4_eq_of_isFourSubgroup hu hU4 hzU htU,
    (hx.swap_conseq t htS htc htsw).2.2.1.2, ?_, ?_⟩
  · refine ⟨q, hP.odd, hP.gt3, ?_⟩
    rw [centralizer_U4_eq hzz]
    exact (ixz_L2 hz hS hP htS htc htsw).2
  · have hord : orderOf (z * t) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact zt_mul_self_eq_one hu) (zt_ne_one hu)
    have h1 : IsConj x₀ (z * t) := by
      rcases hx.classes (z * t) hord with h | h
      · exact absurd h hnc
      · exact h
    rintro x₁ ⟨hx1, hxnc⟩
    rcases hx.classes x₁ hx1 with h | h
    · exact absurd (isCentralInvolution_of_isConj_P27 hz h) hxnc
    · exact h.symm.trans h1

theorem two_class_pattern {k : Kind} {z : G} {S : Subgroup G}
    (hfld : L4TwoFieldStmt G z k S) (ctx : Stage2Ctx G z k S) (hnt : ¬ TypeOneCase G k) :
    IsClassicalKind k ∧ ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) (x₀ : G),
      Stage1Pair G z S q L₁ L₂ ∧ TwoClassData G z S L₁ L₂ q x₀ ∧
      ∀ t' ∈ S, t' * t' = 1 → Swaps z t' L₁ L₂ →
        (IsConj z t' ∧ ¬ IsConj z (z * t')) ∨ (IsConj z (z * t') ∧ ¬ IsConj z t') := by
  have hd := ctx.data
  have hz := ctx.central
  have hS := ctx.sylow
  clear ctx
  cases hd with
  | g2 h => exact absurd (Or.inl h.one_class) hnt
  | m12 h => exact absurd (Or.inr rfl) hnt
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h4⟩ := h
    obtain ⟨x₀, hx⟩ := h4.two
    exact ⟨Or.inl rfl, q, L₁, L₂, x₀, h4.pair, hx, fun t' ht'S ht'2 hsw =>
      pattern_psp4 hz hS h4 hx ht'S ht'2 hsw⟩
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, h4⟩ := h
    rcases h4.fusion with ⟨-, h1⟩ | ⟨hq4, x, hx, -, -⟩
    · exact absurd (Or.inl h1) hnt
    · exact ⟨Or.inr ⟨ε, rfl⟩, q, L₁, L₂, x, h4.pair, hx, fun t' ht'S ht'2 hsw =>
        pattern_l4 hz hS h4.pair h4.index_le hx (hfld ε q L₁ L₂ x rfl h4 hx hq4) ht'S ht'2 hsw⟩
  | mcl h =>
    obtain ⟨n, -, h⟩ := h
    exact absurd (Or.inl h.one_class) hnt
  | ly h =>
    obtain ⟨n, -, h⟩ := h
    exact absurd (Or.inl h.one_class) hnt

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two
