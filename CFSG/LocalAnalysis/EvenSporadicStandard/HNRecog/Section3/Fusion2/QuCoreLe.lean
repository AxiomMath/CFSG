module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.QzConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Qz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem mem_pCoreOf_conj {G : Type} [Group G] {H : Subgroup G} {g y : G}
    (hgn : g ∈ Subgroup.normalizer H) (hy : y ∈ CFSG.Open.pCoreOf 2 H) :
    g * y * g⁻¹ ∈ CFSG.Open.pCoreOf 2 H := by
  obtain ⟨m, hm, hmval⟩ :=
    Subgroup.mem_map.mp (show y ∈ (CFSG.pCore 2 ↥H).map H.subtype from hy)
  have hmap : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgn
  let f : ↥H ≃* ↥H :=
    (MulEquiv.subgroupMap (MulAut.conj g) H).trans (MulEquiv.subgroupCongr hmap)
  have hfm : f m ∈ CFSG.pCore 2 ↥H := by
    rw [← CFSG.pCore_map_iso 2 f]
    exact Subgroup.mem_map_of_mem f.toMonoidHom hm
  refine Subgroup.mem_map.mpr ⟨f m, hfm, ?_⟩
  have hfval : (f m : G) = g * (m : G) * g⁻¹ := by
    show ((MulEquiv.subgroupMap (MulAut.conj g) H) m : G) = g * (m : G) * g⁻¹
    rw [MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  show (f m : G) = g * y * g⁻¹
  rw [hfval, ← hmval]
  rfl

theorem not_mem_pCore_derived_of_central {G : Type} [Group G] {X : Subgroup G} (hT : TwoFourData X)
    {c : G} (hc : ∀ g ∈ X, g * c * g⁻¹ = c) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) :
    c ∉ CFSG.Open.pCoreOf 2 (derivedOf X) := by
  intro hcN
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSle : Subgroup.zpowers c ≤ CFSG.Open.pCoreOf 2 (derivedOf X) :=
    Subgroup.zpowers_le.mpr hcN
  have hSinv : ∀ g ∈ X, ∀ s ∈ Subgroup.zpowers c, g * s * g⁻¹ ∈ Subgroup.zpowers c := by
    intro g hg s hs
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    rw [← conj_zpow, hc g hg]
    exact Subgroup.zpow_mem_zpowers c n
  rcases hT.irreducible (Subgroup.zpowers c) hSle hSinv with hbot | htop
  · have hmem : c ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_zpowers c
    exact hc1 (Subgroup.mem_bot.mp hmem)
  · have hcard1 : Nat.card (Subgroup.zpowers c) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hc2 hc1
    have hcard2 : Nat.card (CFSG.Open.pCoreOf 2 (derivedOf X)) = 2 ^ 4 := hT.elem_two.2
    have heq : Nat.card (Subgroup.zpowers c) =
        Nat.card (CFSG.Open.pCoreOf 2 (derivedOf X)) := by rw [htop]
    rw [hcard1, hcard2] at heq
    exact absurd heq (by norm_num)

theorem pCore_derived_le_Qz {G : Type} [Group G] {u : G} {X : Subgroup G} (hXu : X ≤ Gx u)
    (hC : IsExtraspecialPlusByA5WrTwo ↥(Gx u)) (hT : TwoFourData X) :
    CFSG.Open.pCoreOf 2 (derivedOf X) ≤ Qz u := by
  classical
  have hL_le : derivedOf X ≤ Gx u := (derivedOf_le X).trans hXu
  have hXQ : ∀ g ∈ X, ∀ y ∈ Qz u, g * y * g⁻¹ ∈ Qz u := by
    intro g hg y hy
    have hgu : g ∈ Gx u := hXu hg
    have hfix : g * u * g⁻¹ = u := by
      have h := mem_Gx.mp hgu
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    rw [← hfix]
    exact Qz_conj_mem g hy
  have hXN : ∀ g ∈ X, ∀ y ∈ CFSG.Open.pCoreOf 2 (derivedOf X),
      g * y * g⁻¹ ∈ CFSG.Open.pCoreOf 2 (derivedOf X) := by
    intro g hg y hy
    have hnorm : g ∈ Subgroup.normalizer (derivedOf X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro t
      constructor
      · intro ht
        exact conj_mem_derivedOf hg ht
      · intro ht
        have h := conj_mem_derivedOf (X.inv_mem hg) ht
        rwa [show g⁻¹ * (g * t * g⁻¹) * (g⁻¹)⁻¹ = t by group] at h
    exact mem_pCoreOf_conj hnorm hy
  have hSinv : ∀ g ∈ X, ∀ s ∈ CFSG.Open.pCoreOf 2 (derivedOf X) ⊓ Qz u,
      g * s * g⁻¹ ∈ CFSG.Open.pCoreOf 2 (derivedOf X) ⊓ Qz u := by
    intro g hg s hs
    exact ⟨hXN g hg s hs.1, hXQ g hg s hs.2⟩
  rcases hT.irreducible (CFSG.Open.pCoreOf 2 (derivedOf X) ⊓ Qz u) inf_le_left hSinv with
    hSbot | hStop
  ·
    have hQpg : IsPGroup 2 (Qz u) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(Gx u))).map (Gx u).subtype
    have hMsub_norm : ((derivedOf X ⊓ Qz u).subgroupOf (derivedOf X)).Normal := by
      refine ⟨fun m hm x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      refine ⟨?_, ?_⟩
      · exact (derivedOf X).mul_mem ((derivedOf X).mul_mem x.2 hm.1) ((derivedOf X).inv_mem x.2)
      · exact hXQ (x : G) ((derivedOf_le X) x.2) (m : G) hm.2
    have hMsub_pg : IsPGroup 2 ((derivedOf X ⊓ Qz u).subgroupOf (derivedOf X)) := by
      have hMpg : IsPGroup 2 ↥(derivedOf X ⊓ Qz u) :=
        IsPGroup.to_le hQpg (show derivedOf X ⊓ Qz u ≤ Qz u from inf_le_right)
      exact hMpg.of_equiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : derivedOf X ⊓ Qz u ≤ derivedOf X)).symm
    have hMsub_le : (derivedOf X ⊓ Qz u).subgroupOf (derivedOf X) ≤
        CFSG.pCore 2 ↥(derivedOf X) := by
      rw [CFSG.pCore]
      exact le_sSup ⟨hMsub_norm, hMsub_pg⟩
    have hM_le_N : derivedOf X ⊓ Qz u ≤ CFSG.Open.pCoreOf 2 (derivedOf X) := by
      have hmap := Subgroup.map_mono (f := (derivedOf X).subtype) hMsub_le
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left] at hmap
      exact hmap
    have hLQ : derivedOf X ⊓ Qz u = ⊥ := by
      apply le_bot_iff.mp
      rw [← hSbot]
      exact le_inf hM_le_N inf_le_right
    obtain ⟨Q₀, hQ₀norm, hQ₀W, hQz_eq⟩ := exists_Qz_eq (w := u) hC
    haveI : Q₀.Normal := hQ₀norm
    let L₀ : Subgroup ↥(Gx u) := (derivedOf X).subgroupOf (Gx u)
    have hL0Q0 : L₀ ⊓ Q₀ = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [Subgroup.mem_inf] at hx
      have hxL : (x : G) ∈ derivedOf X := Subgroup.mem_subgroupOf.mp hx.1
      have hxQ : (x : G) ∈ Qz u := by
        rw [hQz_eq]
        exact Subgroup.mem_map_of_mem (Gx u).subtype hx.2
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        rw [← hLQ]
        exact ⟨hxL, hxQ⟩
      exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
    let φ : ↥L₀ →* ↥(Gx u) ⧸ Q₀ := (QuotientGroup.mk' Q₀).comp L₀.subtype
    have hφinj : Function.Injective φ := by
      intro a b hab
      have h1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
      have h2 : ((a * b⁻¹ : ↥L₀) : ↥(Gx u)) ∈ Q₀ := by
        have h1' : (QuotientGroup.mk' Q₀ ((a * b⁻¹ : ↥L₀) : ↥(Gx u))) = 1 := h1
        exact (QuotientGroup.eq_one_iff (N := Q₀) _).mp h1'
      have hz : ((a * b⁻¹ : ↥L₀) : ↥(Gx u)) ∈ L₀ ⊓ Q₀ :=
        ⟨(a * b⁻¹ : ↥L₀).2, h2⟩
      rw [hL0Q0] at hz
      have hz1 : ((a * b⁻¹ : ↥L₀) : ↥(Gx u)) = 1 := Subgroup.mem_bot.mp hz
      have hab' : (a * b⁻¹ : ↥L₀) = 1 := Subtype.ext hz1
      rwa [mul_inv_eq_one] at hab'
    have hL0card : Nat.card ↥L₀ = 960 := by
      have h1 : Nat.card ↥L₀ = Nat.card ↥(derivedOf X) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL_le).toEquiv
      rw [h1, hT.card_derived]
    have hquotcard : Nat.card (↥(Gx u) ⧸ Q₀) = 7200 := by
      obtain ⟨e⟩ := hQ₀W.quotient
      rw [Nat.card_congr e.toEquiv, card_A5WrTwo_eq]
    have hdvd := Subgroup.card_dvd_of_injective φ hφinj
    rw [hL0card, hquotcard] at hdvd
    exact absurd hdvd (by norm_num)
  ·
    intro n hn
    have : n ∈ CFSG.Open.pCoreOf 2 (derivedOf X) ⊓ Qz u := hStop.symm ▸ hn
    exact this.2

end CFSG.EvenSporadicStandard.HNRecog.Section3
