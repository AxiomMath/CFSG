module

public import Mathlib
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25N3
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Witness
public import CFSG.ClassicalInvolution.Asc77.AscC25I10
public import CFSG.ClassicalInvolution.Asc77.AscFusionR11
public import CFSG.ClassicalInvolution.Asc77.AscT7QFinal
public import CFSG.ClassicalInvolution.Asc77.WP2Branch
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Comp
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Main
public import CFSG.ClassicalInvolution.Q3.Q3T7T2Main
public import CFSG.ClassicalInvolution.Q3.Q3T8Defs
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25N0
public import CFSG.ClassicalInvolution.Uniform.U3IH8
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QTOutChar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S.N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.C25V
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Asc77.C25G
open CFSG.ClassicalInvolution.Asc77.T3
open CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7F2 (Hyp25T)
open scoped MatrixGroups commutatorElement

section Quat

variable {Y : Type} [Group Y]

theorem exists_orderOf_four_of_unique_involution {K R₀ : Subgroup Y} {z : Y}
    (hI : IsUniqueInvolution K z) (hRK : R₀ ≤ K) (h2 : IsPGroup 2 ↥R₀) (h8 : 8 ≤ Nat.card R₀) :
    ∃ y ∈ R₀, orderOf y = 4 := by
  classical
  have : Finite R₀ := Nat.finite_of_card_ne_zero (by omega)
  have hex : ∃ x ∈ R₀, x ≠ 1 ∧ x ≠ z := by
    by_contra hcon
    push Not at hcon
    have hsub : (R₀ : Set Y) ⊆ {1, z} := by
      intro x hx
      by_cases h1 : x = 1
      · simp [h1]
      · simp [hcon x hx h1]
    have h1 : (R₀ : Set Y).ncard ≤ ({1, z} : Set Y).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2' : ({1, z} : Set Y).ncard ≤ 2 := by
      calc ({1, z} : Set Y).ncard ≤ ({z} : Set Y).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    have h3 : Nat.card R₀ = (R₀ : Set Y).ncard := by
      rw [← Nat.card_coe_set_eq]
      rfl
    omega
  obtain ⟨x, hxR, hx1, hxz⟩ := hex
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥R₀)).mp h2
  have hx2 : orderOf x ∣ 2 ^ k := by
    have h1 := orderOf_dvd_natCard (⟨x, hxR⟩ : ↥R₀)
    rw [Subgroup.orderOf_mk, hk] at h1
    exact h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hx2
  have hj2 : 2 ≤ j := by
    by_contra hlt
    push Not at hlt
    interval_cases j
    · exact hx1 (orderOf_eq_one_iff.mp (by simpa using hj))
    · have h3 := pow_orderOf_eq_one x
      rw [hj] at h3
      have hsq : x * x = 1 := by simpa [sq] using h3
      rcases hI.unique x (hRK hxR) hsq with h | h
      · exact hx1 h
      · exact hxz h
  refine ⟨x ^ (2 ^ (j - 2)), R₀.pow_mem hxR _, ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) (by rw [hj]; exact pow_dvd_pow 2 (by omega)), hj]
  have : 2 ^ j = 2 ^ (j - 2) * 4 := by
    rw [show j = (j - 2) + 2 by omega, pow_add]
    norm_num
  rw [this]
  exact Nat.mul_div_cancel_left _ (by positivity)

end Quat

section Conj9300

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}




theorem false_of_conj_normalizer_a7 (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {b g : G}
    (hbg : b = g * z * g⁻¹) (hbz : b ≠ z) (hbN : b ∈ Subgroup.normalizer (K' : Set G)) :
    False := by
  have hb2 : b * b = 1 := by
    rw [hbg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.hz'.sq]; group
  obtain ⟨zc, hzc⟩ := h.hs.stand.classical K' h.hK'
  obtain ⟨R₀, hR₀K, hR₀2, hR₀8, hR₀c⟩ :=
    Hat2A7.exists_two_subgroup_centralizing hzc.witness hbN hb2
  obtain ⟨y₀, hy₀R, hy₀4⟩ := exists_orderOf_four_of_unique_involution h.hz' hR₀K hR₀2 hR₀8
  have hbz' := eq_conj_z_of_commute_order_four h (c := 1) (g := g) (y₀ := y₀)
    (by rw [conjSub_one]; exact hR₀K hy₀R) hy₀4 (by rw [← hbg]; exact hR₀c y₀ hy₀R)
  exact hbz (by rw [hbg, hbz']; group)

end Conj9300

section Branches

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' a : G}


local notation "Lₐ" => perfectCoreIn K' a

theorem typed5_data (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hat : a * t' = t' * a) {e₀ : ℕ} (hp : p ≠ 2) (h5 : 5 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩)
    (hy : ∃ y ∈ R', orderOf y = 4 ∧ y * a = a * y ∧
      y ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G)))
    (hO5 : SectionOrthType p e₀ (conjFamily (perfectCoreIn K' a))
      (conjGen (perfectCoreIn K' a)) 5 true) :
    ∃ t₀ y c₁ : G, IsSwap K K' z t₀ ∧ a * t₀ = t₀ * a ∧
      (∃ c : G, c * a = a * c ∧ c * z * c⁻¹ = t₀) ∧ c₁ * a = a * c₁ ∧ y ∈ conjSub c₁ K' ∧
      orderOf y = 4 ∧ y * a = a * y ∧ y * (z * t₀) = (z * t₀) * y ∧
      ∀ c : G, c * a = a * c → a * (z * t₀) ≠ c * z * c⁻¹ := by
  classical
  obtain ⟨ht'a, hzX, a₀, b₀, T⟩ := fs_twinSect0 h hat hp h5 hzA hL hy
  obtain ⟨tg, n, hT, D, hcard, i, hi1, hi2⟩ := hO5
  have hXn : (conjGen Lₐ).Normal := conjGen_normal _
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore ↥(conjGen Lₐ))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  obtain ⟨⟨sw, hsw2, hs1, hs2, hs3, ⟨xq, hsx⟩, ⟨x', yq, hyq, hyq4, hyqc⟩⟩, hcen⟩ :=
    twinSwapQ5_proved (p := p) (f := e₀) hp h5
      (↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) _ D _ _ _ a₀ b₀ hcard
      ⟨i, by rw [hi1, hi2]; exact hT⟩ T
  let w : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨t', ht'a⟩
  let ζ : ↥(conjGen Lₐ) := ⟨⟨z, hzA⟩, hzX⟩
  have hLmem : Lₐ ∈ conjFamily Lₐ := ⟨1, conjSub_one _⟩
  have hLX : Lₐ ≤ conjGen Lₐ := le_conjGen hLmem
  have hL'mem : conjSub w Lₐ ∈ conjFamily Lₐ := ⟨w, rfl⟩
  have hL'X : conjSub w Lₐ ≤ conjGen Lₐ := le_conjGen hL'mem
  have hzz : z * z = 1 := h.hz.sq
  have hζ2 : ζ * ζ = 1 := Subtype.ext (Subtype.ext hzz)
  obtain ⟨t₀, ht₀s, ht₀2, ht₀z⟩ :=
    exists_involution_lift (classicalInvolutionOddCore ↥(conjGen Lₐ)) hOodd hζ2 hsw2 hs1
  obtain ⟨c, hc⟩ := exists_conj_lift (classicalInvolutionOddCore ↥(conjGen Lₐ)) hOodd hζ2 ht₀2
    (x := xq) (by rw [ht₀s]; exact hsx)
  let φ : ↥(conjGen Lₐ) →* G :=
    (Subgroup.centralizer ({a} : Set G)).subtype.comp (conjGen Lₐ).subtype
  have hφinj : Function.Injective φ :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  have hφζ : φ ζ = z := rfl
  have hCa : ∀ x : ↥(conjGen Lₐ), φ x * a = a * φ x := fun x =>
    Subgroup.mem_centralizer_singleton_iff.mp (x : ↥(Subgroup.centralizer ({a} : Set G))).2
  obtain ⟨t₀G, ht₀G⟩ : ∃ g : G, g = φ t₀ := ⟨_, rfl⟩
  have ht₀G2 : t₀G * t₀G = 1 := by rw [ht₀G, ← map_mul, ht₀2, map_one]
  have ht₀Gz : t₀G * z = z * t₀G := by rw [ht₀G, ← hφζ, ← map_mul, ← map_mul, ht₀z]
  have hcG : φ c * z * (φ c)⁻¹ = t₀G := by
    rw [ht₀G, ← hc, ← hφζ, map_mul, map_mul, map_inv]
  have hat₀ : a * t₀G = t₀G * a := by rw [ht₀G]; exact (hCa t₀).symm
  have ht₀G' : t₀G = (((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) :=
    ht₀G
  have hsw1 : (QuotientGroup.mk t₀ :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = sw := ht₀s
  have ht₀C : t₀G ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [ht₀G]
    exact ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))).2
  have hnotN : conjSub t₀G K ≠ K := by
    intro hN
    have ht'K : conjSub t' K = K' := conjSub_t'_K h
    have hc1 : conjSub (t' * t₀G * t') K' = K' := by
      rw [conjSub_mul, conjSub_mul, conjSub_t'_K' h, hN, ht'K]
    have hcC : t' * t₀G * t' ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ ht'a ht₀C) ht'a
    have hfix := conjSub_perfectCoreIn_eq (K := K') hcC (mem_normalizer_iff_conjSub_eq.mpr hc1)
    have h1 : conjSub ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G)))
        (conjSub w Lₐ) = conjSub w Lₐ := by
      have e2 : ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) * w =
          w * (⟨t' * t₀G * t', hcC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) := by
        apply Subtype.ext
        change (((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) * t' =
          t' * (t' * t₀G * t')
        rw [← ht₀G']
        calc t₀G * t' = (t' * t') * t₀G * t' := by rw [h.ht'2]; group
          _ = t' * (t' * t₀G * t') := by group
      rw [← conjSub_mul, e2, conjSub_mul, hfix]
    have hsecw : conjSub sw (secImg (conjGen Lₐ) (conjSub w Lₐ)) =
        secImg (conjGen Lₐ) (conjSub w Lₐ) := by
      have h2 := secAct_secImg (conjGen Lₐ)
        ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) hL'X
      rw [h1] at h2
      calc conjSub sw (secImg (conjGen Lₐ) (conjSub w Lₐ))
          = (secImg (conjGen Lₐ) (conjSub w Lₐ)).map (secAct (conjGen Lₐ)
              ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G)))).toMonoidHom := by
            rw [secAct_of_mem (conjGen Lₐ) (t₀ : ↥(conjGen Lₐ)).2, ← hsw1]
            rfl
        _ = secImg (conjGen Lₐ) (conjSub w Lₐ) := h2
    rw [hsecw] at hs3
    exact T.ne hs3.symm
  have hsw' : conjSub (t₀G * t') K = K := by
    rcases cz_cover h ht₀Gz with h1 | h1
    · exact absurd h1 hnotN
    · exact h1
  have hswK : conjSub t₀G K = K' := by
    have e1 : conjSub t₀G K' = K := by
      have := hsw'
      rwa [conjSub_mul, conjSub_t'_K h] at this
    calc conjSub t₀G K = conjSub t₀G (conjSub t₀G K') := by rw [e1]
      _ = conjSub (t₀G * t₀G) K' := by rw [conjSub_mul]
      _ = K' := by rw [ht₀G2, conjSub_one]
  have hIS : IsSwap K K' z t₀G := ⟨ht₀G2, ht₀Gz, hswK⟩
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk_surjective x'
  have hx₂2 : (ζ * t₀) * (ζ * t₀) = 1 := by
    have h1 := (show Commute ζ t₀ from ht₀z.symm).mul_pow 2
    rw [pow_two, pow_two, pow_two, hζ2, ht₀2, mul_one] at h1
    exact h1
  let M : Subgroup ↥(conjGen Lₐ) :=
    (conjSub ((x₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) Lₐ).subgroupOf
      (conjGen Lₐ)
  have hM : ∃ m ∈ M, (QuotientGroup.mk m :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = yq := by
    rw [← hx₀, conjSub_mk_secImg (conjGen Lₐ) x₀ hLX] at hyq
    obtain ⟨m, hm, hmy⟩ := hyq
    exact ⟨m, hm, hmy⟩
  have hc' : yq * (QuotientGroup.mk (ζ * t₀) :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) =
      QuotientGroup.mk (ζ * t₀) * yq := by
    rw [QuotientGroup.mk_mul, ht₀s]
    exact hyqc
  obtain ⟨h₁, y, ⟨m, hmM, hym⟩, hy4, hyx⟩ :=
    exists_order_four_lift (classicalInvolutionOddCore ↥(conjGen Lₐ)) hOodd hx₂2 M hyq4 hc' hM
  have hmK' : (φ x₀)⁻¹ * φ m * φ x₀ ∈ K' := by
    have h2 := mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hmM)
    exact ((perfectResidualOf_le _).trans inf_le_left) (Subgroup.mem_subgroupOf.mp h2)
  obtain ⟨c₁G, hc₁G⟩ : ∃ g : G, g = φ h₁ * φ x₀ := ⟨_, rfl⟩
  have hyG : φ y = c₁G * ((φ x₀)⁻¹ * φ m * φ x₀) * c₁G⁻¹ := by
    rw [hym, map_mul, map_mul, map_inv, hc₁G, mul_inv_rev]
    group
  have hyK : φ y ∈ conjSub c₁G K' := by
    rw [hyG]
    exact conj_mem_conjSub hmK'
  have hc₁a : c₁G * a = a * c₁G := by
    rw [hc₁G, mul_assoc, hCa x₀, ← mul_assoc, hCa h₁, mul_assoc]
  have hy4G : orderOf (φ y) = 4 := by rw [orderOf_injective φ hφinj y]; exact hy4
  have hyxG : φ y * (z * t₀G) = (z * t₀G) * φ y := by
    have := congrArg φ hyx
    simp only [map_mul, hφζ] at this
    rw [← ht₀G] at this
    exact this
  have hlast : ∀ c : G, c * a = a * c → a * (z * t₀G) ≠ c * z * c⁻¹ := by
    intro c hca heq
    have hcC : c ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hca
    let cY : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨c, hcC⟩
    let aY : ↥(Subgroup.centralizer ({a} : Set G)) :=
      ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    let ζY : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨z, hzA⟩
    let x₂Y : ↥(Subgroup.centralizer ({a} : Set G)) :=
      ((ζ * t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G)))
    have hrel : aY * x₂Y = cY * ζY * cY⁻¹ := by
      apply Subtype.ext
      change a * φ (ζ * t₀) = c * z * c⁻¹
      rw [map_mul, hφζ, ← ht₀G]
      exact heq
    have hx₂Ymem : x₂Y ∈ conjGen Lₐ := (ζ * t₀ : ↥(conjGen Lₐ)).2
    have haY : aY ∈ conjGen Lₐ := by
      have h1 : aY = (cY * ζY * cY⁻¹) * x₂Y⁻¹ := by
        rw [← hrel]
        group
      rw [h1]
      exact Subgroup.mul_mem _ (hXn.conj_mem _ hzX cY) (Subgroup.inv_mem _ hx₂Ymem)
    let aX : ↥(conjGen Lₐ) := ⟨aY, haY⟩
    have haX1 : aX = 1 :=
      eq_one_of_central (classicalInvolutionOddCore ↥(conjGen Lₐ)) hOodd hcen
        (fun v => Subtype.ext (Subtype.ext (hCa v))) (Subtype.ext (Subtype.ext ha2))
    apply ha1
    exact congrArg (fun x : ↥(conjGen Lₐ) => ((x : ↥(Subgroup.centralizer ({a} : Set G))) : G))
      haX1
  exact ⟨t₀G, φ y, c₁G, hIS, hat₀, ⟨φ c, hCa c, hcG⟩, hc₁a, hyK, hy4G, hCa y, hyxG, hlast⟩

end Branches

section Branches6

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' a : G}



local notation "Lₐ" => perfectCoreIn K' a

theorem false_of_omega6 (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    (hat : a * t' = t' * a)
    {e₀ : ℕ} (hp : p ≠ 2) (h5 : 5 ≤ p ^ e₀) (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩)
    (hy : ∃ y ∈ R', orderOf y = 4 ∧ y * a = a * y ∧
      y ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G)))
    (hO6 : SectionOrthType p e₀ (conjFamily (perfectCoreIn K' a)) (conjGen (perfectCoreIn K' a))
      6 (!piSign p e₀)) : False := by
  classical
  obtain ⟨ht'a, hzX, a₀, b₀, T⟩ := fs_twinSect0 h hat hp h5 hzA hL hy
  obtain ⟨tg, n, hT, D, hcard, i, hi1, hi2⟩ := hO6
  have hXn : (conjGen Lₐ).Normal := conjGen_normal _
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore ↥(conjGen Lₐ))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  obtain ⟨τ, y, hτz, hτc, hτ2, hy, hτA, -⟩ := twinCent6_proved (p := p) (f := e₀)
    (↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) _ D _ _ _ a₀ b₀ hcard
    ⟨i, by rw [hi1, hi2]; exact hT⟩ T
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ↥(conjGen Lₐ), ζ = ⟨⟨z, hzA⟩, hzX⟩ := ⟨_, rfl⟩
  rw [← hζ] at hy hτc hτz
  have hzz : z * z = 1 := h.hz.sq
  have hζ2 : ζ * ζ = 1 := by
    rw [hζ]
    apply Subtype.ext
    apply Subtype.ext
    exact hzz
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hmk : (QuotientGroup.mk (y₀ * ζ * y₀⁻¹) :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = τ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hy
  have hcomm : (QuotientGroup.mk (y₀ * ζ * y₀⁻¹) :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) * QuotientGroup.mk ζ =
      QuotientGroup.mk ζ * QuotientGroup.mk (y₀ * ζ * y₀⁻¹) := by
    rw [hmk]
    exact hτc
  obtain ⟨g, hgc, hgm⟩ := exists_conj_comm_lift _ hOodd hζ2 y₀ hcomm
  obtain ⟨w, hw⟩ : ∃ w : ↥(conjGen Lₐ), w = g * ζ * g⁻¹ := ⟨_, rfl⟩
  rw [← hw] at hgc hgm
  have hwτ : (QuotientGroup.mk w :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = τ := by
    rw [hgm]
    exact hmk
  let φ : ↥(conjGen Lₐ) →* G :=
    (Subgroup.centralizer ({a} : Set G)).subtype.comp (conjGen Lₐ).subtype
  have hφinj : Function.Injective φ :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  have hφζ : φ ζ = z := by
    rw [hζ]
    rfl
  have hbC : φ w ∈ Subgroup.centralizer ({a} : Set G) :=
    (w : ↥(Subgroup.centralizer ({a} : Set G))).2
  have hba : φ w * a = a * φ w := Subgroup.mem_centralizer_singleton_iff.mp hbC
  have hbc : φ w * z = z * φ w := by
    have := congrArg φ hgc
    rw [map_mul, map_mul, hφζ] at this
    exact this
  have hbg : φ w = φ g * z * (φ g)⁻¹ := by
    rw [hw, map_mul, map_mul, map_inv, hφζ]
  have hbz : φ w ≠ z := by
    intro hbz
    apply hτz
    have hwζ : w = ζ := hφinj (hbz.trans hφζ.symm)
    rw [← hwτ, hwζ]
  have hbK' : conjSub (φ w) K' = K' := by
    rcases cz_conj_K' h hbc with h1 | h1
    · exfalso
      have hc''C : t' * φ w ∈ Subgroup.centralizer ({a} : Set G) :=
        Subgroup.mul_mem _ ht'a hbC
      have hc''K' : conjSub (t' * φ w) K' = K' := by
        rw [conjSub_mul, h1, conjSub_t'_K h]
      have hfix := conjSub_perfectCoreIn_eq (K := K') hc''C
        (mem_normalizer_iff_conjSub_eq.mpr hc''K')
      have e2 : (w : ↥(Subgroup.centralizer ({a} : Set G))) =
          (⟨t', ht'a⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨t' * φ w, hc''C⟩ := by
        apply Subtype.ext
        change φ w = t' * (t' * φ w)
        calc φ w = (t' * t') * φ w := by rw [h.ht'2, one_mul]
          _ = t' * (t' * φ w) := by group
      have hbL : conjSub (w : ↥(Subgroup.centralizer ({a} : Set G))) Lₐ =
          conjSub (⟨t', ht'a⟩ : ↥(Subgroup.centralizer ({a} : Set G))) Lₐ := by
        rw [e2, conjSub_mul, hfix]
      have hLmem : Lₐ ∈ conjFamily Lₐ := ⟨1, conjSub_one _⟩
      have hLX : Lₐ ≤ conjGen Lₐ := le_conjGen hLmem
      have h2 := secAct_secImg (conjGen Lₐ) (w : ↥(Subgroup.centralizer ({a} : Set G))) hLX
      rw [hbL] at h2
      have hsecτ : conjSub τ (secImg (conjGen Lₐ) Lₐ) = secImg (conjGen Lₐ)
          (conjSub (⟨t', ht'a⟩ : ↥(Subgroup.centralizer ({a} : Set G))) Lₐ) := by
        rw [← h2, secAct_of_mem (conjGen Lₐ) (w : ↥(conjGen Lₐ)).2, ← hwτ]
        rfl
      exact T.ne (hτA.symm.trans hsecτ)
    · exact h1
  have hbN : φ w ∈ Subgroup.normalizer (K' : Set G) := mem_normalizer_iff_conjSub_eq.mpr hbK'
  exact false_of_conj_normalizer_a7 h hbg hbz hbN

end Branches6

end CFSG.ClassicalInvolution.Hat2A7S.N
