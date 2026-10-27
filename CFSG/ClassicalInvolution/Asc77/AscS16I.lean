module

public import CFSG.ClassicalInvolution.Asc77.AscS16H
public import CFSG.ClassicalInvolution.Asc77.AscS22CB

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S16

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section V3

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

@[expose] def V3Ab (Ω : Set (Subgroup G)) (K : Subgroup G) : Prop :=
  ¬ S22.Big Ω K ∧ ∀ M ∈ Ω, ∀ J ∈ omegaStarNbr Ω M,
    ∃ w, IsUniqueInvolution M w ∧ IsUniqueInvolution J w


theorem V3Ab.of_twin {L : Subgroup G} (hz : IsUniqueInvolution K z) (hL : L ∈ twinSet Ω K)
    (hv : V3Ab Ω K) : V3Ab Ω L := by
  refine ⟨fun hb => hv.1 ?_, hv.2⟩
  have h := twinSet_eq_of_mem_twinSet hz hL
  unfold S22.Big at hb ⊢
  rw [← h]
  exact hb


theorem V3Ab.hV3 (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hv : V3Ab Ω K) :
    ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃ := by
  intro M hM
  by_contra hcon
  push Not at hcon
  exact hv.1 (S22.Big.of_four h hM hcon.1 hcon.2.1 hcon.2.2)

end V3

section Hyp51

variable {G : Type} [Group G] [Finite G]

theorem hyp51At_of_zStar {B : Subgroup G} {c z : G} (hzB : z ∈ B) (hz1 : z ≠ 1)
    (hz2 : z * z = 1) (hc2 : c * c = 1) (hzc : z * c = c * z) (hne : z ≠ c)
    (hzs : z ∈ zStarOf (Subgroup.centralizer ({c} : Set G))) : Hyp51At B c := by
  have hzC : z ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzc
  have hvac : ∀ L : Subgroup (OddQuot c), ¬ MovedByAll B c L := by
    intro L hL
    have hx : oddQuotMk c ⟨z, hzC⟩ ∈ modOdd c B :=
      ⟨⟨z, hzC⟩, Subgroup.mem_subgroupOf.mpr hzB, rfl⟩
    have hx' : oddQuotMk c ⟨z, hzC⟩ ∉ modOdd c (Subgroup.zpowers c) := by
      rintro ⟨⟨y, hyC⟩, hy, hyz⟩
      have hy' : y ∈ Subgroup.zpowers c := Subgroup.mem_subgroupOf.mp hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
      have hck : c ^ k = 1 ∨ c ^ k = c := by
        have hc2' : c ^ 2 = 1 := by rw [pow_two]; exact hc2
        obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1) ∧ k = 2 * q + r :=
          ⟨k / 2, k % 2, by omega, by omega⟩
        rcases hr with rfl | rfl
        · left
          rw [add_zero, zpow_mul]
          simp [hc2']
        · right
          rw [zpow_add, zpow_mul]
          simp [hc2']
      have hcomm : z * c ^ k = c ^ k * z := (Commute.zpow_right (show Commute z c from hzc) k).eq
      have hsq : (z⁻¹ * c ^ k) * (z⁻¹ * c ^ k) = 1 := by
        have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
        rcases hck with h1 | h1
        · rw [h1, mul_one, hzi, hz2]
        · rw [h1, hzi]
          calc z * c * (z * c) = z * (c * z) * c := by group
            _ = z * (z * c) * c := by rw [← hzc]
            _ = (z * z) * (c * c) := by group
            _ = 1 := by rw [hz2, hc2, one_mul]
      have hmem : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({c} : Set G)))⁻¹ * ⟨c ^ k, hyC⟩ ∈
          componentClassificationOddCore ↥(Subgroup.centralizer ({c} : Set G)) :=
        QuotientGroup.eq.mp hyz.symm
      have hmem2 : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({c} : Set G)))⁻¹ * ⟨c ^ k, hyC⟩ *
          ((⟨z, hzC⟩ : ↥(Subgroup.centralizer ({c} : Set G)))⁻¹ * ⟨c ^ k, hyC⟩) = 1 :=
        Subtype.ext hsq
      have h1 := T7H.eq_one_of_mem_odd_of_sq
        (CFSG.ComponentClassification.OddCore.odd_card ↥(Subgroup.centralizer ({c} : Set G)))
        hmem hmem2
      have h2 : z⁻¹ * c ^ k = 1 := congrArg Subtype.val h1
      have h3 : z = c ^ k := by
        have := congrArg (fun t => z * t) h2
        simpa [mul_assoc] using this.symm
      rcases hck with h4 | h4
      · exact hz1 (h3.trans h4)
      · exact hne (h3.trans h4)
    obtain ⟨y, hyL, hy⟩ := hL _ hx hx'
    apply hy
    obtain ⟨zh, hzh, hzhz⟩ := Subgroup.mem_map.mp hzs
    rw [Subgroup.mem_comap] at hzh
    have hzh' : zh = ⟨z, hzC⟩ := Subtype.ext hzhz
    rw [hzh'] at hzh
    exact ((Subgroup.mem_center_iff.mp hzh) y).symm
  exact ⟨fun L₁ L₂ _ _ h1 _ => absurd h1 (hvac L₁), fun L _ hm => absurd hm (hvac L)⟩

end Hyp51

section C22

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem invert₂ (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    Hyp22Setting p f Ω K K' K₃ z u₁ u₂⁻¹ u₃ := by
  obtain ⟨R, R', R₃, hR, hR', hR₃, h₁, h₂, h₃, c12, c13, c23⟩ := T7J.exists_sylow_triple h
  exact S22.hyp22Setting_of_sylows h.stand h.hz h.hK' h.hne h.perp h.hK₃ h.hK₃K h.hK₃K' hR hR'
    hR₃ c12 c13 c23 h₁ (R'.inv_mem h₂) h₃ h.hu₁.2 (by rw [orderOf_inv]; exact h.hu₂.2) h.hu₃.2

theorem hyp51At_B (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {c : G}
    (hcB : c ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) (hcz : c ≠ z)
    (hzs : z ∈ zStarOf (Subgroup.centralizer ({c} : Set G))) :
    Hyp51At (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) c := by
  have hzB : z ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := T7B.mem_closure_snd
  have hcc : c * c = 1 := Lemma52Proof.mul_self_eq_one_of_mem h.isElemAbelian_B hcB
  have hcomm : z * c = c * z := by
    have := h.isElemAbelian_B.1.is_comm.comm ⟨z, hzB⟩ ⟨c, hcB⟩
    exact congrArg Subtype.val this
  exact hyp51At_of_zStar hzB h.hz.ne_one h.hz.sq hcc hcomm (Ne.symm hcz) hzs

theorem zStar_pair (hR1 : Z2NoD8 p) (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hv : V3Ab Ω K) :
    z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set G)) ∧
      z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂ * z} : Set G)) := by
  refine ⟨layer_zStar hR1 h (hv.hV3 h) hv.2, ?_⟩
  have h' := invert₂ h
  have hv' : V3Ab Ω K := hv
  have := layer_zStar hR1 h' (hv'.hV3 h') hv'.2
  have e : u₁ * u₂⁻¹ = u₁ * u₂ * z := by
    rw [inv_eq_mul_of_sq h.sq₂ h.hz.sq, mul_assoc]
  rwa [e] at this

theorem hyp51u_of_V3 (hR1 : Z2NoD8 p) (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hv : V3Ab Ω K) :
    ∀ c ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G), c ≠ 1 → c ≠ z →
      Hyp51At (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) c := by
  intro c hc hc1 hcz
  have cm : T7J.Cmt z u₁ u₂ u₃ :=
    ⟨h.sq₁, h.sq₂, h.sq₃, h.hz.sq, h.comm₁₂, T7J.comm₁₃ h, h.comm₂₃⟩
  have hcm := T7J.mem_closure_three cm.commute_xz cm.commute_xw cm.commute_wz.symm cm.sq_pair
    cm.z2 cm.rot.sq_pair hc
  have hB1 := zStar_pair hR1 h hv
  have h2 := S22.rotate h
  have hv2 : V3Ab Ω K' := hv.of_twin h.hz h.hK'
  have hB2 := zStar_pair hR1 h2 hv2
  have h3 := S22.rotate h2
  have hv3 : V3Ab Ω K₃ := hv.of_twin h.hz h.hK₃
  have hB3 := zStar_pair hR1 h3 hv3
  rcases hcm with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact absurd h1 hc1
  · subst h1
    exact hyp51At_B h hc hcz hB1.1
  · exact absurd h1 hcz
  · subst h1
    exact hyp51At_B h hc hcz hB2.1
  · subst h1
    exact hyp51At_B h hc hcz hB1.2
  ·
    have e : c = u₃ * u₁ * z := h1.trans cm.eq_xw
    rw [e] at hc hcz ⊢
    exact hyp51At_B h hc hcz hB3.2
  ·
    have e : c = u₂ * u₃ * z := h1.trans cm.zc₂₃
    rw [e] at hc hcz ⊢
    exact hyp51At_B h hc hcz hB2.2
  ·
    have e : c = u₃ * u₁ := h1.trans cm.eq_xyw
    rw [e] at hc hcz ⊢
    exact hyp51At_B h hc hcz hB3.1

end C22

section Statement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C22_2V : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      V3Ab Ω K →
      Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)))) ∧
        ∀ A : Subgroup G, A ≤ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) →
          IsElemAbelian2 A 2 →
            alphaOf A = alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G))

end Statement

section C22Thm

variable (p f : ℕ) [Fact p.Prime]

theorem c22_2V (hR1 : Z2NoD8 p) : C22_2V p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h hv
  have hB : Hyp51 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
    refine ⟨Hyp22Setting.isElemAbelian_B h, S22.natCard_B h, fun c hc hc1 => ?_⟩
    by_cases hcz : c = z
    · rw [hcz]
      exact hyp22Hyp51z p f G Ω K K' K₃ z u₁ u₂ u₃ h
    · exact hyp51u_of_V3 hR1 h hv c hc hc1 hcz
  exact lemma54_odd_and_eq hB (S22.closure_12_le h) (S22.isElemAbelian2_closure h)

end C22Thm

end S16

end CFSG.ClassicalInvolution.Asc77
