module

public import CFSG.ClassicalInvolution.Asc77.AscT7CSetup24
public import CFSG.ClassicalInvolution.Asc77.AscT7CRecog
public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp23
public import CFSG.ClassicalInvolution.Asc77.AscT7CHyp

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7C

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem mem_normalizer_of_orderOf_four (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {K K₂ R : Subgroup G} {z u v : G} (hK : K ∈ Ω) (hK₂ : K₂ ∈ Ω) (hne : K₂ ≠ K)
    (hz : IsUniqueInvolution K z) (hu : IsUniqueInvolution K₂ u) (hR : IsSylow2In R K) (hvR : v ∈ R)
    (o : orderOf v = 4) (hvu : v * u = u * v) : z ∈ Subgroup.normalizer (K₂ : Set G) := by
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := T7A.isPGroup_zpowers_of_orderOf_four o
  have hquat := hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hR)
  have hnc : ¬ ∀ w ∈ K, v * w = w * v := fun hall => by
    have h1 := hquat.sq_eq_one_of_central hvR (fun y hy => hall y (hR.1 hy))
    have h2 : v ^ 2 = 1 := by rw [pow_two]; exact h1
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [o] at h3
    omega
  have hvN : v ∈ Subgroup.normalizer (K₂ : Set G) :=
    hΩ.omega5 K₂ hK₂ K hK hne u hu v (hR.1 hvR) hnc hv2 hvu
  rw [← T7A.sq_eq_of_orderOf_four hz (hR.1 hvR) o]
  exact Subgroup.mul_mem _ hvN hvN

theorem exists_orderOf_four_mem_dGrp24 {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
    {z u : G} (hs : Hyp23Setting p f Ω K K' z) (hyp : Hyp24Data Ω K K' W S R R' z u) {g : G}
    (hg : g⁻¹ * z * g = u)
    (hcyc : IsCyclic ↥(dGrp24 K S R R' g)) (hne : dGrp24 K S R R' g ≠ Subgroup.zpowers z) :
    ∃ d ∈ dGrp24 K S R R' g, orderOf d = 4 := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hRsyl : IsSylow2In R K := isSylow2In_of_mem_RSet_of_le hp hΩ hK hyp.hR.1 hyp.hR.2.1
  have hWab := Thompson.commutes_of_mem_WSet hp hq hΩ hyp.hW
  obtain ⟨v, hvKW, o⟩ := exists_orderOf_four_mem_inf hp hq hΩ hyp.hW hyp.hWS hK hRsyl hyp.hR.2.2 hz
  have hvR : v ∈ R := by
    have : K ⊓ (S : Subgroup G) = R :=
      hRsyl.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hyp.hR.2.1 hyp.hR.2.2)
    rw [← this]
    exact ⟨hvKW.1, hyp.hWS hvKW.2⟩
  have hu : IsUniqueInvolution (conjSub g⁻¹ K) u := by
    have := hz.conj g⁻¹
    rwa [inv_inv, hg] at this
  have hK₂ : conjSub g⁻¹ K ∈ Ω := hΩ.conjInvariant g⁻¹ K hK
  have hne₂ : conjSub g⁻¹ K ≠ K := fun h => hyp.hu.2.2.2.2 (by
    rw [h] at hu
    exact (hz.eq hu).symm)
  have hzN : z ∈ Subgroup.normalizer ((conjSub g⁻¹ K : Subgroup G) : Set G) :=
    mem_normalizer_of_orderOf_four hp hΩ hK hK₂ hne₂ hz hu hRsyl hvR o
      (hWab v hvKW.2 u hyp.hu.2.1)
  have hzD : z ∈ dGrp24 K S R R' g := by
    unfold dGrp24
    simp only [Subgroup.mem_inf]
    refine ⟨⟨⟨?_, hzN⟩, hyp.hWS hyp.hzW⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (e189_commute_of_mem hz (hyp.hR.2.1 hr)).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (e189_commute_of_mem hz' (hyp.hR'.2.1 hr)).symm
  have hD2 : IsPGroup 2 ↥(dGrp24 K S R R' g) :=
    S.isPGroup'.to_le (by unfold dGrp24; exact inf_le_left.trans inf_le_right)
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h4 : 4 ≤ Nat.card ↥(dGrp24 K S R R' g) := by
    obtain ⟨n, hn⟩ := hD2.exists_card_eq
    by_contra hlt
    have hn1 : n ≤ 1 := by
      by_contra hn2
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hle : Subgroup.zpowers z ≤ dGrp24 K S R R' g := Subgroup.zpowers_le.mpr hzD
    have hcard : Nat.card ↥(dGrp24 K S R R' g) ≤ Nat.card ↥(Subgroup.zpowers z) := by
      rw [Nat.card_zpowers, hzord, hn]
      calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
        _ = 2 := by norm_num
    exact hne (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  obtain ⟨d, hd, hd4⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic hD2 hcyc h4
  exact ⟨d, hd, hd4⟩

end T7C

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C24_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp24 p f Ω K K' W S R R' z u → ∀ g : G, g⁻¹ * z * g = u →
      IsCyclic ↥(dGrp24 K S R R' g)

@[expose] def C24_chain : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp23Setting p f Ω K K' z → Hyp24Data Ω K K' W S R R' z u → 8 < Nat.card ↥R →
      ∀ g : G, g⁻¹ * z * g = u →
      ∀ d x : G, d ∈ dGrp24 K S R R' g → orderOf d = 4 → x ∈ R' ⊓ W → orderOf x = 4 →
        (if piSign p f then SectionLieType p f Ω (rLayer Ω (d * x)) .PSL 3
          else SectionLieType p f Ω (rLayer Ω (d * x)) .PSU 3) →
        rLayer Ω (d * x) ⊔ K' = ⊤ →
          (piSign p f = true → ∃ U : Fin 3 → Subgroup G, LinearChain3 p f U) ∧
          (piSign p f = false → ∃ U : Fin 3 → Subgroup G, PhanChain3 p f U)

variable {p f}

theorem c24_10_of (h2 : C24_2 p f) (h4 : C24_4 p f) (h7 : C24_7 p f) (h8 : C24_8 p f)
    (h9 : C24_9 p f) (hchain : C24_chain p f) : C24_10 p f := by
  intro G _ _ _ Ω K K' W S R R' z u hyp
  obtain ⟨g, -, hg⟩ := h2 G Ω K K' W S R R' z u hyp
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hdata : Hyp24Data Ω K K' W S R R' z u := hyp.data
  obtain ⟨d, hd, hd4⟩ := T7C.exists_orderOf_four_mem_dGrp24 hs hdata hg
    (h4 G Ω K K' W S R R' z u hyp g hg) (h7 G Ω K K' W S R R' z u hyp g hg)
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  obtain ⟨x, hxW, hx4⟩ := T7C.exists_orderOf_four_mem_inf hp hq hΩ hyp.hW hyp.hWS hK' hR'syl
    hyp.hR'.2.2 hz'
  have hxR' : x ∈ R' := by
    have : K' ⊓ (S : Subgroup G) = R' :=
      hR'syl.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hyp.hR'.2.1 hyp.hR'.2.2)
    rw [← this]
    exact ⟨hxW.1, hyp.hWS hxW.2⟩
  obtain ⟨hsec, hgen⟩ := h8 G Ω K K' W S R R' z u hyp g hg d x hd hd4 ⟨hxR', hxW.2⟩ hx4
  obtain ⟨hlin, hphan⟩ := hchain G Ω K K' W S R R' z u hs hdata
    (h9 G Ω K K' W S R R' z u hyp) g hg d x hd hd4 ⟨hxR', hxW.2⟩ hx4 hsec hgen
  have hnab : ∃ a b : G, a * b ≠ b * a := T7C.exists_not_commute_of_stand hst
  refine Or.inl (Or.inl ?_)
  cases hπ : piSign p f
  · obtain ⟨U, hU⟩ := hphan hπ
    exact oddLieType_of_phanChain3 hp hq hnab hU
  · obtain ⟨U, hU⟩ := hlin hπ
    exact oddLieType_of_linearChain3 hp hq hnab hU

theorem c24_1_of_inputs (h2 : C24_2 p f) (h4 : C24_4 p f) (h7 : C24_7 p f) (h8 : C24_8 p f)
    (h9 : C24_9 p f) (hchain : C24_chain p f) : C24_1 p f :=
  c24_1_of_steps (c24_setup p f) (c24_10_of h2 h4 h7 h8 h9 hchain)

end CFSG.ClassicalInvolution.Asc77
