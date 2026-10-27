module

public import CFSG.ClassicalInvolution.Q3.Q3AM289Z4
public import CFSG.ClassicalInvolution.Q3.Q3AMLYBase
public import CFSG.ClassicalInvolution.Q3.Q3AMBadS3Lift
public import CFSG.ClassicalInvolution.Q3.Q3T8B16C
public import CFSG.ClassicalInvolution.Q3.Q3AMXNOrb

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3AM (nbrCoreFam nbrLayer exactCore3_le_nbrLayer
  nbrLayer_le_centralizer)
open scoped commutatorElement

section Lift

variable {G : Type} [Group G]

theorem modOddIn_conj {Y E : Subgroup G} {y : G} (hy : y ∈ Y) :
    modOddIn Y (conjSub y E) =
      conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨y, hy⟩) (modOddIn Y E) := by
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : y⁻¹ * (a : G) * y ∈ E := by
      have := Subgroup.mem_subgroupOf.mp ha
      rwa [mem_conjSub_iff] at this
    rw [mem_conjSub_iff]
    refine ⟨⟨y⁻¹ * (a : G) * y, Y.mul_mem (Y.mul_mem (Y.inv_mem hy) a.2) hy⟩,
      Subgroup.mem_subgroupOf.mpr ha', ?_⟩
    simp
    rfl
  · intro hq
    rw [mem_conjSub_iff] at hq
    obtain ⟨b, hb, hbq⟩ := hq
    refine ⟨⟨y, hy⟩ * b * ⟨y, hy⟩⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      rw [mem_conjSub_iff]
      have h1 := Subgroup.mem_subgroupOf.mp hb
      have e : y⁻¹ * ((⟨y, hy⟩ * b * ⟨y, hy⟩⁻¹ : ↥Y) : G) * y = (b : G) := by
        simp [mul_assoc]
      rw [e]
      exact h1
    · have e : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)
          (⟨y, hy⟩ * b * ⟨y, hy⟩⁻¹) =
          QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨y, hy⟩ *
            QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) b *
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨y, hy⟩)⁻¹ := by
        simp
      rw [e, hbq]
      group

end Lift

section PowFour

variable {H Q : Type*} [Group H] [Group Q] [Finite H]

theorem exists_pow_orderOf_four_lift (φ : H →* Q) (hker : Odd (Nat.card φ.ker)) {x : H}
    (hx : orderOf (φ x) = 4) : ∃ k : ℕ, orderOf (x ^ k) = 4 := by
  have hpos : 0 < orderOf x := orderOf_pos x
  obtain ⟨a, b, hb, hn⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hgcd : Nat.gcd (orderOf x) b = b := by
    rw [hn]
    exact Nat.gcd_eq_right (Dvd.intro_left _ rfl)
  have hu : orderOf (x ^ b) = 2 ^ a := by
    rw [orderOf_pow' x hb0, hgcd]
    conv_lhs => rw [hn]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)
  have hcop : Nat.Coprime 4 b := by
    have : Nat.Coprime (2 ^ 2) b := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hb)
    simpa using this
  have hφu : orderOf (φ (x ^ b)) = 4 := by
    rw [map_pow, orderOf_pow' _ hb0, hx, Nat.Coprime.gcd_eq_one hcop]
  refine ⟨b, ?_⟩
  have hv : (x ^ b) ^ 4 ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, ← hφu]
    exact pow_orderOf_eq_one _
  have hvdvd : orderOf ((x ^ b) ^ 4) ∣ Nat.card φ.ker :=
    Subgroup.orderOf_dvd_natCard φ.ker hv
  have hvdvd2 : orderOf ((x ^ b) ^ 4) ∣ 2 ^ a := by
    have := orderOf_pow_dvd (x := x ^ b) 4
    rwa [hu] at this
  have hvone : orderOf ((x ^ b) ^ 4) = 1 := by
    have hc : Nat.Coprime (2 ^ a) (Nat.card φ.ker) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hker)
    exact Nat.eq_one_of_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hvdvd2 hvdvd)
  have h4 : (x ^ b) ^ 4 = 1 := orderOf_eq_one_iff.mp hvone
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one h4
  · rw [← hφu]
    exact orderOf_map_dvd φ (x ^ b)

end PowFour

section Pair


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem layerS3Pair_of_layerS3 [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    (hL : Q3AM.LayerS3 Ω K z) : Q3AM.LayerS3Pair Ω K J z t := by
  classical
  have hstd := h.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hJcore : exactCore3 z J ≤ nbrLayer Ω K z := exactCore3_le_nbrLayer hstd.hJ
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hstd.hJ hstd.ht
  have htJ : t ∈ exactCore3 z J :=
    ⟨hstd.ht.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  have hS : S3Shape (Q3AM.layerFam Ω K z) := by
    obtain ⟨ι, _, D, i₁, hi, hk⟩ := hL
    exact S3Shape.of_lieSystemData3 D hi hk
  have hJfam : Q3AM.layerImage Ω K z J ∈ Q3AM.layerFam Ω K z :=
    ⟨_, ⟨exactCore3 z J, ⟨⟨J, hstd.hJ, rfl⟩, exactCore3_le_centralizer z J⟩, hJcore, rfl⟩, rfl⟩
  have hut : IsUniqueInvolution (exactCore3 z J) t :=
    ⟨htJ, hstd.ht.ne_one, hstd.ht.sq, fun y hy hy2 =>
      hstd.ht.unique y (exactCore3_le_left z J hy) hy2⟩
  have hu := isUniqueInvolution_modOddIn hJcore hut
  obtain ⟨g, hne, w, hw, hw4, hcomm⟩ := hS.exists_order4 hJfam hu
  obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) g
  have hyY : (y' : G) ∈ nbrLayer Ω K z := y'.2
  have hyC : (y' : G) ∈ Subgroup.centralizer ({z} : Set G) := nbrLayer_le_centralizer Ω K z hyY
  have hyz : (y' : G) * z * (y' : G)⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hyC
    rw [this]
    group
  have hN : conjSub (y' : G) J ∈ omegaNbr Ω K := h.conjSub_mem_omegaNbr hyC hstd.hJ
  have hcore : exactCore3 z (conjSub (y' : G) J) = conjSub (y' : G) (exactCore3 z J) := by
    have := exactCore3_conjSub (y' : G) z J
    rwa [hyz] at this
  have himg : Q3AM.layerImage Ω K z (conjSub (y' : G) J) =
      conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) y')
        (Q3AM.layerImage Ω K z J) := by
    show modOddIn (nbrLayer Ω K z) (exactCore3 z (conjSub (y' : G) J)) = _
    rw [hcore]
    exact modOddIn_conj hyY
  refine ⟨conjSub (y' : G) J, hN, ?_, ?_⟩
  · rw [himg]
    exact hne
  · have hw' : w ∈ Q3AM.layerImage Ω K z (conjSub (y' : G) J) := himg ▸ hw
    obtain ⟨x', hx', hxw⟩ := hw'
    have hker : Odd (Nat.card (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(nbrLayer Ω K z))).ker) := by
      rw [QuotientGroup.ker_mk']
      exact CFSG.ComponentClassification.OddCore.odd_card _
    obtain ⟨k, hk⟩ := exists_pow_orderOf_four_lift (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(nbrLayer Ω K z))) hker (x := x') (by rw [hxw]; exact hw4)
    have hx'N : (x' : G) ∈ exactCore3 z (conjSub (y' : G) J) := Subgroup.mem_subgroupOf.mp hx'
    refine ⟨((x' ^ k : ↥(nbrLayer Ω K z)) : G), ?_, ?_, ?_⟩
    · rw [Subgroup.coe_pow]
      exact Subgroup.pow_mem _ hx'N k
    · rw [Subgroup.orderOf_coe]
      exact hk
    · have hu' : ((x' ^ k : ↥(nbrLayer Ω K z)) : G) ∈ nbrLayer Ω K z := (x' ^ k).2
      have htY : t ∈ nbrLayer Ω K z := hJcore htJ
      have hmk : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z))
          ⟨((x' ^ k : ↥(nbrLayer Ω K z)) : G), hu'⟩ =
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) x') ^ k := by
        rw [← map_pow]
      have himgs : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩ *
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z))
            ⟨((x' ^ k : ↥(nbrLayer Ω K z)) : G), hu'⟩ =
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z))
            ⟨((x' ^ k : ↥(nbrLayer Ω K z)) : G), hu'⟩ *
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩ := by
        rw [hmk, hxw]
        exact ((Commute.pow_left (show Commute w
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩) from hcomm)
          k).eq).symm
      exact (mk_comm_eq_iff htY hu').mp himgs

theorem not_mem_nbrLayer_of_layerS3 (h : BadStd8 Ω K J S R T W z t)
    (hL : Q3AM.LayerS3 Ω K z) : z ∉ nbrLayer Ω K z := by
  intro hzY
  have hstd := h.std
  have hS : S3Shape (Q3AM.layerFam Ω K z) := by
    obtain ⟨ι, _, D, i₁, hi, hk⟩ := hL
    exact S3Shape.of_lieSystemData3 D hi hk
  have hZ := hS.center_eq_bot
  have hcent : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hzY⟩ ∈
      Subgroup.center (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (nbrLayer_le_centralizer Ω K z y.2))
  rw [hZ, Subgroup.mem_bot] at hcent
  have hmem : (⟨z, hzY⟩ : ↥(nbrLayer Ω K z)) ∈
      classicalInvolutionOddCore ↥(nbrLayer Ω K z) := (QuotientGroup.eq_one_iff _).mp hcent
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(nbrLayer Ω K z))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have h1 : orderOf (⟨z, hzY⟩ : ↥(nbrLayer Ω K z)) ∣
      Nat.card (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) :=
    Subgroup.orderOf_dvd_natCard _ hmem
  have h2 : orderOf (⟨z, hzY⟩ : ↥(nbrLayer Ω K z)) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using hstd.hz.sq))
  have hc : Nat.Coprime 2 (Nat.card (classicalInvolutionOddCore ↥(nbrLayer Ω K z))) :=
    Nat.coprime_two_left.mpr hodd
  have h3 : orderOf (⟨z, hzY⟩ : ↥(nbrLayer Ω K z)) = 1 :=
    Nat.eq_one_of_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd h2 h1)
  exact hstd.hz.ne_one (congrArg Subtype.val (orderOf_eq_one_iff.mp h3))

end Pair

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
