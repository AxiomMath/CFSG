module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinTwoA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

omit [Finite G] in
theorem transitive_of_eq_at (hΩ : HypOmegaGen Δ) {t : G}
    (hF : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → ∃ g : G, g * z * g⁻¹ = t)
    (hU : ∀ K ∈ Δ, ∀ K' ∈ Δ, IsUniqueInvolution K t → IsUniqueInvolution K' t → K = K') :
    ∀ J ∈ Δ, ∀ L ∈ Δ, ∃ g : G, conjSub g J = L := by
  intro J hJ L hL
  obtain ⟨⟨zJ, hzJ⟩, -⟩ := hΩ.omega1 J hJ
  obtain ⟨⟨zL, hzL⟩, -⟩ := hΩ.omega1 L hL
  obtain ⟨a, ha⟩ := hF J hJ zJ hzJ
  obtain ⟨b, hb⟩ := hF L hL zL hzL
  have h1 : IsUniqueInvolution (conjSub a J) t := by
    rw [← ha]
    exact hzJ.conj a
  have h2 : IsUniqueInvolution (conjSub b L) t := by
    rw [← hb]
    exact hzL.conj b
  have heq := hU _ (hΩ.conjInvariant a J hJ) _ (hΩ.conjInvariant b L hL) h1 h2
  refine ⟨b⁻¹ * a, ?_⟩
  rw [conjSub_mul, heq, conjSub_inv_conjSub]

theorem eq_of_four_dvd (hΩ : HypOmegaGen Δ) {K J : Subgroup G} (hK : K ∈ Δ) (hJ : J ∈ Δ)
    (h4 : 4 ∣ Nat.card ↥(K ⊓ J)) : K = J := by
  by_contra hne
  have h1 := (hΩ.omega4 K hK J hJ hne).1
  have hpos : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
  have h2 : 2 ≤ padicValNat 2 (Nat.card ↥(K ⊓ J)) :=
    (padicValNat_dvd_iff_le (p := 2) hpos).mp (by simpa using h4)
  omega

theorem eq_of_orderOf_eq_four (hΩ : HypOmegaGen Δ) {K J : Subgroup G} (hK : K ∈ Δ) (hJ : J ∈ Δ)
    {x : G} (hxK : x ∈ K) (hxJ : x ∈ J) (hx : orderOf x = 4) : K = J := by
  refine eq_of_four_dvd hΩ hK hJ ?_
  have hle : Subgroup.zpowers x ≤ K ⊓ J := Subgroup.zpowers_le.mpr ⟨hxK, hxJ⟩
  rw [← hx, ← Nat.card_zpowers]
  exact Subgroup.card_dvd_of_le hle

omit [Finite G] in
theorem le_centralizer_of_isUniqueInvolution {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) : K ≤ Subgroup.centralizer ({z} : Set G) :=
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3.le_centralizer_of_uniqueInvolution hz

omit [Finite G] in
theorem isSubnormal_subgroupOf' {A B : Subgroup G} (h : IsSubnormal A B) :
    (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

theorem commute_of_component (h : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ) {M : Subgroup G}
    (hM : M ∈ Δ) {t : G} (ht : IsUniqueInvolution M t) {J : Subgroup G}
    (hJC : J ≤ Subgroup.centralizer ({t} : Set G))
    (hJ : CFSG.IsComponent (J.subgroupOf (Subgroup.centralizer ({t} : Set G)))) (htJ : t ∈ J) :
    ∀ x ∈ M, ∀ y ∈ J, x * y = y * x := by
  set C := Subgroup.centralizer ({t} : Set G) with hCdef
  have hMs : (M.subgroupOf C).IsSubnormal :=
    isSubnormal_subgroupOf' (h.isSubnormal_centralizer hM ht)
  rcases CFSG.LocalCores.component_subnormal_subgroup hJ hMs with hle | hcomm
  · exfalso
    have hJM : J ≤ M := fun y hy => by
      have h1 : (⟨y, hJC hy⟩ : C) ∈ J.subgroupOf C := Subgroup.mem_subgroupOf.mpr hy
      exact Subgroup.mem_subgroupOf.mp (hle h1)
    have hperf : Group.IsPerfect ↥J := by
      have := hJ.1.1
      exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJC).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hJC).surjective
    set O := classicalInvolutionOddCore ↥M with hO
    let φ : ↥J →* ↥M ⧸ O := (QuotientGroup.mk' O).comp (Subgroup.inclusion hJM)
    have h2 : IsPGroup 2 φ.range := (h.twoGroup M hM).to_subgroup φ.range
    have h1 : φ ⟨t, htJ⟩ = 1 := by
      by_contra hne
      have hnt : Nontrivial φ.range :=
        ⟨⟨⟨φ ⟨t, htJ⟩, ⟨⟨t, htJ⟩, rfl⟩⟩, 1, fun he => hne (congrArg Subtype.val he)⟩⟩
      have hpr : Group.IsPerfect φ.range := Group.IsPerfect.range φ
      exact Group.IsPerfect.not_isNilpotent φ.range h2.isNilpotent
    have htO : (⟨t, hJM htJ⟩ : ↥M) ∈ O := (QuotientGroup.eq_one_iff _).mp h1
    have h2t : IsPGroup 2 (Subgroup.zpowers (⟨t, hJM htJ⟩ : ↥M)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, pow_one]
      exact orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
    have ht1 := eq_one_of_isPGroup_of_mem_odd
      (CFSG.ComponentClassification.OddCore.odd_card ↥M) htO h2t
    exact ht.ne_one (congrArg Subtype.val ht1)
  · intro x hx y hy
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hxC : (⟨x, le_centralizer_of_isUniqueInvolution ht hx⟩ : C) ∈ M.subgroupOf C :=
      Subgroup.mem_subgroupOf.mpr hx
    have h1 := Subgroup.mem_centralizer_iff.mp (hc (Subgroup.mem_subgroupOf.mpr hy :
      (⟨y, hJC hy⟩ : C) ∈ J.subgroupOf C)) _ hxC
    exact congrArg Subtype.val h1

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
