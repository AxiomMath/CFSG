module

public import CFSG.ClassicalInvolution.Q3.Q3YQuat
public import CFSG.ClassicalInvolution.Uniform.USat
public import CFSG.ClassicalInvolution.Uniform.UFacade
public import CFSG.ClassicalInvolution.Balance.GoodDataBasic
public import CFSG.ClassicalInvolution.Q3.Q3TEdge
public import CFSG.ClassicalInvolution.Q3.Q3YAbs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement

variable {G : Type} [Group G]

section Edge

theorem exists_member_commuting_involution [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
    (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z) (hΔ : DeltaConnected K)
    {w : G} (hw : ∃ g : G, w = g * z * g⁻¹) :
    ∃ (J : Subgroup G) (t : G), J ∈ conjClass3 K ∧ IsClassicalMember3 J t ∧ t ≠ w ∧
      t * w = w * t := by
  obtain ⟨E₁, E₂, e₁, e₂, he⟩ := exists_edge3 hnab hz hΔ
  obtain ⟨g, hg⟩ := hw
  obtain ⟨g', -, hg'⟩ := conjClass3_involution hz he.mem₁ he.cls₁
  obtain ⟨h, hh⟩ := he.mem₂
  have hh' : conjSub h K = E₂ := hh
  have hc : (g * g'⁻¹) * e₁ * (g * g'⁻¹)⁻¹ = w := by rw [hg, hg']; group
  refine ⟨conjSub (g * g'⁻¹) E₂, (g * g'⁻¹) * e₂ * (g * g'⁻¹)⁻¹, ⟨g * g'⁻¹ * h, ?_⟩,
    he.cls₂.conj _, ?_, ?_⟩
  · show conjSub (g * g'⁻¹ * h) K = conjSub (g * g'⁻¹) E₂
    rw [conjSub_mul, hh']
  · intro hcon
    apply he.ne
    rw [← hc] at hcon
    exact (mul_left_cancel (mul_right_cancel hcon)).symm
  · rw [← hc]
    have := he.comm_involutions
    calc (g * g'⁻¹) * e₂ * (g * g'⁻¹)⁻¹ * ((g * g'⁻¹) * e₁ * (g * g'⁻¹)⁻¹)
        = (g * g'⁻¹) * (e₂ * e₁) * (g * g'⁻¹)⁻¹ := by group
      _ = (g * g'⁻¹) * (e₁ * e₂) * (g * g'⁻¹)⁻¹ := by rw [this]
      _ = (g * g'⁻¹) * e₁ * (g * g'⁻¹)⁻¹ * ((g * g'⁻¹) * e₂ * (g * g'⁻¹)⁻¹) := by group

end Edge

section Core

variable [Finite G]

theorem commutator_le_oddCoreIn_of_le {K₁ K₂ R : Subgroup G} {w : G}
    (hR : R ≤ Subgroup.centralizer ({w} : Set G)) (hK₁ : K₁ ≤ R) (hK₂ : K₂ ≤ R)
    (h : ⁅K₁, K₂⁆ ≤ Balance.oddCoreIn (Subgroup.centralizer ({w} : Set G))) :
    ⁅K₁, K₂⁆ ≤ Balance.oddCoreIn R := by
  set Q := Balance.oddCoreIn (Subgroup.centralizer ({w} : Set G)) with hQ
  have hnormQ := Balance.normalizer_oddCoreIn (Subgroup.centralizer ({w} : Set G))
  have hS : Q ⊓ R ≤ Balance.oddCoreIn R := by
    refine Balance.le_oddCoreIn_of_normalizes inf_le_right ?_ ?_
    · intro r hr
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.mp (hnormQ (hR hr)) y
      have h2 : y ∈ R ↔ r * y * r⁻¹ ∈ R := by
        constructor
        · intro hy
          exact R.mul_mem (R.mul_mem hr hy) (R.inv_mem hr)
        · intro hy
          have := R.mul_mem (R.mul_mem (R.inv_mem hr) hy) hr
          simpa [mul_assoc] using this
      simp only [Subgroup.mem_inf]
      rw [h1, h2]
    · exact Odd.of_dvd_nat (Balance.odd_card_oddCoreIn _) (Subgroup.card_dvd_of_le inf_le_left)
  refine le_trans ?_ hS
  refine le_inf h ?_
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := rfl
  rw [this]
  exact R.mul_mem (R.mul_mem (R.mul_mem (hK₁ hx) (hK₂ hy)) (R.inv_mem (hK₁ hx)))
    (R.inv_mem (hK₂ hy))

end Core

section Twin

variable [Finite G]

theorem false_of_twin_pair {Ω : Set (Subgroup G)} (hB : ¬ BootData3 Ω) {K₁ K₂ J : Subgroup G}
    {w t : G} (hJΩ : J ∈ Ω) (hJ : IsClassicalMember3 J t) (hK₁ : IsClassicalMember3 K₁ w)
    (hK₂ : IsClassicalMember3 K₂ w)
    (hcomm : ⁅K₁, K₂⁆ ≤ Balance.oddCoreIn (Subgroup.centralizer ({w} : Set G)))
    (hJ₁ : Commutes J K₁) (hJ₂ : Commutes J K₂) (hne : t ≠ w) (htw : t * w = w * t) : False := by
  classical
  set R : Subgroup G := Subgroup.centralizer (J : Set G) ⊓ Subgroup.centralizer ({w} : Set G)
    with hR
  have hK₁w : K₁ ≤ Subgroup.centralizer ({w} : Set G) := isSubnormal_le hK₁.subnormal
  have hK₂w : K₂ ≤ Subgroup.centralizer ({w} : Set G) := isSubnormal_le hK₂.subnormal
  have hK₁R : K₁ ≤ R := fun x hx =>
    ⟨Subgroup.mem_centralizer_iff.mpr fun j hj => hJ₁ j hj x hx, hK₁w hx⟩
  have hK₂R : K₂ ≤ R := fun x hx =>
    ⟨Subgroup.mem_centralizer_iff.mpr fun j hj => hJ₂ j hj x hx, hK₂w hx⟩
  have hRw : R ≤ Subgroup.centralizer ({w} : Set G) := inf_le_right
  have hRJ : R ≤ Subgroup.centralizer (J : Set G) := inf_le_left
  have hwR : w ∈ R := hK₁R hK₁.mem
  have hw2 : w * w = 1 := hK₁.isCentralInvolution.sq
  have ht2 : t * t = 1 := hJ.isCentralInvolution.sq
  have htR : t ∈ R :=
    ⟨Subgroup.mem_centralizer_iff.mpr fun j hj => (hJ.isCentralInvolution.central j hj).symm,
      Subgroup.mem_centralizer_singleton_iff.mpr htw⟩
  have hQR : ⁅K₁, K₂⁆ ≤ Balance.oddCoreIn R := commutator_le_oddCoreIn_of_le hRw hK₁R hK₂R hcomm
  set ρ := QuotientGroup.mk' (classicalInvolutionOddCore ↥R) with hρ
  have himg : ∀ (x y v : G) (hx : x ∈ R) (hy : y ∈ R) (hv : v ∈ R), x * y = v →
      ρ ⟨x, hx⟩ * ρ ⟨y, hy⟩ = ρ ⟨v, hv⟩ := by
    intro x y v hx hy hv hxyv
    rw [← map_mul]
    exact congrArg ρ (Subtype.ext hxyv)
  have hsqρ : ∀ (x : G) (hx : x ∈ R), x * x = 1 → ρ ⟨x, hx⟩ * ρ ⟨x, hx⟩ = 1 := by
    intro x hx hx2
    rw [← map_mul]
    have : (⟨x, hx⟩ : ↥R) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hF : ∀ F : Subgroup (↥R ⧸ classicalInvolutionOddCore ↥R), IsElemAbelian 2 F →
      Nat.card F = 4 → ρ ⟨t, htR⟩ ∈ F := by
    intro F hF hcard
    obtain ⟨H, hH, hHF, hHcard⟩ := Balance.GoodData.exists_isElemAbelian_lift_map
      (classicalInvolutionOddCore ↥R) (CFSG.ComponentClassification.OddCore.odd_card ↥R) F hF
    have hH'card : Nat.card (H.map R.subtype) = 4 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective R), hHcard, hcard]
    have hsq : ∀ x ∈ H.map R.subtype, x * x = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      have := hH.2 x hx
      rw [pow_two] at this
      exact congrArg Subtype.val this
    have hcomm' : ∀ x ∈ H.map R.subtype, ∀ y ∈ H.map R.subtype, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have := hH.1.is_comm.comm (⟨x, hx⟩ : H) ⟨y, hy⟩
      exact congrArg (fun s : H => ((s : ↥R) : G)) this
    have hcent : J ≤ Subgroup.centralizer ((H.map R.subtype : Subgroup G) : Set G) := by
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp (hRJ x.2) j hj).symm
    have ht' : t ∈ H.map R.subtype :=
      mem_fourGroup_of_not_bootData3 hB hJΩ hJ hsq hcomm' hH'card hcent
    obtain ⟨x, hxH, hxt⟩ := ht'
    have hx : x = ⟨t, htR⟩ := Subtype.ext hxt
    rw [← hHF]
    exact ⟨x, hxH, by rw [hx]⟩
  have hw1 : ρ ⟨t, htR⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution R htR ht2 hJ.ne_one
  have hBD : ∀ p q : ↥R ⧸ classicalInvolutionOddCore ↥R, p ∈ (⊤ : Subgroup _) →
      q ∈ (⊤ : Subgroup _) → p * p = 1 → q * q = 1 → p ≠ 1 → q ≠ 1 → p ≠ q → p * q = q * p →
        ρ ⟨t, htR⟩ = p ∨ ρ ⟨t, htR⟩ = q ∨ ρ ⟨t, htR⟩ = p * q :=
    fun p q _ _ hp2 hq2 hp1 hq1 hpq hc =>
      Q3Y.bd_pair_of_forall_fourGroup hw1 hF hp2 hq2 hp1 hq1 hpq hc
  obtain ⟨x₁, hx₁, y₁, hy₁, hx₁x₁, hy₁y₁, hxy⟩ := hK₁.exists_quaternion_pair_sq
  obtain ⟨x₂, hx₂, -, -, hx₂x₂, -, -⟩ := hK₂.exists_quaternion_pair_sq
  have hx₁R : x₁ ∈ R := hK₁R hx₁
  have hy₁R : y₁ ∈ R := hK₁R hy₁
  have hx₂R : x₂ ∈ R := hK₂R hx₂
  have hζ1 : ρ ⟨w, hwR⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution R hwR hw2 hK₁.ne_one
  have hne_ρ : ρ ⟨t, htR⟩ ≠ ρ ⟨w, hwR⟩ := by
    intro h
    have htwR : t * w ∈ R := R.mul_mem htR hwR
    have htw2 : (t * w) * (t * w) = 1 := by
      calc (t * w) * (t * w) = t * (w * t) * w := by group
        _ = t * (t * w) * w := by rw [← htw]
        _ = (t * t) * (w * w) := by group
        _ = 1 := by rw [ht2, hw2, one_mul]
    have htw1 : t * w ≠ 1 := by
      intro h1
      apply hne
      have := eq_inv_of_mul_eq_one_left h1
      rw [this, inv_eq_of_mul_eq_one_right hw2]
    apply Q3Y.mk_ne_one_of_involution R htwR htw2 htw1
    have : (⟨t * w, htwR⟩ : ↥R) = ⟨t, htR⟩ * ⟨w, hwR⟩ := rfl
    rw [this, map_mul, h, hsqρ w hwR hw2]
  have hnc : ρ ⟨x₁, hx₁R⟩ * ρ ⟨y₁, hy₁R⟩ ≠ ρ ⟨y₁, hy₁R⟩ * ρ ⟨x₁, hx₁R⟩ := by
    intro h
    have h1 := (mk_comm_eq_iff hx₁R hy₁R).mp h
    rw [hxy] at h1
    exact hK₁.ne_one (eq_one_of_mem_of_odd_of_sq (Balance.odd_card_oddCoreIn R) h1 hw2)
  have hab : ρ ⟨x₁, hx₁R⟩ * ρ ⟨x₂, hx₂R⟩ = ρ ⟨x₂, hx₂R⟩ * ρ ⟨x₁, hx₁R⟩ :=
    (mk_comm_eq_iff hx₁R hx₂R).mpr (hQR (Subgroup.commutator_mem_commutator hx₁ hx₂))
  have ha'b : ρ ⟨y₁, hy₁R⟩ * ρ ⟨x₂, hx₂R⟩ = ρ ⟨x₂, hx₂R⟩ * ρ ⟨y₁, hy₁R⟩ :=
    (mk_comm_eq_iff hy₁R hx₂R).mpr (hQR (Subgroup.commutator_mem_commutator hy₁ hx₂))
  exact Q3Y.false_of_quaternion_pair (⊤ : Subgroup (↥R ⧸ classicalInvolutionOddCore ↥R))
    (ζ := ρ ⟨w, hwR⟩) (w := ρ ⟨t, htR⟩) (a := ρ ⟨x₁, hx₁R⟩) (a' := ρ ⟨y₁, hy₁R⟩)
    (b := ρ ⟨x₂, hx₂R⟩) hζ1 (hsqρ w hwR hw2) (himg x₁ x₁ w hx₁R hx₁R hwR hx₁x₁)
    (himg y₁ y₁ w hy₁R hy₁R hwR hy₁y₁) (himg x₂ x₂ w hx₂R hx₂R hwR hx₂x₂) hnc hab ha'b
    (Subgroup.mem_top _) (Subgroup.mem_top _) (Subgroup.mem_top _) hne_ρ hBD

end Twin

section Sat

variable [Finite G] [IsSimpleGroup G]

theorem satU_eq_of_involution_eq {K : Subgroup G} {z : G} (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K))
    (hA2 : ¬ A2Configuration z K) {K₁ K₂ : Subgroup G} {w : G} (hK₁ : K₁ ∈ conjClass3 K)
    (hK₂ : K₂ ∈ conjClass3 K) (hw₁ : IsClassicalMember3 K₁ w) (hw₂ : IsClassicalMember3 K₂ w) :
    satU (.sl2 3 1) K₁ w = satU (.sl2 3 1) K₂ w := by
  by_contra hne
  have hm₁ := (IsClassicalMemberU.ofQ3 hw₁).satU_member
  have hm₂ := (IsClassicalMemberU.ofQ3 hw₂).satU_member
  obtain ⟨-, -, -, hQ⟩ := twins_of_memberU hm₁ hm₂ (isIntrinsicU_satU _ _ _)
    (isIntrinsicU_satU _ _ _) hne
  have hQ' : ⁅K₁, K₂⁆ ≤ Balance.oddCoreIn (Subgroup.centralizer ({w} : Set G)) :=
    (Subgroup.commutator_mono le_satU le_satU).trans hQ
  obtain ⟨g, -, hg⟩ := conjClass3_involution hz hK₁ hw₁
  obtain ⟨J, t, hJ, hJt, hne', hc'⟩ := exists_member_commuting_involution hnab hz hΔ ⟨g, hg⟩
  exact false_of_twin_pair hB hJ hJt hw₁ hw₂ hQ'
    (commutes_of_not_a2Configuration3 hz hA2 hJ hK₁ hJt hw₁ hne' hc')
    (commutes_of_not_a2Configuration3 hz hA2 hJ hK₂ hJt hw₂ hne' hc') hne' hc'

theorem noTwins3_of_typeC {K : Subgroup G} {z : G} (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K))
    (hA2 : ¬ A2Configuration z K) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass (satU (.sl2 3 1) K z)) (hU : IsUniqueInvolution J z) :
    J = satU (.sl2 3 1) K z := by
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class _ J hJ
  rw [← satU_conj (.sl2 3 1) K z g] at hU ⊢
  have hm := (IsClassicalMemberU.ofQ3 (hz.conj g)).satU_member
  have hgz : g * z * g⁻¹ = z := (hm.isUniqueInvolution (MemberType.cert_sl2 3 1)).eq hU
  rw [hgz] at hm ⊢
  have hz' : IsClassicalMember3 (conjSub g K) z := hgz ▸ hz.conj g
  exact satU_eq_of_involution_eq hnab hz hΔ hB hA2 ⟨g, rfl⟩ ⟨1, conjSub_one K⟩ hz' hz

end Sat

end CFSG.ClassicalInvolution.Q3.Q3CP
