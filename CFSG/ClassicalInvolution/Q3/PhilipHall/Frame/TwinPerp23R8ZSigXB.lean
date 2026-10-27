module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigXA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

theorem exists_normal_two_of_inO2 {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} {t : Y}
    (htN : t ∈ N) (ht2 : t * t = 1)
    (hOc : ∀ o ∈ oddCoreOf N, ∀ y ∈ N, o * y = y * o)
    (hO2 : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥N) (⟨t, htN⟩ : ↥N))) :
    ∃ V : Subgroup Y, IsPGroup 2 V ∧ t ∈ V ∧ ∀ y ∈ N, ∀ v ∈ V, y * v * y⁻¹ ∈ V := by
  obtain ⟨Pb, hPbn, hPb2, htPb⟩ := hO2
  set f := QuotientGroup.mk' (classicalInvolutionOddCore ↥N)
  set P : Subgroup ↥N := Pb.comap f
  haveI : P.Normal := hPbn.comap f
  haveI : Group.IsNilpotent ↥P := by
    haveI : Group.IsNilpotent ↥Pb := hPb2.isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center (f.subgroupComap Pb) fun m hm => ?_
    have hm1 : f (m : ↥N) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hm)
    have hmO : ((m : ↥N) : Y) ∈ oddCoreOf N :=
      ⟨_, (QuotientGroup.eq_one_iff _).mp hm1, rfl⟩
    exact Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subtype.ext (hOc _ hmO _ (g : ↥N).2).symm)
  set x : ↥P := ⟨⟨t, htN⟩, htPb⟩
  have hxx : x ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (Subtype.ext ht2)
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hxx)
  obtain ⟨Q, hQ⟩ := hx2.exists_le_sylow
  haveI : (Q : Subgroup ↥P).Characteristic := Sylow.characteristic_of_normal Q inferInstance
  have hQN : ((Q : Subgroup ↥P).map P.subtype).Normal := inferInstance
  refine ⟨((Q : Subgroup ↥P).map P.subtype).map N.subtype, (Q.isPGroup'.map _).map _,
    ⟨_, ⟨x, hQ (Subgroup.mem_zpowers x), rfl⟩, rfl⟩, ?_⟩
  rintro y hy _ ⟨w, hw, rfl⟩
  exact ⟨_, hQN.conj_mem w hw ⟨y, hy⟩, rfl⟩


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23E8ZSigX0_of_inO2 (hP : TL4.TightBelowRPlus 3 n) (hT : Thm4RTwinBelow 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hA6 : SecAE R e 6) {x : Y}
    (hne : conjSub x (rLayer (Om R) e) ≠ rLayer (Om R) e) (htwo : ∀ J ∈ Om R, IsPGroup 2 J)
    (heb : ∀ J ∈ Om R, J ≤ conjSub x (rLayer (Om R) e) →
      ∃ y ∈ p23XE R e x, conjSub y (tightCore R) = J)
    (htN : t ∈ p23XE R e x)
    (hOc : ∀ o ∈ oddCoreOf (p23XE R e x), ∀ y ∈ p23XE R e x, o * y = y * o)
    (hO2 : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(p23XE R e x))
      (⟨t, htN⟩ : ↥(p23XE R e x)))) :
    ∃ x₀ ∈ p23XE R e x, x₀ * t = t * x₀ ∧ IsPGroup 3 (Subgroup.zpowers x₀) ∧
      x₀ * e * x₀⁻¹ ≠ e := by
  obtain ⟨V, hV2, htV, hVn⟩ := exists_normal_two_of_inO2 htN
    (Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum).sq hOc hO2
  exact p23E8ZSigX0_of_normal_two hP hT hc hA6 hne htwo heb hV2 htV hVn

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
