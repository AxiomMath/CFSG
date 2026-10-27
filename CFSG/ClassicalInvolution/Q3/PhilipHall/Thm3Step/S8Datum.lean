module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf16Thm3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotCongr
public import CFSG.ClassicalInvolution.Q3.Q3T6DConj

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace S8

variable {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}

omit [Finite Y] in
theorem tightCore_eq (hΦ : TypeRHyp (CoreAssembly.conjClass K)) : tightCore K = K := by
  have hK := CoreAssembly.mem_conjClass_self K
  rcases hΦ.hyp.omega2 K hK with h | h
  · exact h
  · exfalso
    obtain ⟨e⟩ := h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((hΦ.twoGroup K hK).of_equiv e)
    rw [natCard_sl2Three] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 24)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

omit [Finite Y] in
theorem iSup_conjSub_eq_top [IsSimpleGroup Y] {z : Y} (hz : IsUniqueInvolution K z) :
    (⨆ g : Y, conjSub g K) = ⊤ := by
  set N : Subgroup Y := ⨆ g : Y, conjSub g K with hN
  have hle : ∀ h : Y, conjSub h N ≤ N := by
    intro h
    have hc : conjSub h N = ⨆ g : Y, conjSub (h * g) K := by
      change (⨆ g : Y, conjSub g K).map (MulAut.conj h).toMonoidHom = _
      rw [Subgroup.map_iSup]
      congr 1
      funext g
      exact (conjSub_mul h g K).symm
    rw [hc]
    exact iSup_le fun g => le_iSup (fun g : Y => conjSub g K) (h * g)
  have hNn : N.Normal := ⟨fun n hn h => hle h (conj_mem_conjSub hn)⟩
  rcases hNn.eq_bot_or_eq_top with hbot | htop
  · exfalso
    have hKN : K ≤ N := by
      have := le_iSup (fun g : Y => conjSub g K) 1
      simpa using this
    have hmem := hKN hz.mem
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hz.ne_one hmem
  · exact htop

theorem exists_twin (hΦ : HypOmegaGen (CoreAssembly.conjClass K))
    (hA : ¬ AEmpty (CoreAssembly.conjClass K) K) :
    ∃ K' ∈ twinSet (CoreAssembly.conjClass K) K, K' ≠ K := by
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hA
  obtain ⟨a, -, -, hmem, hz', hne⟩ :=
    Q3T6D.AViol.exists_twin hΦ (CoreAssembly.mem_conjClass_self K) hv
  exact ⟨conjSub a J, ⟨hmem, zK, hv.hzK, hz'⟩, hne⟩

theorem frameTightDatum [IsSimpleGroup Y] (hΦ : TypeRHyp (CoreAssembly.conjClass K))
    (hA : ¬ AEmpty (CoreAssembly.conjClass K) K) {z : Y} (hz : IsUniqueInvolution K z) :
    FrameTightDatum K z where
  tightCore_eq := tightCore_eq hΦ
  unique := hz
  quat := hΦ.sylow K (CoreAssembly.mem_conjClass_self K)
  twoGroup := hΦ.twoGroup K (CoreAssembly.mem_conjClass_self K)
  subnormal := CentQ.isSubnormal_centralizer_gen hΦ.hyp (CoreAssembly.mem_conjClass_self K) hz
  hyp := hΦ.hyp
  selfGen := iSup_conjSub_eq_top hz
  twin := exists_twin hΦ.hyp hA

theorem exists_swap (hΦ : HypOmegaGen (CoreAssembly.conjClass K))
    (hA : ¬ AEmpty (CoreAssembly.conjClass K) K) :
    ∃ (J : Subgroup Y) (zK zJ a g : Y), AViol (CoreAssembly.conjClass K) K J zK zJ ∧
      a ∈ pairNormalizers K J zK zJ ∧ a * zJ * a⁻¹ = zK ∧ conjSub a J ≠ K ∧
      conjSub g K = conjSub a J ∧ g * zK * g⁻¹ = zK := by
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hA
  obtain ⟨a, ha, hac, -, -, hne, g, hgz, hg⟩ :=
    Q3T6D.AViol.exists_swap hΦ (CoreAssembly.mem_conjClass_self K)
      (fun M hM => by obtain ⟨g, rfl⟩ := hM; exact ⟨g, rfl⟩) hv
  exact ⟨J, zK, zJ, a, g, hv, ha, hac, hne, hg, hgz⟩

theorem exists_frameData [IsSimpleGroup Y] (hΦ : TypeRHyp (CoreAssembly.conjClass K))
    (hA : ¬ AEmpty (CoreAssembly.conjClass K) K) :
    ∃ (J : Subgroup Y) (zK zJ a g : Y), FrameTightDatum K zK ∧
      AViol (CoreAssembly.conjClass K) K J zK zJ ∧ a ∈ pairNormalizers K J zK zJ ∧
      a * zJ * a⁻¹ = zK ∧ conjSub a J ≠ K ∧ conjSub g K = conjSub a J ∧ g * zK * g⁻¹ = zK := by
  obtain ⟨J, zK, zJ, a, g, hv, ha, hac, hne, hg, hgz⟩ := exists_swap hΦ.hyp hA
  exact ⟨J, zK, zJ, a, g, frameTightDatum hΦ hA hv.hzK, hv, ha, hac, hne, hg, hgz⟩

omit [Finite Y] in
theorem nonabelian (hΦ : HypOmegaGen (CoreAssembly.conjClass K)) : ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨-, P, -, hP⟩ := hΦ.omega1 K (CoreAssembly.mem_conjClass_self K)
  by_contra h
  refine hP (IsMulCommutative.of_comm fun a b => Subtype.ext ?_)
  by_contra hab
  exact h ⟨a, b, hab⟩

end S8

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step
