module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf8Cls
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.GoodLift
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
open scoped commutatorElement

namespace ThmE

section Cls


variable {r : ℕ} {G : Type} [Group G] [Finite G]

theorem commOdd_of_quat {J P : Subgroup G} (h2 : IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J))
    (hP : IsSylow2In P J) (e : ↥P ≃* QuaternionGroup (2 ^ (r - 2))) {u a b : G} (hu : u ∈ J)
    (hu2 : IsPGroup 2 (Subgroup.zpowers u)) (huu : u * u ≠ 1) (ha : a ∈ J) (hb : b ∈ J)
    (hau : a * u = u * a) (hbu : b * u = u * b) : a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf J := by
  classical
  set N : Subgroup ↥J := classicalInvolutionOddCore ↥J with hN
  have hPJ : P ≤ J := hP.1
  let eP : ↥(P.subgroupOf J) ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (Subgroup.subgroupOfEquivOfLe hPJ).trans e
  set ι : ↥(P.subgroupOf J) →* ↥J ⧸ N :=
    (QuotientGroup.mk' N).comp (P.subgroupOf J).subtype with hιdef
  have hι : Function.Bijective ι := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have h1 : ((x : ↥J) : ↥J) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
      have h2 : ((x : ↥J) : G) ∈ oddCoreOf J ⊓ P :=
        ⟨⟨_, h1, rfl⟩, Subgroup.mem_subgroupOf.mp x.2⟩
      rw [TwinExact.inf_oddCoreOf_eq_bot hP.2.1, Subgroup.mem_bot] at h2
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext h2))
    · intro q
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨s, hs, o, ho, hxe⟩ := TwinExact.mem_mul_oddCore_of_sylow h2 hP x hx
      refine ⟨⟨⟨s, hPJ hs⟩, Subgroup.mem_subgroupOf.mpr hs⟩, ?_⟩
      show (QuotientGroup.mk (⟨s, hPJ hs⟩ : ↥J) : ↥J ⧸ N) = QuotientGroup.mk ⟨x, hx⟩
      rw [QuotientGroup.eq]
      obtain ⟨o', ho', rfl⟩ := ho
      have : ((⟨s, hPJ hs⟩ : ↥J)⁻¹ * ⟨x, hx⟩ : ↥J) = o' := by
        apply Subtype.ext
        simp [hxe]
      rw [this]
      exact ho'
  let eQ : (↥J ⧸ N) ≃* QuaternionGroup (2 ^ (r - 2)) := (MulEquiv.ofBijective ι hι).symm.trans eP
  let φ : ↥J →* QuaternionGroup (2 ^ (r - 2)) := eQ.toMonoidHom.comp (QuotientGroup.mk' N)
  have hφ1 : ∀ x : ↥J, φ x = 1 → x ∈ N := by
    intro x hx
    have h1 : eQ (QuotientGroup.mk' N x) = 1 := hx
    rw [MulEquiv.map_eq_one_iff] at h1
    exact (QuotientGroup.eq_one_iff x).mp h1
  have huu' : φ ⟨u, hu⟩ * φ ⟨u, hu⟩ ≠ 1 := by
    intro h1
    rw [← map_mul] at h1
    have h3 := hφ1 _ h1
    apply huu
    have h2 : IsPGroup 2 (Subgroup.zpowers (u * u)) :=
      hu2.to_le (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _ (Subgroup.mem_zpowers u)
        (Subgroup.mem_zpowers u)))
    exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J)
      (mem_oddCoreOf_iff.mpr ⟨J.mul_mem hu hu, h3⟩) h2
  have hau' : φ ⟨a, ha⟩ * φ ⟨u, hu⟩ = φ ⟨u, hu⟩ * φ ⟨a, ha⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hau)
  have hbu' : φ ⟨b, hb⟩ * φ ⟨u, hu⟩ = φ ⟨u, hu⟩ * φ ⟨b, hb⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hbu)
  have hc := quaternionGroup_comm_of_comm huu' hau' hbu'
  have hc' : φ (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥J)⁻¹ * (⟨b, hb⟩ : ↥J)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc]
    group
  exact mem_oddCoreOf_iff.mpr ⟨J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb),
    hφ1 _ hc'⟩

variable {Ω : Set (Subgroup G)}

theorem classicalClause_of_quat (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) :
    Q3CL.ClassicalClause Ω where
  subnormal := by
    intro K hK
    obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 K hK
    exact ⟨z, hz.mem, orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one,
      isSubnormal_of_hypOmegaGen hΩ hK hz⟩
  commOdd := by
    intro J hJ u a b hu hu2 huu ha hb hau hbu
    obtain ⟨P, hP, ⟨e⟩⟩ := hq8 J hJ
    exact commOdd_of_quat (h2 J hJ) hP e hu hu2 huu ha hb hau hbu

end Cls

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
