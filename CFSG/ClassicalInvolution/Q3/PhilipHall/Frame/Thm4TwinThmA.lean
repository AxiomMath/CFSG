module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinSix13
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDich

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace Thm4Twin

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

omit [Finite G] in
theorem TwinT4Hyp.three_le (h : TwinT4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ) : 3 ≤ r := by
  by_contra hr
  obtain ⟨-, P, hP, hPnc⟩ := h.hyp.omega1 J hJ
  obtain ⟨e⟩ := h.quat J hJ P hP
  have hn : 2 ^ (r - 2) = 1 := by
    rw [Nat.sub_eq_zero_of_le (by omega), pow_zero]
  have hcyc : IsCyclic (QuaternionGroup (2 ^ (r - 2))) := by
    rw [hn]
    exact QuaternionGroup.quaternionGroup_one_isCyclic
  refine hPnc ⟨⟨fun a b => e.injective ?_⟩⟩
  rw [map_mul, map_mul]
  exact (IsCyclic.isMulCommutative (α := QuaternionGroup (2 ^ (r - 2)))).is_comm.comm _ _

theorem TwinT4Hyp.q8Datum (h : TwinT4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ) {u : G}
    (hu : IsUniqueInvolution J u) (S : Sylow 2 ↥J) : Q8TwinDatum J S u := by
  have hS := isSylow2In_map_sylow J S
  obtain ⟨e⟩ := h.quat J hJ _ hS
  have e' : ↥(S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)) :=
    ((S : Subgroup J).equivMapOfInjective J.subtype J.subtype_injective).trans e
  have hcent : J ≤ Subgroup.centralizer ({u} : Set G) := isUniqueInvolution_le_centralizer hu
  refine ⟨⟨r, h.three_le hJ, ⟨e'⟩⟩, ?_, orderOf_eq_prime (by rw [pow_two]; exact hu.sq)
    hu.ne_one, hcent, h.twoGroup J hJ⟩
  refine TL4.mem_of_isPGroup_of_ne_bot hu hS.1 hS.2.1 fun hbot => ?_
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨x, hx⟩ := exists_ne (1 : QuaternionGroup (2 ^ (r - 2)))
  apply hx
  have h1 : e.symm x = 1 :=
    Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp hbot _ (e.symm x).2)
  rw [← e.apply_symm_apply x, h1, map_one]

omit [Finite G] in
theorem TwinT4Hyp.tightCore_eq (h : TwinT4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ) :
    tightCore J = J :=
  h.gen hJ

theorem TwinT4Hyp.hypOmegaGen_conjClass (h : TwinT4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ) :
    HypOmegaGen (CoreAssembly.conjClass (tightCore J)) := by
  rw [h.tightCore_eq hJ]
  refine hypOmegaGen_sub h.hyp ?_ (TL4.conjInvariant_conjClass J)
  rintro _ ⟨g, rfl⟩
  exact h.hyp.conjInvariant g J hJ

end Thm4Twin

open Thm4Twin

@[expose] def Thm4TwinThmA (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Δ : Set (Subgroup G)), TwinT4Hyp r G Δ →
    ∀ J ∈ Δ, ∀ u : G, IsUniqueInvolution J u → ¬ TightInO2 u →
      ∀ A : Subgroup G, CFSG.IsComponent A → ∀ x ∈ J, conjSub x A = A

theorem thm4TwinThmA_three : Thm4TwinThmA 3 := by
  intro G _ _ Δ h J hJ u hu hno A hA x hx
  have hle : J ≤ Subgroup.normalizer (A : Set G) := by
    rw [← h.gen hJ, Subgroup.closure_le]
    rintro y ⟨hyJ, hy2⟩
    have hy2' : IsPGroup 2 ↥((Subgroup.zpowers y).subgroupOf J) :=
      hy2.comap_of_injective _ (Subgroup.subtype_injective _)
    obtain ⟨S, hS⟩ := hy2'.exists_le_sylow
    have hyS : y ∈ (S : Subgroup J).map J.subtype :=
      ⟨⟨y, hyJ⟩, hS (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y)), rfl⟩
    have hd := h.q8Datum hJ hu S
    have hq8 : Nonempty (↥(S : Subgroup J) ≃* QuaternionGroup 2) := by
      obtain ⟨e⟩ := h.quat J hJ _ (isSylow2In_map_sylow J S)
      exact ⟨((S : Subgroup J).equivMapOfInjective J.subtype J.subtype_injective).trans e⟩
    exact mem_normalizer_iff_conjSub_eq.mpr
      (thmA_twin hd hq8 (h.hypOmegaGen_conjClass hJ) h.odd hno hA hyS)
  exact mem_normalizer_iff_conjSub_eq.mp (hle hx)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
