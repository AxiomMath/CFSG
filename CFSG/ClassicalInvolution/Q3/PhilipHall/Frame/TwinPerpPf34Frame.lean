module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf34Transfer
public import CFSG.RankThree.PartTwo.Sec8.TransferExtremal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf10Perf
public import CFSG.ClassicalInvolution.Asc77.AscS24BFrame
public import CFSG.ClassicalInvolution.Asc77.AscS24Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9A05
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9A06

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

namespace Asc77
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.S24
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace Ctx8F
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)

include C in

theorem conj_mem_P_of_R {y : G} (hyR : y ∈ R) (hy1 : y ≠ 1) (hyz : y ≠ z) {g : G}
    (hg : g⁻¹ * y * g ∈ (S : Subgroup G)) : g⁻¹ * y * g ∈ (S : Subgroup G) ⊓ MGrp Ω W := by
  have hst := C.hs.stand
  have hΩ : HypOmegaGen Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hzK : IsUniqueInvolution K z := C.hzK
  have hRK : IsSylow2In R K := C.hRsyl
  have hnc : ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x :=
    (hΩ.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In hK hRK)).exists_not_commute
  have hy2 : y * y = z := sq_eq_of_mem_quat hzK C.hd.hR.2.1 C.h8 hnc hyR hy1 hyz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf y = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := y)
      (by rw [pow_one, pow_two, hy2]; exact hzK.ne_one)
      (by
        have : y ^ 2 ^ (1 + 1) = (y * y) * (y * y) := by
          rw [show (2 : ℕ) ^ (1 + 1) = 4 from rfl]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [this, hy2]; exact hzK.sq)
    simpa using h
  have hUy : Subgroup.zpowers y ∈ USet Ω :=
    mem_USet_of_natCard hK hRK (Subgroup.zpowers_le.mpr hyR) inferInstance
      (by rw [Nat.card_zpowers, hord, C.h8])
  have hU : conjSub g⁻¹ (Subgroup.zpowers y) ∈ USet Ω :=
    USet.conj hΩ.conjInvariant hUy g⁻¹
  have hyg : g⁻¹ * y * g ∈ conjSub g⁻¹ (Subgroup.zpowers y) := by
    rw [mem_conjSub_iff]
    refine ⟨1, ?_⟩
    simp only [inv_inv, zpow_one]
    group
  have hUS : conjSub g⁻¹ (Subgroup.zpowers y) ≤ (S : Subgroup G) := by
    intro w hw
    rw [mem_conjSub_iff] at hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
    have : w = (g⁻¹ * y * g) ^ k := by
      have hconj : (g⁻¹ * y * g) ^ k = g⁻¹ * y ^ k * g := by
        have := conj_zpow (a := g⁻¹) (b := y) (i := k)
        simpa only [inv_inv] using this
      rw [hconj, hk]
      group
    rw [this]
    exact (S : Subgroup G).zpow_mem hg k
  obtain ⟨η, hηG, hWη⟩ := C.hd.hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (hWη ▸ le_iSup₂ (f := fun V (_ : V ∈ η) => V) V hV : V ≤ W).trans C.hd.hWS
  obtain ⟨V, ⟨hVη, hcase⟩, -⟩ := l6_8 G Ω hΩ S _ hU hUS η hηG hηS
  have hUP : conjSub g⁻¹ (Subgroup.zpowers y) ≤ (S : Subgroup G) ⊓ MGrp Ω W := by
    refine le_inf hUS ?_
    rcases hcase with h | h
    · rw [h]
      exact ((hWη ▸ le_iSup₂ (f := fun V (_ : V ∈ η) => V) V hVη : V ≤ W).trans
        C.W_le_P).trans inf_le_right
    · have hR₂S : conjSub g⁻¹ (Subgroup.zpowers y) ⊔ V ≤ (S : Subgroup G) :=
        sup_le hUS (hηS V hVη)
      have hD : conjSub g⁻¹ (Subgroup.zpowers y) ⊔ V ∈ DSet Ω W :=
        ⟨h, fun x hx => C.le_normalizer_W (hR₂S hx)⟩
      exact le_sup_left.trans (le_iSup₂ (f := fun R (_ : R ∈ DSet Ω W) => R) _ hD)
  exact hUP hyg


include C in
theorem x₁_mem_of_index_le_two (B : Subgroup ↥(S : Subgroup G)) (hB : B.index ≤ 2) :
    (⟨C.D.x₁, C.hd.hR.2.2 C.x₁_mem_R⟩ : ↥(S : Subgroup G)) ∈ B := by
  have hx₃S : C.D.x₃ ∈ (S : Subgroup G) := C.hd.hWS C.D.x₃_mem
  have hrS : C.D.F.ρ.r ∈ (S : Subgroup G) := C.hd.hR.2.2 C.r_mem_R
  have h := Tr34.commutator_mem_of_index_le_two B hB ⟨C.D.x₃⁻¹, (S : Subgroup G).inv_mem hx₃S⟩
    ⟨C.D.F.ρ.r, hrS⟩
  have e : (⟨C.D.x₁, C.hd.hR.2.2 C.x₁_mem_R⟩ : ↥(S : Subgroup G)) =
      ⟨C.D.x₃⁻¹, (S : Subgroup G).inv_mem hx₃S⟩ * ⟨C.D.F.ρ.r, hrS⟩ *
        ⟨C.D.x₃⁻¹, (S : Subgroup G).inv_mem hx₃S⟩⁻¹ * ⟨C.D.F.ρ.r, hrS⟩⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    calc C.D.x₁ = C.D.x₃⁻¹ * (C.D.x₃ * C.D.x₁) := by group
      _ = C.D.x₃⁻¹ * (C.D.F.ρ.r * C.D.x₃ * C.D.F.ρ.r⁻¹) := by rw [C.D.r₃]
      _ = _ := by group
  rw [e]; exact h


include C in
theorem transfer_eq_one_of_sq {A : Type} [CommGroup A] (ϕ : (S : Subgroup G) →* A) (ε : A)
    (hε2 : ε ^ 2 = 1) (hε1 : ε ≠ 1)
    (hP : ∀ s : (S : Subgroup G), (s : G) ∈ (S : Subgroup G) ⊓ MGrp Ω W → ϕ s = 1)
    (hvals : ∀ s : (S : Subgroup G), (s : G) * s = 1 → ϕ s = 1 ∨ ϕ s = ε)
    {y : G} (hyR : y ∈ R) (hyy : y * y = z) : ϕ.transfer y = 1 := by
  have hy2 : y ^ 2 = z := by rw [pow_two]; exact hyy
  have hy4 : y ^ 4 = 1 := by
    have : y ^ 4 = y ^ 2 * y ^ 2 := by rw [← pow_add]
    rw [this, hy2, C.hzK.sq]
  have hy1 : y ≠ 1 := by
    intro h; apply C.hzK.ne_one; rw [← hyy, h, one_mul]
  have hyz : y ≠ z := by
    intro h
    have h1 : z * z = z := by
      have := hyy; rw [h] at this; exact this
    apply C.hzK.ne_one
    have h2 : z * z = z * 1 := h1.trans (mul_one z).symm
    exact mul_left_cancel h2
  have hz2 : z * z = 1 := C.hzK.sq
  refine Tr34.transfer_eq_one_of_four ϕ y ε hε2 hε1 hy4 ?_ ?_ ?_
  · intro g hg
    exact hP ⟨_, hg⟩ (C.conj_mem_P_of_R hyR hy1 hyz hg)
  · intro X
    by_cases hX : (Quotient.out X)⁻¹ * y ^ 2 * Quotient.out X ∈ (S : Subgroup G)
    · rw [Tr34.cv_of_mem ϕ hX]
      refine hvals ⟨_, hX⟩ ?_
      show (Quotient.out X)⁻¹ * y ^ 2 * Quotient.out X * ((Quotient.out X)⁻¹ * y ^ 2 * Quotient.out X) = 1
      rw [hy2]
      calc (Quotient.out X)⁻¹ * z * Quotient.out X * ((Quotient.out X)⁻¹ * z * Quotient.out X)
          = (Quotient.out X)⁻¹ * (z * z) * Quotient.out X := by group
        _ = 1 := by rw [hz2]; group
    · exact Or.inl (Tr34.cv_of_not_mem ϕ hX)
  · rw [hy2]
    refine Tr34.four_dvd_card_zEps (S : Subgroup G) S.isPGroup' ϕ z C.D.x₁ ε hε1 ?_
      (C.hd.hR.2.2 C.x₁_mem_R) (C.x₁_mem_of_index_le_two) ?_
    · intro s hs
      exact Subgroup.mem_centralizer_singleton_iff.mp (C.le_centralizer_z hs)
    · intro g hg hgz hϕ
      have hx1 : C.D.x₁ ≠ 1 := by
        intro h; apply C.hzK.ne_one; rw [← C.x₁_sq, h, one_pow]
      have hx1sq : C.D.x₁ * C.D.x₁ = z := by rw [← pow_two]; exact C.x₁_sq
      have hx1z : C.D.x₁ ≠ z := by
        intro h
        apply C.hzK.ne_one
        have h1 : z * z = z * 1 := by
          calc z * z = C.D.x₁ * C.D.x₁ := by rw [h]
            _ = z := hx1sq
            _ = z * 1 := (mul_one z).symm
        exact mul_left_cancel h1
      have hgP := C.conj_mem_P_of_R C.x₁_mem_R hx1 hx1z hg
      have hsq : g⁻¹ * z * g = (g⁻¹ * C.D.x₁ * g) ^ 2 := by
        calc g⁻¹ * z * g = g⁻¹ * (C.D.x₁ * C.D.x₁) * g := by rw [hx1sq]
          _ = (g⁻¹ * C.D.x₁ * g) ^ 2 := by rw [pow_two]; group
      have hgzP : g⁻¹ * z * g ∈ (S : Subgroup G) ⊓ MGrp Ω W := by
        rw [hsq]; exact ((S : Subgroup G) ⊓ MGrp Ω W).pow_mem hgP 2
      have := hP ⟨g⁻¹ * z * g, hgz⟩ hgzP
      exact hε1 (hϕ.symm.trans this)


include C in
theorem transfer_kills_R {A : Type} [CommGroup A] (ϕ : (S : Subgroup G) →* A) (ε : A)
    (hε2 : ε ^ 2 = 1) (hε1 : ε ≠ 1)
    (hP : ∀ s : (S : Subgroup G), (s : G) ∈ (S : Subgroup G) ⊓ MGrp Ω W → ϕ s = 1)
    (hvals : ∀ s : (S : Subgroup G), (s : G) * s = 1 → ϕ s = 1 ∨ ϕ s = ε) :
    ∀ y ∈ R, ϕ.transfer y = 1 := by
  have hRD : R ∈ DSet Ω W := C.hR ▸ C.D.F.ρ.hR
  have hcl : R = Subgroup.closure {C.D.x₁, C.D.F.ρ.r} :=
    Thompson.eq_closure_pair C.hs.stand.hyp C.hd.hW hRD (u := C.D.x₁) (r := C.D.F.ρ.r)
      (by rw [C.D.h₁, C.hR]) C.r_mem_R C.D.F.ρ.hrW
  intro y hy
  rw [hcl] at hy
  have hle : Subgroup.closure ({C.D.x₁, C.D.F.ρ.r} : Set G) ≤ ϕ.transfer.ker := by
    rw [Subgroup.closure_le]
    intro v hv
    rcases hv with rfl | rfl
    · exact C.transfer_eq_one_of_sq ϕ ε hε2 hε1 hP hvals C.x₁_mem_R
        (by rw [← pow_two]; exact C.x₁_sq)
    · exact C.transfer_eq_one_of_sq ϕ ε hε2 hε1 hP hvals C.r_mem_R C.r_mul_self
  exact hle hy

end Ctx8F
end S24B

section Ker

open CFSG.RankThree.PartTwo.Sec8

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}

theorem false_of_transfer_ker (hs : AscStand Ω K) {J R : Subgroup G} (hJ : J ∈ Ω)
    (hR : IsSylow2In R J) (P : Sylow 2 G) {N : Subgroup G}
    (habel : ∀ y ∈ (P : Subgroup G), ∀ z ∈ (P : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ N)
    {x : G} (hx : x ∈ (P : Subgroup G)) (hxN : x ∉ N) (hxp : x ^ 2 = 1)
    (hfus : ∀ g : G,
      (∀ y ∈ (P : Subgroup G) ⊓ Subgroup.centralizer {x}, g⁻¹ * y * g ∈ (P : Subgroup G)) →
        x⁻¹ * (g⁻¹ * x * g) ∈ N)
    (hVR : ∀ (A : Type) [CommGroup A] (ϕ : (P : Subgroup G) →* A),
      (∀ s : (P : Subgroup G), ϕ s = 1 ↔ (s : G) ∈ N) → ∀ y ∈ R, ϕ.transfer y = 1) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup (P : Subgroup G) := N.subgroupOf P with hU
  have hUn : U.Normal := ⟨fun u hu y => by
    rw [hU, Subgroup.mem_subgroupOf] at hu ⊢
    have h := N.mul_mem (habel y y.2 u u.2) hu
    rwa [inv_mul_cancel_right] at h⟩
  have hcomm : ∀ a b : (P : Subgroup G) ⧸ U, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H y =>
    induction b using QuotientGroup.induction_on with
    | H z =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have := habel (z : G)⁻¹ (Subgroup.inv_mem _ z.2) (y : G)⁻¹ (Subgroup.inv_mem _ y.2)
    simpa [mul_assoc] using this
  let : CommGroup ((P : Subgroup G) ⧸ U) :=
    { QuotientGroup.Quotient.group U with mul_comm := hcomm }
  let ϕ : (P : Subgroup G) →* (P : Subgroup G) ⧸ U := QuotientGroup.mk' U
  have hT : ϕ.transfer x = ϕ ⟨x, hx⟩ ^ (P : Subgroup G).index := by
    refine transfer_eq_pow_index_of_extremal P ϕ hx hxp fun t hD ht => ?_
    change (QuotientGroup.mk' U _ : _) = QuotientGroup.mk' U _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hfus t hD)
  have hne : ϕ ⟨x, hx⟩ ≠ 1 := fun h =>
    hxN (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have hpow : ϕ ⟨x, hx⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : (P : Subgroup G)) ^ 2 = 1 := Subtype.ext (by simp [hxp])
    rw [this, map_one]
  have hVR' : ∀ y ∈ R, ϕ.transfer y = 1 := by
    refine hVR _ ϕ (fun s => ?_)
    change (QuotientGroup.mk' U s) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hU, Subgroup.mem_subgroupOf]
  have hV1 : ϕ.transfer = 1 := T7C.hom_eq_one_of_sylow hs hJ hR ϕ.transfer hVR'
  have h1 : ϕ.transfer x = 1 := by rw [hV1]; rfl
  rw [hT] at h1
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_eq_prime hpow hne] at hdvd
  exact P.not_dvd_index hdvd

end Ker

end Asc77

end CFSG.ClassicalInvolution.Q8P
