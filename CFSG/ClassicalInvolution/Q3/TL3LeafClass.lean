module

public import CFSG.ClassicalInvolution.Q3.TL3LeafCore
public import CFSG.ClassicalInvolution.Q3.Q3CLStd
public import CFSG.ClassicalInvolution.TwoGroupCase.Fusion
public import CFSG.ClassicalInvolution.Asc77.AscFusionR10

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

open QuaternionGroup in
theorem quaternionGroup_comm_of_comm {n : ℕ} [NeZero n] {u a b : QuaternionGroup n}
    (huu : u * u ≠ 1) (hau : a * u = u * a) (hbu : b * u = u * b) : a * b = b * a := by
  rcases u with i | i <;> rcases a with j | j <;> rcases b with k | k
  · simp only [a_mul_a]; rw [add_comm]
  · exfalso
    simp only [xa_mul_a, a_mul_xa, xa.injEq] at hbu
    apply huu
    simp only [a_mul_a, one_def, a.injEq]
    linear_combination hbu
  · exfalso
    simp only [xa_mul_a, a_mul_xa, xa.injEq] at hau
    apply huu
    simp only [a_mul_a, one_def, a.injEq]
    linear_combination hau
  · exfalso
    simp only [xa_mul_a, a_mul_xa, xa.injEq] at hau
    apply huu
    simp only [a_mul_a, one_def, a.injEq]
    linear_combination hau
  · simp only [a_mul_a]; rw [add_comm]
  · simp only [a_mul_xa, xa_mul_a, xa.injEq] at hau ⊢
    linear_combination hau
  · simp only [a_mul_xa, xa_mul_a, xa.injEq] at hbu ⊢
    linear_combination -hbu
  · simp only [xa_mul_xa, a.injEq] at hau hbu ⊢
    linear_combination hau - hbu

variable {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem core_le_normalizer_inf :
    tightCore R ≤ Subgroup.normalizer ((tightCore R ⊓ oddCoreImg R : Subgroup G) : Set G) := by
  intro x hx
  have hxR : x ∈ R := tightCore_le R hx
  have hxinvR : x⁻¹ ∈ R := R.inv_mem hxR
  refine Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn => ?_, fun hn => ?_⟩
  · exact ⟨(tightCore R).mul_mem ((tightCore R).mul_mem hx hn.1) ((tightCore R).inv_mem hx),
      conj_mem_oddCoreImg (Subgroup.le_normalizer hxR) hn.2⟩
  · have h1 := (tightCore R).mul_mem ((tightCore R).mul_mem ((tightCore R).inv_mem hx) hn.1) hx
    have h2 := conj_mem_oddCoreImg (Subgroup.le_normalizer hxinvR) hn.2
    constructor
    · simpa [mul_assoc] using h1
    · simpa [mul_assoc] using h2

theorem TightDatum.commOdd_core (h : TightDatum R S t) {u a b : G} (hu : u ∈ tightCore R)
    (hu2 : IsPGroup 2 (Subgroup.zpowers u)) (huu : u * u ≠ 1) (ha : a ∈ tightCore R)
    (hb : b ∈ tightCore R) (hau : a * u = u * a) (hbu : b * u = u * b) :
    a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf (tightCore R) := by
  classical
  obtain ⟨r, hr, ⟨eS⟩⟩ := h.quat
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hO : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S ⟨r, hr, ⟨eS⟩⟩ h.mem h.order h.cent h.normal h.twoGroup
  set S' : Subgroup G := (S : Subgroup R).map R.subtype with hS'
  let eS' : ↥S' ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans eS
  have hι := hO.bijective_restrict
  set ι : ↥S' →* R ⧸ oddCore R :=
    (QuotientGroup.mk' (oddCore R)).comp (Subgroup.inclusion hO.S_le) with hιdef
  let eQ : (R ⧸ oddCore R) ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (MulEquiv.ofBijective ι hι).symm.trans eS'
  let φ : R →* QuaternionGroup (2 ^ (r - 2)) :=
    eQ.toMonoidHom.comp (QuotientGroup.mk' (oddCore R))
  have hφ1 : ∀ x : R, φ x = 1 → (x : G) ∈ oddCoreImg R := by
    intro x hx
    have h1 : eQ (QuotientGroup.mk' (oddCore R) x) = 1 := hx
    rw [MulEquiv.map_eq_one_iff] at h1
    exact ⟨x, (QuotientGroup.eq_one_iff x).mp h1, rfl⟩
  have huR : u ∈ R := tightCore_le R hu
  have haR : a ∈ R := tightCore_le R ha
  have hbR : b ∈ R := tightCore_le R hb
  have huu' : φ ⟨u, huR⟩ * φ ⟨u, huR⟩ ≠ 1 := by
    intro h1
    rw [← map_mul] at h1
    have h3 := hφ1 _ h1
    apply huu
    have h2 : IsPGroup 2 (Subgroup.zpowers (u * u)) :=
      hu2.to_le (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _ (Subgroup.mem_zpowers u)
        (Subgroup.mem_zpowers u)))
    exact eq_one_of_isPGroup_of_mem_odd (odd_natCard_oddCoreImg R) h3 h2
  have hau' : φ ⟨a, haR⟩ * φ ⟨u, huR⟩ = φ ⟨u, huR⟩ * φ ⟨a, haR⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hau)
  have hbu' : φ ⟨b, hbR⟩ * φ ⟨u, huR⟩ = φ ⟨u, huR⟩ * φ ⟨b, hbR⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hbu)
  have hc := quaternionGroup_comm_of_comm huu' hau' hbu'
  have hc' : φ (⟨a, haR⟩ * ⟨b, hbR⟩ * (⟨a, haR⟩ : R)⁻¹ * (⟨b, hbR⟩ : R)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc]
    group
  have hcomm : a * b * a⁻¹ * b⁻¹ ∈ oddCoreImg R := by
    simpa using hφ1 _ hc'
  have hK : a * b * a⁻¹ * b⁻¹ ∈ tightCore R :=
    (tightCore R).mul_mem ((tightCore R).mul_mem ((tightCore R).mul_mem ha hb)
      ((tightCore R).inv_mem ha)) ((tightCore R).inv_mem hb)
  have hN : tightCore R ⊓ oddCoreImg R ≤ oddCoreOf (tightCore R) :=
    AscFusion.le_oddCoreOf_of_normal_odd inf_le_left core_le_normalizer_inf
      (Odd.of_dvd_nat (odd_natCard_oddCoreImg R) (Subgroup.card_dvd_of_le inf_le_right))
  exact hN ⟨hK, hcomm⟩

theorem TightDatum.isSubnormal_member (h : TightDatum R S t) (g : G) :
    IsSubnormal (conjSub g (tightCore R)) (Subgroup.centralizer ({g * t * g⁻¹} : Set G)) := by
  have huniq := h.isUniqueInvolution_core
  have hle : conjSub g (tightCore R) ≤ Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxt : (g⁻¹ * x * g) * t = t * (g⁻¹ * x * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.cent (tightCore_le R hx))
    calc x * (g * t * g⁻¹) = g * ((g⁻¹ * x * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by rw [hxt]
      _ = (g * t * g⁻¹) * x := by group
  have hn : ((conjSub g (tightCore R)).subgroupOf
      (Subgroup.centralizer ({g * t * g⁻¹} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    intro c hc
    have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      calc (g⁻¹ * c * g) * t = g⁻¹ * (c * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * c) * g := by rw [hc]
        _ = t * (g⁻¹ * c * g) := by group
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    rw [mem_conjSub_iff, mem_conjSub_iff]
    have := Subgroup.mem_normalizer_iff.mp (h.le_normalizer_core hc') (g⁻¹ * x * g)
    have e : g⁻¹ * (c * x * c⁻¹) * g = (g⁻¹ * c * g) * (g⁻¹ * x * g) * (g⁻¹ * c * g)⁻¹ := by group
    rw [e]
    exact this
  exact IsSubnormal.step hle hn (IsSubnormal.refl _)

theorem TightDatum.classicalClause (h : TightDatum R S t) :
    Q3CL.ClassicalClause (CoreAssembly.conjClass (tightCore R)) where
  subnormal := by
    rintro K ⟨g, rfl⟩
    refine ⟨g * t * g⁻¹, conj_mem_conjSub h.isUniqueInvolution_core.mem, ?_, h.isSubnormal_member g⟩
    have := (MulAut.conj g).orderOf_eq t
    rwa [MulAut.conj_apply, h.order] at this
  commOdd := by
    rintro J ⟨g, rfl⟩ u a b hu hu2 huu ha hb hau hbu
    simp only at hu ha hb ⊢
    rw [AscFusion.oddCoreOf_conjSub' g (tightCore R), mem_conjSub_iff]
    have hu' : g⁻¹ * u * g ∈ tightCore R := mem_conjSub_iff.mp hu
    have ha' : g⁻¹ * a * g ∈ tightCore R := mem_conjSub_iff.mp ha
    have hb' : g⁻¹ * b * g ∈ tightCore R := mem_conjSub_iff.mp hb
    have hu2' : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * u * g)) := by
      have e : g⁻¹ * u * g = (MulAut.conj g⁻¹).toMonoidHom u := by simp
      rw [e, ← MonoidHom.map_zpowers]
      exact hu2.map _
    have huu' : (g⁻¹ * u * g) * (g⁻¹ * u * g) ≠ 1 := by
      intro h1
      apply huu
      have : u * u = g * ((g⁻¹ * u * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
      rw [this, h1]; group
    have hau' : (g⁻¹ * a * g) * (g⁻¹ * u * g) = (g⁻¹ * u * g) * (g⁻¹ * a * g) := by
      calc (g⁻¹ * a * g) * (g⁻¹ * u * g) = g⁻¹ * (a * u) * g := by group
        _ = g⁻¹ * (u * a) * g := by rw [hau]
        _ = (g⁻¹ * u * g) * (g⁻¹ * a * g) := by group
    have hbu' : (g⁻¹ * b * g) * (g⁻¹ * u * g) = (g⁻¹ * u * g) * (g⁻¹ * b * g) := by
      calc (g⁻¹ * b * g) * (g⁻¹ * u * g) = g⁻¹ * (b * u) * g := by group
        _ = g⁻¹ * (u * b) * g := by rw [hbu]
        _ = (g⁻¹ * u * g) * (g⁻¹ * b * g) := by group
    have key := h.commOdd_core hu' hu2' huu' ha' hb' hau' hbu'
    have e : g⁻¹ * (a * b * a⁻¹ * b⁻¹) * g =
        (g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g)⁻¹ := by group
    rw [e]
    exact key

theorem TightDatum.partIHypG (h : TightDatum R S t) :
    Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore R)) :=
  ⟨h.hypOmegaGen, h.classicalClause, h.aEmpty⟩

theorem TightDatum.ascStandCore (h : TightDatum R S t) :
    Q3CL.T8R.Loc.AscStandCore (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
  ⟨h.hypOmegaGen, h.classicalClause, h.aEmpty, CoreAssembly.mem_conjClass_self _,
    fun _ ⟨g, hg⟩ => ⟨g, hg⟩⟩

end CFSG.ClassicalInvolution.Q3
