module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4U3Elt
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Gen
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocL3U3
public import CFSG.ClassicalInvolution.Q3.TL4E3C269GU
public import CFSG.ClassicalInvolution.Q3.TL4MF163LU

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.U3
open CFSG.ClassicalInvolution.Q3.TA3.Q5U3 (neg_one_mem_GU2 slCentScalar_GU2 nonempty_slPart_equiv)
open CFSG.ClassicalInvolution.Q3.TL4.E3C269G (diagOneNeg coe_diagOneNeg diagOneNeg_mem_GU2)
open CFSG.GH74.GLS.IVK.Proofs2 (GU2Stated)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix
open scoped MatrixGroups commutatorElement

theorem cyclic_sq_eq_one_or_eq {G : Type} [Group G] [Finite G] [IsCyclic G] {u v : G}
    (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (hv1 : v ≠ 1) : u = 1 ∨ u = v := by
  classical
  haveI := Fintype.ofFinite G
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.mp hcon
  have hle : (Finset.univ.filter fun a : G => a ^ 2 = 1).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  have h3 : 2 < (Finset.univ.filter fun a : G => a ^ 2 = 1).card := by
    rw [Finset.two_lt_card]
    exact ⟨1, by simp, v, by simp [hv], u, by simp [hu], fun h => hv1 h.symm,
      fun h => h1 h.symm, fun h => h2 h.symm⟩
  exact (not_le.mpr h3) hle

theorem u3_exists_comm_conj {r : ℕ} (hr : 4 ≤ r) {A : Type} [Group A] [Finite A]
    (T : Subgroup A) [T.Normal] (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set A) = ⊥)
    (hU3 : CFSG.ClassicalInvolution.Q3.TA3.SmallU3Ne3 ↥T)
    {R : Subgroup A} {S : Sylow 2 R} {z : A} (hd : TightDatum R S z) (hc : TightClsR r A R S z)
    {x b : A} (hxS : x ∈ (S : Subgroup R).map R.subtype) (hbS : b ∈ (S : Subgroup R).map R.subtype)
    (hxo : orderOf x = 2 ^ (r - 1)) (hbx : b * x * b⁻¹ = x⁻¹) (hbb : b * b = x ^ 2 ^ (r - 2))
    (hxz : x ^ 2 ^ (r - 2) = z) :
    ∃ g : A, g * z * g⁻¹ ≠ z ∧ x * (g * z * g⁻¹) = (g * z * g⁻¹) * x := by
  classical
  have hU3' := hU3
  obtain ⟨p, f, hp, hp2, hf, hq3, hm⟩ := hU3
  have hOut : CFSG.ClassicalInvolution.Nobq.OutTwoCyclic ↥T :=
    CFSG.ClassicalInvolution.Q3.TA3.outTwoCyclic_PSU hm
      ((by decide : Odd 3).of_dvd_nat (Nat.gcd_dvd_left 3 _))
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI := h.finite
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : CharP K p := h.charP
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq5 : 5 ≤ p ^ f := by
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have hodd' := Nat.odd_iff.mp hodd
    omega
  have h2K : (2 : K) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at h0'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h0')
  obtain ⟨hzT, -⟩ := z_mem_of_comm2 hr hC (socleOutAbelian_u3 hU3').comm2 hd hc
  have hz2 : z * z = 1 := by rw [← pow_two, ← hd.order, pow_orderOf_eq_one]
  obtain ⟨F⟩ := exists_u3Frame h hp2 e hzT hd.order
  have hF₀card := LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  have hF₀ : Odd (Nat.card (LieType.Steinberg.fixedSubfield K p f)) := by
    rw [hF₀card]; exact hodd
  have h4 : 4 ≤ Nat.card (LieType.Steinberg.fixedSubfield K p f) := by
    rw [hF₀card]; omega
  obtain ⟨eJ⟩ := nonempty_slPart_equiv h
  have hsc : ScalarsInCore F R := fun r' hr'R hr'T =>
    CFSG.ClassicalInvolution.Q3.TL4.MF163.exists_scalar_of_mem hd F.hrange F.hk
      (slCentScalar_GU2 h) hF₀ h4 eJ hr'R hr'T
  have hxS' : x ∈ sylowSet S := hxS
  have hbS' : b ∈ sylowSet S := hbS
  have hP : IsPGroup 2 (sylowSet S) := S.isPGroup'.map _
  have hxR : x ∈ R := mem_sylowSet_le S hxS'
  have hbR : b ∈ R := mem_sylowSet_le S hbS'
  have hx2T : x ^ 2 ∈ T := by
    have hle := (socleOutAbelian_u3 hU3').comm2 A T ‹T.Normal› ⟨MulEquiv.refl _⟩ hC (sylowSet S) hP
    have hcm : ⁅x, b⁆ ∈ T := hle (Subgroup.commutator_mem_commutator hxS' hbS')
    have hbx' : b * x⁻¹ * b⁻¹ = x := by
      calc b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
        _ = x := by rw [hbx, inv_inv]
    have hcm' : ⁅x, b⁆ = x ^ 2 := by
      rw [commutatorElement_def, show x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) by group, hbx', sq]
    rw [← hcm']
    exact hcm
  have hord_dvd : ∀ n : ℕ, x ^ n = 1 → 2 ^ (r - 1) ∣ n := fun n hn => by
    rw [← hxo]; exact orderOf_dvd_of_pow_eq_one hn
  have h8 : 8 ∣ 2 ^ (r - 1) := by
    have e8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [e8]; exact pow_dvd_pow 2 (by omega)
  have hasq : x ^ 2 * x ^ 2 ≠ 1 := by
    intro h1
    have h4x : x ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]; exact h1
    have := h8.trans (hord_dvd 4 h4x)
    norm_num at this
  have hba : b * x ^ 2 * b⁻¹ = (x ^ 2)⁻¹ := by
    rw [← conj_pow, hbx, inv_pow]
  obtain ⟨Al₂, hπAl₂, c₂, hc₂⟩ := hsc (x ^ 2) (R.pow_mem hxR 2) hx2T
  have hbT : b ∉ T := b_not_mem F hsc hc₂ hπAl₂ hbR hba hasq
  haveI hcycP : IsCyclic ↥((sylowSet S).map (QuotientGroup.mk' T)) :=
    CFSG.ClassicalInvolution.Nobq.isCyclic_of_outTwoCyclic T hC hOut _
      (hP.map (QuotientGroup.mk' T))
  have hu2 : (⟨QuotientGroup.mk' T x, Subgroup.mem_map_of_mem _ hxS'⟩ :
      ↥((sylowSet S).map (QuotientGroup.mk' T))) ^ 2 = 1 := by
    apply Subtype.ext
    show QuotientGroup.mk' T x ^ 2 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (x ^ 2)).mpr hx2T
  have hb2T : b ^ 2 ∈ T := by
    rw [sq, hbb, hxz]; exact hzT
  have hv2 : (⟨QuotientGroup.mk' T b, Subgroup.mem_map_of_mem _ hbS'⟩ :
      ↥((sylowSet S).map (QuotientGroup.mk' T))) ^ 2 = 1 := by
    apply Subtype.ext
    show QuotientGroup.mk' T b ^ 2 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (b ^ 2)).mpr hb2T
  have hv1 : (⟨QuotientGroup.mk' T b, Subgroup.mem_map_of_mem _ hbS'⟩ :
      ↥((sylowSet S).map (QuotientGroup.mk' T))) ≠ 1 := by
    intro h1
    apply hbT
    exact (QuotientGroup.eq_one_iff b).mp (congrArg Subtype.val h1)
  have hxT : x ∈ T := by
    rcases cyclic_sq_eq_one_or_eq hu2 hv2 hv1 with h1 | h1
    · exact (QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val h1)
    · exfalso
      have h2 : QuotientGroup.mk' T x = QuotientGroup.mk' T b := congrArg Subtype.val h1
      have hxb1 : QuotientGroup.mk' T (x * b) = 1 := by
        rw [map_mul, h2, ← map_mul, hbb, hxz]
        exact (QuotientGroup.eq_one_iff z).mpr hzT
      have hxbT : x * b ∈ T := (QuotientGroup.eq_one_iff (x * b)).mp hxb1
      have hxbR : x * b ∈ R := R.mul_mem hxR hbR
      have hba' : (x * b) * x ^ 2 * (x * b)⁻¹ = (x ^ 2)⁻¹ := by
        calc (x * b) * x ^ 2 * (x * b)⁻¹ = x * (b * x ^ 2 * b⁻¹) * x⁻¹ := by group
          _ = x * (x ^ 2)⁻¹ * x⁻¹ := by rw [hba]
          _ = (x ^ 2)⁻¹ := by group
      exact not_mem_of_inv F hsc hc₂ hπAl₂ hxbR hxbT hba' hasq
  obtain ⟨Ax, hπAx, cx, hcx⟩ := hsc x hxR hxT
  obtain ⟨Dg, hDg⟩ : ∃ Dg : ↥(GU2Stated (p ^ f) K), (Dg : GL (Fin 2) K) = diagOneNeg K :=
    ⟨⟨diagOneNeg K, diagOneNeg_mem_GU2 h⟩, rfl⟩
  have hyT : F.π Dg ∈ T := F.π_mem Dg
  have hDD : diagOneNeg K * diagOneNeg K = 1 := Units.ext (by
    rw [Units.val_mul, coe_diagOneNeg, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
  have hD2 : Dg * Dg = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, hDg, Subgroup.coe_one]
    exact hDD)
  have hy2 : F.π Dg ^ 2 = 1 := by rw [← map_pow, sq, hD2, map_one]
  have hnsc : ∀ ω : Kˣ, diagOneNeg K ≠ GeneralLinearGroup.scalar (Fin 2) ω := by
    intro ω hω
    have h00 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 0 0) hω
    have h11 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 1 1) hω
    simp [coe_diagOneNeg, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00 h11
    exact h2K (by linear_combination h00 - h11)
  have hneg : ∀ ω : Kˣ, diagOneNeg K * (-1 : GL (Fin 2) K) ≠
      GeneralLinearGroup.scalar (Fin 2) ω := by
    intro ω hω
    have h00 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 0 0) hω
    have h11 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 1 1) hω
    simp [coe_diagOneNeg, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00 h11
    exact h2K (by linear_combination h11 - h00)
  have hy1 : F.π Dg ≠ 1 := by
    intro h1
    obtain ⟨ω, -, hω⟩ := F.hk Dg h1
    rw [hDg] at hω
    exact hnsc ω hω
  have hyz : F.π Dg ≠ z := by
    intro hyz
    have h1 : F.π (Dg * ⟨-1, neg_one_mem_GU2 h⟩) = 1 := by
      rw [map_mul, hyz, F.hπ1, hz2]
    obtain ⟨ω, -, hω⟩ := F.hk _ h1
    rw [Subgroup.coe_mul, hDg] at hω
    exact hneg ω hω
  have hxy : x * F.π Dg = F.π Dg * x := by
    rw [← hπAx, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcx]
    exact CFSG.ClassicalInvolution.Q3.TA3.Q5GL2.scalar_mul_comm cx _
  obtain ⟨g, hg⟩ := socleInvConj_u3 hU3' ⟨z, hzT⟩ ⟨F.π Dg, hyT⟩
    (by rw [Subgroup.orderOf_mk]; exact hd.order)
    (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime hy2 hy1)
  have hgA : (g : A) * z * (g : A)⁻¹ = F.π Dg := by
    have := congrArg Subtype.val hg
    simpa using this
  exact ⟨(g : A), by rw [hgA]; exact hyz, by rw [hgA]; exact hxy⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
