module

public import CFSG.GF2Type.Aschbacher1976Full.HSPartECentF
public import CFSG.GF2Type.Aschbacher1976Full.HSPartEOrder

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.PartE

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {T V : Subgroup G}

theorem conj_eq_of_sq_conj_eq {u x : G} (hodd : Odd (orderOf u))
    (h : u * (u * x * u⁻¹) * u⁻¹ = x) : u * x * u⁻¹ = x := by
  have hc : Commute (u ^ 2) x := by
    have : u * u * x = x * (u * u) := by
      calc u * u * x = (u * (u * x * u⁻¹) * u⁻¹) * (u * u) := by group
        _ = x * (u * u) := by rw [h]
    rw [pow_two]
    exact this
  obtain ⟨t, ht⟩ := hodd
  have e : (u ^ 2) ^ (t + 1) = u := by
    rw [← pow_mul, show 2 * (t + 1) = orderOf u + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hc' : Commute u x := by
    rw [← e]
    exact hc.pow_left (t + 1)
  rw [hc'.eq]
  group

theorem mem_ZF_self (hset : HSSetting G z) {v : G} (hv : IsConj z v) : v ∈ ZF v := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  have hF2 : IsPGroup 2 ↥(Fz z) := hset.1.2.2.2.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hset.2
  obtain ⟨c, rfl⟩ := isConj_iff.mp hv
  have h1 : c⁻¹⁻¹ * z * c⁻¹ = c * z * c⁻¹ := by rw [inv_inv]
  show c * z * c⁻¹ ∈ CFSG.GF2Type.CenterFour.centerAt (c * z * c⁻¹)
  rw [← h1, CFSG.GF2Type.CenterFour.centerAt_conj, Width.mem_conjugate_iff,
    show c⁻¹ * (c⁻¹⁻¹ * z * c⁻¹) * c⁻¹⁻¹ = z by group]
  exact (Width.mem_centerAt_iff hD hz hF2).mpr hD.mem_z

theorem le_WT (hset : HSSetting G z) (hV : HSV z T V) : V ≤ WT T z := by
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]
    exact one_mem _
  · exact hV.ZF_le_W v hv hv1 (mem_ZF_self hset (hV.isConj v hv hv1))

theorem eq_one_of_odd_mem_centralizer (hset : HSSetting G z) (hV : HSV z T V) {u : G}
    (hu : u ∈ Subgroup.centralizer (V : Set G)) (hodd : Odd (orderOf u)) : u = 1 := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  have hF2 : IsPGroup 2 ↥(Fz z) := hset.1.2.2.2.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hset.2
  have huH : u ∈ Hz z := Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp hu) z hV.z_mem).symm
  have hfixV : ∀ v ∈ V, u * v * u⁻¹ = v := fun v hv =>
    mul_inv_eq_iff_eq_mul.mpr ((Subgroup.mem_centralizer_iff.mp hu) v hv).symm
  have hfixZ : ∀ c ∈ Z, u * c * u⁻¹ = c := fun c hc =>
    conj_eq_of_sq_conj_eq hodd (Width.sq_trivial hD hz huH c hc)
  have hZV : Z ⊔ V ≤ Subgroup.centralizer ({u} : Set G) := by
    refine sup_le (fun c hc => ?_) (fun v hv => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp (hfixZ c hc)).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp (hfixV v hv)).symm
  haveI hnorm : ((Z ⊔ V).subgroupOf (Fz z)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hzZV : z ∈ Z ⊔ V := Subgroup.mem_sup_left hD.mem_z
    have e : (((g * n * g⁻¹ : ↥(Fz z)) : G)) = ⁅(g : G), (n : G)⁆ * (n : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    refine (Z ⊔ V).mul_mem ?_ hn
    rcases Width.comm_F hD hz g.2 n.2 with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact hzZV
  refine Shape.eq_one_of_stable hF2 huH hodd (N := (Z ⊔ V).subgroupOf (Fz z)) ?_ ?_
  · intro n hn
    rw [Subgroup.mem_subgroupOf] at hn
    exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp (hZV hn)).symm
  · intro x
    have hxF : (x : G) ∈ Fz z := x.2
    have hx' : u * (x : G) * u⁻¹ ∈ Fz z := Width.Fz_conj_mem huH hxF
    refine ⟨⟨(x : G)⁻¹ * (u * (x : G) * u⁻¹), (Fz z).mul_mem ((Fz z).inv_mem hxF) hx'⟩, ?_, ?_⟩
    · have hmemC : (x : G)⁻¹ * (u * (x : G) * u⁻¹) ∈ Subgroup.centralizer (V : Set G) := by
        refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
        have hxv : (x : G) * v * (x : G)⁻¹ ∈ V :=
          hV.normal_in_T x (hV.F_le_T hxF) v hv
        have h1 : u⁻¹ * v * u = v := by
          have := hfixV v hv
          calc u⁻¹ * v * u = u⁻¹ * (u * v * u⁻¹) * u := by rw [this]
            _ = v := by group
        have h2 := hfixV _ hxv
        have e1 : u * (x : G) * u⁻¹ * v = u * (x : G) * (u⁻¹ * v * u) * u⁻¹ := by group
        rw [h1] at e1
        have e2 : u * (x : G) * v * u⁻¹ =
            (u * ((x : G) * v * (x : G)⁻¹) * u⁻¹) * (u * (x : G) * u⁻¹) := by group
        rw [h2] at e2
        have e3 : u * (x : G) * u⁻¹ * v = ((x : G) * v * (x : G)⁻¹) * (u * (x : G) * u⁻¹) :=
          e1.trans e2
        calc v * ((x : G)⁻¹ * (u * (x : G) * u⁻¹))
            = (x : G)⁻¹ * (((x : G) * v * (x : G)⁻¹) * (u * (x : G) * u⁻¹)) := by group
          _ = (x : G)⁻¹ * (u * (x : G) * u⁻¹ * v) := by rw [e3]
          _ = (x : G)⁻¹ * (u * (x : G) * u⁻¹) * v := by group
      rw [Subgroup.mem_subgroupOf, ← inf_centralizer_eq_sup hset hV hD]
      exact ⟨(Fz z).mul_mem ((Fz z).inv_mem hxF) hx', hmemC⟩
    · show u * (x : G) * u⁻¹ = (x : G) * ((x : G)⁻¹ * (u * (x : G) * u⁻¹))
      group

theorem centralizer_isPGroup (hset : HSSetting G z) (hV : HSV z T V) :
    IsPGroup 2 ↥(Subgroup.centralizer (V : Set G)) :=
  Shape.isPGroup_two_of_forall_odd fun u hodd =>
    Subtype.ext (eq_one_of_odd_mem_centralizer hset hV u.2
      (by rw [Subgroup.orderOf_coe]; exact hodd))

theorem card_centralizer_eq (hset : HSSetting G z) (hs5 : HSS5 z) (hV : HSV z T V) :
    Nat.card ↥(Subgroup.centralizer (V : Set G)) = 64 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (centralizer_isPGroup hset hV)
  have h6 := factorization_card_C hset hs5 hV
  rw [hn, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at h6
  rw [hn, h6]
  norm_num

theorem centralizer_eq_WT (hset : HSSetting G z) (hs5 : HSS5 z) (hV : HSV z T V) :
    Subgroup.centralizer (V : Set G) = WT T z := by
  have hVW := le_WT hset hV
  have hWC : WT T z ≤ Subgroup.centralizer (V : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => hV.W_comm v (hVW hv) a ha
  exact (Subgroup.eq_of_le_of_card_ge hWC
    (by rw [card_centralizer_eq hset hs5 hV, hV.card_W])).symm

end CFSG.GF2Type.Aschbacher1976Full.HS.PartE
