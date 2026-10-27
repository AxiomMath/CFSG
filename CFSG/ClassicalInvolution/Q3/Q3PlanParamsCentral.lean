module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsLift

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

section Odd

theorem odd_natCard_subgroup_of_forall_odd_orderOf {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (h : ∀ x ∈ H, Odd (orderOf x)) : Odd (Nat.card H) := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hne))
  have h1 := h x x.2
  rw [Subgroup.orderOf_coe, hx] at h1
  exact absurd h1 (by decide)

theorem odd_orderOf_of_mem_oddCore_fin {M : Type*} [Group M] [Finite M] {x : M}
    (hx : x ∈ classicalInvolutionOddCore M) : Odd (orderOf x) := by
  have h1 := Subgroup.orderOf_dvd_natCard (classicalInvolutionOddCore M) hx
  exact Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card M) h1

end Odd

section Central

variable {X Y : Type} [Group X] [Group Y] (φ : X →* Y)

theorem conj_mem_centralizer_of_commutator_mem_center {z g c : X}
    (hg : g * z * g⁻¹ * z⁻¹ ∈ Subgroup.center X) (hc : c ∈ Subgroup.centralizer ({z} : Set X)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer ({z} : Set X) := by
  set κ := g * z * g⁻¹ * z⁻¹ with hκ
  have hκc : ∀ x : X, κ * x = x * κ := fun x => (Subgroup.mem_center_iff.mp hg x).symm
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hgz : g * z * g⁻¹ = κ * z := by rw [hκ]; group
  have h1 : (g * c * g⁻¹) * (g * z * g⁻¹) = (g * z * g⁻¹) * (g * c * g⁻¹) := by
    calc (g * c * g⁻¹) * (g * z * g⁻¹) = g * (c * z) * g⁻¹ := by group
      _ = g * (z * c) * g⁻¹ := by rw [hcz]
      _ = (g * z * g⁻¹) * (g * c * g⁻¹) := by group
  rw [hgz] at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h2 : κ * ((g * c * g⁻¹) * z) = κ * (z * (g * c * g⁻¹)) := by
    calc κ * ((g * c * g⁻¹) * z) = (g * c * g⁻¹) * (κ * z) := by
          rw [← mul_assoc, hκc (g * c * g⁻¹), mul_assoc]
      _ = (κ * z) * (g * c * g⁻¹) := h1
      _ = κ * (z * (g * c * g⁻¹)) := by rw [mul_assoc]
  exact mul_left_cancel h2

section Map

variable [Finite X] (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center X)
include hφ hker

theorem IsClassicalMember3.map_central {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z)
    (hz : φ z ≠ 1) : IsClassicalMember3 (L.map φ) (φ z) where
  orderOf_eq_two := by
    refine orderOf_eq_prime ?_ hz
    rw [← map_pow, ← h.orderOf_eq_two, pow_orderOf_eq_one, map_one]
  mem := Subgroup.mem_map_of_mem φ h.mem
  subnormal := by
    have hC : (Subgroup.centralizer ({z} : Set X)).map φ ≤
        Subgroup.centralizer ({φ z} : Set Y) := by
      rintro _ ⟨c, hc, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp hc]
    have hN : (((Subgroup.centralizer ({z} : Set X)).map φ).subgroupOf
        (Subgroup.centralizer ({φ z} : Set Y))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hC]
      rintro _ k ⟨c, hc, rfl⟩ hk
      obtain ⟨g, rfl⟩ := hφ k
      refine ⟨g * c * g⁻¹, conj_mem_centralizer_of_commutator_mem_center ?_ hc, by simp⟩
      apply hker
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [Subgroup.mem_centralizer_singleton_iff.mp hk]
      group
    exact isSubnormal_trans (CFSG.ClassicalInvolution.ModelFacts.isSubnormal_map φ h.subnormal)
      (isSubnormal_of_normal_subgroupOf hC hN)
  nonempty_equiv := by
    obtain ⟨e⟩ := h.nonempty_equiv
    have hodd3 : Odd (Nat.card (ZMod 3)) := odd_natCard_zmod_three
    set O := classicalInvolutionOddCore L with hO
    have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card L
    set f : L →* L.map φ := φ.subgroupMap L with hf
    have hfsurj : Function.Surjective f := MonoidHom.subgroupMap_surjective φ L
    have hfapp : ∀ l : L, ((f l : L.map φ) : Y) = φ l := fun l => rfl
    have hzz : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rwa [h.orderOf_eq_two, pow_two] at this
    set z' : L := ⟨z, h.mem⟩ with hz'
    have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact h.orderOf_eq_two
    have hz'sq : z' * z' = 1 := Subtype.ext hzz
    have hρz : QuotientGroup.mk' O z' = e.symm (-1) :=
      (orderOf_eq_two_iff_of_equiv_sl2 hodd3 e (QuotientGroup.mk' O z')).mp
        (CFSG.ClassicalInvolution.Generic.orderOf_mk_oddCore_eq_two hz'2)
    have hker_le : f.ker ≤ O := by
      intro l hl
      have hφl : φ (l : X) = 1 := show φ (l : X) = 1 from congrArg Subtype.val
        (MonoidHom.mem_ker.mp hl)
      have hlc : ∀ x : L, x * l = l * x := fun x =>
        Subtype.ext (Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hφl)) (x : X))
      have hρc : QuotientGroup.mk' O l ∈ Subgroup.center (L ⧸ O) := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O q
        rw [← map_mul, ← map_mul, hlc x]
      have hρc' := (mem_center_iff_of_equiv_sl2 e _).mp hρc
      rcases (mem_center_sl2_iff _).mp hρc' with h1 | h1
      · exact (QuotientGroup.eq_one_iff l).mp ((MulEquiv.map_eq_one_iff e).mp h1)
      · exfalso
        have hρl : QuotientGroup.mk' O l = QuotientGroup.mk' O z' := by
          rw [hρz]
          exact e.eq_symm_apply.mpr h1
        obtain ⟨o, ho⟩ : ∃ o : L, o = z'⁻¹ * l := ⟨_, rfl⟩
        have hmem : o ∈ O := by
          rw [← QuotientGroup.eq_one_iff]
          show QuotientGroup.mk' O o = 1
          rw [ho, map_mul, map_inv, ← hρl, inv_mul_cancel]
        obtain ⟨k, hk⟩ := odd_orderOf_of_mem_oddCore₃ hmem
        have hl : l = z' * o := by rw [ho]; group
        have hcomm : Commute z' o := by
          rw [ho]
          exact (Commute.refl z').inv_right.mul_right (show Commute z' l from hlc z')
        have hpow : l ^ orderOf o = z' := by
          rw [hl, hcomm.mul_pow, pow_orderOf_eq_one, mul_one, hk, pow_succ, pow_mul, pow_two,
            hz'sq, one_pow, one_mul]
        apply hz
        have := congrArg (fun t : L => φ (t : X)) hpow
        simp only [Subgroup.coe_pow, map_pow, hφl, one_pow] at this
        exact this.symm
    have : Finite ↥(L.map φ) := Finite.of_surjective f hfsurj
    have hOM : classicalInvolutionOddCore (L.map φ) = O.map f := by
      refine le_antisymm ?_ ?_
      · intro y hy
        obtain ⟨u, rfl⟩ := hfsurj y
        refine Subgroup.mem_map_of_mem f ?_
        have hnorm : ((classicalInvolutionOddCore (L.map φ)).comap f).Normal :=
          Subgroup.Normal.comap inferInstance f
        refine CFSG.ComponentClassification.OddCore.maximal L
          ((classicalInvolutionOddCore (L.map φ)).comap f) hnorm ?_ hy
        refine odd_natCard_subgroup_of_forall_odd_orderOf _ fun v hv => ?_
        have hm : Odd (orderOf (f v)) := odd_orderOf_of_mem_oddCore_fin hv
        have hvm : v ^ orderOf (f v) ∈ f.ker := by
          rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
        have hodd' : Odd (orderOf (v ^ orderOf (f v))) := odd_orderOf_of_mem_oddCore₃ (hker_le hvm)
        have hdvd : orderOf v ∣ orderOf (f v) * orderOf (v ^ orderOf (f v)) := by
          apply orderOf_dvd_of_pow_eq_one
          rw [pow_mul, pow_orderOf_eq_one]
        exact Odd.of_dvd_nat (hm.mul hodd') hdvd
      · exact CFSG.ComponentClassification.OddCore.maximal (L.map φ) (O.map f)
          (Subgroup.Normal.map inferInstance f hfsurj)
          (Odd.of_dvd_nat hOodd (Subgroup.card_map_dvd O f))
    set g : L →* (L.map φ) ⧸ classicalInvolutionOddCore (L.map φ) :=
      (QuotientGroup.mk' _).comp f with hg
    have hgsurj : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hfsurj
    have hgker : g.ker = O := by
      ext x
      rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, hOM]
      constructor
      · rintro ⟨o, ho, hox⟩
        have hk : o⁻¹ * x ∈ f.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hox, inv_mul_cancel]
        have := O.mul_mem ho (hker_le hk)
        rwa [mul_inv_cancel_left] at this
      · intro hx
        exact ⟨x, hx, rfl⟩
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hgker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective g hgsurj)).symm.trans e⟩

end Map

end Central

end CFSG.ClassicalInvolution.Q3
