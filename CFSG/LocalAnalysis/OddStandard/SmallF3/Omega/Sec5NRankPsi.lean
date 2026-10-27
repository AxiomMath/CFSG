module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CentDPull
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5NRankCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5nr_detPhi_nrK : detPhi nrK = 1 := by
  rw [detPhi_apply]
  show leftMulHom sl2f3NegOne * rightMulHom sl2f3NegOne = 1
  rw [leftMulHom_eq_piOrth coe_sl2f3NegOne, rightMulHom_sl2f3NegOne, piOrth_mul_self]

theorem sec5nr_ker_detPhi {p : SL2F3 × SL2F3} (h : detPhi p = 1) : p = 1 ∨ p = nrK := by
  obtain ⟨A, B⟩ := p
  have hX : ∀ X : Mat2, (A : Mat2) * X * ((B⁻¹ : SL2F3) : Mat2) = X := by
    intro X
    have h1 := congrArg (fun g : OGroup detForm => (g : Mat2 ≃ₗ[ZMod 3] Mat2) X) h
    simpa [detPhi_apply, leftMulHom_apply, rightMulHom_apply, Matrix.mul_assoc] using h1
  obtain ⟨hAB, hs⟩ := sl2f3_pair_kernel A B hX
  rcases hs with h1 | h1
  · left
    have hA : A = 1 := Subtype.ext h1
    rw [← hAB, hA]
    rfl
  · right
    have hA : A = sl2f3NegOne := Subtype.ext h1
    rw [← hAB, hA]
    rfl

section TwoCore

variable {G : Type} [Group G] {Ψ : SL2F3 × SL2F3 →* G}

theorem NrKer.twoCoreIn_range (h : NrKer Ψ) : twoCoreIn Ψ.range = nrQ Ψ := by
  refine le_antisymm (fun x hx => ?_) (le_twoCoreIn_of_normal nrQ_le_range ?_ ?_)
  · obtain ⟨m, hm⟩ := isPGroup_twoCoreIn Ψ.range ⟨x, hx⟩
    refine h.mem_nrQ_of_two_pow (twoCoreIn_le_self _ hx) (m := m) ?_
    simpa using congrArg Subtype.val hm
  · intro g
    refine ⟨2, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact nrQ_pow_four g.2
  · rw [Subgroup.normal_subgroupOf_iff nrQ_le_range]
    intro y x hy hx
    exact nrQ_conj_mem hx hy

end TwoCore

variable {G : Type} [Group G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

variable {φ : ↥L →* omegaGroup hQ} {z : G} {hz : z ∈ L}

@[expose] noncomputable def sec5nrOm (D : Om6Par Q (sec5cdPhi φ ⟨z, hz⟩)) :
    SL2F3 × SL2F3 →* omegaGroup hQ :=
  (D.theta.comp detPhi).codRestrict (omegaGroup hQ) fun p =>
    D.theta_mem_omega (a := detPhi p) (by rw [← range_detPhi]; exact ⟨p, rfl⟩)

@[expose] noncomputable def sec5nrPsi (hbij : Function.Bijective φ)
    (D : Om6Par Q (sec5cdPhi φ ⟨z, hz⟩)) : SL2F3 × SL2F3 →* G :=
  L.subtype.comp ((MulEquiv.ofBijective φ hbij).symm.toMonoidHom.comp (sec5nrOm D))

theorem sec5nrPsi_eq_iff (hbij : Function.Bijective φ)
    (D : Om6Par Q (sec5cdPhi φ ⟨z, hz⟩)) (p : SL2F3 × SL2F3) (l : ↥L) :
    sec5nrPsi hbij D p = (l : G) ↔ D.theta (detPhi p) = sec5cdPhi φ l := by
  have h1 : sec5nrPsi hbij D p =
      (((MulEquiv.ofBijective φ hbij).symm (sec5nrOm D p) : ↥L) : G) := rfl
  rw [h1, Subtype.coe_inj, MulEquiv.symm_apply_eq]
  constructor
  · intro h2
    exact congrArg Subtype.val h2
  · intro h2
    exact Subtype.ext h2

theorem sec5nrPsi_ker (hbij : Function.Bijective φ)
    (D : Om6Par Q (sec5cdPhi φ ⟨z, hz⟩)) : NrKer (sec5nrPsi hbij D) := by
  have key : ∀ q : SL2F3 × SL2F3, sec5nrPsi hbij D q = 1 ↔ detPhi q = 1 := by
    intro q
    have h1 := sec5nrPsi_eq_iff hbij D q 1
    rw [Subgroup.coe_one, map_one] at h1
    rw [h1]
    constructor
    · intro h
      exact D.theta_injective (h.trans (map_one _).symm)
    · intro h
      rw [h, map_one]
  intro p
  rw [key]
  constructor
  · exact sec5nr_ker_detPhi
  · rintro (rfl | rfl)
    · exact map_one _
    · exact sec5nr_detPhi_nrK

theorem sec5nrPsi_range (hbij : Function.Bijective φ)
    (D : Om6Par Q (sec5cdPhi φ ⟨z, hz⟩)) :
    (sec5nrPsi hbij D).range = sec5cdPull φ (D.L ⊔ D.R) := by
  ext x
  rw [MonoidHom.mem_range, mem_sec5cdPull_iff]
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨(MulEquiv.ofBijective φ hbij).symm (sec5nrOm D p), rfl, ?_⟩
    have h2 : D.theta (detPhi p) =
        sec5cdPhi φ ((MulEquiv.ofBijective φ hbij).symm (sec5nrOm D p)) :=
      (sec5nrPsi_eq_iff hbij D p _).mp rfl
    rw [← h2, ← D.map_omega]
    exact Subgroup.mem_map.mpr ⟨detPhi p, by rw [← range_detPhi]; exact ⟨p, rfl⟩, rfl⟩
  · rintro ⟨l, rfl, hl⟩
    rw [← D.map_omega] at hl
    obtain ⟨ω, hω, hωl⟩ := Subgroup.mem_map.mp hl
    rw [← range_detPhi] at hω
    obtain ⟨p, rfl⟩ := hω
    exact ⟨p, (sec5nrPsi_eq_iff hbij D p l).mpr hωl⟩

theorem sec5nr_exists_psi [Finite G] (hS : Asc82SchurU43) (hL : IsOm6Z2 L)
    (hodd : oddCoreIn L = ⊥) (hz2 : orderOf z = 2) {K₁ : Subgroup G}
    (hK₁ : Sl23PocketIn L z K₁) :
    ∃ Ψ : SL2F3 × SL2F3 →* G, NrKer Ψ ∧
      Ψ.range = twoRes (L ⊓ centralizer ({z} : Set G)) := by
  obtain ⟨V, _, _, _, Q, hQ, φ, hφ⟩ := t5_exists_cover hS hL
  have hdim := hφ.finrank_eq
  have hsgn := hφ.quadSign_eq
  have hker : CFSG.oddCore ↥L = ⊥ := by
    have h : (CFSG.oddCore ↥L).map L.subtype = ⊥ := hodd
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.oddCore ↥L) L.subtype_injective).mp h
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφ.ker_eq, hker]
  have hsurj : Function.Surjective φ := hφ.surjective
  have hbij : Function.Bijective φ := ⟨hinj, hsurj⟩
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (hK₁.2.1 hK₁.1)).1
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2]; exact pow_orderOf_eq_one z
  let zL : ↥L := ⟨z, hzL⟩
  have hφzz : φ zL * φ zL = 1 := by
    rw [← map_mul, show zL * zL = 1 from Subtype.ext hzz, map_one]
  have hφz1 : φ zL ≠ 1 := by
    intro h
    have h1 : zL = 1 := hinj (h.trans (map_one φ).symm)
    have h2 : z = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at hz2
    omega
  have hI4 : IsI4PlusIn (⊤ : Subgroup ↥(omegaGroup hQ)) (φ zL) :=
    (t5_isI4PlusIn_iff hL hφ hzL hz2).mp ⟨hz2, K₁, hK₁⟩
  have hztt : ((φ zL : omegaGroup hQ) : OGroup Q) * ((φ zL : omegaGroup hQ) : OGroup Q) = 1 :=
    congrArg Subtype.val hφzz
  have hzt4 : invType ((φ zL : omegaGroup hQ) : OGroup Q) = (4, 1) :=
    (t5_isI4PlusIn_omega_iff hdim hsgn hztt hφz1).mp hI4
  let D : Om6Par Q (sec5cdPhi φ zL) := Om6Par.mk' hQ hdim hsgn hztt hzt4
  exact ⟨sec5nrPsi hbij D, sec5nrPsi_ker hbij D,
    (sec5nrPsi_range hbij D).trans (sec5cdPull_sup_eq_twoRes hinj hsurj hzL D)⟩

end CFSG.OddStandard.SmallF3.Omega
