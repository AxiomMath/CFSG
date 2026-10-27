module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutNormQuotA
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutXbar
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutRest4
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutX1Basic

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Fin76b
  CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G} {F L1 N A : Subgroup G}

namespace OutSetup

variable (S : OutSetup L z F L1 N)

include S

theorem inf_centralizer_eq (hAH : A ≤ centralizer ({z} : Set G))
    (hAz : A ⊔ zpowers z = centralizer ({z} : Set G)) :
    normalizer (L1 : Set G) ⊓ centralizer ({z} : Set G) =
      zpowers z ⊔ (normalizer (F : Set G) ⊓ A) := by
  have hzc : zpowers z ≤ centralizer (A : Set G) :=
    zpowers_le.2 (mem_centralizer_iff.2 fun a ha => mem_centralizer_singleton_iff.1 (hAH ha))
  rw [S.one.normalizer_inf_centralizer_z_eq S.L1_normE S.L1_cz S.F_le]
  apply le_antisymm
  · intro g hg
    obtain ⟨hgE, hgC⟩ := Subgroup.mem_inf.1 hg
    have hgA : g ∈ A ⊔ zpowers z := by rw [hAz]; exact hgC
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hzc hgA
    have hF1 := S.one.normalizes_F (Subgroup.mem_normalizer_iff.1 hgE)
    have haF' : ∀ x ∈ F, a * x * a⁻¹ ∈ F := by
      intro x hx
      have hx' := (hF1 x).1 hx
      rcases S.one.mem_zpowers_cases hb with hb1 | hbz
      · simpa [hb1] using hx'
      · rw [hbz] at hx'
        have e : a * z * x * (a * z)⁻¹ = a * x * a⁻¹ := by
          calc a * z * x * (a * z)⁻¹ = a * (z * x) * z⁻¹ * a⁻¹ := by group
            _ = a * (x * z) * z⁻¹ * a⁻¹ := by rw [S.one.z_comm x (S.one.F_le hx)]
            _ = a * x * a⁻¹ := by group
        rwa [e] at hx'
    have ha' : a ∈ normalizer (F : Set G) ⊓ A :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_normalizer_iff.2 (forall_mem_iff_of_forall_mem haF'), ha⟩
    have : a * b ∈ (normalizer (F : Set G) ⊓ A) ⊔ zpowers z := Subgroup.mul_mem_sup ha' hb
    rwa [sup_comm] at this
  · refine sup_le ?_ ?_
    · exact zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)), mem_centralizer_singleton_iff.2 rfl⟩)
    · intro d hd
      obtain ⟨hdF, hdA⟩ := Subgroup.mem_inf.1 hd
      have hdz : d * z * d⁻¹ = z * 1 := by
        rw [mem_centralizer_singleton_iff.1 (hAH hdA)]
        group
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_normalizer_iff.2
        (S.one.mem_normalizer_sup (Subgroup.mem_normalizer_iff.1 hdF) (Subgroup.one_mem F) hdz),
        hAH hdA⟩

theorem centralizer_zbar_equiv (hLA : L ≤ A) (hAH : A ≤ centralizer ({z} : Set G)) (hzA : z ∉ A)
    (hAz : A ⊔ zpowers z = centralizer ({z} : Set G))
    (hq : NormQuot (Equiv.Perm (Fin 6)) (normalizer (F : Set G) ⊓ A) F) :
    Nonempty (centralizer ({(QuotientGroup.mk S.zX : Xbar L1)} : Set (Xbar L1)) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) := by
  classical
  set D : Subgroup G := normalizer (F : Set G) ⊓ A with hD
  obtain ⟨ψ₀, hψ₀, hker₀⟩ := hq
  have hDA : D ≤ A := inf_le_right
  have hz2 : z * z = 1 := S.one.z_mul_self
  have hE := S.inf_centralizer_eq hAH hAz
  have hQX : zpowers z ⊔ D ≤ normalizer (L1 : Set G) := by
    rw [← hE]
    exact inf_le_left
  have hDc : D ≤ centralizer (zpowers z : Set G) := by
    intro d hd
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    exact (Commute.zpow_left (show Commute z d from
      (mem_centralizer_singleton_iff.1 (hAH (hDA hd))).symm) k).eq
  have hdisj : Disjoint (zpowers z) D := by
    rw [Subgroup.disjoint_def]
    intro x hxz hxD
    rcases S.one.mem_zpowers_cases hxz with hx1 | hxz'
    · exact hx1
    · exact absurd (hxz' ▸ hDA hxD) hzA
  let e := internalProdEquiv hDc hdisj
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) S.one.z_ne_one
  have hcard2 : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hzo]
  have : IsCyclic (zpowers z) := isCyclic_of_prime_card hcard2
  have hcardM : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    simp
  have : IsCyclic (Multiplicative (ZMod 2)) := isCyclic_of_prime_card hcardM
  let e₁ : zpowers z ≃* Multiplicative (ZMod 2) :=
    mulEquivOfCyclicCardEq (by rw [hcard2, hcardM])
  let θ : ↥(zpowers z ⊔ D) →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6) :=
    (e₁.toMonoidHom.prodMap ψ₀).comp e.symm.toMonoidHom
  have hθsurj : Function.Surjective θ :=
    (e₁.surjective.prodMap hψ₀).comp e.symm.surjective
  have hθker : θ.ker = F.subgroupOf (zpowers z ⊔ D) := by
    ext q
    obtain ⟨⟨c, d⟩, rfl⟩ := e.surjective q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (e₁ (e.symm (e (c, d))).1, ψ₀ (e.symm (e (c, d))).2) = 1 ↔ _
    rw [MulEquiv.symm_apply_apply, Prod.mk_eq_one, map_eq_one_iff _ e₁.injective]
    show c = 1 ∧ ψ₀ d = 1 ↔ (c : G) * d ∈ F
    constructor
    · rintro ⟨hc, hd⟩
      have hd' : (d : G) ∈ F := by
        have : d ∈ ψ₀.ker := hd
        rw [hker₀] at this
        exact this
      rw [hc]
      simpa using hd'
    · intro h
      have hcA : (c : G) ∈ A := by
        have : (c : G) = (c * d) * (d : G)⁻¹ := by group
        rw [this]
        exact A.mul_mem (hLA (S.one.F_le h)) (A.inv_mem (hDA d.2))
      have hc1 : (c : G) = 1 := by
        rcases S.one.mem_zpowers_cases c.2 with hc1 | hcz
        · exact hc1
        · exact absurd (hcz ▸ hcA) hzA
      have hc : c = 1 := Subtype.ext hc1
      refine ⟨hc, ?_⟩
      have hdF : (d : G) ∈ F := by
        rw [hc1, one_mul] at h
        exact h
      have : d ∈ ψ₀.ker := by
        rw [hker₀]
        exact hdF
      exact this
  let Pi : ↥(zpowers z ⊔ D) →* Xbar L1 := (QuotientGroup.mk' _).comp (Subgroup.inclusion hQX)
  have hrange : Pi.range = centralizer ({(QuotientGroup.mk S.zX : Xbar L1)} : Set (Xbar L1)) := by
    rw [S.centralizer_zbar_eq]
    ext q
    constructor
    · rintro ⟨⟨a, ha⟩, rfl⟩
      refine ⟨⟨a, hQX ha⟩, ?_, rfl⟩
      have : a ∈ normalizer (L1 : Set G) ⊓ centralizer ({z} : Set G) := hE ▸ ha
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 this).2
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, ?_⟩, rfl⟩
      rw [← hE]
      exact Subgroup.mem_inf.2 ⟨y.2, Subgroup.mem_subgroupOf.1 hy⟩
  have hker : Pi.ker = F.subgroupOf (zpowers z ⊔ D) := by
    ext ⟨q, hq⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk ⟨q, hQX hq⟩ : Xbar L1) = 1 ↔ q ∈ F
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hqC
      have h1 := S.one.centralizer_X_z_inf_C S.L1_normE S.L1_cz S.F_le S.L1_comm S.L1_card
        S.K_eq S.z_norm
      rw [← h1]
      exact Subgroup.mem_inf.2 ⟨hE ▸ hq, hqC⟩
    · intro hqF
      exact mem_centralizer_iff.2 fun x hx => S.L1_comm x hx q (S.F_le hqF)
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange Pi).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hker.trans hθker.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj)))⟩

end OutSetup

theorem fin77aOuterXbar_of_engine
    (hEng : AutSylowEngine6 (Carrier .M22)) : Fin77aOuterXbar := by
  intro G _ _ _ L z t T₁ F tb Q x L1 hS
  obtain ⟨A, hLA, hAH, hzA, hAz, -⟩ := hS.complement
  have D := hS.data
  have hq : IsSporadic (L ⧸ center L) .M22 :=
    isSporadic_quotient_of_center_eq_bot D.Zbot hS.sporadic
  have hcZ : center (L ⧸ center L) = ⊥ := center_eq_bot_of_isSporadic hq
  have hout := innAut_index_dvd_two hq
  obtain ⟨e⟩ := hq
  have hE := D.engine6 hcZ (hEng.of_mulEquiv e.symm)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact D.cfg.z_sq) D.cfg.z_ne
  have hθ := thetaH_surjective_of_rel hS.std hS.cyclic D.cfg.z_cent hz2 D.cfg.cent_le hout hS.rel
  have hNQ := D.normQuot_A hcZ hθ hLA hAH hzA hAz hE.s6
  obtain ⟨N, Sup⟩ := OutSetup.of_kStructure hS.one hS.transitive hS.K
  exact ⟨Sup.K_le_X Sup.z_mem_K, Sup.centralizer_zbar_equiv hLA hAH hzA hAz hNQ⟩

theorem fin77aOuterXbar :
    Fin77aOuterXbar :=
  fin77aOuterXbar_of_engine autSylowEngine6_m22

end CFSG.EvenSporadicStandard.M22Std
