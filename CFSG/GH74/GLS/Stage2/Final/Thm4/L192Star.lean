module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.L192Rep
public import CFSG.GH74.GLS.Stage2.Final.Thm4.L192Kinds
public import CFSG.GH74.GLS.Bg.Rank

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open CFSG.GH74.GLS.Stage1.Thm6.Prod (exists_lift_pElement)
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.L192

theorem exists_orderOf_eq_two_pow {X : Type*} [Group X] {x : X} {i : ℕ} (h : x ^ (2 ^ i) = 1) :
    ∃ j : ℕ, orderOf x = 2 ^ j := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  exact ⟨j, hj⟩

theorem oPrimePResidual_le_oResidual (X : Type*) [Group X] (p : ℕ) :
    oPrimePResidual p X ≤ oResidual p X := by
  unfold oPrimePResidual
  rw [Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).2 ?_
  intro y hy
  apply Subgroup.subset_closure
  have h : orderOf ((oPrimeResidual p X).subtype y) = orderOf y := Subgroup.orderOf_coe y
  show Nat.Coprime (orderOf ((oPrimeResidual p X).subtype y)) p
  rw [h]
  exact hy

section Star

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_oResidual_of_mem_LC (z : G) {c : ↥(Cen z)} (hc : (c : G) ∈ LC z) :
    c ∈ oResidual 2 ↥(Cen z) := by
  have h : c ∈ (LC z).subgroupOf (Cen z) := hc
  rw [LC_subgroupOf] at h
  exact oPrimePResidual_le_oResidual _ 2 h.1

theorem hdet_of_rep (z : G) {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) {n : ℕ} (hn : n ≤ 2)
    (ρ : ↥(Cen z) →* GL (Fin n) (ZMod r)) : HDet z ((ρ.ker).map (toBar z)) := by
  intro c hc ⟨a, ha⟩ hc2 g
  obtain ⟨c₀, rfl⟩ := toBar_surjective z c
  obtain ⟨x, i, hxi, hxc⟩ := exists_lift_pElement (toBar z) Nat.prime_two c₀ (j := a)
    (by rw [← ha]; exact pow_orderOf_eq_one _)
  rw [← hxc] at hc hc2 ⊢
  have hxord : ∃ j : ℕ, orderOf x = 2 ^ j := exists_orderOf_eq_two_pow hxi
  have hxL : (x : G) ∈ LC z := by
    refine mem_LC_of_toBar_mem z x.2 ?_ hc
    obtain ⟨j, hj⟩ := hxord
    exact ⟨j, by rw [Subgroup.orderOf_coe]; exact hj⟩
  have hxres : x ∈ oResidual 2 ↥(Cen z) := mem_oResidual_of_mem_LC z hxL
  have hdet : Matrix.GeneralLinearGroup.det (ρ x) = 1 :=
    hom_eq_one_of_mem_oResidual ((Matrix.GeneralLinearGroup.det).comp ρ) hxres hxi
  have hx2ord : ∃ j : ℕ, orderOf (x ^ 2) = 2 ^ j :=
    exists_orderOf_eq_two_pow (i := i) (by rw [← pow_mul, mul_comm, pow_mul, hxi, one_pow])
  have hx2 : x ^ 2 ∈ ρ.ker := by
    refine mem_of_twoElt_of_map_mem (toBar z) ρ.ker hx2ord (odd_card_ker_toBar z) ?_
    rw [map_pow]
    exact hc2
  have hsq : ρ x * ρ x = 1 := by
    have : ρ (x ^ 2) = 1 := hx2
    rwa [map_pow, pow_two] at this
  obtain ⟨g₀, rfl⟩ := toBar_surjective z g
  have hcomm : ρ x * ρ g₀ = ρ g₀ * ρ x := GL_central_of_sq_det hr2 hn _ _ hsq hdet
  refine ⟨⁅x, g₀⁆, ?_, map_commutatorElement _ _ _⟩
  show ⁅x, g₀⁆ ∈ ρ.ker
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm


theorem star {z : G} {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S) {r : ℕ} [hr : Fact r.Prime]
    (hr2 : r ≠ 2) (hrk : CFSG.pRank r ↥(Op r (Cen z)) ≤ 2) {c : G} (hc : c ∈ Cen z)
    (hc2 : ∃ a : ℕ, orderOf c = 2 ^ a) (hcL : toBar z ⟨c, hc⟩ ∈ LBar z) :
    ∀ y ∈ Op r (Cen z), c * y = y * c := by
  have hQ : IsPGroup r ↥(pCore r ↥(Cen z)) := pCore_isPGroup
  have hrk' : CFSG.Open.pRank r (⊤ : Subgroup ↥(pCore r ↥(Cen z))) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    have e := (pCore r ↥(Cen z)).equivMapOfInjective (Cen z).subtype (Cen z).subtype_injective
    rw [CFSG.GH74.GLS.Bg.pRank_mulEquiv hr.out.one_lt e]
    exact hrk
  obtain ⟨n, ρ, hn, hρ1, hρ2⟩ :=
    exists_rep hr2 hQ hrk' (MulAut.conjNormal : ↥(Cen z) →* MulAut ↥(pCore r ↥(Cen z)))
  have hz : ρ ⟨z, mem_Cen_self z⟩ = 1 := by
    apply hρ1
    ext q
    simp only [MulAut.one_apply]
    have h1 : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) * (q : ↥(Cen z)) =
        (q : ↥(Cen z)) * ⟨z, mem_Cen_self z⟩ := by
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.mp (q : ↥(Cen z)).2
      exact this.symm
    have h2 : ((MulAut.conjNormal (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) q : ↥(pCore r ↥(Cen z))) :
        ↥(Cen z)) = (q : ↥(Cen z)) := by
      rw [MulAut.conjNormal_apply, h1]
      simp
    exact congrArg Subtype.val h2
  have : ((ρ.ker).map (toBar z)).Normal :=
    Subgroup.Normal.map inferInstance (toBar z) (toBar_surjective z)
  obtain ⟨a, ha⟩ := hc2
  have hxord : ∃ a : ℕ, orderOf (⟨c, hc⟩ : ↥(Cen z)) = 2 ^ a := ⟨a, by rw [Subgroup.orderOf_mk]; exact ha⟩
  have hbord : ∃ b : ℕ, orderOf (toBar z ⟨c, hc⟩) = 2 ^ b := by
    have hxo : orderOf (⟨c, hc⟩ : ↥(Cen z)) = 2 ^ a := by rw [Subgroup.orderOf_mk]; exact ha
    have hd : orderOf (toBar z ⟨c, hc⟩) ∣ 2 ^ a := hxo ▸ orderOf_map_dvd (toBar z) ⟨c, hc⟩
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact ⟨b, hb⟩
  have hmem := twoElt_mem_of_hdet ctx ((ρ.ker).map (toBar z)) ⟨⟨z, mem_Cen_self z⟩, hz, rfl⟩
    (hdet_of_rep z hr2 hn ρ) (toBar z ⟨c, hc⟩) hcL hbord
  have hker : (⟨c, hc⟩ : ↥(Cen z)) ∈ ρ.ker :=
    mem_of_twoElt_of_map_mem (toBar z) ρ.ker hxord (odd_card_ker_toBar z) hmem
  have hcop : Nat.Coprime (orderOf (⟨c, hc⟩ : ↥(Cen z))) r := by
    rw [Subgroup.orderOf_mk, ha]
    exact Nat.Coprime.pow_left a ((Nat.coprime_primes Nat.prime_two hr.out).mpr (Ne.symm hr2))
  have hα := hρ2 ⟨c, hc⟩ hcop hker
  rintro _ ⟨q, hq, rfl⟩
  have := congrArg (fun φ : MulAut ↥(pCore r ↥(Cen z)) => ((φ ⟨q, hq⟩ : ↥(pCore r ↥(Cen z))) : ↥(Cen z))) hα
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
  have h2 := congrArg Subtype.val this
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  have h3 : c * (q : G) * c⁻¹ = (q : G) := h2
  calc c * (q : G) = (c * (q : G) * c⁻¹) * c := by group
    _ = (q : G) * c := by rw [h3]

end Star

end CFSG.GH74.GLS.Stage2.Final.Thm4.L192
