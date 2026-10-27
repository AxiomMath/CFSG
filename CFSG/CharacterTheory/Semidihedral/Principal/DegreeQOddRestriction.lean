module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualSimpleLayerRegularBasis
public import CFSG.CharacterTheory.Semidihedral.Principal.ProjectivePointSylowAction
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerRotationCongruencesSupport
public import CFSG.GroupTheory.LocalCores.Components

public section

open scoped BigOperators Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOuterQuotient CFSG.Semidihedral.SemilinearOddExtensions
  CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Wreathed CFSG.Open

theorem conjNormal_smul_eq_iff_map_conj_eq {Γ : Type*} [Group Γ] (L : Subgroup Γ) [L.Normal]
    {p : ℕ} (γ : Γ) (P : Sylow p L) :
    MulAut.conjNormal (H := L) γ • P = P ↔
      ((P : Subgroup L).map L.subtype).map (MulAut.conj γ).toMonoidHom =
        (P : Subgroup L).map L.subtype := by
  have hcomm : ((P : Subgroup L).map L.subtype).map (MulAut.conj γ).toMonoidHom =
      ((MulAut.conjNormal (H := L) γ • P : Sylow p L) : Subgroup L).map L.subtype := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨MulAut.conjNormal (H := L) γ y, ?_, ?_⟩
      · rw [Sylow.pointwise_smul_def]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ hy
      · rw [MulAut.conjNormal_apply]
    · rintro ⟨z, hz, rfl⟩
      rw [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hz
      refine ⟨_, ⟨_, hz, rfl⟩, ?_⟩
      rw [MulAut.smul_def, ← map_inv, MulAut.conjNormal_apply]
      group
  rw [hcomm]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Sylow.ext (Subgroup.map_injective L.subtype_injective h)

theorem local_degree_q_principal_odd_restriction_rigidity {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis (C t)) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (α : basis.index)
    (hαB : α ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hαdeg : Module.finrank ℂ (basis.representation α).vector = p ^ f)
    (hαker : MonoidHom.ker (basis.representation α).representation = NZ t) :
    ∀ y : C t, Odd (orderOf y) →
      (basis.representation α).character y =
        (Nat.card {P : Sylow p (CFSG.generalizedFitting (Gamma t)) //
          ((P : Subgroup (CFSG.generalizedFitting (Gamma t))).map
              (CFSG.generalizedFitting (Gamma t)).subtype).map
            (MulAut.conj (kappa t y)).toMonoidHom =
          (P : Subgroup (CFSG.generalizedFitting (Gamma t))).map
            (CFSG.generalizedFitting (Gamma t)).subtype} : ℂ) - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hF, hFfin, ρ, hcard, hρinj, hρL, -, hrest⟩ :=
    actual_simple_layer_centralizer_principal_regular_basis n hn S0 f0 hG t ht hnonab hcentral
      hnc p f hp hpodd hf hmodel ideal basis principal hprincipal
  obtain ⟨-, hcoef, -, -, -, -⟩ := hrest
  obtain ⟨a, b, hab, hb0, hab0, -⟩ := hcoef α hαB
  set L := CFSG.generalizedFitting (Gamma t) with hLdef
  have : L.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := Gamma t)).2
  have hq3 : 3 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      obtain ⟨k, hk⟩ := hpodd
      omega
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have hfix1 : Nat.card {x : Omega F // ((ρ (kappa t 1) : coordinateE F) :
      Equiv.Perm (Omega F)) x = x} = p ^ f + 1 := by
    rw [map_one, map_one]
    simp only [OneMemClass.coe_one, Equiv.Perm.one_apply]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun x => trivial), Finite.card_option, hcard]
  have h1 := hab 1 (by rw [orderOf_one]; exact odd_one)
  beta_reduce at h1
  rw [(basis_character_one basis α).1, hαdeg, hfix1] at h1
  have h1' : ((p ^ f : ℕ) : ℤ) = a + b * (p ^ f : ℕ) := by
    have : ((p ^ f : ℕ) : ℂ) = ((a + b * (p ^ f : ℕ) : ℤ) : ℂ) := by
      rw [h1]
      push_cast
      ring
    exact_mod_cast this
  have hq3' : (3 : ℤ) ≤ ((p ^ f : ℕ) : ℤ) := by exact_mod_cast hq3
  have hb1 : b ≤ 1 := by
    by_contra hb
    push Not at hb
    nlinarith
  have hbne : b ≠ 0 := by
    intro hb
    rw [hb, zero_mul, add_zero] at h1'
    obtain ⟨r, hr, hr2, hrL⟩ : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card L := by
      by_contra! hall
      have hLpos : Nat.card L ≠ 0 := Nat.card_pos.ne'
      have hL2 : IsPGroup 2 L := IsPGroup.of_card
        (Nat.eq_prime_pow_of_unique_prime_dvd hLpos fun {d} hd hdd => by
          by_contra hne
          exact hall d hd hne hdd)
      have : Nontrivial L := by
        obtain ⟨x, y, hxy⟩ := hnonab
        refine ⟨⟨x, y, fun h => hxy (by rw [h])⟩⟩
      have hZ := hL2.center_nontrivial
      have hZtop : Subgroup.center L = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
        · exfalso
          obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center L)
          apply hz
          exact Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp h (z : L) z.2)
        · exact h
      obtain ⟨x, y, hxy⟩ := hnonab
      apply hxy
      have hx : x ∈ Subgroup.center L := hZtop ▸ Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp hx y).symm
    have : Fact r.Prime := ⟨hr⟩
    have : Fintype L := Fintype.ofFinite L
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := L) r
      (by rwa [← Nat.card_eq_fintype_card])
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (NZ t) (x : Gamma t)
    set k := 2 ^ (orderOf c).factorization 2 with hk
    have hkdvd : k ∣ orderOf c := Nat.ordProj_dvd _ _
    have hk0 : k ≠ 0 := pow_ne_zero _ two_ne_zero
    have hyodd : Odd (orderOf (c ^ k)) := by
      rw [orderOf_pow_of_dvd hk0 hkdvd]
      exact Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (orderOf_pos c).ne')
    have hκy : kappa t (c ^ k) ≠ 1 := by
      intro h
      rw [map_pow] at h
      change (QuotientGroup.mk' (NZ t) c) ^ k = 1 at h
      rw [hc] at h
      have h' : (x ^ k : L) = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h)
      have hdvd := orderOf_dvd_of_pow_eq_one h'
      rw [hx, hk] at hdvd
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))
    apply character_ne_one_of_not_mem_ker (basis.representation α) (g := c ^ k)
    · rw [hαker]
      intro hmem
      apply hκy
      change QuotientGroup.mk' (NZ t) (c ^ k) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hmem
    · rw [hab _ hyodd, hb, Int.cast_zero, zero_mul, add_zero, (basis_character_one basis α).1,
        hαdeg]
      have : (a : ℂ) = ((p ^ f : ℕ) : ℂ) := by exact_mod_cast h1'.symm
      rw [this]
  have hb : b = 1 := by omega
  have ha : a = 0 := by
    rw [hb, one_mul] at h1'
    omega
  let ψ : Gamma t →* Equiv.Perm (Omega F) := (coordinateE F).subtype.comp ρ
  have hinj : Function.Injective (ψ.comp L.subtype) :=
    ((coordinateE F).subtype_injective.comp hρinj).comp L.subtype_injective
  have hrange : L.map ψ = coordinateG F := by
    have hGE : coordinateG F ≤ coordinateE F := (coordinateG_le_D F).trans (coordinateD_le_E F)
    change L.map ((coordinateE F).subtype.comp ρ) = coordinateG F
    rw [← Subgroup.map_map, hρL, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hGE]
  have : Fintype F := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hcard])
  obtain ⟨-, hcount, -⟩ := projective_point_action_is_intrinsic_sylow_action.{0, 0, 0} p F L ψ
    hinj hrange
  intro y hy
  rw [hab y hy, ha, hb]
  have hc := hcount (kappa t y)
  have hc' : Nat.card {ω : Omega F // ψ (kappa t y) ω = ω} =
      Nat.card {P : Sylow p L // MulAut.conjNormal (H := L) (kappa t y) • P = P} := by
    have := hc
    omega
  have hc'' : Nat.card {P : Sylow p L // MulAut.conjNormal (H := L) (kappa t y) • P = P} =
      Nat.card {P : Sylow p L // ((P : Subgroup L).map L.subtype).map
        (MulAut.conj (kappa t y)).toMonoidHom = (P : Subgroup L).map L.subtype} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun P =>
      conjNormal_smul_eq_iff_map_conj_eq L (kappa t y) P)
  push_cast
  rw [one_mul, zero_add]
  change (Nat.card {ω : Omega F // ψ (kappa t y) ω = ω} : ℂ) - 1 = _
  rw [hc', hc'']


end CFSG.Semidihedral.Principal
