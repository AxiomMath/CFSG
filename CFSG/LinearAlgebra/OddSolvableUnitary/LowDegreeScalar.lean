module

public import CFSG.LinearAlgebra.OddSolvableUnitary.ExtraspecialModule
public import CFSG.LinearAlgebra.OddSolvableUnitary.ExtraspecialObstruction

public section

namespace CFSG.OddSolvableUnitary

open Subgroup Module
open scoped Pointwise

theorem exists_fixed_of_card_eq_four {G α : Type*} [Group G] [Finite G] [MulAction G α]
    (hodd : Odd (Nat.card G)) (s : Set α) (hs : s.ncard = 4)
    (hinv : ∀ g : G, ∀ x ∈ s, g • x ∈ s) : ∃ x ∈ s, ∀ g : G, g • x = x := by
  classical
  let _ : MulAction G s :=
    { smul := fun g x => ⟨g • (x : α), hinv g x x.2⟩
      one_smul := fun x => Subtype.ext (one_smul G (x : α))
      mul_smul := fun g h x => Subtype.ext (mul_smul g h (x : α)) }
  have hs' : Nat.card s = 4 := by rw [Nat.card_coe_set_eq, hs]
  have : Finite s := Nat.finite_of_card_ne_zero (by rw [hs']; norm_num)
  set P := (MulAction.toPermHom G s).range
  have h24 : Nat.card P ∣ 24 := by
    have h := P.card_subgroup_dvd_card
    rwa [Nat.card_perm, hs'] at h
  have hoddP : Odd (Nat.card P) := Odd.of_dvd_nat hodd (Subgroup.card_range_dvd _)
  have h3 : Nat.card P ∣ 3 := by
    have hcop : Nat.Coprime (Nat.card P) (2 ^ 3) :=
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.2 hoddP)
    exact hcop.dvd_of_dvd_mul_left (by simpa using h24)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 P := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])
  obtain ⟨x, hx⟩ := hP3.nonempty_fixed_point_of_prime_not_dvd_card s (by rw [hs']; norm_num)
  refine ⟨x, x.2, fun g => ?_⟩
  exact congrArg Subtype.val (hx ⟨MulAction.toPermHom G s g, g, rfl⟩)

theorem card_filter_mem_and_not_mem {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {K L : Subgroup G} [DecidablePred (· ∈ K)] [DecidablePred (· ∈ L)] (hKL : K ≤ L) :
    ((Finset.univ : Finset G).filter fun x => x ∈ L ∧ x ∉ K).card =
      Nat.card L - Nat.card K := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset G).filter fun x => x ∈ L) (fun x => x ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have hK : ((Finset.univ : Finset G).filter fun x => x ∈ L ∧ x ∈ K).card = Nat.card K := by
    rw [Finset.filter_congr fun x _ =>
      (show x ∈ L ∧ x ∈ K ↔ x ∈ K from ⟨fun h => h.2, fun h => ⟨hKL h, h⟩⟩),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hL : ((Finset.univ : Finset G).filter fun x => x ∈ L).card = Nat.card L := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  omega

theorem ncard_setOf_card_eq_nine {G : Type*} [Group G] [Finite G] {D Z : Subgroup G}
    (hZD : Z ≤ D) (hD : Nat.card D = 27) (hZ : Nat.card Z = 3)
    (hZc : ∀ z ∈ Z, ∀ x ∈ D, Commute z x) (hDnc : ¬IsMulCommutative D) :
    {E : Subgroup G | Z ≤ E ∧ E ≤ D ∧ Nat.card E = 9}.ncard = 4 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  set s := (Finset.univ : Finset (Subgroup G)).filter fun E => Z ≤ E ∧ E ≤ D ∧ Nat.card E = 9
  set X := (Finset.univ : Finset G).filter fun x => x ∈ D ∧ x ∉ Z
  have hX : X.card = 24 := by rw [card_filter_mem_and_not_mem hZD, hD, hZ]
  have hA : ∀ x ∈ D, x ∉ Z → Nat.card (Z ⊔ zpowers x : Subgroup G) = 9 := by
    intro x hxD hxZ
    have hle : Z ⊔ zpowers x ≤ D := sup_le hZD (zpowers_le.2 hxD)
    have hcomm : IsMulCommutative (Z ⊔ zpowers x : Subgroup G) := by
      rw [sup_eq_closure]
      refine isMulCommutative_closure fun u hu v hv _ => ?_
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact hZc u hu v (hZD hv)
      · exact hZc u hu v (zpowers_le.2 hxD hv)
      · exact (hZc v hv u (zpowers_le.2 hxD hu)).symm
      · obtain ⟨m, rfl⟩ := hu
        obtain ⟨n, rfl⟩ := hv
        exact Commute.zpow_zpow_self x m n
    obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (show Nat.card (Z ⊔ zpowers x : Subgroup G) ∣ 3 ^ 3 from
        (card_dvd_of_le hle).trans (by rw [hD]; norm_num))
    have hlt : 3 < Nat.card (Z ⊔ zpowers x : Subgroup G) := by
      have hZle : Z ≤ Z ⊔ zpowers x := le_sup_left
      have hne : Z ≠ Z ⊔ zpowers x := fun h =>
        hxZ (h ▸ (le_sup_right : zpowers x ≤ Z ⊔ zpowers x) (mem_zpowers x))
      have hle' := card_le_of_le hZle
      rw [hZ] at hle'
      rcases hle'.lt_or_eq with h | h
      · exact h
      · exact absurd (eq_of_le_of_card_ge hZle (by rw [hZ, h])) hne
    have hk3 : k ≠ 3 := by
      rintro rfl
      have heq : Z ⊔ zpowers x = D := eq_of_le_of_card_ge hle (by rw [hcard, hD]; norm_num)
      exact hDnc (heq ▸ hcomm)
    rw [hcard] at hlt ⊢
    interval_cases k
    · norm_num at hlt
    · norm_num at hlt
    · norm_num
    · exact absurd rfl hk3
  have hmaps : Set.MapsTo (fun x => Z ⊔ zpowers x) X s := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, le_sup_left, sup_le hZD (zpowers_le.2 hx.2.1),
      hA x hx.2.1 hx.2.2⟩
  have hfiber : ∀ E ∈ s, (X.filter fun x => Z ⊔ zpowers x = E).card = 6 := by
    intro E hE
    rw [Finset.mem_filter] at hE
    obtain ⟨-, hZE, hED, hE9⟩ := hE
    have : (X.filter fun x => Z ⊔ zpowers x = E) =
        (Finset.univ : Finset G).filter fun x => x ∈ E ∧ x ∉ Z := by
      ext x
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨-, hxZ⟩, hxE⟩
        exact ⟨hxE ▸ (le_sup_right : zpowers x ≤ Z ⊔ zpowers x) (mem_zpowers x), hxZ⟩
      · rintro ⟨hxE, hxZ⟩
        refine ⟨⟨hED hxE, hxZ⟩, eq_of_le_of_card_ge (sup_le hZE (zpowers_le.2 hxE)) ?_⟩
        rw [hE9, hA x (hED hxE) hxZ]
    rw [this, card_filter_mem_and_not_mem hZE, hE9, hZ]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, hX] at hsum
  omega

theorem isCyclic_and_le_center_of_scalar {G : Type*} [Group G] {F V : Type*} [Field F]
    [Finite F] [AddCommGroup V] [Module F V] [Nontrivial V] (ρ : G →* Module.End F V)
    (hρ : Function.Injective ρ) {K : Subgroup G} (hK : ∀ x ∈ K, ∃ c : F, ρ x = c • 1) :
    IsCyclic K ∧ K ≤ center G := by
  refine ⟨?_, fun x hx => mem_center_iff.2 fun g => hρ ?_⟩
  · let ψ : K →* (Module.End F V)ˣ := (ρ.toHomUnits).comp K.subtype
    let R := (Units.map (algebraMap F (Module.End F V)).toMonoidHom).range
    have hR : IsCyclic R := isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    have hψR : ∀ x : K, ψ x ∈ R := by
      intro x
      obtain ⟨c, hc⟩ := hK x x.2
      have hc0 : c ≠ 0 := by
        rintro rfl
        have h1 : ρ ((x : G) * (x : G)⁻¹) = 1 := by rw [mul_inv_cancel, map_one]
        rw [map_mul, hc, zero_smul, zero_mul] at h1
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        exact hv (by simpa using congrArg (fun f : Module.End F V => f v) h1.symm)
      refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
      change algebraMap F (Module.End F V) c = ρ x
      rw [hc, Algebra.algebraMap_eq_smul_one]
    refine isCyclic_of_injective (ψ.codRestrict R hψR) fun x y hxy => Subtype.ext (hρ ?_)
    exact congrArg (fun u : R => ((u : (Module.End F V)ˣ) : Module.End F V)) hxy
  · obtain ⟨c, hc⟩ := hK x hx
    rw [map_mul, map_mul, hc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem smul_mem_setOf_card_eq_nine {G : Type*} [Group G] {D Z : Subgroup G} [D.Normal]
    [Z.Normal] (c : ConjAct G) {E : Subgroup G} (hE : E ∈ {E : Subgroup G | Z ≤ E ∧ E ≤ D ∧
      Nat.card E = 9}) : c • E ∈ {E : Subgroup G | Z ≤ E ∧ E ≤ D ∧ Nat.card E = 9} := by
  obtain ⟨hZE, hED, hE9⟩ := hE
  have hinj : Function.Injective (MulDistribMulAction.toMonoidEnd (ConjAct G) G c) :=
    MulAction.injective c
  refine ⟨?_, ?_, ?_⟩
  · rw [← (inferInstance : Z.Normal).conjAct c, pointwise_smul_def, pointwise_smul_def]
    exact map_mono hZE
  · rw [← (inferInstance : D.Normal).conjAct c, pointwise_smul_def, pointwise_smul_def]
    exact map_mono hED
  · rw [pointwise_smul_def, card_map_of_injective hinj, hE9]

theorem isCyclic_and_scalar_of_forall_abelian_normal_scalar {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (hsolv : Group.IsSolvable G) {F V : Type*} [Field F] [Finite F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hn : finrank F V = 2 ∨ finrank F V = 3) (ρ : G →* Module.End F V)
    (hρ : Function.Injective ρ)
    (hscal : ∀ A : Subgroup G, A.Normal → IsMulCommutative A → ∀ x ∈ A, ∃ c : F, ρ x = c • 1) :
    (∀ x : G, ∃ c : F, ρ x = c • 1) ∧ IsCyclic G := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨A, hA⟩ := (Set.toFinite {B : Subgroup G | B.Normal ∧ IsMulCommutative B}).exists_maximal
    ⟨⊥, inferInstance, inferInstance⟩
  have hA' : Maximal (fun B : Subgroup G => B.Normal ∧ IsMulCommutative B) A := hA
  obtain ⟨hAcyc, hAZ⟩ := isCyclic_and_le_center_of_scalar ρ hρ (hscal A hA'.prop.1 hA'.prop.2)
  by_cases htop : A = ⊤
  · subst htop
    refine ⟨fun x => hscal ⊤ hA'.prop.1 hA'.prop.2 x (mem_top x), ?_⟩
    exact isCyclic_of_surjective Subgroup.topEquiv.toMonoidHom Subgroup.topEquiv.surjective
  exfalso
  have hcen : centralizer (A : Set G) = ⊤ :=
    eq_top_iff.2 fun g _ => mem_centralizer_iff.2 fun a ha => (mem_center_iff.1 (hAZ ha) g).symm
  have hlt : A < centralizer (A : Set G) := hcen ▸ lt_top_iff_ne_top.2 htop
  obtain ⟨r, a, D, hr, hrodd, ha, hDn, -, hDcard, hDexp, hZD, hZDr⟩ :=
    odd_solvable_cyclic_maximal_abelian_normal_extraspecial_obstruction hsolv hodd hA' hAcyc hlt
  have hr2 : r ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.2 even_two) hrodd
  have hZsc : ∀ z ∈ center D, ∃ c : F, ∀ v, (ρ.comp D.subtype) z v = c • v := by
    intro z hz
    obtain ⟨c, hc⟩ := hscal ((center D).map D.subtype) inferInstance
      ((isMulCommutative_map_subtype_iff _).2 inferInstance) _ ⟨z, hz, rfl⟩
    exact ⟨c, fun v => by rw [MonoidHom.comp_apply, show ρ (D.subtype z) = c • 1 from hc]; rfl⟩
  obtain ⟨-, hram, -⟩ := odd_extraspecial_binary_module_mixed_stabilizer_orbits hr hr2 ha hDcard
    (fun x => Subtype.ext (hDexp _ x.2)) hZD hZDr rfl rfl (ρ.comp D.subtype)
    (hρ.comp D.subtype_injective) hZsc
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hra : 3 ≤ r ^ a := hr3.trans (le_self_pow hr.one_lt.le (by omega))
  have hle := Nat.le_of_dvd (by omega) hram
  have hn3 : finrank F V = 3 := by omega
  have hra3 : r ^ a = 3 := by
    rw [hn3] at hram
    rcases (Nat.dvd_prime Nat.prime_three).1 hram with h | h <;> omega
  have ha1 : a = 1 := by
    by_contra h
    have : r ^ 2 ≤ r ^ a := Nat.pow_le_pow_right hr.pos (by omega)
    nlinarith
  subst ha1
  have hr3' : r = 3 := by simpa using hra3
  subst hr3'
  set Z := (center D).map D.subtype with hZdef
  have hZn : Z.Normal := inferInstance
  have hZDle : Z ≤ D := map_subtype_le _
  have hZ3 : Nat.card Z = 3 := by rw [card_map_of_injective D.subtype_injective, hZDr]
  have hD27 : Nat.card D = 27 := by rw [hDcard]; norm_num
  have hZc : ∀ z ∈ Z, ∀ x ∈ D, Commute z x := by
    rintro _ ⟨z, hz, rfl⟩ x hx
    exact congrArg Subtype.val (mem_center_iff.1 hz ⟨x, hx⟩).symm
  have hDnc : ¬IsMulCommutative D := by
    intro hc
    have htopD : center D = ⊤ := eq_top_iff.2 fun x _ =>
      mem_center_iff.2 fun y => hc.is_comm.comm y x
    have h := Nat.card_congr (Subgroup.topEquiv (G := D)).toEquiv
    rw [← htopD, hZDr, hD27] at h
    omega
  set s := {E : Subgroup G | Z ≤ E ∧ E ≤ D ∧ Nat.card E = 9}
  have hs := ncard_setOf_card_eq_nine hZDle hD27 hZ3 hZc hDnc
  have : Finite (ConjAct G) := Finite.of_equiv G ConjAct.toConjAct.toEquiv
  have hoddC : Odd (Nat.card (ConjAct G)) := by
    rwa [Nat.card_congr (ConjAct.toConjAct (G := G)).toEquiv.symm]
  obtain ⟨E, hEs, hEfix⟩ := exists_fixed_of_card_eq_four hoddC s hs
    fun c E hE => smul_mem_setOf_card_eq_nine c hE
  obtain ⟨-, hED, hE9⟩ := hEs
  have hEn : E.Normal := ⟨fun x hx g => by
    have h := smul_mem_pointwise_smul x (ConjAct.toConjAct g) E hx
    rwa [hEfix, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at h⟩
  have hEc : IsMulCommutative E :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hE9]; norm_num)
  obtain ⟨hEcyc, -⟩ := isCyclic_and_le_center_of_scalar ρ hρ (hscal E hEn hEc)
  have hexp : Monoid.exponent E ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hDexp _ (hED x.2))
  rw [IsCyclic.exponent_eq_card, hE9] at hexp
  norm_num at hexp

theorem odd_solvable_low_degree_scalar_normal_subgroups_force_scalars {F : Type*} [Field F]
    [Finite F] {n : ℕ} (hn : n = 2 ∨ n = 3) (H : Subgroup (GL (Fin n) F))
    (hodd : Odd (Nat.card H)) (hsolv : Group.IsSolvable H)
    (hscal : ∀ A : Subgroup H, A.Normal → IsMulCommutative A → ∀ x ∈ A,
      ∃ c : F, ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) c) :
    (∀ x ∈ H, ∃ c : F, (x : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) c) ∧
      IsCyclic H := by
  let ρ : H →* Module.End F (Fin n → F) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp ((Units.coeHom _).comp H.subtype)
  have hρ : Function.Injective ρ := fun x y h =>
    Subtype.ext (Units.ext (Matrix.toLinAlgEquiv'.injective h))
  have hiff : ∀ (x : H) (c : F), ρ x = c • 1 ↔
      ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) c := by
    intro x c
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      ← Matrix.toLinAlgEquiv'.injective.eq_iff, map_smul, map_one]
    rfl
  have hfin : finrank F (Fin n → F) = 2 ∨ finrank F (Fin n → F) = 3 := by
    rwa [Module.finrank_fin_fun]
  obtain ⟨hall, hcyc⟩ := isCyclic_and_scalar_of_forall_abelian_normal_scalar hodd hsolv hfin ρ hρ
    fun A hAn hAc x hx => by
      obtain ⟨c, hc⟩ := hscal A hAn hAc x hx
      exact ⟨c, (hiff x c).2 hc⟩
  refine ⟨fun x hx => ?_, hcyc⟩
  obtain ⟨c, hc⟩ := hall ⟨x, hx⟩
  exact ⟨c, (hiff ⟨x, hx⟩ c).1 hc⟩

end CFSG.OddSolvableUnitary
