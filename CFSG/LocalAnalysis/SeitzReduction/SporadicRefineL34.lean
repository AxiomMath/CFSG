module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatStatement

public section

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

theorem fixedSubgroup_conj_eq_centralizerOf {S : Type*} [Group S] (t : S) :
    fixedSubgroup (MulAut.conj t) = centralizer ({t} : Set S) := by
  ext x
  rw [mem_centralizer_singleton_iff]
  change t * x * t⁻¹ = x ↔ x * t = t * x
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem card_quotient_center_dvd_card_fixedSubgroup {S : Type} [Group S] {σ : MulAut S}
    (D : Subgroup (fixedSubgroup σ)) : Nat.card (D ⧸ center D) ∣ Nat.card (fixedSubgroup σ) :=
  (card_quotient_dvd_card _).trans (card_subgroup_dvd_card D)

theorem nonempty_quotient_center_map_equiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    (D : Subgroup X) :
    Nonempty (D ⧸ center D ≃* (D.map φ.toMonoidHom) ⧸ center (D.map φ.toMonoidHom)) :=
  ⟨QuotientGroup.congr _ _ (D.equivMapOfInjective φ.toMonoidHom φ.injective)
    (Subgroup.map_center_eq _)⟩

theorem lieModel_map_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    {D : Subgroup X} {t : StatedLieTag} {n p f : ℕ} (h : LieModel (D ⧸ center D) t n p f) :
    LieModel ((D.map φ.toMonoidHom) ⧸ center (D.map φ.toMonoidHom)) t n p f := by
  obtain ⟨ψ⟩ := nonempty_quotient_center_map_equiv φ D
  exact LieType.CurtisTits.lieModel_of_mulEquiv ψ h

theorem not_fixedCentralizerTwoSmall_of_normal {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) {N : Subgroup (fixedSubgroup σ)}
    (hN : N.Normal) (hp : IsPGroup 2 N) (h2 : 2 < Nat.card N) :
    ¬ FixedCentralizerTwoSmall σ D := by
  intro hsmall
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : Group.IsSolvable N := by
    have : Group.IsNilpotent N := hp.isNilpotent
    infer_instance
  have hDN := (LocalCores.component_solvable_centralizer hs hN.isSubnormal).1 D hD
  have hle := hsmall (N.map (fixedSubgroup σ).subtype) (hp.map _) ?_ ?_
  · rw [card_map_of_injective (fixedSubgroup σ).subtype_injective] at hle
    omega
  · rintro _ ⟨n, hn, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have hc := commutator_eq_bot_iff_le_centralizer.mp hDN hd
    rw [mem_centralizer_iff] at hc
    have h1 := congrArg Subtype.val (hc n hn)
    simp only [coe_mul] at h1
    simp only [coe_subtype]
    exact h1.symm
  · rintro _ ⟨n, -, rfl⟩
    exact n.2

theorem not_fixedCentralizerTwoSmall_of_mulEquiv_ker {S : Type} [Group S] [Finite S]
    {σ : MulAut S} {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) {H Q : Type*} [Group H]
    [Group Q] (φ : fixedSubgroup σ ≃* H) (ρ : H →* Q) (hker : Nat.card ρ.ker = 4) :
    ¬ FixedCentralizerTwoSmall σ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card (ρ.ker.map φ.symm.toMonoidHom) = 4 := by
    rw [card_map_of_injective φ.symm.injective, hker]
  exact not_fixedCentralizerTwoSmall_of_normal hD
    ((MonoidHom.normal_ker ρ).map _ φ.symm.surjective)
    (IsPGroup.of_card (n := 2) (by rw [hc]; norm_num)) (by rw [hc]; norm_num)

theorem not_lieModel_psl_three_two_of_orderOf_six {X : Type}
    [Group X] {x : X} (hx : orderOf x = 6) : ¬ LieModel X .PSL 3 2 2 := by
  intro h
  obtain ⟨-, hcent, -⟩ := ComponentClassification.PSL3Four.excludes_alternating_models_stated.{0} X
    (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl h)
  have ht : orderOf (x ^ 3) = 2 := by
    rw [orderOf_pow' x (by norm_num), hx]
    decide
  have hmem : x ∈ centralizer ({x ^ 3} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    exact ((Commute.refl x).pow_right 3).eq
  have hdvd : orderOf (⟨x, hmem⟩ : centralizer ({x ^ 3} : Set X)) ∣
      Nat.card (centralizer ({x ^ 3} : Set X)) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hx, hcent _ ht] at hdvd
  norm_num at hdvd

theorem card_centralizer_dvd_of_lieModel_psl_three_two {X : Type}
    [Group X] (h : LieModel X .PSL 3 2 2) {x : X} (hx : x ≠ 1)
    (h2 : 2 ∣ Nat.card (centralizer ({x} : Set X))) :
    Nat.card (centralizer ({x} : Set X)) ∣ 64 := by
  obtain ⟨hcard, hcent, -⟩ :=
    ComponentClassification.PSL3Four.excludes_alternating_models_stated.{0} X
      (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl h)
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({x} : Set X)) 2 h2
  have ht' : orderOf (t : X) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have hxt : x ∈ centralizer ({(t : X)} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.1 t.2).symm
  have hox : orderOf x ∣ 2 ^ 6 := by
    have := orderOf_dvd_natCard (⟨x, hxt⟩ : centralizer ({(t : X)} : Set X))
    rw [Subgroup.orderOf_mk, hcent _ ht'] at this
    simpa using this
  obtain ⟨k, -, hkx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hox
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [pow_zero, orderOf_eq_one_iff] at hkx
      exact absurd hkx hx
    · exact hpos
  have hy2 : orderOf (x ^ (2 ^ (k - 1))) = 2 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      (hkx ▸ pow_dvd_pow 2 (Nat.sub_le k 1)), hkx, Nat.pow_div (Nat.sub_le k 1) two_pos,
      show k - (k - 1) = 1 by omega, pow_one]
  have hle : centralizer ({x} : Set X) ≤ centralizer ({x ^ (2 ^ (k - 1))} : Set X) := by
    intro g hg
    rw [mem_centralizer_singleton_iff] at hg ⊢
    exact (Commute.pow_right hg _).eq
  rw [← hcent _ hy2]
  exact card_dvd_of_le hle

theorem card_centralizer_mul_card_conjClass {X : Type*} [Group X] [Finite X] (x : X) :
    Nat.card (centralizer ({x} : Set X)) * Nat.card (ConjClasses.mk x).carrier = Nat.card X := by
  have h1 : (MulAction.stabilizer (ConjAct X) x).index = Nat.card (ConjClasses.mk x).carrier := by
    rw [MulAction.index_stabilizer, ConjAct.orbit_eq_carrier_conjClasses, Nat.card_coe_set_eq]
  have h2 := (MulAction.stabilizer (ConjAct X) x).card_mul_index
  rw [← Subgroup.nat_card_centralizer_nat_card_stabilizer, h1] at h2
  rw [h2]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

theorem not_lieModel_psl_three_two_of_conjClass {X : Type}
    [Group X] [Finite X] (c : ConjClasses X) {m : ℕ} (hc1 : Nat.card c.carrier ≠ 1)
    (hm : m * Nat.card c.carrier = Nat.card X) (hm2 : 2 ∣ m) (hm64 : ¬ m ∣ 64) :
    ¬ LieModel X .PSL 3 2 2 := by
  intro h
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  have hpos : 0 < Nat.card (ConjClasses.mk x).carrier := by
    have : Nonempty (ConjClasses.mk x).carrier := ⟨⟨x, ConjClasses.mem_carrier_mk⟩⟩
    exact Nat.card_pos
  have hcm : Nat.card (centralizer ({x} : Set X)) = m := by
    have := card_centralizer_mul_card_conjClass x
    rw [← hm] at this
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hx : x ≠ 1 := by
    rintro rfl
    apply hc1
    have h1 : (ConjClasses.mk (1 : X)).carrier = {1} := by
      ext y
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left,
        Set.mem_singleton_iff]
    rw [h1, Nat.card_unique]
  exact hm64 (hcm ▸ card_centralizer_dvd_of_lieModel_psl_three_two h hx (hcm ▸ hm2))

theorem not_lieModel_psl_three_two_of_mulEquiv_orderOf_six
    {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {y : Y} (hy : orderOf y = 6) :
    ¬ LieModel X .PSL 3 2 2 := fun h =>
  not_lieModel_psl_three_two_of_orderOf_six hy (LieType.CurtisTits.lieModel_of_mulEquiv e h)

end CFSG.SeitzReduction.SporadicRefine
