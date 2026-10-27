module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3KCComponentFacts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open scoped commutatorElement

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

private theorem apply_comm_of_finrank_eq_add_two_aux1 (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x)
    {h : F[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) :
    2 ≤ h.natDegree := by
  have hpq' : ¬ p ∣ Nat.card F := by
    intro hd
    have h1 : p ∣ (Nat.card F + 1) - Nat.card F := Nat.dvd_sub hpq hd
    rw [Nat.add_sub_cancel_left] at h1
    exact hp.not_dvd_one h1
  have hpq1 : ¬ p ∣ Nat.card F - 1 := by
    intro hd
    have h2 : p ∣ (Nat.card F + 1) - (Nat.card F - 1) := Nat.dvd_sub hpq hd
    have h2' : p ∣ 2 := by
      have hq : 1 ≤ Nat.card F := Nat.card_pos
      have : (Nat.card F + 1) - (Nat.card F - 1) = 2 := by omega
      rwa [this] at h2
    exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) h2') hp.two_le)
  have hxp : x.toLinearMap ^ p = 1 := by
    rw [← toLinearMap_pow, hx.pow_eq_one]; rfl
  have h2 := CFSG.RankThree.PartOne.KCLinComm.two_le_orderOf_natCast hp Nat.card_pos hpq' hpq1
  have h3 := CFSG.RankThree.PartOne.KCLinComm.orderOf_le_natDegree_of_mem_primaryFactors
    (V := V) hp (x := x.toLinearMap) hxp hh (by simpa using hne)
  omega

private theorem apply_comm_of_finrank_eq_add_two_aux2 {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x)
    (hdim : finrank F V = finrank F (fixedSpace x) + 2) :
    finrank F (othersSpace x.toLinearMap (X - 1)) = 2 := by
  have h1 := Submodule.finrank_add_eq_of_isCompl hx.fixed_others.1
  omega

private theorem apply_comm_of_finrank_eq_add_two_aux3 (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {a : F[X]}
    (ha : a ∈ primaryFactors x.toLinearMap) (hne : a ≠ X - 1)
    (hle : finrank F (primaryComponent x.toLinearMap a) ≤ 2) :
    primaryMultiplicity x.toLinearMap a = 1 := by
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have hdeg := apply_comm_of_finrank_eq_add_two_aux1 hp hp2 hpq hx ha hne
  have hfin := finrank_primaryComponent (x := x.toLinearMap) (a := a)
  have hmpos : 1 ≤ primaryMultiplicity x.toLinearMap a := by
    by_contra h
    have h0 : primaryMultiplicity x.toLinearMap a = 0 := by omega
    have h1 : finrank F (primaryComponent x.toLinearMap a) = 0 := by
      rw [hfin]
      rw [show Module.finrank (AdjoinRoot a) (primaryComponent x.toLinearMap a) = 0 from h0,
        mul_zero]
    have h2 : 1 ≤ finrank F (primaryComponent x.toLinearMap a) :=
      Submodule.one_le_finrank_iff.mpr (primaryComponent_ne_bot hx.squarefree_minpoly ha)
    omega
  by_contra hne1
  have h2 : 2 ≤ primaryMultiplicity x.toLinearMap a := by omega
  have h3 : 4 ≤ a.natDegree * primaryMultiplicity x.toLinearMap a := Nat.mul_le_mul hdeg h2
  have h4 : a.natDegree * primaryMultiplicity x.toLinearMap a ≤ 2 := hfin ▸ hle
  omega

private theorem apply_comm_of_finrank_eq_add_two_aux4 (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {a : F[X]}
    (ha : a ∈ primaryFactors x.toLinearMap) (hne : a ≠ X - 1)
    (hle : finrank F (primaryComponent x.toLinearMap a) ≤ 2) {g k : V ≃ₗ[F] V}
    (hg : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[F] V)))
    (hk : k ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[F] V))) :
    ∀ m ∈ primaryComponent x.toLinearMap a, g (k m) = k (g m) := by
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have hm1 := apply_comm_of_finrank_eq_add_two_aux3 hp hp2 hpq hx ha hne hle
  let G : Module.End (AdjoinRoot a) (primaryComponent x.toLinearMap a) :=
    (centralizerGL x a ⟨g, hg⟩ : BlockGL x a)
  let K : Module.End (AdjoinRoot a) (primaryComponent x.toLinearMap a) :=
    (centralizerGL x a ⟨k, hk⟩ : BlockGL x a)
  have hGcoe : ∀ w : primaryComponent x.toLinearMap a, ((G w : V)) = g (w : V) := by
    intro w
    change (((centralizerGL x a ⟨g, hg⟩ : BlockGL x a) : Module.End (AdjoinRoot a)
      (primaryComponent x.toLinearMap a)) w : V) = g (w : V)
    rw [coe_centralizerGL]
  have hKcoe : ∀ w : primaryComponent x.toLinearMap a, ((K w : V)) = k (w : V) := by
    intro w
    change (((centralizerGL x a ⟨k, hk⟩ : BlockGL x a) : Module.End (AdjoinRoot a)
      (primaryComponent x.toLinearMap a)) w : V) = k (w : V)
    rw [coe_centralizerGL]
  intro m hm
  obtain ⟨cg, hcg, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hm1 G
  obtain ⟨ck, hck, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hm1 K
  have hmul : G * K = K * G := by
    rw [hcg, hck]
    ext u
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    rw [mul_comm cg ck]
  have happ := congrArg (fun f : Module.End (AdjoinRoot a)
    (primaryComponent x.toLinearMap a) => f ⟨m, hm⟩) hmul
  simp only [Module.End.mul_apply] at happ
  have e1 : ((G (K ⟨m, hm⟩)) : V) = g (k m) := by rw [hGcoe, hKcoe]
  have e2 : ((K (G ⟨m, hm⟩)) : V) = k (g m) := by rw [hKcoe, hGcoe]
  rw [← e1, happ, e2]

theorem apply_comm_of_finrank_eq_add_two (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x)
    (hdim : finrank F V = finrank F (fixedSpace x) + 2) {g k : V ≃ₗ[F] V}
    (hg : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[F] V)))
    (hk : k ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[F] V))) :
    ∀ v ∈ othersSpace x.toLinearMap (X - 1), g (k v) = k (g v) := by
  have hothersf := apply_comm_of_finrank_eq_add_two_aux2 hx hdim
  intro v hv
  unfold othersSpace at hv
  refine Submodule.iSup_induction _ (motive := fun m => g (k m) = k (g m)) hv ?_ (by simp) ?_
  · intro a m hm
    refine Submodule.iSup_induction _ (motive := fun m => g (k m) = k (g m)) hm ?_ (by simp) ?_
    · intro hcond m hm
      have ha : a ∈ primaryFactors x.toLinearMap := hcond.1
      have hne : a ≠ X - 1 := hcond.2.1
      have hle : finrank F (primaryComponent x.toLinearMap a) ≤ 2 := by
        have hsub : primaryComponent x.toLinearMap a ≤ othersSpace x.toLinearMap (X - 1) := by
          unfold othersSpace
          exact le_iSup₂_of_le a
            ⟨ha, hne, by rw [reciprocalPolynomial_X_sub_one]; exact hne⟩ le_rfl
        have h2 := Submodule.finrank_mono hsub
        rwa [hothersf] at h2
      exact apply_comm_of_finrank_eq_add_two_aux4 hp hp2 hpq hx ha hne hle hg hk m hm
    · intro u w hu hw
      rw [map_add, map_add, map_add, map_add, hu, hw]
  · intro u w hu hw
    rw [map_add, map_add, map_add, map_add, hu, hw]

theorem commutator_mem_supportedFixedDerived_gen (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x)
    (hdim : finrank F V = finrank F (fixedSpace x) + 2) {g k : V ≃ₗ[F] V}
    (hg : g ∈ isometryCentralizer Q x) (hk : k ∈ isometryCentralizer Q x) :
    ⁅g, k⁆ ∈ supportedFixedDerived Q x := by
  have hgc := (Subgroup.mem_inf.mp hg).2
  have hkc := (Subgroup.mem_inf.mp hk).2
  have hcI : ⁅g, k⁆ ∈ isometryCentralizer Q x := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hk) (inv_mem hg)) (inv_mem hk)
  have hfix : ∀ v ∈ othersSpace x.toLinearMap (X - 1), ⁅g, k⁆ v = v := by
    intro v hv
    have hv1 := mem_othersSpace_of_apply (inv_mem hkc) hv
    have hv2 := mem_othersSpace_of_apply (inv_mem hgc) hv1
    have hcm := apply_comm_of_finrank_eq_add_two hp hp2 hpq hx hdim hgc hkc _ hv2
    rw [commutatorElement_def]
    show g (k (g⁻¹ (k⁻¹ v))) = v
    rw [hcm]
    show k (g (g⁻¹ (k⁻¹ v))) = v
    rw [show g (g⁻¹ (k⁻¹ v)) = k⁻¹ v from g.apply_symm_apply _]
    exact k.apply_symm_apply v
  have hS : ⁅g, k⁆ ∈ supportedBlock Q x (X - 1) := mem_supportedBlock.2 ⟨hcI, hfix⟩
  refine mem_supportedFixedDerived.2 ⟨hS, ?_⟩
  have h1 : restrictFixed Q x ⟨⁅g, k⁆, hS⟩ = ⁅isometryRestrictFixed Q x ⟨g, hg⟩,
      isometryRestrictFixed Q x ⟨k, hk⟩⁆ := by
    rw [← isometryRestrictFixed_restrictFixed]
    rw [← map_commutatorElement]
    rfl
  rw [h1]
  exact Subgroup.commutator_mem_commutator (isometryRestrictFixed_mem_orthogonalGroup _)
    (isometryRestrictFixed_mem_orthogonalGroup _)

theorem commutator_centralizer_le_supportedFixedDerived_gen
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {y : ↥(orthDerived Q)} (hy : orderOf y = p)
    (hdim : finrank F V = finrank F (fixedSpace (y : V ≃ₗ[F] V)) + 2) :
    ⁅Subgroup.centralizer ({y} : Set ↥(orthDerived Q)),
        Subgroup.centralizer ({y} : Set ↥(orthDerived Q))⁆ ≤
      (supportedFixedDerived Q (y : V ≃ₗ[F] V)).subgroupOf (orthDerived Q) := by
  have hx := oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ y hy
  have hmem : ∀ g ∈ Subgroup.centralizer ({y} : Set ↥(orthDerived Q)),
      (g : V ≃ₗ[F] V) ∈ isometryCentralizer Q (y : V ≃ₗ[F] V) := by
    intro g hg
    refine mem_isometryCentralizer.2
      ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (orthDerived_le_orthogonalGroup g.2),
        fun v => ?_⟩
    exact congrArg (fun f : ↥(orthDerived Q) => (f : V ≃ₗ[F] V) v)
      (Subgroup.mem_centralizer_singleton_iff.1 hg)
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [Subgroup.mem_subgroupOf]
  exact commutator_mem_supportedFixedDerived_gen hp hp2 hpq hx hdim (hmem g hg) (hmem h hh)

theorem apply_eq_of_commute_supportedFixedDerived_gen {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x)
    (hT : ∃ U : Submodule F (fixedSpace x), finrank F U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0)
    {t : V ≃ₗ[F] V} (ht : t ∈ isometryCentralizer Q x)
    (hc : ∀ g ∈ supportedFixedDerived Q x, t * g = g * t) : ∀ w ∈ fixedSpace x, t w = w := by
  have hT1 : isometryRestrictFixed Q x ⟨t, ht⟩ = 1 := by
    refine eq_one_of_commute_orthDerived hx.polarBilin_fixed_nondegenerate hT
      (isometryRestrictFixed_mem_orthogonalGroup _) (fun h hh => ?_)
    obtain ⟨g, hg⟩ := restrictFixed_surjective hx h (orthDerived_le_orthogonalGroup hh)
    have hgmem : (g : V ≃ₗ[F] V) ∈ supportedFixedDerived Q x :=
      mem_supportedFixedDerived.mpr ⟨g.2, hg ▸ hh⟩
    have hprod : (⟨t, ht⟩ : ↥(isometryCentralizer Q x)) *
        ⟨(g : V ≃ₗ[F] V), supportedFixedDerived_le_isometryCentralizer hgmem⟩ =
        ⟨(g : V ≃ₗ[F] V), supportedFixedDerived_le_isometryCentralizer hgmem⟩ * ⟨t, ht⟩ :=
      Subtype.ext (hc (g : V ≃ₗ[F] V) hgmem)
    have h1 := congrArg (isometryRestrictFixed Q x) hprod
    rw [map_mul, map_mul] at h1
    have hG : isometryRestrictFixed Q x
        ⟨(g : V ≃ₗ[F] V), supportedFixedDerived_le_isometryCentralizer hgmem⟩ = h := by
      rw [show (⟨(g : V ≃ₗ[F] V), supportedFixedDerived_le_isometryCentralizer hgmem⟩ :
          ↥(isometryCentralizer Q x)) =
          ⟨g.1, supportedBlock_le_isometryCentralizer (X - 1) g.2⟩ from Subtype.ext rfl,
        isometryRestrictFixed_restrictFixed, hg]
    rwa [hG] at h1
  intro w hw
  have h1 := congrArg (fun f : fixedSpace x ≃ₗ[F] fixedSpace x => (f ⟨w, hw⟩ : V)) hT1
  simpa [coe_isometryRestrictFixed] using h1

theorem isQuasisimple_specialBlock_of_multiplicity (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) {m : ℕ}
    (hm : primaryMultiplicity x.toLinearMap h = m)
    (hm4 : 4 ≤ m ∨ ((m = 2 ∨ m = 3) ∧ 4 ≤ Nat.card F)) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  have hm2m : 2 ≤ m := by
    rcases hm4 with h4 | ⟨h2 | h3, -⟩ <;> omega
  by_cases hp3 : 3 < p
  · have hm2 : 2 ≤ primaryMultiplicity x.toLinearMap h := by
      rw [hm]
      exact hm2m
    exact hx.quasisimple_specialBlock hp hp3 hh hne hm2
  · have hself : h = reciprocalPolynomial h :=
      (hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hne).symm
    by_cases hK4 : 4 ≤ Nat.card F
    · exact hx.quasisimple_specialBlock3 hp hp2 hK4 hh hne (by rw [hm]; exact hm2m)
    · have hm4' : 4 ≤ m := by
        rcases hm4 with h4 | ⟨-, hcard⟩
        · exact h4
        · exact absurd hcard hK4
      haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
      exact CFSG.HardMathSupport.Timmesfeld.CrossChar.orth2_isQuasisimple_specialBlock_selfDual
        hx (hp.odd_of_ne_two hp2) hh hne hself (by rw [hm]; exact hm4')

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
