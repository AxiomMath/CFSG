module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.Order5616ProfileSupport
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.SharplyFourTransitiveM11
public import CFSG.CharacterTheory.Semidihedral.Principal.GL2OddKernelElimination

public section

open scoped Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.GL2ThreeCharacters
open CFSG.Semidihedral.FourPointMatrices (normalUnit normalUnit_surjective)
open MulAction

set_option maxRecDepth 20000 in
theorem coord_mem_quatHom_range : ∀ i : Coord, normalUnit i ^ 4 = 1 →
    (normalUnit i ^ 2 = 1 → normalUnit i = 1 ∨ normalUnit i = -1) →
    ∃ q : QuaternionGroup 2, GL2Elimination.quatHom q = normalUnit i := by
  decide

theorem mem_quatHom_range_of_pow_four {g : G23} (h4 : g ^ 4 = 1)
    (h2 : g ^ 2 = 1 → g = 1 ∨ g = -1) : g ∈ GL2Elimination.quatHom.range := by
  obtain ⟨i, rfl⟩ := normalUnit_surjective g
  exact coord_mem_quatHom_range i h4 h2

theorem nat_card_classOf_or {j k : Fin 8} (hjk : j ≠ k) :
    Nat.card {g : G23 // classOf g = j ∨ classOf g = k} = classSize j + classSize k := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_or,
    Finset.card_union_of_disjoint, card_filter_classOf, card_filter_classOf]
  exact Finset.disjoint_filter.mpr fun g _ h1 h2 => hjk (h1.symm.trans h2)

theorem card_subtype_le_card_of_mem (K : Subgroup G23) (P : G23 → Prop)
    (h : ∀ g, P g → g ∈ K) : Nat.card {g // P g} ≤ Nat.card K :=
  Nat.card_le_card_of_injective (fun g => (⟨g.1, h g.1 g.2⟩ : K)) fun _ _ hab => by
    have hv := congrArg Subtype.val hab
    exact Subtype.ext hv

theorem normal_card_eight_eq_quatHom_range (K : Subgroup G23) [hK : K.Normal]
    (hcard : Nat.card K = 8) : K = GL2Elimination.quatHom.range := by
  have hcl : ∀ g ∈ K, ∀ h : G23, classOf h = classOf g → h ∈ K := by
    intro g hg h hh
    obtain ⟨c, rfl⟩ := isConj_iff.mp ((isConj_iff_classOf g h).mpr hh.symm)
    exact hK.conj_mem g hg c
  have h5 : ∀ g ∈ K, classOf g ≠ 5 := by
    intro g hg h5
    have h := card_subtype_le_card_of_mem K _ (hcl g hg)
    rw [hcard, nat_card_classOf, h5] at h
    exact absurd h (by decide)
  have h8 : ∀ g ∈ K, orderOf g ≠ 8 := by
    intro g hg h8
    obtain ⟨h67, h2⟩ := classOf_of_orderOf_eight h8
    have hne : classOf g ≠ 2 := by rcases h67 with h | h <;> rw [h] <;> decide
    have h := card_subtype_le_card_of_mem K (fun h => classOf h = classOf g ∨ classOf h = 2)
      fun h hh => hh.elim (hcl g hg h) fun h' => hcl (g ^ 2) (K.pow_mem hg 2) h (h'.trans h2.symm)
    rw [hcard, nat_card_classOf_or hne] at h
    rcases h67 with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)
  have hle : K ≤ GL2Elimination.quatHom.range := by
    intro g hg
    have hdvd : orderOf g ∣ 8 := hcard ▸ Subgroup.orderOf_dvd_natCard K hg
    have hmem := GL2ThreeStructure.order_exhaustive g
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    refine mem_quatHom_range_of_pow_four ?_ fun hg2 => ?_
    · apply orderOf_dvd_iff_pow_eq_one.mp
      rcases hmem with h | h | h | h | h | h <;> rw [h] at hdvd ⊢ <;> first
        | exact absurd h (h8 g hg) | omega
    · have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact Or.inl (orderOf_eq_one_iff.mp h)
      · by_contra hne
        rw [not_or] at hne
        exact h5 g hg (classOf_of_orderOf_two h hne.2)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, GL2Elimination.card_quatHom_range])

section Action

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem injective_vec_four {x y z v : Ω} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hv : v ∉ ({x, y, z} : Finset Ω)) : Function.Injective ![x, y, z, v] := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  obtain ⟨hvx, hvy, hvz⟩ := hv
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem eq_of_smul_eq_of_sharp
    (hsharp : ∀ a b : Fin 4 → Ω, Function.Injective a → Function.Injective b →
      ∃! g : G, ∀ i, g • a i = b i)
    {a : Fin 4 → Ω} (ha : Function.Injective a) {g g' : G} (h : ∀ i, g • a i = g' • a i) :
    g = g' :=
  (hsharp a (fun i => g' • a i) ha ((MulAction.injective g').comp ha)).unique h fun _ => rfl

theorem faithfulSMul_of_sharp (hΩ : Nat.card Ω = 11)
    (hsharp : ∀ a b : Fin 4 → Ω, Function.Injective a → Function.Injective b →
      ∃! g : G, ∀ i, g • a i = b i) : FaithfulSMul G Ω := by
  have : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hΩ]; norm_num)
  let e := Finite.equivFinOfCardEq hΩ
  have ha : Function.Injective fun i : Fin 4 => e.symm (Fin.castLE (by norm_num) i) :=
    e.symm.injective.comp (Fin.castLE_injective _)
  exact ⟨fun h => eq_of_smul_eq_of_sharp hsharp ha fun i => h _⟩

theorem triple_stabilizer_mulEquiv_quaternion [Finite G]
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) {t : G} (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) (hΩ : Nat.card Ω = 11)
    (hsharp : ∀ a b : Fin 4 → Ω, Function.Injective a → Function.Injective b →
      ∃! g : G, ∀ i, g • a i = b i)
    {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Nonempty (↥(stabilizer G x ⊓ stabilizer G y ⊓ stabilizer G z) ≃* QuaternionGroup 2) := by
  have : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hΩ]; norm_num)
  set s : Finset Ω := {x, y, z} with hs
  set K := stabilizer G x ⊓ stabilizer G y ⊓ stabilizer G z with hKdef
  have hmemK : ∀ g : G, g ∈ K ↔ ∀ p ∈ s, g • p = p := by
    intro g
    simp only [hKdef, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, hs, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq, and_assoc]
  have hcomp : Nat.card {v : Ω // v ∉ s} = 8 := by
    have : Fintype Ω := Fintype.ofFinite Ω
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe,
      ← Nat.card_eq_fintype_card, hΩ, Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩]
  obtain ⟨⟨w, hw⟩⟩ : Nonempty {v : Ω // v ∉ s} :=
    (Nat.card_pos_iff.mp (by rw [hcomp]; norm_num)).1
  have hfix4 : ∀ g : G, (∀ p ∈ s, g • p = p) → ∀ v ∉ s, g • v = v → g = 1 := by
    intro g hg v hv hgv
    refine eq_of_smul_eq_of_sharp hsharp (injective_vec_four hxy hxz hyz hv) fun i => ?_
    fin_cases i <;> simp [hg, hgv, hs]
  have hKcard : Nat.card K = 8 := by
    rw [← hcomp]
    refine Nat.card_eq_of_bijective (fun k : K => (⟨(k : G) • w, fun hk => hw ?_⟩ :
      {v : Ω // v ∉ s})) ⟨?_, ?_⟩
    · have h1 : (k : G) • ((k : G) • w) = (k : G) • w := (hmemK k).mp k.2 _ hk
      rw [← smul_left_cancel _ h1]
      exact hk
    · intro k₁ k₂ h
      have h' : (k₁ : G) • w = (k₂ : G) • w := congrArg Subtype.val h
      refine Subtype.ext (eq_of_smul_eq_of_sharp hsharp (injective_vec_four hxy hxz hyz hw)
        fun i => ?_)
      have h1 := (hmemK k₁).mp k₁.2
      have h2 := (hmemK k₂).mp k₂.2
      fin_cases i <;> simp [h1, h2, h', hs]
    · rintro ⟨v, hv⟩
      obtain ⟨g, hg, -⟩ := hsharp ![x, y, z, w] ![x, y, z, v] (injective_vec_four hxy hxz hyz hw)
        (injective_vec_four hxy hxz hyz hv)
      have hgK : g ∈ K := by
        rw [hmemK]
        intro p hp
        simp only [hs, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl
        · exact hg 0
        · exact hg 1
        · exact hg 2
      exact ⟨⟨g, hgK⟩, Subtype.ext (hg 3)⟩
  have hP : IsPGroup 2 K := IsPGroup.of_card (n := 3) (by rw [hKcard]; norm_num)
  have : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by rw [hKcard]; norm_num)
  have : Nontrivial (Subgroup.center K) := hP.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center K) :=
    ((hP.to_subgroup (Subgroup.center K)).card_eq_or_dvd).resolve_left Finite.one_lt_card.ne'
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  set ug : G := ((u : K) : G) with hugdef
  have hug : orderOf ug = 2 := by rw [hugdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu]
  have hugK : ug ∈ K := (u : K).2
  have hfixu : ∀ v, ug • v = v → v ∈ s := by
    intro v hv
    by_contra hvs
    have h1 := hfix4 ug ((hmemK ug).mp hugK) v hvs hv
    rw [h1, orderOf_one] at hug
    exact absurd hug (by norm_num)
  set C := Subgroup.centralizer ({ug} : Set G) with hCdef
  have hCs : ∀ c ∈ C, ∀ p ∈ s, c • p ∈ s := by
    intro c hc p hp
    refine hfixu _ ?_
    rw [smul_smul, ← Subgroup.mem_centralizer_singleton_iff.mp hc, mul_smul,
      (hmemK ug).mp hugK p hp]
  have hKC : K ≤ C := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_center_iff.mp u.2 ⟨k, hk⟩
    exact congrArg Subtype.val h
  have hK'n : (K.subgroupOf C).Normal := by
    constructor
    intro n hn c
    rw [Subgroup.mem_subgroupOf, hmemK] at hn ⊢
    intro p hp
    have hc' : (c : G)⁻¹ • p ∈ s := hCs _ (C.inv_mem c.2) p hp
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hn _ hc', smul_inv_smul]
  obtain ⟨ψ⟩ := nonempty_centralizer_involution_mulEquiv hinv ht φ hug
  set K'' := (K.subgroupOf C).map ψ.toMonoidHom with hK''def
  have hK''n : K''.Normal := hK'n.map ψ.toMonoidHom ψ.surjective
  have hK''card : Nat.card K'' = 8 := by
    rw [hK''def, ← Nat.card_congr (Subgroup.equivMapOfInjective _ ψ.toMonoidHom
      ψ.injective).toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv, hKcard]
  have hK''eq := normal_card_eight_eq_quatHom_range K'' hK''card
  exact ⟨(Subgroup.subgroupOfEquivOfLe hKC).symm.trans
    ((Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans
      ((MulEquiv.subgroupCongr hK''eq).trans
        (MonoidHom.ofInjective GL2Elimination.quatHom_injective).symm))⟩

theorem exists_triple_stabilizer_mulEquiv_quaternion [Finite G]
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) {t : G} (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) (hΩ : Nat.card Ω = 11)
    (hsharp : ∀ a b : Fin 4 → Ω, Function.Injective a → Function.Injective b →
      ∃! g : G, ∀ i, g • a i = b i) :
    ∃ x y z : Ω, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      Nonempty (↥(stabilizer G x ⊓ stabilizer G y ⊓ stabilizer G z) ≃* QuaternionGroup 2) := by
  have : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hΩ]; norm_num)
  let e := Finite.equivFinOfCardEq hΩ
  have h01 : e.symm 0 ≠ e.symm 1 := e.symm.injective.ne (by decide)
  have h02 : e.symm 0 ≠ e.symm 2 := e.symm.injective.ne (by decide)
  have h12 : e.symm 1 ≠ e.symm 2 := e.symm.injective.ne (by decide)
  exact ⟨e.symm 0, e.symm 1, e.symm 2, h01, h02, h12,
    triple_stabilizer_mulEquiv_quaternion hinv ht φ hΩ hsharp h01 h02 h12⟩

end Action

theorem sharply_four_transitive_GL2_centralizer_exact_M11
    {G : Type} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω]
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) {t : G} (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) (hΩ : Nat.card Ω = 11)
    (hsharp : ∀ a b : Fin 4 → Ω, Function.Injective a → Function.Injective b →
      ∃! g : G, ∀ i, g • a i = b i) :
    (∃ f : Ω ≃ Fin 11, ∀ p : Equiv.Perm (Fin 11), p ∈ CFSG.Open.StatedM11 ↔
        ∃ g : G, ∀ i, p i = f (g • f.symm i)) ∧
      Nonempty (G ≃* CFSG.Open.StatedM11) ∧
      Nonempty (G ≃* CFSG.Assembly.LowTwoRank.StatedM11) := by
  have := faithfulSMul_of_sharp hΩ hsharp
  obtain ⟨f, hf, ⟨e⟩⟩ := sharply_four_transitive_quaternion_action_exact_M11 hΩ hsharp
    (exists_triple_stabilizer_mulEquiv_quaternion hinv ht φ hΩ hsharp)
  exact ⟨⟨f, hf⟩, ⟨e⟩, ⟨e.trans (MulEquiv.subgroupCongr
    (statedM11_eq_nativeM11.trans lowTwoRankStatedM11_eq_nativeM11.symm))⟩⟩

end CFSG.Semidihedral.GL2Recognition
