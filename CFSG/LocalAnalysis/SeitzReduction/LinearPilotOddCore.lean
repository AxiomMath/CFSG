module

public import CFSG.RankThree.SteinbergR3ECALinearPrimaryBlocks
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

section Generic

variable {G : Type*} [Group G]

theorem commute_of_isQuasisimple_of_odd_card {F N : Subgroup G} (hF : CFSG.IsQuasisimple F)
    (hN : Odd (Nat.card N)) (hFN : ∀ f ∈ F, ∀ y ∈ N, f * y * f⁻¹ ∈ N)
    (hNF : ∀ y ∈ N, ∀ f ∈ F, y * f * y⁻¹ ∈ F) {u : G} (huF : u ∈ F) (hu : orderOf u = 2) :
    ∀ y ∈ N, ∀ f ∈ F, y * f = f * y := by
  have hM : (N.subgroupOf F).Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    have := hFN g g.2 m hm
    simpa using this
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hF hM with htop | hcen
  · exfalso
    have huN : u ∈ N := by
      have : (⟨u, huF⟩ : F) ∈ N.subgroupOf F := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    have h2 := Subgroup.orderOf_dvd_natCard N huN
    rw [hu] at h2
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h2)
  · have hcomm : ⁅F, N⁆ ≤ N ⊓ F := by
      rw [Subgroup.commutator_le]
      intro f hf y hy
      rw [commutatorElement_def]
      refine ⟨N.mul_mem (hFN f hf y hy) (N.inv_mem hy), ?_⟩
      have := F.mul_mem hf (hNF y hy f⁻¹ (F.inv_mem hf))
      simpa [mul_assoc] using this
    have hcent : N ⊓ F ≤ centralizer (F : Set G) := by
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 : (⟨c, hc.2⟩ : F) ∈ center F := hcen (Subgroup.mem_subgroupOf.mpr hc.1)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨f, hf⟩)
    have hbot : ⁅⁅F, N⁆, F⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hcomm.trans hcent
    have hFN' := CFSG.LocalCores.perfect_double_commutator hF.1 hbot
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hFN'
    intro y hy f hf
    exact Subgroup.mem_centralizer_iff.mp (hFN' hf) y hy

theorem commute_of_conj_mul_mem_of_coprime {S : Subgroup G} {b : G} {m : ℕ} (hb : b ^ m = 1)
    (hcop : Nat.Coprime m (Nat.card S)) (hSb : ∀ s ∈ S, b * s * b⁻¹ ∈ S)
    (hc : ∀ s ∈ S, Commute b (s⁻¹ * (b * s * b⁻¹))) : ∀ s ∈ S, b * s = s * b := by
  intro s hs
  set c := s⁻¹ * (b * s * b⁻¹) with hcdef
  have hcS : c ∈ S := S.mul_mem (S.inv_mem hs) (hSb s hs)
  have hbc : Commute b c := hc s hs
  have hbs : b * s * b⁻¹ = s * c := by
    rw [hcdef]
    group
  have hiter : ∀ j : ℕ, b ^ j * s * (b ^ j)⁻¹ = s * c ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcj : b * c ^ j * b⁻¹ = c ^ j := by
        rw [(hbc.pow_right j).eq]
        group
      calc b ^ (j + 1) * s * (b ^ (j + 1))⁻¹ = b * (b ^ j * s * (b ^ j)⁻¹) * b⁻¹ := by group
        _ = b * (s * c ^ j) * b⁻¹ := by rw [ih]
        _ = (b * s * b⁻¹) * (b * c ^ j * b⁻¹) := by group
        _ = s * c ^ (j + 1) := by rw [hbs, hcj, mul_assoc, ← pow_succ']
  have hcm : c ^ m = 1 := by
    have h := hiter m
    rw [hb, one_mul, inv_one, mul_one] at h
    exact mul_eq_left.mp h.symm
  have hord : orderOf c = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hcm) hcop)
      (Subgroup.orderOf_dvd_natCard S hcS)
  have hc1 : c = 1 := orderOf_eq_one_iff.mp hord
  have hbs' : b * s * b⁻¹ = s := by rw [hbs, hc1, mul_one]
  calc b * s = b * s * b⁻¹ * b := by group
    _ = s * b := by rw [hbs']

theorem commute_of_map_commute_of_pow_eq_one {P : Type*} [Group P] (π : G →* P)
    (hker : π.ker ≤ center G) {m : ℕ} (hcop : Nat.Coprime m (Nat.card π.ker)) {g a : G}
    (hg : g ^ m = 1) (hga : π g * π a = π a * π g) : g * a = a * g := by
  set c := g * a * g⁻¹ * a⁻¹ with hcdef
  have hcker : c ∈ π.ker := by
    rw [MonoidHom.mem_ker, hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, hga]
    group
  have hcz : c ∈ center G := hker hcker
  have hga' : g * a * g⁻¹ = c * a := by
    rw [hcdef]
    group
  have hiter : ∀ j : ℕ, g ^ j * a * (g ^ j)⁻¹ = c ^ j * a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcj : g * c ^ j * g⁻¹ = c ^ j := by
        rw [(Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hcz j)) g]
        group
      calc g ^ (j + 1) * a * (g ^ (j + 1))⁻¹ = g * (g ^ j * a * (g ^ j)⁻¹) * g⁻¹ := by group
        _ = g * (c ^ j * a) * g⁻¹ := by rw [ih]
        _ = (g * c ^ j * g⁻¹) * (g * a * g⁻¹) := by group
        _ = c ^ (j + 1) * a := by rw [hcj, hga', ← mul_assoc, ← pow_succ]
  have hcm : c ^ m = 1 := by
    have h := hiter m
    rw [hg, one_mul, inv_one, mul_one] at h
    exact mul_eq_right.mp h.symm
  have hord : orderOf c = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hcm) hcop)
      (Subgroup.orderOf_dvd_natCard π.ker hcker)
  have hc1 : c = 1 := orderOf_eq_one_iff.mp hord
  have h1 : g * a * g⁻¹ = a := by rw [hga', hc1, one_mul]
  calc g * a = g * a * g⁻¹ * g := by group
    _ = a * g := by rw [h1]

theorem exists_lift_pow_two_pow_eq_one {P : Type*} [Group P] [Finite G] (π : G →* P)
    (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker)) {z : P} {e : ℕ}
    (hz : z ^ 2 ^ e = 1) : ∃ y : G, π y = z ∧ y ^ 2 ^ e = 1 := by
  obtain ⟨y₀, rfl⟩ := hπ z
  set r := Nat.card π.ker with hr
  have hy₀ : y₀ ^ 2 ^ e ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hz]
  have hy₁ : (y₀ ^ r) ^ 2 ^ e = 1 := by
    have h1 : (⟨y₀ ^ 2 ^ e, hy₀⟩ : π.ker) ^ r = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [← pow_mul, mul_comm, pow_mul]
    exact h2
  have hcop : Nat.Coprime r (orderOf (π y₀)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hz)
      (Nat.Coprime.pow_right e (Odd.coprime_two_right hker))
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(y₀ ^ r) ^ u, ?_, ?_⟩
  · rw [map_pow, map_pow, hu]
  · rw [← pow_mul, mul_comm, pow_mul, hy₁, one_pow]

theorem odd_card_comap_of_odd {P : Type*} [Group P] [Finite G] (π : G →* P)
    (hker : Odd (Nat.card π.ker)) {S : Subgroup P} (hS : Odd (Nat.card S)) :
    Odd (Nat.card (S.comap π)) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := S.comap π) 2 h2
  have hg' : orderOf (g : G) = 2 := by rw [Subgroup.orderOf_coe, hg]
  have h1 : orderOf (π (g : G)) = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (hg' ▸ orderOf_map_dvd π (g : G))
        (Nat.coprime_two_left.mpr hS))
      (Subgroup.orderOf_dvd_natCard S g.2)
  have hgk : (g : G) ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    exact orderOf_eq_one_iff.mp h1
  have h3 := Subgroup.orderOf_dvd_natCard π.ker hgk
  rw [hg'] at h3
  exact (Nat.not_even_iff_odd.mpr hker) (even_iff_two_dvd.mpr h3)

theorem odd_orderOf_of_odd_orderOf_map {P : Type*} [Group P] [Finite G] (π : G →* P)
    (hker : Odd (Nat.card π.ker)) {a : G} (ha : Odd (orderOf (π a))) : Odd (orderOf a) := by
  set m := orderOf (π a)
  have ham : a ^ m ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  have h1 : a ^ (m * Nat.card π.ker) = 1 := by
    have h2 : (⟨a ^ m, ham⟩ : π.ker) ^ Nat.card π.ker = 1 := pow_card_eq_one'
    have h3 := congrArg Subtype.val h2
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h3
    rw [pow_mul]
    exact h3
  exact Odd.of_dvd_nat (ha.mul hker) (orderOf_dvd_of_pow_eq_one h1)

theorem conj_mem_map_subtype_of_normal {C : Subgroup G} {M : Subgroup C} (hM : M.Normal) {g p : G}
    (hg : g ∈ C) (hp : p ∈ M.map C.subtype) : g * p * g⁻¹ ∈ M.map C.subtype := by
  obtain ⟨m, hm, rfl⟩ := hp
  exact ⟨⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹, hM.conj_mem m hm _, rfl⟩

theorem map_oddCore_le_oddCore_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A]
    (φ : A ≃* B) : (CFSG.oddCore A).map φ.toMonoidHom ≤ CFSG.oddCore B :=
  CFSG.DisconnectedInvolutionGraph.Helpers.normal_odd_le_oddCore _
    ((CFSG.oddCore_normal A).map _ φ.surjective)
    (by
      rw [Subgroup.card_map_of_injective φ.injective]
      exact CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd)

end Generic

section GeneralLinear

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.CALinearPrimary

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {x : LinearMap.GeneralLinearGroup k V}

theorem one_le_primaryMultiplicity_of_squarefree
    (hsq : Squarefree (minpoly k (x : Module.End k V))) {h : k[X]}
    (hh : h ∈ primaryFactors (x : Module.End k V)) :
    1 ≤ primaryMultiplicity (x : Module.End k V) h := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have h1 : Module.finrank (AdjoinRoot h) (primaryComponent (x : Module.End k V) h) = 0 := h0
  apply primaryComponent_ne_bot hsq hh
  rw [← Submodule.finrank_eq_zero (R := k), finrank_primaryComponent, h1, mul_zero]

theorem card_le_card_adjoinRoot [Finite k] {h : k[X]} [Fact (Irreducible h)] :
    Nat.card k ≤ Nat.card (AdjoinRoot h) := by
  have : Finite (AdjoinRoot h) := Module.finite_of_finite k
  exact Nat.card_le_card_of_injective _ (algebraMap k (AdjoinRoot h)).injective

theorem exists_orderOf_eq_two_mem_linearSpecialBlock [CharP k 2]
    (hsq : Squarefree (minpoly k (x : Module.End k V))) {h : k[X]}
    (hh : h ∈ primaryFactors (x : Module.End k V))
    (hm : 2 ≤ primaryMultiplicity (x : Module.End k V) h) :
    ∃ u ∈ linearSpecialBlock x h, orderOf u = 2 := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have : CharP (AdjoinRoot h) 2 :=
    charP_of_injective_algebraMap (algebraMap k (AdjoinRoot h)).injective 2
  set m := primaryMultiplicity (x : Module.End k V) h with hmdef
  let b : Module.Basis (Fin m) (AdjoinRoot h) (primaryComponent (x : Module.End k V) h) :=
    Module.finBasisOfFinrankEq _ _ rfl
  have hij : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by
    intro h'
    exact absurd (congrArg Fin.val h') (by norm_num)
  set T : Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h) :=
    Matrix.SpecialLinearGroup.transvection hij 1 with hT
  obtain ⟨g, hg⟩ := linearSpecialBlockRestrict_surjective hsq hh
    (Matrix.SpecialLinearGroup.toLin_equiv b T)
  have hT2 : T ^ 2 = 1 := by
    have h1 := CFSG.RankThree.CALinearPlane.transvection_pow_char (k := AdjoinRoot h) (ℓ := 2)
      hij 1
    rwa [pow_one] at h1
  have hT1 : T ≠ 1 := by
    intro h1
    have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h) =>
      (A : Matrix (Fin m) (Fin m) (AdjoinRoot h)) ⟨0, by omega⟩ ⟨1, by omega⟩) h1
    simp [hT, Matrix.SpecialLinearGroup.transvection_coe, hij] at h2
  refine ⟨g.1, g.2, orderOf_eq_prime ?_ ?_⟩
  · have h1 : g ^ 2 = 1 := by
      apply linearSpecialBlockRestrict_injective hsq
      rw [map_pow, hg, ← map_pow, hT2, map_one, map_one]
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  · intro h1
    have h2 : g = 1 := Subtype.ext h1
    rw [h2, map_one] at hg
    exact hT1 ((Matrix.SpecialLinearGroup.toLin_equiv b).injective (by rw [← hg, map_one]))

theorem commute_of_mem_of_odd_of_conj_mem [Finite k] [CharP k 2]
    (hsq : Squarefree (minpoly k (x : Module.End k V)))
    (hblock : ∀ h ∈ primaryFactors (x : Module.End k V),
      primaryMultiplicity (x : Module.End k V) h = 2 → 4 ≤ Nat.card (AdjoinRoot h))
    {N : Subgroup (LinearMap.GeneralLinearGroup k V)} (hNC : N ≤ gl_centralizer x)
    (hN : Odd (Nat.card N))
    (hFN : ∀ h ∈ primaryFactors (x : Module.End k V), ∀ f ∈ linearSpecialBlock x h, ∀ y ∈ N,
      f * y * f⁻¹ ∈ N)
    {y : LinearMap.GeneralLinearGroup k V} (hy : y ∈ N)
    {g : LinearMap.GeneralLinearGroup k V} (hg : g ∈ gl_centralizer x) : y * g = g * y := by
  have hyC := hNC hy
  have hscal : ∀ a : primaryFactors (x : Module.End k V), ∃ c : AdjoinRoot (a : k[X]),
      ∀ v : primaryComponent (x : Module.End k V) (a : k[X]),
        (y : Module.End k V) (v : V) =
          ((c • v : primaryComponent (x : Module.End k V) (a : k[X])) : V) := by
    rintro ⟨h, hh⟩
    refine exists_smul_of_commute_pow_char (ℓ := 2) hsq hh hyC fun f hf _ => ?_
    rcases (one_le_primaryMultiplicity_of_squarefree hsq hh).eq_or_lt with h1 | h2
    · rw [linearSpecialBlock_eq_bot hsq hh h1.symm, Subgroup.mem_bot] at hf
      rw [hf, mul_one, one_mul]
    · have hq : CFSG.IsQuasisimple (linearSpecialBlock x h) := by
        refine isQuasisimple_linearSpecialBlock hsq hh ?_
        rcases (show 2 ≤ primaryMultiplicity (x : Module.End k V) h from h2).eq_or_lt with
          h3 | h3
        · exact Or.inr ⟨h2, hblock h hh h3.symm⟩
        · exact Or.inl h3
      obtain ⟨u, huF, hu⟩ := exists_orderOf_eq_two_mem_linearSpecialBlock hsq hh h2
      exact commute_of_isQuasisimple_of_odd_card hq hN (hFN h hh)
        (fun y' hy' f' hf' => conj_mem_linearSpecialBlock (hNC hy') hf') huF hu y hy f hf
  set Y : commutant (x : Module.End k V) :=
    ⟨(y : Module.End k V), mem_commutant_of_mem_gl_centralizer hyC⟩ with hYdef
  have hYc : Y ∈ Subalgebra.center k (commutant (x : Module.End k V)) :=
    (mem_center_commutant_iff hsq Y).mpr hscal
  have h1 := Subalgebra.mem_center_iff.mp hYc
    ⟨(g : Module.End k V), mem_commutant_of_mem_gl_centralizer hg⟩
  apply Units.ext
  have h2 := congrArg Subtype.val h1
  simpa [hYdef] using h2.symm

theorem commute_of_mem_of_odd_of_conj_mem_of_four_le [Finite k] [CharP k 2]
    (hk : 4 ≤ Nat.card k) (hsq : Squarefree (minpoly k (x : Module.End k V)))
    {N : Subgroup (LinearMap.GeneralLinearGroup k V)} (hNC : N ≤ gl_centralizer x)
    (hN : Odd (Nat.card N))
    (hFN : ∀ h ∈ primaryFactors (x : Module.End k V), ∀ f ∈ linearSpecialBlock x h, ∀ y ∈ N,
      f * y * f⁻¹ ∈ N)
    {y : LinearMap.GeneralLinearGroup k V} (hy : y ∈ N)
    {g : LinearMap.GeneralLinearGroup k V} (hg : g ∈ gl_centralizer x) : y * g = g * y :=
  commute_of_mem_of_odd_of_conj_mem hsq
    (fun h hh _ => by
      have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
      exact hk.trans card_le_card_adjoinRoot)
    hNC hN hFN hy hg

end GeneralLinear

section SpecialLinear

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.CALinearPrimary

variable {n : ℕ} {k : Type*} [Field k]

theorem commute_oddCore_centralizer_specialLinear [Finite k] [CharP k 2] (hk : 4 ≤ Nat.card k)
    {a : Matrix.SpecialLinearGroup (Fin n) k} (ha : Odd (orderOf a)) :
    ∀ w ∈ CFSG.oddCore (centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) k))),
      ∀ g : centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) k)), Commute w g := by
  set H := centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) k)) with hHdef
  have hpk : ((orderOf a : ℕ) : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k 2]
    exact fun h2 => (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr h2)
  have hsq := squarefree_minpoly_slGL hpk (pow_orderOf_eq_one a)
  set N := ((CFSG.oddCore H).map H.subtype).map (slGL n k) with hNdef
  have hmemH : ∀ {g : Matrix.SpecialLinearGroup (Fin n) k}, g ∈ H →
      slGL n k g ∈ gl_centralizer (slGL n k a) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    rw [← map_mul, ← map_mul, hg]
  have hNC : N ≤ gl_centralizer (slGL n k a) := by
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact hmemH w.2
  have hNodd : Odd (Nat.card N) := by
    rw [hNdef, Subgroup.card_map_of_injective slGL_injective,
      Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hFN : ∀ h ∈ primaryFactors ((slGL n k a : LinearMap.GeneralLinearGroup k (Fin n → k)) :
      Module.End k (Fin n → k)), ∀ f ∈ linearSpecialBlock (slGL n k a) h, ∀ y ∈ N,
      f * y * f⁻¹ ∈ N := by
    intro h hh f hf y hy
    obtain ⟨f', rfl⟩ := linearSpecialBlock_le_range_slGL hsq hh hf
    have hf'H : f' ∈ H := comap_linearSpecialBlock_le_centralizer h hf
    obtain ⟨y₁, hy₁, rfl⟩ := hy
    rw [← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, conj_mem_map_subtype_of_normal (CFSG.oddCore_normal H) hf'H hy₁, rfl⟩
  intro w hw g
  have h1 := commute_of_mem_of_odd_of_conj_mem_of_four_le hk hsq hNC hNodd hFN
    (y := slGL n k w) ⟨w, ⟨w, hw, rfl⟩, rfl⟩ (hmemH g.2)
  rw [← map_mul, ← map_mul] at h1
  exact Subtype.ext (slGL_injective h1)

end SpecialLinear

section Projective

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type*} [Field K]

theorem odd_card_scalars [Finite K] [CharP K 2] : Odd (Nat.card (scalars n K)) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := scalars n K) 2 h2
  obtain ⟨c, -, hgc⟩ := g.2
  have hg2 : g ^ 2 = 1 := hg ▸ pow_orderOf_eq_one g
  have hg1 : g = 1 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact Subtype.ext (Subtype.ext (Matrix.ext fun i _ => i.elim0))
    · have : NeZero n := ⟨hn.ne'⟩
      have hc2 : (c : K) ^ 2 = 1 := by
        have h := congrArg (fun y : scalars n K =>
          ((y : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) 0 0) hg2
        change ((g : Matrix.SpecialLinearGroup (Fin n) K) ^ 2).val 0 0 =
          (1 : Matrix (Fin n) (Fin n) K) 0 0 at h
        rw [Matrix.SpecialLinearGroup.coe_pow, hgc, ← map_pow, Matrix.scalar_apply,
          Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
        exact h
      have hc1 : (c : K) = 1 := by
        have h := sub_pow_char (p := 2) (c : K) 1
        rw [hc2, one_pow, sub_self] at h
        exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h)
      apply Subtype.ext
      apply Subtype.ext
      change (g : Matrix.SpecialLinearGroup (Fin n) K).val = 1
      rw [hgc, hc1, map_one]
  rw [hg1, orderOf_one] at hg
  exact absurd hg (by norm_num)

theorem commute_oddCore_centralizer_singleton [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {x : projectiveSL n K} (hx : Odd (orderOf x)) {z : projectiveSL n K}
    (hzx : z ∈ centralizer ({x} : Set (projectiveSL n K))) {e : ℕ} (hz : z ^ 2 ^ e = 1) :
    ∀ w ∈ CFSG.oddCore (centralizer ({x} : Set (projectiveSL n K))),
      Commute (w : projectiveSL n K) z := by
  set Cb := centralizer ({x} : Set (projectiveSL n K)) with hCbdef
  have hZodd : Odd (Nat.card (proj n K).ker) := by
    rw [ker_proj]
    exact odd_card_scalars
  have hZc : (proj n K).ker ≤ center (Matrix.SpecialLinearGroup (Fin n) K) := by
    rw [ker_proj]
    exact scalars_le_center n K
  obtain ⟨a, rfl⟩ := proj_surjective n K x
  have ha : Odd (orderOf a) := odd_orderOf_of_odd_orderOf_map (proj n K) hZodd hx
  obtain ⟨y, rfl, hye⟩ :=
    exists_lift_pow_two_pow_eq_one (proj n K) (proj_surjective n K) hZodd hz
  set H := centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) K)) with hHdef
  have hHCb : ∀ {g}, g ∈ H → proj n K g ∈ Cb := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    rw [← map_mul, ← map_mul, hg]
  have hyH : y ∈ H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_of_map_commute_of_pow_eq_one (proj n K) hZc
      (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hZodd)) hye
      (Subgroup.mem_centralizer_singleton_iff.mp hzx)
  have hHn : ∀ g, proj n K g ∈ Cb → ∀ h ∈ H, g * h * g⁻¹ ∈ H := by
    intro g hg h hh
    rw [Subgroup.mem_centralizer_singleton_iff] at hg hh ⊢
    have hc : g * a * g⁻¹ * a⁻¹ ∈ center (Matrix.SpecialLinearGroup (Fin n) K) := hZc (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hg]
      group)
    have h1 : Commute (g * h * g⁻¹) (g * a * g⁻¹) := (Commute.conj_iff g).mpr hh
    have h2 : Commute (g * h * g⁻¹) (g * a * g⁻¹ * a⁻¹) :=
      (Subgroup.mem_center_iff.mp hc) (g * h * g⁻¹)
    have h3 := h2.inv_right.mul_right h1
    have h4 : (g * a * g⁻¹ * a⁻¹)⁻¹ * (g * a * g⁻¹) = a := by group
    rw [h4] at h3
    exact h3.eq
  set Ob := (CFSG.oddCore Cb).map Cb.subtype with hObdef
  set N := Ob.comap (proj n K) with hNdef
  have hObodd : Odd (Nat.card Ob) := by
    rw [hObdef, Subgroup.card_map_of_injective Cb.subtype_injective]
    exact CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hNodd : Odd (Nat.card N) := odd_card_comap_of_odd (proj n K) hZodd hObodd
  have hNCb : ∀ s ∈ N, proj n K s ∈ Cb := fun s hs => Subgroup.map_subtype_le _ hs
  have hconjN : ∀ g, proj n K g ∈ Cb → ∀ s ∈ N, g * s * g⁻¹ ∈ N := by
    intro g hg s hs
    rw [hNdef, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact conj_mem_map_subtype_of_normal (CFSG.oddCore_normal Cb) hg hs
  have hMnormal : (N.subgroupOf H).Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    have := hconjN (g : Matrix.SpecialLinearGroup (Fin n) K) (hHCb g.2) m hm
    simpa using this
  have hModd : Odd (Nat.card (N.subgroupOf H)) := by
    have h1 : Nat.card (N.subgroupOf H) = Nat.card (N ⊓ H : Subgroup _) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective H.subtype_injective]
    rw [h1]
    exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le inf_le_left)
  have hMle : N.subgroupOf H ≤ CFSG.oddCore H :=
    CFSG.DisconnectedInvolutionGraph.Helpers.normal_odd_le_oddCore _ hMnormal hModd
  have hcentral := commute_oddCore_centralizer_specialLinear hK ha
  have hiter := commute_of_conj_mul_mem_of_coprime (S := N) hye
    (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hNodd)) (hconjN y hzx) (fun s hs => by
      have hcN : s⁻¹ * (y * s * y⁻¹) ∈ N := N.mul_mem (N.inv_mem hs) (hconjN y hzx s hs)
      have hcH : s⁻¹ * (y * s * y⁻¹) ∈ H := by
        have h1 : s⁻¹ * (y * s * y⁻¹) = (s⁻¹ * y * s⁻¹⁻¹) * y⁻¹ := by group
        rw [h1]
        refine H.mul_mem (hHn s⁻¹ ?_ y hyH) (H.inv_mem hyH)
        rw [map_inv]
        exact Cb.inv_mem (hNCb s hs)
      have h2 := hcentral ⟨_, hcH⟩ (hMle (Subgroup.mem_subgroupOf.mpr hcN)) ⟨y, hyH⟩
      exact (congrArg Subtype.val h2).symm)
  intro w hw
  obtain ⟨s, hs⟩ := proj_surjective n K (w : projectiveSL n K)
  have hsN : s ∈ N := by
    rw [hNdef, Subgroup.mem_comap, hs]
    exact ⟨w, hw, rfl⟩
  have h1 := congrArg (proj n K) (hiter s hsN)
  rw [map_mul, map_mul, hs] at h1
  exact h1.symm

theorem commute_oddCore_centralizer_of_pow_eq_one [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {X : Subgroup (projectiveSL n K)} (hXc : IsCyclic X) (hXodd : Odd (Nat.card X))
    {z : projectiveSL n K} (hzX : z ∈ centralizer (X : Set (projectiveSL n K))) {e : ℕ}
    (hz : z ^ 2 ^ e = 1) :
    ∀ w ∈ CFSG.oddCore (centralizer (X : Set (projectiveSL n K))),
      Commute (w : projectiveSL n K) z := by
  obtain ⟨x, rfl⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top X).mp hXc
  rw [Nat.card_zpowers] at hXodd
  have hcen : centralizer ((zpowers x : Subgroup (projectiveSL n K)) : Set (projectiveSL n K)) =
      centralizer ({x} : Set (projectiveSL n K)) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [hcen] at hzX ⊢
  exact commute_oddCore_centralizer_singleton hK hXodd hzX hz

theorem commute_oddCore_centralizer [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {X : Subgroup (projectiveSL n K)} (hXc : IsCyclic X) (hXodd : Odd (Nat.card X))
    {z : projectiveSL n K} (hzX : z ∈ centralizer (X : Set (projectiveSL n K)))
    (hz : IsPGroup 2 (zpowers z)) :
    ∀ w ∈ CFSG.oddCore (centralizer (X : Set (projectiveSL n K))),
      Commute (w : projectiveSL n K) z := by
  obtain ⟨e, he⟩ := hz ⟨z, mem_zpowers z⟩
  have hze : z ^ 2 ^ e = 1 := by
    have h1 := congrArg Subtype.val he
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
  exact commute_oddCore_centralizer_of_pow_eq_one hK hXc hXodd hzX hze

theorem commute_oddCore_centralizer_of_mulEquiv [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {L : Type*} [Group L] (φ : L ≃* projectiveSL n K) {X : Subgroup L} (hXc : IsCyclic X)
    (hXodd : Odd (Nat.card X)) {z : L} (hzX : z ∈ centralizer (X : Set L))
    (hz : IsPGroup 2 (zpowers z)) :
    ∀ w ∈ CFSG.oddCore (centralizer (X : Set L)), Commute (w : L) z := by
  have : Finite L := Finite.of_equiv _ φ.symm.toEquiv
  obtain ⟨e, he⟩ := hz ⟨z, mem_zpowers z⟩
  have hze : z ^ 2 ^ e = 1 := by
    have h1 := congrArg Subtype.val he
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
  set X' := X.map φ.toMonoidHom with hX'def
  have hcen : ∀ c ∈ centralizer (X : Set L), φ c ∈ centralizer (X' : Set (projectiveSL n K)) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    rintro _ ⟨y, hy, rfl⟩
    change φ y * φ c = φ c * φ y
    rw [← map_mul, ← map_mul, hc y hy]
  have hcen' : ∀ c ∈ centralizer (X' : Set (projectiveSL n K)),
      φ.symm c ∈ centralizer (X : Set L) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have h1 := hc (φ y) ⟨y, hy, rfl⟩
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h1
  let ψ : centralizer (X : Set L) ≃* centralizer (X' : Set (projectiveSL n K)) :=
    { toFun := fun c => ⟨φ (c : L), hcen (c : L) c.2⟩
      invFun := fun c => ⟨φ.symm (c : projectiveSL n K), hcen' (c : projectiveSL n K) c.2⟩
      left_inv := fun c => Subtype.ext (φ.symm_apply_apply (c : L))
      right_inv := fun c => Subtype.ext (φ.apply_symm_apply (c : projectiveSL n K))
      map_mul' := fun c d => Subtype.ext (map_mul φ (c : L) (d : L)) }
  have hXc' : IsCyclic X' :=
    isCyclic_of_surjective (X.equivMapOfInjective φ.toMonoidHom φ.injective).toMonoidHom
      (X.equivMapOfInjective φ.toMonoidHom φ.injective).surjective
  have hXodd' : Odd (Nat.card X') := by
    rw [hX'def, Subgroup.card_map_of_injective φ.injective]
    exact hXodd
  have hze' : (φ z) ^ 2 ^ e = 1 := by rw [← map_pow, hze, map_one]
  intro w hw
  have hw' : ψ w ∈ CFSG.oddCore (centralizer (X' : Set (projectiveSL n K))) :=
    map_oddCore_le_oddCore_of_mulEquiv ψ ⟨w, hw, rfl⟩
  have h1 := commute_oddCore_centralizer_of_pow_eq_one hK hXc' hXodd' (hcen z hzX) hze' (ψ w) hw'
  apply φ.injective
  rw [map_mul, map_mul]
  exact h1

theorem map_oddCore_inf_centralizer_le_centralizer [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {G : Type*} [Group G] {L : Subgroup G} (φ : L ≃* projectiveSL n K) {X : Subgroup G}
    (hXL : X ≤ L) (hXc : IsCyclic X) (hXodd : Odd (Nat.card X)) {z : G} (hzL : z ∈ L)
    (hzX : z ∈ centralizer (X : Set G)) (hz : IsPGroup 2 (zpowers z)) :
    (CFSG.oddCore (L ⊓ centralizer (X : Set G) : Subgroup G)).map
      (L ⊓ centralizer (X : Set G)).subtype ≤ centralizer ({z} : Set G) := by
  have : Finite L := Finite.of_equiv _ φ.symm.toEquiv
  set X₀ := X.subgroupOf L with hX₀def
  have hfwd : ∀ c ∈ centralizer (X₀ : Set L), (c : G) ∈ L ⊓ centralizer (X : Set G) := by
    intro c hc
    refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have h1 := hc ⟨y, hXL hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
    exact congrArg Subtype.val h1
  have hbwd : ∀ (d : G) (hd : d ∈ L ⊓ centralizer (X : Set G)),
      (⟨d, (Subgroup.mem_inf.mp hd).1⟩ : L) ∈ centralizer (X₀ : Set L) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hd.2 (y : G) (Subgroup.mem_subgroupOf.mp hy)
  let ψ : (L ⊓ centralizer (X : Set G) : Subgroup G) ≃* centralizer (X₀ : Set L) :=
    { toFun := fun d => ⟨⟨(d : G), d.2.1⟩, hbwd (d : G) d.2⟩
      invFun := fun c => ⟨((c : L) : G), hfwd (c : L) c.2⟩
      left_inv := fun d => rfl
      right_inv := fun c => rfl
      map_mul' := fun c d => rfl }
  have hXc₀ : IsCyclic X₀ :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hXL).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXL).symm.surjective
  have hXodd₀ : Odd (Nat.card X₀) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv]
    exact hXodd
  have hzX₀ : (⟨z, hzL⟩ : L) ∈ centralizer (X₀ : Set L) := hbwd z ⟨hzL, hzX⟩
  have hz₀ : IsPGroup 2 (zpowers (⟨z, hzL⟩ : L)) := by
    intro g
    obtain ⟨e, he⟩ := hz ⟨z, mem_zpowers z⟩
    have hze : z ^ 2 ^ e = 1 := by
      have h1 := congrArg Subtype.val he
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨e, Subtype.ext (Subtype.ext ?_)⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one, ← hj, Subgroup.coe_zpow]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hze, one_zpow]
  have : Finite (L ⊓ centralizer (X : Set G) : Subgroup G) := Finite.of_equiv _ ψ.symm.toEquiv
  rintro _ ⟨w, hw, rfl⟩
  have hw' : ψ w ∈ CFSG.oddCore (centralizer (X₀ : Set L)) :=
    map_oddCore_le_oddCore_of_mulEquiv ψ ⟨w, hw, rfl⟩
  have h1 := commute_oddCore_centralizer_of_mulEquiv hK φ hXc₀ hXodd₀ hzX₀ hz₀ (ψ w) hw'
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val h1

end Projective

end CFSG.SeitzReduction.LinearPilot
