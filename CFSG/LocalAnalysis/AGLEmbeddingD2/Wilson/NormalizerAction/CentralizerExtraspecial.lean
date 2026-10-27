module

public import CFSG.LinearAlgebra.ExtraspecialCyclotomicModule
public import CFSG.LinearAlgebra.BinaryReflectionNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms
public import Mathlib.Tactic.NormNum.Prime
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.IsometryScalar

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.LinearAlgebra CFSG.LocalAnalysis.ComponentInitial Module
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem pow_three_eq_one_of_dvd_odd {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (hU : finrank (ZMod 2) U = 2)
    {n : ℕ} (hn : Odd n) {u : LinearMap.GeneralLinearGroup (ZMod 2) U} (hu : orderOf u ∣ n) :
    u ^ 3 = 1 := by
  let f : LinearMap.GeneralLinearGroup (ZMod 2) U →* Equiv.Perm U :=
    { toFun := fun u => (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U u).toEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).injective
    exact LinearEquiv.toEquiv_injective hab
  have : Finite U := Module.finite_of_finite (ZMod 2)
  have hcardU : Nat.card U = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hU, Nat.card_zmod]
    norm_num
  have h24 : orderOf u ∣ 24 := by
    rw [← orderOf_injective f hf u]
    have := orderOf_dvd_natCard (f u)
    rwa [Nat.card_perm, hcardU, show Nat.factorial 4 = 24 by decide] at this
  have hcop : Nat.Coprime (orderOf u) 8 := by
    have h8 : Nat.Coprime n (2 ^ 3) := (Nat.coprime_two_right.2 hn).pow_right 3
    exact Nat.Coprime.coprime_dvd_left hu (by simpa using h8)
  have : orderOf u ∣ 3 := by
    have h' : orderOf u ∣ 8 * 3 := by simpa using h24
    exact hcop.dvd_of_dvd_mul_left h'
  exact orderOf_dvd_iff_pow_eq_one.1 this

section Operators

variable {Q : Type*} [Group Q] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) Q V} {z : Q}

theorem range_sub_id_le_centralFixed
    (hcompl : IsCompl (centralFixed ρ z) (centralImage ρ z)) {A : V →ₗ[ZMod 2] V}
    (hAU : ∀ u ∈ centralFixed ρ z, A u ∈ centralFixed ρ z)
    (hAW : ∀ w ∈ centralImage ρ z, A w = w) :
    LinearMap.range (A - LinearMap.id) ≤ centralFixed ρ z := by
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ centralFixed ρ z ⊔ centralImage ρ z := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, LinearMap.sub_apply, LinearMap.sub_apply, hAW w hw, LinearMap.id_apply,
    LinearMap.id_apply, sub_self, add_zero]
  exact (centralFixed ρ z).sub_mem (hAU u hu) hu

theorem ker_sub_id_le_centralFixed (hfield : IsField (centralImageAlgebra ρ z))
    (hcompl : IsCompl (centralFixed ρ z) (centralImage ρ z)) {A : V →ₗ[ZMod 2] V}
    (hAU : ∀ u ∈ centralFixed ρ z, A u ∈ centralFixed ρ z)
    {c : centralImageAlgebra ρ z} (hc1 : c ≠ 1)
    (hc : ∀ w : centralImage ρ z,
      (((c : Module.End (ZMod 2) (centralImage ρ z)) w : centralImage ρ z) : V) = A w) :
    LinearMap.ker (A - LinearMap.id) ≤ centralFixed ρ z := by
  intro v hv
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hv
  have hv' : v ∈ centralFixed ρ z ⊔ centralImage ρ z := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv'
  have hsub : c - 1 ≠ 0 := sub_ne_zero.2 hc1
  obtain ⟨d, hd⟩ := hfield.mul_inv_cancel hsub
  have hd' : d * (c - 1) = 1 := by rw [hfield.mul_comm]; exact hd
  have hAw : A w = (((c : Module.End (ZMod 2) (centralImage ρ z)) ⟨w, hw⟩ :
      centralImage ρ z) : V) := (hc ⟨w, hw⟩).symm
  have h1 : A u + A w = u + w := by rw [← map_add, hv]
  have hmem : A u - u ∈ centralFixed ρ z ⊓ centralImage ρ z := by
    refine Submodule.mem_inf.2 ⟨(centralFixed ρ z).sub_mem (hAU u hu) hu, ?_⟩
    have : A u - u = w - A w := by
      rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
    rw [this, hAw]
    exact (centralImage ρ z).sub_mem hw (((c : Module.End (ZMod 2) (centralImage ρ z))
      ⟨w, hw⟩ : centralImage ρ z)).2
  rw [hcompl.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem
  have hAw' : A w = w := by
    rw [hmem] at h1
    exact add_left_cancel h1
  have hcw : (c : Module.End (ZMod 2) (centralImage ρ z)) ⟨w, hw⟩ = ⟨w, hw⟩ :=
    Subtype.ext (by rw [hc ⟨w, hw⟩]; exact hAw')
  have hw0 : (⟨w, hw⟩ : centralImage ρ z) = 0 := by
    have e := congrArg (fun k : centralImageAlgebra ρ z =>
      (k : Module.End (ZMod 2) (centralImage ρ z)) ⟨w, hw⟩) hd'
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one,
      Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, hcw, sub_self, map_zero] at e
    exact e.symm
  have : w = 0 := congrArg Subtype.val hw0
  rw [this, add_zero]
  exact hu

end Operators

theorem exists_pow_eq_of_pow_eleven_eq_one {K : Type*} [Ring K] [Finite K] (hK : IsField K)
    {c d : Kˣ} (hc : c ^ 11 = 1) (hd : d ^ 11 = 1) (hd1 : d ≠ 1) : ∃ k : ℕ, d ^ k = c := by
  classical
  let _ : Field K := hK.toField
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Fintype Kˣ := Fintype.ofFinite _
  have hord : orderOf d = 11 := orderOf_eq_prime hd hd1
  set S : Finset Kˣ := Finset.univ.filter fun a => a ^ 11 = 1 with hS
  set T : Finset Kˣ := (Finset.range 11).image fun k => d ^ k with hT
  have hTS : T ⊆ S := by
    intro a ha
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 ha
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← pow_mul, mul_comm, pow_mul, hd, one_pow]
  have hTcard : T.card = 11 := by
    rw [hT, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact pow_injOn_Iio_orderOf (by rw [hord]; exact Finset.mem_range.1 hi)
      (by rw [hord]; exact Finset.mem_range.1 hj) hij
  have hScard : S.card ≤ 11 := IsCyclic.card_pow_eq_one_le (by norm_num)
  have hST : T = S := Finset.eq_of_subset_of_card_le hTS (by omega)
  have hcS : c ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hc⟩
  rw [← hST, hT, Finset.mem_image] at hcS
  obtain ⟨k, -, hk⟩ := hcS
  exact ⟨k, hk⟩

theorem orderOf_two_zmod_eleven' : orderOf (2 : ZMod 11) = 11 - 1 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide, by decide⟩

theorem centralizer_le_zpowers_of_realization {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} (hnd : (QuadraticMap.polarBilin q).Nondegenerate)
    (Λ : G →* (V ≃ₗ[ZMod 2] V)) (hΛ : Function.Injective Λ)
    (hΛq : Λ.range ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (hsmall : ∀ g ∈ Λ.range, (orderOf g = 2 ∨ orderOf g = 3) →
      3 ≤ finrank (ZMod 2) (LinearMap.range ((g : V →ₗ[ZMod 2] V) - LinearMap.id)))
    (hbig : ∀ g ∈ Λ.range, orderOf g = 3 →
      3 ≤ finrank (ZMod 2) (LinearMap.ker ((g : V →ₗ[ZMod 2] V) - LinearMap.id)))
    {Q : Subgroup G} (hodd : Odd (Nat.card (Subgroup.centralizer (Q : Set G))))
    (hQ : IsExtraspecialPGroup 11 Q) (hQc : Nat.card Q = 11 ^ 3) (hQe : Monoid.exponent Q = 11)
    {x y z : Q} (hgen : Subgroup.closure {x, y} = ⊤) (hz : z = ⁅x, y⁆)
    (hV : finrank (ZMod 2) V = 112)
    (hU : finrank (ZMod 2)
      (LinearMap.ker (((Λ z : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - 1)) = 2) :
    Subgroup.centralizer (Q : Set G) ≤ Subgroup.zpowers (z : G) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set H := Subgroup.centralizer (Q : Set G) with hH
  set ρ : Representation (ZMod 2) Q V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp (Λ.comp Q.subtype) with hρ
  have hzc : ∀ g : Q, Commute g z := by
    intro g
    have hmem : z ∈ Subgroup.center Q := by
      rw [← hQ.2.1, hz, _root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    exact ((Subgroup.mem_center_iff.1 hmem) g)
  have hz11 : z ^ 11 = 1 := by
    rw [← hQe]
    exact Monoid.pow_exponent_eq_one z
  have hρz11 : ρ z ^ 11 = 1 := by rw [← map_pow, hz11, map_one]
  obtain ⟨hcompl, hUtriv, hfield, hKcard, -, ⟨hW0, -⟩, hW, -, e, he⟩ :=
    extraspecial_prime_cyclotomic_minimal_module (p := 11) (by norm_num) orderOf_two_zmod_eleven'
      hQ hQc hQe hgen hz ρ (r := 2) (by norm_num) (by rw [hV]) hU
  have hU' : finrank (ZMod 2) (centralFixed ρ z) = 2 := hU
  have hKfin : Finite (centralImageAlgebra ρ z) :=
    Nat.finite_of_card_ne_zero (by rw [hKcard]; positivity)
  let C := Subgroup.centralizer (Set.range ρ.asGroupHom)
  have hmemC : ∀ h : H, (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm
      (Λ (h : G)) ∈ C := by
    intro h
    refine Subgroup.mem_centralizer_iff.2 ?_
    rintro _ ⟨g, rfl⟩
    apply Units.ext
    apply LinearMap.ext
    intro v
    rw [Units.val_mul, Units.val_mul, Representation.asGroupHom_apply, Module.End.mul_apply,
      Module.End.mul_apply]
    have hcomm : (g : G) * h = h * g := Subgroup.mem_centralizer_iff.1 h.2 g g.2
    have h' := congrArg (fun k : G => (Λ k) v) hcomm
    simp only [map_mul, LinearEquiv.mul_apply] at h'
    exact h'
  let ψ : H →* C := MonoidHom.codRestrict
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.toMonoidHom.comp
      (Λ.comp H.subtype)) C hmemC
  let φ : H →* LinearMap.GeneralLinearGroup (ZMod 2) (centralFixed ρ z) ×
      (centralImageAlgebra ρ z)ˣ := e.toMonoidHom.comp ψ
  have hφinj : Function.Injective φ := by
    intro h1 h2 h12
    have h' : ψ h1 = ψ h2 := e.injective h12
    apply Subtype.ext
    apply hΛ
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.injective
      (congrArg Subtype.val h')
  have hψ : ∀ (h : H) (v : V),
      (((ψ h : C) : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v =
        Λ (h : G) v := fun _ _ => rfl
  have hφU : ∀ (h : H) (u : centralFixed ρ z),
      ((((φ h).1 : LinearMap.GeneralLinearGroup (ZMod 2) (centralFixed ρ z)) :
        centralFixed ρ z →ₗ[ZMod 2] centralFixed ρ z) u : V) = Λ (h : G) u :=
    fun h u => by
      have := (he (ψ h)).1 u
      rw [hψ] at this
      exact this
  have hφW : ∀ (h : H) (w : centralImage ρ z),
      (((((φ h).2 : (centralImageAlgebra ρ z)ˣ) : centralImageAlgebra ρ z) :
        Module.End (ZMod 2) (centralImage ρ z)) w : V) = Λ (h : G) w :=
    fun h w => by
      have := (he (ψ h)).2 w
      rw [hψ] at this
      exact this
  have hu3 : ∀ h : H, ((φ h).1) ^ 3 = 1 := by
    intro h
    have h1 : orderOf ((φ h).1) ∣ orderOf (φ h) :=
      orderOf_map_dvd (MonoidHom.fst (LinearMap.GeneralLinearGroup (ZMod 2) (centralFixed ρ z))
        (centralImageAlgebra ρ z)ˣ) (φ h)
    have h2 : orderOf (φ h) ∣ orderOf h := orderOf_map_dvd φ h
    have h3 : orderOf h ∣ Nat.card H := orderOf_dvd_natCard h
    exact pow_three_eq_one_of_dvd_odd hU' hodd (h1.trans (h2.trans h3))
  have key3 : ∀ h : H, h ^ 3 = 1 → h = 1 := by
    intro h h3
    by_contra h1
    have hord : orderOf (Λ (h : G)) = 3 := by
      rw [orderOf_injective Λ hΛ, Subgroup.orderOf_coe]
      exact orderOf_eq_prime h3 h1
    have hmem : Λ (h : G) ∈ Λ.range := Λ.mem_range.2 ⟨h, rfl⟩
    have hAU : ∀ u ∈ centralFixed ρ z,
        ((Λ (h : G) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) u ∈ centralFixed ρ z := by
      intro u hu
      have := hφU h ⟨u, hu⟩
      rw [LinearEquiv.coe_coe, ← this]
      exact Subtype.coe_prop _
    by_cases hc1 : (((φ h).2 : (centralImageAlgebra ρ z)ˣ) : centralImageAlgebra ρ z) = 1
    · have hAW : ∀ w ∈ centralImage ρ z,
          ((Λ (h : G) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) w = w := by
        intro w hw
        have := hφW h ⟨w, hw⟩
        rw [hc1] at this
        rw [LinearEquiv.coe_coe, ← this]
        rfl
      have hle := range_sub_id_le_centralFixed hcompl hAU hAW
      have h3' := hsmall _ hmem (Or.inr hord)
      have := Submodule.finrank_mono hle
      omega
    · have hAW : ∀ w : centralImage ρ z,
          (((((φ h).2 : (centralImageAlgebra ρ z)ˣ) : centralImageAlgebra ρ z) :
            Module.End (ZMod 2) (centralImage ρ z)) w : V) =
          ((Λ (h : G) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) w := fun w => hφW h w
      have hle := ker_sub_id_le_centralFixed hfield hcompl hAU hc1 hAW
      have h3' := hbig _ hmem hord
      have := Submodule.finrank_mono hle
      omega
  have hc33 : ∀ g : H, ((φ g).2) ^ 33 = 1 := by
    intro g
    have hzb : ∀ v w, QuadraticMap.polarBilin q (ρ z v) (ρ z w) =
        QuadraticMap.polarBilin q v w := fun v w =>
      polar_map_of_mem_orthogonalGroup (hΛq (Λ.mem_range.2 ⟨(z : G), rfl⟩)) v w
    have hab : ∀ v w, QuadraticMap.polarBilin q ((Λ (g : G) : V ≃ₗ[ZMod 2] V) v)
        ((Λ (g : G) : V ≃ₗ[ZMod 2] V) w) = QuadraticMap.polarBilin q v w := fun v w =>
      polar_map_of_mem_orthogonalGroup (hΛq (Λ.mem_range.2 ⟨(g : G), rfl⟩)) v w
    have hcomm : (z : G) * g = g * z := Subgroup.mem_centralizer_iff.1 g.2 z z.2
    have ha : Commute (((Λ (g : G) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)) (ρ z) := by
      apply LinearMap.ext
      intro v
      have h' := congrArg (fun k : G => (Λ k) v) hcomm
      simp only [map_mul, LinearEquiv.mul_apply] at h'
      exact h'.symm
    have h := scalar_pow_thirtythree_of_isometry ρ z hρz11 hcompl
      (QuadraticMap.polarBilin q) hnd hzb
      ((Λ (g : G) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) hab
      (((φ g).2 : (centralImageAlgebra ρ z)ˣ) : centralImageAlgebra ρ z) (hφW g)
    exact Units.ext (by simpa using h)
  have hg11 : ∀ g : H, g ^ 11 = 1 := by
    intro g
    have h33 : (φ g) ^ 33 = 1 := by
      refine Prod.ext ?_ (by rw [Prod.pow_snd, hc33 g]; rfl)
      rw [Prod.pow_fst, show (33 : ℕ) = 3 * 11 by norm_num, pow_mul, hu3, one_pow]
      rfl
    apply key3
    apply hφinj
    rw [← pow_mul, map_pow, map_one]
    exact h33
  have hzH : (z : G) ∈ H := by
    refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
    exact congrArg Subtype.val (hzc ⟨k, hk⟩).eq
  set ζ : H := ⟨(z : G), hzH⟩ with hζ
  have hζ11 : ζ ^ 11 = 1 := by
    apply Subtype.ext
    have h' := congrArg Subtype.val hz11
    exact h'
  have hζU : (φ ζ).1 = 1 := by
    apply Units.ext
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    rw [hφU ζ u]
    exact hUtriv z u u.2
  have hζ2 : (φ ζ).2 ^ 11 = 1 := by
    have h : (φ ζ) ^ 11 = 1 := by rw [← map_pow, hζ11, map_one]
    simpa using congrArg Prod.snd h
  have hζ2ne : (φ ζ).2 ≠ 1 := by
    intro h1
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    have h2 := hφW ζ ⟨w, hw⟩
    rw [h1] at h2
    have hwU : w ∈ centralFixed ρ z ⊓ centralImage ρ z := by
      refine Submodule.mem_inf.2 ⟨?_, hw⟩
      simp only [centralFixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero]
      exact h2.symm
    rw [hcompl.inf_eq_bot] at hwU
    exact hwU
  intro g hg
  set g' : H := ⟨g, hg⟩ with hg'
  have h11 : (φ g') ^ 11 = 1 := by rw [← map_pow, hg11, map_one]
  have hu : (φ g').1 = 1 := by
    have h1 : (φ g').1 ^ 11 = 1 := by simpa using congrArg Prod.fst h11
    have h2 := pow_gcd_eq_one.2 ⟨h1, hu3 g'⟩
    simpa using h2
  have hc11 : (φ g').2 ^ 11 = 1 := by simpa using congrArg Prod.snd h11
  obtain ⟨k, hk⟩ := exists_pow_eq_of_pow_eleven_eq_one (K := centralImageAlgebra ρ z) hfield hc11 hζ2 hζ2ne
  have hgζ : g' = ζ ^ k := by
    apply hφinj
    rw [map_pow]
    refine Prod.ext ?_ ?_
    · rw [Prod.pow_fst, hζU, one_pow, hu]
    · rw [Prod.pow_snd, hk]
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast]
  exact (congrArg Subtype.val hgζ).symm

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
