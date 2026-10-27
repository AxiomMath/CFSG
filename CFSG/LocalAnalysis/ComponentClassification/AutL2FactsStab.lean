module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup
open scoped commutatorElement

universe u

variable {F : Type u} [Field F]

theorem inl_tor (μ : Fˣ) :
    (SemidirectProduct.inl (tor F μ) : PGammaL2 F) = nm F μ false 1 :=
  SemidirectProduct.ext (by simp) rfl

theorem commute_tor_neg_one_iff (h2 : (2 : F) ≠ 0) (x : PGammaL2 F) :
    x * SemidirectProduct.inl (tor F (-1)) = SemidirectProduct.inl (tor F (-1)) * x ↔
      ∃ a ε, x = nm F a ε x.right := by
  constructor
  · intro h
    have hne : (-1 : Fˣ) ≠ 1 := by
      intro h1
      apply h2
      have := congrArg (fun u : Fˣ => (u : F)) h1
      simp only [Units.val_neg, Units.val_one] at this
      linear_combination -this
    refine exists_nm_of_conj_tor x hne (ν := -1) ?_
    rw [h, mul_inv_cancel_right]
  · rintro ⟨a, ε, hx⟩
    rw [hx, inl_tor, nm_commute_tor_iff]
    cases ε <;> simp

theorem commutator_nm (a b : Fˣ) (ε ε' : Bool) (σ τ : F ≃+* F) :
    ∃ c : Fˣ, nm F a ε σ * nm F b ε' τ * (nm F a ε σ)⁻¹ * (nm F b ε' τ)⁻¹ =
      nm F c false (σ * τ * σ⁻¹ * τ⁻¹) := by
  rw [nm_inv, nm_inv, nm_mul, nm_mul, nm_mul]
  have hx : (ε ^^ ε' ^^ ε ^^ ε') = false := by cases ε <;> cases ε' <;> rfl
  rw [hx]
  exact ⟨_, rfl⟩

variable (F)

abbrev torusRange : Subgroup (PGammaL2 F) :=
  ((SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp (tor F)).range

variable {F}

theorem isSolvable_centralizer_tor_neg_one [Finite F] (h2 : (2 : F) ≠ 0) :
    Group.IsSolvable (centralizer ({SemidirectProduct.inl (tor F (-1))} : Set (PGammaL2 F))) := by
  set C := centralizer ({SemidirectProduct.inl (tor F (-1))} : Set (PGammaL2 F))
  have hmem : ∀ x : C, ∃ a ε, (x : PGammaL2 F) = nm F a ε (x : PGammaL2 F).right := by
    intro x
    apply (commute_tor_neg_one_iff h2 _).mp
    have := mem_centralizer_iff.mp x.2 _ (Set.mem_singleton _)
    exact this.symm
  have hcomm : ∀ σ τ : F ≃+* F, σ * τ = τ * σ := fun σ τ => by
    have := isCyclic_ringAut F
    exact IsCyclic.commGroup.mul_comm σ τ
  let A : Subgroup C := (torusRange F).subgroupOf C
  have hA : ∀ x y : C, x ∈ A → y ∈ A → x * y = y * x := by
    intro x y hx hy
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    apply Subtype.ext
    change (x : PGammaL2 F) * y = y * x
    simp only [Subgroup.coe_subtype] at hc hd
    rw [← hc, ← hd, ← map_mul, ← map_mul, mul_comm]
  have hD1 : derivedSeries C 1 ≤ A := by
    rw [derivedSeries_one, _root_.commutator_def, commutator_le]
    intro x _ y _
    obtain ⟨a, ε, hx⟩ := hmem x
    obtain ⟨b, ε', hy⟩ := hmem y
    obtain ⟨c, hc⟩ := commutator_nm a b ε ε' (x : PGammaL2 F).right (y : PGammaL2 F).right
    have hr : (x : PGammaL2 F).right * (y : PGammaL2 F).right * (x : PGammaL2 F).right⁻¹ *
        (y : PGammaL2 F).right⁻¹ = 1 := by
      rw [hcomm (x : PGammaL2 F).right, mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
    have key : (x : PGammaL2 F) * y * (x : PGammaL2 F)⁻¹ * (y : PGammaL2 F)⁻¹ = nm F c false 1 := by
      rw [← hx, ← hy, hr] at hc
      exact hc
    change ((⁅x, y⁆ : C) : PGammaL2 F) ∈ torusRange F
    rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_inv, key]
    exact ⟨c, by rw [MonoidHom.comp_apply, inl_tor]⟩
  refine ⟨⟨2, ?_⟩⟩
  rw [derivedSeries_succ, eq_bot_iff, commutator_le]
  intro x hx y hy
  rw [mem_bot, commutatorElement_def, hA x y (hD1 hx) (hD1 hy), mul_inv_cancel_right,
    mul_inv_cancel]

theorem card_centralizer_tor_neg_one [Finite F] (h2 : (2 : F) ≠ 0) :
    Nat.card (centralizer ({SemidirectProduct.inl (tor F (-1))} : Set (PGammaL2 F))) =
      Nat.card Fˣ * 2 * Nat.card (F ≃+* F) := by
  set C := centralizer ({SemidirectProduct.inl (tor F (-1))} : Set (PGammaL2 F))
  have hmem : ∀ a ε σ, nm F a ε σ ∈ C := by
    intro a ε σ
    rw [mem_centralizer_iff]
    rintro _ rfl
    exact ((commute_tor_neg_one_iff h2 _).mpr ⟨a, ε, rfl⟩).symm
  let g : Fˣ × Bool × (F ≃+* F) → C := fun x => ⟨nm F x.1 x.2.1 x.2.2, hmem _ _ _⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨a, ε, σ⟩ ⟨b, ε', τ⟩ h
      obtain ⟨h1, h2, h3⟩ := nm_injective (congrArg Subtype.val h)
      simp only at h1 h2 h3
      rw [h1, h2, h3]
    · intro x
      have hx := mem_centralizer_iff.mp x.2 _ (Set.mem_singleton _)
      obtain ⟨a, ε, hx'⟩ := (commute_tor_neg_one_iff h2 _).mp hx.symm
      exact ⟨⟨a, ε, (x : PGammaL2 F).right⟩, Subtype.ext hx'.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective g hg), Nat.card_prod, Nat.card_prod,
    show Nat.card Bool = 2 by simp, mul_assoc]

theorem exists_psl2_tor_neg_one [Finite F] (hsq : IsSquare (-1 : F)) :
    ∃ z : PSL2 F, incl F z = SemidirectProduct.inl (tor F (-1)) := by
  have hmem : tor F (-1) ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
      (R := F)).range := by
    change Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F (-1)) ∈ _
    rw [pgl2_mk_mem_psl2_range_iff_det_isSquare]
    convert hsq using 1
    simp [pGammaL2FullSplitTorusGL]
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, by rw [incl_apply, hz]⟩

theorem map_conj_centralizer {G : Type*} [Group G] (k x : G) :
    (centralizer ({x} : Set G)).map (MulAut.conj k).toMonoidHom =
      centralizer ({k * x * k⁻¹} : Set G) := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq, MulAut.conj_symm_apply]
  constructor
  · intro h
    have h' : k * (x * (k⁻¹ * y * k)) * k⁻¹ = k * ((k⁻¹ * y * k) * x) * k⁻¹ := by rw [h]
    simp only [mul_assoc, mul_inv_cancel_left] at h'
    calc k * x * k⁻¹ * y = k * (x * (k⁻¹ * (y * (k * k⁻¹)))) := by group
      _ = y * (k * (x * k⁻¹)) := h'
      _ = y * (k * x * k⁻¹) := by group
  · intro h
    calc x * (k⁻¹ * y * k) = k⁻¹ * (k * x * k⁻¹ * y) * k := by group
      _ = k⁻¹ * (y * (k * x * k⁻¹)) * k := by rw [h]
      _ = k⁻¹ * y * k * x := by group

@[expose] def centralizerConjEquiv {G : Type*} [Group G] (k x : G) :
    centralizer ({x} : Set G) ≃* centralizer ({k * x * k⁻¹} : Set G) :=
  ((MulAut.conj k).subgroupMap _).trans (MulEquiv.subgroupCongr (map_conj_centralizer k x))

theorem map_stabilizer_eq {Y : Type*} [Group Y] [Finite F] (e : Y ≃* PSL2 F) (y : Y) :
    (MulAction.stabilizer (MulAut Y) y).map (autEquiv e).toMonoidHom =
      centralizer ({incl F (e y)} : Set (PGammaL2 F)) := by
  ext g
  rw [Subgroup.mem_map_equiv, MulAction.mem_stabilizer_iff, MulAut.smul_def,
    apply_eq_iff_commute e, MulEquiv.apply_symm_apply, mem_centralizer_iff]
  constructor
  · rintro h _ rfl
    exact h.symm
  · intro h
    exact (h _ rfl).symm

@[expose] def stabilizerEquiv {Y : Type*} [Group Y] [Finite F] (e : Y ≃* PSL2 F) (y : Y) :
    MulAction.stabilizer (MulAut Y) y ≃* centralizer ({incl F (e y)} : Set (PGammaL2 F)) :=
  ((autEquiv e).subgroupMap _).trans (MulEquiv.subgroupCongr (map_stabilizer_eq e y))

theorem two_ne_zero_of_isOddPrimePower [Finite F] (hodd : IsOddPrimePower (Nat.card F)) :
    (2 : F) ≠ 0 := by
  obtain ⟨p, n, hp, hpodd, -, hcard⟩ := hodd
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = p ^ n := by rw [← Nat.card_eq_fintype_card, hcard]
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow hc
  intro h
  have h2p : p ∣ 2 := by
    rw [← CharP.cast_eq_zero_iff F p]
    exact_mod_cast h
  have := Nat.le_of_dvd (by norm_num) h2p
  have := hp.two_le
  have hp2 : p = 2 := by omega
  rw [hp2] at hpodd
  exact absurd hpodd (by decide)

theorem tor_neg_one_ne_one (h2 : (2 : F) ≠ 0) : tor F (-1) ≠ 1 := by
  intro h
  have h1 := pGammaL2FullSplitTorus_injective F (h.trans (map_one _).symm)
  apply h2
  have := congrArg (fun u : Fˣ => (u : F)) h1
  simp only [Units.val_neg, Units.val_one] at this
  linear_combination -this

theorem nonempty_stabilizer_equiv {Y : Type*} [Group Y] [Finite F] (e : Y ≃* PSL2 F)
    (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F)) (t : Y)
    (ht : orderOf t = 2) :
    Nonempty (MulAction.stabilizer (MulAut Y) t ≃*
      centralizer ({SemidirectProduct.inl (tor F (-1))} : Set (PGammaL2 F))) := by
  obtain ⟨z, hz⟩ := exists_psl2_tor_neg_one hsq
  have h2 := two_ne_zero_of_isOddPrimePower hodd
  have hz2 : BenderSuzuki.PFAppendixIII.IsInvolution z := by
    refine ⟨fun h1 => tor_neg_one_ne_one h2 ?_, ?_⟩
    · have : incl F z = 1 := by rw [h1, map_one]
      rw [hz] at this
      exact SemidirectProduct.inl_injective (this.trans (map_one _).symm)
    · apply incl_injective F
      rw [map_pow, hz, ← map_pow, ← map_pow, neg_one_sq, map_one, map_one, map_one]
  have ht2 : BenderSuzuki.PFAppendixIII.IsInvolution (e t) := by
    have hord : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq, ht]
    refine ⟨fun h1 => ?_, by have := pow_orderOf_eq_one (e t); rwa [hord] at this⟩
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F hodd (e t) z ht2 hz2
  have hconj : incl F g * incl F (e t) * (incl F g)⁻¹ = SemidirectProduct.inl (tor F (-1)) := by
    rw [← map_inv, ← map_mul, ← map_mul, hg, hz]
  exact ⟨(stabilizerEquiv e t).trans ((centralizerConjEquiv (incl F g) (incl F (e t))).trans
    (MulEquiv.subgroupCongr (by rw [hconj])))⟩

theorem isSquare_neg_one_of_card_sq [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ (2 * f)) : IsSquare (-1 : F) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hF, pow_mul']
  obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := f)
  rw [hk, show (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 by ring]
  omega

theorem autL2Stab_conclusions {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hY : Blueprint.LieModel Y .PSL 2 p (2 * f)) (t : Y)
    (ht : orderOf t = 2) :
    Group.IsSolvable ↥(MulAction.stabilizer (MulAut Y) t) ∧
      (p ^ f = 3 → IsPGroup 2 ↥(MulAction.stabilizer (MulAut Y) t)) := by
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hodd := isOddPrimePower_of hp hp2 (by omega : 1 ≤ 2 * f) hF
  obtain ⟨φ⟩ := nonempty_stabilizer_equiv e hodd (isSquare_neg_one_of_card_sq hp hp2 hF) t ht
  have h2 := two_ne_zero_of_isOddPrimePower hodd
  refine ⟨?_, fun h3 => ?_⟩
  · have := isSolvable_centralizer_tor_neg_one h2
    exact Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  · have hp3 : p = 3 := by
      have hdvd : p ∣ 3 := h3 ▸ dvd_pow_self p (by omega)
      exact (Nat.prime_three.eq_one_or_self_of_dvd p hdvd).resolve_left hp.one_lt.ne'
    subst hp3
    have hf1 : f = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h3)
    subst hf1
    apply IsPGroup.of_card (n := 5)
    rw [Nat.card_congr φ.toEquiv, card_centralizer_tor_neg_one h2, Nat.card_units, hF,
      card_ringAut F Nat.prime_three hF]
    norm_num

end CFSG.ComponentClassification.AutL2Facts
