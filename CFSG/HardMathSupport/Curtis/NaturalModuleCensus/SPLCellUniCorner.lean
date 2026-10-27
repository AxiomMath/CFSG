module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellG
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUniBlock
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

open Matrix Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUni

open CFSG.HardMathSupport.Curtis.Coordinator CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

open scoped IsMulCommutative

variable {f n : ℕ} {K : Type} [Field K]

section Abstract

open scoped commutatorElement

variable {U S : Type*} [Group U] [Group S]

theorem gamma_pow_mem {Ē : Subgroup S} (γ : MulAut S) (hγE : ∀ x ∈ Ē, γ x ∈ Ē) (j : ℕ) :
    ∀ x ∈ Ē, (γ ^ j) x ∈ Ē := by
  induction j with
  | zero => intro x hx; simpa using hx
  | succ j ih =>
    intro x hx
    rw [pow_succ']
    exact hγE _ (ih x hx)

theorem gamma_inv_mem {Ē : Subgroup S} (γ : MulAut S) (hγE : ∀ x ∈ Ē, γ x ∈ Ē) {N : ℕ}
    (hγ : γ ^ N = 1) (hN : 0 < N) : ∀ x ∈ Ē, γ⁻¹ x ∈ Ē := by
  intro x hx
  have h1 : γ⁻¹ = γ ^ (N - 1) :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hN, hγ])).symm
  rw [h1]
  exact gamma_pow_mem γ hγE _ x hx

theorem injective_of_ker_central {M : Type*} [Group M] {p r k : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hrp : ¬ r ∣ p - 1) (hr2 : ¬ r ∣ p ^ 2 - 1) (hr3 : ¬ r ∣ p ^ 3 - 1) (hrne : r ≠ p)
    (π : U →* S) (Ē : Subgroup S) (hEc : IsMulCommutative Ē) (hEp : ∀ x ∈ Ē, x ^ p = 1)
    (hcard : Nat.card Ē = p ^ 4) (γ : MulAut S) (hγ : γ ^ r ^ k = 1)
    (hγE : ∀ x ∈ Ē, γ x ∈ Ē) (hnt : ∃ x ∈ Ē, γ x ≠ x)
    (γ' : MulAut U) (hγ' : ∀ e, π (γ' e) = γ (π e))
    (hker : ∀ g, π g = 1 → ∀ u, g * u = u * g)
    (hnonab : ¬ ∀ a b : U, π a ∈ Ē → π b ∈ Ē → a * b = b * a)
    (ρ : ↥(Ē.comap π) →* M) (hρ : ∀ g : ↥(Ē.comap π), π g = 1 → ρ g = 1 → g = 1) :
    Function.Injective ρ := by
  have hrk : 0 < r ^ k := pow_pos hr.pos k
  have hγiE := gamma_inv_mem γ hγE hγ hrk
  let P : Subgroup U := Ē.comap π
  let W : Subgroup Ē := (Subgroup.center P).map (π.subgroupComap Ē)
  have hWstab : ∀ (x : S) (hx : x ∈ Ē), (⟨x, hx⟩ : Ē) ∈ W → (⟨γ x, hγE x hx⟩ : Ē) ∈ W := by
    intro x hx hxW
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxW
    have hzx' : π z = x := congrArg Subtype.val hzx
    have hz'mem : γ' z ∈ P := by
      show π (γ' z) ∈ Ē
      rw [hγ']
      exact hγE _ z.2
    refine Subgroup.mem_map.mpr ⟨⟨γ' z, hz'mem⟩, ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      have hg0 : (γ'⁻¹ g : U) ∈ P := by
        show π (γ'⁻¹ (g : U)) ∈ Ē
        have h1 : π (γ'⁻¹ (g : U)) = γ⁻¹ (π g) := by
          have := hγ' (γ'⁻¹ (g : U))
          rw [MulAut.apply_inv_self] at this
          rw [this]
          simp
        rw [h1]
        exact hγiE _ g.2
      have hc := Subgroup.mem_center_iff.mp hz ⟨γ'⁻¹ g, hg0⟩
      have hc' := congrArg (fun t : P => γ' (t : U)) hc
      simp only [Subgroup.coe_mul, map_mul, MulAut.apply_inv_self] at hc'
      exact Subtype.ext hc'
    · apply Subtype.ext
      show π (γ' z) = γ x
      rw [hγ', hzx']
  have hZ : ∀ z : P, z ∈ Subgroup.center P → π z = 1 := by
    intro z hz
    rcases stable_subgroup_trivial_sub (k := k) hp hr hrp hr2 hr3 hrne Ē hEc hEp hcard γ hγ
      hγE hnt W hWstab with hW | hW
    · have : π.subgroupComap Ē z ∈ W := Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      rw [hW, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      refine hnonab fun a b ha hb => ?_
      have : (⟨π a, ha⟩ : Ē) ∈ W := by rw [hW]; trivial
      obtain ⟨z, hz, hza⟩ := Subgroup.mem_map.mp this
      have hza' : π z = π a := congrArg Subtype.val hza
      have hzb := Subgroup.mem_center_iff.mp hz ⟨b, hb⟩
      have hzb' : (b : U) * z = z * b := congrArg Subtype.val hzb
      have ht : π ((z : U)⁻¹ * a) = 1 := by rw [map_mul, map_inv, hza', inv_mul_cancel]
      have h1 := hker _ ht b
      calc a * b = z * ((z : U)⁻¹ * a) * b := by group
        _ = z * (b * ((z : U)⁻¹ * a)) := by rw [mul_assoc, ← h1]
        _ = (z * b) * ((z : U)⁻¹ * a) := by rw [mul_assoc]
        _ = (b * z) * ((z : U)⁻¹ * a) := by rw [hzb']
        _ = b * a := by group
  refine (injective_iff_map_eq_one ρ).2 fun g hg => ?_
  have hgc : g ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro e
    have hcomm : ⁅g, e⁆ = 1 := by
      refine hρ _ ?_ ?_
      · have : Commute (π (g : U)) (π (e : U)) := by
          have := hEc.is_comm.comm (⟨π g, g.2⟩ : Ē) ⟨π e, e.2⟩
          exact congrArg Subtype.val this
        have h2 : π (⁅g, e⁆ : P) = ⁅π (g : U), π (e : U)⁆ := by
          change π ⁅(g : U), (e : U)⁆ = _
          rw [map_commutatorElement]
        rw [h2]
        exact this.commutator_eq
      · rw [map_commutatorElement, hg]
        simp
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
  exact hρ g (hZ g hgc) hg

end Abstract

section Kernel

variable (h : UnitaryFieldData 2 f K)

theorem conj_eq_one_iff (hn : 3 ≤ n) (A : primeFormUnitary h (idGram K n)) :
    primeFormConjHom h (idGram K n) A = 1 ↔
      ∃ c : Kˣ, h.norm (c : K) = 1 ∧ (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := by
  have key := primeFormPsi_eq_one_iff h (isPrimeFormGram_idGram (K := K) (n := n)) hn ⟨A, 1⟩
  rw [primeFormPsi_apply, map_one, mul_one] at key
  rw [key]
  constructor
  · rintro ⟨-, c, hc, hA⟩
    exact ⟨c, hc, hA⟩
  · rintro ⟨c, hc, hA⟩
    exact ⟨rfl, c, hc, hA⟩

theorem conj_eq_one_commute (hn : 3 ≤ n) (A : primeFormUnitary h (idGram K n))
    (hA : primeFormConjHom h (idGram K n) A = 1) (u : primeFormUnitary h (idGram K n)) :
    A * u = u * A := by
  obtain ⟨c, -, hc⟩ := (conj_eq_one_iff h hn A).mp hA
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
  exact (GeneralLinearGroup.scalar_commute (n := Fin n) c (u : GL (Fin n) K))

theorem norm_eq_one_of_one (hf : f = 1) (c : Kˣ) : h.norm (c : K) = 1 := by
  have := h.finite
  refine (pow_succ_eq_one_iff_norm h c).mp ?_
  have h3 : Nat.card Kˣ = 3 := by
    rw [Nat.card_units K, h.card, hf]; norm_num
  have := pow_card_eq_one' (G := Kˣ) (x := c)
  rw [h3] at this
  rw [hf]
  simpa using this

noncomputable def scalarU (hf : f = 1) (n : ℕ) : Kˣ →* primeFormUnitary h (idGram K n) where
  toFun c := ⟨GeneralLinearGroup.scalar (Fin n) c,
    scalar_mem_primeFormUnitary_one h (norm_eq_one_of_one h hf c)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem scalarU_injective (hf : f = 1) (hn : 3 ≤ n) : Function.Injective (scalarU h hf n) := by
  intro a b hab
  have h1 := congrArg (fun A : primeFormUnitary h (idGram K n) =>
    ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) hab
  exact Units.ext (by simpa [scalarU, GeneralLinearGroup.coe_scalar] using h1)

theorem conj_scalarU (hf : f = 1) (hn : 3 ≤ n) (c : Kˣ) :
    primeFormConjHom h (idGram K n) (scalarU h hf n c) = 1 :=
  (conj_eq_one_iff h hn _).mpr ⟨c, norm_eq_one_of_one h hf c, rfl⟩

end Kernel

section CardGL

theorem card_generalLinearGroup {E W : Type*} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [Module.Finite E W] :
    Nat.card (LinearMap.GeneralLinearGroup E W) =
      ∏ i : Fin (Module.finrank E W), (Nat.card E ^ Module.finrank E W - Nat.card E ^ (i : ℕ)) := by
  classical
  have := Fintype.ofFinite E
  let b := Module.finBasisOfFinrankEq E W (rfl : Module.finrank E W = Module.finrank E W)
  let e : W ≃ₗ[E] (Fin (Module.finrank E W) → E) := b.equivFun
  have h1 : Nat.card (LinearMap.GeneralLinearGroup E W) =
      Nat.card (GL (Fin (Module.finrank E W)) E) :=
    Nat.card_congr ((LinearMap.GeneralLinearGroup.generalLinearEquiv E W).trans
      (e.autCongr.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv E
        (Fin (Module.finrank E W) → E)).symm.trans
        Matrix.GeneralLinearGroup.toLin.symm))).toEquiv
  rw [h1, Matrix.card_GL_field, Nat.card_eq_fintype_card]

theorem card_generalLinearGroup_dvd {E W : Type*} [Field E] [Finite E] [AddCommGroup W]
    [Module E W] [Module.Finite E W] (hE : Nat.card E = 4)
    (hm : Module.finrank E W = 2 ∨ Module.finrank E W = 3) :
    Nat.card (LinearMap.GeneralLinearGroup E W) ∣ 181440 := by
  rw [card_generalLinearGroup, hE]
  generalize Module.finrank E W = m at hm ⊢
  rcases hm with rfl | rfl <;> norm_num [Fin.prod_univ_succ]

end CardGL

section Block

open CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.Uni

variable (h : UnitaryFieldData 2 f K) (y : primeFormUnitary h (idGram K n))

noncomputable def blockHom (a : K[X]) :
    Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n))) →*
      blockGL ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) a :=
  (blockRestrict (toLinU h n y) a).comp
    (((toLinU h n).comp (Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n)))).subtype
      ).codRestrict (gl_centralizer (toLinU h n y)) fun g => toLinU_mem_gl_centralizer g.2)

theorem blockApply_blockHom (a : K[X])
    (g : Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n)))) (v : Fin n → K)
    (hv : v ∈ primaryComponent ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) a) :
    blockApply (blockHom h y a g) v hv =
      ((toLinU h n (g : primeFormUnitary h (idGram K n)) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) v :=
  blockApply_blockRestrict (toLinU h n y) a _ v hv

theorem blockHom_scalar_inj (a : K[X])
    (hne : primaryComponent ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) a ≠ ⊥)
    (g : Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n)))) (c : Kˣ)
    (hg : ((g : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c)
    (h1 : blockHom h y a g = 1) : (g : primeFormUnitary h (idGram K n)) = 1 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h2 := congrArg (fun γ => blockApply γ v hv) h1
  simp only [blockApply_blockHom, blockApply_one] at h2
  rw [toLinU_apply, hg] at h2
  change Matrix.mulVecLin ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) v = v at h2
  rw [GeneralLinearGroup.coe_scalar] at h2
  have h3 : (c : K) • v = v := by
    refine Eq.trans ?_ h2
    funext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hc : (c : K) = 1 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have := congrFun h3 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hi (this.trans (one_mul _).symm)
  have hc1 : c = 1 := Units.ext hc
  subst hc1
  apply Subtype.ext
  rw [hg, map_one]
  rfl

end Block

section Counting

variable (h : UnitaryFieldData 2 f K)

theorem card_comap_dvd (hf : f = 1) (hn : 3 ≤ n) {m : ℕ}
    (Ē : Subgroup (MulAut (primeFormP h (idGram K n)))) (hcard : Nat.card Ē = m)
    (hπE : ∀ x ∈ Ē, ∃ e, primeFormConjHom h (idGram K n) e = x) :
    m * 3 ∣ Nat.card ↥(Ē.comap (primeFormConjHom h (idGram K n))) := by
  have := h.finite
  set π := primeFormConjHom h (idGram K n) with hπ
  set P : Subgroup (primeFormUnitary h (idGram K n)) := Ē.comap π with hP
  let ψ : P →* Ē := π.subgroupComap Ē
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨e, he⟩ := hπE x hx
    exact ⟨⟨e, by show π e ∈ Ē; rw [he]; exact hx⟩, Subtype.ext he⟩
  have h1 : Nat.card P = Nat.card Ē * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
  let s' : Kˣ →* P := (scalarU h hf n).codRestrict P fun c => by
    show π (scalarU h hf n c) ∈ Ē
    rw [conj_scalarU h hf hn]
    exact Ē.one_mem
  have hs' : Function.Injective s' := fun a b hab =>
    scalarU_injective h hf hn (congrArg Subtype.val hab)
  have hle : s'.range ≤ ψ.ker := by
    rintro _ ⟨c, rfl⟩
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (conj_scalarU h hf hn c)
  have h3 : Nat.card s'.range = 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hs').toEquiv, Nat.card_units K, h.card, hf]
    norm_num
  have h4 : 3 ∣ Nat.card ψ.ker := h3 ▸ Subgroup.card_dvd_of_le hle
  rw [h1, hcard]
  exact Nat.mul_dvd_mul_left m h4

theorem arith_false {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : p ^ 4 * 3 ∣ N)
    (hdiv : N ∣ 181440) : False := by
  have h := hN.trans hdiv
  have hle : p ^ 4 * 3 ≤ 181440 := Nat.le_of_dvd (by norm_num) h
  have hp16 : p < 16 := by
    by_contra hcon
    push Not at hcon
    have : 16 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hcon 4
    omega
  interval_cases p <;> first | omega | (norm_num at hp)

end Counting

theorem corner_false (h : UnitaryFieldData 2 f K) (hf : f = 1) (hn : 3 ≤ n) {p r k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hrp : ¬ r ∣ p - 1) (hr2 : ¬ r ∣ p ^ 2 - 1)
    (hr3 : ¬ r ∣ p ^ 3 - 1) (hrne : r ≠ p)
    (Ē : Subgroup (MulAut (primeFormP h (idGram K n)))) (hEc : IsMulCommutative Ē)
    (hEp : ∀ x ∈ Ē, x ^ p = 1) (hcard : Nat.card Ē = p ^ 4)
    (γ : MulAut (MulAut (primeFormP h (idGram K n)))) (hγ : γ ^ r ^ k = 1)
    (hγE : ∀ x ∈ Ē, γ x ∈ Ē) (hnt : ∃ x ∈ Ē, γ x ≠ x)
    (γ' : MulAut (primeFormUnitary h (idGram K n)))
    (hγ' : ∀ e, primeFormConjHom h (idGram K n) (γ' e) =
      γ (primeFormConjHom h (idGram K n) e))
    (hπE : ∀ x ∈ Ē, ∃ e, primeFormConjHom h (idGram K n) e = x)
    (y : primeFormUnitary h (idGram K n)) (hyp : y ^ p = 1)
    (hyE : ∀ e, primeFormConjHom h (idGram K n) e ∈ Ē → y * e = e * y)
    (hsolv : Group.IsSolvable ↥(autFix (primeFormConjHom h (idGram K n) y)))
    (hnonab : ¬ ∀ a b : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) a ∈ Ē → primeFormConjHom h (idGram K n) b ∈ Ē →
        a * b = b * a) : False := by
  subst hf
  have hfin := h.finite
  set π := primeFormConjHom h (idGram K n) with hπ
  have hpK : (p : K) ≠ 0 := Uni.cast_ne_zero_of_ne_char h hp hp2
  have hyp' : (y : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) 1 := by
    rw [map_one, ← Subgroup.coe_pow, hyp]
    rfl
  have hx := Uni.squarefree_minpoly_toLinU_of_pow_scalar y hpK hyp'
  have hPC : Ē.comap π ≤ Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n))) := by
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hyE e he).symm
  by_cases hex : ∃ a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)),
      2 ≤ primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (a : K[X])
  swap
  · push Not at hex
    exact hnonab fun A B hA hB =>
      Uni.centralizer_commute_of_mult_le_one hx (fun a => by have := hex a; omega) (hPC hA)
        (hPC hB)
  obtain ⟨a, ha⟩ := hex
  have hm4 : primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X]) < 4 := by
    by_contra hcon
    exact Uni.not_isSolvable_autFix_of_mult_four hx a (by omega) hsolv
  have hdeg1 : (a : K[X]).natDegree = 1 := by
    have hpos : 0 < (a : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
    by_contra hcon
    have h2 : 2 ≤ (a : K[X]).natDegree := by omega
    have hQ : 4 ≤ 2 ^ (1 * (a : K[X]).natDegree) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (1 * (a : K[X]).natDegree) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Uni.not_isSolvable_autFix_of_good_block hx a
      (Uni.isGoodBlock_of_numeric' a ha (fun _ => hQ) (fun _ => by omega)) hsolv
  have hne := primaryComponent_ne_bot hx a.2
  have hEcard : Nat.card (AdjoinRoot (a : K[X])) = 4 := by
    have hfd : Module.finrank K (AdjoinRoot (a : K[X])) = 1 := by
      rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible (a : K[X])).ne_zero).finrank,
        AdjoinRoot.powerBasis_dim, hdeg1]
    have : Module.Finite K (AdjoinRoot (a : K[X])) :=
      (AdjoinRoot.powerBasis (Fact.out : Irreducible (a : K[X])).ne_zero).finite
    rw [Module.natCard_eq_pow_finrank (K := K), hfd, h.card]
    norm_num
  have hEfin : Finite (AdjoinRoot (a : K[X])) :=
    Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  let ρ := (blockHom h y (a : K[X])).comp (Subgroup.inclusion hPC)
  have hρinj : Function.Injective ρ := by
    refine injective_of_ker_central hp hr hrp hr2 hr3 hrne π Ē hEc hEp hcard γ hγ hγE hnt γ'
      hγ' (fun g hg u => conj_eq_one_commute h hn g hg u) hnonab ρ ?_
    intro g hg hρ1
    obtain ⟨c, -, hc⟩ := (conj_eq_one_iff h hn g).mp hg
    exact Subtype.ext (blockHom_scalar_inj h y (a : K[X]) hne ⟨g, hPC g.2⟩ c hc hρ1)
  have hdvd1 := Subgroup.card_dvd_of_injective ρ hρinj
  have hdvd2 := card_comap_dvd h rfl hn Ē hcard hπE
  have hfr : Module.finrank (AdjoinRoot (a : K[X]))
      (primaryComponent ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (a : K[X])) = 2 ∨
      Module.finrank (AdjoinRoot (a : K[X]))
        (primaryComponent ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) (a : K[X])) = 3 := by
    have h1 : 2 ≤ Module.finrank (AdjoinRoot (a : K[X]))
      (primaryComponent ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (a : K[X])) := ha
    have h2 : Module.finrank (AdjoinRoot (a : K[X]))
      (primaryComponent ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (a : K[X])) < 4 := hm4
    omega
  have hdvd3 := card_generalLinearGroup_dvd hEcard hfr
  exact arith_false hp hp2 hdvd2 (hdvd1.trans hdvd3)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUni
