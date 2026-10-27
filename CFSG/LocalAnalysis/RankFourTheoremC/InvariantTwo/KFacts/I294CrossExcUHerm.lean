module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBlock

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace CrossExcU

open CFSG.LocalAnalysis.ComponentInitial Subgroup

section Perp

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K} {V : Type} [AddCommGroup V]
  [Module K V] (B : V →ₛₗ[h.bar] V →ₗ[K] K)

@[expose] def hermPerp (W : Submodule K V) : Submodule K V where
  carrier := {y | ∀ w ∈ W, B w y = 0}
  add_mem' ha hb w hw := by simp [map_add, ha w hw, hb w hw]
  zero_mem' w hw := by simp
  smul_mem' c y hy w hw := by simp [map_smul, hy w hw]

theorem mem_hermPerp {W : Submodule K V} {y : V} : y ∈ hermPerp B W ↔ ∀ w ∈ W, B w y = 0 :=
  Iff.rfl

@[expose] def HermNondeg (W : Submodule K V) : Prop :=
  ∀ w ∈ W, (∀ w' ∈ W, B w w' = 0) → w = 0

variable {B}

theorem hermPerp_comm (hB : B.IsSymm) {W : Submodule K V} {y : V} :
    y ∈ hermPerp B W ↔ ∀ w ∈ W, B y w = 0 :=
  ⟨fun hy w hw => hB.eq_iff.1 (hy w hw), fun hy w hw => hB.eq_iff.1 (hy w hw)⟩

theorem hermNondeg_bot : HermNondeg B (⊥ : Submodule K V) := fun w hw _ =>
  (Submodule.mem_bot K).1 hw

theorem hermNondeg_disjoint (hB : B.IsSymm) {W : Submodule K V} (hW : HermNondeg B W) :
    Disjoint W (hermPerp B W) := by
  rw [Submodule.disjoint_def]
  intro w hw hwp
  exact hW w hw fun w' hw' => (hermPerp_comm hB).1 hwp w' hw'

variable [FiniteDimensional K V]

theorem hermNondeg_isCompl (hB : B.IsSymm) {W : Submodule K V} (hW : HermNondeg B W) :
    IsCompl W (hermPerp B W) := by
  have hB' : (B.domRestrict₁₂ W W).IsSymm := hB.domRestrict W
  have hBl' : (B.domRestrict₁₂ W W).SeparatingLeft := fun w hw =>
    Subtype.ext (hW w w.2 fun w' hw' => hw ⟨w', hw'⟩)
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hB' hBl'
  refine ⟨hermNondeg_disjoint hB hW, ?_⟩
  rw [codisjoint_iff, eq_top_iff]
  intro y _
  let π : V := ∑ i, B (e i : V) y • (e i : V)
  have hπ : π ∈ W := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (e i).2
  have hyπ : y - π ∈ hermPerp B W := by
    intro w hw
    have hw' : w = ∑ j, (e.repr ⟨w, hw⟩ j) • (e j : V) := by
      have h1 := congrArg (fun z : W => (z : V)) (e.sum_repr ⟨w, hw⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
      exact h1.symm
    have hej : ∀ j, B (e j : V) (y - π) = 0 := by
      intro j
      rw [map_sub, sub_eq_zero]
      simp only [π, map_sum, map_smul, smul_eq_mul]
      have hj := fun i => he j i
      simp only [LinearMap.domRestrict₁₂_apply] at hj
      simp [hj]
    rw [hw', map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smulₛₗ, LinearMap.smul_apply, hej j, smul_zero]
  have : y = π + (y - π) := by abel
  rw [this]
  exact Submodule.add_mem_sup hπ hyπ

theorem hermNondeg_perp (hB : B.IsSymm) (hBl : B.SeparatingLeft) {W : Submodule K V}
    (hW : HermNondeg B W) : HermNondeg B (hermPerp B W) := by
  intro z hz hzz
  have hc := hermNondeg_isCompl hB hW
  apply hBl
  intro v
  have hv : v ∈ W ⊔ hermPerp B W := by rw [hc.sup_eq_top]; trivial
  obtain ⟨w, hw, z', hz', rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, hzz z' hz', (hermPerp_comm hB).1 hz w hw, add_zero]

theorem hermNondeg_sup (hB : B.IsSymm) {W₁ W₂ : Submodule K V} (h₁ : HermNondeg B W₁)
    (h₂ : HermNondeg B W₂) (hperp : W₂ ≤ hermPerp B W₁) : HermNondeg B (W₁ ⊔ W₂) := by
  intro x hx hxx
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.1 hx
  have h21 : ∀ a ∈ W₁, B w₂ a = 0 := fun a ha => (hermPerp_comm hB).1 (hperp hw₂) a ha
  have h12 : ∀ a ∈ W₂, B w₁ a = 0 := fun a ha => hperp ha w₁ hw₁
  have e1 : w₁ = 0 := h₁ w₁ hw₁ fun a ha => by
    have := hxx a (Submodule.mem_sup_left ha)
    rwa [map_add, LinearMap.add_apply, h21 a ha, add_zero] at this
  have e2 : w₂ = 0 := h₂ w₂ hw₂ fun a ha => by
    have := hxx a (Submodule.mem_sup_right ha)
    rwa [map_add, LinearMap.add_apply, h12 a ha, zero_add] at this
  rw [e1, e2, add_zero]

theorem exists_anisotropic (hB : B.IsSymm) {Z : Submodule K V} (hZ : HermNondeg B Z)
    (hZ0 : Z ≠ ⊥) : ∃ y ∈ Z, B y y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have hB' : (B.domRestrict₁₂ Z Z).IsSymm := hB.domRestrict Z
  have hiso : ∀ y : Z, (B.domRestrict₁₂ Z Z) y y = 0 := fun y => hcon y y.2
  have hpol := sesq_eq_zero_of_forall_isotropic hB' hc₀ LinearMap.id hiso
  obtain ⟨z, hzZ, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ0
  exact hz0 (hZ z hzZ fun w' hw' => hpol ⟨z, hzZ⟩ ⟨w', hw'⟩)

end Perp

section Adjoint

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K} {V : Type} [AddCommGroup V]
  [Module K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K}

structure HermOddData (B : V →ₛₗ[h.bar] V →ₗ[K] K) (u : Module.End K V) (p s : ℕ) : Prop where
  pow_eq : u ^ p = 1
  isom : ∀ x y, B (u x) (u y) = B x y
  dvd : p ∣ ℓ ^ s + 1
  bar_eq : ∀ a : K, a ^ (ℓ ^ s) = h.bar a

variable {u : Module.End K V} {p s : ℕ}

theorem HermOddData.adjoint_gen (hd : HermOddData B u p s) (hp : 0 < p) (x y : V) :
    B (u x) y = B x ((u ^ (p - 1)) y) := by
  have h1 : u (((u ^ (p - 1)) y)) = y := by
    rw [← Module.End.mul_apply, ← pow_succ' u (p - 1), Nat.sub_add_cancel hp, hd.pow_eq]
    rfl
  conv_lhs => rw [← h1]
  exact hd.isom x _

theorem HermOddData.adjoint_pow (hd : HermOddData B u p s) (hp : 0 < p) (k : ℕ) (x y : V) :
    B ((u ^ k) x) y = B x (((u ^ (p - 1)) ^ k) y) := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, hd.adjoint_gen hp, ih, pow_succ, Module.End.mul_apply]

@[expose] noncomputable def hermAdjPoly (h : UnitaryFieldData ℓ f K) (p : ℕ) :
    Polynomial K →+* Polynomial K :=
  Polynomial.eval₂RingHom (Polynomial.C.comp h.bar) (Polynomial.X ^ (p - 1))

theorem hermAdjPoly_monomial (h : UnitaryFieldData ℓ f K) (p k : ℕ) (a : K) :
    hermAdjPoly h p (Polynomial.monomial k a) =
      Polynomial.monomial ((p - 1) * k) (h.bar a) := by
  rw [hermAdjPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, ← pow_mul,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  rfl

theorem aeval_monomial_apply (u : Module.End K V) (k : ℕ) (a : K) (x : V) :
    Polynomial.aeval u (Polynomial.monomial k a) x = a • (u ^ k) x := by
  rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]

theorem HermOddData.adjoint_poly (hd : HermOddData B u p s) (hp : 0 < p) (g : Polynomial K)
    (x y : V) : B (Polynomial.aeval u g x) y = B x (Polynomial.aeval u (hermAdjPoly h p g) y) := by
  induction g using Polynomial.induction_on' with
  | add g₁ g₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | monomial k a =>
    rw [aeval_monomial_apply, hermAdjPoly_monomial, aeval_monomial_apply, map_smulₛₗ,
      LinearMap.smul_apply, hd.adjoint_pow hp, map_smul, smul_eq_mul, smul_eq_mul, pow_mul]

theorem HermOddData.aeval_adj_eq (hd : HermOddData B u p s) (hp : 0 < p) (g : Polynomial K) :
    Polynomial.aeval u (hermAdjPoly h p g) = (Polynomial.aeval u g) ^ (ℓ ^ s) := by
  haveI : CharP K ℓ := h.charP
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  let Fr : Polynomial K →+* Polynomial K := iterateFrobenius (Polynomial K) ℓ s
  let I : Ideal (Polynomial K) := Ideal.span {Polynomial.X ^ p - 1}
  let π : Polynomial K →+* Polynomial K ⧸ I := Ideal.Quotient.mk I
  have hXp : π (Polynomial.X ^ p) = 1 := by
    rw [← map_one π, Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨t, ht⟩ := hd.dvd
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by
    have : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0, mul_zero] at ht
        omega
      · exact h0
    omega⟩
  rw [Nat.mul_succ] at ht
  have hN : ℓ ^ s = p * t' + (p - 1) := by omega
  have hcomp : π.comp Fr = π.comp (hermAdjPoly h p) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Fr, iterateFrobenius_def, ← Polynomial.C_pow, hd.bar_eq]
      congr 1
      simp [hermAdjPoly]
    · simp only [RingHom.comp_apply, Fr, iterateFrobenius_def, hermAdjPoly,
        Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, hN, pow_add, pow_mul, map_mul, map_pow, hXp, one_pow, one_mul]
  have hg := congrArg (fun F => F g) hcomp
  simp only [RingHom.comp_apply, Fr, iterateFrobenius_def] at hg
  have hdvd : (Polynomial.X ^ p - 1) ∣ g ^ (ℓ ^ s) - hermAdjPoly h p g := by
    rw [← Ideal.mem_span_singleton]
    exact Ideal.Quotient.eq.1 hg
  obtain ⟨c, hc⟩ := hdvd
  have h0 : Polynomial.aeval u (g ^ (ℓ ^ s) - hermAdjPoly h p g) = 0 := by
    have hpu : Polynomial.aeval u (Polynomial.X ^ p - 1 : Polynomial K) = 0 := by
      simp [hd.pow_eq]
    rw [hc, map_mul, hpu, zero_mul]
  rw [map_sub, sub_eq_zero, map_pow] at h0
  exact h0.symm

theorem HermOddData.adjoint_aeval (hd : HermOddData B u p s) (hp : 0 < p) (g : Polynomial K)
    (x y : V) :
    B (Polynomial.aeval u g x) y = B x (((Polynomial.aeval u g) ^ (ℓ ^ s)) y) := by
  rw [hd.adjoint_poly hp, hd.aeval_adj_eq hp]

theorem HermOddData.adjoint_aeval' (hB : B.IsSymm) (hd : HermOddData B u p s) (hp : 0 < p)
    (g : Polynomial K) (x y : V) :
    B x (Polynomial.aeval u g y) = B (((Polynomial.aeval u g) ^ (ℓ ^ s)) x) y := by
  have h1 : B (Polynomial.aeval u g y) x = B y (((Polynomial.aeval u g) ^ (ℓ ^ s)) x) :=
    hd.adjoint_aeval hp g y x
  calc B x (Polynomial.aeval u g y) = h.bar (B (Polynomial.aeval u g y) x) := (hB.eq _ _).symm
    _ = h.bar (B y (((Polynomial.aeval u g) ^ (ℓ ^ s)) x)) := by rw [h1]
    _ = B (((Polynomial.aeval u g) ^ (ℓ ^ s)) x) y := hB.eq _ _

theorem HermOddData.orthogonal_ker (hB : B.IsSymm) (hd : HermOddData B u p s) (hp : 0 < p)
    {a b : Polynomial K} (hab : IsCoprime a b) {x y : V} (hx : Polynomial.aeval u a x = 0)
    (hy : Polynomial.aeval u b y = 0) : B x y = 0 := by
  obtain ⟨α, β, hαβ⟩ := hab
  have hy' : Polynomial.aeval u (α * a) y = y := by
    have h1 : Polynomial.aeval u (α * a + β * b) y = y := by rw [hαβ]; simp
    simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, hy, map_zero,
      add_zero] at h1
    rwa [map_mul, Module.End.mul_apply]
  have hN1 : 1 ≤ ℓ ^ s := Nat.one_le_pow _ _ h.prime.pos
  have hxa : ((Polynomial.aeval u (α * a)) ^ (ℓ ^ s)) x = 0 := by
    have hpoly : (α * a) ^ (ℓ ^ s) = (α ^ (ℓ ^ s) * a ^ (ℓ ^ s - 1)) * a := by
      rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hN1]
    rw [← map_pow, hpoly, map_mul, Module.End.mul_apply, hx, map_zero]
  calc B x y = B x (Polynomial.aeval u (α * a) y) := by rw [hy']
    _ = B (((Polynomial.aeval u (α * a)) ^ (ℓ ^ s)) x) y := hd.adjoint_aeval' hB hp _ x y
    _ = 0 := by rw [hxa, map_zero, LinearMap.zero_apply]

theorem HermOddData.exists_irreducible_anisotropic (hB : B.IsSymm) (hd : HermOddData B u p s)
    (hp : 0 < p) (hp0 : (p : K) ≠ 0) {Z : Submodule K V} (hZ : ∀ x ∈ Z, u x ∈ Z) {y : V}
    (hyZ : y ∈ Z) (hy : B y y ≠ 0) :
    ∃ (g : Polynomial K) (x : V), Irreducible g ∧ g ∣ Polynomial.X ^ p - 1 ∧ x ∈ Z ∧
      B x x ≠ 0 ∧ Polynomial.aeval u g x = 0 := by
  have hP0 : (Polynomial.X ^ p - 1 : Polynomial K) ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero hp (1 : K)
  have hsq : Squarefree (Polynomial.X ^ p - 1 : Polynomial K) := by
    have hsep : (Polynomial.X ^ p - Polynomial.C (1 : K) : Polynomial K).Separable :=
      Polynomial.separable_X_pow_sub_C 1 hp0 one_ne_zero
    rw [Polynomial.C_1] at hsep
    exact hsep.squarefree
  have hPu : Polynomial.aeval u (Polynomial.X ^ p - 1 : Polynomial K) = 0 := by
    simp [hd.pow_eq]
  have key : ∀ (d : ℕ) (μ : Polynomial K), μ.natDegree = d → μ ∣ Polynomial.X ^ p - 1 →
      ∀ y ∈ Z, B y y ≠ 0 → Polynomial.aeval u μ y = 0 →
      ∃ (g : Polynomial K) (x : V), Irreducible g ∧ g ∣ Polynomial.X ^ p - 1 ∧ x ∈ Z ∧
        B x x ≠ 0 ∧ Polynomial.aeval u g x = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro μ hμd hμP y hyZ hy hμy
      have hμ0 : μ ≠ 0 := fun h0 => hP0 (zero_dvd_iff.1 (h0 ▸ hμP))
      by_cases hirr : Irreducible μ
      · exact ⟨μ, y, hirr, hμP, hyZ, hy, hμy⟩
      · have hnu : ¬ IsUnit μ := by
          intro hu
          obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.1 hu
          rw [Polynomial.aeval_C, Module.algebraMap_end_apply] at hμy
          have hy0 : y = 0 := (smul_eq_zero.1 hμy).resolve_left hc.ne_zero
          exact hy (by simp [hy0])
        obtain ⟨a, b, hab, ha, hb⟩ : ∃ a b : Polynomial K, μ = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
          by_contra hcon
          refine hirr ⟨hnu, fun a b hab => ?_⟩
          by_contra h'
          exact hcon ⟨a, b, hab, fun h'' => h' (Or.inl h''), fun h'' => h' (Or.inr h'')⟩
        have ha0 : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hμ0)
        have hb0 : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hμ0)
        have hdeg : ∀ q : Polynomial K, q ≠ 0 → ¬ IsUnit q → 0 < q.natDegree := by
          intro q hq0 hqu
          refine Nat.pos_of_ne_zero fun h0 => hqu ?_
          obtain ⟨x, hx⟩ := Polynomial.natDegree_eq_zero.1 h0
          rw [← hx] at hq0 ⊢
          exact Polynomial.isUnit_C.2
            (isUnit_iff_ne_zero.2 fun h1 => hq0 (by rw [h1, Polynomial.C_0]))
        have hda := hdeg a ha0 ha
        have hdb := hdeg b hb0 hb
        have hsum : μ.natDegree = a.natDegree + b.natDegree := by
          rw [hab, Polynomial.natDegree_mul ha0 hb0]
        have hμsq : Squarefree μ := hsq.squarefree_of_dvd hμP
        have hcop : IsCoprime a b := by
          refine IsRelPrime.isCoprime fun t hta htb => hμsq t ?_
          rw [hab]
          exact mul_dvd_mul hta htb
        obtain ⟨α, β, hαβ⟩ := hcop
        have hcop' : IsCoprime a b := ⟨α, β, hαβ⟩
        set y₁ := Polynomial.aeval u (β * b) y with hy₁def
        set y₂ := Polynomial.aeval u (α * a) y with hy₂def
        have hy12 : y = y₁ + y₂ := by
          have h1 : Polynomial.aeval u (α * a + β * b) y = y := by rw [hαβ]; simp
          rw [map_add, LinearMap.add_apply] at h1
          rw [hy₁def, hy₂def, add_comm]
          exact h1.symm
        have hy₁a : Polynomial.aeval u a y₁ = 0 := by
          rw [hy₁def, ← Module.End.mul_apply, ← map_mul,
            show a * (β * b) = β * (a * b) by ring, ← hab, map_mul, Module.End.mul_apply, hμy,
            map_zero]
        have hy₂b : Polynomial.aeval u b y₂ = 0 := by
          rw [hy₂def, ← Module.End.mul_apply, ← map_mul,
            show b * (α * a) = α * (a * b) by ring, ← hab, map_mul, Module.End.mul_apply, hμy,
            map_zero]
        have hy₁Z : y₁ ∈ Z := aeval_apply_mem hZ _ hyZ
        have hy₂Z : y₂ ∈ Z := aeval_apply_mem hZ _ hyZ
        have horth₁ : B y₁ y₂ = 0 := hd.orthogonal_ker hB hp hcop' hy₁a hy₂b
        have horth₂ : B y₂ y₁ = 0 := hd.orthogonal_ker hB hp hcop'.symm hy₂b hy₁a
        have hsplit : B y y = B y₁ y₁ + B y₂ y₂ := by
          conv_lhs => rw [hy12]
          simp only [map_add, LinearMap.add_apply, horth₁, horth₂, add_zero, zero_add]
        by_cases h1 : B y₁ y₁ = 0
        · have h2 : B y₂ y₂ ≠ 0 := by
            intro h2
            exact hy (by rw [hsplit, h1, h2, add_zero])
          exact ih b.natDegree (by omega) b rfl ((hab ▸ dvd_mul_left b a).trans hμP) y₂ hy₂Z h2
            hy₂b
        · exact ih a.natDegree (by omega) a rfl ((hab ▸ dvd_mul_right a b).trans hμP) y₁ hy₁Z h1
            hy₁a
  exact key _ (Polynomial.X ^ p - 1) rfl dvd_rfl y hyZ hy (by rw [hPu, LinearMap.zero_apply])

theorem HermOddData.exists_small_nondeg [FiniteDimensional K V] (hB : B.IsSymm)
    (hd : HermOddData B u p s) (hp : 0 < p) (hp0 : (p : K) ≠ 0) {e : ℕ}
    (hdeg : ∀ g : Polynomial K, Irreducible g → g ∣ Polynomial.X ^ p - 1 → g.natDegree ≤ e)
    {Z : Submodule K V} (hZ : ∀ x ∈ Z, u x ∈ Z) (hZnd : HermNondeg B Z) (hZ0 : Z ≠ ⊥) :
    ∃ U : Submodule K V, (∀ x ∈ U, u x ∈ U) ∧ U ≤ Z ∧ U ≠ ⊥ ∧ HermNondeg B U ∧
      Module.finrank K U ≤ e := by
  obtain ⟨y, hyZ, hy⟩ := exists_anisotropic hB hZnd hZ0
  obtain ⟨g, x, hg, hgP, hxZ, hx, hgx⟩ := hd.exists_irreducible_anisotropic hB hp hp0 hZ hyZ hy
  set d := g.natDegree with hdd
  have hdpos : 0 < d := hg.natDegree_pos
  have hg0 : g ≠ 0 := hg.ne_zero
  let gf : Fin d → V := fun i => (u ^ (i : ℕ)) x
  let U := Submodule.span K (Set.range gf)
  have hgU : ∀ i : Fin d, gf i ∈ U := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hlead : g.coeff d ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hg0
  have hrec : (u ^ d) x ∈ U := by
    have hsum : ∑ i ∈ Finset.range (d + 1), g.coeff i • (u ^ i) x = 0 := by
      have h1 := hgx
      rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply] at h1
      simpa [LinearMap.smul_apply] using h1
    rw [Finset.sum_range_succ] at hsum
    have h2 : g.coeff d • (u ^ d) x = -∑ i ∈ Finset.range d, g.coeff i • (u ^ i) x :=
      eq_neg_of_add_eq_zero_right hsum
    have h3 : (u ^ d) x = (-(g.coeff d)⁻¹) • ∑ i ∈ Finset.range d, g.coeff i • (u ^ i) x := by
      rw [neg_smul, ← smul_neg, ← h2, smul_smul, inv_mul_cancel₀ hlead, one_smul]
    rw [h3]
    refine U.smul_mem _ (U.sum_mem fun i hi => U.smul_mem _ ?_)
    exact hgU ⟨i, Finset.mem_range.1 hi⟩
  have hUinv : ∀ z ∈ U, u z ∈ U := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      have hyi : u (gf i) = (u ^ ((i : ℕ) + 1)) x := by
        simp only [gf]
        rw [pow_succ', Module.End.mul_apply]
      rw [hyi]
      by_cases hi : (i : ℕ) + 1 < d
      · exact hgU ⟨(i : ℕ) + 1, hi⟩
      · have : (i : ℕ) + 1 = d := by omega
        rw [this]
        exact hrec
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact U.add_mem ha hb
    | smul a z _ hz => rw [map_smul]; exact U.smul_mem a hz
  have hxU : x ∈ U := by simpa [gf] using hgU ⟨0, hdpos⟩
  have hUpoly : ∀ z ∈ U, ∃ c : Polynomial K, z = Polynomial.aeval u c x := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact ⟨Polynomial.X ^ (i : ℕ), by simp [gf]⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c₁, hc₁⟩ := ha
      obtain ⟨c₂, hc₂⟩ := hb
      exact ⟨c₁ + c₂, by rw [hc₁, hc₂, map_add, LinearMap.add_apply]⟩
    | smul a z _ hz =>
      obtain ⟨c, hc⟩ := hz
      exact ⟨Polynomial.C a * c, by
        rw [hc, map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]⟩
  refine ⟨U, hUinv, Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact pow_apply_mem hZ i hxZ), ?_, ?_, ?_⟩
  · intro hbot
    have : x ∈ (⊥ : Submodule K V) := hbot ▸ hxU
    have hx0 : x = 0 := (Submodule.mem_bot K).1 this
    exact hx (by simp [hx0])
  · intro z hzU hzperp
    by_contra hz0
    obtain ⟨c, rfl⟩ := hUpoly z hzU
    have hnd : ¬ g ∣ c := by
      rintro ⟨c', hc'⟩
      exact hz0 (by rw [hc', mul_comm, map_mul, Module.End.mul_apply, hgx, map_zero])
    obtain ⟨α, β, hαβ⟩ := (Irreducible.coprime_iff_not_dvd hg).2 hnd
    have hxβ : x = Polynomial.aeval u β (Polynomial.aeval u c x) := by
      have h1 : Polynomial.aeval u (α * g + β * c) x = x := by rw [hαβ]; simp
      simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, hgx, map_zero,
        zero_add] at h1
      exact h1.symm
    have hxx : B x x = 0 := by
      calc B x x = B (Polynomial.aeval u β (Polynomial.aeval u c x)) x := by rw [← hxβ]
        _ = B (Polynomial.aeval u c x) (((Polynomial.aeval u β) ^ (ℓ ^ s)) x) :=
          hd.adjoint_aeval hp β _ x
        _ = 0 := by
          refine hzperp _ ?_
          rw [← map_pow]
          exact aeval_apply_mem hUinv _ hxU
    exact hx hxx
  · calc Module.finrank K U ≤ d := by
          simpa [Set.finrank] using finrank_range_le_card (R := K) gf
      _ ≤ e := hdeg g hg hgP

end Adjoint

end CrossExcU

end CFSG.LocalAnalysis.RankFourTheoremC
