module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryLift
public import CFSG.LieType.Steinberg.CentralExt.UnitaryGram
public import CFSG.LieType.Steinberg.CentralExt.PerfectLift
public import CFSG.LieType.Steinberg.CentralExt.UnitaryPerfect
public import CFSG.ClassicalGroups.Unitary.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis

public section

namespace CFSG.LieType.Steinberg

open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.LocalAnalysis.ComponentInitial

section Quotient

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

local notation "σ₀" => unitaryInvolution K p f

theorem pow_ne_two_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (f : ℕ) : p ^ f ≠ 2 := by
  intro h
  rcases f with _ | f
  · simp at h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (h ▸ dvd_pow_self p (Nat.succ_ne_zero f)))

theorem isPerfect_SU_three (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    Group.IsPerfect (SU σ₀ 3) := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 3
  have : Group.IsPerfect (SUid σ₀ 3) := CFSG.ClassicalGroups.Unitary.isPerfect_SUid
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) le_rfl
    fun _ => CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hK
      (pow_ne_two_of_ne_two Fact.out hp2 f)
  exact Group.IsPerfect.ofSurjective (f := (conjEquiv P hP).symm.toMonoidHom)
    (conjEquiv P hP).symm.surjective

theorem exists_section_quotient_of_mulEquiv (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {S : Type*} [Group S] (e : S ≃* SU σ₀ 3) (D : Subgroup S) [D.Normal]
    (hD3 : ∀ d ∈ D, d ^ 3 = 1) {R : Type*} [Group R] [Finite R] {ρ : R →* S ⧸ D}
    (hρ : Function.Surjective ρ) (hcen : ρ.ker ≤ Subgroup.center R) (h2 : IsPGroup 2 ρ.ker) :
    ∃ s : S ⧸ D →* R, ∀ x, ρ (s x) = x := by
  obtain ⟨β₀, hβ₀⟩ := exists_lift_SU_three hK hp2 hρ hcen h2
    ((QuotientGroup.mk' D).comp e.symm.toMonoidHom)
  set β₁ := β₀.comp e.toMonoidHom
  have hβ₁ : ∀ x, ρ (β₁ x) = (x : S ⧸ D) := fun x => by
    have := DFunLike.congr_fun hβ₀ (e x)
    simpa [β₁] using this
  have hle : D ≤ β₁.ker := by
    intro d hd
    have hk : β₁ d ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, hβ₁, QuotientGroup.eq_one_iff]
      exact hd
    obtain ⟨k, hk'⟩ := h2 ⟨_, hk⟩
    have h1 : β₁ d ^ 2 ^ k = 1 := congrArg Subtype.val hk'
    have h3 : β₁ d ^ 3 = 1 := by rw [← map_pow, hD3 d hd, map_one]
    have hcop : Nat.Coprime 3 (2 ^ k) := (Nat.coprime_comm.1 (Nat.coprime_two_left.2
      (by decide : Odd 3))).pow_right k
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
      (orderOf_dvd_of_pow_eq_one h1))
  refine ⟨QuotientGroup.lift D β₁ hle, fun x => ?_⟩
  induction x using QuotientGroup.induction_on with
  | H x => rw [QuotientGroup.lift_mk, hβ₁]

omit [Finite K] in
theorem pow_three_eq_one_of_mem_statedScalars {S : Subgroup (GL (Fin 3) K)}
    (hS : ∀ x ∈ S, (x : Matrix (Fin 3) (Fin 3) K).det = 1) {x : S}
    (hx : x ∈ (StatedScalars (Fin 3) K).subgroupOf S) : x ^ 3 = 1 := by
  obtain ⟨c, hc⟩ : (x : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := hx
  have hdet := hS x x.2
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hc3 : c ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hdet)
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, ← hc, ← map_pow, hc3, map_one, Subgroup.coe_one]

universe w in
theorem finite_isPerfect_forall_section_of_mulEquiv (hK : Nat.card K = (p ^ f) ^ 2)
    (hp2 : p ≠ 2) {S : Type*} [Group S] (e : S ≃* SU σ₀ 3) (D : Subgroup S) [D.Normal]
    (hD3 : ∀ d ∈ D, d ^ 3 = 1) {H : Type*} [Group H] (eH : H ≃* S ⧸ D) :
    Finite H ∧ Group.IsPerfect H ∧
      ∀ (R : Type w) [Group R] [Finite R] (ρ : R →* H), Function.Surjective ρ →
        ρ.ker ≤ Subgroup.center R → IsPGroup 2 ρ.ker → ∃ s : H →* R, ∀ x, ρ (s x) = x := by
  have : Finite S := Finite.of_equiv _ e.symm.toEquiv
  have : Group.IsPerfect (SU σ₀ 3) := isPerfect_SU_three hK hp2
  have : Group.IsPerfect S := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  refine ⟨Finite.of_equiv _ eH.symm.toEquiv,
    Group.IsPerfect.ofSurjective (f := eH.symm.toMonoidHom) eH.symm.surjective,
    fun R _ _ ρ hρ hcen h2 => ?_⟩
  have hker : (eH.toMonoidHom.comp ρ).ker = ρ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ eH.injective]
  obtain ⟨s, hs⟩ := exists_section_quotient_of_mulEquiv hK hp2 e D hD3
    (ρ := eH.toMonoidHom.comp ρ) (eH.surjective.comp hρ) (hker ▸ hcen) (hker ▸ h2)
  refine ⟨s.comp eH.toMonoidHom, fun x => eH.injective ?_⟩
  exact hs (eH x)

end Quotient

section Hermitian

variable {p f : ℕ} {K : Type} [Field K]

theorem unitaryFieldData_bar_eq (hK : UnitaryFieldData p f K) [Finite K] [Fact p.Prime]
    [CharP K p] :
    hK.bar = (unitaryInvolution K p f).toRingHom :=
  RingHom.ext fun c => (hK.bar_apply c).trans (unitaryInvolution_apply K p f c).symm

theorem card_eq_sq_of_unitaryFieldData (hK : UnitaryFieldData p f K) :
    Nat.card K = (p ^ f) ^ 2 := by
  rw [hK.card, ← pow_mul, mul_comm]

theorem nonempty_SUgram_mulEquiv (hK : UnitaryFieldData p f K) [Finite K]
    [Fact p.Prime] [CharP K p] {n : ℕ} {G₀ : Matrix (Fin n) (Fin n) K}
    (hG : ∀ i j, hK.bar (G₀ j i) = G₀ i j) (hdet : G₀.det ≠ 0) :
    Nonempty (SUgram hK.bar G₀ ≃* SU (unitaryInvolution K p f) n) := by
  have hF := card_eq_sq_of_unitaryFieldData hK
  have hGσ : conjTr (unitaryInvolution K p f) G₀ = G₀ := by
    ext i j
    rw [← hG i j, unitaryFieldData_bar_eq hK]
    rfl
  obtain ⟨P, hP⟩ := exists_conjTr_mul_mul_eq_one hF hGσ hdet
  obtain ⟨P', hP'⟩ := exists_wittMatrix hF n
  have hS : SUgram hK.bar G₀ = SUgram (unitaryInvolution K p f).toRingHom G₀ := by
    rw [unitaryFieldData_bar_eq hK]
  exact ⟨((MulEquiv.subgroupCongr hS).trans ((gramEquiv (τ := (unitaryInvolution K p f).toRingHom)
    (G₁ := 1) P hP).trans (MulEquiv.subgroupCongr (SUgram_one _)))).trans
      (conjEquiv P' hP').symm⟩

theorem det_eq_one_of_mem_SUgram {τ : K →+* K} {n : ℕ} {G₀ : Matrix (Fin n) (Fin n) K}
    {x : GL (Fin n) K} (hx : x ∈ SUgram τ G₀) : (x : Matrix (Fin n) (Fin n) K).det = 1 :=
  hx.1

def IsOddUnitaryThreeSource (H : Type) [Group H] : Prop :=
  ∃ (p f : ℕ) (K : Type) (_ : Field K) (hK : UnitaryFieldData p f K) (_ : p ≠ 2)
    (G₀ : Matrix (Fin 3) (Fin 3) K) (_ : ∀ i j, hK.bar (G₀ j i) = G₀ i j) (_ : G₀.det ≠ 0)
    (D : Subgroup (SUgram hK.bar G₀)) (_ : D.Normal)
    (_ : D ≤ (StatedScalars (Fin 3) K).subgroupOf (SUgram hK.bar G₀)),
    Nonempty (H ≃* SUgram hK.bar G₀ ⧸ D)

universe w in
theorem IsOddUnitaryThreeSource.properties {H : Type} [Group H]
    (hH : IsOddUnitaryThreeSource H) :
    Finite H ∧ Group.IsPerfect H ∧
      ∀ (R : Type w) [Group R] [Finite R] (ρ : R →* H), Function.Surjective ρ →
        ρ.ker ≤ Subgroup.center R → IsPGroup 2 ρ.ker → ∃ s : H →* R, ∀ x, ρ (s x) = x := by
  obtain ⟨p, f, K, _, hK, hp2, G₀, hG, hdet, D, _, hD, ⟨eH⟩⟩ := hH
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  have := hK.charP
  obtain ⟨e⟩ := nonempty_SUgram_mulEquiv hK hG hdet
  exact finite_isPerfect_forall_section_of_mulEquiv (card_eq_sq_of_unitaryFieldData hK) hp2 e D
    (fun d hd => pow_three_eq_one_of_mem_statedScalars (fun _ hx => det_eq_one_of_mem_SUgram hx)
      (hD hd)) eH

universe v w in
theorem odd_unitary_three_central_two_homomorphism_lifting {p f : ℕ} {K : Type} [Field K]
    (hK : UnitaryFieldData p f K) (hp2 : p ≠ 2) {G₀ : Matrix (Fin 3) (Fin 3) K}
    (hG : ∀ i j, hK.bar (G₀ j i) = G₀ i j) (hdet : G₀.det ≠ 0)
    (D : Subgroup (SUgram hK.bar G₀)) [D.Normal]
    (hD : D ≤ (StatedScalars (Fin 3) K).subgroupOf (SUgram hK.bar G₀))
    {E : Type v} {G : Type*} [Group E] [Group G] [Finite E] {π : E →* G}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    (∀ α : SUgram hK.bar G₀ ⧸ D →* G, ∃! β : SUgram hK.bar G₀ ⧸ D →* E, π.comp β = α) ∧
    (∀ α : SUgram hK.bar G₀ ⧸ D →* G, Function.Injective α →
      Function.Injective (perfectLift π α)) ∧
    (∀ (α : SUgram hK.bar G₀ ⧸ D →* G) (e : E),
      (MulAut.conj e).toMonoidHom.comp (perfectLift π α) =
        perfectLift π ((MulAut.conj (π e)).toMonoidHom.comp α)) ∧
    (∀ (H' : Type) [Group H'], IsOddUnitaryThreeSource H' →
      ∀ (α : SUgram hK.bar G₀ ⧸ D →* G) (β : H' →* SUgram hK.bar G₀ ⧸ D),
        (perfectLift π α).comp β = perfectLift π (α.comp β)) ∧
    (∀ (H' : Type) [Group H'], IsOddUnitaryThreeSource H' →
      ∀ (α : SUgram hK.bar G₀ ⧸ D →* G) (α' : H' →* G), (∀ x x', Commute (α x) (α' x')) →
        ∀ x x', Commute (perfectLift π α x) (perfectLift π α' x')) ∧
    (∀ (R : Type w) [Group R] [Finite R] (ρ : R →* SUgram hK.bar G₀ ⧸ D),
      Function.Surjective ρ → ρ.ker ≤ Subgroup.center R → IsPGroup 2 ρ.ker →
        (∃! s : SUgram hK.bar G₀ ⧸ D →* R, ∀ x, ρ (s x) = x) ∧
          (Subgroup.closure {r : R | Odd (orderOf r)} = ⊤ → ρ.ker = ⊥)) := by
  have hsrc : IsOddUnitaryThreeSource (SUgram hK.bar G₀ ⧸ D) :=
    ⟨p, f, K, inferInstance, hK, hp2, G₀, hG, hdet, D, inferInstance, hD, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hfin, hperf, hsplit⟩ := IsOddUnitaryThreeSource.properties.{v} hsrc
  refine ⟨existsUnique_lift_of_isPerfect hsplit hπ hcen h2,
    fun α hα => perfectLift_injective hsplit hπ hcen h2 hα,
    perfectLift_conj hsplit hπ hcen h2,
    fun H' _ hH' α β => ?_, fun H' _ hH' α α' hαα' x x' => ?_,
    fun R _ _ ρ hρ hcenR h2R => ?_⟩
  · have := (IsOddUnitaryThreeSource.properties.{v} hH').2.1
    exact perfectLift_comp hsplit hπ hcen h2 α β
  · obtain ⟨hfin', hperf', hsplit'⟩ := IsOddUnitaryThreeSource.properties.{v} hH'
    exact commute_perfectLift hsplit hπ hcen h2 α (comp_perfectLift hsplit' hπ hcen h2 α') hαα'
      x x'
  · obtain ⟨-, -, hsplitR⟩ := IsOddUnitaryThreeSource.properties.{w} hsrc
    obtain ⟨s, hs⟩ := hsplitR R ρ hρ hcenR h2R
    refine ⟨⟨s, hs, fun t ht => eq_of_comp_eq_of_isPerfect hcenR (MonoidHom.ext fun x => ?_)⟩,
      fun hodd => ker_eq_bot_of_closure_odd hcenR h2R hs hodd⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ht x, hs x]

end Hermitian

end CFSG.LieType.Steinberg
