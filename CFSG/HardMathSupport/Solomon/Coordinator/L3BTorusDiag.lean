module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.Group.Pi.Units

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix

variable {K : Type*} [Field K]

@[expose] noncomputable def diagHom (n : ℕ) (K : Type*) [Field K] :
    (Fin n → Kˣ) →* GL (Fin n) K :=
  (Units.map (Matrix.diagonalRingHom (Fin n) K).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin n => K)).symm.toMonoidHom

theorem coe_diagHom {n : ℕ} (d : Fin n → Kˣ) :
    ((diagHom n K d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => (d i : K)) := rfl

theorem diagHom_injective (n : ℕ) : Function.Injective (diagHom n K) := by
  intro d e h
  funext i
  have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i i) h
  simp only [coe_diagHom, diagonal_apply_eq] at this
  exact Units.ext this

@[expose] noncomputable def permGL (K : Type*) [Field K] : Equiv.Perm (Fin 3) →* GL (Fin 3) K :=
  (Matrix.permMatrixHom (n := Fin 3) (R := K)).toHomUnits

theorem coe_permGL (σ : Equiv.Perm (Fin 3)) :
    ((permGL K σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (σ⁻¹).permMatrix K := rfl

theorem permGL_mul_diagHom (σ : Equiv.Perm (Fin 3)) (d : Fin 3 → Kˣ) :
    permGL K σ * diagHom 3 K d = diagHom 3 K (fun i => d (σ⁻¹ i)) * permGL K σ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_permGL, coe_diagHom, coe_diagHom]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  split_ifs with h
  · subst h; simp
  · simp

@[expose] noncomputable def diagTorus (T : Subgroup Kˣ) : Subgroup (GL (Fin 3) K) :=
  (Subgroup.pi Set.univ (fun _ : Fin 3 => T)).map (diagHom 3 K)

theorem mem_diagTorus {T : Subgroup Kˣ} {A : GL (Fin 3) K} :
    A ∈ diagTorus T ↔ ∃ d : Fin 3 → Kˣ, (∀ i, d i ∈ T) ∧ diagHom 3 K d = A := by
  simp [diagTorus, Subgroup.mem_map, Subgroup.mem_pi]

theorem diagHom_mem_diagTorus {T : Subgroup Kˣ} {d : Fin 3 → Kˣ} (hd : ∀ i, d i ∈ T) :
    diagHom 3 K d ∈ diagTorus T :=
  mem_diagTorus.2 ⟨d, hd, rfl⟩

theorem card_diagTorus (T : Subgroup Kˣ) : Nat.card (diagTorus (K := K) T) = Nat.card T ^ 3 := by
  unfold diagTorus
  rw [Subgroup.card_map_of_injective (diagHom_injective 3)]
  let e : Subgroup.pi Set.univ (fun _ : Fin 3 => T) ≃ (Fin 3 → T) :=
    { toFun := fun x i => ⟨x.1 i, (Subgroup.mem_pi Set.univ).1 x.2 i (Set.mem_univ i)⟩
      invFun := fun f => ⟨fun i => (f i : Kˣ), (Subgroup.mem_pi Set.univ).2 fun i _ => (f i).2⟩
      left_inv := fun x => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr e, Nat.card_fun]
  simp

theorem permGL_eq_diagHom {σ : Equiv.Perm (Fin 3)} {d : Fin 3 → Kˣ}
    (h : permGL K σ = diagHom 3 K d) : σ = 1 := by
  refine Equiv.ext fun i => ?_
  by_contra hne
  have h1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) i (σ⁻¹ i)) h
  have hi : i ≠ σ.symm i := fun hi => hne (by simpa using congrArg σ hi)
  simp [coe_permGL, coe_diagHom, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hi] at h1

theorem permGL_injective : Function.Injective (permGL K) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  exact permGL_eq_diagHom (d := 1) (by rw [hσ]; exact (map_one _).symm)

theorem diagHom_conj_mem {T : Subgroup Kˣ} (σ : Equiv.Perm (Fin 3)) {d : Fin 3 → Kˣ}
    (hd : ∀ i, d i ∈ T) : permGL K σ * diagHom 3 K d * (permGL K σ)⁻¹ ∈ diagTorus T := by
  rw [permGL_mul_diagHom, mul_assoc, mul_inv_cancel, mul_one]
  exact diagHom_mem_diagTorus fun i => hd _

theorem le_normalizer_of_conj_mem {G : Type*} [Group G] (A N : Subgroup G)
    (h : ∀ a ∈ A, ∀ x ∈ N, a * x * a⁻¹ ∈ N) : A ≤ Subgroup.normalizer (N : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h a ha x hx, fun hx => ?_⟩
  have := h a⁻¹ (A.inv_mem ha) _ hx
  simpa [mul_assoc] using this

theorem permGL_range_le_normalizer (T : Subgroup Kˣ) :
    (permGL K).range ≤ Subgroup.normalizer (diagTorus T : Set (GL (Fin 3) K)) := by
  refine le_normalizer_of_conj_mem _ _ ?_
  rintro _ ⟨σ, rfl⟩ x hx
  obtain ⟨d, hd, rfl⟩ := mem_diagTorus.1 hx
  exact diagHom_conj_mem σ hd

theorem diagTorus_le_normalizer (T H : Subgroup Kˣ) :
    diagTorus (K := K) T ≤ Subgroup.normalizer (diagTorus H : Set (GL (Fin 3) K)) := by
  refine le_normalizer_of_conj_mem _ _ ?_
  intro a ha x hx
  obtain ⟨d, -, rfl⟩ := mem_diagTorus.1 ha
  obtain ⟨e, he, rfl⟩ := mem_diagTorus.1 hx
  rw [← map_inv, ← map_mul, ← map_mul]
  refine diagHom_mem_diagTorus fun i => ?_
  simpa [mul_comm, mul_assoc] using he i

@[expose] noncomputable def monomialGroup (T : Subgroup Kˣ) : Subgroup (GL (Fin 3) K) :=
  diagTorus T ⊔ (permGL K).range

theorem monomialGroup_le_normalizer (T H : Subgroup Kˣ) :
    monomialGroup (K := K) T ≤ Subgroup.normalizer (diagTorus H : Set (GL (Fin 3) K)) :=
  sup_le (diagTorus_le_normalizer T H) (permGL_range_le_normalizer H)

theorem card_monomialGroup (T : Subgroup Kˣ) :
    Nat.card (monomialGroup (K := K) T) = 6 * Nat.card T ^ 3 := by
  set D := diagTorus (K := K) T with hD
  set Q := (permGL K).range with hQ
  have hle : Q ≤ Subgroup.normalizer (D : Set (GL (Fin 3) K)) := permGL_range_le_normalizer T
  have hbot : D.subgroupOf Q = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨_, σ, rfl⟩ hx
    obtain ⟨d, -, hd⟩ := mem_diagTorus.1 (Subgroup.mem_subgroupOf.1 hx)
    have := permGL_eq_diagHom hd.symm
    subst this
    exact Subgroup.mem_bot.2 (Subtype.ext (map_one _))
  have hQcard : Nat.card Q = 6 := by
    rw [Nat.card_congr (MonoidHom.ofInjective (permGL_injective (K := K))).toEquiv.symm]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  have hidx : (D.subgroupOf (Q ⊔ D)).index = 6 := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hle
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hle
    have h1 : Nat.card (↥Q ⧸ D.subgroupOf Q) =
        Nat.card (↥(Q ⊔ D) ⧸ D.subgroupOf (Q ⊔ D)) :=
      Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient Q D hle).toEquiv
    have h2 : (D.subgroupOf Q).index = 6 := by rw [hbot, Subgroup.index_bot, hQcard]
    rw [← h2]
    simpa only [Subgroup.index] using h1.symm
  have hcard := Subgroup.card_mul_index (D.subgroupOf (Q ⊔ D))
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv,
    card_diagTorus] at hcard
  unfold monomialGroup
  rw [sup_comm, mul_comm]
  exact hcard.symm

@[expose] def coprimeThreeTorsion (G : Type*) [CommGroup G] : Subgroup G where
  carrier := {a | ∃ n, Nat.Coprime 3 n ∧ a ^ n = 1}
  one_mem' := ⟨1, by simp, one_pow 1⟩
  mul_mem' := by
    rintro a b ⟨n, hn, ha⟩ ⟨m, hm, hb⟩
    refine ⟨n * m, hn.mul_right hm, ?_⟩
    rw [mul_pow, pow_mul, ha, mul_comm n m, pow_mul, hb, one_pow, one_pow, one_mul]
  inv_mem' := by
    rintro a ⟨n, hn, ha⟩
    exact ⟨n, hn, by rw [inv_pow, ha, inv_one]⟩

theorem exists_pow_eq_one_of_mem_diagTorus {H : Subgroup Kˣ} (hH : H ≤ coprimeThreeTorsion Kˣ)
    {A : GL (Fin 3) K} (hA : A ∈ diagTorus H) : ∃ N, Nat.Coprime 3 N ∧ A ^ N = 1 := by
  obtain ⟨d, hd, rfl⟩ := mem_diagTorus.1 hA
  have : ∀ i, ∃ n, Nat.Coprime 3 n ∧ (d i) ^ n = 1 := fun i => hH (hd i)
  choose n hn hdn using this
  refine ⟨∏ i, n i, Nat.Coprime.prod_right fun i _ => hn i, ?_⟩
  rw [← map_pow]
  convert map_one (diagHom 3 K)
  funext i
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  show (d i) ^ (∏ i, n i) = 1
  rw [hc, pow_mul, hdn, one_pow]

end CFSG.HardMathSupport.Solomon.Coordinator
