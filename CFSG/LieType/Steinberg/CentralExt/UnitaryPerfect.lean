module

public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.LieType.Steinberg.CentralExt.SUThree
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.LieType.Steinberg

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary

theorem charP_of_card_eq_sq_pow {K : Type*} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = (p ^ f) ^ 2) : CharP K p := by
  have := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  exact charP_of_card_eq_prime_pow (f := f * 2) (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])

theorem odd_card_of_forall_pow_three_eq_one {G : Type*} [Group G] [Finite G]
    (h : ∀ x : G, x ^ 3 = 1) : Odd (Nat.card G) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have := orderOf_dvd_of_pow_eq_one (h x)
  rw [hx] at this
  omega

theorem card_eq_one_of_isPGroup_two_of_dvd_odd {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) {m : ℕ} (hm : Odd m) (hdvd : Nat.card G ∣ m) : Nat.card G = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hG
  rw [hk] at hdvd ⊢
  rcases k with _ | k
  · rfl
  · exfalso
    rw [pow_succ] at hdvd
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 ((Dvd.intro_left _ rfl).trans hdvd))

theorem odd_unitary_three_perfect_central_two_kernel_cyclic {p f : ℕ} (hp2 : p ≠ 2)
    {P Q : Type} [Group P] [Group Q] [Finite P] (hQ : LieModel Q .PSU 3 p f) {η : P →* Q}
    (hη : Function.Surjective η) (hP : Group.IsPerfect P) (hC : η.ker ≤ Subgroup.center P)
    (C₂ : Sylow 2 η.ker) : Nat.card C₂ = 1 := by
  have := hP
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by decide) hQ
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_sq_pow hp hK
  set φ := equivStatedSU hK 3
  let β : SU (unitaryInvolution K p f) 3 →* Q :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp φ.toMonoidHom)
  have hβ : Function.Surjective β :=
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp φ.surjective)
  obtain ⟨hdvd, -⟩ := sylow_two_of_isPerfect (β := β)
    (fun E _ _ π hπ hcen h2 => (su_three_central_two_extension_splitting hK hp2 hπ hcen
      h2).imp fun _ h => h.1) hβ hη hC C₂
  have hker : ∀ x : β.ker, x ^ 3 = 1 := by
    rintro ⟨x, hx⟩
    have hx' : φ x ∈ (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K) := by
      have h1 := hx
      rw [MonoidHom.mem_ker] at h1
      have h2 : (QuotientGroup.mk' _ (φ x) : StatedProj (StatedSU 3 (p ^ f) K)) = 1 :=
        e.symm.injective (by simpa [β] using h1)
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    obtain ⟨c, hc⟩ : ((φ x : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K :=
      hx'
    have hdet := det_eq_one_of_mem_statedSU (φ x).2
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    have hc3 : c ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hdet)
    refine Subtype.ext (φ.injective (Subtype.ext ?_))
    rw [Subgroup.coe_pow, map_pow, Subgroup.coe_pow, ← hc, ← map_pow, hc3, map_one,
      Subgroup.coe_one, map_one, Subgroup.coe_one]
  exact card_eq_one_of_isPGroup_two_of_dvd_odd C₂.isPGroup'
    (odd_card_of_forall_pow_three_eq_one hker) hdvd

theorem isCyclic_scalars_statedSU {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 1 ≤ n) :
    IsCyclic ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)) ∧
      ∀ z : (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K),
        z ^ Nat.gcd n (p ^ f + 1) = 1 := by
  set Z := (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)
  set i₀ : Fin n := ⟨0, by omega⟩
  have hscal : ∀ z : Z, ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c =
      ((z : StatedSU n (p ^ f) K) : GL (Fin n) K) ∧ c ^ n = 1 ∧ c ^ (p ^ f + 1) = 1 := by
    intro z
    obtain ⟨c, hc⟩ : ((z : StatedSU n (p ^ f) K) : GL (Fin n) K) ∈ StatedScalars (Fin n) K :=
      z.2
    have hdet := det_eq_one_of_mem_statedSU (z : StatedSU n (p ^ f) K).2
    have hmem : ((z : StatedSU n (p ^ f) K) : GL (Fin n) K) ∈
        SUid (unitaryInvolution K p f) n := by
      rw [SUid_eq_statedSU hK n]
      exact (z : StatedSU n (p ^ f) K).2
    have hiso := congrFun (congrFun hmem.2 i₀) i₀
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar] at hiso hdet
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    simp only [conjTr, Matrix.scalar_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.diagonal_apply, Matrix.one_apply_eq] at hiso
    rw [Finset.sum_eq_single i₀ (fun b _ hb => by simp [hb]) (by simp)] at hiso
    simp only [ite_true] at hiso
    rw [unitaryInvolution_apply] at hiso
    refine ⟨c, hc, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hdet),
      Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
    exact hiso
  let φ : Z →* K :=
    { toFun := fun z =>
        (((z : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i₀ i₀
      map_one' := by simp
      map_mul' := fun z w => by
        obtain ⟨c, hc, -⟩ := hscal z
        obtain ⟨d, hd, -⟩ := hscal w
        simp only [Subgroup.coe_mul, Units.val_mul, ← hc, ← hd,
          Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal,
          Matrix.diagonal_apply_eq] }
  have hφ : Function.Injective φ := by
    intro z w h
    obtain ⟨c, hc, -⟩ := hscal z
    obtain ⟨d, hd, -⟩ := hscal w
    have h' : (c : K) = d := by
      simpa [φ, ← hc, ← hd, Matrix.GeneralLinearGroup.coe_scalar] using h
    exact Subtype.ext (Subtype.ext (by rw [← hc, ← hd, Units.ext h']))
  have : Finite Z := inferInstance
  refine ⟨isCyclic_of_injective_ringHom φ hφ, fun z => ?_⟩
  obtain ⟨c, hc, hn', hq'⟩ := hscal z
  have hg : c ^ Nat.gcd n (p ^ f + 1) = 1 := pow_gcd_eq_one.2 ⟨hn', hq'⟩
  refine Subtype.ext (Subtype.ext ?_)
  rw [Subgroup.coe_pow, Subgroup.coe_pow, ← hc, ← map_pow, hg, map_one, Subgroup.coe_one,
    Subgroup.coe_one]

end CFSG.LieType.Steinberg
