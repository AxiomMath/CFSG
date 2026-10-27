module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2PositionB
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutU
public import CFSG.LocalAnalysis.SeitzReduction.FusionGenericAutU2

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.EvenSmallLie CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore perfectCore_le)

section Sylow

variable {n : ℕ} {K : Type*} [Field K]

theorem commute_transvection_first_last_of_mem_unitriangular (hn : 2 ≤ n)
    {v : SpecialLinearGroup (Fin n) K} (hv : v ∈ unitriangular n K) :
    v * Matrix.SpecialLinearGroup.transvection (firstIdx_ne_lastIdx hn) (1 : K) =
      Matrix.SpecialLinearGroup.transvection (firstIdx_ne_lastIdx hn) (1 : K) * v := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.1 hv
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul]
  congr 1
  ext i j
  by_cases hj : j = lastIdx hn
  · subst hj
    rw [mul_single_apply_same, mul_one]
    by_cases hi : i = firstIdx hn
    · subst hi
      rw [single_mul_apply_same, one_mul, hdiag, hdiag]
    · rw [single_mul_apply_of_ne _ _ _ _ _ hi, hlow i _ (firstIdx_lt_of_ne hn hi)]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hj]
    by_cases hi : i = firstIdx hn
    · subst hi
      rw [single_mul_apply_same, one_mul, hlow _ j (lt_lastIdx_of_ne hn hj)]
    · rw [single_mul_apply_of_ne _ _ _ _ _ hi]

theorem InvPlacement.exists_sylow_le_centralizer_elt [Finite K] [CharP K 2] (hn : 2 ≤ n)
    (P : InvPlacement n 1) :
    ∃ U : Sylow 2 (LinearFlag.projectiveSL n K),
      (U : Subgroup (LinearFlag.projectiveSL n K)) ≤ Subgroup.centralizer {P.elt K} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, hσf, hσl⟩ := exists_perm_apply_eq_apply_eq (firstIdx_ne_lastIdx hn) (P.u_ne_w 0 0)
  set ρ : SpecialLinearGroup (Fin n) K ≃* SpecialLinearGroup (Fin n) K :=
    reindexSpecialLinear σ with hρ
  set β := descendAut n K ρ with hβ
  set T := Matrix.SpecialLinearGroup.transvection (firstIdx_ne_lastIdx hn) (1 : K) with hT
  have hρT : ρ T = P.mat K := by
    apply Subtype.ext
    ext i j
    rw [hρ, coe_reindexSpecialLinear_apply, hT, Matrix.SpecialLinearGroup.transvection_coe,
      InvPlacement.coe_mat, Matrix.add_apply, Matrix.add_apply, one_apply, one_apply,
      single_apply]
    have h1 : σ.symm i = σ.symm j ↔ i = j := σ.symm.injective.eq_iff
    have h2 : (firstIdx hn = σ.symm i ∧ lastIdx hn = σ.symm j) ↔
        (∃ a : Fin 1, P.u a = i ∧ P.w a = j) := by
      rw [Equiv.eq_symm_apply, Equiv.eq_symm_apply, hσf, hσl]
      constructor
      · rintro ⟨hi, hj⟩
        exact ⟨0, hi, hj⟩
      · rintro ⟨a, hi, hj⟩
        rw [Subsingleton.elim a 0] at hi hj
        exact ⟨hi, hj⟩
    simp only [InvPlacement.nil, Matrix.of_apply]
    by_cases hij : i = j
    · rw [ite_eq_left (h1.2 hij), ite_eq_left hij]
      by_cases hh : ∃ a : Fin 1, P.u a = i ∧ P.w a = j
      · rw [ite_eq_left (h2.2 hh), ite_eq_left hh]
      · rw [ite_eq_right (fun h => hh (h2.1 h)), ite_eq_right hh]
    · rw [ite_eq_right (fun h => hij (h1.1 h)), ite_eq_right hij]
      by_cases hh : ∃ a : Fin 1, P.u a = i ∧ P.w a = j
      · rw [ite_eq_left (h2.2 hh), ite_eq_left hh]
      · rw [ite_eq_right (fun h => hh (h2.1 h)), ite_eq_right hh]
  have hβT : β (LinearFlag.proj n K T) = P.elt K := by
    rw [hβ, descendAut_proj, hρT]
    rfl
  obtain ⟨U₀, hU₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (by omega : 1 ≤ n)
  refine ⟨U₀.mapSurjective (f := β.toMonoidHom) β.surjective, ?_⟩
  intro x hx
  change x ∈ (U₀ : Subgroup (LinearFlag.projectiveSL n K)).map β.toMonoidHom at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [hU₀] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  rw [Subgroup.mem_centralizer_singleton_iff, ← hβT]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul,
    commute_transvection_first_last_of_mem_unitriangular hn hv]

end Sylow

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem isInvolutionClass_one_conj_of_conj_eq_mul_two (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hn : 5 ≤ n) (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {g : G} {y : L} (hy : IsInvolutionClass 1 (e y)) (hg : g⁻¹ * t * g = t * y) :
    ∃ hgy : g * y * g⁻¹ ∈ L, IsInvolutionClass 1 (e ⟨g * y * g⁻¹, hgy⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  set φ : LinearFlag.projectiveSL n K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := EPilot.range_subtype_comp_mulEquiv_symm e
  have hφy : φ (e y) = y := by simp [hφdef]
  have hy2 : (y : G) * y = 1 := by
    have h := congrArg (fun x => (φ x : G)) ((hy.orderOf_eq_two one_ne_zero) ▸
      pow_orderOf_eq_one (e y))
    simp only [map_pow, map_one, hφy] at h
    rw [← sq]
    exact h
  have hyinv : (y : G)⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hty : (y : G) * t = t * y := mem_centralizer_iff.1 htC _ y.2
  have hw' : (y : G)⁻¹ * t ∈ centralizer (CFSG.conjugate L g : Set G) := by
    rw [hyinv, hty, ← hg, mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.1 (EPilot.conjugate_le_centralizer_conj htC g hl)
  have hΛeq := EPilot.perfectCore_inf_centralizer_eq_of_inv_mul_mem hset hOut htC ht
    (Or.inr hg) hw'
  obtain ⟨hperf, -⟩ := centralizer_transvection_perfect_two hK hn hy
  have hcore : perfectCore (Subgroup.centralizer ({e y} : Set (LinearFlag.projectiveSL n K))) =
      Subgroup.centralizer ({e y} : Set (LinearFlag.projectiveSL n K)) :=
    le_antisymm (perfectCore_le _) (CFSG.Quasithin.le_perfectCore_of_perfect le_rfl hperf)
  have hΛ : (Subgroup.centralizer ({e y} : Set (LinearFlag.projectiveSL n K))).map φ =
      perfectCore (CFSG.conjugate L g ⊓ centralizer ({(y : G)} : Set G)) := by
    rw [← hcore, map_perfectCore_centralizer_singleton hφ, hφr, hφy, hΛeq]
  have hΛle : perfectCore (CFSG.conjugate L g ⊓ centralizer ({(y : G)} : Set G)) ≤
      CFSG.conjugate L g ⊓ centralizer ({(y : G)} : Set G) := perfectCore_le _
  have hyLg : (y : G) ∈ CFSG.conjugate L g := by
    have h1 : (y : G) ∈ (Subgroup.centralizer ({e y} : Set (LinearFlag.projectiveSL n K))).map φ :=
      ⟨e y, Subgroup.mem_centralizer_singleton_iff.2 rfl, hφy⟩
    rw [hΛ] at h1
    exact (hΛle h1).1
  have hgy : g * y * g⁻¹ ∈ L := SeitzQ2.mem_conjugate_iff_conj_mem.1 hyLg
  refine ⟨hgy, ?_⟩
  obtain ⟨P, c, hc⟩ := exists_conj_eq_elt_of_isInvolutionClass_one hy
  obtain ⟨U, hU⟩ := P.exists_sylow_le_centralizer_elt (K := K) (by omega)
  set U₁ : Subgroup (LinearFlag.projectiveSL n K) :=
    (U : Subgroup (LinearFlag.projectiveSL n K)).map (MulAut.conj c⁻¹).toMonoidHom with hU₁
  have hU₁C : U₁ ≤ Subgroup.centralizer ({e y} : Set (LinearFlag.projectiveSL n K)) := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' := Subgroup.mem_centralizer_singleton_iff.1 (hU hu)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hy' : e y = c⁻¹ * P.elt K * c := by rw [← hc]; group
    rw [hy']
    calc c⁻¹ * u * c * (c⁻¹ * P.elt K * c) = c⁻¹ * (u * P.elt K) * c := by group
      _ = c⁻¹ * (P.elt K * u) * c := by rw [hu']
      _ = c⁻¹ * P.elt K * c * (c⁻¹ * u * c) := by group
  have hU₁card : Nat.card U₁ = 2 ^ (Nat.card (LinearFlag.projectiveSL n K)).factorization 2 := by
    rw [hU₁, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, Sylow.card_eq_multiplicity]
  set S : Subgroup G := U₁.map φ with hS
  have hSLg : S ≤ CFSG.conjugate L g ⊓ centralizer ({(y : G)} : Set G) := by
    have h1 : S ≤ (Subgroup.centralizer ({e y} : Set (LinearFlag.projectiveSL n K))).map φ :=
      Subgroup.map_mono hU₁C
    rw [hΛ] at h1
    exact h1.trans hΛle
  set e' : CFSG.conjugate L g ≃* LinearFlag.projectiveSL n K :=
    (conjugateMulEquiv L g).symm.trans e with he'
  have he'y : e' ⟨y, hyLg⟩ = e ⟨g * y * g⁻¹, hgy⟩ := by
    rw [he', MulEquiv.trans_apply]
    congr 1
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [coe_conjugateMulEquiv]
    group
  have hcardLg : Nat.card (CFSG.conjugate L g) = Nat.card (LinearFlag.projectiveSL n K) :=
    Nat.card_congr e'.toEquiv
  have hS'card : Nat.card (S.subgroupOf (CFSG.conjugate L g)) =
      2 ^ (Nat.card (CFSG.conjugate L g)).factorization 2 := by
    rw [hcardLg, ← hU₁card,
      Nat.card_congr (S.subgroupOfEquivOfLe (hSLg.trans inf_le_left)).toEquiv, hS,
      Subgroup.card_map_of_injective hφ]
  set U' : Sylow 2 (CFSG.conjugate L g) := Sylow.ofCard _ hS'card with hU'
  have hy1 : (⟨y, hyLg⟩ : CFSG.conjugate L g) ≠ 1 := by
    intro h
    have h1 : (y : G) = 1 := congrArg Subtype.val h
    exact hy.ne_one one_ne_zero (e.symm.injective (by
      rw [MulEquiv.symm_apply_apply, map_one]
      exact Subtype.ext h1))
  have hcomm : ∀ u ∈ (U' : Subgroup (CFSG.conjugate L g)), u * ⟨y, hyLg⟩ = ⟨y, hyLg⟩ * u := by
    intro u hu
    rw [hU', Sylow.coe_ofCard, Subgroup.mem_subgroupOf] at hu
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hSLg hu).2
    exact Subtype.ext h1
  have hcl := isInvolutionClass_one_of_commute_sylow_of_mulEquiv (by omega) e' U' hy1 hcomm
  rwa [he'y] at hcl

theorem exists_le_centralizer_mulEquiv_of_conj_eq_mul_two (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hn : 5 ≤ n) (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin n} (hab : a ≠ b) {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((rootSL2 (K := K) a b).map e.symm.toMonoidHom).map L.subtype) {g : G} {y : L}
    (hyD : e y ∈ blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))
    (hy : IsInvolutionClass 1 (e y)) (hg : g⁻¹ * t * g = t * y) :
    ∃ g₁ y₁ : G,
      y₁ ∈ ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
        L.subtype ∧
      orderOf y₁ = 2 ∧ g₁⁻¹ * t * g₁ = t * y₁ ∧
      ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓ centralizer ({t * y₁} : Set G) ∧
        Nonempty (P ≃* ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map
          e.symm.toMonoidHom).map L.subtype) := by
  obtain ⟨hgy, hy'⟩ := isInvolutionClass_one_conj_of_conj_eq_mul_two hset hOut hK hn e ht hKt hy hg
  exact exists_le_centralizer_mulEquiv_of_conj_eq_mul_of_transvection hset hOut hn e ht hKt hab
    hXodd hXJ hyD hy hg hgy hy'

end Setting

end CFSG.SeitzReduction.LinearPilot
