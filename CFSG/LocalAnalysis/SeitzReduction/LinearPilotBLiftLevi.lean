module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotBLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard
public import CFSG.LocalAnalysis.SeitzReduction.SeitzBranches
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHsyl
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandardSetting
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.F4Pilot (HasBLift)

section PSL

variable {K : Type*} [Field K] {n : ℕ}

theorem exists_pow_eq_units_of_coprime [Finite K] (hcop : Nat.Coprime n (Nat.card K - 1)) (u : Kˣ) :
    ∃ v : Kˣ, v ^ n = u := by
  have h1 : orderOf u ∣ Nat.card K - 1 := by
    rw [← Nat.card_units]
    exact orderOf_dvd_natCard u
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (hcop.coprime_dvd_right h1)
  exact ⟨u ^ m, by rw [← pow_mul, mul_comm, pow_mul, hm]⟩

theorem exists_mem_levTorus_eq_conj_of_fix [Finite K] (hn : 4 ≤ n) (a : Fin n)
    (hpow : ∀ u : Kˣ, ∃ v : Kˣ, v ^ n = u) {β : MulAut (LinearFlag.projectiveSL n K)}
    (hβ : ∀ x ∈ blockSL (({a} : Finset (Fin n))ᶜ), β x = x) :
    ∃ x ∈ levTorus (K := K) a, β = MulAut.conj x := by
  have hcard : (({a} : Finset (Fin n))ᶜ).card = n - 1 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  obtain ⟨A, rfl, hA⟩ := exists_conjAut_eq_of_fix_blockSL (by omega) (by omega) hβ
  have hA' : ∀ i j, (i ≠ a ∨ j ≠ a) →
      (A : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j := fun i j h =>
    hA i j (by simpa only [Finset.mem_compl, Finset.mem_singleton] using h)
  have hAa : (A : Matrix (Fin n) (Fin n) K) a a ≠ 0 := by
    intro h0
    apply Matrix.GeneralLinearGroup.det_ne_zero A
    refine det_eq_zero_of_col (j := a) fun i => ?_
    by_cases hi : i = a
    · rw [hi, h0]
    · rw [hA' i a (Or.inl hi), one_apply_ne hi]
  set lam : Kˣ := Units.mk0 _ hAa with hlam
  obtain ⟨μ, hμ⟩ := hpow lam⁻¹
  have hn1 : μ ^ n = μ ^ (n - 1) * μ := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hlamμ : lam * μ = μ⁻¹ ^ (n - 1) := by
    have h1 : lam = (μ ^ n)⁻¹ := by rw [hμ, inv_inv]
    rw [h1, hn1, _root_.mul_inv_rev, mul_comm μ⁻¹, inv_mul_cancel_right, inv_pow]
  refine ⟨LinearFlag.proj n K (levTorusHom a μ), proj_levTorusHom_mem a μ, ?_⟩
  have hAμ : A * GeneralLinearGroup.scalar (Fin n) μ =
      SpecialLinearGroup.toGL (levTorusHom a μ) := by
    apply Units.ext
    ext i j
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, mul_diagonal,
      SpecialLinearGroup.coe_GL_coe_matrix, coe_levTorusHom]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
      by_cases hia : i = a
      · subst hia
        simp only [levDiag, ite_true]
        have hl : (A : Matrix (Fin n) (Fin n) K) i i = (lam : K) := rfl
        rw [hl, ← Units.val_mul, hlamμ]
      · rw [hA' i i (Or.inl hia), one_apply_eq, one_mul]
        simp [levDiag, hia]
    · have hor : i ≠ a ∨ j ≠ a := by
        by_contra h
        push Not at h
        exact hij (h.1.trans h.2.symm)
      rw [diagonal_apply_ne _ hij, hA' i j hor, one_apply_ne hij, zero_mul]
  rw [← conjAut_toGL, ← hAμ, map_mul, conjAut_scalar, mul_one]

end PSL

section Neighbour

variable {G : Type*} [Group G] {L : Subgroup G}
  {K : Type*} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [CharP K 2] in
theorem exists_mem_map_levTorus_eq_conj_of_fix (e : L ≃* LinearFlag.projectiveSL n K) (hn : 4 ≤ n)
    (a : Fin n) (hpow : ∀ u : Kˣ, ∃ v : Kˣ, v ^ n = u) {D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    (β : MulAut L) (hβ : ∀ x : L, (x : G) ∈ D → β x = x) :
    ∃ y : L, (y : G) ∈ ((levTorus (K := K) a).map e.symm.toMonoidHom).map L.subtype ∧
      β = MulAut.conj y := by
  have hfix : ∀ x ∈ blockSL (({a} : Finset (Fin n))ᶜ), MulAut.congr e β x = x := by
    intro x hx
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    have hmem : ((e.symm x : L) : G) ∈ D := by
      rw [hDe]
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
    rw [hβ _ hmem, MulEquiv.apply_symm_apply]
  obtain ⟨x, hx, hβ'⟩ := exists_mem_levTorus_eq_conj_of_fix hn a hpow hfix
  refine ⟨e.symm x, ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩, MulEquiv.ext fun l => ?_⟩
  have h1 := congrArg (fun γ : MulAut (LinearFlag.projectiveSL n K) => γ (e l)) hβ'
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h1
  have h2 : β l = e.symm x * l * (e.symm x)⁻¹ := by
    apply e.injective
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [h2, MulAut.conj_apply]

variable [Finite G]

theorem bLift_neighbour_levTorus (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 4 ≤ n) (a : Fin n) (hc : ∃ c : Kˣ, c ^ n ≠ 1)
    (hcop : Nat.Coprime n (Nat.card K - 1))
    {X : Subgroup G} (hX : X = ((levTorus (K := K) a).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    (∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X) ∧
      (∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
        c ∈ center (centralizer (X : Set G))) ∧
      ∀ E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        ⁅E, E⁆ = E →
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
          normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆ →
        HasBLift E := by
  have hcard : (({a} : Finset (Fin n))ᶜ).card = n - 1 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  have hLt := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht
  obtain ⟨-, -, -, hXo, hD, -⟩ := neighbour_data_levTorus e hn a hc htC hX hDe
  have hDq : CFSG.IsQuasisimple D := hDe ▸ isQuasisimple_map_blockSL (L := L) e
    (I := ({a} : Finset (Fin n))ᶜ) (by omega) (by omega) (Or.inl (by omega))
  have hmax : ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓
      centralizer (D : Set G), Odd (orderOf c) → c ∈ X := by
    intro c hc' hco
    refine mem_of_forall_fix_eq_conj htC ht hLt hK hXo (fun β hβ => ?_) hc'.1.2 hc'.2 hco
    rw [hX]
    exact exists_mem_map_levTorus_eq_conj_of_fix e hn a (exists_pow_eq_units_of_coprime hcop) hDe
      β hβ
  exact ⟨hmax, mem_center_of_mem_oddCore_of_commute_of_forall_odd_mem htC hLt htX hD hDq hmax,
    fun E hE htE hEt => hasBLift_of_forall_odd_mem htC ht hLt htX hD hDq hmax hE htE hEt⟩

theorem bLift_neighbour_levTorus_four (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* LinearFlag.projectiveSL 4 K) (hq : 4 ≤ Nat.card K) (a : Fin 4)
    {X : Subgroup G} (hX : X = ((levTorus (K := K) a).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin 4))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    (∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X) ∧
      (∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
        c ∈ center (centralizer (X : Set G))) ∧
      ∀ E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        ⁅E, E⁆ = E →
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
          normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆ →
        HasBLift E := by
  have hcop : Nat.Coprime 4 (Nat.card K - 1) := by
    have h := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 (odd_natCard_sub_one (K := K)))
    rwa [show (2 : ℕ) ^ 2 = 4 by norm_num] at h
  exact bLift_neighbour_levTorus hL htC ht hK e le_rfl a (exists_pow_four_ne_one hq) hcop hX htX
    hDe

end Neighbour

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem bLift_neighbour_levTorus_of_seitzSetting (hset : SeitzSetting G L) {f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (e : L ≃* LinearFlag.projectiveSL 4 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (a : Fin 4)
    {X : Subgroup G} (hX : X = ((levTorus (K := K) a).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin 4))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    (∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X) ∧
      (∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
        c ∈ center (centralizer (X : Set G))) ∧
      ∀ E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        ⁅E, E⁆ = E →
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
          normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆ →
        HasBLift E := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  exact bLift_neighbour_levTorus_four hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers hset e hKc le_rfl htC ht) e
    (four_le_card_of_seitzSetting hset hKc e) a hX htX hDe

end Setting

end CFSG.SeitzReduction.LinearPilot
