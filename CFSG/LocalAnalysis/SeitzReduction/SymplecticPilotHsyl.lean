module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotBLift
import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply elt mat_elt E pos1
  E_pos1)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp coe_fieldSp)
open TauCeti.GLSymplecticFin (RootSubgroupIndex)

variable {K : Type} [Field K]

section Aut

variable {r : ℕ}

theorem map_E (σ : K ≃+* K) (ρ : RootSubgroupIndex r) : (E K ρ).map σ = E K ρ := by
  cases ρ <;> ext a b <;>
    simp only [Matrix.map_apply, E, Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply] <;>
    split_ifs <;> simp

theorem fieldSp_elt (σ : K ≃+* K) (ρ : RootSubgroupIndex r) (c : K) :
    fieldSp r K σ (elt ρ c) = elt ρ (σ c) := by
  apply mat_injective
  rw [mat_apply, coe_fieldSp, ← mat_apply, mat_elt, mat_elt]
  ext a b
  have h := congrFun (congrFun (map_E σ ρ) a) b
  rw [Matrix.map_apply] at h
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
    map_mul, h, Matrix.one_apply]
  split_ifs <;> simp

theorem eq_one_of_forall_conj_fieldSp_elt {s : StatedSp r K} {σ : K ≃+* K}
    {ρ : RootSubgroupIndex r} (h : ∀ c : K, s * fieldSp r K σ (elt ρ c) * s⁻¹ = elt ρ c) :
    σ = 1 := by
  set S := mat r K s with hS
  set Si := mat r K s⁻¹ with hSi
  have hSSi : S * Si = 1 := by rw [hS, hSi, ← map_mul, mul_inv_cancel, map_one]
  have key : ∀ c : K, 1 + σ c • (S * E K ρ * Si) = 1 + c • E K ρ := by
    intro c
    have h1 := congrArg (mat r K) (h c)
    rw [fieldSp_elt, map_mul, map_mul, mat_elt, mat_elt] at h1
    rw [← h1, ← hS, ← hSi, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSSi,
      Matrix.mul_smul, Matrix.smul_mul]
  have h1 := key 1
  rw [map_one, one_smul, one_smul, add_right_inj] at h1
  refine RingEquiv.ext fun c => ?_
  have h2 := key c
  rw [h1, add_right_inj] at h2
  have h3 := congrFun (congrFun h2 (pos1 ρ).1) (pos1 ρ).2
  simpa [E_pos1] using h3

theorem exists_eq_conj_mul_fieldSp [Finite K] [CharP K 2] (hr : 3 ≤ r)
    (β : MulAut (StatedSp r K)) :
    ∃ (s : StatedSp r K) (σ : K ≃+* K), β = MulAut.conj s * fieldSp r K σ := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨A, σ, hA⟩ := (SymplecticHigher.automorphism_generation (K := K) hr).2
    (MulAut.congr (F4Pilot.spProjEquiv r K) β)
  obtain ⟨s, hs⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
  refine ⟨s, σ, (MulAut.congr (F4Pilot.spProjEquiv r K)).injective ?_⟩
  rw [hA, hs, map_mul, F4Pilot.mulAutCongr_spProjEquiv_conj,
    F4Pilot.mulAutCongr_spProjEquiv_fieldSp]

theorem exists_eq_conj_of_forall_elt_fix [Finite K] [CharP K 2] (hr : 3 ≤ r)
    {β : MulAut (StatedSp r K)} {ρ : RootSubgroupIndex r}
    (h : ∀ c : K, β (elt ρ c) = elt ρ c) :
    ∃ s : StatedSp r K, β = MulAut.conj s := by
  obtain ⟨s, σ, rfl⟩ := exists_eq_conj_mul_fieldSp hr β
  have hσ : σ = 1 := eq_one_of_forall_conj_fieldSp_elt (s := s) fun c => by
    have := h c
    rwa [MulAut.mul_apply, MulAut.conj_apply] at this
  refine ⟨s, ?_⟩
  rw [hσ, map_one, mul_one]

theorem eq_one_of_conj_eq_one [CharP K 2] {s : StatedSp r K} (h : MulAut.conj s = 1) : s = 1 := by
  have hs : s ∈ center (StatedSp r K) := by
    rw [mem_center_iff]
    intro g
    have := congrArg (fun γ : MulAut (StatedSp r K) => γ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * s = s * g * s⁻¹ * s := by rw [this]
      _ = s * g := by group
  rwa [center_statedSp_eq_bot, mem_bot] at hs

theorem eq_one_of_conj_pow_eq_one [CharP K 2] {s : StatedSp r K} {m : ℕ}
    (h : MulAut.conj s ^ 2 ^ m = 1) {N : ℕ} (hN : Odd N) (hsN : orderOf s ∣ N) : s = 1 := by
  rw [← map_pow] at h
  have h1 := eq_one_of_conj_eq_one h
  have hd1 := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (2 ^ m) N := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hN)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hsN)

end Aut

section RootTorus

variable {n : ℕ}

theorem isSupp_mono {m : ℕ} {S S' : Set (Fin m ⊕ Fin m)} (h : S ⊆ S')
    {M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K} (hM : IsSupp S M) : IsSupp S' M :=
  fun a b hab => hM a b fun h' => hab ⟨h h'.1, h h'.2⟩

theorem coords_subset_compl_coords {m : ℕ} {i k : Fin m} (hik : i ≠ k) :
    coords i ⊆ (coords k)ᶜ := by
  intro a ha hak
  rcases mem_coords.1 ha with rfl | rfl <;> rcases mem_coords.1 hak with h | h <;> simp_all

theorem elt_positiveLong_mem_complSp {m : ℕ} {i k : Fin m} (hik : i ≠ k) (c : K) :
    elt (.positiveLong i) c ∈ complSp K k := by
  rw [mem_complSp, ← longBlock_sl2Upper]
  exact isSupp_mono (coords_subset_compl_coords hik) (isSupp_longBlock i _)

theorem mul_comm_of_conj_apply_eq {G : Type*} [Group G] {s y : G} (h : MulAut.conj s y = y) :
    y * s = s * y := by
  rw [MulAut.conj_apply] at h
  calc y * s = s * y * s⁻¹ * s := by rw [h]
    _ = s * y := by group

theorem exists_mem_rootTorusSp_eq_conj_of_fix [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (hn : 2 ≤ n) (k : Fin (n + 1)) {β : MulAut (StatedSp (n + 1) K)}
    (hX : ∀ x ∈ rootTorusSp K k, β x = x) (hD : ∀ d ∈ complSp K k, β d = d) :
    ∃ x ∈ rootTorusSp K k, β = MulAut.conj x := by
  have : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨i, hik⟩ := exists_ne k
  obtain ⟨s, rfl⟩ := exists_eq_conj_of_forall_elt_fix (ρ := .positiveLong i) (by omega)
    fun c => hD _ (elt_positiveLong_mem_complSp hik c)
  have hs : s ∈ centralizer (rootTorusSp K k : Set (StatedSp (n + 1) K)) ⊓
      centralizer (complSp K k : Set (StatedSp (n + 1) K)) :=
    ⟨mem_centralizer_iff.2 fun x hx => mul_comm_of_conj_apply_eq (hX x hx),
      mem_centralizer_iff.2 fun d hd => mul_comm_of_conj_apply_eq (hD d hd)⟩
  rw [centralizer_rootTorusSp_inf_centralizer_complSp hK k] at hs
  exact ⟨s, hs, rfl⟩

theorem eq_one_of_two_pow_fix_rootTorusSp [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (hn : 2 ≤ n) (k : Fin (n + 1)) {β : MulAut (StatedSp (n + 1) K)}
    (hX : ∀ x ∈ rootTorusSp K k, β x = x) (hD : ∀ d ∈ complSp K k, β d = d) {m : ℕ}
    (hβm : β ^ 2 ^ m = 1) : β = 1 := by
  obtain ⟨x, hx, rfl⟩ := exists_mem_rootTorusSp_eq_conj_of_fix hK hn k hX hD
  rw [eq_one_of_conj_pow_eq_one hβm (odd_card_rootTorusSp k)
    ((rootTorusSp K k).orderOf_dvd_natCard hx), map_one]

theorem eq_one_of_isPGroup_fix_rootTorusSp [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (hn : 2 ≤ n) (k : Fin (n + 1)) {β : MulAut (StatedSp (n + 1) K)}
    (hβ : IsPGroup 2 (zpowers β))
    (hX : ∀ x ∈ rootTorusSp K k, β x = x) (hD : ∀ d ∈ complSp K k, β d = d) : β = 1 := by
  obtain ⟨m, hm⟩ := hβ ⟨β, mem_zpowers β⟩
  exact eq_one_of_two_pow_fix_rootTorusSp hK hn k hX hD (m := m) (congrArg Subtype.val hm)

theorem exists_mem_rootTorusSp_eq_conj_of_odd [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (hn : 2 ≤ n) (k : Fin (n + 1)) {β : MulAut (StatedSp (n + 1) K)}
    (_hβ : Odd (orderOf β))
    (hX : ∀ x ∈ rootTorusSp K k, β x = x) (hD : ∀ d ∈ complSp K k, β d = d) :
    ∃ x ∈ rootTorusSp K k, β = MulAut.conj x :=
  exists_mem_rootTorusSp_eq_conj_of_fix hK hn k hX hD

end RootTorus

section Siegel

variable {n : ℕ}

theorem elt_difference_mem_siegelLevi {i j : Fin n} (hij : i ≠ j) (c : K) :
    elt (.difference i j hij) c ∈ siegelLevi K n := by
  refine ⟨Matrix.SpecialLinearGroup.transvection hij c, ?_⟩
  rw [CFSG.LieType.Universal.Symplectic.SpExtras.elt_difference_eq_leviHom,
    ← TauCeti.toGL_transvection_eq_transvectionUnit]
  simp only [leviEmbedSL, leviEmbedGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

theorem mem_siegelTorus_of_commute_elt_difference (hn : 1 ≤ n) {A : GL (Fin n) K}
    (hA : ∀ (i j : Fin n) (hij : i ≠ j),
      elt (.difference i j hij) (1 : K) * leviEmbedGL K n A =
        leviEmbedGL K n A * elt (.difference i j hij) 1) :
    leviEmbedGL K n A ∈ siegelTorus K n := by
  have hcomm : Pairwise fun i j => Commute (single i j (1 : K)) (A : Matrix (Fin n) (Fin n) K) := by
    intro i j hij
    have h1 := congrArg (mat n K) (hA i j hij)
    rw [CFSG.LieType.Universal.Symplectic.SpExtras.elt_difference_eq_leviHom, map_mul, map_mul]
      at h1
    change mat n K (leviEmbedGL K n (TauCeti.transvectionUnit hij 1)) *
        mat n K (leviEmbedGL K n A) =
      mat n K (leviEmbedGL K n A) * mat n K (leviEmbedGL K n (TauCeti.transvectionUnit hij 1))
      at h1
    rw [mat_leviEmbedGL, mat_leviEmbedGL, fromBlocks_multiply, fromBlocks_multiply,
      fromBlocks_inj] at h1
    have h2 := h1.1
    simp only [Matrix.mul_zero, add_zero, TauCeti.coe_transvectionUnit, Matrix.transvection,
      Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, add_right_inj] at h2
    exact h2
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single hcomm
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    apply Matrix.GeneralLinearGroup.det_ne_zero A
    rw [← hc, map_zero, det_zero]
  refine ⟨Units.mk0 c hc0, ?_⟩
  change leviEmbedGL K n (TauCeti.diagGL fun _ => Units.mk0 c hc0) = leviEmbedGL K n A
  congr 1
  refine Units.ext ?_
  rw [TauCeti.diagGL_coe, ← hc, Matrix.scalar_apply]
  rfl

theorem exists_mem_siegelTorus_eq_conj_of_fix [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (hn : 3 ≤ n) {β : MulAut (StatedSp n K)} (hX : ∀ x ∈ siegelTorus K n, β x = x)
    (hD : ∀ d ∈ siegelLevi K n, β d = d) :
    ∃ x ∈ siegelTorus K n, β = MulAut.conj x := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨s, rfl⟩ := exists_eq_conj_of_forall_elt_fix (ρ := .difference _ _ h01) hn
    fun c => hD _ (elt_difference_mem_siegelLevi h01 c)
  have hsC : s ∈ centralizer (siegelTorus K n : Set (StatedSp n K)) :=
    mem_centralizer_iff.2 fun x hx => mul_comm_of_conj_apply_eq (hX x hx)
  rw [centralizer_siegelTorus hK] at hsC
  obtain ⟨A, rfl⟩ := hsC
  exact ⟨_, mem_siegelTorus_of_commute_elt_difference (by omega) fun i j hij =>
    mul_comm_of_conj_apply_eq (hD _ (elt_difference_mem_siegelLevi hij 1)), rfl⟩

theorem odd_card_siegelTorus [Finite K] [CharP K 2] : Odd (Nat.card (siegelTorus K n)) := by
  have h : Nat.card (siegelTorus K n) ∣ Nat.card Kˣ := card_range_dvd _
  rw [Nat.card_units] at h
  exact (odd_card_rootTorusSp (K := K) (0 : Fin 1)).of_dvd_nat
    (h.trans (by rw [card_rootTorusSp]))

theorem eq_one_of_two_pow_fix_siegelTorus [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (hn : 3 ≤ n) {β : MulAut (StatedSp n K)} (hX : ∀ x ∈ siegelTorus K n, β x = x)
    (hD : ∀ d ∈ siegelLevi K n, β d = d) {m : ℕ} (hβm : β ^ 2 ^ m = 1) : β = 1 := by
  obtain ⟨x, hx, rfl⟩ := exists_mem_siegelTorus_eq_conj_of_fix hK hn hX hD
  rw [eq_one_of_conj_pow_eq_one hβm odd_card_siegelTorus
    ((siegelTorus K n).orderOf_dvd_natCard hx), map_one]

theorem eq_one_of_isPGroup_fix_siegelTorus [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (hn : 3 ≤ n) {β : MulAut (StatedSp n K)} (hβ : IsPGroup 2 (zpowers β))
    (hX : ∀ x ∈ siegelTorus K n, β x = x) (hD : ∀ d ∈ siegelLevi K n, β d = d) : β = 1 := by
  obtain ⟨m, hm⟩ := hβ ⟨β, mem_zpowers β⟩
  exact eq_one_of_two_pow_fix_siegelTorus hK hn hX hD (m := m) (congrArg Subtype.val hm)

end Siegel

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ}

theorem congr_apply_eq_of_fix {C : Type*} [Group C] (e : L ≃* C) {A : Subgroup C}
    {Y : Subgroup G} (hAY : (A.map e.symm.toMonoidHom).map L.subtype ≤ Y) {β : MulAut L}
    (hβ : ∀ x : L, (x : G) ∈ Y → β x = x) : ∀ a ∈ A, MulAut.congr e β a = a := by
  intro a ha
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hmem : ((e.symm a : L) : G) ∈ Y := hAY ⟨e.symm a, ⟨a, ha, rfl⟩, rfl⟩
  rw [hβ _ hmem, MulEquiv.apply_symm_apply]

theorem eq_conj_symm_of_congr_eq_conj {C : Type*} [Group C] (e : L ≃* C) {β : MulAut L} {x : C}
    (h : MulAut.congr e β = MulAut.conj x) : β = MulAut.conj (e.symm x) := by
  refine MulEquiv.ext fun l => ?_
  have h1 := congrArg (fun γ : MulAut C => γ (e l)) h
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

variable [Finite K] [CharP K 2]

theorem eq_one_of_fix_map_rootTorusSp (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n)
    (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1)) {X D : Subgroup G}
    (hX : ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype ≤ X)
    (hD : ((complSp K k).map e.symm.toMonoidHom).map L.subtype ≤ D) :
    ∀ β : MulAut L, (∀ x : L, (x : G) ∈ X → β x = x) → (∀ x : L, (x : G) ∈ D → β x = x) →
      ∀ m : ℕ, β ^ 2 ^ m = 1 → β = 1 := by
  intro β hβX hβD m hβm
  have key : MulAut.congr e β = 1 :=
    eq_one_of_two_pow_fix_rootTorusSp hK hn k (congr_apply_eq_of_fix e hX hβX)
      (congr_apply_eq_of_fix e hD hβD) (m := m) (by rw [← map_pow, hβm, map_one])
  have := congrArg (MulAut.congr e).symm key
  rwa [MulEquiv.symm_apply_apply, map_one] at this

theorem card_le_two_of_rootTorusSp [Finite G] {t : G}
    (hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (ht : orderOf t = 2)
    (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n) (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1))
    {X D : Subgroup G} (hX : ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype ≤ X)
    (hD : ((complSp K k).map e.symm.toMonoidHom).map L.subtype ≤ D)
    {U : Subgroup G} (hU : IsPGroup 2 U)
    (hUC : U ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G)) :
    Nat.card U ≤ 2 :=
  F4Pilot.card_le_two_of_forall_fix_eq_one hCtN hKt ht
    (eq_one_of_fix_map_rootTorusSp hK hn e k hX hD) hU hUC

theorem exists_mem_map_rootTorusSp_eq_conj_of_fix (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n)
    (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1)) {X D : Subgroup G}
    (hX : ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype ≤ X)
    (hD : ((complSp K k).map e.symm.toMonoidHom).map L.subtype ≤ D) (β : MulAut L)
    (hβX : ∀ x : L, (x : G) ∈ X → β x = x) (hβD : ∀ x : L, (x : G) ∈ D → β x = x) :
    ∃ y : L, (y : G) ∈ ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype ∧
      β = MulAut.conj y := by
  obtain ⟨x, hx, hβ'⟩ := exists_mem_rootTorusSp_eq_conj_of_fix hK hn k
    (congr_apply_eq_of_fix e hX hβX) (congr_apply_eq_of_fix e hD hβD)
  exact ⟨e.symm x, ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩, eq_conj_symm_of_congr_eq_conj e hβ'⟩

omit [Finite K] [CharP K 2] in
theorem mem_centralizer_sup {X D : Subgroup G} {c : G} (hcX : c ∈ centralizer (X : Set G))
    (hcD : c ∈ centralizer (D : Set G)) : c ∈ centralizer ((X ⊔ D : Subgroup G) : Set G) := by
  have h : X ⊔ D ≤ centralizer ((zpowers c : Subgroup G) : Set G) :=
    sup_le (le_centralizer_iff.1 ((zpowers_le).2 hcX))
      (le_centralizer_iff.1 ((zpowers_le).2 hcD))
  exact (zpowers_le).1 (le_centralizer_iff.1 h)

theorem mem_of_odd_of_mem_centralizer_rootTorusSp [Finite G] {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n) (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1))
    {X D : Subgroup G} (hXe : X = ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X := by
  intro c hc hco
  have hXo : Odd (Nat.card X) := by
    rw [hXe, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
    exact odd_card_rootTorusSp k
  refine LinearPilot.mem_of_forall_fix_eq_conj htC ht hLt hKt (D := X ⊔ D) hXo
    (fun β hβ => ?_) hc.1.2 (mem_centralizer_sup hc.1.1 hc.2) hco
  rw [hXe]
  exact exists_mem_map_rootTorusSp_eq_conj_of_fix hK hn e k (hXe ▸ le_rfl) (hDe ▸ le_rfl) β
    (fun x hx => hβ x (mem_sup_left hx)) (fun x hx => hβ x (mem_sup_right hx))

theorem eq_one_of_fix_map_siegelTorus (hK : 4 ≤ Nat.card K) (hn : 3 ≤ n)
    (e : L ≃* StatedSp n K) {X D : Subgroup G}
    (hX : ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype ≤ X)
    (hD : ((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype ≤ D) :
    ∀ β : MulAut L, (∀ x : L, (x : G) ∈ X → β x = x) → (∀ x : L, (x : G) ∈ D → β x = x) →
      ∀ m : ℕ, β ^ 2 ^ m = 1 → β = 1 := by
  intro β hβX hβD m hβm
  have key : MulAut.congr e β = 1 :=
    eq_one_of_two_pow_fix_siegelTorus hK hn (congr_apply_eq_of_fix e hX hβX)
      (congr_apply_eq_of_fix e hD hβD) (m := m) (by rw [← map_pow, hβm, map_one])
  have := congrArg (MulAut.congr e).symm key
  rwa [MulEquiv.symm_apply_apply, map_one] at this

theorem card_le_two_of_siegelTorus [Finite G] {t : G}
    (hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (ht : orderOf t = 2)
    (hK : 4 ≤ Nat.card K) (hn : 3 ≤ n) (e : L ≃* StatedSp n K)
    {X D : Subgroup G} (hX : ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype ≤ X)
    (hD : ((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype ≤ D)
    {U : Subgroup G} (hU : IsPGroup 2 U)
    (hUC : U ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G)) :
    Nat.card U ≤ 2 :=
  F4Pilot.card_le_two_of_forall_fix_eq_one hCtN hKt ht
    (eq_one_of_fix_map_siegelTorus hK hn e hX hD) hU hUC

theorem exists_mem_map_siegelTorus_eq_conj_of_fix (hK : 4 ≤ Nat.card K) (hn : 3 ≤ n)
    (e : L ≃* StatedSp n K) {X D : Subgroup G}
    (hX : ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype ≤ X)
    (hD : ((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype ≤ D) (β : MulAut L)
    (hβX : ∀ x : L, (x : G) ∈ X → β x = x) (hβD : ∀ x : L, (x : G) ∈ D → β x = x) :
    ∃ y : L, (y : G) ∈ ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype ∧
      β = MulAut.conj y := by
  obtain ⟨x, hx, hβ'⟩ := exists_mem_siegelTorus_eq_conj_of_fix hK hn
    (congr_apply_eq_of_fix e hX hβX) (congr_apply_eq_of_fix e hD hβD)
  exact ⟨e.symm x, ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩, eq_conj_symm_of_congr_eq_conj e hβ'⟩

theorem mem_of_odd_of_mem_centralizer_siegelTorus [Finite G] {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hK : 4 ≤ Nat.card K) (hn : 3 ≤ n) (e : L ≃* StatedSp n K)
    {X D : Subgroup G} (hXe : X = ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype) :
    ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X := by
  intro c hc hco
  have hXo : Odd (Nat.card X) := by
    rw [hXe, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
    exact odd_card_siegelTorus
  refine LinearPilot.mem_of_forall_fix_eq_conj htC ht hLt hKt (D := X ⊔ D) hXo
    (fun β hβ => ?_) hc.1.2 (mem_centralizer_sup hc.1.1 hc.2) hco
  rw [hXe]
  exact exists_mem_map_siegelTorus_eq_conj_of_fix hK hn e (hXe ▸ le_rfl) (hDe ▸ le_rfl) β
    (fun x hx => hβ x (mem_sup_left hx)) (fun x hx => hβ x (mem_sup_right hx))

end Transport

end CFSG.SeitzReduction.SymplecticPilot
