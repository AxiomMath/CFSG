module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR7iiiAut
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionB
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionPerfectOdd
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore perfectCore_le)

section Radical

variable {n k : ℕ} {K : Type*} [Field K]

theorem commutator_radicalP_le_blockSL (P : InvPlacement n k) :
    ⁅P.radicalP K, P.radicalP K⁆ ≤ blockSL (K := K) P.outer := by
  rw [InvPlacement.radicalP, ← Subgroup.map_commutator]
  exact Subgroup.map_mono P.commutator_radical_le

theorem proj_transvection_mem_commutator_radicalP (P : InvPlacement n k) (hJ : P.free.Nonempty)
    (a b : Fin k) (c : K) :
    LinearFlag.proj n K (Matrix.SpecialLinearGroup.transvection (P.u_ne_w a b) c) ∈
      ⁅P.radicalP K, P.radicalP K⁆ := by
  rw [InvPlacement.radicalP, ← Subgroup.map_commutator]
  exact Subgroup.mem_map_of_mem _ (P.transvection_u_w_mem_commutator hJ a b c)

end Radical

section Induced

variable {G : Type*} [Group G] {n : ℕ} {K : Type*} [Field K]

theorem map_normalizerAut_ofInjective_apply {φ' : LinearFlag.projectiveSL n K →* G}
    (hφ' : Function.Injective φ') (x : normalizer (φ'.range : Set G))
    (p : LinearFlag.projectiveSL n K) :
    φ' (normalizerAut (MonoidHom.ofInjective hφ').symm x p) = x * φ' p * x⁻¹ := by
  have h := coe_symm_normalizerAut_apply (MonoidHom.ofInjective hφ').symm x
    (MonoidHom.ofInjective hφ' p)
  rw [MulEquiv.symm_symm, MulEquiv.symm_apply_apply, MonoidHom.ofInjective_apply,
    MonoidHom.ofInjective_apply] at h
  exact h

end Induced

section Coordinates

variable {G : Type*} [Group G] [Finite G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {φ φ' : LinearFlag.projectiveSL 4 K →* G}

omit [Finite G] [Finite K] in
theorem proj_transvection_not_mem_commutator_radicalP {k : ℕ} (P : InvPlacement 4 k) {u d : Fin 4}
    (hud : u ≠ d) (hd : P.level d = 1) :
    LinearFlag.proj 4 K (Matrix.SpecialLinearGroup.transvection hud 1) ∉
      ⁅P.radicalP K, P.radicalP K⁆ := by
  rw [InvPlacement.radicalP, ← Subgroup.map_commutator]
  rintro ⟨M, hM, hMeq⟩
  have h1 := proj_four_injective hMeq
  subst h1
  have h2 := P.commutator_radical_apply_eq hM (i := u) (j := d) (by rw [hd]; omega)
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_ne hud,
    Matrix.single_apply_same, zero_add] at h2
  exact one_ne_zero h2

theorem exists_le_range_inf_centralizer_mulEquiv_levi (hq : 4 ≤ Nat.card K)
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ') (P : InvPlacement 4 1) {k' : ℕ}
    (P' : InvPlacement 4 k') (hk' : 0 < k') {a : Fin 4}
    (hPout : P.outer ⊆ ({a}ᶜ : Finset (Fin 4)))
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ')
    {x : G} (hxodd : Odd (orderOf x))
    (hxD : ∀ d ∈ (blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map φ, x * d = d * x)
    (hxN : x ∈ normalizer (φ'.range : Set G)) :
    ∃ P₀ : Subgroup G, P₀ ≤ φ'.range ⊓ centralizer ({x} : Set G) ∧
      Nonempty (P₀ ≃* blockSL (K := K) ({a}ᶜ : Finset (Fin 4))) := by
  classical
  have hfree2 : P.free.card = 2 := by rw [P.card_free]
  have haJ : a ∈ P.free := P.compl_subset_free_of_outer_subset hPout (by simp)
  have hJ'2 := two_le_card_free_of_map_perfectCore_eq hq le_rfl hφ hφ' P P' one_pos (by omega) hΛ
  have hcard := card_free_eq_of_map_perfectCore_eq hq hφ hφ' P P' one_pos hk' (by omega) hJ'2 hΛ
  have hk'1 : k' = 1 := by
    have := P'.card_free
    omega
  subst hk'1
  have hQeq := map_radicalP_eq hq hφ hφ' P P' (by omega) hJ'2 hΛ
  have hQQ : (⁅P'.radicalP K, P'.radicalP K⁆).map φ' = (⁅P.radicalP K, P.radicalP K⁆).map φ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hQeq]
  have hxQQ : ∀ z ∈ ⁅P.radicalP K, P.radicalP K⁆, x * φ z = φ z * x := fun z hz =>
    hxD _ (mem_map_of_mem φ (blockSL_mono hPout (commutator_radicalP_le_blockSL P hz)))
  set β := normalizerAut (MonoidHom.ofInjective hφ').symm ⟨x, hxN⟩ with hβdef
  have hβ : ∀ p, φ' (β p) = x * φ' p * x⁻¹ := fun p =>
    map_normalizerAut_ofInjective_apply hφ' ⟨x, hxN⟩ p
  have hβfix : ∀ p, x * φ' p = φ' p * x → β p = p := fun p hp =>
    hφ' (by rw [hβ, hp, mul_inv_cancel_right])
  have hβm : β ^ orderOf x = 1 := by
    rw [hβdef, ← map_pow]
    have h1 : (⟨x, hxN⟩ : normalizer (φ'.range : Set G)) ^ orderOf x = 1 :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow, pow_orderOf_eq_one, OneMemClass.coe_one])
    rw [h1, map_one]
  have hJ'ne : P'.free.Nonempty := Finset.card_pos.1 (by omega)
  have hβR : ∀ c : K, β (LinearFlag.proj 4 K
      (Matrix.SpecialLinearGroup.transvection (P'.u_ne_w 0 0) c)) =
      LinearFlag.proj 4 K (Matrix.SpecialLinearGroup.transvection (P'.u_ne_w 0 0) c) := by
    intro c
    refine hβfix _ ?_
    have hmem : φ' (LinearFlag.proj 4 K
        (Matrix.SpecialLinearGroup.transvection (P'.u_ne_w 0 0) c)) ∈
        (⁅P.radicalP K, P.radicalP K⁆).map φ := by
      rw [← hQQ]
      exact mem_map_of_mem φ' (proj_transvection_mem_commutator_radicalP P' hJ'ne 0 0 c)
    obtain ⟨z, hz, hzeq⟩ := hmem
    rw [← hzeq]
    exact hxQQ z hz
  obtain ⟨d, hdJ, hda⟩ := Finset.exists_mem_ne (by omega : 1 < P.free.card) a
  have hud : P.u 0 ≠ d := fun h => P.u_not_mem_free 0 (h ▸ hdJ)
  have hdlev : P.level d = 1 := P.mem_free.1 hdJ
  set r := LinearFlag.proj 4 K (Matrix.SpecialLinearGroup.transvection hud 1) with hrdef
  have hrQ : r ∈ P.radicalP K :=
    mem_map_of_mem _ (P.transvection_mem_radical hud (by rw [P.level_u, hdlev]; omega) 1)
  have hrD : r ∈ blockSL (K := K) ({a}ᶜ : Finset (Fin 4)) :=
    proj_transvection_mem_blockSL hud (hPout (P.u_mem_outer 0)) (by simpa using hda) 1
  have hrQQ := proj_transvection_not_mem_commutator_radicalP (K := K) P hud hdlev
  obtain ⟨r', hr', hr'eq⟩ : φ r ∈ (P'.radicalP K).map φ' := hQeq ▸ mem_map_of_mem φ hrQ
  obtain ⟨R, hR, rfl⟩ := hr'
  have hβr : β (LinearFlag.proj 4 K R) = LinearFlag.proj 4 K R := by
    refine hβfix _ ?_
    rw [hr'eq]
    exact hxD _ (mem_map_of_mem φ hrD)
  have hRQ : ∃ i j, (R : Matrix (Fin 4) (Fin 4) K) i j ≠ (1 : Matrix (Fin 4) (Fin 4) K) i j ∧
      ¬ (i = P'.u 0 ∧ j = P'.w 0) := by
    by_contra hcon
    push Not at hcon
    have hRt : R = Matrix.SpecialLinearGroup.transvection (P'.u_ne_w 0 0)
        ((R : Matrix (Fin 4) (Fin 4) K) (P'.u 0) (P'.w 0)) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.transvection_coe]
      ext i j
      by_cases hij : i = P'.u 0 ∧ j = P'.w 0
      · obtain ⟨rfl, rfl⟩ := hij
        rw [Matrix.add_apply, Matrix.one_apply_ne (P'.u_ne_w 0 0), Matrix.single_apply_same,
          zero_add]
      · have h1 := hcon i j
        have h3 : Matrix.single (P'.u 0) (P'.w 0) ((R : Matrix (Fin 4) (Fin 4) K) (P'.u 0) (P'.w 0))
            i j = 0 := by
          rw [Matrix.single_apply]
          exact ite_eq_right (fun h => hij ⟨h.1.symm, h.2.symm⟩)
        rw [Matrix.add_apply, h3, add_zero]
        by_contra h2
        exact hij (h1 h2)
    apply hrQQ
    have hmem : φ' (LinearFlag.proj 4 K R) ∈ (⁅P.radicalP K, P.radicalP K⁆).map φ := by
      rw [← hQQ, hRt]
      exact mem_map_of_mem φ' (proj_transvection_mem_commutator_radicalP P' hJ'ne 0 0 _)
    obtain ⟨z, hz, hzeq⟩ := hmem
    rw [hr'eq] at hzeq
    have hzr := hφ hzeq
    rw [hzr] at hz
    exact hz
  obtain ⟨g', b, hfix⟩ := exists_conjAut_blockSL_fix P' hxodd hβm hβR hR hRQ hβr
  refine ⟨((blockSL (K := K) ({b}ᶜ : Finset (Fin 4))).map
    (LinearFlag.conjAut 4 K g').toMonoidHom).map φ', le_inf ?_ ?_, ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    exact ⟨p, rfl⟩
  · rintro _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := hβ (LinearFlag.conjAut 4 K g' h)
    rw [hfix h hh] at h1
    have h2 := congrArg (· * x) h1
    simp only [inv_mul_cancel_right] at h2
    simp only [MulEquiv.coe_toMonoidHom]
    exact h2
  · have hcardb : (({b}ᶜ : Finset (Fin 4))).card < 4 := by
      rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
      omega
    have hcardab : (({b}ᶜ : Finset (Fin 4))).card = (({a}ᶜ : Finset (Fin 4))).card := by
      rw [Finset.card_compl, Finset.card_compl, Finset.card_singleton, Finset.card_singleton]
    obtain ⟨eB⟩ := blockSL_mulEquiv_blockSL (K := K) hcardb hcardab
    exact ⟨((((blockSL (K := K) ({b}ᶜ : Finset (Fin 4))).map
      (LinearFlag.conjAut 4 K g').toMonoidHom).equivMapOfInjective φ' hφ').symm.trans
      (((blockSL (K := K) ({b}ᶜ : Finset (Fin 4)))).equivMapOfInjective _
        (LinearFlag.conjAut 4 K g').injective).symm).trans eB⟩

end Coordinates

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_conjugate_of_mul_mul_inv_mem {g x : G}
    (hx : g * x * g⁻¹ ∈ normalizer (L : Set G)) :
    x ∈ normalizer (CFSG.conjugate L g : Set G) := by
  have hmem : ∀ z, z ∈ CFSG.conjugate L g ↔ g * z * g⁻¹ ∈ L := fun z => by
    constructor
    · rintro ⟨l, hl, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [show g * (g⁻¹ * l * g) * g⁻¹ = l by group]
      exact hl
    · intro hz
      exact ⟨g * z * g⁻¹, hz, by simp [mul_assoc]⟩
  rw [mem_normalizer_iff] at hx ⊢
  intro h
  rw [hmem, hmem, hx (g * h * g⁻¹)]
  constructor <;> intro h' <;> convert h' using 1 <;> group

theorem exists_le_centralizer_mulEquiv_of_conj_eq_mul_levi (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (a : Fin 4) {X : Subgroup G} (hXcyc : IsCyclic X) (hXodd : Odd (Nat.card X))
    (hXt : X ≤ centralizer ({t} : Set G))
    (hDX : ((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map e.symm.toMonoidHom).map L.subtype ≤
      centralizer (X : Set G)) {g y : G}
    (hyD : y ∈ ((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map e.symm.toMonoidHom).map L.subtype)
    (hy : orderOf y = 2) (hg : g⁻¹ * t * g = t * y) :
    ∃ g₁ y₁ : G,
      y₁ ∈ ((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map e.symm.toMonoidHom).map L.subtype ∧
      orderOf y₁ = 2 ∧ g₁⁻¹ * t * g₁ = t * y₁ ∧
      ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓ centralizer ({t * y₁} : Set G) ∧
        Nonempty (P ≃* ((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map
          e.symm.toMonoidHom).map L.subtype) := by
  classical
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  set φ : LinearFlag.projectiveSL 4 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := EPilot.range_subtype_comp_mulEquiv_symm e
  have hφL : ∀ x, φ x ∈ L := fun x => hφr ▸ ⟨x, rfl⟩
  have hmap : ∀ H : Subgroup (LinearFlag.projectiveSL 4 K),
      (H.map e.symm.toMonoidHom).map L.subtype = H.map φ := fun H => by
    rw [Subgroup.map_map]
  rw [hmap] at hyD hDX ⊢
  obtain ⟨y₀, hy₀D, rfl⟩ := hyD
  have hy₀2 : y₀ * y₀ = 1 := by
    apply hφ
    rw [map_mul, map_one, ← sq, ← hy, pow_orderOf_eq_one]
  have hy₀1 : y₀ ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have hIcard : ({a}ᶜ : Finset (Fin 4)).card < 4 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  obtain ⟨k, P, c, hPout, hc⟩ := exists_conj_eq_elt_of_mem_blockSL hIcard hy₀D hy₀2
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · exfalso
      apply hy₀1
      rw [P.elt_eq_one_of_eq_zero h0] at hc
      calc y₀ = c⁻¹ * (c * y₀ * c⁻¹) * c := by group
        _ = 1 := by rw [hc]; group
    · exact h
  have hk1 : k = 1 := by
    have haJ : a ∈ P.free := P.compl_subset_free_of_outer_subset hPout (by simp)
    have h1 : 1 ≤ P.free.card := Finset.card_pos.2 ⟨a, haJ⟩
    rw [P.card_free] at h1
    omega
  subst hk1
  set y₁ := φ (P.elt K) with hy₁def
  set g₁ := g * (φ c)⁻¹ with hg₁def
  have htc : φ c * t = t * φ c := mem_centralizer_iff.1 htC _ (hφL c)
  have hy₁c : y₁ = φ c * φ y₀ * (φ c)⁻¹ := by
    rw [hy₁def, ← hc, map_mul, map_mul, map_inv]
  have hg₁ : g₁⁻¹ * t * g₁ = t * y₁ := by
    have e1 : g₁⁻¹ * t * g₁ = φ c * (g⁻¹ * t * g) * (φ c)⁻¹ := by rw [hg₁def]; group
    rw [e1, hg, hy₁c]
    calc φ c * (t * φ y₀) * (φ c)⁻¹ = (φ c * t) * φ y₀ * (φ c)⁻¹ := by group
      _ = t * (φ c * φ y₀ * (φ c)⁻¹) := by rw [htc]; group
  have hy₁D : y₁ ∈ (blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map φ :=
    ⟨P.elt K, P.elt_mem_blockSL hPout, rfl⟩
  have hy₁sq : y₁ * y₁ = 1 := by
    rw [hy₁def, ← map_mul, InvPlacement.elt, ← map_mul, P.mat_mul_self, map_one, map_one]
  have hy₁1 : y₁ ≠ 1 := by
    rw [hy₁c]
    intro h
    apply hy₀1
    apply hφ
    rw [map_one]
    calc φ y₀ = (φ c)⁻¹ * (φ c * φ y₀ * (φ c)⁻¹) * φ c := by group
      _ = 1 := by rw [h]; group
  have hy₁2 : orderOf y₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hy₁sq) hy₁1
  refine ⟨g₁, y₁, hy₁D, hy₁2, hg₁, ?_⟩
  have ht'C : g₁⁻¹ * t * g₁ ∈ centralizer (CFSG.conjugate L g₁ : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.1 (EPilot.conjugate_le_centralizer_conj htC g₁ hl)
  have hy₁inv : y₁⁻¹ = y₁ := inv_eq_of_mul_eq_one_right hy₁sq
  have hty₁ : y₁ * t = t * y₁ := mem_centralizer_iff.1 htC _ (hφL _)
  have hw' : y₁⁻¹ * t ∈ centralizer (CFSG.conjugate L g₁ : Set G) := by
    rw [hy₁inv, hty₁, ← hg₁]
    exact ht'C
  have hΛeq := EPilot.perfectCore_inf_centralizer_eq_of_inv_mul_mem hset hOut htC ht
    (Or.inr hg₁) hw'
  have hΛ0 : (perfectCore (centralizer {P.elt K})).map φ =
      perfectCore (L ⊓ centralizer ({y₁} : Set G)) := by
    rw [map_perfectCore_centralizer_singleton hφ, hφr]
  have hJ2 : 2 ≤ 4 - 2 * 1 := le_rfl
  have hy₁Λ : y₁ ∈ perfectCore (L ⊓ centralizer ({y₁} : Set G)) := by
    rw [← hΛ0]
    obtain ⟨-, hΛP, -, -, -⟩ := P.centralizer_inv_perfectCore hq hJ2
    refine mem_map_of_mem φ ?_
    rw [hΛP]
    exact mem_sup_left P.elt_mem_radicalP
  have hy₁L' : y₁ ∈ CFSG.conjugate L g₁ := by
    rw [hΛeq] at hy₁Λ
    exact ((perfectCore_le _).trans inf_le_left) hy₁Λ
  set φ'₀ : LinearFlag.projectiveSL 4 K →* G := (MulAut.conj g₁⁻¹).toMonoidHom.comp φ
    with hφ'₀def
  have hφ'₀ : Function.Injective φ'₀ := (MulAut.conj g₁⁻¹).injective.comp hφ
  have hφ'₀r : φ'₀.range = CFSG.conjugate L g₁ := by
    rw [hφ'₀def, MonoidHom.range_comp, hφr]
    rfl
  obtain ⟨z₀, hz₀⟩ : y₁ ∈ φ'₀.range := hφ'₀r ▸ hy₁L'
  have hz₀2 : z₀ * z₀ = 1 := hφ'₀ (by rw [map_mul, hz₀, hy₁sq, map_one])
  obtain ⟨k', P', c', hc'⟩ := exists_conj_eq_elt hz₀2
  set φ' : LinearFlag.projectiveSL 4 K →* G := φ'₀.comp (MulAut.conj c'⁻¹).toMonoidHom
    with hφ'def
  have hφ' : Function.Injective φ' := hφ'₀.comp (MulAut.conj c'⁻¹).injective
  have hφ'r : φ'.range = CFSG.conjugate L g₁ := by
    rw [hφ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, hφ'₀r]
  have hφ'P' : φ' (P'.elt K) = y₁ := by
    rw [hφ'def, MonoidHom.comp_apply, ← hc', ← hz₀]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hk' : 0 < k' := by
    rcases Nat.eq_zero_or_pos k' with h0 | h
    · exfalso
      apply hy₁1
      rw [← hφ'P', P'.elt_eq_one_of_eq_zero h0, map_one]
    · exact h
  have hΛ1 : (perfectCore (centralizer {P'.elt K})).map φ' =
      perfectCore (CFSG.conjugate L g₁ ⊓ centralizer ({y₁} : Set G)) := by
    rw [map_perfectCore_centralizer_singleton hφ', hφ'r, hφ'P']
  have hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ' := by
    rw [hΛ0, hΛ1, hΛeq]
  obtain ⟨x, hx⟩ := hXcyc.exists_generator
  have hxodd : Odd (orderOf (x : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hXodd.of_dvd_nat (orderOf_dvd_natCard x)
  have hxD : ∀ d ∈ (blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map φ, (x : G) * d = d * x :=
    fun d hd => mem_centralizer_iff.1 (hDX hd) x x.2
  have hxt : (x : G) * t = t * x := mem_centralizer_singleton_iff.1 (hXt x.2)
  have hxy₁ : (x : G) * y₁ = y₁ * x := hxD y₁ hy₁D
  have hxN : (x : G) ∈ normalizer (φ'.range : Set G) := by
    rw [hφ'r]
    refine mem_normalizer_conjugate_of_mul_mul_inv_mem
      (centralizer_le_normalizer_of_standard hset.standard htC ht ?_)
    rw [mem_centralizer_singleton_iff]
    have h1 : (x : G) * (g₁⁻¹ * t * g₁) = (g₁⁻¹ * t * g₁) * x := by
      rw [hg₁]
      calc (x : G) * (t * y₁) = ((x : G) * t) * y₁ := by group
        _ = t * ((x : G) * y₁) := by rw [hxt]; group
        _ = t * y₁ * x := by rw [hxy₁]; group
    calc g₁ * x * g₁⁻¹ * t = g₁ * ((x : G) * (g₁⁻¹ * t * g₁)) * g₁⁻¹ := by group
      _ = g₁ * ((g₁⁻¹ * t * g₁) * x) * g₁⁻¹ := by rw [h1]
      _ = t * (g₁ * x * g₁⁻¹) := by group
  obtain ⟨P₀, hP₀, ⟨eP₀⟩⟩ := exists_le_range_inf_centralizer_mulEquiv_levi hq hφ hφ' P P' hk'
    hPout hΛ hxodd hxD hxN
  refine ⟨P₀, le_inf ?_ ?_,
    ⟨eP₀.trans ((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).equivMapOfInjective φ hφ)⟩⟩
  · intro p hp
    rw [mem_centralizer_iff]
    intro z hz
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hx ⟨z, hz⟩)
    have hpx : Commute (x : G) p :=
      (mem_centralizer_singleton_iff.1 ((hP₀.trans inf_le_right) hp)).symm
    have hz' : z = (x : G) ^ m := by
      have h := congrArg Subtype.val hm
      simp only [SubgroupClass.coe_zpow] at h
      exact h.symm
    rw [hz']
    exact (hpx.zpow_left m).eq
  · have hP₀L : P₀ ≤ CFSG.conjugate L g₁ := hφ'r ▸ hP₀.trans inf_le_left
    rw [← hg₁]
    exact hP₀L.trans (EPilot.conjugate_le_centralizer_conj htC g₁)

theorem not_normal_map_oddCore_of_conj_eq_mul_levi (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (a : Fin 4) {X : Subgroup G} (hXcyc : IsCyclic X) (hXodd : Odd (Nat.card X))
    (hXt : X ≤ centralizer ({t} : Set G))
    (hDX : ((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map e.symm.toMonoidHom).map L.subtype ≤
      centralizer (X : Set G)) {g y : G}
    (hyD : y ∈ ((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map e.symm.toMonoidHom).map L.subtype)
    (hy : orderOf y = 2) (hg : g⁻¹ * t * g = t * y)
    (hDq : CFSG.Open.IsQuasisimple
      (((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map e.symm.toMonoidHom).map L.subtype))
    (hZD : Odd (Nat.card (center
      (((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map e.symm.toMonoidHom).map L.subtype))))
    (hOutD : Group.IsSolvable (Outer
      ((((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map e.symm.toMonoidHom).map L.subtype) ⧸
        center (((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map e.symm.toMonoidHom).map
          L.subtype))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer (((((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map
          e.symm.toMonoidHom).map L.subtype).subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ (((((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map e.symm.toMonoidHom).map
        L.subtype).subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have hDt : ((blockSL (K := K) ({a}ᶜ : Finset (Fin 4))).map e.symm.toMonoidHom).map
      L.subtype ≤ centralizer ({t} : Set G) :=
    (map_subtype_le _).trans (le_centralizer_of_mem_centralizer htK.1)
  have htX : t ∈ centralizer (X : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.1 (hXt hx)
  obtain ⟨-, y₁, hy₁D, hy₁, -, P, hP, hPD⟩ :=
    exists_le_centralizer_mulEquiv_of_conj_eq_mul_levi hset hOut hq e ht hKt a hXcyc hXodd hXt hDX
      hyD hy hg
  exact not_normal_map_oddCore_centralizer_of_mulEquiv_of_odd_center htX ht hDX hDq hZD hOutD hDt
    hsyl hy₁D hy₁ (Or.inr rfl) hP hPD

end Setting

end CFSG.SeitzReduction.LinearPilot
