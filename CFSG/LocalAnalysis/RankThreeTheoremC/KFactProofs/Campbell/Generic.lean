module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Basic
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem pCoreOf_le_self (X : Subgroup A) : pCoreOf 2 X ≤ X :=
  Subgroup.map_subtype_le _

theorem isPGroup_pCoreOf (X : Subgroup A) : IsPGroup 2 (pCoreOf 2 X) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype

theorem pcore_subgroupOf_pCoreOf (X : Subgroup A) :
    (pCoreOf 2 X).subgroupOf X = CFSG.pCore 2 ↥X :=
  Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _

theorem normalizer_pCoreOf (X : Subgroup A) : X ≤ normalizer (pCoreOf 2 X : Set A) := by
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le_self X),
    pcore_subgroupOf_pCoreOf]
  exact CFSG.pCore_normal

theorem le_pCoreOf_of_normalizes {X N : Subgroup A} (hN2 : IsPGroup 2 N) (hNX : N ≤ X)
    (hnorm : X ≤ normalizer (N : Set A)) : N ≤ pCoreOf 2 X := by
  have hnormal : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hnorm
  have hp : IsPGroup 2 (N.subgroupOf X) :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNX).symm
  have hle : N.subgroupOf X ≤ CFSG.pCore 2 ↥X := le_sSup ⟨hnormal, hp⟩
  have h2 := Subgroup.map_mono (f := X.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hNX] at h2

theorem pCoreOf_le_of_odd_index {X S : Subgroup A} (hS : IsPGroup 2 S) (hSX : S ≤ X)
    (hidx : ¬ 2 ∣ (S.subgroupOf X).index) : pCoreOf 2 X ≤ S := by
  have hSp : IsPGroup 2 (S.subgroupOf X) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm
  let Q : Sylow 2 ↥X := hSp.toSylow hidx
  have h1 : CFSG.pCore 2 ↥X ≤ S.subgroupOf X :=
    CFSG.pCore_isPGroup.le_sylow_of_normal Q
  have h2 := Subgroup.map_mono (f := X.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hSX] at h2
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise commutatorElement

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem normalizer_omegaCenter {N Y : Subgroup A} (hY : Y ≤ normalizer (N : Set A)) :
    Y ≤ normalizer (omegaCenter N : Set A) :=
  hY.trans (normalizer_le_normalizer_omegaCenter N)

private theorem normalizer_conj_commutator_mem {H L : Subgroup A} {g : A}
    (hH : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hL : ∀ x ∈ L, g * x * g⁻¹ ∈ L) :
    ∀ x ∈ (⁅H, L⁆ : Subgroup A), g * x * g⁻¹ ∈ (⁅H, L⁆ : Subgroup A) := by
  have key : (⁅H, L⁆ : Subgroup A) ≤
      (⁅H, L⁆ : Subgroup A).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro h hh l hl
    rw [Subgroup.mem_comap]
    show g * ⁅h, l⁆ * g⁻¹ ∈ (⁅H, L⁆ : Subgroup A)
    rw [conjugate_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hH h hh) (hL l hl)
  intro x hx
  exact key hx

theorem normalizer_commutator_of_normalizes {H L Y : Subgroup A}
    (hH : Y ≤ normalizer (H : Set A)) (hL : Y ≤ normalizer (L : Set A)) :
    Y ≤ normalizer ((⁅H, L⁆ : Subgroup A) : Set A) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact normalizer_conj_commutator_mem
      (fun y hy => (Subgroup.mem_normalizer_iff.1 (hH hg) y).1 hy)
      (fun y hy => (Subgroup.mem_normalizer_iff.1 (hL hg) y).1 hy) x hx
  · intro hx
    have h := normalizer_conj_commutator_mem (g := g⁻¹)
      (fun y hy => (Subgroup.mem_normalizer_iff.1 (hH (Y.inv_mem hg)) y).1 hy)
      (fun y hy => (Subgroup.mem_normalizer_iff.1 (hL (Y.inv_mem hg)) y).1 hy) _ hx
    simpa [mul_assoc] using h

theorem omegaOneCenterOf_eq_omegaCenter (S : Subgroup A) :
    CFSG.Quasithin.omegaOneCenterOf S = omegaCenter S := by
  have hset : {x | x ∈ CFSG.Quasithin.centerOf S ∧ x ^ 2 = 1} = (omegaCenter S : Set A) := by
    ext x
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_omegaCenter, CFSG.Quasithin.centerOf,
      Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨⟨hxS, hxc⟩, hx2⟩
      exact ⟨hxS, fun s hs => (hxc s hs).symm, hx2⟩
    · rintro ⟨hxS, hxc, hx2⟩
      exact ⟨⟨hxS, fun s hs => (hxc s hs).symm⟩, hx2⟩
  show Subgroup.closure {x | x ∈ CFSG.Quasithin.centerOf S ∧ x ^ 2 = 1} = omegaCenter S
  rw [hset, Subgroup.closure_eq]

theorem normalizer_inf_of_normalizes {B C Y : Subgroup A} (hB : Y ≤ normalizer (B : Set A))
    (hC : Y ≤ normalizer (C : Set A)) : Y ≤ normalizer ((B ⊓ C : Subgroup A) : Set A) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.1 (hB hg) x
  have h2 := Subgroup.mem_normalizer_iff.1 (hC hg) x
  simp only [Subgroup.mem_inf]
  tauto
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem bot_conditions (X K : Subgroup A) :
    K ≤ centralizer ((⊥ : Subgroup A) : Set A) ∧ X ≤ normalizer ((⊥ : Subgroup A) : Set A) := by
  refine ⟨fun k _ => ?_, fun g _ => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
    rw [hh, one_mul, mul_one]
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [Subgroup.mem_bot] at hh ⊢
      rw [hh]
      group
    · intro hh
      rw [Subgroup.mem_bot] at hh ⊢
      have : g * h * g⁻¹ = 1 := hh
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group

theorem mem_normalizer_centralizer_of_mem_normalizer {K : Subgroup A} {g : A}
    (hg : g ∈ normalizer (K : Set A)) :
    g ∈ normalizer ((centralizer (K : Set A) : Subgroup A) : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g : A, g ∈ normalizer (K : Set A) → ∀ c ∈ centralizer (K : Set A),
      g * c * g⁻¹ ∈ centralizer (K : Set A) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : g⁻¹ * k * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff''.1 hg k).1 hk
      simpa using this
    have hc' := (Subgroup.mem_centralizer_iff.1 hc) (g⁻¹ * k * g) hk'
    calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc']
      _ = g * c * g⁻¹ * k := by group
  intro h
  refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have hg' : g⁻¹ ∈ normalizer (K : Set A) := inv_mem hg
  have := key g⁻¹ hg' _ hh
  simpa [mul_assoc] using this

theorem CampbellHyp.c134CQ_conditions (h : CampbellHyp X K R P) :
    K ≤ centralizer ((CFSG.Quasithin.c134CQ X K : Subgroup A) : Set A) ∧
      X ≤ normalizer ((CFSG.Quasithin.c134CQ X K : Subgroup A) : Set A) := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact ((Subgroup.mem_centralizer_iff.1 hc.2) k hk).symm
  · have hQ : X ≤ normalizer ((CFSG.Quasithin.c134Q X K : Subgroup A) : Set A) :=
      normalizer_commutator_of_normalizes (normalizer_pCoreOf X) h.K_normal
    have hC : X ≤ normalizer ((centralizer (K : Set A) : Subgroup A) : Set A) :=
      fun g hg => mem_normalizer_centralizer_of_mem_normalizer (h.K_normal hg)
    exact normalizer_inf_of_normalizes hQ hC
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem closure_odd_of_perfect {K : Subgroup A} (hK : ⁅K, K⁆ = K) :
    K ≤ Subgroup.closure {k | k ∈ K ∧ Odd (orderOf k)} := by
  haveI hperf : Group.IsPerfect K := Subgroup.isPerfect_iff.2 hK
  haveI hN : ((CFSG.Quasithin.opResidual 2 K).subgroupOf K).Normal :=
    CFSG.Quasithin.opResidual_normal 2 K
  have hpg : IsPGroup 2 (K ⧸ (CFSG.Quasithin.opResidual 2 K).subgroupOf K) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := CFSG.Quasithin.exists_pow_mem_opResidual (p := 2) (A := K) x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hk
  haveI : Subsingleton (K ⧸ (CFSG.Quasithin.opResidual 2 K).subgroupOf K) := by
    by_contra hns
    haveI : Nontrivial (K ⧸ (CFSG.Quasithin.opResidual 2 K).subgroupOf K) :=
      not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isNilpotent _ hpg.isNilpotent
  have hres : CFSG.Quasithin.opResidual 2 K =
      Subgroup.closure {k | k ∈ K ∧ Odd (orderOf k)} := by
    simp only [CFSG.Quasithin.opResidual, Nat.coprime_two_right]
  intro x hx
  rw [← hres]
  have hx1 : (QuotientGroup.mk ⟨x, hx⟩ :
      K ⧸ (CFSG.Quasithin.opResidual 2 K).subgroupOf K) = 1 := Subsingleton.elim _ _
  exact (Subgroup.mem_subgroupOf).1 ((QuotientGroup.eq_one_iff _).1 hx1)

theorem centralizes_of_odd_generation {K : Subgroup A}
    (hKgen : K ≤ Subgroup.closure {k | k ∈ K ∧ Odd (orderOf k)}) {e : A}
    (h : ∀ k ∈ K, Odd (orderOf k) →
      (e⁻¹ * (k * e * k⁻¹)) ^ 2 = 1 ∧ k * (e⁻¹ * (k * e * k⁻¹)) * k⁻¹ = e⁻¹ * (k * e * k⁻¹) ∧
        e * (e⁻¹ * (k * e * k⁻¹)) = (e⁻¹ * (k * e * k⁻¹)) * e) :
    ∀ k ∈ K, k * e * k⁻¹ = e := by
  have hodd : ∀ k ∈ K, Odd (orderOf k) → k * e = e * k := by
    intro k hk hko
    obtain ⟨hc2, hkc, -⟩ := h k hk hko
    set c : A := e⁻¹ * (k * e * k⁻¹) with hc
    have hke : k * e * k⁻¹ = e * c := by rw [hc, mul_inv_cancel_left]
    have hpow : ∀ j : ℕ, k ^ j * e * (k ^ j)⁻¹ = e * c ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have h1 : k ^ (j + 1) * e * (k ^ (j + 1))⁻¹ = k * (k ^ j * e * (k ^ j)⁻¹) * k⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          simp only [mul_assoc]
        have h2 : k * c ^ j * k⁻¹ = c ^ j := by
          have := map_pow (MulAut.conj k) c j
          simp only [MulAut.conj_apply] at this
          rw [this, hkc]
        have h3 : k * (e * c ^ j) * k⁻¹ = (k * e * k⁻¹) * (k * c ^ j * k⁻¹) := by
          have := map_mul (MulAut.conj k) e (c ^ j)
          simpa only [MulAut.conj_apply] using this
        rw [h1, ih, h3, h2, hke, pow_succ', mul_assoc]
    have h4 := hpow (orderOf k)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h4
    obtain ⟨m, hm⟩ := hko
    have h5 : c ^ orderOf k = c := by
      rw [hm, pow_succ, pow_mul, hc2, one_pow, one_mul]
    rw [h5] at h4
    have hc1 : c = 1 := by
      have : e * c = e * 1 := by rw [mul_one]; exact h4.symm
      exact mul_left_cancel this
    rw [hc1, mul_one] at hke
    calc k * e = (k * e * k⁻¹) * k := by rw [inv_mul_cancel_right]
      _ = e * k := by rw [hke]
  have hsub : Subgroup.closure {k | k ∈ K ∧ Odd (orderOf k)} ≤ Subgroup.centralizer {e} := by
    rw [Subgroup.closure_le]
    rintro k ⟨hk, hko⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hodd k hk hko
  intro k hk
  have hk' := Subgroup.mem_centralizer_singleton_iff.1 (hsub (hKgen hk))
  rw [hk', mul_inv_cancel_right]
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell
