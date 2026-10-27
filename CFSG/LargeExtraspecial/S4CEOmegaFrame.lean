module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.O62Normalizer
public import CFSG.LargeExtraspecial.S4CEToolTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

structure WittFrame (Q : QuadraticForm (ZMod 2) V) (a : V) (r : ℕ) where
  P : ℕ → HypPair Q
  orth : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j)
  e_zero : (P 0).e = a
  u : V
  v : V
  u_mem : u ∈ tailSpace P r
  v_mem : v ∈ tailSpace P r
  polar_uv : polar Q u v = 1

theorem orth_e_mem_perp {P P' : HypPair Q} (h : P.Orth P') : P'.e ∈ P.perp :=
  HypPair.mem_perp.mpr ⟨h.ee, h.fe⟩

theorem orth_f_mem_perp {P P' : HypPair Q} (h : P.Orth P') : P'.f ∈ P.perp :=
  HypPair.mem_perp.mpr ⟨h.ef, h.ff⟩

open CFSG.ComponentClassification.UnbalancedCatalog CFSG.LocalAnalysis.ComponentInitial in
theorem exists_wittFrame_aux [FiniteDimensional (ZMod 2) V] (hQ : Q.polarBilin.Nondegenerate)
    {a : V} (ha0 : a ≠ 0) (ha : Q a = 0) {n : ℕ} (hn : 2 ≤ n)
    (hdim : finrank (ZMod 2) V = 2 * n) : Nonempty (WittFrame Q a (n - 1)) := by
  obtain ⟨P₀, hP₀⟩ := exists_hypPair hQ ha ha0
  have hS : PolarNondegOn Q P₀.perp := by
    have := (polarNondegOn_top hQ).inf_perp P₀ Submodule.mem_top Submodule.mem_top
    rwa [top_inf_eq] at this
  have hSdim : finrank (ZMod 2) P₀.perp = 2 * (n - 1) := by
    have := finrank_inf_perp_add_two P₀ (S := ⊤) Submodule.mem_top Submodule.mem_top
    rw [finrank_top, top_inf_eq, hdim] at this
    omega
  obtain ⟨P', u, v, hP'S, hP'o, huS, hvS, huv, hpol⟩ : ∃ (P' : ℕ → HypPair Q) (u v : V),
      (∀ i < n - 2, (P' i).e ∈ P₀.perp ∧ (P' i).f ∈ P₀.perp) ∧
      (∀ i j, i < n - 2 → j < n - 2 → i ≠ j → (P' i).Orth (P' j)) ∧ u ∈ P₀.perp ∧
      v ∈ P₀.perp ∧ (∀ i < n - 2, u ∈ (P' i).perp ∧ v ∈ (P' i).perp) ∧ polar Q u v = 1 := by
    rcases exists_hypPairs_normal (n - 1) P₀.perp hS hSdim with ⟨P, hPS, hPo⟩ |
        ⟨m, hm, P, u, v, hPS, hPo, huS, hvS, huv, -, hpol, -⟩
    · set l : Fin (n - 1) := ⟨n - 2, by omega⟩ with hl
      refine ⟨fun i => if h : i < n - 1 then P ⟨i, h⟩ else P₀, (P l).e, (P l).f,
        fun i hi => ?_, fun i j hi hj hij => ?_, (hPS l).1, (hPS l).2, fun i hi => ?_,
        (P l).polar_ef⟩
      · simp only [dite_eq_left (show i < n - 1 by omega)]
        exact hPS _
      · simp only [dite_eq_left (show i < n - 1 by omega),
          dite_eq_left (show j < n - 1 by omega)]
        exact hPo _ _ (by simp [Fin.ext_iff, hij])
      · simp only [dite_eq_left (show i < n - 1 by omega)]
        have h := hPo ⟨i, by omega⟩ l (by simp [Fin.ext_iff, hl]; omega)
        exact ⟨orth_e_mem_perp h, orth_f_mem_perp h⟩
    · refine ⟨fun i => if h : i < m then P ⟨i, h⟩ else P₀, u, v, fun i hi => ?_,
        fun i j hi hj hij => ?_, huS, hvS, fun i hi => ?_,
        CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_one_of_ne_zero hpol⟩
      · simp only [dite_eq_left (show i < m by omega)]
        exact hPS _
      · simp only [dite_eq_left (show i < m by omega), dite_eq_left (show j < m by omega)]
        exact hPo _ _ (by simp [Fin.ext_iff, hij])
      · simp only [dite_eq_left (show i < m by omega)]
        exact huv _
  have hP'0 : ∀ i < n - 2, P₀.Orth (P' i) := fun i hi =>
    HypPair.orth_of_mem_perp (hP'S i hi).1 (hP'S i hi).2
  have hPk0 : ∀ k, k ≠ 0 → (if k = 0 then P₀ else P' (k - 1)) = P' (k - 1) :=
    fun k hk => ite_eq_right hk
  have hP00 : (if (0 : ℕ) = 0 then P₀ else P' (0 - 1)) = P₀ := ite_eq_left rfl
  refine ⟨⟨fun k => if k = 0 then P₀ else P' (k - 1), ?_, ?_, u, v, ?_, ?_, hpol⟩⟩
  · intro i j hi hj hij
    rcases Nat.eq_zero_or_pos i with rfl | hi0 <;> rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact absurd rfl hij
    · rw [hP00, hPk0 j hj0.ne']
      exact hP'0 _ (by omega)
    · rw [hP00, hPk0 i hi0.ne']
      exact (hP'0 _ (by omega)).symm
    · rw [hPk0 i hi0.ne', hPk0 j hj0.ne']
      exact hP'o _ _ (by omega) (by omega) (by omega)
  · rw [hP00]
    exact hP₀
  · refine mem_tailSpace.mpr fun i hi => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hP00]
      exact HypPair.mem_perp.mp huS
    · rw [hPk0 i hi0.ne']
      exact HypPair.mem_perp.mp (huv _ (by omega)).1
  · refine mem_tailSpace.mpr fun i hi => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hP00]
      exact HypPair.mem_perp.mp hvS
    · rw [hPk0 i hi0.ne']
      exact HypPair.mem_perp.mp (huv _ (by omega)).2

theorem exists_wittFrame [FiniteDimensional (ZMod 2) V] (hQ : Q.polarBilin.Nondegenerate)
    {a : V} (ha0 : a ≠ 0) (ha : Q a = 0) {r : ℕ} (hr : 1 ≤ r)
    (hdim : finrank (ZMod 2) V = 2 * (r + 1)) : Nonempty (WittFrame Q a r) := by
  simpa using exists_wittFrame_aux hQ ha0 ha (n := r + 1) (by omega) hdim

namespace WittFrame

variable {a : V} {r : ℕ} (F : WittFrame Q a r)

theorem map_a (F : WittFrame Q a r) : Q a = 0 := F.e_zero ▸ (F.P 0).Q_e

theorem a_ne_zero (F : WittFrame Q a r) : a ≠ 0 := F.e_zero ▸ (F.P 0).e_ne_zero

theorem polar_e_u {i : ℕ} (hi : i < r) : polar Q (F.P i).e F.u = 0 :=
  (mem_tailSpace.mp F.u_mem i hi).1

theorem polar_f_u {i : ℕ} (hi : i < r) : polar Q (F.P i).f F.u = 0 :=
  (mem_tailSpace.mp F.u_mem i hi).2

theorem polar_e_v {i : ℕ} (hi : i < r) : polar Q (F.P i).e F.v = 0 :=
  (mem_tailSpace.mp F.v_mem i hi).1

theorem polar_f_v {i : ℕ} (hi : i < r) : polar Q (F.P i).f F.v = 0 :=
  (mem_tailSpace.mp F.v_mem i hi).2

end WittFrame

theorem commutatorElement_eichler {a x : V} (hx : polar Q a x = 0) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hga : g a = a) :
    ⁅eichler Q a x, g⁆ = eichler Q a (x - g x) := by
  have hgx : polar Q a (g x) = 0 := by
    calc polar Q a (g x) = polar Q (g a) (g x) := by rw [hga]
      _ = 0 := by rw [polar_map_of_mem hg, hx]
  rw [commutatorElement_def, mul_assoc, mul_assoc, eichler_inv hx, ← mul_assoc g,
    eichler_conj hg, hga, map_neg, eichler_mul hx (by rw [polar_neg_right, hgx, neg_zero]),
    sub_eq_add_neg]

theorem pointRadical_le_commutator [FiniteDimensional (ZMod 2) V]
    (hQ : Q.polarBilin.Nondegenerate) {a : V} {r : ℕ} (hr : 2 ≤ r) (F : WittFrame Q a r) :
    pointRadical Q a ≤ ⁅pointRadical Q a, stabIn (omegaGroup Q hQ) a⁆ := by
  set C := ⁅pointRadical Q a, stabIn (omegaGroup Q hQ) a⁆ with hC
  have ha := F.map_a
  have hstep : ∀ x (g : V ≃ₗ[ZMod 2] V), polar Q a x = 0 → g ∈ omegaGroup Q hQ → g a = a →
      eichler Q a (x - g x) ∈ C := by
    intro x g hx hg hga
    rw [← commutatorElement_eichler hx (omegaGroup_le Q hQ hg) hga]
    exact commutator_mem_commutator (eichler_mem_pointRadical ha hx) ⟨hg, hga⟩
  have hadd : ∀ x y, polar Q a x = 0 → polar Q a y = 0 → eichler Q a x ∈ C →
      eichler Q a y ∈ C → eichler Q a (x + y) ∈ C := fun x y hx hy hxC hyC =>
    eichler_mul hx hy ▸ mul_mem hxC hyC
  have hsmul : ∀ (c : ZMod 2) x, eichler Q a x ∈ C → eichler Q a (c • x) ∈ C := by
    intro c x hx
    rcases CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_zero_or_eq_one c with rfl | rfl
    · rw [zero_smul, eichler_zero_right]
      exact one_mem _
    · rwa [one_smul]
  have h01 : (F.P 0).Orth (F.P 1) := F.orth 0 1 (by omega) (by omega) (by omega)
  set e₁ := (F.P 1).e with he₁
  set f₁ := (F.P 1).f with hf₁
  set f₀ := (F.P 0).f with hf₀
  have hae₁ : polar Q a e₁ = 0 := by have hh := h01.ee; rwa [F.e_zero] at hh
  have haf₁ : polar Q a f₁ = 0 := by have hh := h01.ef; rwa [F.e_zero] at hh
  have hau : polar Q a F.u = 0 := by
    have hh := F.polar_e_u (i := 0) (by omega)
    rwa [F.e_zero] at hh
  have hav : polar Q a F.v = 0 := by
    have hh := F.polar_e_v (i := 0) (by omega)
    rwa [F.e_zero] at hh
  have hQe₁ : Q e₁ = 0 := (F.P 1).Q_e
  have hQf₁ : Q f₁ = 0 := (F.P 1).Q_f
  have hf₁e₁ : polar Q f₁ e₁ = 1 := (F.P 1).polar_fe
  have he₁u : polar Q e₁ F.u = 0 := F.polar_e_u (by omega)
  have he₁v : polar Q e₁ F.v = 0 := F.polar_e_v (by omega)
  have hf₁u : polar Q f₁ F.u = 0 := F.polar_f_u (by omega)
  have hf₁v : polar Q f₁ F.v = 0 := F.polar_f_v (by omega)
  have hvu : polar Q F.v F.u = 1 := by rw [polar_comm]; exact F.polar_uv
  have hE1 : eichler Q a e₁ ∈ C := by
    have h := hstep F.v (eichler Q e₁ F.u) hav (O62.eichler_mem_omegaGroup hQ e₁ F.u)
      (eichler_apply_of_polar_eq_zero hae₁ hau)
    have hv : F.v - eichler Q e₁ F.u F.v = e₁ := by
      rw [eichler_apply hQe₁ he₁u, polar_comm Q F.v e₁, he₁v, hvu]
      simp
    rwa [hv] at h
  have hF1 : eichler Q a f₁ ∈ C := by
    have h := hstep F.v (eichler Q f₁ F.u) hav (O62.eichler_mem_omegaGroup hQ f₁ F.u)
      (eichler_apply_of_polar_eq_zero haf₁ hau)
    have hv : F.v - eichler Q f₁ F.u F.v = f₁ := by
      rw [eichler_apply hQf₁ hf₁u, polar_comm Q F.v f₁, hf₁v, hvu]
      simp
    rwa [hv] at h
  have hW : ∀ w ∈ tailSpace F.P 2, eichler Q a w ∈ C := by
    intro w hw
    have hw' := mem_tailSpace.mp hw
    have haw : polar Q a w = 0 := by have hh := (hw' 0 (by omega)).1; rwa [F.e_zero] at hh
    have he₁w : polar Q e₁ w = 0 := (hw' 1 (by omega)).1
    have hf₁w : polar Q f₁ w = 0 := (hw' 1 (by omega)).2
    have h := hstep f₁ (eichler Q e₁ w) haf₁ (O62.eichler_mem_omegaGroup hQ e₁ w)
      (eichler_apply_of_polar_eq_zero hae₁ haw)
    have hv : f₁ - eichler Q e₁ w f₁ = Q w • e₁ - w := by
      rw [eichler_apply hQe₁ he₁w, hf₁e₁, hf₁w]
      module
    rw [hv] at h
    have hy : polar Q a (Q w • e₁ - w) = 0 := by
      rw [polar_sub_right, polar_smul_right_eq, hae₁, haw, mul_zero, sub_zero]
    have hs : polar Q a (Q w • e₁) = 0 := by rw [polar_smul_right_eq, hae₁, mul_zero]
    have := mul_mem (hsmul (Q w) e₁ hE1) (inv_mem h)
    rwa [eichler_inv hy, eichler_mul hs (by rw [polar_neg_right, hy, neg_zero]),
      ← sub_eq_add_neg, sub_sub_cancel] at this
  intro t ht
  obtain ⟨y, hy, rfl⟩ := (mem_pointRadical_iff hQ F.a_ne_zero ha).mp ht
  have hf₀a : polar Q f₀ a = 1 := by have hh := (F.P 0).polar_fe; rwa [F.e_zero] at hh
  have hf₀e₁ : polar Q f₀ e₁ = 0 := h01.fe
  have hf₀f₁ : polar Q f₀ f₁ = 0 := h01.ff
  have he₁f₁ : polar Q e₁ f₁ = 1 := (F.P 1).polar_ef
  have he₁e₁ : polar Q e₁ e₁ = 0 := (F.P 1).polar_ee
  have hf₁f₁ : polar Q f₁ f₁ = 0 := (F.P 1).polar_ff
  have he₁a : polar Q e₁ a = 0 := by rw [polar_comm]; exact hae₁
  have hf₁a : polar Q f₁ a = 0 := by rw [polar_comm]; exact haf₁
  set w := y - polar Q y f₀ • a - polar Q y f₁ • e₁ - polar Q y e₁ • f₁ with hwdef
  have hw : w ∈ tailSpace F.P 2 := by
    refine mem_tailSpace.mpr fun i hi => ?_
    interval_cases i
    · rw [F.e_zero]
      constructor
      · rw [hwdef, polar_sub_right, polar_sub_right, polar_sub_right, polar_smul_right_eq,
          polar_smul_right_eq, polar_smul_right_eq, polar_self_eq_zero ha, hae₁, haf₁, hy]
        ring
      · rw [hwdef, polar_sub_right, polar_sub_right, polar_sub_right, polar_smul_right_eq,
          polar_smul_right_eq, polar_smul_right_eq, hf₀a, hf₀e₁, hf₀f₁, polar_comm Q f₀ y]
        ring
    · constructor
      · rw [hwdef, polar_sub_right, polar_sub_right, polar_sub_right, polar_smul_right_eq,
          polar_smul_right_eq, polar_smul_right_eq, he₁a, he₁e₁, he₁f₁, polar_comm Q e₁ y]
        ring
      · rw [hwdef, polar_sub_right, polar_sub_right, polar_sub_right, polar_smul_right_eq,
          polar_smul_right_eq, polar_smul_right_eq, hf₁a, hf₁e₁, hf₁f₁, polar_comm Q f₁ y]
        ring
  have hdecomp : y = (polar Q y e₁ • f₁ + (polar Q y f₁ • e₁ + w)) + polar Q y f₀ • a := by
    rw [hwdef]
    abel
  have haw : polar Q a w = 0 := by
    have hh := (mem_tailSpace.mp hw 0 (by omega)).1
    rwa [F.e_zero] at hh
  have hpf : polar Q a (polar Q y e₁ • f₁) = 0 := by rw [polar_smul_right_eq, haf₁, mul_zero]
  have hpe : polar Q a (polar Q y f₁ • e₁) = 0 := by rw [polar_smul_right_eq, hae₁, mul_zero]
  have hpew : polar Q a (polar Q y f₁ • e₁ + w) = 0 := by rw [polar_add_right, hpe, haw, add_zero]
  rw [hdecomp, eichler_add_smul_self ha]
  exact hadd _ _ hpf hpew (hsmul _ _ hF1) (hadd _ _ hpe haw (hsmul _ _ hE1) (hW w hw))

end CFSG.LargeExtraspecial.S4
