module

public import CFSG.LargeExtraspecial.AS35ZSDisjA
public import CFSG.LargeExtraspecial.AS35ZSBlk

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZS

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary QuadraticMap
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem exists_herm_eq {w : Fin m → K} (hw : w ≠ 0) (c : K) : ∃ t, herm frob t w = c := by
  obtain ⟨t₀, ht₀⟩ := exists_herm_ne_zero frob hw
  have h1 : herm frob t₀ w ≠ 0 := by
    rw [herm_conj frob frob_frob]
    exact frob_ne_zero ht₀
  refine ⟨frob (c / herm frob t₀ w) • t₀, ?_⟩
  rw [herm_smul_left, frob_frob, div_mul_cancel₀ c h1]

theorem exists_std_pair (hm : 2 ≤ m) {x y : Fin (m + 2) → K} (hx0 : x ≠ 0)
    (hx : herm frob x x = 0) (hxy : herm frob x y = 0) (hyx : ∀ c : K, y ≠ c • x) :
    ∃ g : SUid frob (m + 2), g • x = v₀ m ∧ herm frob (v₀ m) (g • y) = 0 ∧
      herm frob (u₀ m) (g • y) = 0 := by
  obtain ⟨u, -, hu, hxu⟩ := exists_partner_frob hx0 hx
  obtain ⟨g₁, hg₁x, hg₁u⟩ := exists_smul_eq_hyp (n := m) (by omega) hx0 hx hu hxu
  set y' := g₁ • y with hy'
  have hvy' : herm frob (v₀ m) y' = 0 := by rw [← hg₁x, hy', herm_smul_smul, hxy]
  have hπ : π m y' ≠ 0 := by
    intro h0
    set c := herm frob (u₀ m) y' with hc
    have e := decomp_of_perp hvy'
    rw [h0, map_zero, add_zero, ← hc] at e
    apply hyx c
    have e2 : g₁ • y = g₁ • (c • x) := by rw [smul_comm, hg₁x, ← hy']; exact e
    exact smul_left_cancel g₁ e2
  obtain ⟨t, ht⟩ := exists_herm_eq hπ (herm frob (u₀ m) y')
  obtain ⟨d, hdtr⟩ : ∃ d : K, d + frob d = herm frob t t := by
    rcases herm_self_eq_zero_or_one t with h0 | h1
    · exact ⟨0, by rw [map_zero, add_zero, h0]⟩
    · exact ⟨ω, by rw [h1, omega_add_frob]⟩
  set z' := u₀ m + d • v₀ m + ι m t with hz'
  have hz'z' : herm frob z' z' = 0 := by
    simp only [hz', herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
      herm_u₀_u₀, herm_u₀_v₀, herm_v₀_u₀, herm_v₀_v₀, herm_u₀_ι, herm_ι_u₀, herm_v₀_ι,
      herm_ι_v₀, herm_ι_ι, mul_zero, mul_one, add_zero, zero_add]
    linear_combination hdtr + herm frob t t * two_eq_zero
  have hvz' : herm frob (v₀ m) z' = 1 := by
    simp only [hz', herm_add_right, herm_smul_right, herm_v₀_u₀, herm_v₀_v₀, herm_v₀_ι,
      mul_zero, add_zero]
  have hz'y' : herm frob z' y' = 0 := by
    simp only [hz', herm_add_left, herm_smul_left, hvy', mul_zero, add_zero, herm_ι_left, ht]
    exact add_self_K _
  obtain ⟨E, hE, hEu⟩ := exists_mem_L_smul_u₀ hm hz'z' hvz'
  refine ⟨E⁻¹ * g₁, ?_, ?_, ?_⟩
  · rw [mul_smul, hg₁x, inv_smul_eq_iff, smul_v₀_of_mem_L hE]
  · rw [mul_smul, ← hy', ← herm_smul_smul frob E, smul_inv_smul, smul_v₀_of_mem_L hE, hvy']
  · rw [mul_smul, ← hy', ← herm_smul_smul frob E, smul_inv_smul, hEu, hz'y']

theorem exists_std_pair' (hm : 3 ≤ m) {x y : Fin (m + 2) → K} (hx0 : x ≠ 0)
    (hx : herm frob x x = 0) (hy : herm frob y y = 0) (hxy : herm frob x y = 0)
    (hyx : ∀ c : K, y ≠ c • x) :
    ∃ g : SUid frob (m + 2), g • x = v₀ m ∧ g • y = ι m (isoVec (by omega : 2 ≤ m)) := by
  obtain ⟨g, hgx, hgv, hgu⟩ := exists_std_pair (by omega) hx0 hx hxy hyx
  set y₀ := π m (g • y) with hy₀
  have hgy : g • y = ι m y₀ := by
    have e := decomp (g • y)
    rw [hgv, hgu, zero_smul, zero_smul, zero_add, zero_add] at e
    exact e
  have hy₀iso : herm frob y₀ y₀ = 0 := by rw [← herm_ι_ι, ← hgy, herm_smul_smul, hy]
  have hy₀0 : y₀ ≠ 0 := by
    intro h0
    apply hyx 0
    rw [zero_smul, ← smul_left_cancel_iff g, hgy, h0, map_zero, smul_zero]
  obtain ⟨t, ht, hty⟩ := exists_mem_T_smul_eq_of_iso isUnitaryInvolution_frob hm hy₀0 hy₀iso
    (isoVec_ne_zero (by omega)) (isoVec_isotropic (by omega))
  obtain ⟨t', -, htv, -, htι⟩ := exists_lift ht
  exact ⟨t' * g, by rw [mul_smul, hgx, htv], by rw [mul_smul, hgy, htι, hty]⟩

theorem one_add_frob_mul_ne_zero {c d : K} (hc : c ≠ 0) (hcd : c ≠ d) :
    1 + frob c * d ≠ 0 := by
  intro h0
  apply hcd
  have h1 : frob c * d = 1 := by linear_combination h0 - two_eq_zero
  have := frob_mul_self hc
  calc c = c * (frob c * d) := by rw [h1, mul_one]
    _ = (frob c * c) * d := by ring
    _ = d := by rw [this, one_mul]

noncomputable abbrev pv (hm : 3 ≤ m) (j : Fin m) (c : K) : Fin m → K :=
  Pi.single ⟨0, by omega⟩ 1 + Pi.single j c

theorem herm_pv (hm : 3 ≤ m) {j j' : Fin m} (hj : j ≠ ⟨0, by omega⟩)
    (hj' : j' ≠ ⟨0, by omega⟩) (c c' : K) :
    herm frob (pv hm j c) (pv hm j' c') = 1 + frob c * (if j = j' then c' else 0) := by
  rw [pv, herm_single_add_single_left]
  simp [Pi.single_apply, hj, Ne.symm hj']

noncomputable abbrev cval : Fin 3 → K := ![1, ω, frob ω]

theorem cval_ne_zero (i : Fin 3) : cval i ≠ 0 := by
  fin_cases i
  · exact one_ne_zero
  · exact omega_ne_zero
  · exact frob_ne_zero omega_ne_zero

theorem cval_injective : Function.Injective cval := by
  have h1 : (1 : K) ≠ ω := omega_ne_one.symm
  have h2 : (1 : K) ≠ frob ω := frob_omega_ne_one.symm
  have h3 : ω ≠ frob ω := by
    rw [frob_omega]
    intro h
    have : (1 : K) = 0 := by linear_combination -h
    exact one_ne_zero this
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

noncomputable abbrev six (hm : 3 ≤ m) (k : Fin 6) : Fin m → K :=
  pv hm (if (k : ℕ) < 3 then ⟨1, by omega⟩ else ⟨2, by omega⟩) (cval ⟨(k : ℕ) % 3, by omega⟩)

theorem six_isotropic (hm : 3 ≤ m) (k : Fin 6) : herm frob (six hm k) (six hm k) = 0 := by
  refine isotropic_single_add_single ?_ (cval_ne_zero _)
  split_ifs <;> simp [Fin.ext_iff]

theorem six_ne_zero (hm : 3 ≤ m) (k : Fin 6) : six hm k ≠ 0 := by
  intro h0
  have := congrFun h0 ⟨0, by omega⟩
  simp only [six, pv, Pi.add_apply, Pi.zero_apply] at this
  split_ifs at this <;> simp [Fin.ext_iff] at this

theorem herm_six_ne_zero (hm : 3 ≤ m) {k l : Fin 6} (hkl : k ≠ l) :
    herm frob (six hm k) (six hm l) ≠ 0 := by
  have hk : ∀ k : Fin 6, (if (k : ℕ) < 3 then (⟨1, by omega⟩ : Fin m) else ⟨2, by omega⟩) ≠
      ⟨0, by omega⟩ := fun k => by split_ifs <;> simp [Fin.ext_iff]
  rw [six, six, herm_pv hm (hk k) (hk l)]
  split_ifs
  all_goals first
    | (rw [mul_zero, add_zero]; exact one_ne_zero)
    | (exfalso; simp only [Fin.ext_iff] at *; omega)
    | (refine one_add_frob_mul_ne_zero (cval_ne_zero _) fun he => hkl ?_
       have := cval_injective he
       simp only [Fin.ext_iff] at *
       omega)

theorem six_zero (hm : 3 ≤ m) : six hm 0 = isoVec (by omega : 2 ≤ m) := by
  simp [six, pv, isoVec, cval]

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : PG (m + 2) →* (V ≃ₗ[ZMod 2] V)} {q : QuadraticForm (ZMod 2) V}

theorem herm_v₀_u₀_ne_zero : herm frob (v₀ m) (u₀ m) ≠ 0 := by
  rw [herm_v₀_u₀]
  exact one_ne_zero

theorem ι_ne_zero' {z : Fin m → K} (hz : z ≠ 0) : ι m z ≠ 0 := fun h0 =>
  hz (ι_injective (by rw [h0, map_zero]))

namespace ZSHyp

variable (h : ZSHyp (m + 2) q ρ)
include h

theorem std_inf_eq_bot (hm : 3 ≤ m) :
    lineA ρ (v₀ m) ⊓ lineA ρ (ι m (isoVec (by omega : 2 ≤ m))) = ⊥ := by
  set ε := isoVec (by omega : 2 ≤ m) with hε
  have hε0 : ι m ε ≠ 0 := ι_ne_zero' (isoVec_ne_zero _)
  have hεi : herm frob (ι m ε) (ι m ε) = 0 := by rw [herm_ι_ι]; exact isoVec_isotropic _
  rcases h.inf_eq_bot_or_le v₀_ne_zero herm_v₀_v₀ u₀_ne_zero herm_u₀_u₀ herm_v₀_u₀_ne_zero
      hε0 hεi (herm_v₀_ι _) (herm_u₀_ι _) with hg | hb
  · rw [eq_bot_iff, ← hg]
    exact fun v hv => Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hv).2,
      Submodule.mem_sup_left (Submodule.mem_inf.1 hv).1⟩
  · exfalso
    have hiso : ∀ k, herm frob (ι m (six hm k)) (ι m (six hm k)) = 0 := fun k => by
      rw [herm_ι_ι]
      exact six_isotropic hm k
    have hne : ∀ k, ι m (six hm k) ≠ 0 := fun k => ι_ne_zero' (six_ne_zero hm k)
    refine false_of_six_disjoint (U := lineA ρ (v₀ m) ⊔ lineA ρ (u₀ m))
      (by rw [h.finrank_sup_lineA v₀_ne_zero herm_v₀_v₀ u₀_ne_zero herm_u₀_u₀
        herm_v₀_u₀_ne_zero]) (fun k => lineA ρ (ι m (six hm k))) (fun k => ?_)
      (fun k => h.finrank_lineA (hne k) (hiso k)) (fun k l hkl => ?_)
    · by_cases hk : k = 0
      · rw [hk, six_zero]
        exact hb
      · refine h.le_of_le_of_herm_ne_zero v₀_ne_zero herm_v₀_v₀ u₀_ne_zero herm_u₀_u₀
          herm_v₀_u₀_ne_zero hεi (herm_v₀_ι _) (herm_u₀_ι _) (hiso k) (herm_v₀_ι _)
          (herm_u₀_ι _) ?_ hb
        rw [herm_ι_ι, hε, ← six_zero hm]
        exact herm_six_ne_zero hm (Ne.symm hk)
    · exact h.inf_lineA_eq_bot (hne k) (hiso k) (hne l) (hiso l)
        (by rw [herm_ι_ι]; exact herm_six_ne_zero hm hkl)

theorem inf_lineA_eq_bot_of_perp_five (hm : 3 ≤ m) {x y : Fin (m + 2) → K} (hx0 : x ≠ 0)
    (hx : herm frob x x = 0) (hy : herm frob y y = 0) (hxy : herm frob x y = 0)
    (hyx : ∀ c : K, y ≠ c • x) : lineA ρ x ⊓ lineA ρ y = ⊥ := by
  obtain ⟨g, hgx, hgy⟩ := exists_std_pair' hm hx0 hx hy hxy hyx
  have hinj : Function.Injective (rs ρ g : V →ₗ[ZMod 2] V) := (rs ρ g).injective
  have hmap := Submodule.map_inf (rs ρ g : V →ₗ[ZMod 2] V) (p := lineA ρ x) (q := lineA ρ y)
    hinj
  rw [map_lineA g hx, map_lineA g hy, hgx, hgy, h.std_inf_eq_bot hm] at hmap
  rw [eq_bot_iff]
  intro v hv
  have hv' := Submodule.mem_map_of_mem (f := (rs ρ g : V →ₗ[ZMod 2] V)) hv
  rw [hmap, Submodule.mem_bot] at hv'
  rw [Submodule.mem_bot]
  exact hinj (by rw [hv', map_zero])

end ZSHyp

end CFSG.LargeExtraspecial.AS35ZS
