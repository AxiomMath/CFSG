module

public import CFSG.LargeExtraspecial.AS35TFEight
public import CFSG.LargeExtraspecial.AS35TFFive

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

namespace AS35T

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_mem_delta_cl_eq {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) {v : S.Qt} (hv : v ∈ commSpace (S.rhoL htM)) (hv0 : v ≠ 0) :
    ∃ p ∈ S.zConj (S.HAt g), p ≠ S.z ∧ p ≠ g * S.z * g⁻¹ ∧
      p * (g * S.z * g⁻¹) ∈ S.QG ∧ S.cl (p * (g * S.z * g⁻¹)) = v := by
  set t := g * S.z * g⁻¹ with htdef
  have htt : t * t = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
  obtain ⟨q, hq, rfl⟩ := S.exists_cl u
  obtain ⟨h1, h2⟩ := S.cl_conj_mul_eq htM htt hq
  have hpH : q * t * q⁻¹ ∈ S.zConj (S.HAt g) :=
    Asc77.conj_mem_conjIn_of_mem (le_sup_left (b := S.Qa g) hq) (S.mem_zConj_of_mem_ESet ht.1 rfl)
  refine ⟨q * t * q⁻¹, hpH, fun h => ?_, fun h => ?_, h1, h2⟩
  · apply S.ne_z_of_mem_ESet ht.1
    have hqM := S.QG_le_M hq
    calc t = q⁻¹ * (q * t * q⁻¹) * q := by group
      _ = q⁻¹ * S.z * q⁻¹⁻¹ := by rw [h, inv_inv]
      _ = S.z := S.conj_z_of_mem_M (S.M.inv_mem hqM)
  · apply hv0
    rw [← h2, h, htt, S.cl_one]

theorem fiveTwelveSeven (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) :
    ∃ x ∈ S.Mbar, (∃ k : ℕ, orderOf x = 3 ^ k) ∧ x * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * x ∧
      ∀ v ∈ commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt),
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0 := by
  set t := g * S.z * g⁻¹ with htdef
  have hH := (S.isHStar_of_mem_ESet ht.1 rfl).1
  obtain ⟨_, _, h5, -, -, -, hsurj⟩ := (hS.sixFour _ hH).1.1
  have htH := S.mem_zConj_of_mem_ESet ht.1 rfl
  have hzH := Asc77.self_mem_conjIn S.z (S.HAt g)
  have htz := S.ne_z_of_mem_ESet ht.1
  have hsub : ({S.z, t} : Set G) ⊆ S.zConj (S.HAt g) := by
    rintro w (rfl | rfl)
    · exact hzH
    · exact htH
  have h3 : (S.zConj (S.HAt g) \ {S.z, t}).ncard = 3 := by
    rw [Set.ncard_sdiff hsub, h5, Set.ncard_pair htz.symm]
  obtain ⟨a, b, c, hab, hac, hbc, hΔ⟩ := Set.ncard_eq_three.mp h3
  have hmem : ∀ p, p ∈ S.zConj (S.HAt g) \ {S.z, t} ↔ p = a ∨ p = b ∨ p = c := by
    intro p
    rw [hΔ]
    simp
  have ha := (hmem a).mpr (Or.inl rfl)
  have hb := (hmem b).mpr (Or.inr (Or.inl rfl))
  have hc := (hmem c).mpr (Or.inr (Or.inr rfl))
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ha hb hc
  set A : S.zConj (S.HAt g) := ⟨a, ha.1⟩
  set B : S.zConj (S.HAt g) := ⟨b, hb.1⟩
  set C : S.zConj (S.HAt g) := ⟨c, hc.1⟩
  set Z : S.zConj (S.HAt g) := ⟨S.z, hzH⟩
  set T : S.zConj (S.HAt g) := ⟨t, htH⟩
  have hne : ∀ {x y : S.zConj (S.HAt g)}, (x : G) ≠ y → x ≠ y :=
    fun h h' => h (congrArg Subtype.val h')
  have hAB : A ≠ B := hne hab
  have hAC : A ≠ C := hne hac
  have hBC : B ≠ C := hne hbc
  have hZA : Z ≠ A := hne (x := Z) (y := A) (Ne.symm ha.2.1)
  have hZB : Z ≠ B := hne (x := Z) (y := B) (Ne.symm hb.2.1)
  have hZC : Z ≠ C := hne (x := Z) (y := C) (Ne.symm hc.2.1)
  have hTA : T ≠ A := hne (x := T) (y := A) (Ne.symm ha.2.2)
  have hTB : T ≠ B := hne (x := T) (y := B) (Ne.symm hb.2.2)
  have hTC : T ≠ C := hne (x := T) (y := C) (Ne.symm hc.2.2)
  have h3c := Equiv.Perm.isThreeCycle_swap_mul_swap_same hAB hAC hBC
  obtain ⟨h, hh⟩ := hsurj _ h3c.sign
  have hact : ∀ x : S.zConj (S.HAt g), (h : G) * x * (h : G)⁻¹ =
      ((Equiv.swap A B * Equiv.swap A C) x : G) := by
    intro x
    rw [← Asc77.conjAct_apply, hh]
  have hZ : (h : G) * S.z * (h : G)⁻¹ = S.z := by
    have e := hact Z
    rwa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hZA hZC,
      Equiv.swap_apply_of_ne_of_ne hZA hZB] at e
  have hT : (h : G) * t * (h : G)⁻¹ = t := by
    have e := hact T
    rwa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hTA hTC,
      Equiv.swap_apply_of_ne_of_ne hTA hTB] at e
  have hmove : ∀ p, p = a ∨ p = b ∨ p = c → (h : G) * p * (h : G)⁻¹ ≠ p := by
    rintro p (rfl | rfl | rfl)
    · have e := hact A
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hAC) (Ne.symm hBC)] at e
      rw [e]
      exact Ne.symm hac
    · have e := hact B
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hAB) hBC,
        Equiv.swap_apply_right] at e
      rw [e]
      exact hab
    · have e := hact C
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left] at e
      rw [e]
      exact hbc
  have hcube : ∀ x : S.zConj (S.HAt g), (h : G) ^ 3 * x * ((h : G) ^ 3)⁻¹ = x := by
    intro x
    have e : Asc77.conjAct S.z (S.HAt g) (h ^ 3) = 1 := by
      rw [map_pow, hh, ← h3c.orderOf, pow_orderOf_eq_one]
    have e' := congrArg (fun π : Equiv.Perm (S.zConj (S.HAt g)) => (π x : G)) e
    simp only [Asc77.conjAct_apply, Equiv.Perm.coe_one, id_eq] at e'
    simpa using e'
  have hhM : (h : G) ∈ S.M := S.mem_M_of_conj_eq_z hZ
  have hht : (h : G) * t = t * (h : G) := by
    calc (h : G) * t = (h : G) * t * (h : G)⁻¹ * (h : G) := by group
      _ = t * (h : G) := by rw [hT]
  set σ : S.O := S.ρ ⟨h, hhM⟩ with hσ
  have hστ : σ * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * σ := by
    rw [hσ, ← map_mul, ← map_mul]
    exact congrArg S.ρ (Subtype.ext hht)
  have hΔ' : ∀ p ∈ S.zConj (S.HAt g), p ≠ S.z → p ≠ t → p = a ∨ p = b ∨ p = c :=
    fun p hp hpz hpt => (hmem p).mp ⟨hp, by simp [hpz, hpt]⟩
  have hfree : ∀ v ∈ commSpace (S.rhoL htM), S.rhoL hhM v = v → v = 0 := by
    intro v hv hfix
    by_contra hv0
    obtain ⟨p, hpH, hpz, hpt, hptQ, rfl⟩ := AS35T.exists_mem_delta_cl_eq ht htM hv hv0
    have hpD := S.zConj_diff_subset_DSet hS.sixFour ht rfl hpH hpz
    have e1 : (h : G) * (p * t) * (h : G)⁻¹ = (h : G) * p * (h : G)⁻¹ * t := by
      conv_rhs => rw [← hT]
      group
    rw [S.rhoL_cl hhM hptQ, e1] at hfix
    have hQ1 : (h : G) * p * (h : G)⁻¹ * t ∈ S.QG := e1 ▸ S.conj_mem_QG hhM hptQ
    rcases (S.cl_eq_cl_iff hQ1 hptQ).mp hfix with e2 | e2
    · exact hmove p (hΔ' p hpH hpz hpt) (mul_right_cancel e2).symm
    · apply hpD.2
      have hzt : S.z * t = t * S.z := AS35T.commute_of_mem_zConj_of_mem_DSet S hS ht rfl hzH htH
      have hzp : S.z * p = p * S.z := AS35T.commute_of_mem_zConj_of_mem_DSet S hS ht rfl hzH hpH
      have htt : t * t = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
      have e3 : (h : G) * p * (h : G)⁻¹ = S.z * p := by
        calc (h : G) * p * (h : G)⁻¹ = (h : G) * p * (h : G)⁻¹ * t * S.z * (S.z * t) := by
              rw [show (h : G) * p * (h : G)⁻¹ * t * S.z * (S.z * t) =
                (h : G) * p * (h : G)⁻¹ * (t * (S.z * S.z) * t) by group, S.z_mul_z, mul_one,
                htt, mul_one]
          _ = p * t * (S.z * t) := by rw [← e2]
          _ = p * (t * t) * S.z := by rw [hzt]; group
          _ = S.z * p := by rw [htt, mul_one, hzp]
      obtain ⟨k, -, hk⟩ := hpH
      exact isConj_iff.mpr ⟨(h : G) * k, by
        rw [show (h : G) * k * S.z * ((h : G) * k)⁻¹ = (h : G) * (k * S.z * k⁻¹) * (h : G)⁻¹ by
          group, hk, e3]⟩
  have hcube' : ∀ v ∈ commSpace (S.rhoL htM), ((σ ^ 3 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
    obtain ⟨p, hpH, hpz, hpt, hptQ, rfl⟩ := AS35T.exists_mem_delta_cl_eq ht htM hv hv0
    have e : σ ^ 3 = S.ρ ⟨(h : G) ^ 3, S.M.pow_mem hhM 3⟩ := by
      rw [hσ, ← map_pow]
      rfl
    rw [e]
    change S.rhoL _ (S.cl (p * t)) = S.cl (p * t)
    rw [S.rhoL_cl _ hptQ]
    congr 1
    have h1 := hcube ⟨p, hpH⟩
    have h2 := hcube T
    calc (h : G) ^ 3 * (p * t) * ((h : G) ^ 3)⁻¹ =
        ((h : G) ^ 3 * p * ((h : G) ^ 3)⁻¹) * ((h : G) ^ 3 * t * ((h : G) ^ 3)⁻¹) := by group
      _ = p * t := by rw [h1, h2]
  set n := orderOf σ with hn
  have hn0 : n ≠ 0 := (orderOf_pos σ).ne'
  set m := n / 3 ^ n.factorization 3 with hm
  have hm3 : Nat.Coprime 3 m := Nat.coprime_ordCompl Nat.prime_three hn0
  refine ⟨σ ^ m, S.Mbar.pow_mem ⟨⟨h, hhM⟩, rfl⟩ m,
    ⟨n.factorization 3, orderOf_pow_orderOf_div hn0 (Nat.ordProj_dvd n 3)⟩,
    ((Commute.pow_left hστ) m).eq, ?_⟩
  intro v hv hfix
  have hσv : ∀ r : ℕ, ((σ ^ r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ commSpace (S.rhoL htM) :=
    fun r => apply_mem_commSpace_of_commute ((Commute.pow_left hστ) r).eq hv
  have hred : ∀ j r : ℕ, ((σ ^ (3 * j + r) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((σ ^ r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    intro j r
    rw [pow_add, pow_mul]
    change (((σ ^ 3) ^ j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((σ ^ r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = _
    exact AS35T.pow_apply_eq_of_apply_eq (hcube' _ (hσv r)) j
  have hm' : m = 3 * (m / 3) + m % 3 := (Nat.div_add_mod m 3).symm
  have hσ1 : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0 := hfree v hv
  have hmod : m % 3 = 1 ∨ m % 3 = 2 := by
    have h1 : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have h2 : m % 3 ≠ 0 := by
      intro h0
      have : 3 ∣ m := Nat.dvd_of_mod_eq_zero h0
      exact absurd (Nat.Coprime.eq_one_of_dvd hm3 this) (by norm_num)
    omega
  rw [hm', hred] at hfix
  rcases hmod with h1 | h1
  · rw [h1, pow_one] at hfix
    exact hσ1 hfix
  · rw [h1] at hfix
    apply hσ1
    have h3 := hcube' v hv
    rw [pow_succ] at h3
    change (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) (((σ ^ 2 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v at h3
    rwa [hfix] at h3

end AS35T

end Setting

end CFSG.LargeExtraspecial
