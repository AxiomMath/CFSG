module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23NXB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23Zeta

public section

namespace CFSG.Quasithin.H13

open Equiv MulAction CFSG.M23Norm3 CFSG.M23Heptad CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Vol2Native.L239
open CFSG.QuasithinUnique.L246.C123 (A7)
open CFSG.Quasithin.Asc94 (heptad₀)
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem centralizer_le_M2_of_mem_F4
    (hQ : Stmt5_2_8_Q_F4) (h5211 : Stmt5_2_11_four_F4) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) {u : G}
    (hu : u ∈ pCoreOf 2 M2) (hu1 : u ≠ 1) : Subgroup.centralizer ({u} : Set G) ≤ M2 := by
  obtain ⟨z, hz2, hzT, hzU⟩ := stmt5_2_12_center_of_F4 hQ hyp hM23 hS
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    norm_num at hz2
  obtain ⟨m, hm, hmz⟩ := stmt5_2_12_transitive_of_F4 hQ hyp hM23 hS z hzU u hu hz1 hu1
  have hC := centralizer_le_of_setting_F4 hQ h5211 hyp hM23 hS hz2 hzT hzU
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hg' : m⁻¹ * g * m ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m⁻¹ * g * m * z = m⁻¹ * (g * (m * z * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * z * m⁻¹) * g) * m := by rw [hmz, hg]
      _ = z * (m⁻¹ * g * m) := by group
  have e : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
  rw [e]
  exact M2.mul_mem (M2.mul_mem hm (hC hg')) (M2.inv_mem hm)

theorem not_nine_dvd_card_centralizer_F4
    (hQ : Stmt5_2_8_Q_F4) (h5211 : Stmt5_2_11_four_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {u : G} (hu : u ∈ pCoreOf 2 M2) (hu1 : u ≠ 1) :
    ¬ 9 ∣ Nat.card (Subgroup.centralizer ({u} : Set G)) := by
  obtain ⟨π', ρ, -, hker, -, hρ, hU16, -, -, -, hπ'⟩ := exists_rho_of_setting_F4 hQ hyp hM23 hS
  set C := Subgroup.centralizer ({u} : Set G) with hCdef
  have hCM2 : C ≤ M2 := centralizer_le_M2_of_mem_F4 hQ h5211 hyp hM23 hS hu hu1
  set u' : ↥(pCoreOf 2 M2) := ⟨u, hu⟩
  have hu'1 : u' ≠ 1 := fun h => hu1 (congrArg Subtype.val h)

  have htr : ∀ v : ↥(pCoreOf 2 M2), v ≠ 1 → ∃ g, ρ g u' = v := by
    intro v hv
    obtain ⟨m, hm, hmv⟩ := stmt5_2_12_transitive_of_F4 hQ hyp hM23 hS u hu v v.2 hu1
      (fun h => hv (Subtype.ext h))
    refine ⟨π' ⟨m, hm⟩, Subtype.ext ?_⟩
    rw [hρ]
    exact hmv
  have h168 : Nat.card (vecStab ρ u') * 15 = 2520 := by
    rw [card_vecStab_mul ρ hU16 hu'1 htr, CFSG.QuasithinUnique.L246.C123.card_A7]

  have hmapπ : (C.subgroupOf M2).map π ≤
      (vecStab ρ u').map (alternatingGroup (Fin 7)).subtype := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨π' m, ?_, hπ' m⟩
    rw [SetLike.mem_coe, mem_vecStab]
    apply Subtype.ext
    rw [hρ]
    have hmC := Subgroup.mem_subgroupOf.mp hm
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff] at hmC
    calc (m : G) * u * (m : G)⁻¹ = u * m * (m : G)⁻¹ := by rw [hmC]
      _ = u := by group
  have hd1 : Nat.card ((C.subgroupOf M2).map π) ∣ 168 := by
    have h := Subgroup.card_dvd_of_le hmapπ
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective] at h
    have h' : Nat.card (vecStab ρ u') = 168 := by omega
    rwa [h'] at h
  have hd2 : Nat.card ↥(C ⊓ pCoreOf 2 M2) ∣ 16 :=
    hU16 ▸ Subgroup.card_dvd_of_le inf_le_right
  have h1 := card_map_mul_card_inf hS.ker_eq hCM2
  intro h9
  rw [← h1] at h9
  have h2 : Nat.card ((C.subgroupOf M2).map π) * Nat.card ↥(C ⊓ pCoreOf 2 M2) ∣ 168 * 16 :=
    Nat.mul_dvd_mul hd1 hd2
  have := h9.trans h2
  norm_num at this

theorem exists_y_u_of_setting_F4
    (h526 : Stmt5_2_6_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4)
    (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4) (h5211 : Stmt5_2_11_four_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    ∃ y u r : G, y ∈ M2 ∧ orderOf y = 3 ∧ u ∈ pCoreOf 2 M2 ∧ u ≠ 1 ∧ y * u = u * y ∧
      r * u = u * r ∧ r * y * r⁻¹ = y⁻¹ ∧
      (∀ g : G, g * y = y * g → g * u = u * g →
        ∃ e ∈ pCoreOf 2 M2, e * y = y * e ∧ ∃ a : ℕ, g = e * y ^ a) ∧
      Nat.card ↥(pCoreOf 2 M2 ⊓ Subgroup.centralizer ({y} : Set G)) = 4 := by
  obtain ⟨ι, ζ, hι, hιH, hζ⟩ := exists_permEquiv_of_setting_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨hy1, hy2, hy3, hy4, -, huy, hu1, hru, hry, -⟩ := yBar_facts
  set y' : ↥M2 := ζ.symm yB with hy'
  set u' : ↥M2 := ζ.symm uB with hu'
  set r' : ↥M2 := ζ.symm rB with hr'
  have hmemU : ∀ g : ↥M2, ζ g ∈ Ubar → (g : G) ∈ pCoreOf 2 M2 := by
    intro g hg
    have h1 : π g = 1 := (mem_Ubar_iff_of_isPermEquiv hι hιH hζ g).mp hg
    have h2 : g ∈ π.ker := h1
    rw [hS.ker_eq, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hmemU' : ∀ g : ↥M2, (g : G) ∈ pCoreOf 2 M2 → ζ g ∈ Ubar := by
    intro g hg
    have h2 : g ∈ π.ker := by rw [hS.ker_eq, Subgroup.mem_subgroupOf]; exact hg
    exact (mem_Ubar_iff_of_isPermEquiv hι hιH hζ g).mpr h2
  have huB : ζ u' ∈ Ubar := by
    rw [hu', MulEquiv.apply_symm_apply]
    exact uB_mem_Ubar
  have huU : (u' : G) ∈ pCoreOf 2 M2 := hmemU u' huB
  have hu'1 : (u' : G) ≠ 1 := by
    intro h
    have : u' = 1 := Subtype.ext h
    have h2 : uB = 1 := by rw [← ζ.apply_symm_apply uB, ← hu', this, map_one]
    exact hu1 (congrArg Subtype.val h2)
  have hyB3 : orderOf yB = 3 := by
    rw [← Subgroup.orderOf_coe]
    show orderOf yBar = 3
    exact orderOf_eq_prime hy3 hy4
  have hy'3 : orderOf (y' : G) = 3 := by
    rw [Subgroup.orderOf_coe, hy', MulEquiv.orderOf_eq]
    exact hyB3
  have hcomm' : ∀ a b : ↥M2bar, a * b = b * a → ζ.symm a * ζ.symm b = ζ.symm b * ζ.symm a :=
    fun a b h => by rw [← map_mul, ← map_mul, h]
  have hyuB : yB * uB = uB * yB := Subtype.ext huy.symm
  refine ⟨y', u', r', y'.2, hy'3, huU, hu'1, ?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val (hcomm' _ _ hyuB)
  · exact congrArg Subtype.val (hcomm' _ _ (Subtype.ext hru))
  · have : rB * yB * rB⁻¹ = yB⁻¹ := Subtype.ext hry
    have h2 : r' * y' * r'⁻¹ = y'⁻¹ := by
      rw [hr', hy', ← map_inv, ← map_mul, ← map_inv, ← map_mul, this]
    exact congrArg Subtype.val h2
  · intro g hgy hgu
    have hgM2 : g ∈ M2 := centralizer_le_M2_of_mem_F4 hQ h5211 hyp hM23 hS huU hu'1
      (Subgroup.mem_centralizer_singleton_iff.mpr hgu)
    set g' : ↥M2 := ⟨g, hgM2⟩
    have h1 : ζ g' * yB = yB * ζ g' := by
      have : g' * y' = y' * g' := Subtype.ext hgy
      have := congrArg ζ this
      rwa [map_mul, map_mul, hy', MulEquiv.apply_symm_apply] at this
    have h2 : ζ g' * uB = uB * ζ g' := by
      have : g' * u' = u' * g' := Subtype.ext hgu
      have := congrArg ζ this
      rwa [map_mul, map_mul, hu', MulEquiv.apply_symm_apply] at this
    obtain ⟨e, he, hey, a, hga⟩ := mem_of_commute_yB_uB h1 h2
    refine ⟨(ζ.symm e : G), hmemU _ (by rw [MulEquiv.apply_symm_apply]; exact he), ?_, a, ?_⟩
    · exact congrArg Subtype.val (hcomm' _ _ hey)
    · have : g' = ζ.symm e * y' ^ a := by
        rw [hy', ← map_pow, ← map_mul, ← hga, MulEquiv.symm_apply_apply]
      have := congrArg Subtype.val this
      simpa using this
  ·
    rw [← card_Ubar_commute_yB]
    refine Nat.card_congr
      { toFun := fun e => ⟨ζ ⟨e, CFSG.LieType.BorelTits.pCoreOf_le 2 M2 (e.2.1)⟩, ?_, ?_⟩
        invFun := fun e => ⟨(ζ.symm e.1 : G), Subgroup.mem_inf.mpr ⟨hmemU _ (by
          rw [MulEquiv.apply_symm_apply]
          exact e.2.1), ?_⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · exact hmemU' _ e.2.1
    · have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp e.2).2
      have : (⟨e, CFSG.LieType.BorelTits.pCoreOf_le 2 M2 (e.2.1)⟩ : ↥M2) * y' =
          y' * ⟨e, CFSG.LieType.BorelTits.pCoreOf_le 2 M2 (e.2.1)⟩ := Subtype.ext h
      have hζy : ζ y' = yB := by rw [hy', MulEquiv.apply_symm_apply]
      have := congrArg ζ this
      rwa [map_mul, map_mul, hζy] at this
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hcomm' _ _ e.2.2)
    · intro e
      apply Subtype.ext
      simp
    · intro e
      apply Subtype.ext
      simp

end CFSG.Quasithin.H13
