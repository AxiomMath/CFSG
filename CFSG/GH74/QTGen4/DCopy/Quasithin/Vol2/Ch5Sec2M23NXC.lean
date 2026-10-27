module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23NXC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23MX
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23NX
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23NXB

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.M23Norm3 CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Fischer

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem card_centralizer_eq_or_of_setting_F4
    (h526 : Stmt5_2_6_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4)
    (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4) (h5211 : Stmt5_2_11_four_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {w j : G} (hw3 : orderOf w = 3) (hj2 : orderOf j = 2)
    (hwj : w * j = j * w) :
    Nat.card (Subgroup.centralizer ({w} : Set G)) = 36 ∨
      Nat.card (Subgroup.centralizer ({w} : Set G)) = 180 := by
  obtain ⟨y, u, r, -, hy3, huU, hu1, hyu, hru, hry, hcent, hCU⟩ :=
    exists_y_u_of_setting_F4 h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS
  obtain ⟨hUea, -, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hU2 : ∀ e ∈ pCoreOf 2 M2, e * e = 1 := fun e he => by rw [← sq]; exact hUea.2 e he
  have hUc : ∀ e ∈ pCoreOf 2 M2, ∀ f ∈ pCoreOf 2 M2, e * f = f * e := fun e he f hf =>
    congrArg Subtype.val (hUea.1.1.comm ⟨e, he⟩ ⟨f, hf⟩)
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hU2 u huU) hu1
  have huE : u ∈ pCoreOf 2 M2 ⊓ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_inf.mpr ⟨huU, Subgroup.mem_centralizer_singleton_iff.mpr hyu.symm⟩
  have hinv : ∀ i j : G, orderOf i = 2 → orderOf j = 2 → ∃ g : G, g * i * g⁻¹ = j :=
    fun i j hi hj => stmt5_2_13_of_F4 hQ h5211 h526 h1284 hSz hU4 hsp G T M L V H B D L₂ n M2 π hyp
      hM23 hS i j hi hj
  have h9 := not_nine_dvd_card_centralizer_F4 hQ h5211 hyp hM23 hS huU hu1
  have hy := card_centralizer_eq_or_of_bsw hy3 hu2 huE inf_le_right
    (fun e he => hU2 e (Subgroup.mem_inf.mp he).1)
    (fun e he f hf => hUc e (Subgroup.mem_inf.mp he).1 f (Subgroup.mem_inf.mp hf).1) hCU
    (fun g hgy hgu => by
      obtain ⟨e, he, hey, a, hga⟩ := hcent g hgy hgu
      exact ⟨e, Subgroup.mem_inf.mpr ⟨he, Subgroup.mem_centralizer_singleton_iff.mpr hey⟩, a, hga⟩)
    hru hry hinv h9
  obtain ⟨g, hg⟩ := exists_conj_eq_or_eq_inv_of_commute hy3 hu2 hyu hinv h9 hw3 hj2 hwj
  rw [card_centralizer_eq_of_conj hg]
  exact hy

theorem card_centralizer_of_mem_centralizerModO2_F4
    (h526 : Stmt5_2_6_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4)
    (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4) (h5211 : Stmt5_2_11_four_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) (hV : IsVFacts M L) {z : G} (hzM : z ∈ M)
    (hzC : z ∈ centralizerModO2 L) (hz3 : orderOf z = 3) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) = 36 ∨
      Nat.card (Subgroup.centralizer ({z} : Set G)) = 180 := by
  have hCL := card_centralizer_inf_L hV hzM hzC hz3
  have h2 : 2 ∣ Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [hCL]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hj2 : orderOf (j : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hj
  have hzj : z * j = j * z :=
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp j.2).2).symm
  exact card_centralizer_eq_or_of_setting_F4 h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS hz3 hj2 hzj

theorem exists_inv_of_setting_F4
    (h526 : Stmt5_2_6_F4) (h527 : Stmt5_2_7_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4)
    (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {x : G} (hxM2 : x ∈ M2) (hxM : x ∈ M) (hx3 : orderOf x = 3)
    (hxE : π ⟨x, hxM2⟩ ∈ E9Sub) : ∃ r ∈ M, r * x * r⁻¹ = x⁻¹ := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hUle, -, -⟩ := inf_L_facts_of_setting_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hUM : pCoreOf 2 M2 ≤ M := hUle.trans (inf_le_right.trans hyp.L_le)
  have hs : s1245 ∈ π.range := by
    rw [hS.range_eq]
    exact Equiv.Perm.mem_alternatingGroup.mpr perm7_facts.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hs
  have hmM : (m : G) ∈ M := mem_M_of_mem_normalizer_k4Sub_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23
    hS m (by rw [hm]; exact s1245_mem_normalizer_k4Sub)
  have hmx : (m : G) * x * (m : G)⁻¹ ∈ M2 := M2.mul_mem (M2.mul_mem m.2 hxM2) (M2.inv_mem m.2)
  have hπ : π ⟨(m : G) * x * (m : G)⁻¹, hmx⟩ = π ⟨x⁻¹, M2.inv_mem hxM2⟩ := by
    have e1 : (⟨(m : G) * x * (m : G)⁻¹, hmx⟩ : ↥M2) = m * ⟨x, hxM2⟩ * m⁻¹ := rfl
    have e2 : (⟨x⁻¹, M2.inv_mem hxM2⟩ : ↥M2) = (⟨x, hxM2⟩ : ↥M2)⁻¹ := rfl
    rw [e1, e2, map_mul, map_mul, map_inv, map_inv, hm]
    exact s1245_conj_E9 hxE
  have hmx3 : orderOf ((m : G) * x * (m : G)⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx3
  have hxi3 : orderOf x⁻¹ = 3 := by rw [orderOf_inv]; exact hx3
  obtain ⟨g, hg, hgx⟩ := exists_conj_mem_sup_of_map_eq_three hS.ker_eq
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2) (CFSG.LieType.BorelTits.pCoreOf_le 2 M2) hmx
    (M2.inv_mem hxM2) hmx3 hxi3 hπ
  have hgM : g ∈ M := by
    refine (sup_le hUM ?_) hg
    rw [Subgroup.zpowers_le]
    exact M.mul_mem (M.mul_mem hmM hxM) (M.inv_mem hmM)
  refine ⟨g * m, M.mul_mem hgM hmM, ?_⟩
  rw [← hgx]
  group

theorem exists_x_of_setting_F4
    (h526 : Stmt5_2_6_F4) (h527 : Stmt5_2_7_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4)
    (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4) (h5211 : Stmt5_2_11_four_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    ∃ x : G, x ∈ M ⊓ centralizerModO2 L ∧ orderOf x = 3 ∧
      Subgroup.centralizer ({x} : Set G) ≤ M ∧
      Nat.card (Subgroup.centralizer ({x} : Set G)) = 180 ∧ ∃ r ∈ M, r * x * r⁻¹ = x⁻¹ := by
  obtain ⟨x, hxM2, hxMC, hx3, hxE⟩ :=
    exists_mem_centralizerModO2_of_setting_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.mp hxMC
  have hV := isVFacts_of_setting_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hEM := preE9_le_M_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hE := card_preE9_F4 hQ hyp hM23 hS
  have hxpre : x ∈ preE9 M2 π := ⟨⟨x, hxM2⟩, hxE, rfl⟩
  obtain ⟨W, hW, hW180⟩ := exists_le_centralizer_dvd_card hV hEM hE hxpre hxM hxC hx3
  have hC := card_centralizer_of_mem_centralizerModO2_F4 h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS
    hV hxM hxC hx3
  have hWC : W ≤ Subgroup.centralizer ({x} : Set G) := hW.trans inf_le_right
  have hd := Subgroup.card_dvd_of_le hWC
  have h180 : Nat.card (Subgroup.centralizer ({x} : Set G)) = 180 := by
    rcases hC with h | h
    · exfalso
      rw [h] at hd
      have := hW180.trans hd
      norm_num at this
    · exact h
  have hWeq : W = Subgroup.centralizer ({x} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hWC (by rw [h180]; exact Nat.le_of_dvd Nat.card_pos hW180)
  refine ⟨x, hxMC, hx3, ?_, h180,
    exists_inv_of_setting_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS hxM2 hxM hx3 hxE⟩
  rw [← hWeq]
  exact hW.trans inf_le_left

theorem stmt5_2_15_of_F4
    (h526 : Stmt5_2_6_F4) (h527 : Stmt5_2_7_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4)
    (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4) (h5211 : Stmt5_2_11_four_F4) :
    Stmt5_2_15_F4 := by
  intro G _ _ T M L V H B D L₂ n M2 π hyp hM23 hS X hX
  obtain ⟨hn2, -, -, -, -⟩ := setting_K_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  subst hn2
  obtain ⟨x, hxC, hx3, hCM, hC180, r, hrM, hr⟩ :=
    exists_x_of_setting_F4 h526 h527 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS
  have hV := isVFacts_of_setting_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hX3 := card_eq_three_of_isSylowIn hV hyp.lie (fun z hz hz3 =>
    card_centralizer_of_mem_centralizerModO2_F4 h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS hV
      (Subgroup.mem_inf.mp hz).1 (Subgroup.mem_inf.mp hz).2 hz3) hX hxC hx3
  obtain ⟨c, hcC, hcX⟩ := exists_conj_mem_of_isSylowIn hX hxC hx3
  have hcM : c ∈ M := (Subgroup.mem_inf.mp hcC).1
  have hx'3 : orderOf (c * x * c⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx3
  have hXeq : X = Subgroup.zpowers (c * x * c⁻¹) :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcX)
      (by rw [hX3, Nat.card_zpowers, hx'3])).symm
  have hx'C : c * x * c⁻¹ ∈ M ⊓ centralizerModO2 L :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hcC hxC) (Subgroup.inv_mem _ hcC)
  have hCM' : Subgroup.centralizer ({c * x * c⁻¹} : Set G) ≤ M := by
    intro g hg
    have hg' : c⁻¹ * g * c ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      calc c⁻¹ * g * c * x = c⁻¹ * (g * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * g) * c := by rw [hg]
        _ = x * (c⁻¹ * g * c) := by group
    have e : g = c * (c⁻¹ * g * c) * c⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hcM (hCM hg')) (M.inv_mem hcM)
  have hC180' : Nat.card (Subgroup.centralizer ({c * x * c⁻¹} : Set G)) = 180 := by
    rw [card_centralizer_conj]
    exact hC180
  have hr' : (c * r * c⁻¹) * (c * x * c⁻¹) * (c * r * c⁻¹)⁻¹ = (c * x * c⁻¹)⁻¹ := by
    calc (c * r * c⁻¹) * (c * x * c⁻¹) * (c * r * c⁻¹)⁻¹ = c * (r * x * r⁻¹) * c⁻¹ := by group
      _ = (c * x * c⁻¹)⁻¹ := by rw [hr]; group
  have hr'M : c * r * c⁻¹ ∈ M := M.mul_mem (M.mul_mem hcM hrM) (M.inv_mem hcM)
  obtain ⟨hNM, hiso⟩ := normalizer_le_and_gammaL2_of hV (Subgroup.mem_inf.mp hx'C).1
    (Subgroup.mem_inf.mp hx'C).2 hx'3 hCM' hC180' hr'M hr'
  rw [hXeq]
  exact ⟨hNM, F4, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, F4.card], hiso⟩

end CFSG.Quasithin.H13
