module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
import CFSG.LocalAnalysis.GLTheoremB.S7Facts
import CFSG.LargeExtraspecial.BridgeNat
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvAuxK

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

theorem alt_degree_eq {n m : ℕ} (hn : 5 ≤ n) (hm : 5 ≤ m)
    (e : alternatingGroup (Fin n) ≃* alternatingGroup (Fin m)) : n = m := by
  have hnt : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hmt : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hc : Nat.card (alternatingGroup (Fin n)) = Nat.card (alternatingGroup (Fin m)) :=
    Nat.card_congr e.toEquiv
  rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin] at hc
  have h2n : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h2m : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have : n.factorial = m.factorial := by omega
  exact (Nat.factorial_inj (by omega)).1 this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem a7_dec_pow6 : ∀ g : Equiv.Perm (Fin 7), Equiv.Perm.sign g = 1 →
    g * S7.a = S7.a * g → g ^ 6 = 1 := fun g =>
  (Prop95IvAuxK.pow_inv_K S7.a S7.x S7.y (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) g).1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem a7_dec_inv : ∀ g : Equiv.Perm (Fin 7), Equiv.Perm.sign g = 1 →
    g * S7.a = S7.a * g → g ^ 2 = 1 → g = 1 ∨ g = S7.x ∨ g = S7.y ∨ g = S7.x * S7.y := fun g =>
  (Prop95IvAuxK.pow_inv_K S7.a S7.x S7.y (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) g).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem a7_dec_L3 : ∀ g : Equiv.Perm (Fin 7), g.support.card = 3 → g * S7.a = S7.a * g →
    g = S7.a ∨ g = S7.a ^ 2 ∨ Disjoint S7.a.support g.support := fun g =>
  (Prop95IvAuxK.three_K S7.a S7.b (by decide +kernel) (by decide +kernel) (by decide +kernel)
    g).1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem a7_dec_L4 : ∀ g : Equiv.Perm (Fin 7), g.support.card = 3 →
    Disjoint S7.a.support g.support →
      ∃ τ : Equiv.Perm (Fin 7), τ * S7.a = S7.a * τ ∧ τ * g = S7.b * τ := fun g =>
  (Prop95IvAuxK.three_K S7.a S7.b (by decide +kernel) (by decide +kernel) (by decide +kernel)
    g).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem a7_comm_all : ∀ w ∈ [S7.x, S7.y, S7.x * S7.y],
    (⁅w, S7.b⁆ = S7.x ∨ ⁅w, S7.b⁆ = S7.y ∨ ⁅w, S7.b⁆ = S7.x * S7.y) ∧
      (⁅w, S7.b ^ 2⁆ = S7.x ∨ ⁅w, S7.b ^ 2⁆ = S7.y ∨ ⁅w, S7.b ^ 2⁆ = S7.x * S7.y) ∧
      ⁅w, S7.b⁆ ≠ ⁅w, S7.b ^ 2⁆ := by
  intro w hw
  rw [commutatorElement_def, commutatorElement_def]
  exact Prop95IvAuxK.comm_K S7.x S7.y S7.b (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) w hw

set_option maxRecDepth 100000 in
private theorem a7_gen_all : ∀ v ∈ [1, S7.x, S7.y, S7.x * S7.y],
    ∀ u₁ ∈ [S7.x, S7.y, S7.x * S7.y], ∀ u₂ ∈ [S7.x, S7.y, S7.x * S7.y], u₁ ≠ u₂ →
      v = 1 ∨ v = u₁ ∨ v = u₂ ∨ v = u₁ * u₂ :=
  Prop95IvAuxK.gen_K (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem a7_fix_outside : ∀ i : Fin 7, ¬ (i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) →
    S7.x i = i ∧ S7.y i = i ∧ (S7.x * S7.y) i = i := by
  decide

private theorem a7_moves : ∀ i : Fin 7, (i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) → S7.x i ≠ i := by
  decide

private theorem a7_mem_a : S7.a ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

private theorem a7_mem_b : S7.b ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

private def aG : ↥(alternatingGroup (Fin 7)) := ⟨S7.a, a7_mem_a⟩

private def bG : ↥(alternatingGroup (Fin 7)) := ⟨S7.b, a7_mem_b⟩

private abbrev Vg : Subgroup ↥(alternatingGroup (Fin 7)) :=
  S7.V.subgroupOf (alternatingGroup (Fin 7))

private abbrev V'g : Subgroup ↥(alternatingGroup (Fin 7)) :=
  S7.V'.subgroupOf (alternatingGroup (Fin 7))

private abbrev Tg : Subgroup ↥(alternatingGroup (Fin 7)) :=
  S7.T.subgroupOf (alternatingGroup (Fin 7))

private theorem a7_T_le : S7.T ≤ alternatingGroup (Fin 7) :=
  sup_le ((Subgroup.zpowers_le).2 a7_mem_a) ((Subgroup.zpowers_le).2 a7_mem_b)

private theorem a7_T_le_cent : S7.T ≤ Subgroup.centralizer ({S7.a} : Set (Equiv.Perm (Fin 7))) :=
  sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 rfl))
    ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 S7.a_mul_b.symm))

private theorem a7_mem_Vg (v : ↥(alternatingGroup (Fin 7))) :
    v ∈ Vg ↔ (v : Equiv.Perm (Fin 7)) ∈ S7.V :=
  Subgroup.mem_subgroupOf

private theorem a7_mem_V_iff (g : Equiv.Perm (Fin 7)) :
    g ∈ S7.V ↔ g = 1 ∨ g = S7.x ∨ g = S7.y ∨ g = S7.x * S7.y := by
  constructor
  · intro hg
    have hg' : g ∈ Subgroup.zpowers S7.x ⊔ Subgroup.zpowers S7.y := hg
    have hc : Subgroup.zpowers S7.x ≤
        Subgroup.centralizer ((Subgroup.zpowers S7.y : Subgroup (Equiv.Perm (Fin 7))) :
          Set (Equiv.Perm (Fin 7))) := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact ((Commute.zpow_zpow (show Commute S7.x S7.y from S7.x_mul_y) i j).eq).symm
    obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, hz⟩ :=
      CFSG.LocalAnalysis.GLTheoremB.exists_mul_of_mem_sup hc hg'
    have hx2 : S7.x ^ (2 : ℤ) = 1 := by rw [zpow_two, S7.x_mul_x]
    have hy2 : S7.y ^ (2 : ℤ) = 1 := by rw [zpow_two, S7.y_mul_y]
    dsimp only at hz
    rw [hz, zpow_eq_zpow_emod i hx2, zpow_eq_zpow_emod j hy2]
    rcases Int.emod_two_eq_zero_or_one i with hi | hi <;>
      rcases Int.emod_two_eq_zero_or_one j with hj | hj <;> rw [hi, hj] <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact S7.V.one_mem
    · exact S7.x_mem_V
    · exact S7.y_mem_V
    · exact S7.V.mul_mem S7.x_mem_V S7.y_mem_V

private theorem a7_card_V : Nat.card ↥S7.V = 4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun g => a7_mem_V_iff g)), Nat.card_eq_fintype_card]
  exact Prop95IvAuxK.card_V_K S7.x S7.y (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

private theorem a7_isRootFour_Vg : IsRootFour Vg := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S7.V_le_Alt7).toEquiv, a7_card_V]
  · intro v hv
    apply Subtype.ext
    have hvF := (a7_mem_V_iff _).1 ((a7_mem_Vg v).1 hv)
    show ((v : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) ^ 2 = 1
    rcases hvF with h | h | h | h <;> rw [h] <;> decide
  · have hmov : ∀ i : Fin 7, (¬ ∀ v ∈ Vg, (v : Equiv.Perm (Fin 7)) i = i) ↔
        (i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) := by
      intro i
      constructor
      · intro h
        by_contra hi
        apply h
        intro v hv
        obtain ⟨h1, h2, h3⟩ := a7_fix_outside i hi
        rcases (a7_mem_V_iff _).1 ((a7_mem_Vg v).1 hv) with h4 | h4 | h4 | h4 <;> rw [h4]
        · rfl
        · exact h1
        · exact h2
        · exact h3
      · intro hi h
        have hxG : (⟨S7.x, S7.x_mem⟩ : ↥(alternatingGroup (Fin 7))) ∈ Vg :=
          (a7_mem_Vg _).2 S7.x_mem_V
        exact a7_moves i hi (h _ hxG)
    rw [Nat.card_congr (Equiv.subtypeEquivRight hmov), Nat.card_eq_fintype_card]
    decide

private theorem a7_sq_of_pow (z : Equiv.Perm (Fin 7)) (k : ℕ) (h1 : z ^ 2 ^ k = 1)
    (h2 : z ^ 6 = 1) : z ^ 2 = 1 := by
  have hd1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf z ∣ 6 := orderOf_dvd_of_pow_eq_one h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
  rw [hj] at hd2
  have hj2 : j ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have h4 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have h6 : 2 ^ 2 ∣ 6 := h4.trans hd2
    norm_num at h6
  have h2' : orderOf z ∣ 2 := by
    rw [hj]
    interval_cases j <;> simp
  exact orderOf_dvd_iff_pow_eq_one.1 h2'

private theorem a7_cent_eq (g : Equiv.Perm (Fin 7)) (hg : g ∈ alternatingGroup (Fin 7)) :
    (Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 7)))).subgroupOf
        (alternatingGroup (Fin 7)) =
      Subgroup.centralizer ({⟨g, hg⟩} : Set ↥(alternatingGroup (Fin 7))) := by
  ext h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hh
    exact Subtype.ext hh
  · intro hh
    exact congrArg Subtype.val hh

private theorem a7_le_pCore (N : Subgroup (Equiv.Perm (Fin 7))) (g : Equiv.Perm (Fin 7))
    (hg : g ∈ alternatingGroup (Fin 7)) (hNA : N ≤ alternatingGroup (Fin 7))
    (hNC : N ≤ Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 7))))
    (hN2 : IsPGroup 2 ↥N)
    (hnorm : ∀ c : Equiv.Perm (Fin 7), c * g = g * c → c ∈ Subgroup.normalizer (N : Set _)) :
    N.subgroupOf (alternatingGroup (Fin 7)) ≤
      pCoreOf 2 (Subgroup.centralizer ({⟨g, hg⟩} : Set ↥(alternatingGroup (Fin 7)))) := by
  have key := S7.le_pCoreOf_subgroupOf hNA hNC hN2
    (fun c _ hc => hnorm c (Subgroup.mem_centralizer_singleton_iff.1 hc))
  rw [a7_cent_eq g hg] at key
  exact key

private theorem a7_Vg_le_pCore :
    Vg ≤ pCoreOf 2 (Subgroup.centralizer ({aG} : Set ↥(alternatingGroup (Fin 7)))) :=
  a7_le_pCore S7.V S7.a a7_mem_a S7.V_le_Alt7 S7.V_le_centralizer S7.isPGroup_V
    (fun c h => S7.mem_normalizer_V_of_comm h)

private theorem a7_V'g_le_pCore :
    V'g ≤ pCoreOf 2 (Subgroup.centralizer ({bG} : Set ↥(alternatingGroup (Fin 7)))) :=
  a7_le_pCore S7.V' S7.b a7_mem_b S7.V'_le_Alt7 S7.V'_le_centralizer S7.isPGroup_V'
    (fun c h => S7.mem_normalizer_V'_of_comm h)

private abbrev CaG : Subgroup ↥(alternatingGroup (Fin 7)) :=
  Subgroup.centralizer ({aG} : Set ↥(alternatingGroup (Fin 7)))

private theorem a7_coe_comm (y : ↥CaG) :
    ((y : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) * S7.a =
      S7.a * ((y : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) :=
  congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2)

private theorem a7_coe_pow {H : Subgroup ↥(alternatingGroup (Fin 7))} (y : ↥H) (n : ℕ)
    (h : y ^ n = 1) : ((y : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) ^ n = 1 := by
  have := congrArg (fun t : ↥H => ((t : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7))) h
  simpa using this

private theorem a7_pCore_std : pCoreOf 2 CaG = Vg := by
  apply le_antisymm
  · intro w hw
    unfold pCoreOf at hw
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.1 hw
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥CaG)) ⟨y, hy⟩
    have hk2 : (y : ↥CaG) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hzs : Equiv.Perm.sign ((y : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) = 1 :=
      Equiv.Perm.mem_alternatingGroup.1 (y : ↥(alternatingGroup (Fin 7))).2
    have hz2 := a7_sq_of_pow _ k (a7_coe_pow y _ hk2) (a7_dec_pow6 _ hzs (a7_coe_comm y))
    have hzV := (a7_mem_V_iff _).2 (a7_dec_inv _ hzs (a7_coe_comm y) hz2)
    subst hyw
    exact (a7_mem_Vg _).2 hzV
  · exact a7_Vg_le_pCore

private noncomputable def a7Conj (σ : Equiv.Perm (Fin 7)) :
    ↥(alternatingGroup (Fin 7)) ≃* ↥(alternatingGroup (Fin 7)) :=
  MulAut.conjNormal σ

private theorem a7Conj_coe (σ : Equiv.Perm (Fin 7)) (g : ↥(alternatingGroup (Fin 7))) :
    ((a7Conj σ g : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) = σ * g * σ⁻¹ :=
  MulAut.conjNormal_apply σ g

private theorem a7Conj_symm_coe (σ : Equiv.Perm (Fin 7)) (g : ↥(alternatingGroup (Fin 7))) :
    (((a7Conj σ).symm g : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) = σ⁻¹ * g * σ :=
  MulAut.conjNormal_symm_apply σ g

private theorem a7_cent_map (f : ↥(alternatingGroup (Fin 7)) ≃* ↥(alternatingGroup (Fin 7)))
    (c : ↥(alternatingGroup (Fin 7))) :
    (Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7)))).map f.toMonoidHom =
      Subgroup.centralizer ({f c} : Set ↥(alternatingGroup (Fin 7))) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hh ⊢
    show f h * f c = f c * f h
    rw [← map_mul, hh, map_mul]
  · intro hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    refine ⟨f.symm g, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply f.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hg

private theorem a7_pCore_map (f : ↥(alternatingGroup (Fin 7)) ≃* ↥(alternatingGroup (Fin 7)))
    (c : ↥(alternatingGroup (Fin 7))) :
    pCoreOf 2 (Subgroup.centralizer ({f c} : Set ↥(alternatingGroup (Fin 7)))) =
      (pCoreOf 2 (Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7))))).map
        f.toMonoidHom := by
  rw [← a7_cent_map, CFSG.LargeExtraspecial.Bridge.pCoreOf_map]

private theorem a7_pCore_conj (σ : Equiv.Perm (Fin 7)) :
    pCoreOf 2 (Subgroup.centralizer ({a7Conj σ aG} : Set ↥(alternatingGroup (Fin 7)))) =
      Vg.map (a7Conj σ).toMonoidHom := by
  rw [a7_pCore_map, a7_pCore_std]

private theorem a7Conj_inj (σ : Equiv.Perm (Fin 7)) :
    Function.Injective (a7Conj σ).toMonoidHom :=
  (a7Conj σ).injective

private theorem a7_isRootFour_conj {W : Subgroup ↥(alternatingGroup (Fin 7))}
    (hW : IsRootFour W) (σ : Equiv.Perm (Fin 7)) :
    IsRootFour (W.map (a7Conj σ).toMonoidHom) := by
  obtain ⟨h1, h2, h3⟩ := hW
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (a7Conj_inj σ)]
    exact h1
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hv
    rw [← map_pow, h2 w hw, map_one]
  · have hfix : ∀ i : Fin 7,
        (∀ v ∈ W.map (a7Conj σ).toMonoidHom, (v : Equiv.Perm (Fin 7)) i = i) ↔
          (∀ w ∈ W, (w : Equiv.Perm (Fin 7)) (σ⁻¹ i) = σ⁻¹ i) := by
      intro i
      constructor
      · intro h w hw
        have hmem : ((a7Conj σ w : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) i = i :=
          h _ (Subgroup.mem_map_of_mem _ hw)
        rw [a7Conj_coe] at hmem
        simp only [Equiv.Perm.mul_apply] at hmem
        exact Equiv.Perm.eq_inv_iff_eq.2 hmem
      · intro h v hv
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hv
        show ((a7Conj σ w : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) i = i
        rw [a7Conj_coe]
        simp only [Equiv.Perm.mul_apply]
        rw [h w hw]
        simp
    have hiff : ∀ i : Fin 7,
        (¬ ∀ v ∈ W.map (a7Conj σ).toMonoidHom, (v : Equiv.Perm (Fin 7)) i = i) ↔
          (¬ ∀ w ∈ W, (w : Equiv.Perm (Fin 7)) (σ⁻¹ i) = σ⁻¹ i) :=
      fun i => not_congr (hfix i)
    rw [Nat.card_congr (Equiv.subtypeEquiv (σ⁻¹ : Equiv.Perm (Fin 7))
      (q := fun j => ¬ ∀ w ∈ W, (w : Equiv.Perm (Fin 7)) j = j) hiff)]
    exact h3

private theorem a7_sup_eq_top : Vg ⊔ V'g = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : (g : Equiv.Perm (Fin 7)) ∈ S7.V ⊔ S7.V' := S7.alternatingGroup_le_sup g.2
  rw [← Subgroup.subgroupOf_sup S7.V_le_Alt7 S7.V'_le_Alt7]
  exact Subgroup.mem_subgroupOf.2 hg

private theorem a7_Tg_isP3 : IsPGroup 3 ↥Tg :=
  S7.isPGroup_T.of_equiv (Subgroup.subgroupOfEquivOfLe a7_T_le).symm

private theorem a7_Tg_card : Nat.card ↥Tg = 9 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe a7_T_le).toEquiv, S7.card_T]

private theorem a7_Tg_le : Tg ≤ Subgroup.centralizer ({aG} : Set ↥(alternatingGroup (Fin 7))) := by
  intro g hg
  have hgT : (g : Equiv.Perm (Fin 7)) ∈ S7.T := Subgroup.mem_subgroupOf.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (a7_T_le_cent hgT))

private theorem a7_comm_mem (h k : Equiv.Perm (Fin 7)) (hh : h ∈ S7.V)
    (hk : k ∈ Subgroup.normalizer (S7.V : Set (Equiv.Perm (Fin 7)))) :
    h * k * h⁻¹ * k⁻¹ ∈ S7.V := by
  have h1 : k * h⁻¹ * k⁻¹ ∈ S7.V := (Subgroup.mem_normalizer_iff.1 hk h⁻¹).1 (S7.V.inv_mem hh)
  have h2 := S7.V.mul_mem hh h1
  simpa [mul_assoc] using h2

private theorem a7_std_comm (w : ↥(alternatingGroup (Fin 7))) (hw : w ∈ Vg) (hw1 : w ≠ 1) :
    ⁅Subgroup.zpowers w, Tg⁆ = Vg := by
  have hwS : (w : Equiv.Perm (Fin 7)) ∈ S7.V := (a7_mem_Vg w).1 hw
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    rintro g₁ hg₁ g₂ hg₂
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₁
    rw [a7_mem_Vg]
    have hk : ((g₂ : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) ∈
        Subgroup.normalizer (S7.V : Set (Equiv.Perm (Fin 7))) :=
      S7.T_le_normalizer_V (Subgroup.mem_subgroupOf.1 hg₂)
    have hh : (w : Equiv.Perm (Fin 7)) ^ i ∈ S7.V := zpow_mem hwS i
    have key := a7_comm_mem _ _ hh hk
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    exact key
  · intro v hv
    have hvF := (a7_mem_V_iff _).1 ((a7_mem_Vg v).1 hv)
    have hwF0 := (a7_mem_V_iff _).1 hwS
    have hwF : (w : Equiv.Perm (Fin 7)) = S7.x ∨ (w : Equiv.Perm (Fin 7)) = S7.y ∨
        (w : Equiv.Perm (Fin 7)) = S7.x * S7.y := by
      rcases hwF0 with h | h | h | h
      · exfalso
        exact hw1 (Subtype.ext h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hP := a7_comm_all (w : Equiv.Perm (Fin 7)) (by
      rcases hwF with h | h | h <;> simp [h])
    have hgen := a7_gen_all (v : Equiv.Perm (Fin 7)) (by
        rcases hvF with h | h | h | h <;> simp [h])
      (⁅(w : Equiv.Perm (Fin 7)), S7.b⁆) (by rcases hP.1 with h | h | h <;> simp [h])
      (⁅(w : Equiv.Perm (Fin 7)), S7.b ^ 2⁆) (by rcases hP.2.1 with h | h | h <;> simp [h])
      hP.2.2
    have hbT : bG ∈ Tg := Subgroup.mem_subgroupOf.2 S7.b_mem_T
    have hK1 : ⁅w, bG⁆ ∈ ⁅Subgroup.zpowers w, Tg⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers w) hbT
    have hK2 : ⁅w, bG ^ 2⁆ ∈ ⁅Subgroup.zpowers w, Tg⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers w) (pow_mem hbT 2)
    have e1 : ((⁅w, bG⁆ : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) =
        ⁅(w : Equiv.Perm (Fin 7)), S7.b⁆ := by
      simp [commutatorElement_def, bG]
    have e2 : ((⁅w, bG ^ 2⁆ : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) =
        ⁅(w : Equiv.Perm (Fin 7)), S7.b ^ 2⁆ := by
      simp [commutatorElement_def, bG]
    rcases hgen with h | h | h | h
    · have hv1 : v = 1 := Subtype.ext h
      rw [hv1]
      exact one_mem _
    · have hv1 : v = ⁅w, bG⁆ := Subtype.ext (by rw [e1]; exact h)
      rw [hv1]
      exact hK1
    · have hv1 : v = ⁅w, bG ^ 2⁆ := Subtype.ext (by rw [e2]; exact h)
      rw [hv1]
      exact hK2
    · have hv1 : v = ⁅w, bG⁆ * ⁅w, bG ^ 2⁆ :=
        Subtype.ext (by rw [Subgroup.coe_mul, e1, e2]; exact h)
      rw [hv1]
      exact mul_mem hK1 hK2

private theorem a7_conj_exists (c : Equiv.Perm (Fin 7)) (hc : c.IsThreeCycle) :
    ∃ σ : Equiv.Perm (Fin 7), σ * S7.a * σ⁻¹ = c := by
  have ha : S7.a.IsThreeCycle := card_support_eq_three_iff.1 (by decide)
  have hconj : IsConj S7.a c :=
    Equiv.Perm.isConj_iff_cycleType_eq.2 (ha.cycleType.trans hc.cycleType.symm)
  exact isConj_iff.1 hconj

private theorem a7_conj_G (c : ↥(alternatingGroup (Fin 7)))
    (hc : (c : Equiv.Perm (Fin 7)).IsThreeCycle) :
    ∃ σ : Equiv.Perm (Fin 7), a7Conj σ aG = c := by
  obtain ⟨σ, hσ⟩ := a7_conj_exists _ hc
  exact ⟨σ, Subtype.ext (by rw [a7Conj_coe]; exact hσ)⟩

private theorem a7_inv_conj_eq (τ a : Equiv.Perm (Fin 7)) (h : τ * a = a * τ) :
    τ⁻¹ * a * τ = a := by
  calc τ⁻¹ * a * τ = τ⁻¹ * (a * τ) := mul_assoc _ _ _
    _ = τ⁻¹ * (τ * a) := by rw [h]
    _ = a := by group

theorem a7Fact1_holds : A7Fact1 := by
  intro c hc
  obtain ⟨σ, rfl⟩ := a7_conj_G c hc
  rw [a7_pCore_conj]
  exact a7_isRootFour_conj a7_isRootFour_Vg σ

theorem a7Fact2_holds : A7Fact2 := by
  intro c hc
  obtain ⟨σ, rfl⟩ := a7_conj_G c hc
  refine ⟨Tg.map (a7Conj σ).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact a7_Tg_isP3.map (a7Conj σ).toMonoidHom
  · rw [Subgroup.card_map_of_injective (a7Conj_inj σ), a7_Tg_card]
  · rw [← a7_cent_map]
    exact Subgroup.map_mono a7_Tg_le
  · intro x hx hx1
    rw [a7_pCore_conj] at hx ⊢
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
    have hw1 : w ≠ 1 := fun h => hx1 (by rw [h, map_one])
    rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator, a7_std_comm w hw hw1]

theorem a7Fact3_holds : A7Fact3 := by
  intro c c' hc hc' hcc'
  obtain ⟨σ, hσ⟩ := a7_conj_G c hc
  subst hσ
  set d : ↥(alternatingGroup (Fin 7)) := (a7Conj σ).symm c' with hd
  have hdc : a7Conj σ d = c' := (a7Conj σ).apply_symm_apply c'
  have hdS : (d : Equiv.Perm (Fin 7)) = σ⁻¹ * (c' : Equiv.Perm (Fin 7)) * σ :=
    a7Conj_symm_coe σ c'
  have hc'eq : (c' : Equiv.Perm (Fin 7)) = σ * (d : Equiv.Perm (Fin 7)) * σ⁻¹ := by
    rw [← a7Conj_coe, hdc]
  have hcomm : S7.a * (d : Equiv.Perm (Fin 7)) = (d : Equiv.Perm (Fin 7)) * S7.a := by
    have h1 : σ * S7.a * σ⁻¹ * (c' : Equiv.Perm (Fin 7)) =
        (c' : Equiv.Perm (Fin 7)) * (σ * S7.a * σ⁻¹) := by
      have h := congrArg Subtype.val hcc'
      exact h
    rw [hdS]
    calc S7.a * (σ⁻¹ * (c' : Equiv.Perm (Fin 7)) * σ)
        = σ⁻¹ * (σ * S7.a * σ⁻¹ * (c' : Equiv.Perm (Fin 7))) * σ := by group
      _ = σ⁻¹ * ((c' : Equiv.Perm (Fin 7)) * (σ * S7.a * σ⁻¹)) * σ := by rw [h1]
      _ = σ⁻¹ * (c' : Equiv.Perm (Fin 7)) * σ * S7.a := by group
  have hd3 : (d : Equiv.Perm (Fin 7)).support.card = 3 := by
    rw [hdS, show σ⁻¹ * (c' : Equiv.Perm (Fin 7)) * σ = σ⁻¹ * c' * (σ⁻¹)⁻¹ by simp,
      Equiv.Perm.support_conj, Finset.card_map]
    exact hc'.card_support
  have haS : ((a7Conj σ aG : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) =
      σ * S7.a * σ⁻¹ := a7Conj_coe σ aG
  rcases a7_dec_L3 (d : Equiv.Perm (Fin 7)) hd3 hcomm.symm with h | h | h
  · left
    have hdeq : d = aG := Subtype.ext h
    rw [← hdc, hdeq]
    exact Subgroup.mem_zpowers _
  · left
    have hdeq : d = aG ^ 2 := Subtype.ext (by rw [h]; rfl)
    rw [← hdc, hdeq, map_pow]
    exact pow_mem (Subgroup.mem_zpowers _) 2
  · right
    rw [haS, hc'eq, Equiv.Perm.support_conj, Equiv.Perm.support_conj]
    exact (Finset.disjoint_map _).2 h

theorem a7Fact4_holds : A7Fact4 := by
  intro c c' hc hc' hdisj
  obtain ⟨σ₁, hσ₁⟩ := a7_conj_exists (c : Equiv.Perm (Fin 7)) hc
  set d : Equiv.Perm (Fin 7) := σ₁⁻¹ * (c' : Equiv.Perm (Fin 7)) * σ₁ with hd
  have hd3 : d.support.card = 3 := by
    rw [hd, show σ₁⁻¹ * (c' : Equiv.Perm (Fin 7)) * σ₁ = σ₁⁻¹ * c' * (σ₁⁻¹)⁻¹ by simp,
      Equiv.Perm.support_conj, Finset.card_map]
    exact hc'.card_support
  have hA : S7.a.support = (c : Equiv.Perm (Fin 7)).support.map σ₁⁻¹.toEmbedding := by
    rw [← Equiv.Perm.support_conj]
    have e : σ₁⁻¹ * (c : Equiv.Perm (Fin 7)) * σ₁⁻¹⁻¹ = S7.a := by
      rw [← hσ₁]; group
    rw [e]
  have hB : d.support = (c' : Equiv.Perm (Fin 7)).support.map σ₁⁻¹.toEmbedding := by
    rw [hd, show σ₁⁻¹ * (c' : Equiv.Perm (Fin 7)) * σ₁ = σ₁⁻¹ * c' * (σ₁⁻¹)⁻¹ by simp,
      Equiv.Perm.support_conj]
  have hdisj' : Disjoint S7.a.support d.support := by
    rw [hA, hB]
    exact (Finset.disjoint_map _).2 hdisj
  obtain ⟨τ, hτa, hτd⟩ := a7_dec_L4 d hd3 hdisj'
  have hτa' : τ⁻¹ * S7.a * τ = S7.a := a7_inv_conj_eq τ _ hτa
  have hτd' : τ⁻¹ * S7.b * τ = d := by
    calc τ⁻¹ * S7.b * τ = τ⁻¹ * (S7.b * τ) := by group
      _ = τ⁻¹ * (τ * d) := by rw [hτd]
      _ = d := by group
  have hσa : σ₁ * τ⁻¹ * S7.a * (σ₁ * τ⁻¹)⁻¹ = (c : Equiv.Perm (Fin 7)) := by
    calc σ₁ * τ⁻¹ * S7.a * (σ₁ * τ⁻¹)⁻¹ = σ₁ * (τ⁻¹ * S7.a * τ) * σ₁⁻¹ := by group
      _ = σ₁ * S7.a * σ₁⁻¹ := by rw [hτa']
      _ = c := hσ₁
  have hσb : σ₁ * τ⁻¹ * S7.b * (σ₁ * τ⁻¹)⁻¹ = (c' : Equiv.Perm (Fin 7)) := by
    calc σ₁ * τ⁻¹ * S7.b * (σ₁ * τ⁻¹)⁻¹ = σ₁ * (τ⁻¹ * S7.b * τ) * σ₁⁻¹ := by group
      _ = σ₁ * d * σ₁⁻¹ := by rw [hτd']
      _ = c' := by rw [hd]; group
  have hfa : a7Conj (σ₁ * τ⁻¹) aG = c := Subtype.ext (by rw [a7Conj_coe]; exact hσa)
  have hfb : a7Conj (σ₁ * τ⁻¹) bG = c' := Subtype.ext (by rw [a7Conj_coe]; exact hσb)
  rw [← hfa, ← hfb, a7_pCore_map, a7_pCore_map, a7_pCore_std]
  have h2 : Vg.map (a7Conj (σ₁ * τ⁻¹)).toMonoidHom ⊔ V'g.map (a7Conj (σ₁ * τ⁻¹)).toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, a7_sup_eq_top,
      Subgroup.map_top_of_surjective (a7Conj (σ₁ * τ⁻¹)).toMonoidHom (a7Conj (σ₁ * τ⁻¹)).surjective]
  rw [eq_top_iff, ← h2]
  exact sup_le_sup le_rfl (Subgroup.map_mono a7_V'g_le_pCore)

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
