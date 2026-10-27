module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.GH74.GLS.C3.Layer2.FinModelDefs

public section

namespace CFSG.GH74.GLS.EvenAlt

open Equiv Perm Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def altSub (n : ℕ) : Subgroup (Amb n) := (alternatingGroup (Fin n)).prod ⊥

@[expose] def vSub (n : ℕ) : Subgroup (Amb n) :=
  (⊥ : Subgroup (Perm (Fin n))).prod
    (alternatingGroup (Fin 4) ⊓ Subgroup.centralizer ({x4} : Set (Perm (Fin 4))))

theorem mem_alt_inf_centralizer_x4_iff (d : Perm (Fin 4)) :
    d ∈ alternatingGroup (Fin 4) ⊓ Subgroup.centralizer ({x4} : Set (Perm (Fin 4))) ↔
      (d = 1 ∨ d = swap 0 1 * swap 2 3 ∨ d = swap 0 2 * swap 1 3 ∨ d = swap 0 3 * swap 1 2) := by
  rw [Subgroup.mem_inf, mem_alternatingGroup, Subgroup.mem_centralizer_singleton_iff]
  revert d
  decide

theorem mem_vSub_iff (n : ℕ) (p : Amb n) :
    p ∈ vSub n ↔ p.1 = 1 ∧ (p.2 = 1 ∨ p.2 = swap 0 1 * swap 2 3 ∨ p.2 = swap 0 2 * swap 1 3 ∨
      p.2 = swap 0 3 * swap 1 2) := by
  rw [← mem_alt_inf_centralizer_x4_iff]
  exact and_congr_left' Subgroup.mem_bot

theorem mem_altSub_iff (n : ℕ) (p : Amb n) :
    p ∈ altSub n ↔ p.1 ∈ alternatingGroup (Fin n) ∧ p.2 = 1 :=
  and_congr_right' Subgroup.mem_bot

theorem vSub_le (n : ℕ) : vSub n ≤ Fgrp n := by
  intro p hp
  obtain ⟨h1, h2⟩ := (mem_vSub_iff n p).1 hp
  have hd : p.2 ∈ alternatingGroup (Fin 4) ⊓ Subgroup.centralizer ({x4} : Set (Perm (Fin 4))) :=
    (mem_alt_inf_centralizer_x4_iff _).2 h2
  refine ⟨(Subgroup.mem_centralizer_singleton_iff.1 hd.2), ?_⟩
  rw [h1, map_one]
  exact (mem_alternatingGroup.1 hd.1).symm

theorem card_vSub (n : ℕ) : Nat.card (vSub n) = 4 := by
  rw [vSub, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_bot,
    one_mul, Nat.card_congr (Equiv.subtypeEquivRight mem_alt_inf_centralizer_x4_iff),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem vSub_isElementaryAbelian (n : ℕ) : CFSG.IsElementaryAbelian 2 ↥(vSub n) := by
  have hab : ∀ u ∈ vSub n, ∀ v ∈ vSub n, u * v = v * u := by
    intro u hu v hv
    obtain ⟨hu1, hu2⟩ := (mem_vSub_iff n u).1 hu
    obtain ⟨hv1, hv2⟩ := (mem_vSub_iff n v).1 hv
    refine Prod.ext (by simp [hu1, hv1]) ?_
    show u.2 * v.2 = v.2 * u.2
    rcases hu2 with h | h | h | h <;> rcases hv2 with h' | h' | h' | h' <;> rw [h, h'] <;> decide
  have hsq : ∀ u ∈ vSub n, u * u = 1 := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := (mem_vSub_iff n u).1 hu
    refine Prod.ext (by simp [hu1]) ?_
    show u.2 * u.2 = 1
    rcases hu2 with h | h | h | h <;> rw [h] <;> decide
  have : IsMulCommutative ↥(vSub n) := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
  have : (a : Amb n) * a = 1 := hsq a a.2
  apply Subtype.ext
  simp [sq, this]

theorem card_altSub (n : ℕ) : Nat.card (altSub n) = Nat.card (alternatingGroup (Fin n)) := by
  rw [altSub, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_bot,
    mul_one]

theorem card_alt_gt (n : ℕ) (hn : 5 ≤ n) : 24 < Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h5 : 120 ≤ n.factorial := by
    have h := Nat.factorial_le hn
    norm_num at h
    exact h
  omega

theorem eq_altSub_of_equiv (n : ℕ) (hn : 5 ≤ n) {KF : Subgroup (Amb n)} (hKF : KF ≤ Fgrp n)
    (e : ↥KF ≃* alternatingGroup (Fin n)) : KF = altSub n := by
  have h5 : 5 ≤ Nat.card (Fin n) := by
    simpa using hn
  have : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup h5
  have : IsSimpleGroup ↥KF := e.isSimpleGroup
  let π₂ : ↥KF →* Perm (Fin 4) := (MonoidHom.snd (Perm (Fin n)) (Perm (Fin 4))).comp KF.subtype
  have hker : π₂.ker = ⊥ ∨ π₂.ker = ⊤ := Subgroup.Normal.eq_bot_or_eq_top _
  have hcardKF : Nat.card KF = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
  have hlt := card_alt_gt n hn
  rcases hker with h | h
  · exfalso
    have hinj : Function.Injective π₂ := (MonoidHom.ker_eq_bot_iff π₂).1 h
    have hle := Nat.card_le_card_of_injective π₂ hinj
    rw [Nat.card_perm] at hle
    have h24 : (Nat.card (Fin 4)).factorial = 24 := by simp [Nat.factorial]
    omega
  · have hle : KF ≤ altSub n := by
      intro p hp
      have h2 : p.2 = 1 := by
        have hmem : (⟨p, hp⟩ : KF) ∈ π₂.ker := by rw [h]; trivial
        simpa [π₂] using hmem
      refine (mem_altSub_iff n p).2 ⟨?_, h2⟩
      have hs := (hKF hp).2
      rw [h2, map_one] at hs
      exact mem_alternatingGroup.2 hs
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_altSub, hcardKF])

theorem mem_vSub_of_fst_eq_one (n : ℕ) {p : Amb n} (hp : p ∈ Fgrp n) (h : p.1 = 1) :
    p ∈ vSub n := by
  have hd : p.2 ∈ alternatingGroup (Fin 4) ⊓ Subgroup.centralizer ({x4} : Set (Perm (Fin 4))) := by
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 hp.1⟩
    rw [mem_alternatingGroup, ← hp.2, h, map_one]
  exact ⟨h, hd⟩

theorem mem_vSub_iff_centralizes (n : ℕ) (hn : 5 ≤ n) {p : Amb n} (hp : p ∈ Fgrp n) :
    p ∈ vSub n ↔ ∀ k ∈ altSub n, p * k = k * p := by
  constructor
  · intro h k hk
    obtain ⟨h1, _⟩ := (mem_vSub_iff n p).1 h
    obtain ⟨_, hk2⟩ := (mem_altSub_iff n k).1 hk
    exact Prod.ext (by simp [h1]) (by simp [hk2])
  · intro h
    refine mem_vSub_of_fst_eq_one n hp ?_
    have h5 : 5 ≤ Nat.card (Fin n) := by
      simpa using hn
    have hs : p.1 ∈ Subgroup.centralizer (alternatingGroup (Fin n) : Set (Perm (Fin n))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro σ hσ
      have := congrArg Prod.fst (h (σ, 1) ((mem_altSub_iff n _).2 ⟨hσ, rfl⟩))
      simpa using this.symm
    have hCbot : Subgroup.centralizer (alternatingGroup (Fin n) : Set (Perm (Fin n))) = ⊥ := by
      by_contra hne
      have hnt :
          Nontrivial (Subgroup.centralizer (alternatingGroup (Fin n) : Set (Perm (Fin n)))) :=
        (Subgroup.nontrivial_iff_ne_bot _).2 hne
      have hle : alternatingGroup (Fin n) ≤
          Subgroup.centralizer (alternatingGroup (Fin n) : Set (Perm (Fin n))) :=
        Equiv.Perm.alternatingGroup_le_of_normal h5 hnt
      have hcomm : IsMulCommutative (alternatingGroup (Fin n)) :=
        ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hle b.2)) a a.2)⟩⟩
      have := alternatingGroup.isMulCommutative_iff_card_le_three.1 hcomm
      omega
    rw [hCbot] at hs
    exact Subgroup.mem_bot.1 hs

theorem fst_eq_one_iff_mem_vSub (n : ℕ) {p : Amb n} (hp : p ∈ Fgrp n) : p.1 = 1 ↔ p ∈ vSub n :=
  ⟨mem_vSub_of_fst_eq_one n hp, fun h => ((mem_vSub_iff n p).1 h).1⟩

theorem exists_mem_Fgrp_fst_eq (n : ℕ) (σ : Perm (Fin n)) : ∃ p ∈ Fgrp n, p.1 = σ := by
  rcases Int.units_eq_one_or (sign σ) with h | h
  · exact ⟨(σ, 1), ⟨by simp, by simp [h]⟩, rfl⟩
  · refine ⟨(σ, swap 0 1), ⟨?_, ?_⟩, rfl⟩
    · show swap (0 : Fin 4) 1 * x4 = x4 * swap 0 1
      decide
    · show sign σ = sign (swap (0 : Fin 4) 1)
      rw [h, sign_swap (by decide)]

theorem normal_alt_inf_centralizer_x4 :
    (alternatingGroup (Fin 4) ⊓ Subgroup.centralizer ({x4} : Set (Perm (Fin 4)))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_alt_inf_centralizer_x4_iff] at hn ⊢
  rcases hn with rfl | rfl | rfl | rfl <;> revert g <;> decide

theorem normal_vSub (n : ℕ) : (vSub n).Normal := by
  have := normal_alt_inf_centralizer_x4
  unfold vSub
  infer_instance

theorem exists_conj_mem_of_isSylowOf {G : Type*} [Group G] [Finite G] {P K : Subgroup G}
    (hP : IsSylowOf 2 P K) {x : G} (hxK : x ∈ K) (hx : orderOf x = 2) :
    ∃ g ∈ K, g * x * g⁻¹ ∈ P := by
  obtain ⟨Q, hQ⟩ := hP
  let x' : K := ⟨x, hxK⟩
  have hx' : orderOf x' = 2 := by rw [← hx]; exact Subgroup.orderOf_mk _ _
  have hpg : IsPGroup 2 (Subgroup.zpowers x') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx']; simp
  obtain ⟨Q₀, hQ₀⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q₀ Q
  have hmem : g * x' * g⁻¹ ∈ (Q : Subgroup K) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    have h1 : x' ∈ (Q₀ : Subgroup K) := hQ₀ (Subgroup.mem_zpowers x')
    have := Subgroup.smul_mem_pointwise_smul x' (MulAut.conj g) (Q₀ : Subgroup K) h1
    simpa using this
  refine ⟨g, g.2, ?_⟩
  rw [← hQ]
  exact ⟨g * x' * g⁻¹, hmem, rfl⟩

theorem no_commute_aux : ∀ d : Perm (Fin 4), d * x4 = x4 * d → sign d = -1 → d * d = 1 →
    d * (swap 0 2 * swap 1 3) ≠ (swap 0 2 * swap 1 3) * d := by
  decide

theorem fiveCase_model {T : Subgroup (Amb 5)} (hT : IsSylowOf 2 T (Fgrp 5)) :
    ∃ y ∈ T, orderOf y = 2 ∧ T = (T ⊓ altSub 5) ⊔ vSub 5 ⊔ zpowers y ∧
      ∃ q ∈ vSub 5, y * q ≠ q * y := by
  have hVT : vSub 5 ≤ T := by
    have := normal_vSub 5
    have := vSub_isElementaryAbelian 5
    have hpg : IsPGroup 2 (vSub 5) := IsElementaryAbelian.isPGroup 2 ↥(vSub 5)
    have h2 : IsPGroup 2 (vSub 5 ⊔ T : Subgroup (Amb 5)) := hpg.to_sup_of_normal_left hT.isPGroup
    exact le_sup_left.trans (hT.eq_of_le le_sup_right (sup_le (vSub_le 5) hT.le) h2).le
  have hy₀F : ((swap 0 1, swap 0 1) : Amb 5) ∈ Fgrp 5 := by
    refine ⟨?_, ?_⟩
    · show swap (0 : Fin 4) 1 * x4 = x4 * swap 0 1
      decide
    · show sign (swap (0 : Fin 5) 1) = sign (swap (0 : Fin 4) 1)
      rw [sign_swap (by decide), sign_swap (by decide)]
  have hy₀ord : orderOf ((swap 0 1, swap 0 1) : Amb 5) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq]
      exact Prod.ext (swap_mul_self _ _) (swap_mul_self _ _)
    · intro h
      have := congrArg Prod.fst h
      revert this
      decide
  obtain ⟨g, -, hyT⟩ := exists_conj_mem_of_isSylowOf hT hy₀F hy₀ord
  generalize hy : g * ((swap 0 1, swap 0 1) : Amb 5) * g⁻¹ = y at hyT
  have hyF : y ∈ Fgrp 5 := hT.le hyT
  have hyord : orderOf y = 2 := by
    rw [← hy₀ord]
    refine (SemiconjBy.orderOf_eq g ?_).symm
    rw [← hy]
    exact (inv_mul_cancel_right _ g).symm
  have hysign : sign y.1 = -1 := by
    rw [← hy]
    simp
  have key : ∀ s ∈ T, sign s.1 = 1 → s ∈ (T ⊓ altSub 5) ⊔ vSub 5 := by
    intro s hs hsign
    have hsF := hT.le hs
    have hd : s.2 ∈ alternatingGroup (Fin 4) ⊓ Subgroup.centralizer ({x4} : Set (Perm (Fin 4))) :=
      Subgroup.mem_inf.2 ⟨mem_alternatingGroup.2 (hsF.2.symm.trans hsign),
        Subgroup.mem_centralizer_singleton_iff.2 hsF.1⟩
    have hv : ((1, s.2) : Amb 5) ∈ vSub 5 :=
      (mem_vSub_iff 5 _).2 ⟨rfl, (mem_alt_inf_centralizer_x4_iff _).1 hd⟩
    have hn : ((s.1, 1) : Amb 5) ∈ T ⊓ altSub 5 := by
      refine Subgroup.mem_inf.2 ⟨?_, (mem_altSub_iff 5 _).2 ⟨mem_alternatingGroup.2 hsign, rfl⟩⟩
      have : ((s.1, 1) : Amb 5) = s * ((1, s.2) : Amb 5)⁻¹ := by ext <;> simp
      rw [this]
      exact T.mul_mem hs (T.inv_mem (hVT hv))
    have hs' : s = ((s.1, 1) : Amb 5) * ((1, s.2) : Amb 5) := by ext <;> simp
    rw [hs']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hv)
  refine ⟨y, hyT, hyord, ?_, ((1, swap 0 2 * swap 1 3) : Amb 5), ?_, ?_⟩
  · apply le_antisymm
    · intro t ht
      rcases Int.units_eq_one_or (sign t.1) with h | h
      · exact Subgroup.mem_sup_left (key t ht h)
      · have hyt : y⁻¹ * t ∈ T := T.mul_mem (T.inv_mem hyT) ht
        have hs : sign (y⁻¹ * t).1 = 1 := by
          simp [h, hysign]
        have h2 := key _ hyt hs
        have : t = y * (y⁻¹ * t) := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
          (Subgroup.mem_sup_left h2)
    · exact sup_le (sup_le inf_le_left hVT) (Subgroup.zpowers_le.2 hyT)
  · exact (mem_vSub_iff 5 _).2 ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩
  · intro h
    have h2 := congrArg Prod.snd h
    have hysq : y * y = 1 := by
      rw [← sq, ← hyord]
      exact pow_orderOf_eq_one y
    exact no_commute_aux y.2 hyF.1 (hyF.2.symm.trans hysign) (congrArg Prod.snd hysq) h2

end CFSG.GH74.GLS.EvenAlt
