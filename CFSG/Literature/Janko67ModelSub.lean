module

public import CFSG.Literature.Janko67ModelCore
public import CFSG.GroupTheory.ExtraspecialElementaryAbelianBound
public import CFSG.LargeExtraspecial.DWTim79.Bridge
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.Literature.Janko67ModelSubPack

public section

namespace CFSG.Literature.Janko67

open CFSG.RankThree.GF2n.Parrott CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Pointwise
open CFSG.Permutation.FinPack64 (pk_mul eq_of_pk conj_of pk_conj)
open CFSG.RankThree.GF2n.Parrott.Pack45 (h45 pk_t pk_u pk_a1 pk_b1 pk_a2 pk_b2 pk_s1 pk_s2
  pk_a1i pk_b1i pk_s1i pk_s2i)


private instance factPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private def q0Word (p : Fin 5 → Fin 2) : C0 :=
  a1C ^ (p 0 : ℕ) * b1C ^ (p 1 : ℕ) * a2C ^ (p 2 : ℕ) * b2C ^ (p 3 : ℕ) *
    tC ^ (p 4 : ℕ)

private def q0Set : Finset C0 := (Finset.univ : Finset (Fin 5 → Fin 2)).image q0Word

private def q0PermWord (p : Fin 5 → Fin 2) : Equiv.Perm (Fin 45) :=
  alpha1 ^ (p 0 : ℕ) * beta1 ^ (p 1 : ℕ) * alpha2 ^ (p 2 : ℕ) * beta2 ^ (p 3 : ℕ) *
    t ^ (p 4 : ℕ)

private def q0PermSet : Finset (Equiv.Perm (Fin 45)) :=
  (Finset.univ : Finset (Fin 5 → Fin 2)).image q0PermWord

private theorem q0PermWord_inj : Function.Injective q0PermWord := by
  decide +kernel

private theorem q0PermSet_card : q0PermSet.card = 32 := by
  rw [q0PermSet, Finset.card_image_of_injective]
  · simp
  · exact q0PermWord_inj

private theorem q0Word_val (p : Fin 5 → Fin 2) : (q0Word p).val.val = q0PermWord p := by
  rfl

private theorem q0Set_val_image : q0Set.image (fun x : C0 => x.val.val) = q0PermSet := by
  ext y
  constructor
  · intro hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [q0Set, Finset.mem_image] at hx
    obtain ⟨p, -, rfl⟩ := hx
    rw [q0PermSet, Finset.mem_image]
    exact ⟨p, Finset.mem_univ _, (q0Word_val p).symm⟩
  · intro hy
    rw [q0PermSet, Finset.mem_image] at hy
    obtain ⟨p, -, rfl⟩ := hy
    rw [Finset.mem_image]
    exact ⟨q0Word p, by rw [q0Set, Finset.mem_image]; exact ⟨p, Finset.mem_univ _, rfl⟩,
      q0Word_val p⟩

private theorem q0Set_card : q0Set.card = 32 := by
  have h := congrArg Finset.card q0Set_val_image
  rw [Finset.card_image_of_injective] at h
  · rw [h, q0PermSet_card]
  · intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)

private theorem q0Set_subset : (q0Set : Set C0) ⊆ (CFSG.pCore 2 C0 : Set C0) := by
  intro x hx
  rw [q0Set, Finset.mem_coe, Finset.mem_image] at hx
  obtain ⟨p, -, rfl⟩ := hx
  rw [pCore_C0_eq]
  have ha1 : a1C ∈ Subgroup.closure ({a1C, b1C, a2C, b2C} : Set C0) :=
    Subgroup.subset_closure (by simp)
  have hb1 : b1C ∈ Subgroup.closure ({a1C, b1C, a2C, b2C} : Set C0) :=
    Subgroup.subset_closure (by simp)
  have ha2 : a2C ∈ Subgroup.closure ({a1C, b1C, a2C, b2C} : Set C0) :=
    Subgroup.subset_closure (by simp)
  have hb2 : b2C ∈ Subgroup.closure ({a1C, b1C, a2C, b2C} : Set C0) :=
    Subgroup.subset_closure (by simp)
  have ht : tC ∈ Subgroup.closure ({a1C, b1C, a2C, b2C} : Set C0) := by
    rw [show tC = a1C * a1C from by
      apply Subtype.ext; apply Subtype.ext; show t = alpha1 * alpha1
      exact alpha1_sq.symm]
    exact Subgroup.mul_mem _ ha1 ha1
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.pow_mem _ ha1 _) (Subgroup.pow_mem _ hb1 _))
        (Subgroup.pow_mem _ ha2 _))
      (Subgroup.pow_mem _ hb2 _))
    (Subgroup.pow_mem _ ht _)

private theorem q0Set_eq : (q0Set : Set C0) = (CFSG.pCore 2 C0 : Set C0) := by
  apply Set.eq_of_subset_of_ncard_le q0Set_subset
  · have hp : (CFSG.pCore 2 C0 : Set C0).ncard = 32 := by
      rw [← Nat.card_coe_set_eq]
      exact card_pCore_C0
    rw [hp, Set.ncard_coe_finset, q0Set_card]

private theorem uC_not_mem_q0Set : uC ∉ q0Set := by
  intro h
  have hu : u ∈ q0PermSet := by
    have h' : uC.val.val ∈ q0Set.image (fun x : C0 => x.val.val) :=
      Finset.mem_image_of_mem _ h
    rw [q0Set_val_image] at h'
    exact h'
  revert hu
  decide +kernel

private theorem uC_not_mem_pCore : uC ∉ CFSG.pCore 2 C0 := by
  change uC ∉ (CFSG.pCore 2 C0 : Set C0)
  rw [← q0Set_eq]
  exact uC_not_mem_q0Set

private theorem orderOf_uC : orderOf uC = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two]
    apply Subtype.ext
    apply Subtype.ext
    show u * u = 1
    exact u_sq
  · intro h
    apply u_ne_one
    have h1 : (uC : C0).val = (1 : C0).val := Subtype.ext_iff.mp h
    have h2 : ((uC : C0).val).val = ((1 : C0).val).val := Subtype.ext_iff.mp h1
    exact h2

noncomputable def iotaC : C0 →* ↥QA45.originalSubgroup :=
  (Subgroup.inclusion QP45_le_QA45).comp C0.subtype

private theorem iotaC_tC : iotaC tC = (⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup) := by
  apply Subtype.ext
  rfl

private theorem iotaC_uC : iotaC uC = (⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup) := by
  apply Subtype.ext
  rfl

private theorem iotaC_a1a2 : iotaC (a1C * a2C) =
    (⟨alpha1, alpha1_mem_A⟩ : ↥QA45.originalSubgroup) *
      (⟨alpha2, alpha2_mem_A⟩ : ↥QA45.originalSubgroup) := by
  apply Subtype.ext
  rfl

private theorem iotaC_b1b2 : iotaC (b1C * b2C) =
    (⟨beta1, beta1_mem_A⟩ : ↥QA45.originalSubgroup) *
      (⟨beta2, beta2_mem_A⟩ : ↥QA45.originalSubgroup) := by
  apply Subtype.ext
  rfl

theorem iotaC_injective : Function.Injective iotaC := by
  intro x y h
  have h1 : (iotaC x).val = (iotaC y).val := Subtype.ext_iff.mp h
  exact Subtype.ext (Subtype.ext h1)

theorem map_S0_iotaC : S0.map iotaC = sQA45 := by
  have h1 : S0.map iotaC =
      Subgroup.closure (iotaC '' ({tC, uC, a1C * a2C, b1C * b2C} : Set C0)) := by
    rw [S0, MonoidHom.map_closure]
  have h2 : iotaC '' ({tC, uC, a1C * a2C, b1C * b2C} : Set C0) =
      ({⟨u, u_mem_A⟩, ⟨alpha1, alpha1_mem_A⟩ * ⟨alpha2, alpha2_mem_A⟩,
        ⟨beta1, beta1_mem_A⟩ * ⟨beta2, beta2_mem_A⟩, ⟨t, t_mem_A⟩} :
        Set ↥QA45.originalSubgroup) := by
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr iotaC_tC))
      · exact Or.inl iotaC_uC
      · exact Or.inr (Or.inl iotaC_a1a2)
      · exact Or.inr (Or.inr (Or.inl iotaC_b1b2))
    · intro hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨uC, Or.inr (Or.inl rfl), iotaC_uC⟩
      · exact ⟨a1C * a2C, Or.inr (Or.inr (Or.inl rfl)), iotaC_a1a2⟩
      · exact ⟨b1C * b2C, Or.inr (Or.inr (Or.inr rfl)), iotaC_b1b2⟩
      · exact ⟨tC, Or.inl rfl, iotaC_tC⟩
  rw [h1, h2]
  rfl

theorem S0_le_P0 : S0 ≤ P0 := by
  rw [S0, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [show tC = a1C * a1C from by
      apply Subtype.ext; apply Subtype.ext; show t = alpha1 * alpha1
      exact alpha1_sq.symm]
    exact P0.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · exact Subgroup.subset_closure (by simp)
  · exact P0.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · exact P0.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem card_S0 : Nat.card S0 = 16 := by
  rw [← Subgroup.card_map_of_injective iotaC_injective, map_S0_iotaC, card_sQA45]
  norm_num

theorem mul_self_eq_one_of_mem_S0 {s : C0} (hs : s ∈ S0) : s * s = 1 := by
  have hmem : iotaC s ∈ sQA45 := by
    rw [← map_S0_iotaC]
    exact Subgroup.mem_map_of_mem _ hs
  have h2 : (iotaC s) ^ 2 = 1 := isElemAbelian_sQA45.2 (iotaC s) hmem
  apply iotaC_injective
  rw [map_mul, map_one]
  simpa [sq] using h2

theorem card_P0 : Nat.card P0 = 64 := by
  have hP0 : P0 = Subgroup.zpowers uC ⊔ CFSG.pCore 2 C0 := by
    rw [P0]
    rw [show ({uC, a1C, b1C, a2C, b2C} : Set C0) =
        {uC} ∪ ({a1C, b1C, a2C, b2C} : Set C0) from rfl,
      Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, pCore_C0_eq]
  have hinf : Subgroup.zpowers uC ⊓ CFSG.pCore 2 C0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx.1
    rw [← zpow_mod_orderOf, orderOf_uC] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [Nat.cast_ofNat, h0, zpow_zero] at hk
      exact hk.symm
    · rw [Nat.cast_ofNat, h1, zpow_one] at hk
      exact absurd (hk.symm ▸ hx.2) uC_not_mem_pCore
  have hcard := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := Subgroup.zpowers uC) (K := CFSG.pCore 2 C0)
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  rw [hP0]
  have h := hcard
  rw [hinf, Subgroup.card_bot, mul_one, card_pCore_C0, Nat.card_zpowers, orderOf_uC] at h
  rw [h]

private def s0Word (p : Fin 4 → Fin 2) : C0 :=
  tC ^ (p 0 : ℕ) * uC ^ (p 1 : ℕ) * (a1C * a2C) ^ (p 2 : ℕ) *
    (b1C * b2C) ^ (p 3 : ℕ)

private def s0Set : Finset C0 := (Finset.univ : Finset (Fin 4 → Fin 2)).image s0Word

private def s0PermWord (p : Fin 4 → Fin 2) : Equiv.Perm (Fin 45) :=
  t ^ (p 0 : ℕ) * u ^ (p 1 : ℕ) * (alpha1 * alpha2) ^ (p 2 : ℕ) *
    (beta1 * beta2) ^ (p 3 : ℕ)

private def s0PermSet : Finset (Equiv.Perm (Fin 45)) :=
  (Finset.univ : Finset (Fin 4 → Fin 2)).image s0PermWord

private theorem s0PermWord_inj : Function.Injective s0PermWord := by
  decide +kernel

private theorem s0PermSet_card : s0PermSet.card = 16 := by
  rw [s0PermSet, Finset.card_image_of_injective]
  · simp
  · exact s0PermWord_inj

private theorem s0Word_val (p : Fin 4 → Fin 2) : (s0Word p).val.val = s0PermWord p := by
  rfl

private theorem s0Set_val_image : s0Set.image (fun x : C0 => x.val.val) = s0PermSet := by
  ext y
  constructor
  · intro hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [s0Set, Finset.mem_image] at hx
    obtain ⟨p, -, rfl⟩ := hx
    rw [s0PermSet, Finset.mem_image]
    exact ⟨p, Finset.mem_univ _, (s0Word_val p).symm⟩
  · intro hy
    rw [s0PermSet, Finset.mem_image] at hy
    obtain ⟨p, -, rfl⟩ := hy
    rw [Finset.mem_image]
    refine ⟨s0Word p, ?_, s0Word_val p⟩
    rw [s0Set, Finset.mem_image]
    exact ⟨p, Finset.mem_univ _, rfl⟩

private theorem s0Set_card : s0Set.card = 16 := by
  have h := congrArg Finset.card s0Set_val_image
  rw [Finset.card_image_of_injective] at h
  · rw [h, s0PermSet_card]
  · intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)

private theorem s0Set_subset : (s0Set : Set C0) ⊆ (S0 : Set C0) := by
  intro x hx
  rw [s0Set, Finset.mem_coe, Finset.mem_image] at hx
  obtain ⟨p, -, rfl⟩ := hx
  rw [S0]
  have ht : tC ∈ Subgroup.closure ({tC, uC, a1C * a2C, b1C * b2C} : Set C0) :=
    Subgroup.subset_closure (by simp)
  have hu : uC ∈ Subgroup.closure ({tC, uC, a1C * a2C, b1C * b2C} : Set C0) :=
    Subgroup.subset_closure (by simp)
  have ha : a1C * a2C ∈ Subgroup.closure ({tC, uC, a1C * a2C, b1C * b2C} : Set C0) :=
    Subgroup.subset_closure (by simp)
  have hb : b1C * b2C ∈ Subgroup.closure ({tC, uC, a1C * a2C, b1C * b2C} : Set C0) :=
    Subgroup.subset_closure (by simp)
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ ht _) (Subgroup.pow_mem _ hu _))
      (Subgroup.pow_mem _ ha _))
    (Subgroup.pow_mem _ hb _)

private theorem s0Set_eq_S0 : (s0Set : Set C0) = (S0 : Set C0) := by
  apply Set.eq_of_subset_of_ncard_le s0Set_subset
  · rw [Set.ncard_coe_finset, s0Set_card]
    exact le_of_eq card_S0

private theorem mem_s0Set_iff (x : C0) : x.val.val ∈ s0PermSet ↔ x ∈ s0Set := by
  rw [← s0Set_val_image]
  constructor
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨y, hy, hxy⟩ := h
    have : y = x := Subtype.ext (Subtype.ext hxy)
    rwa [this] at hy
  · intro hx
    rw [Finset.mem_image]
    exact ⟨x, hx, rfl⟩

private theorem mem_q0Set_iff (x : C0) : x.val.val ∈ q0PermSet ↔ x ∈ q0Set := by
  rw [← q0Set_val_image]
  constructor
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨y, hy, hxy⟩ := h
    have : y = x := Subtype.ext (Subtype.ext hxy)
    rwa [this] at hy
  · intro hx
    rw [Finset.mem_image]
    exact ⟨x, hx, rfl⟩

private def outWord (p : Fin 5 → Fin 2) : Equiv.Perm (Fin 45) :=
  u * q0PermWord p

private theorem outWord_involution_mem :
    ∀ p : Fin 5 → Fin 2, outWord p * outWord p = 1 → outWord p ∈ s0PermSet := by
  intro p h
  obtain ⟨q, hq⟩ := Pack.out_sound p h
  exact Finset.mem_image.2 ⟨q, Finset.mem_univ _, hq⟩

private theorem uC_val : uC.val.val = u := rfl

private theorem mem_S0_of_uC_mul_of_mem_q0Set {q : C0} (hq : q ∈ q0Set)
    (h2 : (uC * q) * (uC * q) = 1) : uC * q ∈ S0 := by
  rw [q0Set, Finset.mem_image] at hq
  obtain ⟨p, -, rfl⟩ := hq
  have hp2 : outWord p * outWord p = 1 := by
    have h := congrArg (fun z : C0 => z.val.val) h2
    simpa [outWord, q0Word_val, uC_val] using h
  have hval : (uC * q0Word p).val.val = outWord p := by
    simp [outWord, uC_val, q0Word_val]
  have hmem : (uC * q0Word p).val.val ∈ s0PermSet := by
    rw [hval]
    exact outWord_involution_mem p hp2
  have hmemSet : uC * q0Word p ∈ (s0Set : Set C0) := (mem_s0Set_iff _).mp hmem
  rw [s0Set_eq_S0] at hmemSet
  exact hmemSet

private theorem uC_sq : uC * uC = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  show u * u = 1
  exact u_sq

private theorem zpowers_uC_eq : (Subgroup.zpowers uC : Set C0) = {1, uC} := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, orderOf_uC] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [Nat.cast_ofNat, h0, zpow_zero] at hk
      rw [hk]
      simp
    · rw [Nat.cast_ofNat, h1, zpow_one] at hk
      rw [hk]
      simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers uC

private theorem P0_eq_sup : P0 = CFSG.pCore 2 C0 ⊔ Subgroup.zpowers uC := by
  rw [P0]
  rw [show ({uC, a1C, b1C, a2C, b2C} : Set C0) =
      {uC} ∪ ({a1C, b1C, a2C, b2C} : Set C0) from rfl,
    Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, pCore_C0_eq, sup_comm]

private theorem mem_S0_of_involution_of_mem_P0_of_not_mem_pCore {x : C0}
    (hxP : x ∈ P0) (hxQ : x ∉ CFSG.pCore 2 C0) (hx2 : x * x = 1) : x ∈ S0 := by
  have hxsup : x ∈ CFSG.pCore 2 C0 ⊔ Subgroup.zpowers uC := by
    rw [← P0_eq_sup]
    exact hxP
  obtain ⟨q, hqQ, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxsup
  have hh' : h = 1 ∨ h = uC := by
    have hhset : h ∈ ({1, uC} : Set C0) := by
      rw [← zpowers_uC_eq]
      exact hh
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hhset
  rcases hh' with rfl | rfl
  · exact absurd hqQ hxQ
  · have hq'Q : uC * q * uC ∈ CFSG.pCore 2 C0 := by
      have hconj := (CFSG.pCore_normal (p := 2) (G := C0)).conj_mem q hqQ uC
      have huCinv : uC⁻¹ = uC := inv_eq_of_mul_eq_one_right uC_sq
      simpa [huCinv] using hconj
    have hq'q0 : uC * q * uC ∈ q0Set := by
      change uC * q * uC ∈ (q0Set : Set C0)
      rw [q0Set_eq]
      exact hq'Q
    have heq : uC * (uC * q * uC) = q * uC := by
      calc uC * (uC * q * uC) = (uC * uC) * (q * uC) := by group
        _ = q * uC := by rw [uC_sq, one_mul]
    have hq2 : (uC * (uC * q * uC)) * (uC * (uC * q * uC)) = 1 := by
      rw [heq]
      exact hx2
    have hS := mem_S0_of_uC_mul_of_mem_q0Set hq'q0 hq2
    rwa [heq] at hS

private theorem not_le_pCore_of_card_sixteen {A : Subgroup C0} (hcard : Nat.card A = 16)
    (h2 : ∀ a ∈ A, a * a = 1) : ¬ A ≤ CFSG.pCore 2 C0 := by
  intro hAQ
  have hAcomm : ∀ a b : C0, a ∈ A → b ∈ A → a * b = b * a := by
    intro a b ha hb
    have haa : a * a = 1 := h2 a ha
    have hbb : b * b = 1 := h2 b hb
    have hab : (a * b) * (a * b) = 1 := h2 (a * b) (A.mul_mem ha hb)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
      _ = b * a := by rw [inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right hbb]
  have hU : CFSG.Open.IsElemAbelian 2 (A ⊓ CFSG.pCore 2 C0) := by
    refine ⟨IsMulCommutative.of_comm (fun (x y : ↥(A ⊓ CFSG.pCore 2 C0)) =>
      Subtype.ext (hAcomm x.1 y.1 x.2.1 y.2.1)), ?_⟩
    intro x hx
    simpa [sq] using h2 x hx.1
  have hext : CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 (CFSG.pCore 2 C0) :=
    (CFSG.LargeExtraspecial.DWTim79.isExtraspecialPGroup_iff_isExtraspecial2
      (CFSG.pCore 2 C0)).mp isExtraspecialPGroup_pCore_C0
  have hbound := CFSG.GroupTheory.card_le_two_pow_succ_of_isElemAbelian
    (J := CFSG.pCore 2 C0) hext (n := 2) (by rw [card_pCore_C0]; norm_num)
    (inf_le_right : A ⊓ CFSG.pCore 2 C0 ≤ CFSG.pCore 2 C0) hU
  rw [show A ⊓ CFSG.pCore 2 C0 = A from inf_eq_left.mpr hAQ, hcard] at hbound
  norm_num at hbound

theorem eq_S0_of_le_P0 {A : Subgroup C0} (hA : A ≤ P0) (hcard : Nat.card A = 16)
    (h2 : ∀ a ∈ A, a * a = 1) : A = S0 := by
  have hAcomm : ∀ a b : C0, a ∈ A → b ∈ A → a * b = b * a := by
    intro a b ha hb
    have haa : a * a = 1 := h2 a ha
    have hbb : b * b = 1 := h2 b hb
    have hab : (a * b) * (a * b) = 1 := h2 (a * b) (A.mul_mem ha hb)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
      _ = b * a := by rw [inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right hbb]
  have hnotle : ¬ A ≤ CFSG.pCore 2 C0 := not_le_pCore_of_card_sixteen hcard h2
  obtain ⟨x, hxA, hxQ⟩ := Set.not_subset.mp hnotle
  have hx2 : x * x = 1 := h2 x hxA
  have hxS : x ∈ S0 :=
    mem_S0_of_involution_of_mem_P0_of_not_mem_pCore (hA hxA) hxQ hx2
  have hle : A ≤ S0 := by
    intro a ha
    by_cases haQ : a ∈ CFSG.pCore 2 C0
    · have haxQ : a * x ∉ CFSG.pCore 2 C0 := by
        intro h
        apply hxQ
        have heq : x = a⁻¹ * (a * x) := by group
        rw [heq]
        exact (CFSG.pCore 2 C0).mul_mem ((CFSG.pCore 2 C0).inv_mem haQ) h
      have hax2 : (a * x) * (a * x) = 1 := by
        have haa : a * a = 1 := h2 a ha
        have hcomm : a * x = x * a := hAcomm a x ha hxA
        calc (a * x) * (a * x) = a * (x * a) * x := by group
          _ = a * (a * x) * x := by rw [hcomm]
          _ = (a * a) * (x * x) := by group
          _ = 1 := by rw [haa, hx2, mul_one]
      have haxP : a * x ∈ P0 := hA (A.mul_mem ha hxA)
      have haxS : a * x ∈ S0 :=
        mem_S0_of_involution_of_mem_P0_of_not_mem_pCore haxP haxQ hax2
      have heq : a = (a * x) * x⁻¹ := by group
      rw [heq]
      exact S0.mul_mem haxS (S0.inv_mem hxS)
    · exact mem_S0_of_involution_of_mem_P0_of_not_mem_pCore (hA ha) haQ (h2 a ha)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_S0, hcard])

private theorem tC_mem_S0 : tC ∈ S0 := by
  rw [S0]
  exact Subgroup.subset_closure (by simp)

private theorem uC_mem_S0 : uC ∈ S0 := by
  rw [S0]
  exact Subgroup.subset_closure (by simp)

private theorem a1a2_mem_S0 : a1C * a2C ∈ S0 := by
  rw [S0]
  exact Subgroup.subset_closure (by simp)

private theorem b1b2_mem_S0 : b1C * b2C ∈ S0 := by
  rw [S0]
  exact Subgroup.subset_closure (by simp)

private theorem conj_a1_t : a1C * tC * a1C⁻¹ = tC := by
  apply Subtype.ext
  apply Subtype.ext
  show alpha1 * t * alpha1⁻¹ = t
  exact conj_of h45 pk_a1 pk_t pk_t (by decide +kernel)

private theorem conj_a1_u : a1C * uC * a1C⁻¹ = tC * uC * (a1C * a2C) := by
  apply Subtype.ext
  apply Subtype.ext
  show alpha1 * u * alpha1⁻¹ = t * u * (alpha1 * alpha2)
  exact conj_of h45 pk_a1 pk_u (pk_mul h45 (pk_mul h45 pk_t pk_u) (pk_mul h45 pk_a1 pk_a2))
    (by decide +kernel)

private theorem conj_a1_a1a2 : a1C * (a1C * a2C) * a1C⁻¹ = a1C * a2C := by
  apply Subtype.ext
  apply Subtype.ext
  show alpha1 * (alpha1 * alpha2) * alpha1⁻¹ = alpha1 * alpha2
  exact conj_of h45 pk_a1 (pk_mul h45 pk_a1 pk_a2) (pk_mul h45 pk_a1 pk_a2) (by decide +kernel)

private theorem conj_a1_b1b2 : a1C * (b1C * b2C) * a1C⁻¹ = tC * (b1C * b2C) := by
  apply Subtype.ext
  apply Subtype.ext
  show alpha1 * (beta1 * beta2) * alpha1⁻¹ = t * (beta1 * beta2)
  exact conj_of h45 pk_a1 (pk_mul h45 pk_b1 pk_b2) (pk_mul h45 pk_t (pk_mul h45 pk_b1 pk_b2))
    (by decide +kernel)

private theorem conj_b1_t : b1C * tC * b1C⁻¹ = tC := by
  apply Subtype.ext
  apply Subtype.ext
  show beta1 * t * beta1⁻¹ = t
  exact conj_of h45 pk_b1 pk_t pk_t (by decide +kernel)

private theorem conj_b1_u : b1C * uC * b1C⁻¹ = tC * uC * (b1C * b2C) := by
  apply Subtype.ext
  apply Subtype.ext
  show beta1 * u * beta1⁻¹ = t * u * (beta1 * beta2)
  exact conj_of h45 pk_b1 pk_u (pk_mul h45 (pk_mul h45 pk_t pk_u) (pk_mul h45 pk_b1 pk_b2))
    (by decide +kernel)

private theorem conj_b1_a1a2 : b1C * (a1C * a2C) * b1C⁻¹ = tC * (a1C * a2C) := by
  apply Subtype.ext
  apply Subtype.ext
  show beta1 * (alpha1 * alpha2) * beta1⁻¹ = t * (alpha1 * alpha2)
  exact conj_of h45 pk_b1 (pk_mul h45 pk_a1 pk_a2) (pk_mul h45 pk_t (pk_mul h45 pk_a1 pk_a2))
    (by decide +kernel)

private theorem conj_b1_b1b2 : b1C * (b1C * b2C) * b1C⁻¹ = b1C * b2C := by
  apply Subtype.ext
  apply Subtype.ext
  show beta1 * (beta1 * beta2) * beta1⁻¹ = beta1 * beta2
  exact conj_of h45 pk_b1 (pk_mul h45 pk_b1 pk_b2) (pk_mul h45 pk_b1 pk_b2) (by decide +kernel)

private theorem conj_a2_t : a2C * tC * a2C⁻¹ = tC := by
  apply Subtype.ext
  apply Subtype.ext
  show alpha2 * t * alpha2⁻¹ = t
  exact conj_of h45 pk_a2 pk_t pk_t (by decide +kernel)

private theorem conj_a2_u : a2C * uC * a2C⁻¹ = tC * uC * (a1C * a2C) := by
  apply Subtype.ext
  apply Subtype.ext
  show alpha2 * u * alpha2⁻¹ = t * u * (alpha1 * alpha2)
  exact conj_of h45 pk_a2 pk_u (pk_mul h45 (pk_mul h45 pk_t pk_u) (pk_mul h45 pk_a1 pk_a2))
    (by decide +kernel)

private theorem conj_a2_a1a2 : a2C * (a1C * a2C) * a2C⁻¹ = a1C * a2C := by
  apply Subtype.ext
  apply Subtype.ext
  show alpha2 * (alpha1 * alpha2) * alpha2⁻¹ = alpha1 * alpha2
  exact conj_of h45 pk_a2 (pk_mul h45 pk_a1 pk_a2) (pk_mul h45 pk_a1 pk_a2) (by decide +kernel)

private theorem conj_a2_b1b2 : a2C * (b1C * b2C) * a2C⁻¹ = tC * (b1C * b2C) := by
  apply Subtype.ext
  apply Subtype.ext
  show alpha2 * (beta1 * beta2) * alpha2⁻¹ = t * (beta1 * beta2)
  exact conj_of h45 pk_a2 (pk_mul h45 pk_b1 pk_b2) (pk_mul h45 pk_t (pk_mul h45 pk_b1 pk_b2))
    (by decide +kernel)

private theorem conj_b2_t : b2C * tC * b2C⁻¹ = tC := by
  apply Subtype.ext
  apply Subtype.ext
  show beta2 * t * beta2⁻¹ = t
  exact conj_of h45 pk_b2 pk_t pk_t (by decide +kernel)

private theorem conj_b2_u : b2C * uC * b2C⁻¹ = tC * uC * (b1C * b2C) := by
  apply Subtype.ext
  apply Subtype.ext
  show beta2 * u * beta2⁻¹ = t * u * (beta1 * beta2)
  exact conj_of h45 pk_b2 pk_u (pk_mul h45 (pk_mul h45 pk_t pk_u) (pk_mul h45 pk_b1 pk_b2))
    (by decide +kernel)

private theorem conj_b2_a1a2 : b2C * (a1C * a2C) * b2C⁻¹ = tC * (a1C * a2C) := by
  apply Subtype.ext
  apply Subtype.ext
  show beta2 * (alpha1 * alpha2) * beta2⁻¹ = t * (alpha1 * alpha2)
  exact conj_of h45 pk_b2 (pk_mul h45 pk_a1 pk_a2) (pk_mul h45 pk_t (pk_mul h45 pk_a1 pk_a2))
    (by decide +kernel)

private theorem conj_b2_b1b2 : b2C * (b1C * b2C) * b2C⁻¹ = b1C * b2C := by
  apply Subtype.ext
  apply Subtype.ext
  show beta2 * (beta1 * beta2) * beta2⁻¹ = beta1 * beta2
  exact conj_of h45 pk_b2 (pk_mul h45 pk_b1 pk_b2) (pk_mul h45 pk_b1 pk_b2) (by decide +kernel)

private theorem mem_normalizer_S0_of_maps_generators {g : C0}
    (h : ∀ s ∈ ({tC, uC, a1C * a2C, b1C * b2C} : Set C0), g * s * g⁻¹ ∈ S0) :
    g ∈ Subgroup.normalizer (S0 : Set C0) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rw [S0, MonoidHom.map_closure, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    simpa [S0, MulAut.conj_apply] using h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_S0]

theorem pCore_C0_le_normalizer_S0 : CFSG.pCore 2 C0 ≤ Subgroup.normalizer (S0 : Set C0) := by
  rw [pCore_C0_eq, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · apply mem_normalizer_S0_of_maps_generators
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · rw [conj_a1_t]; exact tC_mem_S0
    · rw [conj_a1_u]
      exact S0.mul_mem (S0.mul_mem tC_mem_S0 uC_mem_S0) a1a2_mem_S0
    · rw [conj_a1_a1a2]; exact a1a2_mem_S0
    · rw [conj_a1_b1b2]
      exact S0.mul_mem tC_mem_S0 b1b2_mem_S0
  · apply mem_normalizer_S0_of_maps_generators
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · rw [conj_b1_t]; exact tC_mem_S0
    · rw [conj_b1_u]
      exact S0.mul_mem (S0.mul_mem tC_mem_S0 uC_mem_S0) b1b2_mem_S0
    · rw [conj_b1_a1a2]
      exact S0.mul_mem tC_mem_S0 a1a2_mem_S0
    · rw [conj_b1_b1b2]; exact b1b2_mem_S0
  · apply mem_normalizer_S0_of_maps_generators
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · rw [conj_a2_t]; exact tC_mem_S0
    · rw [conj_a2_u]
      exact S0.mul_mem (S0.mul_mem tC_mem_S0 uC_mem_S0) a1a2_mem_S0
    · rw [conj_a2_a1a2]; exact a1a2_mem_S0
    · rw [conj_a2_b1b2]
      exact S0.mul_mem tC_mem_S0 b1b2_mem_S0
  · apply mem_normalizer_S0_of_maps_generators
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · rw [conj_b2_t]; exact tC_mem_S0
    · rw [conj_b2_u]
      exact S0.mul_mem (S0.mul_mem tC_mem_S0 uC_mem_S0) b1b2_mem_S0
    · rw [conj_b2_a1a2]
      exact S0.mul_mem tC_mem_S0 a1a2_mem_S0
    · rw [conj_b2_b1b2]; exact b1b2_mem_S0

private theorem a1C_val : a1C.val.val = alpha1 := rfl

private theorem b1C_val : b1C.val.val = beta1 := rfl

private theorem uC_mul_tC_val : (uC * tC).val.val = u * t := rfl

private def conjCandidatesC0 : Finset C0 := {1, b1C, a1C, b1C * a1C}

private def conjPermCandidates : Finset (Equiv.Perm (Fin 45)) :=
  {1, beta1, alpha1, beta1 * alpha1}

private theorem exists_conjCandidateC0 {g0 : Equiv.Perm (Fin 45)}
    (hg : g0 ∈ conjPermCandidates) :
    ∃ gC ∈ conjCandidatesC0, gC.val.val = g0 := by
  simp only [conjPermCandidates, Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨1, by simp [conjCandidatesC0], rfl⟩
  · exact ⟨b1C, by simp [conjCandidatesC0], b1C_val⟩
  · exact ⟨a1C, by simp [conjCandidatesC0], a1C_val⟩
  · exact ⟨b1C * a1C, by simp [conjCandidatesC0], rfl⟩

private def outPermWord (p : Fin 4 → Fin 2) : Equiv.Perm (Fin 45) :=
  u * (t ^ (p 0 : ℕ) * (alpha1 * alpha2) ^ (p 2 : ℕ) * (beta1 * beta2) ^ (p 3 : ℕ))

private theorem s0PermWord_eq_outPermWord_of_p1 :
    ∀ p : Fin 4 → Fin 2, p 1 = 1 → s0PermWord p = outPermWord p := by
  intro p hp
  exact Pack.s0_eq_out p hp

private theorem s0PermWord_mem_q0Perm_of_p1_zero :
    ∀ p : Fin 4 → Fin 2, p 1 = 0 → s0PermWord p ∈ q0PermSet := by
  intro p hp
  obtain ⟨q, hq⟩ := Pack.s0_mem_q0 p hp
  exact Finset.mem_image.2 ⟨q, Finset.mem_univ _, hq⟩

private theorem cand_mem (i j : Fin 2) :
    beta1 ^ (i : ℕ) * alpha1 ^ (j : ℕ) ∈ conjPermCandidates := by
  fin_cases i <;> fin_cases j <;> simp [conjPermCandidates]

private theorem outPerm_conj_finite :
    ∀ p : Fin 4 → Fin 2, p 1 = 1 →
      (∃ g ∈ conjPermCandidates, g * outPermWord p * g⁻¹ = u) ∨
      (∃ g ∈ conjPermCandidates, g * outPermWord p * g⁻¹ = u * t) := by
  intro p _
  obtain ⟨i, j, h | h⟩ := Pack.out_conj p
  · exact Or.inl ⟨_, cand_mem i j, h⟩
  · exact Or.inr ⟨_, cand_mem i j, h⟩

private theorem conj_eq_of_perm_eq {g x y : C0}
    (h : g.val.val * x.val.val * (g.val.val)⁻¹ = y.val.val) : g * x * g⁻¹ = y := by
  apply Subtype.ext
  apply Subtype.ext
  simpa using h

private theorem exists_conj_involution_mem_P0 {y : C0} (hy : orderOf y = 2) :
    ∃ (g z : C0), z ∈ P0 ∧ z * z = 1 ∧ g * z * g⁻¹ = y := by
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    simpa [sq] using h
  have hcardC : Nat.card C0 = 576 := qp45_card_centralizer_t
  have hfac : (Nat.card C0).factorization 2 = 6 := by
    rw [hcardC]
    norm_num [Nat.factorization]
  have hcardP0 : Nat.card P0 = 2 ^ (Nat.card C0).factorization 2 := by
    rw [card_P0, hfac]
    norm_num
  let P0Sylow : Sylow 2 C0 := Sylow.ofCard P0 hcardP0
  let Y : Subgroup C0 := Subgroup.zpowers y
  have hY2 : IsPGroup 2 Y := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hy]
    norm_num
  obtain ⟨T, hYT⟩ := hY2.exists_le_sylow
  have hyT : y ∈ (T : Subgroup C0) := hYT (Subgroup.mem_zpowers y)
  have htrans : MulAction.IsPretransitive C0 (Sylow 2 C0) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := @MulAction.IsPretransitive.exists_smul_eq C0 (Sylow 2 C0) _ htrans
    P0Sylow T
  have hyG : y ∈ (g • P0Sylow : Sylow 2 C0) := by
    rw [hg]
    exact hyT
  change y ∈ (((g • P0Sylow : Sylow 2 C0) : Subgroup C0) : Set C0) at hyG
  rw [show (((g • P0Sylow : Sylow 2 C0) : Subgroup C0) : Set C0) =
      MulAut.conj g • ((P0Sylow : Sylow 2 C0) : Set C0) from Sylow.coe_smul] at hyG
  rw [Set.mem_smul_set] at hyG
  obtain ⟨z, hzP0, hzy0⟩ := hyG
  have hzP0' : z ∈ P0 := hzP0
  have hzy : g * z * g⁻¹ = y := by
    simpa [MulAut.conj_apply] using hzy0
  have hz2 : z * z = 1 := by
    have hz_eq : z = g⁻¹ * y * g := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = g⁻¹ * y * g := by rw [hzy]
    rw [hz_eq]
    calc (g⁻¹ * y * g) * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
      _ = 1 := by rw [hy2]; group
  exact ⟨g, z, hzP0', hz2, hzy⟩

private theorem isConj_uC_or_uC_mul_tC_of_mem_P0 {z : C0} (hzP0 : z ∈ P0)
    (hzQ : z ∉ CFSG.pCore 2 C0) (hz2 : z * z = 1) :
    IsConj z uC ∨ IsConj z (uC * tC) := by
  have hzS : z ∈ S0 :=
    mem_S0_of_involution_of_mem_P0_of_not_mem_pCore hzP0 hzQ hz2
  have hzS0 : z ∈ s0Set := by
    have h : z ∈ (s0Set : Set C0) := by
      rw [s0Set_eq_S0]
      exact hzS
    exact h
  simp only [s0Set, Finset.mem_image] at hzS0
  obtain ⟨p, -, hpz⟩ := hzS0
  have hp1 : p 1 = 1 := by
    by_cases h0 : p 1 = 0
    · exfalso
      have hmemPerm : s0PermWord p ∈ q0PermSet :=
        s0PermWord_mem_q0Perm_of_p1_zero p h0
      have hmemval : (s0Word p).val.val ∈ q0PermSet := by
        rwa [s0Word_val]
      have hmemSet : s0Word p ∈ q0Set := (mem_q0Set_iff _).mp hmemval
      have hmemQ : s0Word p ∈ CFSG.pCore 2 C0 := by
        change s0Word p ∈ (CFSG.pCore 2 C0 : Set C0)
        rw [← q0Set_eq]
        exact hmemSet
      rw [hpz] at hmemQ
      exact hzQ hmemQ
    · exact Fin.eq_one_of_ne_zero _ h0
  have hzval : z.val.val = outPermWord p := by
    rw [show z = s0Word p from hpz.symm, s0Word_val,
      s0PermWord_eq_outPermWord_of_p1 p hp1]
  rcases outPerm_conj_finite p hp1 with ⟨g0, hg0mem, hg0eq⟩ | ⟨g0, hg0mem, hg0eq⟩
  · obtain ⟨gC, -, hgCval⟩ := exists_conjCandidateC0 hg0mem
    have hconj : gC * z * gC⁻¹ = uC := by
      apply conj_eq_of_perm_eq
      rw [hgCval, hzval, hg0eq]
      exact uC_val.symm
    exact Or.inl (isConj_iff.mpr ⟨gC, hconj⟩)
  · obtain ⟨gC, -, hgCval⟩ := exists_conjCandidateC0 hg0mem
    have hconj : gC * z * gC⁻¹ = uC * tC := by
      apply conj_eq_of_perm_eq
      rw [hgCval, hzval, hg0eq]
      exact uC_mul_tC_val.symm
    exact Or.inr (isConj_iff.mpr ⟨gC, hconj⟩)

theorem isConj_uC_or_of_not_mem_pCore {y : C0} (hy : orderOf y = 2)
    (hyQ : y ∉ CFSG.pCore 2 C0) : IsConj y uC ∨ IsConj y (uC * tC) := by
  obtain ⟨g, z, hzP0, hz2, hzy⟩ := exists_conj_involution_mem_P0 hy
  have hzQ : z ∉ CFSG.pCore 2 C0 := by
    intro hzq
    apply hyQ
    rw [← hzy]
    exact (CFSG.pCore_normal (p := 2) (G := C0)).conj_mem z hzq g
  have hzyConj : IsConj z y := isConj_iff.mpr ⟨g, hzy⟩
  rcases isConj_uC_or_uC_mul_tC_of_mem_P0 hzP0 hzQ hz2 with h | h
  · exact Or.inl (hzyConj.symm.trans h)
  · exact Or.inr (hzyConj.symm.trans h)

private theorem expr_a1_u :
    (b1C * uC * b1C⁻¹) * (s1C * uC * s1C⁻¹) * (a1C * uC * a1C⁻¹) *
      (s2C * uC * s2C⁻¹) = a1C := by
  apply Subtype.ext
  apply Subtype.ext
  show (beta1 * u * beta1⁻¹) * (sigma1 * u * sigma1⁻¹) * (alpha1 * u * alpha1⁻¹) *
    (sigma2 * u * sigma2⁻¹) = alpha1
  exact eq_of_pk h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_conj h45 pk_b1 pk_b1i pk_u)
    (pk_conj h45 pk_s1 pk_s1i pk_u)) (pk_conj h45 pk_a1 pk_a1i pk_u))
    (pk_conj h45 pk_s2 pk_s2i pk_u)) pk_a1 (by decide +kernel)

private theorem expr_b1_u :
    (s1C * uC * s1C⁻¹) * (b1C * uC * b1C⁻¹) * (s2C * uC * s2C⁻¹) *
      (a1C * uC * a1C⁻¹) = b1C := by
  apply Subtype.ext
  apply Subtype.ext
  show (sigma1 * u * sigma1⁻¹) * (beta1 * u * beta1⁻¹) * (sigma2 * u * sigma2⁻¹) *
    (alpha1 * u * alpha1⁻¹) = beta1
  exact eq_of_pk h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_conj h45 pk_s1 pk_s1i pk_u)
    (pk_conj h45 pk_b1 pk_b1i pk_u)) (pk_conj h45 pk_s2 pk_s2i pk_u))
    (pk_conj h45 pk_a1 pk_a1i pk_u)) pk_b1 (by decide +kernel)

private theorem expr_a2_u :
    (b1C * uC * b1C⁻¹) * (s2C * uC * s2C⁻¹) * (a1C * uC * a1C⁻¹) *
      (s1C * uC * s1C⁻¹) = a2C := by
  apply Subtype.ext
  apply Subtype.ext
  show (beta1 * u * beta1⁻¹) * (sigma2 * u * sigma2⁻¹) * (alpha1 * u * alpha1⁻¹) *
    (sigma1 * u * sigma1⁻¹) = alpha2
  exact eq_of_pk h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_conj h45 pk_b1 pk_b1i pk_u)
    (pk_conj h45 pk_s2 pk_s2i pk_u)) (pk_conj h45 pk_a1 pk_a1i pk_u))
    (pk_conj h45 pk_s1 pk_s1i pk_u)) pk_a2 (by decide +kernel)

private theorem expr_b2_u :
    (s2C * uC * s2C⁻¹) * (b1C * uC * b1C⁻¹) * (s1C * uC * s1C⁻¹) *
      (a1C * uC * a1C⁻¹) = b2C := by
  apply Subtype.ext
  apply Subtype.ext
  show (sigma2 * u * sigma2⁻¹) * (beta1 * u * beta1⁻¹) * (sigma1 * u * sigma1⁻¹) *
    (alpha1 * u * alpha1⁻¹) = beta2
  exact eq_of_pk h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_conj h45 pk_s2 pk_s2i pk_u)
    (pk_conj h45 pk_b1 pk_b1i pk_u)) (pk_conj h45 pk_s1 pk_s1i pk_u))
    (pk_conj h45 pk_a1 pk_a1i pk_u)) pk_b2 (by decide +kernel)

private theorem expr_a1_ut :
    (b1C * (uC * tC) * b1C⁻¹) * (s1C * (uC * tC) * s1C⁻¹) *
      (a1C * (uC * tC) * a1C⁻¹) * (s2C * (uC * tC) * s2C⁻¹) = a1C := by
  apply Subtype.ext
  apply Subtype.ext
  show (beta1 * (u * t) * beta1⁻¹) * (sigma1 * (u * t) * sigma1⁻¹) *
    (alpha1 * (u * t) * alpha1⁻¹) * (sigma2 * (u * t) * sigma2⁻¹) = alpha1
  have hut := pk_mul h45 pk_u pk_t
  exact eq_of_pk h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_conj h45 pk_b1 pk_b1i hut)
    (pk_conj h45 pk_s1 pk_s1i hut)) (pk_conj h45 pk_a1 pk_a1i hut))
    (pk_conj h45 pk_s2 pk_s2i hut)) pk_a1 (by decide +kernel)

private theorem expr_b1_ut :
    (s1C * (uC * tC) * s1C⁻¹) * (b1C * (uC * tC) * b1C⁻¹) *
      (s2C * (uC * tC) * s2C⁻¹) * (a1C * (uC * tC) * a1C⁻¹) = b1C := by
  apply Subtype.ext
  apply Subtype.ext
  show (sigma1 * (u * t) * sigma1⁻¹) * (beta1 * (u * t) * beta1⁻¹) *
    (sigma2 * (u * t) * sigma2⁻¹) * (alpha1 * (u * t) * alpha1⁻¹) = beta1
  have hut := pk_mul h45 pk_u pk_t
  exact eq_of_pk h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_conj h45 pk_s1 pk_s1i hut)
    (pk_conj h45 pk_b1 pk_b1i hut)) (pk_conj h45 pk_s2 pk_s2i hut))
    (pk_conj h45 pk_a1 pk_a1i hut)) pk_b1 (by decide +kernel)

private theorem expr_a2_ut :
    (b1C * (uC * tC) * b1C⁻¹) * (s2C * (uC * tC) * s2C⁻¹) *
      (a1C * (uC * tC) * a1C⁻¹) * (s1C * (uC * tC) * s1C⁻¹) = a2C := by
  apply Subtype.ext
  apply Subtype.ext
  show (beta1 * (u * t) * beta1⁻¹) * (sigma2 * (u * t) * sigma2⁻¹) *
    (alpha1 * (u * t) * alpha1⁻¹) * (sigma1 * (u * t) * sigma1⁻¹) = alpha2
  have hut := pk_mul h45 pk_u pk_t
  exact eq_of_pk h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_conj h45 pk_b1 pk_b1i hut)
    (pk_conj h45 pk_s2 pk_s2i hut)) (pk_conj h45 pk_a1 pk_a1i hut))
    (pk_conj h45 pk_s1 pk_s1i hut)) pk_a2 (by decide +kernel)

private theorem expr_b2_ut :
    (s2C * (uC * tC) * s2C⁻¹) * (b1C * (uC * tC) * b1C⁻¹) *
      (s1C * (uC * tC) * s1C⁻¹) * (a1C * (uC * tC) * a1C⁻¹) = b2C := by
  apply Subtype.ext
  apply Subtype.ext
  show (sigma2 * (u * t) * sigma2⁻¹) * (beta1 * (u * t) * beta1⁻¹) *
    (sigma1 * (u * t) * sigma1⁻¹) * (alpha1 * (u * t) * alpha1⁻¹) = beta2
  have hut := pk_mul h45 pk_u pk_t
  exact eq_of_pk h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_conj h45 pk_s2 pk_s2i hut)
    (pk_conj h45 pk_b1 pk_b1i hut)) (pk_conj h45 pk_s1 pk_s1i hut))
    (pk_conj h45 pk_a1 pk_a1i hut)) pk_b2 (by decide +kernel)

private theorem tC_sq : tC * tC = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  show t * t = 1
  exact t_sq

private theorem Q0_le_of_mem_u {K : Subgroup C0} [K.Normal] {b : C0} (hb : b ∈ K)
    (hb' : b = uC) : Subgroup.closure ({a1C, b1C, a2C, b2C} : Set C0) ≤ K := by
  subst b
  let A : C0 := b1C * uC * b1C⁻¹
  let B : C0 := s1C * uC * s1C⁻¹
  let C : C0 := a1C * uC * a1C⁻¹
  let D : C0 := s2C * uC * s2C⁻¹
  have hA : A ∈ K := (inferInstance : K.Normal).conj_mem uC hb b1C
  have hB : B ∈ K := (inferInstance : K.Normal).conj_mem uC hb s1C
  have hC : C ∈ K := (inferInstance : K.Normal).conj_mem uC hb a1C
  have hD : D ∈ K := (inferInstance : K.Normal).conj_mem uC hb s2C
  have e1 : A * B * C * D = a1C := expr_a1_u
  have e2 : B * A * D * C = b1C := expr_b1_u
  have e3 : A * D * C * B = a2C := expr_a2_u
  have e4 : D * A * B * C = b2C := expr_b2_u
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact e1 ▸ K.mul_mem (K.mul_mem (K.mul_mem hA hB) hC) hD
  · exact e2 ▸ K.mul_mem (K.mul_mem (K.mul_mem hB hA) hD) hC
  · exact e3 ▸ K.mul_mem (K.mul_mem (K.mul_mem hA hD) hC) hB
  · exact e4 ▸ K.mul_mem (K.mul_mem (K.mul_mem hD hA) hB) hC

private theorem Q0_le_of_mem_ut {K : Subgroup C0} [K.Normal] {b : C0} (hb : b ∈ K)
    (hb' : b = uC * tC) : Subgroup.closure ({a1C, b1C, a2C, b2C} : Set C0) ≤ K := by
  subst b
  let A : C0 := b1C * (uC * tC) * b1C⁻¹
  let B : C0 := s1C * (uC * tC) * s1C⁻¹
  let C : C0 := a1C * (uC * tC) * a1C⁻¹
  let D : C0 := s2C * (uC * tC) * s2C⁻¹
  have hA : A ∈ K := (inferInstance : K.Normal).conj_mem (uC * tC) hb b1C
  have hB : B ∈ K := (inferInstance : K.Normal).conj_mem (uC * tC) hb s1C
  have hC : C ∈ K := (inferInstance : K.Normal).conj_mem (uC * tC) hb a1C
  have hD : D ∈ K := (inferInstance : K.Normal).conj_mem (uC * tC) hb s2C
  have e1 : A * B * C * D = a1C := expr_a1_ut
  have e2 : B * A * D * C = b1C := expr_b1_ut
  have e3 : A * D * C * B = a2C := expr_a2_ut
  have e4 : D * A * B * C = b2C := expr_b2_ut
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact e1 ▸ K.mul_mem (K.mul_mem (K.mul_mem hA hB) hC) hD
  · exact e2 ▸ K.mul_mem (K.mul_mem (K.mul_mem hB hA) hD) hC
  · exact e3 ▸ K.mul_mem (K.mul_mem (K.mul_mem hA hD) hC) hB
  · exact e4 ▸ K.mul_mem (K.mul_mem (K.mul_mem hD hA) hB) hC

theorem P0_le_of_uC_mem {K : Subgroup C0} [K.Normal] (hu : uC ∈ K) : P0 ≤ K := by
  have hQ := Q0_le_of_mem_u hu rfl
  rw [P0, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hu
  · exact hQ (Subgroup.subset_closure (by simp))
  · exact hQ (Subgroup.subset_closure (by simp))
  · exact hQ (Subgroup.subset_closure (by simp))
  · exact hQ (Subgroup.subset_closure (by simp))

theorem P0_le_of_uC_mul_tC_mem {K : Subgroup C0} [K.Normal] (hu : uC * tC ∈ K) : P0 ≤ K := by
  have hQ := Q0_le_of_mem_ut hu rfl
  have ha1 : a1C ∈ K := hQ (Subgroup.subset_closure (by simp))
  have htK : tC ∈ K := by
    rw [show tC = a1C * a1C from by
      apply Subtype.ext; apply Subtype.ext; show t = alpha1 * alpha1
      exact alpha1_sq.symm]
    exact K.mul_mem ha1 ha1
  have huK : uC ∈ K := by
    have h := K.mul_mem hu htK
    rwa [show (uC * tC) * tC = uC from by rw [mul_assoc, tC_sq, mul_one]] at h
  rw [P0, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact huK
  · exact hQ (Subgroup.subset_closure (by simp))
  · exact hQ (Subgroup.subset_closure (by simp))
  · exact hQ (Subgroup.subset_closure (by simp))
  · exact hQ (Subgroup.subset_closure (by simp))

theorem mem_pCore_C0_iff (x : C0) :
    x ∈ CFSG.pCore 2 C0 ↔
      ∃ p : Fin 5 → Fin 2,
        x = a1C ^ (p 0 : ℕ) * b1C ^ (p 1 : ℕ) * a2C ^ (p 2 : ℕ) * b2C ^ (p 3 : ℕ) *
          tC ^ (p 4 : ℕ) := by
  change x ∈ (CFSG.pCore 2 C0 : Set C0) ↔ _
  rw [← q0Set_eq, q0Set, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨p, -, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, Finset.mem_univ p, rfl⟩

theorem mem_S0_iff (x : C0) :
    x ∈ S0 ↔
      ∃ p : Fin 4 → Fin 2,
        x = tC ^ (p 0 : ℕ) * uC ^ (p 1 : ℕ) * (a1C * a2C) ^ (p 2 : ℕ) *
          (b1C * b2C) ^ (p 3 : ℕ) := by
  change x ∈ (S0 : Set C0) ↔ _
  rw [← s0Set_eq_S0, s0Set, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨p, -, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, Finset.mem_univ p, rfl⟩

end CFSG.Literature.Janko67
