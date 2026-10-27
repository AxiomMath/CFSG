module

public import CFSG.GH74.Uniqueness.SU.SU9Fib
public import CFSG.GH74.ThompsonOrderFormula

public section

namespace CFSG.GH74.Uniqueness.SU.SU9

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.Uniqueness.SU.SU7
  CFSG CFSG.ShultStronglyClosedTI.InvolutionCounting

namespace L197

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

omit [Finite G] in
theorem card_class [Fintype G] [DecidableEq G] (g : G) [DecidablePred (IsConj g)] :
    Nat.card (centralizer ({g} : Set G)) * (Finset.univ.filter (fun y => IsConj g y)).card =
      Nat.card G := by
  have h := card_centralizer_mul_card_conjugatesOf g
  have h2 : Nat.card (conjugatesOf g) = (Finset.univ.filter (fun y => IsConj g y)).card := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    congr 1
    ext y
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩
  rw [h2] at h
  exact h

omit [Finite G] in
theorem card_comm_conj [Fintype G] [DecidableEq G] (X : Finset G)
    (hX : ∀ g d, d ∈ X → g * d * g⁻¹ ∈ X) (y₀ g : G) :
    (X.filter (fun d => d * (g * y₀ * g⁻¹) = (g * y₀ * g⁻¹) * d)).card =
      (X.filter (fun d => d * y₀ = y₀ * d)).card := by
  refine Finset.card_nbij' (fun d => g⁻¹ * d * g) (fun d => g * d * g⁻¹) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter] at hd ⊢
    refine ⟨by simpa using hX g⁻¹ d hd.1, ?_⟩
    have h := hd.2
    calc g⁻¹ * d * g * y₀ = g⁻¹ * (d * (g * y₀ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y₀ * g⁻¹) * d) * g := by rw [h]
      _ = y₀ * (g⁻¹ * d * g) := by group
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter] at hd ⊢
    refine ⟨hX g d hd.1, ?_⟩
    have h := hd.2
    calc g * d * g⁻¹ * (g * y₀ * g⁻¹) = g * (d * y₀) * g⁻¹ := by group
      _ = g * (y₀ * d) * g⁻¹ := by rw [h]
      _ = (g * y₀ * g⁻¹) * (g * d * g⁻¹) := by group
  · intro d _
    group
  · intro d _
    group

theorem card_W0 (h191 : Lemma191Stmt) (hc : Ctx19 S U M V x z A B R) {a : G}
    (hd : Cnt.Data S U z A B a) (hCz : Nat.card ↥(centralizer ({z} : Set G)) = 1920)
    (hCa : Nat.card ↥(centralizer ({a} : Set G)) = 48) :
    Set.ncard {w : G | IsConj a w ∧ w * z = z * w} = 120 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let ZF : Finset G := Finset.univ.filter (fun y => IsConj z y)
  let AF : Finset G := Finset.univ.filter (fun y => IsConj a y)
  have hZ : Nat.card ↥(centralizer ({z} : Set G)) * ZF.card = Nat.card G := card_class z
  have hA : Nat.card ↥(centralizer ({a} : Set G)) * AF.card = Nat.card G := card_class a
  have hZinv : ∀ g d, d ∈ ZF → g * d * g⁻¹ ∈ ZF := by
    intro g d hd'
    have : IsConj z d := (Finset.mem_filter.1 hd').2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this.trans (isConj_iff.2 ⟨g, rfl⟩)⟩
  have hAinv : ∀ g d, d ∈ AF → g * d * g⁻¹ ∈ AF := by
    intro g d hd'
    have : IsConj a d := (Finset.mem_filter.1 hd').2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this.trans (isConj_iff.2 ⟨g, rfl⟩)⟩
  set nW := (AF.filter (fun y' => y' * z = z * y')).card with hnW
  have hL : ∀ y ∈ ZF, (AF.filter (fun y' => y * y' = y' * y)).card = nW := by
    intro y hy
    obtain ⟨g, rfl⟩ := isConj_iff.1 (Finset.mem_filter.1 hy).2
    rw [hnW, ← card_comm_conj AF hAinv z g]
    congr 1
    apply Finset.filter_congr
    intro d _
    exact eq_comm
  have hR : ∀ y' ∈ AF, (ZF.filter (fun y => y * y' = y' * y)).card = 3 := by
    intro y' hy'
    obtain ⟨g, rfl⟩ := isConj_iff.1 (Finset.mem_filter.1 hy').2
    have h1 := card_comm_conj ZF hZinv a g
    rw [h1]
    have h2 : ((ZF.filter (fun y => y * a = a * y) : Finset G) : Set G) = (U : Set G) \ {1} := by
      rw [← Cnt.zconj_comm_a_eq h191 hc hd]
      ext y
      simp [ZF]
    have h3 := Set.ncard_coe_finset (ZF.filter (fun y => y * a = a * y))
    rw [h2, Set.ncard_sdiff_singleton_of_mem U.one_mem, ← Nat.card_coe_set_eq] at h3
    have : Nat.card (U : Set G) = 4 := Cfg.card_U hc
    omega
  have hsum : ∑ y ∈ ZF, (AF.filter (fun y' => y * y' = y' * y)).card =
      ∑ y' ∈ AF, (ZF.filter (fun y => y * y' = y' * y)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  have hN : 0 < Nat.card G := Nat.card_pos
  have hnW120 : nW = 120 := by
    have h1 : Nat.card G * nW = Nat.card G * 120 := by
      calc Nat.card G * nW = (1920 * ZF.card) * nW := by rw [← hZ, hCz]
        _ = 1920 * (ZF.card * nW) := by ring
        _ = 1920 * (AF.card * 3) := by rw [hsum]
        _ = (48 * AF.card) * 120 := by ring
        _ = Nat.card G * 120 := by rw [← hA, hCa]
    exact Nat.eq_of_mul_eq_mul_left hN h1
  have hset : {w : G | IsConj a w ∧ w * z = z * w} = ((AF.filter (fun y' => y' * z = z * y') :
      Finset G) : Set G) := by
    ext w
    rw [Finset.mem_coe, Finset.mem_filter]
    show (IsConj a w ∧ w * z = z * w) ↔ (w ∈ AF ∧ w * z = z * w)
    simp only [AF, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hset, Set.ncard_coe_finset]
  exact hnW120

theorem r_z_eq (h191 : Lemma191Stmt) (h192 : Lemma192Stmt) (h194 : Lemma194Stmt)
    (hc : Ctx19 S U M V x z A B R) {a : G} (hd : Cnt.Data S U z A B a)
    (hCz : Nat.card ↥(centralizer ({z} : Set G)) = 1920)
    (hCa : Nat.card ↥(centralizer ({a} : Set G)) = 48) : thompsonPairCount z a z = 960 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have haa : a * a = 1 := Cfg.A_sq hc a hd.ha
  have hzz : z * z = 1 := Cfg.z_sq hc
  let AF : Finset G := Finset.univ.filter (fun y => IsConj a y)
  let W0F : Finset G := AF.filter (fun w => w * z = z * w)
  let PF : Finset (G × G) :=
    Finset.univ.filter (fun p => IsConj z p.1 ∧ IsConj a p.2 ∧ z ∈ zpowers (p.1 * p.2))
  have hPF : thompsonPairCount z a z = PF.card := by
    unfold thompsonPairCount
    rw [Nat.card_coe_set_eq]
    have : thompsonPairs z a z = (PF : Set (G × G)) := by
      ext p
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩
    rw [this, Set.ncard_coe_finset]
  have hmap : ∀ p ∈ PF, p.2 ∈ W0F := by
    intro p hp
    have hp' : p ∈ thompsonPairs z a z := (Finset.mem_filter.1 hp).2
    have h2 := (mem_centralizer_of_mem_thompsonPairs hzz haa hzz hp').2
    exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hp'.2.1⟩,
      mem_centralizer_singleton_iff.1 h2⟩
  rw [hPF, Finset.card_eq_sum_card_fiberwise hmap]
  have hfib : ∀ w ∈ W0F, (PF.filter (fun p => p.2 = w)).card = 8 := by
    intro w hw
    have hwC : w ∈ centralizer ({z} : Set G) :=
      mem_centralizer_singleton_iff.2 (Finset.mem_filter.1 hw).2
    have haw : IsConj a w := (Finset.mem_filter.1 (Finset.mem_filter.1 hw).1).2
    have h8 := Cnt.card_fiber h191 h192 h194 hc hd hwC haw
    rw [← h8]
    have hset : {v : G | IsConj z v ∧ z ∈ zpowers (v * w)} =
        ((Finset.univ.filter (fun v => IsConj z v ∧ z ∈ zpowers (v * w)) : Finset G) : Set G) := by
      ext v
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩
    rw [hset, Set.ncard_coe_finset]
    refine Finset.card_nbij' (fun p => p.1) (fun v => (v, w)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, PF] at hp ⊢
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hp
      refine ⟨h1, ?_⟩
      rw [← h4]; exact h3
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, PF] at hv ⊢
      exact ⟨⟨hv.1, haw, hv.2⟩, trivial⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, PF] at hp
      exact Prod.ext rfl hp.2.symm
    · intro v _
      rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  have hW0 : Set.ncard {w : G | IsConj a w ∧ w * z = z * w} = 120 :=
    card_W0 h191 hc hd hCz hCa
  have hW0F : W0F.card = 120 := by
    rw [← hW0, ← Set.ncard_coe_finset]
    congr 1
    ext w
    rw [Finset.mem_coe, Finset.mem_filter]
    show (w ∈ AF ∧ w * z = z * w) ↔ (IsConj a w ∧ w * z = z * w)
    simp only [AF, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hW0F]

theorem exists_mem_A_not_U (hc : Ctx19 S U M V x z A B R) : ∃ a ∈ A, a ∉ U := by
  by_contra h
  push Not at h
  have hle : A ≤ U := fun a ha => h a ha
  have := Subgroup.card_le_of_le hle
  rw [Cfg.card_A hc, Cfg.card_U hc] at this
  omega

end L197

theorem lemma197 (h191 : Lemma191Stmt) (h192 : Lemma192Stmt) (h194 : Lemma194Stmt)
    (h196 : Lemma196Stmt) : Lemma197Stmt := by
  intro G _ _ S U M V x z A B R hc
  obtain ⟨a, ha, haU⟩ := L197.exists_mem_A_not_U hc
  have hd := Cnt.Data.of_h196 h196 hc ha haU
  obtain ⟨-, hCz⟩ := Cnt.cent_z_facts h192 h194 hc
  have hCa : Nat.card ↥(centralizer ({a} : Set G)) = 48 := by
    obtain ⟨e⟩ := hd.cent
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod]
    have h4 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]; simp
    rw [h4, h2]
  have ha1 : a ≠ 1 := fun h => haU (h ▸ U.one_mem)
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact Cfg.A_sq hc a ha) ha1
  have hform := (thompson_two_involution_class_order_formula (G := G) (t := z) (u := a)
    hc.conf.hz ha2 hd.not_conj hd.cover).1
  rw [Cnt.r_a_eq h191 hc hd, L197.r_z_eq h191 h192 h194 hc hd hCz hCa, hCa, hCz] at hform
  rw [hform]
  norm_num

end CFSG.GH74.Uniqueness.SU.SU9
