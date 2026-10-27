module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmMinusFrame
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
  CFSG.LocalAnalysis.GLTheoremA.S172B.Rank CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

private theorem frame_rot_fix_a_zero {a b : Fin 5 → V} (hp : ∀ i, MinusPair Q (a i) (b i))
    (hperp : ∀ i j, i ≠ j → PairPerp Q (a i, b i) (a j, b j))
    (i : Fin 5) (hi : i ≠ 0) :
    ((rotOrthDerived Q (hp i) : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) (a 0) = a 0 := by
  simpa [rotOrthDerived] using (rot_fixes_of_pairPerp (hp i) (hperp i 0 hi)).1

theorem exists_twoLocal_of_frame (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 5)
    {l : List (V × V)} (hl : IsFrame Q l) (hlen : l.length = 5) :
    ∃ E : Subgroup ↥(orthDerived Q), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ TwoLocal E := by
  obtain ⟨a, b, hp, hperp, -⟩ := exists_family_of_isFrame hl hlen
  let r : Fin 5 → ↥(orthDerived Q) := fun i => rotOrthDerived Q (hp i)
  let T : Subgroup ↥(orthDerived Q) := Subgroup.closure (Set.range r)
  have hT := isElemAbelian_card_closure_rotOrthDerived (Q := Q) (a := a) (b := b) hp hperp
  have hTel : IsElemAbelian 3 T := hT.1
  have hTcard : Nat.card T = 3 ^ 5 := hT.2
  let r3 : Fin 3 → ↥(orthDerived Q) := fun i => r (Fin.succ (Fin.succ i))
  let T3 : Subgroup ↥(orthDerived Q) := Subgroup.closure (Set.range r3)
  have hp3 : ∀ i : Fin 3, MinusPair Q (a (Fin.succ (Fin.succ i))) (b (Fin.succ (Fin.succ i))) :=
    fun i => hp _
  have hperp3 : ∀ i j : Fin 3, i ≠ j →
      PairPerp Q (a (Fin.succ (Fin.succ i)), b (Fin.succ (Fin.succ i)))
        (a (Fin.succ (Fin.succ j)), b (Fin.succ (Fin.succ j))) := by
    intro i j hij
    refine hperp _ _ ?_
    intro h
    exact hij (Fin.succ_injective _ (Fin.succ_injective _ h))
  have hT3 := isElemAbelian_card_closure_rotOrthDerived
    (Q := Q) (a := fun i : Fin 3 => a (Fin.succ (Fin.succ i)))
    (b := fun i : Fin 3 => b (Fin.succ (Fin.succ i))) hp3 hperp3
  have hT3card : Nat.card T3 = 3 ^ 3 := by
    simpa [T3, r3, r] using hT3.2
  let g : ↥(orthDerived Q) := r 0 * r 1
  let E : Subgroup ↥(orthDerived Q) := Subgroup.closure (Set.range r3 ∪ {g})
  have h0T : r 0 ∈ T := Subgroup.subset_closure (Set.mem_range_self (0 : Fin 5))
  have h1T : r 1 ∈ T := Subgroup.subset_closure (Set.mem_range_self (1 : Fin 5))
  have hgT : g ∈ T := T.mul_mem h0T h1T
  have hgpow : g ^ 3 = 1 := hTel.2 g hgT
  have hg_a0 : ((g : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) (a 0) = b 0 := by
    dsimp only [g, r]
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
    have h0 : (rotOrthDerived Q (hp 0) : V ≃ₗ[ZMod 2] V) = rot Q (a 0) (b 0) := rfl
    have h1 : (rotOrthDerived Q (hp 1) : V ≃ₗ[ZMod 2] V) = rot Q (a 1) (b 1) := rfl
    rw [h0, h1]
    have hfix : rot Q (a 1) (b 1) (a 0) = a 0 :=
      (rot_fixes_of_pairPerp (hp 1) (hperp 1 0 (by decide))).1
    rw [hfix, rot_apply_left (hp 0)]
  have hT3_fix_a0 : ∀ x ∈ T3, ((x : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) (a 0) = a 0 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        dsimp only [r3]
        have hne : Fin.succ (Fin.succ i) ≠ (0 : Fin 5) := by
          intro h
          have hval := congrArg Fin.val h
          simp at hval
        simpa [r] using frame_rot_fix_a_zero (Q := Q) hp hperp (Fin.succ (Fin.succ i)) hne
    | one => rfl
    | mul x y hx hy ihx ihy =>
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply, ihy, ihx]
    | inv x hx ih =>
        have h1 : ((x : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V).symm (a 0) = a 0 :=
          (congrArg ((x : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V).symm ih.symm).trans
            (((x : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V).symm_apply_apply (a 0))
        rw [Subgroup.coe_inv]
        exact h1
  have hg_not_mem : g ∉ T3 := by
    intro hg
    have hfix := hT3_fix_a0 g hg
    rw [hg_a0] at hfix
    exact (hp 0).ne hfix.symm
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1] at hg_a0
    exact (hp 0).ne (by simpa using hg_a0)
  have hgord : orderOf g = 3 := orderOf_eq_prime hgpow hg1
  have hgcard : Nat.card (Subgroup.zpowers g) = 3 := by
    rw [Nat.card_zpowers, hgord]
  have hT3leT : T3 ≤ T := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨i, rfl⟩
    exact Subgroup.subset_closure (Set.mem_range_self (Fin.succ (Fin.succ i)))
  have hgleT : Subgroup.zpowers g ≤ T := Subgroup.zpowers_le.2 hgT
  have hcomm : ∀ x ∈ T3, ∀ y ∈ Subgroup.zpowers g, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val
      (hTel.1.is_comm.comm ⟨x, hT3leT hx⟩ ⟨y, hgleT hy⟩)
  have hInfBot : T3 ⊓ Subgroup.zpowers g = ⊥ := by
    have hle : (T3 ⊓ Subgroup.zpowers g : Subgroup ↥(orthDerived Q)) ≤
        Subgroup.zpowers g := inf_le_right
    have hdvd : Nat.card ↥(T3 ⊓ Subgroup.zpowers g) ∣ 3 := by
      have h := Subgroup.card_subgroup_dvd_card
        ((T3 ⊓ Subgroup.zpowers g).subgroupOf (Subgroup.zpowers g))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hgcard] at h
    by_contra hne
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact hne (Subgroup.eq_bot_of_card_eq _ h1)
    · have heq : T3 ⊓ Subgroup.zpowers g = Subgroup.zpowers g :=
        Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [h3, hgcard]))
      apply hg_not_mem
      have hmem : g ∈ T3 ⊓ Subgroup.zpowers g := by
        rw [heq]
        exact Subgroup.mem_zpowers_iff.2 ⟨1, by simp⟩
      exact (Subgroup.mem_inf.1 hmem).1
  have hEleT : E ≤ T := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | hx)
    · obtain ⟨i, rfl⟩ := hx
      exact Subgroup.subset_closure (Set.mem_range_self (Fin.succ (Fin.succ i)))
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hgT
  have hEel : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.mono hTel hEleT
  have hEeq : E = T3 ⊔ Subgroup.zpowers g := by
    dsimp only [E, T3]
    rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute T3
    (Subgroup.zpowers g) hcomm).1
  rw [hInfBot, Subgroup.card_bot, mul_one, hT3card, hgcard] at hcard
  have hEcard : Nat.card E = 3 ^ 4 := by
    rw [hEeq, hcard]
    norm_num
  let u : V := a 0 + a 1
  let v : V := b 0 + b 1
  have h01 : PairPerp Q (a 0, b 0) (a 1, b 1) := hperp 0 1 (by decide)
  have huQ : Q u = 0 := by
    dsimp only [u]
    rw [map_add_polar, (hp 0).qa, (hp 1).qa, h01.1]
    decide
  have hvQ : Q v = 0 := by
    dsimp only [v]
    rw [map_add_polar, (hp 0).qb, (hp 1).qb, h01.2.2.2]
    decide
  have huv : polar Q u v = 0 := by
    have h10 : polar Q (a 1) (b 0) = 0 := by rw [polar_comm]; exact h01.2.2.1
    dsimp only [u, v]
    simp only [polar_add_left, polar_add_right, (hp 0).ab, h01.2.1, h10, (hp 1).ab]
    decide
  let s : V ≃ₗ[ZMod 2] V := eichler Q u v
  have hss : s * s = 1 := by
    dsimp only [s]
    rw [eichler_mul huv huv, vec_add_self, eichler_zero_right]
  have hsa0 : s (a 0) = a 1 := by
    dsimp only [s]
    rw [eichler_apply huQ huv]
    have h1 : polar Q (a 0) u = 0 := by
      dsimp only [u]
      rw [polar_add_right, polar_self_zero, h01.1, add_zero]
    have h2 : polar Q (a 0) v = 1 := by
      dsimp only [v]
      rw [polar_add_right, (hp 0).ab, h01.2.1, add_zero]
    simp only [h1, h2, hvQ, zero_mul, add_zero, zero_smul, zero_add, one_smul]
    rw [sub_eq_add_neg, ZModModule.neg_eq_self]
    dsimp only [u]
    linear_combination (norm := module) (vec_add_self (a 0))
  have ha01 : a 0 ≠ a 1 := by
    intro h
    have h1 : polar Q (a 0) (b 1) = 1 := by rw [h, (hp 1).ab]
    rw [h01.2.1] at h1
    exact zero_ne_one h1
  have hs_ne_one : s ≠ 1 := by
    intro h
    apply ha01
    have h1 := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (a 0)) h
    rw [hsa0] at h1
    simpa using h1.symm
  have hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    eichler_mem_orthogonalGroup Q u v
  have hsΩ : s ∈ orthDerived Q :=
    rootGroup_le_orthDerived hQ (by rw [hdim]; norm_num) huQ (eichler_mem_rootGroup huv)
  let S : ↥(orthDerived Q) := ⟨s, hsΩ⟩
  have hSord : orderOf S = 2 :=
    orderOf_eq_prime (Subtype.ext (by dsimp only [S]; rw [pow_two]; exact hss))
      (fun h => hs_ne_one (congrArg Subtype.val h))
  let P : Subgroup ↥(orthDerived Q) := Subgroup.zpowers S
  have hPcard : Nat.card P = 2 := by rw [Nat.card_zpowers, hSord]
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num)
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    omega
  have hrot_fix_u : ∀ i : Fin 3,
      ((r3 i : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) u = u := by
    intro i
    dsimp only [r3, r]
    have hk0 : Fin.succ (Fin.succ i) ≠ (0 : Fin 5) := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
    have hk1 : Fin.succ (Fin.succ i) ≠ (1 : Fin 5) := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
    have hfix0 : ((rotOrthDerived Q (hp (Fin.succ (Fin.succ i)))) : V ≃ₗ[ZMod 2] V)
        (a 0) = a 0 :=
      frame_rot_fix_a_zero (Q := Q) hp hperp _ hk0
    have hfix1 : ((rotOrthDerived Q (hp (Fin.succ (Fin.succ i)))) : V ≃ₗ[ZMod 2] V)
        (a 1) = a 1 :=
      (rot_fixes_of_pairPerp (hp (Fin.succ (Fin.succ i)))
        (hperp (Fin.succ (Fin.succ i)) 1 hk1)).1
    dsimp only [u]
    rw [map_add, hfix0, hfix1]
  have hrot_fix_v : ∀ i : Fin 3,
      ((r3 i : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v = v := by
    intro i
    dsimp only [r3, r]
    have hk0 : Fin.succ (Fin.succ i) ≠ (0 : Fin 5) := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
    have hk1 : Fin.succ (Fin.succ i) ≠ (1 : Fin 5) := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
    have hfix0 : ((rotOrthDerived Q (hp (Fin.succ (Fin.succ i)))) : V ≃ₗ[ZMod 2] V)
        (b 0) = b 0 :=
      (rot_fixes_of_pairPerp (hp (Fin.succ (Fin.succ i)))
        (hperp (Fin.succ (Fin.succ i)) 0 hk0)).2
    have hfix1 : ((rotOrthDerived Q (hp (Fin.succ (Fin.succ i)))) : V ≃ₗ[ZMod 2] V)
        (b 1) = b 1 :=
      (rot_fixes_of_pairPerp (hp (Fin.succ (Fin.succ i)))
        (hperp (Fin.succ (Fin.succ i)) 1 hk1)).2
    dsimp only [v]
    rw [map_add, hfix0, hfix1]
  have hg_u : ((g : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) u = v := by
    dsimp only [g, r, u, v]
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
    have h0 : (rotOrthDerived Q (hp 0) : V ≃ₗ[ZMod 2] V) = rot Q (a 0) (b 0) := rfl
    have h1 : (rotOrthDerived Q (hp 1) : V ≃ₗ[ZMod 2] V) = rot Q (a 1) (b 1) := rfl
    rw [h0, h1]
    have hfix0 : rot Q (a 1) (b 1) (a 0) = a 0 :=
      (rot_fixes_of_pairPerp (hp 1) (hperp 1 0 (by decide))).1
    have hmov1 : rot Q (a 1) (b 1) (a 1) = b 1 := rot_apply_left (hp 1)
    have hmov0 : rot Q (a 0) (b 0) (a 0) = b 0 := rot_apply_left (hp 0)
    have hfix1 : rot Q (a 0) (b 0) (b 1) = b 1 :=
      (rot_fixes_of_pairPerp (hp 0) (hperp 0 1 (by decide))).2
    rw [map_add, hfix0, hmov1, map_add, hmov0, hfix1]
  have hg_v : ((g : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v = u + v := by
    dsimp only [g, r, u, v]
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
    have h0 : (rotOrthDerived Q (hp 0) : V ≃ₗ[ZMod 2] V) = rot Q (a 0) (b 0) := rfl
    have h1 : (rotOrthDerived Q (hp 1) : V ≃ₗ[ZMod 2] V) = rot Q (a 1) (b 1) := rfl
    rw [h0, h1]
    have hfix0 : rot Q (a 1) (b 1) (b 0) = b 0 :=
      (rot_fixes_of_pairPerp (hp 1) (hperp 1 0 (by decide))).2
    have hmov1 : rot Q (a 1) (b 1) (b 1) = a 1 + b 1 := rot_apply_right (hp 1)
    have hmov0 : rot Q (a 0) (b 0) (b 0) = a 0 + b 0 := rot_apply_right (hp 0)
    have hfix1 : rot Q (a 0) (b 0) (a 1 + b 1) = a 1 + b 1 := by
      rw [map_add]
      exact congrArg₂ (· + ·) (rot_fixes_of_pairPerp (hp 0) (hperp 0 1 (by decide))).1
        (rot_fixes_of_pairPerp (hp 0) (hperp 0 1 (by decide))).2
    rw [map_add, hfix0, hmov1, map_add, hmov0, hfix1]
    module
  have hrot_cent : ∀ i : Fin 3, r3 i ∈ Subgroup.centralizer ({S} : Set ↥(orthDerived Q)) := by
    intro i
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hO : ((r3 i : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ∈
        TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup (r3 i).2
    have hconj := eichler_conj hO u v
    rw [hrot_fix_u i, hrot_fix_v i] at hconj
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hg_cent : g ∈ Subgroup.centralizer ({S} : Set ↥(orthDerived Q)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hO : ((g : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ∈
        TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup g.2
    have hconj := eichler_conj hO u v
    rw [hg_u, hg_v, eichler_swap_add huQ hvQ huv] at hconj
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hEcent : E ≤ Subgroup.centralizer ({S} : Set ↥(orthDerived Q)) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | hx)
    · obtain ⟨i, rfl⟩ := hx
      exact hrot_cent i
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hg_cent
  have hcentP : Subgroup.centralizer ({S} : Set ↥(orthDerived Q)) ≤
      Subgroup.centralizer (P : Set ↥(orthDerived Q)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute S x := hx S (Set.mem_singleton S)
    exact (hc.zpow_left k).eq
  have hEnorm : E ≤ Subgroup.normalizer (P : Set ↥(orthDerived Q)) :=
    hEcent.trans (hcentP.trans (Subgroup.centralizer_le_normalizer (P : Set ↥(orthDerived Q))))
  exact ⟨E, hEel, hEcard, ⟨P, hP2, hPne, hEnorm⟩⟩

theorem card_eq_three_pow_four_of_smallModel_minus_five
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank (ZMod 2) V = 2 * 5)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {Bb : Subgroup ↥(orthDerived Q)} (h : SmallModel ↥(orthDerived Q) Bb) :
    Nat.card Bb = 3 ^ 4 := by
  obtain ⟨l, hl, hlen⟩ := exists_frame_five_minus hQ hdim hminus
  obtain ⟨E, hEel, hEcard, hEtwo⟩ := exists_twoLocal_of_frame hQ hdim hl hlen
  have hle := h.max E hEel hEtwo
  rw [hEcard] at hle
  have hle' : Nat.card Bb ≤ 3 ^ 4 := by simpa using h.card_le
  exact le_antisymm hle' hle

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
