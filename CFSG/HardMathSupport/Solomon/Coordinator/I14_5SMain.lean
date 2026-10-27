module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_5SStep
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Local

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def I145SCentralQuot : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], GLAPPrimeCore 3 Y = ⊥ → ∀ (Z : Subgroup Y) [Z.Normal],
    Z ≤ Subgroup.center Y → IsPGroup 3 Z → GLAPPrimeCore 3 (Y ⧸ Z) = ⊥

theorem i145s_main (h : Lemma27Ns.Input14_5) (h18 : Lemma514CoverNs.Input18_1)
    (hSP : I145SCentralQuot) :
    ∀ (n : ℕ) (A : Type) [Group A] [Finite A], Nat.card A ≤ n → CFSG.Open.IsKGroup A →
      GLAPPrimeCore 3 A = ⊥ → ∀ Q : Subgroup A, IsPGroup 3 Q →
        ⁅GLAPLayer 3 (Subgroup.centralizer (Q : Set A)),
          GLAPPrimeCoreOf 3 (Subgroup.centralizer (Q : Set A))⁆ = ⊥ := by
  intro n
  induction n with
  | zero =>
    intro A _ _ hA
    exfalso
    have := Nat.card_pos (α := A)
    omega
  | succ n ih =>
    intro A _ _ hcard hK hcore Q hQ
    by_cases hQ0 : Q = ⊥
    · subst hQ0
      exact i145s_base hcore
    obtain ⟨x, hxQ, hxc, hx3⟩ := i145s_exists_central_order_three Q hQ hQ0
    have hx1 : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
    set H : Subgroup A := Subgroup.centralizer ({x} : Set A) with hH
    have hQH : Q ≤ H := fun q hq => by
      rw [hH, Subgroup.mem_centralizer_singleton_iff]
      exact hxc q hq
    have hDH : Subgroup.centralizer (Q : Set A) ≤ H := fun c hc => by
      rw [hH, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hc x hxQ).symm
    by_cases hHtop : H = ⊤
    ·
      have hxcen : x ∈ Subgroup.center A := by
        refine Subgroup.mem_center_iff.2 fun g => ?_
        have hg : g ∈ H := hHtop ▸ Subgroup.mem_top g
        rw [hH, Subgroup.mem_centralizer_singleton_iff] at hg
        exact hg
      set Z : Subgroup A := Subgroup.zpowers x with hZ
      have hZc : Z ≤ Subgroup.center A := (Subgroup.zpowers_le).2 hxcen
      have : Z.Normal := ⟨fun n hn g => by
        have := Subgroup.mem_center_iff.1 (hZc hn) g
        rw [this, mul_inv_cancel_right]
        exact hn⟩
      have hZ3 : Nat.card Z = 3 := by rw [hZ, Nat.card_zpowers, hx3]
      have hZp : IsPGroup 3 Z := by
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact IsPGroup.of_card (n := 1) (by rw [hZ3]; norm_num)
      have hcardZ : Nat.card (A ⧸ Z) ≤ n := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
        have h2 := Nat.card_pos (α := A ⧸ Z)
        rw [hZ3] at h1
        omega
      have hK' : CFSG.Open.IsKGroup (A ⧸ Z) :=
        i145s_openKGroup_of_surjective hK (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
      have hQ' : IsPGroup 3 (Q.map (QuotientGroup.mk' Z)) :=
        hQ.of_surjective ((QuotientGroup.mk' Z).subgroupMap Q)
          ((QuotientGroup.mk' Z).subgroupMap_surjective Q)
      exact i145s_central_step Z Q hZc hZ3
        (ih (A ⧸ Z) hcardZ hK' (hSP A hcore Z hZc hZp) _ hQ')
    ·
      have hKtop : CFSG.Open.IsKGroup ↥(⊤ : Subgroup A) :=
        i145s_openKGroup_of_surjective hK (Subgroup.topEquiv.symm : A ≃* ↥(⊤ : Subgroup A)).toMonoidHom
          (Subgroup.topEquiv.symm : A ≃* ↥(⊤ : Subgroup A)).surjective
      have hKH : CFSG.Open.IsKGroup ↥H :=
        hKtop.of_le le_top
      set U : Subgroup ↥H := GLAPPrimeCore 3 ↥H with hU
      have hKB : CFSG.Open.IsKGroup (↥H ⧸ U) :=
        i145s_openKGroup_of_surjective hKH (QuotientGroup.mk' U) (QuotientGroup.mk'_surjective U)
      have hQH3 : IsPGroup 3 (Q.subgroupOf H) :=
        hQ.comap_of_injective H.subtype H.subtype_injective
      have hQB : IsPGroup 3 ((Q.subgroupOf H).map (QuotientGroup.mk' U)) :=
        hQH3.of_surjective ((QuotientGroup.mk' U).subgroupMap (Q.subgroupOf H))
          ((QuotientGroup.mk' U).subgroupMap_surjective (Q.subgroupOf H))
      have hcardB : Nat.card (↥H ⧸ U) ≤ n := by
        have h1 : Nat.card (↥H ⧸ U) ≤ Nat.card ↥H :=
          Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective (s := U))
        have h2 : Nat.card ↥H ≠ Nat.card A := fun heq =>
          hHtop (Subgroup.card_eq_iff_eq_top H |>.1 heq)
        have h3 : Nat.card ↥H ≤ Nat.card A := Subgroup.card_le_card_group H
        omega
      have hbadB := ih (↥H ⧸ U) hcardB hKB (i145s_primeCore_three_quotient ↥H) _ hQB
      have hle := i145s_cop_step H Q hQ hQH hDH hbadB
      have hbal : GLAPLayer 3 (Subgroup.centralizer (Q : Set A)) ≤ GLAPLayer 3 H := by
        have := h18 A H (isKGroup_of_openIsKGroup hKH) Q hQH hQ
        rwa [inf_eq_right.2 hDH] at this
      have hLH : ⁅GLAPLayer 3 H, GLAPPrimeCoreOf 3 H⁆ = ⊥ := h A (isKGroup_of_openIsKGroup hK) hcore x hx1
      have hperf := Lemma27Ns.lc_layer_perfect (G := A) (Subgroup.centralizer (Q : Set A))
      generalize GLAPLayer 3 (Subgroup.centralizer (Q : Set A)) = L at hperf hbal hle ⊢
      generalize GLAPPrimeCoreOf 3 (Subgroup.centralizer (Q : Set A)) = W at hle ⊢
      have h1 : ⁅⁅L, W⁆, L⁆ = ⊥ := by
        refine le_bot_iff.1 ?_
        calc ⁅⁅L, W⁆, L⁆ ≤ ⁅GLAPPrimeCoreOf 3 H, GLAPLayer 3 H⁆ :=
              Subgroup.commutator_mono hle hbal
          _ = ⊥ := by rw [Subgroup.commutator_comm]; exact hLH
      have h2 : ⁅⁅W, L⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm W L]; exact h1
      have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
      rwa [hperf] at h3

end CFSG.HardMathSupport.Solomon.Coordinator
