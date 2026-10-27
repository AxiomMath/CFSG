module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Quot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.QuotientAEmpty

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TQ

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

omit [Finite X] in
theorem eq_one_or_eq_of_mem_zpowers {c m : X} (hc : orderOf c = 2)
    (hm : m ∈ Subgroup.zpowers c) : m = 1 ∨ m = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
  rw [← zpow_mod_orderOf, hc]
  have h : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem exists_tightDatum (h : TypeRFam 3 Φ) {A : Subgroup X} (hA : A ∈ Φ) {x : X}
    (hx : IsUniqueInvolution A x) :
    ∃ S : Sylow 2 ↥A, TightDatum A S x ∧
      Nonempty (↥(S : Subgroup ↥A) ≃* QuaternionGroup 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥A) := inferInstance
  have hP : IsSylow2In ((S : Subgroup ↥A).map A.subtype) A := isSylow2In_map_subtype A S
  obtain ⟨e⟩ := h.quat A hA _ hP
  have e' : ↥(S : Subgroup ↥A) ≃* QuaternionGroup 2 :=
    (Subgroup.equivMapOfInjective (S : Subgroup ↥A) A.subtype A.subtype_injective).trans e
  have h8 : Nat.card ↥(S : Subgroup ↥A) = 8 := by
    rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [h8]; norm_num)
  have hs2 : ((s : ↥A) : X) * ((s : ↥A) : X) = 1 := by
    have h1 : s ^ 2 = 1 := by
      have h0 := pow_orderOf_eq_one s
      rwa [hs] at h0
    rw [pow_two] at h1
    exact congrArg (fun y : ↥(S : Subgroup ↥A) => ((y : ↥A) : X)) h1
  have hs1 : ((s : ↥A) : X) ≠ 1 := by
    intro h1
    have h2 : s = 1 := Subtype.ext (Subtype.ext h1)
    rw [h2, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hsx : ((s : ↥A) : X) = x :=
    (hx.unique _ (s : ↥A).2 hs2).resolve_left hs1
  have hmem : x ∈ (S : Subgroup ↥A).map A.subtype := ⟨(s : ↥A), s.2, hsx⟩
  have hcent : A ≤ Subgroup.centralizer ({x} : Set X) := h.le_centralizer hA hx
  refine ⟨S, ⟨⟨3, le_rfl, ⟨e'⟩⟩, hmem, ?_, hcent, ?_, h.twoGroup A hA⟩, ⟨e'⟩⟩
  · exact orderOf_eq_prime (by rw [pow_two]; exact hx.sq) hx.ne_one
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hcent).mpr (h.tight A hA x hx)

end TQ

theorem twinQuotDatum :
    ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), TypeRFam 3 Φ →
      classicalInvolutionOddCore X = ⊥ → (∀ L ∈ Φ, AEmpty Φ L) →
      ∀ A ∈ Φ, (⨆ g : X, conjSub g A) = ⊤ → ∀ B ∈ omegaNbr Φ A, (∃ g : X, conjSub g A = B) →
      ∀ x x' : X, IsUniqueInvolution A x → IsUniqueInvolution B x' →
      x * x' ∈ Subgroup.center X → ∀ (N : Subgroup X) [N.Normal], N = Subgroup.zpowers (x * x') →
        ∃ S : Sylow 2 ↥(A.map (QuotientGroup.mk' N)),
          PhilipHall.QuaternionBridge.Q8TwinDatum (A.map (QuotientGroup.mk' N)) S
            (QuotientGroup.mk' N x) ∧
          Nonempty (↥(S : Subgroup ↥(A.map (QuotientGroup.mk' N))) ≃* QuaternionGroup 2) ∧
          TightSelfGen (A.map (QuotientGroup.mk' N)) ∧ TightOddFree (X ⧸ N) ∧
          HypOmegaGen (CoreAssembly.conjClass (tightCore (A.map (QuotientGroup.mk' N)))) ∧
          AEmpty (CoreAssembly.conjClass (tightCore (A.map (QuotientGroup.mk' N))))
            (tightCore (A.map (QuotientGroup.mk' N))) ∧
          B.map (QuotientGroup.mk' N) ∈
            twinSet (CoreAssembly.conjClass (tightCore (A.map (QuotientGroup.mk' N))))
              (tightCore (A.map (QuotientGroup.mk' N))) ∧
          B.map (QuotientGroup.mk' N) ≠ tightCore (A.map (QuotientGroup.mk' N)) := by
  intro X _ _ Φ hΦ hO _ A hA hgen B hB hAB x x' hx hx' hc N _ hN
  obtain ⟨S, hd, ⟨eS⟩⟩ := TQ.exists_tightDatum hΦ hA hx
  have hcore : tightCore A = A := hΦ.closure_twoElts hA
  have hcls : TightCls X A S x := ⟨⟨eS⟩, by
    change (⨆ g : X, conjSub g (tightCore A)) = ⊤
    rw [hcore]
    exact hgen, hO⟩
  have hcZ : ∀ a : X, a * (x * x') = (x * x') * a := Subgroup.mem_center_iff.mp hc
  have hxx' : x * x' = x' * x := by
    have h1 : x * (x * x') = x * (x' * x) := by rw [hcZ x, mul_assoc]
    exact mul_left_cancel h1
  have hc2 : (x * x') * (x * x') = 1 := by
    calc (x * x') * (x * x') = x * (x' * x) * x' := by group
      _ = x * (x * x') * x' := by rw [hxx']
      _ = (x * x) * (x' * x') := by group
      _ = 1 := by rw [hx.sq, hx'.sq, mul_one]
  have hNc : N ≤ Subgroup.center X := hN ▸ Subgroup.zpowers_le.mpr hc
  have hN2 : IsPGroup 2 ↥N := hN ▸ Balance.isPGroup_zpowers_of_mul_self_eq_one hc2
  have hcN : x * x' ∈ N := hN ▸ Subgroup.mem_zpowers (x * x')
  have hc1 : x * x' ≠ 1 := by
    intro h1
    have hxe : x' = x := by
      calc x' = (x * x) * x' := by rw [hx.sq, one_mul]
        _ = x * (x * x') := by group
        _ = x := by rw [h1, mul_one]
    have hBtw : B ∈ twinSet Φ A := ⟨hB.1, x, hx, hxe ▸ hx'⟩
    exact hB.2.1 (hΦ.noTwins A hA B hBtw)
  have hco : orderOf (x * x') = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
  have htN : x ∉ N := by
    intro hxN
    rw [hN] at hxN
    rcases TQ.eq_one_or_eq_of_mem_zpowers hco hxN with h1 | h1
    · exact hx.ne_one h1
    · apply hx'.ne_one
      have h2 : x * 1 = x * x' := by rw [mul_one]; exact h1
      exact (mul_left_cancel h2).symm
  obtain ⟨g, hg⟩ := hAB
  have hy : g * x * g⁻¹ = x * (x * x') := by
    have h1 := hx.conj g
    rw [hg] at h1
    rw [h1.eq hx']
    calc x' = (x * x) * x' := by rw [hx.sq, one_mul]
      _ = x * (x * x') := by group
  have hQ := q8Quot_of_twin hd hcls hNc hN2 htN hcN hc1 hy
  have hAE := aEmpty_map' hd ⟨eS⟩ hNc hN2 htN
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  have hcoreQ : tightCore (A.map (QuotientGroup.mk' N)) =
      (tightCore A).map (QuotientGroup.mk' N) := (TwistQ.tightCore_map hRN).symm
  have hBmap : B.map (QuotientGroup.mk' N) =
      conjSub (QuotientGroup.mk' N g) ((tightCore A).map (QuotientGroup.mk' N)) := by
    rw [← hg, hcore, TwistQ.conjSub_map (N := N) g A]
  have hz := isUniqueInvolution_map_core hd hN2 htN
  have hfix : QuotientGroup.mk' N g * QuotientGroup.mk' N x * (QuotientGroup.mk' N g)⁻¹ =
      QuotientGroup.mk' N x := by
    have hπc : QuotientGroup.mk' N (x * x') = 1 := (QuotientGroup.eq_one_iff _).mpr hcN
    rw [← map_inv, ← map_mul, ← map_mul, hy, map_mul, hπc, mul_one]
  have htw : conjSub (QuotientGroup.mk' N g) ((tightCore A).map (QuotientGroup.mk' N)) ∈
      twinSet (CoreAssembly.conjClass ((tightCore A).map (QuotientGroup.mk' N)))
        ((tightCore A).map (QuotientGroup.mk' N)) := by
    refine ⟨⟨QuotientGroup.mk' N g, rfl⟩, QuotientGroup.mk' N x, hz, ?_⟩
    have h1 := hz.conj (QuotientGroup.mk' N g)
    rwa [hfix] at h1
  have hne := conjSub_map_ne_of_twin hd ⟨eS⟩ hNc hN2 htN hcN hc1 hy
  refine ⟨TwistQ.sylowMap N S, hQ.datum, hQ.cls.1, hQ.cls.2.1, hQ.cls.2.2, hQ.hyp, hAE, ?_, ?_⟩
  · rw [hcoreQ, hBmap]
    exact htw
  · rw [hcoreQ, hBmap]
    exact hne

end CFSG.ClassicalInvolution.Q3.TL4
