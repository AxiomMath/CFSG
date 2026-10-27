module

public import CFSG.LargeExtraspecial.S5Fus
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOddCoreTransport
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.LargeExtraspecial.S5Lay
public import CFSG.LargeExtraspecial.S5One

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.Open CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_mul_of_mem_sup {X : Type*} [Group X] {A B : Subgroup X}
    (hAB : A ≤ normalizer (B : Set X)) {y : X} (hy : y ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have h : y ∈ ((A ⊔ B : Subgroup X) : Set X) := hy
  rw [coe_mul_of_left_le_normalizer_right A B hAB] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact ⟨a, ha, b, hb, rfl⟩

theorem conj_mem_map_oddCore {X : Type*} [Group X] {K : Subgroup X} {a o : X} (ha : a ∈ K)
    (ho : o ∈ (CFSG.oddCore K).map K.subtype) :
    a * o * a⁻¹ ∈ (CFSG.oddCore K).map K.subtype := by
  obtain ⟨o', ho', rfl⟩ := ho
  exact ⟨⟨a, ha⟩ * o' * ⟨a, ha⟩⁻¹, (CFSG.oddCore_normal K).conj_mem o' ho' ⟨a, ha⟩, rfl⟩

theorem odd_card_map_oddCore {X : Type*} [Group X] [Finite X] (K : Subgroup X) :
    Odd (Nat.card ((CFSG.oddCore K).map K.subtype)) := by
  rw [card_map_of_injective K.subtype_injective]
  exact CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd

theorem Lbar_inf_ne_bot (hIrr : Irr S) (H : Hyp4 S g) (C : Cons311 S g) {X : Subgroup S.O}
    (hX : IsComponentOf X S.Mbar)
    (hnorm : ∀ h : S.M, S.Lbar ((h : G) * g) ≤ normalizer (X : Set S.O)) :
    S.Lbar g ⊓ X ≠ ⊥ := by
  intro h0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haQ := H.conj_mem
  have hq := hX.2.2
  have hXne : X ≠ ⊥ := ne_bot_of_isQuasisimple hq
  have hnormL : S.Lbar g ≤ normalizer (X : Set S.O) := by simpa using hnorm 1
  have hmemL0 : ∀ y, y ∈ S.Lbar g → y ∈ X → y = 1 := by
    intro y hyL hyX
    have : y ∈ S.Lbar g ⊓ X := ⟨hyL, hyX⟩
    rwa [h0, mem_bot] at this
  obtain ⟨T, hT, hLT⟩ := exists_isSylowTwoIn_ge (S.Lbar_le_Mbar g) (S4.isPGroup_Lbar S haQ)
  have hTN : T ≤ normalizer (S.Lbar g : Set S.O) :=
    S4.le_normalizer_of_weaklyClosed C.weaklyClosed hT.isPGroup hT.le hLT
  have hP := hT.inf_of_isSubnormal hX.2.1
  have hLP : ∀ s ∈ S.Lbar g, ∀ x ∈ T ⊓ X, s * x = x * s := by
    intro s hs x hx
    have hc1 : x * s⁻¹ * x⁻¹ ∈ S.Lbar g :=
      (mem_normalizer_iff.mp (hTN hx.1) _).mp (inv_mem hs)
    have hc2 : s * x * s⁻¹ ∈ X := (mem_normalizer_iff.mp (hnormL hs) x).mp hx.2
    have hc : s * x * s⁻¹ * x⁻¹ = 1 := hmemL0 _
      (by simpa [mul_assoc] using mul_mem hs hc1) (X.mul_mem hc2 (X.inv_mem hx.2))
    calc s * x = s * x * s⁻¹ * x⁻¹ * (x * s) := by group
      _ = x * s := by rw [hc, one_mul]
  obtain ⟨s, hs, x₀, hx₀, hsx₀⟩ := exists_not_commute hIrr H hXne hnorm
  have hss : s * s = 1 := S4.mul_self_of_mem_Lbar S haQ hs
  have hs1 : s ≠ 1 := fun h => hsx₀ (by rw [h, one_mul, mul_one])
  have hsM : s ∈ S.Mbar := S.Lbar_le_Mbar g hs
  have hsC : ∀ l ∈ S.Lbar g, s * l = l * s := fun l hl => S4.Lbar_comm S haQ hs hl
  obtain ⟨K, hK⟩ : ∃ K : Subgroup S.O, K = zpowers s ⊔ X := ⟨_, rfl⟩
  have hsN : zpowers s ≤ normalizer (X : Set S.O) := zpowers_le.mpr (hnormL hs)
  have hKM : K ≤ S.Mbar := hK ▸ sup_le (zpowers_le.mpr hsM) hX.1
  have hXK : X ≤ K := hK ▸ le_sup_right
  have hsK : s ∈ K := hK ▸ mem_sup_left (mem_zpowers s)
  have hKdec : ∀ y ∈ K, ∃ a ∈ zpowers s, ∃ b ∈ X, y = a * b := fun y hy =>
    exists_mul_of_mem_sup hsN (hK ▸ hy)
  set P := T ⊓ X with hPdef
  have hsP : zpowers s ≤ normalizer (P : Set S.O) := zpowers_le.mpr
    (mem_normalizer_of_forall_commute fun x hx => hLP s hs x hx)
  obtain ⟨P', hP'⟩ : ∃ P' : Subgroup S.O, P' = zpowers s ⊔ P := ⟨_, rfl⟩
  have hs2 : IsPGroup 2 (zpowers s) := by
    have hss' : s ^ (2 ^ 1) = 1 := by rw [pow_one, pow_two]; exact hss
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hss')
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hP'2 : IsPGroup 2 P' := hP' ▸ IsPGroup.to_sup_of_normal_right' hs2 hP.isPGroup hsP
  have hP'K : P' ≤ K := by
    rw [hP', hK]
    exact sup_le_sup_left inf_le_right _
  have hsP' : s ∈ P' := hP' ▸ mem_sup_left (mem_zpowers s)
  have hPP' : P ≤ P' := hP' ▸ le_sup_right
  have hP'dec : ∀ y ∈ P', ∃ a ∈ zpowers s, ∃ b ∈ P, y = a * b := fun y hy =>
    exists_mul_of_mem_sup hsP (hP' ▸ hy)
  have hP'mem : ∀ a ∈ zpowers s, ∀ b ∈ P, a * b ∈ P' := fun a ha b hb =>
    P'.mul_mem (hP' ▸ mem_sup_left ha) (hPP' hb)
  have hPK : IsSylowTwoIn P' K := by
    obtain ⟨T'', hT'', hP'T''⟩ := exists_isSylowTwoIn_ge hP'K hP'2
    have hT''X : T'' ⊓ X = P :=
      hP.eq_of_le (le_inf (hPP'.trans hP'T'') inf_le_right) inf_le_right
        (hT''.isPGroup.to_le inf_le_left)
    have hle : T'' ≤ P' := by
      intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hKdec y (hT''.le hy)
      have haT : a ∈ T'' := by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
        exact zpow_mem (hP'T'' hsP') i
      have hbP : b ∈ P := by
        rw [← hT''X]
        refine ⟨?_, hb⟩
        have := T''.mul_mem (T''.inv_mem haT) hy
        simpa using this
      exact hP'mem a ha b hbP
    rw [le_antisymm hle hP'T''] at hT''
    exact hT''
  have hP'C : ∀ y ∈ P', ∀ l ∈ S.Lbar g, y * l = l * y := by
    intro y hy l hl
    obtain ⟨a, ha, b, hb, rfl⟩ := hP'dec y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    have h1 : s ^ i * l = l * s ^ i := (Commute.zpow_left (hsC l hl) i).eq
    have h2 : b * l = l * b := (hLP l hl b hb).symm
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have hP's : ∀ y ∈ P', y * s = s * y := fun y hy => hP'C y hy s hs
  set z : K := ⟨s, hsK⟩ with hzdef
  have hz1 : z ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  have hzz : z * z = 1 := Subtype.ext hss
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  set Q := hPK.toSylow with hQ
  have hzC : z ∈ centralizer ((Q : Subgroup K) : Set K) := by
    rw [mem_centralizer_iff]
    intro q hq
    have hq' : (q : S.O) ∈ P' := hq
    exact Subtype.ext (hP's q hq')
  have hwc : ∀ k : K, k⁻¹ * z * k ∈ (Q : Subgroup K) → k⁻¹ * z * k = z := by
    intro k hk
    have hk' : (k : S.O)⁻¹ * s * k ∈ P' := hk
    have hwC : ∀ l ∈ S.Lbar g, (k : S.O)⁻¹ * s * (k : S.O)⁻¹⁻¹ * l =
        l * ((k : S.O)⁻¹ * s * (k : S.O)⁻¹⁻¹) := by
      intro l hl
      rw [inv_inv]
      exact hP'C _ hk' l hl
    obtain ⟨n, -, hnN, hn⟩ := exists_mem_normalizer_conj H C (S.Mbar.inv_mem (hKM k.2)) hsC hwC
    have hwL : (k : S.O)⁻¹ * s * k ∈ S.Lbar g := by
      have h1 : n * s * n⁻¹ ∈ S.Lbar g := (mem_normalizer_iff.mp hnN s).mp hs
      rw [← hn, inv_inv] at h1
      exact h1
    obtain ⟨a, ha, b, hb, hab⟩ := hP'dec _ hk'
    have haL : a ∈ S.Lbar g := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
      exact zpow_mem hs i
    have hbL : b ∈ S.Lbar g := by
      have := mul_mem (inv_mem haL) hwL
      rw [hab] at this
      simpa using this
    have hb1 : b = 1 := hmemL0 b hbL hb.2
    rw [hb1, mul_one] at hab
    apply Subtype.ext
    change (k : S.O)⁻¹ * s * k = s
    rcases (Setting.mem_zpowers_iff_of_mul_self hss).mp ha with h1 | h1
    · exfalso
      rw [h1] at hab
      apply hs1
      have := congrArg (fun y => (k : S.O) * y * (k : S.O)⁻¹) hab
      simpa [mul_assoc] using this
    · rw [hab, h1]
  have hZ := CFSG.ShultStronglyClosedTI.minimalLocalFailure_isolated_commutators_mem_oddCore hzo
    (fun k hcomm => CFSG.Adapters.isolated_of_weakClosure Q hzC hzz hwc k hcomm)
  obtain ⟨O, hO⟩ : ∃ O : Subgroup S.O, O = (CFSG.oddCore K).map K.subtype := ⟨_, rfl⟩
  have hOodd : Odd (Nat.card O) := hO ▸ odd_card_map_oddCore K
  have hcomX : ∀ x ∈ X, x * s * x⁻¹ * s⁻¹ ∈ O ⊓ X := by
    intro x hx
    have hxK : x ∈ K := hXK hx
    refine ⟨hO ▸ ⟨_, hZ ⟨x, hxK⟩, rfl⟩, ?_⟩
    have h1 : s * x⁻¹ * s⁻¹ ∈ X := (mem_normalizer_iff.mp (hnormL hs) _).mp (X.inv_mem hx)
    have := X.mul_mem hx h1
    simpa [mul_assoc] using this
  have hOXnorm : ∀ a ∈ X, ∀ o ∈ O ⊓ X, a * o * a⁻¹ ∈ O ⊓ X := fun a ha o ho =>
    ⟨hO ▸ conj_mem_map_oddCore (hXK ha) (hO ▸ ho.1),
      X.mul_mem (X.mul_mem ha ho.2) (X.inv_mem ha)⟩
  rcases commute_or_eq_of_normalized hq inf_le_right hOXnorm with hcen | heq
  · have : Group.IsPerfect X := ⟨hq.1⟩
    have h1 : ⁅X, zpowers s⁆ ≤ O ⊓ X := by
      rw [commutator_le]
      intro x hx y hy
      rcases (Setting.mem_zpowers_iff_of_mul_self hss).mp hy with rfl | rfl
      · rw [commutatorElement_one_right]
        exact one_mem _
      · exact hcomX x hx
    have h2 : ⁅O ⊓ X, X⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro n hn
      rw [mem_centralizer_iff]
      intro a ha
      exact (hcen n hn a ha).symm
    have hdouble : ⁅⁅X, zpowers s⁆, X⁆ = ⊥ :=
      le_bot_iff.mp (h2 ▸ commutator_mono h1 le_rfl)
    have hcomm := Quasisimple.perfect_double_commutator X (zpowers s) hdouble
    have hc : x₀ * s * x₀⁻¹ * s⁻¹ ∈ ⁅X, zpowers s⁆ :=
      commutator_mem_commutator hx₀ (mem_zpowers s)
    rw [hcomm, mem_bot] at hc
    apply hsx₀
    calc s * x₀ = (x₀ * s * x₀⁻¹ * s⁻¹)⁻¹ * (x₀ * s) := by group
      _ = x₀ * s := by rw [hc, inv_one, one_mul]
  · have hXodd : Odd (Nat.card X) := by
      rw [← heq]
      exact Odd.of_dvd_nat hOodd (card_dvd_of_le inf_le_left)
    exact not_isSolvable_of_isQuasisimple hq (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hXodd)

end CFSG.LargeExtraspecial.S5
