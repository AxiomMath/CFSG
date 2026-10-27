module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf48Z
public import CFSG.Adapters.Involutions

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open
open scoped Pointwise

section ZStarMain

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_moving (hO : classicalInvolutionOddCore G = ⊥)
    (P : Subgroup G) [hPn : P.Normal] (hP : IsPGroup 2 P) (S : Sylow 2 G) (W U : Subgroup G) (w : G)
    (hwW : w ∈ W) (hWS : W ≤ (S : Subgroup G))
    (hWn : ∀ s ∈ (S : Subgroup G), ∀ a ∈ W, s * a * s⁻¹ ∈ W)
    (hWw : W ≤ P ⊔ Subgroup.zpowers w) (hw2 : w * w ∈ P)
    (hweak : ∀ g : G, (∀ a ∈ W, g⁻¹ * a * g ∈ (S : Subgroup G)) → ∀ a ∈ W, g⁻¹ * a * g ∈ W)
    (hUW : U ≤ W)
    (hno : ¬ ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ U ≤ Q) :
    ∃ x ∈ Subgroup.normalClosure (U : Set G), Odd (orderOf x) ∧ ∃ p ∈ P, x * p ≠ p * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push_neg at hcon
  by_cases hwP : w ∈ P
  · apply hno
    refine ⟨P, hPn, hP, fun u hu => ?_⟩
    have : W ≤ P := hWw.trans (sup_le le_rfl (Subgroup.zpowers_le.mpr hwP))
    exact this (hUW hu)
  have hPS : P ≤ (S : Subgroup G) := hP.le_sylow_of_normal S
  have hconjP : ∀ g x : G, x ∈ P ↔ g * x * g⁻¹ ∈ P := fun g x =>
    ⟨fun h => hPn.conj_mem x h g, fun h => by
      have := hPn.conj_mem _ h g⁻¹
      simpa [mul_assoc] using this⟩
  set π := QuotientGroup.mk' P with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective P
  have hπ1 : ∀ x, π x = 1 ↔ x ∈ P := fun x => QuotientGroup.eq_one_iff x
  have hsq : π w * π w = 1 := by rw [← map_mul, hπ1]; exact hw2
  have hπw1 : π w ≠ 1 := fun h => hwP ((hπ1 w).mp h)
  have himg : ∀ a ∈ W, π a = 1 ∨ π a = π w := by
    have hle : P ⊔ Subgroup.zpowers w ≤ (Subgroup.zpowers (π w)).comap π :=
      sup_le (fun p hp => by rw [Subgroup.mem_comap, (hπ1 p).mpr hp]; exact one_mem _)
        (Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers (π w)))
    intro a ha
    exact eq_one_or_of_mem_zpowers_of_mul_self hsq (hle (hWw ha))
  have hconjw : ∀ s ∈ (S : Subgroup G), π s * π w = π w * π s := by
    intro s hs
    rcases himg _ (hWn s hs w hwW) with h | h
    · exact absurd ((hconjP s w).mpr ((hπ1 _).mp h)) hwP
    · have : π s * π w * (π s)⁻¹ = π w := by
        rw [← map_inv, ← map_mul, ← map_mul, h]
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
  let S' : Sylow 2 (G ⧸ P) := S.mapSurjective hπs
  have hS' : (S' : Subgroup (G ⧸ P)) = (S : Subgroup G).map π := Sylow.coe_mapSurjective _ _
  let z : ↥(S' : Subgroup (G ⧸ P)) := ⟨π w, by rw [hS']; exact ⟨w, hWS hwW, rfl⟩⟩
  have hzZ : z ∈ Subgroup.center ↥(S' : Subgroup (G ⧸ P)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨s, hs, hsg⟩ := (hS' ▸ g.2 : (g : G ⧸ P) ∈ (S : Subgroup G).map π)
    apply Subtype.ext
    change (g : G ⧸ P) * π w = π w * (g : G ⧸ P)
    rw [← hsg]
    exact hconjw s hs
  have hz2 : orderOf z = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change π w ^ 2 = 1
      rw [sq]; exact hsq
    · intro h
      exact hπw1 (congrArg Subtype.val h)
  have hwc : ∀ g : G ⧸ P, g⁻¹ * (z : G ⧸ P) * g ∈ (S' : Subgroup (G ⧸ P)) →
      g⁻¹ * (z : G ⧸ P) * g = z := by
    intro gb hmem
    obtain ⟨g, rfl⟩ := hπs gb
    have hmem' : (π g)⁻¹ * π w * π g ∈ (S : Subgroup G).map π := by
      rw [← hS']; exact hmem
    obtain ⟨s, hs, hsg⟩ := hmem'
    have hsm : s⁻¹ * (g⁻¹ * w * g) ∈ P := by
      rw [← hπ1, map_mul, map_inv, hsg]
      simp only [map_mul, map_inv]
      group
    have hgwS : g⁻¹ * w * g ∈ (S : Subgroup G) := by
      have : g⁻¹ * w * g = s * (s⁻¹ * (g⁻¹ * w * g)) := by group
      rw [this]
      exact Subgroup.mul_mem _ hs (hPS hsm)
    have hT : P ⊔ Subgroup.zpowers w ≤
        (S : Subgroup G).comap (MulAut.conj g⁻¹).toMonoidHom := by
      refine sup_le (fun p hp => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_comap]
        change g⁻¹ * p * g⁻¹⁻¹ ∈ _
        exact hPS (hPn.conj_mem p hp g⁻¹)
      · rw [Subgroup.mem_comap]
        change g⁻¹ * w * g⁻¹⁻¹ ∈ _
        simpa using hgwS
    have hW' : ∀ a ∈ W, g⁻¹ * a * g ∈ (S : Subgroup G) := fun a ha => by
      have := hT (hWw ha)
      rw [Subgroup.mem_comap] at this
      simpa using this
    have hgW := hweak g hW' w hwW
    rcases himg _ hgW with h | h
    · exact absurd ((hconjP g⁻¹ w).mpr (by simpa using (hπ1 _).mp h)) hwP
    · change (π g)⁻¹ * π w * π g = π w
      rw [← map_inv, ← map_mul, ← map_mul, h]
  obtain ⟨-, hcent⟩ := Adapters.glauberman_zStar S' z hzZ hz2 hwc
  set ρ : G →* (G ⧸ P) ⧸ CFSG.oddCore (G ⧸ P) :=
    (QuotientGroup.mk' (CFSG.oddCore (G ⧸ P))).comp π with hρ
  have hρw : ρ w ∈ Subgroup.center ((G ⧸ P) ⧸ CFSG.oddCore (G ⧸ P)) := hcent
  have hρ_apply : ∀ x, ρ x = QuotientGroup.mk' (CFSG.oddCore (G ⧸ P)) (π x) := fun x => rfl
  have hρker : ∀ x, ρ x = 1 ↔ π x ∈ CFSG.oddCore (G ⧸ P) := fun x => by
    rw [hρ_apply]; exact QuotientGroup.eq_one_iff _
  have hρP : ∀ p ∈ P, ρ p = 1 := fun p hp => by
    rw [hρker, (hπ1 p).mpr hp]; exact one_mem _
  have hρsq : ρ w * ρ w = 1 := by rw [← map_mul]; exact hρP _ hw2
  set N2 : Subgroup G := (Subgroup.zpowers (ρ w)).comap ρ with hN2
  haveI hN2n : N2.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN2, Subgroup.mem_comap] at hn ⊢
    have hc := Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr hρw) hn) (ρ g)
    have : ρ (g * n * g⁻¹) = ρ n := by
      rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul]
      exact hc
    rw [this]; exact hn
  have hPW : P ⊔ Subgroup.zpowers w ≤ N2 :=
    sup_le (fun p hp => by rw [hN2, Subgroup.mem_comap, hρP p hp]; exact one_mem _)
      (Subgroup.zpowers_le.mpr (by rw [hN2, Subgroup.mem_comap]; exact Subgroup.mem_zpowers _))
  set L : Subgroup G := Subgroup.normalClosure (U : Set G) with hL
  have hLN : L ≤ N2 := Subgroup.normalClosure_le_normal (fun u hu => hPW (hWw (hUW hu)))
  have hLsplit : ∀ x ∈ L, ρ x = 1 ∨ ρ x = ρ w := fun x hx =>
    eq_one_or_of_mem_zpowers_of_mul_self hρsq (hLN hx)
  have hLM : ∀ x ∈ L, ρ (x * x) = 1 := fun x hx => by
    rw [map_mul]
    rcases hLsplit x hx with h | h
    · rw [h, mul_one]
    · rw [h]; exact hρsq
  have hCn : (Subgroup.centralizer (P : Set G)).Normal := by
    refine ⟨fun c hc g h hh => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ (hPn.conj_mem h hh g⁻¹)
    simp only [inv_inv] at h1
    calc h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * h := by group
  have hL0 : ∀ y ∈ L, ρ y = 1 → ∃ k, orderOf y = 2 ^ k := by
    intro y hyL hyM
    by_contra hne
    have hy0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
    obtain ⟨q, hq, hqd, hq2⟩ : ∃ q, q.Prime ∧ q ∣ orderOf y ∧ q ≠ 2 := by
      by_contra h
      push_neg at h
      exact hne ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hy0 (fun {d} hd hdd => h d hd hdd)⟩
    have hqodd : Odd q := hq.odd_of_ne_two hq2
    have hy'ord : orderOf (y ^ (orderOf y / q)) = q := orderOf_pow_orderOf_div hy0 hqd
    have hy'L : y ^ (orderOf y / q) ∈ L := L.pow_mem hyL _
    have hy'M : ρ (y ^ (orderOf y / q)) = 1 := by rw [map_pow, hyM, one_pow]
    have hy'odd : Odd (orderOf (y ^ (orderOf y / q))) := by rw [hy'ord]; exact hqodd
    set y' := y ^ (orderOf y / q) with hy'
    set R : Subgroup G := Subgroup.normalClosure ({y'} : Set G) with hR
    have hRL : R ≤ L := Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hy'L)
    have hy'C : y' ∈ Subgroup.centralizer (P : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun p hp => (hcon y' hy'L hy'odd p hp).symm
    have hRC : R ≤ Subgroup.centralizer (P : Set G) :=
      Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hy'C)
    have hRM : R ≤ ρ.ker :=
      Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hy'M)
    have hodd : Odd (P.subgroupOf R).index := by
      set f : ↥R →* (G ⧸ P) := π.comp R.subtype with hf
      have hker : f.ker = P.subgroupOf R := by
        ext x
        simp [hf, MonoidHom.mem_ker, hπ1, Subgroup.mem_subgroupOf]
      rw [← hker, Subgroup.index_ker]
      have hrange : f.range ≤ CFSG.oddCore (G ⧸ P) := by
        rintro _ ⟨x, rfl⟩
        exact (hρker _).mp (hRM x.2)
      exact Odd.of_dvd_nat (odd_card_oddCore _) (Subgroup.card_dvd_of_le hrange)
    have h1 := odd_elt_eq_one_of_central hO R P hP
      (fun r hr n hn => (Subgroup.mem_centralizer_iff.mp (hRC hr) n hn).symm) hodd
      (Subgroup.subset_normalClosure rfl) hy'odd
    rw [h1, orderOf_one] at hy'ord
    exact hq.one_lt.ne hy'ord
  have hL2 : IsPGroup 2 L := by
    refine IsPGroup.iff_orderOf.mpr fun x => ?_
    obtain ⟨k, hk⟩ := hL0 ((x : G) * x) (L.mul_mem x.2 x.2) (hLM _ x.2)
    have hd : orderOf (x : G) ∣ 2 ^ (k + 1) := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_succ', pow_mul, sq, ← hk, pow_orderOf_eq_one]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact ⟨i, by rw [← Subgroup.orderOf_coe]; exact hi⟩
  exact hno ⟨L, inferInstance, hL2, Subgroup.le_normalClosure⟩

end ZStarMain

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
