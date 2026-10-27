module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017LyFive
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Table

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

variable {X : Type} [Group X] [Finite X]

theorem exists_involution_of_two_group {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) :
    ∃ t ∈ Q, orderOf t = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hne
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hne (Subgroup.card_eq_one.1 hn)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (by
    rw [hn]
    exact dvd_pow_self 2 hn0)
  exact ⟨g, g.2, by rw [← hg, Subgroup.orderOf_coe]⟩

theorem glaTwoLocalRank_le_of_cent {p k m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : ∀ j, 0 < j → j < m → ¬ 2 ^ j ≡ 1 [MOD p])
    (ha : ∀ t : X, orderOf t = 2 → ¬ p ^ (k + 1) ∣ Nat.card (Subgroup.centralizer ({t} : Set X)))
    (hb : ∀ t : X, orderOf t = 2 → ∀ F : Subgroup X, F ≤ Subgroup.centralizer ({t} : Set X) →
      IsElemAbelian p F → Nat.card F = p ^ k →
        ¬ 2 ^ m ∣ Nat.card (Subgroup.centralizer (F : Set X))) :
    GLATwoLocalRank p X ≤ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine glaTwoLocalRank_le_of_card_le hp fun R E₀ hR hR2 hEN hE₀ => ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (isPGroup_of_elemAbelian hE₀)
  have hkn : k + 1 ≤ n := by
    by_contra h
    push Not at h
    rw [hn] at hlt
    exact absurd hlt (not_lt.2 (Nat.pow_le_pow_right hp.pos (by omega)))
  obtain ⟨E₁, hE₁⟩ := Sylow.exists_subgroup_card_pow_prime (G := E₀) p (n := k + 1)
    (by rw [hn]; exact Nat.pow_dvd_pow p hkn)
  set E : Subgroup X := E₁.map E₀.subtype with hEdef
  have hEE₀ : E ≤ E₀ := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hE : IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hE₀ hEE₀
  have hEcard : Nat.card E = p ^ (k + 1) := by
    rw [hEdef, Subgroup.card_map_of_injective E₀.subtype_injective, hE₁]
  have hER : E ≤ Subgroup.normalizer (R : Set X) := hEE₀.trans hEN
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hEcard
    exact absurd hEcard.symm (Nat.one_lt_pow (by omega) hp.one_lt).ne'
  have hR3 : ¬ p ∣ Nat.card R := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hR2
    rw [hj]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  obtain ⟨B, hB, x, hxR, hx1, hBx⟩ := exists_hyperplane_fixed_p hp hE hEne hR3 hR hER
  set F : Subgroup X := B.map E.subtype with hFdef
  have hFE : F ≤ E := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hFab : IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE
  have hFcard : Nat.card F * p = Nat.card E := by
    rw [hFdef, Subgroup.card_map_of_injective E.subtype_injective, ← hB,
      Subgroup.card_mul_index]
  have hFk : Nat.card F = p ^ k := by
    rw [hEcard, pow_succ] at hFcard
    exact Nat.eq_of_mul_eq_mul_right hp.pos hFcard
  set RF : Subgroup X := R ⊓ Subgroup.centralizer (F : Set X) with hRFdef
  have hRF2 : IsPGroup 2 RF := hR2.to_le inf_le_left
  have hxF : x ∈ RF := by
    refine ⟨hxR, Subgroup.mem_centralizer_iff.2 fun f hf => ?_⟩
    obtain ⟨b, hb, rfl⟩ := hf
    exact hBx b hb
  have hRFne : RF ≠ ⊥ := fun h => hx1 ((Subgroup.mem_bot).1 (h ▸ hxF))
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    comm_of_isElemAbelian' hE ha hb
  have hEnorm : E ≤ Subgroup.normalizer (RF : Set X) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ e ∈ E, ∀ r ∈ RF, e * r * e⁻¹ ∈ RF := fun e he r hr => by
      refine ⟨(Subgroup.mem_normalizer_iff.1 (hER he) r).1 hr.1,
        Subgroup.mem_centralizer_iff.2 fun f hf => ?_⟩
      have hfr := Subgroup.mem_centralizer_iff.1 hr.2 f hf
      have hfe := hcommE f (hFE hf) e he
      exact ((Commute.mul_right (Commute.mul_right hfe hfr) (Commute.inv_right hfe))).eq
    intro r
    refine ⟨fun hr => key e he r hr, fun hr => ?_⟩
    have := key e⁻¹ (E.inv_mem he) _ hr
    simpa [mul_assoc] using this
  obtain ⟨t, htRF, ht2⟩ := exists_involution_of_two_group hRF2 hRFne
  have hFt : F ≤ Subgroup.centralizer ({t} : Set X) := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 htRF.2 f hf)
  have hbF := hb t ht2 F hFt hFab hFk
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hRF2
  have hjm : j < m := by
    by_contra h
    push Not at h
    apply hbF
    refine (Nat.pow_dvd_pow 2 h).trans ?_
    rw [← hj]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, pow_zero] at hj
      exact absurd (Subgroup.card_eq_one.1 hj) hRFne
    · exact h
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer E RF hEnorm
  have hEp : IsPGroup p E := isPGroup_of_elemAbelian hE
  have hmod := hEp.card_modEq_card_fixedPoints RF
  rw [hj] at hmod
  have hfix : ∃ r : RF, r ≠ 1 ∧ r ∈ MulAction.fixedPoints E RF := by
    by_contra hall
    push Not at hall
    have h1 : Nat.card (MulAction.fixedPoints E RF) = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨1, fun e => smul_one e⟩, fun ⟨r, hr⟩ => ?_⟩
      by_contra hne
      exact hall r (fun h => hne (Subtype.ext h)) hr
    rw [h1] at hmod
    exact hm j hj0 hjm hmod
  obtain ⟨r, hr1, hrfix⟩ := hfix
  set Q : Subgroup X := RF ⊓ Subgroup.centralizer (E : Set X) with hQdef
  have hrQ : (r : X) ∈ Q := by
    refine ⟨r.2, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
    have h := congrArg Subtype.val (hrfix ⟨e, he⟩)
    change e * (r : X) * e⁻¹ = r at h
    calc e * (r : X) = e * (r : X) * e⁻¹ * e := by group
      _ = r * e := by rw [h]
  have hQne : Q ≠ ⊥ := fun h => hr1 (Subtype.ext ((Subgroup.mem_bot).1 (h ▸ hrQ)))
  obtain ⟨s, hsQ, hs2⟩ := exists_involution_of_two_group (hRF2.to_le inf_le_left) hQne
  have hEs : E ≤ Subgroup.centralizer ({s} : Set X) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hsQ.2 e he)
  exact ha s hs2 (hEcard ▸ Subgroup.card_dvd_of_le hEs)

end CFSG.LocalAnalysis.GLTheoremA.H1017
