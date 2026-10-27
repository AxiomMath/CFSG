module

public import CFSG.LieType.SeitzGeneration.ExcPlaneLow
public import CFSG.RankThree.PartOne.N143X.ReeRank
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicThreeTorus

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.N143X CFSG.RankThree.PartOne.KE CFSG.TauCetiBridge TauCeti

section F4


theorem card_le_sq_of_F4_phiThree (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1)
    {E : Subgroup ↥(adjointGroup .F4 K)} (hE : ∀ x ∈ E, x ^ p = 1) : Nat.card E ≤ p ^ 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨F, hF⟩ := exists_ringHom_pow_card K (AlgebraicClosure K)
  obtain ⟨⟨g, hg, hgn⟩, hmain⟩ := F4_cyclotomic_three_torus_and_regular_prime_centralizers K
    (AlgebraicClosure K) F hF _ rfl
  set Γ := conjEntrywiseImage K g⁻¹ with hΓ
  set T₀ := torusGroup .F4 (AlgebraicClosure K) ⊓ Γ with hT₀
  set T := T₀.map (MulAut.conj g).toMonoidHom with hT
  obtain ⟨-, ⟨eT⟩, -, -, hp', -⟩ := hmain g hg hgn Γ T₀ T rfl rfl rfl
  obtain ⟨-, hconj, -⟩ := hp' p hp hp3 hpd
  obtain ⟨c, hc⟩ := hconj E (isPGroup_of_pow_eq_one hE)
  let ι : ↥(adjointGroup .F4 K) →* ModGL .F4 (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup .F4 K).subtype
  let φ : ↥(adjointGroup .F4 K) →* ModGL .F4 (AlgebraicClosure K) :=
    ι.comp (MulAut.conj c).toMonoidHom
  have hφ : Function.Injective φ :=
    (((baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp
      Subtype.val_injective)).comp (MulAut.conj c).injective
  have hEt : ∀ x ∈ E, φ x ∈ T := fun x hx => hc ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact card_le_sq_of_map_into_prod φ hφ T
    ((Subgroup.equivMapOfInjective T₀ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans eT) hp.pos hE hEt


theorem exists_dvd_phi_of_dvd_card_F4 {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K) (hdvd : p ∣ Nat.card (adjointGroup .F4 K)) :
    ∃ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 8 ∨ m = 12) ∧
      (p : ℤ) ∣ (exhaustionPhi m).eval (Nat.card K : ℤ) := by
  rw [exactF4FiniteOrder K] at hdvd
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hD : ∃ d ∈ ([2, 6, 8, 12] : List ℕ), p ∣ Nat.card K ^ d - 1 := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · exact absurd (hp.dvd_of_dvd_pow h) hpK
          · exact ⟨2, by simp, h⟩
        · exact ⟨6, by simp, h⟩
      · exact ⟨8, by simp, h⟩
    · exact ⟨12, by simp, h⟩
  obtain ⟨m, hm, hpm⟩ := exists_mem_row_of_dvd_pow_sub_one hp hq1
    (D := [2, 6, 8, 12]) (by decide) (row := ({1, 2, 3, 4, 6, 8, 12} : Finset ℕ)) (by decide) hD
  exact ⟨m, by simpa using hm, hpm⟩


theorem rankLE2_adjointGroup_F4 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) (hnd : ¬ p ∣ Nat.card K ^ 2 - 1) :
    RankLE2 p ↥(adjointGroup .F4 K) := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq1 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hp3 : 3 < p := by
    by_contra h
    have hp3 : p = 3 := by have := hp.two_le; omega
    subst hp3
    apply hnd
    have : Fact (Nat.Prime 3) := ⟨hp⟩
    have hne : ((Nat.card K : ℕ) : ZMod 3) ≠ 0 := fun h0 =>
      hpK ((ZMod.natCast_eq_zero_iff _ 3).1 h0)
    have h1 := ZMod.pow_card_sub_one_eq_one hne
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one]
    simpa using sub_eq_zero.2 h1
  intro E hE
  have hEp : ∀ x ∈ E, x ^ p = 1 := hE.2
  have hcastsq : ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one]
  by_cases hdvd : p ∣ Nat.card (adjointGroup .F4 K)
  · obtain ⟨m, hm, hpm⟩ := exists_dvd_phi_of_dvd_card_F4 hp hpK hdvd
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      apply hnd
      have h : (p : ℤ) ∣ (Nat.card K : ℤ) - 1 := by simpa [exhaustionPhi] using hpm
      refine Int.natCast_dvd_natCast.1 ?_
      rw [hcastsq]
      exact h.trans ⟨(Nat.card K : ℤ) + 1, by ring⟩
    · exfalso
      apply hnd
      have h : (p : ℤ) ∣ (Nat.card K : ℤ) + 1 := by simpa [exhaustionPhi] using hpm
      refine Int.natCast_dvd_natCast.1 ?_
      rw [hcastsq]
      exact h.trans ⟨(Nat.card K : ℤ) - 1, by ring⟩
    · refine card_le_sq_of_F4_phiThree K hp hp3 ?_ hEp
      have h : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1 := by
        simpa [exhaustionPhi] using hpm
      exact_mod_cast h
    · refine card_le_sq_of_F4_phiFour K hp hp3 ?_ hEp
      have h : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by simpa [exhaustionPhi] using hpm
      exact_mod_cast h
    · refine card_le_sq_of_F4_phiSix K hp hp3 ?_ hEp
      have h : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1 := by
        simpa [exhaustionPhi] using hpm
      have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow two_ne_zero _
      refine Int.natCast_dvd_natCast.1 ?_
      rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow]
      simpa using h
    · obtain ⟨-, -, hcyc⟩ := F4_eight_cyclic_sylow cyclic_torus_prime_centralizers_F4 K hp hp3 hpm
      obtain ⟨T, -, -, -, -, hQ, -⟩ := hcyc
      exact rankLE2_of_elemAbelian_cyclic hp (fun F hF => hQ F (isPGroup_of_isElemAbelian hF)) E hE
    · obtain ⟨-, -, hcyc⟩ := F4_twelve_cyclic_sylow cyclic_torus_prime_centralizers_F4 K hp hp3 hpm
      obtain ⟨T, -, -, -, -, hQ, -⟩ := hcyc
      exact rankLE2_of_elemAbelian_cyclic hp (fun F hF => hQ F (isPGroup_of_isElemAbelian hF)) E hE
  ·
    have : Fact p.Prime := ⟨hp⟩
    have hfin : Finite (adjointGroup .F4 K) := inferInstance
    obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hE).exists_card_eq
    have hnn : n = 0 := by
      by_contra h
      apply hdvd
      have : p ∣ Nat.card E := by rw [hn]; exact dvd_pow_self p h
      exact this.trans (Subgroup.card_subgroup_dvd_card E)
    rw [hn, hnn]
    simp
    exact Nat.one_le_pow _ _ hp.pos

end F4


section Cat


theorem excPlaneF4Rest : ExcPlaneF4Rest := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨q, rfl, hnd⟩ hr
  exfalso
  apply hr
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp (by simpa using hpd)
  have hnd' : ¬ p ∣ Nat.card K ^ 2 - 1 := by
    rw [hK]
    exact hnd
  exact RankLE2.of_injective e.toMonoidHom e.injective (rankLE2_adjointGroup_F4 K hp hp2 hpK hnd')

theorem excPlaneF4 : ExcPlaneF4 := excPlaneF4_of_parts excPlaneF4Low excPlaneF4Rest

end Cat

end CFSG.LieType.SeitzGeneration
