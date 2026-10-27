module

public import CFSG.LieType.SeitzGeneration.SpBlockPlanes
public import CFSG.LieType.SeitzGeneration.InnerSymplectic
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCSpFull (coprime_card_ker_proj)
open scoped MatrixGroups

section Model

variable {r : ℕ} {K : Type} [Field K]

theorem exists_proj_block_plane [Finite K] (hr : 3 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (A : SL(2, K)) (hA : orderOf A = p) :
    ∃ E : Subgroup (StatedProj (StatedSp r K)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      Subgroup.closure {k : StatedProj (StatedSp r K) | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  obtain ⟨E, hE, hc, hgen⟩ := exists_block_plane hr hp A hA
  have hker : Nat.Coprime (Nat.card (proj r K).ker) p :=
    coprime_card_ker_proj (r := r) (K := K) (by omega) hp hp2
  have hEker : ∀ x ∈ E, proj r K x = 1 → x = 1 := by
    intro x hx hπ
    have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hE.2 x hx)
    have h2 : orderOf x ∣ Nat.card (proj r K).ker := by
      let y : (proj r K).ker := ⟨x, hπ⟩
      calc orderOf x = orderOf y := Subgroup.orderOf_coe y
        _ ∣ Nat.card (proj r K).ker := orderOf_dvd_natCard y
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hker h2 h1)
  have hinj : Function.Injective ((proj r K).comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ h
    exact Subtype.ext (hEker x hx (by simpa using h))
  refine ⟨E.map (proj r K), CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _,
    ?_, ?_⟩
  · have hrange : ((proj r K).comp E.subtype).range = E.map (proj r K) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← hc]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  · rw [eq_top_iff]
    intro k _
    obtain ⟨g, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective
      (r := r) (K := K) k
    have hg : g ∈ Subgroup.closure {g : StatedSp r K | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} := by
      rw [hgen]
      trivial
    have hle : (Subgroup.closure {g : StatedSp r K | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g}).map
        (proj r K) ≤ Subgroup.closure {k : StatedProj (StatedSp r K) |
          ∃ x ∈ E.map (proj r K), x ≠ 1 ∧ k * x = x * k} := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g', ⟨x, hx, hx1, hcomm⟩, rfl⟩
      refine Subgroup.subset_closure ⟨proj r K x, Subgroup.mem_map_of_mem _ hx, ?_, ?_⟩
      · intro h
        exact hx1 (hEker x hx h)
      · rw [← map_mul, ← map_mul, hcomm]
    exact hle ⟨g, hg, rfl⟩

end Model

theorem exists_planeGen_of_model {K P : Type*} [Group K] [Group P] {p : ℕ}
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) (e : K ≃* P) {E₁ : Subgroup P}
    (hE₁ : IsElemAbelian p E₁) (hc : Nat.card E₁ = p ^ 2)
    (hgen : Subgroup.closure {k' : P | ∃ x ∈ E₁, x ≠ 1 ∧ k' * x = x * k'} = ⊤) :
    ∃ E : Subgroup (MulAut K), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      E ≤ (MulAut.conj : K →* MulAut K).range ∧ PlaneGen E := by
  set E₀ : Subgroup K := E₁.map e.symm.toMonoidHom with hE₀
  have hE₀el : IsElemAbelian p E₀ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₁ _
  have hE₀card : Nat.card E₀ = p ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective e.symm.injective, hc]
  have hmap : E₀.map e.toMonoidHom = E₁ := by
    rw [hE₀, Subgroup.map_map]
    have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id P := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  refine ⟨E₀.map (MulAut.conj : K →* MulAut K),
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀el _, ?_,
    Subgroup.map_le_range _ _, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hE₀card]
  · have hle : (⊤ : Subgroup P) ≤
        (Subgroup.closure {k : K | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k}).map e.toMonoidHom := by
      rw [MonoidHom.map_closure, ← hgen]
      refine Subgroup.closure_mono ?_
      rintro k' ⟨x, hx, hx1, hk⟩
      rw [← hmap] at hx
      obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.1 hx
      refine ⟨e.symm k', ⟨x₀, hx₀, ?_, ?_⟩, by simp⟩
      · rintro rfl
        exact hx1 (map_one _)
      · apply e.injective
        simp only [map_mul, MulEquiv.apply_symm_apply]
        exact hk
    have h2 : Subgroup.closure {k : K | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
      rw [eq_top_iff]
      intro k _
      obtain ⟨c, hc', hck⟩ := hle (Subgroup.mem_top (e k))
      exact (e.injective hck) ▸ hc'
    rw [PlaneGen, eq_top_iff, ← h2, Subgroup.closure_le]
    intro k ⟨x, hx, hx1, hk⟩
    refine mem_planeClosure_of_fixed (E := E₀.map (MulAut.conj : K →* MulAut K))
      (e := MulAut.conj x) (Subgroup.mem_map_of_mem _ hx) ?_ ?_
    · intro h
      exact hx1 (hinj (by simpa using h))
    · rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
      exact hk.symm

theorem three_dvd_sq_sub_one {N : ℕ} (h : ¬ 3 ∣ N) : 3 ∣ N ^ 2 - 1 := by
  have h1 : N ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    have : N % 3 = 1 ∨ N % 3 = 2 := by omega
    rcases this with h2 | h2 <;> simp [h2]
  have := Nat.sub_mod_eq_zero_of_mod_eq (show N ^ 2 % 3 = 1 % 3 by simpa using h1)
  exact Nat.dvd_of_mod_eq_zero this

theorem innerEx_psp_model {d : TauCeti.ValidLieTypeIndex} {r ℓ f p : ℕ} {K : Type} [Field K]
    (e : Cat d ≃* StatedProj (StatedSp r K)) (hℓ : ℓ.Prime)
    (hK : Nat.card K = ℓ ^ f) (hr : 3 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K ^ 2 - 1)
    (hex : ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E) :
    ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E ∧ PlaneGen E := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have hKge : 2 ≤ Nat.card K := Finite.one_lt_card
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r (by omega) (by
      by_cases h4 : 4 ≤ Nat.card K
      · exact Or.inl (Or.inr h4)
      · right
        have h2 : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
        rcases h2 with h2 | h2
        · exact Or.inr ⟨h2, hr⟩
        · exact Or.inl ⟨h2, by omega⟩)
  have : IsSimpleGroup (Cat d) := MulEquiv.isSimpleGroup e
  obtain ⟨E₀, -, hc₀, hinn₀⟩ := hex
  have hinj : Function.Injective (MulAut.conj : Cat d →* MulAut (Cat d)) :=
    conj_injective_of_simple_of_range_ne_bot (range_conj_ne_bot_of_inner hp hc₀ hinn₀)
  have hdvd : p ∣ Nat.card (SL(2, K)) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    exact Dvd.dvd.mul_left hpq _
  obtain ⟨A, hA⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨E₁, he, hc, hgen⟩ := exists_proj_block_plane hr hp hp2 A hA
  obtain ⟨E, hE, hcE, hinner, hPG⟩ := exists_planeGen_of_model hinj e he hc hgen
  exact ⟨E, hE, hcE, hinner, hPG⟩

@[expose] def IsSymplecticHigh (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ (r : ℕ) (q : TauCeti.PrimePower), d = .B r q ∧ 3 ≤ r ∧ q.p = 2) ∨
    ∃ (r : ℕ) (q : TauCeti.PrimePower), d = .C r q

theorem innerEx_symplecticHigh_three :
    ∀ (d : TauCeti.ValidLieTypeIndex), IsSymplecticHigh d.1 → ∀ p : ℕ, p = 3 →
      p ≠ d.1.characteristic → ¬ IsD2SeitzException p d.1 →
      (∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        InnerPlane d p E) →
      ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        InnerPlane d p E ∧ PlaneGen E := by
  rintro ⟨d, hv⟩ hsp p hp3 hpd hex hE
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  subst hp3
  rcases hsp with ⟨r, q, rfl, hr3, hq2⟩ | ⟨r, q, rfl⟩
  · have hq : 3 ≠ q.p := by simpa using hpd
    have hpq : 3 ∣ Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) ^ 2 - 1 := by
      rw [CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv]
      refine three_dvd_sq_sub_one fun h => hq ?_
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
        (Nat.prime_three.dvd_of_dvd_pow h))
    exact innerEx_psp_model (d := ⟨.B r q, hv⟩)
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3)
      q.prime_p (CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv) hr3
      Nat.prime_three (by norm_num) hpq hE
  · have hq : 3 ≠ q.p := by simpa using hpd
    have hr3 : 3 ≤ r := hrange.1
    have hpq : 3 ∣ Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩) ^ 2 - 1 := by
      rw [card_fixedField_C r q hv]
      refine three_dvd_sq_sub_one fun h => hq ?_
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
        (Nat.prime_three.dvd_of_dvd_pow h))
    exact innerEx_psp_model (d := ⟨.C r q, hv⟩)
      (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
      q.prime_p (card_fixedField_C r q hv) hr3 Nat.prime_three (by norm_num) hpq hE

end CFSG.LieType.SeitzGeneration
