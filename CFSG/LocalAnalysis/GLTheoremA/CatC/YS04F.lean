module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04Red
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Decode
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinModelAut
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Aux

public section

namespace CFSG.LocalAnalysis.GLTheoremA.YS04F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.GLTheoremA

theorem isElemAbelian_of_le' {G : Type*} [Group G] {p : ℕ} {A B : Subgroup G} (h : A ≤ B)
    (hB : IsElemAbelian p B) : IsElemAbelian p A := by
  haveI := hB.1
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hB.2 x (h hx)⟩
  have := congrArg Subtype.val (mul_comm' (⟨a, h a.2⟩ : ↥B) ⟨b, h b.2⟩)
  exact this

theorem card_le_of_meets_inner {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (I : Subgroup G)
    (h : ∀ D : Subgroup G, IsElemAbelian p D → Nat.card D = p ^ 2 → ∃ x ∈ D ⊓ I, x ≠ 1)
    (D : Subgroup G) (hD : IsElemAbelian p D) :
    Nat.card D ≤ p * Nat.card ↥(D ⊓ I) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨C, hCD, hbot, hsup⟩ :=
    CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma212.exists_complement_of_isElemAbelian hp hD
      (inf_le_left : D ⊓ I ≤ D)
  have hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy => by
    haveI := hD.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥D) ⟨y, hy⟩)
  have hnorm : C ≤ Subgroup.normalizer ((D ⊓ I : Subgroup G) : Set G) := by
    intro c hc
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
    exact hcomm x hx.1 c (hCD hc)
  have hcard : Nat.card D = Nat.card ↥(D ⊓ I) * Nat.card C := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [hbot, Subgroup.card_bot, mul_one, hsup] at h1
    exact h1
  have hC : IsElemAbelian p C := isElemAbelian_of_le' hCD hD
  have hCle : Nat.card C ≤ p := by
    by_contra hlt
    push Not at hlt
    have hpg : IsPGroup p ↥C := fun x => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
      exact hC.2 x x.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
    have hk2 : 2 ≤ k := by
      by_contra hk'
      push Not at hk'
      have : k ≤ 1 := by omega
      have : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos this
      rw [← hk, pow_one] at this
      omega
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp hpg
      (n := 2) (by rw [hk]; exact Nat.pow_le_pow_right hp.pos hk2)
    set D₂ : Subgroup G := H.map C.subtype with hD₂
    have hD₂card : Nat.card D₂ = p ^ 2 := by
      rw [hD₂, Subgroup.card_map_of_injective C.subtype_injective, hH]
    have hD₂le : D₂ ≤ C := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    obtain ⟨x, hx, hx1⟩ := h D₂ (isElemAbelian_of_le' hD₂le hC) hD₂card
    have hxbot : x ∈ (D ⊓ I) ⊓ C :=
      ⟨⟨hCD (hD₂le hx.1), hx.2⟩, hD₂le hx.1⟩
    rw [hbot, Subgroup.mem_bot] at hxbot
    exact hx1 hxbot
  rw [hcard]
  calc Nat.card ↥(D ⊓ I) * Nat.card C ≤ Nat.card ↥(D ⊓ I) * p := Nat.mul_le_mul_left _ hCle
    _ = p * Nat.card ↥(D ⊓ I) := mul_comm _ _

theorem kd26f_psl {S : Type} [Group S] [Finite S] {n q p : ℕ}
    (hS : IsLnEps S n q true) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpg : p ∣ Nat.gcd n (qEps true q)) (hg : ¬ p ^ 2 ∣ Nat.gcd n (qEps true q))
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian p D) :
    Nat.card D ≤ p * Nat.card ↥(D ⊓ inner S) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left _ _)
  obtain ⟨m, F, _, _, hmn, hFq, ⟨e0⟩⟩ := exists_psl_of_isLnEps hS
  subst hmn
  have hn3 : 3 ≤ m + 1 := hp3.trans (Nat.le_of_dvd (by omega) hpn)
  obtain ⟨r, f, hr, hf, hFrf⟩ : ∃ r f : ℕ, r.Prime ∧ 0 < f ∧ Nat.card F = r ^ f := by
    haveI := Fintype.ofFinite F
    obtain ⟨n, hp', hn⟩ := FiniteField.card F (ringChar F)
    exact ⟨ringChar F, n, hp', n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hqr : q = r ^ f := by rw [← hFq, hFrf]
  have hqE : qEps true q = r ^ f - 1 := by simp [qEps, hqr]
  rw [hqE] at hpg hg
  have hadm : StatedLieAdmissible .PSL (m + 1) r f := by
    refine ⟨hr, hf, by omega, ?_, ?_⟩ <;>
    · intro h
      have := congrArg Prod.fst h
      simp only at this
      omega
  have hm : StatedClassicalModel S .PSL (m + 1) r f :=
    ⟨hadm, F, inferInstance, inferInstance, hFrf,
      ⟨e0.trans (projectiveSpecialLinearGroupEquivStatedProj (m + 1) F)⟩⟩
  refine card_le_of_meets_inner hp (inner S) (fun D hD hc => ?_) D hD
  exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.meets_inner_of_psl_model hm hn3 hp hp2 hpg hg D
    hD hc

theorem kd26f_psu {S : Type} [Group S] [Finite S] {n q p : ℕ}
    (hS : IsLnEps S n q false) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpg : p ∣ Nat.gcd n (qEps false q)) (hg : ¬ p ^ 2 ∣ Nat.gcd n (qEps false q))
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian p D) :
    Nat.card D ≤ p * Nat.card ↥(D ⊓ inner S) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left _ _)
  obtain ⟨m, ℓ, f, F, _, hU, hmn, hℓq, h3, ⟨e0⟩⟩ := exists_psu_of_isLnEps hS
  subst hmn
  subst hℓq
  have hn3 : 3 ≤ m + 1 := hp3.trans (Nat.le_of_dvd (by omega) hpn)
  have hqE : qEps false (ℓ ^ f) = ℓ ^ f + 1 := by simp [qEps]
  rw [hqE] at hpg hg
  have hadm : StatedLieAdmissible .PSU (m + 1) ℓ f := by
    refine ⟨hU.prime, hU.one_le, hn3, ?_⟩
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    have := h3 (by omega)
    omega
  have hm : StatedClassicalModel S .PSU (m + 1) ℓ f :=
    ⟨hadm, F, inferInstance, hU.finite, by rw [hU.card, ← pow_mul, mul_comm], ⟨e0⟩⟩
  refine card_le_of_meets_inner hp (inner S) (fun D hD hc => ?_) D hD
  exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.meets_inner_of_psu_model hm hp hp2 hpg hg D hD hc

@[expose] def KD26fE6 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ (q : ℕ) (lin : Bool), IsE6Eps S q lin → 3 ∣ qEps lin q →
      ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D → Nat.card D ≤ 3 * Nat.card ↥(D ⊓ inner S)

theorem kd26fSimple_of_E6 (hE6 : KD26fE6) : KD26fSimple := by
  intro S _ _ hs hna p hp hp2 hhyp D hD
  rcases hhyp with ⟨n, q, lin, hS, hpg, hg⟩ | ⟨q, lin, hS, hp3, h3⟩
  · cases lin
    · exact kd26f_psu hS hp hp2 hpg hg D hD
    · exact kd26f_psl hS hp hp2 hpg hg D hD
  · subst hp3
    exact hE6 S hs hna q lin hS h3 D hD

end CFSG.LocalAnalysis.GLTheoremA.YS04F
