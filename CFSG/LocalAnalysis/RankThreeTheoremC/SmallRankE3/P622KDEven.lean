module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDDefs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.RankThree.PartOne.KE.SuzukiFinal
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup

@[expose] def KFactSuzukiThreeFree : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → ¬ (∀ a b : J, a * b = b * a) →
    CFSG.Open.IsKGroup J → ¬ 3 ∣ Nat.card J → ∃ f : ℕ, CFSG.Blueprint.SuzukiModel J 2 f

section Suzuki


private theorem card_fix_transport {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (β : MulAut G) (γ : MulAut H) (hγ : ∀ x, γ (e x) = e (β x)) :
    Nat.card ↥(MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id G)) =
      Nat.card ↥(MonoidHom.eqLocus γ.toMonoidHom (MonoidHom.id H)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)
  show β x = x ↔ γ (e x) = e x
  rw [hγ, e.injective.eq_iff]

private theorem five_dvd_sq_two_pow_add_one (b : ℕ) : 5 ∣ (2 ^ (2 * b + 1)) ^ 2 + 1 := by
  have key : ∀ n : ℕ, (2 ^ (2 * n + 1)) ^ 2 % 5 = 4 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have e16 : (2 ^ (2 * (n + 1) + 1)) ^ 2 = 16 * (2 ^ (2 * n + 1)) ^ 2 := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add (2 : ℕ) (2 * n + 1) 2]
        ring
      rw [e16, Nat.mul_mod, ih]
  have h := key b
  generalize (2 ^ (2 * b + 1)) ^ 2 = X at h ⊢
  omega

theorem five_dvd_card_fixed {J : Type} [Group J] [Finite J] {f : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel J 2 f) (hJ3 : ¬ 3 ∣ Nat.card J) (α : MulAut J)
    (hα : orderOf α = 3) :
    5 ∣ Nat.card ↥(MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id J)) := by
  obtain ⟨-, a, ha, K, hKf, hKfin, rfl, hcard, ⟨e⟩⟩ := hSz
  have hαe : ∀ x : J, MulAut.congr e α (e x) = e (α x) := fun x => by simp
  have hα' : orderOf (MulAut.congr e α) = 3 := by
    rw [MulEquiv.orderOf_eq]; exact hα
  have hnotinner :
      MulAut.congr e α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Blueprint.suzukiGroup a K) := by
    intro hmem
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hmem
    have h3g : 3 ∣ orderOf g := by
      have hdvd := orderOf_map_dvd MulAut.conj g
      rw [hg, hα'] at hdvd
      exact hdvd
    have h3J : 3 ∣ Nat.card J := by
      rw [Nat.card_congr e.toEquiv]
      exact h3g.trans (orderOf_dvd_natCard g)
    exact hJ3 h3J
  obtain ⟨σ, h, b, k, _, _, -, -, hk, hconj, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hcard 3 Nat.prime_three
      (by norm_num) (MulAut.congr e α) hα' hnotinner
  have hγ : ∀ x : CFSG.Blueprint.suzukiGroup a K,
      (MulAut.conj h * MulAut.congr e α * (MulAut.conj h)⁻¹) (MulAut.conj h x) =
        MulAut.conj h (MulAut.congr e α x) := by
    intro x
    have hx : (MulAut.conj h)⁻¹ (MulAut.conj h x) = x := by
      rw [MulAut.conj_inv_apply, MulAut.conj_apply]; group
    rw [MulAut.mul_apply, MulAut.mul_apply, hx]
  have hfix : Nat.card ↥(MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id J)) =
      (2 ^ (2 * b + 1)) ^ 2 * (2 ^ (2 * b + 1) - 1) * ((2 ^ (2 * b + 1)) ^ 2 + 1) := by
    rw [card_fix_transport e α (MulAut.congr e α) hαe,
      card_fix_transport (MulAut.conj h : CFSG.Blueprint.suzukiGroup a K ≃*
          CFSG.Blueprint.suzukiGroup a K)
        (MulAut.congr e α) (MulAut.conj h * MulAut.congr e α * (MulAut.conj h)⁻¹) hγ,
      hconj, Nat.card_congr φ.toEquiv, CFSG.LieType.Ree.suzuki_order hk]
  rw [hfix]
  exact Dvd.dvd.mul_left (five_dvd_sq_two_pow_add_one b) _

private theorem ev_b_pow_two_odd_mod_five (n : ℕ) :
    2 ^ (2 * n + 1) % 5 = 2 ∨ 2 ^ (2 * n + 1) % 5 = 3 := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have h : 2 ^ (2 * (k + 1) + 1) = 2 ^ (2 * k + 1) * 4 := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add]
      norm_num
    rw [h]
    omega

private theorem ev_b_factorization_two_suzuki (a : ℕ) :
    Nat.factorization ((2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1)) 2 = 2 * (2 * a + 1) := by
  have hlt : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
  have hev : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
  have hX : (2 ^ (2 * a + 1)) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ two_ne_zero)
  have hY : 2 ^ (2 * a + 1) - 1 ≠ 0 := by omega
  have hZ : (2 ^ (2 * a + 1)) ^ 2 + 1 ≠ 0 := Nat.succ_ne_zero _
  have h1 : ((2 ^ (2 * a + 1)) ^ 2).factorization 2 = (2 * a + 1) * 2 := by
    rw [← pow_mul, Nat.factorization_pow_self Nat.prime_two]
  have h2 : (2 ^ (2 * a + 1) - 1).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    omega
  have h3 : ((2 ^ (2 * a + 1)) ^ 2 + 1).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    have h' : 2 ∣ (2 ^ (2 * a + 1)) ^ 2 := dvd_pow hev two_ne_zero
    omega
  rw [Nat.factorization_mul (mul_ne_zero hX hY) hZ, Nat.factorization_mul hX hY,
    Finsupp.add_apply, Finsupp.add_apply]
  omega

theorem not_five_dvd_normalizer {J : Type} [Group J] [Finite J] {f : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel J 2 f) (T : Sylow 2 J) :
    ¬ 5 ∣ Nat.card ↥(normalizer ((T : Subgroup J) : Set J)) := by
  have hB := CFSG.QuasithinUnique.K1.fusionIsBenderGroup_of_suzukiModel hSz
  obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hB T
  obtain ⟨-, a, -, K, hKf, hKfin, rfl, hcard, ⟨e⟩⟩ := hSz
  have hJ : Nat.card J = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.LieType.Ree.suzuki_order hcard
  have hT : Nat.card (T : Subgroup J) = (2 ^ (2 * a + 1)) ^ 2 := by
    have h := Sylow.card_eq_multiplicity T
    rw [hJ, ev_b_factorization_two_suzuki a] at h
    have e2 : (2 ^ (2 * a + 1)) ^ 2 = 2 ^ (2 * (2 * a + 1)) := by
      rw [← pow_mul, mul_comm (2 * a + 1) 2]
    rw [e2]
    exact h
  haveI : Finite (Sylow 2 J) := Nat.finite_of_card_ne_zero (by rw [hD.card]; omega)
  have hIdx : Nat.card (Sylow 2 J) = (normalizer ((T : Subgroup J) : Set J)).index :=
    Sylow.card_eq_index_normalizer T
  have hIdx' : (normalizer ((T : Subgroup J) : Set J)).index = (2 ^ (2 * a + 1)) ^ 2 + 1 := by
    rw [← hIdx, hD.card, hT]
  have key := Subgroup.card_mul_index (normalizer ((T : Subgroup J) : Set J))
  rw [hIdx', hJ] at key
  have hN : Nat.card ↥(normalizer ((T : Subgroup J) : Set J)) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) :=
    Nat.eq_of_mul_eq_mul_right (show 0 < (2 ^ (2 * a + 1)) ^ 2 + 1 by positivity) key
  rw [hN]
  intro h5
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h5 with h | h
  · have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h
    have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h2
    omega
  · have hm := ev_b_pow_two_odd_mod_five a
    have hlt : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
    omega

theorem le_normalizer_of_suzuki {J : Type} [Group J] [Finite J] [IsSimpleGroup J] {f : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel J 2 f) (T : Sylow 2 J) {M : Subgroup J}
    (hTM : (T : Subgroup J) ≤ M) (hM : M ≠ ⊤) :
    M ≤ normalizer ((T : Subgroup J) : Set J) := by
  obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup
    (CFSG.QuasithinUnique.K1.fusionIsBenderGroup_of_suzukiModel hSz) T
  exact hD.le_normalizer_of_le hTM hM

theorem kFactFieldAutEvenAt_three_of_suzuki (h : KFactSuzukiThreeFree) :
    KFactFieldAutEvenAt 3 := by
  intro J _ _ α T hp3 hα h3 hsimple hnab hK hT _
  obtain ⟨f, hSz⟩ := h J hsimple hnab hK h3
  haveI : IsSimpleGroup J := hsimple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTidx : ¬ 2 ∣ T.index := by
    have h2 := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
    rwa [Subgroup.relIndex_top_right] at h2
  let S : Sylow 2 J := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.1.toSylow hTidx
  have hST : (S : Subgroup J) = T := rfl
  by_contra hne
  have hltop : Subgroup.closure ({g : J | α g = g} ∪ (T : Set J)) ≠ ⊤ := hne
  have hTle : (T : Subgroup J) ≤ Subgroup.closure ({g : J | α g = g} ∪ (T : Set J)) :=
    fun t ht => Subgroup.subset_closure (Or.inr ht)
  have hle := le_normalizer_of_suzuki hSz S (hST ▸ hTle) hltop
  have hfix : MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id J) ≤
      normalizer ((S : Subgroup J) : Set J) := by
    intro g hg
    refine hle (Subgroup.subset_closure (Or.inl ?_))
    simpa using hg
  have hd5 := five_dvd_card_fixed hSz h3 α hα
  exact not_five_dvd_normalizer hSz S (hd5.trans (Subgroup.card_dvd_of_le hfix))

end Suzuki

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
