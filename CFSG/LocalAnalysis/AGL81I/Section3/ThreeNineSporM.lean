module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBigOvergroup
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporMLocal
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporMExtra
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporSieveM
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOp
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporMemoir
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporInner
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporKill
import CFSG.LinearAlgebra.CoprimeActions.BinarySmallAutomorphismOddRank
import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

private theorem commute_of_mem_normalizer_of_pow_five {L : Type} [Group L] [Finite L]
    {V : Subgroup L} {k : ℕ} (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hVp : ∀ v ∈ V, v ^ 7 = 1) (hk : Nat.card V = 7 ^ k) (hk3 : k ≤ 3) {f : L}
    (hf : f ^ 5 = 1) (hfV : f ∈ Subgroup.normalizer (V : Set L)) :
    ∀ v ∈ V, f * v = v * f := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : CFSG.IsElementaryAbelian 7 ↥V :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hVab a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun v =>
        Subtype.ext (by simpa using hVp v v.2) }
  set φ := V.normalizerMonoidHom ⟨f, hfV⟩
  have hφ5 : φ ^ 5 = 1 := by
    rw [← map_pow, show (⟨f, hfV⟩ : Subgroup.normalizer (V : Set L)) ^ 5 = 1 from
      Subtype.ext (by simpa using hf), map_one]
  have hdvd : orderOf φ ∣ ∏ i : Fin k, (7 ^ k - 7 ^ (i : ℕ)) :=
    (orderOf_dvd_natCard φ).trans
      (CFSG.LinearAlgebra.CoprimeActions.BinarySmallAutomorphismOddRank.card_mulAut_dvd_GL hk)
  have h5 : ¬ 5 ∣ ∏ i : Fin k, (7 ^ k - 7 ^ (i : ℕ)) := by
    interval_cases k <;> simp [Fin.prod_univ_succ]
  have hφ1 : φ = 1 := by
    rw [← orderOf_eq_one_iff]
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 (orderOf_dvd_of_pow_eq_one hφ5) with
      h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hdvd) h5
  intro v hv
  have h := congrArg (fun ψ : MulAut ↥V => ((ψ ⟨v, hv⟩ : ↥V) : L)) hφ1
  simp only [φ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h
  calc f * v = f * v * f⁻¹ * f := by group
    _ = v * f := by rw [h]

private theorem factorization_monster_seven' :
    (808017424794512875886459904961710757005754368000000000 : ℕ).factorization 7 = 6 := by
  rw [show (808017424794512875886459904961710757005754368000000000 : ℕ) =
      7 ^ 6 * 6868034788179354485685895374900855570432000000000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

private theorem four_le_pRank_of_lieModel_PSL_four_seven {J : Type} [Group J] [Finite J]
    (h : CFSG.Blueprint.LieModel J .PSL 4 7 1) : 4 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup J) := by
  obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank (by norm_num)
    (h.statedClassicalModel (by decide))
  rcases hcases with ⟨-, ⟨h, -⟩ | ⟨h, -⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
  all_goals first | omega | cases h

section Monster

private theorem card_eq_monster_of_mulEquiv {L : Type} [Group L] (e : L ≃* Carrier .M) :
    Nat.card L = 808017424794512875886459904961710757005754368000000000 := by
  have : IsSimpleGroup (Carrier .M) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.isSimpleGroup_y443Derived
  have : IsSimpleGroup L := MulEquiv.isSimpleGroup e
  obtain ⟨f⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  rw [Nat.card_congr f.toEquiv, CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]
  norm_num [CFSG.Open.monsterOrder]

private theorem exists_orderOf_five_mem_of_data {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .M) {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 7 d Y) :
    ∃ f : L, orderOf f = 5 ∧ f ∈ Y := by
  obtain ⟨Eb, hEb, hcard, hcent, -⟩ := h.barE
  have hne : Eb ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨⟨e₀, he₀⟩, hne₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have he₀1 : e₀ ≠ 1 := fun h1 => hne₀ (Subtype.ext h1)
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({e₀} : Set L)) 5
    (five_dvd_card_centralizer_M_seven e (orderOf_eq_prime (hEb.2 e₀ he₀) he₀1))
  exact ⟨f, by rw [Subgroup.orderOf_coe]; exact hf, hcent e₀ he₀ he₀1 f.2⟩

theorem op_eq_bot_M_nineteen {L : Type} [Group L] [Finite L] (e : L ≃* Carrier .M)
    {Y : Subgroup L} (h : SporOvergroupData L 7 19 Y) :
    ∀ R : Subgroup L, IsPGroup 7 R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥ := by
  intro R hRp hRY hRn
  by_contra hR
  obtain ⟨V, k, z, hVle, hVsub, hVab, hVp, hk, hk1, hk3, hzV, hz, hzdvd, hYdvd⟩ :=
    exists_elem_central_of_normal_pGroup h hRp hRY hRn hR
  have hL : Nat.card L = 808017424794512875886459904961710757005754368000000000 :=
    card_eq_monster_of_mulEquiv e
  rw [hL, factorization_monster_seven'] at hzdvd
  obtain ⟨f, hf, hfY⟩ := exists_orderOf_five_mem_of_data e h
  have hfV : f ∈ Subgroup.normalizer (V : Set L) := by
    refine Subgroup.mem_normalizer_iff.2 fun v => ⟨fun hv => ?_, fun hv => ?_⟩
    · exact hVsub.conj_mem ⟨v, hVle hv⟩ hv ⟨f, hfY⟩
    · have h1 : f⁻¹ * (f * v * f⁻¹) * f⁻¹⁻¹ ∈ V :=
        hVsub.conj_mem ⟨f * v * f⁻¹, hVle hv⟩ hv ⟨f⁻¹, Y.inv_mem hfY⟩
      simpa [mul_assoc] using h1
  have hfc := commute_of_mem_normalizer_of_pow_five hVab hVp hk hk3
    (by rw [← hf]; exact pow_orderOf_eq_one f) hfV
  have hVz : V ≤ Subgroup.zpowers z := fun v hv =>
    mem_zpowers_of_commute_five_M e hz hzdvd hf (hfc z hzV) (hVp v hv) (hVab v hv z hzV)
      (hfc v hv).symm
  have hk1' : k = 1 := by
    have h7 : 7 ^ k ≤ 7 ^ 1 := by
      rw [← hk, pow_one, ← hz, ← Nat.card_zpowers]
      exact Subgroup.card_le_of_le hVz
    have := (Nat.pow_le_pow_iff_right (by norm_num)).1 h7
    omega
  subst hk1'
  have h19 : 19 ∣ Nat.card Y := by
    refine (dvd_pow_self 19 ?_).trans (pow_factorization_dvd_card_of_data h).2
    rw [hL]
    exact (Nat.Prime.factorization_pos_of_dvd (by norm_num) (by norm_num) (by norm_num)).ne'
  have h6 : 19 ∣ 6 * Nat.card (Subgroup.centralizer ({z} : Set L)) := by
    refine h19.trans (hYdvd.trans ?_)
    simp
  exact not_nineteen_dvd_card_centralizer_M e hz hzdvd
    ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h6))

theorem false_M_of_data_of_op_eq_bot {L : Type} [Group L] [Finite L] (e : L ≃* Carrier .M)
    {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 7 d Y)
    (hOp : ∀ R : Subgroup L, IsPGroup 7 R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥) :
    False := by
  have hfact : Fact (Nat.Prime 7) := ⟨h.prime⟩
  have hL : Nat.card L = 808017424794512875886459904961710757005754368000000000 :=
    card_eq_monster_of_mulEquiv e
  have hO7 := gLAPPrimeCoreOf_eq_bot_of_data h (oPrimeCoreTrivialAt_M_seven e)
  obtain ⟨J, hJY, hJn, hJs, hJna, hJC⟩ :=
    exists_simple_normal_of_data h (by norm_num) hO7 hOp (card_center_sylow_M e)
  have hcat : CFSG.Blueprint.Catalog ↥J :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective h.kgroup J (MonoidHom.id ↥J)
      Function.surjective_id
  have hord : Nat.card ↥J ∣ 808017424794512875886459904961710757005754368000000000 := by
    rw [← hL]
    exact Subgroup.card_subgroup_dvd_card J
  obtain ⟨hinn, h75⟩ := m_sieve hcat hJna hord
  obtain ⟨F, hFcard, hFexp⟩ := exists_exponent_seven_M e
  obtain ⟨Q, hQY⟩ := exists_sylow_le_of_data h
  obtain ⟨g, -, hg⟩ := CFSG.RankThree.PartOne.K133H.exists_conj_le_of_sylow (Y := ⊤)
    (H := Q) le_top le_top hFexp (by rw [Subgroup.card_top, Sylow.card_eq_multiplicity,
      Nat.Prime.factorization_pow hfact.out, Finsupp.single_eq_same])
  have hF'exp : ∀ x ∈ F.map (MulAut.conj g).toMonoidHom, x ^ 7 = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hFexp y hy, map_one]
  have hF'J : F.map (MulAut.conj g).toMonoidHom ≤ J := by
    rw [← Subgroup.closure_eq (F.map (MulAut.conj g).toMonoidHom)]
    exact closure_le_of_pow_eq_one hJY hJn hJC hinn
      (S := (F.map (MulAut.conj g).toMonoidHom : Set L)) (hg.trans hQY) hF'exp
  have hdvd : 7 ^ 5 ∣ Nat.card ↥J := by
    rw [← hFcard, ← Subgroup.card_map_of_injective (K := F)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
    exact Subgroup.card_dvd_of_le hF'J
  rcases h75 hdvd with hbig | ⟨-, hJlie⟩
  · have hJtop : J = ⊤ := Subgroup.eq_top_of_card_eq J (hbig.trans hL.symm)
    rw [hJtop] at hJY
    exact h.ne_top (top_le_iff.mp hJY)
  · exact false_of_four_le_pRank_of_data h J (four_le_pRank_of_lieModel_PSL_four_seven hJlie)

theorem sporBigNone_M : SporBigNone .M 7 := by
  intro L _ _ ⟨e⟩ d Y h
  refine false_M_of_data_of_op_eq_bot e h ?_
  by_cases hd : d = 19
  · subst hd
    exact op_eq_bot_M_nineteen e h
  · exact op_eq_bot_of_data h (not_pow_dvd_card_mul_card_centralizer_M e h hd)

end Monster

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
