module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Sections
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Reduced

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.ComponentClassification.OuterAutomorphisms Subgroup

variable {K : Type} [Group K] [Finite K] {n p : ℕ} {P : Sylow p K} {z : K} {D : Subgroup K}

namespace Red

theorem moves_all (R : Red n p K P z D) {w : K} (hw : w ∈ D) {C₀ : ComponentIndex K}
    (hmove : w • C₀ ≠ C₀) (C : ComponentIndex K) : w • C ≠ C := by
  obtain ⟨j, rfl⟩ := R.orbit_eq hw hmove C
  intro h
  have h1 : w ^ (j + 1) • C₀ = w ^ j • C₀ := by
    rw [pow_succ', mul_smul]
    exact h
  have h2 := R.pow_smul_eq hw hmove h1
  have h3 : j + 1 ≡ j + 0 [MOD p] := h2
  have h4 := Nat.ModEq.add_left_cancel' j h3
  have h5 : p ∣ 1 := Nat.modEq_zero_iff_dvd.1 h4
  exact R.prime.one_lt.ne' (Nat.dvd_one.1 h5)

theorem card_comp (R : Red n p K P z D) {w : K} (hw : w ∈ D) {C₀ : ComponentIndex K}
    (hmove : w • C₀ ≠ C₀) : Fintype.card (ComponentIndex K) = p := by
  have hwp : w ^ p = 1 := R.conf.elem.2 w hw
  have hbij : Function.Bijective (fun j : Fin p => w ^ (j : ℕ) • C₀) := by
    constructor
    · intro i j h
      have := R.pow_smul_eq hw hmove h
      rw [Nat.ModEq, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at this
      exact Fin.ext this
    · intro C
      obtain ⟨j, hj⟩ := R.orbit_eq hw hmove C
      refine ⟨⟨j % p, Nat.mod_lt _ R.prime.pos⟩, ?_⟩
      show w ^ (j % p) • C₀ = C
      rw [← pow_eq_pow_mod j hwp]
      exact hj
  rw [← Fintype.card_fin p]
  exact (Fintype.card_of_bijective hbij).symm

theorem exists_diag_section (R : Red n p K P z D) {w : K} (hw : w ∈ D) {C : ComponentIndex K}
    (hmove : w • C ≠ C) :
    ∃ (U : Subgroup K) (f : U →* C.1), U ≤ centralizer ({w} : Set K) ∧
      Function.Surjective f := by
  let U : Subgroup K := centralizer ({w} : Set K) ⊓ layer K
  let f : U →* C.1 := (coord R.hZ C).comp (Subgroup.inclusion (inf_le_right : U ≤ layer K))
  refine ⟨U, f, inf_le_left, fun c => ?_⟩
  obtain ⟨y, hy, hwy, hcoord, -, -⟩ := R.exists_diag hw hmove c.2
  have hyw : y * w = w * y := (mul_inv_eq_iff_eq_mul.1 hwy).symm
  have hyU : y ∈ U := ⟨mem_centralizer_singleton_iff.2 hyw, hy⟩
  refine ⟨⟨y, hyU⟩, Subtype.ext ?_⟩
  have h0 := hcoord 0
  simp only [pow_zero, one_smul, one_mul, inv_one, mul_one] at h0
  exact h0

theorem involvedInSymm_comp (R : Red n p K P z D)
    (hOut : ∀ C : ComponentIndex K, Group.IsSolvable (Outer C.1))
    (hemb : CentralizerSectionEmbeds p D z) {w : K} (hw : w ∈ D) {C₀ : ComponentIndex K}
    (hmove : w • C₀ ≠ C₀) (C : ComponentIndex K) : InvolvedInSymm p C.1 := by
  haveI := R.fact
  have hall := R.moves_all hw hmove
  obtain ⟨hsimple, hnonab⟩ := R.isSimpleGroup_comp C
  haveI := hsimple
  obtain ⟨U, f, hU, hf⟩ := R.exists_diag_section hw (hall C)
  obtain ⟨U', f', hU', hf'⟩ := hemb w hw (R.not_mem_zpowers hw (hall C)) C.1
    (dvd_card_comp R.core C) ⟨U, f, hU, hf⟩
  exact R.involvedInSymm_of_section hOut hw hall (R.card_comp hw hmove) hnonab
    (dvd_card_comp R.core C) U' hU' f' hf'

theorem caseB (hB : GL83I203Sigma) (R : Red n p K P z D) (h5 : 5 ≤ p)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections K)
    (hOut : ∀ C : ComponentIndex K, Group.IsSolvable (Outer C.1))
    (hemb : CentralizerSectionEmbeds p D z) {w : K} (hw : w ∈ D) {C₀ : ComponentIndex K}
    (hmove : w • C₀ ≠ C₀) :
    ∀ T : Subgroup K, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set K) → T = ⊥ := by
  intro T hT hDT
  haveI := R.fact
  have hcard := R.card_comp hw hmove
  have hTY : T ≤ (actHom K).ker := by
    have hbot : T.map (actHom K) = ⊥ := by
      refine eq_bot_of_pCycle_mem_normalizer R.prime hcard (c := actHom K w) ?_ ?_ ?_ ?_
      · intro h1
        exact hmove (mem_ker_actHom.1 (MonoidHom.mem_ker.2 h1) C₀)
      · rw [← map_pow, R.conf.elem.2 w hw, map_one]
      · exact hT.coprime_dvd_right (Subgroup.card_map_dvd T (actHom K))
      · exact Subgroup.le_normalizer_map (actHom K) ⟨w, hDT hw, rfl⟩
    intro t ht
    have : actHom K t ∈ T.map (actHom K) := Subgroup.mem_map_of_mem _ ht
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hcent : ∀ t ∈ T, ∀ C : ComponentIndex K, ∀ c ∈ C.1, t * c * t⁻¹ = c := by
    intro t ht C c hc
    obtain ⟨hsimple, hnonab⟩ := R.isSimpleGroup_comp C
    haveI := hsimple
    have hcatC : IsCatalogGroup C.1 := hcat.simple_subgroup C.1 hsimple hnonab
    have hTN : T ≤ normalizer (C.1 : Set K) := hTY.trans (ker_actHom_le_normalizer C)
    let H : Subgroup (normalizer (C.1 : Set K)) := T.subgroupOf (normalizer (C.1 : Set K))
    let A : Subgroup (MulAut C.1) := H.map C.1.normalizerMonoidHom
    have hAcop : p.Coprime (Nat.card A) := by
      have h1 : Nat.card A ∣ Nat.card H := Subgroup.card_map_dvd H _
      have h2 : Nat.card H = Nat.card T :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
      rw [h2] at h1
      exact hT.coprime_dvd_right h1
    let x : C.1 := ⟨R.zc C, R.zc_mem C⟩
    have hx : orderOf x = p :=
      orderOf_eq_prime (Subtype.ext (R.zc_pow C)) (fun h => R.zc_ne_one C (congrArg Subtype.val h))
    let z' : normalizer (C.1 : Set K) := ⟨z, R.z_mem_normalizer C⟩
    have hz'ρ : C.1.normalizerMonoidHom z' = MulAut.conj x := by
      refine MulEquiv.ext fun c => Subtype.ext ?_
      exact R.z_conj_eq C c.2
    have hz'N : z' ∈ normalizer (H : Set (normalizer (C.1 : Set K))) := by
      have h1 : (normalizer (T : Set K)).subgroupOf (normalizer (C.1 : Set K)) =
          normalizer (H : Set (normalizer (C.1 : Set K))) := Subgroup.subgroupOf_normalizer_eq hTN
      rw [← h1]
      exact Subgroup.mem_subgroupOf.2 (hDT R.conf.mem)
    have hAnorm : MulAut.conj x ∈ normalizer (A : Set (MulAut C.1)) := by
      rw [← hz'ρ]
      exact Subgroup.le_normalizer_map C.1.normalizerMonoidHom ⟨z', hz'N, rfl⟩
    have hAbot : A = ⊥ := hB p R.prime h5 C.1 hnonab hcatC (dvd_card_comp R.core C)
      (R.involvedInSymm_comp hOut hemb hw hmove C) x hx A hAcop hAnorm
    have htA : C.1.normalizerMonoidHom ⟨t, hTN ht⟩ ∈ A :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht)
    rw [hAbot, Subgroup.mem_bot] at htA
    have h3 := congrArg (fun a : MulAut C.1 => ((a ⟨c, hc⟩ : C.1) : K)) htA
    exact h3
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  refine R.eq_one_of_mem_centralizer_layer (mem_centralizer_layer_of_forall t fun C c hc => ?_)
  exact mul_inv_eq_iff_eq_mul.1 (hcent t ht C c hc)

end Red

end CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
