module

public import CFSG.RankThree.PartOne.KF.ParabolicNormalizes
public import CFSG.Quasithin.Vol2.F134LieD4Cells
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders

section Td4Parity


theorem card_parabolic_singleton_D4 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3) (hσc : ∀ c, σ c = c ^ (p ^ f))
    (a : Fin TwistTag.D4.foldedTag.rank) :
    Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) =
      Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) *
        (1 + (p ^ f) ^ (TwistTag.D4.orbit a).card) := by
  have hsurj : Function.Surjective σ.toRingHom := σ.surjective
  rw [CFSG.Quasithin.F134.LieD4.card_graphFixedParabolic_singleton hsurj a,
    card_graphFixedInversionUnipotent hsurj
      (card_orbitField (t := TwistTag.D4) hp hf hK hσc) (TwistTag.D4.orbitReflection_mem a),
    length_orbitReflection]

theorem card_root_eq_borel_mul_D4 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3) (hσc : ∀ c, σ c = c ^ (p ^ f)) :
    Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) *
        ((1 + (p ^ f) ^ 3) * ((1 + (p ^ f) ^ 4 + (p ^ f) ^ 8) * (1 + p ^ f))) := by
  have hsurj : Function.Surjective σ.toRingHom := σ.surjective
  have hq := card_orbitField (t := TwistTag.D4) (σ := σ.toRingHom) hp hf hK hσc
  have : Fintype (WeylGroup TwistTag.D4.tag) := Fintype.ofFinite _
  have hC := card_graphFixedRootGroup hsurj hq
  rw [sum_length_relWeylTwist_D4, ncard_posRoots_twistedD4] at hC
  rw [hC, card_graphFixedRootBorel hsurj, graphFixedRootTorus_eq_compatTorus hsurj,
    card_graphFixedPosUnipotent hsurj hq, ncard_posRoots_twistedD4]
  simp only [geomSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ring

theorem td4_native_parity {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3) (hσc : ∀ c, σ c = c ^ (p ^ f))
    (S : Sylow p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hP : P ≠ ⊤)
    (hS : Subgroup.normalizer ((S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤ P) :
    ∃ a m : ℕ, Nat.card P ∣ a ∧
      Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = a * m ∧ 2 ∣ m := by
  have : Fact p.Prime := ⟨hp⟩
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3
  have hfin : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hBC : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedRootBorel_le TwistTag.D4 K σ.toRingHom
  have hUp := isPGroup_graphFixedPosUnipotent_subgroupOf p (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom)
  have hUi := not_dvd_index_graphFixedPosUnipotent p (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom) σ.surjective
  have hUc := IsPGroup.toSylow_coe hUp hUi
  have hBN : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤ Subgroup.normalizer
        (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro b hb
    have hb' : (b : ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := hb
    have : b ∈ (Subgroup.normalizer (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
        Set (ModGL TwistTag.D4.tag K))).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent hb'
    rwa [Subgroup.subgroupOf_normalizer_eq hUC] at this
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.KFU.exists_conj_le_of_normalizes (hUp.toSylow hUi) S
    ((graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) P (by rw [hUc]; exact hBN) hS
  have hP₁top : P.comap (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro h
    apply hP
    rw [eq_top_iff]
    intro y _
    have hy : (MulAut.conj g).toMonoidHom ((MulAut.conj g).symm y) ∈ P :=
      Subgroup.mem_comap.1 (h ▸ Subgroup.mem_top _)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hy
  set A : Subgroup (ModGL TwistTag.D4.tag K) :=
    (P.comap (MulAut.conj g).toMonoidHom).map
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype with hA
  have hBA : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ A := fun b hb =>
    ⟨⟨b, hBC hb⟩, hg (show (⟨b, hBC hb⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈
      (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) from hb), rfl⟩
  have hAC : A ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := Subgroup.map_subtype_le _
  obtain ⟨hAJ, -⟩ := fixed_Borel_overgroup_classification TwistTag.D4 K σ A hBA hAC
  set J : Set (Fin TwistTag.D4.foldedTag.rank) :=
    {a | canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∈ A}
    with hJ
  have hJne : J ≠ Set.univ := fun huniv => hP₁top (by
    rw [eq_top_iff]
    intro y _
    have hy : (y : ModGL TwistTag.D4.tag K) ∈ A := by
      rw [hAJ, huniv, (fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.2.2]
      exact y.2
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = y := Subtype.ext hyy
    rwa [← this])
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJne
  have hex : ∀ i : Fin TwistTag.D4.foldedTag.rank, ∃ j : Fin TwistTag.D4.foldedTag.rank,
      ∀ k, k ≠ i → k = j := by decide
  obtain ⟨a, ha⟩ := hex i
  have hsub : J ⊆ {a} := fun k hk => ha k (fun h => hi (h ▸ hk))
  have hle : A ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} := by
    rw [hAJ]
    exact ((fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.1 J {a}).2 hsub
  have hPA : Nat.card P = Nat.card A := by
    have h1 : Nat.card ((P.comap (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom) =
        Nat.card (P.comap (MulAut.conj g).toMonoidHom) :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective] at h1
    rw [h1]
    exact (Subgroup.card_map_of_injective
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).symm
  have hdvd : Nat.card P ∣ Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) := by
    rw [hPA]
    exact Subgroup.card_dvd_of_le hle
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hcardP := card_parabolic_singleton_D4 σ hp hf hK hσc a
  have hcardC := card_root_eq_borel_mul_D4 σ hp hf hK hσc
  have hd : (TwistTag.D4.orbit a).card = 1 ∨ (TwistTag.D4.orbit a).card = 3 := by
    have : ∀ c : Fin TwistTag.D4.foldedTag.rank,
        (TwistTag.D4.orbit c).card = 1 ∨ (TwistTag.D4.orbit c).card = 3 := by decide
    exact this a
  have heven1 : Even (1 + (p ^ f) ^ 3) := by
    rw [add_comm]
    exact (hodd.pow).add_one
  have heven2 : Even (1 + p ^ f) := by
    rw [add_comm]
    exact hodd.add_one
  rcases hd with h1 | h1
  · refine ⟨_, (1 + (p ^ f) ^ 3) * (1 + (p ^ f) ^ 4 + (p ^ f) ^ 8), hdvd, ?_,
      dvd_mul_of_dvd_left (even_iff_two_dvd.1 heven1) _⟩
    rw [hcardC, hcardP, h1]
    ring
  · refine ⟨_, (1 + p ^ f) * (1 + (p ^ f) ^ 4 + (p ^ f) ^ 8), hdvd, ?_,
      dvd_mul_of_dvd_left (even_iff_two_dvd.1 heven2) _⟩
    rw [hcardC, hcardP, h1]
    ring

theorem td4_parity {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (hm : LieModel Y .trialityD4 0 r f) (S : Sylow r Y) (P : Subgroup Y)
    (hP : P ≠ ⊤) (hS : Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≤ P) :
    ∃ a m : ℕ, Nat.card ↥P ∣ a ∧ Nat.card Y = a * m ∧ 2 ∣ m := by
  have : Fact r.Prime := ⟨hr⟩
  have htw : TwistedChevalleyModel Y .D4 (r ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 hr hf htw
  have hP' : P.map e.toMonoidHom ≠ ⊤ := by
    intro h
    apply hP
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, hz, hzy⟩ : e y ∈ P.map e.toMonoidHom := h ▸ Subgroup.mem_top _
    have : z = y := e.injective hzy
    exact this ▸ hz
  have hesurj : Function.Surjective e.toMonoidHom := e.surjective
  have hS' : Subgroup.normalizer
      ((Sylow.mapSurjective hesurj S : Subgroup (graphFixedRootGroup TwistTag.D4 M σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 M σ.toRingHom)) ≤ P.map e.toMonoidHom := by
    rw [Sylow.coe_mapSurjective, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hS
  obtain ⟨a, m, h1, h2, h3⟩ := td4_native_parity σ hr hr2 hf hM hσ
    (Sylow.mapSurjective hesurj S) (P.map e.toMonoidHom) hP' hS'
  refine ⟨a, m, ?_, ?_, h3⟩
  · rwa [Subgroup.card_map_of_injective e.injective] at h1
  · rw [Nat.card_congr e.toEquiv]
    exact h2

end Td4Parity

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
