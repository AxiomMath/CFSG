module

public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.PRank

public section


namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.BorelTits CFSG.Open

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem card_reeLocalParabolic (j : Fin F4.fixedOrbitCount) :
    Nat.card (F4.reeLocalParabolic K a j) = Nat.card (F4.reeFixedBorel K a) *
      (Nat.card (F4.reeFixedOrbitUnipotent K a j) + 1) := by
  have hfin : Finite (ModGL F4.tag K) := finite_modGL
  have hBP : F4.reeFixedBorel K a ≤ F4.reeLocalParabolic K a j :=
    reeFixedBorel_le_reeGamma_inf_parabolicSubgroup _
  have hidx : (F4.reeFixedBorel K a).relIndex (F4.reeLocalParabolic K a j) =
      Nat.card (F4.reeFixedOrbitUnipotent K a j) + 1 := by
    rw [← CFSG.QuasithinUnique.Setup.X6.ncard_image_coset_eq_relIndex]
    change (F4.reeLocalCosets K a j).ncard = _
    rw [ncard_reeLocalCosets]
  have h := Subgroup.relIndex_mul_card (F4.reeFixedBorel K a) (F4.reeLocalParabolic K a j)
  rw [inf_eq_left.2 hBP, hidx] at h
  rw [mul_comm]
  exact h.symm

theorem card_reeLocalParabolic_zero (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (F4.reeLocalParabolic K a ⟨0, by decide⟩) =
      (2 ^ (2 * a + 1)) ^ 12 * (2 ^ (2 * a + 1) - 1) ^ 2 * (2 ^ (2 * a + 1) + 1) := by
  rw [card_reeLocalParabolic, CFSG.RankThree.LargeReeOrder.card_reeFixedBorel hK,
    card_reeFixedOrbitUnipotent_zero hK, hK]

theorem card_reeLocalParabolic_one (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (F4.reeLocalParabolic K a ⟨1, by decide⟩) =
      (2 ^ (2 * a + 1)) ^ 12 * (2 ^ (2 * a + 1) - 1) ^ 2 * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  rw [card_reeLocalParabolic, CFSG.RankThree.LargeReeOrder.card_reeFixedBorel hK,
    card_reeFixedOrbitUnipotent_one hK, hK]

theorem reeParabolic_mono {J J' : Set (Fin F4.fixedOrbitCount)} (h : J ⊆ J') :
    F4.reeParabolic K a J ≤ F4.reeParabolic K a J' :=
  sup_le_sup_left (Subgroup.closure_mono (Set.image_mono h)) _

theorem reeLocalParabolic_sup (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeLocalParabolic K a ⟨0, by decide⟩ ⊔ F4.reeLocalParabolic K a ⟨1, by decide⟩ =
      F4.reeGamma K a := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  have h := (large_Ree_simple_pair_generation a K hK).le
  exact h.trans (sup_le_sup (large_Ree_local_block_Sylow_action F4 a K ⟨0, by decide⟩).1
    (large_Ree_local_block_Sylow_action F4 a K ⟨1, by decide⟩).1)

theorem holds_reeGamma : Holds ↥(F4.reeGamma K a) 2 := by
  have h := holds_reeFixedGroup F4 K a
  rw [← ReeTag.reeGamma_eq_reeFixedGroup (t := F4) (K := K) (a := a)] at h
  exact h

theorem exists_conj_le_reeLocalParabolic (hK : Nat.card K = 2 ^ (2 * a + 1))
    {T : Subgroup ↥(F4.reeGamma K a)} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) :
    ∃ (g : ↥(F4.reeGamma K a)) (j : Fin F4.fixedOrbitCount),
      ∀ x ∈ Subgroup.normalizer (T : Set ↥(F4.reeGamma K a)),
        ((g⁻¹ * x * g : ↥(F4.reeGamma K a)) : ModGL F4.tag K) ∈ F4.reeLocalParabolic K a j := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hfin : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨S, P, hPtop, hNT, -, -, hNS⟩ := holds_reeGamma (K := K) (a := a) T hT hT2
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨S₀, hS₀⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(F4.reeGamma K a) S₀ S
  have hSmem : ∀ x : ↥(F4.reeGamma K a),
      x ∈ (S : Subgroup ↥(F4.reeGamma K a)) ↔ g⁻¹ * x * g ∈ (S₀ : Subgroup ↥(F4.reeGamma K a)) := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  have hS₀mem : ∀ y : ↥(F4.reeGamma K a),
      y ∈ (S₀ : Subgroup ↥(F4.reeGamma K a)) ↔ (y : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a := by
    intro y
    rw [hS₀]
    exact Subgroup.mem_subgroupOf
  have hBΓ : F4.reeFixedBorel K a ≤ F4.reeGamma K a := reeFixedBorel_le_reeGamma
  have hB : ∀ b : ↥(F4.reeGamma K a), (b : ModGL F4.tag K) ∈ F4.reeFixedBorel K a → g * b * g⁻¹ ∈ P := by
    intro b hb
    apply hNS
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hSmem, hSmem]
    have e : g⁻¹ * (g * b * g⁻¹ * y * (g * b * g⁻¹)⁻¹) * g = b * (g⁻¹ * y * g) * b⁻¹ := by group
    rw [e, hS₀mem, hS₀mem]
    have := Subgroup.mem_normalizer_iff.1 (reeFixedBorel_le_normalizer_reeFixedPosUnipotent hb)
      ((g⁻¹ * y * g : ↥(F4.reeGamma K a)) : ModGL F4.tag K)
    simpa using this
  let P' : Subgroup ↥(F4.reeGamma K a) := P.comap (MulAut.conj g).toMonoidHom
  let P'' : Subgroup (ModGL F4.tag K) := P'.map (F4.reeGamma K a).subtype
  have hP''le : P'' ≤ F4.reeGamma K a := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hBP'' : F4.reeFixedBorel K a ≤ P'' := by
    intro b hb
    refine ⟨⟨b, hBΓ hb⟩, ?_, rfl⟩
    show g * (⟨b, hBΓ hb⟩ : ↥(F4.reeGamma K a)) * g⁻¹ ∈ P
    exact hB _ hb
  have hPJ := (ree_Borel_overgroup_classification F4 a K P'' hBP'' hP''le).1
  set J : Set (Fin F4.fixedOrbitCount) :=
    {j | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ P''} with hJ
  have hJne : J ≠ Set.univ := by
    intro hJu
    rw [hJu] at hPJ
    have hj : ∀ j : Fin F4.fixedOrbitCount, F4.reeLocalParabolic K a j ≤ P'' := by
      intro j
      rw [hPJ, ← ReeTag.reeParabolic_singleton]
      exact reeParabolic_mono (Set.subset_univ _)
    have hΓP'' : F4.reeGamma K a ≤ P'' := by
      rw [← reeLocalParabolic_sup hK]
      exact sup_le (hj _) (hj _)
    apply hPtop
    rw [eq_top_iff]
    intro z _
    have hz : ((g⁻¹ * z * g : ↥(F4.reeGamma K a)) : ModGL F4.tag K) ∈ P'' :=
      hΓP'' (g⁻¹ * z * g).2
    obtain ⟨w, hw, hwe⟩ := hz
    have : w = g⁻¹ * z * g := Subtype.ext hwe
    rw [this] at hw
    have h2 : g * (g⁻¹ * z * g) * g⁻¹ ∈ P := hw
    simpa [mul_assoc] using h2
  obtain ⟨k0, hk0⟩ : ∃ k0, k0 ∉ J := by
    by_contra h
    push Not at h
    exact hJne (Set.eq_univ_of_forall h)
  have hcount : ∀ k : Fin F4.fixedOrbitCount, k.val < 2 := fun k => k.2
  obtain ⟨i, hi⟩ : ∃ i : Fin F4.fixedOrbitCount, ∀ j, j ≠ k0 → j = i := by
    refine ⟨⟨1 - k0.val, by have := hcount k0; show 1 - k0.val < 2; omega⟩, fun j hj => ?_⟩
    apply Fin.ext
    have h1 := hcount j
    have h2 := hcount k0
    have h3 : j.val ≠ k0.val := fun h => hj (Fin.ext h)
    show j.val = 1 - k0.val
    omega
  have hJi : J ⊆ {i} := fun j hj => Set.mem_singleton_iff.2 (hi j (fun h => hk0 (h ▸ hj)))
  refine ⟨g, i, fun x hx => ?_⟩
  have hmem : ((g⁻¹ * x * g : ↥(F4.reeGamma K a)) : ModGL F4.tag K) ∈ P'' := by
    refine ⟨g⁻¹ * x * g, ?_, rfl⟩
    show g * (g⁻¹ * x * g) * g⁻¹ ∈ P
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [this]
    exact hNT hx
  rw [← ReeTag.reeParabolic_singleton]
  exact reeParabolic_mono hJi (hPJ ▸ hmem)

theorem exists_isElemAbelian_le_localParabolic (hK : Nat.card K = 2 ^ (2 * a + 1)) {r : ℕ}
    {E T : Subgroup ↥(F4.reeGamma K a)} (hE : IsElemAbelian r E) (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥)
    (hEN : E ≤ Subgroup.normalizer (T : Set ↥(F4.reeGamma K a))) :
    ∃ (j : Fin F4.fixedOrbitCount) (E' : Subgroup (ModGL F4.tag K)),
      E' ≤ F4.reeLocalParabolic K a j ∧ IsElemAbelian r E' ∧ Nat.card E' = Nat.card E := by
  obtain ⟨g, j, hg⟩ := exists_conj_le_reeLocalParabolic hK hT hT2
  let ι : ↥(F4.reeGamma K a) →* ModGL F4.tag K :=
    (F4.reeGamma K a).subtype.comp (MulAut.conj g⁻¹).toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (MulAut.conj g⁻¹).injective
  refine ⟨j, E.map ι, ?_, CFSG.SectionRank.isElemAbelian_map hE ι, Subgroup.card_map_of_injective hι⟩
  rintro _ ⟨x, hx, rfl⟩
  have := hg x (hEN hx)
  simpa [ι, MulAut.conj_apply] using this

end CFSG.LocalAnalysis.GLTheoremA.HDesc
