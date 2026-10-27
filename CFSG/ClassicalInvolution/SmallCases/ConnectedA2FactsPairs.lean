module

public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2FactsMain
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyRows
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open scoped MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Linear

open CFSG.ClassicalInvolution.WeakCT

variable {F : Type} [Field F] [Finite F] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {S : Set (Subgroup G)}

theorem linearA2Pair_of_normalized (Fr : RankFrame F Ω A S) {K' L' : Subgroup G} (hK' : K' ∈ S)
    (hL' : L' ∈ S) {θ : SL(3, F) →* G} (hker : θ.ker ≤ Subgroup.center SL(3, F))
    (hK : (B12 F).map θ = K') (hL : (B23 F).map θ = L') : LinearA2Pair F A K' L' := by
  have hodd := Fr.odd
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hm1 : (-1 : Fˣ) ≠ 1 := fun h => h2 (by
    have := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this)
  have hinj₀ : Function.Injective (θ.comp (blockSL F 3 2 0 (by omega))) :=
    comp_blockSL_injective hker (by omega) (by omega)
  have hinj₁ : Function.Injective (θ.comp (blockSL F 3 2 1 (by omega))) :=
    comp_blockSL_injective hker (by omega) (by omega)
  have htsq : torusHom F (-1) * torusHom F (-1) = 1 := by
    rw [← map_mul, neg_mul_neg, one_mul, map_one]
  obtain ⟨wK, hwK⟩ := Fr.exists_isUniqueInvolution hK'
  obtain ⟨wL, hwL⟩ := Fr.exists_isUniqueInvolution hL'
  have hzK : θ (blockSL F 3 2 0 (by omega) (torusHom F (-1))) = wK := by
    have hmem : θ (blockSL F 3 2 0 (by omega) (torusHom F (-1))) ∈ K' := by
      rw [← hK]
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    have hsq : θ (blockSL F 3 2 0 (by omega) (torusHom F (-1))) *
        θ (blockSL F 3 2 0 (by omega) (torusHom F (-1))) = 1 := by
      rw [← map_mul, ← map_mul, htsq, map_one, map_one]
    rcases hwK.unique _ hmem hsq with h | h
    · exfalso
      have h1 := hinj₀ (show (θ.comp (blockSL F 3 2 0 (by omega))) (torusHom F (-1)) =
        (θ.comp (blockSL F 3 2 0 (by omega))) 1 by simpa using h)
      exact hm1 (torusHom_injective (h1.trans (map_one _).symm))
    · exact h
  have hzL : θ (blockSL F 3 2 1 (by omega) (torusHom F (-1))) = wL := by
    have hmem : θ (blockSL F 3 2 1 (by omega) (torusHom F (-1))) ∈ L' := by
      rw [← hL]
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    have hsq : θ (blockSL F 3 2 1 (by omega) (torusHom F (-1))) *
        θ (blockSL F 3 2 1 (by omega) (torusHom F (-1))) = 1 := by
      rw [← map_mul, ← map_mul, htsq, map_one, map_one]
    rcases hwL.unique _ hmem hsq with h | h
    · exfalso
      have h1 := hinj₁ (show (θ.comp (blockSL F 3 2 1 (by omega))) (torusHom F (-1)) =
        (θ.comp (blockSL F 3 2 1 (by omega))) 1 by simpa using h)
      exact hm1 (torusHom_injective (h1.trans (map_one _).symm))
    · exact h
  have hwKA : wK ∈ A := Fr.mem_of_isUniqueInvolution hK' hwK
  have hwLA : wL ∈ A := Fr.mem_of_isUniqueInvolution hL' hwL
  have hcard₀ : Nat.card ((D12 F).map θ) = Nat.card F - 1 := by
    rw [map_D12, Subgroup.card_map_of_injective hinj₀, card_diagTorus2_linear]
  have hcard₁ : Nat.card ((D23 F).map θ) = Nat.card F - 1 := by
    rw [map_D23, Subgroup.card_map_of_injective hinj₁, card_diagTorus2_linear]
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hcK : centPart K' A ≤ (D12 F).map θ := by
    intro k hk
    obtain ⟨hkK, hkC⟩ := mem_centPart_iff.mp hk
    rw [← hK] at hkK
    obtain ⟨b, ⟨B, rfl⟩, rfl⟩ := hkK
    have hc := hkC wL hwLA
    have hB : B ∈ diagTorus2 F := mem_diagTorus2_of_map_commute_zero hker hm1 (A := B)
      (by rw [hzL]; exact hc.symm)
    rw [map_D12]
    exact ⟨B, hB, rfl⟩
  have hcL : centPart L' A ≤ (D23 F).map θ := by
    intro k hk
    obtain ⟨hkK, hkC⟩ := mem_centPart_iff.mp hk
    rw [← hL] at hkK
    obtain ⟨b, ⟨B, rfl⟩, rfl⟩ := hkK
    have hc := hkC wK hwKA
    have hB : B ∈ diagTorus2 F := mem_diagTorus2_of_map_commute_one hker hm1 (A := B)
      (by rw [hzK]; exact hc.symm)
    rw [map_D23]
    exact ⟨B, hB, rfl⟩
  refine ⟨θ, hker, hK, hL, ?_, ?_⟩
  · obtain ⟨-, η, hη, hcardK⟩ := (Fr.inSigma hK').isCyclic_and_card_centPart hodd
    have hle := Subgroup.card_le_of_le hcK
    refine Subgroup.eq_of_le_of_card_ge hcK ?_
    rcases hη with rfl | rfl <;> omega
  · obtain ⟨-, η, hη, hcardK⟩ := (Fr.inSigma hL').isCyclic_and_card_centPart hodd
    have hle := Subgroup.card_le_of_le hcL
    refine Subgroup.eq_of_le_of_card_ge hcL ?_
    rcases hη with rfl | rfl <;> omega

theorem linearPair_of_standardPair (Fr : RankFrame F Ω A S) {K' L' : Subgroup G} (hK' : K' ∈ S)
    (hL' : L' ∈ S) {W : Subgroup G} (h : LinearBlockStandardPair F W K' L') :
    LinearPair F A K' L' := by
  obtain ⟨θ, c, -, hker, hcases⟩ := h
  let θ' : SL(3, F) →* G := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  have hker' : θ'.ker ≤ Subgroup.center SL(3, F) := by
    intro x hx
    have h1 : (MulAut.conj c⁻¹).toMonoidHom x ∈ θ.ker := hx
    have h2 := hker h1
    have h3 := (inferInstance : (Subgroup.center SL(3, F)).Normal).conj_mem _ h2 c
    simpa [mul_assoc] using h3
  have hB : ∀ B : Subgroup SL(3, F), B.map θ' = (B.map (MulAut.conj c⁻¹).toMonoidHom).map θ :=
    fun B => by rw [Subgroup.map_map]
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (linearA2Pair_of_normalized Fr hK' hL' hker' (by rw [hB]; exact h1)
      (by rw [hB]; exact h2))
  · exact Or.inr (linearA2Pair_of_normalized Fr hL' hK' hker' (by rw [hB]; exact h1)
      (by rw [hB]; exact h2))

end Linear

section Unitary

open CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan

variable {K₀ : Type} [Field K₀] [Finite K₀] {p f : ℕ} [Fact p.Prime] [CharP K₀ p]
  {F : Type} [Field F] [Finite F] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {S : Set (Subgroup G)}

omit [Finite G] in
theorem eq_of_le_card_unitary {q : ℕ} {T C : Subgroup G} (hq : 5 ≤ q) [Finite T]
    (hT : Nat.card T = q + 1) (hle : C ≤ T) (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hcard : (Nat.card C : ℤ) = q - η) : C = T := by
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rcases hη with rfl | rfl
  · exfalso
    have hC : Nat.card C = q - 1 := by omega
    have hdvd : q - 1 ∣ q + 1 := hC ▸ hT ▸ Subgroup.card_dvd_of_le hle
    have h2 : q - 1 ∣ 2 := by
      refine (Nat.dvd_add_right (dvd_refl (q - 1))).mp ?_
      rw [show q - 1 + 2 = q + 1 by omega]
      exact hdvd
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · omega

theorem unitaryA2Pair_of_normalized (hp2 : p ≠ 2) (hK : Nat.card K₀ = (p ^ f) ^ 2)
    (hF : Nat.card F = p ^ f) (h5 : 5 ≤ p ^ f) (Fr : RankFrame F Ω A S) {P Q : Subgroup G}
    (hP : P ∈ S) (hQ : Q ∈ S) {θ : Su K₀ p f 3 →* G}
    (hker : θ.ker ≤ Subgroup.center (Su K₀ p f 3)) (hPθ : (Phan.B12 K₀ p f).map θ = P)
    (hQθ : (Phan.B23 K₀ p f).map θ = Q) : UnitaryA2Pair K₀ p f A P Q := by
  have hodd := Fr.odd
  have h2 : (2 : K₀) ≠ 0 := CFSG.LieType.BorelTits.two_ne_zero_of_charP_ne_two p hp2
  have h5' : 5 ≤ Nat.card F := by rw [hF]; exact h5
  obtain ⟨sneg, hsneg⟩ : ∃ s : normOne (unitaryInvolution K₀ p f), (s : K₀ˣ) = -1 :=
    ⟨⟨-1, (mem_normOne _).mpr (by simp)⟩, rfl⟩
  have hs1 : (sneg : K₀ˣ) ≠ 1 := fun h => h2 (by
    rw [hsneg] at h
    have := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this)
  have hinj₂ : Function.Injective (θ.comp (embSUid (unitaryInvolution K₀ p f) 2)) :=
    comp_embSUid_injective hK hker 2
  have hinj₀ : Function.Injective (θ.comp (embSUid (unitaryInvolution K₀ p f) 0)) :=
    comp_embSUid_injective hK hker 0
  have htsq : torusTwo (unitaryInvolution K₀ p f) sneg * torusTwo (unitaryInvolution K₀ p f) sneg
      = 1 := by
    rw [← map_mul]
    have : sneg * sneg = 1 := Subtype.ext (by
      show (sneg : K₀ˣ) * (sneg : K₀ˣ) = 1
      rw [hsneg]; simp)
    rw [this, map_one]
  obtain ⟨wP, hwP⟩ := Fr.exists_isUniqueInvolution hP
  obtain ⟨wQ, hwQ⟩ := Fr.exists_isUniqueInvolution hQ
  have hzP : θ (embSUid (unitaryInvolution K₀ p f) 2 (torusTwo (unitaryInvolution K₀ p f) sneg))
      = wP := by
    have hmem : θ (embSUid (unitaryInvolution K₀ p f) 2
        (torusTwo (unitaryInvolution K₀ p f) sneg)) ∈ P := by
      rw [← hPθ]
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    have hsq : θ (embSUid (unitaryInvolution K₀ p f) 2
        (torusTwo (unitaryInvolution K₀ p f) sneg)) * θ (embSUid (unitaryInvolution K₀ p f) 2
        (torusTwo (unitaryInvolution K₀ p f) sneg)) = 1 := by
      rw [← map_mul, ← map_mul, htsq, map_one, map_one]
    rcases hwP.unique _ hmem hsq with h | h
    · exfalso
      have h1 := hinj₂ (show (θ.comp (embSUid (unitaryInvolution K₀ p f) 2))
        (torusTwo (unitaryInvolution K₀ p f) sneg) =
        (θ.comp (embSUid (unitaryInvolution K₀ p f) 2)) 1 by simpa using h)
      have h3 := torusTwo_injective _ (h1.trans (map_one _).symm)
      exact hs1 (by simpa using congrArg Subtype.val h3)
    · exact h
  have hzQ : θ (embSUid (unitaryInvolution K₀ p f) 0 (torusTwo (unitaryInvolution K₀ p f) sneg))
      = wQ := by
    have hmem : θ (embSUid (unitaryInvolution K₀ p f) 0
        (torusTwo (unitaryInvolution K₀ p f) sneg)) ∈ Q := by
      rw [← hQθ]
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    have hsq : θ (embSUid (unitaryInvolution K₀ p f) 0
        (torusTwo (unitaryInvolution K₀ p f) sneg)) * θ (embSUid (unitaryInvolution K₀ p f) 0
        (torusTwo (unitaryInvolution K₀ p f) sneg)) = 1 := by
      rw [← map_mul, ← map_mul, htsq, map_one, map_one]
    rcases hwQ.unique _ hmem hsq with h | h
    · exfalso
      have h1 := hinj₀ (show (θ.comp (embSUid (unitaryInvolution K₀ p f) 0))
        (torusTwo (unitaryInvolution K₀ p f) sneg) =
        (θ.comp (embSUid (unitaryInvolution K₀ p f) 0)) 1 by simpa using h)
      have h3 := torusTwo_injective _ (h1.trans (map_one _).symm)
      exact hs1 (by simpa using congrArg Subtype.val h3)
    · exact h
  have hwPA : wP ∈ A := Fr.mem_of_isUniqueInvolution hP hwP
  have hwQA : wQ ∈ A := Fr.mem_of_isUniqueInvolution hQ hwQ
  have hcard₂ : Nat.card ((Phan.D12 K₀ p f).map θ) = Nat.card F + 1 := by
    rw [Phan.map_D12, Subgroup.card_map_of_injective hinj₂, card_diagTorus2_unitary K₀ p f hK,
      hF]
  have hcard₀ : Nat.card ((Phan.D23 K₀ p f).map θ) = Nat.card F + 1 := by
    rw [Phan.map_D23, Subgroup.card_map_of_injective hinj₀, card_diagTorus2_unitary K₀ p f hK,
      hF]
  have hcP : centPart P A ≤ (Phan.D12 K₀ p f).map θ := by
    intro k hk
    obtain ⟨hkK, hkC⟩ := mem_centPart_iff.mp hk
    rw [← hPθ] at hkK
    obtain ⟨b, ⟨B, rfl⟩, rfl⟩ := hkK
    have hc := hkC wQ hwQA
    have hB : B ∈ Phan.diagTorus2 K₀ p f :=
      Phan.mem_diagTorus2_of_map_commute_zero hK hker hs1 (A := B) (by rw [hzQ]; exact hc.symm)
    rw [Phan.map_D12]
    exact ⟨B, hB, rfl⟩
  have hcQ : centPart Q A ≤ (Phan.D23 K₀ p f).map θ := by
    intro k hk
    obtain ⟨hkK, hkC⟩ := mem_centPart_iff.mp hk
    rw [← hQθ] at hkK
    obtain ⟨b, ⟨B, rfl⟩, rfl⟩ := hkK
    have hc := hkC wP hwPA
    have hB : B ∈ Phan.diagTorus2 K₀ p f :=
      Phan.mem_diagTorus2_of_map_commute_two hK hker hs1 (A := B) (by rw [hzP]; exact hc.symm)
    rw [Phan.map_D23]
    exact ⟨B, hB, rfl⟩
  refine ⟨θ, hker, hPθ, hQθ, ?_, ?_⟩
  · obtain ⟨-, η, hη, hcardP⟩ := (Fr.inSigma hP).isCyclic_and_card_centPart hodd
    exact eq_of_le_card_unitary h5' hcard₂ hcP η hη hcardP
  · obtain ⟨-, η, hη, hcardQ⟩ := (Fr.inSigma hQ).isCyclic_and_card_centPart hodd
    exact eq_of_le_card_unitary h5' hcard₀ hcQ η hη hcardQ

theorem unitaryPair_of_standardPair (hp2 : p ≠ 2) (hK : Nat.card K₀ = (p ^ f) ^ 2)
    (hF : Nat.card F = p ^ f) (h5 : 5 ≤ p ^ f) (Fr : RankFrame F Ω A S) {P Q : Subgroup G}
    (hP : P ∈ S) (hQ : Q ∈ S) {W : Subgroup G} (h : UnitaryBlockStandardPair K₀ p f W P Q) :
    UnitaryPair K₀ p f A P Q := by
  obtain ⟨θ, c, -, hker, hcases⟩ := h
  let θ' : Su K₀ p f 3 →* G := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  have hker' : θ'.ker ≤ Subgroup.center (Su K₀ p f 3) := by
    intro x hx
    have h1 : (MulAut.conj c⁻¹).toMonoidHom x ∈ θ.ker := hx
    have h2 := hker h1
    have h3 := (inferInstance : (Subgroup.center (Su K₀ p f 3)).Normal).conj_mem _ h2 c
    simpa [mul_assoc] using h3
  have hB : ∀ B : Subgroup (Su K₀ p f 3),
      B.map θ' = (B.map (MulAut.conj c⁻¹).toMonoidHom).map θ :=
    fun B => by rw [Subgroup.map_map]
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (unitaryA2Pair_of_normalized hp2 hK hF h5 Fr hP hQ hker' (by rw [hB]; exact h1)
      (by rw [hB]; exact h2))
  · exact Or.inr (unitaryA2Pair_of_normalized hp2 hK hF h5 Fr hQ hP hker' (by rw [hB]; exact h1)
      (by rw [hB]; exact h2))

end Unitary

section Glue

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

omit [Finite G] [IsSimpleGroup G] in
theorem mem_centralizingMembers_of_axisSub {K : Subgroup G} {A : Subgroup G} {x : G}
    {K' : Subgroup G} (hK' : K' ∈ CoreAssembly.conjClass K) (hx : x ∈ axisSub A K') :
    K' ∈ centralizingMembers (CoreAssembly.conjClass K) {x} :=
  ⟨hK', fun k hk => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact ((mem_axisSub_iff.mp hx).2 k hk).symm⟩

theorem linearPair_of_locImg_standardPair {K : Subgroup G} {z : G} (hb : Branch p f K z)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) {A : Subgroup G}
    {S : Set (Subgroup G)} (Fr : RankFrame F (CoreAssembly.conjClass K) A S) {x : G}
    (hP1 : LocalOddCentral (CoreAssembly.conjClass K) {x}) {K' L' : Subgroup G} (hK' : K' ∈ S)
    (hL' : L' ∈ S) (hxK : x ∈ axisSub A K') (hxL : x ∈ axisSub A L')
    {W : Subgroup (RouteD.locQuot (CoreAssembly.conjClass K) x)}
    (h : WeakCT.LinearBlockStandardPair (GaloisField p f) W
      (RouteD.locImg (CoreAssembly.conjClass K) x K')
      (RouteD.locImg (CoreAssembly.conjClass K) x L')) :
    LinearPair F A K' L' := by
  have hq := hb.five
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  obtain ⟨W', hW'⟩ := RouteD.linearBlockStandardPair_of_locImg (by omega : 4 ≤ p ^ f)
    (CoreAssembly.oddCoverSL3_of_five_le hq) (inClass_conjugates hb.member) hP1
    (mem_centralizingMembers_of_axisSub (Fr.subset hK') hxK)
    (mem_centralizingMembers_of_axisSub (Fr.subset hL') hxL) h
  have := Fintype.ofFinite F
  have := Fintype.ofFinite (GaloisField p f)
  obtain ⟨e⟩ : Nonempty (GaloisField p f ≃+* F) := ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, GaloisField.card p f hf])⟩
  exact linearPair_of_standardPair Fr hK' hL' (WeakCT.LinearBlockStandardPair.of_ringEquiv e hW')

theorem unitaryPair_of_locImg_standardPair {K : Subgroup G} {z : G} (hb : Branch p f K z)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) {A : Subgroup G}
    {S : Set (Subgroup G)} (Fr : RankFrame F (CoreAssembly.conjClass K) A S) {x : G}
    (hP1 : LocalOddCentral (CoreAssembly.conjClass K) {x}) {K' L' : Subgroup G} (hK' : K' ∈ S)
    (hL' : L' ∈ S) (hxK : x ∈ axisSub A K') (hxL : x ∈ axisSub A L')
    {W : Subgroup (RouteD.locQuot (CoreAssembly.conjClass K) x)}
    (h : Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W
      (RouteD.locImg (CoreAssembly.conjClass K) x K')
      (RouteD.locImg (CoreAssembly.conjClass K) x L')) :
    UnitaryPair (GaloisField p (2 * f)) p f A K' L' := by
  have hq := hb.five
  have hf : 0 < f := CoreAssembly.pos_of_five_le hq
  have hK₀ : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), pow_mul']
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hb.member
  have hperf : ∀ M ∈ S, M ≤ ⁅M, M⁆ := by
    intro M hM
    obtain ⟨zM, hzM⟩ := hΩ.classical M (Fr.subset hM)
    exact (RouteD.commutator_eq_of_isClassicalMember hzM).ge
  have hmK := mem_centralizingMembers_of_axisSub (Fr.subset hK') hxK
  have hmL := mem_centralizingMembers_of_axisSub (Fr.subset hL') hxL
  obtain ⟨W', hW'⟩ := RouteD.unitaryBlockStandardPair_of_locImg_perfect hq hK₀
    (RouteD.oddCoverSU3 hb.odd hK₀ hq) hP1 (le_centralizingLayer hmK) (le_centralizingLayer hmL)
    (hperf K' hK') (hperf L' hL') h
  exact unitaryPair_of_standardPair hb.odd hK₀ hF hq Fr hK' hL' hW'

end Glue

section Residuals

variable (p f : ℕ) [Fact p.Prime]

@[expose] def A2LocalStdPairs : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch p f K z → HasDatum p f K →
      ∀ (F : Type) [Field F], Nat.card F = p ^ f →
        ∀ (A : Subgroup G) (S : Set (Subgroup G)), RankFrame F (CoreAssembly.conjClass K) A S →
          Nat.card A = 8 → (∃ K' ∈ S, ∃ L' ∈ S, K' ≠ L' ∧ ¬ Commutes K' L') →
          FrameP1 (CoreAssembly.conjClass K) A → ∀ K' ∈ S, ∀ L' ∈ S, K' ≠ L' →
            ¬ Commutes K' L' → ∃ x ∈ axisSub A K' ⊓ axisSub A L', x ≠ 1 ∧
              ((∃ W, WeakCT.LinearBlockStandardPair (GaloisField p f) W
                  (RouteD.locImg (CoreAssembly.conjClass K) x K')
                  (RouteD.locImg (CoreAssembly.conjClass K) x L')) ∨
                (∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W
                  (RouteD.locImg (CoreAssembly.conjClass K) x K')
                  (RouteD.locImg (CoreAssembly.conjClass K) x L')))

variable {p f}

theorem a2PairTypes_of_localStdPairs (h : A2LocalStdPairs p f) : A2PairTypes p f :=
  fun G _ _ _ K z hb hD F _ _ hF A S Fr hcard8 hnc' hP1A K' hK' L' hL' hne hnc => by
    obtain ⟨x, hx, hx1, hstd⟩ :=
      h G K z hb hD F hF A S Fr hcard8 hnc' hP1A K' hK' L' hL' hne hnc
    obtain ⟨hxK, hxL⟩ := Subgroup.mem_inf.mp hx
    have hP1x := hP1A x (mem_axisSub_iff.mp hxK).1 hx1
    rcases hstd with ⟨W, hW⟩ | ⟨W, hW⟩
    · exact Or.inl (linearPair_of_locImg_standardPair hb hF Fr hP1x hK' hL' hxK hxL hW)
    · exact Or.inr (unitaryPair_of_locImg_standardPair hb hF Fr hP1x hK' hL' hxK hxL hW)

variable (p f)

structure ConnectedA2Residuals : Prop where
  datum : A2Datum p f
  p1 : A2P1 p f
  single : A2SingleClass p f
  localPairs : A2LocalStdPairs p f
  injective : A2InjectiveCentral p f
  orth : A2OrthEndpoint p f

variable {p f}

theorem ConnectedA2Residuals.toInputs (h : ConnectedA2Residuals p f) : ConnectedA2Inputs p f where
  datum := h.datum
  p1 := h.p1
  frame := a2FrameFacts_of_residuals p f h.p1 h.single (a2PairTypes_of_localStdPairs h.localPairs)
    h.injective
  orth := h.orth

theorem smallConnectedA2_of_residuals (h : ConnectedA2Residuals p f) :
    CoreAssembly.SmallConnectedA2 p f :=
  smallConnectedA2_of_inputs h.toInputs

end Residuals

end CFSG.ClassicalInvolution.ConnectedA2
