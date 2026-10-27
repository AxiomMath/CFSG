module

public import CFSG.ClassicalInvolution.Asc77.AscC22N1
public import CFSG.ClassicalInvolution.Asc77.AscC22P6
public import CFSG.ClassicalInvolution.Asc77.AscS22E

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement MatrixGroups

namespace C22N

set_option linter.unusedSectionVars false

section Layer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}


theorem layer2_neg (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hex : ExactMembers Ω) (hπ : piSign p f = false)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥) (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃)
    (hV : ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃ ∨ M = K₄) {R R' : Subgroup G}
    {b b' y : G} (hF : C22P.FrameData Ω K₃ K₄ z (u₁ * u₂) R R' b b' y)
    (hP1 : ∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K₃ (conjSub y K₃)) :
    (∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K (conjSub y K₃)) ∧
      (∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K' (conjSub y K₃)) ∧
      conjSub y K₄ ≤ exactLayer Ω (b * b') ∧
      exactLayer Ω (b * b') = K' ⊔ conjSub y K₃ ⊔ K := by
  classical
  have hp2 : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := hs.hzK'
  have hzK₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hzK₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  have hcls : ∀ M ∈ Ω, ∃ z', IsClassicalMember p f M z' := hΩ.classical
  set u : G := u₁ * u₂ with hu
  have hu2 : u * u = 1 := hs.sq_12
  have hbK₃ : b ∈ K₃ := hF.hR.1 hF.hbR
  have hb'K₄ : b' ∈ K₄ := hF.hR'.1 hF.hb'R'
  have hbb : b * b' = b' * b := hF.hRR' b hF.hbR b' hF.hb'R'
  have hbb2 : (b * b') * (b * b') = 1 := by
    calc (b * b') * (b * b') = b * (b' * b) * b' := by group
      _ = b * (b * b') * b' := by rw [← hbb]
      _ = (b * b) * (b' * b') := by group
      _ = 1 := by rw [hF.hbz, hF.hb'z]; exact hzK₃.sq
  have hbb1 : b * b' ≠ 1 :=
    (T7S22.mul_ne_one_of_twins hΩ hK₃Ω hK₄Ω h43.symm hzK₃ hbK₃ hb'K₄ hF.hb'4).1
  have hc2' : IsPGroup 2 (Subgroup.zpowers (b * b')) := isPGroup_zpowers_of_sq_eq_one hbb2
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self hKΩ hz
  have cKK' : Commutes K K' := C22P.commutes_of_twins hs.stand hz hKV hs.hK' hs.hne.symm hex
  have cKK₃ : Commutes K K₃ := C22P.commutes_of_twins hs.stand hz hKV hs.hK₃ hs.hK₃K.symm hex
  have cKK₄ : Commutes K K₄ := C22P.commutes_of_twins hs.stand hz hKV hK₄ h41.symm hex
  have cK'K₃ : Commutes K' K₃ := C22P.commutes_of_twins hs.stand hz hs.hK' hs.hK₃ hs.hK₃K'.symm hex
  have cK'K₄ : Commutes K' K₄ := C22P.commutes_of_twins hs.stand hz hs.hK' hK₄ h42.symm hex
  have cK₃K₄ : Commutes K₃ K₄ := C22P.commutes_of_twins hs.stand hz hs.hK₃ hK₄ h43.symm hex
  have hK₃c : K₃ ≤ Subgroup.centralizer ({u} : Set G) :=
    C22P.le_centralizer_mul hs.hu₁.1 hs.hu₂.1 cKK₃ cK'K₃
  have hK₄c : K₄ ≤ Subgroup.centralizer ({u} : Set G) :=
    C22P.le_centralizer_mul hs.hu₁.1 hs.hu₂.1 cKK₄ cK'K₄
  have hKc' : K ≤ Subgroup.centralizer ({b * b'} : Set G) :=
    C22P.le_centralizer_mul hbK₃ hb'K₄ cKK₃.symm cKK₄.symm
  have hK'c' : K' ≤ Subgroup.centralizer ({b * b'} : Set G) :=
    C22P.le_centralizer_mul hbK₃ hb'K₄ cK'K₃.symm cK'K₄.symm
  have hyc : y ∈ Subgroup.centralizer ({u} : Set G) := exactLayer_le_centralizer Ω u hF.hy
  have hJc : conjSub y K₃ ≤ Subgroup.centralizer ({u} : Set G) :=
    C22P.conjSub_le_centralizer_of_mem hyc hK₃c
  have hJ'c : conjSub y K₄ ≤ Subgroup.centralizer ({u} : Set G) :=
    C22P.conjSub_le_centralizer_of_mem hyc hK₄c
  have hJΩ : conjSub y K₃ ∈ Ω := hΩ.conjInvariant y K₃ hK₃Ω
  have hJ'Ω : conjSub y K₄ ∈ Ω := hΩ.conjInvariant y K₄ hK₄Ω
  have htJ : IsUniqueInvolution (conjSub y K₃) (b * b' * u) := hF.hyz ▸ hzK₃.conj y
  have htJ' : IsUniqueInvolution (conjSub y K₄) (b * b' * u) := hF.hyz ▸ hzK₄.conj y
  have hcentJ : ∀ {M : Subgroup G} {t : G}, IsUniqueInvolution M t →
      M ≤ Subgroup.centralizer ({u} : Set G) → t = b * b' * u →
        M ≤ Subgroup.centralizer ({b * b'} : Set G) := by
    intro M t ht hMu htt x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp (hMu hx)
    have e2 : x * t = t * x := (ht.commute_of_mem hx).symm
    rw [htt] at e2
    have e3 : b * b' = (b * b' * u) * u := by
      calc b * b' = b * b' * (u * u) := by rw [hu2, mul_one]
        _ = (b * b' * u) * u := by group
    calc x * (b * b') = x * ((b * b' * u) * u) := by rw [← e3]
      _ = (x * (b * b' * u)) * u := by group
      _ = (b * b' * u) * (x * u) := by rw [e2]; group
      _ = (b * b' * u) * (u * x) := by rw [e1]
      _ = ((b * b' * u) * u) * x := by group
      _ = (b * b') * x := by rw [← e3]
  have hJc' : conjSub y K₃ ≤ Subgroup.centralizer ({b * b'} : Set G) := hcentJ htJ hJc rfl
  have hJ'c' : conjSub y K₄ ≤ Subgroup.centralizer ({b * b'} : Set G) := hcentJ htJ' hJ'c rfl
  have hKΦ : K ∈ exactFamily Ω (b * b') := centMembers_subset_exactFamily hcls ⟨hKΩ, hKc'⟩
  have hK'Φ : K' ∈ exactFamily Ω (b * b') := centMembers_subset_exactFamily hcls ⟨hK'Ω, hK'c'⟩
  have hJΦ : conjSub y K₃ ∈ exactFamily Ω (b * b') :=
    centMembers_subset_exactFamily hcls ⟨hJΩ, hJc'⟩
  have hJ'Φ : conjSub y K₄ ∈ exactFamily Ω (b * b') :=
    centMembers_subset_exactFamily hcls ⟨hJ'Ω, hJ'c'⟩
  have hle : ∀ {M : Subgroup G}, M ∈ exactFamily Ω (b * b') →
      M ≤ omegaGen (exactFamily Ω (b * b')) := fun hM => le_omegaGen hM
  obtain ⟨R₁, R₂, R₃, hR₁, hR₂, -, hu₁R, hu₂R, -, c12, c13, c23⟩ := T7J.exists_sylow_triple hs
  have hu₁Ω : u₁ * u₁ = z := sq_eq_involution_of_orderOf_four hz hs.hu₁.1 hs.hu₁.2
  have hu₂Ω : u₂ * u₂ = z := sq_eq_involution_of_orderOf_four hzK' hs.hu₂.1 hs.hu₂.2
  have hBelow : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  have hMz : IsClassicalMember p f K₃ z := isClassicalMember_of_twin hΩ hK₃Ω hzK₃
  have hnc : ¬ ({b * b'} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one (exists_noncomm_of_isClassicalMember hMz) hbb1
  have hKt : K ∈ tqMembers Ω (b * b') := ⟨hKΩ, mem_trivialOnQuot_of_le_centralizer hKc'⟩
  have hK't : K' ∈ tqMembers Ω (b * b') := ⟨hK'Ω, mem_trivialOnQuot_of_le_centralizer hK'c'⟩
  have hJt : conjSub y K₃ ∈ tqMembers Ω (b * b') :=
    ⟨hJΩ, mem_trivialOnQuot_of_le_centralizer hJc'⟩
  have hb'K₃ : b' ∈ trivialOnQuot K₃ :=
    T7J.twin_le_trivialOnQuot hΩ hK₄Ω hK₃Ω h43 hzK₄ hzK₃ hb'K₄
  have hbK₄ : b ∈ trivialOnQuot K₄ :=
    T7J.twin_le_trivialOnQuot hΩ hK₃Ω hK₄Ω h43.symm hzK₃ hzK₄ hbK₃
  have hnotK₃ : K₃ ∉ tqMembers Ω (b * b') :=
    T7J.not_mem_tqMembers_of_mul hp2 hq hΩ hK₃Ω hzK₃ hbK₃ hF.hb4 hb'K₃ rfl
  have hnotK₄ : K₄ ∉ tqMembers Ω (b * b') :=
    T7J.not_mem_tqMembers_of_mul hp2 hq hΩ hK₄Ω hzK₄ hb'K₄ hF.hb'4 hbK₄ hbb
  have hperp : ∀ J₀ ∈ tqMembers Ω (b * b'), J₀ ∈ KPerp Ω K → J₀ = K ∨ J₀ = K' := by
    intro J₀ hJt₀ hJperp
    rw [hs.perp] at hJperp
    rcases hV J₀ hJperp with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK₃
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK₄
  have hperp' : ∀ J₀ ∈ tqMembers Ω (b * b'), J₀ ∈ KPerp Ω K' → J₀ = K' ∨ J₀ = K := by
    intro J₀ hJt₀ hJperp
    rw [T7S22.perp_of_twin hs hs.hK', twinSet_eq_of_mem_twinSet hz hs.hK'] at hJperp
    rcases hV J₀ hJperp with h | h | h | h
    · exact Or.inr h
    · exact Or.inl h
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK₃
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK₄
  have hR₁c : R₁ ≤ Subgroup.centralizer ({b * b'} : Set G) := hR₁.1.trans hKc'
  have hR₂c : R₂ ≤ Subgroup.centralizer ({b * b'} : Set G) := hR₂.1.trans hK'c'
  have hex₁ : IsSylow2In R₁ (exactCore (b * b') K) :=
    (isSylow2In_exactCore_iff hΩ hc2' hKΩ hKt.2).mpr ⟨hR₁, hR₁c⟩
  have hex₂ : IsSylow2In R₂ (exactCore (b * b') K') :=
    (isSylow2In_exactCore_iff hΩ hc2' hK'Ω hK't.2).mpr ⟨hR₂, hR₂c⟩
  have hu_comm : u * (b * b') = (b * b') * u := by
    have e1 : b * u = u * b := Subgroup.mem_centralizer_singleton_iff.mp (hK₃c hbK₃)
    have e2 : b' * u = u * b' := Subgroup.mem_centralizer_singleton_iff.mp (hK₄c hb'K₄)
    calc u * (b * b') = (u * b) * b' := by group
      _ = (b * u) * b' := by rw [e1]
      _ = b * (u * b') := by group
      _ = b * (b' * u) := by rw [e2]
      _ = (b * b') * u := by group
  have hL2 : LayerOrthType p f Ω (b * b') 6 false := by
    have h := T7J.layer_orth_six_weak_proved hp2 hq hΩ hBelow hbb2 hnc hKt hK't hJt hz hzK'
      hperp hperp' htJ hF.hzt hF.htz hex₁ hex₂ c12 (hex₁.1 hu₁R) (hex₂.1 hu₂R) hu₁Ω hu₂Ω
      hu_comm.symm
    rwa [hπ] at h
  have hKtw₃ : K ∈ twinSet Ω K₃ := by
    rw [twinSet_eq_of_mem_twinSet hz hs.hK₃]
    exact hKV
  have hK₄tw₃ : K₄ ∈ twinSet Ω K₃ := by
    rw [twinSet_eq_of_mem_twinSet hz hs.hK₃]
    exact hK₄
  have hD' : Hyp22Setting p f Ω K₃ K₄ K z b b' u₁ :=
    S22.hyp22Setting_of_sylows (hs.stand.of_mem hK₃Ω) hzK₃ hK₄tw₃ h43
      (T7S22.perp_of_twin hs hs.hK₃) hKtw₃ hs.hK₃K.symm h41.symm hF.hR hF.hR' hR₁ hF.hRR'
      (fun x hx w hw => (cKK₃ w (hR₁.1 hw) x (hF.hR.1 hx)).symm)
      (fun x hx w hw => (cKK₄ w (hR₁.1 hw) x (hF.hR'.1 hx)).symm) hF.hbR hF.hb'R' hu₁R hF.hb4
      hF.hb'4 hs.hu₁.2
  have hαeq := S22.alpha_eq_of_datum (S22.c22_2S p f) hs hD' (S22.Big.of_four hs hK₄ h41 h42 h43)
  have hα' : alphaOf (Subgroup.closure ({b * b', z} : Set G)) = ⊥ := hαeq.symm.trans hα
  have hKle : K ≤ exactLayer Ω (b * b') := (T7Z.exactLayer_eq_omegaGen Ω (b * b')) ▸ hle hKΦ
  have hzY' : z ∈ exactLayer Ω (b * b') := hKle hz.mem
  have hJY : conjSub y K₃ ≤ exactLayer Ω (b * b') :=
    (T7Z.exactLayer_eq_omegaGen Ω (b * b')) ▸ hle hJΦ
  have hJ'Y : conjSub y K₄ ≤ exactLayer Ω (b * b') :=
    (T7Z.exactLayer_eq_omegaGen Ω (b * b')) ▸ hle hJ'Φ
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hK2 : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf1
  have hOc' : classicalInvolutionOddCore ↥(exactLayer Ω (b * b')) = ⊥ := by
    refine oddCore_layer_eq_bot_neg hp2 hq hΩ.conjInvariant hbb1 hα' hL2 hzY' hzK₃.sq ?_
    intro hall
    obtain ⟨W, hW⟩ := hP1
    have h1 : z = 1 := CFSG.ClassicalInvolution.Asc77.UnitaryBlockStandardPair.eq_one_of_centralizes
      hK2 hq hW hzK₃.mem (fun w hw => (hall w (hJY hw)).symm)
    exact hzK₃.ne_one h1
  obtain ⟨P⟩ := nonempty_psuLayer_of_layerOrth hOc' hL2
  obtain ⟨RK, hRK, hKR⟩ := P.fund K hKΦ
  obtain ⟨RK', hRK', hK'R⟩ := P.fund K' hK'Φ
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund _ hJΦ
  have hu₁K : u₁ ∈ K := hs.hu₁.1
  have hu₂K' : u₂ ∈ K' := hs.hu₂.1
  have he : b * b' ∈ omegaGen (exactFamily Ω (b * b')) := by
    have h1 : u ∈ omegaGen (exactFamily Ω (b * b')) :=
      Subgroup.mul_mem _ (hle hKΦ hu₁K) (hle hK'Φ hu₂K')
    have h2 : b * b' * u ∈ omegaGen (exactFamily Ω (b * b')) := hle hJΦ htJ.mem
    have h3 : (b * b' * u) * u⁻¹ ∈ omegaGen (exactFamily Ω (b * b')) :=
      Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ h1)
    have e : (b * b' * u) * u⁻¹ = b * b' := by group
    rwa [e] at h3
  have hec : ∀ y' ∈ omegaGen (exactFamily Ω (b * b')), (b * b') * y' = y' * (b * b') := by
    intro y' hy'
    have hy'' : y' ∈ exactLayer Ω (b * b') := (T7Z.exactLayer_eq_omegaGen Ω (b * b')) ▸ hy'
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (exactLayer_le_centralizer Ω (b * b') hy'')).symm
  have htab : b * b' * u = u₁ * u₂ * (b * b') := hu_comm.symm
  have htab' : b * b' * u = u₂ * u₁ * (b * b') := by
    rw [htab, hs.comm₁₂]
  obtain ⟨hKJ, hKJc⟩ := C22P.not_commutes_of_involution_S hs (mem_twinSet_self hKΩ hz) hJΩ htJ
    hF.htz
  obtain ⟨hK'J, hK'Jc⟩ := C22P.not_commutes_of_involution_S hs hs.hK' hJΩ htJ hF.htz
  obtain ⟨h1, h2⟩ := C22G.PSULayer.pair_of_member_ne hp2 hq P hRK hRJ hKR hK'R hJR hz htJ hu₁K
    hu₂K' hu₁Ω cKK' he hec htab hKJ hKJc
  obtain ⟨h1', h2'⟩ := C22G.PSULayer.pair_of_member_ne hp2 hq P hRK' hRJ hK'R hKR hJR hzK' htJ
    hu₂K' hu₁K hu₂Ω cKK'.symm he hec htab' hK'J hK'Jc
  refine ⟨h2, h2', hJ'Y, ?_⟩
  obtain ⟨W₁, hW₁⟩ := h1
  have hgen := C22G.PSULayer.sup_eq_omegaGen hp2 hq P hRK' hJR hKR hK'R h1'
    ⟨W₁, Generic.unitaryBlockStandardPair_symm hW₁⟩ cKK'
  rw [T7Z.exactLayer_eq_omegaGen Ω (b * b')]
  exact hgen.symm

end Layer

end C22N

end CFSG.ClassicalInvolution.Asc77
