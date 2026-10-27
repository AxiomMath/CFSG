module

public import CFSG.Quasithin.Background.C22PfI
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrModel
import CFSG.Quasithin.Background.C126RFCases
import CFSG.Quasithin.EmptyFaithful.S146F3
import CFSG.Quasithin.H13.GoldschmidtC137S168Main
import CFSG.Quasithin.H13.QTESylowRoot
import CFSG.Quasithin.Vol2.Ch10SecA312AD
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

section Central

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
  CFSG.Quasithin.SmithC27

variable {G : Type} [Group G]

theorem normal_zpowers_of_mem_center {z : G} (hz : z ∈ Subgroup.center G) :
    (Subgroup.zpowers z).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hxc : x ∈ Subgroup.center G := Subgroup.zpowers_le.mpr hz hx
  have := Subgroup.mem_center_iff.mp hxc g
  rwa [this, mul_inv_cancel_right]

theorem isPGroup_zpowers_two {z : G} {n : ℕ} (hn : z ^ 2 ^ n = 1) :
    IsPGroup 2 (Subgroup.zpowers z) := by
  rintro ⟨x, hx⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨n, Subtype.ext ?_⟩
  have h : (z ^ i) ^ 2 ^ n = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]
  simpa using h

theorem mem_of_mk_mem_map_of_two {Z : Subgroup G} [Z.Normal] (hZ : Z ≤ Subgroup.center G)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hZQ : ∀ z ∈ Z, (∃ n : ℕ, z ^ 2 ^ n = 1) → z ∈ Q) {y : G}
    (hy : QuotientGroup.mk' Z y ∈ Q.map (QuotientGroup.mk' Z)) {n : ℕ} (hyn : y ^ 2 ^ n = 1) :
    y ∈ Q := by
  obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hy
  obtain ⟨z, hz, rfl⟩ := (QuotientGroup.mk'_eq_mk' Z).mp hqy
  obtain ⟨m, hm⟩ := hQ ⟨q, hq⟩
  have hqm : q ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hpow : z ^ 2 ^ (m + n) = 1 := by
    have h := Commute.mul_pow (Subgroup.mem_center_iff.mp (hZ hz) q) (2 ^ (m + n))
    rw [pow_add, pow_mul', hyn, one_pow, pow_mul, hqm, one_pow, one_mul] at h
    rw [pow_add]
    exact h.symm
  exact Q.mul_mem hq (hZQ z hz ⟨m + n, hpow⟩)

theorem normalizer_eq_comap_normalizer_map_of_two {Z : Subgroup G} [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hZQ : ∀ z ∈ Z, (∃ n : ℕ, z ^ 2 ^ n = 1) → z ∈ Q) :
    Subgroup.normalizer (Q : Set G) =
      (Subgroup.normalizer (Q.map (QuotientGroup.mk' Z) : Set (G ⧸ Z))).comap
        (QuotientGroup.mk' Z) := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.mp (Subgroup.le_normalizer_map _)) ?_
  have key : ∀ g ∈ (Subgroup.normalizer (Q.map (QuotientGroup.mk' Z) : Set (G ⧸ Z))).comap
      (QuotientGroup.mk' Z), ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := by
    intro g hg x hx
    obtain ⟨n, hn⟩ := hQ ⟨x, hx⟩
    have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine mem_of_mk_mem_map_of_two hZ hQ hZQ ?_ (n := n)
      (by rw [conj_pow, hxn, mul_one, mul_inv_cancel])
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_comap.mp hg) _).mp
      (Subgroup.mem_map_of_mem _ hx)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  refine fun x => ⟨key g hg x, fun hx => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hx

theorem exists_lift_two [Finite G] (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G)
    {V : Subgroup (G ⧸ Z)} (hV : IsPGroup 2 V) :
    ∃ Q : Subgroup G, IsPGroup 2 Q ∧ Q.map (QuotientGroup.mk' Z) = V ∧
      ∀ z ∈ Z, (∃ n : ℕ, z ^ 2 ^ n = 1) → z ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V₀, hV₀, hV₀V⟩ := exists_isPGroup_map_eq Z hV
  have hnorm : (CFSG.Open.pCore 2 G).Normal := CFSG.LieType.BorelTits.pCore_normal (r := 2) (G := G)
  have hT : IsPGroup 2 (Z ⊓ CFSG.Open.pCore 2 G : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := G)).to_le inf_le_right
  have hT' : (Z ⊓ CFSG.Open.pCore 2 G).map (QuotientGroup.mk' Z) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact inf_le_left
  have hsup : IsPGroup 2 (V₀ ⊔ (Z ⊓ CFSG.Open.pCore 2 G) : Subgroup G) :=
    hV₀.to_sup_of_normal_right hT
  refine ⟨V₀ ⊔ (Z ⊓ CFSG.Open.pCore 2 G), hsup, ?_, ?_⟩
  · rw [Subgroup.map_sup, hV₀V, hT', sup_bot_eq]
  · rintro z hz ⟨n, hn⟩
    have hz' : z ∈ CFSG.Open.pCore 2 G := by
      have := normal_zpowers_of_mem_center (hZ hz)
      exact CFSG.LieType.BorelTits.le_pCore (r := 2) (N := Subgroup.zpowers z) this (isPGroup_zpowers_two hn)
        (Subgroup.mem_zpowers z)
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hz, hz'⟩)

theorem pCoreOf_le_map_pCoreOf_comap_of_two [Finite G] (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) (M : Subgroup (G ⧸ Z)) :
    pCoreOf 2 M ≤ (pCoreOf 2 (M.comap (QuotientGroup.mk' Z))).map (QuotientGroup.mk' Z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, hQM, hZQ⟩ := exists_lift_two Z hZ (pCoreOf_isPGroup 2 M)
  rw [← hQM]
  refine Subgroup.map_mono (le_pCoreOf_of_le_normalizer 2 ?_ ?_ hQ)
  · refine (Subgroup.le_comap_map (QuotientGroup.mk' Z) Q).trans (Subgroup.comap_mono ?_)
    rw [hQM]
    exact pCoreOf_le 2 M
  · rw [normalizer_eq_comap_normalizer_map_of_two hZ hQ hZQ, hQM]
    exact Subgroup.comap_mono (le_normalizer_pCoreOf 2 M)

theorem isRadicalParabolic_top_of_quotient_central [Finite G] (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ Subgroup.center G)
    (h : IsRadicalParabolic (⊤ : Subgroup (G ⧸ Z))) : IsRadicalParabolic (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  intro U _ hU1 hU2 hUO
  rw [top_inf_eq] at hUO ⊢
  have hZU : ∀ z ∈ Z, (∃ n : ℕ, z ^ 2 ^ n = 1) → z ∈ U := by
    rintro z hz ⟨n, hn⟩
    have hzc : z ∈ Subgroup.center G := hZ hz
    have hnorm := normal_zpowers_of_mem_center hzc
    have hle : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.normalizer (U : Set G)) :=
      le_pCoreOf_of_le_normalizer 2
        ((Subgroup.zpowers_le.mpr hzc).trans (Subgroup.center_le_normalizer _))
        (by rw [Subgroup.normalizer_eq_top (H := Subgroup.zpowers z)]; exact le_top)
        (isPGroup_zpowers_two hn)
    rw [← hUO]
    exact hle (Subgroup.mem_zpowers z)
  have hN := normalizer_eq_comap_normalizer_map_of_two hZ hU2 hZU
  by_cases hbot : U.map π = ⊥
  · have hUZ : U ≤ Z := by
      have := (Subgroup.map_eq_bot_iff U).mp hbot
      rwa [QuotientGroup.ker_mk'] at this
    have hUn : U.Normal := ⟨fun x hx g => by
      have hxc := Subgroup.mem_center_iff.mp (hZ (hUZ hx)) g
      rwa [hxc, mul_inv_cancel_right]⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 G))
    exact ⟨le_top, P, sylow_two_isSylowTwoOf_top P, by
      rw [Subgroup.normalizer_eq_top (H := U)]; exact le_top⟩
  have hcore : pCoreOf 2 (⊤ ⊓ Subgroup.normalizer (U.map π : Set (G ⧸ Z))) = U.map π := by
    rw [top_inf_eq]
    refine le_antisymm ?_ ?_
    · refine (pCoreOf_le_map_pCoreOf_comap_of_two Z hZ _).trans ?_
      rw [← hN, hUO]
    · have hN' : (Subgroup.normalizer (U : Set G)).map π =
          Subgroup.normalizer (U.map π : Set (G ⧸ Z)) := by
        rw [hN, Subgroup.map_comap_eq_self_of_surjective hπ]
      rw [← hN']
      calc U.map π = (pCoreOf 2 (Subgroup.normalizer (U : Set G))).map π := by rw [hUO]
        _ ≤ pCoreOf 2 ((Subgroup.normalizer (U : Set G)).map π) := map_pCoreOf_le π _
  obtain ⟨-, S', hS', hS'N⟩ := h (U.map π) le_top hbot (hU2.map π) hcore
  obtain ⟨S, hS, rfl⟩ := exists_isSylowTwoOf_map_eq hπ hS'
  refine ⟨le_top, S, hS, ?_⟩
  rw [top_inf_eq, top_inf_eq] at *
  rw [hN]
  exact (Subgroup.map_le_iff_le_comap.mp (Subgroup.le_normalizer_map _)).trans
    (Subgroup.comap_mono hS'N)

theorem isRadicalParabolic_top_of_central_kernel {G' : Type} [Group G'] [Finite G]
    (f : G →* G') (hf : Function.Surjective f) (hZ : f.ker ≤ Subgroup.center G)
    (h : IsRadicalParabolic (⊤ : Subgroup G')) : IsRadicalParabolic (⊤ : Subgroup G) :=
  isRadicalParabolic_top_of_quotient_central f.ker hZ
    ((isRadicalParabolic_congr (topQuotientKerEquiv f hf)).mpr h)

end Central

section Bridge

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabAutIrr CFSG.Blueprint
  CFSG.Assembly.LowTwoRank

theorem evenLieType_of_classicalTag {Y : Type} [Group Y] {t : StatedLieTag} {n f : ℕ}
    (ht : ClassicalTag t) (h : StatedClassicalModel Y t n 2 f) : EvenLieType Y := by
  refine ⟨t, n, f, h.1, Or.inl ⟨?_, h⟩⟩
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide

theorem evenLieType_of_g2_index
    {Y : Type} [Group Y]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hq : q.p = 2)
    (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.G2 q, hv⟩).Group) :
    EvenLieType Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField 2 q.exponent
  have hK : Nat.card K = q.card := by
    rw [GaloisField.card 2 q.exponent q.exponent_pos.ne', TauCeti.PrimePower.card_def, hq]
  have hq3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hK' : Nat.card K = 2 ^ q.exponent := by
    rw [hK, TauCeti.PrimePower.card_def, hq]
  have h3 : 3 ≤ 2 ^ q.exponent := by
    rw [← hK']
    rwa [hK]
  have hadm : StatedLieAdmissible .G2 0 2 q.exponent := ⟨Nat.prime_two, q.exponent_pos, rfl, h3⟩
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq K hK
  exact ⟨.G2, 0, q.exponent, hadm, Or.inr (Or.inl ⟨rfl, by decide,
    hadm, K, inferInstance, inferInstance, hK', ⟨e.trans b.symm⟩⟩)⟩

theorem isPSL_three_two_of_statedPSL_two_seven {Y : Type} [Group Y] [Finite Y]
    (h : StatedClassicalModel Y .PSL 2 7 1) : CFSG.Quasithin.IsPSL 3 2 1 Y := by
  have hs : IsSimpleGroup Y := CFSG.Quasithin.Vol2.Ch10.A312A.isSimpleGroup_of_stated h
  have hc : Nat.card Y = 168 := by
    rw [CFSG.Quasithin.H13.QTESylow.card_of_statedPSL (by norm_num) h]
    decide
  obtain ⟨e⟩ := CFSG.Quasithin.H13.U3.GC137.SQ.S168.nonempty_mulEquiv_psl_seven hc
  have hP : CFSG.Quasithin.IsPSL 3 2 1 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.Quasithin.isPSL_three_two_iff.mpr ⟨MulEquiv.refl _⟩
  have hs' : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.Quasithin.Vol2.Ch10.A312A.isSimpleGroup_of_stated hP
  have hc' : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [CFSG.Quasithin.H13.QTESylow.card_of_statedPSL (by norm_num) hP]
    decide
  obtain ⟨e'⟩ := CFSG.Quasithin.H13.U3.GC137.SQ.S168.nonempty_mulEquiv_psl_seven hc'
  exact CFSG.Quasithin.isPSL_three_two_iff.mpr ⟨e.trans e'.symm⟩

theorem evenLieType_or_alt_six_or_psu_of_isClassicalTwoOrG2
    {Y : Type} [Group Y] [Finite Y]
    (h : IsClassicalTwoOrG2 Y) :
    EvenLieType Y ∨ CFSG.Quasithin.IsAlt 6 Y ∨ CFSG.Quasithin.IsPSU 3 3 1 Y := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d, hv⟩, hd, ⟨e⟩⟩
  · rcases classical_model_or_g2 d hd e with ⟨t, n, f, ht, hm⟩ | ⟨q, hv, hq, rfl⟩
    · exact Or.inl (evenLieType_of_classicalTag ht hm)
    · exact Or.inl (evenLieType_of_g2_index q hv hq e)
  · rcases hn with rfl | rfl | rfl
    · have h' := CFSG.Quasithin.C126.isPSL_two_two_two_of_alternating_five Y ⟨e⟩
      exact Or.inl ⟨.PSL, 2, 2, h'.1, Or.inl ⟨by decide, h'⟩⟩
    · exact Or.inr (Or.inl ⟨e⟩)
    · have hm := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff Y).2
        ⟨e⟩
      exact Or.inl ⟨.PSL, 4, 1, ⟨Nat.prime_two, le_rfl, by decide⟩, hm⟩
  · rcases hd with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
    · have hdq' : d = .A 1 q := hdq
      subst hdq'
      have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      have hpe := (Nat.Prime.pow_eq_iff Nat.prime_seven).mp
        ((TauCeti.PrimePower.card_def q).symm.trans hq)
      rw [hpe.1, hpe.2] at hm
      exact Or.inl (evenLieType_of_classicalTag (Or.inl rfl) (isPSL_three_two_of_statedPSL_two_seven hm))
    · have hdq' : d = .twistedA 2 q := hdq
      subst hdq'
      have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      have hpe := (Nat.Prime.pow_eq_iff Nat.prime_three).mp
        ((TauCeti.PrimePower.card_def q).symm.trans hq)
      rw [hpe.1, hpe.2] at hm
      exact Or.inr (Or.inr hm)

end Bridge

section Main

open CFSG.AGLEmbedding CFSG.Quasithin CFSG.Quasithin.SmithC27

theorem isRadicalParabolic_of_isClassicalTwoOrG2_center
    {Γ : Type} [Group Γ] [Finite Γ] {Lb : Subgroup Γ}
    (hc : IsClassicalTwoOrG2 (↥Lb ⧸ Subgroup.center ↥Lb)) :
    SmithC27.IsRadicalParabolic Lb := by
  rw [isRadicalParabolic_iff_top]
  have hX := evenLieType_or_alt_six_or_psu_of_isClassicalTwoOrG2 hc
  exact isRadicalParabolic_top_of_central_kernel (QuotientGroup.mk' (Subgroup.center ↥Lb))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    (C22Pf.isRadicalParabolic_c224_holds _ hX)

end Main

end CFSG.HardMathSupport.Cooperstein.StructureLie
