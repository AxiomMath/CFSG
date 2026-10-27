module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeNFactsBasic
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer

public section

namespace CFSG.Wreathed.OriginalAllPrime.ChapterII

open CFSG.ABGTheoremB CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem isQDGroup_of_wreathed [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : IsQDGroup G := by
  rw [isQDGroup_iff]
  refine ⟨⟨n, Or.inr (hasWreathedSylow_of hn S e)⟩, noIndexTwo_of_isSimpleGroup ?_⟩
  intro h2
  obtain ⟨a, b, hab⟩ := hnonab
  have : IsCyclic G := isCyclic_of_prime_card (p := 2) h2
  exact hab (IsCyclic.commGroup.mul_comm a b)

theorem exists_quotient_kernel [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ∃ Kb : Subgroup (centralizerOddCoreQuotient n S e), Kb.Normal ∧ Kb.index = 2 ^ n ∧
      (centralizerOddCoreSylow n hn S e : Subgroup (centralizerOddCoreQuotient n S e)) ⊓ Kb =
        modelY (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) ∧
      commutator (centralizerOddCoreQuotient n S e) ≤ Kb := by
  have hGQD := isQDGroup_of_wreathed hnonab n hn S e
  have hQN : IsQGroup (involutionCentralizer n S e) := wreathed_centralizer_isQGroup hGQD hn S e
  have hQNb : IsQGroup (centralizerOddCoreQuotient n S e) :=
    isQGroup_quotient_oddCore_iff.mpr hQN
  set Sb := centralizerOddCoreSylow n hn S e
  set eb := centralizerOddCoreCoordinates n hn S e
  have hF : WreathedFusionQ Sb eb := wreathedFusionQ_of_isQGroup hn Sb eb hQNb
  have hα : Nat.card
      (Subgroup.normalizer (modelBase Sb eb : Set (centralizerOddCoreQuotient n S e)) ⧸
        (Subgroup.centralizer (modelBase Sb eb : Set (centralizerOddCoreQuotient n S e))).subgroupOf
          (Subgroup.normalizer (modelBase Sb eb : Set (centralizerOddCoreQuotient n S e)))) =
        2 := by
    rw [← automizerIndex_modelBase]
    exact hF.baseIndex
  have hβ : Nonempty
      (Subgroup.normalizer (modelV Sb eb : Set (centralizerOddCoreQuotient n S e)) ⧸
        modelVInnerCentralizer Sb eb ≃* Equiv.Perm (Fin 3)) := by
    rcases modelVNormalizerQuotient_alternatives n hn Sb eb with h2 | h6
    · rw [← outerAutomizerIndex_modelV, hF.quaternionIndex] at h2
      norm_num at h2
    · exact h6
  obtain ⟨Kb, hKb, hidx, hQ⟩ := BrauerWong.typeII_of_base_order_two n hn Sb eb hα hβ
  have : Kb.Normal := hKb
  obtain ⟨hSK, hcyc⟩ := BrauerWong.typeII_subgroup_spec n hn Sb eb Kb hidx hQ
  exact ⟨Kb, hKb, hidx, hSK,
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance⟩

theorem quotient_modelY_eq (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    modelY (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) =
      (centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e) := by
  rw [modelY, centralizerOddCoreModelHom_comp, ← Subgroup.map_map]
  rfl

theorem quotient_modelY_le_layer
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    modelY (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) ≤
      CFSG.layer (centralizerOddCoreQuotient n S e) := by
  rw [quotient_modelY_eq]
  exact OriginalSylowCentralizerCoverage.original_quaternion_image_le_layer hnonab n hn S e hfour

theorem quotient_center_eq (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.center (centralizerOddCoreQuotient n S e) =
      modelCenter (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) := by
  rw [centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e,
    centralizerFullCenterImage_eq_modelCenter]

omit [Finite G] in
theorem mem_modelCenter_of_mem_centralizer_modelY {X : Type*} [Group X] (n : ℕ) (hn : 2 ≤ n)
    (P : Sylow 2 X) (eP : P ≃* Wreath (2 ^ n)) {s : X} (hs : s ∈ (P : Subgroup X))
    (hsY : s ∈ Subgroup.centralizer (modelY P eP : Set X)) : s ∈ modelCenter P eP := by
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  have hnonY : ∃ u v : Original.Y (2 ^ n), u * v ≠ v * u := originalY_is_nonabelian n hn
  have hcent := (hstr.nonabelian_centralizers (Original.Y (2 ^ n)) hnonY).1
  set w := eP ⟨s, hs⟩ with hw
  have hws : wreathModelHom P eP w = s := by
    simp [wreathModelHom, hw]
  have hwC : w ∈ Subgroup.centralizer (Original.Y (2 ^ n) : Set (Wreath (2 ^ n))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyY : wreathModelHom P eP y ∈ modelY P eP := ⟨y, hy, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp hsY _ hyY
    apply wreathModelHom_injective P eP
    rw [map_mul, map_mul, hws]
    exact h
  rw [hcent] at hwC
  rw [← hws]
  exact ⟨w, hwC, rfl⟩

omit [Finite G] in
theorem noIndexTwo_of_perfect_of_odd_index {X : Type*} [Group X] (L : Subgroup X)
    [Group.IsPerfect L] (hL : Odd L.index) : ∀ V : Subgroup X, V.index ≠ 2 := by
  intro V hV
  have hLV : L ≤ V := by
    rw [← Subgroup.commutator_eq_self (H := L)]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (BrauerWong.commutator_le_of_index_two hV)
  have h := Subgroup.index_dvd_of_le hLV
  rw [hV] at h
  exact (Nat.not_even_iff_odd.mpr hL) (even_iff_two_dvd.mpr h)

variable [IsSimpleGroup G]

theorem isQGroup_of_layer_le_of_sylow
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (J : Subgroup (centralizerOddCoreQuotient n S e))
    (hMJ : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ J)
    (R : Subgroup (centralizerOddCoreQuotient n S e)) (hR : IsSylowOf 2 R J)
    (hYR : modelY (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) ≤
      R)
    (hRS : R ≤ (centralizerOddCoreSylow n hn S e : Subgroup (centralizerOddCoreQuotient n S e))) :
    IsQGroup J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Kb, hKn, hKidx, hSK, hcomm⟩ := exists_quotient_kernel hnonab n hn S e
  obtain ⟨-, hMq, -, -⟩ := wreathed_layer_facts hnonab n hn S e hfour
  have hYM := quotient_modelY_le_layer hnonab n hn S e hfour
  set X := centralizerOddCoreQuotient n S e
  set M := CFSG.layer X
  set Sb := centralizerOddCoreSylow n hn S e
  set eb := centralizerOddCoreCoordinates n hn S e
  set Yb := modelY Sb eb
  have : Group.IsPerfect M := hMq.1
  have hMK : M ≤ Kb := by
    rw [← Subgroup.commutator_eq_self (H := M)]
    exact (Subgroup.commutator_mono le_top le_top).trans hcomm
  have hYK : Yb ≤ Kb := hYM.trans hMK
  have hKR : Kb ⊓ R = Yb := by
    apply le_antisymm
    · rw [← hSK]
      intro x hx
      exact ⟨hRS hx.2, hx.1⟩
    · exact le_inf hYK hYR
  have hKnorm : ∀ g : X, g ∈ Subgroup.normalizer (Kb : Set X) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
    exact Subgroup.mem_top g
  have hJK : J ≤ Subgroup.normalizer ((Kb ⊓ J : Subgroup X) : Set X) := fun j hj =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKnorm j, Subgroup.le_normalizer hj⟩
  have hYsyl : IsSylowOf 2 Yb (Kb ⊓ J) := by
    have h := hR.inf_of_le_normalizer (N := Kb ⊓ J) inf_le_right hJK
    have hRKJ : R ⊓ (Kb ⊓ J) = Yb := by
      rw [← hKR, inf_comm Kb J, ← inf_assoc, inf_eq_left.mpr hR.le, inf_comm]
    rwa [hRKJ] at h
  have hModd : Odd (M.relIndex (Kb ⊓ J)) := by
    have h2 := (isSylowOf_iff.mp hYsyl).2.2
    rcases Nat.even_or_odd (M.relIndex (Kb ⊓ J)) with h | h
    · exact absurd ((even_iff_two_dvd.mp h).trans (Subgroup.relIndex_dvd_of_le_left _ hYM)) h2
    · exact h
  obtain ⟨Q, hQ⟩ := id hR
  have hQR : ∀ q : J, q ∈ (Q : Subgroup J) → (q : X) ∈ R := fun q hq => by
    rw [← hQ]
    exact ⟨q, hq, rfl⟩
  have hRQ : ∀ x ∈ R, ∃ q : J, q ∈ (Q : Subgroup J) ∧ (q : X) = x := fun x hx => by
    rw [← hQ] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, hq, rfl⟩
  refine ⟨Q, Kb.subgroupOf J, ⟨inferInstance, ?_, ?_, ?_, ?_⟩⟩
  ·
    have hdvd : (Kb.subgroupOf J).index ∣ 2 ^ n := by
      rw [← hKidx]
      exact Subgroup.relIndex_dvd_index_of_normal Kb J
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨k, hk⟩
  ·
    let ι : (Kb.subgroupOf J) →* X := J.subtype.comp (Kb.subgroupOf J).subtype
    have hι : Function.Injective ι := J.subtype_injective.comp (Subgroup.subtype_injective _)
    have hrange : ι.range = Kb ⊓ J := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.subgroupOf_map_subtype]
    set L := M.comap ι
    have hLmap : L.map ι = M := Subgroup.map_comap_eq_self (hrange ▸ le_inf hMK hMJ)
    have : Group.IsPerfect L := by
      let eL : L ≃* M := (L.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hLmap)
      exact Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
    have hLidx : L.index = M.relIndex (Kb ⊓ J) := by rw [Subgroup.index_comap, hrange]
    exact noIndexTwo_of_perfect_of_odd_index L (hLidx ▸ hModd)
  ·
    let f : (Q : Subgroup J) →* (Sb : Subgroup X) :=
      (J.subtype.comp (Q : Subgroup J).subtype).codRestrict (Sb : Subgroup X)
        (fun q => hRS (hQR q q.2))
    have hf : Function.Injective f := by
      intro a b hab
      have h : ((f a : (Sb : Subgroup X)) : X) = ((f b : (Sb : Subgroup X)) : X) :=
        congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
    refine ⟨inf_le_right, Or.inr ⟨n, hn, eb.toMonoidHom.comp f, eb.injective.comp hf, ?_⟩⟩
    ext w
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hqY : ((q : J) : X) ∈ Yb := by
        rw [← hKR]
        exact ⟨(Subgroup.mem_inf.mp hq).1, hQR q q.2⟩
      obtain ⟨y, hy, hyq⟩ := hqY
      have hfq : f q = eb.symm y := Subtype.ext hyq.symm
      change eb (f q) ∈ Original.Y (2 ^ n)
      rw [hfq, MulEquiv.apply_symm_apply]
      exact hy
    · intro hw
      have hwY : (eb.symm w : X) ∈ Yb := ⟨w, hw, rfl⟩
      obtain ⟨q, hq, hqw⟩ := hRQ _ (hYR hwY)
      refine ⟨⟨q, hq⟩, ⟨?_, hq⟩, ?_⟩
      · change (q : X) ∈ Kb
        rw [hqw]
        exact hYK hwY
      · change eb (f ⟨q, hq⟩) = w
        have hfq : f ⟨q, hq⟩ = eb.symm w := Subtype.ext hqw
        rw [hfq, MulEquiv.apply_symm_apply]
  ·
    intro Z₀ hZ₀
    refine ⟨hZ₀.trans inf_le_left, fun g _ => ?_⟩
    have hcent : Z₀ ≤ centerOf (⊤ : Subgroup J) := by
      intro z hz
      obtain ⟨hzQ, hzC⟩ := Subgroup.mem_inf.mp (hZ₀ hz)
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_top z, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro j _
      have hzS : (z : X) ∈ (Sb : Subgroup X) := hRS (hQR z hzQ)
      have hzY : (z : X) ∈ Subgroup.centralizer (Yb : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨q, hq, rfl⟩ := hRQ y (hYR hy)
        exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hzC q hq)
      have hzZ : (z : X) ∈ Subgroup.center X := by
        rw [quotient_center_eq n hn S e]
        exact mem_modelCenter_of_mem_centralizer_modelY n hn Sb eb hzS hzY
      exact Subtype.ext (Subgroup.mem_center_iff.mp hzZ (j : X))
    exact rightConjugate_eq_of_le_centerOf hcent (Subgroup.mem_top g)

theorem isQGroup_of_layer_le
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (J : Subgroup (centralizerOddCoreQuotient n S e))
    (hMJ : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ J) : IsQGroup J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Kb, hKn, -, hSK, -⟩ := exists_quotient_kernel hnonab n hn S e
  obtain ⟨hMn, -, -, -⟩ := wreathed_layer_facts hnonab n hn S e hfour
  have hYM := quotient_modelY_le_layer hnonab n hn S e hfour
  set X := centralizerOddCoreQuotient n S e
  set M := CFSG.layer X
  set Sb := centralizerOddCoreSylow n hn S e
  set eb := centralizerOddCoreCoordinates n hn S e
  set Yb := modelY Sb eb
  have hYK : Yb ≤ Kb := hSK ▸ inf_le_right
  have hYJ : Yb ≤ J := hYM.trans hMJ
  have hY2 : IsPGroup 2 Yb := Sb.isPGroup'.to_le (modelY_le_sylow Sb eb)
  obtain ⟨Q₀, hQ₀⟩ :=
    (show IsPGroup 2 (Yb.subgroupOf J) from hY2.comap_subtype).exists_le_sylow
  set R₀ := (Q₀ : Subgroup J).map J.subtype
  have hR₀ : IsSylowOf 2 R₀ J := ⟨Q₀, rfl⟩
  have hYR₀ : Yb ≤ R₀ := fun y hy => ⟨⟨y, hYJ hy⟩, hQ₀ hy, rfl⟩
  obtain ⟨P, hRP⟩ := hR₀.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Sb
  let c : X →* X := (MulAut.conj g).toMonoidHom
  have hc : Function.Injective c := (MulAut.conj g).injective
  have hcP : ∀ x ∈ (P : Subgroup X), c x ∈ (Sb : Subgroup X) := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ hx
  set J' := J.map c
  set R' := R₀.map c
  have hR'S : R' ≤ Sb := by
    rintro _ ⟨r, hr, rfl⟩
    exact hcP r (hRP hr)
  have hMJ' : M ≤ J' := by
    intro m hm
    refine ⟨g⁻¹ * m * g, hMJ ?_, ?_⟩
    · have h := hMn.conj_mem m hm g⁻¹
      rwa [inv_inv] at h
    · change g * (g⁻¹ * m * g) * g⁻¹ = m
      group
  have hR' : IsSylowOf 2 R' J' := by
    rw [isSylowOf_iff] at hR₀ ⊢
    obtain ⟨hle, hp, hdvd⟩ := hR₀
    refine ⟨Subgroup.map_mono hle, hp.map c, ?_⟩
    rwa [Subgroup.relIndex_map_map_of_injective _ _ hc]
  have hYR' : Yb ≤ R' := by
    have hle : Yb.map c ≤ Yb := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← hSK]
      exact ⟨hR'S ⟨y, hYR₀ hy, rfl⟩, hKn.conj_mem y (hYK hy) g⟩
    have heq : Yb.map c = Yb :=
      Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective hc).ge
    rw [← heq]
    exact Subgroup.map_mono hYR₀
  have hQ' := isQGroup_of_layer_le_of_sylow hnonab n hn S e hfour J' hMJ' R' hR' hYR' hR'S
  exact hQ'.of_mulEquiv (J.equivMapOfInjective c hc).symm

end CFSG.Wreathed.OriginalAllPrime.ChapterII
