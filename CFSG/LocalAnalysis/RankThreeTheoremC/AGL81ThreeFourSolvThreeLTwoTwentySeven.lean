module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeLinTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsGen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNormalizesNoSU
import CFSG.RankThree.PartTwo.KFacts.KS10L27Aut
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143Card

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

section Generic

variable {Y I₀ : Type} [Group Y] [Finite Y] [Group I₀] [Finite I₀]

theorem range_le_of_forall_two_pow (σ : I₀ →* Y)
    (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀)) {C : Subgroup Y}
    (h : ∀ g : I₀, (∃ k : ℕ, g ^ 2 ^ k = 1) → σ g ∈ C) : σ.range ≤ C := by
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ Subgroup.closure {a : I₀ | ∃ k : ℕ, a ^ 2 ^ k = 1} := by
    rw [SolvNone.closure_twoElements_eq_top hb]
    exact Subgroup.mem_top g
  have hle : Subgroup.closure {a : I₀ | ∃ k : ℕ, a ^ 2 ^ k = 1} ≤ C.comap σ :=
    (Subgroup.closure_le _).mpr fun a ha => h a ha
  exact hle hg

theorem false_of_le_range_of_card (σ : I₀ →* Y)
    (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀)) (hker : Nat.Coprime 3 (Nat.card σ.ker))
    {U : Subgroup Y} (hUS : U ≤ σ.range) (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hU27 : Nat.card U = 27) (hUn : σ.range ≤ normalizer (U : Set Y)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, he⟩ := (CFSG.pCore_isPGroup (p := 2) (G := I₀)).exists_card_eq
  have hcardI : Nat.card I₀ = Nat.card (I₀ ⧸ CFSG.pCore 2 I₀) * 2 ^ e := by
    rw [← he]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hSdvd : Nat.card σ.range ∣ Nat.card I₀ := Subgroup.card_range_dvd σ
  have hUdvd : 27 ∣ Nat.card σ.range := hU27 ▸ Subgroup.card_dvd_of_le hUS
  by_cases hs3 : Nonempty (I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3))
  · obtain ⟨f⟩ := hs3
    have h6 : Nat.card (I₀ ⧸ CFSG.pCore 2 I₀) = 6 := by
      rw [Nat.card_congr f.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    have h1 : 9 * 3 ∣ 2 ^ (e + 1) * 3 := by
      have := hUdvd.trans hSdvd
      rw [hcardI, h6] at this
      have he' : 6 * 2 ^ e = 2 ^ (e + 1) * 3 := by ring
      rw [he'] at this
      exact this
    have h2 : 9 ∣ 2 ^ (e + 1) := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1
    have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three ((by norm_num : 3 ∣ 9).trans h2)
    omega
  obtain ⟨a, b, ha, hb3, hab⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNoSU.exists_cube_not_comm hb (not_nonempty_iff.mp hs3)
  have h216 : Nat.card (I₀ ⧸ CFSG.pCore 2 I₀) = 216 := by
    rcases hb with hf | ⟨F, _, _, hF, ⟨f⟩⟩
    · exact absurd hf hs3
    · rw [Nat.card_congr f.toEquiv,
        CFSG.HardMathSupport.Solomon.Coordinator.card_statedSU_three_of' (q := 2)
          (by rw [hF]; norm_num)]
      norm_num
  set U' : Subgroup σ.range := U.subgroupOf σ.range with hU'
  haveI hU'n : U'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUS).mpr hUn
  have hU'card : Nat.card U' = 27 := by
    rw [hU', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv, hU27]
  obtain ⟨j, hj⟩ : ∃ j : ℕ, U'.index = 2 ^ j := by
    have hidx : U'.index * 27 = Nat.card σ.range := by
      rw [← hU'card, Subgroup.index_mul_card]
    have hdvd : U'.index ∣ 2 ^ (e + 3) := by
      have h1 : U'.index * 27 ∣ 2 ^ (e + 3) * 27 := by
        rw [hidx]
        have := hSdvd
        rw [hcardI, h216] at this
        have he' : 216 * 2 ^ e = 2 ^ (e + 3) * 27 := by ring
        rwa [he'] at this
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  have hodd : ∀ s ∈ σ.range, Odd (orderOf s) → s ∈ U := by
    intro s hs hso
    have h1 : (⟨s, hs⟩ : σ.range) ^ U'.index ∈ U' := Subgroup.pow_index_mem U' _
    rw [hj] at h1
    have hcop : (2 ^ j).Coprime (orderOf (⟨s, hs⟩ : σ.range)) := by
      rw [Subgroup.orderOf_mk]
      exact Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hso)
    obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
    have h2 : (⟨s, hs⟩ : σ.range) ∈ U' := by
      rw [← hc]
      exact U'.pow_mem h1 c
    exact Subgroup.mem_subgroupOf.mp h2
  have hlift : ∀ c : I₀ ⧸ CFSG.pCore 2 I₀, c ^ 3 = 1 → ∃ x : I₀, x ^ 3 = 1 ∧
      QuotientGroup.mk' (CFSG.pCore 2 I₀) x ^ (2 ^ e) = c := by
    intro c hc
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 I₀) c
    have hx'O : x' ^ 3 ∈ CFSG.pCore 2 I₀ := by
      rw [← QuotientGroup.eq_one_iff, ← hc]
      rfl
    refine ⟨x' ^ (2 ^ e), ?_, ?_⟩
    · have h1 := pow_card_eq_one' (G := ↥(CFSG.pCore 2 I₀)) (x := ⟨x' ^ 3, hx'O⟩)
      rw [he] at h1
      have h2 : (x' ^ 3) ^ (2 ^ e) = 1 := by simpa using congrArg Subtype.val h1
      rw [← pow_mul, mul_comm, pow_mul, h2]
    · have h4 : 2 ^ (e * 2) % 3 = 1 := by rw [pow_mul', Nat.pow_mod]; norm_num
      rw [map_pow, ← pow_mul, pow_eq_pow_mod _ hc, ← pow_two, ← pow_mul, h4, pow_one]
  obtain ⟨x, hx3, hxa⟩ := hlift a ha
  obtain ⟨y, hy3, hyb⟩ := hlift b hb3
  have hoddof : ∀ g : I₀, g ^ 3 = 1 → Odd (orderOf (σ g)) := fun g hg =>
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hg, map_one]))
  have hσxy : σ x * σ y = σ y * σ x :=
    hUc _ (hodd _ ⟨x, rfl⟩ (hoddof x hx3)) _ (hodd _ ⟨y, rfl⟩ (hoddof y hy3))
  set z := x * y * x⁻¹ * y⁻¹ with hz
  have hzk : z ∈ σ.ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv, hσxy]
    group
  have hO2 : ∀ g : I₀, g ^ 3 = 1 →
      g ∈ CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀) := fun g hg =>
    Subgroup.subset_closure ⟨Subgroup.mem_top g,
      Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hg)⟩
  have hzO : z ∈ CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hO2 x hx3) (hO2 y hy3))
      (Subgroup.inv_mem _ (hO2 x hx3))) (Subgroup.inv_mem _ (hO2 y hy3))
  set π := QuotientGroup.mk' (CFSG.pCore 2 I₀) with hπ
  have hπz3 : π z ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (cube_mem_pCore_two hb z hzO)
  have hπz : π z = 1 := by
    have h1 : orderOf (π z) ∣ 3 := orderOf_dvd_of_pow_eq_one hπz3
    have h2 : orderOf (π z) ∣ Nat.card σ.ker := by
      have h3 := orderOf_dvd_natCard (⟨z, hzk⟩ : σ.ker)
      rw [Subgroup.orderOf_mk] at h3
      exact (orderOf_map_dvd π z).trans h3
    have h4 : orderOf (π z) ∣ 1 := by
      rw [← Nat.Coprime.gcd_eq_one hker]
      exact Nat.dvd_gcd h1 h2
    rwa [Nat.dvd_one, orderOf_eq_one_iff] at h4
  have hπc : π x * π y = π y * π x := by
    have h1 : π x * π y * (π x)⁻¹ * (π y)⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact hπz
    calc π x * π y = (π x * π y * (π x)⁻¹ * (π y)⁻¹) * (π y * π x) := by group
      _ = π y * π x := by rw [h1, one_mul]
  apply hab
  rw [← hxa, ← hyb]
  exact (Commute.pow_pow hπc (2 ^ e) (2 ^ e)).eq

end Generic

theorem threeFourSolvThreeNoneAt_psl2_27 : ThreeFourSolvThreeNoneAt (PSL2GF 3 3) := by
  intro Y _ _ K Y₀ E R I₀ _ _ σ hK hKX hZ hrk _ hC hcomp hER hE hEc hcore hO2 hker hσY hσs hb _ _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hK
  obtain ⟨e⟩ := hKX
  set C := centralizer (K : Set Y) with hCdef
  haveI hsimple : IsSimpleGroup (PSL2GF 3 3) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
      (by rw [GaloisField.card 3 3 (by norm_num)]; norm_num)
  haveI : IsSimpleGroup K := e.isSimpleGroup
  have hnab : ∃ a b : K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : Subgroup.center K = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => h y x
    rw [hZ] at htop
    have h1 : Nat.card K = 1 := by
      rw [← Subgroup.card_top (G := K), ← htop, Subgroup.card_bot]
    have h2 : Nat.card K = 9828 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.RankThree.PartTwo.KFacts.card_psl2_27
    omega
  have hKnle : ¬ K ≤ Y₀ := by
    refine hcomp K ?_ le_rfl
    haveI : Group.IsPerfect K := ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top K hnab⟩
    exact ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤),
      CFSG.ComponentClassification.Quasisimple.simple_of_perfect K⟩
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  set U : Subgroup Y := (R : Subgroup Y) ⊓ K with hUdef
  set T' : Sylow 3 (PSL2GF 3 3) := T.mapSurjective (f := e.toMonoidHom) e.surjective with hT'
  have hT'coe : (T' : Subgroup (PSL2GF 3 3)) = (T : Subgroup K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨hT'el, hT'card⟩ := psl2GF_sylow 3 3 (by norm_num) T'
  have hmemU : ∀ v : Y, ∀ hv : v ∈ K, v ∈ U ↔ e ⟨v, hv⟩ ∈ (T' : Subgroup (PSL2GF 3 3)) := by
    intro v hv
    rw [hT'coe, ← hT]
    constructor
    · rintro ⟨w, hw, hwv⟩
      have hwv' : w = ⟨v, hv⟩ := Subtype.ext hwv
      exact ⟨w, hw, by rw [hwv']; rfl⟩
    · rintro ⟨w, hw, hwv⟩
      have hwv' : w = ⟨v, hv⟩ := e.injective hwv
      exact ⟨w, hw, by rw [hwv']; rfl⟩
  have hUK : U ≤ K := inf_le_right
  have hUR : U ≤ (R : Subgroup Y) := inf_le_left
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    have ha' := (hmemU a (hUK ha)).mp ha
    have hb' := (hmemU b (hUK hb)).mp hb
    have h1 := hT'el.1.is_comm.comm ⟨_, ha'⟩ ⟨_, hb'⟩
    have h2 : e (⟨a, hUK ha⟩ * ⟨b, hUK hb⟩) = e (⟨b, hUK hb⟩ * ⟨a, hUK ha⟩) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h1
    exact congrArg Subtype.val (e.injective h2)
  have hU3 : ∀ u ∈ U, u ^ 3 = 1 := by
    intro u hu
    have h1 := hT'el.2 _ ((hmemU u (hUK hu)).mp hu)
    have h2 : e (⟨u, hUK hu⟩ ^ 3) = e 1 := by rw [map_pow, h1, map_one]
    have h3 := congrArg Subtype.val (e.injective h2)
    simpa using h3
  have hU27 : Nat.card U = 27 := by
    calc Nat.card U = Nat.card (T : Subgroup K) := by
          rw [← hT, Subgroup.card_map_of_injective K.subtype_injective]
      _ = Nat.card (T' : Subgroup (PSL2GF 3 3)) := by
          rw [hT'coe, Subgroup.card_map_of_injective e.injective]
      _ = 27 := by rw [hT'card]; norm_num
  have hUel : IsElemAbelian 3 U := ⟨⟨⟨fun a b => Subtype.ext (hUc a a.2 b b.2)⟩⟩, hU3⟩
  have hR3 : 3 ≤ CFSG.Open.pRank 3 (R : Subgroup Y) :=
    CFSG.SectionRank.le_pRank (by norm_num) hUR hUel (by rw [hU27]; norm_num)
  have hU3r : 3 ≤ CFSG.Open.pRank 3 U :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hUel (by rw [hU27]; norm_num)
  have hNU : normalizer (U : Set Y) ≤ Y₀ := by
    have hif : (if 3 ≤ CFSG.pRank 3 (R : Subgroup Y) then GLBWeakCore 3 (R : Subgroup Y)
        else GLBCore 3 1 E) = GLBWeakCore 3 (R : Subgroup Y) := by
      rw [if_pos (by rw [CFSG.SectionRank.pRank_coe_eq_openPRank]; exact hR3)]
    rw [hif] at hcore
    refine (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore 3 hUR (by omega) ?_).trans
      hcore
    exact hU3r.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_sup_left)
  have hco := psl2GF_borelCoatom 3 3 (by decide) (by norm_num) T'
  have hle : normalizer ((T' : Subgroup (PSL2GF 3 3)) : Set (PSL2GF 3 3)) ≤
      (Y₀.subgroupOf K).map e.toMonoidHom := by
    intro x' hx'
    refine ⟨e.symm x', ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    apply hNU
    rw [Subgroup.mem_normalizer_iff]
    intro v
    by_cases hv : v ∈ K
    · have hconj : ((e.symm x' : K) : Y) * v * ((e.symm x' : K) : Y)⁻¹ ∈ K :=
        hK.conj_mem v hv _
      rw [hmemU v hv, hmemU _ hconj]
      have h1 : e ⟨((e.symm x' : K) : Y) * v * ((e.symm x' : K) : Y)⁻¹, hconj⟩ =
          x' * e ⟨v, hv⟩ * x'⁻¹ := by
        have : (⟨((e.symm x' : K) : Y) * v * ((e.symm x' : K) : Y)⁻¹, hconj⟩ : K) =
            e.symm x' * ⟨v, hv⟩ * (e.symm x')⁻¹ := Subtype.ext (by simp)
        rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [h1]
      exact Subgroup.mem_normalizer_iff.mp hx' _
    · have hconj : ¬ ((e.symm x' : K) : Y) * v * ((e.symm x' : K) : Y)⁻¹ ∈ K := by
        intro h
        apply hv
        have h1 := hK.conj_mem _ h ((e.symm x' : K) : Y)⁻¹
        simpa [mul_assoc] using h1
      exact ⟨fun h => absurd (hUK h) hv, fun h => absurd (hUK h) hconj⟩
  have hne : (Y₀.subgroupOf K).map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hKnle
    intro k hk
    have h1 : e ⟨k, hk⟩ ∈ (Y₀.subgroupOf K).map e.toMonoidHom := htop ▸ Subgroup.mem_top _
    obtain ⟨w, hw, hwk⟩ := h1
    have hw' : w = ⟨k, hk⟩ := e.injective hwk
    rw [hw'] at hw
    exact Subgroup.mem_subgroupOf.mp hw
  have hEq : (Y₀.subgroupOf K).map e.toMonoidHom =
      normalizer ((T' : Subgroup (PSL2GF 3 3)) : Set (PSL2GF 3 3)) :=
    ((hco.le_iff).mp hle).resolve_left hne
  have hUY₀ : U ≤ Y₀ := Subgroup.le_normalizer.trans hNU
  have hY₀U : ∀ g ∈ Y₀, ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hg u hu
    have hvK : g * u * g⁻¹ ∈ K := hK.conj_mem u (hUK hu) g
    have hvY : g * u * g⁻¹ ∈ Y₀ := Y₀.mul_mem (Y₀.mul_mem hg (hUY₀ hu)) (Y₀.inv_mem hg)
    have hv' : e ⟨g * u * g⁻¹, hvK⟩ ∈
        normalizer ((T' : Subgroup (PSL2GF 3 3)) : Set (PSL2GF 3 3)) := by
      rw [← hEq]
      exact ⟨⟨_, hvK⟩, Subgroup.mem_subgroupOf.mpr hvY, rfl⟩
    have hv3 : (e ⟨g * u * g⁻¹, hvK⟩) ^ 3 = 1 := by
      have h1 : (⟨g * u * g⁻¹, hvK⟩ : K) ^ 3 = 1 := by
        apply Subtype.ext
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [conj_pow, hU3 u hu, mul_one, mul_inv_cancel]
      rw [← map_pow, h1, map_one]
    have hzp : IsPGroup 3 (zpowers (e ⟨g * u * g⁻¹, hvK⟩)) := by
      rintro ⟨w, hw⟩
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
      refine ⟨1, Subtype.ext ?_⟩
      simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hv3, one_zpow]
    have hsup := T'.isPGroup'.to_sup_of_normal_left' hzp (zpowers_le.mpr hv')
    have hmax := T'.is_maximal' hsup le_sup_left
    have hmem : e ⟨g * u * g⁻¹, hvK⟩ ∈ (T' : Subgroup (PSL2GF 3 3)) := by
      rw [← hmax]
      exact mem_sup_right (mem_zpowers _)
    exact (hmemU _ hvK).mpr hmem
  have hUn : Y₀ ≤ normalizer (U : Set Y) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hY₀U g hg x hx, fun hx => ?_⟩
    have h1 := hY₀U g⁻¹ (Y₀.inv_mem hg) _ hx
    simpa [mul_assoc] using h1
  have h2C : ∀ g : I₀, (∃ k : ℕ, g ^ 2 ^ k = 1) → σ g ∈ C := by
    rintro g ⟨k, hk⟩
    set t := σ g with ht
    have htS : t ∈ σ.range := ⟨g, rfl⟩
    have htY : t ∈ Y₀ := hσY htS
    obtain ⟨u, hu, hu1, htu⟩ : ∃ u ∈ U, u ≠ 1 ∧ t * u * t⁻¹ = u := by
      by_contra hno
      push Not at hno
      have hUS : U ≤ σ.range :=
        SolvNone.le_of_isSubnormal_of_fixedPointFree hσs hUY₀ hUn htS
          fun u hu h => by_contra fun h1 => hno u hu h1 h
      exact false_of_le_range_of_card σ hb hker hUS hUc hU27 (hσY.trans hUn)
    have hθ : (MulAut.conjNormal t : MulAut K) = 1 := by
      refine CFSG.RankThree.PartTwo.KFacts.eq_one_of_mulAut_of_mulEquiv_psl2_27 e (k := k) ?_
        (x := ⟨u, hUK hu⟩) ?_ ?_ ?_
      · rw [← map_pow, ht, ← map_pow, hk, map_one, map_one]
      · exact Subtype.ext (by simpa using hU3 u hu)
      · intro h
        exact hu1 (by simpa using congrArg Subtype.val h)
      · exact Subtype.ext (by simpa [MulAut.conjNormal_apply] using htu)
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun a : MulAut K => ((a ⟨x, hx⟩ : K) : Y)) hθ
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    have h2 : t * x = x * t := by
      calc t * x = (t * x * t⁻¹) * t := by group
        _ = x * t := by rw [h1]
    exact h2.symm
  exact (Subgroup.map_le_range σ _).trans (range_le_of_forall_two_pow σ hb h2C)

theorem threeFourSolvThreeLTwoTwentySeven_holds : ThreeFourSolvThreeLTwoTwentySeven := by
  intro q d hq3 hqe hd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (⟨q, hd, hq3, hqe⟩ : IsLinTwoIndex 3 3 d)
  exact ThreeFourSolvThreeNoneAt.of_mulEquiv e.symm threeFourSolvThreeNoneAt_psl2_27

theorem threeFourSolvThreeLinTwo_holds : ThreeFourSolvThreeLinTwo :=
  threeFourSolvThreeLinTwo_of threeFourSolvThreeLTwoTwentySeven_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
