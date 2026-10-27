module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedTenFourteenThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySeven
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111WeakCore
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111AltSixIrred
public import CFSG.Goldschmidt.Steps.Sec82e
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

variable (G) in
@[expose] def AGL81ElevenElevenParabolic : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    AGL81CfgData 3 P M H Q K → IsAltTwoP 3 K → ¬ HasPrimeConstraint (G := H) 3 →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    jZero H L ≤ d1PlusCore 3 H K →
    (∀ b ∈ d1LiftX 3 H Q K, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) →
    H ⊓ Subgroup.normalizer (d1LiftX 3 H Q K : Set G) ≤ M →
    (∀ V : Subgroup G, V ≤ d1LiftX 3 H Q K → V ≠ ⊥ →
      H ⊓ Subgroup.normalizer (d1LiftX 3 H Q K : Set G) ≤ Subgroup.normalizer (V : Set G) →
      V = d1LiftX 3 H Q K) →
    ¬ 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L →
    ⁅d1LiftX 3 H Q K, L⁆ ≤ pCoreOf 2 L

theorem le_normalizer_d1PlusCore_of_map_le {p : ℕ} {H B : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hBH : B ≤ H)
    (hBK : (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ K) :
    B ≤ Subgroup.normalizer (d1PlusCore p H K : Set G) := by
  have hconj : ∀ a : H, QuotientGroup.mk' (primeComplementCore (G := H) p) a ∈ K →
      ∀ x ∈ d1PlusCore p H K, (a : G) * x * (a : G)⁻¹ ∈ d1PlusCore p H K := by
    rintro a ha _ ⟨h, hh, rfl⟩
    refine ⟨a * h * a⁻¹, ?_, by simp⟩
    have hh' : QuotientGroup.mk' (primeComplementCore (G := H) p) h ∈
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := hh
    have hc := Subgroup.mem_centralizer_iff.mp hh' _ ha
    show QuotientGroup.mk' (primeComplementCore (G := H) p) (a * h * a⁻¹) ∈
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
    rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
    exact hh'
  intro b hb
  have hbK : QuotientGroup.mk' (primeComplementCore (G := H) p) (⟨b, hBH hb⟩ : H) ∈ K :=
    hBK ⟨⟨b, hBH hb⟩, hb, rfl⟩
  have hbK' : QuotientGroup.mk' (primeComplementCore (G := H) p) (⟨b, hBH hb⟩⁻¹ : H) ∈ K := by
    rw [map_inv]
    exact K.inv_mem hbK
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hconj _ hbK x hx, fun hx => ?_⟩
  have := hconj _ hbK' _ hx
  simpa [mul_assoc] using this

theorem d1LiftX_facts_cfg {P : Sylow 3 G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hd : AGL81CfgData 3 P M H Q K)
    (hA6 : IsAltTwoP 3 K) :
    d1LiftX 3 H Q K ⊓ d1PlusCore 3 H K = ⊥ ∧ IsElemAbelian 3 (d1LiftX 3 H Q K) ∧
      Nat.card (d1LiftX 3 H Q K) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := primeComplementCore (G := H) 3 with hOdef
  set π := QuotientGroup.mk' O with hπ
  set A := d1LiftX 3 H Q K with hA
  have hAR : A ≤ Q := d1LiftX_le 3 H Q K
  have hAH : A ≤ H := hAR.trans hd.le_H
  set A' := A.subgroupOf H with hA'
  have hA'3 : IsPGroup 3 A' := (hd.base.2.1.to_le hAR).comap_subtype
  have hAO : A' ⊓ O = ⊥ := by
    obtain ⟨n, hn⟩ := hA'3.exists_card_eq
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hn]
    exact (primeComplementCore_coprime (G := H) 3).pow_left n
  have hinj : ∀ a ∈ A', π a = 1 → a = 1 := fun a ha h1 => by
    have hO : a ∈ O := (QuotientGroup.eq_one_iff a).mp h1
    have : a ∈ A' ⊓ O := ⟨ha, hO⟩
    rwa [hAO, Subgroup.mem_bot] at this
  obtain ⟨e⟩ := hA6
  have hZ : ∀ k : K, (∀ k' : K, k * k' = k' * k) → k = 1 := by
    intro k hk
    have hc : e k ∈ Subgroup.center (alternatingGroup (Fin (2 * 3))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hk k']
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
    exact (map_eq_one_iff e e.injective).mp hc
  refine ⟨?_, ?_⟩
  ·
    rw [eq_bot_iff]
    rintro x ⟨⟨a, ⟨haR, haK⟩, rfl⟩, ⟨b, hbC, hba⟩⟩
    have hab : b = a := Subtype.ext hba
    subst hab
    have hz : π b = 1 := by
      have := hZ ⟨π b, haK⟩ fun k' =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp hbC) k' k'.2).symm
      exact congrArg Subtype.val this
    have hbA : b ∈ A' := by
      show (b : G) ∈ A
      exact ⟨b, ⟨haR, haK⟩, rfl⟩
    rw [Subgroup.mem_bot, hinj b hbA hz]
    rfl
  ·
    obtain ⟨S, hS⟩ := hd.sylowK
    have hmap : A'.map π = (S : Subgroup K).map K.subtype := by
      rw [hS, hA', hA, map_d1LiftX]
    set φ : A' →* H ⧸ O := π.comp A'.subtype with hφ
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro a ha
      exact Subtype.ext (hinj a a.2 ha)
    have hφr : φ.range = (S : Subgroup K).map K.subtype := by
      rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype, hmap]
    let f : A ≃* S :=
      ((Subgroup.subgroupOfEquivOfLe hAH).symm.trans (MonoidHom.ofInjective hφinj)).trans
        ((MulEquiv.subgroupCongr hφr).trans
          (Subgroup.equivMapOfInjective (S : Subgroup K) K.subtype K.subtype_injective).symm)
    obtain ⟨hSe, hS9⟩ := isElemAbelian_sylow_of_isAltTwoP ⟨e⟩ S
    refine ⟨⟨⟨⟨fun a b => f.injective ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
    · rw [map_mul, map_mul]
      exact isMulCommutative_iff.mp hSe.1 _ _
    · have h1 : f (⟨x, hx⟩ ^ 3) = 1 := by
        rw [map_pow]
        exact Subtype.ext (hSe.2 _ (f ⟨x, hx⟩).2)
      have h2 := (map_eq_one_iff f f.injective).mp h1
      simpa using congrArg Subtype.val h2
    · rw [Nat.card_congr f.toEquiv, hS9]

theorem agl81ElevenElevenCfg_of (h7 : AGL81ElevenSevenCfgThree G) (hX : AGL81NineThreeXCfg G)
    (h1033 : AGL81TenThreeThreeCfg G) (hPar : AGL81ElevenElevenParabolic G)
    (h1014 : AGL81TenFourteenThreeCfg G) (h10C : AGL81TenOneCZero G) (h91 : AGL81TenNineOneCfg G)
    (h1031 : AGL81TenThreeOneAt G) : AGL81ElevenElevenCfg G := by
  intro hS P M H Q K hσ hd hA6 hnc L hL hLn hno
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hcore : GLBWeakCore 3 (P : Subgroup G) ≤ M := hesc.weakCore_le
  set X := d1PlusCore 3 H K with hXdef
  set A := d1LiftX 3 H Q K with hAdef
  obtain ⟨hAX, hAe, hAc⟩ := d1LiftX_facts_cfg hd hA6
  have hAc' : Nat.card A = 3 ^ 2 := by rw [hAc]; norm_num
  have hAQ : A ≤ Q := d1LiftX_le 3 H Q K
  have hAH : A ≤ H := hAQ.trans hd.le_H
  have hAM : A ≤ M := hAQ.trans hd.base.1
  have hA3 : IsPGroup 3 A := hd.base.2.1.to_le hAQ
  have hXM : X ≤ M := hX hS 3 P M H Q K hd
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  obtain ⟨-, hXr, hJ0, hAJ⟩ := h7 hS P M H Q K hσ hd hnc L hL hLn hno
  have hJX : jZero H L ≤ X := by
    refine hJ0.resolve_right fun h => ?_
    have h1 := Hyp111.card_of_isLinThreeFour h
    rw [card_of_isAltTwoP_three hA6] at h1
    norm_num at h1
  have hAJ' := hAJ hJX
  have h3X : 3 ∣ Nat.card X := by
    obtain ⟨E₀, hE₀X, -, hE₀c⟩ := pRank_attained 3 hp X
    rw [hXr, pow_one] at hE₀c
    exact hE₀c ▸ Subgroup.card_dvd_of_le hE₀X
  have hAXn : A ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_d1PlusCore_of_map_le hAH (by rw [hAdef, map_d1LiftX]; exact inf_le_right)
  obtain ⟨z, hzX, hz3, hzc⟩ := exists_centralizing_of_three_dvd hA3 hAXn h3X
  have hzA : z ∉ A := fun hzA => by
    have : z ∈ A ⊓ X := ⟨hzA, hzX⟩
    rw [hAX, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hz3
    norm_num at hz3
  have hzM : z ∈ M := hXM hzX
  have hz3' : z ^ 3 = 1 := hz3 ▸ pow_orderOf_eq_one z
  obtain ⟨hEe, hEc⟩ := CFSG.Goldschmidt.Sec82.isElemAbelian_sup_zpowers hp hAc' hAe.2 hz3' hzA
    (fun a ha => hzc a ha)
  set E := A ⊔ Subgroup.zpowers z with hEdef
  have hEM : E ≤ M := sup_le hAM ((Subgroup.zpowers_le).mpr hzM)
  have hEQ : IsAGLQ 3 M E :=
    ⟨hEM, CFSG.Open.IsElemAbelian.isPGroup hEe,
      Or.inl (by
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
        exact CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEe hEc)⟩
  have hA2 : 2 ≤ Open.pRank 3 A := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hAe hAc'
  have hNA : Subgroup.normalizer (A : Set G) ≤ M :=
    normalizer_le_of_central hcore hAM hA3 hA2 hzM hz3 hzA fun a ha => (hzc a ha).symm
  have hirr : ∀ V : Subgroup G, V ≤ A → V ≠ ⊥ →
      H ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (V : Set G) → V = A := by
    intro V hVA hV1 hVn
    obtain ⟨S, hS'⟩ := hd.sylowK
    refine eq_of_le_of_normalizer_le hA6 hAH hA3 ⟨S, ?_⟩ hVA hV1 hVn
    rw [hS', hAdef, map_d1LiftX]
  have hAL : ⁅A, L⁆ ≤ pCoreOf 2 L := by
    rcases h1033 hS 3 P M H Q K hd L hL hLn A (le_inf hAH hAM) hA3 hAJ' with hc | hodd
    · rw [Subgroup.commutator_le]
      intro a ha l hl
      rw [commutatorElement_def]
      refine inf_pCoreOf_le hL.le ⟨?_, hc a ha l hl⟩
      have hal : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hMn (hAM ha)) l).mp hl
      exact L.mul_mem hal (L.inv_mem hl)
    · exact hPar hS P M H Q K hd hA6 hnc L hL hLn hJX hAJ' (inf_le_right.trans hNA) hirr hodd
  obtain ⟨I₀, hI₀⟩ := h10C hS 3 P M H Q K hd L hL (h91 hS 3 P M H Q K hd L hL)
  have h3L : 3 ∣ Nat.card L := (h1031 hS 3 P M H Q K hd L hL I₀ hI₀).trans
    (Subgroup.card_dvd_of_le ((IsCZeroMember.oUpperTwo_le_jOne hI₀).trans
      ((jOne_le_jZero H L).trans ((jZero_le H L).trans inf_le_right))))
  have hcent : ∀ a ∈ A, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≤ M := by
    intro a ha ha1
    by_contra hCM
    have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a ha) ha1
    refine h1014 hS P M H Q K hd L hL h3L a (hAM ha) ha3 hCM ⟨E, ?_, hEQ⟩
      ((Subgroup.commutator_mono ((Subgroup.zpowers_le).mpr ha) le_rfl).trans hAL)
    refine sup_le (fun b hb => Subgroup.mem_centralizer_iff.mpr ?_) ?_
    · rintro x rfl
      exact congrArg Subtype.val (isMulCommutative_iff.mp hAe.1 ⟨x, ha⟩ ⟨b, hb⟩)
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      rintro x rfl
      exact hzc x ha
  exact ⟨isAGLQ_of_centralizers hcore hAM hA3 le_rfl hAe hAc' hz3 hzA
    (fun a ha => (hzc a ha).symm) hcent, hAL⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
