module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4314
public import CFSG.GH74.QTGen4.DCopy.Quasithin.MS93.ASC134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch4Sec3L43Steps
public import CFSG.Quasithin.Vol2.Ch4Sec3L4314U

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uMat uSL coe_uSL)
open scoped MatrixGroups Matrix Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting4311

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G}
variable (s : Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y)
include s

theorem exists_char_normal_F4 (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h134 : MS93.AS_C_1_34_corr_F4) :
    ∃ C : Subgroup G, C ≤ R₂ ∧ C ≠ ⊥ ∧ (C.subgroupOf R₂).Characteristic ∧
      K ≤ Subgroup.normalizer (C : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  have hP₀ := s.R₂_eq_P₀ h135 hR hC h37 h38 h39
  have hR₂K : R₂ ≤ K := by
    rw [hP₀]
    exact s.P₀_le.trans inf_le_left
  have hKH : K ≤ H := le_of_mem_cComp s.sk.cComp
  have hHloc : pCoreOf 2 H ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal s.sk.base.inM.1.1
  have hsqtk : IsSQTKIn K :=
    IsSQTKIn.mono (sqtkGroup_of_pCoreOf_ne_bot s.sk.base.hyp.qtke s.sk.base.hyp.simple
      s.sk.base.hyp.nonabelian hHloc) hKH
  have hKc : K ∈ cComp K := cComp_mem_of_le s.sk.cComp le_rfl hKH
  have hset : (K : Set G) = (K : Set G) * (R₂ : Set G) := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, 1, R₂.one_mem, mul_one x⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact K.mul_mem ha (hR₂K hb)
  have e : ModO2 K ≃* ↥(StatedSL 3 F) :=
    (QuotientGroup.quotientMulEquivOfEq s.modO2.2.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α s.modO2.1)
  have hrk := isRankTwoLie2Derived_of_equiv_statedSL (by have := s.two_le; omega) s.card_F e

  have hlt : K ⊓ Subgroup.centralizer (ZS : Set G) < K := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    obtain ⟨g₀, hg₀⟩ := SL3Pt.exists_mulVec_e0 (F := F) (p := ![0, 1, 0]) (by
      intro h0
      have := congrFun h0 1
      simp at this)
    obtain ⟨k, hk⟩ := s.modO2.1 (specialLinearGroupEquivStatedSL 3 F g₀)
    have hkC : (k : G) ∈ K ⊓ Subgroup.centralizer (ZS : Set G) := by
      rw [h]
      exact k.2
    have h1 := (mem_stE0 _).mp ((s.mem_centralizer_ZS_iff k.2).mp hkC.2)
    rw [show (⟨(k : G), k.2⟩ : ↥K) = k from rfl, hk, specialLinearGroupEquivStatedSL_coe,
      hg₀] at h1
    have := congrFun h1 0
    simp at this
  have hodd : ¬ 2 ∣ (K ⊓ Subgroup.centralizer (ZS : Set G)).relIndex K := by
    have hsyl := s.isSylowTwoOf_S_inf_K hR hC h37 h38 h39
    have hle : T ⊓ H ⊓ K ≤ K ⊓ Subgroup.centralizer (ZS : Set G) :=
      le_inf inf_le_right s.S_inf_K_le_centralizer_ZS
    intro h2
    apply hsyl.2.2
    have h1 := Subgroup.relIndex_mul_relIndex (T ⊓ H ⊓ K) (K ⊓ Subgroup.centralizer (ZS : Set G))
      K hle inf_le_left
    exact h2.trans (Dvd.intro_left _ h1)
  have hR₂eq : R₂ = pCoreOf 2 (K ⊓ Subgroup.centralizer (ZS : Set G)) := by
    rw [hP₀, s.pCoreOf_centralizer_ZS]
  have hMS : IsMSPair K R₂ :=
    ⟨⟨hsqtk, s.charTwo, K, hKc, hset, hrk⟩, Or.inl ⟨_, hlt, hodd, hR₂eq⟩, hno⟩
  obtain ⟨i, hi⟩ := h134 G K R₂ K hMS hKc hset ⟨m, F, inferInstance, inferInstance, α, s.card_F,
    s.modO2⟩
  have hQ := s.c134Q_K_eq h135 hR hC h37 h38 h39
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact hi
  ·
    obtain ⟨-, n', F', _, _, -, -, α', -, -, β', -, hβ'k, -⟩ := (hi : IsC134Case1 K R₂ K)
    have hinj : Function.Injective β' := by
      rw [← MonoidHom.ker_eq_bot_iff, hβ'k, Subgroup.bot_subgroupOf]
    have := L4314.comm_of_injective hinj
    rw [hQ] at this
    exact s.q4311_not_comm this
  ·
    obtain ⟨⟨n', F', _, _, α', -, -, -, -, β', -, hβ'k, -⟩, -⟩ := (hi : IsC134Case2 K R₂ K)
    have hinj : Function.Injective β' := by
      rw [← MonoidHom.ker_eq_bot_iff, hβ'k, Subgroup.bot_subgroupOf]
    have := L4314.comm_of_injective hinj
    rw [hQ] at this
    exact s.q4311_not_comm this
  ·
    obtain ⟨-, hNC⟩ := (hi : IsC134Case3 K R₂ K)
    refine hNC _ (s.isSylowTwoOf_S_inf_K hR hC h37 h38 h39)
      (s.R₂_le_S_inf_K h135 hR hC h37 h38 h39) ?_
    rw [s.omegaOneCenterOf_S_inf_K h135 hR hC h37 h38 h39, hR₂eq]
  ·
    obtain ⟨⟨n', F', _, _, α', hF', -, hE, -⟩, -⟩ := (hi : MS93.IsC134Case4Corr K R₂ K)
    have hbot : c134CQ K K = ⊥ := by
      rw [eq_bot_iff, ← s.cent]
      intro x hx
      have hxQ : x ∈ q4311 I K := hQ ▸ hx.1
      refine ⟨?_, hx.2⟩
      exact s.sk.pCoreOf_K_le_S hR hC h37 h38 h39
        ((s.pCoreOf_K_eq h135 hR hC h37 h38 h39).symm ▸ hxQ)
    have hcard := L4314Row.card_isE2 hE
    rw [hbot, Subgroup.card_bot] at hcard
    have hn : n' = 0 := by
      have h1 : (2 : ℕ) ^ (2 * n') = 2 ^ 0 := by rw [← hcard, pow_zero]
      have := Nat.pow_right_injective (le_refl 2) h1
      omega
    rw [hn, pow_zero] at hF'
    have := Fintype.one_lt_card (α := F')
    omega
  ·
    obtain ⟨⟨α₅, hα₅, -, -⟩, -⟩ := (hi : IsC134Case5 K R₂ K)
    have hcardSL : Nat.card ↥(StatedSL 3 (ZMod 2)) = Nat.card ↥(StatedSL 3 F) := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α₅ hα₅.1).toEquiv,
        ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α s.modO2.1).toEquiv,
        hα₅.2, s.modO2.2]
    have hcard := card_eq_of_card_statedSL_eq hcardSL
    rw [ZMod.card, s.card_F] at hcard
    have h2 := s.two_le
    have : (2 : ℕ) ^ 1 < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · exact hi

end Setting4311

theorem step4314_holds_F4
    (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (h134 : MS93.AS_C_1_34_corr_F4) : Step4314_F4 := by
  intro G _ _ T M L n I H K t m F _ _ α β W' ZS K₂ R₂ μ y KZ s hKZ hGZ hK₂KZ hKZC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP₀ := s.R₂_eq_P₀ h135 hR hC h37 h38 h39
  have hR2 : IsPGroup 2 ↥R₂ := by
    rw [s.R₂_eq]
    exact pCoreOf_isPGroup 2 _
  have hRN : K₂ ⊔ T ⊓ H ≤ Subgroup.normalizer (R₂ : Set G) := by
    rw [s.R₂_eq]
    exact le_normalizer_pCoreOf 2 _

  have h1 : Subgroup.normalizer (R₂ : Set G) ≤ H ⊓ Subgroup.normalizer (K₂ : Set G) := by
    obtain ⟨C, hCR, hC1, hCc, hKC⟩ := s.exists_char_normal_F4 h135 hR hC h37 h38 h39 h134
    have hNC : Subgroup.normalizer (R₂ : Set G) ≤ Subgroup.normalizer (C : Set G) := by
      have h := normalizer_le_normalizer_map_of_characteristic (C.subgroupOf R₂)
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCR] at h
    have hSC : T ⊓ H ≤ Subgroup.normalizer (C : Set G) :=
      (le_sup_right.trans hRN).trans hNC
    have hNH : Subgroup.normalizer (C : Set G) ≤ H :=
      isUniqueM_normalizer_le (s.isUniqueM_KS h135 hR hC h37 h38 h39 h312) hC1
        (hR2.to_le hCR) (_root_.sup_le hKC hSC)
    intro g hg
    have hgH : g ∈ H := hNH (hNC hg)
    refine ⟨hgH, ?_⟩

    have hZ : centerOf R₂ = ZS := by
      refine s.centerOf_eq_ZS h135 hR hC h37 h38 h39 le_rfl ?_ ?_
      · rw [hP₀]
        exact s.P₀_le.trans inf_le_left
      · rw [hP₀]
        exact s.P₀_le.trans inf_le_right
    have hgZ : g ∈ Subgroup.normalizer (ZS : Set G) := by
      rw [← hZ]
      exact mem_normalizer_inf hg (A4.mem_normalizer_centralizer hg)
    have hgK := s.H_le_normalizer_K hR hC h37 h38 h39 hgH
    rw [s.K₂_eq]
    exact normalizer_le_normalizer_perfectCore _
      (mem_normalizer_inf hgK (A4.mem_normalizer_centralizer hgZ))

  have hRKZ : R₂ ≤ KZ ⊔ T := by
    rw [s.R₂_eq]
    exact (pCoreOf_le 2 _).trans (_root_.sup_le (hK₂KZ.trans le_sup_left)
      (inf_le_left.trans le_sup_right))

  set X := (KZ ⊔ T) ⊓ Subgroup.normalizer (R₂ : Set G) with hX
  have hK₂X : K₂ ≤ X := le_inf (hK₂KZ.trans le_sup_left) (le_sup_left.trans hRN)
  have h2 : R₂ = pCoreOf 2 X := by
    apply le_antisymm
    · exact le_pCoreOf_of_le_normalizer 2 (le_inf hRKZ Subgroup.le_normalizer) inf_le_right hR2
    · intro x hx
      have hxX : x ∈ X := pCoreOf_le 2 X hx
      have hxN := h1 hxX.2
      have hO2 : IsPGroup 2 ↥(pCoreOf 2 X) := pCoreOf_isPGroup 2 X
      have hOK : pCoreOf 2 X ⊓ K₂ ≤ pCoreOf 2 K₂ :=
        le_pCoreOf_of_le_normalizer 2 inf_le_right
          (fun k hk => mem_normalizer_inf (le_normalizer_pCoreOf 2 X (hK₂X hk))
            (Subgroup.le_normalizer hk)) (hO2.to_le inf_le_left)
      rw [hP₀]
      refine s.mem_P₀_of h135 hR hC h37 h38 h39 hxN.1 ?_ (hP₀ ▸ hxX.2) fun k hk => ?_
      · obtain ⟨a, ha⟩ := hO2 ⟨x, hx⟩
        exact ⟨a, by simpa using congrArg Subtype.val ha⟩
      · apply s.pCoreOf_K₂_le_P₀
        apply hOK
        refine ⟨?_, ?_⟩
        · have hk' : k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 X :=
            (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 X (hK₂X hk)) x⁻¹).mp
              ((pCoreOf 2 X).inv_mem hx)
          have := (pCoreOf 2 X).mul_mem hx hk'
          simpa [mul_assoc] using this
        · have h3 : x * k * x⁻¹ ∈ K₂ := (Subgroup.mem_normalizer_iff.mp hxN.2 k).mp hk
          exact K₂.mul_mem h3 (K₂.inv_mem hk)

  have h3 : pCoreOf 2 (KZ ⊔ T) ≤ R₂ := by
    set O := pCoreOf 2 (KZ ⊔ T) with hO
    have hRO : R₂ ≤ Subgroup.normalizer (O : Set G) :=
      hRKZ.trans (le_normalizer_pCoreOf 2 (KZ ⊔ T))
    have hP2 : IsPGroup 2 ↥(O ⊔ R₂) :=
      IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup 2 _) hR2 hRO

    have hON' : O ⊓ Subgroup.normalizer (R₂ : Set G) ≤ pCoreOf 2 X :=
      le_pCoreOf_of_le_normalizer 2 (inf_le_inf_right _ (pCoreOf_le 2 (KZ ⊔ T)))
        (fun g hg => mem_normalizer_inf (le_normalizer_pCoreOf 2 (KZ ⊔ T) hg.1)
          (Subgroup.le_normalizer hg.2)) ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
    have hON : O ⊓ Subgroup.normalizer (R₂ : Set G) ≤ R₂ := hON'.trans h2.ge
    by_contra hnot
    have hlt : R₂ < O ⊔ R₂ := lt_of_le_of_ne le_sup_right fun h => hnot (h ▸ le_sup_left)
    obtain ⟨w, hw, hwN, hwR⟩ := A4.exists_mem_normalizer_not_mem hP2 hlt
    have hw' : w ∈ (O : Set G) * (R₂ : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left O R₂ hRO]
      exact hw
    obtain ⟨o, ho, r, hr, rfl⟩ := hw'
    have hoN : o ∈ Subgroup.normalizer (R₂ : Set G) := by
      have := Subgroup.mul_mem _ hwN (Subgroup.inv_mem _ (Subgroup.le_normalizer hr))
      simpa using this
    exact hwR (R₂.mul_mem (hON ⟨ho, hoN⟩) hr)
  exact ⟨h1, h2, h3, hP₀⟩

end CFSG.Quasithin.H13.Ch4
