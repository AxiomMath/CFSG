module

public import CFSG.GH74.Uniqueness.SU.SU14Rank3
public import CFSG.GH74.Uniqueness.SU.SU8Main
public import CFSG.GH74.Uniqueness.SU.SU10Alt
public import CFSG.GH74.Uniqueness.SU.SU10SL25Cfg

public section

namespace CFSG.GH74.Uniqueness.SU.SU14

open Subgroup CFSG.GH74.Uniqueness.SU.SU8 CFSG.GH74.Uniqueness.Bender CFSG.Blueprint

@[expose] def Prop201CStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S L A : Subgroup G), Hyp20A z S L A →
    center ↥(hbarImage (centralizer ({z} : Set G)) L) = ⊥ →
      ∃ (Y : Type) (_ : Group Y), IsL24 Y ∧
        Nonempty (Hbar (centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Y)

theorem prop201c_of (hU : NoUnitaryStmt) : Prop201CStmt := by
  intro G _ _ z S L A hyp hZ
  have h := (out203 hyp hZ).benderLinear (hU G z S L A hyp hZ)
  obtain ⟨e⟩ := L205.lemma205_of_lin hyp hZ h
  exact ⟨↥(hbarImage (centralizer ({z} : Set G)) L), inferInstance, isL24_of_benderLinear h, ⟨e⟩⟩

theorem exists_elemAb16_of_twoSz8
    (hKI5 : K.KI5b) {X : Type} [Group X] (hK : K.IsTwoSz8 X) :
    ∃ E : Subgroup X, Open.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨hq, hfin, hZcard, ⟨e⟩⟩ := hK
  have := hfin
  have hZp : IsPGroup 2 (center X) := IsPGroup.of_card (n := 1) (by rw [hZcard]; simp)
  have hZne : center X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZcard
    omega
  obtain ⟨hsq5, hcomm6⟩ := hKI5 X hq hZp hZne ⟨e⟩
  have hB : BenderType (X ⧸ center X) (2 * 1 + 1) 2 1 := BenderType.suzuki 1 le_rfl e
  have hr : Open.twoRank (X ⧸ center X) = 2 * 1 + 1 := hB.twoRank_eq
  obtain ⟨Eb, -, hEb, hEbcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two
    (H := (⊤ : Subgroup (X ⧸ center X))) (k := 3) (by unfold Open.twoRank at hr; omega)
  let ρ : X →* (X ⧸ center X) := QuotientGroup.mk' (center X)
  have hρsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hker : ρ.ker = center X := QuotientGroup.ker_mk' _
  have hEcard : Nat.card (Eb.comap ρ) = 16 := by
    have h1 : (Eb.comap ρ).index = Eb.index := Subgroup.index_comap_of_surjective Eb hρsurj
    have h2 : Nat.card (Eb.comap ρ) * (Eb.comap ρ).index = Nat.card X := Subgroup.card_mul_index _
    have h3 : Nat.card Eb * Eb.index = Nat.card (X ⧸ center X) := Subgroup.card_mul_index _
    have h4 : Nat.card X = Nat.card (X ⧸ center X) * Nat.card (center X) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hpos : 0 < Eb.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have e1 : Nat.card X = Nat.card (Eb.comap ρ) * Eb.index := by
      rw [← h1]
      exact h2.symm
    have e2 : Nat.card X = Nat.card Eb * Eb.index * 2 := by
      rw [h4, ← h3, hZcard]
    have e3 : Nat.card (Eb.comap ρ) = 2 * Nat.card Eb :=
      Nat.eq_of_mul_eq_mul_right hpos (by rw [← e1, e2]; ring)
    rw [e3, hEbcard]
    norm_num
  have hEp : IsPGroup 2 (Eb.comap ρ) := IsPGroup.of_card (n := 4) (by rw [hEcard]; norm_num)
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  have hsq : ∀ g ∈ Eb.comap ρ, g ^ 2 ∈ center X := by
    intro g hg
    have h1 : ρ g ∈ Eb := hg
    have h2 : ρ (g ^ 2) = 1 := by
      rw [map_pow]
      exact (SU1.isElemAbelian_iff.mp hEb).2 (ρ g) h1
    have h3 : g ^ 2 ∈ ρ.ker := MonoidHom.mem_ker.mpr h2
    rwa [hker] at h3
  refine ⟨Eb.comap ρ, SU1.isElemAbelian_iff.mpr ⟨fun a ha b hb => ?_, fun a ha => ?_⟩, hEcard⟩
  · exact hcomm6 P a (hEP ha) b (hEP hb) (hsq a ha) (hsq b hb)
  · exact hsq5 P a (hEP ha) (hsq a ha)

theorem prop211_rank3
    (hKI5 : K.KI5b) (hKI6 : K.KI6) (hP201 : Prop201CStmt) :
    Prop211Rank3Stmt := by
  intro G _ _ S M z h hrank3
  have hzH : z ∈ centralizer ({z} : Set G) := SU10.mem_centralizer_self z
  have hHc : ∀ x ∈ centralizer ({z} : Set G), x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp hx
  by_cases hHM : centralizer ({z} : Set G) ≤ M
  · exact Or.inl hHM
  have h21A : ∀ Q : Subgroup G, Q ≤ (S : Subgroup G) → 2 ≤ Open.pRank 2 Q →
      normalizer (Q : Set G) ⊓ centralizer ({z} : Set G) ≤ M := by
    intro Q hQS hQ x hx
    exact h.gamma_le (SU10.normalizer_le_gammaTwo hQS hQ hx.1)
  obtain ⟨hD, K₁, hcomp, -, hC, hcases, -⟩ := SU10.ki6_concl hKI6 h.kgh h.centralizer_ne_top
    h.isSylowIn h.rank h.z_invol hzH hHc h21A hHM
  refine Or.inr ?_
  have hT : ((SU10.sylowMap (SU10.sylowIn h.isSylowIn) :
      Sylow 2 (Hbar (centralizer ({z} : Set G)))) : Subgroup (Hbar (centralizer ({z} : Set G)))) =
      hbarImage (centralizer ({z} : Set G)) (S : Subgroup G) :=
    SU10.coe_sylowMap_sylowIn h.isSylowIn
  have hwT : SU10.zbar z ∈ ((SU10.sylowMap (SU10.sylowIn h.isSylowIn) :
      Sylow 2 (Hbar (centralizer ({z} : Set G)))) : Subgroup (Hbar (centralizer ({z} : Set G)))) := by
    rw [hT]
    exact SU10.zbar_mem_hbarImage h.z_mem
  rcases hcases with ⟨hKn, hSLB, -, hle⟩ | ⟨hSL, K₂, hK₂c, hne, -, hFit, hle⟩ |
      ⟨hK₁top, hK₁alt, hH₀alt⟩ | ⟨hSz, hsup, hle⟩
  ·
    have := hKn
    rcases hSLB with hSL | hBender
    · exact (SU10.sl25_contradiction_normal h hT hSL hC hle).elim
    · obtain ⟨L, hLc, hLn, hL⟩ := SU10.exists_lift_component hcomp hKn
      have hcfg : SU10.BarCfg (Hbar (centralizer ({z} : Set G)))
          (SU10.sylowMap (SU10.sylowIn h.isSylowIn)) (hbarImage (centralizer ({z} : Set G)) L)
          (SU10.zbar z) := by
        rw [hL]
        exact SU10.BarCfg.of_bender _ hBender (SU10.zbar_orderOf h.z_invol)
          (SU10.zbar_central z) hwT hC hle
      have hLb : CFSG.BenderSuzuki.IsBenderGroup ↥(hbarImage (centralizer ({z} : Set G)) L) ∨
          Nonempty ((↥(hbarImage (centralizer ({z} : Set G)) L) ⧸
            center ↥(hbarImage (centralizer ({z} : Set G)) L)) ≃*
              CFSG.Theory.Comparator.SzModel 1) := by
        left
        rw [hL]
        exact hBender
      have hZ : center ↥(hbarImage (centralizer ({z} : Set G)) L) = ⊥ := by
        rw [hL]
        exact SU10.center_eq_bot_of_isBender hBender
      exact Or.inr (hP201 G z (S : Subgroup G) L (omegaOne (S : Subgroup G))
        (SU10.hyp20A_of_barCfg h hLc hLn hLb hT hcfg) hZ)
  ·
    have hcomm' : ⁅K₁, K₂⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hcomp hK₂c).resolve_left (Ne.symm hne)
    have hle12 : K₁ ≤ centralizer (K₂ : Set (Hbar (centralizer ({z} : Set G)))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
    exact (SU10.sl25_contradiction_product h hT hSL
      (fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hle12 ha) b hb).symm) hFit hC hle).elim
  ·
    subst hK₁top
    exact Or.inl (SU10.isTwoAlt_of_mulEquiv Subgroup.topEquiv hK₁alt)
  ·
    exfalso
    obtain ⟨E, hE, hE16⟩ := exists_elemAb16_of_twoSz8 hKI5 hSz
    have hEmap : Open.IsElemAbelian 2 (E.map K₁.subtype) := by
      refine SU1.isElemAbelian_iff.mpr ⟨?_, ?_⟩
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        have hab := (SU1.isElemAbelian_iff.mp hE).1 a ha b hb
        rw [← map_mul, ← map_mul, hab]
      · rintro _ ⟨a, ha, rfl⟩
        have ha2 := (SU1.isElemAbelian_iff.mp hE).2 a ha
        rw [← map_pow, ha2, map_one]
    have hcard : Nat.card (E.map K₁.subtype) = 2 ^ 4 := by
      rw [Subgroup.card_map_of_injective K₁.subtype_injective, hE16]
      norm_num
    have h4 := SU1.le_pRank (p := 2) (by norm_num) (le_top : E.map K₁.subtype ≤ ⊤) hEmap hcard
    have h2 := pRank_sylow_eq_twoRank_hbar S h.S_le_centralizer
    unfold Open.twoRank at h2
    omega

end CFSG.GH74.Uniqueness.SU.SU14
