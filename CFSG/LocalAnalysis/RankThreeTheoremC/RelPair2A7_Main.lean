module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Quot

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_pRank_of_isElemAbelian' {p : ℕ} (hp : 1 < p) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H :=
  CFSG.SectionRank.le_pRank hp hEH hE hk

theorem isElemAbelian_map {A B : Type} [Group A] [Group B] {p : ℕ} (f : A →* B) {E : Subgroup A}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := CFSG.SectionRank.isElemAbelian_map hE _

theorem le_of_isSylowOf_of_normalizer {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {P K T : Subgroup Y} (hP : CFSG.ABGLocalTools.IsSylowOf p P K)
    (hKP : K ≤ normalizer (P : Set Y)) (hTK : T ≤ K) (hT : IsPGroup p T) : T ≤ P := by
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hQn : (Q : Subgroup K).Normal := by
    rw [hQ]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hP.le).mpr hKP
  have hT' : IsPGroup p (T.subgroupOf K) := hT.comap_subtype
  obtain ⟨Q', hTQ'⟩ := hT'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  have hQQ' : Q' = Q := by
    have := hQn
    rw [← hg]
    exact Sylow.smul_eq_of_normal
  intro x hx
  have h1 : (⟨x, hTK hx⟩ : K) ∈ T.subgroupOf K := hx
  have h2 := hTQ' h1
  rw [hQQ', hQ] at h2
  exact h2

theorem IsOptimalRelPair.a7_structure {p : ℕ} {P : Sylow p G} {M D R T H V : Subgroup G}
    (hd : MaximalRelativePair p P M D R T) (hopt : IsOptimalRelPair p M D R T H V)
    (hfacts : OptimalRelPairFacts p M D H V) (hp3 : p = 3)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (e : L ⧸ center L ≃* alternatingGroup (Fin 7)) :
    Nat.card V = 4 * Nat.card (pCoreOf 2 H) ∧ ∃ n ∈ H, n ∈ normalizer (D : Set G) ∧
      p ∣ Nat.card (V ⊔ V.map (MulAut.conj n).toMonoidHom : Subgroup G) := by
  subst hp3
  have hprime : (3 : ℕ).Prime := Nat.prime_three
  have hfact : Fact (Nat.Prime 3) := ⟨hprime⟩
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hopt.pair.cand.base_le
  have hVH : V ≤ H := hfacts.maximal.1
  set K : Subgroup ↥H := primeComplementCore (G := ↥H) 3 with hK
  set Dy : Subgroup ↥H := D.subgroupOf H with hDy
  set Vy : Subgroup ↥H := V.subgroupOf H with hVy
  have hDp : IsPGroup 3 D := P.isPGroup'.to_le hd.ext.obstruction.2.1
  have hDy3 : IsPGroup 3 Dy := hDp.of_equiv (Subgroup.subgroupOfEquivOfLe hDH).symm
  have hDcard : Nat.card D = 9 := by
    have := (hd.ext.isElemAbelian_of_isMulCommutative hprime hd.abelian).2
    simpa using this
  have hDy9 : Nat.card Dy = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv).trans hDcard
  have hVyM : rankTwoMaximalInvariantTwoSubgroup Dy Vy :=
    invariantTwoMaximalWithin_internal_global D H V hDH hfacts.maximal
  have hKc : (3 : ℕ).Coprime (Nat.card K) := primeComplementCore_coprime 3
  have hKmax : ∀ N : Subgroup ↥H, N.Normal → (3 : ℕ).Coprime (Nat.card N) → N ≤ K :=
    fun N hN hc => normal_coprime_le_primeComplementCore 3 N hN hc
  have h3 : CFSG.pCore 3 (↥H ⧸ K) = ⊥ := by
    exact hfacts.pCore_quotient
  have hrk : ∀ E : Subgroup ↥H, IsElemAbelian 3 E → Nat.card E ≤ 9 := by
    intro E hE
    have hEp : IsPGroup 3 E := fun x => ⟨1, by
      have := hE.2 x x.2
      exact Subtype.ext (by simpa using this)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hEG : IsElemAbelian 3 (E.map H.subtype) := isElemAbelian_map H.subtype hE
    have hcardG : Nat.card (E.map H.subtype) = 3 ^ k := by
      rw [Subgroup.card_map_of_injective H.subtype_injective, hk]
    have hk2 : k ≤ 2 := by
      have := le_pRank_of_isElemAbelian' hprime.one_lt (Subgroup.map_subtype_le E) hEG hcardG
      rwa [hfacts.pRank_eq] at this
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  have hJ : CFSG.IsComponent L := (CFSG.isComponent_iff_open L).mpr hL
  obtain ⟨hcard, m, hm, hjoin⟩ :=
    a7_quotient_structure hKc hKmax h3 hrk hJ e hDy9 hDy3 hVyM
  set O : Subgroup ↥H := CFSG.Open.pCore 2 ↥H with hO
  have hOG : pCoreOf 2 H = O.map H.subtype := rfl
  have hSylY : CFSG.ABGLocalTools.IsSylowOf 2 O K :=
    (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H).mp hfacts.sylow
  have hOn : K ≤ normalizer (O : Set ↥H) := by
    have : O.Normal := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2
    exact fun x _ => Subgroup.mem_normalizer_iff.mpr fun y => by
      constructor <;> intro hy
      · exact this.conj_mem y hy x
      · have h := this.conj_mem _ hy x⁻¹
        rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h
  have hOV : O ≤ Vy := by
    have := hfacts.pCore_le
    rw [hOG] at this
    exact (Subgroup.map_le_iff_le_comap).mp this
  have hVyK : Vy ⊓ K = O := by
    apply le_antisymm
    · exact le_of_isSylowOf_of_normalizer hSylY hOn inf_le_right
        (hVyM.1.to_inf_left)
    · exact le_inf hOV hSylY.le
  refine ⟨?_, ?_⟩
  · have h1 : Nat.card V = Nat.card Vy :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv).symm
    have h2 : Nat.card (pCoreOf 2 H) = Nat.card O := by
      rw [hOG, Subgroup.card_map_of_injective H.subtype_injective]
    rw [h1, h2, hcard, hVyK]
  · refine ⟨(m : G), m.2, ?_, ?_⟩
    · have hmN : m ∈ normalizer ((D.subgroupOf H : Subgroup ↥H) : Set ↥H) := hm
      rw [← Subgroup.subgroupOf_normalizer_eq hDH] at hmN
      exact hmN
    · have hVV : Vy.map H.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVH
      have hmap : (Vy ⊔ Vy.map (MulAut.conj m).toMonoidHom : Subgroup ↥H).map H.subtype =
          V ⊔ V.map (MulAut.conj (m : G)).toMonoidHom := by
        rw [Subgroup.map_sup, Subgroup.map_map, hVV]
        have : H.subtype.comp (MulAut.conj m).toMonoidHom =
            (MulAut.conj (m : G)).toMonoidHom.comp H.subtype := by
          ext x
          simp [MulAut.conj_apply]
        rw [this, ← Subgroup.map_map, hVV]
      have hc := Subgroup.card_map_of_injective H.subtype_injective
        (K := (Vy ⊔ Vy.map (MulAut.conj m).toMonoidHom : Subgroup ↥H))
      rw [hmap] at hc
      rw [hc]
      exact hjoin

omit [Finite G] in
theorem map_conj_map_conj_inv (K : Subgroup G) (n : G) :
    (K.map (MulAut.conj n).toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom = K := by
  rw [Subgroup.map_map]
  have : (MulAut.conj n⁻¹).toMonoidHom.comp (MulAut.conj n).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply]
    group
  rw [this, Subgroup.map_id]

omit [Finite G] in
theorem map_conj_conj_eq {S : Subgroup G} {n : G} (hn : n ∈ normalizer (S : Set G)) (g : G) :
    S.map (MulAut.conj (n⁻¹ * g * n)).toMonoidHom =
      (S.map (MulAut.conj g).toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom := by
  ext x
  rw [mem_map_conj_iff_implicit, mem_map_conj_iff_implicit, mem_map_conj_iff_implicit]
  have h1 := mem_normalizer_iff.mp hn ((n⁻¹ * g * n)⁻¹ * x * (n⁻¹ * g * n))
  have h2 : n * ((n⁻¹ * g * n)⁻¹ * x * (n⁻¹ * g * n)) * n⁻¹ = g⁻¹ * (n * x * n⁻¹) * g := by
    group
  rw [h1, h2]
  have h3 := mem_normalizer_iff.mp hn (g⁻¹ * (n * x * n⁻¹) * g)
  have h4 : (n⁻¹)⁻¹ * x * n⁻¹ = n * x * n⁻¹ := by group
  rw [h4]

omit [Finite G] in
theorem mem_normalizer_map_conj_iff (K : Subgroup G) (n g : G) :
    g ∈ normalizer ((K.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) ↔
      n⁻¹ * g * n ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h y
    have := h (n * y * n⁻¹)
    rw [mem_map_conj_iff_implicit, mem_map_conj_iff_implicit] at this
    simpa [mul_assoc] using this
  · intro h z
    have := h (n⁻¹ * z * n)
    rw [mem_map_conj_iff_implicit, mem_map_conj_iff_implicit]
    simpa [mul_assoc] using this

@[expose] def GL83RelPair2A7B (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D R T H V : Subgroup G),
    MaximalRelativePair p P M D R T → IsOptimalRelPair p M D R T H V →
      OptimalRelPairFacts p M D H V → p = 3 →
        ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
          Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) →
            Nat.card V = 4 * Nat.card (pCoreOf 2 H) →
              (∃ T' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup D T' ∧ V < T') ∧
                ∃ S₁ : Subgroup G, ∀ g ∈ normalizer (V : Set G),
                  (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom = pCoreOf 2 H ∨
                    (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom = S₁

theorem gl83RelPair2A7_of_B (hB : GL83RelPair2A7B G) : GL83RelPair2A7 G := by
  intro p hp P M D R T H V hd hopt hfacts hp3 L hL hLA
  obtain ⟨e⟩ := hLA
  obtain ⟨hcard, n, hnH, hnD, hjoin⟩ := hopt.a7_structure hd hfacts hp3 hL e
  obtain ⟨⟨T', hT', hVT'⟩, S₁, hS₁⟩ := hB p hp P M D R T H V hd hopt hfacts hp3 L hL ⟨e⟩ hcard
  have hnS : n ∈ normalizer ((pCoreOf 2 H : Subgroup G) : Set G) := by
    rw [hfacts.normalizer_pCore]
    exact hnH
  refine ⟨hcard, n, hnH, hnD, hjoin, ⟨T', hT', hVT'⟩, S₁.map (MulAut.conj n).toMonoidHom, ?_⟩
  intro g hg
  have hg' : n⁻¹ * g * n ∈ normalizer (V : Set G) := (mem_normalizer_map_conj_iff V n g).mp hg
  have hS : (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom =
      ((pCoreOf 2 H).map (MulAut.conj (n⁻¹ * g * n)).toMonoidHom).map
        (MulAut.conj n).toMonoidHom := by
    rw [map_conj_conj_eq hnS g, Subgroup.map_map]
    have : (MulAut.conj n).toMonoidHom.comp (MulAut.conj n⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply]
      group
    rw [this, Subgroup.map_id]
  rw [hS]
  have hSn : (pCoreOf 2 H).map (MulAut.conj n).toMonoidHom = pCoreOf 2 H := by
    have := mem_normalizer_iff_map_conj_eq.mp hnS
    exact this
  rcases hS₁ _ hg' with h | h
  · left
    rw [h, hSn]
  · right
    rw [h]

theorem gl83RelativePairExclusion_of_relPair2A7 (hS : Setting G) (hD1 : TheoremD1 G)
    (hK : KFactLemma212) (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hT : GL83RelPair2Thompson G) (hB : GL83RelPair2A7B G) : GL83RelativePairExclusion G :=
  gl83RelativePairExclusion_of_relPair2 hS hD1 hK hR h13 hT (gl83RelPair2A7_of_B hB)

end CFSG.LocalAnalysis.RankThreeTheoremC
