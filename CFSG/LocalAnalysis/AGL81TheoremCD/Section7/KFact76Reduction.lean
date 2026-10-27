module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76RankThree
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76Rows
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76ReductionTools
import CFSG.RankThree.PartTwo.Sec4.RonanK432Transfer
import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open CFSG.RankThree.PartTwo.Sec4

theorem zpowers_normal_of_no_component {G : Type} [Group G] [Finite G]
    (hO : CFSG.pPrimeCore 3 G = ⊥) {z : G} (hz : orderOf z = 3)
    (hwc : ∀ g : G, (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) →
      (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers z)
    (hno : ∀ L : Subgroup G, CFSG.IsComponent L →
      ¬ L ≤ Subgroup.normalClosure ((Subgroup.zpowers z : Subgroup G) : Set G)) :
    (Subgroup.zpowers z).Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.zpowers z with hZ
  set H := Subgroup.normalClosure (Z : Set G) with hH
  have hZH : Z ≤ H := Subgroup.le_normalClosure
  have hlayer : CFSG.layer H = ⊥ := by
    apply sSup_eq_bot.mpr
    intro K hK
    exact (hno _ (Item432Proof.isComponent_map_subtype hK) (Subgroup.map_subtype_le K)).elim
  have hcore : CFSG.pPrimeCore 3 H = ⊥ := by
    have hsub : ((CFSG.pPrimeCore 3 H).map H.subtype).IsSubnormal :=
      (CFSG.pPrimeCore_normal (p := 3) (G := H)).isSubnormal.trans'
        (Subgroup.normalClosure_normal).isSubnormal
    have hcop : Nat.Coprime 3 (Nat.card ((CFSG.pPrimeCore 3 H).map H.subtype)) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hle := GH74.GLS.le_pPrimeCore_of_subnormal 3 hsub hcop
    rw [hO, le_bot_iff] at hle
    exact Subgroup.map_injective H.subtype_injective (by rw [hle, Subgroup.map_bot])
  have hchar := CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot H 3 hcore hlayer
  set O₃ := (CFSG.pCore 3 H).map H.subtype with hO₃
  have hO₃n : O₃.Normal := Item432Proof.map_subtype_normal_of_characteristic (CFSG.pCore 3 H)
  have hO₃p : IsPGroup 3 O₃ := (CFSG.pCore_isPGroup (p := 3) (G := H)).map _
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hsup : IsPGroup 3 (Z ⊔ O₃ : Subgroup G) := hZp.to_sup_of_normal_right hO₃p
  have hcen := Item432Proof.le_centralizer_of_isPGroup hz hwc hsup
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have hZO : Z ≤ O₃ := by
    intro x hx
    have hxH : x ∈ H := hZH hx
    have h1 : (⟨x, hxH⟩ : H) ∈ Subgroup.centralizer ((CFSG.pCore 3 H : Subgroup H) : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      have hyO : (y : G) ∈ O₃ := ⟨y, hy, rfl⟩
      have h2 := Subgroup.mem_centralizer_iff.mp (hcen (Subgroup.mem_sup_right hyO)) x hx
      exact h2.symm
    exact ⟨_, hchar h1, rfl⟩
  refine ⟨fun x hx g => ?_⟩
  have hle : Z.map (MulAut.conj g).toMonoidHom ≤ O₃ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hO₃n.conj_mem _ (hZO hy) g
  have heq := Item432Proof.map_conj_eq_of_le hwc hO₃p hZO hle
  have hmem : g * x * g⁻¹ ∈ Z.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rwa [heq] at hmem

theorem pRank_fixed_le_two_of_not_mem {G : Type} [Group G] [Finite G] {H L : Subgroup G}
    {z : G} (hzN : z ∈ Subgroup.normalizer (L : Set G)) (hz3 : z ^ 3 = 1) (hzL : z ∉ L)
    (hLH : L ≤ H) (hzH : z ∈ H) (hH : CFSG.Open.pRank 3 H ≤ 3) :
    CFSG.Open.pRank 3
      ((L.normalizerMonoidHom ⟨z, hzN⟩).toMonoidHom.eqLocus (MonoidHom.id L)) ≤ 2 := by
  set C := (L.normalizerMonoidHom ⟨z, hzN⟩).toMonoidHom.eqLocus (MonoidHom.id L) with hC
  obtain ⟨E, hEC, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) C
  have hzC : z ∈ Subgroup.centralizer ((E.map L.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    have h0 : L.normalizerMonoidHom ⟨z, hzN⟩ e = e := hEC he
    have h1 : z * (e : G) * z⁻¹ = e := by
      rw [← normalizerMonoidHom_apply_coe hzN e, h0]
    calc (e : G) * z = z * e * z⁻¹ * z := by rw [h1]
      _ = z * e := by group
  have h : CFSG.Open.pRank 3 C + 1 ≤ CFSG.Open.pRank 3 H :=
    CFSG.AGLEmbedding.succ_le_pRank_of_isElemAbelian_of_mem_centralizer Nat.prime_three
      (CFSG.SectionRank.isElemAbelian_map hE L.subtype)
      (by rw [Subgroup.card_map_of_injective L.subtype_injective, hcard]) hz3
      (fun hzE => hzL (Subgroup.map_subtype_le E hzE)) hzC
      ((Subgroup.map_subtype_le E).trans hLH) hzH
  omega

theorem kFact76RankThree_of_rows (hrow : Rows76RankThree) : KFact76RankThree := by
  intro Y _ _ hK hO A hA hwc hbd
  obtain ⟨z, hz, rfl⟩ := Item432Proof.exists_zpowers_eq hA
  set H := Subgroup.normalClosure ((Subgroup.zpowers z : Subgroup Y) : Set Y) with hH
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  by_cases hex : ∃ L : Subgroup Y, CFSG.IsComponent L ∧ L ≤ H
  ·
    obtain ⟨L₀, hL₀, hL₀H⟩ := hex
    obtain ⟨L, hL, hLH, hZC⟩ := Item432Proof.exists_component_not_le_centralizer hL₀ hL₀H
    have hzN := Item432Proof.mem_normalizer_of_isComponent hO hz hwc hL
    set σ := L.normalizerMonoidHom ⟨z, hzN⟩ with hσ
    have hσ3 : σ ^ 3 = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨z, hzN⟩ : Subgroup.normalizer (L : Set Y)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hz3)
      rw [this, map_one]
    have hσ1 : σ ≠ 1 := by
      intro h1
      apply hZC
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro l hl
      have h2 := congrArg (fun τ : MulAut L => ((τ ⟨l, hl⟩ : L) : Y)) h1
      simp only [hσ, normalizerMonoidHom_apply_coe, MulAut.one_apply] at h2
      calc l * z = z * l * z⁻¹ * z := by rw [h2]
        _ = z * l := by group
    have hwcσ : RonanK432.AutWeaklyClosed σ := fun x hx =>
      Item432Proof.mem_zpowers_of_mem_normalizer hz hwc hzN x hx
    have hZ3 := Item432Proof.isPGroup_center_of_isSubnormal hO hL.2
    have h3 := Res432.three_dvd_card_of_isComponent hO hL
    have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 3 :=
      (Item432Proof.pRank_top_eq L).trans_le
        ((CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hLH).trans hbd)
    have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.1.2.1
    have hrowL : Row76 (L ⧸ Subgroup.center L) :=
      hrow _ hL.1.2.1 hL.1.2.2
        (hK.isCatalogGroup_of_surjective L hL.1.2.2 (QuotientGroup.mk' _)
          (QuotientGroup.mk'_surjective _))
        (RonanK432.three_dvd_card_quot_center hL.1.1 h3)
        ⟨L, inferInstance, inferInstance, hL.1, hZ3, ⟨MulEquiv.refl _⟩, hrk⟩
    by_cases hzL : z ∈ L
    ·
      have hZL : Subgroup.zpowers z ≤ L := Subgroup.zpowers_le.mpr hzL
      have hLn : L.Normal := ⟨fun x hx g => by
        have := Item432Proof.mem_normalizer_of_le hwc hL hZL hZC g
        exact (Subgroup.mem_normalizer_iff.mp this x).mp hx⟩
      have hHL : H = L := le_antisymm (Subgroup.normalClosure_le_normal hZL) hLH
      have hσb : σ = MulAut.conj (⟨z, hzL⟩ : L) :=
        Item432Proof.normalizerMonoidHom_eq_conj ⟨z, hzL⟩
      have hb3 : (⟨z, hzL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
      obtain ⟨hs, hc⟩ := isSimpleGroup_of_listRow76 hL.1 hZ3 hrowL.1 hb3
        (by rw [← hσb]; exact hσ1) (by rw [← hσb]; exact hwcσ)
      rw [hHL]
      refine ⟨hs, ?_⟩
      rw [← Item432Proof.pRank_top_eq]
      exact hc
    ·
      obtain ⟨b, t, hb, ht⟩ := exists_inv_of_row76 hL.1 hZ3 h3 hrk hrowL hσ3 hσ1 hwcσ
        (pRank_fixed_le_two_of_not_mem hzN hz3 hzL hLH
          (Subgroup.le_normalClosure (Subgroup.mem_zpowers z)) hbd)
      exact (Item432Proof.false_of_not_mem hz hwc hzN b t hb ht hσ1 hzL).elim
  ·
    push Not at hex
    have hZn := zpowers_normal_of_no_component hO hz hwc hex
    refine ⟨?_, Or.inl (Item432Proof.pRank_eq_one_of_forall hO hz hwc hex)⟩
    have hHZ : H = Subgroup.zpowers z := Subgroup.normalClosure_eq_self _
    rw [hHZ]
    exact isSimpleGroup_of_prime_card (p := 3) (hp := ⟨Nat.prime_three⟩)
      (by rw [Nat.card_zpowers, hz])

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
