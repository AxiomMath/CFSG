module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134Defs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerDefs
import CFSG.LocalAnalysis.SectionRank.QTK.A134Pi
import CFSG.LocalAnalysis.SectionRank.QTK.CoverBA134Basic
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup

section Sup

variable {G : Type*} [Group G] {r : ℕ}

theorem layer_isElemAbelian_sup_card {A B : Subgroup G} (hA : CFSG.Open.IsElemAbelian r A)
    (hB : CFSG.Open.IsElemAbelian r B) (hAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hdisj : ∀ x ∈ A, x ∈ B → x = 1) :
    CFSG.Open.IsElemAbelian r (A ⊔ B) ∧ Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  let Φ : ↥A × ↥B →* G :=
    MonoidHom.noncommCoprod A.subtype B.subtype fun a b => hAB a a.2 b b.2
  have hΦ : ∀ p : ↥A × ↥B, Φ p = (p.1 : G) * (p.2 : G) := fun _ => rfl
  have hrange : Φ.range = A ⊔ B := by
    have h := MonoidHom.noncommCoprod_range A.subtype B.subtype fun a b => hAB a a.2 b b.2
    rw [Subgroup.range_subtype, Subgroup.range_subtype] at h
    exact h
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    rw [hΦ] at h
    have hab : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left h
    have ha1 : (a : G) = 1 := hdisj a a.2 (by rw [hab]; exact B.inv_mem b.2)
    have hb1 : (b : G) = 1 := by
      rw [ha1, one_mul] at h
      exact h
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  have hcomm : ∀ a b : ↥A × ↥B, a * b = b * a := by
    rintro ⟨a, b⟩ ⟨a', b'⟩
    exact Prod.ext (Subtype.ext (congrArg Subtype.val (hA.1.is_comm.comm a a')))
      (Subtype.ext (congrArg Subtype.val (hB.1.is_comm.comm b b')))
  have hpow : ∀ a : ↥A × ↥B, a ^ r = 1 := by
    rintro ⟨a, b⟩
    exact Prod.ext (Subtype.ext (hA.2 a a.2)) (Subtype.ext (hB.2 b b.2))
  refine ⟨?_, ?_⟩
  · rw [← hrange]
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨q, hq⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← hp, ← hq, ← map_mul, ← map_mul, hcomm]
    · obtain ⟨p, rfl⟩ := MonoidHom.mem_range.1 hy
      rw [← map_pow, hpow, map_one]
  · rw [← hrange, ← Nat.card_prod]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Sup

section Lift

variable {H : Type} [Group H] [Finite H]

theorem layer_eq_one_of_mem_inter_commuting {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) {r : ℕ} (hr : r.Prime)
    (hrZ : ¬ r ∣ Nat.card (center ↥L₁)) {x : H} (hx₁ : x ∈ L₁) (hx₂ : x ∈ L₂)
    (hxr : x ^ r = 1) : x = 1 := by
  have hz : (⟨x, hx₁⟩ : ↥L₁) ∈ center ↥L₁ := CoverB.mem_center_of_mem_commuting hc hx₂
  have h1 := eq_one_of_mem_center_of_not_dvd hr hrZ hz (Subtype.ext (by simpa using hxr))
  exact congrArg Subtype.val h1

theorem layer_rank_add_le_two_of_centralizer (he : CFSG.Open.evenRank H ≤ 2)
    {L : Subgroup H} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrZ : ¬ r ∣ Nat.card (center ↥L))
    {R : Subgroup (↥L ⧸ center ↥L)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) {F : Subgroup H}
    (hF : CFSG.Open.IsElemAbelian r F) (hFL : ∀ a ∈ L, ∀ b ∈ F, Commute a b) {c : ℕ}
    (hFc : Nat.card ↥F = r ^ c) :
    CFSG.Open.pRank r (normalizer (R : Set (↥L ⧸ center ↥L))) + c ≤ 2 := by
  obtain ⟨E, hEN, hE, hEc⟩ := exists_eq_pRank hr.one_lt (normalizer (R : Set (↥L ⧸ center ↥L)))
  obtain ⟨P, hP, hPc, hPE⟩ := exists_lift hr hrZ hE
  obtain ⟨R₂, hR₂, hR₂2, hR₂N⟩ := exists_two_subgroup_normalized hR hR2
  have hR' : R₂.map L.subtype ≠ ⊥ := fun h =>
    hR₂ ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h)
  have hAL : P.map L.subtype ≤ L := map_subtype_le P
  have hAN : P.map L.subtype ≤ normalizer ((R₂.map L.subtype : Subgroup H) : Set H) := by
    rintro _ ⟨p, hp, rfl⟩
    have hpE : (QuotientGroup.mk' (center ↥L)) p ∈ E := hPE ▸ mem_map_of_mem _ hp
    exact le_normalizer_map L.subtype (mem_map_of_mem _ (hR₂N p (hEN hpE)))
  have hFN : F ≤ normalizer ((R₂.map L.subtype : Subgroup H) : Set H) :=
    CoverB.le_normalizer_of_commuting hFL (map_subtype_le R₂)
  have hAF : ∀ a ∈ P.map L.subtype, ∀ b ∈ F, Commute a b := fun a ha b hb => hFL a (hAL ha) b hb
  have hA : CFSG.Open.IsElemAbelian r (P.map L.subtype) := isElemAbelian_map _ hP
  have hdisj : ∀ x ∈ P.map L.subtype, x ∈ F → x = 1 := fun x hx hxF =>
    layer_eq_one_of_mem_inter_commuting (L₁ := L) (L₂ := F) hFL hr hrZ (hAL hx) hxF (hA.2 x hx)
  obtain ⟨hAF', hAFc⟩ := layer_isElemAbelian_sup_card hA hF hAF hdisj
  have hAc : Nat.card ↥(P.map L.subtype) =
      r ^ CFSG.Open.pRank r (normalizer (R : Set (↥L ⧸ center ↥L))) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hPc, hEc]
  exact le_two_of_evenRank_le_two he hR' (hR₂2.map _) hr hr2 hAF' (sup_le hAN hFN)
    (k := CFSG.Open.pRank r (normalizer (R : Set (↥L ⧸ center ↥L))) + c)
    (by rw [hAFc, hAc, hFc, pow_add])

theorem layer_pair_bound_of_not_dvd (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (φ : ↥L₁ ≃* ↥L₂) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrZ : ¬ r ∣ Nat.card (center ↥L₁)) {R : Subgroup (↥L₁ ⧸ center ↥L₁)}
    (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    CFSG.Open.pRank r (normalizer (R : Set (↥L₁ ⧸ center ↥L₁))) +
      CFSG.Open.pRank r (⊤ : Subgroup (↥L₂ ⧸ center ↥L₂)) ≤ 2 := by
  have hrZ₂ : ¬ r ∣ Nat.card (center ↥L₂) := by
    rwa [← Nat.card_congr (Subgroup.centerCongr φ).toEquiv]
  obtain ⟨E₂, -, hE₂, hE₂c⟩ := exists_eq_pRank hr.one_lt (⊤ : Subgroup (↥L₂ ⧸ center ↥L₂))
  obtain ⟨P₂, hP₂, hP₂c, -⟩ := exists_lift hr hrZ₂ hE₂
  refine layer_rank_add_le_two_of_centralizer he hr hr2 hrZ hR hR2 (F := P₂.map L₂.subtype)
    (isElemAbelian_map _ hP₂) (fun a ha b hb => ?_) (c := CFSG.Open.pRank r (⊤ : Subgroup _)) ?_
  · obtain ⟨b', -, rfl⟩ := hb
    exact hc a ha b' b'.2
  · rw [Subgroup.card_map_of_injective L₂.subtype_injective, hP₂c, hE₂c]

theorem layer_triple_bound_of_not_dvd (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ L₃ : Subgroup H}
    (h12 : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (h13 : ∀ a ∈ L₁, ∀ b ∈ L₃, Commute a b)
    (h23 : ∀ a ∈ L₂, ∀ b ∈ L₃, Commute a b) (φ₂ : ↥L₁ ≃* ↥L₂) (φ₃ : ↥L₁ ≃* ↥L₃) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrZ : ¬ r ∣ Nat.card (center ↥L₁))
    {R : Subgroup (↥L₁ ⧸ center ↥L₁)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    CFSG.Open.pRank r (normalizer (R : Set (↥L₁ ⧸ center ↥L₁))) +
      CFSG.Open.pRank r (⊤ : Subgroup (↥L₂ ⧸ center ↥L₂)) +
        CFSG.Open.pRank r (⊤ : Subgroup (↥L₃ ⧸ center ↥L₃)) ≤ 2 := by
  have hrZ₂ : ¬ r ∣ Nat.card (center ↥L₂) := by
    rwa [← Nat.card_congr (Subgroup.centerCongr φ₂).toEquiv]
  have hrZ₃ : ¬ r ∣ Nat.card (center ↥L₃) := by
    rwa [← Nat.card_congr (Subgroup.centerCongr φ₃).toEquiv]
  obtain ⟨E₂, -, hE₂, hE₂c⟩ := exists_eq_pRank hr.one_lt (⊤ : Subgroup (↥L₂ ⧸ center ↥L₂))
  obtain ⟨E₃, -, hE₃, hE₃c⟩ := exists_eq_pRank hr.one_lt (⊤ : Subgroup (↥L₃ ⧸ center ↥L₃))
  obtain ⟨P₂, hP₂, hP₂c, -⟩ := exists_lift hr hrZ₂ hE₂
  obtain ⟨P₃, hP₃, hP₃c, -⟩ := exists_lift hr hrZ₃ hE₃
  have hB : CFSG.Open.IsElemAbelian r (P₂.map L₂.subtype) := isElemAbelian_map _ hP₂
  have hC : CFSG.Open.IsElemAbelian r (P₃.map L₃.subtype) := isElemAbelian_map _ hP₃
  have hBL : P₂.map L₂.subtype ≤ L₂ := map_subtype_le P₂
  have hCL : P₃.map L₃.subtype ≤ L₃ := map_subtype_le P₃
  obtain ⟨hBC, hBCc⟩ := layer_isElemAbelian_sup_card hB hC
    (fun b hb c hc => h23 b (hBL hb) c (hCL hc))
    (fun x hx hx' => layer_eq_one_of_mem_inter_commuting h23 hr hrZ₂ (hBL hx) (hCL hx') (hB.2 x hx))
  have hcen : P₂.map L₂.subtype ⊔ P₃.map L₃.subtype ≤ centralizer (L₁ : Set H) := by
    refine sup_le (fun b hb => mem_centralizer_iff.mpr fun a ha => ?_)
      (fun b hb => mem_centralizer_iff.mpr fun a ha => ?_)
    · exact h12 a ha b (hBL hb)
    · exact h13 a ha b (hCL hb)
  have h := layer_rank_add_le_two_of_centralizer he hr hr2 hrZ hR hR2
    (F := P₂.map L₂.subtype ⊔ P₃.map L₃.subtype) hBC
    (fun a ha b hb => mem_centralizer_iff.mp (hcen hb) a ha)
    (c := CFSG.Open.pRank r (⊤ : Subgroup (↥L₂ ⧸ center ↥L₂)) +
      CFSG.Open.pRank r (⊤ : Subgroup (↥L₃ ⧸ center ↥L₃)))
    (by
      rw [hBCc, Subgroup.card_map_of_injective L₂.subtype_injective,
        Subgroup.card_map_of_injective L₃.subtype_injective, hP₂c, hP₃c, hE₂c, hE₃c, pow_add])
  omega

end Lift

section Components

variable {H : Type} [Group H] [Finite H]

theorem layer_commute_of_distinct_components {L₁ L₂ : Subgroup H} (h₁ : CFSG.IsComponent L₁)
    (h₂ : CFSG.IsComponent L₂) (hne : L₁ ≠ L₂) : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b :=
  fun a ha b hb => CFSG.LocalCores.componentIndex_commute (G := H)
    (show (⟨L₁, h₁⟩ : CFSG.LocalCores.ComponentIndex H) ≠ ⟨L₂, h₂⟩ from fun h =>
      hne (congrArg Subtype.val h)) a b ha hb

theorem IsoComponentBound.of_not_dvd (he : CFSG.Open.evenRank H ≤ 2) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hZ : ∀ L₁ L₂ : Subgroup H, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      L₁ ≠ L₂ → Nonempty (↥L₁ ≃* ↥L₂) → ¬ r ∣ Nat.card (center ↥L₁)) :
    IsoComponentBound H r := by
  refine ⟨fun L₁ L₂ h₁ h₂ hne hiso R hR hR2 => ?_,
    fun L₁ L₂ L₃ h₁ h₂ h₃ h12 h13 h23 hiso₂ hiso₃ R hR hR2 => ?_⟩
  · obtain ⟨φ⟩ := hiso
    exact layer_pair_bound_of_not_dvd he (layer_commute_of_distinct_components h₁ h₂ hne) φ hr hr2
      (hZ L₁ L₂ h₁ h₂ hne ⟨φ⟩) hR hR2
  · obtain ⟨φ₂⟩ := hiso₂
    obtain ⟨φ₃⟩ := hiso₃
    exact layer_triple_bound_of_not_dvd he (layer_commute_of_distinct_components h₁ h₂ h12)
      (layer_commute_of_distinct_components h₁ h₃ h13)
      (layer_commute_of_distinct_components h₂ h₃ h23)
      φ₂ φ₃ hr hr2 (hZ L₁ L₂ h₁ h₂ h12 ⟨φ₂⟩) hR hR2

private theorem two_dvd_card_of_quasisimple_layer {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) : 2 ∣ Nat.card Q := by
  by_contra h
  have hs : Group.IsSolvable Q :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h))
  have hn : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have hp : Group.IsPerfect Q := hQ.1
  exact Group.IsPerfect.not_isSolvable Q hs

theorem layer_exists_two_subgroup_le_component {L : Subgroup H} (hL : CFSG.IsComponent L) :
    ∃ R : Subgroup H, R ≠ ⊥ ∧ IsPGroup 2 R ∧ R ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2
    (two_dvd_card_of_quasisimple_layer hL.1)
  have ht' : orderOf (t : H) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have hne : zpowers (t : H) ≠ ⊥ := fun h => by
    have h1 : (t : H) = 1 := Subgroup.mem_bot.mp (h ▸ mem_zpowers (t : H))
    rw [h1, orderOf_one] at ht'
    omega
  exact ⟨zpowers (t : H), hne,
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one]), zpowers_le.mpr t.2⟩

theorem layer_pRank_component_le_two (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (h₁ : CFSG.IsComponent L₁) (h₂ : CFSG.IsComponent L₂) (hne : L₁ ≠ L₂) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) : CFSG.Open.pRank r (⊤ : Subgroup ↥L₁) ≤ 2 := by
  obtain ⟨E, -, hE, hEc⟩ := exists_eq_pRank hr.one_lt (⊤ : Subgroup ↥L₁)
  obtain ⟨R, hR, hR2, hRL⟩ := layer_exists_two_subgroup_le_component h₂
  have hEN : E.map L₁.subtype ≤ normalizer (R : Set H) :=
    (map_subtype_le E).trans
      (CoverB.le_normalizer_of_commuting (layer_commute_of_distinct_components h₂ h₁ hne.symm) hRL)
  exact le_two_of_evenRank_le_two he hR hR2 hr hr2 (isElemAbelian_map _ hE) hEN
    (by rw [Subgroup.card_map_of_injective L₁.subtype_injective, hEc])

theorem layer_eq_sup_of_pRank_three (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (h₁ : CFSG.IsComponent L₁) (h₂ : CFSG.IsComponent L₂)
    (h3 : CFSG.Open.pRank 3 (L₁ ⊔ L₂) = 3) : CFSG.layer H = L₁ ⊔ L₂ := by
  refine le_antisymm ?_
    (sup_le (CFSG.LocalCores.component_le_layer h₁) (CFSG.LocalCores.component_le_layer h₂))
  rw [CFSG.layer.eq_sSup]
  refine sSup_le fun L hL => ?_
  by_contra hcon
  have hL1 : L ≠ L₁ := fun h => hcon (h ▸ le_sup_left)
  have hL2 : L ≠ L₂ := fun h => hcon (h ▸ le_sup_right)
  have hc₁ := layer_commute_of_distinct_components hL h₁ hL1
  have hc₂ := layer_commute_of_distinct_components hL h₂ hL2
  have hcen : L₁ ⊔ L₂ ≤ centralizer (L : Set H) :=
    sup_le (fun b hb => mem_centralizer_iff.mpr fun a ha => hc₁ a ha b hb)
      (fun b hb => mem_centralizer_iff.mpr fun a ha => hc₂ a ha b hb)
  obtain ⟨E, hEle, hE, hEc⟩ := exists_eq_pRank (by norm_num : 1 < 3) (L₁ ⊔ L₂)
  rw [h3] at hEc
  obtain ⟨R, hR, hR2, hRL⟩ := layer_exists_two_subgroup_le_component hL
  have hEN : E ≤ normalizer (R : Set H) :=
    hEle.trans (CoverB.le_normalizer_of_commuting
      (fun a ha b hb => mem_centralizer_iff.mp (hcen hb) a ha) hRL)
  have := le_two_of_evenRank_le_two he hR hR2 Nat.prime_three (by norm_num) hE hEN hEc
  omega

end Components

theorem qtLayerCentreFactOne_of_pair (hP : LayerPairFull) : QTLayerCentreFactOne := by
  intro H _ _ hQT hK r hr hr2 _
  by_cases hex : ∃ L₁ L₂ : Subgroup H, CFSG.IsComponent L₁ ∧ CFSG.IsComponent L₂ ∧ L₁ ≠ L₂ ∧
      Nonempty (↥L₁ ≃* ↥L₂) ∧ r ∣ Nat.card (center ↥L₁)
  · obtain ⟨L₁, L₂, h₁, h₂, hne, hiso, hrZ⟩ := hex
    obtain ⟨hr3, hsu, hrk⟩ := hP H hQT hK L₁ L₂ h₁ h₂ hne hiso r hr hr2 hrZ
    exact Or.inr ⟨hr3, L₁, L₂, h₁, h₂, hne, layer_eq_sup_of_pRank_three hQT h₁ h₂ hrk,
      fun _ => ⟨hsu, hrk⟩⟩
  · push Not at hex
    exact Or.inl (IsoComponentBound.of_not_dvd hQT hr hr2 fun L₁ L₂ h₁ h₂ hne hiso =>
      hex L₁ L₂ h₁ h₂ hne hiso)

end CFSG.SectionRank.QTK.CentreFact
