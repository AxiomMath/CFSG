module

import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ApplyAux1
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup

theorem zja_dvd_card {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] {K₀ J : Subgroup Y}
    [K₀.Normal] {L : Subgroup (Y ⧸ K₀)} (hLnab : ∃ a b : L, a * b ≠ b * a)
    (hJL : J.map (QuotientGroup.mk' K₀) = L) (hJp : pElementSubgroup p J = J) :
    p ∣ Nat.card L := by
  by_contra hpL
  have hcop : p.Coprime (Nat.card L) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpL
  have hker : J ≤ (QuotientGroup.mk' K₀).ker := by
    rw [← hJp]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxJ, k, hk⟩
    have hxL : QuotientGroup.mk' K₀ x ∈ L := hJL ▸ Subgroup.mem_map_of_mem _ hxJ
    have h1 : orderOf (⟨QuotientGroup.mk' K₀ x, hxL⟩ : L) ∣ p ^ k := by
      rw [← hk, Subgroup.orderOf_mk]
      exact orderOf_map_dvd _ x
    have h2 : orderOf (⟨QuotientGroup.mk' K₀ x, hxL⟩ : L) ∣ Nat.card L := orderOf_dvd_natCard _
    have h3 : orderOf (⟨QuotientGroup.mk' K₀ x, hxL⟩ : L) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (hcop.pow_left k)) h2
    have h4 : (⟨QuotientGroup.mk' K₀ x, hxL⟩ : L) = 1 := orderOf_eq_one_iff.mp h3
    exact MonoidHom.mem_ker.mpr (congrArg Subtype.val h4)
  have hbot : L = ⊥ := by
    rw [← hJL]
    exact (Subgroup.map_eq_bot_iff _).mpr hker
  obtain ⟨a, b, hab⟩ := hLnab
  refine hab ?_
  have ha : (a : Y ⧸ K₀) ∈ (⊥ : Subgroup (Y ⧸ K₀)) := hbot.le a.2
  have ha1 : a = 1 := Subtype.ext (Subgroup.mem_bot.mp ha)
  rw [ha1, one_mul, mul_one]

theorem zja_eq_bot_of_normalized {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] {L A : Subgroup G}
    (hLs : IsSimpleGroup L) (hLn : L.Normal) (hLc : centralizer (L : Set G) = ⊥)
    (hpL : p ∣ Nat.card L) (hLA : ∀ l ∈ L, ∀ a ∈ A, l * a * l⁻¹ ∈ A)
    (hA : p.Coprime (Nat.card A)) : A = ⊥ := by
  have hinf : A ⊓ L = ⊥ := by
    have hnorm : ((A ⊓ L).subgroupOf L).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨?_, ?_⟩
      · exact hLA g g.2 n hn.1
      · exact L.mul_mem (L.mul_mem g.2 n.2) (L.inv_mem g.2)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A ⊓ L).subgroupOf L) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hxL : x ∈ L := hx.2
      have hx' : (⟨x, hxL⟩ : L) ∈ (A ⊓ L).subgroupOf L := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
    · exfalso
      have hLA' : L ≤ A := fun x hx => by
        have hx' : (⟨x, hx⟩ : L) ∈ (A ⊓ L).subgroupOf L := by
          rw [h]
          exact Subgroup.mem_top _
        exact hx'.1
      have hdvd : p ∣ Nat.card A := hpL.trans (Subgroup.card_dvd_of_le hLA')
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hA hdvd)
  rw [eq_bot_iff]
  intro a ha
  have hc : a ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : l * a * l⁻¹ * a⁻¹ ∈ A ⊓ L := by
      refine ⟨A.mul_mem (hLA l hl a ha) (A.inv_mem ha), ?_⟩
      have h2 : a * l⁻¹ * a⁻¹ ∈ L := hLn.conj_mem l⁻¹ (L.inv_mem hl) a
      have h3 : l * a * l⁻¹ * a⁻¹ = l * (a * l⁻¹ * a⁻¹) := by group
      rw [h3]
      exact L.mul_mem hl h2
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  rw [hLc] at hc
  exact hc

theorem zja_map_subtype_le {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] {K₀ J W : Subgroup Y}
    [K₀.Normal] {L : Subgroup (Y ⧸ K₀)} (hLs : IsSimpleGroup L) (hLn : L.Normal)
    (hLc : centralizer (L : Set (Y ⧸ K₀)) = ⊥) (hpL : p ∣ Nat.card L)
    (hJL : J.map (QuotientGroup.mk' K₀) = L) (hJW : J ≤ W) {N : Subgroup W} [N.Normal]
    (hN : p.Coprime (Nat.card N)) : N.map W.subtype ≤ K₀ := by
  let ρ : W →* Y ⧸ K₀ := (QuotientGroup.mk' K₀).comp W.subtype
  have hbot : N.map ρ = ⊥ := by
    refine zja_eq_bot_of_normalized hp hLs hLn hLc hpL ?_ ?_
    · intro l hl a ha
      rw [← hJL] at hl
      obtain ⟨j, hj, rfl⟩ := hl
      obtain ⟨n, hn, rfl⟩ := ha
      refine ⟨⟨j, hJW hj⟩ * n * ⟨j, hJW hj⟩⁻¹, Normal.conj_mem inferInstance n hn _, ?_⟩
      simp [ρ]
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd N ρ) hN
  intro x hx
  obtain ⟨n, hn, rfl⟩ := hx
  have hn' : ρ n ∈ N.map ρ := Subgroup.mem_map_of_mem _ hn
  rw [hbot, Subgroup.mem_bot] at hn'
  exact (QuotientGroup.eq_one_iff _).mp hn'

theorem zja_map_eq_bot {p : ℕ} (hp : p.Prime) {G M : Type*} [Group G] [Group M] [IsSimpleGroup M]
    (hpM : p ∣ Nat.card M) (f : G →* M) (hf : Function.Surjective f) {N : Subgroup G}
    [N.Normal] (hN : p.Coprime (Nat.card N)) : N.map f = ⊥ := by
  have hnorm : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with h | h
  · exact h
  · exfalso
    have h1 : Nat.card (N.map f) = Nat.card M := by
      rw [h]
      exact Subgroup.card_top
    have h2 : p ∣ Nat.card N := hpM.trans (h1 ▸ Subgroup.card_map_dvd N f)
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hN h2)

theorem zja_pCore_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y]
    (hsylow : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.pCore 2 Y) (CFSG.pPrimeCore p Y))
    {J W : Subgroup Y} {L : Subgroup (Y ⧸ CFSG.pPrimeCore p Y)} (hLs : IsSimpleGroup L)
    (hLn : L.Normal) (hLc : centralizer (L : Set (Y ⧸ CFSG.pPrimeCore p Y)) = ⊥)
    (hpL : p ∣ Nat.card L) (hJL : J.map (QuotientGroup.mk' (CFSG.pPrimeCore p Y)) = L)
    (hJW : J ≤ W) : CFSG.pCore 2 W = (CFSG.pCore 2 Y).subgroupOf W := by
  apply le_antisymm
  · intro x hx
    have h1 : (CFSG.pCore 2 W).map W.subtype ≤ CFSG.pPrimeCore p Y :=
      zja_map_subtype_le hp hLs hLn hLc hpL hJL hJW
        (zja_coprime_of_isPGroup_two hp hp2 CFSG.pCore_isPGroup)
    have h2 : (CFSG.pCore 2 W).map W.subtype ≤ CFSG.pCore 2 Y :=
      zja_le_of_isSylowOf hsylow h1 (CFSG.pCore_isPGroup.map _)
    exact h2 ⟨x, hx, rfl⟩
  · exact le_sSup ⟨inferInstance, CFSG.pCore_isPGroup.comap_subtype⟩

theorem zja_pPrimeCore_eq {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    {J W : Subgroup Y} {L : Subgroup (Y ⧸ CFSG.pPrimeCore p Y)} (hLs : IsSimpleGroup L)
    (hLn : L.Normal) (hLc : centralizer (L : Set (Y ⧸ CFSG.pPrimeCore p Y)) = ⊥)
    (hpL : p ∣ Nat.card L) (hJL : J.map (QuotientGroup.mk' (CFSG.pPrimeCore p Y)) = L)
    (hJW : J ≤ W) : CFSG.pPrimeCore p W = (CFSG.pPrimeCore p Y).subgroupOf W := by
  have : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · intro x hx
    have h1 := zja_map_subtype_le hp hLs hLn hLc hpL hJL hJW
      (N := CFSG.pPrimeCore p W) CFSG.pPrimeCore_coprime_card
    exact h1 ⟨x, hx, rfl⟩
  · refine le_sSup ⟨inferInstance, ?_⟩
    have hmap : ((CFSG.pPrimeCore p Y).subgroupOf W).map W.subtype =
        CFSG.pPrimeCore p Y ⊓ W := Subgroup.subgroupOf_map_subtype _ _
    have hcard : Nat.card ((CFSG.pPrimeCore p Y).subgroupOf W) =
        Nat.card (CFSG.pPrimeCore p Y ⊓ W : Subgroup Y) := by
      rw [← hmap, Subgroup.card_map_of_injective W.subtype_injective]
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      CFSG.pPrimeCore_coprime_card

theorem zja_sylow_normal {Y : Type} [Group Y] [Finite Y] {K W : Subgroup Y}
    (hsylow : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.pCore 2 Y) K) {P : Subgroup W}
    (hP : P.map W.subtype ≤ K) (T : Sylow 2 P) : (T : Subgroup P).Normal := by
  have hNn : (((CFSG.pCore 2 Y).comap W.subtype).comap P.subtype).Normal :=
    (CFSG.pCore_normal.comap W.subtype).comap P.subtype
  have hNp : IsPGroup 2 (((CFSG.pCore 2 Y).comap W.subtype).comap P.subtype) :=
    CFSG.pCore_isPGroup.comap_subtype.comap_subtype
  have hTN : (T : Subgroup P) ≤ ((CFSG.pCore 2 Y).comap W.subtype).comap P.subtype := by
    have hQ : IsPGroup 2 ((T : Subgroup P).map (W.subtype.comp P.subtype)) :=
      T.isPGroup'.map _
    have hQK : (T : Subgroup P).map (W.subtype.comp P.subtype) ≤ K := by
      rintro _ ⟨t, -, rfl⟩
      exact hP (Subgroup.mem_map_of_mem W.subtype t.2)
    have hQR := zja_le_of_isSylowOf hsylow hQK hQ
    intro t ht
    exact hQR (Subgroup.mem_map_of_mem (W.subtype.comp P.subtype) ht)
  have hTeq := T.is_maximal' hNp hTN
  rw [← hTeq]
  exact hNn

theorem zja_exists_equiv_image {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    {J W : Subgroup Y} {L : Subgroup (Y ⧸ CFSG.pPrimeCore p Y)} (hLs : IsSimpleGroup L)
    (hLn : L.Normal) (hLc : centralizer (L : Set (Y ⧸ CFSG.pPrimeCore p Y)) = ⊥)
    (hpL : p ∣ Nat.card L) (hJL : J.map (QuotientGroup.mk' (CFSG.pPrimeCore p Y)) = L)
    (hJW : J ≤ W) :
    Nonempty (↥((J.subgroupOf W).map (QuotientGroup.mk' (CFSG.pPrimeCore p W))) ≃* ↥L) := by
  have hEq := zja_pPrimeCore_eq hp hLs hLn hLc hpL hJL hJW
  let ρ : W →* Y ⧸ CFSG.pPrimeCore p Y :=
    (QuotientGroup.mk' (CFSG.pPrimeCore p Y)).comp W.subtype
  have hle : CFSG.pPrimeCore p W ≤ ρ.ker := by
    intro x hx
    rw [hEq] at hx
    exact (QuotientGroup.eq_one_iff _).mpr hx
  let φ : (W ⧸ CFSG.pPrimeCore p W) →* (Y ⧸ CFSG.pPrimeCore p Y) :=
    QuotientGroup.lift _ ρ hle
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    have hw1 : ρ w = 1 := by simpa [φ] using hx
    have hw : w ∈ CFSG.pPrimeCore p W := by
      rw [hEq, Subgroup.mem_subgroupOf]
      exact (QuotientGroup.eq_one_iff _).mp hw1
    exact (QuotientGroup.eq_one_iff _).mpr hw
  have hmap : ((J.subgroupOf W).map (QuotientGroup.mk' (CFSG.pPrimeCore p W))).map φ = L := by
    rw [Subgroup.map_map]
    have hcomp : φ.comp (QuotientGroup.mk' (CFSG.pPrimeCore p W)) = ρ := by
      ext w
      simp [φ]
    rw [hcomp, show ρ = (QuotientGroup.mk' (CFSG.pPrimeCore p Y)).comp W.subtype from rfl,
      ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hJW, hJL]
  exact ⟨(Subgroup.equivMapOfInjective _ φ hφ).trans (MulEquiv.subgroupCongr hmap)⟩

theorem zja_quotient_equiv {p : ℕ} (hp : p.Prime) {G M : Type} [Group G] [Finite G] [Group M]
    [IsSimpleGroup M] (hpM : p ∣ Nat.card M) (hM : center M = ⊥) (ψ : G →* M)
    (hψ : Function.Surjective ψ) (hker : p.Coprime (Nat.card ψ.ker)) :
    Nonempty ((G ⧸ CFSG.pPrimeCore p G) ⧸ center (G ⧸ CFSG.pPrimeCore p G) ≃* M) := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : CFSG.pPrimeCore p G = ψ.ker := by
    apply le_antisymm
    · exact (Subgroup.map_eq_bot_iff _).mp
        (zja_map_eq_bot hp hpM ψ hψ (N := CFSG.pPrimeCore p G) CFSG.pPrimeCore_coprime_card)
    · exact le_sSup ⟨inferInstance, hker⟩
  let e₁ : G ⧸ CFSG.pPrimeCore p G ≃* M :=
    (QuotientGroup.quotientMulEquivOfEq h1).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hc : center (G ⧸ CFSG.pPrimeCore p G) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e₁ z ∈ center M := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro m
      obtain ⟨y, rfl⟩ := e₁.surjective m
      rw [← map_mul, ← map_mul, hz y]
    rw [hM, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.mpr (e₁.injective (by simpa using hz'))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e₁⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
