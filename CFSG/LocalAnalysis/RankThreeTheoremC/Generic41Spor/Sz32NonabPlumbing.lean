module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32FInfo
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32EndgameE1
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIEndgame41MaxPair
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem sz32_nonab_false (hS : Setting G) (hU0 : FullCoreLocal G) (hNonab : KFactNonabF5)
    (hc : PointConfig IsSz32Type G 5 P M x J) {U : Subgroup G}
    (hUel : IsElemAbelian 5 U) (hUc : Nat.card U = 5 ^ 2) (hxU : x ∈ U)
    (hC : ∀ u ∈ U, u ∉ Subgroup.zpowers x → Subgroup.centralizer ({u} : Set G) ≤ M)
    {S R₀ : Subgroup G} (hE : EndgameData 5 M U S R₀) {F : Subgroup G}
    (hFH : IsSylowOf 5 F (Subgroup.normalizer (S : Set G))) (hUF : U ≤ F) (hFM : F ≤ M)
    (hFinfo : Sz32FInfo x U F) (hnonab : ¬ IsMulCommutative F) : False := by
  have hp5 : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp5⟩
  obtain ⟨hFcard, -, hFexp, hFcen, hFom⟩ := hFinfo.cases.resolve_left hnonab
  set H : Subgroup G := Subgroup.normalizer (S : Set G) with hH
  have hxo : orderOf x = 5 := orderOf_eq_prime hc.generic.2.1.2.2.1 hc.generic.2.1.2.1
  have hxH : x ∈ H := hE.U_S hxU
  have hxF : x ∈ F := hUF hxU
  have hFle : F ≤ H := hFH.le
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hnormal : S.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have := hS.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h | h
    · exact hE.S_ne h
    · obtain ⟨k, hk⟩ := hE.S_two ⟨x, h ▸ Subgroup.mem_top x⟩
      have hxk : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have h1 := orderOf_dvd_of_pow_eq_one hxk
      rw [hxo] at h1
      have h2 : 5 ∣ 2 := hp5.dvd_of_dvd_pow h1
      omega
  set O : Subgroup H := primeComplementCore (G := H) 5 with hO
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπ
  have hcore : primeComplementCore (G := H ⧸ O) 5 = ⊥ := primeComplementCore_quotient_eq_bot 5
  have hOcop : Nat.Coprime 5 (Nat.card O) := primeComplementCore_coprime 5
  have hFp : IsPGroup 5 (F.subgroupOf H) := hFH.isPGroup.comap_subtype
  have hinj : ∀ a b : H, (a : G) ∈ F → (b : G) ∈ F → π a = π b → a = b := by
    intro a b ha hb hab
    have h1 : a⁻¹ * b ∈ O := by
      rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : a⁻¹ * b ∈ F.subgroupOf H := Subgroup.mem_subgroupOf.mpr (F.mul_mem (F.inv_mem ha) hb)
    have h4 : a⁻¹ * b ∈ F.subgroupOf H ⊓ O := ⟨h2, h1⟩
    rw [CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup hp5 hFp hOcop, Subgroup.mem_bot] at h4
    exact inv_mul_eq_one.mp h4
  have hcat : CFSG.AGLEmbedding.CatalogSimpleSections (H ⧸ O) :=
    (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper H hHtop).quotient O
  have hsyl : IsSylowOf 5 ((F.subgroupOf H).map π) ⊤ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.isSylowOf_top_map_mk hFH
  have hnc : ¬ IsMulCommutative ((F.subgroupOf H).map π) := by
    intro hcomm
    apply hnonab
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    have ha : π ⟨(a : G), hFle a.2⟩ ∈ (F.subgroupOf H).map π := ⟨⟨a, hFle a.2⟩, a.2, rfl⟩
    have hb : π ⟨(b : G), hFle b.2⟩ ∈ (F.subgroupOf H).map π := ⟨⟨b, hFle b.2⟩, b.2, rfl⟩
    have h1 := congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ((F.subgroupOf H).map π))).comm ⟨_, ha⟩ ⟨_, hb⟩)
    have h2 : (⟨(a : G), hFle a.2⟩ * ⟨(b : G), hFle b.2⟩ : H) =
        ⟨(b : G), hFle b.2⟩ * ⟨(a : G), hFle a.2⟩ :=
      hinj _ _ (F.mul_mem a.2 b.2) (F.mul_mem b.2 a.2) (by rw [map_mul, map_mul]; exact h1)
    have h3 := congrArg Subtype.val h2
    exact h3
  have hcard : Nat.card ((F.subgroupOf H).map π) = 125 := by
    rw [CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp5 O hOcop hFp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFle).toEquiv, hFcard]
    norm_num
  have hexp : ∀ f ∈ (F.subgroupOf H).map π, f ^ 25 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    have : a ^ 25 = 1 := Subtype.ext (hFexp (a : G) ha)
    rw [this, map_one]
  have hcen : ∀ z ∈ (F.subgroupOf H).map π,
      (∀ f ∈ (F.subgroupOf H).map π, f * z = z * f) ↔ z ∈ Subgroup.zpowers (π ⟨x, hxH⟩) := by
    rintro _ ⟨z, hz, rfl⟩
    constructor
    · intro hall
      have hzc : ∀ f ∈ F, f * (z : G) = (z : G) * f := by
        intro f hf
        have h1 := hall (π ⟨f, hFle hf⟩) ⟨⟨f, hFle hf⟩, hf, rfl⟩
        rw [← map_mul, ← map_mul] at h1
        exact congrArg Subtype.val (hinj _ _ (F.mul_mem hf hz) (F.mul_mem hz hf) h1)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hFcen (z : G) hz).mp hzc)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have : (⟨x, hxH⟩ : H) ^ k = z := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
      rw [← map_zpow, this]
    · intro hmem f hf
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      obtain ⟨b, hb, rfl⟩ := hf
      rw [← hk]
      have hcomm : Commute (π b) (π ⟨x, hxH⟩) := by
        have h2 : b * ⟨x, hxH⟩ = ⟨x, hxH⟩ * b :=
          Subtype.ext ((hFcen x hxF).mpr (Subgroup.mem_zpowers x) (b : G) hb)
        show π b * π ⟨x, hxH⟩ = π ⟨x, hxH⟩ * π b
        rw [← map_mul, ← map_mul, h2]
      exact (hcomm.zpow_right k).eq
  have hB : ∀ b, b ∈ (U.subgroupOf H).map π ↔ (b ∈ (F.subgroupOf H).map π ∧ b ^ 5 = 1) := by
    intro b
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨⟨u, hUF hu, rfl⟩, ?_⟩
      rw [← map_pow]
      have : u ^ 5 = 1 := Subtype.ext (hUel.2 (u : G) hu)
      rw [this, map_one]
    · rintro ⟨⟨f, hf, rfl⟩, h5⟩
      have h1 : f ^ 5 = 1 := by
        refine hinj _ _ (F.pow_mem hf 5) F.one_mem ?_
        rw [map_pow, h5, map_one]
      exact ⟨f, hFom (f : G) hf (by simpa using congrArg Subtype.val h1), rfl⟩
  have hFΓ : (F.subgroupOf H).map π ≤ ((H ⊓ M).subgroupOf H).map π :=
    Subgroup.map_mono (fun a ha => Subgroup.mem_subgroupOf.mpr ⟨a.2, hFM ha⟩)
  have hCb : ∀ b ∈ (U.subgroupOf H).map π, b ∉ Subgroup.zpowers (π ⟨x, hxH⟩) →
      Subgroup.centralizer ({b} : Set (H ⧸ O)) ≤ ((H ⊓ M).subgroupOf H).map π := by
    rintro _ ⟨u, hu, rfl⟩ hnx
    have hux : (u : G) ∉ Subgroup.zpowers x := by
      intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      apply hnx
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have : (⟨x, hxH⟩ : H) ^ k = u := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
      rw [← map_zpow, this]
    have hu1 : u ≠ 1 := by
      rintro rfl
      exact hux (Subgroup.one_mem _)
    have hu5 : u ^ 5 = 1 := Subtype.ext (hUel.2 (u : G) hu)
    have hro : orderOf u = 5 := orderOf_eq_prime hu5 hu1
    have hCM : Subgroup.centralizer ({(u : G)} : Set G) ≤ M := hC (u : G) hu hux
    refine (CFSG.LocalAnalysis.RankThreeTheoremC.centralizer_mk_le_map hp5 hro).trans
      (Subgroup.map_mono fun c hc => ?_)
    exact Subgroup.mem_subgroupOf.mpr ⟨c.2, hCM (Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)))⟩
  have hRne : (R₀.subgroupOf H).map π ≠ ⊥ := fun hbot =>
    hE.R_not (CFSG.LocalAnalysis.RankThreeTheoremC.le_rankThreePrimeCore_of_map_mk_eq_bot
      hE.R_S hbot)
  have hR2 : IsPGroup 2 ((R₀.subgroupOf H).map π) :=
    (show IsPGroup 2 (R₀.subgroupOf H) from hE.R_two.comap_subtype).map π
  have hBn : (U.subgroupOf H).map π ≤
      Subgroup.normalizer (((R₀.subgroupOf H).map π : Subgroup (H ⧸ O)) : Set (H ⧸ O)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.map_subgroupOf_le_normalizer_map hE.U_R π
  have hBel : IsElemAbelian 5 ((U.subgroupOf H).map π) :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hUel H) π
  have hUp : IsPGroup 5 (U.subgroupOf H) := (IsPGroup.of_card hUc).comap_subtype
  have hBcard : Nat.card ((U.subgroupOf H).map π) = 5 ^ 2 := by
    rw [CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp5 O hOcop hUp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun u hu => hFle (hUF hu))).toEquiv, hUc]
  have hΓ := hNonab (H ⧸ O) hcat hcore ((F.subgroupOf H).map π) (((H ⊓ M).subgroupOf H).map π)
    ((U.subgroupOf H).map π) ((R₀.subgroupOf H).map π) (π ⟨x, hxH⟩) hsyl hnc hcard hexp hcen hB
    hBel hBcard hFΓ hCb hRne hR2 hBn
  set Ob : Subgroup (H ⧸ O) := ((GLBPrimeCore 5 M ⊓ H).subgroupOf H).map π with hOb
  set Γ : Subgroup (H ⧸ O) := ((H ⊓ M).subgroupOf H).map π with hΓdef
  have hObcop : Nat.Coprime 5 (Nat.card Ob) := by
    have h1 : Nat.card Ob ∣ Nat.card ((GLBPrimeCore 5 M ⊓ H).subgroupOf H) :=
      Subgroup.card_map_dvd _ π
    have h2 : Nat.card ((GLBPrimeCore 5 M ⊓ H).subgroupOf H) ∣ Nat.card (GLBPrimeCore 5 M) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        GLBPrimeCore 5 M ⊓ H ≤ H)).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact (CFSG.AGLEmbedding.glbPrimeCore_coprime 5 M).coprime_dvd_right (h1.trans h2)
  have hObΓ : ∀ g ∈ Γ, ∀ o ∈ Ob, g * o * g⁻¹ ∈ Ob := by
    rintro _ ⟨g₀, hg₀, rfl⟩ _ ⟨o₀, ho₀, rfl⟩
    have hg₀' : (g₀ : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp hg₀
    have ho₀' : (o₀ : G) ∈ GLBPrimeCore 5 M ⊓ H := Subgroup.mem_subgroupOf.mp ho₀
    refine ⟨g₀ * o₀ * g₀⁻¹, Subgroup.mem_subgroupOf.mpr ⟨?_, (g₀ * o₀ * g₀⁻¹).2⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 5 M hg₀'.2) _).mp ho₀'.1
    · simp [map_mul, map_inv]
  have hRO : (R₀.subgroupOf H).map π ≤ Ob := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, Subgroup.mem_subgroupOf.mpr
      ⟨(hE.R_core hr : (r : G) ∈ GLBPrimeCore 5 M), r.2⟩, rfl⟩
  exact hRne (sz32_E1 hcore hΓ hObcop hObΓ hR2 hRO)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
