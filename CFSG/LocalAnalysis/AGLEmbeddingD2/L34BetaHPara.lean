module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaAmalgam
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Three
import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaHParaGroup
import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaHParaK

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement Pointwise

theorem D2Escape.map_twoCore_inf_commute {G : Type} [Group G] [Finite G] {P : Sylow 3 G}
    {M A H R : Subgroup G} (h : D2Escape 3 P M A H R)
    (hX₀ : ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      Subgroup.normalizer (((A.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) 3)) : Subgroup _) : Set _))
    {u : H} (hu : (u : G) ∈ pCoreOf 2 (H ⊓ M)) {a : H} (ha : (a : G) ∈ A) :
    QuotientGroup.mk' (primeComplementCore (G := H) 3) u *
        QuotientGroup.mk' (primeComplementCore (G := H) 3) a =
      QuotientGroup.mk' (primeComplementCore (G := H) 3) a *
        QuotientGroup.mk' (primeComplementCore (G := H) 3) u := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hAHM : (a : G) ∈ H ⊓ M := ⟨a.2, h.le_M (h.A_le ha)⟩
  have huHM : (u : G) ∈ H ⊓ M := (pCoreOf_le 2 (H ⊓ M)) hu
  have hπu : π u ∈ Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) := by
    rw [← hX₀]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr huHM)
  have haA : π a ∈ (A.subgroupOf H).map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha)
  have h1 : π u * π a * (π u)⁻¹ ∈ (A.subgroupOf H).map π :=
    (Subgroup.mem_normalizer_iff.mp hπu (π a)).mp haA
  have h2 : π u * π a * (π u)⁻¹ * (π a)⁻¹ ∈ (A.subgroupOf H).map π :=
    Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ haA)
  have hc : ((u * a * u⁻¹ * a⁻¹ : H) : G) ∈ pCoreOf 2 (H ⊓ M) := by
    have h3 : (a : G) * (u : G)⁻¹ * (a : G)⁻¹ ∈ pCoreOf 2 (H ⊓ M) :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M) hAHM) (u : G)⁻¹).mp
        ((pCoreOf 2 (H ⊓ M)).inv_mem hu)
    simpa [mul_assoc] using (pCoreOf 2 (H ⊓ M)).mul_mem hu h3
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (H ⊓ M)) ⟨_, hc⟩
  have hn' : ((u * a * u⁻¹ * a⁻¹ : H) : G) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hn'' : (u * a * u⁻¹ * a⁻¹ : H) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn')
  have hπc : (π u * π a * (π u)⁻¹ * (π a)⁻¹) ^ 2 ^ n = 1 := by
    have := congrArg π hn''
    simpa [map_mul, map_inv, map_pow] using this
  obtain ⟨a', ha', ha'eq⟩ := h2
  have ha'3 : a' ^ 3 = 1 := Subtype.ext (h.elem.2 (a' : G) (Subgroup.mem_subgroupOf.mp ha'))
  have h3c : (π u * π a * (π u)⁻¹ * (π a)⁻¹) ^ 3 = 1 := by
    rw [← ha'eq, ← map_pow, ha'3, map_one]
  have hord : orderOf (π u * π a * (π u)⁻¹ * (π a)⁻¹) ∣ Nat.gcd (2 ^ n) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hπc) (orderOf_dvd_of_pow_eq_one h3c)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left n (by norm_num))] at hord
  have h4 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
  exact h4

theorem isNormal_of_isComponentOf_map_eq {Γ X : Type*} [Group Γ] [Finite Γ] [Group X]
    (φ : Γ →* X) {Lt : Subgroup Γ} (hLt : IsComponentOf Lt ⊤) {K : Subgroup X} [K.Normal]
    (hmap : Lt.map φ = K) (hK : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a) : Lt.Normal := by
  have key : ∀ g : Γ, Lt.map (MulAut.conj g).toMonoidHom = Lt := by
    intro g
    by_contra hne
    have hLt' : IsComponentOf (Lt.map (MulAut.conj g).toMonoidHom) ⊤ :=
      (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) Lt).mpr hLt
    have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne Lt _ hLt hLt'
      (Ne.symm hne)
    have h1 := congrArg (Subgroup.map φ) hcomm
    rw [Subgroup.map_commutator, Subgroup.map_bot] at h1
    have h2 : (Lt.map (MulAut.conj g).toMonoidHom).map φ = K := by
      rw [Subgroup.map_map]
      have hcomp : φ.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj (φ g)).toMonoidHom.comp φ := by ext x; simp
      rw [hcomp, ← Subgroup.map_map, hmap]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (by rw [Subgroup.normalizer_eq_top_iff.mpr ‹K.Normal›]; trivial)
    rw [hmap, h2] at h1
    obtain ⟨a, ha, b, hb, hab⟩ := hK
    apply hab
    have hmem : ⁅a, b⁆ ∈ ⁅K, K⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [h1, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  refine ⟨fun n hn g => ?_⟩
  have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hn
  rw [key g] at h
  exact h

theorem mem_normalizer_zpowers_of_eq_inv_or_eq_one {X : Type*} [Group X] [Finite X] {t y : X}
    (h : t = 1 ∨ t * y * t⁻¹ = y⁻¹) :
    t ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup X) : Set X) := by
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  rcases h with rfl | h
  · simp
  · rw [← conj_zpow, h, inv_zpow']
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) _

end CFSG.AGLEmbeddingD2

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem D2L34BetaConf3.exists_orderThree_inverted
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {U : Subgroup G} (hU : IsBetaBase H M U) :
    ∃ y : H ⧸ primeComplementCore (G := H) 3, y ∈ K ∧ orderOf y = 3 ∧
      y ∉ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ∧
      (∀ u ∈ U.subgroupOf H, QuotientGroup.mk' (primeComplementCore (G := H) 3) u = 1 ∨
        QuotientGroup.mk' (primeComplementCore (G := H) 3) u * y *
          (QuotientGroup.mk' (primeComplementCore (G := H) 3) u)⁻¹ = y⁻¹) ∧
      ∃ u ∈ U.subgroupOf H, QuotientGroup.mk' (primeComplementCore (G := H) 3) u ≠ 1 := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hK := hc.almostSimple
  have hL : IsLinThreeFour K := isLinThreeFour_of_l34Index hc.l34 hc.iso
  have hX₀ := hK.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  have hT₀H : pCoreOf 2 (H ⊓ M) ≤ H := (pCoreOf_le 2 (H ⊓ M)).trans inf_le_left
  have hW'H : (primeComplementCore (G := H) 3).map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hUH : U ≤ H := hU.2.2.1.trans (sup_le hW'H hT₀H)
  have hVle : (U.subgroupOf H).map π ≤ ((pCoreOf 2 (H ⊓ M)).subgroupOf H).map π := by
    have hW : ((primeComplementCore (G := H) 3).map H.subtype).subgroupOf H =
        primeComplementCore (G := H) 3 := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    have h1 : U.subgroupOf H ≤
        primeComplementCore (G := H) 3 ⊔ (pCoreOf 2 (H ⊓ M)).subgroupOf H := by
      rw [← hW, ← Subgroup.subgroupOf_sup hW'H hT₀H]
      exact fun x hx => Subgroup.mem_subgroupOf.mpr (hU.2.2.1 (Subgroup.mem_subgroupOf.mp hx))
    have h3 := Subgroup.map_mono (f := π) h1
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h3
  have hVE : ∀ t ∈ (U.subgroupOf H).map π, ∀ e ∈ (A.subgroupOf H).map π, t * e = e * t := by
    intro t ht e he
    obtain ⟨u, hu, rfl⟩ := hVle ht
    obtain ⟨a, ha, rfl⟩ := he
    exact hc.esc.map_twoCore_inf_commute hX₀ (Subgroup.mem_subgroupOf.mp hu)
      (Subgroup.mem_subgroupOf.mp ha)
  have hV : IsPGroup 2 ((U.subgroupOf H).map π) := hU.1.comap_subtype.map π
  have hAcard : Nat.card ((A.subgroupOf H).map π) = 9 := by
    rw [hK.card_A]
    norm_num
  have := hK.normal
  obtain ⟨y, hyK, hy3, hyN, hy⟩ := L34BetaHPara.exists_inverted_of_centralizes
    hK.centralizer_eq_bot hL hc.le_K hAcard hV hVE
  refine ⟨y, hyK, hy3, fun hy₀ => hyN (hX₀ ▸ hy₀), fun u hu => hy _ (Subgroup.mem_map_of_mem π hu),
    ?_⟩
  obtain ⟨x, hxU, hxW⟩ := IsConcreteLE.not_le_iff_exists.mp hU.2.2.2
  refine ⟨⟨x, hUH hxU⟩, Subgroup.mem_subgroupOf.mpr hxU, fun h1 => hxW ?_⟩
  have : (⟨x, hUH hxU⟩ : H) ∈ primeComplementCore (G := H) 3 := (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨_, this, rfl⟩

theorem d2L34BetaHPara3
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {U : Subgroup G} (hU : IsBetaBase H M U) :
    ∃ Y : Subgroup G, Y ≤ H ∧ ¬ Y ≤ M ∧ Nat.card Y = 3 ∧ IsS3Parabolic U (U ⊔ Y) := by
  obtain ⟨y, hyK, hy3, hyX₀, hyU, u₁, hu₁, hu₁ne⟩ := hc.exists_orderThree_inverted hU
  have hK := hc.almostSimple
  have hL : IsLinThreeFour K := isLinThreeFour_of_l34Index hc.l34 hc.iso
  have hcard : Nat.card K = 20160 := (kFactSmallThreeOrders K).2.1 hL
  have hK2 : 2 ∣ Nat.card K := by rw [hcard]; norm_num
  have hNH : H ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M := by
    rw [hc.normalizer_eq]
    exact inf_eq_right.mpr inf_le_left
  obtain ⟨L, hLw, hLW⟩ := hc.esc.exists_weakBlock_twoCore_inf hK hK2 hc.ne
  have hB := hK.l34BlockFacts hcard hNH hLw hLW
  set φ := twoPrimeMap H Nat.prime_three (by norm_num : (3 : ℕ) ≠ 2) with hφ
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set S := CFSG.pCore 2 ↥H with hS
  have hKnc : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_ne_comm_of_isQuasisimple hK.component.2.2
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  have : K.Normal := hK.normal
  have hLnorm : (barM H L).Normal :=
    isNormal_of_isComponentOf_map_eq φ hLw.component hB.map_eq hKnc
  have hcent : ∀ l ∈ barM H L, φ l = 1 → ∀ m ∈ barM H L, l * m = m * l := by
    intro l hl hφl m hm
    have h1 : (⟨l, hl⟩ : barM H L) ∈ (φ.comp (barM H L).subtype).ker :=
      MonoidHom.mem_ker.mpr hφl
    have h2 := Subgroup.mem_center_iff.mp (hB.ker_le h1) ⟨m, hm⟩
    exact (congrArg Subtype.val h2).symm
  have hcop : ∀ l ∈ barM H L, φ l = 1 → Nat.Coprime 3 (orderOf l) :=
    fun l _ hφl => hB.ker_coprime l hφl
  obtain ⟨Yt, -, hYt3, hyYt, hYtinv⟩ := exists_subgroup_card_three_invariant φ (barM H L) hy3
    (hB.map_eq ▸ hyK) hcent hcop
  have hT₀H : pCoreOf 2 (H ⊓ M) ≤ H := (pCoreOf_le 2 (H ⊓ M)).trans inf_le_left
  have hW'H : (primeComplementCore (G := H) 3).map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hUH : U ≤ H := hU.2.2.1.trans (sup_le hW'H hT₀H)
  have hSU : S ≤ U.subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hU.2.1 ((mem_pCore_two_iff_mem_pCoreOf x).mp hx))
  have hU2 : IsPGroup 2 (U.subgroupOf H) := hU.1.comap_subtype
  have hUY : (U.subgroupOf H).map (QuotientGroup.mk' S) ≤
      Subgroup.normalizer (Yt : Set (↥H ⧸ S)) := by
    rintro _ ⟨u, hu, rfl⟩
    apply hYtinv
    exact mem_normalizer_zpowers_of_eq_inv_or_eq_one (hyU u hu)
  have hact : ∃ u ∈ U.subgroupOf H, ∃ z ∈ Yt,
      QuotientGroup.mk' S u * z * (QuotientGroup.mk' S u)⁻¹ ≠ z := by
    obtain ⟨z, hz, hzy⟩ := hyYt
    refine ⟨u₁, hu₁, z, hz, fun h => ?_⟩
    have h1 := congrArg φ h
    rw [map_mul, map_mul, map_inv, hzy] at h1
    change π u₁ * y * (π u₁)⁻¹ = y at h1
    rcases hyU u₁ hu₁ with h2 | h2
    · exact hu₁ne h2
    · rw [h2] at h1
      have h3 : y ^ 2 = 1 := by
        rw [sq]
        exact mul_eq_one_iff_eq_inv.mpr h1.symm
      have h4 := orderOf_dvd_of_pow_eq_one h3
      rw [hy3] at h4
      omega
  obtain ⟨W, hW3, hWY, hrel, hnn⟩ := exists_card_three_of_normalizing_quotient S
    (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) hSU hU2 hYt3 hUY hact
  refine ⟨W.map H.subtype, Subgroup.map_subtype_le W, ?_, ?_, ?_⟩
  ·
    intro hYM
    obtain ⟨z, hz, hzy⟩ := hyYt
    rw [← hWY] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    apply hyX₀
    rw [← hzy]
    refine ⟨w, Subgroup.mem_subgroupOf.mpr ⟨w.2, hYM ⟨w, hw, rfl⟩⟩, rfl⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hW3]
  ·
    have hU'map : (U.subgroupOf H).map H.subtype = U := Subgroup.map_subgroupOf_eq_of_le hUH
    have hsup : U ⊔ W.map H.subtype = ((U.subgroupOf H) ⊔ W).map H.subtype := by
      rw [Subgroup.map_sup, hU'map]
    have hrel' : U.relIndex (U ⊔ W.map H.subtype) = 3 := by
      have h := Subgroup.relIndex_map_map_of_injective (U.subgroupOf H) ((U.subgroupOf H) ⊔ W)
        H.subtype_injective
      rw [hU'map, ← hsup, hrel] at h
      exact h
    refine ⟨⟨le_sup_left, hU.1, ?_⟩, ?_⟩
    · show ¬ 2 ∣ U.relIndex (U ⊔ W.map H.subtype)
      rw [hrel']
      norm_num
    · rw [hsup]
      have hperm := nonempty_quotient_pCore_perm_three (Γ := ↥(U.subgroupOf H ⊔ W))
        (T := (U.subgroupOf H).subgroupOf (U.subgroupOf H ⊔ W)) hU2.comap_subtype hrel hnn
      exact nonempty_quotient_pCore_perm_three_map H.subtype H.subtype_injective _ hperm

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers

theorem d2L34BetaHPara :
    D2L34BetaHPara := by
  intro d G _ _ P M A H R Rbar K hc U hU
  exact CFSG.LocalAnalysis.RankThreeTheoremC.d2L34BetaHPara3 hc.toConf3 hU

end CFSG.AGLEmbeddingD2
