module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace L34FF

@[expose] def threeComp (H R : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) : Subgroup G :=
  nclIn H (d1LiftX 3 H R K)

@[expose] def threeCompCore (H R : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) : Subgroup G :=
  threeComp H R K ⊓ GLBPrimeCore 3 H

variable {H R : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

omit [Finite G] in
theorem threeComp_le : threeComp H R K ≤ H :=
  nclIn_le_self H _

omit [Finite G] in
theorem le_normalizer_threeComp : H ≤ Subgroup.normalizer (threeComp H R K : Set G) :=
  le_normalizer_nclIn H _

omit [Finite G] in
theorem d1LiftX_le_threeComp : d1LiftX 3 H R K ≤ threeComp H R K :=
  le_nclIn (d1LiftX_le_H 3 H R K)

omit [Finite G] in
theorem threeCompCore_le : threeCompCore H R K ≤ threeComp H R K :=
  inf_le_left

theorem le_normalizer_threeCompCore :
    H ≤ Subgroup.normalizer (threeCompCore H R K : Set G) := by
  intro h hh
  have h1 := le_normalizer_threeComp (R := R) (K := K) hh
  have h2 := le_normalizer_glbPrimeCore 3 H hh
  rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
  intro x
  exact ⟨fun hx => ⟨(h1 x).mp hx.1, (h2 x).mp hx.2⟩, fun hx => ⟨(h1 x).mpr hx.1, (h2 x).mpr hx.2⟩⟩

theorem coprime_card_threeCompCore : Nat.Coprime (Nat.card (threeCompCore H R K)) 3 :=
  (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
    (glbPrimeCore_coprime 3 H)).symm

omit [Finite G] in
theorem threeComp_le_of_forall {S : Subgroup G}
    (hS : ∀ g ∈ H, ∀ t ∈ d1LiftX 3 H R K, g * t * g⁻¹ ∈ S) : threeComp H R K ≤ S := by
  rw [threeComp, nclIn, Subgroup.normalClosure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨t, ht, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  have := hS c c.2 t (Subgroup.mem_subgroupOf.mp ht)
  simpa using this

omit [Finite G] in
theorem exists_pow_conj_eq_one (hT : IsPGroup 3 (d1LiftX 3 H R K)) {g t : G}
    (ht : t ∈ d1LiftX 3 H R K) : ∃ a : ℕ, (g * t * g⁻¹) ^ 3 ^ a = 1 := by
  obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
  refine ⟨a, ?_⟩
  have h1 : t ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
  rw [conj_pow, h1, mul_one, mul_inv_cancel]

end L34FF

variable {P : Sylow 3 G} {M H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

structure L34FF.Core (H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) : Prop where
  normal : K.Normal
  isSimpleGroup : IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a
  mapX : ((d1LiftX 3 H R K).subgroupOf H).map
    (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K
  inf_ne_bot : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K ≠ ⊥
  isPGroup : IsPGroup 3 R

omit [Finite G] in
theorem L34FF.Core.map_threeComp (hd : L34FF.Core H R Rbar K) :
    ((L34FF.threeComp H R K).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3)) = K := by
  have hKn : K.Normal := hd.normal
  obtain ⟨hs, -⟩ := hd.isSimpleGroup
  have h1 : (L34FF.threeComp H R K).subgroupOf H =
      Subgroup.normalClosure ((d1LiftX 3 H R K).subgroupOf H : Set H) := by
    rw [L34FF.threeComp, nclIn, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have h2 : (QuotientGroup.mk' (primeComplementCore (G := H) 3) ''
      ((d1LiftX 3 H R K).subgroupOf H : Set H)) =
      (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K : Subgroup _) : Set _) := by
    rw [← Subgroup.coe_map, hd.mapX]
  rw [h1, Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _), h2]
  refine le_antisymm (Subgroup.normalClosure_le_normal (fun x hx => hx.2)) ?_
  set N := Subgroup.normalClosure
    (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) 3)) :
        Set (H ⧸ primeComplementCore (G := H) 3)) with hN
  have hNn : (N.subgroupOf K).Normal := Subgroup.Normal.subgroupOf inferInstance K
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf K) with h | h
  · exfalso
    have hbot : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxN : (⟨x, hx.2⟩ : K) ∈ N.subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.subset_normalClosure hx)
      rw [h, Subgroup.mem_bot] at hxN
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hxN
    exact hd.inf_ne_bot hbot
  · intro k hk
    have : (⟨k, hk⟩ : K) ∈ N.subgroupOf K := h ▸ Subgroup.mem_top _
    exact this

theorem L34FF.Core.threeComp_dichotomy (hd : L34FF.Core H R Rbar K)
    {N : Subgroup G} (hNL : N ≤ L34FF.threeComp H R K)
    (hLN : L34FF.threeComp H R K ≤ Subgroup.normalizer (N : Set G)) :
    N ≤ L34FF.threeCompCore H R K ∨ L34FF.threeComp H R K ≤ N := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set L := L34FF.threeComp H R K with hLdef
  have hmap := hd.map_threeComp
  obtain ⟨hs, -⟩ := hd.isSimpleGroup
  have hLH : L ≤ H := L34FF.threeComp_le
  set N' := (N.subgroupOf H).map π with hN'
  have hN'K : N' ≤ K := by
    rw [← hmap]
    exact Subgroup.map_mono (Subgroup.comap_mono hNL)
  have hN'n : (N'.subgroupOf K).Normal := by
    refine ⟨fun x hx k => ?_⟩
    obtain ⟨⟨n, hnH⟩, hn, hnx⟩ := Subgroup.mem_subgroupOf.mp hx
    have hk : (k : H ⧸ primeComplementCore (G := H) 3) ∈ (L.subgroupOf H).map π := by
      rw [hmap]; exact k.2
    obtain ⟨⟨l, hlH⟩, hl, hlk⟩ := hk
    rw [Subgroup.mem_subgroupOf]
    have hc : l * n * l⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hLN (Subgroup.mem_subgroupOf.mp hl)) n).mp
        (Subgroup.mem_subgroupOf.mp hn)
    refine ⟨⟨l * n * l⁻¹, H.mul_mem (H.mul_mem hlH hnH) (H.inv_mem hlH)⟩, hc, ?_⟩
    have e : (⟨l * n * l⁻¹, H.mul_mem (H.mul_mem hlH hnH) (H.inv_mem hlH)⟩ : H) =
        ⟨l, hlH⟩ * ⟨n, hnH⟩ * (⟨l, hlH⟩ : H)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hlk, hnx]
    rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.subgroupOf K) with h | h
  · left
    intro n hn
    refine ⟨hNL hn, ?_⟩
    have hnH : n ∈ H := hLH (hNL hn)
    have hmem : π ⟨n, hnH⟩ ∈ N' := ⟨⟨n, hnH⟩, hn, rfl⟩
    have h1 : (⟨π ⟨n, hnH⟩, hN'K hmem⟩ : K) ∈ N'.subgroupOf K := hmem
    rw [h, Subgroup.mem_bot] at h1
    have h2 : π ⟨n, hnH⟩ = 1 := congrArg Subtype.val h1
    exact (mk'_primeComplementCore_eq_one_iff 3 ⟨n, hnH⟩).mp h2
  · right
    have hLNY : L ≤ N ⊔ L34FF.threeCompCore H R K := by
      intro l hl
      have hlH : l ∈ H := hLH hl
      have hlK : π ⟨l, hlH⟩ ∈ K := hmap ▸ ⟨⟨l, hlH⟩, hl, rfl⟩
      have h1 : (⟨π ⟨l, hlH⟩, hlK⟩ : K) ∈ N'.subgroupOf K := h ▸ Subgroup.mem_top _
      obtain ⟨⟨n, hnH⟩, hn, hnl⟩ := Subgroup.mem_subgroupOf.mp h1
      have hn' : n ∈ N := Subgroup.mem_subgroupOf.mp hn
      have hy : n⁻¹ * l ∈ L34FF.threeCompCore H R K := by
        refine ⟨L.mul_mem (L.inv_mem (hNL hn')) hl, ?_⟩
        have e : (⟨n⁻¹ * l, H.mul_mem (H.inv_mem hnH) hlH⟩ : H) = (⟨n, hnH⟩ : H)⁻¹ * ⟨l, hlH⟩ :=
          rfl
        refine (mk'_primeComplementCore_eq_one_iff 3
          ⟨n⁻¹ * l, H.mul_mem (H.inv_mem hnH) hlH⟩).mp ?_
        rw [e, map_mul, map_inv]
        change (π ⟨n, hnH⟩)⁻¹ * π ⟨l, hlH⟩ = 1
        rw [hnl, inv_mul_cancel]
      have e2 : l = n * (n⁻¹ * l) := by group
      rw [e2]
      exact Subgroup.mul_mem_sup hn' hy
    have hT : IsPGroup 3 (d1LiftX 3 H R K) := hd.isPGroup.to_le (d1LiftX_le 3 H R K)
    refine L34FF.threeComp_le_of_forall fun g hg t ht => ?_
    obtain ⟨a, ha⟩ := L34FF.exists_pow_conj_eq_one (g := g) hT ht
    have hmemL : g * t * g⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (L34FF.le_normalizer_threeComp hg) t).mp
        (L34FF.d1LiftX_le_threeComp ht)
    exact L34FF.mem_of_mem_sup_of_pow_prime_pow
      (L34FF.threeCompCore_le.trans hLN) L34FF.coprime_card_threeCompCore (hLNY hmemL) ha

theorem L34FF.Core.commutator_threeComp (hd : L34FF.Core H R Rbar K) :
    ⁅L34FF.threeComp H R K, L34FF.threeComp H R K⁆ = L34FF.threeComp H R K := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set L := L34FF.threeComp H R K with hLdef
  have hLH : L ≤ H := L34FF.threeComp_le
  have hle : ⁅L, L⁆ ≤ L := Subgroup.commutator_le.mpr fun a ha b hb =>
    L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
  have hnorm : L ≤ Subgroup.normalizer ((⁅L, L⁆ : Subgroup G) : Set G) := by
    intro g hg
    have hgN := L34FF.le_normalizer_threeComp (R := R) (K := K) (hLH hg)
    have hmapL : L.map (MulAut.conj g).toMonoidHom = L := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
      · intro x hx
        refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
        have := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (L : Set G)).inv_mem hgN) x).mp hx
        simpa [mul_assoc] using this
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hmap : ⁅L, L⁆.map (MulAut.conj g).toMonoidHom = ⁅L, L⁆ := by
      rw [Subgroup.map_commutator, hmapL]
    constructor
    · intro hx
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hmap] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        simpa using hyx
      rw [← this]
      exact hy
  rcases hd.threeComp_dichotomy hle hnorm with h | h
  · exfalso
    obtain ⟨-, a, b, hab⟩ := hd.isSimpleGroup
    have hmap := hd.map_threeComp
    have ha : (a : H ⧸ primeComplementCore (G := H) 3) ∈ (L.subgroupOf H).map π := by
      rw [hmap]; exact a.2
    have hb : (b : H ⧸ primeComplementCore (G := H) 3) ∈ (L.subgroupOf H).map π := by
      rw [hmap]; exact b.2
    obtain ⟨⟨x, hxH⟩, hx, hxa⟩ := ha
    obtain ⟨⟨y, hyH⟩, hy, hyb⟩ := hb
    have hc : ⁅x, y⁆ ∈ L34FF.threeCompCore H R K :=
      h (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hx)
        (Subgroup.mem_subgroupOf.mp hy))
    have h1 : π ⁅(⟨x, hxH⟩ : H), ⟨y, hyH⟩⁆ = 1 :=
      (mk'_primeComplementCore_eq_one_iff 3 _).mpr hc.2
    rw [map_commutatorElement, hxa, hyb, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hab (Subtype.ext h1)
  · exact le_antisymm hle h

theorem L34FF.Core.not_threeComp_le_threeCompCore (hd : L34FF.Core H R Rbar K) :
    ¬ L34FF.threeComp H R K ≤ L34FF.threeCompCore H R K := by
  intro h
  have hK : K = ⊥ := by
    rw [← hd.map_threeComp, eq_bot_iff]
    rintro _ ⟨⟨l, hlH⟩, hl, rfl⟩
    rw [Subgroup.mem_bot]
    exact (mk'_primeComplementCore_eq_one_iff 3 _).mpr (h hl).2
  obtain ⟨-, a, b, hab⟩ := hd.isSimpleGroup
  have h1 : ∀ x : K, x = 1 := fun x =>
    Subtype.ext (Subgroup.mem_bot.mp ((le_bot_iff.mpr hK) x.2))
  exact hab (by rw [h1 a, h1 b])

theorem D1OneSmallData.toL34FFCore (hd : D1OneSmallData 3 P M H R Rbar K) :
    L34FF.Core H R Rbar K :=
  ⟨hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic, hd.isSimpleGroup,
    hd.cfg.map_d1LiftX_eq_inf, fun hbot => hd.noncyclic (hbot ▸ inferInstance),
    hd.cfg.ext.isPGroup⟩

theorem D1OneSmallData.map_threeComp (hd : D1OneSmallData 3 P M H R Rbar K) :
    ((L34FF.threeComp H R K).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3)) = K :=
  hd.toL34FFCore.map_threeComp

theorem D1OneSmallData.threeComp_dichotomy (hd : D1OneSmallData 3 P M H R Rbar K)
    {N : Subgroup G} (hNL : N ≤ L34FF.threeComp H R K)
    (hLN : L34FF.threeComp H R K ≤ Subgroup.normalizer (N : Set G)) :
    N ≤ L34FF.threeCompCore H R K ∨ L34FF.threeComp H R K ≤ N :=
  hd.toL34FFCore.threeComp_dichotomy hNL hLN

theorem D1OneSmallData.not_threeComp_le_threeCompCore (hd : D1OneSmallData 3 P M H R Rbar K) :
    ¬ L34FF.threeComp H R K ≤ L34FF.threeCompCore H R K :=
  hd.toL34FFCore.not_threeComp_le_threeCompCore

theorem D1OneSmallData.glbPrimeCore_le_inf (hd : D1OneSmallData 3 P M H R Rbar K) :
    GLBPrimeCore 3 H ≤ GLBPrimeCore 3 (H ⊓ M) :=
  le_glbPrimeCore (_root_.le_inf (glbPrimeCore_le 3 H) hd.cfg.ext.toD1Escape.primeCore_le)
    (inf_le_left.trans (le_normalizer_glbPrimeCore 3 H)) (glbPrimeCore_coprime 3 H)

end CFSG.AGLEmbedding
