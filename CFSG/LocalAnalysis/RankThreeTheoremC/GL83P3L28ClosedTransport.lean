module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28ClosedShape
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28ClosedBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Reduced

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Red (Red pr)
open CFSG.AGLEmbedding (glbPrimeCore_subgroupOf glbPrimeCore_le)

theorem no_simple_section {W H K : Type} [Group W] [Finite W] [Group H] [Group K] [Finite K]
    [IsSimpleGroup K] (hKn : ∃ a b : K, a * b ≠ b * a) (h3 : 3 ∣ Nat.card K)
    (N₁ : Subgroup W) [N₁.Normal] (hN₁ : ¬ 3 ∣ Nat.card N₁) [Group.IsSolvable H] (f : W →* H)
    (hf : ∀ w : W, f w = 1 → ∃ n : ℕ, w ^ 3 ^ n ∈ N₁) (S : Subgroup W) (g : S →* K)
    (hg : Function.Surjective g) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnsolv : ¬ Group.IsSolvable K := by
    intro h
    obtain ⟨a, b, hab⟩ := hKn
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr h) a b)
  haveI hAn : (N₁.subgroupOf S).Normal := Normal.subgroupOf inferInstance S
  have hA : (N₁.subgroupOf S).map g = ⊥ := by
    haveI : ((N₁.subgroupOf S).map g).Normal := hAn.map g hg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N₁.subgroupOf S).map g) with
      h | h
    · exact h
    · exfalso
      have h1 : Nat.card K ∣ Nat.card (N₁.subgroupOf S) := by
        have := Subgroup.card_map_dvd (N₁.subgroupOf S) g
        rwa [h, Subgroup.card_top] at this
      have h2 : Nat.card (N₁.subgroupOf S) ∣ Nat.card N₁ := by
        have e : Nat.card (N₁.subgroupOf S) = Nat.card ((N₁.subgroupOf S).map S.subtype) :=
          (Subgroup.card_map_of_injective S.subtype_injective).symm
        rw [e, Subgroup.subgroupOf_map_subtype]
        exact Subgroup.card_dvd_of_le inf_le_left
      exact hN₁ (h3.trans (h1.trans h2))
  have hAker : ∀ s : S, (s : W) ∈ N₁ → g s = 1 := by
    intro s hs
    have : g s ∈ (N₁.subgroupOf S).map g := ⟨s, mem_subgroupOf.mpr hs, rfl⟩
    rw [hA, mem_bot] at this
    exact this
  let f₁ : S →* H := f.comp S.subtype
  haveI hBn : f₁.ker.Normal := inferInstance
  have hB : f₁.ker.map g = ⊥ := by
    haveI : (f₁.ker.map g).Normal := hBn.map g hg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f₁.ker.map g) with h | h
    · exact h
    · exfalso
      apply hnsolv
      have hp : IsPGroup 3 K := by
        intro kk
        have hkk : kk ∈ f₁.ker.map g := by rw [h]; exact Subgroup.mem_top kk
        obtain ⟨b, hb, rfl⟩ := hkk
        obtain ⟨n, hn⟩ := hf b (MonoidHom.mem_ker.mp hb)
        refine ⟨n, ?_⟩
        rw [← map_pow]
        exact hAker _ (by simpa using hn)
      haveI : Group.IsNilpotent K := hp.isNilpotent
      infer_instance
  apply hnsolv
  have hker : f₁.ker ≤ g.ker := by
    intro s hs
    have : g s ∈ f₁.ker.map g := ⟨s, hs, rfl⟩
    rw [hB, mem_bot] at this
    exact this
  haveI : Group.IsSolvable f₁.range := inferInstance
  haveI : Group.IsSolvable (S ⧸ f₁.ker) :=
    Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientKerEquivRange f₁).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivRange f₁).symm.surjective
  exact Group.isSolvable_of_surjective (f := QuotientGroup.lift f₁.ker g hker) (by
    intro kk
    obtain ⟨s, rfl⟩ := hg kk
    exact ⟨s, rfl⟩)

section Embedding

variable {G : Type} [Group G] [Finite G] {M P : Subgroup G} {x k : G}

@[expose] def embed (hPM : P ≤ M) : ↥P →* Red ↥M := (pr ↥M).comp (Subgroup.inclusion hPM)

theorem embed_apply (hPM : P ≤ M) (p : ↥P) : embed hPM p = pr ↥M ⟨p.1, hPM p.2⟩ := rfl

theorem embed_injective (hs : IsSylowOf 3 P M) : Function.Injective (embed hs.le) := by
  intro a b h
  have hP3 : IsPGroup 3 (P.subgroupOf M) := hs.isPGroup.comap_subtype
  have h1 := GL83P3L28Red.injOn_pr hP3 (a := Subgroup.inclusion hs.le a)
    (b := Subgroup.inclusion hs.le b) (mem_subgroupOf.mpr a.2) (mem_subgroupOf.mpr b.2) h
  exact Subtype.ext (congrArg (fun z : ↥M => (z : G)) h1)

theorem range_embed (hPM : P ≤ M) : (embed hPM).range = (P.subgroupOf M).map (pr ↥M) := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨Subgroup.inclusion hPM p, mem_subgroupOf.mpr p.2, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m.1, mem_subgroupOf.mp hm⟩, rfl⟩

theorem isSylowOf_subgroupOf (hs : IsSylowOf 3 P M) : IsSylowOf 3 (P.subgroupOf M) ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← isSylowOf_map_subtype_iff M, subgroupOf_map_subtype, inf_eq_left.mpr hs.le,
    ← MonoidHom.range_eq_map, range_subtype]
  exact hs

theorem sylow_embed (hs : IsSylowOf 3 P M) : IsSylowOf 3 (embed hs.le).range ⊤ := by
  rw [range_embed]
  exact GL83P3L28Red.sylow_map (isSylowOf_subgroupOf hs)

theorem focal_embed (hPM : P ≤ M) (hf : P ≤ ⁅M, M⁆) :
    (embed hPM).range ≤ ⁅(⊤ : Subgroup (Red ↥M)), (⊤ : Subgroup (Red ↥M))⁆ := by
  rintro _ ⟨p, rfl⟩
  have h1 : (p : G) ∈ (⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆).map M.subtype := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hf p.2
  obtain ⟨m, hm, hmp⟩ := h1
  have h3 : (⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆).map (pr ↥M) =
      ⁅(⊤ : Subgroup (Red ↥M)), (⊤ : Subgroup (Red ↥M))⁆ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rw [← h3]
  refine ⟨m, hm, ?_⟩
  rw [embed_apply]
  congr 1
  exact Subtype.ext hmp

end Embedding

section Fields

variable {G : Type} [Group G] [Finite G] {M P : Subgroup G} {x k : G}

theorem shapeMap_zpowers (hPM : P ≤ M) (hk : k ∈ P) :
    shapeMap (embed hPM) (zpowers k) = zpowers (embed hPM ⟨k, hk⟩) := by
  unfold shapeMap
  have : (zpowers k).subgroupOf P = zpowers (⟨k, hk⟩ : P) := by
    ext ⟨p, hp⟩
    rw [mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext (by simpa using hi)⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by simpa using congrArg Subtype.val hi⟩
  rw [this, MonoidHom.map_zpowers]

theorem k_norm_embed (hPM : P ≤ M) (hk : k ∈ P) (hn : P ≤ normalizer (zpowers k : Set G)) :
    (embed hPM).range ≤ normalizer (zpowers (embed hPM ⟨k, hk⟩) : Set (Red ↥M)) := by
  have := shapeMap_normalizer (embed hPM) hn
  rwa [shapeMap_zpowers hPM hk] at this

theorem k_cube_embed (hPM : P ≤ M) (hφ : Function.Injective (embed hPM)) (hk : k ∈ P)
    (h : k ^ 3 ∈ L28Z P) : embed hPM ⟨k, hk⟩ ^ 3 ∈ L28Z (embed hPM).range := by
  refine (mem_L28Z_range (embed hPM) hφ).mpr ⟨k ^ 3, P.pow_mem hk 3, h, ?_⟩
  rw [← map_pow]
  rfl

theorem not_le_centralizer (hc : L28ClosedConfig G M P x k) (hxP : x ∈ P)
    (K : Subgroup (Red ↥M)) (hK : IsSimpleGroup K) (hKn : ∃ a b : K, a * b ≠ b * a)
    (h3 : 3 ∣ Nat.card K) :
    ¬ K ≤ centralizer ({embed hc.sylow.le ⟨x, hxP⟩} : Set (Red ↥M)) := by
  intro hKc
  haveI := hK
  have hPM : P ≤ M := hc.sylow.le
  obtain ⟨N₀, H, hH, f, hN₀W, hN₀n, hN₀c, hHs, hf⟩ := hc.solv
  haveI : (N₀.subgroupOf (M ⊓ centralizer ({x} : Set G))).Normal := hN₀n
  have hN₁ : ¬ 3 ∣ Nat.card (N₀.subgroupOf (M ⊓ centralizer ({x} : Set G))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀W).toEquiv]
    exact hN₀c
  have hf' : ∀ w : ↥(M ⊓ centralizer ({x} : Set G)), f w = 1 →
      ∃ n : ℕ, w ^ 3 ^ n ∈ N₀.subgroupOf (M ⊓ centralizer ({x} : Set G)) := by
    intro w hw
    obtain ⟨n, hn⟩ := hf w hw
    exact ⟨n, mem_subgroupOf.mpr (by simpa using hn)⟩
  let ψ : ↥(M ⊓ centralizer ({x} : Set G)) →* Red ↥M :=
    (pr ↥M).comp (Subgroup.inclusion (inf_le_left : M ⊓ centralizer ({x} : Set G) ≤ M))
  have hg : Function.Surjective (ψ.subgroupComap K) := by
    rintro ⟨y, hy⟩
    have hxM : x ∈ M := hPM hxP
    obtain ⟨n, hn⟩ := hc.sylow.isPGroup ⟨x, hxP⟩
    have hxn : (⟨x, hxM⟩ : ↥M) ^ 3 ^ n = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hn)
    have hyc : y * pr ↥M ⟨x, hxM⟩ = pr ↥M ⟨x, hxM⟩ * y :=
      mem_centralizer_singleton_iff.mp (hKc hy)
    obtain ⟨c, hcu, hcy⟩ := GL83P3L28Red.lift_centralizer hxn hyc
    have hcW : (c : G) ∈ M ⊓ centralizer ({x} : Set G) :=
      ⟨c.2, mem_centralizer_singleton_iff.mpr (congrArg (fun z : ↥M => (z : G)) hcu)⟩
    refine ⟨⟨⟨(c : G), hcW⟩, ?_⟩, Subtype.ext ?_⟩
    · show pr ↥M c ∈ K
      rw [hcy]
      exact hy
    · show pr ↥M c = y
      exact hcy
  exact no_simple_section hKn h3 (N₀.subgroupOf (M ⊓ centralizer ({x} : Set G))) hN₁ f hf'
    (K.comap ψ) (ψ.subgroupComap K) hg

theorem exists_closedData (hc : L28ClosedConfig G M P x k) :
    ∃ (P' : Subgroup (Red ↥M)) (x' k' : Red ↥M), ClosedData P' x' k' := by
  have hPM : P ≤ M := hc.sylow.le
  have hxP : x ∈ P := (GL83P3L28Aux.mem_L28Z_iff.mp hc.x_mem).1
  have hφ : Function.Injective (embed hPM) := embed_injective hc.sylow
  have hkM : k ∈ M := hPM hc.k_mem
  refine ⟨(embed hPM).range, embed hPM ⟨x, hxP⟩, embed hPM ⟨k, hc.k_mem⟩, ?_⟩
  exact
    { catalog := GL83P3L28Red.catalog_red hc.kgroup
      sylow := sylow_embed hc.sylow
      focal := focal_embed hPM hc.focal
      shape := L28Shape.of_injective_hom (embed hPM) hφ hc.shape
      x_mem := (mem_L28Z_range (embed hPM) hφ).mpr ⟨x, hxP, hc.x_mem, rfl⟩
      x_ne := fun h => hc.x_ne (by
        simpa using congrArg Subtype.val (hφ (h.trans (map_one _).symm)))
      k_mem := ⟨_, rfl⟩
      k_order := by
        rw [orderOf_injective _ hφ, Subgroup.orderOf_mk]
        exact hc.k_order
      k_norm := k_norm_embed hPM hc.k_mem hc.k_norm
      k_cube := k_cube_embed hPM hφ hc.k_mem hc.k_cube
      x_not := by
        intro hx
        obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hx
        have h1 : embed hPM (⟨k, hc.k_mem⟩ ^ i) = embed hPM ⟨x, hxP⟩ := by
          rw [map_zpow]
          exact hi
        apply hc.x_not
        exact ⟨i, by simpa using congrArg Subtype.val (hφ h1)⟩
      z_card := by
        rw [← hc.z_card]
        refine (Nat.card_eq_of_bijective
          (fun z : ↥(L28Z P) => (⟨embed hPM ⟨z.1, (GL83P3L28Aux.mem_L28Z_iff.mp z.2).1⟩,
            (mem_L28Z_range (embed hPM) hφ).mpr
              ⟨z.1, (GL83P3L28Aux.mem_L28Z_iff.mp z.2).1, z.2, rfl⟩⟩ :
            ↥(L28Z (embed hPM).range))) ⟨?_, ?_⟩).symm
        · intro a b h
          have h1 := hφ (congrArg (fun z : ↥(L28Z (embed hPM).range) => (z : Red ↥M)) h)
          exact Subtype.ext (congrArg (fun z : ↥P => (z : G)) h1)
        · rintro ⟨y, hy⟩
          obtain ⟨z₀, h₀, hz₀, rfl⟩ := (mem_L28Z_range (embed hPM) hφ).mp hy
          exact ⟨⟨z₀, hz₀⟩, rfl⟩
      invert := by
        obtain ⟨ι, hιM, hιx, hιk⟩ := hc.invert
        refine ⟨pr ↥M ⟨ι, hιM⟩, ?_, ?_⟩
        · show pr ↥M ⟨ι, hιM⟩ * pr ↥M ⟨x, hPM hxP⟩ * (pr ↥M ⟨ι, hιM⟩)⁻¹ = pr ↥M ⟨x, hPM hxP⟩
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext hιx
        · have hk3 : embed hPM ⟨k, hc.k_mem⟩ ^ 3 = pr ↥M ((⟨k, hkM⟩ : ↥M) ^ 3) := by
            rw [map_pow]
            rfl
          rw [hk3, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
          congr 1
          exact Subtype.ext (by simpa using hιk)
      solv := fun K hK hKn h3 => not_le_centralizer hc hxP K hK hKn h3 }

theorem exists_normal_of_pCore_ne_bot (M : Subgroup G) (hp : CFSG.pCore 3 (Red ↥M) ≠ ⊥) :
    ∃ N : Subgroup G, GLBPrimeCore 3 M < N ∧ N ≤ M ∧ M ≤ normalizer (N : Set G) ∧
      ∀ g ∈ N, ∃ n : ℕ, g ^ 3 ^ n ∈ GLBPrimeCore 3 M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker : ∀ m : ↥M, pr ↥M m = 1 ↔ (m : G) ∈ GLBPrimeCore 3 M := by
    intro m
    rw [← MonoidHom.mem_ker, GL83P3L28Red.ker_pr, ← mem_subgroupOf, glbPrimeCore_subgroupOf]
  let N : Subgroup G := ((CFSG.pCore 3 (Red ↥M)).comap (pr ↥M)).map M.subtype
  have hmemN : ∀ g : G, g ∈ N ↔ ∃ m : ↥M, (m : G) = g ∧ pr ↥M m ∈ CFSG.pCore 3 (Red ↥M) := by
    intro g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, rfl, hm⟩
    · rintro ⟨m, rfl, hm⟩
      exact ⟨m, hm, rfl⟩
  have hNM : N ≤ M := Subgroup.map_subtype_le _
  refine ⟨N, ?_, hNM, ?_, ?_⟩
  · refine lt_of_le_of_ne (fun g hg => ?_) (fun heq => ?_)
    · have hgM : g ∈ M := glbPrimeCore_le 3 M hg
      exact (hmemN g).mpr ⟨⟨g, hgM⟩, rfl, by rw [(hker ⟨g, hgM⟩).mpr hg]; exact Subgroup.one_mem _⟩
    · obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hp
      obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := ↥M) 3) (y : Red ↥M)
      have hmN : (m : G) ∈ N := (hmemN _).mpr ⟨m, rfl, by rw [hm]; exact y.2⟩
      rw [← heq] at hmN
      exact hy1 (Subtype.ext (by rw [← hm]; exact (hker m).mpr hmN))
  · rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hNM]
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, hmn, hm⟩ := (hmemN _).mp (mem_subgroupOf.mp hn)
    have hmn' : m = n := Subtype.ext hmn
    subst hmn'
    refine mem_subgroupOf.mpr ((hmemN _).mpr ⟨g * m * g⁻¹, rfl, ?_⟩)
    rw [map_mul, map_mul, map_inv]
    exact (CFSG.pCore_normal (p := 3) (G := Red ↥M)).conj_mem _ hm _
  · intro g hg
    obtain ⟨m, rfl, hm⟩ := (hmemN g).mp hg
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 3) (G := Red ↥M) ⟨_, hm⟩
    refine ⟨n, ?_⟩
    have h1 : pr ↥M (m ^ 3 ^ n) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hn
    exact (hker (m ^ 3 ^ n)).mp h1

end Fields

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl
