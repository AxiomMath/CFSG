module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GFree
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GImage
public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0)

theorem a10t1_fb_injOn_of_ker {H K : Type*} [Group H] [Finite H] [Group K] (f : H →* K)
    (hO : Nat.Coprime 5 (Nat.card f.ker)) {A : Subgroup H} (hA : IsPGroup 5 A) :
    Set.InjOn f (A : Set H) := by
  intro a ha b hb hab
  have h1 : a⁻¹ * b ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  have h2 : a⁻¹ * b ∈ A ⊓ f.ker := ⟨A.mul_mem (A.inv_mem ha) hb, h1⟩
  rw [CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup (by norm_num) hA hO, Subgroup.mem_bot,
    inv_mul_eq_one] at h2
  exact h2

theorem a10t1_fb_core {G : Type} [Group G] {M J T : Subgroup G} {x : G} {Q Y : Type*} [Group Q] [Group Y]
    (π : ↥M →* Y) (ψ : ↥J →* Q) (S : Subgroup Q)
    (hTJ : T ≤ J) (hTM : T ≤ M) (hxM : x ∈ M)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set G))
    (hψinj : ∀ a b : ↥J, a.1 ∈ T → b.1 ∈ T → ψ a = ψ b → a = b)
    (hπinj : ∀ a b : ↥M, a.1 ∈ T → b.1 ∈ T → π a = π b → a = b)
    (hSmem : ∀ t : ↥T, ψ ⟨t.1, hTJ t.2⟩ ∈ S)
    (hfrat : ∀ n ∈ Subgroup.normalizer (S : Set Q), ∃ (f : G) (hf : f ∈ J),
      f ∈ Subgroup.normalizer (T : Set G) ∧ ψ ⟨f, hf⟩ = n)
    (hNJM : J ⊓ Subgroup.normalizer (T : Set G) ≤ M)
    (hirred : ∀ A : Subgroup Q, A ≤ S →
      (∀ n ∈ Subgroup.normalizer (S : Set Q), ∀ a ∈ A, n * a * n⁻¹ ∈ A) → A = ⊥ ∨ A = S)
    (hnofix : ∀ a ∈ S, a ≠ 1 → ∃ n ∈ Subgroup.normalizer (S : Set Q), n * a ≠ a * n) :
    ((J ⊓ Subgroup.normalizer (T : Set G)).subgroupOf M).map π ≤
        Subgroup.centralizer ({π ⟨x, hxM⟩} : Set Y) ∧
      (∀ f ∈ ((J ⊓ Subgroup.normalizer (T : Set G)).subgroupOf M).map π,
        ∀ t ∈ (T.subgroupOf M).map π, f * t * f⁻¹ ∈ (T.subgroupOf M).map π) ∧
      (∀ A : Subgroup Y, A ≤ (T.subgroupOf M).map π →
        (∀ f ∈ ((J ⊓ Subgroup.normalizer (T : Set G)).subgroupOf M).map π, ∀ a ∈ A,
          f * a * f⁻¹ ∈ A) → A = ⊥ ∨ A = (T.subgroupOf M).map π) ∧
      (∀ t ∈ (T.subgroupOf M).map π,
        (∀ f ∈ ((J ⊓ Subgroup.normalizer (T : Set G)).subgroupOf M).map π, f * t * f⁻¹ = t) →
        t = 1) := by
  let πT : ↥T →* Y := π.comp (Subgroup.inclusion hTM)
  let ψT : ↥T →* Q := ψ.comp (Subgroup.inclusion hTJ)
  have hπT : Function.Injective πT := fun a b h =>
    Subgroup.inclusion_injective hTM (hπinj _ _ a.2 b.2 h)
  have hψT : Function.Injective ψT := fun a b h =>
    Subgroup.inclusion_injective hTJ (hψinj _ _ a.2 b.2 h)
  have hTbar : ∀ y, y ∈ (T.subgroupOf M).map π ↔ ∃ t : ↥T, πT t = y := by
    intro y
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m.1, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Subgroup.inclusion hTM t, Subgroup.mem_subgroupOf.mpr t.2, rfl⟩
  have hFmem : ∀ (f : G) (hfJ : f ∈ J) (hfN : f ∈ Subgroup.normalizer (T : Set G)),
      π ⟨f, hNJM (Subgroup.mem_inf.mpr ⟨hfJ, hfN⟩)⟩ ∈
        ((J ⊓ Subgroup.normalizer (T : Set G)).subgroupOf M).map π := fun f hfJ hfN =>
    ⟨⟨f, hNJM (Subgroup.mem_inf.mpr ⟨hfJ, hfN⟩)⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hfJ, hfN⟩), rfl⟩
  have hconjπ : ∀ (f : G) (hfJ : f ∈ J) (hfN : f ∈ Subgroup.normalizer (T : Set G)) (t : ↥T),
      πT ⟨f * t.1 * f⁻¹, (Subgroup.mem_normalizer_iff.mp hfN t.1).mp t.2⟩ =
        π ⟨f, hNJM (Subgroup.mem_inf.mpr ⟨hfJ, hfN⟩)⟩ * πT t *
          (π ⟨f, hNJM (Subgroup.mem_inf.mpr ⟨hfJ, hfN⟩)⟩)⁻¹ := by
    intro f hfJ hfN t
    simp only [πT, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hconjψ : ∀ (f : G) (hfJ : f ∈ J) (hfN : f ∈ Subgroup.normalizer (T : Set G)) (t : ↥T),
      ψT ⟨f * t.1 * f⁻¹, (Subgroup.mem_normalizer_iff.mp hfN t.1).mp t.2⟩ =
        ψ ⟨f, hfJ⟩ * ψT t * (ψ ⟨f, hfJ⟩)⁻¹ := by
    intro f hfJ hfN t
    simp only [ψT, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨f, hf, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hfJ : f.1 ∈ J := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hf)).1
    exact hJx hfJ x rfl
  ·
    rintro _ ⟨f, hf, rfl⟩ _ ⟨t, ht, rfl⟩
    refine ⟨f * t * f⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hfN : f.1 ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hf)).2
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp hfN t.1).mp (Subgroup.mem_subgroupOf.mp ht))
  ·
    intro A hA hAinv
    set A'' : Subgroup ↥T := A.comap πT with hA''
    set A₁ : Subgroup Q := A''.map ψT with hA₁
    have hA₁S : A₁ ≤ S := by
      rintro _ ⟨t, -, rfl⟩
      exact hSmem t
    have hinv : ∀ n ∈ Subgroup.normalizer (S : Set Q), ∀ a ∈ A₁, n * a * n⁻¹ ∈ A₁ := by
      intro n hn a ha
      obtain ⟨t, ht, rfl⟩ := ha
      obtain ⟨f, hfJ, hfN, hfn⟩ := hfrat n hn
      refine ⟨⟨f * t.1 * f⁻¹, (Subgroup.mem_normalizer_iff.mp hfN t.1).mp t.2⟩, ?_, ?_⟩
      · show πT _ ∈ A
        rw [hconjπ f hfJ hfN t]
        exact hAinv _ (hFmem f hfJ hfN) _ ht
      · rw [hconjψ f hfJ hfN t, hfn]
    rcases hirred A₁ hA₁S hinv with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨t, rfl⟩ := (hTbar y).mp (hA hy)
      have ht : t ∈ A'' := hy
      have h1 : ψT t ∈ A₁ := ⟨t, ht, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      have h2 : t = 1 := hψT (by rw [h1, map_one])
      rw [h2, map_one]
      exact Subgroup.one_mem _
    · right
      refine le_antisymm hA ?_
      intro y hy
      obtain ⟨t, rfl⟩ := (hTbar y).mp hy
      have h1 : ψT t ∈ A₁ := by rw [h]; exact hSmem t
      obtain ⟨t', ht', hψ⟩ := h1
      have h2 : t' = t := hψT hψ
      subst h2
      exact ht'
  ·
    intro y hy hfix
    obtain ⟨a, rfl⟩ := (hTbar y).mp hy
    by_contra hne
    have ha1 : ψT a ≠ 1 := by
      intro h
      apply hne
      have h2 : a = 1 := hψT (by rw [h, map_one])
      rw [h2, map_one]
    obtain ⟨n, hn, hnc⟩ := hnofix (ψT a) (hSmem a) ha1
    obtain ⟨f, hfJ, hfN, hfn⟩ := hfrat n hn
    have hfix' := hfix _ (hFmem f hfJ hfN)
    have hct : (⟨f * a.1 * f⁻¹, (Subgroup.mem_normalizer_iff.mp hfN a.1).mp a.2⟩ : ↥T) = a :=
      hπT (by rw [hconjπ f hfJ hfN a]; exact hfix')
    have h2 : n * ψT a * n⁻¹ = ψT a := by
      rw [← hfn, ← hconjψ f hfJ hfN a, hct]
    apply hnc
    calc n * ψT a = (n * ψT a * n⁻¹) * n := by group
      _ = ψT a * n := by rw [h2]

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10_F_basic (hS : Setting G) (hU0 : FullCoreLocal G) (hX : A10Facts) (hL : A10L43Facts)
    (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    (hQ : IsA10Type 5 Q) (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    {S : Sylow 5 Q} (hSyl : (S : Subgroup Q) = ((u3T P x J).subgroupOf J).map ψ) (hxM : x ∈ M) :
    a10Img M (J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G)) ≤
        Subgroup.centralizer ({a10π M ⟨x, hxM⟩} : Set (A10Y M)) ∧
      (∀ f ∈ a10Img M (J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G)),
        ∀ t ∈ a10Img M (u3T P x J), f * t * f⁻¹ ∈ a10Img M (u3T P x J)) ∧
      (∀ A : Subgroup (A10Y M), A ≤ a10Img M (u3T P x J) →
        (∀ f ∈ a10Img M (J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G)), ∀ a ∈ A,
          f * a * f⁻¹ ∈ A) → A = ⊥ ∨ A = a10Img M (u3T P x J)) ∧
      (∀ t ∈ a10Img M (u3T P x J),
        (∀ f ∈ a10Img M (J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G)), f * t * f⁻¹ = t) →
        t = 1) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hTP : u3T P x J ≤ (P : Subgroup G) := (inf_le_left : u3T P x J ≤ u3S P x).trans inf_le_left
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hTM : u3T P x J ≤ M := hTP.trans hPM
  have hTne : u3T P x J ≠ ⊥ := by
    intro h
    have h25 := (plane_T_structure hX.sylow hc).1
    rw [h, Subgroup.card_bot] at h25
    norm_num at h25
  have hNJM : J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ≤ M :=
    a10_NJ_le_M hS hU0 hX hc le_rfl hTne
  have hOJ : rankThreePrimeCore 5 J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le 5 J
  have hOcop : Nat.Coprime 5 (Nat.card (rankThreePrimeCore 5 J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime 5 J
  have hcop : Nat.Coprime 5 (Nat.card ψ.ker) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv]
    exact hOcop
  have hTp : IsPGroup 5 (u3T P x J) := P.isPGroup'.to_le hTP
  have hψinj := a10t1_fb_injOn_of_ker ψ hcop (hTp.comap_subtype (K := J))
  have hπcop : Nat.Coprime 5 (Nat.card (a10π M).ker) := by
    rw [QuotientGroup.ker_mk']
    exact primeComplementCore_coprime 5
  have hπinj := a10t1_fb_injOn_of_ker (a10π M) hπcop (hTp.comap_subtype (K := M))
  exact a10t1_fb_core (a10π M) ψ (S : Subgroup Q) hTJ hTM hxM hc.le_cent
    (fun a b ha hb h =>
      hψinj (Subgroup.mem_subgroupOf.mpr ha) (Subgroup.mem_subgroupOf.mpr hb) h)
    (fun a b ha hb h =>
      hπinj (Subgroup.mem_subgroupOf.mpr ha) (Subgroup.mem_subgroupOf.mpr hb) h)
    (fun t => by
      rw [hSyl]
      exact ⟨⟨t.1, hTJ t.2⟩, Subgroup.mem_subgroupOf.mpr t.2, rfl⟩)
    (fun n hn => a10_frattini hc ψ hψ hker le_rfl (by rwa [hSyl] at hn))
    hNJM
    (fun A hA hinv => hL.irred Q hQ S A hA hinv)
    (hX.noFixed Q hQ S)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
