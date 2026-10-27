module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem le_ker_of_isSimpleGroup {W Λ : Type*} [Group W] [Group Λ] [IsSimpleGroup Λ] {p : ℕ}
    (φ : W →* Λ) (hφ : Function.Surjective φ) (N : Subgroup W) [N.Normal]
    (hN : ∀ n ∈ N, p.Coprime (orderOf n)) {x : Λ} (hx : x ≠ 1) {k : ℕ} (hxk : x ^ p ^ k = 1) :
    N ≤ φ.ker := by
  have : (N.map φ).Normal := Subgroup.Normal.map ‹_› φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map φ) with hbot | htop
  · exact (Subgroup.map_eq_bot_iff _).mp hbot
  · obtain ⟨n, hn, rfl⟩ : x ∈ N.map φ := htop ▸ Subgroup.mem_top x
    have h1 : orderOf (φ n) = 1 := Nat.eq_one_of_dvd_coprimes ((hN n hn).pow_left k)
      (orderOf_dvd_of_pow_eq_one hxk) (orderOf_map_dvd φ n)
    exact (hx (orderOf_eq_one_iff.mp h1)).elim

section Reduced

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {z : G}
  {Pbar : Sylow p (Subgroup.centralizer ({z} : Set G) ⧸
    primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)}
  {K : Subgroup (Subgroup.centralizer ({z} : Set G) ⧸
    primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)}

theorem D1ReducedCentralizer.le_of_isPerfect (hRC : D1ReducedCentralizer p P M z Pbar K)
    (hSch : KFactCatalogSchreier) {A : Subgroup (Subgroup.centralizer ({z} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)}
    (hA : Group.IsPerfect A) : A ≤ K := by
  have := hRC.normal
  have hE := hRC.red.le_layer_of_isPerfect hRC.catalog hSch hRC.comp hA fun L hL => by
    rw [hRC.unique L hL, Subgroup.normalizer_eq_top]
    exact le_top
  refine hE.trans (sSup_le fun L hL => ?_)
  rw [hRC.unique L ((CFSG.isComponent_iff_open L).mp hL)]

theorem D1ReducedCentralizer.exists_surjective_of_le (hRC : D1ReducedCentralizer p P M z Pbar K)
    (hSch : KFactCatalogSchreier) {W : Subgroup G}
    (hW : W ≤ Subgroup.centralizer ({z} : Set G)) {Λ : Type} [Group Λ] [Finite Λ]
    (hΛ : Group.IsPerfect Λ) (φ : W →* Λ) (hφ : Function.Surjective φ)
    (hker : (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p).comap
      (Subgroup.inclusion hW) ≤ φ.ker) :
    ∃ (A : Subgroup K) (f : A →* Λ), Function.Surjective f := by
  set ρ : W →* Subgroup.centralizer ({z} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hW) with hρ
  set D : Subgroup W := perfectCore (⊤ : Subgroup W)
  have hDperf : ⁅D, D⁆ = D := perfectCore_perfect _
  have hDφ : D.map φ = ⊤ := by
    rw [map_perfectCore, Subgroup.map_top_of_surjective φ hφ]
    exact perfectCore_eq_self_of_perfect (by rw [← commutator_def]; exact hΛ.commutator_eq_top)
  have hDK : D.map ρ ≤ K := hRC.le_of_isPerfect hSch
    (Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hDperf]))
  set ρK : D →* K := (ρ.comp D.subtype).codRestrict K fun d => hDK ⟨d, d.2, rfl⟩
  have hφD : Function.Surjective (φ.comp D.subtype) := by
    intro l
    obtain ⟨d, hd, hdl⟩ : l ∈ D.map φ := hDφ ▸ Subgroup.mem_top l
    exact ⟨⟨d, hd⟩, hdl⟩
  obtain ⟨f, -, hf, -⟩ := exists_surjective_comp_eq ρK.rangeRestrict ρK.rangeRestrict_surjective
    (φ.comp D.subtype) hφD (by
      rw [MonoidHom.ker_rangeRestrict]
      intro d hd
      have h1 : ρ (d : W) = 1 := congrArg Subtype.val hd
      rw [hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact hker h1)
  exact ⟨ρK.range, f, hf⟩

theorem D1ReducedCentralizer.exists_surjective_of_isSimpleGroup
    (hRC : D1ReducedCentralizer p P M z Pbar K) (hSch : KFactCatalogSchreier) {W : Subgroup G}
    (hW : W ≤ Subgroup.centralizer ({z} : Set G)) {Λ : Type} [Group Λ] [Finite Λ]
    [IsSimpleGroup Λ] (hΛ : Group.IsPerfect Λ) (φ : W →* Λ) (hφ : Function.Surjective φ)
    {x : Λ} (hx : x ≠ 1) {k : ℕ} (hxk : x ^ p ^ k = 1) :
    ∃ (A : Subgroup K) (f : A →* Λ), Function.Surjective f := by
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G)) p
  have hN : ∀ n ∈ (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p).comap
      (Subgroup.inclusion hW), p.Coprime (orderOf n) := by
    intro n hn
    have h1 : orderOf (Subgroup.inclusion hW n) ∣ Nat.card
        (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) :=
      Subgroup.orderOf_dvd_natCard _ hn
    rw [orderOf_injective _ (Subgroup.inclusion_injective hW)] at h1
    exact hO.coprime_dvd_right h1
  exact hRC.exists_surjective_of_le hSch hW hΛ φ hφ (le_ker_of_isSimpleGroup φ hφ _ hN hx hxk)

end Reduced

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} {e : H}

theorem D1CaseTwoEscapeData.exists_surjective (he : D1CaseTwoEscapeData p P M H R Rbar L e)
    {Pbar : Sylow p (Subgroup.centralizer ({(e : G)} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({(e : G)} : Set G)) p)}
    {K : Subgroup (Subgroup.centralizer ({(e : G)} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({(e : G)} : Set G)) p)}
    (hRC : D1ReducedCentralizer p P M (e : G) Pbar K) (hSch : KFactCatalogSchreier) :
    ∃ (A : Subgroup K) (f : A →* L), Function.Surjective f := by
  have hred := he.data.cfg.red
  have hp := hred.prime
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set W : Subgroup G := Subgroup.centralizer ({(e : G)} : Set G) ⊓ (L.comap π).map H.subtype
  have hWH : W ≤ H := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hWC : W ≤ Subgroup.centralizer ({(e : G)} : Set G) := inf_le_left
  have hφ₀ : ∀ w : W, π (Subgroup.inclusion hWH w) ∈ L := by
    rintro ⟨w, -, h, hh, rfl⟩
    exact hh
  set φ : W →* L := (π.comp (Subgroup.inclusion hWH)).codRestrict L hφ₀
  have hφ : Function.Surjective φ := by
    intro l
    obtain ⟨g, hgC, hgl⟩ := he.exists_lift (he.le_centralizer_mk l.2)
    have hgL : g ∈ L.comap π := by
      rw [Subgroup.mem_comap, hgl]
      exact l.2
    exact ⟨⟨g, hgC, g, hgL, rfl⟩, Subtype.ext hgl⟩
  have hZ := hred.center_eq_bot_of_isCyclic he.comp (he.data.cyclic L he.comp)
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := he.comp.2.2.2
  have : IsSimpleGroup L :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨t, htRL, ht, -⟩ := exists_mem_sylow_inf_component hp hred.ne_two hred.core_eq_bot Rbar
    he.comp
  have hx : (⟨t, htRL.2⟩ : L) ≠ 1 := fun h1 =>
    hp.one_lt.ne' (by rw [← ht, show t = 1 from congrArg Subtype.val h1, orderOf_one])
  have htp : t ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq ht)
  have hxp : (⟨t, htRL.2⟩ : L) ^ p ^ 1 = 1 := by
    rw [pow_one]
    exact Subtype.ext (by rw [Subgroup.coe_pow, htp, Subgroup.coe_one])
  exact hRC.exists_surjective_of_isSimpleGroup hSch hWC ⟨he.comp.2.2.1⟩ φ hφ hx hxp

end Data

end CFSG.AGLEmbedding
