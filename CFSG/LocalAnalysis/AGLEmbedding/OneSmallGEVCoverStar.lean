module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarIa
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem coprime_of_mk_inclusion_eq_one {H' W : Subgroup G} (hWH : W ≤ H') (w : W)
    (hw : QuotientGroup.mk' (primeComplementCore (G := H') p) (Subgroup.inclusion hWH w) = 1) :
    p.Coprime (orderOf w) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw
  have h2 := Subgroup.orderOf_dvd_natCard _ hw
  rw [orderOf_injective _ (Subgroup.inclusion_injective hWH)] at h2
  exact (primeComplementCore_coprime (G := H') p).coprime_dvd_right h2

theorem D1OneSmallData.exists_cover (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) :
    ∃ (W : Subgroup G) (_ : W ≤ Subgroup.centralizer ({z} : Set G)) (φ : W →* K),
      Function.Surjective φ ∧ ∀ w, φ w = 1 → p.Coprime (orderOf w) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hO := primeComplementCore_coprime (G := H) p
  obtain ⟨-, hzp, hzH, hzC⟩ := hz
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set W : Subgroup G := Subgroup.centralizer ({z} : Set G) ⊓ (K.comap π).map H.subtype
  have hWH : W ≤ H := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := inf_le_left
  have hφ₀ : ∀ w : W, π (Subgroup.inclusion hWH w) ∈ K := by
    rintro ⟨w, -, h, hh, rfl⟩
    exact hh
  set φ : W →* K := (π.comp (Subgroup.inclusion hWH)).codRestrict K hφ₀
  have hzH' : orderOf (⟨z, hzH⟩ : H) = p := (Subgroup.orderOf_coe _).symm.trans hzp
  refine ⟨W, hWC, φ, ?_, fun w hw => coprime_of_mk_inclusion_eq_one hWH w
    (congrArg Subtype.val hw)⟩
  intro k
  obtain ⟨g, hg, hgk⟩ := exists_mem_centralizer_mk_eq hp _ hO
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzH', pow_one]))
    (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzC k k.2))
  have hgC : (g : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
  have hgK : g ∈ K.comap π := by
    rw [Subgroup.mem_comap, hgk]
    exact k.2
  exact ⟨⟨g, hgC, g, hgK, rfl⟩, Subtype.ext hgk⟩

theorem inf_centralizer_eq_bot_of_center {X : Type*} [Group X] {L : Subgroup X}
    (hZ : Subgroup.center L = ⊥) : L ⊓ Subgroup.centralizer (L : Set X) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun c hc' => ?_
  have hcen : (⟨c, hc'.1⟩ : L) ∈ Subgroup.center L :=
    Subgroup.mem_center_iff.mpr fun k =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hc'.2 k k.2)
  rw [hZ, Subgroup.mem_bot] at hcen
  exact congrArg Subtype.val hcen

theorem lt_card_of_not_isCyclic [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    {T : Subgroup X} (hT : IsPGroup p T) (hnc : ¬ IsCyclic T) : p < Nat.card T := by
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  have hp := (Fact.out : p.Prime)
  rcases n with _ | _ | n
  · exact absurd (by rw [pow_zero] at hn; exact (Subgroup.card_eq_one.mp hn) ▸
      (inferInstance : IsCyclic (⊥ : Subgroup X))) hnc
  · exact absurd (isCyclic_of_prime_card (p := p) (by rw [hn, pow_one])) hnc
  · rw [hn]
    calc p < p ^ 2 := by nlinarith [hp.two_le]
      _ ≤ p ^ (n + 2) := Nat.pow_le_pow_right hp.pos (by omega)

theorem card_rbar_eq {Hs : Subgroup G} {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hcfg : D1ComponentConfig p P M Hs R Rbars) :
    Nat.card (Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) = Nat.card R := by
  have hp := hcfg.red.prime
  rw [hcfg.rbar, card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p)
    (T := R.subgroupOf Hs) hcfg.ext.isPGroup.comap_subtype]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.ext.le_H).toEquiv

theorem D1OneSmallData.mem_centralizer_of_mem_sup_star (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z)
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)))
    {Hs : Subgroup G} (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    {Ks : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hds : D1CompI p P M Hs R Rbars Ks) (hout : Group.IsSolvable (Outer Ks))
    (hin : d1StarElt p hCHs ∈ Ks ⊔ Subgroup.centralizer (Ks : Set _)) :
    d1StarElt p hCHs ∈ Subgroup.centralizer (Ks : Set _) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  by_contra hnc
  set C := Subgroup.centralizer (Ks : Set (Hs ⧸ primeComplementCore (G := Hs) p)) with hC
  have hKn : Ks.Normal := hds.cfg.red.normal_of_rankOne hds.comp hds.noncyclic
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hKC : Ks ⊓ C = ⊥ := inf_centralizer_eq_bot_of_center hds.center
  have hcomm : ∀ x ∈ Ks, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy x hx
  obtain ⟨k, hk, c, hc, hkc⟩ := Subgroup.mem_sup_of_normal_left.mp hin
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [one_mul] at hkc
    exact hnc (hkc ▸ hc)
  have hzs : d1StarElt p hCHs ^ p = 1 := by
    have h0 : (⟨z, mem_of_centralizer_le hCHs⟩ : Hs) ^ p = 1 :=
      Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one, ← hz.2.1,
        pow_orderOf_eq_one])
    rw [d1StarElt, ← map_pow, h0, map_one]
  have hkp : k ^ p = 1 := by
    have hcomm' : Commute k c := hcomm k hk c hc
    have h1 : k ^ p * c ^ p = 1 := by rw [← hcomm'.mul_pow, hkc, hzs]
    have h2 : k ^ p ∈ Ks ⊓ C := by
      refine ⟨Ks.pow_mem hk p, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact C.inv_mem (C.pow_mem hc p)
    rwa [hKC, Subgroup.mem_bot] at h2
  obtain ⟨W, hWC, φ, hφs, hφk⟩ := D1OneSmallData.exists_cover hd hz
  set Y := perfectCore (⊤ : Subgroup W) with hY
  set f := φ.comp Y.subtype with hf
  have hfs : Function.Surjective f := by
    have h1 : Y.map φ = ⊤ := by
      rw [hY, map_perfectCore, Subgroup.map_top_of_surjective φ hφs]
      exact perfectCore_eq_self_of_perfect hd.comp.2.2.1
    intro x
    have hx : x ∈ Y.map φ := h1 ▸ Subgroup.mem_top x
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, rfl⟩
  have hfk : ∀ y : Y, f y = 1 → p.Coprime (orderOf y) := fun y hy => by
    rw [← Subgroup.orderOf_coe]
    exact hφk y hy
  set ρ := (QuotientGroup.mk' (primeComplementCore (G := Hs) p)).comp
    (Subgroup.inclusion (hWC.trans hCHs)) with hρ
  set g := ρ.comp Y.subtype with hg
  have hgk : ∀ y : Y, g y = 1 → p.Coprime (orderOf y) := fun y hy => by
    rw [← Subgroup.orderOf_coe]
    exact coprime_of_mk_inclusion_eq_one (hWC.trans hCHs) (y : W) hy
  have hgKC : ∀ y : Y, g y ∈ Ks ⊔ C := by
    have hJ : ⁅Y.map ρ, Y.map ρ⁆ = Y.map ρ := by
      rw [← Subgroup.map_commutator, hY, perfectCore_perfect]
    have hle := le_sup_centralizer_of_isPerfect (K := Ks) (Subgroup.isPerfect_iff.mpr hJ) hout
    exact fun y => hle ⟨y, y.2, rfl⟩
  have hgz : ∀ y : Y, g y * (k * c) = k * c * g y := by
    intro y
    rw [hkc]
    have hyz : ((y : W) : G) * z = z * ((y : W) : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hWC (y : W).2)
    have h1 : Subgroup.inclusion (hWC.trans hCHs) (y : W) * ⟨z, mem_of_centralizer_le hCHs⟩ =
        ⟨z, mem_of_centralizer_le hCHs⟩ * Subgroup.inclusion (hWC.trans hCHs) (y : W) :=
      Subtype.ext hyz
    simp only [hg, hρ, MonoidHom.comp_apply, d1StarElt]
    rw [← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' _) h1
  obtain ⟨T₁, hT₁, -⟩ := hd.exists_sylow
  obtain ⟨Ts, hTs⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbars
    (ComponentClassification.Components.mathlib_subnormal_of_chain hds.comp.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨Tc, hTc⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbars hCn.isSubnormal
  have hm : ∀ S : Sylow p K, Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      K : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤ Nat.card S := by
    intro S
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity,
      Sylow.card_eq_multiplicity]
  have ht : ∀ Q : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p), Q ≤ Ks → IsPGroup p Q →
      Nat.card Q ≤ Nat.card ((Rbars : Subgroup _) ⊓ Ks : Subgroup _) := fun Q hQ hQp => by
    rw [← hTs]
    exact card_le_card_map_sylow Ts hQp hQ
  have hs : ∀ Q : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p), Q ≤ C → IsPGroup p Q →
      Nat.card Q ≤ Nat.card ((Rbars : Subgroup _) ⊓ C : Subgroup _) := fun Q hQ hQp => by
    rw [← hTc]
    exact card_le_card_map_sylow Tc hQp hQ
  have h1 : Nat.card ((Rbars : Subgroup _) ⊓ Ks : Subgroup _) *
      Nat.card ((Rbars : Subgroup _) ⊓ C : Subgroup _) ≤ p * Nat.card ((Rbar : Subgroup _) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    have hdisj : ((Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ⊓ Ks) ⊓
        ((Rbars : Subgroup _) ⊓ C) = ⊥ := by
      rw [eq_bot_iff, ← hKC]
      exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    have h2 := mul_card_le_of_inf_eq_bot inf_le_left inf_le_left hdisj
    rw [card_rbar_eq hds.cfg] at h2
    exact h2.trans hR
  have h2 : p ≤ Nat.card ((Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ⊓ C :
      Subgroup _) := by
    obtain ⟨zs, hzsR, -, hzsp, hzsc⟩ := hds.z
    have hle : Subgroup.zpowers zs ≤ (Rbars : Subgroup _) ⊓ C :=
      Subgroup.zpowers_le.mpr ⟨hzsR, hzsc⟩
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, hzsp] at this
  have h3 : p < Nat.card ((Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ⊓ Ks :
      Subgroup _) :=
    lt_card_of_not_isCyclic (Rbars.isPGroup'.to_le inf_le_left) hds.noncyclic
  obtain ⟨hsimple, hnab⟩ := (⟨hd.cfg, hd.comp, hd.center, hd.noncyclic, hd.z⟩ :
    D1CompI p P M H R Rbar K).isSimpleGroup
  exact false_of_inner_cover f hfs hnab hfk g hgk Ks C hKC hcomm hk hc hk1 hkp hgKC hgz hm ht hs
    h1 h2 h3

end CFSG.AGLEmbedding
