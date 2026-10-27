module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma119
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma135
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13d

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (mem_gLAPPrimeCoreOf_iff)

namespace Lemma136

@[expose] def P1BarInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    (d : ↥M), (d : G) ∈ D → (d : G) ≠ 1 →
      (¬ (d : G) ∈ Subgroup.normalizer (L : Set G) ∨ (d : G) ∈ centBar 3 ⊤ L) →
      ∀ K : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M),
        GLAPComponent 3 (barX 3 M (Lstarsub D L) ⊓
          Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) d} :
            Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) K →
        K ≤ barX 3 M (piStar 3 D)

theorem l136_gamma (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement)
    {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m p B M E A D T L) : Prop95Gamma p M D L := by
  have hS : GLStanding G m p := h.standing
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hp2 : p ≠ 2 := hS.ne_two
  have hD : IsEkIn p 2 A D := h.hD
  have hDA : D ≤ A := hD.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDM : D ≤ M := hDA.trans hAM
  have hyp : Prop95Hyp p M D :=
    { twoLocal := h.pre.1.1
      le := hDM
      plane := ⟨hD.2.1, hD.2.2⟩
      clause_a := fun d hd hd1 =>
        (pCoreOf_two_le_glaPPrimeCoreOf hS.prime hp2 _).trans (h111 h.toSec11 (hDA hd) hd1)
      clause_b := fun d hd hd1 => by
        by_contra hc
        exact h121 (⟨h.toSec11, ⟨hDA hd, hd1⟩, hc⟩ : Cex121 G m p B M E A d)
      clause_c := h.hT1.trans (h.hT2.trans (gammaStar_le_gammaD p D)) }
  have hP := hP95 G m p hS M D hyp
  obtain ⟨hLc, hnc⟩ := hcomp h.toSec13 h.hL
  rcases (hP.2.2 L hLc).2 with hc | ⟨-, ha | hb | hg⟩
  · exact absurd ((barX_mono_of_le p (gammaStar_le_gammaD p D)).trans hc) hnc
  · exact absurd ha (fun ha => h.notAB (Or.inl ha))
  · exact absurd hb (fun hb => h.notAB (Or.inr hb))
  · exact hg

theorem l136_mk_eq_of_barMap_eq {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {M L : Subgroup G} (hLM : L ≤ M) (hsn : IsSubnormal L M) {x y : ↥L}
    (h : barMap p hLM x = barMap p hLM y) :
    (QuotientGroup.mk x : ↥L ⧸ GLAPPrimeCore p ↥L) = QuotientGroup.mk y := by
  rw [QuotientGroup.eq]
  have hk := ker_barMap_eq hp hLM hsn
  have hmem : x⁻¹ * y ∈ (barMap p hLM).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [hk] at hmem
  exact hmem

theorem l136_mk_mem_normalizer_barX {G : Type} [Group G] [Finite G] {p : ℕ} {M K : Subgroup G}
    (hK : K ≤ M) {z : G} (hzM : z ∈ M) (hz : z ∈ Subgroup.normalizer (K : Set G)) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨z, hzM⟩ : ↥M) ∈
      Subgroup.normalizer ((barX p M K : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  have h1 : GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨z, hzM⟩ : ↥M))
      (barX p M K) = barX p M K := by
    rw [← l119_barX_gLBConj hzM hK, gLBConj_eq_of_mem_normalizer hz]
  rw [mem_normalizer_iff_gLBConj_eq]
  exact h1

theorem l136_mem_normalizer_of_bar {G : Type} [Group G] [Finite G] {p : ℕ}
    {M K : Subgroup G} (hK : GLAPComponent p M K) (z : ↥M)
    (hz : QuotientGroup.mk' (GLAPPrimeCore p ↥M) z ∈
      Subgroup.normalizer ((barX p M K : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M))) :
    (z : G) ∈ Subgroup.normalizer (K : Set G) := by
  have hzM : (z : G) ∈ M := z.2
  have hnorm : (z : G) ∈ Subgroup.normalizer ((M : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hzM
  have hGC : GLBConj (z : G) M = M := gLBConj_eq_of_mem_normalizer hnorm
  have hp1 : GLAPComponent p M (GLBConj (z : G) K) := by
    have := glaPComponent_gLBConj hK (z : G)
    rwa [hGC] at this
  have hbar : barX p M (GLBConj (z : G) K) = barX p M K := by
    rw [l119_barX_gLBConj hzM hK.1]
    exact gLBConj_eq_of_mem_normalizer hz
  have heq : GLBConj (z : G) K = K := glaPComponent_unique hp1 hK hbar
  rw [mem_normalizer_iff_gLBConj_eq]
  exact heq

theorem l136_centBar_of_centralizes {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {M L : Subgroup G} (hsn : IsSubnormal L M) {d : G} (hdM : d ∈ M)
    (hdN : d ∈ Subgroup.normalizer (L : Set G))
    (hc : ∀ q ∈ barX p M L, QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨d, hdM⟩ : ↥M) * q =
      q * QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨d, hdM⟩ : ↥M)) :
    d ∈ centBar p ⊤ L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hLM : L ≤ M := isSubnormal_le' hsn
  rw [Sec13d.mem_centBar_iff]
  refine ⟨Subgroup.mem_top _, ⟨d, hdN⟩, rfl, ?_⟩
  ext q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.one_apply]
  apply l136_mk_eq_of_barMap_eq hp hLM hsn
  set dm : ↥M := ⟨d, hdM⟩ with hdm
  have hq : QuotientGroup.mk' (GLAPPrimeCore p ↥M) (Subgroup.inclusion hLM y) ∈ barX p M L :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 y.2)
  have hy := hc _ hq
  have hinc : Subgroup.inclusion hLM (L.normalizerMonoidHom ⟨d, hdN⟩ y) =
      dm * Subgroup.inclusion hLM y * dm⁻¹ := by
    apply Subtype.ext
    rfl
  have hkey : QuotientGroup.mk' (GLAPPrimeCore p ↥M) (Subgroup.inclusion hLM (L.normalizerMonoidHom ⟨d, hdN⟩ y)) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥M) (Subgroup.inclusion hLM y) := by
    rw [hinc, map_mul, map_mul, map_inv, hy, mul_inv_cancel_right]
  exact Subtype.ext hkey


@[expose] def l136Fam {G : Type} [Group G] [Finite G] (M L : Subgroup G) (A0 : Subgroup ↥M) :
    Set (Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :=
  {Z | ∃ z ∈ A0, Z = GLBConj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) z) (barX 3 M L)}

theorem l136_fam_comp {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : GLAPComponent 3 M L) (A0 : Subgroup ↥M) :
    ∀ X ∈ l136Fam M L A0, IsComponentOf X ⊤ := by
  rintro X ⟨z, -, rfl⟩
  exact l119_conj_component hL z

theorem l136_fam_comm {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : GLAPComponent 3 M L) (A0 : Subgroup ↥M) :
    ∀ X ∈ l136Fam M L A0, ∀ X' ∈ l136Fam M L A0, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x := by
  rintro X ⟨w, -, rfl⟩ X' ⟨w', -, rfl⟩ hne x hx y hy
  exact l119_conj_comm hL hne hx hy

theorem l136_fam_base {G : Type} [Group G] [Finite G] {M L : Subgroup G} (A0 : Subgroup ↥M)
    (hA : (1 : ↥M) ∈ A0) : barX 3 M L ∈ l136Fam M L A0 :=
  ⟨1, hA, by rw [map_one, gLBConj_one]⟩

theorem l136_gLBConj_le {G : Type} [Group G] {M L : Subgroup G} (hLM : L ≤ M) {g : G} (hg : g ∈ M) :
    GLBConj g L ≤ M := by
  intro y hy
  have h1 : g * y * g⁻¹ ∈ L := mem_gLBConj.1 hy
  have h2 := hLM h1
  have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.inv_mem hg) h2) hg

theorem l136_lstar_eq_iSup {G : Type} [Group G] {D L : Subgroup G} :
    Lstarsub D L = ⨆ d : ↥D, GLBConj (d : G) L := by
  apply le_antisymm
  · exact iSup₂_le fun d hd => le_iSup_of_le (⟨d, hd⟩ : ↥D) le_rfl
  · exact iSup_le fun d => le_iSup₂_of_le (d : G) d.2 le_rfl

theorem l136_barX_lstar_eq_sSup {G : Type} [Group G] [Finite G] {M D L : Subgroup G}
    (hDM : D ≤ M) (hLM : L ≤ M) :
    barX 3 M (Lstarsub D L) = sSup (l136Fam M L (D.subgroupOf M)) := by
  apply le_antisymm
  · rw [l136_lstar_eq_iSup]
    refine (barX_iSup_le_iSup (fun d : ↥D => GLBConj (d : G) L) (fun d => l136_gLBConj_le hLM
      (hDM d.2))).trans (iSup_le fun d => ?_)
    rw [l119_barX_gLBConj (hDM d.2) hLM]
    exact le_sSup ⟨⟨(d : G), hDM d.2⟩, Subgroup.mem_subgroupOf.2 d.2, rfl⟩
  · refine sSup_le fun X hX => ?_
    obtain ⟨z, hz, rfl⟩ := hX
    rw [← l119_barX_gLBConj z.2 hLM]
    exact barX_mono_of_le 3 (le_iSup₂_of_le (z : G) (Subgroup.mem_subgroupOf.1 hz) le_rfl)

theorem l136_barMap_eq_of_mk_eq {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {M L : Subgroup G} (hLM : L ≤ M) (hsn : IsSubnormal L M) {x y : ↥L}
    (h : (QuotientGroup.mk x : ↥L ⧸ GLAPPrimeCore p ↥L) = QuotientGroup.mk y) :
    barMap p hLM x = barMap p hLM y := by
  have hmem : x⁻¹ * y ∈ GLAPPrimeCore p ↥L := QuotientGroup.eq.1 h
  rw [← ker_barMap_eq hp hLM hsn, MonoidHom.mem_ker, map_mul, map_inv] at hmem
  exact inv_mul_eq_one.1 hmem

theorem l136_centralizes_barX_of_centBar {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {M L : Subgroup G} (hLM : L ≤ M) (hsn : IsSubnormal L M) {x : G} (hxM : x ∈ M)
    (hx : x ∈ centBar p ⊤ L) :
    ∀ q ∈ barX p M L, QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨x, hxM⟩ : ↥M) * q =
      q * QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨x, hxM⟩ : ↥M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro q hq
  obtain ⟨u, hu, rfl⟩ := (mem_barX_iff p q).1 hq
  obtain ⟨-, γ, hγ, hbar⟩ := Sec13d.mem_centBar_iff.1 hx
  set y : ↥L := ⟨(u : G), hu⟩ with hy
  have hfix : barAut p L γ (QuotientGroup.mk y) = QuotientGroup.mk y := by
    rw [hbar, MulAut.one_apply]
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at hfix
  have hval := congrArg Subtype.val (l136_barMap_eq_of_mk_eq hp hLM hsn hfix)
  have hinc : Subgroup.inclusion hLM (L.normalizerMonoidHom γ y) =
      (⟨x, hxM⟩ : ↥M) * u * (⟨x, hxM⟩ : ↥M)⁻¹ := by
    apply Subtype.ext
    show (γ : G) * (u : G) * (γ : G)⁻¹ = x * (u : G) * x⁻¹
    rw [hγ]
  have hconj : QuotientGroup.mk' (GLAPPrimeCore p ↥M)
      ((⟨x, hxM⟩ : ↥M) * u * (⟨x, hxM⟩ : ↥M)⁻¹) = QuotientGroup.mk' (GLAPPrimeCore p ↥M) u := by
    rw [← hinc]
    exact hval
  rw [map_mul, map_mul, map_inv] at hconj
  exact mul_inv_eq_iff_eq_mul.1 hconj

theorem l136_le_lstar {G : Type} [Group G] {D L : Subgroup G} : L ≤ Lstarsub D L :=
  le_iSup₂_of_le (1 : G) D.one_mem (gLBConj_one L).ge

theorem l136_bar_normalizes {G : Type} [Group G] [Finite G] {p : ℕ} {M H Q : Subgroup G}
    (hHn : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) :
    barX p M H ≤ Subgroup.normalizer ((barX p M Q : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  have key : ∀ u : ↥M, (u : G) ∈ H → ∀ s ∈ barX p M Q,
      QuotientGroup.mk' (GLAPPrimeCore p ↥M) u * s * (QuotientGroup.mk' (GLAPPrimeCore p ↥M) u)⁻¹ ∈
        barX p M Q := by
    intro u hu s hs
    obtain ⟨v, hv, rfl⟩ := (mem_barX_iff p s).1 hs
    have hval : ((u * v * u⁻¹ : ↥M) : G) ∈ Q := by
      simpa using hHn _ hu _ hv
    refine (mem_barX_iff p _).2 ⟨u * v * u⁻¹, hval, ?_⟩
    rw [map_mul, map_mul, map_inv]
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro s
  obtain ⟨u, hu, rfl⟩ := (mem_barX_iff p y).1 hy
  constructor
  · intro hs
    exact key u hu s hs
  · intro hs
    have h2 := key u⁻¹ (by simpa using H.inv_mem hu) _ hs
    have e : (QuotientGroup.mk' (GLAPPrimeCore p ↥M) u⁻¹) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥M) u * s * (QuotientGroup.mk' (GLAPPrimeCore p ↥M) u)⁻¹) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥M) u⁻¹)⁻¹ = s := by
      rw [map_inv]
      group
    rw [e] at h2
    exact h2

@[expose] def IIHardInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    (hN : D ≤ Subgroup.normalizer (L : Set G)) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1),
    pCoreOf 2 (fixSub (barAut 3 L ⟨d, hN hd⟩)) ≠ ⊥ →
      pCoreOf 2 (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤
        GLAPPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))

theorem l136_ii_easy (hO2 : Cex134_O2Statement) (h121c : Prop121_corStatement)
    (hcomp : Sec13_compStatement)
    {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L) (hN : D ≤ Subgroup.normalizer (L : Set G))
    {d : G} (hd : d ∈ D) (hd1 : d ≠ 1)
    (hfix : pCoreOf 2 (fixSub (barAut 3 L ⟨d, hN hd⟩)) = ⊥) :
    pCoreOf 2 (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : GLStanding G m 3 := h.standing
  have hDA : D ≤ A := h.hD.1
  have hdA : d ∈ A := hDA hd
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hLM : L ≤ M := hLc.1
  have hsub : IsSubnormal L M := hLc.2.1
  have hO2L : GLAPPrimeCoreOf 3 L ≤ pCoreOf 2 L := hO2 h rfl
  have hQ2 : IsPGroup 2 ↥(GLAPPrimeCoreOf 3 L) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hO2L
  have hcopQ : ¬ 3 ∣ Nat.card ↥(GLAPPrimeCoreOf 3 L) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ2
    rw [hn]
    intro h3
    have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h2
  have hd3 : d ^ 3 = 1 := h.hD.2.1.2 d hd
  have hQn : ∀ q ∈ GLAPPrimeCoreOf 3 L, d * q * d⁻¹ ∈ GLAPPrimeCoreOf 3 L := fun q hq =>
    conj_mem_glaPPrimeCoreOf 3 (hN hd) hq
  set Y : Subgroup G := L ⊓ Subgroup.centralizer ({d} : Set G) with hY
  set X : Subgroup G := pCoreOf 2 Y with hX
  have hX2 : IsPGroup 2 ↥X := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hXY : X ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hXL : X ≤ L := hXY.trans inf_le_left
  have hXC : X ≤ Subgroup.centralizer ({d} : Set G) := hXY.trans inf_le_right
  have hYN : Y ≤ Subgroup.normalizer (X : Set G) := le_normalizer_pCoreOf 2 Y
  set σ := barAut 3 L ⟨d, hN hd⟩ with hσ
  have hbm : ∀ x : ↥L, σ (QuotientGroup.mk x) =
      QuotientGroup.mk (L.normalizerMonoidHom ⟨d, hN hd⟩ x) :=
    fun x => CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk 3 L ⟨d, hN hd⟩ x
  have ha : ∀ y : ↥L, (y : G) ∈ X → σ (QuotientGroup.mk y) = QuotientGroup.mk y := by
    intro y hy
    have hcm : d * (y : G) = (y : G) * d :=
      Subgroup.mem_centralizer_iff.1 (hXC hy) d (Set.mem_singleton d)
    rw [hbm]
    congr 1
    apply Subtype.ext
    show d * (y : G) * d⁻¹ = (y : G)
    rw [hcm, mul_assoc, mul_inv_cancel, mul_one]
  have hb : ∀ f ∈ fixSub σ, ∃ y : ↥L, (y : G) ∈ Y ∧
      (QuotientGroup.mk y : ↥L ⧸ GLAPPrimeCore 3 ↥L) = f := by
    intro f hf
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective f
    have hfz : (QuotientGroup.mk (L.normalizerMonoidHom ⟨d, hN hd⟩ z) : ↥L ⧸ GLAPPrimeCore 3 ↥L) =
        QuotientGroup.mk z := by
      rw [← hbm]
      exact mem_fixSub.1 hf
    have hzmem : (z : ↥L)⁻¹ * L.normalizerMonoidHom ⟨d, hN hd⟩ z ∈ GLAPPrimeCore 3 ↥L :=
      QuotientGroup.eq.1 hfz.symm
    have hx : (z : G)⁻¹ * (d * (z : G) * d⁻¹) ∈ GLAPPrimeCoreOf 3 L :=
      (mem_gLAPPrimeCoreOf_iff 3 L _).2 ⟨((z : ↥L)⁻¹ * L.normalizerMonoidHom ⟨d, hN hd⟩ z).2, hzmem⟩
    obtain ⟨q, hqQ, hfixq⟩ :=
      exists_fixed_mem_coset d hd3 (GLAPPrimeCoreOf 3 L) hcopQ hQn (z : G) hx
    obtain ⟨hqL, hqcore⟩ := (mem_gLAPPrimeCoreOf_iff 3 L q).1 hqQ
    have hmk1 : (QuotientGroup.mk (⟨q, hqL⟩ : ↥L) : ↥L ⧸ GLAPPrimeCore 3 ↥L) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hqcore
    have hwL : (z : G) * q ∈ L := Subgroup.mul_mem _ z.2 hqL
    refine ⟨⟨(z : G) * q, hwL⟩, ⟨hwL, ?_⟩, ?_⟩
    · show (z : G) * q ∈ Subgroup.centralizer ({d} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact mul_inv_eq_iff_eq_mul.1 hfixq
    · have hy_eq : (⟨(z : G) * q, hwL⟩ : ↥L) = z * ⟨q, hqL⟩ := Subtype.ext rfl
      rw [hy_eq, QuotientGroup.mk_mul, hmk1, mul_one]
  set X' : Subgroup (↥L ⧸ GLAPPrimeCore 3 ↥L) :=
    (X.subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) with hX'
  have hX'mem : ∀ k ∈ X', ∃ y : ↥L, (y : G) ∈ X ∧
      (QuotientGroup.mk y : ↥L ⧸ GLAPPrimeCore 3 ↥L) = k := by
    intro k hk
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hk
    exact ⟨y, Subgroup.mem_subgroupOf.1 hy, rfl⟩
  have hX'sub : X' ≤ fixSub σ := by
    intro k hk
    obtain ⟨y, hy, rfl⟩ := hX'mem k hk
    exact mem_fixSub.2 (ha y hy)
  have hX'conj : ∀ y : ↥L, (y : G) ∈ Y → ∀ k ∈ X',
      (QuotientGroup.mk y : ↥L ⧸ GLAPPrimeCore 3 ↥L) * k * (QuotientGroup.mk y)⁻¹ ∈ X' := by
    intro y hy k hk
    obtain ⟨x, hx, rfl⟩ := hX'mem k hk
    refine Subgroup.mem_map.2 ⟨y * x * y⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.1 (hYN hy) (x : G)).1 hx
    · simp [map_mul, map_inv]
  have hX'nor : fixSub σ ≤ Subgroup.normalizer (X' : Set (↥L ⧸ GLAPPrimeCore 3 ↥L)) := by
    intro f hf
    obtain ⟨y, hy, rfl⟩ := hb f hf
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hX'conj y hy k hk
    · intro hk
      have h2 := hX'conj y⁻¹ (Y.inv_mem hy) _ hk
      have hinv : (QuotientGroup.mk (y⁻¹ : ↥L) : ↥L ⧸ GLAPPrimeCore 3 ↥L) =
          (QuotientGroup.mk y)⁻¹ := by
        simp
      rw [hinv] at h2
      have e : (QuotientGroup.mk y)⁻¹ * (QuotientGroup.mk y * k * (QuotientGroup.mk y)⁻¹) *
          ((QuotientGroup.mk y)⁻¹)⁻¹ = k := by group
      rwa [e] at h2
  have hX'2 : IsPGroup 2 ↥X' := by
    have hXsub : IsPGroup 2 ↥(X.subgroupOf L) :=
      hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hXL).symm
    exact hXsub.map _
  have hX'0 : X' ≤ pCoreOf 2 (fixSub σ) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hX'sub hX'nor hX'2
  have hX'1 : X' ≤ ⊥ := hfix ▸ hX'0
  have hXO : X ≤ GLAPPrimeCoreOf 3 L := by
    intro x hx
    have hxL : x ∈ L := hXL hx
    have hk : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : ↥L ⧸ GLAPPrimeCore 3 ↥L) ∈ X' :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
    have h1 := hX'1 hk
    rw [Subgroup.mem_bot] at h1
    exact (mem_gLAPPrimeCoreOf_iff 3 L x).2 ⟨hxL, (QuotientGroup.eq_one_iff _).1 h1⟩
  have hX_M : X ≤ pCoreOf 2 M := hXO.trans (hO2L.trans (pCoreOf_le_of_isSubnormal 2 hsub))
  have hX_Cd : X ≤ pCoreOf 2 M ⊓ Subgroup.centralizer ({d} : Set G) := le_inf hX_M hXC
  exact (hX_Cd.trans (h121c h.toSec11 hdA hd1)).trans
    (pCoreOf_two_le_glaPPrimeCoreOf Nat.prime_three (by norm_num) _)

end Lemma136

open Lemma136 in
theorem lemma136_i_of_inputs (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (hI22 : Input22_3_2)
    (hP1 : P1BarInput) :
    ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T L : Subgroup G}
      (h : Cex134 G m p B M E A D T L),
      D ≤ Subgroup.normalizer (L : Set G) ∧ ∀ x ∈ D, x ∈ centBar 3 ⊤ L → x = 1 := by
  intro G _ _ m p B M E A D T L h
  have hγ := l136_gamma hP95 h111 h121 hcomp h
  unfold Prop95Gamma at hγ
  obtain ⟨hp3, e, -⟩ := hγ
  subst hp3
  have hS : GLStanding G m 3 := h.standing
  have hp : Nat.Prime 3 := hS.prime
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hDA : D ≤ A := h.hD.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDM : D ≤ M := hDA.trans hAM
  obtain ⟨hLc, hnc⟩ := hcomp h.toSec13 h.hL
  have hLM : L ≤ M := hLc.1
  have hsub : IsSubnormal L M := hLc.2.1
  have hDel : IsElemAbelian 3 D := h.hD.2.1
  have hDcard : Nat.card D = 3 ^ 2 := h.hD.2.2
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hLcard : 3 ∣ Nat.card (barX 3 M L) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]
  set A0 : Subgroup ↥M := D.subgroupOf M with hA0
  have hYeq : barX 3 M (Lstarsub D L) = sSup (l136Fam M L A0) := l136_barX_lstar_eq_sSup hDM hLM
  have hYcomp : ∀ X ∈ l136Fam M L A0, IsComponentOf X (barX 3 M (Lstarsub D L)) := by
    rw [hYeq]
    exact fun X hX => l119_isComponentOf_sSup (l136_fam_comp hLc A0) (l136_fam_comm hLc A0) hX
  have hcomm : ∀ X ∈ l136Fam M L A0, ∀ X' ∈ l136Fam M L A0, X ≠ X' →
      ∀ x ∈ X, ∀ y ∈ X', x * y = y * x := l136_fam_comm hLc A0
  have htrans : ∀ X ∈ l136Fam M L A0, ∀ X' ∈ l136Fam M L A0, ∃ b ∈ barX 3 M D,
      GLBConj b X = X' := by
    rintro X ⟨w, hw, rfl⟩ X' ⟨w', hw', rfl⟩
    exact ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (w⁻¹ * w'),
      Subgroup.mem_map_of_mem _ (A0.mul_mem (A0.inv_mem hw) hw'), l119_conj_trans w w'⟩
  have hL1 : barX 3 M L ∈ l136Fam M L A0 := l136_fam_base A0 A0.one_mem
  have hBel : IsElemAbelian 3 (barX 3 M D) :=
    CFSG.SectionRank.isElemAbelian_map (l119_isElemAbelian_subgroupOf hDel M) _
  have hBnorm : barX 3 M D ≤ Subgroup.normalizer
      ((barX 3 M (Lstarsub D L) : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) :=
    (Lemma135.barX_lstar_normalizers Lemma135.le_normalizer_lstar
      Lemma135.le_normalizer_lstar).2
  have hcardB : Nat.card (barX 3 M D) = 3 ^ 2 := by
    have hDp : IsPGroup 3 ↥D := IsPGroup.iff_card.2 ⟨2, hDcard⟩
    rw [Lemma135.card_barX_of_isPGroup hDM hDp, hDcard]
  have hrank : 2 ≤ CFSG.Open.pRank 3 (barX 3 M D) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hBel hcardB
  have hpY : 3 ∣ Nat.card (barX 3 M (Lstarsub D L)) :=
    dvd_trans hLcard (Subgroup.card_dvd_of_le (barX_mono_of_le 3 l136_le_lstar))
  have key : ∀ x ∈ D, x ≠ 1 → (¬ x ∈ Subgroup.normalizer (L : Set G) ∨ x ∈ centBar 3 ⊤ L) →
      False := by
    intro x hxD hx1 hxJ
    have hxM : x ∈ M := hDM hxD
    have hb0mem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨x, hxM⟩ : ↥M) ∈ barX 3 M D :=
      (mem_barX_iff 3 _).2 ⟨⟨x, hxM⟩, hxD, rfl⟩
    have hb0ne : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨x, hxM⟩ : ↥M) ≠ 1 := by
      intro h1
      apply hx1
      have hpow : (⟨x, hxM⟩ : ↥M) ^ 3 = 1 := by
        apply Subtype.ext
        simp [hDel.2 x hxD]
      have h2 : (⟨x, hxM⟩ : ↥M) = 1 :=
        l119_eq_one_of_pow_of_mem_core hp hpow ((QuotientGroup.eq_one_iff _).1 h1)
      exact congrArg Subtype.val h2
    have hnon : ∃ b ∈ barX 3 M D, b ≠ 1 ∧
        (b ∈ Subgroup.centralizer ((barX 3 M (Lstarsub D L) : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) ∨
          b ∉ Subgroup.normalizer ((barX 3 M L : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
            Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) := by
      refine ⟨_, hb0mem, hb0ne, ?_⟩
      rcases hxJ with hxN | hxc
      · right
        intro hb
        exact hxN (l136_mem_normalizer_of_bar hLc ⟨x, hxM⟩ hb)
      · left
        have hcent : ∀ X ∈ l136Fam M L A0, ∀ w ∈ X,
            QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨x, hxM⟩ : ↥M) * w =
              w * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨x, hxM⟩ : ↥M) := by
          rintro X ⟨z, hz, rfl⟩ w hw
          refine l119_centralizes_gLBConj ?_ ?_ w hw
          · rw [← map_mul, ← map_mul]
            congr 1
            apply Subtype.ext
            exact hDcomm x hxD z (Subgroup.mem_subgroupOf.1 hz)
          · exact l136_centralizes_barX_of_centBar hp hLM hsub hxM hxc
        have hC : sSup (l136Fam M L A0) ≤
            Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨x, hxM⟩ : ↥M)} :
              Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
          refine sSup_le fun X hX w hw => ?_
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          rw [hh]
          exact hcent X hX w hw
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [hYeq] at hw
        exact ((Subgroup.mem_centralizer_iff.1 (hC hw)) _ (Set.mem_singleton _)).symm
    have hI := hI22 (↥M ⧸ GLAPPrimeCore 3 ↥M) 3 Nat.prime_three (barX 3 M D)
      (barX 3 M (Lstarsub D L)) (barX 3 M L) (l136Fam M L A0) hBel hBnorm hL1 hrank hpY hYeq
      hYcomp hcomm htrans hnon
    have hle : barX 3 M (Lstarsub D L) ≤ barX 3 M (piStar 3 D) := by
      rw [hI]
      refine sSup_le ?_
      rintro Z ⟨b, hb, hb1, hJb, rfl⟩
      obtain ⟨d, hdD, rfl⟩ := (mem_barX_iff 3 b).1 hb
      unfold GLAPLayer
      refine sSup_le fun K hK => ?_
      have hd1 : (d : G) ≠ 1 := by
        intro h1
        apply hb1
        have hd : d = 1 := Subtype.ext h1
        rw [hd, map_one]
      have hJc : ¬ (d : G) ∈ Subgroup.normalizer (L : Set G) ∨ (d : G) ∈ centBar 3 ⊤ L := by
        rcases hJb with hC | hN
        · by_cases hdN : (d : G) ∈ Subgroup.normalizer (L : Set G)
          · right
            refine l136_centBar_of_centralizes hp hsub d.2 hdN ?_
            intro q hq
            have hqL : q ∈ barX 3 M (Lstarsub D L) := barX_mono_of_le 3 l136_le_lstar hq
            exact (Subgroup.mem_centralizer_iff.1 hC q hqL).symm
          · left
            exact hdN
        · left
          intro hdN
          exact hN (l136_mk_mem_normalizer_barX hLM d.2 hdN)
      exact hP1 G m h d hdD hd1 hJc K hK
    set Q : Subgroup G := pCoreOf 2 (piStar 3 D) with hQdef
    have hQ2 : IsPGroup 2 ↥(barX 3 M Q) :=
      isPGroup_barX (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (piStar 3 D))
    have hQn : ∀ h ∈ piStar 3 D, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := fun h hh q hq =>
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (piStar 3 D) hh) q).1 hq
    have hnormS : barX 3 M (piStar 3 D) ≤ Subgroup.normalizer
        ((barX 3 M Q : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) :=
      l136_bar_normalizes hQn
    have hcentQ : ∀ X ∈ l136Fam M L A0, ∀ s ∈ barX 3 M Q, ∀ x ∈ X, s * x = x * s := by
      intro X hX s hs x hx
      have hXL : X ≤ barX 3 M (Lstarsub D L) := by
        rw [hYeq]
        exact le_sSup hX
      have hXN : X ≤ Subgroup.normalizer ((barX 3 M Q : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := hXL.trans (hle.trans hnormS)
      have hcom0 := commutator_eq_bot_of_normalizes (l136_fam_comp hLc A0 X hX) hQ2 hXN
      have hmem := Subgroup.commutator_mem_commutator hx hs
      rw [hcom0, Subgroup.mem_bot] at hmem
      exact (commutatorElement_eq_one_iff_mul_comm.1 hmem).symm
    have hQC : barX 3 M Q ≤ Subgroup.centralizer
        ((barX 3 M (Lstarsub D L) : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hYeq] at hy
      have hC : sSup (l136Fam M L A0) ≤ Subgroup.centralizer ({s} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
        refine sSup_le fun X hX x hx => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hcentQ X hX s hs x hx
      exact ((Subgroup.mem_centralizer_iff.1 (hC hy)) s (Set.mem_singleton _)).symm
    apply hnc
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hgQ : g ∈ barX 3 M Q :=
      barX_mono_of_le 3 (show gammaStar 3 D ≤ pCoreOf 2 (piStar 3 D) from inf_le_right) hg
    have hqL : q ∈ barX 3 M (Lstarsub D L) := barX_mono_of_le 3 l136_le_lstar hq
    exact Subgroup.mem_centralizer_iff.1 (hQC hgQ) q hqL
  refine ⟨fun x hxD => ?_, fun x hxD hxc => ?_⟩
  · by_contra hxN
    exact key x hxD (fun h1 => hxN (by rw [h1]; exact Subgroup.one_mem _)) (Or.inl hxN)
  · by_contra hx1
    exact key x hxD hx1 (Or.inr hxc)



open Lemma136 in
theorem lemma136_ii_of_inputs (hO2 : Cex134_O2Statement) (h121c : Prop121_corStatement)
    (hcomp : Sec13_compStatement) (hII : IIHardInput)
    {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L) (hN : D ≤ Subgroup.normalizer (L : Set G)) :
    ∀ d ∈ D, d ≠ 1 →
      pCoreOf 2 (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤
        GLAPPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) := by
  intro d hd hd1
  by_cases hf : pCoreOf 2 (fixSub (barAut 3 L ⟨d, hN hd⟩)) = ⊥
  · exact l136_ii_easy hO2 h121c hcomp h hN hd hd1 hf
  · exact hII G m h hN hd hd1 hf

open Lemma136 in
theorem lemma136_of_inputs (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (hI22 : Input22_3_2)
    (hP1 : P1BarInput) (hO2 : Cex134_O2Statement) (h121c : Prop121_corStatement)
    (hII : IIHardInput) : Lemma136Statement := by
  intro G _ _ m p B M E A D T L h
  have hi := lemma136_i_of_inputs hP95 h111 h121 hcomp hI22 hP1 h
  have hp3 : p = 3 := Lemma135.cex134_p_eq_three hP95 h111 h121 hcomp h
  subst hp3
  exact ⟨hi, lemma136_ii_of_inputs hO2 h121c hcomp hII h hi.1⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
