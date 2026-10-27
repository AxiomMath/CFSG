module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop126b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6HJNormalA
public import CFSG.GH74.Generic.GKFCover
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1245
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims122
public import CFSG.LocalAnalysis.GLTheoremA.CatA.LStar

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1245b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open scoped commutatorElement

section Generic

variable {G : Type} [Group G] [Finite G]

theorem centralizer_zpowers_eq (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h _ (Subgroup.mem_zpowers _)
  · intro h y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h1 : x * g = g * x := h x (Set.mem_singleton x)
    exact Commute.zpow_left h1 k

theorem centralizer_eq_of_mem_zpowers {x d : G} (hx : x ^ 3 = 1) (hd : d ∈ Subgroup.zpowers x)
    (hd1 : d ≠ 1) : Subgroup.centralizer ({d} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hd1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hd
    rw [← hk, one_zpow]
  have hox : orderOf x = 3 := orderOf_eq_prime hx hx1
  have hle : Subgroup.zpowers d ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hd
  have hd3 : d ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hod : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have heq : Subgroup.zpowers d = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hox, hod])
  rw [← centralizer_zpowers_eq, heq, centralizer_zpowers_eq]

theorem layer_le_of_le_sup {Y N O : Subgroup G} (hO : Nat.Coprime 3 (Nat.card O))
    (hON : O ≤ Subgroup.normalizer (N : Set G)) (h : GLAPLayer 3 Y ≤ N ⊔ O) :
    GLAPLayer 3 Y ≤ N :=
  sSup_le fun _ hL => CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_le_sup Nat.prime_three hL
    hO hON ((le_sSup hL).trans h)

theorem kx_le_of_le_sup {H N O : Subgroup G} {x : G} (hO : Nat.Coprime 3 (Nat.card O))
    (hON : O ≤ Subgroup.normalizer (N : Set G)) (h : Kx 3 (GLAPLayer 3 H) x ≤ N ⊔ O) :
    Kx 3 (GLAPLayer 3 H) x ≤ N := by
  unfold Kx at h ⊢
  refine iSup₂_le fun g hg => ?_
  have hle : GLBConj g (GLAPLayer 3 H) ≤ N ⊔ O :=
    (le_iSup₂_of_le (f := fun g (_ : g ∈ GLAPLayer 3 (Cg x)) => GLBConj g (GLAPLayer 3 H)) g hg
      le_rfl).trans h
  rw [← Prop1310a5b.glaPLayer_gLBConj'] at hle ⊢
  exact layer_le_of_le_sup hO hON hle

theorem layer_perfect (Y : Subgroup G) : ⁅GLAPLayer 3 Y, GLAPLayer 3 Y⁆ = GLAPLayer 3 Y := by
  refine le_antisymm (Subgroup.commutator_le.2 fun u hu v hv => ?_) ?_
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hv) (Subgroup.inv_mem _ hu))
      (Subgroup.inv_mem _ hv)
  refine sSup_le fun L hL => ?_
  have hLe : L ≤ GLAPLayer 3 Y := le_sSup hL
  calc L = ⁅L, L⁆ := (glaPComponent_perfect hL).symm
    _ ≤ ⁅GLAPLayer 3 Y, GLAPLayer 3 Y⁆ := Subgroup.commutator_mono hLe hLe

theorem glaPComponent_of_normal {H N : Subgroup G} (hNH : N ≤ H) (hn : (N.subgroupOf H).Normal)
    (hP : ∀ N₀ O : Subgroup G, O ≤ Subgroup.normalizer (N₀ : Set G) → Nat.Coprime 3 (Nat.card O) →
      N ≤ N₀ ⊔ O → N ≤ N₀)
    (hq : CFSG.Open.IsQuasisimple (↥N ⧸ GLAPPrimeCore 3 ↥N)) : GLAPComponent 3 H N := by
  have hNsn : IsSubnormal N H := IsSubnormal.step hNH hn (IsSubnormal.refl H)
  refine ⟨hNH, hNsn, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := H) 3 hNsn
    rwa [barX_self] at this
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivBarX Nat.prime_three hNH hNsn) hq
  · intro J' hlt hJ'sn heq
    have hJ'N : IsSubnormal J' N := isSubnormal_of_le_of_le hJ'sn hlt.le hNH
    obtain ⟨M', hJ'M', hM'N, hM'ne, hM'n, -⟩ := isSubnormal_exists_normal hJ'N hlt.ne
    apply hM'ne
    refine le_antisymm hM'N (hP M' (GLAPPrimeCoreOf 3 N) ?_ ?_ ?_)
    · exact ((Subgroup.map_subtype_le _ : GLAPPrimeCoreOf 3 N ≤ N)).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hM'N).1 hM'n)
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
        (not_dvd_card_glaPPrimeCoreOf Nat.prime_three N)
    · intro n hn'
      obtain ⟨j, hj, hjn⟩ := exists_of_barX_le (X := H) (J := J') (K := N) (p := 3)
        (le_of_eq heq.symm) hn' (hNH hn')
      have hmem : j⁻¹ * n ∈ N ⊓ GLAPPrimeCoreOf 3 H :=
        ⟨N.mul_mem (N.inv_mem (hlt.le hj)) hn', hjn⟩
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hNsn] at hmem
      have e : n = j * (j⁻¹ * n) := by group
      rw [e]
      exact Subgroup.mul_mem_sup (hJ'M' hj) hmem

theorem isQuasisimple_of_isLThreeFour {X : Type} [Group X] (h : IsLThreeFour X) :
    CFSG.Open.IsQuasisimple X := by
  obtain ⟨hs, hna⟩ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isLThreeFour h
  exact CFSG.HardMathSupport.Solomon.Coordinator.c25_isQuasisimple_of_simple hs hna

theorem three_dvd_card_of_isLThreeFour {J : Subgroup G} (h : IsLThreeFour (barOf 3 J)) :
    3 ∣ Nat.card J := by
  have h1 := CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour h
  have h2 : 3 ∣ Nat.card (barOf 3 J) := by rw [h1]; norm_num
  exact h2.trans (Subgroup.card_quotient_dvd_card _)

theorem gLBConj_iSup_layer {X K' : Subgroup G} {y : G} (hyX : y ∈ X)
    (hyK : y ∈ Subgroup.normalizer (K' : Set G)) :
    GLBConj y (⨆ g ∈ GLAPLayer 3 X, GLBConj g K') = ⨆ g ∈ GLAPLayer 3 X, GLBConj g K' := by
  have key : ∀ y : G, y ∈ X → y ∈ Subgroup.normalizer (K' : Set G) →
      (⨆ g ∈ GLAPLayer 3 X, GLBConj g K') ≤ GLBConj y (⨆ g ∈ GLAPLayer 3 X, GLBConj g K') := by
    intro y hyX hyK
    refine iSup₂_le fun g hg => ?_
    have hg' : y * g * y⁻¹ ∈ GLAPLayer 3 X :=
      (Subgroup.mem_normalizer_iff.1
        (Lemma1245.mem_normalizer_glaPLayer' (p := 3) (Subgroup.le_normalizer hyX)) g).1 hg
    have h1 : GLBConj g K' = GLBConj y (GLBConj (y * g * y⁻¹) K') := by
      rw [gLBConj_gLBConj, show y * g * y⁻¹ * y = y * g by group, ← gLBConj_gLBConj,
        gLBConj_eq_of_mem_normalizer hyK]
    rw [h1]
    exact gLBConj_mono y (le_iSup₂_of_le (f := fun g (_ : g ∈ GLAPLayer 3 X) => GLBConj g K')
      (y * g * y⁻¹) hg' le_rfl)
  refine le_antisymm ?_ (key y hyX hyK)
  have h2 := gLBConj_mono y (key y⁻¹ (X.inv_mem hyX) (Subgroup.inv_mem _ hyK))
  rwa [gLBConj_gLBConj_inv] at h2

theorem glaPComponent_conj {X L : Subgroup G} (hL : GLAPComponent 3 X L) {y : G} (hy : y ∈ X) :
    GLAPComponent 3 X (GLBConj y L) := by
  have h := glaPComponent_gLBConj hL y
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hy)] at h

end Generic

section Single

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

theorem exists_family (h1834 : Input18_3_4) {X K' : Subgroup G} (hXK : CFSG.Open.IsKGroup ↥X) {x : G} (hxX : x ∈ X)
    (hx3 : x ^ 3 = 1)
    (hK' : GLAPComponent 3 (X ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) K') :
    ∃ 𝒞 : Set (Subgroup G), (∀ L ∈ 𝒞, GLAPComponent 3 X L) ∧ K' ≤ ⨆ L ∈ 𝒞, L ∧
      (⨆ L ∈ 𝒞, L) = ⨆ g ∈ GLAPLayer 3 X, GLBConj g K' ∧
      ∀ L ∈ 𝒞, ∀ L' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers x, GLBConj e L = L' := by
  have hel : IsElemAbelian 3 (Subgroup.zpowers x) := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 u.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 v.2
      apply Subtype.ext
      show (u : G) * v = v * u
      rw [← hi, ← hj]
      exact (Commute.zpow_zpow_self x i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  obtain ⟨𝒞, hcomp, heq, -, htr⟩ :=
    h1834 G X hXK 3 Nat.prime_three (Subgroup.zpowers x) (Subgroup.zpowers_le.2 hxX) hel K' hK'
  refine ⟨𝒞, hcomp, ?_, heq, htr⟩
  rw [heq]
  have h1 : (1 : G) ∈ GLAPLayer 3 X := Subgroup.one_mem _
  exact le_iSup₂_of_le (f := fun g (_ : g ∈ GLAPLayer 3 X) => GLBConj g K') 1 h1
    (le_of_eq (gLBConj_one K').symm)

theorem exists_single_component (h1834 : Input18_3_4) {X F J : Subgroup G} (hXK : CFSG.Open.IsKGroup ↥X)
    (hFX : F ≤ X) (hFel : IsElemAbelian 3 F) (hF9 : Nat.card F = 9)
    (hJX : J ≤ X) (hJperf : ⁅J, J⁆ = J) (hJ3 : 3 ∣ Nat.card J)
    (hJF : J ≤ Subgroup.centralizer (F : Set G)) (K' : G → Subgroup G)
    (hKcomp : ∀ x ∈ F, x ≠ 1 →
      GLAPComponent 3 (X ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) (K' x))
    (hJK : ∀ x ∈ F, x ≠ 1 → J ≤ K' x)
    (hFK : ∀ x ∈ F, x ≠ 1 → F ≤ Subgroup.normalizer (K' x : Set G)) :
    ∃ L : Subgroup G, GLAPComponent 3 X L ∧ J ≤ L ∧ F ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ x ∈ F, x ≠ 1 → K' x ≤ L := by
  have hFcomm : ∀ u ∈ F, ∀ v ∈ F, u * v = v * u := fun u hu v hv =>
    CFSG.Open.IsElemAbelian.comm hFel hu hv
  have hFpow : ∀ u ∈ F, u ^ 3 = 1 := hFel.2
  have hfam : ∀ x ∈ F, x ≠ 1 → ∃ 𝒞 : Set (Subgroup G), (∀ L ∈ 𝒞, GLAPComponent 3 X L) ∧
      K' x ≤ ⨆ L ∈ 𝒞, L ∧ (∀ y ∈ F, ∀ L ∈ 𝒞, GLBConj y L ∈ 𝒞) ∧
      ∀ L ∈ 𝒞, ∀ L' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers x, GLBConj e L = L' := by
    intro x hx hx1
    obtain ⟨𝒞, hcomp, hK𝒞, heq, htr⟩ :=
      exists_family h1834 hXK (hFX hx) (hFpow x hx) (hKcomp x hx hx1)
    refine ⟨𝒞, hcomp, hK𝒞, fun y hy L hL => ?_, htr⟩
    have hyL : GLAPComponent 3 X (GLBConj y L) := glaPComponent_conj (hcomp L hL) (hFX hy)
    have hle : GLBConj y L ≤ ⨆ L ∈ 𝒞, L := by
      rw [heq, ← gLBConj_iSup_layer (hFX hy) (hFK x hx hx1 hy), ← heq]
      exact gLBConj_mono y (le_iSup₂_of_le (f := fun L (_ : L ∈ 𝒞) => L) L hL le_rfl)
    obtain ⟨L', hL', hLeq⟩ := Prop126b.exists_glaPComponent_eq_of_family hyL hcomp le_rfl hle
      (glaPComponent_perfect hyL)
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.three_dvd_card_of_glaPComponent hyL)
    rw [hLeq]
    exact hL'
  have hfinish : ∀ L : Subgroup G, GLAPComponent 3 X L → J ≤ L →
      ∃ L : Subgroup G, GLAPComponent 3 X L ∧ J ≤ L ∧ F ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ x ∈ F, x ≠ 1 → K' x ≤ L := by
    intro L hL hJL
    have hFN : F ≤ Subgroup.normalizer (L : Set G) := by
      intro f hf
      rw [mem_normalizer_iff_gLBConj_eq]
      have hfL := glaPComponent_conj hL (hFX hf)
      have hJf : J ≤ GLBConj f L := by
        have h1 : GLBConj f J = J := gLBConj_eq_of_mem_normalizer
          (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun j hj =>
            ((Subgroup.mem_centralizer_iff.1 (hJF hj)) f hf).symm))
        rw [← h1]
        exact gLBConj_mono f hJL
      exact Prop126b.glaPComponent_eq_of_common hfL hL hJf hJL hJperf hJ3
    refine ⟨L, hL, hJL, hFN, fun x hx hx1 => ?_⟩
    obtain ⟨𝒞, hcomp, hK𝒞, -, htr⟩ := hfam x hx hx1
    obtain ⟨L₀, hL₀, hLL₀⟩ := Prop126b.exists_glaPComponent_eq_of_family hL hcomp hJL
      ((hJK x hx hx1).trans hK𝒞) hJperf hJ3
    refine hK𝒞.trans (iSup₂_le fun L' hL' => ?_)
    obtain ⟨e, he, rfl⟩ := htr L₀ hL₀ L' hL'
    have heF : e ∈ F := Subgroup.zpowers_le.2 hx he
    rw [← hLL₀, gLBConj_eq_of_mem_normalizer (hFN heF)]
  have hFne : F ≠ ⊥ := by
    intro hF
    rw [hF, Subgroup.card_bot] at hF9
    omega
  obtain ⟨⟨x₀, hx₀F⟩, hx₀ne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hFne
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀ne (Subtype.ext h)
  have hord : orderOf x₀ = 3 := orderOf_eq_prime (hFpow x₀ hx₀F) hx₀1
  obtain ⟨y, hyF, hyx₀⟩ : ∃ y ∈ F, y ∉ Subgroup.zpowers x₀ := by
    by_contra hcon
    push Not at hcon
    have hle : Nat.card F ≤ Nat.card (Subgroup.zpowers x₀) := Subgroup.card_le_of_le hcon
    rw [Nat.card_zpowers, hord, hF9] at hle
    omega
  obtain ⟨𝒞₀, hcomp₀, hK𝒞₀, hstab₀, htr₀⟩ := hfam x₀ hx₀F hx₀1
  have h𝒞₀ne : 𝒞₀.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hJbot : J ≤ ⊥ := by
      have := (hJK x₀ hx₀F hx₀1).trans hK𝒞₀
      simpa [hcon] using this
    have h1 : Nat.card J = 1 := by
      rw [le_bot_iff.1 hJbot, Subgroup.card_bot]
    rw [h1] at hJ3
    omega
  obtain ⟨L, hL⟩ := h𝒞₀ne
  obtain ⟨e, he, heL⟩ := htr₀ L hL (GLBConj y L) (hstab₀ y hyF L hL)
  have heF : e ∈ F := Subgroup.zpowers_le.2 hx₀F he
  set z : G := y * e⁻¹ with hz
  have hzF : z ∈ F := F.mul_mem hyF (F.inv_mem heF)
  have hz1 : z ≠ 1 := by
    intro h1
    apply hyx₀
    have : y = e := by
      have h2 : y * e⁻¹ * e = e := by rw [show y * e⁻¹ = z from rfl, h1, one_mul]
      simpa using h2
    rw [this]
    exact he
  have hzL : GLBConj z L = L := by
    have h1 : GLBConj e⁻¹ (GLBConj e L) = L := gLBConj_inv_gLBConj e L
    rw [heL, gLBConj_gLBConj] at h1
    exact h1
  have hzfix : ∀ L' ∈ 𝒞₀, GLBConj z L' = L' := by
    intro L' hL'
    obtain ⟨e', he', rfl⟩ := htr₀ L hL L' hL'
    have he'F : e' ∈ F := Subgroup.zpowers_le.2 hx₀F he'
    rw [gLBConj_gLBConj, ← hFcomm z hzF e' he'F, ← gLBConj_gLBConj, hzL]
  obtain ⟨𝒞z, hcompz, hK𝒞z, -, htrz⟩ := hfam z hzF hz1
  obtain ⟨L₁, hL₁z, hL₁₀⟩ : ∃ L₁ ∈ 𝒞z, L₁ ∈ 𝒞₀ := by
    by_contra hcon
    push Not at hcon
    have hJ₀ : J ≤ ⨆ L ∈ 𝒞₀, L := (hJK x₀ hx₀F hx₀1).trans hK𝒞₀
    have hJz : J ≤ ⨆ L ∈ 𝒞z, L := (hJK z hzF hz1).trans hK𝒞z
    refine Prop126b.false_of_barX_comm hJX hJ₀ hJperf hJ3 fun u hu v hv => ?_
    have hu' := Prop126b.barX_biSup_le 3 (fun L hL => (hcomp₀ L hL).1) hu
    have hv' := Prop126b.barX_biSup_le 3 (fun L hL => (hcompz L hL).1) (barX_mono hJz hv)
    have hC : (⨆ L ∈ 𝒞z, barX 3 X L) ≤ Subgroup.centralizer
        (((⨆ L ∈ 𝒞₀, barX 3 X L : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X))) :
          Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
      refine iSup₂_le fun L₂ hL₂ => ?_
      rw [Subgroup.le_centralizer_iff]
      refine iSup₂_le fun L₃ hL₃ => ?_
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro w' hw'
      have hne : L₂ ≠ L₃ := fun h => hcon L₂ hL₂ (h ▸ hL₃)
      have hbar : barX 3 X L₂ ≠ barX 3 X L₃ := fun h =>
        hne (glaPComponent_unique (hcompz L₂ hL₂) (hcomp₀ L₃ hL₃) h)
      exact Prop95Parts.Input18.comp_comm (hcompz L₂ hL₂).2.2.1 (hcomp₀ L₃ hL₃).2.2.1 hbar hw' hw
    exact (Subgroup.mem_centralizer_iff.1 (hC hv')) u hu'
  have hzL₁ : z ∈ Subgroup.normalizer (L₁ : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq]
    exact hzfix L₁ hL₁₀
  have hJL₁ : J ≤ L₁ := by
    refine (hJK z hzF hz1).trans (hK𝒞z.trans (iSup₂_le fun L' hL' => ?_))
    obtain ⟨e', he', rfl⟩ := htrz L₁ hL₁z L' hL'
    rw [gLBConj_eq_of_mem_normalizer (Subgroup.zpowers_le.2 hzL₁ he')]
  exact hfinish L₁ (hcompz L₁ hL₁z) hJL₁

end Single

section TypeStep

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input25_2)

theorem le_normalizer_sup {Y : Type*} [Group Y] {H A B : Subgroup Y}
    (hA : H ≤ Subgroup.normalizer (A : Set Y)) (hB : H ≤ Subgroup.normalizer (B : Set Y)) :
    H ≤ Subgroup.normalizer ((A ⊔ B : Subgroup Y) : Set Y) := by
  intro h hh
  rw [mem_normalizer_iff_gLBConj_eq]
  have h1 := (mem_normalizer_iff_gLBConj_eq).1 (hA hh)
  have h2 := (mem_normalizer_iff_gLBConj_eq).1 (hB hh)
  unfold GLBConj at h1 h2 ⊢
  rw [Subgroup.map_sup, h1, h2]

theorem card_barX_of_isPGroup {X F : Subgroup G} (hF : IsPGroup 3 ↥F) (hFX : F ≤ X) :
    Nat.card (barX 3 X F) = Nat.card F := by
  have hinj := injective_barX_comp Nat.prime_three hF hFX
  have hrange : barX 3 X F = ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp
      (F.subgroupOf X).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFX).toEquiv]

theorem centralizer_barX_le_normalizer {X K' : Subgroup G} {x : G} (hxX : x ∈ X)
    (hx : IsPGroup 3 ↥(Subgroup.zpowers x))
    (hN : X ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (K' : Set G)) :
    Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨x, hxX⟩} :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ≤
      Subgroup.normalizer (barX 3 X K' : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
  have h1 : Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨x, hxX⟩} :
      Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ≤
      Subgroup.centralizer (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff] at hw ⊢
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((Subgroup.mem_subgroupOf).1 hc)
    have hc' : c = (⟨x, hxX⟩ : ↥X) ^ k := Subtype.ext (by simp [hk])
    rw [hc', map_zpow]
    exact (Commute.zpow_left (hw _ (Set.mem_singleton _)) k).eq
  have h2 := CFSG.HardMathSupport.Solomon.Coordinator.i183_centralizer_barX_le Nat.prime_three
    (Subgroup.zpowers_le.2 hxX) hx
  rw [centralizer_zpowers_eq] at h2
  exact (h1.trans h2).trans (barX_le_normalizer hN)

theorem barX_eq_of_isQuasisimple {X J K : Subgroup G} (hJK : J ≤ K) (hKX : K ≤ X)
    (hcov : barX 3 K J = ⊤) (hJperf : ⁅J, J⁆ = J) (hJ3 : 3 ∣ Nat.card J)
    (hq : CFSG.Open.IsQuasisimple ↥(barX 3 X K)) : barX 3 X J = barX 3 X K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJX : J ≤ X := hJK.trans hKX
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hπ
  set Kt := barX 3 X K with hKt
  set Ot := barX 3 X (GLAPPrimeCoreOf 3 K) with hOt
  have hOK : GLAPPrimeCoreOf 3 K ≤ K := Subgroup.map_subtype_le _
  have hOtK : Ot ≤ Kt := barX_mono hOK
  have hOn : (Ot.subgroupOf Kt).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hOtK).2 ?_
    exact barX_le_normalizer (le_normalizer_glaPPrimeCoreOf 3 K)
  have hOne : Ot.subgroupOf Kt ≠ ⊤ := by
    intro htop
    have hle : Kt ≤ Ot := Subgroup.subgroupOf_eq_top.1 htop
    have h3K : 3 ∣ Nat.card Kt :=
      Prop126b.three_dvd_card_barX hKX (hJ3.trans (Subgroup.card_dvd_of_le hJK))
    have hdvd : Nat.card Ot ∣ Nat.card (GLAPPrimeCoreOf 3 K) := by
      rw [hOt]
      unfold barX
      exact (Subgroup.card_map_dvd _ _).trans (dvd_of_eq
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOK.trans hKX)).toEquiv))
    exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
      ((h3K.trans (Subgroup.card_dvd_of_le hle)).trans hdvd)
  have hOc : Ot.subgroupOf Kt ≤ Subgroup.center ↥Kt := l119_normal_le_center hq hOne
  have hJtK : barX 3 X J ≤ Kt := barX_mono hJK
  have hJn : ((barX 3 X J).subgroupOf Kt).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJtK).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk' : (k : G) ∈ K := (Subgroup.mem_subgroupOf).1 hk
    obtain ⟨j, hj, o, ho, hjo⟩ := Sec12b.mem_mul_glaPPrimeCoreOf_of_barX hJK hcov hk'
    have hjX : j ∈ X := hJX hj
    have hoX : o ∈ X := hKX (hOK ho)
    have hke : k = ⟨j, hjX⟩ * ⟨o, hoX⟩ := Subtype.ext hjo
    have hoc : (⟨π ⟨o, hoX⟩, hOtK ⟨⟨o, hoX⟩, (Subgroup.mem_subgroupOf).2 ho, rfl⟩⟩ : ↥Kt) ∈
        Subgroup.center ↥Kt := hOc ((Subgroup.mem_subgroupOf).2 ⟨⟨o, hoX⟩, (Subgroup.mem_subgroupOf).2 ho, rfl⟩)
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hcw : ∀ w' ∈ Kt, π ⟨o, hoX⟩ * w' = w' * π ⟨o, hoX⟩ := by
      intro w' hw'
      have := Subgroup.mem_center_iff.1 hoc ⟨w', hw'⟩
      exact (congrArg Subtype.val this).symm
    have hconj : ∀ w' ∈ Kt, π k * w' * (π k)⁻¹ = π ⟨j, hjX⟩ * w' * (π ⟨j, hjX⟩)⁻¹ := by
      intro w' hw'
      rw [hke, map_mul]
      have h1 : π ⟨o, hoX⟩ * w' * (π ⟨o, hoX⟩)⁻¹ = w' := by
        rw [hcw w' hw']
        group
      calc π ⟨j, hjX⟩ * π ⟨o, hoX⟩ * w' * (π ⟨j, hjX⟩ * π ⟨o, hoX⟩)⁻¹ =
          π ⟨j, hjX⟩ * (π ⟨o, hoX⟩ * w' * (π ⟨o, hoX⟩)⁻¹) * (π ⟨j, hjX⟩)⁻¹ := by group
        _ = π ⟨j, hjX⟩ * w' * (π ⟨j, hjX⟩)⁻¹ := by rw [h1]
    have hjJ : π ⟨j, hjX⟩ ∈ barX 3 X J := ⟨⟨j, hjX⟩, (Subgroup.mem_subgroupOf).2 hj, rfl⟩
    constructor
    · intro hw
      rw [hconj w (hJtK hw)]
      exact (barX 3 X J).mul_mem ((barX 3 X J).mul_mem hjJ hw) ((barX 3 X J).inv_mem hjJ)
    · intro hw
      have hwK : w ∈ Kt := by
        have h1 : π k * w * (π k)⁻¹ ∈ Kt := hJtK hw
        have h2 : π k ∈ Kt := ⟨k, hk, rfl⟩
        have := Kt.mul_mem (Kt.mul_mem (Kt.inv_mem h2) h1) h2
        simpa [mul_assoc] using this
      rw [hconj w hwK] at hw
      have := (barX 3 X J).mul_mem ((barX 3 X J).mul_mem ((barX 3 X J).inv_mem hjJ) hw) hjJ
      simpa [mul_assoc] using this
  have hsn : IsSubnormal (barX 3 X J) Kt := IsSubnormal.step hJtK hJn (IsSubnormal.refl Kt)
  exact Prop126b.eq_of_subnormal_perfect hq hsn (barX_perfect 3 hJX hJperf)
    (Prop126b.barX_ne_bot_of_three_dvd hJX hJ3)

theorem isQuasisimple_of_central {Y : Type} [Group Y] (hperf : commutator Y = ⊤) (N : Subgroup Y)
    [N.Normal] (hN : N ≤ Subgroup.center Y) (hs : IsSimpleGroup (Y ⧸ N))
    (hnc : ∃ u v : Y ⧸ N, u * v ≠ v * u) : CFSG.Open.IsQuasisimple Y := by
  refine ⟨hperf, ?_⟩
  have hZn : ((Subgroup.center Y).map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  haveI := hs
  haveI := hZn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.center Y).map (QuotientGroup.mk' N)) with
    hbot | htop
  · have hZ : Subgroup.center Y = N := by
      refine le_antisymm (fun z hz => ?_) hN
      have h1 : QuotientGroup.mk' N z ∈ (Subgroup.center Y).map (QuotientGroup.mk' N) :=
        Subgroup.mem_map_of_mem _ hz
      rw [hbot, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff z).1 h1
    have e : Y ⧸ Subgroup.center Y ≃* Y ⧸ N := QuotientGroup.quotientMulEquivOfEq hZ
    exact (e.isSimpleGroup_congr).2 hs
  · exfalso
    obtain ⟨u, v, huv⟩ := hnc
    apply huv
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N u
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N v
    have hy : QuotientGroup.mk' N y ∈ (Subgroup.center Y).map (QuotientGroup.mk' N) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨z, hz, hzy⟩ := hy
    rw [← hzy]
    have := Subgroup.mem_center_iff.1 hz w
    rw [← map_mul, ← map_mul, this]

theorem isQuasisimple_of_glaPComponent_centralizer (hLB : CFSG.Open.LBalanceStatement)
    {Q : Type} [Group Q] [Finite Q] (hQK : CFSG.Open.IsKGroup Q) (hQO : GLAPPrimeCore 3 Q = ⊥)
    {b : Q} (hb : b ^ 3 = 1) {K : Subgroup Q}
    (hK : GLAPComponent 3 (Subgroup.centralizer ({b} : Set Q)) K)
    (hs : IsSimpleGroup (↥K ⧸ GLAPPrimeCore 3 ↥K))
    (hnc : ∃ u v : ↥K ⧸ GLAPPrimeCore 3 ↥K, u * v ≠ v * u) : CFSG.Open.IsQuasisimple ↥K := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set P : Subgroup Q := Subgroup.zpowers b with hP
  have hPp : IsPGroup 3 ↥P := l119_isPGroup_zpowers hb
  have hCN : Subgroup.centralizer (P : Set Q) ≤ Subgroup.normalizer (P : Set Q) :=
    Subgroup.centralizer_le_normalizer _
  have hsn : IsSubnormal (Subgroup.centralizer (P : Set Q)) (Subgroup.normalizer (P : Set Q)) := by
    refine IsSubnormal.step hCN ((Subgroup.normal_subgroupOf_iff_le_normalizer hCN).2 ?_)
      (IsSubnormal.refl _)
    intro g hg
    rw [mem_normalizer_iff_gLBConj_eq, gLBConj_centralizer,
      (mem_normalizer_iff_gLBConj_eq).1 hg]
  rw [← centralizer_zpowers_eq] at hK
  have hKN := l119_glaPComponent_of_isSubnormal hp3 hsn hK
  obtain ⟨-, -, hcomm⟩ := hLB Q hQK 3 hp3 P hPp
  have hcore : CFSG.Open.lBalancePrimeCore 3 (⊤ : Subgroup Q) = ⊥ := by
    refine eq_bot_iff.2 (sSup_le fun N hN => ?_)
    obtain ⟨-, hNn, hNc⟩ := hN
    have hNn' : N.Normal := by
      have := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : N ≤ ⊤)).1 hNn
      exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 this)
    have : N ≤ GLAPPrimeCore 3 Q := le_sSup ⟨hNn', hNc⟩
    rwa [hQO] at this
  have hKL : K ≤ CFSG.Open.lBalancePLayer 3 (Subgroup.normalizer (P : Set Q)) :=
    le_sSup ((CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff).1 hKN).2
  have hOL : GLAPPrimeCoreOf 3 K ≤ CFSG.Open.lBalancePrimeCore 3 (Subgroup.normalizer (P : Set Q)) := by
    refine (glaPPrimeCoreOf_le_of_isSubnormal hp3 hKN.2.1).trans (le_sSup ⟨Subgroup.map_subtype_le _, ?_, ?_⟩)
    · rw [GLAPPrimeCoreOf]
      rw [show ∀ (H : Subgroup Q) (S : Subgroup ↥H), (S.map H.subtype).subgroupOf H = S from
        fun H S => Subgroup.comap_map_eq_self_of_injective H.subtype_injective S]
      infer_instance
    · exact (Nat.Prime.coprime_iff_not_dvd hp3).2 (not_dvd_card_glaPPrimeCoreOf hp3 _)
  have hperf : commutator ↥K = ⊤ :=
    Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 (glaPComponent_perfect hK))
  refine isQuasisimple_of_central hperf (GLAPPrimeCore 3 ↥K) ?_ hs hnc
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro k
  apply Subtype.ext
  have hoO : (o : Q) ∈ GLAPPrimeCoreOf 3 K := Subgroup.mem_map_of_mem K.subtype ho
  exact hcomm hcore (k : Q) (hKL k.2) (o : Q) (hOL hoO)

theorem isLThreeFour_of_single (hLB : CFSG.Open.LBalanceStatement) (h252 : Input25_2) {X Ls F J : Subgroup G}
    (hXK : CFSG.Open.IsKGroup ↥X) (hLs : GLAPComponent 3 X Ls) (hJLs : J ≤ Ls)
    (hFX : F ≤ X) (hFel : IsElemAbelian 3 F) (hF9 : Nat.card F = 9)
    (hFN : F ≤ Subgroup.normalizer (Ls : Set G))
    (hJF : J ≤ Subgroup.centralizer (F : Set G)) (hJperf : ⁅J, J⁆ = J)
    (hJt : IsLThreeFour (barOf 3 J)) (K' : G → Subgroup G)
    (hKcomp : ∀ x ∈ F, x ≠ 1 →
      GLAPComponent 3 (X ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) (K' x))
    (hKN : ∀ x ∈ F, x ≠ 1 → X ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (K' x : Set G))
    (hJK : ∀ x ∈ F, x ≠ 1 → J ≤ K' x) (hKL : ∀ x ∈ F, x ≠ 1 → K' x ≤ Ls)
    (hcov : ∀ x ∈ F, x ≠ 1 → barX 3 (K' x) J = ⊤) :
    IsLThreeFour (barOf 3 Ls) ∧ barX 3 X J = barX 3 X Ls := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hπ
  have hQO : GLAPPrimeCore 3 (↥X ⧸ GLAPPrimeCore 3 ↥X) = ⊥ := glaPPrimeCore_quotient_eq_bot hp3
  have hQK : CFSG.Open.IsKGroup (↥X ⧸ GLAPPrimeCore 3 ↥X) := isKGroup_barX_quotient hXK
  have hLcomp : IsComponentOf (barX 3 X Ls) ⊤ := hLs.2.2.1
  have hLq : CFSG.Open.IsQuasisimple ↥(barX 3 X Ls) := hLcomp.2.2
  have hLK : CFSG.Open.IsKGroup ↥(barX 3 X Ls) := isKGroup_subgroup' hQK _
  have hLO : GLAPPrimeCore 3 ↥(barX 3 X Ls) = ⊥ :=
    Prop126b.primeCore_sub_eq_bot hp3 hQO hLcomp.2.1
  have hLX : Ls ≤ X := hLs.1
  have hJX : J ≤ X := hJLs.trans hLX
  have hJ3 : 3 ∣ Nat.card J := three_dvd_card_of_isLThreeFour hJt
  have hFp : IsPGroup 3 ↥F := Lemma124.isPGroup_three_of_isElemAbelian hFel
  have key : ∀ b (hb : b ∈ F), b ≠ 1 → barX 3 X (K' b) = barX 3 X J ∧
      CFSG.Open.IsQuasisimple ↥(barX 3 X J) ∧
      Subgroup.centralizer ({π ⟨b, hFX hb⟩} : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ≤
        Subgroup.normalizer (barX 3 X J : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    intro b hb hb1
    have hbX : b ∈ X := hFX hb
    have hb3 : IsPGroup 3 ↥(Subgroup.zpowers b) := l119_isPGroup_zpowers (hFel.2 b hb)
    have hKb := hKcomp b hb hb1
    have hKbX : K' b ≤ X := hKb.1.trans inf_le_left
    have hKbC : K' b ≤ Subgroup.centralizer ({b} : Set G) := by
      have := hKb.1.trans inf_le_right
      rwa [centralizer_zpowers_eq] at this
    have hKbXC : GLAPComponent 3 (X ⊓ Subgroup.centralizer ({b} : Set G)) (K' b) := by
      rw [← centralizer_zpowers_eq]
      exact hKb
    have hcompX := Prop126b.glaPComponent_barX_inf_centralizer hp3 hbX le_rfl
      (Subgroup.le_normalizer hbX) hb3 hKbXC
    rw [barX_self, top_inf_eq] at hcompX
    have hb3' : π ⟨b, hbX⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨b, hbX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hFel.2 b hb)
      rw [this, map_one]
    have hKbt : IsLThreeFour (↥(barX 3 X (K' b)) ⧸ GLAPPrimeCore 3 ↥(barX 3 X (K' b))) := by
      obtain ⟨e, -⟩ := Lemma1245.exists_barOf_equiv_of_cover (p := 3) hp3 (hJK b hb hb1) (hcov b hb hb1)
      exact Lemma1245.isLThreeFour_congr (e.trans (Prop126b.barOfBarX hp3 hKbX)) hJt
    obtain ⟨hs, hnc⟩ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isLThreeFour hKbt
    have hqK : CFSG.Open.IsQuasisimple ↥(barX 3 X (K' b)) :=
      isQuasisimple_of_glaPComponent_centralizer hLB hQK hQO hb3' hcompX hs hnc
    have heq := barX_eq_of_isQuasisimple (hJK b hb hb1) hKbX (hcov b hb hb1) hJperf hJ3 hqK
    refine ⟨heq.symm, heq ▸ hqK, ?_⟩
    rw [heq]
    exact centralizer_barX_le_normalizer hbX hb3 (hKN b hb hb1)
  have hFne : F ≠ ⊥ := by
    intro hF
    rw [hF, Subgroup.card_bot] at hF9
    omega
  obtain ⟨⟨x₀, hx₀F⟩, hx₀ne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hFne
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀ne (Subtype.ext h)
  obtain ⟨-, hJq, hJN₀⟩ := key x₀ hx₀F hx₀1
  have hJle : barX 3 X J ≤ barX 3 X Ls ⊓ Subgroup.centralizer
      (barX 3 X F : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    refine le_inf (barX_mono hJLs) (barX_le_centralizer fun s hs t ht _ _ => ?_)
    have hst : t * s = s * t := Subgroup.mem_centralizer_iff.1 (hJF hs) t ht
    have : s * t * s⁻¹ * t⁻¹ = 1 := by
      rw [← hst]
      group
    rw [this]
    exact Subgroup.one_mem _
  have hJn : ((barX 3 X J).subgroupOf (barX 3 X Ls ⊓ Subgroup.centralizer
      (barX 3 X F : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).2 ?_
    refine inf_le_right.trans (le_trans ?_ hJN₀)
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.2
      ⟨⟨x₀, hFX hx₀F⟩, (Subgroup.mem_subgroupOf).2 hx₀F, rfl⟩)
  have hJL34 : IsLThreeFour (↥(barX 3 X J) ⧸ GLAPPrimeCore 3 ↥(barX 3 X J)) :=
    Lemma1245.isLThreeFour_congr (Prop126b.barOfBarX hp3 hJX) hJt
  have hcond : ∀ b' ∈ barX 3 X F, b' ≠ 1 →
      ((barX 3 X J ⊔ GLAPPrimeCoreOf 3 (barX 3 X Ls ⊓ Subgroup.centralizer ({b'} :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))).subgroupOf (barX 3 X Ls ⊓ Subgroup.centralizer ({b'} :
          Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))).Normal := by
    rintro _ ⟨⟨b, hbX⟩, hbF, rfl⟩ hb1
    have hbF' : b ∈ F := (Subgroup.mem_subgroupOf).1 hbF
    have hb1' : b ≠ 1 := by
      rintro rfl
      apply hb1
      have h1 : (⟨1, hbX⟩ : ↥X) = 1 := rfl
      rw [h1, map_one]
    obtain ⟨-, -, hJNb⟩ := key b hbF' hb1'
    set H := barX 3 X Ls ⊓ Subgroup.centralizer ({π ⟨b, hbX⟩} : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))
      with hH
    have hJH : barX 3 X J ≤ H := by
      refine le_inf (barX_mono hJLs) ?_
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      have := (hJle hw).2
      exact (Subgroup.mem_centralizer_iff.1 this) _ ⟨⟨b, hbX⟩, (Subgroup.mem_subgroupOf).2 hbF', rfl⟩
    have hle : barX 3 X J ⊔ GLAPPrimeCoreOf 3 H ≤ H := sup_le hJH (Subgroup.map_subtype_le _)
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_
    exact le_normalizer_sup (inf_le_right.trans hJNb) (le_normalizer_glaPPrimeCoreOf 3 H)
  have hF9' : Nat.card (barX 3 X F) = 9 := by rw [card_barX_of_isPGroup hFp hFX, hF9]
  have hres : IsLThreeFour ↥(barX 3 X Ls) :=
    h252 (↥X ⧸ GLAPPrimeCore 3 ↥X) (barX 3 X Ls) (barX 3 X F) (barX 3 X J) hLq hLK hLO
      (barX_le_normalizer hFN) (isElemAbelian_barX hFel) hF9' hJle hJn hJq hJL34 hcond
  have e : barOf 3 Ls ≃* ↥(barX 3 X Ls) :=
    (Prop126b.barOfBarX hp3 hLX).trans
      ((QuotientGroup.quotientMulEquivOfEq hLO).trans QuotientGroup.quotientBot)
  refine ⟨Lemma1245.isLThreeFour_congr e.symm hres, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (barX_mono hJLs) ?_
  rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour hres]
  have h1 := CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour hJL34
  rw [← h1]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)

end TypeStep

section CoreStep

variable {G : Type} [Group G] [Finite G]

open CFSG.RankThree.PerfectCover (hopfMultiplier)

theorem isPGroup_two_of_central_L34
    {Λ : Type} [Group Λ] [Finite Λ] (hperf : commutator Λ = ⊤) (P₂ P₃ : Subgroup Λ) [P₂.Normal]
    [P₃.Normal] (hle : P₂ ≤ P₃) (h2 : IsPGroup 2 ↥P₂) (h3 : Nat.Coprime 3 (Nat.card P₃))
    (hcomm : ∀ g : Λ, ∀ n ∈ P₃, g * n * g⁻¹ * n⁻¹ ∈ P₂) (hL : IsLThreeFour (Λ ⧸ P₃)) :
    IsPGroup 2 ↥P₃ := by
  set Z : Subgroup (Λ ⧸ P₂) := P₃.map (QuotientGroup.mk' P₂) with hZ
  haveI hZn : Z.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hEperf : Group.IsPerfect (Λ ⧸ P₂) := by
    refine Group.isPerfect_def.2 ?_
    rw [_root_.commutator_def, eq_top_iff]
    intro w _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective P₂ w
    have hg : g ∈ ⁅(⊤ : Subgroup Λ), (⊤ : Subgroup Λ)⁆ := by
      rw [← _root_.commutator_def, hperf]
      exact Subgroup.mem_top g
    have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' P₂) hg
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
    exact h1
  have hZc : Z ≤ Subgroup.center (Λ ⧸ P₂) := by
    rintro _ ⟨n, hn, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective P₂ w
    have h1 : QuotientGroup.mk' P₂ (g * n * g⁻¹ * n⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hcomm g n hn)
    simp only [map_mul, map_inv] at h1
    calc QuotientGroup.mk' P₂ g * QuotientGroup.mk' P₂ n =
        (QuotientGroup.mk' P₂ g * QuotientGroup.mk' P₂ n * (QuotientGroup.mk' P₂ g)⁻¹ *
          (QuotientGroup.mk' P₂ n)⁻¹) * (QuotientGroup.mk' P₂ n * QuotientGroup.mk' P₂ g) := by group
      _ = QuotientGroup.mk' P₂ n * QuotientGroup.mk' P₂ g := by rw [h1, one_mul]
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hEperf (QuotientGroup.mk' Z)
    (QuotientGroup.mk'_surjective Z) (by rw [QuotientGroup.ker_mk']; exact hZc)
  rw [QuotientGroup.ker_mk'] at hdvd
  obtain ⟨K, hKf, hKfin, hK4, ⟨e2⟩⟩ := hL
  have h48 : Nat.card (hopfMultiplier ((Λ ⧸ P₂) ⧸ Z)) = 48 := by
    rw [CFSG.Quasithin.H13.L3317.card_hopfMultiplier_congr
      ((QuotientGroup.quotientQuotientEquivQuotient P₂ P₃ hle).trans e2)]
    exact CFSG.HardMathSupport.Solomon.Proving.card_hopfMultiplier_statedProj_three_four hK4
  rw [h48] at hdvd
  have h3Z : Nat.Coprime (Nat.card Z) 3 :=
    Nat.Coprime.symm (h3.coprime_dvd_right (Subgroup.card_map_dvd _ _))
  have h16 : Nat.card Z ∣ 2 ^ 4 := h3Z.dvd_of_dvd_mul_right (by simpa using hdvd)
  intro n
  have hz : (QuotientGroup.mk' P₂ (n : Λ)) ^ (2 ^ 4) = 1 := by
    have hmem : QuotientGroup.mk' P₂ (n : Λ) ∈ Z := ⟨n, n.2, rfl⟩
    obtain ⟨k, hk⟩ := h16
    have h1 : (⟨QuotientGroup.mk' P₂ (n : Λ), hmem⟩ : ↥Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    have h2 : QuotientGroup.mk' P₂ (n : Λ) ^ Nat.card Z = 1 := by
      have := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [hk, pow_mul, h2, one_pow]
  have hnP : (n : Λ) ^ (2 ^ 4) ∈ P₂ := by
    rw [← map_pow] at hz
    exact (QuotientGroup.eq_one_iff _).1 hz
  obtain ⟨k, hk⟩ := h2 ⟨(n : Λ) ^ (2 ^ 4), hnP⟩
  refine ⟨4 + k, Subtype.ext ?_⟩
  have h1 : ((n : Λ) ^ (2 ^ 4)) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [Subgroup.coe_pow, pow_add, pow_mul, h1]
  rfl

def actKer (X N P : Subgroup G) (hPX : X ≤ Subgroup.normalizer (P : Set G))
    (hNX : X ≤ Subgroup.normalizer (N : Set G)) : Subgroup G where
  carrier := {g | g ∈ X ∧ ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ ∈ P}
  mul_mem' := by
    rintro g h ⟨hgX, hg⟩ ⟨hhX, hh⟩
    refine ⟨X.mul_mem hgX hhX, fun n hn => ?_⟩
    have h1 : g * (h * n * h⁻¹ * n⁻¹) * g⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.1 (hPX hgX) _).1 (hh n hn)
    have e : g * h * n * (g * h)⁻¹ * n⁻¹ = (g * (h * n * h⁻¹ * n⁻¹) * g⁻¹) * (g * n * g⁻¹ * n⁻¹) := by
      group
    rw [e]
    exact P.mul_mem h1 (hg n hn)
  one_mem' := ⟨X.one_mem, fun n _ => by simp [P.one_mem]⟩
  inv_mem' := by
    rintro g ⟨hgX, hg⟩
    refine ⟨X.inv_mem hgX, fun n hn => ?_⟩
    have hn' : g⁻¹ * n * g ∈ N := by
      have := (Subgroup.mem_normalizer_iff.1 (hNX (X.inv_mem hgX)) n).1 hn
      simpa using this
    have h1 := P.inv_mem (hg _ hn')
    have e : g⁻¹ * n * g⁻¹⁻¹ * n⁻¹ = (g * (g⁻¹ * n * g) * g⁻¹ * (g⁻¹ * n * g)⁻¹)⁻¹ := by group
    rw [e]
    exact h1

theorem le_actKer_iff {X N P : Subgroup G} {hPX : X ≤ Subgroup.normalizer (P : Set G)}
    {hNX : X ≤ Subgroup.normalizer (N : Set G)} {H : Subgroup G} :
    H ≤ actKer X N P hPX hNX ↔ H ≤ X ∧ ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ ∈ P :=
  ⟨fun h => ⟨fun g hg => (h hg).1, fun g hg => (h hg).2⟩, fun h g hg => ⟨h.1 hg, h.2 g hg⟩⟩

theorem le_normalizer_actKer {X N P : Subgroup G} (hPX : X ≤ Subgroup.normalizer (P : Set G))
    (hNX : X ≤ Subgroup.normalizer (N : Set G)) :
    X ≤ Subgroup.normalizer ((actKer X N P hPX hNX : Subgroup G) : Set G) := by
  have key : ∀ x ∈ X, ∀ g ∈ actKer X N P hPX hNX, x * g * x⁻¹ ∈ actKer X N P hPX hNX := by
    rintro x hxX g ⟨hgX, hg⟩
    refine ⟨X.mul_mem (X.mul_mem hxX hgX) (X.inv_mem hxX), fun n hn => ?_⟩
    have hn' : x⁻¹ * n * x ∈ N := by
      have := (Subgroup.mem_normalizer_iff.1 (hNX (X.inv_mem hxX)) n).1 hn
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.1 (hPX hxX) _).1 (hg _ hn')
    have e : x * g * x⁻¹ * n * (x * g * x⁻¹)⁻¹ * n⁻¹ =
        x * (g * (x⁻¹ * n * x) * g⁻¹ * (x⁻¹ * n * x)⁻¹) * x⁻¹ := by group
    rw [e]
    exact h1
  intro x hxX
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact key x hxX g
  · intro hg
    have := key x⁻¹ (X.inv_mem hxX) _ hg
    simpa [mul_assoc] using this

theorem core_le_pCore_two
    {M X Ls H : Subgroup G} {u : G}
    (hLs : GLAPComponent 3 X Ls) (hLt : IsLThreeFour (barOf 3 Ls))
    (hLJ : Ls ≤ GLAPLayer 3 H ⊔ GLAPPrimeCoreOf 3 X) (hJX : GLAPLayer 3 H ≤ X)
    (hJt : IsLThreeFour (barOf 3 (GLAPLayer 3 H)))
    (hMX : pCoreOf 2 M ≤ X) (hO3 : GLAPPrimeCoreOf 3 X ≤ M)
    (hu : u ∈ pCoreOf 2 M) (huN : u ∈ Subgroup.normalizer (GLAPLayer 3 H : Set G))
    (hu1 : barAut 3 (GLAPLayer 3 H) ⟨u, huN⟩ ≠ 1) :
    GLAPPrimeCoreOf 3 Ls ≤ pCoreOf 2 Ls := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set J := GLAPLayer 3 H with hJdef
  set N := GLAPPrimeCoreOf 3 X with hNdef
  set P := pCoreOf 2 X with hPdef
  have hNX' : N ≤ X := Subgroup.map_subtype_le _
  have hNX : X ≤ Subgroup.normalizer (N : Set G) := le_normalizer_glaPPrimeCoreOf 3 X
  have hPX : X ≤ Subgroup.normalizer (P : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  set 𝒦 := actKer X N P hPX hNX with h𝒦
  have h𝒦N : X ≤ Subgroup.normalizer ((𝒦 : Subgroup G) : Set G) := le_normalizer_actKer hPX hNX
  have hNcop : Nat.Coprime 3 (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd hp3).2 (not_dvd_card_glaPPrimeCoreOf hp3 X)
  have hR : pCoreOf 2 M ⊓ N ≤ P := by
    have hR2 : IsPGroup 2 ↥(pCoreOf 2 M ⊓ N) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
    have hRN : N ≤ Subgroup.normalizer ((pCoreOf 2 M ⊓ N : Subgroup G) : Set G) := by
      intro n hn
      exact Prop121.normalizer_inf_mem (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hO3 hn))
        (Subgroup.le_normalizer hn)
    have h1 : pCoreOf 2 M ⊓ N ≤ pCoreOf 2 N :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hRN hR2
    have h2 : pCoreOf 2 N ≤ P :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 N).trans hNX')
        (hNX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    exact h1.trans h2
  have hM𝒦 : pCoreOf 2 M ≤ 𝒦 := by
    refine le_actKer_iff.2 ⟨hMX, fun t ht n hn => hR ⟨?_, ?_⟩⟩
    · have h1 : n * t⁻¹ * n⁻¹ ∈ pCoreOf 2 M :=
        (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hO3 hn))
          _).1 ((pCoreOf 2 M).inv_mem ht)
      have e : t * n * t⁻¹ * n⁻¹ = t * (n * t⁻¹ * n⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 M).mul_mem ht h1
    · have h1 : t * n * t⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 (hNX (hMX ht)) n).1 hn
      exact N.mul_mem h1 (N.inv_mem hn)
  have hJ𝒦 : J ≤ 𝒦 := by
    set D : Subgroup G := 𝒦 ⊓ J with hD
    have hDJ : D ≤ J := inf_le_right
    have hDn : (D.subgroupOf J).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hDJ).2 ?_
      intro j hj
      exact Prop121.normalizer_inf_mem (h𝒦N (hJX hj)) (Subgroup.le_normalizer hj)
    have hcomm : ∀ j ∈ J, j * u * j⁻¹ * u⁻¹ ∈ D := by
      intro j hj
      refine ⟨?_, ?_⟩
      · have h1 : j * u * j⁻¹ ∈ 𝒦 := (Subgroup.mem_normalizer_iff.1 (h𝒦N (hJX hj)) u).1 (hM𝒦 hu)
        exact 𝒦.mul_mem h1 (𝒦.inv_mem (hM𝒦 hu))
      · have h1 : u * j⁻¹ * u⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 huN _).1 (J.inv_mem hj)
        have e : j * u * j⁻¹ * u⁻¹ = j * (u * j⁻¹ * u⁻¹) := by group
        rw [e]
        exact J.mul_mem hj h1
    haveI := hDn
    have hDbn : ((D.subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J))).Normal :=
      hDn.map _ (QuotientGroup.mk'_surjective _)
    obtain ⟨hsimp, -⟩ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isLThreeFour hJt
    haveI := hsimp
    haveI := hDbn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((D.subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J))) with hbot | htop
    · exfalso
      apply hu1
      apply MulEquiv.ext
      intro w
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective w
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.one_apply]
      have hjm : (j : G)⁻¹ * u * j * u⁻¹ ∈ D := by
        have := hcomm (j : G)⁻¹ (J.inv_mem j.2)
        simpa using this
      have hjm' : (⟨(j : G)⁻¹ * u * j * u⁻¹, hDJ hjm⟩ : ↥J) ∈ D.subgroupOf J :=
        (Subgroup.mem_subgroupOf).2 hjm
      have h1 : (QuotientGroup.mk (⟨(j : G)⁻¹ * u * j * u⁻¹, hDJ hjm⟩ : ↥J) : barOf 3 J) = 1 := by
        have := Subgroup.mem_map_of_mem (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) hjm'
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      have he : (J.normalizerMonoidHom ⟨u, huN⟩ j) = j * ⟨(j : G)⁻¹ * u * j * u⁻¹, hDJ hjm⟩ := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        show u * (j : G) * u⁻¹ = (j : G) * ((j : G)⁻¹ * u * j * u⁻¹)
        group
      rw [he, QuotientGroup.mk_mul, h1, mul_one]
    · have hJle : J ≤ 𝒦 ⊔ GLAPPrimeCoreOf 3 J := by
        intro j hj
        have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) ⟨j, hj⟩ ∈
            (D.subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) := by
          rw [htop]
          exact Subgroup.mem_top _
        obtain ⟨d, hd, hdj⟩ := hmem
        have hdj' : d⁻¹ * ⟨j, hj⟩ ∈ GLAPPrimeCore 3 ↥J := QuotientGroup.eq.1 hdj
        have e : j = (d : G) * ((d⁻¹ * ⟨j, hj⟩ : ↥J) : G) := by simp
        rw [e]
        exact Subgroup.mul_mem_sup ((Subgroup.mem_subgroupOf).1 hd).1
          (Subgroup.mem_map_of_mem J.subtype hdj')
      exact layer_le_of_le_sup ((Nat.Prime.coprime_iff_not_dvd hp3).2
        (not_dvd_card_glaPPrimeCoreOf hp3 J))
        (((Subgroup.map_subtype_le _ : GLAPPrimeCoreOf 3 J ≤ J)).trans (hJX.trans h𝒦N)) hJle
  have hL𝒦 : Ls ≤ 𝒦 :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_le_sup hp3 hLs hNcop (hNX'.trans h𝒦N)
      (hLJ.trans (sup_le_sup_right hJ𝒦 _))
  have hLN : GLAPPrimeCoreOf 3 Ls ≤ N := glaPPrimeCoreOf_le_of_isSubnormal hp3 hLs.2.1
  have hcommL : ∀ l ∈ Ls, ∀ n ∈ GLAPPrimeCoreOf 3 Ls, l * n * l⁻¹ * n⁻¹ ∈ pCoreOf 2 Ls := by
    intro l hl n hn
    have h1 : l * n * l⁻¹ * n⁻¹ ∈ P := ((le_actKer_iff.1 hL𝒦).2 l hl n (hLN hn))
    have hnL : n ∈ Ls := (Subgroup.map_subtype_le _ : GLAPPrimeCoreOf 3 Ls ≤ Ls) hn
    have h2 : l * n * l⁻¹ * n⁻¹ ∈ Ls :=
      Ls.mul_mem (Ls.mul_mem (Ls.mul_mem hl hnL) (Ls.inv_mem hl)) (Ls.inv_mem hnL)
    have hPL : P ⊓ Ls ≤ pCoreOf 2 Ls := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_left)
      intro g hg
      exact Prop121.normalizer_inf_mem (hPX (hLs.1 hg)) (Subgroup.le_normalizer hg)
    exact hPL ⟨h1, h2⟩
  have hperf : commutator ↥Ls = ⊤ :=
    Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 (glaPComponent_perfect hLs))
  have h2P : IsPGroup 2 ↥(GLAPPrimeCore 3 ↥Ls) := by
    refine isPGroup_two_of_central_L34 hperf (CFSG.pCore 2 ↥Ls) (GLAPPrimeCore 3 ↥Ls)
      (Prop126b.pCore_two_le_primeCore_three _) CFSG.pCore_isPGroup CFSG.pPrimeCore_coprime_card
      ?_ hLt
    intro g n hn
    have hn' : (n : G) ∈ GLAPPrimeCoreOf 3 Ls := Subgroup.mem_map_of_mem Ls.subtype hn
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 (hcommL (g : G) g.2 (n : G) hn')
    have hyeq' : y = g * n * g⁻¹ * n⁻¹ := Subtype.ext (by simpa using hyeq)
    rw [← hyeq']
    exact hy
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le _)
    (le_normalizer_glaPPrimeCoreOf 3 Ls) ?_
  exact h2P.map Ls.subtype

end CoreStep

section Jstar

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input25_2)

theorem ff_le_ww {M A K : Subgroup G} (hFM : Lemma1245.FF A K ≤ M) :
    Lemma1245.FF A K ≤ Lemma1245.WW M A K := by
  intro f hf
  by_cases hf1 : f = 1
  · rw [hf1]
    exact Subgroup.one_mem _
  · have hmem : f ∈ (⨆ (_ : f ∈ Lemma1245.FF A K) (_ : f ≠ 1), M ⊓ Cg f : Subgroup G) := by
      rw [iSup_pos hf, iSup_pos hf1]
      refine ⟨hFM hf, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      rfl
    exact le_iSup (fun i => ⨆ (_ : i ∈ Lemma1245.FF A K) (_ : i ≠ 1), M ⊓ Cg i) f hmem

theorem jw_ne_top {m : ℕ} {B M E A K : Subgroup G} {a : G} (h111 : Prop111Statement)
    (h : Cex121 G m 3 B M E A a)
    (hII : ∀ x ∈ Lemma1245.FF A K, x ≠ 1 →
      Cg x ≤ Subgroup.normalizer (Kx 3 (Lemma1245.JJ A K) x : Set G) ∧
        barX 3 (Kx 3 (Lemma1245.JJ A K) x) (Lemma1245.JJ A K) = ⊤)
    (haF : a ∈ Lemma1245.FF A K) : Lemma1245.JJ A K ⊔ Lemma1245.WW M A K ≠ ⊤ := by
  haveI : IsSimpleGroup G := h.standing.simple
  have hFM : Lemma1245.FF A K ≤ M := (inf_le_right : Lemma1245.FF A K ≤ A).trans h.pair.1.2.1.1.1.1
  have hJC : Lemma1245.JJ A K ≤ Subgroup.centralizer ((Lemma1245.FF A K : Subgroup G) : Set G) :=
    (Sec12b.layer_le 3 _).trans inf_le_right
  have hJa : Lemma1245.JJ A K ≤ Cg a := hJC.trans (Sec12b.cent_le_cent_of_mem haF)
  have hJtop : Lemma1245.JJ A K ≠ ⊤ := fun hJ =>
    Sec12b.cent_ne_top h.standing h.ha.2 (top_le_iff.1 (hJ ▸ hJa))
  have hF0 : Lemma1245.FF A K ≠ ⊥ := fun hF => h.ha.2 (by
    rw [hF] at haF
    exact Subgroup.mem_bot.1 haF)
  have hWM : Lemma1245.WW M A K ≤ M := iSup_le fun x => iSup_le fun _ => iSup_le fun _ => inf_le_left
  have hWtop : Lemma1245.WW M A K ≠ ⊤ := fun hW =>
    isTwoLocal_ne_top h.standing h.pre.1.1 (top_le_iff.1 (hW ▸ hWM))
  have hJN : Lemma1245.JJ A K ≤ Subgroup.normalizer ((Lemma1245.FF A K : Subgroup G) : Set G) :=
    fun j hj => Subgroup.centralizer_le_normalizer _ (hJC hj)
  have hdecX := Lemma1245.mem_sup_decomp_of_perm (Lemma1245.perm_J_W h111 h hII)
  intro hTop
  apply GL83.I_32_8_proved G (Lemma1245.WW M A K) (Lemma1245.JJ A K) (Lemma1245.FF A K) hWtop hJtop hF0
    (ff_le_ww hFM) hJN
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨w, hw, j, hj, rfl⟩ := hdecX g (hTop ▸ Subgroup.mem_top g)
  exact Set.mul_mem_mul hw hj

theorem kx_glaPComponent {m : ℕ} {B M E A K : Subgroup G} {a : G} (h111 : Prop111Statement)
    (h : Cex121 G m 3 B M E A a) (hJt : IsLThreeFour (barOf 3 (Lemma1245.JJ A K)))
    {x : G} (hx : x ∈ Lemma1245.FF A K) (hx1 : x ≠ 1)
    (hN : Cg x ≤ Subgroup.normalizer (Kx 3 (Lemma1245.JJ A K) x : Set G))
    (hcov : barX 3 (Kx 3 (Lemma1245.JJ A K) x) (Lemma1245.JJ A K) = ⊤) :
    GLAPComponent 3 ((Lemma1245.JJ A K ⊔ Lemma1245.WW M A K) ⊓
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) (Kx 3 (Lemma1245.JJ A K) x) := by
  rw [centralizer_zpowers_eq]
  have hJC : Lemma1245.JJ A K ≤ Subgroup.centralizer ((Lemma1245.FF A K : Subgroup G) : Set G) :=
    (Sec12b.layer_le 3 _).trans inf_le_right
  have hJx : Lemma1245.JJ A K ≤ Subgroup.centralizer ({x} : Set G) :=
    hJC.trans (Sec12b.cent_le_cent_of_mem hx)
  have hle : Kx 3 (Lemma1245.JJ A K) x ≤ (Lemma1245.JJ A K ⊔ Lemma1245.WW M A K) ⊓ Cg x :=
    le_inf (Lemma1245.kx_le_JW h111 h hx hx1 hN hcov) (Sec12b.kx_le_cent hJx)
  refine glaPComponent_of_normal hle ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2
    (inf_le_right.trans hN)) (fun N₀ O hON hO h' => kx_le_of_le_sup hO hON h') ?_
  obtain ⟨e, -⟩ := Lemma1245.exists_barOf_equiv_of_cover (p := 3) Nat.prime_three
    (Sec12b.le_kx (p := 3) x (Lemma1245.JJ A K)) hcov
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e
    (isQuasisimple_of_isLThreeFour hJt)

theorem jstarClaim_of_inputs
    (h111 : Prop111Statement) (h1834 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4)
    (hLB : CFSG.Open.LBalanceStatement) (h252 : Input25_2) : Lemma1245.JstarClaim := by
  intro G _ _ m B M E A a h K hK _hK3 _hKM _hu₀ _hA0 hII hJt hIV hF2 hO3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  set F := Lemma1245.FF A K with hFdef
  set J := Lemma1245.JJ A K with hJdef
  set W := Lemma1245.WW M A K with hWdef
  have hFA : F ≤ A := inf_le_right
  have hFM : F ≤ M := hFA.trans hAM
  have hFel : IsElemAbelian 3 F := Lemma124.isElemAbelian_of_le hFA hAel
  have hF9 : Nat.card F = 9 := by
    rw [Lemma124.card_eq_pow_pRank hFel, hF2]
    norm_num
  have haF : a ∈ F := Lemma1245.mem_centBar_of_component h.ha.1 (Lemma124.comp_le_aux hK)
  have hJC : J ≤ Subgroup.centralizer (F : Set G) := (Sec12b.layer_le 3 _).trans inf_le_right
  have hXtop : J ⊔ W ≠ ⊤ := jw_ne_top h111 h hII haF
  have hXK : CFSG.Open.IsKGroup ↥(J ⊔ W) := isKGroup_of_isKProper h.standing.kProper hXtop
  have hFX : F ≤ J ⊔ W := (ff_le_ww hFM).trans le_sup_right
  have hJX : J ≤ J ⊔ W := le_sup_left
  have hJperf : ⁅J, J⁆ = J := layer_perfect _
  have hJ3 : 3 ∣ Nat.card J := three_dvd_card_of_isLThreeFour hJt
  have hKcomp : ∀ x ∈ F, x ≠ 1 → GLAPComponent 3 ((J ⊔ W) ⊓
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) (Kx 3 J x) :=
    fun x hx hx1 => kx_glaPComponent h111 h hJt hx hx1 (hII x hx hx1).1 (hII x hx hx1).2
  have hFK : ∀ x ∈ F, x ≠ 1 → F ≤ Subgroup.normalizer (Kx 3 J x : Set G) := by
    intro x hx hx1 f hf
    refine (hII x hx hx1).1 (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
    rw [Set.mem_singleton_iff.1 hy]
    exact CFSG.Open.IsElemAbelian.comm hFel hx hf
  obtain ⟨Ls, hLs, hJLs, hFN, hKLs⟩ := exists_single_component h1834 hXK hFX hFel hF9 hJX hJperf hJ3
    hJC (Kx 3 J) hKcomp (fun x _ _ => Sec12b.le_kx (p := 3) x J) hFK
  obtain ⟨hLt, hbar⟩ := isLThreeFour_of_single hLB h252 hXK hLs hJLs hFX hFel hF9 hFN hJC hJperf hJt
    (Kx 3 J) hKcomp (fun x hx hx1 => inf_le_right.trans (hII x hx hx1).1)
    (fun x _ _ => Sec12b.le_kx (p := 3) x J) hKLs (fun x hx hx1 => (hII x hx hx1).2)
  have hLJ : Ls ≤ J ⊔ GLAPPrimeCoreOf 3 (J ⊔ W) := by
    intro l hl
    obtain ⟨j, hj, hjl⟩ := exists_of_barX_le (le_of_eq hbar.symm) hl (hLs.1 hl)
    have e : l = j * (j⁻¹ * l) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hj hjl
  obtain ⟨u, ⟨⟨huO, -⟩, -⟩, huN, huU⟩ := hIV
  have hu1 : barAut 3 J ⟨u, huN⟩ ≠ 1 := by
    intro h1
    have := huU.1
    rw [h1, orderOf_one] at this
    norm_num at this
  have hMX : pCoreOf 2 M ≤ J ⊔ W :=
    (Sec12b.pCore_le_join hFM hFel hF2).trans le_sup_right
  exact ⟨Ls, hLs, hJLs, hLt, core_le_pCore_two hLs hLt hLJ hJX hJt hMX hO3 huO huN hu1⟩

end Jstar

section SClaimSec

variable {G : Type} [Group G] [Finite G]

@[expose] def Input27_5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → GLAPPrimeCore 3 X = ⊥ →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
    ∀ B : Subgroup X, IsElemAbelian 3 B → Nat.card B = 9 →
    ∀ S : Subgroup X, IsPGroup 2 ↥S → B ≤ Subgroup.normalizer (S : Set X) →
      S ≤ Subgroup.normalizer ((⨆ b ∈ B, GLBConj b K : Subgroup X) : Set X) →
      ¬ (⨆ b ∈ B, GLBConj b K) ≤ Subgroup.centralizer (S : Set X) →
      (∀ b ∈ B, b ≠ 1 →
        S ⊓ Subgroup.centralizer ({b} : Set X) ≤ pCoreOf 2 (Subgroup.centralizer ({b} : Set X))) →
      (⨆ b ∈ B, GLBConj b K) ≤ (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), Subgroup.centralizer ({b} : Set X)) ∨
      (∃ n : ℕ, IsAltType n ↥K) ∨
      (CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = 2 ∧ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) = 2 ∧
        9 ∣ Nat.card ↥K ∧ ¬ 81 ∣ Nat.card ↥K)

@[expose] def Input31_10ab : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (X L : Subgroup G), GLAPComponent 3 X L →
    ((∃ n : ℕ, IsAltType n (barOf 3 L)) ∨
      (¬ 81 ∣ Nat.card L ∧ CFSG.Open.pRank 3 (⊤ : Subgroup (barOf 3 L)) = 2 ∧
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 L))) = 2)) →
    ∀ R : Subgroup G, IsSylowIn 3 X R → ∀ U V : Subgroup G, IsEkIn 3 4 R U → IsEkIn 3 4 R V →
      IsKConnectedIn 3 3 X U V

theorem le_normalizer_iSup {Y : Type*} [Group Y] {ι : Sort*} {H : Subgroup Y} (L : ι → Subgroup Y)
    (h : ∀ i, H ≤ Subgroup.normalizer (L i : Set Y)) :
    H ≤ Subgroup.normalizer ((⨆ i, L i : Subgroup Y) : Set Y) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  unfold GLBConj
  rw [Subgroup.map_iSup]
  congr 1
  funext i
  have := (mem_normalizer_iff_gLBConj_eq).1 (h i hg)
  unfold GLBConj at this
  exact this

theorem centralizer_mk_le_barX {X : Subgroup G} {x : G} (hxX : x ∈ X)
    (hx : IsPGroup 3 ↥(Subgroup.zpowers x)) :
    Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨x, hxX⟩} :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ≤ barX 3 X (X ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have h1 : Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨x, hxX⟩} :
      Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ≤
      Subgroup.centralizer (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff] at hw ⊢
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((Subgroup.mem_subgroupOf).1 hc)
    have hc' : c = (⟨x, hxX⟩ : ↥X) ^ k := Subtype.ext (by simp [hk])
    rw [hc', map_zpow]
    exact (Commute.zpow_left (hw _ (Set.mem_singleton _)) k).eq
  have h2 := CFSG.HardMathSupport.Solomon.Coordinator.i183_centralizer_barX_le Nat.prime_three
    (Subgroup.zpowers_le.2 hxX) hx
  rw [centralizer_zpowers_eq] at h2
  exact h1.trans h2

theorem commutatorElement_mul_central {Y : Type*} [Group Y] {a b z w : Y} (hz : ∀ y : Y, z * y = y * z)
    (hw : ∀ y : Y, w * y = y * w) : ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc z * a * (w * b) * (z * a)⁻¹ * (w * b)⁻¹ = z * (a * (w * b) * a⁻¹) * z⁻¹ * (w * b)⁻¹ := by group
    _ = (a * (w * b) * a⁻¹) * z * z⁻¹ * (w * b)⁻¹ := by rw [hz]
    _ = a * w * (b * a⁻¹ * b⁻¹) * w⁻¹ := by group
    _ = w * a * (b * a⁻¹ * b⁻¹) * w⁻¹ := by rw [← hw a]
    _ = w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * w * w⁻¹ := by rw [hw]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem le_centralizer_of_mutual {Y : Type} [Group Y] [Finite Y] {I S : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥I) (hS2 : IsPGroup 2 ↥S)
    (hSI : S ≤ Subgroup.normalizer (I : Set Y)) (hIS : I ≤ Subgroup.normalizer (S : Set Y)) :
    S ≤ Subgroup.centralizer (I : Set Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup Y := S ⊓ I with hD
  have hcommD : ∀ s ∈ S, ∀ k ∈ I, s * k * s⁻¹ * k⁻¹ ∈ D := by
    intro s hs k hk
    refine ⟨?_, ?_⟩
    · have h1 : k * s⁻¹ * k⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hIS hk) _).1 (S.inv_mem hs)
      have e : s * k * s⁻¹ * k⁻¹ = s * (k * s⁻¹ * k⁻¹) := by group
      rw [e]
      exact S.mul_mem hs h1
    · have h1 : s * k * s⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 (hSI hs) k).1 hk
      exact I.mul_mem h1 (I.inv_mem hk)
  have hDn : (D.subgroupOf I).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 ?_
    intro k hk
    exact Prop121.normalizer_inf_mem (hIS hk) (Subgroup.le_normalizer hk)
  have hDne : D.subgroupOf I ≠ ⊤ := by
    intro htop
    have hI2 : IsPGroup 2 ↥I := by
      intro k
      have hkD : (k : Y) ∈ D := (Subgroup.mem_subgroupOf).1 (htop ▸ Subgroup.mem_top k)
      obtain ⟨n, hn⟩ := hS2 ⟨k, hkD.1⟩
      exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
    haveI : Group.IsNilpotent ↥I := hI2.isNilpotent
    haveI : Nontrivial (↥I ⧸ Subgroup.center ↥I) := hq.2.toNontrivial
    haveI : Nontrivial ↥I := (QuotientGroup.mk'_surjective (Subgroup.center ↥I)).nontrivial
    haveI : Group.IsPerfect ↥I := ⟨hq.1⟩
    exact (Group.IsPerfect.not_isSolvable (G := ↥I)) inferInstance
  haveI := hDn
  have hDc : D.subgroupOf I ≤ Subgroup.center ↥I := l119_normal_le_center hq hDne
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  have hIperf : ⁅I, I⁆ = I := by
    have h1 : commutator ↥I = ⊤ := hq.1
    exact Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 h1)
  have hfix : ⁅I, I⁆ ≤ Subgroup.centralizer ({s} : Set Y) := by
    refine Subgroup.commutator_le.2 fun k₁ hk₁ k₂ hk₂ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    set φ₁ : ↥I := ⟨s * k₁ * s⁻¹, (Subgroup.mem_normalizer_iff.1 (hSI hs) k₁).1 hk₁⟩
    set φ₂ : ↥I := ⟨s * k₂ * s⁻¹, (Subgroup.mem_normalizer_iff.1 (hSI hs) k₂).1 hk₂⟩
    have hz : ∀ (k : Y) (hk : k ∈ I) (hφ : s * k * s⁻¹ ∈ I),
        (⟨s * k * s⁻¹, hφ⟩ : ↥I) * (⟨k, hk⟩ : ↥I)⁻¹ ∈ Subgroup.center ↥I := by
      intro k hk hφ
      apply hDc
      rw [Subgroup.mem_subgroupOf]
      exact hcommD s hs k hk
    have hc := commutatorElement_mul_central (a := (⟨k₁, hk₁⟩ : ↥I)) (b := (⟨k₂, hk₂⟩ : ↥I))
      (fun y => (Subgroup.mem_center_iff.1 (hz k₁ hk₁ φ₁.2) y).symm)
      (fun y => (Subgroup.mem_center_iff.1 (hz k₂ hk₂ φ₂.2) y).symm)
    have hc' := congrArg Subtype.val hc
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at hc'
    rw [commutatorElement_def]
    have e : s * (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) * s⁻¹ =
        s * k₁ * s⁻¹ * k₁⁻¹ * k₁ * (s * k₂ * s⁻¹ * k₂⁻¹ * k₂) *
          (s * k₁ * s⁻¹ * k₁⁻¹ * k₁)⁻¹ * (s * k₂ * s⁻¹ * k₂⁻¹ * k₂)⁻¹ := by group
    refine Eq.symm ?_
    calc s * (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) = s * (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) * s⁻¹ * s := by group
      _ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ * s := by rw [e, hc']
  have hk : ∀ k ∈ I, s * k = k * s := by
    intro k hk'
    have := hfix (hIperf.symm ▸ hk' : k ∈ ⁅I, I⁆)
    exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
  intro k hk'
  exact (hk k hk').symm

theorem false_of_sylow_connected' {m : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m 3 B M E A a)
    (hk : CFSG.Open.pRank 3 (E ⊓ A) = 2) (hA4 : 4 ≤ CFSG.Open.pRank 3 A)
    {P : Subgroup G} (hP : IsSylowIn 3 ⊤ P)
    (hconnP : ∀ U V : Subgroup G, IsEkIn 3 4 P U → IsEkIn 3 4 P V → IsKConnectedIn 3 3 ⊤ U V) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hSC : IsSCp 3 ⊤ A := (lemma104_ii_holds h.toSec11.toSec10Fails h.pair).2
  have hcardA : Nat.card A = 3 ^ CFSG.Open.pRank 3 A := Lemma124.card_eq_pow_pRank hAel
  have hEel : IsElemAbelian 3 E := h.pair.1.1.1.1.2.1
  have hEM : E ≤ M := h.pair.1.1.1.1.1
  have hE4 : 4 ≤ CFSG.Open.pRank 3 E := by
    have h3 : 3 ≤ CFSG.Open.pRank 3 E := h.pair.1.1.1.2
    by_contra hlt
    have hE3 : CFSG.Open.pRank 3 E = 3 := by omega
    have := lemma104_vi_holds h.toSec11.toSec10Fails h.pair hE3
    omega
  have hcardE : Nat.card E = 3 ^ CFSG.Open.pRank 3 E := Lemma124.card_eq_pow_pRank hEel
  obtain ⟨H4, hH4⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 3 (n := 4)
    (by rw [hcardE]; exact pow_dvd_pow 3 hE4)
  set E4 : Subgroup G := H4.map E.subtype with hE4def
  have hE4E : E4 ≤ E := Subgroup.map_subtype_le _
  have hE4card : Nat.card E4 = 3 ^ 4 := by
    rw [hE4def, Subgroup.card_map_of_injective E.subtype_injective, hH4]
  have hE4el : IsElemAbelian 3 E4 := Lemma124.isElemAbelian_of_le hE4E hEel
  obtain ⟨U4, hU4⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) 3 (n := 4)
    (by rw [hcardA]; exact pow_dvd_pow 3 hA4)
  set A4 : Subgroup G := U4.map A.subtype with hA4def
  have hA4A : A4 ≤ A := Subgroup.map_subtype_le _
  have hA4card : Nat.card A4 = 3 ^ 4 := by
    rw [hA4def, Subgroup.card_map_of_injective A.subtype_injective, hU4]
  have hA4el : IsElemAbelian 3 A4 := Lemma124.isElemAbelian_of_le hA4A hAel
  have hEA3 : IsPGroup 3 ↥(E ⊔ A) := lemma104_i_holds h.toSec11.toSec10Fails h.pair
  obtain ⟨R, hR, hEAR⟩ := Lemma124.exists_isSylowIn_above_aux (sup_le hEM hAM) hEA3
  obtain ⟨-, -, hRG⟩ := lemma104_iv_holds h.toSec11.toSec10Fails h.pair hk hR
  obtain ⟨g, hg⟩ := Lemma1112b.exists_glbConj_le_of_isSylowIn hRG hP.2.1
  have hgP : GLBConj g P = R :=
    ((Lemma1211.isSylowIn_top_gLBConj hP g).2.2 R le_top hRG.2.1 hg).symm
  have hRP : GLBConj g⁻¹ R = P := by rw [← hgP, gLBConj_inv_gLBConj]
  have hEk : ∀ U, IsEkIn 3 4 R U → IsEkIn 3 4 P (GLBConj g⁻¹ U) := fun U hU =>
    ⟨hRP ▸ gLBConj_mono g⁻¹ hU.1, Lemma1112b.isElemAbelian_glbConj hU.2.1 _,
      (Lemma1112b.card_glbConj _ _).trans hU.2.2⟩
  have hAk : IsEkIn 3 4 R A4 := ⟨hA4A.trans (le_sup_right.trans hEAR), hA4el, hA4card⟩
  have hE4k : IsEkIn 3 4 R E4 := ⟨hE4E.trans (le_sup_left.trans hEAR), hE4el, hE4card⟩
  have hc2 := Claims1245.isKConnectedIn_top_gLBConj (hconnP _ _ (hEk A4 hAk) (hEk E4 hE4k)) g
  rw [gLBConj_gLBConj_inv, gLBConj_gLBConj_inv] at hc2
  have hc3 : IsKConnectedIn 3 3 ⊤ A E := Lemma116.isKConnectedIn_extend hp3 le_rfl hc2 hA4A hE4E
    hAel hEel (by rw [hcardA]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
    (by rw [hcardE]; exact Nat.pow_le_pow_right (by norm_num) (by omega)) le_top le_top
  have hconn : IsKConnectedIn 3 (CFSG.Open.pRank 3 (E ⊓ A) + 1) ⊤ A E := by
    rw [hk]
    exact hc3
  have hDA : inD 3 M A := lemma104_iii_holds h.toSec11.toSec10Fails h.pair hSC h.pair.1.1 hconn
  exact h.pair.1.2.1.2 hDA.2

theorem sClaim_of_inputs (h117 : Prop117_cex_falseStatement) (h191 : Lemma129.Input19_1_two)
    (h275 : Input27_5)
    (h3110 : Input31_10ab) : Lemma1245.SClaim := by
  intro G _ _ m B M E A a h K hK hK3 hKM _hu₀ hA0 hdec hF2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hS10 : GLStanding G m 3 := h.standing
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hEM : E ≤ M := h.pair.1.1.1.1.1
  set F := Lemma1245.FF A K with hFdef
  set J := Lemma1245.JJ A K with hJdef
  set W := Lemma1245.WW M A K with hWdef
  set S := pCoreOf 2 (M ⊓ (J ⊔ W)) with hSdef
  have hFA : F ≤ A := inf_le_right
  have hFM : F ≤ M := hFA.trans hAM
  have hFel : IsElemAbelian 3 F := Lemma124.isElemAbelian_of_le hFA hAel
  have hF9 : Nat.card F = 9 := by
    rw [Lemma124.card_eq_pow_pRank hFel, hF2]
    norm_num
  have hFp : IsPGroup 3 ↥F := Lemma124.isPGroup_three_of_isElemAbelian hFel
  have hFW : F ≤ W := ff_le_ww hFM
  have hAX : A ≤ J ⊔ W := by
    rw [hdec]
    exact sup_le (inf_le_right.trans le_sup_left) (hFW.trans le_sup_right)
  have hYS : M ⊓ (J ⊔ W) ≤ Subgroup.normalizer (S : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := fun x hx => hYS ⟨hAM hx, hAX hx⟩
  have hSM : S ≤ M := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hS2 : IsPGroup 2 ↥S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hCW : ∀ x ∈ F, x ≠ 1 → M ⊓ Cg x ≤ M ⊓ (J ⊔ W) := by
    intro x hx hx1
    have hxW : M ⊓ Cg x ≤ W := le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le hx1 le_rfl))
    exact le_inf inf_le_left (hxW.trans le_sup_right)
  have hMtop : M ≠ ⊤ := isTwoLocal_ne_top hS10 h.pre.1.1
  have hMK : CFSG.Open.IsKGroup ↥M := isKGroup_of_isKProper hS10.kProper hMtop
  have hQK : CFSG.Open.IsKGroup (↥M ⧸ GLAPPrimeCore 3 ↥M) := isKGroup_barX_quotient hMK
  have hQO : GLAPPrimeCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M) = ⊥ := glaPPrimeCore_quotient_eq_bot hp3
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) with hπ
  have hπinj := injective_barX_comp hp3 hFp hFM
  have hπx : ∀ x (hx : x ∈ F), x ≠ 1 → π ⟨x, hFM hx⟩ ^ 3 = 1 ∧ π ⟨x, hFM hx⟩ ≠ 1 := by
    intro x hx hx1
    refine ⟨?_, fun h1 => hx1 ?_⟩
    · rw [← map_pow]
      have : (⟨x, hFM hx⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hFel.2 x hx)
      rw [this, map_one]
    · have h2 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)).comp (F.subgroupOf M).subtype ⟨⟨x, hFM hx⟩, hx⟩ =
          (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)).comp (F.subgroupOf M).subtype 1 := by
        rw [map_one]
        exact h1
      have := congrArg (fun y : ↥(F.subgroupOf M) => ((y : ↥M) : G)) (hπinj h2)
      simpa using this
  by_contra hSO
  have hSt : barX 3 M S ≠ ⊥ := fun hb =>
    hSO ((CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_eq_bot_iff hSM).1 hb)
  have hSt2 : IsPGroup 2 ↥(barX 3 M S) :=
    (hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm).map _
  have hCx : ∀ x (hx : x ∈ F), x ≠ 1 → Subgroup.centralizer ({π ⟨x, hFM hx⟩} :
      Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) ≤ barX 3 M (M ⊓ (J ⊔ W)) := fun x hx hx1 =>
    (centralizer_mk_le_barX (hFM hx) (l119_isPGroup_zpowers (hFel.2 x hx))).trans
      (barX_mono (hCW x hx hx1))
  have hStN : barX 3 M (M ⊓ (J ⊔ W)) ≤
      Subgroup.normalizer (barX 3 M S : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := barX_le_normalizer hYS
  have hSx : ∀ x (hx : x ∈ F), x ≠ 1 → barX 3 M S ⊓ Subgroup.centralizer ({π ⟨x, hFM hx⟩} :
      Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) ≤ pCoreOf 2 (Subgroup.centralizer ({π ⟨x, hFM hx⟩} :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) := by
    intro x hx hx1
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (hSt2.to_le inf_le_left)
    intro c hc
    exact Prop121.normalizer_inf_mem (hStN (hCx x hx hx1 hc)) (Subgroup.le_normalizer hc)
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3 hp3 F S
    (fun f => Subtype.ext (by simpa using hFel.2 f.1 f.2)) (by rw [hF9]; norm_num)
    (by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS2
      rw [hn]
      intro hd
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp3 Nat.prime_two).1 (hp3.dvd_of_dvd_pow hd))
        (by norm_num))
    (hFA.trans hAS)
  have hSle : ∀ T : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M),
      (∀ x (_ : x ∈ F), x ≠ 1 → barX 3 M (S ⊓ Cg x) ≤ T) → barX 3 M S ≤ T := by
    intro T hT
    rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff hSM, hgen]
    refine iSup₂_le fun f hf1 => ?_
    have hf1' : (f : G) ≠ 1 := fun h' => hf1 (Subtype.ext h')
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff (inf_le_left.trans hSM)]
    exact hT f f.2 hf1'
  have hΔ : ∀ x (hx : x ∈ F), x ≠ 1 →
      barX 3 M (S ⊓ Cg x) ≤ barX 3 M (Lemma129.deltaTwo M (Subgroup.zpowers x)) ∧
      (∀ L : Subgroup G, GLAPComponent 3 M L →
        barX 3 M (Lemma129.deltaTwo M (Subgroup.zpowers x)) ≤
          Subgroup.normalizer (barX 3 M L : Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) ∧
      barX 3 M (Lemma129.deltaTwo M (Subgroup.zpowers x)) ≤ Subgroup.centralizer
        (CFSG.Open.pCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M) : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    intro x hx hx1
    have hx3 : x ^ 3 = 1 := hFel.2 x hx
    have hEk : IsEkIn 3 1 M (Subgroup.zpowers x) :=
      ⟨Subgroup.zpowers_le.2 (hFM hx),
        Lemma124.isElemAbelian_of_le (Subgroup.zpowers_le.2 hx) hFel,
        by rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, pow_one]⟩
    obtain ⟨⟨h1, h2⟩, -⟩ := h191 G hS10.kProper 3 hp3 (by norm_num) M hMtop 1 _ le_rfl hEk
    refine ⟨barX_mono ?_, h1, h2⟩
    refine le_iInf₂ fun d hd => le_iInf fun hd1 => ?_
    rw [centralizer_eq_of_mem_zpowers hx3 hd hd1]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (inf_le_left.trans hSM) inf_le_right) ?_ (hS2.to_le inf_le_left)
    intro c hc
    exact Prop121.normalizer_inf_mem (hYS (hCW x hx hx1 hc)) (Subgroup.le_normalizer hc.2)
  have hSN : ∀ L : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M), IsComponentOf L ⊤ →
      barX 3 M S ≤ Subgroup.normalizer (L : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    intro L hL
    obtain ⟨L₀, hL₀, rfl⟩ := exists_glaPComponent_barX_eq M hL
    exact hSle _ fun x hx hx1 => (hΔ x hx hx1).1.trans ((hΔ x hx hx1).2.1 L₀ hL₀)
  have hSC : barX 3 M S ≤ Subgroup.centralizer
      (CFSG.Open.pCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M) : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) :=
    hSle _ fun x hx hx1 => (hΔ x hx hx1).1.trans (hΔ x hx hx1).2.2
  obtain ⟨I, hI, hIS⟩ : ∃ I : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M), IsComponentOf I ⊤ ∧
      ¬ barX 3 M S ≤ Subgroup.centralizer (I : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    by_contra hcon
    push Not at hcon
    apply hSt
    have hdisj := IsPGroup.disjoint_of_ne 2 3 (by norm_num) (barX 3 M S)
      (CFSG.Open.pCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M)) hSt2 CFSG.pCore_isPGroup
    refine eq_bot_iff.2 fun s hs => ?_
    have hsO := mem_pCore_of_centralizes hp3 hQO (hSC hs) (fun L hL => hcon L hL hs)
    exact (Subgroup.disjoint_def.1 hdisj) hs hsO ▸ Subgroup.one_mem _
  set Ks := ⨆ b ∈ barX 3 M F, GLBConj b I with hKs
  have hIKs : I ≤ Ks := le_iSup₂_of_le (f := fun b (_ : b ∈ barX 3 M F) => GLBConj b I) 1
    (Subgroup.one_mem _) (le_of_eq (gLBConj_one I).symm)
  have hSNKs : barX 3 M S ≤ Subgroup.normalizer (Ks : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    refine le_normalizer_iSup _ fun b => le_normalizer_iSup _ fun hb => hSN _ ?_
    have := Prop95Parts.Input18.isComponentOf_conj hI b⁻¹
    exact this
  have hnot : ¬ Ks ≤ Subgroup.centralizer (barX 3 M S : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := fun h' =>
    hIS (Subgroup.le_centralizer_iff.1 (hIKs.trans h'))
  have hcond : ∀ b ∈ barX 3 M F, b ≠ 1 → barX 3 M S ⊓ Subgroup.centralizer ({b} :
      Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) ≤ pCoreOf 2 (Subgroup.centralizer ({b} :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) := by
    rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩ hx1
    have hxF : x ∈ F := (Subgroup.mem_subgroupOf).1 hx
    have hx1' : x ≠ 1 := by
      rintro rfl
      apply hx1
      have h1 : (⟨1, hxM⟩ : ↥M) = 1 := rfl
      rw [h1, map_one]
    exact hSx x hxF hx1'
  rcases h275 _ hQK hQO I hI (barX 3 M F) (isElemAbelian_barX hFel)
      (by rw [card_barX_of_isPGroup hFp hFM, hF9]) (barX 3 M S) hSt2
      (barX_le_normalizer (hFA.trans hAS)) hSNKs hnot hcond with ha | hbc
  ·
    have hKsY : Ks ≤ barX 3 M (M ⊓ (J ⊔ W)) := by
      refine ha.trans (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_)
      obtain ⟨⟨x, hxM⟩, hx, rfl⟩ := hb
      have hxF : x ∈ F := (Subgroup.mem_subgroupOf).1 hx
      have hx1' : x ≠ 1 := by
        rintro rfl
        apply hb1
        have h1 : (⟨1, hxM⟩ : ↥M) = 1 := rfl
        rw [h1, map_one]
      exact hCx x hxF hx1'
    exact hIS (le_centralizer_of_mutual hI.2.2 hSt2 (hSN I hI) ((hIKs.trans hKsY).trans hStN))
  ·
    obtain ⟨L, hL, hLbar⟩ := exists_glaPComponent_barX_eq M hI
    have e : barOf 3 L ≃* ↥I :=
      (quotEquivBarX hp3 hL.1 hL.2.1).trans (MulEquiv.subgroupCongr hLbar)
    have htype : (∃ n : ℕ, IsAltType n (barOf 3 L)) ∨
        (¬ 81 ∣ Nat.card L ∧ CFSG.Open.pRank 3 (⊤ : Subgroup (barOf 3 L)) = 2 ∧
          CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 L))) = 2) := by
      rcases hbc with ⟨n, ⟨f⟩⟩ | ⟨h1, h2, -, h4⟩
      · exact Or.inl ⟨n, ⟨e.trans f⟩⟩
      · refine Or.inr ⟨fun h81 => h4 ?_, ?_, ?_⟩
        · have hcard : Nat.card L = Nat.card (barOf 3 L) * Nat.card (GLAPPrimeCore 3 ↥L) :=
            Subgroup.card_eq_card_quotient_mul_card_subgroup _
          rw [hcard] at h81
          have hcop : Nat.Coprime 81 (Nat.card (GLAPPrimeCore 3 ↥L)) := by
            have := Nat.Coprime.pow_left 4 (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥L))
            norm_num at this
            exact this
          rw [← Nat.card_congr e.toEquiv]
          exact hcop.dvd_of_dvd_mul_right h81
        · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
          exact h1
        · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (MulAut.congr e)]
          exact h2
    obtain ⟨R, hR, hEAR⟩ := Lemma124.exists_isSylowIn_above_aux (sup_le hEM hAM)
      (lemma104_i_holds h.toSec11.toSec10Fails h.pair)
    have hk : CFSG.Open.pRank 3 (E ⊓ A) = 2 :=
      Lemma124.pRank_eq_two_of_card_nine (Lemma124.isElemAbelian_of_le inf_le_right hAel) hA0.1
    obtain ⟨-, -, hRG⟩ := lemma104_iv_holds h.toSec11.toSec10Fails h.pair hk hR
    have hA4 : 4 ≤ CFSG.Open.pRank 3 A := by
      have h3 : 3 ≤ CFSG.Open.pRank 3 A := h.pair.1.2.1.1.2
      by_contra hlt
      have hA3 : CFSG.Open.pRank 3 A = 3 := by omega
      rcases (Lemma1245.prop117c_of_cex_false h117) h.toSec11 h.ha.1 h.ha.2 hK ⟨rfl, hA3, hK3⟩ with
        hKM' | ⟨A1, hA1, haA1⟩
      · exact hKM (Lemma124.barX_mono_aux 3 (le_inf hKM' (Lemma124.comp_le_aux hK)))
      · exact (Claims122.lemma122_i_ii_holds h).2 ⟨A1, hA1, haA1⟩
    exact false_of_sylow_connected' h hk hA4 hRG fun U V hU hV =>
      Claims1245.isKConnectedIn_top_of (h3110 M L hL htype R hR U V hU hV)

end SClaimSec

section VxSec

variable {G : Type} [Group G] [Finite G]

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem derivedInf_le' (H : Subgroup G) : derivedInf H ≤ H := by
  intro x hx
  have h0 := (Subgroup.mem_iInf.1 hx) 0
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 h0
  exact y.2

theorem derivedInf_perfect (H : Subgroup G) : ⁅derivedInf H, derivedInf H⁆ = derivedInf H := by
  have hstep : ∀ n : ℕ, derivedSeries ↥H (n + 1) ≤ derivedSeries ↥H n := fun n => by
    rw [derivedSeries_succ]
    exact Subgroup.commutator_le_left _ _
  have hanti : Antitone (derivedSeries ↥H) := antitone_nat_of_succ_le hstep
  obtain ⟨N, hN⟩ : ∃ N : ℕ, derivedSeries ↥H (N + 1) = derivedSeries ↥H N := by
    by_contra hne
    push Not at hne
    have hlt : ∀ n : ℕ, Nat.card (derivedSeries ↥H (n + 1)) < Nat.card (derivedSeries ↥H n) := fun n =>
      lt_of_le_of_ne (Subgroup.card_le_of_le (hstep n))
        (fun h => hne n (Subgroup.eq_of_le_of_card_ge (hstep n) h.ge))
    have key : ∀ n : ℕ, Nat.card (derivedSeries ↥H n) + n ≤ Nat.card (derivedSeries ↥H 0) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => have := hlt n; omega
    have h1 := key (Nat.card (derivedSeries ↥H 0) + 1)
    omega
  have hconst : ∀ k : ℕ, derivedSeries ↥H (N + k) = derivedSeries ↥H N := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← add_assoc, derivedSeries_succ, ih, ← derivedSeries_succ, hN]
  have hD : derivedInf H = (derivedSeries ↥H N).map H.subtype := by
    unfold derivedInf
    refine le_antisymm (iInf_le _ N) (le_iInf fun n => ?_)
    rcases le_total n N with hn | hn
    · exact Subgroup.map_mono (hanti hn)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [hconst k]
  rw [hD, ← Subgroup.map_commutator, ← derivedSeries_succ, hN]

theorem pCoreOf_two_inf_le {H K' : Subgroup G} (hK'H : K' ≤ H) :
    pCoreOf 2 H ⊓ K' ≤ pCoreOf 2 K' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left)
  intro k hk
  exact Prop121.normalizer_inf_mem (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hK'H hk))
    (Subgroup.le_normalizer hk)

theorem pCoreOf_two_cent_le_normalizer {A Y L : Subgroup G} (hA3 : IsPGroup 3 ↥A) (hAY : A ≤ Y)
    (hCY : Subgroup.centralizer (A : Set G) ≤ Y) (hL : GLAPComponent 3 Y L) :
    pCoreOf 2 (Subgroup.centralizer (A : Set G)) ≤ Subgroup.normalizer (L : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := pCoreOf 2 (Subgroup.centralizer (A : Set G)) with hW
  have hWC : W ≤ Subgroup.centralizer (A : Set G) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hWY : W ≤ Y := hWC.trans hCY
  have hW2 : IsPGroup 2 ↥W := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) with hπ
  have hO : GLAPPrimeCore 3 (↥Y ⧸ GLAPPrimeCore 3 ↥Y) = ⊥ :=
    glaPPrimeCore_quotient_eq_bot Nat.prime_three
  have hAb : IsPGroup 3 ↥(barX 3 Y A) :=
    (hA3.comap_of_injective Y.subtype Y.subtype_injective).map π
  have hWb2 : IsPGroup 2 ↥(barX 3 Y W) :=
    (hW2.comap_of_injective Y.subtype Y.subtype_injective).map π
  have hle : barX 3 Y W ≤ Subgroup.centralizer (barX 3 Y A : Set (↥Y ⧸ GLAPPrimeCore 3 ↥Y)) := by
    refine barX_le_centralizer fun s hs t ht _ _ => ?_
    have hst : t * s = s * t := Subgroup.mem_centralizer_iff.1 (hWC hs) t ht
    have : s * t * s⁻¹ * t⁻¹ = 1 := by
      rw [← hst]
      group
    rw [this]
    exact Subgroup.one_mem _
  have hWb : barX 3 Y W ≤ GLAPPrimeCoreOf 3
      (Subgroup.centralizer (barX 3 Y A : Set (↥Y ⧸ GLAPPrimeCore 3 ↥Y))) := by
    refine sec11_le_glaPPrimeCoreOf hle ?_ ?_
    · intro c hc n hn
      have hc' := CFSG.HardMathSupport.Solomon.Coordinator.i183_centralizer_barX_le Nat.prime_three hAY hA3 hc
      have hNW : Y ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (W : Set G) :=
        inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      exact (Subgroup.mem_normalizer_iff.1 (barX_le_normalizer hNW hc') n).1 hn
    · obtain ⟨k, hk⟩ := hWb2.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right _ (by norm_num)
  intro w hw
  have hwY : w ∈ Y := hWY hw
  have hnorm := CFSG.LocalAnalysis.GLTheoremA.lstar_claim hO _ (barX 3 Y A) hAb rfl (barX 3 Y L) hL.2.2.1
  have hwb : π ⟨w, hwY⟩ ∈ Subgroup.normalizer (barX 3 Y L : Set (↥Y ⧸ GLAPPrimeCore 3 ↥Y)) :=
    hnorm (hWb ⟨⟨w, hwY⟩, (Subgroup.mem_subgroupOf).2 hw, rfl⟩)
  rw [mem_normalizer_iff_gLBConj_eq]
  refine glaPComponent_unique (glaPComponent_conj hL hwY) hL ?_
  rw [CFSG.LocalAnalysis.GLTheoremB.barX_gLBConj_eq 3 hwY L]
  exact gLBConj_eq_of_mem_normalizer hwb

theorem gLBConj_le_normalizer {Y V L : Subgroup G} {g : G} (hg : g ∈ Y)
    (hV : ∀ L' : Subgroup G, GLAPComponent 3 Y L' → V ≤ Subgroup.normalizer (L' : Set G))
    (hL : GLAPComponent 3 Y L) : GLBConj g V ≤ Subgroup.normalizer (L : Set G) := by
  intro u hu
  have hgu : g * u * g⁻¹ ∈ V := mem_gLBConj.1 hu
  have h1 := hV _ (glaPComponent_conj hL (Y.inv_mem hg)) hgu
  rw [mem_normalizer_iff_gLBConj_eq, gLBConj_gLBConj] at h1
  have h2 := congrArg (GLBConj g) h1
  rw [gLBConj_gLBConj, gLBConj_gLBConj] at h2
  have e1 : g⁻¹ * (g * u * g⁻¹) * g = u := by group
  have e2 : g⁻¹ * g = 1 := by group
  rw [e1, e2, gLBConj_one] at h2
  rw [mem_normalizer_iff_gLBConj_eq]
  exact h2

theorem exists_inner_of_perfect' {Y : Type} [Group Y] {K P : Subgroup Y}
    (hK : Group.IsSolvable (Outer ↥K)) (hP : ⁅P, P⁆ = P)
    (hPN : P ≤ Subgroup.normalizer (K : Set Y)) {p : Y} (hp : p ∈ P) :
    ∃ l ∈ K, l⁻¹ * p ∈ Subgroup.centralizer (K : Set Y) := by
  haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hP
  haveI := hK
  obtain ⟨l, hl⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
    ((K.normalizerMonoidHom).comp (Subgroup.inclusion hPN)) ⟨p, hp⟩
  refine ⟨(l : Y), l.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨y, hy⟩ : ↥K) : Y)) hl
  simp only [MonoidHom.comp_apply, MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv] at h1
  calc y * ((l : Y)⁻¹ * p) = (l : Y)⁻¹ * ((l : Y) * y * (l : Y)⁻¹) * p := by group
    _ = (l : Y)⁻¹ * (p * y * p⁻¹) * p := by rw [h1]
    _ = (l : Y)⁻¹ * p * y := by group

theorem mem_centBar_forall_iff {Y : Type} [Group Y] {p : ℕ} {X L : Subgroup Y} {c : Y} :
    c ∈ centBar p X L ↔ c ∈ X ∧ ∃ _ : c ∈ Subgroup.normalizer (L : Set Y),
      ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf p L := by
  have key : ∀ γ : ↥(Subgroup.normalizer (L : Set Y)), barAut p L γ = 1 ↔
      ∀ l ∈ L, (γ : Y) * l * (γ : Y)⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf p L := by
    intro γ
    have hN := GLAPPrimeCore.normal p ↥L
    constructor
    · intro h l hl
      have h1 : barAut p L γ (QuotientGroup.mk ⟨l, hl⟩) = QuotientGroup.mk ⟨l, hl⟩ := by
        rw [h]; rfl
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, QuotientGroup.eq] at h1
      have h2 := hN.conj_mem _ (Subgroup.inv_mem _ h1) ⟨l, hl⟩
      refine ⟨_, h2, ?_⟩
      show ((⟨l, hl⟩ : ↥L) : Y) * (((L.normalizerMonoidHom γ ⟨l, hl⟩ : ↥L) : Y)⁻¹ * l)⁻¹ * l⁻¹ = _
      have e : ((L.normalizerMonoidHom γ ⟨l, hl⟩ : ↥L) : Y) = (γ : Y) * l * (γ : Y)⁻¹ := rfl
      rw [e]
      group
    · intro h
      ext q
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.one_apply, QuotientGroup.eq]
        obtain ⟨y, hy, hyx⟩ := h (x : Y) x.2
        simp only [Subgroup.coe_subtype] at hyx
        have h3 := hN.conj_mem _ (Subgroup.inv_mem _ hy) x⁻¹
        convert h3 using 1
        apply Subtype.ext
        have e : ((L.normalizerMonoidHom γ x : ↥L) : Y) = (γ : Y) * x * (γ : Y)⁻¹ := rfl
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, e, hyx]
        group
  constructor
  · intro hc
    obtain ⟨⟨γ, hγ, hγc⟩, hcX⟩ := Subgroup.mem_inf.1 hc
    subst hγc
    exact ⟨hcX, γ.2, (key γ).1 (MonoidHom.mem_ker.1 hγ)⟩
  · rintro ⟨hcX, hcN, hc⟩
    exact Subgroup.mem_inf.2 ⟨⟨⟨c, hcN⟩, MonoidHom.mem_ker.2 ((key ⟨c, hcN⟩).2 hc), rfl⟩, hcX⟩

theorem mem_core_of_barX {X J : Subgroup G} (hJX : J ≤ X) {c : G} (hcJ : c ∈ J)
    (hc : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨c, hJX hcJ⟩ ∈ GLAPPrimeCoreOf 3 (barX 3 X J)) :
    c ∈ GLAPPrimeCoreOf 3 J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hπ
  set f : ↥J →* ↥X ⧸ GLAPPrimeCore 3 ↥X := π.comp (Subgroup.inclusion hJX) with hf
  set O := GLAPPrimeCoreOf 3 (barX 3 X J) with hO
  set N : Subgroup ↥J := O.comap f with hN
  have hfJ : ∀ j : ↥J, f j ∈ barX 3 X J := fun j =>
    ⟨Subgroup.inclusion hJX j, (Subgroup.mem_subgroupOf).2 j.2, rfl⟩
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    show f (g * n * g⁻¹) ∈ O
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 (barX 3 X J) (hfJ g)) (f n)).1 hn
  have hNc : Nat.Coprime 3 (Nat.card N) := by
    apply Prop115.coprime_card_of_forall_orderOf_ne
    intro z hz hz3
    have hfz : f z ∈ O := hz
    have h1 : orderOf (f z) ∣ 3 := by
      have := orderOf_map_dvd f z
      rwa [hz3] at this
    have h2 : orderOf (f z) ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨f z, hfz⟩ : ↥O)
      rwa [Subgroup.orderOf_mk] at this
    have hnd := not_dvd_card_glaPPrimeCoreOf Nat.prime_three (barX 3 X J)
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · have hf1 : f z = 1 := orderOf_eq_one_iff.1 h
      have hinc : Subgroup.inclusion hJX z ∈ GLAPPrimeCore 3 ↥X := by
        rw [← QuotientGroup.eq_one_iff]
        exact hf1
      have hord : orderOf (Subgroup.inclusion hJX z) = 3 := by
        rw [orderOf_injective (Subgroup.inclusion hJX) (Subgroup.inclusion_injective hJX) z, hz3]
      exact (Prop115.orderOf_ne_of_coprime_card Nat.prime_three hinc CFSG.pPrimeCore_coprime_card) hord
    · rw [h] at h2
      exact hnd h2
  have hle : N ≤ GLAPPrimeCore 3 ↥J := le_sSup ⟨hNn, hNc⟩
  exact ⟨⟨c, hcJ⟩, hle hc, rfl⟩

theorem mulAut_congr_conj {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (z : X) :
    MulAut.congr e (MulAut.conj z) = MulAut.conj (e z) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem quotientCenterAut'_conj'' {Y : Type*} [Group Y] (y : Y) :
    quotientCenterAut' Y (MulAut.conj y) = MulAut.conj (QuotientGroup.mk y) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    show QuotientGroup.mk (MulAut.conj y x) = _
    rw [MulAut.conj_apply, MulAut.conj_apply]
    rfl

theorem barAut_eq_one_of_inner {K A₀ : Subgroup G}
    (hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hKperf : commutator (barOf 3 K) = ⊤) (hA0N : A₀ ≤ Subgroup.normalizer (K : Set G))
    (hA09 : Nat.card A₀ = 9) (hA0el : IsElemAbelian 3 A₀)
    (hA0f : ∀ b (hb : b ∈ A₀), barAut 3 K ⟨b, hA0N hb⟩ = 1 → b = 1)
    (hA0i : ∀ b (hb : b ∈ A₀), ∃ z : barOf 3 K, barAut 3 K ⟨b, hA0N hb⟩ = MulAut.conj z)
    {v : G} (hvN : v ∈ Subgroup.normalizer (K : Set G)) {n : ℕ} (hv2 : v ^ (2 ^ n) = 1)
    (hvA : ∀ b ∈ A₀, b * v = v * b) {z : barOf 3 K} (hvz : barAut 3 K ⟨v, hvN⟩ = MulAut.conj z) :
    barAut 3 K ⟨v, hvN⟩ = 1 := by
  set ρ : ↥(Subgroup.normalizer (K : Set G)) →* MulAut (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) :=
    (quotientCenterAut' (barOf 3 K)).comp (barAut 3 K) with hρ
  have hρconj : ∀ (g : ↥(Subgroup.normalizer (K : Set G))) (w : barOf 3 K), barAut 3 K g = MulAut.conj w →
      ρ g = MulAut.conj (QuotientGroup.mk w : barOf 3 K ⧸ Subgroup.center (barOf 3 K)) := by
    intro g w hg
    rw [hρ, MonoidHom.comp_apply, hg]
    exact quotientCenterAut'_conj'' w
  obtain ⟨hLs, hLnc⟩ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isLThreeFour hK3
  have hLc : Subgroup.center (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) = ⊥ := by
    haveI := hLs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (barOf 3 K ⧸ Subgroup.center (barOf 3 K))) with h | h
    · exact h
    · exfalso
      obtain ⟨u, w, huw⟩ := hLnc
      apply huw
      have hu : u ∈ Subgroup.center (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) := h ▸ Subgroup.mem_top u
      exact (Subgroup.mem_center_iff.1 hu w).symm
  have hinj := Lemma1245.conj_injective_of_center_bot hLc
  set ρ₀ : ↥A₀ →* MulAut (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) := ρ.comp (Subgroup.inclusion hA0N) with hρ₀
  have hρ₀c : ∀ b : ↥A₀, ∃ e : barOf 3 K ⧸ Subgroup.center (barOf 3 K), ρ₀ b = MulAut.conj e := by
    intro b
    obtain ⟨w, hw⟩ := hA0i b b.2
    exact ⟨QuotientGroup.mk w, hρconj _ w hw⟩
  have hρ₀inj : Function.Injective ρ₀ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have h1 : barAut 3 K (Subgroup.inclusion hA0N b) = 1 := by
      apply quotientCenterAut'_injective hKperf
      rw [map_one]
      exact hb
    exact Subtype.ext (hA0f b b.2 h1)
  set E : Subgroup (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) :=
    ρ₀.range.comap (MulAut.conj : (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) →* MulAut (barOf 3 K ⧸ Subgroup.center (barOf 3 K))) with hE
  have hEmap : E.map (MulAut.conj : (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) →* MulAut (barOf 3 K ⧸ Subgroup.center (barOf 3 K))) =
      ρ₀.range := by
    refine Subgroup.map_comap_eq_self ?_
    rintro _ ⟨b, rfl⟩
    obtain ⟨e, he⟩ := hρ₀c b
    exact ⟨e, he.symm⟩
  have hE9 : Nat.card E = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hEmap, ← hA09]
    exact (Nat.card_congr (MonoidHom.ofInjective hρ₀inj).toEquiv).symm
  have hEmem : ∀ e ∈ E, ∃ b : ↥A₀, ρ₀ b = MulAut.conj e := by
    intro e he
    obtain ⟨b, hb⟩ := he
    exact ⟨b, hb⟩
  have hEel : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun u w => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨b₁, hb₁⟩ := hEmem u u.2
      obtain ⟨b₂, hb₂⟩ := hEmem w w.2
      apply Subtype.ext
      apply hinj
      have hcomm : b₁ * b₂ = b₂ * b₁ :=
        Subtype.ext (CFSG.Open.IsElemAbelian.comm hA0el b₁.2 b₂.2)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, ← hb₁, ← hb₂, ← map_mul, ← map_mul, hcomm]
    · obtain ⟨b, hb⟩ := hEmem y hy
      apply hinj
      have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using hA0el.2 b b.2)
      rw [map_pow, ← hb, ← map_pow, hb3, map_one, map_one]
  set jh : barOf 3 K ⧸ Subgroup.center (barOf 3 K) := QuotientGroup.mk z with hjh
  have hρv : ρ ⟨v, hvN⟩ = MulAut.conj jh := hρconj _ z hvz
  have hjh2 : jh ^ (2 ^ n) = 1 := by
    apply hinj
    have hv' : (⟨v, hvN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ (2 ^ n) = 1 :=
      Subtype.ext (by simpa using hv2)
    rw [map_pow, ← hρv, ← map_pow, hv', map_one, map_one]
  have hS2 : IsPGroup 2 ↥(Subgroup.zpowers jh) := by
    have hdvd : orderOf jh ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hjh2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hES : E ≤ Subgroup.normalizer (Subgroup.zpowers jh : Set (barOf 3 K ⧸ Subgroup.center (barOf 3 K))) := by
    intro e he
    obtain ⟨b, hb⟩ := hEmem e he
    have hbv : (Subgroup.inclusion hA0N b) * ⟨v, hvN⟩ = ⟨v, hvN⟩ * (Subgroup.inclusion hA0N b) :=
      Subtype.ext (hvA b b.2)
    have hc : jh * e = e * jh := by
      apply hinj
      have h1 := congrArg ρ hbv
      rw [map_mul, map_mul] at h1
      have hb' : ρ (Subgroup.inclusion hA0N b) = MulAut.conj e := hb
      rw [hb', hρv] at h1
      rw [map_mul, map_mul]
      exact h1.symm
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun g hg => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (Commute.zpow_left hc k).eq
  have hS := CFSG.HardMathSupport.Solomon.UniquenessMaximal.eq_bot_of_two_group_normalized_by_nine hK3 hEel hE9
    hS2 hES
  have hj1 : jh = 1 := Subgroup.zpowers_eq_bot.1 hS
  have hρv1 : ρ ⟨v, hvN⟩ = 1 := by rw [hρv, hj1, map_one]
  apply quotientCenterAut'_injective hKperf
  rw [map_one]
  exact hρv1

end VxSec

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1245b

end
