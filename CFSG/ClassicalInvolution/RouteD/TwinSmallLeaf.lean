module

public import CFSG.ClassicalInvolution.RouteD.TwinSmallLeafSpin
public import CFSG.ClassicalInvolution.RouteD.TwinSmallCross
public import CFSG.ClassicalInvolution.RouteD.TwinSmallChain
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallLeaf
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.CurtisTits
open scoped MatrixGroups

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Group

variable {G : Type} [Group G]

theorem commutes_map_conj_iff (x : G) {A B : Subgroup G} :
    Commutes (A.map (MulAut.conj x).toMonoidHom) (B.map (MulAut.conj x).toMonoidHom) ↔
      Commutes A B := by
  refine ⟨fun h a ha b hb => ?_, commutes_map_of_commutes _⟩
  have := h (x * a * x⁻¹) ⟨a, ha, rfl⟩ (x * b * x⁻¹) ⟨b, hb, rfl⟩
  calc a * b = x⁻¹ * (x * a * x⁻¹ * (x * b * x⁻¹)) * x := by group
    _ = x⁻¹ * (x * b * x⁻¹ * (x * a * x⁻¹)) * x := by rw [this]
    _ = b * a := by group

theorem invOf_map_conj {R : Subgroup G} {x r : G}
    (h : InvOf (R.map (MulAut.conj x).toMonoidHom) r) : ∃ r₀, InvOf R r₀ ∧ r = x * r₀ * x⁻¹ := by
  obtain ⟨⟨r₀, hr₀, rfl⟩, hord⟩ := h
  refine ⟨r₀, ⟨hr₀, ?_⟩, rfl⟩
  rw [← hord]
  exact (orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective r₀).symm

theorem invs_commute_map_conj {R R' : Subgroup G} (x : G)
    (h : ∀ r r', InvOf R r → InvOf R' r' → r * r' = r' * r) :
    ∀ r r', InvOf (R.map (MulAut.conj x).toMonoidHom) r →
      InvOf (R'.map (MulAut.conj x).toMonoidHom) r' → r * r' = r' * r := by
  intro r r' hr hr'
  obtain ⟨r₀, hr₀, rfl⟩ := invOf_map_conj hr
  obtain ⟨r₀', hr₀', rfl⟩ := invOf_map_conj hr'
  have := h r₀ r₀' hr₀ hr₀'
  calc x * r₀ * x⁻¹ * (x * r₀' * x⁻¹) = x * (r₀ * r₀') * x⁻¹ := by group
    _ = x * (r₀' * r₀) * x⁻¹ := by rw [this]
    _ = x * r₀' * x⁻¹ * (x * r₀ * x⁻¹) := by group

end Group

section Spin

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V} {𝓕 : Set (Subgroup (spinGroup Q))} {Z' : Subgroup (V ≃ₗ[F] V)}

omit [Finite F] in
theorem map_conj_mem_fund (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) Z')
    {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝓕) (x : spinGroup Q) :
    R.map (MulAut.conj x).toMonoidHom ∈ 𝓕 := by
  obtain ⟨i, hi⟩ := cq.map_mem R hR
  have hg : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have himg : (R.map (MulAut.conj x).toMonoidHom).map (spinAction Q) =
      (R.map (spinAction Q)).map (MulAut.conj (spinAction Q x)).toMonoidHom :=
    CFSG.ClassicalInvolution.ModelFacts.map_conj_map (spinAction Q) x R
  have hL : (R.map (MulAut.conj x).toMonoidHom).map (spinAction Q) ∈ fundSet Q :=
    ⟨_, himg ▸ IsFundamental.conj hg hi⟩
  obtain ⟨R', hR', hR'e⟩ := cq.surj _ hL
  have hperf : ⁅R.map (MulAut.conj x).toMonoidHom, R.map (MulAut.conj x).toMonoidHom⁆ =
      R.map (MulAut.conj x).toMonoidHom := by
    rw [← Subgroup.map_commutator, cq.perf R hR]
  have := CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect (spinAction Q) cq.ker_le
    (cq.perf R' hR') hperf hR'e
  rwa [← this]

end Spin

section Cluster

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem leaf_fixed_cluster (c : TCtx p f .POmegaMinus 7 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaMinus 7 Ω z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember p f β t) (htz : t * z * t⁻¹ = z) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (nd : DNodes p f (7 - 1) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    (x : SpinM p f 7) (tM : Bool)
    (hnode : ∀ a (ha : a ≤ 2), locImg Ω z (nd.J ⟨a + 2, by omega⟩) =
      ((rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) a (a + 1) (by omega)
        (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hMimg : locImg Ω z M =
      ((rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) 4 5 (by omega) (by omega)
        (by omega) true tM).map (MulAut.conj x).toMonoidHom).map c.d.ψ) :
    ∃ R : Subgroup (SpinM p f 7),
      R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)) ∧
      (∃ F_N : OPFrame (QM p f 7), R.map (spinAction (QM p f 7)) = F_N.La.range ∧
        leafV₀ 7 (⟨2, by omega⟩ : Fin (7 - 1)) ∈ F_N.span ∧ ∀ w, planeVec 7 w ∈ F_N.span) ∧
      ∀ y ∈ R.map (MulAut.conj x).toMonoidHom,
        locAut c.hΩ.conjInvariant htz (c.d.ψ y) = c.d.ψ y := by
  classical
  have hΩ := c.hΩ
  have hp2 := c.hp2
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have cq := ctx_centralQuot c (by norm_num : 4 ≤ 7)
  have hKJ : ∀ a (h : a < 7 - 1), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hmemz : ∀ a (h : a < 7 - 1), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  obtain ⟨R, hR, hRF, hcommR, hncommR, hneR, hinvR⟩ := exists_leaf_subgroup (p := p) (f := f) hp2
    c.hq (m := 7) (by norm_num) (i := ⟨2, by omega⟩) (j := ⟨3, by omega⟩)
    (by simp [Fin.ext_iff]) true false
  have hRx : R.map (MulAut.conj x).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)) :=
    map_conj_mem_fund cq hR x
  have hRd : (rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) 2 3 (by omega)
      (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)) :=
    rootSL2_conj_mem_gen (by have := c.hq; omega) cq _ _ _ _ _ _ x
  obtain ⟨N, hNz, hNK, hNQ, hNimg⟩ := c.exists_member_of_fund hRx
  have hNK' : Commutes N K := commutes_symm (c.commutes_K_of_ne hNz hNK)
  have hJ2z := hmemz 2 (by omega) le_rfl
  have hJ4z := hmemz 4 (by omega) (by omega)
  have hMK : Commutes M K := by
    rw [← h0]
    exact nd.commK _
  have hMz : M ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hMΩ c.hz.mem hMK
  have hN2 : Commutes N (nd.J ⟨2, by omega⟩) :=
    (c.commutes_iff_fund hNz hJ2z hRx hNimg (hnode 0 (by omega))).mpr
      (commutes_map_of_commutes _ (hcommR 0 1 (by omega) (by omega) (by omega) (by simp) (by simp)
        (by simp) (by simp) true false))
  have hNM : Commutes N M :=
    (c.commutes_iff_fund hNz hMz hRx hNimg hMimg).mpr
      (commutes_map_of_commutes _ (hcommR 4 5 (by omega) (by omega) (by omega) (by simp) (by simp)
        (by simp) (by simp) true tM))
  obtain ⟨wN, hwN⟩ := hΩ.classical N hNz.1
  have hDne : nd.J ⟨4, by omega⟩ ≠ N := by
    intro e
    rw [← e] at hNimg
    have h1' := (hnode 2 (by omega)).symm.trans hNimg
    have h2' := CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect c.d.ψ c.d.ker_le
      (cq.perf _ hRd) (cq.perf _ hRx) h1'
    exact hneR (Subgroup.map_injective (MulAut.conj x).injective h2').symm
  have hDNn : ¬ Commutes (nd.J ⟨4, by omega⟩) N := by
    intro hc
    have := (c.commutes_iff_fund hJ4z hNz hRd (hnode 2 (by omega)) hNimg).mp hc
    exact hncommR ((commutes_map_conj_iff x).mp this)
  have hinv : ∀ r r', InvOf ((rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) 2 3
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom) r →
      InvOf (R.map (MulAut.conj x).toMonoidHom) r' → r * r' = r' * r :=
    invs_commute_map_conj x fun r r' hr hr' => (hinvR r' r hr' hr).symm
  have hDNw : Commute (nd.w ⟨4, by omega⟩) wN :=
    commute_w_of_model c hJ4z hNz hRd hRx (hnode 2 (by omega)) hNimg (nd.cl _) hwN hinv
  obtain ⟨xM, hxM⟩ := hΩ.classical M hMΩ
  have hF := orthCross_minusDatum (f := f) hp2 (by norm_num : 5 ≤ 7) c.hq
  have a32 : DNodes.Adj (⟨3, by omega⟩ : Fin (7 - 1)) ⟨2, by omega⟩ := by fr_idx
  have hβN : Commutes N β :=
    leaf_commutes_beta_gen (by norm_num : 7 ≤ 7) c hsingle hshape hF nd h0 h1 hMΩ hxM
      (fun a h _ => commutes_symm (nd.commK ⟨a, h⟩)) (nd.mem ⟨3, by omega⟩) (nd.cl _)
      (commutes_symm (nd.commK _)) (commutes_symm (hKJ 3 (by omega) (by omega)))
      (nd.not_commutes_of_adj a32) (nd.ne_J hΩ a32.ne) (nd.commute_w h2 _ _)
      (nd.mem ⟨4, by omega⟩) hNz.1 (nd.cl _) hwN (commutes_symm (nd.commK _)) hNM
      (commutes_symm (hKJ 4 (by omega) (by omega)))
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp)) (by fr_idx)) hNK' hN2 hDne hDNn hDNw
  refine ⟨R, hR, hRF, fun y hy => ?_⟩
  have hNt : N ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hβN n hn t ht.mem)
  exact (locAut_fixed_iff hΩ c.hP1 htz hNz).mp hNt (c.d.ψ y) (by rw [hNimg]; exact ⟨y, hy, rfl⟩)

end Cluster

section StdPairE

variable {p f : ℕ} [Fact p.Prime]

theorem stdPair_E (hp2 : p ≠ 2) (x : SpinM p f 7) :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W
      ((rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) 0 1 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom)
      ((rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) 1 4 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom) := by
  have hirr := minusCoeffs_irr p f
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨W₁, hW₁⟩ := linearBlockStandardPair_minusDatum hirr h2 (by omega : 4 ≤ 7)
    (i := (⟨0, by omega⟩ : Fin (7 - 1))) (j := ⟨1, by omega⟩) (by show 0 + 1 = 1; rfl)
    (by show 1 + 1 < 7 - 1; omega)
  rw [rankOne_minusDatum_of_lt hirr (by show 0 + 1 < 7 - 1; omega),
    rankOne_minusDatum_of_lt hirr (by show 1 + 1 < 7 - 1; omega)] at hW₁
  set Fr := minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2 with hFr
  have hij : (⟨2, by omega⟩ : Fin (7 - 1)) ≠ ⟨4, by omega⟩ := by simp [Fin.ext_iff]
  set w := Fr.longWeyl hij false true with hw
  have hW₂ := CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ w
  have h1 : (rootSL2 Fr 0 1 (by omega) (by omega) (by omega) true false).map
      (MulAut.conj w).toMonoidHom = rootSL2 Fr 0 1 (by omega) (by omega) (by omega) true false := by
    rw [hw, map_conj_longWeyl_rootSL2 Fr hij false true]
    have e1 : (Equiv.swap (⟨2, by omega⟩ : Fin (7 - 1)) ⟨4, by omega⟩ ⟨0, by omega⟩).val = 0 := by
      rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
    have e2 : (Equiv.swap (⟨2, by omega⟩ : Fin (7 - 1)) ⟨4, by omega⟩ ⟨1, by omega⟩).val = 1 := by
      rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
    rw [rootSL2_congr Fr _ _ _ (by omega) (by omega) (by omega) e1 e2,
      longWeylBool_of_ne false true (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]),
      longWeylBool_of_ne false true (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
  have h2' : (rootSL2 Fr 1 2 (by omega) (by omega) (by omega) true false).map
      (MulAut.conj w).toMonoidHom = rootSL2 Fr 1 4 (by omega) (by omega) (by omega) true false := by
    rw [hw, map_conj_longWeyl_rootSL2 Fr hij false true]
    have e1 : (Equiv.swap (⟨2, by omega⟩ : Fin (7 - 1)) ⟨4, by omega⟩ ⟨1, by omega⟩).val = 1 := by
      rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
    have e2 : (Equiv.swap (⟨2, by omega⟩ : Fin (7 - 1)) ⟨4, by omega⟩ ⟨2, by omega⟩).val = 4 := by
      rw [Equiv.swap_apply_left]
    rw [rootSL2_congr Fr _ _ _ (by omega) (by omega) (by omega) e1 e2,
      longWeylBool_of_ne false true (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
    have e3 : longWeylBool (⟨2, by omega⟩ : Fin (7 - 1)) ⟨4, by omega⟩ false true
        ⟨2, by omega⟩ false = false := by simp
    rw [e3]
  rw [h1, h2'] at hW₂
  exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₂ x⟩

end StdPairE

section MSide

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem leaf_fixed_M (c : TCtx p f .POmegaMinus 7 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaMinus 7 Ω z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember p f β t) (htz : t * z * t⁻¹ = z) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (nd : DNodes p f (7 - 1) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    (x : SpinM p f 7) (tM : Bool)
    (hnode : ∀ a (ha : a ≤ 2), locImg Ω z (nd.J ⟨a + 2, by omega⟩) =
      ((rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) a (a + 1) (by omega)
        (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hMimg : locImg Ω z M =
      ((rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) 4 5 (by omega) (by omega)
        (by omega) true tM).map (MulAut.conj x).toMonoidHom).map c.d.ψ) :
    ∃ R : Subgroup (SpinM p f 7),
      R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)) ∧
      (∃ F_N : OPFrame (QM p f 7), R.map (spinAction (QM p f 7)) = F_N.La.range ∧
        leafV₀ 7 (⟨4, by omega⟩ : Fin (7 - 1)) ∈ F_N.span ∧ ∀ w, planeVec 7 w ∈ F_N.span) ∧
      ∀ y ∈ R.map (MulAut.conj x).toMonoidHom,
        locAut c.hΩ.conjInvariant htz (c.d.ψ y) = c.d.ψ y := by
  classical
  have hΩ := c.hΩ
  have hp2 := c.hp2
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have cq := ctx_centralQuot c (by norm_num : 4 ≤ 7)
  have hq4 : 4 ≤ p ^ f := by have := c.hq; omega
  have hKJ : ∀ a (h : a < 7 - 1), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hmemz : ∀ a (h : a < 7 - 1), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hMK : Commutes M K := by
    rw [← h0]
    exact nd.commK _
  have hMz : M ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hMΩ c.hz.mem hMK
  have hJ2z := hmemz 2 (by omega) le_rfl
  have hJ4z := hmemz 4 (by omega) (by omega)
  obtain ⟨R, hR, hRF, hcommR, hncommR, hneR, hinvR⟩ := exists_leaf_subgroup (p := p) (f := f) hp2
    c.hq (m := 7) (by norm_num) (i := ⟨4, by omega⟩) (j := ⟨5, by omega⟩)
    (by simp [Fin.ext_iff]) true tM
  have hRx : R.map (MulAut.conj x).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)) :=
    map_conj_mem_fund cq hR x
  have hRM : (rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) 4 5 (by omega)
      (by omega) (by omega) true tM).map (MulAut.conj x).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)) :=
    rootSL2_conj_mem_gen hq4 cq _ _ _ _ _ _ x
  obtain ⟨N, hNz, hNK, hNQ, hNimg⟩ := c.exists_member_of_fund hRx
  have hNK' : Commutes N K := commutes_symm (c.commutes_K_of_ne hNz hNK)
  have hN2 : Commutes N (nd.J ⟨2, by omega⟩) :=
    (c.commutes_iff_fund hNz hJ2z hRx hNimg (hnode 0 (by omega))).mpr
      (commutes_map_of_commutes _ (hcommR 0 1 (by omega) (by omega) (by omega) (by simp) (by simp)
        (by simp) (by simp) true false))
  have hN4 : Commutes N (nd.J ⟨4, by omega⟩) :=
    (c.commutes_iff_fund hNz hJ4z hRx hNimg (hnode 2 (by omega))).mpr
      (commutes_map_of_commutes _ (hcommR 2 3 (by omega) (by omega) (by omega) (by simp) (by simp)
        (by simp) (by simp) true false))
  have hRE : (rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) 1 4 (by omega)
      (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)) :=
    rootSL2_conj_mem_gen hq4 cq _ _ _ _ _ _ x
  obtain ⟨E, hEz, hEK, hEQ, hEimg⟩ := c.exists_member_of_fund hRE
  have hEK' : Commutes E K := commutes_symm (c.commutes_K_of_ne hEz hEK)
  obtain ⟨wE, hwE⟩ := hΩ.classical E hEz.1
  have hE4 : Commutes E (nd.J ⟨4, by omega⟩) :=
    (c.commutes_iff_fund hEz hJ4z hRE hEimg (hnode 2 (by omega))).mpr
      (commutes_map_of_commutes _ (commutes_rootSL2_disjoint _ (a := 1) (b := 4) (c := 2) (d := 3)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) true false true false))
  obtain ⟨W, hW⟩ := stdPair_E hp2 x
  obtain ⟨W', hW'⟩ := c.stdPair_of_fund hJ2z hEz hW (hnode 0 (by omega)) hEimg
  have hEJ : ¬ Commutes E (nd.J ⟨2, by omega⟩) := fun h =>
    not_commutes_of_linearBlockStandardPair hW' (commutes_symm h)
  have hEne : E ≠ nd.J ⟨2, by omega⟩ := fun e =>
    ne_of_linearBlockStandardPair hW' e.symm
  have hEw : Commute wE (nd.w ⟨2, by omega⟩) :=
    (standardPair_involutions_commute h2 hW' (nd.cl ⟨2, by omega⟩).mem hwE.mem
      (nd.cl ⟨2, by omega⟩).orderOf_eq_two hwE.orderOf_eq_two).symm
  obtain ⟨wN, hwN⟩ := hΩ.classical N hNz.1
  obtain ⟨xM, hxM⟩ := hΩ.classical M hMΩ
  have hDne : M ≠ N := by
    intro e
    rw [← e] at hNimg
    have h1' := hMimg.symm.trans hNimg
    have h2' := CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect c.d.ψ c.d.ker_le
      (cq.perf _ hRM) (cq.perf _ hRx) h1'
    exact hneR (Subgroup.map_injective (MulAut.conj x).injective h2').symm
  have hDNn : ¬ Commutes M N := by
    intro hc
    have := (c.commutes_iff_fund hMz hNz hRM hMimg hNimg).mp hc
    exact hncommR ((commutes_map_conj_iff x).mp this)
  have hinv : ∀ r r', InvOf ((rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) 4 5
      (by omega) (by omega) (by omega) true tM).map (MulAut.conj x).toMonoidHom) r →
      InvOf (R.map (MulAut.conj x).toMonoidHom) r' → r * r' = r' * r :=
    invs_commute_map_conj x fun r r' hr hr' => (hinvR r' r hr' hr).symm
  have hDNw : Commute xM wN := commute_w_of_model c hMz hNz hRM hRx hMimg hNimg hxM hwN hinv
  have hF := orthCross_minusDatum (f := f) hp2 (by norm_num : 5 ≤ 7) c.hq
  have hβN : Commutes N β :=
    leaf_commutes_beta_gen (by norm_num : 7 ≤ 7) c hsingle hshape hF nd h0 h1 (nd.mem ⟨4, by omega⟩)
      (nd.cl ⟨4, by omega⟩)
      (fun a h ha => nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp; omega)) (by fr_idx))
      hEz.1 hwE hE4 hEK' hEJ hEne hEw hMΩ hNz.1 hxM hwN (nd.commK _) hN4 hMK (nd.commK _) hNK'
      hN2 hDne hDNn hDNw
  refine ⟨R, hR, hRF, fun y hy => ?_⟩
  have hNt : N ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hβN n hn t ht.mem)
  exact (locAut_fixed_iff hΩ c.hP1 htz hNz).mp hNt (c.d.ψ y) (by rw [hNimg]; exact ⟨y, hy, rfl⟩)

end MSide

end CFSG.ClassicalInvolution.RouteD.TwinSmall
