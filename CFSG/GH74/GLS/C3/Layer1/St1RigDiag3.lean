module

public import CFSG.GH74.GLS.C3.Layer1.St1RigDiag

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpRigid

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.C3.Layer1.PumpCalc
open scoped commutatorElement

section General

variable {Y : Type} [Group Y] [Finite Y]

theorem perfect_le_twoResidual {P A : Subgroup Y} (hPA : P ≤ A) (hP : Group.IsPerfect ↥P)
    {p : Y} (hp : p ∈ P) : p ∈ (TwoResidual.subgroup ↥A).map A.subtype := by
  set N := TwoResidual.subgroup ↥A with hN
  have hchar : N.Characteristic := TwoResidual.characteristic ↥A
  have hNnormal : N.Normal := Subgroup.normal_of_characteristic N
  have hodd : Odd (Nat.card (↥A ⧸ N)) := by
    have := TwoResidual.odd_index ↥A
    rwa [Subgroup.index, ← hN] at this
  have hsolv : Group.IsSolvable (↥A ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hf : (QuotientGroup.mk' N).comp (Subgroup.inclusion hPA) = 1 :=
    SolvableKernelContainment.hom_eq_one _
  have h1 : (Subgroup.inclusion hPA ⟨p, hp⟩ : ↥A) ∈ N := by
    have := congrArg (fun f => f ⟨p, hp⟩) hf
    simpa using this
  exact ⟨_, h1, rfl⟩

theorem le_of_perfect_map_le {P M : Subgroup Y} (hP : Group.IsPerfect ↥P)
    (hM : TwoComponents.IsTwoComponent M) (h : P.map (barMk Y) ≤ M.map (barMk Y)) : P ≤ M := by
  have hPA : P ≤ (M.map (barMk Y)).comap (barMk Y) := Subgroup.map_le_iff_le_comap.mp h
  have hres := TwoComponentSubnormal.ambient_residual_preimage (barMk Y) barMk_surjective
    odd_card_ker_barMk M hM
  intro p hp
  rw [← hres]
  exact perfect_le_twoResidual hPA hP hp

end General

section General2

variable {G : Type} [Group G] [Finite G]

theorem le_of_forall_two_elt {X Θ A : Subgroup G} (hΘ : IsPCompIn 2 X Θ)
    (h : ∀ z ∈ Θ, (∃ n : ℕ, z ^ (2 ^ n) = 1) → z ∈ A) : Θ ≤ A := by
  have hres : TwoResidual.subgroup ↥(Θ.subgroupOf X) = ⊤ :=
    TwoComponentConvention.residual_eq_top_of_twoComponent (isPCompIn_two_iff.mp hΘ).2
  let W : Subgroup ↥(Θ.subgroupOf X) := (A.subgroupOf X).comap (Θ.subgroupOf X).subtype
  have hW : TwoResidual.subgroup ↥(Θ.subgroupOf X) ≤ W := by
    refine sSup_le fun P hP => ?_
    intro p hp
    obtain ⟨n, hn⟩ := hP ⟨p, hp⟩
    have hz : (((p : ↥(Θ.subgroupOf X)) : ↥X) : G) ∈ Θ := Subgroup.mem_subgroupOf.mp p.2
    have h1 : (((p : ↥(Θ.subgroupOf X)) : ↥X) : G) ^ (2 ^ n) = 1 := by
      have := congrArg (fun q : ↥P => (((q : ↥(Θ.subgroupOf X)) : ↥X) : G)) hn
      simpa using this
    exact Subgroup.mem_subgroupOf.mpr (h _ hz ⟨n, h1⟩)
  intro θ hθ
  have h2 : (⟨⟨θ, hΘ.1 hθ⟩, Subgroup.mem_subgroupOf.mpr hθ⟩ : ↥(Θ.subgroupOf X)) ∈
      TwoResidual.subgroup ↥(Θ.subgroupOf X) := by
    rw [hres]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp (hW h2)

omit [Finite G] in
theorem mem_pPrimeCoreOf_of_barMk_eq_one' {Λ Y' : Subgroup G} [Finite ↥Y'] (hΛY : Λ ≤ Y') {k : G}
    (hk : k ∈ Λ) (hkY : k ∈ Y') (h : barMk ↥Y' ⟨k, hkY⟩ = 1) : k ∈ pPrimeCoreOf 2 Λ := by
  have : Finite ↥Λ := Finite.of_injective (Subgroup.inclusion hΛY) (Subgroup.inclusion_injective hΛY)
  set N : Subgroup ↥Λ := (barMk ↥Y').ker.comap (Subgroup.inclusion hΛY) with hN
  have hNn : N.Normal := (MonoidHom.normal_ker (barMk ↥Y')).comap _
  have hodd : Odd (Nat.card N) := (odd_card_ker_barMk (Y := ↥Y')).of_dvd_nat
    (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hΛY))
  have hle : N ≤ pPrimeCore 2 ↥Λ := le_sSup ⟨hNn, Nat.coprime_two_left.mpr hodd⟩
  have hmem : (⟨k, hk⟩ : ↥Λ) ∈ N := by
    rw [hN, Subgroup.mem_comap, MonoidHom.mem_ker]
    exact h
  exact ⟨⟨k, hk⟩, hle hmem, rfl⟩

end General2

section Pump

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_lam {z u q : G} {J Λ : Subgroup G} (hΛ : IsLam z u J Λ)
    (hq : q ∈ centralizer ({u} : Set G)) (hqJ : q ∈ normalizer (J : Set G)) :
    q ∈ normalizer (Λ : Set G) := by
  have hqX : q ∈ normalizer ((J ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) :=
    TwoThin.mem_normalizer_inf hqJ (Subgroup.le_normalizer hq)
  have hqX' : q⁻¹ ∈ normalizer ((J ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) :=
    inv_mem hqX
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact conj_mem_of_unique_isPCompIn hΛ.pc hΛ.uniq hqX ha
  · intro ha
    have := conj_mem_of_unique_isPCompIn hΛ.pc hΛ.uniq hqX' ha
    simpa [mul_assoc] using this

theorem exists_pumpUpLT
    {x : G} {K : Subgroup G} (hP : IsILo 2 x K) {w : G} (hwo : orderOf w = 2)
    (hwC : w ∈ CxK x K) (hR : 3 ≤ pRank 2 ↥(centralizer ({w} : Set G))) :
    ∃ M : Subgroup G, PumpUpLT 2 x K w M := by
  have hxo : orderOf x = 2 := hP.1
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hP.2.2
  have hwx : w ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.mp hwC).1
  have hws : w ∈ centralizerSection K (pPrimeCoreOf 2 K) := (Subgroup.mem_inf.mp hwC).2
  obtain ⟨Λ, hΛ⟩ := exists_isLam (z := x) hwo hKc hws
  have hxY : x ∈ centralizer ({w} : Set G) := mem_centralizer_symm hwx
  set Y' := centralizer ({w} : Set G) with hY'
  have hso : orderOf (⟨x, hxY⟩ : ↥Y') = 2 := orderOf_mk_centralizer hxY hxo
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛ.pcW).1 hxY
  have hΛ2 := isTwoComponent_centralizer_mk hΛ.pcW hxY
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hiff⟩ := pumpupY_structure hso hΛC hΛ2
  have hL2 : TwoComponents.IsTwoComponent L :=
    TwoLayerTransport.ordinary_isTwoComponent_of_corefree oddCore_barQ L
      ((CFSG.isComponent_iff_open L).mp hL)
  obtain ⟨M, hM2, hML⟩ := OddKernelTwoComponents.exists_lift (barMk ↥Y') barMk_surjective
    odd_card_ker_barMk L hL2
  have hMJ : M ≤ pumpupY (Λ.subgroupOf Y') := (hiff M hM2).mpr (Or.inl hML)
  set MG : Subgroup G := M.map Y'.subtype with hMG
  have hMGY : MG ≤ Y' := Subgroup.map_subtype_le M
  have hMGsub : MG.subgroupOf Y' = M :=
    Subgroup.comap_map_eq_self_of_injective Y'.subtype_injective M
  have hMG2 : TwoComponents.IsTwoComponent (MG.subgroupOf Y') := by
    rw [hMGsub]
    exact hM2
  have hJ : pumpUp 2 K w = (pumpupY (Λ.subgroupOf Y')).map Y'.subtype := by
    rw [pumpUp_eq_map_pumpupY, hΛ.layer]
  have hMGJ : MG ≤ pumpUp 2 K w := by
    rw [hJ]
    exact Subgroup.map_mono hMJ
  have hpumpPC : IsPCompIn 2 (pumpUp 2 K w) MG :=
    ⟨hMGJ, (CatalogueBAlternating.pComponent_two_iff _).mpr
      (TwoComponentTransport.restrict_nested MG (pumpUp 2 K w) Y' hMGJ
        (pumpUp_le_centralizer K w) hMG2)⟩
  have hILo : IsILo 2 w MG :=
    ⟨hwo, by simpa [oBound] using hR, isPCompIn_two_iff.mpr ⟨hMGY, hMG2⟩⟩
  exact ⟨MG, hP, hILo, hwx, hws, hpumpPC⟩

end Pump

section Theta

variable {G : Type} [Group G] [Finite G]

namespace DiagData

variable {x t : G} {K K' Λ : Subgroup G} {hxY : x ∈ centralizer ({t} : Set G)}

theorem exists_theta (h : DiagData x t K K' Λ hxY) {w : G} (hwo : orderOf w = 2)
    (hwY : w ∈ centralizer ({t} : Set G)) (hwC : w ∈ CxK x K) :
    ∃ Θ : Subgroup G, IsPCompIn 2 (Λ ⊓ centralizer ({w} : Set G)) Θ ∧
      (∀ z ∈ Λ ⊓ centralizer ({w} : Set G), (∃ n : ℕ, z ^ (2 ^ n) = 1) → z ∈ Θ) ∧
      (∀ k ∈ Λ, ∃ l ∈ Θ, ∃ o ∈ pPrimeCoreOf 2 Λ, k = l * o) := by
  have hΛY : Λ ≤ centralizer ({t} : Set G) := h.lam.le.trans inf_le_right
  have hwK : w ∈ normalizer (K : Set G) := (Subgroup.mem_inf.mp hwC).2.1
  have hwN : w ∈ normalizer (Λ : Set G) := mem_normalizer_lam h.lam hwY hwK
  have hwΛ : w ∈ centralizerSection Λ (pPrimeCoreOf 2 Λ) := by
    refine ⟨hwN, mem_normalizer_pPrimeCoreOf hwN, fun a ha => ?_⟩
    have haY : a ∈ centralizer ({t} : Set G) := hΛY ha
    have hwa : w * a⁻¹ * w⁻¹ ∈ Λ := by
      have := (Subgroup.mem_normalizer_iff.mp hwN (a⁻¹)).mp (inv_mem ha)
      exact this
    have hcΛ : ⁅a, w⁆ ∈ Λ := by
      have : ⁅a, w⁆ = a * (w * a⁻¹ * w⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact mul_mem ha hwa
    have hcY : ⁅a, w⁆ ∈ centralizer ({t} : Set G) := by
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem haY hwY) (inv_mem haY)) (inv_mem hwY)
    refine mem_pPrimeCoreOf_of_barMk_eq_one' (Y' := centralizer ({t} : Set G)) hΛY hcΛ hcY ?_
    have h1 := h.cent w hwY hwC (barMk _ ⟨a, haY⟩) ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have h2 : (⟨⁅a, w⁆, hcY⟩ : ↥(centralizer ({t} : Set G))) =
        ⟨a, haY⟩ * ⟨w, hwY⟩ * ⟨a, haY⟩⁻¹ * ⟨w, hwY⟩⁻¹ := rfl
    rw [h2]
    simp only [map_mul, map_inv]
    change barMk _ ⟨a, haY⟩ * sbar w hwY * (barMk _ ⟨a, haY⟩)⁻¹ * (sbar w hwY)⁻¹ = 1
    generalize barMk ↥(centralizer ({t} : Set G)) ⟨a, haY⟩ = α at h1 ⊢
    generalize sbar w hwY = β at h1 ⊢
    have h3 : β * α = α * β := by
      calc β * α = (β * α * β⁻¹) * β := by group
        _ = α * β := by rw [h1]
    calc α * β * α⁻¹ * β⁻¹ = (β * α) * α⁻¹ * β⁻¹ := by rw [h3]
      _ = 1 := by group
  have hcov := exists_centralizer_mul_pPrimeCore hwΛ hwo
  have hKq : CFSG.IsQuasisimple (↥Λ ⧸ pPrimeCore 2 ↥Λ) := isQuasisimple_hat h.lam.pc
  obtain ⟨Θ, -, hpc, -, -, h2el, hcovΘ⟩ := cover_data (inf_le_left : Λ ⊓ centralizer ({w} : Set G) ≤ Λ)
    hcov hKq
  exact ⟨Θ, hpc, h2el, hcovΘ⟩

end DiagData

end Theta

section Step3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjSub_eq_of_centralizes {Z : Type} [Group Z] (g : Z) (L : Subgroup Z)
    (hg : ∀ v ∈ L, g * v * g⁻¹ = v) : conjSub g L = L := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    have : (MulAut.conj g).toMonoidHom v = v := hg v hv
    rw [this]
    exact hv
  · intro hz
    exact ⟨z, hz, hg z hz⟩

omit [Finite G] in
theorem conjSub_inv_eq_of_centralizes {Z : Type} [Group Z] (g : Z) (L : Subgroup Z)
    (hg : ∀ v ∈ L, g * v * g⁻¹ = v) : conjSub g⁻¹ L = L := by
  have h1 := conjSub_eq_of_centralizes g L hg
  calc conjSub g⁻¹ L = conjSub g⁻¹ (conjSub g L) := by rw [h1]
    _ = L := conjSub_inv_conjSub g L

namespace DiagData

variable {x t : G} {K K' Λ : Subgroup G} {hxY : x ∈ centralizer ({t} : Set G)}

theorem exists_diag_of_mem
    (hILo : IsILo 2 x K) {w : G}
    (hle : ∀ M : Subgroup G, PumpUpLT 2 x K w M → hatCard M ≤ hatCard K)
    (h : DiagData x t K K' Λ hxY) (htC : t ∈ CxK x K) (hwo : orderOf w = 2) (hwC : w ∈ CxK x K)
    (hwt : w ∈ CxK t K') (hRank : 3 ≤ pRank 2 ↥(centralizer ({w} : Set G))) :
    ∃ M : Subgroup G, PumpUpLT 2 x K w M ∧ x ∉ normalizer (M : Set G) := by
  by_contra hno
  have hvert : ∀ M : Subgroup G, PumpUpLT 2 x K w M → x ∈ normalizer (M : Set G) := fun M hM =>
    by_contra fun hx => hno ⟨M, hM, hx⟩
  have hwY : w ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hwt).1
  have hwx : w ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.mp hwC).1
  have htw : t ∈ centralizer ({w} : Set G) := mem_centralizer_symm hwY
  have hxw : x ∈ centralizer ({w} : Set G) := mem_centralizer_symm hwx
  obtain ⟨M₀, hlt₀⟩ := exists_pumpUpLT hILo hwo hwC hRank
  have hxN : x ∈ normalizer (M₀ : Set G) := hvert M₀ hlt₀
  obtain ⟨Λw, hΛw, hM₀c, -, -, hcentw, hcases⟩ := rigid_step hlt₀ hxw (hle M₀ hlt₀)
  have hDw : bar w Λw = bar w M₀ := (hcases.resolve_right (fun hh => hh.1 hxN)).2
  have htCw : t ∈ CxK w M₀ := mem_CxK_of_centralizes hM₀c htw (fun v hv => by
    rw [← hDw] at hv
    exact hcentw t htw htC v hv)
  obtain ⟨Θ, hΘpc, hΘ2, hΘcov⟩ := h.exists_theta hwo hwY hwC
  have hΘX : Θ ≤ Λ ⊓ centralizer ({w} : Set G) := hΘpc.1
  have hΘΛ : Θ ≤ Λ := hΘX.trans inf_le_left
  have hΘw : Θ ≤ centralizer ({w} : Set G) := hΘX.trans inf_le_right
  have hΛK : Λ ≤ K := h.lam.le.trans inf_le_left
  have hΛt : Λ ≤ centralizer ({t} : Set G) := h.lam.le.trans inf_le_right
  have hΘΛw : Θ ≤ Λw := le_of_forall_two_elt hΘpc (fun z hz hz2 =>
    hΛw.twoElt z (Subgroup.mem_inf.mpr ⟨hΛK (hΘΛ hz), hΘw hz⟩) hz2)
  have hΛwM₀ : Λw ≤ M₀ := by
    have hperf : Group.IsPerfect ↥(Λw.subgroupOf (centralizer ({w} : Set G))) :=
      Subgroup.isPerfect_iff.mpr (lam_perfect_Y hΛw)
    have hM2 : TwoComponents.IsTwoComponent (M₀.subgroupOf (centralizer ({w} : Set G))) :=
      (isPCompIn_two_iff.mp hM₀c).2
    have hmap : (Λw.subgroupOf (centralizer ({w} : Set G))).map
        (barMk ↥(centralizer ({w} : Set G))) ≤
        (M₀.subgroupOf (centralizer ({w} : Set G))).map (barMk ↥(centralizer ({w} : Set G))) :=
      hDw.le
    intro a ha
    have haY : a ∈ centralizer ({w} : Set G) :=
      (Subgroup.mem_inf.mp (hΛw.le ha)).2
    have := le_of_perfect_map_le hperf hM2 hmap
      (Subgroup.mem_subgroupOf.mpr ha : (⟨a, haY⟩ : ↥(centralizer ({w} : Set G))) ∈ _)
    exact Subgroup.mem_subgroupOf.mp this
  have hΘM₀ : Θ ≤ M₀ := hΘΛw.trans hΛwM₀
  obtain ⟨Λ', hΛ'⟩ := exists_isLam (z := w) h.hto hM₀c (Subgroup.mem_inf.mp htCw).2
  have hΘΛ' : Θ ≤ Λ' := le_of_forall_two_elt hΘpc (fun z hz hz2 =>
    hΛ'.twoElt z (Subgroup.mem_inf.mpr ⟨hΘM₀ hz, hΛt (hΘΛ hz)⟩) hz2)
  have hD_le : bar t Λ ≤ bar t Λ' := by
    rintro _ ⟨m, hm, rfl⟩
    have hmΛ : (m : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hm
    obtain ⟨l, hl, o, ho, hlo⟩ := hΘcov m hmΛ
    have hoY : o ∈ centralizer ({t} : Set G) := hΛt (pPrimeCoreOf_le Λ ho)
    have hlY : l ∈ centralizer ({t} : Set G) := hΛt (hΘΛ hl)
    refine ⟨⟨l, hlY⟩, Subgroup.mem_subgroupOf.mpr (hΘΛ' hl), ?_⟩
    have h1 : barMk ↥(centralizer ({t} : Set G)) ⟨o, hoY⟩ = 1 := h.ker o hoY ho
    have hm' : m = ⟨l, hlY⟩ * ⟨o, hoY⟩ := Subtype.ext hlo
    rw [hm', map_mul, h1, mul_one]
  set Yt := centralizer ({t} : Set G) with hYt
  have hwo' : orderOf (⟨w, hwY⟩ : ↥Yt) = 2 := orderOf_mk_centralizer hwY hwo
  have hΛ'C := le_centralizer_mk (isPCompIn_two_iff.mp hΛ'.pcW).1 hwY
  have hΛ'2 := isTwoComponent_centralizer_mk hΛ'.pcW hwY
  obtain ⟨-, -, L'', hL'', hcases'', -⟩ := pumpupY_structure hwo' hΛ'C hΛ'2
  have hΛ'le : bar t Λ' ≤ L'' ⊔ conjSub (sbar w hwY)⁻¹ L'' := by
    rcases hcases'' with ⟨hst, hAL⟩ | ⟨-, hAB, hAD⟩
    · exact hAL.trans le_sup_left
    · refine hAD.trans ?_
      rintro _ ⟨b, rfl⟩
      exact swapDiag_mem_sup hAB b
  have hDle'' : bar t Λ ≤ L'' ⊔ conjSub (sbar w hwY)⁻¹ L'' := hD_le.trans hΛ'le
  have hC₂ : CFSG.IsComponent (conjSub (sbar w hwY)⁻¹ L'') := isComponent_conjSub hL'' _
  have hAB' : ⁅conjSub (sbar x hxY)⁻¹ (bar t K'), bar t K'⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact h.hAB
  have h1 := eq_of_diag_le_sup h.isComponent_L₁ hL'' hC₂ h.hAB hDle'' h.hproj₁
  have h2 := eq_of_diag_le_sup h.isComponent_L₂ hL'' hC₂ hAB' hDle'' h.hproj₂
  have hwL₁ : ∀ v ∈ bar t K', sbar w hwY * v * (sbar w hwY)⁻¹ = v :=
    centralizes_of_mem_CxK h.hK'c hwY hwt
  have hwxs : sbar w hwY * sbar x hxY = sbar x hxY * sbar w hwY :=
    sbar_commute hwY hxY (mem_centralizer_singleton_iff.mp hwx)
  have hwL₂ : ∀ v ∈ conjSub (sbar x hxY)⁻¹ (bar t K'),
      sbar w hwY * v * (sbar w hwY)⁻¹ = v := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    have h3 := hwL₁ ℓ hℓ
    have h4 : sbar w hwY * (sbar x hxY)⁻¹ = (sbar x hxY)⁻¹ * sbar w hwY := by
      calc sbar w hwY * (sbar x hxY)⁻¹
          = (sbar x hxY)⁻¹ * (sbar x hxY * sbar w hwY) * (sbar x hxY)⁻¹ := by group
        _ = (sbar x hxY)⁻¹ * (sbar w hwY * sbar x hxY) * (sbar x hxY)⁻¹ := by rw [hwxs]
        _ = (sbar x hxY)⁻¹ * sbar w hwY := by group
    set u := (sbar x hxY)⁻¹ with hu
    set ŵ := sbar w hwY with hŵ
    have hwu : ŵ * u * ŵ⁻¹ = u := by
      calc ŵ * u * ŵ⁻¹ = (u * ŵ) * ŵ⁻¹ := by rw [h4]
        _ = u := by group
    have hwu' : ŵ * u⁻¹ * ŵ⁻¹ = u⁻¹ := by
      have : ŵ * u⁻¹ * ŵ⁻¹ = (ŵ * u * ŵ⁻¹)⁻¹ := by group
      rw [this, hwu]
    change ŵ * (u * ℓ * u⁻¹) * ŵ⁻¹ = u * ℓ * u⁻¹
    calc ŵ * (u * ℓ * u⁻¹) * ŵ⁻¹ = (ŵ * u * ŵ⁻¹) * (ŵ * ℓ * ŵ⁻¹) * (ŵ * u⁻¹ * ŵ⁻¹) := by group
      _ = u * ℓ * u⁻¹ := by rw [hwu, h3, hwu']
  have hst₁ := conjSub_inv_eq_of_centralizes (sbar w hwY) (bar t K') hwL₁
  have hst₂ := conjSub_inv_eq_of_centralizes (sbar w hwY) (conjSub (sbar x hxY)⁻¹ (bar t K')) hwL₂
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact h.ne (h2.trans h1.symm)
  · have e1 : conjSub (sbar w hwY)⁻¹ L'' = bar t K' := by
      rw [← h1]
      exact hst₁
    exact h.ne (h2.trans e1)
  · have e2 : conjSub (sbar w hwY)⁻¹ L'' = conjSub (sbar x hxY)⁻¹ (bar t K') := by
      rw [← h2]
      exact hst₂
    exact h.ne (e2.symm.trans h1.symm)
  · exact h.ne (h2.trans h1.symm)

end DiagData

end Step3

end CFSG.GH74.GLS.C3.Layer1.PumpRigid
