module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightThree
public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightIdx
public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightTV
public import CFSG.CGT.PushingUpLit.EightOneWindowBasic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open CFSG.Open (IsElemAbelian)
open CFSG.ComponentClassification.OutcomeLocal (IsF2Transvection)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem eight_alt_normal {Y R : Subgroup G} {T : Sylow 2 G} (h : EightCtx Y T R) {a : ℕ}
    (ha : 1 ≤ a) {φ : (↥Y ⧸ pCore 2 ↥Y) ≃* alternatingGroup (Fin (2 * a + 1))}
    (hnat : IsNaturalAltModuleWith ↥Y a φ) : Y.Normal := by
  classical
  obtain ⟨A, hA, hnot⟩ := h.exists_isMax_not_le
  obtain ⟨β, Φ, hequiv, hΦY, ⟨t, htA, i0, j0, hij0, hΦt⟩, hVeq, hwt⟩ :=
    exists_altPkg' h ha hnat hA hnot
  have h3 : 3 ≤ 2 * a + 1 := by omega
  have hodd : Odd (2 * a + 1) := ⟨a, rfl⟩
  have hVn : (omegaOneCenterIn R).Normal := h.V_normal
  have hJN := h.jIn_le_normalizer
  have hY1N : Y ⊔ jIn (T : Subgroup G) ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le Subgroup.le_normalizer hJN
  have hC : Y ⊓ Subgroup.centralizer (blockU Y : Set G) = oTwoIn Y :=
    inf_centralizer_blockU_eq h.hY.1 h3 hnat
  have hΦ1 : ∀ g : ↥(Subgroup.normalizer (Y : Set G)), Φ g = 1 →
      (g : G) ∈ Subgroup.centralizer (blockU Y : Set G) := fun g hg =>
    mem_centralizer_blockU_of_eq_one β Φ hequiv hg
  have hOR : oTwoIn Y ≤ R := h.le_R_of_le_centralizerModCore
    (ThreeFromEight.isPGroup_oTwoIn Y) (EightOneWindow.oTwoIn_le_centralizerModCore Y)
  have hJ2 : IsPGroup 2 ↥(jIn (T : Subgroup G)) := T.isPGroup'.to_le (jIn_le _)
  have hK : ∀ (g : G) (hg : g ∈ Y ⊔ jIn (T : Subgroup G)),
      Φ ⟨g, hY1N hg⟩ = 1 → g ∈ R := by
    intro g hg hΦg
    have hgN : g ∈ Subgroup.normalizer (Y : Set G) := hY1N hg
    have hgU := hΦ1 ⟨g, hgN⟩ hΦg
    have hgC : g ∈ centralizerModCore Y :=
      EightCtx.mem_centralizerModCore_of_centralizer_blockU hC hgN hgU
    obtain ⟨k, hk⟩ := exists_pow_mem_sup hJ2 hJN hg
    have hkC : g ^ 2 ^ k ∈ Subgroup.centralizer (blockU Y : Set G) :=
      Subgroup.pow_mem _ hgU _
    have hkR : g ^ 2 ^ k ∈ R := by
      have : g ^ 2 ^ k ∈ oTwoIn Y := by
        rw [← hC]
        exact ⟨hk, hkC⟩
      exact hOR this
    have hRn := h.hRn
    refine mem_of_pow_mem_of_commutator_mem h.hNo h.hR (fun y hy => ?_) hkR
    exact hOR (hgC.2 y hy)
  have hCUV : Subgroup.centralizer (omegaOneCenterIn R : Set G) ≤
      Subgroup.centralizer (blockU Y : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h.blockU_le_V)
  have hΦ1' : ∀ g : ↥(Subgroup.normalizer (Y : Set G)),
      (g : G) ∈ Subgroup.centralizer (blockU Y : Set G) → Φ g = 1 := fun g hg =>
    eq_one_of_mem_centralizer_blockU h3 β Φ hequiv hg
  set Y1 : Subgroup G := Y ⊔ jIn (T : Subgroup G) with hY1
  have hY1V : Y1 ≤ Subgroup.normalizer (omegaOneCenterIn R : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  let Φ1 : ↥Y1 →* Equiv.Perm (Fin (2 * a + 1)) := Φ.comp (Subgroup.inclusion hY1N)
  have hΦ1s : Function.Surjective Φ1 := by
    have hY1le : Y ≤ Y1 := le_sup_left
    have hAalt : ∀ π : Equiv.Perm (Fin (2 * a + 1)), π ∈ alternatingGroup (Fin (2 * a + 1)) →
        π ∈ Φ1.range := by
      intro π hπ
      obtain ⟨y, hy⟩ := hΦY π hπ
      exact ⟨⟨(y : G), hY1le y.2⟩, hy⟩
    have hAJ : A ≤ jIn (T : Subgroup G) := by
      rw [jIn_eq_thompsonJ]
      exact le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) A hA
    have htY1 : t ∈ Y1 := (le_sup_right : jIn (T : Subgroup G) ≤ Y1) (hAJ htA)
    have hs : Equiv.swap i0 j0 ∈ Φ1.range := ⟨⟨t, htY1⟩, hΦt⟩
    intro π
    by_cases hπ : π ∈ alternatingGroup (Fin (2 * a + 1))
    · exact hAalt π hπ
    · have hπs : π * Equiv.swap i0 j0 ∈ alternatingGroup (Fin (2 * a + 1)) := by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij0]
        have : Equiv.Perm.sign π = -1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | h1
          · exact absurd ((Equiv.Perm.mem_alternatingGroup).2 h1) hπ
          · exact h1
        rw [this]
        decide
      have h1 := hAalt _ hπs
      have : π = (π * Equiv.swap i0 j0) * Equiv.swap i0 j0 := by
        rw [mul_assoc, Equiv.swap_mul_self, mul_one]
      rw [this]
      exact Φ1.range.mul_mem h1 hs
  have hΦ1k : Φ1.ker = (Y1 ⊓ Subgroup.centralizer (omegaOneCenterIn R : Set G)).subgroupOf Y1 := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      refine ⟨g.2, ?_⟩
      rw [h.hC]
      exact hK (g : G) g.2 hg
    · rintro ⟨-, hgC⟩
      exact hΦ1' ⟨(g : G), hY1N g.2⟩ (hCUV hgC)
  obtain ⟨θ1, hθ1⟩ := exists_natIso hY1V Φ1 hΦ1s hΦ1k
  have hV := isElemAbelian_omegaOneCenterIn R
  let _ : CommGroup ↥(omegaOneCenterIn R) := commGroupOfElemAbelian hV
  have _ : ElemAbelianTwo ↥(omegaOneCenterIn R) :=
    ⟨fun w => Subtype.ext (by simpa using hV.2 w w.2)⟩
  let σ : Equiv.Perm (Fin (2 * a + 1)) →* MulAut ↥(omegaOneCenterIn R) :=
    (autOn Y1 (omegaOneCenterIn R)).subtype.comp θ1.symm.toMonoidHom
  have hσinj : Function.Injective σ :=
    Subtype.val_injective.comp θ1.symm.injective
  have hσG : ∀ s, σ s ∈ autOn (⊤ : Subgroup G) (omegaOneCenterIn R) := by
    intro s
    obtain ⟨x, -, hx⟩ := mem_autOn_iff.mp (θ1.symm s).2
    exact mem_autOn_iff.mpr ⟨x, Subgroup.mem_top _, hx⟩
  have htY1 : t ∈ Y1 := by
    have hAJ : A ≤ jIn (T : Subgroup G) := by
      rw [jIn_eq_thompsonJ]
      exact le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) A hA
    exact (le_sup_right : jIn (T : Subgroup G) ≤ Y1) (hAJ htA)
  have htN : t ∈ Subgroup.normalizer (Y : Set G) := hY1N htY1
  have hσt : σ (Equiv.swap i0 j0) =
      conjAct (omegaOneCenterIn R) ⟨t, hY1V htY1⟩ := by
    have h1 : θ1 (actOnRange (omegaOneCenterIn R) Y1 hY1V ⟨t, htY1⟩) = Equiv.swap i0 j0 := by
      rw [hθ1]
      exact hΦt
    have h2 : θ1.symm (Equiv.swap i0 j0) = actOnRange (omegaOneCenterIn R) Y1 hY1V ⟨t, htY1⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact h1.symm
    show ((θ1.symm (Equiv.swap i0 j0) : ↥(autOn Y1 (omegaOneCenterIn R))) :
      MulAut ↥(omegaOneCenterIn R)) = _
    rw [h2]
    rfl
  have hcardU2 : Nat.card ↥(blockU Y) =
      2 * Nat.card ↥(blockU Y ⊓ Subgroup.centralizer ({t} : Set G)) := by
    have h1 := card_coreMod_eq_two_mul_fix_swap hij0 h3
    have h2 := card_fixU_eq β Φ hequiv ⟨t, htN⟩
    rw [hΦt] at h2
    have h3' : Nat.card ↥(blockU Y) = Nat.card ↥(coreMod (2 * a + 1)) := Nat.card_congr β.toEquiv
    rw [h3', h1, ← h2]
  have hVindex : Nat.card ↥(omegaOneCenterIn R) =
      2 * Nat.card ↥(omegaOneCenterIn R ⊓ Subgroup.centralizer ({t} : Set G)) := by
    have e := card_index_transfer hV h.blockU_le_V htA hVeq
    have hpos : 0 < Nat.card ↥(blockU Y ⊓ Subgroup.centralizer ({t} : Set G)) := Nat.card_pos
    rw [hcardU2] at e
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card ↥(omegaOneCenterIn R) * Nat.card ↥(blockU Y ⊓ Subgroup.centralizer ({t} : Set G))
        = 2 * Nat.card ↥(blockU Y ⊓ Subgroup.centralizer ({t} : Set G)) *
          Nat.card ↥(omegaOneCenterIn R ⊓ Subgroup.centralizer ({t} : Set G)) := e
      _ = _ := by ring
  have hfixmap : (fixSub (conjAct (omegaOneCenterIn R) ⟨t, hY1V htY1⟩)).map
      (omegaOneCenterIn R).subtype =
      omegaOneCenterIn R ⊓ Subgroup.centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [Set.mem_singleton_iff.mp hy]
      have h1 := congrArg (fun z : ↥(omegaOneCenterIn R) => (z : G)) (mem_fixSub.mp hw)
      have h2 : (t : G) * w * (t : G)⁻¹ = w := h1
      calc t * (w : G) = (t * w * t⁻¹) * t := by group
        _ = w * t := by rw [h2]
    · rintro ⟨hxV, hxt⟩
      refine ⟨⟨x, hxV⟩, mem_fixSub.mpr (Subtype.ext ?_), rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hxt t (Set.mem_singleton t)
      show t * x * t⁻¹ = x
      calc t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [h1]
        _ = x := by group
  have htvaut : Nat.card ↥(omegaOneCenterIn R) =
      2 * Nat.card ↥(fixSub (conjAct (omegaOneCenterIn R) ⟨t, hY1V htY1⟩)) := by
    rw [hVindex, ← hfixmap, Subgroup.card_map_of_injective (omegaOneCenterIn R).subtype_injective]
  have htv : IsF2Transvection (autGL (σ (Equiv.swap i0 j0))) := by
    rw [hσt]
    exact isF2Transvection_autGL _ htvaut
  have hNV : ∀ x : G, x ∈ Subgroup.normalizer (omegaOneCenterIn R : Set G) := fun x => by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  have hTopN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (omegaOneCenterIn R : Set G) := by
    rw [Subgroup.normalizer_eq_top]
  set Gb : Subgroup (MulAut ↥(omegaOneCenterIn R)) := autOn (⊤ : Subgroup G) (omegaOneCenterIn R)
    with hGb
  let ρG : G →* ↥Gb := (actOnRange (omegaOneCenterIn R) ⊤ hTopN).comp
    (Subgroup.topEquiv (G := G)).symm.toMonoidHom
  have hρGs : Function.Surjective ρG :=
    (actOnRange_surjective _ _ hTopN).comp (Subgroup.topEquiv (G := G)).symm.surjective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Tb : Sylow 2 ↥Gb := Sylow.mapSurjective hρGs T
  have hVc : ∀ v ∈ omegaOneCenterIn R, ∀ r ∈ R, v * r = r * v := fun v hv r hr =>
    ((mem_omegaOneCenterIn_iff.mp hv).2.1 r hr).symm
  have hD : ∀ g ∈ Gb, g * σ (Equiv.swap i0 j0) * g⁻¹ ∈ (Tb : Subgroup ↥Gb).map Gb.subtype →
      ∃ i j, i ≠ j ∧ g * σ (Equiv.swap i0 j0) * g⁻¹ = σ (Equiv.swap i j) := by
    intro g hg hmem
    obtain ⟨g₀, -, rfl⟩ := mem_autOn_iff.mp hg
    have hVnormal := hVn
    have hRnormal := h.hRn
    have huN : (g₀ : G) * t * (g₀ : G)⁻¹ ∈ Subgroup.normalizer (omegaOneCenterIn R : Set G) :=
      hNV _
    have hconj : conjAct (omegaOneCenterIn R) g₀ * σ (Equiv.swap i0 j0) *
        (conjAct (omegaOneCenterIn R) g₀)⁻¹ =
        conjAct (omegaOneCenterIn R) ⟨(g₀ : G) * t * (g₀ : G)⁻¹, huN⟩ := by
      rw [hσt, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hconj] at hmem ⊢
    have huT : (g₀ : G) * t * (g₀ : G)⁻¹ ∈ (T : Subgroup G) := by
      obtain ⟨τ', hτ'T, hτ'⟩ := hmem
      have hτ'T' : τ' ∈ (T : Subgroup G).map ρG := by
        have : (Tb : Subgroup ↥Gb) = (T : Subgroup G).map ρG := Sylow.coe_mapSurjective hρGs T
        rw [← this]
        exact hτ'T
      obtain ⟨τ, hτT, rfl⟩ := hτ'T'
      have h1 : conjAct (omegaOneCenterIn R) ⟨τ, hTopN (Subgroup.mem_top τ)⟩ =
          conjAct (omegaOneCenterIn R) ⟨(g₀ : G) * t * (g₀ : G)⁻¹, huN⟩ := hτ'
      have h2 : conjAct (omegaOneCenterIn R)
          (⟨τ, hTopN (Subgroup.mem_top τ)⟩⁻¹ * ⟨(g₀ : G) * t * (g₀ : G)⁻¹, huN⟩) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      have h3 := (conjAct_eq_one_iff (omegaOneCenterIn R) _).mp h2
      have h4 : τ⁻¹ * ((g₀ : G) * t * (g₀ : G)⁻¹) ∈ R := by
        rw [h.hC] at h3
        exact h3
      have : (g₀ : G) * t * (g₀ : G)⁻¹ = τ * (τ⁻¹ * ((g₀ : G) * t * (g₀ : G)⁻¹)) := by group
      rw [this]
      exact (T : Subgroup G).mul_mem hτT (h.R_le_T h4)
    obtain ⟨E, hE, huE⟩ := exists_isMax_mem_of_conj_transvection (V := omegaOneCenterIn R) (R := R)
      (T := (T : Subgroup G)) (A := A) hV (omegaOneCenterIn_le R) hVc h.hC h.R_le_T hA hwt htA
      hVindex huT
    have hEJ : E ≤ jIn (T : Subgroup G) := by
      rw [jIn_eq_thompsonJ]
      exact le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) E hE
    have hu1 : (g₀ : G) * t * (g₀ : G)⁻¹ ∈ Y1 :=
      (le_sup_right : jIn (T : Subgroup G) ≤ Y1) (hEJ huE)
    have huN' : (g₀ : G) * t * (g₀ : G)⁻¹ ∈ Subgroup.normalizer (Y : Set G) := hY1N hu1
    have hxmem : conjAct (omegaOneCenterIn R) ⟨(g₀ : G) * t * (g₀ : G)⁻¹, huN⟩ ∈
        autOn Y1 (omegaOneCenterIn R) := mem_autOn_iff.mpr ⟨⟨_, huN⟩, hu1, rfl⟩
    set π : Equiv.Perm (Fin (2 * a + 1)) := θ1 ⟨_, hxmem⟩ with hπ
    have hσπ : σ π = conjAct (omegaOneCenterIn R) ⟨(g₀ : G) * t * (g₀ : G)⁻¹, huN⟩ := by
      show ((θ1.symm (θ1 ⟨_, hxmem⟩) : ↥(autOn Y1 (omegaOneCenterIn R))) :
        MulAut ↥(omegaOneCenterIn R)) = _
      rw [MulEquiv.symm_apply_apply]
    have hπΦ : π = Φ ⟨(g₀ : G) * t * (g₀ : G)⁻¹, huN'⟩ := by
      have h1 : actOnRange (omegaOneCenterIn R) Y1 hY1V ⟨(g₀ : G) * t * (g₀ : G)⁻¹, hu1⟩ =
          ⟨conjAct (omegaOneCenterIn R) ⟨(g₀ : G) * t * (g₀ : G)⁻¹, huN⟩, hxmem⟩ := rfl
      rw [hπ, ← h1, hθ1]
      rfl
    have hVu : Nat.card ↥(omegaOneCenterIn R) = 2 * Nat.card ↥(omegaOneCenterIn R ⊓
        Subgroup.centralizer ({(g₀ : G) * t * (g₀ : G)⁻¹} : Set G)) := by
      rw [card_inf_centralizer_conj]
      exact hVindex
    have hUidx := card_le_two_mul_of_index hV h.blockU_le_V hVu
    have hΔ : Nat.card ↥(coreMod (2 * a + 1)) ≤ 2 * Nat.card ↥(fixSub (coreAct (2 * a + 1) π)) := by
      have e1 := card_fixU_eq β Φ hequiv ⟨(g₀ : G) * t * (g₀ : G)⁻¹, huN'⟩
      rw [← hπΦ] at e1
      have e2 : Nat.card ↥(blockU Y) = Nat.card ↥(coreMod (2 * a + 1)) :=
        Nat.card_congr β.toEquiv
      rw [← e1, ← e2]
      exact hUidx
    have hπ1 : π ≠ 1 := by
      intro hπ1
      have huR : (g₀ : G) * t * (g₀ : G)⁻¹ ∈ R := hK _ hu1 (by rw [← hπΦ]; exact hπ1)
      have huC : (g₀ : G) * t * (g₀ : G)⁻¹ ∈ Subgroup.centralizer (omegaOneCenterIn R : Set G) := by
        rw [h.hC]
        exact huR
      have hfull : omegaOneCenterIn R ⊓
          Subgroup.centralizer ({(g₀ : G) * t * (g₀ : G)⁻¹} : Set G) = omegaOneCenterIn R := by
        refine inf_eq_left.mpr fun v hv => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
        rw [Set.mem_singleton_iff.mp hy]
        exact (Subgroup.mem_centralizer_iff.mp huC v hv).symm
      rw [hfull] at hVu
      have := Nat.card_pos (α := ↥(omegaOneCenterIn R))
      omega
    obtain ⟨i, j, hij, hπij⟩ := isSwap_of_card_le_two_mul_fix hodd hπ1 hΔ
    refine ⟨i, j, hij, ?_⟩
    rw [← hσπ, hπij]
  have hfin := twoFive_aut σ hσinj hσG hij0 htv Tb hD
  have hD2 : IsPGroup 2 ↥(jIn (T : Subgroup G) ⊔ R) :=
    T.isPGroup'.to_le (sup_le (jIn_le _) h.R_le_T)
  have hDY : jIn (T : Subgroup G) ⊔ R ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le hJN h.R_le_normalizer_Y
  refine ⟨fun y hy g₀ => ?_⟩
  have hg₀ : g₀ ∈ Subgroup.normalizer (Y : Set G) := by
    refine mem_normalizer_of_conj_le_sup h.hNo hD2 hDY (fun y' hy' => ?_)
    have hy'1 : y' ∈ Y1 := (le_sup_left : Y ≤ Y1) hy'
    have hmemσ : conjAct (omegaOneCenterIn R) ⟨y', hNV y'⟩ ∈ σ.range := by
      refine ⟨θ1 ⟨conjAct (omegaOneCenterIn R) ⟨y', hNV y'⟩, mem_autOn_iff.mpr ⟨⟨y', hNV y'⟩, hy'1, rfl⟩⟩, ?_⟩
      show ((θ1.symm (θ1 ⟨_, _⟩) : ↥(autOn Y1 (omegaOneCenterIn R))) : MulAut ↥(omegaOneCenterIn R)) = _
      rw [MulEquiv.symm_apply_apply]
    have hĝ : conjAct (omegaOneCenterIn R) ⟨g₀, hNV g₀⟩ ∈ Gb :=
      mem_autOn_iff.mpr ⟨⟨g₀, hNV g₀⟩, Subgroup.mem_top _, rfl⟩
    obtain ⟨π, hπ⟩ := hfin _ hĝ _ hmemσ
    obtain ⟨x, hxY1, hx⟩ := mem_autOn_iff.mp (θ1.symm π).2
    have hxσ : conjAct (omegaOneCenterIn R) x =
        conjAct (omegaOneCenterIn R) ⟨g₀, hNV g₀⟩ * conjAct (omegaOneCenterIn R) ⟨y', hNV y'⟩ *
          (conjAct (omegaOneCenterIn R) ⟨g₀, hNV g₀⟩)⁻¹ := by
      rw [← hπ]
      exact hx
    have h1 : conjAct (omegaOneCenterIn R) (x⁻¹ * ⟨g₀ * y' * g₀⁻¹, hNV _⟩) = 1 := by
      have : (⟨g₀ * y' * g₀⁻¹, hNV _⟩ : ↥(Subgroup.normalizer (omegaOneCenterIn R : Set G))) =
          ⟨g₀, hNV g₀⟩ * ⟨y', hNV y'⟩ * (⟨g₀, hNV g₀⟩)⁻¹ := rfl
      rw [map_mul, map_inv, this, map_mul, map_mul, map_inv, ← hxσ, inv_mul_cancel]
    have h2 := (conjAct_eq_one_iff (omegaOneCenterIn R) _).mp h1
    have h3 : (x : G)⁻¹ * (g₀ * y' * g₀⁻¹) ∈ R := by
      rw [h.hC] at h2
      exact h2
    have h4 : g₀ * y' * g₀⁻¹ = (x : G) * ((x : G)⁻¹ * (g₀ * y' * g₀⁻¹)) := by group
    rw [h4]
    refine Subgroup.mul_mem _ ?_ ?_
    · have : (x : G) ∈ Y ⊔ jIn (T : Subgroup G) := hxY1
      exact (sup_le le_sup_left (le_sup_left.trans le_sup_right) : Y ⊔ jIn (T : Subgroup G) ≤ Y ⊔ (jIn (T : Subgroup G) ⊔ R)) this
    · exact (le_sup_right : jIn (T : Subgroup G) ⊔ R ≤ Y ⊔ (jIn (T : Subgroup G) ⊔ R))
        (Subgroup.mem_sup_right h3)
  exact (Subgroup.mem_normalizer_iff.mp hg₀ y).mp hy

end CFSG.CGT.PushingUpLit.CGT6
