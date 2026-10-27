module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.CGT.PushingUpLit.BHS6.ThreeEightAlt
import CFSG.Quasithin.Background.B5FinPerm
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.Quasithin CFSG.RankThree.PartOne Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)

variable {Ω : Type} [Group Ω]


private theorem actOnRange_ker_pCore_bnalt {B W : Subgroup Ω}
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hker : B ⊓ Subgroup.centralizer (W : Set Ω) = pCoreOf 2 B) :
    (CFSG.CGT.PushingUpLit.BHS6.actOnRange W B hBW).ker = CFSG.pCore 2 ↥B := by
  rw [CFSG.CGT.PushingUpLit.BHS6.ker_actOnRange, hker, CFSG.openPCoreOf_subgroupOf]

private theorem altDn_ker_bnalt (n : ℕ) :
    (FFModel.altDn (2 * n + 1)).ker.subgroupOf (FFModel.altDn (2 * n + 1)).sec = ⊥ := by
  have hodd : Odd (2 * n + 1) := ⟨n, by ring⟩
  have hbot : Subgroup.zpowers (G6.allOnes (2 * n + 1)) ⊓ G6.coreMod (2 * n + 1) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hz, hc⟩
    rcases CFSG.Quasithin.B5FinPerm.mem_zpowers_allOnes_iff.mp hz with h | h
    · exact h
    · exfalso
      change x ∈ G6.coreMod (2 * n + 1) at hc
      rw [G6.mem_coreMod, h] at hc
      have h1 : ∑ i : Fin (2 * n + 1),
          Multiplicative.toAdd (G6.allOnes (2 * n + 1)) i = ((2 * n + 1 : ℕ) : ZMod 2) := by
        simp [G6.allOnes]
      rw [h1, ZMod.natCast_eq_zero_iff_even] at hc
      exact (Nat.not_even_iff_odd.2 hodd) hc
  rw [show (FFModel.altDn (2 * n + 1)).ker = ⊥ from hbot, Subgroup.bot_subgroupOf]

private noncomputable def altDnQuotEquiv_bnalt (n : ℕ) :
    ↥((FFModel.altDn (2 * n + 1)).sec) ⧸
      (FFModel.altDn (2 * n + 1)).ker.subgroupOf (FFModel.altDn (2 * n + 1)).sec ≃*
      ↥((FFModel.altDn (2 * n + 1)).sec) :=
  (QuotientGroup.quotientMulEquivOfEq (altDn_ker_bnalt n)).trans QuotientGroup.quotientBot

private theorem altDnQuotEquiv_bnalt_mk (n : ℕ)
    (x : ↥((FFModel.altDn (2 * n + 1)).sec)) :
    altDnQuotEquiv_bnalt n (QuotientGroup.mk x) = x := rfl

private noncomputable def altDnSecCast_bnalt (n : ℕ) :
    ↥((FFModel.altDn (2 * n + 1)).sec) ≃* ↥(G6.coreMod (2 * n + 1)) :=
  MulEquiv.subgroupCongr rfl

private theorem altDnSecCast_bnalt_apply (n : ℕ)
    (x : ↥((FFModel.altDn (2 * n + 1)).sec)) : altDnSecCast_bnalt n x = x := rfl

open scoped IsMulCommutative in
private theorem map_commV_blockU_bnalt {B W : Subgroup Ω} [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) :
    (commV (autOn B W)).map W.subtype = CFSG.QuasithinUnique.blockU B := by
  rw [show CFSG.QuasithinUnique.blockU B = ⁅W, B⁆ from hU]
  exact AutOn.map_commV_autOn_eq hBW

open scoped IsMulCommutative in
private theorem map_fixV_bnalt {B W : Subgroup Ω} [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω)) :
    (fixV (autOn B W)).map W.subtype = W ⊓ Subgroup.centralizer (B : Set Ω) := by
  rw [AutOn.fixV_autOn_eq hBW, Subgroup.subgroupOf, Subgroup.map_comap_eq,
    Subgroup.range_subtype]

private theorem blockU_le_W_bnalt {B W : Subgroup Ω}
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) : CFSG.QuasithinUnique.blockU B ≤ W := by
  rw [show CFSG.QuasithinUnique.blockU B = ⁅W, B⁆ from hU, Subgroup.commutator_le]
  intro w hw b hb
  rw [commutatorElement_def]
  have hb' : b * w⁻¹ * b⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (hBW hb) w⁻¹).mp (W.inv_mem hw)
  simpa only [mul_assoc] using W.mul_mem hw hb'

open scoped IsMulCommutative in
private theorem map_gomiWXKer_bnalt {B W : Subgroup Ω} [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) :
    (gomiWXKer (autOn B W)).map W.subtype = CFSG.QuasithinUnique.blockZ B := by
  rw [gomiWXKer, Subgroup.map_inf (commV (autOn B W)) (fixV (autOn B W)) W.subtype
      W.subtype_injective, map_commV_blockU_bnalt hBW hU, map_fixV_bnalt hBW,
    show CFSG.QuasithinUnique.blockZ B = CFSG.QuasithinUnique.blockU B ⊓
      Subgroup.centralizer (B : Set Ω) from rfl, ← inf_assoc,
    inf_eq_left.mpr (blockU_le_W_bnalt hBW hU)]

open scoped IsMulCommutative in
private noncomputable def commVEquivBlockU_bnalt {B W : Subgroup Ω} [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) :
    ↥(commV (autOn B W)) ≃* ↥(CFSG.QuasithinUnique.blockU B) :=
  (Subgroup.equivMapOfInjective (commV (autOn B W)) W.subtype W.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_commV_blockU_bnalt hBW hU))

open scoped IsMulCommutative in
private theorem commVEquivBlockU_bnalt_apply {B W : Subgroup Ω} [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) (u : ↥(commV (autOn B W))) :
    ((commVEquivBlockU_bnalt hBW hU u : CFSG.QuasithinUnique.blockU B) : Ω) =
      ((u : W) : Ω) := by
  change ((Subgroup.equivMapOfInjective (commV (autOn B W)) W.subtype W.subtype_injective u :
    (commV (autOn B W)).map W.subtype) : Ω) = ((u : W) : Ω)
  rw [Subgroup.coe_equivMapOfInjective_apply]
  rfl

open scoped IsMulCommutative in
private theorem commVEquivBlockU_bnalt_symm_coe {B W : Subgroup Ω} [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) (x : ↥(CFSG.QuasithinUnique.blockU B)) :
    ((commVEquivBlockU_bnalt hBW hU).symm x : Ω) = (x : Ω) := by
  have h := congrArg (fun z : ↥(CFSG.QuasithinUnique.blockU B) => (z : Ω))
    ((commVEquivBlockU_bnalt hBW hU).apply_symm_apply x)
  rwa [commVEquivBlockU_bnalt_apply hBW hU
    ((commVEquivBlockU_bnalt hBW hU).symm x)] at h

open scoped IsMulCommutative in
private theorem commVEquivBlockU_bnalt_mem_Z_iff {B W : Subgroup Ω} [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) (u : ↥(commV (autOn B W))) :
    (u : W) ∈ gomiWXKer (autOn B W) ↔
      ((commVEquivBlockU_bnalt hBW hU u : CFSG.QuasithinUnique.blockU B) : Ω) ∈
        CFSG.QuasithinUnique.blockZ B := by
  rw [← map_gomiWXKer_bnalt hBW hU]
  rw [show ((commVEquivBlockU_bnalt hBW hU u : CFSG.QuasithinUnique.blockU B) : Ω) =
    W.subtype (u : W) from commVEquivBlockU_bnalt_apply hBW hU u]
  exact (Subgroup.mem_map_iff_mem W.subtype_injective).symm

open scoped IsMulCommutative in
private noncomputable def WV_bnalt (B W : Subgroup Ω) [IsMulCommutative ↥W] : Subgroup W :=
  commV (autOn B W)

open scoped IsMulCommutative in
private noncomputable def altBetaCore_bnalt {B W : Subgroup Ω} [IsMulCommutative ↥W]
    {n : ℕ}
    (β₀ : ↥(commV (autOn B W)) →*
      ↥((FFModel.altDn (2 * n + 1)).sec) ⧸
        (FFModel.altDn (2 * n + 1)).ker.subgroupOf (FFModel.altDn (2 * n + 1)).sec) :
    ↥(commV (autOn B W)) →* ↥(G6.coreMod (2 * n + 1)) :=
  (altDnSecCast_bnalt n).toMonoidHom.comp ((altDnQuotEquiv_bnalt n).toMonoidHom.comp β₀)

open scoped IsMulCommutative in
private theorem altBetaCore_bnalt_apply {B W : Subgroup Ω} [IsMulCommutative ↥W] {n : ℕ}
    (β₀ : ↥(WV_bnalt B W) →*
      ↥((FFModel.altDn (2 * n + 1)).sec) ⧸
        (FFModel.altDn (2 * n + 1)).ker.subgroupOf (FFModel.altDn (2 * n + 1)).sec)
    (x : ↥(WV_bnalt B W)) :
    altBetaCore_bnalt β₀ x =
      altDnSecCast_bnalt n (altDnQuotEquiv_bnalt n (β₀ x)) := rfl

open scoped IsMulCommutative in
private noncomputable def altBeta_bnalt {B W : Subgroup Ω} [IsMulCommutative ↥W]
    {n : ℕ} (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆)
    (β₀ : ↥(commV (autOn B W)) →*
      ↥((FFModel.altDn (2 * n + 1)).sec) ⧸
        (FFModel.altDn (2 * n + 1)).ker.subgroupOf (FFModel.altDn (2 * n + 1)).sec) :
    ↥(CFSG.QuasithinUnique.blockU B) →*
      Multiplicative (CFSG.QuasithinUnique.evenWeight (2 * n + 1)) :=
  (CFSG.CGT.PushingUpLit.BHS6.coreModEvenEquiv (2 * n + 1)).toMonoidHom.comp
    ((altBetaCore_bnalt β₀).comp (commVEquivBlockU_bnalt hBW hU).symm.toMonoidHom)

open scoped IsMulCommutative in
private theorem altBeta_bnalt_apply {B W : Subgroup Ω} [IsMulCommutative ↥W] {n : ℕ}
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω)) (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆)
    (β₀ : ↥(WV_bnalt B W) →*
      ↥((FFModel.altDn (2 * n + 1)).sec) ⧸
        (FFModel.altDn (2 * n + 1)).ker.subgroupOf (FFModel.altDn (2 * n + 1)).sec)
    (x : ↥(CFSG.QuasithinUnique.blockU B)) :
    altBeta_bnalt hBW hU β₀ x =
      (CFSG.CGT.PushingUpLit.BHS6.coreModEvenEquiv (2 * n + 1))
        (altBetaCore_bnalt β₀ ((commVEquivBlockU_bnalt hBW hU).symm x)) := rfl

private theorem toAdd_coreModEvenEquiv_bnalt {n : ℕ} (x : ↥(G6.coreMod (2 * n + 1))) :
    ((Multiplicative.toAdd (CFSG.CGT.PushingUpLit.BHS6.coreModEvenEquiv (2 * n + 1) x) :
        CFSG.QuasithinUnique.evenWeight (2 * n + 1)) : Fin (2 * n + 1) → ZMod 2) =
      Multiplicative.toAdd (x : G6.PermMod (2 * n + 1)) := rfl

open scoped IsMulCommutative in
private theorem altBetaCore_bnalt_surjective {B W : Subgroup Ω} [IsMulCommutative ↥W]
    {n : ℕ}
    (β₀ : ↥(commV (autOn B W)) →*
      ↥((FFModel.altDn (2 * n + 1)).sec) ⧸
        (FFModel.altDn (2 * n + 1)).ker.subgroupOf (FFModel.altDn (2 * n + 1)).sec)
    (hβ₀s : Function.Surjective β₀) :
    Function.Surjective (altBetaCore_bnalt β₀) :=
  (altDnSecCast_bnalt n).surjective.comp ((altDnQuotEquiv_bnalt n).surjective.comp hβ₀s)

open scoped IsMulCommutative in
private theorem altBeta_bnalt_surjective {B W : Subgroup Ω} [IsMulCommutative ↥W]
    {n : ℕ} (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆)
    (β₀ : ↥(commV (autOn B W)) →*
      ↥((FFModel.altDn (2 * n + 1)).sec) ⧸
        (FFModel.altDn (2 * n + 1)).ker.subgroupOf (FFModel.altDn (2 * n + 1)).sec)
    (hβ₀s : Function.Surjective β₀) :
    Function.Surjective (altBeta_bnalt hBW hU β₀) :=
  (CFSG.CGT.PushingUpLit.BHS6.coreModEvenEquiv (2 * n + 1)).surjective.comp
    ((altBetaCore_bnalt_surjective β₀ hβ₀s).comp
      (commVEquivBlockU_bnalt hBW hU).symm.surjective)

open scoped IsMulCommutative in
private theorem altBeta_bnalt_ker {B W : Subgroup Ω} [IsMulCommutative ↥W]
    {n : ℕ} (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆)
    (β₀ : ↥(commV (autOn B W)) →*
      ↥((FFModel.altDn (2 * n + 1)).sec) ⧸
        (FFModel.altDn (2 * n + 1)).ker.subgroupOf (FFModel.altDn (2 * n + 1)).sec)
    (hβ₀k : ∀ u, β₀ u = 1 ↔ (u : W) ∈ gomiWXKer (autOn B W)) :
    (altBeta_bnalt hBW hU β₀).ker =
      (CFSG.QuasithinUnique.blockZ B).subgroupOf (CFSG.QuasithinUnique.blockU B) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have h1 : altBeta_bnalt hBW hU β₀ x = 1 ↔
      (((commVEquivBlockU_bnalt hBW hU).symm x : ↥(commV (autOn B W))) : W) ∈
        gomiWXKer (autOn B W) := by
    change (CFSG.CGT.PushingUpLit.BHS6.coreModEvenEquiv (2 * n + 1))
      (altDnSecCast_bnalt n (altDnQuotEquiv_bnalt n
        (β₀ ((commVEquivBlockU_bnalt hBW hU).symm x)))) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, hβ₀k]
  rw [h1, commVEquivBlockU_bnalt_mem_Z_iff hBW hU
    ((commVEquivBlockU_bnalt hBW hU).symm x), MulEquiv.apply_symm_apply]

private def gamPerm_bnalt {n : ℕ} (γ : (FFModel.altDn (2 * n + 1)).Gam) :
    Equiv.Perm (Fin (2 * n + 1)) :=
  (show ↥(alternatingGroup (Fin (2 * n + 1))) from γ).1

private def secToAmb_bnalt (n : ℕ) (x : ↥((FFModel.altDn (2 * n + 1)).sec)) :
    G6.PermMod (2 * n + 1) :=
  (x : (FFModel.altDn (2 * n + 1)).Amb)

private theorem altBeta_bnalt_act_aux {B W : Subgroup Ω} [IsMulCommutative ↥W] {n : ℕ}
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω)) (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆)
    (πe : (FFModel.altDn (2 * n + 1)).Gam ≃* ↥(autOn B W)) (ψ : ↥B →* ↥(autOn B W))
    (hψ : ∀ b, (ψ b : MulAut W) = conjAct W (Subgroup.inclusion hBW b))
    (β₀ : ↥(WV_bnalt B W) →* ↥((FFModel.altDn (2 * n + 1)).sec) ⧸
      (FFModel.altDn (2 * n + 1)).ker.subgroupOf (FFModel.altDn (2 * n + 1)).sec)
    (hsecinv : ∀ γ : (FFModel.altDn (2 * n + 1)).Gam, ∀ m ∈ (FFModel.altDn (2 * n + 1)).sec,
      (FFModel.altDn (2 * n + 1)).act γ m ∈ (FFModel.altDn (2 * n + 1)).sec)
    (hβ₀e : ∀ (γ : (FFModel.altDn (2 * n + 1)).Gam) (u : ↥(WV_bnalt B W))
      (m : ↥((FFModel.altDn (2 * n + 1)).sec))
      (hu : ((πe γ : ↥(autOn B W)) : MulAut W) (u : W) ∈ WV_bnalt B W)
      (hm : (FFModel.altDn (2 * n + 1)).act γ (m : (FFModel.altDn (2 * n + 1)).Amb) ∈
        (FFModel.altDn (2 * n + 1)).sec),
      β₀ u = QuotientGroup.mk m →
        β₀ ⟨((πe γ : ↥(autOn B W)) : MulAut W) (u : W), hu⟩ =
          QuotientGroup.mk ⟨(FFModel.altDn (2 * n + 1)).act γ
            (m : (FFModel.altDn (2 * n + 1)).Amb), hm⟩)
    (ℓ : ↥B) (u v : ↥(CFSG.QuasithinUnique.blockU B)) (hv : (v : Ω) = ℓ * u * ℓ⁻¹) :
    ∃ γ : (FFModel.altDn (2 * n + 1)).Gam, πe γ = ψ ℓ ∧
      ∃ m : ↥((FFModel.altDn (2 * n + 1)).sec),
        altBetaCore_bnalt β₀ ((commVEquivBlockU_bnalt hBW hU).symm u) = m ∧
        altBetaCore_bnalt β₀ ((commVEquivBlockU_bnalt hBW hU).symm v) =
          ⟨(FFModel.altDn (2 * n + 1)).act γ (m : (FFModel.altDn (2 * n + 1)).Amb),
            hsecinv γ m m.2⟩ := by
  let γ := πe.symm (ψ ℓ)
  have hπγ : πe γ = ψ ℓ := MulEquiv.apply_symm_apply πe (ψ ℓ)
  let uW : ↥(WV_bnalt B W) := (commVEquivBlockU_bnalt hBW hU).symm u
  let vW : ↥(WV_bnalt B W) := (commVEquivBlockU_bnalt hBW hU).symm v
  have hvW : (vW : W) = (πe γ : MulAut W) (uW : W) := by
    change (((commVEquivBlockU_bnalt hBW hU).symm v : ↥(WV_bnalt B W)) : W) =
      (πe γ : MulAut W) (((commVEquivBlockU_bnalt hBW hU).symm u : ↥(WV_bnalt B W)) : W)
    apply Subtype.ext
    rw [commVEquivBlockU_bnalt_symm_coe hBW hU v, hv, hπγ, hψ ℓ, AutOn.coe_conjAct_apply,
      commVEquivBlockU_bnalt_symm_coe hBW hU u]
    rfl
  have hu : (πe γ : MulAut W) (uW : W) ∈ WV_bnalt B W := by
    rw [← hvW]; exact vW.2
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₀ uW)
  have hact := hsecinv γ m m.2
  have h1 := hβ₀e γ uW m hu hact hm.symm
  have hvW' : vW = (⟨(πe γ : MulAut W) (uW : W), hu⟩ : ↥(WV_bnalt B W)) :=
    Subtype.ext hvW
  have hβv : altBetaCore_bnalt β₀ vW =
      ⟨(FFModel.altDn (2 * n + 1)).act γ (m : (FFModel.altDn (2 * n + 1)).Amb), hact⟩ := by
    rw [altBetaCore_bnalt_apply, hvW', h1, altDnQuotEquiv_bnalt_mk, altDnSecCast_bnalt_apply]
    rfl
  have hβu : altBetaCore_bnalt β₀ uW = m := by
    rw [altBetaCore_bnalt_apply, hm.symm, altDnQuotEquiv_bnalt_mk, altDnSecCast_bnalt_apply]
  exact ⟨γ, hπγ, m, hβu, hβv⟩

private theorem altBeta_bnalt_act {B W : Subgroup Ω} [IsMulCommutative ↥W] {n : ℕ}
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω)) (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆)
    (α : ↥B →* (FFModel.altDn (2 * n + 1)).Gam)
    (hsecinv : ∀ γ : (FFModel.altDn (2 * n + 1)).Gam, ∀ m ∈ (FFModel.altDn (2 * n + 1)).sec,
      (FFModel.altDn (2 * n + 1)).act γ m ∈ (FFModel.altDn (2 * n + 1)).sec)
    (β₀ : ↥(WV_bnalt B W) →* ↥((FFModel.altDn (2 * n + 1)).sec) ⧸
      (FFModel.altDn (2 * n + 1)).ker.subgroupOf (FFModel.altDn (2 * n + 1)).sec)
    (hcore : ∀ (ℓ : ↥B) (u v : ↥(CFSG.QuasithinUnique.blockU B)), (v : Ω) = ℓ * u * ℓ⁻¹ →
      ∃ (γ : (FFModel.altDn (2 * n + 1)).Gam) (m : ↥((FFModel.altDn (2 * n + 1)).sec)),
        α ℓ = γ ∧
        altBetaCore_bnalt β₀ ((commVEquivBlockU_bnalt hBW hU).symm u) = m ∧
        altBetaCore_bnalt β₀ ((commVEquivBlockU_bnalt hBW hU).symm v) =
          ⟨(FFModel.altDn (2 * n + 1)).act γ (m : (FFModel.altDn (2 * n + 1)).Amb),
            hsecinv γ m m.2⟩) :
    ∀ (ℓ : ↥B) (u v : ↥(CFSG.QuasithinUnique.blockU B)), (v : Ω) = ℓ * u * ℓ⁻¹ →
      ∀ i : Fin (2 * n + 1),
      ((Multiplicative.toAdd (altBeta_bnalt hBW hU β₀ v) :
        CFSG.QuasithinUnique.evenWeight (2 * n + 1)) : Fin (2 * n + 1) → ZMod 2) i =
      ((Multiplicative.toAdd (altBeta_bnalt hBW hU β₀ u) :
        CFSG.QuasithinUnique.evenWeight (2 * n + 1)) : Fin (2 * n + 1) → ZMod 2)
        ((gamPerm_bnalt (α ℓ))⁻¹ i) := by
  intro ℓ u v hv i
  obtain ⟨γ, m, hαγ, hβu, hβv⟩ := hcore ℓ u v hv
  let uW : ↥(WV_bnalt B W) := (commVEquivBlockU_bnalt hBW hU).symm u
  let vW : ↥(WV_bnalt B W) := (commVEquivBlockU_bnalt hBW hU).symm v
  calc
    ((Multiplicative.toAdd (altBeta_bnalt hBW hU β₀ v) :
        CFSG.QuasithinUnique.evenWeight (2 * n + 1)) : Fin (2 * n + 1) → ZMod 2) i
        = Multiplicative.toAdd (secToAmb_bnalt n
          ⟨(FFModel.altDn (2 * n + 1)).act γ (m : (FFModel.altDn (2 * n + 1)).Amb),
            hsecinv γ m m.2⟩) i := by
          rw [altBeta_bnalt_apply, toAdd_coreModEvenEquiv_bnalt, hβv]
          rfl
    _ = Multiplicative.toAdd (secToAmb_bnalt n m) ((gamPerm_bnalt γ)⁻¹ i) := by
          change Multiplicative.toAdd (G6.permAct (2 * n + 1) (gamPerm_bnalt γ)
            (secToAmb_bnalt n m)) i =
            Multiplicative.toAdd (secToAmb_bnalt n m) ((gamPerm_bnalt γ)⁻¹ i)
          exact G6.permAct_apply (2 * n + 1) (gamPerm_bnalt γ) (secToAmb_bnalt n m) i
    _ = ((Multiplicative.toAdd (altBeta_bnalt hBW hU β₀ u) :
        CFSG.QuasithinUnique.evenWeight (2 * n + 1)) : Fin (2 * n + 1) → ZMod 2)
          ((gamPerm_bnalt (α ℓ))⁻¹ i) := by
          rw [show α ℓ = γ from hαγ, altBeta_bnalt_apply, toAdd_coreModEvenEquiv_bnalt, hβu]
          rfl

open scoped IsMulCommutative in
private theorem isAltType_of_realizes_bnalt {B W : Subgroup Ω} [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hker : B ⊓ Subgroup.centralizer (W : Set Ω) = pCoreOf 2 B)
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) {n : ℕ} (hA : IsAlt ↥(autOn B W) (2 * n + 1))
    (hnat : (FFModel.altDn (2 * n + 1)).Realizes (autOn B W) (commV (autOn B W))
      (gomiWXKer (autOn B W))) :
    CFSG.QuasithinUnique.IsAltType B (2 * n + 1) := by
  classical
  obtain ⟨π, hπs, _, _, _, _, hsecinv, _, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := hnat
  obtain ⟨e⟩ := hA
  let ψ := CFSG.CGT.PushingUpLit.BHS6.actOnRange W B hBW
  let πe : (FFModel.altDn (2 * n + 1)).Gam ≃* ↥(autOn B W) :=
    MulEquiv.ofBijective π
      ⟨(Finite.injective_iff_surjective_of_equiv e.toEquiv.symm).2 hπs, hπs⟩
  let α : ↥B →* (FFModel.altDn (2 * n + 1)).Gam := πe.symm.toMonoidHom.comp ψ
  have hαeq : ∀ b, α b = πe.symm (ψ b) := fun _ => rfl
  have hαs : Function.Surjective α :=
    πe.symm.surjective.comp (CFSG.CGT.PushingUpLit.BHS6.actOnRange_surjective W B hBW)
  have hαker : α.ker = CFSG.pCore 2 ↥B := by
    ext b
    change πe.symm (ψ b) = 1 ↔ b ∈ CFSG.pCore 2 ↥B
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, actOnRange_ker_pCore_bnalt hBW hker]
  have hcore : ∀ (ℓ : ↥B) (u v : ↥(CFSG.QuasithinUnique.blockU B)),
      (v : Ω) = ℓ * u * ℓ⁻¹ →
      ∃ (γ : (FFModel.altDn (2 * n + 1)).Gam) (m : ↥((FFModel.altDn (2 * n + 1)).sec)),
        α ℓ = γ ∧
        altBetaCore_bnalt β₀ ((commVEquivBlockU_bnalt hBW hU).symm u) = m ∧
        altBetaCore_bnalt β₀ ((commVEquivBlockU_bnalt hBW hU).symm v) =
          ⟨(FFModel.altDn (2 * n + 1)).act γ (m : (FFModel.altDn (2 * n + 1)).Amb),
            hsecinv γ m m.2⟩ := by
    intro ℓ u v hv
    obtain ⟨γ, hπγ, m, hβu, hβv⟩ :=
      altBeta_bnalt_act_aux hBW hU πe ψ (fun _ => rfl) β₀ hsecinv hβ₀e
        ℓ u v hv
    have hγ : γ = πe.symm (ψ ℓ) := by rw [← hπγ, MulEquiv.symm_apply_apply]
    exact ⟨γ, m, (hαeq ℓ).trans hγ.symm, hβu, hβv⟩
  refine ⟨α, hαs, hαker, altBeta_bnalt hBW hU β₀,
    altBeta_bnalt_surjective hBW hU β₀ hβ₀s, altBeta_bnalt_ker hBW hU β₀ hβ₀k, ?_⟩
  exact altBeta_bnalt_act hBW hU α hsecinv β₀ hcore

open scoped IsMulCommutative in
theorem isNaturalAltModule_of_realizes {B W : Subgroup Ω} [IsMulCommutative ↥W]
    (hBW : B ≤ normalizer (W : Set Ω)) (hker : B ⊓ centralizer (W : Set Ω) = pCoreOf 2 B)
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) {n : ℕ} (hA : IsAlt ↥(autOn B W) (2 * n + 1))
    (hnat : (FFModel.altDn (2 * n + 1)).Realizes (autOn B W) (commV (autOn B W))
      (gomiWXKer (autOn B W))) :
    IsNaturalAltModule ↥B n :=
  CFSG.CGT.PushingUpLit.BHS6.isNaturalAltModule_of_isAltType
    (E := B) (m := n) (isAltType_of_realizes_bnalt hBW hker hU hA hnat)

end CFSG.GroupTheory
