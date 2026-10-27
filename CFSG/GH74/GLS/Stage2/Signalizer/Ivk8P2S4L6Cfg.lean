module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Star
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4Facts
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4Comp
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L4Aux
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S3B
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8K0Odd
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G]

theorem cfg_basic (h171 : Prop17_1) (hL31 : Lemma31Narrow) (h183 : Lemma18_3a) {z : G} {k : Kind}
    {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t)
    {X : Subgroup G} (hXv : ∀ v ∈ Vof M E, v ∈ normalizer (X : Set G)) (hXM : ¬ X ≤ M)
    (hXG : X ≠ ⊤) {J : Subgroup G} (hJ : IsCompIn X J) :
    ⁅J, zpowers z⁆ = J ∧ z ∈ normalizer (J : Set G) ∧ ⁅J, omega1Z p (Op p M)⁆ = J ∧
      (∀ v ∈ Vof M E, Odd (orderOf v) → v ∈ normalizer (J : Set G)) := by
  obtain ⟨hMz, hz2', hz2, hp, hp2, hMc, hsimple, hzV, hVle, hZP, hZV, hZodd, hMZ, hZbot, hNZ, hEO,
    hZO⟩ := P2S4.CtxFacts.of_ctx h171 hctx
  have hS2 : Stage2Ctx G z k S := hctx.base.ctx.ctx
  have h3 := h183 G z k S M p E t hctx X hXv hXM hXG J hJ
  have hJz : ⁅J, zpowers z⁆ = J := h3.2.1
  have hJZ : ⁅J, omega1Z p (Op p M)⁆ = J := h3.2.2
  refine ⟨hJz, P2S4.mem_normalizer_of_commutator_eq hJz, hJZ, ?_⟩
  intro v hv hodd
  have hzX : z ∈ normalizer (X : Set G) := hXv z hzV
  have hVX : Vof M E ≤ normalizer (X : Set G) := fun v hv => hXv v hv
  have hJq : IsQuasisimple ↥J := P2S3.quasisimple_of_isCompIn hJ
  have hnebot : ∀ D : Subgroup G, IsQuasisimple ↥D → D ≠ ⊥ := fun D hD =>
    (Subgroup.nontrivial_iff_ne_bot D).mp (CFSG.LocalCores.isQuasisimple_nontrivial hD)
  set H : Subgroup G := X ⊔ Vof M E ⊔ zpowers z with hH
  have hXH : X ≤ H := le_sup_left.trans le_sup_left
  have hVH : Vof M E ≤ H := le_sup_right.trans le_sup_left
  have hzH : z ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hHN : H ≤ normalizer (X : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hVX) (Subgroup.zpowers_le.mpr hzX)
  have hXbot : X ≠ ⊥ := fun h => hnebot J hJq (le_bot_iff.mp (h ▸ hJ.1))
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hn : X.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact top_le_iff.mp (htop ▸ hHN)
    rcases hsimple.eq_bot_or_eq_top_of_normal X with h | h
    · exact hXbot h
    · exact hXG h
  have hno3 : ∀ K₁ K₂ K₃ : Subgroup ↥H, IsComponent K₁ → IsComponent K₂ → IsComponent K₃ →
      K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := fun K₁ K₂ K₃ h₁ h₂ h₃ =>
    P2S3.comps_le_two hL31 hS2 hHtop hzH h₁ h₂ h₃
  exact P2S3.mem_normalizer_of_odd hno3 (P2S4.isCompIn_of_normal hXH hHN hJ) (hVH hv) hodd

theorem cfg_Z_facts (h171 : Prop17_1) (hL31 : Lemma31Narrow) (h183 : Lemma18_3a) {z : G}
    {k : Kind} {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G}
    (hctx : Ctx18 G z k S M p E t) {X : Subgroup G}
    (hXv : ∀ v ∈ Vof M E, v ∈ normalizer (X : Set G)) (hXM : ¬ X ≤ M) (hXG : X ≠ ⊤)
    {J : Subgroup G} (hJ : IsCompIn X J) :
    omega1Z p (Op p M) ≤ normalizer (J : Set G) ∧
      ¬ omega1Z p (Op p M) ≤ centralizer (J : Set G) := by
  obtain ⟨hMz, hz2', hz2, hp, hp2, hMc, hsimple, hzV, hVle, hZP, hZV, hZodd, hMZ, hZbot, hNZ, hEO,
    hZO⟩ := P2S4.CtxFacts.of_ctx h171 hctx
  obtain ⟨hJz, hzN, hJZ, hVN⟩ := cfg_basic h171 hL31 h183 hctx hXv hXM hXG hJ
  have hq : IsQuasisimple ↥J := P2S3.quasisimple_of_isCompIn hJ
  have hnebot : J ≠ ⊥ := fun h => by
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot J).mp this h
  refine ⟨fun x hx => hVN x (hZV hx) (hZodd x hx), ?_⟩
  intro hle
  have h1 : ⁅omega1Z p (Op p M), J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
  rw [Subgroup.commutator_comm, hJZ] at h1
  exact hnebot h1

theorem cfg_odd_center (hMin : MinIndexL34) (hInv : InvSec)
    {z : G} {k : Kind} {S : Subgroup G} (hS2 : Stage2Ctx G z k S) {J : Subgroup G}
    (hq : IsQuasisimple ↥J) (hLie : IsL34Quotient ↥J) : Odd (Nat.card (center ↥J)) :=
  odd_center_of_l34 hMin hq (fun x hx T _ _ hns hsec => hInv G z k S hS2 x hx T hns hsec) hLie

theorem cfg_star (hMin : MinIndexL34) (hInv : InvSec)
    (hstar : KStarL34) (h171 : Prop17_1) (hL31 : Lemma31Narrow) (h183 : Lemma18_3a) {z : G}
    {k : Kind} {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G}
    (hctx : Ctx18 G z k S M p E t) {X : Subgroup G}
    (hXv : ∀ v ∈ Vof M E, v ∈ normalizer (X : Set G)) (hXM : ¬ X ≤ M) (hXG : X ≠ ⊤)
    {J : Subgroup G} (hJ : IsCompIn X J) (hLie : IsL34Quotient ↥J) :
    ∃ hzN : z ∈ normalizer (J : Set G), p = 3 ∧ UnitaryFix (alphaZ J hzN) ∧
      alphaZ J hzN ∉ innSub (↥J ⧸ center ↥J) ∧
      Nat.card ↥(Pbar J (Op p M ⊓ normalizer (J : Set G))) = 9 ∧
      Nat.card ↥(Pbar J (omega1Z p (Op p M))) = 9 := by
  obtain ⟨hMz, hz2', hz2, hp, hp2, hMc, hsimple, hzV, hVle, hZP, hZV, hZodd, hMZ, hZbot, hNZ, hEO,
    hZO⟩ := P2S4.CtxFacts.of_ctx h171 hctx
  have hS2 : Stage2Ctx G z k S := hctx.base.ctx.ctx
  obtain ⟨hJz, hzN, hJZ, hVN⟩ := cfg_basic h171 hL31 h183 hctx hXv hXM hXG hJ
  have hq : IsQuasisimple ↥J := P2S3.quasisimple_of_isCompIn hJ
  have hZc := cfg_odd_center hMin hInv hS2 hq hLie
  have hnebot : J ≠ ⊥ := fun h => by
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot J).mp this h
  have hZN : omega1Z p (Op p M) ≤ normalizer (J : Set G) := fun x hx =>
    hVN x (hZV hx) (hZodd x hx)
  have hZnc : ¬ omega1Z p (Op p M) ≤ centralizer (J : Set G) := by
    intro hle
    have h1 : ⁅omega1Z p (Op p M), J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    rw [Subgroup.commutator_comm, hJZ] at h1
    exact hnebot h1
  have hMc' : ∀ c : G, c * z = z * c → c ∈ M := fun c hc => by
    rw [hMz]
    exact Subgroup.mem_centralizer_singleton_iff.2 hc
  have hLie' : LieModel (↥J ⧸ center ↥J) .PSL 3 2 2 := hLie
  have hPN : Op p M ⊓ normalizer (J : Set G) ≤ normalizer (J : Set G) := inf_le_right
  have hPp : IsPGroup p ↥(Op p M ⊓ normalizer (J : Set G)) :=
    (isPGroup_Op p hp M).to_le inf_le_left
  have hPnc : ¬ Op p M ⊓ normalizer (J : Set G) ≤ centralizer (J : Set G) := fun hle =>
    hZnc fun x hx => hle ⟨hZP hx, hZN hx⟩
  have hPz : ∀ x ∈ Op p M ⊓ normalizer (J : Set G), z * x = x * z := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.1
      (hMz ▸ Op_le p M hx.1 : x ∈ centralizer ({z} : Set G))).symm
  have hPnorm : ∀ y ∈ J, y * z = z * y →
      y ∈ normalizer ((Op p M ⊓ normalizer (J : Set G) : Subgroup G) : Set G) := fun y hy hyz =>
    mem_normalizer_inf' (le_normalizer_Op p M (hMc' y hyz))
      (Subgroup.le_normalizer (Subgroup.le_normalizer hy))
  obtain ⟨hp3, hU, h9, hninn⟩ :=
    star_J hstar hq hLie' hZc hzN hz2 hJz hp hp2 hPN hPp hPnc hPz hPnorm
  have hZp : IsPGroup p ↥(omega1Z p (Op p M)) := (isPGroup_Op p hp M).to_le hZP
  have hZz : ∀ x ∈ omega1Z p (Op p M), z * x = x * z := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.1
      (hMz ▸ Op_le p M (hZP hx) : x ∈ centralizer ({z} : Set G))).symm
  have hZnorm : ∀ y ∈ J, y * z = z * y →
      y ∈ normalizer ((omega1Z p (Op p M) : Subgroup G) : Set G) := fun y _ hyz =>
    hMZ (hMc' y hyz)
  obtain ⟨-, -, h9Z, -⟩ := star_J hstar hq hLie' hZc hzN hz2 hJz hp hp2 hZN hZp hZnc hZz hZnorm
  exact ⟨hzN, hp3, hU, hninn, h9, h9Z⟩

end Basic

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6
