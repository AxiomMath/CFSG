module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Cent
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Mx
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Cmp
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Gen
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S3B

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem part1 (hMin : MinIndexL34) (hInv : InvSec)
    (hstar : KStarL34) (hkb : KB813) (h171 : Prop17_1) (hL31 : Lemma31Narrow)
    (hB12 : Bender12) (h183 : Lemma18_3a) (h184 : Lemma18_4ac) (hKA : IVK_8_13_lift) {z : G}
    {k : Kind} {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G}
    (hctx : Ctx18 G z k S M p E t) (hZE : omega1Z p (Op p M) ≤ E) {X : Subgroup G}
    (hXv : ∀ v ∈ Vof M E, v ∈ normalizer (X : Set G)) (hXM : ¬ X ≤ M) (hXG : X ≠ ⊤)
    {J : Subgroup G} (hJ : IsCompIn X J) (hLie : IsL34Quotient ↥J) {e : G} (heE : e ∈ E)
    (he1 : e ≠ 1) (heJ : J ≤ centralizer ({e} : Set G)) :
    ∃ I : Subgroup G, IsCompIn (centralizer ({e} : Set G)) I ∧ J ≤ I ∧ IsL34Quotient ↥I := by
  obtain ⟨hMz, hz2', hz2, hp, hp2, hMc, hsimple, hzV, hVle, hZP, hZV, hZodd, hMZ, hZbot, hNZ, hEO,
    hZO⟩ := P2S4.CtxFacts.of_ctx h171 hctx
  have hS2 : Stage2Ctx G z k S := hctx.base.ctx.ctx
  have hF := S5Facts.of_ctx h171 hctx
  have hq : IsQuasisimple ↥J := P2S3.quasisimple_of_isCompIn hJ
  have hperf : Group.IsPerfect ↥J := hq.1
  obtain ⟨hJz, hzN, hJZ, hVN⟩ := cfg_basic h171 hL31 h183 hctx hXv hXM hXG hJ
  have hZc := cfg_odd_center hMin hInv hS2 hq hLie
  obtain ⟨-, hp3, -, -, -, h9Z⟩ := cfg_star hMin hInv hstar h171 hL31 h183 hctx hXv hXM hXG hJ hLie
  have hJM : ¬ J ≤ M := fun h => not_le_of_comm hq hJz (hMz ▸ h)
  set K : Subgroup G := centralizer ({e} : Set G) with hK
  have hKM : ¬ K ≤ M := fun h => hJM (heJ.trans h)
  have hKG : K ≠ ⊤ := centralizer_ne_top hF.hkps he1
  obtain ⟨hzC, hVC, -, -⟩ := centralizer_facts hB12 h171 hctx heE
  have hKv : ∀ v ∈ Vof M E, v ∈ normalizer (K : Set G) := fun v hv =>
    Subgroup.le_normalizer (hVC hv)
  have hJEm : J ≤ Em K :=
    J_le_Em_cent hB12 h184 h171 hctx heE he1 hKM (Subgroup.isPerfect_iff.mp hperf) heJ hJz
  have hno3 := comps_no3 h183 hctx hKv hKM hKG
  have hno3H : ∀ K₁ K₂ K₃ : Subgroup ↥K, IsComponent K₁ → IsComponent K₂ → IsComponent K₃ →
      K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := fun K₁ K₂ K₃ h₁ h₂ h₃ =>
    P2S3.comps_le_two hL31 hS2 hKG hzC h₁ h₂ h₃
  obtain ⟨I, hI, hJI⟩ := exists_comp_of_le_Em hq hZc (exists_elem_four hkb hLie hZc)
    (no_involution_cent hMin hInv hS2 hq hLie) hS2.std.rank.2 hno3 hJEm
  refine ⟨I, hI, hJI, ?_⟩
  have hIq : IsQuasisimple ↥I := P2S3.quasisimple_of_isCompIn hI
  have hzI : z ∈ normalizer (I : Set G) := normalizer_of_le_comp hI hzC hq hJI hzN
  have hIz : ⁅I, zpowers z⁆ = I := by
    refine commutator_eq_of_not_le_centralizer hIq (Subgroup.zpowers_le.mpr hzI) ?_
    intro h
    have h1 : ⁅J, zpowers z⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (fun j hj => Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (h hy) j (hJI hj)).symm)
    rw [hJz] at h1
    have : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot J).mp this h1
  have hEcomm := hctx.E_elem.toIsMulCommutative
  have hZK : omega1Z p (Op p M) ≤ K := fun x hx => by
    rw [hK, Subgroup.mem_centralizer_singleton_iff]
    exact setLike_mul_comm (s := E) (hZE hx) heE
  have hZI : omega1Z p (Op p M) ≤ normalizer (I : Set G) := fun x hx =>
    P2S3.mem_normalizer_of_odd hno3H hI (hZK hx) (hZodd x hx)
  have hZJ : omega1Z p (Op p M) ≤ normalizer (J : Set G) := fun x hx =>
    hVN x (hZV hx) (hZodd x hx)
  have hQ : omega1Z p (Op p M) ≤
      Op p M ⊓ K ⊓ normalizer (I : Set G) ⊓ normalizer (J : Set G) := fun x hx =>
    ⟨⟨⟨hZP hx, hZK hx⟩, hZI hx⟩, hZJ hx⟩
  have hnc : ¬ IsCyclic ↥(Pbar J (omega1Z p (Op p M))) := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(Pbar J (omega1Z p (Op p M))))
    rw [h9Z] at hg
    have hg3 : g ^ 3 = 1 := by
      obtain ⟨x, hx, hxZ, hxe⟩ := K0.mem_Pbar.mp g.2
      apply Subtype.ext
      show ((g : MulAut (↥J ⧸ center ↥J))) ^ 3 = 1
      rw [← hxe, ← map_pow]
      have hx3 : x ^ 3 = 1 := by
        have := hxZ.2.2
        rwa [hp3] at this
      have : (⟨x, hx⟩ : ↥(normalizer (J : Set G))) ^ 3 = 1 := Subtype.ext hx3
      rw [this, map_one]
    have hord : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    rw [hg] at hord
    omega
  exact isL34_of_noncyclic hKA hS2 hMz hz2' hp hp2 hKG hI hIq hq hzI hIz hJI hQ hnc

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6
