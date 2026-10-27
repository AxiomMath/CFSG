module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Dict

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup _root_.Certificates

private lemma fz410_cOrdGo_perm {X : Type} [DecidableEq X] (m : X → X → X) (one : X)
    (σ : X ≃ X) (hm : ∀ x y, σ (m x y) = m (σ x) (σ y)) (h1 : σ one = one) (x : X) :
    ∀ (f : ℕ) (r : X) (n : ℕ),
      FzL410.cOrdGo m one (σ x) f (σ r) n = FzL410.cOrdGo m one x f r n := by
  intro f
  induction f with
  | zero => intro r n; rfl
  | succ f ih =>
    intro r n
    simp only [FzL410.cOrdGo]
    have hiff : σ r = one ↔ r = one := by
      constructor
      · intro h; exact σ.injective (h.trans h1.symm)
      · intro h; rw [h, h1]
    by_cases hr : r = one
    · rw [if_pos (hiff.mpr hr), if_pos hr]
    · rw [if_neg (fun h => hr (hiff.mp h)), if_neg hr, ← hm, ih]

private lemma fz410_cOrd_perm {X : Type} [DecidableEq X] (m : X → X → X) (one : X)
    (σ : X ≃ X) (hm : ∀ x y, σ (m x y) = m (σ x) (σ y)) (h1 : σ one = one) (x : X) :
    FzL410.cOrd m one (σ x) = FzL410.cOrd m one x :=
  fz410_cOrdGo_perm m one σ hm h1 x 32 x 1

private lemma fz410_cRound_perm {X : Type} [Fintype X] (m : X → X → X) (σ : X ≃ X)
    (hm : ∀ x y, σ (m x y) = m (σ x) (σ y)) (c : X → ℕ) (hc : ∀ x, c (σ x) = c x) (x : X) :
    FzL410.cRound m c (σ x) = FzL410.cRound m c x := by
  have hs : ∑ y : X, FzL410.cMix (c y * 1000003) (c (m (σ x) y) * 998244353 + 1) =
      ∑ y : X, FzL410.cMix (c y * 1000003) (c (m x y) * 998244353 + 1) := by
    calc _ = ∑ y, FzL410.cMix (c (σ y) * 1000003)
          (c (m (σ x) (σ y)) * 998244353 + 1) :=
          (Equiv.sum_comp σ (fun y => FzL410.cMix (c y * 1000003)
            (c (m (σ x) y) * 998244353 + 1))).symm
      _ = _ := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← hm, hc, hc]
  unfold FzL410.cRound
  rw [hs]

theorem fz410_c1_perm {X : Type} [Fintype X] [DecidableEq X] (m : X → X → X) (one : X)
    (σ : X ≃ X) (hm : ∀ x y, σ (m x y) = m (σ x) (σ y)) (h1 : σ one = one) (x : X) :
    FzL410.c1 m one (σ x) = FzL410.c1 m one x := by
  unfold FzL410.c1
  exact fz410_cRound_perm m σ hm _ (fun y => fz410_cOrd_perm m one σ hm h1 y) x

namespace Fz410Mod

variable {G : Type} [Group G] [Finite G] {t tau lam rho s : G} {Z E W Q R T P : Subgroup G}
  {emb : FzL410.A → G} (M : Fz410Mod t tau lam rho s Z E W Q R T P emb)

private noncomputable def fz410_conjFun {X : Type} (φ : X → G) {K : Subgroup G}
    (hφ_mem : ∀ x, φ x ∈ K) (hφ_surj : ∀ g ∈ K, ∃ x, φ x = g)
    (u : G) (hu : u ∈ normalizer (K : Set G)) (x : X) : X :=
  Classical.choose (hφ_surj (u * φ x * u⁻¹)
    ((Subgroup.mem_set_normalizer_iff.mp hu (φ x)).mp (hφ_mem x)))

private lemma fz410_conjFun_spec {X : Type} (φ : X → G) {K : Subgroup G}
    (hφ_mem : ∀ x, φ x ∈ K) (hφ_surj : ∀ g ∈ K, ∃ x, φ x = g)
    (u : G) (hu : u ∈ normalizer (K : Set G)) (x : X) :
    φ (fz410_conjFun φ hφ_mem hφ_surj u hu x) = u * φ x * u⁻¹ :=
  Classical.choose_spec (hφ_surj (u * φ x * u⁻¹)
    ((Subgroup.mem_set_normalizer_iff.mp hu (φ x)).mp (hφ_mem x)))

private lemma fz410_conjFun_injective {X : Type} (φ : X → G)
    (hφ_inj : Function.Injective φ) {K : Subgroup G}
    (hφ_mem : ∀ x, φ x ∈ K) (hφ_surj : ∀ g ∈ K, ∃ x, φ x = g)
    (u : G) (hu : u ∈ normalizer (K : Set G)) :
    Function.Injective (fz410_conjFun φ hφ_mem hφ_surj u hu) := by
  intro x y hxy
  apply hφ_inj
  have hx := fz410_conjFun_spec φ hφ_mem hφ_surj u hu x
  have hy := fz410_conjFun_spec φ hφ_mem hφ_surj u hu y
  rw [hxy] at hx
  rw [hx] at hy
  exact mul_left_cancel (mul_right_cancel hy)

private lemma fz410_conjFun_surjective {X : Type} (φ : X → G)
    (hφ_inj : Function.Injective φ) {K : Subgroup G}
    (hφ_mem : ∀ x, φ x ∈ K) (hφ_surj : ∀ g ∈ K, ∃ x, φ x = g)
    (u : G) (hu : u ∈ normalizer (K : Set G)) :
    Function.Surjective (fz410_conjFun φ hφ_mem hφ_surj u hu) := by
  intro z
  have hw : u⁻¹ * φ z * u ∈ K :=
    (Subgroup.mem_set_normalizer_iff''.mp hu (φ z)).mp (hφ_mem z)
  obtain ⟨y, hy⟩ := hφ_surj (u⁻¹ * φ z * u) hw
  refine ⟨y, ?_⟩
  apply hφ_inj
  have h := fz410_conjFun_spec φ hφ_mem hφ_surj u hu y
  rw [h, hy]
  group

private noncomputable def fz410_conjEquiv {X : Type} (φ : X → G)
    (hφ_inj : Function.Injective φ) {K : Subgroup G}
    (hφ_mem : ∀ x, φ x ∈ K) (hφ_surj : ∀ g ∈ K, ∃ x, φ x = g)
    (u : G) (hu : u ∈ normalizer (K : Set G)) : X ≃ X :=
  Equiv.ofBijective (fz410_conjFun φ hφ_mem hφ_surj u hu)
    ⟨fz410_conjFun_injective φ hφ_inj hφ_mem hφ_surj u hu,
     fz410_conjFun_surjective φ hφ_inj hφ_mem hφ_surj u hu⟩

private lemma fz410_conjEquiv_apply {X : Type} (φ : X → G)
    (hφ_inj : Function.Injective φ) {K : Subgroup G}
    (hφ_mem : ∀ x, φ x ∈ K) (hφ_surj : ∀ g ∈ K, ∃ x, φ x = g)
    (u : G) (hu : u ∈ normalizer (K : Set G)) (x : X) :
    fz410_conjEquiv φ hφ_inj hφ_mem hφ_surj u hu x =
      fz410_conjFun φ hφ_mem hφ_surj u hu x := rfl

private lemma fz410_conjEquiv_mul {X : Type} (m : X → X → X) (φ : X → G)
    (hφ_inj : Function.Injective φ) (hφ_mul : ∀ x y, φ (m x y) = φ x * φ y)
    {K : Subgroup G} (hφ_mem : ∀ x, φ x ∈ K) (hφ_surj : ∀ g ∈ K, ∃ x, φ x = g)
    (u : G) (hu : u ∈ normalizer (K : Set G)) (x y : X) :
    fz410_conjEquiv φ hφ_inj hφ_mem hφ_surj u hu (m x y) =
      m (fz410_conjEquiv φ hφ_inj hφ_mem hφ_surj u hu x)
        (fz410_conjEquiv φ hφ_inj hφ_mem hφ_surj u hu y) := by
  apply hφ_inj
  simp only [fz410_conjEquiv_apply, fz410_conjFun_spec, hφ_mul]
  group

private lemma fz410_conjEquiv_one {X : Type} (φ : X → G) (one : X)
    (hφ_inj : Function.Injective φ) (hφ_one : φ one = 1)
    {K : Subgroup G} (hφ_mem : ∀ x, φ x ∈ K) (hφ_surj : ∀ g ∈ K, ∃ x, φ x = g)
    (u : G) (hu : u ∈ normalizer (K : Set G)) :
    fz410_conjEquiv φ hφ_inj hφ_mem hφ_surj u hu one = one := by
  apply hφ_inj
  simp only [fz410_conjEquiv_apply, fz410_conjFun_spec, hφ_one]
  group

private def fz410_iota (y : FzL410.RM) : FzL410.TM := (y.1, (y.2.1, y.2.2, 0))

private lemma fz410_iota_injective : Function.Injective fz410_iota := by
  intro y y' h
  have h1 : y.1 = y'.1 := congrArg (fun z : FzL410.TM => z.1) h
  have h2 : y.2 = y'.2 := by
    have h2' := congrArg (fun z : FzL410.TM => z.2) h
    simp only [fz410_iota] at h2'
    exact Prod.ext (congrArg (fun z : FzL410.V => z.1) h2')
      (congrArg (fun z : FzL410.V => z.2.1) h2')
  exact Prod.ext h1 h2

private lemma fz410_iota_mul (y y' : FzL410.RM) :
    fz410_iota (FzL410.mulR y y') = FzL410.mulT (fz410_iota y) (fz410_iota y') := by
  simp [fz410_iota, FzL410.mulT, FzL410.mulR, FzL410.act, FzL410.actR, FzL410.ap]

private lemma fz410_iota_one : fz410_iota FzL410.oneR = FzL410.oneT := rfl

private lemma fz410_iota_inP (y : FzL410.RM) :
    FzL410.inP (fz410_iota y) ↔ y.2 = 0 := by
  constructor
  · intro h
    have h1 : y.2.1 = 0 := congrArg (fun z : FzL410.V => z.1) h
    have h2 : y.2.2 = 0 := congrArg (fun z : FzL410.V => z.2.1) h
    exact Prod.ext h1 h2
  · intro h
    have h1 : y.2.1 = 0 := congrArg (fun z : ZMod 2 × ZMod 2 => z.1) h
    have h2 : y.2.2 = 0 := congrArg (fun z : ZMod 2 × ZMod 2 => z.2) h
    show ((y.2.1, y.2.2, (0 : ZMod 2)) : FzL410.V) = 0
    rw [h1, h2]
    rfl

include M
private lemma fz410_mu_one : fz410Mu emb t s lam FzL410.oneT = 1 := by
  rw [show FzL410.oneT = FzL410.pe (0 : FzL410.A) from rfl, M.mu_pe, M.emb.emb_zero]

private noncomputable def fz410_sigmaT (u : G) (hu : u ∈ normalizer (T : Set G)) :
    FzL410.TM ≃ FzL410.TM :=
  fz410_conjEquiv (fz410Mu emb t s lam) M.mu_inj
    (fun z => (M.mem_T _).mpr ⟨z, rfl⟩) (fun g hg => (M.mem_T g).mp hg) u hu

private lemma fz410_sigmaT_spec (u : G) (hu : u ∈ normalizer (T : Set G)) (y : FzL410.TM) :
    fz410Mu emb t s lam (fz410_sigmaT M u hu y) = u * fz410Mu emb t s lam y * u⁻¹ := by
  simp only [fz410_sigmaT, fz410_conjEquiv_apply, fz410_conjFun_spec]

private lemma fz410_sigmaT_mul (u : G) (hu : u ∈ normalizer (T : Set G)) :
    ∀ x y, fz410_sigmaT M u hu (FzL410.mulT x y) =
      FzL410.mulT (fz410_sigmaT M u hu x) (fz410_sigmaT M u hu y) :=
  fz410_conjEquiv_mul FzL410.mulT (fz410Mu emb t s lam) M.mu_inj M.mu_mul
    (fun z => (M.mem_T _).mpr ⟨z, rfl⟩) (fun g hg => (M.mem_T g).mp hg) u hu

private lemma fz410_sigmaT_one (u : G) (hu : u ∈ normalizer (T : Set G)) :
    fz410_sigmaT M u hu FzL410.oneT = FzL410.oneT :=
  fz410_conjEquiv_one (fz410Mu emb t s lam) FzL410.oneT M.mu_inj (fz410_mu_one M)
    (fun z => (M.mem_T _).mpr ⟨z, rfl⟩) (fun g hg => (M.mem_T g).mp hg) u hu

private lemma fz410_sigmaT_c1 (u : G) (hu : u ∈ normalizer (T : Set G)) (y : FzL410.TM) :
    FzL410.c1 FzL410.mulT FzL410.oneT (fz410_sigmaT M u hu y) =
      FzL410.c1 FzL410.mulT FzL410.oneT y :=
  fz410_c1_perm FzL410.mulT FzL410.oneT (fz410_sigmaT M u hu)
    (fz410_sigmaT_mul M u hu) (fz410_sigmaT_one M u hu) y

theorem charR_transfer (hC : FzL410.CharR) :
    ∀ u ∈ normalizer (T : Set G), ∀ x ∈ R, u * x * u⁻¹ ∈ R := by
  intro u hu x hx
  obtain ⟨y, hy⟩ := (M.mem_T x).mp (M.str.RT hx)
  have hyR : FzL410.inR y := (M.mem_R y).mp (hy.symm ▸ hx)
  have hσ : fz410Mu emb t s lam (fz410_sigmaT M u hu y) = u * x * u⁻¹ := by
    rw [fz410_sigmaT_spec, hy]
  rw [← hσ]
  exact (M.mem_R _).mpr
    (((hC y (fz410_sigmaT M u hu y)) (fz410_sigmaT_c1 M u hu y).symm).mp hyR)

private lemma fz410_mu_iota_mem (y : FzL410.RM) :
    fz410Mu emb t s lam (fz410_iota y) ∈ R :=
  (M.mem_R _).mpr (by simp [FzL410.inR, fz410_iota])

private lemma fz410_mu_iota_surj (g : G) (hg : g ∈ R) :
    ∃ y : FzL410.RM, fz410Mu emb t s lam (fz410_iota y) = g := by
  obtain ⟨z, hz⟩ := (M.mem_T g).mp (M.str.RT hg)
  have hzR : FzL410.inR z := (M.mem_R z).mp (hz.symm ▸ hg)
  have hiy : fz410_iota (z.1, (z.2.1, z.2.2.1)) = z := by
    have hzR' : z.2.2.2 = 0 := hzR
    ext <;> simp [fz410_iota, hzR']
  exact ⟨(z.1, (z.2.1, z.2.2.1)), by rw [hiy, hz]⟩

private lemma fz410_mu_iota_injective :
    Function.Injective (fun y : FzL410.RM => fz410Mu emb t s lam (fz410_iota y)) := by
  intro y y' h
  exact fz410_iota_injective (M.mu_inj h)

private lemma fz410_mu_iota_mul (y y' : FzL410.RM) :
    fz410Mu emb t s lam (fz410_iota (FzL410.mulR y y')) =
      fz410Mu emb t s lam (fz410_iota y) * fz410Mu emb t s lam (fz410_iota y') := by
  rw [fz410_iota_mul, M.mu_mul]

private lemma fz410_mu_iota_one :
    fz410Mu emb t s lam (fz410_iota FzL410.oneR) = 1 := by
  rw [fz410_iota_one, fz410_mu_one M]

private noncomputable def fz410_sigmaR (n : G) (hn : n ∈ normalizer (R : Set G)) :
    FzL410.RM ≃ FzL410.RM :=
  fz410_conjEquiv (fun y => fz410Mu emb t s lam (fz410_iota y)) (fz410_mu_iota_injective M)
    (fun y => fz410_mu_iota_mem M y) (fun g hg => fz410_mu_iota_surj M g hg) n hn

private lemma fz410_sigmaR_spec (n : G) (hn : n ∈ normalizer (R : Set G)) (y : FzL410.RM) :
    fz410Mu emb t s lam (fz410_iota (fz410_sigmaR M n hn y)) =
      n * fz410Mu emb t s lam (fz410_iota y) * n⁻¹ := by
  simp only [fz410_sigmaR, fz410_conjEquiv_apply]
  exact fz410_conjFun_spec (fun y : FzL410.RM => fz410Mu emb t s lam (fz410_iota y))
    (fun y => fz410_mu_iota_mem M y) (fun g hg => fz410_mu_iota_surj M g hg) n hn y

private lemma fz410_sigmaR_c1 (n : G) (hn : n ∈ normalizer (R : Set G)) (y : FzL410.RM) :
    FzL410.c1 FzL410.mulR FzL410.oneR (fz410_sigmaR M n hn y) =
      FzL410.c1 FzL410.mulR FzL410.oneR y :=
  fz410_c1_perm FzL410.mulR FzL410.oneR (fz410_sigmaR M n hn)
    (fz410_conjEquiv_mul FzL410.mulR (fun y => fz410Mu emb t s lam (fz410_iota y))
      (fz410_mu_iota_injective M) (fun y y' => fz410_mu_iota_mul M y y')
      (fun y => fz410_mu_iota_mem M y) (fun g hg => fz410_mu_iota_surj M g hg) n hn)
    (fz410_conjEquiv_one (fun y => fz410Mu emb t s lam (fz410_iota y)) FzL410.oneR
      (fz410_mu_iota_injective M) (fz410_mu_iota_one M) (fun y => fz410_mu_iota_mem M y)
      (fun g hg => fz410_mu_iota_surj M g hg) n hn) y

theorem charP_transfer (hC : FzL410.CharP) :
    ∀ n ∈ normalizer (R : Set G), ∀ x ∈ P, n * x * n⁻¹ ∈ P := by
  intro n hn x hx
  have hxR : x ∈ R := M.str.QR (M.pf.PQ hx)
  obtain ⟨y, hy⟩ := fz410_mu_iota_surj M x hxR
  have hyP : FzL410.inP (fz410_iota y) := (M.mem_P (fz410_iota y)).mp (hy.symm ▸ hx)
  have hyP' : y.2 = 0 := (fz410_iota_inP y).mp hyP
  have hchar := (hC y (fz410_sigmaR M n hn y)) (fz410_sigmaR_c1 M n hn y).symm
  have hgoal : n * x * n⁻¹ = fz410Mu emb t s lam (fz410_iota (fz410_sigmaR M n hn y)) := by
    rw [← hy, fz410_sigmaR_spec]
  rw [hgoal, M.mem_P]
  exact (fz410_iota_inP (fz410_sigmaR M n hn y)).mpr (hchar.mp hyP')

end Fz410Mod

end CFSG.OddStandard.SmallF3.FritzII
