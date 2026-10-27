module

public import CFSG.ClassicalGroups.AlternatingInvolutionCentralizer
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic

public section

namespace CFSG.ClassicalGroups.QuadraticCentralizer

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M] [CharP F 2]

include F in
private theorem neg_vec (x : M) : -x = x := by
  rw [← neg_one_smul F x, CharTwo.neg_eq, one_smul]

include F in
private theorem add_self_vec (x : M) : x + x = 0 := by
  have h := add_neg_cancel x
  rwa [neg_vec (F := F)] at h

@[expose] def orthogonalRep (Q : QuadraticForm F M) :
    TauCeti.QuadraticMap.orthogonalGroup Q →* Module.End F M :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype

private theorem polar_isAlt (Q : QuadraticForm F M) : Q.polarBilin.IsAlt := by
  intro x
  change polar Q x x = 0
  simp only [polar, add_self_vec (F := F), QuadraticMap.map_zero, zero_sub,
    CharTwo.neg_eq, sub_self]

theorem paired_reflection_action
    (Q : QuadraticForm F M)
    (hNondeg : ∀ w : M, w ≠ 0 → ∃ a : M, Q.polarBilin w a ≠ 0)
    (r : TauCeti.QuadraticMap.orthogonalGroup Q) (hr : r ^ 2 = 1)
    (hAlt : ∀ a : M, Q.polarBilin a (r.1 a - a) = 0) :
    ∀ a : M, ∃ g ∈ Subgroup.centralizer ({r} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)),
      ∀ x ∈ LinearMap.range (orthogonalRep Q r - 1),
        orthogonalRep Q g x = x + Q.polarBilin x a • (orthogonalRep Q r - 1) a := by
  let B : LinearMap.BilinForm F M := Q.polarBilin
  let N := orthogonalRep Q r - 1
  have hB : B.IsAlt := polar_isAlt Q
  have hSym (x y : M) : B x y = B y x := by
    change polar Q x y = polar Q y x
    exact polar_comm Q x y
  have hQ (x : M) : Q (r.1 x) = Q x :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp r.2 x
  have hPres (x y : M) : B (r.1 x) (r.1 y) = B x y := by
    change polar Q (r.1 x) (r.1 y) = polar Q x y
    simp only [polar, ← map_add, hQ]
  have hRR (x : M) : r.1 (r.1 x) = x := by
    have h := congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup Q => g.1 x) hr
    change r.1 (r.1 x) = x at h
    exact h
  have hAdj (x y : M) : B (r.1 x) y = B x (r.1 y) := by
    calc
      B (r.1 x) y = B (r.1 x) (r.1 (r.1 y)) := by rw [hRR]
      _ = B x (r.1 y) := hPres x (r.1 y)
  have hRangeFix {x : M} (hx : x ∈ LinearMap.range N) : r.1 x = x := by
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hx
    change r.1 (r.1 c - c) = r.1 c - c
    rw [map_sub, hRR]
    simp only [sub_eq_add_neg, neg_vec (F := F)]
    exact add_comm _ _
  have hNil (c : M) : N (N c) = 0 := by
    change r.1 (N c) - N c = 0
    rw [hRangeFix (LinearMap.mem_range_self N c), sub_self]
  have hNAdj (x y : M) : B (N x) y = B x (N y) := by
    change B (r.1 x - x) y = B x (r.1 y - y)
    simp only [map_sub, LinearMap.sub_apply, hAdj]
  have hRangeOrth {x : M} (hx : x ∈ LinearMap.range N) (c : M) : B x (N c) = 0 := by
    rw [← hNAdj]
    have hx0 : N x = 0 := by
      change r.1 x - x = 0
      rw [hRangeFix hx, sub_self]
    rw [hx0, map_zero, LinearMap.zero_apply]
  have hQNil (c : M) : Q (N c) = 0 := by
    have hc : B c (r.1 c) = 0 := by
      have h := hAlt c
      rw [map_sub, hB.self_eq_zero, sub_zero] at h
      exact h
    change Q (r.1 c - c) = 0
    rw [sub_eq_add_neg, neg_vec (F := F), QuadraticMap.map_add Q, hQ]
    change Q c + Q c + B (r.1 c) c = 0
    rw [hSym, hc, add_zero, CharTwo.add_self_eq_zero]
  intro a
  by_cases ha : N a = 0
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    intro x hx
    change x = x + B x a • N a
    rw [ha, smul_zero, add_zero]
  obtain ⟨c, hc⟩ := hNondeg (N a) ha
  have hd : B a (N c) ≠ 0 := by rwa [← hNAdj]
  let k := (1 - Q a) / B a (N c)
  let b := a + k • N c
  have hb : Q b = 1 := by
    change Q (a + k • N c) = 1
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, hQNil c, mul_zero, add_zero,
      polar_smul_right_eq]
    change Q a + ((1 - Q a) / B a (N c)) * B a (N c) = 1
    rw [div_mul_cancel₀ _ hd]
    ring
  have hNb : N b = N a := by
    change N (a + k • N c) = N a
    rw [map_add, map_smul, hNil, smul_zero, add_zero]
  have hxb {x : M} (hx : x ∈ LinearMap.range N) : B x b = B x a := by
    change B x (a + k • N c) = B x a
    rw [map_add, map_smul, hRangeOrth hx, smul_zero, add_zero]
  have hrb : Q (r.1 b) = 1 := (hQ b).trans hb
  have hOrth : B b (r.1 b) = 0 := by
    have h := hAlt b
    rw [map_sub, hB.self_eq_zero, sub_zero] at h
    exact h
  let s : TauCeti.QuadraticMap.orthogonalGroup Q :=
    ⟨reflect Q b, reflect_mem_orthogonalGroup Q b⟩
  let t : TauCeti.QuadraticMap.orthogonalGroup Q :=
    ⟨reflect Q (r.1 b), reflect_mem_orthogonalGroup Q (r.1 b)⟩
  have hs (x : M) : s.1 x = x + B x b • b := by
    change reflect Q b x = _
    rw [reflect_apply (by rw [hb]; exact one_ne_zero), hb, div_one, polar_comm,
      sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
    rfl
  have ht (x : M) : t.1 x = x + B x (r.1 b) • r.1 b := by
    change reflect Q (r.1 b) x = _
    rw [reflect_apply (by rw [hrb]; exact one_ne_zero), hrb, div_one, polar_comm,
      sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
    rfl
  have hsb : s.1 (r.1 b) = r.1 b := by
    rw [hs, hSym, hOrth, zero_smul, add_zero]
  have hConjS : r * s * r⁻¹ = t := by
    apply Subtype.ext
    exact reflect_conj r.2 b
  have hConjT : r * t * r⁻¹ = s := by
    apply Subtype.ext
    change r.1 * reflect Q (r.1 b) * r.1⁻¹ = reflect Q b
    rw [reflect_conj r.2, hRR]
  have hConjST : s * t * s⁻¹ = t := by
    apply Subtype.ext
    change s.1 * reflect Q (r.1 b) * s.1⁻¹ = reflect Q (r.1 b)
    rw [reflect_conj s.2, hsb]
  have hST : s * t = t * s := (mul_inv_eq_iff_eq_mul).mp hConjST
  let g := s * t
  have hConjG : r * g * r⁻¹ = g := by
    change r * (s * t) * r⁻¹ = s * t
    calc
      r * (s * t) * r⁻¹ = (r * s * r⁻¹) * (r * t * r⁻¹) := by group
      _ = t * s := by rw [hConjS, hConjT]
      _ = s * t := hST.symm
  refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr
    ((mul_inv_eq_iff_eq_mul.mp hConjG).symm), ?_⟩
  intro x hx
  have hxr : B x (r.1 b) = B x b := by rw [← hAdj, hRangeFix hx]
  change s.1 (t.1 x) = x + B x a • N a
  rw [ht, map_add, map_smul, hs, hsb, hxr, hxb hx]
  rw [← hNb]
  change x + B x a • b + B x a • r.1 b = x + B x a • (r.1 b - b)
  rw [sub_eq_add_neg, neg_vec (F := F), smul_add]
  dsimp only [b]
  simp only [smul_add, smul_smul]
  abel

variable [Finite F] [Finite M]

theorem pCoreOf_centralizer_fixes_displacement
    (Q : QuadraticForm F M)
    (hNondeg : ∀ w : M, w ≠ 0 → ∃ a : M, Q.polarBilin w a ≠ 0)
    (r : TauCeti.QuadraticMap.orthogonalGroup Q) (hr : r ^ 2 = 1)
    (hAlt : ∀ a : M, Q.polarBilin a (r.1 a - a) = 0) :
    ∀ g ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({r} : Set (TauCeti.QuadraticMap.orthogonalGroup Q))),
      ∀ x ∈ LinearMap.range (orthogonalRep Q r - 1), g.1 x = x := by
  apply CFSG.ClassicalGroups.AlternatingCentralizer.pCoreOf_fixes_range_of_transvections
    (orthogonalRep Q) (orthogonalRep Q r - 1) Q.polarBilin hNondeg
    (Subgroup.centralizer ({r} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)))
  · intro g hg x hx
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
    have hComm : r * g = g * r := (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
    have hVec := congrArg (fun k : TauCeti.QuadraticMap.orthogonalGroup Q => k.1 a) hComm
    change r.1 (g.1 a) = g.1 (r.1 a) at hVec
    refine LinearMap.mem_range.mpr ⟨g.1 a, ?_⟩
    change r.1 (g.1 a) - g.1 a = g.1 (r.1 a - a)
    rw [map_sub, hVec]
  · exact paired_reflection_action Q hNondeg r hr hAlt

theorem pCoreOf_centralizer_le_centralizer_of_fix_kernel
    (Q : QuadraticForm F M)
    (hNondeg : ∀ w : M, w ≠ 0 → ∃ a : M, Q.polarBilin w a ≠ 0)
    (r : TauCeti.QuadraticMap.orthogonalGroup Q) (hr : r ^ 2 = 1)
    (hAlt : ∀ a : M, Q.polarBilin a (r.1 a - a) = 0)
    (V : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hFix : ∀ v ∈ V, ∀ x ∈ LinearMap.ker (orthogonalRep Q r - 1), v.1 x = x) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({r} : Set (TauCeti.QuadraticMap.orthogonalGroup Q))) ≤
      Subgroup.centralizer (V : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have : FiniteDimensional F M := Module.Finite.of_finite
  let B : LinearMap.BilinForm F M := Q.polarBilin
  have hB : B.IsAlt := polar_isAlt Q
  have hSym (x y : M) : B x y = B y x := by
    change polar Q x y = polar Q y x
    exact polar_comm Q x y
  have hn : B.Nondegenerate := by
    constructor
    · intro x hx
      by_contra hx0
      obtain ⟨a, ha⟩ := hNondeg x hx0
      exact ha (hx a)
    · intro x hx
      by_contra hx0
      obtain ⟨a, ha⟩ := hNondeg x hx0
      exact ha ((hSym _ _).trans (hx a))
  have hrefl : B.IsRefl := by
    intro x y hxy
    rw [← hSym x y, hxy]
  have hPres (g : TauCeti.QuadraticMap.orthogonalGroup Q) (x y : M) :
      B (g.1 x) (g.1 y) = B x y := by
    have hQ (z : M) : Q (g.1 z) = Q z :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2 z
    change polar Q (g.1 x) (g.1 y) = polar Q x y
    simp only [polar, ← map_add, hQ]
  have hker : LinearMap.ker (orthogonalRep Q r - 1) =
      B.orthogonal (LinearMap.range (orthogonalRep Q r - 1)) :=
    CFSG.RankThree.GF2n.Stroth80.sec7_ker_sub_one_eq_perp_range B hn hrefl r.1 (hPres r)
  intro g hg
  apply Subgroup.mem_centralizer_iff.mpr
  intro v hv
  have hrange : LinearMap.range (CFSG.RankThree.GF2n.Stroth80.opm v.1) ≤
      LinearMap.range (orthogonalRep Q r - 1) := by
    intro z hz
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
    rw [CFSG.RankThree.GF2n.Stroth80.opm_apply]
    have h := CFSG.RankThree.GF2n.Stroth80.sub_mem_orthogonal_of_fixes B v.1 (hPres v)
      (LinearMap.ker (orthogonalRep Q r - 1)) (hFix v hv) x
    rwa [hker, B.orthogonal_orthogonal hn hrefl] at h
  have hk : B.orthogonal (LinearMap.range (orthogonalRep Q r - 1)) ≤
      LinearMap.ker (CFSG.RankThree.GF2n.Stroth80.opm v.1) := by
    intro x hx
    rw [← hker] at hx
    rw [LinearMap.mem_ker, CFSG.RankThree.GF2n.Stroth80.opm_apply, hFix v hv x hx, sub_self]
  have h := CFSG.RankThree.GF2n.Stroth80.mul_comm_of_fixes B g.1 v.1 (hPres g)
    (LinearMap.range (orthogonalRep Q r - 1))
    (fun x hx => pCoreOf_centralizer_fixes_displacement Q hNondeg r hr hAlt g hg x hx)
    hrange hk
  have hgv : g * v = v * g := Subtype.ext h
  first | exact hgv | exact hgv.symm

theorem pCoreOf_centralizer_le_centralizer_of_injective_of_fix_kernel
    {G : Type} [Group G]
    (Q : QuadraticForm F M)
    (hNondeg : ∀ w : M, w ≠ 0 → ∃ a : M, Q.polarBilin w a ≠ 0)
    (f : G →* TauCeti.QuadraticMap.orthogonalGroup Q)
    (hf : Function.Injective f) (hNormal : f.range.Normal)
    (r : G) (hr : r ^ 2 = 1)
    (hAlt : ∀ a : M, Q.polarBilin a ((f r).1 a - a) = 0)
    (V : Subgroup G)
    (hFix : ∀ v ∈ V, ∀ x : M, (f r).1 x = x → (f v).1 x = x) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ≤
      Subgroup.centralizer (V : Set G) := by
  let C := Subgroup.centralizer ({f r} : Set (TauCeti.QuadraticMap.orthogonalGroup Q))
  have hC : (Subgroup.centralizer ({r} : Set G)).map f = f.range ⊓ C := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨MonoidHom.mem_range.mpr ⟨x, rfl⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      simpa only [map_mul] using congrArg f (Subgroup.mem_centralizer_singleton_iff.mp hx)
    · rintro ⟨hg, hgr⟩
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
      refine ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      apply hf
      simpa only [map_mul] using Subgroup.mem_centralizer_singleton_iff.mp hgr
  have hN : C ≤ Subgroup.normalizer ((f.range ⊓ C : Subgroup
      (TauCeti.QuadraticMap.orthogonalGroup Q)) : Set _) := by
    let : f.range.Normal := hNormal
    have hRN : C ≤ Subgroup.normalizer (f.range : Set _) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    exact (le_inf hRN C.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hCore : (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({r} : Set G))).map f ≤
      CFSG.Open.pCoreOf 2 C := by
    rw [← CFSG.ASVolI.ChH.pCoreOf_map_of_injective 2 f hf, hC]
    exact CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 inf_le_right hN
  have hr' : (f r) ^ 2 = 1 := by rw [← map_pow, hr, map_one]
  have hFix' : ∀ v ∈ V.map f, ∀ x ∈ LinearMap.ker (orthogonalRep Q (f r) - 1),
      v.1 x = x := by
    rintro v ⟨v₀, hv₀, rfl⟩ x hx
    rw [LinearMap.mem_ker] at hx
    exact hFix v₀ hv₀ x (sub_eq_zero.mp hx)
  have hTarget := pCoreOf_centralizer_le_centralizer_of_fix_kernel
    Q hNondeg (f r) hr' hAlt (V.map f) hFix'
  intro g hg
  have hgc := hTarget (hCore (Subgroup.mem_map_of_mem f hg))
  rw [Subgroup.mem_centralizer_iff] at hgc ⊢
  intro v hv
  apply hf
  simpa only [map_mul] using hgc (f v) (Subgroup.mem_map_of_mem f hv)

end CFSG.ClassicalGroups.QuadraticCentralizer
