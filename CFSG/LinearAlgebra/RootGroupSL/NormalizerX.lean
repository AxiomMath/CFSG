module

public import CFSG.LinearAlgebra.RootGroupSL.NormalizerYW
public import CFSG.LinearAlgebra.RootGroupSL.SLFacts
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open CFSG.Open

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
  [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

private lemma flagW_coord (v : DSpace E X) :
    v ∈ flagW k E X ↔ v.2.1 = 0 ∧ v.2.2 = 0 := by
  simp [flagW, Prod.ext_iff]

private lemma flagK_coord (v : DSpace E X) :
    v ∈ flagK k E X ↔ v.2.2 = 0 := by
  simp [flagK]

private abbrev rootNorm (k E X : Type) [Field k] [Field E] [Algebra k E] [AddCommGroup X]
    [Module k X] : Subgroup (SpecialLinearGroup k (DSpace E X)) :=
  Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))

private abbrev rhoApply (n : rootNorm k E X) (v : DSpace E X) : DSpace E X :=
  SpecialLinearGroup.toLinearEquiv (n : SpecialLinearGroup k (DSpace E X)) v

private lemma pCoreOf_conj_mem {G : Type*} [Group G] (p : ℕ) {H : Subgroup G} {n o : G}
    (hn : n ∈ H) (ho : o ∈ CFSG.Open.pCoreOf p H) :
    n * o * n⁻¹ ∈ CFSG.Open.pCoreOf p H := by
  obtain ⟨h, hh, heq⟩ := Subgroup.mem_map.mp ho
  rw [← heq]
  refine Subgroup.mem_map.mpr ⟨⟨n, hn⟩ * h * ⟨n, hn⟩⁻¹, ?_, ?_⟩
  · exact (CFSG.pCore_normal (p := p) (G := ↥H)).conj_mem h hh ⟨n, hn⟩
  · rfl

private def rhoLinearMap (n : rootNorm k E X) : X →ₗ[k] X where
  toFun x := (rhoApply n (0, x, 0)).2.1
  map_add' x y := by
    have h := congrArg (fun v : DSpace E X => v.2.1)
      (map_add (SpecialLinearGroup.toLinearEquiv (n : SpecialLinearGroup k (DSpace E X)))
        (0, x, 0) (0, y, 0))
    simpa [rhoApply] using h
  map_smul' c x := by
    have h := congrArg (fun v : DSpace E X => v.2.1)
      (map_smul (SpecialLinearGroup.toLinearEquiv (n : SpecialLinearGroup k (DSpace E X)))
        c (0, x, 0))
    simpa [rhoApply] using h

private lemma rho_eq_zero (n : rootNorm k E X) (x : X)
    (h : (rhoApply n (0, x, 0)).2.1 = 0) : x = 0 := by
  have hK : (rhoApply n (0, x, 0)) ∈ flagK k E X :=
    (mem_flagK_iff_of_mem_normalizer n.2 (0, x, 0)).mpr (by rw [flagK_coord])
  have hW : (rhoApply n (0, x, 0)) ∈ flagW k E X := by
    rw [flagW_coord]
    exact ⟨h, (flagK_coord _).mp hK⟩
  have hvW : (0, x, 0) ∈ flagW k E X :=
    (mem_flagW_iff_of_mem_normalizer n.2 (0, x, 0)).mp hW
  have := (flagW_coord (0, x, 0)).mp hvW
  simpa using this.1

private lemma rho_injective (n : rootNorm k E X) :
    Function.Injective (rhoLinearMap n) := by
  intro x y hxy
  have hz : rhoLinearMap n (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h0 : x - y = 0 := rho_eq_zero n (x - y) hz
  exact sub_eq_zero.mp h0

private lemma rho_surjective (n : rootNorm k E X) :
    Function.Surjective (rhoLinearMap n) := by
  intro y
  let m : DSpace E X ≃ₗ[k] DSpace E X := SpecialLinearGroup.toLinearEquiv
    (n : SpecialLinearGroup k (DSpace E X))
  let z : DSpace E X := m.symm (0, y, 0)
  refine ⟨z.2.1, ?_⟩
  have hz : m z = (0, y, 0) := LinearEquiv.apply_symm_apply m (0, y, 0)
  have hmz : m z ∈ flagK k E X := by rw [hz, flagK_coord]
  have hzK : z ∈ flagK k E X := (mem_flagK_iff_of_mem_normalizer n.2 z).mp hmz
  have hz3 : z.2.2 = 0 := (flagK_coord z).mp hzK
  have hsplit : z = (0, z.2.1, 0) + (z.1, 0, 0) := by ext <;> simp [hz3]
  have hW : (z.1, 0, 0) ∈ flagW k E X := by
    rw [flagW_coord]; exact ⟨rfl, rfl⟩
  have hmW : m (z.1, 0, 0) ∈ flagW k E X :=
    (mem_flagW_iff_of_mem_normalizer n.2 (z.1, 0, 0)).mpr hW
  have hsec : (m (z.1, 0, 0)).2.1 = 0 := (flagW_coord _).mp hmW |>.1
  have heq : m (0, z.2.1, 0) = (0, y, 0) - m (z.1, 0, 0) := by
    have h := hz
    rw [hsplit, map_add] at h
    exact eq_sub_of_add_eq h
  have hsecond : (m (0, z.2.1, 0)).2.1 = y := by
    rw [heq]; simp [hsec]
  change (m (0, z.2.1, 0)).2.1 = y
  exact hsecond

private noncomputable def rhoEquiv (n : rootNorm k E X) : X ≃ₗ[k] X :=
  LinearEquiv.ofBijective (rhoLinearMap n) ⟨rho_injective n, rho_surjective n⟩

private lemma rhoEquiv_apply (n : rootNorm k E X) (x : X) :
    rhoEquiv n x = (rhoApply n (0, x, 0)).2.1 := rfl

private lemma rhoApply_mul (m n : rootNorm k E X) (v : DSpace E X) :
    rhoApply (m * n) v = rhoApply m (rhoApply n v) := by
  change SpecialLinearGroup.toLinearEquiv ((m : SpecialLinearGroup k (DSpace E X)) *
      (n : SpecialLinearGroup k (DSpace E X))) v = _
  rw [map_mul, LinearEquiv.mul_apply]

private lemma units_smul_one_pow (c : kˣ) (n : ℕ) :
    ((c : kˣ) • (1 : X ≃ₗ[k] X)) ^ n = (c ^ n : kˣ) • (1 : X ≃ₗ[k] X) := by
  induction n with
  | zero =>
    ext x
    simp [LinearEquiv.smul_apply]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    ext x
    simp [LinearEquiv.mul_apply, LinearEquiv.smul_apply, smul_smul, Units.val_mul, mul_comm]

private noncomputable def rhoHom : rootNorm k E X →* (X ≃ₗ[k] X) where
  toFun := rhoEquiv
  map_one' := by
    ext x
    simp [rhoEquiv_apply]
  map_mul' m n := by
    ext x
    rw [LinearEquiv.mul_apply, rhoEquiv_apply, rhoEquiv_apply, rhoEquiv_apply, rhoApply_mul]
    set w : DSpace E X := rhoApply n (0, x, 0) with hw
    have hwK : w ∈ flagK k E X :=
      (mem_flagK_iff_of_mem_normalizer n.2 (0, x, 0)).mpr (by rw [flagK_coord])
    have hw3 : w.2.2 = 0 := (flagK_coord w).mp hwK
    have hsplit : w = (0, w.2.1, 0) + (w.1, 0, 0) := by ext <;> simp [hw3]
    have hW : (w.1, 0, 0) ∈ flagW k E X := by rw [flagW_coord]; exact ⟨rfl, rfl⟩
    have hmW : rhoApply m (w.1, 0, 0) ∈ flagW k E X :=
      (mem_flagW_iff_of_mem_normalizer m.2 (w.1, 0, 0)).mpr hW
    have hsec : (rhoApply m (w.1, 0, 0)).2.1 = 0 :=
      (flagW_coord _).mp hmW |>.1
    conv_lhs => rw [hsplit]
    rw [show rhoApply m ((0, w.2.1, 0) + (w.1, 0, 0)) =
        rhoApply m (0, w.2.1, 0) + rhoApply m (w.1, 0, 0) from
      map_add (SpecialLinearGroup.toLinearEquiv (m : SpecialLinearGroup k (DSpace E X)))
        (0, w.2.1, 0) (w.1, 0, 0)]
    simp only [Prod.fst_add, Prod.snd_add]
    rw [hsec, add_zero]

private lemma blockSL_one_det (s : SpecialLinearGroup k X) :
    LinearEquiv.det (1 : E ≃ₗ[k] E) *
        LinearEquiv.det (SpecialLinearGroup.toLinearEquiv s) *
        LinearEquiv.det (1 : E ≃ₗ[k] E) = 1 := by
  simpa only [map_one, one_mul, mul_one, SpecialLinearGroup.toLinearEquiv_eq_coe] using s.2

private lemma blockSL_one_mem_rootNorm (s : SpecialLinearGroup k X) :
    blockSL (1 : E ≃ₗ[k] E) (SpecialLinearGroup.toLinearEquiv s) (1 : E ≃ₗ[k] E)
      (blockSL_one_det s) ∈ rootNorm k E X := by
  rw [rootNorm, blockSL_mem_normalizer_iff]
  intro t
  exact ⟨t, by ext x; rfl⟩

private noncomputable def blockOfSL (s : SpecialLinearGroup k X) : rootNorm k E X :=
  ⟨blockSL (1 : E ≃ₗ[k] E) (SpecialLinearGroup.toLinearEquiv s) (1 : E ≃ₗ[k] E)
    (blockSL_one_det s), blockSL_one_mem_rootNorm s⟩

private lemma rhoHom_blockSL_rootNorm (s : SpecialLinearGroup k X) :
    rhoHom (blockOfSL (E := E) s) = SpecialLinearGroup.toLinearEquiv s := by
  ext x
  simp [blockOfSL, rhoHom, rhoEquiv_apply, blockSL, blockDiag]

private noncomputable def rhoY (O : Subgroup (SpecialLinearGroup k (DSpace E X))) :
    Subgroup (X ≃ₗ[k] X) :=
  (O.subgroupOf (rootNorm k E X)).map (rhoHom (k := k) (E := E) (X := X))

private noncomputable def rhoP (O : Subgroup (SpecialLinearGroup k (DSpace E X))) :
    Subgroup (SpecialLinearGroup k X) :=
  (rhoY O).comap SpecialLinearGroup.toLinearEquiv

private lemma rho_conj_mem (n : rootNorm k E X) {y : X ≃ₗ[k] X}
    (hy : y ∈ rhoY (pCoreOf 2 (rootNorm k E X))) :
    rhoHom n * y * (rhoHom n)⁻¹ ∈ rhoY (pCoreOf 2 (rootNorm k E X)) := by
  obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.mp hy
  have hconj : n * o * n⁻¹ ∈
      (pCoreOf 2 (rootNorm k E X)).subgroupOf (rootNorm k E X) := by
    rw [Subgroup.mem_subgroupOf]
    exact pCoreOf_conj_mem 2 n.2 (Subgroup.mem_subgroupOf.mp ho)
  refine Subgroup.mem_map.mpr ⟨n * o * n⁻¹, hconj, ?_⟩
  simp only [map_mul, map_inv]

private lemma rhoY_pCoreOf_rootN_eq_bot (hX : 0 < Module.finrank k X) :
    rhoY (pCoreOf 2 (rootNorm k E X)) = ⊥ := by
  let O := pCoreOf 2 (rootNorm k E X)
  let Y := rhoY O
  have hOp : IsPGroup 2 O :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(rootNorm k E X))).map (rootNorm k E X).subtype
  have hYp : IsPGroup 2 Y := (hOp.comap_subtype (K := rootNorm k E X)).map rhoHom
  have hPp : IsPGroup 2 (rhoP O) :=
    hYp.comap_of_injective SpecialLinearGroup.toLinearEquiv
      SpecialLinearGroup.toLinearEquiv_injective
  have hPnormal : (rhoP O).Normal := by
    refine ⟨fun p hp s => ?_⟩
    have hp' : SpecialLinearGroup.toLinearEquiv p ∈ Y := hp
    have hbρ : rhoHom (blockOfSL (E := E) s) = SpecialLinearGroup.toLinearEquiv s :=
      rhoHom_blockSL_rootNorm s
    show SpecialLinearGroup.toLinearEquiv (s * p * s⁻¹) ∈ Y
    rw [map_mul, map_mul, map_inv, ← hbρ]
    exact rho_conj_mem (blockOfSL (E := E) s) hp'
  have hPle : rhoP O ≤ CFSG.pCore 2 (SpecialLinearGroup k X) := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (rhoP O) (le_iSup_of_le hPnormal (le_iSup_of_le hPp le_rfl))
  have hPbot : rhoP O = ⊥ := by
    rw [eq_bot_iff, ← pCore_two_specialLinearGroup_eq_bot']
    exact hPle
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hcomm : ∀ s : SpecialLinearGroup k X,
      y * SpecialLinearGroup.toLinearEquiv s = SpecialLinearGroup.toLinearEquiv s * y := by
    intro s
    have hbρ : rhoHom (blockOfSL (E := E) s) = SpecialLinearGroup.toLinearEquiv s :=
      rhoHom_blockSL_rootNorm s
    have hnorm : rhoHom (blockOfSL (E := E) s) * y * (rhoHom (blockOfSL (E := E) s))⁻¹ ∈ Y :=
      rho_conj_mem (blockOfSL (E := E) s) hy
    have hcomY : y * SpecialLinearGroup.toLinearEquiv s * y⁻¹ *
        (SpecialLinearGroup.toLinearEquiv s)⁻¹ ∈ Y := by
      rw [← hbρ]
      have hrew : y * rhoHom (blockOfSL (E := E) s) * y⁻¹ * (rhoHom (blockOfSL (E := E) s))⁻¹ =
          y * (rhoHom (blockOfSL (E := E) s) * y * (rhoHom (blockOfSL (E := E) s))⁻¹)⁻¹ := by group
      rw [hrew]
      exact mul_mem hy (inv_mem hnorm)
    let t : SpecialLinearGroup k X :=
      ⟨y * SpecialLinearGroup.toLinearEquiv s * y⁻¹ * (SpecialLinearGroup.toLinearEquiv s)⁻¹,
        by simp [map_mul, map_inv, SpecialLinearGroup.toLinearEquiv_eq_coe, s.2]⟩
    have htP : t ∈ rhoP O :=
      Subgroup.mem_comap.mpr (show SpecialLinearGroup.toLinearEquiv t ∈ Y from hcomY)
    have ht1 : t = 1 := Subgroup.mem_bot.mp (hPbot ▸ htP)
    have hthis : y * SpecialLinearGroup.toLinearEquiv s * y⁻¹ *
        (SpecialLinearGroup.toLinearEquiv s)⁻¹ = 1 := by
      have := congrArg Subtype.val ht1
      simpa [t] using this
    have hs1 : y * SpecialLinearGroup.toLinearEquiv s * y⁻¹ =
        SpecialLinearGroup.toLinearEquiv s := by
      have := congrArg (· * SpecialLinearGroup.toLinearEquiv s) hthis
      simpa [mul_assoc] using this
    have hs2 : y * SpecialLinearGroup.toLinearEquiv s =
        SpecialLinearGroup.toLinearEquiv s * y := by
      have := congrArg (· * y) hs1
      simpa [mul_assoc] using this
    exact hs2
  obtain ⟨c, hc⟩ := exists_smul_of_commute_specialLinearGroup y hcomm
  obtain ⟨a, ha⟩ := hYp ⟨y, hy⟩
  have ha' : y ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hy_eq : y = (c : kˣ) • (1 : X ≃ₗ[k] X) := by
    ext x
    simpa [LinearEquiv.smul_apply] using hc x
  have hpow : ((c : kˣ) • (1 : X ≃ₗ[k] X)) ^ 2 ^ a =
      (c ^ 2 ^ a : kˣ) • (1 : X ≃ₗ[k] X) :=
    units_smul_one_pow c (2 ^ a)
  have h1 : (c ^ 2 ^ a : kˣ) • (1 : X ≃ₗ[k] X) = 1 := by
    rw [← hpow, ← hy_eq]
    exact ha'
  have hc_pow : (c ^ 2 ^ a : kˣ) = 1 := by
    haveI : Nontrivial X := Module.nontrivial_of_finrank_pos hX
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    have happ : (c ^ 2 ^ a : k) • x = x := by
      have := congrArg (fun e : X ≃ₗ[k] X => e x) h1
      simpa [LinearEquiv.smul_apply] using this
    have hzero : ((c ^ 2 ^ a : k) - 1) • x = 0 := by
      rw [sub_smul, one_smul, happ, sub_self]
    have hsub : (c ^ 2 ^ a : k) - 1 = 0 := (smul_eq_zero.mp hzero).resolve_right hx
    exact Units.ext (sub_eq_zero.mp hsub)
  have hc1 : c = 1 := by
    have hc_pow_k : (c : k) ^ 2 ^ a = 1 := by
      have := congrArg Units.val hc_pow
      simpa using this
    have hfrob : ((c : k) - 1) ^ 2 ^ a = 0 := by
      rw [sub_pow_char_pow, hc_pow_k]
      simp
    have hsub : (c : k) - 1 = 0 := (pow_eq_zero_iff (n := 2 ^ a) (by positivity)).mp hfrob
    exact Units.ext (sub_eq_zero.mp hsub)
  rw [hy_eq, hc1]
  ext x
  simp [LinearEquiv.smul_apply]

theorem pCoreOf_normalizer_trivial_on_flagK (hX : 0 < Module.finrank k X)
    {g : SpecialLinearGroup k (DSpace E X)}
    (hg : g ∈ pCoreOf 2
      (Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))))
    (v : DSpace E X) (hv : v ∈ flagK k E X) : g v - v ∈ flagW k E X := by
  have hYbot := rhoY_pCoreOf_rootN_eq_bot (k := k) (E := E) (X := X) hX
  have hgN : g ∈ rootNorm k E X :=
    Subgroup.map_subtype_le (CFSG.pCore 2 ↥(rootNorm k E X)) hg
  have hρg : rhoHom (⟨g, hgN⟩ : rootNorm k E X) = 1 := by
    have hmemO : (⟨g, hgN⟩ : rootNorm k E X) ∈
        (pCoreOf 2 (rootNorm k E X)).subgroupOf (rootNorm k E X) := by
      rw [Subgroup.mem_subgroupOf]
      exact hg
    have hmem : rhoHom (⟨g, hgN⟩ : rootNorm k E X) ∈
        rhoY (pCoreOf 2 (rootNorm k E X)) :=
      Subgroup.mem_map.mpr ⟨⟨g, hgN⟩, hmemO, rfl⟩
    rw [hYbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hρg_fun : ∀ x : X,
      ((g : DSpace E X ≃ₗ[k] DSpace E X) (0, x, 0)).2.1 = x := by
    intro x
    have h := congrArg (fun e : X ≃ₗ[k] X => e x) hρg
    simpa [rhoHom, rhoEquiv_apply] using h
  have hv3 : v.2.2 = 0 := (flagK_coord v).mp hv
  set a : DSpace E X := (v.1, 0, 0) with ha
  set b : DSpace E X := (0, v.2.1, 0) with hb
  have hvsplit : v = a + b := by rw [ha, hb]; ext <;> simp [hv3]
  have haW : a ∈ flagW k E X := by rw [ha, flagW_coord]; exact ⟨rfl, rfl⟩
  have hgaW : (g : SpecialLinearGroup k (DSpace E X)) a ∈ flagW k E X :=
    (mem_flagW_iff_of_mem_normalizer hgN a).mpr haW
  have hsecW : ((g : SpecialLinearGroup k (DSpace E X)) a).2.1 = 0 :=
    (flagW_coord _).mp hgaW |>.1
  have hgaW3 : ((g : SpecialLinearGroup k (DSpace E X)) a).2.2 = 0 :=
    (flagW_coord _).mp hgaW |>.2
  have hbK : b ∈ flagK k E X := by rw [hb, flagK_coord]
  have hgbK : (g : SpecialLinearGroup k (DSpace E X)) b ∈ flagK k E X :=
    (mem_flagK_iff_of_mem_normalizer hgN b).mpr hbK
  have hgbK3 : ((g : SpecialLinearGroup k (DSpace E X)) b).2.2 = 0 :=
    (flagK_coord _).mp hgbK
  have hsec0 : ((g : SpecialLinearGroup k (DSpace E X)) b).2.1 = b.2.1 := by
    simpa [hb] using hρg_fun v.2.1
  have ha1 : a.2.1 = 0 := by rw [ha]
  have ha2 : a.2.2 = 0 := by rw [ha]
  have hb2 : b.2.2 = 0 := by rw [hb]
  have h1 : (g : SpecialLinearGroup k (DSpace E X)) a - a ∈ flagW k E X := by
    rw [flagW_coord]
    exact ⟨by simp [hsecW, ha1], by simp [hgaW3, ha2]⟩
  have h2 : (g : SpecialLinearGroup k (DSpace E X)) b - b ∈ flagW k E X := by
    rw [flagW_coord]
    exact ⟨by simp [hsec0], by simp [hgbK3, hb2]⟩
  have hgv : (g : SpecialLinearGroup k (DSpace E X)) v - v =
      ((g : SpecialLinearGroup k (DSpace E X)) a - a) +
      ((g : SpecialLinearGroup k (DSpace E X)) b - b) := by
    change (g : DSpace E X ≃ₗ[k] DSpace E X) v - v =
      ((g : DSpace E X ≃ₗ[k] DSpace E X) a - a) +
      ((g : DSpace E X ≃ₗ[k] DSpace E X) b - b)
    rw [hvsplit, map_add]
    abel
  rw [hgv]
  exact add_mem h1 h2

theorem pCoreOf_normalizer_le_QK (hX : 0 < Module.finrank k X) :
    pCoreOf 2 (Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))) ≤
      QK k E X := by
  intro g hg
  rw [mem_QK_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact pCoreOf_normalizer_trivial_on_flagW hX hg v hv
  · intro v hv
    exact pCoreOf_normalizer_trivial_on_flagK hX hg v hv
  · intro v
    exact pCoreOf_normalizer_trivial_on_quotient hX hg v

theorem pCoreOf_normalizer_rootSL (hX : 0 < Module.finrank k X) :
    pCoreOf 2 (Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))) =
      QK k E X :=
  le_antisymm (pCoreOf_normalizer_le_QK hX) QK_le_pCoreOf_normalizer

end CFSG.LinearAlgebra.RootGroupSL
