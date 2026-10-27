module

public import CFSG.GH74.Generic.BProg.B3.S3L3Defs
public import CFSG.GH74.Generic.BProg.B3.S3L3Lift
public import CFSG.GH74.Generic.BProg.B3.S3FusionCtx

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3.S3Fusion CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace S3L3Facts

section Unpack

variable {x y : G} {K A : Subgroup G}

theorem ord_x (h : Setup30 G x K A y) : orderOf x = 2 := h.circ.1.1.1.1

theorem pcomp (h : Setup30 G x K A y) : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) K :=
  h.circ.1.1.1.2.2

theorem y_mem_K (h : Setup30 G x K A y) : y ∈ K := (Subgroup.mem_inf.1 h.y_mem).2

theorem y_mem_A (h : Setup30 G x K A y) : y ∈ A := (Subgroup.mem_inf.1 h.y_mem).1

theorem barShape (h : Setup30 G x K A y) :
    BarShape (CentralizerBar x) (xbar x) (S3.imgBar x K) :=
  barShape_of_ctx h.hyp.gen4 (ord_x h) (pcomp h) h.shape h.rank1

end Unpack

theorem exists_conj_ge {D T₀ A : Subgroup G} (hT₀ : IsSylowOf 2 T₀ D) (hAD : A ≤ D)
    (hA : IsPGroup 2 ↥A) : ∃ g ∈ D, A ≤ T₀.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hQ₀⟩ := hT₀
  obtain ⟨S, hS⟩ := (hA.comap_subtype (K := D)).exists_le_sylow
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D Q₀ S
  refine ⟨d, d.2, fun a ha => ?_⟩
  have h1 : (⟨a, hAD ha⟩ : ↥D) ∈ (S : Subgroup ↥D) := hS ha
  rw [← hd, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨q, hq, hqa⟩ := h1
  refine ⟨(q : G), ?_, ?_⟩
  · rw [← hQ₀]
    exact ⟨q, hq, rfl⟩
  · have := congrArg Subtype.val hqa
    simpa [MulAut.smul_def, MulAut.conj_apply] using this

omit [Finite G] in
theorem piC_commutator (x : G) {a b : G} (ha : a ∈ centralizer ({x} : Set G))
    (hb : b ∈ centralizer ({x} : Set G)) : piC x ⁅a, b⁆ = ⁅piC x a, piC x b⁆ := by
  have hab : a * b ∈ centralizer ({x} : Set G) := mul_mem ha hb
  have hai : a⁻¹ ∈ centralizer ({x} : Set G) := inv_mem ha
  have hbi : b⁻¹ ∈ centralizer ({x} : Set G) := inv_mem hb
  rw [commutatorElement_def, commutatorElement_def, piC_mul x (mul_mem hab hai) hbi,
    piC_mul x hab hai, piC_mul x ha hb, piC_inv x ha, piC_inv x hb]

end S3L3Facts

theorem Setup30.layer {x y : G} {K A : Subgroup G} (h : Setup30 G x K A y) :
    IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) (Ly K y) ∧ y ∈ Ly K y ∧
      HasSL2Model (↥(Ly K y) ⧸ pPrimeCore 2 ↥(Ly K y)) (fun q => Odd q ∧ 5 ≤ q) := by
  have hy := h.y_ord
  obtain ⟨F, hF, hFin, S, hS, -⟩ :=
    S3L3Lift.exists_layerHyp (S3L3Facts.pcomp h) (S3L3Facts.y_mem_K h) hy (S3L3Facts.barShape h)
  obtain ⟨L, hL, -⟩ := hS.exists_comp hy
  have hLy : Ly K y = L := hS.pLayerOf_eq hy hL
  refine ⟨by rw [hLy]; exact hL, hS.mem_layer hy, ?_⟩
  obtain ⟨ψ, hψs, hψk, -⟩ := hS.psi_data hy hL
  obtain ⟨e⟩ := hS.equiv
  rw [hLy]
  refine ⟨F, hF, hFin, ⟨hS.odd, ?_⟩, ⟨?_⟩⟩
  · have h4 := hS.big
    obtain ⟨k, hk⟩ := hS.odd
    omega
  · exact ((QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)).trans
        (e.trans (specialLinearGroupEquivStatedSL 2 F))

theorem Setup30.exists_T {x y : G} {K A : Subgroup G} (h : Setup30 G x K A y) :
    ∃ T : Subgroup G, IsZT x y T ∧ A ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx := S3L3Facts.ord_x h
  have hy := h.y_ord
  obtain ⟨T₀, hT₀S, hxT₀, hyT₀, hT₀y, hT₀Z⟩ :=
    S3Fusion.exists_T (S3L3Facts.barShape h) hx (S3L3Facts.pcomp h) (S3L3Facts.y_mem_K h) hy
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set D : Subgroup G := C ⊓ centralizer ({y} : Set G) with hD
  have hT₀D : T₀ ≤ D := fun t ht =>
    Subgroup.mem_inf.2 ⟨hT₀S.le ht, Subgroup.mem_centralizer_singleton_iff.2 (hT₀y t ht)⟩
  have hT₀SD : IsSylowOf 2 T₀ D := hT₀S.of_le hT₀D inf_le_left
  have hAC : A ≤ C := h.src.1
  have hel : CFSG.IsElementaryAbelian 2 ↥A := h.src.2.1
  have hAD : A ≤ D := fun a ha =>
    Subgroup.mem_inf.2 ⟨hAC ha, Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥A) ⟨y, S3L3Facts.y_mem_A h⟩))⟩
  have hA2 : IsPGroup 2 ↥A := IsPGroup.of_card (n := 3) (by rw [h.src.2.2.1]; norm_num)
  obtain ⟨g, hgD, hAg⟩ := S3L3Facts.exists_conj_ge hT₀SD hAD hA2
  have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hgD).1
  have hgy : g * y = y * g := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hgD).2
  have hgC : g ∈ C := (Subgroup.mem_inf.1 hgD).1
  set c : MulAut G := MulAut.conj g with hc
  have cx : c x = x := by
    rw [hc, MulAut.conj_apply, hgx, mul_inv_cancel_right]
  have cy : c y = y := by
    rw [hc, MulAut.conj_apply, hgy, mul_inv_cancel_right]
  set T : Subgroup G := T₀.map c.toMonoidHom with hT
  have hTle : T ≤ C := by
    rintro _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, hc, MulAut.conj_apply]
    exact C.mul_mem (C.mul_mem hgC (hT₀S.le ht)) (C.inv_mem hgC)
  have hTcard : Nat.card T = 2 ^ (Nat.card C).factorization 2 := by
    rw [hT, Subgroup.card_map_of_injective c.injective]
    exact hT₀S.card_eq
  have hTS : IsSylowOf 2 T C := isSylowOf_of_card hTle hTcard
  refine ⟨T, ⟨hTS, ⟨x, hxT₀, cx⟩, ⟨y, hyT₀, cy⟩, ?_, ?_⟩, hAg⟩
  · rintro _ ⟨t, ht, rfl⟩
    show c t * y = y * c t
    calc c t * y = c t * c y := by rw [cy]
      _ = c (t * y) := (map_mul c t y).symm
      _ = c (y * t) := by rw [hT₀y t ht]
      _ = c y * c t := map_mul c y t
      _ = y * c t := by rw [cy]
  · rintro _ ⟨z₀, hz₀, rfl⟩ hzc hz2
    show c z₀ = 1 ∨ c z₀ = x ∨ c z₀ = y ∨ c z₀ = x * y
    have hcen : ∀ a ∈ T₀, a * z₀ = z₀ * a := by
      intro a ha
      have := hzc (c a) ⟨a, ha, rfl⟩
      apply c.injective
      rw [map_mul, map_mul]
      exact this
    have hsq : z₀ * z₀ = 1 := by
      apply c.injective
      rw [map_mul, map_one]
      exact hz2
    have hxy : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1
        (hC ▸ (S3L3Facts.pcomp h).1 (S3L3Facts.y_mem_K h))
    rcases hT₀Z z₀ hz₀ hcen hsq with h1 | h1 | h1 | h1
    · left; rw [h1, map_one]
    · right; left; rw [h1, cx]
    · right; right; left; rw [h1, cy]
    · right; right; right
      rw [h1, map_mul, cy, cx, ← hxy]

theorem Setup30.omega_CTL {x y : G} {K A T : Subgroup G} (h : Setup30 G x K A y) (hT : IsZT x y T) :
    ∀ t ∈ T, t ∈ centralizerSection (Ly K y) (pPrimeCoreOf 2 (Ly K y)) → t * t = 1 →
      t = 1 ∨ t = x ∨ t = y ∨ t = x * y := by
  intro t htT htc ht2
  have hy := h.y_ord
  have hK := S3L3Facts.pcomp h
  have hyK := S3L3Facts.y_mem_K h
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hshape := S3L3Facts.barShape h
  obtain ⟨F, hF, hFin, S, hS, hB4⟩ := S3L3Lift.exists_layerHyp hK hyK hy hshape
  obtain ⟨L, hL, -⟩ := hS.exists_comp hy
  have hLy : Ly K y = L := hS.pLayerOf_eq hy hL
  rw [hLy] at htc
  obtain ⟨ψ, hψs, hψk, hψc⟩ := hS.psi_data hy hL
  obtain ⟨hTS, hxT, hyT, hTy, -⟩ := hT
  have hTC : T ≤ centralizer ({x} : Set G) := hTS.le
  have hTp : IsPGroup 2 ↥T := hTS.isPGroup
  have htC : t ∈ centralizer ({x} : Set G) := hTC htT
  have hyC : y ∈ centralizer ({x} : Set G) := hKC hyK
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  have hinj : ∀ a ∈ T, ∀ b ∈ T, piC x a = piC x b → a = b := by
    intro a ha b hb hab
    have h1 : piC x (a⁻¹ * b) = 1 := by
      rw [piC_mul x (hTC (T.inv_mem ha)) (hTC hb), piC_inv x (hTC ha), hab, inv_mul_cancel]
    have := eq_one_of_piC_eq_one hTp hTC (T.mul_mem (T.inv_mem ha) hb) h1
    exact inv_mul_eq_one.mp this
  set tb : CentralizerBar x := piC x t with htb
  set yb : CentralizerBar x := piC x y with hyb
  have htb2 : tb * tb = 1 := by rw [htb, ← piC_mul x htC htC, ht2, piC_one]
  have hyb2 : yb * yb = 1 := by rw [hyb, ← piC_mul x hyC hyC, hy2, piC_one]
  have hty : tb * yb = yb * tb := by
    rw [htb, hyb, ← piC_mul x htC hyC, ← piC_mul x hyC htC, hTy t htT]
  have hybinv : yb⁻¹ = yb := inv_eq_of_mul_eq_one_right hyb2
  have htbinv : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right htb2
  have hcent : ∀ s ∈ S, (s : CentralizerBar x) * tb = tb * (s : CentralizerBar x) := by
    intro s hs
    obtain ⟨⟨l, hl⟩, hls⟩ := hψs ⟨s, hs⟩
    have hs_eq : (s : CentralizerBar x) = piC x l := by
      rw [← hψc l hl, hls]
    have hlC : l ∈ centralizer ({x} : Set G) := hKC (Subgroup.mem_inf.1 (hL.1 hl)).1
    have hc1 : ⁅l, t⁆ ∈ pPrimeCoreOf 2 L := htc.2.2 l hl
    have h1 : piC x ⁅l, t⁆ = 1 := by
      obtain ⟨z, hz, hzv⟩ := hc1
      have hzk : z ∈ ψ.ker := hψk ▸ hz
      have h2 := hψc (z : G) z.2
      have h3 : ψ ⟨(z : G), z.2⟩ = 1 := hzk
      rw [h3] at h2
      rw [← hzv]
      exact h2.symm
    rw [S3L3Facts.piC_commutator x hlC htC, ← hs_eq, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hKn : (S3.imgBar x K).Normal := hshape.normal
  set σ : MulAut ↥(S3.imgBar x K) := MulAut.conjNormal (H := S3.imgBar x K) tb with hσ
  have hσσ : σ * σ = 1 := by
    rw [hσ, ← map_mul, htb2, map_one]
  have hσS : ∀ s ∈ S, σ s = s := by
    intro s hs
    apply Subtype.ext
    rw [hσ, MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
    exact (hcent s hs).symm
  rcases hB4 σ hσσ hσS with hσ1 | hσ2
  · have hcentK : tb ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
        Set (CentralizerBar x)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := congrArg (fun τ : MulAut ↥(S3.imgBar x K) =>
        ((τ ⟨k, hk⟩ : ↥(S3.imgBar x K)) : CentralizerBar x)) hσ1
      simp only [hσ, MulAut.conjNormal_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    by_cases h1 : tb = 1
    · left
      exact hinj t htT 1 T.one_mem (by rw [piC_one]; exact h1)
    · right; left
      have h2 := hshape.only tb hcentK (orderOf_eq_prime (by rw [sq]; exact htb2) h1)
      exact hinj t htT x hxT (by rw [piC_x]; exact h2)
  · have hcentK : yb * tb ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
        Set (CentralizerBar x)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := congrArg (fun τ : MulAut ↥(S3.imgBar x K) =>
        ((τ ⟨k, hk⟩ : ↥(S3.imgBar x K)) : CentralizerBar x)) hσ2
      simp only [hσ, MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        S3L3Lift.yK_coe, ← hyb, hybinv, htbinv] at this
      calc k * (yb * tb) = (yb * yb) * k * (yb * tb) := by rw [hyb2, one_mul]
        _ = yb * (yb * k * yb) * tb := by simp only [mul_assoc]
        _ = yb * (tb * k * tb) * tb := by rw [← this]
        _ = yb * tb * k * (tb * tb) := by simp only [mul_assoc]
        _ = yb * tb * k := by rw [htb2, mul_one]
    have hc2 : (yb * tb) * (yb * tb) = 1 := by
      calc yb * tb * (yb * tb) = yb * (tb * yb) * tb := by simp only [mul_assoc]
        _ = yb * (yb * tb) * tb := by rw [hty]
        _ = (yb * yb) * (tb * tb) := by simp only [mul_assoc]
        _ = 1 := by rw [hyb2, htb2, mul_one]
    by_cases h1 : yb * tb = 1
    · right; right; left
      have h2 : tb = yb := by
        have : tb = yb⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this, hybinv]
      exact hinj t htT y hyT h2
    · right; right; right
      have h2 := hshape.only (yb * tb) hcentK (orderOf_eq_prime (by rw [sq]; exact hc2) h1)
      have h3 : tb = yb * xbar x := by
        have : tb = yb⁻¹ * (yb * tb) := by group
        rw [this, h2, hybinv]
      refine hinj t htT (x * y) (T.mul_mem hxT hyT) ?_
      rw [piC_mul x (show x ∈ centralizer ({x} : Set G) from
        Subgroup.mem_centralizer_singleton_iff.2 rfl) hyC, piC_x, ← hyb]
      exact h3.trans (hshape.xh_cent yb)

end CFSG.GH74.Generic.BProg.B3
