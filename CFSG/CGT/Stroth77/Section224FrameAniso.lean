module

public import CFSG.CGT.Stroth77.DeviationGenericFamilyOne
public import CFSG.CGT.Stroth77.DeviationGenericAniso
public import CFSG.CGT.Stroth77.Section226Bridge
public import CFSG.CGT.Stroth77.Stroth34Frame
public import CFSG.CGT.Stroth77.Section223Layer
public import CFSG.CGT.Stroth77.StrothFrameAmbient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J4SBinary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace DeviationGeneric

open Stroth225Frame Stroth224Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

variable {G : Type} [Group G] [Finite G] {S D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

theorem mem_omegaIn_one_of_inverted (hfam : τ.m + 1 = τ.n) (hk : ∀ i, 2 ≤ τ.k i) {y : G}
    (hy : y ∈ 𝓡[S, D])
    (hf : devMat dD hk y hy 0 0 = 0 ∧ devMat dD hk y hy 0 1 = 0 ∧ devMat dD hk y hy 0 2 = 0)
    {d : G} (hd : d ∈ D) (hinv : y * d * y⁻¹ = d⁻¹) : d ∈ omegaIn 1 D := by
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => comm_of_mem dD ha hb
  have hmem := commutator_mem_omegaIn_one dD hy hd
  have hval := devMat_val_eq (dD := dD) hk y hy ⟨d, hd⟩
  have h0 : barD dD hk ⟨d, hd⟩ 0 = 0 := by
    have he : (2 : ℕ) * dD.e (Additive.ofMul (⟨d, hd⟩ : D)) 0 = 0 := by
      have h3 := congrArg (fun v : Torus τ.k => v 0) hval
      simp only at h3
      rw [torusHalf_mulVec_zero_of_row_zero _ hf] at h3
      have hcd : (⟨y * (d : G) * y⁻¹ * (d : G)⁻¹,
          omegaIn_le 1 D (commutator_mem_omegaIn_one dD hy hd)⟩ : D) =
          (⟨d, hd⟩ * ⟨d, hd⟩)⁻¹ := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hinv]; group)
      rw [hcd, ofMul_inv, ofMul_mul, map_neg, map_add, Pi.neg_apply, Pi.add_apply,
        neg_eq_zero] at h3
      rw [← h3]
      push_cast
      ring
    obtain ⟨z, hz⟩ := exists_two_mul_of_two_mul_eq_zero (hk 0) he
    rw [barD, torusBar_apply, ← hz]
    push_cast
    rw [ZMod.cast_mul (dvd_pow_self 2 (by have := hk 0; omega)),
      show ((2 : ZMod (2 ^ τ.k 0)).cast : ZMod 2) = 0 from by
        rw [show (2 : ZMod (2 ^ τ.k 0)) = ((2 : ℕ) : ZMod (2 ^ τ.k 0)) by norm_cast,
          ZMod.cast_natCast (dvd_pow_self 2 (by have := hk 0; omega))]
        decide, zero_mul]
  rw [hinv] at hmem
  have hd4 : (⟨d, hd⟩ : D) ^ 4 = 1 := by
    have h4 := ((mem_omegaIn_iff_of_comm hcomm).mp hmem).2
    have h5 : ((d : G)⁻¹ * (d : G)⁻¹) ^ 2 = ((d : G) ^ 4)⁻¹ := by group
    rw [pow_one, h5] at h4
    exact Subtype.ext (by simpa using inv_eq_one.mp h4)
  have hkk := familyOne_k hfam
  have hk0 := hk 0
  have hk3 : 3 ≤ τ.k 1 := by rw [hkk] at hk0 ⊢; simp at hk0 ⊢; omega
  have hk3' : 3 ≤ τ.k 2 := by rw [hkk] at hk0 ⊢; simp at hk0 ⊢; omega
  obtain ⟨h1, h2⟩ := barD_of_pow_four hk hk3 hk3' hd4
  have hbar : barD dD hk ⟨d, hd⟩ = 0 := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hdM := (barD_eq_zero_iff hk ⟨d, hd⟩).mp hbar
  have hyd := Subgroup.mem_centralizer_iff.mp (mem_centralizer_of_mem_R hy) d hdM
  have hdd : d = d⁻¹ := by
    calc d = y * d * y⁻¹ := by rw [← hyd]; group
      _ = d⁻¹ := hinv
  refine mem_omegaIn_one_of_mul_self hd ?_
  calc d * d = d * d⁻¹ := by rw [← hdd]
    _ = 1 := mul_inv_cancel d

theorem exists_conj_mul_eq_of_row_zero (hfam : τ.m + 1 = τ.n) (dD : StrothWeakTypeData D τ)
    (hk : ∀ i, 2 ≤ τ.k i) {y : G} (hy : y ∈ 𝓡[S, D])
    (hf : devMat dD hk y hy 0 0 = 0 ∧ devMat dD hk y hy 0 1 = 0 ∧ devMat dD hk y hy 0 2 = 0)
    {e : G} (he : e ∈ mhoOne D) : ∃ d ∈ D, y⁻¹ * d * y * d = e := by
  have hω := omegaIn_one_le_mhoOne dD hk
  have hyN : y ∈ Subgroup.normalizer (D : Set G) := mem_normalizer_of_mem_R hy
  have hyiN : y⁻¹ ∈ Subgroup.normalizer (D : Set G) := inv_mem hyN
  have hconjD : ∀ d ∈ D, y⁻¹ * d * y ∈ D := fun d hd => by
    simpa using (Subgroup.mem_normalizer_iff.mp hyiN d).mp hd
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => comm_of_mem dD ha hb
  let θ : D →* D :=
    { toFun := fun d => ⟨y⁻¹ * d * y * d, D.mul_mem (hconjD d d.2) d.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hab' : (a : G) * (b : G) = (b : G) * (a : G) := hcomm a a.2 b b.2
        have hc1 := hcomm (y⁻¹ * b * y * b) (D.mul_mem (hconjD b b.2) b.2) a a.2
        simp only [Subgroup.coe_mul]
        calc y⁻¹ * (a * b) * y * (a * b) = (y⁻¹ * a * y) * (y⁻¹ * b * y) * (a * b) := by group
          _ = (y⁻¹ * a * y) * (y⁻¹ * b * y) * (b * a) := by rw [hab']
          _ = y⁻¹ * a * y * ((y⁻¹ * b * y * b) * a) := by group
          _ = y⁻¹ * a * y * (a * (y⁻¹ * b * y * b)) := by rw [hc1]
          _ = y⁻¹ * a * y * a * (y⁻¹ * b * y * b) := by group }
  let sq : D →* D :=
    { toFun := fun d => d * d
      map_one' := by simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hab' : (a : G) * (b : G) = (b : G) * (a : G) := hcomm a a.2 b b.2
        simp only [Subgroup.coe_mul]
        calc (a : G) * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hab']
          _ = a * a * (b * b) := by group }
  have hker : θ.ker = sq.ker := by
    ext d
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h0
      have h1 : y⁻¹ * (d : G) * y * d = 1 := congrArg Subtype.val h0
      have h3 : y⁻¹ * (d : G) * y = (d : G)⁻¹ := by
        calc y⁻¹ * (d : G) * y = (y⁻¹ * (d : G) * y * d) * (d : G)⁻¹ := by group
          _ = (d : G)⁻¹ := by rw [h1, one_mul]
      have h2 : y * (d : G) * y⁻¹ = (d : G)⁻¹ := by
        have e : y * (d : G)⁻¹ * y⁻¹ = d := by rw [← h3]; group
        calc y * (d : G) * y⁻¹ = (y * (d : G)⁻¹ * y⁻¹)⁻¹ := by group
          _ = (d : G)⁻¹ := by rw [e]
      have hdΩ := mem_omegaIn_one_of_inverted hfam hk hy hf d.2 h2
      have h4 := ((mem_omegaIn_iff_of_comm hcomm).mp hdΩ).2
      apply Subtype.ext
      show (d : G) * d = 1
      simpa [pow_two] using h4
    · intro h0
      have h1 : (d : G) * d = 1 := congrArg Subtype.val h0
      have hdΩ : (d : G) ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self d.2 h1
      have hyd : y⁻¹ * (d : G) * y = d := by
        have := Subgroup.mem_centralizer_iff.mp (mem_centralizer_of_mem_R hy) (d : G) (hω hdΩ)
        calc y⁻¹ * (d : G) * y = y⁻¹ * ((d : G) * y) := by group
          _ = y⁻¹ * (y * (d : G)) := by rw [this]
          _ = d := by group
      apply Subtype.ext
      show y⁻¹ * (d : G) * y * d = 1
      rw [hyd, h1]
  have hcard : Nat.card θ.range = Nat.card sq.range := by
    have h1 := Subgroup.card_ker_mul_card_range θ
    have h2 := Subgroup.card_ker_mul_card_range sq
    rw [hker] at h1
    have hpos : 0 < Nat.card sq.ker := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  have hle : θ.range ≤ sq.range := by
    rintro _ ⟨d, rfl⟩
    have hc : y⁻¹ * (d : G) * y * (d : G)⁻¹ ∈ omegaIn 1 D := by
      have := commutator_mem_omegaIn_one dD (inv_mem hy) d.2
      simpa using this
    obtain ⟨c, hcD, hc2⟩ := (mem_mhoOne_iff dD).mp (hω hc)
    refine ⟨⟨c, hcD⟩ * d, ?_⟩
    apply Subtype.ext
    have hcd : c * (d : G) = (d : G) * c := hcomm c hcD d d.2
    show (c * (d : G)) * (c * d) = y⁻¹ * (d : G) * y * d
    calc c * (d : G) * (c * d) = (c * c) * ((d : G) * d) := by
          rw [mul_assoc c, ← mul_assoc (d : G), ← hcd]; group
      _ = (y⁻¹ * (d : G) * y * (d : G)⁻¹) * ((d : G) * d) := by rw [hc2]
      _ = y⁻¹ * (d : G) * y * d := by group
  have heq : θ.range = sq.range := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  obtain ⟨f, hfD, hf2⟩ := (mem_mhoOne_iff dD).mp he
  have hmem : (⟨e, hf2 ▸ D.mul_mem hfD hfD⟩ : D) ∈ θ.range := by
    rw [heq]
    exact ⟨⟨f, hfD⟩, Subtype.ext hf2⟩
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, d.2, congrArg Subtype.val hd⟩

end DeviationGeneric

namespace StrothFrame.IsD

open DeviationGeneric Stroth225Frame Stroth224Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem mem_of_sqBar_eq_zero_familyOne (h : F.IsD D dD) (hfam : τ.m + 1 = τ.n)
    (hk : ∀ i, 2 ≤ τ.k i) {x : G} (hx : x ∈ 𝓡[(F.S : Subgroup G), D])
    (hf : devMat dD hk x hx 0 0 = 0 ∧ devMat dD hk x hx 0 1 = 0 ∧ devMat dD hk x hx 0 2 = 0)
    (hq : sqBar dD hk h.cent x hx = 0) : x ∈ D := by
  have hx2 : x * x ∈ mhoOne D :=
    (barD_eq_zero_iff hk ⟨x * x, mul_self_mem_of_mem_R dD hk h.cent hx⟩).mp hq
  obtain ⟨d, hdD, hd⟩ := exists_conj_mul_eq_of_row_zero hfam dD hk hx hf (inv_mem hx2)
  set z := x * d with hzdef
  have hz2 : z * z = 1 := by
    calc z * z = (x * x) * (x⁻¹ * d * x * d) := by simp only [z]; group
      _ = 1 := by rw [hd, mul_inv_cancel]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hdR : d ∈ 𝓡[(F.S : Subgroup G), D] := D_le_R dD h.le_S hdD
  have hz : z ∈ 𝓡[(F.S : Subgroup G), D] := mul_mem hx hdR
  have hdevz : devMat dD hk z hz = devMat dD hk x hx := by
    rw [devMat_mul hk hx hdR, (devMat_eq_zero_iff hk h.cent hdR).mpr hdD, add_zero]
  have hfz : devMat dD hk z hz 0 0 = 0 ∧ devMat dD hk z hz 0 1 = 0 ∧
      devMat dD hk z hz 0 2 = 0 := by rw [hdevz]; exact hf
  have hfix := (fixed_iff_row_zero (devMat dD hk z hz)).mpr hfz
  have hmove : ∀ g : G, g ∈ (F.S : Subgroup G) → g ∈ Subgroup.normalizer (D : Set G) →
      g * g = 1 → (g = F.dA.uv ∨ g = F.dA.t) →
      (∀ (hg : g⁻¹ * z * g ∈ 𝓡[(F.S : Subgroup G), D]),
        devMat dD hk _ hg = devMat dD hk z hz) →
      z⁻¹ * g * z * g⁻¹ ∈ F.E := by
    intro g hgS hgN hg2 hgE hdev
    have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
    have hgz := conj_mem_R hgS hgN hz
    have hr : z⁻¹ * (g⁻¹ * z * g) ∈ D :=
      inv_mul_mem_of_devMat_eq hk h.cent hz hgz (hdev hgz).symm
    set r := z⁻¹ * (g⁻¹ * z * g) with hrdef
    have hzr : z * r * z⁻¹ = r⁻¹ := by
      rw [hzinv, hrdef, hzinv, hginv]
      calc z * (z * (g * z * g)) * z = (z * z) * (g * z * g) * z := by group
        _ = g * z * g * z := by rw [hz2, one_mul]
        _ = (z * (g * z * g))⁻¹ := by
            rw [show (z * (g * z * g))⁻¹ = g⁻¹ * z⁻¹ * g⁻¹ * z⁻¹ by group, hginv, hzinv]
    have hrΩ := mem_omegaIn_one_of_inverted hfam hk hz hfz hr hzr
    have hrA : r ∈ F.A := (h.isTyped.omegaIn_one_eq ▸ hrΩ : r ∈ omegaIn 1 F.A) |> omegaIn_le 1 F.A
    have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => comm_of_mem dD ha hb
    have hr2 : r * r = 1 := by
      have := ((mem_omegaIn_iff_of_comm hcomm).mp hrΩ).2
      simpa [pow_two] using this
    have hgr : g⁻¹ * r * g = r := by
      have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
      calc g⁻¹ * r * g = g * (z * (g * z * g)) * g := by rw [hginv, hrdef, hzinv, hginv]
        _ = (g * z * g) * z * (g * g) := by group
        _ = (g * z * g) * z := by rw [hg2, mul_one]
        _ = (z * (g * z * g))⁻¹ := by
            rw [show (z * (g * z * g))⁻¹ = g⁻¹ * z⁻¹ * g⁻¹ * z⁻¹ by group, hginv, hzinv]
        _ = r⁻¹ := by rw [hrdef, hzinv, hginv]
        _ = r := hrinv
    have hrE : r ∈ F.E := by
      rw [← Stroth76.frame_closureE_eq F]
      exact Stroth76.mem_closureE_of_fixed F.dA.toConfig hrA hr2
        (by rcases hgE with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl) hgr
    have : z⁻¹ * g * z * g⁻¹ = r := by rw [hrdef, hginv]; group
    rw [this]
    exact hrE
  have huv := hmove dD.uv h.uv_mem_S dD.uv_mem dD.uv_sq (Or.inl h.uv_eq)
    (fun hg => (devMat_conj_uv_familyOne hfam hk hz hg).trans hfix.1)
  have ht := hmove dD.t h.t_mem_S dD.t_mem dD.t_sq (Or.inr h.t_eq)
    (fun hg => (devMat_conj_t_familyOne hfam hk hz hg).trans hfix.2)
  have hzC : z ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (omegaIn_one_le_mhoOne dD hk) (mem_centralizer_of_mem_R hz)
  have hzD : z ∈ D := h.mem_of_conj_mem_E (mem_S_of_mem_R hz) hzC huv ht
  have : x = z * d⁻¹ := by simp only [z]; group
  rw [this]
  exact mul_mem hzD (inv_mem hdD)

end StrothFrame.IsD

end CFSG.CGT.Stroth77
