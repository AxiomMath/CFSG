module

public import CFSG.GH74.GLS.NT44.RigidActorClasses
import CFSG.GH74.GLS.NT44.RigidSingleton
import CFSG.GH74.GLS.NT44.RigidPumpExistence
import CFSG.GH74.GLS.NT44.RigidCoverage
import CFSG.GH74.GLS.C3.Layer1.BkIv81Aux
import CFSG.GroupTheory.InversionFourSubgroup
import CFSG.GroupTheory.PCore.CommonQuotientTransport
import CFSG.LocalAnalysis.ComponentClassification.Foote47Transport
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOutSquare
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsAction

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG
open CFSG.GH74.GLS
open CFSG.GH74.GLS.Stage1.Thm4

theorem exists_sq_eq_of_sq_eq_one_of_mulEquiv {A : Type*} [Group A]
    (e : A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) {z : A} (hz : z ^ 2 = 1) :
    ∃ ζ : A, ζ ^ 2 = z := by
  have key : ∀ p : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
      p ^ 2 = 1 → ∃ q, q ^ 2 = p := by decide
  have hp : e z ^ 2 = 1 := by rw [← map_pow, hz, map_one]
  obtain ⟨q, hq⟩ := key (e z) hp
  refine ⟨e.symm q, ?_⟩
  apply e.injective
  rw [map_pow, MulEquiv.apply_symm_apply, hq]

variable {G : Type} [Group G] [Finite G]

theorem exists_sq_eq_mem_inf_zStar
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x : G} {J S : Subgroup G} (hx2 : orderOf x = 2) (hJ : J ∈ RigidSet fullQ x) (hxJ : x ∈ J)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Subgroup.centralizer ({x} : Set G))) :
    ∃ ζ ∈ S ⊓ zStar J, ζ ^ 2 = x := by
  classical
  have hx2' : x ^ 2 = 1 := by simpa [hx2] using pow_orderOf_eq_one x
  have hxS : x ∈ S := Alt51.z_mem_sylow (z := x) hx2 hS
  have hxZ : x ∈ zStar J := Alt51.z_mem_zStar (K := J) (z := x) (P92.rig_le_cen hJ) hxJ
  obtain ⟨eZ, e4, -⟩ :=
    exists_rigid_center_sylow_equiv_of_center_card_sixteen hJ hS hL34 h16
  let e : ↥(S ⊓ zStar J) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := eZ.trans e4
  have hxW : (⟨x, hxS, hxZ⟩ : ↥(S ⊓ zStar J)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hx2'
  obtain ⟨ζ, hζ⟩ := exists_sq_eq_of_sq_eq_one_of_mulEquiv e hxW
  refine ⟨(ζ : G), ⟨ζ.2.1, ζ.2.2⟩, ?_⟩
  have h := congrArg (Subtype.val) hζ
  simpa using h

omit [Finite G] in
theorem mapQuotient_mem_range_conj_of_mem_withKernel {M : Subgroup G} {y : G}
    (hy : y ∈ CFSG.ComponentClassification.GrSLit.withKernel M)
    (hyM : y ∈ Subgroup.normalizer (M : Set G)) :
    MulAut.mapQuotient (pPrimeCore 2 ↥M) (M.normalizerMonoidHom ⟨y, hyM⟩) ∈
      (MulAut.conj : kBar M →* MulAut (kBar M)).range := by
  obtain ⟨e₀, he₀⟩ := CFSG.ComponentClassification.GrSLit.L34Facts.exists_inner hy hyM
  refine ⟨e₀, ?_⟩
  let A : MulAut (kBar M) :=
    MulAut.mapQuotient (pPrimeCore 2 ↥M) (M.normalizerMonoidHom ⟨y, hyM⟩)
  show MulAut.conj e₀ = A
  ext q
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) q
  have hA : A (QuotientGroup.mk' (pPrimeCore 2 ↥M) j) =
      QuotientGroup.mk' (pPrimeCore 2 ↥M) ((M.normalizerMonoidHom ⟨y, hyM⟩) j) := by
    dsimp only [A]
    rw [QuotientGroup.mk'_apply, MulAut.mapQuotient_mk, QuotientGroup.mk'_apply]
  have h1 : CFSG.ComponentClassification.GrSLit.L34Facts.betaHat M hyM
      (A (QuotientGroup.mk' (pPrimeCore 2 ↥M) j)) =
      QuotientGroup.mk' (pPrimeCore 2 ↥M) j := by
    rw [hA, CFSG.ComponentClassification.GrSLit.L34Facts.betaHat_jq]
    congr 1
    apply Subtype.ext
    simp only [CFSG.ComponentClassification.GrSLit.L34Facts.coe_conjJ,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    group
  have h2 : e₀⁻¹ * A (QuotientGroup.mk' (pPrimeCore 2 ↥M) j) * e₀ =
      QuotientGroup.mk' (pPrimeCore 2 ↥M) j :=
    (he₀ (A (QuotientGroup.mk' (pPrimeCore 2 ↥M) j))).symm.trans h1
  rw [MulAut.conj_apply]
  symm
  calc A (QuotientGroup.mk' (pPrimeCore 2 ↥M) j)
      = e₀ * (e₀⁻¹ * A (QuotientGroup.mk' (pPrimeCore 2 ↥M) j) * e₀) * e₀⁻¹ := by
        group
    _ = e₀ * QuotientGroup.mk' (pPrimeCore 2 ↥M) j * e₀⁻¹ := by rw [h2]

theorem false_of_inner_involution_mem_zStar
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ Subgroup.normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    (h81 : ∀ y : G, IsConj x y → y * x = x * y → ∀ hyJ : y ∈ Subgroup.normalizer (J : Set G),
      y ∉ centralizerSection J (pPrimeCoreOf 2 J) →
      MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨y, hyJ⟩) ∉
        (MulAut.conj : kBar J →* MulAut (kBar J)).range)
    {L : Subgroup G} (hL : L ∈ RigidSet fullQ v)
    {a : G} (ha2 : orderOf a = 2) (hax : a ∈ Subgroup.centralizer ({x} : Set G))
    (hav : a ∈ Subgroup.centralizer ({v} : Set G)) (haZ : a ∈ zStar L)
    (haJ : a ∈ Subgroup.normalizer (J : Set G))
    (hainn : MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨a, haJ⟩) ∈
      (MulAut.conj : kBar J →* MulAut (kBar J)).range) :
    False := by
  classical
  have hsub := rigidSet_subsingleton_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
    hJ hvN hvact hxP hmax
  have hJx : Kz fullQ x = J := kz_eq_of_rigidSet_subsingleton (hsub x hx2) hJ
  have hxJ : x ∈ J := by rw [hJx] at hxP; exact hxP
  have hLv : Kz fullQ v = L := kz_eq_of_rigidSet_subsingleton (hsub v hv2) hL
  have hCxN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) :=
    centralizer_le_normalizer_of_rigidSet_subsingleton (hsub x hx2) hJ
  have hCvN : Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_rigidSet_subsingleton (hsub v hv2) hL
  have hx2sq : x ^ 2 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx2] at h
  have ha2sq : a ^ 2 = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha2] at h
  have hzaP : IsPGroup 2 ↥(Subgroup.zpowers a) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa [Nat.card_zpowers] using orderOf_dvd_of_pow_eq_one ha2sq)
  have hzaC : Subgroup.zpowers a ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.zpowers_le.mpr hax
  obtain ⟨S, hS, hzaS⟩ :=
    exists_isSylowOf_centralizer_le_of_isPGroup hzaP hzaC
  have haS : a ∈ S := hzaS (Subgroup.mem_zpowers a)
  obtain ⟨ζ, hζS, hζ2⟩ := exists_sq_eq_mem_inf_zStar hL34 h16 hx2 hJ hxJ hS
  have hζJ : ζ ∈ J := hζS.2.1
  have hmemJ : a * ζ * a⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp haJ ζ).mp hζJ
  let uJ : ↥J := ⟨a * ζ * a⁻¹, hmemJ⟩
  let zJ : ↥J := ⟨ζ, hζJ⟩
  have hcenter : (QuotientGroup.mk zJ : kBar J) ∈ Subgroup.center (kBar J) :=
    (Alt51.mem_zStar_iff_hat_mem_center (K := J) zJ).1 hζS.2
  have hαcenter : MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨a, haJ⟩)
      (QuotientGroup.mk zJ) = QuotientGroup.mk zJ := by
    obtain ⟨q, hq⟩ := hainn
    rw [← hq, MulAut.conj_apply]
    have h := Subgroup.mem_center_iff.mp hcenter q
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have hαmk : MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨a, haJ⟩)
      (QuotientGroup.mk zJ) = QuotientGroup.mk uJ := by
    rw [MulAut.mapQuotient_mk]
    rw [show (J.normalizerMonoidHom ⟨a, haJ⟩) zJ = uJ from by
      apply Subtype.ext
      simp only [uJ, zJ, Subgroup.normalizerMonoidHom_apply_apply_coe]]
  have hquot : QuotientGroup.mk' (pPrimeCore 2 ↥J) uJ =
      QuotientGroup.mk' (pPrimeCore 2 ↥J) zJ := hαmk.symm.trans hαcenter
  have hcommO : a * ζ * a⁻¹ * ζ⁻¹ ∈ pPrimeCoreOf 2 J := by
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥J) (uJ * zJ⁻¹) = 1 := by
      rw [map_mul, map_inv, hquot, mul_inv_cancel]
    have h2 : uJ * zJ⁻¹ ∈ pPrimeCore 2 ↥J := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_map_of_mem J.subtype h2
  have hcommS : a * ζ * a⁻¹ * ζ⁻¹ ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem haS hζS.1) (S.inv_mem haS)) (S.inv_mem hζS.1)
  have hbot : S ⊓ pPrimeCoreOf 2 J = ⊥ :=
    CFSG.GH74.GLS.Bg.Iii2.inf_pPrimeCoreOf_eq_bot (T := S) (X := J) hS.isPGroup
  have hcommOne : a * ζ * a⁻¹ * ζ⁻¹ = 1 := by
    have hmem : a * ζ * a⁻¹ * ζ⁻¹ ∈ S ⊓ pPrimeCoreOf 2 J := ⟨hcommS, hcommO⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have haζ : a * ζ = ζ * a := by
    have h2 : a * ζ * a⁻¹ = ζ := by
      calc a * ζ * a⁻¹ = a * ζ * a⁻¹ * ζ⁻¹ * ζ := by group
        _ = 1 * ζ := by rw [hcommOne]
        _ = ζ := one_mul ζ
    calc a * ζ = (a * ζ * a⁻¹) * a := by group
      _ = ζ * a := by rw [h2]
  have hζa : ζ * a = a * ζ := haζ.symm
  have haZ' : a ∈ zStar (Kz fullQ v) := by rw [hLv]; exact haZ
  obtain ⟨Jf, hJf⟩ := exists_pump_family_of_mem_zStar_kz (x := v) (t := a) hnonab ha2 haZ'
  let M : Subgroup G := Jf L
  have hMlt : PumpUpLT 2 v L a M := hJf L hL
  have hMrig : IsRigidOfType fullQ a M :=
    P92.isRigidOfType_of_pumpUpLT hL hMlt
  have hKa : Kz fullQ a = M := kz_eq_of_rigidSet_subsingleton (hsub a ha2) hMrig
  have hCaN : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (M : Set G) :=
    centralizer_le_normalizer_of_rigidSet_subsingleton (hsub a ha2) hMrig
  have hζaC : ζ ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hζa
  have hζN : ζ ∈ Subgroup.normalizer (M : Set G) := hCaN hζaC
  have hxaC : x ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [← hζ2]
    exact (Subgroup.centralizer ({a} : Set G)).pow_mem hζaC 2
  have hxM : x ∈ Subgroup.normalizer (M : Set G) := hCaN hxaC
  have hζP : IsPGroup 2 ↥(Subgroup.zpowers ζ) :=
    IsPGroup.to_le hS.isPGroup (Subgroup.zpowers_le.mpr hζS.1)
  have hL34Hat : IsL34Quotient (kBar M) := by
    obtain ⟨eM⟩ := hMrig.2
    exact CFSG.GH74.GLS.TwoThin.isL34Quotient_of_mulEquiv eM.symm hL34
  have hL34M : CFSG.ComponentClassification.GrSLit.IsL34Type (M ⧸ Open.fusionZStar M) := by
    obtain ⟨eFZ⟩ :=
      CFSG.ComponentClassification.GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥M
    exact CFSG.Blueprint.LieModel.of_mulEquiv eFZ hL34Hat
  have hperf : ⁅M, M⁆ = M :=
    CFSG.GH74.GLS.C3.Layer1.Bk.perfect_of_isPCompIn (P92.rig_pcomp hMrig)
  have hxwith : x ∈ CFSG.ComponentClassification.GrSLit.withKernel M := by
    have h := CFSG.ComponentClassification.GrSLit.L34Facts.outSquare (G := G) M hperf hL34M
      ζ hζN hζP
    rw [← pow_two, hζ2] at h
    exact h
  have hαM_inner := mapQuotient_mem_range_conj_of_mem_withKernel hxwith hxM
  have haCv : v ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hav).symm
  have hcardA : (RigidSet fullQ a).ncard = 1 := by
    rw [(hsub a ha2).eq_singleton_of_mem hMrig]
    simp
  have hcardV : (RigidSet fullQ v).ncard = 1 := by
    rw [(hsub v hv2).eq_singleton_of_mem hL]
    simp
  have hcard : (RigidSet fullQ a).ncard ≤ (RigidSet fullQ v).ncard := by rw [hcardA, hcardV]
  obtain ⟨hsupv, hsupa⟩ := rigid_product_coverage (J := Jf) (x := v) (t := a) haCv hJf hcard
  have hsupL : (L ⊓ M) ⊔ pPrimeCoreOf 2 L = L := by
    simpa only [hLv, hKa] using hsupv
  have hsupM : (L ⊓ M) ⊔ pPrimeCoreOf 2 M = M := by
    simpa only [hLv, hKa] using hsupa
  have hxL : x ∈ Subgroup.normalizer (L : Set G) :=
    hCvN (Subgroup.mem_centralizer_singleton_iff.mpr hvx.symm)
  have hxD : x ∈ Subgroup.normalizer ((L ⊓ M : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hxL, hxM⟩)
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htrans0 :=
    common_pPrimeCore_quotient_transport (p := 2) (D := L ⊓ M) (B := L) (H := M)
      inf_le_left inf_le_right
      (CFSG.ComponentClassification.Foote47.oddCoreRestriction_surjective inf_le_left hsupL)
      (CFSG.ComponentClassification.Foote47.oddCoreRestriction_surjective inf_le_right hsupM)
  dsimp only at htrans0
  obtain ⟨-, -, e, -, -, htrans⟩ := htrans0
  obtain ⟨-, -, -, -, hinner_iff⟩ := htrans x hxD hxL hxM
  have hαL_inner : MulAut.mapQuotient (pPrimeCore 2 ↥L) (L.normalizerMonoidHom ⟨x, hxL⟩) ∈
      (MulAut.conj : kBar L →* MulAut (kBar L)).range := hinner_iff.mpr hαM_inner
  have hxact : x ∉ centralizerSection L (pPrimeCoreOf 2 L) := by
    intro hxcs
    have hxLcxK : x ∈ CxK v L :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hvx.symm, hxcs⟩
    have hxJcxK : x ∈ CxK x J := mem_cxK_self_of_isPCompIn (P92.rig_pcomp hJ)
    have hxone : x = 1 :=
      eq_one_of_mem_cxK_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN
        hvact hxP hmax hJ hL hxJcxK hxLcxK ⟨1, by simpa using hx2sq⟩
    rw [hxone, orderOf_one] at hx2
    omega
  obtain ⟨g, hg⟩ := isConj_iff.mp hxv
  have hL' : CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap g J ∈ RigidSet fullQ v := by
    have h := isRigidOfType_conj (Q := fullQ) hJ g
    rwa [hg] at h
  have hLJ : CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap g J = L := hsub v hv2 hL' hL
  have hJL : CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap g⁻¹ L = J := by
    rw [← hLJ, CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap_inv_cancel]
  let y : G := g⁻¹ * x * (g⁻¹)⁻¹
  have hyJ : y ∈ Subgroup.normalizer (J : Set G) := by
    have h := conj_mem_normalizer_cmap hxL g⁻¹
    rw [hJL] at h
    exact h
  have hconj : IsConj x y := isConj_iff.mpr ⟨g⁻¹, rfl⟩
  have hycomm : y * x = x * y := by
    have h1 : g * x * g⁻¹ * x = x * (g * x * g⁻¹) := by
      rw [hg]
      exact hvx
    calc y * x = g⁻¹ * (x * (g * x * g⁻¹)) * g := by
          dsimp only [y]
          group
      _ = g⁻¹ * (g * x * g⁻¹ * x) * g := by rw [← h1]
      _ = x * y := by
          dsimp only [y]
          group
  have hyact : y ∉ centralizerSection J (pPrimeCoreOf 2 J) := by
    have h := conj_not_mem_centralizerSection_cmap hxact g⁻¹
    rw [hJL] at h
    exact h
  have hInnerY : MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨y, hyJ⟩) ∈
      (MulAut.conj : kBar J →* MulAut (kBar J)).range :=
    mapQuotient_mem_range_conj_cmap hJL hxL hyJ hαL_inner
  exact h81 y hconj hycomm hyJ hyact hInnerY

theorem exists_fixed_center_subgroup
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ Subgroup.normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    {L : Subgroup G} (hL : L ∈ RigidSet fullQ v) :
    ∃ V : Subgroup G, V ≤ Subgroup.centralizer ({x} : Set G) ∧
      V ≤ Subgroup.centralizer ({v} : Set G) ∧ V ≤ zStar L ∧ IsPGroup 2 V ∧
      (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) ∧ 4 ≤ Nat.card V := by
  classical
  have hs := rigidSet_subsingleton_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
    hJ hvN hvact hxP hmax
  have hCN : Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_rigidSet_subsingleton (Q := fullQ) (z := v) (hs v hv2) hL
  have hxC : x ∈ Subgroup.centralizer ({v} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hvx.symm
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hCN hxC
  have hx2' : x * x = 1 := by simpa [hx2, pow_two] using pow_orderOf_eq_one x
  have hzp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (p := 2) (n := 1) (by rw [Nat.card_zpowers, hx2]; norm_num)
  have hle : Subgroup.zpowers x ≤ Subgroup.centralizer ({v} : Set G) :=
    Subgroup.zpowers_le.mpr hxC
  obtain ⟨S', hS', hxS'⟩ :=
    P92.exists_sylow_ge (C := Subgroup.centralizer ({v} : Set G))
      (S := Subgroup.zpowers x) hzp hle
  let W : Subgroup G := S' ⊓ zStar L
  have hxS'x : x ∈ S' := hxS' (Subgroup.mem_zpowers x)
  have hxW : x ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hxS'x, Alt51.mem_normalizer_zStar hxN⟩
  obtain ⟨eZ, e4, -⟩ := exists_rigid_center_sylow_equiv_of_center_card_sixteen hL hS' hL34 h16
  have hWeq : Nonempty (↥W ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :=
    ⟨eZ.trans e4⟩
  have hVcard : 4 ≤ Nat.card ↥(W ⊓ Subgroup.centralizer ({x} : Set G)) :=
    CFSG.four_le_card_inf_centralizer_of_c4_prod_c4 hWeq hx2' hxW
  have hWcomm : ∀ a b : ↥W, a * b = b * a := by
    intro a b
    apply (eZ.trans e4).injective
    simp only [map_mul, mul_comm]
  refine ⟨W ⊓ Subgroup.centralizer ({x} : Set G), inf_le_right, ?_, ?_, ?_, ?_, hVcard⟩
  · exact ((inf_le_left.trans inf_le_right).trans inf_le_left).trans (P92.rig_le_cen hL)
  · exact inf_le_left.trans inf_le_right
  · exact hS'.isPGroup.to_le (inf_le_left.trans inf_le_left)
  · intro a ha b hb
    exact congrArg Subtype.val (hWcomm ⟨a, ha.1⟩ ⟨b, hb.1⟩)

end CFSG.GH74.GLS.NT44

end
