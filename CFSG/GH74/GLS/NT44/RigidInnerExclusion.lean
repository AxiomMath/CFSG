module

public import CFSG.GH74.GLS.NT44.RigidSingleton
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
import CFSG.GH74.GLS.NT44.RigidPumpExistence
import CFSG.GH74.GLS.NT44.RigidPump
import CFSG.GH74.GLS.NT44.RigidCoverage
import CFSG.LocalAnalysis.ComponentClassification.Foote47Transport
import CFSG.GroupTheory.PCore.CommonQuotientTransport
import CFSG.GH74.GLS.Balance.SolvCompBasic
import CFSG.GH74.GLS.NT44.SylowCommutator

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.ComponentClassification
open scoped commutatorElement

private theorem exists_faithful_center_action_of_inner_rigid_actor
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2)
    (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (hvN : v ∈ Subgroup.normalizer (J : Set G))
    (hvact : v ∉ CFSG.GH74.GLS.centralizerSection J
      (CFSG.GH74.GLS.pPrimeCoreOf 2 J))
    (hxP : x ∈ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s) ≤
        Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)) :
    MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥J)
      (J.normalizerMonoidHom ⟨v, hvN⟩) ∈
        (MulAut.conj : CFSG.GH74.GLS.kBar J →*
          MulAut (CFSG.GH74.GLS.kBar J)).range →
    ∃ (g : G) (S : Subgroup G),
      let L : Subgroup G := CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap g J
      let Z : Subgroup G := S ⊓ CFSG.GH74.GLS.zStar J
      g * x * g⁻¹ = v ∧
      CFSG.ABGLocalTools.IsSylowOf 2 S (Subgroup.centralizer ({x} : Set G)) ∧
      v ∈ S ∧
      CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x = J ∧
      CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ v = L ∧
      L ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ v ∧
      (∀ s : G, orderOf s = 2 →
        (CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s).Subsingleton) ∧
      x ∈ Z ∧
      Z ≤ Subgroup.centralizer ({v} : Set G) ∧
      ∃ (eZ : ↥Z ≃* Subgroup.center (CFSG.GH74.GLS.kBar J))
        (_e4 : Subgroup.center (CFSG.GH74.GLS.kBar J) ≃*
          (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
        (hZL : Z ≤ Subgroup.normalizer (L : Set G))
        (P : Sylow 2 ↥L),
        (∀ z : ↥Z, (eZ z : CFSG.GH74.GLS.kBar J) =
          CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J ⟨(z : G), z.2.2.1⟩) ∧
        let ρ : ↥Z →* MulAut ↥L :=
          L.normalizerMonoidHom.comp (Subgroup.inclusion hZL)
        (∀ (a : ↥Z) (c : ↥L),
          (((ρ a) c : ↥L) : G) = (a : G) * (c : G) * (a : G)⁻¹) ∧
        Function.Injective
          (fun a : ↥Z => MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥L) (ρ a)) ∧
        (∀ (a : ↥Z) (c : ↥L), c ∈ (P : Subgroup ↥L) →
          (ρ a) c ∈ (P : Subgroup ↥L)) := by
  classical
  intro hinner
  have hsub := rigidSet_subsingleton_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2
    hxv hvx hJ hvN hvact hxP hmax
  obtain ⟨g, hg⟩ := isConj_iff.mp hxv
  let L : Subgroup G := cmap g J
  have hL : L ∈ RigidSet fullQ v := by
    have h := isRigidOfType_conj (Q := fullQ) hJ g
    rwa [hg] at h
  have hKzJ : Kz fullQ x = J :=
    kz_eq_of_rigidSet_subsingleton (Q := fullQ) (z := x) (hsub x hx2) hJ
  have hKzL : Kz fullQ v = L :=
    kz_eq_of_rigidSet_subsingleton (Q := fullQ) (z := v) (hsub v hv2) hL
  have hxJ : x ∈ J := by
    rw [← hKzJ]
    exact hxP
  have hxZJ : x ∈ zStar J :=
    Alt51.z_mem_zStar (K := J) hJ.1.1.2.2.1 hxJ
  have hx2' : x ^ 2 = 1 := by
    rw [← hx2]
    exact pow_orderOf_eq_one x
  have hv2' : v ^ 2 = 1 := by
    rw [← hv2]
    exact pow_orderOf_eq_one v
  have hv4 : v ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hv2', one_pow]
  have hE2 : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers v) :=
    isPGroup_zpowers_sup_zpowers (v := x) (y := v) hx2' hv4 hvx.symm
  have hEC : Subgroup.zpowers x ⊔ Subgroup.zpowers v ≤
      Subgroup.centralizer ({x} : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hvx
  obtain ⟨S, hS, hES⟩ :=
    P92.exists_sylow_ge (C := Subgroup.centralizer ({x} : Set G)) hE2 hEC
  have hxS : x ∈ S := hES (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hvS : v ∈ S := hES (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  let Z : Subgroup G := S ⊓ zStar J
  have hxZ : x ∈ Z := ⟨hxS, hxZJ⟩
  obtain ⟨eZ, e4, heZ⟩ :=
    exists_rigid_center_sylow_equiv_of_center_card_sixteen (G := G) (fullQ := fullQ)
      (x := x) (J := J) (S := S) hJ hS hL34 h16
  have hZ2 : IsPGroup 2 ↥Z := hS.isPGroup.to_inf_left
  have hvNS : v ∈ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer hvS
  have hvNzJ : v ∈ Subgroup.normalizer (zStar J : Set G) :=
    Alt51.mem_normalizer_zStar hvN
  have hvNZ : v ∈ Subgroup.normalizer (Z : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro z
    exact ⟨fun hz =>
        ⟨(Subgroup.mem_normalizer_iff.1 hvNS z).1 hz.1,
          (Subgroup.mem_normalizer_iff.1 hvNzJ z).1 hz.2⟩,
      fun hz =>
        ⟨(Subgroup.mem_normalizer_iff.1 hvNS z).2 hz.1,
          (Subgroup.mem_normalizer_iff.1 hvNzJ z).2 hz.2⟩⟩
  have hα : MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥J)
      (J.normalizerMonoidHom ⟨v, hvN⟩) =
        MulAut.conj (Classical.choose (MonoidHom.mem_range.mp hinner)) :=
    (Classical.choose_spec (MonoidHom.mem_range.mp hinner)).symm
  have hZCv : Z ≤ Subgroup.centralizer ({v} : Set G) := by
    intro z hz
    let zz : ↥Z := ⟨z, hz⟩
    have hwZ : v * z * v⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.1 hvNZ z).1 hz
    let w : ↥Z := ⟨v * z * v⁻¹, hwZ⟩
    have hwZmem : v * z * v⁻¹ ∈ S ⊓ zStar J := by simpa only [Z] using w.2
    have hwJ : v * z * v⁻¹ ∈ J := hwZmem.2.1
    have hzZmem : z ∈ S ⊓ zStar J := by simpa only [Z] using zz.2
    have hzJmem : z ∈ J := hzZmem.2.1
    have hαz : MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥J)
        (J.normalizerMonoidHom ⟨v, hvN⟩)
          (CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J ⟨z, hzJmem⟩) =
          CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J ⟨v * z * v⁻¹, hwJ⟩ := by
      change ((MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥J))
        (J.normalizerMonoidHom ⟨v, hvN⟩)) (QuotientGroup.mk ⟨z, hzJmem⟩) =
          QuotientGroup.mk ⟨v * z * v⁻¹, hwJ⟩
      have hvz : (J.normalizerMonoidHom ⟨v, hvN⟩) ⟨z, hzJmem⟩ =
          ⟨v * z * v⁻¹, hwJ⟩ := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rw [MulAut.mapQuotient_mk, hvz]
    have hfix : MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥J)
        (J.normalizerMonoidHom ⟨v, hvN⟩)
          (CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J ⟨z, hzJmem⟩) =
          CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J ⟨z, hzJmem⟩ := by
      rw [hα, MulAut.conj_apply]
      have hcent : CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J ⟨z, hzJmem⟩ =
          (eZ zz : CFSG.GH74.GLS.kBar J) := (heZ zz).symm
      rw [hcent]
      have hcomm : Classical.choose (MonoidHom.mem_range.mp hinner) *
          (eZ zz : CFSG.GH74.GLS.kBar J) =
            (eZ zz : CFSG.GH74.GLS.kBar J) *
              Classical.choose (MonoidHom.mem_range.mp hinner) :=
        Subgroup.mem_center_iff.mp (eZ zz).2 _
      rw [hcomm]
      group
    have hw_eq_z : w = zz := by
      apply eZ.injective
      apply Subtype.ext
      rw [heZ w, heZ zz]
      exact hαz.symm.trans hfix
    have hw : v * z * v⁻¹ = z := congrArg Subtype.val hw_eq_z
    have h2 : v * (z : G) = (z : G) * v := by
      have := congrArg (fun t => t * v) hw
      simpa [mul_assoc] using this
    exact Subgroup.mem_centralizer_singleton_iff.mpr h2.symm
  have hCvL : Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_rigidSet_subsingleton (Q := fullQ) (z := v) (K := L)
      (hsub v hv2) hL
  have hZL : Z ≤ Subgroup.normalizer (L : Set G) := fun z hz => hCvL (hZCv hz)
  let ρ : ↥Z →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hZL)
  have hρ_apply : ∀ (a : ↥Z) (c : ↥L),
      (((ρ a) c : ↥L) : G) = (a : G) * (c : G) * (a : G)⁻¹ := by
    intro a c
    simp only [ρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion]
  have hψ_inj : Function.Injective
      (fun a : ↥Z => MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥L) (ρ a)) := by
    let ψ : ↥Z →* MulAut (CFSG.GH74.GLS.kBar L) :=
      (MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥L)).comp ρ
    have hψker : ψ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      rw [MonoidHom.mem_ker] at ha
      have hact0 : MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥L) (ρ a) = 1 := by
        simpa only [ψ, MonoidHom.comp_apply] using ha
      have hρa : ρ a = L.normalizerMonoidHom ⟨(a : G), hZL a.2⟩ := rfl
      have hact : MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥L)
          (L.normalizerMonoidHom ⟨(a : G), hZL a.2⟩) = 1 := by
        rw [← hρa]
        exact hact0
      have haSecL : (a : G) ∈ centralizerSection L (pPrimeCoreOf 2 L) :=
        (mapQuotient_normalizerMonoidHom_eq_one_iff (hZL a.2)).mp hact
      have haZmem : (a : G) ∈ S ⊓ zStar J := by simpa only [Z] using a.2
      have haCxJ : (a : G) ∈ CxK x J :=
        ⟨hJ.1.1.2.2.1 haZmem.2.1, haZmem.2.2⟩
      have haCvL : (a : G) ∈ CxK v L := ⟨hZCv a.2, haSecL⟩
      obtain ⟨n, hn⟩ := hZ2.exists_card_eq
      have ha2 : ∃ n : ℕ, (a : G) ^ 2 ^ n = 1 := by
        refine ⟨n, ?_⟩
        have hdvd : orderOf (a : G) ∣ 2 ^ n := by
          rw [← hn]
          exact Subgroup.orderOf_dvd_natCard Z a.2
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      have ha1 : (a : G) = 1 :=
        eq_one_of_mem_cxK_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
          hJ hvN hvact hxP hmax hJ hL haCxJ haCvL ha2
      exact Subtype.ext ha1
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hψker
    intro a b hab
    exact hinj (by simpa only [ψ, MonoidHom.comp_apply] using hab)
  let : MulDistribMulAction ↥Z ↥L := MulDistribMulAction.compHom ↥L ρ
  have : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have : Finite (Sylow 2 ↥L) :=
    Sylow.finite_of_finiteIndex (Classical.choice (Sylow.nonempty (p := 2) (G := ↥L)))
  obtain ⟨P, hPfix⟩ :=
    hZ2.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥L)
      (not_dvd_card_sylow (p := 2) (G := ↥L))
  have hPinv : ∀ a : ↥Z, (P : Subgroup ↥L).map (ρ a).toMonoidHom = P := by
    intro a
    have h := congrArg (fun Q : Sylow 2 ↥L => (Q : Subgroup ↥L))
      (MulAction.mem_fixedPoints.mp hPfix a)
    rw [Sylow.pointwise_smul_def] at h
    exact h
  refine ⟨g, S, hg, hS, hvS, hKzJ, hKzL, hL, hsub, hxZ, hZCv, ?_⟩
  refine ⟨eZ, e4, hZL, P, heZ, hρ_apply, hψ_inj, ?_⟩
  intro a c hc
  rw [← hPinv a]
  exact Subgroup.mem_map_of_mem (ρ a).toMonoidHom hc


private theorem false_of_rigid_actor_commutator_witness
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2)
    (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (hvN : v ∈ Subgroup.normalizer (J : Set G))
    (hvact : v ∉ CFSG.GH74.GLS.centralizerSection J
      (CFSG.GH74.GLS.pPrimeCoreOf 2 J))
    (hxP : x ∈ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s) ≤
        Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x))
    (g : G) (S : Subgroup G) :
    let L : Subgroup G := CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap g J
    let Z : Subgroup G := S ⊓ CFSG.GH74.GLS.zStar J
    ∀ (_hS : CFSG.ABGLocalTools.IsSylowOf 2 S
          (Subgroup.centralizer ({x} : Set G)))
      (_hKzJ : CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x = J)
      (_hL : L ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ v)
      (_hxZ : x ∈ Z)
      (_eZ : ↥Z ≃* Subgroup.center (CFSG.GH74.GLS.kBar J))
      (hZL : Z ≤ Subgroup.normalizer (L : Set G))
      (P : Sylow 2 ↥L),
      let ρ : ↥Z →* MulAut ↥L :=
        L.normalizerMonoidHom.comp (Subgroup.inclusion hZL)
      (∀ (a : ↥Z) (c : ↥L),
        c ∈ (P : Subgroup ↥L) → (ρ a) c ∈ (P : Subgroup ↥L)) →
      ∀ (s : ↥Z) (w : ↥L),
        orderOf s = 2 →
        orderOf w = 2 →
        w ∈ (P : Subgroup ↥L) →
        (w : G) ∈ CFSG.GH74.GLS.zStar L →
        w ∈ Subgroup.closure
          {d : ↥L | ∃ (c : ↥L) (a : ↥Z),
            c ∈ (P : Subgroup ↥L) ∧
            (ρ s) c = c ∧
            d = c⁻¹ * (ρ a) c} →
        False := by
  classical
  dsimp only
  set L : Subgroup G := CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap g J with hL_def
  set Z : Subgroup G := S ⊓ CFSG.GH74.GLS.zStar J with hZ_def
  intro hS hKzJ hL hxZ eZ hZL P
  set ρ : ↥Z →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hZL) with hρ_def
  intro hP s w hs2 hw2 hwP hwzStar hwclosure
  have hρ_apply : ∀ (a : ↥Z) (c : ↥L),
      (((ρ a) c : ↥L) : G) = (a : G) * (c : G) * (a : G)⁻¹ := by
    intro a c
    simp only [ρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion]
  have hZ2 : IsPGroup 2 ↥Z := hS.isPGroup.to_inf_left
  have hZcard : ∃ n : ℕ, Nat.card ↥Z = 2 ^ n := hZ2.exists_card_eq
  have hpowZ : ∀ a : ↥Z, ∃ n : ℕ, (a : G) ^ 2 ^ n = 1 := by
    intro a
    obtain ⟨n, hn⟩ := hZcard
    refine ⟨n, ?_⟩
    have hdvd : orderOf (a : G) ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.orderOf_dvd_natCard Z a.2
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hZcomm : ∀ a b : ↥Z, a * b = b * a := by
    intro a b
    apply eZ.injective
    apply Subtype.ext
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp (eZ a).2 (eZ b)).symm
  have hs2G : orderOf (s : G) = 2 := by
    rw [Subgroup.orderOf_coe, hs2]
  have hsZ : (s : G) ∈ zStar (Kz fullQ x) := by
    rw [hKzJ]
    exact s.2.2
  obtain ⟨Jp, hJp⟩ := exists_pump_family_of_mem_zStar_kz hnonab hs2G hsZ
  set H : Subgroup G := Kz fullQ (s : G) with hH_def
  have hJlt : PumpUpLT 2 x J (s : G) (Jp J) := hJp J hJ
  have hZleH : Z ≤ zStar H := by
    intro z hz
    have hzJ : z ∈ zStar J := hz.2
    have hz2 : ∃ n : ℕ, z ^ 2 ^ n = 1 := hpowZ ⟨z, hz⟩
    have hzc : z ∈ Subgroup.centralizer ({(s : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hZcomm ⟨z, hz⟩ s)
    have h := mem_zStar_kz_of_pumpUpLT (hK := hJ) hJlt hzJ hz2 hzc
    simpa [H] using h
  let T : Set ↥L := {d : ↥L | ∃ (c : ↥L) (a : ↥Z),
    c ∈ (P : Subgroup ↥L) ∧ (ρ s) c = c ∧ d = c⁻¹ * (ρ a) c}
  have hTsub : T ⊆ ((zStar H).comap L.subtype : Set ↥L) := by
    rintro d ⟨c, a, hcP, hsc, rfl⟩
    change ((c⁻¹ * (ρ a) c : ↥L) : G) ∈ zStar H
    have hscG : (s : G) * (c : G) * (s : G)⁻¹ = (c : G) := by
      calc (s : G) * (c : G) * (s : G)⁻¹ = (((ρ s) c : ↥L) : G) := (hρ_apply s c).symm
        _ = (c : G) := congrArg Subtype.val hsc
    have hsc_comm : (s : G) * (c : G) = (c : G) * (s : G) := by
      have h := congrArg (fun z => z * (s : G)) hscG
      simpa [mul_assoc] using h
    have hcC : (c : G) ∈ Subgroup.centralizer ({(s : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hsc_comm.symm
    have hcN : (c : G) ∈ Subgroup.normalizer (H : Set G) :=
      centralizer_le_normalizer_kz (Q := fullQ) (z := (s : G)) hcC
    have hcNz : (c : G) ∈ Subgroup.normalizer (zStar H : Set G) :=
      Alt51.mem_normalizer_zStar hcN
    have hcInvNz : (c : G)⁻¹ ∈ Subgroup.normalizer (zStar H : Set G) :=
      (Subgroup.normalizer (zStar H : Set G)).inv_mem hcNz
    have hcac : (c : G)⁻¹ * (a : G) * (c : G) ∈ zStar H := by
      have h := (Subgroup.mem_normalizer_iff.1 hcInvNz (a : G)).1 (hZleH a.2)
      simpa using h
    have hainv : (a : G)⁻¹ ∈ zStar H := (zStar H).inv_mem (hZleH a.2)
    have hprod : (c : G)⁻¹ * (a : G) * (c : G) * (a : G)⁻¹ ∈ zStar H :=
      (zStar H).mul_mem hcac hainv
    have hcoe : ((c⁻¹ * (ρ a) c : ↥L) : G) =
        (c : G)⁻¹ * (a : G) * (c : G) * (a : G)⁻¹ := by
      change (c : G)⁻¹ * (((ρ a) c : ↥L) : G) =
        (c : G)⁻¹ * (a : G) * (c : G) * (a : G)⁻¹
      rw [hρ_apply a c]
      group
    rw [hcoe]
    exact hprod
  have hwT : w ∈ Subgroup.closure T := by
    simpa [T, ρ] using hwclosure
  have hwZstarH : (w : G) ∈ zStar H := by
    have hwcomap : w ∈ (zStar H).comap L.subtype :=
      (Subgroup.closure_le _).mpr hTsub hwT
    exact hwcomap
  let R : Subgroup G := (P : Subgroup ↥L).map L.subtype
  let E : Subgroup G := R ⊔ Z
  have hR2 : IsPGroup 2 ↥R := by
    simpa [R] using P.isPGroup'.map L.subtype
  have hZNR : Z ≤ Subgroup.normalizer (R : Set G) := by
    have hforward : ∀ z : G, z ∈ Z → ∀ r : G, r ∈ R → z * r * z⁻¹ ∈ R := by
      intro z hz r hr
      obtain ⟨c, hcP, hcr⟩ := Subgroup.mem_map.mp hr
      have hzcP : (ρ ⟨z, hz⟩) c ∈ (P : Subgroup ↥L) := hP ⟨z, hz⟩ c hcP
      have hmem : (((ρ ⟨z, hz⟩) c : ↥L) : G) ∈ R :=
        Subgroup.mem_map_of_mem L.subtype hzcP
      have hcoe : (((ρ ⟨z, hz⟩) c : ↥L) : G) = z * (c : G) * z⁻¹ := by
        simpa using hρ_apply ⟨z, hz⟩ c
      rw [← hcr]
      simpa [hcoe] using hmem
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · exact hforward z hz r
    · intro hr
      have hz' : z⁻¹ ∈ Z := Z.inv_mem hz
      have h := hforward z⁻¹ hz' (z * r * z⁻¹) hr
      simpa [mul_assoc] using h
  have hE2 : IsPGroup 2 ↥E := by
    simpa [E] using
      IsPGroup.to_sup_of_normal_left' (H := R) (K := Z) hR2 hZ2 hZNR
  have hwSecH : (w : G) ∈ centralizerSection H (pPrimeCoreOf 2 H) := hwZstarH.2
  have hcomm_Z : ∀ a : ↥Z, (w : G) * (a : G) = (a : G) * (w : G) := by
    intro a
    have hwR : (w : G) ∈ R := Subgroup.mem_map_of_mem L.subtype hwP
    have hwE : (w : G) ∈ E := Subgroup.mem_sup_left hwR
    have haE : (a : G) ∈ E := Subgroup.mem_sup_right a.2
    have hcommE : ⁅(w : G), (a : G)⁆ ∈ E :=
      Subgroup.commutator_le_self E
        (Subgroup.commutator_mem_commutator (H₁ := E) (H₂ := E) hwE haE)
    have hpowE : ∃ n : ℕ, ⁅(w : G), (a : G)⁆ ^ 2 ^ n = 1 := by
      obtain ⟨k, hk⟩ := hE2.exists_orderOf_eq_pow ⟨⁅(w : G), (a : G)⁆, hcommE⟩
      refine ⟨k, ?_⟩
      have hk' : orderOf ⁅(w : G), (a : G)⁆ = 2 ^ k := by
        rw [Subgroup.orderOf_coe (⟨⁅(w : G), (a : G)⁆, hcommE⟩ : ↥E), hk]
      rw [← hk']
      exact pow_orderOf_eq_one _
    have hcommO : ⁅(w : G), (a : G)⁆ ∈ pPrimeCoreOf 2 H := by
      have hO : ⁅(a : G), (w : G)⁆ ∈ pPrimeCoreOf 2 H :=
        hwSecH.2.2 (a : G) (hZleH a.2).1
      have hsym : ⁅(w : G), (a : G)⁆ = ⁅(a : G), (w : G)⁆⁻¹ :=
        (commutatorElement_inv (a : G) (w : G)).symm
      rw [hsym]
      exact Subgroup.inv_mem _ hO
    obtain ⟨n, hn⟩ := hpowE
    have h1 : ⁅(w : G), (a : G)⁆ = 1 :=
      CFSG.GH74.GLS.Balance.SolvComp.eq_one_of_mem_pPrimeCoreOf_of_two_pow
        (C := H) hcommO hn
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hw_comm_x : (w : G) * x = x * (w : G) := hcomm_Z ⟨x, hxZ⟩
  have hsub := rigidSet_subsingleton_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2
    hxv hvx hJ hvN hvact hxP hmax
  have hwx : (w : G) * x * (w : G)⁻¹ = x := by
    rw [hw_comm_x]
    group
  have hJw : cmap (w : G) J ∈ RigidSet fullQ x := by
    have h := isRigidOfType_conj (Q := fullQ) hJ (w : G)
    rwa [hwx] at h
  have hJ_eq : cmap (w : G) J = J := (hsub x hx2) hJw hJ
  have hwNJ : (w : G) ∈ Subgroup.normalizer (J : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hJ_eq
  have hwH : (w : G) ∈ H := hwZstarH.1
  have hwNH : (w : G) ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hwH
  let D : Subgroup G := J ⊓ H
  have hwND : (w : G) ∈ Subgroup.normalizer (D : Set G) := by
    have hmem : (w : G) ∈ Subgroup.normalizer (J : Set G) ⊓
        Subgroup.normalizer (H : Set G) := ⟨hwNJ, hwNH⟩
    simpa [D] using
      (Subgroup.inf_normalizer_le_normalizer_inf (H := J) (K := H) hmem)
  have hcardmax : (RigidSet fullQ (s : G)).ncard ≤ (RigidSet fullQ x).ncard := by
    rw [← Nat.card_coe_set_eq (RigidSet fullQ (s : G)),
      ← Nat.card_coe_set_eq (RigidSet fullQ x)]
    exact hmax (s : G) hs2G
  have hxY : x ∈ Subgroup.centralizer ({(s : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hZcomm ⟨x, hxZ⟩ s))
  have hcov := rigid_product_coverage (fullQ := fullQ) Jp hxY hJp hcardmax
  have hcovJ : (D : Subgroup G) ⊔ pPrimeCoreOf 2 J = J := by
    have h := hcov.1
    rw [hKzJ] at h
    simpa [D, H] using h
  have hcovH : (D : Subgroup G) ⊔ pPrimeCoreOf 2 H = H := by
    have h := hcov.2
    rw [hKzJ] at h
    simpa [D, H] using h
  have hsupJ : (D : Subgroup G) ⊔ FooteLit.oddCoreIn J = J := by
    simpa [FooteLit.oddCoreIn, pPrimeCoreOf] using hcovJ
  have hsupH : (D : Subgroup G) ⊔ FooteLit.oddCoreIn H = H := by
    simpa [FooteLit.oddCoreIn, pPrimeCoreOf] using hcovH
  have hsurjJ : Function.Surjective
      ((QuotientGroup.mk' (pPrimeCore 2 ↥J)).comp (Subgroup.inclusion (inf_le_left : D ≤ J))) := by
    have h := Foote47.oddCoreRestriction_surjective (D := D) (K := J)
      (inf_le_left : D ≤ J) hsupJ
    simpa [Foote47.oddCoreRestriction] using h
  have hsurjH : Function.Surjective
      ((QuotientGroup.mk' (pPrimeCore 2 ↥H)).comp (Subgroup.inclusion (inf_le_right : D ≤ H))) := by
    have h := Foote47.oddCoreRestriction_surjective (D := D) (K := H)
      (inf_le_right : D ≤ H) hsupH
    simpa [Foote47.oddCoreRestriction] using h
  have : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have htrans := common_pPrimeCore_quotient_transport (p := 2) (D := D) (B := J) (H := H)
    (inf_le_left : D ≤ J) (inf_le_right : D ≤ H) hsurjJ hsurjH
  obtain ⟨-, -, e, -, -, htrans⟩ := htrans
  have htransport := htrans (w : G) hwND hwNJ hwNH
  dsimp only at htransport
  have hαiff := htransport.2.2.1
  have hwSecH : (w : G) ∈ centralizerSection H (pPrimeCoreOf 2 H) := hwZstarH.2
  have hαH : MulAut.mapQuotient (pPrimeCore 2 ↥H)
      (H.normalizerMonoidHom ⟨(w : G), hwNH⟩) = 1 :=
    (mapQuotient_normalizerMonoidHom_eq_one_iff hwNH).mpr hwSecH
  have hαJ : MulAut.mapQuotient (pPrimeCore 2 ↥J)
      (J.normalizerMonoidHom ⟨(w : G), hwNJ⟩) = 1 := hαiff.mpr hαH
  have hwSecJ : (w : G) ∈ centralizerSection J (pPrimeCoreOf 2 J) :=
    (mapQuotient_normalizerMonoidHom_eq_one_iff hwNJ).mp hαJ
  have hwCxJ : (w : G) ∈ CxK x J :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hw_comm_x, hwSecJ⟩
  have hwCvL : (w : G) ∈ CxK v L :=
    ⟨hL.1.1.2.2.1 w.2, hwzStar.2⟩
  have hwG2 : orderOf (w : G) = 2 := by
    rw [Subgroup.orderOf_coe, hw2]
  have hwGpow : (w : G) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (w : G)
    rwa [hwG2] at h
  have hwpow : ∃ n : ℕ, (w : G) ^ 2 ^ n = 1 := ⟨1, by simpa using hwGpow⟩
  have hw1G : (w : G) = 1 :=
    eq_one_of_mem_cxK_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
      hJ hvN hvact hxP hmax (I := J) (L := L) hJ hL hwCxJ hwCvL hwpow
  have hw1L : w = 1 := Subtype.ext hw1G
  rw [hw1L] at hw2
  norm_num at hw2


theorem not_inner_of_rigid_actor
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2)
    (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (hvN : v ∈ Subgroup.normalizer (J : Set G))
    (hvact : v ∉ CFSG.GH74.GLS.centralizerSection J
      (CFSG.GH74.GLS.pPrimeCoreOf 2 J))
    (hxP : x ∈ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s) ≤
        Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)) :
    MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥J)
      (J.normalizerMonoidHom ⟨v, hvN⟩) ∉
        (MulAut.conj : CFSG.GH74.GLS.kBar J →*
          MulAut (CFSG.GH74.GLS.kBar J)).range := by
  classical
  intro hinner
  obtain ⟨g, S, hcfg⟩ :=
    exists_faithful_center_action_of_inner_rigid_actor
      hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN hvact hxP hmax hinner
  let L : Subgroup G := cmap g J
  let Z : Subgroup G := S ⊓ zStar J
  dsimp only at hcfg
  rcases hcfg with
    ⟨hg, hS, hvS, hKzJ, hKzL, hL, hsub, hxZ, hZCv,
      eZ, e4, hZL, P, heZ, hact, hfaithful, hPinv⟩
  let ρ : ↥Z →* MulAut ↥L :=
    L.normalizerMonoidHom.comp (Subgroup.inclusion hZL)
  obtain ⟨eL⟩ := hL.2
  have hLq : CFSG.IsQuasisimple (CFSG.GH74.GLS.kBar L) :=
    TwoThin.isQuasisimple_hat (P92.rig_pcomp hL)
  have hL34L : CFSG.GH74.GLS.IsL34Quotient (CFSG.GH74.GLS.kBar L) :=
    TwoThin.isL34Quotient_of_mulEquiv eL.symm hL34
  have h16L : Nat.card (Subgroup.center (CFSG.GH74.GLS.kBar L)) = 16 :=
    (Nat.card_congr (Subgroup.centerCongr eL).toEquiv).trans h16
  have hA : Nonempty (↥Z ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :=
    ⟨eZ.trans e4⟩
  obtain ⟨s, w, hs2, hw2, hwP, hwzStar, hwclosure⟩ :=
    exists_involution_mem_zStar_sylow_commutator_closure
      L hLq hL34L h16L ↥Z hA ρ hfaithful P hPinv
  exact false_of_rigid_actor_commutator_witness
    hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN hvact hxP hmax
    g S hS hKzJ hL hxZ eZ hZL P hPinv s w hs2 hw2 hwP hwzStar hwclosure


end CFSG.GH74.GLS.NT44

end
