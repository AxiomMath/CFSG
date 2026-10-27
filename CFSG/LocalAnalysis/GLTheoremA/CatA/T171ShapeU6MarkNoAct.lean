module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Mark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSetup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniGeom

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem commutator_range_le_inner
    {Ω R : Type} [Group Ω] [Group R] {L : Subgroup Ω} [L.Normal]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hL : commutator ↥L = ⊤) {p : ℕ}
    {I : Set (MulAut R)} {D : Subgroup (MulAut R)}
    (hDn : D.Normal) (hID : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ D)
    (hodd : Odd ((MulAut.conj : R →* MulAut R).range.relIndex D))
    {B A T : Subgroup Ω} (hAelem : IsElemAbelian p A) (hT2 : IsPGroup 2 T)
    (hBN : B ≤ Subgroup.normalizer (L : Set Ω))
    (hAB : A ≤ B)
    (hAI : ∀ a ha, ggLAut L θ ⟨a, hBN (hAB ha)⟩ ∈ I)
    (hTN : T ≤ Subgroup.normalizer (L : Set Ω))
    (hBT : B ≤ Subgroup.normalizer (T : Set Ω)) :
    ⁅((ggLAut L θ).comp (Subgroup.inclusion hTN)).range,
      ((ggLAut L θ).comp (Subgroup.inclusion (fun a ha => hBN (hAB ha)))).range⁆ ≤
      (MulAut.conj : R →* MulAut R).range := by
  rw [Subgroup.commutator_le]
  rintro _ ⟨⟨t, ht⟩, rfl⟩ _ ⟨⟨a, haA⟩, rfl⟩
  have hzT : ⁅(t : Ω), (a : Ω)⁆ ∈ T := by
    have h1 : (a : Ω) * (t : Ω)⁻¹ * (a : Ω)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hBT (hAB haA)) (t : Ω)⁻¹).mp (T.inv_mem ht)
    have hz : ⁅(t : Ω), (a : Ω)⁆ = (t : Ω) * ((a : Ω) * (t : Ω)⁻¹ * (a : Ω)⁻¹) := by
      rw [commutatorElement_def]; group
    rw [hz]
    exact T.mul_mem ht h1
  have hzN : ⁅(t : Ω), (a : Ω)⁆ ∈ Subgroup.normalizer (L : Set Ω) := hTN hzT
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT2 ⟨_, hzT⟩
  rw [Subgroup.orderOf_mk] at hk
  have hzpow : ⁅(t : Ω), (a : Ω)⁆ ^ 2 ^ k = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  have hzmap : ggLAut L θ ⟨⁅(t : Ω), (a : Ω)⁆, hzN⟩ =
      ⁅ggLAut L θ ⟨(t : Ω), hTN ht⟩, ggLAut L θ ⟨(a : Ω), hBN (hAB haA)⟩⁆ := by
    have h1 : (⟨⁅(t : Ω), (a : Ω)⁆, hzN⟩ : Subgroup.normalizer (L : Set Ω)) =
        ⁅(⟨(t : Ω), hTN ht⟩ : Subgroup.normalizer (L : Set Ω)),
          (⟨(a : Ω), hBN (hAB haA)⟩ : Subgroup.normalizer (L : Set Ω))⁆ :=
      Subtype.ext rfl
    rw [h1, map_commutatorElement]
  have hgaD : ggLAut L θ ⟨(a : Ω), hBN (hAB haA)⟩ ∈ D := by
    have hpowN : (⟨(a : Ω), hBN (hAB haA)⟩ : Subgroup.normalizer (L : Set Ω)) ^ p = 1 := by
      ext
      simpa using hAelem.2 a haA
    have hpow : (ggLAut L θ ⟨(a : Ω), hBN (hAB haA)⟩) ^ p = 1 := by
      rw [← map_pow, hpowN, map_one]
    exact hID _ (hAI a haA) hpow
  have hDmem : ⁅ggLAut L θ ⟨(t : Ω), hTN ht⟩,
      ggLAut L θ ⟨(a : Ω), hBN (hAB haA)⟩⁆ ∈ D := by
    rw [commutatorElement_def]
    exact D.mul_mem (hDn.conj_mem _ hgaD _) (D.inv_mem hgaD)
  have hzpowN : (⟨⁅(t : Ω), (a : Ω)⁆, hzN⟩ : Subgroup.normalizer (L : Set Ω)) ^ 2 ^ k = 1 := by
    ext
    simpa using hzpow
  have hpow0 : (ggLAut L θ ⟨⁅(t : Ω), (a : Ω)⁆, hzN⟩) ^ 2 ^ k = 1 := by
    rw [← map_pow, hzpowN, map_one]
  have hpow : (⁅ggLAut L θ ⟨(t : Ω), hTN ht⟩,
      ggLAut L θ ⟨(a : Ω), hBN (hAB haA)⟩⁆) ^ 2 ^ k = 1 := by
    rw [← hzmap]
    exact hpow0
  exact mem_range_conj_of_pow_two_pow hodd hDmem hpow

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem t171NoActFact_of
    (h9 : U6Type9) (hn : U6NoActModel) (hE : TwE6NoAct) :
    T171.T171NoActFact := by
  intro p Ω _ _ B x L D K β hKis hcfg hmax hLN hpre hKcomp hch hβB hβD hni hext T hTN hTx hT2 hBT
  have hext0 := hext
  obtain ⟨hp3, n, hnodd, hcase⟩ := hext
  subst hp3
  rcases hcase with hU6 | hTE6
  · obtain ⟨A, d, hAB, hxA, hSetup, hcardB⟩ :=
      setup_of_cfg hcfg hpre hKcomp hch hβB hβD hni
    obtain ⟨K', hKfield, hKfinite, hfield, θ, hmark⟩ :=
      u6Marking_holds Ω L K A d β n hSetup hU6 hnodd
    letI := hKfield
    letI := hKfinite
    letI := hfield
    letI : CharP K' 2 := hfield.charP
    haveI : L.Normal := hLN
    have hL : commutator ↥L = ⊤ := hcfg.qs.1
    have hpq : 3 ∣ 2 ^ n + 1 := by
      obtain ⟨k, rfl⟩ := hnodd
      have h : ((2 : ZMod 3) ^ (2 * k + 1) + 1) = 0 := by
        have h1 : ((-1 : ZMod 3)) ^ (2 * k) = 1 := by
          rw [pow_mul]
          norm_num
        rw [show (2 : ZMod 3) = -1 by decide, pow_succ, h1]
        ring
      exact (ZMod.natCast_eq_zero_iff _ 3).mp (by push_cast; exact h)
    have hKcard : Nat.card K' = (2 ^ n) ^ 2 := by
      rw [hfield.card, ← pow_mul, Nat.mul_comm n 2]
    let N := Subgroup.normalizer (L : Set Ω)
    have hBN : B ≤ N := hcfg.norm
    have hAN : A ≤ N := fun a ha => hBN (hAB ha)
    let R := LargeEvenProj (unitarySU 2 n K' 6)
    let lam : N →* MulAut R := CFSG.StandardType.ggLAut L θ
    let lamA : A →* MulAut R := lam.comp (Subgroup.inclusion hAN)
    let lamB : B →* MulAut R := lam.comp (Subgroup.inclusion hBN)
    let Ab : Subgroup (MulAut R) := lamA.range
    let lamT : Subgroup (MulAut R) := (lam.comp (Subgroup.inclusion hTN)).range
    let T1 : Subgroup (MulAut R) := ⁅lamT, Ab⁆
    have hAI : ∀ a ha, CFSG.StandardType.ggLAut L θ ⟨a, hAN ha⟩ ∈
        LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K' 6))
          (LargeEvenGUSet (Fin 6) K' (2 ^ n)) :=
      fun a ha => CFSG.StandardType.ggLAut_mem_of_induces L θ hAN hmark ha
    have hmapAb : Subgroup.map lam (A.subgroupOf N) = Ab := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a.1, ha⟩, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨⟨a.1, hAN a.2⟩, a.2, rfl⟩
    have hAb : IsElemAbelian 3 Ab := by
      have h := (hSetup.elem.subgroupOf N).map lam
      rwa [hmapAb] at h
    have hkerA : lamA.ker = ⊥ := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_bot]
      constructor
      · intro h
        have hc : (a : Ω) ∈ Subgroup.centralizer (L : Set Ω) :=
          CFSG.StandardType.mem_centralizer_of_ggLAut_eq_one L θ hL h
        have hmem : (a : Ω) ∈ A ⊓ Subgroup.centralizer (L : Set Ω) := ⟨a.2, hc⟩
        rw [hSetup.faithful] at hmem
        exact Subtype.ext (by simpa using hmem)
      · intro ha
        rw [ha, map_one]
    have hcardA' : Nat.card Ab = Nat.card A := by
      have h := Subgroup.card_ker_mul_card_range lamA
      rw [hkerA, Subgroup.card_bot, one_mul] at h
      change Nat.card lamA.range = Nat.card A
      exact h
    have hkerB : lamB.ker = (Subgroup.zpowers x).subgroupOf B := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        exact (hcfg.cent b b.2).1
          (CFSG.StandardType.mem_centralizer_of_ggLAut_eq_one L θ hL h)
      · intro hx
        exact CFSG.StandardType.ggLAut_eq_one_of_mem_centralizer L θ ((hcfg.cent b b.2).2 hx)
    have hcardB' : Nat.card lamB.range = Nat.card A := by
      have h := Subgroup.card_ker_mul_card_range lamB
      have hker : Nat.card ((Subgroup.zpowers x).subgroupOf B) = 3 := by
        rw [Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hcfg.mem)).toEquiv,
          Nat.card_zpowers, orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one]
      rw [hkerB, hker, hcardB] at h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
    have hAb_le_Bt : Ab ≤ lamB.range := by
      rintro _ ⟨a, rfl⟩
      exact ⟨⟨a, hAB a.2⟩, rfl⟩
    have hAb_eq_Bt : Ab = lamB.range := by
      refine Subgroup.eq_of_le_of_card_ge hAb_le_Bt ?_
      rw [hcardB']
      exact Nat.le_of_eq hcardA'.symm
    have hAbNT : Ab ≤ Subgroup.normalizer (lamT : Set (MulAut R)) := by
      rw [hAb_eq_Bt, Subgroup.le_normalizer_iff]
      rintro _ ⟨⟨b, hb⟩, rfl⟩ x hx
      obtain ⟨⟨t, ht⟩, rfl⟩ := hx
      refine ⟨⟨b * t * b⁻¹, (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht⟩, ?_⟩
      change lam ⟨b * t * b⁻¹, _⟩ =
        lam ⟨b, hBN hb⟩ * lam ⟨t, hTN ht⟩ * (lam ⟨b, hBN hb⟩)⁻¹
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
    have hT1_le_lamT : T1 ≤ lamT := by
      have h := (Subgroup.le_normalizer_iff_commutator_le_right (H := Ab) (K := lamT)).mp hAbNT
      rwa [Subgroup.commutator_comm] at h
    have hlamT2 : IsPGroup 2 lamT :=
      hT2.of_surjective ((lam.comp (Subgroup.inclusion hTN)).rangeRestrict)
        (MonoidHom.rangeRestrict_surjective _)
    have hT1_2 : IsPGroup 2 T1 := hlamT2.to_le hT1_le_lamT
    have hOD := CFSG.StandardType.InndiagSU.ggOutdiagOdd_unitary (n := n) (d := 6)
      (K := K') hKcard hfield.one_le (by norm_num) (by norm_num) 3
    obtain ⟨D, hDn, hID, hodd⟩ := hOD
    have hT1_le_inn : T1 ≤ (MulAut.conj : R →* MulAut R).range := by
      have h := commutator_range_le_inner (L := L) θ hL (p := 3) (I :=
        LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K' 6))
          (LargeEvenGUSet (Fin 6) K' (2 ^ n))) (D := D) hDn hID hodd
        hSetup.elem hT2 hBN hAB hAI hTN hBT
      simpa [T1, lamT, Ab, lam, lamA, lamB, R] using h
    have hRsimple_na := CFSG.LocalAnalysis.GLTheoremA.T156.Uni.simple_noncomm_proj
      (d := 6) (k := K') (g := n) hKcard (by norm_num) (by norm_num)
    haveI : IsSimpleGroup R := hRsimple_na.1
    have hRnc : ¬ IsMulCommutative R := by
      intro h
      obtain ⟨a, b, hab⟩ := hRsimple_na.2
      exact hab (h.is_comm.comm a b)
    have hRcenter : Subgroup.center R = ⊥ :=
      TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hRnc
    have hconjinj : Function.Injective (MulAut.conj : R →* MulAut R) := by
      intro a b hab
      have h1 : MulAut.conj (a⁻¹ * b) = 1 := by
        rw [map_mul, map_inv, hab, inv_mul_cancel]
      have hc : a⁻¹ * b ∈ Subgroup.center R := by
        rw [Subgroup.mem_center_iff]
        intro r
        have h := congrArg (fun f : MulAut R => f r) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h
        have h3 : (a⁻¹ * b) * r = r * (a⁻¹ * b) := by
          rw [← mul_inv_eq_iff_eq_mul]
          exact h
        simpa only [mul_assoc] using h3.symm
      rw [hRcenter] at hc
      exact inv_mul_eq_one.mp (by simpa using hc)
    let V : Subgroup R := T1.comap (MulAut.conj : R →* MulAut R)
    by_contra hne
    have hT1ne : T1 ≠ ⊥ := by
      intro hbot
      apply hne
      rw [Subgroup.commutator_le]
      intro t ht b hb
      have hbz : lamB ⟨b, hb⟩ ∈ Ab := by
        rw [hAb_eq_Bt]
        exact ⟨⟨b, hb⟩, rfl⟩
      have hmem : ⁅(lam.comp (Subgroup.inclusion hTN)) ⟨t, ht⟩, lamB ⟨b, hb⟩⁆ ∈ T1 :=
        Subgroup.commutator_mem_commutator (MonoidHom.mem_range.mpr ⟨⟨t, ht⟩, rfl⟩) hbz
      rw [hbot] at hmem
      have hcomm : ⁅(lam.comp (Subgroup.inclusion hTN)) ⟨t, ht⟩, lamB ⟨b, hb⟩⁆ = 1 := by
        simpa using hmem
      have hzN : ⁅t, b⁆ ∈ N :=
        N.mul_mem (N.mul_mem (N.mul_mem (hTN ht) (hBN hb)) (N.inv_mem (hTN ht)))
          (N.inv_mem (hBN hb))
      have hlz : lam ⟨⁅t, b⁆, hzN⟩ = 1 := by
        have h1 : lam ⟨⁅t, b⁆, hzN⟩ = ⁅lam ⟨t, hTN ht⟩, lam ⟨b, hBN hb⟩⁆ := by
          have h := map_commutatorElement lam
            (⟨t, hTN ht⟩ : Subgroup.normalizer (L : Set Ω))
            (⟨b, hBN hb⟩ : Subgroup.normalizer (L : Set Ω))
          convert h using 3 <;> rfl
        rw [h1]
        exact hcomm
      exact CFSG.StandardType.mem_centralizer_of_ggLAut_eq_one L θ hL hlz
    have hV2 : IsPGroup 2 V :=
      hT1_2.comap_of_injective (MulAut.conj : R →* MulAut R) hconjinj
    have hVne : V ≠ ⊥ := by
      intro hVbot
      apply hT1ne
      have hmap := Subgroup.map_comap_eq_self (f := (MulAut.conj : R →* MulAut R)) hT1_le_inn
      change Subgroup.map (MulAut.conj : R →* MulAut R) V = T1 at hmap
      rw [hVbot, Subgroup.map_bot] at hmap
      exact hmap.symm
    have hAbV : ∀ φ ∈ Ab, ∀ v ∈ V, φ v ∈ V := by
      intro φ hφ v hv
      change MulAut.conj (φ v) ∈ T1
      have h1 : (MulAut.conj (φ v) : MulAut R) = φ * MulAut.conj v * φ⁻¹ := by
        ext w
        simp [MulAut.conj_apply, MulAut.mul_apply]
      rw [h1]
      have hNT1 : Ab ≤ Subgroup.normalizer (T1 : Set (MulAut R)) :=
        Subgroup.normalizer_commutator_ge_right lamT Ab
      exact (Subgroup.mem_normalizer_iff.mp (hNT1 hφ) (MulAut.conj v)).mp hv
    have hID_inndiag : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K' 6))
        (LargeEvenGUSet (Fin 6) K' (2 ^ n)),
        φ ∈ CFSG.StandardType.InndiagSU.inndiagU (d := 6) hfield (by norm_num) := by
      intro φ hφ
      exact (CFSG.StandardType.InndiagSU.mem_inndiagU (d := 6) (h := hfield)
        (hd := by norm_num)).mpr
        (CFSG.StandardType.InndiagSU.congr_mem_primeFormD (d := 6) (K := K') hfield
          (by norm_num) hKcard hφ)
    have hAbD : Ab ≤ CFSG.StandardType.InndiagSU.inndiagU (d := 6) hfield (by norm_num) := by
      rintro _ ⟨a, rfl⟩
      exact hID_inndiag _ (hAI a a.2)
    have hA27 : 3 ^ 3 ≤ Nat.card A := by
      have h' : 3 * 3 ^ 3 ≤ 3 * Nat.card A := by
        have h := hcfg.card_ge
        rw [hcardB] at h
        norm_num at h ⊢
        exact h
      exact Nat.le_of_mul_le_mul_left h' (by norm_num)
    have hcardAb27 : 3 ^ 3 ≤ Nat.card Ab := by
      rw [hcardA']
      exact hA27
    have hdinvA : d⁻¹ ∈ A := A.inv_mem hSetup.d_mem
    have hdN : d⁻¹ ∈ N := hAN hdinvA
    obtain ⟨φd, hφdI, hφdind⟩ := hmark d hSetup.d_mem
    have hφdeq : φd = CFSG.StandardType.ggLAut L θ ⟨d⁻¹, hdN⟩ :=
      CFSG.StandardType.eq_ggLAut_of_induces L θ (hAN hSetup.d_mem) hφdind
    have hφdfield : FieldType hfield (CFSG.StandardType.ggLAut L θ ⟨d⁻¹, hdN⟩) := by
      rw [← hφdeq]
      exact h9 Ω L K A d β n K' hfield θ hSetup hpq hmark φd hφdind
    have hφdAb : CFSG.StandardType.ggLAut L θ ⟨d⁻¹, hdN⟩ ∈ Ab := by
      refine ⟨⟨d⁻¹, hdinvA⟩, rfl⟩
    have hVbot : V = ⊥ :=
      hn n K' hfield hpq Ab hAb hAbD hcardAb27
        ⟨_, hφdAb, hφdfield⟩ V hV2 hAbV
    rw [hVbot] at hVne
    exact hVne rfl
  · exact hE 3 Ω B x L D K β n hKis hcfg hmax hLN hpre hKcomp hch hβB hβD hni
      hext0 hTE6 hnodd T hTN hTx hT2 hBT

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
