module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenDefs
import CFSG.GroupTheory.PLayer.CenterQuotientAction
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267RankAut
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup b3Lie_comp_le_or_comm
  exists_glaPComponent_map_central glaPComponent_map_fixSubgroup commutatorElement_mul_mul')
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem map_conj_one (K : Subgroup Ω) : K.map (MulAut.conj (1 : Ω)).toMonoidHom = K := by
  ext x
  simp

private theorem map_conj_map_conj (K : Subgroup Ω) (a b : Ω) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem map_conj_eq_of_mem_normalizer {K : Subgroup Ω} {a : Ω}
    (ha : a ∈ Subgroup.normalizer (K : Set Ω)) : K.map (MulAut.conj a).toMonoidHom = K := by
  have h := CFSG.LocalAnalysis.GLTheoremB.mem_normalizer_iff_gLBConj_eq.1 (Subgroup.inv_mem _ ha)
  simpa only [GLBConj, inv_inv] using h

private theorem glaPComponent_map_conj {p : ℕ} {X K : Subgroup Ω} (hK : GLAPComponent p X K)
    {g : Ω} (hg : g ∈ Subgroup.normalizer (X : Set Ω)) :
    GLAPComponent p X (K.map (MulAut.conj g).toMonoidHom) := by
  have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hK g⁻¹
  rw [CFSG.LocalAnalysis.GLTheoremB.mem_normalizer_iff_gLBConj_eq.1 (Subgroup.inv_mem _ hg)] at h
  simpa only [GLBConj, inv_inv] using h

private theorem conj_mem_closureIn {I H : Subgroup Ω} {g u : Ω} (hg : g ∈ H)
    (hu : u ∈ closureIn I H) : g * u * g⁻¹ ∈ closureIn I H := by
  have hle : closureIn I H ≤ (closureIn I H).comap (MulAut.conj g).toMonoidHom := by
    refine iSup₂_le fun a ha => ?_
    rw [← Subgroup.map_le_iff_le_comap, map_conj_map_conj]
    exact le_iSup₂_of_le (g * a) (H.mul_mem hg ha) le_rfl
  exact hle hu

private theorem not_le_centralizer_self {K : Subgroup Ω} (hK : CFSG.Open.IsQuasisimple ↥K) :
    ¬ K ≤ Subgroup.centralizer (K : Set Ω) := by
  intro h
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.1⟩
  have hbot : K = ⊥ :=
    calc K = ⁅K, K⁆ := hperf.symm
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 h
  exact (Subgroup.nontrivial_iff_ne_bot K).1
    (CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial hK) hbot

private theorem commutator_eq_bot_of_isComponentOf {X K₁ K₂ : Subgroup Ω}
    (h₁ : CFSG.Open.IsComponentOf K₁ X) (h₂ : CFSG.Open.IsComponentOf K₂ X) (hne : K₁ ≠ K₂) :
    ⁅K₁, K₂⁆ = ⊥ := by
  rcases b3Lie_comp_le_or_comm h₁ h₂.1 h₂.2.1 with h | h
  · rcases b3Lie_comp_le_or_comm h₂ h₁.1 h₁.2.1 with h' | h'
    · exact absurd (le_antisymm h h') hne
    · refine absurd ?_ (not_le_centralizer_self h₁.2.2)
      exact (Subgroup.le_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h')).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 h))
  · exact h

private theorem glaPPrimeCore_ne_top {p : ℕ} (hp : p.Prime) {X L : Subgroup Ω}
    (hL : GLAPComponent p X L) : GLAPPrimeCore p ↥L ≠ ⊤ := by
  intro htop
  haveI := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial
    (isQuasisimple_pQuot_of_glaPComponent hp hL)
  have hsub : Subsingleton (PQuot p L) := by
    show Subsingleton (↥L ⧸ GLAPPrimeCore p ↥L)
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton _ hsub

private theorem mem_centralizer_of_centMod {p : ℕ} (hp : p.Prime) {X L : Subgroup Ω}
    (hL : GLAPComponent p X L) (hq : CFSG.Open.IsQuasisimple ↥L) {g : Ω} (hc : CentMod p L g) :
    g ∈ Subgroup.centralizer (L : Set Ω) := by
  haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hOZ : GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L :=
    le_center_of_normal_of_isQuasisimple hq inferInstance (glaPPrimeCore_ne_top hp hL)
  let σ : ↥L →* ↥L := ((Subgroup.normalizerMonoidHom (H := L)) ⟨g, hc.1⟩).toMonoidHom
  have hσ : ∀ y : ↥L, ((σ y : ↥L) : Ω) = g * (y : Ω) * g⁻¹ := fun y => rfl
  have hdisp : ∀ y : ↥L, y⁻¹ * σ y ∈ Subgroup.center ↥L := by
    intro y
    have hmem : ⁅((y : ↥L) : Ω)⁻¹, g⁆ ∈ GLAPPrimeCoreOf p L :=
      hc.2 (Subgroup.commutator_mem_commutator (L.inv_mem y.2) (Subgroup.mem_zpowers g))
    have hmemL : ⁅((y : ↥L) : Ω)⁻¹, g⁆ ∈ L := Subgroup.map_subtype_le _ hmem
    have hval : y⁻¹ * σ y = ⟨⁅((y : ↥L) : Ω)⁻¹, g⁆, hmemL⟩ := by
      apply Subtype.ext
      show ((y⁻¹ * σ y : ↥L) : Ω) = ⁅((y : ↥L) : Ω)⁻¹, g⁆
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ, commutatorElement_def]
      group
    rw [hval]
    exact hOZ ((chev_mem_glaPPrimeCoreOf_iff hmemL).1 hmem)
  have hid :=
    CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement σ hdisp
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  have hfix : g * y * g⁻¹ = y := by
    have h1 : σ ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [hid]; rfl
    have h2 := congrArg Subtype.val h1
    rw [hσ] at h2
    exact h2
  exact (mul_inv_eq_iff_eq_mul.1 hfix).symm

private theorem isComponentOf_of_glaPComponent {Q : TauCeti.LieTypeIndex → Prop}
    (h2 : GenCompQuasiOn Q) {p q : ℕ} {S B : Subgroup Ω} (H : GenHyp Q p q S B) {x : Ω}
    (hxp : x ^ p = 1) (hxS : x ∉ centModSubgroup p S) {K : Subgroup Ω}
    (hK : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) K) :
    CFSG.Open.IsComponentOf K (S ⊓ Subgroup.centralizer ({x} : Set Ω)) := by
  have hp := H.pPrime
  obtain ⟨d, hdq, hQd, ⟨e⟩⟩ := H.lie
  have hperf : Group.IsPerfect ↥S := ⟨S267.perfect_of_commutator_self_eq H.perfect⟩
  have hBN : (⊤ : Subgroup Ω) ≤ Subgroup.normalizer (S : Set Ω) :=
    (Subgroup.normalizer_eq_top_iff.2 H.normal).ge
  set b : ↥(⊤ : Subgroup Ω) := ⟨x, Subgroup.mem_top x⟩ with hb
  set α : MulAut ↥S := CFSG.normalizerConjAutOfMem S ⊤ hBN b
  set β := CFSG.normalizerToCenterQuotientAut S ⊤ hBN b with hβ
  set π : ↥S →* ↥S ⧸ Subgroup.center ↥S := QuotientGroup.mk' (Subgroup.center ↥S) with hπ
  have hodd : OddLie p (↥S ⧸ Subgroup.center ↥S) d := by
    refine ⟨hp, H.pOdd, ⟨(QuotientGroup.congr _ _ ((QuotientGroup.quotientMulEquivOfEq H.core).trans
      QuotientGroup.quotientBot) (Subgroup.map_center_eq _)).symm.trans e⟩, ?_, ?_⟩
    · rw [hdq]; exact H.qOdd
    · rw [hdq]; exact H.qp.symm
  have hβp : β ^ p = 1 := by
    have hbp : b ^ p = 1 := Subtype.ext (by simp [hb, hxp])
    rw [hβ, ← map_pow, hbp, map_one]
  have hβ1 : β ≠ 1 := by
    intro h1
    rw [hβ, CFSG.normalizerToCenterQuotientAut_eq_one_iff hperf hBN b] at h1
    exact hxS (centMod_iff.1 (centMod_of_mem_centralizer h1.2))
  have hfix : (fixSubgroup α).map S.subtype = S ⊓ Subgroup.centralizer ({x} : Set Ω) :=
    CFSG.map_eqLocus_normalizerMonoidHom S (hBN b.2)
  obtain ⟨K₀, hK₀, rfl⟩ := exists_glaPComponent_map_central hp S.subtype (X := fixSubgroup α)
    (fun y hy z _ => by
      have hy1 : y = 1 := by simpa [Subgroup.ker_subtype] using hy.2
      rw [hy1, mul_one, one_mul])
    (by rw [hfix]; exact hK)
  have hπK := glaPComponent_map_fixSubgroup π (by rw [hπ, QuotientGroup.ker_mk']) α β
    (CFSG.normalizerConjAutOfMem_comp_mk S ⊤ hBN b) (QuotientGroup.mk'_surjective _) hp hK₀
  have hcomp := h2 p _ d hodd hQd β hβp hβ1 _ hπK
  have hK₀q : CFSG.Open.IsQuasisimple ↥K₀ := by
    have hker : (π.subgroupMap K₀).ker ≤ Subgroup.center ↥K₀ := by
      intro k hk
      have hk1 : π (k : ↥S) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
      have hkc : (k : ↥S) ∈ Subgroup.center ↥S := by
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk1
      exact Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 hkc y)
    have hq := (CFSG.LocalCores.isQuasisimple_iff_of_surjective
      (Subgroup.isPerfect_iff.2 (glaPComponent_perfect hK₀)) (π.subgroupMap K₀)
      (π.subgroupMap_surjective K₀) hker).2
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hcomp.2.2)
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hq
  exact ⟨hK.1, hK.2.1, CFSG.Open.IsQuasisimple.of_mulEquiv
    (Subgroup.equivMapOfInjective K₀ S.subtype S.subtype_injective).symm hK₀q⟩

private theorem commutator_mem_sup_inf {U V : Subgroup Ω} {d : Ω}
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hdU : ∀ u ∈ U, d * u * d⁻¹ ∈ U)
    (hdV : ∀ v ∈ V, d * v * d⁻¹ ∈ V) {x y : Ω}
    (hx : x ∈ (U ⊔ V) ⊓ Subgroup.centralizer ({d} : Set Ω))
    (hy : y ∈ (U ⊔ V) ⊓ Subgroup.centralizer ({d} : Set Ω)) :
    ⁅x, y⁆ ∈ (U ⊓ Subgroup.centralizer ({d} : Set Ω)) ⊔
      (V ⊓ Subgroup.centralizer ({d} : Set Ω)) := by
  have cUV : ∀ {a b : Ω}, a ∈ U → b ∈ V → Commute a b := fun ha hb => hUV _ ha _ hb
  have key : ∀ {u v : Ω}, u ∈ U → v ∈ V → u * v ∈ Subgroup.centralizer ({d} : Set Ω) →
      ∃ z ∈ U ⊓ V, d * u * d⁻¹ = u * z ∧ d * v * d⁻¹ = z⁻¹ * v := by
    intro u v hu hv huv
    have hprod : (d * u * d⁻¹) * (d * v * d⁻¹) = u * v := by
      have h := Subgroup.mem_centralizer_singleton_iff.1 huv
      calc (d * u * d⁻¹) * (d * v * d⁻¹) = d * (u * v) * d⁻¹ := by group
        _ = u * v * d * d⁻¹ := by rw [← h]
        _ = u * v := by group
    refine ⟨u⁻¹ * (d * u * d⁻¹), ⟨U.mul_mem (U.inv_mem hu) (hdU u hu), ?_⟩, by group, ?_⟩
    · have e : u⁻¹ * (d * u * d⁻¹) = v * (d * v * d⁻¹)⁻¹ := by
        calc u⁻¹ * (d * u * d⁻¹)
            = u⁻¹ * ((d * u * d⁻¹) * (d * v * d⁻¹)) * (d * v * d⁻¹)⁻¹ := by group
          _ = u⁻¹ * (u * v) * (d * v * d⁻¹)⁻¹ := by rw [hprod]
          _ = v * (d * v * d⁻¹)⁻¹ := by group
      rw [e]
      exact V.mul_mem hv (V.inv_mem (hdV v hv))
    · calc d * v * d⁻¹ = (d * u * d⁻¹)⁻¹ * ((d * u * d⁻¹) * (d * v * d⁻¹)) := by group
        _ = (d * u * d⁻¹)⁻¹ * (u * v) := by rw [hprod]
        _ = (u⁻¹ * (d * u * d⁻¹))⁻¹ * v := by group
  obtain ⟨u₁, hu₁, v₁, hv₁, rfl⟩ := CFSG.QuasithinUnique.mem_sup_of_commute hUV hx.1
  obtain ⟨u₂, hu₂, v₂, hv₂, rfl⟩ := CFSG.QuasithinUnique.mem_sup_of_commute hUV hy.1
  obtain ⟨z, hz, hzu, hzv⟩ := key hu₁ hv₁ hx.2
  obtain ⟨w, hw, hwu, hwv⟩ := key hu₂ hv₂ hy.2
  have hsplit : ⁅u₁ * v₁, u₂ * v₂⁆ = ⁅u₁, u₂⁆ * ⁅v₁, v₂⁆ := by
    have c1 : v₁ * u₂ = u₂ * v₁ := (cUV hu₂ hv₁).eq.symm
    have c2 : (v₁ * v₂ * v₁⁻¹) * u₁⁻¹ = u₁⁻¹ * (v₁ * v₂ * v₁⁻¹) :=
      (cUV (U.inv_mem hu₁) (V.mul_mem (V.mul_mem hv₁ hv₂) (V.inv_mem hv₁))).eq.symm
    have c3 : (v₁ * v₂ * v₁⁻¹ * v₂⁻¹) * u₂⁻¹ = u₂⁻¹ * (v₁ * v₂ * v₁⁻¹ * v₂⁻¹) :=
      (cUV (U.inv_mem hu₂)
        (V.mul_mem (V.mul_mem (V.mul_mem hv₁ hv₂) (V.inv_mem hv₁)) (V.inv_mem hv₂))).eq.symm
    calc ⁅u₁ * v₁, u₂ * v₂⁆
        = u₁ * (v₁ * u₂) * v₂ * v₁⁻¹ * u₁⁻¹ * v₂⁻¹ * u₂⁻¹ := by
          rw [commutatorElement_def]; group
      _ = u₁ * u₂ * ((v₁ * v₂ * v₁⁻¹) * u₁⁻¹) * v₂⁻¹ * u₂⁻¹ := by rw [c1]; group
      _ = u₁ * u₂ * u₁⁻¹ * ((v₁ * v₂ * v₁⁻¹ * v₂⁻¹) * u₂⁻¹) := by rw [c2]; group
      _ = ⁅u₁, u₂⁆ * ⁅v₁, v₂⁆ := by
          rw [c3, commutatorElement_def, commutatorElement_def]; group
  rw [hsplit]
  refine Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨?_, ?_⟩) (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
  · rw [commutatorElement_def]
    exact U.mul_mem (U.mul_mem (U.mul_mem hu₁ hu₂) (U.inv_mem hu₁)) (U.inv_mem hu₂)
  · have e : d * ⁅u₁, u₂⁆ * d⁻¹ = ⁅u₁, u₂⁆ := by
      rw [conjugate_commutatorElement, hzu, hwu]
      exact commutatorElement_mul_mul' (cUV hu₂ hz.2).symm (cUV hw.1 hz.2).symm
        (cUV hu₁ hw.2).symm
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ⁅u₁, u₂⁆ * d = (d * ⁅u₁, u₂⁆ * d⁻¹) * d := by rw [e]
      _ = d * ⁅u₁, u₂⁆ := by group
  · rw [commutatorElement_def]
    exact V.mul_mem (V.mul_mem (V.mul_mem hv₁ hv₂) (V.inv_mem hv₁)) (V.inv_mem hv₂)
  · have e : d * ⁅v₁, v₂⁆ * d⁻¹ = ⁅v₁, v₂⁆ := by
      rw [conjugate_commutatorElement, hzv, hwv, (cUV (U.inv_mem hz.1) hv₁).eq,
        (cUV (U.inv_mem hw.1) hv₂).eq]
      exact commutatorElement_mul_mul' (cUV (U.inv_mem hz.1) hv₂)
        (cUV (U.inv_mem hz.1) (V.inv_mem hw.2)) (cUV (U.inv_mem hw.1) hv₁)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ⁅v₁, v₂⁆ * d = (d * ⁅v₁, v₂⁆ * d⁻¹) * d := by rw [e]
      _ = d * ⁅v₁, v₂⁆ := by group

theorem genStep4On_of_leaves {Q : TauCeti.LieTypeIndex → Prop}
    (hLB : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → LBalanceAt G p)
    (h2 : GenCompQuasiOn Q) : GenStep4On Q := by
  intro p q Ω _ _ S B H hI B' d J hmax _ d₁ hd₁ hd₁J hd₁S
  have hp := H.pPrime
  obtain ⟨⟨hFB, hdB', hdS, hJ⟩, hJmax⟩ := hmax
  have hB'el := hFB.1
  have hdp : d ^ p = 1 := hB'el.2 d hdB'
  have hd₁p : d₁ ^ p = 1 := hB'el.2 d₁ hd₁
  have hdd₁ : d * d₁ = d₁ * d := isElemAbelian_commute hB'el hdB' hd₁
  have hBB' : Nat.card B ≤ Nat.card B' := by
    rcases hFB.2.2 with h | ⟨h, -⟩
    · rw [h]
    · exact h
  have hJc := isComponentOf_of_glaPComponent h2 H hdp hdS hJ
  have hd₁C := mem_centralizer_of_centMod hp hJ hJc.2.2 hd₁J
  set C : Subgroup Ω := Subgroup.centralizer ({d} : Set Ω)
  set X : Subgroup Ω := S ⊓ Subgroup.centralizer ({d₁} : Set Ω)
  have hcomp : ∀ K, GLAPComponent p X K → CFSG.Open.IsComponentOf K X := fun K hK =>
    isComponentOf_of_glaPComponent h2 H hd₁p hd₁S hK
  have hEX : GLAPLayer p X ≤ X := sSup_le fun L hL => hL.1
  have hdX : d ∈ Subgroup.normalizer (X : Set Ω) := by
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, ?_⟩
    · rw [Subgroup.normalizer_eq_top_iff.2 H.normal]
      exact Subgroup.mem_top d
    · exact Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2 hdd₁)
  set P : Subgroup Ω := Subgroup.zpowers d
  have hPX : P ≤ Subgroup.normalizer (X : Set Ω) := Subgroup.zpowers_le.2 hdX
  have hPp : IsPGroup p P := (isPGroup_of_isElemAbelian hB'el).to_le (Subgroup.zpowers_le.2 hdB')
  have hbal := glaPLayer_inf_centralizer_le hp (hLB Ω p hp) (H.kGroup.subgroup (X ⊔ P)) hPp hPX
  have hJX : J ≤ X := le_inf (hJ.1.trans inf_le_left) fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hd₁C j hj)
  have hJY : J ≤ X ⊓ Subgroup.centralizer (P : Set Ω) := by
    refine le_inf hJX fun j hj => Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hjd : Commute j d := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hj).2
    exact (hjd.symm.zpow_left k).eq
  have hYS : X ⊓ Subgroup.centralizer (P : Set Ω) ≤ S ⊓ C :=
    inf_le_inf inf_le_left
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Subgroup.mem_zpowers d)))
  have hJE : J ≤ GLAPLayer p X :=
    (show J ≤ GLAPLayer p (X ⊓ Subgroup.centralizer (P : Set Ω)) from
      le_sSup (glaPComponent_of_le hp hJ hJY hYS)).trans hbal
  obtain ⟨K, hK, hJK⟩ : ∃ K, GLAPComponent p X K ∧ ¬ K ≤ Subgroup.centralizer (J : Set Ω) := by
    by_contra hno
    have hEC : GLAPLayer p X ≤ Subgroup.centralizer (J : Set Ω) :=
      sSup_le fun K hK => not_not.1 fun h => hno ⟨K, hK, h⟩
    exact not_le_centralizer_self hJc.2.2 (hJE.trans hEC)
  set U : Subgroup Ω := closureIn K P
  set V : Subgroup Ω := sSup {K' | GLAPComponent p X K' ∧
    ∀ a ∈ P, K' ≠ K.map (MulAut.conj a).toMonoidHom}
  have hconjK : ∀ a ∈ P, GLAPComponent p X (K.map (MulAut.conj a).toMonoidHom) :=
    fun a ha => glaPComponent_map_conj hK (hPX ha)
  have hUE : U ≤ GLAPLayer p X := iSup₂_le fun a ha => le_sSup (hconjK a ha)
  have hVE : V ≤ GLAPLayer p X := sSup_le fun K' hK' => le_sSup hK'.1
  have hKU : K ≤ U := le_iSup₂_of_le (1 : Ω) P.one_mem (map_conj_one K).ge
  have hUV : U ≤ Subgroup.centralizer (V : Set Ω) := by
    refine iSup₂_le fun a ha => ?_
    rw [Subgroup.le_centralizer_iff]
    refine sSup_le fun K' hK' => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (commutator_eq_bot_of_isComponentOf (hcomp _ hK'.1) (hcomp _ (hconjK a ha)) (hK'.2 a ha))
  have hUVc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u := fun u hu v hv =>
    (Subgroup.mem_centralizer_iff.1 (hUV hu) v hv).symm
  have hEUV : GLAPLayer p X ≤ U ⊔ V := by
    refine sSup_le fun K' hK' => ?_
    by_cases h : ∃ a ∈ P, K' = K.map (MulAut.conj a).toMonoidHom
    · obtain ⟨a, ha, rfl⟩ := h
      exact le_sup_of_le_left (le_iSup₂_of_le a ha le_rfl)
    · exact le_sup_of_le_right (le_sSup ⟨hK', fun a ha he => h ⟨a, ha, he⟩⟩)
  have hdU : ∀ u ∈ U, d * u * d⁻¹ ∈ U := fun u hu =>
    conj_mem_closureIn (Subgroup.mem_zpowers d) hu
  have hdV : ∀ v ∈ V, d * v * d⁻¹ ∈ V := by
    have hle : V ≤ V.comap (MulAut.conj d).toMonoidHom := by
      refine sSup_le fun K' hK' => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      refine le_sSup ⟨glaPComponent_map_conj hK'.1 hdX, fun a ha he => hK'.2 (d⁻¹ * a)
        (P.mul_mem (P.inv_mem (Subgroup.mem_zpowers d)) ha) ?_⟩
      have h := congrArg (Subgroup.map (MulAut.conj d⁻¹).toMonoidHom) he
      rwa [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel, map_conj_one] at h
    exact fun v hv => hle hv
  set W : Subgroup Ω := (U ⊔ V) ⊓ C
  have hWS : W ≤ S ⊓ C := inf_le_inf_right _ ((sup_le hUE hVE).trans (hEX.trans inf_le_left))
  have hJW : J ≤ W := le_inf (hJE.trans hEUV) (hJ.1.trans inf_le_right)
  have hJWc : CFSG.Open.IsComponentOf J W := by
    refine ⟨hJW, ?_, hJc.2.2⟩
    have h := hJc.2.1.inf W
    rwa [inf_eq_left.2 hJW, inf_eq_right.2 hWS] at h
  have hsn : ∀ M : Subgroup Ω, U ⊔ V ≤ Subgroup.normalizer (M : Set Ω) → M ≤ U ⊔ V →
      CFSG.Open.IsSubnormal (M ⊓ C) W := by
    intro M hMN hM
    have hle : M ⊓ C ≤ W := inf_le_inf_right _ hM
    refine CFSG.Open.IsSubnormal.step hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_) (CFSG.Open.IsSubnormal.refl W)
    exact (inf_le_inf_right _ hMN).trans ((inf_le_inf_left _ Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf)
  have hUVN : U ⊔ V ≤ Subgroup.normalizer (U : Set Ω) :=
    sup_le Subgroup.le_normalizer
      ((Subgroup.le_centralizer_iff.1 hUV).trans (Subgroup.centralizer_le_normalizer _))
  have hUVN' : U ⊔ V ≤ Subgroup.normalizer (V : Set Ω) :=
    sup_le (hUV.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hJU : J ≤ U := by
    rcases b3Lie_comp_le_or_comm hJWc (inf_le_inf_right _ le_sup_left)
        (hsn U hUVN le_sup_left) with h | h
    · exact h.trans inf_le_left
    rcases b3Lie_comp_le_or_comm hJWc (inf_le_inf_right _ le_sup_right)
        (hsn V hUVN' le_sup_right) with h' | h'
    · exact absurd ((hKU.trans hUV).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (h'.trans inf_le_left)))) hJK
    · exfalso
      have hJM : J ≤ (U ⊓ C) ⊔ (V ⊓ C) :=
        calc J = ⁅J, J⁆ := (glaPComponent_perfect hJ).symm
          _ ≤ _ := Subgroup.commutator_le.2 fun x hx y hy =>
            commutator_mem_sup_inf hUVc hdU hdV (hJW hx) (hJW hy)
      refine not_le_centralizer_self hJc.2.2 (hJM.trans (sup_le ?_ ?_))
      · exact Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h)
      · exact Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h')
  have hKJ : Nat.card K ≤ Nat.card J := hJmax B' d₁ K ⟨hFB, hd₁, hd₁S, hK⟩
  by_cases hdK : d ∈ Subgroup.normalizer (K : Set Ω)
  ·
    have hUK : U ≤ K := iSup₂_le fun a ha =>
      (map_conj_eq_of_mem_normalizer (Subgroup.zpowers_le.2 hdK ha)).le
    rw [Subgroup.eq_of_le_of_card_ge (hJU.trans hUK) hKJ]
    exact hK
  ·
    exfalso
    obtain ⟨hp3, -, -, -, hsmall⟩ :=
      hI B' d₁ K hB'el hBB' hd₁ hd₁S hK fun h => hdK (h hdB')
    have hUB : U ≤ closureIn K B' := iSup₂_le fun a ha =>
      le_iSup₂_of_le a (Subgroup.zpowers_le.2 hdB' ha) le_rfl
    have hKS : closureIn K B' ≤ S := iSup₂_le fun a _ =>
      Subgroup.map_le_iff_le_comap.2 fun k hk => H.normal.conj_mem k ((hK.1.trans inf_le_left) hk) a
    subst hp3
    have hJ3 : GLAPComponent 3 (closureIn K B' ⊓ C) J :=
      glaPComponent_of_le hp hJ (le_inf (hJU.trans hUB) (hJ.1.trans inf_le_right))
        (inf_le_inf_right _ hKS)
    have hlt := hsmall d hdB' hdK J hJ3
    omega

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
