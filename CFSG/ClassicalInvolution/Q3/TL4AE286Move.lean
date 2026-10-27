module

public import CFSG.ClassicalInvolution.Q3.TL4AE286Link
public import CFSG.ClassicalInvolution.Q3.TL4OddMu6

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent)

section Gen

theorem isPGroup_zpowers_of_pow_three_pow {G : Type*} [Group G] {g : G} {a : ℕ}
    (h : g ^ 3 ^ a = 1) : IsPGroup 3 (Subgroup.zpowers g) := by
  rintro ⟨z, hz⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨a, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, h, one_zpow]

theorem exists_pow_map_eq_of_pow_three {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (w : G) {x : H} (hw : f w = x) (hx : x ^ 3 = 1) :
    ∃ e : ℕ, f (w ^ e) = x ∧ ∃ a : ℕ, (w ^ e) ^ 3 ^ a = 1 := by
  obtain ⟨a, s, hs, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos w).ne' 3 (by norm_num)
  refine ⟨s * s, ?_, a, ?_⟩
  · have hs2 : s * s % 3 = 1 := by
      have : s % 3 = 1 ∨ s % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    rw [map_pow, hw, pow_eq_pow_mod _ hx, hs2, pow_one]
  · rw [← pow_mul, show s * s * 3 ^ a = (3 ^ a * s) * s by ring, ← hN, pow_mul,
      pow_orderOf_eq_one, one_pow]

theorem mem_normalizer_of_forall_conj_mem {G : Type} [Group G] [Finite G] {T : Subgroup G}
    {g : G} (h : ∀ x ∈ T, g * x * g⁻¹ ∈ T) : g ∈ Subgroup.normalizer (T : Set G) := by
  have hle : conjSub g T ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  refine mem_normalizer_iff_conjSub_eq.mpr (Subgroup.eq_of_le_of_card_ge hle ?_)
  exact (Subgroup.card_map_of_injective (K := T) (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective).ge

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem eq_of_mk_eq_of_isPGroup {D : Subgroup G} (hD2 : IsPGroup 2 D) {a b : ↥(layerY Ω x)}
    (ha : (a : G) ∈ D) (hb : (b : G) ∈ D)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) a =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) b) : a = b := by
  have h1 : a⁻¹ * b ∈ classicalInvolutionOddCore ↥(layerY Ω x) := QuotientGroup.eq.mp h
  have h2 : ((a⁻¹ * b : ↥(layerY Ω x)) : G) ∈ D ⊓ oddCoreOf (layerY Ω x) :=
    ⟨by simpa using D.mul_mem (D.inv_mem ha) hb, ⟨_, h1, rfl⟩⟩
  rw [S1916.inf_oddCoreOf_eq_bot hD2, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.mp (Subtype.ext h2)

theorem exists_lift_mem_normalizer {D : Subgroup G} (hD2 : IsPGroup 2 D) (hDY : D ≤ layerY Ω x)
    (yb : SecQuot Ω x)
    (hyb : ∀ d : ↥(layerY Ω x), (d : G) ∈ D → ∃ d' : ↥(layerY Ω x), (d' : G) ∈ D ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) d' =
        yb * QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) d * yb⁻¹) :
    ∃ w : ↥(layerY Ω x), QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) w = yb ∧
      (w : G) ∈ Subgroup.normalizer (D : Set G) := by
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥(layerY Ω x)) yb
  have hNodd : Odd (Nat.card ↥(oddCoreOf (layerY Ω x))) := oddCoreOf_odd_natCard _
  have hDN : D ≤ Subgroup.normalizer (oddCoreOf (layerY Ω x) : Set G) := fun d hd =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hDY hd))
  have hle : conjSub (y₀ : G) D ≤ oddCoreOf (layerY Ω x) ⊔ D := by
    intro z hz
    rw [mem_conjSub_iff] at hz
    obtain ⟨d', hd'D, hd'e⟩ := hyb ⟨_, hDY hz⟩ hz
    have hzY : z ∈ layerY Ω x := by
      have e : z = (y₀ : G) * ((y₀ : G)⁻¹ * z * y₀) * (y₀ : G)⁻¹ := by group
      rw [e]
      exact (layerY Ω x).mul_mem ((layerY Ω x).mul_mem y₀.2 (hDY hz))
        ((layerY Ω x).inv_mem y₀.2)
    have hze : (⟨z, hzY⟩ : ↥(layerY Ω x)) = y₀ * ⟨_, hDY hz⟩ * y₀⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hmk : QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) d' =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨z, hzY⟩ := by
      rw [hd'e, hze, map_mul, map_mul, map_inv]
    have h1 := QuotientGroup.eq.mp hmk
    have h2 : (d' : G)⁻¹ * z ∈ oddCoreOf (layerY Ω x) := ⟨_, h1, by simp⟩
    have e : z = (d' : G) * ((d' : G)⁻¹ * z) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hd'D) (Subgroup.mem_sup_left h2)
  have hcard : Nat.card ↥(conjSub (y₀ : G) D) = Nat.card ↥D :=
    (Nat.card_congr (Subgroup.equivMapOfInjective D (MulAut.conj (y₀ : G)).toMonoidHom
      (MulAut.conj (y₀ : G)).injective).toEquiv).symm
  obtain ⟨ν, hν, hνD⟩ := Q3T7M.CentQ.exists_conjSub_of_le_sup_odd hDN hNodd
    (S1916.inf_oddCoreOf_eq_bot hD2 _) hD2 (isPGroup_conjSub _ hD2) hcard hle
  obtain ⟨hνY, hνO⟩ := mem_oddCoreOf_iff.mp hν
  have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨ν, hνY⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hνO
  refine ⟨⟨ν, hνY⟩⁻¹ * y₀, ?_, ?_⟩
  · rw [map_mul, map_inv, h1, inv_one, one_mul]
  · rw [mem_normalizer_iff_conjSub_eq]
    show conjSub (ν⁻¹ * (y₀ : G)) D = D
    rw [conjSub_mul, ← hνD, conjSub_inv_conjSub]

end Gen

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_moveY_of_linkAEAt (hL : TightLargeHypR r n Y R S t) (hAE : LinkAEAt R t)
    {M : Subgroup Y} (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    ∃ y : Y, IsPGroup 3 (Subgroup.zpowers y) ∧ y ∈ Subgroup.centralizer ({t} : Set Y) ∧
      (∃ T : Subgroup Y, IsSylow2In T M ∧ y ∈ Subgroup.normalizer (T : Set Y) ∧
        ∃ x ∈ T, y * x * y⁻¹ ≠ x) ∧
      ∃ P : Subgroup Y, IsSylow2In P (tightCore R) ∧ ∀ x ∈ P, y * x = x * y := by
  obtain ⟨m, hm, -, ⟨I⟩⟩ := hAE
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have ht := hd.isUniqueInvolution_core
  have hMx := xMem_of_mem_omegaNbr_core hL hM
  have hKx := xMem_core hL
  obtain ⟨yb, -, hyb3, hybN, ⟨xb, hxb, hxbne⟩, hybK⟩ := exists_linkY_of_aeIdent hL hm I hM
  obtain ⟨hMΩ, -, T, hTR, hTM, hTN⟩ := id hM
  have hTs : IsSylow2In T M := Q3CL.Sec7.isSylow2In_of_mem_RSet_of_le hΩ hTR hMΩ hTM
  have hTt : T ≤ Subgroup.centralizer ({t} : Set Y) := fun z hz =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hTN hz)
  obtain ⟨R₀, hR₀K, hR₀2, hR₀c, hTR₀, -⟩ :=
    CFSG.RankThree.Coprime.exists_sylow_normalized (p := 2) (tightCore R) T hTs.2.1 hTN
  have hR₀ : IsSylow2In R₀ (tightCore R) := by
    obtain ⟨V, hV, -⟩ :=
      IsSylow2In.exists_ge (P := tightCore R) (IsPGroup.of_bot (p := 2)) bot_le
    obtain ⟨k, hk⟩ := hV.2.1.exists_card_eq
    have hVd : 2 ^ k ∣ Nat.card (tightCore R) := hk ▸ Subgroup.card_dvd_of_le hV.1
    have hle : Nat.card V ≤ Nat.card R₀ := by
      rw [hk]
      exact Nat.le_of_dvd Nat.card_pos (hR₀c k hVd)
    exact hV.of_natCard_le hR₀2 hR₀K hle
  have hK₀t : tightCore R ≤ Subgroup.centralizer ({t} : Set Y) := (tightCore_le R).trans hd.cent
  have hD2 : IsPGroup 2 ↥(R₀ ⊔ T) := IsPGroup.to_sup_of_normal_left' hR₀.2.1 hTs.2.1 hTR₀
  have hR₀core : R₀ ≤ coreAt t (tightCore R) := le_coreAt t hR₀.2.1 hR₀.1 (hR₀.1.trans hK₀t)
  have hR₀Y : R₀ ≤ layerY (CoreAssembly.conjClass (tightCore R)) t :=
    hR₀core.trans (coreAt_le_layerY hKx)
  have hTcore : IsSylow2In T (coreAt t M) := (isSylow2In_coreAt_iff hMx).mpr ⟨hTs, hTt⟩
  have hTY : T ≤ layerY (CoreAssembly.conjClass (tightCore R)) t :=
    hTcore.1.trans (coreAt_le_layerY hMx)
  have hDY : R₀ ⊔ T ≤ layerY (CoreAssembly.conjClass (tightCore R)) t := sup_le hR₀Y hTY
  set q := QuotientGroup.mk' (classicalInvolutionOddCore
    ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) with hq
  have hqT : (T.subgroupOf (layerY (CoreAssembly.conjClass (tightCore R)) t)).map q =
      secImg (CoreAssembly.conjClass (tightCore R)) t M := by
    have hS := isSylow2In_map_mk odd_natCard_oddCore_layerY
      (hTcore.subgroupOf (coreAt_le_layerY hMx))
    exact (hS.2.2 _ le_rfl (isPGroup_secImg_of_aeIdent hL I ⟨M, hM, rfl⟩) hS.1).symm
  have hTM' : ∀ z (hz : z ∈ T), q ⟨z, hTY hz⟩ ∈ secImg (CoreAssembly.conjClass (tightCore R)) t M :=
    fun z hz => by
      rw [← hqT]
      exact ⟨⟨z, hTY hz⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
  have hR₀K' : ∀ z (hz : z ∈ R₀),
      q ⟨z, hR₀Y hz⟩ ∈ secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) :=
    fun z hz => ⟨⟨z, hR₀Y hz⟩, Subgroup.mem_subgroupOf.mpr (hR₀core hz), rfl⟩
  have hconj : ∀ d : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t), (d : Y) ∈ R₀ ⊔ T →
      ∃ d' : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t), (d' : Y) ∈ R₀ ⊔ T ∧
        q d' = yb * q d * yb⁻¹ := by
    intro d hd'
    obtain ⟨a, ha, b, hb, hab⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hTR₀ hd'
    have ha' : yb * q ⟨a, hR₀Y ha⟩ * yb⁻¹ = q ⟨a, hR₀Y ha⟩ := by
      rw [hybK _ (hR₀K' a ha), mul_inv_cancel_right]
    have hb' := (Subgroup.mem_normalizer_iff.mp hybN _).mp (hTM' b hb)
    rw [← hqT] at hb'
    obtain ⟨b', hb'T, hb'e⟩ := hb'
    have hdab : d = ⟨a, hR₀Y ha⟩ * ⟨b, hTY hb⟩ := Subtype.ext hab
    refine ⟨⟨a, hR₀Y ha⟩ * b', Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hb'T)), ?_⟩
    calc q (⟨a, hR₀Y ha⟩ * b') = q ⟨a, hR₀Y ha⟩ * (yb * q ⟨b, hTY hb⟩ * yb⁻¹) := by
          rw [map_mul, hb'e]
      _ = (yb * q ⟨a, hR₀Y ha⟩ * yb⁻¹) * (yb * q ⟨b, hTY hb⟩ * yb⁻¹) := by rw [ha']
      _ = yb * (q ⟨a, hR₀Y ha⟩ * q ⟨b, hTY hb⟩) * yb⁻¹ := by group
      _ = yb * q d * yb⁻¹ := by rw [hdab, map_mul]
  obtain ⟨w, hw, hwN⟩ := exists_lift_mem_normalizer hD2 hDY yb hconj
  obtain ⟨e, hwe, b, hwb⟩ := exists_pow_map_eq_of_pow_three q w hw hyb3
  have hyN : ((w ^ e : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y) ∈
      Subgroup.normalizer ((R₀ ⊔ T : Subgroup Y) : Set Y) := by
    rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ hwN e
  have hact : ∀ d : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t), (d : Y) ∈ R₀ ⊔ T →
      ((w ^ e * d * (w ^ e)⁻¹ : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y) ∈
        R₀ ⊔ T ∧ q (w ^ e * d * (w ^ e)⁻¹) = yb * q d * yb⁻¹ := by
    intro d hd'
    refine ⟨?_, by rw [map_mul, map_mul, map_inv, hwe]⟩
    have := (Subgroup.mem_normalizer_iff.mp hyN (d : Y)).mp hd'
    simpa using this
  refine ⟨((w ^ e : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y), ?_,
    layerY_le_centralizer (w ^ e).2, ⟨T, hTs, ?_, ?_⟩, R₀, hR₀, ?_⟩
  · apply isPGroup_zpowers_of_pow_three_pow (a := b)
    rw [← Subgroup.coe_pow, hwb, Subgroup.coe_one]
  · refine mem_normalizer_of_forall_conj_mem fun z hz => ?_
    obtain ⟨hmem, hmk⟩ := hact ⟨z, hTY hz⟩ (Subgroup.mem_sup_right hz)
    have h1 := (Subgroup.mem_normalizer_iff.mp hybN _).mp (hTM' z hz)
    rw [← hqT, ← hmk] at h1
    obtain ⟨z', hz'T, hz'e⟩ := h1
    have h2 := eq_of_mk_eq_of_isPGroup hD2
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hz'T)) hmem hz'e
    have h3 : ((w ^ e * ⟨z, hTY hz⟩ * (w ^ e)⁻¹ :
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y) ∈ T := by
      rw [← h2]
      exact Subgroup.mem_subgroupOf.mp hz'T
    simpa using h3
  · rw [← hqT] at hxb
    obtain ⟨d, hdT, rfl⟩ := hxb
    refine ⟨(d : Y), Subgroup.mem_subgroupOf.mp hdT, fun he => hxbne ?_⟩
    obtain ⟨-, hmk⟩ := hact d (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hdT))
    have h1 : w ^ e * d * (w ^ e)⁻¹ = d := Subtype.ext (by simpa using he)
    rw [h1] at hmk
    calc yb * q d = yb * q d * yb⁻¹ * yb := by group
      _ = q d * yb := by rw [← hmk]
  · intro z hz
    obtain ⟨hmem, hmk⟩ := hact ⟨z, hR₀Y hz⟩ (Subgroup.mem_sup_left hz)
    rw [hybK _ (hR₀K' z hz), mul_inv_cancel_right] at hmk
    have h1 := congrArg Subtype.val
      (eq_of_mk_eq_of_isPGroup hD2 hmem (Subgroup.mem_sup_left hz) hmk)
    have h2 : ((w ^ e : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y) * z *
        ((w ^ e : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y)⁻¹ = z := by
      simpa using h1
    calc ((w ^ e : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y) * z =
        ((w ^ e : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y) * z *
          ((w ^ e : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y)⁻¹ *
          ((w ^ e : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y) := by group
      _ = z * ((w ^ e : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y) := by rw [h2]

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
