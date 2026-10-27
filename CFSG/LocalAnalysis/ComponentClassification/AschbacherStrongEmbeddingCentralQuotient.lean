module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

theorem mem_center_of_isolated {Y : Type} [Group Y] [Finite Y] (hO : CFSG.oddCore Y = ⊥)
    {y : Y} (hy : orderOf y = 2) (hcentral : InvolutionPointCentralSylow y)
    (hiso : ∀ t ∈ involutionPointClass y, Commute y t → t = y) : y ∈ Subgroup.center Y := by
  obtain ⟨S, hyS, hyc⟩ := hcentral
  have hycomm := commute_of_mem_center hyS hyc
  have hyorder : orderOf (⟨y, hyS⟩ : (S : Subgroup Y)) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hy
  have hwc : ∀ g : Y, g⁻¹ * ((⟨y, hyS⟩ : (S : Subgroup Y)) : Y) * g ∈ (S : Subgroup Y) →
      g⁻¹ * ((⟨y, hyS⟩ : (S : Subgroup Y)) : Y) * g = (⟨y, hyS⟩ : (S : Subgroup Y)) := by
    intro g hg
    exact hiso _ (class_conj_mem (distinguished_mem_pointClass y) g) (hycomm _ hg)
  obtain ⟨-, hycenter⟩ :=
    CFSG.Milestones.glauberman_zStar_central_sylow_involution S ⟨y, hyS⟩ hyc hyorder hwc
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  have hc := Subgroup.mem_center_iff.mp hycenter (QuotientGroup.mk g)
  change (QuotientGroup.mk (g * y) : Y ⧸ CFSG.oddCore Y) = QuotientGroup.mk (y * g) at hc
  rw [QuotientGroup.eq, hO, Subgroup.mem_bot] at hc
  have h := congrArg (fun w => (g * y) * w) hc
  simpa only [mul_inv_cancel_left, mul_one] using h.symm

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem mem_zpowers_of_orderOf_two {u w : X} (hu : orderOf u = 2) :
    w ∈ Subgroup.zpowers u ↔ w = 1 ∨ w = u := by
  constructor
  · intro hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have huu : u * u = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hu).1
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, zpow_two, huu, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, huu, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem oddCore_central_quotient_eq_bot (hO : CFSG.oddCore X = ⊥) (Z : Subgroup X) [Z.Normal]
    (hZc : Z ≤ Subgroup.center X) (hZ2 : Nat.card Z = 2) : CFSG.oddCore (X ⧸ Z) = ⊥ := by
  let q := QuotientGroup.mk' Z
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective Z
  let Ob := CFSG.oddCore (X ⧸ Z)
  let P : Subgroup X := Ob.comap q
  have hZP : Z ≤ P := by
    intro w hw
    change q w ∈ Ob
    have h1 : q w = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hw
    rw [h1]
    exact Ob.one_mem
  have hPnormal : P.Normal := Subgroup.Normal.comap inferInstance q
  have hrel : Z.relIndex P = Nat.card Ob := by
    have h := Subgroup.relIndex_ker P q
    rw [QuotientGroup.ker_mk', Subgroup.map_comap_eq_self_of_surjective hq] at h
    exact h
  have hObodd : Odd (Nat.card Ob) := CFSG.ComponentClassification.OddCore.odd_card (X ⧸ Z)
  let ZP : Subgroup P := Z.subgroupOf P
  have hZPnormal : ZP.Normal := Subgroup.normal_subgroupOf
  have hZPcard : Nat.card ZP = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ2]
  have hcop : Nat.Coprime (Nat.card ZP) ZP.index := by
    rw [hZPcard]
    change Nat.Coprime 2 (Z.relIndex P)
    rw [hrel]
    exact Nat.coprime_two_left.mpr hObodd
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hKcard : Nat.card K = Nat.card Ob := by
    have h := hK.card_mul_card
    rw [hZPcard] at h
    have hP := ZP.card_mul_index
    rw [hZPcard] at hP
    have : ZP.index = Nat.card Ob := hrel
    omega
  have hKnormal : K.Normal := by
    constructor
    intro k hk p
    obtain ⟨a, ha, b, hb, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := ZP) (t := K)).mp
      (hK.sup_eq_top ▸ Subgroup.mem_top p)
    have hacentral : ∀ w : P, a * w = w * a := by
      intro w
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp (hZc ha)) (w : X) |>.symm
    have h := K.mul_mem (K.mul_mem hb hk) (K.inv_mem hb)
    have heq : a * b * k * (a * b)⁻¹ = b * k * b⁻¹ := by
      calc a * b * k * (a * b)⁻¹ = a * (b * k * b⁻¹) * a⁻¹ := by group
        _ = (b * k * b⁻¹) * a * a⁻¹ := by rw [hacentral]
        _ = b * k * b⁻¹ := by group
    rw [heq]
    exact h
  have hKodd : Odd (Nat.card K) := hKcard ▸ hObodd
  have hKbot : K = ⊥ := by
    have hle : K ≤ CFSG.oddCore P := le_sSup ⟨hKnormal, hKodd⟩
    rw [oddCore_eq_bot_of_normal hO P, le_bot_iff] at hle
    exact hle
  rw [hKbot, Subgroup.card_bot] at hKcard
  exact Subgroup.eq_bot_of_card_eq Ob hKcard.symm

omit [Finite X] in
theorem orderOf_central_quotient {M : Subgroup X} {x u : X} (hx : orderOf x = 2)
    (huniq : ∀ g : X, x ∈ rightConjugate M g ↔ g ∈ M) (hM : M ≠ ⊤)
    (hu : u ∈ Subgroup.center X) (hu2 : orderOf u = 2) (Z : Subgroup X) [Z.Normal]
    (hZ : Z = Subgroup.zpowers u) : orderOf (QuotientGroup.mk' Z x) = 2 := by
  have hxu : x ≠ u := by
    rintro rfl
    apply hM
    refine eq_top_iff.mpr fun g _ => centralizer_le_of_unique huniq ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hu g)
  have hx1 : x ≠ 1 := (orderOf_eq_prime_iff.mp hx).2
  apply orderOf_eq_prime
  · rw [← map_pow, (orderOf_eq_prime_iff.mp hx).1, map_one]
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZ,
      mem_zpowers_of_orderOf_two hu2] at h
    rcases h with h | h
    · exact hx1 h
    · exact hxu h

theorem centralProduct_central_quotient {M : Subgroup X} {x u : X} (hx : orderOf x = 2)
    (huniq : ∀ g : X, x ∈ rightConjugate M g ↔ g ∈ M) (hM : M ≠ ⊤)
    (h2 : CentralProductCentralizer M x) (hu : u ∈ Subgroup.center X) (hu2 : orderOf u = 2)
    (Z : Subgroup X) [Z.Normal] (hZ : Z = Subgroup.zpowers u) :
    CentralProductCentralizer (M.map (QuotientGroup.mk' Z)) (QuotientGroup.mk' Z x) := by
  set q := QuotientGroup.mk' Z with hqdef
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective Z
  have h1 := productUniqueContainment_of_centralProductCentralizer hx huniq h2
  obtain ⟨⟨S, hxS, hxc⟩, hcent⟩ := h2
  have huM : u ∈ M := centralizer_le_of_unique huniq
    (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hu x).symm)
  have hxM := mem_of_unique huniq
  have hxx : x * x = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hx).1
  have huc : ∀ g : X, g * u = u * g := fun g => Subgroup.mem_center_iff.mp hu g
  have hmemZ : ∀ w : X, w ∈ Z ↔ w = 1 ∨ w = u := by
    intro w
    rw [hZ, mem_zpowers_of_orderOf_two hu2]
  refine ⟨?_, ?_⟩
  · obtain ⟨T, -, hxT, hcomm⟩ := CFSG.ProperTwoGeneratedCore.central_sylow_two_image q hq S hxS
      (commute_of_mem_center hxS hxc)
    exact ⟨T, hxT, Subgroup.mem_center_iff.mpr fun t => Subtype.ext (hcomm t t.property).eq.symm⟩
  intro tb htb hxtb hne
  rw [class_map q hq] at htb
  obtain ⟨t, ht, rfl⟩ := htb
  have hc : q ⁅x, t⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hxtb.eq]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmemZ] at hc
  rcases hc with hc1 | hcu
  · have hxt : Commute x t := commutatorElement_eq_one_iff_mul_comm.mp hc1
    have hne' : t ≠ x := fun h => hne (by rw [h])
    have hC := hcent t ht hxt hne'
    have htx : t ∈ M := hC (Subgroup.mem_centralizer_singleton_iff.mpr
      (hxt.symm.mul_right (Commute.refl t)).eq)
    intro gb hgb
    obtain ⟨g, rfl⟩ := hq gb
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hgb
    have hd : q (g * (x * t) * g⁻¹) = q (x * t) := by
      rw [map_mul, map_mul, map_inv, map_mul, hcomm, mul_inv_cancel_right]
    obtain ⟨w, hw, hwd⟩ := (QuotientGroup.mk'_eq_mk' Z).mp hd.symm
    have hgM : g ∈ M := by
      rcases (hmemZ w).mp hw with rfl | rfl
      · apply hC
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        rw [mul_one] at hwd
        calc g * (x * t) = g * (x * t) * g⁻¹ * g := by group
          _ = x * t * g := by rw [← hwd]
      · have hmem : g⁻¹⁻¹ * (x * t) * g⁻¹ ∈ M := by
          rw [inv_inv, ← hwd]
          exact M.mul_mem (M.mul_mem hxM htx) huM
        exact M.inv_mem_iff.mp ((h1 t ht hxt hne' g⁻¹).mp hmem)
    exact ⟨g, hgM, rfl⟩
  · exfalso
    have hxt' : x * t = u * (t * x) := by
      calc x * t = ⁅x, t⁆ * (t * x) := by rw [commutatorElement_def]; group
        _ = u * (t * x) := by rw [hcu]
    have hxu : t⁻¹ * x * t = u * x := by
      calc t⁻¹ * x * t = t⁻¹ * (x * t) := mul_assoc _ _ _
        _ = t⁻¹ * u * (t * x) := by rw [hxt', mul_assoc]
        _ = u * x := by rw [huc t⁻¹, mul_assoc, inv_mul_cancel_left]
    have hux : u * x ∈ involutionPointClass x := hxu ▸ class_conj_mem
      (distinguished_mem_pointClass x) t
    have hcomm : Commute x (u * x) := by
      change x * (u * x) = u * x * x
      rw [← mul_assoc, huc x]
    have hne'' : u * x ≠ x := by
      intro h
      apply (orderOf_eq_prime_iff.mp hu2).2
      have h' := congrArg (· * x) h
      simpa only [mul_assoc, hxx, mul_one] using h'
    have hC := hcent (u * x) hux hcomm hne''
    apply hM
    refine eq_top_iff.mpr fun g _ => hC ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxux : x * (u * x) = u := by rw [← mul_assoc, huc x, mul_assoc, hxx, mul_one]
    rw [hxux]
    exact huc g

end CFSG.ComponentClassification.AschbacherStrongEmbedding
