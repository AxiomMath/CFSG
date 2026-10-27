module

public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersParabolic
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeSylowCenter
public import Certificates.Certificate18000

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag
open scoped Pointwise
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom pairedTorusHom_apply f4i torusPair
  torusPair_apply torusPair_conj_pinnedX torusWeight torusWeight_apply torusExp0 torusExp1)

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem isRoot_centralRoot44
    : IsRoot F4.tag centralRoot44 ∧ 0 < height centralRoot44 :=
  CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog.isRoot_largeReeAlpha44

theorem isRoot_centralRoot47
    : IsRoot F4.tag centralRoot47 ∧ 0 < height centralRoot47 :=
  CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog.isRoot_largeReeAlpha47

variable (K a) in
@[expose] def centralZ
    (c : K) : ModGL F4.tag K :=
  pinnedX F4.tag K centralRoot44 c * pinnedX F4.tag K centralRoot47 (c ^ (2 * 2 ^ a))

omit [Finite K] [CharP K F4.prime] in
theorem centralZ_zero
    : centralZ K a 0 = 1 := by
  rw [centralZ, zero_pow (by positivity), pinnedX_zero, pinnedX_zero, one_mul]

omit [Finite K] [CharP K F4.prime] in
theorem centralZ_injective
    : Function.Injective (centralZ K a) := by
  intro c d h
  have hL := pinnedX_list_prod_injective (R := K) [centralRoot44, centralRoot47] (by decide)
    (by
      intro α hα
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
      rcases hα with rfl | rfl
      · exact isRoot_centralRoot44
      · exact isRoot_centralRoot47)
    (fun α => if α = centralRoot44 then c else c ^ (2 * 2 ^ a))
    (fun α => if α = centralRoot44 then d else d ^ (2 * 2 ^ a))
    (by
      have hne : centralRoot47 ≠ centralRoot44 := by decide
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hne,
        ↓reduceIte]
      exact h)
  simpa using hL centralRoot44 (by simp)

theorem coe_center_eq_range_centralZ
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ((Subgroup.center (F4.reeFixedPosUnipotent K a)).map
        (F4.reeFixedPosUnipotent K a).subtype : Set (ModGL F4.tag K)) =
      Set.range (centralZ K a) :=
  (CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_Sylow_center a ha K hK).2.1

theorem centralZ_mem
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    centralZ K a c ∈ F4.reeFixedPosUnipotent K a := by
  have h : centralZ K a c ∈ ((Subgroup.center (F4.reeFixedPosUnipotent K a)).map
      (F4.reeFixedPosUnipotent K a).subtype : Set (ModGL F4.tag K)) := by
    rw [coe_center_eq_range_centralZ ha hK]
    exact ⟨c, rfl⟩
  obtain ⟨w, -, hw⟩ := h
  rw [← hw]
  exact w.2

theorem commute_centralZ
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ F4.reeFixedPosUnipotent K a) (c : K) : u * centralZ K a c = centralZ K a c * u := by
  have h : centralZ K a c ∈ ((Subgroup.center (F4.reeFixedPosUnipotent K a)).map
      (F4.reeFixedPosUnipotent K a).subtype : Set (ModGL F4.tag K)) := by
    rw [coe_center_eq_range_centralZ ha hK]
    exact ⟨c, rfl⟩
  obtain ⟨w, hw, hwz⟩ := h
  rw [← hwz]
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨u, hu⟩)

omit [CharP K F4.prime] in
theorem torusPair_conj_centralZ
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : Kˣ) (c : K) :
    torusPair a (u, v) * centralZ K a c * (torusPair a (u, v))⁻¹ =
      centralZ K a ((u : K) ^ 2 ^ a * c) := by
  have e : ∀ A X Y : ModGL F4.tag K, A * (X * Y) * A⁻¹ = (A * X * A⁻¹) * (A * Y * A⁻¹) :=
    fun A X Y => by group
  rw [centralZ, e, torusPair_conj_pinnedX _ _ isRoot_centralRoot44.1,
    torusPair_conj_pinnedX _ _ isRoot_centralRoot47.1, centralZ]
  have hθ : ((2 : ℤ) ^ a) = ((2 ^ a : ℕ) : ℤ) := by push_cast; ring
  have h44 : torusWeight a centralRoot44 (u, v) = u ^ 2 ^ a := by
    rw [torusWeight_apply]
    have e0 : torusExp0 (2 ^ a) centralRoot44 = 2 ^ a := by
      simp only [torusExp0]
      rw [show F4.cartanPair (f4i 0) centralRoot44 = 0 by decide,
        show F4.cartanPair (f4i 3) centralRoot44 = 1 by decide]
      ring
    have e1 : torusExp1 (2 ^ a) centralRoot44 = 0 := by
      simp only [torusExp1]
      rw [show F4.cartanPair (f4i 1) centralRoot44 = 0 by decide,
        show F4.cartanPair (f4i 2) centralRoot44 = 0 by decide]
      ring
    rw [e0, e1, zpow_zero, mul_one, hθ, zpow_natCast]
  have h47 : torusWeight a centralRoot47 (u, v) = u := by
    rw [torusWeight_apply]
    have e0 : torusExp0 (2 ^ a) centralRoot47 = 1 := by
      simp only [torusExp0]
      rw [show F4.cartanPair (f4i 0) centralRoot47 = 1 by decide,
        show F4.cartanPair (f4i 3) centralRoot47 = 0 by decide]
      ring
    have e1 : torusExp1 (2 ^ a) centralRoot47 = 0 := by
      simp only [torusExp1]
      rw [show F4.cartanPair (f4i 1) centralRoot47 = 0 by decide,
        show F4.cartanPair (f4i 2) centralRoot47 = 0 by decide]
      ring
    rw [e0, e1, zpow_zero, mul_one, zpow_one]
  have hq : ((u : K)) ^ (2 ^ a * (2 * 2 ^ a)) = u := by
    have h1 : 2 ^ a * (2 * 2 ^ a) = Nat.card K := by rw [hK]; ring
    rw [h1]
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, FiniteField.pow_card]
  rw [h44, h47, Units.val_pow_eq_pow_val, mul_pow, ← pow_mul, hq]

omit [Finite K] [CharP K F4.prime] in
theorem rankOneTorusPair_left (u : Kˣ) :
    torusPair a (u, 1) = pairedTorusHom a (f4i 0) (f4i 3) u := by
  rw [torusPair_apply, pairedTorusHom_apply, one_pow, torusElt_one, torusElt_one, one_mul,
    mul_one]

omit [Finite K] [CharP K F4.prime] in
theorem rankOneTorusPair_right
    (v : Kˣ) :
    torusPair a (1, v) = pairedTorusHom a (f4i 1) (f4i 2) v := by
  rw [torusPair_apply, pairedTorusHom_apply, one_pow, torusElt_one, torusElt_one, one_mul,
    one_mul]

omit [Finite K] [CharP K F4.prime] in
theorem rankOneTorusPair_eq_mul
    (u v : Kˣ) :
    torusPair a (u, v) = pairedTorusHom a (f4i 0) (f4i 3) u * pairedTorusHom a (f4i 1) (f4i 2) v :=
  by rw [torusPair_apply, pairedTorusHom_apply, pairedTorusHom_apply]

theorem rankOne_exists_torusPair_eq
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {h : ModGL F4.tag K}
    (hh : h ∈ F4.reeFixedTorus K a) : ∃ u v : Kˣ, torusPair a (u, v) = h := by
  obtain ⟨hT, hΓ⟩ := Subgroup.mem_inf.1 hh
  have hH := mem_nativeData_H_of_mem_torusGroup (t := F4) hT
  have hF : (⟨h, torusGroup_le_adjointGroup F4 K hT⟩ : adjointGroup F4.tag K) ∈
      reeFixed F4 K a := by
    rw [← map_reeFixed_eq_reeGamma] at hΓ
    obtain ⟨x, hx, hxh⟩ := hΓ
    have e : x = ⟨h, torusGroup_le_adjointGroup F4 K hT⟩ := Subtype.ext hxh
    rw [← e]
    exact hx
  obtain ⟨u, v, huv⟩ := CFSG.SectionRank.LargeRee.exists_eq_reeTorus_mul hK hH hF
  refine ⟨u, v, ?_⟩
  rw [LargeReeCover.torusPair_eq_reeTorus]
  exact (congrArg Subtype.val huv).symm

theorem exists_conj_centralZ
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {b : ModGL F4.tag K} (hb : b ∈ F4.reeFixedBorel K a) (c : K) :
    ∃ u : Kˣ, b * centralZ K a c * b⁻¹ = centralZ K a ((u : K) ^ 2 ^ a * c) := by
  have hb' : b ∈ (F4.reeFixedBorel K a : Set (ModGL F4.tag K)) := hb
  rw [reeFixedBorel_eq_mul] at hb'
  obtain ⟨h, hh, x, hx, rfl⟩ := hb'
  obtain ⟨u, v, rfl⟩ := rankOne_exists_torusPair_eq hK hh
  refine ⟨u, ?_⟩
  have hxz := commute_centralZ ha hK hx c
  calc torusPair a (u, v) * x * centralZ K a c * (torusPair a (u, v) * x)⁻¹ =
      torusPair a (u, v) * (x * centralZ K a c * x⁻¹) * (torusPair a (u, v))⁻¹ := by group
    _ = torusPair a (u, v) * centralZ K a c * (torusPair a (u, v))⁻¹ := by
        rw [hxz, mul_inv_cancel_right]
    _ = _ := torusPair_conj_centralZ hK u v c

omit [Finite K] [CharP K F4.prime] in
theorem fixedOrbitElement_one_smul_centralRoot44 :
    F4.fixedOrbitElement ⟨1, by decide⟩ • centralRoot44 = centralRoot44 := by
  rw [fixedOrbitElement_smul]
  exact Certificates.certificate18000.1

omit [Finite K] [CharP K F4.prime] in
theorem fixedOrbitElement_one_smul_centralRoot47 :
    F4.fixedOrbitElement ⟨1, by decide⟩ • centralRoot47 = centralRoot47 := by
  rw [fixedOrbitElement_smul]
  exact Certificates.certificate18000.2.1

omit [Finite K] in
theorem canonicalRep_conj_centralZ
    (c : K) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) *
        centralZ K a c *
          (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩))⁻¹ =
      centralZ K a c := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e : ∀ A X Y : ModGL F4.tag K, A * (X * Y) * A⁻¹ = (A * X * A⁻¹) * (A * Y * A⁻¹) :=
    fun A X Y => by group
  rw [centralZ, e, canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ isRoot_centralRoot44.1,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ isRoot_centralRoot47.1,
    fixedOrbitElement_one_smul_centralRoot44, fixedOrbitElement_one_smul_centralRoot47]

theorem rankOneGroupTwo_le_centralizer
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (c : K) : rankOneGroupTwo K a ≤ Subgroup.centralizer {centralZ K a c} := by
  rw [rankOneGroupTwo, Subgroup.closure_le]
  have hcomm : ∀ {g x : ModGL F4.tag K}, g * x * g⁻¹ = x → g * x = x * g := fun {g x} h => by
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h]
  rintro g ((hg | ⟨v, rfl⟩) | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  · exact (commute_centralZ ha hK (reeFixedOrbitUnipotent_le _ hg) c)
  · have h := torusPair_conj_centralZ hK 1 v c
    rw [Units.val_one, one_pow, one_mul, rankOneTorusPair_right] at h
    exact hcomm h
  · exact hcomm (canonicalRep_conj_centralZ (a := a) c)

theorem complement_le_centralizer
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ≤
      Subgroup.centralizer {centralZ K a c} := fun _ hv =>
  Subgroup.mem_centralizer_singleton_iff.2
    (commute_centralZ ha hK (reeFixedOrbitComplementUnipotent_le _ hv) c)

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem fixedRelElt_smul_eq_centralWeylImage
    (k : Fin F4.fixedWeylOrder) (α : Fin F4.tag.rank → ℤ) :
    F4.fixedRelElt k • α = centralWeylImage k α := by
  rw [fixedRelElt, list_prod_map_fixedOrbitElement, CFSG.LieType.Ree.wordProd_smul]

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem centralZ_weyl_check : ∀ k : Fin F4.fixedWeylOrder,
    F4.fixedRelWord k = [] ∨ F4.fixedRelWord k = [⟨1, by decide⟩] ∨
      height (centralWeylImage k centralRoot44) < 0 ∨
      height (centralWeylImage k centralRoot47) < 0 ∨
      (centralWeylImage k centralRoot44 ≠ centralRoot44 ∧
        centralWeylImage k centralRoot44 ≠ centralRoot47 ∧
        centralWeylImage k centralRoot47 ≠ centralRoot44 ∧
        centralWeylImage k centralRoot47 ≠ centralRoot47) :=
  Certificates.certificate18000.2.2.1

omit [Finite K] [CharP K F4.prime] in
theorem centralZ_pinnedX_ne_one
    {α : Fin F4.tag.rank → ℤ} {c : K} (hc : c ≠ 0) :
    pinnedX F4.tag K α c ≠ 1 := fun h =>
  hc (pinnedX_injective F4.tag K α (h.trans (pinnedX_zero F4.tag K α).symm))

omit [Finite K] [CharP K F4.prime] in
theorem not_neg_of_mul_eq_centralZ
    {β γ : Fin F4.tag.rank → ℤ} (hβ : IsRoot F4.tag β)
    (hγ : IsRoot F4.tag γ) {c d c' : K} (hc : c ≠ 0) (hd : d ≠ 0) (hc' : c' ≠ 0)
    (h : pinnedX F4.tag K β c * pinnedX F4.tag K γ d = centralZ K a c') :
    0 < height β ∧ 0 < height γ := by
  have hz1 : centralZ K a c' ≠ 1 := fun h1 =>
    hc' (centralZ_injective (h1.trans centralZ_zero.symm))
  have hzU : centralZ K a c' ∈ posUnipotent F4.tag K :=
    mul_mem (pinnedX_mem_rootSpan (S := {α | IsRoot F4.tag α ∧ 0 < height α})
      isRoot_centralRoot44 _) (pinnedX_mem_rootSpan (S := {α | IsRoot F4.tag α ∧ 0 < height α})
      isRoot_centralRoot47 _)
  have hmemU : ∀ {δ : Fin F4.tag.rank → ℤ} (e : K), IsRoot F4.tag δ → 0 < height δ →
      pinnedX F4.tag K δ e ∈ posUnipotent F4.tag K := fun e hδ hp =>
    pinnedX_mem_rootSpan (S := {α | IsRoot F4.tag α ∧ 0 < height α}) ⟨hδ, hp⟩ _
  have hmemV : ∀ {δ : Fin F4.tag.rank → ℤ} (e : K), IsRoot F4.tag δ → height δ < 0 →
      pinnedX F4.tag K δ e ∈ negUnipotent F4.tag K := fun e hδ hp =>
    pinnedX_mem_rootSpan (S := {α | IsRoot F4.tag α ∧ height α < 0}) ⟨hδ, hp⟩ _
  have hUV := CFSG.Blueprint.Chevalley.posUnipotent_inf_negUnipotent F4.tag K
  have hβ0 := hβ.height_ne_zero
  have hγ0 := hγ.height_ne_zero
  by_contra hneg
  rcases not_and_or.1 hneg with hβn | hγn
  · have hβn : height β < 0 := by omega
    rcases lt_or_gt_of_ne hγ0 with hγn | hγp
    ·
      have hzV : centralZ K a c' ∈ negUnipotent F4.tag K :=
        h ▸ mul_mem (hmemV c hβ hβn) (hmemV d hγ hγn)
      have := Subgroup.mem_inf.2 ⟨hzU, hzV⟩
      rw [hUV, Subgroup.mem_bot] at this
      exact hz1 this
    ·
      have e : pinnedX F4.tag K β c = centralZ K a c' * (pinnedX F4.tag K γ d)⁻¹ := by
        rw [← h, mul_inv_cancel_right]
      have hU : pinnedX F4.tag K β c ∈ posUnipotent F4.tag K :=
        e ▸ mul_mem hzU (inv_mem (hmemU d hγ hγp))
      have := Subgroup.mem_inf.2 ⟨hU, hmemV c hβ hβn⟩
      rw [hUV, Subgroup.mem_bot] at this
      exact centralZ_pinnedX_ne_one hc this
  · have hγn : height γ < 0 := by omega
    rcases lt_or_gt_of_ne hβ0 with hβn | hβp
    · have hzV : centralZ K a c' ∈ negUnipotent F4.tag K :=
        h ▸ mul_mem (hmemV c hβ hβn) (hmemV d hγ hγn)
      have := Subgroup.mem_inf.2 ⟨hzU, hzV⟩
      rw [hUV, Subgroup.mem_bot] at this
      exact hz1 this
    · have e : pinnedX F4.tag K γ d = (pinnedX F4.tag K β c)⁻¹ * centralZ K a c' := by
        rw [← h, inv_mul_cancel_left]
      have hU : pinnedX F4.tag K γ d ∈ posUnipotent F4.tag K :=
        e ▸ mul_mem (inv_mem (hmemU c hβ hβp)) hzU
      have := Subgroup.mem_inf.2 ⟨hU, hmemV d hγ hγn⟩
      rw [hUV, Subgroup.mem_bot] at this
      exact centralZ_pinnedX_ne_one hd this

omit [Finite K] [CharP K F4.prime] in
theorem eq_zero_of_mul_eq_centralZ
    {β γ : Fin F4.tag.rank → ℤ}
    (hβ : IsRoot F4.tag β ∧ 0 < height β) (hγ : IsRoot F4.tag γ ∧ 0 < height γ) (hβγ : β ≠ γ)
    (h1 : β ≠ centralRoot44) (h2 : β ≠ centralRoot47) (h3 : γ ≠ centralRoot44)
    (h4 : γ ≠ centralRoot47) {c d c' : K}
    (h : pinnedX F4.tag K β c * pinnedX F4.tag K γ d = centralZ K a c') : c = 0 := by
  have h47 : centralRoot47 ≠ centralRoot44 := by decide
  have hL := pinnedX_list_prod_injective (R := K) [β, γ, centralRoot44, centralRoot47]
    (by simp [hβγ, h1, h2, h3, h4, h47.symm])
    (by
      intro α hα
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
      rcases hα with rfl | rfl | rfl | rfl
      · exact hβ
      · exact hγ
      · exact isRoot_centralRoot44
      · exact isRoot_centralRoot47)
    (fun α => if α = β then c else if α = γ then d else 0)
    (fun α => if α = centralRoot44 then c' else if α = centralRoot47 then c' ^ (2 * 2 ^ a) else 0)
    (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        ↓reduceIte, hβγ.symm, h1, h2, h3, h4, h1.symm, h2.symm, h3.symm, h4.symm, h47,
        pinnedX_zero, one_mul]
      rw [h]
      rfl)
  simpa [h1, h2] using hL β (by simp)

variable (K a) in
abbrev centralWeylRep
    (k : Fin F4.fixedWeylOrder) : ModGL F4.tag K :=
  canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k)

omit [Finite K] in
theorem weylRep_conj_centralZ
    (k : Fin F4.fixedWeylOrder) (c : K) :
    centralWeylRep K k * centralZ K a c * (centralWeylRep K k)⁻¹ =
      pinnedX F4.tag K (centralWeylImage k centralRoot44) c *
        pinnedX F4.tag K (centralWeylImage k centralRoot47) (c ^ (2 * 2 ^ a)) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e : ∀ A X Y : ModGL F4.tag K, A * (X * Y) * A⁻¹ = (A * X * A⁻¹) * (A * Y * A⁻¹) :=
    fun A X Y => by group
  rw [centralZ, e, canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ isRoot_centralRoot44.1,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ isRoot_centralRoot47.1,
    fixedRelElt_smul_eq_centralWeylImage,
    fixedRelElt_smul_eq_centralWeylImage]

theorem reeGamma_inf_centralizer_le_reeLocalParabolic
    (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ Subgroup.centralizer {centralZ K a 1} ≤
      F4.reeLocalParabolic K a ⟨1, by decide⟩ := by
  intro g hg
  obtain ⟨hgΓ, hgc⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hgc
  have hg' : g ∈ (F4.reeGamma K a : Set (ModGL F4.tag K)) := hgΓ
  rw [reeGamma_eq_iUnion_reeFixedBruhatCell] at hg'
  obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨k, rfl⟩ := exists_fixedRelElt_eq hw
  have hgw' := hgw
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hgw
  obtain ⟨u, hu⟩ := exists_conj_centralZ ha hK hb' 1
  obtain ⟨u', hu'⟩ := exists_conj_centralZ ha hK (inv_mem hb) 1
  have hne : ∀ v : Kˣ, (v : K) ^ 2 ^ a * 1 ≠ 0 := fun v => by
    rw [mul_one]
    exact pow_ne_zero _ v.ne_zero
  have key : centralWeylRep K k * centralZ K a ((u : K) ^ 2 ^ a * 1) * (centralWeylRep K k)⁻¹ =
      centralZ K a ((u' : K) ^ 2 ^ a * 1) := by
    rw [← hu, ← hu', inv_inv]
    have hc : (b * centralWeylRep K k * b') * centralZ K a 1 * (b * centralWeylRep K k * b')⁻¹ =
        centralZ K a 1 := by rw [hgc, mul_inv_cancel_right]
    calc centralWeylRep K k * (b' * centralZ K a 1 * b'⁻¹) * (centralWeylRep K k)⁻¹ =
        b⁻¹ * ((b * centralWeylRep K k * b') * centralZ K a 1 *
          (b * centralWeylRep K k * b')⁻¹) * b := by
          group
      _ = b⁻¹ * centralZ K a 1 * b := by rw [hc]
  rw [weylRep_conj_centralZ] at key
  have hroot44 : IsRoot F4.tag (centralWeylImage k centralRoot44) := by
    rw [← fixedRelElt_smul_eq_centralWeylImage]
    exact CFSG.LieType.Chevalley.IsRoot.smul isRoot_centralRoot44.1 _
  have hroot47 : IsRoot F4.tag (centralWeylImage k centralRoot47) := by
    rw [← fixedRelElt_smul_eq_centralWeylImage]
    exact CFSG.LieType.Chevalley.IsRoot.smul isRoot_centralRoot47.1 _
  have hpos := not_neg_of_mul_eq_centralZ hroot44 hroot47 (hne u)
    (pow_ne_zero _ (hne u)) (hne u') key
  rcases centralZ_weyl_check k with h1 | h1 | h1 | h1 | ⟨h1, h2, h3, h4⟩
  ·
    have hw1 : F4.fixedRelElt k = 1 := by rw [fixedRelElt, h1, List.map_nil, List.prod_nil]
    have hb1 : centralWeylRep K k = 1 := by rw [centralWeylRep, hw1, canonicalRep_one]
    have hgB : b * centralWeylRep K k * b' ∈ F4.reeFixedBorel K a := by
      rw [hb1, mul_one]
      exact mul_mem hb hb'
    exact (reeFixedBorel_le_reeGamma_inf_parabolicSubgroup (t := F4) ⟨1, by decide⟩) hgB
  ·
    have hw2 : F4.fixedRelElt k = F4.fixedOrbitElement ⟨1, by decide⟩ := by
      rw [fixedRelElt, h1, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have hmem : b * centralWeylRep K k * b' ∈
        ((F4.reeGamma K a ⊓ parabolicSubgroup F4.tag K (F4.fixedOrbitSet ⟨1, by decide⟩) :
          Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) := by
      rw [coe_reeGamma_inf_parabolicSubgroup]
      right
      rw [← hw2]
      exact hgw'
    exact hmem
  · exact absurd hpos.1 (by omega)
  · exact absurd hpos.2 (by omega)
  · have hβγ : centralWeylImage k centralRoot44 ≠ centralWeylImage k centralRoot47 := by
      rw [← fixedRelElt_smul_eq_centralWeylImage, ← fixedRelElt_smul_eq_centralWeylImage]
      intro h
      exact absurd (smul_left_cancel _ h) (by decide)
    exact absurd (eq_zero_of_mul_eq_centralZ ⟨hroot44, hpos.1⟩ ⟨hroot47, hpos.2⟩ hβγ h1 h2 h3 h4
      key) (hne u)

omit [Finite K] [CharP K F4.prime] in
theorem rankOne_torusPair_mem_torusGroup
    (u v : Kˣ) : torusPair a (u, v) ∈ torusGroup F4.tag K := by
  rw [torusPair_apply]
  exact mul_mem (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
    (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))

theorem rankOne_torusPair_mem_reeFixedTorus
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : Kˣ) :
    torusPair a (u, v) ∈ F4.reeFixedTorus K a :=
  Subgroup.mem_inf.2 ⟨rankOne_torusPair_mem_torusGroup u v,
    LargeReeCover.torusPair_mem_reeGamma a hK _⟩

theorem rankOneTorusOne_le
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneTorusOne K a ≤ F4.reeFixedTorus K a := by
  rintro _ ⟨u, rfl⟩
  rw [← rankOneTorusPair_left]
  exact rankOne_torusPair_mem_reeFixedTorus hK u 1

theorem rankOneTorusTwo_le
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneTorusTwo K a ≤ F4.reeFixedTorus K a := by
  rintro _ ⟨v, rfl⟩
  rw [← rankOneTorusPair_right]
  exact rankOne_torusPair_mem_reeFixedTorus hK 1 v

theorem canonicalRep_conj_torusOne
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (u : Kˣ) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) *
        pairedTorusHom a (f4i 0) (f4i 3) u *
          (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩))⁻¹ =
      pairedTorusHom a (f4i 0) (f4i 3) u *
        pairedTorusHom a (f4i 1) (f4i 2) (u ^ (2 + 2 * ((2 ^ a : ℕ) : ℤ))) := by
  have h := congrArg Subtype.val (CFSG.SectionRank.LargeRee.torus_reflections (a := a) hK u).2.2.2
  have hn : (nrep F4.tag K (F4.blockElt (CFSG.SectionRank.LargeRee.fi 1)) : ModGL F4.tag K) =
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) := by
    change canonicalRep (coxeterSystem F4.tag) K _ = _
    rw [blockElt_eq]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hn] at h
  rw [← rankOneTorusPair_left, ← rankOneTorusPair_right, LargeReeCover.torusPair_eq_reeTorus,
    LargeReeCover.torusPair_eq_reeTorus]
  simp only [CFSG.SectionRank.LargeRee.reeTorus_one, mul_one, one_mul]
  exact h

omit [Finite K] [CharP K F4.prime] in
theorem rankOne_commute_pairedTorusHom
    (j k j' k' : Fin 4) (u v : Kˣ) :
    Commute (pairedTorusHom a (f4i j) (f4i k) u) (pairedTorusHom a (f4i j') (f4i k') v) := by
  rw [pairedTorusHom_apply, pairedTorusHom_apply]
  exact ((LargeReeCover.torusElt_commute _ _ _ _).mul_left
    (LargeReeCover.torusElt_commute _ _ _ _)).mul_right
      ((LargeReeCover.torusElt_commute _ _ _ _).mul_left (LargeReeCover.torusElt_commute _ _ _ _))

theorem rankOne_canonicalRep_two_mem_reeGamma :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) ∈
      F4.reeGamma K a :=
  (canonicalRep_mem_reeFixedMonomial F4 K a (fixedOrbitElement_mem _)).2

theorem rankOneGroupTwo_le_reeGamma
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupTwo K a ≤ F4.reeGamma K a := by
  rw [rankOneGroupTwo, Subgroup.closure_le]
  rintro g ((hg | hg) | rfl)
  · exact (Subgroup.mem_inf.1 hg).2
  · exact (Subgroup.mem_inf.1 (rankOneTorusTwo_le hK hg)).2
  · exact rankOne_canonicalRep_two_mem_reeGamma

theorem rankOneGroupTwo_le_normalizer_complement
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupTwo K a ≤ Subgroup.normalizer
      (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ : Set (ModGL F4.tag K)) := by
  rw [rankOneGroupTwo, Subgroup.closure_le]
  rintro g ((hg | hg) | rfl)
  · exact reeFixedPosUnipotent_le_normalizer _ (reeFixedOrbitUnipotent_le _ hg)
  · exact reeFixedTorus_le_normalizer_complement _ (rankOneTorusTwo_le hK hg)
  · exact mem_normalizer_of_map_eq (map_conj_reeFixedOrbitComplementUnipotent _)

theorem centralZ_conj_eq_of_conj_eq {G : Type*} [Group G] {n T T' : G} (hr : n * T * n⁻¹ = T * T')
    (hc : T * T' = T' * T) : T * n * T⁻¹ = T'⁻¹ * n := by
  calc T * n * T⁻¹ = T * (n * T * n⁻¹)⁻¹ * n := by group
    _ = T'⁻¹ * n := by rw [hr, hc]; group

theorem rankOneTorusOne_le_normalizer_rankOneGroupTwo
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneTorusOne K a ≤ Subgroup.normalizer (rankOneGroupTwo K a : Set (ModGL F4.tag K)) := by
  have key : ∀ t ∈ rankOneTorusOne K a, ∀ g ∈ rankOneGroupTwo K a,
      t * g * t⁻¹ ∈ rankOneGroupTwo K a := by
    intro t ht g hg
    have hle : rankOneGroupTwo K a ≤
        (rankOneGroupTwo K a).comap (MulAut.conj t).toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x ((hx | ⟨v, rfl⟩) | rfl)
      · have hxU : t * x * t⁻¹ ∈ F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ :=
          (Subgroup.mem_normalizer_iff.1
            (reeFixedTorus_le_normalizer_reeFixedOrbitUnipotent _ (rankOneTorusOne_le hK ht))
              x).1 hx
        exact Subgroup.subset_closure (.inl (.inl hxU))
      · obtain ⟨u, rfl⟩ := ht
        have hc : pairedTorusHom a (f4i 0) (f4i 3) u * pairedTorusHom a (f4i 1) (f4i 2) v *
            (pairedTorusHom a (f4i 0) (f4i 3) u)⁻¹ = pairedTorusHom a (f4i 1) (f4i 2) v := by
          rw [(rankOne_commute_pairedTorusHom 0 3 1 2 u v).eq, mul_inv_cancel_right]
        have hv : pairedTorusHom a (f4i 1) (f4i 2) v ∈ rankOneGroupTwo K a :=
          Subgroup.subset_closure (.inl (.inr ⟨v, rfl⟩))
        simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        rw [hc]
        exact hv
      · obtain ⟨u, rfl⟩ := ht
        have hr := canonicalRep_conj_torusOne (a := a) hK u
        have hTT' := (rankOne_commute_pairedTorusHom (a := a) (K := K) 0 3 1 2 u
          (u ^ (2 + 2 * ((2 ^ a : ℕ) : ℤ)))).eq
        change pairedTorusHom a (f4i 0) (f4i 3) u *
          canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) *
            (pairedTorusHom a (f4i 0) (f4i 3) u)⁻¹ ∈ rankOneGroupTwo K a
        rw [centralZ_conj_eq_of_conj_eq hr hTT']
        exact mul_mem (inv_mem (Subgroup.subset_closure (.inl (.inr ⟨_, rfl⟩))))
          (Subgroup.subset_closure (.inr rfl))
    exact hle hg
  intro t ht
  refine Subgroup.mem_normalizer_iff.2 fun g => ⟨fun hg => key t ht g hg, fun hg => ?_⟩
  have h := key t⁻¹ (inv_mem ht) _ hg
  rwa [show t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g by group] at h

variable (K a) in
abbrev centralizerZ
    : Subgroup (ModGL F4.tag K) :=
  F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ⊔ rankOneGroupTwo K a

theorem rankOneTorusOne_le_normalizer_centralizerZ
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneTorusOne K a ≤ Subgroup.normalizer (centralizerZ K a : Set (ModGL F4.tag K)) :=
  fun _ ht => Subgroup.inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.2
    ⟨reeFixedTorus_le_normalizer_complement _ (rankOneTorusOne_le hK ht),
      rankOneTorusOne_le_normalizer_rankOneGroupTwo hK ht⟩)

theorem exists_mul_of_mem_reeFixedBorel
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {b : ModGL F4.tag K} (hb : b ∈ F4.reeFixedBorel K a) :
    ∃ t ∈ rankOneTorusOne K a, ∃ s ∈ centralizerZ K a, t * s = b := by
  have hb' : b ∈ (F4.reeFixedBorel K a : Set (ModGL F4.tag K)) := hb
  rw [reeFixedBorel_eq_mul] at hb'
  obtain ⟨h, hh, x, hx, rfl⟩ := hb'
  obtain ⟨u, v, rfl⟩ := rankOne_exists_torusPair_eq hK hh
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_reeFixedPosUnipotent ⟨1, by decide⟩ hx
  refine ⟨pairedTorusHom a (f4i 0) (f4i 3) u, ⟨u, rfl⟩,
    pairedTorusHom a (f4i 1) (f4i 2) v * (y * z), ?_, ?_⟩
  · refine mul_mem (Subgroup.mem_sup_right (Subgroup.subset_closure (.inl (.inr ⟨v, rfl⟩))))
      (mul_mem (Subgroup.mem_sup_left hy)
        (Subgroup.mem_sup_right (Subgroup.subset_closure (.inl (.inl hz)))))
  · beta_reduce
    rw [rankOneTorusPair_eq_mul, mul_assoc]

theorem exists_mul_of_mem_reeLocalParabolic
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : ModGL F4.tag K} (hg : g ∈ F4.reeLocalParabolic K a ⟨1, by decide⟩) :
    ∃ t ∈ rankOneTorusOne K a, ∃ s ∈ centralizerZ K a, t * s = g := by
  have hg' : g ∈ ((F4.reeGamma K a ⊓ parabolicSubgroup F4.tag K
      (F4.fixedOrbitSet ⟨1, by decide⟩) : Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) :=
    hg
  rw [coe_reeGamma_inf_parabolicSubgroup] at hg'
  rcases hg' with hB | hD
  · exact exists_mul_of_mem_reeFixedBorel hK hB
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hD
    obtain ⟨t, ht, s, hs, rfl⟩ := exists_mul_of_mem_reeFixedBorel hK hb
    obtain ⟨t', ht', s', hs', rfl⟩ := exists_mul_of_mem_reeFixedBorel hK hb'
    have hn : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) ∈
        centralizerZ K a := Subgroup.mem_sup_right (Subgroup.subset_closure (.inr rfl))
    have hsn := mul_mem hs hn
    have hconj : t'⁻¹ * (s * canonicalRep (coxeterSystem F4.tag) K
        (F4.fixedOrbitElement ⟨1, by decide⟩)) * t' ∈ centralizerZ K a := by
      have := (Subgroup.mem_normalizer_iff.1
        (rankOneTorusOne_le_normalizer_centralizerZ hK (inv_mem ht')) _).1 hsn
      rwa [inv_inv] at this
    refine ⟨t * t', mul_mem ht ht', t'⁻¹ * (s * canonicalRep (coxeterSystem F4.tag) K
        (F4.fixedOrbitElement ⟨1, by decide⟩)) * t' * s', mul_mem hconj hs', ?_⟩
    group

theorem centralizerZ_le_centralizer
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    centralizerZ K a ≤ Subgroup.centralizer {centralZ K a c} :=
  sup_le (complement_le_centralizer ha hK c) (rankOneGroupTwo_le_centralizer ha hK c)

theorem centralizerZ_le_reeGamma
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    centralizerZ K a ≤ F4.reeGamma K a :=
  sup_le (fun _ hv => (Subgroup.mem_inf.1 hv).2) (rankOneGroupTwo_le_reeGamma hK)

theorem reeGamma_inf_centralizer_eq
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ Subgroup.centralizer {centralZ K a 1} = centralizerZ K a := by
  refine le_antisymm (fun g hg => ?_) (le_inf (centralizerZ_le_reeGamma hK)
    (centralizerZ_le_centralizer ha hK 1))
  obtain ⟨t, ht, s, hs, rfl⟩ :=
    exists_mul_of_mem_reeLocalParabolic hK (reeGamma_inf_centralizer_le_reeLocalParabolic ha hK hg)
  obtain ⟨u, rfl⟩ := ht
  have hgc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2
  have hsc := Subgroup.mem_centralizer_singleton_iff.1 (centralizerZ_le_centralizer ha hK 1 hs)
  have htc : pairedTorusHom a (f4i 0) (f4i 3) u * centralZ K a 1 *
      (pairedTorusHom a (f4i 0) (f4i 3) u)⁻¹ = centralZ K a 1 := by
    have e : pairedTorusHom a (f4i 0) (f4i 3) u * centralZ K a 1 =
        centralZ K a 1 * pairedTorusHom a (f4i 0) (f4i 3) u := by
      calc pairedTorusHom a (f4i 0) (f4i 3) u * centralZ K a 1 =
          pairedTorusHom a (f4i 0) (f4i 3) u * (s * centralZ K a 1) * s⁻¹ := by
            rw [hsc]
            group
        _ = (pairedTorusHom a (f4i 0) (f4i 3) u * s * centralZ K a 1) * s⁻¹ := by group
        _ = centralZ K a 1 * pairedTorusHom a (f4i 0) (f4i 3) u := by
            rw [hgc]
            group
    rw [e, mul_inv_cancel_right]
  have h := torusPair_conj_centralZ hK u 1 1
  rw [rankOneTorusPair_left, htc] at h
  have hu1 : (u : K) ^ 2 ^ a = 1 := by
    have := centralZ_injective h
    rwa [mul_one, eq_comm] at this
  have hu : u = 1 := by
    have hq : (u : K) ^ (2 ^ a * (2 * 2 ^ a)) = u := by
      have h1 : 2 ^ a * (2 * 2 ^ a) = Nat.card K := by rw [hK]; ring
      rw [h1]
      have := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card, FiniteField.pow_card]
    refine Units.ext ?_
    rw [← hq, pow_mul, hu1, one_pow, Units.val_one]
  rw [hu, map_one, one_mul]
  exact hs

theorem complement_inf_rankOneGroupTwo
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ⊓ rankOneGroupTwo K a = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxV, hxR⟩ := Subgroup.mem_inf.1 hx
  rw [rankOneGroupTwo_eq_map hK] at hxR
  obtain ⟨x', hx'R, rfl⟩ := hxR
  have hxU : reeFixedEmb K a x' ∈ posUnipotent F4.tag K :=
    (Subgroup.mem_inf.1 (reeFixedOrbitComplementUnipotent_le _ hxV)).1
  have hx'U : (x' : adjointGroup F4.tag K) ∈ (nativeData F4.tag K).U := by
    have h := hxU
    rw [← map_nativeU_eq_posUnipotent] at h
    obtain ⟨y, hy, hyx⟩ := h
    have e : y = (x' : adjointGroup F4.tag K) := Subtype.ext hyx
    rw [← e]
    exact hy
  obtain ⟨t, ht, y, hy, hty⟩ := CFSG.SectionRank.LargeRee.exists_eq_mul_of_mem_B_of_mem_r2 hK ha
    ((nativeData F4.tag K).U_le_B hx'U) hx'R
  have htT : reeFixedEmb K a t ∈ torusGroup F4.tag K := by
    have h : reeFixedEmb K a t ∈ rankOneTorusTwo K a := by
      rw [← map_blockT_one hK]
      exact ⟨t, ht, rfl⟩
    exact (Subgroup.mem_inf.1 (rankOneTorusTwo_le hK h)).1
  have hyU : reeFixedEmb K a y ∈ F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ := by
    rw [← map_blockX_one]
    exact ⟨y, hy, rfl⟩
  have htU : reeFixedEmb K a t ∈ posUnipotent F4.tag K := by
    have e : reeFixedEmb K a t = reeFixedEmb K a x' * (reeFixedEmb K a y)⁻¹ := by
      rw [hty, map_mul, mul_inv_cancel_right]
    rw [e]
    exact mul_mem hxU (inv_mem (Subgroup.mem_inf.1 (reeFixedOrbitUnipotent_le _ hyU)).1)
  have ht1 : reeFixedEmb K a t = 1 := by
    have h := Subgroup.mem_inf.2 ⟨htT, htU⟩
    rwa [CFSG.LieType.Chevalley.torusGroup_inf_posUnipotent, Subgroup.mem_bot] at h
  have hxy : reeFixedEmb K a x' = reeFixedEmb K a y := by rw [hty, map_mul, ht1, one_mul]
  have hm : reeFixedEmb K a x' ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ⊓
      F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ := Subgroup.mem_inf.2 ⟨hxV, hxy ▸ hyU⟩
  rwa [reeFixedOrbitComplementUnipotent_inf_reeFixedOrbitUnipotent] at hm

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem centralRoot_mem_complementRoots :
    centralRoot44 ∈ F4.fixedOrbitComplementRoots ⟨1, by decide⟩ ∧
      centralRoot47 ∈ F4.fixedOrbitComplementRoots ⟨1, by decide⟩ := by
  refine ⟨mem_fixedOrbitComplementRoots_iff.2 ⟨isRoot_centralRoot44.1, isRoot_centralRoot44.2,
    ⟨0, by decide⟩, by decide, by decide⟩, mem_fixedOrbitComplementRoots_iff.2
      ⟨isRoot_centralRoot47.1, isRoot_centralRoot47.2, ⟨0, by decide⟩, by decide, by decide⟩⟩

theorem centralZ_mem_complement
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    centralZ K a c ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ :=
  Subgroup.mem_inf.2 ⟨mul_mem (pinnedX_mem_rootSpan centralRoot_mem_complementRoots.1 _)
    (pinnedX_mem_rootSpan centralRoot_mem_complementRoots.2 _),
    (Subgroup.mem_inf.1 (centralZ_mem ha hK c)).2⟩

theorem centralizerZ_le_normalizer
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    centralizerZ K a ≤ Subgroup.normalizer
      (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ : Set (ModGL F4.tag K)) :=
  sup_le Subgroup.le_normalizer (rankOneGroupTwo_le_normalizer_complement hK)

theorem isPGroup_reeFixedPosUnipotent
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsPGroup 2 (F4.reeFixedPosUnipotent K a) := by
  obtain ⟨S, hS⟩ := (CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_Sylow_center a ha
    K hK).1
  have h := S.isPGroup'
  rw [hS] at h
  exact h.of_equiv (Subgroup.subgroupOfEquivOfLe (reeFixedPosUnipotent_le_reeGamma
    (t := F4) (K := K) (a := a)))

omit [Finite K] [CharP K F4.prime] in
theorem centralZ_eq_zero_of_pinnedX_mul_eq
    {β γ δ ε : Fin F4.tag.rank → ℤ}
    (hβ : IsRoot F4.tag β ∧ 0 < height β) (hγ : IsRoot F4.tag γ ∧ 0 < height γ)
    (hδ : IsRoot F4.tag δ ∧ 0 < height δ) (hε : IsRoot F4.tag ε ∧ 0 < height ε)
    (hnd : [β, γ, δ, ε].Nodup) {c d c' d' : K}
    (h : pinnedX F4.tag K β c * pinnedX F4.tag K γ d =
      pinnedX F4.tag K δ c' * pinnedX F4.tag K ε d') : c = 0 := by
  have hβγ : β ≠ γ := fun e => by simp [e] at hnd
  have hβδ : β ≠ δ := fun e => by simp [e] at hnd
  have hβε : β ≠ ε := fun e => by simp [e] at hnd
  have hγδ : γ ≠ δ := fun e => by simp [e] at hnd
  have hγε : γ ≠ ε := fun e => by simp [e] at hnd
  have hδε : δ ≠ ε := fun e => by simp [e] at hnd
  have hL := pinnedX_list_prod_injective (R := K) [β, γ, δ, ε] hnd
    (by
      intro α hα
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
      rcases hα with rfl | rfl | rfl | rfl
      · exact hβ
      · exact hγ
      · exact hδ
      · exact hε)
    (fun α => if α = β then c else if α = γ then d else 0)
    (fun α => if α = δ then c' else if α = ε then d' else 0)
    (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        ↓reduceIte, hβδ, hβε, hγδ, hγε, hβγ.symm, hβδ.symm, hβε.symm, hγδ.symm,
        hγε.symm, hδε.symm, pinnedX_zero, one_mul]
      exact h)
  simpa [hβδ, hβε] using hL β (by simp)

abbrev centralAOne : ModGL F4.tag K :=
  xUnit F4.tag K largeReeI1 1 * xUnit F4.tag K largeReeI4 1

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem fixedOrbitRoots_zero_subset_complement :
    F4.fixedOrbitRoots ⟨0, by decide⟩ ⊆ F4.fixedOrbitComplementRoots ⟨1, by decide⟩ := by
  rw [F4_fixedOrbitRoots_zero]
  rintro α (rfl | rfl)
  · exact mem_fixedOrbitComplementRoots_iff.2 ⟨isRoot_single _ _, by decide, ⟨0, by decide⟩,
      by decide, by decide⟩
  · exact mem_fixedOrbitComplementRoots_iff.2 ⟨isRoot_single _ _, by decide, ⟨3, by decide⟩,
      by decide, by decide⟩

theorem centralAOne_mem_complement
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    centralAOne ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ := by
  have h : (centralAOne : ModGL F4.tag K) ∈
      (F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ : Set (ModGL F4.tag K)) := by
    rw [coe_reeFixedOrbitUnipotent_zero hK]
    exact ⟨1, by simp [centralAOne]⟩
  exact Subgroup.mem_inf.2 ⟨rootSpan_mono fixedOrbitRoots_zero_subset_complement
    (Subgroup.mem_inf.1 h).1, (Subgroup.mem_inf.1 h).2⟩

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem single_largeReeI1 : (Pi.single largeReeI1 1 : Fin F4.tag.rank → ℤ) = centralRootE1 := by
  funext i
  change Fin 4 at i
  fin_cases i <;> rfl

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem single_largeReeI4 : (Pi.single largeReeI4 1 : Fin F4.tag.rank → ℤ) = centralRootE4 := by
  funext i
  change Fin 4 at i
  fin_cases i <;> rfl

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem fixedOrbitElement_one_smul_centralRootE1 :
    F4.fixedOrbitElement ⟨1, by decide⟩ • centralRootE1 = centralRootZE1 := by
  rw [fixedOrbitElement_smul]
  exact Certificates.certificate18000.2.2.2.1

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem fixedOrbitElement_one_smul_centralRootE4 :
    F4.fixedOrbitElement ⟨1, by decide⟩ • centralRootE4 = centralRootZE4 := by
  rw [fixedOrbitElement_smul]
  exact Certificates.certificate18000.2.2.2.2

omit [Finite K] in
theorem canonicalRep_mul_centralAOne_ne :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) * centralAOne ≠
      centralAOne * canonicalRep (coxeterSystem F4.tag) K
        (F4.fixedOrbitElement ⟨1, by decide⟩) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  intro h
  have hconj : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) *
      centralAOne * (canonicalRep (coxeterSystem F4.tag) K
        (F4.fixedOrbitElement ⟨1, by decide⟩))⁻¹ = (centralAOne : ModGL F4.tag K) := by
    rw [h, mul_inv_cancel_right]
  have e : ∀ A X Y : ModGL F4.tag K, A * (X * Y) * A⁻¹ = (A * X * A⁻¹) * (A * Y * A⁻¹) :=
    fun A X Y => by group
  have hE1 : IsRoot F4.tag centralRootE1 := by rw [← single_largeReeI1]; exact isRoot_single _ _
  have hE4 : IsRoot F4.tag centralRootE4 := by rw [← single_largeReeI4]; exact isRoot_single _ _
  rw [centralAOne, ← pinnedX_single, ← pinnedX_single, single_largeReeI1, single_largeReeI4, e,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ hE1,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ hE4, fixedOrbitElement_one_smul_centralRootE1,
    fixedOrbitElement_one_smul_centralRootE4] at hconj
  have hZ1 : IsRoot F4.tag centralRootZE1 ∧ 0 < height centralRootZE1 := by
    rw [← fixedOrbitElement_one_smul_centralRootE1]
    exact ⟨CFSG.LieType.Chevalley.IsRoot.smul hE1 _, by
      rw [fixedOrbitElement_one_smul_centralRootE1]; decide⟩
  have hZ4 : IsRoot F4.tag centralRootZE4 ∧ 0 < height centralRootZE4 := by
    rw [← fixedOrbitElement_one_smul_centralRootE4]
    exact ⟨CFSG.LieType.Chevalley.IsRoot.smul hE4 _, by
      rw [fixedOrbitElement_one_smul_centralRootE4]; decide⟩
  exact one_ne_zero (centralZ_eq_zero_of_pinnedX_mul_eq hZ1 hZ4 ⟨hE1, by decide⟩
    ⟨hE4, by decide⟩ (by decide) hconj)

theorem centralizerZ_kernel
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ((F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf
        (centralizerZ K a)).Normal ∧
      IsPGroup 2 ((F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf
        (centralizerZ K a)) ∧
      Subgroup.centralizer (((F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf
        (centralizerZ K a) : Subgroup (centralizerZ K a)) : Set (centralizerZ K a)) ≤
          (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf (centralizerZ K a) ∧
      (∀ M : Subgroup (centralizerZ K a), M.Normal → IsPGroup 2 M →
        M ≤ (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf
          (centralizerZ K a)) ∧
      ∀ M : Subgroup (centralizerZ K a), M.Normal → Odd (Nat.card M) → M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := F4.tag) (K := K)
  have hle : F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ≤ centralizerZ K a :=
    le_sup_left
  have hRle : rankOneGroupTwo K a ≤ centralizerZ K a := le_sup_right
  have hN : ((F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf
      (centralizerZ K a)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 (centralizerZ_le_normalizer hK)
  have hN2 : IsPGroup 2 ((F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf
      (centralizerZ K a)) :=
    ((isPGroup_reeFixedPosUnipotent ha hK).to_le
      (reeFixedOrbitComplementUnipotent_le _)).of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hNR : (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf
      (centralizerZ K a) ⊔ (rankOneGroupTwo K a).subgroupOf (centralizerZ K a) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hle hRle, Subgroup.subgroupOf_self]
  obtain ⟨hsimple, x, y, hxy⟩ := isSimpleGroup_rankOneGroupTwo ha hK
  set e := Subgroup.subgroupOfEquivOfLe hRle
  have : IsSimpleGroup ((rankOneGroupTwo K a).subgroupOf (centralizerZ K a)) := e.isSimpleGroup
  have hRnab : ∃ x y : (rankOneGroupTwo K a).subgroupOf (centralizerZ K a), x * y ≠ y * x := by
    refine ⟨e.symm x, e.symm y, fun h => hxy ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact e.symm.injective h
  have hn : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) ∈
      rankOneGroupTwo K a := Subgroup.subset_closure (.inr rfl)
  have hA := centralAOne_mem_complement (K := K) (a := a) hK
  have hact : ∃ r ∈ (rankOneGroupTwo K a).subgroupOf (centralizerZ K a),
      ∃ n ∈ (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf
        (centralizerZ K a), r * n ≠ n * r :=
    ⟨⟨_, hRle hn⟩, hn, ⟨_, hle hA⟩, hA, fun h =>
      canonicalRep_mul_centralAOne_ne (congrArg Subtype.val h)⟩
  obtain ⟨hC, hO, hOdd⟩ := kernel_selfCentralizing hN hN2 hNR hRnab hact
  exact ⟨hN, hN2, hC, hO, hOdd⟩

theorem card_centralizerZ
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (centralizerZ K a) =
      Nat.card (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩) *
        Nat.card (rankOneGroupTwo K a) := by
  have hset : ((centralizerZ K a : Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) =
      (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ : Set (ModGL F4.tag K)) *
        (rankOneGroupTwo K a : Set (ModGL F4.tag K)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (rankOneGroupTwo_le_normalizer_complement hK)
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective (fun p : F4.reeFixedOrbitComplementUnipotent K a
      ⟨1, by decide⟩ × rankOneGroupTwo K a => (⟨(p.1 : ModGL F4.tag K) * p.2,
        mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ :
          centralizerZ K a)) ⟨?_, ?_⟩)).symm
  · rintro ⟨v, r⟩ ⟨v', r'⟩ h
    have h' : (v : ModGL F4.tag K) * r = v' * r' := congrArg Subtype.val h
    have hm : (v' : ModGL F4.tag K)⁻¹ * v ∈
        F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ⊓ rankOneGroupTwo K a := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem v'.2) v.2, ?_⟩
      have e : (v' : ModGL F4.tag K)⁻¹ * v = r' * (r : ModGL F4.tag K)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
      rw [e]
      exact mul_mem r'.2 (inv_mem r.2)
    rw [complement_inf_rankOneGroupTwo ha hK, Subgroup.mem_bot, inv_mul_eq_one] at hm
    have hv : v = v' := Subtype.ext hm.symm
    subst hv
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h'))
  · rintro ⟨g, hg⟩
    have hg' : g ∈ ((centralizerZ K a : Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) := hg
    rw [hset] at hg'
    obtain ⟨v, hv, r, hr, rfl⟩ := hg'
    exact ⟨(⟨v, hv⟩, ⟨r, hr⟩), rfl⟩

theorem card_complement_two_mul
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩) * (2 ^ (2 * a + 1)) ^ 2 =
      Nat.card (F4.reeFixedPosUnipotent K a) := by
  rw [card_reeFixedPosUnipotent_eq_mul ⟨1, by decide⟩, card_reeFixedOrbitUnipotent_one hK, hK]

theorem card_complement_two_and_centralizerZ
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hU : Nat.card (F4.reeFixedPosUnipotent K a) = (2 ^ (2 * a + 1)) ^ 12) :
    Nat.card (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩) = (2 ^ (2 * a + 1)) ^ 10 ∧
      Nat.card (centralizerZ K a) =
        (2 ^ (2 * a + 1)) ^ 12 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have h1 := card_complement_two_mul (a := a) hK
  rw [hU] at h1
  have hq : 0 < (2 ^ (2 * a + 1)) ^ 2 := by positivity
  have hV : Nat.card (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩) =
      (2 ^ (2 * a + 1)) ^ 10 := by
    have : (2 ^ (2 * a + 1)) ^ 12 = (2 ^ (2 * a + 1)) ^ 10 * (2 ^ (2 * a + 1)) ^ 2 := by ring
    rw [this] at h1
    exact Nat.eq_of_mul_eq_mul_right hq h1
  refine ⟨hV, ?_⟩
  rw [card_centralizerZ ha hK, hV, card_rankOneGroupTwo ha hK]
  ring

theorem centralZ_mem_center
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    (⟨centralZ K a c, Subgroup.mem_sup_left (centralZ_mem_complement ha hK c)⟩ :
      centralizerZ K a) ∈ Subgroup.center (centralizerZ K a) := by
  refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
  exact Subgroup.mem_centralizer_singleton_iff.1 (centralizerZ_le_centralizer ha hK c g.2)

theorem large_Ree_centralZ_centralizer
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ Subgroup.centralizer {centralZ K a 1} =
      F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ⊔ rankOneGroupTwo K a ∧
    F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ⊓ rankOneGroupTwo K a = ⊥ ∧
    Nonempty (rankOneGroupTwo K a ≃* CFSG.Blueprint.suzukiGroup a K) ∧
    ((F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf
        (centralizerZ K a)).Normal ∧
    IsPGroup 2 ((F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf
      (centralizerZ K a)) ∧
    Subgroup.centralizer (((F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf
      (centralizerZ K a) : Subgroup (centralizerZ K a)) : Set (centralizerZ K a)) ≤
        (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf (centralizerZ K a) ∧
    (∀ M : Subgroup (centralizerZ K a), M.Normal → IsPGroup 2 M →
      M ≤ (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf
        (centralizerZ K a)) ∧
    (∀ M : Subgroup (centralizerZ K a), M.Normal → Odd (Nat.card M) → M = ⊥) ∧
    (∀ c : K, (⟨centralZ K a c, Subgroup.mem_sup_left (centralZ_mem_complement ha hK c)⟩ :
      centralizerZ K a) ∈ Subgroup.center (centralizerZ K a)) ∧
    Nat.card (centralizerZ K a) =
      Nat.card (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩) *
        Nat.card (rankOneGroupTwo K a) ∧
    Nat.card (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩) * (2 ^ (2 * a + 1)) ^ 2 =
      Nat.card (F4.reeFixedPosUnipotent K a) ∧
    Nat.card (rankOneGroupTwo K a) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  obtain ⟨hN, hN2, hC, hO, hOdd⟩ := centralizerZ_kernel ha hK
  exact ⟨reeGamma_inf_centralizer_eq ha hK, complement_inf_rankOneGroupTwo ha hK,
    ⟨rankOneEquivSuzuki K a ha hK⟩, hN, hN2, hC, hO, hOdd, centralZ_mem_center ha hK,
    card_centralizerZ ha hK, card_complement_two_mul hK, card_rankOneGroupTwo ha hK⟩

end CFSG.LieType.Ree.LargeReeInvolution
