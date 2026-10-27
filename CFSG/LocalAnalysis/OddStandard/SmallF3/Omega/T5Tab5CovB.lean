module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Tab5Cov
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped Pointwise

section CoverFacts


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate} {φ : ↥L →* omegaGroup hQ}

private theorem invType_piOrth_mul_of_type_two (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {t : OGroup Q}
    (htt : t * t = 1) (ht : invType t = (2, -1)) :
    invType (piOrth Q * t) = (4, 1) ∧ (piOrth Q * t) * (piOrth Q * t) = 1 := by
  have hdim2 : invDim t = 2 := congrArg Prod.fst ht
  have hsign2 : invSign t = -1 := congrArg Prod.snd ht
  have hcpi : t * piOrth Q = piOrth Q * t :=
    Subgroup.mem_center_iff.mp piOrth_mem_center t
  constructor
  · have h' := invType_piOrth_mul_of_even_minus hQ htt (by rw [hdim]; decide) hsgn
    rw [h', hdim2, hsign2, hdim]
    decide
  · calc (piOrth Q * t) * (piOrth Q * t) = piOrth Q * (t * piOrth Q) * t := by group
      _ = piOrth Q * (piOrth Q * t) * t := by rw [hcpi]
      _ = (piOrth Q * piOrth Q) * (t * t) := by group
      _ = 1 := by rw [piOrth_mul_self, htt, mul_one]

private theorem mem_conjClassIn_of_conj (h : IsCoverMap L φ) (hO : OddCentralCover φ)
    {a b : ↥L} (ha : a * a = 1) (hb : b * b = 1) {c : OGroup Q} (hcΩ : c ∈ omegaGroup hQ)
    (hc : c * (φ a : OGroup Q) * c⁻¹ = (φ b : OGroup Q)) :
    (b : G) ∈ conjClassIn L (a : G) := by
  obtain ⟨l, hl⟩ := h.surjective (⟨c, hcΩ⟩ : omegaGroup hQ)
  have hsq : (l * a * l⁻¹) * (l * a * l⁻¹) = 1 := by
    calc (l * a * l⁻¹) * (l * a * l⁻¹) = l * (a * a) * l⁻¹ := by group
      _ = 1 := by rw [ha]; group
  have himg : φ (l * a * l⁻¹) = φ b := by
    rw [map_mul, map_mul, map_inv, hl]
    exact Subtype.ext hc
  have heq : l * a * l⁻¹ = b := hO.eq_of_mul_self_eq_one hsq hb himg
  exact ⟨(l : G), l.2, (congrArg Subtype.val heq).symm⟩

end CoverFacts

theorem asc82Tab5_inner_lift_of (hS : Asc82SchurU43) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → Kind5 L s 0 →
        ∃ w ∈ L, orderOf w = 2 ∧ w⁻¹ * s ∈ centralizer (L : Set G) := by
  intro G _ _ L hL s hs2 _ hsK
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, h⟩ := t5_exists_cover hS hL
  letI := i1; letI := i2; letI := i3
  have hO : OddCentralCover φ := h.oddCentralCover hL
  have hdim : Module.finrank (ZMod 3) V = 6 := h.finrank_eq
  have hsgn : quadSign Q = -1 := h.quadSign_eq
  obtain ⟨hsInner, hs_notC⟩ := hsK
  unfold InnerOn at hsInner
  have hcoe : ((L ⊔ centralizer (L : Set G) : Subgroup G) : Set G) =
      (L : Set G) * (centralizer (L : Set G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L (centralizer (L : Set G))
      (Subgroup.centralizer_le_normalizer (L : Set G))
  have hmulmem : s ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
    rw [← hcoe]; exact hsInner
  rw [Set.mem_mul] at hmulmem
  obtain ⟨l, hl, c, hc, hlc⟩ := hmulmem
  have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc l hl
  have hs_sq : s * s = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
  have h1 : (l * c) * (l * c) = 1 := by rw [hlc, hs_sq]
  have h2 : l * l * (c * c) = 1 := by
    calc l * l * (c * c) = l * (l * c) * c := by group
      _ = l * (c * l) * c := by rw [← hcl]
      _ = (l * c) * (l * c) := by group
      _ = 1 := h1
  have hd : l * l = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left h2
  have hl'2_center : (⟨l, hl⟩ : ↥L) * ⟨l, hl⟩ ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    show (m : G) * (l * l) = (l * l) * (m : G)
    rw [hd]
    exact Subgroup.mem_centralizer_iff.mp (inv_mem (mul_mem hc hc)) (m : G) m.2
  have hphil2_cent : φ ((⟨l, hl⟩ : ↥L) * ⟨l, hl⟩) ∈ Subgroup.center (omegaGroup hQ) :=
    t5_map_center_le_center φ h.surjective (Subgroup.mem_map_of_mem φ hl'2_center)
  rcases t5_center_omegaGroup_six_minus hQ hdim hsgn hphil2_cent with hsq | hpi
  · have hsl'_sq : φ ⟨l, hl⟩ * φ ⟨l, hl⟩ = 1 := by rw [← map_mul]; exact hsq
    have hpow1 : (⟨l, hl⟩ : ↥L) ^ Nat.card φ.ker * ⟨l, hl⟩ ^ Nat.card φ.ker = 1 :=
      (hO.pow_card_ker hsl'_sq).1
    have hpow2 : φ ((⟨l, hl⟩ : ↥L) ^ Nat.card φ.ker) = φ ⟨l, hl⟩ :=
      (hO.pow_card_ker hsl'_sq).2
    have hl'_ne : φ ⟨l, hl⟩ ≠ 1 := by
      intro h1'
      have hl'_ker : (⟨l, hl⟩ : ↥L) ∈ φ.ker := MonoidHom.mem_ker.mpr h1'
      have hl'_cent : (⟨l, hl⟩ : ↥L) ∈ Subgroup.center ↥L := hO.ker_le_center hl'_ker
      have hl_cent : l ∈ centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hl'_cent ⟨m, hm⟩)
      exact hs_notC (by rw [← hlc]; exact mul_mem hl_cent hc)
    have hw'_ne : (⟨l, hl⟩ : ↥L) ^ Nat.card φ.ker ≠ 1 := by
      intro h1'
      exact hl'_ne (by rw [← hpow2, h1', map_one])
    have hw'_ord : orderOf ((⟨l, hl⟩ : ↥L) ^ Nat.card φ.ker) = 2 :=
      orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hpow1) hw'_ne
    refine ⟨(((⟨l, hl⟩ : ↥L) ^ Nat.card φ.ker : ↥L) : G),
      ((⟨l, hl⟩ : ↥L) ^ Nat.card φ.ker).2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, hw'_ord]
    · have hker : ((⟨l, hl⟩ : ↥L) ^ Nat.card φ.ker)⁻¹ * ⟨l, hl⟩ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hpow2, inv_mul_cancel]
      have hcent : (((⟨l, hl⟩ : ↥L) ^ Nat.card φ.ker)⁻¹ * ⟨l, hl⟩) ∈
          Subgroup.center ↥L := hO.ker_le_center hker
      have hcentG : ((((⟨l, hl⟩ : ↥L) ^ Nat.card φ.ker)⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈
          centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcent ⟨m, hm⟩)
      have heq : (((⟨l, hl⟩ : ↥L) ^ Nat.card φ.ker : ↥L) : G)⁻¹ * s =
          ((((⟨l, hl⟩ : ↥L) ^ Nat.card φ.ker)⁻¹ * ⟨l, hl⟩ : ↥L) : G) * c := by
        rw [← hlc, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [heq]
      exact mul_mem hcentG hc
  · have hsqpi : ∃ p : omegaGroup hQ, (p : OGroup Q) * p = piOrth Q := by
      refine ⟨φ ⟨l, hl⟩, ?_⟩
      have h' := hpi
      rw [map_mul] at h'
      exact h'
    exact absurd hsqpi (t5_pi_not_sq hdim hsgn)

theorem asc82Tab5_inv_classes_of (hS : Asc82SchurU43) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ t : G, t ∈ centerIn L → orderOf t = 2 → ∀ z : G, IsI4PlusIn L z →
        ∀ u ∈ L, orderOf u = 2 → u ≠ t → u ∈ conjClassIn L z ∨ u ∈ conjClassIn L (t * z) := by
  intro G _ _ L hL t ht ht2 z hz u hu hu2 hut
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, h⟩ := t5_exists_cover hS hL
  letI := i1; letI := i2; letI := i3
  have hO : OddCentralCover φ := h.oddCentralCover hL
  have hdim : Module.finrank (ZMod 3) V = 6 := h.finrank_eq
  have hsgn : quadSign Q = -1 := h.quadSign_eq
  have hz2 : orderOf z = 2 := hz.1
  obtain ⟨K, hzK, hKL, _, _⟩ := hz.2
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (hKL hzK)).1
  obtain ⟨t', ht'center, ht'val⟩ := Subgroup.mem_map.mp ht
  have htL : t ∈ L := ht'val ▸ t'.2
  have hz'sq : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 :=
    t5_mul_self_eq_one_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, hz2])
  have hu'sq : (⟨u, hu⟩ : ↥L) * ⟨u, hu⟩ = 1 :=
    t5_mul_self_eq_one_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, hu2])
  have ht'sq : (⟨t, htL⟩ : ↥L) * ⟨t, htL⟩ = 1 :=
    t5_mul_self_eq_one_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, ht2])
  have hzphi_type : invType (((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q)) = (4, 1) :=
    t5_phi_pocket_invType h hL hz hzL
  have hzphi_sq : ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) *
      ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hz'sq, map_one]
    rfl
  have huphi_sq : ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) *
      ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hu'sq, map_one]
    rfl
  have huphi_ne : φ ⟨u, hu⟩ ≠ 1 := by
    intro h1
    have hu'1 : (⟨u, hu⟩ : ↥L) = 1 :=
      hO.eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr h1) hu'sq
    have hu1 : u = 1 := congrArg Subtype.val hu'1
    rw [hu1, orderOf_one] at hu2
    exact absurd hu2 (by decide)
  have hpi : piOrth Q ∈ omegaGroup hQ :=
    (piOrth_mem_omegaGroup_iff hQ).mpr ⟨by rw [hdim]; decide, by rw [hsgn, hdim]; decide⟩
  have ht_pi : φ ⟨t, htL⟩ = (⟨piOrth Q, hpi⟩ : omegaGroup hQ) :=
    Subtype.ext (h.map_central hL ht ht2 htL)
  have ht_center : (⟨t, htL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    have hxw : t' = (⟨t, htL⟩ : ↥L) := Subtype.ext ht'val
    rw [← hxw]; exact ht'center
  have ht'z' : (⟨t, htL⟩ : ↥L) * ⟨z, hzL⟩ = ⟨z, hzL⟩ * ⟨t, htL⟩ :=
    (Subgroup.mem_center_iff.mp ht_center ⟨z, hzL⟩).symm
  have htG : t * t = 1 := congrArg Subtype.val ht'sq
  have hzG : z * z = 1 := congrArg Subtype.val hz'sq
  have hcomm : z * t = t * z := (congrArg Subtype.val ht'z').symm
  have haG : (t * z) * (t * z) = 1 := by
    calc (t * z) * (t * z) = t * (z * t) * z := by group
      _ = t * (t * z) * z := by rw [hcomm]
      _ = (t * t) * (z * z) := by group
      _ = 1 := by rw [htG, hzG, mul_one]
  have ha : ((⟨t, htL⟩ : ↥L) * ⟨z, hzL⟩) * ((⟨t, htL⟩ : ↥L) * ⟨z, hzL⟩) = 1 := by
    apply Subtype.ext
    exact haG
  rcases t5_omega_involution_type hdim huphi_sq (φ ⟨u, hu⟩ : omegaGroup hQ).2 with
    h0 | h2t | h4 | h6
  · have h0dim : invDim ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) = 0 :=
      congrArg Prod.fst h0
    have h0eq : ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) = 1 :=
      (invDim_eq_zero_iff huphi_sq).mp h0dim
    exact absurd (Subtype.ext h0eq) huphi_ne
  · obtain ⟨hpiu_type, hpiu_sq⟩ := invType_piOrth_mul_of_type_two hQ hdim hsgn huphi_sq h2t
    obtain ⟨c, hcΩ, hc⟩ := exists_mem_omegaGroup_conj hQ (by rw [hdim]; norm_num)
      hzphi_sq hpiu_sq (by rw [hzphi_type, hpiu_type])
    have hc' : c * (piOrth Q * ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q)) * c⁻¹ =
        ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) := by
      have hcpic : c * piOrth Q = piOrth Q * c :=
        Subgroup.mem_center_iff.mp piOrth_mem_center c
      calc c * (piOrth Q * ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q)) * c⁻¹
          = (c * piOrth Q) * ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) * c⁻¹ := by group
        _ = (piOrth Q * c) * ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) * c⁻¹ := by rw [hcpic]
        _ = piOrth Q * (c * ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) * c⁻¹) := by group
        _ = piOrth Q * (piOrth Q * ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q)) := by rw [hc]
        _ = ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) := by
          rw [← mul_assoc, piOrth_mul_self, one_mul]
    have hconj : c * ((φ (⟨t, htL⟩ * ⟨z, hzL⟩) : omegaGroup hQ) : OGroup Q) * c⁻¹ =
        ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) := by
      rw [map_mul, Subgroup.coe_mul, h.map_central hL ht ht2 htL]
      exact hc'
    exact Or.inr (mem_conjClassIn_of_conj (a := ⟨t, htL⟩ * ⟨z, hzL⟩) (b := ⟨u, hu⟩)
      h hO ha hu'sq hcΩ hconj)
  · obtain ⟨c, hcΩ, hc⟩ := exists_mem_omegaGroup_conj hQ (by rw [hdim]; norm_num)
      hzphi_sq huphi_sq (by rw [hzphi_type, h4])
    exact Or.inl (mem_conjClassIn_of_conj (a := ⟨z, hzL⟩) (b := ⟨u, hu⟩)
      h hO hz'sq hu'sq hcΩ hc)
  · have h6dim : invDim ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) =
        Module.finrank (ZMod 3) V := by
      have h' := congrArg Prod.fst h6
      rw [hdim]
      exact h'
    have h6eq : ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) = piOrth Q :=
      (invDim_eq_finrank_iff huphi_sq).mp h6dim
    have heq : φ ⟨u, hu⟩ = φ ⟨t, htL⟩ := by
      apply Subtype.ext
      rw [h6eq, ht_pi]
    exact absurd (congrArg Subtype.val (hO.eq_of_mul_self_eq_one hu'sq ht'sq heq)) hut

end CFSG.OddStandard.SmallF3.Omega
