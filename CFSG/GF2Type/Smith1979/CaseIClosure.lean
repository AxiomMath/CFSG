module

public import CFSG.GF2Type.Smith1979.CaseIDefs
public import CFSG.LargeExtraspecial.S7Three
public import CFSG.LargeExtraspecial.O62Normalizer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_add_smul_self eichler_conj
  eichler_zero_right)

namespace CaseIClosure

section Abstract

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {Q : QuadraticForm (ZMod 2) W}

theorem eichler_eq_iff (hQ : Q.polarBilin.Nondegenerate) {a x y : W} (ha0 : a ≠ 0) (ha : Q a = 0)
    (hx : polar Q a x = 0) (hy : polar Q a y = 0) :
    eichler Q a x = eichler Q a y ↔ x = y ∨ x = y + a := by
  constructor
  · intro h
    have hxy : polar Q a (x + y) = 0 := by rw [polar_add_right, hx, hy, add_zero]
    have h1 : eichler Q a (x + y) = 1 := by
      rw [← eichler_mul hx hy, h, eichler_mul hy hy, vec_add_self, eichler_zero_right]
    have h2 := (eichler_eq_one_iff hQ ha0 ha hxy).mp h1
    rcases mem_span_cl_iff.mp h2 with h3 | h3
    · left
      rw [eq_neg_of_add_eq_zero_left h3, vec_neg]
    · right
      rw [← h3, add_comm y (x + y), add_assoc, vec_add_self, add_zero]
  · rintro (rfl | rfl)
    · rfl
    · have := eichler_add_smul_self (Q := Q) ha y 1
      rwa [one_smul] at this

theorem ncard_eichler_image_le {a : W} (ha0 : a ≠ 0) (ha : Q a = 0)
    (h10 : {x : W | polar Q a x = 0 ∧ Q x = 0 ∧ x ≠ 0 ∧ x ≠ a}.ncard = 10) :
    (eichler Q a '' {x : W | polar Q a x = 0 ∧ Q x = 0 ∧ x ≠ 0 ∧ x ≠ a}).ncard ≤ 5 := by
  classical
  have : Finite W := Module.finite_of_finite (ZMod 2)
  set T : Set W := {x : W | polar Q a x = 0 ∧ Q x = 0 ∧ x ≠ 0 ∧ x ≠ a} with hT
  have hTf : T.Finite := Set.toFinite _
  have himg : eichler Q a '' T = ↑(hTf.toFinset.image (eichler Q a)) := by
    ext y
    simp
  rw [himg, Set.ncard_coe_finset]
  have h2 : 2 * (hTf.toFinset.image (eichler Q a)).card ≤ hTf.toFinset.card := by
    refine Finset.mul_card_image_le_card hTf.toFinset 2 fun b hb => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    have hx' := hTf.mem_toFinset.mp hx
    obtain ⟨hxp, hxq, hx0, hxa⟩ := hx'
    have hsub : ({x, x + a} : Finset W) ⊆
        hTf.toFinset.filter (fun y => eichler Q a y = eichler Q a x) := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Finset.mem_filter, hTf.mem_toFinset]
      rcases hy with rfl | rfl
      · exact ⟨⟨hxp, hxq, hx0, hxa⟩, rfl⟩
      · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [polar_add_right, hxp, polar_self_eq_zero, add_zero]
        · rw [QuadraticMap.map_add Q x a, hxq, ha, polar_comm Q x a, hxp, add_zero, add_zero]
        · intro h
          apply hxa
          rw [← neg_eq_of_add_eq_zero_left h, vec_neg]
        · intro h
          apply hx0
          have := congrArg (fun z => z + a) h
          simpa [add_assoc, vec_add_self] using this
        · simpa using eichler_add_smul_self (Q := Q) ha x 1
    have hne : x ≠ x + a := by
      intro h
      apply ha0
      have := congrArg (fun z => z - x) h
      simpa using this.symm
    calc 2 = ({x, x + a} : Finset W).card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hc : hTf.toFinset.card = 10 := by
    rw [← Set.ncard_eq_toFinset_card T hTf]
    exact h10
  omega

end Abstract

section Counting

theorem ncard_le_two_mul {X Y : Type*} {A : Set X} {B : Set Y} (hA : A.Finite) (hB : B.Finite)
    (f : X → Y) (ι : X → X) (hmap : ∀ x ∈ A, f x ∈ B)
    (hfib : ∀ x₁ ∈ A, ∀ x₂ ∈ A, f x₁ = f x₂ → x₂ = x₁ ∨ x₂ = ι x₁) :
    A.ncard ≤ 2 * B.ncard := by
  classical
  have h := Finset.card_le_mul_card_image_of_maps_to (f := f) (s := hA.toFinset)
    (t := hB.toFinset) (fun x hx => hB.mem_toFinset.mpr (hmap x (hA.mem_toFinset.mp hx))) 2
    (fun b _ => ?_)
  · rwa [← Set.ncard_eq_toFinset_card A hA, ← Set.ncard_eq_toFinset_card B hB] at h
  · by_cases hne : ∃ x₁ ∈ hA.toFinset, f x₁ = b
    · obtain ⟨x₁, hx₁, hfx⟩ := hne
      have hsub : hA.toFinset.filter (fun a => f a = b) ⊆ {x₁, ι x₁} := by
        intro x hx
        rw [Finset.mem_filter] at hx
        have := hfib x₁ (hA.mem_toFinset.mp hx₁) x (hA.mem_toFinset.mp hx.1)
          (by rw [hfx, hx.2])
        rw [Finset.mem_insert, Finset.mem_singleton]
        exact this
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    · push Not at hne
      have : hA.toFinset.filter (fun a => f a = b) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        exact fun x hx => hne x hx
      rw [this]
      simp

theorem five_dvd_ncard {X : Type*} [Group X] {A : Set X} (hA : A.Finite) {c : X}
    (hc5 : ∀ x ∈ A, c ^ 5 * x * (c ^ 5)⁻¹ = x) (hcA : ∀ x ∈ A, c * x * c⁻¹ ∈ A)
    (hfree : ∀ x ∈ A, c * x * c⁻¹ ≠ x) : 5 ∣ A.ncard := by
  haveI : Fintype A := hA.fintype
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let f : A → A := fun x => ⟨c * x * c⁻¹, hcA x x.2⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  let σ : Equiv.Perm A := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hσ : ∀ (n : ℕ) (x : A), ((σ ^ n) x : X) = c ^ n * x * (c ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      change c ^ n * (c * (x : X) * c⁻¹) * (c ^ n)⁻¹ = _
      rw [pow_succ]
      group
  have hσ5 : σ ^ 5 ^ 1 = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [pow_one, hσ 5 x, hc5 x x.2]
    rfl
  by_contra hdvd
  have hcard : ¬ 5 ∣ Fintype.card A := by
    rwa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ5
  exact hfree x x.2 (congrArg Subtype.val hx)

end Counting

section OrderFive

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {Q : QuadraticForm (ZMod 2) W}

theorem exists_order_five_stab (hV : finrank (ZMod 2) W = 6) (hQ : Q.polarBilin.Nondegenerate)
    {a : W} (ha0 : a ≠ 0) (ha : Q a = 0) (h27 : {v : W | v ≠ 0 ∧ Q v = 0}.ncard = 27) :
    ∃ c ∈ omegaGroup Q hQ, c a = a ∧ c ^ 5 = 1 ∧ c ≠ 1 := by
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have : Finite (W ≃ₗ[ZMod 2] W) := O62.finite_linearEquiv
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set Ω := omegaGroup Q hQ with hΩ
  have horb : MulAction.orbit Ω a = {v : W | v ≠ 0 ∧ Q v = 0} := by
    ext v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨?_, ?_⟩
      · intro h
        apply ha0
        exact (LinearEquiv.map_eq_zero_iff (x : W ≃ₗ[ZMod 2] W)).mp h
      · have := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
          (omegaGroup_le Q hQ x.2) a
        exact this.trans ha
    · rintro ⟨hv0, hv⟩
      obtain ⟨x, hx, hxa⟩ := O62.exists_mem_omegaGroup_apply_eq hQ (by omega) ha0 hv0
        (by rw [ha, hv])
      exact ⟨⟨x, hx⟩, hxa⟩
  have key : Nat.card (MulAction.orbit Ω a) * Nat.card (MulAction.stabilizer Ω a) =
      Nat.card Ω := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Ω a)
  have horbcard : Nat.card (MulAction.orbit Ω a) = 27 := by
    rw [horb, Nat.card_coe_set_eq]
    exact h27
  have h5 : 5 ∣ Nat.card Ω := by
    rcases O62.card_omegaGroup hV hQ with h | h <;> rw [h] <;> norm_num
  rw [horbcard] at key
  have h5' : 5 ∣ Nat.card (MulAction.stabilizer Ω a) :=
    (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 5 27) (key ▸ h5))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := MulAction.stabilizer Ω a) 5 h5'
  refine ⟨((x : Ω) : W ≃ₗ[ZMod 2] W), (x : Ω).2, ?_, ?_, ?_⟩
  · have := x.2
    rw [MulAction.mem_stabilizer_iff] at this
    exact this
  · have h1 : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have := congrArg (fun y : MulAction.stabilizer Ω a => ((y : Ω) : W ≃ₗ[ZMod 2] W)) h1
    simpa using this
  · intro h1
    have : x = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hx
    omega

theorem eq_one_of_conj_fixed (hV : finrank (ZMod 2) W = 6) (hQ : Q.polarBilin.Nondegenerate)
    {a : W} (ha0 : a ≠ 0) (ha : Q a = 0) {c : W ≃ₗ[ZMod 2] W}
    (hcO : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hca : c a = a) (hc5 : c ^ 5 = 1)
    (hc1 : c ≠ 1) :
    ∀ u ∈ pointRadical Q a, c * u * c⁻¹ = u → u = 1 := by
  classical
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have : Finite (W ≃ₗ[ZMod 2] W) := O62.finite_linearEquiv
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set N := pointRadical Q a with hN
  haveI : Fintype N := Fintype.ofFinite N
  have hNcard : Nat.card N = 16 := by
    rw [card_pointRadical hQ ha0 ha, hV]
    norm_num
  have hconj : ∀ {d : W ≃ₗ[ZMod 2] W}, d ∈ TauCeti.QuadraticMap.orthogonalGroup Q → d a = a →
      ∀ u ∈ N, d * u * d⁻¹ ∈ N := by
    intro d hd hda u hu
    have := conj_mem_pointRadical hd hu
    rwa [hda] at this
  have hcinv : c⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := inv_mem hcO
  have hcinva : c⁻¹ a = a := by
    conv_lhs => rw [← hca]
    exact LinearEquiv.symm_apply_apply c a
  have hnorm : c ∈ normalizer (N : Set (W ≃ₗ[ZMod 2] W)) := by
    rw [mem_normalizer_iff]
    intro u
    refine ⟨fun hu => hconj hcO hca u hu, fun hu => ?_⟩
    have := hconj hcinv hcinva _ hu
    simpa [mul_assoc] using this
  set φ : MulAut N := N.normalizerMonoidHom ⟨c, hnorm⟩ with hφdef
  have hφ : ∀ u : N, ((φ u : N) : W ≃ₗ[ZMod 2] W) = c * u * c⁻¹ := fun u => rfl
  have hφ5 : φ ^ 5 = 1 := by
    rw [hφdef, ← map_pow]
    have : (⟨c, hnorm⟩ : normalizer (N : Set (W ≃ₗ[ZMod 2] W))) ^ 5 = 1 :=
      Subtype.ext (by simpa using hc5)
    rw [this, map_one]
  set σ : Equiv.Perm N := MulAut.toPerm N φ with hσdef
  have hσ5 : σ ^ 5 ^ 1 = 1 := by
    rw [pow_one, hσdef, ← map_pow, hφ5, map_one]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ5
  set F : Subgroup N := MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id N) with hF
  have hFmem : ∀ u : N, u ∈ F ↔ c * (u : W ≃ₗ[ZMod 2] W) * c⁻¹ = u := by
    intro u
    change φ u = u ↔ _
    rw [← Subtype.coe_inj, hφ]
  have hFcard : Nat.card F = σ.supportᶜ.card := by
    have h1 : σ.supportᶜ = Finset.univ.filter (fun u => σ u = u) := by
      ext u
      simp [Equiv.Perm.mem_support]
    rw [h1, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => Iff.rfl)
  have hFdvd : Nat.card F ∣ 16 := hNcard ▸ Subgroup.card_subgroup_dvd_card F
  have hmod' : Nat.card F ≡ 16 [MOD 5] := by
    rw [hFcard, ← hNcard, Nat.card_eq_fintype_card]
    exact hmod
  have hF16 : Nat.card F = 1 ∨ Nat.card F = 16 := by
    have hle : Nat.card F ≤ 16 := Nat.le_of_dvd (by norm_num) hFdvd
    unfold Nat.ModEq at hmod'
    generalize Nat.card F = m at hFdvd hmod' hle ⊢
    interval_cases m <;> omega
  rcases hF16 with h1 | h16
  · have hbot : F = ⊥ := Subgroup.eq_bot_of_card_eq F h1
    intro u hu hfix
    have : (⟨u, hu⟩ : N) ∈ F := (hFmem _).mpr hfix
    rw [hbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (h16.trans hNcard.symm)
    have hall : ∀ u ∈ N, c * u * c⁻¹ = u := fun u hu => by
      have : (⟨u, hu⟩ : N) ∈ F := by rw [htop]; exact Subgroup.mem_top _
      exact (hFmem _).mp this
    have hpolc : ∀ v w, polar Q (c v) (c w) = polar Q v w := fun v w =>
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hcO v w
    have hcN : c ∈ N := by
      refine ⟨hcO, hca, fun x hx => ?_, fun v => ?_⟩
      · have hcx : polar Q a (c x) = 0 := by rw [← hca, hpolc, hx]
        have h1 := hall _ (eichler_mem_pointRadical ha hx)
        rw [eichler_conj hcO, hca] at h1
        rcases (eichler_eq_iff hQ ha0 ha hcx hx).mp h1 with h2 | h2
        · rw [h2, sub_self]
          exact Submodule.zero_mem _
        · rw [h2, add_sub_cancel_left]
          exact Submodule.mem_span_singleton_self a
      · rw [polar_sub_right, ← hca, hpolc, hca, sub_self]
    obtain ⟨w, hw, hcw⟩ := (mem_pointRadical_iff hQ ha0 ha).mp hcN
    have hc2 : c * c = 1 := by
      rw [hcw, eichler_mul hw hw, vec_add_self, eichler_zero_right]
    apply hc1
    have hc2' : c ^ 2 = 1 := by rw [pow_two]; exact hc2
    calc c = (c ^ 2) ^ 2 * c := by rw [hc2']; simp
      _ = c ^ 5 := by rw [← pow_mul, ← pow_succ]
      _ = 1 := hc5

theorem exists_order_five (hV : finrank (ZMod 2) W = 6) (hQ : Q.polarBilin.Nondegenerate)
    {a : W} (ha0 : a ≠ 0) (ha : Q a = 0) (h27 : {v : W | v ≠ 0 ∧ Q v = 0}.ncard = 27) :
    ∃ c ∈ omegaGroup Q hQ, c a = a ∧ c ^ 5 = 1 ∧ c ≠ 1 ∧
      ∀ u ∈ pointRadical Q a, c * u * c⁻¹ = u → u = 1 := by
  obtain ⟨c, hcΩ, hca, hc5, hc1⟩ := exists_order_five_stab hV hQ ha0 ha h27
  exact ⟨c, hcΩ, hca, hc5, hc1,
    eq_one_of_conj_fixed hV hQ ha0 ha (omegaGroup_le Q hQ hcΩ) hca hc5 hc1⟩

end OrderFive

section DeltaCount

theorem ncard_conj_orbit {X : Type*} [Group X] [Finite X] (N : Subgroup X) (t : X) :
    {x : X | ∃ n ∈ N, x = n * t * n⁻¹}.ncard =
      ((centralizer ({t} : Set X)).subgroupOf N).index := by
  set Hs := (centralizer ({t} : Set X)).subgroupOf N with hHs
  have key : ∀ a b : N, a⁻¹ * b ∈ Hs ↔ (a : X) * t * (a : X)⁻¹ = (b : X) * t * (b : X)⁻¹ := by
    intro a b
    rw [hHs, mem_subgroupOf, mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro h
      calc (a : X) * t * (a : X)⁻¹ = (a : X) * (t * ((a : X)⁻¹ * b)) * (b : X)⁻¹ := by group
        _ = (a : X) * (((a : X)⁻¹ * b) * t) * (b : X)⁻¹ := by rw [← h]
        _ = (b : X) * t * (b : X)⁻¹ := by group
    · intro h
      calc ((a : X)⁻¹ * b) * t = (a : X)⁻¹ * ((b : X) * t * (b : X)⁻¹) * b := by group
        _ = (a : X)⁻¹ * ((a : X) * t * (a : X)⁻¹) * b := by rw [h]
        _ = t * ((a : X)⁻¹ * b) := by group
  let f : N ⧸ Hs → X := fun q => Quotient.liftOn' q (fun n : N => (n : X) * t * (n : X)⁻¹)
    (fun a b hab => (key a b).mp (by rwa [QuotientGroup.leftRel_apply] at hab))
  have hinj : Function.Injective f := by
    intro q₁ q₂
    induction q₁ using Quotient.inductionOn'
    induction q₂ using Quotient.inductionOn'
    rename_i a b
    intro h
    exact Quotient.sound' ((QuotientGroup.leftRel_apply).mpr ((key a b).mpr h))
  have hrange : Set.range f = {x : X | ∃ n ∈ N, x = n * t * n⁻¹} := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      induction q using Quotient.inductionOn'
      rename_i a
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨Quotient.mk'' ⟨n, hn⟩, rfl⟩
  rw [← hrange, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
  rfl

theorem index_dvd_card_mulAut {X : Type*} [Group X] [Finite X] (L N : Subgroup X)
    (hNL : N ≤ normalizer (L : Set X)) {t : X} (ht : t ∈ L) :
    ((centralizer ({t} : Set X)).subgroupOf N).index ∣ Nat.card (MulAut L) := by
  set ψ : N →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hNL) with hψ
  have hker : ψ.ker ≤ (centralizer ({t} : Set X)).subgroupOf N := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    have h1 : ((ψ n ⟨t, ht⟩ : L) : X) = (n : X) * t * (n : X)⁻¹ := rfl
    rw [hn] at h1
    have h2 : t = (n : X) * t * (n : X)⁻¹ := h1
    calc (n : X) * t = ((n : X) * t * (n : X)⁻¹) * (n : X) := by group
      _ = t * (n : X) := by rw [← h2]
  refine (Subgroup.index_dvd_of_le hker).trans ?_
  rw [Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card _

theorem not_eleven_dvd_card_mulAut {L : Type*} [Group L] [Finite L]
    (hcomm : ∀ a b : L, a * b = b * a) (hsq : ∀ a : L, a ^ 2 = 1) (hcard : Nat.card L = 2 ^ 5) :
    ¬ 11 ∣ Nat.card (MulAut L) := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hsq hcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  simp [Fin.prod_univ_succ]

end DeltaCount

section Helpers

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem resL_eq_resV (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) {x : S.O}
    (hx : x ∈ S.Lbar g) :
    resL H.conj_mem ht ⟨x, hx⟩ = resV H.conj_mem t ⟨x, Lbar_le_Rbar ht hx⟩ :=
  LinearEquiv.ext fun _ => Subtype.ext rfl

theorem mem_zpowers_of_resL_eq_one (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hN : Nbar S g t = zpowers t) {x : S.O} (hx : x ∈ S.Lbar g)
    (h : resL H.conj_mem ht ⟨x, hx⟩ = 1) : x ∈ zpowers t := by
  rw [resL_eq_resV H ht hx, resV_eq_one_iff, hN] at h
  exact h

theorem Q_aV_eq_zero (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    {Q : QuadraticForm (ZMod 2) (Vt S g t)}
    (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht))) :
    Q (aV ht) = 0 :=
  (hsing _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩

theorem singular_eq_orbitOf (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    {Q : QuadraticForm (ZMod 2) (Vt S g t)}
    (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht))) :
    {v : Vt S g t | v ≠ 0 ∧ Q v = 0} = orbitOf (RmodN S g t) (aV ht) := by
  ext v
  constructor
  · rintro ⟨hv0, hv⟩
    exact (hsing v hv0).mp hv
  · intro hv
    have hv0 : v ≠ 0 := by
      obtain ⟨x, -, rfl⟩ := hv
      intro h
      exact aV_ne_zero H ht ((LinearEquiv.map_eq_zero_iff x).mp h)
    exact ⟨hv0, (hsing v hv0).mpr hv⟩

theorem resL_eq_one_or_eichler (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    {Q : QuadraticForm (ZMod 2) (Vt S g t)} {hQ : Q.polarBilin.Nondegenerate}
    (hX : RmodN S g t = omegaGroup Q hQ) (hE : LmodN S g t = pointRadical Q (aV ht))
    (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht)))
    {x : S.O} (hx : x ∈ S.Lbar g) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hth : t ∈ S.Lbar ((h : G) * g))
    (hxh : x ∈ S.Lbar ((h : G) * g)) (hne : bV hth ≠ aV ht) :
    resL H.conj_mem ht ⟨x, hx⟩ = 1 ∨
      resL H.conj_mem ht ⟨x, hx⟩ = eichler Q (aV ht) (bV hth) := by
  have h1 : resL H.conj_mem ht ⟨x, hx⟩ ∈ LmodN S g t := by
    rw [← range_resL H.conj_mem ht]
    exact ⟨_, rfl⟩
  have h2 : resL H.conj_mem ht ⟨x, hx⟩ ∈ LhmodN S g t h := by
    rw [resL_eq_resV H ht hx]
    exact resV_mem_LhmodN H.conj_mem hth hxh
  rw [hE] at h1
  rw [LhmodN_eq_pointRadical H ht hh hth hX hE] at h2
  exact S2.mem_pointRadical_inf_of_orthogonal hQ (aV_ne_zero H ht) (bV_ne_zero H hth)
    (Ne.symm hne) (Q_aV_eq_zero H ht hsing) ⟨h1, h2⟩

end Helpers

section Main

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

variable (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
include H hNo C ht ht1 hVQ hΩ hN h6

theorem exists_D {k : S.M} (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) :
    ∃ D : Submodule (ZMod 2) (Vt S g t), aV ht ∈ D ∧ 4 ≤ finrank (ZMod 2) D ∧
      (∀ d ∈ D, beta H C ht ht1 hVQ (aV ht) d = 0) ∧
      ∀ d ∈ D, (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d ∈ Vt S g t := by
  set e : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with he
  have hn := width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ
  have hdP := S.finrank_clSub_QG_inf_Qa H.conj_mem H.conj_ne C.card_QG_inf_Qa
  have hdPV := finrank_clSub_inf_Vt H C ht ht1 hVQ
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  have hxa := fix_of_mem_normalizer H hk
  have hPx : ∀ v ∈ P, e v ∈ P := fun v hv =>
    apply_mem_clSub_of_fix H.conj_mem H.conj_ne ⟨k, rfl⟩ hxa hv
  have hPmap : P.map e.toLinearMap = P := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq e P)
    rintro _ ⟨v, hv, rfl⟩
    exact hPx v hv
  set Y := (Vt S g t).map e.toLinearMap with hY
  have hPY : (P ⊓ Vt S g t).map e.toLinearMap = P ⊓ Y := by
    rw [Submodule.map_inf _ e.injective, hPmap]
  have h1 : finrank (ZMod 2) ↥(P ⊓ Y) = finrank (ZMod 2) ↥(P ⊓ Vt S g t) := by
    rw [← hPY, LinearEquiv.finrank_map_eq]
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ Vt S g t) (P ⊓ Y)
  have h3 : finrank (ZMod 2) ↥((P ⊓ Vt S g t) ⊔ (P ⊓ Y)) ≤ finrank (ZMod 2) P :=
    Submodule.finrank_mono (sup_le inf_le_left inf_le_left)
  have h4 : finrank (ZMod 2) ↥((P ⊓ Vt S g t) ⊓ (P ⊓ Y)) ≤
      finrank (ZMod 2) ↥(Vt S g t ⊓ (P ⊓ Y)) :=
    Submodule.finrank_mono fun v hv => ⟨hv.1.2, hv.2⟩
  set D : Submodule (ZMod 2) (Vt S g t) := (P ⊓ Y).comap (Vt S g t).subtype with hD
  have hdD : finrank (ZMod 2) D = finrank (ZMod 2) ↥(Vt S g t ⊓ (P ⊓ Y)) := by
    rw [← Submodule.finrank_map_subtype_eq, hD, Submodule.map_comap_subtype]
  refine ⟨D, ?_, by omega, ?_, ?_⟩
  · refine ⟨cl_mem_clSub_self H.conj_mem, ⟨aV ht, (aV ht).2, ?_⟩⟩
    exact hxa
  · intro d hd
    rw [beta_aV_eq_zero_iff H C ht ht1 hVQ]
    exact hd.1
  · intro d hd
    obtain ⟨v, hv, hvd⟩ := (show (d : S.Qt) ∈ Y from hd.2)
    rw [← hvd]
    change (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
      ∈ Vt S g t
    rw [inv_apply_apply_O]
    exact hv

theorem exists_base_of_singular (hCE : CentralExtInput.{0})
    {Q : QuadraticForm (ZMod 2) (Vt S g t)}
    (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht)))
    {k : S.M} {α : Vt S g t} (hα0 : α ≠ 0) (hQα : Q α = 0)
    (hinv : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) α ∈ Vt S g t) :
    ∃ (h : S.M) (_ : S.ρ h ∈ Rbar S g t) (hth : t ∈ S.Lbar ((h : G) * g)),
      bV hth = α ∧ S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar ((h : G) * g) := by
  have h67 := orbit67_of_omegaCase hCE H hNo C hΩ (by omega : 6 ≤ finrank (ZMod 2) (Vt S g t))
  have hαo := (hsing α hα0).mp hQα
  rw [mem_orbitOf_RmodN_iff H.conj_mem ht] at hαo
  obtain ⟨h₁, hh₁, hα⟩ := exists_of_mem_orbit hαo H.conj_mem
  have htk₁ := mem_Lbar_mul_of_mem_Rbar H ht hh₁
  have hα' : bV htk₁ = α := Subtype.ext (by rw [coe_bV]; exact hα.symm)
  refine ⟨h₁, hh₁, htk₁, hα', ?_⟩
  exact conj_mem_Lbar_of_inv_apply_mem H ht h67 k h₁ (hα ▸ hinv)

section ClaimA

variable {Q : QuadraticForm (ZMod 2) (Vt S g t)} {hQ : Q.polarBilin.Nondegenerate}
  (hpol : Q.polarBilin = beta H C ht ht1 hVQ) (hX : RmodN S g t = omegaGroup Q hQ)
  (hE : LmodN S g t = pointRadical Q (aV ht))
  (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht)))
include hpol hX hE hsing

theorem claimA (hCE : CentralExtInput.{0}) (hcount : CountSixStmt) {k : S.M}
    (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) :
    S.ρ k * t * (S.ρ k)⁻¹ = t ∨
      ({v : Vt S g t | v ≠ 0 ∧ Q v = 0}.ncard = 27 ∧
        ∃ α : Vt S g t, α ≠ 0 ∧ α ≠ aV ht ∧ Q α = 0 ∧ polar Q (aV ht) α = 0 ∧
          ∃ hx : S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g,
            resL H.conj_mem ht ⟨_, hx⟩ = eichler Q (aV ht) α) := by
  by_cases hteq : S.ρ k * t * (S.ρ k)⁻¹ = t
  · exact Or.inl hteq
  right
  have ht' : S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g := (mem_normalizer_iff.mp hk t).mp ht
  have ht'1 : S.ρ k * t * (S.ρ k)⁻¹ ≠ 1 := by
    intro h
    apply ht1
    have := congrArg (fun y => (S.ρ k)⁻¹ * y * S.ρ k) h
    simpa [mul_assoc] using this
  have hnot : S.ρ k * t * (S.ρ k)⁻¹ ∉ zpowers t := by
    rw [mem_zpowers_iff_of_mem_Lbar H ht]
    rintro (h | h)
    · exact ht'1 h
    · exact hteq h
  have hres1 : resL H.conj_mem ht ⟨_, ht'⟩ ≠ 1 := fun h =>
    hnot (mem_zpowers_of_resL_eq_one H ht hN ht' h)
  obtain ⟨D, haD, hD4, hDperp, hDinv⟩ := exists_D H hNo C ht ht1 hVQ hΩ hN h6 hk
  have hQa : Q (aV ht) = 0 := Q_aV_eq_zero H ht hsing
  have hDpolar : ∀ d ∈ D, polar Q (aV ht) d = 0 := by
    intro d hd
    have := hDperp d hd
    rw [← hpol, polarBilin_apply_apply] at this
    exact this
  have hkey : ∀ α ∈ D, Q α = 0 → α ≠ 0 → α ≠ aV ht →
      resL H.conj_mem ht ⟨_, ht'⟩ = eichler Q (aV ht) α := by
    intro α hαD hQα hα0 hαa
    obtain ⟨h, hh, hth, hbα, hmem⟩ :=
      exists_base_of_singular H hNo C ht ht1 hVQ hΩ hN h6 hCE hsing hα0 hQα (hDinv α hαD)
    have := (resL_eq_one_or_eichler H ht hX hE hsing ht' hh hth hmem
      (by rw [hbα]; exact hαa)).resolve_left hres1
    rwa [hbα] at this
  obtain ⟨⟨α₀, hα₀D, hα₀Q, hα₀0, hα₀a⟩, hcnt⟩ :=
    (hcount (Vt S g t) Q h6 hQ (aV ht) (aV_ne_zero H ht) hQa).1 D haD hDpolar hD4
  refine ⟨hcnt ?_, α₀, hα₀0, hα₀a, hα₀Q, hDpolar α₀ hα₀D, ht',
    hkey α₀ hα₀D hα₀Q hα₀0 hα₀a⟩
  intro x hx y hy hQx hQy hx0 hxa hy0 hya
  have h1 := hkey x hx hQx hx0 hxa
  have h2 := hkey y hy hQy hy0 hya
  exact (eichler_eq_iff hQ (aV_ne_zero H ht) hQa (hDpolar x hx) (hDpolar y hy)).mp
    (h1.symm.trans h2)

end ClaimA

end Main

section DeltaS

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem ncard_Delta_eq_index (S : Setting G) (g : G) (t : S.O) :
    (Delta S g t).ncard = ((centralizer ({t} : Set S.O)).subgroupOf (NLbar S g)).index :=
  ncard_conj_orbit (NLbar S g) t

theorem not_eleven_dvd_ncard_Delta (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (hw : S.width = 6) : ¬ 11 ∣ (Delta S g t).ncard := by
  intro h11
  rw [ncard_Delta_eq_index] at h11
  have hdvd := index_dvd_card_mulAut (S.Lbar g) (NLbar S g) inf_le_right ht
  refine not_eleven_dvd_card_mulAut (L := S.Lbar g) (fun a b => Subtype.ext ?_)
    (fun a => ?_) ?_ (h11.trans hdvd)
  · exact Lbar_comm S H.conj_mem a.2 b.2
  · rw [pow_two]
    exact Subtype.ext (mul_self_of_mem_Lbar S H.conj_mem a.2)
  · rw [C.card_Lbar, hw]

theorem odd_ncard_Delta (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (h2c : TwoCentralBar S t) : Odd (Delta S g t).ncard := by
  obtain ⟨T, hT, hTc⟩ := h2c
  set K : Subgroup S.O := S.Mbar ⊓ centralizer ({t} : Set S.O) with hK
  have hTK : T ≤ K := fun x hx =>
    ⟨hT.le hx, mem_centralizer_singleton_iff.mpr (hTc x hx)⟩
  have hLK : S.Lbar g ≤ K := fun x hx =>
    ⟨S.Lbar_le_Mbar g hx, mem_centralizer_singleton_iff.mpr (Lbar_comm S H.conj_mem hx ht)⟩
  obtain ⟨T₁, hT₁, hLT₁⟩ := S5.exists_isSylowTwoIn_ge hLK (S4.isPGroup_Lbar S H.conj_mem)
  have hT₁M : T₁ ≤ S.Mbar := hT₁.le.trans inf_le_left
  have hT₁N : T₁ ≤ NLbar S g :=
    le_inf hT₁M (le_normalizer_of_weaklyClosed C.weaklyClosed hT₁.isPGroup hT₁M hLT₁)
  have hmulT := relIndex_mul_relIndex T K S.Mbar hTK inf_le_left
  have hK1 : ¬ 2 ∣ K.relIndex S.Mbar := fun h2 =>
    hT.not_dvd (hmulT ▸ Dvd.dvd.mul_left h2 _)
  have hmulT₁ := relIndex_mul_relIndex T₁ K S.Mbar hT₁.le inf_le_left
  have hodd1 : ¬ 2 ∣ T₁.relIndex S.Mbar := by
    rw [← hmulT₁]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hT₁.not_dvd h
    · exact hK1 h
  have hmulN := relIndex_mul_relIndex T₁ (NLbar S g) S.Mbar hT₁N inf_le_left
  have hodd2 : ¬ 2 ∣ T₁.relIndex (NLbar S g) := fun h2 =>
    hodd1 (hmulN ▸ Dvd.dvd.mul_right h2 _)
  have hle : T₁.subgroupOf (NLbar S g) ≤
      (centralizer ({t} : Set S.O)).subgroupOf (NLbar S g) := by
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact (hT₁.le hx).2
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [ncard_Delta_eq_index, Nat.odd_iff]
  have : ¬ 2 ∣ ((centralizer ({t} : Set S.O)).subgroupOf (NLbar S g)).index := fun h2 =>
    hodd2 (h2.trans hdvd)
  omega

end DeltaS

section FiveElement

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_five_element (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hN : Nbar S g t = zpowers t) (h6 : finrank (ZMod 2) (Vt S g t) = 6)
    {Q : QuadraticForm (ZMod 2) (Vt S g t)} {hQ : Q.polarBilin.Nondegenerate}
    (hX : RmodN S g t = omegaGroup Q hQ) (hE : LmodN S g t = pointRadical Q (aV ht))
    (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht)))
    (h27 : {v : Vt S g t | v ≠ 0 ∧ Q v = 0}.ncard = 27) :
    ∃ c ∈ Rbar S g t, c ∈ normalizer (S.Lbar g : Set S.O) ∧
      (∀ x ∈ S.Lbar g, c ^ 5 * x * (c ^ 5)⁻¹ = x) ∧
      ∀ x ∈ S.Lbar g, c * x * c⁻¹ = x → x ∈ zpowers t := by
  have hQa := Q_aV_eq_zero H ht hsing
  obtain ⟨cb, hcbΩ, hcba, hcb5, hcb1, hfix⟩ :=
    exists_order_five h6 hQ (aV_ne_zero H ht) hQa h27
  have hcbR : cb ∈ RmodN S g t := hX ▸ hcbΩ
  obtain ⟨r, hr, hrcb⟩ := hcbR
  have hrv : resV H.conj_mem t ⟨r, hr⟩ = cb :=
    LinearEquiv.ext fun v => Subtype.ext (hrcb v).symm
  have hra : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
    have := hrcb (aV ht)
    rw [hcba] at this
    exact this.symm
  have hrN : r ∈ normalizer (S.Lbar g : Set S.O) := by
    have := mem_normalizer_of_fix (S := S) (g := g) (h := 1) H.conj_mem H.conj_ne
      (Rbar_le_Mbar hr) (by simpa using hra)
    simpa using this
  refine ⟨r, hr, hrN, ?_, ?_⟩
  · intro x hx
    have h5R : r ^ 5 ∈ Rbar S g t := pow_mem hr 5
    have h5 : resV H.conj_mem t ⟨r ^ 5, h5R⟩ = 1 := by
      have : (⟨r ^ 5, h5R⟩ : Rbar S g t) = ⟨r, hr⟩ ^ 5 := Subtype.ext (by simp)
      rw [this, map_pow, hrv, hcb5]
    have h5N : r ^ 5 ∈ Nbar S g t := (resV_eq_one_iff H.conj_mem ⟨r ^ 5, h5R⟩).mp h5
    rw [hN] at h5N
    have h5L : r ^ 5 ∈ S.Lbar g := (zpowers_le.mpr ht) h5N
    rw [Lbar_comm S H.conj_mem h5L hx]
    group
  · intro x hx hfixx
    have hxR : x ∈ Rbar S g t := Lbar_le_Rbar ht hx
    have hu : resL H.conj_mem ht ⟨x, hx⟩ ∈ pointRadical Q (aV ht) := by
      rw [← hE, ← range_resL H.conj_mem ht]
      exact ⟨_, rfl⟩
    have e : resV H.conj_mem t (⟨r, hr⟩ * ⟨x, hxR⟩ * ⟨r, hr⟩⁻¹) =
        resV H.conj_mem t ⟨x, hxR⟩ := by
      congr 1
      exact Subtype.ext (by simpa using hfixx)
    rw [map_mul, map_mul, map_inv, hrv] at e
    rw [← resL_eq_resV H ht hx] at e
    exact mem_zpowers_of_resL_eq_one H ht hN hx (hfix _ hu e)

end FiveElement

theorem strongClosed_of_normalizer {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}
    (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hnorm : ∀ n ∈ NLbar S g, n * t * n⁻¹ = t) :
    ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t := by
  intro x hx hxt
  have hcomm : ∀ l ∈ S.Lbar g, t * l = l * t := fun l hl => Lbar_comm S H.conj_mem ht hl
  have hcomm' : ∀ l ∈ S.Lbar g, x * t * x⁻¹ * l = l * (x * t * x⁻¹) := fun l hl =>
    Lbar_comm S H.conj_mem hxt hl
  obtain ⟨n, hnM, hnN, hn⟩ := S5.exists_mem_normalizer_conj H C hx hcomm hcomm'
  rw [hn]
  exact hnorm n ⟨hnM, hnN⟩

theorem Delta_eq_class_inter {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}
    (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) :
    Delta S g t = {x | x ∈ S.Lbar g ∧ ∃ m ∈ S.Mbar, x = m * t * m⁻¹} := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨(mem_normalizer_iff.mp hn.2 t).mp ht, n, hn.1, rfl⟩
  · rintro ⟨hxL, m, hm, rfl⟩
    have hcomm : ∀ l ∈ S.Lbar g, t * l = l * t := fun l hl => Lbar_comm S H.conj_mem ht hl
    have hcomm' : ∀ l ∈ S.Lbar g, m * t * m⁻¹ * l = l * (m * t * m⁻¹) := fun l hl =>
      Lbar_comm S H.conj_mem hxL hl
    obtain ⟨n, hnM, hnN, hn⟩ := S5.exists_mem_normalizer_conj H C hm hcomm hcomm'
    exact ⟨n, ⟨hnM, hnN⟩, hn⟩

end CaseIClosure

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem dichotomy_six (hCE : CentralExtInput.{0}) (hcount : CountSixStmt)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (hN : Nbar S g t = zpowers t) (h6 : finrank (ZMod 2) (Vt S g t) = 6) :
    (∀ n ∈ NLbar S g, n * t * n⁻¹ = t) ∨
      ((Delta S g t).ncard = 6 ∧ (orbitOf (RmodN S g t) (aV ht)).ncard = 27) := by
  classical
  by_cases hall : ∀ n ∈ NLbar S g, n * t * n⁻¹ = t
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨n₀, hn₀, hn₀t⟩ := hall
  obtain ⟨Q, hQ, hpol, hX, hE, hsing⟩ := hΩ.exists_form
  have hQa : Q (aV ht) = 0 := CaseIClosure.Q_aV_eq_zero H ht hsing
  have hw : S.width = 6 := by
    rw [width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ, h6]
  have hClaim : ∀ n ∈ NLbar S g, n * t * n⁻¹ = t ∨
      ({v : Vt S g t | v ≠ 0 ∧ Q v = 0}.ncard = 27 ∧
        ∃ α : Vt S g t, α ≠ 0 ∧ α ≠ aV ht ∧ Q α = 0 ∧ polar Q (aV ht) α = 0 ∧
          ∃ hx : n * t * n⁻¹ ∈ S.Lbar g,
            resL H.conj_mem ht ⟨_, hx⟩ = eichler Q (aV ht) α) := by
    intro n hn
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hn.1
    exact CaseIClosure.claimA H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hCE hcount hn.2
  have h27 : {v : Vt S g t | v ≠ 0 ∧ Q v = 0}.ncard = 27 := by
    rcases hClaim n₀ hn₀ with h | ⟨h27, _⟩
    · exact absurd h hn₀t
    · exact h27
  refine ⟨?_, by rw [← CaseIClosure.singular_eq_orbitOf H ht hsing]; exact h27⟩
  set Δ' : Set S.O := Delta S g t \ {t} with hΔ'
  have hΔ'L : ∀ x ∈ Δ', x ∈ S.Lbar g := by
    rintro x ⟨⟨n, hn, rfl⟩, -⟩
    exact (mem_normalizer_iff.mp hn.2 t).mp ht
  set Sg : Set (Vt S g t) := {x | polar Q (aV ht) x = 0 ∧ Q x = 0 ∧ x ≠ 0 ∧ x ≠ aV ht} with hSg
  set φ : S.O → (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := fun x =>
    if hx : x ∈ S.Lbar g then resL H.conj_mem ht ⟨x, hx⟩ else 1 with hφdef
  have hφ : ∀ (x : S.O) (hx : x ∈ S.Lbar g), φ x = resL H.conj_mem ht ⟨x, hx⟩ := fun x hx => by
    simp only [hφdef, hx, ↓reduceDIte]
  have hmap : ∀ x ∈ Δ', φ x ∈ eichler Q (aV ht) '' Sg := by
    rintro x ⟨⟨n, hn, rfl⟩, hxt⟩
    rcases hClaim n hn with h | ⟨-, α, hα0, hαa, hQα, hpolα, hx', hres⟩
    · exact absurd (Set.mem_singleton_iff.mpr h) hxt
    · exact ⟨α, ⟨hpolα, hQα, hα0, hαa⟩, by rw [hφ _ hx', hres]⟩
  have hfib : ∀ x₁ ∈ Δ', ∀ x₂ ∈ Δ', φ x₁ = φ x₂ → x₂ = x₁ ∨ x₂ = x₁ * t := by
    intro x₁ hx₁ x₂ hx₂ h
    have h1 := hΔ'L x₁ hx₁
    have h2 := hΔ'L x₂ hx₂
    rw [hφ x₁ h1, hφ x₂ h2] at h
    have h3 : resL H.conj_mem ht (⟨x₁, h1⟩⁻¹ * ⟨x₂, h2⟩) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have h4 := CaseIClosure.mem_zpowers_of_resL_eq_one H ht hN (mul_mem (inv_mem h1) h2) h3
    rw [mem_zpowers_iff_of_mem_Lbar H ht] at h4
    rcases h4 with h4 | h4
    · left
      calc x₂ = x₁ * (x₁⁻¹ * x₂) := by group
        _ = x₁ := by rw [h4, mul_one]
    · right
      calc x₂ = x₁ * (x₁⁻¹ * x₂) := by group
        _ = x₁ * t := by rw [h4]
  have hcard10 : Sg.ncard = 10 :=
    (hcount _ Q h6 hQ (aV ht) (aV_ne_zero H ht) hQa).2 h27
  have hbound : Δ'.ncard ≤ 10 := by
    have h1 := CaseIClosure.ncard_le_two_mul (Set.toFinite Δ') (Set.toFinite _) φ
      (fun x => x * t) hmap hfib
    have h2 : (eichler Q (aV ht) '' Sg).ncard ≤ 5 :=
      CaseIClosure.ncard_eichler_image_le (aV_ne_zero H ht) hQa hcard10
    omega
  obtain ⟨c, hcR, hcN, hc5, hcfix⟩ :=
    CaseIClosure.exists_five_element H ht hN h6 hX hE hsing h27
  have hcNL : c ∈ NLbar S g := ⟨Rbar_le_Mbar hcR, hcN⟩
  have hct : c * t = t * c := commute_of_mem_Rbar H.conj_mem hcR
  have hcΔ' : ∀ x ∈ Δ', c * x * c⁻¹ ∈ Δ' := by
    rintro x ⟨⟨n, hn, rfl⟩, hxt⟩
    refine ⟨⟨c * n, mul_mem hcNL hn, by group⟩, fun h => hxt ?_⟩
    rw [Set.mem_singleton_iff] at h ⊢
    calc n * t * n⁻¹ = c⁻¹ * (c * (n * t * n⁻¹) * c⁻¹) * c := by group
      _ = c⁻¹ * t * c := by rw [h]
      _ = t := by rw [mul_assoc, ← hct, inv_mul_cancel_left]
  have hfree : ∀ x ∈ Δ', c * x * c⁻¹ ≠ x := by
    rintro x ⟨⟨n, hn, rfl⟩, hxt⟩ hfx
    have hxL : n * t * n⁻¹ ∈ S.Lbar g := (mem_normalizer_iff.mp hn.2 t).mp ht
    have hz := hcfix _ hxL hfx
    rw [mem_zpowers_iff_of_mem_Lbar H ht] at hz
    rcases hz with h | h
    · apply ht1
      have := congrArg (fun y => n⁻¹ * y * n) h
      simpa [mul_assoc] using this
    · exact hxt (Set.mem_singleton_iff.mpr h)
  have hdvd5 : 5 ∣ Δ'.ncard :=
    CaseIClosure.five_dvd_ncard (Set.toFinite _) (fun x hx => hc5 x (hΔ'L x hx)) hcΔ' hfree
  have hne : Δ'.Nonempty :=
    ⟨n₀ * t * n₀⁻¹, ⟨n₀, hn₀, rfl⟩, fun h => hn₀t (Set.mem_singleton_iff.mp h)⟩
  have hpos : 0 < Δ'.ncard := (Set.ncard_pos (Set.toFinite _)).mpr hne
  have hΔcard : Δ'.ncard + 1 = (Delta S g t).ncard :=
    Set.ncard_sdiff_singleton_add_one (mem_Delta_self S g t) (Set.toFinite _)
  have h11 := CaseIClosure.not_eleven_dvd_ncard_Delta H C ht hw
  have h510 : Δ'.ncard = 5 ∨ Δ'.ncard = 10 := by omega
  rcases h510 with h | h
  · omega
  · exfalso
    apply h11
    rw [← hΔcard, h]

theorem strongClosed_six (hCE : CentralExtInput.{0}) (hcount : CountSixStmt)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (hN : Nbar S g t = zpowers t) (h6 : finrank (ZMod 2) (Vt S g t) = 6)
    (h2c : TwoCentralBar S t) :
    ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t := by
  rcases dichotomy_six hCE hcount H hNo C ht ht1 hVQ hΩ hN h6 with h | ⟨h6', -⟩
  · exact CaseIClosure.strongClosed_of_normalizer H C ht h
  · exfalso
    have hodd := CaseIClosure.odd_ncard_Delta H C ht h2c
    rw [h6', Nat.odd_iff] at hodd
    omega

theorem strongClosed_or_delta_six (hCE : CentralExtInput.{0}) (hcount : CountSixStmt)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (hN : Nbar S g t = zpowers t) (h6 : finrank (ZMod 2) (Vt S g t) = 6) :
    (∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t) ∨
      ({x | x ∈ S.Lbar g ∧ ∃ m ∈ S.Mbar, x = m * t * m⁻¹}.ncard = 6 ∧
        (orbitOf (RmodN S g t) (aV ht)).ncard = 27) := by
  rcases dichotomy_six hCE hcount H hNo C ht ht1 hVQ hΩ hN h6 with h | h
  · exact Or.inl (CaseIClosure.strongClosed_of_normalizer H C ht h)
  · rw [← CaseIClosure.Delta_eq_class_inter H C ht]
    exact Or.inr h

end CFSG.GF2Type.Smith1979
