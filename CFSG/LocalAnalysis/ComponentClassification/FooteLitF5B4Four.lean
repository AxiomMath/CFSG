module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Tools
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Core

public section

namespace CFSG.ComponentClassification.FooteLit.F5

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.Asc76X
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_of_mul_self {E : Subgroup G} (h : ∀ x ∈ E, x * x = 1) :
    Open.IsElemAbelian 2 E := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => by rw [sq]; exact h x hx⟩
  have ha : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (h a a.2)
  have hb : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right (h b b.2)
  have hab : ((a : G) * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (h _ (E.mul_mem a.2 b.2))
  change (a : G) * b = b * a
  rw [← hab, mul_inv_rev, ha, hb]

omit [Finite G] in
theorem isPGroup_of_mul_self {E : Subgroup G} (h : ∀ x ∈ E, x * x = 1) : IsPGroup 2 E :=
  fun x => ⟨1, Subtype.ext (by rw [pow_one, coe_pow, sq, coe_one]; exact h x x.2)⟩

omit [Finite G] in
theorem mul_self_eq_one_of_dihedral_four {D : Subgroup G}
    (hD : AschbacherTheorem3.IsDihedralTwoGroup D) (h4 : Nat.card D = 4) :
    ∀ x ∈ D, x * x = 1 := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hD
  have hcard : Nat.card D = 2 * 2 ^ (n - 1) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hn2 : n - 1 = 1 := by
    rw [h4] at hcard
    have h2 : 2 ^ (n - 1) = 2 ^ 1 := by omega
    exact Nat.pow_right_injective le_rfl h2
  obtain rfl : n = 2 := by omega
  have key : ∀ y : DihedralGroup 2, y * y = 1 := by decide
  intro x hx
  have h1 : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 := key _
  rw [← map_mul, map_eq_one_iff _ e.injective] at h1
  exact congrArg Subtype.val h1

omit [Finite G] in
theorem conj_mem_of_mem_normalizer {D : Subgroup G} (hD : ∀ x ∈ D, x * x = 1)
    (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d)
    {d : G} (hd : d ∈ D) {g : G} (hg : g⁻¹ * d * g ∈ normalizer (D : Set G)) :
    g⁻¹ * d * g ∈ D := by
  by_cases hd1 : d = 1
  · rw [hd1, mul_one, inv_mul_cancel]
    exact one_mem _
  by_contra hx
  have hd2 : orderOf d = 2 := orderOf_eq_prime (by rw [sq]; exact hD d hd) hd1
  have hx2 : orderOf (g⁻¹ * d * g) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) d
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, hd2]
  exact hcl _ hg hx hx2 d hd hd2 g⁻¹ (by group)

theorem le_normalizer_of_involutionClosed {D S : Subgroup G} (hD : ∀ x ∈ D, x * x = 1)
    (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d)
    (hS : IsPGroup 2 S) (hDS : D ≤ S) : S ≤ normalizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hle
  set H := S ⊓ normalizer (D : Set G) with hH
  have hlt : H < S := lt_of_le_of_ne inf_le_left fun h => hle (h ▸ inf_le_right)
  obtain ⟨y, hyS, hyH, hyN⟩ := exists_mem_normalizer_of_lt hS hlt
  apply hyH
  refine mem_inf.mpr ⟨hyS, ?_⟩
  have hsub : ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
    intro d hd
    have hdH : d ∈ H := mem_inf.mpr ⟨hDS hd, le_normalizer hd⟩
    have h1 : y * d * y⁻¹ ∈ H := (mem_normalizer_iff.mp hyN d).mp hdH
    have h2 := conj_mem_of_mem_normalizer hD hcl hd (g := y⁻¹)
      (by rw [inv_inv]; exact (mem_inf.mp h1).2)
    rwa [inv_inv] at h2
  have hmap : D.map (MulAut.conj y).toMonoidHom = D := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj y).injective).ge
    rintro _ ⟨d, hd, rfl⟩
    exact hsub d hd
  exact mem_normalizer_iff_map_conj_eq.mpr hmap

theorem card_le_four_of_quotient_psu3 {M : Type} [Group M] [Finite M]
    (e : M ⧸ Assembly.oddCore M ≃* Open.PSU3 2 2) {E : Subgroup M} (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := Assembly.oddCore M
  have hOodd : Odd (Nat.card O) := CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  set f : E →* M ⧸ O := (QuotientGroup.mk' O).comp E.subtype with hf
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have h1 : orderOf (x : M) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hE x x.2)
    have h2 : orderOf (x : M) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hx
    have h3 : orderOf (x : M) = 1 := by
      have h4 := Nat.dvd_gcd h1 h2
      rwa [(Nat.coprime_two_left.mpr hOodd).gcd_eq_one, Nat.dvd_one] at h4
    exact mem_bot.mpr (Subtype.ext (orderOf_eq_one_iff.mp h3))
  set E' := f.range
  have hcard : Nat.card E' = Nat.card E := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hE' : ∀ y ∈ E', y ^ 2 = 1 := by
    rintro _ ⟨x, rfl⟩
    have hx2 : x ^ 2 = 1 := Subtype.ext (by rw [coe_pow, sq, coe_one]; exact hE x x.2)
    rw [← map_pow, hx2, map_one]
  have hE'2 : IsPGroup 2 E' := by
    intro y
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (by rw [coe_pow, coe_one]; exact hE' y y.2)
  obtain ⟨P₀, hP₀⟩ := hE'2.exists_le_sylow
  have hB := fusionBenderBorel_of_mulEquiv_psu3 (le_refl 2) e
  have hle : E' ≤ sylowCenter (P₀ : Subgroup (M ⧸ O)) := fun y hy =>
    mem_inf.mpr ⟨hP₀ hy, mem_centralizer_of_fusionBenderBorel hB (by norm_num) P₀ (hP₀ hy)
      (hE' y hy)⟩
  have hZ : Nat.card (sylowCenter (P₀ : Subgroup (M ⧸ O))) = 4 := by
    rw [← Hall32.card_center_eq_card_sylowCenter, (hB P₀).2.2.2.1]
    norm_num
  rw [← hcard, ← hZ]
  exact card_le_of_le hle

theorem card_le_four_of_fourgroup
    {D : Subgroup G} (hD4 : Nat.card D = 4) (hD : ∀ x ∈ D, x * x = 1)
    (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d)
    {P : Subgroup G} (hP : IsSylowOf 2 P (normalClosure (D : Set G))) {E : Subgroup G}
    (hEP : E ≤ P) (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hDS⟩ := exists_isSylowOf_ge_of_le (le_top : D ≤ ⊤) (isPGroup_of_mul_self hD)
  have hSN := le_normalizer_of_involutionClosed hD hcl hS.isPGroup hDS
  have hwc : ∀ g : G, rightConjugate D g ≤ S → rightConjugate D g = D := by
    intro g hg
    refine eq_of_le_of_card_ge ?_
      (card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective).ge
    rintro _ ⟨d, hd, rfl⟩
    have h1 : (MulAut.conj g⁻¹).toMonoidHom d ∈ S := hg ⟨d, hd, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1 ⊢
    exact conj_mem_of_mem_normalizer hD hcl hd (hSN h1)
  rcases hallFusionThm32 G S D hS hDS hD4 (isElemAbelian_of_mul_self hD) hwc with h1 | h1 | h1
  · calc Nat.card E ≤ Nat.card P := card_le_of_le hEP
      _ = Nat.card D := by rw [hP.card_eq, h1.card_eq]
      _ = 4 := hD4
  · obtain ⟨e⟩ := h1
    set M := normalClosure (D : Set G)
    have h2 := card_le_four_of_quotient_psu3 e (E := E.subgroupOf M) fun x hx =>
      Subtype.ext (hE x (mem_subgroupOf.mp hx))
    rwa [Nat.card_congr (subgroupOfEquivOfLe (hEP.trans hP.le)).toEquiv] at h2
  · exact Foote5.card_le_four_of_dihedral_or_semidihedral (Or.inl ⟨3, by norm_num, h1 P hP⟩) hEP
      hE

end CFSG.ComponentClassification.FooteLit.F5
