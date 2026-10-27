module

public import CFSG.GH74.Orders.LieType
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Fac

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup
open scoped commutatorElement

theorem ordA_one_mul_two {q : ℕ} (hq : Odd q) : Open.ordA 1 q * 2 = q * (q ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ := hq
  unfold Open.ordA
  have hg : Nat.gcd (1 + 1) (2 * k + 1 - 1) = 2 := by
    rw [show 2 * k + 1 - 1 = 2 * k by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton, hg]
  apply Nat.div_mul_cancel
  have h1 : (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
    omega
  rw [h1]
  exact Dvd.dvd.mul_left (dvd_mul_right 2 _) _

theorem eq_of_ordA_one_eq_odd {q q' : ℕ} (hq : Odd q) (hq' : Odd q')
    (h : Open.ordA 1 q = Open.ordA 1 q') : q = q' := by
  have h1 := ordA_one_mul_two hq
  have h2 := ordA_one_mul_two hq'
  have h3 : q * (q ^ 2 - 1) = q' * (q' ^ 2 - 1) := by rw [← h1, ← h2, h]
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
  have hq1' : 1 ≤ q' ^ 2 := Nat.one_le_pow _ _ hq'.pos
  have h4 : (q : ℤ) * ((q : ℤ) ^ 2 - 1) = (q' : ℤ) * ((q' : ℤ) ^ 2 - 1) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h3
    simp only [Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_sub hq1', Nat.cast_pow,
      Nat.cast_one] at this
    exact this
  have hp : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hp' : (0 : ℤ) < q' := by exact_mod_cast hq'.pos
  rcases lt_trichotomy q q' with hlt | heq | hgt
  · have hlt' : (q : ℤ) < q' := by exact_mod_cast hlt
    nlinarith [mul_pos (sub_pos.mpr hlt') (show (0 : ℤ) < q' ^ 2 + q * q' + q ^ 2 - 1 by
      nlinarith)]
  · exact heq
  · have hgt' : (q' : ℤ) < q := by exact_mod_cast hgt
    nlinarith [mul_pos (sub_pos.mpr hgt') (show (0 : ℤ) < q ^ 2 + q * q' + q' ^ 2 - 1 by
      nlinarith)]

theorem pow_eq_of_lieModel_psl_two {X : Type} [Group X] {p f p' f' : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp' : p'.Prime) (hp2' : p' ≠ 2) (h1 : Blueprint.LieModel X .PSL 2 p f)
    (h2 : Blueprint.LieModel X .PSL 2 p' f') : p ^ f = p' ^ f' := by
  have c1 := GH74.card_of_lieModel_PSL (by norm_num) h1
  have c2 := GH74.card_of_lieModel_PSL (by norm_num) h2
  exact eq_of_ordA_one_eq_odd (hp.odd_of_ne_two hp2).pow (hp'.odd_of_ne_two hp2').pow
    (c1.symm.trans c2)

theorem simple_of_lieModel_psl_two {Y : Type} [Group Y] {p f : ℕ}
    (h : Blueprint.LieModel Y .PSL 2 p f) : IsSimpleGroup Y ∧ ∃ a b : Y, a * b ≠ b * a := by
  rcases h with ⟨-, ⟨-, -, -, h22, h23⟩, F, _, _, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hF2 : Nat.card F ≠ 2 := fun h => h22 (by rw [← hF, h])
    have hF3 : Nat.card F ≠ 3 := fun h => h23 (by rw [← hF, h])
    set e' := e.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
    obtain ⟨-, hs, a, b, hab⟩ :=
      CatalogueBGeneralLinear.specialLinear_quasisimple 2 F le_rfl (Or.inr hF2) (Or.inr hF3)
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := hs
    refine ⟨e'.isSimpleGroup, e'.symm a, e'.symm b, fun hc => hab ?_⟩
    have := congrArg e' hc
    simpa using this
  all_goals exact absurd h0 (by norm_num)

theorem ne_bot_of_pComponent {X : Type*} [Group X] {L : Subgroup X} (hL : IsPComponent 2 L) :
    L ≠ ⊥ := by
  obtain ⟨K, hK, -, hLK, -⟩ := hL
  intro h
  rw [h, Subgroup.map_bot] at hLK
  subst hLK
  obtain ⟨a, b, hab⟩ := hK.1.2.2
  apply hab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have : a = b := Subsingleton.elim _ _
  rw [this]

theorem pPrimeCore_eq_center {L : Type*} [Group L] (hL : IsQuasisimple L)
    (hs : IsSimpleGroup (L ⧸ pPrimeCore 2 L)) (hna : ∃ a b : L ⧸ pPrimeCore 2 L, a * b ≠ b * a) :
    pPrimeCore 2 L = center L := by
  apply le_antisymm
  · rcases LocalCores.quasisimple_normal_subgroups hL
      (inferInstance : (pPrimeCore 2 L).Normal) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      have ha : (QuotientGroup.mk a : L ⧸ pPrimeCore 2 L) = 1 :=
        (QuotientGroup.eq_one_iff a).mpr (h ▸ mem_top a)
      have hb : (QuotientGroup.mk b : L ⧸ pPrimeCore 2 L) = 1 :=
        (QuotientGroup.eq_one_iff b).mpr (h ▸ mem_top b)
      rw [ha, hb]
    · exact h
  · intro z hz
    have hN : ((center L).map (QuotientGroup.mk' (pPrimeCore 2 L))).Normal :=
      (inferInstance : (center L).Normal).map _ (QuotientGroup.mk'_surjective _)
    rcases hN.eq_bot_or_eq_top with h | h
    · have hz' : QuotientGroup.mk' (pPrimeCore 2 L) z ∈
          (center L).map (QuotientGroup.mk' (pPrimeCore 2 L)) := ⟨z, hz, rfl⟩
      rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz'
      exact hz'
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      obtain ⟨x, hx, rfl⟩ : a ∈ (center L).map (QuotientGroup.mk' (pPrimeCore 2 L)) :=
        h ▸ mem_top a
      obtain ⟨y, -, rfl⟩ : b ∈ (center L).map (QuotientGroup.mk' (pPrimeCore 2 L)) :=
        h ▸ mem_top b
      apply hab
      rw [← map_mul, ← map_mul, mem_center_iff.mp hx y]

theorem lieModel_center_of_pPrimeCore {L : Type} [Group L] (hL : IsQuasisimple L) {p f : ℕ}
    (h : Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) :
    Blueprint.LieModel (L ⧸ center L) .PSL 2 p f := by
  obtain ⟨hs, hna⟩ := simple_of_lieModel_psl_two h
  exact LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (pPrimeCore_eq_center hL hs hna)) h

theorem eq_of_perfect {X : Type*} [Group X] (P : Subgroup X) (hP : ⁅P, P⁆ = P) (ψ : X →* X)
    (hc : ∀ x ∈ P, ∀ y ∈ P, Commute (x⁻¹ * ψ x) y)
    (hcc : ∀ x ∈ P, ∀ y ∈ P, Commute (x⁻¹ * ψ x) (y⁻¹ * ψ y)) : ∀ x ∈ P, ψ x = x := by
  have key : ⁅P, P⁆ ≤ MonoidHom.eqLocus ψ (MonoidHom.id X) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    change ψ ⁅x, y⁆ = ⁅x, y⁆
    set z₁ := x⁻¹ * ψ x with hz₁
    set z₂ := y⁻¹ * ψ y with hz₂
    have e1 : ψ x = x * z₁ := by rw [hz₁]; group
    have e2 : ψ y = y * z₂ := by rw [hz₂]; group
    have c1 : z₁ * y = y * z₁ := (hc x hx y hy).eq
    have c2 : z₂ * x⁻¹ = x⁻¹ * z₂ := (hc y hy x⁻¹ (inv_mem hx)).eq
    have c12 : z₁ * z₂ = z₂ * z₁ := (hcc x hx y hy).eq
    rw [map_commutatorElement, e1, e2, commutatorElement_def, commutatorElement_def]
    calc x * z₁ * (y * z₂) * (x * z₁)⁻¹ * (y * z₂)⁻¹
        = x * (z₁ * y) * z₂ * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by group
      _ = x * y * (z₁ * z₂) * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by rw [c1]; group
      _ = x * y * (z₂ * x⁻¹) * z₂⁻¹ * y⁻¹ := by rw [c12]; group
      _ = x * y * x⁻¹ * y⁻¹ := by rw [c2]; group
  intro x hx
  exact (hP ▸ key) hx

theorem commute_of_mem_coreActionKernel {H : Type} [Group H] {J : Subgroup H}
    (hJ : IsQuasisimple J) {p f : ℕ} (hm : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f)
    {b : H} (hb : b ∈ UnbalancedLayer.coreActionKernel J) : ∀ j ∈ J, b * j = j * b := by
  obtain ⟨hs, hna⟩ := simple_of_lieModel_psl_two hm
  have heq := pPrimeCore_eq_center hJ hs hna
  have hb' := (UnbalancedLayer.mem_coreActionKernel.mp hb).2
  rw [heq] at hb'
  have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ.1
  have hzz : ∀ x ∈ J, ∃ z ∈ center J, (z : H) = x⁻¹ * (MulAut.conj b⁻¹).toMonoidHom x := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hb' x hx
    refine ⟨z, hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show (z : H) = J.subtype z from rfl, hzx]
    group
  have key := eq_of_perfect J hperf (MulAut.conj b⁻¹).toMonoidHom
    (fun x hx y hy => by
      obtain ⟨z, hz, hzx⟩ := hzz x hx
      rw [← hzx]
      exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)).symm)
    (fun x hx y hy => by
      obtain ⟨z, hz, hzx⟩ := hzz x hx
      obtain ⟨w, -, hwy⟩ := hzz y hy
      rw [← hzx, ← hwy]
      exact (congrArg Subtype.val (mem_center_iff.mp hz w)).symm)
  intro j hj
  have h1 := key j hj
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
  calc b * j = b * (b⁻¹ * j * b) := by rw [h1]
    _ = j * b := by group

theorem isPComponent_of_prod_bot {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    {L : Subgroup X} (hL : IsPComponent 2 (L.prod (⊥ : Subgroup Y))) : IsPComponent 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := inl_range_normal (X := X) (Y := Y)
  have hinj : Function.Injective (MonoidHom.inl X Y) := fun _ _ h => (Prod.ext_iff.mp h).1
  have hle : L.prod (⊥ : Subgroup Y) ≤ (MonoidHom.inl X Y).range := by
    rintro ⟨x, y⟩ ⟨-, hy⟩
    refine ⟨x, ?_⟩
    simp only [MonoidHom.inl_apply, Prod.mk.injEq, true_and]
    exact ((Subgroup.mem_bot).mp hy).symm
  have h1 := CatalogueBFixedCentralQuotient.pComponent_restrict_normal 2 _ _ hle hL
  have h2 := CatalogueBAlternating.pComponent_map_equiv 2 (MonoidHom.ofInjective hinj).symm _ h1
  convert h2 using 1
  ext x
  constructor
  · intro hx
    refine ⟨MonoidHom.ofInjective hinj x, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_subgroupOf, MonoidHom.ofInjective_apply]
    exact ⟨hx, Subgroup.one_mem _⟩
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨x, hx⟩ := n.property
    have hnx : n = MonoidHom.ofInjective hinj x := Subtype.ext (by
      rw [MonoidHom.ofInjective_apply]; exact hx.symm)
    subst hnx
    rw [SetLike.mem_coe, mem_subgroupOf, MonoidHom.ofInjective_apply] at hn
    have hsx : (MonoidHom.ofInjective hinj).symm.toMonoidHom
        (MonoidHom.ofInjective hinj x) = x := by simp
    rw [hsx]
    exact hn.1

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
