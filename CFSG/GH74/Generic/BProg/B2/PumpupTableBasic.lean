module

import CFSG.GH74.Generic.S3.L3Cert
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Generic.BProg.Vocab
public import CFSG.GH74.Generic.ClassicalCerts
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupTableBasic

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Filter.ClassicalOdd CFSG.GH74.L5U5
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

theorem exists_lift_two_subgroup {G H : Type*} [Group G] [Finite G] [Group H] (ρ : G →* H)
    (hker : ¬ 2 ∣ Nat.card ρ.ker) (E : Subgroup H) (hE : E ≤ ρ.range) {k : ℕ}
    (hEcard : Nat.card E = 2 ^ k) :
    ∃ E₀ : Subgroup G, E₀.map ρ = E ∧ ∀ x ∈ E₀, ρ x = 1 → x = 1 := by
  classical
  have hp : Nat.Prime 2 := Nat.prime_two
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero k hp.ne_zero)
  set P' : Subgroup G := E.comap ρ with hP'
  let f : P' →* E := (ρ.comp P'.subtype).codRestrict E fun x => x.2
  have hfsurj : Function.Surjective f := fun e => by
    obtain ⟨g, hg⟩ := hE e.2
    exact ⟨⟨g, show ρ g ∈ E by rw [hg]; exact e.2⟩, Subtype.ext hg⟩
  have hfx : ∀ x : P', (f x : H) = ρ x := fun x => rfl
  have hkerf : Nat.card f.ker = Nat.card ρ.ker := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, ?_⟩, fun x => ⟨⟨x.1, ?_⟩, ?_⟩, ?_, ?_⟩
    · have := x.2
      rw [MonoidHom.mem_ker] at this ⊢
      have h2 := congrArg Subtype.val this
      rwa [hfx] at h2
    · show ρ x.1 ∈ E
      rw [MonoidHom.mem_ker.mp x.2]; exact E.one_mem
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hfx]
      exact MonoidHom.mem_ker.mp x.2
    · intro x; rfl
    · intro x; rfl
  have hPc : Nat.card P' = Nat.card ρ.ker * 2 ^ k := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv, hEcard,
      hkerf] at h1
    rw [h1, mul_comm]
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 P'))
  have hScard : Nat.card S = 2 ^ k := by
    rw [Sylow.card_eq_multiplicity, hPc, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero k hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, Nat.Prime.factorization_pow hp]
    simp
  have key : ∀ x ∈ S.map P'.subtype, ρ x = 1 → x = 1 := by
    intro x hx hρx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : orderOf (x' : G) ∣ 2 ^ k := by
      rw [← hScard]
      have := Subgroup.orderOf_dvd_natCard (S : Subgroup P') hx'
      simpa [Subgroup.orderOf_coe] using this
    have h2 : orderOf (x' : G) ∣ Nat.card ρ.ker := by
      have hmem : (x' : G) ∈ ρ.ker := hρx
      have := Subgroup.orderOf_dvd_natCard ρ.ker hmem
      simpa [Subgroup.orderOf_coe] using this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ρ.ker) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hker)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  have hSinj : ∀ x ∈ S.map P'.subtype, ∀ y ∈ S.map P'.subtype, ρ x = ρ y → x = y := by
    intro x hx y hy hxy
    have : x * y⁻¹ = 1 := key _ (Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy))
      (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  set E₀ : Subgroup G := S.map P'.subtype with hE₀
  have hE₀card : Nat.card E₀ = 2 ^ k := by
    rw [hE₀, Subgroup.card_map_of_injective P'.subtype_injective, hScard]
  have hmapE : E₀.map ρ = E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
      exact g'.2
    · have : Nat.card (E₀.map ρ) = Nat.card E₀ := by
        refine Nat.card_congr (Equiv.ofBijective
          (fun x : E₀ => ⟨ρ x, Subgroup.mem_map_of_mem _ x.2⟩) ⟨?_, ?_⟩).symm
        · intro x y hxy
          exact Subtype.ext (hSinj _ x.2 _ y.2 (congrArg Subtype.val hxy))
        · rintro ⟨_, g, hg, rfl⟩
          exact ⟨⟨g, hg⟩, rfl⟩
      rw [this, hE₀card, hEcard]
  exact ⟨E₀, hmapE, key⟩

theorem exists_lift_hom_two {G H Q : Type*} [Group G] [Finite G] [Group H] [Group Q] [Finite Q]
    (ρ : G →* H) (hker : ¬ 2 ∣ Nat.card ρ.ker) (hQ : IsPGroup 2 Q) (ψ : Q →* H)
    (hψ : Function.Injective ψ) (hrange : ψ.range ≤ ρ.range) :
    ∃ ψ' : Q →* G, Function.Injective ψ' ∧ ρ.comp ψ' = ψ := by
  classical
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hEcard : Nat.card ψ.range = 2 ^ k := by
    rw [← hk]
    exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  obtain ⟨E₀, hmap, key⟩ := exists_lift_two_subgroup ρ hker ψ.range hrange hEcard
  let g : E₀ →* ψ.range := (ρ.comp E₀.subtype).codRestrict ψ.range fun x => by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem ρ x.2
  have hginj : Function.Injective g := by
    intro x y hxy
    have h1 : ρ (x : G) = ρ (y : G) := congrArg Subtype.val hxy
    have : (x : G) * (y : G)⁻¹ = 1 := key _ (Subgroup.mul_mem _ x.2 (Subgroup.inv_mem _ y.2))
      (by rw [map_mul, map_inv, h1, mul_inv_cancel])
    exact Subtype.ext (mul_inv_eq_one.mp this)
  have hgsurj : Function.Surjective g := by
    rintro ⟨_, hy⟩
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : E₀ ≃* ψ.range := MulEquiv.ofBijective g ⟨hginj, hgsurj⟩
  refine ⟨E₀.subtype.comp (e.symm.toMonoidHom.comp ψ.rangeRestrict), ?_, ?_⟩
  · exact E₀.subtype_injective.comp (e.symm.injective.comp (fun a b h => hψ (by
      have := congrArg Subtype.val h
      exact this)))
  · ext q
    have h1 : g (e.symm (ψ.rangeRestrict q)) = ψ.rangeRestrict q := e.apply_symm_apply _
    have h2 := congrArg Subtype.val h1
    exact h2

theorem exists_q8_statedProj_three {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    ∃ ψ : Q8 →* StatedProj (StatedSL 3 F), Function.Injective ψ := by
  obtain ⟨a, b, h⟩ := (odd_field_two_dimensional_quaternion_matrices hF).1
  let Q : QuatRep F := QuatRep.ofSq hF h
  have hQinj : Function.Injective Q.ρ := fun g g' hgg' =>
    quatHom_injective hF h (Subtype.ext hgg')
  let χ : Multiplicative (ZMod 4) →* Fˣ := 1
  let α : Q8 →* GL (Fin 3) F :=
    ((alpha3 Q.ρ χ).comp (MonoidHom.inl Q8 (Multiplicative (ZMod 4)))).toHomUnits
  have hαapp : ∀ g, (α g : Matrix (Fin 3) (Fin 3) F) =
      diagBlock (Q.ρ g) (1 : Matrix (Fin 1) (Fin 1) F) := by
    intro g
    change alpha3 Q.ρ χ (g, 1) = _
    rw [alpha3_apply]
    simp [χ]
  have hαdet : ∀ g, α g ∈ StatedSL 3 F := fun g => by
    refine Subgroup.subset_closure ?_
    change (α g : Matrix (Fin 3) (Fin 3) F).det = 1
    rw [hαapp, det_diagBlock, Q.det_eq, det_one, mul_one]
  refine ⟨(QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F))).comp
    (α.codRestrict (StatedSL 3 F) hαdet), ?_⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  have hc' : (α g : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) (c : F) := by
    rw [← GeneralLinearGroup.coe_scalar, hc]
    rfl
  rw [hαapp] at hc'
  obtain ⟨h1, h3⟩ := eq_scalar_of_diagBlock_eq hc'
  have hc1 : (c : F) = 1 := by
    have := congrFun (congrFun h3 0) 0
    simp [scalar_apply] at this
    exact this.symm
  rw [hc1] at h1
  apply hQinj
  rw [h1, map_one]
  ext i j
  simp [one_apply]

theorem exists_q8_statedProj_su_three {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (hq : Odd q) :
    ∃ ψ : Q8 →* StatedProj (StatedSU 3 q F), Function.Injective ψ := by
  obtain ⟨p, f, hpf, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hodd : Odd (Nat.card F) := by rw [hF]; exact hq.pow
  have hp2 : p ≠ 2 := prime_ne_two_of_odd_card hodd
  have hK2 : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  obtain ⟨a, b, ha, hb, hab⟩ := exists_quat_unitary hp2 hF
  let Q : QuatRep F := QuatRep.ofSq hK2 hab
  have hQinj : Function.Injective Q.ρ := fun g g' hgg' =>
    quatHom_injective hK2 hab (Subtype.ext hgg')
  have hσ : ∀ x, iterateFrobenius F p f x = x ^ (p ^ f) :=
    CFSG.SectionRank.ClassicalOdd.frob_apply
  have hQ : ∀ g, IsUni (iterateFrobenius F p f) (Q.ρ g) := fun g =>
    isUni_quatHom hab (by rw [hσ]; exact ha) (by rw [hσ]; exact hb) g
  let χ : Multiplicative (ZMod 4) →* Fˣ := 1
  let α : Q8 →* GL (Fin 3) F :=
    ((alpha3 Q.ρ χ).comp (MonoidHom.inl Q8 (Multiplicative (ZMod 4)))).toHomUnits
  have hαapp : ∀ g, (α g : Matrix (Fin 3) (Fin 3) F) =
      diagBlock (Q.ρ g) (1 : Matrix (Fin 1) (Fin 1) F) := by
    intro g
    change alpha3 Q.ρ χ (g, 1) = _
    rw [alpha3_apply]
    simp [χ]
  have hαmem : ∀ g, α g ∈ StatedSU 3 (p ^ f) F := fun g => by
    refine mem_statedSU_of_isUni hσ _ ?_ ?_
    · rw [hαapp, det_diagBlock, Q.det_eq, det_one, mul_one]
    · rw [hαapp]
      exact (hQ g).diagBlock IsUni.one
  refine ⟨(QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ f) F))).comp
    (α.codRestrict (StatedSU 3 (p ^ f) F) hαmem), ?_⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  have hc' : (α g : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) (c : F) := by
    rw [← GeneralLinearGroup.coe_scalar, hc]
    rfl
  rw [hαapp] at hc'
  obtain ⟨h1, h3⟩ := eq_scalar_of_diagBlock_eq hc'
  have hc1 : (c : F) = 1 := by
    have := congrFun (congrFun h3 0) 0
    simp [scalar_apply] at this
    exact this.symm
  rw [hc1] at h1
  apply hQinj
  rw [h1, map_one]
  ext i j
  simp [one_apply]

theorem stated_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (h : LieModel X t n p f) : StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by rcases ht with rfl | rfl <;> decide)

theorem exists_q8_of_shape13 {X : Type} [Group X] (h : QShape1 X ∨ QShape3 X) :
    ∃ ψ : Q8 →* X, Function.Injective ψ := by
  rcases h with h | h
  · obtain ⟨z, φ, w, -, -, hφ, -⟩ := IsSL4Model.exists_q8_frame h
    refine ⟨φ.comp (MonoidHom.inl Q8 Q8), hφ.comp fun a b hab => ?_⟩
    simpa using hab
  · obtain ⟨p, f, hp, hp2, -, hm | hm⟩ := h
    · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := stated_of_lieModel (Or.inl rfl) hm
      have hF2 : ringChar F ≠ 2 :=
        CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
      obtain ⟨ψ, hψ⟩ := exists_q8_statedProj_three hF2
      exact ⟨e.symm.toMonoidHom.comp ψ, e.symm.injective.comp hψ⟩
    · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := stated_of_lieModel (Or.inr rfl) hm
      obtain ⟨ψ, hψ⟩ := exists_q8_statedProj_su_three hF (hp.odd_of_ne_two hp2).pow
      exact ⟨e.symm.toMonoidHom.comp ψ, e.symm.injective.comp hψ⟩

theorem isPGroup_q8 : IsPGroup 2 Q8 := by
  refine IsPGroup.of_card (n := 3) ?_
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  norm_num

theorem q8_in_H_of_shape {N : Type} [Group N] [Finite N] {H L : Subgroup N} (hLH : L ≤ H)
    {Z : Subgroup ↥L} (hZ : Z.Normal) (hZo : Odd (Nat.card ↥Z))
    (hψ : ∃ ψ : Q8 →* ↥L ⧸ Z, Function.Injective ψ) :
    ∃ ψ : Q8 →* ↥H, Function.Injective ψ := by
  have := hZ
  obtain ⟨ψ, hψi⟩ := hψ
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' Z).ker := by
    rw [QuotientGroup.ker_mk']
    exact fun h => (Nat.not_even_iff_odd.mpr hZo) (even_iff_two_dvd.mpr h)
  obtain ⟨ψ', hψ', -⟩ := exists_lift_hom_two (QuotientGroup.mk' Z) hker isPGroup_q8 ψ hψi
    (by rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Z)]; exact le_top)
  exact ⟨(Subgroup.inclusion hLH).comp ψ',
    (Subgroup.inclusion_injective hLH).comp hψ'⟩

theorem rankCertified_in_H_of_shape {N : Type} [Group N] [Finite N] {H L : Subgroup N} (hLH : L ≤ H)
    {Z : Subgroup ↥L} (hZ : Z.Normal) {r : ℕ} (h : RankCertified (↥L ⧸ Z) r) :
    RankCertified ↥H r := by
  have := hZ
  exact (h.of_quotient Z).of_injective (Subgroup.inclusion hLH) (Subgroup.inclusion_injective hLH)

end CFSG.GH74.Generic.BProg.B2.PumpupTableBasic
