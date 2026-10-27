module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54SL

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54

open CFSG Subgroup Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def ConclZ (p f : ℕ) (Y : Type) [Group Y] (t : Y) : Prop :=
  ∃ u : Y, orderOf u = 2 ∧ u ∉ center Y ∧ ∃ J₁ J₂ : Subgroup Y,
    IsTwoComponentIn J₁ (centralizer {u}) ∧ IsTwoComponentIn J₂ (centralizer {u}) ∧ J₁ ≠ J₂ ∧
    u ∈ J₁ ∧ J₁ ⊓ center Y = ⊥ ∧ IsSLTwoOver (p ^ f) ↥J₁ ∧ IsQuasisimple ↥J₂ ∧
    (∃ x ∈ J₂, orderOf x = 2 ∧ x ∉ center Y) ∧
    (∃ (τ' : StatedLieTag) (n' : ℕ), Blueprint.LieModel (↥J₂ ⧸ center ↥J₂) τ' n' p f) ∧
    (t ∈ J₂ ∨ t * u ∈ J₂)

section Central

variable {Y B : Type} [Group Y] [Group B] [Finite Y] [Finite B] {φ : Y →* B}

omit [Finite Y] [Finite B] in
theorem mem_center_of_commutator_mem_center (hq : IsQuasisimple Y) {x : Y}
    (h : ∀ g : Y, ⁅x, g⁆ ∈ center Y) : x ∈ center Y := by
  obtain ⟨-, hs, a, b, hab⟩ := hq
  have hZ : center (Y ⧸ center Y) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Y ⧸ center Y)) with hc | hc
    · exact hc
    · exact absurd (mem_center_iff.mp (hc ▸ mem_top b) a) hab
  have hxZ : QuotientGroup.mk' (center Y) x ∈ center (Y ⧸ center Y) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (center Y) g
    have hc := h m
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc.symm
  rwa [hZ, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxZ

omit [Finite Y] [Finite B] in
theorem mem_center_of_map_mem_center (hq : IsQuasisimple Y) (hk : φ.ker ≤ center Y)
    {x : Y} (hx : φ x ∈ center B) : x ∈ center Y := by
  refine mem_center_of_commutator_mem_center hq fun g => hk ?_
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (mem_center_iff.mp hx (φ g)).symm

omit [Finite Y] [Finite B] in
theorem map_mem_center (hφ : Function.Surjective φ) {x : Y} (hx : x ∈ center Y) :
    φ x ∈ center B := by
  rw [mem_center_iff]
  intro g
  obtain ⟨g, rfl⟩ := hφ g
  rw [← map_mul, ← map_mul, mem_center_iff.mp hx g]

omit [Finite Y] [Finite B] in
theorem isQuasisimple_of_surjective (hq : IsQuasisimple Y) (hφ : Function.Surjective φ)
    (hB : Nontrivial B) : IsQuasisimple B := by
  have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hφ
  rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hq φ with h | h
  · exfalso
    obtain ⟨b, hb⟩ := exists_ne (1 : B)
    have : b ∈ φ.range := hrange ▸ mem_top b
    rw [h, mem_bot] at this
    exact hb this
  · exact LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv) h

omit [Finite Y] [Finite B] in
theorem isQuasisimple_map {J : Subgroup Y} (hq : IsQuasisimple ↥J) {x : Y} (hxJ : x ∈ J)
    (hx : φ x ≠ 1) : IsQuasisimple ↥(J.map φ) := by
  have : Nontrivial ↥(J.map φ) :=
    ⟨⟨⟨φ x, mem_map_of_mem φ hxJ⟩, 1, fun h => hx (congrArg Subtype.val h)⟩⟩
  exact isQuasisimple_of_surjective (φ := φ.subgroupMap J) hq (φ.subgroupMap_surjective J)
    inferInstance

omit [Finite Y] [Finite B] in
theorem conj_mem_centralizer (hk : φ.ker ≤ center Y) {u c y : Y}
    (hc : φ c ∈ centralizer {φ u}) (hy : y ∈ centralizer ({u} : Set Y)) :
    c * y * c⁻¹ ∈ centralizer ({u} : Set Y) := by
  rw [mem_centralizer_singleton_iff] at hy hc ⊢
  have hkc : (c * u * c⁻¹)⁻¹ * u ∈ center Y := hk (by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hc, mul_inv_cancel_right, inv_mul_cancel])
  have h1 : c * y * c⁻¹ * (c * u * c⁻¹) = c * u * c⁻¹ * (c * y * c⁻¹) := by
    calc c * y * c⁻¹ * (c * u * c⁻¹) = c * (y * u) * c⁻¹ := by group
      _ = c * (u * y) * c⁻¹ := by rw [hy]
      _ = c * u * c⁻¹ * (c * y * c⁻¹) := by group
  have h2 := mem_center_iff.mp hkc (c * y * c⁻¹)
  calc c * y * c⁻¹ * u = c * y * c⁻¹ * (c * u * c⁻¹) * ((c * u * c⁻¹)⁻¹ * u) := by group
    _ = c * u * c⁻¹ * (c * y * c⁻¹) * ((c * u * c⁻¹)⁻¹ * u) := by rw [h1]
    _ = c * u * c⁻¹ * ((c * y * c⁻¹) * ((c * u * c⁻¹)⁻¹ * u)) := by group
    _ = c * u * c⁻¹ * (((c * u * c⁻¹)⁻¹ * u) * (c * y * c⁻¹)) := by rw [h2]
    _ = u * (c * y * c⁻¹) := by group

omit [Finite Y] [Finite B] in
theorem normal_map_centralizer (hφ : Function.Surjective φ) (hk : φ.ker ≤ center Y) (u : Y) :
    (centralizer ({u} : Set Y)).map φ ≤ centralizer {φ u} ∧
      (((centralizer ({u} : Set Y)).map φ).subgroupOf (centralizer {φ u})).Normal := by
  have hle : (centralizer ({u} : Set Y)).map φ ≤ centralizer {φ u} := by
    intro q hq
    obtain ⟨c, hc, rfl⟩ := mem_map.mp hq
    rw [mem_centralizer_singleton_iff] at hc ⊢
    rw [← map_mul, ← map_mul, hc]
  refine ⟨hle, (normal_subgroupOf_iff_le_normalizer hle).mpr fun b hb => ?_⟩
  obtain ⟨c, rfl⟩ := hφ b
  have hcN : c ∈ normalizer (centralizer ({u} : Set Y)) := by
    rw [mem_normalizer_iff]
    intro y
    refine ⟨conj_mem_centralizer hk hb, fun hy => ?_⟩
    have hb' : φ c⁻¹ ∈ centralizer {φ u} := by
      rw [map_inv]
      exact inv_mem hb
    have h1 := conj_mem_centralizer hk hb' hy
    rwa [show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at h1
  exact le_normalizer_map φ ⟨c, hcN, rfl⟩

omit [Finite Y] in
theorem isTwoComponentIn_map_of_central (hφ : Function.Surjective φ) (hk : φ.ker ≤ center Y)
    {u : Y} {J : Subgroup Y} (hJ : IsTwoComponentIn J (centralizer {u}))
    (hqJ : IsQuasisimple ↥(J.map φ)) (h2 : 2 ∣ Nat.card ↥(J.map φ)) :
    IsTwoComponentIn (J.map φ) (centralizer {φ u}) := by
  obtain ⟨hle, hn⟩ := normal_map_centralizer hφ hk u
  have hsn : ((J.map φ).subgroupOf ((centralizer ({u} : Set Y)).map φ)).IsSubnormal := by
    have h1 := hJ.2.1.map (φ.subgroupMap_surjective (centralizer ({u} : Set Y)))
    rwa [GSThmB.OddQuot.map_subgroupOf_subgroupMap φ hJ.1] at h1
  exact ⟨(map_mono hJ.1).trans hle, CFSG.GroupTheory.isSubnormal_subgroupOf_trans (map_mono hJ.1)
    hle hsn hn.isSubnormal, SL.isTwoQuasisimple_of_isQuasisimple hqJ h2⟩

omit [Finite Y] [Finite B] in
theorem eq_of_map_eq_of_central (hk : φ.ker ≤ center Y) {J₁ J₂ : Subgroup Y}
    (h₁ : Group.IsPerfect ↥J₁) (h₂ : Group.IsPerfect ↥J₂) (h : J₁.map φ = J₂.map φ) :
    J₁ = J₂ := by
  have key : ∀ {A A' : Subgroup Y}, Group.IsPerfect ↥A → A.map φ = A'.map φ → A ≤ A' := by
    intro A A' hA hAA'
    have hAA : ⁅A, A⁆ = A := by
      have h1 := congrArg (Subgroup.map A.subtype) hA.commutator_eq_top
      rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h1
    have hdec : ∀ a ∈ A, ∃ k ∈ center Y, ∃ a' ∈ A', a = k * a' := by
      intro a ha
      obtain ⟨a', ha', hφa⟩ : φ a ∈ A'.map φ := hAA' ▸ mem_map_of_mem φ ha
      refine ⟨a * a'⁻¹, hk ?_, a', ha', by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφa, mul_inv_cancel]
    calc A = ⁅A, A⁆ := hAA.symm
      _ ≤ A' := by
        rw [commutator_le]
        intro a ha b hb
        obtain ⟨k, hk', a', ha', rfl⟩ := hdec a ha
        obtain ⟨k', hk'', b', hb', rfl⟩ := hdec b hb
        rw [LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hk' hk'',
          commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha' hb') (inv_mem ha')) (inv_mem hb')
  exact le_antisymm (key h₁ h) (key h₂ h.symm)

omit [Finite Y] [Finite B] in
theorem nonempty_center_quot_equiv (hq : IsQuasisimple Y) (hφ : Function.Surjective φ)
    (hk : φ.ker ≤ center Y) : Nonempty (Y ⧸ center Y ≃* B ⧸ center B) := by
  set θ := (QuotientGroup.mk' (center B)).comp φ with hθ
  have hθs : Function.Surjective θ := (QuotientGroup.mk'_surjective _).comp hφ
  have hθk : θ.ker = center Y := by
    ext y
    rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ⟨mem_center_of_map_mem_center hq hk, map_mem_center hφ⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hθk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθs)⟩

omit [Finite Y] in
theorem ConclZ.map (hq : IsQuasisimple Y) (hφ : Function.Surjective φ) (hk : φ.ker ≤ center Y)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) {t : Y} (h : ConclZ p f Y t) :
    Concl p f B (φ t) := by
  obtain ⟨u, hu2, huZ, J₁, J₂, hJ₁, hJ₂, hne, huJ, hJ₁Z, hs₁, hq₂, ⟨x, hxJ, hx2, hxZ⟩,
    ⟨τ', n', hlie⟩, ht⟩ := h
  have hφu : φ u ≠ 1 := fun h1 => huZ (hk (MonoidHom.mem_ker.mpr h1))
  have hφx : φ x ≠ 1 := fun h1 => hxZ (hk (MonoidHom.mem_ker.mpr h1))
  have hqB : IsQuasisimple B := isQuasisimple_of_surjective hq hφ ⟨⟨φ u, 1, hφu⟩⟩
  have hu2' : orderOf (φ u) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, ← hu2, pow_orderOf_eq_one, map_one]) hφu
  have hx2' : orderOf (φ x) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, ← hx2, pow_orderOf_eq_one, map_one]) hφx
  have hinj : Function.Injective (φ.comp J₁.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    have h1 : (a : Y) ∈ J₁ ⊓ center Y := ⟨a.2, hk (MonoidHom.mem_ker.mpr ha)⟩
    rw [hJ₁Z, mem_bot] at h1
    exact Subtype.ext h1
  have hrange : (φ.comp J₁.subtype).range = J₁.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e₁ : ↥J₁ ≃* ↥(J₁.map φ) := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hs₁' : IsSLTwoOver (p ^ f) ↥(J₁.map φ) := isSLTwoOver_of_mulEquiv e₁ hs₁
  have hq₁' : IsQuasisimple ↥(J₁.map φ) := (isQuasisimple_of_isSLTwoOver hp hp2 h5 hs₁').1
  have hq₂' : IsQuasisimple ↥(J₂.map φ) := isQuasisimple_map hq₂ hxJ hφx
  have h2J₁ : 2 ∣ Nat.card ↥(J₁.map φ) := by
    have h1 := orderOf_dvd_natCard (⟨φ u, mem_map_of_mem φ huJ⟩ : ↥(J₁.map φ))
    rwa [Subgroup.orderOf_mk, hu2'] at h1
  have h2J₂ : 2 ∣ Nat.card ↥(J₂.map φ) := by
    have h1 := orderOf_dvd_natCard (⟨φ x, mem_map_of_mem φ hxJ⟩ : ↥(J₂.map φ))
    rwa [Subgroup.orderOf_mk, hx2'] at h1
  have hk₂ : (φ.subgroupMap J₂).ker ≤ center ↥J₂ := by
    intro a ha
    have h1 : (a : Y) ∈ center Y := hk (by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
      exact MonoidHom.mem_ker.mpr this)
    rw [mem_center_iff] at h1 ⊢
    intro g
    exact Subtype.ext (h1 g)
  obtain ⟨e₂⟩ := nonempty_center_quot_equiv hq₂ (φ.subgroupMap_surjective J₂) hk₂
  have hlie' : Blueprint.LieModel (↥(J₂.map φ) ⧸ Open.fusionZStar ↥(J₂.map φ)) τ' n' p f :=
    GSThmB.OddQuot.lieModel_of_equiv (e₂.trans (QuotientGroup.quotientMulEquivOfEq
      (fusionZStar_eq_center_of_isQuasisimple hq₂' h2J₂).symm)) hlie
  refine ⟨φ u, hu2', not_mem_fusionZStar hqB hu2'
    (fun h1 => huZ (mem_center_of_map_mem_center hq hk h1)), J₁.map φ, J₂.map φ,
    isTwoComponentIn_map_of_central hφ hk hJ₁ hq₁' h2J₁,
    isTwoComponentIn_map_of_central hφ hk hJ₂ hq₂' h2J₂,
    fun h1 => hne (eq_of_map_eq_of_central hk hJ₁.2.2.1 hJ₂.2.2.1 h1), mem_map_of_mem φ huJ,
    isSLTwoOver_quot hp hp2 h5 hs₁', ⟨τ', n', hlie'⟩, ?_⟩
  rcases ht with ht | ht
  · exact .inl (mem_map_of_mem φ ht)
  · refine .inr ?_
    rw [← map_mul]
    exact mem_map_of_mem φ ht

end Central

end CFSG.ComponentClassification.HarrisLit.T1.P54
