module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Semidihedral CFSG.Wreathed CFSG.GorensteinWalter
open CFSG.BenderSuzuki.External CFSG.BenderSuzuki.PFchapter1section1

universe u v

section Odd

variable {G : Type u} [Group G] [Finite G]

theorem le_of_odd_of_isPGroup_quotient (K : Subgroup G) [K.Normal] (hK : IsPGroup 2 (G ⧸ K))
    (N : Subgroup G) (hN : Odd (Nat.card N)) : N ≤ K := by
  have hmap : N.map (QuotientGroup.mk' K) = ⊥ := by
    have h1 : IsPGroup 2 (N.map (QuotientGroup.mk' K)) := hK.to_subgroup _
    have h2 : Nat.card (N.map (QuotientGroup.mk' K)) ∣ Nat.card N := Subgroup.card_map_dvd N _
    obtain ⟨k, hk⟩ := h1.exists_card_eq
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact Subgroup.card_eq_one.mp hk
    · exfalso
      rw [hk] at h2
      have h2' : 2 ∣ Nat.card N := dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero k)) h2
      exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h2')
  intro x hx
  have hx' : (QuotientGroup.mk' K) x ∈ N.map (QuotientGroup.mk' K) := ⟨x, hx, rfl⟩
  rw [hmap, Subgroup.mem_bot] at hx'
  exact (QuotientGroup.eq_one_iff x).mp hx'

theorem le_of_odd_of_two_pow_index (K : Subgroup G) [K.Normal] (hK : ∃ k : ℕ, K.index = 2 ^ k)
    (N : Subgroup G) (hN : Odd (Nat.card N)) : N ≤ K := by
  obtain ⟨k, hk⟩ := hK
  exact le_of_odd_of_isPGroup_quotient K
    (IsPGroup.of_card (n := k) (by rw [← Subgroup.index_eq_card, hk])) N hN

omit [Finite G] in
theorem odd_card_subgroupOf {N : Subgroup G} (hN : Odd (Nat.card N)) (K : Subgroup G) :
    Odd (Nat.card (N.subgroupOf K)) := by
  have hcard : Nat.card (N.subgroupOf K) = Nat.card (N ⊓ K : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]
  rw [hcard]
  exact Odd.of_dvd_nat hN (Subgroup.card_dvd_of_le inf_le_left)

end Odd

section Kernel

variable {A : Type u} {B : Type v} [Group A] [Group B] [Finite A] (φ : A →* B)

theorem inf_ker_eq_bot (hker : Odd (Nat.card φ.ker)) (P : Subgroup A) (hP : IsPGroup 2 P) :
    P ⊓ φ.ker = ⊥ := by
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hker)

theorem injective_comp_subtype (hker : Odd (Nat.card φ.ker)) (P : Subgroup A)
    (hP : IsPGroup 2 P) : Function.Injective (φ.comp P.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have h2 : (x : A) ∈ P ⊓ φ.ker := ⟨x.2, hx⟩
  rw [inf_ker_eq_bot φ hker P hP, Subgroup.mem_bot] at h2
  exact Subgroup.mem_bot.mpr (Subtype.ext h2)

theorem eq_of_mem_of_map_eq (hker : Odd (Nat.card φ.ker)) {P : Subgroup A} (hP : IsPGroup 2 P)
    {x y : A} (hx : x ∈ P) (hy : y ∈ P) (hxy : φ x = φ y) : x = y := by
  have h := injective_comp_subtype φ hker P hP (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy
  exact congrArg Subtype.val h

@[expose] noncomputable def equivMapOfIsPGroup (hker : Odd (Nat.card φ.ker)) (P : Subgroup A)
    (hP : IsPGroup 2 P) : P ≃* P.map φ :=
  (MonoidHom.ofInjective (injective_comp_subtype φ hker P hP)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))

theorem equivMapOfIsPGroup_coe (hker : Odd (Nat.card φ.ker)) (P : Subgroup A)
    (hP : IsPGroup 2 P) (x : P) : (equivMapOfIsPGroup φ hker P hP x : B) = φ x := rfl

theorem exists_sylow_map_eq (hφ : Function.Surjective φ) (S' : Sylow 2 B) :
    ∃ S : Sylow 2 A, (S : Subgroup A).map φ = S' := by
  have : Finite B := Finite.of_surjective φ hφ
  obtain ⟨S⟩ : Nonempty (Sylow 2 A) := inferInstance
  let T : Sylow 2 B := S.mapSurjective hφ
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B T S'
  obtain ⟨g, rfl⟩ := hφ b
  refine ⟨g • S, ?_⟩
  rw [← hb, Sylow.coe_subgroup_smul, Sylow.coe_subgroup_smul, Sylow.coe_mapSurjective]
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hy
    exact ⟨φ c, ⟨c, hc, rfl⟩, by simp [MulAut.smul_def]⟩
  · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨MulAut.conj g • c, (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨c, hc, rfl⟩, ?_⟩
    simp [MulAut.smul_def]

theorem nonempty_sylow_equiv_map (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker))
    (S : Sylow 2 A) : Nonempty ((S : Subgroup A) ≃* (S.mapSurjective hφ : Sylow 2 B)) := by
  have : Finite B := Finite.of_surjective φ hφ
  exact ⟨(equivMapOfIsPGroup φ hker S S.isPGroup').trans
    (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective hφ S).symm)⟩

theorem sylow_types_iff (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker))
    (X : Type*) [Group X] :
    (∀ S' : Sylow 2 B, Nonempty ((S' : Subgroup B) ≃* X)) ↔
      ∀ S : Sylow 2 A, Nonempty ((S : Subgroup A) ≃* X) := by
  have : Finite B := Finite.of_surjective φ hφ
  constructor
  · intro h S
    obtain ⟨e⟩ := h (S.mapSurjective hφ)
    obtain ⟨e'⟩ := nonempty_sylow_equiv_map φ hφ hker S
    exact ⟨e'.trans e⟩
  · intro h S'
    obtain ⟨S, hS⟩ := exists_sylow_map_eq φ hφ S'
    obtain ⟨e⟩ := h S
    exact ⟨((equivMapOfIsPGroup φ hker S S.isPGroup').trans
      (MulEquiv.subgroupCongr hS)).symm.trans e⟩

theorem hasSemidihedralSylow_iff_of_oddKernel (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) (n : ℕ) :
    HasSemidihedralSylow B n ↔ HasSemidihedralSylow A n := by
  have h := sylow_types_iff φ hφ hker (SemidihedralGroup n)
  constructor
  · rintro ⟨hn, hB⟩
    refine ⟨hn, fun S => ?_⟩
    obtain ⟨e⟩ := h.mp (fun S' => ⟨(hB S').some.symm⟩) S
    exact ⟨e.symm⟩
  · rintro ⟨hn, hA⟩
    refine ⟨hn, fun S' => ?_⟩
    obtain ⟨e⟩ := h.mpr (fun S => ⟨(hA S).some.symm⟩) S'
    exact ⟨e.symm⟩

theorem hasWreathedSylow_iff_of_oddKernel (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) (n : ℕ) :
    HasWreathedSylow B n ↔ HasWreathedSylow A n := by
  have h := sylow_types_iff φ hφ hker (Wreath (2 ^ n))
  exact ⟨fun ⟨hn, hB⟩ => ⟨hn, h.mp hB⟩, fun ⟨hn, hA⟩ => ⟨hn, h.mpr hA⟩⟩

theorem hasQDOrWreathedSylow_iff_of_oddKernel (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) : HasQDOrWreathedSylow B ↔ HasQDOrWreathedSylow A := by
  constructor
  · rintro ⟨h, hh⟩
    rcases hh with ⟨h1, n, hn⟩ | hw
    · exact ⟨h, Or.inl ⟨h1, n, (hasSemidihedralSylow_iff_of_oddKernel φ hφ hker n).mp hn⟩⟩
    · exact ⟨h, Or.inr ((hasWreathedSylow_iff_of_oddKernel φ hφ hker h).mp hw)⟩
  · rintro ⟨h, hh⟩
    rcases hh with ⟨h1, n, hn⟩ | hw
    · exact ⟨h, Or.inl ⟨h1, n, (hasSemidihedralSylow_iff_of_oddKernel φ hφ hker n).mpr hn⟩⟩
    · exact ⟨h, Or.inr ((hasWreathedSylow_iff_of_oddKernel φ hφ hker h).mpr hw)⟩

theorem hasDihedralSylowTwo_iff_of_oddKernel (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) : HasDihedralSylowTwo B ↔ HasDihedralSylowTwo A := by
  have : Finite B := Finite.of_surjective φ hφ
  constructor
  · intro hB S
    obtain ⟨m, hm, ⟨e⟩⟩ := hB (S.mapSurjective hφ)
    obtain ⟨e'⟩ := nonempty_sylow_equiv_map φ hφ hker S
    exact ⟨m, hm, ⟨e'.trans e⟩⟩
  · intro hA S'
    obtain ⟨S, hS⟩ := exists_sylow_map_eq φ hφ S'
    obtain ⟨m, hm, ⟨e⟩⟩ := hA S
    exact ⟨m, hm, ⟨((equivMapOfIsPGroup φ hker S S.isPGroup').trans
      (MulEquiv.subgroupCongr hS)).symm.trans e⟩⟩

theorem hasGeneralizedQuaternionSylow_iff_of_oddKernel (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) :
    HasGeneralizedQuaternionSylow B ↔ HasGeneralizedQuaternionSylow A := by
  have : Finite B := Finite.of_surjective φ hφ
  constructor
  · intro hB S
    obtain ⟨k, hk, ⟨e⟩⟩ := hB (S.mapSurjective hφ)
    obtain ⟨e'⟩ := nonempty_sylow_equiv_map φ hφ hker S
    exact ⟨k, hk, ⟨e'.trans e⟩⟩
  · intro hA S'
    obtain ⟨S, hS⟩ := exists_sylow_map_eq φ hφ S'
    obtain ⟨k, hk, ⟨e⟩⟩ := hA S
    exact ⟨k, hk, ⟨((equivMapOfIsPGroup φ hker S S.isPGroup').trans
      (MulEquiv.subgroupCongr hS)).symm.trans e⟩⟩

theorem abelianSylow_iff_of_oddKernel (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) :
    (∀ P : Sylow 2 B, IsMulCommutative P) ↔ ∀ P : Sylow 2 A, IsMulCommutative P := by
  have : Finite B := Finite.of_surjective φ hφ
  constructor
  · intro hB S
    obtain ⟨e'⟩ := nonempty_sylow_equiv_map φ hφ hker S
    exact isMulCommutative_of_mulEquiv e'.symm (hB _)
  · intro hA S'
    obtain ⟨S, hS⟩ := exists_sylow_map_eq φ hφ S'
    exact isMulCommutative_of_mulEquiv ((equivMapOfIsPGroup φ hker S S.isPGroup').trans
      (MulEquiv.subgroupCongr hS)) (hA S)

theorem noIndexTwo_iff_of_oddKernel (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) :
    (∀ M : Subgroup A, M.index ≠ 2) ↔ ∀ M : Subgroup B, M.index ≠ 2 := by
  constructor
  · intro hA M hM
    apply hA (M.comap φ)
    rw [Subgroup.index_comap_of_surjective _ hφ, hM]
  · intro hB M hM
    have : M.Normal := Subgroup.normal_of_index_eq_two hM
    have hkerM : φ.ker ≤ M := le_of_odd_of_two_pow_index M ⟨1, by rw [hM, pow_one]⟩ φ.ker hker
    apply hB (M.map φ)
    rw [Subgroup.index_map, sup_eq_left.mpr hkerM, MonoidHom.range_eq_top.mpr hφ,
      Subgroup.index_top, mul_one, hM]

theorem hasNormalPComplement_iff_of_oddKernel (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) : HasNormalPComplement 2 B ↔ HasNormalPComplement 2 A := by
  have : Finite B := Finite.of_surjective φ hφ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro ⟨N', hN', hcop, hq⟩
    have hNn : (N'.comap φ).Normal := hN'.comap φ
    refine ⟨N'.comap φ, hNn, ?_, ?_⟩
    · rw [Nat.coprime_two_left]
      by_contra hodd
      have heven : 2 ∣ Nat.card (N'.comap φ) :=
        even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N'.comap φ) 2 heven
      have hφx : φ (x : A) ∈ N' := x.property
      have h1 : orderOf (⟨φ x, hφx⟩ : N') ∣ 2 := by
        rw [Subgroup.orderOf_mk]
        calc orderOf (φ (x : A)) ∣ orderOf (x : A) := orderOf_map_dvd φ _
          _ = 2 := by rw [Subgroup.orderOf_coe, hx]
      have h2 : orderOf (⟨φ x, hφx⟩ : N') ∣ Nat.card N' := orderOf_dvd_natCard _
      have h3 : orderOf (⟨φ x, hφx⟩ : N') = 1 :=
        Nat.dvd_one.mp (Nat.Coprime.gcd_eq_one hcop ▸ Nat.dvd_gcd h1 h2)
      rw [orderOf_eq_one_iff] at h3
      have hxker : (x : A) ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val h3
      have h4 := orderOf_dvd_natCard (⟨(x : A), hxker⟩ : φ.ker)
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx] at h4
      exact (Nat.not_even_iff_odd.mpr hker) (even_iff_two_dvd.mpr h4)
    · intro q
      induction q using QuotientGroup.induction_on with | H a => ?_
      obtain ⟨k, hk⟩ := hq (φ a)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      change φ (a ^ 2 ^ k) ∈ N'
      rw [map_pow]
      rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
  · rintro ⟨N, hN, hcop, hq⟩
    have hNn : (N.map φ).Normal := hN.map φ hφ
    refine ⟨N.map φ, hNn, ?_, ?_⟩
    · rw [Nat.coprime_two_left] at hcop ⊢
      exact Odd.of_dvd_nat hcop (Subgroup.card_map_dvd N φ)
    · intro q
      induction q using QuotientGroup.induction_on with | H b => ?_
      obtain ⟨a, rfl⟩ := hφ b
      obtain ⟨k, hk⟩ := hq a
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← map_pow]
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
      exact ⟨_, hk, rfl⟩

omit [Finite A] in
theorem odd_card_ker_subgroupMap (hker : Odd (Nat.card φ.ker)) (K : Subgroup A) :
    Odd (Nat.card (φ.subgroupMap K).ker) := by
  have hk : (φ.subgroupMap K).ker = φ.ker.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [hk]
  exact odd_card_subgroupOf hker K

end Kernel

section Data

variable {A : Type u} {B : Type v} [Group A] [Group B] [Finite A] (φ : A →* B)
  (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker))

include hφ hker in
theorem IsDGroupData.map_of_oddKernel {K : Subgroup A} (h : IsDGroupData K) :
    IsDGroupData (K.map φ) := by
  have : Finite B := Finite.of_surjective φ hφ
  have : K.Normal := h.normal
  have hkerK : φ.ker ≤ K := le_of_odd_of_two_pow_index K ⟨1, by rw [h.index_eq_two, pow_one]⟩
    φ.ker hker
  have hsurj := φ.subgroupMap_surjective K
  have hoddK := odd_card_ker_subgroupMap φ hker K
  refine ⟨h.normal.map φ hφ, ?_, (noIndexTwo_iff_of_oddKernel _ hsurj hoddK).mp h.noIndexTwo, ?_⟩
  · rw [Subgroup.index_map, sup_eq_left.mpr hkerK, MonoidHom.range_eq_top.mpr hφ,
      Subgroup.index_top, mul_one, h.index_eq_two]
  · rcases h.sylow with ⟨n, hSD, hD⟩ | ⟨n, hW, hab⟩
    · exact Or.inl ⟨n, (hasSemidihedralSylow_iff_of_oddKernel φ hφ hker n).mpr hSD,
        (hasDihedralSylowTwo_iff_of_oddKernel _ hsurj hoddK).mpr hD⟩
    · exact Or.inr ⟨n, (hasWreathedSylow_iff_of_oddKernel φ hφ hker n).mpr hW,
        (abelianSylow_iff_of_oddKernel _ hsurj hoddK).mpr hab⟩

include hφ hker in
theorem IsDGroupData.comap_of_oddKernel {K : Subgroup B} (h : IsDGroupData K) :
    IsDGroupData (K.comap φ) := by
  have : Finite B := Finite.of_surjective φ hφ
  have hmap : (K.comap φ).map φ = K := Subgroup.map_comap_eq_self_of_surjective hφ K
  have hsurj : Function.Surjective ((MulEquiv.subgroupCongr hmap).toMonoidHom.comp
      (φ.subgroupMap (K.comap φ))) :=
    (MulEquiv.subgroupCongr hmap).surjective.comp (φ.subgroupMap_surjective _)
  have hoddK : Odd (Nat.card ((MulEquiv.subgroupCongr hmap).toMonoidHom.comp
      (φ.subgroupMap (K.comap φ))).ker) := by
    have hk : ((MulEquiv.subgroupCongr hmap).toMonoidHom.comp
        (φ.subgroupMap (K.comap φ))).ker = (φ.subgroupMap (K.comap φ)).ker := by
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
    rw [hk]
    exact odd_card_ker_subgroupMap φ hker _
  refine ⟨h.normal.comap φ, ?_, (noIndexTwo_iff_of_oddKernel _ hsurj hoddK).mpr h.noIndexTwo, ?_⟩
  · rw [Subgroup.index_comap_of_surjective _ hφ, h.index_eq_two]
  · rcases h.sylow with ⟨n, hSD, hD⟩ | ⟨n, hW, hab⟩
    · exact Or.inl ⟨n, (hasSemidihedralSylow_iff_of_oddKernel φ hφ hker n).mp hSD,
        (hasDihedralSylowTwo_iff_of_oddKernel _ hsurj hoddK).mp hD⟩
    · exact Or.inr ⟨n, (hasWreathedSylow_iff_of_oddKernel φ hφ hker n).mp hW,
        (abelianSylow_iff_of_oddKernel _ hsurj hoddK).mp hab⟩

end Data

end CFSG.QuasiDihedralFusion
