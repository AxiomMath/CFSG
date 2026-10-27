module

public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchLocal
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchCore
public import CFSG.CharacterTheory.CyclicBlocks.InertialIndexTwo
public import CFSG.CharacterTheory.Semidihedral.Principal.RealOddPrincipalBlock
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

open scoped Pointwise

namespace CFSG.Semidihedral.UnitaryBranch

open CFSG.Open CFSG.Semidihedral CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Semidihedral.Principal
open CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] [Finite G]

theorem multiplier_preimage_facts {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) :
    IsCyclic ((multiplierHom F).range.comap κ) ∧ NZ t ≤ (multiplierHom F).range.comap κ ∧
      (∀ a ∈ (multiplierHom F).range.comap κ, ∀ b ∈ (multiplierHom F).range.comap κ,
        a * b = b * a) := by
  have hcyc := multiplier_preimage_isCyclic hD n hn S fS ht
  refine ⟨hcyc, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_comap]
    have : x ∈ κ.ker := hD.ker_eq ▸ hx
    rw [MonoidHom.mem_ker] at this
    rw [this]
    exact Subgroup.one_mem _
  · intro a ha b hb
    have := hcyc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this

theorem multiplier_or_antimultiplier {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) {s₁ g : C t}
    (hs₁ : s₁ ∈ (multiplierHom F).range.comap κ) (hs₁N : s₁ ∉ NZ t)
    (hg : g * s₁ * g⁻¹ ∈ (multiplierHom F).range.comap κ) :
    g ∈ (multiplierHom F).range.comap κ ∨ ∃ μ : Fˣ, κ g = multiplier F μ * inversion F := by
  obtain ⟨c, hc⟩ := hs₁
  obtain ⟨c', hc'⟩ := hg
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hs₁N
    rw [← hD.ker_eq, MonoidHom.mem_ker, ← hc, map_one]
  have hc'1 : c' ≠ 1 := by
    rintro rfl
    apply hs₁N
    have h1 : g * s₁ * g⁻¹ ∈ κ.ker := by rw [MonoidHom.mem_ker, ← hc', map_one]
    rw [hD.ker_eq] at h1
    have hNZn : (NZ t).Normal := by
      have hc := (NZ_facts hD.orderOf_t hD.core_central hD.core_cyclic).2.1
      exact ⟨fun x hx y => by
        have h := Subgroup.mem_center_iff.mp (hc hx) y
        rw [h, mul_inv_cancel_right]
        exact hx⟩
    have := hNZn.conj_mem _ h1 g⁻¹
    simpa [mul_assoc] using this
  have hconj : κ g * multiplier F c * (κ g)⁻¹ = multiplier F c' := by
    rw [← multiplierHom_apply, ← multiplierHom_apply, hc, hc']
    simp [map_mul, map_inv]
  have hpres := preserves_of_conj_multiplier F hc1 hc'1 hconj
  have hmem : κ g ∈ coordinateD F := hD.range_eq ▸ ⟨g, rfl⟩
  rcases eq_multiplier_or_of_preserves F hmem hpres with ⟨μ, hμ⟩ | hμ
  · exact Or.inl ⟨μ, hμ.symm⟩
  · exact Or.inr hμ

omit [Finite G] in
theorem kappa_conj_of_antimultiplier {t : G} {F : Type} [Field F]
    {κ : C t →* Equiv.Perm (Omega F)} {g x : C t} {μ : Fˣ}
    (hg : κ g = multiplier F μ * inversion F) (hx : x ∈ (multiplierHom F).range.comap κ) :
    κ (g * x * g⁻¹) = (κ x)⁻¹ := by
  obtain ⟨c, hc⟩ := hx
  rw [map_mul, map_mul, map_inv, hg, ← hc, multiplierHom_apply]
  have h1 : multiplier F μ * inversion F * multiplier F c * (multiplier F μ * inversion F)⁻¹ =
      multiplier F μ * (inversion F * multiplier F c * (inversion F)⁻¹) * (multiplier F μ)⁻¹ := by
    group
  rw [h1, inversion_conj_multiplier, ← multiplierHom_apply, ← multiplierHom_apply,
    ← multiplierHom_apply, ← map_inv, ← map_inv, ← map_mul, ← map_mul, mul_comm μ, mul_assoc,
    mul_inv_cancel, mul_one]

theorem conj_eq_inv_of_antimultiplier {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) {g x : C t} {μ : Fˣ}
    (hg : κ g = multiplier F μ * inversion F) (hx : x ∈ (multiplierHom F).range.comap κ)
    (hcop : Nat.Coprime (orderOf x) (2 * Nat.card (N t))) : g * x * g⁻¹ = x⁻¹ := by
  obtain ⟨-, hNZH, hHcomm⟩ := multiplier_preimage_facts hD n hn S fS ht
  obtain ⟨-, -, -, hNZcard⟩ := NZ_facts hD.orderOf_t hD.core_central hD.core_cyclic
  have hκ := kappa_conj_of_antimultiplier hg hx
  set y := g * x * g⁻¹ with hy
  have hyH : y ∈ (multiplierHom F).range.comap κ := by
    rw [Subgroup.mem_comap, hκ]
    exact Subgroup.inv_mem _ hx
  have hyx : y * x ∈ NZ t := by
    rw [← hD.ker_eq, MonoidHom.mem_ker, map_mul, hκ, inv_mul_cancel]
  have hcomm : y * x = x * y := hHcomm y hyH x hx
  have hoy : orderOf y = orderOf x := by
    rw [hy, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have h1 : orderOf (y * x) ∣ orderOf x := by
    apply orderOf_dvd_of_pow_eq_one
    rw [(Commute.mul_pow hcomm (orderOf x)), ← hoy, pow_orderOf_eq_one, hoy, pow_orderOf_eq_one,
      one_mul]
  have h2 : orderOf (y * x) ∣ 2 * Nat.card (N t) := by
    rw [← hNZcard]
    have := orderOf_dvd_natCard (⟨y * x, hyx⟩ : NZ t)
    rwa [Subgroup.orderOf_mk] at this
  have h3 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  exact eq_inv_of_mul_eq_one_left h3

theorem principal_character_section_eq {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {w : G} {e : ℕ}
    (hw : orderOf w ∣ 2 ^ e)
    (hcyc : ∃ R : Sylow 2 (Subgroup.centralizer (Subgroup.zpowers w : Set G)), IsCyclic R)
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    {y : G} (hy : y ∈ Subgroup.centralizer (Subgroup.zpowers w : Set G))
    (hyodd : Odd (orderOf y)) :
    (basis.representation χ).character (w * y) = (basis.representation χ).character w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cw := Subgroup.centralizer (Subgroup.zpowers w : Set G)
  obtain ⟨R, hR⟩ := hcyc
  obtain ⟨K, hKn, hKc⟩ := exists_normal_isComplement'_of_isCyclic_sylow_two R hR
  have hcard : Nat.card K * Nat.card R = Nat.card Cw := hKc.card_mul_card
  obtain ⟨k, hk⟩ := R.isPGroup'.exists_card_eq
  set v := (Nat.card Cw).factorization 2 with hv
  have hRfac : Nat.card R = 2 ^ v := Sylow.card_eq_multiplicity R
  have hKodd : Nat.Coprime 2 (Nat.card K) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h2
    have h1 : 2 ^ (v + 1) ∣ Nat.card Cw := by
      rw [← hcard, hRfac, pow_succ, mul_comm (2 ^ v) 2]
      exact Nat.mul_dvd_mul h2 (dvd_refl _)
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h1
    omega
  have hquot : IsPGroup 2 (Cw ⧸ K) := by
    apply IsPGroup.of_card (n := k)
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    have h2 : Nat.card (Cw ⧸ K) * Nat.card K = Nat.card R * Nat.card K := by
      rw [← h1, ← hcard, mul_comm]
    rw [← hk]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hyK : (⟨y, hy⟩ : Cw) ∈ K := by
    have himg : ((⟨y, hy⟩ : Cw) : Cw ⧸ K) = 1 := by
      obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hquot ((⟨y, hy⟩ : Cw) : Cw ⧸ K)
      have h1 : orderOf ((⟨y, hy⟩ : Cw) : Cw ⧸ K) ∣ orderOf y := by
        rw [← Subgroup.orderOf_mk y hy]
        exact orderOf_map_dvd (QuotientGroup.mk' K) _
      rw [hj] at h1
      rcases j with _ | j
      · rw [pow_zero] at hj
        exact orderOf_eq_one_iff.mp hj
      · exfalso
        have h2 : 2 ∣ orderOf y := (dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h1
        exact (Nat.not_even_iff_odd.mpr hyodd) (even_iff_two_dvd.mpr h2)
    exact (QuotientGroup.eq_one_iff _).mp himg
  exact principal_character_section_constant_of_normal_complement basis ideal 2 principal
    hprincipal hw K hKodd hquot hχ hyK

theorem exists_conj_r_of_commute_of_card {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (R : Subgroup G) (hR : IsPGroup 2 R)
    (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRcard : Nat.card R = 2 ^ (n - 1)) :
    ∃ r' : G, IsConj r' (fS (r n) : G) ∧ R = Subgroup.zpowers r' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hRS'⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  set R₀ := R.map (MulAut.conj g).toMonoidHom with hR₀def
  have hR₀S : R₀ ≤ (S : Subgroup G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hRS' hx)
  set R'' := R₀.comap ((S : Subgroup G).subtype.comp fS.toMonoidHom) with hR''
  have hφinj : Function.Injective ((S : Subgroup G).subtype.comp fS.toMonoidHom) :=
    Subtype.val_injective.comp fS.injective
  have hR''map : R''.map ((S : Subgroup G).subtype.comp fS.toMonoidHom) = R₀ := by
    apply Subgroup.map_comap_eq_self
    intro x hx
    obtain ⟨a, ha⟩ := fS.surjective ⟨x, hR₀S hx⟩
    exact ⟨a, by simp [ha]⟩
  have hR₀comm : ∀ a ∈ R₀, ∀ b ∈ R₀, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hRcomm x hx y hy]
  have hR''comm : ∀ a ∈ R'', ∀ b ∈ R'', a * b = b * a := by
    intro a ha b hb
    apply hφinj
    rw [map_mul, map_mul]
    exact hR₀comm _ ha _ hb
  have hR''card : Nat.card R'' = 2 ^ (n - 1) := by
    rw [← hRcard, ← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, ← hR₀def, ← hR''map, Subgroup.card_map_of_injective hφinj]
  have hR''eq := eq_zpowers_r_of_commute n hn R'' hR''comm hR''card
  refine ⟨g⁻¹ * (fS (r n) : G) * g, ?_, ?_⟩
  · exact isConj_iff.mpr ⟨g, by group⟩
  · have hR₀eq : R₀ = Subgroup.zpowers (fS (r n) : G) := by
      rw [← hR''map, hR''eq, MonoidHom.map_zpowers]
      rfl
    have hRR₀ : R = R₀.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [hR₀def, Subgroup.map_map]
      conv_lhs => rw [← Subgroup.map_id R]
      congr 1
      ext x
      simp only [MulAut.conj_apply, MonoidHom.id_apply, MonoidHom.coe_comp,
        MulEquiv.coe_toMonoidHom, Function.comp_apply]
      group
    rw [hRR₀, hR₀eq, MonoidHom.map_zpowers]
    congr 1
    simp

theorem exists_torus_sylow_two {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) :
    ∃ r' : C t, IsConj (r' : G) (fS (r n) : G) ∧ r' ∈ (multiplierHom F).range.comap κ ∧
      r' ∉ NZ t ∧ orderOf r' = 2 ^ (n - 1) ∧
      (∀ x ∈ (multiplierHom F).range.comap κ, (∃ k : ℕ, orderOf x = 2 ^ k) →
        x ∈ Subgroup.zpowers r') ∧ tInC t ∈ Subgroup.zpowers r' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcyc, hNZH, hHcomm⟩ := multiplier_preimage_facts hD n hn S fS ht
  obtain ⟨h2fac, -⟩ := factorization_two_multiplier_preimage hD n hn S fS ht
  obtain ⟨hodd, -, -, hNZcard⟩ := NZ_facts hD.orderOf_t hD.core_central hD.core_cyclic
  set H' := (multiplierHom F).range.comap κ
  let P₂ : Sylow 2 H' := default
  have hP₂card : Nat.card P₂ = 2 ^ (n - 1) := by rw [Sylow.card_eq_multiplicity, h2fac]
  set R : Subgroup G := ((P₂ : Subgroup H').map H'.subtype).map (C t).subtype with hRdef
  have hRcard : Nat.card R = 2 ^ (n - 1) := by
    rw [hRdef, Subgroup.card_map_of_injective (C t).subtype_injective,
      Subgroup.card_map_of_injective H'.subtype_injective, hP₂card]
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩ _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    exact congrArg Subtype.val (hHcomm x x.2 y y.2)
  obtain ⟨r'G, hconj, hReq⟩ :=
    exists_conj_r_of_commute_of_card hn S fS R (IsPGroup.of_card hRcard) hRcomm hRcard
  have hr'R : r'G ∈ R := hReq ▸ Subgroup.mem_zpowers r'G
  obtain ⟨_, ⟨x₀, hx₀P, rfl⟩, hx₀⟩ := hr'R
  set r' : C t := (x₀ : C t)
  have hr'G : (r' : G) = r'G := hx₀
  have hP₂normal : (P₂ : Subgroup H').Normal := by
    have : IsMulCommutative H' := ⟨⟨fun a b => Subtype.ext (hHcomm a a.2 b b.2)⟩⟩
    infer_instance
  have hP₂all : ∀ x : H', (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ (P₂ : Subgroup H') := by
    rintro x ⟨k, hk⟩
    have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
      apply IsPGroup.of_card (n := k)
      rw [Nat.card_zpowers, hk]
    obtain ⟨P', hP'⟩ := hxp.exists_le_sylow
    have := Sylow.unique_of_normal P₂ hP₂normal
    rw [Subsingleton.elim P' P₂] at hP'
    exact hP' (Subgroup.mem_zpowers x)
  have hmemR : ∀ y : C t, y ∈ Subgroup.zpowers r' ↔ (y : G) ∈ R := by
    intro y
    rw [hReq, ← hr'G]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by simp⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, Subtype.ext ?_⟩
      simpa using hk
  have hr'H : r' ∈ H' := x₀.2
  have hr'o : orderOf r' = 2 ^ (n - 1) := by
    rw [← Subgroup.orderOf_coe, hr'G, ← Nat.card_zpowers, ← hReq, hRcard]
  have h2elt : ∀ x ∈ H', (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ Subgroup.zpowers r' := by
    intro x hx hk
    rw [hmemR]
    have hxP := hP₂all ⟨x, hx⟩ (by rwa [Subgroup.orderOf_mk])
    exact ⟨x, ⟨⟨x, hx⟩, hxP, rfl⟩, rfl⟩
  refine ⟨r', hr'G ▸ hconj, hr'H, ?_, hr'o, h2elt, ?_⟩
  · intro hr'NZ
    have hle : Subgroup.zpowers r' ≤ NZ t := Subgroup.zpowers_le.mpr hr'NZ
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, hr'o, hNZcard] at hdvd
    have h4 : 4 ∣ 2 ^ (n - 1) := by
      rw [show n - 1 = 2 + (n - 3) by omega, pow_add]
      exact dvd_mul_right 4 _
    obtain ⟨m, hm⟩ := hodd
    have := h4.trans hdvd
    omega
  · apply h2elt _ (hNZH (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
    refine ⟨1, ?_⟩
    rw [tInC, Subgroup.orderOf_mk, hD.orderOf_t, pow_one]

theorem conj_eq_self_of_sq_eq_one_of_isCyclic {X : Subgroup G} [IsCyclic X] {g x : G}
    (hx : x ∈ X) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hgx : g * x * g⁻¹ ∈ X) : g * x * g⁻¹ = x := by
  have h2 : (g * x * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hx2, mul_one, mul_inv_cancel]
  have h1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, h]
    group
  have := eq_of_sq_eq_one_of_isCyclic (K := X) (a := ⟨_, hgx⟩) (b := ⟨x, hx⟩)
    (Subtype.ext (by simpa using h2)) (fun h => h1 (congrArg Subtype.val h))
    (Subtype.ext (by simpa using hx2)) (fun h => hx1 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem eq_zpowers_of_le_centralizer {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) {r' : C t}
    (hr'H : r' ∈ (multiplierHom F).range.comap κ) (hr'NZ : r' ∉ NZ t)
    (h2elt : ∀ x ∈ (multiplierHom F).range.comap κ, (∃ k : ℕ, orderOf x = 2 ^ k) →
      x ∈ Subgroup.zpowers r') (htr : tInC t ∈ Subgroup.zpowers r') {w : G}
    (hPw : ∀ g : C t, (∃ μ : Fˣ, κ g = multiplier F μ * inversion F) → (g : G) * w ≠ w * g)
    {R : Subgroup G} (hR : IsPGroup 2 R) (hrR : Subgroup.zpowers (r' : G) ≤ R)
    (hRw : R ≤ Subgroup.centralizer {w}) : R = Subgroup.zpowers (r' : G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hlt : (Subgroup.zpowers (r' : G)).subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm (fun x hx => ?_) hrR
    have : (⟨x, hx⟩ : R) ∈ (Subgroup.zpowers (r' : G)).subgroupOf R := htop ▸ Subgroup.mem_top _
    exact this
  have : Group.IsNilpotent R := hR.isNilpotent
  obtain ⟨g, hgN, hgT⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hgnorm : ∀ x ∈ Subgroup.zpowers (r' : G), (g : G) * x * (g : G)⁻¹ ∈
      Subgroup.zpowers (r' : G) := by
    intro x hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hgN ⟨x, hrR hx⟩).mp hx
    exact h1
  have htG : t ∈ Subgroup.zpowers (r' : G) := by
    obtain ⟨k, hk⟩ := htr
    exact ⟨k, by
      have h := congrArg Subtype.val hk
      simpa [tInC] using h⟩
  have hgt : (g : G) * t * (g : G)⁻¹ = t := by
    have : IsCyclic (Subgroup.zpowers (r' : G)) := inferInstance
    have ht2 : t ^ 2 = 1 := by rw [← hD.orderOf_t]; exact pow_orderOf_eq_one t
    have ht1 : t ≠ 1 := by
      intro h
      have := hD.orderOf_t
      rw [h, orderOf_one] at this
      omega
    exact conj_eq_self_of_sq_eq_one_of_isCyclic htG ht2 ht1 (hgnorm t htG)
  have hgC : (g : G) ∈ C t := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (g : G) * t = (g : G) * t * (g : G)⁻¹ * g := by group
      _ = t * g := by rw [hgt]
  set gC : C t := ⟨g, hgC⟩
  have hconj : gC * r' * gC⁻¹ ∈ (multiplierHom F).range.comap κ := by
    have h1 := hgnorm _ (Subgroup.mem_zpowers (r' : G))
    obtain ⟨k, hk⟩ := h1
    have : gC * r' * gC⁻¹ = r' ^ k := Subtype.ext (by simpa [gC] using hk.symm)
    rw [this]
    exact Subgroup.zpow_mem _ hr'H k
  rcases multiplier_or_antimultiplier hD hr'H hr'NZ hconj with hgH | hanti
  · apply hgT
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR g
    have h1 := h2elt gC hgH ⟨k, by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hk]⟩
    obtain ⟨j, hj⟩ := h1
    change (g : G) ∈ Subgroup.zpowers (r' : G)
    exact ⟨j, by
      have h := congrArg Subtype.val hj
      simpa [gC] using h⟩
  · apply hPw gC hanti
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hRw g.2)).symm ▸
      (Subgroup.mem_centralizer_singleton_iff.mp (hRw g.2))

theorem antimultiplier_not_commute_of_coprime {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) {u : C t}
    (huH : u ∈ (multiplierHom F).range.comap κ) (hu1 : u ≠ 1)
    (hcop : Nat.Coprime (orderOf u) (2 * Nat.card (N t))) (g : C t)
    (hg : ∃ μ : Fˣ, κ g = multiplier F μ * inversion F) : (g : G) * u ≠ u * g := by
  obtain ⟨μ, hμ⟩ := hg
  intro hcomm
  have hinv := conj_eq_inv_of_antimultiplier hD n hn S fS ht hμ huH hcop
  have hcomm' : g * u * g⁻¹ = u := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcomm]
    group
  rw [hcomm'] at hinv
  have hu2 : u ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hinv]
    exact mul_inv_cancel u
  have h1 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
  have h2 : orderOf u ∣ 2 * Nat.card (N t) := h1.trans (dvd_mul_right 2 _)
  exact hu1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl h2))

theorem antimultiplier_not_commute_rotation {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) (n : ℕ) (hn : 4 ≤ n)
    {r' : C t}
    (hr'H : r' ∈ (multiplierHom F).range.comap κ) (hr'o : orderOf r' = 2 ^ (n - 1))
    (h2elt : ∀ x ∈ (multiplierHom F).range.comap κ, (∃ k : ℕ, orderOf x = 2 ^ k) →
      x ∈ Subgroup.zpowers r') {v : ℕ} (hv : v = 1 ∨ v = 2) (g : C t)
    (hg : ∃ μ : Fˣ, κ g = multiplier F μ * inversion F) :
    (g : G) * ((r' : G) ^ v) ≠ ((r' : G) ^ v) * g := by
  obtain ⟨μ, hμ⟩ := hg
  obtain ⟨-, -, -, hNZcard⟩ := NZ_facts hD.orderOf_t hD.core_central hD.core_cyclic
  obtain ⟨hodd, -, -, -⟩ := NZ_facts hD.orderOf_t hD.core_central hD.core_cyclic
  intro hcomm
  have hκ := kappa_conj_of_antimultiplier hμ hr'H
  set y := g * r' * g⁻¹ with hy
  have hyH : y ∈ (multiplierHom F).range.comap κ := by
    rw [Subgroup.mem_comap, hκ]
    exact Subgroup.inv_mem _ hr'H
  have hoy : orderOf y = 2 ^ (n - 1) := by
    rw [hy, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hr'o]
  obtain ⟨k, hk⟩ := h2elt y hyH ⟨n - 1, hoy⟩
  set z := y * r' with hz
  have hzNZ : z ∈ NZ t := by
    rw [← hD.ker_eq, MonoidHom.mem_ker, hz, map_mul, hκ, inv_mul_cancel]
  have hzr : z ∈ Subgroup.zpowers r' := Subgroup.mul_mem _ (hk ▸ Subgroup.zpow_mem_zpowers r' k)
    (Subgroup.mem_zpowers r')
  have hz2 : z ^ 2 = 1 := by
    obtain ⟨j, hj⟩ := hzr
    have h1 : orderOf z ∣ 2 * Nat.card (N t) := by
      rw [← hNZcard]
      have := orderOf_dvd_natCard (⟨z, hzNZ⟩ : NZ t)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf z ∣ 2 ^ (n - 1) := hr'o ▸ orderOf_dvd_of_mem_zpowers ⟨j, hj⟩
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    have h3 : orderOf z ∣ 2 := by
      rw [hi] at h1 ⊢
      rcases i with _ | _ | i
      · simp
      · simp
      · exfalso
        have h4 : 4 ∣ 2 * Nat.card (N t) :=
          (show 4 ∣ 2 ^ (i + 2) by rw [pow_add]; exact dvd_mul_left 4 _).trans h1
        obtain ⟨m, hm⟩ := hodd
        omega
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  have hzc : Commute z r' := by
    obtain ⟨j, hj⟩ := hzr
    rw [← hj]
    exact Commute.zpow_left (Commute.refl r') j
  have hyv : g * r' ^ v * g⁻¹ = z ^ v * (r' ^ v)⁻¹ := by
    have hyz : y = z * r'⁻¹ := by rw [hz]; group
    rw [← conj_pow, ← hy, hyz, (hzc.inv_right).mul_pow, inv_pow]
  have hcommC : g * r' ^ v * g⁻¹ = r' ^ v := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow]
    rw [hcomm]
    group
  rw [hcommC] at hyv
  have h4 : r' ^ 4 = 1 := by
    rcases hv with rfl | rfl
    · have h1 : r' ^ 2 = z := by
        simp only [pow_one] at hyv
        calc r' ^ 2 = r' * r' := pow_two r'
          _ = z * r'⁻¹ * r' := by rw [← hyv]
          _ = z := by group
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h1, hz2]
    · have h1 : r' ^ 4 = z ^ 2 := by
        calc r' ^ 4 = r' ^ 2 * r' ^ 2 := by rw [← pow_add]
          _ = z ^ 2 * (r' ^ 2)⁻¹ * r' ^ 2 := by rw [← hyv]
          _ = z ^ 2 := by group
      rw [h1, hz2]
  have h5 : 2 ^ (n - 1) ∣ 4 := by
    rw [← hr'o]
    exact orderOf_dvd_of_pow_eq_one h4
  have h6 : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h7 := Nat.le_of_dvd (by norm_num) h5
  omega

omit [Finite G] in
theorem mem_centralizer_zpowers_iff {u x : G} :
    x ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G) ↔ x * u = u * x := by
  constructor
  · intro hx
    exact (Subgroup.mem_centralizer_iff.mp hx u (Subgroup.mem_zpowers u)).symm
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_right hx k).eq).symm

theorem mem_C_of_conj_mem_zpowers {t : G} (ht : orderOf t = 2) {r' : G}
    (htr : t ∈ Subgroup.zpowers r') {g : G} (hg : g * r' * g⁻¹ ∈ Subgroup.zpowers r') :
    g ∈ Subgroup.centralizer {t} := by
  have hgt : g * t * g⁻¹ ∈ Subgroup.zpowers r' := by
    obtain ⟨k, rfl⟩ := htr
    simp only
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hg k
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have h := conj_eq_self_of_sq_eq_one_of_isCyclic htr ht2 ht1 hgt
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [h]

theorem exists_cyclic_sylow_centralizer {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) {n : ℕ} {r' : C t}
    (hr'H : r' ∈ (multiplierHom F).range.comap κ) (hr'NZ : r' ∉ NZ t)
    (hr'o : orderOf r' = 2 ^ (n - 1))
    (h2elt : ∀ x ∈ (multiplierHom F).range.comap κ, (∃ k : ℕ, orderOf x = 2 ^ k) →
      x ∈ Subgroup.zpowers r') (htr : tInC t ∈ Subgroup.zpowers r') {w : G}
    (hrw : (r' : G) * w = w * r')
    (hPw : ∀ g : C t, (∃ μ : Fˣ, κ g = multiplier F μ * inversion F) → (g : G) * w ≠ w * g) :
    ∃ R : Sylow 2 (Subgroup.centralizer (Subgroup.zpowers w : Set G)), IsCyclic R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cw := Subgroup.centralizer (Subgroup.zpowers w : Set G)
  have hr'Cw : (r' : G) ∈ Cw := mem_centralizer_zpowers_iff.mpr hrw
  have hr'p : IsPGroup 2 (Subgroup.zpowers (r' : G)) := by
    apply IsPGroup.of_card (n := n - 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hr'o]
  have hTp : IsPGroup 2 ((Subgroup.zpowers (r' : G)).subgroupOf Cw) :=
    hr'p.comap_of_injective _ Cw.subtype_injective
  obtain ⟨R₀, hR₀⟩ := hTp.exists_le_sylow
  have hR₀' : (R₀ : Subgroup Cw).map Cw.subtype = Subgroup.zpowers (r' : G) := by
    apply eq_zpowers_of_le_centralizer hD hr'H hr'NZ h2elt htr hPw
    · exact R₀.isPGroup'.map _
    · intro x hx
      have hxC : x ∈ Cw := Subgroup.zpowers_le.mpr hr'Cw hx
      exact ⟨⟨x, hxC⟩, hR₀ hx, rfl⟩
    · rintro _ ⟨y, -, rfl⟩
      have := (mem_centralizer_zpowers_iff.mp y.2)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact this
  refine ⟨R₀, ?_⟩
  have hcyc : IsCyclic ((R₀ : Subgroup Cw).map Cw.subtype) := hR₀' ▸ inferInstance
  exact isCyclic_of_injective
    ((R₀ : Subgroup Cw).equivMapOfInjective _ Cw.subtype_injective).toMonoidHom
    (MulEquiv.injective _)

theorem conj_eq_or_eq_inv {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) {r' : C t}
    (hr'H : r' ∈ (multiplierHom F).range.comap κ) (hr'NZ : r' ∉ NZ t)
    (hr'o : orderOf r' = 2 ^ (n - 1))
    (h2elt : ∀ x ∈ (multiplierHom F).range.comap κ, (∃ k : ℕ, orderOf x = 2 ^ k) →
      x ∈ Subgroup.zpowers r') (htr : tInC t ∈ Subgroup.zpowers r') {u₀ u₁ : C t}
    (hu₀H : u₀ ∈ (multiplierHom F).range.comap κ) (hu₁H : u₁ ∈ (multiplierHom F).range.comap κ)
    (hu₀1 : u₀ ≠ 1) (hcop : Nat.Coprime (orderOf u₀) (2 * Nat.card (N t))) {b : G}
    (hb : b * (u₀ : G) * b⁻¹ = u₁) : b * (u₀ : G) * b⁻¹ = u₀ ∨ b * (u₀ : G) * b⁻¹ = (u₀ : G)⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hHcomm⟩ := multiplier_preimage_facts hD n hn S fS ht
  have hou : orderOf u₁ = orderOf u₀ := by
    rw [← Subgroup.orderOf_coe, ← hb, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
      Subgroup.orderOf_coe]
  have hu₁1 : u₁ ≠ 1 := by
    intro h
    apply hu₀1
    rw [← orderOf_eq_one_iff, ← hou, h, orderOf_one]
  set X := Subgroup.centralizer ({(u₁ : G)} : Set G)
  have hPw := antimultiplier_not_commute_of_coprime hD n hn S fS ht hu₁H hu₁1 (hou ▸ hcop)
  have hmax : ∀ R : Subgroup G, IsPGroup 2 R → Subgroup.zpowers (r' : G) ≤ R → R ≤ X →
      R = Subgroup.zpowers (r' : G) := fun R hR h1 h2 =>
    eq_zpowers_of_le_centralizer hD hr'H hr'NZ h2elt htr hPw hR h1 h2
  have hr'X : (r' : G) ∈ X := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hHcomm r' hr'H u₁ hu₁H)
  have hbr'X : b * (r' : G) * b⁻¹ ∈ X := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hb]
    have h1 : (r' : G) * u₀ = u₀ * r' := congrArg Subtype.val (hHcomm r' hr'H u₀ hu₀H)
    calc b * (r' : G) * b⁻¹ * (b * (u₀ : G) * b⁻¹) = b * ((r' : G) * u₀) * b⁻¹ := by group
      _ = b * ((u₀ : G) * r') * b⁻¹ := by rw [h1]
      _ = b * (u₀ : G) * b⁻¹ * (b * (r' : G) * b⁻¹) := by group
  have hr'p : IsPGroup 2 (Subgroup.zpowers (r' : G)) := by
    apply IsPGroup.of_card (n := n - 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hr'o]
  obtain ⟨Q₁, hQ₁⟩ := (hr'p.comap_of_injective _ X.subtype_injective).exists_le_sylow
  have hQ₁G : (Q₁ : Subgroup X).map X.subtype = Subgroup.zpowers (r' : G) := by
    apply hmax _ (Q₁.isPGroup'.map _)
    · intro x hx
      have hxX : x ∈ X := Subgroup.zpowers_le.mpr hr'X hx
      exact ⟨⟨x, hxX⟩, hQ₁ hx, rfl⟩
    · exact Subgroup.map_subtype_le _
  have hQ₁card : Nat.card Q₁ = 2 ^ (n - 1) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, hQ₁G, Nat.card_zpowers,
      Subgroup.orderOf_coe, hr'o]
  set B : Subgroup X := (Subgroup.zpowers (b * (r' : G) * b⁻¹)).subgroupOf X
  have hBcard : Nat.card B = Nat.card Q₁ := by
    rw [hQ₁card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hbr'X)).toEquiv, Nat.card_zpowers, ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hr'o]
  let BS : Sylow 2 X := Sylow.ofCard B (by rw [hBcard, Sylow.card_eq_multiplicity])
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X BS Q₁
  set g : G := (c : G) * b
  have hgr : g * (r' : G) * g⁻¹ ∈ Subgroup.zpowers (r' : G) := by
    rw [← hQ₁G]
    have h1 : (⟨b * (r' : G) * b⁻¹, hbr'X⟩ : X) ∈ (BS : Subgroup X) := by
      change _ ∈ B
      exact Subgroup.mem_zpowers _
    have h2 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) (BS : Subgroup X) h1
    rw [← Sylow.coe_subgroup_smul, hc] at h2
    refine ⟨_, h2, ?_⟩
    simp only [Subgroup.coe_subtype, MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv, g]
    group
  have htG : t ∈ Subgroup.zpowers (r' : G) := by
    obtain ⟨k, hk⟩ := htr
    exact ⟨k, by
      have h := congrArg Subtype.val hk
      simpa [tInC] using h⟩
  have hgC : g ∈ C t := mem_C_of_conj_mem_zpowers hD.orderOf_t htG hgr
  set gC : C t := ⟨g, hgC⟩
  have hgCr : gC * r' * gC⁻¹ ∈ (multiplierHom F).range.comap κ := by
    obtain ⟨k, hk⟩ := hgr
    have : gC * r' * gC⁻¹ = r' ^ k := Subtype.ext (by simpa [gC] using hk.symm)
    rw [this]
    exact Subgroup.zpow_mem _ hr'H k
  have hcu : g * (u₀ : G) * g⁻¹ = u₁ := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp c.2
    calc g * (u₀ : G) * g⁻¹ = (c : G) * (b * (u₀ : G) * b⁻¹) * (c : G)⁻¹ := by
          simp only [g]
          group
      _ = (c : G) * u₁ * (c : G)⁻¹ := by rw [hb]
      _ = u₁ := by rw [h1]; group
  rcases multiplier_or_antimultiplier hD hr'H hr'NZ hgCr with hgH | ⟨μ, hμ⟩
  · left
    have h1 : gC * u₀ = u₀ * gC := hHcomm gC hgH u₀ hu₀H
    have h2 : g * (u₀ : G) * g⁻¹ = u₀ := by
      have := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, gC] at this
      rw [this]
      group
    rw [hb, ← hcu, h2]
  · right
    have h1 := conj_eq_inv_of_antimultiplier hD n hn S fS ht hμ hu₀H hcop
    have h2 : g * (u₀ : G) * g⁻¹ = (u₀ : G)⁻¹ := by
      have := congrArg Subtype.val h1
      simpa [gC] using this
    rw [hb, ← hcu, h2]

theorem exists_torus_sylow_odd {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hG : Nat.card G = 2 * Nat.card (N t) * (p ^ f) ^ 3 * (p ^ f - 1) * ((p ^ f) ^ 3 + 1))
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀2 : p₀ ≠ 2) (hp₀q : p₀ ∣ p ^ f - 1) {r' : C t}
    (hr'H : r' ∈ (multiplierHom F).range.comap κ) (hr'NZ : r' ∉ NZ t)
    (hr'o : orderOf r' = 2 ^ (n - 1))
    (h2elt : ∀ x ∈ (multiplierHom F).range.comap κ, (∃ k : ℕ, orderOf x = 2 ^ k) →
      x ∈ Subgroup.zpowers r') (htr : tInC t ∈ Subgroup.zpowers r') :
    ∃ P : Sylow p₀ G, IsCyclic (P : Subgroup G) ∧ (P : Subgroup G) ≠ ⊥ ∧
      (∀ u ∈ (P : Subgroup G), ∃ hu : u ∈ C t,
        (⟨u, hu⟩ : C t) ∈ (multiplierHom F).range.comap κ) ∧
      (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) = 2 := by
  classical
  have hp := hD.prime
  have : Fact p₀.Prime := ⟨hp₀⟩
  obtain ⟨hcyc, -, hHcomm⟩ := multiplier_preimage_facts hD n hn S fS ht
  obtain ⟨-, hH'card⟩ := factorization_two_multiplier_preimage hD n hn S fS ht
  set H' := (multiplierHom F).range.comap κ
  set a := Nat.card (N t)
  set q := p ^ f with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hp.pos
  have hp₀a : ¬ p₀ ∣ 2 * a := by
    intro h
    rcases (Nat.Prime.dvd_mul hp₀).mp h with h2 | ha
    · exact hp₀2 ((Nat.prime_dvd_prime_iff_eq hp₀ Nat.prime_two).mp h2)
    · have h1 : p₀ ∣ Nat.gcd a (p * (q - 1)) := Nat.dvd_gcd ha (dvd_mul_of_dvd_right hp₀q p)
      rw [hD.core_coprime] at h1
      exact hp₀.one_lt.ne' (Nat.dvd_one.mp h1)
  have hp₀q3 : ¬ p₀ ∣ q ^ 3 * (q ^ 3 + 1) := by
    intro h
    rcases (Nat.Prime.dvd_mul hp₀).mp h with h3 | h3
    · have h4 : p₀ ∣ q := hp₀.dvd_of_dvd_pow h3
      have h5 : p₀ ∣ q - (q - 1) := Nat.dvd_sub h4 hp₀q
      rw [Nat.sub_sub_self hq1] at h5
      exact hp₀.one_lt.ne' (Nat.dvd_one.mp h5)
    · have h4 : q - 1 ∣ q ^ 3 - 1 := by
        simpa using Nat.pow_sub_one_dvd_pow_sub_one (x := q) (one_dvd 3)
      have h5 : p₀ ∣ q ^ 3 - 1 := hp₀q.trans h4
      have h6 : p₀ ∣ (q ^ 3 + 1) - (q ^ 3 - 1) := Nat.dvd_sub h3 h5
      have h7 : (q ^ 3 + 1) - (q ^ 3 - 1) = 2 := by
        have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
        omega
      rw [h7] at h6
      exact hp₀2 ((Nat.prime_dvd_prime_iff_eq hp₀ Nat.prime_two).mp h6)
  have hGH : Nat.card G = Nat.card H' * (q ^ 3 * (q ^ 3 + 1)) := by
    rw [hG, hH'card]
    ring
  have hfac : (Nat.card G).factorization p₀ = (Nat.card H').factorization p₀ := by
    have hne : q ^ 3 * (q ^ 3 + 1) ≠ 0 := by positivity
    rw [hGH, Nat.factorization_mul Nat.card_pos.ne' hne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hp₀q3, add_zero]
  let P' : Sylow p₀ H' := default
  set PG : Subgroup G := ((P' : Subgroup H').map H'.subtype).map (C t).subtype with hPG
  have hPGcard : Nat.card PG = p₀ ^ (Nat.card G).factorization p₀ := by
    rw [hPG, Subgroup.card_map_of_injective (C t).subtype_injective,
      Subgroup.card_map_of_injective H'.subtype_injective, Sylow.card_eq_multiplicity, hfac]
  let PS : Sylow p₀ G := Sylow.ofCard PG hPGcard
  have hPS : (PS : Subgroup G) = PG := rfl
  have hPGcyc : IsCyclic PG := isCyclic_of_injective
    (((P' : Subgroup H').equivMapOfInjective _ H'.subtype_injective).trans
      (((P' : Subgroup H').map H'.subtype).equivMapOfInjective _
        (C t).subtype_injective)).symm.toMonoidHom (MulEquiv.injective _)
  have hPGH : ∀ u ∈ PG, ∃ hu : u ∈ C t, (⟨u, hu⟩ : C t) ∈ H' := by
    rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    exact ⟨(x : C t).2, x.2⟩
  have hPGne : PG ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card PG = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hPGcard] at h1
    have h2 : p₀ ∣ Nat.card G := by
      rw [hGH, hH'card]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp₀q _) _
    have h3 := (Nat.Prime.dvd_iff_one_le_factorization hp₀ Nat.card_pos.ne').mp h2
    have h4 : p₀ ^ 1 ≤ p₀ ^ (Nat.card G).factorization p₀ := Nat.pow_le_pow_right hp₀.pos h3
    rw [pow_one, h1] at h4
    have := hp₀.one_lt
    omega
  refine ⟨PS, hPS ▸ hPGcyc, hPS ▸ hPGne, hPS ▸ hPGH, ?_⟩
  obtain ⟨u₀, hu₀⟩ := CFSG.CyclicBlocks.exists_eq_zpowers_of_isCyclic PG
  have hu₀PG : u₀ ∈ PG := hu₀ ▸ Subgroup.mem_zpowers u₀
  obtain ⟨hu₀C, hu₀H⟩ := hPGH u₀ hu₀PG
  set ū₀ : C t := ⟨u₀, hu₀C⟩
  have hū₀1 : ū₀ ≠ 1 := by
    intro h
    apply hPGne
    rw [hu₀, show u₀ = 1 from congrArg Subtype.val h, Subgroup.zpowers_one_eq_bot]
  have hcop : Nat.Coprime (orderOf ū₀) (2 * a) := by
    have hp₀grp : IsPGroup p₀ PG := hPS ▸ PS.isPGroup'
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hp₀grp ⟨u₀, hu₀PG⟩
    have hk' : orderOf u₀ = p₀ ^ k := by rw [← hk, Subgroup.orderOf_mk]
    rw [Subgroup.orderOf_mk, hk']
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp₀).mpr hp₀a)
  have hdich : ∀ b : G, b ∈ Subgroup.normalizer (PG : Set G) →
      b * u₀ * b⁻¹ = u₀ ∨ b * u₀ * b⁻¹ = u₀⁻¹ := by
    intro b hb
    have hb1 : b * u₀ * b⁻¹ ∈ PG := (Subgroup.mem_normalizer_iff.mp hb u₀).mp hu₀PG
    obtain ⟨hu₁C, hu₁H⟩ := hPGH _ hb1
    exact conj_eq_or_eq_inv hD n hn S fS ht hr'H hr'NZ hr'o h2elt htr hu₀H hu₁H hū₀1 hcop
      (u₁ := ⟨_, hu₁C⟩) rfl
  have hinvD : inversion F ∈ κ.range := hD.range_eq ▸ inversion_mem_coordinateD F
  obtain ⟨ũ, hũ⟩ := hinvD
  have hũanti : κ ũ = multiplier F 1 * inversion F := by
    rw [hũ]
    have : multiplier F 1 = 1 := by
      rw [← multiplierHom_apply, map_one]
    rw [this, one_mul]
  have hũu : ũ * ū₀ * ũ⁻¹ = ū₀⁻¹ :=
    conj_eq_inv_of_antimultiplier hD n hn S fS ht hũanti hu₀H hcop
  have hũu' : (ũ : G) * u₀ * (ũ : G)⁻¹ = u₀⁻¹ := by
    have := congrArg Subtype.val hũu
    simpa [ū₀] using this
  have hu₀inv : u₀⁻¹ ≠ u₀ := by
    intro h
    apply hū₀1
    have hsq : ū₀ ^ 2 = 1 := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, ū₀]
      rw [pow_two]
      nth_rewrite 1 [← h]
      exact inv_mul_cancel u₀
    have h1 : orderOf ū₀ ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl
      (h1.trans (dvd_mul_right 2 _)))
  have hcentr : ∀ x : G, x ∈ Subgroup.centralizer (PG : Set G) ↔ x * u₀ * x⁻¹ = u₀ := by
    intro x
    rw [hu₀, mem_centralizer_zpowers_iff]
    constructor
    · intro h
      rw [h]
      group
    · intro h
      calc x * u₀ = x * u₀ * x⁻¹ * x := by group
        _ = u₀ * x := by rw [h]
  have hconjmap : ∀ x : G, x * u₀ * x⁻¹ = u₀⁻¹ → ∀ y ∈ PG, x * y * x⁻¹ ∈ PG := by
    intro x hx y hy
    rw [hu₀] at hy ⊢
    obtain ⟨k, rfl⟩ := hy
    refine ⟨-k, ?_⟩
    simp only
    rw [← conj_zpow, hx, inv_zpow']
  have hũinv : (ũ : G)⁻¹ * u₀ * (ũ : G)⁻¹⁻¹ = u₀⁻¹ := by
    calc (ũ : G)⁻¹ * u₀ * (ũ : G)⁻¹⁻¹ = (ũ : G)⁻¹ * (u₀⁻¹)⁻¹ * ũ := by rw [inv_inv, inv_inv]
      _ = (ũ : G)⁻¹ * ((ũ : G) * u₀ * (ũ : G)⁻¹)⁻¹ * ũ := by rw [hũu']
      _ = u₀⁻¹ := by group
  have hũN : (ũ : G) ∈ Subgroup.normalizer (PG : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconjmap _ hũu' y, fun hy => ?_⟩
    have h1 := hconjmap _ hũinv _ hy
    have h2 : (ũ : G)⁻¹ * ((ũ : G) * y * (ũ : G)⁻¹) * (ũ : G)⁻¹⁻¹ = y := by group
    rwa [h2] at h1
  change (Subgroup.centralizer (PG : Set G)).relIndex (Subgroup.normalizer (PG : Set G)) = 2
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨ũ, hũN⟩, fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, hcentr, hcentr]
  rcases hdich b b.2 with h | h
  · have hbu : ((b : G) * ũ) * u₀ * ((b : G) * ũ)⁻¹ = u₀⁻¹ := by
      calc ((b : G) * ũ) * u₀ * ((b : G) * ũ)⁻¹
            = (b : G) * ((ũ : G) * u₀ * (ũ : G)⁻¹) * (b : G)⁻¹ := by group
        _ = ((b : G) * u₀ * (b : G)⁻¹)⁻¹ := by rw [hũu']; group
        _ = u₀⁻¹ := by rw [h]
    rw [hbu]
    exact Or.inr ⟨h, hu₀inv⟩
  · have hbu : ((b : G) * ũ) * u₀ * ((b : G) * ũ)⁻¹ = u₀ := by
      calc ((b : G) * ũ) * u₀ * ((b : G) * ũ)⁻¹
            = (b : G) * ((ũ : G) * u₀ * (ũ : G)⁻¹) * (b : G)⁻¹ := by group
        _ = ((b : G) * u₀ * (b : G)⁻¹)⁻¹ := by rw [hũu']; group
        _ = u₀ := by rw [h, inv_inv]
    rw [hbu, h]
    exact Or.inl ⟨rfl, hu₀inv⟩
theorem not_dvd_orderOf_mul_of_dvd_sub_one {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hG : Nat.card G = 2 * Nat.card (N t) * (p ^ f) ^ 3 * (p ^ f - 1) * ((p ^ f) ^ 3 + 1))
    [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (χ₁ χ₂ χ₃ : basis.index)
    (hodd : ∀ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      Odd (Module.finrank ℂ (basis.representation c).vector) ↔
        c = principal ∨ c = χ₁ ∨ c = χ₂ ∨ c = χ₃)
    (huniq : ∀ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ c' ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      Odd (Module.finrank ℂ (basis.representation c).vector) →
      Module.finrank ℂ (basis.representation c).vector =
        Module.finrank ℂ (basis.representation c').vector → c = c')
    (hχ₂B : χ₂ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hχ₃B : χ₃ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hχ₁ : Module.finrank ℂ (basis.representation χ₁).vector = (p ^ f) ^ 3)
    (hχ₂ : (basis.representation χ₂).character (fS (r n) : G) ≠
      (basis.representation χ₂).character ((fS (r n) : G) ^ 2))
    (hχ₃ : (basis.representation χ₃).character (fS (r n) : G) ≠
      (basis.representation χ₃).character ((fS (r n) : G) ^ 2)) :
    ∀ p₀ : ℕ, p₀.Prime → p₀ ≠ 2 → p₀ ∣ p ^ f - 1 → ∀ g : G, ¬ p * p₀ ∣ orderOf g := by
  classical
  intro p₀ hp₀ hp₀2 hp₀q g hg
  have hp := hD.prime
  have : Fact p₀.Prime := ⟨hp₀⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r', hconj, hr'H, hr'NZ, hr'o, h2elt, htr⟩ := exists_torus_sylow_two hD n hn S fS ht
  obtain ⟨P, hPcyc, hPne, hPH, hPidx⟩ :=
    exists_torus_sylow_odd hD n hn S fS ht hG hp₀ hp₀2 hp₀q hr'H hr'NZ hr'o h2elt htr
  obtain ⟨-, -, hHcomm⟩ := multiplier_preimage_facts hD n hn S fS ht
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  obtain ⟨⟨ideal₀, hmax₀, hmem₀⟩, hchar₀⟩ := CFSG.BlockBasics.residue_prime_existence p₀ hp₀
  have : ideal₀.IsMaximal := hmax₀
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₀) p₀ := hchar₀ ideal₀ hmax₀ hmem₀
  have : IsCyclic (P : Subgroup G) := hPcyc
  obtain ⟨ψ₁, ψ, δ, hδ, hψ₁ne, hψinj, hψne, hψ₁val, hψdeg, hψ₁real, hψreal, hψ3⟩ :=
    CFSG.CyclicBlocks.principal_block_cyclic_sylow_inertial_index_two basis ideal₀ p₀ hp₀2
      principal hprincipal P hPcyc hPidx
  obtain ⟨kP, hkP⟩ := P.isPGroup'.exists_card_eq
  have hkP1 : 1 ≤ kP := by
    rcases kP with _ | kP
    · exfalso
      apply hPne
      rw [← Subgroup.card_eq_one]
      simpa using hkP
    · omega
  have hP3 : 3 ≤ Nat.card P := by
    rw [hkP]
    calc 3 ≤ p₀ := by
          rcases hp₀.eq_two_or_odd with h | h
          · exact absurd h hp₀2
          · have := hp₀.two_le
            omega
      _ = p₀ ^ 1 := (pow_one p₀).symm
      _ ≤ p₀ ^ kP := Nat.pow_le_pow_right hp₀.pos hkP1
  obtain ⟨ψ', ε, hε, hψ'ne, hψ'real, hψ'odd, hψ'val⟩ : ∃ (ψ' : basis.index) (ε : ℤ),
      (ε = 1 ∨ ε = -1) ∧ ψ' ≠ principal ∧
      (∀ x : G, starRingEnd ℂ ((basis.representation ψ').character x) =
        (basis.representation ψ').character x) ∧
      Odd (Module.finrank ℂ (basis.representation ψ').vector) ∧
      ∀ x : G, p₀ ∣ orderOf x → (basis.representation ψ').character x = ε := by
    by_cases hodd₁ : Odd (Module.finrank ℂ (basis.representation ψ₁).vector)
    · exact ⟨ψ₁, δ, hδ, hψ₁ne, hψ₁real, hodd₁, hψ₁val⟩
    ·
      have hoddμ : ∀ μ ∈ Finset.Icc 1 ((Nat.card P - 1) / 2),
          Odd (Module.finrank ℂ (basis.representation (ψ μ)).vector) := by
        intro μ hμ
        have h1 := hψdeg μ hμ
        rw [Nat.not_odd_iff_even] at hodd₁
        obtain ⟨m, hm⟩ := hodd₁
        rcases hδ with rfl | rfl
        · refine ⟨m, ?_⟩
          have : (Module.finrank ℂ (basis.representation (ψ μ)).vector : ℤ) = 2 * m + 1 := by
            rw [h1, hm]
            push_cast
            ring
          exact_mod_cast this
        · have h3 : (0 : ℤ) ≤ (Module.finrank ℂ (basis.representation (ψ μ)).vector : ℤ) :=
            Int.natCast_nonneg _
          have h4 : (Module.finrank ℂ (basis.representation (ψ μ)).vector : ℤ) =
              2 * (m : ℤ) - 1 := by
            rw [h1, hm]
            push_cast
            ring
          have hm0 : 1 ≤ m := by omega
          refine ⟨m - 1, ?_⟩
          have : (Module.finrank ℂ (basis.representation (ψ μ)).vector : ℤ) =
              2 * ((m - 1 : ℕ) : ℤ) + 1 := by
            rw [h4]
            push_cast [hm0]
            ring
          exact_mod_cast this
      by_cases hPeq : Nat.card P = 3
      · have h1 : (1 : ℕ) ∈ Finset.Icc 1 ((Nat.card P - 1) / 2) := by
          rw [hPeq]
          simp
        refine ⟨ψ 1, -δ, ?_, (hψne 1 h1).1, hψreal 1 h1, hoddμ 1 h1, ?_⟩
        · rcases hδ with rfl | rfl
          · right
            norm_num
          · left
            norm_num
        · intro x hx
          rw [hψ3 hPeq x hx]
          push_cast
          ring
      · exfalso
        have hP5 : 2 ≤ (Nat.card P - 1) / 2 := by
          have hPodd : Odd (Nat.card P) := by
            rw [hkP]
            exact (hp₀.eq_two_or_odd'.resolve_left hp₀2).pow
          obtain ⟨m, hm⟩ := hPodd
          omega
        have h1 : (1 : ℕ) ∈ Finset.Icc 1 ((Nat.card P - 1) / 2) := by
          simp only [Finset.mem_Icc]
          omega
        have h2 : (2 : ℕ) ∈ Finset.Icc 1 ((Nat.card P - 1) / 2) := by
          simp only [Finset.mem_Icc]
          omega
        have hB1 := real_valued_odd_degree_irreducible_mem_principal_two_block basis ideal
          principal hprincipal (ψ 1) (hψreal 1 h1) (hoddμ 1 h1)
        have hB2 := real_valued_odd_degree_irreducible_mem_principal_two_block basis ideal
          principal hprincipal (ψ 2) (hψreal 2 h2) (hoddμ 2 h2)
        have hdeg12 : Module.finrank ℂ (basis.representation (ψ 1)).vector =
            Module.finrank ℂ (basis.representation (ψ 2)).vector := by
          have := (hψdeg 1 h1).trans (hψdeg 2 h2).symm
          exact_mod_cast this
        have := hψinj (Finset.mem_coe.mpr h1) (Finset.mem_coe.mpr h2)
          (huniq _ hB1 _ hB2 (hoddμ 1 h1) hdeg12)
        omega
  have hψ'B : ψ' ∈ B := real_valued_odd_degree_irreducible_mem_principal_two_block basis ideal
    principal hprincipal ψ' hψ'real hψ'odd
  have hεne : (ε : ℂ) ≠ 0 := by
    rcases hε with rfl | rfl <;> norm_num
  rcases (hodd ψ' hψ'B).mp hψ'odd with h | h | h | h
  · exact hψ'ne h
  ·
    subst h
    have hfac : (Nat.card G).factorization p = 3 * f := by
      rw [hG, show 2 * Nat.card (N t) * (p ^ f) ^ 3 * (p ^ f - 1) * ((p ^ f) ^ 3 + 1) =
        p ^ (3 * f) * (2 * Nat.card (N t) * (p ^ f - 1) * ((p ^ f) ^ 3 + 1)) by ring_nf]
      apply factorization_prime_pow_mul hp
      intro hdvd
      have hKp := (unitaryK_properties hD).2.2.1
      rw [(unitaryLocalData_card hD).1] at hKp
      have hpq : p ∣ p ^ f := dvd_pow_self p (by have := hD.one_le; omega)
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
      · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
        · exact hKp h2
        · have h3 : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub hpq h2
          rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h3
          exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
      · have h4 : p ∣ (p ^ f) ^ 3 := dvd_pow hpq (by norm_num)
        have h5 : p ∣ (p ^ f) ^ 3 + 1 - (p ^ f) ^ 3 := Nat.dvd_sub h1 h4
        rw [Nat.add_sub_cancel_left] at h5
        exact hp.one_lt.ne' (Nat.dvd_one.mp h5)
    have hzero := CFSG.DefectZeroSylow.character_eq_zero_of_finrank_dvd
      (basis.representation ψ').representation (basis.irreducible ψ')
      (by rw [hfac, hχ₁, ← pow_mul, mul_comm]) (dvd_of_mul_right_dvd hg)
    have hval := hψ'val g (dvd_of_mul_left_dvd hg)
    exact hεne (hval.symm.trans hzero)
  all_goals
    subst h
    obtain ⟨⟨u, huP⟩, hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
    have hu1 : u ≠ 1 := fun h' => hu1' (Subtype.ext h')
    obtain ⟨huC, huH⟩ := hPH u huP
    set ū : C t := ⟨(u : G), huC⟩
    have hū1 : ū ≠ 1 := fun h' => hu1 (congrArg Subtype.val h')
    have hcomm : (r' : G) * u = u * r' := congrArg Subtype.val (hHcomm r' hr'H ū huH)
    obtain ⟨ku, hku⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨u, huP⟩
    have hku' : orderOf (u : G) = p₀ ^ ku := by rw [← hku, Subgroup.orderOf_mk]
    have hku1 : 1 ≤ ku := by
      rcases ku with _ | ku
      · exfalso
        apply hu1
        rw [pow_zero] at hku'
        exact orderOf_eq_one_iff.mp hku'
      · omega
    have hval : ∀ v : ℕ, (v = 1 ∨ v = 2) →
        (basis.representation ψ').character (((r' : G) ^ v) * u) =
          (basis.representation ψ').character ((r' : G) ^ v) := by
      intro v hv
      have hw2 : orderOf ((r' : G) ^ v) ∣ 2 ^ (n - 1) :=
        (orderOf_pow_dvd v).trans (by rw [Subgroup.orderOf_coe, hr'o])
      have hrw : (r' : G) * (r' : G) ^ v = (r' : G) ^ v * r' := (Commute.self_pow _ v).eq
      have hPw := antimultiplier_not_commute_rotation hD n hn hr'H hr'o h2elt hv
      have hcyc := exists_cyclic_sylow_centralizer hD hr'H hr'NZ hr'o h2elt htr hrw hPw
      have huw : (u : G) ∈ Subgroup.centralizer (Subgroup.zpowers ((r' : G) ^ v) : Set G) := by
        rw [mem_centralizer_zpowers_iff]
        exact (Commute.pow_left hcomm.symm.symm v).eq.symm ▸ (Commute.pow_left hcomm v).eq.symm
      have huodd : Odd (orderOf (u : G)) := by
        rw [hku']
        exact (hp₀.eq_two_or_odd'.resolve_left hp₀2).pow
      exact principal_character_section_eq basis ideal principal hprincipal hw2 hcyc hψ'B huw
        huodd
    have hsing : ∀ v : ℕ, (v = 1 ∨ v = 2) → p₀ ∣ orderOf (((r' : G) ^ v) * u) := by
      intro v hv
      have hc : Commute ((r' : G) ^ v) u := Commute.pow_left hcomm v
      have hcop : Nat.Coprime (orderOf ((r' : G) ^ v)) (orderOf (u : G)) := by
        have h1 : orderOf ((r' : G) ^ v) ∣ 2 ^ (n - 1) :=
          (orderOf_pow_dvd v).trans (by rw [Subgroup.orderOf_coe, hr'o])
        rw [hku']
        exact Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow _ _
          ((Nat.coprime_primes Nat.prime_two hp₀).mpr (Ne.symm hp₀2)))
      rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hku']
      exact dvd_mul_of_dvd_right (dvd_pow_self p₀ (by omega)) _
    have hconj2 : ∀ v : ℕ, (basis.representation ψ').character ((r' : G) ^ v) =
        (basis.representation ψ').character ((fS (r n) : G) ^ v) := by
      intro v
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      rw [← hc, conj_pow]
      exact (Representation.char_conj _ _ _).symm
    have h1 := hval 1 (Or.inl rfl)
    have h2 := hval 2 (Or.inr rfl)
    rw [hψ'val _ (hsing 1 (Or.inl rfl)), hconj2, pow_one] at h1
    rw [hψ'val _ (hsing 2 (Or.inr rfl)), hconj2] at h2
    first
      | exact hχ₂ (h1.symm.trans h2)
      | exact hχ₃ (h1.symm.trans h2)

end CFSG.Semidihedral.UnitaryBranch
