module

public import CFSG.Timmesfeld.Bridge.Asc72Unitary
public import CFSG.CGT.Timmesfeld75.Inputs214

public section

namespace CFSG.CGT.T75N

open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.Open
open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.BenderSuzuki.External Matrix

theorem exists_ne_one_commute_two_of_unitary {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (Q Q' : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ c : ProjectiveSpecialUnitaryMatrixGroup J, c ≠ 1 ∧
      (∀ z ∈ Subgroup.center (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
        Commute (z : ProjectiveSpecialUnitaryMatrixGroup J) c) ∧
      ∀ z ∈ Subgroup.center (Q' : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
        Commute (z : ProjectiveSpecialUnitaryMatrixGroup J) c := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have hfBB := bender_projectiveSpecialUnitary_borel J f hf hcard hfixed hJ
  obtain ⟨hconj, -, -, -, -, rho, -, -, -, htwo, hstabα, -, hUnormal, -, hUT, -, -, -, ⟨S, hS⟩,
    -, -, -, -, hinvB, -, ⟨w, -, hwα, hwβ⟩, hswap⟩ :=
    unitary_three_point_structure J f hf hcard hfixed hJ
  set α := unitaryOuterIsotropicPoint J hJ 0 (by decide) with hα
  set β := unitaryOuterIsotropicPoint J hJ 2 (by decide) with hβ
  set U := (hermitianUnipotentPSU J hJ).range with hU
  set B := unitaryCoordinateStabilizer J 0 with hB
  have hmemB : ∀ g : G, g ∈ B ↔ rho g α = α := fun g => by
    rw [← hstabα]
    rfl
  have hUB : ∀ u ∈ U, u ∈ B := fun u hu => hUT ▸ Subgroup.mem_sup_left hu
  have hαβ : α ≠ β := fun h => unitaryCoordinatePoint_two_ne_zero (congrArg Subtype.val h).symm
  obtain ⟨c, hcq, hc3⟩ := exists_unit_pow_succ_eq_one (K := K) (q := 2 ^ f)
    (by calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf) hcard
  have hcK : (c : K) * J.conj c = 1 := by
    rw [hconj, ← pow_succ', ← Units.val_pow_eq_pow_val, hcq, Units.val_one]
  set τ : G := torusPSU J hJ c with hτ
  have hτ1 : τ ≠ 1 := torusPSU_ne_one J hJ hcK hc3
  have hτα : ∀ g : G, rho g α = α → orderOf g = 2 → Commute g τ := by
    intro g hg hg2
    obtain ⟨b, M, -, -, hM, hgM⟩ := (hinvB g).mp ⟨(hmemB g).mpr hg, hg2⟩
    exact commute_torusPSU_of_root J hJ hcK hM hgM
  have hτw : Commute w τ := by
    have h := (hswap w hwα hwβ).1 c
    have hcinv : (c ^ (2 ^ f))⁻¹ = c := by
      rw [inv_eq_iff_eq_inv]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hcq])
    rw [hcinv] at h
    change w * τ = τ * w
    calc w * τ = w * (w⁻¹ * τ * w) := by rw [h]
      _ = τ * w := by group
  have hτβ : ∀ g : G, rho g β = β → orderOf g = 2 → Commute g τ := by
    intro g hg hg2
    have hs : rho (w⁻¹ * g * w) α = α := by
      rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hwα, hg,
        Equiv.Perm.inv_eq_iff_eq, hwα]
    have hs2 : orderOf (w⁻¹ * g * w) = 2 := by
      rw [← inv_inv w, inv_inv w⁻¹, orderOf_mul_mul_inv, hg2]
    have hcs := hτα _ hs hs2
    have hg' : g = w * (w⁻¹ * g * w) * w⁻¹ := by group
    rw [hg']
    exact (hτw.mul_left hcs).mul_left hτw.inv_left
  have hτZ : ∀ z ∈ U, (∀ u ∈ U, Commute u z) → Commute z τ := by
    intro z hz hcz
    have hsq : z ^ 2 = 1 := by
      have hzS : z ∈ (S : Subgroup G) := hS ▸ hz
      have := (hfBB S).2.2.1 ⟨z, hzS⟩ (Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (hcz g (hS ▸ g.2)).eq)
      exact congrArg Subtype.val this
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h1 | h2
    · rw [orderOf_eq_one_iff] at h1
      rw [h1]
      exact Commute.one_left τ
    · exact hτα z ((hmemB z).mp (hUB z hz)) h2
  have hconjU : ∀ h : G, rho h α = α → ∀ u ∈ U, h * u * h⁻¹ ∈ U := by
    intro h hh u hu
    have := hUnormal.conj_mem ⟨u, hUB u hu⟩ (Subgroup.mem_subgroupOf.mpr hu) ⟨h, (hmemB h).mpr hh⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  have hconjZ : ∀ h : G, rho h α = α → ∀ z ∈ U, (∀ u ∈ U, Commute u z) →
      h * z * h⁻¹ ∈ U ∧ ∀ u ∈ U, Commute u (h * z * h⁻¹) := by
    intro h hh z hz hcz
    refine ⟨hconjU h hh z hz, fun u hu => ?_⟩
    have hh' : rho h⁻¹ α = α := by
      rw [map_inv, Equiv.Perm.inv_eq_iff_eq, hh]
    have h1 := (hcz _ (hconjU h⁻¹ hh' u hu)).conj h
    have e : h * (h⁻¹ * u * h⁻¹⁻¹) * h⁻¹ = u := by group
    rwa [e] at h1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G S (g • Q')
  have hinv2 : ∀ y : G, y * y = 1 → y = 1 ∨ orderOf y = 2 := fun y hy => by
    by_cases h1 : y = 1
    · exact Or.inl h1
    · exact Or.inr (orderOf_eq_prime (by rw [pow_two]; exact hy) h1)
  have hsq' : ∀ z ∈ Subgroup.center (Q' : Subgroup G), (z : G) * z = 1 := by
    intro z hz
    have := congrArg Subtype.val ((hfBB Q').2.2.1 z hz)
    simpa [pow_two] using this
  have hzfix : ∀ z ∈ Subgroup.center (Q' : Subgroup G),
      rho (g * (z : G) * g⁻¹) (rho x α) = rho x α := by
    intro z hz
    have hy : g * (z : G) * g⁻¹ ∈ ((g • Q' : Sylow 2 G) : Subgroup G) := by
      rw [mem_smul_sylow_iff]
      simp [mul_assoc]
    rw [← hx, mem_smul_sylow_iff] at hy
    have h1 := (hmemB _).mp (hUB _ (hS ▸ hy))
    rwa [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_eq_iff_eq] at h1
  have hsq'' : ∀ z ∈ Subgroup.center (Q' : Subgroup G),
      (g * (z : G) * g⁻¹) * (g * (z : G) * g⁻¹) = 1 := by
    intro z hz
    have e : (g * (z : G) * g⁻¹) * (g * (z : G) * g⁻¹) = g * ((z : G) * z) * g⁻¹ := by group
    rw [e, hsq' z hz]; group
  obtain ⟨h, hhα, hcomm⟩ : ∃ h : G, rho h α = α ∧
      ∀ z ∈ Subgroup.center (Q' : Subgroup G), Commute (h * (g * (z : G) * g⁻¹) * h⁻¹) τ := by
    by_cases hp : rho x α = α
    · refine ⟨1, by rw [map_one, Equiv.Perm.one_apply], fun z hz => ?_⟩
      rw [one_mul, inv_one, mul_one]
      rcases hinv2 _ (hsq'' z hz) with h1 | h2
      · rw [h1]; exact Commute.one_left τ
      · exact hτα _ (by simpa [hp] using hzfix z hz) h2
    · obtain ⟨h, hh1, hh2⟩ := htwo α (rho x α) α β (Ne.symm hp) hαβ
      refine ⟨h, hh1, fun z hz => ?_⟩
      rcases hinv2 _ (hsq'' z hz) with h1 | h2
      · rw [h1]; simp
      · refine hτβ _ ?_ (by rw [orderOf_mul_mul_inv, h2])
        rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hh2,
          Equiv.Perm.inv_eq_iff_eq.mpr rfl, hzfix z hz]
  set φ := MulAut.conj (h * g) with hφ
  have hφz : ∀ z : G, φ z = h * (g * z * g⁻¹) * h⁻¹ := by
    intro z
    rw [hφ, MulAut.conj_apply]
    group
  refine ⟨φ.symm τ, (MulEquiv.map_ne_one_iff φ.symm).mpr hτ1, fun z hz => ?_, fun z hz => ?_⟩
  · have hzS : g * (z : G) * g⁻¹ ∈ U := by
      rw [← hS, ← hg, mem_smul_sylow_iff]
      simp [mul_assoc]
    have hzc : ∀ u ∈ U, Commute u (g * (z : G) * g⁻¹) := by
      intro u hu
      rw [← hS, ← hg, mem_smul_sylow_iff] at hu
      have h2 : Commute (g⁻¹ * u * g) (z : G) :=
        Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hz ⟨_, hu⟩)
      have h3 := h2.conj g
      have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
      rwa [e] at h3
    obtain ⟨-, hcZ⟩ := hconjZ h hhα _ hzS hzc
    have := (hφz z ▸ hτZ _ (hconjU h hhα _ hzS) hcZ).map φ.symm
    rwa [MulEquiv.symm_apply_apply] at this
  · have := (hφz z ▸ hcomm z hz).map φ.symm
    rwa [MulEquiv.symm_apply_apply] at this


theorem exists_ne_one_commute_two_of_psu3 {X : Type*} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (e : X ≃* PSU3Model n) (Q Q' : Sylow 2 X) :
    ∃ c : X, c ≠ 1 ∧ (∀ z ∈ Subgroup.center (Q : Subgroup X), Commute (z : X) c) ∧
      ∀ z ∈ Subgroup.center (Q' : Subgroup X), Commute (z : X) c := by
  let J := binaryQuadraticHermitian n (by omega)
  have hEcard : Nat.card (FiniteField.Extension (GaloisField 2 n) 2 2) = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : FiniteField.Extension (GaloisField 2 n) 2 2 // J.conj x = x} =
      2 ^ n := quadraticBinaryFrobenius_fixed_card n (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  obtain ⟨e'⟩ := projectiveSpecialUnitary_equiv_PSU3Model J n hn hJ hEcard hfixed
  let φ : X ≃* ProjectiveSpecialUnitaryMatrixGroup J := e.trans e'.symm
  have : Finite X := Finite.of_injective φ φ.injective
  let Q₁ : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Q.mapSurjective (f := φ.toMonoidHom) φ.surjective
  let Q₂ : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Q'.mapSurjective (f := φ.toMonoidHom) φ.surjective
  obtain ⟨c, hc1, hzc, hzc'⟩ := exists_ne_one_commute_two_of_unitary J n hn hEcard hfixed hJ Q₁ Q₂
  have transport : ∀ (R : Sylow 2 X) (R₁ : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)),
      R₁ = R.mapSurjective (f := φ.toMonoidHom) φ.surjective →
      (∀ z ∈ Subgroup.center (R₁ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
        Commute (z : ProjectiveSpecialUnitaryMatrixGroup J) c) →
      ∀ z ∈ Subgroup.center (R : Subgroup X), Commute (z : X) (φ.symm c) := by
    intro R R₁ hR₁ hzc z hz
    subst hR₁
    have hz' : (⟨φ z, Subgroup.mem_map_of_mem _ z.2⟩ :
        ((R.mapSurjective (f := φ.toMonoidHom) φ.surjective :
          Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
          Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) ∈
        Subgroup.center ((R.mapSurjective (f := φ.toMonoidHom) φ.surjective :
          Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
          Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨y, hy⟩
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      apply Subtype.ext
      have h1 := Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hz ⟨y', hy'⟩)
      simp only [Subgroup.coe_mul] at h1 ⊢
      change φ y' * φ z = φ z * φ y'
      rw [← map_mul, ← map_mul, h1]
    have := (hzc _ hz').map φ.symm
    rwa [MulEquiv.symm_apply_apply] at this
  exact ⟨φ.symm c, (MulEquiv.map_ne_one_iff φ.symm).mpr hc1, transport Q Q₁ rfl hzc,
    transport Q' Q₂ rfl hzc'⟩


theorem sup_conj_ne_top_of_psu3 {X : Type*} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (e : X ≃* PSU3Model n) (A : Subgroup X) (hA2 : ∀ a ∈ A, a * a = 1) (g : X) :
    A ⊔ A.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
  have : Finite (PSU3Model n) := by
    have : Finite (ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * n))) :=
      Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
    exact Subtype.finite
  have : Finite X := Finite.of_injective e e.injective
  have hB : IsBenderGroup X := IsBenderGroup.isPSU3 n hn e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAp : IsPGroup 2 A := fun x => ⟨1, by
    have := hA2 x x.2
    rw [pow_one, pow_two]
    exact Subtype.ext this⟩
  obtain ⟨Q, hAQ⟩ := hAp.exists_le_sylow
  obtain ⟨c, hc1, hzc, hzc'⟩ := exists_ne_one_commute_two_of_psu3 hn e Q (g • Q)
  have hA1 : A ≤ Subgroup.centralizer {c} := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz : (⟨a, hAQ ha⟩ : (Q : Subgroup X)) ∈ Subgroup.center (Q : Subgroup X) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (IsBenderGroup.commute_of_mul_self_eq_one hB Q (hAQ ha) (hA2 a ha) y
        y.2).symm
    exact (hzc _ hz).eq
  have hA2' : A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer {c} := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmem : (MulAut.conj g).toMonoidHom a ∈ ((g • Q : Sylow 2 X) : Subgroup X) := by
      rw [mem_smul_sylow_iff]
      have e1 : g⁻¹ * ((MulAut.conj g).toMonoidHom a) * g = a := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e1]
      exact hAQ ha
    have hsq : ((MulAut.conj g).toMonoidHom a) * ((MulAut.conj g).toMonoidHom a) = 1 := by
      rw [← map_mul, hA2 a ha, map_one]
    have hz : (⟨(MulAut.conj g).toMonoidHom a, hmem⟩ : ((g • Q : Sylow 2 X) : Subgroup X)) ∈
        Subgroup.center ((g • Q : Sylow 2 X) : Subgroup X) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (IsBenderGroup.commute_of_mul_self_eq_one hB (g • Q) hmem hsq y y.2).symm
    exact (hzc' _ hz).eq
  intro htop
  have hle : A ⊔ A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer {c} :=
    sup_le hA1 hA2'
  rw [htop] at hle
  have hcZ : c ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun y =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top y))
  have := IsBenderGroup.isSimpleGroup hB
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with h | h
  · rw [h, Subgroup.mem_bot] at hcZ
    exact hc1 hcZ
  · obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hB
    have ha : a ∈ Subgroup.center X := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm


theorem unitaryTwoGenerationInput : CFSG.CGT.Timmesfeld75.UnitaryTwoGenerationInput := by
  intro K _ _ T hT _ _ ⟨f, hf, ⟨e⟩⟩ g htop
  let π : K →* PSU3Model f := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hA2 : ∀ a ∈ T.map π, a * a = 1 := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 ha
    rw [← map_mul, ← pow_two, hT.1.2 t ht, map_one]
  apply sup_conj_ne_top_of_psu3 hf (MulEquiv.refl _) (T.map π) hA2 (π g)
  have hmap : (CFSG.CGT.Timmesfeld75.conjSubgroup g T).map π =
      (T.map π).map (MulAut.conj (π g)).toMonoidHom := by
    unfold CFSG.CGT.Timmesfeld75.conjSubgroup
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext t
    simp [MulAut.conj_apply]
  rw [← hmap, ← Subgroup.map_sup, htop, Subgroup.map_top_of_surjective π hπs]

end CFSG.CGT.T75N
