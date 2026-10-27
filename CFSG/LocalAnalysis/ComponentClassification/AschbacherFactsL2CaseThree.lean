module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Field
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Quaternion
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Dickson

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.GorensteinWalter

theorem two_le_of_ringEquiv_ne_one {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hKcard : Nat.card K = p ^ f) {σ : K ≃+* K} (hσ : σ ≠ 1) : 2 ≤ f := by
  have : Finite (K ≃+* K) := Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
    intro e e' h
    ext x
    exact congrFun h x)
  have h1 : 1 < Nat.card (K ≃+* K) := Finite.one_lt_card_iff_nontrivial.mpr ⟨σ, 1, hσ⟩
  rw [card_ringEquiv_of_card hp hKcard] at h1
  omega

@[expose] noncomputable def restrictConjPSL {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {γ : PGammaL2 K}
    (hγ : γ ^ 2 = 1) (H : Subgroup (PSL2 K)) (hH : ∀ x ∈ H, conjPSL K hK hcard γ x ∈ H) :
    MulAut H :=
  restrictMulAut (conjPSL K hK hcard γ) H (fun x => ⟨hH x, fun hx => by
    have h1 := hH _ hx
    have h2 : conjPSL K hK hcard γ (conjPSL K hK hcard γ x) = x := by
      rw [conjPSL_eq_iff, psl2Incl_conjPSL]
      calc γ * (γ * psl2Incl K x * γ⁻¹) * γ⁻¹ = (γ * γ) * psl2Incl K x * (γ * γ)⁻¹ := by group
        _ = psl2Incl K x := by rw [← pow_two, hγ]; group
    rwa [h2] at h1⟩)

theorem restrictConjPSL_apply {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {γ : PGammaL2 K}
    (hγ : γ ^ 2 = 1) (H : Subgroup (PSL2 K)) (hH : ∀ x ∈ H, conjPSL K hK hcard γ x ∈ H)
    (x : H) : (restrictConjPSL hK hcard hγ H hH x : PSL2 K) = conjPSL K hK hcard γ x := rfl

theorem restrictConjPSL_involutive {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {γ : PGammaL2 K}
    (hγ : γ ^ 2 = 1) (H : Subgroup (PSL2 K)) (hH : ∀ x ∈ H, conjPSL K hK hcard γ x ∈ H)
    (x : H) : restrictConjPSL hK hcard hγ H hH (restrictConjPSL hK hcard hγ H hH x) = x := by
  apply Subtype.ext
  rw [restrictConjPSL_apply, restrictConjPSL_apply, conjPSL_eq_iff, psl2Incl_conjPSL]
  calc γ * (γ * psl2Incl K x * γ⁻¹) * γ⁻¹ = (γ * γ) * psl2Incl K x * (γ * γ)⁻¹ := by group
    _ = psl2Incl K x := by rw [← pow_two, hγ]; group

theorem conjPSL_eq_self_of_commute {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {γ : PGammaL2 K}
    {x : PSL2 K} (h : γ * psl2Incl K x = psl2Incl K x * γ) : conjPSL K hK hcard γ x = x := by
  rw [conjPSL_eq_iff, h]
  group

theorem perm_four_eq_one_of_commute_alternating : ∀ σ : Equiv.Perm (Fin 4),
    (∀ a : alternatingGroup (Fin 4), σ * a = a * σ) → σ = 1 := by
  decide

theorem case_three_psl2 {K : Type} [Field K] [Finite K] {p f : ℕ} [hp : Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {z : PSL2 K} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) {u : PGammaL2 K} (hu2 : u ^ 2 = 1)
    (hufield : u.right ≠ 1) (huz : u * psl2Incl K z = psl2Incl K z * u)
    (H : Subgroup (PSL2 K)) (hinvu : ∀ x ∈ H, conjPSL K hK hcard u x ∈ H)
    (hinvuz : ∀ x ∈ H, conjPSL K hK hcard (u * psl2Incl K z) x ∈ H)
    (hP1u : ∀ x, u * psl2Incl K x = psl2Incl K x * u → Odd (orderOf x) → x ∈ H)
    (hP1uz : ∀ x, u * psl2Incl K z * psl2Incl K x = psl2Incl K x * (u * psl2Incl K z) →
      Odd (orderOf x) → x ∈ H)
    (hP2 : ∀ y, z ∈ Subgroup.zpowers y → y ∈ H) : H = ⊤ := by
  classical
  have hf2 : 2 ≤ f := two_le_of_ringEquiv_ne_one hp.out hKcard hufield
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hqodd := odd_card_of_isOddPrimePower hK
    rw [hKcard] at hqodd
    exact (Nat.not_even_iff_odd.mpr hqodd) ((Nat.even_pow' (by omega)).mpr even_two)
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have huz2 : (u * psl2Incl K z) ^ 2 = 1 := by
    rw [pow_two]
    calc u * psl2Incl K z * (u * psl2Incl K z) = u * (psl2Incl K z * u) * psl2Incl K z := by
          group
      _ = u ^ 2 * psl2Incl K (z ^ 2) := by rw [← huz, map_pow]; simp only [pow_two, mul_assoc]
      _ = 1 := by rw [hu2, hz2, map_one, one_mul]
  have huzfield : (u * psl2Incl K z).right ≠ 1 := by
    rw [SemidirectProduct.mul_right, psl2Incl_apply, SemidirectProduct.right_inl, mul_one]
    exact hufield
  obtain ⟨r₁, r₂, h₁p, h₁1, h₂p, h₂1, h₁₂, hu₁, hu₂⟩ :=
    field_involution_fixed_root_pair hKcard hK hcard hu2 hufield
  obtain ⟨s₁, -, hs₁p, hs₁1, -, -, -, hus₁, -⟩ :=
    field_involution_fixed_root_pair hKcard hK hcard huz2 huzfield
  have hoddp : ∀ {x : PSL2 K}, x ^ p = 1 → x ≠ 1 → Odd (orderOf x) := by
    intro x hx hx1
    rw [orderOf_eq_prime hx hx1]
    exact hpodd
  have hr₁H := hP1u r₁ hu₁ (hoddp h₁p h₁1)
  have hr₂H := hP1u r₂ hu₂ (hoddp h₂p h₂1)
  have hs₁H := hP1uz s₁ hus₁ (hoddp hs₁p hs₁1)
  obtain ⟨c, hzc, hceven, hcord, -⟩ := psl2_torus_of_involution hK hz2 hz1
  have hcH := hP2 c hzc
  have hzH := hP2 z (Subgroup.mem_zpowers z)
  have hq9 : 9 ≤ Nat.card K := by
    rw [hKcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left (by have := hp.out.two_le; omega) 2
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.out.pos hf2
  have hqodd := odd_card_of_isOddPrimePower hK
  have hc4 : 4 ≤ orderOf c := by
    obtain ⟨k, hk⟩ := hqodd
    obtain ⟨j, hj⟩ := hceven
    rcases hcord with h | h <;> omega
  have hqc : Nat.card K ≤ 2 * orderOf c + 1 := by
    obtain ⟨k, hk⟩ := hqodd
    rcases hcord with h | h <;> omega
  rcases dickson_root_pair hKcard hK hf2 H hr₁H hr₂H hcH h₁p h₁1 h₂p h₁₂ hc4 hqc with
    h | ⟨h9, ⟨-, ⟨e⟩⟩ | ⟨h5, -⟩⟩
  · exact h
  ·
    exfalso
    obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_nine hp.out (hKcard ▸ h9)
    let α := restrictConjPSL hK hcard hu2 H hinvu
    let β := restrictConjPSL hK hcard huz2 H hinvuz
    have hfixα := (fix_commutator_of_equiv_perm_four e α
      (restrictConjPSL_involutive hK hcard hu2 H hinvu) (y := ⟨r₁, hr₁H⟩)
      (Subtype.ext (by simpa using h₁p)) (fun h => h₁1 (congrArg Subtype.val h))
      (Subtype.ext (conjPSL_eq_self_of_commute hK hcard hu₁))).1
    have hfixβ := (fix_commutator_of_equiv_perm_four e β
      (restrictConjPSL_involutive hK hcard huz2 H hinvuz) (y := ⟨s₁, hs₁H⟩)
      (Subtype.ext (by simpa using hs₁p)) (fun h => hs₁1 (congrArg Subtype.val h))
      (Subtype.ext (conjPSL_eq_self_of_commute hK hcard hus₁))).1
    have hzc' : ∀ x ∈ commutator H, (⟨z, hzH⟩ : H) * x = x * ⟨z, hzH⟩ := by
      intro x hx
      have ha := congrArg Subtype.val (hfixα x hx)
      have hb := congrArg Subtype.val (hfixβ x hx)
      rw [restrictConjPSL_apply, conjPSL_eq_iff] at ha hb
      apply Subtype.ext
      apply psl2Incl_injective K
      simp only [Subgroup.coe_mul, map_mul]
      have hb' : u * psl2Incl K z * psl2Incl K x * (psl2Incl K z)⁻¹ * u⁻¹ =
          psl2Incl K x := by
        calc u * psl2Incl K z * psl2Incl K x * (psl2Incl K z)⁻¹ * u⁻¹ =
            u * psl2Incl K z * psl2Incl K x * (u * psl2Incl K z)⁻¹ := by group
          _ = psl2Incl K x := hb
      have h1 : psl2Incl K z * psl2Incl K x * (psl2Incl K z)⁻¹ = psl2Incl K x := by
        calc psl2Incl K z * psl2Incl K x * (psl2Incl K z)⁻¹ =
            u⁻¹ * (u * psl2Incl K z * psl2Incl K x * (psl2Incl K z)⁻¹ * u⁻¹) * u := by group
          _ = u⁻¹ * psl2Incl K x * u := by rw [hb']
          _ = u⁻¹ * (u * psl2Incl K x * u⁻¹) * u := by rw [ha]
          _ = psl2Incl K x := by group
      calc psl2Incl K z * psl2Incl K x =
          psl2Incl K z * psl2Incl K x * (psl2Incl K z)⁻¹ * psl2Incl K z := by group
        _ = psl2Incl K x * psl2Incl K z := by rw [h1]
    have hmap : (commutator H).map e.toMonoidHom = alternatingGroup (Fin 4) := by
      have h1 := map_commutator_eq (G := H) e.toMonoidHom
      have h2 : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
      rw [h2, ← _root_.commutator_def, commutator_perm_fin_four_eq_alternatingGroup] at h1
      exact h1
    have hez : e ⟨z, hzH⟩ = 1 := by
      apply perm_four_eq_one_of_commute_alternating
      intro a
      have ha : (a : Equiv.Perm (Fin 4)) ∈ (commutator H).map e.toMonoidHom := by
        rw [hmap]
        exact a.2
      obtain ⟨x, hx, hxa⟩ := ha
      rw [← hxa]
      change e ⟨z, hzH⟩ * e x = e x * e ⟨z, hzH⟩
      rw [← map_mul, ← map_mul, hzc' x hx]
    apply hz1
    have := congrArg Subtype.val (e.injective (hez.trans (map_one e).symm))
    simpa using this
  ·
    exfalso
    obtain ⟨j, hj⟩ := hceven
    omega

theorem exists_outer_torus_sq {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {g : PGL2 K}
    (hg2 : g ^ 2 = 1) (hgJ : g ∉ pslRange K) :
    ∃ y : PSL2 K, orderOf y = outerTorusOrder (Nat.card K) / 2 ∧
      Matrix.ProjectiveSpecialLinearGroup.toPGL y * g =
        g * Matrix.ProjectiveSpecialLinearGroup.toPGL y := by
  classical
  obtain ⟨U, -, hUc, hUcard, hgU, -, -, -, -⟩ := outer_involution_centralizer hK hcard hg2 hgJ
  have hJ2 := pslRange_index_eq_two hK
  have hm := outerTorusOrder_mod_four (odd_card_of_isOddPrimePower hK)
  obtain ⟨x₀, hx₀⟩ := hUc.exists_generator
  have hx₀ord : orderOf (x₀ : PGL2 K) = outerTorusOrder (Nat.card K) := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hx₀, hUcard]
  obtain ⟨y, hy⟩ := Subgroup.mul_self_mem_of_index_two hJ2 (x₀ : PGL2 K)
  refine ⟨y, ?_, ?_⟩
  · rw [← orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective y, hy,
      ← pow_two, orderOf_pow' _ two_ne_zero, hx₀ord]
    rw [Nat.gcd_eq_right (by omega : 2 ∣ outerTorusOrder (Nat.card K))]
  · rw [hy]
    have h := hUc.commGroup.mul_comm (x₀ * x₀) ⟨g, hgU⟩
    exact congrArg Subtype.val h

theorem case_field_outer_psl2 {K : Type} [Field K] [Finite K] {p f : ℕ} [hp : Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {g : PGL2 K} (hg2 : g ^ 2 = 1) (hgJ : g ∉ pslRange K) {u : PGammaL2 K} (hu2 : u ^ 2 = 1)
    (hufield : u.right ≠ 1) (H : Subgroup (PSL2 K))
    (hinvg : ∀ x ∈ H, conjPSL K hK hcard (SemidirectProduct.inl g) x ∈ H)
    (hP1g : ∀ x, SemidirectProduct.inl g * psl2Incl K x = psl2Incl K x * SemidirectProduct.inl g →
      Odd (orderOf x) → x ∈ H)
    (hP1u : ∀ x, u * psl2Incl K x = psl2Incl K x * u → Odd (orderOf x) → x ∈ H) : H = ⊤ := by
  classical
  have hf2 : 2 ≤ f := two_le_of_ringEquiv_ne_one hp.out hKcard hufield
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hqodd := odd_card_of_isOddPrimePower hK
    rw [hKcard] at hqodd
    exact (Nat.not_even_iff_odd.mpr hqodd) ((Nat.even_pow' (by omega)).mpr even_two)
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  obtain ⟨r₁, r₂, h₁p, h₁1, h₂p, h₂1, h₁₂, hu₁, hu₂⟩ :=
    field_involution_fixed_root_pair hKcard hK hcard hu2 hufield
  have hoddp : ∀ {x : PSL2 K}, x ^ p = 1 → x ≠ 1 → Odd (orderOf x) := by
    intro x hx hx1
    rw [orderOf_eq_prime hx hx1]
    exact hpodd
  have hr₁H := hP1u r₁ hu₁ (hoddp h₁p h₁1)
  have hr₂H := hP1u r₂ hu₂ (hoddp h₂p h₂1)
  obtain ⟨y, hyord, hyg⟩ := exists_outer_torus_sq hK hcard hg2 hgJ
  have hqodd := odd_card_of_isOddPrimePower hK
  have hm := outerTorusOrder_mod_four hqodd
  have hyodd : Odd (orderOf y) := by
    rw [hyord, Nat.odd_iff]
    omega
  have hgy : SemidirectProduct.inl g * psl2Incl K y = psl2Incl K y * SemidirectProduct.inl g := by
    rw [psl2Incl_apply, ← map_mul, ← map_mul, hyg]
  have hyH := hP1g y hgy hyodd
  have hq9 : 9 ≤ Nat.card K := by
    rw [hKcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left (by have := hp.out.two_le; omega) 2
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.out.pos hf2
  have hmq := outerTorusOrder_eq (q := Nat.card K)
  have hy4 : 4 ≤ orderOf y := by
    rw [hyord]
    rcases hmq with h | h <;> omega
  have hqy : Nat.card K ≤ 2 * orderOf y + 1 := by
    rw [hyord]
    rcases hmq with h | h <;> omega
  rcases dickson_root_pair hKcard hK hf2 H hr₁H hr₂H hyH h₁p h₁1 h₂p h₁₂ hy4 hqy with
    h | ⟨h9, ⟨h4, -⟩ | ⟨-, ⟨e⟩⟩⟩
  · exact h
  · exfalso
    rw [h4] at hyodd
    exact absurd hyodd (by decide)
  ·
    exfalso
    have hgg : SemidirectProduct.inl g ^ 2 = (1 : PGammaL2 K) := by rw [← map_pow, hg2, map_one]
    let α := restrictConjPSL hK hcard hgg H hinvg
    have hord5 : orderOf y = 5 := by
      rw [hyord, h9]
      rfl
    have hy5' : y ^ 5 = 1 := by
      rw [← hord5]
      exact pow_orderOf_eq_one y
    have hy5 : (⟨y, hyH⟩ : H) ^ 5 = 1 := Subtype.ext (by simpa using hy5')
    have hy1 : (⟨y, hyH⟩ : H) ≠ 1 := by
      intro h
      have h' : y = 1 := by simpa using congrArg Subtype.val h
      rw [h', orderOf_one] at hord5
      omega
    have hfix := fix_of_equiv_alternating_five e α
      (restrictConjPSL_involutive hK hcard hgg H hinvg) hy5 hy1
      (Subtype.ext (conjPSL_eq_self_of_commute hK hcard hgy))
    have hle : H.map (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)) ≤
        Subgroup.centralizer ({g} : Set (PGL2 K)) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := congrArg Subtype.val (hfix ⟨x, hx⟩)
      rw [restrictConjPSL_apply, conjPSL_eq_iff, psl2Incl_apply, ← map_inv,
        ← map_mul, ← map_mul] at h1
      have h2 := SemidirectProduct.inl_injective h1
      calc Matrix.ProjectiveSpecialLinearGroup.toPGL x * g =
          g * Matrix.ProjectiveSpecialLinearGroup.toPGL x * g⁻¹ * g := by rw [h2]
        _ = g * Matrix.ProjectiveSpecialLinearGroup.toPGL x := by group
    have hcardC := card_outer_involution_centralizer hK hcard hg2 hgJ
    let : Finite (PGL2 K) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    have h1 := Subgroup.card_le_of_le hle
    rw [← Nat.card_congr (H.equivMapOfInjective _
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).toEquiv, hcardC,
      Nat.card_congr e.toEquiv, nat_card_alternatingGroup, h9] at h1
    have h10 : outerTorusOrder 9 = 10 := rfl
    rw [h10] at h1
    simp [Nat.factorial] at h1

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
