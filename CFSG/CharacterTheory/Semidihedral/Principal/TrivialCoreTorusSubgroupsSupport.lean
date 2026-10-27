module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicTorusNormalizerQuotientsSupport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicSubgroupCharacteristic

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

theorem normalizer_le_normalizer_pPrimeCore_map {G : Type*} [Group G] (p : ℕ) (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (((CFSG.pPrimeCore p A).map A.subtype : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let φ : A ≃* A := A.normalizerMonoidHom ⟨g, hg⟩
  have hfix := Subgroup.characteristic_iff_map_le.mp
    (inferInstance : (CFSG.pPrimeCore p A).Characteristic) φ
  have himage : φ y ∈ CFSG.pPrimeCore p A := hfix (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  exact Subgroup.mem_map.mpr ⟨φ y, himage, A.normalizerMonoidHom_apply_apply_coe ⟨g, hg⟩ y⟩

theorem conj_eq_of_mem_centralizer {G : Type*} [Group G] {S : Set G} {g x : G}
    (hg : g ∈ Subgroup.centralizer S) (hx : x ∈ S) : g * x * g⁻¹ = x := by
  rw [(Subgroup.mem_centralizer_iff.mp hg x hx).symm, mul_assoc, mul_inv_cancel, mul_one]

theorem inv_ne_self_of_odd_card {G : Type*} [Group G] {W : Subgroup G} (hW : Odd (Nat.card W))
    {w : G} (hw : w ∈ W) (hw1 : w ≠ 1) : w⁻¹ ≠ w := by
  intro h
  have h2 : w ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← h]
    exact inv_mul_cancel w
  have hodd₁ : Odd (orderOf w) := Odd.of_dvd_nat hW (Subgroup.orderOf_dvd_natCard W hw)
  have h1 : orderOf w = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
    · exact h
    · rw [h] at hodd₁
      exact absurd hodd₁ (by decide)
  exact hw1 (orderOf_eq_one_iff.mp h1)

theorem exists_mul_mem_normalizer_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {A V : Subgroup G} (P : Sylow p A) (hP : (P : Subgroup A).map A.subtype = V)
    {j : G} (hj : j ∈ Subgroup.normalizer (A : Set G)) :
    ∃ a ∈ A, a * j ∈ Subgroup.normalizer (V : Set G) := by
  have hVA : V ≤ A := hP ▸ Subgroup.map_subtype_le _
  have hPV : (P : Subgroup A) = V.subgroupOf A := by
    rw [← hP, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
  have hAnorm : ∀ x ∈ A, j * x * j⁻¹ ∈ A := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hj x).mp hx
  set V₁ := V.map (MulAut.conj j).toMonoidHom with hV₁
  have hV₁A : V₁ ≤ A := by
    rintro _ ⟨v, hv, rfl⟩
    exact hAnorm v (hVA hv)
  have hV₁card : Nat.card (V₁.subgroupOf A) = Nat.card (P : Subgroup A) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₁A).toEquiv, hV₁,
      Subgroup.card_map_of_injective (MulAut.conj j).injective, ← hP,
      Subgroup.card_map_of_injective A.subtype_injective]
  let S₁ : Sylow p A := Sylow.ofCard (V₁.subgroupOf A) (by
    rw [hV₁card, Sylow.card_eq_multiplicity])
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A S₁ P
  refine ⟨a, a.2, ?_⟩
  have hsub : ∀ v ∈ V, ((a : G) * j) * v * ((a : G) * j)⁻¹ ∈ V := by
    intro v hv
    have hmem : (⟨j * v * j⁻¹, hV₁A ⟨v, hv, rfl⟩⟩ : A) ∈ (S₁ : Subgroup A) := by
      change _ ∈ V₁.subgroupOf A
      rw [Subgroup.mem_subgroupOf]
      exact ⟨v, hv, rfl⟩
    have hmem' : MulAut.conj a • (⟨j * v * j⁻¹, hV₁A ⟨v, hv, rfl⟩⟩ : A) ∈
        ((a • S₁ : Sylow p A) : Subgroup A) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hmem
    rw [ha, hPV, Subgroup.mem_subgroupOf] at hmem'
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hmem'
    have he : ((a : G) * j) * v * ((a : G) * j)⁻¹ = a * (j * v * j⁻¹) * (a : G)⁻¹ := by
      group
    rw [he]
    exact hmem'
  have hle : V.map (MulAut.conj ((a : G) * j)).toMonoidHom ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    exact hsub v hv
  have heq : V.map (MulAut.conj ((a : G) * j)).toMonoidHom = V :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj _).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hsub y hy, fun hy => ?_⟩
  rw [← heq] at hy
  obtain ⟨v, hv, hvy⟩ := hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hvy
  have : v = y := by
    have := congrArg (fun x => ((a : G) * j)⁻¹ * x * ((a : G) * j)) hvy
    simpa [mul_assoc] using this
  exact this ▸ hv

theorem torus_subgroup_normalizer_data {G : Type*} [Group G] [Finite G] {t : G}
    (V W : Subgroup G) (hV : IsKleinFour V) (htV : t ∈ V) (hWodd : Odd (Nat.card W))
    (hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hsup : V ⊔ W = Subgroup.centralizer (V : Set G)) (hdisj : Disjoint V W)
    (hcentw : ∀ w ∈ W, w ≠ 1 →
      Subgroup.centralizer {t} ⊓ Subgroup.centralizer {w} = Subgroup.centralizer (V : Set G))
    (hMH : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (W : Set G))
    (hinvH : ∀ h ∈ Subgroup.normalizer (W : Set G), h ∉ Subgroup.centralizer (W : Set G) →
      ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hKM : Nat.card (Subgroup.centralizer (W : Set G) ⊓ Subgroup.normalizer (V : Set G) :
      Subgroup G) = 12 * Nat.card W)
    {d : G} (hdM : d ∈ Subgroup.normalizer (V : Set G)) (hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹)
    {U : Subgroup G} (hUW : U ≤ W) (hU1 : U ≠ ⊥) :
    (∃ P : Sylow 2 (Subgroup.centralizer (U : Set G)),
        (P : Subgroup _).map (Subgroup.centralizer (U : Set G)).subtype = V) ∧
      Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (U : Set G) ∧
      Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (U : Set G) ∧
      Subgroup.centralizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G) =
        Subgroup.centralizer (W : Set G) ⊓ Subgroup.normalizer (V : Set G) ∧
      Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer {t} =
        Subgroup.centralizer (V : Set G) ∧
      (Subgroup.centralizer (U : Set G) : Set G) * (Subgroup.normalizer (V : Set G) : Set G) =
        (Subgroup.normalizer (U : Set G) : Set G) ∧
      (Subgroup.centralizer (U : Set G)).relIndex (Subgroup.normalizer (U : Set G)) = 2 ∧
      (∀ j ∈ Subgroup.normalizer (U : Set G), j ∉ Subgroup.centralizer (U : Set G) →
        ∀ u ∈ U, j * u * j⁻¹ = u⁻¹) ∧
      ∃ k : ℕ, Odd k ∧ Nat.card (Subgroup.normalizer (U : Set G)) = 8 * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := Subgroup.centralizer (U : Set G) with hAdef
  set J := Subgroup.normalizer (U : Set G) with hJdef
  set D := Subgroup.centralizer (V : Set G) with hDdef
  set M := Subgroup.normalizer (V : Set G) with hMdef
  set H := Subgroup.normalizer (W : Set G) with hHdef
  set K := Subgroup.centralizer (W : Set G) with hKdef
  obtain ⟨-, -, hDK, -, -⟩ := klein_centralizer_odd_core V W hV hWodd hWcomm hsup hdisj
  have hVD : V ≤ D := hsup ▸ le_sup_left
  have hKA : K ≤ A := Subgroup.centralizer_le hUW
  have hDA : D ≤ A := hDK.trans hKA
  have hVA : V ≤ A := hVD.trans hDA
  have hAJ : A ≤ J := Subgroup.centralizer_le_normalizer _
  obtain ⟨u, huU, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra! hall
    exact hU1 ((Subgroup.eq_bot_iff_forall _).mpr hall)
  have huinv : u⁻¹ ≠ u := inv_ne_self_of_odd_card hWodd (hUW huU) hu1
  have hconjH : ∀ g ∈ H, ∀ x ∈ U, g * x * g⁻¹ ∈ U := by
    intro g hg x hx
    by_cases hgK : g ∈ K
    · rw [conj_eq_of_mem_centralizer hgK (hUW hx)]
      exact hx
    · rw [hinvH g hg hgK x (hUW hx)]
      exact U.inv_mem hx
  have hHJ : H ≤ J := Subgroup.le_normalizer_iff.mpr hconjH
  have hAHK : ∀ g ∈ H, g ∈ A → g ∈ K := by
    intro g hg hgA
    by_contra hgK
    apply huinv
    rw [← hinvH g hg hgK u (hUW huU), conj_eq_of_mem_centralizer hgA huU]
  have hAM : A ⊓ M = K ⊓ M := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgA, hgM⟩ := Subgroup.mem_inf.mp hg
      exact Subgroup.mem_inf.mpr ⟨hAHK g (hMH hgM) hgA, hgM⟩
    · exact inf_le_inf_right _ hKA
  have hV4 : Nat.card (V.subgroupOf A) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv, hV.card_four]
  have hNA : Nat.card (Subgroup.normalizer ((V.subgroupOf A : Subgroup A) : Set A)) =
      12 * Nat.card W := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective,
      ← Subgroup.subgroupOf_normalizer_eq hVA, Subgroup.subgroupOf_map_subtype, inf_comm, hAM,
      hKM]
  have hmod := Sylow.card_normalizer_modEq_card (p := 2) (n := 2) (H := V.subgroupOf A)
    (by rw [hV4]; norm_num)
  have hA8 : ¬ 8 ∣ Nat.card A := by
    intro h8
    rw [hNA] at hmod
    have hmod' : (12 * Nat.card W) % 8 = Nat.card A % 8 := hmod
    obtain ⟨k, hk⟩ := hWodd
    omega
  have hidx : ¬ 2 ∣ (V.subgroupOf A).index := by
    intro h2
    apply hA8
    rw [← Subgroup.card_mul_index (V.subgroupOf A), hV4]
    exact Nat.mul_dvd_mul_left 4 h2
  have hVp : IsPGroup 2 (V.subgroupOf A) := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  let PV : Sylow 2 A := hVp.toSylow hidx
  have hPV : (PV : Subgroup A).map A.subtype = V := by
    change (V.subgroupOf A).map _ = V
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVA]
  have hAt : A ⊓ Subgroup.centralizer {t} = D := by
    apply le_antisymm
    · rw [← hcentw u (hUW huU) hu1, inf_comm]
      exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huU))
    · refine le_inf hDA ?_
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hx t htV).symm
  have hJA : J ≤ Subgroup.normalizer (A : Set G) := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer U
  have hdec : ∀ j ∈ J, ∃ a ∈ A, a * j ∈ M := fun j hj =>
    exists_mul_mem_normalizer_of_sylow PV hPV (hJA hj)
  have hdichJ : ∀ j ∈ J, (∀ x ∈ U, j * x * j⁻¹ = x) ∨ (∀ x ∈ U, j * x * j⁻¹ = x⁻¹) := by
    intro j hj
    obtain ⟨a, ha, haj⟩ := hdec j hj
    have hac : ∀ x ∈ U, a⁻¹ * x * a = x := fun x hx => by
      have h := conj_eq_of_mem_centralizer ha hx
      calc a⁻¹ * x * a = a⁻¹ * (a * x * a⁻¹) * a := by rw [h]
        _ = x := by group
    have hj' : ∀ x ∈ U, j * x * j⁻¹ = a⁻¹ * ((a * j) * x * (a * j)⁻¹) * a := fun x _ => by
      group
    by_cases hK' : a * j ∈ K
    · left
      intro x hx
      rw [hj' x hx, conj_eq_of_mem_centralizer hK' (hUW hx), hac x hx]
    · right
      intro x hx
      rw [hj' x hx, hinvH _ (hMH haj) hK' x (hUW hx), hac x⁻¹ (U.inv_mem hx)]
  have hdJ : d ∈ J := hHJ (hMH hdM)
  obtain ⟨hAJ2, hinvJ, -⟩ := relIndex_centralizer_eq_two_of_dichotomy hdJ
    (fun x hx => hdW x (hUW hx)) ⟨u, huU, huinv⟩ hdichJ
  have hAMset : (A : Set G) * (M : Set G) = (J : Set G) := by
    ext j
    constructor
    · rintro ⟨a, ha, g, hg, rfl⟩
      exact J.mul_mem (hAJ ha) (hHJ (hMH hg))
    · intro hj
      obtain ⟨a, ha, haj⟩ := hdec j hj
      exact ⟨a⁻¹, A.inv_mem ha, a * j, haj, by group⟩
  have hAcard : Nat.card A = 4 * (V.subgroupOf A).index := by
    rw [← Subgroup.card_mul_index (V.subgroupOf A), hV4]
  have hJcard : Nat.card J = 2 * Nat.card A := by
    have h := Subgroup.card_mul_index (A.subgroupOf J)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ).toEquiv] at h
    have hri : (A.subgroupOf J).index = 2 := hAJ2
    rw [hri] at h
    omega
  refine ⟨⟨PV, hPV⟩, hKA, hHJ, hAM, hAt, hAMset, hAJ2, hinvJ, (V.subgroupOf A).index, ?_, ?_⟩
  · rcases Nat.even_or_odd (V.subgroupOf A).index with h | h
    · exact absurd (even_iff_two_dvd.mp h) hidx
    · exact h
  · rw [hJcard, hAcard]
    ring

theorem torus_subgroup_odd_core_data {G : Type*} [Group G] [Finite G] {t : G}
    (V W : Subgroup G) (hV : IsKleinFour V) (htV : t ∈ V) (hWcyc : IsCyclic W)
    (hWodd : Odd (Nat.card W))
    (hsup : V ⊔ W = Subgroup.centralizer (V : Set G)) (hdisj : Disjoint V W)
    (hcentw : ∀ w ∈ W, w ≠ 1 →
      Subgroup.centralizer {t} ⊓ Subgroup.centralizer {w} = Subgroup.centralizer (V : Set G))
    (hMH : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (W : Set G))
    (hinvH : ∀ h ∈ Subgroup.normalizer (W : Set G), h ∉ Subgroup.centralizer (W : Set G) →
      ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hKM : Nat.card (Subgroup.centralizer (W : Set G) ⊓ Subgroup.normalizer (V : Set G) :
      Subgroup G) = 12 * Nat.card W)
    {d : G} (hdM : d ∈ Subgroup.normalizer (V : Set G)) (hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹)
    (htrans : ∀ v ∈ V, v ≠ 1 → ∃ k ∈ Subgroup.centralizer (W : Set G), k * t * k⁻¹ = v)
    {U : Subgroup G} (hUW : U ≤ W) (hU1 : U ≠ ⊥) :
    let A : Subgroup G := Subgroup.centralizer (U : Set G)
    let J : Subgroup G := Subgroup.normalizer (U : Set G)
    let R : Subgroup G := (CFSG.pPrimeCore 2 A).map A.subtype
    U ≤ R ∧ R ≤ W ∧ R ≤ (Subgroup.center A).map A.subtype ∧
      (CFSG.pPrimeCore 2 J).map J.subtype = R ∧
      J = Subgroup.normalizer (R : Set G) ∧ A = Subgroup.centralizer (R : Set G) ∧
      R ≠ ⊥ ∧ IsCyclic R ∧
      ∀ T : Subgroup G, R ≤ T → T ≤ W →
        A ⊓ Subgroup.normalizer (T : Set G) = Subgroup.centralizer (T : Set G) := by
  intro A J R
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨-, -, hDK, hodd, -⟩ := klein_centralizer_odd_core V W hV hWodd hWcomm hsup hdisj
  obtain ⟨-, hKA, -, -, hAt, -, hAJ2, -, -⟩ := torus_subgroup_normalizer_data V W hV htV hWodd
    hWcomm hsup hdisj hcentw hMH hinvH hKM hdM hdW hUW hU1
  have hVD : V ≤ Subgroup.centralizer (V : Set G) := hsup ▸ le_sup_left
  have hWD : W ≤ Subgroup.centralizer (V : Set G) := hsup ▸ le_sup_right
  have hVA : V ≤ A := (hVD.trans hDK).trans hKA
  have hUA : U ≤ A := ((hUW.trans hWD).trans hDK).trans hKA
  have hAJ : A ≤ J := Subgroup.centralizer_le_normalizer _
  have hJA : J ≤ Subgroup.normalizer (A : Set G) := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer U
  have hJR : J ≤ Subgroup.normalizer (R : Set G) :=
    hJA.trans (normalizer_le_normalizer_pPrimeCore_map 2 A)
  have hRA : R ≤ A := Subgroup.map_subtype_le _
  have hRodd : Odd (Nat.card R) := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hRnormA : ∀ a ∈ A, ∀ x ∈ R, a * x * a⁻¹ ∈ R := fun a ha x hx =>
    (Subgroup.mem_normalizer_iff.mp (hJR (hAJ ha)) x).mp hx
  have hUR : U ≤ R := by
    have hUn : (U.subgroupOf A).Normal := by
      refine ⟨fun x hx a => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [conj_eq_of_mem_centralizer a.2 hx]
      exact hx
    have hcardU : Nat.card (U.subgroupOf A) = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUA).toEquiv
    have hUodd : Odd (Nat.card U) := Odd.of_dvd_nat hWodd (Subgroup.card_dvd_of_le hUW)
    have hle : U.subgroupOf A ≤ CFSG.pPrimeCore 2 A :=
      le_sSup ⟨hUn, by rw [hcardU]; exact Nat.coprime_two_left.mpr hUodd⟩
    intro x hx
    exact ⟨⟨x, hUA hx⟩, hle hx, rfl⟩
  have hRt : R ⊓ Subgroup.centralizer ({t} : Set G) ≤ W := by
    intro x hx
    obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxD : x ∈ Subgroup.centralizer (V : Set G) := by
      rw [← hAt]
      exact Subgroup.mem_inf.mpr ⟨hRA hxR, hxC⟩
    exact hodd x hxD (Odd.of_dvd_nat hRodd (Subgroup.orderOf_dvd_natCard R hxR))
  have hRv : ∀ v ∈ V, v ≠ 1 → R ⊓ Subgroup.centralizer ({v} : Set G) ≤ W := by
    intro v hv hv1 x hx
    obtain ⟨k, hkK, hk⟩ := htrans v hv hv1
    obtain ⟨hxR, hxv⟩ := Subgroup.mem_inf.mp hx
    have hy : k⁻¹ * x * k ∈ R ⊓ Subgroup.centralizer ({t} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h := hRnormA k⁻¹ (A.inv_mem (hKA hkK)) x hxR
        rwa [inv_inv] at h
      · rw [Subgroup.mem_centralizer_singleton_iff] at hxv ⊢
        rw [← hk] at hxv
        calc k⁻¹ * x * k * t = k⁻¹ * (x * (k * t * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * t * k⁻¹) * x) * k := by rw [hxv]
          _ = t * (k⁻¹ * x * k) := by group
    have hyW := hRt hy
    have hx' : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rw [hx', conj_eq_of_mem_centralizer hkK hyW]
    exact hyW
  have hVN : V ≤ Subgroup.normalizer (R : Set G) := fun v hv => hJR (hAJ (hVA hv))
  let φ : V →* MulAut R := R.normalizerMonoidHom.comp (Subgroup.inclusion hVN)
  let : MulDistribMulAction V R := MulDistribMulAction.compHom R φ
  have : CFSG.IsElementaryAbelian 2 V :=
    { toIsMulCommutative := ⟨⟨mul_comm_of_exponent_two hV.exponent_two⟩⟩
      exponent_dvd_p := by rw [hV.exponent_two] }
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := V) (H := R)
    (by rw [hV.card_four]; norm_num)
    (fun h => (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr h))
  have hRW : R ≤ W := by
    intro x hx
    have hmem : (⟨x, hx⟩ : R) ∈ (⊤ : Subgroup R) := Subgroup.mem_top _
    rw [← hgen] at hmem
    have hle : (⨆ (a : V) (_ : a ≠ 1), fixedPointSubgroup (Subgroup.zpowers a) R) ≤
        W.comap R.subtype := by
      refine iSup₂_le fun a ha => ?_
      intro y hy
      rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
      have hy' : (a : G) * (y : G) * (a : G)⁻¹ = y := by
        have h := congrArg Subtype.val hy
        exact h
      apply hRv a a.2 (fun h => ha (Subtype.ext h))
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : G) * a = (a : G) * (y : G) * (a : G)⁻¹ * a := by rw [hy']
        _ = a * y := by group
    exact hle hmem
  have hR1 : R ≠ ⊥ := fun h => hU1 (le_bot_iff.mp (h ▸ hUR))
  have hRcyc : IsCyclic R := by
    have := hWcyc
    exact isCyclic_of_injective (Subgroup.inclusion hRW) (Subgroup.inclusion_injective hRW)
  have hJ2 : (CFSG.pPrimeCore 2 J).map J.subtype = R := by
    apply le_antisymm
    · set O := (CFSG.pPrimeCore 2 J).map J.subtype with hOdef
      have hOodd : Odd (Nat.card O) := by
        rw [Subgroup.card_map_of_injective J.subtype_injective]
        exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
      have hOJ : O ≤ J := Subgroup.map_subtype_le _
      have hOA : O ≤ A := le_of_odd_card_of_relIndex_eq_two hAJ2 hOJ hOodd
      have hOn : (O.subgroupOf A).Normal := by
        refine ⟨fun x hx a => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        refine ⟨⟨a, hAJ a.2⟩ * y * ⟨a, hAJ a.2⟩⁻¹,
          (inferInstance : (CFSG.pPrimeCore 2 J).Normal).conj_mem y hy _, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyx ⊢
        rw [hyx]
      have hOcard : Nat.card (O.subgroupOf A) = Nat.card O :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOA).toEquiv
      have hle : O.subgroupOf A ≤ CFSG.pPrimeCore 2 A :=
        le_sSup ⟨hOn, by rw [hOcard]; exact Nat.coprime_two_left.mpr hOodd⟩
      intro x hx
      exact ⟨⟨x, hOA hx⟩, hle hx, rfl⟩
    · have hRJ : R ≤ J := hRA.trans hAJ
      have hRn : (R.subgroupOf J).Normal := by
        refine ⟨fun x hx j => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (Subgroup.mem_normalizer_iff.mp (hJR j.2) x).mp hx
      have hRcard : Nat.card (R.subgroupOf J) = Nat.card R :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRJ).toEquiv
      have hle : R.subgroupOf J ≤ CFSG.pPrimeCore 2 J :=
        le_sSup ⟨hRn, by rw [hRcard]; exact Nat.coprime_two_left.mpr hRodd⟩
      intro x hx
      exact ⟨⟨x, hRJ hx⟩, hle hx, rfl⟩
  have hJeq : J = Subgroup.normalizer (R : Set G) :=
    le_antisymm hJR (CFSG.GorensteinWalter.normalizer_le_normalizer_of_le_cyclic hRcyc hUR)
  have hAeq : A = Subgroup.centralizer (R : Set G) := by
    obtain ⟨-, -, -, -, -, -, hR2, -, -⟩ := torus_subgroup_normalizer_data V W hV htV hWodd
      hWcomm hsup hdisj hcentw hMH hinvH hKM hdM hdW hRW hR1
    have hCRA : Subgroup.centralizer (R : Set G) ≤ A := Subgroup.centralizer_le hUR
    rw [← hJeq] at hR2
    have h := Subgroup.relIndex_mul_relIndex _ _ _ hCRA hAJ
    rw [hR2, hAJ2] at h
    have h1 : (Subgroup.centralizer (R : Set G)).relIndex A = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hCRA
  have hRZ : R ≤ (Subgroup.center A).map A.subtype := by
    intro x hx
    refine ⟨⟨x, hRA hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have ha : (a : G) ∈ Subgroup.centralizer (R : Set G) := hAeq.le a.2
    exact (Subgroup.mem_centralizer_iff.mp ha x hx).symm
  refine ⟨hUR, hRW, hRZ, hJ2, hJeq, hAeq, hR1, hRcyc, fun T hRT hTW => ?_⟩
  have hT1 : T ≠ ⊥ := fun h => hR1 (le_bot_iff.mp (h ▸ hRT))
  obtain ⟨-, -, -, -, -, -, -, hinvT, -⟩ := torus_subgroup_normalizer_data V W hV htV hWodd
    hWcomm hsup hdisj hcentw hMH hinvH hKM hdM hdW hTW hT1
  have hCTA : Subgroup.centralizer (T : Set G) ≤ A :=
    (Subgroup.centralizer_le hRT).trans hAeq.ge
  obtain ⟨r, hrR, hr1⟩ : ∃ r ∈ R, r ≠ 1 := by
    by_contra! hall
    exact hR1 ((Subgroup.eq_bot_iff_forall _).mpr hall)
  have hrinv : r⁻¹ ≠ r := inv_ne_self_of_odd_card hRodd hrR hr1
  apply le_antisymm
  · intro x hx
    obtain ⟨hxA, hxN⟩ := Subgroup.mem_inf.mp hx
    by_contra hxC
    apply hrinv
    rw [← hinvT x hxN hxC r (hRT hrR), conj_eq_of_mem_centralizer (hAeq.le hxA) hrR]
  · exact le_inf hCTA (Subgroup.centralizer_le_normalizer _)

theorem map_centralizer_subgroupOf {G : Type*} [Group G] {T A : Subgroup G} (hTA : T ≤ A) :
    (Subgroup.centralizer ((T.subgroupOf A : Subgroup A) : Set A)).map A.subtype =
      A ⊓ Subgroup.centralizer (T : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hy
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val (hy ⟨v, hTA hv⟩ hv)
  · intro hx
    obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC v hv)

theorem map_normalizer_subgroupOf {G : Type*} [Group G] {T A : Subgroup G} (hTA : T ≤ A) :
    (Subgroup.normalizer ((T.subgroupOf A : Subgroup A) : Set A)).map A.subtype =
      A ⊓ Subgroup.normalizer (T : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hTA, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem quotient_normalizer_eq_of_inf_normalizer_eq {G : Type*} [Group G] {A T : Subgroup G}
    (N : Subgroup A) [N.Normal] (hTA : T ≤ A) (hNT : N ≤ T.subgroupOf A)
    (hT : A ⊓ Subgroup.normalizer (T : Set G) = Subgroup.centralizer (T : Set G)) :
    Subgroup.normalizer (((T.subgroupOf A).map (QuotientGroup.mk' N) : Subgroup (A ⧸ N)) :
        Set (A ⧸ N)) =
      ((Subgroup.centralizer (T : Set G)).subgroupOf A).map (QuotientGroup.mk' N) ∧
    Subgroup.centralizer (((T.subgroupOf A).map (QuotientGroup.mk' N) : Subgroup (A ⧸ N)) :
        Set (A ⧸ N)) =
      ((Subgroup.centralizer (T : Set G)).subgroupOf A).map (QuotientGroup.mk' N) := by
  set π := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hcomap : ((T.subgroupOf A).map π).comap π = T.subgroupOf A := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNT]
  have hnorm : Subgroup.normalizer (((T.subgroupOf A).map π : Subgroup (A ⧸ N)) : Set (A ⧸ N)) =
      (Subgroup.normalizer ((T.subgroupOf A : Subgroup A) : Set A)).map π := by
    rw [← Subgroup.map_comap_eq_self_of_surjective hsurj (Subgroup.normalizer _),
      Subgroup.comap_normalizer_eq_of_surjective _ hsurj, hcomap]
  have hNA : Subgroup.normalizer ((T.subgroupOf A : Subgroup A) : Set A) =
      (Subgroup.centralizer (T : Set G)).subgroupOf A := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTA, ← hT, ← Subgroup.inf_subgroupOf_left]
  have hle : ((Subgroup.centralizer (T : Set G)).subgroupOf A).map π ≤
      Subgroup.centralizer (((T.subgroupOf A).map π : Subgroup (A ⧸ N)) : Set (A ⧸ N)) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨τ, hτ, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hc hτ
    simpa only [Subgroup.coe_mul] using Subgroup.mem_centralizer_iff.mp hc τ hτ
  have heq : Subgroup.normalizer (((T.subgroupOf A).map π : Subgroup (A ⧸ N)) : Set (A ⧸ N)) =
      ((Subgroup.centralizer (T : Set G)).subgroupOf A).map π := by
    rw [hnorm, hNA]
  refine ⟨heq, le_antisymm ?_ hle⟩
  rw [← heq]
  exact Subgroup.centralizer_le_normalizer _

end CFSG.Semidihedral.Principal
