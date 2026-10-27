module

public import CFSG.Quasithin.Background.BlueprintB2Reduced

public section

namespace CFSG.QuasithinUnique.Setup

open CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2

variable {E : Type*} [Group E]

theorem isElementaryAbelian_centerTorsion (p : ℕ) (K : Subgroup E) :
    IsElementaryAbelian p (centerTorsion p K) :=
  isElementaryAbelian_iff.mpr
    ⟨fun _ ha _ hb => (mem_centerTorsion_iff.mp hb).2.1 _ (centerTorsion_le p K ha),
      fun _ ha => (mem_centerTorsion_iff.mp ha).2.2⟩

theorem normal_centerTorsion_pCore (p : ℕ) : (centerTorsion p (CFSG.pCore p E)).Normal where
  conj_mem x hx g := by
    obtain ⟨hxO, hxc, hxp⟩ := mem_centerTorsion_iff.mp hx
    refine mem_centerTorsion_iff.mpr
      ⟨(CFSG.pCore_normal : (CFSG.pCore p E).Normal).conj_mem x hxO g, fun k hk => ?_, ?_⟩
    · have hk' : g⁻¹ * k * g ∈ CFSG.pCore p E := by
        simpa using (CFSG.pCore_normal : (CFSG.pCore p E).Normal).conj_mem k hk g⁻¹
      have h := hxc _ hk'
      calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [h]
        _ = g * x * g⁻¹ * k := by group
    · rw [conj_pow, hxp, mul_one, mul_inv_cancel]

variable [Finite E]

theorem normal_le_centralizer_of_pPower (p : ℕ) [Fact p.Prime] (T : Sylow p E) {Z K D : Subgroup E}
    [K.Normal] [D.Normal] (hZc : ∀ z ∈ Z, ∀ t ∈ (T : Subgroup E), t * z = z * t)
    (hK : K ≤ Subgroup.centralizer (Z : Set E))
    (hDp : ∀ d ∈ D, ∃ k : ℕ, d ^ p ^ k ∈ K) : D ≤ Subgroup.centralizer (Z : Set E) := by
  have hsurj := QuotientGroup.mk'_surjective K
  have hDbar : IsPGroup p (D.map (QuotientGroup.mk' K)) := by
    rintro ⟨_, d, hd, rfl⟩
    obtain ⟨k, hk⟩ := hDp d hd
    refine ⟨k, Subtype.ext ?_⟩
    show (QuotientGroup.mk' K d) ^ p ^ k = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk
  have hDbn : (D.map (QuotientGroup.mk' K)).Normal := Subgroup.Normal.map inferInstance _ hsurj
  have hle := hDbar.le_sylow_of_normal (Sylow.mapSurjective hsurj T)
  intro d hd
  have hmem : QuotientGroup.mk' K d ∈ (Sylow.mapSurjective hsurj T : Subgroup (E ⧸ K)) :=
    hle (Subgroup.mem_map_of_mem _ hd)
  rw [Sylow.coe_mapSurjective] at hmem
  obtain ⟨t, ht, htd⟩ := hmem
  have hc : t⁻¹ * d ∈ K := QuotientGroup.eq.mp htd
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  have h1 : z * (t⁻¹ * d) = (t⁻¹ * d) * z := (Subgroup.mem_centralizer_iff.mp (hK hc)) z hz
  have h2 : t * z = z * t := hZc z hz t ht
  calc z * d = z * t * (t⁻¹ * d) := by group
    _ = t * z * (t⁻¹ * d) := by rw [← h2]
    _ = t * (z * (t⁻¹ * d)) := by group
    _ = t * ((t⁻¹ * d) * z) := by rw [h1]
    _ = d * z := by group

theorem isPrimeReduced_normalClosure_of_le_pCore (p : ℕ) [Fact p.Prime] (T : Sylow p E)
    {Z : Subgroup E} (hZO : Z ≤ CFSG.pCore p E) (hZT : Z ≤ centerTorsion p (T : Subgroup E)) :
    IsPrimeReduced p (Subgroup.normalClosure (Z : Set E)) := by
  have hZmem : ∀ z ∈ Z, z ∈ (T : Subgroup E) ∧ (∀ k ∈ (T : Subgroup E), k * z = z * k) ∧
      z ^ p = 1 := fun z hz => mem_centerTorsion_iff.mp (hZT hz)
  have hOT : CFSG.pCore p E ≤ (T : Subgroup E) :=
    (CFSG.pCore_isPGroup (p := p) (G := E)).le_sylow_of_normal T
  have hΩn : (centerTorsion p (CFSG.pCore p E)).Normal := normal_centerTorsion_pCore p
  have hZΩ : Z ≤ centerTorsion p (CFSG.pCore p E) := fun z hz =>
    mem_centerTorsion_iff.mpr
      ⟨hZO hz, fun k hk => (hZmem z hz).2.1 k (hOT hk), (hZmem z hz).2.2⟩
  have hWΩ : Subgroup.normalClosure (Z : Set E) ≤ centerTorsion p (CFSG.pCore p E) :=
    Subgroup.normalClosure_le_normal hZΩ
  refine (isPrimeReduced_iff_forall p).mpr ⟨Subgroup.normalClosure_normal,
    isElementaryAbelian_of_le hWΩ (isElementaryAbelian_centerTorsion p _), ?_⟩
  intro D hD hDp
  have : D.Normal := hD
  have hDZ : D ≤ Subgroup.centralizer (Z : Set E) :=
    normal_le_centralizer_of_pPower p T (fun z hz t ht => (hZmem z hz).2.1 t ht)
      (Subgroup.centralizer_le Subgroup.le_normalClosure) hDp
  have hZD : Z ≤ Subgroup.centralizer (D : Set E) := Subgroup.le_centralizer_iff.mp hDZ
  have : (Subgroup.centralizer (D : Set E)).Normal := inferInstance
  exact Subgroup.le_centralizer_iff.mp (Subgroup.normalClosure_le_normal hZD)

theorem qt_central_Sylow_seed_reduced_normal_closure (p : ℕ) [Fact p.Prime] (T : Sylow p E)
    {Z : Subgroup E} (hZ1 : Z ≠ ⊥) (hZO : Z ≤ CFSG.pCore p E)
    (hZT : Z ≤ centerTorsion p (T : Subgroup E)) :
    IsPrimeReduced p (Subgroup.normalClosure (Z : Set E)) ∧ Z ≠ ⊥ ∧
      Z ≤ Subgroup.normalClosure (Z : Set E) ∧
      Subgroup.normalClosure (Z : Set E) ≤ primeReducedAggregate E p :=
  have hW := isPrimeReduced_normalClosure_of_le_pCore p T hZO hZT
  ⟨hW, hZ1, Subgroup.le_normalClosure, le_primeReducedAggregate hW⟩

theorem qt_characteristic_p_Sylow_center_reduced_closure (p : ℕ) [Fact p.Prime]
    (hE : CFSG.IsCharacteristicP p E) (T : Sylow p E) {Z : Subgroup E}
    (hZT : Z ≤ centerTorsion p (T : Subgroup E)) :
    Z ≤ CFSG.pCore p E ∧ IsPrimeReduced p (Subgroup.normalClosure (Z : Set E)) ∧
      Z ≤ Subgroup.normalClosure (Z : Set E) ∧
      Subgroup.normalClosure (Z : Set E) ≤ primeReducedAggregate E p := by
  have hOT : CFSG.pCore p E ≤ (T : Subgroup E) :=
    (CFSG.pCore_isPGroup (p := p) (G := E)).le_sylow_of_normal T
  have hZO : Z ≤ CFSG.pCore p E := fun z hz => by
    obtain ⟨_, hzc, _⟩ := mem_centerTorsion_iff.mp (hZT hz)
    exact hE (Subgroup.mem_centralizer_iff.mpr fun o ho => hzc o (hOT ho))
  have hW := isPrimeReduced_normalClosure_of_le_pCore p T hZO hZT
  exact ⟨hZO, hW, Subgroup.le_normalClosure, le_primeReducedAggregate hW⟩

end CFSG.QuasithinUnique.Setup
