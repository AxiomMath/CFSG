module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2A8Basic
public import CFSG.GroupTheory.FourGroupOddOrderIdentity

public section

namespace CFSG.OddStandard.ThmC.O2.A8

open CFSG Subgroup

section Counting

variable {K : Type} [Group K] [Finite K] {A : Type} [Group A] [Finite A]
  {ρ : K →* MulAut A} {V : Sylow 2 K} {Z : Subgroup A}

omit [Finite A] in
theorem oc_isKleinFour (h : Hyp ρ V Z) : IsKleinFour (V : Subgroup K) := by
  have : Nontrivial (V : Subgroup K) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h.cardV]; decide)
  refine ⟨h.cardV, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun v hv => ?_⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext (h.sqV v v.2)) hv

omit [Finite A] in
theorem oc_exists_ne (h : Hyp ρ V Z) : ∃ v ∈ (V : Subgroup K), v ≠ 1 := by
  have : Nontrivial (V : Subgroup K) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h.cardV]; decide)
  obtain ⟨v, hv⟩ := exists_ne (1 : (V : Subgroup K))
  exact ⟨v, v.2, fun h1 => hv (Subtype.ext h1)⟩

omit [Finite K] [Finite A] in
theorem oc_stab_of_comm (h : Hyp ρ V Z) {v m : K} (hv : v ∈ (V : Subgroup K)) (hv1 : v ≠ 1)
    (hc : m * v = v * m) : ∀ a ∈ Z, ρ m a ∈ Z := by
  intro a ha
  rw [← h.fix v hv hv1]
  have h1 : ρ v (ρ m a) = ρ m (ρ v a) := by
    have h2 := congrArg (fun k => ρ k a) hc
    simpa [map_mul] using h2.symm
  rw [h1, (h.fix v hv hv1 a).2 ha]

theorem oc_odd_card (L : Type) [Group L] [Finite L] : Odd (Nat.card (pPrimeCore 2 L)) :=
  Nat.coprime_two_left.1 pPrimeCore_coprime_card

omit [Finite K] in
theorem oc_mem_normalizer_iff (P : Sylow 2 K) (g : K) :
    g ∈ normalizer ((P : Subgroup K) : Set K) ↔ g • P = P :=
  Sylow.smul_eq_iff_mem_normalizer.symm

theorem oc_core_le_normalizer (h : Hyp ρ V Z) :
    pPrimeCore 2 K ≤ normalizer ((V : Subgroup K) : Set K) := by
  classical
  have : IsKleinFour (V : Subgroup K) := oc_isKleinFour h
  have hodd := oc_odd_card K
  let : MulDistribMulAction (V : Subgroup K) (pPrimeCore 2 K) :=
    MulDistribMulAction.compHom (pPrimeCore 2 K)
      ((MulAut.conjNormal (H := pPrimeCore 2 K)).comp (V : Subgroup K).subtype)
  let : Fintype (V : Subgroup K) := Fintype.ofFinite _
  have hsmul : ∀ (v : (V : Subgroup K)) (m : pPrimeCore 2 K),
      ((v • m : pPrimeCore 2 K) : K) = (v : K) * (m : K) * (v : K)⁻¹ := fun v m => rfl
  let Y : Subgroup (pPrimeCore 2 K) :=
    (normalizer ((V : Subgroup K) : Set K)).subgroupOf (pPrimeCore 2 K)
  have hVN : (V : Subgroup K) ≤ normalizer ((V : Subgroup K) : Set K) := Subgroup.le_normalizer
  have hYinv : ∀ v : (V : Subgroup K), ∀ y ∈ Y, v • y ∈ Y := by
    intro v y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    rw [hsmul]
    exact mul_mem (mul_mem (hVN v.2) hy) (inv_mem (hVN v.2))
  have hfix : ∀ v : (V : Subgroup K), v ≠ 1 → ∀ m : pPrimeCore 2 K, v • m = m → m ∈ Y := by
    intro v hv1 m hm
    have hc : (m : K) * (v : K) = (v : K) * (m : K) := by
      have h1 := congrArg Subtype.val hm
      rw [hsmul] at h1
      calc (m : K) * (v : K) = ((v : K) * (m : K) * (v : K)⁻¹) * (v : K) := by rw [h1]
        _ = (v : K) * (m : K) := by group
    have hv1' : (v : K) ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
    exact Subgroup.mem_subgroupOf.2 ((h.stab_iff m).1 (oc_stab_of_comm h v.2 hv1' hc))
  have hid := (CFSG.GroupTheory.odd_group_four_group_centralizer_order_identity
    (A := (V : Subgroup K)) (X := pPrimeCore 2 K) hodd).2 Y hYinv
  have h1 : ∀ a ∈ Finset.univ.erase (1 : (V : Subgroup K)),
      Y.relIndex (fixedPointSubgroup (Subgroup.zpowers a) (pPrimeCore 2 K)) = 1 := by
    intro a ha
    rw [Subgroup.relIndex_eq_one]
    intro x hx
    exact hfix a (Finset.mem_erase.1 ha).1 x (hx ⟨a, Subgroup.mem_zpowers a⟩)
  have h2 : Y.relIndex (fixedPointSubgroup (V : Subgroup K) (pPrimeCore 2 K)) = 1 := by
    obtain ⟨v, hv, hv1⟩ := oc_exists_ne h
    rw [Subgroup.relIndex_eq_one]
    intro x hx
    exact hfix ⟨v, hv⟩ (fun h1 => hv1 (congrArg Subtype.val h1)) x
      ((FixedPoints.mem_subgroup _ _ _).1 hx ⟨v, hv⟩)
  rw [Finset.prod_eq_one h1, h2] at hid
  have hY : Y = ⊤ := Subgroup.index_eq_one.1 (by simpa using hid)
  exact Subgroup.subgroupOf_eq_top.1 hY

theorem oc_core_le_normalizer_all (h : Hyp ρ V Z) (W : Sylow 2 K) :
    pPrimeCore 2 K ≤ normalizer ((W : Subgroup K) : Set K) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K V W
  intro m hm
  have hgm : g⁻¹ * m * g ∈ pPrimeCore 2 K := by
    simpa using (inferInstance : (pPrimeCore 2 K).Normal).conj_mem m hm g⁻¹
  have h1 := oc_core_le_normalizer h hgm
  rw [oc_mem_normalizer_iff] at h1 ⊢
  calc m • (g • V) = g • ((g⁻¹ * m * g) • V) := by
        rw [smul_smul, smul_smul]
        congr 1
        group
    _ = g • V := by rw [h1]

theorem oc_core_comm (h : Hyp ρ V Z) {m v : K} (hm : m ∈ pPrimeCore 2 K)
    (hv : v ∈ (V : Subgroup K)) : m * v = v * m := by
  have hn : m ∈ normalizer ((V : Subgroup K) : Set K) := oc_core_le_normalizer h hm
  have hcM : m * v * m⁻¹ * v⁻¹ ∈ pPrimeCore 2 K := by
    have h1 : v * m⁻¹ * v⁻¹ ∈ pPrimeCore 2 K :=
      (inferInstance : (pPrimeCore 2 K).Normal).conj_mem _ (inv_mem hm) v
    have h2 := mul_mem hm h1
    simpa [mul_assoc] using h2
  have hcV : m * v * m⁻¹ * v⁻¹ ∈ (V : Subgroup K) :=
    mul_mem ((Subgroup.mem_normalizer_iff.1 hn v).1 hv) (inv_mem hv)
  have hodd : Odd (orderOf (m * v * m⁻¹ * v⁻¹)) :=
    Odd.of_dvd_nat (oc_odd_card K) (Subgroup.orderOf_dvd_natCard _ hcM)
  have hdvd : orderOf (m * v * m⁻¹ * v⁻¹) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h.sqV _ hcV)
  have h1 : m * v * m⁻¹ * v⁻¹ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h2 | h2
    · exact orderOf_eq_one_iff.1 h2
    · rw [h2] at hodd
      exact absurd hodd (by decide)
  calc m * v = (m * v * m⁻¹ * v⁻¹) * v * m := by group
    _ = v * m := by rw [h1]; group

omit [Finite K] [Finite A] in
theorem oc_ker (h : Hyp ρ V Z) {v m : K} (hv : v ∈ (V : Subgroup K)) (hv1 : v ≠ 1)
    (hc : m * v = v * m) (hmZ : ∀ a ∈ Z, ρ m a = a) (hodd : Odd (orderOf m)) : m = 1 := by
  have hcomm : ∀ a : A, ρ v (ρ m a) = ρ m (ρ v a) := by
    intro a
    have h2 := congrArg (fun k => ρ k a) hc
    simpa [map_mul] using h2.symm
  have mul4 : ∀ a b c d : A, a * b * (c * d) = a * c * (b * d) := by
    intro a b c d
    calc a * b * (c * d) = a * (b * (c * d)) := mul_assoc _ _ _
      _ = a * (b * c * d) := by rw [mul_assoc b c d]
      _ = a * (c * b * d) := by rw [h.comm b c]
      _ = a * (c * (b * d)) := by rw [mul_assoc c b d]
      _ = a * c * (b * d) := (mul_assoc _ _ _).symm
  have sq_mul : ∀ a b : A, a * b * b = a := fun a b => by rw [mul_assoc, h.sq, mul_one]
  have key : ∀ a : A, ρ m a * a ∈ Z := by
    intro a
    rw [← h.fix v hv hv1]
    have hcZ : ρ v a * a ∈ Z := by
      simpa [inv_eq_of_mul_eq_one_right (h.sq a)] using h.comm_mem hv hv1 a
    calc ρ v (ρ m a * a) = ρ m (ρ v a) * ρ v a := by rw [map_mul, hcomm]
      _ = ρ m ((ρ v a * a) * a) * ((ρ v a * a) * a) := by rw [sq_mul]
      _ = ((ρ v a * a) * ρ m a) * ((ρ v a * a) * a) := by rw [map_mul, hmZ _ hcZ]
      _ = ((ρ v a * a) * (ρ v a * a)) * (ρ m a * a) := mul4 _ _ _ _
      _ = ρ m a * a := by rw [h.sq, one_mul]
  have hmm : ρ (m * m) = 1 := by
    ext a
    obtain ⟨b, hbZ, hba⟩ : ∃ b ∈ Z, ρ m a = b * a := ⟨ρ m a * a, key a, (sq_mul _ _).symm⟩
    rw [map_mul]
    change ρ m (ρ m a) = a
    calc ρ m (ρ m a) = ρ m (b * a) := by rw [hba]
      _ = b * (b * a) := by rw [map_mul, hmZ _ hbZ, hba]
      _ = (b * b) * a := by rw [mul_assoc]
      _ = a := by rw [h.sq b, one_mul]
  have hm2 : m * m = 1 := h.inj (by rw [hmm, map_one])
  have hdvd : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hm2)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h2 | h2
  · exact orderOf_eq_one_iff.1 h2
  · rw [h2] at hodd
    exact absurd hodd (by decide)

theorem oc_core_card_dvd (h : Hyp ρ V Z) : Nat.card (pPrimeCore 2 K) ∣ 3 := by
  obtain ⟨v, hv, hv1⟩ := oc_exists_ne h
  have hcomm : ∀ m ∈ pPrimeCore 2 K, m * v = v * m := fun m hm => oc_core_comm h hm hv
  have hstab : ∀ m ∈ pPrimeCore 2 K, ∀ a ∈ Z, ρ m a ∈ Z :=
    fun m hm => oc_stab_of_comm h hv hv1 (hcomm m hm)
  let : MulAction (pPrimeCore 2 K) Z :=
    { smul := fun m a => ⟨ρ m a, hstab m m.2 a a.2⟩
      one_smul := fun a => Subtype.ext (show ρ ((1 : pPrimeCore 2 K) : K) a = a by simp)
      mul_smul := fun m n a => Subtype.ext
        (show ρ ((m * n : pPrimeCore 2 K) : K) a = ρ m (ρ n a) by simp) }
  have hsmul : ∀ (m : pPrimeCore 2 K) (a : Z), ((m • a : Z) : A) = ρ m a := fun m a => rfl
  have hinj : Function.Injective (MulAction.toPermHom (pPrimeCore 2 K) Z) := by
    rw [injective_iff_map_eq_one]
    intro m hm
    apply Subtype.ext
    refine oc_ker h hv hv1 (hcomm m m.2) (fun a ha => ?_) ?_
    · have h1 := congrArg (fun f => ((f ⟨a, ha⟩ : Z) : A)) hm
      simpa [hsmul] using h1
    · have := Subgroup.orderOf_dvd_natCard _ m.2
      exact Odd.of_dvd_nat (oc_odd_card K) this
  have hdvd : Nat.card (pPrimeCore 2 K) ∣ Nat.card (Equiv.Perm Z) :=
    Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_perm, h.cardZ] at hdvd
  have hcop : Nat.Coprime (Nat.card (pPrimeCore 2 K)) 8 := by
    have := (Nat.coprime_two_right.2 (oc_odd_card K)).pow_right 3
    simpa using this
  exact hcop.dvd_of_dvd_mul_left (by simpa [Nat.factorial] using hdvd)

theorem Hyp.odd_core (h : Hyp ρ V Z) :
    (∀ W : Sylow 2 K, pPrimeCore 2 K ≤ normalizer ((W : Subgroup K) : Set K)) ∧
      Nat.card (pPrimeCore 2 K) ∣ 3 :=
  ⟨oc_core_le_normalizer_all h, oc_core_card_dvd h⟩

end Counting

end CFSG.OddStandard.ThmC.O2.A8
