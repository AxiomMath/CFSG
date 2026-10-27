module

public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.Semidihedral.Local

theorem derivedSeries_eq_top_of_isPerfect {G : Type*} [Group G] [Group.IsPerfect G] (k : ℕ) :
    derivedSeries G k = ⊤ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, Group.IsPerfect.commutator_eq_top]

theorem equal_perfect_section_forces_local_odd_core_intersection {C : Type*} [Group C] [Finite C]
    (N : Subgroup C) [N.Normal] (hN : Odd (Nat.card N)) (Q : Subgroup (C ⧸ N)) [Q.Normal]
    (hsolv : Group.IsSolvable ((C ⧸ N) ⧸ Q))
    (hQodd : ∀ U : Subgroup Q, U.Normal → Odd (Nat.card U) → U = ⊥)
    (hCQ : IsPGroup 2 (Subgroup.centralizer (Q : Set (C ⧸ N))))
    (B : Subgroup C) (Q₀ : Subgroup (B ⧸ CFSG.pPrimeCore 2 B)) [Q₀.Normal]
    (hQ₀ : Group.IsPerfect Q₀) (hcard : Nat.card Q₀ = Nat.card Q)
    (hQ₀odd : ∀ U : Subgroup Q₀, U.Normal → Odd (Nat.card U) → U = ⊥) :
    let π := QuotientGroup.mk' N
    let R := CFSG.pPrimeCore 2 B
    R.map B.subtype = B ⊓ N ∧ Q ≤ B.map π ∧
      ∃ ι : B ⧸ R →* C ⧸ N, Function.Injective ι ∧
        (∀ b : B, ι (QuotientGroup.mk' R b) = π b) ∧ ι.range = B.map π := by
  intro π R
  have hcopN : Nat.Coprime 2 (Nat.card N) := Nat.coprime_two_left.mpr hN
  have hcopR : Nat.Coprime 2 (Nat.card R) := CFSG.pPrimeCore_coprime_card (p := 2) (G := B)
  have hNB : N.subgroupOf B ≤ R := by
    refine le_sSup ⟨inferInstance, hcopN.coprime_dvd_right ?_⟩
    rw [← Subgroup.card_map_of_injective B.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  let T : Subgroup B := Q₀.comap (QuotientGroup.mk' R)
  let ηT : T →* Q₀ := ((QuotientGroup.mk' R).comp T.subtype).codRestrict Q₀ fun x => x.2
  have hηT : Function.Surjective ηT := by
    rintro ⟨q, hq⟩
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective R q
    exact ⟨⟨b, hq⟩, rfl⟩
  obtain ⟨⟨k, hk, -⟩, -, hPperf, -⟩ := CFSG.perfect_residual_characterization (G := T)
  have hPmap : (CFSG.perfectResidual T).map ηT = ⊤ := by
    rw [hk, map_derivedSeries_eq hηT, derivedSeries_eq_top_of_isPerfect]
  let ι₀ : CFSG.perfectResidual T →* B := T.subtype.comp (CFSG.perfectResidual T).subtype
  let φ₁ : CFSG.perfectResidual T →* C ⧸ N := π.comp (B.subtype.comp ι₀)
  let ψ : CFSG.perfectResidual T →* Q₀ := ηT.comp (CFSG.perfectResidual T).subtype
  have hψ : Function.Surjective ψ := by
    intro q
    have hq : q ∈ (CFSG.perfectResidual T).map ηT := by
      rw [hPmap]
      exact Subgroup.mem_top q
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : φ₁.ker ≤ ψ.ker := by
    have hUodd : Odd (Nat.card φ₁.ker) := by
      have hinj : Function.Injective (B.subtype.comp ι₀) := fun a b h =>
        Subtype.ext (Subtype.ext (Subtype.ext h))
      have hle : φ₁.ker.map (B.subtype.comp ι₀) ≤ N := by
        rintro _ ⟨x, hx, rfl⟩
        exact (QuotientGroup.eq_one_iff _).mp hx
      have h1 := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective hinj] at h1
      exact Odd.of_dvd_nat hN h1
    have hUψ : φ₁.ker.map ψ = ⊥ := hQ₀odd _ (Subgroup.Normal.map inferInstance ψ hψ)
      (Odd.of_dvd_nat hUodd (Subgroup.card_map_dvd _ _))
    intro x hx
    have h1 : ψ x ∈ φ₁.ker.map ψ := Subgroup.mem_map_of_mem ψ hx
    rw [hUψ] at h1
    exact h1
  have hrangeQ : φ₁.range ≤ Q := by
    have := hsolv
    let g : T →* (C ⧸ N) ⧸ Q := (QuotientGroup.mk' Q).comp (π.comp (B.subtype.comp T.subtype))
    have hXperf : Group.IsPerfect ((CFSG.perfectResidual T).map g) := Group.IsPerfect.map g
    have hXbot : (CFSG.perfectResidual T).map g = ⊥ := by
      by_contra hne
      have : Nontrivial ((CFSG.perfectResidual T).map g) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      exact Group.IsPerfect.not_isSolvable ((CFSG.perfectResidual T).map g) inferInstance
    rintro _ ⟨x, rfl⟩
    have h1 : g x ∈ (CFSG.perfectResidual T).map g := Subgroup.mem_map_of_mem g x.2
    rw [hXbot, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hψrange : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr hψ
  have hcard_le : Nat.card Q ≤ Nat.card φ₁.range := by
    have h1 : Nat.card Q₀ = ψ.ker.index := by
      rw [Subgroup.index_ker, hψrange, Subgroup.card_top]
    rw [← hcard, h1, ← Subgroup.index_ker φ₁]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker)
  have hrange_eq : φ₁.range = Q := Subgroup.eq_of_le_of_card_ge hrangeQ hcard_le
  have hQB : Q ≤ B.map π := by
    rw [← hrange_eq]
    rintro _ ⟨x, rfl⟩
    exact ⟨ι₀ x, (ι₀ x).2, rfl⟩
  have hRN : R.map (π.comp B.subtype) = ⊥ := by
    have hUodd : Odd (Nat.card (R.map (π.comp B.subtype))) :=
      Nat.coprime_two_left.mp (hcopR.coprime_dvd_right (Subgroup.card_map_dvd _ _))
    have hUQ : ∀ q ∈ Q, ∀ u ∈ R.map (π.comp B.subtype),
        q * u * q⁻¹ ∈ R.map (π.comp B.subtype) := by
      intro q hq u hu
      obtain ⟨b, hb, rfl⟩ := hQB hq
      obtain ⟨r, hr, rfl⟩ := hu
      refine ⟨⟨b, hb⟩ * r * ⟨b, hb⟩⁻¹,
        (CFSG.pPrimeCore_normal (p := 2) (G := B)).conj_mem r hr ⟨b, hb⟩, ?_⟩
      simp only [map_mul, map_inv]
      rfl
    have hinf : (R.map (π.comp B.subtype) ⊓ Q).subgroupOf Q = ⊥ := by
      refine hQodd _ ?_ ?_
      · constructor
        intro x hx q
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact ⟨hUQ q q.2 x hx.1, Q.mul_mem (Q.mul_mem q.2 hx.2) (Q.inv_mem q.2)⟩
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
        exact Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left)
    have hUC : R.map (π.comp B.subtype) ≤ Subgroup.centralizer (Q : Set (C ⧸ N)) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 : q * u * q⁻¹ * u⁻¹ ∈ R.map (π.comp B.subtype) :=
        Subgroup.mul_mem _ (hUQ q hq u hu) (Subgroup.inv_mem _ hu)
      have h2 : q * u * q⁻¹ * u⁻¹ ∈ Q := by
        have h3 : u * q⁻¹ * u⁻¹ ∈ Q := (inferInstance : Q.Normal).conj_mem _ (Q.inv_mem hq) u
        have h4 := Q.mul_mem hq h3
        rwa [← mul_assoc, ← mul_assoc] at h4
      have h5 : q * u * q⁻¹ * u⁻¹ = 1 := by
        have h6 : (⟨_, h2⟩ : Q) ∈ (R.map (π.comp B.subtype) ⊓ Q).subgroupOf Q := ⟨h1, h2⟩
        rw [hinf, Subgroup.mem_bot] at h6
        exact congrArg Subtype.val h6
      calc q * u = q * u * q⁻¹ * u⁻¹ * (u * q) := by group
        _ = u * q := by rw [h5, one_mul]
    obtain ⟨j, hj⟩ := (hCQ.to_le hUC).exists_card_eq
    have hj0 : j = 0 := by
      by_contra h
      rw [hj] at hUodd
      exact (Nat.not_even_iff_odd.mpr hUodd) ((Nat.even_pow' h).mpr even_two)
    rw [hj0, pow_zero] at hj
    exact Subgroup.card_eq_one.mp hj
  have hR : R.map B.subtype = B ⊓ N := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      refine ⟨r.2, ?_⟩
      have h1 : (π.comp B.subtype) r ∈ R.map (π.comp B.subtype) := Subgroup.mem_map_of_mem _ hr
      rw [hRN, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    · rintro x ⟨hxB, hxN⟩
      exact ⟨⟨x, hxB⟩, hNB hxN, rfl⟩
  have hkerB : (π.comp B.subtype).ker = R := by
    ext b
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (b : C) ∈ N := (QuotientGroup.eq_one_iff _).mp h
      exact hNB h1
    · intro h
      have h1 : (b : C) ∈ B ⊓ N := by
        rw [← hR]
        exact ⟨b, h, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mpr h1.2
  let ι : B ⧸ R →* C ⧸ N := QuotientGroup.lift R (π.comp B.subtype) hkerB.ge
  refine ⟨hR, hQB, ι, ?_, fun _ => rfl, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, hkerB, QuotientGroup.map_mk'_self]
  · ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ q
      exact ⟨b, b.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨QuotientGroup.mk' _ ⟨c, hc⟩, rfl⟩

end CFSG.Semidihedral.Local
