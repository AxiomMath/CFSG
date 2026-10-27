module

public import CFSG.GH74.Generic.BProg.B3.S45EvenN5D8
public import CFSG.GH74.Generic.BProg.B3.S45EvenDefs
public import CFSG.GH74.Generic.S45.LPsuCover
public import CFSG.GH74.Generic.S45.LUniHyp

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.Generic.BProg.B3.S45TableA CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.Generic.S45

namespace S45EvenN5

theorem exists_prime_pow_of_card_sq {F : Type} [Field F] [Finite F] {q : ℕ}
    (hFq : Nat.card F = q ^ 2) (hq : q % 4 = 1) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ q = p ^ f := by
  have := Fintype.ofFinite F
  obtain ⟨p, _, n, hp, hn⟩ := FiniteField.card' (K := F)
  have hdvd : q ∣ p ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hFq]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hq1 : q ≠ 1 := by
    rintro rfl
    have : 1 < Fintype.card F := Fintype.one_lt_card
    rw [← Nat.card_eq_fintype_card, hFq] at this
    simp at this
  refine ⟨p, f, hp, ?_, ?_, hf⟩
  · rintro rfl
    rcases Nat.eq_zero_or_pos f with rfl | hf0
    · exact hq1 (by simpa using hf)
    · have : 2 ∣ q := by rw [hf]; exact dvd_pow_self 2 hf0.ne'
      omega
  · rcases Nat.eq_zero_or_pos f with rfl | hf0
    · exact absurd (by simpa using hf) hq1
    · exact hf0

theorem su_split {p f n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F) (hp2 : p ≠ 2)
    (hn : 3 ≤ n) :
    ∀ (E : Type) [Group E] [Finite E] (π : E →* ↥(unitarySU p f F n)),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker →
        ∃ σ : ↥(unitarySU p f F n) →* E, ∀ x, π (σ x) = x := by
  classical
  have : Finite F := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hK : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  intro E _ _ π hπ hcen h2'
  set ι := CFSG.LieType.Universal.Unitary.equivStatedSU hK n with hι
  let π' : E →* CFSG.LieType.Universal.Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F p f) n :=
    ι.symm.toMonoidHom.comp π
  have hπ' : Function.Surjective π' := ι.symm.surjective.comp hπ
  have hker : π'.ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change ι.symm (π x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
  obtain ⟨s, hs, -⟩ := CFSG.LieType.Steinberg.su_central_two_extension_splitting hK hp2 (n := n)
    (by omega) hπ' (hker ▸ hcen) (hker ▸ h2')
  refine ⟨s.comp ι.symm.toMonoidHom, fun x => ?_⟩
  have := hs (ι.symm x)
  change ι.symm (π (s (ι.symm x))) = ι.symm x at this
  exact ι.symm.injective this

theorem exists_fixed_dvd_four_su4 {X : Type} [Group X] [Finite X] {p f : ℕ} {F : Type} [Field F]
    (hud : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    (e : X ≃* ↥(unitarySU p f F 4)) {y : MulAut X} (hy : orderOf y = 2) :
    ∃ x : X, y x = x ∧ 4 ∣ orderOf x := by
  classical
  have : Finite F := hud.finite
  have : Fact p.Prime := ⟨hud.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hperfSU, hcenSU⟩ := isPerfect_and_center_unitarySU' hud hp2 (by norm_num : 3 ≤ 4)
  have hperf : Group.IsPerfect X := by
    have := hperfSU
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcard : Nat.card (Subgroup.center X) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hcenSU,
      card_unitaryScalars hud (by norm_num)]
    have h1 := Nat.gcd_rec 4 (p ^ f + 1)
    rw [show (p ^ f + 1) % 4 = 2 by omega] at h1
    simpa using h1
  have hZ2 : IsPGroup 2 ↥(Subgroup.center X) := IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  obtain ⟨yb, hyb, hyb1, hyb2⟩ := LAlt.exists_induced_quotient hperf y hy
  have hmap : (Subgroup.center X).map e.toMonoidHom =
      (StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (p ^ f) F) := by
    rw [← unitaryScalars_eq hud (by norm_num : 1 ≤ 4), ← hcenSU]
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro k
      obtain ⟨k', rfl⟩ := e.surjective k
      show e k' * e z = e z * e k'
      rw [← map_mul, ← map_mul, hz k']
    · intro hg
      refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
      rw [Subgroup.mem_center_iff] at hg ⊢
      intro k
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hg (e k)
  have hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 4 p f :=
    ⟨⟨hud.prime, hud.one_le, by norm_num, fun h => by simpa using congrArg Prod.fst h⟩, F, inferInstance,
      hud.finite, hud.card_eq_sq, ⟨QuotientGroup.congr _ _ e hmap⟩⟩
  obtain ⟨F', _, h', θ, τ, c, hθ, hτ, hc, hord⟩ := psu_fixed_data (n := 4) (by norm_num) hp2 hmodel
    (fun h A l hAu hAA hNl => Uni.fixed_class1b_four h hp2 A l hAu hAA hNl)
    (fun h A hAu hAA => Uni.fixed_class2alt h (Uni.two_ne_zero_of_ne h hp2) (by norm_num) A hAu hAA)
    hyb2
  have : Finite F' := h'.finite
  have hPp' : Group.IsPerfect ↥(unitarySU p f F' 4) :=
    (isPerfect_and_center_unitarySU' h' hp2 (by norm_num : 3 ≤ 4)).1
  let η : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hη : Function.Surjective η := QuotientGroup.mk'_surjective _
  have hηker : η.ker = Subgroup.center X := QuotientGroup.ker_mk' _
  have hη2 : IsPGroup 2 η.ker := by rw [hηker]; exact hZ2
  exact exists_fixed_dvd_of_cover hperf hPp' (su_split h' hp2 (by norm_num)) hη hηker.le hη2 hθ
    (y := y) (yb := yb) (fun k => (hyb k).symm) hτ hc (by rw [hord])

theorem false_of_fixed_dvd_four {X : Type} [Group X] [Finite X] {y : MulAut X}
    (h1 : ∀ s : X, y s = s → ∀ k : ℕ, s ^ (2 ^ k) = 1 → s ^ 2 = 1) {x : X} (hx : y x = x)
    (h4 : 4 ∣ orderOf x) : False := by
  have hpos : 0 < orderOf x := orderOf_pos x
  obtain ⟨a, m, hm, hmx⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  have ha : 2 ≤ a := by
    by_contra h
    rw [hmx] at h4
    obtain ⟨j, hj⟩ := hm
    interval_cases a <;> simp at h4 <;> omega
  have hs : y (x ^ m) = x ^ m := by rw [map_pow, hx]
  have h2k : (x ^ m) ^ (2 ^ a) = 1 := by
    rw [← pow_mul, mul_comm, ← hmx]
    exact pow_orderOf_eq_one x
  have h3 := h1 _ hs a h2k
  have h4' : orderOf x ∣ m * 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact h3)
  rw [hmx, mul_comm (2 ^ a) m] at h4'
  have h5 : 2 ^ a ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hm.pos h4'
  have h6 : 2 ^ a ≤ 2 := Nat.le_of_dvd (by norm_num) h5
  have h7 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  omega

end S45EvenN5

theorem N5_su4 {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {q : ℕ}
    (hFq : Nat.card F = q ^ 2) (hq : q % 4 = 1) (e : X ≃* ↥(StatedSU 4 q F)) {y : MulAut X}
    (hy : orderOf y = 2) (hd : Datum X y)
    (hab : ∀ T : Subgroup X, IsPGroup 2 ↥T → (∀ t ∈ T, y t = t) → ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hEA : EvenEA X y) : False := by
  classical
  obtain ⟨p, f, hp, hp2, hf, rfl⟩ := S45EvenN5.exists_prime_pow_of_card_sq hFq hq
  have hud : UnitaryFieldData p f F := ⟨hp, hf, by rw [hFq, ← pow_mul, mul_comm]⟩
  rcases hEA with h1 | ⟨t, htt, htc, hyt⟩
  · obtain ⟨x, hx, h4⟩ := S45EvenN5.exists_fixed_dvd_four_su4 hud hp2 hq e hy
    exact S45EvenN5.false_of_fixed_dvd_four h1 hx h4
  · have hte : ((e t : ↥(unitarySU p f F 4)) : GL (Fin 4) F) * ((e t : ↥(unitarySU p f F 4)) : GL (Fin 4) F) = 1 := by
      have h0 : e t * e t = 1 := by rw [← map_mul, htt, map_one]
      have := congrArg (fun z : ↥(unitarySU p f F 4) => (z : GL (Fin 4) F)) h0
      simpa using this
    obtain ⟨a, b, ha, hb, hat, hbt, ha4, ha2, hb2, hba⟩ :=
      S45EvenN5D8.exists_D8_comm_su4 hud hp2 (e t).2 hte
    let aS : ↥(unitarySU p f F 4) := ⟨a, ha⟩
    let bS : ↥(unitarySU p f F 4) := ⟨b, hb⟩
    have hyfix : ∀ g : ↥(unitarySU p f F 4), (g : GL (Fin 4) F) * ((e t : ↥(unitarySU p f F 4)) : GL (Fin 4) F) =
        ((e t : ↥(unitarySU p f F 4)) : GL (Fin 4) F) * g → y (e.symm g) = e.symm g := fun g hg => by
      have hg' : e.symm g * t = t * e.symm g := by
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact Subtype.ext hg
      rw [hyt, mul_inv_eq_iff_eq_mul]
      exact hg'.symm
    have h5 : Hyp5w X y := ⟨hy, hab, hd⟩
    refine h5.false_of_dihedral (a := e.symm aS) (b := e.symm bS) (hyfix aS hat) (hyfix bS hbt) ?_ ?_ ?_ ?_
    · rw [← map_pow]
      have : aS ^ 4 = 1 := Subtype.ext (by simpa [aS] using ha4)
      rw [this, map_one]
    · intro h
      rw [← map_pow] at h
      have h' : aS ^ 2 = 1 := e.symm.injective (by rw [h, map_one])
      exact ha2 (by simpa [aS] using congrArg Subtype.val h')
    · rw [← map_mul]
      have : bS * bS = 1 := Subtype.ext (by simpa [bS] using hb2)
      rw [this, map_one]
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
      congr 1
      apply Subtype.ext
      simpa [aS, bS] using hba

end CFSG.GH74.Generic.BProg.B3
