module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Perm
public import CFSG.GH74.Uniqueness.SU.SU13TA1Invol

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Uniqueness.SU.SU13.TA Equiv Equiv.Perm
  CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

theorem pPrimeCore_two_eq_bot {P : Type*} [Group P] [Finite P] (h : IsPGroup 2 P) :
    pPrimeCore 2 P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop := pPrimeCore_coprime_card (p := 2) (G := P)
  obtain ⟨k, hk⟩ := h.exists_card_eq
  have hd : Nat.card ↥(pPrimeCore 2 P) ∣ 2 ^ k := hk ▸ Subgroup.card_subgroup_dvd_card _
  have h1 : Nat.card ↥(pPrimeCore 2 P) = 1 :=
    Nat.Coprime.eq_one_of_dvd (hcop.symm.pow_right k) hd
  exact Subgroup.card_eq_one.mp h1

theorem exists_sylow_iso {R P : Type*} [Group R] [Finite R] [Group P] [Finite P]
    (hP : IsPGroup 2 P) (e : P ≃* (R ⧸ pPrimeCore 2 R)) :
    ∃ (T : Subgroup R), IsPGroup 2 ↥T ∧ Nonempty (P ≃* ↥T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O := pPrimeCore 2 R
  let q : R →* R ⧸ O := QuotientGroup.mk' O
  obtain ⟨T⟩ : Nonempty (Sylow 2 R) := inferInstance
  have hcopO : Nat.Coprime 2 (Nat.card ↥O) := pPrimeCore_coprime_card
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hQ : Nat.card (R ⧸ O) = 2 ^ k := by rw [← Nat.card_congr e.toEquiv, hk]
  have hR : Nat.card R = 2 ^ k * Nat.card ↥O := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup O, hQ]
  have hTcard : Nat.card ↥(T : Subgroup R) = 2 ^ k := by
    rw [Sylow.card_eq_multiplicity, hR, Nat.factorization_mul (by positivity)
      (Nat.card_pos).ne', Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd]
    · simp
    · intro hd
      have := Nat.Coprime.eq_one_of_dvd hcopO hd
      omega
  have hinj : Function.Injective (q.comp (T : Subgroup R).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : (x : R) ∈ O := (QuotientGroup.eq_one_iff _).mp hx
    have hx2 : orderOf (x : R) ∣ 2 ^ k := by
      rw [Subgroup.orderOf_coe]
      exact hTcard ▸ orderOf_dvd_natCard x
    have hxO' : orderOf (x : R) ∣ Nat.card ↥O := by
      have := orderOf_dvd_natCard (⟨(x : R), hxO⟩ : ↥O)
      rwa [Subgroup.orderOf_mk] at this
    have hg : Nat.gcd (2 ^ k) (Nat.card ↥O) = 1 := (Nat.Coprime.pow_left k hcopO).gcd_eq_one
    have hxo : orderOf x = 1 := by
      have h1 : orderOf (x : R) ∣ Nat.gcd (2 ^ k) (Nat.card ↥O) := Nat.dvd_gcd hx2 hxO'
      rw [hg, Nat.dvd_one, Subgroup.orderOf_coe] at h1
      exact h1
    exact orderOf_eq_one_iff.mp hxo
  have hbij : Function.Bijective (q.comp (T : Subgroup R).subtype) :=
    hinj.bijective_of_nat_card_le (by rw [hQ, hTcard])
  exact ⟨T, T.isPGroup', ⟨e.trans (MulEquiv.ofBijective _ hbij).symm⟩⟩


section Model

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}

theorem zb_comm (hfr : AFrame A zb Sb Vb) : ∀ s ∈ Sb, s * zb = zb * s := by
  have hP : IsPGroup 2 ↥Sb := hfr.sylow.isPGroup
  have hne : (⊤ : Subgroup ↥Sb) ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥Sb = 1 := by
      have := Subgroup.card_eq_one.mpr h
      simpa using this
    have := hfr.card
    omega
  obtain ⟨w, -, hwc, hw2⟩ := Gen.exists_involution_center_of_normal hP hne
  have hwcomm : ∀ s ∈ Sb, s * ((w : ↥Sb) : A) = ((w : ↥Sb) : A) * s := fun s hs =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hwc ⟨s, hs⟩)
  have hwz : ((w : ↥Sb) : A) = zb :=
    hfr.zcen _ w.2 hwcomm (by rw [Subgroup.orderOf_coe]; exact hw2)
  intro s hs
  rw [← hwz]
  exact hwcomm s hs

end Model

section Model2

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}

theorem card_alt_ten : Nat.card (alternatingGroup (Fin 10)) = 1814400 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

theorem two_adic_alt (n : ℕ) (hn : n = 10 ∨ n = 11) :
    (Nat.card (alternatingGroup (Fin n))).factorization 2 = 7 := by
  rcases hn with rfl | rfl
  · rw [card_alt_ten, show (1814400 : ℕ) = 2 ^ 7 * 14175 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simp
  · exact factorization_card_alternatingGroup_eleven

theorem exists_sb_hom (hfr : AFrame A zb Sb Vb) :
    ∃ (n : ℕ) (Θ : ↥Sb →* Perm (Fin n)), (n = 10 ∨ n = 11) ∧
      (∀ s : ↥Sb, Θ s = 1 ↔ (s : A) = 1 ∨ (s : A) = zb) ∧
      (∀ s : ↥Sb, Θ s ∈ alternatingGroup (Fin n)) ∧ Nat.card ↥Θ.range = 2 ^ 7 ∧
      (∀ s : ↥Sb, (Θ s).cycleType = {2, 2, 2, 2} → (s : A) * (s : A) = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzc := zb_comm hfr
  have hP : IsPGroup 2 ↥Sb := hfr.sylow.isPGroup
  obtain ⟨n, K, instK, R', hn, hcov, ⟨e⟩⟩ := hfr.cbar zb hfr.zb_ord Sb (fun s hs => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hzc s hs)
  obtain ⟨hKq, hZ, ⟨eK⟩⟩ := hcov
  have hKfin : Finite K := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
    rw [hZ, Nat.card_congr eK.toEquiv] at h
    apply Nat.finite_of_card_ne_zero
    rw [h]
    have : 0 < Nat.card (alternatingGroup (Fin n)) := Nat.card_pos
    omega
  let π : K →* alternatingGroup (Fin n) := eK.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hker : π.ker = center K := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : eK ((QuotientGroup.mk' (center K)) x) = 1 := hx
      exact (QuotientGroup.eq_one_iff x).mp ((map_eq_one_iff eK eK.injective).mp h1)
    · intro hx
      have h1 : (QuotientGroup.mk' (center K)) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      show eK ((QuotientGroup.mk' (center K)) x) = 1
      rw [h1, map_one]
  have hπ : TwoCover π :=
    ⟨eK.surjective.comp (QuotientGroup.mk'_surjective _), hker.le, by rw [hker]; exact hZ,
      hKq.1⟩
  have hbot : pPrimeCore 2 ↥Sb = ⊥ := pPrimeCore_two_eq_bot hP
  let e' : ↥Sb ≃* (↥R' ⧸ pPrimeCore 2 ↥R') :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e
  obtain ⟨T, hTp, ⟨φ⟩⟩ := exists_sylow_iso hP e'
  let ρ : ↥T →* alternatingGroup (Fin n) := π.comp (R'.subtype.comp T.subtype)
  have hTcard : Nat.card ↥T = 2 ^ 8 := by rw [← Nat.card_congr φ.toEquiv, hfr.card]
  have hρker_le : Nat.card ↥ρ.ker ≤ 2 := by
    let g : ↥ρ.ker → ↥π.ker := fun t => ⟨(((t : ↥T) : ↥R') : K), t.2⟩
    have hg : Function.Injective g := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext (Subtype.ext h1))
    have := Nat.card_le_card_of_injective g hg
    rwa [hπ.card_ker] at this
  have hmul := Subgroup.card_ker_mul_card_range ρ
  rw [hTcard] at hmul
  have hrange_dvd : Nat.card ↥ρ.range ∣ Nat.card (alternatingGroup (Fin n)) :=
    Subgroup.card_subgroup_dvd_card _
  have hN0 : Nat.card (alternatingGroup (Fin n)) ≠ 0 := Nat.card_pos.ne'
  have h2ker : Nat.card ↥ρ.ker = 2 := by
    have hdvd : Nat.card ↥ρ.ker ∣ 2 ^ 8 := Dvd.intro _ hmul
    have hpos : 0 < Nat.card ↥ρ.ker := Nat.card_pos
    by_contra hne
    have h1 : Nat.card ↥ρ.ker = 1 := by omega
    rw [h1, one_mul] at hmul
    rw [hmul] at hrange_dvd
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).mp hrange_dvd
    rw [two_adic_alt n hn] at this
    omega
  have hrange_card : Nat.card ↥ρ.range = 2 ^ 7 := by
    rw [h2ker] at hmul
    omega
  obtain ⟨y, hy1, hyu⟩ := (Nat.card_eq_two_iff' (1 : ↥ρ.ker)).mp h2ker
  have hker_cases : ∀ x : ↥ρ.ker, x = 1 ∨ x = y := fun x => by
    by_cases hx : x = 1
    · exact Or.inl hx
    · exact Or.inr (hyu x hx)
  let t₀ : ↥T := (y : ↥T)
  have ht₀ρ : ρ t₀ = 1 := y.2
  have ht₀1 : t₀ ≠ 1 := fun h => hy1 (Subtype.ext h)
  have ht₀sq : t₀ * t₀ = 1 := by
    have h := pow_card_eq_one' (G := ↥ρ.ker) (x := y)
    rw [h2ker, pow_two] at h
    exact congrArg Subtype.val h
  let s₀ : ↥Sb := φ.symm t₀
  have hs₀c : ∀ s : ↥Sb, s * s₀ = s₀ * s := by
    intro s
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    apply Subtype.ext
    have hmem : (((t₀ : ↥T) : ↥R') : K) ∈ π.ker := ht₀ρ
    have hc := Subgroup.mem_center_iff.mp (hπ.ker_le_center hmem)
      ((((φ s : ↥T) : ↥R')) : K)
    exact hc
  have hs₀sq : s₀ * s₀ = 1 := by
    apply φ.injective
    rw [map_mul, MulEquiv.apply_symm_apply, map_one]
    exact ht₀sq
  have hs₀1 : s₀ ≠ 1 := fun h => ht₀1 (by
    have := congrArg φ h
    rwa [MulEquiv.apply_symm_apply, map_one] at this)
  have hs₀ord : orderOf (s₀ : A) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hs₀sq) hs₀1
  have hs₀zb : (s₀ : A) = zb :=
    hfr.zcen _ s₀.2 (fun s hs => congrArg Subtype.val (hs₀c ⟨s, hs⟩)) hs₀ord
  let Θ : ↥Sb →* Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp (ρ.comp φ.toMonoidHom)
  have hΘapply : ∀ s : ↥Sb, Θ s = ((ρ (φ s) : alternatingGroup (Fin n)) : Perm (Fin n)) :=
    fun s => rfl
  have hΘker : ∀ s : ↥Sb, Θ s = 1 ↔ s = 1 ∨ s = s₀ := by
    intro s
    rw [hΘapply]
    constructor
    · intro h
      have hρ : ρ (φ s) = 1 := Subtype.ext h
      rcases hker_cases ⟨φ s, hρ⟩ with h1 | h1
      · left
        have := congrArg Subtype.val h1
        exact φ.injective (by simpa using this)
      · right
        have := congrArg Subtype.val h1
        exact φ.injective (by simpa [s₀, t₀] using this)
    · rintro (rfl | rfl)
      · simp
      · have : ρ (φ s₀) = 1 := by simpa [s₀] using ht₀ρ
        rw [this]
        rfl
  refine ⟨n, Θ, hn, ?_, fun s => (ρ (φ s)).2, ?_, ?_⟩
  · intro s
    rw [hΘker, ← hs₀zb]
    constructor
    · rintro (rfl | rfl)
      · left; rfl
      · right; rfl
    · rintro (h | h)
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
  · have hrange : Θ.range = ρ.range.map (alternatingGroup (Fin n)).subtype := by
      ext y
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨ρ (φ s), ⟨φ s, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
        exact ⟨φ.symm t, by simp [Θ]⟩
    rw [hrange, Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective]
    exact hrange_card
  · intro s hs
    have hx : (π (((φ s : ↥T) : ↥R') : K) : alternatingGroup (Fin n)).val.cycleType =
        {2, 2, 2, 2} := hs
    have hn8 : 8 ≤ n := by rcases hn with rfl | rfl <;> norm_num
    have hsq := hπ.sq_eq_one_of_cycleType_two_two_two_two hn8 hx
    have h1 : (φ s) ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hsq
    have h2 : s ^ 2 = 1 := by
      apply φ.injective
      rw [map_pow, h1, map_one]
    have := congrArg Subtype.val h2
    simpa [pow_two] using this

theorem normal_contains_involution (hfr : AFrame A zb Sb Vb) {N : Subgroup A} (hNS : N ≤ Sb)
    (hNn : ∀ s ∈ Sb, ∀ x ∈ N, s * x * s⁻¹ ∈ N) (hN : ¬ N ≤ Subgroup.zpowers zb) :
    ∃ w ∈ N, orderOf w = 2 ∧ w ≠ zb := by
  obtain ⟨n, Θ, hn, hker, halt, hcard, hlift⟩ := exists_sb_hom hfr
  let Nsb : Subgroup ↥Sb := N.subgroupOf Sb
  let N' : Subgroup (Perm (Fin n)) := Nsb.map Θ
  have hT : Θ.range ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨s, rfl⟩
    exact halt s
  have hN'T : N' ≤ Θ.range := Subgroup.map_le_range Θ Nsb
  have hN'n : ∀ t ∈ Θ.range, ∀ x ∈ N', t * x * t⁻¹ ∈ N' := by
    rintro _ ⟨s, rfl⟩ _ ⟨u, hu, rfl⟩
    refine ⟨s * u * s⁻¹, ?_, by simp⟩
    have hu' : (u : A) ∈ N := Subgroup.mem_subgroupOf.mp hu
    show s * u * s⁻¹ ∈ Nsb
    rw [Subgroup.mem_subgroupOf]
    simpa using hNn _ s.2 _ hu'
  have hN'1 : N' ≠ ⊥ := by
    obtain ⟨x, hx, hxz⟩ := Set.not_subset.mp hN
    have hx1 : x ≠ 1 := fun h => hxz (h ▸ Subgroup.one_mem _)
    have hxz' : x ≠ zb := fun h => hxz (h ▸ Subgroup.mem_zpowers zb)
    intro h
    have hu : (⟨x, hNS hx⟩ : ↥Sb) ∈ Nsb := Subgroup.mem_subgroupOf.mpr hx
    have : Θ ⟨x, hNS hx⟩ ∈ N' := ⟨_, hu, rfl⟩
    rw [h, Subgroup.mem_bot, hker] at this
    rcases this with h1 | h1
    · exact hx1 h1
    · exact hxz' h1
  obtain ⟨g, hgN', hgcyc⟩ : ∃ g ∈ N', g.cycleType = {2, 2, 2, 2} := by
    rcases hn with rfl | rfl
    · exact L1Perm.exists_type2222_of_card10 hT hcard hN'T hN'n hN'1
    · exact L1Perm.exists_type2222_of_card hT hcard hN'T hN'n hN'1
  obtain ⟨w, hw, rfl⟩ := hgN'
  have hsq : (w : A) * (w : A) = 1 := hlift w hgcyc
  have hg1 : Θ w ≠ 1 := by
    intro h
    rw [h, Equiv.Perm.cycleType_one] at hgcyc
    exact absurd hgcyc (by decide)
  have hw1 : (w : A) ≠ 1 := fun h => hg1 ((hker w).mpr (Or.inl h))
  have hwz : (w : A) ≠ zb := fun h => hg1 ((hker w).mpr (Or.inr h))
  exact ⟨(w : A), Subgroup.mem_subgroupOf.mp hw,
    orderOf_eq_prime (by rw [pow_two]; exact hsq) hw1, hwz⟩

theorem exists_elemAbelian_sb (hfr : AFrame A zb Sb Vb) :
    ∃ E : Subgroup ↥Sb, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x * x = 1) ∧
      16 ≤ Nat.card ↥E := by
  let S : Set ℕ := {r | ∃ B : Subgroup ↥Sb, IsElementaryAbelian 2 ↥B ∧ Nat.card ↥B = 2 ^ r}
  have hr : 4 ≤ sSup S := hfr.rank_lo
  have hne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, csSup_empty] at hr
    simp at hr
  have hbdd : BddAbove S := by
    refine ⟨8, fun r hr' => ?_⟩
    obtain ⟨B, -, hB⟩ := hr'
    have h1 : Nat.card ↥B ∣ Nat.card ↥Sb := Subgroup.card_subgroup_dvd_card B
    rw [hB, hfr.card] at h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
  obtain ⟨B, hB, hBc⟩ := Nat.sSup_mem hne hbdd
  have := hB
  refine ⟨B, fun x hx y hy => ?_, fun x hx => ?_, ?_⟩
  · exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  · have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) x hx
    rwa [pow_two] at this
  · rw [hBc]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ sSup S := Nat.pow_le_pow_right (by norm_num) hr

theorem exists_elemAbelian_image (hfr : AFrame A zb Sb Vb) {M : Type*} [Group M] [Finite M]
    (ψ : ↥Sb →* M)
    (hker : ∀ s : ↥Sb, ψ s = 1 → (s : A) = 1 ∨ (s : A) = zb) :
    ∃ E : Subgroup M, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x * x = 1) ∧
      16 ≤ Nat.card ↥E := by
  by_cases hz : ψ ⟨zb, hfr.zb_mem⟩ = 1
  ·
    obtain ⟨n, Θ, hn, hkerΘ, halt, hcard, -⟩ := exists_sb_hom hfr
    have hT : Θ.range ≤ alternatingGroup (Fin n) := by
      rintro _ ⟨s, rfl⟩
      exact halt s
    obtain ⟨E₁, hE₁T, hE₁c, hE₁s, hE₁card⟩ : ∃ E : Subgroup (Perm (Fin n)), E ≤ Θ.range ∧
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x * x = 1) ∧ 16 ≤ Nat.card ↥E := by
      rcases hn with rfl | rfl
      · exact L1Perm.exists_elemAbelian_of_card10 hT hcard
      · exact L1Perm.exists_elemAbelian_of_card hT hcard
    have hψ1 : ∀ s : ↥Sb, ((s : A) = 1 ∨ (s : A) = zb) → ψ s = 1 := by
      rintro s (h | h)
      · have : s = 1 := Subtype.ext h
        rw [this, map_one]
      · have : s = ⟨zb, hfr.zb_mem⟩ := Subtype.ext h
        rw [this]
        exact hz
    let Eh : Subgroup ↥Sb := E₁.comap Θ
    refine ⟨Eh.map ψ, ?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hc : Θ a * Θ b = Θ b * Θ a := hE₁c _ ha _ hb
      have h1 : Θ (a * b * (b * a)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, map_mul, hc, mul_inv_cancel]
      have h2 := hψ1 _ ((hkerΘ _).mp h1)
      rw [map_mul, map_inv, map_mul, mul_inv_eq_one, map_mul] at h2
      exact h2
    · rintro _ ⟨a, ha, rfl⟩
      have hc : Θ a * Θ a = 1 := hE₁s _ ha
      have h1 : Θ (a * a) = 1 := by rw [map_mul]; exact hc
      have h2 := hψ1 _ ((hkerΘ _).mp h1)
      rwa [map_mul] at h2
    · have hsurj : ∀ e : ↥E₁, ∃ s : ↥Sb, Θ s = e := fun e => hE₁T e.2
      choose f hf using hsurj
      have hmem : ∀ e : ↥E₁, ψ (f e) ∈ Eh.map ψ := fun e =>
        ⟨f e, by show Θ (f e) ∈ E₁; rw [hf]; exact e.2, rfl⟩
      have hinj : Function.Injective (fun e : ↥E₁ => (⟨ψ (f e), hmem e⟩ : ↥(Eh.map ψ))) := by
        intro e e' h
        have h1 : ψ (f e) = ψ (f e') := congrArg Subtype.val h
        have h2 : ψ ((f e')⁻¹ * f e) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
        have h3 : Θ ((f e')⁻¹ * f e) = 1 := (hkerΘ _).mpr (hker _ h2)
        rw [map_mul, map_inv, hf, hf, inv_mul_eq_one] at h3
        exact Subtype.ext h3.symm
      exact hE₁card.trans (Nat.card_le_card_of_injective _ hinj)
  · have hinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro s hs
      rcases hker s hs with h | h
      · exact Subtype.ext h
      · exfalso
        apply hz
        have : s = ⟨zb, hfr.zb_mem⟩ := Subtype.ext h
        rw [← this]
        exact hs
    obtain ⟨E, hc, hs, hcard⟩ := exists_elemAbelian_sb hfr
    refine ⟨E.map ψ, ?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, hs a ha, map_one]
    · rw [Subgroup.card_map_of_injective hinj]
      exact hcard

end Model2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
