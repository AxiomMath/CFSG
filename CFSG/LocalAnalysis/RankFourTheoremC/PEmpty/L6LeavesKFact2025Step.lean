module

public import CFSG.RankThree.PartOne.S11c.DegreeSixPrimesCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.DegreeSixInduction

universe u v

theorem sq_mem_frattini_two' {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) (x : P) :
    x ^ 2 ∈ frattini P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hP.isNilpotent
  unfold frattini Order.radical
  rw [Subgroup.mem_iInf]
  intro M
  rw [Subgroup.mem_iInf]
  intro hM
  exact Subgroup.sq_mem_of_index_two ((IsPGroup.isCoatom_iff_index_eq_prime hP).mp hM) x


structure Min32 {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    (R : Subgroup (Module.End k V)ˣ) (u : (Module.End k V)ˣ) : Prop where
  card_eq : Nat.card R = 32
  isExtra : IsExtraspecialPGroup 2 R
  norm : u ∈ Subgroup.normalizer (R : Set (Module.End k V)ˣ)
  moved : ∃ r ∈ R, u * r ≠ r * u
  minimal : ∀ S : Subgroup (Module.End k V)ˣ, S ≤ R → S ≠ R →
    u ∈ Subgroup.normalizer (S : Set (Module.End k V)ˣ) → ∀ s ∈ S, u * s = s * u
  center : ∃ z : R, Subgroup.center R = Subgroup.zpowers z ∧
    ((z : (Module.End k V)ˣ) : Module.End k V) = -1
  fpf : ∀ r ∈ R, u * r * u⁻¹ * r⁻¹ ∈ (Subgroup.center R).map R.subtype →
    r ∈ (Subgroup.center R).map R.subtype

theorem step_of_lt {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V ≤ 4)
    (ih : ∀ W : Submodule k V, Module.finrank k W < Module.finrank k V → CommuteStmt k p W)
    (Q : Subgroup (Module.End k V)ˣ) [Finite Q] (hQ : IsPGroup 2 Q)
    (u : (Module.End k V)ˣ) (hu : u ∈ Subgroup.normalizer (Q : Set (Module.End k V)ˣ))
    {m : ℕ} (hum : u ^ p ^ m = 1) :
    (∀ q ∈ Q, u * q = q * u) ∨
      ∃ R : Subgroup (Module.End k V)ˣ, R ≤ Q ∧ Min32 R u ∧ p = 5 ∧ Module.finrank k V = 4 := by
  classical
  by_cases hcomm : ∀ q ∈ Q, u * q = q * u
  · exact Or.inl hcomm
  right
  push Not at hcomm
  obtain ⟨q₀, hq₀, hq₀ne⟩ := hcomm
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Subgroup (Module.End k V)ˣ := Subgroup.zpowers u
  have hAfin : Finite A :=
    finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ m, pow_pos hp.pos m, hum⟩)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hum)
  have hAcard : Nat.card A = p ^ j := by rw [Nat.card_zpowers]; exact hj
  have hAp : IsPGroup p A := IsPGroup.of_card hAcard
  have hA2 : ¬ 2 ∣ Nat.card A := by
    rw [hAcard]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h)
    omega
  have hAQ : A ≤ Subgroup.normalizer (Q : Set (Module.End k V)ˣ) := Subgroup.zpowers_le.mpr hu
  let Good : Subgroup (Module.End k V)ˣ → Prop := fun R =>
    R ≤ Q ∧ (∀ a ∈ A, ∀ r ∈ R, a * r * a⁻¹ ∈ R) ∧ ∃ a ∈ A, ∃ r ∈ R, a * r * a⁻¹ ≠ r
  have hgood : Good Q := by
    refine ⟨le_rfl, fun a ha r hr => ?_, u, Subgroup.mem_zpowers u, q₀, hq₀, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hAQ ha) r).mp hr
    · intro h
      apply hq₀ne
      calc u * q₀ = u * q₀ * u⁻¹ * u := by group
        _ = q₀ * u := by rw [h]
  have hex : ∃ n : ℕ, ∃ R : Subgroup (Module.End k V)ˣ, Good R ∧ Nat.card R = n :=
    ⟨_, Q, hgood, rfl⟩
  obtain ⟨R, ⟨hRQ, hRinv, a₀, ha₀, r₀, hr₀, hmove₀⟩, hRn⟩ := Nat.find_spec hex
  have hRmin : ∀ S : Subgroup (Module.End k V)ˣ, Good S → Nat.card R ≤ Nat.card S :=
    fun S hS => hRn ▸ Nat.find_min' hex ⟨S, hS, rfl⟩
  have hAR : A ≤ Subgroup.normalizer (R : Set (Module.End k V)ˣ) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun hr => hRinv a ha r hr, fun h => ?_⟩
    have := hRinv a⁻¹ (A.inv_mem ha) _ h
    simpa [mul_assoc] using this
  have : Finite R :=
    Finite.of_injective (Subgroup.inclusion hRQ) (Subgroup.inclusion_injective hRQ)
  have hR2 : IsPGroup 2 R := hQ.to_le hRQ
  have : Fact (A ≤ Subgroup.normalizer (R : Set (Module.End k V)ˣ)) := ⟨hAR⟩
  have hnt : ∃ (a : A) (q : R), a • q ≠ q := by
    refine ⟨⟨a₀, ha₀⟩, ⟨r₀, hr₀⟩, fun h => hmove₀ ?_⟩
    have := congrArg Subtype.val h
    simpa using this
  have hmin : ∀ S : Subgroup R, S ≠ ⊤ → (∀ (a : A), ∀ s ∈ S, a • s ∈ S) →
      ∀ (a : A), ∀ s ∈ S, a • s = s := by
    intro S hS hSinv
    by_contra hcon
    push Not at hcon
    obtain ⟨a, s, hs, hes⟩ := hcon
    have hgoodS : Good (S.map R.subtype) := by
      refine ⟨(Subgroup.map_subtype_le S).trans hRQ, ?_, a, a.2, s,
        Subgroup.mem_map_of_mem _ hs, ?_⟩
      · rintro b hb _ ⟨t, ht, rfl⟩
        refine ⟨(⟨b, hb⟩ : A) • t, hSinv ⟨b, hb⟩ t ht, ?_⟩
        simp
      · intro h
        apply hes
        apply Subtype.ext
        simpa using h
    have hle := hRmin _ hgoodS
    rw [Subgroup.card_map_of_injective R.subtype_injective] at hle
    exact hS ((Subgroup.card_eq_iff_eq_top S).mp (le_antisymm (Subgroup.card_le_card_group S) hle))
  obtain ⟨htop, hΦ, ⟨hVnt, hVel, hVmove, hVirr⟩, hab, hnab⟩ :=
    SteinbergBY.minimal_coprime_action_elementary_or_special (A := A) (P := R) (l := 2) hR2 hA2
      hnt hmin
  by_cases hRab : IsMulCommutative R
  ·
    exfalso
    obtain ⟨-, hel⟩ := hab hRab
    have : IsElementaryAbelian 2 R := hel
    have hc := commute_of_isElementaryAbelian_of_normalizes h2 hp hAp (by omega) hAR a₀ ha₀ r₀
      hr₀
    apply hmove₀
    rw [hc, mul_inv_cancel_right]
  · obtain ⟨hcf, hfc, hcne, hcel, hcen⟩ := hnab hRab
    have : IsElementaryAbelian 2 (commutator R) := hcel
    have hsqR : ∀ z : R, z ∈ Subgroup.center R → z * z = 1 := by
      intro z hz
      have hzc : z ∈ commutator R := by rw [hcf, hfc]; exact hz
      have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (commutator R)) ⟨z, hzc⟩
      have h' : z ^ 2 = 1 := congrArg Subtype.val h
      rwa [pow_two] at h'
    have hsq : ∀ z : R, z ∈ Subgroup.center R →
        ((z : (Module.End k V)ˣ) : Module.End k V) * ((z : (Module.End k V)ˣ) : Module.End k V) =
          1 := by
      intro z hz
      rw [← Units.val_mul, ← Subgroup.coe_mul, hsqR z hz]
      simp
    have hcomm : ∀ z : R, z ∈ Subgroup.center R → ∀ r ∈ R,
        r * (z : (Module.End k V)ˣ) = (z : (Module.End k V)ˣ) * r := by
      intro z hz r hr
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨r, hr⟩)
    have hAfix : ∀ z : R, z ∈ Subgroup.center R → ∀ a ∈ A,
        a * (z : (Module.End k V)ˣ) * a⁻¹ = z := by
      intro z hz a ha
      have := congrArg Subtype.val (hcen ⟨a, ha⟩ z hz)
      simpa using this
    have h1ne : (1 : k) ≠ -1 := fun h => h2 (by linear_combination h)
    by_cases hA : ∃ z : R, z ∈ Subgroup.center R ∧
        Module.End.eigenspace ((z : (Module.End k V)ˣ) : Module.End k V) 1 ≠ ⊥ ∧
        Module.End.eigenspace ((z : (Module.End k V)ˣ) : Module.End k V) (-1) ≠ ⊥
    ·
      exfalso
      obtain ⟨z, hzc, hE1, hE2⟩ := hA
      let C : Subgroup (Module.End k V)ˣ := Subgroup.centralizer {(z : (Module.End k V)ˣ)}
      have hCinv : ∀ ε : k, ∀ g ∈ C, ∀ w ∈ Module.End.eigenspace
          ((z : (Module.End k V)ˣ) : Module.End k V) ε,
          ((g : (Module.End k V)ˣ) : Module.End k V) w ∈ Module.End.eigenspace
            ((z : (Module.End k V)ˣ) : Module.End k V) ε := by
        intro ε g hg w hw
        have hgz := Subgroup.mem_centralizer_singleton_iff.mp hg
        rw [Module.End.mem_eigenspace_iff] at hw ⊢
        rw [← Module.End.mul_apply, ← Units.val_mul, ← hgz, Units.val_mul, Module.End.mul_apply, hw,
          map_smul]
      have hRC : R ≤ C := fun r hr =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzc r hr)
      have huC : u ∈ C := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := hAfix z hzc u (Subgroup.mem_zpowers u)
        calc u * z = u * z * u⁻¹ * u := by group
          _ = z * u := by rw [this]
      have hu_norm : u ∈ Subgroup.normalizer (R : Set (Module.End k V)ˣ) :=
        hAR (Subgroup.mem_zpowers u)
      have hne1 := eigenspace_ne_top_of_ne (z := ((z : (Module.End k V)ˣ) : Module.End k V))
        h1ne hE2
      have hne2 := eigenspace_ne_top_of_ne (z := ((z : (Module.End k V)ˣ) : Module.End k V))
        h1ne.symm hE1
      have hc₁ := commute_on_invariant_subspace (hCinv 1) (ih _ (Submodule.finrank_lt hne1)) hR2
        hRC huC hu_norm hum
      have hc₂ := commute_on_invariant_subspace (hCinv (-1)) (ih _ (Submodule.finrank_lt hne2))
        hR2 hRC huC hu_norm hum
      have hcu : ∀ r ∈ R, u * r = r * u := by
        intro r hr
        apply Units.ext
        rw [Units.val_mul, Units.val_mul]
        exact eq_of_eq_on_eigenspaces h2 (hsq z hzc) (fun w hw => hc₁ r hr w hw)
          (fun w hw => hc₂ r hr w hw)
      apply hmove₀
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₀
      have := (Commute.zpow_left (show Commute u r₀ from hcu r₀ hr₀) i).eq
      rw [this, mul_inv_cancel_right]
    ·
      have hB : ∀ z : R, z ∈ Subgroup.center R →
          Module.End.eigenspace ((z : (Module.End k V)ˣ) : Module.End k V) 1 = ⊥ ∨
          Module.End.eigenspace ((z : (Module.End k V)ˣ) : Module.End k V) (-1) = ⊥ := by
        intro z hz
        by_contra hcon
        push Not at hcon
        exact hA ⟨z, hz, hcon.1, hcon.2⟩
      have hdich : ∀ z : R, z ∈ Subgroup.center R →
          ((z : (Module.End k V)ˣ) : Module.End k V) = 1 ∨
            ((z : (Module.End k V)ˣ) : Module.End k V) = -1 := fun z hz =>
        eq_one_or_eq_neg_one_of_eigenspace_eq_bot (hsq z hz) (hB z hz)
      have hcenter_ne : Subgroup.center R ≠ ⊥ := by
        rw [← hfc, ← hcf]
        exact hcne
      obtain ⟨⟨z₀, hz₀c⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter_ne
      have hz₀ne : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
      have : Nontrivial V := by
        by_contra hnt'
        rw [not_nontrivial_iff_subsingleton] at hnt'
        apply hz₀ne
        apply Subtype.ext
        apply Units.ext
        apply LinearMap.ext
        intro v
        exact Subsingleton.elim _ _
      have hz₀neg : ((z₀ : (Module.End k V)ˣ) : Module.End k V) = -1 := by
        rcases hdich z₀ hz₀c with h | h
        · exfalso
          apply hz₀ne
          apply Subtype.ext
          apply Units.ext
          simpa using h
        · exact h
      have hz : Subgroup.center R = Subgroup.zpowers z₀ := by
        apply le_antisymm
        · intro z hz
          rcases hdich z hz with h | h
          · have : z = 1 := by
              apply Subtype.ext
              apply Units.ext
              simpa using h
            rw [this]
            exact one_mem _
          · have : z = z₀ := by
              apply Subtype.ext
              apply Units.ext
              rw [h, hz₀neg]
            rw [this]
            exact Subgroup.mem_zpowers z₀
        · rw [Subgroup.zpowers_le]
          exact hz₀c
      have hcard2 : Nat.card (Subgroup.center R) = 2 := by
        rw [hz, Nat.card_zpowers]
        refine orderOf_eq_prime ?_ hz₀ne
        rw [pow_two]
        exact hsqR z₀ hz₀c
      have hext : IsExtraspecialPGroup 2 R := ⟨hR2, hcf.trans hfc, hfc, hcard2⟩
      obtain ⟨n, hn1, hn2, hcardR⟩ := extraspecial_card_le h2 hext hz hz₀neg (by omega)
      have hΦcard : Nat.card (frattini R) = 2 := by
        rw [hfc]
        exact hcard2
      have hquot : Nat.card (R ⧸ frattini R) = 2 ^ (2 * n) := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini R)
        rw [hcardR, hΦcard, pow_add, pow_one] at h
        omega
      have hdimpow : 2 ^ n ≤ Module.finrank k V := by
        let ρ : Representation k R V := (Units.coeHom (Module.End k V)).comp R.subtype
        have h := SteinbergBM.pow_le_finrank_of_invariant hext hcardR hz h2 ρ ⊤ top_ne_bot
          (fun _ _ _ => Submodule.mem_top) (fun w _ => by
            change ((z₀ : (Module.End k V)ˣ) : Module.End k V) w = -w
            rw [hz₀neg]
            rfl)
        rwa [finrank_top] at h
      let _ := SteinbergBY.frattiniQuotientAction A R
      have hmod := card_modEq_one_of_irreducible (A := A) (X := R ⧸ frattini R) (p := p) hAp
        hVirr hVmove
      rw [hquot] at hmod
      have hdvd : p ∣ 2 ^ (2 * n) - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm
      have hn2' : n = 2 := by
        interval_cases n
        · exfalso
          have h3 : p ∣ 3 := by simpa using hdvd
          have := Nat.le_of_dvd (by norm_num) h3
          omega
        · rfl
      subst hn2'
      have hp5' : p = 5 := by
        have h15 : p ∣ 3 * 5 := by simpa using hdvd
        rcases (Nat.Prime.dvd_mul hp).mp h15 with h3 | h5
        · exfalso
          have := Nat.le_of_dvd (by norm_num) h3
          omega
        · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5
      have hdim4 : Module.finrank k V = 4 := by
        have : 2 ^ 2 ≤ Module.finrank k V := hdimpow
        omega
      have hfixX : letI := SteinbergBY.frattiniQuotientAction A R
          ∀ x : R ⧸ frattini R, (∀ a : A, a • x = x) → x = 1 := by
        letI := SteinbergBY.frattiniQuotientAction A R
        have hS : FixedPoints.subgroup A (R ⧸ frattini R) = ⊥ := by
          rcases hVirr (FixedPoints.subgroup A (R ⧸ frattini R)) (fun a s hs => by
            rw [(FixedPoints.mem_subgroup A (R ⧸ frattini R) s).mp hs a]; exact hs) with h | h
          · exact h
          · exfalso
            obtain ⟨a, v, hv⟩ := hVmove
            apply hv
            have : v ∈ FixedPoints.subgroup A (R ⧸ frattini R) := by
              rw [h]; exact Subgroup.mem_top v
            exact (FixedPoints.mem_subgroup A (R ⧸ frattini R) v).mp this a
        intro x hx
        have : x ∈ FixedPoints.subgroup A (R ⧸ frattini R) :=
          (FixedPoints.mem_subgroup A (R ⧸ frattini R) x).mpr hx
        rw [hS, Subgroup.mem_bot] at this
        exact this
      refine ⟨R, hRQ, ⟨?_, hext, hAR (Subgroup.mem_zpowers u), ?_, ?_, ⟨z₀, hz, hz₀neg⟩, ?_⟩,
        hp5', hdim4⟩
      · rw [hcardR]; norm_num
      · refine ⟨r₀, hr₀, fun h => hmove₀ ?_⟩
        have hc : Commute u r₀ := h
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₀
        have := (Commute.zpow_left hc i).eq
        rw [this, mul_inv_cancel_right]
      · intro S hSR hSne hSnorm s hs
        by_contra hns
        have hgS : Good S := by
          refine ⟨hSR.trans hRQ, fun a ha r hr => ?_, u, Subgroup.mem_zpowers u, s, hs, ?_⟩
          · exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.zpowers_le.mpr hSnorm) ha) r).mp hr
          · intro h
            apply hns
            calc u * s = u * s * u⁻¹ * u := by group
              _ = s * u := by rw [h]
        have hle := hRmin S hgS
        exact hSne (Subgroup.eq_of_le_of_card_ge hSR hle)
      · intro r hr hrc
        letI := SteinbergBY.frattiniQuotientAction A R
        obtain ⟨c, hcc, hcr⟩ := hrc
        have hΦ' : ∀ c : R, c ∈ Subgroup.center R → c ∈ frattini R := fun c hc => by
          rw [hfc]; exact hc
        have hx : ((⟨u * r * u⁻¹, (Subgroup.mem_normalizer_iff.mp
            (hAR (Subgroup.mem_zpowers u)) r).mp hr⟩ : R) : R ⧸ frattini R) =
            ((⟨r, hr⟩ : R) : R ⧸ frattini R) := by
          rw [QuotientGroup.eq]
          have hfn : frattini R ≤ frattini R := le_rfl
          have hnorm : (frattini R).Normal := inferInstance
          have hcF : c ∈ frattini R := hΦ' c hcc
          have hceq : (⟨u * r * u⁻¹, (Subgroup.mem_normalizer_iff.mp
              (hAR (Subgroup.mem_zpowers u)) r).mp hr⟩ : R) = c * ⟨r, hr⟩ := by
            apply Subtype.ext
            change u * r * u⁻¹ = (c : (Module.End k V)ˣ) * r
            have h1 : (c : (Module.End k V)ˣ) = u * r * u⁻¹ * r⁻¹ := hcr
            rw [h1]
            group
          have hcc' : (c * (⟨r, hr⟩ : R))⁻¹ * ⟨r, hr⟩ =
              (⟨r, hr⟩ : R)⁻¹ * c⁻¹ * ((⟨r, hr⟩ : R)⁻¹)⁻¹ := by group
          rw [hceq, hcc']
          exact hnorm.conj_mem _ (inv_mem hcF) _
        have hfixu : ∀ a : A, a • ((⟨r, hr⟩ : R) : R ⧸ frattini R) =
            ((⟨r, hr⟩ : R) : R ⧸ frattini R) := by
          intro a
          have hu0 : (⟨u, Subgroup.mem_zpowers u⟩ : A) •
              ((⟨r, hr⟩ : R) : R ⧸ frattini R) = ((⟨r, hr⟩ : R) : R ⧸ frattini R) := hx
          have hstab : (⟨u, Subgroup.mem_zpowers u⟩ : A) ∈
              MulAction.stabilizer A ((⟨r, hr⟩ : R) : R ⧸ frattini R) := hu0
          obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
          have ha : a = (⟨u, Subgroup.mem_zpowers u⟩ : A) ^ i := Subtype.ext (by simp [hi])
          rw [ha]
          exact (Subgroup.zpow_mem _ hstab i)
        have h1 := hfixX _ hfixu
        have hmem : (⟨r, hr⟩ : R) ∈ frattini R := (QuotientGroup.eq_one_iff _).mp h1
        rw [hfc] at hmem
        exact ⟨⟨r, hr⟩, hmem, rfl⟩


theorem commuteStmt_of_finrank_le_three {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ (n : ℕ) (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V],
      Module.finrank k V = n → n ≤ 3 → CommuteStmt k p V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ hn hn3 Q hQfin hQ u hu m hum
    rcases step_of_lt h2 hp hp5 (by omega)
      (fun W hW => ih (Module.finrank k W) (hn ▸ hW) W rfl (by omega)) Q hQ u hu hum with
      h | ⟨R, -, -, -, hdim⟩
    · exact h
    · omega

theorem exists_min32_of_finrank_le_four {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (hV : Module.finrank k V ≤ 4) (Q : Subgroup (Module.End k V)ˣ)
    [Finite Q] (hQ : IsPGroup 2 Q) (u : (Module.End k V)ˣ)
    (hu : u ∈ Subgroup.normalizer (Q : Set (Module.End k V)ˣ)) {m : ℕ} (hum : u ^ p ^ m = 1) :
    (∀ q ∈ Q, u * q = q * u) ∨
      ∃ R : Subgroup (Module.End k V)ˣ, R ≤ Q ∧ Min32 R u ∧ p = 5 ∧ Module.finrank k V = 4 :=
  step_of_lt h2 hp hp5 hV
    (fun W hW => commuteStmt_of_finrank_le_three h2 hp hp5 (Module.finrank k W) W rfl
      (by omega)) Q hQ u hu hum

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025
