module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Nat

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open scoped commutatorElement

section Lift

variable {K : Type*} [Group K]

theorem mem_centralizer_of_central_comm {P : Subgroup K} (hP : ⁅P, P⁆ = P) {k : K}
    (hk : ∀ p ∈ P, k * p * k⁻¹ * p⁻¹ ∈ Subgroup.center K) :
    k ∈ Subgroup.centralizer (P : Set K) := by
  have hperfX : commutator ↥P = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact hP
  let f : ↥P →* ↥(Subgroup.center K) :=
    { toFun := fun p => ⟨k * (p : K) * k⁻¹ * (p : K)⁻¹, hk p p.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro p q
        apply Subtype.ext
        have hq : k * (q : K) * k⁻¹ * (q : K)⁻¹ ∈ Subgroup.center K := hk q q.2
        have hq' := Subgroup.mem_center_iff.mp hq (p : K)
        show k * ((p : K) * q) * k⁻¹ * ((p : K) * q)⁻¹ =
          (k * (p : K) * k⁻¹ * (p : K)⁻¹) * (k * (q : K) * k⁻¹ * (q : K)⁻¹)
        have e1 : (p : K) * (k * (q : K) * k⁻¹ * (q : K)⁻¹) * (p : K)⁻¹ =
            k * (q : K) * k⁻¹ * (q : K)⁻¹ := by
          rw [hq', mul_inv_cancel_right]
        calc k * ((p : K) * q) * k⁻¹ * ((p : K) * q)⁻¹
            = (k * (p : K) * k⁻¹ * (p : K)⁻¹) *
              ((p : K) * (k * (q : K) * k⁻¹ * (q : K)⁻¹) * (p : K)⁻¹) := by group
          _ = _ := by rw [e1] }
  have hker : commutator ↥P ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hp1 : f ⟨p, hp⟩ = 1 := by
    have : (⟨p, hp⟩ : ↥P) ∈ commutator ↥P := by rw [hperfX]; exact Subgroup.mem_top _
    exact hker this
  have h2 := congrArg Subtype.val hp1
  have h3 : k * p * k⁻¹ * p⁻¹ = 1 := h2
  have h4 : k * p = p * k := by
    calc k * p = (k * p * k⁻¹ * p⁻¹) * (p * k) := by group
      _ = p * k := by rw [h3, one_mul]
  exact h4.symm

theorem central_comm_of_quotient_comm {k p : K}
    (h : QuotientGroup.mk' (Subgroup.center K) k * QuotientGroup.mk' (Subgroup.center K) p =
      QuotientGroup.mk' (Subgroup.center K) p * QuotientGroup.mk' (Subgroup.center K) k) :
    k * p * k⁻¹ * p⁻¹ ∈ Subgroup.center K := by
  rw [← QuotientGroup.ker_mk' (Subgroup.center K), MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  rw [h]
  group

theorem commutator_range_eq {Y : Type*} [Group Y] (ρ : Y →* K) (N : Subgroup Y) [N.Normal]
    (hρN : ∀ y, ρ y = 1 ↔ y ∈ N) (hperf : commutator (Y ⧸ N) = ⊤) :
    ⁅ρ.range, ρ.range⁆ = ρ.range := by
  have hmap : ⁅ρ.range, ρ.range⁆ = (commutator Y).map ρ := by
    rw [MonoidHom.range_eq_map, commutator_def, Subgroup.map_commutator]
  apply le_antisymm
  · rw [hmap]
    exact Subgroup.map_le_range _ _
  · rw [hmap]
    rintro _ ⟨y, rfl⟩
    have h1 : (QuotientGroup.mk y : Y ⧸ N) ∈ commutator (Y ⧸ N) := by
      rw [hperf]
      exact Subgroup.mem_top _
    have h2 : (commutator (Y ⧸ N)) = (commutator Y).map (QuotientGroup.mk' N) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective N)]
    rw [h2] at h1
    obtain ⟨c, hc, hcy⟩ := h1
    have h3 : c⁻¹ * y ∈ N := QuotientGroup.eq.mp hcy
    have h4 : ρ c = ρ y := by
      have := (hρN _).mpr h3
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this
    exact ⟨c, hc, h4⟩

end Lift

section Power

theorem coprime_div_gcd_pow (N m : ℕ) (hN : 0 < N) : Nat.Coprime (N / Nat.gcd N (m ^ N)) m := by
  refine Nat.coprime_of_dvd (fun p hp hpb hpm => ?_)
  set g := Nat.gcd N (m ^ N) with hg
  have hgN : g ∣ N := Nat.gcd_dvd_left _ _
  have hNg : N = g * (N / g) := (Nat.mul_div_cancel' hgN).symm
  have hpm' : p ∣ m := hpm
  have hlt : N.factorization p < N := Nat.factorization_lt p hN.ne'
  have h1 : p ^ N.factorization p ∣ N := Nat.ordProj_dvd N p
  have h2 : p ^ N.factorization p ∣ m ^ N :=
    (pow_dvd_pow p hlt.le).trans (pow_dvd_pow_of_dvd hpm' N)
  have h3 : p ^ N.factorization p ∣ g := Nat.dvd_gcd h1 h2
  have h4 : g * p ∣ N := by
    rw [hNg]
    conv_rhs => rw [← hNg]
    exact mul_dvd_mul_left g hpb |>.trans (by rw [← hNg])
  have h5 : p ^ (N.factorization p + 1) ∣ N := by
    rw [pow_succ]
    exact (mul_dvd_mul_right h3 p).trans h4
  exact Nat.pow_succ_factorization_not_dvd hN.ne' hp h5

variable {K : Type*} [Group K]

theorem exists_pow_orderOf_coprime [Finite K] (x : K) (m : ℕ) :
    ∃ t : ℕ, Nat.Coprime (orderOf (x ^ t)) m ∧ ∀ r : ℕ, Nat.Coprime m r → Nat.Coprime t r := by
  have hN : 0 < orderOf x := orderOf_pos x
  have hdvd : Nat.gcd (orderOf x) (m ^ orderOf x) ∣ orderOf x := Nat.gcd_dvd_left _ _
  have hpos : Nat.gcd (orderOf x) (m ^ orderOf x) ≠ 0 := by
    have := Nat.gcd_pos_of_pos_left (m ^ orderOf x) hN
    omega
  refine ⟨Nat.gcd (orderOf x) (m ^ orderOf x), ?_, fun r hr => ?_⟩
  · rw [orderOf_pow_of_dvd hpos hdvd]
    exact coprime_div_gcd_pow _ _ hN
  · exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) (Nat.Coprime.pow_left _ hr)

end Power

section FrameK

theorem map_map_conj_eq {Q Γ : Type*} [Group Q] [Group Γ] (κ : Q →* Γ) (S : Subgroup Q) (q : Q) :
    (S.map (MulAut.conj q).toMonoidHom).map κ = (S.map κ).map (MulAut.conj (κ q)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

variable {K V : Type*} [Group K] [Finite K] [Group V] [Finite V]

theorem frame_false_K (hc : ∀ a b : V, a * b = b * a) {θ : K →* MulAut V}
    (hθ : Function.Injective θ) {m r : ℕ} (hmr : Nat.Coprime m r) (hr : Odd r)
    {Y₀ : Subgroup K} (hY₀ : NatQ θ Y₀ m) (hperf : ⁅Y₀, Y₀⁆ = Y₀)
    (hinj : ∀ y ∈ Y₀, QuotientGroup.mk' (Subgroup.center K) y = 1 → y = 1)
    {k₁ k₃ d y y₃ : K ⧸ Subgroup.center K}
    (hy : y ∈ (Y₀.map (QuotientGroup.mk' (Subgroup.center K))).map (MulAut.conj k₁).toMonoidHom)
    (hy₃ : y₃ ∈ (Y₀.map (QuotientGroup.mk' (Subgroup.center K))).map (MulAut.conj k₃).toMonoidHom)
    (hy1 : y ≠ 1) (hy₃1 : y₃ ≠ 1) (hyr : y ^ r = 1) (hy₃r : y₃ ^ r = 1)
    (hdc₃ : ∀ x ∈ (Y₀.map (QuotientGroup.mk' (Subgroup.center K))).map
      (MulAut.conj k₃).toMonoidHom, d * x = x * d)
    (hdc₁ : ∀ x ∈ (Y₀.map (QuotientGroup.mk' (Subgroup.center K))).map
      (MulAut.conj k₁).toMonoidHom, d * y⁻¹ * x = x * (d * y⁻¹))
    (hyc₃ : ∀ x ∈ (Y₀.map (QuotientGroup.mk' (Subgroup.center K))).map
      (MulAut.conj k₃).toMonoidHom, y * y₃⁻¹ * x = x * (y * y₃⁻¹)) : False := by
  classical
  obtain ⟨κ₁, hκ₁⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) k₁
  obtain ⟨κ₃, hκ₃⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) k₃
  subst hκ₁ hκ₃
  set π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K) with hπ
  set Y₁ : Subgroup K := Y₀.map (MulAut.conj κ₁).toMonoidHom with hY₁
  set Y₃ : Subgroup K := Y₀.map (MulAut.conj κ₃).toMonoidHom with hY₃
  have hY₁π : Y₁.map π = (Y₀.map π).map (MulAut.conj (π κ₁)).toMonoidHom :=
    map_map_conj_eq π Y₀ κ₁
  have hY₃π : Y₃.map π = (Y₀.map π).map (MulAut.conj (π κ₃)).toMonoidHom :=
    map_map_conj_eq π Y₀ κ₃
  have hperf₁ : ⁅Y₁, Y₁⁆ = Y₁ := by
    rw [hY₁, ← Subgroup.map_commutator, hperf]
  have hperf₃ : ⁅Y₃, Y₃⁆ = Y₃ := by
    rw [hY₃, ← Subgroup.map_commutator, hperf]
  have hinjc : ∀ (κ x : K), x ∈ Y₀ → π ((MulAut.conj κ).toMonoidHom x) = 1 → (MulAut.conj κ).toMonoidHom x = 1 := by
    intro κ x hx h1
    have h2 : π x = 1 := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, map_mul,
        map_inv, mul_inv_eq_one, mul_eq_left] at h1
      exact h1
    rw [hinj x hx h2, map_one]
  have hinj₁ : ∀ x ∈ Y₁, π x = 1 → x = 1 := by
    rintro _ ⟨x₀, hx₀, rfl⟩ h1
    exact hinjc κ₁ x₀ hx₀ h1
  have hinj₃ : ∀ x ∈ Y₃, π x = 1 → x = 1 := by
    rintro _ ⟨x₀, hx₀, rfl⟩ h1
    exact hinjc κ₃ x₀ hx₀ h1
  obtain ⟨y', hy'Y, hy'⟩ : ∃ y' ∈ Y₁, π y' = y := by
    rw [← hY₁π] at hy
    exact Subgroup.mem_map.mp hy
  obtain ⟨y₃', hy₃'Y, hy₃'⟩ : ∃ y₃' ∈ Y₃, π y₃' = y₃ := by
    rw [← hY₃π] at hy₃
    exact Subgroup.mem_map.mp hy₃
  obtain ⟨d', hd'⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) d
  have hmem₁ : ∀ p ∈ Y₁, π p ∈ (Y₀.map π).map (MulAut.conj (π κ₁)).toMonoidHom := fun p hp => by
    rw [← hY₁π]
    exact Subgroup.mem_map_of_mem _ hp
  have hmem₃ : ∀ p ∈ Y₃, π p ∈ (Y₀.map π).map (MulAut.conj (π κ₃)).toMonoidHom := fun p hp => by
    rw [← hY₃π]
    exact Subgroup.mem_map_of_mem _ hp
  have hd'C : d' ∈ Subgroup.centralizer (Y₃ : Set K) := by
    refine mem_centralizer_of_central_comm hperf₃ (fun p hp => central_comm_of_quotient_comm ?_)
    have := hdc₃ (π p) (hmem₃ p hp)
    rw [← hd'] at this
    exact this
  have hdyC : d' * y'⁻¹ ∈ Subgroup.centralizer (Y₁ : Set K) := by
    refine mem_centralizer_of_central_comm hperf₁ (fun p hp => central_comm_of_quotient_comm ?_)
    have := hdc₁ (π p) (hmem₁ p hp)
    rw [← hd', ← hy'] at this
    simpa only [map_mul, map_inv] using this
  have hyyC : y' * y₃'⁻¹ ∈ Subgroup.centralizer (Y₃ : Set K) := by
    refine mem_centralizer_of_central_comm hperf₃ (fun p hp => central_comm_of_quotient_comm ?_)
    have := hyc₃ (π p) (hmem₃ p hp)
    rw [← hy', ← hy₃'] at this
    simpa only [map_mul, map_inv] using this
  have hy'r : y' ^ r = 1 := by
    apply hinj₁ _ (Subgroup.pow_mem _ hy'Y r)
    rw [map_pow, hy', hyr]
  have hy₃'r : y₃' ^ r = 1 := by
    apply hinj₃ _ (Subgroup.pow_mem _ hy₃'Y r)
    rw [map_pow, hy₃', hy₃r]
  have hy'1 : y' ≠ 1 := fun hh => hy1 (by rw [← hy', hh, map_one])
  have hy₃'1 : y₃' ≠ 1 := fun hh => hy₃1 (by rw [← hy₃', hh, map_one])
  have hcomm₁ : Commute d' y' := by
    have hc1 := Subgroup.mem_centralizer_iff.mp hdyC y' hy'Y
    show d' * y' = y' * d'
    calc d' * y' = ((d' * y'⁻¹) * y') * y' := by group
      _ = (y' * (d' * y'⁻¹)) * y' := by rw [← hc1]
      _ = y' * d' := by group
  have hcomm₃ : Commute y' y₃' := by
    have hc1 := Subgroup.mem_centralizer_iff.mp hyyC y₃' hy₃'Y
    show y' * y₃' = y₃' * y'
    calc y' * y₃' = ((y' * y₃'⁻¹) * y₃') * y₃' := by group
      _ = (y₃' * (y' * y₃'⁻¹)) * y₃' := by rw [← hc1]
      _ = y₃' * y' := by group
  obtain ⟨t, htd, htr⟩ := exists_pow_orderOf_coprime d' m
  have htr' : Nat.Coprime t r := htr r hmr
  have hord : ∀ z : K, z ^ r = 1 → z ≠ 1 → z ^ t ≠ 1 := by
    intro z hz hz1 hzt
    have h1 : orderOf z ∣ t := orderOf_dvd_of_pow_eq_one hzt
    have h2 : orderOf z ∣ r := orderOf_dvd_of_pow_eq_one hz
    have h3 : Nat.Coprime (orderOf z) r := Nat.Coprime.coprime_dvd_left h1 htr'
    exact hz1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h3 h2))
  have hpowdvd : ∀ z : K, z ^ r = 1 → orderOf (z ^ t) ∣ r := by
    intro z hz
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  refine frame_false hc hθ (hY₀.conj κ₁) (hY₀.conj κ₃) (d := d' ^ t) (y := y' ^ t)
    (y₃ := y₃' ^ t) (Subgroup.pow_mem _ hd'C t) htd (Subgroup.pow_mem _ hy'Y t)
    (hord y' hy'r hy'1) (Odd.of_dvd_nat hr (hpowdvd y' hy'r))
    (Nat.Coprime.coprime_dvd_left (hpowdvd y' hy'r) hmr.symm) ?_
    (Subgroup.pow_mem _ hy₃'Y t) (hord y₃' hy₃'r hy₃'1) (Odd.of_dvd_nat hr (hpowdvd y₃' hy₃'r))
    (Nat.Coprime.coprime_dvd_left (hpowdvd y₃' hy₃'r) hmr.symm) ?_
  · have := Subgroup.pow_mem _ hdyC t
    rwa [(hcomm₁.inv_right).mul_pow, inv_pow] at this
  · have := Subgroup.pow_mem _ hyyC t
    rwa [(hcomm₃.inv_right).mul_pow, inv_pow] at this

end FrameK

end CFSG.CGT.PushingUpLit.CGT6
