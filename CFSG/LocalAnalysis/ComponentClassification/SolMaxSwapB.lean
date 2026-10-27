module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33C

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapP2

theorem exists_fixed_in_coset [Finite X] {U V : Subgroup X} (hU : IsPGroup 2 ↥U)
    (hV : Odd (Nat.card ↥V)) (hUV : U ≤ normalizer (V : Set X)) {x : X}
    (hxV : x ∈ normalizer (V : Set X)) (hx : ∀ u ∈ U, u * x * u⁻¹ * x⁻¹ ∈ V) :
    ∃ v ∈ V, ∀ u ∈ U, u * (x * v) * u⁻¹ = x * v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Type := {y : X // x⁻¹ * y ∈ V}
  have hclosed : ∀ (u : ↥U) (y : T), x⁻¹ * ((u : X) * (y : X) * (u : X)⁻¹) ∈ V := by
    intro u y
    have hv : (u : X) * (x⁻¹ * (y : X)) * (u : X)⁻¹ ∈ V :=
      (mem_normalizer_iff.1 (hUV u.2) _).1 y.2
    have hxw : x⁻¹ * ((u : X) * x * (u : X)⁻¹ * x⁻¹) * x ∈ V := by
      have h1 := (mem_normalizer_iff.1 (inv_mem hxV) _).1 (hx u u.2)
      rwa [inv_inv] at h1
    have h2 : x⁻¹ * ((u : X) * (y : X) * (u : X)⁻¹) =
        (x⁻¹ * ((u : X) * x * (u : X)⁻¹ * x⁻¹) * x) * ((u : X) * (x⁻¹ * (y : X)) * (u : X)⁻¹) := by
      group
    rw [h2]
    exact mul_mem hxw hv
  let inst : MulAction ↥U T :=
    { smul := fun u y => ⟨(u : X) * (y : X) * (u : X)⁻¹, hclosed u y⟩
      one_smul := fun y => Subtype.ext (by
        change ((1 : ↥U) : X) * (y : X) * ((1 : ↥U) : X)⁻¹ = (y : X)
        simp)
      mul_smul := fun u₁ u₂ y => Subtype.ext (by
        change ((u₁ * u₂ : ↥U) : X) * (y : X) * ((u₁ * u₂ : ↥U) : X)⁻¹ =
          (u₁ : X) * ((u₂ : X) * (y : X) * (u₂ : X)⁻¹) * (u₁ : X)⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card T = Nat.card ↥V := by
    refine Nat.card_congr ⟨fun y => ⟨x⁻¹ * (y : X), y.2⟩, fun v => ⟨x * (v : X), by simp⟩,
      fun y => by apply Subtype.ext; simp, fun v => by apply Subtype.ext; simp⟩
  have hVp : ¬ 2 ∣ Nat.card T := by
    rw [hcard]
    exact fun h => (Nat.not_even_iff_odd.mpr hV) (even_iff_two_dvd.mpr h)
  obtain ⟨y, hy⟩ := hU.nonempty_fixed_point_of_prime_not_dvd_card T hVp
  refine ⟨x⁻¹ * (y : X), y.2, fun u hu => ?_⟩
  have h1 : (u : X) * (y : X) * (u : X)⁻¹ = (y : X) := congrArg Subtype.val (hy ⟨u, hu⟩)
  rw [show x * (x⁻¹ * (y : X)) = (y : X) by group]
  exact h1

theorem exists_involution_decomp [Finite X] {M M' U : Subgroup X}
    (hMM' : M ≤ normalizer (M' : Set X))
    (hV : Odd (Nat.card ↥(M ⊓ M'))) (hU : IsPGroup 2 ↥U) (hUM : U ≤ normalizer (M : Set X))
    (hUM' : U ≤ normalizer (M' : Set X)) {f : X} (hf : f ∈ M ⊔ M') (hf2 : f * f = 1)
    (hfU : f ∈ U) (hUf : U ≤ centralizer ({f} : Set X)) :
    ∃ a ∈ M, ∃ b ∈ M', f = a * b ∧ a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧
      U ≤ centralizer ({a} : Set X) ∧ U ≤ centralizer ({b} : Set X) := by
  classical
  set V := M ⊓ M' with hVdef
  have hf' : f ∈ ((M ⊔ M' : Subgroup X) : Set X) := hf
  rw [coe_mul_of_left_le_normalizer_right M M' hMM'] at hf'
  obtain ⟨m, hm, m', hm', hfmm⟩ := hf'
  replace hm : m ∈ M := hm
  replace hm' : m' ∈ M' := hm'
  have hfmm' : f = m * m' := hfmm.symm
  have hUV : U ≤ normalizer (V : Set X) := fun u hu =>
    inf_normalizer_le_normalizer_inf ⟨hUM hu, hUM' hu⟩
  have hmV : m ∈ normalizer (V : Set X) :=
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hm, hMM' hm⟩
  have hx : ∀ u ∈ U, u * m * u⁻¹ * m⁻¹ ∈ V := by
    intro u hu
    have h1 : u * m * u⁻¹ ∈ M := (mem_normalizer_iff.mp (hUM hu) m).mp hm
    have h2 : u * m' * u⁻¹ ∈ M' := (mem_normalizer_iff.mp (hUM' hu) m').mp hm'
    have hfu : u * f * u⁻¹ = f := by
      rw [mem_centralizer_singleton_iff.mp (hUf hu), mul_inv_cancel_right]
    have h3 : m⁻¹ * (u * m * u⁻¹) = m' * (u * m' * u⁻¹)⁻¹ := by
      have h4 : (u * m * u⁻¹) * (u * m' * u⁻¹) = m * m' := by
        rw [← hfmm', ← hfu, hfmm']
        group
      calc m⁻¹ * (u * m * u⁻¹) = m⁻¹ * ((u * m * u⁻¹) * (u * m' * u⁻¹)) *
          (u * m' * u⁻¹)⁻¹ := by group
        _ = m' * (u * m' * u⁻¹)⁻¹ := by rw [h4]; group
    have h5 : m⁻¹ * (u * m * u⁻¹) ∈ V :=
      mem_inf.mpr ⟨mul_mem (inv_mem hm) h1, by rw [h3]; exact mul_mem hm' (inv_mem h2)⟩
    have h6 := (mem_normalizer_iff.mp hmV _).mp h5
    rwa [show m * (m⁻¹ * (u * m * u⁻¹)) * m⁻¹ = u * m * u⁻¹ * m⁻¹ by group] at h6
  obtain ⟨v, hv, hvU⟩ := exists_fixed_in_coset hU hV hUV hmV hx
  set x := m * v with hxdef
  have hxM : x ∈ M := mul_mem hm (mem_inf.mp hv).1
  have hxU : ∀ u ∈ U, u * x = x * u := by
    intro u hu
    have h1 := hvU u hu
    calc u * x = u * x * u⁻¹ * u := by group
      _ = x * u := by rw [h1]
  have hxf : x * f = f * x := (hxU f hfU).symm
  have hx'M' : x⁻¹ * f ∈ M' := by
    rw [hxdef, hfmm', show (m * v)⁻¹ * (m * m') = v⁻¹ * m' by group]
    exact mul_mem (inv_mem (mem_inf.mp hv).2) hm'
  have hx2V : x * x ∈ V := by
    refine mem_inf.mpr ⟨mul_mem hxM hxM, ?_⟩
    have h1 : x * x = ((x⁻¹ * f) * (x⁻¹ * f))⁻¹ := by
      have h2 : (x⁻¹ * f) * (x⁻¹ * f) = x⁻¹ * x⁻¹ * (f * f) := by
        calc (x⁻¹ * f) * (x⁻¹ * f) = x⁻¹ * (f * x⁻¹) * f := by group
          _ = x⁻¹ * (x⁻¹ * f) * f := by
            rw [show f * x⁻¹ = x⁻¹ * f by
              rw [eq_comm, inv_mul_eq_iff_eq_mul, ← mul_assoc, hxf, mul_inv_cancel_right]]
          _ = x⁻¹ * x⁻¹ * (f * f) := by group
      rw [h2, hf2, mul_one, mul_inv_rev, inv_inv]
    rw [h1]
    exact inv_mem (mul_mem hx'M' hx'M')
  set q := orderOf (x * x) with hqdef
  have hqodd : Odd q := by
    have h1 : orderOf (⟨x * x, hx2V⟩ : ↥V) ∣ Nat.card ↥V := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hV.of_dvd_nat h1
  obtain ⟨k, hk⟩ := hqodd
  set a := x ^ q with hadef
  have haM : a ∈ M := pow_mem hxM q
  have ha2 : a * a = 1 := by
    rw [hadef, ← pow_add, ← two_mul, pow_mul, sq, pow_orderOf_eq_one]
  have haU : ∀ u ∈ U, u * a = a * u := by
    intro u hu
    exact ((Commute.pow_right (hxU u hu) q))
  have haf : a * f = f * a := (haU f hfU).symm
  have hbM' : a * f ∈ M' := by
    have h1 : a * f = (x * x) ^ (k + 1) * (x⁻¹ * f) := by
      rw [hadef, hk, ← pow_two, ← pow_mul]
      group
    rw [h1]
    exact mul_mem (pow_mem (mem_inf.mp hx2V).2 _) hx'M'
  refine ⟨a, haM, a * f, hbM', by rw [← mul_assoc, ha2, one_mul], ha2, ?_, ?_, ?_, ?_⟩
  · calc a * f * (a * f) = a * (f * a) * f := by group
      _ = a * (a * f) * f := by rw [haf]
      _ = (a * a) * (f * f) := by group
      _ = 1 := by rw [ha2, hf2, one_mul]
  · calc a * (a * f) = a * (f * a) := by rw [haf]
      _ = a * f * a := by group
  · intro u hu
    exact mem_centralizer_singleton_iff.mpr (haU u hu)
  · intro u hu
    refine mem_centralizer_singleton_iff.mpr ?_
    have h1 : u * f = f * u := mem_centralizer_singleton_iff.mp (hUf hu)
    calc u * (a * f) = (u * a) * f := by group
      _ = (a * u) * f := by rw [haU u hu]
      _ = a * (u * f) := by group
      _ = a * (f * u) := by rw [h1]
      _ = a * f * u := by group

theorem mem_coreActionKernel_sup [Finite X] {L₁ L₂ : Subgroup X}
    (h₁₂ : L₁ ≤ normalizer (L₂ : Set X)) (h₂₁ : L₂ ≤ normalizer (L₁ : Set X)) {x : X}
    (hx₁ : x ∈ UnbalancedLayer.coreActionKernel L₁)
    (hx₂ : x ∈ UnbalancedLayer.coreActionKernel L₂) :
    x ∈ UnbalancedLayer.coreActionKernel (L₁ ⊔ L₂) := by
  classical
  set O := (pPrimeCore 2 ↥(L₁ ⊔ L₂)).map (L₁ ⊔ L₂).subtype with hOdef
  have hO₁ : (pPrimeCore 2 ↥L₁).map L₁.subtype ≤ O := by
    refine le_pPrimeCore_map ((map_subtype_le _).trans le_sup_left) (sup_le ?_ ?_) ?_
    · exact fun y hy => le_normalizer_pPrimeCore (le_normalizer hy)
    · exact fun y hy => le_normalizer_pPrimeCore (h₂₁ hy)
    · rw [card_map_of_injective L₁.subtype_injective]
      exact pPrimeCore_coprime_card
  have hO₂ : (pPrimeCore 2 ↥L₂).map L₂.subtype ≤ O := by
    refine le_pPrimeCore_map ((map_subtype_le _).trans le_sup_right) (sup_le ?_ ?_) ?_
    · exact fun y hy => le_normalizer_pPrimeCore (h₁₂ hy)
    · exact fun y hy => le_normalizer_pPrimeCore (le_normalizer hy)
    · rw [card_map_of_injective L₂.subtype_injective]
      exact pPrimeCore_coprime_card
  refine UnbalancedLayer.mem_coreActionKernel.mpr
    ⟨inf_normalizer_le_normalizer_sup _ _ ⟨hx₁.1, hx₂.1⟩, fun y hy => ?_⟩
  have hy' : y ∈ ((L₂ ⊔ L₁ : Subgroup X) : Set X) := by rw [sup_comm]; exact hy
  rw [coe_mul_of_left_le_normalizer_right L₂ L₁ h₂₁] at hy'
  obtain ⟨l₂, hl₂, l₁, hl₁, rfl⟩ := hy'
  have hc₁ := hO₁ ((UnbalancedLayer.mem_coreActionKernel.mp hx₁).2 l₁ hl₁)
  have hc₂ := hO₂ ((UnbalancedLayer.mem_coreActionKernel.mp hx₂).2 l₂ hl₂)
  have hl₁O : l₁⁻¹ ∈ normalizer (O : Set X) :=
    le_normalizer_pPrimeCore (le_normalizer (inv_mem (mem_sup_left hl₁)))
  have h1 := (mem_normalizer_iff.mp hl₁O _).mp hc₂
  rw [inv_inv] at h1
  have h2 := mul_mem h1 hc₁
  rwa [show l₁⁻¹ * (l₂⁻¹ * x⁻¹ * l₂ * x) * l₁ * (l₁⁻¹ * x⁻¹ * l₁ * x) =
    (l₂ * l₁)⁻¹ * x⁻¹ * (l₂ * l₁) * x by group] at h2

theorem eq_bot_of_perfect_of_solvable {G : Type*} [Group G] {B : Subgroup G}
    (hB : ⁅B, B⁆ = B) [Group.IsSolvable B] : B = ⊥ := by
  have htop : commutator B = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_subtype_commutator, hB, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hder : ∀ k, derivedSeries B k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
  obtain ⟨k, hk⟩ := Group.IsSolvable.solvable (G := B)
  rw [hder] at hk
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : B) ∈ (⊥ : Subgroup B) := hk ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at hx' ⊢
  exact congrArg Subtype.val hx'

theorem eq_bot_of_perfect_of_commute_fixAlt {m : ℕ} {τ : Perm (Fin m)}
    (h4 : τ.support.card ≤ 4) (h5 : 5 ≤ m - τ.support.card) {P : Subgroup (Perm (Fin m))}
    (hP : ⁅P, P⁆ = P) (hc : ∀ p ∈ P, ∀ σ ∈ fixAlt τ, p * (σ : Perm (Fin m)) = σ * p) :
    P = ⊥ := by
  classical
  have hfix : ∀ p ∈ P, ∀ ω, ω ∉ τ.support → p ω = ω := fun p hp ω hω =>
    apply_eq_of_commute_fixAlt (by omega) (hc p hp) hω
  have hS : ∀ l ∈ P, ∀ x, l x ∈ τ.support ↔ x ∈ τ.support := by
    intro l hl x
    constructor
    · intro hlx
      by_contra hx
      rw [hfix l hl x hx] at hlx
      exact hx hlx
    · intro hx
      by_contra hlx
      have h1 := hfix l hl (l x) hlx
      have h2 : l x = x := l.injective h1
      exact hlx (by rw [h2]; exact hx)
  set ψ := CatFactsSmall.restrHom P τ.support hS with hψdef
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro l hl
    apply Subtype.ext
    refine Perm.ext fun x => ?_
    by_cases hx : x ∈ τ.support
    · have h1 := congrArg (fun σ : Perm {x // x ∈ τ.support} => (σ ⟨x, hx⟩ : Fin m)) hl
      simpa [ψ, CatFactsSmall.restrHom] using h1
    · simpa using hfix l l.2 x hx
  have : Group.IsSolvable (Perm {x // x ∈ τ.support}) :=
    Equiv.Perm.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact h4)
  have : Group.IsSolvable ↥P := Group.isSolvable_of_isSolvable_injective hinj
  exact eq_bot_of_perfect_of_solvable hP

end SwapP2

end CFSG.ComponentClassification.SolMax
