module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNFOrbBase
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNFOrb
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFForm

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv NFOrb

variable {X : Type} [Group X]

variable {M : Subgroup X} {n : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)}

theorem false_of_four_fix_orbit [Finite X] (hρ : IsPermAction θ ρ) (hn : 11 ≤ n) (hodd : Odd n)
    {a g : X} (hCaN : centralizer ({a} : Set X) ≤ normalizer (M : Set X))
    (hsN : g⁻¹ * a * g ∈ normalizer (M : Set X)) (hs2 : g⁻¹ * a * g * (g⁻¹ * a * g) = 1)
    {x : X} (hxM : x ∈ M) (hxo : x ∈ oddGen (centralizer ({g⁻¹ * a * g} : Set X)))
    (hx2 : x * x = 1) (hxf : FourForm (ρ ⟨g⁻¹ * a * g, hsN⟩) (ρ ⟨x, le_normalizer hxM⟩))
    (hx'N : g * x * g⁻¹ ∈ normalizer (M : Set X))
    (hx'5 : n - (ρ ⟨g * x * g⁻¹, hx'N⟩).support.card < 5)
    (h10 : 10 ≤ (ρ ⟨g⁻¹ * a * g, hsN⟩).support.card)
    (hfix : n ≤ (ρ ⟨g⁻¹ * a * g, hsN⟩).support.card + 4) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s := g⁻¹ * a * g with hsdef
  set σ := ρ ⟨s, hsN⟩ with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul, show (⟨s, hsN⟩ : ↥(normalizer (M : Set X))) * ⟨s, hsN⟩ = 1 from
      Subtype.ext hs2, map_one]
  obtain ⟨i₀, hi₀, i₁, hi₁, -, -, hδ⟩ : ∃ i ∈ σ.support, ∃ i' ∈ σ.support, i' ≠ i ∧
      i' ≠ σ i ∧ ρ ⟨x, le_normalizer hxM⟩ = swap i (σ i) * swap i' (σ i') := by
    rcases hxf with ⟨-, h⟩ | ⟨h6, -⟩
    · exact h
    · omega
  have hgs : g * s * g⁻¹ = a := by rw [hsdef]; group
  set ιM : ↥M →* Perm (Fin n) := ρ.comp (inclusion le_normalizer) with hιMdef
  have hιM : ∀ m : ↥M, ιM m = ρ ⟨m, le_normalizer m.2⟩ := fun _ => rfl
  set PM : Subgroup ↥M := (oddCentGen σ).comap ιM ⊓
    (oddGen (centralizer ({s} : Set X))).subgroupOf M with hPMdef
  set ρP : ↥PM →* ↥(oddCentGen σ) :=
    (ιM.comp PM.subtype).codRestrict _ (fun z => (mem_inf.mp z.2).1) with hρPdef
  have hρP : ∀ z : ↥PM, ((ρP z : ↥(oddCentGen σ)) : Perm (Fin n)) =
      ρ ⟨((z : ↥M) : X), le_normalizer (z : ↥M).2⟩ := fun _ => rfl
  have hρPs : Function.Surjective ρP := by
    rintro ⟨π, hπ⟩
    obtain ⟨q, hq, hqo, hρq⟩ := hρ.exists_lift_oddCentGen (by omega) hsN hs2 hπ
    refine ⟨⟨⟨q, hq⟩, mem_inf.mpr ⟨?_, hqo⟩⟩, Subtype.ext ?_⟩
    · change ιM ⟨q, hq⟩ ∈ oddCentGen σ
      rw [hιM, hρq]
      exact hπ
    · rw [hρP]
      exact hρq
  have hconjN : ∀ z : ↥PM, g * ((z : ↥M) : X) * g⁻¹ ∈ normalizer (M : Set X) := by
    intro z
    have h1 := conj_mem_oddGen_centralizer (g := g) (mem_inf.mp z.2).2
    rw [hgs] at h1
    exact hCaN (oddGen_le _ h1)
  set φc : ↥PM →* X := (MulAut.conj g).toMonoidHom.comp (M.subtype.comp PM.subtype) with hφcdef
  set φ : ↥PM →* Perm (Fin n) := ρ.comp (φc.codRestrict _ hconjN) with hφdef
  have hφ : ∀ z : ↥PM, φ z = ρ ⟨g * ((z : ↥M) : X) * g⁻¹, hconjN z⟩ := fun _ => rfl
  set B : Subgroup ↥(oddCentGen σ) := (baseGroup σ hσ2).comap (oddCentGen σ).subtype with hBdef
  have hBn : B.Normal :=
    ⟨fun u hu w => conj_mem_baseGroup (hσ := hσ2) (commute_of_mem_oddCentGen w.2) hu⟩
  have hB2 : IsPGroup 2 ↥B := by
    intro u
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    rw [pow_one, sq]
    exact mul_self_of_mem_baseGroup (hσ := hσ2) u.2
  set V : Subgroup ↥PM := B.comap ρP with hVdef
  have hVn : V.Normal := hBn.comap ρP
  have hxδ : ρ ⟨x, le_normalizer hxM⟩ ∈ oddCentGen σ := by
    rw [hδ]
    exact mul_mem_oddCentGen_of_mem_cycleFactorsFinset hσ2 (by omega)
      (swap_mem_cycleFactorsFinset hσ2 hi₀) (swap_mem_cycleFactorsFinset hσ2 hi₁)
  set xP : ↥PM := ⟨⟨x, hxM⟩, mem_inf.mpr ⟨hxδ, hxo⟩⟩ with hxPdef
  have hxV : xP ∈ V := by
    change ρ ⟨x, le_normalizer hxM⟩ ∈ baseGroup σ hσ2
    rw [hδ]
    exact mul_mem swap_mem_baseGroup swap_mem_baseGroup
  set xV : ↥V := ⟨xP, hxV⟩ with hxVdef
  have hxV2 : xV ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    exact Subtype.ext (Subtype.ext (Subtype.ext hx2))
  obtain ⟨D, hxD⟩ := (isPGroup_zpowers_of_pow_eq_one hxV2).exists_le_sylow
  set D' : Subgroup ↥PM := (D : Subgroup ↥V).map V.subtype with hD'def
  have hxD' : xP ∈ D' := ⟨xV, hxD (mem_zpowers xV), rfl⟩
  have hD'V : D' ≤ V := map_subtype_le _
  have hinj : ∀ d ∈ D', ρP d = 1 → d = 1 := by
    intro d hd h1
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    obtain ⟨k, hk⟩ := D.isPGroup' ⟨d₀, hd₀⟩
    have hk' : (V.subtype d₀) ^ 2 ^ k = 1 := by
      have := congrArg (fun y : ↥(D : Subgroup ↥V) => V.subtype (y : ↥V)) hk
      simpa using this
    have hcore : (((V.subtype d₀ : ↥PM) : ↥M) : X) ∈ (pPrimeCore 2 ↥M).map M.subtype := by
      refine mem_core_of_mem_coreActionKernel hρ (by omega) ((V.subtype d₀ : ↥PM) : ↥M).2
        (hρ.mem_coreActionKernel (le_normalizer ((V.subtype d₀ : ↥PM) : ↥M).2) ?_)
      have h2 := congrArg Subtype.val h1
      rw [hρP] at h2
      exact h2
    have hodd : Odd (orderOf (V.subtype d₀)) := by
      have h2 := odd_orderOf_of_mem_oddCoreIn hcore
      rwa [Subgroup.orderOf_coe, Subgroup.orderOf_coe] at h2
    have hdvd := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hm] at hodd
    have hm0 : m = 0 := by
      by_contra hm0
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      rw [pow_succ] at hodd
      exact absurd hodd (by simp [Nat.odd_mul])
    rw [hm0, pow_zero] at hm
    exact orderOf_eq_one_iff.mp hm
  set ρV : ↥V →* ↥B := (ρP.comp V.subtype).codRestrict B (fun v => v.2) with hρVdef
  have hρVs : Function.Surjective ρV := by
    intro u
    obtain ⟨z, hz⟩ := hρPs u
    have hzV : z ∈ V := by
      change ρP z ∈ B
      rw [hz]
      exact u.2
    exact ⟨⟨z, hzV⟩, Subtype.ext hz⟩
  have hDtop : (D.mapSurjective hρVs : Subgroup ↥B) = ⊤ :=
    ((D.mapSurjective hρVs).is_maximal' (hB2.to_subgroup ⊤) le_top).symm
  set ρD : ↥D' →* ↥B := (ρP.comp D'.subtype).codRestrict B (fun d => hD'V d.2) with hρDdef
  have hρDi : Function.Injective ρD := by
    rw [injective_iff_map_eq_one]
    intro d hd
    exact Subtype.ext (hinj d d.2 (congrArg Subtype.val hd))
  have hρDs : Function.Surjective ρD := by
    intro u
    have hu : u ∈ (D.mapSurjective hρVs : Subgroup ↥B) := by rw [hDtop]; exact mem_top u
    rw [Sylow.coe_mapSurjective] at hu
    obtain ⟨d₀, hd₀, hd₀u⟩ := hu
    exact ⟨⟨V.subtype d₀, d₀, hd₀, rfl⟩, Subtype.ext (congrArg Subtype.val hd₀u)⟩
  set e : ↥D' ≃* ↥B := MulEquiv.ofBijective ρD ⟨hρDi, hρDs⟩ with hedef
  have he : ∀ d : ↥D', (((e d : ↥B) : ↥(oddCentGen σ)) : Perm (Fin n)) =
      ρ ⟨(((d : ↥PM) : ↥M) : X), le_normalizer ((d : ↥PM) : ↥M).2⟩ := fun _ => rfl
  set ι := ↥σ.cycleFactorsFinset
  have hcyc : ∀ c d : ι, (c : Perm (Fin n)) * d ∈ oddCentGen σ := fun c d =>
    mul_mem_oddCentGen_of_mem_cycleFactorsFinset hσ2 (by omega) c.2 d.2
  set u : ι → ι → ↥B := fun c d => ⟨⟨(c : Perm (Fin n)) * d, hcyc c d⟩,
    mul_mem (mem_baseGroup_of_mem_cycleFactorsFinset (hσ := hσ2) c.2)
      (mem_baseGroup_of_mem_cycleFactorsFinset (hσ := hσ2) d.2)⟩ with hudef
  set t : ι → ι → Perm (Fin n) := fun c d => φ (D'.subtype (e.symm (u c d))) with htdef
  have ht : ∀ c d e', t c d * t d e' = t c e' := by
    intro c d e'
    have hu : u c d * u d e' = u c e' := by
      apply Subtype.ext
      apply Subtype.ext
      change (c : Perm (Fin n)) * d * (d * e') = c * e'
      rw [mul_assoc, ← mul_assoc (d : Perm (Fin n)),
        mul_self_of_mem_baseGroup (mem_baseGroup_of_mem_cycleFactorsFinset (hσ := hσ2) d.2),
        one_mul]
    change φ (D'.subtype (e.symm (u c d))) * φ (D'.subtype (e.symm (u d e'))) =
      φ (D'.subtype (e.symm (u c e')))
    rw [← map_mul, ← map_mul, ← map_mul, hu]
  have hs : ∀ c d, t c d = t d c := by
    intro c d
    have hu : u c d = u d c := by
      apply Subtype.ext
      apply Subtype.ext
      exact baseGroup_commute (mem_baseGroup_of_mem_cycleFactorsFinset (hσ := hσ2) c.2)
        (mem_baseGroup_of_mem_cycleFactorsFinset (hσ := hσ2) d.2)
    change φ (D'.subtype (e.symm (u c d))) = φ (D'.subtype (e.symm (u d c)))
    rw [hu]
  have hequiv : ∀ τ ∈ alternatingGroup ι, ∃ π : Perm (Fin n), ∀ c d,
      π * t c d * π⁻¹ = t (τ c) (τ d) := by
    intro τ hτ
    obtain ⟨w, hw⟩ := exists_oddCentGen_cycleAction_eq hσ2 hτ
    obtain ⟨z, hz⟩ := hρPs w
    have hzt : z ∈ normalizer ((D : Subgroup ↥V).map V.subtype) ⊔ V := by
      rw [Sylow.normalizer_sup_eq_top D]
      exact mem_top z
    obtain ⟨y, hy, v, hv, hyv⟩ := mem_sup_of_normal_right.mp hzt
    refine ⟨φ y, fun c d => ?_⟩
    set d₁ : ↥PM := D'.subtype (e.symm (u c d)) with hd₁
    have hd₁D : y * d₁ * y⁻¹ ∈ D' := (mem_normalizer_iff.mp hy d₁).mp (e.symm (u c d)).2
    have hkey : e.symm (u (τ c) (τ d)) = ⟨y * d₁ * y⁻¹, hd₁D⟩ := by
      rw [MulEquiv.symm_apply_eq, ← hw]
      apply Subtype.ext
      apply Subtype.ext
      symm
      have hρy : ρP y = w * (ρP v)⁻¹ := by
        rw [← hz, ← hyv, map_mul, mul_inv_cancel_right]
      have hρd₁ : ρP d₁ = (u c d : ↥(oddCentGen σ)) := by
        have := congrArg Subtype.val (e.apply_symm_apply (u c d))
        exact this
      have hvB : ((ρP v : ↥(oddCentGen σ)) : Perm (Fin n)) ∈ baseGroup σ hσ2 := hv
      have hcdB : (c : Perm (Fin n)) * d ∈ baseGroup σ hσ2 :=
        mul_mem (mem_baseGroup_of_mem_cycleFactorsFinset (hσ := hσ2) c.2)
          (mem_baseGroup_of_mem_cycleFactorsFinset (hσ := hσ2) d.2)
      change ((ρP (y * d₁ * y⁻¹) : ↥(oddCentGen σ)) : Perm (Fin n)) =
        ((Perm.OnCycleFactors.toPermHom σ (inclusion (oddCentGen_le_centralizer σ) w) c :
          ι) : Perm (Fin n)) *
        ((Perm.OnCycleFactors.toPermHom σ (inclusion (oddCentGen_le_centralizer σ) w) d :
          ι) : Perm (Fin n))
      rw [Perm.OnCycleFactors.coe_toPermHom, Perm.OnCycleFactors.coe_toPermHom, map_mul,
        map_mul, map_inv, hρy, hρd₁]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_inclusion]
      have hcomm := baseGroup_commute hvB hcdB
      calc (w : Perm (Fin n)) * ((ρP v : ↥(oddCentGen σ)) : Perm (Fin n))⁻¹ *
            ((c : Perm (Fin n)) * d) *
            ((w : Perm (Fin n)) * ((ρP v : ↥(oddCentGen σ)) : Perm (Fin n))⁻¹)⁻¹ =
          (w : Perm (Fin n)) * (((ρP v : ↥(oddCentGen σ)) : Perm (Fin n))⁻¹ *
            (((c : Perm (Fin n)) * d) * ((ρP v : ↥(oddCentGen σ)) : Perm (Fin n)))) *
            (w : Perm (Fin n))⁻¹ := by group
        _ = (w : Perm (Fin n)) * ((c : Perm (Fin n)) * d) * (w : Perm (Fin n))⁻¹ := by
          rw [← hcomm]
          group
        _ = _ := by group
    change φ y * φ d₁ * (φ y)⁻¹ = φ (D'.subtype (e.symm (u (τ c) (τ d))))
    rw [hkey, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hcardι : Fintype.card ι = σ.cycleFactorsFinset.card := Fintype.card_coe _
  have h2card := two_mul_card_cycleFactorsFinset hσ2
  have h5ι : 5 ≤ Fintype.card ι := by omega
  have hΩ : Fintype.card (Fin n) ≤ 2 * Fintype.card ι + 3 := by
    rw [Fintype.card_fin]
    obtain ⟨m, hm⟩ := hodd
    omega
  set c₀ : ι := ⟨swap i₀ (σ i₀), swap_mem_cycleFactorsFinset hσ2 hi₀⟩
  set c₁ : ι := ⟨swap i₁ (σ i₁), swap_mem_cycleFactorsFinset hσ2 hi₁⟩
  have hsupp := altPairFamilySupportInput_holds ι (Fin n) t h5ι hΩ ht hs hequiv c₀ c₁
  have hex : e.symm (u c₀ c₁) = ⟨xP, hxD'⟩ := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    apply Subtype.ext
    change (swap i₀ (σ i₀) * swap i₁ (σ i₁) : Perm (Fin n)) = ρ ⟨x, le_normalizer hxM⟩
    rw [hδ]
  have htx : t c₀ c₁ = ρ ⟨g * x * g⁻¹, hx'N⟩ := by
    change φ (D'.subtype (e.symm (u c₀ c₁))) = _
    rw [hex]
    rfl
  rw [htx] at hsupp
  omega

end CFSG.ComponentClassification.SolMax
