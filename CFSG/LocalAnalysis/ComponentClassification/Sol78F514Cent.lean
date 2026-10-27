module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Basic

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_mem_of_odd_of_orderOf_two {K : Subgroup G} (hK : Odd (Nat.card K)) {x : G}
    (hx : orderOf x = 2) : x ∉ K := fun hxK => by
  have h1 := Subgroup.orderOf_dvd_natCard K hxK
  rw [hx] at h1
  exact (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr h1)

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem type_𝕊 : Nonempty (𝕊 ≃* alternatingGroup (Fin 7)) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel 𝕊 .PSL 2 p f := by
  obtain ⟨e₀⟩ := H.sec5.quotient_simple.2
  rcases H.sec5.sec4.footeFamilyType with ⟨⟨e₁⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
  · exact Or.inl ⟨ε.symm.trans (e₀.trans e₁)⟩
  · exact Or.inr ⟨p, f, hp, hp2, hf,
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (ε.symm.trans e₀).symm hL⟩

theorem orderOf_psi_t : orderOf (psi L ε ⟨t, H.sec5.tL⟩) = 2 := by
  apply orderOf_eq_prime
  · rw [sq, ← map_mul]
    rw [show (⟨t, H.sec5.tL⟩ * ⟨t, H.sec5.tL⟩ : ↥L) = 1 from Subtype.ext H.mul_self_t, map_one]
  · intro h1
    rw [psi_eq_one_iff] at h1
    exact not_mem_of_odd_of_orderOf_two (odd_card_oddCoreIn L) H.sec5.t2 h1

theorem perfectCore_le_coreActionKernel {X : Subgroup G} (hXN : X ≤ normalizer (L : Set G))
    (hXt : ∀ x ∈ X, x * t = t * x) : perfectCore X ≤ coreActionKernel L := by
  set N := normalizer (L : Set G) with hN
  set τ := psi L ε ⟨t, H.sec5.tL⟩ with hτ
  set X' := X.subgroupOf N with hX'
  set A := X'.map (act L ε) with hA
  have htN : t ∈ N := le_normalizer H.sec5.tL
  have hactt : act L ε ⟨t, htN⟩ = MulAut.conj τ := act_of_mem ε ⟨t, H.sec5.tL⟩ htN
  have hAc : ∀ α ∈ A, α * MulAut.conj τ = MulAut.conj τ * α := by
    rintro _ ⟨x, hx, rfl⟩
    have hxt : x * ⟨t, htN⟩ = ⟨t, htN⟩ * x := Subtype.ext (hXt _ (mem_subgroupOf.mp hx))
    rw [← hactt, ← map_mul, hxt, map_mul]
  have hPinn : perfectCore A ≤ innAut5 𝕊 := by
    rw [← perfectCore_perfect A, commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact H.autData.commutator_mem a b
  have hcen : center 𝕊 = ⊥ := H.sec5.center_eq_bot ε
  have hconj_inj : Function.Injective (MulAut.conj : 𝕊 →* MulAut 𝕊) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have hac : a ∈ center 𝕊 := by
      rw [mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut 𝕊 => φ g) ha
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * a = a * g * a⁻¹ * a := by rw [h1]
        _ = a * g := by group
    rw [hcen] at hac
    exact hac
  have hPM : perfectCore A ≤ (centralizer ({τ} : Set 𝕊)).map (MulAut.conj : 𝕊 →* MulAut 𝕊) := by
    intro α hα
    obtain ⟨a, rfl⟩ := hPinn hα
    refine ⟨a, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have h1 := hAc _ (perfectCore_le A hα)
    rw [← map_mul, ← map_mul] at h1
    exact hconj_inj h1
  have hsolvC : Group.IsSolvable ↥(centralizer ({τ} : Set 𝕊)) :=
    H.sec5.sec4.hSolv 𝕊 H.type_𝕊 τ H.orderOf_psi_t
  have hsolvM : Group.IsSolvable
      ↥((centralizer ({τ} : Set 𝕊)).map (MulAut.conj : 𝕊 →* MulAut 𝕊)) :=
    Group.isSolvable_of_surjective
      (f := ((centralizer ({τ} : Set 𝕊)).equivMapOfInjective _ hconj_inj).toMonoidHom)
      ((centralizer ({τ} : Set 𝕊)).equivMapOfInjective _ hconj_inj).surjective
  have hPbot : perfectCore A = ⊥ := by
    have h1 := le_perfectCore_of_perfect hPM (perfectCore_perfect A)
    rwa [(isSolvable_iff_perfectCore_eq_bot _).mp hsolvM, le_bot_iff] at h1
  have h2 : (perfectCore X').map (act L ε) = ⊥ := by rw [map_perfectCore, ← hA, hPbot]
  have h3 : (perfectCore X').map N.subtype = perfectCore X := by
    rw [map_perfectCore, hX', subgroupOf_map_subtype, inf_of_le_left hXN]
  intro x hx
  rw [← h3] at hx
  obtain ⟨x', hx', rfl⟩ := hx
  have h4 : act L ε x' = 1 := by
    have h5 : act L ε x' ∈ (perfectCore X').map (act L ε) := mem_map_of_mem _ hx'
    rw [h2, mem_bot] at h5
    exact h5
  exact (act_eq_one_iff ε x').mp h4

theorem isSylowOf_S_CZ :
    IsSylowOf 2 S (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) :=
  H.isSylowOf_S_centralizer_z.of_le
    (le_inf H.sec5.S_le_centralizer fun x hx => mem_centralizer_singleton_iff.mpr (H.sec5.tZ x hx))
    inf_le_left

theorem isSolvable_CZ :
    Group.IsSolvable ↥(centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set CZ := centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) with hCZ
  rw [isSolvable_iff_perfectCore_eq_bot]
  set Y := perfectCore CZ with hY
  have hY1 : Y ≤ coreActionKernel L := H.perfectCore_le_coreActionKernel
    (inf_le_left.trans H.sec5.centralizer_le_normalizer)
    (fun x hx => mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2)
  have hCZs : CZ.map (MulAut.conj s).toMonoidHom = CZ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hxz := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).1
      have hxt := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
        mem_centralizer_singleton_iff.mpr ?_⟩
      ·
        rw [← H.conj_s_t]
        calc s * x * s⁻¹ * (s * t * s⁻¹) = s * (x * t) * s⁻¹ := by group
          _ = s * (t * x) * s⁻¹ := by rw [hxt]
          _ = s * t * s⁻¹ * (s * x * s⁻¹) := by group
      · rw [← H.conj_s_z]
        calc s * x * s⁻¹ * (s * z * s⁻¹) = s * (x * z) * s⁻¹ := by group
          _ = s * (z * x) * s⁻¹ := by rw [hxz]
          _ = s * z * s⁻¹ * (s * x * s⁻¹) := by group
    · intro x hx
      refine ⟨s⁻¹ * x * s, ?_, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
      have hxz := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).1
      have hxt := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
        mem_centralizer_singleton_iff.mpr ?_⟩
      · rw [← H.conj_s_inv_t]
        calc s⁻¹ * x * s * (s⁻¹ * t * s) = s⁻¹ * (x * t) * s := by group
          _ = s⁻¹ * (t * x) * s := by rw [hxt]
          _ = s⁻¹ * t * s * (s⁻¹ * x * s) := by group
      · rw [← H.conj_s_inv_z]
        calc s⁻¹ * x * s * (s⁻¹ * z * s) = s⁻¹ * (x * z) * s := by group
          _ = s⁻¹ * (z * x) * s := by rw [hxz]
          _ = s⁻¹ * z * s * (s⁻¹ * x * s) := by group
  have hYs : Y.map (MulAut.conj s).toMonoidHom = Y := by
    rw [hY, map_perfectCore, hCZs]
  have hYS : S ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyS, hyY⟩ := mem_inf.mp hy
    have hyQ : y ∈ Q := by
      rw [← H.sec5.inf_coreActionKernel]; exact mem_inf.mpr ⟨hyS, hY1 hyY⟩
    have hy' : s * y * s⁻¹ ∈ Y := by
      rw [← hYs]
      exact ⟨y, hyY, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have hy'S : s * y * s⁻¹ ∈ S := by
      have := Foote5.conj_mem_of_mem_normalizer (inv_mem H.s_mem_normalizer) hyS
      rwa [inv_inv] at this
    have hy'Q : s * y * s⁻¹ ∈ Q := by
      rw [← H.sec5.inf_coreActionKernel]; exact mem_inf.mpr ⟨hy'S, hY1 hy'⟩
    have h1 : y ∈ Q ⊓ conjugate Q s := mem_inf.mpr ⟨hyQ, mem_conjugate_iff.mpr hy'Q⟩
    rwa [H.QQs] at h1
  have hYodd : Odd (Nat.card Y) := by
    have hsyl : IsSylowOf 2 (S ⊓ Y) Y := H.isSylowOf_S_CZ.inf_of_le_normalizer (perfectCore_le CZ)
      ((normal_subgroupOf_iff_le_normalizer (perfectCore_le CZ)).mp (perfectCore_normal CZ))
    have h1 := hsyl.card_eq
    rw [hYS, card_bot] at h1
    have h2 : (Nat.card Y).factorization 2 = 0 := by
      have h3 : 2 ^ (Nat.card Y).factorization 2 = 2 ^ 0 := by rw [← h1, pow_zero]
      exact Nat.pow_right_injective le_rfl h3
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h4
    have h5 := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two (Nat.card_pos.ne')).mp h4
    omega
  have hYsolv : Group.IsSolvable Y := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hYodd
  have hYperf : perfectCore Y = Y := perfectCore_eq_self_of_perfect (perfectCore_perfect CZ)
  rw [← hYperf]
  exact (isSolvable_iff_perfectCore_eq_bot Y).mp hYsolv

end Hyp

end CFSG.ComponentClassification.Sol78.F514
