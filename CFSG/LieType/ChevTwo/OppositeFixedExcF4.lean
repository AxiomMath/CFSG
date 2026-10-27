module

public import CFSG.LieType.ChevTwo.OppositeFixedExcTwCore
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusNum

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Chevalley.EvenOddRadical CFSG.Open

variable {K : Type} [Field K]

section Cert


theorem coe_exactNormalAut_one (τ : Tag) (σ : K ≃+* K) (h : ↥(adjointGroup τ K)) :
    ((exactNormalAut τ K 1 σ 0 h : ↥(adjointGroup τ K)) : ModGL τ K) =
      Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) := by
  rw [coe_exactNormalAut, exactQ_zero, rootDiagUnit_one, inv_one]
  simp

theorem uniqueNormalFormTw_F4 [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {R : Subgroup (MulAut ↥(C0 (1 : RingAut K)))} (hR : ∀ α ∈ R, Odd (orderOf α)) :
    UniqueNormalFormTw (1 : RingAut K) R := by
  classical
  haveI : CharP K 2 := charP_two_of_card_two_pow hK
  haveI : CharP K ReeTag.F4.prime := (inferInstance : CharP K 2)
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨hΓ, -, -, -, ⟨Ψ, hΨ, -, -, -⟩, -, hσ, -⟩ :=
    even_E6_pure_graph_fixed_group_exact_F4 K hK2
  have e1 : ((1 : RingAut K) : K →+* K) = RingHom.id K := rfl
  have hC0 : C0 (1 : RingAut K) = twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
    rw [C0, e1]; exact hΓ.symm
  let Ψ'' : ↥(C0 (1 : RingAut K)) ≃* ↥(adjointGroup ReeTag.F4.tag K) :=
    (MulEquiv.subgroupCongr hC0).trans Ψ
  have hF4 := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨-, hex, ⟨Θ, hΘ, -, -⟩, -, -, -, -⟩ := hF4
  have hσ₀c : ∀ δ : RingAut K, δ * (1 : RingAut K) = (1 : RingAut K) * δ := fun δ => by simp
  have hΨ'' : ∀ h : ↥(C0 (1 : RingAut K)), ((Ψ'' h : ↥(adjointGroup ReeTag.F4.tag K)) : ModGL ReeTag.F4.tag K) =
      e6FixedToF4 K ⟨(h : ModGL TwistTag.E6.tag K), hC0 ▸ h.2⟩ := fun h => hΨ _
  have hint : ∀ (σ : RingAut K) (h : ↥(C0 (1 : RingAut K))),
      ((Ψ'' ⟨Units.map (entrywiseHom σ.toRingHom) (h : ModGL TwistTag.E6.tag K),
          fieldAut_mem_C0 hσ₀c σ h.2⟩ : ↥(adjointGroup ReeTag.F4.tag K)) : ModGL ReeTag.F4.tag K) =
        Units.map (entrywiseHom σ.toRingHom) ((Ψ'' h : ↥(adjointGroup ReeTag.F4.tag K)) :
          ModGL ReeTag.F4.tag K) := by
    intro σ h
    rw [hΨ'', hΨ'']
    exact (hσ σ).2 _ _ rfl
  have hpar : ∀ (α' : MulAut ↥(adjointGroup ReeTag.F4.tag K)), Odd (orderOf α') →
      ∀ (g : ↥(adjointGroup ReeTag.F4.tag K)) (k : ℕ),
        α' = MulAut.conj g * ReeTag.F4.finiteExceptionalAut K ^ k → Even k := by
    intro α' hodd g k hk
    have h1 := hΘ α' g k hk
    have h2 : (Θ α') ^ orderOf α' = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [h1, ← ofAdd_nsmul] at h2
    have h3 : orderOf α' • (k : ZMod (2 * f)) = 0 := by
      have := congrArg Multiplicative.toAdd h2
      simpa using this
    rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h3
    have h4 : 2 ∣ orderOf α' * k := (dvd_mul_right 2 f).trans h3
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h4 with h | h
    · exact absurd h (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hodd))
    · exact even_iff_two_dvd.2 h
  have hfrob : ∀ σ : RingAut K, ∃ j : ℕ, j < f ∧ ∀ c, σ c = c ^ 2 ^ j := fun σ =>
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.exists_ringEquiv_eq_frobenius_pow Nat.prime_two hf
      hK σ
  have hsig : ∀ (σ : RingAut K) (j : ℕ), (∀ c, σ c = c ^ 2 ^ j) →
      exactNormalAut ReeTag.F4.tag K 1 σ 0 = ReeTag.F4.finiteFrobeniusAut K ^ j :=
    fun σ j hσj => exactNormalAut_one_eq_finiteFrobeniusAut_pow (t := ReeTag.F4) hσj
  have hmodel : ∀ (α : MulAut ↥(C0 (1 : RingAut K))) (g : ↥(C0 (1 : RingAut K))) (σ : RingAut K),
      (∀ h : ↥(C0 (1 : RingAut K)), ((α h : ↥(C0 (1 : RingAut K))) : ModGL TwistTag.E6.tag K) =
        (g : ModGL TwistTag.E6.tag K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL _ K) *
          (g : ModGL TwistTag.E6.tag K)⁻¹) →
      ∀ x : ↥(adjointGroup ReeTag.F4.tag K),
        MulAut.congr Ψ'' α x = MulAut.conj (Ψ'' g) (exactNormalAut ReeTag.F4.tag K 1 σ 0 x) := by
    intro α g σ hα x
    have hx : (⟨Units.map (entrywiseHom σ.toRingHom) ((Ψ''.symm x : ↥(C0 (1 : RingAut K))) :
        ModGL TwistTag.E6.tag K), fieldAut_mem_C0 hσ₀c σ (Ψ''.symm x).2⟩ : ↥(C0 (1 : RingAut K))) =
        ⟨_, fieldAut_mem_C0 hσ₀c σ (Ψ''.symm x).2⟩ := rfl
    have hαx : α (Ψ''.symm x) = g * ⟨Units.map (entrywiseHom σ.toRingHom)
        ((Ψ''.symm x : ↥(C0 (1 : RingAut K))) : ModGL TwistTag.E6.tag K),
          fieldAut_mem_C0 hσ₀c σ (Ψ''.symm x).2⟩ * g⁻¹ := Subtype.ext (hα _)
    change Ψ'' (α (Ψ''.symm x)) = _
    rw [hαx, map_mul, map_mul, map_inv, MulAut.conj_apply]
    congr 2
    refine Subtype.ext ?_
    rw [coe_exactNormalAut_one]
    have := hint σ (Ψ''.symm x)
    rwa [MulEquiv.apply_symm_apply] at this
  intro α hα
  have hodd : Odd (orderOf (MulAut.congr Ψ'' α)) := by
    rw [(MulAut.congr Ψ'').orderOf_eq α]
    exact hR α hα
  obtain ⟨⟨g', k⟩, hgk, huniq⟩ := hex (MulAut.congr Ψ'' α)
  have hkeven : Even (k : ℕ) := hpar _ hodd g' k hgk
  obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = 2 * j := ⟨(k : ℕ) / 2, by
    obtain ⟨m, hm⟩ := hkeven; omega⟩
  have hjf : j < f := by have := k.2; omega
  let δ : RingAut K := iterateFrobeniusEquiv K 2 j
  have hδ : ∀ c, δ c = c ^ 2 ^ j := iterateFrobeniusEquiv_def K 2 j
  have hα' : MulAut.congr Ψ'' α = MulAut.conj g' * exactNormalAut ReeTag.F4.tag K 1 δ 0 := by
    rw [hgk, hj, finiteExceptionalAut_pow_two_mul, hsig δ j hδ]
  refine ⟨(Ψ''.symm g', δ), fun h => ?_, ?_⟩
  ·
    show ((α h : ↥(C0 (1 : RingAut K))) : ModGL TwistTag.E6.tag K) =
      ((Ψ''.symm g' : ↥(C0 (1 : RingAut K))) : ModGL TwistTag.E6.tag K) *
        Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) *
          ((Ψ''.symm g' : ↥(C0 (1 : RingAut K))) : ModGL TwistTag.E6.tag K)⁻¹
    have hmem := fieldAut_mem_C0 hσ₀c δ h.2
    have e : α h = Ψ''.symm g' * ⟨Units.map (entrywiseHom δ.toRingHom)
        (h : ModGL TwistTag.E6.tag K), hmem⟩ * (Ψ''.symm g')⁻¹ := by
      apply Ψ''.injective
      have h1 : Ψ'' (α h) = MulAut.congr Ψ'' α (Ψ'' h) := by
        change _ = Ψ'' (α (Ψ''.symm (Ψ'' h)))
        rw [MulEquiv.symm_apply_apply]
      rw [h1, hα', MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
      congr 2
      refine Subtype.ext ?_
      rw [coe_exactNormalAut_one]
      exact (hint δ h).symm
    rw [e]
    rfl
  ·
    rintro ⟨g₂, δ₂⟩ hg₂
    obtain ⟨j₂, hj₂, hδ₂⟩ := hfrob δ₂
    have hα₂ : MulAut.congr Ψ'' α =
        MulAut.conj (Ψ'' g₂) * ReeTag.F4.finiteExceptionalAut K ^ (2 * j₂) := by
      rw [finiteExceptionalAut_pow_two_mul, ← hsig δ₂ j₂ hδ₂]
      exact MulEquiv.ext (hmodel α g₂ δ₂ hg₂)
    have hu := huniq (Ψ'' g₂, ⟨2 * j₂, by omega⟩) hα₂
    have h1 : Ψ'' g₂ = g' := congrArg Prod.fst hu
    have h2 : 2 * j₂ = (k : ℕ) := congrArg (fun y : _ × Fin (2 * f) => (y.2 : ℕ)) hu
    have hjj : j₂ = j := by omega
    subst hjj
    have hδδ : δ₂ = δ := RingEquiv.ext fun c => by rw [hδ₂, hδ]
    refine Prod.ext ?_ hδδ
    simpa using congrArg Ψ''.symm h1

theorem nonempty_C0_equiv_F4 (hK2 : ringChar K = 2) :
    Nonempty (↥(C0 (1 : RingAut K)) ≃* ↥(adjointGroup Tag.F4 K)) := by
  obtain ⟨hΓ, -, -, -, ⟨Ψ, -⟩, -⟩ := even_E6_pure_graph_fixed_group_exact_F4 K hK2
  have e1 : ((1 : RingAut K) : K →+* K) = RingHom.id K := rfl
  have hC0 : C0 (1 : RingAut K) = twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
    rw [C0, e1]; exact hΓ.symm
  exact ⟨(MulEquiv.subgroupCongr hC0).trans Ψ⟩

theorem odd_orderOf_of_isPGroup {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup G} (hR : IsPGroup p R) : ∀ α ∈ R, Odd (orderOf α) := by
  intro α hα
  obtain ⟨k, hk⟩ := hR ⟨α, hα⟩
  have h1 : orderOf α ∣ p ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    simpa using congrArg Subtype.val hk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 h1
  rw [hi]
  exact (hp.eq_two_or_odd'.resolve_left hp2).pow

theorem oppositeFixed_C0_F4 [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    OppositeFixed ↥(C0 (1 : RingAut K)) := by
  haveI : CharP K 2 := charP_two_of_card_two_pow hK
  exact oppositeFixed_C0 (σ₀ := 1) (fun c => rfl) (fun δ => by simp)
    (fun p hp hp2 R hR => uniqueNormalFormTw_F4 hf hK (odd_orderOf_of_isPGroup hp hp2 hR))

theorem oppositeFixed_of_untwistedChevalleyModel_F4 {S : Type} [Group S] {f : ℕ} (hf : 1 ≤ f)
    (h : UntwistedChevalleyModel S Tag.F4 (2 ^ f)) : OppositeFixed S := by
  obtain ⟨K', _, hfin, hcard, ⟨e⟩⟩ := h
  haveI : CharP K' 2 := charP_two_of_card_two_pow hcard
  obtain ⟨Ψ''⟩ := nonempty_C0_equiv_F4 (K := K') (ringChar.eq K' 2)
  have e' : S ≃* ↥(adjointGroup Tag.F4 K') := e.trans
    ((QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := Tag.F4) (K := K'))).trans
      QuotientGroup.quotientBot)
  exact oppositeFixed_of_mulEquiv (e'.trans Ψ''.symm) (oppositeFixed_C0_F4 hf hcard)

end Cert

end CFSG.LieType.ChevTwo.Semi
