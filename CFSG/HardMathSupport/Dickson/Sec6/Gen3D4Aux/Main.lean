module

public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.Link
public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.Build
public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.SylowSpec
public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.GenSpec
public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.Cover

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.Quasithin CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.AGLEmbedding.ChevOuter CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

theorem exists_pow_four_ne {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4 ^ 3) :
    ∃ c : k, c ^ 4 ≠ c := by
  by_contra h
  push Not at h
  have : Fintype k := Fintype.ofFinite k
  have hcard : Fintype.card k = 4 ^ 3 := by rw [← Nat.card_eq_fintype_card]; exact hk
  open Polynomial in
  let p : k[X] := X ^ 4 - X
  have hp : p = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (f := id)
      Function.injective_id (fun a => by simp [p, h a]) ?_
    rw [hcard]
    simp only [p]
    have : (Polynomial.X ^ 4 - Polynomial.X : Polynomial k).natDegree ≤ 4 := by
      compute_degree
    omega
  have h4 : p.coeff 4 = 1 := by
    simp [p, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  rw [hp] at h4
  simp at h4

theorem eq_one_of_conj_eq_one' {C : Type*} [Group C] (hZ : Subgroup.center C = ⊥) {g : C}
    (h : (MulAut.conj g : MulAut C) = 1) : g = 1 := by
  have hc : g ∈ Subgroup.center C := Subgroup.mem_center_iff.2 fun y => by
    have := congrArg (fun φ : MulAut C => φ y) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rw [hZ] at hc
  exact hc

theorem isElemAbelian_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {p : ℕ} {B : Subgroup G} (hB : IsElemAbelian p B) :
    IsElemAbelian p (B.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨z, hz, hzb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    have h := congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
    simp only [Subgroup.coe_mul] at h ⊢
    rw [← hxa, ← hzb, ← map_mul, ← map_mul, h]
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow, hB.2 x hx, map_one]

theorem exists_conj_le_sylow {X : Type*} [Group X] [Finite X] (P0 : Sylow 3 X) (A : Subgroup X)
    (hA : IsElemAbelian 3 A) : ∃ g : X, A.map (MulAut.conj g).toMonoidHom ≤ (P0 : Subgroup X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 A := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hA.2 x.1 x.2)⟩
  obtain ⟨Q, hAQ⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P0
  have hQ : ((g • Q : Sylow 3 X) : Subgroup X) = (Q : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g, ?_⟩
  have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hAQ
  rw [← hQ, hg] at this
  exact this

section C0


theorem genBelow_C0 {kf : Type} [Field kf] [Finite kf] [CharP kf 2] (σ : kf ≃+* kf)
    (hk : Nat.card kf = 4 ^ 3) (hσ : ∀ c, σ c = c ^ 4) (e : kf ≃+* GF64)
    (hC0 : graphFixedRootGroup TwistTag.D4 kf σ.toRingHom =
      (twistedGroup σ.toRingHom).map (adjointGroup d4 kf).subtype)
    [IsSimpleGroup ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom)]
    (hv3 : (Nat.card ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom)).factorization 3 = 4) :
    ∀ A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom)),
      IsElemAbelian 3 A → GenBelow A := by
  classical
  have hk2 : Nat.card kf = (2 ^ 2) ^ 3 := by rw [hk]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 2) := fun c => by simpa using hσ c
  obtain ⟨-, hunique, ⟨Θ, hΘ, -, -, -⟩, hcyc, hcard6, -, hZC, -⟩ :=
    even_triality_exact_automorphism_normal_form (f := 2) (by norm_num) kf hk2 σ hσ2
  let fa : RingAut kf →* MulAut ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) :=
    fieldActorHom (t := TwistTag.D4) σ
  have hΘ' : ∀ (g : ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom)) (δ : kf ≃+* kf),
      Θ (MulAut.conj g * fa δ) = δ := fun g δ => hΘ _ g δ rfl
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    show σ (σ (σ c)) = c
    exact sigma_three_of_card (q := 4) hk (σ := σ.toRingHom) (fun c => by simpa using hσ c) c
  have hσ1 : σ ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := exists_pow_four_ne hk
    apply hc
    rw [← hσ c, h]
    rfl
  have hφ3 : fa σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  have hid : ∀ (g : ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom)) (j : ℕ), j < 3 →
      MulAut.conj g * fa σ ^ j = 1 → j = 0 ∧ g = 1 := by
    intro g j hj h
    have h1 : Θ (MulAut.conj g * fa (σ ^ j)) = σ ^ j := hΘ' g _
    rw [map_pow, h, map_one] at h1
    have hj0 : j = 0 := by
      interval_cases j
      · rfl
      · exact absurd (by simpa using h1.symm) hσ1
      · exfalso
        apply hσ1
        have h2 : σ ^ 2 = 1 := h1.symm
        calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
          _ = 1 := by rw [hσ3, h2]; simp
    subst hj0
    refine ⟨rfl, ?_⟩
    rw [pow_zero, mul_one] at h
    exact eq_one_of_conj_eq_one' hZC h
  have hconjinj : Function.Injective
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) →* _) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact eq_one_of_conj_eq_one' hZC hg
  have hψCinj : Function.Injective (psiC σ e hC0) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (psiC σ e hC0).ker with h | h
    · exact h
    · exfalso
      obtain ⟨c, hc⟩ : letterGL 0 ∈ (psiC σ e hC0).range := by
        rw [range_psiC σ hk hσ e hC0]
        exact letterGL_mem (by norm_num)
      have h1 : psiC σ e hC0 c = 1 := by
        rw [← MonoidHom.mem_ker, h]; trivial
      rw [h1] at hc
      exact letterMat_zero_ne_one (congrArg (fun g : GL (Fin 8) GF64 =>
        (g : Matrix (Fin 8) (Fin 8) GF64)) hc).symm
  have hφψ : ∀ g, (psiC σ e hC0 (fa σ g) : Matrix (Fin 8) (Fin 8) GF64) =
      (psiC σ e hC0 g : Matrix (Fin 8) (Fin 8) GF64).map frobF := by
    intro g
    have h1 := psiC_fieldActor σ hk hσ e hC0 σ g
    show (psiC σ e hC0 (fieldActor (t := TwistTag.D4) σ σ g) : Matrix (Fin 8) (Fin 8) GF64) = _
    rw [h1, CFSG.AGLEmbedding.ChevOuterD48.coe_map_gl]
    congr 1
    funext x
    show e (σ (e.symm x)) = frobF x
    rw [frobF_apply, hσ, map_pow, RingEquiv.apply_symm_apply]
  have hlet : ∀ k, k < 16 → ∃ c, psiC σ e hC0 c = letterGL k := by
    intro k hk'
    have : letterGL k ∈ (psiC σ e hC0).range := by
      rw [range_psiC σ hk hσ e hC0]
      exact letterGL_mem hk'
    exact this
  choose! gk hgk using hlet
  have hlt : ∀ k, k < 16 → ∃ g : ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom),
      (psiC σ e hC0 g : Matrix (Fin 8) (Fin 8) GF64) = letterMat k ∧
        (MonoidHom.id (MulAut ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom)))
          (MulAut.conj (gk k)) = MulAut.conj g :=
    fun k hk' => ⟨gk k, by rw [hgk k hk']; rfl, rfl⟩
  let R : Realization (MulAut ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom)) :=
    buildReal (MonoidHom.id _) (psiC σ e hC0) (fa σ) hφ3 hφψ (fun _ _ h => h) hψCinj hid
      (fun k => MulAut.conj (gk k)) hlt (fa σ) rfl
  have hletR : ∀ k, R.letter k = MulAut.conj (gk k) := fun k => rfl
  have hclosure : Subgroup.closure {x | ∃ k, k < 16 ∧ gk k = x} = ⊤ := by
    set H : Subgroup ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) :=
      Subgroup.closure {x | ∃ k, k < 16 ∧ gk k = x} with hH
    have hmapH : H.map (psiC σ e hC0) = letterGroup := by
      rw [MonoidHom.map_closure, letterGroup]
      congr 1
      ext A
      constructor
      · rintro ⟨_, ⟨k, hk', rfl⟩, rfl⟩
        exact ⟨k, hk', (hgk k hk').symm⟩
      · rintro ⟨k, hk', rfl⟩
        exact ⟨gk k, ⟨k, hk', rfl⟩, hgk k hk'⟩
    refine eq_top_iff.2 fun c _ => ?_
    have hc : psiC σ e hC0 c ∈ letterGroup := by
      rw [← range_psiC σ hk hσ e hC0]
      exact ⟨c, rfl⟩
    rw [← hmapH] at hc
    obtain ⟨c', hc', hcc⟩ := hc
    exact (hψCinj hcc) ▸ hc'
  have hI := gen_checkI
  have hII := gen_checkII
  simp only [genCheckI, genCheckII, Bool.and_eq_true] at hI hII
  have hgen : ∀ c, c < 4 → GenBelow (R.Eg c) := by
    intro c hc
    have hchk : genCheckClass c = true := by
      interval_cases c
      · exact hI.1
      · exact hI.2
      · exact hII.1
      · exact hII.2
    have hlett := R.gen_spec hc hchk
    obtain ⟨hElem, hEcard⟩ := R.Eg_facts hc
    unfold GenBelow
    set T : Subgroup ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) :=
      ⨆ (S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom)))
        (_ : S ≤ R.Eg c ∧ Nat.card (R.Eg c) ≤ 3 * Nat.card S), c25Fix S with hT
    have hfix : ∀ x ∈ R.FixedSet c, x ∈ T.map MulAut.conj := by
      rintro x ⟨hxI, S, hSE, hS9, hSc⟩
      have hxr : x ∈ (MulAut.conj :
          ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) →* _).range := by
        have : R.Innr ≤ (MulAut.conj :
            ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) →* _).range := by
          rw [Realization.Innr, Subgroup.closure_le]
          rintro _ ⟨k, -, rfl⟩
          exact ⟨gk k, (hletR k).symm⟩
        exact this hxI
      obtain ⟨g, rfl⟩ := hxr
      refine ⟨g, ?_, rfl⟩
      have hgS : g ∈ c25Fix S := by
        intro s hs'
        have h1 := hSc s hs'
        have h2 : MulAut.conj (s g) = MulAut.conj g := by
          have := mulAut_mul_conj_eq s g
          rw [h1.eq] at this
          exact (mul_right_cancel this).symm
        exact hconjinj h2
      have hle : c25Fix S ≤ T := le_iSup₂_of_le S ⟨hSE, by rw [hEcard, hS9]⟩ le_rfl
      exact hle hgS
    have hclos : Subgroup.closure (R.FixedSet c) ≤ T.map MulAut.conj := by
      rw [Subgroup.closure_le]
      exact hfix
    have hgkT : ∀ k, k < 16 → gk k ∈ T := by
      intro k hk'
      obtain ⟨g, hg, hg'⟩ := hclos (hlett k hk')
      have : g = gk k := hconjinj (hg'.trans (hletR k))
      rw [← this]
      exact hg
    rw [← hclosure]
    exact (Subgroup.closure_le T).2 (by rintro _ ⟨k, hk', rfl⟩; exact hgkT k hk')
  obtain ⟨P, hPcard, hcover⟩ := sylow_spec R
  have hXcard : Nat.card (MulAut ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom)) =
      Nat.card ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) * 6 := by
    have hbij : Function.Bijective (fun p : ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) ×
        (kf ≃+* kf) => (MulAut.conj p.1 * fa p.2 :
          MulAut ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom))) := by
      constructor
      · intro p q hpq
        obtain ⟨r, -, hr⟩ := hunique (MulAut.conj p.1 * fa p.2)
        exact (hr p rfl).trans (hr q hpq).symm
      · intro α
        obtain ⟨p, hp, -⟩ := hunique α
        exact ⟨p, hp.symm⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, hcard6]
  have hv : (Nat.card (MulAut ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom))).factorization 3
      = 5 := by
    rw [hXcard, Nat.factorization_mul Nat.card_pos.ne' (by norm_num)]
    simp only [Finsupp.add_apply, hv3]
    have h6 : (6 : ℕ).factorization 3 = 1 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
      simp [Nat.Prime.factorization Nat.prime_two, Nat.Prime.factorization Nat.prime_three]
    rw [h6]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P0 : Sylow 3 (MulAut ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom)) :=
    Sylow.ofCard P (by rw [hPcard, hv])
  refine genBelow_of_covering (Set.range fun c : Fin 4 => R.Eg c) ?_ ?_
  · intro A hA
    obtain ⟨g, hle⟩ := exists_conj_le_sylow P0 A hA
    have hEA : IsElemAbelian 3 (A.map (MulAut.conj g).toMonoidHom) :=
      isElemAbelian_map _ (MulAut.conj g).injective hA
    obtain ⟨c, hc, g', hg'⟩ := hcover _ hle hEA
    refine ⟨R.Eg c, ⟨⟨c, hc⟩, rfl⟩, g' * g, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have := hg' ⟨(MulAut.conj g).toMonoidHom a, ⟨a, ha, rfl⟩, rfl⟩
    have e : (MulAut.conj (g' * g)).toMonoidHom a =
        (MulAut.conj g').toMonoidHom ((MulAut.conj g).toMonoidHom a) := by
      rw [map_mul]
      rfl
    rw [e]
    exact this
  · rintro _ ⟨c, rfl⟩
    exact hgen c c.2

end C0

end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
