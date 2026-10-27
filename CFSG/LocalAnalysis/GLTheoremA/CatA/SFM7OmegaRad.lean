module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.FixedSpace
public import CFSG.RankThree.OrthogonalInvolutions.OmegaClasses

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM7Omega


open Module QuadraticMap
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open CFSG.RankThree.OrthogonalInvolutions

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  [FiniteDimensional (ZMod 2) V]

@[expose] def radSing (Q : QuadraticForm (ZMod 2) V) (T : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Submodule (ZMod 2) V where
  carrier := {x | x ∈ fixSub T ∧ x ∈ perpSub Q (fixSub T) ∧ Q x = 0}
  add_mem' := by
    rintro x y ⟨hxW, hxP, hxQ⟩ ⟨hyW, hyP, hyQ⟩
    have hp : polar Q x y = 0 := hxP y hyW
    refine ⟨add_mem hxW hyW, add_mem hxP hyP, ?_⟩
    calc Q (x + y) = Q x + Q y + polar Q x y := QuadraticMap.map_add Q x y
      _ = 0 := by rw [hxQ, hyQ, hp]; norm_num
  zero_mem' := ⟨zero_mem _, zero_mem _, QuadraticMap.map_zero Q⟩
  smul_mem' := by
    rintro c x ⟨hxW, hxP, hxQ⟩
    have hc : c = 0 ∨ c = 1 := by
      revert c
      decide
    rcases hc with rfl | rfl
    · simp
    · simpa [hxW, hxP, hxQ]

theorem mem_radSing {Q : QuadraticForm (ZMod 2) V} {T : Subgroup (V ≃ₗ[ZMod 2] V)}
    {x : V} : x ∈ radSing Q T ↔ x ∈ fixSub T ∧ x ∈ perpSub Q (fixSub T) ∧ Q x = 0 :=
  Iff.rfl

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
theorem two_mul_finrank_radSing_le (Q : QuadraticForm (ZMod 2) V)
    (hQ : (polarBilin Q).Nondegenerate) (T : Subgroup (V ≃ₗ[ZMod 2] V)) :
    2 * finrank (ZMod 2) (radSing Q T) ≤ finrank (ZMod 2) V :=
  CFSG.RankThree.OrthogonalInvolutions.two_mul_finrank_le_of_forall_eq_zero hQ
    fun x hx => (mem_radSing.mp hx).2.2

theorem apply_mem_radSing {Q : QuadraticForm (ZMod 2) V} {T : Subgroup (V ≃ₗ[ZMod 2] V)}
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgT : g ∈ Subgroup.normalizer (T : Set (V ≃ₗ[ZMod 2] V))) {x : V}
    (hx : x ∈ radSing Q T) : g x ∈ radSing Q T := by
  obtain ⟨hxW, hxP, hxQ⟩ := mem_radSing.mp hx
  have hconj : ∀ h ∈ T, g * h * g⁻¹ ∈ T := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp hgT h).mp hh
  have hconj' : ∀ h ∈ T, g⁻¹ * h * g ∈ T := fun h hh =>
    (Subgroup.mem_normalizer_iff''.mp hgT h).mp hh
  have hW : g x ∈ fixSub T := by
    rw [mem_fixSub]
    intro h hh
    have hx' : (g⁻¹ * h * g) x = x := (mem_fixSub.mp hxW) _ (hconj' h hh)
    calc h (g x) = (h * g) x := by rw [LinearEquiv.mul_apply]
      _ = (g * (g⁻¹ * h * g)) x := by rw [show h * g = g * (g⁻¹ * h * g) by group]
      _ = g ((g⁻¹ * h * g) x) := by rw [LinearEquiv.mul_apply]
      _ = g x := by rw [hx']
  have hP : g x ∈ perpSub Q (fixSub T) := by
    rw [mem_perpSub]
    intro y hy
    have hgy : g⁻¹ y ∈ fixSub T := by
      rw [mem_fixSub]
      intro h hh
      have hy' : (g * h * g⁻¹) y = y := (mem_fixSub.mp hy) _ (hconj h hh)
      calc h (g⁻¹ y) = (h * g⁻¹) y := by rw [LinearEquiv.mul_apply]
        _ = (g⁻¹ * (g * h * g⁻¹)) y := by
          rw [show h * g⁻¹ = g⁻¹ * (g * h * g⁻¹) by group]
        _ = g⁻¹ ((g * h * g⁻¹) y) := by rw [LinearEquiv.mul_apply]
        _ = g⁻¹ y := by rw [hy']
    have hzero : polar Q x (g⁻¹ y) = 0 := (mem_perpSub.mp hxP) _ hgy
    calc polar Q (g x) y = polar Q (g x) (g (g⁻¹ y)) := by simp
      _ = polar Q x (g⁻¹ y) := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hg x _
      _ = 0 := hzero
  refine mem_radSing.mpr ⟨hW, hP, ?_⟩
  rw [CFSG.ClassicalGroups.Orthogonal.map_of_mem hg x]
  exact hxQ

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
theorem radSing_ne_bot (Q : QuadraticForm (ZMod 2) V)
    (hQ : (polarBilin Q).Nondegenerate) {T : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hT : T ≤ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ)
    (h2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) : radSing Q T ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Submodule (ZMod 2) V := fixSub T with hWdef
  set Wp : Submodule (ZMod 2) V := perpSub Q W with hWpdef
  set R : Submodule (ZMod 2) V := W ⊓ Wp with hRdef
  have hiso : ∀ t ∈ T, (t : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun t ht => CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le Q hQ (hT ht)
  have hrefl : (polarBilin Q).IsRefl := (QuadraticMap.isSymm_polarBilin Q).isRefl
  have horth : ∀ U : Submodule (ZMod 2) V,
      perpSub Q U = LinearMap.BilinForm.orthogonal (polarBilin Q) U := by
    intro U
    ext x
    rw [mem_perpSub, LinearMap.BilinForm.mem_orthogonal_iff]
    exact forall₂_congr fun w _ => by rw [polarBilin_apply_apply, polar_comm]
  have hcardV : Nat.card V = 2 ^ finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hVnt : Nontrivial V := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hT1
    rw [Subgroup.eq_bot_iff_forall]
    intro t _ht
    ext v
    exact Subsingleton.elim _ _
  have hVdvd : 2 ∣ Nat.card V := by
    rw [hcardV]
    haveI : Nontrivial V := hVnt
    have hpos : 0 < finrank (ZMod 2) V := Module.finrank_pos
    obtain ⟨n, hn⟩ : ∃ n, finrank (ZMod 2) V = n + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hn, pow_succ]
    exact dvd_mul_left 2 (2 ^ n)
  have hWne : W ≠ ⊥ := by
    obtain ⟨v, hvfix, hv0⟩ := h2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      V hVdvd (a := (0 : V)) (by
        rw [MulAction.mem_fixedPoints]
        intro t
        simp [LinearEquiv.smul_def])
    intro hbot
    have hvW : v ∈ W := by
      rw [hWdef, mem_fixSub]
      intro t ht
      simpa [Subgroup.smul_def, LinearEquiv.smul_def] using
        (MulAction.mem_fixedPoints.mp hvfix) ⟨t, ht⟩
    rw [hbot, Submodule.mem_bot] at hvW
    exact hv0 hvW.symm
  have hWtop : W ≠ ⊤ := by
    intro htop
    apply hT1
    rw [Subgroup.eq_bot_iff_forall]
    intro t ht
    ext v
    have hvW : v ∈ W := by rw [htop]; trivial
    exact (mem_fixSub.mp (by rwa [hWdef] at hvW)) t ht
  have hdouble : perpSub Q Wp = W := by
    rw [hWpdef]
    simp only [horth]
    exact LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl W
  have hWpne : Wp ≠ ⊥ := by
    intro hbot
    apply hWtop
    rw [← hdouble, hbot]
    simp only [horth]
    exact LinearMap.BilinForm.orthogonal_bot
  have hWp_mem : ∀ t ∈ T, ∀ x ∈ Wp, (t : V ≃ₗ[ZMod 2] V) x ∈ Wp := by
    intro t ht x hx
    rw [hWpdef, mem_perpSub] at hx ⊢
    intro y hy
    have hyW : y ∈ fixSub T := by rwa [hWdef] at hy
    have hty : (t : V ≃ₗ[ZMod 2] V) y = y := hyW t ht
    calc polar Q ((t : V ≃ₗ[ZMod 2] V) x) y
        = polar Q ((t : V ≃ₗ[ZMod 2] V) x) ((t : V ≃ₗ[ZMod 2] V) y) := by rw [hty]
      _ = polar Q x y := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem (hiso t ht) x y
      _ = 0 := hx y hy
  let actW : T →* Equiv.Perm Wp :=
    { toFun := fun t =>
        { toFun := fun x => ⟨(t : V ≃ₗ[ZMod 2] V) (x : V), hWp_mem t t.2 x x.2⟩
          invFun := fun x =>
            ⟨(t⁻¹ : V ≃ₗ[ZMod 2] V) (x : V), hWp_mem t⁻¹ (inv_mem t.2) x x.2⟩
          left_inv := by
            intro x
            ext
            simpa using LinearEquiv.apply_symm_apply (t : V ≃ₗ[ZMod 2] V) (x : V)
          right_inv := by
            intro x
            ext
            simpa using LinearEquiv.symm_apply_apply (t : V ≃ₗ[ZMod 2] V) (x : V) }
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro s t
        ext x
        simp [LinearEquiv.mul_apply, Subgroup.coe_mul] }
  letI : MulAction T Wp := MulAction.compHom Wp actW
  have hWp_even : 2 ∣ Nat.card Wp := by
    haveI : FiniteDimensional (ZMod 2) Wp := Module.Finite.of_finite
    have hcard : Nat.card Wp = 2 ^ finrank (ZMod 2) Wp := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    rw [hcard]
    have hpos : 0 < finrank (ZMod 2) Wp :=
      lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.mpr hWpne)
    obtain ⟨n, hn⟩ : ∃ n, finrank (ZMod 2) Wp = n + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hn, pow_succ]
    exact dvd_mul_left 2 (2 ^ n)
  have hRne : R ≠ ⊥ := by
    intro hR
    obtain ⟨x, hxfix, hx0⟩ := h2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      Wp hWp_even (a := (0 : Wp)) (by
        rw [MulAction.mem_fixedPoints]
        intro t
        apply Subtype.ext
        change (t : V ≃ₗ[ZMod 2] V) (0 : V) = 0
        exact map_zero _)
    have hxW : (x : V) ∈ W := by
      rw [hWdef, mem_fixSub]
      intro t ht
      have h := (MulAction.mem_fixedPoints.mp hxfix) ⟨t, ht⟩
      simpa [actW, MulAction.compHom_smul_def, Equiv.Perm.smul_def] using
        congrArg (fun z : Wp => (z : V)) h
    have hxR : (x : V) ∈ R := by
      rw [hRdef]
      exact ⟨hxW, x.2⟩
    rw [hR, Submodule.mem_bot] at hxR
    exact hx0 (Subtype.ext hxR.symm)
  intro hrad
  have hz2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
    intro c
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  let qR : R →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => Q (x : V)
      map_add' := by
        intro x y
        change Q ((x : V) + (y : V)) = Q (x : V) + Q (y : V)
        have hp : polar Q (x : V) (y : V) = 0 := (mem_perpSub.mp x.2.2) (y : V) y.2.1
        calc Q ((x : V) + (y : V))
            = Q (x : V) + Q (y : V) + polar Q (x : V) (y : V) :=
              QuadraticMap.map_add Q (x : V) (y : V)
          _ = Q (x : V) + Q (y : V) := by rw [hp, add_zero]
      map_smul' := by
        intro c x
        change Q (c • (x : V)) = c • Q (x : V)
        rcases hz2 c with rfl | rfl
        · simp
        · simp }
  have hker : LinearMap.ker qR = ⊥ := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro hx
      apply Subtype.ext
      have hxrad : (x : V) ∈ radSing Q T := by
        rw [mem_radSing]
        exact ⟨x.2.1, x.2.2, hx⟩
      rw [hrad, Submodule.mem_bot] at hxrad
      exact hxrad
    · intro hx
      rw [hx]
      simp
  have hRdim_le : finrank (ZMod 2) R ≤ 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker qR
    rw [hker, finrank_bot, add_zero] at h
    rw [← h]
    calc finrank (ZMod 2) (LinearMap.range qR)
        ≤ finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (ZMod 2)) :=
          Submodule.finrank_mono le_top
      _ = 1 := by rw [finrank_top, Module.finrank_self]
  have hRdim : finrank (ZMod 2) R = 1 := by
    have hge : 1 ≤ finrank (ZMod 2) R := Submodule.one_le_finrank_iff.mpr hRne
    omega
  obtain ⟨r, hrR, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRne
  have hrW : r ∈ W := by rw [hRdef] at hrR; exact hrR.1
  have hrWp : r ∈ Wp := by rw [hRdef] at hrR; exact hrR.2
  have hRspan : R = Submodule.span (ZMod 2) {(r : V)} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hRdim hrR (by simpa using hr0)
  have hrQ0 : Q r ≠ 0 := by
    intro h0
    have : r ∈ radSing Q T := mem_radSing.mpr ⟨hrW, hrWp, h0⟩
    rw [hrad, Submodule.mem_bot] at this
    exact hr0 this
  have hrQ : Q r = 1 := by
    rcases hz2 (Q r) with h | h
    · exact absurd h hrQ0
    · exact h
  have hWple : finrank (ZMod 2) Wp ≤ 1 := by
    by_contra hle
    push Not at hle
    have hk : 2 ≤ finrank (ZMod 2) Wp := hle
    let rWp : Wp := ⟨r, hrWp⟩
    let Y : Type := {x : Wp // Q (x : V) = 0}
    let Z : Type := {x : Wp // ¬ Q (x : V) = 0}
    have htrans : Y ≃ Z :=
      { toFun := fun y =>
          ⟨⟨(y.1 : Wp) + rWp, add_mem y.1.2 rWp.2⟩, by
            intro h0
            change Q ((y.1 : V) + r) = 0 at h0
            have hp : polar Q (y.1 : V) r = 0 := (mem_perpSub.mp y.1.2) r hrW
            rw [QuadraticMap.map_add Q (y.1 : V) r, y.2, hrQ, hp] at h0
            norm_num at h0⟩
        invFun := fun z =>
          ⟨⟨(z.1 : Wp) + rWp, add_mem z.1.2 rWp.2⟩, by
            have hzQ : Q (z.1 : V) = 1 := by
              rcases hz2 (Q (z.1 : V)) with h | h
              · exact absurd h z.2
              · exact h
            have hp : polar Q (z.1 : V) r = 0 := (mem_perpSub.mp z.1.2) r hrW
            change Q ((z.1 : V) + r) = 0
            rw [QuadraticMap.map_add Q (z.1 : V) r, hzQ, hrQ, hp]
            norm_num
            exact ZMod.natCast_self 2⟩
        left_inv := by
          intro y
          ext
          dsimp only
          have hr2 : ((rWp : Wp) : V) + ((rWp : Wp) : V) = 0 := by
            rw [← two_smul (ZMod 2) ((rWp : Wp) : V)]
            rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_smul]
          rw [add_assoc, hr2, add_zero]
        right_inv := by
          intro z
          ext
          dsimp only
          have hr2 : ((rWp : Wp) : V) + ((rWp : Wp) : V) = 0 := by
            rw [← two_smul (ZMod 2) ((rWp : Wp) : V)]
            rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_smul]
          rw [add_assoc, hr2, add_zero] }
    haveI : FiniteDimensional (ZMod 2) Wp := Module.Finite.of_finite
    have hcardWp : Nat.card Wp = 2 ^ finrank (ZMod 2) Wp := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have hWpcard : Nat.card Wp = Nat.card Y + Nat.card Z := by
      have e : Y ⊕ Z ≃ Wp := Equiv.sumCompl (fun x : Wp => Q (x : V) = 0)
      rw [← Nat.card_congr e, Nat.card_sum]
    have hYZ : Nat.card Z = Nat.card Y := (Nat.card_congr htrans).symm
    have h2Y : 2 * Nat.card Y = Nat.card Wp := by
      rw [hWpcard, hYZ]
      omega
    have h4 : 2 * 2 ∣ Nat.card Wp := by
      rw [hcardWp]
      obtain ⟨m, hm⟩ : ∃ m, finrank (ZMod 2) Wp = m + 2 :=
        ⟨finrank (ZMod 2) Wp - 2, by omega⟩
      rw [hm, pow_add]
      exact ⟨2 ^ m, by ring⟩
    have hYdvd : 2 ∣ Nat.card Y := by
      have h4' : 2 * 2 ∣ 2 * Nat.card Y := by
        rw [h2Y]
        exact h4
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h4'
    have hYmem : ∀ (t : T) (y : Y), Q ((t : V ≃ₗ[ZMod 2] V) (y.1 : V)) = 0 := by
      intro t y
      rw [CFSG.ClassicalGroups.Orthogonal.map_of_mem (hiso t t.2) (y.1 : V)]
      exact y.2
    have hYWp : ∀ (t : T) (y : Y), (t : V ≃ₗ[ZMod 2] V) (y.1 : V) ∈ Wp :=
      fun t y => hWp_mem t t.2 (y.1 : V) y.1.2
    let actY : T →* Equiv.Perm Y :=
      { toFun := fun t =>
          { toFun := fun y => ⟨⟨(t : V ≃ₗ[ZMod 2] V) (y.1 : V), hYWp t y⟩, hYmem t y⟩
            invFun := fun y =>
              ⟨⟨(t⁻¹ : V ≃ₗ[ZMod 2] V) (y.1 : V), hYWp t⁻¹ y⟩, hYmem t⁻¹ y⟩
            left_inv := by
              intro y
              ext
              simpa using LinearEquiv.apply_symm_apply (t : V ≃ₗ[ZMod 2] V) (y.1 : V)
            right_inv := by
              intro y
              ext
              simpa using LinearEquiv.symm_apply_apply (t : V ≃ₗ[ZMod 2] V) (y.1 : V) }
        map_one' := by
          ext y
          simp
        map_mul' := by
          intro s t
          ext y
          simp [LinearEquiv.mul_apply, Subgroup.coe_mul] }
    letI : MulAction T Y := MulAction.compHom Y actY
    let zY : Y := ⟨0, by simp⟩
    obtain ⟨y, hyfix, hyne0⟩ := h2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      Y hYdvd (a := zY) (by
        rw [MulAction.mem_fixedPoints]
        intro t
        apply Subtype.ext
        apply Subtype.ext
        change (t : V ≃ₗ[ZMod 2] V) (0 : V) = 0
        exact map_zero _)
    have hyW : ((y.1 : Wp) : V) ∈ W := by
      rw [hWdef, mem_fixSub]
      intro t ht
      have h := (MulAction.mem_fixedPoints.mp hyfix) ⟨t, ht⟩
      simpa [actY, MulAction.compHom_smul_def, Equiv.Perm.smul_def] using
        congrArg (fun z : Y => ((z.1 : Wp) : V)) h
    have hyne : ((y.1 : Wp) : V) ≠ 0 := by
      intro h0
      apply hyne0
      ext
      exact h0.symm
    have hyR : ((y.1 : Wp) : V) ∈ R := by
      rw [hRdef]
      exact ⟨hyW, y.1.2⟩
    rw [hRspan, Submodule.mem_span_singleton] at hyR
    obtain ⟨c, hc⟩ := hyR
    rcases hz2 c with rfl | rfl
    · rw [zero_smul] at hc
      exact hyne hc.symm
    · rw [one_smul] at hc
      have hq := y.2
      rw [← hc, hrQ] at hq
      exact one_ne_zero hq
  have hWpdim : finrank (ZMod 2) Wp = 1 := by
    have hge : 1 ≤ finrank (ZMod 2) Wp := Submodule.one_le_finrank_iff.mpr hWpne
    omega
  have hWpspan : Wp = Submodule.span (ZMod 2) {(r : V)} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hWpdim hrWp hr0
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
  let tV : V ≃ₗ[ZMod 2] V := (t : V ≃ₗ[ZMod 2] V)
  have htV1 : tV ≠ 1 := fun h => ht1 (Subtype.ext h)
  have htEven : Even (finrank (ZMod 2) (commSpace tV)) :=
    (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp (hT t.2)).2
  have hcommspan : commSpace tV ≤ Submodule.span (ZMod 2) {(r : V)} := by
    intro x hx
    obtain ⟨v, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hx
    have hxWp : tV v - v ∈ Wp := by
      rw [hWpdef, mem_perpSub]
      intro y hy
      have hyW : y ∈ fixSub T := by rwa [hWdef] at hy
      have hty : tV y = y := hyW t t.2
      calc polar Q (tV v - v) y
          = polar Q (tV v) y - polar Q v y := by rw [QuadraticMap.polar_sub_left]
        _ = polar Q (tV v) (tV y) - polar Q v y := by rw [hty]
        _ = polar Q v y - polar Q v y := by
            rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
              (show tV ∈ TauCeti.QuadraticMap.orthogonalGroup Q from hiso t t.2)]
        _ = 0 := sub_self _
    rwa [hWpspan] at hxWp
  have hcomm_le : finrank (ZMod 2) (commSpace tV) ≤ 1 := by
    have hmono := Submodule.finrank_mono hcommspan
    have hspan : finrank (ZMod 2) (Submodule.span (ZMod 2) {(r : V)}) = 1 := by
      simpa using finrank_span_singleton (K := ZMod 2) hr0
    rwa [hspan] at hmono
  have hcomm_ge : 1 ≤ finrank (ZMod 2) (commSpace tV) :=
    CFSG.RankThree.OrthogonalInvolutions.one_le_finrank_commSpace htV1
  have hcommdim : finrank (ZMod 2) (commSpace tV) = 1 := by omega
  obtain ⟨a, ha⟩ := htEven
  rw [hcommdim] at ha
  omega

end CFSG.LocalAnalysis.GLTheoremA.SFM7Omega
