module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.PhiRows
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.TwistedThree

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open TauCeti CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)

open CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator (PhiPlaneGenAt)


@[expose] def PlaneGen (Y : Type) [Group Y] (p : ℕ) : Prop :=
  ∀ E : Subgroup Y, CFSG.IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    Subgroup.closure {k : Y | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤

theorem planeGen_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {p : ℕ}
    [Fact p.Prime] (h : PlaneGen Y' p) : PlaneGen Y p := by
  intro E hE hcard
  refine closure_centralizers_transfer e E (h _ ?_ ?_)
  · have : CFSG.IsElementaryAbelian p E := hE
    refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
    · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
      have := congrArg (fun z : E => e.toMonoidHom (z : Y))
        (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
      refine Subtype.ext ?_
      change e a * e b = e b * e a
      simpa using this
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      rintro ⟨_, y, hy, rfl⟩
      refine Subtype.ext ?_
      change e.toMonoidHom y ^ p = 1
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) y hy, map_one]
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hcard

theorem isElementaryAbelian_map {X Z : Type*} [Group X] [Group Z] {p : ℕ} (f : X →* Z)
    {E : Subgroup X} (hE : CFSG.IsElementaryAbelian p E) :
    CFSG.IsElementaryAbelian p (E.map f) := by
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    have := congrArg (fun z : E => f (z : X))
      (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
    refine Subtype.ext ?_
    change f a * f b = f b * f a
    simpa using this
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    rintro ⟨_, y, hy, rfl⟩
    refine Subtype.ext ?_
    change f y ^ p = 1
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) y hy, map_one]

theorem planeGen_graphFixed
    {ℓ f p : ℕ} (hphi : PhiPlaneGenAt 1 p) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {X : Type} [Field X] [Finite X] (hX : Nat.card X = (ℓ ^ f) ^ 3) (σ : X ≃+* X)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1 * ((ℓ ^ f : ℕ) : ℤ) + 1) :
    PlaneGen (graphFixedRootGroup TwistTag.D4 X σ.toRingHom) p :=
  fun E hE hcard => hphi ℓ f hℓ hℓ2 hf X hX σ hσ hp hpℓ hd E hE hcard

section Even

theorem planeGen_even {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] {q : PrimePower} (hq : q.p = 2)
    (hext : ExtSeitzAtInnerFor (.trialityD4 q) fun _ => True)
    (hiso : IsoLie Y (.trialityD4 q)) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    PlaneGen Y p := by
  intro E hE hcard
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hnab : ∃ a b : Y, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    let : CommGroup Y := { ‹Group Y› with mul_comm := fun a b => hcomm a b }
    have hprime := IsSimpleGroup.prime_card (α := Y)
    have hpdvd : p ^ 2 ∣ Nat.card Y := hcard ▸ Subgroup.card_subgroup_dvd_card E
    have hp1 : p ∣ Nat.card Y := dvd_trans (dvd_pow_self p two_ne_zero) hpdvd
    rcases (Nat.dvd_prime hprime).1 hp1 with h1 | h1
    · exact (Fact.out : p.Prime).one_lt.ne' h1
    · rw [← h1] at hpdvd
      have := Nat.le_of_dvd (Fact.out : p.Prime).pos hpdvd
      nlinarith [hp5]
  have hinj := conj_injective_of_simple hnab
  let Ea : Subgroup (MulAut Y) := E.map (MulAut.conj : Y →* MulAut Y)
  have hEa : CFSG.IsElementaryAbelian p Ea := isElementaryAbelian_map _ hE
  have hEacard : Nat.card Ea = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj]; exact hcard
  have hinner : ∀ φ ∈ Ea, ∃ g : Y, φ = MulAut.conj g := by
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, rfl⟩
  have hpd : p ≠ (LieTypeIndex.trialityD4 q).characteristic := by
    intro h
    have h2 : (LieTypeIndex.trialityD4 q).characteristic = q.p := by simp
    have : p = 2 := by rw [h, h2, hq]
    omega
  have hx := hext Y hnab ⟨hv, ⟨e0⟩⟩ p (Fact.out) hp5 hpd
    trivial Ea hEa hEacard hinner
  rcases hx with hx | ⟨-, hd⟩
  · rw [eq_top_iff, ← hx]
    refine Subgroup.closure_mono ?_
    rintro k ⟨F, hFE, hF1, hfix⟩
    obtain ⟨⟨φ, hφF⟩, hφ1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hF1
    have hφ1 : φ ≠ 1 := fun h => hφ1' (Subtype.ext h)
    obtain ⟨x, hxE, hxφ⟩ := hFE hφF
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hφ1 (by rw [← hxφ]; simp)
    refine ⟨x, hxE, hx1, ?_⟩
    have h : φ k = k := hfix φ hφF
    rw [← hxφ] at h
    have h' : x * k * x⁻¹ = k := h
    calc k * x = x * k * x⁻¹ * x := by rw [h']
      _ = x * k := by group
  · rcases hd with hd | hd <;> exact absurd hd (by simp)

end Even

section IsoLie



theorem planeGen_of_isoLie {Y : Type} [Group Y] {q : PrimePower}
    (hiso : IsoLie Y (.trialityD4 q)) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ≠ q.p)
    (hdvd : (p : ℤ) ∣ (q.card : ℤ) ^ 2 + 1 * (q.card : ℤ) + 1)
    (hphi : q.p ≠ 2 → PhiPlaneGenAt 1 p)
    (hext : q.p = 2 → ExtSeitzAtInnerFor (.trialityD4 q) fun _ => True)
    (hfs : q.p = 2 → Finite Y ∧ IsSimpleGroup Y) :
    PlaneGen Y p := by
  by_cases hq : q.p = 2
  · obtain ⟨hfin, hsimp⟩ := hfs hq
    exact planeGen_even hq (hext hq) hiso hp5
  · obtain ⟨X, _, _, σ, hX, hσ, -, ⟨e⟩⟩ :=
      CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.exists_trialityD4_model_of_isoLie hiso
    have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
    rw [hqc] at hX hσ hdvd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    exact planeGen_of_mulEquiv e
      (planeGen_graphFixed (hphi hq) q.prime_p hq q.exponent_pos hX σ hσ (Fact.out) hpq hdvd)

end IsoLie

end CFSG.HardMathSupport.Malle.SeitzCube
