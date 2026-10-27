module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55G2TM
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55G2NT
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Field
public import CFSG.LieType.Chevalley.DiagonalFieldActorData

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.IVK.Proofs2
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartTwo.KFacts
  CFSG.GH74.GLS.Stage2.Bender.Thm1

section Pure

variable {K : Type} [Field K]

def g2Tup (c : Kˣ) : Fin Tag.G2.rank → Kˣ := fun i => if (i : ℕ) = 0 then c else 1

theorem g2Tup_one : g2Tup (1 : Kˣ) = 1 := by
  funext i
  fin_cases i <;> simp [g2Tup]

theorem g2Tup_mul (c c' : Kˣ) : g2Tup (c * c') = g2Tup c * g2Tup c' := by
  funext i
  fin_cases i <;> simp [g2Tup]

end Pure

section Cert


variable {K : Type} [Field K]

theorem rootDiagUnit_g2_mem (a : Fin Tag.G2.rank → Kˣ) :
    rootDiagUnit Tag.G2 a ∈ adjointGroup Tag.G2 K := by
  obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner Tag.G2 (Or.inl rfl) K
  exact (hrest B hB a).2.2.1

noncomputable def g2Tor : Kˣ →* adjointGroup Tag.G2 K where
  toFun c := ⟨rootDiagUnit Tag.G2 (g2Tup c), rootDiagUnit_g2_mem _⟩
  map_one' := Subtype.ext (by simp [g2Tup_one, rootDiagUnit_one])
  map_mul' c c' := Subtype.ext (by simp [g2Tup_mul, rootDiagUnit_mul])

theorem g2Tor_injective : Function.Injective (g2Tor (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have h1 : rootDiagUnit Tag.G2 (g2Tup c) = 1 := congrArg Subtype.val hc
  have h2 := (root_diagonal_conjugation Tag.G2 K (g2Tup c)).1 ⟨0, by decide⟩ 1
  rw [h1] at h2
  simp only [one_mul, inv_one, mul_one] at h2
  have h3 : xOp Tag.G2 K ⟨0, by decide⟩ 1 =
      xOp Tag.G2 K ⟨0, by decide⟩ (g2Tup c ⟨0, by decide⟩ * 1) := by
    have := congrArg (fun u : ModGL Tag.G2 K => (u : Module.End K (RootModule Tag.G2 K))) h2
    simpa [coe_xUnit] using this
  have h4 := xOp_injective _ h3
  have h5 : ((g2Tup c ⟨0, by decide⟩ : Kˣ) : K) = 1 := by simpa using h4.symm
  exact Units.ext (by simpa [g2Tup] using h5)

theorem g2FieldHom_g2Tor [Finite K] (σ : K ≃+* K) (c : Kˣ) :
    g2FieldHom K σ (g2Tor c) = g2Tor (Units.map σ.toRingHom.toMonoidHom c) := by
  refine Subtype.ext ?_
  rw [coe_g2FieldHom]
  show Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.G2 (g2Tup c)) = _
  rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv]
  congr 1
  funext i
  fin_cases i <;> simp [g2Tup]

theorem outerFalse_g2_native [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) : OuterFalse p (adjointGroup Tag.G2 K) := by
  intro α hαinn hαp _ hHH
  have : Fact p.Prime := ⟨hp⟩
  have hα1 : α ≠ 1 := by
    rintro rfl
    exact hαinn ⟨1, by simp⟩
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  obtain ⟨hpf, i, δ, τ, hτ, hτord, hδ⟩ :=
    g2_field_descent hp hp2 hf K hK hp (hp.odd_of_ne_two hp2) hord hαinn
  have hi : ¬ p ∣ i := by
    intro hdvd
    have hαi : α ^ i = 1 := by
      obtain ⟨m, rfl⟩ := hdvd
      rw [pow_mul, hαp, one_pow]
    have h1 : g2FieldHom K τ = 1 := by rw [← hδ, hαi]; simp
    have hτ1 : τ = 1 := g2FieldHom_faithful hp hp2 hf K hK τ ⟨1, by rw [h1]; simp⟩
    rw [hτ1, orderOf_one] at hτord
    exact hp.one_lt.ne hτord
  have hHHi := hh_pow_of_coprime hp hαp hi hHH
  obtain ⟨e, he⟩ := hpf
  have hfe : f / p = e := by rw [he]; exact Nat.mul_div_cancel_left e hp.pos
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      omega
    · exact h
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq0odd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hq03 : 3 ≤ p ^ e := hp3.trans (Nat.le_self_pow (by omega) p)
  have hpq0 : p ∣ p ^ e := dvd_pow_self p (by omega)
  obtain ⟨r, hr, hr2, hrp, hrdvd, hrnd⟩ :=
    exists_prime_dvd_pow_sub_one_not_dvd hp hp2 hpq0 hq03 hq0odd
  have hunits : Nat.card Kˣ = (p ^ e) ^ p - 1 := by
    rw [Nat.card_units, hK, he, ← pow_mul, mul_comm]
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' r (hunits ▸ hrdvd)
  have hot : orderOf (g2Tor c) = r := by
    rw [orderOf_injective g2Tor g2Tor_injective c]
    exact hc
  have hft : g2FieldHom K τ (g2Tor c) = (g2Tor c) ^ (p ^ e) := by
    rw [g2FieldHom_g2Tor, ← map_pow]
    congr 1
    apply Units.ext
    simp [hτ, hfe]
  have hne : g2FieldHom K τ (g2Tor c) ≠ g2Tor c := by
    intro h
    rw [hft] at h
    have h1 : (g2Tor c) ^ (p ^ e - 1) = 1 := by
      have h2 : (g2Tor c) ^ (p ^ e - 1) * g2Tor c = 1 * g2Tor c := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul]
        exact h
      exact mul_right_cancel h2
    exact hrnd (hot ▸ orderOf_dvd_of_pow_eq_one h1)
  have hα' : α ^ i = δ⁻¹ * g2FieldHom K τ * δ⁻¹⁻¹ := by
    rw [← hδ]
    group
  exact false_of_torus_moved_pow hα' hr hr2 hrp hot hft hne hHHi

end Cert

section Model


theorem outerFalse_g2 {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hm : LieModel Y .G2 0 p f) : OuterFalse p Y := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hm
  exact OuterFalse.of_mulEquiv e (outerFalse_g2_native hp hp2 hf hcard)

end Model

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
