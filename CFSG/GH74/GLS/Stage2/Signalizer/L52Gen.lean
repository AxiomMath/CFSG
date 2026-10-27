module

public import CFSG.GH74.GLS.Stage2.Local.P34Comp
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeSylow
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.DisconnectedInvolutionGraph.Helpers CFSG.ABGLocalTools
open scoped commutatorElement

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_invariant_sylowOf_containing {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {B O Q : Subgroup G} (hBq : IsPGroup q ↥B) (hBO : B ≤ normalizer (O : Set G))
    (hOq : ¬ q ∣ Nat.card ↥O) (hQO : Q ≤ O) (hQp : IsPGroup p ↥Q)
    (hBQ : B ≤ normalizer (Q : Set G)) :
    ∃ P' : Subgroup G, IsSylowOf p P' O ∧ Q ≤ P' ∧ B ≤ normalizer (P' : Set G) := by
  classical
  let φ : ↥B →* MulAut ↥O := O.normalizerMonoidHom.comp (Subgroup.inclusion hBO)
  let _ : MulDistribMulAction ↥B ↥O := MulDistribMulAction.compHom ↥O φ
  have hQ'p : IsPGroup p ↥(Q.subgroupOf O) := hQp.comap_subtype
  have hsmul : ∀ (b : ↥B) (x : ↥O), ((b • x : ↥O) : G) = (b : G) * (x : G) * (b : G)⁻¹ := by
    intro b x
    change (((O.normalizerMonoidHom) (Subgroup.inclusion hBO b)) x : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hinv : InvariantSubgroup (A := ↥B) (Q.subgroupOf O) := by
    intro b x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmul]
    exact (Subgroup.mem_normalizer_iff.1 (hBQ b.2) _).1 hx
  obtain ⟨sylow, hQle, hsyinv⟩ := coprime_pgroup_invariant_sylow_containment q p hBq hOq
    (Q.subgroupOf O) hQ'p hinv
  refine ⟨(sylow : Subgroup O).map O.subtype, ⟨sylow, rfl⟩, ?_, ?_⟩
  · intro x hx
    have hx' : (⟨x, hQO hx⟩ : ↥O) ∈ (sylow : Subgroup ↥O) := hQle (Subgroup.mem_subgroupOf.2 hx)
    exact ⟨⟨x, hQO hx⟩, hx', rfl⟩
  · rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨y, hy, rfl⟩
    have := hsyinv ⟨b, hb⟩ y hy
    exact ⟨_, this, hsmul ⟨b, hb⟩ y⟩

end Sylow

section Layer

theorem centralizes_centralizer_layer {X : Type} [Group X] [Finite X] (hO : pPrimeCore 2 X = ⊥)
    {a : X} {m : ℕ} (hm : Odd m) (ham : a ^ m = 1) (hD : ∀ d ∈ pCore 2 X, d * a = a * d) :
    ∀ x ∈ centralizer ((layer X : Subgroup X) : Set X), x * a = a * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : (layer X).Normal := by
    have : (layer X).Characteristic := LocalCores.layer_characteristic (G := X)
    infer_instance
  have hFD : fittingSubgroup X ≤ pCore 2 X := (Fitting_eq_pcore X 2 hO).le
  intro x hx
  have hxE : ∀ e ∈ layer X, x * e * x⁻¹ = e := by
    intro e he
    have := Subgroup.mem_centralizer_iff.mp hx e he
    rw [← this]; group
  set xa : X := a⁻¹ * x * a with hxa
  set f : X := x⁻¹ * xa with hf
  have hagree : ∀ y ∈ generalizedFitting X, xa * y * xa⁻¹ = x * y * x⁻¹ := by
    have hle : generalizedFitting X ≤ MonoidHom.eqLocus (MulAut.conj xa).toMonoidHom
        (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · show xa * y * xa⁻¹ = x * y * x⁻¹
        have hyD : y ∈ pCore 2 X := hFD hy
        have h1 : a * y * a⁻¹ = y := by rw [← hD y hyD]; group
        have hxyx : x * y * x⁻¹ ∈ pCore 2 X :=
          hFD (fittingSubgroup_normal.conj_mem y hy x)
        have h2 : a⁻¹ * (x * y * x⁻¹) * a = x * y * x⁻¹ := by
          have := hD _ hxyx
          calc a⁻¹ * (x * y * x⁻¹) * a = a⁻¹ * (a * (x * y * x⁻¹)) := by rw [← this]; group
            _ = x * y * x⁻¹ := by group
        calc xa * y * xa⁻¹ = a⁻¹ * (x * (a * y * a⁻¹) * x⁻¹) * a := by simp only [hxa]; group
          _ = a⁻¹ * (x * y * x⁻¹) * a := by rw [h1]
          _ = x * y * x⁻¹ := h2
      · show xa * y * xa⁻¹ = x * y * x⁻¹
        have hy' : a * y * a⁻¹ ∈ layer X := by simpa using hE.conj_mem y hy a
        calc xa * y * xa⁻¹ = a⁻¹ * (x * (a * y * a⁻¹) * x⁻¹) * a := by simp only [hxa]; group
          _ = a⁻¹ * (a * y * a⁻¹) * a := by rw [hxE _ hy']
          _ = y := by group
          _ = x * y * x⁻¹ := (hxE y hy).symm
    intro y hy
    exact hle hy
  have hfc : f ∈ centralizer ((generalizedFitting X : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hagree y hy
    calc y * f = (x⁻¹ * (x * y * x⁻¹) * x) * f := by group
      _ = (x⁻¹ * (xa * y * xa⁻¹) * x) * f := by rw [h]
      _ = f * y := by simp only [hf]; group
  have hfF : f ∈ generalizedFitting X := centralizer_generalizedFitting_le X hfc
  have hfD : f ∈ pCore 2 X := by
    have hfs : f ∈ fittingSubgroup X ⊔ layer X := hfF
    rw [Subgroup.mem_sup_of_normal_left] at hfs
    obtain ⟨u, hu, e, he, hue⟩ := hfs
    have hu_comm : ∀ l ∈ layer X, u * l = l * u := by
      intro l hl
      have h1 : ⁅u, l⁆ ∈ ⁅fittingSubgroup X, layer X⁆ := Subgroup.commutator_mem_commutator hu hl
      rw [LocalCores.fitting_layer_commute, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hf_comm : ∀ l ∈ layer X, l * f = f * l := fun l hl =>
      Subgroup.mem_centralizer_iff.mp hfc l (Subgroup.mem_sup_right hl)
    have he_comm : ∀ l ∈ layer X, l * e = e * l := by
      intro l hl
      have he' : e = u⁻¹ * f := by rw [← hue]; group
      have hl' := hu_comm l hl
      have hlf := hf_comm l hl
      calc l * e = l * (u⁻¹ * f) := by rw [he']
        _ = (l * u⁻¹) * f := by group
        _ = (u⁻¹ * l) * f := by
            have : l * u⁻¹ = u⁻¹ * l := by
              calc l * u⁻¹ = u⁻¹ * (u * l) * u⁻¹ := by group
                _ = u⁻¹ * (l * u) * u⁻¹ := by rw [hl']
                _ = u⁻¹ * l := by group
            rw [this]
        _ = u⁻¹ * (l * f) := by group
        _ = u⁻¹ * (f * l) := by rw [hlf]
        _ = (u⁻¹ * f) * l := by group
        _ = e * l := by rw [he']
    have hecen : e ∈ (center ↥(layer X)).map (layer X).subtype :=
      ⟨⟨e, he⟩, Subgroup.mem_center_iff.2 (fun g => Subtype.ext (he_comm (g : X) g.2)), rfl⟩
    have heD : e ∈ pCore 2 X :=
      hFD (CFSG.GH74.GLS.Stage2.Local.P34.center_layer_le_fitting (Y := X) hecen)
    rw [← hue]
    exact (pCore 2 X).mul_mem (hFD hu) heD
  have hfa : f * a = a * f := hD f hfD
  have hxaf : xa = x * f := by simp only [hxa, hf]; group
  have hcoc : ∀ n : ℕ, (a⁻¹) ^ n * x * a ^ n = x * f ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hfa' : Commute a f := hfa.symm
      have hc : Commute a (f ^ n) := Commute.pow_right hfa' n
      calc (a⁻¹) ^ (n + 1) * x * a ^ (n + 1) = a⁻¹ * ((a⁻¹) ^ n * x * a ^ n) * a := by
            rw [pow_succ' a⁻¹ n, pow_succ a n]; group
        _ = a⁻¹ * (x * f ^ n) * a := by rw [ih]
        _ = (a⁻¹ * x * a) * (a⁻¹ * f ^ n * a) := by group
        _ = xa * f ^ n := by
            have : a⁻¹ * f ^ n * a = f ^ n := by
              rw [mul_assoc, ← hc.eq]; group
            rw [this]
        _ = x * f ^ (n + 1) := by rw [hxaf, pow_succ' f n]; group
  have hfm : f ^ m = 1 := by
    have h := hcoc m
    rw [inv_pow, ham, inv_one, one_mul, mul_one] at h
    exact (mul_eq_left.mp h.symm)
  have hf1 : f = 1 := by
    obtain ⟨j, hj⟩ := (pCore_isPGroup (p := 2) (G := X)) ⟨f, hfD⟩
    have hj' : f ^ (2 ^ j) = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)
    have := (pow_gcd_eq_one (a := f)).mpr ⟨hj', hfm⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hxa1 : a⁻¹ * x * a = x := by
    have : xa = x := by rw [hxaf, hf1, mul_one]
    simpa [hxa] using this
  calc x * a = a * (a⁻¹ * x * a) := by group
    _ = a * x := by rw [hxa1]

end Layer

end CFSG.GH74.GLS.Stage2.Signalizer
