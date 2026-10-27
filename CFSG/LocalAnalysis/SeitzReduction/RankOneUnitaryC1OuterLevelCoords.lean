module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Stage

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

theorem outerLevel_exists_field_of_transitive {M : Type} [AddCommGroup M] [Finite M]
    (h2 : ∀ m : M, m + m = 0) (φ : AddMonoid.End M) {a₀ : M} (ha₀ : a₀ ≠ 0)
    (htrans : ∀ m m' : M, m ≠ 0 → m' ≠ 0 → ∃ n : ℕ, (φ ^ n) m = m') :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2) (e : M ≃+ K) (μ : K),
      (∀ m, e (φ m) = μ * e m) ∧ ∀ w : K, w ≠ 0 → ∃ n : ℕ, μ ^ n = w := by
  classical
  set S : Subring (AddMonoid.End M) := Subring.centralizer ({φ} : Set (AddMonoid.End M)) with hS
  have hφS : φ ∈ S := Subring.mem_centralizer_iff.mpr fun g hg => by
    rw [Set.mem_singleton_iff.mp hg]
  have hpow : ∀ P ∈ S, ∀ n : ℕ, ∀ m : M, P ((φ ^ n) m) = (φ ^ n) (P m) := by
    intro P hP n m
    have hc : Commute φ P := Subring.mem_centralizer_iff.mp hP φ rfl
    have e := congrArg (fun F : AddMonoid.End M => F m) (hc.pow_left n).eq
    exact e.symm
  have key : ∀ P ∈ S, ∀ m₀ : M, m₀ ≠ 0 → P m₀ = 0 → P = 0 := by
    intro P hP m₀ hm₀ h0
    ext m
    by_cases hm : m = 0
    · rw [hm, map_zero, map_zero]
    · obtain ⟨n, rfl⟩ := htrans m₀ m hm₀ hm
      rw [hpow P hP n m₀, h0, map_zero]
      rfl
  have hne : (1 : S) ≠ 0 := by
    intro h
    apply ha₀
    have := congrArg (fun P : S => (P : AddMonoid.End M) a₀) h
    simpa using this
  have : Nontrivial S := ⟨⟨1, 0, hne⟩⟩
  have : NoZeroDivisors S := by
    refine ⟨fun {P Q} hPQ => ?_⟩
    by_cases hQ : Q = 0
    · exact Or.inr hQ
    left
    have hQa : (Q : AddMonoid.End M) a₀ ≠ 0 := fun h0 =>
      hQ (Subtype.ext (key Q Q.2 a₀ ha₀ h0))
    refine Subtype.ext (key P P.2 _ hQa ?_)
    have := congrArg (fun F : S => (F : AddMonoid.End M) a₀) hPQ
    simpa using this
  have : IsDomain S := NoZeroDivisors.to_isDomain S
  have : Finite (AddMonoid.End M) := .of_injective _ DFunLike.coe_injective
  let hF : Field S := (Finite.isDomain_to_isField S).toField
  let : Fintype S := Fintype.ofFinite S
  have h2S : (2 : S) = 0 := by
    apply Subtype.ext
    ext m
    have e2 : ((2 : S) : AddMonoid.End M) = 2 := rfl
    rw [e2, AddMonoid.End.ofNat_apply, two_nsmul, h2]
    rfl
  have hchar : CharP S 2 := CharTwo.of_one_ne_zero_of_two_eq_zero hne h2S
  let ev : S →+ M :=
    { toFun := fun P => (P : AddMonoid.End M) a₀
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hev : ∀ P : S, ev P = (P : AddMonoid.End M) a₀ := fun _ => rfl
  have hinj : Function.Injective ev := by
    intro P Q hPQ
    have h1 : ((P - Q : S) : AddMonoid.End M) a₀ = 0 := by
      show (P : AddMonoid.End M) a₀ - (Q : AddMonoid.End M) a₀ = 0
      rw [← hev, ← hev, hPQ, sub_self]
    have := key _ (P - Q).2 a₀ ha₀ h1
    exact sub_eq_zero.mp (Subtype.ext this)
  have hsurj : Function.Surjective ev := by
    intro m
    by_cases hm : m = 0
    · exact ⟨0, by rw [hm, map_zero]⟩
    obtain ⟨n, hn⟩ := htrans a₀ m ha₀ hm
    exact ⟨⟨φ ^ n, pow_mem hφS n⟩, hn⟩
  set E : S ≃+ M := AddEquiv.ofBijective ev ⟨hinj, hsurj⟩ with hE
  have hEapp : ∀ P : S, E P = (P : AddMonoid.End M) a₀ := fun _ => rfl
  refine ⟨S, hF, inferInstance, hchar, E.symm, ⟨φ, hφS⟩, fun m => ?_, fun w hw => ?_⟩
  · apply E.injective
    rw [AddEquiv.apply_symm_apply]
    have h1 : ((E.symm m : S) : AddMonoid.End M) a₀ = m := by
      rw [← hEapp, AddEquiv.apply_symm_apply]
    show φ m = φ (((E.symm m : S) : AddMonoid.End M) a₀)
    rw [h1]
  · have hEw : E w ≠ 0 := fun h0 => hw (E.injective (by rw [h0, map_zero]))
    obtain ⟨n, hn⟩ := htrans a₀ (E w) ha₀ hEw
    refine ⟨n, E.injective ?_⟩
    rw [hEapp, ← hn]
    rfl

theorem outerLevel_exists_coords {G : Type} [Group G] {A : Subgroup G} [Finite A]
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (h2 : ∀ a ∈ A, a ^ 2 = 1) {a₀ : G} (ha₀ : a₀ ∈ A)
    (ha₀1 : a₀ ≠ 1) {d : G} (hd : ∀ b ∈ A, d⁻¹ * b * d ∈ A)
    (htrans : ∀ b ∈ A, ∀ b' ∈ A, b ≠ 1 → b' ≠ 1 → ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b') :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2) (v : G → K) (μ : K),
      Fintype.card K = Nat.card A ∧ U3A₁Coords A d v μ ∧
        ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w := by
  classical
  let _ : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun a b => Subtype.ext (hA a a.2 b b.2) }
  let c : A →* A :=
    { toFun := fun b => ⟨d⁻¹ * b * d, hd b b.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let φ : AddMonoid.End (Additive A) := MonoidHom.toAdditive c
  have hφ : ∀ n : ℕ, ∀ b : A,
      ((Additive.toMul ((φ ^ n) (Additive.ofMul b)) : A) : G) = (d ^ n)⁻¹ * b * d ^ n := by
    intro n
    induction n with
    | zero => intro b; simp
    | succ n ih =>
      intro b
      rw [pow_succ']
      show d⁻¹ * ((Additive.toMul ((φ ^ n) (Additive.ofMul b)) : A) : G) * d = _
      rw [ih b, pow_succ]
      group
  have h2' : ∀ m : Additive A, m + m = 0 := by
    intro m
    show Additive.ofMul (Additive.toMul m * Additive.toMul m) = Additive.ofMul 1
    congr 1
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, ← sq]
    exact h2 _ (Additive.toMul m).2
  have hzero : ∀ b : A, Additive.ofMul b = 0 → (b : G) = 1 := by
    intro b hb
    have : b = 1 := hb
    rw [this, Subgroup.coe_one]
  have htrans' : ∀ m m' : Additive A, m ≠ 0 → m' ≠ 0 → ∃ n : ℕ, (φ ^ n) m = m' := by
    intro m m' hm hm'
    obtain ⟨b, rfl⟩ : ∃ b : A, Additive.ofMul b = m := ⟨Additive.toMul m, rfl⟩
    obtain ⟨b', rfl⟩ : ∃ b' : A, Additive.ofMul b' = m' := ⟨Additive.toMul m', rfl⟩
    have hb : (b : G) ≠ 1 := fun h1 => hm (by
      have : b = 1 := Subtype.ext h1
      rw [this]
      rfl)
    have hb' : (b' : G) ≠ 1 := fun h1 => hm' (by
      have : b' = 1 := Subtype.ext h1
      rw [this]
      rfl)
    obtain ⟨n, hn⟩ := htrans b b.2 b' b'.2 hb hb'
    refine ⟨n, Additive.toMul.injective (Subtype.ext ?_)⟩
    rw [hφ n b, hn]
    rfl
  have ha₀' : Additive.ofMul (⟨a₀, ha₀⟩ : A) ≠ 0 := fun h0 => ha₀1 (hzero _ h0)
  obtain ⟨K, _, _, _, e, μ, he, hgen⟩ :=
    outerLevel_exists_field_of_transitive h2' φ ha₀' htrans'
  let v : G → K := fun g => if hg : g ∈ A then e (Additive.ofMul ⟨g, hg⟩) else 0
  have hv : ∀ b (hb : b ∈ A), v b = e (Additive.ofMul ⟨b, hb⟩) := fun b hb => dite_eq_left hb
  refine ⟨K, inferInstance, inferInstance, inferInstance, v, μ, ?_, ⟨?_, ?_, ?_, hd, ?_⟩, hgen⟩
  · rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr Additive.toMul)
  · intro b hb b' hb'
    rw [hv _ (mul_mem hb hb'), hv b hb, hv b' hb', ← map_add]
    rfl
  · intro b hb b' hb' hbb'
    rw [hv b hb, hv b' hb'] at hbb'
    have := congrArg (fun m : Additive A => ((Additive.toMul m : A) : G)) (e.injective hbb')
    exact this
  · intro w
    refine ⟨((Additive.toMul (e.symm w) : A) : G), (Additive.toMul (e.symm w)).2, ?_⟩
    rw [hv _ (Additive.toMul (e.symm w)).2]
    exact e.apply_symm_apply w
  · intro b hb
    rw [hv _ (hd b hb), hv b hb, ← he]
    rfl

end CFSG.SeitzReduction.RankOne
