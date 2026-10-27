module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.SolvableHall

attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G] {p : ℕ}
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem mem_invariants_comp_subtype {ρ : Representation (ZMod p) G V} {X : Subgroup G} {v : V} :
    v ∈ Representation.invariants (ρ.comp X.subtype) ↔ ∀ a ∈ X, ρ a v = v :=
  ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a a.2⟩

theorem invariants_comp_subtype_antitone (ρ : Representation (ZMod p) G V) {X Y : Subgroup G}
    (h : X ≤ Y) :
    Representation.invariants (ρ.comp Y.subtype) ≤
      Representation.invariants (ρ.comp X.subtype) :=
  fun _ hw => mem_invariants_comp_subtype.mpr fun a ha =>
    mem_invariants_comp_subtype.mp hw a (h ha)

private def stabilizer (ρ : Representation (ZMod p) G V) (w : V) : Subgroup G where
  carrier := {g | ρ g w = w}
  mul_mem' {g h} hg hh := by
    change ρ (g * h) w = w
    rw [map_mul, Module.End.mul_apply, hh, hg]
  one_mem' := by
    change ρ 1 w = w
    rw [map_one, Module.End.one_apply]
  inv_mem' {g} hg := by
    change ρ g⁻¹ w = w
    conv_lhs => rw [← hg]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem invariants_comp_subtype_sup (ρ : Representation (ZMod p) G V) (X Y : Subgroup G) :
    Representation.invariants (ρ.comp (X ⊔ Y).subtype) =
      Representation.invariants (ρ.comp X.subtype) ⊓
        Representation.invariants (ρ.comp Y.subtype) := by
  refine le_antisymm (le_inf (invariants_comp_subtype_antitone ρ le_sup_left)
    (invariants_comp_subtype_antitone ρ le_sup_right)) ?_
  intro w hw
  obtain ⟨hX, hY⟩ := Submodule.mem_inf.mp hw
  have hle : X ⊔ Y ≤ stabilizer ρ w :=
    sup_le (fun a ha => mem_invariants_comp_subtype.mp hX a ha)
      (fun b hb => mem_invariants_comp_subtype.mp hY b hb)
  exact mem_invariants_comp_subtype.mpr fun z hz => hle hz

noncomputable def subgroupAverage (ρ : Representation (ZMod p) G V) (X : Subgroup G) :
    V →ₗ[ZMod p] V :=
  (Nat.card X : ZMod p)⁻¹ • ∑ x : X, ρ (x : G)

theorem subgroupAverage_apply (ρ : Representation (ZMod p) G V) (X : Subgroup G) (v : V) :
    subgroupAverage ρ X v = (Nat.card X : ZMod p)⁻¹ • ∑ x : X, ρ (x : G) v := by
  rw [subgroupAverage, LinearMap.smul_apply, LinearMap.sum_apply]

theorem subgroupAverage_mem_invariants (ρ : Representation (ZMod p) G V) (X : Subgroup G) (v : V) :
    subgroupAverage ρ X v ∈ Representation.invariants (ρ.comp X.subtype) := by
  rw [mem_invariants_comp_subtype]
  intro x hx
  rw [subgroupAverage_apply]
  have h1 : ρ x (∑ y : X, ρ (y : G) v) = ∑ y : X, ρ (x * (y : G)) v := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun y _ => by
      rw [← Module.End.mul_apply, ← map_mul]
  rw [map_smul, h1]
  exact congrArg (fun w => (Nat.card X : ZMod p)⁻¹ • w)
    (Equiv.sum_comp (Equiv.mulLeft (⟨x, hx⟩ : X)) (fun y : X => ρ (y : G) v))

theorem subgroupAverage_eq_self (ρ : Representation (ZMod p) G V) (hp : p.Prime) {X : Subgroup G}
    {v : V} (hcard : (Nat.card X : ZMod p) ≠ 0)
    (hv : v ∈ Representation.invariants (ρ.comp X.subtype)) : subgroupAverage ρ X v = v := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [subgroupAverage_apply]
  have h : ∀ y : X, ρ (y : G) v = v :=
    fun y => mem_invariants_comp_subtype.mp hv (y : G) y.2
  rw [Finset.sum_congr rfl fun y _ => h y]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul (R := ZMod p) (Nat.card X) v]
  rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]

theorem subgroupAverage_mem_invariants_of_commute (ρ : Representation (ZMod p) G V)
    {X Y : Subgroup G} (hcomm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {v : V}
    (hv : v ∈ Representation.invariants (ρ.comp Y.subtype)) :
    subgroupAverage ρ X v ∈ Representation.invariants (ρ.comp Y.subtype) := by
  rw [mem_invariants_comp_subtype]
  intro y hy
  rw [subgroupAverage_apply, map_smul, map_sum]
  rw [Finset.sum_congr rfl fun x _ => by
    rw [← Module.End.mul_apply, ← map_mul, ← hcomm x x.2 y hy, map_mul, Module.End.mul_apply,
      mem_invariants_comp_subtype.mp hv y hy]]

theorem subgroupAverage_rho_of_mem_normalizer (ρ : Representation (ZMod p) G V) (X : Subgroup G)
    {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) (v : V) :
    subgroupAverage ρ X (ρ g v) = ρ g (subgroupAverage ρ X v) := by
  rw [subgroupAverage_apply, subgroupAverage_apply, map_smul, map_sum]
  congr 1
  simp only [← Module.End.mul_apply, ← map_mul]
  let e : X ≃ X :=
    { toFun := fun x =>
        ⟨g⁻¹ * (x : G) * g, (Subgroup.mem_normalizer_iff''.mp hg (x : G)).mp x.2⟩
      invFun := fun x =>
        ⟨g * (x : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp x.2⟩
      left_inv := fun x => by ext; simp only [Subtype.coe_mk]; group
      right_inv := fun x => by ext; simp only [Subtype.coe_mk]; group }
  have h := Equiv.sum_comp e (fun y : X => ρ (g * (y : G)) v)
  simpa [e, mul_assoc] using h

theorem natCast_card_ne_zero_of_isPGroup {q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    {X : Subgroup G} (hX : IsPGroup q X) : (Nat.card X : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q) (G := X)).mp hX
  rw [hn, Nat.cast_pow]
  exact pow_ne_zero n fun h0 =>
    (Ne.symm hqp) ((Nat.prime_dvd_prime_iff_eq hp hq).mp ((ZMod.natCast_eq_zero_iff q p).mp h0))

private theorem natCast_card_ne_zero_of_le_elemAbelian {q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q ≠ p) {A X : Subgroup G} (hA : CFSG.Open.IsElemAbelian q A) (hX : X ≤ A) :
    (Nat.card X : ZMod p) ≠ 0 := by
  haveI : CFSG.IsElementaryAbelian q A :=
    { toIsMulCommutative := hA.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
        apply Subtype.ext
        exact hA.2 (x : G) x.2 }
  exact natCast_card_ne_zero_of_isPGroup hp hq hqp
    ((CFSG.IsElementaryAbelian.isPGroup q A).to_le hX)

theorem sup_eq_of_ne_hyperplane {q : ℕ} (hq : q.Prime) {A B₀ B : Subgroup G}
    (hB₀A : B₀ ≤ A) (hBA : B ≤ A) (hB₀ : B₀.relIndex A = q) (hB : B.relIndex A = q)
    (hne : B₀ ≠ B) : B₀ ⊔ B = A := by
  have hcard : ∀ C : Subgroup G, C ≤ A → C.relIndex A = q → Nat.card C = Nat.card B₀ := by
    intro C hCA hC
    have h1 : q * Nat.card C = Nat.card A := by
      have h := Subgroup.relIndex_mul_card (H := C) (K := A)
      rwa [hC, inf_eq_left.mpr hCA] at h
    have h2 : q * Nat.card B₀ = Nat.card A := by
      have h := Subgroup.relIndex_mul_card (H := B₀) (K := A)
      rwa [hB₀, inf_eq_left.mpr hB₀A] at h
    exact Nat.eq_of_mul_eq_mul_left hq.pos (h1.trans h2.symm)
  have hsupA : B₀ ⊔ B ≤ A := sup_le hB₀A hBA
  have hdvd : (B₀ ⊔ B).relIndex A ∣ q := by
    rw [← hB₀]
    exact Subgroup.relIndex_dvd_of_le_left A le_sup_left
  rcases (Nat.dvd_prime hq).mp hdvd with h1 | hq'
  · exact le_antisymm hsupA (Subgroup.relIndex_eq_one.mp h1)
  · exfalso
    have hcq : Nat.card (B₀ ⊔ B : Subgroup G) = Nat.card B₀ := hcard (B₀ ⊔ B) hsupA hq'
    have heq : B₀ ⊔ B = B₀ := (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcq])).symm
    have hBle : B ≤ B₀ := by rw [← heq]; exact le_sup_right
    have hcB : Nat.card B = Nat.card B₀ := hcard B hBA hB
    exact hne (Subgroup.eq_of_le_of_card_ge hBle (by rw [hcB])).symm

@[instance_reducible]
private noncomputable def act (ρ : Representation (ZMod p) G V) (A : Subgroup G) :
    MulDistribMulAction ↥A (Multiplicative V) where
  smul a x := Multiplicative.ofAdd (ρ (a : G) (Multiplicative.toAdd x))
  one_smul x := by
    change Multiplicative.ofAdd (ρ (1 : G) (Multiplicative.toAdd x)) = x
    rw [map_one, Module.End.one_apply, ofAdd_toAdd]
  mul_smul a b x := by
    change Multiplicative.ofAdd (ρ ((a : G) * (b : G)) (Multiplicative.toAdd x)) =
      Multiplicative.ofAdd (ρ (a : G) (ρ (b : G) (Multiplicative.toAdd x)))
    rw [map_mul, Module.End.mul_apply]
  smul_mul a x y := by
    change Multiplicative.ofAdd (ρ (a : G) (Multiplicative.toAdd (x * y))) =
      Multiplicative.ofAdd (ρ (a : G) (Multiplicative.toAdd x)) *
        Multiplicative.ofAdd (ρ (a : G) (Multiplicative.toAdd y))
    rw [toAdd_mul, map_add, ofAdd_add]
  smul_one a := by
    change Multiplicative.ofAdd (ρ (a : G) (Multiplicative.toAdd (1 : Multiplicative V))) = 1
    rw [show Multiplicative.toAdd (1 : Multiplicative V) = 0 from rfl, map_zero, ofAdd_zero]

theorem iSupIndep_invariants_hyperplanes (ρ : Representation (ZMod p) G V) (hp : p.Prime)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian q A)
    (hfix : Representation.invariants (ρ.comp A.subtype) = ⊥) :
    iSupIndep (fun B : {B : Subgroup G // B ≤ A ∧ B.relIndex A = q} =>
      Representation.invariants (ρ.comp B.1.subtype)) := by
  rw [iSupIndep_def]
  intro B₀
  rw [Submodule.disjoint_def]
  intro v hv₀ hv
  have hv' : v ∈ ⨆ B : {B : {B : Subgroup G // B ≤ A ∧ B.relIndex A = q} // B ≠ B₀},
      Representation.invariants (ρ.comp B.1.1.subtype) := by
    rw [iSup_subtype'] at hv
    exact hv
  have hproj : subgroupAverage ρ B₀.1 v = 0 := by
    refine Submodule.iSup_induction (motive := fun x => subgroupAverage ρ B₀.1 x = 0)
      (fun B : {B : {B : Subgroup G // B ≤ A ∧ B.relIndex A = q} // B ≠ B₀} =>
        Representation.invariants (ρ.comp B.1.1.subtype)) hv' ?_ ?_ ?_
    · intro B x hx
      haveI := hA.1
      have hne : B₀.1 ≠ B.1.1 := fun h => B.2 (Subtype.ext h).symm
      have hcomm : ∀ a ∈ B₀.1, ∀ b ∈ B.1.1, a * b = b * a := fun a ha b hb =>
        congrArg Subtype.val (mul_comm' (⟨a, B₀.2.1 ha⟩ : ↥A) (⟨b, B.1.2.1 hb⟩ : ↥A))
      have hmem : subgroupAverage ρ B₀.1 x ∈
          Representation.invariants (ρ.comp (B₀.1 ⊔ B.1.1).subtype) := by
        rw [invariants_comp_subtype_sup]
        exact ⟨subgroupAverage_mem_invariants ρ _ x,
          subgroupAverage_mem_invariants_of_commute ρ hcomm hx⟩
      rw [sup_eq_of_ne_hyperplane hq B₀.2.1 B.1.2.1 B₀.2.2 B.1.2.2 hne] at hmem
      change subgroupAverage ρ B₀.1 x ∈ Representation.invariants (ρ.comp A.subtype) at hmem
      rw [hfix] at hmem
      simpa using hmem
    · exact (subgroupAverage ρ B₀.1).map_zero
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
  rw [← subgroupAverage_eq_self ρ hp (X := B₀.1)
      (natCast_card_ne_zero_of_le_elemAbelian hp hq hqp hA B₀.2.1) hv₀,
    hproj]

theorem iSup_invariants_hyperplanes_eq_top [Finite V] (ρ : Representation (ZMod p) G V)
    (hp : p.Prime) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian q A) (hA1 : A ≠ ⊥) :
    ⨆ B : {B : Subgroup G // B ≤ A ∧ B.relIndex A = q},
      Representation.invariants (ρ.comp B.1.subtype) = ⊤ := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  haveI : CFSG.IsElementaryAbelian q A :=
    { toIsMulCommutative := hA.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
        apply Subtype.ext
        exact hA.2 (x : G) x.2 }
  haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
  letI : MulDistribMulAction ↥A (Multiplicative V) := act ρ A
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hcardV : Nat.card (Multiplicative V) = p ^ Module.finrank (ZMod p) V := by
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [Nat.card_zmod] at this
    exact this
  have hcop : ¬ q ∣ Nat.card (Multiplicative V) := by
    rw [hcardV]
    intro hd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd))
  have hgen := abelian_hyperplane_generation (p := q) (A := ↥A) (H := Multiplicative V) hcop
  have hgen' : (⨆ B : {B : Subgroup ↥A // B.index = q},
      CFSG.fixedPointSubgroup B.1 (Multiplicative V)) = ⊤ := by
    rw [iSup_subtype]
    exact hgen
  apply eq_top_iff.mpr
  intro v _
  have hv : Multiplicative.ofAdd v ∈ (⊤ : Subgroup (Multiplicative V)) := Subgroup.mem_top _
  rw [← hgen'] at hv
  refine Subgroup.iSup_induction (fun B : {B : Subgroup ↥A // B.index = q} =>
      CFSG.fixedPointSubgroup B.1 (Multiplicative V))
    (C := fun x => Multiplicative.toAdd x ∈
      ⨆ B : {B : Subgroup G // B ≤ A ∧ B.relIndex A = q},
        Representation.invariants (ρ.comp B.1.subtype))
    hv ?_ ?_ ?_
  · intro B x hx
    have hxB : Multiplicative.toAdd x ∈
        Representation.invariants (ρ.comp (B.1.map A.subtype).subtype) := by
      rw [mem_invariants_comp_subtype]
      intro b hb
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      have h' := hx ⟨b', hb'⟩
      change Multiplicative.ofAdd (ρ ((b' : ↥A) : G) (Multiplicative.toAdd x)) =
        Multiplicative.ofAdd (Multiplicative.toAdd x) at h'
      exact Multiplicative.ofAdd.injective h'
    have hmemB : B.1.map A.subtype ≤ A ∧ (B.1.map A.subtype).relIndex A = q := by
      refine ⟨Subgroup.map_subtype_le _, ?_⟩
      have hri := Subgroup.relIndex_map_map_of_injective (f := A.subtype) B.1 ⊤ A.subtype_injective
      rw [Subgroup.map_top, Subgroup.subtype_range, Subgroup.relIndex_top_right] at hri
      exact hri.trans B.2
    exact Submodule.mem_iSup_of_mem
      (p := fun B : {B : Subgroup G // B ≤ A ∧ B.relIndex A = q} =>
        Representation.invariants (ρ.comp B.1.subtype))
      ⟨B.1.map A.subtype, hmemB⟩ hxB
  · simpa using Submodule.zero_mem
      (⨆ B : {B : Subgroup G // B ≤ A ∧ B.relIndex A = q},
        Representation.invariants (ρ.comp B.1.subtype))
  · intro x y hx hy
    rw [toAdd_mul]
    exact Submodule.add_mem _ hx hy

end CFSG.SolvableHall
