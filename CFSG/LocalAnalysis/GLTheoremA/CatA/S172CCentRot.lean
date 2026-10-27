module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentDecomp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.K159 CFSG.Open
  CFSG.GroupTheory.WeirSylow

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {Bb : Subgroup ↥(orthDerived Q)} {r : ℕ}
  {U : Fin r → Submodule F V}

theorem pow_apply_eq_self {f : V ≃ₗ[F] V} {x : V} (h : f x = x) (k : ℕ) : (f ^ k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, h, ih]

theorem pow_apply_eq_of_apply_eq {f g : V ≃ₗ[F] V} {W : Submodule F V} (hgW : ∀ x ∈ W, g x ∈ W)
    (h : ∀ x ∈ W, f x = g x) (k : ℕ) : ∀ x ∈ W, (f ^ k) x = (g ^ k) x := by
  induction k with
  | zero => intro x _; rfl
  | succ k ih =>
    intro x hx
    rw [pow_succ, pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h x hx]
    exact ih _ (hgW x hx)

theorem IsPlaneDecomp.eq_one_of_forall_apply_eq (hU : IsPlaneDecomp Q Bb ⊤ U)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb) (h : ∀ j, ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = x) : d = 1 := by
  have hall : ∀ x ∈ (⨆ j, U j), (d : V ≃ₗ[F] V) x = x := by
    intro x hx
    refine Submodule.iSup_induction U (motive := fun x => (d : V ≃ₗ[F] V) x = x) hx
      (fun j y hy => h j y hy) (map_zero _) ?_
    intro x y hx hy
    rw [map_add, hx, hy]
  have hx : ∀ x : V, x ∈ (⨆ j, U j) ⊔ polarPerp Q (⨆ j, U j) := fun x => by
    rw [hU.toIsPlaneSystem.isCompl_iSup.sup_eq_top]
    exact Submodule.mem_top
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 (hx x)
  rw [map_add, hall a ha, hU.apply_of_perp d hd z Submodule.mem_top hz]
  rfl

theorem IsPlaneDecomp.exists_exps (hU : IsPlaneDecomp Q Bb ⊤ U) (hBb : IsElemAbelian p Bb)
    (hp : p.Prime) :
    ∃ (g : Fin r → ↥(orthDerived Q)) (Φ : ↥Bb → Fin r → ZMod p), Function.Injective Φ ∧
      (∀ j, g j ∈ Bb) ∧ (∀ j, ∀ x ∈ U j, (g j : V ≃ₗ[F] V) x = x → x = 0) ∧
      ∀ (b : ↥Bb) (j : Fin r), ∀ x ∈ U j,
        ((b : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = ((g j : V ≃ₗ[F] V) ^ (Φ b j).val) x := by
  choose g hgB hgfix hgpow using hU.exists_gen
  choose m hm using hgpow
  have hgp : ∀ j, ((g j : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ p = 1 := fun j => by
    have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) (hBb.2 (g j) (hgB j))
    simpa using this
  have hΦ : ∀ (b : ↥Bb) (j : Fin r), ∀ x ∈ U j, ((b : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
      ((g j : V ≃ₗ[F] V) ^ ((m j b b.2 : ℕ) : ZMod p).val) x := by
    intro b j x hx
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hgp j)]
    exact hm j b b.2 x hx
  refine ⟨g, fun b j => ((m j b b.2 : ℕ) : ZMod p), ?_, hgB, hgfix, hΦ⟩
  intro b b' hbb'
  have h1 : (b : ↥(orthDerived Q))⁻¹ * (b' : ↥(orthDerived Q)) = 1 := by
    refine hU.eq_one_of_forall_apply_eq (Bb.mul_mem (Bb.inv_mem b.2) b'.2) ?_
    intro j x hx
    have hj : ((m j b b.2 : ℕ) : ZMod p) = ((m j b' b'.2 : ℕ) : ZMod p) := congrFun hbb' j
    have e1 := hΦ b j x hx
    have e2 := hΦ b' j x hx
    rw [← hj] at e2
    have hbx : ((b' : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = ((b : ↥(orthDerived Q)) : V ≃ₗ[F] V) x := by
      rw [e1, e2]
    calc (((b : ↥(orthDerived Q))⁻¹ * (b' : ↥(orthDerived Q)) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x
        = (((b : ↥(orthDerived Q))⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          (((b' : ↥(orthDerived Q)) : V ≃ₗ[F] V) x) := rfl
      _ = (((b : ↥(orthDerived Q))⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          (((b : ↥(orthDerived Q)) : V ≃ₗ[F] V) x) := by rw [hbx]
      _ = (((b : ↥(orthDerived Q))⁻¹ * (b : ↥(orthDerived Q)) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x := rfl
      _ = x := by rw [inv_mul_cancel]; rfl
  exact Subtype.ext (inv_mul_eq_one.1 h1)

theorem IsPlaneDecomp.card_le_pow (hU : IsPlaneDecomp Q Bb ⊤ U) (hBb : IsElemAbelian p Bb)
    (hp : p.Prime) : Nat.card Bb ≤ p ^ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, Φ, hinj, -⟩ := hU.exists_exps hBb hp
  calc Nat.card Bb ≤ Nat.card (Fin r → ZMod p) := Nat.card_le_card_of_injective Φ hinj
    _ = p ^ r := by simp [Nat.card_eq_fintype_card]

theorem IsPlaneDecomp.exists_dual (hU : IsPlaneDecomp Q Bb ⊤ U) (hBb : IsElemAbelian p Bb)
    (hp : p.Prime) (hcard : Nat.card Bb = p ^ r) :
    ∃ e : Fin r → ↥(orthDerived Q), (∀ j, e j ∈ Bb) ∧
      (∀ j, ∀ x ∈ U j, (e j : V ≃ₗ[F] V) x = x → x = 0) ∧
      (∀ i j, i ≠ j → ∀ x ∈ U i, (e j : V ≃ₗ[F] V) x = x) ∧
      ∀ b ∈ Bb, ∀ j, ∃ k : ℕ, ∀ x ∈ U j, (b : V ≃ₗ[F] V) x = ((e j : V ≃ₗ[F] V) ^ k) x := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, Φ, hinj, hgB, hgfix, hΦ⟩ := hU.exists_exps hBb hp
  have hbij : Function.Bijective Φ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcard]
    simp [Nat.card_eq_fintype_card]
  choose b hb using fun j : Fin r => hbij.2 (Pi.single j 1)
  have hbj : ∀ j, ∀ x ∈ U j, (((b j : ↥Bb) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = (g j : V ≃ₗ[F] V) x := by
    intro j x hx
    have h1 : Φ (b j) j = 1 := by rw [hb j]; exact Pi.single_eq_same j 1
    rw [hΦ (b j) j x hx, h1, ZMod.val_one, pow_one]
  have hbi : ∀ i j, i ≠ j → ∀ x ∈ U i, (((b j : ↥Bb) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
    intro i j hij x hx
    have h1 : Φ (b j) i = 0 := by rw [hb j]; exact Pi.single_eq_of_ne hij 1
    rw [hΦ (b j) i x hx, h1, ZMod.val_zero, pow_zero]
    rfl
  refine ⟨fun j => ((b j : ↥Bb) : ↥(orthDerived Q)), fun j => (b j).2, ?_, hbi, ?_⟩
  · intro j x hx hfix
    exact hgfix j x hx (by rw [← hbj j x hx]; exact hfix)
  · intro c hc j
    refine ⟨(Φ ⟨c, hc⟩ j).val, fun x hx => ?_⟩
    rw [hΦ ⟨c, hc⟩ j x hx]
    exact (pow_apply_eq_of_apply_eq (fun y hy => hU.maps_to _ (hgB j) j y hy) (fun y hy => hbj j y hy)
      _ x hx).symm

theorem IsPlaneDecomp.apply_eq_of_mem_polarPerp (hU : IsPlaneDecomp Q Bb ⊤ U) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (j : Fin r) (hother : ∀ i, i ≠ j → ∀ x ∈ U i, (d : V ≃ₗ[F] V) x = x) {x : V}
    (hx : x ∈ polarPerp Q (U j)) : (d : V ≃ₗ[F] V) x = x := by
  have hP : ∀ b ∈ Bb, ∀ y ∈ U j, (b : V ≃ₗ[F] V) y ∈ U j := fun b hb y hy => hU.maps_to b hb j y hy
  have hsub : ∀ y : V, (d : V ≃ₗ[F] V) y - y ∈ U j := by
    intro y
    have hy : y ∈ (⨆ i, U i) ⊔ polarPerp Q (⨆ i, U i) := by
      rw [hU.toIsPlaneSystem.isCompl_iSup.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
    have hz' := hU.apply_of_perp d hd z Submodule.mem_top hz
    have ha' : (d : V ≃ₗ[F] V) a - a ∈ U j := by
      refine Submodule.iSup_induction U (motive := fun a => (d : V ≃ₗ[F] V) a - a ∈ U j) ha ?_ ?_ ?_
      · intro i y hy
        by_cases hij : i = j
        · subst hij
          exact Submodule.sub_mem _ (hP d hd y hy) hy
        · rw [hother i hij y hy, sub_self]
          exact Submodule.zero_mem _
      · simp
      · intro x y hx hy
        have : (d : V ≃ₗ[F] V) (x + y) - (x + y) = ((d : V ≃ₗ[F] V) x - x) + ((d : V ≃ₗ[F] V) y - y) := by
          rw [map_add]
          abel
        rw [this]
        exact Submodule.add_mem _ hx hy
    rw [map_add, hz']
    simpa using ha'
  have hperp : (d : V ≃ₗ[F] V) x ∈ polarPerp Q (U j) := apply_mem_polarPerp hP hd hx
  have h2 : (d : V ≃ₗ[F] V) x - x ∈ U j ⊓ polarPerp Q (U j) :=
    ⟨hsub x, Submodule.sub_mem _ hperp hx⟩
  rw [disjoint_iff.1 (isCompl_polarPerp (hU.nondeg j)).disjoint] at h2
  exact sub_eq_zero.1 ((Submodule.mem_bot F).1 h2)

theorem IsPlaneDecomp.closure_eq_of_exists_pow (hU : IsPlaneDecomp Q Bb ⊤ U)
    (e : Fin r → ↥(orthDerived Q)) (hmem : ∀ j, e j ∈ Bb)
    (hother : ∀ i j, i ≠ j → ∀ x ∈ U i, (e j : V ≃ₗ[F] V) x = x)
    (hpow : ∀ b ∈ Bb, ∀ j, ∃ k : ℕ, ∀ x ∈ U j,
      (b : V ≃ₗ[F] V) x = ((e j : V ≃ₗ[F] V) ^ k) x) :
    Subgroup.closure (Set.range e) = Bb := by
  apply le_antisymm
  · exact (Subgroup.closure_le Bb).2 (by rintro _ ⟨j, rfl⟩; exact hmem j)
  · suffices h : ∀ s : Finset (Fin r), ∀ b ∈ Bb,
        (∀ i, i ∉ s → ∀ x ∈ U i, (b : V ≃ₗ[F] V) x = x) → b ∈ Subgroup.closure (Set.range e) from
      fun b hb => h Finset.univ b hb fun i hi => absurd (Finset.mem_univ i) hi
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro b hb h
      rw [hU.eq_one_of_forall_apply_eq hb fun j x hx => h j (Finset.notMem_empty j) x hx]
      exact Subgroup.one_mem _
    | insert a s ha ih =>
      intro b hb h
      obtain ⟨k, hk⟩ := hpow b hb a
      have hmemk : e a ^ k ∈ Subgroup.closure (Set.range e) :=
        Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self a)) k
      have hinv : ∀ (y : V) (f : V ≃ₗ[F] V), f y = y → f⁻¹ y = y := fun y f hf => by
        have h1 : (f⁻¹ * f) y = y := by rw [inv_mul_cancel]; rfl
        rw [LinearEquiv.mul_apply, hf] at h1
        exact h1
      have hb' : (e a ^ k)⁻¹ * b ∈ Subgroup.closure (Set.range e) := by
        refine ih _ (Bb.mul_mem (Bb.inv_mem (Bb.pow_mem (hmem a) k)) hb) ?_
        intro i hi x hx
        by_cases hia : i = a
        · subst hia
          have h1 := hk x hx
          calc (((e i ^ k)⁻¹ * b : ↥(orthDerived Q)) : V ≃ₗ[F] V) x
              = ((e i : V ≃ₗ[F] V) ^ k)⁻¹ ((b : V ≃ₗ[F] V) x) := rfl
            _ = ((e i : V ≃ₗ[F] V) ^ k)⁻¹ (((e i : V ≃ₗ[F] V) ^ k) x) := by rw [h1]
            _ = (((e i : V ≃ₗ[F] V) ^ k)⁻¹ * ((e i : V ≃ₗ[F] V) ^ k)) x := rfl
            _ = x := by rw [inv_mul_cancel]; rfl
        · have hbx : (b : V ≃ₗ[F] V) x = x :=
            h i (fun hi' => (Finset.mem_insert.1 hi').elim hia hi) x hx
          have hex : ((e a : V ≃ₗ[F] V) ^ k) x = x := pow_apply_eq_self (hother i a hia x hx) k
          calc (((e a ^ k)⁻¹ * b : ↥(orthDerived Q)) : V ≃ₗ[F] V) x
              = ((e a : V ≃ₗ[F] V) ^ k)⁻¹ ((b : V ≃ₗ[F] V) x) := rfl
            _ = x := by rw [hbx]; exact hinv x _ hex
      have := Subgroup.mul_mem _ hmemk hb'
      simpa using this

theorem IsPlaneDecomp.exists_planeFrame (hU : IsPlaneDecomp Q Bb ⊤ U) (hBb : IsElemAbelian p Bb)
    (hp : p.Prime) (hcard : Nat.card Bb = p ^ r) :
    ∃ e : Fin r → ↥(orthDerived Q), IsPlaneFrame Q p U e Bb := by
  obtain ⟨e, hmem, hfix, hother, hpow⟩ := hU.exists_dual hBb hp hcard
  refine ⟨e, ?_⟩
  refine
    { toIsPlaneSystem := hU.toIsPlaneSystem
      orderOf_eq := ?_
      apply_of_perp := ?_
      maps_to := ?_
      eq_zero_of_apply_eq := hfix
      isElemAbelian := hBb
      closure_eq := hU.closure_eq_of_exists_pow e hmem hother hpow }
  · intro j
    haveI : Fact p.Prime := ⟨hp⟩
    refine orderOf_eq_prime (hBb.2 _ (hmem j)) ?_
    intro h1
    obtain ⟨x, hxU, hx0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U j) (hU.finrank_eq j)
    exact hx0 (hfix j x hxU (by rw [h1]; rfl))
  · intro j x hx
    exact hU.apply_eq_of_mem_polarPerp (hmem j) j (fun i hij => hother i j hij) hx
  · intro j x hx
    exact hU.maps_to (e j) (hmem j) j x hx

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
