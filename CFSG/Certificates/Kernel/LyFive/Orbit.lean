module

public import CFSG.Certificates.Kernel.LyFive.Bfs
public import CFSG.Certificates.Kernel.LyFive.G2Group

public section

namespace CFSG.KS.LyFive.G2

open CFSG.KS.LyFive.Bfs CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier
open CFSG.Sporadic.LySchreier.Native
open CFSG.RankThree.PartOne.LyFive (conjClosedOK)
open Matrix

inductive Reach (r : Array ℕ) : Array ℕ → Prop
  | base : Reach r r
  | step {X : Array ℕ} {j : ℕ} : j < (hGenPairs asArr).size → Reach r X →
      Reach r (cj (hGenPairs asArr) j X)

@[expose] def CentS (X : M) : Subgroup (M)ˣ where
  carrier := {g | (g : M) * X = X * g}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (a : M) * (b : M) * X = X * ((a : M) * (b : M))
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  inv_mem' := by
    intro a ha
    change (a : M) * X = X * (a : M) at ha
    change ((a⁻¹ : (M)ˣ) : M) * X = X * ((a⁻¹ : (M)ˣ) : M)
    have e1 : ((a⁻¹ : (M)ˣ) : M) * ((a : M) * X) * ((a⁻¹ : (M)ˣ) : M) = X * ((a⁻¹ : (M)ˣ) : M) := by
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have e2 : ((a⁻¹ : (M)ˣ) : M) * (X * (a : M)) * ((a⁻¹ : (M)ˣ) : M) = ((a⁻¹ : (M)ˣ) : M) * X := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← e2, ← ha, e1]

theorem mat7_cj {j : ℕ} (hj : j < 5) (X : Array ℕ) :
    mat7 (cj (hGenPairs asArr) j X) = ((uG j hj : (M)ˣ) : M) * mat7 X * (((uG j hj)⁻¹ : (M)ˣ) : M) := by
  rw [cj, mat7_mul7, mat7_mul7]
  rfl

theorem hp_size : (hGenPairs asArr).size = 5 := hGenPairs_size

theorem mat7_reach {r : Array ℕ} (hr : Red r) :
    ∀ {X : Array ℕ}, Reach r X → Red X ∧ ∃ g ∈ G7, mat7 X = (g : M) * mat7 r * ((g⁻¹ : (M)ˣ) : M)
  | _, .base => ⟨hr, 1, G7.one_mem, by simp⟩
  | _, .step (X := X) (j := j) hj hX => by
    obtain ⟨-, g, hg, e⟩ := mat7_reach hr hX
    rw [hp_size] at hj
    refine ⟨red_mul7 _ _, uG j hj * g, G7.mul_mem (uG_mem j hj) hg, ?_⟩
    rw [mat7_cj hj, e, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]

theorem pow_reach {r : Array ℕ} {g : (M)ˣ}
    (hg : ∀ X, Reach r X → ∃ Y, Reach r Y ∧ mat7 Y = (g : M) * mat7 X * ((g⁻¹ : (M)ˣ) : M)) :
    ∀ (n : ℕ) (X : Array ℕ), Reach r X → ∃ Y, Reach r Y ∧
      mat7 Y = ((g ^ n : (M)ˣ) : M) * mat7 X * (((g ^ n)⁻¹ : (M)ˣ) : M)
  | 0, X, hX => ⟨X, hX, by simp⟩
  | n + 1, X, hX => by
    obtain ⟨Y, hY, e⟩ := pow_reach hg n X hX
    obtain ⟨Z, hZ, e'⟩ := hg Y hY
    refine ⟨Z, hZ, ?_⟩
    rw [e', e, pow_succ', _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]

theorem reach_of_mem {r : Array ℕ} {g : (M)ˣ} (hg : g ∈ G7) :
    ∀ X, Reach r X → ∃ Y, Reach r Y ∧ mat7 Y = (g : M) * mat7 X * ((g⁻¹ : (M)ˣ) : M) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, e⟩ := hx
    have hu : x = uG j hj := Units.ext e
    subst hu
    intro X hX
    exact ⟨_, Reach.step (by rw [hp_size]; exact hj) hX, mat7_cj hj X⟩
  | one => exact fun X hX => ⟨X, hX, by simp⟩
  | mul x y _ _ hx hy =>
    intro X hX
    obtain ⟨Y, hY, e⟩ := hy X hX
    obtain ⟨Z, hZ, e'⟩ := hx Y hY
    refine ⟨Z, hZ, ?_⟩
    rw [e', e, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
  | inv x _ hx =>
    have e : x⁻¹ = x ^ (orderOf x - 1) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [pow_sub_one_mul (orderOf_pos x).ne', pow_orderOf_eq_one]
    rw [e]
    exact pow_reach hx _

@[expose] def cls (K : Subgroup (M)ˣ) (X : M) : Set M := {Y | ∃ g ∈ K, Y = (g : M) * X * ((g⁻¹ : (M)ˣ) : M)}

@[expose] def cK (K : Subgroup (M)ˣ) : Subgroup (ConjAct (M)ˣ) :=
  K.map (ConjAct.toConjAct : (M)ˣ ≃* ConjAct (M)ˣ).toMonoidHom

theorem mem_cK {K : Subgroup (M)ˣ} {h : ConjAct (M)ˣ} : h ∈ cK K ↔ ConjAct.ofConjAct h ∈ K := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hh
    exact ⟨ConjAct.ofConjAct h, hh, rfl⟩

theorem orbit_cK (K : Subgroup (M)ˣ) (X : M) : MulAction.orbit (cK K) X = cls K X := by
  ext Y
  constructor
  · rintro ⟨⟨h, hh⟩, rfl⟩
    exact ⟨ConjAct.ofConjAct h, mem_cK.1 hh, ConjAct.units_smul_def h X⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨ConjAct.toConjAct g, mem_cK.2 hg⟩, ConjAct.units_smul_def _ X⟩

theorem card_stab_cK (K : Subgroup (M)ˣ) (X : M) :
    Nat.card (MulAction.stabilizer (cK K) X) = Nat.card (K ⊓ CentS X : Subgroup (M)ˣ) := by
  refine Nat.card_congr
    { toFun := fun h => ⟨ConjAct.ofConjAct h.1.1, mem_cK.1 h.1.2, ?_⟩
      invFun := fun g => ⟨⟨ConjAct.toConjAct g.1, mem_cK.2 (Subgroup.mem_inf.1 g.2).1⟩, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · have hs := MulAction.mem_stabilizer_iff.1 h.2
    change ((h.1 : ConjAct (M)ˣ) • X) = X at hs
    rw [ConjAct.units_smul_def] at hs
    change ((ConjAct.ofConjAct h.1.1 : (M)ˣ) : M) * X = X * ((ConjAct.ofConjAct h.1.1 : (M)ˣ) : M)
    generalize ConjAct.ofConjAct (h.1 : ConjAct (M)ˣ) = g at hs ⊢
    have e : (g : M) * X = ((g : M) * X * ((g⁻¹ : (M)ˣ) : M)) * (g : M) := by
      rw [Matrix.mul_assoc _ _ (g : M), Units.inv_mul, Matrix.mul_one]
    rw [e, hs]
  · rw [MulAction.mem_stabilizer_iff]
    change (ConjAct.toConjAct g.1 : ConjAct (M)ˣ) • X = X
    rw [ConjAct.units_smul_def]
    have hc : ((g.1 : (M)ˣ) : M) * X = X * (g.1 : M) := (Subgroup.mem_inf.1 g.2).2
    change ((g.1 : (M)ˣ) : M) * X * ((g.1⁻¹ : (M)ˣ) : M) = X
    rw [hc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem card_cls_mul (K : Subgroup (M)ˣ) (X : M) :
    Nat.card (cls K X) * Nat.card (K ⊓ CentS X : Subgroup (M)ˣ) = Nat.card K := by
  rw [← orbit_cK, ← card_stab_cK, ← Nat.card_prod,
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (cK K) X)]
  exact Subgroup.card_map_of_injective (ConjAct.toConjAct : (M)ˣ ≃* ConjAct (M)ˣ).injective

theorem cls_mono {K L : Subgroup (M)ˣ} (h : K ≤ L) (X : M) : cls K X ⊆ cls L X := by
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, h hg, rfl⟩

theorem cls_finite (K : Subgroup (M)ˣ) (X : M) : (cls K X).Finite := Set.toFinite _

theorem conjBFS_reach {r : Array ℕ} (hr : Red r) (cap : ℕ) :
    ∀ k < (conjBFS r (hGenPairs asArr) cap).1.size, Reach r (conjBFS r (hGenPairs asArr) cap).1[k]! :=
  conjBFS_mem hr (Reach r) Reach.base fun _ _ hj hX => Reach.step hj hX

theorem conjBFS_size_le {r : Array ℕ} (hr : Red r) (cap : ℕ) :
    (conjBFS r (hGenPairs asArr) cap).1.size ≤ Nat.card (cls G7 (mat7 r)) := by
  set T := conjBFS r (hGenPairs asArr) cap
  have hmem : ∀ k : Fin T.1.size, mat7 T.1[k.val]! ∈ cls G7 (mat7 r) := by
    intro k
    obtain ⟨-, g, hg, e⟩ := mat7_reach hr (conjBFS_reach hr cap k.val k.isLt)
    exact ⟨g, hg, e⟩
  let φ : Fin T.1.size → cls G7 (mat7 r) := fun k => ⟨mat7 T.1[k.val]!, hmem k⟩
  have hφ : Function.Injective φ := by
    intro a b e
    have e' := congrArg Subtype.val e
    apply Fin.ext
    exact conjBFS_inj hr a.val a.isLt b.val b.isLt
      (mat7_inj (conjBFS_red hr a.val a.isLt) (conjBFS_red hr b.val b.isLt) e')
  have := Finite.of_injective _ hφ
  have := Nat.card_le_card_of_injective φ hφ
  simpa using this

theorem card_cls_le_size {r : Array ℕ} (hr : Red r) {cap : ℕ}
    (hcap : (conjBFS r (hGenPairs asArr) cap).1.size ≤ cap) :
    Nat.card (cls G7 (mat7 r)) ≤ (conjBFS r (hGenPairs asArr) cap).1.size := by
  set T := conjBFS r (hGenPairs asArr) cap
  have hall : ∀ X, Reach r X → ∃ k < T.1.size, T.1[k]! = X := by
    intro X hX
    induction hX with
    | base => exact ⟨0, conjBFS_pos hr, conjBFS_zero hr⟩
    | step hj _ ih =>
      obtain ⟨k, hk, e⟩ := ih
      obtain ⟨k', hk', e'⟩ := conjBFS_closed hr hcap k hk _ hj
      exact ⟨k', hk', by rw [e', e]⟩
  have hsub : cls G7 (mat7 r) ⊆ Set.range fun k : Fin T.1.size => mat7 T.1[k.val]! := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨Y, hY, e⟩ := reach_of_mem hg r Reach.base
    obtain ⟨k, hk, ek⟩ := hall Y hY
    refine ⟨⟨k, hk⟩, ?_⟩
    change mat7 T.1[k]! = _
    rw [ek, e]
  calc Nat.card (cls G7 (mat7 r)) ≤ Nat.card (Set.range fun k : Fin T.1.size => mat7 T.1[k.val]!) :=
        Nat.card_mono (Set.finite_range _) hsub
    _ ≤ Nat.card (Fin T.1.size) :=
        Nat.card_le_card_of_surjective (Set.rangeFactorization _) Set.rangeFactorization_surjective
    _ = T.1.size := Nat.card_eq_fintype_card.trans (Fintype.card_fin _)

theorem conjBFS_size_ge {r : Array ℕ} (hr : Red r) {N : ℕ} (hN : N ≤ Nat.card (cls G7 (mat7 r))) :
    N ≤ (conjBFS r (hGenPairs asArr) N).1.size := by
  by_contra h
  have h' := card_cls_le_size hr (cap := N) (by omega)
  omega

theorem conjBFS_closed_eq {r : Array ℕ} (hr : Red r) {N : ℕ} (hN : Nat.card (cls G7 (mat7 r)) = N) :
    conjClosedOK (hGenPairs asArr) (conjBFS r (hGenPairs asArr) N) = true ∧
      (conjBFS r (hGenPairs asArr) N).1.size = N := by
  have h1 := conjBFS_size_le hr N
  have h2 := conjBFS_size_ge hr hN.ge
  rw [hN] at h1
  exact ⟨conjBFS_closedOK hr h1, le_antisymm h1 h2⟩

end CFSG.KS.LyFive.G2

end
