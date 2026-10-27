module

public import CFSG.GH74.Generic.S1.BlkSplit
public import CFSG.GH74.Generic.S45.PumpC1
public import CFSG.GH74.GLS.TwoThin.PumpData
public import CFSG.GH74.Generic.S1.SymLayer

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.LocalCores
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

theorem commutator_sup_self {X : Type*} [Group X] {A B : Subgroup X} (hA : ⁅A, A⁆ = A)
    (hB : ⁅B, B⁆ = B) : ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := by
  apply le_antisymm
  · exact Subgroup.commutator_le_self _
  · refine sup_le ?_ ?_
    · calc A = ⁅A, A⁆ := hA.symm
        _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc B = ⁅B, B⁆ := hB.symm
        _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem quasisimple_not_commutative {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ¬ ∀ a b : Q, a * b = b * a := by
  intro h
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])

theorem eq_or_eq_of_normal_sup {X : Type*} [Group X] [Finite X] {B J N : Subgroup X}
    (hBJ : ∀ b ∈ B, ∀ j ∈ J, b * j = j * b) (hBq : IsQuasisimple ↥B) (hJq : IsQuasisimple ↥J)
    (hNq : IsQuasisimple ↥N) (hNW : N ≤ B ⊔ J)
    (hNn : ∀ w ∈ B ⊔ J, ∀ n ∈ N, w * n * w⁻¹ ∈ N) : N = B ∨ N = J := by
  classical
  set W : Subgroup X := B ⊔ J with hW
  have hBW : B ≤ W := le_sup_left
  have hJW : J ≤ W := le_sup_right
  have hBJ_le : J ≤ centralizer (B : Set X) := fun j hj =>
    mem_centralizer_iff.2 fun b hb => (hBJ b hb j hj)
  have hJB_le : B ≤ centralizer (J : Set X) := fun b hb =>
    mem_centralizer_iff.2 fun j hj => (hBJ b hb j hj).symm
  have hBn : (B.subgroupOf W).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBW).2
      (sup_le le_normalizer (hBJ_le.trans (Subgroup.centralizer_le_normalizer _)))
  have hJn : (J.subgroupOf W).Normal :=
    (normal_subgroupOf_iff_le_normalizer hJW).2
      (sup_le (hJB_le.trans (Subgroup.centralizer_le_normalizer _)) le_normalizer)
  have hNn' : (N.subgroupOf W).Normal :=
    ⟨fun n hn g => mem_subgroupOf.2 (hNn g.1 g.2 n.1 (mem_subgroupOf.1 hn))⟩
  have hBc : IsComponent (B.subgroupOf W) :=
    ⟨isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hBW).symm hBq, hBn.isSubnormal⟩
  have hJc : IsComponent (J.subgroupOf W) :=
    ⟨isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJW).symm hJq, hJn.isSubnormal⟩
  have hNc : IsComponent (N.subgroupOf W) :=
    ⟨isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hNW).symm hNq, hNn'.isSubnormal⟩
  rcases distinct_components_commute hNc hBc with h1 | h1
  · left
    have := (Subgroup.subgroupOf_inj).1 h1
    rwa [inf_eq_left.2 hNW, inf_eq_left.2 hBW] at this
  rcases distinct_components_commute hNc hJc with h2 | h2
  · right
    have := (Subgroup.subgroupOf_inj).1 h2
    rwa [inf_eq_left.2 hNW, inf_eq_left.2 hJW] at this
  exfalso
  refine quasisimple_not_commutative (Q := ↥(N.subgroupOf W)) hNc.1 fun a b => ?_
  have hcB : N.subgroupOf W ≤ centralizer ((B.subgroupOf W : Subgroup ↥W) : Set ↥W) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1
  have hcJ : N.subgroupOf W ≤ centralizer ((J.subgroupOf W : Subgroup ↥W) : Set ↥W) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2
  have hsup : (B ⊔ J).subgroupOf W = B.subgroupOf W ⊔ J.subgroupOf W := subgroupOf_sup hBW hJW
  have hcW : ∀ n ∈ N.subgroupOf W, ∀ w : ↥W, w * n = n * w := by
    intro n hn w
    have hcent : B.subgroupOf W ⊔ J.subgroupOf W ≤ centralizer ({n} : Set ↥W) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.1 (hcB hn) w hw)
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.1 (hcJ hn) w hw)
    have htop : (⊤ : Subgroup ↥W) = B.subgroupOf W ⊔ J.subgroupOf W := by
      rw [← hsup, ← hW]
      exact (Subgroup.subgroupOf_self W).symm
    have hw : w ∈ B.subgroupOf W ⊔ J.subgroupOf W := by rw [← htop]; trivial
    exact (mem_centralizer_singleton_iff.1 (hcent hw))
  exact Subtype.ext (hcW (b : ↥W) b.2 (a : ↥W))


section PairNormal

variable (ops : BlockOps F S)

theorem pairLayer_conj_le {y : G} (D : LayerData y S) {a b c d : Fin 4} {z0 : ↥S}
    (hz0 : z0 ∈ ops.blk c d)
    (hbc : ∀ g ∈ ops.blk a b, ∀ h ∈ ops.blk c d, g * h = h * g)
    (hcent : ∀ g ∈ ops.blk c d, g * z0 = z0 * g)
    (hM2 : ∀ P : Subgroup ↥S, (∀ g ∈ P, g * z0 = z0 * g) → ⁅P, P⁆ = P →
      P ≤ ops.blk a b ⊔ ops.blk c d)
    {g : G} (hgy : g ∈ centralizer ({y} : Set G)) (hgc : g ∈ centralizer ({D.ι z0} : Set G))
    {A : Subgroup G} (hA : A ≤ (ops.blk a b ⊔ ops.blk c d).map D.ι) (hperf : ⁅A, A⁆ = A) :
    A.map (MulAut.conj g).toMonoidHom ≤ (ops.blk a b ⊔ ops.blk c d).map D.ι := by
  set A' : Subgroup G := A.map (MulAut.conj g).toMonoidHom with hA'
  have hA'perf : ⁅A', A'⁆ = A' := by
    rw [hA', ← Subgroup.map_commutator, hperf]
  have hWy : (ops.blk a b ⊔ ops.blk c d).map D.ι ≤ centralizer ({y} : Set G) := by
    rintro _ ⟨s, -, rfl⟩
    exact D.ι_mem_cent s
  have hA'y : A' ≤ centralizer ({y} : Set G) := by
    rintro _ ⟨a', ha', rfl⟩
    have h1 : a' ∈ centralizer ({y} : Set G) := hWy (hA ha')
    rw [mem_centralizer_singleton_iff] at h1 hgy ⊢
    have hgyC : Commute g y := hgy
    have h1C : Commute a' y := h1
    have := (Commute.mul_left hgyC h1C).mul_left hgyC.inv_left
    simpa [MulAut.conj_apply] using this.eq
  have hrange := D.le_range_ι hA'perf hA'y
  set P : Subgroup ↥S := A'.comap D.ι with hP
  have hmapP : P.map D.ι = A' := by
    rw [hP, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hrange
  have hPperf : ⁅P, P⁆ = P := by
    apply Subgroup.map_injective D.ι_injective
    rw [Subgroup.map_commutator, hmapP, hA'perf]
  have hWz : ∀ w ∈ ops.blk a b ⊔ ops.blk c d, w * z0 = z0 * w := by
    intro w hw
    have hle : ops.blk a b ⊔ ops.blk c d ≤ centralizer ({z0} : Set ↥S) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact (hbc w hw z0 hz0)
      · rw [mem_centralizer_singleton_iff]
        exact hcent w hw
    exact mem_centralizer_singleton_iff.1 (hle hw)
  have hPcomm : ∀ p ∈ P, p * z0 = z0 * p := by
    intro p hp
    have hpA' : D.ι p ∈ A' := hp
    obtain ⟨a', ha', hpa⟩ := hpA'
    obtain ⟨w, hw, rfl⟩ := hA ha'
    have h1 : D.ι w * D.ι z0 = D.ι z0 * D.ι w := by
      rw [← map_mul, ← map_mul, hWz w hw]
    have h2 : D.ι p * D.ι z0 = D.ι z0 * D.ι p := by
      have hgcC : Commute g (D.ι z0) := mem_centralizer_singleton_iff.1 hgc
      have h1C : Commute (D.ι w) (D.ι z0) := h1
      have := (Commute.mul_left hgcC h1C).mul_left hgcC.inv_left
      rw [← hpa]
      simpa [MulAut.conj_apply] using this.eq
    rw [← map_mul, ← map_mul] at h2
    exact D.ι_injective h2
  have hPle := hM2 P hPcomm hPperf
  rw [← hmapP]
  exact Subgroup.map_mono hPle

omit [Finite G] in
theorem pairConj_mem_iff {g : G} {A : Subgroup G} {x : G} :
    x ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [Finite G] in
theorem pairMap_conj_conj_inv (g : G) (A : Subgroup G) :
    (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro hx
    exact ⟨g⁻¹ * x * g, ⟨x, hx, by simp [mul_assoc]⟩, by
      simp [MulAut.conj_apply, mul_assoc]⟩

theorem pairLayer_normal {y : G} (D : LayerData y S) {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d)
    {z0 : ↥S} (hz0 : z0 ∈ ops.blk c d) (hz01 : z0 ≠ 1)
    (hbc : ∀ g ∈ ops.blk a b, ∀ h ∈ ops.blk c d, g * h = h * g)
    (hcent : ∀ g ∈ ops.blk c d, g * z0 = z0 * g)
    (hM2 : ∀ P : Subgroup ↥S, (∀ g ∈ P, g * z0 = z0 * g) → ⁅P, P⁆ = P →
      P ≤ ops.blk a b ⊔ ops.blk c d)
    (hinf : ops.blk a b ⊓ ops.blk c d = ⊥)
    (hBq : IsQuasisimple ↥((ops.blk a b).map D.ι)) (hJq : IsQuasisimple ↥((ops.blk c d).map D.ι))
    {g : G} (hgy : g ∈ centralizer ({y} : Set G)) (hgc : g ∈ centralizer ({D.ι z0} : Set G)) :
    ((ops.blk a b).map D.ι).map (MulAut.conj g).toMonoidHom = (ops.blk a b).map D.ι ∧
      ((ops.blk c d).map D.ι).map (MulAut.conj g).toMonoidHom = (ops.blk c d).map D.ι := by
  set B : Subgroup G := (ops.blk a b).map D.ι with hB
  set J : Subgroup G := (ops.blk c d).map D.ι with hJ
  have hW : (ops.blk a b ⊔ ops.blk c d).map D.ι = B ⊔ J := Subgroup.map_sup _ _ _
  have hBperf : ⁅B, B⁆ = B := by
    rw [hB, ← Subgroup.map_commutator, ops.perfect a b hab]
  have hJperf : ⁅J, J⁆ = J := by
    rw [hJ, ← Subgroup.map_commutator, ops.perfect c d hcd]
  have hBJ : ∀ u ∈ B, ∀ v ∈ J, u * v = v * u := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul, hbc u hu v hv]
  have hWperf : ⁅B ⊔ J, B ⊔ J⁆ = B ⊔ J := commutator_sup_self hBperf hJperf
  have hgc' : g⁻¹ ∈ centralizer ({D.ι z0} : Set G) := (centralizer _).inv_mem hgc
  have hgy' : g⁻¹ ∈ centralizer ({y} : Set G) := (centralizer _).inv_mem hgy
  have hle : ∀ (h : G), h ∈ centralizer ({y} : Set G) → h ∈ centralizer ({D.ι z0} : Set G) →
      ∀ A : Subgroup G, A ≤ B ⊔ J → ⁅A, A⁆ = A → A.map (MulAut.conj h).toMonoidHom ≤ B ⊔ J := by
    intro h hhy hhc A hA hAp
    have := pairLayer_conj_le ops D hz0 hbc hcent hM2 hhy hhc (A := A) (by rw [hW]; exact hA) hAp
    rwa [hW] at this
  have hgW : (B ⊔ J).map (MulAut.conj g).toMonoidHom = B ⊔ J := by
    refine le_antisymm (hle g hgy hgc _ le_rfl hWperf) ?_
    have h1 := hle g⁻¹ hgy' hgc' _ le_rfl hWperf
    calc B ⊔ J = ((B ⊔ J).map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
          (pairMap_conj_conj_inv g _).symm
      _ ≤ (B ⊔ J).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono h1
  have hBn : ∀ w ∈ B ⊔ J, ∀ n ∈ B, w * n * w⁻¹ ∈ B := by
    have hle' : B ⊔ J ≤ normalizer (B : Set G) := by
      refine sup_le le_normalizer ?_
      intro j hj
      have : j ∈ centralizer (B : Set G) := mem_centralizer_iff.2 fun b hb => (hBJ b hb j hj)
      exact Subgroup.centralizer_le_normalizer _ this
    intro w hw n hn
    exact (mem_normalizer_iff.1 (hle' hw) n).1 hn
  have hJn : ∀ w ∈ B ⊔ J, ∀ n ∈ J, w * n * w⁻¹ ∈ J := by
    have hle' : B ⊔ J ≤ normalizer (J : Set G) := by
      refine sup_le ?_ le_normalizer
      intro b hb
      have : b ∈ centralizer (J : Set G) := mem_centralizer_iff.2 fun j hj => (hBJ b hb j hj).symm
      exact Subgroup.centralizer_le_normalizer _ this
    intro w hw n hn
    exact (mem_normalizer_iff.1 (hle' hw) n).1 hn
  have hcJ : D.ι z0 ∈ J := ⟨z0, hz0, rfl⟩
  have hcBJ : D.ι z0 ∉ B := by
    intro hcB
    have h1 : D.ι z0 ∈ B ⊓ J := ⟨hcB, hcJ⟩
    have h2 : B ⊓ J = ⊥ := by
      rw [hB, hJ, ← Subgroup.map_inf_eq _ _ _ D.ι_injective, hinf, Subgroup.map_bot]
    rw [h2, Subgroup.mem_bot] at h1
    exact hz01 (D.ι_injective (by rw [h1, map_one]))
  have hgcc : g⁻¹ * D.ι z0 * g = D.ι z0 := by
    have := mem_centralizer_singleton_iff.1 hgc
    calc g⁻¹ * D.ι z0 * g = g⁻¹ * (D.ι z0 * g) := by group
      _ = g⁻¹ * (g * D.ι z0) := by rw [this]
      _ = D.ι z0 := by group
  have hgcc' : g * D.ι z0 * g⁻¹ = D.ι z0 := by
    have := mem_centralizer_singleton_iff.1 hgc
    calc g * D.ι z0 * g⁻¹ = (g * D.ι z0) * g⁻¹ := by group
      _ = (D.ι z0 * g) * g⁻¹ := by rw [this]
      _ = D.ι z0 := by group
  refine ⟨?_, ?_⟩
  ·
    have hNW : B.map (MulAut.conj g).toMonoidHom ≤ B ⊔ J := hle g hgy hgc B le_sup_left hBperf
    have hNq : IsQuasisimple ↥(B.map (MulAut.conj g).toMonoidHom) :=
      isQuasisimple_of_mulEquiv (B.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective) hBq
    have hNn : ∀ w ∈ B ⊔ J, ∀ n ∈ B.map (MulAut.conj g).toMonoidHom,
        w * n * w⁻¹ ∈ B.map (MulAut.conj g).toMonoidHom := by
      intro w hw n hn
      have hw' : w ∈ (B ⊔ J).map (MulAut.conj g).toMonoidHom := by rw [hgW]; exact hw
      rw [pairConj_mem_iff] at hw' hn ⊢
      have := hBn _ hw' _ hn
      convert this using 1
      group
    rcases eq_or_eq_of_normal_sup hBJ hBq hJq hNq hNW hNn with h | h
    · exact h
    · exfalso
      apply hcBJ
      have : D.ι z0 ∈ B.map (MulAut.conj g).toMonoidHom := by rw [h]; exact hcJ
      rw [pairConj_mem_iff, hgcc] at this
      exact this
  ·
    have hNW : J.map (MulAut.conj g).toMonoidHom ≤ B ⊔ J := hle g hgy hgc J le_sup_right hJperf
    have hNq : IsQuasisimple ↥(J.map (MulAut.conj g).toMonoidHom) :=
      isQuasisimple_of_mulEquiv (J.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective) hJq
    have hNn : ∀ w ∈ B ⊔ J, ∀ n ∈ J.map (MulAut.conj g).toMonoidHom,
        w * n * w⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom := by
      intro w hw n hn
      have hw' : w ∈ (B ⊔ J).map (MulAut.conj g).toMonoidHom := by rw [hgW]; exact hw
      rw [pairConj_mem_iff] at hw' hn ⊢
      have := hJn _ hw' _ hn
      convert this using 1
      group
    rcases eq_or_eq_of_normal_sup hBJ hBq hJq hNq hNW hNn with h | h
    · exfalso
      apply hcBJ
      have : D.ι z0 ∈ J.map (MulAut.conj g).toMonoidHom := by
        rw [pairConj_mem_iff, hgcc]; exact hcJ
      rw [h] at this
      exact this
    · exact h

end PairNormal


section TwoComp

theorem isPCompIn_of_normal_block {V B : Subgroup G} (hBV : B ≤ V)
    (hn : ∀ g ∈ V, ∀ u ∈ B, g * u * g⁻¹ ∈ B) (hq : IsQuasisimple ↥B) :
    CFSG.GH74.GLS.IsPCompIn 2 V B := by
  have hBn : (B.subgroupOf V).Normal :=
    ⟨fun n hn' g => mem_subgroupOf.2 (hn g.1 g.2 n.1 (mem_subgroupOf.1 hn'))⟩
  have hcomp : IsComponent (B.subgroupOf V) :=
    ⟨isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hBV).symm hq, hBn.isSubnormal⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCO : Group.IsSolvable (pPrimeCore 2 ↥V) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    have := pPrimeCore_coprime_card (p := 2) (G := ↥V)
    exact (Nat.coprime_two_left.1 this)
  exact ⟨hBV, CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hcomp
    (CFSG.LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hcomp hCO)⟩


theorem layerPair_normal (ops : BlockOps F S) (hpf : PairFacts ops)
    (hblkq : ∀ a b : Fin 4, a ≠ b → IsQuasisimple ↥(ops.blk a b)) {y : G} (D : LayerData y S)
    {a b c d : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) {z0 : ↥S} (hz0 : z0 ∈ ops.blk c d) (hz0sq : z0 * z0 = 1) (hz01 : z0 ≠ 1)
    (hcent : ∀ g ∈ ops.blk c d, g * z0 = z0 * g) :
    ∀ g ∈ centralizer ({y} : Set G) ⊓ centralizer ({D.ι z0} : Set G),
      ((ops.blk a b).map D.ι).map (MulAut.conj g).toMonoidHom = (ops.blk a b).map D.ι ∧
      ((ops.blk c d).map D.ι).map (MulAut.conj g).toMonoidHom = (ops.blk c d).map D.ι := by
  have hcomm := ops.commute a b c d hab hcd hac had hbc hbd
  have hBq : IsQuasisimple ↥((ops.blk a b).map D.ι) :=
    isQuasisimple_of_mulEquiv ((ops.blk a b).equivMapOfInjective D.ι D.ι_injective) (hblkq a b hab)
  have hJq : IsQuasisimple ↥((ops.blk c d).map D.ι) :=
    isQuasisimple_of_mulEquiv ((ops.blk c d).equivMapOfInjective D.ι D.ι_injective) (hblkq c d hcd)
  have hM2 := hpf.perf_le a b c d hab hac had hbc hbd hcd z0 hz0 hz0sq hz01
  have hinf := hpf.inf_bot a b c d hab hcd hac had hbc hbd
  intro g hg
  exact pairLayer_normal ops D hab hcd hz0 hz01 hcomm hcent hM2 hinf hBq hJq hg.1 hg.2

theorem layerPair_isPCompIn (ops : BlockOps F S) (hpf : PairFacts ops)
    (hblkq : ∀ a b : Fin 4, a ≠ b → IsQuasisimple ↥(ops.blk a b)) {y : G} (D : LayerData y S)
    {a b c d : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) {z0 : ↥S} (hz0 : z0 ∈ ops.blk c d) (hz0sq : z0 * z0 = 1) (hz01 : z0 ≠ 1)
    (hcent : ∀ g ∈ ops.blk c d, g * z0 = z0 * g) :
    CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({y} : Set G) ⊓ centralizer ({D.ι z0} : Set G))
        ((ops.blk a b).map D.ι) ∧
      CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({y} : Set G) ⊓ centralizer ({D.ι z0} : Set G))
        ((ops.blk c d).map D.ι) := by
  have hcomm := ops.commute a b c d hab hcd hac had hbc hbd
  have hBq : IsQuasisimple ↥((ops.blk a b).map D.ι) :=
    isQuasisimple_of_mulEquiv ((ops.blk a b).equivMapOfInjective D.ι D.ι_injective) (hblkq a b hab)
  have hJq : IsQuasisimple ↥((ops.blk c d).map D.ι) :=
    isQuasisimple_of_mulEquiv ((ops.blk c d).equivMapOfInjective D.ι D.ι_injective) (hblkq c d hcd)
  have hBV : (ops.blk a b).map D.ι ≤ centralizer ({y} : Set G) ⊓ centralizer ({D.ι z0} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    refine Subgroup.mem_inf.2 ⟨D.ι_mem_cent s, ?_⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcomm s hs z0 hz0]
  have hJV : (ops.blk c d).map D.ι ≤ centralizer ({y} : Set G) ⊓ centralizer ({D.ι z0} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    refine Subgroup.mem_inf.2 ⟨D.ι_mem_cent s, ?_⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcent s hs]
  have hnorm := layerPair_normal ops hpf hblkq D hab hac had hbc hbd hcd hz0 hz0sq hz01 hcent
  refine ⟨isPCompIn_of_normal_block hBV (fun g hg u hu => ?_) hBq,
    isPCompIn_of_normal_block hJV (fun g hg u hu => ?_) hJq⟩
  · have := (hnorm g hg).1
    rw [← this]
    exact ⟨u, hu, by simp [MulAut.conj_apply]⟩
  · have := (hnorm g hg).2
    rw [← this]
    exact ⟨u, hu, by simp [MulAut.conj_apply]⟩


theorem barSub_le_layer_of_isPCompIn {c s : G} (hs : orderOf s = 2)
    (hsc : s ∈ centralizer ({c} : Set G)) {B : Subgroup G}
    (hB : CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({s} : Set G) ⊓ centralizer ({c} : Set G)) B) :
    S45.barSub c B ≤ layer (CentralizerBar c) := by
  have hs' := CFSG.GH74.GLS.TwoThin.orderOf_mk_centralizer hsc hs
  have hΛC := CFSG.GH74.GLS.TwoThin.le_centralizer_mk hB.1 hsc
  have hΛ := CFSG.GH74.GLS.TwoThin.isTwoComponent_centralizer_mk hB hsc
  exact CFSG.GH74.GLS.TwoThin.map_barMk_le_layer hs' hΛC hΛ

end TwoComp


end CFSG.GH74.Generic.S1
