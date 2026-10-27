module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.KCut
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.Quasithin.Background.D2Offenders

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.KCut

structure CutData (G : Type) [Group G] where
  A : Set G
  Q : G → Subgroup G
  a : G
  b : G
  A_inv : ∀ z ∈ A, z * z = 1 ∧ z ≠ 1
  A_conj : ∀ z ∈ A, ∀ z' ∈ A, ∃ g : G, z' = g * z * g⁻¹
  ha : a ∈ A
  hb : b ∈ A
  hab : a * b ∈ A
  hab_comm : a * b = b * a
  hab_ne : a ≠ b
  gen₁ : Subgroup.centralizer {a} ⊔ Subgroup.centralizer {b} = ⊤
  gen₂ : Subgroup.centralizer {a} ⊔ Subgroup.centralizer {a * b} = ⊤
  gen₃ : Subgroup.centralizer {b} ⊔ Subgroup.centralizer {a * b} = ⊤
  dich : ∀ z ∈ A, ∀ N : Subgroup G, N ≤ Subgroup.centralizer {z} →
    (∀ c ∈ Subgroup.centralizer {z}, ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
      N ≤ Q z ∨ N = Subgroup.centralizer {z}
  Q_rank : ∀ z ∈ A, ∀ B : Subgroup G, B ≤ Q z → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 5
  noA_rank : ∀ B : Subgroup G, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
    (∀ x ∈ B, x ≠ 1 → x ∉ A) → Nat.card B ≤ 2 ^ 5
  heisA : ∀ t ∈ A, ∃ (x y : Fin (0 + 1) → G) (z : G), HeisCfg 5 (0 + 1) x y z ∧
    t * x 0 * t⁻¹ = (x 0)⁻¹
  dihNonA : ∀ t : G, t * t = 1 → t ≠ 1 → t ∉ A → ∃ c : G, orderOf (t * (c * t * c⁻¹)) = 13

section Base

variable {G : Type} [Group G]

@[expose] def classOf (a₀ : G) : Set G := {z | ∃ g : G, z = g * a₀ * g⁻¹}

theorem mem_centralizer_conj {g x y : G} :
    g * y * g⁻¹ ∈ Subgroup.centralizer {g * x * g⁻¹} ↔ y ∈ Subgroup.centralizer {x} := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
      calc g * (y * x) * g⁻¹ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
        _ = g * x * g⁻¹ * (g * y * g⁻¹) := h
        _ = g * (x * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)
  · intro h
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group

theorem gen_conj {u v : G} (h : Subgroup.centralizer {u} ⊔ Subgroup.centralizer {v} = ⊤)
    (g : G) :
    Subgroup.centralizer {g * u * g⁻¹} ⊔ Subgroup.centralizer {g * v * g⁻¹} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : g⁻¹ * x * g ∈ Subgroup.centralizer {u} ⊔ Subgroup.centralizer {v} := by
    rw [h]; trivial
  have key : ∀ y : G, y ∈ Subgroup.centralizer {u} ⊔ Subgroup.centralizer {v} →
      g * y * g⁻¹ ∈ Subgroup.centralizer {g * u * g⁻¹} ⊔ Subgroup.centralizer {g * v * g⁻¹} := by
    intro y hy
    refine sup_induction' (p := fun y : G => g * y * g⁻¹ ∈ Subgroup.centralizer {g * u * g⁻¹} ⊔
      Subgroup.centralizer {g * v * g⁻¹}) hy ?_ ?_ ?_ ?_ ?_
    · intro y hy
      exact Subgroup.mem_sup_left (mem_centralizer_conj.2 hy)
    · intro y hy
      exact Subgroup.mem_sup_right (mem_centralizer_conj.2 hy)
    · simp
    · intro a b ha hb
      have := Subgroup.mul_mem _ ha hb
      simpa [mul_assoc] using this
    · intro a ha
      have := Subgroup.inv_mem _ ha
      simpa [mul_assoc] using this
  have := key _ hx
  simpa [mul_assoc] using this

open scoped Classical in
theorem exists_Q_of_base (a₀ : G) (Q₀ : Subgroup G)
    (hdich₀ : ∀ N : Subgroup G, N ≤ Subgroup.centralizer {a₀} →
      (∀ c ∈ Subgroup.centralizer {a₀}, ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
        N ≤ Q₀ ∨ N = Subgroup.centralizer {a₀})
    (hrank₀ : ∀ B : Subgroup G, B ≤ Q₀ → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 5) :
    ∃ Q : G → Subgroup G,
      (∀ z ∈ classOf a₀, ∀ N : Subgroup G, N ≤ Subgroup.centralizer {z} →
        (∀ c ∈ Subgroup.centralizer {z}, ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
          N ≤ Q z ∨ N = Subgroup.centralizer {z}) ∧
      (∀ z ∈ classOf a₀, ∀ B : Subgroup G, B ≤ Q z → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
        (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 5) := by
  let cv : G → G := fun z => if h : ∃ g : G, z = g * a₀ * g⁻¹ then h.choose else 1
  have hcv : ∀ z ∈ classOf a₀, z = cv z * a₀ * (cv z)⁻¹ := by
    intro z hz
    have h : ∃ g : G, z = g * a₀ * g⁻¹ := hz
    simp only [cv, h, ↓reduceDIte]
    exact h.choose_spec
  refine ⟨fun z => Q₀.map (MulAut.conj (cv z)).toMonoidHom, ?_, ?_⟩
  · intro z hz N hNz hnorm
    have hzg := hcv z hz
    beta_reduce
    generalize cv z = g at hzg ⊢
    set N' : Subgroup G := N.comap (MulAut.conj g).toMonoidHom with hN'
    have hmemN' : ∀ x, x ∈ N' ↔ g * x * g⁻¹ ∈ N := fun x => Iff.rfl
    have h1 : N' ≤ Subgroup.centralizer {a₀} := by
      intro x hx
      have := hNz ((hmemN' x).1 hx)
      rw [hzg] at this
      exact mem_centralizer_conj.1 this
    have h2 : ∀ c ∈ Subgroup.centralizer {a₀}, ∀ n ∈ N', c * n * c⁻¹ ∈ N' := by
      intro c hc n hn
      have hcz : g * c * g⁻¹ ∈ Subgroup.centralizer {z} := by
        rw [hzg]; exact mem_centralizer_conj.2 hc
      have := hnorm _ hcz _ ((hmemN' n).1 hn)
      rw [hmemN']
      simpa [mul_assoc] using this
    rcases hdich₀ N' h1 h2 with h | h
    · left
      intro x hx
      have : g⁻¹ * x * g ∈ N' := by
        rw [hmemN']; simpa [mul_assoc] using hx
      exact ⟨g⁻¹ * x * g, h this, by simp [mul_assoc]⟩
    · right
      refine le_antisymm hNz fun x hx => ?_
      have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer {a₀} := by
        have : g⁻¹ * x * g ∈ Subgroup.centralizer {g⁻¹ * z * g} := by
          have := (mem_centralizer_conj (g := g⁻¹) (x := z) (y := x)).2 hx
          simpa using this
        have e : g⁻¹ * z * g = a₀ := by rw [hzg]; group
        rwa [e] at this
      rw [← h, hmemN'] at hx'
      simpa [mul_assoc] using hx'
  · intro z hz B hB hcomm hsq
    beta_reduce at hB
    generalize cv z = g at hB
    set B' : Subgroup G := B.comap (MulAut.conj g).toMonoidHom with hB'
    have hB'Q : B' ≤ Q₀ := by
      intro x hx
      have : g * x * g⁻¹ ∈ B := hx
      obtain ⟨q, hq, hqe⟩ := hB this
      have : x = q := by
        have h2 : g * q * g⁻¹ = g * x * g⁻¹ := hqe
        exact mul_left_cancel (mul_right_cancel h2) |>.symm
      rw [this]; exact hq
    have hcard : Nat.card B' = Nat.card B := by
      have : B' = B.map (MulAut.conj g⁻¹).toMonoidHom := by
        ext x
        simp only [hB', Subgroup.mem_comap, Subgroup.mem_map]
        constructor
        · intro hx
          exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩
        · rintro ⟨y, hy, rfl⟩
          simpa [mul_assoc] using hy
      rw [this]
      exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    rw [← hcard]
    refine hrank₀ B' hB'Q ?_ ?_
    · intro x hx y hy
      have h3 := hcomm _ hx _ hy
      have : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
        calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
          _ = g * y * g⁻¹ * (g * x * g⁻¹) := h3
          _ = g * (y * x) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel this)
    · intro x hx
      have h3 := hsq _ hx
      have : g * (x * x) * g⁻¹ = 1 := by
        calc g * (x * x) * g⁻¹ = g * x * g⁻¹ * (g * x * g⁻¹) := by group
          _ = 1 := h3
      have h4 : g * (x * x) * g⁻¹ = g * 1 * g⁻¹ := by rw [this]; group
      exact mul_left_cancel (mul_right_cancel h4)

end Base

section Transport

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {G : Type} [Group G]
  (φ : ↥L ≃* G)

@[expose] def AL (A : Set G) : Set (MulAut W) := {y | ∃ h : y ∈ L, φ ⟨y, h⟩ ∈ A}

open scoped Classical in
@[expose] noncomputable def QL (Q : G → Subgroup G) : MulAut W → Subgroup (MulAut W) :=
  fun y => if h : y ∈ L then ((Q (φ ⟨y, h⟩)).comap φ.toMonoidHom).map L.subtype else ⊥

theorem mem_QL {Q : G → Subgroup G} {y : MulAut W} (hy : y ∈ L) {k : MulAut W} :
    k ∈ QL φ Q y ↔ ∃ hk : k ∈ L, φ ⟨k, hk⟩ ∈ Q (φ ⟨y, hy⟩) := by
  have hQ : QL φ Q y = ((Q (φ ⟨y, hy⟩)).comap φ.toMonoidHom).map L.subtype := by
    simp [QL, hy]
  rw [hQ, Subgroup.mem_map]
  constructor
  · rintro ⟨k', hk', rfl⟩
    exact ⟨k'.2, hk'⟩
  · rintro ⟨hk, hk'⟩
    exact ⟨⟨k, hk⟩, hk', rfl⟩

theorem genPair_of_top {u v : MulAut W} (hu : u ∈ L) (hv : v ∈ L)
    (h : Subgroup.centralizer {φ ⟨u, hu⟩} ⊔ Subgroup.centralizer {φ ⟨v, hv⟩} = ⊤) :
    GenPair L u v := by
  unfold GenPair
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx => ?_
  have hmem : φ ⟨x, hx⟩ ∈ Subgroup.centralizer {φ ⟨u, hu⟩} ⊔
      Subgroup.centralizer {φ ⟨v, hv⟩} := by rw [h]; trivial
  have key : ∀ g : G, g ∈ Subgroup.centralizer {φ ⟨u, hu⟩} ⊔
      Subgroup.centralizer {φ ⟨v, hv⟩} →
      ((φ.symm g : ↥L) : MulAut W) ∈ (L ⊓ Subgroup.centralizer {u}) ⊔
        (L ⊓ Subgroup.centralizer {v}) := by
    intro g hg
    refine sup_induction' (p := fun g : G => ((φ.symm g : ↥L) : MulAut W) ∈
      (L ⊓ Subgroup.centralizer {u}) ⊔ (L ⊓ Subgroup.centralizer {v})) hg ?_ ?_ ?_ ?_ ?_
    · intro g hg
      refine Subgroup.mem_sup_left ⟨(φ.symm g).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.1 hg
      have h2 := congrArg (fun z => ((φ.symm z : ↥L) : MulAut W)) this
      simpa [map_mul] using h2
    · intro g hg
      refine Subgroup.mem_sup_right ⟨(φ.symm g).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.1 hg
      have h2 := congrArg (fun z => ((φ.symm z : ↥L) : MulAut W)) this
      simpa [map_mul] using h2
    · simp
    · intro a b ha hb
      have := Subgroup.mul_mem _ ha hb
      simpa [map_mul] using this
    · intro a ha
      have := Subgroup.inv_mem _ ha
      simpa [map_inv] using this
  simpa using key _ hmem

theorem dich_L {A : Set G} {Q : G → Subgroup G}
    (hdich : ∀ z ∈ A, ∀ N : Subgroup G, N ≤ Subgroup.centralizer {z} →
      (∀ c ∈ Subgroup.centralizer {z}, ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
        N ≤ Q z ∨ N = Subgroup.centralizer {z})
    {y : MulAut W} (hy : y ∈ L) (hyA : φ ⟨y, hy⟩ ∈ A) :
    Kgrp L y ≤ QL φ Q y ∨ Kgrp L y = L ⊓ Subgroup.centralizer {y} := by
  set N : Subgroup G := ((Kgrp L y).subgroupOf L).map φ.toMonoidHom with hN
  have hN1 : N ≤ Subgroup.centralizer {φ ⟨y, hy⟩} := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hkc := Subgroup.mem_centralizer_singleton_iff.1 (Kgrp_le_centralizer L y hk)
    have : k * ⟨y, hy⟩ = ⟨y, hy⟩ * k := Subtype.ext hkc
    simpa [map_mul] using congrArg φ this
  have hN2 : ∀ c ∈ Subgroup.centralizer {φ ⟨y, hy⟩}, ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    rintro c hc _ ⟨k, hk, rfl⟩
    have hcc := Subgroup.mem_centralizer_singleton_iff.1 hc
    have hc' : (φ.symm c : ↥L) * ⟨y, hy⟩ = ⟨y, hy⟩ * φ.symm c := by
      have := congrArg φ.symm hcc
      simpa [map_mul] using this
    have hcy : ((φ.symm c : ↥L) : MulAut W) * y = y * ((φ.symm c : ↥L) : MulAut W) :=
      congrArg Subtype.val hc'
    have hkK : (k : MulAut W) ∈ Kgrp L y := hk
    have := Kgrp_cent_mem (φ.symm c).2 hcy hkK
    refine ⟨φ.symm c * k * (φ.symm c)⁻¹, ?_, by simp⟩
    exact this
  rcases hdich _ hyA N hN1 hN2 with h | h
  · left
    intro k hk
    have hkL : k ∈ L := Kgrp_le L y hk
    refine (mem_QL φ hy).2 ⟨hkL, h ⟨⟨k, hkL⟩, hk, rfl⟩⟩
  · right
    refine le_antisymm (Kgrp_le_cent L y) fun k hk => ?_
    have hmem : φ ⟨k, hk.1⟩ ∈ Subgroup.centralizer {φ ⟨y, hy⟩} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.1 hk.2
      have h2 : (⟨k, hk.1⟩ : ↥L) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨k, hk.1⟩ := Subtype.ext this
      rw [← map_mul, ← map_mul, h2]
    rw [← h] at hmem
    obtain ⟨k', hk', hkk⟩ := hmem
    have : k' = ⟨k, hk.1⟩ := φ.injective hkk
    have hk2 : (k' : MulAut W) ∈ Kgrp L y := hk'
    rw [this] at hk2
    exact hk2

end Transport

theorem card_map_eq_of_le {W : Type} [CommGroup W] {L E : Subgroup (MulAut W)} {G : Type} [Group G]
    (φ : ↥L ≃* G) (hEL : E ≤ L) :
    Nat.card ((E.subgroupOf L).map φ.toMonoidHom) = Nat.card E := by
  rw [Subgroup.card_map_of_injective φ.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv

theorem card_le_of_quadratic_cut {W : Type} [CommGroup W] [Finite W] [Nontrivial W]
    (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)} {G : Type} [Group G] (D : CutData G)
    (φ : ↥L ≃* G) (hirr : IsIrrOn L) (hL : L ≠ ⊥) (hEL : E ≤ L) (hel : IsElemAbelian2 E)
    (hquad : IsQuadratic E) : Nat.card E ≤ 2 ^ 5 := by
  have hfix : fixV L = ⊥ := fixV_eq_bot_of_irr hirr hL
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hel.2 x hx
  by_cases hsmall : Nat.card E ≤ 3
  · omega
  push Not at hsmall
  have hc : (E : Set (MulAut W)).ncard = Nat.card E := (Nat.card_coe_set_eq _).symm
  have hfall : ∀ x : MulAut W, ∃ f ∈ E, f ≠ 1 ∧ f ≠ x := by
    intro x
    by_contra hcon
    push Not at hcon
    have hsub : (E : Set (MulAut W)) ⊆ {1, x} := fun y hy => by
      by_cases h1 : y = 1
      · exact Or.inl h1
      · exact Or.inr (hcon y hy h1)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, x} : Set (MulAut W)).ncard ≤ 2 :=
      (Set.ncard_insert_le 1 {x}).trans (by simp)
    rw [hc] at this
    omega
  set Eb : Subgroup G := (E.subgroupOf L).map φ.toMonoidHom with hEb
  have hEbcard : Nat.card Eb = Nat.card E := card_map_eq_of_le φ hEL
  have hcommEb : ∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x := by
    rintro _ ⟨k₁, hk₁, rfl⟩ _ ⟨k₂, hk₂, rfl⟩
    have : k₁ * k₂ = k₂ * k₁ := Subtype.ext (hel.1 _ hk₁ _ hk₂)
    simp only [← map_mul, this]
  have hsqEb : ∀ x ∈ Eb, x * x = 1 := by
    rintro _ ⟨k, hk, rfl⟩
    have : k * k = 1 := Subtype.ext (hEsq _ hk)
    simp only [← map_mul, this, map_one]
  by_cases hA : ∃ x ∈ E, x ≠ 1 ∧ ∃ h : x ∈ L, φ ⟨x, h⟩ ∈ D.A
  · obtain ⟨x, hxE, hx1, hxL, hxA⟩ := hA
    obtain ⟨f, hfE, hf1, hfx⟩ := hfall x
    have hEK : E ≤ Kgrp L x := le_Kgrp_of_isQuadratic hEL hel hquad hxE hx1 hfE hf1 hfx
    have e1 : ∀ g : G, φ ⟨((φ.symm g : ↥L) : MulAut W), (φ.symm g).2⟩ = g := fun g => by simp
    have hmul : ∀ g h : G, ((φ.symm g : ↥L) : MulAut W) * ((φ.symm h : ↥L) : MulAut W) =
        ((φ.symm (g * h) : ↥L) : MulAut W) := fun g h => by simp [map_mul]
    set aL : MulAut W := ((φ.symm D.a : ↥L) : MulAut W) with haL
    set bL : MulAut W := ((φ.symm D.b : ↥L) : MulAut W) with hbL
    have haL_mem : aL ∈ L := (φ.symm D.a).2
    have hbL_mem : bL ∈ L := (φ.symm D.b).2
    have habL_mem : aL * bL ∈ L := L.mul_mem haL_mem hbL_mem
    have e2 : φ ⟨aL * bL, habL_mem⟩ = D.a * D.b := by
      have : (⟨aL * bL, habL_mem⟩ : ↥L) = φ.symm D.a * φ.symm D.b := Subtype.ext rfl
      rw [this, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have hkey : ∀ z ∈ AL φ D.A, Kgrp L z ≤ QL φ D.Q z := by
      refine Kgrp_le_of_dichotomy hW hirr.2 hfix (AL φ D.A) ?_ ?_ ?_ (QL φ D.Q) ?_
        (a := aL) (b := bL) ⟨haL_mem, by rw [e1]; exact D.ha⟩ ⟨hbL_mem, by rw [e1]; exact D.hb⟩
        ⟨habL_mem, by rw [e2]; exact D.hab⟩ ?_ ?_ ?_ ?_ ?_
      · rintro z ⟨hz, hzA⟩
        have := (D.A_inv _ hzA).1
        have h2 : (⟨z, hz⟩ : ↥L) * ⟨z, hz⟩ = 1 := φ.injective (by rw [map_mul, map_one]; exact this)
        exact congrArg Subtype.val h2
      · rintro z ⟨hz, hzA⟩ hz1
        apply (D.A_inv _ hzA).2
        have : (⟨z, hz⟩ : ↥L) = 1 := Subtype.ext hz1
        rw [this, map_one]
      · rintro z ⟨hz, hzA⟩ z' ⟨hz', hz'A⟩
        obtain ⟨g, hg⟩ := D.A_conj _ hzA _ hz'A
        refine ⟨((φ.symm g : ↥L) : MulAut W), (φ.symm g).2, ?_⟩
        have h2 : (⟨z', hz'⟩ : ↥L) = φ.symm g * ⟨z, hz⟩ * (φ.symm g)⁻¹ := by
          apply φ.injective
          rw [hg]; simp [map_mul]
        exact congrArg Subtype.val h2
      · rintro z ⟨hz, hzA⟩
        exact dich_L φ D.dich hz hzA
      · have h2 : aL * bL = bL * aL := by
          rw [hmul, hmul, D.hab_comm]
        exact h2
      · intro h
        exact D.hab_ne (φ.symm.injective (Subtype.ext h))
      · exact genPair_of_top φ haL_mem hbL_mem (by rw [e1, e1]; exact D.gen₁)
      · exact genPair_of_top φ haL_mem habL_mem (by rw [e1, e2]; exact D.gen₂)
      · exact genPair_of_top φ hbL_mem habL_mem (by rw [e1, e2]; exact D.gen₃)
    have hEQ : E ≤ QL φ D.Q x := hEK.trans (hkey x ⟨hxL, hxA⟩)
    have hEbQ : Eb ≤ D.Q (φ ⟨x, hxL⟩) := by
      rintro _ ⟨k, hk, rfl⟩
      have := hEQ hk
      obtain ⟨hk', hk''⟩ := (mem_QL φ hxL).1 this
      exact hk''
    rw [← hEbcard]
    exact D.Q_rank _ hxA Eb hEbQ hcommEb hsqEb
  · push Not at hA
    rw [← hEbcard]
    refine D.noA_rank Eb hcommEb hsqEb ?_
    rintro _ ⟨k, hk, rfl⟩ hne hmem
    have hk1 : (k : MulAut W) ≠ 1 := fun h => hne (by
      have : k = 1 := Subtype.ext h
      simp [this])
    exact hA k hk hk1 k.2 hmem

theorem orderOf_two_zmod_five_cut : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_two_zmod_thirteen_cut : orderOf (2 : ZMod 13) = 12 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem index_ge_of_cut {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)} {G : Type} [Group G] (D : CutData G) (hirr : IsIrrOn L)
    (e : CQ L ≃* G) (φ : ↥L ≃* G) (hφ : ∀ x : ↥L, φ x = e (QuotientGroup.mk x)) {b : MulAut W}
    (hb : b ∈ L) (hb1 : b ≠ 1) (hb2 : b * b = 1) :
    2 ^ 6 ≤ (fixV (Subgroup.zpowers b)).index := by
  have ht2 : e (QuotientGroup.mk ⟨b, hb⟩) * e (QuotientGroup.mk ⟨b, hb⟩) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul, ← map_one e, ← QuotientGroup.mk_one]
    congr 2
    exact Subtype.ext hb2
  have ht1 : e (QuotientGroup.mk ⟨b, hb⟩) ≠ 1 := by
    intro h
    apply hb1
    have h1 : (QuotientGroup.mk (⟨b, hb⟩ : ↥L) : CQ L) = 1 := e.injective (by rw [h, map_one])
    rw [QuotientGroup.eq_one_iff] at h1
    refine eq_one_of_commutes_of_sq_eq_one hW hirr (fun l hl => ?_) hb2
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 h1 ⟨l, hl⟩)
  set t := e (QuotientGroup.mk ⟨b, hb⟩) with ht
  by_cases hA : t ∈ D.A
  ·
    obtain ⟨x, y, z, h, htx⟩ := D.heisA t hA
    let f : G →* MulAut W := L.subtype.comp φ.symm.toMonoidHom
    have hfinj : Function.Injective f := L.subtype_injective.comp φ.symm.injective
    have hfz : f z ≠ 1 := fun h1 => h.z1 (hfinj (by rw [h1, map_one]))
    have hft : f t = b := by
      have : φ.symm t = ⟨b, hb⟩ := by
        rw [ht, ← hφ]; exact φ.symm_apply_apply _
      show ((φ.symm t : ↥L) : MulAut W) = b
      rw [this]
    have hinv : b * f (x 0) * b⁻¹ = (f (x 0))⁻¹ := by
      have := congrArg f htx
      rw [map_mul, map_mul, map_inv, map_inv, hft] at this
      exact this
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h1 := two_pow_le_index_sq_of_heisCfg hW (p := 5) (n := 0) (by norm_num)
      (h.map f hfz) hb2 hinv
    rw [orderOf_two_zmod_five_cut] at h1
    exact two_pow_le_of_pow_le (index_fixV_eq_two_pow hW _) h1 (by norm_num)
  · obtain ⟨c, hc⟩ := D.dihNonA t ht2 ht1 hA
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    have h1 := two_pow_le_index_sq_of_dihedral hW e hb (p := 13) (by norm_num) c hc
    rw [orderOf_two_zmod_thirteen_cut] at h1
    exact two_pow_le_of_pow_le (index_fixV_eq_two_pow hW _) h1 (by norm_num)

theorem noIrrFFOffender_of_cutData {G : Type} [Group G] (D : CutData G)
    (hAut : ∀ φ : G ≃* G, ∃ s : G, ∀ x, φ x = s * x * s⁻¹)
    (hZ : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L →
      Nonempty (L ⧸ Subgroup.center L ≃* G) → Nat.card (Subgroup.center L) ∣ 2) :
    NoIrrFFOffender G := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel hquad
  have : Nontrivial W := hirr.1
  have hperf : Group.IsPerfect ↥L := hq.1
  have hZdvd := hZ ↥L hq ⟨e⟩
  have hodd := odd_card_center_of_irreducible hW hirr.2
  have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hZdvd with h1 | h2
    · exact h1
    · rw [h2] at hodd
      exact absurd hodd (by decide)
  have hZbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
  let π : ↥L →* G := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπi : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (QuotientGroup.mk x : CQ L) = 1 := by
      apply e.injective
      simpa [π] using hx
    rw [QuotientGroup.eq_one_iff, hZbot, Subgroup.mem_bot] at h1
    exact h1
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let φ : ↥L ≃* G := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  have hφ : ∀ x : ↥L, φ x = e (QuotientGroup.mk x) := fun _ => rfl
  have hL : L ≠ ⊥ := ne_bot_of_isQuasisimple hq
  have hEL : E ≤ L := le_of_autInner hW hperf hirr hEN hel e hAut
  have hE32 : Nat.card E ≤ 2 ^ 5 := card_le_of_quadratic_cut hW D φ hirr hL hEL hel hquad
  obtain ⟨⟨b, hbE⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hb2 : b * b = 1 := by rw [← sq]; exact hel.2 b hbE
  have h64 := index_ge_of_cut hW D hirr e φ hφ (hEL hbE) hb1' hb2
  have h3 : (fixV (Subgroup.zpowers b)).index ≤ (fixV E).index := by
    apply Subgroup.index_antitone
    apply CFSG.Quasithin.fixV_anti
    rw [Subgroup.zpowers_le]
    exact hbE
  have h4 : Nat.card E < (fixV E).index := by omega
  have hpos : 0 < Nat.card (fixV E) := Nat.card_pos
  calc Nat.card E * Nat.card (fixV E) < (fixV E).index * Nat.card (fixV E) :=
        Nat.mul_lt_mul_of_pos_right h4 hpos
    _ = Nat.card W := by rw [mul_comm, Subgroup.card_mul_index]

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
