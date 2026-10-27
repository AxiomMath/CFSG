module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma seg27_center_iff {H : Type} [Group H]
    (ψ : H ≃* Elem2 2 × alternatingGroup (Fin 8)) (h : H) :
    h ∈ Subgroup.center H ↔ (ψ h).2 = 1 := by
  have hmap : h ∈ Subgroup.center H ↔
      ψ h ∈ Subgroup.center (Elem2 2 × alternatingGroup (Fin 8)) := by
    rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro hh w
      obtain ⟨g, rfl⟩ := ψ.surjective w
      rw [← map_mul, ← map_mul, hh g]
    · intro hh g
      apply ψ.injective
      rw [map_mul, map_mul]
      exact hh (ψ g)
  rw [hmap]
  constructor
  · intro hx
    have hc : (ψ h).2 ∈ Subgroup.center (alternatingGroup (Fin 8)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg Prod.snd (Subgroup.mem_center_iff.mp hx ((1 : Elem2 2), g))
      simpa using h2
    rwa [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 8)),
      Subgroup.mem_bot] at hc
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro w
    apply Prod.ext
    · exact mul_comm w.1 (ψ h).1
    · simp [hx]

theorem seg27_exists_theta {H : Type} [Group H] (ψ : H ≃* Elem2 2 × alternatingGroup (Fin 8))
    (φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator H)) :
    ∃ θ : H →* Equiv.Perm (Fin 8), (∀ g, θ (φ g : H) = (g : Equiv.Perm (Fin 8))) ∧
      (∀ h, θ h ∈ alternatingGroup (Fin 8)) ∧ θ.ker = Subgroup.center H := by
  haveI : IsMulCommutative (Elem2 2) := ⟨⟨fun a b => mul_comm a b⟩⟩
  let p : H →* alternatingGroup (Fin 8) :=
    (MonoidHom.snd (Elem2 2) (alternatingGroup (Fin 8))).comp ψ.toMonoidHom
  let fst : H →* Elem2 2 :=
    (MonoidHom.fst (Elem2 2) (alternatingGroup (Fin 8))).comp ψ.toMonoidHom
  let α : alternatingGroup (Fin 8) →* alternatingGroup (Fin 8) :=
    p.comp ((_root_.commutator H).subtype.comp φ.toMonoidHom)
  have hα1 : ∀ g, α g = 1 → g = 1 := by
    intro g hg
    have hp : p (φ g : H) = 1 := hg
    have hf : fst (φ g : H) = 1 :=
      MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker fst (φ g).2)
    have hψ : ψ (φ g : H) = 1 := by
      apply Prod.ext
      · simpa [fst] using hf
      · simpa [p] using hp
    have hφH : (φ g : H) = 1 := ψ.injective (by simpa using hψ)
    have hφ : φ g = 1 := Subtype.ext (by simpa using hφH)
    exact φ.injective (by simpa using hφ)
  have hαinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro g hg
    exact hα1 g (MonoidHom.mem_ker.mp hg)
  have hαbij : Function.Bijective α := Finite.injective_iff_bijective.mp hαinj
  let α' : alternatingGroup (Fin 8) ≃* alternatingGroup (Fin 8) := MulEquiv.ofBijective α hαbij
  let θ : H →* Equiv.Perm (Fin 8) :=
    (alternatingGroup (Fin 8)).subtype.comp (α'.symm.toMonoidHom.comp p)
  have hθker : θ.ker = p.ker := by
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hθ
      change ((alternatingGroup (Fin 8)).subtype) (α'.symm (p h)) = 1 at hθ
      have h1 : α'.symm (p h) = 1 := Subtype.ext (by simpa using hθ)
      have := congrArg α' h1
      simpa using this
    · intro hp
      change ((alternatingGroup (Fin 8)).subtype) (α'.symm (p h)) = 1
      rw [hp]
      simp
  refine ⟨θ, ?_, ?_, ?_⟩
  · intro g
    have hpφg : p (φ g : H) = α g := rfl
    have hαg : α g = α' g := rfl
    change ((α'.symm (p (φ g : H)) : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
      (g : Equiv.Perm (Fin 8))
    rw [hpφg, hαg, MulEquiv.symm_apply_apply]
  · intro h
    change ((alternatingGroup (Fin 8)).subtype) (α'.symm (p h)) ∈
      alternatingGroup (Fin 8)
    exact (α'.symm (p h)).2
  · rw [hθker]
    ext h
    rw [MonoidHom.mem_ker, seg27_center_iff ψ h]
    simp [p]

theorem seg27_mul_self_of_mem_center {H : Type} [Group H]
    (ψ : H ≃* Elem2 2 × alternatingGroup (Fin 8)) {z : H} (hz : z ∈ Subgroup.center H) :
    z * z = 1 := by
  have hsq : ∀ u : Elem2 2, u * u = 1 := by
    intro u
    apply Multiplicative.ext
    funext i
    rw [toAdd_mul, toAdd_one]
    exact CharTwo.add_self_eq_zero (u.toAdd i)
  have hz2 : (ψ z).2 = 1 := (seg27_center_iff ψ z).mp hz
  apply ψ.injective
  rw [map_mul, map_one]
  apply Prod.ext
  · exact hsq (ψ z).1
  · simp [hz2]

theorem seg27_card_center {H : Type} [Group H] (ψ : H ≃* Elem2 2 × alternatingGroup (Fin 8)) :
    Nat.card (Subgroup.center H) = 4 := by
  rw [Nat.card_congr (Subgroup.centerCongr ψ).toEquiv]
  rw [Subgroup.center_prod]
  rw [Nat.card_congr (Subgroup.prodEquiv (Subgroup.center (Elem2 2))
    (Subgroup.center (alternatingGroup (Fin 8)))).toEquiv]
  rw [Nat.card_prod]
  have hE : Nat.card ↥(Subgroup.center (Elem2 2)) = 4 := by
    have e : ↥(Subgroup.center (Elem2 2)) ≃ Elem2 2 :=
      { toFun := fun x => x.1
        invFun := fun x => ⟨x, by
          rw [Subgroup.mem_center_iff]
          intro y
          exact mul_comm y x⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    rw [Nat.card_congr e]
    change Nat.card (Multiplicative (Fin 2 → ZMod 2)) = 4
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hA : Nat.card ↥(Subgroup.center (alternatingGroup (Fin 8))) = 1 := by
    rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 8))]
    exact Subgroup.card_bot
  rw [hE, hA, mul_one]

theorem seg27_ne_of_center {H : Type} [Group H] {a b : H}
    (hZ : (Subgroup.center H : Set H) = {1, a, b, a * b})
    (hc : Nat.card (Subgroup.center H) = 4) : a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have h4 : ({1, a, b, a * b} : Set H).ncard = 4 := by
    rw [← hZ, ← Nat.card_coe_set_eq]
    exact hc
  have hsub_le : ∀ (x y : H), ({1, a, b, a * b} : Set H) ⊆ {x, y} →
      ({1, a, b, a * b} : Set H).ncard ≤ 2 := by
    intro x y hsub
    calc ({1, a, b, a * b} : Set H).ncard ≤ ({x, y} : Set H).ncard := Set.ncard_le_ncard hsub
      _ = (insert x ({y} : Set H)).ncard := rfl
      _ ≤ ({y} : Set H).ncard + 1 := Set.ncard_insert_le x {y}
      _ = 2 := by simp [Set.ncard_singleton]
  have hsub_le3 : ∀ (x y z : H), ({1, a, b, a * b} : Set H) ⊆ {x, y, z} →
      ({1, a, b, a * b} : Set H).ncard ≤ 3 := by
    intro x y z hsub
    have h1 : ({x, y, z} : Set H).ncard ≤ ({y, z} : Set H).ncard + 1 :=
      Set.ncard_insert_le x {y, z}
    have h2 : ({y, z} : Set H).ncard ≤ ({z} : Set H).ncard + 1 :=
      Set.ncard_insert_le y {z}
    have h3 : ({z} : Set H).ncard = 1 := Set.ncard_singleton z
    have hle := Set.ncard_le_ncard hsub
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro ha
    have hset : ({1, a, b, a * b} : Set H) = {1, b} := by
      ext x
      simp [ha]
    have := hsub_le 1 b (le_of_eq hset)
    omega
  · intro hb
    have hset : ({1, a, b, a * b} : Set H) = {1, a} := by
      ext x
      simp [hb]
    have := hsub_le 1 a (le_of_eq hset)
    omega
  · intro hab
    have hset : ({1, a, b, a * b} : Set H) = {1, a, a * a} := by
      ext x
      simp [← hab]
    have := hsub_le3 1 a (a * a) (le_of_eq hset)
    omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
