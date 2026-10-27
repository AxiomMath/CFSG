module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S12A6
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PairAction

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.EvenSporadicStandard.HSStd.Zassenhaus

section Perfect

theorem eq_of_central_ratio {N : Type*} [Group N] (hN : commutator N = ⊤) (f₁ f₂ : N →* N)
    (h : ∀ n, (f₂ n)⁻¹ * f₁ n ∈ center N) : f₁ = f₂ := by
  let ζ : N →* N :=
    { toFun := fun n => (f₂ n)⁻¹ * f₁ n
      map_one' := by simp
      map_mul' := fun a b => by
        have hc : (f₂ a)⁻¹ * f₁ a * (f₂ b)⁻¹ = (f₂ b)⁻¹ * ((f₂ a)⁻¹ * f₁ a) :=
          ((mem_center_iff.1 (h a) ((f₂ b)⁻¹)).symm)
        simp only [map_mul]
        calc (f₂ a * f₂ b)⁻¹ * (f₁ a * f₁ b)
            = (f₂ b)⁻¹ * ((f₂ a)⁻¹ * f₁ a) * f₁ b := by group
          _ = (f₂ a)⁻¹ * f₁ a * (f₂ b)⁻¹ * f₁ b := by rw [← hc]
          _ = _ := by group }
  have hζ : ∀ n, ζ n = 1 := by
    intro n
    have hn : n ∈ commutator N := by rw [hN]; trivial
    have : commutator N ≤ ζ.ker := by
      rw [commutator_def, commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.1 (h a) (ζ b)).symm
    exact this hn
  ext n
  have := hζ n
  simp only [ζ, MonoidHom.coe_mk, OneHom.coe_mk] at this
  exact (inv_mul_eq_one.1 this).symm

end Perfect

section Transport

variable {N : Type*} [Group N]

theorem map_center_mem (φ : MulAut N) {z : N} (hz : z ∈ center N) : φ z ∈ center N := by
  rw [mem_center_iff] at hz ⊢
  intro g
  have := congrArg φ (hz (φ.symm g))
  simpa using this

theorem exists_alpha (π : N →* alternatingGroup (Fin 6)) (hs : Function.Surjective π)
    (hk : π.ker = center N) (φ : MulAut N) :
    ∃ α : MulAut (alternatingGroup (Fin 6)), ∀ n, α (π n) = π (φ n) := by
  have key : ∀ ψ : MulAut N, π.ker ≤ (π.comp ψ.toMonoidHom).ker := by
    intro ψ n hn
    rw [hk] at hn
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    have : ψ n ∈ center N := map_center_mem ψ hn
    rw [← hk] at this
    exact this
  let ri := Function.surjInv hs
  have hri : Function.RightInverse ri π := Function.rightInverse_surjInv hs
  let α0 : alternatingGroup (Fin 6) →* alternatingGroup (Fin 6) :=
    π.liftOfRightInverse ri hri ⟨π.comp φ.toMonoidHom, key φ⟩
  let α1 : alternatingGroup (Fin 6) →* alternatingGroup (Fin 6) :=
    π.liftOfRightInverse ri hri ⟨π.comp φ.symm.toMonoidHom, key φ.symm⟩
  have h0 : ∀ n, α0 (π n) = π (φ n) := fun n => by
    simp [α0, MonoidHom.liftOfRightInverse_comp_apply]
  have h1 : ∀ n, α1 (π n) = π (φ.symm n) := fun n => by
    simp [α1, MonoidHom.liftOfRightInverse_comp_apply]
  refine ⟨MonoidHom.toMulEquiv α0 α1 ?_ ?_, h0⟩
  · ext a
    obtain ⟨n, rfl⟩ := hs a
    simp [h0, h1]
  · ext a
    obtain ⟨n, rfl⟩ := hs a
    simp [h0, h1]

end Transport

section Frame

variable {G : Type*} [Group G]

structure A6Frame (N X : Subgroup G) (x : G) : Prop where
  perf : commutator ↥N = ⊤
  x_mem : x ∈ X
  X_le : X ≤ N ⊓ centralizer ({x} : Set G)
  X_card : Nat.card X = 9
  X_Z : ∀ (g : G) (hg : g ∈ N), g ∈ X → (⟨g, hg⟩ : ↥N) ∈ center ↥N → g = 1
  x_ord : orderOf x = 3
  quot : Nonempty (↥N ⧸ center ↥N ≃* alternatingGroup (Fin 6))

variable {N X : Subgroup G} {x : G}

theorem A6Frame.exists_pi (F : A6Frame N X x) :
    ∃ π : ↥N →* alternatingGroup (Fin 6), Function.Surjective π ∧ π.ker = center ↥N := by
  obtain ⟨e⟩ := F.quot
  refine ⟨(e : ↥N ⧸ center ↥N →* alternatingGroup (Fin 6)).comp (QuotientGroup.mk' _), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext n
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    exact (map_eq_one_iff e e.injective).trans (QuotientGroup.eq_one_iff n)

theorem A6Frame.x_mem_N (F : A6Frame N X x) : x ∈ N := (F.X_le F.x_mem).1

theorem A6Frame.X_mem_N (F : A6Frame N X x) {b : G} (hb : b ∈ X) : b ∈ N := (F.X_le hb).1

theorem A6Frame.X_comm (F : A6Frame N X x) {b : G} (hb : b ∈ X) : b * x = x * b :=
  mem_centralizer_singleton_iff.1 (F.X_le hb).2


theorem A6Frame.orderOf_pi (F : A6Frame N X x) {π : ↥N →* alternatingGroup (Fin 6)}
    (hk : π.ker = center ↥N) : orderOf (π ⟨x, F.x_mem_N⟩) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have h3 : (⟨x, F.x_mem_N⟩ : ↥N) ^ 3 = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one x
      rw [F.x_ord] at this
      exact this
    rw [h3, map_one]
  · intro h
    have hx1 : (⟨x, F.x_mem_N⟩ : ↥N) ∈ center ↥N := by rw [← hk]; exact h
    have h1 := F.X_Z x F.x_mem_N F.x_mem hx1
    have h2 := F.x_ord
    rw [h1, orderOf_one] at h2
    omega

theorem A6Frame.exists_mem_X (F : A6Frame N X x) {π : ↥N →* alternatingGroup (Fin 6)}
    (hk : π.ker = center ↥N) {n : ↥N}
    (hn : π n ∈ centralizer ({π ⟨x, F.x_mem_N⟩} : Set (alternatingGroup (Fin 6)))) :
    ∃ b ∈ X, ∃ hb : b ∈ N, π ⟨b, hb⟩ = π n := by
  have hx3 := F.orderOf_pi hk
  let f : X → ↥(centralizer ({π ⟨x, F.x_mem_N⟩} : Set (alternatingGroup (Fin 6)))) :=
    fun b => ⟨π ⟨b, F.X_mem_N b.2⟩, by
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (F.X_comm b.2)⟩
  have hinj : Function.Injective f := by
    intro b b' h
    have h1 : π ⟨b, F.X_mem_N b.2⟩ = π ⟨b', F.X_mem_N b'.2⟩ := congrArg Subtype.val h
    have h2 : (⟨b, F.X_mem_N b.2⟩ : ↥N)⁻¹ * ⟨b', F.X_mem_N b'.2⟩ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    rw [hk] at h2
    have h3 := F.X_Z (b⁻¹ * b') (by
      exact mul_mem (inv_mem (F.X_mem_N b.2)) (F.X_mem_N b'.2)) (mul_mem (inv_mem b.2) b'.2) h2
    exact Subtype.ext (inv_mul_eq_one.1 h3)
  have hcard : Nat.card X = Nat.card ↥(centralizer ({π ⟨x, F.x_mem_N⟩} : Set (alternatingGroup (Fin 6)))) := by
    rw [F.X_card, card_centralizer_of_orderOf_eq_three hx3]
  have hbij : Function.Bijective f := by
    have : Finite ↥(centralizer ({π ⟨x, F.x_mem_N⟩} : Set (alternatingGroup (Fin 6)))) := inferInstance
    exact (Nat.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  obtain ⟨b, hb⟩ := hbij.2 ⟨π n, hn⟩
  exact ⟨b, b.2, F.X_mem_N b.2, congrArg Subtype.val hb⟩


theorem A6Frame.exp_three (F : A6Frame N X x) {b : G} (hb : b ∈ X) : b ^ 3 = 1 := by
  obtain ⟨π, hs, hk⟩ := F.exists_pi
  have hπb : π ⟨b, F.X_mem_N hb⟩ ∈
      centralizer ({π ⟨x, F.x_mem_N⟩} : Set (alternatingGroup (Fin 6))) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (F.X_comm hb)
  have h3 := pow_three_of_mem_centralizer (F.orderOf_pi hk) _ hπb
  have h4 : (⟨b, F.X_mem_N hb⟩ : ↥N) ^ 3 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact h3
  rw [hk] at h4
  exact F.X_Z (b ^ 3) (pow_mem (F.X_mem_N hb) 3) (pow_mem hb 3) h4

theorem A6Frame.eq_of_pi_eq (F : A6Frame N X x) {π : ↥N →* alternatingGroup (Fin 6)}
    (hk : π.ker = center ↥N) (φ : MulAut ↥N) (c : ↥N)
    (h : ∀ n, π (φ n) = π (c * n * c⁻¹)) : ∀ n, φ n = c * n * c⁻¹ := by
  have := eq_of_central_ratio F.perf φ.toMonoidHom (MulAut.conj c).toMonoidHom (fun n => by
    rw [← hk, MonoidHom.mem_ker, map_mul, map_inv]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h n, inv_mul_cancel])
  intro n
  exact congrArg (fun f : ↥N →* ↥N => f n) this

theorem A6Frame.exists_conj_of_cube (F : A6Frame N X x) {g : G}
    (hg : g ∈ normalizer (N : Set G)) (hg3 : g ^ 3 = 1) (hgx : g * x = x * g) :
    ∃ b ∈ X, ∀ n ∈ N, g * n * g⁻¹ = b * n * b⁻¹ := by
  obtain ⟨π, hs, hk⟩ := F.exists_pi
  obtain ⟨α, hα⟩ := exists_alpha π hs hk (conjAutOf N hg)
  have hcube : α * α * α = 1 := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨n, rfl⟩ := hs a
    simp only [MulAut.mul_apply, MulAut.one_apply, hα]
    congr 1
    apply Subtype.ext
    simp only [conjAutOf_apply]
    have hg3' : g * (g * g) = 1 := by rw [← pow_three]; exact hg3
    have : g * (g * (g * (n : G) * g⁻¹) * g⁻¹) * g⁻¹ =
        (g * (g * g)) * n * (g * (g * g))⁻¹ := by group
    rw [this, hg3']
    simp
  obtain ⟨a0, ha0⟩ := mulAut_cube_inner α hcube
  have hx : α (π ⟨x, F.x_mem_N⟩) = π ⟨x, F.x_mem_N⟩ := by
    rw [hα]
    congr 1
    apply Subtype.ext
    simp only [conjAutOf_apply]
    rw [hgx]
    group
  have hcomm : a0 ∈ centralizer ({π ⟨x, F.x_mem_N⟩} : Set (alternatingGroup (Fin 6))) := by
    rw [mem_centralizer_singleton_iff]
    rw [← ha0] at hx
    simp only [MulAut.conj_apply] at hx
    exact (mul_inv_eq_iff_eq_mul.1 hx)
  obtain ⟨n0, rfl⟩ := hs a0
  obtain ⟨b, hbX, hbN, hb⟩ := F.exists_mem_X hk hcomm
  refine ⟨b, hbX, ?_⟩
  have := F.eq_of_pi_eq hk (conjAutOf N hg) ⟨b, hbN⟩ (fun n => by
    rw [← hα, ← ha0]
    simp [hb])
  intro n hn
  exact congrArg Subtype.val (this ⟨n, hn⟩)

theorem A6Frame.centralizes_of_fix (F : A6Frame N X x) {g : G}
    (hg : g ∈ normalizer (N : Set G)) (hg2 : g * g = 1) (hX : ∀ b ∈ X, g * b * g⁻¹ = b) :
    ∀ n ∈ N, g * n * g⁻¹ = n := by
  obtain ⟨π, hs, hk⟩ := F.exists_pi
  obtain ⟨α, hα⟩ := exists_alpha π hs hk (conjAutOf N hg)
  have hsq : α * α = 1 := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨n, rfl⟩ := hs a
    simp only [MulAut.mul_apply, MulAut.one_apply, hα]
    congr 1
    apply Subtype.ext
    simp only [conjAutOf_apply]
    have : g * (g * (n : G) * g⁻¹) * g⁻¹ = (g * g) * n * (g * g)⁻¹ := by group
    rw [this, hg2]
    simp
  have hfix : ∀ a ∈ centralizer ({π ⟨x, F.x_mem_N⟩} : Set (alternatingGroup (Fin 6))), α a = a := by
    intro a ha
    obtain ⟨n, rfl⟩ := hs a
    obtain ⟨b, hbX, hbN, hb⟩ := F.exists_mem_X hk ha
    rw [← hb, hα]
    congr 1
    apply Subtype.ext
    simp only [conjAutOf_apply]
    exact hX b hbX
  have h1 := mulAut_eq_one_of_fix_centralizer (F.orderOf_pi hk) α hsq hfix
  have := F.eq_of_pi_eq hk (conjAutOf N hg) 1 (fun n => by
    rw [← hα, h1]
    simp)
  intro n hn
  have h2 := congrArg Subtype.val (this ⟨n, hn⟩)
  rw [conjAutOf_apply] at h2
  simpa using h2

theorem A6Frame.outer_of_not_fix (F : A6Frame N X x) {g : G}
    (_hg : g ∈ normalizer (N : Set G)) (hgx : g * x = x * g)
    (hgX : ∀ b ∈ X, g * b * g⁻¹ ∈ X) {b : G} (hb : b ∈ X) (hgb : g * b * g⁻¹ ≠ b) :
    ∀ l ∈ N, ∃ a ∈ N, g * a * g⁻¹ ≠ l * a * l⁻¹ := by
  intro l hl
  by_contra hcon
  push Not at hcon
  obtain ⟨π, hs, hk⟩ := F.exists_pi
  have hlx : l * x * l⁻¹ = x := by
    rw [← hcon x F.x_mem_N, hgx]
    group
  have hπl : π ⟨l, hl⟩ ∈ centralizer ({π ⟨x, F.x_mem_N⟩} : Set (alternatingGroup (Fin 6))) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.1 hlx)
  have hπb : π ⟨b, F.X_mem_N hb⟩ ∈
      centralizer ({π ⟨x, F.x_mem_N⟩} : Set (alternatingGroup (Fin 6))) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (F.X_comm hb)
  have hcomm := centralizer_commute_of_orderOf_eq_three (F.orderOf_pi hk) _ hπl _ hπb
  have hlb : l * b * l⁻¹ = g * b * g⁻¹ := (hcon b (F.X_mem_N hb)).symm
  have hker : (⟨b, F.X_mem_N hb⟩ : ↥N)⁻¹ * ⟨g * b * g⁻¹, F.X_mem_N (hgX b hb)⟩ ∈ π.ker := by
    have : (⟨g * b * g⁻¹, F.X_mem_N (hgX b hb)⟩ : ↥N) =
        ⟨l, hl⟩ * ⟨b, F.X_mem_N hb⟩ * ⟨l, hl⟩⁻¹ := Subtype.ext (by simp [hlb])
    rw [MonoidHom.mem_ker, this, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  rw [hk] at hker
  have := F.X_Z (b⁻¹ * (g * b * g⁻¹)) (mul_mem (inv_mem (F.X_mem_N hb)) (F.X_mem_N (hgX b hb)))
    (mul_mem (inv_mem hb) (hgX b hb)) hker
  exact hgb (inv_mul_eq_one.1 this).symm

end Frame

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
