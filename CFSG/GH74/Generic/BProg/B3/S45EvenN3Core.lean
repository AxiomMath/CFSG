module

public import CFSG.GH74.Generic.S45.LAltCore
public import CFSG.GH74.Generic.BProg.B3.S45EvenN3Comb

public section

namespace CFSG.GH74.Generic.BProg.B3.S45EvenN3Core

open Equiv Equiv.Perm Subgroup CFSG.GH74.Generic.S45.LAlt CFSG.GH74.Generic.BProg.B3.S45EvenN3Comb
open scoped commutatorElement

theorem isPGroup_sup_zpowers {G : Type*} [Group G] {u v : G} (hu : u * u = 1) (hv : v * v = 1)
    (huv : u * v = v * u) : IsPGroup 2 ↥(zpowers u ⊔ zpowers v) := by
  have hz : ∀ {a : G}, a * a = 1 → IsPGroup 2 ↥(zpowers a) := by
    intro a ha2
    by_cases ha1 : a = 1
    · subst ha1
      exact IsPGroup.of_card (n := 0) (by simp)
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  refine IsPGroup.to_sup_of_normal_right' (hz hu) (hz hv) ?_
  rw [Subgroup.zpowers_le]
  apply Subgroup.centralizer_le_normalizer _
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact ((show Commute u v from huv).zpow_right k).symm.eq

theorem mul_eq_one_of_card_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2) {a b : G}
    (ha : a ≠ 1) (hb : b ≠ 1) : a * b = 1 := by
  have hnt : Nontrivial G := ⟨⟨a, 1, ha⟩⟩
  have h2 : Nat.card G = 2 := le_antisymm h (Nat.succ_le_of_lt (Finite.one_lt_card))
  obtain ⟨c, -, hc⟩ := (Nat.card_eq_two_iff' (1 : G)).1 h2
  have hab : a = b := (hc a ha).trans (hc b hb).symm
  rw [← hab, ← pow_two]
  exact sq_eq_one_of_card_le_two h a

theorem commutator_mul_central {X : Type*} [Group X] {g h a b : X} (ha : a ∈ center X)
    (hb : b ∈ center X) : ⁅g * a, h * b⁆ = ⁅g, h⁆ := by
  have ha' := Subgroup.mem_center_iff.1 ha
  have hb' := Subgroup.mem_center_iff.1 hb
  have hb'' := Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hb)
  have hh : a * (h * b) * a⁻¹ = h * b := by
    rw [mul_inv_eq_iff_eq_mul, ← ha' (h * b)]
  calc ⁅g * a, h * b⁆ = g * (a * (h * b) * a⁻¹) * g⁻¹ * (h * b)⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = g * (h * b) * g⁻¹ * (h * b)⁻¹ := by rw [hh]
    _ = g * h * (b * g⁻¹) * b⁻¹ * h⁻¹ := by group
    _ = g * h * (g⁻¹ * b) * b⁻¹ * h⁻¹ := by rw [← hb' g⁻¹]
    _ = ⁅g, h⁆ := by simp only [commutatorElement_def]; group

theorem commutator_fixed {X : Type*} [Group X] {P : Type*} [Group P] (ψ : X →* P)
    (hker : ψ.ker ≤ center X) {y : MulAut X} {σ : P} (hyσ : ∀ k, ψ (y k) = σ * ψ k * σ⁻¹)
    {C : Subgroup P} (hC : ∀ c ∈ C, c * σ = σ * c) :
    ∀ k ∈ ⁅C.comap ψ, C.comap ψ⁆, y k = k := by
  have hcent : ∀ g ∈ C.comap ψ, g⁻¹ * y g ∈ center X := by
    intro g hg
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyσ, ← hC (ψ g) hg, mul_inv_cancel_right,
      inv_mul_cancel]
  have hle : ⁅C.comap ψ, C.comap ψ⁆ ≤ (y.toMonoidHom).eqLocus (MonoidHom.id X) := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    have ha := hcent g hg
    have hb := hcent h hh
    show y ⁅g, h⁆ = ⁅g, h⁆
    calc y ⁅g, h⁆ = ⁅y g, y h⁆ := map_commutatorElement y g h
      _ = ⁅g * (g⁻¹ * y g), h * (h⁻¹ * y h)⁆ := by simp only [mul_inv_cancel_left]
      _ = ⁅g, h⁆ := commutator_mul_central ha hb
  exact fun k hk => hle hk

theorem false_of_klein_commutators {X : Type} [Group X] [Finite X] (hXp : Group.IsPerfect X)
    {n : ℕ} (hn : 6 ≤ n) (π : X →* alternatingGroup (Fin n)) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center X) (hZ2 : IsPGroup 2 π.ker) (hZ : π.ker ≠ ⊥)
    (hZc : Nat.card π.ker ≤ 2) {y : MulAut X} {σ : Perm (Fin n)}
    (hyσ : ∀ k, ((π (y k) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      σ * (π k : Perm (Fin n)) * σ⁻¹)
    (hab : ∀ T : Subgroup X, IsPGroup 2 ↥T → (∀ t ∈ T, y t = t) → ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    {u v : Perm (Fin n)} (hu : u ∈ ⁅centAlt σ, centAlt σ⁆) (hv : v ∈ ⁅centAlt σ, centAlt σ⁆)
    (huv : u * v = v * u) (hud : IsDblTransp u) (hvd : IsDblTransp v)
    (huvd : IsDblTransp (u * v)) : False := by
  classical
  have := hXp
  let ψ : X →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp π
  have hψker : ψ.ker = π.ker :=
    MonoidHom.ker_comp_of_injective π (alternatingGroup (Fin n)).subtype
      (alternatingGroup (Fin n)).subtype_injective
  have hCle : centAlt σ ≤ ψ.range := by
    intro c hc
    obtain ⟨hcA, -⟩ := mem_centAlt.1 hc
    obtain ⟨k, hk⟩ := hπ ⟨c, hcA⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hfix := commutator_fixed ψ (by rw [hψker]; exact hker) (y := y) (σ := σ)
    (fun k => hyσ k) (C := centAlt σ) (fun c hc => (mem_centAlt.1 hc).2)
  have hmap : (⁅(centAlt σ).comap ψ, (centAlt σ).comap ψ⁆).map ψ = ⁅centAlt σ, centAlt σ⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq, inf_eq_right.2 hCle]
  rw [← hmap] at hu hv
  obtain ⟨lu, hlu, rfl⟩ := hu
  obtain ⟨lv, hlv, rfl⟩ := hv
  have hluf : y lu = lu := hfix lu hlu
  have hlvf : y lv = lv := hfix lv hlv
  have hW := isPGroup_sup_zpowers (dblTransp_mul_self hud) (dblTransp_mul_self hvd) huv
  have hT2 : IsPGroup 2 ↥(closure ({lu, lv} : Set X)) := by
    refine IsPGroup.to_le (K := (zpowers (ψ lu) ⊔ zpowers (ψ lv)).comap ψ)
      (IsPGroup.comap_of_ker_isPGroup hW ψ (by rw [hψker]; exact hZ2)) ?_
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_comap.2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    · exact Subgroup.mem_comap.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hTfix : ∀ t ∈ closure ({lu, lv} : Set X), y t = t := by
    have hle : closure ({lu, lv} : Set X) ≤ (y.toMonoidHom).eqLocus (MonoidHom.id X) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hluf
      · exact hlvf
    exact fun t ht => hle ht
  have hcomm : lu * lv = lv * lu :=
    hab _ hT2 hTfix lu (Subgroup.subset_closure (by simp)) lv (Subgroup.subset_closure (by simp))
  have hsq : ∀ w : X, IsDblTransp (ψ w) → w ^ 2 ≠ 1 := by
    rintro w ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hw⟩
    exact sq_ne_one_of_lift_swap_mul_swap hn π hπ hker hZ2 hZ hab hac had hbc hbd hcd hw
  have hker_mem : ∀ w : X, ψ w * ψ w = 1 → w ^ 2 ∈ π.ker := by
    intro w hw
    rw [← hψker, MonoidHom.mem_ker, map_pow, pow_two]
    exact hw
  have h1 : lu ^ 2 ∈ π.ker := hker_mem lu (dblTransp_mul_self hud)
  have h2 : lv ^ 2 ∈ π.ker := hker_mem lv (dblTransp_mul_self hvd)
  have h12 : lu ^ 2 * lv ^ 2 = 1 := by
    have := mul_eq_one_of_card_le_two hZc (a := ⟨lu ^ 2, h1⟩) (b := ⟨lv ^ 2, h2⟩)
      (fun h => hsq lu hud (congrArg Subtype.val h)) (fun h => hsq lv hvd (congrArg Subtype.val h))
    exact congrArg Subtype.val this
  refine hsq (lu * lv) (by rw [map_mul]; exact huvd) ?_
  rw [(show Commute lu lv from hcomm).mul_pow, h12]

theorem n3_alt_core {X : Type} [Group X] [Finite X] (hXp : Group.IsPerfect X)
    (hZ2 : IsPGroup 2 ↥(Subgroup.center X)) (hZ : Subgroup.center X ≠ ⊥) {n : ℕ} (hn8 : 8 ≤ n)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n)) {y : MulAut X}
    (hy : orderOf y = 2)
    (hab : ∀ T : Subgroup X, IsPGroup 2 ↥T → (∀ t ∈ T, y t = t) → ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    False := by
  have := hXp
  obtain ⟨yb, hπy, hyb1, hyb2⟩ := exists_induced hXp e y hy
  obtain ⟨σ, hσ2, -, hσyb⟩ := exists_sigma (Or.inr (by omega)) yb hyb1 hyb2
  have hπker := ker_projAlt e
  have hZ2' : IsPGroup 2 (projAlt e).ker := by rw [hπker]; exact hZ2
  obtain ⟨u, v, hu, hv, huv, hud, hvd, huvd⟩ := exists_klein_commutators hσ2 hn8
  exact false_of_klein_commutators hXp (by omega) (projAlt e) (projAlt_surjective e) hπker.le hZ2'
    (by rw [hπker]; exact hZ)
    (CFSG.LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
      (by omega) (projAlt e) (projAlt_surjective e) hπker.le hZ2')
    (fun k => by rw [hπy, hσyb]) hab hu hv huv hud hvd huvd

end CFSG.GH74.Generic.BProg.B3.S45EvenN3Core
