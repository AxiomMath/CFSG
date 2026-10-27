module

public import CFSG.CGT.Foote82.T66.CaseIHeart
import CFSG.Quasithin.Background.G11Basic
public import CFSG.CGT.Foote82.T66.CaseIPerm

public section

namespace CFSG.CGT.Foote82

namespace CaseIHeart

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.Coordinator
open Equiv Equiv.Perm CaseIPerm

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem shift2_eq_succ_succ {k : ℕ} (j : Fin k) : (shift2 k j : Fin (k + 2)) = j.succ.succ :=
  Fin.ext (by simp [shift2_val])

theorem sum_fin_add_two {k : ℕ} (x : Fin (k + 2) → ZMod 2) :
    ∑ i, x i = x 0 + x 1 + ∑ j : Fin k, x (shift2 k j) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [shift2_eq_succ_succ, Fin.succ_zero_eq_one]
  ring

@[expose] def resVec {k : ℕ} (j₀ : Fin k) (x : Fin (k + 2) → ZMod 2) : Fin k → ZMod 2 :=
  fun j => x (shift2 k j) + if j = j₀ then x 0 + x 1 else 0

theorem sum_resVec {k : ℕ} (j₀ : Fin k) (x : Fin (k + 2) → ZMod 2) :
    ∑ j, resVec j₀ x j = ∑ i, x i := by
  rw [sum_fin_add_two]
  simp only [resVec, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

@[expose] def resHom {k : ℕ} (j₀ : Fin k) : evenWeight (k + 2) →+ evenWeight k where
  toFun x := ⟨resVec j₀ x, by
    have h := sum_evenWeight x
    show (∑ j, resVec j₀ (x : Fin (k + 2) → ZMod 2) j) = 0
    rw [sum_resVec, h]⟩
  map_zero' := Subtype.ext (funext fun j => by simp [resVec])
  map_add' x y := Subtype.ext (funext fun j => by
    show resVec j₀ ((x : Fin (k + 2) → ZMod 2) + y) j = resVec j₀ x j + resVec j₀ y j
    simp only [resVec, Pi.add_apply]
    split_ifs <;> ring)

@[expose] noncomputable def resHeart {k : ℕ} (j₀ : Fin k) : altHeart (k + 2) →+ altHeart k :=
  QuotientAddGroup.map _ _ (resHom j₀) fun x hx => by
    obtain ⟨κ, hκ⟩ := exists_forall_eq_of_mem_evenWeightOnes hx
    refine mem_evenWeightOnes_of_forall_eq (c := κ) fun j => ?_
    show resVec j₀ (x : Fin (k + 2) → ZMod 2) j = κ
    simp only [resVec, hκ]
    split_ifs <;> simp [CharTwo.add_self_eq_zero]

theorem resHeart_mk {k : ℕ} (j₀ : Fin k) (x : evenWeight (k + 2)) :
    resHeart j₀ (x : altHeart (k + 2)) = (resHom j₀ x : altHeart k) := rfl

theorem resHom_apply_of_zero {k : ℕ} (j₀ : Fin k) {x : evenWeight (k + 2)}
    (h0 : (x : Fin (k + 2) → ZMod 2) 0 = 0) (h1 : (x : Fin (k + 2) → ZMod 2) 1 = 0) (j : Fin k) :
    ((resHom j₀ x : evenWeight k) : Fin k → ZMod 2) j = (x : Fin (k + 2) → ZMod 2) (shift2 k j) := by
  show resVec j₀ (x : Fin (k + 2) → ZMod 2) j = _
  simp [resVec, h0, h1]

theorem resHom_evenWeightPerm {k : ℕ} (j₀ : Fin k) (σ : Perm (Fin k)) {x : evenWeight (k + 2)}
    (h0 : (x : Fin (k + 2) → ZMod 2) 0 = 0) (h1 : (x : Fin (k + 2) → ZMod 2) 1 = 0) :
    resHom j₀ (evenWeightPerm (iota2 k σ) x) = evenWeightPerm σ (resHom j₀ x) := by
  have hι0 : (iota2 k σ)⁻¹ 0 = 0 := by
    rw [Perm.inv_eq_iff_eq, iota2_apply_zero]
  have hι1 : (iota2 k σ)⁻¹ 1 = 1 := by
    rw [Perm.inv_eq_iff_eq, iota2_apply_one]
  have h0' : ((evenWeightPerm (iota2 k σ) x : evenWeight (k + 2)) : Fin (k + 2) → ZMod 2) 0 = 0 := by
    show (x : Fin (k + 2) → ZMod 2) ((iota2 k σ)⁻¹ 0) = 0
    rw [hι0, h0]
  have h1' : ((evenWeightPerm (iota2 k σ) x : evenWeight (k + 2)) : Fin (k + 2) → ZMod 2) 1 = 0 := by
    show (x : Fin (k + 2) → ZMod 2) ((iota2 k σ)⁻¹ 1) = 0
    rw [hι1, h1]
  apply Subtype.ext
  funext j
  rw [resHom_apply_of_zero j₀ h0' h1']
  show (x : Fin (k + 2) → ZMod 2) ((iota2 k σ)⁻¹ (shift2 k j)) =
    ((resHom j₀ x : evenWeight k) : Fin k → ZMod 2) (σ⁻¹ j)
  rw [resHom_apply_of_zero j₀ h0 h1]
  have : (iota2 k σ)⁻¹ (shift2 k j) = shift2 k (σ⁻¹ j) := by
    rw [Perm.inv_eq_iff_eq, iota2_apply_shift, perm_apply_inv]
  rw [this]

variable {X X' : Subgroup (GLV V)} {k : ℕ} {ρ : ↥X →* Perm (Fin (k + 2))}
  {β : ↥(commSpace X' ⊤) →+ altHeart (k + 2)}

theorem altSub (hk : 5 ≤ k) (hH : HeartFor X (k + 2) ρ X' β) (hinj : Function.Injective ρ)
    (hsurj : ∀ τ ∈ altOn {i : Fin (k + 2) | i ≠ 0 ∧ i ≠ 1}, ∃ x : ↥X, ρ x = τ)
    {B : Subgroup (GLV V)} (hBX : B ≤ X)
    (hB : ∀ x : ↥X, (x : GLV V) ∈ B ↔ ρ x ∈ altOn {i : Fin (k + 2) | i ≠ 0 ∧ i ≠ 1}) :
    ∃ (ρB : ↥B →* Perm (Fin k)) (βB : ↥(commSpace B ⊤) →+ altHeart k),
      HeartFor B k ρB B βB ∧ Function.Injective ρB ∧
      (∀ σ ∈ alternatingGroup (Fin k), ∃ b : ↥B, ρB b = σ) ∧
      ∀ b : ↥B, ρ ⟨b, hBX b.2⟩ = iota2 k (ρB b) := by
  classical
  set F : Set (Fin (k + 2)) := {i | i ≠ 0 ∧ i ≠ 1} with hF
  have hBX' : B ≤ X' := fun b hb => by
    have h1 := (hB ⟨b, hBX hb⟩).1 hb
    exact (hH.mem_iff ⟨b, hBX hb⟩).2 (mem_altOn_iff.1 h1).1
  let eF : alternatingGroup (Fin k) ≃* altOn F :=
    MulEquiv.ofBijective
      (((iota2 k).comp (alternatingGroup (Fin k)).subtype).codRestrict (altOn F) fun σ => by
        rw [hF, altOn_eq_map_iota2]; exact ⟨σ, σ.2, rfl⟩)
      ⟨fun σ τ h => Subtype.ext (iota2_injective k (congrArg Subtype.val h)), fun τ => by
        have hτ : (τ : Perm (Fin (k + 2))) ∈ (alternatingGroup (Fin k)).map (iota2 k) := by
          rw [← altOn_eq_map_iota2]; exact τ.2
        obtain ⟨σ, hσ, hστ⟩ := hτ
        exact ⟨⟨σ, hσ⟩, Subtype.ext hστ⟩⟩
  have heF : ∀ σ, ((eF σ : altOn F) : Perm (Fin (k + 2))) = iota2 k σ := fun _ => rfl
  let ρres : ↥B →* altOn F :=
    (ρ.comp (Subgroup.inclusion hBX)).codRestrict (altOn F) fun b => (hB _).1 b.2
  let ρB : ↥B →* Perm (Fin k) := (alternatingGroup (Fin k)).subtype.comp
    (eF.symm.toMonoidHom.comp ρres)
  have hρB : ∀ b : ↥B, ρ ⟨b, hBX b.2⟩ = iota2 k (ρB b) := by
    intro b
    have := heF (eF.symm (ρres b))
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hρBA : ∀ b : ↥B, ρB b ∈ alternatingGroup (Fin k) := fun b => (eF.symm (ρres b)).2
  have hρBinj : Function.Injective ρB := by
    intro b₁ b₂ h
    have h1 : ρ ⟨b₁, hBX b₁.2⟩ = ρ ⟨b₂, hBX b₂.2⟩ := by rw [hρB, hρB, h]
    have h2 := hinj h1
    have h3 : (b₁ : GLV V) = b₂ := congrArg (fun x : ↥X => (x : GLV V)) h2
    exact Subtype.ext h3
  have hρBonto : ∀ σ ∈ alternatingGroup (Fin k), ∃ b : ↥B, ρB b = σ := by
    intro σ hσ
    have hτ : iota2 k σ ∈ altOn F := by
      rw [hF, altOn_eq_map_iota2]; exact ⟨σ, hσ, rfl⟩
    obtain ⟨x, hx⟩ := hsurj _ hτ
    have hxB : (x : GLV V) ∈ B := (hB x).2 (hx ▸ hτ)
    refine ⟨⟨x, hxB⟩, iota2_injective k ?_⟩
    rw [← hρB]
    exact hx
  have hperf : ⁅B, B⁆ = B := by
    set B' : Subgroup ↥X := B.subgroupOf X with hB'
    have hmapB' : B'.map ρ = altOn F := by
      ext τ
      refine ⟨?_, fun hτ => ?_⟩
      · rintro ⟨x, hx, rfl⟩
        exact (hB x).1 (Subgroup.mem_subgroupOf.1 hx)
      · obtain ⟨x, hx⟩ := hsurj τ hτ
        exact ⟨x, Subgroup.mem_subgroupOf.2 ((hB x).2 (hx ▸ hτ)), hx⟩
    have hc : ⁅B', B'⁆ = B' := by
      apply Subgroup.map_injective hinj
      rw [Subgroup.map_commutator, hmapB', hF, commutator_altOn_eq_self hk]
    have hmap : B'.map X.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBX
    rw [← hmap, ← Subgroup.map_commutator, hc]
  let Δ2 : AddSubgroup (evenWeight (k + 2)) :=
    { carrier := {x | (x : Fin (k + 2) → ZMod 2) 0 = 0 ∧ (x : Fin (k + 2) → ZMod 2) 1 = 0}
      add_mem' := fun {a b} ha hb => ⟨by
          show (a : Fin (k + 2) → ZMod 2) 0 + (b : Fin (k + 2) → ZMod 2) 0 = 0
          rw [ha.1, hb.1, add_zero], by
          show (a : Fin (k + 2) → ZMod 2) 1 + (b : Fin (k + 2) → ZMod 2) 1 = 0
          rw [ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨rfl, rfl⟩
      neg_mem' := fun {a} ha => ⟨by
          have := ha.1; simp [this], by
          have := ha.2; simp [this]⟩ }
  let T2 : AddSubgroup (altHeart (k + 2)) := Δ2.map (QuotientAddGroup.mk' (evenWeightOnes (k + 2)))
  have hcommB : commSpace B ⊤ ≤ commSpace X' ⊤ := commSpace_mono hBX' le_rfl
  have hlift : ∀ w : ↥(commSpace X' ⊤), (w : V) ∈ commSpace B ⊤ →
      ∃ x : evenWeight (k + 2), x ∈ Δ2 ∧ β w = (x : altHeart (k + 2)) := by
    intro w hw
    have hT : β w ∈ T2 := by
      refine image_le_of_perfect hH hBX' hperf T2 (fun y hy x => ?_) hw
      refine ⟨_, ⟨?_, ?_⟩, rfl⟩
      · have hy0 := (mem_altOn_iff.1 ((hB ⟨y, hBX hy⟩).1 hy)).2 0 (by simp [hF])
        show (x : Fin (k + 2) → ZMod 2) ((ρ ⟨y, _⟩)⁻¹ 0) - (x : Fin (k + 2) → ZMod 2) 0 = 0
        rw [show (ρ ⟨y, hH.le (hBX' hy)⟩)⁻¹ 0 = 0 by
          rw [Perm.inv_eq_iff_eq]; exact hy0.symm, sub_self]
      · have hy1 := (mem_altOn_iff.1 ((hB ⟨y, hBX hy⟩).1 hy)).2 1 (by simp [hF])
        show (x : Fin (k + 2) → ZMod 2) ((ρ ⟨y, _⟩)⁻¹ 1) - (x : Fin (k + 2) → ZMod 2) 1 = 0
        rw [show (ρ ⟨y, hH.le (hBX' hy)⟩)⁻¹ 1 = 1 by
          rw [Perm.inv_eq_iff_eq]; exact hy1.symm, sub_self]
    obtain ⟨x, hx, hxw⟩ := hT
    exact ⟨x, hx, hxw.symm⟩
  obtain ⟨j₀⟩ : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let incl : ↥(commSpace B ⊤) →+ ↥(commSpace X' ⊤) :=
    (Submodule.inclusion hcommB).toAddMonoidHom
  let βB : ↥(commSpace B ⊤) →+ altHeart k := (resHeart j₀).comp (β.comp incl)
  have hβB : ∀ w : ↥(commSpace B ⊤), βB w = resHeart j₀ (β ⟨w, hcommB w.2⟩) := fun _ => rfl
  have hequiv : ∀ (b : ↥B) (w w' : ↥(commSpace B ⊤)), (w' : V) = (b : GLV V) (w : V) →
      ∀ y : evenWeight k, βB w = (y : altHeart k) →
        βB w' = (evenWeightPerm (ρB b) y : altHeart k) := by
    intro b w w' hww' y hy
    obtain ⟨x, hx, hxw⟩ := hlift ⟨w, hcommB w.2⟩ w.2
    have h1 := hH.equiv ⟨b, hBX b.2⟩ ⟨w, hcommB w.2⟩ ⟨w', hcommB w'.2⟩ hww' x hxw
    rw [hβB, h1, hρB, resHeart_mk, resHom_evenWeightPerm j₀ _ hx.1 hx.2]
    rw [hβB, hxw, resHeart_mk] at hy
    have hyx := QuotientAddGroup.eq.1 hy
    refine QuotientAddGroup.eq.2 ?_
    obtain ⟨κ, hκ⟩ := exists_forall_eq_of_mem_evenWeightOnes hyx
    refine mem_evenWeightOnes_of_forall_eq (c := κ) fun j => ?_
    have := hκ ((ρB b)⁻¹ j)
    simpa [evenWeightPerm] using this
  have hsurjB : Function.Surjective βB := by
    have hU : ∀ σ ∈ alternatingGroup (Fin k), ∀ y : evenWeight k,
        (y : altHeart k) ∈ βB.range → (evenWeightPerm σ y : altHeart k) ∈ βB.range := by
      rintro σ hσ y ⟨w, hw⟩
      obtain ⟨b, rfl⟩ := hρBonto σ hσ
      have hbw : (b : GLV V) (w : V) ∈ commSpace B ⊤ :=
        invariant_commSpace (fun k' hk' k hk => B.mul_mem (B.mul_mem hk' hk) (B.inv_mem hk'))
          (invariant_top B) _ b.2 _ w.2
      exact ⟨⟨_, hbw⟩, hequiv b w ⟨_, hbw⟩ rfl y hw⟩
    rcases altHeart_irreducible (by omega) βB.range hU with h | h
    ·
      exfalso
      set j₁ : Fin k := ⟨1, by omega⟩
      set j₂ : Fin k := ⟨2, by omega⟩
      set j₃ : Fin k := ⟨3, by omega⟩
      have h12 : j₁ ≠ j₂ := by simp [j₁, j₂, Fin.ext_iff]
      have h13 : j₁ ≠ j₃ := by simp [j₁, j₃, Fin.ext_iff]
      have h23 : j₂ ≠ j₃ := by simp [j₂, j₃, Fin.ext_iff]
      set γ : Perm (Fin k) := swap j₁ j₂ * swap j₂ j₃ with hγ
      have hγA : γ ∈ alternatingGroup (Fin k) := by
        rw [Equiv.Perm.mem_alternatingGroup, hγ, map_mul, sign_swap h12, sign_swap h23]; rfl
      have hγi2 : γ⁻¹ j₂ = j₁ := by
        rw [hγ, mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply, swap_apply_right,
          swap_apply_of_ne_of_ne h12 h13]
      have hγi1 : γ⁻¹ j₁ = j₃ := by
        rw [hγ, mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply, swap_apply_left, swap_apply_left]
      obtain ⟨b, hb⟩ := hρBonto γ hγA
      set y : evenWeight (k + 2) := pairEW (shift2 k j₂ : Fin (k + 2)) 0 with hy
      obtain ⟨u, hu⟩ := hH.surj (y : altHeart (k + 2))
      have hbu : (b : GLV V) (u : V) ∈ commSpace X' ⊤ := mem_comm_of_mem hH (hBX' b.2) u
      have hw : (b : GLV V) (u : V) - u ∈ commSpace B ⊤ :=
        sub_mem_commSpace b.2 Submodule.mem_top
      set z : evenWeight (k + 2) := evenWeightPerm (iota2 k γ) y - y with hz
      have hβw : β ⟨_, hcommB hw⟩ = (z : altHeart (k + 2)) := by
        have h1 := hH.equiv ⟨b, hBX b.2⟩ u ⟨_, hbu⟩ rfl _ hu
        have h2 : (⟨_, hcommB hw⟩ : ↥(commSpace X' ⊤)) = ⟨_, hbu⟩ - u := rfl
        rw [h2, map_sub, h1, hu, hρB, hb]
        rfl
      have hzi : ∀ i, (z : Fin (k + 2) → ZMod 2) i =
          (y : Fin (k + 2) → ZMod 2) ((iota2 k γ)⁻¹ i) - (y : Fin (k + 2) → ZMod 2) i :=
        fun i => rfl
      have hz0 : (z : Fin (k + 2) → ZMod 2) 0 = 0 := by
        rw [hzi, show (iota2 k γ)⁻¹ 0 = 0 by rw [Perm.inv_eq_iff_eq, iota2_apply_zero], sub_self]
      have hz1 : (z : Fin (k + 2) → ZMod 2) 1 = 0 := by
        rw [hzi, show (iota2 k γ)⁻¹ 1 = 1 by rw [Perm.inv_eq_iff_eq, iota2_apply_one], sub_self]
      have hzs : ∀ j, (z : Fin (k + 2) → ZMod 2) (shift2 k j) =
          (y : Fin (k + 2) → ZMod 2) (shift2 k (γ⁻¹ j)) - (y : Fin (k + 2) → ZMod 2) (shift2 k j) := by
        intro j
        have : (iota2 k γ)⁻¹ (shift2 k j) = shift2 k (γ⁻¹ j) := by
          rw [Perm.inv_eq_iff_eq, iota2_apply_shift, perm_apply_inv]
        rw [hzi, this]
      have hys : ∀ j, (y : Fin (k + 2) → ZMod 2) (shift2 k j) = if j = j₂ then 1 else 0 := by
        intro j
        rw [hy, pairEW_apply]
        have h0 : (shift2 k j : Fin (k + 2)) ≠ 0 := (shift2 k j).2.1
        simp only [h0, if_false, add_zero]
        by_cases hj : j = j₂
        · simp [hj]
        · have : (shift2 k j : Fin (k + 2)) ≠ shift2 k j₂ := fun h =>
            hj ((shift2 k).injective (Subtype.ext h))
          simp [hj, this]
      have hmem : βB ⟨_, hw⟩ ∈ βB.range := ⟨_, rfl⟩
      rw [h, AddSubgroup.mem_bot, hβB, hβw, resHeart_mk] at hmem
      have hval := congrArg (pairFun j₂ j₁) hmem
      rw [map_zero, pairFun_mk, resHom_apply_of_zero j₀ hz0 hz1,
        resHom_apply_of_zero j₀ hz0 hz1, hzs, hzs, hys, hys, hys, hys, hγi2, hγi1] at hval
      simp [h12, h13, h23, Ne.symm h12, Ne.symm h13, Ne.symm h23] at hval
    · intro y
      have : y ∈ βB.range := by rw [h]; trivial
      exact this
  have hker : βB.ker = ((fixedSpace B).comap (commSpace B ⊤).subtype).toAddSubgroup := by
    ext w
    simp only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Submodule.mem_comap,
      Submodule.coe_subtype]
    constructor
    · intro h0
      obtain ⟨x, hx, hxw⟩ := hlift ⟨w, hcommB w.2⟩ w.2
      rw [hβB, hxw, resHeart_mk] at h0
      obtain ⟨κ, hκ⟩ := exists_forall_eq_of_mem_evenWeightOnes ((QuotientAddGroup.eq_zero_iff _).1 h0)
      have hxs : ∀ j, (x : Fin (k + 2) → ZMod 2) (shift2 k j) = κ := fun j => by
        rw [← hκ j, resHom_apply_of_zero j₀ hx.1 hx.2]
      have hfixx : ∀ b : ↥B, evenWeightPerm (ρ ⟨b, hBX b.2⟩) x = x := by
        intro b
        apply Subtype.ext
        funext i
        show (x : Fin (k + 2) → ZMod 2) ((ρ ⟨b, hBX b.2⟩)⁻¹ i) = (x : Fin (k + 2) → ZMod 2) i
        rw [hρB]
        by_cases hi : i ≠ 0 ∧ i ≠ 1
        · obtain ⟨j, hj⟩ := (shift2 k).surjective ⟨i, hi⟩
          have hij : i = shift2 k j := by rw [hj]
          rw [hij, show (iota2 k (ρB b))⁻¹ (shift2 k j) = shift2 k ((ρB b)⁻¹ j) by
            rw [Perm.inv_eq_iff_eq, iota2_apply_shift, perm_apply_inv], hxs, hxs]
        · simp only [not_and_or, not_not] at hi
          rcases hi with rfl | rfl
          · rw [show (iota2 k (ρB b))⁻¹ 0 = 0 by rw [Perm.inv_eq_iff_eq, iota2_apply_zero]]
          · rw [show (iota2 k (ρB b))⁻¹ 1 = 1 by rw [Perm.inv_eq_iff_eq, iota2_apply_one]]
      have hc : ∀ b : ↥B, (b : GLV V) (w : V) - w ∈ fixedSpace B := by
        intro b
        have hbw : (b : GLV V) (w : V) ∈ commSpace X' ⊤ := mem_comm_of_mem hH (hBX' b.2) ⟨w, hcommB w.2⟩
        have h1 := hH.equiv ⟨b, hBX b.2⟩ ⟨w, hcommB w.2⟩ ⟨_, hbw⟩ rfl x hxw
        rw [hfixx] at h1
        have hk : (⟨_, hbw⟩ : ↥(commSpace X' ⊤)) - ⟨w, hcommB w.2⟩ ∈ β.ker := by
          rw [AddMonoidHom.mem_ker, map_sub, h1, hxw, sub_self]
        rw [hH.ker] at hk
        exact fun g hg => hk g (hBX' hg)
      have hcomm : ⁅B, B⁆ ≤ MulAction.stabilizer (GLV V) (w : V) := by
        rw [Subgroup.commutator_le]
        intro b₁ hb₁ b₂ hb₂
        rw [MulAction.mem_stabilizer_iff]
        obtain ⟨c₁, hc₁, e₁⟩ : ∃ c₁ ∈ fixedSpace B, b₁ (w : V) = w + c₁ :=
          ⟨_, hc ⟨b₁, hb₁⟩, by abel⟩
        obtain ⟨c₂, hc₂, e₂⟩ : ∃ c₂ ∈ fixedSpace B, b₂ (w : V) = w + c₂ :=
          ⟨_, hc ⟨b₂, hb₂⟩, by abel⟩
        have t₁ : b₁ ((w : V) - c₁) = w := by rw [map_sub, e₁, hc₁ b₁ hb₁]; abel
        have t₂ : b₂ ((w : V) - c₂) = w := by rw [map_sub, e₂, hc₂ b₂ hb₂]; abel
        have i₁ : b₁⁻¹ (w : V) = w - c₁ := by
          calc b₁⁻¹ (w : V) = b₁⁻¹ (b₁ ((w : V) - c₁)) := by rw [t₁]
            _ = w - c₁ := b₁.symm_apply_apply _
        have i₂ : b₂⁻¹ (w : V) = w - c₂ := by
          calc b₂⁻¹ (w : V) = b₂⁻¹ (b₂ ((w : V) - c₂)) := by rw [t₂]
            _ = w - c₂ := b₂.symm_apply_apply _
        have s2 : b₁⁻¹ ((w : V) - c₂) = w - c₁ - c₂ := by
          rw [map_sub, i₁, hc₂ _ (B.inv_mem hb₁)]
        have s3 : b₂ ((w : V) - c₁ - c₂) = w - c₁ := by
          rw [map_sub, map_sub, e₂, hc₁ _ hb₂, hc₂ _ hb₂]; abel
        have s4 : b₁ ((w : V) - c₁) = w := t₁
        show b₁ (b₂ (b₁⁻¹ (b₂⁻¹ (w : V)))) = w
        rw [i₂, s2, s3, s4]
      rw [hperf] at hcomm
      exact fun b hb => MulAction.mem_stabilizer_iff.1 (hcomm hb)
    · intro hw
      obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (βB w)
      rw [← hy]
      refine altHeart_fixed_eq_zero (by omega) y fun σ hσ => ?_
      obtain ⟨b, rfl⟩ := hρBonto σ hσ
      have h1 := hequiv b w w (hw b b.2).symm y hy.symm
      rw [← h1, hy]
  refine ⟨ρB, βB, ⟨le_rfl, fun x => ⟨fun _ => hρBA x, fun _ => x.2⟩, hsurjB, hker, hequiv⟩,
    hρBinj, hρBonto, hρB⟩

end CaseIHeart

end CFSG.CGT.Foote82
