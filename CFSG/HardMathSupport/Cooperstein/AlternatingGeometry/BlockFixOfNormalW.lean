module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BlockFixOfNormal
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.StabNormalTwoGroup

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def blockTransp (i : ι) : Perm (ι × Bool) := swap (i, false) (i, true)

theorem blockStab_of_mem_normalizer {W : Subgroup (Perm (ι × Bool))} (hWF : W ≤ blockFix ι)
    (hWfl : ∀ i : ι, ∃ w ∈ W, w (i, false) = (i, true)) {g : Perm (ι × Bool)}
    (hg : g ∈ Subgroup.normalizer (W : Set (Perm (ι × Bool)))) : g ∈ blockStab ι := by
  have key : ∀ h ∈ Subgroup.normalizer (W : Set (Perm (ι × Bool))), ∀ i : ι,
      (h (i, false)).1 = (h (i, true)).1 := by
    intro h hh i
    obtain ⟨w, hw, hwf⟩ := hWfl i
    have hconj : h * w * h⁻¹ ∈ W := ((Subgroup.mem_normalizer_iff.1 hh) w).1 hw
    have := hWF hconj (h (i, false))
    have e : (h * w * h⁻¹) (h (i, false)) = h (i, true) := by simp [Perm.mul_apply, hwf]
    rw [e] at this
    exact this.symm
  have fwd : ∀ h ∈ Subgroup.normalizer (W : Set (Perm (ι × Bool))), ∀ x y : ι × Bool,
      x.1 = y.1 → (h x).1 = (h y).1 := by
    intro h hh x y hxy
    obtain ⟨i, a⟩ := x
    obtain ⟨j, b⟩ := y
    simp only at hxy
    subst hxy
    cases a <;> cases b
    · rfl
    · exact key h hh i
    · exact (key h hh i).symm
    · rfl
  intro x y
  refine ⟨fun h => ?_, fwd g hg x y⟩
  have hinv : g⁻¹ ∈ Subgroup.normalizer (W : Set (Perm (ι × Bool))) := inv_mem hg
  have := fwd g⁻¹ hinv (g x) (g y) h
  simpa using this

theorem conj_blockTransp {g : Perm (ι × Bool)} (hg : g ∈ blockStab ι) (i : ι) :
    g * blockTransp i * g⁻¹ = blockTransp (blockMap g hg i) := by
  have h1 : g * blockTransp i * g⁻¹ = swap (g (i, false)) (g (i, true)) := by
    rw [blockTransp, ← Equiv.swap_apply_apply]
  have hf : (g (i, false)).1 = blockMap g hg i := (blockMap_apply hg (i, false)).symm
  have ht : (g (i, true)).1 = blockMap g hg i := (blockMap_apply hg (i, true)).symm
  have hne : g (i, false) ≠ g (i, true) := fun h => by
    have := g.injective h
    simp at this
  rw [h1, blockTransp]
  rcases hP : g (i, false) with ⟨a, ha⟩
  rcases hQ : g (i, true) with ⟨b, hb⟩
  rw [hP] at hf hne
  rw [hQ] at ht hne
  have hf' : a = blockMap g hg i := hf
  have ht' : b = blockMap g hg i := ht
  subst hf'; subst ht'
  cases ha <;> cases hb
  · exact absurd rfl hne
  · rfl
  · exact swap_comm _ _
  · exact absurd rfl hne

theorem tt_mem_iff_of_mem_normalizer {W : Subgroup (Perm (ι × Bool))}
    {g : Perm (ι × Bool)} (hg : g ∈ Subgroup.normalizer (W : Set (Perm (ι × Bool))))
    (hgs : g ∈ blockStab ι) (i : ι) :
    blockTransp i ∈ W ↔ blockTransp (blockMap g hgs i) ∈ W := by
  rw [← conj_blockTransp hgs i]
  exact Subgroup.mem_normalizer_iff.1 hg _

theorem predStab_not (p : ι → Prop) : predStab (fun i => ¬ p i) = predStab p := by
  ext π
  exact forall_congr' fun i => not_iff_not

@[expose] noncomputable def blockMapHom : ↥(blockStab ι) →* Perm ι where
  toFun g := blockMap g.1 g.2
  map_one' := Equiv.ext fun a => blockMap_apply (blockStab ι).one_mem (a, false)
  map_mul' a b := blockMap_mul a.2 b.2

theorem blockMapHom_apply (g : ↥(blockStab ι)) (x : ι × Bool) :
    blockMapHom g x.1 = ((g : Perm (ι × Bool)) x).1 := blockMap_apply g.2 x

theorem le_blockFix_of_normal_isPGroup_W
    {W : Subgroup (Perm (ι × Bool))} (hWF : W ≤ blockFix ι)
    (hWfl : ∀ i : ι, ∃ w ∈ W, w (i, false) = (i, true))
    [DecidablePred fun i : ι => blockTransp i ∈ W]
    (hcardT : Fintype.card {i // blockTransp i ∈ W} ≠ 2 ∧ Fintype.card {i // blockTransp i ∈ W} ≠ 4)
    (hcardC : Fintype.card {i // ¬ blockTransp i ∈ W} ≠ 2 ∧
      Fintype.card {i // ¬ blockTransp i ∈ W} ≠ 4)
    {N Q : Subgroup (Perm (ι × Bool))}
    (hNW : N ≤ Subgroup.normalizer (W : Set (Perm (ι × Bool))))
    (hNlift : ∀ π : Perm ι, (∀ i, blockTransp i ∈ W ↔ blockTransp (π i) ∈ W) →
      prodCongrLeft (fun _ : Bool => π) ∈ N)
    (hQN : Q ≤ N) (hQ : IsPGroup 2 Q) (hQn : ∀ x ∈ N, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) :
    Q ≤ blockFix ι := by
  have hstab : ∀ g ∈ N, g ∈ blockStab ι := fun g hg =>
    blockStab_of_mem_normalizer hWF hWfl (hNW hg)
  set Q' : Subgroup (Perm ι) := (Q.subgroupOf (blockStab ι)).map blockMapHom with hQ'
  have hQ'p : IsPGroup 2 Q' :=
    (hQ.comap_of_injective _ (blockStab ι).subtype_injective).map blockMapHom
  have hQ's : Q' ≤ predStab (fun i : ι => blockTransp i ∈ W) := by
    rintro _ ⟨⟨q, hqs⟩, hq, rfl⟩ i
    exact tt_mem_iff_of_mem_normalizer (hNW (hQN (Subgroup.mem_subgroupOf.1 hq))) hqs i
  have hQ'n : ∀ σ ∈ predStab (fun i : ι => blockTransp i ∈ W), ∀ π ∈ Q', σ * π * σ⁻¹ ∈ Q' := by
    rintro σ hσ _ ⟨⟨q, hqs⟩, hq, rfl⟩
    have hqQ : q ∈ Q := Subgroup.mem_subgroupOf.1 hq
    have hx : prodCongrLeft (fun _ : Bool => σ) ∈ N := hNlift σ hσ
    have hxs := hstab _ hx
    have hbx : blockMapHom (⟨prodCongrLeft (fun _ : Bool => σ), hxs⟩ : ↥(blockStab ι)) = σ := by
      ext a
      have := blockMapHom_apply (⟨prodCongrLeft (fun _ : Bool => σ), hxs⟩ : ↥(blockStab ι)) (a, false)
      exact this.trans rfl
    have hxqN : prodCongrLeft (fun _ : Bool => σ) * q * (prodCongrLeft (fun _ : Bool => σ))⁻¹ ∈ Q :=
      hQn _ hx q hqQ
    refine ⟨⟨_, (blockStab ι).mul_mem ((blockStab ι).mul_mem hxs hqs) ((blockStab ι).inv_mem hxs)⟩,
      Subgroup.mem_subgroupOf.2 hxqN, ?_⟩
    have : (⟨prodCongrLeft (fun _ : Bool => σ) * q * (prodCongrLeft (fun _ : Bool => σ))⁻¹,
        (blockStab ι).mul_mem ((blockStab ι).mul_mem hxs hqs) ((blockStab ι).inv_mem hxs)⟩ :
        ↥(blockStab ι)) = ⟨_, hxs⟩ * ⟨q, hqs⟩ * ⟨_, hxs⟩⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hbx]
  have h1 := eq_one_of_normal_isPGroup_pred (fun i : ι => blockTransp i ∈ W) hcardT hQ'p hQ's hQ'n
  have hQ's' : Q' ≤ predStab (fun i : ι => ¬ blockTransp i ∈ W) := by rw [predStab_not (fun i : ι => blockTransp i ∈ W)]; exact hQ's
  have hQ'n' : ∀ σ ∈ predStab (fun i : ι => ¬ blockTransp i ∈ W), ∀ π ∈ Q', σ * π * σ⁻¹ ∈ Q' := by
    rw [predStab_not (fun i : ι => blockTransp i ∈ W)]; exact hQ'n
  have h2 := eq_one_of_normal_isPGroup_pred (fun i : ι => ¬ blockTransp i ∈ W) hcardC hQ'p hQ's' hQ'n'
  intro q hq
  have hqs : q ∈ blockStab ι := hstab q (hQN hq)
  apply mem_blockFix_of_blockMap_eq_one hqs
  have hmem : blockMapHom (⟨q, hqs⟩ : ↥(blockStab ι)) ∈ Q' :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hq)
  ext i
  by_cases hi : blockTransp i ∈ W
  · exact h1 _ hmem i hi
  · exact h2 _ hmem i hi

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
