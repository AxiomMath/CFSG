module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.LieType.Chevalley.ParabolicWeylStabilizer
public import CFSG.LieType.Chevalley.KernelComponentRoots

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis


structure LeviDataFor (τ : Tag) (J₂ : Set (Fin τ.rank)) (S₁ : Set (Fin τ.rank → ℤ)) {k : ℕ}
    (ω : Fin k → WeylGroup τ) : Prop where
  min : ∀ i, ∀ β ∈ parabolicPosRoots τ (Jθ τ), 0 < height (ω i • β)
  perp : ∀ β ∈ parabolicPosRoots τ (Jθ τ),
    (∀ i, β ∈ (fun γ => ω i • γ) '' parabolicPosRoots τ (Jθ τ)) → β ∈ parabolicRoots τ J₂
  fix : ∀ w : WeylGroup τ, w • highRoot τ = highRoot τ →
    (∀ i, w • (ω i • highRoot τ) = ω i • highRoot τ) → w ∈ parabolicWeylGroup τ J₂
  mem : ∀ i, ω i • highRoot τ ∈ S₁ ∧ (ω i • highRoot τ) (iθ τ) = 1
  lattice : ∀ v : Fin τ.rank → ℤ, (∀ j ∈ J₂, ∑ l, τ.cartan j l * v l = 0) →
    ∃ (c₀ : ℤ) (co : Fin k → ℤ), v = c₀ • highRoot τ + ∑ m, co m • (ω m • highRoot τ)


structure TwClassData (c : TwClass) : Prop where
  wθ : c.w • highRoot c.tag = highRoot c.tag
  wS₂ : ∀ α ∈ c.S₂, c.w⁻¹ • α ∈ c.S₂
  levi : ∃ (k : ℕ) (ω : Fin k → WeylGroup c.tag),
    LeviDataFor c.tag {i : Fin c.tag.rank | i.val ∈ c.J₂} c.S₁ ω

section Words

variable {τ : Tag}

theorem wordProd_smul_foldr (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd ω • v = ω.foldr (reflect τ) v := by
  induction ω with
  | nil => simp
  | cons i ω ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem wordProd_inv_smul_foldr (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    ((coxeterSystem τ).wordProd ω)⁻¹ • v = ω.reverse.foldr (reflect τ) v := by
  rw [← CoxeterSystem.wordProd_reverse, wordProd_smul_foldr]

theorem iform_sub_right (x y z : Fin τ.rank → ℤ) :
    CFSG.LieType.Steinberg.Adjoint.iform x (y - z) =
      CFSG.LieType.Steinberg.Adjoint.iform x y - CFSG.LieType.Steinberg.Adjoint.iform x z := by
  rw [Heis.iform_eq_sum_single, Heis.iform_eq_sum_single, Heis.iform_eq_sum_single,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.sub_apply, mul_sub]

theorem fix_of_cert {k : ℕ} (J₂ : Finset ℕ) (δ₀ : Fin τ.rank → ℤ) (δ : Fin k → Fin τ.rank → ℤ)
    (μ₀ : Fin τ.rank → ℤ) (μ : Fin τ.rank → Fin k → ℤ) (Nf : Fin τ.rank → ℤ)
    (hNf : ∀ j : Fin τ.rank, j.val ∉ J₂ → Nf j ≠ 0)
    (hμ : ∀ j : Fin τ.rank, j.val ∉ J₂ → ∀ l : Fin τ.rank,
      μ₀ j * CFSG.LieType.Steinberg.Adjoint.iform δ₀ (Pi.single l 1) +
        ∑ m, μ j m * CFSG.LieType.Steinberg.Adjoint.iform (δ m) (Pi.single l 1) =
          Nf j * (if l = j then 1 else 0))
    (x : Fin τ.rank → ℤ) (h0 : CFSG.LieType.Steinberg.Adjoint.iform δ₀ x = 0)
    (hδ : ∀ m, CFSG.LieType.Steinberg.Adjoint.iform (δ m) x = 0) (j : Fin τ.rank)
    (hj : j.val ∉ J₂) : x j = 0 := by
  have hx0 : ∑ l, CFSG.LieType.Steinberg.Adjoint.iform δ₀ (Pi.single l 1) * x l = 0 := by
    rw [← Heis.iform_eq_sum_single]; exact h0
  have hxm : ∀ m, ∑ l, CFSG.LieType.Steinberg.Adjoint.iform (δ m) (Pi.single l 1) * x l = 0 := by
    intro m; rw [← Heis.iform_eq_sum_single]; exact hδ m
  have h1 : Nf j * x j = ∑ l, (μ₀ j * CFSG.LieType.Steinberg.Adjoint.iform δ₀ (Pi.single l 1) +
        ∑ m, μ j m * CFSG.LieType.Steinberg.Adjoint.iform (δ m) (Pi.single l 1)) * x l := by
    have : ∀ l, (μ₀ j * CFSG.LieType.Steinberg.Adjoint.iform δ₀ (Pi.single l 1) +
        ∑ m, μ j m * CFSG.LieType.Steinberg.Adjoint.iform (δ m) (Pi.single l 1)) * x l =
        if l = j then Nf j * x j else 0 := by
      intro l
      rw [hμ j hj l]
      by_cases hl : l = j
      · subst hl; simp
      · simp [hl]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h2 : ∑ l, (μ₀ j * CFSG.LieType.Steinberg.Adjoint.iform δ₀ (Pi.single l 1) +
        ∑ m, μ j m * CFSG.LieType.Steinberg.Adjoint.iform (δ m) (Pi.single l 1)) * x l =
      μ₀ j * ∑ l, CFSG.LieType.Steinberg.Adjoint.iform δ₀ (Pi.single l 1) * x l +
        ∑ m, μ j m * ∑ l, CFSG.LieType.Steinberg.Adjoint.iform (δ m) (Pi.single l 1) * x l := by
    have e1 : ∀ l, (μ₀ j * CFSG.LieType.Steinberg.Adjoint.iform δ₀ (Pi.single l 1) +
        ∑ m, μ j m * CFSG.LieType.Steinberg.Adjoint.iform (δ m) (Pi.single l 1)) * x l =
        μ₀ j * (CFSG.LieType.Steinberg.Adjoint.iform δ₀ (Pi.single l 1) * x l) +
          ∑ m, μ j m * (CFSG.LieType.Steinberg.Adjoint.iform (δ m) (Pi.single l 1) * x l) := by
      intro l
      rw [add_mul, Finset.sum_mul]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun m _ => by ring
    simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have h3 : Nf j * x j = 0 := by
    rw [h1, h2, hx0]
    simp [hxm]
  exact (mul_eq_zero.1 h3).resolve_left (hNf j hj)

theorem lattice_of_cert {k : ℕ} (J₂ : Finset ℕ) (δ₀ : Fin τ.rank → ℤ) (δ : Fin k → Fin τ.rank → ℤ)
    (U₀ : Fin τ.rank → ℤ) (U : Fin τ.rank → Fin k → ℤ) (N : ℤ) (hN : N ≠ 0)
    (W : Fin τ.rank → Fin τ.rank → ℤ)
    (hU : ∀ j l : Fin τ.rank, N * ((if j = l then 1 else 0) -
      (δ₀ j * U₀ l + ∑ m, δ m j * U l m)) =
        ∑ i : Fin τ.rank, if i.val ∈ J₂ then W j i * τ.cartan i l else 0)
    (v : Fin τ.rank → ℤ) (hv : ∀ j : Fin τ.rank, j.val ∈ J₂ → ∑ l, τ.cartan j l * v l = 0) :
    ∃ (c₀ : ℤ) (co : Fin k → ℤ), v = c₀ • δ₀ + ∑ m, co m • δ m := by
  refine ⟨∑ l, U₀ l * v l, fun m => ∑ l, U l m * v l, ?_⟩
  funext j
  have hR : (∑ l, U₀ l * v l) * δ₀ j + ∑ m, (∑ l, U l m * v l) * δ m j =
      ∑ l, (δ₀ j * U₀ l + ∑ m, δ m j * U l m) * v l := by
    have e1 : ∀ l, (δ₀ j * U₀ l + ∑ m, δ m j * U l m) * v l =
        δ₀ j * (U₀ l * v l) + ∑ m, δ m j * (U l m * v l) := by
      intro l
      rw [add_mul, Finset.sum_mul]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun m _ => by ring
    calc (∑ l, U₀ l * v l) * δ₀ j + ∑ m, (∑ l, U l m * v l) * δ m j
        = δ₀ j * ∑ l, U₀ l * v l + ∑ m, δ m j * ∑ l, U l m * v l := by
          rw [mul_comm (∑ l, U₀ l * v l) (δ₀ j)]
          congr 1
          exact Finset.sum_congr rfl fun m _ => mul_comm _ _
      _ = ∑ l, δ₀ j * (U₀ l * v l) + ∑ m, ∑ l, δ m j * (U l m * v l) := by
          rw [Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]
      _ = ∑ l, (δ₀ j * (U₀ l * v l) + ∑ m, δ m j * (U l m * v l)) := by
          rw [Finset.sum_add_distrib]
          congr 1
          exact Finset.sum_comm
      _ = ∑ l, (δ₀ j * U₀ l + ∑ m, δ m j * U l m) * v l :=
          Finset.sum_congr rfl fun l _ => (e1 l).symm
  have hN0 : N * (v j - ∑ l, (δ₀ j * U₀ l + ∑ m, δ m j * U l m) * v l) = 0 := by
    have e2 : v j = ∑ l, (if j = l then 1 else 0) * v l := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hl
        simp [Ne.symm hl]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have e3 : N * (v j - ∑ l, (δ₀ j * U₀ l + ∑ m, δ m j * U l m) * v l) =
        ∑ l, N * ((if j = l then 1 else 0) - (δ₀ j * U₀ l + ∑ m, δ m j * U l m)) * v l := by
      conv_lhs => rw [e2]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e3]
    have e4 : ∀ l, N * ((if j = l then 1 else 0) - (δ₀ j * U₀ l + ∑ m, δ m j * U l m)) * v l =
        ∑ i : Fin τ.rank, if i.val ∈ J₂ then W j i * (τ.cartan i l * v l) else 0 := by
      intro l
      rw [hU j l, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    simp only [e4]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i.val ∈ J₂
    · simp only [hi, if_true]
      rw [← Finset.mul_sum, hv i hi, mul_zero]
    · simp [hi]
  have h5 : v j = ∑ l, (δ₀ j * U₀ l + ∑ m, δ m j * U l m) * v l := by
    have := (mul_eq_zero.1 hN0).resolve_left hN
    linarith
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [h5, ← hR]

theorem leviDataFor_of_words {k : ℕ} (J₂ : Set (Fin τ.rank)) (S₁ : Set (Fin τ.rank → ℤ))
    (words : Fin k → List (Fin τ.rank))
    (hmin : ∀ i, ∀ β ∈ rootFinset τ, β (iθ τ) = 0 → 0 < height β →
      0 < height ((words i).foldr (reflect τ) β))
    (hperp : ∀ β ∈ rootFinset τ, β (iθ τ) = 0 → 0 < height β →
      (∀ i, ((words i).reverse.foldr (reflect τ) β) (iθ τ) = 0 ∧
        0 < height ((words i).reverse.foldr (reflect τ) β)) → ∀ j, j ∉ J₂ → β j = 0)
    (hfix : ∀ x : Fin τ.rank → ℤ,
      CFSG.LieType.Steinberg.Adjoint.iform (highRoot τ) x = 0 →
      (∀ i, CFSG.LieType.Steinberg.Adjoint.iform ((words i).foldr (reflect τ) (highRoot τ)) x = 0) →
      ∀ j, j ∉ J₂ → x j = 0)
    (hS₁ : ∀ i, (words i).foldr (reflect τ) (highRoot τ) ∈ S₁)
    (hdeg : ∀ i, ((words i).foldr (reflect τ) (highRoot τ)) (iθ τ) = 1)
    (hlat : ∀ v : Fin τ.rank → ℤ, (∀ j ∈ J₂, ∑ l, τ.cartan j l * v l = 0) →
      ∃ (c₀ : ℤ) (co : Fin k → ℤ), v = c₀ • highRoot τ +
        ∑ m, co m • ((words m).foldr (reflect τ) (highRoot τ))) :
    LeviDataFor τ J₂ S₁ (fun i : Fin k => (coxeterSystem τ).wordProd (words i)) := by
  have hA : ∀ {β : Fin τ.rank → ℤ}, β ∈ parabolicPosRoots τ (Jθ τ) ↔
      IsRoot τ β ∧ β (iθ τ) = 0 ∧ 0 < height β := by
    intro β
    constructor
    · rintro ⟨⟨hr, h0⟩, -, hp⟩
      exact ⟨hr, h0 (iθ τ) (by simp [Jθ]), hp⟩
    · rintro ⟨hr, h0, hp⟩
      refine ⟨⟨hr, fun i hi => ?_⟩, hr, hp⟩
      have : i = iθ τ := by simpa [Jθ] using hi
      subst this
      exact h0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i β hβ
    obtain ⟨hr, h0, hp⟩ := hA.1 hβ
    rw [wordProd_smul_foldr]
    exact hmin i β (mem_rootFinset.2 hr) h0 hp
  · intro β hβ hall
    obtain ⟨hr, h0, hp⟩ := hA.1 hβ
    refine ⟨hr, fun j hj => ?_⟩
    refine hperp β (mem_rootFinset.2 hr) h0 hp (fun i => ?_) j hj
    obtain ⟨γ, hγ, hγβ⟩ := hall i
    obtain ⟨hγr, hγ0, hγp⟩ := hA.1 hγ
    have : (words i).reverse.foldr (reflect τ) β = γ := by
      rw [← wordProd_inv_smul_foldr, ← hγβ]
      simp
    rw [this]
    exact ⟨hγ0, hγp⟩
  · intro w hwθ hwδ
    rw [← SetLike.mem_coe, (parabolic_Weyl_coordinate_stabilizer τ J₂).1]
    intro v j hj
    have key : ∀ δ : Fin τ.rank → ℤ, w • δ = δ →
        CFSG.LieType.Steinberg.Adjoint.iform δ (w • v - v) = 0 := by
      intro δ hδ
      have := iform_smul w δ v
      rw [hδ] at this
      rw [iform_sub_right, this, sub_self]
    have h := hfix (w • v - v) (key _ hwθ) (fun i => by
      refine key _ ?_
      have := hwδ i
      rwa [wordProd_smul_foldr] at this) j hj
    simpa [sub_eq_zero] using h
  · intro i
    have h1 := hS₁ i
    have h2 := hdeg i
    rw [wordProd_smul_foldr]
    exact ⟨h1, h2⟩
  · intro v hv
    obtain ⟨c₀, co, hco⟩ := hlat v hv
    refine ⟨c₀, co, ?_⟩
    rw [hco]
    simp only [wordProd_smul_foldr]

theorem leviDataFor_of_cert {k : ℕ} (J₂ : Finset ℕ) (S₁ : Set (Fin τ.rank → ℤ))
    (words : Fin k → List (Fin τ.rank))
    (hmin : ∀ i, ∀ β ∈ rootFinset τ, β (iθ τ) = 0 → 0 < height β →
      0 < height ((words i).foldr (reflect τ) β))
    (hperp : ∀ β ∈ rootFinset τ, β (iθ τ) = 0 → 0 < height β →
      (∀ i, ((words i).reverse.foldr (reflect τ) β) (iθ τ) = 0 ∧
        0 < height ((words i).reverse.foldr (reflect τ) β)) →
      ∀ j : Fin τ.rank, j.val ∉ J₂ → β j = 0)
    (hS₁ : ∀ i, (words i).foldr (reflect τ) (highRoot τ) ∈ S₁)
    (hdeg : ∀ i, ((words i).foldr (reflect τ) (highRoot τ)) (iθ τ) = 1)
    (μ₀ : Fin τ.rank → ℤ) (μ : Fin τ.rank → Fin k → ℤ) (Nf : Fin τ.rank → ℤ)
    (hNf : ∀ j : Fin τ.rank, j.val ∉ J₂ → Nf j ≠ 0)
    (hμ : ∀ j : Fin τ.rank, j.val ∉ J₂ → ∀ l : Fin τ.rank,
      μ₀ j * CFSG.LieType.Steinberg.Adjoint.iform (highRoot τ) (Pi.single l 1) +
        ∑ m, μ j m * CFSG.LieType.Steinberg.Adjoint.iform
          ((words m).foldr (reflect τ) (highRoot τ)) (Pi.single l 1) =
          Nf j * (if l = j then 1 else 0))
    (U₀ : Fin τ.rank → ℤ) (U : Fin τ.rank → Fin k → ℤ) (N : ℤ) (hN : N ≠ 0)
    (W : Fin τ.rank → Fin τ.rank → ℤ)
    (hU : ∀ j l : Fin τ.rank, N * ((if j = l then 1 else 0) -
      (highRoot τ j * U₀ l + ∑ m, ((words m).foldr (reflect τ) (highRoot τ)) j * U l m)) =
        ∑ i : Fin τ.rank, if i.val ∈ J₂ then W j i * τ.cartan i l else 0) :
    LeviDataFor τ {i : Fin τ.rank | i.val ∈ J₂} S₁
      (fun i : Fin k => (coxeterSystem τ).wordProd (words i)) :=
  leviDataFor_of_words _ S₁ words hmin hperp
    (fun x h0 hall j hj => fix_of_cert J₂ (highRoot τ)
      (fun m => (words m).foldr (reflect τ) (highRoot τ)) μ₀ μ Nf hNf hμ x h0 hall j hj)
    hS₁ hdeg
    (fun v hv => lattice_of_cert J₂ (highRoot τ)
      (fun m => (words m).foldr (reflect τ) (highRoot τ)) U₀ U N hN W hU v hv)

end Words

theorem mem_S₁_of_orth (c : TwClass) {δ : Fin c.tag.rank → ℤ} (hδ : δ ∈ rootFinset c.tag)
    (h : ∀ j : Fin c.tag.rank, j.val ∈ c.J₂ →
      CFSG.LieType.Steinberg.Adjoint.iform δ (Pi.single j 1) = 0) : δ ∈ c.S₁ := by
  refine ⟨mem_rootFinset.1 hδ, fun α hα => ?_⟩
  rw [Heis.iform_eq_sum_single]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j.val ∈ c.J₂
  · rw [h j hj, zero_mul]
  · rw [hα.2 j hj, mul_zero]

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux
