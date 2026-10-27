module

public import CFSG.LocalAnalysis.GLTheoremB.Defs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem exists_mulEquiv_pi_fin {Q : Type*} [Group Q] [Finite Q] {ι : Type*} [Fintype ι]
    {K : Type*} [Group K] (H : ι → Subgroup Q) (e : ∀ i, ↥(H i) ≃* K)
    (hK : IsSimpleGroup K) (hKn : ∃ a b : K, a * b ≠ b * a)
    (hcomm : Pairwise fun i j => H i ≤ Subgroup.centralizer (H j : Set Q)) {n : ℕ}
    (hn : Fintype.card ι = n) :
    Nonempty (↥(⨆ i, H i) ≃* (Fin n → K)) := by
  classical
  have hcomm' : Pairwise fun i j : ι => ∀ x y : Q, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij x y hx hy
    exact (Subgroup.mem_centralizer_iff.mp (hcomm hij hx) y hy).symm
  have hcent : ∀ c : K, (∀ k : K, k * c = c * k) → c = 1 := by
    intro c hc
    have hc' : c ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]; exact hc
    rcases hK.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · rw [h] at hc'; simpa using hc'
    · obtain ⟨a, b, hab⟩ := hKn
      exfalso
      apply hab
      have : b ∈ Subgroup.center K := by rw [h]; trivial
      exact (Subgroup.mem_center_iff.mp this) a
  have hind : iSupIndep H := by
    intro i
    rw [Subgroup.disjoint_def]
    intro x hx hx'
    have hM : (⨆ (j) (_ : j ≠ i), H j) ≤ Subgroup.centralizer (H i : Set Q) :=
      iSup₂_le fun j hj => hcomm hj
    have hxc := hM hx'
    have h1 : e i ⟨x, hx⟩ = 1 := by
      apply hcent
      intro k
      obtain ⟨y, rfl⟩ := (e i).surjective k
      apply (e i).symm.injective
      simp only [map_mul, MulEquiv.symm_apply_apply]
      apply Subtype.ext
      simpa using (Subgroup.mem_centralizer_iff.mp hxc y.1 y.2)
    have h2 : (⟨x, hx⟩ : ↥(H i)) = 1 := (e i).injective (by rw [h1, map_one])
    simpa using congrArg Subtype.val h2
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm') hind
  have hrange := Subgroup.noncommPiCoprod_range (hcomm := hcomm')
  let f : (∀ i : ι, ↥(H i)) →* Q := Subgroup.noncommPiCoprod hcomm'
  let g : (∀ i : ι, ↥(H i)) ≃* ↥(⨆ i, H i) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let h : (∀ i : ι, ↥(H i)) ≃* (ι → K) := MulEquiv.piCongrRight e
  let σ : ι ≃ Fin n := Fintype.equivFinOfCardEq hn
  let c : (ι → K) ≃* (Fin n → K) :=
    { Equiv.piCongrLeft (fun _ : Fin n => K) σ with
      map_mul' := fun x y => by
        ext j
        simp [Equiv.piCongrLeft_apply_eq_cast] }
  exact ⟨g.symm.trans (h.trans c)⟩

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
