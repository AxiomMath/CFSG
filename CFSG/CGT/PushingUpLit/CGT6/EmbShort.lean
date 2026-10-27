module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

theorem map_shortU {G : Type} [Group G] (L : Subgroup G) :
    (shortU ↥L).map L.subtype = ⁅oTwoIn L, L⁆ := by
  unfold shortU
  rw [Subgroup.map_commutator]
  congr 1
  rw [← MonoidHom.range_eq_map]
  exact L.range_subtype

theorem eq_one_of_fixes_sum_zero {n : ℕ} (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (2 * n + 1)))
    (h : ∀ v : Fin (2 * n + 1) → ZMod 2, ∑ i, v i = 0 → permActionTwo σ v = v) : σ = 1 := by
  classical
  have hpair : ∀ a b : Fin (2 * n + 1), a ≠ b → σ⁻¹ a = a ∨ σ⁻¹ a = b := by
    intro a b hab
    let v : Fin (2 * n + 1) → ZMod 2 := fun i => if i = a ∨ i = b then 1 else 0
    have hv : ∑ i, v i = 0 := by
      have : ∑ i, v i = ∑ i ∈ ({a, b} : Finset (Fin (2 * n + 1))), (1 : ZMod 2) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i = a ∨ i = b)]
        have h1 : Finset.univ.filter (fun i => i = a ∨ i = b) = {a, b} := by
          ext i; simp
        have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ (i = a ∨ i = b)), v i = 0 :=
          Finset.sum_eq_zero fun i hi => by
            simp only [Finset.mem_filter] at hi
            simp [v, hi.2]
        rw [h2, add_zero, h1]
        refine Finset.sum_congr rfl fun i hi => ?_
        have : i = a ∨ i = b := by simpa using hi
        simp [v, this]
      rw [this, Finset.sum_const, Finset.card_pair hab]
      decide
    have h1 : (if σ⁻¹ a = a ∨ σ⁻¹ a = b then (1 : ZMod 2) else 0) =
        if a = a ∨ a = b then 1 else 0 := congrFun (h v hv) a
    by_contra hcon
    push Not at hcon
    have hc2 : σ.symm a ≠ a := hcon.1
    have hc3 : σ.symm a ≠ b := hcon.2
    simp [Equiv.Perm.inv_def, hc2, hc3] at h1
  apply Equiv.ext
  intro a
  have h3 : 2 < 2 * n + 1 := by omega
  let e0 : Fin (2 * n + 1) := ⟨0, by omega⟩
  let e1 : Fin (2 * n + 1) := ⟨1, by omega⟩
  let e2 : Fin (2 * n + 1) := ⟨2, h3⟩
  have key : ∀ b₁ b₂ : Fin (2 * n + 1), b₁ ≠ a → b₂ ≠ a → b₁ ≠ b₂ → σ⁻¹ a = a := by
    intro b₁ b₂ h1 h2 h12
    rcases hpair a b₁ h1.symm with h | h
    · exact h
    · rcases hpair a b₂ h2.symm with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') h12
  have hσ : σ⁻¹ a = a := by
    by_cases ha0 : a = e0
    · exact key e1 e2 (by rw [ha0]; simp [e0, e1, Fin.ext_iff]) (by rw [ha0]; simp [e0, e2, Fin.ext_iff])
        (by simp [e1, e2, Fin.ext_iff])
    · by_cases ha1 : a = e1
      · exact key e0 e2 (by rw [ha1]; simp [e0, e1, Fin.ext_iff]) (by rw [ha1]; simp [e1, e2, Fin.ext_iff])
          (by simp [e0, e2, Fin.ext_iff])
      · exact key e0 e1 (fun h => ha0 h.symm) (fun h => ha1 h.symm) (by simp [e0, e1, Fin.ext_iff])
  have : σ a = a := (Equiv.Perm.inv_eq_iff_eq.mp hσ).symm
  exact this

theorem centralizer_shortU_le_pCore {L : Type} [Group L] [Finite L] (hL : InClassX L) :
    Subgroup.centralizer (shortU L : Set L) ≤ pCore 2 L := by
  intro c hc
  have hc' : ∀ u ∈ shortU L, c * u * c⁻¹ = u := fun u hu => by
    have := Subgroup.mem_centralizer_iff.mp hc u hu
    calc c * u * c⁻¹ = u * c * c⁻¹ := by rw [← this]
      _ = u := by group
  rcases hL.2 with ⟨n, hn, φ, ψ, -, hsurj, -, hequiv⟩ | ⟨n, hn, φ, ψ, hsurj, -, hequiv⟩
  · have hσ : φ (c : L ⧸ pCore 2 L) = 1 := by
      have hfix : ∀ v : Fin (2 * n + 1) → ZMod 2, ∑ i, v i = 0 →
          permActionTwo ((φ (c : L ⧸ pCore 2 L) : alternatingGroup _) : Equiv.Perm _) v = v := by
        intro v hv
        obtain ⟨u, hu⟩ := hsurj v hv
        have hu' : c * (u : L) * c⁻¹ ∈ shortU L := by rw [hc' u u.2]; exact u.2
        have h1 := hequiv c u u.2 hu'
        have h2 : (⟨c * (u : L) * c⁻¹, hu'⟩ : ↥(shortU L)) = u := Subtype.ext (hc' u u.2)
        rw [h2, hu] at h1
        have h3 := Multiplicative.ofAdd.injective h1
        simpa using h3.symm
      have h1 : ((φ (c : L ⧸ pCore 2 L) : alternatingGroup _) : Equiv.Perm (Fin (2 * n + 1))) = 1 :=
        eq_one_of_fixes_sum_zero hn _ hfix
      exact Subtype.ext h1
    have : (c : L ⧸ pCore 2 L) = 1 := φ.injective (by rw [hσ, map_one])
    exact (QuotientGroup.eq_one_iff c).mp this
  · have hσ : φ (c : L ⧸ pCore 2 L) = 1 := by
      have hfix : ∀ w : Fin 2 → GaloisField 2 n,
          (φ (c : L ⧸ pCore 2 L) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w = w := by
        intro w
        obtain ⟨u, hu⟩ := hsurj (Multiplicative.ofAdd w)
        have hu' : c * (u : L) * c⁻¹ ∈ shortU L := by rw [hc' u u.2]; exact u.2
        have h1 := hequiv c u u.2 hu'
        have h2 : (⟨c * (u : L) * c⁻¹, hu'⟩ : ↥(shortU L)) = u := Subtype.ext (hc' u u.2)
        rw [h2, hu] at h1
        have h3 := Multiplicative.ofAdd.injective h1
        rw [toAdd_ofAdd] at h3
        exact h3.symm
      apply Subtype.ext
      ext i j
      have := congrFun (hfix (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
    have : (c : L ⧸ pCore 2 L) = 1 := φ.injective (by rw [hσ, map_one])
    exact (QuotientGroup.eq_one_iff c).mp this

theorem inf_centralizer_le_oTwoIn {G : Type} [Group G] [Finite G] {V Y : Subgroup G} [V.Normal]
    (hY : InClassX ↥Y) (hU : ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆) :
    Y ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoIn Y := by
  rintro y ⟨hyY, hyC⟩
  have hc : (⟨y, hyY⟩ : ↥Y) ∈ Subgroup.centralizer (shortU ↥Y : Set ↥Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    apply Subtype.ext
    have hu1 : (u : G) ∈ ⁅oTwoIn Y, Y⁆ := by
      rw [← map_shortU]
      exact ⟨u, hu, rfl⟩
    rw [← hU] at hu1
    have hu2 : (u : G) ∈ V := by
      have : ⁅V, Y⁆ ≤ V := by
        refine Subgroup.commutator_le_left V Y
      exact this hu1
    exact Subgroup.mem_centralizer_iff.mp hyC (u : G) hu2
  exact ⟨⟨y, hyY⟩, centralizer_shortU_le_pCore hY hc, rfl⟩

end CFSG.CGT.PushingUpLit.CGT6
