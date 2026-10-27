module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.CanonicalHeart
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.RankThree.PartTwo CFSG.QuasithinUnique

theorem irreducible_of_natural {G : Type*} [Group G] {L T Z : Subgroup G} (hZT : Z ≤ T) {d : ℕ}
    (hd : 4 ≤ d) (π : ↥T →* Multiplicative (Heart d)) (hπs : Function.Surjective π)
    (hker : π.ker = Z.subgroupOf T) (θ : ↥L →* Perm (Fin d))
    (hθ : alternatingGroup (Fin d) ≤ θ.range)
    (hequiv : ∀ (l : ↥L) (t t' : ↥T), (t' : G) = (l : G) * t * (l : G)⁻¹ →
      π t' = Multiplicative.ofAdd (heartAct (θ l) (Multiplicative.toAdd (π t)))) :
    Z < T ∧ ∀ W : Subgroup G, Z ≤ W → W ≤ T → L ≤ Subgroup.normalizer (W : Set G) →
      W = Z ∨ W = T := by
  have hntriv : Nontrivial (Heart d) := heart_nontrivial (by omega)
  refine ⟨lt_of_le_of_ne hZT ?_, ?_⟩
  · intro hZ
    obtain ⟨x, hx⟩ := exists_ne (0 : Heart d)
    obtain ⟨t, ht⟩ := hπs (Multiplicative.ofAdd x)
    have : t ∈ π.ker := by
      rw [hker, Subgroup.mem_subgroupOf, hZ]
      exact t.2
    rw [MonoidHom.mem_ker] at this
    rw [this] at ht
    exact hx (by simpa using ht.symm)
  · intro W hZW hWT hLW
    set W' : Subgroup ↥T := W.subgroupOf T with hW'
    let U : AddSubgroup (Heart d) := AddSubgroup.toSubgroup'.symm (W'.map π)
    have hmemU : ∀ u : Heart d, u ∈ U ↔ Multiplicative.ofAdd u ∈ W'.map π := fun u => Iff.rfl
    have hinv : ∀ σ ∈ alternatingGroup (Fin d), ∀ u ∈ U, heartAct σ u ∈ U := by
      intro σ hσ u hu
      obtain ⟨l, hl⟩ := hθ hσ
      rw [hmemU] at hu ⊢
      obtain ⟨w, hw, hwu⟩ := hu
      have hwW : (w : G) ∈ W := hw
      have hlw : (l : G) * w * (l : G)⁻¹ ∈ W := by
        have := (Subgroup.mem_normalizer_iff.1 (hLW l.2) (w : G)).1 hwW
        exact this
      refine ⟨⟨(l : G) * w * (l : G)⁻¹, hWT hlw⟩, hlw, ?_⟩
      rw [hequiv l w ⟨(l : G) * w * (l : G)⁻¹, hWT hlw⟩ rfl, hwu, hl]
      rfl
    rcases heart_irreducible hd U hinv with h | h
    · left
      apply le_antisymm
      · intro w hw
        have : π ⟨w, hWT hw⟩ ∈ W'.map π := ⟨⟨w, hWT hw⟩, hw, rfl⟩
        have hu : Multiplicative.toAdd (π ⟨w, hWT hw⟩) ∈ U := this
        rw [h] at hu
        have h0 : π ⟨w, hWT hw⟩ = 1 := by
          have := (AddSubgroup.mem_bot.1 hu)
          simpa using congrArg Multiplicative.ofAdd this
        have : (⟨w, hWT hw⟩ : ↥T) ∈ π.ker := h0
        rw [hker, Subgroup.mem_subgroupOf] at this
        exact this
      · exact hZW
    · right
      apply le_antisymm hWT
      intro t ht
      have hu : Multiplicative.toAdd (π ⟨t, ht⟩) ∈ U := by rw [h]; exact AddSubgroup.mem_top _
      obtain ⟨w, hw, hwt⟩ := (hmemU _).1 hu
      have hwW : (w : G) ∈ W := hw
      have hkerm : (⟨t, ht⟩ : ↥T) * w⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have : π w = π ⟨t, ht⟩ := by simpa using hwt
        rw [this, mul_inv_cancel]
      rw [hker, Subgroup.mem_subgroupOf] at hkerm
      have hmul : ((⟨t, ht⟩ : ↥T) * w⁻¹ : ↥T).1 * (w : G) ∈ W :=
        W.mul_mem (hZW hkerm) hwW
      simpa using hmul

theorem hasIrreducibleCommutatorQuotient_of_natural {G : Type} [Group G] {L V : Subgroup G}
    {d : ℕ} (hd : 4 ≤ d) (π : ↥⁅V, L⁆ →* Multiplicative (Heart d))
    (hπs : Function.Surjective π)
    (hker : π.ker = (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅V, L⁆)
    (θ : ↥L →* Perm (Fin d)) (hθ : alternatingGroup (Fin d) ≤ θ.range)
    (hequiv : ∀ (l : ↥L) (t t' : ↥⁅V, L⁆), (t' : G) = (l : G) * t * (l : G)⁻¹ →
      π t' = Multiplicative.ofAdd (heartAct (θ l) (Multiplicative.toAdd (π t)))) :
    HasIrreducibleCommutatorQuotient L V :=
  irreducible_of_natural inf_le_left hd π hπs hker θ hθ hequiv

theorem hasIrreducibleCommutatorQuotient_of_altNatural {G : Type} [Group G] {L V : Subgroup G}
    {d : ℕ} (hd : 4 ≤ d) (π : ↥⁅V, L⁆ →* Multiplicative (altHeart d))
    (hπs : Function.Surjective π)
    (hker : π.ker = (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅V, L⁆)
    (θ : ↥L →* Perm (Fin d)) (hθ : alternatingGroup (Fin d) ≤ θ.range)
    (hequiv : ∀ (l : ↥L) (t t' : ↥⁅V, L⁆), (t' : G) = (l : G) * t * (l : G)⁻¹ →
      ∀ x : evenWeight d, Multiplicative.toAdd (π t) = (QuotientAddGroup.mk x : altHeart d) →
        Multiplicative.toAdd (π t') =
          (QuotientAddGroup.mk (evenWeightPerm (θ l) x) : altHeart d)) :
    HasIrreducibleCommutatorQuotient L V := by
  let e := heartEquivAlt d
  let π' : ↥⁅V, L⁆ →* Multiplicative (Heart d) :=
    (AddEquiv.toMultiplicative e.symm).toMonoidHom.comp π
  have hπ's : Function.Surjective π' := by
    intro u
    obtain ⟨t, ht⟩ := hπs (Multiplicative.ofAdd (e (Multiplicative.toAdd u)))
    refine ⟨t, ?_⟩
    simp [π', ht]
  have hker' : π'.ker = π.ker := by
    ext t
    simp [π', MonoidHom.mem_ker]
  refine hasIrreducibleCommutatorQuotient_of_natural (by omega) π' hπ's (hker'.trans hker) θ hθ ?_
  intro l t t' htt'
  obtain ⟨f, hf⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π' t))
  have h1 : Multiplicative.toAdd (π t) = (QuotientAddGroup.mk ⟨f.1, by rw [← evenSub_eq]; exact f.2⟩ :
      altHeart d) := by
    have : e (Multiplicative.toAdd (π' t)) = Multiplicative.toAdd (π t) := by simp [π', e]
    rw [← this, ← hf]; rfl
  have h2 := hequiv l t t' htt' ⟨f.1, by rw [← evenSub_eq]; exact f.2⟩ h1
  have h3 : e (heartAct (θ l) (Multiplicative.toAdd (π' t))) = Multiplicative.toAdd (π t') := by
    rw [← hf, h2]; rfl
  show π' t' = Multiplicative.ofAdd (heartAct (θ l) (Multiplicative.toAdd (π' t)))
  have : Multiplicative.toAdd (π' t') = e.symm (Multiplicative.toAdd (π t')) := rfl
  apply Multiplicative.toAdd.injective
  rw [this, ← h3]
  simp

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
