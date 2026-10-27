module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Step2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Step7
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Step8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5TDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.HNRecog

private theorem isSylow2In_and_conj_u_of_tfacts (hT : TMUFacts)
    {S : Subgroup (Equiv.Perm (Fin 1408))} (hS : Good S (elemA * elemZ)) {k : ℕ} (hk : k < 2)
    (hY : S ⊓ Subgroup.centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408))) = yK k)
    (tf : TFacts k) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408)))) = 240 ∧
      IsSylow2In S (tSub k) ∧
      ∃ g ∈ S, g * (elemA * elemZ) * g⁻¹ = uElt k := by
  haveI := hS.simple
  have htY : elemA * elemZ ∈
      S ⊓ Subgroup.centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408))) :=
    ⟨hS.mem, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hcomm : ∀ y ∈ S ⊓ Subgroup.centralizer ({elemA * elemZ} :
        Set (Equiv.Perm (Fin 1408))),
      (elemA * elemZ) * y = y * (elemA * elemZ) := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
  have hYcard : Nat.card ↥(S ⊓ Subgroup.centralizer ({elemA * elemZ} :
      Set (Equiv.Perm (Fin 1408)))) = 240 :=
    (step2 hS.cover htY hcomm hS.ne).1
  have hTY : tSub k ≤ S ⊓ Subgroup.centralizer ({elemA * elemZ} :
      Set (Equiv.Perm (Fin 1408))) := by
    rw [hY]
    exact tSub_le_yK k
  have hSyl : IsSylow2In S (tSub k) :=
    sylow_of_center hYcard hTY tf.card_T tf.t₀_mem hS.ne tf.cen
  have hy1A : yOne k ∈ S ⊓ Subgroup.centralizer ({elemA * elemZ} :
      Set (Equiv.Perm (Fin 1408))) := by
    rw [hY]
    exact yOne_mem hk
  have hy2A : yTwo k ∈ S ⊓ Subgroup.centralizer ({elemA * elemZ} :
      Set (Equiv.Perm (Fin 1408))) := by
    rw [hY]
    exact yTwo_mem hk
  have hnonab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a :=
    ⟨yOne k, hy1A.1, yTwo k, hy2A.1, tf.nonab⟩
  obtain ⟨g, hgS, hg⟩ :=
    exists_conj_u hnonab hSyl tf.M_le tf.relIndex_M tf.inv_M tf.u_mem tf.u_not_M tf.u_ord
  exact ⟨hYcard, hSyl, g, hgS, hg⟩

theorem exists_h_of_tmuFacts (hT : TMUFacts) {S : Subgroup (Equiv.Perm (Fin 1408))}
    (hS : Good S (elemA * elemZ)) {k : ℕ} (hk : k < 2)
    (hY : S ⊓ Subgroup.centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408))) = yK k) :
    k = 0 ∧ IsSylow2In S (tSub 0) ∧
      ∃ h ∈ S, h * (elemA * elemZ) * h⁻¹ = uElt 0 ∧
        (h * uElt 0 * h⁻¹ = elemA * elemZ ∨ h * uElt 0 * h⁻¹ = elemA * elemZ * uElt 0) := by
  have hk01 : k = 0 ∨ k = 1 := by omega
  have tf : TFacts k := by
    rcases hk01 with rfl | rfl
    · exact hT.k0
    · exact hT.k1
  obtain ⟨hYcard, hSyl, g, hgS, hg⟩ := isSylow2In_and_conj_u_of_tfacts hT hS hk hY tf
  rcases hk01 with rfl | rfl
  ·
    have hTY0 : tSub 0 ≤ S ⊓ Subgroup.centralizer ({elemA * elemZ} :
        Set (Equiv.Perm (Fin 1408))) := by
      rw [hY]
      exact tSub_le_yK 0
    have hSylY : IsSylow2In (S ⊓ Subgroup.centralizer ({elemA * elemZ} :
        Set (Equiv.Perm (Fin 1408)))) (tSub 0) :=
      isSylow2In_of_card hTY0 hT.k0.card_T hYcard
    have ht₀2 : orderOf (elemA * elemZ) = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact hS.sq) hS.ne
    have hcommT : ∀ x ∈ tSub 0, x * (elemA * elemZ) = (elemA * elemZ) * x := by
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hTY0 hx).2
    obtain ⟨h, hhS, hh1, hh2⟩ :=
      exists_mem_D hS.mem hSylY hT.k0.t₀_mem hcommT ht₀2 hT.k0.u_mem hT.k0.u_ord
        hT.k0.u_ne hT.c8 hgS hg
    exact ⟨rfl, hSyl, h, hhS, hh1, hh2⟩
  ·
    exfalso
    obtain ⟨p, hp⟩ := hT.fix
    have hpu : uElt 1 (g p) = g p := by
      have h := congrArg (fun σ : Equiv.Perm (Fin 1408) => σ (g p)) hg
      have h1 : (g * (elemA * elemZ) * g⁻¹) (g p) = g p := by
        simp [Equiv.Perm.mul_apply, hp]
      exact h.symm.trans h1
    exact hT.fpf (g p) hpu

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
