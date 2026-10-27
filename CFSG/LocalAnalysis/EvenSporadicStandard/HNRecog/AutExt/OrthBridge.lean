module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthCoord
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthLabel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthKer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthPi
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthTheta

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm Section3

variable {G : Type} [Group G]

theorem orthCoord_of_orbits [Finite G] {K M : Subgroup G} (hMK : M ≤ K) (hM : IsElemTwo 4 M)
    {S : Fin 2 → Set G} (hS : IsOrbitPartition K {x | x ∈ M ∧ x ≠ 1} S)
    (h0 : Nat.card ↥(S 0) = 5) (h1 : Nat.card ↥(S 1) = 10)
    {ψ : ↥K →* alternatingGroup (Fin 5)} (hsurj : Function.Surjective ψ)
    (hker : ∀ l : ↥K, ψ l = 1 ↔ (l : G) ∈ M) :
    ∃ (ρ : ↥K →* Perm (Fin 5)) (θ : G → Fv5), OrthCoord K M ρ θ := by
  have hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hM.1.1.is_comm.comm (⟨x, hx⟩ : M) ⟨y, hy⟩)
  have hsq : ∀ x ∈ M, x * x = 1 := fun x hx => by rw [← pow_two]; exact hM.1.2 x hx
  have hM16 : Nat.card ↥M = 16 := by rw [hM.2]; norm_num
  have hnorm : ∀ l : ↥K, ∀ x ∈ M, (l : G) * x * (l : G)⁻¹ ∈ M := by
    intro l x hx
    have hxK : x ∈ K := hMK hx
    have h1 : ψ ⟨x, hxK⟩ = 1 := (hker ⟨x, hxK⟩).mpr hx
    have h2 : ψ (l * ⟨x, hxK⟩ * l⁻¹) = 1 := by
      rw [map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
    exact (hker _).mp h2
  obtain ⟨s, ρ, hsinj, hsS, hsS', hρ⟩ := exists_label (hS.orbit 0).conj_mem h0
  have hsM : ∀ i, s i ∈ M := fun i => (hS.subset 0 (hsS i)).1
  have hMρ : ∀ l : ↥K, (l : G) ∈ M → ρ l = 1 := by
    intro l hl
    refine Equiv.Perm.ext fun i => hsinj ?_
    rw [← hρ l i, hcomm _ hl _ (hsM i), mul_assoc, mul_inv_cancel, mul_one]
    rfl
  have hnt : ∃ l : ↥K, ρ l ≠ 1 := by
    have hne : s 0 ≠ s 1 := fun h => absurd (hsinj h) (by decide)
    obtain ⟨k, hk, hk'⟩ := (hS.orbit 0).transitive (s 0) (hsS 0) (s 1) (hsS 1)
    refine ⟨⟨k, hk⟩, fun h => hne ?_⟩
    have h2 := hρ ⟨k, hk⟩ 0
    rw [h] at h2
    rw [← hk']
    exact h2.symm
  have hker' : ∀ l : ↥K, ρ l = 1 ↔ (l : G) ∈ M :=
    fun l => ⟨ker_le_of_simple hsurj hker ρ hMρ hnt l, hMρ l⟩
  obtain ⟨hsign, hsurj'⟩ := even_surj_of_ker ρ ψ hsurj fun l => (hker' l).trans (hker l).symm
  obtain ⟨π, hπM, hπadd, hπs, hπconj⟩ := exists_pi hcomm hsq hnorm hsM hρ
  have hπone := pi_one_vec hS h0 h1 hπM hπconj
  have hπsurj := pi_surj hM hS h0 h1 hsS' hπM hπadd hπs hπconj
  obtain ⟨θ, hmul, heven, hinj, hex, hconj⟩ :=
    exists_orthTheta hM16 hπM hπadd hπone (fun x hx => hπsurj x hx) hπconj
  exact ⟨ρ, θ, ⟨hMK, hsign, hsurj', hker', hmul, heven, hinj, hex, hconj⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
