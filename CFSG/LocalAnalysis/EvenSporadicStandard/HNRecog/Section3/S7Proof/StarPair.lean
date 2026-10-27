module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.StarTransp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.StarCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.StarCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.StarHom

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem s7_exists_hom {a z b c : G} (H : S7Hyps a z) (hb : b ∈ orb2A a a)
    (hc : c ∈ sSet a z b 2) :
    ∃ ρ : Sym 8 →* G, Function.Injective ρ ∧ (∀ τ : Sym 8, τ.IsSwap → IsConj a (ρ τ)) ∧
      ∀ s : Sym 8, s.cycleType = {2, 2} → IsConj a (ρ s) := by
  have hc' : c ∈ sBase a b ∧ (a * c) ^ 2 = b := by simpa [sSet] using hc
  have hca : IsConj a c := hc'.1.1
  have hc2 : c ^ 2 = 1 := s7_sq_of_isConj_a H hca
  let A : Subgroup G := derivedOf (Gxy a b)
  let S : Subgroup G := A ⊔ Subgroup.zpowers c
  obtain ⟨ψ⟩ := H.tableIV.self.s8_4B b hb c hc
  have hAS : A ≤ S := le_sup_left
  have hcS : c ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hA : Nat.card ↥A = 20160 := s7_card_derived H hb
  have hcA : c ∉ A := s7_not_mem_derived H hb hc
  have h720 : Nat.card ↥(A ⊓ Gx c) = 720 := s7_card_cent_derived H hb hc
  have htransp : (ψ ⟨c, hcS⟩).cycleType = {2} :=
    s7_sym8_transposition hAS ψ hA hcS hc2 hcA h720
  let ρ : Sym 8 →* G := S.subtype.comp ψ.symm.toMonoidHom
  have hρ_inj : Function.Injective ρ := by
    intro x y hxy
    have h1 : (ψ.symm x : ↥S) = ψ.symm y := Subtype.ext hxy
    exact ψ.symm.injective h1
  have hρσ : ρ (ψ ⟨c, hcS⟩) = c := by
    show ((ψ.symm (ψ ⟨c, hcS⟩) : ↥S) : G) = c
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨φ₀, hφ₀⟩ := s7_alt_equiv hAS ψ hA
  refine ⟨ρ, hρ_inj, ?_, ?_⟩
  · intro τ hτ
    have hτc : τ.cycleType = {2} := Equiv.Perm.isSwap_iff_cycleType.mp hτ
    have hconjτ : IsConj τ (ψ ⟨c, hcS⟩) :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [hτc, htransp])
    obtain ⟨k, hk⟩ := isConj_iff.mp hconjτ
    have hconjρ : IsConj (ρ τ) (ρ (ψ ⟨c, hcS⟩)) :=
      isConj_iff.mpr ⟨ρ k, by simpa only [map_mul, map_inv] using congrArg ρ hk⟩
    have hthis : IsConj a (ρ (ψ ⟨c, hcS⟩)) := by rw [hρσ]; exact hca
    exact hthis.trans hconjρ.symm
  · intro s hs2
    have hsalt : s ∈ alternatingGroup (Fin 8) := by
      have hbase : Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3 ∈ alternatingGroup (Fin 8) :=
        Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
          (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
          (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
      have hconj : IsConj (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3) s := by
        rw [Equiv.Perm.isConj_iff_cycleType_eq, hs2]
        exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup
          (by decide : ([0, 1, 2, 3] : List (Fin 8)).Nodup)
      obtain ⟨k, hk⟩ := isConj_iff.mp hconj
      have hmem : k * (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3) * k⁻¹ ∈
          alternatingGroup (Fin 8) :=
        (inferInstance : (alternatingGroup (Fin 8)).Normal).conj_mem
          (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3) hbase k
      rwa [hk] at hmem
    have hfig := H.pic.self.fig8a b hb φ₀ ⟨s, hsalt⟩ hs2
    have hρ_eq_φ : ρ s = ((φ₀ ⟨s, hsalt⟩ : ↥A) : G) := by
      rw [hφ₀ ⟨s, hsalt⟩]
      rfl
    rw [hρ_eq_φ]
    exact hfig.1

theorem s7_exists_pair {a z : G} (H : S7Hyps a z) :
    ∃ x d t : G, x ∈ orb3A a a ∧ d ∈ orb2A a a ∩ orb2A a x ∧ t ∈ orb2A a a ∩ orb2A a x ∧
      d ≠ t ∧ d * t = t * d := by
  obtain ⟨b, hb⟩ := (H.tableV.self.partition.orbit 0).nonempty
  have hb' : b ∈ orb2A a a := by simpa [tab5Set] using hb
  obtain ⟨c, hc⟩ := ((H.tableIV.self.partition b hb').orbit 2).nonempty
  have hc' : c ∈ sSet a z b 2 := by simpa using hc
  obtain ⟨ρ, hρ, hT, hP⟩ := s7_exists_hom H hb' hc'
  obtain ⟨a', x', d', t', ha', hx', hd', ht', had', hat', hxd', hxt', ho, hdt, hcomm⟩ :=
    s7_pair_of_hom ρ hρ hT hP
  exact s7_pair_conj ha' hx' hd' ht' had' hat' hxd' hxt' ho hdt hcomm

end CFSG.EvenSporadicStandard.HNRecog.Section3
