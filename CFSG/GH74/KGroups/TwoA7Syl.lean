module

public import CFSG.GH74.KGroups.TwoA7Cover
public import CFSG.GH74.GLS.IVK.A7.Glue

public section

namespace CFSG.GH74.KGroups.TwoA7

open CFSG.ClassicalInvolution.Hat2A7 Equiv Equiv.Perm Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Stage1.Thm2.Recip

section Syl

variable {E : Type} [Group E] [Finite E] {π : E →* A7} {z : E}

omit [Finite E] in
theorem finite_mulAut (h : IsDoubleCoverA7 π z) : Finite (MulAut E) :=
  Finite.of_injective h.autPerm h.autPerm_injective

theorem card_sylow_mulAut
    (h : IsDoubleCoverA7 π z) (T : Sylow 2 (MulAut E)) :
    Nat.card ↥T = 16 := by
  have := finite_mulAut h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Sylow.card_eq_multiplicity T
  rw [Nat.card_congr (autPermEquiv h).toEquiv, CFSG.GH74.GLS.IVK.A7.factorization_S7] at h1
  rw [show Nat.card ↥T = Nat.card ↥(T : Subgroup (MulAut E)) from rfl, h1]
  norm_num

theorem conj5 (h : IsDoubleCoverA7 π z) (T : Sylow 2 (MulAut E)) :
    Nat.card ↥T = 16 ∧ (¬ ∃ n, IsDihedralTwoGroup ↥T n) ∧
      ∃ φ ∈ (T : Subgroup (MulAut E)), φ ∉ innOf E ∧ φ * φ = 1 := by
  have := finite_mulAut h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ε := autPermEquiv h with hε
  have hcard := card_sylow_mulAut h T
  set T' : Sylow 2 (Perm (Fin 7)) := Sylow.mapSurjective (f := ε.toMonoidHom) ε.surjective T
    with hT'def
  have hT' : (T' : Subgroup (Perm (Fin 7))) = (T : Subgroup (MulAut E)).map ε.toMonoidHom :=
    Sylow.coe_mapSurjective _ T
  obtain ⟨f, hsplit⟩ := ivk_1_1T T'
  obtain ⟨hf2, hfct, hfT, -, hcomm, hsup⟩ := hsplit
  have hfsq : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, pow_two] at this
  have hfodd : Perm.sign f = -1 := by
    obtain ⟨a, b, hab, rfl⟩ := Equiv.Perm.isSwap_iff_cycleType.mpr hfct
    exact Equiv.Perm.sign_swap hab
  have hfT' : ε.symm f ∈ (T : Subgroup (MulAut E)) := by
    have : f ∈ (T : Subgroup (MulAut E)).map ε.toMonoidHom := by rw [← hT']; exact hfT
    exact Subgroup.mem_map_equiv.1 this
  refine ⟨hcard, ?_, ε.symm f, hfT', ?_, ?_⟩
  ·
    rintro ⟨n, -, k, hk, hk2, ⟨e⟩⟩
    have hk0 : NeZero k := ⟨by omega⟩
    have hDcard : Nat.card (DihedralGroup k) = 2 * k := by
      rw [Nat.card_eq_fintype_card, DihedralGroup.card]
    have h8 : k = 8 := by
      have := Nat.card_congr e.toEquiv
      rw [hcard, hDcard] at this
      omega
    subst h8
    obtain ⟨k4, hk4, -, ⟨eP⟩⟩ := ivk_1_1a T'
    have hk4' : k4 = 4 := by omega
    subst hk4'
    set z0 : ↥((T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) :=
      eP.symm (DihedralGroup.r 2) with hz0
    have hz0c : ∀ y : ↥((T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)),
        z0 * y = y * z0 := by
      intro y
      apply eP.injective
      simp only [map_mul, hz0, MulEquiv.apply_symm_apply]
      have : ∀ d : DihedralGroup 4, DihedralGroup.r 2 * d = d * DihedralGroup.r 2 := by decide
      exact this _
    have hz0sq : z0 * z0 = 1 := by
      apply eP.injective
      simp only [map_mul, hz0, MulEquiv.apply_symm_apply, map_one]
      decide
    have hz0ne : z0 ≠ 1 := by
      intro h1
      have := congrArg eP h1
      simp only [hz0, MulEquiv.apply_symm_apply, map_one] at this
      exact absurd this (by decide)
    set zz : Perm (Fin 7) := (z0 : Perm (Fin 7)) with hzz
    have hzzT : zz ∈ (T' : Subgroup (Perm (Fin 7))) := z0.2.1
    have hzzA : zz ∈ alternatingGroup (Fin 7) := z0.2.2
    have hzz1 : zz ≠ 1 := fun h1 => hz0ne (Subtype.ext h1)
    have hzzf : zz ≠ f := by
      intro h1
      have := Equiv.Perm.mem_alternatingGroup.1 hzzA
      rw [h1, hfodd] at this
      exact absurd this (by decide)
    have hfne : f ≠ 1 := by
      intro h1
      rw [h1, map_one] at hfodd
      exact absurd hfodd (by decide)
    have hzzcomm : ∀ x ∈ (T' : Subgroup (Perm (Fin 7))), zz * x = x * zz := by
      intro x hx
      have hx' : x ∈ (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) ⊔
          Subgroup.zpowers f := by rw [hsup]; exact hx
      have hle : (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) ⊔ Subgroup.zpowers f ≤
          Subgroup.centralizer ({zz} : Set (Perm (Fin 7))) := by
        refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.2 ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have := hz0c ⟨y, hy⟩
          exact (congrArg Subtype.val this).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hcomm zz ⟨hzzT, hzzA⟩).symm
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx')).symm
    have hfcomm : ∀ x ∈ (T' : Subgroup (Perm (Fin 7))), f * x = x * f := by
      intro x hx
      have hx' : x ∈ (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) ⊔
          Subgroup.zpowers f := by rw [hsup]; exact hx
      have hle : (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) ⊔ Subgroup.zpowers f ≤
          Subgroup.centralizer ({f} : Set (Perm (Fin 7))) := by
        refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.2 ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact hcomm y hy
        · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx')).symm
    have hcentral : ∀ w : Perm (Fin 7), w ∈ (T' : Subgroup (Perm (Fin 7))) →
        (∀ x ∈ (T' : Subgroup (Perm (Fin 7))), w * x = x * w) →
        ∃ a : ↥T, (a : MulAut E) = ε.symm w ∧ ∀ t : ↥T, a * t = t * a := by
      intro w hw hwc
      have hwT : ε.symm w ∈ (T : Subgroup (MulAut E)) := by
        have : w ∈ (T : Subgroup (MulAut E)).map ε.toMonoidHom := by rw [← hT']; exact hw
        exact Subgroup.mem_map_equiv.1 this
      refine ⟨⟨ε.symm w, hwT⟩, rfl, fun t => ?_⟩
      apply Subtype.ext
      show ε.symm w * (t : MulAut E) = (t : MulAut E) * ε.symm w
      apply ε.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      have htT : ε (t : MulAut E) ∈ (T' : Subgroup (Perm (Fin 7))) := by
        rw [hT']; exact ⟨(t : MulAut E), t.2, rfl⟩
      exact hwc _ htT
    obtain ⟨a1, ha1, ha1c⟩ := hcentral f hfT (fun x hx => hfcomm x hx)
    obtain ⟨a2, ha2, ha2c⟩ := hcentral zz hzzT (fun x hx => hzzcomm x hx)
    have hcen : ∀ a : ↥T, (∀ t : ↥T, a * t = t * a) → a ≠ 1 → e a = DihedralGroup.r 4 := by
      intro a hac ha1
      have h1 : ∀ d : DihedralGroup 8, e a * d = d * e a := by
        intro d
        obtain ⟨t, rfl⟩ := e.surjective d
        rw [← map_mul, ← map_mul, hac]
      have h2 : ∀ x : DihedralGroup 8, (∀ d, x * d = d * x) → x = 1 ∨ x = DihedralGroup.r 4 := by
        decide
      rcases h2 _ h1 with h3 | h3
      · exact absurd (e.injective (h3.trans (map_one e).symm)) ha1
      · exact h3
    have ha1ne : a1 ≠ 1 := by
      intro h1
      have : (a1 : MulAut E) = 1 := congrArg Subtype.val h1
      rw [ha1] at this
      exact hfne (ε.symm.injective (this.trans (map_one ε.symm).symm))
    have ha2ne : a2 ≠ 1 := by
      intro h1
      have : (a2 : MulAut E) = 1 := congrArg Subtype.val h1
      rw [ha2] at this
      exact hzz1 (ε.symm.injective (this.trans (map_one ε.symm).symm))
    have heq : e a1 = e a2 := (hcen a1 ha1c ha1ne).trans (hcen a2 ha2c ha2ne).symm
    have : a1 = a2 := e.injective heq
    have h3 : ε.symm f = ε.symm zz := by
      rw [← ha1, ← ha2]
      exact congrArg Subtype.val this
    exact hzzf (ε.symm.injective h3).symm
  ·
    intro hin
    have : ε (ε.symm f) ∈ alternatingGroup (Fin 7) := by
      rw [← map_innOf h]
      exact ⟨ε.symm f, hin, rfl⟩
    rw [MulEquiv.apply_symm_apply, Equiv.Perm.mem_alternatingGroup, hfodd] at this
    exact absurd this (by decide)
  · apply ε.injective
    rw [map_mul, MulEquiv.apply_symm_apply, hfsq, map_one]

end Syl

end CFSG.GH74.KGroups.TwoA7
