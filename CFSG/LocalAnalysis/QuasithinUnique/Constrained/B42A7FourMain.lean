module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A7FourDef
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A7FourFam
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57R4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7B
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7Base

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open Equiv

namespace B42A57

theorem altConj_of_typeA {B : Subgroup (Perm (Fin 7))} (hc4 : Nat.card B = 4) {a b c' d : Fin 7}
    (hnd : [a, b, c', d].Nodup) (h1 : swap a b * swap c' d ∈ B) (h2 : swap a c' * swap b d ∈ B)
    (h3 : swap a d * swap b c' ∈ B) :
    ∃ c ∈ alternatingGroup (Fin 7), B = kleinRegular7.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨σ, hσ⟩ := exists_perm_list [0, 1, 2, 3] [a, b, c', d] (by decide) hnd rfl
  have s0 : σ 0 = a := hσ 0 (by simp)
  have s1 : σ 1 = b := hσ 1 (by simp)
  have s2 : σ 2 = c' := hσ 2 (by simp)
  have s3 : σ 3 = d := hσ 3 (by simp)
  obtain ⟨c, hc, hcx, hcy⟩ : ∃ c ∈ alternatingGroup (Fin 7),
      c * (swap 0 1 * swap 2 3) * c⁻¹ ∈ B ∧ c * (swap 0 2 * swap 1 3) * c⁻¹ ∈ B := by
    by_cases hev : σ ∈ alternatingGroup (Fin 7)
    · refine ⟨σ, hev, ?_, ?_⟩
      · rw [conj_swap_mul_swap, s0, s1, s2, s3]
        exact h1
      · rw [conj_swap_mul_swap, s0, s2, s1, s3]
        exact h2
    · refine ⟨σ * swap 0 1, ?_, ?_, ?_⟩
      · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
          sign_eq_neg_one_of_not_mem hev, Equiv.Perm.sign_swap (by decide)]
        decide
      · have e1 : swap (0 : Fin 7) 1 * (swap 0 1 * swap 2 3) * (swap 0 1)⁻¹ = swap 0 1 * swap 2 3 := by
          decide +kernel
        have e2 : (σ * swap 0 1) * (swap 0 1 * swap 2 3) * (σ * swap 0 1)⁻¹ =
            σ * (swap 0 1 * (swap 0 1 * swap 2 3) * (swap 0 1)⁻¹) * σ⁻¹ := by group
        rw [e2, e1, conj_swap_mul_swap, s0, s1, s2, s3]
        exact h1
      · have e1 : swap (0 : Fin 7) 1 * (swap 0 2 * swap 1 3) * (swap 0 1)⁻¹ = swap 0 3 * swap 1 2 := by
          decide +kernel
        have e2 : (σ * swap 0 1) * (swap 0 2 * swap 1 3) * (σ * swap 0 1)⁻¹ =
            σ * (swap 0 1 * (swap 0 2 * swap 1 3) * (swap 0 1)⁻¹) * σ⁻¹ := by group
        rw [e2, e1, conj_swap_mul_swap, s0, s1, s2, s3]
        exact h3
  refine ⟨c, hc, ?_⟩
  have hle : kleinRegular7.map (MulAut.conj c).toMonoidHom ≤ B := by
    rintro _ ⟨k, hk, rfl⟩
    have : kleinRegular7 ≤ B.comap (MulAut.conj c).toMonoidHom := by
      unfold kleinRegular7
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hcx
      · exact hcy
    exact this hk
  have hcard : Nat.card (kleinRegular7.map (MulAut.conj c).toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact card_V0
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hc4])).symm

theorem asB42A7Four_holds : AsB42A7Four := by
  intro S _ _ hS G L A C hirr hA hcard π
  unfold AltConjTo
  have hS2 : ∀ s : S, s * s = 1 := fun s => by simpa [pow_two] using hS s
  have hS16 : Nat.card S = 16 := by rw [hcard]; norm_num
  have hL2520 : Nat.card ↥L = 2520 := by
    rw [C.card_eq]
    exact L246.C123.card_A7
  have hnorm := L246.C123.normalizer_eq_of_card_2520 hS hS16 hL2520
  have hGL : G = L := by
    refine le_antisymm (fun g hg => ?_) C.le_G
    have hg' : g ∈ Subgroup.normalizer (L : Set (MulAut S)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro l
      refine ⟨fun hl => C.normal g hg l hl, fun hl => ?_⟩
      have := C.normal g⁻¹ (G.inv_mem hg) _ hl
      simpa [mul_assoc] using this
    rw [hnorm] at hg'
    exact hg'
  let ι : ↥L ≃* alternatingGroup (Fin 7) := π.symm
  let e : ↥G →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp
    (π.symm.toMonoidHom.comp (Subgroup.inclusion hGL.le))
  have hinj : Function.Injective e :=
    Subtype.val_injective.comp (π.symm.injective.comp (Subgroup.inclusion_injective hGL.le))
  have hL : ∀ l : ↥L, e ⟨(l : MulAut S), C.le_G l.2⟩ = (ι l : Perm (Fin 7)) := fun l => rfl
  obtain ⟨h1, hc, h2, hcardB⟩ := offender_image hA e hinj
  have hBA : (A.subgroupOf G).map e ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨g, -, rfl⟩
    exact (π.symm (Subgroup.inclusion hGL.le g)).2
  have hPB : ((A.subgroupOf L).comap π.toMonoidHom).map (alternatingGroup (Fin 7)).subtype =
      (A.subgroupOf G).map e := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyA : ((π y : ↥L) : MulAut S) ∈ A := Subgroup.mem_subgroupOf.1 hy
      refine ⟨⟨((π y : ↥L) : MulAut S), C.le_G (π y).2⟩, Subgroup.mem_subgroupOf.2 hyA, ?_⟩
      show ((π.symm (Subgroup.inclusion hGL.le ⟨((π y : ↥L) : MulAut S), C.le_G (π y).2⟩) :
        alternatingGroup (Fin 7)) : Perm (Fin 7)) = y
      have : Subgroup.inclusion hGL.le ⟨((π y : ↥L) : MulAut S), C.le_G (π y).2⟩ = π y :=
        Subtype.ext rfl
      rw [this, MulEquiv.symm_apply_apply]
    · rintro ⟨g, hg, rfl⟩
      have hgA : (g : MulAut S) ∈ A := Subgroup.mem_subgroupOf.1 hg
      refine ⟨π.symm (Subgroup.inclusion hGL.le g), ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      show π (π.symm (Subgroup.inclusion hGL.le g)) ∈ A.subgroupOf L
      rw [MulEquiv.apply_symm_apply]
      exact Subgroup.mem_subgroupOf.2 hgA
  rcases classify7A h1 hBA hc h2 with ⟨hc2, r, f, hf, hr, hcl⟩ | hres
  · exfalso
    have hAcard : Nat.card A = 2 := by rw [← hcardB]; exact hc2
    have := card_le_of_cert C hirr hA ι e hinj hL f hf (N := 2 ^ 3)
      (by rw [hAcard]; exact Nat.pow_le_pow_right (by norm_num) hr) hcl
    rw [hS16] at this
    norm_num at this
  · rcases hres with ⟨hc4, a, b, c', d, hnd, h1', h2', h3'⟩ |
      ⟨hc4, a, b, c', d, e', f, hnd, h1', h2', h3'⟩
    · obtain ⟨c, hc', hB⟩ := altConj_of_typeA hc4 hnd h1' h2' h3'
      exact ⟨c, hc', by rw [hPB]; exact hB⟩
    · exfalso
      exact typeB_false C hirr hA ι e hinj hL hcard (by rw [← hcardB]; exact hc4)
        ⟨a, b, c', d, e', f, hnd, h1', h2', h3'⟩

end B42A57

end CFSG.QuasithinUnique
