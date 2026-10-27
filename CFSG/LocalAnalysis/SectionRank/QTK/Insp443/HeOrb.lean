module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig
public import CFSG.Quasithin.Vol2.KGFactC31He

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He
  CFSG.Sporadic.HeldB
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Quasithin.KGC31.Native
  _root_.Certificates

variable {A : Type} [Group A] [Finite A] {L V MK : Subgroup A}
  {ι : A →* Equiv.Perm (Fin 8330)}

theorem KConfig.he_ref
    (h : KConfig A L V MK) (hι : CFSG.Quasithin.KGC31.He.Emb ⊤ ι) :
    ∃ ι' : A →* Equiv.Perm (Fin 8330), CFSG.Quasithin.KGC31.He.Emb ⊤ ι' ∧
      ∃ y ∈ L, ∃ p k : ℕ, p.Prime ∧ 5 ≤ p ∧ y ^ p ^ k = 1 ∧ y ≠ 1 ∧
        ((∀ i, vW5 i ∈ V.map ι') ∨ (∀ i, vW7 i ∈ V.map ι')) := by
  have hne : ⁅V, L⁆ ≠ ⊥ := by rw [← h.eq_commutator]; exact h.ne_bot
  obtain ⟨p, hp, hp5, y, hy, ⟨k, hyk⟩, t, ht, hyt⟩ :=
    exists_pElement_not_comm h.perfect h.le_normalizer hne
  have hy1 : y ≠ 1 := fun h1 => hyt (by rw [h1, one_mul, inv_one, mul_one])
  have hcommA : ∀ j : ℕ, t * (y ^ j * t * (y ^ j)⁻¹) = y ^ j * t * (y ^ j)⁻¹ * t := fun j => by
    have hm : y ^ j * t * (y ^ j)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (h.le_normalizer hy) j) t).mp ht
    have := h.elemAbelian.1.is_comm.comm ⟨t, ht⟩ ⟨_, hm⟩
    simpa using congrArg Subtype.val this
  have ht2 : orderOf t = 2 := by
    apply orderOf_eq_prime
    · rw [sq]
      have := h.elemAbelian.2 t ht
      rwa [sq] at this
    · intro h1
      apply hyt
      rw [h1, mul_one, mul_inv_cancel]
  have hyP : ι y ∈ heP := hι.mem_heP (Subgroup.mem_top y)
  have htP : ι t ∈ heP := hι.mem_heP (Subgroup.mem_top t)
  have hy1' : ι y ≠ 1 := fun h1 => hy1 (hι.inj (by rw [h1, map_one]))
  have he : ∃ e ∈ [25, 343, 17], (ι y) ^ e = 1 := by
    have hyk' : (⟨ι y, hyP⟩ : ↥heP) ^ p ^ k = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← map_pow, hyk, map_one, Subgroup.coe_one])
    obtain ⟨e, hes, hye⟩ := exists_pow_eq_one card_heP hp hp5 hyk'
      (fun h1 => hy1' (congrArg Subtype.val h1))
    exact ⟨e, hes, by simpa using congrArg Subtype.val hye⟩
  have hmove : ι y * ι t * (ι y)⁻¹ ≠ ι t := fun h1 => hyt (hι.inj (by
    rw [map_mul, map_mul, map_inv, h1]))
  have hcommP : ∀ j : ℕ, ι t * ((ι y) ^ j * ι t * ((ι y) ^ j)⁻¹) =
      (ι y) ^ j * ι t * ((ι y) ^ j)⁻¹ * ι t := fun j => by
    simp only [← map_pow, ← map_inv, ← map_mul, hcommA j]
  obtain ⟨d, hd, m, hm⟩ := exists_ref_le_orbSub htP
    (by rw [orderOf_injective ι hι.inj]; exact ht2) hyP hmove he hcommP
  have hι' := hι.conj (heAutGroup.inv_mem hd)
  have hU : ∀ bw ∈ refW m, elt bw ∈ V.map ((MulAut.conj d⁻¹).toMonoidHom.comp ι) := by
    intro bw hbw
    have hx := hm bw hbw
    rw [← orbSub_map] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    refine ⟨z, orbSub_le (h.le_normalizer hy) ht hz, ?_⟩
    rw [MonoidHom.comp_apply, hzx]
    show d⁻¹ * (d * elt bw * d⁻¹) * d⁻¹⁻¹ = elt bw
    group
  refine ⟨(MulAut.conj d⁻¹).toMonoidHom.comp ι, hι', y, hy, p, k, hp, hp5, hyk, hy1, ?_⟩
  by_cases hm0 : m = 0
  · subst hm0
    left
    intro i
    show elt (w5W.getD i []) ∈ V.map ((MulAut.conj d⁻¹).toMonoidHom.comp ι)
    exact hU _ (by
      rw [refW, ite_eq_left rfl, List.getD_eq_getElem _ _ (by rw [len_w5W]; exact i.2)]
      exact List.getElem_mem _)
  · right
    intro i
    show elt (w7W.getD i []) ∈ V.map ((MulAut.conj d⁻¹).toMonoidHom.comp ι)
    exact hU _ (by
      rw [refW, ite_eq_right hm0, List.getD_eq_getElem _ _ (by rw [len_w7W]; exact i.2)]
      exact List.getElem_mem _)

end CFSG.SectionRank.QTK.Insp443

end
