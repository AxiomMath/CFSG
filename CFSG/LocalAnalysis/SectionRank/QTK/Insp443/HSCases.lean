module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.AbelCentConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RefConfig
public import CFSG.Quasithin.Vol2.KGFactC31HS

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.HS

theorem KConfig.hs_cases
    {L V MK : Subgroup G₀} (h : KConfig G₀ L V MK) :
    ∃ σ : G₀ ≃* G₀,
      (V = (eSub basis_u16).map σ.toMonoidHom ∧ L = M16.map σ.toMonoidHom) ∨
      (V = (eSub basis_u8).map σ.toMonoidHom ∧ L = N8.map σ.toMonoidHom) := by
  have hne : ⁅V, L⁆ ≠ ⊥ := by rw [← h.eq_commutator]; exact h.ne_bot
  obtain ⟨p, hp, hp5, y, hy, ⟨k, hyk⟩, t, ht, hyt⟩ :=
    exists_pElement_not_comm h.perfect h.le_normalizer hne
  have ht2 : orderOf t = 2 := by
    apply orderOf_eq_prime
    · rw [sq]
      have := h.elemAbelian.2 t ht
      rwa [sq] at this
    · intro h1
      apply hyt
      rw [h1, mul_one, mul_inv_cancel]
  have hcommA : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t := fun j => by
    have hm : y ^ j * t * y⁻¹ ^ j ∈ V := by
      rw [inv_pow]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (h.le_normalizer hy) j) t).mp ht
    have := h.elemAbelian.1.is_comm.comm ⟨t, ht⟩ ⟨_, hm⟩
    simpa using congrArg Subtype.val this
  have hpd : p ∣ 44352000 := by
    by_contra hpd
    have h1 : y = 1 := eq_one_of_pow_of_not_dvd hp (by rwa [card_G₀]) ⟨k, hyk⟩
    apply hyt
    rw [h1, one_mul, inv_one, mul_one]
  rcases prime_dvd_hs hp hp5 hpd with rfl | rfl | rfl
  ·
    obtain ⟨s, hs, hU⟩ := orbSub_cases5 ⟨k, hyk⟩ ht2 hyt hcommA
    refine ⟨conjR s hs, Or.inl ?_⟩
    exact KConfig.eq_of_refData h (RefData.map_mulEquiv refData_u16 (conjR s hs)) hy ht hU
  ·
    obtain ⟨s, hs, hU⟩ := orbSub_cases7 ⟨k, hyk⟩ ht2 hyt hcommA
    set σ : G₀ ≃* G₀ := conjR s hs with hσ
    have hUσ : orbSub y t = (eSub basis_u8).map σ.toMonoidHom := by
      rw [hσ]
      exact hU
    have hcomp : σ.toMonoidHom.comp σ.symm.toMonoidHom = MonoidHom.id G₀ := by
      ext x
      simp
    have hcomp' : σ.symm.toMonoidHom.comp σ.toMonoidHom = MonoidHom.id G₀ := by
      ext x
      simp
    have h' : KConfig G₀ (L.map σ.symm.toMonoidHom) (V.map σ.symm.toMonoidHom)
        (MK.map σ.symm.toMonoidHom) := h.map_mulEquiv σ.symm
    have hy' : σ.symm y ∈ L.map σ.symm.toMonoidHom := Subgroup.mem_map_of_mem _ hy
    have ht' : σ.symm t ∈ V.map σ.symm.toMonoidHom := Subgroup.mem_map_of_mem _ ht
    have hU' : orbSub (σ.symm y) (σ.symm t) = eSub basis_u8 :=
      calc orbSub (σ.symm y) (σ.symm t)
          = (orbSub y t).map σ.symm.toMonoidHom := (orbSub_map σ.symm.toMonoidHom y t).symm
        _ = ((eSub basis_u8).map σ.toMonoidHom).map σ.symm.toMonoidHom := by rw [hUσ]
        _ = (eSub basis_u8).map (σ.symm.toMonoidHom.comp σ.toMonoidHom) := by
              rw [Subgroup.map_map]
        _ = eSub basis_u8 := by rw [hcomp', Subgroup.map_id]
    obtain ⟨hV', hL'⟩ :=
      KConfig.eq_of_abelCent h' (U := eSub basis_u8) (Q := Q8) (N := N8)
        cent_u8_eq (fun q hq hq2 => mem_u8_of_sq hq hq2) N8_eq.symm
        (fun X hX hNX hperf hXQ => N8_normal_eq X hX hNX hperf hXQ) hy' ht' hU'
    have hmap : ∀ H : Subgroup G₀, (H.map σ.symm.toMonoidHom).map σ.toMonoidHom = H := by
      intro H
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    refine ⟨σ, Or.inr ⟨?_, ?_⟩⟩
    · rw [← hmap V, hV']
    · rw [← hmap L, hL']
  ·
    exact (not_bad11 ⟨k, hyk⟩ ht2 hyt hcommA).elim

end CFSG.SectionRank.QTK.Insp443

end
