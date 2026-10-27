module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallReeF2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS01Rest
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallReeMain

open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallAbs CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Red
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Open
open scoped Pointwise

section Transport

variable {S T : Type} [Group S] [Group T] [Finite S] (e : S ≃* T)

theorem congr_conj (g : S) : MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext t
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem congr_mem_inner_iff (f : MulAut S) :
    MulAut.congr e f ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner T ↔
      f ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨e.symm t, ?_⟩
    apply (MulAut.congr e).injective
    rw [congr_conj, e.apply_symm_apply]
    exact ht
  · rintro ⟨g, rfl⟩
    exact ⟨e g, (congr_conj e g).symm⟩

theorem map_inf_inner (E : Subgroup (MulAut S)) :
    E.map (MulAut.congr e).toMonoidHom ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner T =
      (E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S).map (MulAut.congr e).toMonoidHom := by
  ext t
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, ht⟩
    exact Subgroup.mem_map.2 ⟨s, ⟨hs, (congr_mem_inner_iff e s).1 ht⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hsi⟩, rfl⟩
    exact ⟨Subgroup.mem_map.2 ⟨s, hs, rfl⟩, (congr_mem_inner_iff e s).2 hsi⟩

theorem smallF2_transport (E : Subgroup (MulAut S))
    (h : SmallF2 T (E.map (MulAut.congr e).toMonoidHom)) : SmallF2 S E := by
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  intro W hW hWi hcent
  have hW' : IsPGroup 2 (W.map (MulAut.congr e).toMonoidHom) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hW
    apply IsPGroup.of_card (n := n)
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hn]
  have key : W.map (MulAut.congr e).toMonoidHom = ⊥ := by
    apply h _ hW'
    · intro t ht
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 ht
      exact (congr_mem_inner_iff e w).2 (hWi hw)
    · intro t ht
      obtain ⟨⟨s, hs, rfl⟩, ht2⟩ := Subgroup.mem_inf.1 ht
      have hsi := (congr_mem_inner_iff e s).1 ht2
      rw [Subgroup.mem_centralizer_iff]
      intro t' ht'
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 (SetLike.mem_coe.1 ht')
      have hc := Subgroup.mem_centralizer_iff.1 (hcent (Subgroup.mem_inf.2 ⟨hs, hsi⟩)) w hw
      show (MulAut.congr e) w * (MulAut.congr e) s = (MulAut.congr e) s * (MulAut.congr e) w
      rw [← map_mul, ← map_mul, hc]
  rw [eq_bot_iff]
  intro w hw
  have : (MulAut.congr e) w ∈ W.map (MulAut.congr e).toMonoidHom := Subgroup.mem_map.2 ⟨w, hw, rfl⟩
  rw [key, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact (MulAut.congr e).injective (by rw [this, map_one])

include e in
theorem kleinFour_transport (hK : KleinFour3 (CFSG.ComponentClassification.OuterAutomorphisms.inner T)) :
    KleinFour3 (CFSG.ComponentClassification.OuterAutomorphisms.inner S) := by
  intro g₁ g₂ k h₁ h₂ hs₁ hs₂ hn₁ hn₂ hne hc hkI hk3 hk1 hk2
  have := hK (MulAut.congr e g₁) (MulAut.congr e g₂) (MulAut.congr e k)
    ((congr_mem_inner_iff e _).2 h₁) ((congr_mem_inner_iff e _).2 h₂)
    (by rw [← map_pow, hs₁, map_one]) (by rw [← map_pow, hs₂, map_one])
    (fun h => hn₁ ((MulAut.congr e).injective (by rw [h, map_one])))
    (fun h => hn₂ ((MulAut.congr e).injective (by rw [h, map_one])))
    (fun h => hne ((MulAut.congr e).injective h))
    (by rw [← map_mul, ← map_mul, hc]) ((congr_mem_inner_iff e _).2 hkI)
    (by rw [← map_pow, hk3, map_one]) (by rw [← map_mul, ← map_mul, hk1])
    (by rw [← map_mul, ← map_mul, hk2])
  exact (MulAut.congr e).injective (by rw [this, map_one])

end Transport

section Cert


theorem smallF12_Ree : CFSG.LocalAnalysis.GLTheoremA.SmallF12At (.reeG2 1) := by
  intro S _ _ hv ⟨e⟩ E hE hEc hnot hE0
  have hK : Nat.card (GaloisField 3 3) = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge 1 hv (GaloisField 3 3) (by rw [hK])
  have hmodel : CFSG.Blueprint.ReeTitsModel S .twistedG2 3 3 :=
    ⟨⟨Nat.prime_three, by norm_num, rfl, rfl, by decide, le_rfl⟩, 1, by norm_num,
      GaloisField 3 3, inferInstance, inferInstance, hK, ⟨e.trans b.symm⟩⟩
  obtain ⟨eG⟩ := (CFSG.LieType.Ree.small_Ree_model_Schreier S 3 3 hmodel).2.2.2.2 1
    (GaloisField 3 3) (by norm_num) hK ⟨e.trans b.symm⟩
  have hK' : Nat.card (GaloisField 3 3) = 3 ^ (2 * 1 + 1) := hK
  have hEt : IsElemAbelian 3 (E.map (MulAut.congr eG).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  have hEtc : Nat.card (E.map (MulAut.congr eG).toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr eG).injective, hEc]
  have hnott : ¬ (E.map (MulAut.congr eG).toMonoidHom) ≤
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.LieType.Ree.ReeTag.G2.reeGamma (GaloisField 3 3) 1) := by
    intro h
    apply hnot
    intro x hx
    apply (congr_mem_inner_iff eG x).1
    exact h (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  have hE0t : Nat.card ↥((E.map (MulAut.congr eG).toMonoidHom) ⊓
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.LieType.Ree.ReeTag.G2.reeGamma (GaloisField 3 3) 1)) = 3 ^ 2 := by
    rw [map_inf_inner, Subgroup.card_map_of_injective (MulAut.congr eG).injective, hE0]
  have hF2Γ := KDRank3SmallReeF2.smallF2_gamma hK' (E.map (MulAut.congr eG).toMonoidHom) hEt hnott hE0t
  have hF2 := smallF2_transport eG E hF2Γ
  have hK4 := kleinFour_transport eG
    (KDRank3SmallReeBorel.kleinFour_inner (K := GaloisField 3 3) hK')
  exact ⟨hF2, smallF1_of_f2_klein S E hE hEc hE0 hF2 hK4⟩

end Cert

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallReeMain
