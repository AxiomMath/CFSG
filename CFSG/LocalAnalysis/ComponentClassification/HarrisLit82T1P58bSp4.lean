module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bCov
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClSp

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank Blueprint CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped MatrixGroups


open P58b

theorem noConfig_PSp_two : Harris82Lemma58bNoConfig .PSp 2 := by
  intro X _ _ hX hO p f hp hp2 hm k c t Q hcfg
  have hc2 : orderOf c = 2 := hcfg.1
  have hcZ : c ∈ center X := hcfg.2.1
  have htZ : t ∉ center X := hcfg.2.2.2.1
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [hcfg.2.2.1, pow_two] at h
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  rcases hm with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨-, F, _, _, hFc, ⟨θ⟩⟩ := hcl
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  set β : StatedSp 2 F →* X ⧸ center X := θ.symm.toMonoidHom.comp (SymplecticFlag.proj 2 F)
    with hβ
  refine false_of_cover hX hO hp hp2 hcfg (G := StatedSp 2 F)
    (fun E _ _ π hπ hker h2 => ?_) β (θ.symm.surjective.comp (QuotientGroup.mk'_surjective _)) ?_
  · obtain ⟨s, hs, -⟩ :=
      CFSG.LieType.Steinberg.odd_symplectic_central_two_extension_splitting hF 2 hπ hker h2
    exact ⟨s, hs⟩
  intro α hαs hαβ hker g hg
  have hβ1 : ∀ z, β z = 1 → z = 1 ∨ z = Burgoyne.Sp.lrInv F 0 * Burgoyne.Sp.lrInv F 1 := by
    intro z hz
    rw [hβ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at hz
    exact Burgoyne.B.eq_one_or_eq_lrInv_mul_of_scalar ((QuotientGroup.eq_one_iff z).mp hz)
  have hcm : α (Burgoyne.Sp.lrInv F 0 * Burgoyne.Sp.lrInv F 1) ≠ 1 := by
    have hc : c ∈ β.ker.map α := hker ▸ hcZ
    obtain ⟨y, hy, hyc⟩ := hc
    rcases hβ1 y hy with rfl | rfl
    · rw [map_one] at hyc
      exact absurd hyc.symm hc1
    · rw [hyc]
      exact hc1
  have hinj : ∀ z, α z = 1 → z = 1 := by
    intro z hz
    rcases hβ1 z (by rw [← hαβ, hz, map_one]) with h | h
    · exact h
    · exact (hcm (by rw [← h]; exact hz)).elim
  have hgg : g * g = 1 := hinj _ (by rw [map_mul, hg, ht2])
  have hns : ∀ c' : Fˣ,
      ((⟨(g : GL (Fin 2 ⊕ Fin 2) F), statedSp_le_gsp g.2⟩ : gsp 2 F) : GL (Fin 2 ⊕ Fin 2) F) ≠
      GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c' := by
    intro c' hc'
    apply htZ
    rw [hker]
    refine ⟨g, MonoidHom.mem_ker.mpr ?_, hg⟩
    rw [hβ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact (QuotientGroup.eq_one_iff g).mpr (mem_subgroupOf.mpr ⟨c', hc'.symm⟩)
  have hAA : ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((1 : F) ^ 2) • 1 := by
    have h := congrArg
      (fun x : StatedSp 2 F => ((x : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hgg
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] at h
    rw [one_pow, one_smul]
    exact h
  have hJ : ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
      formJ 2 F * ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((1 : F) ^ 2) • formJ 2 F := by
    rw [one_pow, one_smul]
    exact SymplecticTorusWeyl.mem_statedSp_iff.1 g.2
  have hNo := Burgoyne.Cl.noL2At_sp_split hF
    (Ag := ⟨(g : GL (Fin 2 ⊕ Fin 2) F), statedSp_le_gsp g.2⟩) one_ne_zero hAA hJ hns
  rw [conjAut_statedSp] at hNo
  refine Burgoyne.Cl.NoL2At.of_congr θ ?_
  have e : MulAut.congr θ (MulAut.conj (β g)) = MulAut.conj (SymplecticFlag.proj 2 F g) :=
    mulAut_congr_conj θ (SymplecticFlag.proj 2 F g)
  rw [e]
  exact hNo

end CFSG.ComponentClassification.HarrisLit.T1
