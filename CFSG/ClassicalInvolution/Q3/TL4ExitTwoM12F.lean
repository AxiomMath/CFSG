module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoM12E
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Disconnected.AschTight

theorem M12.transitive_of_conj_at {G : Type} [Group G] {Δ : Set (Subgroup G)}
    (hΩ : HypOmegaGen Δ) {t : G}
    (hF : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → ∃ g : G, g * z * g⁻¹ = t)
    (hU : ∀ K ∈ Δ, ∀ K' ∈ Δ, IsUniqueInvolution K t → IsUniqueInvolution K' t →
      ∃ c : G, conjSub c K = K') :
    ∀ J ∈ Δ, ∀ L ∈ Δ, ∃ g : G, conjSub g J = L := by
  intro J hJ L hL
  obtain ⟨⟨zJ, hzJ⟩, -⟩ := hΩ.omega1 J hJ
  obtain ⟨⟨zL, hzL⟩, -⟩ := hΩ.omega1 L hL
  obtain ⟨a, ha⟩ := hF J hJ zJ hzJ
  obtain ⟨b, hb⟩ := hF L hL zL hzL
  have h1 : IsUniqueInvolution (conjSub a J) t := by
    rw [← ha]
    exact hzJ.conj a
  have h2 : IsUniqueInvolution (conjSub b L) t := by
    rw [← hb]
    exact hzL.conj b
  obtain ⟨c, hc⟩ := hU _ (hΩ.conjInvariant a J hJ) _ (hΩ.conjInvariant b L hL) h1 h2
  refine ⟨b⁻¹ * c * a, ?_⟩
  rw [conjSub_mul, conjSub_mul, hc, conjSub_inv_conjSub]

theorem socleTransitive_m12 : SocleTransitive IsM12 := by
  intro G _ _ N _ _ _ hC hP Δ h hmem
  obtain ⟨e⟩ := hP
  let S : M12.Setting N Δ := ⟨e, hC, h, hmem⟩
  have hU : ∀ K ∈ Δ, ∀ K' ∈ Δ, IsUniqueInvolution K (S.e.symm M12.r1 : G) →
      IsUniqueInvolution K' (S.e.symm M12.r1 : G) → ∃ c : G, conjSub c K = K' := by
    intro K hK K' hK' hz hz'
    have hKN := S.le_of_rep hK hz
    have hK'N := S.le_of_rep hK' hz'
    obtain ⟨b, hb⟩ := S.corr_of_rep hK hz
    obtain ⟨b', hb'⟩ := S.corr_of_rep hK' hz'
    have heq : ∀ {b : Bool}, M12.Corr S.e K b → M12.Corr S.e K' b → ∃ c : G, conjSub c K = K' :=
      fun h₁ h₂ => ⟨1, by
        rw [conjSub_one]
        exact le_antisymm (M12.eq_of_corr _ hKN h₁ h₂) (M12.eq_of_corr _ hK'N h₂ h₁)⟩
    cases b <;> cases b'
    · exact heq hb hb'
    · exact S.conj_of_corr hK hK' hKN hb hb' hz hz'
    · obtain ⟨c, hc⟩ := S.conj_of_corr hK' hK hK'N hb' hb hz' hz
      exact ⟨c⁻¹, by rw [← hc, conjSub_inv_conjSub]⟩
    · exact heq hb hb'
  exact M12.transitive_of_conj_at h.hyp (fun K hK z hz => S.exists_conj_rep hK hz) hU

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
