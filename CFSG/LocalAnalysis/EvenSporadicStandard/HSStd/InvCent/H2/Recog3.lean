module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Recog1b
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Recog2

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

namespace H2Two

variable {G : Type*} [Group G] [Finite G] {t v : G} {J S₁ : Subgroup G}

theorem mem_normalizer (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    (hs : H2Two G t v J S₁) (φ : ↥S₁ ≃* alternatingGroup (Fin 5)) (g : G) :
    g ∈ normalizer (S₁ : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rcases hs.comps _ (isComponent_conj hs.comp₁ g) with h | h
  · exact h
  · exfalso
    have hMleC : (jOne t S₁).map (MulAut.conj g).toMonoidHom ≤
        centralizer ((⁅J, J⁆ : Subgroup G) : Set G) := by
      intro y hy
      rcases hy with ⟨j, hj, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [← h] at hb
      rcases hb with ⟨s, hsS, rfl⟩
      have hjs : j * s = s * j := by
        have hjC : j ∈ centralizer (S₁ : Set G) := (Subgroup.mem_inf.1 hj).2
        exact (Subgroup.mem_centralizer_iff.1 hjC s hsS).symm
      calc (MulAut.conj g) s * (MulAut.conj g) j
          = (MulAut.conj g) (s * j) := (map_mul (MulAut.conj g).toMonoidHom s j).symm
        _ = (MulAut.conj g) (j * s) := by rw [hjs]
        _ = (MulAut.conj g) j * (MulAut.conj g) s := map_mul (MulAut.conj g).toMonoidHom j s
    have hMleS : (jOne t S₁).map (MulAut.conj g).toMonoidHom ≤ S₁ :=
      hMleC.trans (centralizer_derived_le cfg hF hs φ)
    have hcard : Nat.card ↥((jOne t S₁).map (MulAut.conj g).toMonoidHom) = 120 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact card_jOne cfg hF hs φ
    have hle := Subgroup.card_le_of_le hMleS
    rw [hcard, card_of_equiv_alt5 φ] at hle
    exact absurd hle (by decide)

theorem exists_equiv (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    (hs : H2Two G t v J S₁) (φ : ↥S₁ ≃* alternatingGroup (Fin 5)) :
    Nonempty (G ≃* alternatingGroup (Fin 5) × Equiv.Perm (Fin 5)) := by
  have hcomm : ∀ a ∈ S₁, ∀ b ∈ jOne t S₁, a * b = b * a := by
    intro a ha b hb
    have hbC : b ∈ centralizer (S₁ : Set G) := (Subgroup.mem_inf.1 hb).2
    exact Subgroup.mem_centralizer_iff.1 hbC a ha
  have hdisj : S₁ ⊓ jOne t S₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxS : x ∈ S₁ := (Subgroup.mem_inf.1 hx).1
    have hxJ : x ∈ jOne t S₁ := (Subgroup.mem_inf.1 hx).2
    have hxC : x ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.1 hxJ).1
    have hxV : x ∈ kleinV t v := hs.inf_le (Subgroup.mem_inf.2 ⟨hxS, hxC⟩)
    have hxbot : x ∈ jOne t S₁ ⊓ kleinV t v := Subgroup.mem_inf.2 ⟨hxJ, hxV⟩
    rw [jOne_inf_kleinV cfg hF hs] at hxbot
    exact Subgroup.mem_bot.1 hxbot
  have htop : S₁ ⊔ jOne t S₁ = ⊤ := by
    apply le_antisymm le_top
    intro g _
    obtain ⟨s, hsS, j, hj, rfl⟩ :=
      mem_sup_of_mem_normalizer cfg hF hs φ (mem_normalizer cfg hF hs φ g)
    exact Subgroup.mul_mem_sup hsS hj
  obtain ⟨e⟩ := nonempty_mulEquiv_sup_prod (P := S₁) (Q := jOne t S₁) hcomm hdisj
  refine ⟨(Subgroup.topEquiv.symm).trans
    ((MulEquiv.subgroupCongr htop.symm).trans
      (e.trans (MulEquiv.prodCongr φ (jOne_equiv cfg hF hs φ).some)))⟩

end H2Two

end CFSG.EvenSporadicStandard.HSStd.InvCent
