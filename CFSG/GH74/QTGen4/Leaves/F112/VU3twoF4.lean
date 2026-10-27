module

public import CFSG.GH74.QTGen4.U42.VertexGen4

public section

namespace CFSG.GH74.QTGen4.Leaves.F112

open CFSG.Open CFSG.Quasithin

theorem exists_injective_oTwoQuot_to_GL4 {G : Type} [Group G] [Finite G]
    (hG : CFSG.GH74.Gen4 G) {Li Lj S : Subgroup G} (h : CFSG.Quasithin.Hyp111At Li Lj S) :
    ∃ ψ : CFSG.Quasithin.oTwoQuot ↥Li →* GL (Fin 4) (ZMod 2), Function.Injective ψ := by
  let X : Subgroup G := Li ⊔ S ⊔ CFSG.Quasithin.borelOf Lj S
  have hLX : Li ≤ X := le_trans le_sup_left le_sup_left
  have hNX : X ≤ Subgroup.normalizer (Li : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer h.normalizes) h.borel_le
  have hXp : CFSG.IsCharacteristicP 2 ↥X :=
    CFSG.GH74.QTGen4.U42.VertexGen4.isCharP_of_charTwo h.charTwo
  have hXg : CFSG.GH74.Gen4 ↥X := CFSG.GH74.Gen4.subgroup X hG
  obtain ⟨ψX, hψX⟩ := CFSG.GH74.QTGen4.exists_injective_quotient_pCore_to_GL4 hXp hXg
  let f : ↥Li →* ↥X ⧸ CFSG.pCore 2 ↥X :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hLX)
  let φ : ↥Li →* GL (Fin 4) (ZMod 2) := ψX.comp f
  have hker : φ.ker ≤ CFSG.pCore 2 ↥Li := by
    intro g hg
    have h1 : f g = 1 := (injective_iff_map_eq_one ψX).mp hψX (f g) hg
    have h2 : Subgroup.inclusion hLX g ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).mp h1
    exact CFSG.GH74.QTGen4.U42.VertexGen4.comap_pCore_le hLX h2
  have hN : CFSG.pCore 2 ↥Li ≤ φ.ker := by
    intro n hn
    show ψX (f n) = 1
    have h1 : f n = 1 :=
      (QuotientGroup.eq_one_iff _).mpr
        (CFSG.GH74.QTGen4.U42.VertexGen4.pCore_map_le hLX hNX ⟨n, hn, rfl⟩)
    rw [h1, map_one]
  have hpc : CFSG.pCore 2 ↥Li = CFSG.Open.pCore 2 ↥Li := CFSG.pCore_eq_open ↥Li 2
  have hker' : φ.ker ≤ CFSG.Open.pCore 2 ↥Li := by rw [← hpc]; exact hker
  have hN' : CFSG.Open.pCore 2 ↥Li ≤ φ.ker := by rw [← hpc]; exact hN
  let ψ1 : CFSG.Quasithin.oTwoQuot ↥Li →* GL (Fin 4) (ZMod 2) := QuotientGroup.lift _ φ hN'
  have hinj : Function.Injective ψ1 := by
    refine (injective_iff_map_eq_one ψ1).mpr fun a ha => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    exact (QuotientGroup.eq_one_iff g).mpr (hker' ha)
  exact ⟨ψ1, hinj⟩

end CFSG.GH74.QTGen4.Leaves.F112
