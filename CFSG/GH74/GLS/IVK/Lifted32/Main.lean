module

public import CFSG.GH74.GLS.IVK.Lifted32.ZW
public import CFSG.GH74.GLS.IVK.Lifted32.HypCtr
public import CFSG.GH74.GLS.IVK.Prod32.Out

public section

namespace CFSG.GH74.GLS.IVK.Lifted32

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {a x : G}

theorem l53Data_of_absData (hII : II4_4_4_center) (h2A7 : IVK.Lifted.II4_2A7)
    (hctr : Ctr5 G z S K₁ K₂ a x) (h52 : L52 S K₁ K₂) (haC : a ∈ Cen z)
    (hnotK : toBar z ⟨a, haC⟩ ∉ barOf z K₁ ⊔ barOf z K₂)
    {Y A : Subgroup (CentralizerBar z)} {r : ℕ} (hD : AbsData z S K₁ K₂ a haC Y A r) :
    L53Data z S K₁ K₂ a (pull z S Y) (pull z S A) := by
  have hlat := l53Lat_of_absData hII h2A7 hctr h52 haC hnotK hD
  obtain ⟨hc1, hc2, hc3⟩ := l53_classes hII h2A7 hctr h52 haC hD
  exact
    { Y_le := hlat.Y_le
      A_le := hlat.A_le
      prod := hlat.prod
      inter := hlat.inter
      Y_normal := hlat.Y_normal
      Y_index := hlat.Y_index
      a_mem := hlat.a_mem
      A_cyclic := hlat.A_cyclic
      A_order := hlat.A_order
      YA_comm := hlat.YA_comm
      S_nonab := hlat.S_nonab
      field := hlat.field
      two_classes := hc1
      fused := hc2
      a_az := hc3
      swap := hlat.swap
      a_not_K := hlat.a_not_K
      ZW := l53_ZW hII h2A7 hctr h52 haC hD }

end Main

theorem ivk_3_2_lifted_of_abstract (hII : II4_4_4_center)
    (h44 : CFSG.GH74.GLS.Stage1.Thm2.Recip.II4_44) (h2A7 : IVK.Lifted.II4_2A7)
    (hA : IVK_3_2_abstract) : IVK_3_2_lifted := by
  intro G _ _ z S K₁ K₂ a x hctr h52
  have haC : a ∈ Cen z := elt5_mem_Cen hII hctr.cfg hctr.elt
  have hyp := hyp_of_ctr5 hII h44 h2A7 hctr haC
  obtain ⟨hP₁, hP₂⟩ := sylow_P_of_L52 hII hctr h52
  obtain ⟨hCa, hrest⟩ :=
    hA (CentralizerBar z) (barOf z K₁) (barOf z K₂) (zBar z) (barOf z S) (toBar z ⟨a, haC⟩) hyp
  obtain ⟨Y, A, r, hYle, hAle, hprod, hinter, hCb, hCc, hCd, hCe, hCf, hCg, hCh, hCi, hCj⟩ :=
    hrest hP₁ hP₂
  have hD : AbsData z S K₁ K₂ a haC Y A r :=
    ⟨hCa, hYle, hAle, hprod, hinter, hCb, hCc, hCd, hCe, hCf, hCg, hCh, hCi, hCj⟩
  have hnotK : toBar z ⟨a, haC⟩ ∉ barOf z K₁ ⊔ barOf z K₂ := hyp.a_not_mem_K
  exact ⟨pull z S Y, pull z S A, l53Data_of_absData hII h2A7 hctr h52 haC hnotK hD⟩

end CFSG.GH74.GLS.IVK.Lifted32
