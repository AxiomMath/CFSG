module

public import CFSG.GH74.Uniqueness.SU.SU13TA9N
public import CFSG.GH74.Uniqueness.SU.SU13TA9D
public import CFSG.GH74.Uniqueness.SU.SU13TA9Elts9
public import CFSG.GH74.Uniqueness.SU.SU13TA9E
public import CFSG.GH74.Uniqueness.SU.SU13TA9EBasic

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU13
  CFSG.GH74.Uniqueness.SU.SU4

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 9)}

theorem NHE_eq {E : Subgroup H} {z : H} (hz : ∀ g : H, g * z = z * g) :
    NHE E z = normalizer (E : Set H) := by
  have hzz : centralizer ({z} : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hz g)
  unfold NHE
  rw [hzz, inf_top_eq]

theorem exists_epart9 [Finite H] (hπ : TwoCover π) (c : Cfg π) {E : Subgroup H} (hE : IsE π E)
    {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) (f : FPart z (c.elts hπ hz hz1)) (hf : f.F = Fh π) :
    ∃ ep : EPart9 z (c.elts hπ hz hz1) (c.elts9 hπ hz hz1) f, ep.E = E := by
  have hzc : ∀ g : H, g * z = z * g := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz)
  obtain ⟨Es, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := exists_Es hπ c hz hz1 hE.1 hE.2
  obtain ⟨r, hr⟩ := hπ.surj er
  refine ⟨⟨E, Es, DE π E, IsE.S2h π, r, hE.s₁_mem hπ c, hE.s₂_mem hπ c, hE.s₄_mem hπ c,
    fun g hg => hE.exists_gen hπ c hg, h3, h4, fun a ha => hE.pow_three hπ ha, h2, h5, h6, h7,
    h8, h9, h10, fun a ha => hE.t_conj_mem hπ c ha, fun a ha => hE.x_conj_mem hπ c ha, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  ·
    intro N hN hnorm hodd
    rw [NHE_eq hzc] at hN hnorm
    exact hE.noOdd hπ hN hnorm hodd
  ·
    intro P hPE hs₁ hinv
    rw [NHE_eq hzc] at hinv
    exact hE.irred hπ c hPE hs₁ hinv
  ·
    intro u hu hord huz
    rw [NHE_eq hzc] at hu ⊢
    exact hE.invClass hπ c hz hz1 hu hord huz
  ·
    rw [NHE_eq hzc]
    exact hE.isSylowIn_S2h hπ
  · exact IsE.z_mem_S2h hz
  · intro y hy hord hc
    exact IsE.S2h_cen hπ hz hz1 hy hord hc
  ·
    rw [hf]
    exact DE_le_Fh
  · exact DE_le_E
  · exact hE.card_DE hπ
  · intro g hg
    exact hE.exists_eq_zpow_mul_DE hπ c hg
  · rw [hf]
    exact r_mem_Fh hr
  · exact orderOf_r hπ hr hz hz1
  · exact pow_four_r hπ hr hz hz1
  · intro d hd
    exact r_conj_mem_DE hπ hE hr hd
  · intro d hd
    exact t_conj_mem_DE hπ c hE hd
  · exact t_r_mem_zpowers hπ c hr hz hz1
  · exact t_r_ne c hr

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
