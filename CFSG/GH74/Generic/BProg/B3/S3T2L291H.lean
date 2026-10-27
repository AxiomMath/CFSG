module

public import CFSG.GH74.Generic.BProg.B3.S3T2L291E
public import CFSG.GH74.Generic.BProg.B3.S3T2L291G
public import CFSG.GH74.Generic.BProg.B3.S3Rk1Four
public import CFSG.GH74.Generic.BProg.B3.S3Boot292

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem lemma291_of_prop101 (h101 : Prop10_1Stmt) : Lemma291 G := by
  intro x a K A D J hB2 hc h3 y₁ hy₁ hy₁1
  have hx : orderOf x = 2 := hc.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK h3
  obtain ⟨E, hEK, hAE, -, hEel, hE4⟩ := S3Theta52.exists_E_of_src hc.src hZ
  have hxK : x ∉ K := B1.PilotS5.not_mem_of_center_trivial hx hK.1 hZ
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hEx : ∀ h ∈ E, h * x = x * h := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.1 (hK.1 (hEK hh))
  have hy₁E : y₁ ∈ E := by
    obtain ⟨hyA, hyK⟩ := Subgroup.mem_inf.1 hy₁
    rw [hAE] at hyA
    obtain ⟨e, he, rfl | rfl⟩ := S3Sec29H.mem_sup_zpowers hx2 hEx hyA
    · exact he
    · exact (hxK (by simpa using K.mul_mem (K.inv_mem (hEK he)) hyK)).elim
  obtain ⟨F, _, _, hY⟩ := S3T2L291.exists_split3 hK h3
  refine ⟨S3T2L291.Lbar x y₁ K,
    S3T2L291.isAdmPair_Lbar hx hK hxK hY hEK hAE hEel hE4 hy₁E hy₁1, fun hss => hc.notAllow ?_⟩
  have hall : ∀ e ∈ E, e ≠ 1 → NbhdSemisimple x e (S3T2L291.Lbar x e K) := by
    intro e he he1
    obtain ⟨g, hg, rfl⟩ := S3Rk1Four.exists_cyc h3 hEK hEel hE4 hy₁E he hy₁1 he1
    rw [S3T2L291.Lbar_cmap hK.1 (Subgroup.mem_inf.1 hg).1 (hK.1 (hEK hy₁E))]
    exact S3T2L291.nbhdSemisimple_cmap (hK.1 (Subgroup.mem_inf.1 hg).1) hss
  intro y Lb hadm
  obtain ⟨E₀, Ib, ⟨hE₀A, -, -⟩, hna | hsa⟩ := hadm.adm
  · exact S3T2L291.nbhdSemisimple_of_nonsolvAdm hB2 hc.hyp hx hK hY hEK hAE hEel hE₀A hna hall
  · exact S3T2L291.nbhdSemisimple_of_solvAdm h101 hc.hyp hx hK hY hEK hAE hEel hE₀A hsa hall

end CFSG.GH74.Generic.BProg.B3
