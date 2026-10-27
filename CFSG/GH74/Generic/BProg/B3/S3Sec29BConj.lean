module

public import CFSG.GH74.Generic.BProg.B3.S3Boot293

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.GH74.GLS.Stage1.Thm2
open scoped commutatorElement

namespace S3Sec29BConj

variable {G : Type} [Group G]

theorem obs52_map_conj [Finite G] {B : Subgroup G} {b b' g : G} {D J : Subgroup G}
    (hobs : Obs52 B b D J) (hg : g ∈ normalizer (B : Set G)) (hgb : g * b * g⁻¹ = b') :
    Obs52 B b' (D.map (MulAut.conj g).toMonoidHom) (J.map (MulAut.conj g).toMonoidHom) := by
  have hcjB : B.map (MulAut.conj g).toMonoidHom = B := Th2.cj_eq_of_mem_normalizer hg
  have hBg : ∀ u : G, u ∈ B ↔ g⁻¹ * u * g ∈ B := by
    intro u
    have := Th2.mem_cj_iff g B u
    rw [show Th2.cj g B = B from hcjB] at this
    exact this
  have hDle : IsE 2 B (D.map (MulAut.conj g).toMonoidHom) := by
    have h := Th2.isE_cj hobs.D_le g
    rwa [show Th2.cj g B = B from hcjB] at h
  have hmemD : ∀ d ∈ D.map (MulAut.conj g).toMonoidHom, g⁻¹ * d * g ∈ D := fun d hd =>
    (Th2.mem_cj_iff g D d).1 hd
  have hmemC : ∀ c : G, c ∈ centralizer ({b'} : Set G) ↔
      g⁻¹ * c * g ∈ centralizer ({b} : Set G) := by
    intro c
    rw [← hgb]
    have := Th2.mem_cj_iff g (centralizer ({b} : Set G)) c
    rw [Th2.cj_centralizer_singleton] at this
    exact this
  refine ⟨?_, ?_, hDle, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hgb, ← hobs.b_ord]
    exact MulEquiv.orderOf_eq (MulAut.conj g) b
  · intro z hz
    have hz' : g⁻¹ * z * g ∈ B := (hBg z).1 hz
    have hc := (Subgroup.mem_centralizer_iff.1 hobs.b_cent) (g⁻¹ * z * g) hz'
    rw [← hgb]
    calc z * (g * b * g⁻¹) = g * ((g⁻¹ * z * g) * b) * g⁻¹ := by group
      _ = g * (b * (g⁻¹ * z * g)) * g⁻¹ := by rw [hc]
      _ = g * b * g⁻¹ * z := by group
  · exact (Th2.pRank_cj g D).le.trans hobs.D_rank
  · have h := Recip.isPCompIn_map_conj hobs.comp g
    have e : (centralizer ({b} : Set G)).map (MulAut.conj g).toMonoidHom =
        centralizer ({b'} : Set G) := by
      rw [← hgb]
      exact Th2.cj_centralizer_singleton g b
    rwa [e] at h
  · intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    exact S3Boot293.mem_normalizer_map_conj (hobs.D_norm hd₀) g
  · intro d hd hne hmem
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    apply hobs.D_faith d₀ hd₀ (fun h => hne (by simp [h]))
    have h2 : g * d₀ * g⁻¹ ∈ cSec (J.map (MulAut.conj g).toMonoidHom) := hmem
    exact (S3Boot293.mem_cSec_map_conj_iff g d₀ J).1 h2
  · have hAGe : AG (D.map (MulAut.conj g).toMonoidHom) =
        (AG D).map (MulAut.conj g).toMonoidHom := Th2.AG_cj g D
    have hmemAG : ∀ c : G, c ∈ AG (D.map (MulAut.conj g).toMonoidHom) ↔
        g⁻¹ * c * g ∈ AG D := fun c => by
      rw [hAGe]
      exact Th2.mem_cj_iff g (AG D) c
    rcases hobs.unbal with ⟨hr, hnc⟩ | ⟨hr, c, hc, e, he, hce⟩
    · left
      refine ⟨(Th2.pRank_cj g D).trans hr, fun hsub => hnc fun c hc => ?_⟩
      have hc' : g * c * g⁻¹ ∈ AG (D.map (MulAut.conj g).toMonoidHom) ⊓
          centralizer ({b'} : Set G) := by
        refine ⟨(hmemAG _).2 ?_, (hmemC _).2 ?_⟩ <;>
          rw [show g⁻¹ * (g * c * g⁻¹) * g = c by group]
        · exact hc.1
        · exact hc.2
      exact (S3Boot293.mem_cSec_map_conj_iff g c J).1 (hsub hc')
    · right
      refine ⟨(Th2.pRank_cj g D).trans hr, g * c * g⁻¹, ?_, g * e * g⁻¹, ?_, ?_⟩
      · refine ⟨(hmemAG _).2 ?_, (hmemC _).2 ?_⟩ <;>
          rw [show g⁻¹ * (g * c * g⁻¹) * g = c by group]
        · exact hc.1
        · exact hc.2
      · exact (hBg _).2 (by rw [show g⁻¹ * (g * e * g⁻¹) * g = e by group]; exact he)
      · intro hmem
        apply hce
        rw [show ⁅g * c * g⁻¹, g * e * g⁻¹⁆ = g * ⁅c, e⁆ * g⁻¹ by
          simp only [commutatorElement_def]; group] at hmem
        exact (S3Boot293.mem_cSec_map_conj_iff g _ J).1 hmem

end S3Sec29BConj

end CFSG.GH74.Generic.BProg.B3
