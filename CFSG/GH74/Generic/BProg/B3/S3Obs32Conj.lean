module

public import CFSG.GH74.Generic.BProg.B3.S3Prop29

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.GH74.GLS.Stage1.Thm2
open scoped commutatorElement

namespace S3Obs32Conj

variable {G : Type} [Group G]

theorem mem_cSec_map_conj_iff [Finite G] (g z : G) (J : Subgroup G) :
    g * z * g⁻¹ ∈ Recip.cSec (J.map (MulAut.conj g).toMonoidHom) ↔ z ∈ Recip.cSec J := by
  constructor
  · intro h
    have h1 := Recip.mem_cSec_cj h g⁻¹
    have e : (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = J :=
      Th2.cj_cj_inv g J
    have h2 : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ ∈
        Recip.cSec ((J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom) := h1
    rwa [e, show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h2
  · intro h
    exact Recip.mem_cSec_cj h g

theorem mem_normalizer_map_conj {Q : Subgroup G} {n : G} (hn : n ∈ normalizer (Q : Set G))
    (g : G) :
    g * n * g⁻¹ ∈ normalizer ((Q.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : ∀ w : G, w ∈ Q.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * w * g ∈ Q :=
    fun w => Th2.mem_cj_iff g Q w
  rw [h1, h1]
  have h2 := Subgroup.mem_normalizer_iff.1 hn (g⁻¹ * x * g)
  rw [show g⁻¹ * (g * n * g⁻¹ * x * (g * n * g⁻¹)⁻¹) * g = n * (g⁻¹ * x * g) * n⁻¹ by group]
  exact h2

variable [Finite G]

theorem obs32_map_conj {A : Subgroup G} {a₀ y g : G} {D₀ J₀ : Subgroup G}
    (hobs : Obs32 A a₀ D₀ J₀) (hg : g ∈ normalizer (A : Set G)) (hga : g * a₀ * g⁻¹ = y)
    (hy : orderOf y = 2) (hyA : y ∈ A) (hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) :
    Obs32 A y (D₀.map (MulAut.conj g).toMonoidHom) (J₀.map (MulAut.conj g).toMonoidHom) := by
  have hcjA : A.map (MulAut.conj g).toMonoidHom = A := Th2.cj_eq_of_mem_normalizer hg
  have hAg : ∀ u : G, u ∈ A ↔ g⁻¹ * u * g ∈ A := by
    intro u
    have := Th2.mem_cj_iff g A u
    rw [show Th2.cj g A = A from hcjA] at this
    exact this
  have hDle : IsE 1 A (D₀.map (MulAut.conj g).toMonoidHom) := by
    have h := Th2.isE_cj hobs.D_le g
    rwa [show Th2.cj g A = A from hcjA] at h
  refine ⟨hy, fun u hu => hAc u hu y hyA, hDle, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Th2.pRank_cj g D₀).le.trans hobs.D_rank
  · have h := Recip.isPCompIn_map_conj hobs.comp g
    have e : (centralizer ({a₀} : Set G)).map (MulAut.conj g).toMonoidHom =
        centralizer ({y} : Set G) := by
      rw [← hga]
      exact Th2.cj_centralizer_singleton g a₀
    rwa [e] at h
  · intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    exact mem_normalizer_map_conj (hobs.D_norm hd₀) g
  · intro d hd hne hmem
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    apply hobs.D_faith d₀ hd₀ (fun h => hne (by simp [h]))
    have h2 : g * d₀ * g⁻¹ ∈ Recip.cSec (J₀.map (MulAut.conj g).toMonoidHom) := hmem
    exact (mem_cSec_map_conj_iff g d₀ J₀).1 h2
  · have hAGe : AG (D₀.map (MulAut.conj g).toMonoidHom) =
        (AG D₀).map (MulAut.conj g).toMonoidHom := Th2.AG_cj g D₀
    have hmemAG : ∀ c : G, c ∈ AG (D₀.map (MulAut.conj g).toMonoidHom) ↔
        g⁻¹ * c * g ∈ AG D₀ := fun c => by
      rw [hAGe]
      exact Th2.mem_cj_iff g (AG D₀) c
    have hmemC : ∀ c : G, c ∈ centralizer ({y} : Set G) ↔
        g⁻¹ * c * g ∈ centralizer ({a₀} : Set G) := by
      intro c
      rw [← hga]
      have := Th2.mem_cj_iff g (centralizer ({a₀} : Set G)) c
      rw [Th2.cj_centralizer_singleton] at this
      exact this
    rcases hobs.unbal with ⟨hr, hnc⟩ | ⟨hr, c, hc, b, hb, hcb⟩
    · left
      refine ⟨(Th2.pRank_cj g D₀).trans hr, fun hsub => hnc fun c hc => ?_⟩
      have hc' : g * c * g⁻¹ ∈ AG (D₀.map (MulAut.conj g).toMonoidHom) ⊓
          centralizer ({y} : Set G) := by
        refine ⟨(hmemAG _).2 ?_, (hmemC _).2 ?_⟩ <;>
          rw [show g⁻¹ * (g * c * g⁻¹) * g = c by group]
        · exact hc.1
        · exact hc.2
      exact (mem_cSec_map_conj_iff g c J₀).1 (hsub hc')
    · right
      refine ⟨(Th2.pRank_cj g D₀).trans hr, g * c * g⁻¹, ?_, g * b * g⁻¹, ?_, ?_⟩
      · refine ⟨(hmemAG _).2 ?_, (hmemC _).2 ?_⟩ <;>
          rw [show g⁻¹ * (g * c * g⁻¹) * g = c by group]
        · exact hc.1
        · exact hc.2
      · exact (hAg _).2 (by rw [show g⁻¹ * (g * b * g⁻¹) * g = b by group]; exact hb)
      · intro hmem
        apply hcb
        rw [show ⁅g * c * g⁻¹, g * b * g⁻¹⁆ = g * ⁅c, b⁆ * g⁻¹ by
          simp only [commutatorElement_def]; group] at hmem
        exact (mem_cSec_map_conj_iff g _ J₀).1 hmem

end S3Obs32Conj

theorem s3_a_ne_conj_x {G : Type} [Group G] [Finite G] {x a : G} {K A D J : Subgroup G}
    (hc : Ctx21 G x K A a D J) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) {g : G}
    (hg : g ∈ normalizer (A : Set G)) : a ≠ g * x * g⁻¹ := by
  intro hax
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4, hxK⟩ := S3Rk1Basic.exists_E hc.circ hc.src h3
  have hx2 : orderOf x = 2 := S3Rk1Basic.orderOf_x_of_circ hc.circ
  have hxA : x ∈ A := hAE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u :=
    (CFSG.GH74.GLS.C3.Layer1.Back.forall_of_isElementaryAbelian hc.src.2.1).1
  have hga : g⁻¹ * a * g⁻¹⁻¹ = x := by rw [hax]; group
  have hobs := S3Obs32Conj.obs32_map_conj hc.obs ((normalizer (A : Set G)).inv_mem hg) hga hx2 hxA hAc
  exact s3_a_ne_x (a := x) ⟨hc.hyp, hc.noAlt, hc.circ, hc.src, hc.notAllow, hc.theta, hc.notBal, hxA, hobs⟩
    h3 rfl

end CFSG.GH74.Generic.BProg.B3
