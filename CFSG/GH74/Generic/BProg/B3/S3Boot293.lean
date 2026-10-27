module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.GH74.GLS.Stage1.Thm2
open scoped commutatorElement

section SD15

variable {G : Type} [Group G] [Finite G]

namespace S3Boot293

theorem exists_E_inf_le {x : G} {K A : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hsrc : IsSource2 x K A)
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∃ E : Subgroup G, E ≤ K ∧ A = E ⊔ zpowers x ∧ CFSG.IsElementaryAbelian 2 ↥E ∧
      Nat.card ↥E = 4 ∧ A ⊓ K ≤ E := by
  classical
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK h3
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4⟩ := S3Theta52.exists_E_of_src hsrc hZ
  have hxA : x ∈ A := hAE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hsrc.2.1
  have hx2 : x ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) x hxA
  have hx : orderOf x = 2 := orderOf_eq_prime hx2 fun h => hxE (h ▸ one_mem E)
  have hxK : x ∉ K := B1.PilotS5.not_mem_of_center_trivial hx hKC hZ
  have hExc : ∀ e ∈ E, ∀ z ∈ zpowers x, e * z = z * e := by
    intro e he z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_right (show Commute e x from
      Subgroup.mem_centralizer_singleton_iff.1 (hKC (hEK he))) n).eq
  refine ⟨E, hEK, hAE, hEel, hE4, fun y hy => ?_⟩
  obtain ⟨hyA, hyK⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨e, he, z, hz, hyez⟩ :=
    S3Theta52.exists_mul_of_mem_sup hExc (hAE ▸ hyA : y ∈ E ⊔ zpowers x)
  rcases B1.PilotS5.mem_zpowers_of_two hx hz with hz1 | hz1
  · rw [hz1, mul_one] at hyez
    exact hyez ▸ he
  · exfalso
    apply hxK
    have : x = e⁻¹ * y := by rw [hyez, hz1]; group
    rw [this]
    exact K.mul_mem (K.inv_mem (hEK he)) hyK

omit [Finite G] in
theorem nonempty_quot_map_conj (g : G) (J : Subgroup G) :
    Nonempty ((↥(J.map (MulAut.conj g).toMonoidHom) ⧸
      pPrimeCore 2 ↥(J.map (MulAut.conj g).toMonoidHom)) ≃* (↥J ⧸ pPrimeCore 2 ↥J)) := by
  let e : ↥J ≃* ↥(J.map (MulAut.conj g).toMonoidHom) := (MulAut.conj g).subgroupMap J
  exact ⟨(QuotientGroup.congr (pPrimeCore 2 ↥J)
    (pPrimeCore 2 ↥(J.map (MulAut.conj g).toMonoidHom)) e (pPrimeCore_map_iso 2 e)).symm⟩

omit [Finite G] in
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

theorem map_gammaK_le (g : G) (S : Subgroup G) (k : ℕ) :
    (gammaK 2 S k).map (MulAut.conj g).toMonoidHom ≤
      gammaK 2 (S.map (MulAut.conj g).toMonoidHom) k := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun Q hQS => iSup_le fun hk => ?_
  intro n hn
  have hQ' : Q.map (MulAut.conj g).toMonoidHom ≤ S.map (MulAut.conj g).toMonoidHom :=
    Subgroup.map_mono hQS
  have hrk : k ≤ pRank 2 ↥(Q.map (MulAut.conj g).toMonoidHom) := by
    have h := Th2.pRank_cj g Q
    exact h ▸ hk
  have hn' := mem_normalizer_map_conj hn g
  have hle : normalizer ((Q.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤
      gammaK 2 (S.map (MulAut.conj g).toMonoidHom) k :=
    le_iSup₂_of_le (Q.map (MulAut.conj g).toMonoidHom) hQ' (le_iSup_of_le hrk le_rfl)
  exact hle hn'

omit [Finite G] in
theorem mem_cSec_map_conj_iff (g z : G) (J : Subgroup G) :
    g * z * g⁻¹ ∈ cSec (J.map (MulAut.conj g).toMonoidHom) ↔ z ∈ cSec J := by
  constructor
  · intro h
    have h1 := Recip.mem_cSec_cj h g⁻¹
    have e : (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = J :=
      Th2.cj_cj_inv g J
    have h2 : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ ∈
        cSec ((J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom) := h1
    rwa [e, show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h2
  · intro h
    exact Recip.mem_cSec_cj h g

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
  have hmemD : ∀ d ∈ D₀.map (MulAut.conj g).toMonoidHom, g⁻¹ * d * g ∈ D₀ := fun d hd =>
    (Th2.mem_cj_iff g D₀ d).1 hd
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
    have h := mem_normalizer_map_conj (hobs.D_norm hd₀) g
    exact h
  · intro d hd hne hmem
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    apply hobs.D_faith d₀ hd₀ (fun h => hne (by simp [h]))
    have e : pPrimeCoreOf 2 (J₀.map (MulAut.conj g).toMonoidHom) =
        (pPrimeCoreOf 2 J₀).map (MulAut.conj g).toMonoidHom := Th2.pPrimeCoreOf_cj g J₀
    have h2 : g * d₀ * g⁻¹ ∈ cSec (J₀.map (MulAut.conj g).toMonoidHom) := hmem
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

end S3Boot293

end SD15

end CFSG.GH74.Generic.BProg.B3
