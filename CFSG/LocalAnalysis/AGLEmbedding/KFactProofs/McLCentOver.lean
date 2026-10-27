module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLCentOverSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal
public import Certificates.Certificate19900

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.MaxD2
open CFSG.RankThree.Native CFSG.Sporadic.Schreier Certificates.MaxD2Heis

@[expose] def CentOverLocal {X : Type*} [Group X] (R : Subgroup X) : Prop :=
  ∃ z ∈ R, z ≠ 1 ∧ R ≤ Subgroup.centralizer {z} ∧
    ∀ Y : Subgroup X, Subgroup.centralizer {z} ≤ Y →
      Y ≤ Subgroup.normalizer (R : Set X) ∨ Y = ⊤

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem CentOverLocal.map {R : Subgroup X} (e : X ≃* Y) (h : CentOverLocal R) :
    CentOverLocal (R.map e.toMonoidHom) := by
  obtain ⟨z, hz, hz1, hRz, hY⟩ := h
  refine ⟨e z, ⟨z, hz, rfl⟩, by simpa using hz1, ?_, fun W hW => ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 (hRz hr)
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]
  have hW' : Subgroup.centralizer {z} ≤ W.comap e.toMonoidHom := by
    intro g hg
    rw [Subgroup.mem_comap]
    apply hW
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hg]
  rcases hY _ hW' with h | h
  · left
    intro y hy
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨e.symm y, h (by simpa using hy), by simp⟩
  · right
    rw [eq_top_iff]
    intro y _
    have : e.symm y ∈ W.comap e.toMonoidHom := h ▸ Subgroup.mem_top _
    simpa using this

theorem centOverLocal_sylow [Finite X] [Finite Y] {p : ℕ} [Fact p.Prime] (e : X ≃* Y)
    {R₀ : Subgroup Y} (h : CentOverLocal R₀)
    (hsyl : Nat.card R₀ = p ^ (Nat.card Y).factorization p) (R : Sylow p X) :
    CentOverLocal (R : Subgroup X) := by
  have h1 := h.map e.symm
  have hcard : Nat.card (R₀.map e.symm.toMonoidHom) = p ^ (Nat.card X).factorization p := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hsyl, Nat.card_congr e.toEquiv]
  let R₁ : Sylow p X := Sylow.ofCard (R₀.map e.symm.toMonoidHom) hcard
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X R₁ R
  have hRc : (R : Subgroup X) = (R₀.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul]
    rfl
  rw [hRc]
  exact h1.map (MulAut.conj c)

end Transport

theorem mcl_cent_over_check :
    Certificates.MclCentOver.checkCentOver mclFiveDataP = true :=
  Certificates.certificate19900

theorem centOverLocal_mclP :
    ∃ R₀ : Subgroup (Equiv.Perm (Fin 275)), R₀ ≤ mcl275P ∧ Nat.card R₀ = 5 ^ 3 ∧
      CentOverLocal (R₀.subgroupOf mcl275P) := by
  obtain ⟨R, z, hz, hRG, hRc, hz1, hRz, hY⟩ := centOver_of_check (S := [mcl275A, mcl275B])
    (D := mclFiveDataP) rfl mclFiveDataP_hS
    (by
      have h1 : [mcl275A, mcl275B].length = 2 := rfl
      have h2 : mclFiveDataP.gT.size = 2 := rfl
      rw [h1, h2])
    (by rw [mclP_closure_eq]; exact card_mclP) mcl_five_check_P mcl_cent_over_check
  rw [mclP_closure_eq] at hRG hY
  refine ⟨R, hRG, hRc, ⟨z, hRG hz⟩, Subgroup.mem_subgroupOf.2 hz,
    fun h1 => hz1 (congrArg Subtype.val h1), fun r hr => ?_, fun W hW => ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.1 (hRz (Subgroup.mem_subgroupOf.1 hr)))
  have hCY : ∀ g ∈ mcl275P, g * z = z * g → g ∈ W.map mcl275P.subtype := fun g hg hgz =>
    ⟨⟨g, hg⟩, hW (Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hgz)), rfl⟩
  rcases hY _ (Subgroup.map_subtype_le W) hCY with h | h
  · left
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.1 (h ⟨w, hw, rfl⟩)) k.1
  · right
    rw [eq_top_iff]
    intro g _
    have hg : (g : Equiv.Perm (Fin 275)) ∈ W.map mcl275P.subtype := by rw [h]; exact g.2
    obtain ⟨w, hw, hwg⟩ := hg
    rwa [show w = g from Subtype.ext hwg] at hw

theorem centOverLocal_mcl
    {X : Type*} [Group X] [Finite X] (e : X ≃* mcl275P)
    (R : Sylow 5 X) : CentOverLocal (R : Subgroup X) := by
  obtain ⟨R₀, hR₀, hc, h⟩ := centOverLocal_mclP
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine centOverLocal_sylow e h ?_ R
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀).toEquiv, hc,
    factorization_card_mcl275P_five]

theorem centOverLocal_of_mulEquiv_mcl
    {K : Type*} [Group K] [Finite K]
    (e : K ≃* TauCeti.SporadicName.McL.Group) (T : Sylow 5 K) :
    CentOverLocal (T : Subgroup K) ∧ HeisLocal 5 (T : Subgroup K) := by
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  exact ⟨centOverLocal_mcl ((e.trans eC.symm).trans mcl275Equiv) T,
    heisLocal_mclP ((e.trans eC.symm).trans mcl275Equiv) T⟩

end CFSG.AGLEmbeddingD2
