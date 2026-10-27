module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128WrDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128WrSD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128WrD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128WrV
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128WrCompat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128WrAlg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128WrK

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

theorem sec128_wreath_recognition {G : Type} [Group G] [Finite G] (V : Subgroup G)
    (hV : IsElemAb2 V 8)
    (hC : centralizer (V : Set G) = V ⊔ oddCoreIn (normalizer (V : Set G)))
    (hWr : Sec128WrAct V (autIn (normalizer (V : Set G)) V))
    {K : Subgroup G} (hKN : K ≤ normalizer (V : Set G))
    (hKO : oddCoreIn (normalizer (V : Set G)) ≤ K) (hKV : K ⊓ V = ⊥)
    (hKsup : K ⊔ V = normalizer (V : Set G))
    {D : Subgroup G}
    (hD : ∃ (B X0 : Subgroup G) (φ₀ : (Fin 5 → ZMod 2) → G), B ≤ D ∧ X0 ≤ D ∧ X0 ⊓ B = ⊥ ∧
      Nonempty (↥X0 ≃* ↥(alternatingGroup (Fin 5))) ∧
      IsPermModuleVia IsEvenVec φ₀ B D (alternatingGroup (Fin 5)) ∧
      centralizer (B : Set G) ⊓ D = B) :
    QuotEquivTo (normalizer (V : Set G)) (oddCoreIn (normalizer (V : Set G))) (WrZ2 ↥D) := by
  classical
  obtain ⟨B, X0, φ₀, hBD, hXD, hXB, hX, hP, hCB⟩ := hD
  obtain ⟨e, φ, Vq, hcoord, hsup, hinf, hact⟩ := hWr
  obtain ⟨χ, hχinj, hχX, hχact, hDdec⟩ := sec128_D_side hXD hXB hX hP hCB
  obtain ⟨ι, hιinj, hιform, hιblock, hιrange⟩ :=
    sec128_V_coord_hom hV.1 hBD hP hcoord hsup hinf
  have hgen := sec128_V_gen hcoord hsup
  have hcompat := sec128_compat hχact hgen hιblock e hact
  obtain ⟨κ₀, hκ₀act, hκ₀surj⟩ := sec128_K_side hV.1 hKN hKsup
  let κ : ↥K →* WrZ2 ↥D := (sec128WrMap χ).comp (e.symm.toMonoidHom.comp κ₀)
  have hκ_apply : ∀ k : ↥K, κ k = sec128WrMap χ (e.symm (κ₀ k)) := by
    intro k; rfl
  have hcomp : ∀ (k : ↥K) (h h' : ↥V), (h' : G) = (k : G) * (h : G) * (k : G)⁻¹ →
      ι h' = κ k * ι h * (κ k)⁻¹ := by
    intro k h h' hh'
    have hactk : ((e (e.symm (κ₀ k)) : ↥(autIn (normalizer (V : Set G)) V)) :
        MulAut ↥V) h = h' := by
      refine Subtype.ext ?_
      rw [MulEquiv.apply_symm_apply]
      exact (hκ₀act k h).trans hh'.symm
    have h1 := hcompat (e.symm (κ₀ k)) h
    rw [hactk, ← hκ_apply k] at h1
    exact h1
  obtain ⟨ψ, hψV, hψK⟩ :=
    sec128_internal_semidirect_hom (H := V) (K := K) (M := normalizer (V : Set G))
      hKN (by rw [inf_comm]; exact hKV) (by rw [sup_comm]; exact hKsup) ι κ hcomp
  refine ⟨ψ, ?_, ?_⟩
  ·
    intro w
    obtain ⟨v, γ, hvγ⟩ := sec128_wr_surj hBD hDdec hιrange w
    obtain ⟨k, hk⟩ := hκ₀surj (e γ)
    refine ⟨⟨(v : G), V.le_normalizer v.2⟩ * ⟨(k : G), hKN k.2⟩, ?_⟩
    have hκk : κ k = sec128WrMap χ γ := by
      rw [hκ_apply k, hk, MulEquiv.symm_apply_apply]
    rw [map_mul, hψV v (V.le_normalizer v.2), hψK k (hKN k.2), hκk, hvγ]
  ·
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hψn
      have hnN : (n : G) ∈ V ⊔ K := by rw [sup_comm, hKsup]; exact n.2
      have hmem : (n : G) ∈ (V : Set G) * (K : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left V K hKN]
        exact hnN
      obtain ⟨v, hv, k, hk, hvk⟩ := Set.mem_mul.mp hmem
      have hn_eq : n = (⟨v, V.le_normalizer hv⟩ : ↥(normalizer (V : Set G))) *
          ⟨k, hKN hk⟩ := by
        refine Subtype.ext ?_
        simp only [Subgroup.coe_mul]
        exact hvk.symm
      have hψnk : ψ n = ι ⟨v, hv⟩ * κ ⟨k, hk⟩ := by
        rw [hn_eq, map_mul, hψV ⟨v, hv⟩ (V.le_normalizer hv), hψK ⟨k, hk⟩ (hKN hk)]
      have h1 : ι ⟨v, hv⟩ * κ ⟨k, hk⟩ = 1 := by rw [← hψnk]; exact hψn
      let γ : WrZ2 ↥(alternatingGroup (Fin 5)) := e.symm (κ₀ ⟨k, hk⟩)
      have hγdef : γ = e.symm (κ₀ ⟨k, hk⟩) := rfl
      have hκk : κ ⟨k, hk⟩ = sec128WrMap χ γ := by
        rw [hκ_apply ⟨k, hk⟩]
      have h1' : ι ⟨v, hv⟩ * sec128WrMap χ γ = 1 := by rw [← hκk]; exact h1
      obtain ⟨hv1, hγ1⟩ := sec128_wr_triv hXB hχinj hχX hιinj hιform ⟨v, hv⟩ γ h1'
      have hv1' : (v : G) = 1 := by
        simpa using congrArg (fun x : ↥V => (x : G)) hv1
      have he1 : e.symm (κ₀ ⟨k, hk⟩) = 1 := hγdef.symm.trans hγ1
      have hκ0k : κ₀ ⟨k, hk⟩ = 1 := by
        have happ := MulEquiv.apply_symm_apply e (κ₀ ⟨k, hk⟩)
        rw [he1, map_one] at happ
        exact happ.symm
      have hcent : ∀ u : ↥V, (k : G) * (u : G) * (k : G)⁻¹ = (u : G) := by
        intro u
        have h := hκ₀act ⟨k, hk⟩ u
        have hco : (((κ₀ ⟨k, hk⟩ : ↥(autIn (normalizer (V : Set G)) V)) :
            MulAut ↥V) u : ↥V) = u := by rw [hκ0k]; rfl
        rw [hco] at h
        exact h.symm
      have hkO : (k : G) ∈ oddCoreIn (normalizer (V : Set G)) :=
        sec128_K_ker hC hKO hKV hk hcent
      have hnk' : (n : G) = (k : G) := by rw [← hvk, hv1', one_mul]
      rw [hnk']; exact hkO
    · intro hnO
      have hkK : (n : G) ∈ K := hKO hnO
      have hψnk : ψ n = κ ⟨(n : G), hkK⟩ :=
        hψK ⟨(n : G), hkK⟩ n.2
      have hκ0k : κ₀ ⟨(n : G), hkK⟩ = 1 := by
        refine Subtype.ext ?_
        ext u
        have h := hκ₀act ⟨(n : G), hkK⟩ u
        rw [sec128_O_cent hC hnO u] at h
        simpa using h
      have hκk : κ ⟨(n : G), hkK⟩ = 1 := by
        rw [hκ_apply ⟨(n : G), hkK⟩, hκ0k]; simp
      rw [hψnk, hκk]

end CFSG.OddStandard.SmallF3.Omega
