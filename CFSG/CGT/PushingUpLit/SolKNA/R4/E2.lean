module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.E11

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section End

variable {r : ℕ} {G : Type} [Group G] [Finite G]

variable {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem TightMemStdR.exists_wSet_le_normal (ht : TightMemStdR r K z) (S : Sylow 2 G) :
    ∃ W ∈ WSet (CoreAssembly.conjClass K), W ≤ (S : Subgroup G) ∧
      (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet ht.hypGen S
  exact ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2,
    fun s hs => mem_normalizer_iff_conjSub_eq.mpr (S1911.conjSub_iSup_eq (hinv s hs))⟩

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem conj_t_eq_or_of_le_normalizer (hSW : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G))
    {s : G} (hsS : s ∈ (S : Subgroup G)) : s * t * s⁻¹ = t ∨ s * t * s⁻¹ = t * z := by
  have htW : s * t * s⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hSW hsS) t).mp hd.mem_W
  have h2 : s * t * s⁻¹ * (s * t * s⁻¹) = 1 := by
    rw [show s * t * s⁻¹ * (s * t * s⁻¹) = s * (t * t) * s⁻¹ by group, hd.invL.sq]
    group
  have h3 : s * t * s⁻¹ ≠ 1 := fun h => hd.invL.ne_one (by
    calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
      _ = 1 := by rw [h]; group)
  rcases hd.invol_mem_W htW h2 h3 with h | h | h
  · exfalso
    have hsz : s * z * s⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hsS)]
      group
    apply hd.ne
    calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
      _ = s⁻¹ * (s * z * s⁻¹) * s := by rw [h, hsz]
      _ = z := by group
  · exact Or.inl h
  · exact Or.inr h

theorem inf_centralizer_t_le (hB : TightBPrimeBot K S W L) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ({t} : Set G) ≤
      W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  rintro a ⟨⟨haS, haR⟩, hat⟩
  refine ⟨hd.mem_W_of_comm_U hB haS hat fun u hu => ?_, haR⟩
  exact (Subgroup.mem_centralizer_iff.mp haR u ⟨hd.hWS hu.2, hu.1⟩).symm

theorem isCyclic_inf_centralizer_t (hB : TightBPrimeBot K S W L) :
    IsCyclic ↥((S : Subgroup G) ⊓
      Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ({t} : Set G)) := by
  have hcyc := hd.isCyclic_inf_sec19Y
  rw [hd.toTightSylowDataR.inf_sec19Y_eq] at hcyc
  exact Subgroup.isCyclic_of_le (hd.inf_centralizer_t_le hB)

theorem inv_mul_mem_centralizer_t (hSW : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G))
    {x y : G} (hxS : x ∈ (S : Subgroup G)) (hyS : y ∈ (S : Subgroup G))
    (hx : x ∉ Subgroup.centralizer ({t} : Set G)) (hy : y ∉ Subgroup.centralizer ({t} : Set G)) :
    x⁻¹ * y ∈ Subgroup.centralizer ({t} : Set G) := by
  have hc : ∀ s ∈ (S : Subgroup G), s ∉ Subgroup.centralizer ({t} : Set G) →
      s * t * s⁻¹ = t * z := by
    intro s hs hst
    refine (hd.conj_t_eq_or_of_le_normalizer hSW hs).resolve_left fun h => hst ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc s * t = s * t * s⁻¹ * s := by group
      _ = t * s := by rw [h]
  have hxt := hc x hxS hx
  have hyt := hc y hyS hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e : x⁻¹ * y * t * (x⁻¹ * y)⁻¹ = t := by
    calc x⁻¹ * y * t * (x⁻¹ * y)⁻¹ = x⁻¹ * (y * t * y⁻¹) * x := by group
      _ = x⁻¹ * (x * t * x⁻¹) * x := by rw [hyt, hxt]
      _ = t := by group
  calc x⁻¹ * y * t = x⁻¹ * y * t * (x⁻¹ * y)⁻¹ * (x⁻¹ * y) := by group
    _ = t * (x⁻¹ * y) := by rw [e]

end TightSylowDataTR


theorem TightSylowDataR.tightE2Prime (hd : TightSylowDataR r K z S W)
    (hcore : ∀ (W₀ L : Subgroup G) (t : G) (V : Subgroup G),
      TightSylowDataTR r K z S W₀ L t V → TightBPrimeBot K S W₀ L) : TightE2Prime K S := by
  obtain ⟨W₀, hW₀, hW₀S, hSW₀⟩ := hd.tight.exists_wSet_le_normal S
  have hd₀ : TightSylowDataR r K z S W₀ := { hd with hW := hW₀, hWS := hW₀S }
  obtain ⟨L, t, V, hdT⟩ := hd₀.exists_dataT
  refine ⟨_, hdT.isCyclic_inf_centralizer_t (hcore W₀ L t V hdT), inf_le_left,
    fun x hx y hy hxC hyC => ?_⟩
  have hxt : x ∉ Subgroup.centralizer ({t} : Set G) := fun h => hxC ⟨hx, h⟩
  have hyt : y ∉ Subgroup.centralizer ({t} : Set G) := fun h => hyC ⟨hy, h⟩
  exact ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy,
    hdT.inv_mul_mem_centralizer_t hSW₀ hx.1 hy.1 hxt hyt⟩

end End

end CFSG.CGT.PushingUpLit.SolKNA.R4
