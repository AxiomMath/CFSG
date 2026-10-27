module

public import CFSG.ClassicalInvolution.AschTight.S1911Case2b

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem exists_wSet_le_normal {K : Subgroup G} {z : G} (ht : S19R.TightStd p f K z)
    (S : Sylow 2 G) :
    ∃ W ∈ WSet (CoreAssembly.conjClass K), W ≤ (S : Subgroup G) ∧
      (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
  obtain ⟨η, hη, hinv⟩ := (l6_9_proved p f ht.branch.odd ht.branch.five G _
    (hypOmegaMod_of_tightD ht) S).1
  exact ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2,
    fun s hs => mem_normalizer_iff_conjSub_eq.mpr (conjSub_iSup_eq (hinv s hs))⟩

variable {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G}
  {V : Subgroup G}

theorem conj_t_eq_or_of_le_normalizer (hd : Sec19DataT p f K z S W L t V)
    (hSW : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G)) {s : G}
    (hsS : s ∈ (S : Subgroup G)) : s * t * s⁻¹ = t ∨ s * t * s⁻¹ = t * z := by
  have htW : s * t * s⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hSW hsS) t).mp (mem_W hd)
  have h2 : s * t * s⁻¹ * (s * t * s⁻¹) = 1 := by
    rw [show s * t * s⁻¹ * (s * t * s⁻¹) = s * (t * t) * s⁻¹ by group, hd.invL.sq]
    group
  have h3 : s * t * s⁻¹ ≠ 1 := fun h => hd.invL.ne_one (by
    calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
      _ = 1 := by rw [h]; group)
  rcases invol_mem_W hd htW h2 h3 with h | h | h
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

theorem inf_centralizer_t_le (h11b : C19_11bTmp p f) (hd : Sec19DataT p f K z S W L t V) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ({t} : Set G) ≤
      W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  rintro a ⟨⟨haS, haR⟩, hat⟩
  refine ⟨mem_W_of_comm_U h11b hd haS hat fun u hu => ?_, haR⟩
  exact (Subgroup.mem_centralizer_iff.mp haR u ⟨hd.hWS hu.2, hu.1⟩).symm

theorem isCyclic_inf_centralizer_t (h11b : C19_11bTmp p f) (hd : Sec19DataT p f K z S W L t V) :
    IsCyclic ↥((S : Subgroup G) ⊓
      Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ({t} : Set G)) := by
  have hcyc := isCyclic_inf_sec19Y hd
  rw [inf_sec19Y_eq hd.toSec19Data] at hcyc
  exact Subgroup.isCyclic_of_le (inf_centralizer_t_le h11b hd)

theorem inv_mul_mem_centralizer_t (hd : Sec19DataT p f K z S W L t V)
    (hSW : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G)) {x y : G}
    (hxS : x ∈ (S : Subgroup G)) (hyS : y ∈ (S : Subgroup G))
    (hx : x ∉ Subgroup.centralizer ({t} : Set G)) (hy : y ∉ Subgroup.centralizer ({t} : Set G)) :
    x⁻¹ * y ∈ Subgroup.centralizer ({t} : Set G) := by
  have hc : ∀ s ∈ (S : Subgroup G), s ∉ Subgroup.centralizer ({t} : Set G) →
      s * t * s⁻¹ = t * z := by
    intro s hs hst
    refine (conj_t_eq_or_of_le_normalizer hd hSW hs).resolve_left fun h => hst ?_
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

variable (p f) in
@[expose] def C19_E2PrimeTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      ∃ C : Subgroup G, IsCyclic ↥C ∧
        C ≤ (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ∧
        ∀ x ∈ (S : Subgroup G) ⊓
            Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G),
          ∀ y ∈ (S : Subgroup G) ⊓
              Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G),
            x ∉ C → y ∉ C → x⁻¹ * y ∈ C

variable (p f) in
theorem c19_E2PrimeTmp_of (h11b : C19_11bTmp p f) : C19_E2PrimeTmp p f := by
  intro G _ _ _ K z S W hd
  obtain ⟨W₀, hW₀, hW₀S, hSW₀⟩ := exists_wSet_le_normal hd.tight S
  have hd₀ : Sec19Data p f K z S W₀ := { hd with hW := hW₀, hWS := hW₀S }
  obtain ⟨L, t, V, hdT⟩ := exists_sec19DataT hd₀
  refine ⟨_, isCyclic_inf_centralizer_t h11b hdT, inf_le_left, fun x hx y hy hxC hyC => ?_⟩
  have hxt : x ∉ Subgroup.centralizer ({t} : Set G) := fun h => hxC ⟨hx, h⟩
  have hyt : y ∉ Subgroup.centralizer ({t} : Set G) := fun h => hyC ⟨hy, h⟩
  exact ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy,
    inv_mul_mem_centralizer_t hdT hSW₀ hx.1 hy.1 hxt hyt⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
