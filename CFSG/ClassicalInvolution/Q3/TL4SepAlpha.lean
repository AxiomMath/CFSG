module

import CFSG.ClassicalInvolution.Asc77.AscAlphaBotEng
public import CFSG.ClassicalInvolution.Q3.TL4SepFam

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_of_alphaOf_eq_bot_sep {A : Subgroup G} (hA : alphaOf A = ⊥) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {x y : G} (hx : x ∈ oddCoreOf (Subgroup.centralizer ({a} : Set G)))
    (hy : y ∈ A) : x * y = y * x :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExact.commute_of_alpha_bot_gen hA ha ha1 hx hy

omit [Finite G] in
theorem mem_closure_pair_left (z u : G) : z ∈ Subgroup.closure ({z, u} : Set G) :=
  Subgroup.subset_closure (Set.mem_insert z {u})

omit [Finite G] in
theorem mem_closure_pair_right (z u : G) : u ∈ Subgroup.closure ({z, u} : Set G) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem z rfl)

variable {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem TightSepAlpha.at_conj (hd : TightDatum R S t) (hα : TightSepAlpha R t) (g : G)
    {J : Subgroup G}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (conjSub g (tightCore R)))
    {u : G} (hu : IsUniqueInvolution J u) :
    alphaOf (Subgroup.closure ({g * t * g⁻¹, u} : Set G)) = ⊥ := by
  have hJ' := Asc77.omegaNbr_conj hd.hypOmegaGen.conjInvariant hJ g⁻¹
  rw [conjSub_inv_conjSub] at hJ'
  have h1 := hα _ hJ' (g⁻¹ * u * g⁻¹⁻¹) (hu.conj g⁻¹)
  have h2 := congrArg (conjSub g) h1
  rw [← alphaOf_conjSub, conjSub_closure_pair] at h2
  have e1 : g * t * g⁻¹ = g * t * g⁻¹ := rfl
  have e2 : g * (g⁻¹ * u * g⁻¹⁻¹) * g⁻¹ = u := by group
  rw [e2] at h2
  rw [h2]
  exact Subgroup.map_bot _

theorem exists_mul_of_isSylow2In {J T : Subgroup G}
    (hJ2 : IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)) (hT : IsSylow2In T J) {x : G}
    (hx : x ∈ J) : ∃ s ∈ T, ∃ o ∈ oddCoreImg J, x = s * o := by
  set f := QuotientGroup.mk' (classicalInvolutionOddCore ↥J)
  have hTs : IsSylow2In ((T.subgroupOf J).map f) ((⊤ : Subgroup ↥J).map f) :=
    Hall196.isSylow2In_map_hom f ((isSylow2In_map_subtype_iff (Y := J)).mp (by
      rw [Subgroup.map_subgroupOf_eq_of_le hT.1, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
      exact hT))
  have htop : (⊤ : Subgroup ↥J).map f = ⊤ := by
    rw [Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective _)]
  rw [htop] at hTs
  have heq : (T.subgroupOf J).map f = ⊤ := (hTs.2.2 ⊤ le_rfl (hJ2.to_subgroup ⊤) le_top).symm
  have hmem : f ⟨x, hx⟩ ∈ (T.subgroupOf J).map f := heq ▸ Subgroup.mem_top _
  obtain ⟨s, hs, hsx⟩ := hmem
  refine ⟨s, Subgroup.mem_subgroupOf.mp hs, (s : G)⁻¹ * x, ?_, by group⟩
  have h1 : s⁻¹ * ⟨x, hx⟩ ∈ classicalInvolutionOddCore ↥J := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, hsx,
      inv_mul_cancel]
  exact ⟨_, h1, by simp⟩

theorem oddCoreImg_le_of_tight {J : Subgroup G} {u : G} (hu : IsUniqueInvolution J u)
    (ht : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G)) :
    oddCoreImg J ≤ oddCoreImg (Subgroup.centralizer ({u} : Set G)) :=
  TC.le_oddCoreImg_of_normalizes ((oddCoreImg_le J).trans (isUniqueInvolution_le_centralizer hu))
    (fun _ he _ hn => conj_mem_oddCoreImg (ht he) hn) (odd_natCard_oddCoreImg J)

theorem le_centralizer_of_alpha_sep {K J T : Subgroup G} {z u : G} (hz : IsUniqueInvolution K z)
    (hu : IsUniqueInvolution J u) (hJ2 : IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J))
    (hT : IsSylow2In T J) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (ht : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hα : alphaOf (Subgroup.closure ({z, u} : Set G)) = ⊥) :
    J ≤ Subgroup.centralizer ({z} : Set G) := by
  intro x hx
  obtain ⟨s, hs, o, ho, rfl⟩ := exists_mul_of_isSylow2In hJ2 hT hx
  refine Subgroup.mul_mem _ (S1911.normalizer_le_centralizer_member hz (hTK hs)) ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact commute_of_alphaOf_eq_bot_sep hα (mem_closure_pair_right z u) hu.ne_one
    (oddCoreImg_le_of_tight hu ht ho) (mem_closure_pair_left z u)

omit [Finite G] in
theorem oddCoreImg_le_normalizer_of_alpha {J : Subgroup G} {z u : G} (hz1 : z ≠ 1)
    (ht : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hα : alphaOf (Subgroup.closure ({z, u} : Set G)) = ⊥) :
    oddCoreImg (Subgroup.centralizer ({z} : Set G)) ≤ Subgroup.normalizer (J : Set G) := by
  intro o ho
  refine ht ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact commute_of_alphaOf_eq_bot_sep hα (mem_closure_pair_left z u) hz1 ho
    (mem_closure_pair_right z u)

omit [Finite G] in
theorem TightFam.mem_normalizer_of_conj_eq_mul {r : ℕ} {Δ : Set (Subgroup G)}
    (h : TightFam r G Δ) {J : Subgroup G} (hJ : J ∈ Δ) {u : G} (hu : IsUniqueInvolution J u)
    {s n : G} (hs : s * u * s⁻¹ = u * n) (hn : Odd (orderOf n))
    (hnJ : n ∈ Subgroup.normalizer (J : Set G)) : s ∈ Subgroup.normalizer (J : Set G) := by
  obtain ⟨k, hk⟩ := OddQ.exists_conj_eq_mul hu.sq (by rw [← hs]; exact (hu.conj s).sq) hn
  have h1 : IsUniqueInvolution (conjSub (n ^ k) J) (s * u * s⁻¹) := by
    have := hu.conj (n ^ k)
    rwa [hk, ← hs] at this
  have h2 := h.noTwins _ (h.conjInvariant _ J hJ) _ (h.conjInvariant s J hJ) _ h1 (hu.conj s)
  rw [conjSub_eq_of_mem_normalizer (Subgroup.pow_mem _ hnJ k)] at h2
  exact mem_normalizer_of_conjSub_eq h2.symm

omit [Finite G] in
theorem three_le_of_quat {r : ℕ} (hd : TightDatum R S t)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) : 3 ≤ r := by
  obtain ⟨r', hr', ⟨e'⟩⟩ := hd.quat
  obtain ⟨e⟩ := hq
  have h1 := Nat.card_congr (e.symm.trans e').toEquiv
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, QuaternionGroup.card,
    QuaternionGroup.card] at h1
  have h2 : r - 2 = r' - 2 :=
    Nat.pow_right_injective le_rfl (show 2 ^ (r - 2) = 2 ^ (r' - 2) by omega)
  omega

end CFSG.ClassicalInvolution.Q3.TL4
