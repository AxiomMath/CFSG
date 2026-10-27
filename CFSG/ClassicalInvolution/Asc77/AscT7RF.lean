module

import CFSG.ClassicalInvolution.Asc77.AscIHSectMA
public import CFSG.ClassicalInvolution.Asc77.AscT7FA
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer

section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.sectionHull_u_ne_top (h : Hyp21 p f Ω K K' z u J t W) :
    sectionHull Ω (Subgroup.zpowers u) ≠ ⊤ := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  intro htop
  have hcent : Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) =
      Subgroup.centralizer ({u} : Set G) := by
    rw [CFSG.ClassicalInvolution.Balance.Bootstrap.centralizer_zpowers_eq_singleton']
  have hle : sectionHull Ω (Subgroup.zpowers u) ≤ Subgroup.centralizer ({u} : Set G) := by
    have := sectionHull_le_centralizer Ω (Subgroup.zpowers u)
    rwa [hcent] at this
  rw [htop, top_le_iff] at hle
  have hcomm : ∀ g : G, g * u = u * g := fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle ▸ Subgroup.mem_top g)
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
  obtain ⟨x, -, y, -, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hp hVR).exists_not_commute
  exact h.hu1 (T7A.eq_one_of_central ⟨x, y, hxy⟩ hcomm)

theorem Hyp21.oddCore_rLayer_u_le (h : Hyp21 p f Ω K K' z u J t W) :
    oddCoreOf (rLayer Ω u) ≤ oddCoreOf (Subgroup.centralizer ({u} : Set G)) := by
  have h1 := oddCoreOf_sectionHull_le h.std.stand.hyp (Subgroup.zpowers u)
  rw [← rLayer_eq_sectionHull h.std.stand.odd h.std.stand.five h.std.stand.hyp h.hu2,
    CFSG.ClassicalInvolution.Balance.Bootstrap.centralizer_zpowers_eq_singleton'] at h1
  exact h1

theorem Hyp21.centralizer_u_le_of_disc (h : Hyp21 p f Ω K K' z u J t W)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (hconn : ¬ SectionConnected Ω u)
    {H : Subgroup G} (hY : rLayer Ω u ≤ H)
    (hN : ∀ J₀ ∈ dComp Ω K, Subgroup.normalizer (J₀ : Set G) ≤ H) :
    Subgroup.centralizer ({u} : Set G) ≤ H := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hBelow : CITBelowU p f (Nat.card G) := h.std.stand.below f hq
  have hcA : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one h.hu2
  obtain ⟨g₀, -, hJ₀nbr, hJ₀t⟩ := exists_mem_tqMembers_u hp hq hΩ hK hz h.std.hK' h.std.hne h.hu
    h.hu2 h.hu1 h.hJ h.ht
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hK hz))
  have hJ₀m : conjSub g₀ J ∈ sectionMembers Ω (Subgroup.zpowers u) := by
    rw [sectionMembers_zpowers]; exact hJ₀t
  have horb := (section_connected_or_orbit hp hq hΩ hcA h.sectionHull_u_ne_top hBelow
    (h3s _ hBelow) hJ₀m).resolve_left hconn
  intro c' hc'
  have h1 : conjSub c' (conjSub g₀ J) ∈ sectionMembers Ω (Subgroup.zpowers u) := by
    rw [sectionMembers_zpowers]
    exact conjSub_mem_tqMembers hΩ.conjInvariant hc' hJ₀t
  obtain ⟨g, hg, hgeq⟩ := exists_mem_sectionHull_conj_of_orbit hp hq hΩ hcA hJ₀m horb h1
  have hgY : g ∈ rLayer Ω u := by
    rw [rLayer_eq_sectionHull hp hq hΩ h.hu2]
    exact hg
  set m : G := g⁻¹ * c' with hmdef
  have hm : conjSub m (conjSub g₀ J) = conjSub g₀ J := by
    rw [hmdef, conjSub_mul, hgeq, conjSub_inv_conjSub]
  have hmN : m ∈ Subgroup.normalizer ((conjSub g₀ J : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hm
  have e : c' = g * m := by rw [hmdef]; group
  rw [e]
  exact Subgroup.mul_mem _ (hY hgY) (hN _ hJ₀d hmN)

omit [IsSimpleGroup G] in
theorem Hyp21.centralizer_u_le_of_conn (h : Hyp21 p f Ω K K' z u J t W)
    (hconn : SectionConnected Ω u) {H : Subgroup G}
    (hO : oddCoreOf (Subgroup.centralizer ({u} : Set G)) ≤ H)
    (hN : Subgroup.normalizer (K : Set G) ≤ H)
    (htrans : ∀ L ∈ dstarComp Ω K, ∃ x ∈ H, conjSub x K = L) :
    Subgroup.centralizer ({u} : Set G) ≤ H := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  obtain ⟨g₀, -, hJ₀nbr, hJ₀t⟩ := exists_mem_tqMembers_u hp hq hΩ hK hz h.std.hK' h.std.hne h.hu
    h.hu2 h.hu1 h.hJ h.ht
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hK hz))
  have hJ₀ds : conjSub g₀ J ∈ dstarComp Ω K := T7A.mem_dstarComp_of_mem_dComp hp hΩ hJ₀d
  intro c' hc'
  have h1 : conjSub c' (conjSub g₀ J) ∈ tqMembers Ω u :=
    conjSub_mem_tqMembers hΩ.conjInvariant hc' hJ₀t
  obtain ⟨n, hn, J', -, hJ'd, hMeq⟩ :=
    exists_conj_tqMembers_of_connected hp hq hΩ h.hu2 hJ₀t hconn _ h1
  have hJ'ds : J' ∈ dstarComp Ω K := by
    rw [T7A.dstarComp_eq_of_mem hK hJ₀ds] at hJ'd
    exact hJ'd
  obtain ⟨x', hx'H, hx'⟩ := htrans J' hJ'ds
  obtain ⟨x₀, hx₀H, hx₀⟩ := htrans _ hJ₀ds
  have hc'eq : conjSub (c' * x₀) K = conjSub (n * x') K := by
    rw [conjSub_mul, hx₀, hMeq, ← hx', conjSub_mul]
  have hm : conjSub ((n * x')⁻¹ * (c' * x₀)) K = K := by
    rw [conjSub_mul, hc'eq, conjSub_inv_conjSub]
  have hmH : (n * x')⁻¹ * (c' * x₀) ∈ H := hN (mem_normalizer_iff_conjSub_eq.mpr hm)
  have e : c' = ((n * x') * ((n * x')⁻¹ * (c' * x₀))) * x₀⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hO hn) hx'H) hmH)
    (Subgroup.inv_mem _ hx₀H)

end Frame

end CFSG.ClassicalInvolution.Asc77
