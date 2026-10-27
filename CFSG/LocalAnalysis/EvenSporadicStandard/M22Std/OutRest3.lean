module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutSplit
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutKEngine
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutEngineData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22Engine
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter2
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutConfig

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std

theorem z_ne_sq_of_complement {G : Type} [Group G] {z : G} {A : Subgroup G} (hz2 : z * z = 1)
    (hAH : A ≤ centralizer ({z} : Set G)) (hzA : z ∉ A)
    (hAz : A ⊔ zpowers z = centralizer ({z} : Set G)) (g : G) : g * g ≠ z := by
  intro hg
  have hgC : g ∈ A ⊔ zpowers z := by
    rw [hAz, mem_centralizer_singleton_iff]
    rw [← hg]
    group
  have hzA' : zpowers z ≤ centralizer (A : Set G) :=
    zpowers_le.2 (mem_centralizer_iff.2 fun a ha => mem_centralizer_singleton_iff.1 (hAH ha))
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hzA' hgC
  have hac : a * z = z * a := mem_centralizer_iff.1 (hzA' (Subgroup.mem_zpowers z)) a ha
  rcases mem_zpowers_involution hz2 hb with hb1 | hbz
  · rw [hb1, mul_one] at hab
    apply hzA
    rw [← hg, hab]
    exact A.mul_mem ha ha
  · rw [hbz] at hab
    have : g * g = a * a := by
      rw [hab]
      calc a * z * (a * z) = a * (z * a) * z := by simp only [mul_assoc]
        _ = a * (a * z) * z := by rw [← hac]
        _ = a * a * (z * z) := by simp only [mul_assoc]
        _ = a * a := by rw [hz2, mul_one]
    apply hzA
    rw [← hg, this]
    exact A.mul_mem ha ha

@[expose] def Fin77aOuterRest₃ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (L : Subgroup G) (z t : G)
    (T₁ : Subgroup (centralizer ({z} : Set G))) (F : Subgroup (L ⧸ center L))
    (tb : L ⧸ center L) (Q : Sylow 2 G) (x : G) (L1 : Subgroup G),
    OutData L z t T₁ F tb → StdHyp G L → IsSporadic L .M22 →
    (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    (L ⊔ zpowers z).relIndex (centralizer ({z} : Set G)) = 2 →
    (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) ≤ (Q : Subgroup G) →
    x ∈ (Q : Subgroup G) → x ∉ (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) →
    x ∈ normalizer ((T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) : Set G) →
    x * z * x⁻¹ = z * t → x * t * x⁻¹ = t →
    (∀ q ∈ (Q : Subgroup G), q * t = t * q) →
    (Q : Subgroup G) ⊓ centralizer ({z} : Set G) =
      (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) →
    z ∈ (commutator ↥(centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype →
    OutOne L z (liftSub F) →
    (∃ y ∈ centralizer ({z} : Set G), y ∉ L ⊔ zpowers z ∧ y * y = 1) →
    (∃ A : Subgroup G, L ≤ A ∧ A ≤ centralizer ({z} : Set G) ∧ z ∉ A ∧
      A ⊔ zpowers z = centralizer ({z} : Set G) ∧ (L.subgroupOf A).index = 2) →
    (∀ f ∈ liftSub F, ∃ c : G, (∀ y, y ∈ liftSub F ⊔ zpowers z ↔
      c * y * c⁻¹ ∈ liftSub F ⊔ zpowers z) ∧ c * z * c⁻¹ = z * f) →
    Nat.card (Ksub z (liftSub F)) = 512 →
    (∀ k ∈ Ksub z (liftSub F), (∀ k' ∈ Ksub z (liftSub F), k * k' = k' * k) ↔ k ∈ liftSub F) →
    (∀ g : G, g * g ≠ z) → KStructure z (liftSub F) L1 → False

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_outer_of_rest₃
    (hEng : AutSylowEngine (Carrier .M22)) (hR : Fin77aOuterRest₃) (h : StdHyp G L)
    (hL : IsSporadic L .M22) {z : G} (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2)
    (hrel : (L ⊔ zpowers z).relIndex (centralizer ({z} : Set G)) = 2) : False := by
  have := h.simple
  have hS := card_sylow_eq_two_of_isSporadic h hL
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic hL
  have hq : IsSporadic (L ⧸ center L) .M22 := isSporadic_quotient_of_center_eq_bot hZ hL
  have hcZ : center (L ⧸ center L) = ⊥ := center_eq_bot_of_isSporadic hq
  have hout := innAut_index_dvd_two hq
  obtain ⟨e⟩ := hq
  have hEng' : AutSylowEngine (L ⧸ center L) := hEng.of_mulEquiv e.symm
  obtain ⟨T₁, t, tb, F, hcfg, htl, W⟩ :=
    exists_outerConfig_facts h hS hZ hcZ hEng'.facts hout hz hz2 hrel
  have hMN := h.centralizer_le_normalizer hz hz2
  have D : OutData L z t T₁ F tb :=
    ⟨hcfg, hZ, fun g => thetaH_eq_one_iff h hS hz hz2 hMN g, W, htl⟩
  obtain ⟨Q, x, hTQ, hxQ, hxT, hxN, hxz, hxt⟩ := hcfg.exists_swap h.nonabelian
  have htQ := hcfg.t_central_Q Q.isPGroup' hTQ hxQ hxz hxt
  have hcomm := hcfg.z_mem_commutator h.nonabelian
  have hone : ∀ u ∈ L, u * u = 1 → u ≠ 1 → ∃ c ∈ L, u = c * t * c⁻¹ := fun u hu hu2 hu1 =>
    oneClass_of_isSporadic hL D.t_mem_L hu hcfg.t_sq hu2 hcfg.t_ne hu1
  have hO := D.outOne h.nonabelian hone
  have htr := D.transitive_E1 hone hxN hxz hxt h.nonabelian
  obtain ⟨y, hyH, hyo, hy2⟩ := D.exists_outer_involution hcZ hxN hxz hxt
  obtain ⟨A, hLA, hAH, -, hzA, hAz, hidx⟩ := D.exists_complement hyH hyo hy2
  have hsq : ∀ g : G, g * g ≠ z := z_ne_sq_of_complement D.cfg.z_sq hAH hzA hAz
  have hE := D.engine hcZ hEng'
  have hcr := hO.centRank_of_rankFour (m22_rankFour hL) hrel
  obtain ⟨L1, hK⟩ := hO.kStructure hsq (D.fixedData hE.fixed) htr (D.liftData hE.lift) hcr
  exact hR G L z t T₁ F tb Q x L1 D h hL hS hrel hTQ hxQ hxT hxN hxz hxt htQ
    (hcfg.inf_centralizer_eq Q.isPGroup' hTQ) ⟨_, hcomm, rfl⟩ hO
    ⟨y, hyH, hyo, hy2⟩ ⟨A, hLA, hAH, hzA, hAz, hidx⟩ htr
    (D.card_K hone hxN hxz hxt h.nonabelian)
    (fun k hk => D.center_K hone hxN hxz hxt h.nonabelian hk) hsq hK

end CFSG.EvenSporadicStandard.M22Std
