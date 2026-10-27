module

public import CFSG.ClassicalInvolution.Q3.TL4SepCompo

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

theorem T4Hyp.commutes_of_not_mem_component (h : T4Hyp r G Δ) (hgen : omegaGen Δ = ⊤)
    (hno : NoInvO2 Δ) {K J : Subgroup G} (hK : K ∈ Δ) (hJ : J ∈ Δ) {z t : G}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) {L : Subgroup G}
    (hL : CFSG.IsComponent L) (hzL : z ∈ L) (htL : t ∉ L) : Commutes K J := by
  have hLn := h.component_normal hgen hno hL
  obtain ⟨L', hL', hL'n, htL'⟩ := h.exists_component hgen hno hJ ht
  have hne : L ≠ L' := fun e => htL (e ▸ htL')
  have hLt : L ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_ne hL hL' hne hx htL')
  have hL'z : L' ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_ne hL' hL hne.symm hx hzL)
  have hJL := h.le_centralizer_component_of_le hJ ht hL hLn hLt
  have hKL' := h.le_centralizer_component_of_le hK hz hL' hL'n hL'z
  have hJN : J ≤ Subgroup.normalizer (K : Set G) := fun j hj =>
    h.tight K hK z hz (Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hJL hj)) z hzL).symm)
  have hKN : K ≤ Subgroup.normalizer (J : Set G) := fun k hk =>
    h.tight J hJ t ht (Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hKL' hk)) t htL').symm)
  have hzJ : z ∉ J := by
    intro hzJ
    have hzt : z = t := (ht.unique z hzJ hz.sq).resolve_left hz.ne_one
    exact htL (hzt ▸ hzL)
  obtain ⟨SK⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hdK := h.tightDatum hK hz SK
  have hKJ : ∀ c ∈ K, c ∈ J → c = 1 := by
    intro c hcK hcJ
    have hodd := odd_orderOf_of_not_mem hdK hzJ hcK hcJ
    have hle : layer G ≤ Subgroup.centralizer ({c} : Set G) := by
      refine sSup_le fun M hM => ?_
      by_cases hML : M = L
      · subst hML
        exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (hJL hcJ)) x hx)
      · have hzM := h.not_mem_component_of_ne hno hK hz hL hM (Ne.symm hML) hzL
        have hKM := h.le_centralizer_component hgen hno hK hz hM hzM
        exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (hKM hcK)) x hx)
    have hcE : c ∈ Subgroup.centralizer (layer G : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    have hFZ := h.le_center_of_normal_two hgen hno fittingSubgroup_normal
      (isPGroup_fittingSubgroup h.odd)
    have hcF : c ∈ Subgroup.centralizer (fittingSubgroup G : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => (Subgroup.mem_center_iff.mp (hFZ hy) c).symm
    have hcC : c ∈ Subgroup.centralizer (generalizedFitting G : Set G) :=
      le_centralizer_sup (Subgroup.zpowers_le.mpr hcF) (Subgroup.zpowers_le.mpr hcE)
        (Subgroup.mem_zpowers c)
    have hcFs : c ∈ generalizedFitting G := centralizer_generalizedFitting_le G hcC
    exact eq_one_of_isPGroup_of_mem_odd (A := Subgroup.zpowers c)
      (by rw [Nat.card_zpowers]; exact hodd) (Subgroup.mem_zpowers c)
      ((isPGroup_center_fstar h.odd).to_le (Subgroup.zpowers_le.mpr ⟨hcFs, hcC⟩))
  intro k hk j hj
  have hc1 : k * j * k⁻¹ * j⁻¹ ∈ J :=
    J.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN hk) j).mp hj) (J.inv_mem hj)
  have hc2 : k * j * k⁻¹ * j⁻¹ ∈ K := by
    have h1 : j * k⁻¹ * j⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hJN hj) k⁻¹).mp (K.inv_mem hk)
    have h2 := K.mul_mem hk h1
    rwa [show k * (j * k⁻¹ * j⁻¹) = k * j * k⁻¹ * j⁻¹ by group] at h2
  have h1 := hKJ _ hc2 hc1
  calc k * j = k * j * k⁻¹ * j⁻¹ * (j * k) := by group
    _ = j * k := by rw [h1, one_mul]

variable {J L : Subgroup G}

theorem T4Min.inv_mem_component
    (hm : T4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L)
    (hgen : omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤)
    (hno : NoInvO2 (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L)) :
    ∃ L₀ : Subgroup G, CFSG.IsComponent L₀ ∧
      ∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, ∀ z : G,
        IsUniqueInvolution K z → z ∈ L₀ := by
  obtain ⟨u, hu⟩ := (hm.hyp.hyp.omega1 J hm.memJ).1
  obtain ⟨v, hv⟩ := (hm.hyp.hyp.omega1 L hm.memL).1
  obtain ⟨L₀, hL₀, hL₀n, huL₀⟩ := hm.hyp.exists_component hgen hno hm.memJ hu
  have hvL₀ : v ∈ L₀ := by
    by_contra hvL₀
    exact hm.notComm (hm.hyp.commutes_of_not_mem_component hgen hno hm.memJ hm.memL hu hv hL₀
      huL₀ hvL₀)
  refine ⟨L₀, hL₀, ?_⟩
  rintro K (⟨g, rfl⟩ | ⟨g, rfl⟩) z hz
  · rw [hz.eq (hu.conj g)]
    exact hL₀n.conj_mem u huL₀ g
  · rw [hz.eq (hv.conj g)]
    exact hL₀n.conj_mem v hvL₀ g

end CFSG.ClassicalInvolution.Q3.TL4
