module

public import CFSG.ClassicalInvolution.Q3.Q3PBal
public import CFSG.ClassicalInvolution.Q3.Q3MApp
public import CFSG.ClassicalInvolution.Q3.Q3MEnd

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ComponentClassification
open CFSG.ClassicalInvolution.Q3.M
open scoped MatrixGroups

namespace M

theorem three_decomp {X : Type} [Group X] {T D N : Subgroup X} {z : X}
    (hTN : T ≤ N) (hcomm : ∀ t ∈ T, ∀ d ∈ D, t * d = d * t) (hNTD : N ≤ T ⊔ D)
    (h2 : ∀ x ∈ T ⊓ D, ∃ j : ℕ, x ^ (2 ^ j) = 1) (hzN : z ∈ N) :
    ∀ c ∈ Subgroup.centralizer ({z} : Set X) ⊓ N, (∃ k : ℕ, c ^ (3 ^ k) = 1) →
      ∃ u ∈ (Subgroup.centralizer ({z} : Set X) ⊓ N) ⊓ T,
        ∃ v ∈ (Subgroup.centralizer ({z} : Set X) ⊓ N) ⊓ D, c = u * v := by
  intro c hc ⟨k, hk⟩
  obtain ⟨t, ht, d, hd, hcd⟩ := exists_mul_of_mem_sup hcomm (hNTD hc.2)
  obtain ⟨t₀, ht₀, d₀, hd₀, hzd⟩ := exists_mul_of_mem_sup hcomm (hNTD hzN)
  have hzc : z * c = c * z := Subgroup.mem_centralizer_iff.mp hc.1 z (Set.mem_singleton z)
  have hc' : t * d * (t₀ * d₀) = t₀ * d₀ * (t * d) := by
    rw [hcd, hzd] at hzc
    exact hzc.symm
  have hk' : (t * d) ^ (3 ^ k) = 1 := by rw [← hcd]; exact hk
  have ht_comm := commute_of_three_element hcomm h2 ht₀ hd₀ ht hd hc' hk'
  have htz : t ∈ Subgroup.centralizer ({z} : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh, hzd]
    exact ht_comm.symm
  have htCg : t ∈ Subgroup.centralizer ({z} : Set X) ⊓ N := ⟨htz, hTN ht⟩
  refine ⟨t, ⟨htCg, ht⟩, t⁻¹ * c, ⟨?_, ?_⟩, by group⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ htCg) hc
  · have : t⁻¹ * c = d := by rw [hcd]; group
    rw [this]
    exact hd

end M

theorem solvableMemberSplit_proved : SolvableMemberSplit := by
  intro X _ _ hO z L hz hL T hT hTz
  have hzL : z ∈ L := hz.mem
  have hNnorm : (Layer.subgroup X ⊔ CFSG.solvableRadical X).Normal := layer_sup_radical_normal
  set N : Subgroup X := Layer.subgroup X ⊔ CFSG.solvableRadical X with hNdef
  set D : Subgroup X := Subgroup.centralizer (T : Set X) ⊓ N with hDdef
  have hTN : T ≤ N := (Layer.component_le hT).trans le_sup_left
  have hNT : N ≤ Subgroup.normalizer (T : Set X) := layer_sup_radical_le_normalizer hT
  have hNTD : N ≤ T ⊔ D := le_sup_centralizer_inf hT
  have hcommTD : ∀ t ∈ T, ∀ d ∈ D, t * d = d * t := fun t ht d hd =>
    Subgroup.mem_centralizer_iff.mp hd.1 t ht
  have hTconj : ∀ n ∈ N, ∀ t ∈ T, n * t * n⁻¹ ∈ T := fun n hn t ht =>
    (Subgroup.mem_normalizer_iff.mp (hNT hn) t).mp ht
  have hDconj : ∀ n ∈ N, ∀ d ∈ D, n * d * n⁻¹ ∈ D := by
    intro n hn d hd
    have hc : n * d * n⁻¹ ∈ Subgroup.centralizer (T : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have ht' : n⁻¹ * t * n ∈ T := by
        simpa using hTconj n⁻¹ (N.inv_mem hn) t ht
      have h1 : (n⁻¹ * t * n) * d = d * (n⁻¹ * t * n) :=
        Subgroup.mem_centralizer_iff.mp hd.1 _ ht'
      calc t * (n * d * n⁻¹) = n * ((n⁻¹ * t * n) * d) * n⁻¹ := by group
        _ = n * (d * (n⁻¹ * t * n)) * n⁻¹ := by rw [h1]
        _ = n * d * n⁻¹ * t := by group
    exact ⟨hc, N.mul_mem (N.mul_mem hn hd.2) (N.inv_mem hn)⟩
  have hNsub : IsSubnormal N ⊤ := isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hZ2 : ∀ x ∈ T ⊓ D, ∃ j : ℕ, x ^ (2 ^ j) = 1 :=
    central_two_group hO hNsub hTN hcommTD hNTD
  have hzN : z ∈ N := hL hzL
  have hLCz : L ≤ Subgroup.centralizer ({z} : Set X) := isSubnormal_le hz.subnormal
  have hzD : z ∉ D := by
    intro hzD
    apply hTz
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (Subgroup.mem_centralizer_iff.mp hzD.1 t ht).symm
  obtain ⟨φ, hφs, hφodd⟩ := exists_hom_of_member hz
  have hzord := hz.orderOf_eq_two
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzord] at this
  have hz1 : z ≠ 1 := hz.ne_one
  have hzL2 : (⟨z, hzL⟩ : L) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
  have hzL1 : (⟨z, hzL⟩ : L) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzLc : ∀ g : L, g * ⟨z, hzL⟩ = ⟨z, hzL⟩ * g := fun g =>
    Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hLCz g.2) z (Set.mem_singleton z)).symm)
  have hMT : (T.subgroupOf L).Normal := ⟨fun m hm l => by
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    exact hTconj l (hL l.2) m hm⟩
  have hMD : (D.subgroupOf L).Normal := ⟨fun m hm l => by
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    exact hDconj l (hL l.2) m hm⟩
  have hKD : ∀ x : L, (x : X) ∈ D → φ x = 1 := fun x hx =>
    kz_lemma φ hφs hφodd hzL2 hzL1 hzLc (M := D.subgroupOf L)
      (fun h => hzD (Subgroup.mem_subgroupOf.mp h)) x hx
  have hLCg : IsSubnormal L (Subgroup.centralizer ({z} : Set X) ⊓ N) := by
    have := isSubnormal_inf hz.subnormal N
    rwa [inf_eq_left.mpr hL] at this
  have hclaim : ∃ x : L, (x : X) ∈ T ∧ φ x ^ 2 ≠ 1 := by
    by_contra hno
    push Not at hno
    exact wd_apply (Cg := Subgroup.centralizer ({z} : Set X) ⊓ N) (Tg := T) (Dg := D) (L := L)
      (fun c hc t ht => hTconj c hc.2 t ht) (fun c hc d hd => hDconj c hc.2 d hd) hcommTD hZ2
      (three_decomp hTN hcommTD hNTD hZ2 hzN) hLCg φ hφs hKD hno
  obtain ⟨x₀, hx₀T, hx₀⟩ := hclaim
  have hzT : z ∈ T := by
    by_contra hzT
    have h := kz_lemma φ hφs hφodd hzL2 hzL1 hzLc (M := T.subgroupOf L)
      (fun h => hzT (Subgroup.mem_subgroupOf.mp h)) x₀ hx₀T
    exact hx₀ (by rw [h]; exact one_pow 2)
  have hQ : sl2ThreeQ ≤ (T.subgroupOf L).map φ := by
    have : ((T.subgroupOf L).map φ).Normal := Subgroup.Normal.map hMT φ hφs
    exact sl2_normal_Q _ (Subgroup.mem_map_of_mem φ hx₀T) hx₀
  have hodd : Odd (T.relIndex L) := odd_index_of_Q φ hφs hφodd hQ
  have hDCg : D ≤ Subgroup.centralizer ({z} : Set X) ⊓ N := fun d hd =>
    ⟨Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact hcommTD z hzT d hd, hd.2⟩
  exact le_of_odd_index hO hNsub hTN inf_le_right hL hNT hNTD hcommTD hDconj hZ2 inf_le_right
    hDCg hLCg hodd


theorem quasisimpleConnected3Comp_of_L2PrimeBalanceSolv (hb : L2PrimeBalanceSolv) :
    QuasisimpleConnected3Comp :=
  quasisimpleConnected3Comp_of_solvBalance hb solvableMemberSplit_proved

theorem quasisimpleConnected3_of_L2PrimeBalanceSolv (hb : L2PrimeBalanceSolv) :
    QuasisimpleConnected3 :=
  quasisimpleConnected3_of_solvBalance hb solvableMemberSplit_proved

end CFSG.ClassicalInvolution.Q3
