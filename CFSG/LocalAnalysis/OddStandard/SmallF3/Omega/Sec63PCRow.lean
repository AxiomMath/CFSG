module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCMap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCComp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketCentral

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63PC_isI4PlusIn_of_chain {Y K M : Subgroup G} {y : G} (hy2 : orderOf y = 2)
    (hyK : y ∈ K) (hKM : K ≤ M) (hMC : M ≤ Y ⊓ centralizer ({y} : Set G))
    (hK : ∀ k ∈ K, ∀ m ∈ M, m * k * m⁻¹ ∈ K)
    (hM : ∀ m ∈ M, ∀ c ∈ Y ⊓ centralizer ({y} : Set G), c * m * c⁻¹ ∈ M)
    (hSL : IsSL23Mod ↥K) : IsI4PlusIn Y y := by
  refine ⟨hy2, K, hyK, hKM.trans hMC, ?_, hSL⟩
  exact isSubnormal_subgroupOf_of_three_step hKM le_rfl hK
    (fun l hl m hm => M.mul_mem (M.mul_mem hm hl) (M.inv_mem hm)) hM

theorem sec63PC_fact_inner [Finite G] {Y L : Subgroup G} {t b c : G} (hA : Sec63PCA6 Y t L)
    (hb : b ∈ L) (hconj : ∀ x ∈ L, orderOf x = 2 → ∃ l ∈ L, x = l * b * l⁻¹)
    (hc : c ∈ Y) (hct : c * t * c⁻¹ = b)
    (hcent : Nat.card ↥(L ⊓ centralizer ({b} : Set G) ⊓
      centralizer ((L.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G)) ≤ 2)
    {R : Subgroup G} (hR : R ≤ L ⊓ centralizer ({b} : Set G)) (hR8 : Nat.card R = 8)
    (hRgen : R = closure {r : G | r ∈ R ∧ orderOf r = 2}) : Sec63PCFact Y t := by
  obtain ⟨hLH, hLn, hpow, hs⟩ := hA
  intro V hV hL b' hb' hb'2
  have hVeq : V = L := sec63PC_component_eq hLH hLn hpow hs hV
  subst V
  obtain ⟨l, hl, hl_eq⟩ := hconj b' hb' hb'2
  have hlY : l ∈ Y := (Subgroup.mem_inf.mp (hLH hl)).1
  rw [hl_eq]
  apply sec63PC_at_conj hlY hl
  have hH : (Y ⊓ centralizer ({t} : Set G)).map (MulAut.conj c).toMonoidHom =
      Y ⊓ centralizer ({b} : Set G) := by
    rw [CFSG.centralizer_inter_map (MulAut.conj c) Y t, sec63PC_map_conj_of_mem hc]
    have he : (MulAut.conj c) t = b := by
      rw [MulAut.conj_apply]
      exact hct
    rw [he]
  refine Or.inr ⟨L.map (MulAut.conj c).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hH]
    exact (sec63PT_isComponentIn_map_iff (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective).mpr hV
  · exact (sec63PT_isL29_map_iff (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective).mpr hL
  · intro K hK
    have hH' : (Y ⊓ centralizer ({b} : Set G)).map (MulAut.conj c).symm.toMonoidHom =
        Y ⊓ centralizer ({t} : Set G) := by
      rw [← hH, Subgroup.map_map]
      have hcomp : (MulAut.conj c).symm.toMonoidHom.comp (MulAut.conj c).toMonoidHom =
          MonoidHom.id G := by
        ext x
        simp
      rw [hcomp, Subgroup.map_id]
    have hK' : IsComponentIn (K.map (MulAut.conj c).symm.toMonoidHom)
        (Y ⊓ centralizer ({t} : Set G)) := by
      have h := (sec63PT_isComponentIn_map_iff (MulAut.conj c).symm.toMonoidHom
        (MulAut.conj c).symm.injective).mpr hK
      rwa [hH'] at h
    have hKL : K.map (MulAut.conj c).symm.toMonoidHom = L :=
      sec63PC_component_eq hLH hLn hpow hs hK'
    have hmap := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) hKL
    rw [Subgroup.map_map] at hmap
    have hcomp : (MulAut.conj c).toMonoidHom.comp (MulAut.conj c).symm.toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id] at hmap
    exact hmap
  · intro Q _ hQle
    exact le_trans (Subgroup.card_le_of_le hQle) hcent
  · exact ⟨R, IsPGroup.of_card (n := 3) (by rw [hR8]; norm_num), hR, hR8, hRgen⟩

theorem sec63PC_fact_outer [Finite G] {Y L : Subgroup G} {t b : G} (hA : Sec63PCA6 Y t L)
    (hconj : ∀ x ∈ L, orderOf x = 2 → ∃ l ∈ L, x = l * b * l⁻¹)
    (hpocket : IsI4PlusIn Y b) : Sec63PCFact Y t := by
  obtain ⟨hLH, hLn, hpow, hs⟩ := hA
  intro V hV _ b' hb' hb'2
  have hVeq : V = L := sec63PC_component_eq hLH hLn hpow hs hV
  subst V
  obtain ⟨l, hl, hl_eq⟩ := hconj b' hb' hb'2
  have hlY : l ∈ Y := (Subgroup.mem_inf.mp (hLH hl)).1
  rw [hl_eq]
  exact sec63PC_at_conj hlY hl (Or.inl hpocket)

end CFSG.OddStandard.SmallF3.Omega
