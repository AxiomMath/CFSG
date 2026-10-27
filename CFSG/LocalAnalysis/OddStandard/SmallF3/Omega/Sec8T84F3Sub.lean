module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem isElemAb2_map {H G : Type} [Group H] [Group G] (ι : H →* G)
    (hι : Function.Injective ι) {U : Subgroup H} {k : ℕ} :
    IsElemAb2 (U.map ι) k ↔ IsElemAb2 U k := by
  constructor
  · intro h
    haveI : IsMulCommutative (U.map ι) := h.1.1
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine IsMulCommutative.of_setLike_mul_comm fun a ha b hb => hι ?_
      rw [map_mul, map_mul]
      exact setLike_mul_comm (Subgroup.mem_map_of_mem ι ha) (Subgroup.mem_map_of_mem ι hb)
    · intro x hx
      exact hι (by rw [map_pow, map_one]; exact h.1.2 (ι x) (Subgroup.mem_map_of_mem ι hx))
    · rw [← Subgroup.card_map_of_injective hι, h.2]
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · haveI : IsMulCommutative U := h.1.1
      infer_instance
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, h.1.2 u hu, map_one]
    · rw [Subgroup.card_map_of_injective hι, h.2]

private theorem comap_le_of_map_le {H G : Type*} [Group H] [Group G] (ι : H →* G)
    (hι : Function.Injective ι) {K' : Subgroup G} {P : Subgroup H}
    (h : K' ≤ P.map ι) : K'.comap ι ≤ P := by
  intro x hx
  exact (Subgroup.mem_map_iff_mem hι).mp (h (Subgroup.mem_comap.mp hx))

private theorem normal_subgroupOf_map {H G : Type*} [Group H] [Group G] (ι : H →* G)
    {U P : Subgroup H} (hUP : U ≤ P) (hN : (U.subgroupOf P).Normal) :
    ((U.map ι).subgroupOf (P.map ι)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hUP)]
  intro f p hf hp
  obtain ⟨f₀, hf₀, rfl⟩ := Subgroup.mem_map.mp hf
  obtain ⟨p₀, hp₀, rfl⟩ := Subgroup.mem_map.mp hp
  refine ⟨p₀ * f₀ * p₀⁻¹,
    (Subgroup.normal_subgroupOf_iff hUP).mp hN f₀ p₀ hf₀ hp₀, ?_⟩
  simp only [map_mul, map_inv]

private theorem map_inf_centralizer_eq {H G : Type*} [Group H] [Group G] (ι : H →* G)
    (hι : Function.Injective ι) (P V : Subgroup H) :
    (P ⊓ Subgroup.centralizer (V : Set H)).map ι =
      (P.map ι) ⊓ Subgroup.centralizer ((V.map ι : Subgroup G) : Set G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨hyP, hyC⟩ := hy
    have hyC' := Subgroup.mem_centralizer_iff.mp hyC
    refine ⟨Subgroup.mem_map_of_mem ι hyP, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro z hz
    rw [Subgroup.coe_map] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    rw [← map_mul, ← map_mul, hyC' v hv]
  · intro x hx
    obtain ⟨hxP, hxC⟩ := hx
    obtain ⟨y, hyP, rfl⟩ := Subgroup.mem_map.mp hxP
    have hxC' := Subgroup.mem_centralizer_iff.mp hxC
    refine Subgroup.mem_map_of_mem ι ⟨hyP, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro v hv
    apply hι
    rw [map_mul, map_mul]
    exact hxC' (ι v) (by rw [Subgroup.coe_map]; exact ⟨v, hv, rfl⟩)

theorem sec8t84_pmod_subtype {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    {V P F : Subgroup ↥Y} (h : Sec8T84PMod ↥Y V P F) :
    Sec8T84PMod G (V.map Y.subtype) (P.map Y.subtype) (F.map Y.subtype) := by
  let ι : ↥Y →* G := Y.subtype
  have hι : Function.Injective ι := Subgroup.subtype_injective Y
  change Sec8T84PMod G (V.map ι) (P.map ι) (F.map ι)
  refine ⟨?_, Subgroup.map_mono h.V_le, Subgroup.map_mono h.F_le,
    (isElemAb2_map ι hι).mpr h.V_e16, (isElemAb2_map ι hι).mpr h.F_e16,
    fun heq => h.F_ne (Subgroup.map_injective hι heq),
    normal_subgroupOf_map ι h.V_le h.V_norm, normal_subgroupOf_map ι h.F_le h.F_norm,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hι, h.card]
  · intro F' hFP hE4
    have hF''P : F'.comap ι ≤ P := comap_le_of_map_le ι hι hFP
    have hEq : (F'.comap ι).map ι = F' :=
      Subgroup.map_comap_eq_self (f := ι) (hFP.trans (Subgroup.map_le_range (f := ι) P))
    have hF''4 : IsElemAb2 (F'.comap ι) 4 := by
      rw [← hEq] at hE4
      exact (isElemAb2_map ι hι).mp hE4
    rcases h.only (F'.comap ι) hF''P hF''4 with hV | hF
    · left
      have := congrArg (Subgroup.map ι) hV
      rwa [hEq] at this
    · right
      have := congrArg (Subgroup.map ι) hF
      rwa [hEq] at this
  · intro F' hFP hE5
    have hF''P : F'.comap ι ≤ P := comap_le_of_map_le ι hι hFP
    have hEq : (F'.comap ι).map ι = F' :=
      Subgroup.map_comap_eq_self (f := ι) (hFP.trans (Subgroup.map_le_range (f := ι) P))
    have hF''5 : IsElemAb2 (F'.comap ι) 5 := by
      rw [← hEq] at hE5
      exact (isElemAb2_map ι hι).mp hE5
    exact h.no32 (F'.comap ι) hF''P hF''5
  · rw [← Subgroup.map_sup V F ι, Subgroup.card_map_of_injective hι, h.J_card]
  · rw [← Subgroup.map_inf V F ι hι, Subgroup.card_map_of_injective hι, h.EF_card]
  · rw [← map_inf_centralizer_eq ι hι P V, h.cent_V]
  · rw [← map_inf_centralizer_eq ι hι P F, h.cent_F]
  · obtain ⟨s, hsP, hsJ, hs_ord, hsp⟩ := h.gen
    refine ⟨ι s, Subgroup.mem_map_of_mem ι hsP, ?_, ?_, ?_⟩
    · intro hsJ'
      rw [← Subgroup.map_sup V F ι] at hsJ'
      exact hsJ ((Subgroup.mem_map_iff_mem hι).mp hsJ')
    · rw [orderOf_injective ι hι s, hs_ord]
    · rw [hsp, Subgroup.map_sup (zpowers s) (V ⊔ F) ι, Subgroup.map_sup V F ι,
        MonoidHom.map_zpowers]

end CFSG.OddStandard.SmallF3.Omega
