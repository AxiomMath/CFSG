module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict1
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

private theorem conj_mem_centralizer_of_mem_normalizer {G : Type*} [Group G] {M : Subgroup G}
    {g x : G} (hg : g ∈ Subgroup.normalizer (M : Set G))
    (hx : x ∈ Subgroup.centralizer (M : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (M : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro l hl
  have hgl : g⁻¹ * l * g ∈ M :=
    (Subgroup.mem_set_normalizer_iff''.mp hg l).mp hl
  calc l * (g * x * g⁻¹)
      = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [hx (g⁻¹ * l * g) hgl]
    _ = (g * x * g⁻¹) * l := by group

private theorem normalizer_le_normalizer_map_of_characteristic {X : Type*} [Group X]
    {J : Subgroup X} (K : Subgroup J) [hK : K.Characteristic] :
    Subgroup.normalizer (J : Set X) ≤
      Subgroup.normalizer (K.map J.subtype : Set X) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  let e : J ≃* J :=
    ((MulAut.conj g).subgroupMap J).trans (MulEquiv.subgroupCongr hmap)
  have hey : e y ∈ K := by
    rw [← Subgroup.characteristic_iff_map_eq.mp hK e]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hy
  exact Subgroup.mem_map.mpr ⟨e y, hey, rfl⟩

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_centIn_H (hS : HRSetting G L)
    (hSyl : IsSylowIn 2 (centralizer (L : Set G)) (zpowers s.t)) :
    centIn s.H L = zpowers s.t ⊔ s.oddH := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoddH : s.oddH = ⊥ := by
    show (CFSG.oddCore ↥(centralizer ({s.t} : Set G))).map
        (centralizer ({s.t} : Set G)).subtype = ⊥
    rw [hS.balanced s.t s.t_order, Subgroup.map_bot]
  rw [hoddH, sup_bot_eq]
  let C : Subgroup G := centralizer (L : Set G)
  let D : Subgroup G := s.H ⊓ C
  change D = zpowers s.t
  have htH : s.t ∈ s.H := by
    rw [Setting3.H, Subgroup.mem_centralizer_singleton_iff]
  have htD : s.t ∈ D := Subgroup.mem_inf.mpr ⟨htH, s.t_mem⟩
  have hAD : zpowers s.t ≤ D := Subgroup.zpowers_le.mpr htD
  have hDC : D ≤ C := inf_le_right
  have hDH : D ≤ s.H := inf_le_left
  have hPgrpA : IsPGroup 2 (zpowers s.t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, s.t_order]; norm_num)
  have hPgrpPA : IsPGroup 2 ((zpowers s.t).subgroupOf D) :=
    hPgrpA.of_equiv (Subgroup.subgroupOfEquivOfLe hAD).symm
  have hrelidx : (zpowers s.t).relIndex D * D.relIndex C = (zpowers s.t).relIndex C :=
    Subgroup.relIndex_mul_relIndex (H := zpowers s.t) (K := D) (L := C) hAD hDC
  have hPidxPA : ¬ 2 ∣ ((zpowers s.t).subgroupOf D).index := fun h =>
    hSyl.2.2 (h.trans ⟨D.relIndex C, hrelidx.symm⟩)
  let PD : Sylow 2 ↥D := hPgrpPA.toSylow hPidxPA
  have hPDcoe : (PD : Subgroup ↥D) = (zpowers s.t).subgroupOf D := by
    dsimp only [PD]
    exact IsPGroup.toSylow_coe hPgrpPA hPidxPA
  have hcycPA : IsCyclic ↥((zpowers s.t).subgroupOf D) :=
    (Subgroup.subgroupOfEquivOfLe hAD).isCyclic.mpr
      (inferInstance : IsCyclic ↥(zpowers s.t))
  have hcycPD : IsCyclic ↥PD := by
    haveI : IsCyclic ↥((zpowers s.t).subgroupOf D) := hcycPA
    exact Subgroup.isCyclic_of_le (H := (PD : Subgroup ↥D))
      (H' := (zpowers s.t).subgroupOf D) (le_of_eq hPDcoe)
  let K : Subgroup ↥D := CFSG.pPrimeCore 2 ↥D
  obtain ⟨-, hKmul, hKinf, ⟨-, hKodd, -, -⟩, -⟩ :=
    CFSG.cyclic_sylow_normal_odd_complement PD hcycPD
  have hKcomp : K.IsComplement' (PD : Subgroup ↥D) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hKinf) hKmul
  let KG : Subgroup G := K.map D.subtype
  have hKGleH : KG ≤ s.H := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hDH y.2
  let KH : Subgroup ↥s.H := KG.subgroupOf s.H
  have hnormD : s.H ≤ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.le_set_normalizer_iff]
    intro h hh d hd
    rcases Subgroup.mem_inf.mp hd with ⟨hdH, hdC⟩
    exact Subgroup.mem_inf.mpr
      ⟨s.H.mul_mem (s.H.mul_mem hh hdH) (s.H.inv_mem hh),
        conj_mem_centralizer_of_mem_normalizer (s3_H_le_N s hS hh) hdC⟩
  have hnormKG : s.H ≤ Subgroup.normalizer (KG : Set G) :=
    hnormD.trans (normalizer_le_normalizer_map_of_characteristic (J := D) K)
  have hKH_normal : KH.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKGleH).mpr hnormKG
  haveI : KH.Normal := hKH_normal
  have hKHodd : Odd (Nat.card KH) := by
    have h1 : Nat.card KH = Nat.card KG :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKGleH).toEquiv
    have h2 : Nat.card KG = Nat.card K :=
      Subgroup.card_map_of_injective (K := K) (f := D.subtype) Subtype.val_injective
    rw [h1, h2]; exact hKodd
  have hKHle : KH ≤ CFSG.oddCore ↥s.H :=
    le_sSup (s := {N : Subgroup ↥s.H | N.Normal ∧ Odd (Nat.card N)})
      ⟨hKH_normal, hKHodd⟩
  have hKGbot : KG = ⊥ := by
    refine le_bot_iff.mp ?_
    have h := Subgroup.map_mono (f := s.H.subtype) hKHle
    rw [Subgroup.map_subgroupOf_eq_of_le hKGleH] at h
    exact h.trans (le_of_eq hoddH)
  refine le_antisymm ?_ ?_
  · intro d hd
    obtain ⟨⟨n, p⟩, hnp, -⟩ := hKcomp.existsUnique ⟨d, hd⟩
    have hnpG : ((n : ↥D) : G) * ((p : ↥D) : G) = d := by
      simpa using congrArg (fun z : ↥D => (z : G)) hnp
    have hn1 : ((n : ↥D) : G) = 1 := by
      have hnKG : ((n : ↥D) : G) ∈ KG := Subgroup.mem_map.mpr ⟨(n : ↥D), n.2, rfl⟩
      rw [hKGbot] at hnKG
      exact Subgroup.mem_bot.mp hnKG
    have hp_mem : ((p : ↥D) : G) ∈ zpowers s.t := by
      have hp' : (p : ↥D) ∈ (zpowers s.t).subgroupOf D := hPDcoe ▸ p.2
      exact Subgroup.mem_subgroupOf.mp hp'
    rw [← hnpG, hn1, one_mul]
    exact hp_mem
  · exact Subgroup.zpowers_le.mpr htD

end CFSG.OddStandard.HigherRank.YamadaG23
