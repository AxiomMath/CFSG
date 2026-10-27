module

public import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

theorem index_centralizer_le_of_plane {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ] [Finite Γ]
    (hΓ : IsPGroup p Γ) (U : Subgroup Γ) [U.Normal] (hU : IsElemAbelian p U)
    (hcard : Nat.card U = p ^ 2) : (Subgroup.centralizer (U : Set Γ)).index ≤ p := by
  have hp : p.Prime := Fact.out
  have : Group.IsNilpotent Γ := hΓ.isNilpotent
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have := hp.one_lt
    nlinarith
  obtain ⟨⟨z, hzU, hzC⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hUne)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  by_cases hcen : U ≤ Subgroup.center Γ
  · have : Subgroup.centralizer (U : Set Γ) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.mem_center_iff.1 (hcen hh) g).symm
    rw [this, Subgroup.index_top]
    exact hp.one_lt.le
  obtain ⟨u, huU, hu⟩ : ∃ u ∈ U, u ∉ Subgroup.center Γ := by
    by_contra h
    exact hcen fun x hx => by_contra fun hx' => h ⟨x, hx, hx'⟩
  have hzpow : z ^ p = 1 := hU.2 z hzU
  have hzord : orderOf z = p := orderOf_eq_prime hzpow hz1'
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzord]
  have hzle : Subgroup.zpowers z ≤ Subgroup.center Γ := by
    rw [Subgroup.zpowers_le]; exact hzC
  have huz : u ∉ Subgroup.zpowers z := fun h => hu (hzle h)
  set W : Subgroup Γ := Subgroup.zpowers z ⊔ Subgroup.zpowers u with hW
  have hWU : W ≤ U := sup_le ((Subgroup.zpowers_le).2 hzU) ((Subgroup.zpowers_le).2 huU)
  have hWeq : W = U := by
    have hdvd : Nat.card W ∣ p ^ 2 := hcard ▸ Subgroup.card_dvd_of_le hWU
    obtain ⟨i, hi, hWi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hzW : Subgroup.zpowers z ≤ W := le_sup_left
    have huW : u ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    have hge : p ≤ Nat.card W := hzcard ▸ Subgroup.card_le_of_le hzW
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · exfalso
      have hle : Nat.card W ≤ p := by
        rw [hWi]
        calc p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
          _ = p := pow_one p
      have := Subgroup.eq_of_le_of_card_ge hzW
        (by omega : Nat.card W ≤ Nat.card (Subgroup.zpowers z))
      exact huz (by rw [this]; exact huW)
    · refine Subgroup.eq_of_le_of_card_ge hWU ?_
      rw [hcard, hWi]
      have : i = 2 := le_antisymm hi hi2
      rw [this]
  have hle : Subgroup.centralizer ({u} : Set Γ) ≤ Subgroup.centralizer (U : Set Γ) := by
    intro g hg
    have hug : u * g = g * u := Subgroup.mem_centralizer_iff.1 hg u rfl
    have h1 : Subgroup.zpowers z ≤ Subgroup.centralizer ({g} : Set Γ) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact Subgroup.mem_center_iff.1 hzC g
    have h2 : Subgroup.zpowers u ≤ Subgroup.centralizer ({g} : Set Γ) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact hug.symm
    have h3 : U ≤ Subgroup.centralizer ({g} : Set Γ) := hWeq ▸ sup_le h1 h2
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.1 (h3 hx) g rfl).symm
  have hsub : conjugatesOf u ⊆ (U : Set Γ) \ (Subgroup.zpowers z : Set Γ) := by
    intro v hv
    obtain ⟨c, rfl⟩ := isConj_iff.1 hv
    refine ⟨(inferInstance : U.Normal).conj_mem u huU c, fun hvz => ?_⟩
    have hc : c * u * c⁻¹ ∈ Subgroup.center Γ := hzle hvz
    have : c⁻¹ * (c * u * c⁻¹) * c⁻¹⁻¹ ∈ Subgroup.center Γ :=
      (inferInstance : (Subgroup.center Γ).Normal).conj_mem _ hc c⁻¹
    apply hu
    simpa [mul_assoc] using this
  have hUn : (U : Set Γ).ncard = p ^ 2 := by
    rw [← Nat.card_coe_set_eq]; exact hcard
  have hZn : (Subgroup.zpowers z : Set Γ).ncard = p := by
    rw [← Nat.card_coe_set_eq]; exact hzcard
  have hzsub : (Subgroup.zpowers z : Set Γ) ⊆ (U : Set Γ) := by
    intro x hx
    exact ((Subgroup.zpowers_le).2 hzU) hx
  have hcnt : (conjugatesOf u).ncard ≤ p ^ 2 - p := by
    calc (conjugatesOf u).ncard
        ≤ ((U : Set Γ) \ (Subgroup.zpowers z : Set Γ)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = (U : Set Γ).ncard - (Subgroup.zpowers z : Set Γ).ncard :=
          Set.ncard_sdiff hzsub (Set.toFinite _)
      _ = p ^ 2 - p := by rw [hUn, hZn]
  have hidx : (Subgroup.centralizer ({u} : Set Γ)).index = (conjugatesOf u).ncard :=
    Subgroup.index_centralizer_eq_ncard u
  obtain ⟨n, hn⟩ := hΓ.index (Subgroup.centralizer ({u} : Set Γ))
  have hlt : p ^ n < p ^ 2 := by
    rw [← hn, hidx]
    calc (conjugatesOf u).ncard ≤ p ^ 2 - p := hcnt
      _ < p ^ 2 := Nat.sub_lt (pow_pos hp.pos 2) hp.pos
  have hn2 : n < 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
  have hpn : p ^ n ≤ p := by
    calc p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      _ = p := pow_one p
  exact (Nat.le_of_dvd (by rw [hn]; exact pow_pos hp.pos n)
    (Subgroup.index_dvd_of_le hle)).trans (hn ▸ hpn)

theorem card_le_mul_card_inf_centralizer {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {P U F : Subgroup G} (hP : IsPGroup p P) (hU : IsPPlane p U) (hUP : U ≤ P)
    (hN : P ≤ Subgroup.normalizer (U : Set G)) (hFP : F ≤ P) :
    Nat.card F ≤ p * Nat.card ↥(F ⊓ Subgroup.centralizer (U : Set G)) := by
  set U' : Subgroup P := U.subgroupOf P with hU'
  have hnormal : U'.Normal := ⟨fun n hn g => by
    rw [hU', Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hN g.2) n.1).1 hn⟩
  have hel : IsElemAbelian p U' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · exact elemAbelian_comm hU.1 a.2 b.2
    · exact Subtype.ext (hU.1.2 x.1 hx)
  have hcard : Nat.card U' = p ^ 2 := by
    rw [← hU.2, ← Subgroup.card_map_of_injective P.subtype_injective, hU',
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUP]
  have hidx := index_centralizer_le_of_plane (p := p) hP U' hel hcard
  have hC : (Subgroup.centralizer (U : Set G)).subgroupOf P =
      Subgroup.centralizer (U' : Set P) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx h hh
      exact Subtype.ext (hx h.1 hh)
    · intro hx h hh
      exact congrArg Subtype.val (hx ⟨h, hUP hh⟩ hh)
  have hrel : (Subgroup.centralizer (U : Set G)).relIndex P ≤ p := by
    rw [Subgroup.relIndex, hC]; exact hidx
  have hne : (Subgroup.centralizer (U : Set G)).relIndex P ≠ 0 := by
    intro h0
    have hd := Subgroup.relIndex_dvd_card (H := Subgroup.centralizer (U : Set G)) (K := P)
    rw [h0, zero_dvd_iff] at hd
    exact (Nat.card_pos (α := P)).ne' hd
  have hrelF : (Subgroup.centralizer (U : Set G)).relIndex F ≤
      (Subgroup.centralizer (U : Set G)).relIndex P :=
    Subgroup.relIndex_le_of_le_right hFP hne
  have := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (U : Set G)) (K := F)
  rw [inf_comm] at this
  rw [← this]
  exact Nat.mul_le_mul_right _ (hrelF.trans hrel)

end CFSG.LocalAnalysis.GLTheoremB
