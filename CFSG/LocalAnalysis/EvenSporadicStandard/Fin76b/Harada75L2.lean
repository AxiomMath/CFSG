module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75L22
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Quot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Frame
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75V

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section L2

variable {S : Type} [Group S] [Finite S] {E F : Subgroup S} {z : S}

theorem Cfg2.E_le_centralizer (h : Cfg2 S E F z) :
    E ≤ Subgroup.centralizer (E : Set S) := by
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro e' he'
  exact h.E_comm he' he

theorem Cfg2.card_K_le (hS : IsPGroup 2 S) (h : Cfg2 S E F z) :
    Nat.card (Subgroup.centralizer (E : Set S)) ≤ 16 := by
  have := h.hEn
  refine card_le_sixteen_of_fourGroup hS (K := Subgroup.centralizer (E : Set S)) (E := E) (F := F)
    inferInstance h.hEn h.E_le_centralizer ?_ (fun x hx => h.E_sq hx) h.hE8
    (fun f hf => h.F_sq hf) h.hF4 ?_ ?_
  · intro x hx k hk
    exact Subgroup.mem_centralizer_iff.mp hk x hx
  · intro f hf hf1
    exact h.card_K_fix_le hS hf hf1
  · intro f hf hf1
    exact (h.card_fixE hf hf1).le

theorem Cfg2.K_comm (hS : IsPGroup 2 S) (h : Cfg2 S E F z) :
    ∀ x ∈ Subgroup.centralizer (E : Set S), ∀ y ∈ Subgroup.centralizer (E : Set S),
      x * y = y * x := by
  have := h.hEn
  set K : Subgroup S := Subgroup.centralizer (E : Set S) with hK
  have hEK : E ≤ K := h.E_le_centralizer
  set E' : Subgroup K := E.subgroupOf K with hE'
  have : E'.Normal := Subgroup.Normal.subgroupOf inferInstance K
  have hE'card : Nat.card E' = 8 := by
    rw [hE']
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, h.hE8]
  have hcardK : Nat.card K ≤ 16 := h.card_K_le hS
  have hmul : Nat.card (K ⧸ E') * Nat.card E' = Nat.card K := by
    rw [← Subgroup.index_eq_card]
    exact Subgroup.index_mul_card E'
  have hQ2 : Nat.card (K ⧸ E') ≤ 2 := by
    rw [hE'card] at hmul
    omega
  have : IsCyclic (K ⧸ E') := isCyclic_of_natCard_le_two hQ2
  have hker : (QuotientGroup.mk' E').ker ≤ Subgroup.center K := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hx' : (x : S) ∈ E := hx
    have := Subgroup.mem_centralizer_iff.mp g.2 (x : S) hx'
    exact Subtype.ext this.symm
  intro x hx y hy
  have := commutative_of_cyclic_center_quotient (QuotientGroup.mk' E') hker ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this


theorem Cfg2.rank_quot [E.Normal] (hS : IsPGroup 2 S) (h : Cfg2 S E F z) (U : Subgroup S) :
    Group.rank (U.map (QuotientGroup.mk' (Subgroup.centralizer (E : Set S)))) ≤ 2 := by
  set K : Subgroup S := Subgroup.centralizer (E : Set S) with hK
  have : K.Normal := inferInstance
  set π := QuotientGroup.mk' K with hπ
  set V := U.map π with hV
  have hQp : IsPGroup 2 (S ⧸ K) := hS.to_quotient K
  have hVp : IsPGroup 2 V := hQp.to_subgroup V
  have hidx : K.index ≤ 8 := index_centralizer_le_eight hS h.hEn h.hEa h.hE8
  have hcardQ : Nat.card (S ⧸ K) ≤ 8 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hVle : Nat.card V ≤ 8 := (Subgroup.card_le_card_group V).trans hcardQ
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hVp
  by_cases hm3 : m ≤ 2
  · apply rank_le_of_card_le_two_pow 2 V hVp
    rw [hm]
    exact Nat.pow_le_pow_right (by norm_num) hm3
  · have hm3' : m = 3 := by
      by_contra hne
      have h4 : 4 ≤ m := by omega
      have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h4
      rw [← hm] at this
      omega
    have hV8 : Nat.card V = 8 := by rw [hm, hm3']; norm_num
    have hQ8 : Nat.card (S ⧸ K) = 8 := by
      have := Subgroup.card_le_card_group V
      omega
    have hVtop : V = ⊤ := Subgroup.eq_top_of_card_eq V (by rw [hV8, hQ8])
    obtain ⟨s, t, hst⟩ := exists_comm_not_mem_centralizer hS h.hEn h.hEa h.hE8
      (by rw [Subgroup.index_eq_card]; exact hQ8)
    have hsV : π s ∈ V := by rw [hVtop]; exact Subgroup.mem_top _
    have htV : π t ∈ V := by rw [hVtop]; exact Subgroup.mem_top _
    apply rank_le_of_card_le_mul_frattini hVp 2
    by_cases hΦ : Nat.card (frattini V) = 1
    · exfalso
      have hbot : frattini V = ⊥ := (Subgroup.eq_bot_iff_card _).mpr hΦ
      have hcomm := (commute_sq_of_frattini_bot hVp hbot).1 ⟨π s, hsV⟩ ⟨π t, htV⟩
      have hcomm' : π s * π t = π t * π s := congrArg Subtype.val hcomm
      apply hst
      have hker : π (s * t * s⁻¹ * t⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm']
        group
      exact (QuotientGroup.eq_one_iff (N := K) _).mp hker
    · have hpos : 0 < Nat.card (frattini V) := Nat.card_pos
      have h2 : 2 ≤ Nat.card (frattini V) := by omega
      rw [hV8]
      nlinarith


theorem Cfg2.exists_comm [E.Normal] (hS : IsPGroup 2 S) (h : Cfg2 S E F z) (U : Subgroup S)
    (hU : ¬ IsCyclic (U.map (QuotientGroup.mk' (Subgroup.centralizer (E : Set S))))) :
    ∃ g ∈ U, Nat.card (Subgroup.centralizer ({g} : Set S) ⊓ Subgroup.centralizer (E : Set S) :
      Subgroup S) ≤ 4 := by
  set K : Subgroup S := Subgroup.centralizer (E : Set S) with hK
  have : K.Normal := inferInstance
  set π := QuotientGroup.mk' K with hπ
  set V := U.map π with hV
  have hQp : IsPGroup 2 (S ⧸ K) := hS.to_quotient K
  have hidx : K.index ≤ 8 := index_centralizer_le_eight hS h.hEn h.hEa h.hE8
  have hcardQ : Nat.card (S ⧸ K) ≤ 8 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hKab := h.K_comm hS
  set ψ : F →* S ⧸ K := π.comp F.subtype with hψ
  have hψker : ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    have hf' : π (f : S) = 1 := hf
    have hfK : (f : S) ∈ K := (QuotientGroup.eq_one_iff (N := K) _).mp hf'
    have : (f : S) = 1 := h.hFK f f.2 (fun e he => (Subgroup.mem_centralizer_iff.mp hfK e he).symm)
    exact Subtype.ext this
  have hFbar : Nat.card (F.map π) = 4 := by
    have h1 := card_eq_ker_mul_range ψ
    rw [hψker, Subgroup.card_bot, one_mul, h.hF4] at h1
    have h2 : ψ.range = F.map π := by
      rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h2]
    exact h1.symm
  have hFidx : (F.map π).index ≤ 2 := by
    have := Subgroup.card_mul_index (F.map π)
    rw [hFbar] at this
    omega
  have hV2 : Nat.card V ≤ 2 * Nat.card (V ⊓ F.map π : Subgroup (S ⧸ K)) :=
    card_le_two_mul_inf hFidx V
  have hVcard : 3 ≤ Nat.card V := by
    by_contra hlt
    exact hU (isCyclic_of_natCard_le_two (show Nat.card V ≤ 2 by omega))
  have h3 : 3 ≤ 2 * Nat.card (V ⊓ F.map π : Subgroup (S ⧸ K)) := le_trans hVcard hV2
  have hVF : 2 ≤ Nat.card (V ⊓ F.map π : Subgroup (S ⧸ K)) := by omega
  have hnt : Nontrivial (V ⊓ F.map π : Subgroup (S ⧸ K)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v, hv1⟩ := exists_ne (1 : (V ⊓ F.map π : Subgroup (S ⧸ K)))
  have hvV : (v : S ⧸ K) ∈ V := v.2.1
  have hvF : (v : S ⧸ K) ∈ F.map π := v.2.2
  obtain ⟨u, huU, hu⟩ := Subgroup.mem_map.mp hvV
  obtain ⟨f, hfF, hf⟩ := Subgroup.mem_map.mp hvF
  have hf1 : f ≠ 1 := by
    rintro rfl
    apply hv1
    apply Subtype.ext
    show (v : S ⧸ K) = 1
    rw [← hf, map_one]
  refine ⟨u, huU, ?_⟩
  have hk0 : u⁻¹ * f ∈ K := by
    have : π (u⁻¹ * f) = 1 := by
      rw [map_mul, map_inv, hu, hf, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (N := K) _).mp this
  have hle : Subgroup.centralizer ({u} : Set S) ⊓ K ≤ K ⊓ Subgroup.centralizer ({f} : Set S) := by
    intro y hy
    obtain ⟨hyu, hyK⟩ := hy
    refine ⟨hyK, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hyu' : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hyu
    have hcomm := hKab y hyK (u⁻¹ * f) hk0
    calc y * f = y * (u * (u⁻¹ * f)) := by group
      _ = (y * u) * (u⁻¹ * f) := by group
      _ = (u * y) * (u⁻¹ * f) := by rw [hyu']
      _ = u * (y * (u⁻¹ * f)) := by group
      _ = u * ((u⁻¹ * f) * y) := by rw [hcomm]
      _ = f * y := by group
  exact (Subgroup.card_le_of_le hle).trans (h.card_K_fix_le hS hfF hf1)

theorem genLE4_of_cfg2 (hS : IsPGroup 2 S) (h : Cfg2 S E F z) : GenLE4 S := by
  have := h.hEn
  refine genLE4_of_abelian_normal hS (Subgroup.centralizer (E : Set S)) inferInstance
    (h.K_comm hS) (h.card_K_le hS) ?_ (fun U => h.rank_quot hS U)
    (fun U hU => h.exists_comm hS U hU)
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  exact Subgroup.mem_centralizer_iff.mp hg e (h.E_le_centralizer he)

end L2

end CFSG.EvenSporadicStandard.Fin76b
