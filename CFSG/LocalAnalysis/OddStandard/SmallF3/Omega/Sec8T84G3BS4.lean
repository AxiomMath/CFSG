module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BQh
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BAut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84g3b_pfacts_quot (hP : Sec8T84FactP) {A : Type} [Group A] [Finite A]
    {N V H P F : Subgroup A} [N.Normal] [V.Normal] (hN : Odd (Nat.card N))
    (hV : IsElemAb2 V 4) (hVN : ∀ v ∈ V, ∀ n ∈ N, v * n = n * v)
    (hA6 : ∃ φ : A →* alternatingGroup (Fin 6), Function.Surjective φ ∧ φ.ker = V ⊔ N)
    (hHN : H ⊓ (V ⊔ N) ≤ N) (hHsup : H ⊔ (V ⊔ N) = ⊤)
    (htrans : ∀ v ∈ V, v ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ y : A, y * v * y⁻¹ = w)
    (hPs : IsSylow2Of P ⊤) (hFP : F ≤ P) (hF : IsElemAb2 F 4) (hFV : F ≠ V) :
    Sec8T84PFacts (A ⧸ N) (V.map (QuotientGroup.mk' N)) (P.map (QuotientGroup.mk' N))
      (F.map (QuotientGroup.mk' N)) := by
  obtain ⟨Fb, hFb⟩ := sec8t84_factP_quot hP hN hV hVN hA6 hHN hHsup htrans hPs
  have hPN : P ⊓ N = ⊥ := (sec8t84_sylow_map_quot N P hN hPs).1
  have hFN : F ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ P ⊓ N := ⟨hFP hx.1, hx.2⟩
    rwa [hPN] at hx'
  have hFab : IsElemAb2 (F.map (QuotientGroup.mk' N)) 4 :=
    ⟨CFSG.Open.IsElemAbelian.map hF.1 (QuotientGroup.mk' N),
      by rw [sec8t84g3b_card_map_quot N F hFN, hF.2]⟩
  have hFeq : F.map (QuotientGroup.mk' N) = Fb := by
    rcases hFb.only _ (Subgroup.map_mono hFP) hFab with h | h
    · exfalso
      apply hFV
      have hle : F ≤ V := by
        intro f hf
        have hfV : QuotientGroup.mk' N f ∈ V.map (QuotientGroup.mk' N) := by
          rw [← h]; exact Subgroup.mem_map_of_mem _ hf
        obtain ⟨v, hv, hvf⟩ := Subgroup.mem_map.mp hfV
        have hn : v⁻¹ * f ∈ N := by
          have h8 : (QuotientGroup.mk' N) (v⁻¹ * f) = 1 := by
            rw [map_mul, map_inv, hvf, inv_mul_cancel]
          rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h8
        have hfsq : f * f = 1 := hF.1.mul_self_eq_one hf
        have hfv : f = v * (v⁻¹ * f) := by rw [mul_inv_cancel_left]
        have hnv : v * (v⁻¹ * f) = (v⁻¹ * f) * v := hVN v hv _ hn
        have hvv : v * v = 1 := hV.1.mul_self_eq_one hv
        have hnn : (v⁻¹ * f) * (v⁻¹ * f) = 1 := by
          have h9 : f * f = (v * v) * ((v⁻¹ * f) * (v⁻¹ * f)) := by
            calc f * f = (v * (v⁻¹ * f)) * (v * (v⁻¹ * f)) := by rw [← hfv]
              _ = v * ((v⁻¹ * f) * v) * (v⁻¹ * f) := by group
              _ = v * (v * (v⁻¹ * f)) * (v⁻¹ * f) := by rw [← hnv]
              _ = (v * v) * ((v⁻¹ * f) * (v⁻¹ * f)) := by group
          rw [hfsq, hvv, one_mul] at h9
          exact h9.symm
        have hn1 : v⁻¹ * f = 1 := by
          have h10 : orderOf (v⁻¹ * f) ∣ 2 :=
            orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hnn)
          have h11 : orderOf (v⁻¹ * f) ∣ Nat.card N := by
            have := orderOf_dvd_natCard (⟨v⁻¹ * f, hn⟩ : N)
            rwa [Subgroup.orderOf_mk] at this
          rcases (Nat.dvd_prime Nat.prime_two).mp h10 with h12 | h12
          · exact orderOf_eq_one_iff.mp h12
          · rw [h12] at h11
            exact absurd h11 hN.not_two_dvd_nat
        rw [hfv, hn1, mul_one]
        exact hv
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hV.2, hF.2])
    · exact h
  rw [hFeq]
  exact hFb

theorem sec8t84g3b_S4_quot (hP : Sec8T84FactP) (hS4 : Sec8T84FactS4) {A : Type} [Group A]
    [Finite A] {N V H P F : Subgroup A} [N.Normal] [V.Normal] (hN : Odd (Nat.card N))
    (hV : IsElemAb2 V 4) (hVN : ∀ v ∈ V, ∀ n ∈ N, v * n = n * v)
    (hA6 : ∃ φ : A →* alternatingGroup (Fin 6), Function.Surjective φ ∧ φ.ker = V ⊔ N)
    (hHN : H ⊓ (V ⊔ N) ≤ N) (hHsup : H ⊔ (V ⊔ N) = ⊤)
    (htrans : ∀ v ∈ V, v ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ y : A, y * v * y⁻¹ = w)
    (hPs : IsSylow2Of P ⊤) (hFP : F ≤ P) (hF : IsElemAb2 F 4) (hFV : F ≠ V) :
    Sec8T84G3BS4Concl (A ⧸ N) (V.map (QuotientGroup.mk' N)) (F.map (QuotientGroup.mk' N)) := by
  have hF' := sec8t84g3b_pfacts_quot hP hN hV hVN hA6 hHN hHsup htrans hPs hFP hF hFV
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    sec8t84g3b_quot_hyps hN hV hVN hA6 hHN hHsup htrans hPs
  exact hS4 (A ⧸ N) (V.map (QuotientGroup.mk' N)) (H.map (QuotientGroup.mk' N))
    (P.map (QuotientGroup.mk' N)) (F.map (QuotientGroup.mk' N)) h1 h2 h3 h4 h5 h6 h7 hF'

theorem sec8t84g3b_normJ {Y : Type} [Group Y] [Finite Y] {E P F : Subgroup Y} (hE : E.Normal)
    (h : Sec8T84PFacts Y E P F) :
    normalizer ((E ⊔ F : Subgroup Y) : Set Y) ≤ normalizer (F : Set Y) := by
  intro r hr
  have hJle : E ⊔ F ≤ P := sup_le h.E_le h.F_le
  set F' : Subgroup Y := F.map (MulAut.conj r).toMonoidHom with hF'
  have hF'J : F' ≤ E ⊔ F := by
    rintro _ ⟨f, hf, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hr f).mp (Subgroup.mem_sup_right hf)
  have hF'ab : IsElemAb2 F' 4 :=
    ⟨CFSG.Open.IsElemAbelian.map h.F_e16.1 _, by
      rw [hF', Subgroup.card_map_of_injective (MulAut.conj r).injective, h.F_e16.2]⟩
  have hcancel : ∀ f x : Y, r * f * r⁻¹ = r * x * r⁻¹ → f = x := by
    intro f x hfx
    have h1 : r * f = r * x := mul_right_cancel hfx
    exact mul_left_cancel h1
  rcases h.only F' (hF'J.trans hJle) hF'ab with h1 | h1
  · exfalso
    apply h.F_ne
    ext x
    constructor
    · intro hx
      have hrx : r * x * r⁻¹ ∈ F' := Subgroup.mem_map_of_mem (MulAut.conj r).toMonoidHom hx
      rw [h1] at hrx
      have h2 := hE.conj_mem _ hrx r⁻¹
      simpa [mul_assoc] using h2
    · intro hx
      have hrx : r * x * r⁻¹ ∈ E := hE.conj_mem x hx r
      rw [← h1] at hrx
      obtain ⟨f, hf, hfx⟩ := Subgroup.mem_map.mp hrx
      have h2 : f = x := hcancel f x hfx
      rw [← h2]; exact hf
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hrx : r * x * r⁻¹ ∈ F' := Subgroup.mem_map_of_mem (MulAut.conj r).toMonoidHom hx
      rwa [h1] at hrx
    · intro hx
      rw [← h1] at hx
      obtain ⟨f, hf, hfx⟩ := Subgroup.mem_map.mp hx
      have h2 : f = x := hcancel f x hfx
      rw [← h2]; exact hf

theorem sec8t84g3b_pfacts_ydata (hP : Sec8T84FactP) {G : Type} [Group G] [Finite G]
    {Y O V H P F : Subgroup G} (hY : Sec8T84YData G Y O V H) (hPY : IsSylow2Of P Y)
    (hFP : F ≤ P) (hF : IsElemAb2 F 4) (hFV : F ≠ V) [hN : (O.subgroupOf Y).Normal] :
    Sec8T84PFacts (↥Y ⧸ O.subgroupOf Y)
      ((V.subgroupOf Y).map (QuotientGroup.mk' (O.subgroupOf Y)))
      ((P.subgroupOf Y).map (QuotientGroup.mk' (O.subgroupOf Y)))
      ((F.subgroupOf Y).map (QuotientGroup.mk' (O.subgroupOf Y))) := by
  haveI : (V.subgroupOf Y).Normal := hY.V_norm
  obtain ⟨hNo, hV, hVN, hA6, hHN, hHsup, htr⟩ := sec8t84g3b_ydata_sub hY
  have hP' : IsSylow2Of (P.subgroupOf Y) ⊤ := by
    refine ⟨le_top, hPY.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPY.1).symm, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact hPY.2.2
  have hFY : F ≤ Y := hFP.trans hPY.1
  refine sec8t84g3b_pfacts_quot hP hNo hV hVN hA6 hHN hHsup htr hP' (fun x hx => hFP hx)
    ⟨hF.1.subgroupOf Y, by rw [sec8t84g3b_card_subgroupOf hFY, hF.2]⟩ (fun h => hFV ?_)
  have h1 := Subgroup.subgroupOf_inj.mp h
  rwa [inf_eq_left.mpr hFY, inf_eq_left.mpr hY.V_le] at h1

theorem sec8t84g3b_S4_ydata (hP : Sec8T84FactP) (hS4 : Sec8T84FactS4) {G : Type} [Group G]
    [Finite G] {Y O V H P F : Subgroup G} (hY : Sec8T84YData G Y O V H) (hPY : IsSylow2Of P Y)
    (hFP : F ≤ P) (hF : IsElemAb2 F 4) (hFV : F ≠ V) [hN : (O.subgroupOf Y).Normal] :
    Sec8T84G3BS4Concl (↥Y ⧸ O.subgroupOf Y)
      ((V.subgroupOf Y).map (QuotientGroup.mk' (O.subgroupOf Y)))
      ((F.subgroupOf Y).map (QuotientGroup.mk' (O.subgroupOf Y))) := by
  haveI : (V.subgroupOf Y).Normal := hY.V_norm
  obtain ⟨hNo, hV, hVN, hA6, hHN, hHsup, htr⟩ := sec8t84g3b_ydata_sub hY
  have hP' : IsSylow2Of (P.subgroupOf Y) ⊤ := by
    refine ⟨le_top, hPY.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPY.1).symm, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact hPY.2.2
  have hFY : F ≤ Y := hFP.trans hPY.1
  refine sec8t84g3b_S4_quot hP hS4 hNo hV hVN hA6 hHN hHsup htr hP' (fun x hx => hFP hx)
    ⟨hF.1.subgroupOf Y, by rw [sec8t84g3b_card_subgroupOf hFY, hF.2]⟩ (fun h => hFV ?_)
  have h1 := Subgroup.subgroupOf_inj.mp h
  rwa [inf_eq_left.mpr hFY, inf_eq_left.mpr hY.V_le] at h1

theorem sec8t84g3b_normJ_ydata (hP : Sec8T84FactP) {G : Type} [Group G] [Finite G]
    {Y O V H P F : Subgroup G} (hY : Sec8T84YData G Y O V H) (hPY : IsSylow2Of P Y)
    (hFP : F ≤ P) (hF : IsElemAb2 F 4) (hFV : F ≠ V) [hN : (O.subgroupOf Y).Normal] :
    normalizer ((((V.subgroupOf Y).map (QuotientGroup.mk' (O.subgroupOf Y))) ⊔
        ((F.subgroupOf Y).map (QuotientGroup.mk' (O.subgroupOf Y))) :
          Subgroup (↥Y ⧸ O.subgroupOf Y)) : Set (↥Y ⧸ O.subgroupOf Y)) ≤
      normalizer ((((F.subgroupOf Y).map (QuotientGroup.mk' (O.subgroupOf Y))) :
        Subgroup (↥Y ⧸ O.subgroupOf Y)) : Set (↥Y ⧸ O.subgroupOf Y)) := by
  haveI : (V.subgroupOf Y).Normal := hY.V_norm
  exact sec8t84g3b_normJ
    (Subgroup.Normal.map (inferInstance : (V.subgroupOf Y).Normal) _
      (QuotientGroup.mk'_surjective _))
    (sec8t84g3b_pfacts_ydata hP hY hPY hFP hF hFV)

end CFSG.OddStandard.SmallF3.Omega
