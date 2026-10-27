module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.K1Cent

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G]

theorem card_le_four_of_lt {B E : Subgroup G} (hBE : B ≤ E) (hE : Nat.card E = 8) (hne : B ≠ E) :
    Nat.card B ≤ 4 := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBE
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hBE (by rw [hk, mul_one]))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero, hE] at hk
    omega
  have h2 : Nat.card B * 2 ≤ 8 :=
    calc Nat.card B * 2 ≤ Nat.card B * k := Nat.mul_le_mul_left _ (by omega)
      _ = Nat.card E := hk.symm
      _ = 8 := hE
  omega

theorem card_inf_le_two_mul {S T : Subgroup G} (hS2 : T.relIndex S = 2) (hTS : T ≤ S)
    (N : Subgroup G) : Nat.card (S ⊓ N : Subgroup G) ≤ 2 * Nat.card (T ⊓ N : Subgroup G) := by
  have hTNK : (T ⊓ N) ⊓ (S ⊓ N) = T ⊓ N := inf_eq_left.2 (inf_le_inf_right N hTS)
  have hTK : T ⊓ N = T ⊓ (S ⊓ N) := by rw [← inf_assoc, inf_eq_left.2 hTS]
  have hT0 : T.relIndex S ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : (T ⊓ N).relIndex (S ⊓ N) ≤ 2 := by
    rw [hTK, Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_le_of_le_right inf_le_left hT0).trans hS2.le
  have h6 := Subgroup.relIndex_mul_card (H := T ⊓ N) (K := S ⊓ N)
  rw [hTNK] at h6
  calc Nat.card (S ⊓ N : Subgroup G) = (T ⊓ N).relIndex (S ⊓ N) * Nat.card (T ⊓ N : Subgroup G) :=
        h6.symm
    _ ≤ 2 * Nat.card (T ⊓ N : Subgroup G) := Nat.mul_le_mul_right _ hrel

namespace K1Ctx

variable {x z : G} {S T P Q Rd F V : Subgroup G} (c : K1Ctx G x z S T P Q Rd F V)
include c

theorem Z_le_of_le_T {E' : Subgroup G} (hE'T : E' ≤ T) (hE'ab : IsElemAb2 E')
    (hE'8 : Nat.card E' = 8) : omegaZ T ≤ E' := by
  intro u hu
  by_contra huE
  have hc : ∀ e ∈ E', ∀ b ∈ Subgroup.zpowers u, e * b = b * e := by
    intro e he b hb
    rcases zpowers_sq_cases hu.2.1 hb with rfl | rfl
    · simp
    · exact (hu.2.2 e (hE'T he)).symm
  have hd : E' ⊓ Subgroup.zpowers u = ⊥ := by
    rw [eq_bot_iff]
    rintro b ⟨hbE, hbu⟩
    rcases zpowers_sq_cases hu.2.1 hbu with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hbE huE
  have hu1 : u ≠ 1 := fun e => huE (by rw [e]; exact E'.one_mem)
  have h16 : Nat.card (E' ⊔ Subgroup.zpowers u : Subgroup G) = 16 := by
    rw [card_sup_of_commute hc hd, hE'8, card_zpowers_of_sq hu.2.1 hu1]
  have hab : IsElemAb2 (E' ⊔ Subgroup.zpowers u) := hE'ab.sup (isElemAb2_zpowers hu.2.1) hc
  have hle : E' ⊔ Subgroup.zpowers u ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (hE'T.trans c.base.T_le_C) ((Subgroup.zpowers_le).2 (c.base.T_le_C hu.1))
  have := c.base.rank_le _ hle hab
  rw [h16] at this
  norm_num at this

theorem card_norm_le_of_le_R {E' : Subgroup G} (hE'R : E' ≤ P ⊔ Subgroup.zpowers x)
    (hE'ab : IsElemAb2 E') (hE'8 : Nat.card E' = 8) :
    Nat.card (T ⊓ Subgroup.normalizer (E' : Set G) : Subgroup G) ≤ 16 := by
  have hRT : P ⊔ Subgroup.zpowers x ≤ T :=
    sup_le c.base.P_le_T ((Subgroup.zpowers_le).2 c.base.x_mem_T)
  have hE'T := hE'R.trans hRT
  have hZE := c.Z_le_of_le_T hE'T hE'ab hE'8
  have hxE : x ∈ E' := hZE c.base.x_mem_Z
  have hzE : z ∈ E' := hZE (c.hz.mem_Z c.base.P_le_T)
  have hB4 : Nat.card (E' ⊓ P : Subgroup G) ≤ 4 :=
    card_le_four_of_lt inf_le_left hE'8 (fun e => c.base.x_not_mem_P (by
      rw [← e] at hxE
      exact hxE.2))
  have hEle : E' ≤ (E' ⊓ P) ⊔ Subgroup.zpowers x := by
    intro e he
    obtain ⟨p, hp, b, hb, rfl⟩ := mem_sup_of_commute c.P_comm_x (hE'R he)
    have hbE : b ∈ E' := by
      rcases zpowers_sq_cases c.base.x_sq hb with rfl | rfl
      · exact E'.one_mem
      · exact hxE
    have hpE : p ∈ E' := by
      have := E'.mul_mem he (E'.inv_mem hbE)
      simpa [mul_assoc] using this
    exact Subgroup.mul_mem_sup ⟨hpE, hp⟩ hb
  have hB4' : 4 ≤ Nat.card (E' ⊓ P : Subgroup G) := by
    have hc : ∀ a ∈ E' ⊓ P, ∀ b ∈ Subgroup.zpowers x, a * b = b * a :=
      fun a ha b hb => c.P_comm_x a ha.2 b hb
    have hd : (E' ⊓ P) ⊓ Subgroup.zpowers x = ⊥ :=
      le_bot_iff.1 (c.PX_disj ▸ inf_le_inf_right _ inf_le_right)
    have h1 := Subgroup.card_le_of_le hEle
    rw [card_sup_of_commute hc hd, card_zpowers_of_sq c.base.x_sq c.base.x_ne_one, hE'8] at h1
    omega
  have hzB : z ∈ E' ⊓ P := ⟨hzE, c.hz.z_mem_P⟩
  have hBn : ((E' ⊓ P : Subgroup G) : Set G).ncard = Nat.card (E' ⊓ P : Subgroup G) := by
    rw [← Nat.card_coe_set_eq]; rfl
  obtain ⟨w, hwB, hw⟩ : ∃ w ∈ ((E' ⊓ P : Subgroup G) : Set G), w ∉ ({1, z} : Set G) :=
    Set.exists_mem_notMem_of_ncard_lt_ncard
      (by rw [Set.ncard_pair c.hz.z_ne_one.symm, hBn]; omega) (Set.toFinite _)
  have hw1 : w ≠ 1 := fun e => hw (Or.inl e)
  have hwz : w ≠ z := fun e => hw (Or.inr e)
  have hwE : w ∈ E' := hwB.1
  have hwP : w ∈ P := hwB.2
  have hwT : w ∈ T := c.base.P_le_T hwP
  have hw2 : w * w = 1 := (hE'ab w hwE).1
  have hwZ : w ∉ omegaZ T := fun hZ => (c.base.P_inf_Z c.hz c.h4 hwP hZ).elim hw1 hwz
  have hX : ∀ t ∈ T ⊓ Subgroup.normalizer (E' : Set G),
      t * w * t⁻¹ ∈ E' ⊓ P ∧ t * w * t⁻¹ ≠ 1 ∧ t * w * t⁻¹ ≠ z := by
    rintro t ⟨htT, htN⟩
    refine ⟨⟨(Subgroup.mem_normalizer_iff.1 htN w).1 hwE, c.base.P_normal.2 t htT w hwP⟩, ?_, ?_⟩
    · intro e
      exact hw1 (conj_inj t (e.trans (by group)))
    · intro e
      have htz : t * z * t⁻¹ = z := by rw [← c.hz.z_central t htT]; group
      exact hwz (conj_inj t (e.trans htz.symm))
  have h2 := card_le_two_mul_of_conj_mem (T ⊓ Subgroup.normalizer (E' : Set G)) w hB4 hzB
    c.hz.z_ne_one hX
  have h3 : Nat.card ((T ⊓ Subgroup.normalizer (E' : Set G)) ⊓ Subgroup.centralizer {w} :
      Subgroup G) ≤ Nat.card (T ⊓ Subgroup.centralizer {w} : Subgroup G) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)
  have h4 := c.card_cent_le hwT hw2 hwZ
  omega

theorem conj_mem_wP (hRdT : Rd = T) {w : G} (hwT : w ∈ T) (hwR : w ∉ P ⊔ Subgroup.zpowers x)
    {t : G} (htT : t ∈ T) : w⁻¹ * (t * w * t⁻¹) ∈ P := by
  have key : ∀ r ∈ P ⊔ Subgroup.zpowers x, w⁻¹ * (r * w * r⁻¹) ∈ P := by
    intro r hr
    obtain ⟨p, hp, b, hb, rfl⟩ := mem_sup_of_commute c.P_comm_x hr
    have hbw : b * w = w * b := by
      rcases zpowers_sq_cases c.base.x_sq hb with rfl | rfl
      · simp
      · exact c.base.x_central w hwT
    have e : w⁻¹ * (p * b * w * (p * b)⁻¹) = (w⁻¹ * p * w) * p⁻¹ := by
      calc w⁻¹ * (p * b * w * (p * b)⁻¹) = w⁻¹ * p * (b * w) * b⁻¹ * p⁻¹ := by group
        _ = w⁻¹ * p * (w * b) * b⁻¹ * p⁻¹ := by rw [hbw]
        _ = (w⁻¹ * p * w) * p⁻¹ := by group
    rw [e]
    exact P.mul_mem (c.base.P_normal.inv_conj hwT hp) (P.inv_mem hp)
  by_cases htR : t ∈ P ⊔ Subgroup.zpowers x
  · exact key t htR
  · have htRd : t ∈ Rd := by rw [hRdT]; exact htT
    have hwRd : w⁻¹ ∈ Rd := by rw [hRdT]; exact T.inv_mem hwT
    have hr := relIndex_two_mul_mem c.R_index htRd hwRd htR
      (fun h => hwR (by simpa using (P ⊔ Subgroup.zpowers x).inv_mem h))
    have e : t * w * t⁻¹ = (t * w⁻¹) * w * (t * w⁻¹)⁻¹ := by group
    rw [e]
    exact key _ hr

theorem card_norm_le_of_le_T {E' : Subgroup G} (hE'T : E' ≤ T)
    (hE'R : ¬ E' ≤ P ⊔ Subgroup.zpowers x) (hE'ab : IsElemAb2 E') (hE'8 : Nat.card E' = 8) :
    Nat.card (T ⊓ Subgroup.normalizer (E' : Set G) : Subgroup G) ≤ 16 := by
  obtain ⟨w, hwE, hwR⟩ := IsConcreteLE.not_le_iff_exists.1 hE'R
  have hZE := c.Z_le_of_le_T hE'T hE'ab hE'8
  have hwT := hE'T hwE
  have hw2 := (hE'ab w hwE).1
  have hwZ : w ∉ omegaZ T := fun h => hwR (c.Z_le_R h)
  have hE'Rd : E' ≤ Rd := fun e he => c.inv_mem_Rd (hE'T he) (hE'ab e he).1
  rcases c.Tn with h1 | ⟨F', hF'T, _, _, hFinf, hTeq, hc1, _, _⟩
  · obtain ⟨t, ht, he⟩ := h1 _ _ c.EV_le_Rd hE'Rd c.EV_ab hE'ab c.EV_card hE'8
    have heq : T ⊓ Subgroup.normalizer (E' : Set G) =
        Hconj t (T ⊓ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) := by
      rw [he, Hconj_inf, Hconj_self_of_mem ht, Hconj_normalizer]
    rw [heq, Hconj_card]
    exact c.card_norm_le_of_le_R c.EV_le_R c.EV_ab c.EV_card
  · have hRdT := c.rd_eq_T hF'T hFinf hTeq hc1
    have hEPZ : ∀ u ∈ E', u ∈ P → u = 1 ∨ u = z := by
      have hlt : E' ⊓ (P ⊔ Subgroup.zpowers x) ≠ E' := fun e => hwR (by
        rw [← e] at hwE
        exact hwE.2)
      have h4 := card_le_four_of_lt inf_le_left hE'8 hlt
      have hZle : omegaZ T ≤ E' ⊓ (P ⊔ Subgroup.zpowers x) := le_inf hZE c.Z_le_R
      have heq : omegaZ T = E' ⊓ (P ⊔ Subgroup.zpowers x) :=
        Subgroup.eq_of_le_of_card_ge hZle (by rw [c.h4]; exact h4)
      intro u huE huP
      have huZ : u ∈ omegaZ T := by rw [heq]; exact ⟨huE, Subgroup.mem_sup_left huP⟩
      exact c.base.P_inf_Z c.hz c.h4 huP huZ
    have hX : ∀ t ∈ T ⊓ Subgroup.normalizer (E' : Set G), t * w * t⁻¹ ∈ ({w, w * z} : Set G) := by
      rintro t ⟨htT, htN⟩
      have h1 := c.conj_mem_wP hRdT hwT hwR htT
      have h2 : w⁻¹ * (t * w * t⁻¹) ∈ E' :=
        E'.mul_mem (E'.inv_mem hwE) ((Subgroup.mem_normalizer_iff.1 htN w).1 hwE)
      rcases hEPZ _ h2 h1 with e | e
      · refine Or.inl ?_
        calc t * w * t⁻¹ = w * (w⁻¹ * (t * w * t⁻¹)) := by group
          _ = w := by rw [e, mul_one]
      · refine Or.inr ?_
        calc t * w * t⁻¹ = w * (w⁻¹ * (t * w * t⁻¹)) := by group
          _ = w * z := by rw [e]
    have h2 := card_le_ncard_mul_of_conj_mem (T ⊓ Subgroup.normalizer (E' : Set G)) w _ hX
    have hn : ({w, w * z} : Set G).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    have h3 : Nat.card ((T ⊓ Subgroup.normalizer (E' : Set G)) ⊓ Subgroup.centralizer {w} :
        Subgroup G) ≤ Nat.card (T ⊓ Subgroup.centralizer {w} : Subgroup G) :=
      Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)
    have h4 := c.card_cent_le hwT hw2 hwZ
    have h5 := Nat.mul_le_mul hn (h3.trans h4)
    omega

theorem card_norm_le_of_not_le_T (hS2 : T.relIndex S = 2) {E' : Subgroup G} (hE'S : E' ≤ S)
    (hE'T : ¬ E' ≤ T) (hE'ab : IsElemAb2 E') (hE'8 : Nat.card E' = 8) (hzE : z ∈ E') :
    Nat.card (T ⊓ Subgroup.normalizer (E' : Set G) : Subgroup G) ≤ 16 := by
  obtain ⟨e, heE, heT⟩ := IsConcreteLE.not_le_iff_exists.1 hE'T
  have hxE : x ∉ E' := fun hx => heT (c.base.extremal e (hE'S heE) ((hE'ab e heE).2 x hx))
  have hT0 : T.relIndex S ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : T.relIndex E' ≤ 2 := (Subgroup.relIndex_le_of_le_right hE'S hT0).trans hS2.le
  have hrel1 : T.relIndex E' ≠ 1 := fun h1 => heT (Subgroup.relIndex_eq_one.1 h1 heE)
  have hrel0 : T.relIndex E' ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul := Subgroup.relIndex_mul_card (H := T) (K := E')
  have hrel2 : T.relIndex E' = 2 := by omega
  have hA4 : Nat.card (T ⊓ E' : Subgroup G) = 4 := by
    rw [hrel2, hE'8] at hmul
    omega
  have hzT : z ∈ T := c.base.P_le_T c.hz.z_mem_P
  have hzB : z ∈ T ⊓ E' := ⟨hzT, hzE⟩
  have hBn : ((T ⊓ E' : Subgroup G) : Set G).ncard = Nat.card (T ⊓ E' : Subgroup G) := by
    rw [← Nat.card_coe_set_eq]; rfl
  obtain ⟨w, hwB, hw⟩ : ∃ w ∈ ((T ⊓ E' : Subgroup G) : Set G), w ∉ ({1, z} : Set G) :=
    Set.exists_mem_notMem_of_ncard_lt_ncard
      (by rw [Set.ncard_pair c.hz.z_ne_one.symm, hBn, hA4]; omega) (Set.toFinite _)
  have hw1 : w ≠ 1 := fun e => hw (Or.inl e)
  have hwz : w ≠ z := fun e => hw (Or.inr e)
  have hwT : w ∈ T := hwB.1
  have hwE : w ∈ E' := hwB.2
  have hw2 : w * w = 1 := (hE'ab w hwE).1
  have hwZ : w ∉ omegaZ T := by
    intro hZ
    rcases c.base.Z_cases c.hz c.h4 w hZ with h | h | h | h
    · exact hw1 h
    · exact hxE (h ▸ hwE)
    · exact hwz h
    · apply hxE
      have : x = w * z := by rw [h, mul_assoc, c.hz.z_sq, mul_one]
      rw [this]
      exact E'.mul_mem hwE hzE
  have hX : ∀ t ∈ T ⊓ Subgroup.normalizer (E' : Set G),
      t * w * t⁻¹ ∈ T ⊓ E' ∧ t * w * t⁻¹ ≠ 1 ∧ t * w * t⁻¹ ≠ z := by
    rintro t ⟨htT, htN⟩
    refine ⟨⟨T.mul_mem (T.mul_mem htT hwT) (T.inv_mem htT),
      (Subgroup.mem_normalizer_iff.1 htN w).1 hwE⟩, ?_, ?_⟩
    · intro e
      exact hw1 (conj_inj t (e.trans (by group)))
    · intro e
      have htz : t * z * t⁻¹ = z := by rw [← c.hz.z_central t htT]; group
      exact hwz (conj_inj t (e.trans htz.symm))
  have h2 := card_le_two_mul_of_conj_mem (T ⊓ Subgroup.normalizer (E' : Set G)) w hA4.le hzB
    c.hz.z_ne_one hX
  have h3 : Nat.card ((T ⊓ Subgroup.normalizer (E' : Set G)) ⊓ Subgroup.centralizer {w} :
      Subgroup G) ≤ Nat.card (T ⊓ Subgroup.centralizer {w} : Subgroup G) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)
  have h4 := c.card_cent_le hwT hw2 hwZ
  omega

theorem card_normalizer_lt (hS2 : T.relIndex S = 2) {E' : Subgroup G} (hE'S : E' ≤ S)
    (hE'ab : IsElemAb2 E') (hE'8 : Nat.card E' = 8) (hzE : z ∈ E') :
    Nat.card (S ⊓ Subgroup.normalizer (E' : Set G) : Subgroup G) < 64 := by
  have h16 : Nat.card (T ⊓ Subgroup.normalizer (E' : Set G) : Subgroup G) ≤ 16 := by
    by_cases hE'T : E' ≤ T
    · by_cases hE'R : E' ≤ P ⊔ Subgroup.zpowers x
      · exact c.card_norm_le_of_le_R hE'R hE'ab hE'8
      · exact c.card_norm_le_of_le_T hE'T hE'R hE'ab hE'8
    · exact c.card_norm_le_of_not_le_T hS2 hE'S hE'T hE'ab hE'8 hzE
  have h2 := card_inf_le_two_mul hS2 c.base.T_le_S (Subgroup.normalizer (E' : Set G))
  omega

end K1Ctx

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
