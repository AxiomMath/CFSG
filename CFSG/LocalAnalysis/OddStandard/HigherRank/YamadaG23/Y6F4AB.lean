module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AI
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {C : Type} [Group C] {g t : C} {P M : Subgroup C} [(zpowers g).Normal]

private lemma zpowers_eq_one_or_self_of_orderOf {G : Type*} [Group G] {u : G}
    (hu : orderOf u = 2) : ∀ x ∈ zpowers u, x = 1 ∨ x = u := by
  intro x hx
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨k, rfl⟩ := hx
  rw [← zpow_mod_orderOf u k, hu, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

private lemma zpowers_le_closure_pair : zpowers g ≤ closure ({g, t} : Set C) :=
  Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))

private lemma mk'_injective_of_inf_bot {H : Subgroup C} (hH : H ⊓ zpowers g = ⊥) :
    Function.Injective ((QuotientGroup.mk' (zpowers g)).comp H.subtype) := by
  intro a b hab
  have hmem : (a : C)⁻¹ * (b : C) ∈ zpowers g := by
    have h := QuotientGroup.eq.mp (show (QuotientGroup.mk (a : C) : C ⧸ zpowers g)
        = QuotientGroup.mk (b : C) from hab)
    simpa using h
  have hHmem : (a : C)⁻¹ * (b : C) ∈ H := H.mul_mem (H.inv_mem a.2) b.2
  have hone : (a : C)⁻¹ * (b : C) = 1 := by
    have hbot : (a : C)⁻¹ * (b : C) ∈ H ⊓ zpowers g := Subgroup.mem_inf.mpr ⟨hHmem, hmem⟩
    rw [hH] at hbot
    exact Subgroup.mem_bot.mp hbot
  exact Subtype.ext (inv_mul_eq_one.mp hone)

private lemma equiv_map_of_inf_bot {H : Subgroup C} (hH : H ⊓ zpowers g = ⊥) :
    Nonempty (↥H ≃* ↥(H.map (QuotientGroup.mk' (zpowers g)))) := by
  have hinj := mk'_injective_of_inf_bot hH
  refine ⟨MulEquiv.ofBijective
    (((QuotientGroup.mk' (zpowers g)).comp H.subtype).codRestrict
      (H.map (QuotientGroup.mk' (zpowers g))) fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun y => ?_⟩⟩
  obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp y.2
  exact ⟨⟨a, ha⟩, Subtype.ext hay⟩

private lemma mk_mem_zpowers_of_mem_closure {v : C} (hv : v ∈ closure ({g, t} : Set C)) :
    QuotientGroup.mk v ∈ zpowers (QuotientGroup.mk t : C ⧸ zpowers g) := by
  refine Subgroup.closure_induction (p := fun w _ =>
    QuotientGroup.mk w ∈ zpowers (QuotientGroup.mk t : C ⧸ zpowers g)) ?_ ?_ ?_ ?_ hv
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with hxg | hx
    · rw [hxg]
      rw [show (QuotientGroup.mk g : C ⧸ zpowers g) = 1 from by
        rw [QuotientGroup.eq_one_iff]; exact Subgroup.mem_zpowers g]
      exact Subgroup.one_mem _
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Subgroup.mem_zpowers _
  · exact Subgroup.one_mem _
  · intro a b _ _ ha hb
    rw [QuotientGroup.mk_mul]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [QuotientGroup.mk_inv]
    exact Subgroup.inv_mem _ ha

theorem y6f4a_mem_cent_of_mk (hd : Y6CData g t P M) {x : C}
    (hx : (QuotientGroup.mk x : C ⧸ zpowers g) ∈
      centralizer ({(QuotientGroup.mk t : C ⧸ zpowers g)} : Set (C ⧸ zpowers g))) :
    x ∈ centralizer ({t} : Set C) := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hd.t_order] at h
    simpa [pow_two] using h
  have htinv : t⁻¹ = t := by
    calc t⁻¹ = t⁻¹ * 1 := by rw [mul_one]
      _ = t⁻¹ * (t * t) := by rw [ht2]
      _ = t := by group
  have hcomm : (QuotientGroup.mk x : C ⧸ zpowers g) * QuotientGroup.mk t
      = QuotientGroup.mk t * QuotientGroup.mk x :=
    (Subgroup.mem_centralizer_iff.mp hx (QuotientGroup.mk t) (Set.mem_singleton _)).symm
  have hq : (QuotientGroup.mk (x * t * x⁻¹) : C ⧸ zpowers g) = QuotientGroup.mk t := by
    have h1 : (QuotientGroup.mk (x * t * x⁻¹) : C ⧸ zpowers g)
        = QuotientGroup.mk x * QuotientGroup.mk t * (QuotientGroup.mk x)⁻¹ := by
      simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    rw [h1, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hzmem : x * t * x⁻¹ * t ∈ zpowers g := by
    have h := QuotientGroup.eq_iff_div_mem.mp hq
    rwa [div_eq_mul_inv, htinv] at h
  rcases zpowers_eq_one_or_self_of_orderOf hd.g_order (x * t * x⁻¹ * t) hzmem with hz | hz
  · have hxt : x * t * x⁻¹ = t := by
      have h := congrArg (fun w => w * t) hz
      simpa [mul_assoc, ht2] using h
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc t * x = (x * t * x⁻¹) * x := by rw [hxt]
      _ = x * t := by group
  · have hxt : x * t * x⁻¹ = g * t := by
      have h := congrArg (fun w => w * t) hz
      simpa [mul_assoc, ht2] using h
    exact absurd hxt (hd.no_conj x)

theorem y6f4a_V_comm_P (hd : Y6CData g t P M) {p v : C} (hp : p ∈ P)
    (hv : v ∈ closure ({g, t} : Set C)) : p * v = v * p := by
  have hPle : P ≤ centralizer ({t} : Set C) := by
    rw [hd.D_eq]
    exact le_sup_left
  have hpt : t * p = p * t := Subgroup.mem_centralizer_iff.mp (hPle hp) t (Set.mem_singleton t)
  have hpg : p * g = g * p := Subgroup.mem_center_iff.mp hd.g_central p
  have hcomm : ∀ w ∈ closure ({g, t} : Set C), Commute p w := by
    intro w hw
    refine Subgroup.closure_induction (p := fun w _ => Commute p w) ?_ ?_ ?_ ?_ hw
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hpg
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hpt.symm
    · exact Commute.one_right p
    · intro a b _ _ ha hb
      exact ha.mul_right hb
    · intro a _ ha
      exact Commute.inv_right_iff.mpr ha
  exact hcomm v hv

theorem y6f4a_decomp (hd : Y6CData g t P M) {x : C} (hx : x ∈ centralizer ({t} : Set C)) :
    ∃ p ∈ P, ∃ v ∈ closure ({g, t} : Set C), x = p * v := by
  have hx' : x ∈ P ⊔ closure ({g, t} : Set C) := by
    rw [← hd.D_eq]
    exact hx
  rw [Subgroup.sup_eq_closure] at hx'
  refine Subgroup.closure_induction (p := fun y _ =>
    ∃ q ∈ P, ∃ v ∈ closure ({g, t} : Set C), y = q * v) ?_ ?_ ?_ ?_ hx'
  · intro y hy
    rw [Set.mem_union] at hy
    rcases hy with hyP | hyV
    · exact ⟨y, hyP, 1, Subgroup.one_mem _, by simp⟩
    · exact ⟨1, P.one_mem, y, hyV, by simp⟩
  · exact ⟨1, P.one_mem, 1, Subgroup.one_mem _, by simp⟩
  · intro a b _ _ ha hb
    obtain ⟨pa, hpa, va, hva, rfl⟩ := ha
    obtain ⟨pb, hpb, vb, hvb, rfl⟩ := hb
    refine ⟨pa * pb, P.mul_mem hpa hpb, va * vb, Subgroup.mul_mem _ hva hvb, ?_⟩
    have hvpa : va * pb = pb * va := (y6f4a_V_comm_P hd hpb hva).symm
    calc pa * va * (pb * vb) = pa * (va * pb) * vb := by group
      _ = pa * (pb * va) * vb := by rw [hvpa]
      _ = pa * pb * (va * vb) := by group
  · intro a _ ha
    obtain ⟨pa, hpa, va, hva, rfl⟩ := ha
    refine ⟨pa⁻¹, P.inv_mem hpa, va⁻¹, Subgroup.inv_mem _ hva, ?_⟩
    have hvpa : pa * va = va * pa := y6f4a_V_comm_P hd hpa hva
    calc (pa * va)⁻¹ = (va * pa)⁻¹ := by rw [hvpa]
      _ = pa⁻¹ * va⁻¹ := by group

theorem y6f4a_equiv_map_of_le_P (hd : Y6CData g t P M) {J : Subgroup C} (hJ : J ≤ P) :
    Nonempty (↥J ≃* ↥(J.map (QuotientGroup.mk' (zpowers g)))) := by
  have hbot : J ⊓ zpowers g = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    obtain ⟨hzJ, hzg⟩ := Subgroup.mem_inf.mp hz
    have hzV : z ∈ closure ({g, t} : Set C) := zpowers_le_closure_pair hzg
    have hmem : z ∈ P ⊓ closure ({g, t} : Set C) :=
      Subgroup.mem_inf.mpr ⟨hJ hzJ, hzV⟩
    rw [hd.P_inf] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact equiv_map_of_inf_bot hbot

theorem y6f4a_equiv_map_M (hd : Y6CData g t P M) :
    Nonempty (↥M ≃* ↥(M.map (QuotientGroup.mk' (zpowers g)))) := by
  have hbot : M ⊓ zpowers g = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    obtain ⟨hzM, hzg⟩ := Subgroup.mem_inf.mp hz
    rcases zpowers_eq_one_or_self_of_orderOf hd.g_order z hzg with h | h
    · rw [h]
      exact Subgroup.mem_bot.mpr rfl
    · exact absurd (h ▸ hzM) hd.g_not_mem_M
  exact equiv_map_of_inf_bot hbot

theorem y6f4a_J_norm (hd : Y6CData g t P M) {J : Subgroup C} (hJP : J ≤ P)
    (hJn : ∀ x ∈ P, ∀ j ∈ J, x * j * x⁻¹ ∈ J) :
    centralizer ({(QuotientGroup.mk t : C ⧸ zpowers g)} : Set (C ⧸ zpowers g)) ≤
      normalizer ((J.map (QuotientGroup.mk' (zpowers g)) : Subgroup (C ⧸ zpowers g)) :
        Set (C ⧸ zpowers g)) := by
  have hmain : ∀ c : C, c ∈ centralizer ({t} : Set C) →
      ∀ z ∈ (J.map (QuotientGroup.mk' (zpowers g)) : Subgroup (C ⧸ zpowers g)),
        QuotientGroup.mk c * z * (QuotientGroup.mk c)⁻¹ ∈
          J.map (QuotientGroup.mk' (zpowers g)) := by
    intro c hc z hz
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨p, hp, v, hv, rfl⟩ := y6f4a_decomp hd hc
    have hvj : v * j = j * v := (y6f4a_V_comm_P hd (hJP hj) hv).symm
    have hconj : (p * v) * j * (p * v)⁻¹ = p * j * p⁻¹ := by
      calc (p * v) * j * (p * v)⁻¹ = p * (v * j) * v⁻¹ * p⁻¹ := by group
        _ = p * (j * v) * v⁻¹ * p⁻¹ := by rw [hvj]
        _ = p * j * p⁻¹ := by group
    have hmemJ : p * j * p⁻¹ ∈ J := hJn p hp j hj
    refine Subgroup.mem_map.mpr ⟨p * j * p⁻¹, hmemJ, ?_⟩
    rw [← hconj]
    simp
  intro y hy
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
  have hc : c ∈ centralizer ({t} : Set C) := y6f4a_mem_cent_of_mk hd hy
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact hmain c hc z
  · intro hz
    have hz' := hmain c⁻¹ (Subgroup.inv_mem _ hc)
      (QuotientGroup.mk c * z * (QuotientGroup.mk c)⁻¹) hz
    have hceq : (QuotientGroup.mk c⁻¹ : C ⧸ zpowers g) = (QuotientGroup.mk c)⁻¹ := by simp
    rw [hceq] at hz'
    convert hz' using 1
    group

theorem y6f4a_J_cent (hd : Y6CData g t P M) {J : Subgroup C} (hJP : J ≤ P)
    (hJn : ∀ x ∈ P, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hJc : ∀ x ∈ P, (∀ j ∈ J, x * j = j * x) → x = 1) :
    centralizer ((J.map (QuotientGroup.mk' (zpowers g)) : Subgroup (C ⧸ zpowers g)) :
        Set (C ⧸ zpowers g)) ⊓
      centralizer ({(QuotientGroup.mk t : C ⧸ zpowers g)} : Set (C ⧸ zpowers g)) =
      zpowers (QuotientGroup.mk t : C ⧸ zpowers g) := by
  have hPle : P ≤ centralizer ({t} : Set C) := by
    rw [hd.D_eq]
    exact le_sup_left
  have ht_cent : (QuotientGroup.mk t : C ⧸ zpowers g) ∈
      centralizer ((J.map (QuotientGroup.mk' (zpowers g)) : Subgroup (C ⧸ zpowers g)) :
        Set (C ⧸ zpowers g)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hz
    have htj : t * j = j * t :=
      Subgroup.mem_centralizer_iff.mp (hPle (hJP hj)) t (Set.mem_singleton t)
    show QuotientGroup.mk j * QuotientGroup.mk t = QuotientGroup.mk t * QuotientGroup.mk j
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, htj]
  have ht_self : (QuotientGroup.mk t : C ⧸ zpowers g) ∈
      centralizer ({(QuotientGroup.mk t : C ⧸ zpowers g)} : Set (C ⧸ zpowers g)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rfl
  apply le_antisymm
  · intro y hy
    obtain ⟨hyH, hyτ⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
    have hc : c ∈ centralizer ({t} : Set C) := y6f4a_mem_cent_of_mk hd hyτ
    obtain ⟨p, hp, v, hv, rfl⟩ := y6f4a_decomp hd hc
    have hkey : ∀ j ∈ J, p * j * p⁻¹ * j⁻¹ = 1 := by
      intro j hj
      have hcomm : (QuotientGroup.mk (p * v) : C ⧸ zpowers g) * QuotientGroup.mk j
          = QuotientGroup.mk j * QuotientGroup.mk (p * v) :=
        (Subgroup.mem_centralizer_iff.mp hyH (QuotientGroup.mk j)
          (Subgroup.mem_map.mpr ⟨j, hj, rfl⟩)).symm
      have hq : (QuotientGroup.mk ((p * v) * j * (p * v)⁻¹ * j⁻¹) :
          C ⧸ zpowers g) = 1 := by
        rw [show (QuotientGroup.mk ((p * v) * j * (p * v)⁻¹ * j⁻¹) : C ⧸ zpowers g)
            = QuotientGroup.mk (p * v) * QuotientGroup.mk j * (QuotientGroup.mk (p * v))⁻¹
              * (QuotientGroup.mk j)⁻¹ from by simp]
        rw [hcomm]
        group
      have hzN : (p * v) * j * (p * v)⁻¹ * j⁻¹ ∈ zpowers g :=
        (QuotientGroup.eq_one_iff _).mp hq
      have hvj : v * j = j * v := (y6f4a_V_comm_P hd (hJP hj) hv).symm
      have heq : (p * v) * j * (p * v)⁻¹ * j⁻¹ = p * j * p⁻¹ * j⁻¹ := by
        calc (p * v) * j * (p * v)⁻¹ * j⁻¹ = p * (v * j) * v⁻¹ * p⁻¹ * j⁻¹ := by group
          _ = p * (j * v) * v⁻¹ * p⁻¹ * j⁻¹ := by rw [hvj]
          _ = p * j * p⁻¹ * j⁻¹ := by group
      have hzN' : p * j * p⁻¹ * j⁻¹ ∈ zpowers g := by
        rw [← heq]
        exact hzN
      have hmemJ : p * j * p⁻¹ * j⁻¹ ∈ J := J.mul_mem (hJn p hp j hj) (J.inv_mem hj)
      have hV : p * j * p⁻¹ * j⁻¹ ∈ closure ({g, t} : Set C) :=
        zpowers_le_closure_pair hzN'
      have hinf : p * j * p⁻¹ * j⁻¹ ∈ P ⊓ closure ({g, t} : Set C) :=
        Subgroup.mem_inf.mpr ⟨hJP hmemJ, hV⟩
      rw [hd.P_inf] at hinf
      exact Subgroup.mem_bot.mp hinf
    have hp1 : p = 1 := by
      refine hJc p hp fun j hj => ?_
      have h2 : p * j * p⁻¹ = j := by
        have h := congrArg (fun w => w * j) (hkey j hj)
        simpa [mul_assoc] using h
      calc p * j = (p * j * p⁻¹) * p := by group
        _ = j * p := by rw [h2]
    have hcv : p * v = v := by rw [hp1, one_mul]
    rw [hcv]
    exact mk_mem_zpowers_of_mem_closure hv
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨ht_cent, ht_self⟩)

end CFSG.OddStandard.HigherRank.YamadaG23
