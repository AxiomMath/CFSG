module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5CentHA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Dihed

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y53_mem_H_iff {c : Ctx5 G L} {x : G} :
    x ∈ c.s.H ↔ x * c.s.t = c.s.t * x := by
  rw [Setting3.H, Subgroup.mem_centralizer_singleton_iff]

private lemma y53_d_inv (c : Ctx5 G L) : c.d⁻¹ = c.d := by
  have h : c.d * c.d = 1 := by
    rw [← pow_two]
    exact y5_d_sq c
  exact inv_eq_of_mul_eq_one_right h

private theorem y53_mem_Q {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {x : G}
    (hx : x ∈ (c.s.fr.A ⊔ zpowers c.s.t : Subgroup G)) :
    x ∈ c.s.fr.A ∨ ∃ a ∈ c.s.fr.A, x = a * c.s.t := by
  have htt : c.s.t * c.s.t = 1 := by
    rw [← pow_two, ← c.s.t_order]
    exact pow_orderOf_eq_one c.s.t
  rw [show (c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) =
      Subgroup.closure ((c.s.fr.A : Set G) ∪ (Subgroup.zpowers c.s.t : Set G)) from
    Subgroup.sup_eq_closure _ _] at hx
  refine Subgroup.closure_induction (p := fun x _ =>
    x ∈ c.s.fr.A ∨ ∃ a ∈ c.s.fr.A, x = a * c.s.t) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hy | hy
    · exact Or.inl hy
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rcases Int.emod_two_eq_zero_or_one n with h2 | h2
      · left
        have h2' : n % ((2 : ℕ) : ℤ) = 0 := h2
        rw [show c.s.t ^ n = 1 by rw [← zpow_mod_orderOf c.s.t n, c.s.t_order, h2']; simp]
        exact c.s.fr.A.one_mem
      · right
        refine ⟨1, c.s.fr.A.one_mem, ?_⟩
        have h2' : n % ((2 : ℕ) : ℤ) = 1 := h2
        rw [show c.s.t ^ n = c.s.t by rw [← zpow_mod_orderOf c.s.t n, c.s.t_order, h2']; simp,
          one_mul]
  · exact Or.inl c.s.fr.A.one_mem
  · intro u v _ _ hu hv
    rcases hu with hu | ⟨a, ha, rfl⟩
    · rcases hv with hv | ⟨b, hb, rfl⟩
      · exact Or.inl (c.s.fr.A.mul_mem hu hv)
      · exact Or.inr ⟨u * b, c.s.fr.A.mul_mem hu hb, by group⟩
    · rcases hv with hv | ⟨b, hb, rfl⟩
      · refine Or.inr ⟨a * v, c.s.fr.A.mul_mem ha hv, ?_⟩
        calc a * c.s.t * v = a * (c.s.t * v) := by group
          _ = a * (v * c.s.t) := by rw [← s3_comm_t_of_mem_A c.s hv]
          _ = a * v * c.s.t := by group
      · refine Or.inl ?_
        rw [show a * c.s.t * (b * c.s.t) = a * b by
          calc a * c.s.t * (b * c.s.t) = a * (c.s.t * b) * c.s.t := by group
            _ = a * (b * c.s.t) * c.s.t := by rw [← s3_comm_t_of_mem_A c.s hb]
            _ = a * b * (c.s.t * c.s.t) := by group
            _ = a * b := by rw [htt, mul_one]]
        exact c.s.fr.A.mul_mem ha hb
  · intro u _ hu
    rcases hu with hu | ⟨a, ha, rfl⟩
    · exact Or.inl (c.s.fr.A.inv_mem hu)
    · refine Or.inr ⟨a⁻¹, c.s.fr.A.inv_mem ha, ?_⟩
      have hta : c.s.t * a⁻¹ = a⁻¹ * c.s.t :=
        (s3_comm_t_of_mem_A c.s (c.s.fr.A.inv_mem ha)).symm
      calc (a * c.s.t)⁻¹ = c.s.t⁻¹ * a⁻¹ := mul_inv_rev a c.s.t
        _ = c.s.t * a⁻¹ := by rw [inv_eq_of_mul_eq_one_right htt]
        _ = a⁻¹ * c.s.t := hta

private theorem y53_Q_inf_L {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    (c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) ⊓ L = c.s.fr.A := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxQ, hxL⟩ := Subgroup.mem_inf.mp hx
    rcases y53_mem_Q hH hxQ with h | ⟨a, ha, rfl⟩
    · exact h
    · exfalso
      apply s3_t_not_mem_L c.s hH.h31
      have heq : c.s.t = a⁻¹ * (a * c.s.t) := by group
      rw [heq]
      exact L.mul_mem (L.inv_mem (s3_A_le_L c.s ha)) hxL
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hx, s3_A_le_L c.s hx⟩

private theorem y53_t_cent_Q {c : Ctx5 G L} :
    c.s.t ∈ Subgroup.centralizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) := by
  have hQle : (c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) ≤
      Subgroup.centralizer (Subgroup.zpowers c.s.t : Set G) := by
    rw [Subgroup.sup_eq_closure]
    refine (Subgroup.closure_le (Subgroup.centralizer (Subgroup.zpowers c.s.t : Set G))).mpr ?_
    intro x hx
    rw [Set.mem_union] at hx
    rcases hx with hxA | hxt
    · change x ∈ Subgroup.centralizer (Subgroup.zpowers c.s.t : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((show Commute x c.s.t from s3_comm_t_of_mem_A c.s hxA).zpow_right i).symm
    · exact Subgroup.le_centralizer (Subgroup.zpowers c.s.t) hxt
  exact (Subgroup.le_centralizer_iff.mp hQle) (Subgroup.mem_zpowers c.s.t)

private theorem y53_cen_Q_le {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    cen (c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) ≤ zt c.s := by
  have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
  have htC : c.s.t ∈ Subgroup.centralizer (c.s.fr.A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact s3_comm_t_of_mem_A c.s hx
  intro w hw
  obtain ⟨hwQ, hwC⟩ := Subgroup.mem_inf.mp hw
  have hwCA : w ∈ Subgroup.centralizer (c.s.fr.A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp hwC a (Subgroup.mem_sup_left ha)
  rcases y53_mem_Q hH hwQ with hwA | ⟨a, haA, rfl⟩
  · have hwZ : w ∈ c.s.fr.Z := by
      have hmem : w ∈ cen c.s.fr.A := Subgroup.mem_inf.mpr ⟨hwA, hwCA⟩
      rwa [hA.cen_A] at hmem
    rw [SFrame.Z] at hwZ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hwZ
    rw [← hj]
    exact Subgroup.zpow_mem (zt c.s) (Subgroup.subset_closure (by simp)) j
  · have haCA : a ∈ Subgroup.centralizer (c.s.fr.A : Set G) := by
      have htinv : c.s.t⁻¹ ∈ Subgroup.centralizer (c.s.fr.A : Set G) := Subgroup.inv_mem _ htC
      have heq : a = (a * c.s.t) * c.s.t⁻¹ := by group
      rw [heq]
      exact Subgroup.mul_mem _ hwCA htinv
    have haZ : a ∈ c.s.fr.Z := by
      have hmem : a ∈ cen c.s.fr.A := Subgroup.mem_inf.mpr ⟨haA, haCA⟩
      rwa [hA.cen_A] at hmem
    rw [SFrame.Z] at haZ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp haZ
    rw [← hj]
    exact Subgroup.mul_mem (zt c.s)
      (Subgroup.zpow_mem (zt c.s) (Subgroup.subset_closure (by simp)) j)
      (Subgroup.subset_closure (by simp))

private theorem y53_conj_t_mem {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {x : G}
    (hx : x ∈ Subgroup.normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G)) :
    x * c.s.t * x⁻¹ = c.s.t ∨ x * c.s.t * x⁻¹ = c.s.fr.z * c.s.t := by
  have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
  let Q : Subgroup G := c.s.fr.A ⊔ zpowers c.s.t
  have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := hx
  have htQ : c.s.t ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)
  have hxtQ : x * c.s.t * x⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hxQ c.s.t).mp htQ
  have htcentQ : c.s.t ∈ Subgroup.centralizer (Q : Set G) := y53_t_cent_Q (c := c)
  have huC : x * c.s.t * x⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : x⁻¹ * y * x ∈ Q := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxQ) y).mp hy
      simpa using h
    have htz : c.s.t * (x⁻¹ * y * x) = (x⁻¹ * y * x) * c.s.t :=
      (Subgroup.mem_centralizer_iff.mp htcentQ (x⁻¹ * y * x) hy').symm
    calc y * (x * c.s.t * x⁻¹)
        = x * ((x⁻¹ * y * x) * c.s.t) * x⁻¹ := by group
      _ = x * (c.s.t * (x⁻¹ * y * x)) * x⁻¹ := by rw [htz.symm]
      _ = (x * c.s.t * x⁻¹) * y := by group
  have hu : x * c.s.t * x⁻¹ ∈ cen Q := Subgroup.mem_inf.mpr ⟨hxtQ, huC⟩
  have hzt : x * c.s.t * x⁻¹ ∈ zt c.s := y53_cen_Q_le (c := c) hH hu
  rcases (s3_mem_zt_iff c.s hA).mp hzt with h1 | hz | ht | hzt'
  · exfalso
    have ht1 : c.s.t = 1 := by
      calc c.s.t = x⁻¹ * (x * c.s.t * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group
    have hord := c.s.t_order
    rw [ht1, orderOf_one] at hord
    norm_num at hord
  · exfalso
    exact hH.h31.2.2.1 x (hz ▸ s3_z_mem_L c.s)
  · exact Or.inl ht
  · exact Or.inr hzt'

private theorem y53_mem_normalizer_A {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {x : G}
    (hxQ : x ∈ Subgroup.normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G))
    (hxH : x ∈ c.s.H) : x ∈ Subgroup.normalizer (c.s.fr.A : Set G) := by
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := s3_H_le_N c.s hH.hS hxH
  have hxinf := Subgroup.inf_normalizer_le_normalizer_inf
    (H := (c.s.fr.A ⊔ zpowers c.s.t : Subgroup G)) (K := L)
    (Subgroup.mem_inf.mpr ⟨hxQ, hxL⟩)
  rwa [y53_Q_inf_L hH] at hxinf

private theorem y53_d_centralizer_A {c : Ctx5 G L} :
    c.d ∈ Subgroup.centralizer (c.s.fr.A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hd : c.d * a * c.d = a := by
    simpa [y53_d_inv c] using y5_d_cent_A c a ha
  have hd2 : c.d * c.d = 1 := by rw [← pow_two]; exact y5_d_sq c
  have hda : c.d * a = a * c.d := by
    calc c.d * a = c.d * a * (c.d * c.d) := by rw [hd2, mul_one]
      _ = (c.d * a * c.d) * c.d := by group
      _ = a * c.d := by rw [hd]
  exact hda.symm

private theorem y53_d_normalizes_A {c : Ctx5 G L} :
    c.d ∈ Subgroup.normalizer (c.s.fr.A : Set G) :=
  Subgroup.centralizer_le_normalizer (c.s.fr.A : Set G) (y53_d_centralizer_A (c := c))

private theorem y53_d_normalizes_Q {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    c.d ∈ Subgroup.normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) := by
  have hdA := y53_d_normalizes_A (c := c)
  have hAmap : c.s.fr.A.map (MulAut.conj c.d : G →* G) = c.s.fr.A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hdA
  have hztQ : c.s.fr.z * c.s.t ∈ (c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) :=
    Subgroup.mul_mem _
      (Subgroup.mem_sup_left (s3_z_mem_A c.s))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t))
  have hconjt : MulAut.conj c.d c.s.t = c.s.fr.z * c.s.t := by
    rw [MulAut.conj_apply]
    simpa [y53_d_inv c] using y5_dtd hH
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.map_sup, hAmap, MonoidHom.map_zpowers]
    exact sup_le le_sup_left (Subgroup.zpowers_le.mpr (by simpa [hconjt] using hztQ))
  · exact le_of_eq (Subgroup.card_map_of_injective (f := (MulAut.conj c.d : G →* G))
      (MulAut.conj c.d).injective).symm

private theorem y53_normIn_le_N {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    normIn c.s.H c.s.fr.A ≤
      Subgroup.normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨hxH, hxA⟩ := Subgroup.mem_inf.mp hx
  have hxHt : x * c.s.t = c.s.t * x := y53_mem_H_iff.mp hxH
  have hAmap : c.s.fr.A.map (MulAut.conj x : G →* G) = c.s.fr.A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hxA
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, hAmap, MonoidHom.map_zpowers]
  have hconj : MulAut.conj x c.s.t = c.s.t := by
    rw [MulAut.conj_apply]
    calc x * c.s.t * x⁻¹ = (x * c.s.t) * x⁻¹ := rfl
      _ = (c.s.t * x) * x⁻¹ := by rw [hxHt]
      _ = c.s.t := by group
  simpa [hconj]

private theorem y53_dinv_mul_mem_H {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {x : G}
    (hx : x * c.s.t * x⁻¹ = c.s.fr.z * c.s.t) : c.d⁻¹ * x ∈ c.s.H := by
  have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
  have hz2 : c.s.fr.z * c.s.fr.z = 1 := by
    rw [← pow_two, ← s3_z_order c.s hA]
    exact pow_orderOf_eq_one c.s.fr.z
  have hdzd : c.d⁻¹ * c.s.fr.z * c.d = c.s.fr.z := by
    simpa [y53_d_inv c] using y5_dz hH
  have hdtd : c.d⁻¹ * c.s.t * c.d = c.s.fr.z * c.s.t := by
    simpa [y53_d_inv c] using y5_dtd hH
  rw [y53_mem_H_iff]
  have hconj : (c.d⁻¹ * x) * c.s.t * (c.d⁻¹ * x)⁻¹ = c.s.t := by
    calc (c.d⁻¹ * x) * c.s.t * (c.d⁻¹ * x)⁻¹
        = c.d⁻¹ * (x * c.s.t * x⁻¹) * c.d := by group
      _ = c.d⁻¹ * (c.s.fr.z * c.s.t) * c.d := by rw [hx]
      _ = (c.d⁻¹ * c.s.fr.z * c.d) * (c.d⁻¹ * c.s.t * c.d) := by group
      _ = c.s.fr.z * (c.s.fr.z * c.s.t) := by rw [hdzd, hdtd]
      _ = c.s.t := by rw [← mul_assoc, hz2, one_mul]
  calc (c.d⁻¹ * x) * c.s.t = ((c.d⁻¹ * x) * c.s.t * (c.d⁻¹ * x)⁻¹) * (c.d⁻¹ * x) := by group
    _ = c.s.t * (c.d⁻¹ * x) := by rw [hconj]

theorem y5_normN_Aqt {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) =
      normIn c.s.H c.s.fr.A ⊔ zpowers c.d := by
  apply le_antisymm
  · intro x hx
    rcases y53_conj_t_mem hH hx with ht | hzt
    · have hxH : x ∈ c.s.H := by
        rw [y53_mem_H_iff]
        calc x * c.s.t = (x * c.s.t * x⁻¹) * x := by group
          _ = c.s.t * x := by rw [ht]
      have hxA : x ∈ Subgroup.normalizer (c.s.fr.A : Set G) :=
        y53_mem_normalizer_A hH hx hxH
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hxH, hxA⟩)
    · have hyH : c.d⁻¹ * x ∈ c.s.H := y53_dinv_mul_mem_H hH hzt
      have hyQ : c.d⁻¹ * x ∈
          Subgroup.normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (y53_d_normalizes_Q hH)) hx
      have hyA : c.d⁻¹ * x ∈ Subgroup.normalizer (c.s.fr.A : Set G) :=
        y53_mem_normalizer_A hH hyQ hyH
      have hy : c.d⁻¹ * x ∈ normIn c.s.H c.s.fr.A := Subgroup.mem_inf.mpr ⟨hyH, hyA⟩
      have hxeq : x = c.d * (c.d⁻¹ * x) := by group
      rw [hxeq]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.d))
        (Subgroup.mem_sup_left hy)
  · exact sup_le (y53_normIn_le_N hH)
      (Subgroup.zpowers_le.mpr (y53_d_normalizes_Q hH))

theorem y5_C0_eq_cent {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    C0 c.e = centIn (normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G)) c.s.fr.A := by
  apply le_antisymm
  · intro x hx
    have hsup : C0 c.e ≤ normIn c.s.H c.s.fr.A ⊔ zpowers c.d := by
      rw [c.intro5.gen]
      refine (Subgroup.closure_le (normIn c.s.H c.s.fr.A ⊔ zpowers c.d)).mpr ?_
      intro u hu
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · refine Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
        · rw [y53_mem_H_iff]
        · exact Subgroup.centralizer_le_normalizer (c.s.fr.A : Set G) (by
            rw [Subgroup.mem_centralizer_iff]
            intro a ha
            exact s3_comm_t_of_mem_A c.s ha)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.d)
    refine Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_inf.mp hx).2⟩
    rw [y5_normN_Aqt hH]
    exact hsup hx
  · intro x hx
    obtain ⟨hxN, hxA⟩ := Subgroup.mem_inf.mp hx
    have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
    rcases y53_conj_t_mem hH hxN with ht | hzt
    · have hxH : x ∈ c.s.H := by
        rw [y53_mem_H_iff]
        calc x * c.s.t = (x * c.s.t * x⁻¹) * x := by group
          _ = c.s.t * x := by rw [ht]
      have hHA : x ∈ centIn c.s.H c.s.fr.A := Subgroup.mem_inf.mpr ⟨hxH, hxA⟩
      rw [y5_centHA (s := c.s) (e := c.e) hH] at hHA
      exact s3_zt_le_C0 c.s hA c.e hHA
    · have hyH : c.d⁻¹ * x ∈ c.s.H := y53_dinv_mul_mem_H hH hzt
      have hdcent : c.d⁻¹ ∈ Subgroup.centralizer (c.s.fr.A : Set G) := by
        simpa [y53_d_inv c] using y53_d_centralizer_A (c := c)
      have hyA : c.d⁻¹ * x ∈ Subgroup.centralizer (c.s.fr.A : Set G) :=
        Subgroup.mul_mem _ hdcent hxA
      have hyHA : c.d⁻¹ * x ∈ centIn c.s.H c.s.fr.A := Subgroup.mem_inf.mpr ⟨hyH, hyA⟩
      rw [y5_centHA (s := c.s) (e := c.e) hH] at hyHA
      have hxeq : x = c.d * (c.d⁻¹ * x) := by group
      rw [hxeq]
      exact Subgroup.mul_mem (C0 c.e) c.d_mem (s3_zt_le_C0 c.s hA c.e hyHA)

theorem y5_normN_C0 {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    normIn c.s.H c.s.fr.A ⊔ zpowers c.d ≤ normalizer (C0 c.e : Set G) := by
  rw [y5_C0_eq_cent hH, Subgroup.le_normalizer_iff]
  have hN : normIn c.s.H c.s.fr.A ⊔ zpowers c.d ≤
      Subgroup.normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) :=
    (y5_normN_Aqt hH).ge
  have hNA : normIn c.s.H c.s.fr.A ⊔ zpowers c.d ≤
      Subgroup.normalizer (c.s.fr.A : Set G) := by
    refine sup_le inf_le_right ?_
    exact Subgroup.zpowers_le.mpr (y53_d_normalizes_A (c := c))
  intro x hx y hy
  have hxN : x ∈ Subgroup.normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) :=
    hN hx
  have hxNA : x ∈ Subgroup.normalizer (c.s.fr.A : Set G) := hNA hx
  obtain ⟨hyN, hyC⟩ := Subgroup.mem_inf.mp hy
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hyN) (Subgroup.inv_mem _ hxN)
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : x⁻¹ * a * x ∈ c.s.fr.A := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxNA) a).mp ha
      simpa using h
    have hya : (x⁻¹ * a * x) * y = y * (x⁻¹ * a * x) :=
      Subgroup.mem_centralizer_iff.mp hyC _ ha'
    calc a * (x * y * x⁻¹) = x * ((x⁻¹ * a * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * a * x)) * x⁻¹ := by rw [hya]
      _ = (x * y * x⁻¹) * a := by group

end CFSG.OddStandard.HigherRank.YamadaG23
