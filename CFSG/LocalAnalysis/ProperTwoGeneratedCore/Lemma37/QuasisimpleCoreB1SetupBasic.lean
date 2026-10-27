module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePB1Char
public import CFSG.Dihedral.DisconnectedInvolutionGraph.SylowNormalizerControl
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePSetup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {u : J}

structure CaseB1 (Q : Sylow 2 J) (B : Subgroup J) (T : Sylow 2 (quasiNormalizer u))
    (L : Subgroup (QuasiQuotient u)) (M : ℕ) : Prop where
  setting : Setting J Q B
  le_subgroupOf : (T : Subgroup (quasiNormalizer u)) ≤ B.subgroupOf (quasiNormalizer u)
  normal : L.Normal
  partC : PartC (partCSylow T) (partCLeft T L) (partCRight T L) (centralElt J) u
  le_sup : partCSylow T ≤ partCLeft T L ⊔ partCRight T L
  four_dvd : 4 ∣ M
  ne_zero : M ≠ 0
  quaternion : Nonempty (partCRight T L ≃* QuaternionGroup M)

theorem Setting.caseB1 (h : Setting J Q B) (T : Sylow 2 (quasiNormalizer u))
    (hTB : (T : Subgroup (quasiNormalizer u)) ≤ B.subgroupOf (quasiNormalizer u))
    {L : Subgroup (QuasiQuotient u)} (hLn : L.Normal)
    (hc : PartC (partCSylow T) (partCLeft T L) (partCRight T L) (centralElt J) u)
    (hT : partCSylow T ≤ partCLeft T L ⊔ partCRight T L) {n : ℕ} (hn : 4 ≤ n)
    (hφ : Nonempty (partCRight T L ≃* QuaternionGroup (2 ^ (n - 2)))) :
    CaseB1 Q B T L (2 ^ (n - 2)) :=
  ⟨h, hTB, hLn, hc, hT, by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 (by omega), by positivity, hφ⟩

omit [Finite J] in
abbrev b1Bar (B : Subgroup J) : Subgroup (J ⧸ Subgroup.center J) :=
  B.map (QuotientGroup.mk' (Subgroup.center J))

omit [Finite J] in
abbrev b1S (T : Sylow 2 (quasiNormalizer u)) : Subgroup (J ⧸ Subgroup.center J) :=
  (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J))

omit [Finite J] in
abbrev b1X (T : Sylow 2 (quasiNormalizer u)) (L : Subgroup (QuasiQuotient u)) :
    Subgroup (J ⧸ Subgroup.center J) :=
  (partCLeft T L).map (QuotientGroup.mk' (Subgroup.center J))

omit [Finite J] in
abbrev b1D (T : Sylow 2 (quasiNormalizer u)) (L : Subgroup (QuasiQuotient u)) :
    Subgroup (J ⧸ Subgroup.center J) :=
  (partCRight T L).map (QuotientGroup.mk' (Subgroup.center J))

omit [Finite J] in
theorem mk_mem_map_iff_of_center_le {H : Subgroup J} (hH : Subgroup.center J ≤ H) (x : J) :
    (x : J ⧸ Subgroup.center J) ∈ H.map (QuotientGroup.mk' (Subgroup.center J)) ↔ x ∈ H := by
  rw [← QuotientGroup.mk'_apply, ← Subgroup.mem_comap, Subgroup.comap_map_eq_self (by
    rw [QuotientGroup.ker_mk']
    exact hH)]

@[expose] def sylowOfCoeEq {p : ℕ} {G : Type*} [Group G] (P : Sylow p G) (H : Subgroup G)
    (h : (P : Subgroup G) = H) : Sylow p G where
  toSubgroup := H
  isPGroup' := by
    rw [← h]
    exact P.isPGroup'
  is_maximal' := fun {K} hK hHK => by
    rw [← h] at hHK ⊢
    exact P.is_maximal' hK hHK

namespace CaseB1

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {M : ℕ}

theorem four_le (hb : CaseB1 Q B T L M) : 4 ≤ M :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hb.ne_zero) hb.four_dvd

theorem even (hb : CaseB1 Q B T L M) : Even M :=
  even_iff_two_dvd.mpr ((dvd_mul_left 2 2).trans hb.four_dvd)

theorem partCSylow_le (hb : CaseB1 Q B T L M) : partCSylow T ≤ B :=
  Subgroup.map_le_iff_le_comap.mpr hb.le_subgroupOf

omit [Finite J] in
theorem partCSylow_le_quasiNormalizer : partCSylow T ≤ quasiNormalizer u :=
  Subgroup.map_subtype_le _

theorem normalizer_partCSylow_le (hb : CaseB1 Q B T L M) :
    Subgroup.normalizer (partCSylow T : Set J) ≤ quasiNormalizer u := by
  have : NeZero M := ⟨hb.ne_zero⟩
  exact hb.partC.normalizer_le_normalizer_zpowers hb.le_sup hb.four_dvd hb.quaternion.some
    partCSylow_le_quasiNormalizer

theorem exists_sylowJ (hb : CaseB1 Q B T L M) :
    ∃ P : Sylow 2 J, (P : Subgroup J) = partCSylow T := by
  obtain ⟨P, hP⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.sylow_inheritance_of_normalizer_le 2
    (quasiNormalizer u) T hb.normalizer_partCSylow_le
  exact ⟨P, hP.symm⟩

@[expose] noncomputable def sylowJ (hb : CaseB1 Q B T L M) : Sylow 2 J :=
  sylowOfCoeEq hb.exists_sylowJ.choose _ hb.exists_sylowJ.choose_spec

@[simp] theorem coe_sylowJ (hb : CaseB1 Q B T L M) : (hb.sylowJ : Subgroup J) = partCSylow T :=
  rfl

@[expose] noncomputable def sylow (hb : CaseB1 Q B T L M) : Sylow 2 (J ⧸ Subgroup.center J) :=
  sylowOfCoeEq (hb.sylowJ.mapSurjective (QuotientGroup.mk'_surjective _)) (b1S T)
    (by rw [Sylow.coe_mapSurjective, hb.coe_sylowJ])

@[simp] theorem coe_sylow (hb : CaseB1 Q B T L M) :
    (hb.sylow : Subgroup (J ⧸ Subgroup.center J)) = b1S T :=
  rfl

theorem center_le_partCLeft (hb : CaseB1 Q B T L M) : Subgroup.center J ≤ partCLeft T L := by
  intro x hx
  rcases hb.setting.mem_center_iff.mp hx with rfl | rfl
  · exact one_mem _
  · exact hb.partC.mem_left

theorem center_le_partCRight (hb : CaseB1 Q B T L M) : Subgroup.center J ≤ partCRight T L := by
  intro x hx
  rcases hb.setting.mem_center_iff.mp hx with rfl | rfl
  · exact one_mem _
  · exact hb.partC.mem_right

theorem center_le_partCSylow (hb : CaseB1 Q B T L M) : Subgroup.center J ≤ partCSylow T :=
  hb.center_le_partCLeft.trans hb.partC.left_le

theorem mk_mem_S_iff (hb : CaseB1 Q B T L M) (x : J) :
    (x : J ⧸ Subgroup.center J) ∈ b1S T ↔ x ∈ partCSylow T :=
  mk_mem_map_iff_of_center_le hb.center_le_partCSylow x

theorem mk_mem_X_iff (hb : CaseB1 Q B T L M) (x : J) :
    (x : J ⧸ Subgroup.center J) ∈ b1X T L ↔ x ∈ partCLeft T L :=
  mk_mem_map_iff_of_center_le hb.center_le_partCLeft x

theorem mk_mem_D_iff (hb : CaseB1 Q B T L M) (x : J) :
    (x : J ⧸ Subgroup.center J) ∈ b1D T L ↔ x ∈ partCRight T L :=
  mk_mem_map_iff_of_center_le hb.center_le_partCRight x

theorem S_le (hb : CaseB1 Q B T L M) : b1S T ≤ b1Bar B :=
  Subgroup.map_mono hb.partCSylow_le

theorem X_le_S (hb : CaseB1 Q B T L M) : b1X T L ≤ b1S T :=
  Subgroup.map_mono hb.partC.left_le

theorem D_le_S (hb : CaseB1 Q B T L M) : b1D T L ≤ b1S T :=
  Subgroup.map_mono hb.partC.right_le

theorem X_inf_D (hb : CaseB1 Q B T L M) : b1X T L ⊓ b1D T L = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨⟨q, hq, rfl⟩, hd⟩ := Subgroup.mem_inf.mp hy
  rw [QuotientGroup.mk'_apply, hb.mk_mem_D_iff] at hd
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rcases hb.partC.mem_inf q hq hd with rfl | rfl
  · exact one_mem _
  · exact hb.setting.centralElt_mem_center

theorem eq_one_of_mem_X_of_mem_D (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hd : x ∈ b1D T L) : x = 1 := by
  have h : x ∈ b1X T L ⊓ b1D T L := ⟨hx, hd⟩
  rwa [hb.X_inf_D, Subgroup.mem_bot] at h

theorem commute_of_mem_X_of_mem_D (hb : CaseB1 Q B T L M) {x d : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hd : d ∈ b1D T L) : Commute x d := by
  obtain ⟨q, hq, rfl⟩ := hx
  obtain ⟨p, hp, rfl⟩ := hd
  change _ * _ = _ * _
  rw [← map_mul, ← map_mul, hb.partC.commute q hq p hp]

theorem exists_mul_of_mem_S (hb : CaseB1 Q B T L M) {s : J ⧸ Subgroup.center J}
    (hs : s ∈ b1S T) : ∃ x ∈ b1X T L, ∃ d ∈ b1D T L, x * d = s := by
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨q, hq, p, hp, rfl⟩ := hb.partC.mem_sup_iff.mp (hb.le_sup ht)
  exact ⟨_, ⟨q, hq, rfl⟩, _, ⟨p, hp, rfl⟩, (map_mul _ _ _).symm⟩

theorem mul_self_of_mem_X (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) : x * x = 1 := by
  obtain ⟨q, hq, rfl⟩ := hx
  rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rcases quaternion_mul_self hb.partC.quaternion.some hb.partC.mem_left hb.partC.order hq with
    h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact hb.setting.centralElt_mem_center

theorem orderOf_of_mem_X (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hb.mul_self_of_mem_X hx) hx1

theorem not_mem_center (hb : CaseB1 Q B T L M) : u ∉ Subgroup.center J := by
  intro hu
  have hsq := hb.partC.sq
  rcases hb.setting.mem_center_iff.mp hu with h | h
  · rw [h, mul_one] at hsq
    exact hb.setting.centralElt_ne_one hsq.symm
  · rw [h, hb.setting.centralElt_mul_self] at hsq
    exact hb.setting.centralElt_ne_one hsq.symm

theorem mk_mem_D (hb : CaseB1 Q B T L M) : (u : J ⧸ Subgroup.center J) ∈ b1D T L :=
  ⟨u, hb.partC.self_mem, rfl⟩

theorem mk_mem_S (hb : CaseB1 Q B T L M) : (u : J ⧸ Subgroup.center J) ∈ b1S T :=
  hb.D_le_S hb.mk_mem_D

theorem mk_ne_one (hb : CaseB1 Q B T L M) : (u : J ⧸ Subgroup.center J) ≠ 1 := by
  rw [Ne, QuotientGroup.eq_one_iff]
  exact hb.not_mem_center

theorem orderOf_mk (hb : CaseB1 Q B T L M) : orderOf (u : J ⧸ Subgroup.center J) = 2 := by
  refine orderOf_eq_prime ?_ hb.mk_ne_one
  rw [pow_two, ← QuotientGroup.mk_mul, hb.partC.sq, QuotientGroup.eq_one_iff]
  exact hb.setting.centralElt_mem_center

theorem mk_not_mem_X (hb : CaseB1 Q B T L M) : (u : J ⧸ Subgroup.center J) ∉ b1X T L :=
  fun h => hb.mk_ne_one (hb.eq_one_of_mem_X_of_mem_D h hb.mk_mem_D)

theorem commute_mk_of_mem_S (hb : CaseB1 Q B T L M) {s : J ⧸ Subgroup.center J}
    (hs : s ∈ b1S T) : Commute s (u : J ⧸ Subgroup.center J) := by
  obtain ⟨t, ht, rfl⟩ := hs
  exact (hb.setting.mem_normalizer_zpowers_iff_commute hb.partC.sq).mp
    (partCSylow_le_quasiNormalizer ht)

end CaseB1

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
