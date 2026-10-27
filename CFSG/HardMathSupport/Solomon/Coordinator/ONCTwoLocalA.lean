module

public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.RankThree.Native.ONTripleSig

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple Subgroup
open scoped commutatorElement

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


theorem xG1_mem_K0 : xG 1 ∈ K0G := yG_mem_K0 (j := 0) (by norm_num)

theorem xG2_mem_K0 : xG 2 ∈ K0G := by
  have h := mul_mem (inv_mem (yG_mem_K0 (j := 0) (by norm_num))) (yG_mem_K0 (j := 1) (by norm_num))
  rw [yG_zero, yG_one, inv_mul_cancel_left] at h
  exact h

noncomputable def actK6 : K0G →* alternatingGroup (Fin 6) :=
  actK.codRestrict _ (fun k => by rw [← range_actK]; exact ⟨k, rfl⟩)

theorem actK6_surjective : Function.Surjective (actK6 : K0G →* alternatingGroup (Fin 6)) := by
  intro y
  have : (y : Equiv.Perm (Fin 6)) ∈ actK.range := by rw [range_actK]; exact y.2
  obtain ⟨k, hk⟩ := this
  exact ⟨k, Subtype.ext hk⟩

theorem ker_actK6 : (actK6 : K0G →* alternatingGroup (Fin 6)).ker = zpowers (⟨zG, zG_mem_K0⟩ : K0G) := by
  rw [actK6, MonoidHom.ker_codRestrict, ker_actK]

theorem zK0_mem_center : (⟨zG, zG_mem_K0⟩ : K0G) ∈ Subgroup.center K0G := by
  rw [Subgroup.mem_center_iff]
  intro k
  exact Subtype.ext (zG_central k).symm

theorem ker_actK6_le_center : (actK6 : K0G →* alternatingGroup (Fin 6)).ker ≤ Subgroup.center K0G := by
  rw [ker_actK6, zpowers_le]
  exact zK0_mem_center

theorem center_K0 : Subgroup.center K0G = zpowers (⟨zG, zG_mem_K0⟩ : K0G) := by
  rw [center_eq_ker_of_alt actK6 actK6_surjective ker_actK6_le_center, ker_actK6]

theorem K0_perfect : commutator K0G = ⊤ := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : (⁅(⟨xG 1, xG1_mem_K0⟩ : K0G), (⟨xG 2, xG2_mem_K0⟩ : K0G)⁆ : K0G) =
      ⟨zG ^ (omegaZ 1 2).val, pow_mem zG_mem_K0 _⟩ := by
    apply Subtype.ext
    exact relG.comm 1 2
  refine isPerfect_of_ext_alt actK6 actK6_surjective ker_actK6_le_center
    (by rw [ker_actK6]; exact card_zpowers_zK0) (a := ⟨xG 1, xG1_mem_K0⟩) (b := ⟨xG 2, xG2_mem_K0⟩) ?_ ?_
  · rw [hcomm, ker_actK6]
    exact pow_mem (mem_zpowers _) _
  · rw [hcomm]
    intro h
    have h1 : zG ^ (omegaZ 1 2).val = 1 := congrArg Subtype.val h
    have hv : (omegaZ 1 2).val = 2 := by rw [omegaZ_val]; rfl
    rw [hv] at h1
    apply relG.x1
    calc zG = zG ^ 3 * (zG ^ 2)⁻¹ := by group
      _ = 1 := by rw [relG.xcube, h1]; simp

theorem commutator_mul_of_commute {K : Type*} [Group K] {c₁ c₂ n₁ n₂ : K}
    (h₁ : Commute n₁ (c₂ * n₂)) (h₂ : Commute c₁ n₂) : ⁅c₁ * n₁, c₂ * n₂⁆ = ⁅c₁, c₂⁆ := by
  have e₁ : ⁅n₁, c₂ * n₂⁆ = 1 := commutatorElement_eq_one_iff_commute.2 h₁
  have e₂ : ⁅c₁, n₂⁆ = 1 := commutatorElement_eq_one_iff_commute.2 h₂
  rw [commutatorElement_mul_left_eq_conj_mul, e₁, mul_one, mul_inv_cancel, one_mul,
    commutatorElement_mul_right_eq_mul_conj, e₂, mul_one, mul_inv_cancel_right]

theorem commutator_K0G_self : ⁅K0G, K0G⁆ = K0G := by
  have h1 : (commutator K0G).map K0G.subtype = ⁅K0G, K0G⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (fun k hk => ?_)
  · exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · have : (⟨k, hk⟩ : K0G) ∈ commutator K0G := by rw [K0_perfect]; exact mem_top _
    rw [← h1]
    exact ⟨_, this, rfl⟩

theorem commutator_centralizer_x0 :
    ⁅centralizer ({xG 0} : Set GM), centralizer ({xG 0} : Set GM)⁆ = K0G := by
  apply le_antisymm
  · rw [commutator_le]
    intro g hg h hh
    obtain ⟨a, k, hk, rfl⟩ := mem_centralizer_x0_iff.1 hg
    obtain ⟨b, k', hk', rfl⟩ := mem_centralizer_x0_iff.1 hh
    have hc : ∀ {m : GM}, m ∈ K0G → ∀ n : ℕ, Commute (xG 0 ^ n) m := by
      intro m hm n
      have h0 : Commute m (xG 0) := K0_comm hm
      exact (h0.pow_right n).symm
    rw [(hc hk a).eq, (hc hk' b).eq,
      commutator_mul_of_commute ((hc hk' a).mul_right (Commute.pow_pow_self _ _ _))
        (hc hk b).symm]
    exact mul_mem (mul_mem (mul_mem hk hk') (inv_mem hk)) (inv_mem hk')
  · calc K0G = ⁅K0G, K0G⁆ := commutator_K0G_self.symm
      _ ≤ _ := Subgroup.commutator_mono (fun k hk => mem_centralizer_singleton_iff.2 (K0_comm hk))
        (fun k hk => mem_centralizer_singleton_iff.2 (K0_comm hk))

theorem P0_le_normalizer_K0 : P0G ≤ normalizer (K0G : Set GM) := by
  intro p hp
  obtain ⟨c, hc⟩ : ∃ c : ℕ, p * xG 0 * p⁻¹ = xG 0 * zG ^ c := by
    obtain ⟨c, hc⟩ : ∃ c : ℕ, ⁅p, xG 0⁆ = zG ^ c :=
      ⟨_, relG.comm_coord_coord (⟨p, hp⟩ : P0G) ⟨xG 0, ThreeQRel.v_mem 0⟩⟩
    refine ⟨c, ?_⟩
    have h' : p * xG 0 * p⁻¹ * (xG 0)⁻¹ = zG ^ c := hc
    rw [mul_inv_eq_iff_eq_mul] at h'
    rw [h']
    exact (Commute.pow_left (zG_central (xG 0)) c).eq
  have hC : (centralizer ({xG 0} : Set GM)).map (MulAut.conj p).toMonoidHom =
      centralizer ({xG 0} : Set GM) := by
    rw [map_conj_centralizer, hc, centralizer_mul_zpow]
  have hmap : K0G.map (MulAut.conj p).toMonoidHom = K0G := by
    conv_lhs => rw [← commutator_centralizer_x0, Subgroup.map_commutator, hC]
    exact commutator_centralizer_x0
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hmap]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← hmap] at hh
    obtain ⟨k, hk, hkh⟩ := hh
    have : k = h := (MulAut.conj p).injective hkh
    rwa [← this]

noncomputable def psiK0 : P0G →* MulAut K0G :=
  (K0G.normalizerMonoidHom).comp (Subgroup.inclusion P0G_le_normalizer_K0')
  where P0G_le_normalizer_K0' := P0_le_normalizer_K0

noncomputable def YG : Subgroup GM := (psiK0.ker).map P0G.subtype

theorem YG_le_P0 : YG ≤ P0G := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem mem_YG {y : GM} : y ∈ YG ↔ y ∈ P0G ∧ ∀ k ∈ K0G, y * k = k * y := by
  constructor
  · rintro ⟨y', hy', rfl⟩
    refine ⟨y'.2, fun k hk => ?_⟩
    have h : (⟨(y' : GM), P0_le_normalizer_K0 y'.2⟩ : normalizer (K0G : Set GM)) ∈
        K0G.normalizerMonoidHom.ker := hy'
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, mem_centralizer_iff] at h
    exact (h k hk).symm
  · rintro ⟨hp, hc⟩
    refine ⟨⟨y, hp⟩, ?_, rfl⟩
    show (⟨y, P0_le_normalizer_K0 hp⟩ : normalizer (K0G : Set GM)) ∈ K0G.normalizerMonoidHom.ker
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, mem_centralizer_iff]
    exact fun k hk => (hc k hk).symm

theorem card_YG_ge : 27 ≤ Nat.card YG := by
  have h1 := Subgroup.card_ker_mul_card_range psiK0
  rw [relG.card_threeQ_type] at h1
  have hdvd : Nat.card psiK0.range ∣ 3 ^ 5 := by
    have := Subgroup.card_range_dvd psiK0
    rwa [relG.card_threeQ_type, show (243 : ℕ) = 3 ^ 5 by norm_num] at this
  obtain ⟨k, hk5, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hpg : IsPGroup 3 psiK0.range := IsPGroup.of_card hk
  have h9 := card_le_nine_of_pGroup_mulAut K0_perfect actK6 actK6_surjective ker_actK6_le_center
    psiK0.range hpg
  have hY : Nat.card YG = Nat.card psiK0.ker :=
    Subgroup.card_map_of_injective P0G.subtype_injective
  rw [hY]
  by_contra hlt
  push Not at hlt
  have : Nat.card psiK0.ker * Nat.card psiK0.range < 243 := by nlinarith
  omega

theorem xG_not_mem_zpowers_z (i : Fin 4) : xG i ∉ zpowers zG := by
  intro h
  have h0 := (relG.coord_eq_zero_iff ⟨xG i, ThreeQRel.v_mem i⟩).2 h
  rw [coord_xG] at h0
  have := congrFun h0 i
  simp at this

theorem xG1_not_mem_YG : xG 1 ∉ YG := by
  intro h
  have hc : (⟨xG 1, xG1_mem_K0⟩ : K0G) ∈ Subgroup.center K0G := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext ((mem_YG.1 h).2 k k.2).symm
  rw [center_K0] at hc
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hc
  apply xG_not_mem_zpowers_z 1
  rw [mem_zpowers_iff]
  refine ⟨n, ?_⟩
  have := congrArg Subtype.val hn
  simpa using this

noncomputable def WG : Subgroup GM :=
  (centralizer ({(⟨xG 1, ThreeQRel.v_mem 1⟩ : P0G)} : Set P0G)).map P0G.subtype

theorem mem_WG {w : GM} : w ∈ WG ↔ w ∈ P0G ∧ w * xG 1 = xG 1 * w := by
  constructor
  · rintro ⟨w', hw', rfl⟩
    refine ⟨w'.2, ?_⟩
    have := mem_centralizer_singleton_iff.1 hw'
    exact congrArg Subtype.val this
  · rintro ⟨hw, hc⟩
    exact ⟨⟨w, hw⟩, mem_centralizer_singleton_iff.2 (Subtype.ext hc), rfl⟩

theorem card_WG : Nat.card WG = 81 := by
  have h := relG.card_centralizer ⟨xG 1, ThreeQRel.v_mem 1⟩ (xG_not_mem_zpowers_z 1)
  rw [WG, Subgroup.card_map_of_injective P0G.subtype_injective]
  exact h

theorem YG_le_WG : YG ≤ WG := fun _ hy =>
  mem_WG.2 ⟨YG_le_P0 hy, (mem_YG.1 hy).2 _ xG1_mem_K0⟩

theorem xG1_mem_WG : xG 1 ∈ WG := mem_WG.2 ⟨ThreeQRel.v_mem 1, rfl⟩

theorem WG_eq : YG ⊔ zpowers (xG 1) = WG := by
  have hle : YG ⊔ zpowers (xG 1) ≤ WG :=
    sup_le YG_le_WG ((zpowers_le).2 xG1_mem_WG)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_WG]
  have hP : YG ⊔ zpowers (xG 1) ≤ P0G :=
    sup_le YG_le_P0 ((zpowers_le).2 (ThreeQRel.v_mem 1))
  have hdvd : Nat.card (YG ⊔ zpowers (xG 1) : Subgroup GM) ∣ 243 := by
    have := Subgroup.card_dvd_of_le hP
    rwa [relG.card_threeQ_type] at this
  have hle81 : Nat.card (YG ⊔ zpowers (xG 1) : Subgroup GM) ≤ 81 := by
    rw [← card_WG]
    exact Subgroup.card_le_of_le hle
  have h27 : 27 ≤ Nat.card (YG ⊔ zpowers (xG 1) : Subgroup GM) :=
    card_YG_ge.trans (Subgroup.card_le_of_le le_sup_left)
  have hY := card_YG_ge
  rcases ThreeQRel.pow_of_dvd hdvd with h | h | h | h | h | h
  · omega
  · omega
  · omega
  · exfalso
    have heq : YG = YG ⊔ zpowers (xG 1) :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    apply xG1_not_mem_YG
    rw [heq]
    exact mem_sup_right (mem_zpowers _)
  · omega
  · omega

theorem WG_le_normalizer_V :
    WG ≤ normalizer (VG 0 0 (by norm_num) (by norm_num) : Set GM) := by
  rw [← WG_eq]
  refine sup_le (fun _ hy => ?_) ?_
  · exact mem_normalizer_of_comm fun v hv =>
      (mem_YG.1 hy).2 v (VG_le_K0 (by norm_num) (by norm_num) hv)
  · rw [zpowers_le]
    have hx : xG 1 ∈ AG 0 := yG_zero ▸ yG_mem_AG (j := 0) (by norm_num)
    exact AG_le_normalizer_VG (by norm_num) (by norm_num) hx

theorem exists_two_group_normalized_by_centralizer_x1 :
    ∃ S : Subgroup GM, S ≠ ⊥ ∧ IsPGroup 2 S ∧
      ∀ w ∈ P0G, w * xG 1 = xG 1 * w → w ∈ normalizer (S : Set GM) := by
  refine ⟨VG 0 0 (by norm_num) (by norm_num), ?_, ?_, fun w hw hc => ?_⟩
  · intro h
    have := card_VG (j := 0) (m := 0) (by norm_num) (by norm_num)
    rw [h, Subgroup.card_bot] at this
    omega
  · exact IsPGroup.of_card (n := 2) (by rw [card_VG (by norm_num) (by norm_num)]; norm_num)
  · exact WG_le_normalizer_V (mem_WG.2 ⟨hw, hc⟩)

end CFSG.HardMathSupport.Solomon.Coordinator
