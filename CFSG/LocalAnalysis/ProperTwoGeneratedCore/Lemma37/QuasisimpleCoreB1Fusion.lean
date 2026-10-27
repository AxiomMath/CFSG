module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1Closure

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open DihedralGroup

@[expose] def dihedralParity {M : ℕ} (hM : 2 ∣ M) (c : ZMod 2) :
    DihedralGroup M →* Multiplicative (ZMod 2) where
  toFun
    | r i => Multiplicative.ofAdd (ZMod.castHom hM (ZMod 2) i)
    | sr i => Multiplicative.ofAdd (ZMod.castHom hM (ZMod 2) i + c)
  map_one' := by
    change Multiplicative.ofAdd (ZMod.castHom hM (ZMod 2) 0) = 1
    rw [map_zero]
    rfl
  map_mul' := by
    rintro (i | i) (j | j) <;>
      simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, map_add, RingHom.map_sub,
        ← ofAdd_add] <;>
      congr 1 <;>
      generalize ZMod.castHom hM (ZMod 2) i = a <;>
      generalize ZMod.castHom hM (ZMod 2) j = b <;>
      revert a b c <;> decide

theorem dihedralParity_sr {M : ℕ} (hM : 2 ∣ M) (c : ZMod 2) (i : ZMod M) :
    dihedralParity hM c (sr i) = Multiplicative.ofAdd (ZMod.castHom hM (ZMod 2) i + c) :=
  rfl

theorem zmod_exists_eq_two_mul_or {M : ℕ} [NeZero M] (i : ZMod M) :
    ∃ k : ZMod M, i = 2 * k ∨ i = 2 * k + 1 := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' i.val
  · exact ⟨m, Or.inl (by rw [← ZMod.natCast_zmod_val i, hm]; push_cast; ring)⟩
  · exact ⟨m, Or.inr (by rw [← ZMod.natCast_zmod_val i, hm]; push_cast; ring)⟩

theorem exists_eq_add_two_mul_of_dihedralParity {M : ℕ} [NeZero M] (hM : 2 ∣ M) {c : ZMod 2}
    {i i' : ZMod M} (h : dihedralParity hM c (sr i) = dihedralParity hM c (sr i')) :
    ∃ k : ZMod M, i' = i + 2 * k := by
  rw [dihedralParity_sr, dihedralParity_sr, EmbeddingLike.apply_eq_iff_eq, add_left_inj] at h
  obtain ⟨k, hk | hk⟩ := zmod_exists_eq_two_mul_or (i' - i)
  · exact ⟨k, by rw [← hk, add_sub_cancel]⟩
  · exfalso
    have h' := congrArg (ZMod.castHom hM (ZMod 2)) hk
    rw [RingHom.map_sub, h, sub_self, map_add, map_mul, map_one, map_ofNat] at h'
    revert h'
    generalize ZMod.castHom hM (ZMod 2) k = a
    revert a
    decide

theorem exists_conj_mem_ker_of_surjective {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (φ : (P : Subgroup G) →* Multiplicative (ZMod 2)) (hφ : Function.Surjective φ) {t : G}
    (ht : orderOf t = 2) (htc : t ∈ commutator G) :
    ∃ g : G, ∃ h : g⁻¹ * t * g ∈ (P : Subgroup G), φ ⟨g⁻¹ * t * g, h⟩ = 1 := by
  have hidx : φ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top]
    simp
  obtain ⟨g, hg⟩ := derived_involution_sylow_maximal_transfer P
    (φ.ker.map (P : Subgroup G).subtype) (Subgroup.map_subtype_le _) (by
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
      exact hidx) t ht htc
  obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp hg
  refine ⟨g, hyt ▸ y.2, ?_⟩
  have hy' : (⟨g⁻¹ * t * g, hyt ▸ y.2⟩ : (P : Subgroup G)) = y := Subtype.ext hyt.symm
  rw [hy']
  exact hy

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {u : J}

namespace CaseB1

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {M : ℕ}

theorem two_dvd (hb : CaseB1 Q B T L M) : 2 ∣ M :=
  even_iff_two_dvd.mp hb.even

noncomputable abbrev dRefl (hb : CaseB1 Q B T L M) (i : ZMod M) : J ⧸ Subgroup.center J :=
  ((hb.psi.symm (1, sr i) : b1S T) : J ⧸ Subgroup.center J)

theorem dRefl_mem_D (hb : CaseB1 Q B T L M) (i : ZMod M) : hb.dRefl i ∈ b1D T L :=
  hb.psi_symm_mem_D _

theorem orderOf_dRefl (hb : CaseB1 Q B T L M) (i : ZMod M) : orderOf (hb.dRefl i) = 2 := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Prod.orderOf, orderOf_one, Nat.lcm_one_left,
    orderOf_sr]

theorem eq_dRefl (hb : CaseB1 Q B T L M) {d : J ⧸ Subgroup.center J} (hd : d ∈ b1D T L)
    {i : ZMod M} (hi : hb.psi ⟨d, hb.D_le_S hd⟩ = (1, sr i)) : d = hb.dRefl i := by
  rw [dRefl, ← hi, MulEquiv.symm_apply_apply]

theorem isConj_dRefl_add_two_mul (hb : CaseB1 Q B T L M) (i k : ZMod M) :
    IsConj (hb.dRefl i) (hb.dRefl (i + 2 * k)) := by
  have h : IsConj ((1 : DihedralGroup 2), sr i) (1, sr (i + 2 * k)) :=
    isConj_iff.mpr ⟨(1, r (-k)), by simp [r_mul_sr, sr_mul_r]; ring⟩
  exact ((b1S T).subtype.comp hb.psi.symm.toMonoidHom).map_isConj h

theorem isConj_dRefl_of_parity (hb : CaseB1 Q B T L M) {c : ZMod 2} {i i' : ZMod M}
    (h : dihedralParity hb.two_dvd c (sr i) = dihedralParity hb.two_dvd c (sr i')) :
    IsConj (hb.dRefl i) (hb.dRefl i') := by
  have : NeZero M := ⟨hb.ne_zero⟩
  obtain ⟨k, rfl⟩ := exists_eq_add_two_mul_of_dihedralParity hb.two_dvd h
  exact hb.isConj_dRefl_add_two_mul i k

theorem isConj_dRefl_zero_or_one (hb : CaseB1 Q B T L M) (i : ZMod M) :
    IsConj (hb.dRefl i) (hb.dRefl 0) ∨ IsConj (hb.dRefl i) (hb.dRefl 1) := by
  have : NeZero M := ⟨hb.ne_zero⟩
  obtain ⟨k, rfl | rfl⟩ := zmod_exists_eq_two_mul_or i
  · left
    have h := hb.isConj_dRefl_add_two_mul 0 k
    rwa [zero_add, isConj_comm] at h
  · right
    have h := hb.isConj_dRefl_add_two_mul 1 k
    rwa [add_comm 1, isConj_comm] at h

theorem commutator_eq_top (hb : CaseB1 Q B T L M) :
    commutator (J ⧸ Subgroup.center J) = ⊤ := by
  have := hb.setting.perfect
  exact Group.IsPerfect.commutator_eq_top

theorem isConj_mk_or_of_ne_one (hb : CaseB1 Q B T L M)
    (χ : DihedralGroup M →* Multiplicative (ZMod 2)) {j : ZMod M} (hj : χ (sr j) ≠ 1) :
    IsConj (hb.dRefl j) (u : J ⧸ Subgroup.center J) ∨
      ∃ i : ZMod M, χ (sr i) = 1 ∧ IsConj (hb.dRefl j) (hb.dRefl i) := by
  set φ : b1S T →* Multiplicative (ZMod 2) :=
    χ.comp ((MonoidHom.snd _ _).comp hb.psi.toMonoidHom)
  have hφ : Function.Surjective φ := by
    intro a
    have h2 : ∀ a b : Multiplicative (ZMod 2), b ≠ 1 → a = 1 ∨ a = b := by decide
    rcases h2 a _ hj with rfl | rfl
    · exact ⟨1, map_one φ⟩
    · exact ⟨hb.psi.symm (1, sr j), by simp [φ]⟩
  obtain ⟨g, hgS, hg1⟩ := exists_conj_mem_ker_of_surjective hb.sylow φ hφ (hb.orderOf_dRefl j)
    (by rw [hb.commutator_eq_top]; exact Subgroup.mem_top _)
  rw [coe_sylow] at hgS
  have hy2 : orderOf (g⁻¹ * hb.dRefl j * g) = 2 :=
    (Assembly.orderOf_inv_mul_mul g _).trans (hb.orderOf_dRefl j)
  have hym : ¬ IsMixedInv (g⁻¹ * hb.dRefl j * g) := by
    rw [isMixedInv_inv_mul_mul_iff]
    exact hb.not_isMixedInv_of_mem_D (hb.dRefl_mem_D j)
  have hyD : g⁻¹ * hb.dRefl j * g ∈ b1D T L := by
    refine (hb.mem_X_or_mem_D_of_not_isMixedInv hgS hy2 hym).resolve_left fun hyX => ?_
    have h1 := hb.eq_one_of_inv_mul_mul_mem_D hyX (g := g⁻¹) (by
      rw [inv_inv, show g * (g⁻¹ * hb.dRefl j * g) * g⁻¹ = hb.dRefl j by group]
      exact hb.dRefl_mem_D j)
    rw [h1, orderOf_one] at hy2
    exact absurd hy2 (by decide)
  have hconj : IsConj (hb.dRefl j) (g⁻¹ * hb.dRefl j * g) :=
    isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩
  rcases hb.eq_mk_or_exists_sr hyD hy2 with hyu | ⟨i, hi⟩
  · exact Or.inl (hyu ▸ hconj)
  · refine Or.inr ⟨i, ?_, hb.eq_dRefl hyD hi ▸ hconj⟩
    have h : φ ⟨g⁻¹ * hb.dRefl j * g, hgS⟩ = χ (sr i) := by
      simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.coe_snd]
      rw [hi]
    rw [← h]
    exact hg1

theorem isConj_mk_or_of_dihedralParity (hb : CaseB1 Q B T L M) {c : ZMod 2} {j : ZMod M}
    (hj : dihedralParity hb.two_dvd c (sr j) ≠ 1) :
    IsConj (hb.dRefl j) (u : J ⧸ Subgroup.center J) ∨
      ∃ i : ZMod M, dihedralParity hb.two_dvd c (sr i) = 1 ∧
        IsConj (hb.dRefl j) (hb.dRefl i) :=
  hb.isConj_mk_or_of_ne_one _ hj

theorem isConj_dRefl_one (hb : CaseB1 Q B T L M) :
    IsConj (hb.dRefl 1) (u : J ⧸ Subgroup.center J) ∨ IsConj (hb.dRefl 1) (hb.dRefl 0) := by
  have h1 : dihedralParity hb.two_dvd 0 (sr 1) ≠ 1 := by
    rw [dihedralParity_sr, map_one, Ne, ofAdd_eq_one]
    decide
  have h0 : dihedralParity hb.two_dvd 0 (sr 0) = 1 := by
    rw [dihedralParity_sr, map_zero, add_zero, ofAdd_zero]
  rcases hb.isConj_mk_or_of_dihedralParity h1 with h | ⟨i, hi, h⟩
  · exact Or.inl h
  · exact Or.inr (h.trans (hb.isConj_dRefl_of_parity (hi.trans h0.symm)))

theorem isConj_dRefl_zero (hb : CaseB1 Q B T L M) :
    IsConj (hb.dRefl 0) (u : J ⧸ Subgroup.center J) ∨ IsConj (hb.dRefl 0) (hb.dRefl 1) := by
  have h0 : dihedralParity hb.two_dvd 1 (sr 0) ≠ 1 := by
    rw [dihedralParity_sr, map_zero, Ne, ofAdd_eq_one]
    decide
  have h1 : dihedralParity hb.two_dvd 1 (sr 1) = 1 := by
    rw [dihedralParity_sr, map_one]
    rfl
  rcases hb.isConj_mk_or_of_dihedralParity h0 with h | ⟨i, hi, h⟩
  · exact Or.inl h
  · exact Or.inr (h.trans (hb.isConj_dRefl_of_parity (hi.trans h1.symm)))

theorem oddCore_eq_bot (hb : CaseB1 Q B T L M) :
    CFSG.oddCore (J ⧸ Subgroup.center J) = ⊥ := by
  have := hb.setting.simple
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_right fun h => ?_
  exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hb.orderOf_mk (h ▸ Subgroup.mem_top _)

theorem mk_not_mem_center (hb : CaseB1 Q B T L M) :
    (u : J ⧸ Subgroup.center J) ∉ Subgroup.center (J ⧸ Subgroup.center J) := by
  intro hu
  have := hb.setting.simple
  have htop : Subgroup.center (J ⧸ Subgroup.center J) = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left fun h =>
      hb.mk_ne_one (by rwa [h, Subgroup.mem_bot] at hu)
  have hbot : commutator (J ⧸ Subgroup.center J) = ⊥ := by
    rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ, htop]
  have h1 : (u : J ⧸ Subgroup.center J) ∈ commutator (J ⧸ Subgroup.center J) := by
    rw [hb.commutator_eq_top]
    exact Subgroup.mem_top _
  rw [hbot, Subgroup.mem_bot] at h1
  exact hb.mk_ne_one h1

theorem exists_inv_mul_mk_mul_ne (hb : CaseB1 Q B T L M) :
    ∃ g : J ⧸ Subgroup.center J, g⁻¹ * (u : J ⧸ Subgroup.center J) * g ∈ b1S T ∧
      g⁻¹ * (u : J ⧸ Subgroup.center J) * g ≠ u := by
  by_contra hno
  push Not at hno
  obtain ⟨hfac, -⟩ := CFSG.Adapters.glauberman_zStar hb.sylow ⟨u, hb.mk_mem_S⟩
    hb.mk_mem_center (by rw [← Subgroup.orderOf_coe]; exact hb.orderOf_mk) hno
  refine hb.mk_not_mem_center (Subgroup.mem_center_iff.mpr fun g => ?_)
  obtain ⟨c, hc, k, hk, rfl⟩ := hfac g
  rw [hb.oddCore_eq_bot, Subgroup.mem_bot] at hk
  rw [hk, mul_one]
  exact Subgroup.mem_centralizer_singleton_iff.mp hc

theorem exists_isConj_mk_dRefl (hb : CaseB1 Q B T L M) :
    ∃ i : ZMod M, IsConj (u : J ⧸ Subgroup.center J) (hb.dRefl i) := by
  obtain ⟨g, hgS, hgu⟩ := hb.exists_inv_mul_mk_mul_ne
  have hgD := hb.inv_mul_mk_mul_mem_D hgS
  rcases hb.eq_mk_or_exists_sr hgD ((Assembly.orderOf_inv_mul_mul _ _).trans hb.orderOf_mk) with
    h | ⟨i, hi⟩
  · exact absurd h hgu
  · exact ⟨i, isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]; exact hb.eq_dRefl hgD hi⟩⟩

theorem isConj_dRefl_zero_and_one (hb : CaseB1 Q B T L M) :
    IsConj (hb.dRefl 0) (u : J ⧸ Subgroup.center J) ∧
      IsConj (hb.dRefl 1) (u : J ⧸ Subgroup.center J) := by
  obtain ⟨i, hi⟩ := hb.exists_isConj_mk_dRefl
  rcases hb.isConj_dRefl_zero_or_one i with h | h
  · have hu0 := (hi.trans h).symm
    exact ⟨hu0, hb.isConj_dRefl_one.elim id fun h10 => h10.trans hu0⟩
  · have hu1 := (hi.trans h).symm
    exact ⟨hb.isConj_dRefl_zero.elim id fun h01 => h01.trans hu1, hu1⟩

theorem isConj_mk_of_mem_D (hb : CaseB1 Q B T L M) {d : J ⧸ Subgroup.center J}
    (hd : d ∈ b1D T L) (hd2 : orderOf d = 2) : IsConj d (u : J ⧸ Subgroup.center J) := by
  rcases hb.eq_mk_or_exists_sr hd hd2 with rfl | ⟨i, hi⟩
  · exact IsConj.refl _
  · rw [hb.eq_dRefl hd hi]
    obtain ⟨h0, h1⟩ := hb.isConj_dRefl_zero_and_one
    exact (hb.isConj_dRefl_zero_or_one i).elim (fun h => h.trans h0) fun h => h.trans h1

theorem isConj_mk_of_isConj (hb : CaseB1 Q B T L M) {v d : J ⧸ Subgroup.center J}
    (hd : d ∈ b1D T L) (hd2 : orderOf d = 2) (hvd : IsConj v d) :
    IsConj v (u : J ⧸ Subgroup.center J) :=
  hvd.trans (hb.isConj_mk_of_mem_D hd hd2)

end CaseB1

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
