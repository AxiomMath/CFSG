module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs710
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Triple
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowContainment

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7K28

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Solomon.UniquenessMaximal

section Core

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def oPrime3 (X : Type) [Group X] : Subgroup X :=
  GLAPPrimeCoreOf 3 (⊤ : Subgroup X)

omit [Finite X] in
theorem oPrime3_normal : (oPrime3 X).Normal :=
  ⟨fun x hx g => GLAPPrimeCoreOf_conj_mem g (Subgroup.mem_top g) x hx⟩

theorem coprime_card_oPrime3 : Nat.Coprime 3 (Nat.card (oPrime3 X)) :=
  coprime_card_GLAPPrimeCoreOf Nat.prime_three _

omit [Finite X] in
theorem mk_eq_of_mem_oPrime3 {o : X} (ho : o ∈ oPrime3 X) :
    (QuotientGroup.mk ⟨o, trivial⟩ : ↥(⊤ : Subgroup X) ⧸ GLAPPrimeCore 3 ↥(⊤ : Subgroup X)) = 1 := by
  rw [QuotientGroup.eq_one_iff]
  obtain ⟨y, hy, hyo⟩ := Subgroup.mem_map.1 ho
  have : y = ⟨o, trivial⟩ := Subtype.ext hyo
  exact this ▸ hy

theorem barX_eq_top_of_sup {N : Subgroup X} (h : N ⊔ oPrime3 X = ⊤) :
    barX 3 (⊤ : Subgroup X) N = ⊤ := by
  have := (oPrime3_normal (X := X))
  rw [eq_top_iff]
  intro z _
  obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective z
  have hg' : g ∈ N ⊔ oPrime3 X := h ▸ trivial
  obtain ⟨n, hn, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg'
  refine ⟨⟨n, trivial⟩, Subgroup.mem_subgroupOf.2 hn, ?_⟩
  have := mk_eq_of_mem_oPrime3 ho
  change (QuotientGroup.mk (⟨n, trivial⟩ : ↥(⊤ : Subgroup X)) :
      ↥(⊤ : Subgroup X) ⧸ GLAPPrimeCore 3 ↥(⊤ : Subgroup X)) =
    QuotientGroup.mk ((⟨n, trivial⟩ : ↥(⊤ : Subgroup X)) * ⟨o, trivial⟩)
  rw [QuotientGroup.mk_mul, this, mul_one]

theorem normalizer_sup_oPrime3_eq_top {P : Subgroup X} (hPO : P ≤ oPrime3 X) (hP : IsPGroup 2 P)
    (hidx : ¬ 2 ∣ P.relIndex (oPrime3 X)) :
    Subgroup.normalizer (P : Set X) ⊔ oPrime3 X = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := (oPrime3_normal (X := X))
  have hP' : IsPGroup 2 (P.subgroupOf (oPrime3 X)) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPO).symm
  let S : Sylow 2 (oPrime3 X) := hP'.toSylow hidx
  have h := Sylow.normalizer_sup_eq_top S
  have hmap : (S : Subgroup (oPrime3 X)).map (oPrime3 X).subtype = P := by
    change (P.subgroupOf (oPrime3 X)).map (oPrime3 X).subtype = P
    rw [Subgroup.map_subgroupOf_eq_of_le hPO]
  rw [← h, hmap]

theorem mem_normalizer_sup_oPrime3 {T : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (T : Set X)) : g ∈ Subgroup.normalizer ((T ⊔ oPrime3 X : Subgroup X) : Set X) := by
  have hO := oPrime3_normal (X := X)
  have key : ∀ {g : X}, g ∈ Subgroup.normalizer (T : Set X) → ∀ x ∈ T ⊔ oPrime3 X,
      g * x * g⁻¹ ∈ T ⊔ oPrime3 X := by
    intro g hg x hx
    obtain ⟨t, ht, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    have : g * (t * o) * g⁻¹ = (g * t * g⁻¹) * (g * o * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.1 hg t).1 ht) (hO.conj_mem o ho g)
  exact Sec7.mem_normalizer_of_conj_mem (key hg) (fun x hx => by simpa using key (inv_mem hg) x hx)

theorem not_two_dvd_relIndex_inf {B T : Subgroup X} (hB : IsPGroup 3 B)
    (hT : IsMaxBInvariantTwo B T) : ¬ 2 ∣ (T ⊓ oPrime3 X).relIndex (oPrime3 X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := oPrime3_normal (X := X)
  obtain ⟨hT2, hBT, hTmax⟩ := hT
  set O := oPrime3 X with hOdef
  set H : Subgroup X := T ⊔ O with hH
  have hTH : T ≤ H := le_sup_left
  have hOH : O ≤ H := le_sup_right
  have hBH : B ≤ Subgroup.normalizer (H : Set X) := fun b hb => mem_normalizer_sup_oPrime3 (hBT hb)
  have hc : O.relIndex H = O.relIndex T := Subgroup.relIndex_sup_right T O
  have hcT : (T ⊓ O).relIndex T = O.relIndex T := Subgroup.inf_relIndex_left T O
  have hcdvd : O.relIndex T ∣ Nat.card T := Subgroup.relIndex_dvd_card O T
  have hq : (O.relIndex T) * Nat.card ↥(T ⊓ O) = Nat.card T := by
    rw [← hcT]
    have := Subgroup.relIndex_mul_card (H := T ⊓ O) (K := T)
    rwa [inf_eq_left.mpr inf_le_left] at this
  have hOc : O.relIndex H * Nat.card O = Nat.card H := by
    have := Subgroup.relIndex_mul_card (H := O) (K := H)
    rwa [inf_eq_left.mpr hOH] at this
  have hb : (T ⊓ O).relIndex O * Nat.card ↥(T ⊓ O) = Nat.card O := by
    have := Subgroup.relIndex_mul_card (H := T ⊓ O) (K := O)
    rwa [inf_eq_left.mpr inf_le_right] at this
  have ha : T.relIndex H * Nat.card T = Nat.card H := by
    have := Subgroup.relIndex_mul_card (H := T) (K := H)
    rwa [inf_eq_left.mpr hTH] at this
  have hc0 : O.relIndex T ≠ 0 := fun h =>
    Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd (h ▸ hcdvd))
  have hq0 : Nat.card ↥(T ⊓ O) ≠ 0 := Nat.card_pos.ne'
  have hab : T.relIndex H = (T ⊓ O).relIndex O := by
    have h1 : T.relIndex H * (O.relIndex T * Nat.card ↥(T ⊓ O)) =
        O.relIndex T * ((T ⊓ O).relIndex O * Nat.card ↥(T ⊓ O)) := by
      rw [hq, hb, ha, ← hOc, hc]
    have h2 : (T.relIndex H) * (O.relIndex T * Nat.card ↥(T ⊓ O)) =
        (O.relIndex T * Nat.card ↥(T ⊓ O)) * T.relIndex H := by ring
    have h3 : O.relIndex T * ((T ⊓ O).relIndex O * Nat.card ↥(T ⊓ O)) =
        (O.relIndex T * Nat.card ↥(T ⊓ O)) * (T ⊓ O).relIndex O := by ring
    rw [h2, h3] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.pos_of_ne_zero hc0) (Nat.pos_of_ne_zero hq0)) h1
  rw [← hab]
  have hBcop : Nat.Coprime 3 (Nat.card H) := by
    rw [← hOc, hc]
    refine Nat.Coprime.mul_right ?_ coprime_card_oPrime3
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    have : O.relIndex T ∣ 2 ^ n := hn ▸ hcdvd
    exact (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)).coprime_dvd_right this
  let φ : B →* MulAut H := H.normalizerMonoidHom.comp (Subgroup.inclusion hBH)
  let _ : MulDistribMulAction B H := MulDistribMulAction.compHom H φ
  have hT' : IsPGroup 2 (T.subgroupOf H) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hinv : ∀ b : B, ∀ x ∈ T.subgroupOf H, b • x ∈ T.subgroupOf H := by
    intro b x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    change (((H.normalizerMonoidHom) (Subgroup.inclusion hBH b)) x : X) ∈ T
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (Subgroup.mem_normalizer_iff.1 (hBT b.2) _).1 hx
  obtain ⟨S, hTS, hSfix⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing 3 2
    Nat.prime_three Nat.prime_two hB hBcop (T.subgroupOf H) hT' hinv
  let S' : Subgroup X := (S : Subgroup H).map H.subtype
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map H.subtype
  have hS'B : B ≤ Subgroup.normalizer (S' : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨y, hy, rfl⟩
    have hfix : (⟨b, hb⟩ : B) • S = S := hSfix ⟨b, hb⟩
    have hmem : (⟨b, hb⟩ : B) • y ∈ (S : Subgroup H) := by
      have h := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : B) (S : Subgroup H) hy
      rwa [← Sylow.pointwise_smul_def, hfix] at h
    refine ⟨_, hmem, ?_⟩
    change (((H.normalizerMonoidHom) (Subgroup.inclusion hBH ⟨b, hb⟩)) y : X) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hTS' : T ≤ S' := by
    intro x hx
    exact ⟨⟨x, hTH hx⟩, hTS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hS'T : S' = T := hTmax S' hS'2 hS'B hTS'
  have hST : (S : Subgroup H) = T.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTH]
    exact hS'T
  have := S.not_dvd_index
  rwa [hST] at this

section Jgroups

variable {T : Subgroup X}

theorem pRank_inf_eq (h : jOneOf T ≤ oPrime3 X) : CFSG.Open.pRank 2 (T ⊓ oPrime3 X) = CFSG.Open.pRank 2 T := by
  obtain ⟨E, hET, hE, hcard⟩ := CFSG.SectionRank.exists_pRank Nat.one_lt_two T
  have hEJ : E ≤ jOneOf T := le_iSup₂_of_le E ⟨hET, hE, by
    rw [hcard]; exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)⟩ le_rfl
  exact le_antisymm (CFSG.SectionRank.pRank_mono Nat.one_lt_two inf_le_left)
    (CFSG.SectionRank.le_pRank Nat.one_lt_two (le_inf hET (hEJ.trans h)) hE hcard)

theorem jOneOf_eq_inf (h : jOneOf T ≤ oPrime3 X) : jOneOf T = jOneOf (T ⊓ oPrime3 X) := by
  refine le_antisymm (iSup₂_le fun E hE => ?_) (iSup₂_le fun E hE => ?_)
  · have hEO : E ≤ oPrime3 X := (le_iSup₂_of_le E hE le_rfl).trans h
    exact le_iSup₂_of_le E ⟨le_inf hE.1 hEO, hE.2.1, by rw [pRank_inf_eq h]; exact hE.2.2⟩ le_rfl
  · exact le_iSup₂_of_le E ⟨hE.1.trans inf_le_left, hE.2.1, by
      rw [← pRank_inf_eq h]; exact hE.2.2⟩ le_rfl

theorem jOf_eq_inf (h : jOneOf T ≤ oPrime3 X) : jOf T = jOf (T ⊓ oPrime3 X) := by
  refine le_antisymm (iSup₂_le fun E hE => ?_) (iSup₂_le fun E hE => ?_)
  · have hEJ : E ≤ jOneOf T := le_iSup₂_of_le E ⟨hE.1, hE.2.1, by
      rw [hE.2.2]; exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)⟩ le_rfl
    exact le_iSup₂_of_le E ⟨le_inf hE.1 (hEJ.trans h), hE.2.1, by
      rw [pRank_inf_eq h]; exact hE.2.2⟩ le_rfl
  · exact le_iSup₂_of_le E ⟨hE.1.trans inf_le_left, hE.2.1, by
      rw [← pRank_inf_eq h]; exact hE.2.2⟩ le_rfl

end Jgroups

theorem barX_normalizer_tripleOf_eq_top {B T : Subgroup X} (hB : IsPGroup 3 B)
    (hT : IsMaxBInvariantTwo B T) (h : jOneOf T ≤ oPrime3 X) (i : Fin 3) (hi : i ≠ 2) :
    barX 3 (⊤ : Subgroup X) (Subgroup.normalizer (tripleOf T i : Set X)) = ⊤ := by
  have hP2 : IsPGroup 2 ↥(T ⊓ oPrime3 X) := hT.1.to_le inf_le_left
  have hfr := normalizer_sup_oPrime3_eq_top inf_le_right hP2 (not_two_dvd_relIndex_inf hB hT)
  have hle : Subgroup.normalizer ((T ⊓ oPrime3 X : Subgroup X) : Set X) ≤
      Subgroup.normalizer (tripleOf T i : Set X) := by
    have h1 := Sec7.normalizer_le_normalizer_tripleOf (T ⊓ oPrime3 X) i
    have h2 : tripleOf T i = tripleOf (T ⊓ oPrime3 X) i := by
      rcases Sec7.fin_three_cases i with rfl | rfl | rfl
      · rw [Sec7.tripleOf_zero, Sec7.tripleOf_zero]; exact jOf_eq_inf h
      · rw [Sec7.tripleOf_one, Sec7.tripleOf_one, ← jOneOf_eq_inf h]
      · exact absurd rfl hi
    rwa [h2]
  exact barX_eq_top_of_sup (top_le_iff.1 (hfr ▸ sup_le_sup_right hle _))

end Core

open CFSG.LocalAnalysis.GLTheoremB in
@[expose] def Input28_8Offending : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    Subgroup.centralizer (CFSG.Open.pCore 2 X : Set X) ≤ CFSG.Open.pCore 2 X →
    ∀ K T B : Subgroup X, GLAPComponent 3 (⊤ : Subgroup X) K →
      IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K) → IsElemAbelian 3 B → IsMaxBInvariantTwo B T →
      ¬ jOneOf T ≤ GLAPPrimeCoreOf 3 (⊤ : Subgroup X) →
      barX 3 (⊤ : Subgroup X) K ⊔ barX 3 (⊤ : Subgroup X) T ⊔ barX 3 (⊤ : Subgroup X) B = ⊤ →
      Nat.card ↥(barX 3 (⊤ : Subgroup X) B ⊓ barX 3 (⊤ : Subgroup X) K) = 9 →
        ∃ s : Finset (Fin 3), 2 ≤ s.card ∧ ∀ i ∈ s,
          barX 3 (⊤ : Subgroup X) K ≤
            barX 3 (⊤ : Subgroup X) (Subgroup.normalizer (tripleOf T i : Set X))

theorem input28_8_of_offending (h : Input28_8Offending) : Input28_8 := by
  intro X _ _ hK hC K T B hKc hL hB hT hX h9
  by_cases hJ : jOneOf T ≤ GLAPPrimeCoreOf 3 (⊤ : Subgroup X)
  · have hBp : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hB.2 g g.2)⟩
    refine ⟨{0, 1}, by decide, ?_⟩
    intro i hi
    have hi2 : i ≠ 2 := by
      rintro rfl
      revert hi; decide
    have := barX_normalizer_tripleOf_eq_top hBp hT hJ i hi2
    rw [this]
    exact le_top
  · exact h X hK hC K T B hKc hL hB hT hJ hX h9

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7K28
