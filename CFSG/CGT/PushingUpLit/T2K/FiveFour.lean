module

public import CFSG.CGT.PushingUpLit.T2K.FiveTwo
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.CGT.PushingUpLit.T2K.FourSevenA

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Sylow

theorem exists_conj_le_of_isPGroup {H T B : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H) (hB : IsPGroup 2 B) (hBH : B ≤ H) :
    ∃ k ∈ H, B.map (MulAut.conj k).toMonoidHom ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (hB.comap_subtype (K := H)).exists_le_sylow
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 ((S : Subgroup H).map H.subtype) H := ⟨S, rfl⟩
  obtain ⟨k, hk, hconj⟩ := hS'.exists_mem_conj hT
  refine ⟨k, hk, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have hbS : b ∈ (S : Subgroup H).map H.subtype :=
    ⟨⟨b, hBH hb⟩, hS (show (⟨b, hBH hb⟩ : ↥H) ∈ B.subgroupOf H from hb), rfl⟩
  refine (hconj _).2 ?_
  have e : k⁻¹ * ((MulAut.conj k).toMonoidHom b) * k = b := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact hbS

theorem frattini_ambient {H Y P : Subgroup G} (hYH : Y ≤ H)
    (hn : H ≤ Subgroup.normalizer (Y : Set G)) (hP : CFSG.ABGLocalTools.IsSylowOf 2 P Y) :
    ∀ x ∈ H, ∃ y ∈ Y, ∃ m ∈ H ⊓ Subgroup.normalizer (P : Set G), x = y * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  have hxY : x ∈ Subgroup.normalizer (Y : Set G) := hn hx
  have hP' : CFSG.ABGLocalTools.IsSylowOf 2 (P.map (MulAut.conj x).toMonoidHom) Y := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      have := (Subgroup.mem_normalizer_iff.1 hxY p).1 (hP.le hp)
      simpa [MulAut.conj_apply] using this
    · rw [card_map_conj, hP.card_eq]
  obtain ⟨k, hk, hconj⟩ := hP.exists_mem_conj hP'
  refine ⟨k, hk, k⁻¹ * x, ⟨?_, ?_⟩, by group⟩
  · exact H.mul_mem (H.inv_mem (hYH hk)) hx
  · show k⁻¹ * x ∈ Subgroup.normalizer (P : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro p
    have e1 : x * p * x⁻¹ ∈ P.map (MulAut.conj x).toMonoidHom ↔ p ∈ P := by
      rw [mem_map_conj_iff]
      simp [mul_assoc]
    have e2 := hconj (x * p * x⁻¹)
    have e3 : k⁻¹ * (x * p * x⁻¹) * k = (k⁻¹ * x) * p * (k⁻¹ * x)⁻¹ := by group
    rw [e1, e3] at e2
    exact e2

theorem thompsonJ_le_of_isSylowOf {H T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H) :
    thompsonJ T ≤ thompsonJ H := by
  refine iSup_le fun A => iSup_le fun hA => le_thompsonJ' ?_
  refine ⟨hA.1.trans hT.le, hA.2.1, fun B hBH hBe => ?_⟩
  have hBp : IsPGroup 2 B := fun g => ⟨1, Subtype.ext (by simpa using hBe.2 g g.2)⟩
  obtain ⟨k, -, hkB⟩ := exists_conj_le_of_isPGroup hT hBp hBH
  have := hA.2.2 _ hkB (isElemAbelian_map_conj hBe k)
  rwa [card_map_conj] at this

theorem thompsonJ_eq_of_le {T X : Subgroup G} (hXT : X ≤ T) (hJX : thompsonJ T ≤ X) :
    thompsonJ X = thompsonJ T := by
  apply le_antisymm
  · refine iSup_le fun A => iSup_le fun hA => ?_
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
    have hA₀X : A₀ ≤ X := (le_thompsonJ' hA₀).trans hJX
    have h1 : Nat.card A₀ ≤ Nat.card A := hA.2.2 A₀ hA₀X hA₀.2.1
    exact le_thompsonJ' ⟨hA.1.trans hXT, hA.2.1, fun B hBT hBe => (hA₀.2.2 B hBT hBe).trans h1⟩
  · refine iSup_le fun A => iSup_le fun hA => le_thompsonJ' ?_
    exact ⟨(le_thompsonJ' hA).trans hJX, hA.2.1, fun B hBX hBe => hA.2.2 B (hBX.trans hXT) hBe⟩

end Sylow

section Closure

@[expose] def normalClosureIn (H Z : Subgroup G) : Subgroup G :=
  ⨆ (h : G) (_ : h ∈ H), Z.map (MulAut.conj h).toMonoidHom

omit [Finite G] in
theorem le_normalClosureIn {H Z : Subgroup G} : Z ≤ normalClosureIn H Z := by
  intro z hz
  have : Z.map (MulAut.conj (1 : G)).toMonoidHom ≤ normalClosureIn H Z :=
    le_iSup₂_of_le (1 : G) H.one_mem le_rfl
  exact this ⟨z, hz, by simp⟩

theorem le_normalizer_normalClosureIn {H Z : Subgroup G} :
    H ≤ Subgroup.normalizer (normalClosureIn H Z : Set G) := by
  intro h₀ hh₀
  have hle : (normalClosureIn H Z).map (MulAut.conj h₀).toMonoidHom ≤ normalClosureIn H Z := by
    unfold normalClosureIn
    rw [Subgroup.map_iSup]
    refine iSup_le fun h => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hh => ?_
    rw [Subgroup.map_map]
    have e : (MulAut.conj h₀).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
        (MulAut.conj (h₀ * h)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [e]
    exact le_iSup₂_of_le (h₀ * h) (H.mul_mem hh₀ hh) le_rfl
  exact mem_normalizer_of_map_conj_eq
    (Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_conj]))

end Closure

@[expose] def HOf (N R : Subgroup G) : Subgroup G := N ⊓ Subgroup.normalizer (R : Set G)

@[expose] def WOf (N R T : Subgroup G) : Subgroup G :=
  normalClosureIn (HOf N R) (omegaOneCenterOf T)

@[expose] def COf (N R T : Subgroup G) : Subgroup G :=
  HOf N R ⊓ Subgroup.centralizer (WOf N R T : Set G)

theorem exists_maximal_R {M N T : Subgroup G} (hN : IsMaximalTwoLocal N)
    (hM : IsMaximalTwoLocal M) (hNM : N ≠ M) :
    ∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ N ∧ T ≤ Subgroup.normalizer (R : Set G) ∧
      ¬ N ⊓ Subgroup.normalizer (R : Set G) ≤ M ∧
      ∀ R' : Subgroup G, IsPGroup 2 R' → R' ≤ N → R < R' →
        T ≤ Subgroup.normalizer (R' : Set G) → N ⊓ Subgroup.normalizer (R' : Set G) ≤ M := by
  let 𝓡 : Set (Subgroup G) := {R' | IsPGroup 2 R' ∧ R' ≤ N ∧
    T ≤ Subgroup.normalizer (R' : Set G) ∧ ¬ N ⊓ Subgroup.normalizer (R' : Set G) ≤ M}
  have hbot : (⊥ : Subgroup G) ∈ 𝓡 := by
    refine ⟨fun g => ⟨0, ?_⟩, bot_le, ?_, ?_⟩
    · have := Subgroup.mem_bot.1 g.2
      exact Subtype.ext (by simp [this])
    · intro t _
      exact (Subgroup.normalizer_eq_top_iff.2 (inferInstance : (⊥ : Subgroup G).Normal)) ▸
        Subgroup.mem_top t
    · intro hle
      have h1 : N ⊓ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = N := by
        rw [Subgroup.normalizer_eq_top_iff.2 (inferInstance : (⊥ : Subgroup G).Normal), inf_top_eq]
      rw [h1] at hle
      exact hN.2 M (lt_of_le_of_ne hle hNM) hM.1
  obtain ⟨R, hR, hmax⟩ := Set.exists_max_image 𝓡 (fun R' => Nat.card ↥R') (Set.toFinite _)
    ⟨⊥, hbot⟩
  refine ⟨R, hR.1, hR.2.1, hR.2.2.1, hR.2.2.2, fun R' hR'p hR'N hlt hT' => ?_⟩
  by_contra hnot
  have hmem : R' ∈ 𝓡 := ⟨hR'p, hR'N, hT', hnot⟩
  have hcard := hmax R' hmem
  exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le hcard)

structure Sit54 (G : Type) [Group G] [Finite G] (M T N R : Subgroup G) : Prop where
  N_max : IsMaximalTwoLocal N
  T_le_N : T ≤ N
  N_ne : N ≠ M
  R_pgroup : IsPGroup 2 R
  R_le_T : R ≤ T
  T_norm_R : T ≤ Subgroup.normalizer (R : Set G)
  H_not_le : ¬ HOf N R ≤ M
  R_max : ∀ R' : Subgroup G, IsPGroup 2 R' → R' ≤ N → R < R' →
    T ≤ Subgroup.normalizer (R' : Set G) → HOf N R' ≤ M
  C_le : COf N R T ≤ M
  J_not_le : ¬ thompsonJ (HOf N R) ≤ Subgroup.centralizer (WOf N R T : Set G)
  local_le : ∀ P' : Subgroup G, COf N R T < P' → P' ≤ COf N R T ⊔ T →
    T ≤ Subgroup.normalizer (P' : Set G) → HOf N R ⊓ Subgroup.normalizer (P' : Set G) ≤ M

namespace T2Hyp

variable {L M T : Subgroup G} {n : ℕ}

theorem sit54 (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hTG : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (h47 : Subgroup.normalizer (thompsonJ T : Set G) ≤ M)
    (hne : T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {N : Subgroup G}
    (hN : IsMaximalTwoLocal N) (hTN : T ≤ N) (hNM : N ≠ M) : ∃ R : Subgroup G, Sit54 G M T N R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hRp, hRN, hTR, hRH, hRmax⟩ := exists_maximal_R (T := T) hN h.maxLocal hNM
  refine ⟨R, ?_⟩
  have hRT : R ≤ T := by
    have hsup : IsPGroup 2 ↥(T ⊔ R) := hT.isPGroup.to_sup_of_normal_right' hRp hTR
    have := hTG.eq_of_le le_sup_left le_top hsup
    exact this ▸ le_sup_right
  have hTH : T ≤ HOf N R := le_inf hTN hTR
  have hTH' : CFSG.ABGLocalTools.IsSylowOf 2 T (HOf N R) := hTG.of_le hTH le_top
  have hCle : COf N R T ≤ M := by
    refine inf_le_right.trans ?_
    have hZW : (omegaOneCenterOf T : Set G) ⊆ (WOf N R T : Set G) := le_normalClosureIn
    refine (Subgroup.centralizer_le hZW).trans ?_
    exact h.five_two hE1 hT hne
  have hRH' : R ≤ HOf N R := hRT.trans hTH
  have hZT : omegaOneCenterOf T ≤ Subgroup.centralizer (T : Set G) := by
    unfold omegaOneCenterOf omegaOneOf
    rw [Subgroup.closure_le]
    rintro x ⟨hxZ, -⟩
    exact hxZ.2
  have hWR : WOf N R T ≤ Subgroup.centralizer (R : Set G) := by
    unfold WOf normalClosureIn
    refine iSup_le fun g => iSup_le fun hg => ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hgn : g ∈ Subgroup.normalizer (R : Set G) := hg.2
    have hr' : g⁻¹ * r * g ∈ R := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgn) r).1 hr
      simpa using this
    have hzc : z * (g⁻¹ * r * g) = (g⁻¹ * r * g) * z :=
      (Subgroup.mem_centralizer_iff.1 (hZT hz) _ (hRT hr')).symm
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc r * (g * z * g⁻¹) = g * ((g⁻¹ * r * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by rw [hzc]
      _ = (g * z * g⁻¹) * r := by group
  have hRC : R ≤ COf N R T := le_inf hRH' (Subgroup.le_centralizer_iff.1 hWR)
  have hTnormC : T ≤ Subgroup.normalizer (COf N R T : Set G) := by
    intro t ht
    have h1 : t ∈ Subgroup.normalizer (HOf N R : Set G) := Subgroup.le_normalizer (hTH ht)
    have h2 : t ∈ Subgroup.normalizer (Subgroup.centralizer (WOf N R T : Set G) : Set G) :=
      mem_normalizer_centralizer (le_normalizer_normalClosureIn (hTH ht))
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
  refine ⟨hN, hTN, hNM, hRp, hRT, hTR, hRH, fun R' hR'p hR'N hlt hT' => hRmax R' hR'p hR'N hlt hT',
    hCle, ?_, ?_⟩
  ·
    intro hJ
    have hJC : thompsonJ (HOf N R) ≤ COf N R T := le_inf thompsonJ_le hJ
    have hHY : HOf N R ≤ Subgroup.normalizer (thompsonJ (HOf N R) : Set G) := fun x hx =>
      normalizer_le_normalizer_thompsonJ (HOf N R) (Subgroup.le_normalizer hx)
    have hTY : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ thompsonJ (HOf N R)) (thompsonJ (HOf N R)) :=
      hTH'.inf_of_le_normalizer thompsonJ_le hHY
    have hJTY : thompsonJ T ≤ T ⊓ thompsonJ (HOf N R) :=
      le_inf thompsonJ_le (thompsonJ_le_of_isSylowOf hTH')
    have heq : thompsonJ (T ⊓ thompsonJ (HOf N R)) = thompsonJ T :=
      thompsonJ_eq_of_le inf_le_left hJTY
    have hfr := frattini_ambient (thompsonJ_le : thompsonJ (HOf N R) ≤ HOf N R) hHY hTY
    refine hRH ?_
    intro x hx
    obtain ⟨y, hy, m, ⟨-, hm⟩, rfl⟩ := hfr x hx
    refine M.mul_mem ((hJC.trans hCle) hy) ?_
    apply h47
    rw [← heq]
    exact normalizer_le_normalizer_thompsonJ _ hm
  ·
    intro P' hCP hP'CT hTP'
    have hQnorm : T ≤ Subgroup.normalizer ((T ⊓ P' : Subgroup G) : Set G) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hTP' hx⟩
    have hQp : IsPGroup 2 ↥(T ⊓ P') := hT.isPGroup.to_le inf_le_left
    have hQN : T ⊓ P' ≤ N := inf_le_left.trans hTN
    have hRQ : R ≤ T ⊓ P' := le_inf hRT (hRC.trans hCP.le)
    have hprod : ∀ p ∈ P', ∃ c ∈ COf N R T, ∃ t ∈ T, p = c * t := by
      intro p hp
      have hp' : p ∈ ((COf N R T ⊔ T : Subgroup G) : Set G) := hP'CT hp
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTnormC] at hp'
      obtain ⟨c, hc, t, ht, rfl⟩ := hp'
      exact ⟨c, hc, t, ht, rfl⟩
    have hQC : ¬ T ⊓ P' ≤ COf N R T := by
      intro hQC
      apply hCP.not_ge
      intro p hp
      obtain ⟨c, hc, t, ht, rfl⟩ := hprod p hp
      have htP' : t ∈ P' := by
        have := P'.mul_mem (P'.inv_mem (hCP.le hc)) hp
        simpa using this
      exact (COf N R T).mul_mem hc (hQC ⟨ht, htP'⟩)
    have hlt : R < T ⊓ P' := lt_of_le_of_ne hRQ fun heq => hQC (heq ▸ hRC)
    have hmax : HOf N (T ⊓ P') ≤ M := hRmax _ hQp hQN hlt hQnorm
    have hP'H : P' ≤ HOf N R := hP'CT.trans (sup_le inf_le_left hTH)
    have hXn : HOf N R ⊓ Subgroup.normalizer (P' : Set G) ≤ Subgroup.normalizer (P' : Set G) :=
      inf_le_right
    have hP'X : P' ≤ HOf N R ⊓ Subgroup.normalizer (P' : Set G) :=
      le_inf hP'H Subgroup.le_normalizer
    have hTX : T ≤ HOf N R ⊓ Subgroup.normalizer (P' : Set G) := le_inf hTH hTP'
    have hTX' : CFSG.ABGLocalTools.IsSylowOf 2 T (HOf N R ⊓ Subgroup.normalizer (P' : Set G)) :=
      hTG.of_le hTX le_top
    have hQsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ P') P' :=
      hTX'.inf_of_le_normalizer hP'X hXn
    have hfr := frattini_ambient hP'X hXn hQsyl
    intro x hx
    obtain ⟨y, hy, m, ⟨hmH, hmQ⟩, rfl⟩ := hfr x hx
    exact M.mul_mem ((hP'CT.trans (sup_le hCle hT.le)) hy) (hmax ⟨hmH.1.1, hmQ⟩)

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
