module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGSix
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveHRoot

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section TypeFree

variable {Y : Type*} [Group Y] [Finite Y]

theorem sup_zpowers_eq_top_of_normal (hO : oddCore Y = ⊥) {s : Y} (hs : orderOf s = 2)
    {Lh : Subgroup Y} (hLn : Lh.Normal) (hLs : Lh ≤ centralizer ({s} : Set Y))
    (hCs : centralizer ({s} : Set Y) ≤ Lh ⊔ zpowers s)
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (Lh : Set Y) → Nat.card U ≤ 2) :
    Lh ⊔ zpowers s = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup Y := centralizer (Lh : Set Y) with hC
  have hCn : C.Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [hC, mem_centralizer_iff] at hx ⊢
    intro l hl
    have hl' : y⁻¹ * l * y ∈ Lh := by
      have := hLn.conj_mem l hl y⁻¹
      rwa [inv_inv] at this
    have h1 := hx _ hl'
    calc l * (y * x * y⁻¹) = y * ((y⁻¹ * l * y) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * l * y)) * y⁻¹ := by rw [h1]
      _ = y * x * y⁻¹ * l := by group
  have hsC : s ∈ C := cKind_mem_centralizer hLs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    exact absurd hs (by decide)
  set s' : C := ⟨s, hsC⟩ with hs'
  have hos' : orderOf s' = 2 := by
    rw [← orderOf_injective C.subtype C.subtype_injective s']
    exact hs
  have hs'2 : IsPGroup 2 (zpowers s') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, hos']
  obtain ⟨S, hSs⟩ := hs'2.exists_le_sylow
  have hScard : Nat.card S = 2 := by
    have hle : Nat.card S ≤ 2 := by
      have h1 := hsyl (S.toSubgroup.map C.subtype) (S.isPGroup'.map C.subtype)
        (map_subtype_le _)
      rwa [card_map_of_injective C.subtype_injective] at h1
    have hge : 2 ≤ Nat.card S := by
      have h1 := Subgroup.card_le_of_le hSs
      rwa [Nat.card_zpowers, hos'] at h1
    omega
  have hidx := F4Pilot.index_pPrimeCore_two_eq_two S hScard
  set A : Subgroup Y := (pPrimeCore 2 C).map C.subtype with hA
  have hAn : A.Normal := by
    refine ⟨fun x hx y => ?_⟩
    obtain ⟨a, ha, rfl⟩ := hx
    have hyC : y * (a : Y) * y⁻¹ ∈ C := hCn.conj_mem _ a.2 y
    refine ⟨⟨_, hyC⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, F4Pilot.mem_pPrimeCore_two_iff_odd_orderOf S hScard] at ha ⊢
    have h1 : orderOf (⟨_, hyC⟩ : C) = orderOf (y * (a : Y) * y⁻¹) :=
      (orderOf_injective C.subtype C.subtype_injective ⟨_, hyC⟩).symm
    have h2 : orderOf a = orderOf (a : Y) :=
      (orderOf_injective C.subtype C.subtype_injective a).symm
    have h3 : orderOf (y * (a : Y) * y⁻¹) = orderOf (a : Y) := by
      rw [← MulAut.conj_apply]
      exact orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective _
    rw [h1, h3, ← h2]
    exact ha
  have hAodd : Odd (Nat.card A) := by
    rw [hA, card_map_of_injective C.subtype_injective]
    exact F4Pilot.odd_card_pPrimeCore_two
  have hAbot : A = ⊥ := by
    rw [eq_bot_iff, ← hO]
    exact le_sSup ⟨hAn, hAodd⟩
  have hPbot : pPrimeCore 2 C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : Y) ∈ A := ⟨x, hx, rfl⟩
    rw [hAbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hCcard : Nat.card C = 2 := by
    rw [hPbot, index_bot] at hidx
    exact hidx
  have hzs : zpowers s' = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hos', hCcard])
  have hconj : ∀ y : Y, y * s * y⁻¹ = s := by
    intro y
    have hyC : y * s * y⁻¹ ∈ C := hCn.conj_mem s hsC y
    have hmem : (⟨_, hyC⟩ : C) ∈ zpowers s' := hzs ▸ mem_top _
    have hmem' : y * s * y⁻¹ ∈ zpowers s := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
      refine mem_zpowers_iff.2 ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa [hs'] using this
    rcases F4Pilot.eq_one_or_eq_of_mem_zpowers hs hmem' with h | h
    · exfalso
      apply hs1
      have : s = y⁻¹ * (y * s * y⁻¹) * y := by group
      rw [this, h]
      group
    · exact h
  rw [eq_top_iff]
  intro y _
  exact hCs (mem_centralizer_singleton_iff.2 (by
    have h := hconj y
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [h]))

end TypeFree

section InN

variable {N : Type} [Group N] [Finite N]

theorem card_dvd_of_isPGroup_of_normal_map {s : N} (hs : orderOf s = 2) {Lb : Subgroup N}
    (hLs : Lb ≤ centralizer ({s} : Set N)) (hLq : CFSG.Open.IsQuasisimple Lb)
    (hLZ : center Lb = ⊥) (hCs : centralizer ({s} : Set N) ≤ Lb ⊔ zpowers s)
    (hnorm : (Lb.map (QuotientGroup.mk' (oddCore N))).Normal) {P : Subgroup N}
    (hP : IsPGroup 2 P) : Nat.card P ∣ 2 * Nat.card Lb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (oddCore N) with hπ
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hOodd : Odd (Nat.card (oddCore N)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hO : oddCore (N ⧸ oddCore N) = ⊥ := F4Pilot.oddCore_quotient_oddCore_eq_bot_of_finite
  have hsO : s ∉ oddCore N := by
    intro h
    have h1 := Subgroup.orderOf_dvd_natCard (oddCore N) h
    rw [hs] at h1
    exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 h1)
  have hs1 : π s ≠ 1 := by
    rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact hsO
  have hs' : orderOf (π s) = 2 := by
    refine orderOf_eq_prime ?_ hs1
    rw [← map_pow, sq, hs2, map_one]
  have hLs' : Lb.map π ≤ centralizer ({π s} : Set (N ⧸ oddCore N)) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 (hLs hl)]
  have hCs' := centralizer_mk_le_sup_of_le_sup hs hCs
  obtain ⟨-, hsyl, -⟩ := inheritance_of_centralizer_le_sup hs hLs hLq hLZ hCs
  have htop := sup_zpowers_eq_top_of_normal hO hs' hnorm hLs' hCs' hsyl
  set φ := mapOddCoreMulEquivOfCenter hLq hLZ with hφ
  have hLZ' : center (Lb.map π) = ⊥ := F4Pilot.center_eq_bot_congr φ hLZ
  have hsL : π s ∉ Lb.map π := fun h =>
    hs1 (cKind_eq_one_of_mem_centralizer hLZ' h (cKind_mem_centralizer hLs'))
  have hcardY : Nat.card (N ⧸ oddCore N) = 2 * Nat.card Lb := by
    have h1 := card_sup_zpowers_eq (V := Lb.map π) (t := π s)
      (by rw [← map_mul, hs2, map_one]) (cKind_mem_normalizer hLs') hsL
    rw [htop, Subgroup.card_top] at h1
    rw [h1, ← Nat.card_congr φ.toEquiv]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have hcop : Nat.Coprime (Nat.card P) (Nat.card (oddCore N)) := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hOodd)
  have hinf : P ⊓ oddCore N = ⊥ := disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard hcop)
  set f : P →* N ⧸ oddCore N := π.comp P.subtype with hf
  have hker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : π (x : N) = 1 := hx
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : (x : N) ∈ P ⊓ oddCore N := Subgroup.mem_inf.2 ⟨x.2, h1⟩
    rw [hinf, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.2 (Subtype.ext h2)
  have hcard := card_ker_mul_card_range f
  rw [hker, Subgroup.card_bot, one_mul] at hcard
  rw [← hcard, ← hcardY]
  exact Subgroup.card_subgroup_dvd_card _

end InN

section InG

variable {G : Type} [Group G] [Finite G]

theorem card_dvd_of_isPGroup_of_normal_bar {W : Subgroup G} {t : G}
    (htN : t ∈ normalizer (W : Set G)) {Lb : Subgroup (seitzBar W)}
    (hs : orderOf (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨t, htN⟩) = 2)
    (hLs : Lb ≤ centralizer
      ({QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨t, htN⟩} : Set (seitzBar W)))
    (hLq : CFSG.Open.IsQuasisimple Lb) (hLZ : center Lb = ⊥)
    (hCs : centralizer
      ({QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨t, htN⟩} : Set (seitzBar W)) ≤
        Lb ⊔ zpowers (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨t, htN⟩))
    (hnorm : (Lb.map (QuotientGroup.mk' (oddCore (seitzBar W)))).Normal) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPN : P ≤ normalizer (W : Set G)) :
    Nat.card P ∣ Nat.card W * (2 * Nat.card Lb) := by
  set ν := QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) with hν
  set P' := P.subgroupOf (normalizer (W : Set G)) with hP'
  have hPP' : Nat.card P' = Nat.card P := Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv
  have hP'2 : IsPGroup 2 P' := hP.of_equiv (subgroupOfEquivOfLe hPN).symm
  set f : P' →* seitzBar W := ν.comp P'.subtype with hf
  have hcard := card_ker_mul_card_range f
  have hrange : f.range = P'.map ν := by rw [hf, MonoidHom.range_comp, range_subtype]
  have hker : Nat.card f.ker ∣ Nat.card W := by
    have hle : f.ker.map P'.subtype ≤ W.subgroupOf (normalizer (W : Set G)) := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : ν (x : normalizer (W : Set G)) = 1 := hx
      rw [hν, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have h1 := Subgroup.card_dvd_of_le hle
    rw [card_map_of_injective P'.subtype_injective,
      Nat.card_congr (subgroupOfEquivOfLe (le_normalizer (H := W))).toEquiv] at h1
    exact h1
  have hran : Nat.card f.range ∣ 2 * Nat.card Lb := by
    rw [hrange]
    exact card_dvd_of_isPGroup_of_normal_map hs hLs hLq hLZ hCs hnorm (hP'2.map ν)
  rw [← hPP', ← hcard]
  exact Nat.mul_dvd_mul hker hran

theorem card_le_two_pow_of_isPGroup_of_dvd {X : Type*} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsPGroup 2 P) {a m : ℕ} (hm : Odd m) (hdvd : Nat.card P ∣ 2 ^ a * m) :
    Nat.card P ≤ 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have hcop : Nat.Coprime (Nat.card P) m := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
  have h1 : Nat.card P ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right hdvd
  exact Nat.le_of_dvd (by positivity) h1

end InG

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_leviHat_five_of_lt_card (hset : SeitzSetting G L) {K : Type} [Field K]
    [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htW₁ : t ∈ normalizer (W₁ : Set G))
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPN : P ≤ normalizer (W₁ : Set G))
    (hPc : 2 ^ 15 < Nat.card P) :
    ¬ ((((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
            (normalizer (W₁ : Set G))).map
          (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))))).map
        (QuotientGroup.mk' (oddCore (normalizer (W₁ : Set G) ⧸
          W₁.subgroupOf (normalizer (W₁ : Set G)))))).Normal := by
  intro hnorm
  have htC : t ∈ centralizer (L : Set G) := by
    have h := mem_zpowers t
    rw [← hKt] at h
    exact (Subgroup.mem_inf.1 h).1
  obtain ⟨hLq, hLZ, -, hLc, hLs⟩ := leviBar_facts e hK htC hW₁c hLW htW₁
  have hs := orderOf_mk_wOne_eq_two e hK ht hW₁c hW₁2 hW₁t htW₁
  have hCs := centralizer_bar_le_sup e hK ht hW₁c hW₁2 hW₁t htW₁ hLW
    (normalizer_pointRadical_inf_le hset (by norm_num) hK e ht hKt c)
  have hdvd := card_dvd_of_isPGroup_of_normal_bar htW₁ hs hLs hLq hLZ hCs hnorm hP hPN
  rw [hW₁c, hLc] at hdvd
  have h := card_le_two_pow_of_isPGroup_of_dvd hP (a := 15) (m := 315) (by decide)
    (by rw [show 2 ^ 15 * 315 = 2 ^ 8 * (2 * 20160) by norm_num]; exact hdvd)
  omega

@[expose] def LSixSOneNotSylowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 6 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ (a b : Fin 6) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 6 K)),
        X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
        ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) →
    ∀ (c : Fin 6) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 10 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
      t ∈ normalizer (W₁ : Set G) →
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G) →
      ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≤ normalizer (W₁ : Set G) ∧ 2 ^ 21 < Nat.card P

theorem card_specialLinearGroup_five_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 5) K) = 9999360 :=
  CFSG.SeitzReduction.LinearPilot.card_specialLinearGroup_fin_five_eq hK

theorem not_normal_seitzLeviHat_six_of_lt_card (hset : SeitzSetting G L) {K : Type} [Field K]
    [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 6 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 6) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 10) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G))
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPN : P ≤ normalizer (W₁ : Set G))
    (hPc : 2 ^ 21 < Nat.card P) : ¬ (seitzLeviHat e c W₁).Normal := by
  intro hnorm
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht
    exact absurd ht (by decide)
  have htW : t ∉ W₁ := fun h => by
    have h' : t ∈ W₁ ⊓ centralizer ({t} : Set G) :=
      Subgroup.mem_inf.2 ⟨h, mem_centralizer_singleton_iff.2 rfl⟩
    rw [hW₁t] at h'
    exact not_mem_of_mem_centralizer hset.center_eq_bot htC ht1 (modelToG_le e _ h')
  have hWc : ∀ v ∈ W₁, ∀ w ∈ W₁, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW₁2 hv hw
  set s : seitzBar W₁ := QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htN⟩
    with hs_def
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : orderOf s = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hs_def, ← map_pow]
      have : (⟨t, htN⟩ : normalizer (W₁ : Set G)) ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
      rw [this, map_one]
    · intro h1
      rw [hs_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      exact htW h1
  have hLs : seitzLeviBar e c W₁ ≤ centralizer ({s} : Set (seitzBar W₁)) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [mem_centralizer_singleton_iff, hs_def, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_iff.1 htC) _ (modelToG_le e _ (mem_subgroupOf.1 hl))
  obtain ⟨hsimp, hnonab⟩ := isSimpleGroup_seitzLeviBar hK e c hWc hLN
  obtain ⟨hLq, hLZ⟩ := open_isQuasisimple_and_center_of_isSimpleGroup
    (X := seitzLeviBar e c W₁) hnonab
  have hCs := lSixNOneCentralizerInput G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN
  have hmap : (seitzLeviBar e c W₁).map (QuotientGroup.mk' (oddCore (seitzBar W₁))) =
      seitzLeviHat e c W₁ := by
    rw [seitzLeviBar, seitzLeviHat, Subgroup.map_map]
    rfl
  have hdvd := card_dvd_of_isPGroup_of_normal_bar htN hs hLs hLq hLZ hCs (hmap ▸ hnorm) hP hPN
  have hcard : (({c}ᶜ : Finset (Fin 6))).card = 5 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have φ : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≃*
      Matrix.SpecialLinearGroup (Fin 5) K :=
    (linearModelToGEquiv e _).symm.trans
      (blockSLEquivOfEquiv (K := K) (by rw [hcard]; norm_num) (Finset.equivFinOfCardEq hcard)).symm
  have hLdvd : Nat.card (seitzLeviBar e c W₁) ∣ 9999360 := by
    have h1 := Subgroup.card_map_dvd
      ((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6)))).subgroupOf
        (normalizer (W₁ : Set G))) (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))))
    rw [Nat.card_congr (subgroupOfEquivOfLe hLN).toEquiv, Nat.card_congr φ.toEquiv,
      card_specialLinearGroup_five_of_card_two hK] at h1
    exact h1
  rw [hW₁c] at hdvd
  have hdvd' : Nat.card P ∣ 2 ^ 21 * 9765 := by
    refine hdvd.trans ?_
    rw [show 2 ^ 21 * 9765 = 2 ^ 10 * (2 * 9999360) by norm_num]
    exact Nat.mul_dvd_mul_left _ (Nat.mul_dvd_mul_left _ hLdvd)
  have h := card_le_two_pow_of_isPGroup_of_dvd hP (a := 21) (m := 9765) (by decide) hdvd'
  omega

theorem lSixNOneNotNormalInput_of_notSylow (h : LSixSOneNotSylowInput) :
    LSixNOneNotNormalInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hall c W₁ hW₁c hW₁2 hW₁t htN hLN
  obtain ⟨P, hP, hPN, hPc⟩ := h G L hset K hK e t ht hKt hall c W₁ hW₁c hW₁2 hW₁t htN hLN
  exact not_normal_seitzLeviHat_six_of_lt_card hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hP hPN hPc

end Seitz

end CFSG.SeitzReduction.LinearPilot
