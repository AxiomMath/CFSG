module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFBlockLiftBasic

public section

set_option linter.unusedSectionVars false

open scoped commutatorElement

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.QuasithinUnique CFSG.Open

variable {G : Type*} [Group G]

@[expose] def commQV (M Q V : Subgroup G) (hMV : M ≤ Subgroup.normalizer (V : Set G)) : Subgroup G where
  carrier := {x | x ∈ M ∧ ∀ q ∈ Q, ⁅q, x⁆ ∈ V}
  one_mem' := ⟨M.one_mem, fun q _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
    refine ⟨M.mul_mem hxM hyM, fun q hq => ?_⟩
    have e : ⁅q, x * y⁆ = ⁅q, x⁆ * (x * ⁅q, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem (hx q hq) ((Subgroup.mem_normalizer_iff.mp (hMV hxM) _).mp (hy q hq))
  inv_mem' := by
    rintro x ⟨hxM, hx⟩
    refine ⟨M.inv_mem hxM, fun q hq => ?_⟩
    have e : ⁅q, x⁻¹⁆ = x⁻¹ * ⁅q, x⁆⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 : ⁅q, x⁆⁻¹ ∈ V := V.inv_mem (hx q hq)
    have := (Subgroup.mem_normalizer_iff.mp (hMV (M.inv_mem hxM)) _).mp h1
    simpa [mul_assoc] using this

theorem commQV_le {M Q V : Subgroup G} {hMV : M ≤ Subgroup.normalizer (V : Set G)} :
    commQV M Q V hMV ≤ M := fun _ hx => hx.1

theorem le_normalizer_commQV {M Q V : Subgroup G} {hMV : M ≤ Subgroup.normalizer (V : Set G)}
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) :
    M ≤ Subgroup.normalizer (commQV M Q V hMV : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ commQV M Q V hMV, m * x * m⁻¹ ∈ commQV M Q V hMV := by
    rintro m hm x ⟨hxM, hx⟩
    refine ⟨M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm), fun q hq => ?_⟩
    have hq' : m⁻¹ * q * m ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hMQ (M.inv_mem hm)) q).mp hq
      simpa using this
    have e : ⁅q, m * x * m⁻¹⁆ = m * ⁅m⁻¹ * q * m, x⁆ * m⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hMV hm) _).mp (hx _ hq')
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key m hm x hx, fun hx => by simpa [mul_assoc] using key m⁻¹ (M.inv_mem hm) _ hx⟩

theorem le_normalizer_centralizer {M V : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G)) :
    M ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  have key : ∀ m ∈ M, ∀ z ∈ Subgroup.centralizer (V : Set G),
      m * z * m⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro m hm z hz
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : m⁻¹ * v * m ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hMV (M.inv_mem hm)) v).mp hv
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hz _ hv'
    calc v * (m * z * m⁻¹) = m * ((m⁻¹ * v * m) * z) * m⁻¹ := by group
      _ = m * (z * (m⁻¹ * v * m)) * m⁻¹ := by rw [this]
      _ = m * z * m⁻¹ * v := by group
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key m hm x hx, fun hx => by simpa [mul_assoc] using key m⁻¹ (M.inv_mem hm) _ hx⟩

structure BLCtx (M V Y : Subgroup G) : Prop where
  hYM : Y ≤ M
  hVQ : V ≤ pCoreOf 2 M
  hMV : M ≤ Subgroup.normalizer (V : Set G)
  hQcV : ∀ q ∈ pCoreOf 2 M, ∀ v ∈ V, q * v = v * q
  hchar : CharTwo M
  hQY : pCoreOf 2 M ≤ Subgroup.normalizer (Y : Set G)
  short : IsShort2 Y
  alt : IsAltType Y 3
  hYC : ¬ Y ≤ Subgroup.centralizer (V : Set G)

section Main

variable [Finite G] {M V Y : Subgroup G} (B : BLCtx M V Y)
include B

theorem BLCtx.Q2 : IsPGroup 2 (pCoreOf 2 M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M

theorem BLCtx.V2 : IsPGroup 2 V := B.Q2.to_le B.hVQ

theorem BLCtx.M_le_normalizer_Q : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M

theorem BLCtx.not_mem_centralizer {y : G} (hy : y ∈ Y) (h3 : orderOf y = 3) :
    y ∉ Subgroup.centralizer (V : Set G) := by
  intro hyC
  have hy1 : y ≠ 1 := by rintro rfl; simp at h3
  have hyQ : y ∉ pCoreOf 2 Y := (orderOf_eq_three_of_odd B.alt hy (by rw [h3]; decide) hy1).2
  apply B.hYC
  have hMN := le_normalizer_centralizer B.hMV
  have hQ2Y : IsPGroup 2 (pCoreOf 2 Y) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  refine (le_closure_odd_of_isShort2 B.short).trans ((Subgroup.closure_le _).2 ?_)
  rintro x ⟨hxY, hxodd⟩
  by_cases hx1 : x = 1
  · subst hx1; exact Subgroup.one_mem _
  obtain ⟨o, ho, k, hk⟩ := exists_decomp_of_altType B.alt hy hyQ x hxY
  have hoY : o ∈ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y ho
  have hoM : o ∈ M := B.hYM hoY
  refine mem_of_odd_eq_two_mul (N := Subgroup.centralizer (V : Set G)) (o := o) (c := y ^ k)
    (hMN (B.hYM hxY)) (hMN hoM) (Subgroup.zpow_mem _ hyC k) hk hxodd (exists_orderOf_two_pow hQ2Y ho)

theorem BLCtx.mem_commQV_of_orderOf_three {y : G} (hy : y ∈ Y) (h3 : orderOf y = 3) :
    y ∈ commQV M (pCoreOf 2 M) V B.hMV := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy1 : y ≠ 1 := by rintro rfl; simp at h3
  have hyQ : y ∉ pCoreOf 2 Y := (orderOf_eq_three_of_odd B.alt hy (by rw [h3]; decide) hy1).2
  set A : Subgroup G := Subgroup.zpowers y with hA
  have hAY : A ≤ Y := (Subgroup.zpowers_le).2 hy
  have hA3 : IsPGroup 3 A := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [hA, Nat.card_zpowers, h3]; simp⟩
  have hYM := B.hYM
  have hYQ : Y ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := hYM.trans B.M_le_normalizer_Q
  have hYV : Y ≤ Subgroup.normalizer (V : Set G) := hYM.trans B.hMV
  have hVY : V ≤ Subgroup.normalizer (Y : Set G) := fun x hx => B.hQY (B.hVQ hx)
  have hQU : ⁅pCoreOf 2 M, A⁆ ≤ blockU Y :=
    commutator_le_blockU Nat.prime_three (by norm_num) hAY hA3 B.Q2 B.hQY hYQ
  have hVU : ⁅V, A⁆ ≤ blockU Y :=
    commutator_le_blockU Nat.prime_three (by norm_num) hAY hA3 B.V2 hVY hYV
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := hAY.trans hYV
  have hAQ : A ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := hAY.trans hYQ
  have hidemV : ⁅⁅V, A⁆, A⁆ = ⁅V, A⁆ :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three A V
      hA3 (not_dvd_card_of_isPGroup_two Nat.prime_three (by norm_num) B.V2) hAV
  have hidemQ : ⁅⁅pCoreOf 2 M, A⁆, A⁆ = ⁅pCoreOf 2 M, A⁆ :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three A _
      hA3 (not_dvd_card_of_isPGroup_two Nat.prime_three (by norm_num) B.Q2) hAQ
  have hVA1 : ⁅V, A⁆ ≠ ⊥ := by
    intro hbot
    apply B.not_mem_centralizer hy h3
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have : ⁅v, y⁆ ∈ ⁅V, A⁆ := Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers y)
    rw [hbot, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  set Z := blockZ Y with hZ
  set U := blockU Y with hU
  have hZU : Z ≤ U := inf_le_left
  have hUY : U ≤ Y := by
    rw [hU, blockU, Subgroup.commutator_le]
    intro x hx g hg
    have hxY : x ∈ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y hx
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hxY hg) (Y.inv_mem hxY)) (Y.inv_mem hg)
  have hZc : ∀ z ∈ Z, ∀ g ∈ Y, g * z = z * g := fun z hz g hg =>
    Subgroup.mem_centralizer_iff.mp hz.2 g hg
  have hZc' : ∀ g ∈ Y, ∀ z ∈ Z, g * z * g⁻¹ = z := by
    intro g hg z hz
    rw [hZc z hz g hg]; group
  have hUc : ∀ o ∈ pCoreOf 2 Y, ∀ u ∈ U, o * u = u * o := fun o ho u hu =>
    Subgroup.mem_centralizer_iff.mp (B.short.2.2.1.1 hu).2 o ho
  have hyNV : y ∈ Subgroup.normalizer ((⁅V, A⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator (hYV hy) (Subgroup.le_normalizer (Subgroup.mem_zpowers y))
  have hZN : ∀ g ∈ Y, g ∈ Subgroup.normalizer (Z : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hZc' g hg x hx]; exact hx
    · intro hx
      have := hZc' g⁻¹ (Y.inv_mem hg) _ hx
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rw [e] at this
      rw [this]; exact hx
  set W : Subgroup G := ⁅V, A⁆ ⊔ Z with hW
  have hWU : W ≤ U := sup_le hVU hZU
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := by
    intro g hg
    obtain ⟨o, ho, k, rfl⟩ := exists_decomp_of_altType B.alt hy hyQ g hg
    have hyW : y ∈ Subgroup.normalizer (W : Set G) := mem_normalizer_sup hyNV (hZN y hy)
    have hoW : o ∈ Subgroup.normalizer (W : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (hUc o ho w (hWU hw)).symm
    exact mul_mem hoW (zpow_mem hyW k)
  have hWU' : W = U := by
    rcases B.short.2.2.2.2.2 W le_sup_right hWU hYW with h | h
    · exfalso
      apply hVA1
      have hle : ⁅V, A⁆ ≤ Z := le_sup_left.trans h.le
      rw [← hidemV, eq_bot_iff, Subgroup.commutator_le]
      intro w hw a ha
      have := hZc w (hle hw) a (hAY ha)
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr this.symm
    · exact h
  have hWS : ∀ u ∈ W, u ∈ Subgroup.normalizer ((⁅V, A⁆ : Subgroup G) : Set G) ∧
      ∀ a ∈ A, ⁅u, a⁆ ∈ ⁅V, A⁆ := by
    intro u hu
    rw [hW, Subgroup.sup_eq_closure] at hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · refine ⟨Subgroup.le_normalizer hx, fun a ha => ?_⟩
        have := Subgroup.commutator_mem_commutator hx ha
        rwa [hidemV] at this
      · have hxY : x ∈ Y := hUY (hZU hx)
        have hxA : x ∈ Subgroup.centralizer (A : Set G) :=
          Subgroup.mem_centralizer_iff.mpr (fun a ha => hZc x hx a (hAY ha))
        refine ⟨mem_normalizer_commutator (hYV hxY) (Subgroup.centralizer_le_normalizer _ hxA),
          fun a ha => ?_⟩
        have : ⁅x, a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
          (hZc x hx a (hAY ha)).symm
        rw [this]; exact (⁅V, A⁆).one_mem
    | one => exact ⟨(Subgroup.normalizer _).one_mem, fun a _ => by simp⟩
    | mul x y _ _ hx hy =>
      refine ⟨(Subgroup.normalizer _).mul_mem hx.1 hy.1, fun a ha => ?_⟩
      have e : ⁅x * y, a⁆ = x * ⁅y, a⁆ * x⁻¹ * ⁅x, a⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (⁅V, A⁆).mul_mem ((Subgroup.mem_normalizer_iff.mp hx.1 _).mp (hy.2 a ha)) (hx.2 a ha)
    | inv x _ hx =>
      refine ⟨inv_mem hx.1, fun a ha => ?_⟩
      have e : ⁅x⁻¹, a⁆ = x⁻¹ * ⁅x, a⁆⁻¹ * x := by
        simp only [commutatorElement_def]; group
      rw [e]
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hx.1) _).mp ((⁅V, A⁆).inv_mem (hx.2 a ha))
      simpa using this
  have hSV : ⁅V, A⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv a ha
    have h2 : a * v⁻¹ * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hAV ha) v⁻¹).mp (V.inv_mem hv)
    have e : ⁅v, a⁆ = v * (a * v⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]; exact V.mul_mem hv h2
  have hQS : ⁅pCoreOf 2 M, A⁆ ≤ ⁅V, A⁆ := by
    rw [← hidemQ, Subgroup.commutator_le]
    intro u hu a ha
    exact (hWS u (hWU'.symm ▸ hQU hu)).2 a ha
  refine ⟨hYM hy, fun q hq => ?_⟩
  exact hSV (hQS (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers y)))

theorem BLCtx.le_commQV : Y ≤ commQV M (pCoreOf 2 M) V B.hMV := by
  refine (le_closure_odd_of_isShort2 B.short).trans ((Subgroup.closure_le _).2 ?_)
  rintro x ⟨hxY, hxodd⟩
  by_cases hx1 : x = 1
  · subst hx1; exact Subgroup.one_mem _
  exact B.mem_commQV_of_orderOf_three hxY (orderOf_eq_three_of_odd B.alt hxY hxodd hx1).1

theorem BLCtx.commQV_inf_le :
    commQV M (pCoreOf 2 M) V B.hMV ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 M := by
  set R : Subgroup G := commQV M (pCoreOf 2 M) V B.hMV ⊓ Subgroup.centralizer (V : Set G) with hR
  have hRM : R ≤ M := inf_le_left.trans commQV_le
  have hR2 : IsPGroup 2 R := by
    rw [IsPGroup.iff_card]
    by_contra hnot
    obtain ⟨p, hp, hpd, hp2⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card R ∧ p ≠ 2 := by
      by_contra hcon
      push Not at hcon
      apply hnot
      refine ⟨(Nat.card R).primeFactorsList.length, ?_⟩
      refine Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := R)).ne' ?_
      intro q hq hqd
      exact hcon q hq hqd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) p hpd
    have hxo : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx]
    set A : Subgroup G := Subgroup.zpowers (x : G) with hA
    have hAR : A ≤ R := (Subgroup.zpowers_le).2 x.2
    have hAp : IsPGroup p A := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [hA, Nat.card_zpowers, hxo]; simp⟩
    have hAQ : A ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      (hAR.trans hRM).trans B.M_le_normalizer_Q
    have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp A _
      hAp (not_dvd_card_of_isPGroup_two hp hp2 B.Q2) hAQ
    have hAD : A ≤ commQV M (pCoreOf 2 M) V B.hMV := hAR.trans inf_le_left
    have hAC : A ≤ Subgroup.centralizer (V : Set G) := hAR.trans inf_le_right
    have hQAV : ⁅pCoreOf 2 M, A⁆ ≤ V := by
      rw [Subgroup.commutator_le]
      intro q hq a ha
      exact (hAD ha).2 q hq
    have hbot : ⁅pCoreOf 2 M, A⁆ = ⊥ := by
      rw [← hidem, eq_bot_iff, Subgroup.commutator_le]
      intro u hu a ha
      rw [Subgroup.mem_bot]
      refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
      exact Subgroup.mem_centralizer_iff.mp (hAC ha) u (hQAV hu)
    have hxc : (x : G) ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have : ⁅q, (x : G)⁆ ∈ ⁅pCoreOf 2 M, A⁆ :=
        Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers _)
      rw [hbot, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    have hxQ : (x : G) ∈ pCoreOf 2 M := B.hchar ⟨hRM x.2, hxc⟩
    obtain ⟨k, hk⟩ := exists_orderOf_two_pow B.Q2 hxQ
    rw [hxo] at hk
    have : p = 2 := by
      have h2 : p ∣ 2 ^ k := hk ▸ dvd_refl p
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
    exact hp2 this
  have hnorm : M ≤ Subgroup.normalizer (R : Set G) := fun m hm =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_commQV B.M_le_normalizer_Q hm, le_normalizer_centralizer B.hMV hm⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRM hnorm hR2

theorem BLCtx.centralizer_le_normalizer :
    Subgroup.centralizer (V : Set G) ⊓ M ≤ Subgroup.normalizer (Y : Set G) := by
  have hQ2 := B.commQV_inf_le
  have hDM := le_normalizer_commQV (M := M) (V := V) (hMV := B.hMV) B.M_le_normalizer_Q
  have hCM := le_normalizer_centralizer B.hMV
  have key : ∀ c ∈ Subgroup.centralizer (V : Set G) ⊓ M, ∀ x ∈ Y, c * x * c⁻¹ ∈ Y := by
    intro c hc x hx
    have hcM : c ∈ M := hc.2
    have h := le_closure_odd_of_isShort2 B.short hx
    clear hx
    induction h using Subgroup.closure_induction with
    | mem x hx' =>
      obtain ⟨hxY, hxodd⟩ := hx'
      have hxM : x ∈ M := B.hYM hxY
      have hxD : x ∈ commQV M (pCoreOf 2 M) V B.hMV := B.le_commQV hxY
      set r : G := c * x * c⁻¹ * x⁻¹ with hr
      have hrD : r ∈ commQV M (pCoreOf 2 M) V B.hMV := by
        have h1 : c * x * c⁻¹ ∈ commQV M (pCoreOf 2 M) V B.hMV :=
          (Subgroup.mem_normalizer_iff.mp (hDM hcM) x).mp hxD
        exact mul_mem h1 (inv_mem hxD)
      have hrC : r ∈ Subgroup.centralizer (V : Set G) := by
        have h1 : x * c⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
          (Subgroup.mem_normalizer_iff.mp (hCM hxM) c⁻¹).mp (inv_mem hc.1)
        have e : r = c * (x * c⁻¹ * x⁻¹) := by rw [hr]; group
        rw [e]; exact mul_mem hc.1 h1
      have hrQ : r ∈ pCoreOf 2 M := hQ2 ⟨hrD, hrC⟩
      have hrN : r ∈ Subgroup.normalizer (Y : Set G) := B.hQY hrQ
      have hxN : x ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hxY
      have e : c * x * c⁻¹ = r * x := by rw [hr]; group
      have hodd' : Odd (orderOf (c * x * c⁻¹)) := by
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
        simpa [MulAut.conj_apply] using this ▸ hxodd
      exact mem_of_odd_eq_two_mul (N := Y) (x := c * x * c⁻¹) (o := r) (c := x)
        (by rw [e]; exact mul_mem hrN hxN) hrN hxY e hodd' (exists_orderOf_two_pow B.Q2 hrQ)
    | one => simp
    | mul x y _ _ hx hy =>
      have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
      rw [e]; exact Y.mul_mem hx hy
    | inv x _ hx =>
      have e : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
      rw [e]; exact Y.inv_mem hx
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => key c hc x hx
  · intro hx
    have hc' : c⁻¹ ∈ Subgroup.centralizer (V : Set G) ⊓ M := inv_mem hc
    have := key c⁻¹ hc' _ hx
    simpa [mul_assoc] using this

theorem BLCtx.sup_le_normalizer :
    Y ⊔ (Subgroup.centralizer (V : Set G) ⊓ M) ≤ Subgroup.normalizer (Y : Set G) :=
  sup_le Subgroup.le_normalizer B.centralizer_le_normalizer

end Main

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
