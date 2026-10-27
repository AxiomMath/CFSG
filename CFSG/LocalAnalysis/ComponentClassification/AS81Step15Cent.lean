module

public import CFSG.LocalAnalysis.ComponentClassification.AS81AutRad
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Points

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Descend

variable {A B : Type} [Group A] [Group B] (φ : A →* B) (hφ : Function.Surjective φ)
  (σ : MulAut A) (hσ : φ.ker.map (σ : A →* A) = φ.ker)

@[expose] noncomputable def descendAut : MulAut B :=
  ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    (QuotientGroup.congr φ.ker φ.ker σ hσ)).trans (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

theorem descendAut_apply (a : A) : descendAut φ hφ σ hσ (φ a) = φ (σ a) := by
  have h1 : QuotientGroup.quotientKerEquivOfSurjective φ hφ (a : A ⧸ φ.ker) = φ a := rfl
  have h2 : (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ a) = (a : A ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    exact h1.symm
  simp only [descendAut, MulEquiv.trans_apply, h2, QuotientGroup.congr_mk]
  rfl

end Descend

@[expose] def normalizerConj {A : Subgroup G} {c : G} (hc : c ∈ normalizer (A : Set G)) :
    MulAut ↥A where
  toFun a := ⟨c * a * c⁻¹, (mem_normalizer_iff.mp hc a).mp a.2⟩
  invFun a := ⟨c⁻¹ * a * c, by simpa using (mem_normalizer_iff.mp (inv_mem hc) a).mp a.2⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv a := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp only [coe_mul]; group)

omit [Finite G] in
theorem coe_normalizerConj_apply {A : Subgroup G} {c : G} (hc : c ∈ normalizer (A : Set G))
    (a : ↥A) : ((normalizerConj hc a : ↥A) : G) = c * a * c⁻¹ :=
  rfl

omit [Finite G] in
theorem mem_centralizer_of_conj_mem_center {A : Subgroup G} (hA : commutator ↥A = ⊤) {d : G}
    (hd : ∀ a ∈ A, ∃ z ∈ A, (∀ b ∈ A, z * b = b * z) ∧ d * a * d⁻¹ = z * a) :
    d ∈ centralizer (A : Set G) := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, d * ⁅a, b⁆ * d⁻¹ = ⁅a, b⁆ := by
    intro a ha b hb
    obtain ⟨z, hzA, hz, hza⟩ := hd a ha
    obtain ⟨w, hwA, hw, hwb⟩ := hd b hb
    have h0 : d * ⁅a, b⁆ * d⁻¹ = ⁅z * a, w * b⁆ := by
      rw [← hza, ← hwb, commutatorElement_def, commutatorElement_def]
      group
    have h1 : z * (a * w * b * a⁻¹) = (a * w * b * a⁻¹) * z :=
      hz _ (A.mul_mem (A.mul_mem (A.mul_mem ha hwA) hb) (A.inv_mem ha))
    have h2 : w * (b * a⁻¹ * b⁻¹) = (b * a⁻¹ * b⁻¹) * w :=
      hw _ (A.mul_mem (A.mul_mem hb (A.inv_mem ha)) (A.inv_mem hb))
    rw [h0]
    calc ⁅z * a, w * b⁆ = z * (a * w * b * a⁻¹) * z⁻¹ * b⁻¹ * w⁻¹ := by
          rw [commutatorElement_def]; group
      _ = (a * w * b * a⁻¹) * z * z⁻¹ * b⁻¹ * w⁻¹ := by rw [h1]
      _ = a * (w * (b * a⁻¹ * b⁻¹)) * w⁻¹ := by group
      _ = a * ((b * a⁻¹ * b⁻¹) * w) * w⁻¹ := by rw [h2]
      _ = ⁅a, b⁆ := by rw [commutatorElement_def]; group
  set Y : Subgroup ↥A := (centralizer ({d} : Set G)).subgroupOf A
  have hY : (⊤ : Subgroup ↥A) ≤ Y := by
    rw [← hA, _root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [mem_subgroupOf, mem_centralizer_iff]
    intro e he
    rw [Set.mem_singleton_iff.mp he]
    change d * ⁅(x : G), (y : G)⁆ = ⁅(x : G), (y : G)⁆ * d
    have := hcomm x x.2 y y.2
    calc d * ⁅(x : G), (y : G)⁆ = d * ⁅(x : G), (y : G)⁆ * d⁻¹ * d := by group
      _ = ⁅(x : G), (y : G)⁆ * d := by rw [this]
  rw [mem_centralizer_iff]
  intro a ha
  have h := hY (mem_top ⟨a, ha⟩)
  rw [mem_subgroupOf, mem_centralizer_iff] at h
  exact (h d rfl).symm

theorem exists_mem_inv_mul_mem_centralizer {A H : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥A)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) (hHA : H ≤ A)
    (hH : IsElemAbelian 2 H) (hH16 : Nat.card H = 16) {c : G}
    (hcA : c ∈ normalizer (A : Set G)) (hcH : ∀ h ∈ H, c * h * c⁻¹ = h) :
    ∃ h ∈ H, h⁻¹ * c ∈ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨cv⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have hO := oddCore_le_center hq.1 hq.2
  have : Finite cv.k := Nat.finite_of_card_ne_zero (by rw [cv.card_k]; omega)
  have : CharP cv.k 2 := charP_two_of_card cv.card_k
  have hH₀ : IsPGroup 2 (H.subgroupOf A) := (isPGroup_two_of_isElemAbelian hH).comap_subtype
  obtain ⟨T, hT⟩ := hH₀.exists_le_sylow
  obtain ⟨φ, hφs, hφk, hφT⟩ := cv.exists_std hO T
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hH₀2 : ∀ x ∈ (H.subgroupOf A).map φ, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by simpa using hH.2 _ (mem_subgroupOf.mp hx)),
      map_one]
  have hH₀16 : Nat.card ((H.subgroupOf A).map φ) = 16 := by
    rw [card_map_of_isPGroup φ hkerodd hH₀, ← hH16]
    exact Nat.card_congr (subgroupOfEquivOfLe hHA).toEquiv
  have hH₀U : (H.subgroupOf A).map φ ≤ projUnip cv.k := hφT ▸ map_mono hT
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, (H.subgroupOf A).map φ = projRad cv.k i := by
    rcases eq_projRad_of_le_projUnip cv.card_k hH₀U hH₀2 hH₀16 with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  set σ := normalizerConj hcA with hσdef
  have hσ : φ.ker.map (σ : ↥A →* ↥A) = φ.ker := by
    rw [hφk]
    exact Subgroup.map_center_eq σ
  have hα : ∀ x ∈ projRad cv.k i, descendAut φ hφs σ hσ x = x := by
    intro x hx
    rw [← hi] at hx
    obtain ⟨h₀, hh₀, rfl⟩ := hx
    rw [descendAut_apply]
    congr 1
    apply Subtype.ext
    rw [hσdef, coe_normalizerConj_apply]
    exact hcH _ (mem_subgroupOf.mp hh₀)
  obtain ⟨r, hr, hαr⟩ := exists_eq_conj_of_fix_projRad i hα
  rw [← hi] at hr
  obtain ⟨h₁, hh₁, rfl⟩ := hr
  refine ⟨h₁, mem_subgroupOf.mp hh₁, mem_centralizer_of_conj_mem_center hq.1 fun a ha => ?_⟩
  have h1 : φ (σ ⟨a, ha⟩) = φ (h₁ * ⟨a, ha⟩ * h₁⁻¹) := by
    rw [← descendAut_apply φ hφs σ hσ, hαr, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set z : ↥A := (h₁ * ⟨a, ha⟩ * h₁⁻¹)⁻¹ * σ ⟨a, ha⟩ with hz
  have hzk : z ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_inv, h1, inv_mul_cancel]
  rw [hφk] at hzk
  have hzc : ∀ b ∈ A, (z : G) * b = b * z := fun b hb =>
    congrArg Subtype.val (mem_center_iff.mp hzk ⟨b, hb⟩).symm
  refine ⟨z, z.2, hzc, ?_⟩
  have hσa : ((σ ⟨a, ha⟩ : ↥A) : G) = (h₁ : G) * a * (h₁ : G)⁻¹ * z := by
    rw [hz]
    simp only [coe_mul, coe_inv]
    group
  have hcac : c * a * c⁻¹ = (h₁ : G) * a * (h₁ : G)⁻¹ * z := by
    rw [← hσa, hσdef, coe_normalizerConj_apply]
  have hz1 : (z : G) * (h₁ : G) = h₁ * z := hzc _ h₁.2
  calc (h₁ : G)⁻¹ * c * a * ((h₁ : G)⁻¹ * c)⁻¹ = (h₁ : G)⁻¹ * (c * a * c⁻¹) * h₁ := by group
    _ = (h₁ : G)⁻¹ * ((h₁ : G) * a * (h₁ : G)⁻¹ * z) * h₁ := by rw [hcac]
    _ = a * ((h₁ : G)⁻¹ * ((z : G) * h₁)) := by group
    _ = a * z := by rw [hz1]; group
    _ = z * a := (hzc a ha).symm

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem centralizer_eq_sup_oddCoreIn (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    centralizer (E : Set G) = E ⊔ AS76b.oddCoreIn (centralizer (E : Set G)) ∧
      Nat.card (centralizer (E : Set G)) =
        64 * Nat.card (AS76b.oddCoreIn (centralizer (E : Set G))) ∧
      AS76b.oddCoreIn (centralizer (E : Set G)) ≤ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have hEA16 : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hF.R_le_E hF.E_le hRA1
    rw [hF.cardE, hF.cardR] at this
    omega
  have hHe : IsElemAbelian 2 (E ⊓ A) := AS76b.IsElemAbelian.mono hF.elemE inf_le_left
  have hE2 : IsPGroup 2 E := isPGroup_two_of_isElemAbelian hF.elemE
  have hEC : E ≤ centralizer (E : Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx
  have hR1 : R ≠ ⊥ := AS76b.isSylowOf_ne_bot_of_even hR hKte.1
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hCN : ∀ c ∈ centralizer (E : Set G), c ∈ normalizer (A : Set G) := fun c hc => by
    rw [← hNK]
    exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hKte (hRA hr) hr1'
      (hF.elemR.2 r hr) (mem_centralizer_iff.mp hc r (hF.R_le_E hr)).symm
  have hdec : ∀ c ∈ centralizer (E : Set G), ∃ h ∈ E ⊓ A, h⁻¹ * c ∈ centralizer (A : Set G) :=
    fun c hc => exists_mem_inv_mul_mem_centralizer hstd.1 hL hodd inf_le_right hHe hEA16
      (hCN c hc) fun h hh => mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hc h hh.1).symm
  have h2E : ∀ c ∈ centralizer (E : Set G), ∀ n : ℕ, c ^ 2 ^ n = 1 → c ∈ E := by
    intro c hc n hcn
    rcases n with _ | n
    · rw [pow_zero, pow_one] at hcn
      rw [hcn]
      exact E.one_mem
    obtain ⟨h, hh, hd⟩ := hdec c hc
    have hhc : Commute h⁻¹ c := (show Commute h c from mem_centralizer_iff.mp hc h hh.1).inv_left
    have hh2 : h⁻¹ ^ 2 ^ (n + 1) = 1 := by
      have : h⁻¹ ^ 2 = 1 := by rw [inv_pow, hHe.2 h hh, inv_one]
      rw [pow_succ, pow_mul', this, one_pow]
    have hd2 : (h⁻¹ * c) ^ 2 ^ (n + 1) = 1 := by rw [hhc.mul_pow, hh2, hcn, one_mul]
    have hdR : h⁻¹ * c ∈ centralizer (R : Set G) := mem_centralizer_iff.mpr fun x hx =>
      mem_centralizer_iff.mp ((centralizer (E : Set G)).mul_mem (inv_mem (hEC hh.1)) hc) x
        (hF.R_le_E hx)
    have hQ : IsPGroup 2 ↥(R ⊔ zpowers (h⁻¹ * c)) :=
      hR.isPGroup.to_sup_of_normal_left' (AS76b.isPGroup_zpowers_of_pow_eq_one hd2)
        (zpowers_le.mpr (centralizer_le_normalizer _ hdR))
    have heq := hR.eq_of_le le_sup_left (sup_le hRA (zpowers_le.mpr hd)) hQ
    have hdR' : h⁻¹ * c ∈ R := by
      have := (le_sup_right : zpowers (h⁻¹ * c) ≤ R ⊔ zpowers (h⁻¹ * c)) (mem_zpowers _)
      rwa [heq] at this
    have : c = h * (h⁻¹ * c) := by group
    rw [this]
    exact E.mul_mem hh.1 (hF.R_le_E hdR')
  set C := centralizer (E : Set G) with hCdef
  set O := AS76b.oddCoreIn C with hOdef
  have hEsub : IsPGroup 2 (E.subgroupOf C) := hE2.comap_subtype
  obtain ⟨Q, hQ⟩ := hEsub.exists_le_sylow
  have hQE : (Q : Subgroup ↥C) ≤ E.subgroupOf C := by
    intro x hx
    obtain ⟨n, hn⟩ := Q.isPGroup' ⟨x, hx⟩
    have hn' : (x : G) ^ 2 ^ n = 1 := by
      have := congrArg (fun y : ↥(Q : Subgroup ↥C) => ((y : ↥C) : G)) hn
      simpa using this
    exact h2E x x.2 n hn'
  have hQeq : (Q : Subgroup ↥C) = E.subgroupOf C := le_antisymm hQE hQ
  have hPc : normalizer ((Q : Subgroup ↥C) : Set ↥C) ≤
      centralizer ((Q : Subgroup ↥C) : Set ↥C) := by
    intro x _
    rw [mem_centralizer_iff]
    intro q hq
    exact Subtype.ext (mem_centralizer_iff.mp x.2 q (hQE hq))
  obtain ⟨K, hKn, hK2, hKidx, -⟩ := CFSG.GroupTheory.burnside_normal_complement Q hPc
  have hKodd : Odd (Nat.card K) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hK2)
  have hKO : K ≤ CFSG.Assembly.oddCore ↥C := by
    unfold CFSG.Assembly.oddCore
    exact le_sSup ⟨hKn, hKodd⟩
  have hcardQ : Nat.card (Q : Subgroup ↥C) = 64 := by
    rw [hQeq, ← hF.cardE]
    exact Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv
  have hKcard : Nat.card C = 64 * Nat.card K := by
    rw [← hcardQ, ← hKidx, Subgroup.index_mul_card]
  have hOcard : Nat.card K ≤ Nat.card O := by
    rw [hOdef, AS76b.oddCoreIn, card_map_of_injective C.subtype_injective]
    exact Subgroup.card_le_of_le hKO
  have hOE : O ⊓ E = ⊥ := AS76b.oddCoreIn_inf_eq_bot hE2
  have hON : E ≤ normalizer (O : Set G) := fun e he => AS76b.le_normalizer_oddCoreIn C (hEC he)
  have hsup := card_sup_mul_card_inf hON
  rw [hOE, card_bot, mul_one, hF.cardE] at hsup
  have hle : O ⊔ E ≤ C := sup_le (AS76b.oddCoreIn_le C) hEC
  have hcardle := Subgroup.card_le_of_le hle
  rw [hsup] at hcardle
  have hEq : O ⊔ E = C := Subgroup.eq_of_le_of_card_ge hle (by rw [hsup, hKcard]; omega)
  refine ⟨by rw [sup_comm, hEq], by omega, ?_⟩
  intro o ho
  have hoC : o ∈ C := AS76b.oddCoreIn_le C ho
  obtain ⟨h, hh, hd⟩ := hdec o hoC
  have hodd_o : Odd (orderOf o) :=
    (AS76b.odd_card_oddCoreIn C).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ ho)
  obtain ⟨m, hm⟩ := hodd_o
  have hhc : Commute h⁻¹ o := (show Commute h o from mem_centralizer_iff.mp hoC h hh.1).inv_left
  have h2 : h⁻¹ ^ 2 = 1 := by rw [inv_pow, hHe.2 h hh, inv_one]
  have hpow : (h⁻¹ * o) ^ orderOf o = h⁻¹ := by
    rw [hhc.mul_pow, pow_orderOf_eq_one, mul_one, hm, pow_succ, pow_mul, h2, one_pow, one_mul]
  have hhA : h⁻¹ ∈ centralizer (A : Set G) := by
    have := pow_mem hd (orderOf o)
    rwa [hpow] at this
  have hzp : zpowers h ≤ centralizer (A : Set G) :=
    zpowers_le.mpr (by simpa using inv_mem hhA)
  have hz2 : IsPGroup 2 (zpowers h) :=
    AS76b.isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one]; exact hHe.2 h hh)
  have hbot := inf_eq_bot_of_odd_center hzp hz2 hodd
  have hh1 : h = 1 := by
    have : h ∈ zpowers h ⊓ A := ⟨mem_zpowers h, hh.2⟩
    rwa [hbot, mem_bot] at this
  rw [hh1, inv_one, one_mul] at hd
  exact hd

end Frame

end CFSG.ComponentClassification.AS81
