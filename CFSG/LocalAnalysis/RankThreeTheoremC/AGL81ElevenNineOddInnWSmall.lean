module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineFieldIndexWTypes
import CFSG.GroupTheory.SubnormalJoin
import CFSG.ClassicalInvolution.Q3.TwinLemmaBasic
import CFSG.Adapters.GeneralizedFittingTop
import CFSG.RankThree.PartTwo.Sec4.RonanK432Real
import CFSG.RankThree.OddKernel.FailureReduction
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceAltSeven
import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoverSU3
import CFSG.Quasithin.EmptyFaithful.SBdK36Abs
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree Subgroup Equiv

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_gens_of_mulEquiv_perm_three {T : Subgroup Q} (e : T ≃* Perm (Fin 3)) :
    ∃ x t : Q, x ∈ T ∧ t ∈ T ∧ orderOf x = 3 ∧ t * t = 1 ∧ t * x * t⁻¹ = x⁻¹ ∧
      (∀ y ∈ T, ∃ i j : ℕ, y = x ^ j * t ^ i) := by
  set c : Perm (Fin 3) := swap 0 1 * swap 1 2
  set a : Perm (Fin 3) := swap 0 1
  have hall : ∀ y : Perm (Fin 3), ∃ (i : Fin 2) (j : Fin 3), y = c ^ (j : ℕ) * a ^ (i : ℕ) := by
    decide
  have hc3 : c ^ 3 = 1 := by decide
  have hc1 : c ≠ 1 := by decide
  have ha2 : a * a = 1 := by decide
  have hac : a * c * a⁻¹ = c⁻¹ := by decide
  refine ⟨(e.symm c : Q), (e.symm a : Q), (e.symm c).2, (e.symm a).2, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hc3 hc1
  · rw [← Subgroup.coe_mul, ← map_mul, ha2, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_mul, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← map_inv, ← map_mul,
      ← map_mul, hac, map_inv, Subgroup.coe_inv]
  · intro y hy
    obtain ⟨i, j, hij⟩ := hall (e ⟨y, hy⟩)
    refine ⟨i, j, ?_⟩
    have h1 : (⟨y, hy⟩ : T) = e.symm c ^ (j : ℕ) * e.symm a ^ (i : ℕ) := by
      rw [← map_pow, ← map_pow, ← map_mul, ← hij, MulEquiv.symm_apply_apply]
    have h2 := congrArg Subtype.val h1
    simpa using h2

theorem zpowers_eq_of_isSubnormal (hrk : Open.pRank 3 (wSup Q) ≤ 1) {x y : Q}
    (hx : orderOf x = 3) (hy : orderOf y = 3) (hxs : (zpowers x).IsSubnormal)
    (hys : (zpowers y).IsSubnormal) (hxW : x ∈ wSup Q) (hyW : y ∈ wSup Q) :
    zpowers x = zpowers y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P₀ := CFSG.pCore 3 Q ⊓ wSup Q with hP₀
  have hx3 : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; rfl)
  have hy3 : IsPGroup 3 (zpowers y) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; rfl)
  have hxP : zpowers x ≤ P₀ :=
    le_inf (CFSG.ClassicalInvolution.Q3.Twin.le_pCore_of_isSubnormal hxs hx3)
      (zpowers_le.mpr hxW)
  have hyP : zpowers y ≤ P₀ :=
    le_inf (CFSG.ClassicalInvolution.Q3.Twin.le_pCore_of_isSubnormal hys hy3)
      (zpowers_le.mpr hyW)
  have hP3 : IsPGroup 3 P₀ := CFSG.pCore_isPGroup.to_le inf_le_left
  have hrk' : Open.pRank 3 (⊤ : Subgroup ↥P₀) ≤ 1 := by
    have h1 : Open.pRank 3 (⊤ : Subgroup ↥P₀) ≤ Open.pRank 3 ((⊤ : Subgroup ↥P₀).map P₀.subtype) :=
      CFSG.RankThree.OddKernel.pRank_le_map_of_not_dvd Nat.prime_three _ _ (by
        rw [Subgroup.ker_subtype, Subgroup.card_bot]
        decide)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1.trans ((CFSG.SectionRank.pRank_mono (by norm_num) inf_le_right).trans hrk)
  haveI hcyc : IsCyclic ↥(⊤ : Subgroup ↥P₀) :=
    CFSG.RankThree.PartTwo.Sec4.RonanK432.isCyclic_of_pRank_le_one hrk' (hP3.to_subgroup ⊤)
  haveI : IsCyclic ↥P₀ := isCyclic_of_surjective (Subgroup.topEquiv (G := ↥P₀)).toMonoidHom
    (Subgroup.topEquiv (G := ↥P₀)).surjective
  have hcard : Nat.card ((zpowers x).subgroupOf P₀) = Nat.card ((zpowers y).subgroupOf P₀) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxP).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyP).toEquiv,
      Nat.card_zpowers, Nat.card_zpowers, hx, hy]
  have h := (IsCyclic.subgroup_eq_iff_card_eq).mpr hcard
  have h2 := Subgroup.subgroupOf_inj.mp h
  rwa [inf_of_le_left hxP, inf_of_le_left hyP] at h2

theorem isSubnormal_zpowers_of_gens {T : Subgroup Q} {x t : Q} (hx : x ∈ T)
    (hinv : t * x * t⁻¹ = x⁻¹) (hw : ∀ y ∈ T, ∃ i j : ℕ, y = x ^ j * t ^ i)
    (hT : T.IsSubnormal) : (zpowers x).IsSubnormal := by
  refine Subgroup.IsSubnormal.step _ T (zpowers_le.mpr hx) hT ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (zpowers_le.mpr hx)]
  have ht : t ∈ normalizer (zpowers x : Set Q) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    rw [← conj_zpow, hinv]
    exact zpow_mem (inv_mem (mem_zpowers x)) k
  intro y hy
  obtain ⟨i, j, rfl⟩ := hw y hy
  exact mul_mem (pow_mem (le_normalizer (mem_zpowers x)) _) (pow_mem ht _)

theorem card_eq_six_of_mulEquiv {T : Subgroup Q} (e : T ≃* Perm (Fin 3)) : Nat.card T = 6 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

theorem eq_of_isSubnormal_of_mulEquiv_perm_three (hO : CFSG.pCore 2 Q = ⊥)
    (hrk : Open.pRank 3 (wSup Q) ≤ 1) {T₁ T₂ : Subgroup Q} (h₁ : T₁.IsSubnormal)
    (h₂ : T₂.IsSubnormal) (e₁ : T₁ ≃* Perm (Fin 3)) (e₂ : T₂ ≃* Perm (Fin 3))
    (hW₁ : T₁ ≤ wSup Q) (hW₂ : T₂ ≤ wSup Q) : T₁ = T₂ := by
  classical
  obtain ⟨x₁, t₁, hx₁, ht₁, ho₁, htt₁, hinv₁, hw₁⟩ := exists_gens_of_mulEquiv_perm_three e₁
  obtain ⟨x₂, t₂, hx₂, ht₂, ho₂, htt₂, hinv₂, hw₂⟩ := exists_gens_of_mulEquiv_perm_three e₂
  have hX : zpowers x₁ = zpowers x₂ := zpowers_eq_of_isSubnormal hrk ho₁ ho₂
    (isSubnormal_zpowers_of_gens hx₁ hinv₁ hw₁ h₁) (isSubnormal_zpowers_of_gens hx₂ hinv₂ hw₂ h₂)
    (hW₁ hx₁) (hW₂ hx₂)
  have hi₁ : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right htt₁
  have hi₂ : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right htt₂
  have hinv₂₁ : t₂ * x₁ * t₂⁻¹ = x₁⁻¹ := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hX ▸ mem_zpowers x₁ : x₁ ∈ zpowers x₂)
    rw [← hk, ← conj_zpow, hinv₂, inv_zpow]
  have hinv₁₂ : t₁ * x₂ * t₁⁻¹ = x₂⁻¹ := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hX.symm ▸ mem_zpowers x₂ : x₂ ∈ zpowers x₁)
    rw [← hk, ← conj_zpow, hinv₁, inv_zpow]
  set u := t₁ * t₂ with hu
  have hux : ∀ {x : Q}, t₁ * x * t₁⁻¹ = x⁻¹ → t₂ * x * t₂⁻¹ = x⁻¹ → x * u = u * x := by
    intro x h1 h2
    have h3 : u * x * u⁻¹ = x := by
      calc u * x * u⁻¹ = t₁ * (t₂ * x * t₂⁻¹) * t₁⁻¹ := by rw [hu]; group
        _ = (t₁ * x * t₁⁻¹)⁻¹ := by rw [h2]; group
        _ = x := by rw [h1, inv_inv]
    calc x * u = u * x * u⁻¹ * u := by rw [h3]
      _ = u * x := by group
  have hux₁ := hux hinv₁ hinv₂₁
  have hux₂ := hux hinv₁₂ hinv₂
  have hut₁ : t₁ * u * t₁⁻¹ = u⁻¹ := by
    calc t₁ * u * t₁⁻¹ = (t₁ * t₁) * t₂ * t₁⁻¹ := by rw [hu]; group
      _ = (t₁ * t₂)⁻¹ := by rw [htt₁, one_mul, mul_inv_rev, hi₂]
  have hut₂ : t₂ * u * t₂⁻¹ = u⁻¹ := by
    calc t₂ * u * t₂⁻¹ = t₂ * t₁ := by rw [hu]; group
      _ = (t₁ * t₂)⁻¹ := by rw [mul_inv_rev, hi₁, hi₂]
  have hD : (T₁ ⊔ T₂).IsSubnormal := CFSG.GroupTheory.isSubnormal_sup h₁ h₂
  have huD : u ∈ T₁ ⊔ T₂ := mul_mem (mem_sup_left ht₁) (mem_sup_right ht₂)
  have hodd : Odd (orderOf u) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨m, hm⟩ := hev
    have hpos : 0 < orderOf u := orderOf_pos u
    set v := u ^ m with hv
    have hv1 : v ≠ 1 := fun h => by
      have := orderOf_le_of_pow_eq_one (by omega) h
      omega
    have hv2 : v ^ 2 = 1 := by
      rw [hv, ← pow_mul, show m * 2 = m + m by ring, ← hm, pow_orderOf_eq_one]
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← sq, hv2])
    have hcen : ∀ {t : Q}, t * u * t⁻¹ = u⁻¹ → t * v = v * t := by
      intro t h
      have h1 : t * v * t⁻¹ = v := by rw [hv, ← conj_pow, h, inv_pow, ← hv, hvi]
      calc t * v = t * v * t⁻¹ * t := by group
        _ = v * t := by rw [h1]
    have hxv : ∀ {x : Q}, x * u = u * x → x * v = v * x := fun h =>
      (Commute.pow_right h m).eq
    have hC : ∀ {T : Subgroup Q} {x t : Q}, (∀ y ∈ T, ∃ i j : ℕ, y = x ^ j * t ^ i) →
        x * u = u * x → t * u * t⁻¹ = u⁻¹ → T ≤ centralizer {v} := by
      intro T x t hw hxu htu y hy
      obtain ⟨i, j, rfl⟩ := hw y hy
      have hx' : x ∈ centralizer {v} := mem_centralizer_singleton_iff.mpr (hxv hxu)
      have ht' : t ∈ centralizer {v} := mem_centralizer_singleton_iff.mpr (hcen htu)
      exact mul_mem (pow_mem hx' _) (pow_mem ht' _)
    have hDC : T₁ ⊔ T₂ ≤ centralizer {v} := sup_le (hC hw₁ hux₁ hut₁) (hC hw₂ hux₂ hut₂)
    have hvD : v ∈ T₁ ⊔ T₂ := pow_mem huD m
    have hND : zpowers v ≤ T₁ ⊔ T₂ := zpowers_le.mpr hvD
    have hNn : ((zpowers v).subgroupOf (T₁ ⊔ T₂)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hND]
      intro y hy
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
      have h1 : y * v * y⁻¹ = v := by
        rw [mem_centralizer_singleton_iff.mp (hDC hy)]
        group
      rw [← conj_zpow, h1]
      exact zpow_mem (mem_zpowers v) k
    have hNs : (zpowers v).IsSubnormal := Subgroup.IsSubnormal.step _ _ hND hD hNn
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hN2 : IsPGroup 2 (zpowers v) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime hv2 hv1]
      rfl)
    have hle := CFSG.ClassicalInvolution.Q3.Twin.le_pCore_of_isSubnormal hNs hN2
    rw [hO] at hle
    exact hv1 ((mem_bot).mp (hle (mem_zpowers v)))
  have huT : u ∈ T₁ := by
    set E := T₁ ⊔ zpowers u with hE
    have hT₁E : T₁ ≤ E := le_sup_left
    by_cases htop : T₁.subgroupOf E = ⊤
    · have h1 : (⟨u, mem_sup_right (mem_zpowers u)⟩ : E) ∈ T₁.subgroupOf E := htop ▸ mem_top _
      exact h1
    · exfalso
      obtain ⟨K, hK, hTK, hKlt⟩ :=
        Subgroup.IsSubnormal.exists_normal_and_le_and_lt_top_of_ne h₁.subgroupOf htop
      have htt : (⟨t₁, hT₁E ht₁⟩ : E) ∈ K := hTK ht₁
      have hUK : ∀ (c : Q) (hc : c ∈ zpowers u), (⟨c, mem_sup_right hc⟩ : E) ∈ K := by
        intro c hc
        set ct : E := ⟨c, mem_sup_right hc⟩
        set tt : E := ⟨t₁, hT₁E ht₁⟩
        have hc' : t₁ * c * t₁⁻¹ = c⁻¹ := by
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
          rw [← conj_zpow, hut₁, inv_zpow]
        have h1 : tt⁻¹ * (ct * tt * ct⁻¹) ∈ K := K.mul_mem (K.inv_mem htt) (hK.conj_mem tt htt ct)
        have h2 : tt⁻¹ * (ct * tt * ct⁻¹) = ct⁻¹ ^ 2 := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
          rw [hi₁] at hc' ⊢
          calc t₁ * (c * t₁ * c⁻¹) = (t₁ * c * t₁) * c⁻¹ := by group
            _ = c⁻¹ ^ 2 := by rw [hc', sq]
        rw [h2] at h1
        have hoc : Odd (orderOf ct) := by
          rw [Subgroup.orderOf_mk]
          exact hodd.of_dvd_nat (orderOf_dvd_of_mem_zpowers hc)
        obtain ⟨k, hk⟩ := hoc
        have h3 : (ct⁻¹ ^ 2) ^ k = ct := by
          have h4 : ct ^ (2 * k) * ct = 1 := by
            rw [← pow_succ, ← hk, pow_orderOf_eq_one]
          rw [← pow_mul, inv_pow, eq_inv_of_mul_eq_one_left h4, inv_inv]
        rw [← h3]
        exact pow_mem h1 k
      apply hKlt.ne
      rw [eq_top_iff]
      intro y _
      have h1 : E ≤ K.map E.subtype := sup_le (fun z hz => ⟨⟨z, hT₁E hz⟩, hTK hz, rfl⟩)
        (fun c hc => ⟨⟨c, mem_sup_right hc⟩, hUK c hc, rfl⟩)
      obtain ⟨y', hy', hyy⟩ := h1 y.2
      have : y' = y := Subtype.ext hyy
      rwa [← this]
  have ht₂T : t₂ ∈ T₁ := by
    have : t₂ = t₁⁻¹ * u := by rw [hu]; group
    rw [this]
    exact mul_mem (inv_mem ht₁) huT
  have hx₂T : x₂ ∈ T₁ := zpowers_le.mpr hx₁ (hX ▸ mem_zpowers x₂)
  have hle : T₂ ≤ T₁ := by
    intro y hy
    obtain ⟨i, j, rfl⟩ := hw₂ y hy
    exact mul_mem (pow_mem hx₂T _) (pow_mem ht₂T _)
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_eq_six_of_mulEquiv e₁, card_eq_six_of_mulEquiv e₂])).symm

theorem oddInnW_of_wSup_eq {T₀ : Subgroup Q} (h : wSup Q = T₀) (e : T₀ ≃* Perm (Fin 3)) :
    OddInnW Q := by
  intro α _
  have hfix : T₀.map α.toMonoidHom = T₀ := by rw [← h]; exact map_wSup_eq α
  let α' : MulAut T₀ := (α.subgroupMap T₀).trans (MulEquiv.subgroupCongr hfix)
  have hα' : ∀ y : T₀, (α' y : Q) = α y := fun y => rfl
  obtain ⟨g, hg⟩ := CFSG.Quasithin.SBd.perm_three_aut_inner (MulAut.congr e α')
  refine ⟨e.symm g, h ▸ (e.symm g).2, fun x hx => ?_⟩
  rw [h] at hx
  have h1 := hg (e ⟨x, hx⟩)
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  have h2 : α' ⟨x, hx⟩ = e.symm g * ⟨x, hx⟩ * (e.symm g)⁻¹ := by
    apply e.injective
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have h3 := congrArg Subtype.val h2
  rw [hα'] at h3
  simpa using h3

open CFSG.Quasithin.Background.Harris in
theorem oddInnW_of_card_dvd_seventyTwo (hQ : Nat.card Q ∣ 72) (hO : CFSG.pCore 2 Q = ⊥)
    (hrk : Open.pRank 3 (wSup Q) ≤ 1) : OddInnW Q := by
  classical
  set 𝒢 := {T : Subgroup Q | IsSubnormal T ⊤ ∧ (IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T)}
  have hle : ∀ T ∈ 𝒢, T ≤ wSup Q := fun T hT =>
    le_iSup₂ (f := fun (T : Subgroup Q) (_ : T ∈ 𝒢) => T) T hT
  have hgen : ∀ T ∈ 𝒢, T.IsSubnormal ∧ Nonempty (↥T ≃* Perm (Fin 3)) := by
    rintro T ⟨hsub, hc | hs⟩
    · exfalso
      obtain ⟨-, -, hperf, hsimp⟩ := hc
      haveI : Group.IsPerfect T := Group.isPerfect_def.mpr hperf
      haveI : Nontrivial T := (QuotientGroup.mk'_surjective (Subgroup.center T)).nontrivial
      haveI : Group.IsSolvable Q := ToralReduce.isSolvable_of_card_dvd_seventyTwo hQ
      exact Group.IsPerfect.not_isSolvable (G := T) (subgroup_solvable_of_solvable T)
    · refine ⟨(CFSG.Adapters.isSubnormal_top_iff T).mp hsub, ?_⟩
      rcases hs with hs | ⟨K, _, _, hK, ⟨e⟩⟩
      · exact hs
      · exfalso
        have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
        have h216 :=
          OrdinaryProofs.card_statedSU_three_two_of_card_four hK'
        have h216' : Nat.card T = 216 := by
          rw [Nat.card_congr e.toEquiv]
          simpa using h216
        have h1 := (Subgroup.card_subgroup_dvd_card T).trans hQ
        rw [h216'] at h1
        norm_num at h1
  by_cases hne : ∃ T₀, T₀ ∈ 𝒢
  · obtain ⟨T₀, hT₀⟩ := hne
    obtain ⟨hs₀, ⟨e₀⟩⟩ := hgen T₀ hT₀
    have hWeq : wSup Q = T₀ := by
      refine le_antisymm (iSup₂_le fun T hT => ?_) (hle T₀ hT₀)
      obtain ⟨hs, ⟨e⟩⟩ := hgen T hT
      exact (eq_of_isSubnormal_of_mulEquiv_perm_three hO hrk hs hs₀ e e₀ (hle T hT)
        (hle T₀ hT₀)).le
    exact oddInnW_of_wSup_eq hWeq e₀
  · have hWeq : wSup Q = ⊥ := le_bot_iff.mp (iSup₂_le fun T hT => absurd ⟨T, hT⟩ hne)
    intro α _
    refine ⟨1, one_mem _, fun x hx => ?_⟩
    rw [hWeq, mem_bot] at hx
    simp [hx]

end CFSG.LocalAnalysis.RankThreeTheoremC
