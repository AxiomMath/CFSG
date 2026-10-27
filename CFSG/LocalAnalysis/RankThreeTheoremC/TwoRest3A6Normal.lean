module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexRank
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterClass
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaAux
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6

open CFSG.Open CFSG.AGLEmbedding

variable {X : Type*} [Group X] [Finite X]

theorem mul_mem_or_of_index_le_three {U K : Subgroup X} (hU : IsPGroup 3 U)
    (hK : ((U ⊓ K).subgroupOf U).index ≤ 3) {a b : X} (ha : a ∈ U) (hb : b ∈ U)
    (haK : a ∉ K) (hbK : b ∉ K) : a * b⁻¹ ∈ K ∨ a * b ∈ K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K' := (U ⊓ K).subgroupOf U with hK'
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU
  have hdvd : K'.index ∣ 3 ^ n := hn ▸ K'.index_dvd_card
  obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hi1 : i ≤ 1 := by
    by_contra h
    have : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hie] at this
    omega
  have hmemK : ∀ y : U, y ∈ K' → (y : X) ∈ K := fun y hy =>
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).2
  interval_cases i
  · exfalso
    rw [pow_zero, Subgroup.index_eq_one] at hie
    exact haK (hmemK ⟨a, ha⟩ (hie ▸ Subgroup.mem_top _))
  · rw [pow_one] at hie
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hdvd
      rw [hie] at hdvd
      omega
    have hmin : (Nat.card U).minFac = 3 := by
      rw [hn]
      exact Nat.Prime.pow_minFac Nat.prime_three hn0
    haveI : K'.Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hie, hmin])
    have hcq : Nat.card (U ⧸ K') = 3 := by rw [← Subgroup.index, hie]
    set qa := QuotientGroup.mk' K' ⟨a, ha⟩ with hqa
    set qb := QuotientGroup.mk' K' ⟨b, hb⟩ with hqb
    have hne : ∀ y : U, (y : X) ∉ K → QuotientGroup.mk' K' y ≠ 1 := fun y hy h1 =>
      hy (hmemK y ((QuotientGroup.eq_one_iff _).mp h1))
    have hob : orderOf qb = 3 := by
      have h := orderOf_dvd_natCard qb
      rw [hcq] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) (hne ⟨b, hb⟩ hbK)
      · exact h
    have hzp : qa ∈ Subgroup.zpowers qb := by
      have : Subgroup.zpowers qb = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hob, hcq])
      rw [this]
      trivial
    rw [mem_zpowers_iff_mem_range_orderOf, hob] at hzp
    simp only [Finset.mem_image, Finset.mem_range] at hzp
    obtain ⟨k, hk, hkq⟩ := hzp
    interval_cases k
    · exact (hne ⟨a, ha⟩ haK (hkq.symm.trans (pow_zero qb))).elim
    · left
      have h1 : QuotientGroup.mk' K' (⟨a, ha⟩ * (⟨b, hb⟩ : U)⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hqa, ← hqb, ← hkq, pow_one, mul_inv_cancel]
      exact hmemK _ ((QuotientGroup.eq_one_iff _).mp h1)
    · right
      have h1 : QuotientGroup.mk' K' (⟨a, ha⟩ * (⟨b, hb⟩ : U)) = 1 := by
        rw [map_mul, ← hqa, ← hqb, ← hkq, ← pow_succ]
        have := pow_orderOf_eq_one qb
        rwa [hob] at this
      exact hmemK _ ((QuotientGroup.eq_one_iff _).mp h1)

theorem exists_comm_center {A : Subgroup X} (hcard : Nat.card A = 1080)
    (hb : ∀ l ∈ A, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1)
    (hc : ∀ T : Subgroup X, T ≤ A → IsPGroup 3 T →
      Nat.card T ≤ 3 ^ 3 ∧ (IsMulCommutative T → Nat.card T ≤ 3 ^ 2))
    {r ζ : X} (hr : r ∈ A) (hrn : r ∉ Subgroup.centralizer (A : Set X)) (hr3 : r ^ 3 = 1)
    (hζA : ζ ∈ A) (hζC : ζ ∈ Subgroup.centralizer (A : Set X)) (hζ1 : ζ ≠ 1)
    (hζ3 : ζ ^ 3 = 1) :
    ∃ T₀ : Subgroup X, T₀ ≤ A ∧ IsPGroup 3 T₀ ∧ r ∈ T₀ ∧ ∃ x ∈ T₀,
      x * r * x⁻¹ * r⁻¹ ∈ Subgroup.centralizer (A : Set X) ∧ x * r * x⁻¹ * r⁻¹ ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hQc, hQe⟩ := card_sup_zpowers_rep hr hrn hr3 hζC hζ1 hζ3
  set Q := Subgroup.zpowers r ⊔ Subgroup.zpowers ζ with hQ
  have hQA : Q ≤ A := sup_le ((Subgroup.zpowers_le).mpr hr) ((Subgroup.zpowers_le).mpr hζA)
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card hQc
  have hQ'3 : IsPGroup 3 (Q.subgroupOf A) := hQ3.comap_of_injective A.subtype A.subtype_injective
  obtain ⟨S₀, hQS⟩ := hQ'3.exists_le_sylow
  set T₀ : Subgroup X := (S₀ : Subgroup A).map A.subtype with hT₀
  have hT₀A : T₀ ≤ A := Subgroup.map_subtype_le _
  have hT₀3 : IsPGroup 3 T₀ := S₀.isPGroup'.map _
  have hmemT : ∀ q ∈ Q, q ∈ T₀ := fun q hq =>
    ⟨⟨q, hQA hq⟩, hQS (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  have hrT : r ∈ T₀ := hmemT r (Subgroup.mem_sup_left (Subgroup.mem_zpowers r))
  have hζT : ζ ∈ T₀ := hmemT ζ (Subgroup.mem_sup_right (Subgroup.mem_zpowers ζ))
  have hT₀c : Nat.card T₀ = 3 ^ 3 := by
    have hce : Nat.card T₀ = Nat.card S₀ := Subgroup.card_map_of_injective A.subtype_injective
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S₀.isPGroup'
    have hle := (hc T₀ hT₀A hT₀3).1
    rw [hce, hk] at hle
    have hk3 : k ≤ 3 := by
      by_contra h
      have : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hmul := (S₀ : Subgroup A).card_mul_index
    rw [hk, hcard] at hmul
    have hnd := S₀.not_dvd_index
    rw [hce, hk]
    interval_cases k
    · exact absurd ⟨360, by omega⟩ hnd
    · exact absurd ⟨120, by omega⟩ hnd
    · exact absurd ⟨40, by omega⟩ hnd
    · rfl
  have hx : ∃ x ∈ T₀, x * r ≠ r * x := by
    by_contra hall
    push Not at hall
    have hy : ∃ y ∈ T₀, y ∉ Q := by
      by_contra hno
      push Not at hno
      have := Subgroup.card_le_of_le (show T₀ ≤ Q from hno)
      rw [hT₀c, hQc] at this
      norm_num at this
    obtain ⟨y, hyT, hyQ⟩ := hy
    have hy3 : y ^ 3 = 1 := hb y (hT₀A hyT) (by
      obtain ⟨k, hk⟩ := hT₀3 ⟨y, hyT⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩)
    have hQy : Q ≤ Subgroup.centralizer ({y} : Set X) := by
      refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      · exact (hall y hyT).symm
      · exact (Subgroup.mem_centralizer_iff.mp hζC y (hT₀A hyT)).symm
    obtain ⟨hWc, hWe⟩ := card_sup_zpowers_elem le_rfl hy3 hyQ hQy hQe
    have hWT : Q ⊔ Subgroup.zpowers y ≤ T₀ :=
      sup_le (fun q hq => hmemT q hq) ((Subgroup.zpowers_le).mpr hyT)
    have h9 := (hc _ (hWT.trans hT₀A) (hT₀3.to_le hWT)).2 hWe.1
    rw [hWc, hQc] at h9
    norm_num at h9
  obtain ⟨x, hxT, hxr⟩ := hx
  refine ⟨T₀, hT₀A, hT₀3, hrT, x, hxT, ?_, ?_⟩
  ·
    set π := (QuotientGroup.mk' (Subgroup.center A)).comp (Subgroup.inclusion hT₀A) with hπ
    have hker : (⟨ζ, hζT⟩ : T₀) ∈ π.ker := by
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hζC g g.2)
    have hkerne : π.ker ≠ ⊥ := by
      intro h
      have := (Subgroup.mem_bot.mp (h ▸ hker))
      exact hζ1 (congrArg Subtype.val this)
    have hkr := Subgroup.card_ker_mul_card_range π
    rw [hT₀c] at hkr
    have hkd : Nat.card π.ker ∣ 3 ^ 3 := ⟨_, hkr.symm⟩
    obtain ⟨j, hj, hje⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hkd
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hkerne (Subgroup.eq_bot_of_card_eq _ (by simpa using hje))
    have hrd : Nat.card π.range ∣ 3 ^ 3 := ⟨_, by rw [mul_comm] at hkr; exact hkr.symm⟩
    obtain ⟨m, hm, hme⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hrd
    rw [hje, hme, ← pow_add] at hkr
    have hjm : j + m = 3 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hkr
    have hcommR : IsMulCommutative π.range := by
      have hm2 : m ≤ 2 := by omega
      interval_cases m
      · haveI : Subsingleton π.range :=
          (Nat.card_eq_one_iff_unique.mp (by simpa using hme)).1
        exact ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
      · haveI : IsCyclic π.range := isCyclic_of_prime_card (p := 3) (by simpa using hme)
        infer_instance
      · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hme
    have hc := hcommR.is_comm.comm ⟨π ⟨x, hxT⟩, ⟨_, rfl⟩⟩ ⟨π ⟨r, hrT⟩, ⟨_, rfl⟩⟩
    have hc' : π (⟨x, hxT⟩ * ⟨r, hrT⟩ * (⟨x, hxT⟩ : T₀)⁻¹ * (⟨r, hrT⟩ : T₀)⁻¹) = 1 := by
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at this
      simp only [map_mul, map_inv, this]
      group
    rw [hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_center_iff] at hc'
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := congrArg Subtype.val (hc' ⟨g, hg⟩)
    simpa using this
  · intro h1
    apply hxr
    have : x * r * x⁻¹ = r := by
      have := congrArg (· * r) h1
      simpa using this
    calc x * r = x * r * x⁻¹ * x := by group
      _ = r * x := by rw [this]

theorem conj_mem_centralizer_iff {A : Subgroup X} (g t : X) :
    g * t * g⁻¹ ∈ Subgroup.centralizer (A : Set X) ↔
      t ∈ Subgroup.centralizer ((A.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup X) : Set X) := by
  simp only [Subgroup.mem_centralizer_iff, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  refine forall₂_congr fun a _ => ?_
  constructor <;> intro h
  · calc g⁻¹ * a * g * t = g⁻¹ * (a * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * a) * g := by rw [h]
      _ = t * (g⁻¹ * a * g) := by group
  · calc a * (g * t * g⁻¹) = g * ((g⁻¹ * a * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
      _ = g * t * g⁻¹ * a := by group

theorem not_mem_centralizer_of_noncomm {A : Subgroup X} {r v : X} (hr : r ∈ A)
    (hrv : v * r ≠ r * v) :
    v ∉ Subgroup.centralizer (A : Set X) ∧ r * v⁻¹ ∉ Subgroup.centralizer (A : Set X) ∧
      r * v ∉ Subgroup.centralizer (A : Set X) := by
  refine ⟨fun h => hrv (Subgroup.mem_centralizer_iff.mp h r hr).symm, fun h => ?_, fun h => ?_⟩
  · have h' := Subgroup.mem_centralizer_iff.mp h r hr
    have h'' : v⁻¹ * r = r * v⁻¹ := by
      have := mul_left_cancel (a := r) (show r * (r * v⁻¹) = r * (v⁻¹ * r) by
        rw [h']; group)
      exact this.symm
    apply hrv
    calc v * r = v * (r * v⁻¹) * v := by group
      _ = v * (v⁻¹ * r) * v := by rw [h'']
      _ = r * v := by group
  · have h' := Subgroup.mem_centralizer_iff.mp h r hr
    apply hrv
    have := mul_left_cancel (a := r) (show r * (r * v) = r * (v * r) by rw [h']; group)
    exact this.symm

theorem false_of_conj_pair {U A B : Subgroup X} (hU : IsPGroup 3 U)
    (hidx : ((U ⊓ Subgroup.centralizer (A : Set X)).subgroupOf U).index ≤ 3) {g r v : X}
    (hiff : ∀ t, g * t * g⁻¹ ∈ Subgroup.centralizer (A : Set X) ↔
      t ∈ Subgroup.centralizer (B : Set X))
    (hr : r ∈ B) (hrn : r ∉ Subgroup.centralizer (B : Set X)) (hrv : v * r ≠ r * v)
    (hgr : g * r * g⁻¹ ∈ U) (hgv : g * v * g⁻¹ ∈ U) : False := by
  obtain ⟨hv, hrv', hrv''⟩ := not_mem_centralizer_of_noncomm hr hrv
  rcases mul_mem_or_of_index_le_three hU hidx hgr hgv (by rwa [hiff]) (by rwa [hiff]) with h | h
  · rw [show g * r * g⁻¹ * (g * v * g⁻¹)⁻¹ = g * (r * v⁻¹) * g⁻¹ by group, hiff] at h
    exact hrv' h
  · rw [show g * r * g⁻¹ * (g * v * g⁻¹) = g * (r * v) * g⁻¹ by group, hiff] at h
    exact hrv'' h

theorem eq_or_eq_inv_of_mem_zpowers {ζ c c' : X} (hζ3 : ζ ^ 3 = 1)
    (hc : c ∈ Subgroup.zpowers ζ) (hc' : c' ∈ Subgroup.zpowers ζ) (hc1 : c ≠ 1)
    (hc'1 : c' ≠ 1) : c' = c ∨ c' = c⁻¹ := by
  classical
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hc
    exact hc1 hc
  have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  rw [mem_zpowers_iff_mem_range_orderOf, hζo] at hc hc'
  simp only [Finset.mem_image, Finset.mem_range] at hc hc'
  obtain ⟨i, hi, rfl⟩ := hc
  obtain ⟨j, hj, rfl⟩ := hc'
  interval_cases i
  · exact absurd (pow_zero ζ) hc1
  · interval_cases j
    · exact absurd (pow_zero ζ) hc'1
    · left; rfl
    · right; rw [pow_one, eq_inv_iff_mul_eq_one, ← pow_succ]; exact hζ3
  · interval_cases j
    · exact absurd (pow_zero ζ) hc'1
    · right; rw [pow_one, eq_inv_iff_mul_eq_one, ← pow_succ']; exact hζ3
    · left; rfl

theorem exists_conj_eq_mul {A : Subgroup X} (hcard : Nat.card A = 1080)
    (hb : ∀ l ∈ A, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1)
    (hc : ∀ T : Subgroup X, T ≤ A → IsPGroup 3 T →
      Nat.card T ≤ 3 ^ 3 ∧ (IsMulCommutative T → Nat.card T ≤ 3 ^ 2))
    {r ζ ω : X} (hr : r ∈ A) (hrn : r ∉ Subgroup.centralizer (A : Set X)) (hr3 : r ^ 3 = 1)
    (hζA : ζ ∈ A) (hζC : ζ ∈ Subgroup.centralizer (A : Set X)) (hζ1 : ζ ≠ 1)
    (hζ3 : ζ ^ 3 = 1) (hω3 : ω ^ 3 = 1)
    (hZ : ∀ y ∈ A, y ∈ Subgroup.centralizer (A : Set X) → y ∈ Subgroup.zpowers ω)
    {c' : X} (hc' : c' ∈ Subgroup.zpowers ω) (hc'1 : c' ≠ 1) :
    ∃ T₀ : Subgroup X, T₀ ≤ A ∧ IsPGroup 3 T₀ ∧ r ∈ T₀ ∧ ∃ x ∈ T₀, x * r * x⁻¹ = c' * r := by
  obtain ⟨T₀, hT₀A, hT₀3, hrT, x, hxT, hcC, hc1⟩ :=
    exists_comm_center hcard hb hc hr hrn hr3 hζA hζC hζ1 hζ3
  refine ⟨T₀, hT₀A, hT₀3, hrT, ?_⟩
  have hxA := hT₀A hxT
  have hcA : x * r * x⁻¹ * r⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (A.mul_mem hxA hr) (A.inv_mem hxA)) (A.inv_mem hr)
  have hcω := hZ _ hcA hcC
  generalize hcd : x * r * x⁻¹ * r⁻¹ = c at hcC hc1 hcA hcω
  have hxr : x * r * x⁻¹ = c * r := by rw [← hcd]; group
  have hcx : x * c = c * x := (Subgroup.mem_centralizer_iff.mp hcC x hxA)
  rcases eq_or_eq_inv_of_mem_zpowers hω3 hcω hc' hc1 hc'1 with rfl | rfl
  · exact ⟨x, hxT, hxr⟩
  · refine ⟨x⁻¹, T₀.inv_mem hxT, ?_⟩
    have key : c * x⁻¹ = x⁻¹ * c := by
      calc c * x⁻¹ = x⁻¹ * (x * c) * x⁻¹ := by group
        _ = x⁻¹ * (c * x) * x⁻¹ := by rw [hcx]
        _ = x⁻¹ * c := by group
    calc x⁻¹ * r * x⁻¹⁻¹ = c⁻¹ * (c * x⁻¹) * r * x := by group
      _ = c⁻¹ * (x⁻¹ * c) * r * x := by rw [key]
      _ = c⁻¹ * (x⁻¹ * (c * r) * x) := by group
      _ = c⁻¹ * (x⁻¹ * (x * r * x⁻¹) * x) := by rw [hxr]
      _ = c⁻¹ * r := by group

theorem conj_eq_self_of_comm {y t : X} (h : y * t = t * y) : y * t * y⁻¹ = t := by
  rw [h]; group

theorem false_of_two_blocks {A₀ A₁ U : Subgroup X} {zb r₀ r₁ ζ ζ₁ : X}
    (hcard₀ : Nat.card A₀ = 1080) (hcard₁ : Nat.card A₁ = 1080)
    (hb₀ : ∀ l ∈ A₀, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1)
    (hb₁ : ∀ l ∈ A₁, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1)
    (hc₀ : ∀ T : Subgroup X, T ≤ A₀ → IsPGroup 3 T →
      Nat.card T ≤ 3 ^ 3 ∧ (IsMulCommutative T → Nat.card T ≤ 3 ^ 2))
    (hc₁ : ∀ T : Subgroup X, T ≤ A₁ → IsPGroup 3 T →
      Nat.card T ≤ 3 ^ 3 ∧ (IsMulCommutative T → Nat.card T ≤ 3 ^ 2))
    (h01 : A₁ ≤ Subgroup.centralizer (A₀ : Set X))
    (hr₀ : r₀ ∈ A₀) (hr₀n : r₀ ∉ Subgroup.centralizer (A₀ : Set X)) (hr₀3 : r₀ ^ 3 = 1)
    (hr₀z : r₀⁻¹ * zb ∈ Subgroup.centralizer (A₀ : Set X))
    (hr₁ : r₁ ∈ A₁) (hr₁n : r₁ ∉ Subgroup.centralizer (A₁ : Set X)) (hr₁3 : r₁ ^ 3 = 1)
    (hr₁z : r₁⁻¹ * zb ∈ Subgroup.centralizer (A₁ : Set X))
    (hζA : ζ ∈ A₀) (hζC : ζ ∈ Subgroup.centralizer (A₀ : Set X)) (hζ1 : ζ ≠ 1)
    (hζ3 : ζ ^ 3 = 1)
    (hZ₀ : ∀ y ∈ A₀, y ∈ Subgroup.centralizer (A₀ : Set X) → y ∈ Subgroup.zpowers ζ)
    (hζ₁A : ζ₁ ∈ A₁) (hζ₁C : ζ₁ ∈ Subgroup.centralizer (A₁ : Set X)) (hζ₁1 : ζ₁ ≠ 1)
    (hζ₁3 : ζ₁ ^ 3 = 1)
    (hZ₁ : ∀ y ∈ A₁, y ∈ Subgroup.centralizer (A₁ : Set X) → y ∈ Subgroup.zpowers ζ₁)
    (hrk : ∀ E : Subgroup X, E ≤ Subgroup.centralizer ({zb} : Set X) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3)
    (hU : IsPGroup 3 U)
    (hSyl : ∀ T : Subgroup X, T ≤ Subgroup.centralizer ({zb} : Set X) → IsPGroup 3 T →
      ∃ g ∈ Subgroup.centralizer ({zb} : Set X), T.map (MulAut.conj g).toMonoidHom ≤ U)
    (horb : ∀ g ∈ Subgroup.centralizer ({zb} : Set X),
      A₀.map (MulAut.conj g⁻¹).toMonoidHom = A₀ ∨ A₀.map (MulAut.conj g⁻¹).toMonoidHom = A₁)
    (hidx : ((U ⊓ Subgroup.centralizer (A₀ : Set X)).subgroupOf U).index ≤ 3) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h10 : A₀ ≤ Subgroup.centralizer (A₁ : Set X) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (Subgroup.mem_centralizer_iff.mp (h01 hb) a ha).symm
  have hcomm : ∀ a ∈ A₀, ∀ b ∈ A₁, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (h01 hb) a ha
  have hr₀zc := d1_mem_centralizer_of_rep hr₀ hr₀z
  have hr₁zc := d1_mem_centralizer_of_rep hr₁ hr₁z
  have hζz := d1_mem_centralizer_of_rep_center hr₀ hr₀z hζA hζC
  have hζ₁z := d1_mem_centralizer_of_rep_center hr₁ hr₁z hζ₁A hζ₁C
  have hζ₁ζ : ζ₁ ∈ Subgroup.zpowers ζ := by
    by_cases hζ₁A₀ : ζ₁ ∈ A₀
    · exact hZ₀ ζ₁ hζ₁A₀ (h01 hζ₁A)
    exfalso
    obtain ⟨hQ₀c, hQ₀e⟩ := card_sup_zpowers_rep hr₀ hr₀n hr₀3 hζC hζ1 hζ3
    obtain ⟨hQ₁c, hQ₁e⟩ := card_sup_zpowers_rep hr₁ hr₁n hr₁3 hζ₁C hζ₁1 hζ₁3
    have hQ₀A : Subgroup.zpowers r₀ ⊔ Subgroup.zpowers ζ ≤ A₀ :=
      sup_le (Subgroup.zpowers_le.mpr hr₀) (Subgroup.zpowers_le.mpr hζA)
    have hQ₁A : Subgroup.zpowers r₁ ⊔ Subgroup.zpowers ζ₁ ≤ A₁ :=
      sup_le (Subgroup.zpowers_le.mpr hr₁) (Subgroup.zpowers_le.mpr hζ₁A)
    have hinf : (Subgroup.zpowers r₀ ⊔ Subgroup.zpowers ζ) ⊓
        (Subgroup.zpowers r₁ ⊔ Subgroup.zpowers ζ₁) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      by_contra hy1
      have hyA₀ : y ∈ A₀ := hQ₀A hy.1
      have hyz : y ∈ Subgroup.zpowers ζ₁ := hZ₁ y (hQ₁A hy.2) (h10 hyA₀)
      rcases eq_or_eq_inv_of_mem_zpowers hζ₁3 hyz (Subgroup.mem_zpowers ζ₁) hy1 hζ₁1 with h | h
      · exact hζ₁A₀ (h ▸ hyA₀)
      · exact hζ₁A₀ (h ▸ A₀.inv_mem hyA₀)
    have hc := card_sup_of_le_centralizer
      ((hQ₁A.trans h01).trans (Subgroup.centralizer_le hQ₀A)) hinf
    have he := d1_isElemAbelian_sup_of_le_centralizer hQ₀e hQ₁e
      ((hQ₀A.trans h10).trans (Subgroup.centralizer_le hQ₁A))
    have hz : (Subgroup.zpowers r₀ ⊔ Subgroup.zpowers ζ) ⊔
        (Subgroup.zpowers r₁ ⊔ Subgroup.zpowers ζ₁) ≤ Subgroup.centralizer ({zb} : Set X) :=
      sup_le (sup_le (Subgroup.zpowers_le.mpr hr₀zc) (Subgroup.zpowers_le.mpr hζz))
        (sup_le (Subgroup.zpowers_le.mpr hr₁zc) (Subgroup.zpowers_le.mpr hζ₁z))
    have := hrk _ hz he
    rw [hc, hQ₀c, hQ₁c] at this
    norm_num at this
  obtain ⟨T₀, hT₀A, hT₀3, hrT₀, x₀, hx₀T, hx₀⟩ := exists_conj_eq_mul hcard₀ hb₀ hc₀ hr₀ hr₀n
    hr₀3 hζA hζC hζ1 hζ3 hζ3 hZ₀ (Subgroup.mem_zpowers ζ) hζ1
  have hzle : Subgroup.zpowers ζ₁ ≤ Subgroup.zpowers ζ := Subgroup.zpowers_le.mpr hζ₁ζ
  obtain ⟨T₁, hT₁A, hT₁3, hrT₁, x₁, hx₁T, hx₁⟩ := exists_conj_eq_mul hcard₁ hb₁ hc₁ hr₁ hr₁n
    hr₁3 hζ₁A hζ₁C hζ₁1 hζ₁3 hζ3 (fun y hy hyC => hzle (hZ₁ y hy hyC))
    (Subgroup.inv_mem _ (Subgroup.mem_zpowers ζ)) (inv_ne_one.mpr hζ1)
  have hx₀A := hT₀A hx₀T
  have hx₁A := hT₁A hx₁T
  have hζCA₁ : ζ ∈ Subgroup.centralizer (A₁ : Set X) := h10 hζA
  set d := r₁⁻¹ * (r₀⁻¹ * zb) with hd
  have hdC₀ : d ∈ Subgroup.centralizer (A₀ : Set X) :=
    Subgroup.mul_mem _ (h01 (A₁.inv_mem hr₁)) hr₀z
  have hdC₁ : d ∈ Subgroup.centralizer (A₁ : Set X) := by
    have : d = r₀⁻¹ * (r₁⁻¹ * zb) := by
      rw [hd, ← mul_assoc, ← mul_assoc, ← mul_inv_rev, ← mul_inv_rev,
        hcomm r₀ hr₀ r₁ hr₁]
    rw [this]
    exact Subgroup.mul_mem _ (h10 (A₀.inv_mem hr₀)) hr₁z
  have hzb : zb = r₀ * r₁ * d := by rw [hd]; group
  have cd₀ : x₀ * d = d * x₀ := (Subgroup.mem_centralizer_iff.mp hdC₀ x₀ hx₀A)
  have cd₁ : x₁ * d = d * x₁ := (Subgroup.mem_centralizer_iff.mp hdC₁ x₁ hx₁A)
  set u := x₀ * x₁ with hu
  have e1 : x₁ * zb * x₁⁻¹ = r₀ * (ζ⁻¹ * r₁) * d := by
    rw [hzb, show x₁ * (r₀ * r₁ * d) * x₁⁻¹ =
      (x₁ * r₀ * x₁⁻¹) * (x₁ * r₁ * x₁⁻¹) * (x₁ * d * x₁⁻¹) by group, hx₁,
      conj_eq_self_of_comm (hcomm r₀ hr₀ x₁ hx₁A).symm, conj_eq_self_of_comm cd₁]
  have e2 : x₀ * (r₀ * (ζ⁻¹ * r₁) * d) * x₀⁻¹ = zb := by
    rw [show x₀ * (r₀ * (ζ⁻¹ * r₁) * d) * x₀⁻¹ =
      (x₀ * r₀ * x₀⁻¹) * (x₀ * ζ⁻¹ * x₀⁻¹) * (x₀ * r₁ * x₀⁻¹) * (x₀ * d * x₀⁻¹) by group, hx₀,
      conj_eq_self_of_comm (hcomm x₀ hx₀A r₁ hr₁), conj_eq_self_of_comm cd₀,
      conj_eq_self_of_comm (Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hζC) x₀ hx₀A),
      hzb]
    have hζr : ζ * r₀ = r₀ * ζ := (Subgroup.mem_centralizer_iff.mp hζC r₀ hr₀).symm
    calc ζ * r₀ * ζ⁻¹ * r₁ * d = (ζ * r₀) * ζ⁻¹ * r₁ * d := rfl
      _ = r₀ * ζ * ζ⁻¹ * r₁ * d := by rw [hζr]
      _ = r₀ * r₁ * d := by group
  have huz : u ∈ Subgroup.centralizer ({zb} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : u * zb * u⁻¹ = zb := by
      rw [hu, show x₀ * x₁ * zb * (x₀ * x₁)⁻¹ = x₀ * (x₁ * zb * x₁⁻¹) * x₀⁻¹ by group, e1, e2]
    calc u * zb = u * zb * u⁻¹ * u := by group
      _ = zb * u := by rw [h]
  have hur₀ : u * r₀ ≠ r₀ * u := by
    intro h
    have h' : u * r₀ * u⁻¹ = r₀ := conj_eq_self_of_comm h
    rw [hu, show x₀ * x₁ * r₀ * (x₀ * x₁)⁻¹ = x₀ * (x₁ * r₀ * x₁⁻¹) * x₀⁻¹ by group,
      conj_eq_self_of_comm (hcomm r₀ hr₀ x₁ hx₁A).symm, hx₀] at h'
    exact hζ1 (by simpa using h')
  have hur₁ : u * r₁ ≠ r₁ * u := by
    intro h
    have h' : u * r₁ * u⁻¹ = r₁ := conj_eq_self_of_comm h
    rw [hu, show x₀ * x₁ * r₁ * (x₀ * x₁)⁻¹ = x₀ * (x₁ * r₁ * x₁⁻¹) * x₀⁻¹ by group, hx₁,
      show x₀ * (ζ⁻¹ * r₁) * x₀⁻¹ = (x₀ * ζ⁻¹ * x₀⁻¹) * (x₀ * r₁ * x₀⁻¹) by group,
      conj_eq_self_of_comm (hcomm x₀ hx₀A r₁ hr₁),
      conj_eq_self_of_comm (Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hζC) x₀ hx₀A)]
      at h'
    exact hζ1 (inv_eq_one.mp (by simpa using h'))
  have hT01 : IsPGroup 3 (T₀ ⊔ T₁ : Subgroup X) := hT₀3.to_sup_of_normal_right' hT₁3
    (fun a ha => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hcomm a (hT₀A ha) b (hT₁A hb)).symm))
  set T := (T₀ ⊔ T₁) ⊓ Subgroup.centralizer ({zb} : Set X) with hT
  obtain ⟨g, hg, hTU⟩ := hSyl T inf_le_right (hT01.to_le inf_le_left)
  have hgU : ∀ t ∈ T, g * t * g⁻¹ ∈ U := fun t ht => by
    have := hTU (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ht)
    simpa using this
  have hr₀T : r₀ ∈ T := ⟨Subgroup.mem_sup_left hrT₀, hr₀zc⟩
  have hr₁T : r₁ ∈ T := ⟨Subgroup.mem_sup_right hrT₁, hr₁zc⟩
  have huT : u ∈ T := ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left hx₀T)
    (Subgroup.mem_sup_right hx₁T), huz⟩
  rcases horb g hg with h | h
  · exact false_of_conj_pair hU hidx (B := A₀) (fun t => by rw [conj_mem_centralizer_iff, h])
      hr₀ hr₀n hur₀ (hgU _ hr₀T) (hgU _ huT)
  · exact false_of_conj_pair hU hidx (B := A₁) (fun t => by rw [conj_mem_centralizer_iff, h])
      hr₁ hr₁n hur₁ (hgU _ hr₁T) (hgU _ huT)

theorem map_conj_map_conj_inv (A : Subgroup X) (μ : X) :
    (A.map (MulAut.conj μ).toMonoidHom).map (MulAut.conj μ⁻¹).toMonoidHom = A := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id A
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, MonoidHom.id_apply]
  group

theorem mem_zpowers_of_card_center {A : Subgroup X} (hZ : Nat.card (Subgroup.center A) = 3)
    {ζ : X} (hζA : ζ ∈ A) (hζC : ζ ∈ Subgroup.centralizer (A : Set X)) (hζ1 : ζ ≠ 1)
    (hζ3 : ζ ^ 3 = 1) :
    ∀ y ∈ A, y ∈ Subgroup.centralizer (A : Set X) → y ∈ Subgroup.zpowers ζ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro y hyA hyC
  have hmemZ : ∀ w (hw : w ∈ A), w ∈ Subgroup.centralizer (A : Set X) →
      (⟨w, hw⟩ : A) ∈ Subgroup.center A := fun w hw hwC =>
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_centralizer_iff.mp hwC g g.2)
  have hζo : orderOf (⟨ζ, hζA⟩ : A) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hζ3)) (fun h => hζ1 (congrArg Subtype.val h))
  have hle : Subgroup.zpowers (⟨ζ, hζA⟩ : A) ≤ Subgroup.center A :=
    Subgroup.zpowers_le.mpr (hmemZ ζ hζA hζC)
  have heq : Subgroup.zpowers (⟨ζ, hζA⟩ : A) = Subgroup.center A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, Nat.card_zpowers, hζo])
  have hy : (⟨y, hyA⟩ : A) ∈ Subgroup.zpowers (⟨ζ, hζA⟩ : A) := heq ▸ hmemZ y hyA hyC
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem conj_block_facts {A A' : Subgroup X} (μ : X)
    (hA' : A' = A.map (MulAut.conj μ).toMonoidHom) (hcard : Nat.card A = 1080)
    (hb : ∀ l ∈ A, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1)
    (hc : ∀ T : Subgroup X, T ≤ A → IsPGroup 3 T →
      Nat.card T ≤ 3 ^ 3 ∧ (IsMulCommutative T → Nat.card T ≤ 3 ^ 2))
    {ζ : X} (hζA : ζ ∈ A) (hζC : ζ ∈ Subgroup.centralizer (A : Set X)) (hζ1 : ζ ≠ 1)
    (hζ3 : ζ ^ 3 = 1)
    (hZ : ∀ y ∈ A, y ∈ Subgroup.centralizer (A : Set X) → y ∈ Subgroup.zpowers ζ) :
    Nat.card A' = 1080 ∧ (∀ l ∈ A', (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1) ∧
      (∀ T : Subgroup X, T ≤ A' → IsPGroup 3 T →
        Nat.card T ≤ 3 ^ 3 ∧ (IsMulCommutative T → Nat.card T ≤ 3 ^ 2)) ∧
      μ * ζ * μ⁻¹ ∈ A' ∧ μ * ζ * μ⁻¹ ∈ Subgroup.centralizer (A' : Set X) ∧
      μ * ζ * μ⁻¹ ≠ 1 ∧ (μ * ζ * μ⁻¹) ^ 3 = 1 ∧
      ∀ y ∈ A', y ∈ Subgroup.centralizer (A' : Set X) → y ∈ Subgroup.zpowers (μ * ζ * μ⁻¹) := by
  have hback : A'.map (MulAut.conj μ⁻¹).toMonoidHom = A := by
    rw [hA']; exact map_conj_map_conj_inv A μ
  have hinj : ∀ ν : X, Function.Injective (MulAut.conj ν).toMonoidHom :=
    fun ν => (MulAut.conj ν).injective
  have hCiff : ∀ a : X, μ * a * μ⁻¹ ∈ Subgroup.centralizer (A' : Set X) ↔
      a ∈ Subgroup.centralizer (A : Set X) := fun a => by
    rw [conj_mem_centralizer_iff, hback]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hA', Subgroup.card_map_of_injective (hinj μ), hcard]
  · intro l hl hp
    exact d1_pow_three_of_mem_map_conj hb (hA' ▸ hl) hp
  · intro T hT hT3
    have hT'A : T.map (MulAut.conj μ⁻¹).toMonoidHom ≤ A := hback ▸ Subgroup.map_mono hT
    have hcT : Nat.card (T.map (MulAut.conj μ⁻¹).toMonoidHom) = Nat.card T :=
      Subgroup.card_map_of_injective (hinj μ⁻¹)
    obtain ⟨h1, h2⟩ := hc _ hT'A (hT3.map _)
    rw [hcT] at h1 h2
    exact ⟨h1, fun hcomm => h2 inferInstance⟩
  · rw [hA']; exact ⟨ζ, hζA, by simp [MulAut.conj_apply]⟩
  · exact (hCiff ζ).mpr hζC
  · intro h
    apply hζ1
    calc ζ = μ⁻¹ * (μ * ζ * μ⁻¹) * μ := by group
      _ = 1 := by rw [h]; group
  · rw [conj_pow, hζ3]; group
  · intro y hy hyC
    rw [hA'] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyC ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hZ a ha ((hCiff a).mp hyC))
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [conj_zpow, hk]⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6

open CFSG.Open CFSG.AGLEmbedding

section Concrete

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_le_barR {M R : Subgroup G} {z : G} (hzM : z ∈ M) (hz3 : z ^ 3 = 1)
    (hRM : R ≤ M) (hB0 : D1CzB0 3 R z) :
    IsPGroup 3 ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hRM)).range ∧
    ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      T ≤ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      IsPGroup 3 T →
      ∃ g ∈ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        T.map (MulAut.conj g).toMonoidHom ≤
          ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hRM)).range := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Cz := Subgroup.centralizer ({z} : Set G) with hCz
  set Cb := Subgroup.centralizer ({mk ⟨z, hzM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  set fR := mk.comp (Subgroup.inclusion hRM) with hfR
  obtain ⟨Q, hQR⟩ := hB0
  have hR3 : IsPGroup 3 R := hQR ▸ Q.isPGroup'.map _
  have hRz : R ≤ Cz := hQR ▸ Subgroup.map_subtype_le _
  have hcardR : Nat.card R = Nat.card Q :=
    hQR ▸ Subgroup.card_map_of_injective Cz.subtype_injective
  have hRmax : ∀ T : Subgroup G, T ≤ Cz → IsPGroup 3 T → Nat.card T ≤ Nat.card R := by
    intro T hT hT3
    obtain ⟨S', hS'⟩ := (hT3.comap_of_injective Cz.subtype Cz.subtype_injective).exists_le_sylow
    have h1 : Nat.card T = Nat.card (T.subgroupOf Cz) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv).symm
    rw [h1, hcardR]
    calc Nat.card (T.subgroupOf Cz) ≤ Nat.card S' := Subgroup.card_le_of_le hS'
      _ = Nat.card Q := by rw [S'.card_eq_multiplicity, Q.card_eq_multiplicity]
  have hYmax : ∀ Y : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Y ≤ Cb → IsPGroup 3 Y →
      Nat.card Y ≤ Nat.card R := fun Y hY hY3 =>
    card_le_of_le_centralizer_barM_pgroup hzM hz3 hRmax hY hY3
  have hinj : Function.Injective fR := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have h2 : (⟨a, hRM a.2⟩ : M) ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff _).mp ha
    obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥M) ⟨_, h2⟩
    obtain ⟨k, hk⟩ := hR3 a
    have hj1 := congrArg Subtype.val (congrArg Subtype.val hj)
    have hj' : a ^ 2 ^ j = 1 := Subtype.ext (by simpa using hj1)
    have hcp : Nat.Coprime (3 ^ k) (2 ^ j) := Nat.Coprime.pow k j (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcp
      (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hj'))
  have hUcard : Nat.card fR.range = Nat.card R :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hU3 : IsPGroup 3 fR.range := by
    rintro ⟨_, a, rfl⟩
    obtain ⟨k, hk⟩ := hR3 a
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, hk, map_one]; rfl)⟩
  have hUCb : fR.range ≤ Cb := by
    rintro _ ⟨a, rfl⟩
    have hc : (⟨a, hRM a.2⟩ : M) * ⟨z, hzM⟩ = ⟨z, hzM⟩ * ⟨a, hRM a.2⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hRz a.2))
    rw [hCb, Subgroup.mem_centralizer_singleton_iff]
    show mk ⟨a, hRM a.2⟩ * mk ⟨z, hzM⟩ = mk ⟨z, hzM⟩ * mk ⟨a, hRM a.2⟩
    rw [← map_mul, ← map_mul, hc]
  refine ⟨hU3, fun T hT hT3 => ?_⟩
  have hU'3 : IsPGroup 3 (fR.range.subgroupOf Cb) :=
    hU3.comap_of_injective Cb.subtype Cb.subtype_injective
  obtain ⟨S, hUS⟩ := hU'3.exists_le_sylow
  have hSU : (S : Subgroup Cb) = fR.range.subgroupOf Cb := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hUS ?_
    have h1 : Nat.card (fR.range.subgroupOf Cb) = Nat.card fR.range :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUCb).toEquiv
    have h2 : Nat.card ((S : Subgroup Cb).map Cb.subtype) = Nat.card S :=
      Subgroup.card_map_of_injective Cb.subtype_injective
    rw [h1, hUcard, ← h2]
    exact hYmax _ (Subgroup.map_subtype_le _) (S.isPGroup'.map _)
  obtain ⟨S₂, hTS₂⟩ := (hT3.comap_of_injective Cb.subtype Cb.subtype_injective).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Cb S₂ S
  refine ⟨c, c.2, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have ht' : (⟨t, hT ht⟩ : Cb) ∈ T.subgroupOf Cb := Subgroup.mem_subgroupOf.mpr ht
  have hmem := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ (hTS₂ ht')
  change _ ∈ ((c • S₂ : Sylow 3 Cb) : Subgroup Cb) at hmem
  rw [hc, hSU, MulAut.smul_def, MulAut.conj_apply, Subgroup.mem_subgroupOf] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem normal_of_threeASix {P : Sylow 3 G} {M H R : Subgroup G}
    (h : D1PhaseThree 3 P M H R) (hThree : KFactBlockThreeASix)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q)
    {z : G} (hzM : z ∈ M) (hz3 : z ^ 3 = 1) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hin : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hrk : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3)
    (hB0 : D1CzB0 3 R z) (hRM : R ≤ M)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hZ : Nat.card (Subgroup.center ↥(barM M L)) = 3)
    (hA6 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    (hidx : ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hRM))).index ≤ 3) :
    (L.subgroupOf M).Normal := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hL.le]
  intro m hmM
  by_contra hmL
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set zb := mk ⟨z, hzM⟩ with hzb
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hzb3 : zb ^ 3 = 1 := by
    have h1 : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [hzb, ← map_pow, h1, map_one]
  have hnC : ∀ L : Subgroup G, IsWeakSBlock M S L →
      zb ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L hL =>
    h.not_mem_centralizer_block hp hp2 hzM hz hCz hL
  set A₀ := barM M L with hA₀
  obtain ⟨-, hb, hc⟩ := hThree G M L hL.toIsTwoPrimeComponent hZ hA6
  have hcard : Nat.card A₀ = 1080 := by
    obtain ⟨φ⟩ := hA6
    rw [(Subgroup.center A₀).card_eq_card_quotient_mul_card_subgroup, hZ,
      Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  obtain ⟨ζ, hζA, hζC, hζ1, hζ3⟩ := exists_center_of_card hZ
  have hZ₀ := mem_zpowers_of_card_center hZ hζA hζC hζ1 hζ3
  obtain ⟨r₀, hr₀A, hr₀p, hr₀c, hr₀n⟩ := exists_rep_of_mem_sup (hin L hL) hzb3 (hnC L hL)
  have hr₀3 : r₀ ^ 3 = 1 := hb r₀ hr₀A hr₀p
  obtain ⟨hE₀c, hE₀e⟩ := card_sup_zpowers_rep hr₀A hr₀n hr₀3 hζC hζ1 hζ3
  have hE₀A : Subgroup.zpowers r₀ ⊔ Subgroup.zpowers ζ ≤ A₀ :=
    sup_le ((Subgroup.zpowers_le).mpr hr₀A) ((Subgroup.zpowers_le).mpr hζA)
  have hE₀3 : IsPGroup 3 (Subgroup.zpowers r₀ ⊔ Subgroup.zpowers ζ : Subgroup _) :=
    fun x => ⟨1, Subtype.ext (by simpa using hE₀e.2 x x.2)⟩
  have hE₀nc := not_isCyclic_of_isElemAbelian Nat.prime_three hE₀e le_rfl hE₀c
  have hconjW : ∀ n : G, n ∈ M → IsWeakSBlock M S (L.map (MulAut.conj n).toMonoidHom) :=
    fun n hn => D1PhaseThree.isWeakSBlock_map_conj_of_cyc h hcyc hL hE₀A hE₀3 hE₀nc hn
  have hbne : ∀ {X Y : Subgroup G}, IsWeakSBlock M S X → IsWeakSBlock M S Y → X ≠ Y →
      barM M X ≠ barM M Y := fun hX hY hXY he =>
    hXY (hX.toIsTwoPrimeComponent.eq_of_barM_eq hY.toIsTwoPrimeComponent he)
  have hL₁w := hconjW m hmM
  have hne : L ≠ L.map (MulAut.conj m).toMonoidHom := by
    intro he
    apply hmL
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [he]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    · intro hx
      rw [he] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := (MulAut.conj m).injective (by simpa [MulAut.conj_apply] using hyx)
      exact this ▸ hy
  set A₁ := barM M (L.map (MulAut.conj m).toMonoidHom) with hA₁
  have h01 : A₁ ≤ Subgroup.centralizer (A₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    le_centralizer_of_component_ne hL₁w.component hL.component (hbne hL₁w hL hne.symm)
  have hA₁eq : A₁ = A₀.map (MulAut.conj (mk ⟨m, hmM⟩)).toMonoidHom := barM_map_conj hmM L
  obtain ⟨hcard₁, hb₁, hc₁, hζ₁A, hζ₁C, hζ₁1, hζ₁3, hZ₁⟩ :=
    conj_block_facts (mk ⟨m, hmM⟩) hA₁eq hcard hb hc hζA hζC hζ1 hζ3 hZ₀
  obtain ⟨r₁, hr₁A, hr₁p, hr₁c, hr₁n⟩ := exists_rep_of_mem_sup (hin _ hL₁w) hzb3 (hnC _ hL₁w)
  have hr₁3 : r₁ ^ 3 = 1 := hb₁ r₁ hr₁A hr₁p
  have hrk' : ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      E ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3 := fun E hE he => card_le_of_le_centralizer_barM hzM hz3 hrk hE he
  obtain ⟨hU3, hSyl⟩ := exists_conj_le_barR hzM hz3 hRM hB0
  have horb : ∀ g ∈ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      A₀.map (MulAut.conj g⁻¹).toMonoidHom = A₀ ∨ A₀.map (MulAut.conj g⁻¹).toMonoidHom = A₁ := by
    intro g _
    obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) g⁻¹
    have hL₂w := hconjW n n.2
    have hA₂eq : barM M (L.map (MulAut.conj (n : G)).toMonoidHom) =
        A₀.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [barM_map_conj n.2 L, Subtype.coe_eta, ← hn]
    rw [← hA₂eq]
    by_contra hno
    push Not at hno
    obtain ⟨h20, h21⟩ := hno
    have h02 := le_centralizer_of_component_ne hL₂w.component hL.component h20
    have h12 := le_centralizer_of_component_ne hL₂w.component hL₁w.component h21
    obtain ⟨r₂, hr₂A, hr₂p, hr₂c, hr₂n⟩ :=
      exists_rep_of_mem_sup (hin _ hL₂w) hzb3 (hnC _ hL₂w)
    have hr₂3 : r₂ ^ 3 = 1 := d1_pow_three_of_mem_map_conj hb (hA₂eq ▸ hr₂A) hr₂p
    obtain ⟨hEc, hEe⟩ := card_three_reps_center h01 h02 h12 hr₀A hr₀n hr₀3 hr₁A hr₁n hr₁3 hr₂A
      hr₂n hr₂3 hζA hζC hζ1 hζ3
    have hEz : (Subgroup.zpowers r₀ ⊔ Subgroup.zpowers ζ) ⊔ Subgroup.zpowers r₁ ⊔
        Subgroup.zpowers r₂ ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_ <;> rw [Subgroup.zpowers_le]
      · exact d1_mem_centralizer_of_rep hr₀A hr₀c
      · exact d1_mem_centralizer_of_rep_center hr₀A hr₀c hζA hζC
      · exact d1_mem_centralizer_of_rep hr₁A hr₁c
      · exact d1_mem_centralizer_of_rep hr₂A hr₂c
    have hle := hrk' _ hEz hEe
    rw [hEc] at hle
    norm_num at hle
  have hidx' : ((((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hRM)).range ⊓
      Subgroup.centralizer (A₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M))).subgroupOf
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hRM)).range).index ≤ 3 := by
    rw [Subgroup.inf_subgroupOf_left]
    rw [Subgroup.index_comap] at hidx
    exact hidx
  exact false_of_two_blocks hcard hcard₁ hb hb₁ hc hc₁ h01 hr₀A hr₀n hr₀3 hr₀c hr₁A hr₁n hr₁3
    hr₁c hζA hζC hζ1 hζ3 hZ₀ hζ₁A hζ₁C hζ₁1 hζ₁3 hZ₁ hrk' hU3 hSyl horb hidx'

end Concrete

end CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6

