module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Group
public import CFSG.LocalAnalysis.AGLEmbeddingD2.TransLocal
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Field

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.Sz32Local
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.RankThree.PartOne.K159.SzAbs (SzSylow)

section Cyclic

variable {X : Type*} [Group X]

theorem le_of_card_dvd_of_isCyclic [Finite X] {T U V : Subgroup X} [IsCyclic T] (hU : U ≤ T)
    (hV : V ≤ T) (h : Nat.card V ∣ Nat.card U) : V ≤ U := by
  have hle : V.subgroupOf T ≤ U.subgroupOf T := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv]
    exact h
  intro v hv
  exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_subgroupOf.mpr hv :
    (⟨v, hV hv⟩ : T) ∈ V.subgroupOf T))

theorem mem_of_dvd_card_of_isCyclic [Finite X] {p : ℕ} {T U : Subgroup X} [IsCyclic T] {z : X}
    (hzT : z ∈ T) (hz : orderOf z = p) (hUT : U ≤ T) (hU : p ∣ Nat.card U) : z ∈ U := by
  refine le_of_card_dvd_of_isCyclic (T := T) hUT (Subgroup.zpowers_le.mpr hzT) ?_
    (Subgroup.mem_zpowers z)
  rw [Nat.card_zpowers, hz]
  exact hU

theorem MulAut.zpowers_apply_eq_inv {p : ℕ} (hp : p.Prime) {z : X} (hz : orderOf z = p)
    {β : MulAut (Subgroup.zpowers z)} (hβ : β ≠ 1) (hβ2 : β ^ 2 = 1) :
    ((β ⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) : X) = z⁻¹ := by
  set g : Subgroup.zpowers z := ⟨z, Subgroup.mem_zpowers z⟩ with hg
  have hgen : ∀ x : Subgroup.zpowers z, ∃ k : ℤ, x = g ^ k := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    exact ⟨k, Subtype.ext (by simpa [hg] using hk.symm)⟩
  obtain ⟨k, hk⟩ := hgen (β g)
  have hkk : g ^ (k * k) = g := by
    have h1 : (β ^ 2) g = g := by rw [hβ2]; rfl
    rw [pow_two, MulAut.mul_apply, hk, map_zpow, hk, ← zpow_mul] at h1
    exact h1
  have hdvd : (p : ℤ) ∣ k * k - 1 := by
    have h2 : z ^ (k * k - 1) = 1 := by
      have := congrArg Subtype.val hkk
      simp only [hg, Subgroup.coe_zpow] at this
      rw [zpow_sub, this, zpow_one, mul_inv_cancel]
    rw [← hz]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h2
  have hfac : k * k - 1 = (k - 1) * (k + 1) := by ring
  rw [hfac] at hdvd
  rcases (Int.Prime.dvd_mul' hp hdvd) with h1 | h1
  · exfalso
    apply hβ
    have hzk : g ^ k = g := by
      obtain ⟨m, hm⟩ := h1
      apply Subtype.ext
      simp only [hg, Subgroup.coe_zpow]
      have : k = 1 + p * m := by omega
      rw [this, zpow_add, zpow_one, zpow_mul, ← hz, zpow_natCast, pow_orderOf_eq_one, one_zpow,
        mul_one]
    refine MulEquiv.ext fun x => ?_
    obtain ⟨m, rfl⟩ := hgen x
    rw [map_zpow, hk, hzk, MulAut.one_apply]
  · rw [hk]
    obtain ⟨m, hm⟩ := h1
    simp only [hg, Subgroup.coe_zpow]
    have : k = -1 + p * m := by omega
    rw [this, zpow_add, zpow_neg_one, zpow_mul, ← hz, zpow_natCast, pow_orderOf_eq_one, one_zpow,
      mul_one]

end Cyclic

structure Sz32Normal {X : Type} [Group X] (K : Subgroup X) : Prop where
  normal : K.Normal
  centralizer_eq_bot : Subgroup.centralizer (K : Set X) = ⊥
  data : ∀ T : Sylow 5 K, Sz32Data K (T : Subgroup K)
  szSylow : SzSylow K
  simple : IsSimpleGroup K
  outer : (inner K).index ∣ 5

namespace Sz32Normal

variable {X : Type} [Group X] {K : Subgroup X}

theorem card (hK : Sz32Normal K) : Nat.card K = 32537600 := hK.szSylow.card

theorem conj_injective (hK : Sz32Normal K) :
    haveI := hK.normal
    Function.Injective (MulAut.conjNormal : X →* MulAut K) := by
  have := hK.normal
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hK.centralizer_eq_bot]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 := congrArg (fun f : MulAut K => ((f ⟨k, hk⟩ : K) : X)) (MonoidHom.mem_ker.mp hx)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc k * x = x * k * x⁻¹ * x := by rw [h1]
    _ = x * k := by group

theorem index_dvd_five (hK : Sz32Normal K) : K.index ∣ 5 := by
  have := hK.normal
  have hmap : K.map (MulAut.conjNormal : X →* MulAut K) = inner K := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, (MulAut.conjNormal_val (h := ⟨k, hk⟩)).symm⟩
    · rintro _ ⟨k, rfl⟩
      exact ⟨k, k.2, MulAut.conjNormal_val⟩
  have h := Subgroup.index_map_of_injective (H := K) hK.conj_injective
  rw [hmap] at h
  exact (Dvd.intro _ h.symm).trans hK.outer

variable [Finite X]

theorem data_of_card (hK : Sz32Normal K) {T : Subgroup X} (hTK : T ≤ K) (hTc : Nat.card T = 25) :
    Sz32Data K (T.subgroupOf K) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : Nat.card (T.subgroupOf K) = 5 ^ (Nat.card K).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv, hTc, hK.card,
      CFSG.RankThree.PartOne.K159.SzAbs.factorization_five]
    norm_num
  exact hK.data (Sylow.ofCard (T.subgroupOf K) hc)

theorem isCyclic_of_card (hK : Sz32Normal K) {T : Subgroup X} (hTK : T ≤ K)
    (hTc : Nat.card T = 25) : IsCyclic T := by
  have := (hK.data_of_card hTK hTc).isCyclic
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hTK).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTK).surjective

theorem mem_of_commute (hK : Sz32Normal K) {T : Subgroup X} (hTK : T ≤ K)
    (hTc : Nat.card T = 25) {t : X} (ht : t ∈ T) (ht1 : t ≠ 1) {g : X} (hg : g ∈ K)
    (hgt : g * t = t * g) : g ∈ T := by
  have h := (hK.data_of_card hTK hTc).centralizer_le ⟨t, hTK ht⟩
    (Subgroup.mem_subgroupOf.mpr ht) (fun h1 => ht1 (congrArg Subtype.val h1)) ⟨g, hg⟩
    (Subtype.ext hgt)
  exact Subgroup.mem_subgroupOf.mp h

theorem mem_of_forall_commute (hK : Sz32Normal K) {T : Subgroup X} (hTK : T ≤ K)
    (hTc : Nat.card T = 25) {x : X} (hx : ∀ t ∈ T, x * t = t * x) : x ∈ T := by
  have := hK.normal
  have hf : ∀ y ∈ T.subgroupOf K, (MulAut.conjNormal x : MulAut K) y = y := by
    intro y hy
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply, hx _ (Subgroup.mem_subgroupOf.mp hy)]
    group
  obtain ⟨t, htT, hft⟩ := (hK.data_of_card hTK hTc).aut hK.szSylow hK.simple hK.outer hf
  have heq : x = (t : X) := hK.conj_injective (hft.trans MulAut.conjNormal_val.symm)
  rw [heq]
  exact Subgroup.mem_subgroupOf.mp htT

omit [Finite X] in
theorem card_inf_eq (H : Subgroup X) :
    Nat.card (H ⊓ K : Subgroup X) = Nat.card (H.subgroupOf K) := by
  rw [← Subgroup.inf_subgroupOf_right]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm

theorem card_normalizer_inf (hK : Sz32Normal K) {T : Subgroup X} (hTK : T ≤ K)
    (hTc : Nat.card T = 25) :
    Nat.card (Subgroup.normalizer (T : Set X) ⊓ K : Subgroup X) = 100 := by
  have h := (hK.data_of_card hTK hTc).card_normalizer
  rw [← Subgroup.subgroupOf_normalizer_eq hTK] at h
  rw [card_inf_eq, h]

theorem inf_eq_or_le (hK : Sz32Normal K) {T : Subgroup X} (hTK : T ≤ K) (hTc : Nat.card T = 25)
    {Y : Subgroup X} (hY : Subgroup.normalizer (T : Set X) ≤ Y) :
    Y.subgroupOf K = (Subgroup.normalizer (T : Set X)).subgroupOf K ∨ K ≤ Y := by
  have hle : Subgroup.normalizer ((T.subgroupOf K : Subgroup K) : Set K) ≤ Y.subgroupOf K := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTK]
    exact Subgroup.subgroupOf_mono _ hY
  rcases (hK.data_of_card hTK hTc).maximal hle with h | h
  · left
    rw [h, Subgroup.subgroupOf_normalizer_eq hTK]
  · right
    exact Subgroup.subgroupOf_eq_top.mp h

theorem card_sylow_inf (hK : Sz32Normal K) (R : Sylow 5 X) :
    Nat.card ((R : Subgroup X) ⊓ K : Subgroup X) = 25 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hKn := hK.normal
  apply le_antisymm
  · have hp : IsPGroup 5 (((R : Subgroup X) ⊓ K).subgroupOf K) :=
      (R.isPGroup'.to_inf_left).comap_subtype
    obtain ⟨S, hS⟩ := hp.exists_le_sylow
    calc Nat.card ((R : Subgroup X) ⊓ K : Subgroup X)
        = Nat.card (((R : Subgroup X) ⊓ K).subgroupOf K) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
      _ ≤ Nat.card (S : Subgroup K) := Subgroup.card_le_of_le hS
      _ = 25 := (hK.data S).card_eq
  · obtain ⟨S₀⟩ : Nonempty (Sylow 5 K) := inferInstance
    set S : Subgroup X := (S₀ : Subgroup K).map K.subtype with hSdef
    have hSc : Nat.card S = 25 := by
      rw [hSdef, Subgroup.card_map_of_injective K.subtype_injective]
      exact (hK.data S₀).card_eq
    have hSp : IsPGroup 5 S := IsPGroup.of_card (n := 2) (by rw [hSc]; norm_num)
    obtain ⟨Q, hSQ⟩ := hSp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q R
    have hQR : (R : Subgroup X) = (Q : Subgroup X).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul]
      rfl
    have hle : S.map (MulAut.conj g).toMonoidHom ≤ (R : Subgroup X) ⊓ K := by
      refine le_inf (hQR ▸ Subgroup.map_mono hSQ) ?_
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨k, -, rfl⟩ := hs
      exact hKn.conj_mem _ k.2 g
    calc 25 = Nat.card (S.map (MulAut.conj g).toMonoidHom) := by
          rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hSc]
      _ ≤ _ := Subgroup.card_le_of_le hle

theorem factorization_five_mul : (32537600 * 5 : ℕ).factorization 5 = 3 := by
  have h : (32537600 * 5 : ℕ) = 5 ^ 3 * (2 ^ 10 * 31 * 41) := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply]
  rw [Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem transLocal (hK : Sz32Normal K) (R : Sylow 5 X) (A : Subgroup X) (hAR : A ≤ R)
    (hA : IsElemAbelian 5 A) (hAc : Nat.card A = 5 ^ 2) :
    ∃ z : X, z ∈ A ∧ orderOf z = 5 ∧ z ∈ K ∧
      Subgroup.zpowers z = (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ∧
      (∀ Y : Subgroup X, Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ Y →
        Y = Subgroup.normalizer ((R : Subgroup X) : Set X) ∨ Y = ⊤) ∧
      (∀ W : Subgroup X, W ≤ Subgroup.normalizer ((R : Subgroup X) : Set X) →
        Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ Subgroup.normalizer (W : Set X) →
        W = ⊥ ∨ z ∈ W) ∧
      Subgroup.normalizer ((R : Subgroup X) : Set X) ⊓ Subgroup.centralizer ({z} : Set X) ≤ R ∧
      Group.IsSolvable (Subgroup.normalizer ((R : Subgroup X) : Set X)) ∧
      (∃ b ∈ (R : Subgroup X), b * z * b⁻¹ = z ∧
        (∀ y ∈ A, b * y * b⁻¹ * y⁻¹ ∈ Subgroup.zpowers z) ∧
        ∃ a₀ ∈ A, ∀ k : ℕ, 0 < k → k < 5 → b ^ k * a₀ * (b ^ k)⁻¹ ≠ a₀) ∧
      (∃ b ∈ (R : Subgroup X), b ^ 5 ≠ 1) ∧
      (∃ t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X),
        ∃ e : ℕ, 6 ∣ e ∧ t ^ e * z * (t ^ e)⁻¹ = z⁻¹) ∧
      ∀ T : Sylow 5 K, IsCyclic T := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hKn := hK.normal
  set T : Subgroup X := (R : Subgroup X) ⊓ K with hTdef
  have hTK : T ≤ K := inf_le_right
  have hTR : T ≤ R := inf_le_left
  have hTc : Nat.card T = 25 := hK.card_sylow_inf R
  have hTcyc : IsCyclic T := hK.isCyclic_of_card hTK hTc
  obtain ⟨⟨a, haT⟩, ha⟩ := hTcyc.exists_generator
  have hTa : T = Subgroup.zpowers a := by
    refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr haT)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (ha ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hoa : orderOf a = 25 := by rw [← Nat.card_zpowers, ← hTa, hTc]
  set z : X := a ^ 5 with hzdef
  have hoz : orderOf z = 5 := by
    rw [hzdef, orderOf_pow' a (by norm_num), hoa]
    norm_num
  have hzT : z ∈ T := T.pow_mem haT 5
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hoz; omega
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    rw [hTa] at hx hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self a m n).eq
  have hzmem : ∀ U : Subgroup X, U ≤ T → U ≠ ⊥ → z ∈ U := by
    intro U hUT hU
    refine mem_of_dvd_card_of_isCyclic (T := T) hzT hoz hUT ?_
    have hd : Nat.card U ∣ 5 ^ 2 := by
      rw [show (5 : ℕ) ^ 2 = 25 by norm_num, ← hTc]
      exact Subgroup.card_dvd_of_le hUT
    obtain ⟨k, -, hkU⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hd
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hU (Subgroup.eq_bot_of_card_eq U (by rw [hkU, pow_zero]))
    rw [hkU]
    exact dvd_pow_self 5 hk0
  have hCT : ∀ x : X, (∀ t ∈ T, x * t = t * x) → x ∈ T := fun x hx =>
    hK.mem_of_forall_commute hTK hTc hx
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hAK : ¬ A ≤ K := by
    intro hAK
    have hAT : A = T := Subgroup.eq_of_le_of_card_ge (le_inf hAR hAK) (by rw [hTc, hAc]; norm_num)
    have h5 : a ^ 5 = 1 := hA.2 a (hAT ▸ haT)
    exact hz1 h5
  obtain ⟨σ, hσA, hσK⟩ := IsConcreteLE.not_le_iff_exists.mp hAK
  have hσR : σ ∈ (R : Subgroup X) := hAR hσA
  have hidx : K.index = 5 := by
    rcases (Nat.dvd_prime (by norm_num)).mp hK.index_dvd_five with h | h
    · exact absurd (Subgroup.index_eq_one.mp h ▸ Subgroup.mem_top σ) hσK
    · exact h
  have hRc : Nat.card (R : Subgroup X) = 125 := by
    rw [Sylow.card_eq_multiplicity, ← Subgroup.card_mul_index K, hK.card, hidx,
      factorization_five_mul]
    norm_num
  have hσT : ∀ g ∈ T, g * σ = σ * g → g ∈ Subgroup.zpowers z := by
    intro g hg hgσ
    have hd : orderOf g ∣ 5 ^ 2 := by
      rw [show (5 : ℕ) ^ 2 = 25 by norm_num, ← hTc]
      exact Subgroup.orderOf_dvd_natCard T hg
    obtain ⟨k, hk, hkg⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hd
    by_cases hk2 : k = 2
    · exfalso
      have hgT : Subgroup.zpowers g = T := Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr hg) (by rw [Nat.card_zpowers, hkg, hk2, hTc]; norm_num)
      apply hσK
      refine hTK (hCT σ fun t ht => ?_)
      rw [← hgT] at ht
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
      exact ((Commute.zpow_right (show Commute σ g from hgσ.symm) n)).eq
    · refine le_of_card_dvd_of_isCyclic (T := T) (Subgroup.zpowers_le.mpr hzT)
        (Subgroup.zpowers_le.mpr hg) ?_ (Subgroup.mem_zpowers g)
      rw [Nat.card_zpowers, Nat.card_zpowers, hkg, hoz]
      exact (pow_dvd_pow 5 (show k ≤ 1 by omega)).trans (by rw [pow_one])
  have hTA : T ⊔ A = R := by
    have hle : T ⊔ A ≤ R := sup_le hTR hAR
    have hd : Nat.card (T ⊔ A : Subgroup X) ∣ 5 ^ 3 := by
      rw [show (5 : ℕ) ^ 3 = 125 by norm_num, ← hRc]
      exact Subgroup.card_dvd_of_le hle
    obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hd
    have hgt : 25 < Nat.card (T ⊔ A : Subgroup X) := by
      by_contra hle'
      push Not at hle'
      have heq : T = T ⊔ A := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hTc]; exact hle')
      exact hσK (hTK (heq ▸ (le_sup_right : A ≤ T ⊔ A) hσA))
    have hk3 : k = 3 := by
      rw [hkc] at hgt
      interval_cases k <;> first | rfl | (norm_num at hgt)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hRc, hkc, hk3]
    norm_num
  have hzA : z ∈ A := by
    have h1 := Subgroup.relIndex_mul_card T (R : Subgroup X)
    rw [inf_eq_left.mpr hTR, hTc, hRc] at h1
    have h2 := Subgroup.relIndex_mul_card T A
    rw [hAc] at h2
    have h3 : T.relIndex A ≤ T.relIndex R :=
      Subgroup.relIndex_le_of_le_right hAR (by omega)
    have hne : T ⊓ A ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot, mul_one] at h2
      omega
    exact (hzmem (T ⊓ A) inf_le_left hne).2
  have hzC : (R : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := by
    rw [← hTA]
    refine sup_le (fun t ht => ?_) (fun y hy => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hTcomm z hzT t ht).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm z hzA y hy).symm
  have hzR : ∀ r ∈ (R : Subgroup X), r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hzC hr)
  have hcen : Subgroup.zpowers z =
      (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) := by
    refine le_antisymm (Subgroup.zpowers_le.mpr ⟨hTR hzT, Subgroup.mem_centralizer_iff.mpr
      fun r hr => hzR r hr⟩) ?_
    rintro y ⟨hyR, hyC⟩
    have hyT : y ∈ T := hCT y fun t ht =>
      (Subgroup.mem_centralizer_iff.mp hyC t (hTR ht)).symm
    exact hσT y hyT (Subgroup.mem_centralizer_iff.mp hyC σ hσR).symm
  set N : Subgroup X := Subgroup.normalizer (T : Set X) with hNdef
  have hRN : (R : Subgroup X) ≤ N := fun r hr =>
    Subgroup.mem_normalizer_fintype fun t ht =>
      ⟨R.mul_mem (R.mul_mem hr (hTR ht)) (R.inv_mem hr), hKn.conj_mem t (hTK ht) r⟩
  have hcomm : ∀ n ∈ N, ∀ m ∈ N, n * m * n⁻¹ * m⁻¹ ∈ T := by
    intro n hn m hm
    set φ := T.normalizerMonoidHom with hφ
    have hab : ∀ f g : MulAut T, f * g = g * f := fun f g =>
      (IsCyclic.mulAutMulEquiv T).injective (by rw [map_mul, map_mul, mul_comm])
    have hker : (⟨n, hn⟩ * ⟨m, hm⟩ * (⟨n, hn⟩ : N)⁻¹ * (⟨m, hm⟩ : N)⁻¹ : N) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hab (φ ⟨n, hn⟩),
        mul_inv_cancel_right, mul_inv_cancel]
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
    refine hCT _ fun t ht => ?_
    exact (Subgroup.mem_centralizer_iff.mp hker t ht).symm
  have hNR : Subgroup.normalizer ((R : Subgroup X) : Set X) = N := by
    apply le_antisymm
    · intro n hn
      refine Subgroup.mem_normalizer_fintype fun t ht => ⟨?_, hKn.conj_mem t (hTK ht) n⟩
      exact (Subgroup.mem_normalizer_iff.mp hn t).mp (hTR ht)
    · intro n hn
      refine Subgroup.mem_normalizer_fintype fun r hr => ?_
      have h1 : n * r * n⁻¹ * r⁻¹ ∈ (R : Subgroup X) := hTR (hcomm n hn r (hRN hr))
      have h2 : n * r * n⁻¹ = n * r * n⁻¹ * r⁻¹ * r := by group
      rw [h2]
      exact R.mul_mem h1 hr
  rw [hNR]
  have hNK : Nat.card (N ⊓ K : Subgroup X) = 100 := hK.card_normalizer_inf hTK hTc
  have hrelN : K.relIndex N = 5 := by
    rcases (Nat.dvd_prime (by norm_num)).mp (hidx ▸ Subgroup.relIndex_dvd_index_of_normal K N)
      with h | h
    · exact absurd (Subgroup.relIndex_eq_one.mp h (hRN hσR)) hσK
    · exact h
  have hNc : Nat.card N = 500 := by
    have h := Subgroup.relIndex_mul_card K N
    rw [hrelN, inf_comm, hNK] at h
    omega
  have hNz : N ⊓ Subgroup.centralizer ({z} : Set X) ≤ R := by
    set C : Subgroup X := N ⊓ Subgroup.centralizer ({z} : Set X) with hCdef
    have hCK : C ⊓ K ≤ T := fun c hc =>
      hK.mem_of_commute hTK hTc hzT hz1 hc.2 (Subgroup.mem_centralizer_singleton_iff.mp hc.1.2)
    have hCc : Nat.card C ≤ 125 := by
      have h := Subgroup.relIndex_mul_card K C
      have hr : K.relIndex C ≤ 5 := Nat.le_of_dvd (by norm_num)
        (hidx ▸ Subgroup.relIndex_dvd_index_of_normal K C)
      have hc : Nat.card (K ⊓ C : Subgroup X) ≤ 25 := by
        rw [inf_comm, ← hTc]
        exact Subgroup.card_le_of_le hCK
      calc Nat.card C = K.relIndex C * Nat.card (K ⊓ C : Subgroup X) := h.symm
        _ ≤ 5 * 25 := Nat.mul_le_mul hr hc
        _ = 125 := by norm_num
    have hRC : (R : Subgroup X) ≤ C := le_inf hRN hzC
    have heq : (R : Subgroup X) = C := Subgroup.eq_of_le_of_card_ge hRC (by rw [hRc]; exact hCc)
    exact heq ▸ le_rfl
  refine ⟨z, hzA, hoz, hTK hzT, hcen, ?_, ?_, hNz, ?_, ?_, ⟨a, hTR haT, hz1⟩, ?_,
    hK.szSylow.cyclic⟩
  ·
    intro Y hY
    rcases hK.inf_eq_or_le hTK hTc hY with h | h
    · left
      have hYK : Nat.card (Y ⊓ K : Subgroup X) = 100 := by
        rw [card_inf_eq, h, ← card_inf_eq, hNK]
      have hYc : Nat.card Y ≤ 500 := by
        have h1 := Subgroup.relIndex_mul_card K Y
        have hr : K.relIndex Y ≤ 5 := Nat.le_of_dvd (by norm_num)
          (hidx ▸ Subgroup.relIndex_dvd_index_of_normal K Y)
        rw [inf_comm, hYK] at h1
        omega
      exact (Subgroup.eq_of_le_of_card_ge hY (by rw [hNc]; exact hYc)).symm
    · right
      have hdvd : Y.index ∣ 5 := hidx ▸ Subgroup.index_dvd_of_le h
      rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h1
      · exact Subgroup.index_eq_one.mp h1
      · exfalso
        have h2 := Subgroup.relIndex_mul_index h
        rw [h1, hidx] at h2
        have h3 : K.relIndex Y = 1 := by omega
        exact hσK (Subgroup.relIndex_eq_one.mp h3 (hY (hRN hσR)))
  ·
    intro W hWN hNW
    by_cases hWT : W ⊓ T = ⊥
    · left
      rw [eq_bot_iff]
      intro w hw
      have hwT : w ∈ T := by
        refine hCT w fun t ht => ?_
        have hc : w * t * w⁻¹ * t⁻¹ ∈ W ⊓ T := by
          refine ⟨?_, T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hWN hw) t).mp ht)
            (T.inv_mem ht)⟩
          have h1 : t * w⁻¹ * t⁻¹ ∈ W :=
            (Subgroup.mem_normalizer_iff.mp (hNW (hRN (hTR ht))) w⁻¹).mp (W.inv_mem hw)
          have h2 : w * t * w⁻¹ * t⁻¹ = w * (t * w⁻¹ * t⁻¹) := by group
          rw [h2]
          exact W.mul_mem hw h1
        rw [hWT, Subgroup.mem_bot] at hc
        have h3 : w * t * w⁻¹ = t := by
          have := congrArg (· * t) hc
          simpa [mul_assoc] using this
        calc w * t = w * t * w⁻¹ * w := by group
          _ = t * w := by rw [h3]
      have : w ∈ W ⊓ T := ⟨hw, hwT⟩
      rwa [hWT] at this
    · exact Or.inr (hzmem (W ⊓ T) inf_le_right hWT).1
  ·
    have hTn : (T.subgroupOf N).Normal := Subgroup.normal_in_normalizer
    have hTs : Group.IsSolvable (T.subgroupOf N) :=
      Group.isSolvable_of_comm fun x y => Subtype.ext (Subtype.ext
        (hTcomm _ (Subgroup.mem_subgroupOf.mp x.2) _ (Subgroup.mem_subgroupOf.mp y.2)))
    have hQs : Group.IsSolvable (N ⧸ T.subgroupOf N) := by
      refine Group.isSolvable_of_comm fun x y => ?_
      induction x using QuotientGroup.induction_on with
      | _ x =>
        induction y using QuotientGroup.induction_on with
        | _ y =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
            Subgroup.mem_subgroupOf]
          have h := hcomm (y⁻¹ : N) (y⁻¹ : N).2 (x⁻¹ : N) (x⁻¹ : N).2
          simpa [mul_assoc] using h
    exact Group.isSolvable_of_ker_le_range (T.subgroupOf N).subtype
      (QuotientGroup.mk' (T.subgroupOf N)) (by simp [QuotientGroup.ker_mk'])
  ·
    refine ⟨a, hTR haT, by rw [hzdef]; group, fun y hy => ?_, σ, hσA, ?_⟩
    ·
      set Z : Subgroup (R : Subgroup X) := (Subgroup.zpowers z).subgroupOf R with hZdef
      have hZR : Subgroup.zpowers z ≤ R := Subgroup.zpowers_le.mpr (hTR hzT)
      have hZn : Z.Normal := ⟨fun n hn g => by
        rw [hZdef, Subgroup.mem_subgroupOf] at hn ⊢
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
        have hgz : (g : X) * z = z * g := hzR g g.2
        have h1 : (g : X) * z ^ k * (g : X)⁻¹ = z ^ k := by
          rw [(Commute.zpow_right (show Commute (g : X) z from hgz) k).eq, mul_inv_cancel_right]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hk, h1]
        exact Subgroup.zpow_mem_zpowers z k⟩
      have hZc : Nat.card Z = 5 := by
        rw [hZdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv, Nat.card_zpowers,
          hoz]
      have hQc : Nat.card ((R : Subgroup X) ⧸ Z) = 5 ^ 2 := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
        rw [hRc, hZc] at h
        rw [show (5 : ℕ) ^ 2 = 25 by norm_num]
        omega
      have hab := IsPGroup.isMulCommutative_of_card_eq_prime_sq hQc
      have hyR : y ∈ (R : Subgroup X) := hAR hy
      have haR : a ∈ (R : Subgroup X) := hTR haT
      have h1 : (QuotientGroup.mk' Z (⟨a, haR⟩ * ⟨y, hyR⟩ * (⟨a, haR⟩ : R)⁻¹ * (⟨y, hyR⟩ : R)⁻¹)) =
          1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv,
          hab.is_comm.comm (QuotientGroup.mk' Z ⟨a, haR⟩), mul_inv_cancel_right, mul_inv_cancel]
      have h2 := (QuotientGroup.eq_one_iff _).mp h1
      rw [hZdef, Subgroup.mem_subgroupOf] at h2
      simpa using h2
    ·
      intro k hk0 hk5 hfix
      have hak : a ^ k ∈ Subgroup.zpowers z := by
        refine hσT (a ^ k) (T.pow_mem haT k) ?_
        calc a ^ k * σ = a ^ k * σ * (a ^ k)⁻¹ * a ^ k := by group
          _ = σ * a ^ k := by rw [hfix]
      have hcop : (orderOf a).Coprime k := by
        rw [hoa]
        interval_cases k <;> norm_num
      have h1 := orderOf_dvd_of_mem_zpowers hak
      rw [hcop.orderOf_pow, hoa, hoz] at h1
      norm_num at h1
  ·
    set Z : Subgroup X := Subgroup.zpowers z with hZdef
    have hZc : Nat.card Z = 5 := by rw [hZdef, Nat.card_zpowers, hoz]
    have hZT : Z ≤ T := Subgroup.zpowers_le.mpr hzT
    have hNZ : N ≤ Subgroup.normalizer (Z : Set X) := by
      intro n hn
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have hnz : n * z * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hn z).mp hzT
      have hnzZ : n * z * n⁻¹ ∈ Z := by
        refine le_of_card_dvd_of_isCyclic (T := T) hZT (Subgroup.zpowers_le.mpr hnz) ?_
          (Subgroup.mem_zpowers _)
        rw [Nat.card_zpowers, hZc]
        have h1 := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective z
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
        rw [h1, hoz]
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← conj_zpow]
      exact Z.zpow_mem hnzZ k
    set ψ : N →* MulAut Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hNZ) with hψ
    have hψapp : ∀ (n : N) (x : Z), ((ψ n x : Z) : X) = (n : X) * x * (n : X)⁻¹ := fun n x => rfl
    have hker : ψ.ker = (R : Subgroup X).subgroupOf N := by
      ext ⟨n, hn⟩
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        have h2 : n * z * n⁻¹ = z := by
          have := congrArg (fun f : MulAut Z => ((f ⟨z, Subgroup.mem_zpowers z⟩ : Z) : X)) h1
          simpa only [hψapp, MulAut.one_apply] using this
        refine hNz ⟨hn, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc n * z = n * z * n⁻¹ * n := by group
          _ = z * n := by rw [h2]
      · intro hnR
        refine MulEquiv.ext fun x => Subtype.ext ?_
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
        rw [hψapp, MulAut.one_apply, ← hk]
        have hnz : n * z = z * n := hzR n hnR
        show n * z ^ k * n⁻¹ = z ^ k
        rw [(Commute.zpow_right (show Commute n z from hnz) k).eq, mul_inv_cancel_right]
    have hrange : Nat.card ψ.range = 4 := by
      have h := Subgroup.card_ker_mul_card_range ψ
      rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv, hRc, hNc] at h
      omega
    have hAutc : Nat.card (MulAut Z) = 4 := by
      rw [IsCyclic.card_mulAut, hZc]
      rfl
    have hAutcyc : IsCyclic (MulAut Z) := by
      have : Fact (Nat.card Z).Prime := ⟨by rw [hZc]; norm_num⟩
      have : NeZero (Nat.card Z) := ⟨by rw [hZc]; norm_num⟩
      exact isCyclic_of_surjective (IsCyclic.mulAutMulEquiv Z).symm.toMonoidHom
        (IsCyclic.mulAutMulEquiv Z).symm.surjective
    have hsurj : ψ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, hAutc])
    obtain ⟨g, hg⟩ := hAutcyc.exists_generator
    have hog : orderOf g = 4 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hAutc]
    obtain ⟨⟨t, htN⟩, ht⟩ : g ∈ ψ.range := hsurj ▸ Subgroup.mem_top g
    refine ⟨t, htN, 6, dvd_refl 6, ?_⟩
    have hβ : g ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hog]; norm_num)
    have hβ2 : (g ^ 2) ^ 2 = 1 := by
      rw [← pow_mul, show 2 * 2 = orderOf g by rw [hog], pow_orderOf_eq_one]
    have hinv := MulAut.zpowers_apply_eq_inv (by norm_num : Nat.Prime 5) hoz hβ hβ2
    have h6 : ψ (⟨t, htN⟩ ^ 6) = g ^ 2 := by
      rw [map_pow, ht, show (6 : ℕ) = 4 + 2 by rfl, pow_add, ← hog, pow_orderOf_eq_one, one_mul]
    rw [← h6, hψapp] at hinv
    simpa using hinv

end Sz32Normal

open CFSG.AGLEmbedding.KFactProofs.Sz32 in
theorem sz32Normal_of_mulEquiv
    {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .suzuki 2) (hKn : K.Normal)
    (hC : Subgroup.centralizer (K : Set X) = ⊥) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Sz32Normal K := by
  obtain ⟨x, hv⟩ := d
  simp only at hd
  subst hd
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie K (.suzuki 2) := ⟨hv, ⟨e⟩⟩
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso
  have hOut : (inner K).index ∣ 5 := CFSG.RankThree.PartOne.K159F.card_outer_dvd_five hiso
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ :=
    CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  have hsimple : IsSimpleGroup K := by
    have := (CFSG.LieType.Ree.suzuki_simple ha hF').2.2
    exact eF.isSimpleGroup
  obtain rfl : a = 2 := by omega
  let ε := eF.trans (modelEquiv (F32.ringEquiv F hF'))
  have hcard : ∀ T : Sylow 5 K, Nat.card (T : Subgroup K) = 25 := by
    intro T
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [Sylow.card_eq_multiplicity, hSz.card,
      CFSG.RankThree.PartOne.K159.SzAbs.factorization_five]
    norm_num
  exact ⟨hKn, hC, fun T => ⟨hSz.card, hcard T, hSz.cyclic T, centralizer_le_of_equiv ε T⟩, hSz,
    hsimple, hOut⟩

theorem d2TransLocalAt_sz32
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .suzuki 2) :
    D2TransLocalAt (.lie d) fun p => p = 5 := by
  intro X _ _ K hKn hC ⟨e⟩ p hp R A hAR hA hAc
  subst hp
  exact (sz32Normal_of_mulEquiv d hd hKn hC e).transLocal R A hAR hA hAc

end CFSG.AGLEmbeddingD2
