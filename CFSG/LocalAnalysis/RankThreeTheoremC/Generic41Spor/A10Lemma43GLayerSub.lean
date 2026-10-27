module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a10t1_sub_mem_sup_prod {Y : Type*} [Group Y] {H O : Subgroup Y}
    (hHO : ∀ h ∈ H, ∀ o ∈ O, h * o * h⁻¹ ∈ O) {x : Y} (hx : x ∈ H ⊔ O) :
    ∃ h ∈ H, ∃ o ∈ O, x = h * o := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ h ∈ H, ∃ o ∈ O, x = h * o) ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, O.one_mem, (mul_one x).symm⟩
    · exact ⟨1, H.one_mem, x, hx, (one_mul x).symm⟩
  · exact ⟨1, H.one_mem, 1, O.one_mem, (mul_one 1).symm⟩
  · rintro x y _ _ ⟨h, hh, o, ho, rfl⟩ ⟨h', hh', o', ho', rfl⟩
    refine ⟨h * h', H.mul_mem hh hh', (h'⁻¹ * o * h'⁻¹⁻¹) * o', O.mul_mem ?_ ho', ?_⟩
    · exact hHO h'⁻¹ (H.inv_mem hh') o ho
    · group
  · rintro x _ ⟨h, hh, o, ho, rfl⟩
    refine ⟨h⁻¹, H.inv_mem hh, h * o⁻¹ * h⁻¹, hHO h hh o⁻¹ (O.inv_mem ho), ?_⟩
    group

theorem a10t1_sub_simple_normal {Y : Type*} [Group Y] {A S : Subgroup Y} (hA : IsSimpleGroup ↥A)
    (hSA : S ≤ A) (hS : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S) : S = ⊥ ∨ S = A := by
  have hN : (S.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff hSA).2 (fun s a hs ha => hS a ha s hs)
  haveI := hN
  rcases hA.eq_bot_or_eq_top_of_normal (S.subgroupOf A) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hSA] at h
    exact h
  · right
    exact le_antisymm hSA (Subgroup.subgroupOf_eq_top.1 h)

theorem a10t1_sub_center_triv {Y : Type*} [Group Y] {A : Subgroup Y} (hA : IsSimpleGroup ↥A)
    (hAn : ¬ IsMulCommutative ↥A) {a : Y} (ha : a ∈ A) (hc : ∀ a' ∈ A, a' * a = a * a') :
    a = 1 := by
  have hZ : Subgroup.center ↥A = ⊥ := by
    rcases hA.eq_bot_or_eq_top_of_normal (Subgroup.center ↥A) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.1 h) hAn
  have hmem : (⟨a, ha⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g.1 g.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem a10t1_sub_comp_central {Y : Type*} [Group Y] {A B S : Subgroup Y}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hSA : S ⊓ A = ⊥)
    (hS : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S) {a b : Y} (ha : a ∈ A) (hb : b ∈ B)
    (hs : a * b ∈ S) : ∀ a' ∈ A, a' * a = a * a' := by
  intro a' ha'
  have h1 : a' * (a * b) * a'⁻¹ * (a * b)⁻¹ ∈ S :=
    S.mul_mem (hS a' ha' _ hs) (S.inv_mem hs)
  have h2 : a' * (a * b) * a'⁻¹ * (a * b)⁻¹ = a' * a * a'⁻¹ * a⁻¹ := by
    have hc : b * a'⁻¹ = a'⁻¹ * b := (hAB a'⁻¹ (A.inv_mem ha') b hb).symm
    calc a' * (a * b) * a'⁻¹ * (a * b)⁻¹ = a' * a * (b * a'⁻¹) * b⁻¹ * a⁻¹ := by group
      _ = a' * a * (a'⁻¹ * b) * b⁻¹ * a⁻¹ := by rw [hc]
      _ = a' * a * a'⁻¹ * a⁻¹ := by group
  have h3 : a' * a * a'⁻¹ * a⁻¹ ∈ S ⊓ A :=
    ⟨h2 ▸ h1, A.mul_mem (A.mul_mem (A.mul_mem ha' ha) (A.inv_mem ha')) (A.inv_mem ha)⟩
  rw [hSA, Subgroup.mem_bot] at h3
  calc a' * a = a' * a * a'⁻¹ * a⁻¹ * (a * a') := by group
    _ = a * a' := by rw [h3, one_mul]

theorem a10t1_sub_one_factor {Y : Type*} [Group Y] {A B S : Subgroup Y}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hSN : S ≤ A ⊔ B) (hAS : A ≤ S)
    (hSB : S ⊓ B = ⊥) : S = A := by
  refine le_antisymm (fun s hs => ?_) hAS
  obtain ⟨a, ha, b, hb, rfl⟩ := a10t1_sub_mem_sup_prod
    (fun a ha b hb => by rw [hAB a ha b hb, mul_inv_cancel_right]; exact hb) (hSN hs)
  have hbS : b ∈ S := by
    have := S.mul_mem (S.inv_mem (hAS ha)) hs
    simpa using this
  have hb1 : b ∈ S ⊓ B := ⟨hbS, hb⟩
  rw [hSB, Subgroup.mem_bot] at hb1
  simpa [hb1] using ha

theorem a10t1_sub_trivial_case {Y : Type*} [Group Y] {A B S : Subgroup Y}
    (hA : IsSimpleGroup ↥A) (hAn : ¬ IsMulCommutative ↥A) (hB : IsSimpleGroup ↥B)
    (hBn : ¬ IsMulCommutative ↥B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hSN : S ≤ A ⊔ B) (hSA : S ⊓ A = ⊥) (hSB : S ⊓ B = ⊥)
    (hSn : ∀ n ∈ A ⊔ B, ∀ s ∈ S, n * s * n⁻¹ ∈ S) : S = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := a10t1_sub_mem_sup_prod
    (fun a ha b hb => by rw [hAB a ha b hb, mul_inv_cancel_right]; exact hb) (hSN hs)
  have hcA := a10t1_sub_comp_central hAB hSA (fun a ha s hs => hSn a (Subgroup.mem_sup_left ha) s hs) ha hb hs
  have hcB := a10t1_sub_comp_central (A := B) (B := A) (fun b hb a ha => (hAB a ha b hb).symm) hSB
    (fun b hb s hs => hSn b (Subgroup.mem_sup_right hb) s hs) hb ha (by rwa [← hAB a ha b hb])
  have ha1 := a10t1_sub_center_triv hA hAn ha hcA
  have hb1 := a10t1_sub_center_triv hB hBn hb hcB
  simp [ha1, hb1]

theorem a10t1_sub_normal_cases {Y : Type*} [Group Y] {A B S : Subgroup Y}
    (hA : IsSimpleGroup ↥A) (hAn : ¬ IsMulCommutative ↥A) (hB : IsSimpleGroup ↥B)
    (hBn : ¬ IsMulCommutative ↥B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hSN : S ≤ A ⊔ B) (hSn : ∀ n ∈ A ⊔ B, ∀ s ∈ S, n * s * n⁻¹ ∈ S) :
    S = ⊥ ∨ S = A ∨ S = B ∨ S = A ⊔ B := by
  have hSA : S ⊓ A = ⊥ ∨ S ⊓ A = A :=
    a10t1_sub_simple_normal hA inf_le_right (fun a ha s hs =>
      ⟨hSn a (Subgroup.mem_sup_left ha) s hs.1, A.mul_mem (A.mul_mem ha hs.2) (A.inv_mem ha)⟩)
  have hSB : S ⊓ B = ⊥ ∨ S ⊓ B = B :=
    a10t1_sub_simple_normal hB inf_le_right (fun b hb s hs =>
      ⟨hSn b (Subgroup.mem_sup_right hb) s hs.1, B.mul_mem (B.mul_mem hb hs.2) (B.inv_mem hb)⟩)
  rcases hSA with hSA | hSA <;> rcases hSB with hSB | hSB
  · exact Or.inl (a10t1_sub_trivial_case hA hAn hB hBn hAB hSN hSA hSB hSn)
  · right; right; left
    exact a10t1_sub_one_factor (A := B) (B := A) (fun b hb a ha => (hAB a ha b hb).symm)
      (by rwa [sup_comm]) (inf_eq_right.1 hSB) hSA
  · right; left
    exact a10t1_sub_one_factor hAB hSN (inf_eq_right.1 hSA) hSB
  · right; right; right
    exact le_antisymm hSN (sup_le (inf_eq_right.1 hSA) (inf_eq_right.1 hSB))

theorem a10t1_sub_subnormal_cases {Y : Type*} [Group Y] {A B : Subgroup Y}
    (hA : IsSimpleGroup ↥A) (hAn : ¬ IsMulCommutative ↥A) (hB : IsSimpleGroup ↥B)
    (hBn : ¬ IsMulCommutative ↥B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {S : Subgroup Y}
    (hS : S.IsSubnormal) :
    S ⊓ (A ⊔ B) = ⊥ ∨ S ⊓ (A ⊔ B) = A ∨ S ⊓ (A ⊔ B) = B ∨ S ⊓ (A ⊔ B) = A ⊔ B := by
  induction hS with
  | top => exact Or.inr (Or.inr (Or.inr (top_inf_eq _)))
  | step H K h_le hSubn hN ih =>
    have hconj : ∀ k ∈ K ⊓ (A ⊔ B), ∀ s ∈ H ⊓ (A ⊔ B), k * s * k⁻¹ ∈ H ⊓ (A ⊔ B) := by
      intro k hk s hs
      exact ⟨(Subgroup.normal_subgroupOf_iff h_le).1 hN s k hs.1 hk.1,
        (A ⊔ B).mul_mem ((A ⊔ B).mul_mem hk.2 hs.2) ((A ⊔ B).inv_mem hk.2)⟩
    have hle : H ⊓ (A ⊔ B) ≤ K ⊓ (A ⊔ B) := inf_le_inf_right _ h_le
    rcases ih with h | h | h | h
    · left
      rw [h] at hle
      exact le_bot_iff.1 hle
    · rw [h] at hle hconj
      rcases a10t1_sub_simple_normal hA hle hconj with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rw [h] at hle hconj
      rcases a10t1_sub_simple_normal hB hle hconj with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inl h'))
    · rw [h] at hle hconj
      exact a10t1_sub_normal_cases hA hAn hB hBn hAB inf_le_right hconj

theorem a10t1_sub_quasi_ne_bot {Y : Type*} [Group Y] {C : Subgroup Y} (hq : CFSG.IsQuasisimple ↥C) :
    C ≠ ⊥ := by
  have h1 : Nontrivial (↥C ⧸ Subgroup.center ↥C) := hq.2.1.toNontrivial
  have h2 : Nontrivial ↥C := (QuotientGroup.mk_surjective (s := Subgroup.center ↥C)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot C).1 h2

theorem a10t1_sub_center_sup {Y : Type*} [Group Y] {A B : Subgroup Y}
    (hA : IsSimpleGroup ↥A) (hAn : ¬ IsMulCommutative ↥A) (hB : IsSimpleGroup ↥B)
    (hBn : ¬ IsMulCommutative ↥B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {z : Y}
    (hz : z ∈ A ⊔ B) (hzc : ∀ n ∈ A ⊔ B, n * z = z * n) : z = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := a10t1_sub_mem_sup_prod
    (fun a ha b hb => by rw [hAB a ha b hb, mul_inv_cancel_right]; exact hb) hz
  have hcA : ∀ a' ∈ A, a' * a = a * a' := by
    intro a' ha'
    have h := hzc a' (Subgroup.mem_sup_left ha')
    refine mul_right_cancel (b := b) ?_
    calc a' * a * b = a' * (a * b) := mul_assoc _ _ _
      _ = a * b * a' := h
      _ = a * (b * a') := mul_assoc _ _ _
      _ = a * (a' * b) := by rw [hAB a' ha' b hb]
      _ = a * a' * b := (mul_assoc _ _ _).symm
  have hcB : ∀ b' ∈ B, b' * b = b * b' := by
    intro b' hb'
    have h := hzc b' (Subgroup.mem_sup_right hb')
    refine mul_left_cancel (a := a) ?_
    calc a * (b' * b) = a * b' * b := (mul_assoc _ _ _).symm
      _ = b' * a * b := by rw [hAB a ha b' hb']
      _ = b' * (a * b) := mul_assoc _ _ _
      _ = a * b * b' := h
      _ = a * (b * b') := mul_assoc _ _ _
  have ha1 := a10t1_sub_center_triv hA hAn ha hcA
  have hb1 := a10t1_sub_center_triv hB hBn hb hcB
  simp [ha1, hb1]

theorem a10t1_sub_quasi_ne_sup {Y : Type*} [Group Y] {A B C : Subgroup Y}
    (hA : IsSimpleGroup ↥A) (hAn : ¬ IsMulCommutative ↥A) (hB : IsSimpleGroup ↥B)
    (hBn : ¬ IsMulCommutative ↥B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥)
    (hq : CFSG.IsQuasisimple ↥C) : C ≠ A ⊔ B := by
  intro hCN
  have hAC : A ≤ C := hCN ▸ le_sup_left
  have hBC : B ≤ C := hCN ▸ le_sup_right
  have hZ : Subgroup.center ↥C = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_center_iff] at hz
    have hz1 : (z : Y) = 1 := by
      refine a10t1_sub_center_sup hA hAn hB hBn hAB (hCN ▸ z.2) (fun n hn => ?_)
      exact congrArg Subtype.val (hz ⟨n, hCN ▸ hn⟩)
    exact (Subgroup.mem_bot).2 (Subtype.ext hz1)
  haveI : IsSimpleGroup (↥C ⧸ Subgroup.center ↥C) := hq.2.1
  have hbij : Function.Bijective (QuotientGroup.mk' (Subgroup.center ↥C)) := by
    refine ⟨(injective_iff_map_eq_one _).2 (fun x hx => ?_), QuotientGroup.mk'_surjective _⟩
    have : x ∈ Subgroup.center ↥C := (QuotientGroup.eq_one_iff x).1 hx
    rw [hZ] at this
    exact (Subgroup.mem_bot).1 this
  haveI hCs : IsSimpleGroup ↥C := (MulEquiv.ofBijective _ hbij).isSimpleGroup
  have hAN : (A.subgroupOf C).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hAC).2 (fun h k hh hk => ?_)
    rw [hCN] at hk
    obtain ⟨a, ha, b, hb, rfl⟩ := a10t1_sub_mem_sup_prod
      (fun a ha b hb => by rw [hAB a ha b hb, mul_inv_cancel_right]; exact hb) hk
    have : a * b * h * (a * b)⁻¹ = a * h * a⁻¹ := by
      have hc : b * h = h * b := (hAB h hh b hb).symm
      calc a * b * h * (a * b)⁻¹ = a * (b * h) * b⁻¹ * a⁻¹ := by group
        _ = a * (h * b) * b⁻¹ * a⁻¹ := by rw [hc]
        _ = a * h * a⁻¹ := by group
    rw [this]
    exact A.mul_mem (A.mul_mem ha hh) (A.inv_mem ha)
  haveI := hAN
  rcases hCs.eq_bot_or_eq_top_of_normal (A.subgroupOf C) with h | h
  · rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hAC] at h
    exact (Subgroup.nontrivial_iff_ne_bot A).1 hA.toNontrivial h
  · have hCA : C ≤ A := Subgroup.subgroupOf_eq_top.1 h
    have hBA : B ≤ A := hBC.trans hCA
    have : B = ⊥ :=
      calc B = B ⊓ A := (inf_of_le_left hBA).symm
        _ = A ⊓ B := inf_comm _ _
        _ = ⊥ := hinf
    exact (Subgroup.nontrivial_iff_ne_bot B).1 hB.toNontrivial this

theorem a10_subnormal_direct {X : Type} [Group X] {A B C : Subgroup X} (hA : IsSimpleGroup ↥A)
    (hAn : ¬ IsMulCommutative ↥A) (hB : IsSimpleGroup ↥B) (hBn : ¬ IsMulCommutative ↥B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) (hCle : C ≤ A ⊔ B)
    (hC : C.IsSubnormal) (hq : CFSG.IsQuasisimple ↥C) : C = A ∨ C = B := by
  have hcases := a10t1_sub_subnormal_cases hA hAn hB hBn hAB hC
  rw [inf_eq_left.2 hCle] at hcases
  rcases hcases with h | h | h | h
  · exact absurd h (a10t1_sub_quasi_ne_bot hq)
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (a10t1_sub_quasi_ne_sup hA hAn hB hBn hAB hinf hq)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
