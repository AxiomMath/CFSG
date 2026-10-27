module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KMBasic
public import CFSG.LargeExtraspecial.AS35IExtra

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S3.KM

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Extra (S : Subgroup G) (z : G) : Prop where
  two : IsPGroup 2 S
  zS : z ∈ S
  z1 : z ≠ 1
  z2 : z ^ 2 = 1
  center : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) ↔ (s = 1 ∨ s = z)
  comm_mem : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ = 1 ∨ ⁅s, t⁆ = z
  sq_mem : ∀ s ∈ S, s ^ 2 = 1 ∨ s ^ 2 = z
  nonab : ∃ s ∈ S, ∃ t ∈ S, s * t ≠ t * s

namespace Extra

variable {S : Subgroup G} {z : G}

theorem z_central (h : Extra S z) : ∀ t ∈ S, z * t = t * z := fun t ht =>
  (h.center z h.zS).2 (Or.inr rfl) t ht

theorem isExtraspecial (h : Extra S z) : IsExtraspecialPGroup 2 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : ∀ w : S, w ∈ Subgroup.center S ↔ ((w : G) = 1 ∨ (w : G) = z) := by
    intro w
    rw [Subgroup.mem_center_iff]
    constructor
    · intro hw
      refine (h.center w w.2).1 (fun t ht => ?_)
      have := hw ⟨t, ht⟩
      exact (congrArg Subtype.val this).symm
    · intro hw g
      refine Subtype.ext ?_
      exact ((h.center w w.2).2 hw g g.2).symm
  have hcom : _root_.commutator S = Subgroup.center S := by
    apply le_antisymm
    · unfold _root_.commutator
      rw [Subgroup.commutator_le]
      intro x _ y _
      rw [hcen]
      exact h.comm_mem x x.2 y y.2
    · intro w hw
      rcases (hcen w).1 hw with h1 | h1
      · have : w = 1 := Subtype.ext h1
        rw [this]; exact one_mem _
      · obtain ⟨s, hs, t, ht, hst⟩ := h.nonab
        have hc : ⁅s, t⁆ = z := by
          rcases h.comm_mem s hs t ht with h2 | h2
          · exact absurd ((commutatorElement_eq_one_iff_mul_comm.1 h2)) hst
          · exact h2
        have : w = ⁅(⟨s, hs⟩ : S), (⟨t, ht⟩ : S)⁆ := Subtype.ext (by
          rw [h1, ← hc]; rfl)
        rw [this]
        exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
  have hzcen : (⟨z, h.zS⟩ : S) ∈ Subgroup.center S := (hcen _).2 (Or.inr rfl)
  refine ⟨h.two, hcom, ?_, ?_⟩
  · haveI : Fact (IsPGroup 2 S) := ⟨h.two⟩
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro w (hw | ⟨x, rfl⟩)
      · rw [← hcom]; exact hw
      · rw [SetLike.mem_coe, hcen]
        rcases h.sq_mem x x.2 with h2 | h2
        · left; simpa using h2
        · right; simpa using h2
    · intro w hw
      rw [← hcom] at hw
      exact Subgroup.subset_closure (Or.inl hw)
  · rw [Nat.card_eq_two_iff' (1 : Subgroup.center S)]
    refine ⟨⟨⟨z, h.zS⟩, hzcen⟩, ?_, ?_⟩
    · intro h1
      have := congrArg (fun w : Subgroup.center S => ((w : S) : G)) h1
      exact h.z1 this
    · intro y hy
      have hy' := (hcen y.1).1 y.2
      rcases hy' with h1 | h1
      · exact absurd (Subtype.ext (Subtype.ext h1)) hy
      · exact Subtype.ext (Subtype.ext h1)

theorem card_cent_mul (h : Extra S z) {B : Subgroup G} (hB : B ≤ S) (hzB : z ∈ B) :
    Nat.card ↥(S ⊓ centralizer (B : Set G)) * Nat.card B = 2 * Nat.card S := by
  have hcenB : Subgroup.center S ≤ B.subgroupOf S := by
    intro w hw
    have : (w : G) = 1 ∨ (w : G) = z := by
      have := (Subgroup.mem_center_iff.1 hw)
      exact (h.center w w.2).1 (fun t ht => (congrArg Subtype.val (this ⟨t, ht⟩)).symm)
    rw [mem_subgroupOf]
    rcases this with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact hzB
  have key := CFSG.LargeExtraspecial.Asc22.card_centralizer_mul_card h.isExtraspecial hcenB
  have h1 : Nat.card ↥(centralizer ((B.subgroupOf S : Subgroup S) : Set S)) =
      Nat.card ↥(S ⊓ centralizer (B : Set G)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : S) : G), mem_inf.2 ⟨(x : S).2, mem_centralizer_iff.2
          (fun b hb => ?_)⟩⟩
        invFun := fun y => ⟨⟨(y : G), (mem_inf.1 y.2).1⟩, mem_centralizer_iff.2
          (fun b hb => ?_)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have := mem_centralizer_iff.1 x.2 ⟨b, hB hb⟩
        (by rw [SetLike.mem_coe, mem_subgroupOf]; exact hb)
      exact congrArg Subtype.val this
    · have hb' : ((b : S) : G) ∈ B := hb
      have hyc := mem_centralizer_iff.1 (mem_inf.1 y.2).2 ((b : S) : G) hb'
      exact Subtype.ext hyc
  have h2 : Nat.card (B.subgroupOf S) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv
  rw [h1, h2] at key
  exact key

theorem exists_maxAbelian (h : Extra S z) :
    ∃ P : Subgroup G, P ≤ S ∧ z ∈ P ∧ (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
      Nat.card P * Nat.card P = 2 * Nat.card S := by
  classical
  let Q : Subgroup G → Prop := fun P => P ≤ S ∧ z ∈ P ∧ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x
  have hQ0 : Q (zpowers z) := by
    refine ⟨zpowers_le.2 h.zS, mem_zpowers z, ?_⟩
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
    rw [← zpow_add, ← zpow_add, add_comm]
  obtain ⟨P, hP, hPmax⟩ := (wellFounded_gt (α := Subgroup G)).has_min {P | Q P} ⟨_, hQ0⟩
  obtain ⟨hPS, hzP, hPc⟩ := hP
  refine ⟨P, hPS, hzP, hPc, ?_⟩
  have hcen : S ⊓ centralizer (P : Set G) = P := by
    apply le_antisymm
    · intro y hy
      obtain ⟨hyS, hyC⟩ := mem_inf.1 hy
      by_contra hyP
      set P' := P ⊔ zpowers y with hP'
      have hP'le : P < P' := by
        refine lt_of_le_of_ne le_sup_left fun he => hyP ?_
        rw [he]
        exact (le_sup_right : zpowers y ≤ P ⊔ zpowers y) (mem_zpowers y)
      have hQP' : Q P' := by
        refine ⟨sup_le hPS (zpowers_le.2 hyS), (le_sup_left : P ≤ P ⊔ zpowers y) hzP, ?_⟩
        exact comm_sup_of_commuting hPc (comm_zpowers y)
          (fun x hx y' hy' => by
            obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hy'
            exact (Commute.zpow_right (mem_centralizer_iff.1 hyC x hx) i :
              Commute x (y ^ i)).eq)
      exact hPmax P' hQP' hP'le
    · exact le_inf hPS (fun x hx => by
        rw [mem_centralizer_iff]
        intro y hy
        exact hPc y hy x hx)
  have := h.card_cent_mul hPS hzP
  rw [hcen] at this
  exact this

theorem card_S_of_rank (h : Extra S z)
    (hrank : ∀ V : Subgroup G, V ≤ S → IsElemAbelian 2 V → Nat.card V ≤ 4) :
    Nat.card S = 8 ∨ Nat.card S = 32 := by
  obtain ⟨P, hPS, hzP, hPc, hPcard⟩ := h.exists_maxAbelian
  obtain ⟨V, hVP, hVe, hVc⟩ := exists_elemAbelian_card_le hPc
    (fun x hx => h.sq_mem x (hPS hx))
  have hV4 := hrank V (hVP.trans hPS) hVe
  have hP8 : Nat.card P ≤ 8 := by omega
  have hS3 : 3 ≤ Nat.card S := by
    by_contra hlt
    push Not at hlt
    obtain ⟨s, hs, t, ht, hst⟩ := h.nonab
    have hsc : ¬ (s = 1 ∨ s = z) := by
      rintro hsz
      exact hst (((h.center s hs).2 hsz) t ht)
    have hsc' : s ≠ 1 ∧ s ≠ z := by
      push Not at hsc
      exact hsc
    have := eq_of_card_le_two (V := S) (by omega) hs h.zS hsc'.1 h.z1
    exact hsc'.2 this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (h.two.to_le hPS).exists_card_eq
  have hk3 : k ≤ 3 := by
    by_contra hk3
    push Not at hk3
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
    omega
  rw [hk] at hPcard
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  · omega
  · omega
  · left; omega
  · right; omega

theorem exists_inner (h : Extra S z) {t : G}
    (ht : ∀ s ∈ S, t * s = s * t ∨ t * s = z * s * t) :
    ∃ s₀ ∈ S, ∀ s ∈ S, (t * s₀⁻¹) * s = s * (t * s₀⁻¹) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : z * z = 1 := by rw [← pow_two]; exact h.z2
  have hzt : t * z = z * t := by
    rcases ht z h.zS with h1 | h1
    · exact h1
    · exfalso
      have h2 : t * z = t := by rw [h1, hzz, one_mul]
      exact h.z1 (mul_left_cancel (a := t) (by rw [h2, mul_one]))
  set K : Subgroup G := S ⊓ centralizer ({t} : Set G) with hK
  have hmemK : ∀ s, s ∈ K ↔ s ∈ S ∧ s * t = t * s := fun s => by
    rw [hK, mem_inf, mem_centralizer_singleton_iff]
  have hzK : z ∈ K := (hmemK z).2 ⟨h.zS, hzt.symm⟩
  have hKS : K ≤ S := inf_le_left
  set τ : G ≃* G := MulAut.conj t with hτdef
  have hτ : ∀ x, τ x = t * x * t⁻¹ := fun x => rfl
  have hτK : ∀ x, x ∈ K → τ x = x := by
    intro x hx
    rw [hτ, ← ((hmemK x).1 hx).2]
    exact mul_inv_cancel_right x t
  have hτn : ∀ x ∈ S, x ∉ K → τ x = z * x := by
    intro x hx hxK
    rcases ht x hx with h1 | h1
    · exact absurd ((hmemK x).2 ⟨hx, h1.symm⟩) hxK
    · rw [hτ, h1, mul_inv_cancel_right]
  have hτz : τ z = z := hτK z hzK
  by_cases hKS' : S ≤ K
  · refine ⟨1, one_mem _, fun x hx => ?_⟩
    have := ((hmemK x).1 (hKS' hx)).2
    simp only [inv_one, mul_one]
    exact this.symm
  obtain ⟨s₁, hs₁, hs₁K⟩ := SetLike.not_le_iff_exists.1 hKS'
  have hcos : ∀ s ∈ S, s ∉ K → ∀ s' ∈ S, s' ∉ K → s⁻¹ * s' ∈ K := by
    intro s hs hsK s' hs' hs'K
    refine (hmemK _).2 ⟨S.mul_mem (S.inv_mem hs) hs', ?_⟩
    have h1 : τ (s⁻¹ * s') = s⁻¹ * s' := by
      rw [map_mul, map_inv, hτn s hs hsK, hτn s' hs' hs'K]
      group
    rw [hτ] at h1
    have := mul_inv_eq_iff_eq_mul.1 h1
    exact this.symm
  have hidx : (K.subgroupOf S).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s₁, hs₁⟩, fun b => ?_⟩
    by_cases hb : (b : G) ∈ K
    · right
      refine ⟨hb, fun hba => hs₁K ?_⟩
      have hba' : (b : G) * s₁ ∈ K := hba
      have := K.mul_mem (K.inv_mem hb) hba'
      simpa using this
    · left
      refine ⟨?_, hb⟩
      have h1 := hcos (b : G)⁻¹ (S.inv_mem b.2) (fun h' => hb (by simpa using K.inv_mem h')) s₁ hs₁ hs₁K
      rw [mem_subgroupOf]
      simpa using h1
  have hcardK : Nat.card K * 2 = Nat.card S := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf S)
    rw [hidx, Nat.card_congr (subgroupOfEquivOfLe hKS).toEquiv] at h1
    exact h1
  have hcent := h.card_cent_mul hKS hzK
  have hD4 : Nat.card ↥(S ⊓ centralizer (K : Set G)) = 4 := by
    have hpos : 0 < Nat.card K := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hcent, ← hcardK]
    ring
  obtain ⟨s₀, hs₀D, hs₀z⟩ : ∃ s₀ ∈ S ⊓ centralizer (K : Set G), ¬ (s₀ = 1 ∨ s₀ = z) := by
    by_contra hcon
    push Not at hcon
    have hle : S ⊓ centralizer (K : Set G) ≤ zpowers z := by
      intro y hy
      rcases hcon y hy with hy1 | hy1
      · rw [hy1]; exact one_mem _
      · rw [hy1]; exact mem_zpowers z
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card (zpowers z) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hzz) h.z1
    omega
  obtain ⟨hs₀S, hs₀C⟩ := mem_inf.1 hs₀D
  have hs₀K : ∀ k ∈ K, k * s₀ = s₀ * k := fun k hk => mem_centralizer_iff.1 hs₀C k hk
  have hs₀nc : ∀ s ∈ S, s ∉ K → s₀ * s ≠ s * s₀ := by
    intro s hs hsK hcomm
    apply hs₀z
    refine (h.center s₀ hs₀S).1 (fun x hx => ?_)
    by_cases hxK : x ∈ K
    · exact (hs₀K x hxK).symm
    · have hsx : s⁻¹ * x ∈ K := hcos s hs hsK x hx hxK
      have h1 := hs₀K _ hsx
      have : x = s * (s⁻¹ * x) := by group
      rw [this]
      calc s₀ * (s * (s⁻¹ * x)) = (s₀ * s) * (s⁻¹ * x) := by group
        _ = (s * s₀) * (s⁻¹ * x) := by rw [hcomm]
        _ = s * (s₀ * (s⁻¹ * x)) := by group
        _ = s * ((s⁻¹ * x) * s₀) := by rw [h1]
        _ = s * (s⁻¹ * x) * s₀ := by group
  refine ⟨s₀, hs₀S, fun x hx => ?_⟩
  by_cases hxK : x ∈ K
  · have h1 : x * s₀ = s₀ * x := hs₀K x hxK
    have h2 : t * x = x * t := ((hmemK x).1 hxK).2.symm
    have h3 : s₀⁻¹ * x = x * s₀⁻¹ := (Commute.inv_left (show Commute s₀ x from h1.symm)).eq
    calc t * s₀⁻¹ * x = t * (s₀⁻¹ * x) := by group
      _ = t * (x * s₀⁻¹) := by rw [h3]
      _ = (t * x) * s₀⁻¹ := by group
      _ = (x * t) * s₀⁻¹ := by rw [h2]
      _ = x * (t * s₀⁻¹) := by group
  ·
    have hcz : s₀ * x * s₀⁻¹ * x⁻¹ = z := by
      rcases h.comm_mem s₀ hs₀S x hx with h1 | h1
      · exact absurd ((commutatorElement_eq_one_iff_mul_comm.1 h1)) (hs₀nc x hx hxK)
      · exact h1
    have h1 : s₀ * x = z * x * s₀ := by
      calc s₀ * x = (s₀ * x * s₀⁻¹ * x⁻¹) * x * s₀ := by group
        _ = z * x * s₀ := by rw [hcz]
    have hzs : z * s₀⁻¹ = s₀⁻¹ * z := h.z_central _ (S.inv_mem hs₀S)
    have key : z * (s₀⁻¹ * x * s₀) = x := by
      calc z * (s₀⁻¹ * x * s₀) = (z * s₀⁻¹) * x * s₀ := by group
        _ = (s₀⁻¹ * z) * x * s₀ := by rw [hzs]
        _ = s₀⁻¹ * (z * x * s₀) := by group
        _ = s₀⁻¹ * (s₀ * x) := by rw [← h1]
        _ = x := by group
    have h2 : s₀⁻¹ * x * s₀ = z * x := by
      calc s₀⁻¹ * x * s₀ = z * (z * (s₀⁻¹ * x * s₀)) := by rw [← mul_assoc, hzz, one_mul]
        _ = z * x := by rw [key]
    have h3 : τ (s₀⁻¹ * x * s₀) = x := by
      rw [h2, map_mul, hτz, hτn x hx hxK]
      calc z * (z * x) = (z * z) * x := by group
        _ = x := by rw [hzz, one_mul]
    rw [hτ] at h3
    have h4 : t * (s₀⁻¹ * x * s₀) = x * t := mul_inv_eq_iff_eq_mul.1 h3
    calc t * s₀⁻¹ * x = t * (s₀⁻¹ * x * s₀) * s₀⁻¹ := by group
      _ = x * t * s₀⁻¹ := by rw [h4]
      _ = x * (t * s₀⁻¹) := by group

end Extra

end CFSG.LocalAnalysis.GLTheoremA.S3.KM
