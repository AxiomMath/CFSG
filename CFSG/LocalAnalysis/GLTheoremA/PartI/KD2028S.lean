module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD2028SMat
public import CFSG.ClassicalInvolution.PerfectCase.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Mathieu
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCard
public import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB

@[expose] def KD2028S : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    (IsHatSix L ∨ IsHatSeven L ∨ IsHatMTwentyTwo L ∨ IsSLThreeExc L ∨
      (IsSUThreeExc L ∧ ¬ IsSUThreeTwoPow L)) →
    ∀ x : L, orderOf x = 3 → ∃ T : Subgroup L, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      x ∈ Subgroup.normalizer (T : Set L)

private abbrev KdsN {L : Type} [Group L] (x : L) : Prop :=
  ∃ T : Subgroup L, T ≠ ⊥ ∧ IsPGroup 2 T ∧ x ∈ Subgroup.normalizer (T : Set L)

private def Ae2 {G : Type*} [Group G] (σ : G) : Prop :=
  ∃ W : Subgroup G, W ≠ ⊥ ∧ (∀ w ∈ W, w ^ 2 = 1) ∧ (∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) ∧
    ∀ w ∈ W, σ * w * σ⁻¹ ∈ W

private theorem Ae2.map {G H : Type*} [Group G] [Group H] (f : G ≃* H) {σ : G} (h : Ae2 σ) :
    Ae2 (f σ) := by
  obtain ⟨W, hW1, hW2, hWc, hWn⟩ := h
  refine ⟨W.map f.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hW1
    apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
    rw [h0, Subgroup.map_bot]
  · rintro _ ⟨w, hw, rfl⟩
    show f w ^ 2 = 1
    rw [← map_pow, hW2 w hw, map_one]
  · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    show f w * f w' = f w' * f w
    rw [← map_mul, ← map_mul, hWc w hw w' hw']
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨σ * w * σ⁻¹, hWn w hw, by simp⟩

private theorem Ae2.of_klein {G : Type*} [Group G] {σ v₁ v₂ : G} (h1 : v₁ ^ 2 = 1)
    (h2 : v₂ ^ 2 = 1) (hc : v₁ * v₂ = v₂ * v₁) (hne : v₁ ≠ 1) (hσ1 : σ * v₁ * σ⁻¹ = v₂)
    (hσ2 : σ * v₂ * σ⁻¹ = v₁ * v₂) : Ae2 σ := by
  set W := Subgroup.closure ({v₁, v₂} : Set G) with hW
  have hv₁ : v₁ ∈ W := Subgroup.subset_closure (by simp)
  have hv₂ : v₂ ∈ W := Subgroup.subset_closure (by simp)
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    letI := Subgroup.closureCommGroupOfComm (k := ({v₁, v₂} : Set G)) (by
      intro a ha b hb _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact Commute.refl _
      · exact hc
      · exact hc.symm
      · exact Commute.refl _)
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : W) ⟨b, hb⟩)
  refine ⟨W, ?_, ?_, hcomm, ?_⟩
  · intro h0
    rw [h0, Subgroup.mem_bot] at hv₁
    exact hne hv₁
  · intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact h1
      · rw [Set.mem_singleton_iff.mp hx]; exact h2
    | one => simp
    | mul a b ha hb iha ihb =>
      rw [Commute.mul_pow (hcomm a ha b hb), iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  · intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · rw [hσ1]; exact hv₂
      · rw [Set.mem_singleton_iff.mp hx, hσ2]; exact W.mul_mem hv₁ hv₂
    | one => simp [W.one_mem]
    | mul a b ha hb iha ihb =>
      rw [show σ * (a * b) * σ⁻¹ = (σ * a * σ⁻¹) * (σ * b * σ⁻¹) by group]
      exact W.mul_mem iha ihb
    | inv a ha iha =>
      rw [show σ * a⁻¹ * σ⁻¹ = (σ * a * σ⁻¹)⁻¹ by group]
      exact W.inv_mem iha

private theorem Ae2.of_comm {G : Type*} [Group G] {σ t : G} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hc : σ * t = t * σ) : Ae2 σ := by
  have hcomm : Commute σ t := hc
  refine ⟨Subgroup.zpowers t, ?_, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.zpowers_eq_bot]
    exact ht1
  · intro w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  · intro w hw w' hw'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
    exact (Commute.zpow_zpow_self t m n).eq
  · intro w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have e : σ * t ^ m * σ⁻¹ = t ^ m := by
      rw [(hcomm.zpow_right m).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩

private theorem kds_isPGroup_two {G : Type*} [Group G] (T : Subgroup G) (h : ∀ g ∈ T, g ^ 2 = 1) :
    IsPGroup 2 T := by
  intro g
  refine ⟨1, ?_⟩
  show g ^ 2 = 1
  exact Subtype.ext (by simpa using h g.1 g.2)

private theorem kds_mem_normalizer {G : Type*} [Group G] (T : Subgroup G) {x : G} (hx : x ^ 3 = 1)
    (h : ∀ g ∈ T, x * g * x⁻¹ ∈ T) : x ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro g
  refine ⟨fun hg => h g hg, fun hg => ?_⟩
  have h2 := h _ (h _ hg)
  have e : x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = g := by
    have hxxx : x * x * x = 1 := (pow_three' x).symm.trans hx
    have hxi : x⁻¹ * x⁻¹ * x⁻¹ = 1 := by
      rw [show x⁻¹ * x⁻¹ * x⁻¹ = (x * x * x)⁻¹ by simp [mul_inv_rev, mul_assoc], hxxx, inv_one]
    calc x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * g * (x⁻¹ * x⁻¹ * x⁻¹) := by
          simp only [mul_assoc]
      _ = g := by rw [hxxx, hxi]; simp
  rwa [e] at h2

private theorem kds_comm_of_sq {L : Type} [Group L] (hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1)
    {g h : L} (hg : g ^ 2 = 1) (hh : h ^ 2 = 1)
    (hm : (g : L ⧸ Subgroup.center L) * (h : L ⧸ Subgroup.center L) =
      (h : L ⧸ Subgroup.center L) * (g : L ⧸ Subgroup.center L)) : g * h = h * g := by
  have hgg : g * g = 1 := by rw [← sq]; exact hg
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hh' : h⁻¹ = h := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hh)
  have hcz : g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hm]
    group
  set c := g * h * g⁻¹ * h⁻¹ with hc_def
  have hcen : ∀ y : L, y * c = c * y := fun y => Subgroup.mem_center_iff.mp hcz y
  have hc3 : c ^ 3 = 1 := hZ3 c hcz
  have e1 : g * c * g⁻¹ = c := by rw [hcen g, mul_assoc, mul_inv_cancel, mul_one]
  have e2 : g * c * g⁻¹ = h * g * h * g := by
    have : g * c * g⁻¹ = g * g * (h * g⁻¹ * h⁻¹ * g⁻¹) := by rw [hc_def]; group
    rw [this, hgg, one_mul, hg', hh']
  have e3 : c⁻¹ = h * g * h * g := by
    have : c⁻¹ = h * g * h⁻¹ * g⁻¹ := by rw [hc_def]; group
    rw [this, hg', hh']
  have hcc : c * c = 1 := mul_eq_one_iff_inv_eq.mpr (by rw [e3, ← e2, e1])
  have hc1 : c = 1 := by
    rw [pow_three, hcc, mul_one] at hc3
    exact hc3
  calc g * h = c * (h * g) := by rw [hc_def]; group
    _ = h * g := by rw [hc1, one_mul]

private def kdsHatT {L : Type} [Group L] (hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1)
    (W : Subgroup (L ⧸ Subgroup.center L)) (hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) :
    Subgroup L where
  carrier := {g | g ^ 2 = 1 ∧ (g : L ⧸ Subgroup.center L) ∈ W}
  one_mem' := ⟨by rw [one_pow], by rw [QuotientGroup.mk_one]; exact W.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha2, ha⟩ ⟨hb2, hb⟩
    have hab : Commute a b := kds_comm_of_sq hZ3 ha2 hb2 (hWc _ ha _ hb)
    refine ⟨?_, ?_⟩
    · rw [hab.mul_pow, ha2, hb2, one_mul]
    · rw [QuotientGroup.mk_mul]
      exact W.mul_mem ha hb
  inv_mem' := by
    rintro a ⟨ha2, ha⟩
    refine ⟨?_, ?_⟩
    · rw [inv_pow, ha2, inv_one]
    · rw [QuotientGroup.mk_inv]
      exact W.inv_mem ha

private theorem kds_hat {L : Type} [Group L] (hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1) {x : L}
    (hx : x ^ 3 = 1) (h : Ae2 (x : L ⧸ Subgroup.center L)) : KdsN x := by
  obtain ⟨W, hWne, hW2, hWc, hWn⟩ := h
  have hT : kdsHatT hZ3 W hWc ≠ ⊥ := by
    obtain ⟨⟨w, hwW⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
    have hw1' : (w : L ⧸ Subgroup.center L) ≠ 1 := fun h => hw1 (Subtype.ext h)
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective w
    have hg2 : g₀ ^ 2 ∈ Subgroup.center L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hW2 _ hwW]
    have ht2 : (g₀ ^ 3) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact hZ3 _ hg2
    have h3w : ((g₀ : L) : L ⧸ Subgroup.center L) ^ 3 = (g₀ : L ⧸ Subgroup.center L) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hW2 _ hwW, one_mul]
    have htW : ((g₀ ^ 3 : L) : L ⧸ Subgroup.center L) ∈ W := by
      rw [QuotientGroup.mk_pow, h3w]
      exact hwW
    have htne : g₀ ^ 3 ≠ 1 := by
      intro h
      apply hw1'
      have h' : ((g₀ ^ 3 : L) : L ⧸ Subgroup.center L) = 1 := by
        rw [h, QuotientGroup.mk_one]
      rw [QuotientGroup.mk_pow, h3w] at h'
      exact h'
    intro hbot
    have hmem : g₀ ^ 3 ∈ kdsHatT hZ3 W hWc := ⟨ht2, htW⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact htne hmem
  refine ⟨kdsHatT hZ3 W hWc, hT, kds_isPGroup_two _ (fun g hg => hg.1), ?_⟩
  refine kds_mem_normalizer _ hx ?_
  rintro g ⟨hg2, hgW⟩
  refine ⟨?_, ?_⟩
  · rw [show (x * g * x⁻¹) ^ 2 = x * g ^ 2 * x⁻¹ by rw [sq, sq]; group, hg2, mul_one,
      mul_inv_cancel]
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hWn _ hgW

private theorem kds_of_comm_involution {G : Type} [Group G] {x g : G} (hg2 : g ^ 2 = 1)
    (hg1 : g ≠ 1) (hc : x * g = g * x) : KdsN x := by
  have hcomm : Commute x g := hc
  refine ⟨Subgroup.zpowers g, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.zpowers_eq_bot]
    exact hg1
  · apply kds_isPGroup_two
    intro w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg2,
      one_zpow]
  · apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (hcomm.zpow_right m).eq.symm

section Alt

open Equiv Equiv.Perm

private theorem kds_cycleType_three {n : ℕ} (hn : n ≤ 7) {σ : Perm (Fin n)}
    (h3 : orderOf σ = 3) : σ.cycleType = {3} ∨ σ.cycleType = {3, 3} := by
  have hne : σ.cycleType ≠ 0 := by
    intro h0
    have := cycleType_eq_zero.mp h0
    rw [this, orderOf_one] at h3
    omega
  have hall : ∀ m ∈ σ.cycleType, m = 3 := by
    intro m hm
    have hd := dvd_of_mem_cycleType hm
    rw [h3] at hd
    have h2 := two_le_of_mem_cycleType hm
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h <;> omega
  have hsum : σ.cycleType.sum ≤ n := by
    rw [sum_cycleType]
    calc σ.support.card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  obtain ⟨k, hk⟩ : ∃ k, σ.cycleType = Multiset.replicate k 3 :=
    ⟨_, Multiset.eq_replicate_of_mem hall⟩
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne hk
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  · exact (hk0 rfl).elim
  · left; simpa using hk
  · right; simpa using hk

private theorem kds_ae2_alt {n : ℕ} (hn : n ≤ 7) (τ₁ τ₂ : alternatingGroup (Fin n))
    (h1 : (τ₁ : Perm (Fin n)).cycleType = {3}) (h2 : (τ₂ : Perm (Fin n)).cycleType = {3, 3})
    (a1 : Ae2 τ₁) (a2 : Ae2 τ₂) {σ : alternatingGroup (Fin n)} (hσ : orderOf σ = 3) : Ae2 σ := by
  have hσ' : orderOf (σ : Perm (Fin n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hσ
  have key : ∀ τ : alternatingGroup (Fin n),
      (τ : Perm (Fin n)).cycleType = (σ : Perm (Fin n)).cycleType → Ae2 τ → Ae2 σ := by
    intro τ hτ aτ
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr hτ.symm)
    have hθ : MulAut.conjNormal (H := alternatingGroup (Fin n)) c σ = τ :=
      Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hc)
    have := Ae2.map (MulAut.conjNormal (H := alternatingGroup (Fin n)) c).symm aτ
    rwa [← hθ, MulEquiv.symm_apply_apply] at this
  rcases kds_cycleType_three hn hσ' with h | h
  · exact key τ₁ (by rw [h1, h]) a1
  · exact key τ₂ (by rw [h2, h]) a2

private theorem kds_ae2_alt67 {n : ℕ} (hn : n = 6 ∨ n = 7) {σ : alternatingGroup (Fin n)}
    (hσ : orderOf σ = 3) : Ae2 σ := by
  rcases hn with rfl | rfl <;>
  · refine kds_ae2_alt (by norm_num)
      ⟨swap 0 1 * swap 0 2, mem_alternatingGroup.mpr (by decide)⟩
      ⟨(swap 0 1 * swap 0 2) * (swap 3 4 * swap 3 5), mem_alternatingGroup.mpr (by decide)⟩
      ?_ ?_ ?_ ?_ hσ
    · exact (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType
    · show (swap _ _ * swap _ _ * (swap _ _ * swap _ _) : Perm (Fin _)).cycleType = {3, 3}
      rw [Disjoint.cycleType_mul (by unfold Equiv.Perm.Disjoint; decide),
        (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType,
        (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType]
      rfl
    · refine Ae2.of_klein
        (v₁ := ⟨swap 0 1 * swap 2 3, mem_alternatingGroup.mpr (by decide)⟩)
        (v₂ := ⟨swap 0 2 * swap 1 3, mem_alternatingGroup.mpr (by decide)⟩) ?_ ?_ ?_ ?_ ?_ ?_ <;>
      first
        | exact Subtype.ext (by decide)
        | (intro h; exact absurd (congrArg Subtype.val h) (by decide))
    · refine Ae2.of_klein
        (v₁ := ⟨swap 0 3 * swap 2 5, mem_alternatingGroup.mpr (by decide)⟩)
        (v₂ := ⟨swap 2 5 * swap 1 4, mem_alternatingGroup.mpr (by decide)⟩) ?_ ?_ ?_ ?_ ?_ ?_ <;>
      first
        | exact Subtype.ext (by decide)
        | (intro h; exact absurd (congrArg Subtype.val h) (by decide))

end Alt

private theorem kds_exp_center {L : Type} [Group L] [Finite L]
    (hZ : Nat.card (Subgroup.center L) = 3) : ∀ z ∈ Subgroup.center L, z ^ 3 = 1 := by
  intro z hz
  have h := congrArg Subtype.val (pow_card_eq_one' (G := ↥(Subgroup.center L)) (x := ⟨z, hz⟩))
  rw [hZ] at h
  simpa using h

private theorem kds_bar_order {L : Type} [Group L] {x : L} (hx3 : orderOf x = 3)
    (hxZ : x ∉ Subgroup.center L) : orderOf (x : L ⧸ Subgroup.center L) = 3 := by
  have hxp : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow, hxp, QuotientGroup.mk_one]
  · exact fun h => hxZ ((QuotientGroup.eq_one_iff x).mp h)

private theorem kds_hatAlt {L : Type} [Group L] [Finite L] {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (e : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n)) {x : L} (hx3 : orderOf x = 3)
    (hxZ : x ∉ Subgroup.center L) : KdsN x := by
  have hxp : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hord : orderOf (e (x : L ⧸ Subgroup.center L)) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact kds_bar_order hx3 hxZ
  have h2 := Ae2.map e.symm (kds_ae2_alt67 hn hord)
  rw [MulEquiv.symm_apply_apply] at h2
  exact kds_hat (kds_exp_center hZ) hxp h2

private theorem kds_hatSix {L : Type} [Group L] [Finite L] (h : IsHatSix L) {x : L}
    (hx3 : orderOf x = 3) (hxZ : x ∉ Subgroup.center L) : KdsN x := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  exact kds_hatAlt (n := 6) (Or.inl rfl) hZ e hx3 hxZ

private theorem kds_hatSeven {L : Type} [Group L] [Finite L] (h : IsHatSeven L) {x : L}
    (hx3 : orderOf x = 3) (hxZ : x ∉ Subgroup.center L) : KdsN x := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  exact kds_hatAlt (n := 7) (Or.inr rfl) hZ e hx3 hxZ

private theorem kds_m22_centralizer
    (s : ↥CFSG.Blueprint.NativeSporadic.M22) (hs : orderOf s = 3) :
    Nat.card ↥(Subgroup.centralizer ({s} : Set ↥CFSG.Blueprint.NativeSporadic.M22)) = 36 := by
  have hx : (s : Equiv.Perm (Fin 22)) ∈ CFSG.Blueprint.NativeSporadic.M22 := s.2
  have hx3 : orderOf (s : Equiv.Perm (Fin 22)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hs
  obtain ⟨c, hc, hcard⟩ := CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_sound
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data
    CFSG.HardMathSupport.Solomon.Coordinator.rep_m22A
    CFSG.HardMathSupport.Solomon.Coordinator.rep_m22B
    Certificates.certificate13511.2.2.1 (s : Equiv.Perm (Fin 22)) hx hx3
  have h36 : ∀ c < CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data.cases.size,
      CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data.cases[c]!.card = 36 := by
    decide +kernel
  have key : Nat.card ↥((Subgroup.centralizer ({s} : Set ↥CFSG.Blueprint.NativeSporadic.M22)).map
      CFSG.Blueprint.NativeSporadic.M22.subtype) =
      Nat.card ↥(Subgroup.centralizer ({s} : Set ↥CFSG.Blueprint.NativeSporadic.M22)) :=
    Subgroup.card_map_of_injective CFSG.Blueprint.NativeSporadic.M22.subtype_injective
  rw [← key, CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype]
  exact hcard.trans (h36 c hc)

private theorem kds_hatM22 {L : Type} [Group L] [Finite L]
    (h : IsHatMTwentyTwo L) {x : L} (hx3 : orderOf x = 3) (hxZ : x ∉ Subgroup.center L) :
    KdsN x := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  have hxp : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  obtain ⟨ψ⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  set xb : L ⧸ Subgroup.center L := (x : L ⧸ Subgroup.center L) with hxb
  set s : ↥CFSG.Blueprint.NativeSporadic.M22 := ψ.symm (e xb) with hs_def
  have hs : orderOf s = 3 := by
    rw [hs_def, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
    exact kds_bar_order hx3 hxZ
  have h2 : 2 ∣ Nat.card ↥(Subgroup.centralizer
      ({s} : Set ↥CFSG.Blueprint.NativeSporadic.M22)) := by
    rw [kds_m22_centralizer s hs]
    norm_num
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ht' : orderOf (t : ↥CFSG.Blueprint.NativeSporadic.M22) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact ht
  have hst : s * (t : ↥CFSG.Blueprint.NativeSporadic.M22) =
      (t : ↥CFSG.Blueprint.NativeSporadic.M22) * s :=
    Subgroup.mem_centralizer_iff.mp t.2 s (Set.mem_singleton s)
  set u : L ⧸ Subgroup.center L := e.symm (ψ (t : ↥CFSG.Blueprint.NativeSporadic.M22)) with hu
  have hu2 : u ^ 2 = 1 := by
    rw [hu, ← map_pow, ← map_pow, ← ht', pow_orderOf_eq_one, map_one, map_one]
  have hu1 : u ≠ 1 := by
    intro h1
    have : (t : ↥CFSG.Blueprint.NativeSporadic.M22) = 1 := by
      have h' := congrArg (fun y => ψ.symm (e y)) h1
      simpa [hu] using h'
    rw [this, orderOf_one] at ht'
    omega
  have hxu : xb * u = u * xb := by
    have h' : ψ s * ψ (t : ↥CFSG.Blueprint.NativeSporadic.M22) =
        ψ (t : ↥CFSG.Blueprint.NativeSporadic.M22) * ψ s := by
      rw [← map_mul, ← map_mul, hst]
    have h'' := congrArg e.symm h'
    simp only [map_mul, hs_def, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply] at h''
    exact h''
  exact kds_hat (kds_exp_center hZ) hxp (Ae2.of_comm hu2 hu1 hxu)

section Classical

open Matrix

variable {K : Type} [Field K]

private theorem kds_exists_cube_root (K : Type) [Field K] [Finite K] (h3 : Nat.card K % 3 = 1) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units K]
    have : 0 < Nat.card K := Nat.card_pos
    omega
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hdvd
  rw [orderOf_eq_prime_iff] at hg
  refine ⟨(g : K), ?_, fun e => hg.2 (Units.ext e)⟩
  rw [← Units.val_pow_eq_pow_val, hg.1, Units.val_one]

private theorem kds_two_ne_zero_of_card (K : Type) [Field K] [Finite K] {q : ℕ}
    (hq : Nat.card K = q ^ 2) (hodd : q % 2 = 1) : (2 : K) ≠ 0 := by
  intro h2
  letI := Fintype.ofFinite K
  have hchar : ringChar K = 2 := by
    haveI : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by simpa using h2)
    exact ringChar.eq K 2
  have hev := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card, hq] at hev
  have ho : q ^ 2 % 2 = 1 := Nat.odd_iff.mp (Nat.odd_iff.mpr hodd).pow
  omega

private theorem kds_card_sq (K : Type) [Field K] [Finite K] {q : ℕ} (hq : Nat.card K = q ^ 2) :
    ∃ p f : ℕ, Fact p.Prime ∧ CharP K p ∧ q = p ^ f := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hp, hm⟩ := FiniteField.card K (ringChar K)
  have hKc : q ^ 2 = ringChar K ^ (m : ℕ) := by
    rw [← hq, Nat.card_eq_fintype_card, hm]
  have hdq : q ∣ ringChar K ^ (m : ℕ) := ⟨q, by rw [← hKc, sq]⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hdq
  exact ⟨ringChar K, i, ⟨hp⟩, ringChar.charP K, hi⟩

private theorem kds_matrix_data {H : Subgroup (GL (Fin 3) K)} {y : ↥H} (hy3 : orderOf y = 3)
    (hyZ : y ∉ Subgroup.center ↥H) :
    ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 ∧
      ∀ c : K, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
        c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  refine ⟨?_, ?_⟩
  · have h : y ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy3] at this
    have := congrArg (fun g : ↥H => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
    simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using this
  · intro c hc
    apply hyZ
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hc]
    simp [Matrix.mul_smul, Matrix.smul_mul]

private def kdsGL (t : Matrix (Fin 3) (Fin 3) K) (h : t * t = 1) : GL (Fin 3) K :=
  ⟨t, t, h, h⟩

private theorem kds_slThree (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1)
    (y : ↥(StatedSL 3 K)) (hy3 : orderOf y = 3) (hyZ : y ∉ Subgroup.center ↥(StatedSL 3 K)) :
    KdsN y := by
  obtain ⟨ω, hω3, hω1⟩ := kds_exists_cube_root K hK
  obtain ⟨hxp, hns⟩ := kds_matrix_data hy3 hyZ
  have hy3' : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3] at this
  set x : Matrix (Fin 3) (Fin 3) K := ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hx
  by_cases h2 : (2 : K) = 0
  · obtain ⟨P, Q, α, β, hQP, hP, hQ, hxP, hQx⟩ := kds_even_matrix hω3 hω1 hxp hns
    have hxinv : (((y : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = x ^ 2 :=
      Units.inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hxp)
    refine ⟨(kdsUnip P Q hQP).subgroupOf (StatedSL 3 K), ?_, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := kds_exists_mul_ne_zero hP hQ
      intro hbot
      have hmem : (⟨kdsUnipGL hQP z, CFSG.Open.StatedAPI.mem_statedSL_of_det
          (kdsPyQ_det hQP h2 z)⟩ : ↥(StatedSL 3 K)) ∈
          (kdsUnip P Q hQP).subgroupOf (StatedSL 3 K) :=
        Subgroup.mem_subgroupOf.mpr (kdsUnipGL_mem hQP z)
      rw [hbot, Subgroup.mem_bot] at hmem
      have h1 := congrArg (fun g : ↥(StatedSL 3 K) =>
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hmem
      apply hz
      have h1' : (1 : Matrix (Fin 3) (Fin 3) K) + P * z * Q = 1 := h1
      simpa using h1'
    · apply kds_isPGroup_two
      intro g hg
      obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.mp hg
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, sq, hz, kdsPyQ_sq hQP h2]
      rfl
    · refine kds_mem_normalizer _ hy3' (fun g hg => ?_)
      obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.mp hg
      have hconj : (((y * g * y⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) =
          x * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x ^ 2 := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
          hxinv]
      refine Subgroup.mem_subgroupOf.mpr ⟨(α * β) • z, ?_⟩
      show (((y * g * y⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
      rw [hconj, hz]
      exact kdsPyQ_conj hxp hxP hQx z
  · obtain ⟨t, htt, ht1, hdet, hcomm, -⟩ := kds_odd_matrix hω3 hω1 h2 hxp hns
    refine kds_of_comm_involution (g := (⟨kdsGL t htt,
      CFSG.Open.StatedAPI.mem_statedSL_of_det hdet⟩ : ↥(StatedSL 3 K))) ?_ ?_ ?_
    · apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, sq]
      exact htt
    · intro h
      apply ht1
      have := congrArg (fun g : ↥(StatedSL 3 K) =>
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
      exact this
    · apply Subtype.ext
      apply Units.ext
      exact hcomm

private theorem kds_suThree (K : Type) [Field K] [Finite K] (q : ℕ) (hq : Nat.card K = q ^ 2)
    (hq3 : q % 3 = 2) (hqodd : q % 2 = 1) (y : ↥(StatedSU 3 q K)) (hy3 : orderOf y = 3)
    (hyZ : y ∉ Subgroup.center ↥(StatedSU 3 q K)) : KdsN y := by
  have hK : Nat.card K % 3 = 1 := by rw [hq, Nat.pow_mod, hq3]
  obtain ⟨ω, hω3, hω1⟩ := kds_exists_cube_root K hK
  have h2 : (2 : K) ≠ 0 := kds_two_ne_zero_of_card K hq hqodd
  obtain ⟨hxp, hns⟩ := kds_matrix_data hy3 hyZ
  have hqe : q = 3 * (q / 3) + 2 := by omega
  obtain ⟨p, f, hp, hchar, hqf⟩ := kds_card_sq K hq
  subst hqf
  set σ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K p f with hσ
  have hmem : ∀ A : GL (Fin 3) K, A ∈ StatedSU 3 (p ^ f) K ↔
      (A : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
        ((A : Matrix (Fin 3) (Fin 3) K).map σ)ᵀ * (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
    intro A
    rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hq 3]
    exact CFSG.LieType.Universal.Unitary.mem_SUid
  have hy := (hmem _).1 y.2
  set x : Matrix (Fin 3) (Fin 3) K := ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hx
  have hxs : (x.map σ.toRingHom)ᵀ = x ^ 2 := by
    have h3 : x * x ^ 2 = 1 := by rw [← pow_succ']; exact hxp
    calc (x.map σ.toRingHom)ᵀ = (x.map σ.toRingHom)ᵀ * (x * x ^ 2) := by rw [h3, Matrix.mul_one]
      _ = ((x.map σ.toRingHom)ᵀ * x) * x ^ 2 := by rw [Matrix.mul_assoc]
      _ = x ^ 2 := by rw [show (x.map σ.toRingHom)ᵀ * x = 1 from hy.2, Matrix.one_mul]
  have hσω : σ.toRingHom ω = ω ^ 2 := by
    show σ ω = ω ^ 2
    rw [hσ, CFSG.LieType.BorelTits.unitaryInvolution_apply, hqe, pow_add, pow_mul, hω3, one_pow,
      one_mul]
  obtain ⟨t, htt, ht1, hdet, hcomm, hstar⟩ := kds_odd_matrix hω3 hω1 h2 hxp hns
  have hts : (t.map σ.toRingHom)ᵀ = t := hstar σ.toRingHom hσω hxs
  have hgmem : kdsGL t htt ∈ StatedSU 3 (p ^ f) K := by
    rw [hmem]
    refine ⟨hdet, ?_⟩
    show (t.map σ)ᵀ * t = 1
    have : (t.map σ)ᵀ = t := hts
    rw [this]
    exact htt
  refine kds_of_comm_involution (g := (⟨kdsGL t htt, hgmem⟩ : ↥(StatedSU 3 (p ^ f) K))) ?_ ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, sq]
    exact htt
  · intro h
    apply ht1
    have := congrArg (fun g : ↥(StatedSU 3 (p ^ f) K) =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
    exact this
  · apply Subtype.ext
    apply Units.ext
    exact hcomm

end Classical

private theorem kds_two_dvd_card {L : Type} [Group L] [Finite L]
    (hQ : CFSG.Open.IsQuasisimple L) : 2 ∣ Nat.card L := by
  by_contra h
  have hodd : Odd (Nat.card L) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  have : Group.IsSolvable L := CFSG.Milestones.odd_order_solvable hodd
  obtain ⟨hc, hs⟩ := hQ
  have : Nontrivial L := (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
  have : Group.IsPerfect L := ⟨hc⟩
  exact Group.IsPerfect.not_isSolvable L ‹_›

private theorem kds_central {L : Type} [Group L] [Finite L] (h2 : 2 ∣ Nat.card L) {x : L}
    (hx : x ∈ Subgroup.center L) : KdsN x := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht] at this
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  exact kds_of_comm_involution ht2 ht1 (Subgroup.mem_center_iff.mp hx t).symm

private theorem kds_transport {L M : Type} [Group L] [Group M] (e : L ≃* M) {x : L}
    (h : KdsN (e x)) : KdsN x := by
  obtain ⟨T, hT, hT2, hN⟩ := h
  have hmem : ∀ z : L, z ∈ T.map e.symm.toMonoidHom ↔ e z ∈ T := fun z => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  refine ⟨T.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro h0
    apply hT
    apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
    rw [h0, Subgroup.map_bot]
  · intro g
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp g.2
    obtain ⟨k, hk⟩ := hT2 ⟨y, hy⟩
    have hk' : y ^ 2 ^ k = 1 := by
      have h1 := congrArg Subtype.val hk
      simpa using h1
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hyg, ← map_pow, hk', map_one]
  · rw [Subgroup.mem_set_normalizer_iff]
    intro y
    have hN' := Subgroup.mem_set_normalizer_iff.mp hN (e y)
    simp only [SetLike.mem_coe, hmem, map_mul, map_inv] at hN' ⊢
    exact hN'

private theorem kds_not_center {L M : Type} [Group L] [Group M] (e : L ≃* M) {x : L}
    (hx : x ∉ Subgroup.center L) : e x ∉ Subgroup.center M := by
  intro hc
  apply hx
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro g
  have h1 := hc (e g)
  apply e.injective
  simpa using h1

private theorem kds_two_pow_mod_nine {i : ℕ} (h : 2 ^ i % 9 = 2 ∨ 2 ^ i % 9 = 5) :
    i % 2 = 1 ∧ i % 3 ≠ 0 := by
  have h6 : 2 ^ i % 9 = 2 ^ (i % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod i 6, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [h6] at h
  have hcases : i % 6 = 0 ∨ i % 6 = 1 ∨ i % 6 = 2 ∨ i % 6 = 3 ∨ i % 6 = 4 ∨ i % 6 = 5 := by
    omega
  rcases hcases with h0 | h0 | h0 | h0 | h0 | h0 <;> rw [h0] at h <;> (try norm_num at h) <;>
    omega

private theorem kds_suThree_odd {L : Type} [Group L] (hQ : CFSG.Open.IsQuasisimple L)
    (h : IsSUThreeExc L) (hnot : ¬ IsSUThreeTwoPow L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧ q % 3 = 2 ∧
      q % 2 = 1 ∧ Nonempty (L ≃* ↥(StatedSU 3 q K)) := by
  obtain ⟨K, hK, hfin, q, hcard, hq9, ⟨e⟩⟩ := h
  have hq3 : q % 3 = 2 := by omega
  by_cases hodd : q % 2 = 1
  · exact ⟨K, hK, hfin, q, hcard, hq3, hodd, ⟨e⟩⟩
  · exfalso
    have hq2 : 2 ∣ q := by omega
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨m, hp, hm⟩ := FiniteField.card K (ringChar K)
    have hKc : q ^ 2 = ringChar K ^ (m : ℕ) := by
      rw [← hcard, Nat.card_eq_fintype_card, hm]
    have h2 : 2 ∣ ringChar K ^ (m : ℕ) := by
      rw [← hKc]
      exact dvd_pow hq2 (by norm_num)
    have hp2 : ringChar K = 2 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)).symm
    rw [hp2] at hKc
    have hdq : q ∣ 2 ^ (m : ℕ) := ⟨q, by rw [← hKc, sq]⟩
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdq
    obtain ⟨hi2, hi3⟩ := kds_two_pow_mod_nine hq9
    have hi0 : i ≠ 0 := by
      rintro rfl
      norm_num at hodd
    by_cases hi1 : i = 1
    · subst hi1
      have hs : Group.IsSolvable (StatedSU 3 (2 ^ 1) K) :=
        CFSG.Quasithin.isSolvable_statedSU_one hcard
      exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hQ
        (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
    · exact hnot ⟨K, hK, hfin, i, hi2, by omega, hi3, hcard, ⟨e⟩⟩

theorem kd2028S_holds : KD2028S := by
  intro L _ _ hQ hcase x hx3
  by_cases hxZ : x ∈ Subgroup.center L
  · exact kds_central (kds_two_dvd_card hQ) hxZ
  · rcases hcase with h | h | h | h | ⟨h, hnot⟩
    · exact kds_hatSix h hx3 hxZ
    · exact kds_hatSeven h hx3 hxZ
    · exact kds_hatM22 h hx3 hxZ
    · obtain ⟨K, hF, hfin, h9, ⟨e⟩⟩ := h
      exact kds_transport e (kds_slThree K (by omega) (e x)
        (by rw [MulEquiv.orderOf_eq]; exact hx3) (kds_not_center e hxZ))
    · obtain ⟨K, hF, hfin, q, hcard, hq3, hqodd, ⟨e⟩⟩ := kds_suThree_odd hQ h hnot
      exact kds_transport e (kds_suThree K q hcard hq3 hqodd (e x)
        (by rw [MulEquiv.orderOf_eq]; exact hx3) (kds_not_center e hxZ))

end CFSG.LocalAnalysis.GLTheoremA
