module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec85a
import CFSG.Goldschmidt.Steps.Sec85c
import CFSG.Goldschmidt.Steps.Sec87c
import CFSG.Goldschmidt.Steps.Sec87f
import CFSG.Goldschmidt.Steps.Sec87g
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem isMulCommutative_commutator (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a b : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1) (hba : b ≠ a) {P : Subgroup G}
    (hSP : (S : Subgroup G) ≤ Subgroup.normalizer (P : Set G))
    (huniq : ∀ t ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (P : Set G), t ^ 2 = 1 →
      t = 1 ∨ t = a)
    (hAD : A ≤ ⁅(S : Subgroup G), (S : Subgroup G)⁆)
    (hC2 : ∀ u ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆, u ^ 2 = 1 → u ∈ A)
    (hC3 : ∀ y ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆, y ^ 2 ∈ Subgroup.centralizer (P : Set G) →
      y ∈ Subgroup.centralizer (P : Set G) ∨ b * y ∈ Subgroup.centralizer (P : Set G)) :
    IsMulCommutative (⁅(S : Subgroup G), (S : Subgroup G)⁆ : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnab
  obtain ⟨hexp, hZA, hcard⟩ := higman_data hset h4 hAD hC2 hnab
  set D := ⁅(S : Subgroup G), (S : Subgroup G)⁆ with hD
  have hDS : D ≤ S := commutator_self_le _
  have hDp : IsPGroup 2 D := S.isPGroup'.to_le hDS
  set C := Subgroup.centralizer (P : Set G) with hC
  have hb2 : b * b = 1 := mul_self_eq_one hset.elem hb
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have haC : a ∈ C := by
    rcases hC3 a (hAD ha) (by rw [hset.elem.2 a ha]; exact C.one_mem) with h | h
    · exact h
    · exfalso
      have hba2 : (b * a) ^ 2 = 1 := hset.elem.2 _ (A.mul_mem hb ha)
      rcases huniq (b * a) ⟨hset.le (A.mul_mem hb ha), h⟩ hba2 with h1 | h1
      · exact hba (by rw [← mul_inv_eq_one, inv_eq_of_mul_eq_one_right
          (mul_self_eq_one hset.elem ha)]; exact h1)
      · exact hb1 (by simpa using h1)
  set K₁ := D ⊓ C with hK₁
  have hK₁D : K₁ ≤ D := inf_le_left
  have hDK₁ : D ≤ Subgroup.normalizer (K₁ : Set G) := fun y hy =>
    mem_normalizer_inf (Subgroup.le_normalizer hy) (normalizer_le_normalizer_centralizer P
      (hSP (hDS hy)))
  have hK₁inv : ∀ k ∈ K₁, k ^ 2 = 1 → k = 1 ∨ k = a := fun k hk hk2 =>
    huniq k ⟨hDS hk.1, hk.2⟩ hk2
  have hord2 : ∀ {X : Type} [Group X] (y : X), orderOf y = 2 → y ^ 2 = 1 := fun y hy => by
    rw [← hy]
    exact pow_orderOf_eq_one y
  have hord1 : ∀ {X : Type} [Group X] (y : X), orderOf y = 2 → y ≠ 1 := fun y hy h => by
    rw [h, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have hK₁8 : Nat.card K₁ ≤ 8 := by
    refine card_le_eight (hDp.to_le hK₁D) (fun k k' hk hk' => Subtype.ext ?_) fun k =>
      Subtype.ext (by simpa using hexp _ (hK₁D k.2))
    have e1 := (hK₁inv k k.2 (by simpa using congrArg Subtype.val (hord2 k hk))).resolve_left
      fun h => hord1 k hk (Subtype.ext h)
    have e2 := (hK₁inv k' k'.2 (by simpa using congrArg Subtype.val (hord2 k' hk'))).resolve_left
      fun h => hord1 k' hk' (Subtype.ext h)
    rw [e1, e2]
  have hnormal : (K₁.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₁D).mpr hDK₁
  have hbD : b ∈ D := hAD hb
  have hQ8 : Nat.card (D ⧸ K₁.subgroupOf D) ≤ 8 := by
    have hQinv : ∀ q : D ⧸ K₁.subgroupOf D, orderOf q = 2 →
        q = (QuotientGroup.mk (⟨b, hbD⟩ : D))⁻¹ := by
      intro q hq
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      have hy2 : (y : G) ^ 2 ∈ K₁ := by
        have := hord2 _ hq
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
        simpa using this
      have hyK : (y : G) ∉ K₁ := fun h => hord1 _ hq (by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact h)
      rcases hC3 y y.2 hy2.2 with h | h
      · exact absurd ⟨y.2, h⟩ hyK
      · rw [eq_inv_iff_mul_eq_one, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
          Subgroup.mem_subgroupOf]
        have hyb : (y : G) * b = b * y := Subgroup.mem_centralizer_iff.mp
          (le_centralizer hset h4 (hDS y.2)) b hb |>.symm
        show (y : G) * b ∈ K₁
        rw [hyb]
        exact ⟨D.mul_mem hbD y.2, h⟩
    refine card_le_eight (hDp.to_quotient _) (fun q q' hq hq' => (hQinv q hq).trans
      (hQinv q' hq').symm) fun q => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy4 : y ^ 4 = 1 := Subtype.ext (by simpa using hexp _ y.2)
    rw [← QuotientGroup.mk_pow, hy4]
    rfl
  have hDcard : Nat.card D = Nat.card (D ⧸ K₁.subgroupOf D) * Nat.card K₁ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (K₁.subgroupOf D),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₁D).toEquiv]
  obtain ⟨x, hxS, hxaA, hxa⟩ := exists_mem_normalizer_sylow hset h4 ha ha1
  have hxD : x ∈ Subgroup.normalizer (D : Set G) := mem_normalizer_commutator hxS
  have hxxD : x * x ∈ Subgroup.normalizer (D : Set G) := Subgroup.mul_mem _ hxD hxD
  have hxA : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.inv_mem _ (normalizer_le_normalizer hset hxS)
  have hxC : x⁻¹ ∉ Subgroup.centralizer (A : Set G) := fun h => hxa (by
    have := conj_eq_of_mem_centralizer h ha
    simpa using this)
  have hσ := (conj_conj_eq_mul hset h4 hxA hxC ha ha1).2
  simp only [inv_inv] at hσ
  set K₂ := conjSub x K₁ with hK₂
  set K₃ := conjSub (x * x) K₁ with hK₃
  obtain ⟨hK₂D, hDK₂⟩ := conjSub_le_and_le_normalizer hK₁D hDK₁ hxD
  obtain ⟨hK₃D, hDK₃⟩ := conjSub_le_and_le_normalizer hK₁D hDK₁ hxxD
  have hinvK : ∀ g : G, ∀ z ∈ conjSub g K₁, z ^ 2 = 1 → z = 1 ∨ z = g⁻¹ * a * g := by
    intro g z hz hz2
    rcases hK₁inv _ (mem_conjSub.mp hz) (conj_sq_eq_one hz2) with h | h
    · left
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · right
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = g⁻¹ * a * g := by rw [h]
  have hx2 : (x * x)⁻¹ * a * (x * x) = a * (x⁻¹ * a * x) := by
    rw [← hσ]
    group
  have hK₂p : IsPGroup 2 K₂ := hDp.to_le hK₂D
  have h12 : K₁ ⊓ K₂ = ⊥ := inf_eq_bot_of_involutions (hDp.to_le hK₁D) hK₁inv (hinvK x)
    (Ne.symm hxa)
  have h13 : K₁ ⊓ K₃ = ⊥ := inf_eq_bot_of_involutions (hDp.to_le hK₁D) hK₁inv (hinvK (x * x))
    (by rw [hx2]; intro h; exact conj_ne_one (n := x⁻¹) ha1 (by simpa using
      (mul_eq_left.mp h.symm)))
  have h23 : K₂ ⊓ K₃ = ⊥ := inf_eq_bot_of_involutions hK₂p (hinvK x) (hinvK (x * x))
    (by rw [hx2]; intro h; exact ha1 (by simpa using (mul_eq_right.mp h.symm)))
  have hcK₂ : Nat.card K₂ = Nat.card K₁ := card_conjSub _ _
  have hcK₃ : Nat.card K₃ = Nat.card K₁ := card_conjSub _ _
  have hsq : Nat.card K₁ * Nat.card K₁ ≤ Nat.card D := by
    have := card_mul_card_le hK₂D hK₃D h23
    rwa [hcK₂, hcK₃] at this
  have hcase1 : Nat.card K₁ * Nat.card K₁ = Nat.card D → False := by
    intro heq
    have hsup : K₂ ⊔ K₃ = D := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hK₂D hK₃D) ?_
      have := card_mul_card_le (D := K₂ ⊔ K₃) le_sup_left le_sup_right h23
      rw [hcK₂, hcK₃, heq] at this
      exact this
    have hcent : D ≤ Subgroup.centralizer (K₁ : Set G) := by
      rw [← hsup]
      refine sup_le (fun z hz => Subgroup.mem_centralizer_iff.mpr fun k hk => ?_)
        (fun z hz => Subgroup.mem_centralizer_iff.mpr fun k hk => ?_)
      · exact commute_of_inf_eq_bot hK₁D hK₂D hDK₁ hDK₂ h12 hk hz
      · exact commute_of_inf_eq_bot hK₁D hK₃D hDK₁ hDK₃ h13 hk hz
    have hK₁a : K₁ ≤ Subgroup.zpowers a := fun k hk => by
      have hkA : k ∈ A := hZA k (hK₁D hk) fun y hy =>
        Subgroup.mem_centralizer_iff.mp (hcent hy) k hk
      rcases hK₁inv k hk (hset.elem.2 k hkA) with h | h
      · exact h ▸ Subgroup.one_mem _
      · exact h ▸ Subgroup.mem_zpowers a
    have h2 : Nat.card K₁ ≤ 2 := (Subgroup.card_le_of_le hK₁a).trans (by
      rw [Nat.card_zpowers, orderOf_eq_prime (hset.elem.2 a ha) ha1])
    have : Nat.card D ≤ 4 := by
      rw [← heq]
      exact Nat.mul_le_mul h2 h2
    rcases hcard with h | h <;> omega
  have hcase2 : Nat.card K₁ ≤ 2 → False := by
    intro h2
    have hc2 : Nat.card K₁ ∣ 2 := by
      have h0 : 0 < Nat.card K₁ := Nat.card_pos
      rcases (show Nat.card K₁ = 1 ∨ Nat.card K₁ = 2 by omega) with h | h <;> simp [h]
    have hK₁sq : ∀ k ∈ K₁, k = 1 ∨ k = a := fun k hk => hK₁inv k hk (by
      have h1 := (orderOf_dvd_natCard (⟨k, hk⟩ : K₁)).trans hc2
      have := orderOf_dvd_iff_pow_eq_one.mp h1
      simpa using congrArg Subtype.val this)
    obtain ⟨g, hgD, hg2⟩ : ∃ g ∈ D, g ^ 2 ≠ 1 := by
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      refine hnab ⟨⟨fun u v => Subtype.ext ?_⟩⟩
      have hu := hall u u.2
      have hv := hall v v.2
      have huv := hall _ (D.mul_mem u.2 v.2)
      rw [sq] at hu hv huv
      show (u : G) * v = v * u
      calc (u : G) * v = ((u : G) * v)⁻¹ := (inv_eq_of_mul_eq_one_right huv).symm
        _ = (v : G)⁻¹ * (u : G)⁻¹ := mul_inv_rev _ _
        _ = v * u := by rw [inv_eq_of_mul_eq_one_right hu, inv_eq_of_mul_eq_one_right hv]
    have hg2A : g ^ 2 ∈ A := hC2 _ (D.pow_mem hgD 2) (by rw [← pow_mul]; exact hexp g hgD)
    obtain ⟨h, hhD, hh2⟩ : ∃ h ∈ D, h ^ 2 = a := by
      rcases mem_four hset.elem h4 ha hxaA hg2A ha1 (by simpa using conj_ne_one (n := x⁻¹) ha1)
        (Ne.symm hxa) with h | h | h | h
      · exact absurd h hg2
      · exact ⟨g, hgD, h⟩
      · refine ⟨x * g * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxD g).mp hgD, ?_⟩
        rw [conj_pow, h]
        group
      · refine ⟨(x * x) * g * (x * x)⁻¹, (Subgroup.mem_normalizer_iff.mp hxxD g).mp hgD, ?_⟩
        rw [conj_pow, h, ← hx2]
        group
    rcases hC3 h hhD (by rw [hh2]; exact haC) with hC' | hC'
    · rcases hK₁sq h ⟨hhD, hC'⟩ with h1 | h1
      · rw [h1, one_pow] at hh2
        exact ha1 hh2.symm
      · rw [h1, hset.elem.2 a ha] at hh2
        exact ha1 hh2.symm
    · rcases hK₁sq (b * h) ⟨D.mul_mem hbD hhD, hC'⟩ with h1 | h1
      · have : h = b := by rw [← hbi]; exact eq_inv_of_mul_eq_one_right h1
        rw [this, hset.elem.2 b hb] at hh2
        exact ha1 hh2.symm
      · have : h = b * a := by
          calc h = b⁻¹ * (b * h) := by group
            _ = b * a := by rw [h1, hbi]
        rw [this, hset.elem.2 _ (A.mul_mem hb ha)] at hh2
        exact ha1 hh2.symm
  obtain ⟨j, hj⟩ := (hDp.to_le hK₁D).exists_card_eq
  have hj3 : j ≤ 3 := by
    by_contra hj3
    have : 2 ^ 4 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases j
  · exact hcase2 (by rw [hj]; norm_num)
  · exact hcase2 (by rw [hj]; norm_num)
  · refine hcase1 ?_
    rcases hcard with h | h
    · rw [hj, h]; norm_num
    · rw [hDcard, hj] at h
      omega
  · refine hcase1 ?_
    rcases hcard with h | h
    · have := hsq
      rw [hj, h] at this
      norm_num at this
    · rw [hj, h]; norm_num

end CFSG.Goldschmidt.Sec8
