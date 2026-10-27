module

public import CFSG.ClassicalInvolution.TwoGroupCase.TightEmbedding

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem mem_normalizer_of_commute {X : Subgroup G} {z : G} (h : ∀ x ∈ X, z * x = x * z) :
    z ∈ Subgroup.normalizer (X : Set G) :=
  Subgroup.centralizer_le_normalizer _ (fun x hx => (h x hx).symm)

theorem exists_pow_four_eq_one_pow_two_ne_one {P : Subgroup G} (hP : IsPGroup 2 P) {y : G}
    (hy : y ∈ P) (hy2 : y * y ≠ 1) : ∃ x ∈ P, x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨y, hy⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k
    · have h1 : y = 1 := orderOf_eq_one_iff.mp (by simpa using hk)
      exact hy2 (by rw [h1, mul_one])
    · exact hy2 (by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hk]; simp))
  refine ⟨y ^ 2 ^ (k - 2), P.pow_mem hy _, ?_, ?_⟩
  · rw [← pow_mul]
    have : 2 ^ (k - 2) * 4 = 2 ^ k := by
      have : k = (k - 2) + 2 := by omega
      conv_rhs => rw [this, pow_add]
      norm_num
    rw [this, ← hk]
    exact pow_orderOf_eq_one y
  · rw [← pow_mul]
    intro h
    have hdvd := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hk] at hdvd
    have : 2 ^ k ≤ 2 ^ (k - 2) * 2 := Nat.le_of_dvd (by positivity) hdvd
    have h3 : 2 ^ (k - 2) * 2 = 2 ^ (k - 1) := by
      have : k - 1 = (k - 2) + 1 := by omega
      rw [this, pow_succ]
    rw [h3] at this
    have : 2 ^ k = 2 ^ (k - 1) * 2 := by
      have : k = (k - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
    have : 0 < 2 ^ (k - 1) := by positivity
    omega

theorem exists_central_involution [Finite G] {A : Subgroup G} (hA : IsPGroup 2 A) (hA1 : A ≠ ⊥) :
    ∃ z ∈ A, orderOf z = 2 ∧ ∀ a ∈ A, z * a = a * z := by
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
  have := hA.center_nontrivial
  obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center A)
  have hc1 : (c : A) ≠ 1 := fun h => hc (Subtype.ext h)
  obtain ⟨n, hn⟩ := exists_pow_orderOf_eq_two hA hc1
  refine ⟨(((c : A) ^ n : A) : G), ((c : A) ^ n).2, ?_, fun a ha => ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hn
  · have hmem : ((c : A) ^ n) ∈ Subgroup.center A := Subgroup.pow_mem _ c.2 n
    have h := Subgroup.mem_center_iff.mp hmem ⟨a, ha⟩
    exact (congrArg Subtype.val h).symm

theorem exists_central_involution_commuting [Finite G] {A : Subgroup G} (hA : IsPGroup 2 A)
    (hA1 : A ≠ ⊥) {x : G} (hx : x * x = 1) (hxN : x ∈ Subgroup.normalizer (A : Set G)) :
    ∃ z ∈ A, orderOf z = 2 ∧ (∀ a ∈ A, z * a = a * z) ∧ x * z = z * x := by
  obtain ⟨u, huA, hu2, huc⟩ := exists_central_involution hA hA1
  have huu : u * u = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hu2])
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hxu : x * u * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxN u).mp huA
  by_cases h : x * u * x⁻¹ = u
  · refine ⟨u, huA, hu2, huc, ?_⟩
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  · set v := x * u * x⁻¹ with hv
    have hvc : ∀ a ∈ A, v * a = a * v := by
      intro a ha
      have ha' : x⁻¹ * a * x ∈ A := by
        refine (Subgroup.mem_normalizer_iff.mp hxN (x⁻¹ * a * x)).mpr ?_
        have e : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
        rw [e]; exact ha
      calc v * a = x * (u * (x⁻¹ * a * x)) * x⁻¹ := by rw [hv]; group
        _ = x * ((x⁻¹ * a * x) * u) * x⁻¹ := by rw [huc _ ha']
        _ = a * v := by rw [hv]; group
    have hvv : v * v = 1 := by
      rw [hv]
      calc x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
        _ = 1 := by rw [huu]; group
    have huv : u * v = v * u := huc v hxu
    have hz1 : u * v ≠ 1 := by
      intro h1
      apply h
      have : v = u⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this, inv_eq_of_mul_eq_one_right huu]
    have hz2 : (u * v) * (u * v) = 1 := by
      calc (u * v) * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [← huv]
        _ = (u * u) * (v * v) := by group
        _ = 1 := by rw [huu, hvv, one_mul]
    refine ⟨u * v, A.mul_mem huA hxu, ?_, ?_, ?_⟩
    · rw [← pow_two] at hz2
      exact orderOf_eq_prime hz2 hz1
    · intro a ha
      rw [mul_assoc, hvc a ha, ← mul_assoc, huc a ha, mul_assoc]
    · have hxv : x * v * x⁻¹ = u := by
        rw [hv]
        calc x * (x * u * x⁻¹) * x⁻¹ = (x * x) * u * (x⁻¹ * x⁻¹) := by group
          _ = u := by rw [hx, hxinv, hx]; group
      calc x * (u * v) = (x * u * x⁻¹) * (x * v * x⁻¹) * x := by group
        _ = v * u * x := by rw [← hv, hxv]
        _ = u * v * x := by rw [huv]

@[expose] def PairwiseCommuting (Γ : Set (Subgroup G)) : Prop :=
  ∀ A ∈ Γ, ∀ B ∈ Γ, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a

@[expose] def famSup (Γ : Set (Subgroup G)) : Subgroup G :=
  Subgroup.closure (⋃ A ∈ Γ, (A : Set G))

section FamSup

variable {Γ : Set (Subgroup G)} {A : Subgroup G}

theorem le_famSup (hA : A ∈ Γ) : A ≤ famSup Γ := fun _ hx =>
  Subgroup.subset_closure (Set.mem_biUnion hA hx)

theorem famSup_le {M : Subgroup G} (h : ∀ A ∈ Γ, A ≤ M) : famSup Γ ≤ M := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.mp hx
  exact h B hB hxB

theorem famSup_le_normalizer (hΓ : PairwiseCommuting Γ) (hA : A ∈ Γ) :
    famSup Γ ≤ Subgroup.normalizer (A : Set G) := by
  refine famSup_le fun B hB => ?_
  by_cases hBA : B = A
  · rw [hBA]; exact Subgroup.le_normalizer
  · intro x hxB
    exact Subgroup.centralizer_le_normalizer _ fun a ha => (hΓ B hB A hA hBA x hxB a ha).symm

theorem commute_famSup {z : G} (h : ∀ A ∈ Γ, ∀ a ∈ A, z * a = a * z) :
    ∀ w ∈ famSup Γ, z * w = w * z := by
  have : famSup Γ ≤ Subgroup.centralizer ({z} : Set G) := by
    refine famSup_le fun A hA a ha => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact h A hA a ha
  intro w hw
  exact Subgroup.mem_centralizer_iff.mp (this hw) z (Set.mem_singleton z)

theorem conjSubgroup_famSup_le [Finite G] {s : G} (h : ∀ A ∈ Γ, conjSubgroup s A ∈ Γ) :
    conjSubgroup s (famSup Γ) ≤ famSup Γ := by
  rw [Subgroup.map_le_iff_le_comap]
  refine famSup_le fun A hA x hx => ?_
  exact le_famSup (h A hA) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

theorem mem_normalizer_famSup [Finite G] {s : G} (h : ∀ A ∈ Γ, conjSubgroup s A ∈ Γ) :
    s ∈ Subgroup.normalizer (famSup Γ : Set G) := by
  refine conjSubgroup_eq_self_iff.mp ?_
  exact Subgroup.eq_of_le_of_card_ge (conjSubgroup_famSup_le h) (by rw [card_conjSubgroup])

end FamSup

structure TightFamily (S : Subgroup G) (Δ : Set (Subgroup G)) : Prop where
  two : IsPGroup 2 S
  le : ∀ A ∈ Δ, A ≤ S
  ne_bot : ∀ A ∈ Δ, A ≠ ⊥
  not_elementary : ∀ A ∈ Δ, ∃ y ∈ A, y * y ≠ 1
  conj_mem : ∀ A ∈ Δ, ∀ s ∈ S, conjSubgroup s A ∈ Δ
  normalizer_le : ∀ A ∈ Δ, ∀ X : Subgroup G, X ≤ A → X ≠ ⊥ → ∀ g ∈ S,
    g ∈ Subgroup.normalizer (X : Set G) → g ∈ Subgroup.normalizer (A : Set G)
  commute : ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → B ≤ Subgroup.normalizer (A : Set G) →
    A ⊓ B = ⊥ ∧ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a

namespace TightFamily

variable [Finite G] {S : Subgroup G} {Δ : Set (Subgroup G)}

theorem star (h : TightFamily S Δ) {Γ : Set (Subgroup G)} (hΓΔ : Γ ⊆ Δ)
    (hΓ : PairwiseCommuting Γ) {T Q : Subgroup G} (hT : T ∈ Δ) (hTΓ : T ∉ Γ)
    (hTn : ∀ x ∈ T, ∀ A ∈ Γ, conjSubgroup x A ∈ Γ) (hQ : Q ∈ Γ)
    (hN : T ⊓ Subgroup.normalizer (Q : Set G) ≠ ⊥) :
    ∀ a ∈ Q, ∀ b ∈ T, a * b = b * a := by
  have hQΔ : Q ∈ Δ := hΓΔ hQ
  have hTS : T ≤ S := h.le T hT
  have hQS : Q ≤ S := h.le Q hQΔ
  have hQ2 : IsPGroup 2 Q := h.two.to_le hQS
  have hTW : ∀ x ∈ T, x ∈ Subgroup.normalizer (famSup Γ : Set G) := fun x hx =>
    mem_normalizer_famSup (hTn x hx)
  have hNT2 : IsPGroup 2 (T ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) :=
    h.two.to_le (inf_le_left.trans hTS)
  obtain ⟨x, hxmem, hx2⟩ := exists_mem_orderOf_eq_two_of_isPGroup_subgroup hNT2 hN
  have hxT : x ∈ T := hxmem.1
  have hxN : x ∈ Subgroup.normalizer (Q : Set G) := hxmem.2
  have hxx : x * x = 1 := by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hx2])
  have hx1 : x ≠ 1 := fun e => by rw [e] at hx2; simp at hx2
  obtain ⟨z, hzQ, hz2, hzc, hxz⟩ :=
    exists_central_involution_commuting hQ2 (h.ne_bot Q hQΔ) hxx hxN
  have hzS : z ∈ S := hQS hzQ
  have hz1 : z ≠ 1 := fun e => by rw [e] at hz2; simp at hz2
  have hzW : ∀ w ∈ famSup Γ, z * w = w * z := by
    refine commute_famSup fun A hA a ha => ?_
    rcases eq_or_ne A Q with hAQ | hAQ
    · rw [hAQ] at ha; exact hzc a ha
    · exact hΓ Q hQ A hA (Ne.symm hAQ) z hzQ a ha
  have hzT : z ∈ Subgroup.normalizer (T : Set G) := by
    refine h.normalizer_le T hT (Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hxT)
      (Subgroup.zpowers_eq_bot.not.mpr hx1) z hzS ?_
    refine mem_normalizer_of_commute fun v hv => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (show Commute z x from hxz.symm) k).eq
  have hcom : ∀ y ∈ T, ∀ w ∈ famSup Γ, (z * y * z⁻¹ * y⁻¹) * w = w * (z * y * z⁻¹ * y⁻¹) := by
    intro y hy w hw
    have hzi : ∀ w ∈ famSup Γ, z⁻¹ * w = w * z⁻¹ := fun w hw => by
      calc z⁻¹ * w = z⁻¹ * (w * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * w) * z⁻¹ := by rw [hzW w hw]
        _ = w * z⁻¹ := by group
    have hw' : y⁻¹ * w * y ∈ famSup Γ := by
      have := (Subgroup.mem_normalizer_iff.mp (hTW y⁻¹ (T.inv_mem hy)) w).mp hw
      simpa using this
    have h1 : (y * z⁻¹ * y⁻¹) * w = w * (y * z⁻¹ * y⁻¹) := by
      calc (y * z⁻¹ * y⁻¹) * w = y * (z⁻¹ * (y⁻¹ * w * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * w * y) * z⁻¹) * y⁻¹ := by rw [hzi _ hw']
        _ = w * (y * z⁻¹ * y⁻¹) := by group
    calc (z * y * z⁻¹ * y⁻¹) * w = z * ((y * z⁻¹ * y⁻¹) * w) := by group
      _ = z * (w * (y * z⁻¹ * y⁻¹)) := by rw [h1]
      _ = (z * w) * (y * z⁻¹ * y⁻¹) := by group
      _ = (w * z) * (y * z⁻¹ * y⁻¹) := by rw [hzW w hw]
      _ = w * (z * y * z⁻¹ * y⁻¹) := by group
  by_cases hcase : ∃ y ∈ T, z * y * z⁻¹ * y⁻¹ ≠ 1
  · obtain ⟨y, hyT, hy1⟩ := hcase
    have hcT : z * y * z⁻¹ * y⁻¹ ∈ T :=
      T.mul_mem ((Subgroup.mem_normalizer_iff.mp hzT y).mp hyT) (T.inv_mem hyT)
    have hQN : Q ≤ Subgroup.normalizer (T : Set G) := fun q hq => by
      refine h.normalizer_le T hT (Subgroup.zpowers (z * y * z⁻¹ * y⁻¹))
        (Subgroup.zpowers_le.mpr hcT) (Subgroup.zpowers_eq_bot.not.mpr hy1) q (hQS hq) ?_
      refine mem_normalizer_of_commute fun v hv => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      have hc : Commute (z * y * z⁻¹ * y⁻¹) q := hcom y hyT q (le_famSup hQ hq)
      exact (hc.zpow_left k).symm.eq
    have hne : T ≠ Q := fun e => hTΓ (e ▸ hQ)
    intro a ha b hb
    exact ((h.commute T hT Q hQΔ hne hQN).2 b hb a ha).symm
  · push Not at hcase
    have hzT' : ∀ y ∈ T, z * y = y * z := fun y hy => by
      calc z * y = (z * y * z⁻¹ * y⁻¹) * (y * z) := by group
        _ = y * z := by rw [hcase y hy, one_mul]
    have hTN : T ≤ Subgroup.normalizer (Q : Set G) := fun y hy => by
      refine h.normalizer_le Q hQΔ (Subgroup.zpowers z) (Subgroup.zpowers_le.mpr hzQ)
        (Subgroup.zpowers_eq_bot.not.mpr hz1) y (hTS hy) ?_
      refine mem_normalizer_of_commute fun v hv => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact (Commute.zpow_left (show Commute z y from hzT' y hy) k).symm.eq
    have hne : Q ≠ T := fun e => hTΓ (e ▸ hQ)
    intro a ha b hb
    exact (h.commute Q hQΔ T hT hne hTN).2 a ha b hb

theorem stepA (h : TightFamily S Δ) {Γ : Set (Subgroup G)} (hΓΔ : Γ ⊆ Δ)
    (hΓ : PairwiseCommuting Γ)
    (hmax : ∀ B ∈ Δ, B ∉ Γ → ∃ A ∈ Γ, ∃ a ∈ A, ∃ b ∈ B, a * b ≠ b * a)
    {T : Subgroup G} (hT : T ∈ Δ) (hTΓ : T ∉ Γ)
    (hTn : ∀ x ∈ T, ∀ A ∈ Γ, conjSubgroup x A ∈ Γ) : False := by
  obtain ⟨Q, hQΓ, a, haQ, b, hbT, hab⟩ := hmax T hT hTΓ
  have hQΔ : Q ∈ Δ := hΓΔ hQΓ
  have hTS : T ≤ S := h.le T hT
  have hQS : Q ≤ S := h.le Q hQΔ
  have hWN : famSup Γ ≤ Subgroup.normalizer (Q : Set G) := famSup_le_normalizer hΓ hQΓ
  have hWS : famSup Γ ≤ S := famSup_le fun A hA => h.le A (hΓΔ hA)
  have hTW : ∀ x ∈ T, x ∈ Subgroup.normalizer (famSup Γ : Set G) := fun x hx =>
    mem_normalizer_famSup (hTn x hx)
  have hNT : T ⊓ Subgroup.normalizer (Q : Set G) = ⊥ := by
    by_contra hne
    exact hab (star h hΓΔ hΓ hT hTΓ hTn hQΓ hne a haQ b hbT)
  have hnorm : ∀ g ∈ T, g ≠ 1 → g ∉ Subgroup.normalizer (Q : Set G) := fun g hg hg1 hgN => by
    have : g ∈ T ⊓ Subgroup.normalizer (Q : Set G) := ⟨hg, hgN⟩
    rw [hNT, Subgroup.mem_bot] at this
    exact hg1 this
  obtain ⟨y, hyT, hy2⟩ := h.not_elementary T hT
  obtain ⟨x, hxT, hx4, hx2⟩ := exists_pow_four_eq_one_pow_two_ne_one (h.two.to_le hTS) hyT hy2
  have hx1 : x ≠ 1 := fun e => hx2 (by rw [e]; simp)
  set t : G := x * x with ht
  have htT : t ∈ T := T.mul_mem hxT hxT
  have ht1 : t ≠ 1 := by rw [ht, ← pow_two]; exact hx2
  have htt : t * t = 1 := by
    calc t * t = (x * x) ^ 2 := (pow_two _).symm
      _ = (x ^ 2) ^ 2 := by rw [pow_two x]
      _ = x ^ 4 := by rw [← pow_mul]
      _ = 1 := hx4
  have hxN : x ∉ Subgroup.normalizer (Q : Set G) := hnorm x hxT hx1
  have htN : t ∉ Subgroup.normalizer (Q : Set G) := hnorm t htT ht1
  have hQx : conjSubgroup x Q ∈ Γ := hTn x hxT Q hQΓ
  have hQt : conjSubgroup t Q ∈ Γ := hTn t htT Q hQΓ
  have hQxne : Q ≠ conjSubgroup x Q := fun e => hxN (conjSubgroup_eq_self_iff.mp e.symm)
  have hQtne : Q ≠ conjSubgroup t Q := fun e => htN (conjSubgroup_eq_self_iff.mp e.symm)
  obtain ⟨u, huQ, hu2⟩ :=
    exists_mem_orderOf_eq_two_of_isPGroup_subgroup (h.two.to_le hQS) (h.ne_bot Q hQΔ)
  have huu : u * u = 1 := by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hu2])
  have hu1 : u ≠ 1 := fun e => by rw [e] at hu2; simp at hu2
  have hconj : ∀ g v : G, v * v = 1 → (g * v * g⁻¹) * (g * v * g⁻¹) = 1 := fun g v hv => by
    calc (g * v * g⁻¹) * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
      _ = 1 := by rw [hv]; group
  set u1 : G := x * u * x⁻¹ with hu1def
  set u2 : G := x * u1 * x⁻¹ with hu2def
  set u3 : G := x * u2 * x⁻¹ with hu3def
  have hu1u1 : u1 * u1 = 1 := hconj x u huu
  have hu2u2 : u2 * u2 = 1 := hconj x u1 hu1u1
  have hu3u3 : u3 * u3 = 1 := hconj x u2 hu2u2
  have e_tu : t * u * t⁻¹ = u2 := by rw [ht, hu2def, hu1def]; group
  have e_tu1 : t * u1 * t⁻¹ = u3 := by rw [ht, hu3def, hu2def, hu1def]; group
  have e_tu2 : t * u2 * t⁻¹ = u := by
    calc t * u2 * t⁻¹ = t * (t * u * t⁻¹) * t⁻¹ := by rw [e_tu]
      _ = (t * t) * u * (t * t)⁻¹ := by group
      _ = u := by rw [htt]; group
  have hu1Q : u1 ∈ conjSubgroup x Q := mem_conjSubgroup_of_mem huQ
  have hu2t : u2 ∈ conjSubgroup t Q := by
    rw [← e_tu]; exact mem_conjSubgroup_of_mem huQ
  have hc01 : u * u1 = u1 * u := hΓ Q hQΓ _ hQx hQxne u huQ u1 hu1Q
  have hc02 : u * u2 = u2 * u := hΓ Q hQΓ _ hQt hQtne u huQ u2 hu2t
  have huW : u ∈ famSup Γ := le_famSup hQΓ huQ
  have hu1W : u1 ∈ famSup Γ := le_famSup hQx hu1Q
  have hu2W : u2 ∈ famSup Γ := le_famSup hQt hu2t
  have hxC : ∀ w ∈ famSup Γ, t * w * t⁻¹ = w → x * w = w * x := by
    intro w hw hwt
    have hwS : w ∈ S := hWS hw
    have hwt' : w * t = t * w := by
      have := hwt
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have hwNt : w ∈ Subgroup.normalizer (T : Set G) := by
      refine h.normalizer_le T hT (Subgroup.zpowers t) (Subgroup.zpowers_le.mpr htT)
        (Subgroup.zpowers_eq_bot.not.mpr ht1) w hwS ?_
      refine mem_normalizer_of_commute fun v hv => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact (Commute.zpow_right (show Commute w t from hwt') k).eq
    have hcW : x * w * x⁻¹ * w⁻¹ ∈ famSup Γ :=
      (famSup Γ).mul_mem ((Subgroup.mem_normalizer_iff.mp (hTW x hxT) w).mp hw)
        ((famSup Γ).inv_mem hw)
    have hcT : x * w * x⁻¹ * w⁻¹ ∈ T := by
      have hmem : w * x⁻¹ * w⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hwNt x⁻¹).mp (T.inv_mem hxT)
      have e : x * w * x⁻¹ * w⁻¹ = x * (w * x⁻¹ * w⁻¹) := by group
      rw [e]
      exact T.mul_mem hxT hmem
    have hc1 : x * w * x⁻¹ * w⁻¹ = 1 := by
      have : x * w * x⁻¹ * w⁻¹ ∈ T ⊓ Subgroup.normalizer (Q : Set G) := ⟨hcT, hWN hcW⟩
      rw [hNT, Subgroup.mem_bot] at this
      exact this
    calc x * w = (x * w * x⁻¹ * w⁻¹) * (w * x) := by group
      _ = w * x := by rw [hc1, one_mul]
  have hR1 : u1 * u3 = u * u2 := by
    have h1 : t * (u * u2) * t⁻¹ = u * u2 := by
      calc t * (u * u2) * t⁻¹ = (t * u * t⁻¹) * (t * u2 * t⁻¹) := by group
        _ = u2 * u := by rw [e_tu, e_tu2]
        _ = u * u2 := hc02.symm
    have h2 := hxC (u * u2) ((famSup Γ).mul_mem huW hu2W) h1
    calc u1 * u3 = x * (u * u2) * x⁻¹ := by rw [hu3def, hu1def]; group
      _ = u * u2 := by rw [h2]; group
  have hR1' : u2 * u3 = u * u1 := by
    have e2 : u2 = u * (u1 * u3) := by
      rw [hR1]
      calc u2 = (u * u) * u2 := by rw [huu, one_mul]
        _ = u * (u * u2) := by rw [mul_assoc]
    calc u2 * u3 = u * (u1 * u3) * u3 := by rw [← e2]
      _ = u * u1 * (u3 * u3) := by group
      _ = u * u1 := by rw [hu3u3, mul_one]
  have hR2 : u1 * u2 = u * u1 := by
    have h1 : t * (u * u1) * t⁻¹ = u * u1 := by
      calc t * (u * u1) * t⁻¹ = (t * u * t⁻¹) * (t * u1 * t⁻¹) := by group
        _ = u2 * u3 := by rw [e_tu, e_tu1]
        _ = u * u1 := hR1'
    have h2 := hxC (u * u1) ((famSup Γ).mul_mem huW hu1W) h1
    calc u1 * u2 = x * (u * u1) * x⁻¹ := by rw [hu2def, hu1def]; group
      _ = u * u1 := by rw [h2]; group
  have hu2u : u2 = u := by
    have : u1 * u2 = u1 * u := by rw [hR2, hc01]
    exact mul_left_cancel this
  have hQtΔ : conjSubgroup t Q ∈ Δ := hΓΔ hQt
  have hle : conjSubgroup t Q ≤ Subgroup.normalizer (Q : Set G) := (le_famSup hQt).trans hWN
  have hbot := (h.commute Q hQΔ _ hQtΔ hQtne hle).1
  have : u ∈ Q ⊓ conjSubgroup t Q := ⟨huQ, hu2u ▸ hu2t⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hu1 this

theorem commute_of_ne (h : TightFamily S Δ) {A B : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (hne : A ≠ B) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Γ, hΓmem, hΓmax⟩ := Set.Finite.exists_maximal
    (s := {Γ : Set (Subgroup G) | Γ ⊆ Δ ∧ PairwiseCommuting Γ}) (Set.toFinite _)
    ⟨∅, Set.empty_subset _, fun A hA => absurd hA (Set.notMem_empty _)⟩
  obtain ⟨hΓΔ, hΓ⟩ := hΓmem
  have hmax : ∀ B ∈ Δ, B ∉ Γ → ∃ A ∈ Γ, ∃ a ∈ A, ∃ b ∈ B, a * b ≠ b * a := by
    intro B hBΔ hBΓ
    by_contra hcon
    push Not at hcon
    have hins : insert B Γ ∈ {Γ : Set (Subgroup G) | Γ ⊆ Δ ∧ PairwiseCommuting Γ} := by
      refine ⟨Set.insert_subset hBΔ hΓΔ, ?_⟩
      intro A1 hA1 A2 hA2 hne12 a ha b hb
      rcases hA1 with rfl | hA1 <;> rcases hA2 with rfl | hA2
      · exact absurd rfl hne12
      · exact (hcon A2 hA2 b hb a ha).symm
      · exact hcon A1 hA1 a ha b hb
      · exact hΓ A1 hA1 A2 hA2 hne12 a ha b hb
    exact hBΓ (hΓmax hins (Set.subset_insert B Γ) (Set.mem_insert B Γ))
  set W := famSup Γ with hW
  have hWN : ∀ A ∈ Γ, W ≤ Subgroup.normalizer (A : Set G) := fun A hA => famSup_le_normalizer hΓ hA
  have hWS : W ≤ S := famSup_le fun A hA => h.le A (hΓΔ hA)
  set M : Subgroup G := S ⊓ Subgroup.normalizer (W : Set G) with hM
  have hMS : M ≤ S := inf_le_left
  have hWM : W ≤ M := le_inf hWS Subgroup.le_normalizer
  have hii : ∀ s ∈ S, s ∈ Subgroup.normalizer (W : Set G) →
      ∀ A ∈ Γ, conjSubgroup s A ∈ Γ := by
    intro s hsS hsW A hA
    by_contra hnot
    refine stepA h hΓΔ hΓ hmax (h.conj_mem A (hΓΔ hA) s hsS) hnot ?_
    intro x hx B hB
    have hxW : x ∈ W := by
      have h1 : conjSubgroup s A ≤ conjSubgroup s W :=
        conjSubgroup_mono (le_famSup hA)
      rw [conjSubgroup_eq_self_iff.mpr hsW] at h1
      exact h1 hx
    rw [conjSubgroup_eq_self_iff.mpr (hWN B hB hxW)]
    exact hB
  have hMS' : M = S := by
    by_contra hne'
    obtain ⟨s, hsS, hsN, hsnot⟩ := exists_mem_normalizer_not_mem h.two hMS hne'
    refine hsnot ⟨hsS, mem_normalizer_famSup fun A hA => ?_⟩
    by_contra hnot
    refine stepA h hΓΔ hΓ hmax (h.conj_mem A (hΓΔ hA) s hsS) hnot ?_
    intro x hx B hB
    have hxM : x ∈ M := by
      have h1 : conjSubgroup s A ≤ conjSubgroup s M :=
        conjSubgroup_mono ((le_famSup hA).trans hWM)
      rw [conjSubgroup_eq_self_iff.mpr hsN] at h1
      exact h1 hx
    exact hii x hxM.1 hxM.2 B hB
  have hΔΓ : ∀ B ∈ Δ, B ∈ Γ := by
    intro B hB
    by_contra hnot
    refine stepA h hΓΔ hΓ hmax hB hnot ?_
    intro x hx C hC
    have hxM : x ∈ M := hMS' ▸ (h.le B hB hx)
    exact hii x hxM.1 hxM.2 C hC
  exact hΓ A (hΔΓ A hA) B (hΔΓ B hB) hne

end TightFamily

@[expose] def conjClass (H Q S : Subgroup G) : Set (Subgroup G) :=
  {A | (∃ h ∈ H, A = conjSubgroup h Q) ∧ A ≤ S}

namespace TightData

variable [Finite G] {K H Q S : Subgroup G} (d : TightData K H Q S)
include d

theorem tightFamily (hΦ : ∃ x ∈ Q, x * x ≠ 1) : TightFamily S (conjClass H Q S) := by
  refine ⟨d.two, fun A hA => hA.2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro A ⟨⟨h, hh, rfl⟩, -⟩ hbot
    exact d.ne_bot (conjSubgroup_eq_bot_iff.mp hbot)
  · rintro A ⟨⟨h, hh, rfl⟩, -⟩
    obtain ⟨x, hxQ, hx2⟩ := hΦ
    refine ⟨h * x * h⁻¹, mem_conjSubgroup_of_mem hxQ, fun e => hx2 ?_⟩
    have : h * (x * x) * h⁻¹ = 1 := by rw [← e]; group
    simpa using this
  · rintro A ⟨⟨h, hh, rfl⟩, hAS⟩ s hs
    refine ⟨⟨s * h, H.mul_mem (d.le_H hs) hh, ?_⟩, ?_⟩
    · rw [conjSubgroup_conjSubgroup]
    · rintro y ⟨a, ha, rfl⟩
      exact S.mul_mem (S.mul_mem hs (hAS ha)) (S.inv_mem hs)
  · rintro A ⟨⟨h, hh, rfl⟩, hAS⟩ X hXA hX1 g hgS hg
    exact (d.conj hh hAS).normalizer_inf_le hXA hX1 hgS hg
  · rintro A ⟨⟨h, hh, rfl⟩, hAS⟩ B ⟨⟨k, hk, rfl⟩, hBS⟩ hne hle
    have hg : conjSubgroup (k * h⁻¹) (conjSubgroup h Q) = conjSubgroup k Q := by
      rw [conjSubgroup_conjSubgroup]; congr 1; group
    have := (d.conj hh hAS).commute_of_le_normalizer (g := k * h⁻¹)
      (H.mul_mem hk (H.inv_mem hh)) (by rw [hg]; exact fun e => hne e.symm)
      (by rw [hg]; exact le_inf hBS hle)
    rwa [hg] at this

theorem commute_conj (hΦ : ∃ x ∈ Q, x * x ≠ 1) {h k : G} (hh : h ∈ H) (hk : k ∈ H)
    (hhS : conjSubgroup h Q ≤ S) (hkS : conjSubgroup k Q ≤ S)
    (hne : conjSubgroup h Q ≠ conjSubgroup k Q) :
    conjSubgroup h Q ⊓ conjSubgroup k Q = ⊥ ∧
      ∀ x ∈ conjSubgroup h Q, ∀ y ∈ conjSubgroup k Q, x * y = y * x := by
  refine ⟨?_, (d.tightFamily hΦ).commute_of_ne ⟨⟨h, hh, rfl⟩, hhS⟩ ⟨⟨k, hk, rfl⟩, hkS⟩ hne⟩
  have hg : conjSubgroup (k * h⁻¹) (conjSubgroup h Q) = conjSubgroup k Q := by
    rw [conjSubgroup_conjSubgroup]; congr 1; group
  have := (d.conj hh hhS).inf_conj_eq_bot (g := k * h⁻¹) (H.mul_mem hk (H.inv_mem hh))
    (by rw [hg]; exact hkS) (by rw [hg]; exact fun e => hne e.symm)
  rwa [hg] at this

end TightData

@[expose] def TwoGroupTIInput.{v} : Prop :=
  ∀ {G : Type v} [Group G] [Finite G] (X V A : Subgroup G), IsPGroup 2 X → V ≤ X → A ≤ X →
    (∀ v ∈ V, v * v = 1) → (∀ a ∈ A, a * a = 1) → Nat.card V = Nat.card A → V ⊓ A = ⊥ →
    (∀ x ∈ X, conjSubgroup x V = V ∨ V ⊓ conjSubgroup x V = ⊥) →
    (∀ x ∈ X, conjSubgroup x A = A ∨ A ⊓ conjSubgroup x A = ⊥) →
    (∀ x ∈ X, conjSubgroup x A ≠ V → V ⊓ conjSubgroup x A = ⊥) →
    V ⊓ Subgroup.normalizer (A : Set G) ≠ ⊥ → ∀ v ∈ V, ∀ a ∈ A, v * a = a * v

namespace TightData

variable {K H Q S : Subgroup G} (d : TightData K H Q S)
include d

theorem commute_of_normalizer_ne_bot [Finite G] (h62 : TwoGroupTIInput.{u}) {g : G} (hg : g ∈ H)
    (hne : conjSubgroup g Q ≠ Q) (hgS : conjSubgroup g Q ≤ S)
    (hN : conjSubgroup g Q ⊓ Subgroup.normalizer (Q : Set G) ≠ ⊥) :
    Q ⊓ conjSubgroup g Q = ⊥ ∧ ∀ x ∈ Q, ∀ y ∈ conjSubgroup g Q, x * y = y * x := by
  by_cases hΦ : ∃ x ∈ Q, x * x ≠ 1
  · have h1 := d.commute_conj hΦ (h := 1) (k := g) H.one_mem hg
      (by rw [conjSubgroup_one]; exact d.le_S) hgS
      (by rw [conjSubgroup_one]; exact fun e => hne e.symm)
    rw [conjSubgroup_one] at h1
    exact h1
  · push Not at hΦ
    have d' := d.conj hg hgS
    have hbot := d.inf_conj_eq_bot hg hgS hne
    have hQS : Q ≤ S := d.le_S
    refine ⟨hbot, ?_⟩
    have hXS : conjSubgroup g Q ⊔ Q ≤ S := sup_le hgS hQS
    have hX2 : IsPGroup 2 (conjSubgroup g Q ⊔ Q : Subgroup G) := d.two.to_le hXS
    have hel : ∀ v ∈ conjSubgroup g Q, v * v = 1 := by
      rintro _ ⟨q, hq, rfl⟩
      have : (g * q * g⁻¹) * (g * q * g⁻¹) = g * (q * q) * g⁻¹ := by group
      show (g * q * g⁻¹) * (g * q * g⁻¹) = 1
      rw [this, hΦ q hq]; group
    have hTIV : ∀ x ∈ conjSubgroup g Q ⊔ Q, conjSubgroup x (conjSubgroup g Q) = conjSubgroup g Q ∨
        conjSubgroup g Q ⊓ conjSubgroup x (conjSubgroup g Q) = ⊥ := fun x hx =>
      d'.conj_eq_or_inf_eq_bot (Subgroup.le_normalizer (hXS hx))
    have hTIA : ∀ x ∈ conjSubgroup g Q ⊔ Q, conjSubgroup x Q = Q ∨ Q ⊓ conjSubgroup x Q = ⊥ :=
      fun x hx => d.conj_eq_or_inf_eq_bot (Subgroup.le_normalizer (hXS hx))
    have hcross : ∀ x ∈ conjSubgroup g Q ⊔ Q, conjSubgroup x Q ≠ conjSubgroup g Q →
        conjSubgroup g Q ⊓ conjSubgroup x Q = ⊥ := by
      intro x hx hx'
      have hxS : x ∈ S := hXS hx
      have hmem : conjSubgroup (x * g⁻¹) (conjSubgroup g Q) = conjSubgroup x Q := by
        rw [conjSubgroup_conjSubgroup]; congr 1; group
      have hxQ : conjSubgroup x Q ≤ S := by
        rintro y ⟨a, ha, rfl⟩
        exact S.mul_mem (S.mul_mem hxS (hQS ha)) (S.inv_mem hxS)
      have h1 := d'.inf_conj_eq_bot (g := x * g⁻¹) (H.mul_mem (d.le_H hxS) (H.inv_mem hg))
        (by rw [hmem]; exact hxQ) (by rw [hmem]; exact hx')
      rwa [hmem] at h1
    have hcard : Nat.card (conjSubgroup g Q) = Nat.card Q := card_conjSubgroup g Q
    have hbot' : conjSubgroup g Q ⊓ Q = ⊥ := by rw [inf_comm]; exact hbot
    have key := h62 (conjSubgroup g Q ⊔ Q) (conjSubgroup g Q) Q hX2 le_sup_left le_sup_right hel hΦ
      hcard hbot' hTIV hTIA hcross hN
    exact fun x hx y hy => (key y hy x hx).symm

end TightData

end CFSG.ClassicalInvolution
