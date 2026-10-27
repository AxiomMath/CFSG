module

public import CFSG.ClassicalInvolution.Asc77.AscFusionR10
public import CFSG.ClassicalInvolution.Asc77.AscFusionR6

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    IsPGroup 2 (Subgroup.closure {a, b}) := by
  set C : Subgroup G := Subgroup.closure {a, b} with hC
  have h1 : ∀ x ∈ C, x * a = a * x ∧ x * b = b * x := by
    intro x hx
    have hle : C ≤ Subgroup.centralizer ({a, b} : Set G) := by
      rw [hC, Subgroup.closure_le]
      intro y hy
      show y ∈ Subgroup.centralizer ({a, b} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rcases hy with rfl | rfl <;> rcases hw with rfl | rfl
      · rfl
      · exact hab.symm
      · exact hab
      · rfl
    have := Subgroup.mem_centralizer_iff.mp (hle hx)
    exact ⟨(this a (by simp)).symm, (this b (by simp)).symm⟩
  have h2 : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
    intro x hx y hy
    have hle : C ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [hC, Subgroup.closure_le]
      intro w hw
      show w ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      rcases hw with rfl | rfl
      · exact (h1 v hx).1
      · exact (h1 v hx).2
    exact (Subgroup.mem_centralizer_iff.mp (hle hy) x (by simp))
  have h3 : ∀ x ∈ C, x * x = 1 := by
    intro x hx
    rw [hC] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    | one => simp
    | mul x y hxC hyC hx hy =>
      have hxy : x * y = y * x := h2 x (hC ▸ hxC) y (hC ▸ hyC)
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx, hy]; simp
    | inv x hxC hx =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [hx]; simp
  intro g
  refine ⟨1, ?_⟩
  simpa [pow_two] using Subtype.ext (h3 g.1 g.2)


theorem exists_sylow_normalized {J E : Subgroup G} (hE2 : IsPGroup 2 E)
    (hEN : E ≤ Subgroup.normalizer (J : Set G)) :
    ∃ R : Subgroup G, IsPGroup 2 R ∧ E ≤ R ∧ IsSylow2In (R ⊓ J) J := by
  have hXN : J ⊔ E ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hEN
  obtain ⟨R, hRX, hER⟩ := IsSylow2In.exists_ge hE2 (le_sup_right : E ≤ J ⊔ E)
  exact ⟨R, hRX.2.1, hER, isSylow2In_inf_of_le_normalizer hRX le_sup_left hXN⟩

theorem exists_inverted_involution_member (hp2 : p ≠ 2) {J : Subgroup G} {t : G}
    (hJ : IsClassicalMember p f J t) (hq : 5 ≤ p ^ f) {R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRJ : IsSylow2In (R ⊓ J) J) {w : G} (hwR : w ∈ R) (hw2 : w * w = 1)
    (hwN : w ∈ Subgroup.normalizer (J : Set G))
    (hnt : ¬ ∀ k ∈ J, ⁅w, k⁆ ∈ oddCoreOf J) :
    ∃ κ ∈ R ⊓ J, κ * κ = t ∧ w⁻¹ * κ * w = κ⁻¹ := by
  classical
  have hKz : IsUniqueInvolution J t :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hJ
  set Qs : Subgroup G := R ⊓ J with hQs
  have hQsK : Qs ≤ J := inf_le_right
  have hQs2 : IsPGroup 2 Qs := hR2.to_le inf_le_left
  have hQuat : IsQuatSub Qs := isQuatSub_of_isSylow2In hp2 hJ hRJ
  obtain ⟨k₁, hk₁, ⟨eQ⟩⟩ := id hQuat
  have hQcard : 2 ≤ Nat.card Qs := by
    obtain ⟨k₂, hk₂, hcard⟩ := hQuat.natCard_eq
    rw [hcard]
    calc 2 ≤ 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k₂ + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hzQ : t ∈ Qs := AscL62.mem_of_uniqueInvolution_of_pGroup hKz hQsK hQs2 hQcard
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hconjQ : ∀ x : G, x ∈ Qs → w⁻¹ * x * w ∈ Qs := by
    intro x hx
    refine ⟨R.mul_mem (R.mul_mem (R.inv_mem hwR) hx.1) hwR, ?_⟩
    exact (mem_conj_iff_of_mem_normalizer hwN x).mpr hx.2
  let τ : ↥Qs ≃* ↥Qs :=
    { toFun := fun x => ⟨w⁻¹ * x * w, hconjQ x x.2⟩
      invFun := fun x => ⟨w * x * w⁻¹, by
        have h1 := hconjQ x x.2
        rw [hwi] at h1
        simpa [hwi] using h1⟩
      left_inv := fun x => by
        apply Subtype.ext
        show w * (w⁻¹ * (x : G) * w) * w⁻¹ = x
        group
      right_inv := fun x => by
        apply Subtype.ext
        show w⁻¹ * (w * (x : G) * w⁻¹) * w = x
        group
      map_mul' := fun x y => by
        apply Subtype.ext
        show w⁻¹ * ((x : G) * y) * w = (w⁻¹ * x * w) * (w⁻¹ * y * w)
        group }
  have hτ2 : ∀ x, τ (τ x) = x := by
    intro x
    apply Subtype.ext
    show w⁻¹ * (w⁻¹ * (x : G) * w) * w = x
    rw [hwi]
    calc w * (w * (x : G) * w) * w = (w * w) * x * (w * w) := by group
      _ = x := by rw [hw2]; group
  have hτ1 : ∃ x, τ x ≠ x := by
    by_contra hcon
    push Not at hcon
    have hcen : ∀ r ∈ Qs, ∀ v' ∈ Subgroup.zpowers w, r * v' = v' * r := by
      intro r hr v' hv'
      have hr1 : w⁻¹ * r * w = r := congrArg Subtype.val (hcon ⟨r, hr⟩)
      have hrn : r * w = w * r := by
        calc r * w = w * (w⁻¹ * r * w) := by group
          _ = w * r := by rw [hr1]
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv'
      exact (Commute.zpow_right (show Commute r w from hrn) m).eq
    have hV2 : IsPGroup 2 ↥(Subgroup.zpowers w) :=
      hR2.to_le (Subgroup.zpowers_le.mpr hwR)
    have hVK : ∀ y ∈ Subgroup.zpowers w, conjSub y J = J := by
      intro y hy
      exact conjSub_eq_of_mem_normalizer (Subgroup.zpowers_le.mpr hwN hy)
    have := centSylow_member hp2 hq hJ (R := Qs) (V := Subgroup.zpowers w) hRJ hV2 hVK hcen
    exact hnt (fun k hk => this k hk w (Subgroup.mem_zpowers w))
  have hgen : ∀ H : Subgroup ↥Qs, (∀ x : ↥Qs, orderOf x = 4 → x ∈ H) → H = ⊤ := by
    intro H hH
    have : NeZero (2 ^ k₁) := ⟨by positivity⟩
    exact quaternion_generated_by_order_four eQ H hH
  have hzu : ∀ x : ↥Qs, x * x = 1 → x = 1 ∨ x = ⟨t, hzQ⟩ := by
    intro x hx
    have hxG : (x : G) * (x : G) = 1 := congrArg Subtype.val hx
    rcases hKz.unique (x : G) (hQsK x.2) hxG with h | h
    · left
      exact Subtype.ext h
    · right
      exact Subtype.ext h
  have hz2 : (⟨t, hzQ⟩ : ↥Qs) * ⟨t, hzQ⟩ = 1 := Subtype.ext hKz.sq
  obtain ⟨κ', hκ'4, hκ'⟩ := exists_inverted_order_four ⟨t, hzQ⟩ hz2 (fun x => hQs2 x) hzu hgen τ hτ2
    hτ1
  set κ : G := (κ' : G) with hκ
  have hκK : κ ∈ J := hQsK κ'.2
  have hκ4 : orderOf κ = 4 := by rw [hκ, Subgroup.orderOf_coe]; exact hκ'4
  refine ⟨κ, κ'.2, ?_, ?_⟩
  · have h1 : (κ * κ) * (κ * κ) = 1 := by
      have : κ ^ 4 = 1 := by rw [← hκ4]; exact pow_orderOf_eq_one κ
      calc (κ * κ) * (κ * κ) = κ ^ 4 := by simp [pow_succ, mul_assoc]
        _ = 1 := this
    rcases hKz.unique (κ * κ) (J.mul_mem hκK hκK) h1 with h | h
    · exfalso
      have : orderOf κ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hκ4] at this
      omega
    · exact h
  · have := congrArg Subtype.val hκ'
    simpa [τ, hκ] using this


omit [Finite G] in
theorem orderOf_eq_four_of_sq_eq {a z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) (ha : a * a = z) :
    orderOf a = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : a ^ 2 ^ (1 + 1) = 1 := by
    calc a ^ 2 ^ (1 + 1) = (a * a) * (a * a) := by simp [pow_succ, mul_assoc]
      _ = 1 := by rw [ha, hz2]
  have h2 : ¬ a ^ 2 ^ 1 = 1 := by
    intro h
    apply hz1
    rw [← ha, ← pow_two]
    simpa using h
  have := orderOf_eq_prime_pow h2 h1
  simpa using this

omit [Finite G] in
theorem isPGroup_zpowers_of_sq_eq {a z : G} (hz2 : z * z = 1) (ha : a * a = z) :
    IsPGroup 2 (Subgroup.zpowers a) :=
  isPGroup_zpowers_of_sq_sq (by rw [ha, hz2])

theorem exists_sq_eq_of_isSylow2In (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K V : Subgroup G} {z : G}
    (hK : IsClassicalMember p f K z) (hV : IsSylow2In V K) : ∃ a ∈ V, a * a = z := by
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hK
  have hQuat : IsQuatSub V := isQuatSub_of_isSylow2In hp2 hK hV
  obtain ⟨k₁, hk₁, ⟨eQ⟩⟩ := id hQuat
  have : NeZero (2 ^ k₁) := ⟨by positivity⟩
  set x : ↥V := eQ.symm (QuaternionGroup.xa 0) with hx
  have hx4 : orderOf x = 4 := by
    rw [hx, MulEquiv.orderOf_eq]
    exact QuaternionGroup.orderOf_xa 0
  set a : G := (x : G) with ha
  have ha4 : orderOf a = 4 := by rw [ha, Subgroup.orderOf_coe]; exact hx4
  have haK : a ∈ K := hV.1 x.2
  have h1 : (a * a) * (a * a) = 1 := by
    have : a ^ 4 = 1 := by rw [← ha4]; exact pow_orderOf_eq_one a
    calc (a * a) * (a * a) = a ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := this
  refine ⟨a, x.2, ?_⟩
  rcases hKz.unique (a * a) (K.mul_mem haK haK) h1 with h | h
  · exfalso
    have : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [ha4] at this
    omega
  · exact h


theorem exists_conj_of_twin_pairs (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K₀ : Subgroup G} {z₀ : G}
    (h₀ : IsClassicalMember p f K₀ z₀) {K K' : Subgroup G} {z : G}
    (hK : K ∈ CoreAssembly.conjClass K₀) (hK' : K' ∈ CoreAssembly.conjClass K₀)
    (hKz : IsUniqueInvolution K z) (hK'z : IsUniqueInvolution K' z) (hne : K ≠ K')
    {a κ b κ' : G} (ha : a ∈ K) (hκ : κ ∈ K) (hb : b ∈ K') (hκ' : κ' ∈ K')
    (ha2 : a * a = z) (hb2 : b * b = z) (hab : a * b = b * a)
    (hκ2 : κ * κ = z) (hκ'2 : κ' * κ' = z) (hκκ' : κ * κ' = κ' * κ)
    :
    ∃ c ∈ K ⊔ K', c * (a * b) * c⁻¹ = κ * κ' := by
  classical
  have hKm : IsClassicalMember p f K z := isClassicalMember_of_mem_conjClass hp2 hq h₀ hK hKz
  have hK'm : IsClassicalMember p f K' z := isClassicalMember_of_mem_conjClass hp2 hq h₀ hK' hK'z
  obtain ⟨g, hgK, hg⟩ := exists_conj_in_member hp2 hq hKm hκ ha hκ2 ha2
  obtain ⟨g', hg'K', hg'⟩ := exists_conj_in_member hp2 hq hK'm hκ' hb hκ'2 hb2
  obtain ⟨hK'N, hKN', hcomm⟩ := twin_facts_general hq hp2 h₀ hK hK' hKz hK'z hne
  set M : Subgroup G := K ⊔ K' with hM
  have hKM : K ≤ M := le_sup_left
  have hK'M : K' ≤ M := le_sup_right
  set N : Subgroup G := oddCoreOf M with hN
  have hMN : ∀ m ∈ M, m ∈ Subgroup.normalizer (N : Set G) := fun m hm =>
    mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hm)
  have hOK : oddCoreOf K ≤ N := by
    refine le_oddCoreOf_of_normal_odd ((oddCoreOf_le_self K).trans hKM) ?_ (oddCoreOf_odd_natCard K)
    refine sup_le ?_ ?_
    · exact fun m hm => mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hm)
    · exact fun m hm => mem_normalizer_oddCoreOf_of_mem_normalizer' (hK'N hm)
  have hcN : ∀ u ∈ K, ∀ w ∈ K', ⁅u, w⁆ ∈ N := fun u hu w hw =>
    hOK (hcomm (Subgroup.commutator_mem_commutator hu hw)).1
  have hcN' : ∀ w ∈ K', ∀ u ∈ K, ⁅w, u⁆ ∈ N := fun w hw u hu => by
    rw [← commutatorElement_inv]
    exact N.inv_mem (hcN u hu w hw)
  set x : G := g * g' with hx
  set y : G := x * (κ * κ') * x⁻¹ with hy
  set c₁ : G := g' * κ * g'⁻¹ * κ⁻¹ with hc₁
  set c₂ : G := g * b * g⁻¹ * b⁻¹ with hc₂
  have hc₁N : c₁ ∈ N := by
    have : c₁ = ⁅g', κ⁆ := by rw [hc₁, commutatorElement_def]
    rw [this]
    exact hcN' g' hg'K' κ hκ
  have hc₂N : c₂ ∈ N := by
    have : c₂ = ⁅g, b⁆ := by rw [hc₂, commutatorElement_def]
    rw [this]
    exact hcN g hgK b hb
  have hgM : g ∈ M := hKM hgK
  have haM : a ∈ M := hKM ha
  have hbM : b ∈ M := hK'M hb
  have hy' : y = (g * c₁ * g⁻¹) * a * c₂ * b := by
    have e1 : g' * κ' * g'⁻¹ = b := hg'
    have e2 : g * κ * g⁻¹ = a := hg
    calc y = g * (g' * κ * g'⁻¹) * (g' * κ' * g'⁻¹) * g⁻¹ := by rw [hy, hx]; group
      _ = g * (c₁ * κ) * b * g⁻¹ := by
        rw [e1]
        congr 3
        rw [hc₁]
        group
      _ = (g * c₁ * g⁻¹) * (g * κ * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * c₁ * g⁻¹) * a * c₂ * b := by
        rw [e2]
        have : g * b * g⁻¹ = c₂ * b := by rw [hc₂]; group
        rw [this]
        group
  have hn1 : g * c₁ * g⁻¹ ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hMN g hgM) c₁).mp hc₁N
    exact this
  have hn2 : a⁻¹ * (g * c₁ * g⁻¹) * a ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hMN a⁻¹ (M.inv_mem haM)) (g * c₁ * g⁻¹)).mp hn1
    simpa using this
  have hn3 : b⁻¹ * ((a⁻¹ * (g * c₁ * g⁻¹) * a) * c₂) * b ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hMN b⁻¹ (M.inv_mem hbM)) _).mp
      (N.mul_mem hn2 hc₂N)
    simpa using this
  have hxy : (a * b)⁻¹ * y ∈ N := by
    have : (a * b)⁻¹ * y = b⁻¹ * ((a⁻¹ * (g * c₁ * g⁻¹) * a) * c₂) * b := by
      rw [hy']
      group
    rw [this]
    exact hn3
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2]; exact hKz.sq
  have hδ2 : (κ * κ') * (κ * κ') = 1 := by
    calc (κ * κ') * (κ * κ') = κ * (κ' * κ) * κ' := by group
      _ = κ * (κ * κ') * κ' := by rw [← hκκ']
      _ = (κ * κ) * (κ' * κ') := by group
      _ = 1 := by rw [hκ2, hκ'2]; exact hKz.sq
  have hy2 : y * y = 1 := by
    calc y * y = x * ((κ * κ') * (κ * κ')) * x⁻¹ := by rw [hy]; group
      _ = 1 := by rw [hδ2]; group
  have hxt : IsPGroup 2 (Subgroup.zpowers (a * b)) :=
    isPGroup_zpowers_of_sq_sq (by rw [hab2]; group)
  have hyt : IsPGroup 2 (Subgroup.zpowers y) :=
    isPGroup_zpowers_of_sq_sq (by rw [hy2]; group)
  obtain ⟨h, hhM, hh⟩ := exists_conj_of_odd_coset (oddCoreOf_odd_natCard M) hxt hyt
    (hMN (a * b) (M.mul_mem haM hbM)) hxy
  have hhM' : h ∈ M :=
    (sup_le (oddCoreOf_le_self M) (Subgroup.zpowers_le.mpr (M.mul_mem haM hbM))) hhM
  have hxM : x⁻¹ ∈ M := M.inv_mem (M.mul_mem hgM (hK'M hg'K'))
  refine ⟨x⁻¹ * h, M.mul_mem hxM hhM', ?_⟩
  calc (x⁻¹ * h) * (a * b) * (x⁻¹ * h)⁻¹ = x⁻¹ * (h * (a * b) * h⁻¹) * x := by group
    _ = x⁻¹ * y * x := by rw [hh]
    _ = κ * κ' := by rw [hy]; group



end CFSG.ClassicalInvolution.Asc77.AscFusion
