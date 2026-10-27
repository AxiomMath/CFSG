module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedQuaternion
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
public import CFSG.ClassicalInvolution.Balance.BootstrapTriple
public import CFSG.ClassicalInvolution.Balance.PassTwoConj

public section

namespace CFSG.ClassicalInvolution.Generic.TypeCSetup

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem quaternion_aux (N m : ℕ) [NeZero N] (hN : N = 2 * m) :
    ((QuaternionGroup.xa 0 : QuaternionGroup N) * QuaternionGroup.xa 0 =
        QuaternionGroup.a (N : ZMod (2 * N))) ∧
      (QuaternionGroup.a (m : ZMod (2 * N)) * QuaternionGroup.xa 0 =
        QuaternionGroup.xa 0 * QuaternionGroup.a (N : ZMod (2 * N)) *
          QuaternionGroup.a (m : ZMod (2 * N))) := by
  subst hN
  refine ⟨?_, ?_⟩
  · rw [QuaternionGroup.xa_mul_xa]
    simp
  · rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_a]
    congr 1
    have h2 : ((2 * m : ℕ) : ZMod (2 * (2 * m))) + ((2 * m : ℕ) : ZMod (2 * (2 * m))) = 0 := by
      have : ((2 * m + 2 * m : ℕ) : ZMod (2 * (2 * m))) = 0 := by
        have h : 2 * m + 2 * m = 2 * (2 * m) := by ring
        rw [h]
        exact ZMod.natCast_self _
      simpa using this
    have h3 : ((2 * m : ℕ) : ZMod (2 * (2 * m))) =
        (m : ZMod (2 * (2 * m))) + (m : ZMod (2 * (2 * m))) := by
      push_cast
      ring
    rw [zero_sub, zero_add]
    have h4 : ((2 * m : ℕ) : ZMod (2 * (2 * m))) + (m : ZMod (2 * (2 * m))) +
        (m : ZMod (2 * (2 * m))) = 0 := by
      rw [add_assoc, ← h3]
      exact h2
    linear_combination (-1 : ZMod (2 * (2 * m))) * h4

theorem exists_sq_eq_involution [Finite G] {K : Subgroup G} {z : G} (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hz : IsClassicalMember p f K z) :
    ∃ t w : G, t ∈ K ∧ w ∈ K ∧ t * t = z ∧ w * t = t * z * w := by
  classical
  set z' : ↥K := ⟨z, hz.mem⟩ with hz'
  have hz'2 : orderOf z' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz.orderOf_eq_two
  have hP : IsPGroup 2 (Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'2]; simp)
  obtain ⟨T, hT⟩ := hP.exists_le_sylow
  have hzT : z' ∈ (T : Subgroup ↥K) := hT (Subgroup.mem_zpowers z')
  obtain ⟨r, hr, ⟨e⟩⟩ :=
    CFSG.ClassicalInvolution.Disconnected.quaternion_sylow_of_isClassicalMember hp2 hq hz T
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℕ, 0 < m ∧ 2 ^ (r - 2) = 2 * m := by
    refine ⟨2 ^ (r - 3), pow_pos (by norm_num) _, ?_⟩
    have : r - 2 = (r - 3) + 1 := by omega
    rw [this, pow_succ]
    ring
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  obtain ⟨hsq, hcomm⟩ := quaternion_aux (2 ^ (r - 2)) m hm
  set zT : ↥(T : Subgroup ↥K) := ⟨z', hzT⟩ with hzT'
  have hzT2 : orderOf zT = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz'2
  have hez : e zT = QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) :=
    CFSG.ClassicalInvolution.QuaternionStructure.quaternionGroup_eq_a_of_orderOf_eq_two
      ((e.orderOf_eq zT).trans hzT2)
  have h1 : e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.xa 0) = zT := by
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, hsq, hez]
  have h2 : e.symm (QuaternionGroup.a (m : ZMod (2 * 2 ^ (r - 2)))) *
      e.symm (QuaternionGroup.xa 0) = e.symm (QuaternionGroup.xa 0) * zT *
        e.symm (QuaternionGroup.a (m : ZMod (2 * 2 ^ (r - 2)))) := by
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply, hez]
    exact hcomm
  refine ⟨(((e.symm (QuaternionGroup.xa 0) : ↥(T : Subgroup ↥K)) : ↥K) : G),
    (((e.symm (QuaternionGroup.a (m : ZMod (2 * 2 ^ (r - 2)))) : ↥(T : Subgroup ↥K)) : ↥K) : G),
    ((e.symm (QuaternionGroup.xa 0) : ↥(T : Subgroup ↥K)) : ↥K).2,
    ((e.symm (QuaternionGroup.a (m : ZMod (2 * 2 ^ (r - 2)))) : ↥(T : Subgroup ↥K)) : ↥K).2,
    ?_, ?_⟩
  · have := congrArg (fun x : ↥(T : Subgroup ↥K) => ((x : ↥K) : G)) h1
    simpa [zT, z'] using this
  · have := congrArg (fun x : ↥(T : Subgroup ↥K) => ((x : ↥K) : G)) h2
    simpa [zT, z', mul_assoc] using this

section Edge

variable [Finite G]

theorem exists_edge_distinct_involutions [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hf : 0 < f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hΔ : CFSG.ClassicalInvolution.DeltaConnected K) :
    ∃ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), K₁ ∈ conjClass K ∧ K₂ ∈ conjClass K ∧
      IsClassicalMember p f K₁ z₁ ∧ IsClassicalMember p f K₂ z₂ ∧ Commutes K₁ K₂ ∧ z₁ ≠ z₂ := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ B : Subgroup G, B ∈ CFSG.ClassicalInvolution.conjugateSet K →
      ∃ g : G, B = conjSub g K := fun B hB => by
    rw [conjugateSet_eq_range] at hB
    obtain ⟨g, rfl⟩ := hB
    exact ⟨g, rfl⟩
  have key : ∀ B : Subgroup G,
      Relation.ReflTransGen (CFSG.ClassicalInvolution.commutingAdj K) K B →
        ∀ w : G, IsClassicalMember p f B w → w = z := by
    intro B hB
    induction hB with
    | refl => exact fun w hw => hz.eq_of_isCentralInvolution hp2 hf hw.isCentralInvolution
    | @tail b c _ hadj ih =>
      intro w hw
      obtain ⟨hbmem, hcmem, hbc, hcomm⟩ := hadj
      obtain ⟨g₁, hg₁⟩ := hmem b hbmem
      obtain ⟨g₂, hg₂⟩ := hmem c hcmem
      have hb : IsClassicalMember p f b (g₁ * z * g₁⁻¹) := hg₁ ▸ hz.conj g₁
      have hc : IsClassicalMember p f c (g₂ * z * g₂⁻¹) := hg₂ ▸ hz.conj g₂
      have h1 : g₁ * z * g₁⁻¹ = z := ih _ hb
      have h2 : g₂ * z * g₂⁻¹ = g₁ * z * g₁⁻¹ :=
        (hcon b c _ _ (by rw [← conjugateSet_eq_range]; exact hbmem)
          (by rw [← conjugateSet_eq_range]; exact hcmem) hb hc hcomm).symm
      have h3 : w = g₂ * z * g₂⁻¹ := hc.eq_of_isCentralInvolution hp2 hf hw.isCentralInvolution
      rw [h3, h2, h1]
  have hKmem : K ∈ CFSG.ClassicalInvolution.conjugateSet K := by
    rw [conjugateSet_eq_range]; exact mem_conjClass_self K
  have hcentral : ∀ g : G, g * z * g⁻¹ = z := fun g => by
    have hg : conjSub g K ∈ CFSG.ClassicalInvolution.conjugateSet K := by
      rw [conjugateSet_eq_range]; exact ⟨g, rfl⟩
    exact key _ (hΔ K hKmem _ hg) _ (hz.conj g)
  apply singleton_not_subset_center hnab hz.ne_one
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  have := hcentral g
  calc g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [this]

theorem commutes_of_not_a2Configuration (hp2 : p ≠ 2) (hf : 0 < f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hA2 : ¬ A2Configuration z K) {K₁ K₂ : Subgroup G}
    {z₁ z₂ : G} (h₁ : K₁ ∈ conjClass K) (h₂ : K₂ ∈ conjClass K)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hz₂ : IsClassicalMember p f K₂ z₂) (hne : z₁ ≠ z₂)
    (hc : z₁ * z₂ = z₂ * z₁) : Commutes K₁ K₂ := by
  by_contra hnc
  obtain ⟨g₁, rfl⟩ := h₁
  obtain ⟨g₂, rfl⟩ := h₂
  change IsClassicalMember p f (conjSub g₁ K) z₁ at hz₁
  change IsClassicalMember p f (conjSub g₂ K) z₂ at hz₂
  change ¬ Commutes (conjSub g₁ K) (conjSub g₂ K) at hnc
  have e₁ : z₁ = g₁ * z * g₁⁻¹ :=
    (hz.conj g₁).eq_of_isCentralInvolution hp2 hf hz₁.isCentralInvolution
  have e₂ : z₂ = g₂ * z * g₂⁻¹ :=
    (hz.conj g₂).eq_of_isCentralInvolution hp2 hf hz₂.isCentralInvolution
  apply hA2
  refine ⟨g₁⁻¹, g₂⁻¹, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : conjSub g₁ K = conjSub g₂ K := by simpa [conjSub] using h
    rw [← h'] at hz₂
    exact hne ((hz₁.eq_of_isCentralInvolution hp2 hf hz₂.isCentralInvolution).symm)
  · simpa [e₁, e₂] using hne
  · simpa [e₁, e₂, inv_inv] using hc
  · simpa [conjSub] using hnc

end Edge

section Triple

theorem exactTriple_zpowers {z₁ z₂ z₃ : G} (h₁ : z₁ * z₁ = 1) (h₂ : z₂ * z₂ = 1)
    (h₃ : z₃ * z₃ = 1) (n₁ : z₁ ≠ 1) (n₂ : z₂ ≠ 1) (n₃ : z₃ ≠ 1) (c₁₂ : z₁ * z₂ = z₂ * z₁)
    (c₁₃ : z₁ * z₃ = z₃ * z₁) (c₂₃ : z₂ * z₃ = z₃ * z₂) (d₁₂ : z₁ ≠ z₂) (d₁₃ : z₁ ≠ z₃)
    (d₂₃ : z₂ ≠ z₃) :
    CFSG.ClassicalInvolution.Balance.Bootstrap.ExactTriple (Subgroup.zpowers z₁)
      (Subgroup.zpowers z₂) (Subgroup.zpowers z₃) z₁ z₂ z₃ := by
  have hcomm : ∀ {a b : G}, a * b = b * a → ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b,
      x * y = y * x := by
    intro a b hab x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_zpow (show Commute a b from hab) m n)).eq
  have hcent : ∀ {a : G}, ∀ k ∈ Subgroup.zpowers a, k * a = a * k := by
    intro a k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact ((Commute.refl a).zpow_left m).eq
  exact ⟨Subgroup.mem_zpowers z₁, Subgroup.mem_zpowers z₂, Subgroup.mem_zpowers z₃, hcent, hcent,
    hcent, h₁, h₂, h₃, n₁, n₂, n₃, hcomm c₁₂, hcomm c₁₃, hcomm c₂₃, d₁₂, d₁₃, d₂₃⟩

theorem mem_closure_pair {x y g : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hg : g ∈ Subgroup.closure ({x, y} : Set G)) : g = 1 ∨ g = x ∨ g = y ∨ g = x * y := by
  have c : y * x = x * y := hxy.symm
  have s1' : ∀ b, x * (x * b) = b := fun b => by rw [← mul_assoc, hx, one_mul]
  have c' : ∀ b, y * (x * b) = x * (y * b) := fun b => by rw [← mul_assoc, c, mul_assoc]
  have i1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have i2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  refine Subgroup.closure_induction
    (p := fun g _ => g = 1 ∨ g = x ∨ g = y ∨ g = x * y) ?_ ?_ ?_ ?_ hg
  · intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hu | hu <;> subst hu <;> simp
  · simp
  · rintro a b - - (ha | ha | ha | ha) (hb | hb | hb | hb) <;> subst ha <;> subst hb <;>
      simp [mul_assoc, hx, hy, s1', c, c']
  · rintro a - (ha | ha | ha | ha) <;> subst ha <;> simp [i1, i2, c]

theorem exactTriple_of_classical {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (c₁ : IsClassicalMember p f K₁ z₁) (c₂ : IsClassicalMember p f K₂ z₂)
    (c₃ : IsClassicalMember p f K₃ z₃) (m₁₂ : Commutes K₁ K₂) (m₁₃ : Commutes K₁ K₃)
    (m₂₃ : Commutes K₂ K₃) (d₁₂ : z₁ ≠ z₂) (d₁₃ : z₁ ≠ z₃) (d₂₃ : z₂ ≠ z₃) :
    CFSG.ClassicalInvolution.Balance.Bootstrap.ExactTriple K₁ K₂ K₃ z₁ z₂ z₃ := by
  have cen : ∀ {K : Subgroup G} {z : G}, IsClassicalMember p f K z → ∀ k ∈ K, k * z = z * k :=
    fun hz k hk => Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.RouteD.le_centralizer_of_isClassicalMember hz hk)
  exact ⟨c₁.mem, c₂.mem, c₃.mem, cen c₁, cen c₂, cen c₃, c₁.isCentralInvolution.sq,
    c₂.isCentralInvolution.sq, c₃.isCentralInvolution.sq, c₁.ne_one, c₂.ne_one, c₃.ne_one,
    m₁₂, m₁₃, m₂₃, d₁₂, d₁₃, d₂₃⟩

structure DepTriple (p f : ℕ) [Fact p.Prime] (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G) : Prop where
  cls₁ : IsClassicalMember p f K₁ z₁
  cls₂ : IsClassicalMember p f K₂ z₂
  cls₃ : IsClassicalMember p f K₃ z₃
  comm₁₂ : Commutes K₁ K₂
  comm₁₃ : Commutes K₁ K₃
  comm₂₃ : Commutes K₂ K₃
  ne : z₁ ≠ z₂
  prod : z₁ * z₂ = z₃

variable {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}

namespace DepTriple

theorem sq₁ (T : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃) : z₁ * z₁ = 1 := T.cls₁.isCentralInvolution.sq

theorem sq₂ (T : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃) : z₂ * z₂ = 1 := T.cls₂.isCentralInvolution.sq

theorem sq₃ (T : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃) : z₃ * z₃ = 1 := T.cls₃.isCentralInvolution.sq

theorem comm_z₁₂ (T : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃) : z₁ * z₂ = z₂ * z₁ :=
  T.comm₁₂ z₁ T.cls₁.mem z₂ T.cls₂.mem

theorem exactTriple (T : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃) :
    CFSG.ClassicalInvolution.Balance.Bootstrap.ExactTriple K₁ K₂ K₃ z₁ z₂ z₃ := by
  refine exactTriple_of_classical T.cls₁ T.cls₂ T.cls₃ T.comm₁₂ T.comm₁₃ T.comm₂₃ T.ne ?_ ?_
  · intro h
    apply T.cls₂.ne_one
    have : z₁ * z₂ = z₁ * 1 := by rw [T.prod, ← h, mul_one]
    exact mul_left_cancel this
  · intro h
    apply T.cls₁.ne_one
    have : z₁ * z₂ = 1 * z₂ := by rw [T.prod, ← h, one_mul]
    exact mul_right_cancel this

end DepTriple

@[expose] def axis (z₁ z₂ t₁ t₂ t₃ : G) : Subgroup G :=
  Subgroup.closure ({z₁, z₂, t₁ * t₂ * t₃} : Set G)

theorem DepTriple.axis_eight [Finite G] (T : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃) {t₁ t₂ t₃ w : G}
    (ht₁ : t₁ ∈ K₁) (ht₂ : t₂ ∈ K₂) (ht₃ : t₃ ∈ K₃) (e₁ : t₁ * t₁ = z₁) (e₂ : t₂ * t₂ = z₂)
    (e₃ : t₃ * t₃ = z₃) (hw : w ∈ K₁) (hwt : w * t₁ = t₁ * z₁ * w) :
    (t₁ * t₂ * t₃) * (t₁ * t₂ * t₃) = 1 ∧ z₁ * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * z₁ ∧
      z₂ * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * z₂ ∧
      w * (t₁ * t₂ * t₃) = z₁ * (t₁ * t₂ * t₃) * w ∧
      t₁ * t₂ * t₃ ∉ Subgroup.closure ({z₁, z₂} : Set G) ∧
      IsElemAbelian 2 (axis z₁ z₂ t₁ t₂ t₃) ∧ Nat.card (axis z₁ z₂ t₁ t₂ t₃) = 8 := by
  have cen : ∀ {K : Subgroup G} {z : G}, IsClassicalMember p f K z → ∀ k ∈ K, k * z = z * k :=
    fun hz k hk => Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.RouteD.le_centralizer_of_isClassicalMember hz hk)
  have hz₁K := T.cls₁.mem
  have hz₂K := T.cls₂.mem
  have c12 : Commute t₁ t₂ := T.comm₁₂ t₁ ht₁ t₂ ht₂
  have c13 : Commute t₁ t₃ := T.comm₁₃ t₁ ht₁ t₃ ht₃
  have c23 : Commute t₂ t₃ := T.comm₂₃ t₂ ht₂ t₃ ht₃
  have cz11 : Commute z₁ t₁ := (cen T.cls₁ t₁ ht₁).symm
  have cz12 : Commute z₁ t₂ := T.comm₁₂ z₁ hz₁K t₂ ht₂
  have cz13 : Commute z₁ t₃ := T.comm₁₃ z₁ hz₁K t₃ ht₃
  have cz21 : Commute z₂ t₁ := (T.comm₁₂ t₁ ht₁ z₂ hz₂K).symm
  have cz22 : Commute z₂ t₂ := (cen T.cls₂ t₂ ht₂).symm
  have cz23 : Commute z₂ t₃ := T.comm₂₃ z₂ hz₂K t₃ ht₃
  have hw2 : Commute w t₂ := T.comm₁₂ w hw t₂ ht₂
  have hw3 : Commute w t₃ := T.comm₁₃ w hw t₃ ht₃
  have hwz1 : Commute w z₁ := cen T.cls₁ w hw
  have hwz2 : Commute w z₂ := T.comm₁₂ w hw z₂ hz₂K
  have hss : (t₁ * t₂ * t₃) * (t₁ * t₂ * t₃) = 1 := by
    have h1 : (t₁ * t₂ * t₃) ^ 2 = (t₁ * t₁) * (t₂ * t₂) * (t₃ * t₃) := by
      rw [(c13.mul_left c23).mul_pow, c12.mul_pow, sq, sq, sq]
    rw [← sq, h1, e₁, e₂, e₃, ← T.prod]
    calc z₁ * z₂ * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
      _ = z₁ * (z₁ * z₂) * z₂ := by rw [← T.comm_z₁₂]
      _ = (z₁ * z₁) * (z₂ * z₂) := by group
      _ = 1 := by rw [T.sq₁, T.sq₂, one_mul]
  have hcz₁ : z₁ * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * z₁ :=
    ((cz11.mul_right cz12).mul_right cz13).eq
  have hcz₂ : z₂ * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * z₂ :=
    ((cz21.mul_right cz22).mul_right cz23).eq
  have hws : w * (t₁ * t₂ * t₃) = z₁ * (t₁ * t₂ * t₃) * w := by
    calc w * (t₁ * t₂ * t₃) = (w * t₁) * t₂ * t₃ := by group
      _ = (t₁ * z₁ * w) * t₂ * t₃ := by rw [hwt]
      _ = t₁ * z₁ * (w * t₂) * t₃ := by group
      _ = t₁ * z₁ * (t₂ * w) * t₃ := by rw [hw2.eq]
      _ = t₁ * z₁ * t₂ * (w * t₃) := by group
      _ = t₁ * z₁ * t₂ * (t₃ * w) := by rw [hw3.eq]
      _ = z₁ * t₁ * t₂ * t₃ * w := by rw [← cz11.eq]; group
      _ = z₁ * (t₁ * t₂ * t₃) * w := by group
  have hnot : t₁ * t₂ * t₃ ∉ Subgroup.closure ({z₁, z₂} : Set G) := by
    intro hs
    have hwB : ∀ x ∈ Subgroup.closure ({z₁, z₂} : Set G), w * x = x * w := by
      intro x hx
      rcases mem_closure_pair T.sq₁ T.sq₂ T.comm_z₁₂ hx with rfl | rfl | rfl | rfl
      · simp
      · exact hwz1.eq
      · exact hwz2.eq
      · exact (hwz1.mul_right hwz2).eq
    have h1 := hwB _ hs
    have h2 : z₁ * (t₁ * t₂ * t₃) * w = (t₁ * t₂ * t₃) * w := by rw [← hws, h1]
    have h3 : z₁ * (t₁ * t₂ * t₃) = t₁ * t₂ * t₃ := mul_right_cancel h2
    exact T.cls₁.ne_one (mul_eq_right.mp h3)
  have hz₁B : z₁ ∈ Subgroup.closure ({z₁, z₂} : Set G) := Subgroup.subset_closure (by simp)
  have hz₂B : z₂ ∈ Subgroup.closure ({z₁, z₂} : Set G) := Subgroup.subset_closure (by simp)
  have hs1 : t₁ * t₂ * t₃ ≠ 1 := fun h => hnot (h ▸ one_mem _)
  have hsz₁ : z₁ ≠ t₁ * t₂ * t₃ := fun h => hnot (h ▸ hz₁B)
  have hsz₂ : z₂ ≠ t₁ * t₂ * t₃ := fun h => hnot (h ▸ hz₂B)
  have hind : z₁ * z₂ ≠ t₁ * t₂ * t₃ := fun h => hnot (h ▸ mul_mem hz₁B hz₂B)
  have T' := exactTriple_zpowers T.sq₁ T.sq₂ hss T.cls₁.ne_one T.cls₂.ne_one hs1 T.comm_z₁₂ hcz₁
    hcz₂ T.ne hsz₁ hsz₂
  exact ⟨hss, hcz₁, hcz₂, hws, hnot, T'.isElemAbelian, T'.card_eq_eight hind⟩

theorem depTriple_of_not_bootData [Finite G] {Ω : Set (Subgroup G)} (hBD : ¬ BootData p f Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (h₁ : K₁ ∈ Ω) (c₁ : IsClassicalMember p f K₁ z₁)
    (c₂ : IsClassicalMember p f K₂ z₂) (c₃ : IsClassicalMember p f K₃ z₃)
    (m₁₂ : Commutes K₁ K₂) (m₁₃ : Commutes K₁ K₃) (m₂₃ : Commutes K₂ K₃) (d₁₂ : z₁ ≠ z₂)
    (d₁₃ : z₁ ≠ z₃) (d₂₃ : z₂ ≠ z₃) : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃ := by
  have T := exactTriple_of_classical c₁ c₂ c₃ m₁₂ m₁₃ m₂₃ d₁₂ d₁₃ d₂₃
  refine ⟨c₁, c₂, c₃, m₁₂, m₁₃, m₂₃, d₁₂, ?_⟩
  by_contra hne
  exact hBD ⟨K₁, z₁, T.group, h₁, c₁, T.isElemAbelian, T.card_eq_eight hne,
    Subgroup.subset_closure (by simp), T.le_centralizer₁⟩

theorem DepTriple.exists_axis [Finite G] (T : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) :
    ∃ t₁ t₂ t₃ w : G, t₁ ∈ K₁ ∧ t₂ ∈ K₂ ∧ t₃ ∈ K₃ ∧ w ∈ K₁ ∧ t₁ * t₁ = z₁ ∧ t₂ * t₂ = z₂ ∧
      t₃ * t₃ = z₃ ∧ w * t₁ = t₁ * z₁ * w ∧ IsElemAbelian 2 (axis z₁ z₂ t₁ t₂ t₃) ∧
        Nat.card (axis z₁ z₂ t₁ t₂ t₃) = 8 := by
  obtain ⟨t₁, w, ht₁, hw, e₁, hwt⟩ := exists_sq_eq_involution hp2 hq T.cls₁
  obtain ⟨t₂, -, ht₂, -, e₂, -⟩ := exists_sq_eq_involution hp2 hq T.cls₂
  obtain ⟨t₃, -, ht₃, -, e₃, -⟩ := exists_sq_eq_involution hp2 hq T.cls₃
  obtain ⟨-, -, -, -, -, hA, hcard⟩ := T.axis_eight ht₁ ht₂ ht₃ e₁ e₂ e₃ hw hwt
  exact ⟨t₁, t₂, t₃, w, ht₁, ht₂, ht₃, hw, e₁, e₂, e₃, hwt, hA, hcard⟩

theorem axis_ge_pair (z₁ z₂ t₁ t₂ t₃ : G) :
    Subgroup.closure ({z₁, z₂} : Set G) ≤ axis z₁ z₂ t₁ t₂ t₃ :=
  Subgroup.closure_mono (by intro x hx; simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx ⊢; tauto)

end Triple

end CFSG.ClassicalInvolution.Generic.TypeCSetup
