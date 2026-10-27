module

public import CFSG.GH74.Generic.S1.RA4Facts
public import CFSG.GH74.Generic.S1.SymNbhd
public import CFSG.GH74.Generic.S1.RLevelECore
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.Generic

theorem exists_conj_of_proj_eq {G : Type} [Group G] [Finite G] {x : G}
    {u v : ↥(centralizer ({x} : Set G))} (hu : u * u = 1) (hv : v * v = 1)
    (h : proj x u = proj x v) :
    ∃ r ∈ pPrimeCore 2 ↥(centralizer ({x} : Set G)), r * u * r⁻¹ = v := by
  set a : ↥(centralizer ({x} : Set G)) := u⁻¹ * v with ha
  have hπa : proj x a = 1 := by rw [ha, map_mul, map_inv, h, inv_mul_cancel]
  have hmem : a ∈ pPrimeCore 2 ↥(centralizer ({x} : Set G)) := (QuotientGroup.eq_one_iff _).1 hπa
  have hodd : Odd (orderOf a) := proj_odd x a hπa
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have ha' : a = u * v := by rw [ha, huinv]
  have hua : u * a * u = a⁻¹ := by
    have h1 : u * a * u = v * u := by
      rw [ha', ← mul_assoc, hu, one_mul]
    rw [h1, ha', mul_inv_rev, hvinv, huinv]
  obtain ⟨k, hk⟩ := hodd
  set b : ↥(centralizer ({x} : Set G)) := a ^ (k + 1) with hb
  have hbb : b * b = a := by
    rw [hb, ← pow_add, show k + 1 + (k + 1) = orderOf a + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hub : u * b * u = b⁻¹ := by
    have h1 : ∀ n : ℕ, u * a ^ n * u = (a ^ n)⁻¹ := by
      intro n
      have h0 : (MulAut.conj u : MulAut ↥(centralizer ({x} : Set G))) a = a⁻¹ := by
        rw [MulAut.conj_apply, huinv]; exact hua
      have h2 : (MulAut.conj u : MulAut ↥(centralizer ({x} : Set G))) (a ^ n) = (a ^ n)⁻¹ := by
        rw [map_pow, h0, inv_pow]
      rw [MulAut.conj_apply, huinv] at h2
      exact h2
    rw [hb]
    exact h1 _
  refine ⟨b⁻¹, ?_, ?_⟩
  · exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hmem _)
  · rw [inv_inv]
    calc b⁻¹ * u * b = (u * b * u) * u * b := by rw [hub]
      _ = u * (b * b) := by simp only [mul_assoc]; rw [← mul_assoc u u, hu, one_mul]
      _ = v := by rw [hbb, ha', ← mul_assoc, hu, one_mul]

theorem mem_closure_pair_of_comm {G : Type} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hc : x * y = y * x) {z : G} (hz : z ∈ Subgroup.closure ({x, y} : Set G)) :
    z = 1 ∨ z = x ∨ z = y ∨ z = x * y := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hyx : y * x = x * y := hc.symm
  have t1 : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have t2 : (x * y) * x = y := by rw [mul_assoc, hyx, ← mul_assoc, hx, one_mul]
  have t3 : y * (x * y) = x := by rw [← hyx, ← mul_assoc, hy, one_mul]
  have t4 : (x * y) * y = x := by rw [mul_assoc, hy, mul_one]
  have t5 : (x * y) * (x * y) = 1 := by
    rw [mul_assoc, ← mul_assoc y, hyx, mul_assoc, ← mul_assoc x, hx, one_mul, hy]
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | hz
    · exact Or.inr (Or.inl rfl)
    · rw [Set.mem_singleton_iff] at hz
      exact Or.inr (Or.inr (Or.inl hz))
  | one => exact Or.inl rfl
  | mul a b _ _ ha hb =>
    rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
      simp only [one_mul, mul_one, hx, hy, hyx, t1, t2, t3, t4, t5, true_or, or_true]
  | inv a _ ha =>
    rcases ha with ha | ha | ha | ha <;> rw [ha]
    · left; simp
    · right; left; exact hxinv
    · right; right; left; exact hyinv
    · right; right; right
      rw [mul_inv_rev, hxinv, hyinv, hyx]

theorem normalizer_cases {G : Type} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hc : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) {N : Subgroup G}
    (hxN : centralizer ({x} : Set G) ≤ N) (hyN : centralizer ({y} : Set G) ≤ N)
    (hxyN : centralizer ({x * y} : Set G) ≤ N) (hnc1 : ¬ IsConj x y) (hnc2 : ¬ IsConj x (x * y))
    {Q : Subgroup G} (hQ : Q ≠ ⊥) (hQD : Q ≤ Subgroup.closure ({x, y} : Set G)) :
    normalizer (Q : Set G) ≤ N := by
  intro n hn
  have hcl := fun z (hz : z ∈ Q) => mem_closure_pair_of_comm hx hy hc (hQD hz)
  have hconj : ∀ q ∈ Q, n * q * n⁻¹ ∈ Q := fun q hq => (Subgroup.mem_normalizer_iff.1 hn q).1 hq
  have hne1 : ∀ q : G, q ≠ 1 → n * q * n⁻¹ ≠ 1 := by
    intro q hq h
    apply hq
    have : n * q * n⁻¹ = 1 := h
    simpa using this
  have hcent : ∀ q : G, n * q * n⁻¹ = q → n ∈ centralizer ({q} : Set G) := by
    intro q h
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    calc h' * n = (n * h' * n⁻¹) * n := by rw [h]
      _ = n * h' := by group
  have hxyne : x * y ≠ 1 := by
    intro h
    apply hnc1
    have h1 : y = x := by
      have h2 : x⁻¹ = y := inv_eq_of_mul_eq_one_right h
      rw [← h2]
      exact inv_eq_of_mul_eq_one_right hx
    rw [h1]
  have hconjx : IsConj x (n * x * n⁻¹) := isConj_iff.2 ⟨n, rfl⟩
  have hconjxy : IsConj (x * y) (n * (x * y) * n⁻¹) := isConj_iff.2 ⟨n, rfl⟩
  have hconjy : IsConj y (n * y * n⁻¹) := isConj_iff.2 ⟨n, rfl⟩
  by_cases hxQ : x ∈ Q
  · rcases hcl _ (hconj x hxQ) with h | h | h | h
    · exact absurd h (hne1 x hx1)
    · exact hxN (hcent x h)
    · exact absurd (h ▸ hconjx) hnc1
    · exact absurd (h ▸ hconjx) hnc2
  · by_cases hyQ : y ∈ Q
    · rcases hcl _ (hconj y hyQ) with h | h | h | h
      · exact absurd h (hne1 y hy1)
      · exact absurd (h ▸ hconj y hyQ) hxQ
      · exact hyN (hcent y h)
      · exfalso
        have hxyQ : x * y ∈ Q := h ▸ hconj y hyQ
        apply hxQ
        have : x = (x * y) * y := by rw [mul_assoc, hy, mul_one]
        rw [this]
        exact Q.mul_mem hxyQ hyQ
    · obtain ⟨q, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hQ
      have hqQ' : (q : G) ∈ Q := q.2
      have hq1' : (q : G) ≠ 1 := fun h => hq1 (Subtype.ext h)
      have hxyQ : x * y ∈ Q := by
        rcases hcl _ hqQ' with h | h | h | h
        · exact absurd h hq1'
        · exact absurd (h ▸ hqQ') hxQ
        · exact absurd (h ▸ hqQ') hyQ
        · exact h ▸ hqQ'
      rcases hcl _ (hconj _ hxyQ) with h | h | h | h
      · exact absurd h (hne1 _ hxyne)
      · exact absurd (h ▸ hconj _ hxyQ) hxQ
      · exact absurd (h ▸ hconj _ hxyQ) hyQ
      · exact hxyN (hcent _ h)

theorem notMem_center_of_ne {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hfront : S1Front G x K) (t : ↥K)
    (h1 : (t : CentralizerBar x) ≠ 1) (hx' : (t : CentralizerBar x) ≠ xbar x) :
    t ∉ Subgroup.center ↥K := by
  intro hc
  have hcent : (t : CentralizerBar x) ∈ centralizer (K : Set (CentralizerBar x)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := Subgroup.mem_center_iff.1 hc ⟨k, hk⟩
    exact congrArg Subtype.val this
  rw [hfront.cent_eq] at hcent
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcent
  have hxx := xbar_mul_self hx
  rcases zpow_eq_one_or_self hxx k with h | h
  · exact h1 (by rw [← hk, h])
  · exact hx' (by rw [← hk, h])

theorem centralizer_le_of_yclause {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} [K.Normal] (hfront : S1Front G x K) (D : FrontData0 ↥K)
    (hExact : LiftExact x K) (G₁ : Subgroup G)
    (H' : Subgroup ↥(centralizer ({x} : Set G)))
    (hH'G : H'.map (centralizer ({x} : Set G)).subtype ≤ G₁) (hHK : H'.map (proj x) = K)
    {y : G} (hyC : y ∈ centralizer ({x} : Set G)) (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hyL : (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) ∈ liftL x K)
    (hyne : proj x ⟨y, hyC⟩ ≠ xbar x)
    (hY : centralizer ({y} : Set G) ≤ normalizer (G₁ : Set G)) :
    centralizer ({x} : Set G) ≤ normalizer (G₁ : Set G) := by
  classical
  intro c hc
  set y₀ : ↥(centralizer ({x} : Set G)) := ⟨y, hyC⟩ with hy₀
  set c₀ : ↥(centralizer ({x} : Set G)) := ⟨c, hc⟩ with hc₀
  have hy₀2 : y₀ * y₀ = 1 := Subtype.ext hy2
  have hy₀1 : y₀ ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hπK : proj x y₀ ∈ K := liftL_le x K hyL
  have hπ1 : proj x y₀ ≠ 1 := by
    intro h
    have hodd := proj_odd x y₀ h
    have : orderOf y₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hy₀2) hy₀1
    rw [this] at hodd
    exact absurd hodd (by decide)
  have hKn : ∀ t : ↥(centralizer ({x} : Set G)), proj x (t * y₀ * t⁻¹) ∈ K := by
    intro t
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.Normal.conj_mem inferInstance _ hπK (proj x t)
  set y' : ↥(centralizer ({x} : Set G)) := c₀ * y₀ * c₀⁻¹ with hy'
  have hy'2 : y' * y' = 1 := by
    rw [hy']
    calc c₀ * y₀ * c₀⁻¹ * (c₀ * y₀ * c₀⁻¹) = c₀ * (y₀ * y₀) * c₀⁻¹ := by group
      _ = 1 := by rw [hy₀2]; group
  have hy'1 : y' ≠ 1 := by
    intro h
    apply hy₀1
    have : c₀⁻¹ * y' * c₀ = y₀ := by rw [hy']; group
    rw [← this, h]; group
  have hπ'K : proj x y' ∈ K := hKn c₀
  have hπ'1 : proj x y' ≠ 1 := by
    intro h
    have hodd := proj_odd x y' h
    have : orderOf y' = 2 := orderOf_eq_prime (by rw [sq]; exact hy'2) hy'1
    rw [this] at hodd
    exact absurd hodd (by decide)
  have hπ'x : proj x y' ≠ xbar x := by
    intro h
    apply hyne
    have h1 : proj x y₀ = (proj x c₀)⁻¹ * proj x y' * proj x c₀ := by
      rw [hy']; simp only [map_mul, map_inv]; group
    rw [h1, h]
    have := xbar_comm x (proj x c₀)
    rw [mul_assoc, ← this, ← mul_assoc, inv_mul_cancel, one_mul]
  have hone : ∀ (z : ↥(centralizer ({x} : Set G))) (hzK : proj x z ∈ K), z * z = 1 → proj x z ≠ 1 → proj x z ≠ xbar x →
      ∃ k : ↥K, k * (⟨proj x z, hzK⟩ : ↥K) * k⁻¹ = D.φ (QuaternionGroup.a 2, 1) := by
    intro z hzK hz2 hz1 hzx
    refine D.oneClass _ ?_ ?_ ?_
    · apply Subtype.ext
      show proj x z * proj x z = 1
      rw [← map_mul, hz2, map_one]
    · intro h
      exact hz1 (congrArg Subtype.val h)
    · exact notMem_center_of_ne hx hfront _ hz1 hzx
  obtain ⟨k₁, hk₁⟩ := hone y₀ hπK hy₀2 hπ1 hyne
  obtain ⟨k₂, hk₂⟩ := hone y' hπ'K hy'2 hπ'1 hπ'x
  set k : ↥K := k₂⁻¹ * k₁ with hk
  have hkt : k * (⟨proj x y₀, hπK⟩ : ↥K) * k⁻¹ = ⟨proj x y', hπ'K⟩ := by
    have h1 : (⟨proj x y', hπ'K⟩ : ↥K) = k₂⁻¹ * (k₂ * ⟨proj x y', hπ'K⟩ * k₂⁻¹) * k₂ := by group
    rw [h1, hk₂, ← hk₁, hk]
    group
  have hkmem : (k : CentralizerBar x) ∈ H'.map (proj x) := hHK ▸ k.2
  obtain ⟨h', hh', hπh'⟩ := hkmem
  set u₁ : ↥(centralizer ({x} : Set G)) := h' * y₀ * h'⁻¹ with hu₁
  have hu₁2 : u₁ * u₁ = 1 := by
    rw [hu₁]
    calc h' * y₀ * h'⁻¹ * (h' * y₀ * h'⁻¹) = h' * (y₀ * y₀) * h'⁻¹ := by group
      _ = 1 := by rw [hy₀2]; group
  have hπu₁ : proj x u₁ = proj x y' := by
    have h1 : proj x u₁ = ((k * (⟨proj x y₀, hπK⟩ : ↥K) * k⁻¹ : ↥K) : CentralizerBar x) := by
      rw [hu₁, map_mul, map_mul, map_inv, hπh']
      rfl
    rw [h1, hkt]
  obtain ⟨r, hr, hru⟩ := exists_conj_of_proj_eq hu₁2 hy'2 hπu₁
  set w : ↥(centralizer ({x} : Set G)) := c₀⁻¹ * r * h' with hw
  have hwy : w * y₀ * w⁻¹ = y₀ := by
    have h1 : c₀⁻¹ * (r * u₁ * r⁻¹) * c₀ = y₀ := by rw [hru, hy']; group
    calc w * y₀ * w⁻¹ = c₀⁻¹ * (r * u₁ * r⁻¹) * c₀ := by rw [hw, hu₁]; group
      _ = y₀ := h1
  have hwC : (w : G) ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : w * y₀ = y₀ * w := by
      have := congrArg (· * w) hwy
      simpa using this
    exact congrArg Subtype.val this
  have hLn : (liftL x K).Normal := liftL_normal
  have hRn : (pPrimeCore 2 ↥(centralizer ({x} : Set G))).Normal := pPrimeCore_normal
  have hrc : r * y₀ = y₀ * r := by
    set z : ↥(centralizer ({x} : Set G)) := r * y₀ * r⁻¹ * y₀⁻¹ with hz
    have hzL : z ∈ liftL x K :=
      (liftL x K).mul_mem (hLn.conj_mem y₀ hyL r) ((liftL x K).inv_mem hyL)
    have hzR : z ∈ pPrimeCore 2 ↥(centralizer ({x} : Set G)) := by
      have h1 : z = r * (y₀ * r⁻¹ * y₀⁻¹) := by rw [hz]; group
      rw [h1]
      exact (pPrimeCore 2 ↥(centralizer ({x} : Set G))).mul_mem hr (hRn.conj_mem r⁻¹ ((pPrimeCore 2 ↥(centralizer ({x} : Set G))).inv_mem hr) y₀)
    have hπz : proj x z = 1 := (QuotientGroup.eq_one_iff z).2 hzR
    have := hExact z hzL hπz
    rw [hz] at this
    calc r * y₀ = (r * y₀ * r⁻¹ * y₀⁻¹) * y₀ * r := by group
      _ = y₀ * r := by rw [this]; group
  have hrC : (r : G) ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hrc
  have hcw : c₀ = r * h' * w⁻¹ := by rw [hw]; group
  have hcG : c = (r : G) * (h' : G) * ((w⁻¹ : ↥(centralizer ({x} : Set G))) : G) := by
    have := congrArg Subtype.val hcw
    simpa using this
  have hh'N : (h' : G) ∈ normalizer (G₁ : Set G) := Subgroup.le_normalizer (hH'G ⟨h', hh', rfl⟩)
  have hwinv : ((w⁻¹ : ↥(centralizer ({x} : Set G))) : G) ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.coe_inv]
    exact Subgroup.inv_mem _ hwC
  rw [hcG]
  exact (normalizer (G₁ : Set G)).mul_mem ((normalizer (G₁ : Set G)).mul_mem (hY hrC) hh'N)
    (hY hwinv)

theorem normalizer_clause_of_yclause_of_lift {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} [K.Normal] (hfront : S1Front G x K) (hxK : xbar x ∈ K)
    (D : FrontData0 ↥K) (hExact : LiftExact x K) {J : Fin 4 → Subgroup G} {y : G} (hyJ : y ∈ J 1)
    (hy2 : orderOf y = 2)
    (hL : ∀ hyC : y ∈ centralizer ({x} : Set G), proj x ⟨y, hyC⟩ ∈ K →
      (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) ∈ liftL x K)
    (hfacts : S1A4Facts x K J y)
    (hY : centralizer ({y} : Set G) ≤ normalizer ((⨆ i, J i : Subgroup G) : Set G)) :
    ∀ Q : Subgroup G, Q ≠ ⊥ → Q ≤ Subgroup.closure ({x, y} : Set G) →
      normalizer (Q : Set G) ≤ normalizer ((⨆ i, J i : Subgroup G) : Set G) := by
  classical
  set G₁ : Subgroup G := ⨆ i, J i with hG₁
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  have hxx : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hyy : y * y = 1 := by rw [← sq, ← hy2]; exact pow_orderOf_eq_one y
  have hyC : y ∈ centralizer ({x} : Set G) := hfacts.jc 0 hyJ
  have hxy_comm : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm
  set H' : Subgroup ↥(centralizer ({x} : Set G)) :=
    ⨆ i : Fin 3, (J i.succ).subgroupOf (centralizer ({x} : Set G)) with hH'
  have hH'G : H'.map (centralizer ({x} : Set G)).subtype ≤ G₁ := by
    rw [hH', Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hfacts.jc i)]
    exact le_iSup J i.succ
  have hxH : xH x ∈ H' := x_mem_of_proj_eq hx hxK H' hfacts.hk
  have hxG₁ : x ∈ G₁ := hH'G ⟨xH x, hxH, rfl⟩
  have hyG₁ : y ∈ G₁ := le_iSup J 1 hyJ
  have hyH : (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) ∈ H' := by
    have : (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) ∈ (J (0 : Fin 3).succ).subgroupOf
        (centralizer ({x} : Set G)) := hyJ
    exact le_iSup (fun i : Fin 3 => (J i.succ).subgroupOf (centralizer ({x} : Set G))) 0 this
  have hπyK : proj x ⟨y, hyC⟩ ∈ K := by
    rw [← hfacts.hk]
    exact Subgroup.mem_map_of_mem _ hyH
  have hyx : y ≠ x := by
    intro h
    apply hfacts.noncomm
    intro v hv
    have hvC : v ∈ centralizer ({x} : Set G) := hfacts.jc 1 hv
    have := Subgroup.mem_centralizer_iff.1 hvC y (by rw [h]; exact Set.mem_singleton x)
    exact this.symm
  have hy₀2 : (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) * ⟨y, hyC⟩ = 1 := Subtype.ext hyy
  have hy₀1 : (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hπ1 : proj x ⟨y, hyC⟩ ≠ 1 := by
    intro h
    have hodd := proj_odd x _ h
    have : orderOf (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hy₀2) hy₀1
    rw [this] at hodd
    exact absurd hodd (by decide)
  have hπyne : proj x ⟨y, hyC⟩ ≠ xbar x := by
    intro h
    apply hyx
    have hxx' : xH x * xH x = 1 := xH_mul_self hx
    have hc : (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) * xH x = xH x * ⟨y, hyC⟩ :=
      xH_central x ⟨y, hyC⟩
    have := eq_of_proj_eq hy₀2 hxx' hc h
    exact congrArg Subtype.val this
  have hxy_nc : ¬ IsConj x y := hfront.b5 y hyC hyy hπyK hπyne
  have hxyC : x * y ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x * y) * x = x * (y * x) := by rw [mul_assoc]
      _ = x * (x * y) := by rw [← hxy_comm]
  have hxy2 : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [← hxy_comm]
      _ = (x * x) * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hxx, hyy, one_mul]
  have hπxyK : proj x ⟨x * y, hxyC⟩ ∈ K := by
    have : proj x ⟨x * y, hxyC⟩ = xbar x * proj x ⟨y, hyC⟩ := by
      rw [show xbar x = proj x (xH x) from rfl, ← map_mul]
      rfl
    rw [this]
    exact K.mul_mem hxK hπyK
  have hπxyne : proj x ⟨x * y, hxyC⟩ ≠ xbar x := by
    intro h
    apply hπ1
    have : proj x ⟨x * y, hxyC⟩ = xbar x * proj x ⟨y, hyC⟩ := by
      rw [show xbar x = proj x (xH x) from rfl, ← map_mul]
      rfl
    rw [this] at h
    exact (mul_eq_left.1 h)
  have hxxy_nc : ¬ IsConj x (x * y) := hfront.b5 (x * y) hxyC hxy2 hπxyK hπxyne
  obtain ⟨a, b, hab⟩ := hfacts.classes
  have hcl := two_classes hxy_nc hab hxG₁ hyG₁ hx hy2
  have hL' : (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) ∈ liftL x K := hL hyC hπyK
  have hCx : centralizer ({x} : Set G) ≤ normalizer (G₁ : Set G) :=
    centralizer_le_of_yclause hx hfront D hExact G₁ H' hH'G hfacts.hk hyC hyy hy1 hL' hπyne hY
  have hxy1 : x * y ≠ 1 := by
    intro h
    apply hyx
    have h2 : x⁻¹ = y := inv_eq_of_mul_eq_one_right h
    rw [← h2]
    exact inv_eq_of_mul_eq_one_right hxx
  have hCxy : centralizer ({x * y} : Set G) ≤ normalizer (G₁ : Set G) := by
    have hxyG₁ : x * y ∈ G₁ := G₁.mul_mem hxG₁ hyG₁
    have hxy2' : orderOf (x * y) = 2 := orderOf_eq_prime (by rw [sq]; exact hxy2) hxy1
    obtain ⟨g, hg, hcase⟩ := hcl (x * y) hxyG₁ hxy2'
    rcases hcase with h | h
    · refine absurd (isConj_iff.2 ⟨g, ?_⟩) hxxy_nc
      calc g * x * g⁻¹ = g * (g⁻¹ * (x * y) * g) * g⁻¹ := by rw [h]
        _ = x * y := by group
    · intro n hn
      have hnc : n * (x * y) = (x * y) * n := (Subgroup.mem_centralizer_singleton_iff.1 hn)
      have hm : g⁻¹ * n * g ∈ centralizer ({y} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc g⁻¹ * n * g * y = g⁻¹ * n * g * (g⁻¹ * (x * y) * g) := by rw [h]
          _ = g⁻¹ * (n * (x * y)) * g := by group
          _ = g⁻¹ * ((x * y) * n) * g := by rw [hnc]
          _ = (g⁻¹ * (x * y) * g) * (g⁻¹ * n * g) := by group
          _ = y * (g⁻¹ * n * g) := by rw [h]
      have hgN : g ∈ normalizer (G₁ : Set G) := Subgroup.le_normalizer hg
      have : n = g * (g⁻¹ * n * g) * g⁻¹ := by group
      rw [this]
      exact (normalizer (G₁ : Set G)).mul_mem ((normalizer (G₁ : Set G)).mul_mem hgN (hY hm))
        ((normalizer (G₁ : Set G)).inv_mem hgN)
  intro Q hQ hQD
  exact normalizer_cases hxx hyy hxy_comm hx1 hy1 hCx hY hCxy hxy_nc hxxy_nc hQ hQD

@[expose] def S1NormalizerYClause : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → S1LargeModel K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → S1SymFrame x u →
        ∀ y ∈ symJ (symX x u) 1, orderOf y = 2 → (∀ a ∈ symJ (symX x u) 1, a * y = y * a) →
          centralizer ({y} : Set G) ≤ normalizer ((⨆ i, symJ (symX x u) i : Subgroup G) : Set G)

theorem normalizer_clause_of_yclause {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} [K.Normal] (hfront : S1Front G x K) (hxK : xbar x ∈ K)
    (D : FrontData0 ↥K) (hExact : LiftExact x K) {J : Fin 4 → Subgroup G} {y : G} (hyJ : y ∈ J 1)
    (hy2 : orderOf y = 2) (hJ1 : ⁅J 1, J 1⁆ = J 1) (hfacts : S1A4Facts x K J y)
    (hY : centralizer ({y} : Set G) ≤ normalizer ((⨆ i, J i : Subgroup G) : Set G)) :
    ∀ Q : Subgroup G, Q ≠ ⊥ → Q ≤ Subgroup.closure ({x, y} : Set G) →
      normalizer (Q : Set G) ≤ normalizer ((⨆ i, J i : Subgroup G) : Set G) := by
  refine normalizer_clause_of_yclause_of_lift hx hfront hxK D hExact hyJ hy2 (fun hyC _ => ?_) hfacts hY
  have hP : ⁅(J 1).subgroupOf (centralizer ({x} : Set G)),
      (J 1).subgroupOf (centralizer ({x} : Set G))⁆ =
      (J 1).subgroupOf (centralizer ({x} : Set G)) := by
    have hJ1C : J 1 ≤ centralizer ({x} : Set G) := hfacts.jc 0
    apply Subgroup.map_injective (centralizer ({x} : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hJ1C, hJ1]
  have hPK : (J 1).subgroupOf (centralizer ({x} : Set G)) ≤ K.comap (proj x) := by
    intro g hg
    have hgH : g ∈ ⨆ i : Fin 3, (J i.succ).subgroupOf (centralizer ({x} : Set G)) :=
      le_iSup (fun i : Fin 3 => (J i.succ).subgroupOf (centralizer ({x} : Set G))) 0 hg
    rw [Subgroup.mem_comap, ← hfacts.hk]
    exact Subgroup.mem_map_of_mem _ hgH
  exact perfect_le_liftL hPK hP hyJ

variable {G : Type} [Group G] [Finite G]

theorem symJ_one_perfect (X : Fin 5 → G) : ⁅symJ X 1, symJ X 1⁆ = symJ X 1 :=
  resCent_perfect _

theorem s1Nbhd_lin_of_yclause (hExact : S1LiftExactProp) (hY : S1NormalizerYClause)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu)
    (hsym : S1SymFrame x u) {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (h4 : 3 < Nat.card F) (hlin : S1SymFrameLin x u F) (ops : BlockOps F (StatedSL 4 F))
    (hstd : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      ∃ W : Subgroup ↥(StatedSL 4 F), (linKind F).Pair W (ops.blk a b) (ops.blk b c))
    (hchain : ∃ W : Fin 3 → Fin 3 → Subgroup ↥(StatedSL 4 F),
      (linKind F).Chain (fun i : Fin 3 => ops.blk i.castSucc i.succ) W)
    (hcen : ∃ z ∈ ops.blk 0 1, orderOf z = 2 ∧ ∀ g ∈ ops.blk 0 1, g * z = z * g) :
    ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J := by
  obtain ⟨-, -, hXc, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData hExact x u hw hloc
  obtain ⟨hcomm, hpair, ⟨U, W, hchain', hlinked⟩, ⟨z, hz, hz2, hzc⟩⟩ :=
    symSystem ops (symX x u) D hw hDact (linKind F) hstd hchain hcen
  have hK : (D 4).K = K := (hDK 4).trans hfront.layer_eq
  have eK : ↥K ≃* ↥(StatedSL 4 F) := by
    have h : (D 4).K = K := hK
    subst h
    exact (D 4).iso
  have hbigK : S1LargeModel K := Or.inl ⟨F, inferInstance, inferInstance, hF, h4, ⟨eK⟩⟩
  obtain ⟨p, f, hpp, -, hcard⟩ := exists_prime_pow_card F
  have hlink : S1LinkedLin x (D 4).K F (symJ (symX x u)) := ⟨U, W, hchain', hlinked⟩
  have hlinkK : S1LinkedLin x K F (symJ (symX x u)) := hlink.congr hK
  have hq3 : 3 ≤ p ^ f := by rw [← hcard]; omega
  refine ⟨symJ (symX x u), Or.inl ⟨p, f, F, inferInstance, inferInstance, hpp, hcard, hq3,
    ⟨hcomm, hpair⟩, hlinkK⟩, ⟨z, hz, hz2, hzc, ?_⟩⟩
  intro Q hQ hQle
  have hKn : K.Normal := normal_of_layer_eq hfront.layer_eq
  have hfacts := s1A4Facts_lin (symJ (symX x u)) p f F hpp hcard hq3 ⟨hcomm, hpair⟩ hlinkK hz hz2 hzc
  obtain ⟨D0⟩ := frontDataStatement ↥K (Or.inl hset.shape.1)
  exact normalizer_clause_of_yclause hset.inv hfront hset.shape.2 D0.toFrontData0 (hExact G x K hset hfront) hz hz2
    (symJ_one_perfect _) hfacts (hY G x K hset hfront hbigK u hu hf hsym z hz hz2 hzc) Q hQ hQle

theorem s1Nbhd_uni_of_yclause (hExact : S1LiftExactProp) (hY : S1NormalizerYClause)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu)
    (hsym : S1SymFrame x u) {q : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) (huni : S1SymFrameUni x u q F) (ops : BlockOps F (StatedSU 4 q F))
    (p f : ℕ) [Fact p.Prime] [CharP F p] (hqpf : q = p ^ f)
    (hstd : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      ∃ W : Subgroup ↥(StatedSU 4 q F), (uniKind F p f).Pair W (ops.blk a b) (ops.blk b c))
    (hchain : ∃ W : Fin 3 → Fin 3 → Subgroup ↥(StatedSU 4 q F),
      (uniKind F p f).Chain (fun i : Fin 3 => ops.blk i.castSucc i.succ) W)
    (hcen : ∃ z ∈ ops.blk 0 1, orderOf z = 2 ∧ ∀ g ∈ ops.blk 0 1, g * z = z * g) :
    ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J := by
  obtain ⟨-, -, hXc, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSU 4 q F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := huni e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData hExact x u hw hloc
  obtain ⟨hcomm, hpair, ⟨U, W, hchain', hlinked⟩, ⟨z, hz, hz2, hzc⟩⟩ :=
    symSystem ops (symX x u) D hw hDact (uniKind F p f) hstd hchain hcen
  have hK : (D 4).K = K := (hDK 4).trans hfront.layer_eq
  have eK : ↥K ≃* ↥(StatedSU 4 q F) := by
    have h : (D 4).K = K := hK
    subst h
    exact (D 4).iso
  have hbigK : S1LargeModel K := Or.inr ⟨q, F, inferInstance, inferInstance, hF, hq, ⟨eK⟩⟩
  have hlink : S1LinkedUni x (D 4).K F p f (symJ (symX x u)) := ⟨U, W, hchain', hlinked⟩
  have hlinkK : S1LinkedUni x K F p f (symJ (symX x u)) := hlink.congr hK
  have hq5 : 5 ≤ p ^ f := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    have hq1 : 1 < q := by
      by_contra hle
      have hle' : q ≤ 1 := by omega
      interval_cases q <;> simp at h1
    rw [← hqpf]
    omega
  have hFpf : Nat.card F = (p ^ f) ^ 2 := by rw [← hqpf]; exact hF
  refine ⟨symJ (symX x u), Or.inr ⟨p, f, F, inferInstance, inferInstance, inferInstance, inferInstance,
    hFpf, hq5, ⟨hcomm, hpair⟩, hlinkK⟩, ⟨z, hz, hz2, hzc, ?_⟩⟩
  intro Q hQ hQle
  have hKn : K.Normal := normal_of_layer_eq hfront.layer_eq
  have hfacts := s1A4Facts_uni (symJ (symX x u)) p f F hFpf hq5 ⟨hcomm, hpair⟩ hlinkK hz hz2 hzc
  obtain ⟨D0⟩ := frontDataStatement ↥K (Or.inl hset.shape.1)
  exact normalizer_clause_of_yclause hset.inv hfront hset.shape.2 D0.toFrontData0 (hExact G x K hset hfront) hz hz2
    (symJ_one_perfect _) hfacts (hY G x K hset hfront hbigK u hu hf hsym z hz hz2 hzc) Q hQ hQle

end CFSG.GH74.Generic.S1
