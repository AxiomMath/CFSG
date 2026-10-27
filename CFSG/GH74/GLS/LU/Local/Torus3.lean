module

public import CFSG.GH74.GLS.LU.Local.Torus2

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
open scoped Pointwise MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

theorem zpowers_cross_comm {A : Type*} [Group A] {y₀ y₂ : A} (h : y₀ * y₂ = y₂ * y₀) :
    ∀ a ∈ zpowers y₀, ∀ b ∈ zpowers y₂, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
  exact (Commute.zpow_zpow (show Commute y₀ y₂ from h) i j).eq

theorem sup_zpowers_comm {A : Type*} [Group A] {y₀ y₂ : A} (h : y₀ * y₂ = y₂ * y₀) :
    ∀ x ∈ zpowers y₀ ⊔ zpowers y₂, ∀ x' ∈ zpowers y₀ ⊔ zpowers y₂, x * x' = x' * x := by
  have hc : Commute y₀ y₂ := h
  intro x hx x' hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute (zpowers_cross_comm h) hx
  obtain ⟨a', ha', b', hb', rfl⟩ := mem_sup_of_commute (zpowers_cross_comm h) hx'
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨i', rfl⟩ := mem_zpowers_iff.mp ha'
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
  obtain ⟨j', rfl⟩ := mem_zpowers_iff.mp hb'
  have e1 : y₀ ^ i * y₀ ^ i' = y₀ ^ i' * y₀ ^ i := (Commute.zpow_zpow_self y₀ i i').eq
  have e2 : y₂ ^ j * y₂ ^ j' = y₂ ^ j' * y₂ ^ j := (Commute.zpow_zpow_self y₂ j j').eq
  have e3 : y₀ ^ i * y₂ ^ j' = y₂ ^ j' * y₀ ^ i := (hc.zpow_zpow i j').eq
  have e4 : y₀ ^ i' * y₂ ^ j = y₂ ^ j * y₀ ^ i' := (hc.zpow_zpow i' j).eq
  calc y₀ ^ i * y₂ ^ j * (y₀ ^ i' * y₂ ^ j') = y₀ ^ i * (y₂ ^ j * y₀ ^ i') * y₂ ^ j' := by group
    _ = y₀ ^ i * (y₀ ^ i' * y₂ ^ j) * y₂ ^ j' := by rw [← e4]
    _ = (y₀ ^ i * y₀ ^ i') * (y₂ ^ j * y₂ ^ j') := by group
    _ = (y₀ ^ i' * y₀ ^ i) * (y₂ ^ j' * y₂ ^ j) := by rw [e1, e2]
    _ = y₀ ^ i' * (y₀ ^ i * y₂ ^ j') * y₂ ^ j := by group
    _ = y₀ ^ i' * (y₂ ^ j' * y₀ ^ i) * y₂ ^ j := by rw [e3]
    _ = y₀ ^ i' * y₂ ^ j' * (y₀ ^ i * y₂ ^ j) := by group

theorem sup_zpowers_pow_eq_one {A : Type*} [Group A] {y₀ y₂ : A} {r : ℕ} (h : y₀ * y₂ = y₂ * y₀)
    (h₀ : y₀ ^ r = 1) (h₂ : y₂ ^ r = 1) : ∀ x ∈ zpowers y₀ ⊔ zpowers y₂, x ^ r = 1 := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute (zpowers_cross_comm h) hx
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
  have hc : Commute (y₀ ^ i) (y₂ ^ j) := Commute.zpow_zpow (show Commute y₀ y₂ from h) i j
  have h1 : (y₀ ^ i) ^ r = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h₀, one_zpow]
  have h2 : (y₂ ^ j) ^ r = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h₂, one_zpow]
  rw [hc.mul_pow, h1, h2, one_mul]

variable {G : Type} [Group G] [Finite G] {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}
  {p f : ℕ} {ε : ℤ}

omit [Finite G] in
theorem mem_zpowers_of_centralizes₂ {q : ℕ} (hc : LUComps G q z K₁ K₂) {a : G} (ha : a ∈ K₂)
    (h : ∀ k ∈ K₂, a * k = k * a) : a ∈ zpowers z := by
  have : (⟨a, ha⟩ : ↥K₂) ∈ center ↥K₂ := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact (h k k.2).symm
  have h1 : a ∈ (center ↥K₂).map K₂.subtype := ⟨⟨a, ha⟩, this, rfl⟩
  rw [hc.cen₂] at h1
  exact h1

omit [Finite G] in
theorem conj_z_not_mem_zpowers (hs : LUSyl G z S K₁ K₂ t u) {h₀ : G}
    (hh₀ : h₀⁻¹ * z * h₀ = u) : (h₀ * z * h₀⁻¹) ∉ zpowers z := by
  intro hmem
  have hz2 : z * z = 1 := hs.z_sq
  rcases eq_one_or_eq_of_mem_zpowers hz2 hmem with h | h
  · apply hs.z_ne_one
    calc z = h₀⁻¹ * (h₀ * z * h₀⁻¹) * h₀ := by group
      _ = 1 := by rw [h]; group
  · apply hs.u_ne
    calc u = h₀⁻¹ * z * h₀ := hh₀.symm
      _ = h₀⁻¹ * (h₀ * z * h₀⁻¹) * h₀ := by rw [h]
      _ = z := by group

theorem A0_not_cent_L
    (X : LUCtx G p f z S K₁ K₂ t u ε) {h₀ : G} (hh₀ : h₀⁻¹ * z * h₀ = u)
    {a₀ : G} (ha₀ : a₀ ∈ A0 z) {r : ℕ} (hr : r.Prime) (hord : orderOf a₀ = r) :
    ¬ ∀ k ∈ cj K₁ h₀, a₀ * k = k * a₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic ↥(A0 z) := X.eps.A0_cyc
  intro hcent
  have hc := X.comps
  have hs := X.syl
  have hz2 : z * z = 1 := hs.z_sq
  have hYne : (zpowers a₀ : Subgroup G) ≠ ⊥ := by
    intro h
    have h1 : a₀ ∈ (zpowers a₀ : Subgroup G) := mem_zpowers a₀
    rw [h, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hord
    exact hr.one_lt.ne hord
  have hYr : ∃ r' : ℕ, r'.Prime ∧ IsPGroup r' (zpowers a₀ : Subgroup G) :=
    ⟨r, hr, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])⟩
  have hYA : (zpowers a₀ : Subgroup G) ≤ A0 z := (Subgroup.zpowers_le).mpr ha₀
  have hCY : Cz z ≤ normalizer ((zpowers a₀ : Subgroup G) : Set G) := fun c hc' =>
    normalizer_le_of_cyclic hYA (mem_normalizer_pPrimeCoreOf hc')
  have hmax := hmax_of_6A X.isSimple X.nonab X.hp X.hp2 X.hq X.h6A hYne hYr hCY
  have hLC : ∀ l ∈ cj K₁ h₀, l * z = z * l := by
    intro l hl
    have hlY : l ∈ centralizer ((zpowers a₀ : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (show Commute a₀ l from hcent l hl) i).eq
    have hln : l ∈ normalizer ((zpowers a₀ : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ hlY
    have hlC : l ∈ Cz z := by rw [← hmax]; exact hln
    exact mem_centralizer_singleton_iff.mp hlC
  have hzcK : ∀ k ∈ K₁, (h₀ * z * h₀⁻¹) * k = k * (h₀ * z * h₀⁻¹) := by
    intro k hk
    have hl : h₀⁻¹ * k * h₀ ∈ cj K₁ h₀ := by
      rw [mem_cj]
      have : h₀ * (h₀⁻¹ * k * h₀) * h₀⁻¹ = k := by group
      rw [this]; exact hk
    have := hLC _ hl
    calc (h₀ * z * h₀⁻¹) * k = h₀ * (z * (h₀⁻¹ * k * h₀)) * h₀⁻¹ := by group
      _ = h₀ * ((h₀⁻¹ * k * h₀) * z) * h₀⁻¹ := by rw [this]
      _ = k * (h₀ * z * h₀⁻¹) := by group
  have hzcC : h₀ * z * h₀⁻¹ ∈ Cz z := mem_centralizer_singleton_iff.mpr (conj_comm_z hh₀ hs.zu_comm)
  have hzc2 : (h₀ * z * h₀⁻¹) * (h₀ * z * h₀⁻¹) = 1 := by rw [conj_mul_mul, hz2]; group
  exact conj_z_not_mem_zpowers hs hh₀
    (inv_cent_mem_zpowers hc hs X.odd_q (Or.inl rfl) hzcC hzc2 hzcK)

theorem exists_x
    (X : LUCtx G p f z S K₁ K₂ t u ε) {r : ℕ} (hr : GoodR p f r) {a₁ : G}
    (ha₁ : a₁ ∈ K₁ ⊓ centralizer ({u} : Set G)) (hord : orderOf a₁ = r) {a₀ : G}
    (ha₀ : a₀ ∈ A0 z) (ha₀ord : orderOf a₀ = r) {h₀ : G} (hh₀ : h₀⁻¹ * z * h₀ = u) :
    ∃ x : G, x ≠ 1 ∧ z * x = x * z ∧ u * x = x * u ∧ (∀ k ∈ K₁, x * k = k * x) ∧
      (∀ k ∈ cj K₁ h₀, x * k = k * x) ∧ (∃ a ∈ A0 z, ∃ k ∈ K₂, x = a * k ∧ orderOf k = r) ∧
      ¬ (∀ k ∈ K₂, x * k = k * x) ∧ orderOf x = r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic ↥(A0 z) := X.eps.A0_cyc
  obtain ⟨hrp, hr2, hrne, hrf, -⟩ := hr
  have : Fact r.Prime := ⟨hrp⟩
  have : Fact p.Prime := ⟨X.hp⟩
  have hc := X.comps
  have hs := X.syl
  have hcu := comps_u X hh₀
  have hrodd : Odd r := hrp.odd_of_ne_two hr2
  have h3 : 3 < p ^ f := lt_of_lt_of_le (by norm_num) X.hq
  have ha₁K : a₁ ∈ K₁ := ha₁.1
  have ha₁u : a₁ * u = u * a₁ := mem_centralizer_singleton_iff.mp ha₁.2
  obtain ⟨b, -, -, -, -, -, ⟨a₂, ha₂K, -, -, ha₂ord, ha₂u⟩⟩ :=
    exists_b hc hs hrp hr2 ha₁K ha₁u hord
  have ha₀r : a₀ ^ r = 1 := by rw [← ha₀ord]; exact pow_orderOf_eq_one a₀
  have ha₂r : a₂ ^ r = 1 := by rw [← ha₂ord]; exact pow_orderOf_eq_one a₂
  have ha₀z : a₀ * z = z * a₀ := mem_centralizer_singleton_iff.mp (A0_le_Cz ha₀)
  have ha₀u : a₀ * u = u * a₀ := by
    have h := X.h61.u_cent a₀ ha₀
    calc a₀ * u = (u * a₀ * u⁻¹) * u := by rw [h]
      _ = u * a₀ := by group
  have ha₀K : ∀ k ∈ K₁ ⊔ K₂, a₀ * k = k * a₀ := fun k hk =>
    mem_centralizer_iff.mp (hc.le_centralizer_A0 hk) a₀ ha₀
  have ha₀a₂ : a₀ * a₂ = a₂ * a₀ := ha₀K a₂ (Subgroup.mem_sup_right ha₂K)
  have ha₂z : a₂ * z = z * a₂ := hc.cz₂ ha₂K
  have ha₀L : a₀ ∈ normalizer ((cj K₁ h₀ : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (hcu.odd_fix (mem_centralizer_singleton_iff.mpr ha₀u) (by rw [ha₀ord]; exact hrodd)).1
  have ha₂L : a₂ ∈ normalizer ((cj K₁ h₀ : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (hcu.odd_fix (mem_centralizer_singleton_iff.mpr ha₂u) (by rw [ha₂ord]; exact hrodd)).1
  obtain ⟨F, hF, hFin, hFq, -⟩ := hc.sl₁
  obtain ⟨e⟩ := exists_mulEquiv_cj (exists_mulEquiv_SL2 hc.sl₁ F hFq) h₀
  have hrF : (r : F) ≠ 0 := by
    have : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card]; exact hFq
    have hchar : CharP F p := charP_of_card_eq_prime_pow hcard
    intro h0
    have hpr : p ∣ r := (CharP.cast_eq_zero_iff F p r).mp h0
    exact hrne ((Nat.prime_dvd_prime_iff_eq X.hp hrp).mp hpr).symm
  have hα₀r : actAut e a₀ ha₀L ^ r = 1 := by
    rw [← actAut_pow e ha₀L r]
    exact (actAut_eq_one_iff e _).mpr (fun k _ => by rw [ha₀r, one_mul, mul_one])
  have hα₂r : actAut e a₂ ha₂L ^ r = 1 := by
    rw [← actAut_pow e ha₂L r]
    exact (actAut_eq_one_iff e _).mpr (fun k _ => by rw [ha₂r, one_mul, mul_one])
  obtain ⟨y₀, hy₀r, hy₀⟩ := exists_odd_lift X.hp hFq X.hp2 h3 hrp hr2 hrf hα₀r
  obtain ⟨y₂, hy₂r, hy₂⟩ := exists_odd_lift X.hp hFq X.hp2 h3 hrp hr2 hrf hα₂r
  have hcomm₀₂ : actAut e a₀ ha₀L * actAut e a₂ ha₂L = actAut e a₂ ha₂L * actAut e a₀ ha₀L := by
    rw [← actAut_mul e ha₀L ha₂L, ← actAut_mul e ha₂L ha₀L]
    exact actAut_congr e _ _ ha₀a₂
  have hy₀₂ : y₀ * y₂ = y₂ * y₀ := by
    have hfix : MulAut.conj y₀ y₂ = y₂ := by
      refine aut_fix_of_commute hrodd hy₂r ?_
      rw [← hy₀, ← hy₂]; exact hcomm₀₂
    have h' : y₀ * y₂ * y₀⁻¹ = y₂ := by simpa [MulAut.conj_apply] using hfix
    calc y₀ * y₂ = (y₀ * y₂ * y₀⁻¹) * y₀ := by group
      _ = y₂ * y₀ := by rw [h']
  have hXab := sup_zpowers_comm hy₀₂
  have hXexp := sup_zpowers_pow_eq_one hy₀₂ hy₀r hy₂r
  have hXcard : Nat.card ↥(zpowers y₀ ⊔ zpowers y₂) ≤ r :=
    sl2_elem_abelian_card_le hrp hr2 hrF _ hXab hXexp
  have hy₀1 : y₀ ≠ 1 := by
    intro h1
    apply A0_not_cent_L X hh₀ ha₀ hrp ha₀ord
    intro k hk
    have : actAut e a₀ ha₀L = 1 := by rw [hy₀, h1, map_one]
    exact (actAut_eq_one_iff e ha₀L).mp this k hk
  have hy₀ord : orderOf y₀ = r := orderOf_eq_prime hy₀r hy₀1
  have hcardz : Nat.card ↥(zpowers y₀) = r := by rw [Nat.card_zpowers, hy₀ord]
  have hzXg : zpowers y₀ = zpowers y₀ ⊔ zpowers y₂ :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcardz]; exact hXcard)
  have hy₂mem : y₂ ∈ zpowers y₀ := by
    rw [hzXg]; exact Subgroup.mem_sup_right (mem_zpowers y₂)
  obtain ⟨m, hm⟩ :=
    (Submonoid.mem_powers_iff y₂ y₀).mp (mem_powers_iff_mem_zpowers.mpr hy₂mem)
  have hxn : a₀ ^ m * a₂⁻¹ ∈ normalizer ((cj K₁ h₀ : Subgroup G) : Set G) :=
    (normalizer ((cj K₁ h₀ : Subgroup G) : Set G)).mul_mem
      ((normalizer ((cj K₁ h₀ : Subgroup G) : Set G)).pow_mem ha₀L m)
      ((normalizer ((cj K₁ h₀ : Subgroup G) : Set G)).inv_mem ha₂L)
  have hxone : actAut e (a₀ ^ m * a₂⁻¹) hxn = 1 := by
    rw [actAut_mul e ((normalizer ((cj K₁ h₀ : Subgroup G) : Set G)).pow_mem ha₀L m)
      ((normalizer ((cj K₁ h₀ : Subgroup G) : Set G)).inv_mem ha₂L), actAut_pow e ha₀L m,
      actAut_inv e ha₂L, hy₀, hy₂,
      ← map_pow (MulAut.conj : SL(2, F) →* MulAut SL(2, F)), hm]
    exact mul_inv_cancel _
  have hxcent : ∀ k ∈ cj K₁ h₀, (a₀ ^ m * a₂⁻¹) * k = k * (a₀ ^ m * a₂⁻¹) :=
    (actAut_eq_one_iff e hxn).mp hxone
  have hcomm_x : ∀ w : G, w * a₀ = a₀ * w → w * a₂ = a₂ * w →
      w * (a₀ ^ m * a₂⁻¹) = (a₀ ^ m * a₂⁻¹) * w := by
    intro w h1 h2
    have c1 : Commute w a₀ := h1
    have c2 : Commute w a₂ := h2
    exact ((c1.pow_right m).mul_right c2.inv_right).eq
  have hnc₂ : ¬ ∀ k ∈ K₂, a₂ * k = k * a₂ := by
    intro h
    have h2 : a₂ ∈ zpowers z := mem_zpowers_of_centralizes₂ hc ha₂K h
    have h3 : orderOf a₂ ∣ orderOf z := orderOf_dvd_of_mem_zpowers h2
    rw [ha₂ord, hs.z_inv] at h3
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp h3)
  have hxnc : ¬ ∀ k ∈ K₂, (a₀ ^ m * a₂⁻¹) * k = k * (a₀ ^ m * a₂⁻¹) := by
    intro h
    apply hnc₂
    intro k hk
    have cx : Commute (a₀ ^ m * a₂⁻¹) k := h k hk
    have ca : Commute (a₀ ^ m) k :=
      (show Commute a₀ k from ha₀K k (Subgroup.mem_sup_right hk)).pow_left m
    have c3 : Commute a₂⁻¹ k := by
      have h' := (ca.inv_left).mul_left cx
      simpa using h'
    have c4 : Commute a₂ k := by simpa using c3.inv_left
    exact c4.eq
  have hx1 : a₀ ^ m * a₂⁻¹ ≠ 1 := by
    intro h1
    apply hxnc
    intro k _
    rw [h1, one_mul, mul_one]
  have hxr : (a₀ ^ m * a₂⁻¹) ^ r = 1 := by
    have hcm : Commute (a₀ ^ m) a₂⁻¹ := ((show Commute a₀ a₂ from ha₀a₂).pow_left m).inv_right
    rw [hcm.mul_pow, inv_pow, ← pow_mul, mul_comm m r, pow_mul, ha₀r, one_pow, ha₂r, inv_one,
      one_mul]
  refine ⟨a₀ ^ m * a₂⁻¹, hx1, hcomm_x z ha₀z.symm ha₂z.symm, hcomm_x u ha₀u.symm ha₂u.symm, ?_, hxcent,
    ⟨a₀ ^ m, (A0 z).pow_mem ha₀ m, a₂⁻¹, K₂.inv_mem ha₂K, rfl, by rw [orderOf_inv, ha₂ord]⟩, hxnc,
    orderOf_eq_prime hxr hx1⟩
  intro k hk
  exact (hcomm_x k (ha₀K k (Subgroup.mem_sup_left hk)).symm (hc.comm k hk a₂ ha₂K)).symm

end CFSG.GH74.GLS.LU.Local
