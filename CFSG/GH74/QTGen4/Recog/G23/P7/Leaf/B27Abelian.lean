module

public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open scoped MatrixGroups

section Generic

open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_sup_iff_of_normalizes {A B : Subgroup G} (hB : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A)
    {x : G} : x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  refine ⟨fun hx => ?_, fun ⟨a, ha, b, hb, h⟩ => h ▸ mul_mem (Subgroup.mem_sup_left ha)
    (Subgroup.mem_sup_right hb)⟩
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, mul_one x⟩
    · exact ⟨1, A.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy
    exact ⟨a₁ * (b₁ * a₂ * b₁⁻¹), A.mul_mem ha₁ (hB b₁ hb₁ a₂ ha₂), b₁ * b₂, B.mul_mem hb₁ hb₂,
      by group⟩
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have h1 := hB b⁻¹ (B.inv_mem hb) a⁻¹ (A.inv_mem ha)
    refine ⟨b⁻¹ * a⁻¹ * b, by simpa using h1, b⁻¹, B.inv_mem hb, by group⟩

theorem card_sup_of_normalizes [Finite G] {A B : Subgroup G}
    (hB : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (hAB : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hmem : ∀ p : ↥A × ↥B, (p.1 : G) * (p.2 : G) ∈ A ⊔ B := fun p =>
    mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
  let f : ↥A × ↥B → ↥(A ⊔ B) := fun p => ⟨(p.1 : G) * (p.2 : G), hmem p⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : G) * (b : G) = (a' : G) * (b' : G) := congrArg Subtype.val h
    have key : (a' : G)⁻¹ * a = (b' : G) * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * ((a : G) * (b : G)) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * ((a' : G) * (b' : G)) * (b : G)⁻¹ := by rw [h']
        _ = (b' : G) * (b : G)⁻¹ := by group
    have hmem2 : (a' : G)⁻¹ * a ∈ A ⊓ B := by
      refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
      rw [key]
      exact B.mul_mem b'.2 (B.inv_mem b.2)
    rw [hAB, Subgroup.mem_bot] at hmem2
    have haa : a = a' := Subtype.ext (inv_mul_eq_one.mp hmem2).symm
    subst haa
    have hbb : b = b' := Subtype.ext (mul_left_cancel h')
    subst hbb
    rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_normalizes hB).mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

theorem zpowers_central {M : Subgroup G} {σ : G} (hσc : ∀ m ∈ M, σ * m = m * σ) :
    ∀ c ∈ Subgroup.zpowers σ, ∀ m ∈ M, c * m = m * c := by
  intro c hc m hm
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact (Commute.zpow_left (show Commute σ m from hσc m hm) k).eq

theorem conj_of_commute_zpowers {σ g : G} (h : g * σ = σ * g) {c : G}
    (hc : c ∈ Subgroup.zpowers σ) : g * c * g⁻¹ = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hk : g * σ ^ k = σ ^ k * g := (Commute.zpow_right (show Commute g σ from h) k).eq
  rw [hk, mul_inv_cancel_right]

theorem zpow_three_mod {σ : G} (h3 : orderOf σ = 3) (k : ℤ) : σ ^ k = σ ^ (k % 3) := by
  have := zpow_mod_orderOf σ k
  rw [h3] at this
  simpa using this.symm

theorem cube_of_mem_zpowers {σ : G} (h3 : σ ^ 3 = 1) {c : G} (hc : c ∈ Subgroup.zpowers σ) :
    c ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]

theorem eq_one_of_sq_cube {d : G} (h2 : d * d = 1) (h3 : d ^ 3 = 1) : d = 1 := by
  have : d = d ^ 3 * (d * d)⁻¹ := by group
  rw [this, h2, h3]
  simp

theorem zpowers_comm_zpowers {σ : G} {s s' : G} (hs : s ∈ Subgroup.zpowers σ)
    (hs' : s' ∈ Subgroup.zpowers σ) : s * s' = s' * s := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs'
  exact zpow_mul_comm σ k l

theorem conj_fix {M : Subgroup G} {σ : G} (hσc : ∀ m ∈ M, σ * m = m * σ) {c : G}
    (hc : c ∈ Subgroup.zpowers σ) {g : G} (hg : g ∈ M) : g * c * g⁻¹ = c := by
  have := zpowers_central hσc c hc g hg
  rw [← this, mul_inv_cancel_right]

theorem comm_mod_exists [Finite G] {M : Subgroup G} (hM : Nat.card ↥M = 27) {σ : G}
    (hσM : σ ∈ M) (hσc : ∀ m ∈ M, σ * m = m * σ) (hσ3 : orderOf σ = 3) :
    ∀ x ∈ M, ∀ y ∈ M, ∃ c ∈ Subgroup.zpowers σ, x * y = y * x * c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzM : Subgroup.zpowers σ ≤ M := Subgroup.zpowers_le.mpr hσM
  set N : Subgroup ↥M := (Subgroup.zpowers σ).subgroupOf M with hNdef
  have hNn : N.Normal := by
    constructor
    intro n hn g
    have hn' : (n : G) ∈ Subgroup.zpowers σ := (Subgroup.mem_subgroupOf).mp hn
    rw [Subgroup.mem_subgroupOf]
    have hcen := conj_fix hσc hn' g.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcen]
    exact hn'
  have hNcard : Nat.card ↥N = 3 := by
    rw [hNdef, ← hσ3, ← Nat.card_zpowers]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzM).toEquiv
  have hidx : N.index * 3 = 27 := by
    rw [← hNcard, Subgroup.index_mul_card, hM]
  have hidx9 : N.index = 9 := by omega
  have hq : Nat.card (↥M ⧸ N) = 3 ^ 2 := by
    rw [← Subgroup.index_eq_card, hidx9]; norm_num
  haveI : IsMulCommutative (↥M ⧸ N) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  intro x hx y hy
  have hc : ((⟨x, hx⟩ : ↥M) : ↥M ⧸ N) * ((⟨y, hy⟩ : ↥M) : ↥M ⧸ N) =
      ((⟨y, hy⟩ : ↥M) : ↥M ⧸ N) * ((⟨x, hx⟩ : ↥M) : ↥M ⧸ N) :=
    (inferInstance : IsMulCommutative (↥M ⧸ N)).is_comm.comm _ _
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hc
  have hd := QuotientGroup.eq.mp hc
  rw [hNdef, Subgroup.mem_subgroupOf] at hd
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hd
  refine ⟨((x * y)⁻¹ * (y * x))⁻¹, Subgroup.inv_mem _ hd, ?_⟩
  group

theorem comm_mod_zpowers [Finite G] {M : Subgroup G} (hM : Nat.card ↥M = 27) {σ : G}
    (hσM : σ ∈ M) (hσc : ∀ m ∈ M, σ * m = m * σ) (hσ3 : orderOf σ = 3) :
    ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers σ := by
  intro x hx y hy
  obtain ⟨c, hc, hxy⟩ := comm_mod_exists hM hσM hσc hσ3 x hx y hy
  have hcx : x * c * x⁻¹ = c := conj_fix hσc hc hx
  have hcy : y * c * y⁻¹ = c := conj_fix hσc hc hy
  have hcomm : x * y * x⁻¹ * y⁻¹ = c := by
    calc x * y * x⁻¹ * y⁻¹ = y * x * c * x⁻¹ * y⁻¹ := by rw [hxy]
      _ = y * (x * c * x⁻¹) * y⁻¹ := by group
      _ = y * c * y⁻¹ := by rw [hcx]
      _ = c := hcy
  rw [hcomm]
  exact hc


theorem inv_mod_of_involution [Finite G] {M : Subgroup G} (hM : Nat.card ↥M = 27) {σ z : G}
    (hσM : σ ∈ M) (hσc : ∀ m ∈ M, σ * m = m * σ) (hσ3 : orderOf σ = 3)
    (hz2 : z * z = 1) (hzσ : z * σ = σ * z)
    (hzM : ∀ m ∈ M, z * m * z⁻¹ ∈ M)
    (hMz : ∀ m ∈ M, z * m = m * z → m ∈ Subgroup.zpowers σ) :
    ∀ x ∈ M, z * x * z⁻¹ * x ∈ Subgroup.zpowers σ := by
  intro x hx
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzi2 : z⁻¹ * z⁻¹ = 1 := by rw [← mul_inv_rev, hz2, inv_one]
  have hσ3' : σ ^ 3 = 1 := by rw [← hσ3]; exact pow_orderOf_eq_one σ
  have hu : z * x * z⁻¹ ∈ M := hzM x hx
  obtain ⟨c, hc, hxu⟩ := comm_mod_exists hM hσM hσc hσ3 x hx (z * x * z⁻¹) hu
  obtain ⟨u, hu_def⟩ : ∃ u, u = z * x * z⁻¹ := ⟨_, rfl⟩
  rw [← hu_def] at hu hxu ⊢
  obtain ⟨y, hy_def⟩ : ∃ y, y = x * u := ⟨_, rfl⟩
  have hyM : y ∈ M := by rw [hy_def]; exact M.mul_mem hx hu
  have hzu : z * u * z⁻¹ = x := by
    rw [hu_def]
    calc z * (z * x * z⁻¹) * z⁻¹ = (z * z) * x * (z⁻¹ * z⁻¹) := by group
      _ = x := by rw [hz2, hzi2, one_mul, mul_one]
  have hzy : z * y * z⁻¹ = u * x := by
    rw [hy_def]
    calc z * (x * u) * z⁻¹ = (z * x * z⁻¹) * (z * u * z⁻¹) := by group
      _ = u * x := by rw [← hu_def, hzu]
  have hux : u * x = y * c⁻¹ := by
    rw [hy_def]
    calc u * x = (u * x * c) * c⁻¹ := by group
      _ = (x * u) * c⁻¹ := by rw [← hxu]
  have hzc : ∀ d ∈ Subgroup.zpowers σ, z * d * z⁻¹ = d := fun d hd =>
    conj_of_commute_zpowers hzσ hd
  have hd : c⁻¹ ∈ Subgroup.zpowers σ := Subgroup.inv_mem _ hc
  have hzy' : z * y * z⁻¹ = y * c⁻¹ := by rw [hzy, hux]
  have h1 : y * c⁻¹ * c⁻¹ = y := by
    calc y * c⁻¹ * c⁻¹ = (z * y * z⁻¹) * (z * c⁻¹ * z⁻¹) := by rw [hzy', hzc _ hd]
      _ = z * (y * c⁻¹) * z⁻¹ := by group
      _ = z * (z * y * z⁻¹) * z⁻¹ := by rw [← hzy']
      _ = y := by
        calc z * (z * y * z⁻¹) * z⁻¹ = (z * z) * y * (z⁻¹ * z⁻¹) := by group
          _ = y := by rw [hz2, hzi2, one_mul, mul_one]
  have h2 : c⁻¹ * c⁻¹ = 1 := mul_left_cancel (a := y) (by rw [mul_one, ← mul_assoc]; exact h1)
  have hc1 : c⁻¹ = 1 := eq_one_of_sq_cube h2 (cube_of_mem_zpowers hσ3' hd)
  have hyz : z * y * z⁻¹ = y := by rw [hzy', hc1, mul_one]
  have hyz' : z * y = y * z := by
    calc z * y = (z * y * z⁻¹) * z := by group
      _ = y * z := by rw [hyz]
  have hy_mem : y ∈ Subgroup.zpowers σ := hMz y hyM hyz'
  rw [hux, hc1, mul_one]
  exact hy_mem

theorem centralize_of_trivial [Finite G] {M : Subgroup G} {σ τ z : G} (hσ3 : σ ^ 3 = 1)
    (hστ : σ * τ = τ * σ) (hzσ : z * σ = σ * z) (hzτ : z * τ = τ * z) (hz2 : z * z = 1)
    (hσc : ∀ m ∈ M, σ * m = m * σ) (hzM : ∀ m ∈ M, z * m * z⁻¹ ∈ M)
    (hinv : ∀ x ∈ M, z * x * z⁻¹ * x ∈ Subgroup.zpowers σ)
    (hTV : ∀ y ∈ M, τ * y * τ⁻¹ * y⁻¹ ∈ Subgroup.zpowers σ) :
    ∀ y ∈ M, τ * y = y * τ := by
  intro y hy
  have hzzc : ∀ d ∈ Subgroup.zpowers σ, z * d * z⁻¹ = d := fun d hd =>
    conj_of_commute_zpowers hzσ hd
  have hτc : ∀ d ∈ Subgroup.zpowers σ, τ * d * τ⁻¹ = d := fun d hd =>
    conj_of_commute_zpowers hστ.symm hd
  obtain ⟨c, hc_def⟩ : ∃ c, c = τ * y * τ⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hc : c ∈ Subgroup.zpowers σ := by rw [hc_def]; exact hTV y hy
  obtain ⟨y', hy'_def⟩ : ∃ y', y' = z * y * z⁻¹ := ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ s, s = y' * y := ⟨_, rfl⟩
  have hs : s ∈ Subgroup.zpowers σ := by rw [hs_def, hy'_def]; exact hinv y hy
  have hy'eq : y' = s * y⁻¹ := by rw [hs_def]; group
  have hτzconj : ∀ a : G, τ * (z * a * z⁻¹) * τ⁻¹ = z * (τ * a * τ⁻¹) * z⁻¹ := by
    intro a
    have hcomm : z * τ = τ * z := hzτ
    calc τ * (z * a * z⁻¹) * τ⁻¹ = (τ * z) * a * (τ * z)⁻¹ := by group
      _ = (z * τ) * a * (z * τ)⁻¹ := by rw [hcomm]
      _ = z * (τ * a * τ⁻¹) * z⁻¹ := by group
  have hc1 : τ * y' * τ⁻¹ * y'⁻¹ = c := by
    calc τ * y' * τ⁻¹ * y'⁻¹ = (τ * y' * τ⁻¹) * y'⁻¹ := by group
      _ = (z * (τ * y * τ⁻¹) * z⁻¹) * (z * y⁻¹ * z⁻¹) := by
          rw [hy'_def, hτzconj]; group
      _ = z * (τ * y * τ⁻¹ * y⁻¹) * z⁻¹ := by group
      _ = z * c * z⁻¹ := by rw [hc_def]
      _ = c := hzzc c hc
  have hτy : τ * y * τ⁻¹ = c * y := by rw [hc_def]; group
  have hτyinv : τ * y⁻¹ * τ⁻¹ = y⁻¹ * c⁻¹ := by
    calc τ * y⁻¹ * τ⁻¹ = (τ * y * τ⁻¹)⁻¹ := by group
      _ = (c * y)⁻¹ := by rw [hτy]
      _ = y⁻¹ * c⁻¹ := by group
  have hcy : c⁻¹ * y = y * c⁻¹ := zpowers_central hσc c⁻¹ (Subgroup.inv_mem _ hc) y hy
  have hX : τ * y⁻¹ * τ⁻¹ * y = c⁻¹ := by
    rw [hτyinv]
    calc y⁻¹ * c⁻¹ * y = y⁻¹ * (c⁻¹ * y) := by group
      _ = y⁻¹ * (y * c⁻¹) := by rw [hcy]
      _ = c⁻¹ := by group
  have hc2 : τ * y' * τ⁻¹ * y'⁻¹ = c⁻¹ := by
    rw [hy'eq]
    calc τ * (s * y⁻¹) * τ⁻¹ * (s * y⁻¹)⁻¹ = s * (τ * y⁻¹ * τ⁻¹ * y) * s⁻¹ := by
          calc τ * (s * y⁻¹) * τ⁻¹ * (s * y⁻¹)⁻¹ = (τ * s * τ⁻¹) * (τ * y⁻¹ * τ⁻¹) * (y * s⁻¹) := by
                group
            _ = s * (τ * y⁻¹ * τ⁻¹) * (y * s⁻¹) := by rw [hτc s hs]
            _ = s * (τ * y⁻¹ * τ⁻¹ * y) * s⁻¹ := by group
      _ = s * c⁻¹ * s⁻¹ := by rw [hX]
      _ = c⁻¹ := by
          rw [zpowers_comm_zpowers hs (Subgroup.inv_mem _ hc)]
          group
  have hcc : c * c = 1 := by
    have hceq : c = c⁻¹ := hc1.symm.trans hc2
    exact mul_eq_one_iff_eq_inv.mpr hceq
  have hc1' : c = 1 := eq_one_of_sq_cube hcc (cube_of_mem_zpowers hσ3 hc)
  calc τ * y = (τ * y * τ⁻¹ * y⁻¹) * y * τ := by group
    _ = y * τ := by rw [← hc_def, hc1']; group


theorem center_le_zpowers [Finite G] {M : Subgroup G} (hM : Nat.card ↥M = 27) {σ : G}
    (hσM : σ ∈ M) (hσc : ∀ m ∈ M, σ * m = m * σ) (hσ3 : orderOf σ = 3)
    (hnon : ∃ x ∈ M, ∃ y ∈ M, x * y ≠ y * x) :
    ∀ g ∈ M, (∀ a ∈ M, a * g = g * a) → g ∈ Subgroup.zpowers σ := by
  intro g hgM hg
  by_contra hgσ
  obtain ⟨x0, hx0, y0, hy0, hxy0⟩ := hnon
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup ↥M, Z = Subgroup.center ↥M := ⟨_, rfl⟩
  haveI hZn : Z.Normal := by rw [hZ]; exact inferInstance
  have hσZ : (⟨σ, hσM⟩ : ↥M) ∈ Z := by
    rw [hZ, Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (hσc h.1 h.2).symm
  have hgZ : (⟨g, hgM⟩ : ↥M) ∈ Z := by
    rw [hZ, Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (hg h.1 h.2)
  have hord : orderOf (⟨σ, hσM⟩ : ↥M) = 3 := by
    rw [Subgroup.orderOf_mk]; exact hσ3
  have h3Z : 3 ∣ Nat.card Z := by
    have h := orderOf_dvd_natCard (⟨(⟨σ, hσM⟩ : ↥M), hσZ⟩ : Z)
    rwa [Subgroup.orderOf_mk, hord] at h
  have hZdvd : Nat.card Z ∣ 3 ^ 3 := by
    have := Subgroup.card_subgroup_dvd_card Z
    rw [hM] at this
    norm_num
    exact this
  obtain ⟨i, hi, hZi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hZdvd
  interval_cases i
  · rw [pow_zero] at hZi
    rw [hZi] at h3Z
    norm_num at h3Z
  · rw [pow_one] at hZi
    have hle : Subgroup.zpowers (⟨σ, hσM⟩ : ↥M) ≤ Z := Subgroup.zpowers_le.mpr hσZ
    have heq : Subgroup.zpowers (⟨σ, hσM⟩ : ↥M) = Z :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, hZi])
    have hg'Z : (⟨g, hgM⟩ : ↥M) ∈ Z := hgZ
    rw [← heq] at hg'Z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg'Z
    apply hgσ
    have hk' := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at hk'
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hk'⟩
  · have hidx := Subgroup.index_mul_card Z
    rw [hZi, hM] at hidx
    have hq : Nat.card (↥M ⧸ Z) = 3 := by
      rw [← Subgroup.index_eq_card]; omega
    haveI : IsCyclic (↥M ⧸ Z) := isCyclic_of_prime_card hq
    have hker : (QuotientGroup.mk' Z).ker ≤ Subgroup.center ↥M := by
      rw [QuotientGroup.ker_mk', hZ]
    have hcomm : ∀ a b : ↥M, a * b = b * a := fun a b =>
      (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' Z) hker).is_comm.comm a b
    exact hxy0 (congrArg Subtype.val (hcomm ⟨x0, hx0⟩ ⟨y0, hy0⟩))
  · have hZtop : Z = ⊤ := Subgroup.eq_top_of_card_eq Z (by rw [hZi, hM]; norm_num)
    have hmem : (⟨x0, hx0⟩ : ↥M) ∈ Subgroup.center ↥M := by
      rw [← hZ, hZtop]; exact Subgroup.mem_top _
    have hc := Subgroup.mem_center_iff.mp hmem ⟨y0, hy0⟩
    exact hxy0 (congrArg Subtype.val hc).symm

theorem sq_comm_of_conj {σ x : G} (hσo : orderOf σ = 3) (hx : x * σ * x⁻¹ ∈ Subgroup.zpowers σ) :
    x ^ 2 * σ = σ * x ^ 2 := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hj0 : j % 3 ≠ 0 := by
    intro h0
    have h1 : σ ^ j = 1 := by rw [zpow_three_mod hσo j, h0, zpow_zero]
    rw [h1] at hj
    have hσ1 : σ = 1 := by
      have h2 : x * σ * x⁻¹ = 1 := hj.symm
      simpa using h2
    rw [hσ1, orderOf_one] at hσo
    norm_num at hσo
  have hjj : (j * j) % 3 = 1 := by
    rcases (by omega : j % 3 = 1 ∨ j % 3 = 2) with h | h <;> simp [Int.mul_emod, h]
  have hx2 : x ^ 2 * σ * (x ^ 2)⁻¹ = σ := by
    calc x ^ 2 * σ * (x ^ 2)⁻¹ = x * (x * σ * x⁻¹) * x⁻¹ := by
          simp only [pow_two, mul_inv_rev]; group
      _ = x * σ ^ j * x⁻¹ := by rw [hj]
      _ = (x * σ * x⁻¹) ^ j := (conj_zpow (i := j) (a := x) (b := σ)).symm
      _ = (σ ^ j) ^ j := by rw [hj]
      _ = σ ^ (j * j) := (zpow_mul σ j j).symm
      _ = σ := by rw [zpow_three_mod hσo (j * j), hjj, zpow_one]
  calc x ^ 2 * σ = x ^ 2 * σ * (x ^ 2)⁻¹ * x ^ 2 := by group
    _ = σ * x ^ 2 := by rw [hx2]

theorem no_tau_centralizer [Finite G] {M : Subgroup G} (hM : Nat.card ↥M = 27) {σ τ z : G}
    (hσo : orderOf σ = 3) (hσM : σ ∈ M) (hστ : σ * τ = τ * σ) (hzσ : z * σ = σ * z)
    (hzτ : z * τ = τ * z) (hz2 : z * z = 1) (hσc : ∀ m ∈ M, σ * m = m * σ)
    (hzM : ∀ m ∈ M, z * m * z⁻¹ ∈ M)
    (hinv : ∀ x ∈ M, z * x * z⁻¹ * x ∈ Subgroup.zpowers σ)
    (hMC : Nat.card ↥(M ⊓ Subgroup.centralizer ({τ} : Set G)) = 9) {m : G} (hm : m ∈ M)
    (hc : ∀ a ∈ M, m * τ * a = a * (m * τ)) : False := by
  have hσ3 : σ ^ 3 = 1 := by rw [← hσo]; exact pow_orderOf_eq_one σ
  have hT : ∀ y ∈ M, τ * y * τ⁻¹ * y⁻¹ ∈ Subgroup.zpowers σ := by
    intro y hy
    have hm' : m⁻¹ ∈ M := M.inv_mem hm
    have e : τ * y * τ⁻¹ * y⁻¹ = m⁻¹ * y * m⁻¹⁻¹ * y⁻¹ := by
      have h1 : τ * y = m⁻¹ * y * m * τ := by
        calc τ * y = m⁻¹ * (m * τ * y) := by group
          _ = m⁻¹ * (y * (m * τ)) := by rw [hc y hy]
          _ = m⁻¹ * y * m * τ := by group
      calc τ * y * τ⁻¹ * y⁻¹ = m⁻¹ * y * m * τ * τ⁻¹ * y⁻¹ := by rw [h1]
        _ = m⁻¹ * y * m * y⁻¹ := by group
        _ = m⁻¹ * y * m⁻¹⁻¹ * y⁻¹ := by group
    rw [e]
    exact comm_mod_zpowers hM hσM hσc hσo m⁻¹ hm' y hy
  have hcomm := centralize_of_trivial hσ3 hστ hzσ hzτ hz2 hσc hzM hinv hT
  have hMeq : M ⊓ Subgroup.centralizer ({τ} : Set G) = M := by
    refine inf_eq_left.mpr (fun y hy => Subgroup.mem_centralizer_iff.mpr ?_)
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hcomm y hy
  rw [hMeq, hM] at hMC
  norm_num at hMC

theorem center_sup_le [Finite G] {M : Subgroup G} (hM : Nat.card ↥M = 27) {σ τ z : G}
    (hσo : orderOf σ = 3) (hτo : orderOf τ = 3) (hσM : σ ∈ M) (hσc : ∀ m ∈ M, σ * m = m * σ)
    (hστ : σ * τ = τ * σ) (hzσ : z * σ = σ * z) (hzτ : z * τ = τ * z) (hz2 : z * z = 1)
    (hzM : ∀ m ∈ M, z * m * z⁻¹ ∈ M)
    (hinv : ∀ x ∈ M, z * x * z⁻¹ * x ∈ Subgroup.zpowers σ)
    (hτN : τ ∈ Subgroup.normalizer (M : Set G))
    (hMC : Nat.card ↥(M ⊓ Subgroup.centralizer ({τ} : Set G)) = 9)
    (hnon : ∃ x ∈ M, ∃ y ∈ M, x * y ≠ y * x) :
    ∀ g ∈ M ⊔ Subgroup.zpowers τ, (∀ a ∈ M, a * g = g * a) → g ∈ Subgroup.zpowers σ := by
  intro g hg hcomm
  have hτ3 : τ ^ 3 = 1 := by rw [← hτo]; exact pow_orderOf_eq_one τ
  have hτM : ∀ m ∈ M, τ * m * τ⁻¹ ∈ M := fun m hm => (Subgroup.mem_normalizer_iff.mp hτN m).mp hm
  have hBn : ∀ b ∈ Subgroup.zpowers τ, ∀ a ∈ M, b * a * b⁻¹ ∈ M := fun b hb a ha =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr hτN hb) a).mp ha
  obtain ⟨m, hm, b, hb, rfl⟩ := (mem_sup_iff_of_normalizes hBn).mp hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hk := zpow_three_mod hτo k
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · have h1 : τ ^ k = 1 := by rw [hk, h, zpow_zero]
    rw [h1, mul_one] at hcomm ⊢
    exact center_le_zpowers hM hσM hσc hσo hnon m hm hcomm
  · have h1 : τ ^ k = τ := by rw [hk, h, zpow_one]
    rw [h1] at hcomm
    exact (no_tau_centralizer hM hσo hσM hστ hzσ hzτ hz2 hσc hzM hinv hMC hm
      (fun a ha => (hcomm a ha).symm)).elim
  · have h1 : τ ^ k = τ ^ 2 := by rw [hk, h, zpow_ofNat]
    rw [h1] at hcomm
    have hτ2 : (τ ^ 2)⁻¹ = τ := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ]; exact hτ3
    have hinvg : (m * τ ^ 2)⁻¹ = (τ * m⁻¹ * τ⁻¹) * τ := by
      rw [mul_inv_rev, hτ2]; group
    have hm' : τ * m⁻¹ * τ⁻¹ ∈ M := hτM m⁻¹ (M.inv_mem hm)
    refine (no_tau_centralizer hM hσo hσM hστ hzσ hzτ hz2 hσc hzM hinv hMC hm' ?_).elim
    intro a ha
    have hcom : Commute a (m * τ ^ 2) := hcomm a ha
    have h2 := hcom.inv_right.eq
    rw [hinvg] at h2
    exact h2.symm

theorem not_pow5_dvd [Finite G] {A : Subgroup G} {σ : G} (hA : Nat.card ↥A = 81)
    (hσo : orderOf σ = 3)
    (hσN : ∀ x ∈ Subgroup.normalizer (A : Set G), x * σ * x⁻¹ ∈ Subgroup.zpowers σ)
    (hC : Nat.card ↥(Subgroup.centralizer ({σ} : Set G)) = 648) :
    ¬ 3 ^ 5 ∣ Nat.card G := by
  intro h5
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA' : Nat.card ↥A = 3 ^ 4 := by rw [hA]; norm_num
  have hdvd : 3 ^ 5 ∣ Nat.card ↥(Subgroup.normalizer (A : Set G)) :=
    Sylow.prime_pow_dvd_card_normalizer (n := 4) h5 hA'
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  set K : Subgroup G := K'.map (Subgroup.normalizer (A : Set G)).subtype with hKdef
  have hKc : Nat.card ↥K = 3 ^ 5 := by
    rw [hKdef, Subgroup.card_map_of_injective Subtype.val_injective]
    exact hK'
  have hKle : K ≤ Subgroup.centralizer ({σ} : Set G) := by
    intro k hk
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
    have hσk := hσN (k' : G) k'.2
    have hsq := sq_comm_of_conj hσo hσk
    have hpow : (k' : G) ^ (3 ^ 5) = 1 := by
      have h : (⟨k', hk'⟩ : ↥K') ^ (3 ^ 5) = 1 := by
        rw [← hK']; exact pow_card_eq_one'
      have h2 : (k' : ↥(Subgroup.normalizer (A : Set G))) ^ (3 ^ 5) = 1 := by
        have := congrArg Subtype.val h
        rw [Subgroup.coe_pow, Subgroup.coe_one] at this
        exact this
      have h3 := congrArg Subtype.val h2
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h3
      exact h3
    have hk244 : (k' : G) ^ 244 = (k' : G) := by
      rw [show (244 : ℕ) = 3 ^ 5 + 1 from by norm_num, pow_succ, hpow, one_mul]
    have hkk : (k' : G) = ((k' : G) ^ 2) ^ 122 := by
      rw [← pow_mul, show 2 * 122 = 244 by norm_num, hk244]
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hcom2 : Commute ((k' : G) ^ 2) σ := hsq
    have hcom3 : Commute (((k' : G) ^ 2) ^ 122) σ := hcom2.pow_left 122
    rw [← hkk] at hcom3
    exact hcom3.eq.symm
  have hd := Subgroup.card_dvd_of_le hKle
  rw [hKc, hC] at hd
  norm_num at hd


theorem inf_zpowers_eq_bot [Finite G] {M : Subgroup G} {τ : G} (hτo : orderOf τ = 3) (hτM : τ ∉ M) :
    M ⊓ Subgroup.zpowers τ = ⊥ := by
  have hle : M ⊓ Subgroup.zpowers τ ≤ Subgroup.zpowers τ := inf_le_right
  have hd := Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers, hτo] at hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have heq : M ⊓ Subgroup.zpowers τ = Subgroup.zpowers τ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hτo, h3])
    have hτX : τ ∈ M ⊓ Subgroup.zpowers τ := by
      rw [heq]; exact Subgroup.mem_zpowers τ
    exact hτM (Subgroup.mem_inf.mp hτX).1

theorem vertex_comm [Finite G] {σ τ z t : G} {M N : Subgroup G}
    (hM : Nat.card ↥M = 27) (hσo : orderOf σ = 3) (hσM : σ ∈ M)
    (hσc : ∀ m ∈ M, σ * m = m * σ)
    (hτN : τ ∈ Subgroup.normalizer (M : Set G)) (hτM : τ ∉ M)
    (hMτC : Nat.card ↥(M ⊓ Subgroup.centralizer ({τ} : Set G)) = 9)
    (hMz : ∀ m ∈ M, z * m = m * z → m ∈ Subgroup.zpowers σ)
    (hzM : ∀ m ∈ M, z * m * z⁻¹ ∈ M)
    (hCσ : Nat.card ↥(Subgroup.centralizer ({σ} : Set G)) = 648)
    (hN : Nat.card ↥N = 27) (hτN_mem : τ ∈ N) (hNτ : ∀ n ∈ N, τ * n = n * τ)
    (hσN : σ ∈ Subgroup.normalizer (N : Set G)) (hσN' : σ ∉ N)
    (hτo : orderOf τ = 3) (hστ : σ * τ = τ * σ) (hzσ : z * σ = σ * z) (hzτ : z * τ = τ * z)
    (hz2 : z * z = 1) (htσ : t * σ * t⁻¹ = σ⁻¹) (hfour : ¬ IsConj σ τ) :
    ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0, y0, hy0, hxy0⟩ := hcon
  have hnon : ∃ x ∈ M, ∃ y ∈ M, x * y ≠ y * x := ⟨x0, hx0, y0, hy0, hxy0⟩
  have hinv := inv_mod_of_involution hM hσM hσc hσo hz2 hzσ hzM hMz
  have hZ := center_sup_le hM hσo hτo hσM hσc hστ hzσ hzτ hz2 hzM hinv hτN hMτC hnon
  have hτzp : ∀ b ∈ Subgroup.zpowers τ, ∀ a ∈ M, b * a * b⁻¹ ∈ M := fun b hb a ha =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr hτN hb) a).mp ha
  have hσzp : ∀ b ∈ Subgroup.zpowers σ, ∀ n ∈ N, b * n * b⁻¹ ∈ N := fun b hb n hn =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr hσN hb) n).mp hn
  have hdisj := inf_zpowers_eq_bot hτo hτM
  have hdisjN : N ⊓ Subgroup.zpowers σ = ⊥ := by
    exact inf_zpowers_eq_bot hσo hσN'
  have hA : Nat.card ↥(M ⊔ Subgroup.zpowers τ) = 81 := by
    rw [card_sup_of_normalizes hτzp hdisj, hM, Nat.card_zpowers, hτo]
  have hB : Nat.card ↥(N ⊔ Subgroup.zpowers σ) = 81 := by
    rw [card_sup_of_normalizes hσzp hdisjN, hN, Nat.card_zpowers, hσo]
  have hστz : ∀ b ∈ Subgroup.zpowers τ, σ * b = b * σ := fun b hb => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_right (show Commute σ τ from hστ) k)).eq
  have hσ𝔐 : ∀ a ∈ M ⊔ Subgroup.zpowers τ, σ * a = a * σ := by
    intro a ha
    obtain ⟨m, hm, b, hb, rfl⟩ := (mem_sup_iff_of_normalizes hτzp).mp ha
    rw [← mul_assoc, hσc m hm, mul_assoc, hστz b hb, mul_assoc]
  have hNorm : ∀ x ∈ Subgroup.normalizer ((M ⊔ Subgroup.zpowers τ : Subgroup G) : Set G),
      x * σ * x⁻¹ ∈ Subgroup.zpowers σ := by
    intro x hx
    have hσ𝔐' : σ ∈ M ⊔ Subgroup.zpowers τ := Subgroup.mem_sup_left hσM
    have hw : x * σ * x⁻¹ ∈ M ⊔ Subgroup.zpowers τ := (Subgroup.mem_normalizer_iff.mp hx σ).mp hσ𝔐'
    refine hZ _ hw (fun a ha => ?_)
    have hconj : x⁻¹ * a * x ∈ M ⊔ Subgroup.zpowers τ := by
      refine (Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * a * x)).mpr ?_
      have e : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
      rw [e]
      exact Subgroup.mem_sup_left ha
    have hcs := hσ𝔐 _ hconj
    calc a * (x * σ * x⁻¹) = x * ((x⁻¹ * a * x) * σ) * x⁻¹ := by group
      _ = x * (σ * (x⁻¹ * a * x)) * x⁻¹ := by rw [← hcs]
      _ = x * σ * x⁻¹ * a := by group
  have h5 : ¬ 3 ^ 5 ∣ Nat.card G := not_pow5_dvd hA hσo hNorm hCσ
  have hP2 : ¬ 3 ∣ (M ⊔ Subgroup.zpowers τ).index := by
    intro h3
    apply h5
    have hidx := Subgroup.index_mul_card (M ⊔ Subgroup.zpowers τ)
    rw [hA] at hidx
    rw [← hidx]
    have h35 : (3 : ℕ) ^ 5 = 3 * 81 := by norm_num
    rw [h35]
    exact Nat.mul_dvd_mul_right h3 81
  have hQ2 : ¬ 3 ∣ (N ⊔ Subgroup.zpowers σ).index := by
    intro h3
    apply h5
    have hidx := Subgroup.index_mul_card (N ⊔ Subgroup.zpowers σ)
    rw [hB] at hidx
    rw [← hidx]
    have h35 : (3 : ℕ) ^ 5 = 3 * 81 := by norm_num
    rw [h35]
    exact Nat.mul_dvd_mul_right h3 81
  have hA' : Nat.card ↥(M ⊔ Subgroup.zpowers τ) = 3 ^ 4 := by rw [hA]; norm_num
  have hB' : Nat.card ↥(N ⊔ Subgroup.zpowers σ) = 3 ^ 4 := by rw [hB]; norm_num
  obtain ⟨P, hPdef⟩ : ∃ P : Sylow 3 G, P = (IsPGroup.of_card hA').toSylow hP2 := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Sylow 3 G, Q = (IsPGroup.of_card hB').toSylow hQ2 := ⟨_, rfl⟩
  have hPcoe : (P : Subgroup G) = M ⊔ Subgroup.zpowers τ := by
    rw [hPdef]; exact IsPGroup.toSylow_coe _ _
  have hQcoe : (Q : Subgroup G) = N ⊔ Subgroup.zpowers σ := by
    rw [hQdef]; exact IsPGroup.toSylow_coe _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hgset : (Q : Set G) = MulAut.conj g • (P : Set G) := by
    rw [← hg]; exact Sylow.coe_smul
  have hPmem : ∀ x, x ∈ (P : Subgroup G) ↔ x ∈ M ⊔ Subgroup.zpowers τ := fun x => by
    rw [hPcoe]
  have hQmem : ∀ x, x ∈ (Q : Subgroup G) ↔ x ∈ N ⊔ Subgroup.zpowers σ := fun x => by
    rw [hQcoe]
  have hsmul : ∀ x ∈ M ⊔ Subgroup.zpowers τ, g * x * g⁻¹ ∈ N ⊔ Subgroup.zpowers σ := by
    intro x hx
    have hxP : x ∈ (P : Set G) := (hPmem x).mpr hx
    have h1 : MulAut.conj g x ∈ MulAut.conj g • (P : Set G) := Set.smul_mem_smul_set hxP
    rw [← hgset] at h1
    have h2 : MulAut.conj g x ∈ (Q : Subgroup G) := h1
    rw [hQmem] at h2
    simpa [MulAut.conj_apply] using h2
  have hsmul' : ∀ x ∈ N ⊔ Subgroup.zpowers σ, g⁻¹ * x * g ∈ M ⊔ Subgroup.zpowers τ := by
    intro x hx
    have hx' : x ∈ (Q : Set G) := (hQmem x).mpr hx
    rw [hgset] at hx'
    obtain ⟨y, hy, hyx⟩ := Set.mem_smul_set.mp hx'
    have hy' : y ∈ M ⊔ Subgroup.zpowers τ := (hPmem y).mp hy
    have hxy : g⁻¹ * x * g = y := by
      rw [← hyx, MulAut.smul_def, MulAut.conj_apply]
      group
    rw [hxy]; exact hy'
  have hτb : ∀ b ∈ Subgroup.zpowers σ, τ * b = b * τ := fun b hb => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute τ σ from hστ.symm) k).eq
  have hτcent : ∀ n ∈ N ⊔ Subgroup.zpowers σ, τ * n = n * τ := by
    intro n hn
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_normalizes hσzp).mp hn
    rw [← mul_assoc, hNτ a ha, mul_assoc, hτb b hb, mul_assoc]
  have hτ𝔑 : τ ∈ N ⊔ Subgroup.zpowers σ := Subgroup.mem_sup_left hτN_mem
  obtain ⟨w, hw_def⟩ : ∃ w, w = g⁻¹ * τ * g := ⟨_, rfl⟩
  have hw𝔐 : w ∈ M ⊔ Subgroup.zpowers τ := by rw [hw_def]; exact hsmul' τ hτ𝔑
  have hwcomm : ∀ a ∈ M, a * w = w * a := by
    intro a ha
    have hga : g * a * g⁻¹ ∈ N ⊔ Subgroup.zpowers σ := hsmul a (Subgroup.mem_sup_left ha)
    have hcen : τ * (g * a * g⁻¹) = (g * a * g⁻¹) * τ := hτcent _ hga
    calc a * w = g⁻¹ * ((g * a * g⁻¹) * τ) * g := by rw [hw_def]; group
      _ = g⁻¹ * (τ * (g * a * g⁻¹)) * g := by rw [hcen]
      _ = w * a := by rw [hw_def]; group
  have hwz : w ∈ Subgroup.zpowers σ := hZ w hw𝔐 hwcomm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwz
  have hk3 := zpow_three_mod hσo k
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hτo
    norm_num at hτo
  have hσ3' : σ ^ 3 = 1 := by rw [← hσo]; exact pow_orderOf_eq_one σ
  have hσ2 : σ ^ 2 = σ⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact hσ3'
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
  · exfalso
    apply hτ1
    have hw1 : w = 1 := by rw [← hk, hk3, h0, zpow_zero]
    calc τ = g * (g⁻¹ * τ * g) * g⁻¹ := by group
      _ = 1 := by rw [← hw_def, hw1]; group
  · apply hfour
    rw [isConj_iff]
    refine ⟨g, ?_⟩
    have hσk : σ = w := by rw [← hk, hk3, h1, zpow_one]
    calc g * σ * g⁻¹ = g * w * g⁻¹ := by rw [← hσk]
      _ = τ := by rw [hw_def]; group
  · apply hfour
    rw [isConj_iff]
    refine ⟨g * t, ?_⟩
    have hσinv : σ⁻¹ = w := by rw [← hσ2, ← hk, hk3, h2, zpow_ofNat]
    calc (g * t) * σ * (g * t)⁻¹ = g * (t * σ * t⁻¹) * g⁻¹ := by group
      _ = g * σ⁻¹ * g⁻¹ := by rw [htσ]
      _ = g * w * g⁻¹ := by rw [hσinv]
      _ = τ := by rw [hw_def]; group


theorem cube_eq_one_of_card_three {H : Subgroup G} [Finite G] (hH : Nat.card ↥H = 3) {y : G}
    (hy : y ∈ H) : y ^ 3 = 1 := by
  have h := orderOf_dvd_natCard (⟨y, hy⟩ : ↥H)
  rw [hH] at h
  have h' : (⟨y, hy⟩ : ↥H) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp h
  have h'' := congrArg Subtype.val h'
  simpa using h''

theorem cube_one_of_comm [Finite G] {σ z t : G} {M : Subgroup G} (hM : Nat.card ↥M = 27)
    (hσo : orderOf σ = 3) (hσM : σ ∈ M) (hσc : ∀ m ∈ M, σ * m = m * σ)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (hzσ : z * σ = σ * z) (hz2 : z * z = 1) (ht2 : t * t = 1) (htσ : t * σ * t⁻¹ = σ⁻¹)
    (hzt : z * t = t * z)
    (hzM : ∀ m ∈ M, z * m * z⁻¹ ∈ M) (htM : ∀ m ∈ M, t * m * t⁻¹ ∈ M)
    (hMz : ∀ m ∈ M, z * m = m * z → m ∈ Subgroup.zpowers σ)
    (hMCt : Nat.card ↥(M ⊓ Subgroup.centralizer ({t} : Set G)) = 3)
    (hMCtz : Nat.card ↥(M ⊓ Subgroup.centralizer ({t * z} : Set G)) = 3) :
    ∀ x ∈ M, x ^ 3 = 1 := by
  intro x hx
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hinv := inv_mod_of_involution hM hσM hσc hσo hz2 hzσ hzM hMz
  have hσ3 : σ ^ 3 = 1 := by rw [← hσo]; exact pow_orderOf_eq_one σ
  have htpow : ∀ k : ℤ, t * σ ^ k * t⁻¹ = σ ^ (-k) := fun k => by
    rw [← conj_zpow, htσ, inv_zpow, zpow_neg]
  have hzpow : ∀ k : ℤ, z * σ ^ k * z⁻¹ = σ ^ k := fun k =>
    conj_of_commute_zpowers hzσ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers σ) k)
  have hσk : ∀ k : ℤ, σ ^ k ∈ M := fun k => M.zpow_mem hσM k
  obtain ⟨p, hp_def⟩ : ∃ p, p = t * x * t⁻¹ := ⟨_, rfl⟩
  have hpM : p ∈ M := by rw [hp_def]; exact htM x hx
  have htp : t * p * t⁻¹ = x := by
    rw [hp_def]
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
      _ = x := by rw [ht2, ht_inv, ht2, mul_one, one_mul]
  have hx1M : x * p ∈ M := M.mul_mem hx hpM
  have hx1C : t * (x * p) * t⁻¹ = x * p := by
    calc t * (x * p) * t⁻¹ = (t * x * t⁻¹) * (t * p * t⁻¹) := by group
      _ = p * x := by rw [← hp_def, htp]
      _ = x * p := hcomm p hpM x hx
  have hx1 : x * p ∈ M ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hx1M, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact mul_inv_eq_iff_eq_mul.mp hx1C
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hinv x hx)
  have hzx : z * x * z⁻¹ = σ ^ a * x⁻¹ := by
    calc z * x * z⁻¹ = (z * x * z⁻¹ * x) * x⁻¹ := by group
      _ = σ ^ a * x⁻¹ := by rw [ha]
  have hzp : z * p * z⁻¹ = σ ^ (-a) * p⁻¹ := by
    calc z * p * z⁻¹ = z * (t * x * t⁻¹) * z⁻¹ := by rw [hp_def]
      _ = (z * t) * x * (z * t)⁻¹ := by group
      _ = (t * z) * x * (t * z)⁻¹ := by rw [hzt]
      _ = t * (z * x * z⁻¹) * t⁻¹ := by group
      _ = t * (σ ^ a * x⁻¹) * t⁻¹ := by rw [hzx]
      _ = (t * σ ^ a * t⁻¹) * (t * x⁻¹ * t⁻¹) := by group
      _ = σ ^ (-a) * p⁻¹ := by rw [htpow a, hp_def]; group
  have hqM : x * p⁻¹ ∈ M := M.mul_mem hx (M.inv_mem hpM)
  have hzq : z * (x * p⁻¹) * z⁻¹ = σ ^ a * (x⁻¹ * p) * σ ^ a := by
    calc z * (x * p⁻¹) * z⁻¹ = (z * x * z⁻¹) * (z * p⁻¹ * z⁻¹) := by group
      _ = (σ ^ a * x⁻¹) * (p * σ ^ a) := by
          rw [hzx]
          congr 1
          calc z * p⁻¹ * z⁻¹ = (z * p * z⁻¹)⁻¹ := by group
            _ = (σ ^ (-a) * p⁻¹)⁻¹ := by rw [hzp]
            _ = p * σ ^ a := by group
      _ = σ ^ a * (x⁻¹ * p) * σ ^ a := by group
  have hqtz : (t * z) * (x * p⁻¹) * (t * z)⁻¹ = σ ^ (-a) * (x * p⁻¹) * σ ^ (-a) := by
    have hxp : t * (x⁻¹ * p) * t⁻¹ = p⁻¹ * x := by
      calc t * (x⁻¹ * p) * t⁻¹ = (t * x⁻¹ * t⁻¹) * (t * p * t⁻¹) := by group
        _ = p⁻¹ * x := by rw [htp, hp_def]; group
    calc (t * z) * (x * p⁻¹) * (t * z)⁻¹ = t * (z * (x * p⁻¹) * z⁻¹) * t⁻¹ := by group
      _ = t * (σ ^ a * (x⁻¹ * p) * σ ^ a) * t⁻¹ := by rw [hzq]
      _ = (t * σ ^ a * t⁻¹) * (t * (x⁻¹ * p) * t⁻¹) * (t * σ ^ a * t⁻¹) := by group
      _ = σ ^ (-a) * (p⁻¹ * x) * σ ^ (-a) := by rw [htpow a, hxp]
      _ = σ ^ (-a) * (x * p⁻¹) * σ ^ (-a) := by rw [hcomm p⁻¹ (M.inv_mem hpM) x hx]
  obtain ⟨r, hr_def⟩ : ∃ r, r = (x * p⁻¹) * σ ^ (-a) := ⟨_, rfl⟩
  have hrM : r ∈ M := by rw [hr_def]; exact M.mul_mem hqM (hσk _)
  have hrC : (t * z) * r * (t * z)⁻¹ = r := by
    have hσa : (t * z) * σ ^ (-a) * (t * z)⁻¹ = σ ^ a := by
      calc (t * z) * σ ^ (-a) * (t * z)⁻¹ = t * (z * σ ^ (-a) * z⁻¹) * t⁻¹ := by group
        _ = t * σ ^ (-a) * t⁻¹ := by rw [hzpow]
        _ = σ ^ a := by rw [htpow (-a), neg_neg]
    have hcq : σ ^ (-a) * (x * p⁻¹) = (x * p⁻¹) * σ ^ (-a) :=
      zpowers_central hσc (σ ^ (-a)) (Subgroup.mem_zpowers_iff.mpr ⟨-a, rfl⟩) (x * p⁻¹) hqM
    calc (t * z) * r * (t * z)⁻¹
        = ((t * z) * (x * p⁻¹) * (t * z)⁻¹) * ((t * z) * σ ^ (-a) * (t * z)⁻¹) := by
          rw [hr_def]; group
      _ = (σ ^ (-a) * (x * p⁻¹) * σ ^ (-a)) * σ ^ a := by rw [hqtz, hσa]
      _ = (σ ^ (-a) * (x * p⁻¹)) * σ ^ (-a) * σ ^ a := by group
      _ = ((x * p⁻¹) * σ ^ (-a)) * σ ^ (-a) * σ ^ a := by rw [hcq]
      _ = r := by rw [hr_def]; group
  have hrC' : r ∈ M ⊓ Subgroup.centralizer ({t * z} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hrM, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact mul_inv_eq_iff_eq_mul.mp hrC
  have hx2 : x ^ 2 = (x * p) * r * σ ^ a := by
    have hσσ : σ ^ (-a) * σ ^ a = 1 := by rw [← zpow_add]; simp
    rw [hr_def]
    calc x ^ 2 = x * (p * x) * p⁻¹ := by rw [hcomm p hpM x hx, pow_two]; group
      _ = (x * p) * (x * p⁻¹) * (σ ^ (-a) * σ ^ a) := by rw [hσσ, mul_one]; group
      _ = (x * p) * ((x * p⁻¹) * σ ^ (-a)) * σ ^ a := by group
  have hcube1 : (x * p) ^ 3 = 1 := cube_eq_one_of_card_three hMCt hx1
  have hcube_r : r ^ 3 = 1 := cube_eq_one_of_card_three hMCtz hrC'
  have hcube_s : (σ ^ a) ^ 3 = 1 := cube_of_mem_zpowers hσ3 (Subgroup.mem_zpowers_iff.mpr ⟨a, rfl⟩)
  have hx6 : x ^ 6 = 1 := by
    have hc1 : Commute (x * p) r := hcomm (x * p) hx1M r hrM
    have hc2 : Commute ((x * p) * r) (σ ^ a) := hcomm _ (M.mul_mem hx1M hrM) (σ ^ a) (hσk a)
    have h2 : (x ^ 2) ^ 3 = 1 := by
      rw [hx2, hc2.mul_pow, hc1.mul_pow, hcube1, hcube_r, hcube_s]; simp
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, h2]
  have h27 : x ^ 27 = 1 := by
    have h := pow_card_eq_one' (x := (⟨x, hx⟩ : ↥M))
    rw [hM] at h
    have h' := congrArg Subtype.val h
    simpa using h'
  calc x ^ 3 = (x ^ 6) ^ 4 * x ^ 3 := by rw [hx6, one_pow, one_mul]
    _ = x ^ 27 := by rw [← pow_mul, ← pow_add]
    _ = 1 := h27


theorem comm_of_word {a b : G} (h : a⁻¹ * b⁻¹ * a * b = 1) : a * b = b * a := by
  have h' : b⁻¹ * a * b = a := by
    calc b⁻¹ * a * b = a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = a := by rw [h, mul_one]
  calc a * b = b * (b⁻¹ * a * b) := by group
    _ = b * a := by rw [h']

theorem sq_eq_one_of_card_two {I : Subgroup G} [Finite G] (hI : Nat.card ↥I = 2) {w : G}
    (hw : w ∈ I) (hw1 : w ≠ 1) : w * w = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_dvd_natCard (⟨w, hw⟩ : ↥I)
  rw [hI, Subgroup.orderOf_mk] at h
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h2 | h2
  · exact absurd (orderOf_eq_one_iff.mp h2) hw1
  · have := pow_orderOf_eq_one w
    rw [h2] at this
    simpa [sq] using this

theorem exists_ne_one_of_card_two {I : Subgroup G} [Finite G] (hI : Nat.card ↥I = 2) :
    ∃ w ∈ I, w ≠ 1 := by
  have hnt : Nontrivial ↥I := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hI]; norm_num)
  obtain ⟨w, hw⟩ := exists_ne (1 : ↥I)
  exact ⟨w, w.2, fun h => hw (Subtype.ext h)⟩

theorem side_facts [Finite G] {H L X : Subgroup G} {e : Fin 6 → G} {x y : G}
    (v : VertexCore e H x L X) (hzH : ∀ g : G, g ∈ H ↔ zOf e * g = g * zOf e)
    (hxH : x ∈ H) (hyL : y ∈ L) (hy1 : y ≠ 1) (hxy : x * y = y * x)
    (hLc : Nat.card ↥L = 24) (hXc : Nat.card ↥X = 27)
    (hXy : Nat.card ↥(X ⊓ Subgroup.centralizer ({y} : Set G)) = 9) :
    x ∈ X ∧ (∀ m ∈ X, x * m = m * x) ∧ (∀ m ∈ X, zOf e * m * (zOf e)⁻¹ ∈ X) ∧
      (∀ m ∈ X, zOf e * m = m * zOf e → m ∈ Subgroup.zpowers x) ∧
      (∀ m ∈ X, e 4 * m * (e 4)⁻¹ ∈ X) ∧ y ∈ Subgroup.normalizer (X : Set G) ∧ y ∉ X ∧
      Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = 648 ∧
      Nat.card ↥(X ⊓ Subgroup.centralizer ({e 4} : Set G)) = 3 ∧
      Nat.card ↥(X ⊓ Subgroup.centralizer ({e 4 * zOf e} : Set G)) = 3 := by
  have hzx : zOf e * x = x * zOf e := (hzH x).mp hxH
  have hxX : x ∈ X := by
    have h : x ∈ X ⊓ H := by
      rw [v.inf_H]; exact Subgroup.mem_zpowers x
    exact (Subgroup.mem_inf.mp h).1
  have hXC : X ≤ Subgroup.centralizer ({x} : Set G) := v.compl.left_le
  have hxc : ∀ m ∈ X, x * m = m * x := by
    intro m hm
    have := Subgroup.mem_centralizer_iff.mp (hXC hm) x (Set.mem_singleton x)
    exact this
  have hzC : zOf e ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hzx.symm)
  have hyC : y ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hxy)
  have hLC : L ≤ Subgroup.centralizer ({x} : Set G) := v.compl.right_le
  have hzX : ∀ m ∈ X, zOf e * m * (zOf e)⁻¹ ∈ X := fun m hm => v.compl.conj_mem _ hzC m hm
  have hMz : ∀ m ∈ X, zOf e * m = m * zOf e → m ∈ Subgroup.zpowers x := by
    intro m hm hzm
    have hmH : m ∈ H := (hzH m).mpr hzm
    have h : m ∈ X ⊓ H := Subgroup.mem_inf.mpr ⟨hm, hmH⟩
    rw [v.inf_H] at h
    exact h
  have hyN : y ∈ Subgroup.normalizer (X : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr (fun m => ⟨fun hm => v.compl.conj_mem _ hyC m hm, fun hm => ?_⟩)
    have := v.compl.conj_mem _ (Subgroup.inv_mem _ hyC) _ hm
    have e1 : y⁻¹ * (y * m * y⁻¹) * y⁻¹⁻¹ = m := by group
    rw [e1] at this
    exact this
  have hyX : y ∉ X := by
    intro hyX
    have h : y ∈ X ⊓ L := Subgroup.mem_inf.mpr ⟨hyX, hyL⟩
    rw [v.compl.disjoint] at h
    exact hy1 (Subgroup.mem_bot.mp h)
  have hCx : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = 648 := by
    rw [← v.compl.sup_eq]
    have hLn : ∀ b ∈ L, ∀ a ∈ X, b * a * b⁻¹ ∈ X := fun b hb a ha =>
      v.compl.conj_mem b (hLC hb) a ha
    rw [card_sup_of_normalizes hLn v.compl.disjoint, hXc, hLc]
  have hcard_t : Nat.card ↥(X ⊓ Subgroup.centralizer ({e 4} : Set G)) = 3 := by
    have h := v.card_eq
    rw [hXc] at h
    have h9 : Nat.card ↥(X ⊓ Subgroup.centralizer ({e 4} : Set G)) ^ 2 = 3 * 3 := by
      omega
    have hc := Nat.pow_left_injective (n := 2) (by norm_num) (h9.trans (by norm_num : 3 * 3 = 3 ^ 2))
    exact hc
  refine ⟨hxX, hxc, hzX, hMz, fun m hm => v.conj_t m hm, hyN, hyX, hCx, hcard_t, ?_⟩
  rw [v.card_cent']
  exact hcard_t

end Generic

theorem leafB27Abelian : LeafB27Abelian := by
  intro G _ _ T H H₁ H₂ M e M₁ M₂ Pb Np Nm h hF _hO hL hPb
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hone : G23One H H₁ H₂ := h.ctx.one
  have hrel : SatisfiesWords g23WordsH e := h.lets.rels
  have hgen : Subgroup.closure (Set.range fun i : Fin 5 => e i.castSucc) = H := h.lets.gen
  have hgen₁ : Subgroup.closure ({e 0, e 1} : Set G) = H₁ := h.lets.gen₁
  have hgen₂ : Subgroup.closure ({e 2, e 3} : Set G) = H₂ := h.lets.gen₂
  have he0₁ : e 0 ∈ H₁ := by rw [← hgen₁]; exact Subgroup.subset_closure (by simp)
  have he1₁ : e 1 ∈ H₁ := by rw [← hgen₁]; exact Subgroup.subset_closure (by simp)
  have he2₂ : e 2 ∈ H₂ := by rw [← hgen₂]; exact Subgroup.subset_closure (by simp)
  have he3₂ : e 3 ∈ H₂ := by rw [← hgen₂]; exact Subgroup.subset_closure (by simp)
  have he4 : e 4 ∈ H := by rw [← hgen]; exact Subgroup.subset_closure ⟨4, rfl⟩
  have he0 : e 0 ∈ H := hone.le_one he0₁
  have he2 : e 2 ∈ H := hone.le_two he2₂
  have r0 : e 0 * e 0 * e 0 = 1 := by
    have h' := hrel [(0, true), (0, true), (0, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using h'
  have r3 : e 2 * e 2 * e 2 = 1 := by
    have h' := hrel [(2, true), (2, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using h'
  have r7 : (e 0)⁻¹ * (e 2)⁻¹ * e 0 * e 2 = 1 := by
    have h' := hrel [(0, false), (2, false), (0, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using h'
  have r6 : e 0 * e 1 * e 0 * e 1 * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹ = 1 := by
    have h' := hrel [(0, true), (1, true), (0, true), (1, true), (3, false), (2, false),
      (3, false), (2, false)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using h'
  have r11 : e 4 * e 4 = 1 := by
    have h' := hrel [(4, true), (4, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using h'
  have r12 : e 4 * e 0 * e 4 * e 0 = 1 := by
    have h' := hrel [(4, true), (0, true), (4, true), (0, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using h'
  have r14 : e 4 * e 2 * e 4 * e 2 = 1 := by
    have h' := hrel [(4, true), (2, true), (4, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using h'
  have hσ3 : e 0 ^ 3 = 1 := by rw [pow_three, ← mul_assoc]; exact r0
  have hτ3 : e 2 ^ 3 = 1 := by rw [pow_three, ← mul_assoc]; exact r3
  have hστ : e 0 * e 2 = e 2 * e 0 := comm_of_word r7
  have ht2 : e 4 * e 4 = 1 := r11
  have ht_inv : (e 4)⁻¹ = e 4 := inv_eq_of_mul_eq_one_right ht2
  have htσ : e 4 * e 0 * (e 4)⁻¹ = (e 0)⁻¹ := by
    rw [ht_inv]; exact eq_inv_of_mul_eq_one_left r12
  have htτ : e 4 * e 2 * (e 4)⁻¹ = (e 2)⁻¹ := by
    rw [ht_inv]; exact eq_inv_of_mul_eq_one_left r14
  have hzeq : zOf e = e 2 * e 3 * e 2 * e 3 := by
    have r6' : (e 0 * e 1 * e 0 * e 1) * ((e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹) = 1 := by
      simpa only [mul_assoc] using r6
    have hX := eq_inv_of_mul_eq_one_left r6'
    calc zOf e = e 0 * e 1 * e 0 * e 1 := by simp [zOf, sq, mul_assoc]
      _ = ((e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹)⁻¹ := hX
      _ = e 2 * e 3 * e 2 * e 3 := by group
  have hzH2 : zOf e ∈ H₂ := by
    rw [hzeq]; exact H₂.mul_mem (H₂.mul_mem (H₂.mul_mem he2₂ he3₂) he2₂) he3₂
  have hzH1 : zOf e ∈ H₁ := by
    show (e 0 * e 1) ^ 2 ∈ H₁
    exact H₁.pow_mem (H₁.mul_mem he0₁ he1₁) 2
  have hzI : zOf e ∈ H₁ ⊓ H₂ := Subgroup.mem_inf.mpr ⟨hzH1, hzH2⟩
  have hcardI : Nat.card ↥(H₁ ⊓ H₂) = 2 := hone.card_inf
  have hz1 : zOf e ≠ 1 := by
    intro hz1
    obtain ⟨w, hwI, hw1⟩ := exists_ne_one_of_card_two hcardI
    have hcw : w * e 0 = e 0 * w := by
      have hσ_cent : e 0 ∈ Subgroup.centralizer ((H₁ ⊓ H₂ : Subgroup G) : Set G) := by
        rw [← hone.eq_centralizer]; exact he0
      exact Subgroup.mem_centralizer_iff.mp hσ_cent w hwI
    have hw_cent : w ∈ Subgroup.centralizer ({e 0} : Set G) ⊓ H₁ := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, (Subgroup.mem_inf.mp hwI).1⟩
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]; exact hcw.symm
    rw [hF.centL₁, hz1, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at hw_cent
    have hw3 : w ^ 3 = 1 := cube_of_mem_zpowers hσ3 hw_cent
    have hw2 : w * w = 1 := sq_eq_one_of_card_two hcardI hwI hw1
    exact hw1 (eq_one_of_sq_cube hw2 hw3)
  have hz2' : zOf e ^ 2 = 1 := by
    rw [sq]; exact sq_eq_one_of_card_two hcardI hzI hz1
  have hz2 : zOf e * zOf e = 1 := by rw [← sq]; exact hz2'
  have hord2 : orderOf (zOf e) = 2 := orderOf_eq_prime hz2' hz1
  have hzp : Subgroup.zpowers (zOf e) = H₁ ⊓ H₂ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzI) ?_
    rw [Nat.card_zpowers, hord2, hcardI]
  have hzH : ∀ g : G, g ∈ H ↔ zOf e * g = g * zOf e := by
    intro g
    constructor
    · intro hg
      rw [hone.eq_centralizer] at hg
      exact Subgroup.mem_centralizer_iff.mp hg (zOf e) hzI
    · intro hg
      rw [hone.eq_centralizer]
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro k hk
      have hk' : k ∈ Subgroup.zpowers (zOf e) := by rw [hzp]; exact hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk'
      exact (Commute.zpow_left (show Commute (zOf e) g from hg) n).eq
  have hzσ : zOf e * e 0 = e 0 * zOf e := (hzH _).mp he0
  have hzτ : zOf e * e 2 = e 2 * zOf e := (hzH _).mp he2
  have hzt : zOf e * e 4 = e 4 * zOf e := (hzH _).mp he4
  have hSL : Nat.card (SL(2, ZMod 3)) = 24 := by
    rw [Nat.card_eq_fintype_card]; decide +kernel
  have hLH₁ : Nat.card ↥H₁ = 24 := by
    obtain ⟨φ⟩ := hone.iso_one
    rw [Nat.card_congr φ.toEquiv, hSL]
  have hLH₂ : Nat.card ↥H₂ = 24 := by
    obtain ⟨φ⟩ := hone.iso_two
    rw [Nat.card_congr φ.toEquiv, hSL]
  have he0ne : e 0 ≠ 1 := by
    intro h0
    have hle : Psub e ≤ Subgroup.zpowers (e 2) := by
      unfold Psub
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · rw [h0]; exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    have hd := Subgroup.card_dvd_of_le hle
    rw [hF.card_P, Nat.card_zpowers] at hd
    have := Nat.dvd_trans hd (orderOf_dvd_of_pow_eq_one hτ3)
    norm_num at this
  have he2ne : e 2 ≠ 1 := by
    intro h2
    have hle : Psub e ≤ Subgroup.zpowers (e 0) := by
      unfold Psub
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_zpowers _
      · rw [h2]; exact Subgroup.one_mem _
    have hd := Subgroup.card_dvd_of_le hle
    rw [hF.card_P, Nat.card_zpowers] at hd
    have := Nat.dvd_trans hd (orderOf_dvd_of_pow_eq_one hσ3)
    norm_num at this
  have hσo : orderOf (e 0) = 3 := orderOf_eq_prime hσ3 he0ne
  have hτo : orderOf (e 2) = 3 := orderOf_eq_prime hτ3 he2ne
  have hM1 : Nat.card ↥M₁ = 27 := by
    rcases hL.cor.cases with ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩
    · rw [hPb] at h2; norm_num at h2
    · exact h1
    · rw [hPb] at h2; norm_num at h2
  have hM2 : Nat.card ↥M₂ = 27 := by rw [← hL.cor.card_eq]; exact hM1
  have hXy1 : Nat.card ↥(M₁ ⊓ Subgroup.centralizer ({e 2} : Set G)) = 9 := by
    have h := hL.cor.card_Pb₂
    rw [hPb] at h
    omega
  have hXy2 : Nat.card ↥(M₂ ⊓ Subgroup.centralizer ({e 0} : Set G)) = 9 := by
    have h := hL.cor.card_Pb₁
    rw [hPb] at h
    omega
  obtain ⟨s1a, s1b, s1c, s1d, s1e, s1f, s1g, s1h, s1i, s1j⟩ :=
    side_facts hL.v₁ hzH he0 he2₂ he2ne hστ hLH₂ hM1 hXy1
  obtain ⟨s2a, s2b, s2c, s2d, s2e, s2f, s2g, s2h, s2i, s2j⟩ :=
    side_facts hL.v₂ hzH he2 he0₁ he0ne hστ.symm hLH₁ hM2 hXy2
  have hcomm1 : ∀ x ∈ M₁, ∀ y ∈ M₁, x * y = y * x :=
    vertex_comm (σ := e 0) (τ := e 2) (z := zOf e) (t := e 4) (M := M₁) (N := M₂) hM1 hσo
      s1a s1b s1f s1g hXy1 s1d s1c s1h hM2 s2a s2b s2f s2g hτo hστ hzσ hzτ hz2 htσ
      hL.four.s12
  have hcomm2 : ∀ x ∈ M₂, ∀ y ∈ M₂, x * y = y * x :=
    vertex_comm (σ := e 2) (τ := e 0) (z := zOf e) (t := e 4) (M := M₂) (N := M₁) hM2 hτo
      s2a s2b s2f s2g hXy2 s2d s2c s2h hM1 s1a s1b s1f s1g hσo hστ.symm hzτ hzσ hz2 htτ
      (fun hc => hL.four.s12 hc.symm)
  have cube1 : ∀ x ∈ M₁, x ^ 3 = 1 :=
    cube_one_of_comm (σ := e 0) (z := zOf e) (t := e 4) (M := M₁) hM1 hσo s1a s1b hcomm1
      hzσ hz2 ht2 htσ hzt s1c s1e s1d s1i s1j
  have cube2 : ∀ x ∈ M₂, x ^ 3 = 1 :=
    cube_one_of_comm (σ := e 2) (z := zOf e) (t := e 4) (M := M₂) hM2 hτo s2a s2b hcomm2
      hzτ hz2 ht2 htτ hzt s2c s2e s2d s2i s2j
  have hE1 : IsElemAbelian 3 M₁ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hcomm1 a a.2 b b.2)⟩⟩, fun x hx => cube1 x hx⟩
  have hE2 : IsElemAbelian 3 M₂ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hcomm2 a a.2 b b.2)⟩⟩, fun x hx => cube2 x hx⟩
  exact ⟨hE1, hE2⟩

end CFSG.GH74.QTGen4.Recog.G23.P7
