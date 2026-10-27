module

public import CFSG.GroupTheory.QuaternionQuotientCenter

public section

namespace CFSG.GroupTheory

open Subgroup QuaternionGroup

variable {G : Type*} [Group G]

theorem mem_centerIn_or_of_card_eq_four_mul [Finite G] {N : Subgroup G}
    (hidx : Nat.card N = 4 * Nat.card (centerIn N)) {x y : G} (hx : x ∈ N) (hy : y ∈ N)
    (hxy : x * y ≠ y * x) :
    ∀ m ∈ N, m ∈ centerIn N ∨ x⁻¹ * m ∈ centerIn N ∨ y⁻¹ * m ∈ centerIn N ∨
      (x * y)⁻¹ * m ∈ centerIn N := by
  classical
  have hmem : ∀ u : ↥N, u ∈ Subgroup.center ↥N ↔ (u : G) ∈ centerIn N := by
    intro u
    rw [Subgroup.mem_center_iff]
    constructor
    · intro h
      refine Subgroup.mem_inf.mpr ⟨u.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      exact congrArg Subtype.val (h ⟨n, hn⟩)
    · intro h v
      apply Subtype.ext
      simpa using Subgroup.mem_centralizer_iff.mp h.2 (v : G) v.2
  have hZcomm : ∀ u ∈ centerIn N, ∀ n ∈ N, n * u = u * n :=
    fun u hu n hn => Subgroup.mem_centralizer_iff.mp hu.2 n hn
  have hxZ : x ∉ centerIn N := fun h => hxy (hZcomm x h y hy).symm
  have hyZ : y ∉ centerIn N := fun h => hxy (hZcomm y h x hx)
  have hxyZ : x * y ∉ centerIn N := by
    intro h
    have h1 : x * (x * y) = (x * y) * x := hZcomm (x * y) h x hx
    have h2 : x * (x * y) = x * (y * x) := by rw [h1]; group
    exact hxy (mul_left_cancel h2)
  have hxiyZ : x⁻¹ * y ∉ centerIn N := by
    intro h
    have h1 : x * (x⁻¹ * y) = (x⁻¹ * y) * x := hZcomm (x⁻¹ * y) h x hx
    have h1' : y = x⁻¹ * y * x := by
      calc y = x * (x⁻¹ * y) := by group
        _ = (x⁻¹ * y) * x := h1
    have h2 : x * y = y * x := by
      have := congrArg (fun t => x * t) h1'
      simpa [mul_assoc] using this
    exact hxy h2
  let Q := ↥N ⧸ Subgroup.center ↥N
  have : Fintype Q := Fintype.ofFinite Q
  let q1 : Q := QuotientGroup.mk (1 : ↥N)
  let qx : Q := QuotientGroup.mk ⟨x, hx⟩
  let qy : Q := QuotientGroup.mk ⟨y, hy⟩
  let qxy : Q := QuotientGroup.mk ⟨x * y, N.mul_mem hx hy⟩
  have h1x : q1 ≠ qx := by
    intro h
    have h' := QuotientGroup.eq.mp h
    have hx' : x ∈ centerIn N := by
      simpa using (hmem ((1 : ↥N)⁻¹ * ⟨x, hx⟩)).mp h'
    exact hxZ hx'
  have h1y : q1 ≠ qy := by
    intro h
    have h' := QuotientGroup.eq.mp h
    have hy' : y ∈ centerIn N := by
      simpa using (hmem ((1 : ↥N)⁻¹ * ⟨y, hy⟩)).mp h'
    exact hyZ hy'
  have h1xy : q1 ≠ qxy := by
    intro h
    have h' := QuotientGroup.eq.mp h
    have hxy' : x * y ∈ centerIn N := by
      simpa using (hmem ((1 : ↥N)⁻¹ * ⟨x * y, N.mul_mem hx hy⟩)).mp h'
    exact hxyZ hxy'
  have hxy_ne : qx ≠ qy := by
    intro h
    have h' := QuotientGroup.eq.mp h
    have h'' : x⁻¹ * y ∈ centerIn N := by
      simpa using (hmem ((⟨x, hx⟩ : ↥N)⁻¹ * ⟨y, hy⟩)).mp h'
    exact hxiyZ h''
  have hxxy : qx ≠ qxy := by
    intro h
    have h' := QuotientGroup.eq.mp h
    have h2 : ((⟨x, hx⟩ : ↥N)⁻¹ * ⟨x * y, N.mul_mem hx hy⟩ : ↥N) = ⟨y, hy⟩ := by
      apply Subtype.ext
      simp
    rw [h2] at h'
    exact hyZ ((hmem ⟨y, hy⟩).mp h')
  have hyxy : qy ≠ qxy := by
    intro h
    have h' := QuotientGroup.eq.mp h
    have h'' : y⁻¹ * x * y ∈ centerIn N := by
      simpa [mul_assoc] using (hmem ((⟨y, hy⟩ : ↥N)⁻¹ * ⟨x * y, N.mul_mem hx hy⟩)).mp h'
    have h3 : y * (y⁻¹ * x * y) = (y⁻¹ * x * y) * y := hZcomm _ h'' y hy
    have h5 : x = y⁻¹ * x * y := by
      have := congrArg (fun t => t * y⁻¹) h3
      simpa [mul_assoc] using this
    have h6 : y * x = x * y := by
      have := congrArg (fun t => y * t) h5
      simpa [mul_assoc] using this
    exact hxy h6.symm
  have hZcard : Nat.card (Subgroup.center ↥N) = Nat.card (centerIn N) := by
    rw [centerIn_eq_map_center, Subgroup.card_map_of_injective N.subtype_injective]
  have hZpos : 0 < Nat.card (Subgroup.center ↥N) := by
    have : Nonempty ↥(Subgroup.center ↥N) :=
      Nonempty.intro ⟨1, Subgroup.one_mem _⟩
    exact Nat.card_pos
  have hQ : Nat.card Q = 4 := by
    have h1 : Nat.card Q * Nat.card (Subgroup.center ↥N) = 4 * Nat.card (Subgroup.center ↥N) := by
      rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥N), hidx, hZcard]
    exact Nat.eq_of_mul_eq_mul_right hZpos h1
  have hcardS : ({q1, qx, qy, qxy} : Finset Q).card = 4 := by
    have h1 : q1 ∉ ({qx, qy, qxy} : Finset Q) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1x, h1y, h1xy⟩
    have h2 : qx ∉ ({qy, qxy} : Finset Q) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy_ne, hxxy⟩
    have h3 : qy ∉ ({qxy} : Finset Q) := by
      simpa using hyxy
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have huniv : ({q1, qx, qy, qxy} : Finset Q) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcardS, ← Nat.card_eq_fintype_card, hQ]
  intro m hm
  let qm : Q := QuotientGroup.mk ⟨m, hm⟩
  have hq : qm ∈ ({q1, qx, qy, qxy} : Finset Q) := by
    rw [huniv]
    exact Finset.mem_univ qm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with h | h | h | h
  · left
    have h' := QuotientGroup.eq.mp h
    have h'' : m⁻¹ ∈ centerIn N := by
      simpa using (hmem ((⟨m, hm⟩ : ↥N)⁻¹ * 1)).mp h'
    simpa using (centerIn N).inv_mem h''
  · right; left
    have h' := QuotientGroup.eq.mp h
    have h'' : m⁻¹ * x ∈ centerIn N := by
      simpa using (hmem ((⟨m, hm⟩ : ↥N)⁻¹ * ⟨x, hx⟩)).mp h'
    have h3 : (m⁻¹ * x)⁻¹ ∈ centerIn N := (centerIn N).inv_mem h''
    simpa using h3
  · right; right; left
    have h' := QuotientGroup.eq.mp h
    have h'' : m⁻¹ * y ∈ centerIn N := by
      simpa using (hmem ((⟨m, hm⟩ : ↥N)⁻¹ * ⟨y, hy⟩)).mp h'
    have h3 : (m⁻¹ * y)⁻¹ ∈ centerIn N := (centerIn N).inv_mem h''
    simpa using h3
  · right; right; right
    have h' := QuotientGroup.eq.mp h
    have h'' : m⁻¹ * (x * y) ∈ centerIn N := by
      simpa using (hmem ((⟨m, hm⟩ : ↥N)⁻¹ * ⟨x * y, N.mul_mem hx hy⟩)).mp h'
    have h3 : (m⁻¹ * (x * y))⁻¹ ∈ centerIn N := (centerIn N).inv_mem h''
    simpa [mul_assoc] using h3

private theorem commutator_inv_mul_eq_one_of_central {n g x e : G} (he : e * e = 1)
    (hne : n * e = e * n) (hg : g * x * g⁻¹ * x⁻¹ = e) (hn : n * x * n⁻¹ * x⁻¹ = e) :
    (n⁻¹ * g) * x * (n⁻¹ * g)⁻¹ * x⁻¹ = 1 := by
  have hg' : g * x * g⁻¹ = e * x := by
    calc g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
      _ = e * x := by rw [hg]
  have hn' : n * x * n⁻¹ = e * x := by
    calc n * x * n⁻¹ = (n * x * n⁻¹ * x⁻¹) * x := by group
      _ = e * x := by rw [hn]
  have hne' : n⁻¹ * e = e * n⁻¹ := by
    have hconj : n * e * n⁻¹ = e := by rw [hne]; group
    calc n⁻¹ * e = n⁻¹ * (n * e * n⁻¹) := by rw [hconj]
      _ = e * n⁻¹ := by group
  have hnx : n⁻¹ * x * n = e * x := by
    have h3 : x = e * (n⁻¹ * x * n) := by
      calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
        _ = n⁻¹ * (e * x) * n := by rw [hn']
        _ = e * (n⁻¹ * x * n) := by
              calc n⁻¹ * (e * x) * n = (n⁻¹ * e) * (x * n) := by group
                _ = (e * n⁻¹) * (x * n) := by rw [hne']
                _ = e * (n⁻¹ * x * n) := by group
    calc n⁻¹ * x * n = (e * e) * (n⁻¹ * x * n) := by rw [he, one_mul]
      _ = e * (e * (n⁻¹ * x * n)) := by group
      _ = e * x := by rw [← h3]
  have hnen : n⁻¹ * e * n = e := by
    calc n⁻¹ * e * n = n⁻¹ * (e * n) := by group
      _ = n⁻¹ * (n * e) := by rw [hne]
      _ = e := by group
  calc (n⁻¹ * g) * x * (n⁻¹ * g)⁻¹ * x⁻¹
      = n⁻¹ * (g * x * g⁻¹) * n * x⁻¹ := by group
    _ = n⁻¹ * (e * x) * n * x⁻¹ := by rw [hg']
    _ = (n⁻¹ * e * n) * (n⁻¹ * x * n * x⁻¹) := by group
    _ = e * e := by rw [hnen, hnx]; group
    _ = 1 := he

private theorem commute_inv_mul_of_commute {n g a : G} (hn : n * a = a * n) (hg : g * a = a * g) :
    (n⁻¹ * g) * a = a * (n⁻¹ * g) := by
  have hconj : n * a * n⁻¹ = a := by rw [hn]; group
  have hn' : n⁻¹ * a = a * n⁻¹ := by
    calc n⁻¹ * a = n⁻¹ * (n * a * n⁻¹) := by rw [hconj]
      _ = a * n⁻¹ := by group
  calc (n⁻¹ * g) * a = n⁻¹ * (g * a) := by group
    _ = n⁻¹ * (a * g) := by rw [hg]
    _ = (n⁻¹ * a) * g := by group
    _ = (a * n⁻¹) * g := by rw [hn']
    _ = a * (n⁻¹ * g) := by group

theorem exists_inv_mul_commute_of_commutator_eq_one_or_eq [Finite G] {T N : Subgroup G}
    (hidx : Nat.card N = 4 * Nat.card (centerIn N))
    (hZ2 : ∀ x ∈ centerIn N, x * x = 1) {z : G} (hz : z ∈ centerIn N)
    (hcommN : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z)
    (hTZ : ∀ g ∈ T, ∀ x ∈ centerIn N, g * x = x * g)
    (hθ : ∀ g ∈ T, ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ = 1 ∨ g * n * g⁻¹ * n⁻¹ = z) :
    ∀ g ∈ T, ∃ n ∈ N, ∀ m ∈ N, n⁻¹ * g * m = m * (n⁻¹ * g) := by
  classical
  have hzz : z * z = 1 := hZ2 z hz
  have hNnab : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hNle : N ≤ centerIn N := by
      intro a ha
      refine Subgroup.mem_inf.mpr ⟨ha, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (h a ha b hb).symm
    have heq : centerIn N = N := le_antisymm inf_le_left hNle
    have hpos : 0 < Nat.card N := Nat.card_pos
    rw [heq] at hidx
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := hNnab
  have hzyx : x * y * x⁻¹ * y⁻¹ = z := by
    rcases hcommN x hx y hy with h | h
    · rw [← commutatorElement_def] at h
      exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h) hxy
    · exact h
  have hzinv : z⁻¹ = z := (mul_eq_one_iff_inv_eq).mp hzz
  have hyx : y * x * y⁻¹ * x⁻¹ = z := by
    have h : (x * y * x⁻¹ * y⁻¹)⁻¹ = z⁻¹ := by rw [hzyx]
    simpa only [mul_inv_rev, inv_inv, hzinv, mul_assoc] using h
  have hxx : x * x * x⁻¹ * x⁻¹ = 1 := by group
  have hyy : y * y * y⁻¹ * y⁻¹ = 1 := by group
  have hxyx : (x * y) * x * (x * y)⁻¹ * x⁻¹ = z := by
    have h1 : (x * y) * x * (x * y)⁻¹ * x⁻¹
        = x * (y * x * y⁻¹ * x⁻¹) * x⁻¹ * (x * x * x⁻¹ * x⁻¹) := by group
    rw [h1, hyx, hxx, mul_one, Subgroup.mem_centralizer_iff.mp hz.2 x hx]
    group
  have hxyy : (x * y) * y * (x * y)⁻¹ * y⁻¹ = z := by
    have h1 : (x * y) * y * (x * y)⁻¹ * y⁻¹
        = x * (y * y * y⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
    rw [h1, hyy, hzyx]
    simp only [mul_one]
    group
  have key : ∀ k, (∀ a ∈ centerIn N, k * a = a * k) → k * x = x * k → k * y = y * k →
      ∀ m ∈ N, k * m = m * k := by
    intro k hkZ hkx hky m hm
    rcases mem_centerIn_or_of_card_eq_four_mul hidx hx hy hxy m hm with h1 | h2 | h3 | h4
    · exact hkZ m h1
    · have hc : k * (x⁻¹ * m) = (x⁻¹ * m) * k := hkZ _ h2
      calc k * m = k * (x * (x⁻¹ * m)) := by rw [mul_inv_cancel_left]
        _ = (k * x) * (x⁻¹ * m) := by group
        _ = (x * k) * (x⁻¹ * m) := by rw [hkx]
        _ = x * (k * (x⁻¹ * m)) := by group
        _ = x * ((x⁻¹ * m) * k) := by rw [hc]
        _ = m * k := by group
    · have hc : k * (y⁻¹ * m) = (y⁻¹ * m) * k := hkZ _ h3
      calc k * m = k * (y * (y⁻¹ * m)) := by rw [mul_inv_cancel_left]
        _ = (k * y) * (y⁻¹ * m) := by group
        _ = (y * k) * (y⁻¹ * m) := by rw [hky]
        _ = y * (k * (y⁻¹ * m)) := by group
        _ = y * ((y⁻¹ * m) * k) := by rw [hc]
        _ = m * k := by group
    · have hc : k * ((x * y)⁻¹ * m) = ((x * y)⁻¹ * m) * k := hkZ _ h4
      have hkxy : k * (x * y) = (x * y) * k := by
        calc k * (x * y) = (k * x) * y := by group
          _ = (x * k) * y := by rw [hkx]
          _ = x * (k * y) := by group
          _ = x * (y * k) := by rw [hky]
          _ = (x * y) * k := by group
      calc k * m = k * ((x * y) * ((x * y)⁻¹ * m)) := by rw [mul_inv_cancel_left]
        _ = (k * (x * y)) * ((x * y)⁻¹ * m) := by group
        _ = ((x * y) * k) * ((x * y)⁻¹ * m) := by rw [hkxy]
        _ = (x * y) * (k * ((x * y)⁻¹ * m)) := by group
        _ = (x * y) * (((x * y)⁻¹ * m) * k) := by rw [hc]
        _ = m * k := by group
  intro g hg
  rcases hθ g hg x hx with hgx1 | hgxz <;> rcases hθ g hg y hy with hgy1 | hgyz
  · refine ⟨1, N.one_mem, ?_⟩
    intro m hm
    have hkx : g * x = x * g := by
      rw [← commutatorElement_def] at hgx1
      exact commutatorElement_eq_one_iff_mul_comm.mp hgx1
    have hky : g * y = y * g := by
      rw [← commutatorElement_def] at hgy1
      exact commutatorElement_eq_one_iff_mul_comm.mp hgy1
    simpa using key g (hTZ g hg) hkx hky m hm
  · refine ⟨x, hx, ?_⟩
    intro m hm
    have ckx : (x⁻¹ * g) * x * (x⁻¹ * g)⁻¹ * x⁻¹ = 1 :=
      commutator_inv_mul_eq_one_of_central (n := x) (g := g) (x := x) (e := 1)
        (by group) (by group) hgx1 hxx
    have cky : (x⁻¹ * g) * y * (x⁻¹ * g)⁻¹ * y⁻¹ = 1 :=
      commutator_inv_mul_eq_one_of_central (n := x) (g := g) (x := y) (e := z)
        hzz (Subgroup.mem_centralizer_iff.mp hz.2 x hx) hgyz hzyx
    have hkx : (x⁻¹ * g) * x = x * (x⁻¹ * g) := by
      rw [← commutatorElement_def] at ckx
      exact commutatorElement_eq_one_iff_mul_comm.mp ckx
    have hky : (x⁻¹ * g) * y = y * (x⁻¹ * g) := by
      rw [← commutatorElement_def] at cky
      exact commutatorElement_eq_one_iff_mul_comm.mp cky
    exact key _ (fun a ha => commute_inv_mul_of_commute
      (Subgroup.mem_centralizer_iff.mp ha.2 x hx) (hTZ g hg a ha)) hkx hky m hm
  · refine ⟨y, hy, ?_⟩
    intro m hm
    have ckx : (y⁻¹ * g) * x * (y⁻¹ * g)⁻¹ * x⁻¹ = 1 :=
      commutator_inv_mul_eq_one_of_central (n := y) (g := g) (x := x) (e := z)
        hzz (Subgroup.mem_centralizer_iff.mp hz.2 y hy) hgxz hyx
    have cky : (y⁻¹ * g) * y * (y⁻¹ * g)⁻¹ * y⁻¹ = 1 :=
      commutator_inv_mul_eq_one_of_central (n := y) (g := g) (x := y) (e := 1)
        (by group) (by group) hgy1 hyy
    have hkx : (y⁻¹ * g) * x = x * (y⁻¹ * g) := by
      rw [← commutatorElement_def] at ckx
      exact commutatorElement_eq_one_iff_mul_comm.mp ckx
    have hky : (y⁻¹ * g) * y = y * (y⁻¹ * g) := by
      rw [← commutatorElement_def] at cky
      exact commutatorElement_eq_one_iff_mul_comm.mp cky
    exact key _ (fun a ha => commute_inv_mul_of_commute
      (Subgroup.mem_centralizer_iff.mp ha.2 y hy) (hTZ g hg a ha)) hkx hky m hm
  · refine ⟨x * y, N.mul_mem hx hy, ?_⟩
    intro m hm
    have ckx : ((x * y)⁻¹ * g) * x * ((x * y)⁻¹ * g)⁻¹ * x⁻¹ = 1 :=
      commutator_inv_mul_eq_one_of_central (n := x * y) (g := g) (x := x) (e := z)
        hzz (Subgroup.mem_centralizer_iff.mp hz.2 (x * y) (N.mul_mem hx hy)) hgxz hxyx
    have cky : ((x * y)⁻¹ * g) * y * ((x * y)⁻¹ * g)⁻¹ * y⁻¹ = 1 :=
      commutator_inv_mul_eq_one_of_central (n := x * y) (g := g) (x := y) (e := z)
        hzz (Subgroup.mem_centralizer_iff.mp hz.2 (x * y) (N.mul_mem hx hy)) hgyz hxyy
    have hkx : ((x * y)⁻¹ * g) * x = x * ((x * y)⁻¹ * g) := by
      rw [← commutatorElement_def] at ckx
      exact commutatorElement_eq_one_iff_mul_comm.mp ckx
    have hky : ((x * y)⁻¹ * g) * y = y * ((x * y)⁻¹ * g) := by
      rw [← commutatorElement_def] at cky
      exact commutatorElement_eq_one_iff_mul_comm.mp cky
    exact key _ (fun a ha => commute_inv_mul_of_commute
      (Subgroup.mem_centralizer_iff.mp ha.2 (x * y) (N.mul_mem hx hy)) (hTZ g hg a ha))
      hkx hky m hm

theorem commute_of_mem_centerIn_of_quaternion_quotient_of_pow_three_mem {T N : Subgroup G}
    (hNT : N ≤ T) (π : ↥T →* QuaternionGroup 2) (hπ : Function.Surjective π)
    (hker : π.ker = N.subgroupOf T) (hZ2 : ∀ x ∈ centerIn N, x * x = 1)
    {ρ : G} (hρT : ∀ g ∈ T, ρ * g * ρ⁻¹ ∈ T) (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N)
    (hρZ : ∀ x ∈ centerIn N, ρ * x = x * ρ) (hρ3 : ρ ^ 3 ∈ N)
    (hρ : ∃ g ∈ T, ρ * g * ρ⁻¹ * g⁻¹ ∉ N) :
    ∀ x ∈ centerIn T, ρ * x = x * ρ := by
  classical
  have hρinvT : ∀ g ∈ T, ρ⁻¹ * g * ρ ∈ T := by
    intro g hg
    have h1 : ρ⁻¹ * g * ρ = ρ ^ 2 * ((ρ ^ 3)⁻¹ * g * ρ ^ 3) * (ρ ^ 2)⁻¹ := by group
    have h2 : (ρ ^ 3)⁻¹ * g * ρ ^ 3 ∈ T :=
      T.mul_mem (T.mul_mem (T.inv_mem (hNT hρ3)) hg) (hNT hρ3)
    have h3 : ρ * ((ρ ^ 3)⁻¹ * g * ρ ^ 3) * ρ⁻¹ ∈ T := hρT _ h2
    have h4 : ρ * (ρ * ((ρ ^ 3)⁻¹ * g * ρ ^ 3) * ρ⁻¹) * ρ⁻¹ ∈ T := hρT _ h3
    have h5 : ρ ^ 2 * ((ρ ^ 3)⁻¹ * g * ρ ^ 3) * (ρ ^ 2)⁻¹ =
        ρ * (ρ * ((ρ ^ 3)⁻¹ * g * ρ ^ 3) * ρ⁻¹) * ρ⁻¹ := by group
    rw [h1, h5]
    exact h4
  have hρinvN : ∀ n ∈ N, ρ⁻¹ * n * ρ ∈ N := by
    intro n hn
    have h1 : ρ⁻¹ * n * ρ = ρ ^ 2 * ((ρ ^ 3)⁻¹ * n * ρ ^ 3) * (ρ ^ 2)⁻¹ := by group
    have h2 : (ρ ^ 3)⁻¹ * n * ρ ^ 3 ∈ N :=
      N.mul_mem (N.mul_mem (N.inv_mem hρ3) hn) hρ3
    have h3 : ρ * ((ρ ^ 3)⁻¹ * n * ρ ^ 3) * ρ⁻¹ ∈ N := hρN _ h2
    have h4 : ρ * (ρ * ((ρ ^ 3)⁻¹ * n * ρ ^ 3) * ρ⁻¹) * ρ⁻¹ ∈ N := hρN _ h3
    have h5 : ρ ^ 2 * ((ρ ^ 3)⁻¹ * n * ρ ^ 3) * (ρ ^ 2)⁻¹ =
        ρ * (ρ * ((ρ ^ 3)⁻¹ * n * ρ ^ 3) * ρ⁻¹) * ρ⁻¹ := by group
    rw [h1, h5]
    exact h4
  intro x hx
  have hxT : x ∈ T := hx.1
  have hyT : ρ * x * ρ⁻¹ ∈ T := hρT x hxT
  have hyZ : ρ * x * ρ⁻¹ ∈ centerIn T := by
    refine Subgroup.mem_inf.mpr ⟨hyT, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' : ρ⁻¹ * g * ρ ∈ T := hρinvT g hg
    have hxcomm : (ρ⁻¹ * g * ρ) * x = x * (ρ⁻¹ * g * ρ) :=
      Subgroup.mem_centralizer_iff.mp hx.2 _ hg'
    calc g * (ρ * x * ρ⁻¹) = ρ * (ρ⁻¹ * g * ρ) * x * ρ⁻¹ := by group
      _ = ρ * ((ρ⁻¹ * g * ρ) * x) * ρ⁻¹ := by group
      _ = ρ * (x * (ρ⁻¹ * g * ρ)) * ρ⁻¹ := by rw [hxcomm]
      _ = (ρ * x * ρ⁻¹) * g := by group
  have hπcentral : ∀ y : QuaternionGroup 2, π ⟨x, hxT⟩ * y = y * π ⟨x, hxT⟩ := by
    intro y
    obtain ⟨g, rfl⟩ := hπ y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hx.2 g g.2).symm
  obtain ⟨α, hα, hα3, hαne⟩ :=
    exists_quaternionGroup_two_endomorphism_of_conj hNT π hπ hker hρT hρN hρ3 hρ
  have hαx : α (π ⟨x, hxT⟩) = π ⟨x, hxT⟩ := by
    rcases quaternionGroup_two_eq_one_or_eq_a_two_of_commute (π ⟨x, hxT⟩) hπcentral with h | h
    · rw [h, map_one]
    · rw [h, quaternionGroup_two_apply_a_two α hα3]
  have heT : ρ * x * ρ⁻¹ * x⁻¹ ∈ T := T.mul_mem hyT (T.inv_mem hxT)
  have heN : ρ * x * ρ⁻¹ * x⁻¹ ∈ N := by
    have hπe : π ⟨ρ * x * ρ⁻¹ * x⁻¹, heT⟩ = 1 := by
      have h1 : π ⟨ρ * x * ρ⁻¹ * x⁻¹, heT⟩ =
          π ⟨ρ * x * ρ⁻¹, hyT⟩ * (π ⟨x, hxT⟩)⁻¹ := by
        rw [show (⟨ρ * x * ρ⁻¹ * x⁻¹, heT⟩ : ↥T) = ⟨ρ * x * ρ⁻¹, hyT⟩ * ⟨x, hxT⟩⁻¹ from rfl]
        rw [map_mul, map_inv]
      have hα' : π ⟨ρ * x * ρ⁻¹, hyT⟩ = α (π ⟨x, hxT⟩) := hα ⟨x, hxT⟩
      rw [h1, hα', hαx]
      simp
    have hmem : (⟨ρ * x * ρ⁻¹ * x⁻¹, heT⟩ : ↥T) ∈ N.subgroupOf T := by
      rw [← hker, MonoidHom.mem_ker]
      exact hπe
    exact Subgroup.mem_subgroupOf.mp hmem
  have heZT : ρ * x * ρ⁻¹ * x⁻¹ ∈ centerIn T :=
    (centerIn T).mul_mem hyZ ((centerIn T).inv_mem hx)
  have heZ : ρ * x * ρ⁻¹ * x⁻¹ ∈ centerIn N := by
    refine Subgroup.mem_inf.mpr ⟨heN, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact Subgroup.mem_centralizer_iff.mp heZT.2 n (hNT hn)
  have hρe : ρ * (ρ * x * ρ⁻¹ * x⁻¹) = (ρ * x * ρ⁻¹ * x⁻¹) * ρ := hρZ _ heZ
  have hee : (ρ * x * ρ⁻¹ * x⁻¹) * (ρ * x * ρ⁻¹ * x⁻¹) = 1 := hZ2 _ heZ
  have hxe : ρ * x * ρ⁻¹ = (ρ * x * ρ⁻¹ * x⁻¹) * x := by group
  have hρ2 : ρ ^ 2 * x * (ρ ^ 2)⁻¹ = x := by
    have h1 : ρ ^ 2 * x * (ρ ^ 2)⁻¹ = ρ * (ρ * x * ρ⁻¹) * ρ⁻¹ := by
      rw [pow_two]
      group
    rw [h1]
    have h2 : ρ * (ρ * x * ρ⁻¹) * ρ⁻¹ = ρ * ((ρ * x * ρ⁻¹ * x⁻¹) * x) * ρ⁻¹ := by
      conv_lhs => rw [hxe]
    rw [h2]
    have h3 : ρ * ((ρ * x * ρ⁻¹ * x⁻¹) * x) * ρ⁻¹ =
        (ρ * (ρ * x * ρ⁻¹ * x⁻¹) * ρ⁻¹) * (ρ * x * ρ⁻¹) := by group
    rw [h3]
    have h4 : ρ * (ρ * x * ρ⁻¹ * x⁻¹) * ρ⁻¹ = ρ * x * ρ⁻¹ * x⁻¹ := by
      rw [hρe]
      group
    rw [h4]
    nth_rewrite 2 [hxe]
    rw [← mul_assoc, hee, one_mul]
  have hρ3x : ρ ^ 3 * x * (ρ ^ 3)⁻¹ = x := by
    have hxcomm : ρ ^ 3 * x = x * ρ ^ 3 := Subgroup.mem_centralizer_iff.mp hx.2 _ (hNT hρ3)
    rw [hxcomm]
    group
  have he1 : ρ * x * ρ⁻¹ * x⁻¹ = 1 := by
    have h : ρ ^ 3 * x * (ρ ^ 3)⁻¹ = ρ * (ρ ^ 2 * x * (ρ ^ 2)⁻¹) * ρ⁻¹ := by
      rw [pow_two, pow_three]
      group
    rw [hρ2, hρ3x] at h
    rw [hxe] at h
    have h3 : (ρ * x * ρ⁻¹ * x⁻¹) * x = 1 * x := by rw [← h, one_mul]
    exact mul_right_cancel h3
  calc ρ * x = (ρ * x * ρ⁻¹) * ρ := by group
    _ = x * ρ := by rw [hxe, he1, one_mul]

private def q8Map (p q : QuaternionGroup 2) : QuaternionGroup 2 → QuaternionGroup 2
  | .a k => p ^ k.val
  | .xa k => q * p ^ k.val

private theorem q8Map_check_enum : ∀ p q : QuaternionGroup 2,
    (∀ g h, q8Map p q (g * h) = q8Map p q g * q8Map p q h) →
    (∀ g, q8Map p q (q8Map p q (q8Map p q g)) = g) →
    (∃ g, q8Map p q g ≠ g) →
    ∀ x : QuaternionGroup 2, x ≠ 1 → x ≠ a 2 →
      x = a 1 ∨ x = (a 1)⁻¹ ∨ x = p ∨ x = p⁻¹ ∨
        x = q8Map p q p ∨ x = (q8Map p q p)⁻¹ := by
  decide

private theorem q8Map_check_noncentral : ∀ p q : QuaternionGroup 2,
    (∀ g h, q8Map p q (g * h) = q8Map p q g * q8Map p q h) →
    (∀ g, q8Map p q (q8Map p q (q8Map p q g)) = g) →
    (∃ g, q8Map p q g ≠ g) →
    p * (a 1)⁻¹ ≠ 1 ∧ p * (a 1)⁻¹ ≠ a 2 := by
  decide

private theorem quaternionGroup_two_facts_of_pow_three
    (α : QuaternionGroup 2 →* QuaternionGroup 2) (h3 : ∀ x, α (α (α x)) = x)
    (hne : ∃ x, α x ≠ x) :
    (∀ x : QuaternionGroup 2, x ≠ 1 → x ≠ a 2 →
      x = a 1 ∨ x = (a 1)⁻¹ ∨ x = α (a 1) ∨ x = (α (a 1))⁻¹ ∨
        x = α (α (a 1)) ∨ x = (α (α (a 1)))⁻¹) ∧
      α (a 1) * (a 1)⁻¹ ≠ 1 ∧ α (a 1) * (a 1)⁻¹ ≠ a 2 := by
  have hmap : ∀ g, α g = q8Map (α (a 1)) (α (xa 0)) g := by
    intro g
    cases g with
    | a k =>
      have h : (a k : QuaternionGroup 2) = a 1 ^ k.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
      calc α (a k) = α (a 1 ^ k.val) := by rw [h]
        _ = α (a 1) ^ k.val := map_pow ..
        _ = q8Map (α (a 1)) (α (xa 0)) (a k) := rfl
    | xa k =>
      have h : (xa k : QuaternionGroup 2) = xa 0 * a 1 ^ k.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val, QuaternionGroup.xa_mul_a,
          zero_add]
      calc α (xa k) = α (xa 0 * a 1 ^ k.val) := by rw [h]
        _ = α (xa 0) * α (a 1) ^ k.val := by rw [map_mul, map_pow]
        _ = q8Map (α (a 1)) (α (xa 0)) (xa k) := rfl
  have hhom : ∀ g h, q8Map (α (a 1)) (α (xa 0)) (g * h) =
      q8Map (α (a 1)) (α (xa 0)) g * q8Map (α (a 1)) (α (xa 0)) h := by
    intro g h
    rw [← hmap, ← hmap, ← hmap, map_mul]
  have hcube : ∀ g, q8Map (α (a 1)) (α (xa 0))
      (q8Map (α (a 1)) (α (xa 0)) (q8Map (α (a 1)) (α (xa 0)) g)) = g := by
    intro g
    rw [← hmap, ← hmap, ← hmap, h3]
  have hnid : ∃ g, q8Map (α (a 1)) (α (xa 0)) g ≠ g := by
    obtain ⟨g, hg⟩ := hne
    exact ⟨g, fun h => hg (by rw [hmap]; exact h)⟩
  have hcheck := q8Map_check_enum (α (a 1)) (α (xa 0)) hhom hcube hnid
  have hnc := q8Map_check_noncentral (α (a 1)) (α (xa 0)) hhom hcube hnid
  exact ⟨fun x hx1 hx2 => by simpa only [← hmap] using hcheck x hx1 hx2, hnc⟩

private theorem quaternionGroup_two_sq_eq_one (x : QuaternionGroup 2) (hx : x * x = 1) :
    x = 1 ∨ x = a 2 := by
  revert x
  decide

private theorem centerIn_cases_of_card_eq_four [Finite G] {N : Subgroup G}
    (hZN : Nat.card (centerIn N) = 4) (hZ2 : ∀ x ∈ centerIn N, x * x = 1)
    {z z₁ a : G} (hz : z ∈ centerIn N) (hz1 : z ≠ 1) (hz₁ : z₁ ∈ centerIn N) (hz₁1 : z₁ ≠ 1)
    (hz₁z : z₁ ≠ z) (ha : a ∈ centerIn N) :
    a = 1 ∨ a = z ∨ a = z₁ ∨ a = z * z₁ := by
  classical
  have : Fintype ↥(centerIn N) := Fintype.ofFinite _
  have hK4 : IsKleinFour ↥(centerIn N) := by
    refine IsKleinFour.mk hZN ?_
    have hdvd : Monoid.exponent ↥(centerIn N) ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => by
        apply Subtype.ext
        simpa [pow_two] using hZ2 (g : G) g.2)
    have hne : Monoid.exponent ↥(centerIn N) ≠ 1 := by
      intro h1
      have hz' : (⟨z, hz⟩ : ↥(centerIn N)) = 1 := by
        have h := Monoid.pow_exponent_eq_one (⟨z, hz⟩ : ↥(centerIn N))
        rwa [h1, pow_one] at h
      exact hz1 (congrArg Subtype.val hz')
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hzz : z * z = 1 := hZ2 z hz
  have hz₁z₁ : z₁ * z₁ = 1 := hZ2 z₁ hz₁
  have hzz₁1 : z * z₁ ≠ 1 := by
    intro h
    have h2 : z₁ = z := by
      calc z₁ = (z * z) * z₁ := by rw [hzz, one_mul]
        _ = z * (z * z₁) := by group
        _ = z * 1 := by rw [h]
        _ = z := mul_one z
    exact hz₁z h2
  have hzz₁z : z * z₁ ≠ z := by
    intro h
    have h2 : z₁ = 1 := by
      have h3 := congrArg (fun t => z * t) h
      rw [hzz] at h3
      calc z₁ = (z * z) * z₁ := by rw [hzz, one_mul]
        _ = z * (z * z₁) := by group
        _ = 1 := h3
    exact hz₁1 h2
  have hzz₁z₁ : z * z₁ ≠ z₁ := by
    intro h
    have h3 := congrArg (fun t => t * z₁) h
    rw [hz₁z₁] at h3
    have h2 : z = 1 := by
      calc z = z * (z₁ * z₁) := by rw [hz₁z₁, mul_one]
        _ = (z * z₁) * z₁ := by group
        _ = 1 := h3
    exact hz1 h2
  have hlift : ∀ {u v : G} (hu : u ∈ centerIn N) (hv : v ∈ centerIn N), u ≠ v →
      (⟨u, hu⟩ : ↥(centerIn N)) ≠ ⟨v, hv⟩ := by
    intro u v hu hv huv h
    exact huv (congrArg Subtype.val h)
  have h1z : (⟨z, hz⟩ : ↥(centerIn N)) ≠ 1 := hlift hz (Subgroup.one_mem _) hz1
  have h1z₁ : (⟨z₁, hz₁⟩ : ↥(centerIn N)) ≠ 1 := hlift hz₁ (Subgroup.one_mem _) hz₁1
  have hzz₁ : (⟨z, hz⟩ : ↥(centerIn N)) ≠ ⟨z₁, hz₁⟩ := hlift hz hz₁ hz₁z.symm
  have hset := IsKleinFour.eq_finset_univ (G := ↥(centerIn N)) h1z h1z₁ hzz₁
  have hmem : (⟨a, ha⟩ : ↥(centerIn N)) ∈
      ({⟨z, hz⟩ * ⟨z₁, hz₁⟩, ⟨z, hz⟩, ⟨z₁, hz₁⟩, (1 : ↥(centerIn N))} :
        Finset ↥(centerIn N)) := by
    rw [hset]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hzz₁' : ((⟨z, hz⟩ * ⟨z₁, hz₁⟩ : ↥(centerIn N)) : G) = z * z₁ := rfl
  rcases hmem with h | h | h | h
  · right; right; right
    have := congrArg Subtype.val h
    simpa [hzz₁'] using this
  · right; left
    exact congrArg Subtype.val h
  · right; right; left
    exact congrArg Subtype.val h
  · left
    exact congrArg Subtype.val h

theorem mem_commutator_or_ncard_sqrt_ne_of_quaternion_quotient [Finite G] {T N : Subgroup G}
    (hNT : N ≤ T) (hNnorm : ∀ g ∈ T, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (π : ↥T →* QuaternionGroup 2) (hπ : Function.Surjective π)
    (hker : π.ker = N.subgroupOf T)
    (hN : Nat.card N = 16) (hZN : Nat.card (centerIn N) = 4)
    (hZ2 : ∀ x ∈ centerIn N, x * x = 1)
    {z z₁ : G} (hz : z ∈ centerIn N) (hz1 : z ≠ 1) (hz₁ : z₁ ∈ centerIn N) (hz₁1 : z₁ ≠ 1)
    (hz₁z : z₁ ≠ z)
    (hsqN : ∀ n ∈ N, n * n = 1 ∨ n * n = z)
    (hcommN : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z)
    {ρ : G} (hρT : ∀ g ∈ T, ρ * g * ρ⁻¹ ∈ T) (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N)
    (hρz : ρ * z = z * ρ) (hρ3 : ρ ^ 3 = 1) (hρ : ∃ g ∈ T, ρ * g * ρ⁻¹ * g⁻¹ ∉ N)
    {t : G} (htN : t ∉ N) :
    z₁ ∈ ⁅T, T⁆ ∨
      {k : G | k ∈ T ∧ k * k = z}.ncard ≠ {k : G | k ∈ T ∧ k * k = t}.ncard ∨
      {k : G | k ∈ T ∧ k * k = z}.ncard ≠ {k : G | k ∈ T ∧ k * k = t * z}.ncard := by
  classical
  have hidx : Nat.card N = 4 * Nat.card (centerIn N) := by rw [hN, hZN]
  have hρ3N : ρ ^ 3 ∈ N := by rw [hρ3]; exact N.one_mem
  have hQ8card : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hkerCard : Nat.card (N.subgroupOf T) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv
  have hTcard : Nat.card ↥T = 8 * Nat.card ↥N := by
    have h := Subgroup.card_ker_mul_card_of_surjective (G := ↥T) (G' := QuaternionGroup 2) hπ
    rw [hker, hkerCard, hQ8card] at h
    rw [← h]; ring
  have hcardT : Nat.card ↥T = 2 ^ 7 := by rw [hTcard, hN]; norm_num
  have hT2 : IsPGroup 2 ↥T := IsPGroup.of_card hcardT
  have hTZ : ∀ g ∈ T, ∀ x ∈ centerIn N, g * x = x * g :=
    commute_of_mem_centerIn_of_quaternion_quotient hNT hNnorm π hπ hker hZN hT2 hρT hρN hρ3N hρ
  have hρZ : ∀ x ∈ centerIn N, ρ * x = x * ρ :=
    commute_of_mem_centerIn_of_pow_three_mem hZN hZ2 hz hz1 hρN hρz hρ3N
  obtain ⟨hZTcard, hZT2⟩ :=
    card_centerIn_eq_eight_and_sq_eq_one_of_quaternion_quotient hNT hNnorm π hπ hker hN hZN hZ2
      hz hz1 hρT hρN hρz hρ3N hρ
  have hZNT : centerIn N ≤ centerIn T := by
    intro u hu
    exact Subgroup.mem_inf.mpr ⟨hNT hu.1, by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hTZ g hg u hu⟩
  have hzT : z ∈ centerIn T := hZNT hz
  have hz₁T : z₁ ∈ centerIn T := hZNT hz₁
  have hNnab : ∃ u ∈ N, ∃ v ∈ N, u * v ≠ v * u := by
    by_contra h
    push Not at h
    have hNle : N ≤ centerIn N := by
      intro u hu
      refine Subgroup.mem_inf.mpr ⟨hu, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (h u hu v hv).symm
    have heq : centerIn N = N := le_antisymm inf_le_left hNle
    have hpos : 0 < Nat.card N := Nat.card_pos
    rw [heq] at hidx
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := hNnab
  have hxT : x ∈ T := hNT hx
  have hyT : y ∈ T := hNT hy
  have hzyx : x * y * x⁻¹ * y⁻¹ = z := by
    rcases hcommN x hx y hy with h | h
    · rw [← commutatorElement_def] at h
      exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h) hxy
    · exact h
  by_cases hθ : ∀ g ∈ T, ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ = 1 ∨ g * n * g⁻¹ * n⁻¹ = z
  ·
    right
    have hsplit : ∀ g ∈ T, ∃ n ∈ N, ∀ m ∈ N, n⁻¹ * g * m = m * (n⁻¹ * g) :=
      exists_inv_mul_commute_of_commutator_eq_one_or_eq hidx hZ2 hz hcommN hTZ hθ
    have hpiN : ∀ (n : G) (hn : n ∈ N), π ⟨n, hNT hn⟩ = 1 := by
      intro n hn
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      exact hn
    have hNpi : ∀ u : ↥T, π u = 1 → (u : G) ∈ N := by
      intro u hu
      rw [← Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker]
      exact hu
    let C : Subgroup G := T ⊓ Subgroup.centralizer (N : Set G)
    have hmemC : ∀ k : G, k ∈ C ↔ k ∈ T ∧ ∀ m ∈ N, m * k = k * m := by
      intro k
      simp only [C, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
    have hcenter_of : ∀ k : ↥T, (∀ m ∈ N, (k : G) * m = m * (k : G)) →
        (π k = 1 ∨ π k = a 2) → (k : G) ∈ centerIn T :=
      fun k hk hkπ => mem_centerIn_of_quaternion_quotient hNT hNnorm π hπ hker hZ2 hTZ hρT hρN
        hρZ hρ3N hρ k hk hkπ
    have hsq_one_of : ∀ k : ↥T, (∀ m ∈ N, (k : G) * m = m * (k : G)) →
        (π k = 1 ∨ π k = a 2) → (k : G) * (k : G) = 1 :=
      fun k hk hkπ => hZT2 (k : G) (hcenter_of k hk hkπ)
    obtain ⟨g₀, hg₀⟩ := hπ (a 1)
    have hg₀T : (g₀ : G) ∈ T := g₀.2
    obtain ⟨n₁, hn₁, hn₁comm⟩ := hsplit g₀ hg₀T
    let v : G := n₁⁻¹ * g₀
    have hvT : v ∈ T := T.mul_mem (T.inv_mem (hNT hn₁)) hg₀T
    have hvC : ∀ m ∈ N, m * v = v * m := fun m hm => (hn₁comm m hm).symm
    have hvπ : π ⟨v, hvT⟩ = a 1 := by
      have h1 : π ⟨v, hvT⟩ = (π ⟨n₁, hNT hn₁⟩)⁻¹ * π g₀ := by
        rw [show (⟨v, hvT⟩ : ↥T) = (⟨n₁, hNT hn₁⟩ : ↥T)⁻¹ * g₀ from rfl]
        rw [map_mul, map_inv]
      rw [h1, hpiN n₁ hn₁, hg₀, inv_one, one_mul]
    let s : G := v * v
    have hsT : s ∈ T := T.mul_mem hvT hvT
    have hsC : ∀ m ∈ N, m * s = s * m := by
      intro m hm
      have h1 : m * v = v * m := hvC m hm
      calc m * (v * v) = (m * v) * v := by group
        _ = (v * m) * v := by rw [h1]
        _ = v * (m * v) := by group
        _ = v * (v * m) := by rw [h1]
        _ = (v * v) * m := by group
    have hsπ : π ⟨s, hsT⟩ = a 2 := by
      have h1 : π ⟨s, hsT⟩ = π ⟨v, hvT⟩ * π ⟨v, hvT⟩ := by
        rw [show (⟨s, hsT⟩ : ↥T) = ⟨v, hvT⟩ * ⟨v, hvT⟩ from rfl, map_mul]
      rw [h1, hvπ]
      decide
    have hsZ : s ∈ centerIn T := hcenter_of ⟨s, hsT⟩ (fun m hm => (hsC m hm).symm) (Or.inr hsπ)
    have hss : s * s = 1 := hZT2 s hsZ
    let b : G := ρ * v * ρ⁻¹
    let b' : G := ρ * b * ρ⁻¹
    have hbT : b ∈ T := hρT v hvT
    have hb'T : b' ∈ T := hρT b hbT
    have hρinv : ρ⁻¹ = ρ ^ 2 := by
      calc ρ⁻¹ = ρ⁻¹ * 1 := by rw [mul_one]
        _ = ρ⁻¹ * ρ ^ 3 := by rw [hρ3]
        _ = ρ ^ 2 := by group
    have hρ2inv : (ρ ^ 2)⁻¹ = ρ := by
      rw [← hρinv]
      simp
    have hρinvN : ∀ m ∈ N, ρ⁻¹ * m * ρ ∈ N := by
      intro m hm
      have hX : ρ ^ 2 * m * (ρ ^ 2)⁻¹ ∈ N := by
        have h1 : ρ * m * ρ⁻¹ ∈ N := hρN m hm
        have h2 : ρ * (ρ * m * ρ⁻¹) * ρ⁻¹ ∈ N := hρN _ h1
        have h3 : ρ ^ 2 * m * (ρ ^ 2)⁻¹ = ρ * (ρ * m * ρ⁻¹) * ρ⁻¹ := by
          rw [pow_two]
          group
        rw [h3]
        exact h2
      have hkey : ρ ^ 2 * m * (ρ ^ 2)⁻¹ = ρ⁻¹ * m * ρ := by
        rw [← hρinv]
        simp
      rwa [hkey] at hX
    have hbC : ∀ m ∈ N, b * m = m * b := by
      intro m hm
      have hm' : ρ⁻¹ * m * ρ ∈ N := hρinvN m hm
      have hvm : v * (ρ⁻¹ * m * ρ) = (ρ⁻¹ * m * ρ) * v := (hvC _ hm').symm
      have hconj : b * m * b⁻¹ = m := by
        have h1 : b * m * b⁻¹ = ρ * (v * (ρ⁻¹ * m * ρ) * v⁻¹) * ρ⁻¹ := by
          rw [show b = ρ * v * ρ⁻¹ from rfl]
          group
        rw [h1]
        have h2 : v * (ρ⁻¹ * m * ρ) * v⁻¹ = ρ⁻¹ * m * ρ := by rw [hvm]; group
        rw [h2]
        group
      calc b * m = (b * m * b⁻¹) * b := by group
        _ = m * b := by rw [hconj]
    have hb'C : ∀ m ∈ N, b' * m = m * b' := by
      intro m hm
      have hm' : ρ⁻¹ * m * ρ ∈ N := hρinvN m hm
      have hbm : b * (ρ⁻¹ * m * ρ) = (ρ⁻¹ * m * ρ) * b := hbC _ hm'
      have hconj : b' * m * b'⁻¹ = m := by
        have h1 : b' * m * b'⁻¹ = ρ * (b * (ρ⁻¹ * m * ρ) * b⁻¹) * ρ⁻¹ := by
          rw [show b' = ρ * b * ρ⁻¹ from rfl]
          group
        rw [h1]
        have h2 : b * (ρ⁻¹ * m * ρ) * b⁻¹ = ρ⁻¹ * m * ρ := by rw [hbm]; group
        rw [h2]
        group
      calc b' * m = (b' * m * b'⁻¹) * b' := by group
        _ = m * b' := by rw [hconj]
    have hρs : ρ * s = s * ρ :=
      commute_of_mem_centerIn_of_quaternion_quotient_of_pow_three_mem hNT π hπ hker hZ2 hρT hρN
        hρZ hρ3N hρ s hsZ
    have hbb : b * b = s := by
      have h1 : b * b = ρ * s * ρ⁻¹ := by
        rw [show b = ρ * v * ρ⁻¹ from rfl, show s = v * v from rfl]
        group
      rw [h1]
      calc ρ * s * ρ⁻¹ = (s * ρ) * ρ⁻¹ := by rw [hρs]
        _ = s := by group
    have hb'b' : b' * b' = s := by
      have h1 : b' * b' = ρ * (b * b) * ρ⁻¹ := by
        rw [show b' = ρ * b * ρ⁻¹ from rfl]
        group
      rw [h1, hbb]
      calc ρ * s * ρ⁻¹ = (s * ρ) * ρ⁻¹ := by rw [hρs]
        _ = s := by group
    obtain ⟨α, hα, hα3, hαne⟩ :=
      exists_quaternionGroup_two_endomorphism_of_conj hNT π hπ hker hρT hρN hρ3N hρ
    have hbπ : π ⟨b, hbT⟩ = α (a 1) := by
      have h := hα ⟨v, hvT⟩
      rw [hvπ] at h
      exact h
    have hb'π : π ⟨b', hb'T⟩ = α (α (a 1)) := by
      have h := hα ⟨b, hbT⟩
      rw [hbπ] at h
      exact h
    obtain ⟨henum, hnc1, hnc2⟩ := quaternionGroup_two_facts_of_pow_three α hα3 hαne
    have hss_inv : s⁻¹ = s := (mul_eq_one_iff_inv_eq).mp hss
    have hvCin : v ∈ C := (hmemC v).mpr ⟨hvT, hvC⟩
    have hbCin : b ∈ C := (hmemC b).mpr ⟨hbT, fun m hm => (hbC m hm).symm⟩
    have hb'Cin : b' ∈ C := (hmemC b').mpr ⟨hb'T, fun m hm => (hb'C m hm).symm⟩
    have hv_inv_sq : v⁻¹ * v⁻¹ = s := by
      have h1 : v⁻¹ * v⁻¹ = (v * v)⁻¹ := by group
      rw [h1, show v * v = s from rfl, hss_inv]
    have hb_inv_sq : b⁻¹ * b⁻¹ = s := by
      have h1 : b⁻¹ * b⁻¹ = (b * b)⁻¹ := by group
      rw [h1, hbb, hss_inv]
    have hb'_inv_sq : b'⁻¹ * b'⁻¹ = s := by
      have h1 : b'⁻¹ * b'⁻¹ = (b' * b')⁻¹ := by group
      rw [h1, hb'b', hss_inv]
    have hvπ' : π ⟨v⁻¹, T.inv_mem hvT⟩ = (a 1)⁻¹ := by
      rw [show (⟨v⁻¹, T.inv_mem hvT⟩ : ↥T) = (⟨v, hvT⟩ : ↥T)⁻¹ from rfl, map_inv, hvπ]
    have hbπ' : π ⟨b⁻¹, T.inv_mem hbT⟩ = (α (a 1))⁻¹ := by
      rw [show (⟨b⁻¹, T.inv_mem hbT⟩ : ↥T) = (⟨b, hbT⟩ : ↥T)⁻¹ from rfl, map_inv, hbπ]
    have hb'π' : π ⟨b'⁻¹, T.inv_mem hb'T⟩ = (α (α (a 1)))⁻¹ := by
      rw [show (⟨b'⁻¹, T.inv_mem hb'T⟩ : ↥T) = (⟨b', hb'T⟩ : ↥T)⁻¹ from rfl, map_inv, hb'π]
    have hfind : ∀ u : QuaternionGroup 2, u ≠ 1 → u ≠ a 2 →
        ∃ r : ↥T, (r : G) ∈ C ∧ (r : G) * (r : G) = s ∧ π r = u := by
      intro u hu1 hu2
      rcases henum u hu1 hu2 with h | h | h | h | h | h
      · exact ⟨⟨v, hvT⟩, hvCin, by rfl, by rw [h]; exact hvπ⟩
      · exact ⟨⟨v⁻¹, T.inv_mem hvT⟩, C.inv_mem hvCin, by simpa using hv_inv_sq,
          by rw [h]; exact hvπ'⟩
      · exact ⟨⟨b, hbT⟩, hbCin, by simpa using hbb, by rw [h]; exact hbπ⟩
      · exact ⟨⟨b⁻¹, T.inv_mem hbT⟩, C.inv_mem hbCin, by simpa using hb_inv_sq,
          by rw [h]; exact hbπ'⟩
      · exact ⟨⟨b', hb'T⟩, hb'Cin, by simpa using hb'b', by rw [h]; exact hb'π⟩
      · exact ⟨⟨b'⁻¹, T.inv_mem hb'T⟩, C.inv_mem hb'Cin, by simpa using hb'_inv_sq,
          by rw [h]; exact hb'π'⟩
    have hsq_of_not : ∀ k : ↥T, (∀ m ∈ N, (k : G) * m = m * (k : G)) →
        π k ≠ 1 → π k ≠ a 2 → (k : G) * (k : G) = s := by
      intro k hk hk1 hk2
      obtain ⟨r, hrC, hr2, hrπ⟩ := hfind (π k) hk1 hk2
      have hkCin : (k : G) ∈ C := (hmemC k).mpr ⟨k.2, fun m hm => (hk m hm).symm⟩
      let p : ↥T := r⁻¹ * k
      have hpC : (p : G) ∈ C := C.mul_mem (C.inv_mem hrC) hkCin
      have hpπ : π p = 1 := by
        have h1 : π p = (π r)⁻¹ * π k := by
          rw [show p = r⁻¹ * k from rfl, map_mul, map_inv]
        rw [h1, hrπ]
        simp
      have hpN : (p : G) ∈ N := hNpi p hpπ
      have hpp : (p : G) * (p : G) = 1 := hZ2 _ (Subgroup.mem_inf.mpr ⟨hpN, hpC.2⟩)
      have hcomm_pr : (p : G) * (r : G) = (r : G) * (p : G) :=
        Subgroup.mem_centralizer_iff.mp hrC.2 (p : G) hpN
      have hk_eq : (k : G) = (r : G) * (p : G) := by
        rw [show (p : G) = (r : G)⁻¹ * (k : G) from rfl]
        group
      calc (k : G) * (k : G) = ((r : G) * (p : G)) * ((r : G) * (p : G)) := by rw [hk_eq]
        _ = ((r : G) * (r : G)) * ((p : G) * (p : G)) := by
              rw [show ((r : G) * (p : G)) * ((r : G) * (p : G)) =
                (r : G) * ((p : G) * (r : G)) * (p : G) from by group, hcomm_pr]
              group
        _ = s * 1 := by rw [hr2, hpp]
        _ = s := mul_one s
    have hsq_mem : ∀ g ∈ T, g * g = 1 ∨ g * g = z ∨ g * g = s ∨ g * g = z * s := by
      intro g hg
      obtain ⟨n, hn, hncomm⟩ := hsplit g hg
      have hkT : n⁻¹ * g ∈ T := T.mul_mem (T.inv_mem (hNT hn)) hg
      have hkC : ∀ m ∈ N, (n⁻¹ * g) * m = m * (n⁻¹ * g) := fun m hm => hncomm m hm
      have hnn : n * n = 1 ∨ n * n = z := hsqN n hn
      have hkk : (n⁻¹ * g) * (n⁻¹ * g) = 1 ∨ (n⁻¹ * g) * (n⁻¹ * g) = s := by
        by_cases h1 : π ⟨n⁻¹ * g, hkT⟩ = 1
        · left; exact hsq_one_of ⟨n⁻¹ * g, hkT⟩ hkC (Or.inl h1)
        · by_cases h2 : π ⟨n⁻¹ * g, hkT⟩ = a 2
          · left; exact hsq_one_of ⟨n⁻¹ * g, hkT⟩ hkC (Or.inr h2)
          · right; exact hsq_of_not ⟨n⁻¹ * g, hkT⟩ hkC h1 h2
      have hcomm_nk : (n⁻¹ * g) * n = n * (n⁻¹ * g) := hkC n hn
      have hgg : g * g = (n * n) * ((n⁻¹ * g) * (n⁻¹ * g)) := by
        have hg_eq : g = n * (n⁻¹ * g) := by group
        conv_lhs => rw [hg_eq]
        calc (n * (n⁻¹ * g)) * (n * (n⁻¹ * g))
            = n * ((n⁻¹ * g) * n) * (n⁻¹ * g) := by group
          _ = n * (n * (n⁻¹ * g)) * (n⁻¹ * g) := by rw [hcomm_nk]
          _ = (n * n) * ((n⁻¹ * g) * (n⁻¹ * g)) := by group
      rcases hnn with h | h <;> rcases hkk with h' | h' <;> rw [hgg, h, h']
      · left; rw [one_mul]
      · right; right; left; rw [one_mul]
      · right; left; rw [mul_one]
      · right; right; right; rfl
    have hex : ∃ n₀ ∈ N, n₀ * n₀ = z := by
      by_contra h
      push Not at h
      have hall : ∀ n ∈ N, n * n = 1 := by
        intro n hn
        rcases hsqN n hn with h1 | h1
        · exact h1
        · exact absurd h1 (h n hn)
      have hNcomm : ∀ u ∈ N, ∀ w ∈ N, u * w = w * u := by
        intro u hu w hw
        have h1 : (u * w) * (u * w) = 1 := hall _ (N.mul_mem hu hw)
        have h2 : u * u = 1 := hall u hu
        have h3 : w * w = 1 := hall w hw
        have h4 : w * u * w = u := by
          calc w * u * w = (u * u) * (w * u * w) := by rw [h2, one_mul]
            _ = u * (u * w * u * w) := by group
            _ = u * (u * w * (u * w)) := by group
            _ = u * 1 := by rw [h1]
            _ = u := mul_one u
        have h5 : (w * u * w) * w = w * u := by
          calc (w * u * w) * w = w * u * (w * w) := by group
            _ = w * u * 1 := by rw [h3]
            _ = w * u := mul_one _
        calc u * w = (w * u * w) * w := by rw [h4]
          _ = w * u := h5
      exact hxy (hNcomm x hx y hy)
    obtain ⟨n₀, hn₀N, hn₀z⟩ := hex
    set A : Set G := {k : G | k ∈ T ∧ k * k = z} with hAdef
    have hzss : s * z = z * s := (Subgroup.mem_centralizer_iff.mp hsZ.2 z hzT.1).symm
    have hA_lt : A.ncard < {k : G | k ∈ T ∧ k * k = z * s}.ncard := by
      have hinj : Function.Injective (fun g : G => g * v) := fun u w h => mul_right_cancel h
      have hsub : (fun g : G => g * v) '' A ⊆ {k : G | k ∈ T ∧ k * k = z * s} := by
        rintro _ ⟨g, hg, rfl⟩
        obtain ⟨hgT, hgg⟩ := hg
        refine ⟨T.mul_mem hgT hvT, ?_⟩
        have hπg : π ⟨g, hgT⟩ * π ⟨g, hgT⟩ = 1 := by
          have h1 : π ⟨g * g, T.mul_mem hgT hgT⟩ = π ⟨g, hgT⟩ * π ⟨g, hgT⟩ := by
            rw [show (⟨g * g, T.mul_mem hgT hgT⟩ : ↥T) = ⟨g, hgT⟩ * ⟨g, hgT⟩ from rfl, map_mul]
          have h2 : (⟨g * g, T.mul_mem hgT hgT⟩ : ↥T) = ⟨z, hNT hz.1⟩ := Subtype.ext hgg
          rw [← h1, h2, hpiN z hz.1]
        have hπg12 : π ⟨g, hgT⟩ = 1 ∨ π ⟨g, hgT⟩ = a 2 := quaternionGroup_two_sq_eq_one _ hπg
        obtain ⟨n, hn, hncomm⟩ := hsplit g hgT
        have hkT : n⁻¹ * g ∈ T := T.mul_mem (T.inv_mem (hNT hn)) hgT
        have hkC : ∀ m ∈ N, (n⁻¹ * g) * m = m * (n⁻¹ * g) := fun m hm => hncomm m hm
        have hg_eq : g = n * (n⁻¹ * g) := by group
        have hπk : π ⟨n⁻¹ * g, hkT⟩ = π ⟨g, hgT⟩ := by
          have h1 : π ⟨n⁻¹ * g, hkT⟩ = (π ⟨n, hNT hn⟩)⁻¹ * π ⟨g, hgT⟩ := by
            rw [show (⟨n⁻¹ * g, hkT⟩ : ↥T) = (⟨n, hNT hn⟩ : ↥T)⁻¹ * ⟨g, hgT⟩ from rfl,
              map_mul, map_inv]
          rw [h1, hpiN n hn, inv_one, one_mul]
        have hkZ : (n⁻¹ * g) ∈ centerIn T :=
          hcenter_of ⟨n⁻¹ * g, hkT⟩ hkC (by rw [hπk]; exact hπg12)
        have hgv : g * v = v * g := by
          have hnv : n * v = v * n := hvC n hn
          have hkv : (n⁻¹ * g) * v = v * (n⁻¹ * g) :=
            (Subgroup.mem_centralizer_iff.mp hkZ.2 v hvT).symm
          rw [hg_eq]
          calc n * (n⁻¹ * g) * v = n * ((n⁻¹ * g) * v) := by group
            _ = n * (v * (n⁻¹ * g)) := by rw [hkv]
            _ = (n * v) * (n⁻¹ * g) := by group
            _ = (v * n) * (n⁻¹ * g) := by rw [hnv]
            _ = v * (n * (n⁻¹ * g)) := by group
        have hsq : (g * v) * (g * v) = z * s := by
          calc (g * v) * (g * v) = g * (v * g) * v := by group
            _ = g * (g * v) * v := by rw [← hgv]
            _ = (g * g) * (v * v) := by group
            _ = z * s := by rw [hgg]
        exact hsq
      have hstrict : ∃ y ∈ {k : G | k ∈ T ∧ k * k = z * s}, ∀ g ∈ A, g * v ≠ y := by
        refine ⟨n₀ * b, ⟨T.mul_mem (hNT hn₀N) hbT, ?_⟩, ?_⟩
        · have hnb : n₀ * b = b * n₀ := (hbC n₀ hn₀N).symm
          have h1 : (n₀ * b) * (n₀ * b) = (n₀ * n₀) * (b * b) := by
            calc (n₀ * b) * (n₀ * b) = n₀ * (b * n₀) * b := by group
              _ = n₀ * (n₀ * b) * b := by rw [hnb]
              _ = (n₀ * n₀) * (b * b) := by group
          rw [h1, hn₀z, hbb]
        · rintro g hg hgv
          have hgT : g ∈ T := hg.1
          have hgg : g * g = z := hg.2
          have hπg : π ⟨g, hgT⟩ * π ⟨g, hgT⟩ = 1 := by
            have h1 : π ⟨g * g, T.mul_mem hgT hgT⟩ = π ⟨g, hgT⟩ * π ⟨g, hgT⟩ := by
              rw [show (⟨g * g, T.mul_mem hgT hgT⟩ : ↥T) = ⟨g, hgT⟩ * ⟨g, hgT⟩ from rfl, map_mul]
            have h2 : (⟨g * g, T.mul_mem hgT hgT⟩ : ↥T) = ⟨z, hNT hz.1⟩ := Subtype.ext hgg
            rw [← h1, h2, hpiN z hz.1]
          have hπg12 : π ⟨g, hgT⟩ = 1 ∨ π ⟨g, hgT⟩ = a 2 := quaternionGroup_two_sq_eq_one _ hπg
          have hπnb : π ⟨n₀ * b, T.mul_mem (hNT hn₀N) hbT⟩ = α (a 1) := by
            have h1 : π ⟨n₀ * b, T.mul_mem (hNT hn₀N) hbT⟩ =
                π ⟨n₀, hNT hn₀N⟩ * π ⟨b, hbT⟩ := by
              rw [show (⟨n₀ * b, T.mul_mem (hNT hn₀N) hbT⟩ : ↥T) =
                ⟨n₀, hNT hn₀N⟩ * ⟨b, hbT⟩ from rfl, map_mul]
            rw [h1, hpiN n₀ hn₀N, hbπ, one_mul]
          have hπgv : π ⟨g * v, T.mul_mem hgT hvT⟩ = π ⟨g, hgT⟩ * a 1 := by
            have h1 : π ⟨g * v, T.mul_mem hgT hvT⟩ = π ⟨g, hgT⟩ * π ⟨v, hvT⟩ := by
              rw [show (⟨g * v, T.mul_mem hgT hvT⟩ : ↥T) = ⟨g, hgT⟩ * ⟨v, hvT⟩ from rfl,
                map_mul]
            rw [h1, hvπ]
          have heq : α (a 1) = π ⟨g, hgT⟩ * a 1 := by
            have h2 : (⟨n₀ * b, T.mul_mem (hNT hn₀N) hbT⟩ : ↥T) =
                ⟨g * v, T.mul_mem hgT hvT⟩ := Subtype.ext hgv.symm
            rw [← hπnb, h2, hπgv]
          rcases hπg12 with h1 | h1
          · have h2 : α (a 1) * (a 1)⁻¹ = 1 := by rw [heq, h1]; group
            exact hnc1 h2
          · have h2 : α (a 1) * (a 1)⁻¹ = a 2 := by
              rw [heq, h1]
              group
            exact hnc2 h2
      have hssub : (fun g : G => g * v) '' A ⊂ {k : G | k ∈ T ∧ k * k = z * s} := by
        refine ⟨hsub, ?_⟩
        intro hBA
        obtain ⟨y, hy, hyw⟩ := hstrict
        obtain ⟨g, hg, hgy⟩ := hBA hy
        exact hyw g hg hgy
      have h1 := Set.ncard_lt_ncard hssub (Set.toFinite _)
      rwa [Set.ncard_image_of_injective A hinj] at h1
    by_cases hts : t = s
    · right
      have htz : t * z = z * s := by rw [hts, hzss]
      rw [htz]
      exact ne_of_lt hA_lt
    · by_cases htzs : t = z * s
      · left
        rw [htzs]
        exact ne_of_lt hA_lt
      · left
        have hempty : {k : G | k ∈ T ∧ k * k = t} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro k hk
          have hsq := hsq_mem k hk.1
          rw [hk.2] at hsq
          rcases hsq with h | h | h | h
          · exact htN (by rw [h]; exact N.one_mem)
          · exact htN (by rw [h]; exact hz.1)
          · exact hts h
          · exact htzs h
        rw [hempty, Set.ncard_empty]
        exact ne_of_gt (by
          rw [Set.ncard_pos (Set.toFinite A)]
          exact ⟨n₀, hNT hn₀N, hn₀z⟩)
  ·
    push Not at hθ
    obtain ⟨g, hg, n, hn, hgn⟩ := hθ
    left
    have hcZ : g * n * g⁻¹ * n⁻¹ ∈ centerIn N :=
      commutator_mem_centerIn_of_quaternion_quotient hNT hNnorm π hπ hker hidx hT2 hρT hρN hρ3N
        hρ g hg n hn
    have hc1 : g * n * g⁻¹ * n⁻¹ ≠ 1 := fun h => hgn.1 h
    have hcz : g * n * g⁻¹ * n⁻¹ ≠ z := fun h => hgn.2 h
    have hcases := centerIn_cases_of_card_eq_four hZN hZ2 hz hz1 hz₁ hz₁1 hz₁z hcZ
    have hz_mem : z ∈ ⁅T, T⁆ := by
      have h := Subgroup.commutator_mem_commutator (H₁ := T) (H₂ := T) hxT hyT
      rw [commutatorElement_def] at h
      rwa [hzyx] at h
    have hc_mem : g * n * g⁻¹ * n⁻¹ ∈ ⁅T, T⁆ := by
      have h := Subgroup.commutator_mem_commutator (H₁ := T) (H₂ := T) hg (hNT hn)
      rwa [commutatorElement_def] at h
    rcases hcases with h1 | h1 | h1 | h1
    · exact absurd h1 hc1
    · exact absurd h1 hcz
    · rwa [h1] at hc_mem
    · have hz₁_eq : z₁ = (g * n * g⁻¹ * n⁻¹) * z := by
        rw [h1]
        have hzz₁ : z₁ * z = z * z₁ := by
          exact Subgroup.mem_centralizer_iff.mp hz.2 z₁ hz₁.1
        calc z₁ = (z * z) * z₁ := by rw [hZ2 z hz, one_mul]
          _ = z * (z * z₁) := by group
          _ = z * (z₁ * z) := by rw [← hzz₁]
          _ = z * z₁ * z := by group
      rw [hz₁_eq]
      exact (⁅T, T⁆).mul_mem hc_mem hz_mem

end CFSG.GroupTheory
