module

public import CFSG.Assembly.Defs

public section

namespace CFSG.Assembly.InvolutionGraph

variable {G : Type*} [Group G]

@[expose] def conjV (g : G) (v : {t : G // orderOf t = 2}) : {t : G // orderOf t = 2} :=
  ⟨g⁻¹ * v * g, by
    have := (MulAut.conj g⁻¹).orderOf_eq (v : G)
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [this, v.2]⟩

@[simp] theorem conjV_val (g : G) (v : {t : G // orderOf t = 2}) :
    (conjV g v : G) = g⁻¹ * v * g := rfl

@[expose] def conjHom (g : G) : involutionGraph G →g involutionGraph G where
  toFun := conjV g
  map_rel' := by
    intro u v h
    rw [involutionGraph, SimpleGraph.fromRel_adj] at h ⊢
    refine ⟨fun huv => h.1 (Subtype.ext ?_), ?_⟩
    · simpa using congrArg Subtype.val huv
    · rcases h.2 with h | h
      · left
        simp only [conjV_val, mul_assoc, mul_inv_cancel_left]
        rw [← mul_assoc (u : G), h, mul_assoc]
      · right
        simp only [conjV_val, mul_assoc, mul_inv_cancel_left]
        rw [← mul_assoc (v : G), h, mul_assoc]

theorem reachable_of_commute {u v : {t : G // orderOf t = 2}} (h : (u : G) * v = v * u) :
    (involutionGraph G).Reachable u v := by
  by_cases huv : u = v
  · exact huv ▸ SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by
      rw [involutionGraph, SimpleGraph.fromRel_adj]
      exact ⟨huv, Or.inl h⟩)

variable (Δ : (involutionGraph G).ConnectedComponent)

@[expose] def compSet : Set G := Subtype.val '' Δ.supp

variable {Δ}

theorem mem_compSet {x : G} (hx : orderOf x = 2) :
    x ∈ compSet Δ ↔ (involutionGraph G).connectedComponentMk ⟨x, hx⟩ = Δ := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem orderOf_of_mem_compSet {x : G} (hx : x ∈ compSet Δ) : orderOf x = 2 := by
  obtain ⟨v, -, rfl⟩ := hx
  exact v.2

theorem conj_mem_compSet {g v : G} (hv : v ∈ compSet Δ) (hgv : g⁻¹ * v * g ∈ compSet Δ)
    {t : G} (ht : t ∈ compSet Δ) : g⁻¹ * t * g ∈ compSet Δ := by
  obtain ⟨v, hvΔ, rfl⟩ := hv
  obtain ⟨t, htΔ, rfl⟩ := ht
  have hreach : (involutionGraph G).Reachable v t :=
    SimpleGraph.ConnectedComponent.exact (hvΔ.trans htΔ.symm)
  have hmap := hreach.map (conjHom g)
  have hgv' : (involutionGraph G).connectedComponentMk (conjV g v) = Δ :=
    (mem_compSet (conjV g v).2).mp hgv
  refine (mem_compSet (conjV g t).2).mpr ?_
  exact (SimpleGraph.ConnectedComponent.sound hmap).symm.trans hgv'

variable {M : Subgroup G}

@[expose] def IsStabilizer (Δ : (involutionGraph G).ConnectedComponent) (M : Subgroup G) : Prop :=
  ∀ g : G, g ∈ M ↔ (fun t => g⁻¹ * t * g) '' compSet Δ = compSet Δ

theorem conj_mem_of_mem (hM : IsStabilizer Δ M) {g t : G} (hg : g ∈ M) (ht : t ∈ compSet Δ) :
    g⁻¹ * t * g ∈ compSet Δ := by
  rw [← (hM g).mp hg]
  exact ⟨t, ht, rfl⟩

theorem mem_of_conj_mem (hM : IsStabilizer Δ M) {g v : G} (hv : v ∈ compSet Δ)
    (hgv : g⁻¹ * v * g ∈ compSet Δ) : g ∈ M := by
  rw [hM]
  apply Set.Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact conj_mem_compSet hv hgv ht
  · intro t ht
    refine ⟨g * t * g⁻¹, ?_, by group⟩
    have h := conj_mem_compSet (g := g⁻¹) hgv (by simpa [mul_assoc] using hv) ht
    simpa using h

theorem mem_of_mem_compSet (hM : IsStabilizer Δ M) {s : G} (hs : s ∈ compSet Δ) : s ∈ M := by
  have hs2 : s * s = 1 := by
    rw [← sq, ← orderOf_of_mem_compSet hs, pow_orderOf_eq_one]
  refine mem_of_conj_mem hM hs ?_
  rwa [show s⁻¹ * s * s = s by group]

theorem involution_mem_of_mem [Finite G] (hM : IsStabilizer Δ M) {x : G} (hx : orderOf x = 2)
    (hxM : x ∈ M) : x ∈ compSet Δ := by
  obtain ⟨⟨s, hs⟩, hsΔ⟩ := Δ.nonempty_supp
  have hsC : s ∈ compSet Δ := ⟨⟨s, hs⟩, hsΔ, rfl⟩
  have hsM := mem_of_mem_compSet hM hsC
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hx2 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  set w := s * x with hw
  have hsw : ∀ j : ℕ, s * w ^ j * s = (w ^ j)⁻¹ := by
    intro j
    have h1 : s * w * s = w⁻¹ := by
      rw [hw, mul_inv_rev, hsi, hxi, ← mul_assoc, hs2, one_mul]
    have := map_pow (MulAut.conj s) w j
    simp only [MulAut.conj_apply, hsi, h1] at this
    rw [this, inv_pow]
  have hxw : ∀ j : ℕ, x * w ^ j * x = (w ^ j)⁻¹ := by
    intro j
    have h1 : x * w * x = w⁻¹ := by
      rw [hw, mul_inv_rev, hsi, hxi, mul_assoc, mul_assoc, hx2, mul_one]
    have := map_pow (MulAut.conj x) w j
    simp only [MulAut.conj_apply, hxi, h1] at this
    rw [this, inv_pow]
  have hm : 0 < orderOf w := orderOf_pos w
  rcases Nat.even_or_odd (orderOf w) with ⟨k, hk⟩ | ⟨k, hk⟩
  ·
    set z := w ^ k
    have hz2 : z * z = 1 := by rw [← pow_add, ← hk, pow_orderOf_eq_one]
    have hz1 : z ≠ 1 := fun h => by
      have := orderOf_le_of_pow_eq_one (by omega) h
      omega
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [sq, hz2]) hz1
    have hcs : s * z = z * s := by
      have := hsw k
      rw [hzi] at this
      calc s * z = s * z * s * s := by rw [mul_assoc _ s s, hs2, mul_one]
        _ = z * s := by rw [this]
    have hcx : z * x = x * z := by
      have := hxw k
      rw [hzi] at this
      calc z * x = x * z * x * x := by rw [this]
        _ = x * z := by rw [mul_assoc _ x x, hx2, mul_one]
    have hreach : (involutionGraph G).Reachable ⟨s, hs⟩ ⟨x, hx⟩ :=
      (reachable_of_commute (u := ⟨s, hs⟩) (v := ⟨z, hzo⟩) hcs).trans
        (reachable_of_commute (u := ⟨z, hzo⟩) (v := ⟨x, hx⟩) hcx)
    rw [mem_compSet hx, ← hsΔ]
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  ·
    have hwM : w ∈ M := M.mul_mem hsM hxM
    have hcM : w ^ k * s ∈ M := M.mul_mem (M.pow_mem hwM k) hsM
    have h2k : w ^ (2 * k) = w⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, ← hk, pow_orderOf_eq_one]
    have hconj : (w ^ k * s)⁻¹ * s * (w ^ k * s) = x := by
      have hinv : (w ^ k)⁻¹ = s * w ^ k * s := (hsw k).symm
      calc (w ^ k * s)⁻¹ * s * (w ^ k * s) = s * (w ^ k)⁻¹ * s * w ^ k * s := by
            rw [mul_inv_rev, hsi]; group
        _ = (s * s) * w ^ k * (s * s) * w ^ k * s := by rw [hinv]; group
        _ = w ^ (2 * k) * s := by rw [hs2, one_mul, mul_one, two_mul, pow_add]
        _ = x := by rw [h2k, hw, mul_inv_rev, hsi, hxi, mul_assoc, hs2, mul_one]
    rw [← hconj]
    exact conj_mem_of_mem hM hcM hsC

theorem stronglyEmbedded_of_ne [Finite G] (hM : IsStabilizer Δ M)
    {Δ' : (involutionGraph G).ConnectedComponent} (hne : Δ' ≠ Δ) :
    M ≠ ⊤ ∧ Even (Nat.card M) ∧
      ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom)) := by
  refine ⟨fun htop => ?_, ?_, fun g hg => ?_⟩
  · obtain ⟨v, hv⟩ := Δ'.nonempty_supp
    have := involution_mem_of_mem hM v.2 (htop ▸ Subgroup.mem_top (v : G))
    rw [mem_compSet v.2] at this
    exact hne (hv.symm.trans this)
  · obtain ⟨⟨s, hs⟩, hsΔ⟩ := Δ.nonempty_supp
    have hsM := mem_of_mem_compSet hM (s := s) ⟨⟨s, hs⟩, hsΔ, rfl⟩
    rw [even_iff_two_dvd, ← hs, ← Subgroup.orderOf_mk s hsM]
    exact orderOf_dvd_natCard _
  · by_contra hodd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom))
      2 (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd))
    have hyo : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
    obtain ⟨hyM, m, hmM, hmy⟩ := y.2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hmy
    have hmo : orderOf m = 2 := by
      rw [← hyo, ← hmy]
      have := (MulAut.conj g⁻¹).orderOf_eq m
      simpa using this.symm
    have hyC := involution_mem_of_mem hM hyo hyM
    have hmC := involution_mem_of_mem hM hmo hmM
    exact hg (mem_of_conj_mem hM hmC (by rwa [hmy]))

theorem not_preconnected_of_stronglyEmbedded [Finite G] (M : Subgroup G)
    (hM : M ≠ ⊤ ∧ Even (Nat.card M) ∧
      ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom))) :
    ¬ (involutionGraph G).Preconnected := by
  obtain ⟨hMtop, hMeven, hModd⟩ := hM
  have hcent : ∀ t ∈ M, orderOf t = 2 → ∀ g : G, g * t = t * g → g ∈ M := by
    intro t htM ht g hgt
    by_contra hg
    refine Nat.not_odd_iff_even.mpr ?_ (hModd g hg)
    rw [even_iff_two_dvd, ← ht]
    have hmem : t ∈ M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom :=
      ⟨htM, t, htM, by simp [mul_assoc, ← hgt]⟩
    rw [← Subgroup.orderOf_mk t hmem]
    exact orderOf_dvd_natCard _
  obtain ⟨⟨t, htM⟩, ht⟩ := exists_prime_orderOf_dvd_card' (G := M) 2
    (even_iff_two_dvd.mp hMeven)
  rw [Subgroup.orderOf_mk] at ht
  obtain ⟨g, hg⟩ : ∃ g, g ∉ M := by
    by_contra h
    push Not at h
    exact hMtop (eq_top_iff.mpr fun g _ => h g)
  let u : {t : G // orderOf t = 2} := conjV g ⟨t, ht⟩
  have hu : (u : G) ∉ M := by
    intro huM
    refine Nat.not_odd_iff_even.mpr ?_ (hModd g hg)
    rw [even_iff_two_dvd, ← u.2]
    have hmem : (u : G) ∈ M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom :=
      ⟨huM, t, htM, by simp [u]⟩
    rw [← Subgroup.orderOf_mk (u : G) hmem]
    exact orderOf_dvd_natCard _
  intro hconn
  obtain ⟨p⟩ := hconn ⟨t, ht⟩ u
  have key : ∀ (a b : {t : G // orderOf t = 2}) (p : (involutionGraph G).Walk a b),
      (a : G) ∈ M → (b : G) ∈ M := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a' b' c' hadj _ ih =>
      intro haM
      apply ih
      rw [involutionGraph, SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with h | h
      · exact hcent _ haM a'.2 _ h.symm
      · exact hcent _ haM a'.2 _ h
  exact hu (key _ _ p htM)

end CFSG.Assembly.InvolutionGraph
