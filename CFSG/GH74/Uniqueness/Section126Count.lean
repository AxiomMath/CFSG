module

public import CFSG.GH74.Uniqueness.Section126
public import CFSG.GH74.Uniqueness.Section126Dihedral

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X} {c : Ctx12 Z M} {n i : ℕ}

theorem lemma126_isConj_of_commute (S : ZDSetup X Z M) (h : LData c n i) {u : X} (huD : u ∈ c.D)
    (hu2 : orderOf u = 2) (ha : zHull Z M ≤ centralizer ({u} : Set X))
    (hfirst : ∀ x ∈ deltaSet Z M u, x = u ∨ IsConj (u * c.z) x) {z'' : X} (hz'' : z'' ∈ Z)
    (hcomm : u * z'' = z'' * u) : IsConj (u * c.z) (u * z'') := by
  have huM : u ∈ M := (Subgroup.mem_inf.mp huD).1
  obtain ⟨g₀, hg₀⟩ := S.prodDisc.exists_conj_mem_subgroup S.invariant hz''
  have hz₀Z : g₀⁻¹ * z'' * g₀ ∈ Z := S.invariant.2 z'' hz'' g₀
  have hu₀c : (g₀⁻¹ * u * g₀) * (g₀⁻¹ * z'' * g₀) = (g₀⁻¹ * z'' * g₀) * (g₀⁻¹ * u * g₀) := by
    calc (g₀⁻¹ * u * g₀) * (g₀⁻¹ * z'' * g₀) = g₀⁻¹ * (u * z'') * g₀ := by group
      _ = g₀⁻¹ * (z'' * u) * g₀ := by rw [hcomm]
      _ = (g₀⁻¹ * z'' * g₀) * (g₀⁻¹ * u * g₀) := by group
  have hu₀M : g₀⁻¹ * u * g₀ ∈ M :=
    S.prodDisc.centralizer_le_of_mem hz₀Z hg₀ (Subgroup.mem_centralizer_singleton_iff.mpr hu₀c)
  obtain ⟨m, hm, hmu⟩ := S.exists_mem_conj_of_isPGroup huM
    (sec126_isPGroup_zpowers_of_orderOf_eq_two hu2) hu₀M
  have hz₀H : g₀⁻¹ * z'' * g₀ ∈ zHull Z M := Subgroup.subset_closure ⟨hz₀Z, hg₀⟩
  have hz₁H : m * (g₀⁻¹ * z'' * g₀) * m⁻¹ ∈ zHull Z M := h.sec126_conj_mem_zHull' hm hz₀H
  have hz₁1 : m * (g₀⁻¹ * z'' * g₀) * m⁻¹ ≠ 1 := by
    intro h1
    have h2 : g₀⁻¹ * z'' * g₀ = 1 := by
      calc g₀⁻¹ * z'' * g₀ = m⁻¹ * (m * (g₀⁻¹ * z'' * g₀) * m⁻¹) * m := by group
        _ = 1 := by rw [h1]; group
    have h3 := S.invariant.1 _ hz₀Z
    rw [h2, orderOf_one] at h3
    omega
  have hz₁c : (m * (g₀⁻¹ * z'' * g₀) * m⁻¹) * u = u * (m * (g₀⁻¹ * z'' * g₀) * m⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (ha hz₁H)
  have hmem : u * (m * (g₀⁻¹ * z'' * g₀) * m⁻¹) ∈ deltaSet Z M u :=
    ⟨m * (g₀⁻¹ * z'' * g₀) * m⁻¹, Subgroup.mem_inf.mpr ⟨ha hz₁H, hz₁H⟩, hz₁c.symm⟩
  have hne : u * (m * (g₀⁻¹ * z'' * g₀) * m⁻¹) ≠ u := by
    intro h1
    apply hz₁1
    have h2 : u * (m * (g₀⁻¹ * z'' * g₀) * m⁻¹) = u * 1 := by rw [h1, mul_one]
    exact mul_left_cancel h2
  have h1 : IsConj (u * c.z) (u * (m * (g₀⁻¹ * z'' * g₀) * m⁻¹)) :=
    (hfirst _ hmem).resolve_left hne
  have e : g₀⁻¹ * (u * z'') * g₀ = m⁻¹ * (u * (m * (g₀⁻¹ * z'' * g₀) * m⁻¹)) * m := by
    calc g₀⁻¹ * (u * z'') * g₀ = (g₀⁻¹ * u * g₀) * (g₀⁻¹ * z'' * g₀) := by group
      _ = (m⁻¹ * u * m) * (g₀⁻¹ * z'' * g₀) := by rw [hmu]
      _ = m⁻¹ * (u * (m * (g₀⁻¹ * z'' * g₀) * m⁻¹)) * m := by group
  have h2 : IsConj (u * (m * (g₀⁻¹ * z'' * g₀) * m⁻¹)) (u * z'') := by
    refine isConj_iff.mpr ⟨g₀ * m⁻¹, ?_⟩
    calc g₀ * m⁻¹ * (u * (m * (g₀⁻¹ * z'' * g₀) * m⁻¹)) * (g₀ * m⁻¹)⁻¹
        = g₀ * (m⁻¹ * (u * (m * (g₀⁻¹ * z'' * g₀) * m⁻¹)) * m) * g₀⁻¹ := by group
      _ = g₀ * (g₀⁻¹ * (u * z'') * g₀) * g₀⁻¹ := by rw [e]
      _ = u * z'' := by group
  exact h1.trans h2

theorem lemma126_odd (S : ZDSetup X Z M) (h : LData c n i) {u : X} (huD : u ∈ c.D)
    (hu2 : orderOf u = 2) (ha : zHull Z M ≤ centralizer ({u} : Set X)) {z' : X} (hz' : z' ∈ Z)
    {d : ℕ} (hd : orderOf (u * z') = 2 * d) (hd0 : d ≠ 0) : Odd d := by
  have huM : u ∈ M := (Subgroup.mem_inf.mp huD).1
  have hz2 : orderOf c.z = 2 := S.invariant.1 c.z c.hz
  obtain ⟨g, hg⟩ := isConj_iff.mp (S.prodDisc.isConj_of_mem S.invariant c.hz hz')
  have hzg : c.z = g⁻¹ * z' * g := by rw [← hg]; group
  have hũ2 : orderOf (g⁻¹ * u * g) = 2 := sec126_orderOf_conj_eq_two hu2 g
  have hũZ : g⁻¹ * u * g ∉ Z := by
    intro hmem
    apply S.sec126_not_mem_of_mem_dGrp c.htM huD
    have := S.invariant.2 _ hmem g⁻¹
    simpa [mul_assoc] using this
  obtain ⟨hcard, hsec⟩ := h.dihedral (g⁻¹ * u * g) hũ2 hũZ
  have hordũ : orderOf (g⁻¹ * u * g * c.z) = 2 * d := by
    have : g⁻¹ * u * g * c.z = g⁻¹ * (u * z') * g := by rw [hzg]; group
    rw [this, sec126_orderOf_conj_inv_eq, hd]
  have hcardeq : Nat.card ↥(closure ({g⁻¹ * u * g, c.z} : Set X)) = 4 * d := by
    rw [card_closure_pair_involutions hũ2 hz2, hordũ]
    ring
  rcases hcard with h8 | ⟨k, hk, hk4⟩
  · exfalso
    have hd2 : d = 2 := by omega
    subst hd2
    obtain ⟨-, hũM, hũc⟩ := hsec ((g⁻¹ * u * g * c.z) ^ 2)
      (Subgroup.npow_mem_zpowers _ _) (orderOf_pow_half hordũ (by omega)) h8
    obtain ⟨m, hm, hmu⟩ := S.exists_mem_conj_of_isPGroup huM
      (sec126_isPGroup_zpowers_of_orderOf_eq_two hu2) hũM
    apply hũc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [← hmu]
    exact h.sec126_centralizes_conj hm
      (fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (ha hy)) x hx
  · have : d = k := by omega
    rwa [this]

theorem lemma126_c_core (S : ZDSetup X Z M) (h : LData c n i) {u : X} (huD : u ∈ c.D)
    (hu2 : orderOf u = 2) (ha : zHull Z M ≤ centralizer ({u} : Set X))
    (hfirst : ∀ x ∈ deltaSet Z M u, x = u ∨ IsConj (u * c.z) x) {z' : X} (hz' : z' ∈ Z) {w : X}
    (hw2 : orderOf w = 2) (hw : w ∈ zpowers (u * z')) : IsConj (u * c.z) w := by
  have hu1 : u * u = 1 := sec126_involution_mul_self hu2
  have hz'1 : z' * z' = 1 := S.invariant.mul_self_eq_one hz'
  have huZ := S.sec126_not_mem_of_mem_dGrp c.htM huD
  have hnc : ¬ IsConj u z' := fun hc => huZ (S.invariant.isConj_mem hz' hc)
  obtain ⟨d, hd0, hd⟩ := exists_orderOf_mul_eq_two_mul hu1 hz'1 hnc
  have hodd : Odd d := lemma126_odd S h huD hu2 ha hz' hd hd0
  have hwd : w = (u * z') ^ d := (mem_zpowers_iff_eq_pow_half hd hd0 hw2).mp hw
  obtain ⟨x, -, hx⟩ := exists_conj_mul_pow_of_odd_half hu1 hz'1 hd hodd
  obtain ⟨-, -, huv, -, -⟩ := dihedral_even hu1 hz'1 (Nat.pos_of_ne_zero hd0) hd
  have hz''Z : x⁻¹ * z' * x ∈ Z := S.invariant.2 z' hz' x
  have hz''w : x⁻¹ * z' * x = u * w := by rw [hx, hwd]
  have huv' : u * w = w * u := by rw [hwd]; exact huv
  have hcomm : u * (x⁻¹ * z' * x) = (x⁻¹ * z' * x) * u := by
    rw [hz''w]
    have e1 : u * (u * w) = w := by rw [← mul_assoc, hu1, one_mul]
    have e2 : (u * w) * u = w := by rw [huv', mul_assoc, hu1, mul_one]
    rw [e1, e2]
  have hfin := lemma126_isConj_of_commute S h huD hu2 ha hfirst hz''Z hcomm
  rwa [hz''w, ← mul_assoc, hu1, one_mul] at hfin

theorem lemma126_c (S : ZDSetup X Z M) (h : LData c n i) {u : X} (huD : u ∈ c.D)
    (hu2 : orderOf u = 2) (ha : zHull Z M ≤ centralizer ({u} : Set X))
    (hfirst : ∀ x ∈ deltaSet Z M u, x = u ∨ IsConj (u * c.z) x) :
    ∀ w : X, orderOf w = 2 → ¬ IsConj (u * c.z) w → thompsonPairCount u c.z w = 0 := by
  intro w hw2 hwn
  have hempty : thompsonPairs u c.z w = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨u', z'⟩ ⟨hu'c, hz'c, hwmem⟩
    have hu'c' : IsConj u u' := hu'c
    have hz'c' : IsConj c.z z' := hz'c
    have hwmem' : w ∈ zpowers (u' * z') := hwmem
    obtain ⟨g, hg⟩ := isConj_iff.mp hu'c'
    have hz'Z : z' ∈ Z := S.invariant.isConj_mem c.hz hz'c'.symm
    have hz''Z : g⁻¹ * z' * g ∈ Z := S.invariant.2 z' hz'Z g
    have hmem' : g⁻¹ * w * g ∈ zpowers (u * (g⁻¹ * z' * g)) := by
      have := sec126_mem_zpowers_conj g hwmem'
      have e : g⁻¹ * (u' * z') * g = u * (g⁻¹ * z' * g) := by rw [← hg]; group
      rwa [e] at this
    have hconj := lemma126_c_core S h huD hu2 ha hfirst hz''Z
      (sec126_orderOf_conj_eq_two hw2 g) hmem'
    exact hwn (hconj.trans (isConj_iff.mpr ⟨g, by group⟩))
  rw [thompsonPairCount, hempty]
  simp

theorem lemma126_d (S : ZDSetup X Z M) (h : LData c n i) {u : X} (huD : u ∈ c.D)
    (hu2 : orderOf u = 2) (ha : zHull Z M ≤ centralizer ({u} : Set X))
    (hb : ∀ u' ∈ deltaSet Z M u, u' ≠ u → centralizer ({u'} : Set X) ≤ M)
    (hns : ¬ Shears Z M u) (hzu : u * c.z = c.z * u) :
    thompsonPairCount u c.z (u * c.z) = 1 := by
  have hu1 : u * u = 1 := sec126_involution_mul_self hu2
  have hz2 : orderOf c.z = 2 := S.invariant.1 c.z c.hz
  have hz1 : c.z * c.z = 1 := sec126_involution_mul_self hz2
  have hzH : c.z ∈ zHull Z M := Subgroup.subset_closure ⟨c.hz, c.hzM⟩
  have huz1 : (u * c.z) * (u * c.z) = 1 := by
    calc (u * c.z) * (u * c.z) = u * (c.z * u) * c.z := by group
      _ = u * (u * c.z) * c.z := by rw [hzu]
      _ = (u * u) * (c.z * c.z) := by group
      _ = 1 := by rw [hu1, hz1, one_mul]
  have hmemz : u * c.z ∈ deltaSet Z M u :=
    ⟨c.z, Subgroup.mem_inf.mpr ⟨ha hzH, hzH⟩, hzu⟩
  have hneu : u * c.z ≠ u := by
    intro h1
    have h2 : u * c.z = u * 1 := by rw [h1, mul_one]
    have := mul_left_cancel h2
    rw [this, orderOf_one] at hz2
    omega
  have hbz := hb (u * c.z) hmemz hneu
  have key : thompsonPairs u c.z (u * c.z) = {(u, c.z)} := by
    ext ⟨u', z'⟩
    constructor
    · intro hp
      obtain ⟨hu'c, hz'c, hwmem⟩ := hp
      have hu'1 : u' * u' = 1 := mul_self_eq_one_of_isConj hu1 hu'c
      have hz'Z : z' ∈ Z := S.invariant.isConj_mem c.hz hz'c.symm
      have hz'1 : z' * z' = 1 := S.invariant.mul_self_eq_one hz'Z
      obtain ⟨hu'cen, hz'cen⟩ := mem_centralizer_of_mem_thompsonPairs hu1 hz1 huz1
        (show (u', z') ∈ thompsonPairs u c.z (u * c.z) from ⟨hu'c, hz'c, hwmem⟩)
      have hu'M : u' ∈ M := hbz hu'cen
      have hz'M : z' ∈ M := hbz hz'cen
      have hz'H : z' ∈ zHull Z M := Subgroup.subset_closure ⟨hz'Z, hz'M⟩
      have hz'u : z' * u = u * z' := Subgroup.mem_centralizer_singleton_iff.mp (ha hz'H)
      have hsq : (u' * z') * (u' * z') ∈ zHull Z M := by
        have h1 := h.sec126_conj_mem_zHull' hu'M hz'H
        have hu'i : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right hu'1
        rw [hu'i] at h1
        have h2 := (zHull Z M).mul_mem h1 hz'H
        have e : (u' * z') * (u' * z') = u' * z' * u' * z' := by group
        rw [e]
        exact h2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwmem
      obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
      ·
        exfalso
        have hcj : (u' * z') ^ k ∈ zHull Z M := by
          rw [hj, zpow_mul, zpow_two]
          exact Subgroup.zpow_mem _ hsq j
        rw [hk] at hcj
        apply h.sec126_not_mem_zHull S huD hu2
        have := (zHull Z M).mul_mem hcj ((zHull Z M).inv_mem hzH)
        rwa [mul_assoc, mul_inv_cancel, mul_one] at this
      ·
        have hcj : (u' * z') ^ (2 * j) ∈ zHull Z M := by
          rw [zpow_mul, zpow_two]
          exact Subgroup.zpow_mem _ hsq j
        have hk' : (u' * z') ^ (2 * j) * (u' * z') = u * c.z := by
          rw [← zpow_add_one, ← hj, hk]
        generalize he : (u' * z') ^ (2 * j) = e at hcj hk'
        have e1 : u' * z' = e⁻¹ * (u * c.z) := by rw [← hk', inv_mul_cancel_left]
        have e2 : u' = e⁻¹ * (u * c.z) * z' := by
          calc u' = u' * z' * z' := by rw [mul_assoc, hz'1, mul_one]
            _ = e⁻¹ * (u * c.z) * z' := congrArg (· * z') e1
        have hzz : (c.z * z') * u = u * (c.z * z') :=
          Subgroup.mem_centralizer_singleton_iff.mp (ha ((zHull Z M).mul_mem hzH hz'H))
        have hyH : e⁻¹ * (c.z * z') ∈ zHull Z M :=
          (zHull Z M).mul_mem ((zHull Z M).inv_mem hcj) ((zHull Z M).mul_mem hzH hz'H)
        have hu'eq : u' = (e⁻¹ * (c.z * z')) * u := by
          rw [e2]
          calc e⁻¹ * (u * c.z) * z' = e⁻¹ * (u * (c.z * z')) := by group
            _ = e⁻¹ * ((c.z * z') * u) := by rw [hzz]
            _ = (e⁻¹ * (c.z * z')) * u := by group
        have hu'D : u' ∈ deltaSet Z M u :=
          ⟨e⁻¹ * (c.z * z'), Subgroup.mem_inf.mpr ⟨ha hyH, hyH⟩, hu'eq⟩
        have hu'u : u' = u := by
          by_contra hne
          exact hns ⟨u', hu'D, hne, hu'c⟩
        have hsq1 : (u * z') * (u * z') = 1 := by
          calc (u * z') * (u * z') = u * (z' * u) * z' := by group
            _ = u * (u * z') * z' := by rw [hz'u]
            _ = (u * u) * (z' * z') := by group
            _ = 1 := by rw [hu1, hz'1, one_mul]
        have he1 : e = 1 := by
          rw [← he, hu'u, zpow_mul, zpow_two, hsq1, one_zpow]
        rw [he1, inv_one, one_mul] at e1
        rw [hu'u] at e1
        have hz'c' : z' = c.z := mul_left_cancel e1
        rw [Set.mem_singleton_iff]
        exact Prod.ext hu'u hz'c'
    · intro hp
      rw [Set.mem_singleton_iff] at hp
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      exact ⟨IsConj.refl _, IsConj.refl _, Subgroup.mem_zpowers _⟩
  rw [thompsonPairCount, key]
  simp

theorem ZDSetup.lemma126
    (S : ZDSetup X Z M) (h124 : Lemma124Stmt Z M) : Lemma126Stmt Z M := by
  intro c n i hL u hu hu2
  have huD : u ∈ c.D := (Subgroup.mem_inf.mp hu).1
  have huM : u ∈ M := (Subgroup.mem_inf.mp huD).1
  have hzu : u * c.z = c.z * u :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hu).2
  have hfirst := lemma126_first h124 hL huD hu2 hzu (S.invariant.1 c.z c.hz)
  refine ⟨hfirst, fun hns => ?_⟩
  have ha := lemma126_a hL huM hu2 hns
  have hb := lemma126_b S hL huD hu2 ha hns
  exact ⟨ha, hb, lemma126_c S hL huD hu2 ha hfirst, lemma126_d S hL huD hu2 ha hb hns hzu⟩

end CFSG.GH74.Uniqueness
