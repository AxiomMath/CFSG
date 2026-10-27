module

public import CFSG.LargeExtraspecial.AS35ESixSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Asc77

namespace S14

@[expose] def AschbacherSixEightOneStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), AschbacherBelow (Nat.card G) →
    S.SixHyp → S.SixFiveConcl → ∀ s ∈ S.DSet, ∀ h : G, h * S.z * h⁻¹ ∈ S.DSet →
      s * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * s → s ≠ h * S.z * h⁻¹ → s ∈ S.DAt h

@[expose] def AschbacherSixEightTwoStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), AschbacherBelow (Nat.card G) →
    S.SixHyp → S.SixFiveConcl → ∀ k d : G, d * S.z * d⁻¹ ∈ S.DSet →
      d * S.z * d⁻¹ ∈ S.DAt k → orderOf (S.z * (k * S.z * k⁻¹)) = 3 →
        closure S.DSet ≤ closure (S.DSet ∩ S.DAt k) ⊔ S.QG

end S14

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

omit [Finite G] in
theorem orderOf_conj_eq (c x : G) : orderOf (c * x * c⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq c (show c * x = c * x * c⁻¹ * c by group)).symm

omit [Finite G] in
theorem exists_conj_of_mem_DSet {t : G} (ht : t ∈ S.DSet) : ∃ h : G, h * S.z * h⁻¹ = t := by
  obtain ⟨⟨h, hh, -⟩, -⟩ := ht
  exact ⟨h, hh⟩

omit [Finite G] in
theorem exists_conj_of_mem_DAt {g x : G} (hx : x ∈ S.DAt g) : ∃ h : G, h * S.z * h⁻¹ = x := by
  obtain ⟨d, hd, rfl⟩ := hx
  obtain ⟨h, rfl⟩ := S.exists_conj_of_mem_DSet hd
  exact ⟨g * h, by group⟩

omit [Finite G] in
theorem conj_mem_BAt {g c x : G} (hx : x ∈ S.BAt g) : c * x * c⁻¹ ∈ S.BAt (c * g) := by
  obtain ⟨k, hk, hxk⟩ := hx
  refine ⟨c * k, ?_, S.conj_mem_DAt_mul hxk⟩
  rw [show c * k * S.z * (c * k)⁻¹ = c * (k * S.z * k⁻¹) * c⁻¹ by group]
  exact S.conj_mem_DAt_mul hk

omit [Finite G] in
theorem mem_BAt_iff {g x : G} : x ∈ S.BAt g ↔ g⁻¹ * x * g ∈ S.BSet := by
  constructor
  · intro hx
    have := S.conj_mem_BAt (c := g⁻¹) hx
    rwa [inv_mul_cancel, inv_inv] at this
  · intro hx
    have := S.conj_mem_BAt (c := g) hx
    rwa [mul_one, show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this

theorem mem_BAt_symm (hS : S.SixFourConcl) {g k : G} (h : g * S.z * g⁻¹ ∈ S.BAt k) :
    k * S.z * k⁻¹ ∈ S.BAt g := by
  obtain ⟨j, hj, hgj⟩ := h
  exact ⟨j, S.mem_DAt_symm hS hgj, S.mem_DAt_symm hS hj⟩

theorem self_mem_BAt (hS : S.SixFourConcl) (hD : S.DSet.Nonempty) (g : G) :
    g * S.z * g⁻¹ ∈ S.BAt g := by
  obtain ⟨d, hd⟩ := hD
  obtain ⟨h, rfl⟩ := S.exists_conj_of_mem_DSet hd
  have h1 : (g * h) * S.z * (g * h)⁻¹ ∈ S.DAt g := by
    rw [show g * h * S.z * (g * h)⁻¹ = g * (h * S.z * h⁻¹) * g⁻¹ by group]
    exact S.conj_mem_DAt hd
  exact ⟨g * h, h1, S.mem_DAt_symm hS h1⟩

theorem mem_DAt_of_mem_zConj (hS : S.SixFourConcl) {t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) {g : G} (hg : g ∈ S.HAt h) {p : G}
    (hp : p ∈ S.zConj (S.HAt h)) (hpg : p ≠ g * S.z * g⁻¹) : p ∈ S.DAt g := by
  rw [mem_DAt]
  have h1 := conj_mem_conjIn_of_mem ((S.HAt h).inv_mem hg) hp
  rw [inv_inv] at h1
  refine S.zConj_diff_subset_DSet hS ht hh h1 fun h2 => hpg ?_
  calc p = g * (g⁻¹ * p * g) * g⁻¹ := by group
    _ = g * S.z * g⁻¹ := by rw [h2]

theorem DSet_subset_BSet (hS : S.SixFourConcl) {t : G} (ht : t ∈ S.DSet) : t ∈ S.BSet := by
  obtain ⟨h, hh, -, h5⟩ := id ht.1
  obtain ⟨x, hxH, hx⟩ := S.mem_zConj_of_mem_ESet ht.1 hh
  have htz := S.ne_z_of_mem_ESet ht.1
  have hsub : ({S.z, t} : Set G) ⊆ S.zConj (S.HAt h) := by
    rintro y (rfl | rfl)
    · exact self_mem_conjIn _ _
    · exact S.mem_zConj_of_mem_ESet ht.1 hh
  have h3 : (S.zConj (S.HAt h) \ {S.z, t}).ncard = 3 := by
    rw [Set.ncard_sdiff hsub, h5, Set.ncard_pair htz.symm]
  obtain ⟨p, hp⟩ := Set.nonempty_of_ncard_ne_zero (s := S.zConj (S.HAt h) \ {S.z, t})
    (by omega)
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp
  obtain ⟨hpH, hpz, hpt⟩ := hp
  have hpD : p ∈ S.DSet := S.zConj_diff_subset_DSet hS ht hh hpH hpz
  obtain ⟨j, rfl⟩ := S.exists_conj_of_mem_DSet hpD
  have hpt' : j * S.z * j⁻¹ ∈ S.DAt x := S.mem_DAt_of_mem_zConj hS ht hh hxH hpH (by rwa [hx])
  refine ⟨j, by rwa [DAt_one], ?_⟩
  rw [← hx]
  exact S.mem_DAt_symm hS hpt'

omit [Finite G] in
theorem conj_mem_DAt_of_commute {k c x : G} (hc : c * (k * S.z * k⁻¹) = k * S.z * k⁻¹ * c)
    (hx : x ∈ S.DAt k) : c * x * c⁻¹ ∈ S.DAt k := by
  rw [mem_DAt] at hx ⊢
  have hm : k⁻¹ * c * k ∈ S.M := by
    rw [S.mem_M_iff]
    calc k⁻¹ * c * k * S.z = k⁻¹ * (c * (k * S.z * k⁻¹)) * k := by group
      _ = k⁻¹ * (k * S.z * k⁻¹ * c) * k := by rw [hc]
      _ = S.z * (k⁻¹ * c * k) := by group
  have := S.conj_mem_DSet hm hx
  rwa [show k⁻¹ * c * k * (k⁻¹ * x * k) * (k⁻¹ * c * k)⁻¹ = k⁻¹ * (c * x * c⁻¹) * k by
    group] at this

theorem commute_of_mem_DAt (hS : S.SixFourConcl) {k f : G} (hf : f ∈ S.DAt k) :
    f * (k * S.z * k⁻¹) = k * S.z * k⁻¹ * f := by
  rw [mem_DAt] at hf
  have h1 := S.mem_M_iff.mp (S.mem_M_of_mem_ESet hS hf.1)
  calc f * (k * S.z * k⁻¹) = k * ((k⁻¹ * f * k) * S.z) * k⁻¹ := by group
    _ = k * (S.z * (k⁻¹ * f * k)) * k⁻¹ := by rw [h1]
    _ = k * S.z * k⁻¹ * f := by group

theorem mem_BAt_of_supplement (hS : S.SixHyp) (h65 : S.SixFiveConcl)
    (h681 : ∀ s ∈ S.DSet, ∀ h : G, h * S.z * h⁻¹ ∈ S.DSet →
      s * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * s → s ≠ h * S.z * h⁻¹ → s ∈ S.DAt h)
    {k : G} (h682 : closure S.DSet ≤ closure (S.DSet ∩ S.DAt k) ⊔ S.QG)
    (hne : (S.DSet ∩ S.DAt k).Nonempty) {b : G} (hb : b ∈ S.DSet) : b ∈ S.BAt k := by
  have hS4 := hS.sixFour
  have hMD : ∀ {f : G}, f ∈ S.DSet → f ∈ S.M := fun hf => S.mem_M_of_mem_ESet hS4 hf.1
  set I : Set S.O := {σ | ∃ f ∈ S.DSet ∩ S.DAt k, ∃ hf : f ∈ S.M, S.ρ ⟨f, hf⟩ = σ} with hIdef
  have hID : I ⊆ S.DbarAsc := by
    rintro _ ⟨f, hf, hfM, rfl⟩
    exact ⟨f, hf.1, hfM, rfl⟩
  have hY : closure S.DSet ≤ ((closure I).comap S.ρ).map S.M.subtype := by
    refine h682.trans (sup_le ?_ ?_)
    · rw [closure_le]
      intro f hf
      exact ⟨⟨f, hMD hf.1⟩, subset_closure ⟨f, hf, hMD hf.1, rfl⟩, rfl⟩
    · intro q hq
      refine ⟨⟨q, S.QG_le_M hq⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap, (S.ρ_eq_one_iff _).mpr hq]
      exact one_mem _
  have hDbarI : S.DbarAsc ⊆ closure I := by
    rintro _ ⟨d, hd, hdM, rfl⟩
    obtain ⟨m, hm, hmd⟩ := hY (subset_closure hd)
    have : m = ⟨d, hdM⟩ := Subtype.ext hmd
    rw [← this]
    exact hm
  have hgen : ∀ σ ∈ I, ∀ τ ∈ I, σ * τ * σ⁻¹ ∈ I := by
    rintro _ ⟨f, hf, hfM, rfl⟩ _ ⟨f', hf', hf'M, rfl⟩
    have hff : f * f' * f⁻¹ ∈ S.DSet ∩ S.DAt k :=
      ⟨S.conj_mem_DSet hfM hf'.1, S.conj_mem_DAt_of_commute (S.commute_of_mem_DAt hS4 hf.2) hf'.2⟩
    refine ⟨f * f' * f⁻¹, hff, hMD hff.1, ?_⟩
    rw [show (⟨f * f' * f⁻¹, hMD hff.1⟩ : S.M) = ⟨f, hfM⟩ * ⟨f', hf'M⟩ * ⟨f, hfM⟩⁻¹ from rfl,
      map_mul, map_mul, map_inv]
  have hnorm : ∀ g ∈ closure I, ∀ τ ∈ I, g * τ * g⁻¹ ∈ I ∧ g⁻¹ * τ * g ∈ I := by
    intro g hg
    induction hg using closure_induction with
    | mem σ hσ =>
      intro τ hτ
      have hσσ : σ * σ = 1 := by
        obtain ⟨f, hf, hfM, rfl⟩ := hσ
        exact S.ρ_mul_self_eq_one hfM (S.mul_self_of_isConj (S.isConj_of_mem_ESet hf.1.1))
      have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
      refine ⟨hgen σ hσ τ hτ, ?_⟩
      have := hgen σ hσ τ hτ
      rw [hσinv] at this ⊢
      exact this
    | one =>
      intro τ hτ
      simpa using hτ
    | mul x y _ _ hx hy =>
      intro τ hτ
      constructor
      · rw [show x * y * τ * (x * y)⁻¹ = x * (y * τ * y⁻¹) * x⁻¹ by group]
        exact (hx _ (hy τ hτ).1).1
      · rw [show (x * y)⁻¹ * τ * (x * y) = y⁻¹ * (x⁻¹ * τ * x) * y by group]
        exact (hy _ (hx τ hτ).2).2
    | inv x _ hx =>
      intro τ hτ
      refine ⟨?_, ?_⟩
      · rw [inv_inv]
        exact (hx τ hτ).2
      · rw [inv_inv]
        exact (hx τ hτ).1
  have hDbar_sub : S.DbarAsc ⊆ I := by
    intro β hβ
    obtain ⟨f₀, hf₀⟩ := hne
    have hα : S.ρ ⟨f₀, hMD hf₀.1⟩ ∈ I := ⟨f₀, hf₀, hMD hf₀.1, rfl⟩
    obtain ⟨g, hg, hgβ⟩ := h65.conj _ (hID hα) β hβ
    have hg' : g ∈ closure I := (closure_le _).mpr hDbarI hg
    rw [← hgβ]
    exact (hnorm g hg' _ hα).1
  have hbM := hMD hb
  obtain ⟨φ, hφ, hφne, hφc⟩ := h65.exists_commute _ (S.ρ_mem_DbarAsc hb hbM)
  obtain ⟨f, hf, hfM, rfl⟩ := hDbar_sub hφ
  have hcomm := S.fiveThirteen hS h65 hf.1 hb hfM hbM hφc.symm hφne
  have hfb : f ≠ b := by
    rintro rfl
    exact hφne rfl
  obtain ⟨h, rfl⟩ := S.exists_conj_of_mem_DSet hf.1
  exact ⟨h, hf.2, h681 b hb h hf.1 hcomm.symm (Ne.symm hfb)⟩

theorem mem_BSet_of_mem_DAt (hS : S.SixHyp) (h65 : S.SixFiveConcl)
    (h681 : ∀ s ∈ S.DSet, ∀ h : G, h * S.z * h⁻¹ ∈ S.DSet →
      s * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * s → s ≠ h * S.z * h⁻¹ → s ∈ S.DAt h)
    (h682 : ∀ k d : G, d * S.z * d⁻¹ ∈ S.DSet → d * S.z * d⁻¹ ∈ S.DAt k →
      orderOf (S.z * (k * S.z * k⁻¹)) = 3 → closure S.DSet ≤ closure (S.DSet ∩ S.DAt k) ⊔ S.QG)
    {g b : G} (hg : g * S.z * g⁻¹ ∈ S.BSet) (hb : b ∈ S.DAt g) : b ∈ S.BSet := by
  have hS4 := hS.sixFour
  obtain ⟨k₁, hk₁, hak₁⟩ := hg
  rw [DAt_one] at hk₁
  have hzk : S.z ∈ S.DAt k₁ := S.z_mem_DAt hS4 hk₁ rfl
  have hs1 := S.mem_DAt.mp hak₁
  have hs2 := S.mem_DAt.mp hzk
  have hord := S.sixSix hS h65 hs1 hs2
  rw [show k₁⁻¹ * (g * S.z * g⁻¹) * k₁ * (k₁⁻¹ * S.z * k₁) =
      k₁⁻¹ * (g * S.z * g⁻¹ * S.z) * k₁⁻¹⁻¹ by group, orderOf_conj_eq] at hord
  have hzz : S.z * S.z = 1 := S.z_mul_z
  have hzinv : S.z⁻¹ = S.z := inv_eq_of_mul_eq_one_right hzz
  have haa : g * S.z * g⁻¹ * (g * S.z * g⁻¹) = 1 := by
    rw [show g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ by group, hzz]
    group
  rcases hord with h1 | h2 | h3
  ·
    have ha : g * S.z * g⁻¹ = S.z := by
      have h4 := orderOf_eq_one_iff.mp h1
      calc g * S.z * g⁻¹ = g * S.z * g⁻¹ * S.z * S.z := by rw [mul_assoc _ S.z S.z, hzz, mul_one]
        _ = S.z := by rw [h4, one_mul]
    rw [S.DAt_eq_of_conj_eq (k := 1) (by rw [ha]; group), DAt_one] at hb
    exact S.DSet_subset_BSet hS4 hb
  ·
    have h4 : (g * S.z * g⁻¹ * S.z) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (g * S.z * g⁻¹ * S.z)
      rwa [h2] at this
    have hc : g * S.z * g⁻¹ * S.z = S.z * (g * S.z * g⁻¹) := by
      have h5 : g * S.z * g⁻¹ * S.z * (g * S.z * g⁻¹ * S.z) = 1 := by rw [← pow_two]; exact h4
      calc g * S.z * g⁻¹ * S.z = (g * S.z * g⁻¹ * S.z)⁻¹ := eq_inv_of_mul_eq_one_left h5
        _ = S.z * (g * S.z * g⁻¹) := by
            rw [mul_inv_rev, hzinv, inv_eq_of_mul_eq_one_right haa]
    have hne : g * S.z * g⁻¹ ≠ S.z := by
      intro h6
      rw [h6, hzz, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    have h7 := h681 _ hs1 k₁⁻¹ (by rwa [inv_inv]) (by
        rw [inv_inv]
        calc k₁⁻¹ * (g * S.z * g⁻¹) * k₁ * (k₁⁻¹ * S.z * k₁) =
            k₁⁻¹ * (g * S.z * g⁻¹ * S.z) * k₁ := by group
          _ = k₁⁻¹ * (S.z * (g * S.z * g⁻¹)) * k₁ := by rw [hc]
          _ = k₁⁻¹ * S.z * k₁ * (k₁⁻¹ * (g * S.z * g⁻¹) * k₁) := by group) (by
        rw [inv_inv]
        intro h6
        apply hne
        calc g * S.z * g⁻¹ = k₁ * (k₁⁻¹ * (g * S.z * g⁻¹) * k₁) * k₁⁻¹ := by group
          _ = S.z := by rw [h6]; group)
    have h8 := S.conj_mem_DAt_mul (c := k₁) h7
    rw [mul_inv_cancel, DAt_one, show k₁ * (k₁⁻¹ * (g * S.z * g⁻¹) * k₁) * k₁⁻¹ =
      g * S.z * g⁻¹ by group] at h8
    exact ⟨g, by rwa [DAt_one], hb⟩
  ·
    have hd1 : g⁻¹ * (k₁ * S.z * k₁⁻¹) * g ∈ S.DSet := S.mem_DAt.mp (S.mem_DAt_symm hS4 hak₁)
    have hd2 : g⁻¹ * (k₁ * S.z * k₁⁻¹) * g⁻¹⁻¹ ∈ S.DAt g⁻¹ := S.conj_mem_DAt hk₁
    rw [inv_inv] at hd2
    have hdk : (g⁻¹ * k₁) * S.z * (g⁻¹ * k₁)⁻¹ = g⁻¹ * (k₁ * S.z * k₁⁻¹) * g := by group
    have h3' : orderOf (S.z * (g⁻¹ * S.z * g⁻¹⁻¹)) = 3 := by
      rw [inv_inv, show S.z * (g⁻¹ * S.z * g) = g⁻¹ * (g * S.z * g⁻¹ * S.z) * g⁻¹⁻¹ by group,
        orderOf_conj_eq]
      exact h3
    have hsup := h682 g⁻¹ (g⁻¹ * k₁) (hdk ▸ hd1) (hdk ▸ hd2) h3'
    have hb' : g⁻¹ * b * g ∈ S.DSet := S.mem_DAt.mp hb
    have h4 := S.mem_BAt_of_supplement hS h65 h681 hsup ⟨_, hd1, hd2⟩ hb'
    have h5 := S.conj_mem_BAt (c := g) h4
    rwa [mul_inv_cancel, show g * (g⁻¹ * b * g) * g⁻¹ = b by group] at h5

theorem sixNine (hS : S.SixHyp) (h65 : S.SixFiveConcl)
    (h681 : ∀ s ∈ S.DSet, ∀ h : G, h * S.z * h⁻¹ ∈ S.DSet →
      s * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * s → s ≠ h * S.z * h⁻¹ → s ∈ S.DAt h)
    (h682 : ∀ k d : G, d * S.z * d⁻¹ ∈ S.DSet → d * S.z * d⁻¹ ∈ S.DAt k →
      orderOf (S.z * (k * S.z * k⁻¹)) = 3 → closure S.DSet ≤ closure (S.DSet ∩ S.DAt k) ⊔ S.QG)
    {g : G} (hg : g * S.z * g⁻¹ ∈ S.BSet) : S.BAt g ⊆ S.BSet := by
  rintro b ⟨j, hj, hbj⟩
  exact S.mem_BSet_of_mem_DAt hS h65 h681 h682
    (S.mem_BSet_of_mem_DAt hS h65 h681 h682 hg hj) hbj

end Setting

namespace S14

theorem aschbacherSixNineStmt_of (h681 : AschbacherSixEightOneStmt)
    (h682 : AschbacherSixEightTwoStmt) : AschbacherSixNineStmt :=
  fun G _ _ S ih hS h65 _ hg => S.sixNine hS h65 (h681 G S ih hS h65) (h682 G S ih hS h65) hg

end S14

end CFSG.LargeExtraspecial
