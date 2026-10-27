module

public import CFSG.CGT.T75N.L29Rad
public import CFSG.CGT.T75N.L29Wc
public import CFSG.CGT.Timmesfeld75.WeaklyClosed

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups CFSG.CGT.Timmesfeld75

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} [NeZero n] {Y : Type} [Group Y]

section Lift

variable (π : Y →* SpecialLinearGroup (Fin n) F)

omit [Finite F] [CharP F 2] [NeZero n] in
theorem conj_inf_ker {E : Subgroup Y} (hEK : E ⊓ π.ker = ⊥) (w : Y) :
    conjSubgroup w E ⊓ π.ker = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxA, hxK⟩
  rw [Subgroup.mem_bot]
  have h1 : w⁻¹ * x * w ∈ E := mem_conjSubgroup.1 hxA
  have h2 : w⁻¹ * x * w ∈ π.ker := by
    have hxK' : x ∈ π.ker := hxK
    rw [MonoidHom.mem_ker] at hxK' ⊢
    rw [map_mul, map_mul, hxK', mul_one, map_inv, inv_mul_cancel]
  have h3 : w⁻¹ * x * w ∈ E ⊓ π.ker := ⟨h1, h2⟩
  rw [hEK, Subgroup.mem_bot] at h3
  have : x = w * (w⁻¹ * x * w) * w⁻¹ := by group
  rw [this, h3]
  group

omit [Finite F] [CharP F 2] [NeZero n] in
theorem mem_map_conj (E : Subgroup Y) (w : Y) {y : SpecialLinearGroup (Fin n) F} :
    y ∈ (conjSubgroup w E).map π ↔ (π w)⁻¹ * y * π w ∈ E.map π := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : w⁻¹ * x * w ∈ E := mem_conjSubgroup.1 hx
    exact ⟨_, hx', by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨e, he, hey⟩
    refine ⟨w * e * w⁻¹, mem_conjSubgroup.2 (by simpa [mul_assoc] using he), ?_⟩
    rw [map_mul, map_mul, map_inv, hey]
    group

@[expose] def liftRad (E : Subgroup Y) (w : Y) (j : Fin n) : Subgroup Y :=
  conjSubgroup w E ⊓ (radRow n F j).comap π

omit [Finite F] [CharP F 2] [NeZero n] in
theorem liftRad_inf_ker {E : Subgroup Y} (hEK : E ⊓ π.ker = ⊥) (w : Y) (j : Fin n) :
    liftRad π E w j ⊓ π.ker = ⊥ :=
  eq_bot_iff.2 (fun x hx => by
    have := conj_inf_ker π hEK w
    exact (eq_bot_iff.1 this) ⟨hx.1.1, hx.2⟩)

omit [Finite F] in
theorem radRow_le_map_conj {E : Subgroup Y} (hEπ : E.map π = radRow n F 0) {w : Y} {j : Fin n}
    (hw : π w = swapSL j) : radRow n F j ≤ (conjSubgroup w E).map π := by
  intro g hg
  rw [mem_map_conj, hw, swapSL_inv, hEπ]
  have := swap_conj_radRow hg
  rwa [swapSL_inv] at this

omit [Finite F] in
theorem map_liftRad {E : Subgroup Y} (hEπ : E.map π = radRow n F 0) {w : Y} {j : Fin n}
    (hw : π w = swapSL j) : (liftRad π E w j).map π = radRow n F j := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro g hg
    obtain ⟨x, hxA, hxg⟩ := radRow_le_map_conj π hEπ hw hg
    exact ⟨x, ⟨hxA, Subgroup.mem_comap.2 (hxg ▸ hg)⟩, hxg⟩

theorem card_liftRad {E : Subgroup Y} (hEπ : E.map π = radRow n F 0) (hEK : E ⊓ π.ker = ⊥)
    {w : Y} {j : Fin n} (hw : π w = swapSL j) :
    Nat.card (liftRad π E w j) = Nat.card F ^ (n - 1 - j.val) := by
  rw [← card_radRow j]
  have hinj : Function.Injective ((π.comp (liftRad π E w j).subtype)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxK : (x : Y) ∈ π.ker := hx
    have : (x : Y) ∈ liftRad π E w j ⊓ π.ker := ⟨x.2, hxK⟩
    rw [liftRad_inf_ker π hEK w j, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hrange : (π.comp (liftRad π E w j).subtype).range = radRow n F j := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, map_liftRad π hEπ hw]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv)

omit [Finite F] in
theorem conj_mem_liftRad (hcen : π.ker ≤ Subgroup.center Y) {E : Subgroup Y} (hE : IsWC E)
    (hE1 : E ≠ ⊥) (hEπ : E.map π = radRow n F 0) {w : Y} {j : Fin n} (hw : π w = swapSL j)
    {h : Y} (hh : π h ∈ fixPt n F (j.val + 1)) {x : Y} (hx : x ∈ liftRad π E w j) :
    h * x * h⁻¹ ∈ liftRad π E w j := by
  have hA : IsWC (conjSubgroup w E) := hE.conj w
  have hA1 : conjSubgroup w E ≠ ⊥ := by
    obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE1
    intro hbot
    have hmem : w * e * w⁻¹ ∈ conjSubgroup w E := mem_conjSubgroup.2 (by simpa [mul_assoc] using he)
    rw [hbot, Subgroup.mem_bot] at hmem
    apply he1
    apply Subtype.ext
    show e = 1
    calc e = w⁻¹ * (w * e * w⁻¹) * w := by group
      _ = 1 := by rw [hmem]; group
  have hnorm : ∀ y ∈ (conjSubgroup w E).map π, π h * y * (π h)⁻¹ ∈ (conjSubgroup w E).map π := by
    intro y hy
    rw [mem_map_conj, hw, swapSL_inv, hEπ] at hy ⊢
    have hg' := swap_conj_fixPt hh
    rw [swapSL_inv] at hg'
    have hconj := conj_radRow_mem (j := (0 : Fin n)) (k := 1) (by simp) hg' hy
    have h2 : (swapSL j : SpecialLinearGroup (Fin n) F) * swapSL j = 1 := swapSL_mul_self j
    have hid : swapSL j * (π h * y * (π h)⁻¹) * swapSL j =
        (swapSL j * π h * swapSL j) * (swapSL j * y * swapSL j) *
          (swapSL j * π h * swapSL j)⁻¹ := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, swapSL_inv]
      calc swapSL j * (π h * y * (π h)⁻¹) * swapSL j
          = swapSL j * π h * (swapSL j * swapSL j) * y * (swapSL j * swapSL j) * (π h)⁻¹ *
              swapSL j := by rw [h2]; group
        _ = _ := by group
    rw [hid]
    exact hconj
  refine ⟨conj_mem_of_normalizes_image π hcen hA hA1 hnorm hx.1, Subgroup.mem_comap.2 ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact conj_radRow_mem (Nat.lt_succ_self _) hh (Subgroup.mem_comap.1 hx.2)

end Lift

section Chain

variable (π : Y →* SpecialLinearGroup (Fin n) F)

omit [Finite F] in
theorem chain_step (hcen : π.ker ≤ Subgroup.center Y) {E : Subgroup Y} (hE : IsWC E)
    (hE1 : E ≠ ⊥) (hEπ : E.map π = radRow n F 0) (hEK : E ⊓ π.ker = ⊥) {w : Y} {k : Fin n}
    (hw : π w = swapSL k) (H' : Subgroup Y) (hH'K : H' ⊓ π.ker = ⊥)
    (hH'low : ∀ h ∈ H', π h ∈ lowRows n F (k.val + 1))
    (hH'fix : ∀ h ∈ H', π h ∈ fixPt n F (k.val + 1)) :
    ∃ H : Subgroup Y, H ⊓ π.ker = ⊥ ∧ (∀ h ∈ H, π h ∈ lowRows n F k.val) ∧
      (∀ h ∈ H, π h ∈ fixPt n F k.val) ∧
      Nat.card H = Nat.card (liftRad π E w k) * Nat.card H' := by
  classical
  set R := liftRad π E w k with hR
  have hconj : ∀ h ∈ H', ∀ x ∈ R, h * x * h⁻¹ ∈ R := fun h hh x hx =>
    conj_mem_liftRad π hcen hE hE1 hEπ hw (hH'fix h hh) hx
  have hRlow : ∀ r ∈ R, π r ∈ lowRows n F k.val := fun r hr => radRow_le_lowRows k hr.2
  have hRfix : ∀ r ∈ R, π r ∈ fixPt n F k.val := fun r hr =>
    fixPt_anti (Nat.le_succ _) (radRow_le_fixPt k hr.2)
  let H : Subgroup Y :=
    { carrier := {x | ∃ r ∈ R, ∃ h ∈ H', x = r * h}
      one_mem' := ⟨1, R.one_mem, 1, H'.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨r, hr, h, hh, rfl⟩ ⟨r', hr', h', hh', rfl⟩
        refine ⟨r * (h * r' * h⁻¹), R.mul_mem hr (hconj h hh r' hr'), h * h', H'.mul_mem hh hh',
          ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨r, hr, h, hh, rfl⟩
        refine ⟨h⁻¹ * r⁻¹ * h, ?_, h⁻¹, H'.inv_mem hh, by group⟩
        have := hconj h⁻¹ (H'.inv_mem hh) r⁻¹ (R.inv_mem hr)
        simpa using this }
  have hRK : R ⊓ π.ker = ⊥ := liftRad_inf_ker π hEK w k
  have hsep : ∀ r ∈ R, ∀ h ∈ H', r * h ∈ π.ker → r = 1 ∧ h = 1 := by
    intro r hr h hh hrh
    rw [MonoidHom.mem_ker, map_mul] at hrh
    have h1 : π r ∈ radRow n F k := hr.2
    have h2 : π r = (π h)⁻¹ := eq_inv_of_mul_eq_one_left hrh
    have h3 : π r ∈ lowRows n F (k.val + 1) := by
      rw [h2]
      exact (lowRows n F (k.val + 1)).inv_mem (hH'low h hh)
    have h4 : π r = 1 := by
      have : π r ∈ radRow n F k ⊓ lowRows n F (k.val + 1) := ⟨h1, h3⟩
      rw [radRow_inf_lowRows, Subgroup.mem_bot] at this
      exact this
    have h5 : π h = 1 := by
      rw [h4, one_mul] at hrh
      exact hrh
    have hr1 : r = 1 := by
      have : r ∈ R ⊓ π.ker := ⟨hr, h4⟩
      rw [hRK, Subgroup.mem_bot] at this
      exact this
    have hh1 : h = 1 := by
      have : h ∈ H' ⊓ π.ker := ⟨hh, h5⟩
      rw [hH'K, Subgroup.mem_bot] at this
      exact this
    exact ⟨hr1, hh1⟩
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨⟨r, hr, h, hh, rfl⟩, hxK⟩
    rw [Subgroup.mem_bot]
    obtain ⟨h1, h2⟩ := hsep r hr h hh hxK
    rw [h1, h2, one_mul]
  · rintro _ ⟨r, hr, h, hh, rfl⟩
    rw [map_mul]
    exact (lowRows n F k.val).mul_mem (hRlow r hr)
      (lowRows_anti (Nat.le_succ _) (hH'low h hh))
  · rintro _ ⟨r, hr, h, hh, rfl⟩
    rw [map_mul]
    exact (fixPt n F k.val).mul_mem (hRfix r hr) (fixPt_anti (Nat.le_succ _) (hH'fix h hh))
  · have hbij : Function.Bijective (fun p : R × H' => (⟨(p.1 : Y) * (p.2 : Y),
        ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩ : H)) := by
      constructor
      · rintro ⟨⟨r, hr⟩, ⟨h, hh⟩⟩ ⟨⟨r', hr'⟩, ⟨h', hh'⟩⟩ heq
        have heq' : r * h = r' * h' := congrArg Subtype.val heq
        have hker : (r'⁻¹ * r) * (h * h'⁻¹) = 1 := by
          calc r'⁻¹ * r * (h * h'⁻¹) = r'⁻¹ * (r * h) * h'⁻¹ := by group
            _ = 1 := by rw [heq']; group
        obtain ⟨h1, h2⟩ := hsep (r'⁻¹ * r) (R.mul_mem (R.inv_mem hr') hr) (h * h'⁻¹)
          (H'.mul_mem hh (H'.inv_mem hh')) (by rw [hker]; exact π.ker.one_mem)
        have e1 : r = r' := (inv_mul_eq_one.1 h1).symm
        have e2 : h = h' := mul_inv_eq_one.1 h2
        subst e1
        subst e2
        rfl
      · rintro ⟨_, r, hr, h, hh, rfl⟩
        exact ⟨(⟨r, hr⟩, ⟨h, hh⟩), rfl⟩
    rw [← Nat.card_prod]
    exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

theorem chain_exists (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center Y)
    {E : Subgroup Y} (hE : IsWC E) (hE1 : E ≠ ⊥) (hEπ : E.map π = radRow n F 0)
    (hEK : E ⊓ π.ker = ⊥) :
    ∀ d s : ℕ, s + d = n - 1 → ∃ H : Subgroup Y, H ⊓ π.ker = ⊥ ∧
      (∀ h ∈ H, π h ∈ lowRows n F s) ∧ (∀ h ∈ H, π h ∈ fixPt n F s) ∧
      Nat.card H = Nat.card F ^ (∑ j ∈ Finset.Ico s (n - 1), (n - 1 - j)) := by
  intro d
  induction d with
  | zero =>
    intro s hs
    have hs' : s = n - 1 := by omega
    subst hs'
    refine ⟨⊥, by simp, ?_, ?_, ?_⟩
    · intro h hh
      rw [Subgroup.mem_bot] at hh
      rw [hh, map_one]
      exact Subgroup.one_mem _
    · intro h hh
      rw [Subgroup.mem_bot] at hh
      rw [hh, map_one]
      exact Subgroup.one_mem _
    · simp
  | succ d ih =>
    intro s hs
    obtain ⟨H', hH'K, hH'low, hH'fix, hH'card⟩ := ih (s + 1) (by omega)
    have hsn : s < n := by omega
    obtain ⟨w, hw⟩ := hπ (swapSL (⟨s, hsn⟩ : Fin n))
    obtain ⟨H, hHK, hHlow, hHfix, hHcard⟩ := chain_step π hcen hE hE1 hEπ hEK hw H' hH'K hH'low
      hH'fix
    refine ⟨H, hHK, hHlow, hHfix, ?_⟩
    rw [hHcard, hH'card, card_liftRad π hEπ hEK hw, ← pow_add,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : s < n - 1)]

end Chain

end CFSG.CGT.T75N
