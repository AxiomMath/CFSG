module

public import CFSG.LargeExtraspecial.GLRLinGL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.GLR

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {X : Subgroup S.O}
  {A B : Submodule (ZMod 2) S.Qt}

theorem exists_siegel (h : Pair S X A B) {u c : S.Qt} (hu : u ∈ A) (hc : c ∈ B)
    (huc : polar S.q u c = 0) :
    ∃ x ∈ X, ∀ w, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + polar S.q w c • u + polar S.q w u • c := by
  obtain ⟨x, hx, hxa⟩ := h.exists_transvection hu huc
  refine ⟨x, hx, fun w => ?_⟩
  have hw : w ∈ A ⊔ B := by rw [h.sup_eq]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
  have hxb : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) b = b + polar S.q b u • c := by
    refine (h.apply_eq_iff hx hb (B.add_mem hb (B.smul_mem _ hc))).mpr fun a' ha' => ?_
    rw [hxa a' ha']
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul,
      huc, mul_zero, add_zero, polar_comm S.q u b]
    generalize polar S.q a' b = P
    generalize polar S.q b u = r
    generalize polar S.q a' c = p
    revert P r p
    decide
  rw [map_add, hxa a ha, hxb, polar_add_left, polar_add_left, h.symm.polar_A hb hc,
    h.polar_A ha hu, add_zero, zero_add]
  abel

theorem mem_of_siegel_invariant (h : Pair S X A B) {a b : S.Qt} (ha : a ∈ A) (hb : b ∈ B)
    (hab : polar S.q a b = 0) {W : Submodule (ZMod 2) S.Qt} (hx : a + b ∈ W)
    (hperp : ∀ w ∈ W, polar S.q w (a + b) = 0) {w₁ w₂ : S.Qt} (hw₁ : w₁ ∈ W) (hw₂ : w₂ ∈ W)
    (hw₁n : w₁ ∉ Submodule.span (ZMod 2) {a + b})
    (hw₂n : w₂ ∉ Submodule.span (ZMod 2) {a + b, w₁})
    (hinv : ∀ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (a + b) = a + b →
      ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W) : a ∈ W := by
  have hpA := fun {u v : S.Qt} (hu : u ∈ A) (hv : v ∈ A) => h.polar_A hu hv
  have hpB := fun {u v : S.Qt} (hu : u ∈ B) (hv : v ∈ B) => h.symm.polar_A hu hv
  have hmove : ∀ {u c : S.Qt}, u ∈ A → c ∈ B → polar S.q u c = 0 →
      polar S.q (a + b) c = 0 → polar S.q (a + b) u = 0 → ∀ w ∈ W,
        polar S.q w c • u + polar S.q w u • c ∈ W := by
    intro u c hu hc huc h1 h2 w hw
    obtain ⟨x, hxX, hxw⟩ := exists_siegel h hu hc huc
    have hfix : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (a + b) = a + b := by
      rw [hxw, h1, h2, zero_smul, zero_smul, add_zero, add_zero]
    have := W.sub_mem (hinv x hxX hfix w hw) hw
    rwa [hxw, add_assoc, add_sub_cancel_left] at this
  obtain ⟨w, hw, hwn, hwb⟩ : ∃ w ∈ W, w ∉ Submodule.span (ZMod 2) {a + b} ∧
      polar S.q w b = 0 := by
    have h12 : w₁ + w₂ ∉ Submodule.span (ZMod 2) {a + b} := fun hm => hw₂n (by
      have : w₂ = (w₁ + w₂) - w₁ := by abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.span_mono (by simp) hm)
        (Submodule.subset_span (by simp)))
    rcases zmod2_eq_zero_or_one (polar S.q w₁ b) with e₁ | e₁
    · exact ⟨w₁, hw₁, hw₁n, e₁⟩
    rcases zmod2_eq_zero_or_one (polar S.q w₂ b) with e₂ | e₂
    · exact ⟨w₂, hw₂, fun hm => hw₂n (Submodule.span_mono (by simp) hm), e₂⟩
    · refine ⟨w₁ + w₂, W.add_mem hw₁ hw₂, h12, ?_⟩
      rw [polar_add_left, e₁, e₂]
      decide
  have hwa : polar S.q w a = 0 := by
    have := hperp w hw
    rwa [polar_add_right, hwb, add_zero] at this
  have hw' : w ∈ A ⊔ B := by rw [h.sup_eq]; exact Submodule.mem_top
  obtain ⟨w₀, hw₀, ws, hws, rfl⟩ := Submodule.mem_sup.mp hw'
  by_cases hw₀a : w₀ ∈ Submodule.span (ZMod 2) {a}
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw₀a
    have hmW : ws - c • b ∈ W := by
      have := W.sub_mem hw (W.smul_mem c hx)
      convert this using 1
      rw [smul_add]
      abel
    have hmB : ws - c • b ∈ B := B.sub_mem hws (B.smul_mem c hb)
    by_cases hmb : ws - c • b ∈ Submodule.span (ZMod 2) {b}
    · obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hmb
      rcases zmod2_eq_zero_or_one d with rfl | rfl
      · exfalso
        apply hwn
        rw [zero_smul] at hd
        have : ws = c • b := (sub_eq_zero.mp hd.symm)
        rw [this, ← smul_add]
        exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
      · rw [one_smul] at hd
        have hbW : b ∈ W := hd ▸ hmW
        have := W.sub_mem hx hbW
        rwa [add_sub_cancel_right] at this
    · obtain ⟨v, hvA, hvb, hvm⟩ := h.symm.exists_polar_sep
        ((Submodule.span_singleton_le_iff_mem b B).mpr hb) hmB hmb
      have hvb' : polar S.q v b = 0 := by
        rw [polar_comm]
        exact hvb b (Submodule.mem_span_singleton_self b)
      have hm := hmove hvA hb hvb' (by rw [polar_add_left, hab, hpB hb hb, add_zero])
        (by rw [polar_add_left, hpA ha hvA, polar_comm, hvb', zero_add]) _ hmW
      rw [hpB hmB hb, zero_smul, zero_add, hvm, one_smul] at hm
      have := W.sub_mem hx hm
      rwa [add_sub_cancel_right] at this
  · obtain ⟨μ, hμB, hμa, hμw⟩ := h.exists_polar_sep
      ((Submodule.span_singleton_le_iff_mem a A).mpr ha) hw₀ hw₀a
    have haμ : polar S.q a μ = 0 := hμa a (Submodule.mem_span_singleton_self a)
    have hm := hmove ha hμB haμ (by rw [polar_add_left, haμ, hpB hb hμB, add_zero])
      (by rw [polar_add_left, hpA ha ha, polar_comm, hab, add_zero]) _ hw
    rw [hwa, zero_smul, add_zero, polar_add_left, hμw, hpB hws hμB, add_zero, one_smul] at hm
    exact hm

theorem exists_polar_eq_one_eq_one (h : Pair S X A B) {a a' : S.Qt} (ha : a ∈ A) (ha' : a' ∈ A)
    (ha0 : a ≠ 0) (ha'0 : a' ≠ 0) (hne : a ≠ a') :
    ∃ c ∈ B, polar S.q a c = 1 ∧ polar S.q a' c = 1 := by
  have hnot : ∀ {u u' : S.Qt}, u ≠ 0 → u ≠ u' → u ∉ Submodule.span (ZMod 2) {u'} :=
    fun hu hne hm => by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
      rcases zmod2_eq_zero_or_one c with rfl | rfl
      · exact hu (by rw [← hc, zero_smul])
      · exact hne (by rw [← hc, one_smul])
  obtain ⟨c₁, hc₁B, hc₁U, hc₁⟩ := h.exists_polar_sep
    ((Submodule.span_singleton_le_iff_mem _ _).mpr ha') ha (hnot ha0 hne)
  obtain ⟨c₂, hc₂B, hc₂U, hc₂⟩ := h.exists_polar_sep
    ((Submodule.span_singleton_le_iff_mem _ _).mpr ha) ha' (hnot ha'0 (Ne.symm hne))
  have e₁ : polar S.q a' c₁ = 0 := hc₁U _ (Submodule.mem_span_singleton_self _)
  have e₂ : polar S.q a c₂ = 0 := hc₂U _ (Submodule.mem_span_singleton_self _)
  exact ⟨c₁ + c₂, B.add_mem hc₁B hc₂B, by rw [polar_add_right, hc₁, e₂, add_zero],
    by rw [polar_add_right, hc₂, e₁, zero_add]⟩

theorem exists_mem_apply_eq_pair (h : Pair S X A B) {a b a' b' : S.Qt} (ha : a ∈ A) (hb : b ∈ B)
    (ha' : a' ∈ A) (hb' : b' ∈ B) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha'0 : a' ≠ 0) (hb'0 : b' ≠ 0)
    (hab : polar S.q a b = 0) (hab' : polar S.q a' b' = 0) :
    ∃ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a' ∧ (x : S.Qt ≃ₗ[ZMod 2] S.Qt) b = b' := by
  have hpA := fun {u v : S.Qt} (hu : u ∈ A) (hv : v ∈ A) => h.polar_A hu hv
  have hpB := fun {u v : S.Qt} (hu : u ∈ B) (hv : v ∈ B) => h.symm.polar_A hu hv
  obtain ⟨x₁, hx₁, hx₁a⟩ : ∃ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a' := by
    by_cases he : a = a'
    · exact ⟨1, X.one_mem, by rw [he]; rfl⟩
    obtain ⟨c, hcB, hc, hc'⟩ := exists_polar_eq_one_eq_one h ha ha' ha0 ha'0 he
    obtain ⟨x, hx, hxw⟩ := exists_siegel h (A.add_mem ha ha') hcB
      (by rw [polar_add_left, hc, hc']; decide)
    refine ⟨x, hx, ?_⟩
    rw [hxw, hc, one_smul, polar_add_right, hpA ha ha, hpA ha ha', add_zero, zero_smul, add_zero,
      ← add_assoc, ZModModule.add_self, zero_add]
  set b'' := (x₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) b with hb''
  have hb''B : b'' ∈ B := h.apply_B x₁ hx₁ b hb
  have hb''0 : b'' ≠ 0 := fun h0 => hb0 (by
    rw [hb'', LinearEquiv.map_eq_zero_iff] at h0
    exact h0)
  have hab'' : polar S.q a' b'' = 0 := by
    rw [← hx₁a, hb'', TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x₁.2, hab]
  obtain ⟨x₂, hx₂, hx₂a, hx₂b⟩ : ∃ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a' = a' ∧
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) b'' = b' := by
    by_cases he : b'' = b'
    · exact ⟨1, X.one_mem, rfl, by rw [he]; rfl⟩
    obtain ⟨u, huA, hu, hu'⟩ := exists_polar_eq_one_eq_one h.symm hb''B hb' hb''0 hb'0 he
    have hc : polar S.q u (b'' + b') = 0 := by
      rw [polar_add_right, polar_comm, hu, polar_comm, hu']
      decide
    obtain ⟨x, hx, hxw⟩ := exists_siegel h huA (B.add_mem hb''B hb') hc
    refine ⟨x, hx, ?_, ?_⟩
    · rw [hxw, polar_add_right, hab'', hab', add_zero, zero_smul, add_zero, hpA ha' huA,
        zero_smul, add_zero]
    · rw [hxw, polar_add_right, hpB hb''B hb''B, hpB hb''B hb', add_zero, zero_smul, add_zero, hu,
        one_smul, ← add_assoc, ZModModule.add_self, zero_add]
  refine ⟨x₂ * x₁, X.mul_mem hx₂ hx₁, ?_, ?_⟩
  · rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hx₁a, hx₂a]
  · rw [Subgroup.coe_mul, LinearEquiv.mul_apply, ← hb'', hx₂b]

end CFSG.LargeExtraspecial.GLW4
