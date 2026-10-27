module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

@[expose] def tvMat (u h : V3) : Matrix (Fin 3) (Fin 3) (ZMod 2) := 1 + Matrix.vecMulVec u h

theorem tvMat_mulVec (u h x : V3) : (tvMat u h).mulVec x = x + (h ⬝ᵥ x) • u := by
  revert u h x
  decide +kernel

theorem tv_tvMat_mul_self : ∀ u h : V3, h ⬝ᵥ u = 0 → tvMat u h * tvMat u h = 1 := by
  decide +kernel

@[expose] def tvGL (u h : V3) (hu : h ⬝ᵥ u = 0) : GL32 :=
  ⟨tvMat u h, tvMat u h, tv_tvMat_mul_self u h hu, tv_tvMat_mul_self u h hu⟩

theorem act_tvGL (u h : V3) (hu : h ⬝ᵥ u = 0) (x : V3) :
    act (tvGL u h hu) x = x + (h ⬝ᵥ x) • u :=
  tvMat_mulVec u h x

theorem tvGL_mul_self (u h : V3) (hu : h ⬝ᵥ u = 0) : tvGL u h hu * tvGL u h hu = 1 :=
  Units.ext (tv_tvMat_mul_self u h hu)

theorem tv_tvMat_eq_one_iff : ∀ u h : V3, tvMat u h = 1 ↔ u = 0 ∨ h = 0 := by
  decide +kernel

theorem tvGL_eq_one_iff (u h : V3) (hu : h ⬝ᵥ u = 0) : tvGL u h hu = 1 ↔ u = 0 ∨ h = 0 := by
  constructor
  · intro h1
    exact (tv_tvMat_eq_one_iff u h).1 (congrArg Units.val h1)
  · intro h1
    exact Units.ext ((tv_tvMat_eq_one_iff u h).2 h1)

theorem GL32_ext {g g' : GL32} (h : ∀ x, act g x = act g' x) : g = g' := by
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  exact h

theorem tv_zmod_two (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem tv_tvGL_mem_Spt (p h : V3) (hh : h ⬝ᵥ p = 0) : tvGL p h hh ∈ Spt p := by
  intro x
  rw [act_tvGL]
  rcases tv_zmod_two (h ⬝ᵥ x) with h0 | h1
  · left
    rw [h0, zero_smul, add_zero]
  · right
    rw [h1, one_smul]

theorem tv_Spt_check : ∀ p : V3, ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
    M.mulVec p = p ∧ (∀ x : V3, M.mulVec x = x ∨ M.mulVec x = x + p) →
      ∃ h : V3, h ⬝ᵥ p = 0 ∧ M = tvMat p h := by
  decide +kernel

theorem mem_Spt_iff {p : V3} {g : GL32} :
    g ∈ Spt p ↔ ∃ (h : V3) (hh : h ⬝ᵥ p = 0), g = tvGL p h hh := by
  constructor
  · intro hg
    obtain ⟨h, hh, hM⟩ := tv_Spt_check p (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
      ⟨act_fixes_of_forall (mem_Spt.1 hg), mem_Spt.1 hg⟩
    exact ⟨h, hh, Units.ext hM⟩
  · rintro ⟨h, hh, rfl⟩
    exact tv_tvGL_mem_Spt p h hh

theorem tv_involution_check : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M * M = 1 → M ≠ 1 →
    ∃ u h : V3, h ⬝ᵥ u = 0 ∧ u ≠ 0 ∧ h ≠ 0 ∧ M = tvMat u h := by
  decide +kernel

theorem involution_eq_tvGL (g : GL32) (hg : g ^ 2 = 1) (hg1 : g ≠ 1) :
    ∃ (u h : V3) (hu : h ⬝ᵥ u = 0), u ≠ 0 ∧ h ≠ 0 ∧ g = tvGL u h hu := by
  have h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    have := congrArg Units.val hg
    simpa [pow_two] using this
  have h2 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := fun h => hg1 (Units.ext h)
  obtain ⟨u, h, hu, hu0, h0, hM⟩ := tv_involution_check _ h1 h2
  exact ⟨u, h, hu, hu0, h0, Units.ext hM⟩

@[expose] def tv_colMat (p q r : V3) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j => (![p, q, r] : Fin 3 → V3) j i

theorem tv_colMat_e0 : ∀ p q r : V3, (tv_colMat p q r).mulVec ![1, 0, 0] = p := by
  decide +kernel

theorem tv_colMat_e1 : ∀ p q r : V3, (tv_colMat p q r).mulVec ![0, 1, 0] = q := by
  decide +kernel

theorem tv_colMat_det : ∀ p q : V3, p ≠ 0 → q ≠ 0 → p ≠ q →
    ∃ r : V3, (tv_colMat p q r).det = 1 := by
  decide +kernel

theorem tv_exists_pair_basis {p q : V3} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q) :
    ∃ g : GL32, act g ![1, 0, 0] = p ∧ act g ![0, 1, 0] = q := by
  obtain ⟨r, hr⟩ := tv_colMat_det p q hp hq hpq
  exact ⟨Matrix.SpecialLinearGroup.toGL ⟨tv_colMat p q r, hr⟩,
    tv_colMat_e0 p q r, tv_colMat_e1 p q r⟩

theorem exists_act_pair {p q p' q' : V3} (hp : p ≠ 0) (hq : q ≠ 0) (hp' : p' ≠ 0) (hq' : q' ≠ 0)
    (hpq : p ≠ q) (hpq' : p' ≠ q') : ∃ g : GL32, act g p = p' ∧ act g q = q' := by
  obtain ⟨g₁, h1, h2⟩ := tv_exists_pair_basis hp hq hpq
  obtain ⟨g₂, h3, h4⟩ := tv_exists_pair_basis hp' hq' hpq'
  refine ⟨g₂ * g₁⁻¹, ?_, ?_⟩
  · rw [act_mul, ← h1, act_inv_act, h3]
  · rw [act_mul, ← h2, act_inv_act, h4]

theorem tv_exists_ne : ∀ p : V3, p ≠ 0 → ∃ p₂ : V3, p₂ ≠ 0 ∧ p₂ ≠ p := by
  decide +kernel

theorem exists_act {p q : V3} (hp : p ≠ 0) (hq : q ≠ 0) : ∃ g : GL32, act g p = q := by
  obtain ⟨p₂, hp₂, hp₂p⟩ := tv_exists_ne p hp
  obtain ⟨q₂, hq₂, hq₂q⟩ := tv_exists_ne q hq
  obtain ⟨g, h1, -⟩ := exists_act_pair hp hp₂ hq hq₂ (Ne.symm hp₂p) (Ne.symm hq₂q)
  exact ⟨g, h1⟩

theorem tv_tvMat_inj : ∀ p h k : V3, p ≠ 0 → tvMat p h = tvMat p k → h = k := by
  decide +kernel

theorem tv_card_perp : ∀ p : V3, p ≠ 0 → Fintype.card {h : V3 // h ⬝ᵥ p = 0} = 4 := by
  decide +kernel

theorem Spt_card {p : V3} (hp : p ≠ 0) : Nat.card (Spt p) = 4 := by
  have e : {h : V3 // h ⬝ᵥ p = 0} ≃ Spt p :=
    Equiv.ofBijective (fun h => ⟨tvGL p h.1 h.2, tv_tvGL_mem_Spt p h.1 h.2⟩)
      ⟨fun h₁ h₂ h => Subtype.ext (tv_tvMat_inj p h₁.1 h₂.1 hp
          (congrArg Units.val (congrArg Subtype.val h))),
        fun ⟨g, hg⟩ => by
          obtain ⟨h, hh, rfl⟩ := mem_Spt_iff.1 hg
          exact ⟨⟨h, hh⟩, rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  exact tv_card_perp p hp

theorem tv_conj_mem_Spt {g s : GL32} {p : V3} (hs : s ∈ Spt p) :
    g * s * g⁻¹ ∈ Spt (act g p) := by
  intro x
  rw [act_mul, act_mul]
  rcases hs (act g⁻¹ x) with h | h
  · left
    rw [h, act_act_inv]
  · right
    rw [h, act_add, act_act_inv]

theorem Spt_conj (g : GL32) (p : V3) :
    (Spt p).map (MulAut.conj g).toMonoidHom = Spt (act g p) := by
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    exact tv_conj_mem_Spt hs
  · intro s hs
    have h := tv_conj_mem_Spt (g := g⁻¹) hs
    rw [act_inv_act] at h
    refine ⟨g⁻¹ * s * g⁻¹⁻¹, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem tv_exists_perp : ∀ p : V3, p ≠ 0 → ∃ k : V3, k ≠ 0 ∧ k ⬝ᵥ p = 0 := by
  decide +kernel

theorem tv_exists_dot_one : ∀ k : V3, k ≠ 0 → ∃ x : V3, k ⬝ᵥ x = 1 := by
  decide +kernel

theorem tv_Spt_injective {p q : V3} (hp : p ≠ 0) (h : Spt p = Spt q) : p = q := by
  obtain ⟨k, hk0, hkp⟩ := tv_exists_perp p hp
  obtain ⟨x, hx⟩ := tv_exists_dot_one k hk0
  have hmem : tvGL p k hkp ∈ Spt q := h ▸ tv_tvGL_mem_Spt p k hkp
  rcases hmem x with h1 | h1
  · rw [act_tvGL, hx, one_smul] at h1
    exact absurd (by simpa using h1) hp
  · rw [act_tvGL, hx, one_smul] at h1
    exact add_left_cancel h1

theorem normalizer_Spt {p : V3} (hp : p ≠ 0) : normalizer (Spt p : Set GL32) = Pstab p := by
  ext g
  rw [mem_normalizer_iff_map_conj_eq, mem_Pstab]
  have hc := Spt_conj g p
  have hne : act g p ≠ 0 := fun h => hp ((act_eq_zero_iff g p).1 h)
  constructor
  · intro h
    exact tv_Spt_injective hne (hc.symm.trans h)
  · intro h
    rw [h] at hc
    exact hc

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
