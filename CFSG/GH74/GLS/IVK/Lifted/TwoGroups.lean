module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralModel
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition

public section

namespace CFSG.GH74.GLS.IVK.Lifted

section SDFacts

open Subgroup CFSG CFSG.Semidihedral CFSG.Open

theorem sd_z_mem_of_index_two (n : ℕ) (hn : 4 ≤ n) (M : Subgroup (SemidihedralGroup n))
    (hM : M.index = 2) : z n ∈ M := by
  have h2 : r n ^ 2 ∈ M := Subgroup.sq_mem_of_index_two hM (r n)
  have hev : half n = 2 * (half n / 2) := by
    obtain ⟨k, hk⟩ := half_even (by omega : 3 ≤ n)
    omega
  have : z n = (r n ^ 2) ^ (half n / 2) := by
    rw [← pow_mul]
    unfold z
    congr 1
  rw [this]
  exact Subgroup.pow_mem _ h2 _

theorem sd_centralizer_s (n : ℕ) (hn : 4 ≤ n) (g : SemidihedralGroup n) (hg : g * s n = s n * g) :
    g = 1 ∨ g = z n ∨ g = s n ∨ g = z n * s n := by
  have hn3 : 3 ≤ n := by omega
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn3).symm.surjective g
  change element n hn3 i e * s n = s n * element n hn3 i e at hg
  rw [s_eq_element n hn3] at hg
  change element n hn3 i e = _ ∨ element n hn3 i e = _ ∨ element n hn3 i e = _ ∨ element n hn3 i e = _
  rcases exponent_cases e with rfl | rfl
  · rw [element_reflection_mul, element_rotation_mul, element_eq_iff] at hg
    have h1 : twist n * i = i := by linear_combination -hg.1
    rcases (twist_fixed_iff n hn i).1 h1 with rfl | rfl
    · left; rw [element_zero_zero]
    · right; left; rw [z_eq_element n hn3]
  · rw [element_reflection_mul, element_reflection_mul, element_eq_iff] at hg
    have h1 : twist n * i = i := by linear_combination -hg.1
    rcases (twist_fixed_iff n hn i).1 h1 with rfl | rfl
    · right; right; left; rw [s_eq_element n hn3]
    · right; right; right
      rw [z_eq_element n hn3, s_eq_element n hn3, element_rotation_mul, add_zero]



theorem sd_quarter_mem_of_index_two (n : ℕ) (hn : 4 ≤ n) (M : Subgroup (SemidihedralGroup n))
    (hM : M.index = 2) : r n ^ (half n / 2) ∈ M := by
  have h2 : r n ^ 2 ∈ M := Subgroup.sq_mem_of_index_two hM (r n)
  have h4 : 4 ∣ half n := by
    have h1 : half n = 2 ^ (n - 2) := rfl
    rw [h1]
    calc 4 = 2 ^ 2 := by norm_num
      _ ∣ 2 ^ (n - 2) := pow_dvd_pow 2 (by omega)
  obtain ⟨m, hm⟩ := h4
  have : r n ^ (half n / 2) = (r n ^ 2) ^ m := by
    rw [← pow_mul]
    congr 1
    omega
  rw [this]
  exact Subgroup.pow_mem _ h2 _

theorem sd_quarter_facts (n : ℕ) (hn : 4 ≤ n) :
    (r n ^ (half n / 2)) * (r n ^ (half n / 2)) = z n ∧
    s n * (r n ^ (half n / 2)) * (s n)⁻¹ = (r n ^ (half n / 2))⁻¹ := by
  have hn3 : 3 ≤ n := by omega
  have h4 : 4 ∣ half n := by
    have h1 : half n = 2 ^ (n - 2) := rfl
    rw [h1]
    calc 4 = 2 ^ 2 := by norm_num
      _ ∣ 2 ^ (n - 2) := pow_dvd_pow 2 (by omega)
  obtain ⟨m, hm⟩ := h4
  have hq : half n / 2 = 2 * m := by omega
  rw [hq]
  constructor
  · rw [← pow_add]
    unfold z
    congr 1
    omega
  · rw [r_pow_eq_element n hn3, s_eq_element n hn3, conjugate_rotation_by_reflection,
      element_rotation_inv n hn3]
    congr 1
    have hdvd : modulus n ∣ half n * (2 * m) :=
      ⟨m, by rw [modulus_eq_two_mul_half (by omega)]; ring⟩
    have hz : ((half n * (2 * m) : ℕ) : ZMod (modulus n)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    push_cast at hz
    unfold twist
    push_cast
    linear_combination hz

theorem sd_card (n : ℕ) (hn : 3 ≤ n) : Nat.card (SemidihedralGroup n) = 2 * modulus n := by
  rw [Nat.card_congr (coordinateEquiv n hn), Nat.card_prod, Nat.card_zmod, Nat.card_zmod]
  ring

theorem sd_sq_ne_z (n : ℕ) (hn : 4 ≤ n) (M : Subgroup (SemidihedralGroup n)) (hM : M.index = 2)
    (hr : r n ∉ M) (hs : s n ∉ M) (u : SemidihedralGroup n) (hu : u ∉ M) : u * u ≠ z n := by
  have hn3 : 3 ≤ n := by omega
  have h2 : r n ^ 2 ∈ M := Subgroup.sq_mem_of_index_two hM (r n)
  have hmod : modulus n = 2 * half n := modulus_eq_two_mul_half (by omega)
  have hpos : 0 < half n := by
    have h1 : half n = 2 ^ (n - 2) := rfl
    rw [h1]
    positivity
  have h4 : 4 ∣ half n := by
    have h1 : half n = 2 ^ (n - 2) := rfl
    rw [h1]
    calc 4 = 2 ^ 2 := by norm_num
      _ ∣ 2 ^ (n - 2) := pow_dvd_pow 2 (by omega)
  have hrs : r n * s n ∈ M := (Subgroup.mul_mem_iff_of_index_two hM).2 (iff_of_false hr hs)
  have hrM : ∀ k : ℕ, k % 2 = 0 → r n ^ k ∈ M := by
    intro k hk
    have : r n ^ k = (r n ^ 2) ^ (k / 2) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [this]
    exact Subgroup.pow_mem _ h2 _
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn3).symm.surjective u
  change element n hn3 i e * element n hn3 i e ≠ z n
  intro hsq
  rw [z_eq_element n hn3] at hsq
  rcases exponent_cases e with rfl | rfl
  · rw [element_rotation_mul, element_eq_iff] at hsq
    have hi : i + i = ((half n : ℕ) : ZMod (modulus n)) := hsq.1
    have hodd : i.val % 2 = 1 := by
      by_contra hev
      apply hu
      have := hrM i.val (by omega)
      rwa [r_pow_eq_element n hn3, ZMod.natCast_zmod_val] at this
    have h5 : ((2 * i.val : ℕ) : ZMod (modulus n)) = ((half n : ℕ) : ZMod (modulus n)) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      linear_combination hi
    have h6 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h5
    have hv : i.val < modulus n := ZMod.val_lt i
    have hlt : half n < modulus n := by omega
    rw [Nat.mod_eq_of_lt hlt] at h6
    have hq := Nat.div_add_mod (2 * i.val) (modulus n)
    have hqlt : 2 * i.val / modulus n < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    generalize 2 * i.val / modulus n = q at hq hqlt
    rw [h6] at hq
    interval_cases q <;> omega
  · rw [← sq, element_reflection_sq, element_eq_iff] at hsq
    have hi : (half n : ZMod (modulus n)) * i = (half n : ZMod (modulus n)) := hsq.1
    have h5 : ((half n * i.val : ℕ) : ZMod (modulus n)) = ((half n * 1 : ℕ) : ZMod (modulus n)) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      linear_combination hi
    have h6 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h5
    have h6' : half n * i.val ≡ half n * 1 [MOD half n * 2] := by
      have e : half n * 2 = modulus n := by omega
      rw [e]
      exact h6
    have h7 := (Nat.ModEq.mul_left_cancel_iff' hpos.ne').1 h6'
    have hodd : i.val % 2 = 1 := by
      have := h7
      unfold Nat.ModEq at this
      omega
    apply hu
    change element n hn3 i 1 ∈ M
    have e1 : element n hn3 i 1 =
        element n hn3 ((i.val - 1 : ℕ) : ZMod (modulus n)) 0 * element n hn3 1 1 := by
      rw [element_rotation_mul]
      congr 1
      have : ((i.val - 1 : ℕ) : ZMod (modulus n)) = (i.val : ZMod (modulus n)) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      rw [this, ZMod.natCast_zmod_val]
      ring
    have e2 : element n hn3 1 1 = r n * s n := by
      have h1 : r n = element n hn3 1 0 := by
        have := r_pow_eq_element n hn3 1
        simpa using this
      rw [h1, s_eq_element n hn3, element_rotation_mul]
      congr 1
      ring
    rw [e1, e2]
    refine M.mul_mem ?_ hrs
    rw [← r_pow_eq_element n hn3]
    exact hrM _ (by omega)

theorem sd_facts_main {G : Type} [Group G] (P : Subgroup G) (ze y : G) (hz : ze ∈ P) (hz2 : ze * ze = 1)
    (hz1 : ze ≠ 1) (hy2 : y * y = 1) (hyP : y ∉ P) (hN : ∀ p ∈ P, y * p * y⁻¹ ∈ P)
    {n : ℕ}
    (hn : 4 ≤ n) (ι : ↥(P ⊔ Subgroup.zpowers y) ≃* SemidihedralGroup n) :
    (∀ p ∈ P, y * p = p * y → p = 1 ∨ p = ze) ∧
    (∀ v ∈ P, (v * y) * (v * y) = 1 → ∃ p ∈ P, p⁻¹ * y * p = v * y) ∧
    (∃ u₁ ∈ P, u₁ * u₁ = ze ∧ y * u₁ * y⁻¹ = u₁⁻¹) ∧
    ((¬ ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) → ∀ v ∈ P, (v * y) * (v * y) ≠ ze) := by
  classical
  have hn3 : 3 ≤ n := by omega
  have : Finite (SemidihedralGroup n) := presentation_finite n hn3
  set W : Subgroup G := P ⊔ Subgroup.zpowers y with hW
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hPW : P ≤ W := le_sup_left
  have hyW : y ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  let Wd : Subgroup G :=
    { carrier := {g | g ∈ P ∨ ∃ p ∈ P, g = p * y}
      mul_mem' := by
        rintro a b (ha | ⟨p, hp, rfl⟩) (hb | ⟨q, hq, rfl⟩)
        · exact Or.inl (P.mul_mem ha hb)
        · exact Or.inr ⟨a * q, P.mul_mem ha hq, by rw [mul_assoc]⟩
        · refine Or.inr ⟨p * (y * b * y⁻¹), P.mul_mem hp (hN b hb), ?_⟩
          group
        · refine Or.inl ?_
          have : p * y * (q * y) = p * (y * q * y⁻¹) := by
            calc p * y * (q * y) = p * (y * q * y⁻¹) * (y * y) := by group
              _ = p * (y * q * y⁻¹) := by rw [hy2, mul_one]
          rw [this]
          exact P.mul_mem hp (hN q hq)
      one_mem' := Or.inl P.one_mem
      inv_mem' := by
        rintro a (ha | ⟨p, hp, rfl⟩)
        · exact Or.inl (P.inv_mem ha)
        · refine Or.inr ⟨y * p⁻¹ * y⁻¹, hN _ (P.inv_mem hp), ?_⟩
          calc (p * y)⁻¹ = y⁻¹ * p⁻¹ := mul_inv_rev _ _
            _ = y * p⁻¹ := by rw [hyinv]
            _ = y * p⁻¹ * y⁻¹ * y := by group }
  have hdec : ∀ g ∈ W, g ∈ P ∨ ∃ p ∈ P, g = p * y := by
    intro g hg
    have : W ≤ Wd := sup_le (fun x hx => Or.inl hx)
      ((Subgroup.zpowers_le).2 (Or.inr ⟨1, P.one_mem, (one_mul y).symm⟩))
    exact this hg
  have hidx : (P.subgroupOf W).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨y, hyW⟩, ?_⟩
    rintro ⟨b, hb⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases hdec b hb with hbP | ⟨p, hp, rfl⟩
    · right
      refine ⟨hbP, fun h => hyP ?_⟩
      have := P.mul_mem (P.inv_mem hbP) h
      simpa using this
    · left
      refine ⟨?_, fun h => hyP ?_⟩
      · have : p * y * y = p := by rw [mul_assoc, hy2, mul_one]
        rw [this]
        exact hp
      · have := P.mul_mem (P.inv_mem hp) h
        simpa using this
  set M : Subgroup (SemidihedralGroup n) := (P.subgroupOf W).map (ι : ↥W →* SemidihedralGroup n) with hM
  have hMidx : M.index = 2 := by
    rw [hM, Subgroup.index_map_equiv (P.subgroupOf W) ι, hidx]
  have hMn : M.Normal := Subgroup.normal_of_index_eq_two hMidx
  have hzS : z n ∈ M := sd_z_mem_of_index_two n hn M hMidx
  have hmemM : ∀ w : W, ι w ∈ M ↔ (w : G) ∈ P := by
    intro w
    rw [hM, Subgroup.mem_map]
    constructor
    · rintro ⟨w', hw', h⟩
      have : w' = w := ι.injective h
      subst this
      exact hw'
    · intro h
      exact ⟨w, h, rfl⟩
  set y' : SemidihedralGroup n := ι ⟨y, hyW⟩ with hy'
  have hy'2 : y' * y' = 1 := by
    rw [hy', ← map_mul]
    have : (⟨y, hyW⟩ * ⟨y, hyW⟩ : W) = 1 := Subtype.ext (by simpa using hy2)
    rw [this, map_one]
  have hy'ne : y' ≠ 1 := by
    intro h
    apply hyP
    have : (⟨y, hyW⟩ : W) = 1 := ι.injective (by rw [← hy', h, map_one])
    have h6 := congrArg Subtype.val this
    simp only [Subgroup.coe_one] at h6
    rw [h6]
    exact P.one_mem
  have hy'M : y' ∉ M := fun h => hyP ((hmemM _).1 h)
  have hord2 : ∀ g : SemidihedralGroup n, g * g = 1 → g ≠ 1 → orderOf g = 2 := by
    intro g h1 h2
    exact orderOf_eq_prime (by rw [sq]; exact h1) h2
  have hconj : ∀ g : SemidihedralGroup n, g * g = 1 → g ≠ 1 → g ∉ M → IsConj (s n) g := by
    intro g h1 h2 hgM
    rcases CFSG.QuasiDihedralFusion.sd_involution_cases hn g (hord2 g h1 h2) with h | h
    · exact absurd (h ▸ hzS) hgM
    · exact h
  obtain ⟨c, hc⟩ := isConj_iff.1 (hconj y' hy'2 hy'ne hy'M)
  have hzcoe : ι ⟨ze, hPW hz⟩ = z n := by
    set zS : SemidihedralGroup n := ι ⟨ze, hPW hz⟩ with hzSdef
    have h1 : zS * zS = 1 := by
      rw [hzSdef, ← map_mul]
      have : (⟨ze, hPW hz⟩ * ⟨ze, hPW hz⟩ : W) = 1 := Subtype.ext (by simpa using hz2)
      rw [this, map_one]
    have h2 : zS ≠ 1 := by
      intro h
      apply hz1
      have : (⟨ze, hPW hz⟩ : W) = 1 := ι.injective (by rw [← hzSdef, h, map_one])
      simpa using congrArg Subtype.val this
    have h3 : zS ∈ M := (hmemM _).2 hz
    rcases CFSG.QuasiDihedralFusion.sd_involution_cases hn zS (hord2 zS h1 h2) with h | h
    · exact h
    · exfalso
      obtain ⟨d, hd⟩ := isConj_iff.1 h
      have hsM : s n ∈ M := by
        have : d⁻¹ * zS * d ∈ M := by
          have h9 := hMn.conj_mem _ h3 d⁻¹
          rwa [inv_inv] at h9
        have e : d⁻¹ * zS * d = s n := by rw [← hd]; group
        simpa [e] using this
      apply hy'M
      rw [← hc]
      exact hMn.conj_mem _ hsM c
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp hcomm
    set g : SemidihedralGroup n := ι ⟨p, hPW hp⟩ with hg
    have hgM : g ∈ M := (hmemM _).2 hp
    have hgy : g * y' = y' * g := by
      rw [hg, hy', ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simpa using hcomm.symm)
    have hg' : (c⁻¹ * g * c) * s n = s n * (c⁻¹ * g * c) := by
      have e1 : s n = c⁻¹ * y' * c := by rw [← hc]; group
      rw [e1]
      calc c⁻¹ * g * c * (c⁻¹ * y' * c) = c⁻¹ * (g * y') * c := by group
        _ = c⁻¹ * (y' * g) * c := by rw [hgy]
        _ = c⁻¹ * y' * c * (c⁻¹ * g * c) := by group
    have hzc : c * z n * c⁻¹ = z n := by
      have := Subgroup.mem_center_iff.1 (z_mem_center n hn) c
      rw [this]
      group
    rcases sd_centralizer_s n hn _ hg' with h | h | h | h
    · left
      have : g = 1 := by
        have e : g = c * (c⁻¹ * g * c) * c⁻¹ := by group
        rw [e, h]; group
      have h9 : (⟨p, hPW hp⟩ : W) = 1 := ι.injective (by rw [← hg, this, map_one])
      simpa using congrArg Subtype.val h9
    · right
      have e : g = c * (c⁻¹ * g * c) * c⁻¹ := by group
      have : g = z n := by rw [e, h]; exact hzc
      have : (⟨p, hPW hp⟩ : W) = ⟨ze, hPW hz⟩ := ι.injective (by rw [← hg, this, hzcoe])
      simpa using congrArg Subtype.val this
    · exfalso
      have e : g = c * (c⁻¹ * g * c) * c⁻¹ := by group
      have : g = y' := by rw [e, h, ← hc]
      exact hy'M (this ▸ hgM)
    · exfalso
      have e : g = c * (c⁻¹ * g * c) * c⁻¹ := by group
      have : g = z n * y' := by
        rw [e, h]
        calc c * (z n * s n) * c⁻¹ = (c * z n * c⁻¹) * (c * s n * c⁻¹) := by group
          _ = z n * y' := by rw [hzc, hc]
      apply hy'M
      have h5 : (z n)⁻¹ * g ∈ M := M.mul_mem (M.inv_mem hzS) hgM
      rwa [this, inv_mul_cancel_left] at h5
  · intro v hv huv
    have hvW : v ∈ W := hPW hv
    have huW : v * y ∈ W := W.mul_mem hvW hyW
    set u' : SemidihedralGroup n := ι ⟨v * y, huW⟩ with hu'
    have hu'2 : u' * u' = 1 := by
      rw [hu', ← map_mul]
      have : (⟨v * y, huW⟩ * ⟨v * y, huW⟩ : W) = 1 := Subtype.ext (by simpa using huv)
      rw [this, map_one]
    have huP : v * y ∉ P := fun h => hyP (by simpa using P.mul_mem (P.inv_mem hv) h)
    have hu'M : u' ∉ M := fun h => huP ((hmemM _).1 h)
    have hu'ne : u' ≠ 1 := by
      intro h
      apply huP
      have : (⟨v * y, huW⟩ : W) = 1 := ι.injective (by rw [← hu', h, map_one])
      have h6 := congrArg Subtype.val this
      simp only [Subgroup.coe_one] at h6
      rw [h6]
      exact P.one_mem
    obtain ⟨d, hd⟩ := isConj_iff.1 (hconj u' hu'2 hu'ne hu'M)
    have hgy : (d * c⁻¹) * y' * (d * c⁻¹)⁻¹ = u' := by
      rw [← hc, ← hd]; group
    set w : W := ι.symm (d * c⁻¹) with hw
    have hwy : ((w : G) * y * (w : G)⁻¹) = v * y := by
      have h7 : w * ⟨y, hyW⟩ * w⁻¹ = ⟨v * y, huW⟩ := by
        apply ι.injective
        rw [map_mul, map_mul, map_inv, hw, MulEquiv.apply_symm_apply, ← hy', hgy, hu']
      have h8 := congrArg Subtype.val h7
      simpa using h8
    rcases hdec (w : G) w.2 with hwP | ⟨p, hp, hpw⟩
    · refine ⟨(w : G)⁻¹, P.inv_mem hwP, ?_⟩
      rw [inv_inv]
      exact hwy
    · refine ⟨p⁻¹, P.inv_mem hp, ?_⟩
      rw [inv_inv]
      have : (w : G) * y * (w : G)⁻¹ = p * y * p⁻¹ := by
        rw [hpw]
        calc p * y * y * (p * y)⁻¹ = p * (y * y) * y * p⁻¹ := by
              rw [mul_inv_rev, hyinv]; simp only [mul_assoc]
          _ = p * y * p⁻¹ := by rw [hy2, mul_one]
      rw [← this]
      exact hwy
  ·
    obtain ⟨hq1, hq2⟩ := sd_quarter_facts n hn
    have hrrM := sd_quarter_mem_of_index_two n hn M hMidx
    set rr := r n ^ (half n / 2) with hrr
    set u1S : SemidihedralGroup n := c * rr * c⁻¹ with hu1S
    have hu1M : u1S ∈ M := hMn.conj_mem rr hrrM c
    set u1 : W := ι.symm u1S with hu1
    have hι : ι u1 = u1S := by rw [hu1, MulEquiv.apply_symm_apply]
    refine ⟨(u1 : G), (hmemM u1).1 (by rw [hι]; exact hu1M), ?_, ?_⟩
    · have h1 : u1 * u1 = ⟨ze, hPW hz⟩ := by
        apply ι.injective
        rw [map_mul, hι, hzcoe, hu1S]
        calc c * rr * c⁻¹ * (c * rr * c⁻¹) = c * (rr * rr) * c⁻¹ := by group
          _ = c * z n * c⁻¹ := by rw [hq1]
          _ = z n := by
            have := Subgroup.mem_center_iff.1 (z_mem_center n hn) c
            rw [this]; group
      simpa using congrArg Subtype.val h1
    · have h1 : (⟨y, hyW⟩ : W) * u1 * (⟨y, hyW⟩ : W)⁻¹ = u1⁻¹ := by
        apply ι.injective
        rw [map_mul, map_mul, map_inv, map_inv, hι, ← hy']
        rw [← hc, hu1S]
        calc c * s n * c⁻¹ * (c * rr * c⁻¹) * (c * s n * c⁻¹)⁻¹
            = c * (s n * rr * (s n)⁻¹) * c⁻¹ := by group
          _ = c * rr⁻¹ * c⁻¹ := by rw [hq2]
          _ = (c * rr * c⁻¹)⁻¹ := by group
      simpa using congrArg Subtype.val h1
  · intro hPnc v hv hsq
    have hvW : v ∈ W := hPW hv
    have huW : v * y ∈ W := W.mul_mem hvW hyW
    set u' : SemidihedralGroup n := ι ⟨v * y, huW⟩ with hu'
    have huP : v * y ∉ P := fun h => hyP (by simpa using P.mul_mem (P.inv_mem hv) h)
    have hu'M : u' ∉ M := fun h => huP ((hmemM _).1 h)
    have hu'sq : u' * u' = z n := by
      rw [hu', ← map_mul, ← hzcoe]
      congr 1
      exact Subtype.ext (by simpa using hsq)
    have hsM : s n ∉ M := by
      intro hsM
      apply hy'M
      rw [← hc]
      exact hMn.conj_mem _ hsM c
    have hrM : r n ∉ M := by
      intro hrM
      apply hPnc
      have hcardG : Nat.card (SemidihedralGroup n) = 2 * modulus n := sd_card n hn3
      have hcardM : Nat.card M = modulus n := by
        have h1 := Subgroup.card_mul_index M
        rw [hMidx, hcardG] at h1
        omega
      have hEq : Subgroup.zpowers (r n) = M :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hrM)
          (by rw [Nat.card_zpowers, orderOf_r n hn3, hcardM])
      intro a ha b hb
      have haM : ι ⟨a, hPW ha⟩ ∈ M := (hmemM _).2 ha
      have hbM : ι ⟨b, hPW hb⟩ ∈ M := (hmemM _).2 hb
      rw [← hEq] at haM hbM
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 haM
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hbM
      have hcomm : ι ⟨a, hPW ha⟩ * ι ⟨b, hPW hb⟩ = ι ⟨b, hPW hb⟩ * ι ⟨a, hPW ha⟩ := by
        rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
      have : (⟨a, hPW ha⟩ : W) * ⟨b, hPW hb⟩ = ⟨b, hPW hb⟩ * ⟨a, hPW ha⟩ :=
        ι.injective (by rw [map_mul, map_mul]; exact hcomm)
      simpa using congrArg Subtype.val this
    exact sd_sq_ne_z n hn M hMidx hrM hsM u' hu'M hu'sq

end SDFacts

section QuatNormal

open Subgroup CFSG QuaternionGroup

theorem quat_inv_a (N : ℕ) (i : ZMod (2 * N)) : (a i : QuaternionGroup N)⁻¹ = a (-i) := rfl

theorem quat_inv_xa (N : ℕ) (i : ZMod (2 * N)) : (xa i : QuaternionGroup N)⁻¹ = xa ((N : ZMod (2 * N)) + i) := rfl

theorem quat_mul_ne {n : ℕ} (hn : 2 ≤ n) : (a 1 : QuaternionGroup n) * xa 0 ≠ xa 0 * a 1 := by
  rw [a_mul_xa, xa_mul_a]
  intro h
  have h' : (0 : ZMod (2 * n)) - 1 = 0 + 1 := QuaternionGroup.xa.inj h
  have h2 : ((2 : ℕ) : ZMod (2 * n)) = 0 := by
    push_cast
    linear_combination -h'
  have hdvd := (ZMod.natCast_eq_zero_iff 2 (2 * n)).mp h2
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem index_le_two_of_xa_mem (N : ℕ) [NeZero N] (hN : 2 ≤ N) (Y : Subgroup (QuaternionGroup N))
    [Y.Normal] (j : ZMod (2 * N)) (hj : xa j ∈ Y) : Y.index ≤ 2 := by
  have h1 : xa (j - 2) ∈ Y := by
    have := Subgroup.Normal.conj_mem inferInstance (xa j) hj (a 1)
    have e : a 1 * xa j * (a 1)⁻¹ = xa (j - 2) := by
      rw [a_mul_xa, quat_inv_a, xa_mul_a]
      congr 1
      ring
    rwa [e] at this
  have h2 : a 2 ∈ Y := by
    have h3 := Y.mul_mem hj (Y.inv_mem h1)
    have e : xa j * (xa (j - 2))⁻¹ = a (-2) := by
      rw [quat_inv_xa, xa_mul_xa]
      have : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := ZMod.natCast_self _
      push_cast at this
      congr 1
      linear_combination this
    rw [e] at h3
    have h4 := Y.inv_mem h3
    rwa [quat_inv_a, neg_neg] at h4
  have hcard : Nat.card (Subgroup.zpowers (a 2 : QuaternionGroup N)) = N := by
    rw [Nat.card_zpowers, orderOf_a]
    have h2val : (2 : ZMod (2 * N)).val = 2 := by
      have : (2 : ZMod (2 * N)) = ((2 : ℕ) : ZMod (2 * N)) := by norm_num
      rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [h2val]
    have : Nat.gcd (2 * N) 2 = 2 := Nat.gcd_eq_right (dvd_mul_right 2 N)
    rw [this]
    omega
  have hle : Subgroup.zpowers (a 2 : QuaternionGroup N) ≤ Y := (Subgroup.zpowers_le).2 h2
  have hdvd : N ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hcard] at this
  have hform : ∀ k : ℤ, ∃ i, (a 2 : QuaternionGroup N) ^ k = a i := by
    intro k
    induction k using Int.induction_on with
    | zero => exact ⟨0, by rw [zpow_zero, one_def]⟩
    | succ k ih =>
      obtain ⟨i, hi⟩ := ih
      exact ⟨i + 2, by rw [zpow_add_one, hi, a_mul_a]⟩
    | pred k ih =>
      obtain ⟨i, hi⟩ := ih
      exact ⟨i - 2, by rw [zpow_sub_one, hi, quat_inv_a, a_mul_a]; congr 1; ring⟩
  have hne : Nat.card Y ≠ N := by
    intro heq
    have hEq : Subgroup.zpowers (a 2 : QuaternionGroup N) = Y :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, heq])
    have hmem : xa j ∈ Subgroup.zpowers (a 2 : QuaternionGroup N) := hEq ▸ hj
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    obtain ⟨i, hi⟩ := hform k
    rw [hi] at hk
    cases hk
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : 2 ≤ c := by
    rcases Nat.lt_or_ge c 2 with h | h
    · exfalso
      interval_cases c
      · simp at hc
        exact (Nat.card_pos (α := Y)).ne' hc
      · simp at hc
        exact hne hc
    · exact h
  have hQcard : Nat.card (QuaternionGroup N) = 4 * N := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hidx := Subgroup.card_mul_index Y
  rw [hQcard, hc] at hidx
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h5 : c * Y.index = 4 := by
    have : N * (c * Y.index) = N * 4 := by
      calc N * (c * Y.index) = N * c * Y.index := by ring
        _ = 4 * N := hidx
        _ = N * 4 := by ring
    exact Nat.eq_of_mul_eq_mul_left hNpos this
  nlinarith


theorem quat_normal_index : CFSG.GH74.GLS.Stage1.Thm3.Sec6.Quat_normal_index := by
  intro G _ _ X Y hYX hnorm ⟨n, hn3, ⟨eX⟩⟩ ⟨m, hm3, ⟨eY⟩⟩
  have hNpos : 0 < 2 ^ (n - 2) := by positivity
  have : NeZero (2 ^ (n - 2)) := ⟨hNpos.ne'⟩
  have hN2 : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk2 : 2 ≤ 2 ^ (m - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set Y0 : Subgroup ↥X := Y.subgroupOf X with hY0
  have hY0n : Y0.Normal := ⟨fun y hy x => by
    rw [hY0, Subgroup.mem_subgroupOf] at hy ⊢
    exact hnorm x x.2 y hy⟩
  set Y' : Subgroup (QuaternionGroup (2 ^ (n - 2))) := Y0.map eX.toMonoidHom with hY'
  have hY'n : Y'.Normal := Subgroup.Normal.map hY0n eX.toMonoidHom (fun b => ⟨eX.symm b, by simp⟩)
  have hxa : ∃ j, xa j ∈ Y' := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ u ∈ Y', ∃ i, u = a i := by
      intro u hu
      cases u with
      | a i => exact ⟨i, rfl⟩
      | xa i => exact absurd hu (hcon i)
    let φ : QuaternionGroup (2 ^ (m - 2)) ≃* Y' :=
      eY.symm.trans ((Subgroup.subgroupOfEquivOfLe hYX).symm.trans
        (Subgroup.equivMapOfInjective Y0 eX.toMonoidHom eX.injective))
    have hcomm : ∀ u v : Y', u * v = v * u := by
      intro u v
      obtain ⟨i, hi⟩ := hall u u.2
      obtain ⟨j, hj⟩ := hall v v.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hi, hj, a_mul_a, a_mul_a, add_comm]
    apply quat_mul_ne hk2
    apply φ.injective
    rw [map_mul, map_mul]
    exact hcomm _ _
  obtain ⟨j, hj⟩ := hxa
  have hidx := index_le_two_of_xa_mem (2 ^ (n - 2)) hN2 Y' j hj
  have : Y'.index = Y0.index := Subgroup.index_map_equiv Y0 eX
  show (Y.subgroupOf X).index ≤ 2
  rw [← hY0, ← this]
  exact hidx

end QuatNormal

section CosetSq

open Subgroup CFSG QuaternionGroup CFSG.DisconnectedInvolutionGraph CFSG.DisconnectedInvolutionGraph.Helpers

theorem quat_rot_cyclic (N : ℕ) [NeZero N] (Y : Subgroup (QuaternionGroup N))
    (h : ∀ g ∈ Y, ∃ i, g = a i) : IsCyclic Y := by
  have hle : Y ≤ Subgroup.zpowers (a 1 : QuaternionGroup N) := by
    intro g hg
    obtain ⟨i, rfl⟩ := h g hg
    refine ⟨(i.val : ℤ), ?_⟩
    simp only [zpow_natCast]
    rw [a_one_pow, ZMod.natCast_zmod_val]
  exact Subgroup.isCyclic_of_le hle

theorem quat_top_of_a_one_xa (N : ℕ) [NeZero N] (Y : Subgroup (QuaternionGroup N))
    (h1 : (a 1 : QuaternionGroup N) ∈ Y) (j : ZMod (2 * N)) (hj : xa j ∈ Y) :
    ∀ g : QuaternionGroup N, g ∈ Y := by
  intro g
  have hrot : ∀ i : ZMod (2 * N), (a i : QuaternionGroup N) ∈ Y := by
    intro i
    have : (a i : QuaternionGroup N) = (a 1) ^ i.val := by
      rw [a_one_pow, ZMod.natCast_zmod_val]
    rw [this]
    exact Subgroup.pow_mem _ h1 _
  cases g with
  | a i => exact hrot i
  | xa k =>
    have : (xa k : QuaternionGroup N) = xa j * a (k - j) := by
      rw [xa_mul_a]; congr 1; ring
    rw [this]
    exact Y.mul_mem hj (hrot _)

theorem twoGroup_coset_sq_core {G : Type} [Group G] [Finite G] (X Q : Subgroup G) (z b : G)
    (hX : IsPGroup 2 ↥X) (hbX : b ∈ X) (hbQ : b ∉ Q)
    (huniq : ∀ u ∈ X, u * u = 1 → u = 1 ∨ u = z) (hXc : ¬ IsCyclic ↥X) :
    ∃ t ∈ X, t ∉ Q ∧ t * t = z := by
  have hinv : ∀ u : Involution ↥X, ((u.1 : ↥X) : G) = z := by
    intro u
    have h := u.2
    have hsq : u.1 * u.1 = 1 := by
      have := pow_orderOf_eq_one u.1
      rwa [h, sq] at this
    have hne : u.1 ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at h
      omega
    have hG : ((u.1 : ↥X) : G) * ((u.1 : ↥X) : G) = 1 := by
      have := congrArg Subtype.val hsq
      simpa using this
    rcases huniq _ u.1.2 hG with h1 | h1
    · exact absurd (Subtype.ext h1) hne
    · exact h1
  have hrank : NoCommutingDistinctInvolutions ↥X := by
    intro u v _
    exact Subtype.ext (Subtype.ext ((hinv u).trans (hinv v).symm))
  rcases rank_one_two_cyclic_or_quaternion hX hrank with hcyc | ⟨e, he1, ⟨φ⟩⟩
  · exact absurd hcyc hXc
  · have : NeZero (2 ^ e) := ⟨by positivity⟩
    set N := 2 ^ e with hN
    set Q'' : Subgroup (QuaternionGroup N) := (Q.subgroupOf X).map φ.symm.toMonoidHom with hQ''
    have hmem : ∀ g : QuaternionGroup N, g ∈ Q'' ↔ ((φ g : ↥X) : G) ∈ Q := by
      intro g
      rw [hQ'', Subgroup.mem_map_equiv]
      simp [Subgroup.mem_subgroupOf]
    have hN0 : ((N : ℕ) : ZMod (2 * N)) ≠ 0 := by
      intro h
      have := (ZMod.natCast_eq_zero_iff N (2 * N)).1 h
      have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      have := Nat.le_of_dvd hpos this
      omega
    have hex : ∃ i, (xa i : QuaternionGroup N) ∉ Q'' := by
      by_cases hxa : ∃ j, xa j ∈ Q''
      · obtain ⟨j, hj⟩ := hxa
        refine ⟨j + 1, fun h => ?_⟩
        have h1 : (a 1 : QuaternionGroup N) ∈ Q'' := by
          have h2 := Q''.mul_mem h (Q''.inv_mem hj)
          have e : xa (j + 1) * (xa j)⁻¹ = a (-1) := by
            show xa (j + 1) * xa ((N : ZMod (2 * N)) + j) = a (-1)
            rw [xa_mul_xa]
            have : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := ZMod.natCast_self _
            push_cast at this
            congr 1
            linear_combination this
          rw [e] at h2
          have h3 := Q''.inv_mem h2
          have e2 : (a (-1) : QuaternionGroup N)⁻¹ = a 1 := by
            show a (-(-1)) = a 1
            rw [neg_neg]
          rwa [e2] at h3
        have hall := quat_top_of_a_one_xa N Q'' h1 j hj
        apply hbQ
        have hb := (hmem (φ.symm ⟨b, hbX⟩)).1 (hall _)
        simpa using hb
      · push Not at hxa
        exact ⟨0, hxa 0⟩
    obtain ⟨i, hi⟩ := hex
    refine ⟨((φ (xa i) : ↥X) : G), (φ (xa i)).2, fun h => hi ((hmem _).2 h), ?_⟩
    have hsq : (xa i : QuaternionGroup N) * xa i = a (N : ZMod (2 * N)) := by
      rw [xa_mul_xa]; congr 1; ring
    have haN : ((φ (a (N : ZMod (2 * N))) : ↥X) : G) = z := by
      have h1 : (a (N : ZMod (2 * N)) : QuaternionGroup N) * a N = 1 := by
        rw [a_mul_a, one_def]
        have : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := ZMod.natCast_self _
        push_cast at this
        congr 1
        linear_combination this
      have h2 : (a (N : ZMod (2 * N)) : QuaternionGroup N) ≠ 1 := by
        rw [one_def]
        intro h
        exact hN0 (QuaternionGroup.a.inj h)
      have h3 : orderOf (φ (a (N : ZMod (2 * N)))) = 2 := by
        rw [MulEquiv.orderOf_eq]
        exact orderOf_eq_prime (by rw [sq]; exact h1) h2
      exact hinv ⟨φ (a (N : ZMod (2 * N))), h3⟩
    rw [← haN, ← hsq, map_mul, Subgroup.coe_mul]

open CFSG.GH74.GLS.Stage1.Thm3.Sec5 in
theorem twoGroup_coset_sq : TwoGroup_coset_sq := by
  intro G _ _ X Q z b hX hQX hbX hbQ _ _ huniq hQc
  have hXc : ¬ IsCyclic ↥X := fun hXc => hQc (by
    have : IsCyclic ↥(Q.subgroupOf X) := inferInstance
    exact (Subgroup.subgroupOfEquivOfLe hQX).isCyclic.1 this)
  exact twoGroup_coset_sq_core X Q z b hX hbX hbQ huniq hXc

end CosetSq

section SDProps

open Subgroup CFSG CFSG.Semidihedral CFSG.Open

theorem quatGroup_not_comm {G : Type} [Group G] (P : Subgroup G) (hP : ∃ n, IVK.IsQuaternionTwoGroup ↥P n) :
    ¬ ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  obtain ⟨n, hn3, ⟨ι⟩⟩ := hP
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hN2 : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  intro hc
  apply quat_mul_ne hN2
  have h1 : ι.symm (QuaternionGroup.a 1) * ι.symm (QuaternionGroup.xa 0) =
      ι.symm (QuaternionGroup.xa 0) * ι.symm (QuaternionGroup.a 1) :=
    Subtype.ext (hc _ (ι.symm (QuaternionGroup.a 1)).2 _ (ι.symm (QuaternionGroup.xa 0)).2)
  have h2 := congrArg ι h1
  simpa using h2

open CFSG.GH74.GLS.Stage1.Thm3.Sec6 in
theorem sd_facts : SD_facts := by
  intro G _ _ P z y hq hz hz2 hz1 hy2 hyP hN ⟨n, hn4, ⟨ι⟩⟩
  obtain ⟨h1, h2, -⟩ := sd_facts_main P z y hz hz2 hz1 hy2 hyP hN hn4 ι
  exact ⟨h1, h2⟩

open CFSG.GH74.GLS.Stage1.Thm3.Sec4 in
theorem sd_involution_fusion : SD_involution_fusion := by
  intro X _ _ P z t hq hz hz2 hz1 hzc huniq ht2 htP htN ⟨n, hn4, ⟨ι⟩⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hN : ∀ p ∈ P, t * p * t⁻¹ ∈ P := fun p hp => by rw [htinv]; exact htN p hp
  obtain ⟨h1, h2, ⟨u₁, hu₁P, hu₁sq, hu₁conj⟩, -⟩ :=
    sd_facts_main P z t hz hz2 hz1 ht2 htP hN hn4 ι
  rw [htinv] at hu₁conj
  refine ⟨⟨u₁, hu₁P, hu₁sq, hu₁conj, ?_⟩, ?_⟩
  ·
    have h3 : u₁⁻¹ * t = t * u₁ := by
      calc u₁⁻¹ * t = (t * u₁ * t) * t := by rw [hu₁conj]
        _ = t * u₁ := by rw [mul_assoc, ht2, mul_one]
    have h4 : (u₁⁻¹ * t) * (u₁⁻¹ * t) = 1 := by
      calc (u₁⁻¹ * t) * (u₁⁻¹ * t) = u₁⁻¹ * (t * u₁⁻¹ * t) := by group
        _ = u₁⁻¹ * u₁ := by
            congr 1
            have : t * u₁⁻¹ * t = (t * u₁ * t)⁻¹ := by
              rw [mul_inv_rev, mul_inv_rev, htinv]; group
            rw [this, hu₁conj, inv_inv]
        _ = 1 := inv_mul_cancel u₁
    obtain ⟨p, hp, hp'⟩ := h2 u₁⁻¹ (P.inv_mem hu₁P) h4
    exact ⟨p, hp, by rw [hp', h3]⟩
  ·
    have htz : t * z * t = z := by
      have hmem : t * z * t ∈ P := htN z hz
      have hsq : (t * z * t) * (t * z * t) = 1 := by
        calc (t * z * t) * (t * z * t) = t * (z * (t * t) * z) * t := by group
          _ = 1 := by rw [ht2, mul_one, hz2, mul_one, ht2]
      rcases huniq _ hmem hsq with h | h
      · exfalso
        apply hz1
        have : z = t * (t * z * t) * t := by
          calc z = (t * t) * z * (t * t) := by rw [ht2]; group
            _ = t * (t * z * t) * t := by group
        rw [this, h]; simpa [mul_assoc] using ht2
      · exact h
    have hzt : z * t = t * z := by
      calc z * t = (t * z * t) * t := by rw [htz]
        _ = t * z := by rw [mul_assoc, ht2, mul_one]
    have h4 : (z * t) * (z * t) = 1 := by
      calc (z * t) * (z * t) = z * (t * z * t) := by group
        _ = z * z := by rw [htz]
        _ = 1 := hz2
    obtain ⟨p, hp, hp'⟩ := h2 z hz h4
    exact ⟨p, hp, by rw [hp', hzt]⟩

end SDProps

end CFSG.GH74.GLS.IVK.Lifted
