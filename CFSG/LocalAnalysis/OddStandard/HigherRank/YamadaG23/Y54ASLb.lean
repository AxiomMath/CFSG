module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54ASLa

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

private lemma exists_pair_ne_one {V : Type} [Group V] [Finite V] (hcard : Nat.card V = 8) :
    ∃ a b : V, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hcardV : Fintype.card V = 8 := by rw [Fintype.card_eq_nat_card, hcard]
  have hAcard : Nat.card {v : V // v ≠ 1} = 7 := by
    rw [Nat.subtype_card (({1} : Finset V)ᶜ) (by intro x; simp)]
    have h := Finset.card_compl_add_card ({1} : Finset V)
    rw [Finset.card_singleton] at h
    omega
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card (α := {v : V // v ≠ 1})
    (by rw [Fintype.card_eq_nat_card]; omega)
  exact ⟨x.1, y.1, x.2, y.2, fun h => hxy (Subtype.ext h)⟩

variable {W V N : Type} [Group W] [Finite W] [Group V] [Finite V] [Group N] [Finite N]

theorem asl_complement (act : N →* MulAut W) (vact : N →* MulAut V) (π : W →* V)
    (hπ : Function.Surjective π) (hπact : ∀ (n : N) (w : W), π (act n w) = vact n (π w))
    (hW : ∀ w : W, w ^ 2 = 1) (hV8 : Nat.card V = 8)
    (hU : ∀ n : N, ∀ u ∈ π.ker, act n u = u)
    (htrans : ∀ a b a' b' : V, a ≠ 1 → b ≠ 1 → a ≠ b → a' ≠ 1 → b' ≠ 1 → a' ≠ b' →
      ∃ n : N, vact n a = a' ∧ vact n b = b')
    (S : Subgroup N) (hSN : Nat.card N = 21 * Nat.card S) {w₀ : W}
    (hw₀ : ∀ x ∈ S, act x w₀ = w₀) (hw₀1 : π w₀ ≠ 1) :
    ∃ M : Subgroup W, (∀ (n : N), ∀ m ∈ M, act n m ∈ M) ∧ M ⊓ π.ker = ⊥ ∧
      M ⊔ π.ker = ⊤ := by
  classical
  have hW2 : ∀ w : W, w * w = 1 := by
    intro w
    simpa [pow_two] using hW w
  have hcomm : ∀ a b : W, a * b = b * a := by
    intro a b
    have h : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hW2 (a * b))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hW2 a),
      inv_eq_of_mul_eq_one_right (hW2 b)] at h
    exact h.symm
  letI : CommGroup W := { ‹Group W› with mul_comm := hcomm }
  have hV2 : ∀ v : V, v ^ 2 = 1 := by
    intro v
    obtain ⟨w, rfl⟩ := hπ v
    rw [← map_pow, hW w, map_one]
  have hmul_ne_one : ∀ a b : V, a ≠ 1 → b ≠ 1 → a ≠ b → a * b ≠ 1 := by
    intro a b _ _ hab h
    apply hab
    have h1 : a = b⁻¹ := mul_eq_one_iff_eq_inv.mp h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV2 b)
  obtain ⟨s, hs1, hsπ, hseq⟩ :=
    asl_section act vact π hπ hπact hW hV8 hU htrans S hSN hw₀ hw₀1
  obtain ⟨a, b, ha, hb, hab⟩ := exists_pair_ne_one hV8
  let u₀ : W := s a * s b * s (a * b)
  have hu₀ker : u₀ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    show π (s a * s b * s (a * b)) = 1
    rw [map_mul, map_mul, hsπ, hsπ, hsπ, ← pow_two]
    exact hV2 (a * b)
  have hu₀π : π u₀ = 1 := MonoidHom.mem_ker.mp hu₀ker
  have hu₀fix : ∀ n : N, act n u₀ = u₀ := fun n => hU n u₀ hu₀ker
  have hc : ∀ a' b' : V, a' ≠ 1 → b' ≠ 1 → a' ≠ b' →
      s a' * s b' * s (a' * b') = u₀ := by
    intro a' b' ha' hb' hab'
    obtain ⟨n, hn1, hn2⟩ := htrans a b a' b' ha hb hab ha' hb' hab'
    have hab_ne : a * b ≠ 1 := hmul_ne_one a b ha hb hab
    have hvab : vact n (a * b) = a' * b' := by rw [map_mul, hn1, hn2]
    calc s a' * s b' * s (a' * b')
        = s (vact n a) * s (vact n b) * s (vact n (a * b)) := by rw [hn1, hn2, hvab]
      _ = act n (s a) * act n (s b) * act n (s (a * b)) := by
            rw [hseq n a ha, hseq n b hb, hseq n (a * b) hab_ne]
      _ = act n (s a * s b * s (a * b)) := by rw [map_mul, map_mul]
      _ = act n u₀ := rfl
      _ = u₀ := hu₀fix n
  let s' : V → W := fun v => if v = 1 then 1 else s v * u₀
  have hs'1 : s' 1 = 1 := by simp [s']
  have hπs' : ∀ v : V, π (s' v) = v := by
    intro v
    by_cases hv : v = 1
    · rw [hv, hs'1, map_one]
    · have hs'v : s' v = s v * u₀ := by simp [s', hv]
      rw [hs'v, map_mul, hsπ v, hu₀π, mul_one]
  have hkey : ∀ (n : N) (v : V), act n (s' v) = s' (vact n v) := by
    intro n v
    by_cases hv : v = 1
    · rw [hv]
      simp [s']
    · have hv' : vact n v ≠ 1 := by
        intro h
        exact hv ((vact n).injective (by rw [h, map_one]))
      have hs'v : s' v = s v * u₀ := by simp [s', hv]
      have hs'v' : s' (vact n v) = s (vact n v) * u₀ := by simp [s', hv']
      rw [hs'v, hs'v', map_mul, hu₀fix n, ← hseq n v hv]
  have hs'mul : ∀ x y : V, s' (x * y) = s' x * s' y := by
    intro x y
    by_cases hx : x = 1
    · rw [hx]; simp [s']
    by_cases hy : y = 1
    · rw [hy]; simp [s']
    by_cases hxy : x = y
    · rw [← hxy]
      have hxx : x * x = 1 := by rw [← pow_two]; exact hV2 x
      have hpx : s' x * s' x = 1 := by rw [← pow_two]; exact hW (s' x)
      rw [hxx, hs'1, hpx]
    · have hxy_ne : x * y ≠ 1 := hmul_ne_one x y hx hy hxy
      have hcxy : s x * s y * s (x * y) = u₀ := hc x y hx hy hxy
      have hsx : s' x = s x * u₀ := by simp [s', hx]
      have hsy : s' y = s y * u₀ := by simp [s', hy]
      have hsxy : s' (x * y) = s (x * y) * u₀ := by simp [s', hxy_ne]
      rw [hsxy, hsx, hsy]
      have hu₀sq : u₀ * u₀ = 1 := by rw [← pow_two]; exact hW u₀
      have hcsq : s (x * y) * s (x * y) = 1 := by
        rw [← pow_two]; exact hW (s (x * y))
      have hsplit : s x * s y = u₀ * s (x * y) := by
        calc s x * s y
            = s x * s y * (s (x * y) * s (x * y)) := by rw [hcsq, mul_one]
          _ = (s x * s y * s (x * y)) * s (x * y) := by ac_rfl
          _ = u₀ * s (x * y) := by rw [hcxy]
      have hR : (s x * u₀) * (s y * u₀) = (s x * s y) * (u₀ * u₀) := by ac_rfl
      rw [hR, hu₀sq, mul_one, hsplit, mul_comm u₀ (s (x * y))]
  let s'hom : V →* W := MonoidHom.mk' s' hs'mul
  have hs'hom : ∀ v : V, s'hom v = s' v := fun _ => rfl
  refine ⟨s'hom.range, ?_, ?_, ?_⟩
  · intro n m hm
    rw [MonoidHom.mem_range] at hm
    obtain ⟨v, rfl⟩ := hm
    rw [MonoidHom.mem_range]
    exact ⟨vact n v, by rw [hs'hom]; exact (hkey n v).symm⟩
  · refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxM, hxker⟩ := hx
    rw [MonoidHom.mem_range] at hxM
    obtain ⟨v, hv⟩ := hxM
    rw [Subgroup.mem_bot]
    have hxker' : π x = 1 := MonoidHom.mem_ker.mp hxker
    rw [← hv] at hxker' ⊢
    rw [hs'hom v] at hxker'
    rw [hπs' v] at hxker'
    rw [hs'hom v, hxker']
    exact hs'1
  · rw [eq_top_iff]
    intro w _
    rw [Subgroup.mem_sup]
    refine ⟨s' (π w), MonoidHom.mem_range.mpr ⟨π w, hs'hom (π w)⟩,
      w * (s' (π w))⁻¹, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hπs' (π w), mul_inv_cancel]
    · rw [← mul_assoc, mul_comm (s' (π w)) w, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.OddStandard.HigherRank.YamadaG23
