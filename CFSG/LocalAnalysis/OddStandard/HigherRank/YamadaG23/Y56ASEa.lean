module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

variable {W V N : Type} [Group W] [Finite W] [Group V] [Finite V] [Group N] [Finite N]

theorem ase_section (act : N →* MulAut W) (vact : N →* MulAut V) (π : W →* V)
    (hπ : Function.Surjective π) (hπact : ∀ (n : N) (w : W), π (act n w) = vact n (π w))
    (hW : ∀ w : W, w ^ 2 = 1) (hU : ∀ n : N, ∀ u ∈ π.ker, act n u = u)
    {z : V} (hz1 : z ≠ 1) (hzfix : ∀ n : N, vact n z = z)
    (htrans : ∀ a b : V, a ≠ 1 → a ≠ z → b ≠ 1 → b ≠ z → ∃ n : N, vact n a = b)
    {wz : W} (hwz : π wz = z) (hwzfix : ∀ n : N, act n wz = wz)
    {v₀ : V} (hv₀1 : v₀ ≠ 1) (hv₀z : v₀ ≠ z) {w₀ : W} (hw₀ : π w₀ = v₀)
    (hw₀fix : ∀ n : N, vact n v₀ = v₀ → act n w₀ = w₀)
    {a : N} (hav₀ : vact a v₀ = z * v₀) (haw₀ : act a w₀ = w₀ * wz)
    {u₀ : W} (hu₀ : u₀ ∈ π.ker) :
    ∃ s : V → W, s 1 = 1 ∧ s z = wz ∧ (∀ v, π (s v) = v) ∧ s v₀ = w₀ * u₀ ∧
      (∀ (n : N) (v : V), v ≠ 1 → s (vact n v) = act n (s v)) ∧
      (∀ v : V, v ≠ 1 → v ≠ z → s (z * v) = s v * wz) := by
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
  have hz2 : z * z = 1 := by rw [← pow_two]; exact hV2 z
  have hsurj : ∀ v : V, v ≠ 1 → v ≠ z → ∃ n : N, vact n v₀ = v :=
    fun v hv1 hvz => htrans v₀ v hv₀1 hv₀z hv1 hvz
  have hwell : ∀ n m : N, vact n v₀ = vact m v₀ →
      act n (w₀ * u₀) = act m (w₀ * u₀) := by
    intro n m h
    have hfixv : vact (m⁻¹ * n) v₀ = v₀ := by
      rw [map_mul vact m⁻¹ n]
      change vact m⁻¹ (vact n v₀) = v₀
      rw [h, ← MulAut.mul_apply, ← map_mul vact m⁻¹ m, inv_mul_cancel, map_one]
      rfl
    have hfixw : act (m⁻¹ * n) w₀ = w₀ := hw₀fix (m⁻¹ * n) hfixv
    have hfixu : act (m⁻¹ * n) u₀ = u₀ := hU (m⁻¹ * n) u₀ hu₀
    calc act n (w₀ * u₀)
        = act (m * (m⁻¹ * n)) (w₀ * u₀) := by rw [mul_inv_cancel_left]
      _ = act m (act (m⁻¹ * n) (w₀ * u₀)) := by
            rw [map_mul act m (m⁻¹ * n), MulAut.mul_apply]
      _ = act m (w₀ * u₀) := by rw [map_mul, hfixw, hfixu]
  let s : V → W := fun v =>
    if hv1 : v = 1 then 1
    else if hvz : v = z then wz
    else act (Classical.choose (hsurj v hv1 hvz)) (w₀ * u₀)
  have hs1 : s 1 = 1 := by dsimp only [s]; simp
  have hsz : s z = wz := by dsimp only [s]; rw [dif_neg hz1, dif_pos rfl]
  have hs_eq : ∀ (v : V) (hv1 : v ≠ 1) (hvz : v ≠ z) (n : N),
      vact n v₀ = v → s v = act n (w₀ * u₀) := by
    intro v hv1 hvz n hn
    have hch := Classical.choose_spec (hsurj v hv1 hvz)
    have hs : s v = act (Classical.choose (hsurj v hv1 hvz)) (w₀ * u₀) := by
      dsimp only [s]; rw [dif_neg hv1, dif_neg hvz]
    rw [hs]
    exact hwell (Classical.choose (hsurj v hv1 hvz)) n (by rw [hch, hn])
  have hπs : ∀ v : V, π (s v) = v := by
    intro v
    by_cases hv1 : v = 1
    · subst v; rw [hs1, map_one]
    · by_cases hvz : v = z
      · subst v; rw [hsz, hwz]
      · have hch := Classical.choose_spec (hsurj v hv1 hvz)
        have hs : s v = act (Classical.choose (hsurj v hv1 hvz)) (w₀ * u₀) := by
          dsimp only [s]; rw [dif_neg hv1, dif_neg hvz]
        rw [hs, hπact]
        have hker : π (w₀ * u₀) = v₀ := by
          rw [map_mul, hw₀, MonoidHom.mem_ker.mp hu₀, mul_one]
        rw [hker, hch]
  have hsv₀ : s v₀ = w₀ * u₀ := by
    have h := hs_eq v₀ hv₀1 hv₀z 1 (by rw [map_one]; rfl)
    simpa using h
  have hseq : ∀ (n : N) (v : V), v ≠ 1 → s (vact n v) = act n (s v) := by
    intro n v hv1
    by_cases hvz : v = z
    · subst v
      rw [hzfix n, hsz, hwzfix n]
    · obtain ⟨m, hm⟩ := hsurj v hv1 hvz
      have hsv : s v = act m (w₀ * u₀) := hs_eq v hv1 hvz m hm
      have hnv1 : vact n v ≠ 1 := by
        intro h
        apply hv1
        have h1 : vact n⁻¹ (vact n v) = v := by
          rw [← MulAut.mul_apply, ← map_mul vact n⁻¹ n, inv_mul_cancel, map_one]
          rfl
        rw [h, map_one] at h1
        exact h1.symm
      have hnvz : vact n v ≠ z := by
        intro h
        apply hvz
        have h1 : vact n⁻¹ (vact n v) = v := by
          rw [← MulAut.mul_apply, ← map_mul vact n⁻¹ n, inv_mul_cancel, map_one]
          rfl
        rw [h, hzfix n⁻¹] at h1
        exact h1.symm
      have hkey : vact (n * m) v₀ = vact n v := by
        rw [map_mul]
        change vact n (vact m v₀) = vact n v
        rw [hm]
      rw [hs_eq (vact n v) hnv1 hnvz (n * m) hkey, hsv, map_mul act n m, MulAut.mul_apply]
  have hszv : ∀ v : V, v ≠ 1 → v ≠ z → s (z * v) = s v * wz := by
    intro v hv1 hvz
    obtain ⟨m, hm⟩ := hsurj v hv1 hvz
    have hsv : s v = act m (w₀ * u₀) := hs_eq v hv1 hvz m hm
    have hzv1 : z * v ≠ 1 := by
      intro h
      apply hvz
      have h2 : z * (z * v) = z * 1 := congrArg (fun x => z * x) h
      calc v = 1 * v := (one_mul v).symm
        _ = (z * z) * v := by rw [hz2]
        _ = z * (z * v) := by rw [mul_assoc]
        _ = z * 1 := h2
        _ = z := mul_one z
    have hzvz : z * v ≠ z := by
      intro h
      apply hv1
      have h2 : z * (z * v) = z * z := congrArg (fun x => z * x) h
      calc v = 1 * v := (one_mul v).symm
        _ = (z * z) * v := by rw [hz2]
        _ = z * (z * v) := by rw [mul_assoc]
        _ = z * z := h2
        _ = 1 := hz2
    have hkey : vact (m * a) v₀ = z * v := by
      rw [map_mul]
      change vact m (vact a v₀) = z * v
      rw [hav₀, map_mul, hzfix m, hm]
    rw [hs_eq (z * v) hzv1 hzvz (m * a) hkey, hsv]
    rw [map_mul act m a, MulAut.mul_apply]
    have hact : act a (w₀ * u₀) = (w₀ * wz) * u₀ := by
      rw [map_mul, haw₀, hU a u₀ hu₀]
    rw [hact, map_mul (act m) (w₀ * wz) u₀, map_mul (act m) w₀ wz,
      map_mul (act m) w₀ u₀, hwzfix m]
    ac_rfl
  exact ⟨s, hs1, hsz, hπs, hsv₀, hseq, hszv⟩

end CFSG.OddStandard.HigherRank.YamadaG23
