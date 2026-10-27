module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56ASEa

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

private lemma exists_generic_pair {V : Type*} [Group V] [Finite V]
    (hsq : ∀ v : V, v * v = 1) (hcard : Nat.card V = 8) {z : V} (hz1 : z ≠ 1) :
    ∃ a b : V, a ≠ 1 ∧ a ≠ z ∧ b ≠ 1 ∧ b ≠ z ∧ a ≠ b ∧ a ≠ z * b := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hcardV : Fintype.card V = 8 := by rw [Fintype.card_eq_nat_card, hcard]
  have h2 : ({1, z} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hz1.symm]), Finset.card_singleton]
  have h2lt : ({1, z} : Finset V).card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ, hcardV, h2]
    norm_num
  obtain ⟨a, _, ha_notin⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := ({1, z} : Finset V))
      (t := Finset.univ) h2lt
  have ha1 : a ≠ 1 := by intro h; exact ha_notin (by simp [h])
  have haz : a ≠ z := by intro h; exact ha_notin (by simp [h])
  have hza1 : z * a ≠ 1 := by
    intro h
    exact haz ((mul_eq_one_iff_eq_inv.mp h).trans
      (inv_eq_of_mul_eq_one_right (hsq a))).symm
  have hzaz : z * a ≠ z := by
    intro h
    exact ha1 (mul_left_cancel (by rw [h, mul_one]))
  have hzaa : z * a ≠ a := by
    intro h
    exact hz1 (mul_right_cancel (by rw [h, one_mul]))
  have hTcard : ({1, z, a, z * a} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hz1.symm, ha1.symm, hza1.symm]),
      Finset.card_insert_of_notMem (by simp [haz.symm, hzaz.symm]),
      Finset.card_insert_of_notMem (by simp [hzaa.symm]),
      Finset.card_singleton]
  have hTlt : ({1, z, a, z * a} : Finset V).card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ, hcardV, hTcard]
    norm_num
  obtain ⟨b, _, hb_notin⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := ({1, z, a, z * a} : Finset V))
      (t := Finset.univ) hTlt
  have hb1 : b ≠ 1 := by intro h; exact hb_notin (by simp [h])
  have hbz : b ≠ z := by intro h; exact hb_notin (by simp [h])
  have hba : b ≠ a := by intro h; exact hb_notin (by simp [h])
  have hbza : b ≠ z * a := by intro h; exact hb_notin (by simp [h])
  have hazb : a ≠ z * b := by
    intro h
    apply hbza
    calc b = z * (z * b) := by rw [← mul_assoc, hsq z, one_mul]
      _ = z * a := by rw [← h]
  exact ⟨a, b, ha1, haz, hb1, hbz, hba.symm, hazb⟩

variable {W V N : Type} [Group W] [Finite W] [Group V] [Finite V] [Group N] [Finite N]

theorem ase_complement (act : N →* MulAut W) (vact : N →* MulAut V) (π : W →* V)
    (hπ : Function.Surjective π) (hπact : ∀ (n : N) (w : W), π (act n w) = vact n (π w))
    (hW : ∀ w : W, w ^ 2 = 1) (hV8 : Nat.card V = 8)
    (hU : ∀ n : N, ∀ u ∈ π.ker, act n u = u)
    {z : V} (hz1 : z ≠ 1) (hzfix : ∀ n : N, vact n z = z)
    (htrans : ∀ a b : V, a ≠ 1 → a ≠ z → b ≠ 1 → b ≠ z → ∃ n : N, vact n a = b)
    (hpairs : ∀ a b a' b' : V, a ≠ 1 → a ≠ z → b ≠ 1 → b ≠ z → a ≠ b → a ≠ z * b →
      a' ≠ 1 → a' ≠ z → b' ≠ 1 → b' ≠ z → a' ≠ b' → a' ≠ z * b' →
      ∃ n : N, vact n a = a' ∧ vact n b = b')
    {wz : W} (hwz : π wz = z) (hwzfix : ∀ n : N, act n wz = wz)
    {v₀ : V} (hv₀1 : v₀ ≠ 1) (hv₀z : v₀ ≠ z) {w₀ : W} (hw₀ : π w₀ = v₀)
    (hw₀fix : ∀ n : N, vact n v₀ = v₀ → act n w₀ = w₀)
    {a : N} (hav₀ : vact a v₀ = z * v₀) (haw₀ : act a w₀ = w₀ * wz) :
    ∃ M : Subgroup W, (∀ (n : N), ∀ m ∈ M, act n m ∈ M) ∧ M ⊓ π.ker = ⊥ ∧
      M ⊔ π.ker = ⊤ ∧ wz ∈ M := by
  classical
  have hW2 : ∀ w : W, w * w = 1 := fun w => by simpa [pow_two] using hW w
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
  have hsqV : ∀ v : V, v * v = 1 := fun v => by simpa [pow_two] using hV2 v
  have hVcomm : ∀ a b : V, a * b = b * a := by
    intro a b
    have h : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hsqV (a * b))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsqV a),
      inv_eq_of_mul_eq_one_right (hsqV b)] at h
    exact h.symm
  letI : CommGroup V := { ‹Group V› with mul_comm := hVcomm }
  obtain ⟨a₁, b₁, ha₁1, ha₁z, hb₁1, hb₁z, ha₁b₁, ha₁zb₁⟩ :=
    exists_generic_pair hsqV hV8 hz1
  obtain ⟨s0, hs01, hs0z, hs0π, hs0v₀, hs0eq, _⟩ :=
    ase_section act vact π hπ hπact hW hU hz1 hzfix htrans hwz hwzfix hv₀1 hv₀z
      hw₀ hw₀fix hav₀ haw₀ (u₀ := 1) (by simp)
  let D : W := s0 a₁ * s0 b₁ * s0 (a₁ * b₁)
  have hDker : D ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    show π (s0 a₁ * s0 b₁ * s0 (a₁ * b₁)) = 1
    rw [map_mul, map_mul, hs0π a₁, hs0π b₁, hs0π (a₁ * b₁)]
    exact hsqV (a₁ * b₁)
  have hDfix : ∀ n : N, act n D = D := fun n => hU n D hDker
  obtain ⟨s, hs1, hsz, hsπ, hsv₀, hseq, hszmul⟩ :=
    ase_section act vact π hπ hπact hW hU hz1 hzfix htrans hwz hwzfix hv₀1 hv₀z
      hw₀ hw₀fix hav₀ haw₀ (u₀ := D) hDker
  have hs_eq : ∀ v : V, v ≠ 1 → v ≠ z → s v = s0 v * D := by
    intro v hv1 hvz
    obtain ⟨n, hn⟩ := htrans v₀ v hv₀1 hv₀z hv1 hvz
    have hsv : s v = act n (s v₀) := by rw [← hn, hseq n v₀ hv₀1]
    have hs0v : s0 v = act n (s0 v₀) := by rw [← hn, hs0eq n v₀ hv₀1]
    rw [hsv, hs0v, hsv₀, hs0v₀, map_mul (act n) w₀ D, hDfix n,
      map_mul (act n) w₀ 1, map_one, mul_one]
  have hab₁_ne : a₁ * b₁ ≠ 1 := by
    intro h
    exact ha₁b₁ ((mul_eq_one_iff_eq_inv.mp h).trans
      (inv_eq_of_mul_eq_one_right (hsqV b₁)))
  have hab₁z : a₁ * b₁ ≠ z := by
    intro h
    apply ha₁zb₁
    calc a₁ = a₁ * b₁ * b₁ := by rw [mul_assoc, hsqV b₁, mul_one]
      _ = z * b₁ := by rw [h]
  have hD2 : D * D = 1 := hW2 D
  have hL : s0 (a₁ * b₁) * D = s0 a₁ * s0 b₁ := by
    have hDdef : D = s0 a₁ * s0 b₁ * s0 (a₁ * b₁) := rfl
    rw [hDdef]
    calc s0 (a₁ * b₁) * (s0 a₁ * s0 b₁ * s0 (a₁ * b₁))
        = (s0 a₁ * s0 b₁) * (s0 (a₁ * b₁) * s0 (a₁ * b₁)) := by ac_rfl
      _ = s0 a₁ * s0 b₁ := by rw [hW2 (s0 (a₁ * b₁)), mul_one]
  have hR : (s0 a₁ * D) * (s0 b₁ * D) = s0 a₁ * s0 b₁ := by
    rw [mul_mul_mul_comm (s0 a₁) D (s0 b₁) D, hD2, mul_one]
  have hs_base_mul : s (a₁ * b₁) = s a₁ * s b₁ := by
    rw [hs_eq a₁ ha₁1 ha₁z, hs_eq b₁ hb₁1 hb₁z, hs_eq (a₁ * b₁) hab₁_ne hab₁z]
    exact hL.trans hR.symm
  have hs_mul : ∀ x y : V, s (x * y) = s x * s y := by
    intro x y
    by_cases hx1 : x = 1
    · rw [hx1, one_mul, hs1, one_mul]
    by_cases hy1 : y = 1
    · rw [hy1, mul_one, hs1, mul_one]
    by_cases hxy : x = y
    · rw [hxy, hsqV y, hs1, hW2 (s y)]
    by_cases hxz : x = z
    · have hyz : y ≠ z := by rintro rfl; exact hxy hxz
      rw [hxz, hszmul y hy1 hyz, hsz, mul_comm (s y) wz]
    by_cases hyz : y = z
    · rw [hyz, mul_comm x z, hszmul x hx1 hxz, hsz]
    · by_cases hyzx : y = z * x
      · have hxyz : x * y = z := by
          rw [hyzx]
          calc x * (z * x) = z * (x * x) := by ac_rfl
            _ = z := by rw [hsqV x, mul_one]
        have hsy : s y = s x * wz := by rw [hyzx, hszmul x hx1 hxz]
        rw [hxyz, hsz, hsy, ← mul_assoc, hW2 (s x), one_mul]
      · have hxzy : x ≠ z * y := by
          intro h
          apply hyzx
          calc y = z * (z * y) := by rw [← mul_assoc, hsqV z, one_mul]
            _ = z * x := by rw [← h]
        obtain ⟨n, hn1, hn2⟩ :=
          hpairs a₁ b₁ x y ha₁1 ha₁z hb₁1 hb₁z ha₁b₁ ha₁zb₁ hx1 hxz hy1 hyz hxy hxzy
        have hprod : vact n (a₁ * b₁) = x * y := by rw [map_mul, hn1, hn2]
        calc s (x * y)
            = s (vact n (a₁ * b₁)) := by rw [hprod]
          _ = act n (s (a₁ * b₁)) := hseq n (a₁ * b₁) hab₁_ne
          _ = act n (s a₁ * s b₁) := by rw [hs_base_mul]
          _ = act n (s a₁) * act n (s b₁) := by rw [map_mul]
          _ = s (vact n a₁) * s (vact n b₁) := by
                rw [← hseq n a₁ ha₁1, ← hseq n b₁ hb₁1]
          _ = s x * s y := by rw [hn1, hn2]
  let shom : V →* W := MonoidHom.mk' s hs_mul
  refine ⟨shom.range, ?_, ?_, ?_, ?_⟩
  · intro n m hm
    rw [MonoidHom.mem_range] at hm
    obtain ⟨v, rfl⟩ := hm
    rw [MonoidHom.mem_range]
    by_cases hv : v = 1
    · refine ⟨1, ?_⟩
      rw [hv]
      change s 1 = act n (s 1)
      rw [hs1, map_one]
    · refine ⟨vact n v, ?_⟩
      change s (vact n v) = act n (s v)
      exact hseq n v hv
  · refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxM, hxker⟩ := hx
    rw [Subgroup.mem_bot]
    rw [MonoidHom.mem_range] at hxM
    obtain ⟨v, hv⟩ := hxM
    have hxv : x = s v := by rw [← hv]; rfl
    have hπx : π x = 1 := MonoidHom.mem_ker.mp hxker
    rw [hxv, hsπ v] at hπx
    rw [hxv, hπx, hs1]
  · rw [eq_top_iff]
    intro w _
    rw [Subgroup.mem_sup]
    refine ⟨shom (π w), MonoidHom.mem_range.mpr ⟨π w, rfl⟩,
      w * (shom (π w))⁻¹, ?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      change π (w * (s (π w))⁻¹) = 1
      rw [map_mul, map_inv, hsπ (π w), mul_inv_cancel]
    · change s (π w) * (w * (s (π w))⁻¹) = w
      rw [← mul_assoc, mul_comm (s (π w)) w, mul_assoc, mul_inv_cancel, mul_one]
  · exact MonoidHom.mem_range.mpr ⟨z, by change s z = wz; rw [hsz]⟩

end CFSG.OddStandard.HigherRank.YamadaG23
