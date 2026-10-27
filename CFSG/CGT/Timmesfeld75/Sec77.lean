module

public import CFSG.CGT.Timmesfeld75.Sec77Q
public import CFSG.CGT.Timmesfeld75.Sec77Stmt
public import CFSG.CGT.Timmesfeld75.Sec76

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem orderOf_eq_four_of_sq {a : G} (h1 : a ^ 2 ≠ 1) (h2 : a ^ 2 * a ^ 2 = 1) :
    orderOf a = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : a ^ 2 ^ (1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 by norm_num, pow_add]
    exact h2
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h1) h4
  simpa using this

theorem Sec6Ctx.mem_T_of_sq_mem (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) (hn3 : 3 ≤ n)
    (hA8 : ¬ (n = 4 ∧ m = 1)) {a b : G} (ha : a ∈ classD T) (hb : b ∈ classD T)
    (hord : orderOf (a * b) = 4) (hsq : (a * b) ^ 2 ∈ T) : a ∈ T ∨ b ∈ T := by
  have hTwc := hc.hy.pair.wc
  have hTab := hTwc.1
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_classD hTab ha)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_classD hTab hb)
  have hk1 : (a * b) ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num)
  rcases sec74_of h66 h1 h62 h63 G T T₁ n m hc hnat hn3 hA8 a ha b hb hord with
    ⟨h, hah, hba⟩ | ⟨g, hbg, hab⟩
  · left
    have hkh : (a * b) ^ 2 ∈ conjSubgroup h T := by
      have e1 : (a * b) ^ 2 = a * (b⁻¹ * a * b) := by rw [pow_two, hbi]; group
      rw [e1]
      exact (conjSubgroup h T).mul_mem hah hba
    have hinf : T ⊓ conjSubgroup h T ≠ ⊥ := fun h0 => hk1 (by
      have : (a * b) ^ 2 ∈ T ⊓ conjSubgroup h T := ⟨hsq, hkh⟩
      rw [h0, Subgroup.mem_bot] at this
      exact this)
    have := hTwc.conj_eq_of_inf_ne_bot hinf
    exact this ▸ hah
  · right
    have hkg : (a * b) ^ 2 ∈ conjSubgroup g T := by
      have e1 : (a * b) ^ 2 = (a⁻¹ * b * a) * b := by rw [pow_two, hai]; group
      rw [e1]
      exact (conjSubgroup g T).mul_mem hab hbg
    have hinf : T ⊓ conjSubgroup g T ≠ ⊥ := fun h0 => hk1 (by
      have : (a * b) ^ 2 ∈ T ⊓ conjSubgroup g T := ⟨hsq, hkg⟩
      rw [h0, Subgroup.mem_bot] at this
      exact this)
    have := hTwc.conj_eq_of_inf_ne_bot hinf
    exact this ▸ hbg

theorem TModel.toAdd_phi_comm' [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (M : TModel T T₁ n m) {d : G} (hd : d ∈ normD T) {t : G} (ht : t ∈ T) (hct : ⁅d, t⁆ ∈ T) :
    Multiplicative.toAdd (M.φ ⟨⁅d, t⁆, hct⟩) =
      sact (ubar M.ε d) (Multiplicative.toAdd (M.φ ⟨t, ht⟩)) -
        Multiplicative.toAdd (M.φ ⟨t, ht⟩) := by
  have hdH := M.mem_H hd
  have h := toAdd_phi_comm M.compat hdH hd.2 ht hct
  rw [h, ubar_of_mem M.ε hdH]
  rfl

theorem Sec6Ctx.sec77_core (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) (hn3 : 3 ≤ n)
    (hA8 : ¬ (n = 4 ∧ m = 1)) {x z y : G} (hx : x ∈ classD T) (hz : z ∈ classD T)
    (hy : y ∈ classD T) (hxz : x * z = z * x) (hxzD : x * z ∉ classD T) (hxz1 : x * z ≠ 1)
    (hyv : y * (x * z) = (x * z) * y) (hord : orderOf (x * y) = 4) (hcT : (x * y) ^ 2 ∈ T) :
    False := by
  obtain ⟨hN, ε, φ, hcompat, htr⟩ := hc.sec67_transv h1 h63 hA8 hnat
  have := hN
  let M : TModel T T₁ n m := ⟨ε, φ, hcompat, htr⟩
  have := hc.finite
  have hTwc := hc.hy.pair.wc
  have hTab := hTwc.1
  have hx2 : x * x = 1 := mul_self_eq_one_of_mem_classD hTab hx
  have hz2 : z * z = 1 := mul_self_eq_one_of_mem_classD hTab hz
  have hy2 : y * y = 1 := mul_self_eq_one_of_mem_classD hTab hy
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  obtain ⟨hcdef, hc1', hcc', -, hcx', hxc', hyc'⟩ :=
    ay_facts (b := y * x * y) (c := x * (y * x * y)) hx2 hy2 hord rfl rfl
  obtain ⟨c, hcdef_c⟩ : ∃ c : G, c = (x * y) ^ 2 := ⟨_, rfl⟩
  have hcc : x * (y * x * y) = c := hcdef.trans hcdef_c.symm
  have hc1 : c ≠ 1 := by rw [← hcc]; exact hc1'
  have hcc2 : c * c = 1 := by rw [← hcc]; exact hcc'
  have hxc : x * c = c * x := by rw [← hcc]; exact hxc'.trans hcx'.symm
  have hyc : y * c = c * y := by rw [← hcc]; exact hyc'
  have hcT' : c ∈ T := by rw [hcdef_c]; exact hcT
  have hv2 : (x * z) * (x * z) = 1 := by
    calc (x * z) * (x * z) = x * (z * x) * z := by group
      _ = x * (x * z) * z := by rw [hxz]
      _ = (x * x) * (z * z) := by group
      _ = 1 := by rw [hx2, hz2, one_mul]
  have hvx : (x * z) * x = x * (x * z) := by
    calc (x * z) * x = x * (z * x) := by group
      _ = x * (x * z) := by rw [hxz]
  have hzv : z = x * (x * z) := by rw [← mul_assoc, hx2, one_mul]
  have key : (x * z) * (x * (x * z)) = x := by
    calc (x * z) * (x * (x * z)) = ((x * z) * x) * (x * z) := by group
      _ = (x * (x * z)) * (x * z) := by rw [hvx]
      _ = x * ((x * z) * (x * z)) := by group
      _ = x := by rw [hv2, mul_one]
  have hzy : (z * y) ^ 2 = c := by
    rw [hcdef_c, pow_two, pow_two]
    calc z * y * (z * y) = (x * (x * z)) * y * (x * (x * z)) * y := by rw [← hzv]; group
      _ = x * ((x * z) * y) * (x * (x * z)) * y := by group
      _ = x * (y * (x * z)) * (x * (x * z)) * y := by rw [← hyv]
      _ = x * y * ((x * z) * (x * (x * z))) * y := by group
      _ = x * y * x * y := by rw [key]
      _ = x * y * (x * y) := by group
  have hordz : orderOf (z * y) = 4 :=
    orderOf_eq_four_of_sq (by rw [hzy]; exact hc1) (by rw [hzy]; exact hcc2)
  obtain ⟨hcdefz, -, -, -, hczz, hzcz, -⟩ :=
    ay_facts (b := y * z * y) (c := z * (y * z * y)) hz2 hy2 hordz rfl rfl
  have hc'' : z * (y * z * y) = c := hcdefz.trans hzy
  have hzc : z * c = c * z := by rw [← hc'']; exact hzcz.trans hczz.symm
  have hxN : x ∈ Subgroup.normalizer (T : Set G) :=
    hTwc.centralizer_le_normalizer hcT' hc1 (Subgroup.mem_centralizer_singleton_iff.2 hxc)
  have hzN : z ∈ Subgroup.normalizer (T : Set G) :=
    hTwc.centralizer_le_normalizer hcT' hc1 (Subgroup.mem_centralizer_singleton_iff.2 hzc)
  have hxD : x ∈ normD T := ⟨hx, hxN⟩
  have hzD : z ∈ normD T := ⟨hz, hzN⟩
  have hyT : y ∈ T := by
    by_contra hyT
    have hxT := (hc.mem_T_of_sq_mem h66 h1 h62 h63 hnat hn3 hA8 hx hy hord hcT).resolve_right hyT
    have hzT := (hc.mem_T_of_sq_mem h66 h1 h62 h63 hnat hn3 hA8 hz hy hordz
      (by rw [hzy]; exact hcT')).resolve_right hyT
    exact hxzD (mem_classD_of_mem (T.mul_mem hxT hzT) hxz1)
  have hxT : x ∉ T := by
    intro hxT
    apply hc1
    have h3 : x * y = y * x := elemAbelian_mul_comm hTab hxT hyT
    rw [hcdef_c, pow_two]
    calc x * y * (x * y) = x * y * (y * x) := by rw [← h3]
      _ = x * (y * y) * x := by group
      _ = 1 := by rw [hy2, mul_one, hx2]
  have hzT : z ∉ T := by
    intro hzT
    apply hc1
    have h3 : z * y = y * z := elemAbelian_mul_comm hTab hzT hyT
    rw [← hzy, pow_two]
    calc z * y * (z * y) = z * y * (y * z) := by rw [← h3]
      _ = z * (y * y) * z := by group
      _ = 1 := by rw [hy2, mul_one, hz2]
  obtain ⟨fx, vx, hfvx, hvx, hfx0, hdx⟩ := M.exists_data hxD hxT
  obtain ⟨fz, vz, hfvz, hvz, hfz0, hdz⟩ := M.exists_data hzD hzT
  set wy := Multiplicative.toAdd (M.φ ⟨y, hyT⟩) with hwy
  have hct_x : ⁅x, y⁆ ∈ T := comm_mem_of_mem_normalizer hxN hyT
  have hct_z : ⁅z, y⁆ ∈ T := comm_mem_of_mem_normalizer hzN hyT
  have hxy : ⁅x, y⁆ = c := by
    rw [commutatorElement_def, hxi, hyi, hcdef_c, pow_two]
    group
  have hzy' : ⁅z, y⁆ = c := by
    rw [commutatorElement_def, hzi, hyi, ← hzy, pow_two]
    group
  have hφx : Multiplicative.toAdd (M.φ ⟨c, hcT'⟩) = fx wy • vx := by
    have h := M.toAdd_phi_comm' hxD hyT hct_x
    have e : (⟨⁅x, y⁆, hct_x⟩ : ↥T) = ⟨c, hcT'⟩ := Subtype.ext hxy
    rw [e, ← hwy, hdx wy] at h
    rw [h]
    abel
  have hφz : Multiplicative.toAdd (M.φ ⟨c, hcT'⟩) = fz wy • vz := by
    have h := M.toAdd_phi_comm' hzD hyT hct_z
    have e : (⟨⁅z, y⁆, hct_z⟩ : ↥T) = ⟨c, hcT'⟩ := Subtype.ext hzy'
    rw [e, ← hwy, hdz wy] at h
    rw [h]
    abel
  have hφ0 : Multiplicative.toAdd (M.φ ⟨c, hcT'⟩) ≠ 0 := by
    intro h0
    have h1' : M.φ ⟨c, hcT'⟩ = 1 := by
      have : M.φ ⟨c, hcT'⟩ = Multiplicative.ofAdd 0 := by
        rw [← h0]
        rfl
      simpa using this
    have h2' : (⟨c, hcT'⟩ : ↥T) = 1 := M.φ.injective (h1'.trans M.φ.map_one.symm)
    exact hc1 (congrArg Subtype.val h2')
  have hfxy : fx wy ≠ 0 := by
    intro h0
    apply hφ0
    rw [hφx, h0, zero_smul]
  have hfzy : fz wy ≠ 0 := by
    intro h0
    apply hφ0
    rw [hφz, h0, zero_smul]
  set μ : GaloisField 2 m := (fz wy)⁻¹ * fx wy with hμ
  have hμ0 : μ ≠ 0 := mul_ne_zero (inv_ne_zero hfzy) hfxy
  have hvzμ : vz = μ • vx := by
    have h3 : fz wy • vz = fx wy • vx := hφz.symm.trans hφx
    calc vz = (fz wy)⁻¹ • (fz wy • vz) := by rw [smul_smul, inv_mul_cancel₀ hfzy, one_smul]
      _ = (fz wy)⁻¹ • (fx wy • vx) := by rw [h3]
      _ = μ • vx := by rw [smul_smul]
  have hfzvx : fz vx = 0 := by
    have h4 : fz vz = 0 := hfvz
    rw [hvzμ, map_smul, smul_eq_mul] at h4
    exact (mul_eq_zero.1 h4).resolve_left hμ0
  have hdz' : ∀ w, sact (ubar M.ε z) w = w + (μ • fz) w • vx := by
    intro w
    rw [hdz w, hvzμ, smul_smul]
    simp only [LinearMap.smul_apply, smul_eq_mul, mul_comm]
  have hfz'vx : (μ • fz) vx = 0 := by
    simp only [LinearMap.smul_apply, smul_eq_mul, hfzvx, mul_zero]
  have hfz'0 : μ • fz ≠ 0 := smul_ne_zero hμ0 hfz0
  rcases hc.mul_mem_of_same_center h66 h1 h62 h63 hnat hn3 hA8 M hxD hxT hzD hzT hxz hvx hfvx
    hfz'vx hfx0 hfz'0 hdx hdz' with hT' | hD'
  · exact hxzD (mem_classD_of_mem hT' hxz1)
  · exact hxzD hD'

theorem sec77_of (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) : Sec77 := by
  intro G _ T T₁ n m hc hnat hn3 hA8 x hx z hz hxz hxz1 hxzD y hy hyv hord
  have hcD : (x * y) ^ 2 ∈ classD T := h66 G T T₁ n m hc x hx y hy hord
  obtain ⟨g, t₀, ht₀, ht₀1, hct⟩ := hcD
  have hconj : ∀ a b : G, g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := fun a b => by group
  refine hc.sec77_core h66 h1 h62 h63 hnat hn3 hA8 (x := g * x * g⁻¹) (z := g * z * g⁻¹)
    (y := g * y * g⁻¹) (classD_conj_mul hx g) (classD_conj_mul hz g) (classD_conj_mul hy g)
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hconj, hconj, hxz]
  · intro h
    rw [hconj] at h
    have := classD_conj h g
    have e : g⁻¹ * (g * (x * z) * g⁻¹) * g = x * z := by group
    rw [e] at this
    exact hxzD this
  · intro h
    rw [hconj] at h
    apply hxz1
    have e : x * z = g⁻¹ * (g * (x * z) * g⁻¹) * g := by group
    rw [e, h]
    group
  · rw [hconj, hconj, hconj, hyv]
  · have e : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    rw [e]
    have := MulEquiv.orderOf_eq (MulAut.conj g) (x * y)
    simpa [MulAut.conj_apply, hord] using this
  · have e : (g * x * g⁻¹ * (g * y * g⁻¹)) ^ 2 = g * (x * y) ^ 2 * g⁻¹ := by
      rw [← conj_pow]
      group
    rw [e, hct]
    have e2 : g * (g⁻¹ * t₀ * g) * g⁻¹ = t₀ := by group
    rw [e2]
    exact ht₀

end CFSG.CGT.Timmesfeld75
