module

public import CFSG.CGT.T75F.E710Loc4
public import CFSG.CGT.Timmesfeld75.Sec77Stmt
public import CFSG.CGT.Timmesfeld75.Sec78Dihedral

public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {m : ℕ}

theorem comm_of_sec77 (h77 : Sec77) (hc : Sec6Ctx T T₁ 3 m)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) 3 m) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    {x₀ z₀ d : G} (hx₀ : x₀ ∈ A) (hx₀D : x₀ ∈ classD T) (hz₀D : z₀ ∈ classD T)
    (hxz : x₀ * z₀ = z₀ * x₀) (hxz1 : x₀ * z₀ ≠ 1) (hxzD : x₀ * z₀ ∉ classD T)
    (hdD : d ∈ classD T) (hdN : d ∈ Subgroup.normalizer (A : Set G))
    (hdc : d * (x₀ * z₀) = (x₀ * z₀) * d) : d * x₀ = x₀ * d ∧ d * z₀ = z₀ * d := by
  have hTab := hc.hy.pair.wc.1
  have hd2 : d * d = 1 := mul_self_eq_one_of_mem_classD hTab hdD
  have hx2 : x₀ * x₀ = 1 := elemAbelian_mul_self hA hx₀
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hsq : (x₀ * d) ^ 2 ∈ A := by
    have h1 := conj_mem_of_mem_normalizer hdN hx₀
    rw [hdi] at h1
    have : (x₀ * d) ^ 2 = x₀ * (d * x₀ * d) := by rw [pow_two]; group
    rw [this]
    exact A.mul_mem hx₀ h1
  have h4 : (x₀ * d) ^ (2 * 2) = 1 := by
    have := elemAbelian_mul_self hA hsq
    rw [← pow_add] at this
    exact this
  have hord4 : orderOf (x₀ * d) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one h4
  have hne4 : orderOf (x₀ * d) ≠ 4 :=
    h77 G T T₁ 3 m hc hnat (by norm_num) (by omega) x₀ hx₀D z₀ hz₀D hxz hxz1 hxzD d hdD hdc
  have hord2 : orderOf (x₀ * d) ∣ 2 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord4
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have : k = 2 := by omega
      subst this
      exact hne4 (by simpa using hk')
    rw [hk']
    simpa using pow_dvd_pow 2 hk1
  have h2sq : (x₀ * d) * (x₀ * d) = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 hord2
  have hdx : d * x₀ = x₀ * d := by
    have h1 : (x₀ * d)⁻¹ = x₀ * d := inv_eq_of_mul_eq_one_right h2sq
    have h2 : (x₀ * d)⁻¹ = d * x₀ := by
      rw [mul_inv_rev, hdi, inv_eq_of_mul_eq_one_right hx2]
    rw [← h2, h1]
  refine ⟨hdx, ?_⟩
  have : x₀ * (d * z₀) = x₀ * (z₀ * d) := by
    calc x₀ * (d * z₀) = (x₀ * d) * z₀ := by group
      _ = (d * x₀) * z₀ := by rw [← hdx]
      _ = d * (x₀ * z₀) := by group
      _ = (x₀ * z₀) * d := hdc
      _ = x₀ * (z₀ * d) := by group
  exact mul_left_cancel this

variable [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]

theorem H3_local (M : TModel T T₁ 3 m) (h62 : Sec62) (h63 : Sec63) (h77 : Sec77)
    (hc : Sec6Ctx T T₁ 3 m) (hnat : NaturalSL T (hSub T (normIn T₁ T)) 3 m) {x z : G}
    (hl : Loc710 T T₁ x z) {β d : G} (hβD : β ∈ classD T) (hβM : β ∈ cfgM T T₁)
    (hdD : d ∈ classD T) (hdv : d * (x * z) = (x * z) * d) (hdβ : d * β = β * d) :
    d ∈ cfgM T T₁ := by
  have hcfg := hc.sec3.cfg
  have hwcT := hc.hy.pair.wc
  have hwcT₁ := hcfg.wc₁
  obtain ⟨hzD, hzT⟩ := mem_normD_of_mem_normIn₁ hc hl.zL hl.z1
  have hxD : x ∈ classD T := mem_classD_of_mem hl.xT hl.x1
  have hxz1 : x * z ≠ 1 := by
    intro h
    apply hzT
    have : z = x⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact T.inv_mem hl.xT
  by_cases hβT : β ∈ T
  ·
    have hβ1 : β ≠ 1 := ne_one_of_mem_classD hβD
    have hdN : d ∈ Subgroup.normalizer (T : Set G) :=
      hwcT.centralizer_le_normalizer hβT hβ1 (Subgroup.mem_centralizer_singleton_iff.2 hdβ)
    obtain ⟨hdx, hdz⟩ := comm_of_sec77 h77 hc hnat hwcT.1 hl.xT hxD hzD.1 hl.xz hxz1 hl.xzD hdD
      hdN hdv
    exact mem_cfgM_of_comm M h62 h63 hc hl ⟨hdD, hdN⟩ hdz hdx
  ·
    obtain ⟨l, hlL, e, he, rfl⟩ := hcfg.mem_cfgM_iff.1 hβM
    have he1 : e ≠ 1 := by
      rintro rfl
      exact hβT (by simpa using normIn_le _ _ hlL)
    obtain ⟨heD, heT⟩ := mem_normD_of_mem_normIn₁ hc he he1
    have hle : l * e = e * l := hcfg.comm_L_L₁ hlL he
    obtain ⟨s, hsT, hs⟩ := hc.eq_conj_of_mem_coset h62 h63 heD heT hβD (normIn_le _ _ hlL) hle
    have hxL : x ∈ normIn T T₁ := (mem_normIn_iff_comm h63 hc hl.zL hl.z1 hl.xT).2 hl.xz.symm
    have hsz : ⁅s, z⁆ ∈ normIn T T₁ := by
      have := comm_mem_normIn M h63 hc hl.zL hsT
      have h2 : ⁅s, z⁆ = (⁅z, s⁆)⁻¹ := (commutatorElement_inv z s).symm
      rw [h2]
      exact (normIn T T₁).inv_mem this
    set x' : G := x * ⁅s, z⁆ with hx'def
    have hx'L : x' ∈ normIn T T₁ := (normIn T T₁).mul_mem hxL hsz
    have hx'T : x' ∈ T := normIn_le _ _ hx'L
    have hv' : s * (x * z) * s⁻¹ = x' * z := by
      have hsx : s * x = x * s := elemAbelian_mul_comm hwcT.1 hsT hl.xT
      rw [hx'def, commutatorElement_def]
      calc s * (x * z) * s⁻¹ = (s * x) * z * s⁻¹ := by group
        _ = (x * s) * z * s⁻¹ := by rw [hsx]
        _ = x * (s * z * s⁻¹ * z⁻¹) * z := by group
    have hx'z : x' * z = z * x' := hcfg.comm_L_L₁ hx'L hl.zL
    have hx'zD : x' * z ∉ classD T := by
      intro hD
      apply hl.xzD
      rw [← hv'] at hD
      have := classD_conj hD s
      have e : s⁻¹ * (s * (x * z) * s⁻¹) * s = x * z := by group
      rwa [e] at this
    have hx'1 : x' ≠ 1 := by
      intro h1
      apply hx'zD
      rw [h1, one_mul]
      exact hzD.1
    have hl' : Loc710 T T₁ x' z := ⟨hx'T, hx'1, hl.zL, hl.z1, hx'z, hx'zD⟩
    set d' : G := s * d * s⁻¹ with hd'def
    have hd'D : d' ∈ classD T := classD_conj_mul hdD s
    have hd'v : d' * (x' * z) = (x' * z) * d' := by
      rw [← hv', hd'def]
      calc s * d * s⁻¹ * (s * (x * z) * s⁻¹) = s * (d * (x * z)) * s⁻¹ := by group
        _ = s * ((x * z) * d) * s⁻¹ := by rw [hdv]
        _ = s * (x * z) * s⁻¹ * (s * d * s⁻¹) := by group
    have hd'e : d' * e = e * d' := by
      have hβe : s⁻¹ * e * s = l * e := hs.symm
      have h1 : e = s * (l * e) * s⁻¹ := by rw [← hβe]; group
      calc d' * e = s * d * s⁻¹ * (s * (l * e) * s⁻¹) := by rw [← h1]
        _ = s * (d * (l * e)) * s⁻¹ := by group
        _ = s * ((l * e) * d) * s⁻¹ := by rw [hdβ]
        _ = s * (l * e) * s⁻¹ * (s * d * s⁻¹) := by group
        _ = e * d' := by rw [← h1]
    have hd'N₁ : d' ∈ Subgroup.normalizer (T₁ : Set G) :=
      hwcT₁.centralizer_le_normalizer (normIn_le _ _ he) he1
        (Subgroup.mem_centralizer_singleton_iff.2 hd'e)
    have hzx'1 : z * x' ≠ 1 := by
      intro h
      apply hzT
      have : z = x'⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact T.inv_mem hx'T
    have hzx'D : z * x' ∉ classD T := by rw [← hx'z]; exact hx'zD
    obtain ⟨hd'z, hd'x'⟩ := comm_of_sec77 h77 hc hnat hwcT₁.1 (normIn_le _ _ hl.zL) hzD.1
      (mem_classD_of_mem hx'T hx'1) hx'z.symm hzx'1 hzx'D hd'D hd'N₁
      (by rw [← hx'z]; exact hd'v)
    have hd'N : d' ∈ Subgroup.normalizer (T : Set G) :=
      hwcT.centralizer_le_normalizer hx'T hx'1 (Subgroup.mem_centralizer_singleton_iff.2 hd'x')
    have hd'M : d' ∈ cfgM T T₁ := mem_cfgM_of_comm M h62 h63 hc hl' ⟨hd'D, hd'N⟩ hd'z hd'x'
    have := conj_mem_cfgM M h63 hc (T.inv_mem hsT) hd'M
    rw [inv_inv, hd'def] at this
    have h3 : s⁻¹ * (s * d * s⁻¹) * s = d := by group
    rwa [h3] at this

omit [(T.subgroupOf (hSub T (normIn T₁ T))).Normal] in
theorem exists_loc710 (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ 3 m)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) 3 m) {x y z : G} {k : ℕ}
    (hcfg : BadConfig78 T x z y k) :
    ∃ x' y' z' : G, Loc710 T T₁ x' z' ∧ y' ∈ classD T ∧ y' * (x' * z') = (x' * z') * y' ∧
      orderOf (x' * y') = 2 * k := by
  have hcf := hc.sec3.cfg
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ normIn T₁ T, u ≠ 1 := by
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hcf.ne₁
    exact ⟨u, hu, fun h => hu1 (Subtype.ext h)⟩
  obtain ⟨huD, huT⟩ := mem_normD_of_mem_normIn₁ hc hu hu1
  obtain ⟨g, hg, hgz⟩ := hc.sec67_conj h1 h62 h63 (by omega) hnat z hcfg.zN hcfg.zT u huD huT
  have hxT : g * x * g⁻¹ ∈ T := conj_mem_of_mem_normalizer hg hcfg.xT
  refine ⟨g * x * g⁻¹, g * y * g⁻¹, u, ⟨hxT, ?_, hu, hu1, ?_, ?_⟩, classD_conj_mul hcfg.yD g, ?_,
    ?_⟩
  · intro h
    apply hcfg.x1
    have : g * x * g⁻¹ = g * 1 * g⁻¹ := by rw [h]; group
    simpa using this
  · rw [hgz]
    calc g * x * g⁻¹ * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
      _ = g * (z * x) * g⁻¹ := by rw [hcfg.xz]
      _ = g * z * g⁻¹ * (g * x * g⁻¹) := by group
  · intro hD
    apply hcfg.xzD
    have h2 : g * x * g⁻¹ * u = g * (x * z) * g⁻¹ := by rw [hgz]; group
    rw [h2] at hD
    have := classD_conj hD g
    have e : g⁻¹ * (g * (x * z) * g⁻¹) * g = x * z := by group
    rwa [e] at this
  · rw [hgz]
    calc g * y * g⁻¹ * (g * x * g⁻¹ * (g * z * g⁻¹)) = g * (y * (x * z)) * g⁻¹ := by group
      _ = g * ((x * z) * y) * g⁻¹ := by rw [hcfg.yc]
      _ = g * x * g⁻¹ * (g * z * g⁻¹) * (g * y * g⁻¹) := by group
  · have h2 : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    rw [h2]
    have := MulEquiv.orderOf_eq (MulAut.conj g) (x * y)
    simpa [MulAut.conj_apply, hcfg.ord] using this

end CFSG.CGT.T75F
