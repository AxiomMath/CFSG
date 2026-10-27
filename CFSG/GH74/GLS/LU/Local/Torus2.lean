module

public import CFSG.GH74.GLS.LU.Local.Torus1
public import CFSG.GH74.GLS.LU.Local.ActBridge

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
open scoped Pointwise MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

variable {G : Type} [Group G] [Finite G] {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}

omit [Finite G] in
theorem mem_normalizer_cj_iff (K : Subgroup G) (h w : G) :
    w ∈ normalizer ((cj K h : Subgroup G) : Set G) ↔ h * w * h⁻¹ ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro hw k
    have hx := hw (h⁻¹ * k * h)
    rw [mem_cj, mem_cj] at hx
    have e1 : h * (h⁻¹ * k * h) * h⁻¹ = k := by group
    have e2 : h * (w * (h⁻¹ * k * h) * w⁻¹) * h⁻¹ = (h * w * h⁻¹) * k * (h * w * h⁻¹)⁻¹ := by group
    rw [e1, e2] at hx
    exact hx
  · intro hw x
    have hx := hw (h * x * h⁻¹)
    rw [mem_cj, mem_cj]
    have e2 : (h * w * h⁻¹) * (h * x * h⁻¹) * (h * w * h⁻¹)⁻¹ = h * (w * x * w⁻¹) * h⁻¹ := by group
    rw [e2] at hx
    exact hx

omit [Finite G] in
theorem exists_h₀ (hs : LUSyl G z S K₁ K₂ t u) : ∃ h₀ : G, h₀⁻¹ * z * h₀ = u := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hs.u_conj
  refine ⟨c⁻¹, ?_⟩
  rw [inv_inv]; exact hc

theorem invol_nontriv {q : ℕ} (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) (hq : Odd q)
    {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) {w : G} (hwC : w ∈ Cz z) (hw2 : w * w = 1)
    (hwz : w ∉ zpowers z) : ∃ k ∈ K, w * k ≠ k * w := by
  by_contra h
  push Not at h
  exact hwz (inv_cent_mem_zpowers hc hs hq hK hwC hw2 h)

variable {p f : ℕ} {ε : ℤ}

omit [Finite G] in
theorem orderOf_conj' (h a : G) : orderOf (h * a * h⁻¹) = orderOf a := by
  have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective a
  simpa using this

omit [Finite G] in
theorem conj_mul_mul (h a b : G) : (h * a * h⁻¹) * (h * b * h⁻¹) = h * (a * b) * h⁻¹ := by group

omit [Finite G] in
theorem conj_comm_conj {h a b : G} (hab : a * b = b * a) :
    (h * a * h⁻¹) * (h * b * h⁻¹) = (h * b * h⁻¹) * (h * a * h⁻¹) := by
  rw [conj_mul_mul, conj_mul_mul, hab]

omit [Finite G] in
theorem conj_comm_z {h₀ w : G} (hh₀ : h₀⁻¹ * z * h₀ = u) (hwu : w * u = u * w) :
    (h₀ * w * h₀⁻¹) * z = z * (h₀ * w * h₀⁻¹) := by
  have hz' : h₀ * u * h₀⁻¹ = z := by rw [← hh₀]; group
  have := conj_comm_conj (h := h₀) hwu
  rw [hz'] at this
  exact this

theorem exists_b {q r : ℕ} (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) (hr : r.Prime)
    (hr2 : r ≠ 2) {a₁ : G} (ha₁K : a₁ ∈ K₁) (ha₁u : a₁ * u = u * a₁) (hord : orderOf a₁ = r) :
    ∃ b : G, orderOf b = r ∧ b * z = z * b ∧ b * u = u * b ∧ b * t = t * b ∧
      b ∈ K₁ ⊔ K₂ ∧ (∃ a₂ ∈ K₂, a₂ = t * a₁ * t⁻¹ ∧ b = a₁ * a₂ ∧ orderOf a₂ = r ∧ a₂ * u = u * a₂) := by
  have : Fact r.Prime := ⟨hr⟩
  have ht2 : t * t = 1 := hs.t_sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set a₂ : G := t * a₁ * t⁻¹ with ha₂
  have ha₂K : a₂ ∈ K₂ := LUComps.mem_of_map hs.t_swap ha₁K
  have ha₂ord : orderOf a₂ = r := by rw [ha₂, orderOf_conj', hord]
  have h12 : a₁ * a₂ = a₂ * a₁ := hc.comm a₁ ha₁K a₂ ha₂K
  have ha₂u : a₂ * u = u * a₂ := by
    have hut : u * t = t * u := hs.ut
    calc a₂ * u = t * a₁ * t⁻¹ * u := rfl
      _ = t * a₁ * (t⁻¹ * u) := by group
      _ = t * a₁ * (u * t⁻¹) := by
          rw [htinv]
          congr 1
          exact hut.symm
      _ = t * (a₁ * u) * t⁻¹ := by group
      _ = t * (u * a₁) * t⁻¹ := by rw [ha₁u]
      _ = u * (t * a₁ * t⁻¹) := by
          calc t * (u * a₁) * t⁻¹ = (t * u) * a₁ * t⁻¹ := by group
            _ = (u * t) * a₁ * t⁻¹ := by rw [hut]
            _ = u * (t * a₁ * t⁻¹) := by group
  set b : G := a₁ * a₂ with hb
  have hbr : b ^ r = 1 := by
    have h1 : Commute a₁ a₂ := h12
    rw [hb, h1.mul_pow]
    have h2 : a₁ ^ r = 1 := by rw [← hord]; exact pow_orderOf_eq_one a₁
    have h3 : a₂ ^ r = 1 := by rw [← ha₂ord]; exact pow_orderOf_eq_one a₂
    rw [h2, h3, one_mul]
  have hb1 : b ≠ 1 := by
    intro h
    have h1 : a₁ = a₂⁻¹ := by
      have : a₁ * a₂ = 1 := h
      exact eq_inv_of_mul_eq_one_left this
    have h2 : a₁ ∈ K₁ ⊓ K₂ := ⟨ha₁K, by rw [h1]; exact K₂.inv_mem ha₂K⟩
    rw [hc.inf_eq] at h2
    have h3 : orderOf a₁ ∣ orderOf z := orderOf_dvd_of_mem_zpowers h2
    rw [hord, hs.z_inv] at h3
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h3)
  refine ⟨b, orderOf_eq_prime hbr hb1, ?_, ?_, ?_, ?_, ⟨a₂, ha₂K, rfl, rfl, ha₂ord, ha₂u⟩⟩
  · have e1 := hc.cz₁ ha₁K
    have e2 := hc.cz₂ ha₂K
    calc b * z = a₁ * (a₂ * z) := by rw [hb]; group
      _ = a₁ * (z * a₂) := by rw [e2]
      _ = (a₁ * z) * a₂ := by group
      _ = (z * a₁) * a₂ := by rw [e1]
      _ = z * b := by rw [hb]; group
  · calc b * u = a₁ * (a₂ * u) := by rw [hb]; group
      _ = a₁ * (u * a₂) := by rw [ha₂u]
      _ = (a₁ * u) * a₂ := by group
      _ = (u * a₁) * a₂ := by rw [ha₁u]
      _ = u * b := by rw [hb]; group
  ·
    have htb : t * b * t⁻¹ = b := by
      have e1 : t * a₂ * t⁻¹ = a₁ := by
        rw [ha₂]
        calc t * (t * a₁ * t⁻¹) * t⁻¹ = (t * t) * a₁ * (t * t)⁻¹ := by group
          _ = a₁ := by rw [ht2]; group
      calc t * b * t⁻¹ = (t * a₁ * t⁻¹) * (t * a₂ * t⁻¹) := by rw [hb]; group
        _ = a₂ * a₁ := by rw [e1]
        _ = b := h12.symm
    calc b * t = (t * b * t⁻¹) * t := by rw [htb]
      _ = t * b := by group
  · exact (K₁ ⊔ K₂).mul_mem (Subgroup.mem_sup_left ha₁K) (Subgroup.mem_sup_right ha₂K)

theorem norm₂_of_norm₁ {q : ℕ} (hc : LUComps G q z K₁ K₂) {w : G} (hwC : w ∈ Cz z)
    (hw : w ∈ normalizer (K₁ : Set G)) : w ∈ normalizer (K₂ : Set G) := by
  rcases hc.perm hwC with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr e2
  · exfalso
    have this : K₁.map (MulAut.conj w).toMonoidHom = K₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hw
    rw [e1] at this
    exact hc.ne this.symm

omit [Finite G] in
theorem t_ne_one (hs : LUSyl G z S K₁ K₂ t u) : t ≠ 1 := by
  intro h
  have h1 := orderOf_eq_of_isConj hs.t_conj
  rw [h, orderOf_one, hs.z_inv] at h1
  omega

theorem z_norm_L (X : LUCtx G p f z S K₁ K₂ t u ε) {h₀ : G}
    (hh₀ : h₀⁻¹ * z * h₀ = u) : z ∈ normalizer ((cj K₁ h₀ : Subgroup G) : Set G) := by
  have hc := X.comps
  have hs := X.syl
  refine normalizes_L X hh₀ hs.zu_comm hs.z_sq (g := 1) (by simp) ?_ ?_ hs.u_ne
  · intro k hk
    simpa using conj_mem_of_mem_normalizer hs.u_norm hk
  · intro k hk
    simpa using conj_mem_of_mem_normalizer (u_norm₂ hc hs) hk

theorem t_norm_L (X : LUCtx G p f z S K₁ K₂ t u ε) {h₀ : G}
    (hh₀ : h₀⁻¹ * z * h₀ = u) : t ∈ normalizer ((cj K₁ h₀ : Subgroup G) : Set G) := by
  have hc := X.comps
  have hs := X.syl
  obtain ⟨g, hgt, hJ₁, hJ₂⟩ := X.h61.u_norm_J
  have htu : t * u = u * t := hs.ut.symm
  refine normalizes_L X hh₀ htu hs.t_sq hgt ?_ ?_ (fun h => hs.t_not_normalizer hc (h ▸ hs.u_norm))
  · intro k hk
    have ha : g⁻¹ * k * g ∈ cj K₁ g := by
      rw [mem_cj]; simpa [mul_assoc] using hk
    have h1 := mem_cj.mp (hJ₁ _ ha)
    have e : g * (u * (g⁻¹ * k * g) * u⁻¹) * g⁻¹ = (g * u * g⁻¹) * k * (g * u * g⁻¹)⁻¹ := by
      group
    rw [e] at h1; exact h1
  · intro k hk
    have ha : g⁻¹ * k * g ∈ cj K₂ g := by
      rw [mem_cj]; simpa [mul_assoc] using hk
    have h1 := mem_cj.mp (hJ₂ _ ha)
    have e : g * (u * (g⁻¹ * k * g) * u⁻¹) * g⁻¹ = (g * u * g⁻¹) * k * (g * u * g⁻¹)⁻¹ := by
      group
    rw [e] at h1; exact h1

theorem exists_a0_of (X : LUCtx G p f z S K₁ K₂ t u ε) {r : ℕ} (hr : GoodR p f r) {a₁ : G}
    (ha₁ : a₁ ∈ K₁ ⊓ centralizer ({u} : Set G)) (hord : orderOf a₁ = r) :
    ∃ a₀ ∈ A0 z, orderOf a₀ = r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hrp, hr2, hrne, hrf, hgood⟩ := hr
  have hc := X.comps
  have hs := X.syl
  have hq := X.odd_q
  have hz2 : z * z = 1 := hs.z_sq
  have ht2 : t * t = 1 := hs.t_sq
  have hu2 : u * u = 1 := hs.u_sq
  obtain ⟨h₀, hh₀⟩ := exists_h₀ hs
  have ha₁K : a₁ ∈ K₁ := ha₁.1
  have ha₁u : a₁ * u = u * a₁ := mem_centralizer_singleton_iff.mp ha₁.2
  obtain ⟨b, hbord, hbz, hbu, hbt, hbK, ⟨a₂, ha₂K, ha₂, hb, -, -⟩⟩ :=
    exists_b hc hs hrp hr2 ha₁K ha₁u hord
  set zc : G := h₀ * z * h₀⁻¹ with hzc
  set tc : G := h₀ * t * h₀⁻¹ with htc
  set bc : G := h₀ * b * h₀⁻¹ with hbc
  have hcu := comps_u X hh₀
  have hzu : z * u = u * z := hs.zu_comm
  have htu : t * u = u * t := hs.ut.symm
  have hzcC : zc ∈ Cz z := mem_centralizer_singleton_iff.mpr (conj_comm_z hh₀ hzu)
  have htcC : tc ∈ Cz z := mem_centralizer_singleton_iff.mpr (conj_comm_z hh₀ htu)
  have hbcC : bc ∈ Cz z := mem_centralizer_singleton_iff.mpr (conj_comm_z hh₀ hbu)
  have hzL := z_norm_L X hh₀
  have htL := t_norm_L X hh₀
  have hbL : b ∈ normalizer ((cj K₁ h₀ : Subgroup G) : Set G) := by
    have hbodd : Odd (orderOf b) := by rw [hbord]; exact hrp.odd_of_ne_two hr2
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (hcu.odd_fix (mem_centralizer_singleton_iff.mpr hbu) hbodd).1
  have hzcn : zc ∈ normalizer (K₁ : Set G) := (mem_normalizer_cj_iff K₁ h₀ z).mp hzL
  have htcn : tc ∈ normalizer (K₁ : Set G) := (mem_normalizer_cj_iff K₁ h₀ t).mp htL
  have hbcn : bc ∈ normalizer (K₁ : Set G) := (mem_normalizer_cj_iff K₁ h₀ b).mp hbL
  have hzcn₂ := norm₂_of_norm₁ hc hzcC hzcn
  have htcn₂ := norm₂_of_norm₁ hc htcC htcn
  have hbcn₂ := norm₂_of_norm₁ hc hbcC hbcn
  have hzc2 : zc * zc = 1 := by rw [hzc, conj_mul_mul, hz2]; group
  have htc2 : tc * tc = 1 := by rw [htc, conj_mul_mul, ht2]; group
  have h12 : zc * tc = tc * zc := conj_comm_conj hs.zt_comm
  have hy1 : bc * zc = zc * bc := conj_comm_conj hbz
  have hy2 : bc * tc = tc * bc := conj_comm_conj hbt
  have hzctc2 : (zc * tc) * (zc * tc) = 1 := by
    calc (zc * tc) * (zc * tc) = (zc * zc) * (tc * tc) := by
          calc (zc * tc) * (zc * tc) = zc * (tc * zc) * tc := by group
            _ = zc * (zc * tc) * tc := by rw [h12]
            _ = (zc * zc) * (tc * tc) := by group
      _ = 1 := by rw [hzc2, htc2]; group
  have hyr : bc ^ r = 1 := by
    rw [hbc, conj_pow]
    have : b ^ r = 1 := by rw [← hbord]; exact pow_orderOf_eq_one b
    rw [this]; group
  have hzcz : zc ∉ zpowers z := by
    intro hmem
    rcases eq_one_or_eq_of_mem_zpowers hz2 hmem with h | h
    · apply hs.z_ne_one
      calc z = h₀⁻¹ * zc * h₀ := by rw [hzc]; group
        _ = 1 := by rw [h]; group
    · apply hs.u_ne
      calc u = h₀⁻¹ * z * h₀ := hh₀.symm
        _ = h₀⁻¹ * zc * h₀ := by rw [h]
        _ = z := by rw [hzc]; group
  have htcz : tc ∉ zpowers z := by
    intro hmem
    rcases eq_one_or_eq_of_mem_zpowers hz2 hmem with h | h
    · apply t_ne_one hs
      calc t = h₀⁻¹ * tc * h₀ := by rw [htc]; group
        _ = 1 := by rw [h]; group
    · apply hs.t_not_normalizer hc
      have : t = u := by
        calc t = h₀⁻¹ * tc * h₀ := by rw [htc]; group
          _ = h₀⁻¹ * z * h₀ := by rw [h]
          _ = u := hh₀
      rw [this]; exact hs.u_norm
  have hzctcz : zc * tc ∉ zpowers z := by
    intro hmem
    rcases eq_one_or_eq_of_mem_zpowers hz2 hmem with h | h
    · apply hs.t_ne_z hc
      have h1 : z * t = 1 := by
        calc z * t = h₀⁻¹ * (zc * tc) * h₀ := by rw [hzc, htc]; group
          _ = 1 := by rw [h]; group
      calc t = z * (z * t) := by rw [← mul_assoc, hz2, one_mul]
        _ = z := by rw [h1, mul_one]
    · apply hs.t_not_normalizer hc
      have h1 : z * t = u := by
        calc z * t = h₀⁻¹ * (zc * tc) * h₀ := by rw [hzc, htc]; group
          _ = h₀⁻¹ * z * h₀ := by rw [h]
          _ = u := hh₀
      have h2 : t = z * u := by
        calc t = z * (z * t) := by rw [← mul_assoc, hz2, one_mul]
          _ = z * u := by rw [h1]
      rw [h2]
      exact (normalizer (K₁ : Set G)).mul_mem hc.z_mem_normalizer₁ hs.u_norm
  have ho2 : ∀ w : G, w * w = 1 → w ≠ 1 → ∃ n : ℕ, orderOf w = 2 ^ n := by
    intro w hw hw1
    refine ⟨1, ?_⟩
    have : w ^ 2 = 1 := by rw [pow_two]; exact hw
    simpa using orderOf_eq_prime this hw1
  have hzc1 : zc ≠ 1 := fun h => hzcz (h ▸ Subgroup.one_mem _)
  have htc1 : tc ≠ 1 := fun h => htcz (h ▸ Subgroup.one_mem _)
  have hzctc1 : zc * tc ≠ 1 := fun h => hzctcz (h ▸ Subgroup.one_mem _)
  obtain ⟨F, hF, hFin, hFq, -⟩ := hc.sl₁
  obtain ⟨e₁⟩ := exists_mulEquiv_SL2 hc.sl₁ F hFq
  obtain ⟨e₂⟩ := exists_mulEquiv_SL2 hc.sl₂ F hFq
  have h3 : 3 < p ^ f := lt_of_lt_of_le (by norm_num) X.hq
  have hK₁ : ∀ k ∈ K₁, bc * k = k * bc :=
    centralizes_of_four_group X.hp hFq X.hp2 h3 hrp hr2 hrf e₁ hzcn htcn hbcn hzc2 htc2 h12 hy1 hy2 hyr
      (invol_nontriv hc hs hq (Or.inl rfl) hzcC hzc2 hzcz)
      (invol_nontriv hc hs hq (Or.inl rfl) htcC htc2 htcz)
      (invol_nontriv hc hs hq (Or.inl rfl) ((Cz z).mul_mem hzcC htcC) hzctc2 hzctcz)
      (cenAb_C hc hs (Or.inl rfl) hzcC (ho2 zc hzc2 hzc1) hzcn
        (invol_nontriv hc hs hq (Or.inl rfl) hzcC hzc2 hzcz))
      (cenAb_C hc hs (Or.inl rfl) htcC (ho2 tc htc2 htc1) htcn
        (invol_nontriv hc hs hq (Or.inl rfl) htcC htc2 htcz))
  have hK₂ : ∀ k ∈ K₂, bc * k = k * bc :=
    centralizes_of_four_group X.hp hFq X.hp2 h3 hrp hr2 hrf e₂ hzcn₂ htcn₂ hbcn₂ hzc2 htc2 h12 hy1 hy2
      hyr
      (invol_nontriv hc hs hq (Or.inr rfl) hzcC hzc2 hzcz)
      (invol_nontriv hc hs hq (Or.inr rfl) htcC htc2 htcz)
      (invol_nontriv hc hs hq (Or.inr rfl) ((Cz z).mul_mem hzcC htcC) hzctc2 hzctcz)
      (cenAb_C hc hs (Or.inr rfl) hzcC (ho2 zc hzc2 hzc1) hzcn₂
        (invol_nontriv hc hs hq (Or.inr rfl) hzcC hzc2 hzcz))
      (cenAb_C hc hs (Or.inr rfl) htcC (ho2 tc htc2 htc1) htcn₂
        (invol_nontriv hc hs hq (Or.inr rfl) htcC htc2 htcz))
  have hbcCCK : bc ∈ CCK z K₁ K₂ := by
    refine mem_CCK.mpr ⟨hbcC, fun k hk => ?_⟩
    obtain ⟨a, ha, b', hb', rfl⟩ := mem_sup_of_commute hc.comm hk
    have e1 := hK₁ a ha
    have e2 := hK₂ b' hb'
    calc bc * (a * b') = (bc * a) * b' := by group
      _ = (a * bc) * b' := by rw [e1]
      _ = a * (bc * b') := by group
      _ = a * (b' * bc) := by rw [e2]
      _ = (a * b') * bc := by group
  have hodd : Odd (orderOf bc) := by rw [hbc, orderOf_conj', hbord]; exact hrp.odd_of_ne_two hr2
  exact ⟨bc, odd_mem_A0_of_centralizes hs hc hbcCCK hodd, by rw [hbc, orderOf_conj', hbord]⟩

end CFSG.GH74.GLS.LU.Local
