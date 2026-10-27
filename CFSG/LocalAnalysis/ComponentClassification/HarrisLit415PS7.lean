module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PS6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PS1

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem exists_conj_alpha_mul
    (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁)
    {ℓ c : X} (hℓ : ℓ ∈ 𝒱 ⊓ centralizer {z₁}) (hℓc : ℓ * ℓ = c) (hc1 : c ≠ 1)
    (hc2 : c * c = 1) (hcc : ∀ v ∈ 𝒱 ⊓ centralizer {z₁}, v * c = c * v)
    (hcz : ∀ g : X, g * z * g⁻¹ ≠ c)
    (hn : ∀ v ∈ 𝒱 ⊓ centralizer {z₁}, v * ℓ * v⁻¹ = ℓ ∨ v * ℓ * v⁻¹ = ℓ * c) :
    ∃ g' : X, g' * α * g'⁻¹ = α * c := by
  have hαV := hD.fd.α_mem
  have hcℓ : ℓ * c = c * ℓ := hcc ℓ hℓ
  rcases hn α hαV with h | h
  · exfalso
    obtain ⟨g, i', j', hgα, hgz, hgS, -⟩ := hD.exists_conj_x hnβ
    have hσ := hD.hs.setup
    have hαℓ : ℓ * α = α * ℓ := by
      calc ℓ * α = α * ℓ * α⁻¹ * α := by rw [h]
        _ = α * ℓ := by group
    have hℓ4 : ℓ ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hℓc, hc2]
    have hzpow : ∀ y ∈ zpowers ℓ, y = 1 ∨ y = ℓ ∨ y = c ∨ y = ℓ * c := by
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      have hk : ℓ ^ k = ℓ ^ (k % 4) := by
        have hℓ4' : ℓ ^ (4 : ℤ) = 1 := by
          rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, hℓ4]
        conv_lhs => rw [← Int.mul_ediv_add_emod k 4, zpow_add, zpow_mul, hℓ4', one_zpow, one_mul]
      have h0 : 0 ≤ k % 4 := Int.emod_nonneg k (by norm_num)
      have h4 : k % 4 < 4 := Int.emod_lt_of_pos k (by norm_num)
      rw [hk]
      interval_cases (k % 4)
      · left; exact zpow_zero ℓ
      · right; left; rw [zpow_one]
      · right; right; left
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sq, hℓc]
      · right; right; right
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, pow_succ, sq, hℓc, hcℓ]
    have hℓV : zpowers ℓ ≤ 𝒱 ⊓ centralizer {z₁} := zpowers_le.mpr hℓ
    have hgS' : ∀ y ∈ 𝒱 ⊓ centralizer ({α} : Set X), g⁻¹ * y * g ∈ S := by
      intro y hy
      rw [← hgS] at hy
      obtain ⟨s, hs, hsy⟩ := hy
      have hsy' : g * s * g⁻¹ = y := hsy
      rw [← hsy']
      simpa [mul_assoc] using hs
    have hET : (zpowers ℓ).map (MulAut.conj g⁻¹).toMonoidHom ≤
        zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
      rintro _ ⟨y, hy, rfl⟩
      have hyV := hℓV hy
      have hyα : y * α = α * y := by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        exact (Commute.zpow_left (show Commute ℓ α from hαℓ) k).eq
      have hyS := hgS' y ⟨hyV.1, mem_centralizer_singleton_iff.mpr hyα⟩
      rw [← hσ.centralizer_u]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      refine ⟨hyS, mem_centralizer_singleton_iff.mpr ?_⟩
      have hyz₁ : y * z₁ = z₁ * y := mem_centralizer_singleton_iff.mp hyV.2
      have hx : g⁻¹ * y * g * (w ^ (orderOf w / 2) * t ^ i' * z ^ j') =
          (w ^ (orderOf w / 2) * t ^ i' * z ^ j') * (g⁻¹ * y * g) := by
        have hx' : w ^ (orderOf w / 2) * t ^ i' * z ^ j' = g⁻¹ * z₁ * g := by
          rw [← hgz]; group
        rw [hx']
        calc g⁻¹ * y * g * (g⁻¹ * z₁ * g) = g⁻¹ * (y * z₁) * g := by group
          _ = g⁻¹ * (z₁ * y) * g := by rw [hyz₁]
          _ = g⁻¹ * z₁ * g * (g⁻¹ * y * g) := by group
      have ht : g⁻¹ * y * g * t = t * (g⁻¹ * y * g) :=
        mem_centralizer_singleton_iff.mp (hD.hs.sylow.le hyS)
      have hz : g⁻¹ * y * g * z = z * (g⁻¹ * y * g) := hσ.z_comm hyS
      have htz : Commute (g⁻¹ * y * g) (t ^ i' * z ^ j') :=
        ((Commute.pow_right (show Commute (g⁻¹ * y * g) t from ht) i').mul_right
          (Commute.pow_right (show Commute (g⁻¹ * y * g) z from hz) j'))
      have hu : w ^ (orderOf w / 2) = (w ^ (orderOf w / 2) * t ^ i' * z ^ j') *
          (t ^ i' * z ^ j')⁻¹ := by group
      rw [hu]
      exact ((show Commute (g⁻¹ * y * g) (w ^ (orderOf w / 2) * t ^ i' * z ^ j') from hx).mul_right
        htz.inv_right).eq
    have hEn : ∀ s ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w,
        ∀ e ∈ (zpowers ℓ).map (MulAut.conj g⁻¹).toMonoidHom,
          s * e * s⁻¹ ∈ (zpowers ℓ).map (MulAut.conj g⁻¹).toMonoidHom := by
      intro s hs e he
      obtain ⟨y, hy, rfl⟩ := he
      have hsS := hσ.T_le hs
      have hvV : g * s * g⁻¹ ∈ 𝒱 ⊓ centralizer {z₁} := by
        have h1 : g * s * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := ⟨s, hsS, rfl⟩
        rw [hgS] at h1
        refine ⟨h1.1, mem_centralizer_singleton_iff.mpr ?_⟩
        have hxT := (hσ.X_le_center_T (Standing.Setup42.beta_mem_X i' j')).2
        have h2 : s * (w ^ (orderOf w / 2) * t ^ i' * z ^ j') =
            (w ^ (orderOf w / 2) * t ^ i' * z ^ j') * s :=
          mem_centralizer_iff.mp hxT s hs
        rw [← hgz]
        calc g * s * g⁻¹ * (g * (w ^ (orderOf w / 2) * t ^ i' * z ^ j') * g⁻¹) =
            g * (s * (w ^ (orderOf w / 2) * t ^ i' * z ^ j')) * g⁻¹ := by group
          _ = g * ((w ^ (orderOf w / 2) * t ^ i' * z ^ j') * s) * g⁻¹ := by rw [h2]
          _ = _ := by group
      have hvy : (g * s * g⁻¹) * y * (g * s * g⁻¹)⁻¹ ∈ zpowers ℓ := by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
        refine zpow_mem ?_ k
        have hcZ : c ∈ zpowers ℓ := by
          rw [← hℓc]
          exact mul_mem (mem_zpowers ℓ) (mem_zpowers ℓ)
        rcases hn _ hvV with h1 | h1 <;> rw [h1]
        · exact mem_zpowers ℓ
        · exact mul_mem (mem_zpowers ℓ) hcZ
      refine ⟨_, hvy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    by_cases hzE : z ∈ (zpowers ℓ).map (MulAut.conj g⁻¹).toMonoidHom
    · obtain ⟨y, hy, hyz⟩ := hzE
      have hyz' : g⁻¹ * y * g = z := by simpa using hyz
      have hgz' : g * z * g⁻¹ = y := by rw [← hyz']; group
      have hz2 : z * z = 1 := by
        rw [← sq]
        exact hσ.sq_eq_one_of_mem_X (subset_closure (by simp))
      have hy2 : y * y = 1 := by
        rw [← hgz', show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hz2]
        group
      rcases hzpow y hy with h1 | h1 | h1 | h1
      · apply hD.z_ne_one
        rw [← hyz', h1]
        group
      · apply hc1
        rw [← hℓc, ← h1, hy2]
      · exact hcz g (hgz'.trans h1)
      · apply hc1
        rw [h1, show ℓ * c * (ℓ * c) = ℓ * ℓ * (c * c) by
          rw [mul_assoc, ← mul_assoc c ℓ, ← hcℓ]; group, hℓc, hc2, mul_one] at hy2
        exact hy2
    · obtain ⟨hX, -⟩ := hσ.le_X_of_normal hET hEn hzE
      have hℓX : g⁻¹ * ℓ * g ∈ closure {t, w ^ (orderOf w / 2), z} :=
        hX ⟨ℓ, mem_zpowers ℓ, by simp⟩
      have h1 := hσ.sq_eq_one_of_mem_X hℓX
      apply hc1
      rw [← hℓc]
      rw [sq, show g⁻¹ * ℓ * g * (g⁻¹ * ℓ * g) = g⁻¹ * (ℓ * ℓ) * g by group] at h1
      calc ℓ * ℓ = g * (g⁻¹ * (ℓ * ℓ) * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
  · refine ⟨ℓ⁻¹, ?_⟩
    have h1 : α * ℓ = ℓ * c * α := by
      calc α * ℓ = α * ℓ * α⁻¹ * α := by group
        _ = ℓ * c * α := by rw [h]
    calc ℓ⁻¹ * α * ℓ⁻¹⁻¹ = ℓ⁻¹ * (α * ℓ) := by group
      _ = ℓ⁻¹ * (ℓ * c * α) := by rw [h1]
      _ = c * α := by group
      _ = α * c := (hcc α hαV).symm

theorem conj_t_mem_V₀ {v : X} (hv : v ∈ 𝒱 ⊓ centralizer {z₁}) :
    t * v * t⁻¹ ∈ 𝒱 ⊓ centralizer {z₁} := by
  have htt : t * (t * z₁ * t⁻¹) * t⁻¹ = z₁ := by
    rw [show t * (t * z₁ * t⁻¹) * t⁻¹ = (t * t) * z₁ * (t * t)⁻¹ by group, hD.t_mul_t]
    group
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hD.fd.t_mem hv.1) (inv_mem hD.fd.t_mem), ?_⟩
  rw [mem_centralizer_singleton_iff]
  have h1 := hD.comm_z₂ hv
  calc t * v * t⁻¹ * z₁ = t * v * t⁻¹ * (t * (t * z₁ * t⁻¹) * t⁻¹) := by rw [htt]
    _ = t * (v * (t * z₁ * t⁻¹)) * t⁻¹ := by group
    _ = t * ((t * z₁ * t⁻¹) * v) * t⁻¹ := by rw [h1]
    _ = (t * (t * z₁ * t⁻¹) * t⁻¹) * (t * v * t⁻¹) := by group
    _ = z₁ * (t * v * t⁻¹) := by rw [htt]

theorem not_L2 (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁)
    (hlt : barOf (centralizer {z₁}) K₂ < layer (MBar z₁))
    (hsyl : IsSylowOf 2 (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ layer (MBar z₁))
      (layer (MBar z₁)))
    (hdih : GorensteinWalter.HasDihedralSylowTwo ↥(layer (MBar z₁))) : False := by
  obtain ⟨ℓ, hℓV, hℓ2, hℓn⟩ := hD.exists_ell hlt hsyl hdih
  have htt : t * (t * z₁ * t⁻¹) * t⁻¹ = z₁ := by
    rw [show t * (t * z₁ * t⁻¹) * t⁻¹ = (t * t) * z₁ * (t * t)⁻¹ by group, hD.t_mul_t]
    group
  have hz₂2 : t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = 1 := by
    rw [show t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = t * (z₁ * z₁) * t⁻¹ by group, hD.z₁_mul_z₁]
    group
  have hz₂z : ∀ g : X, g * z * g⁻¹ ≠ t * z₁ * t⁻¹ := by
    intro g hg
    apply hD.fd.not_conj_z (g⁻¹ * t)
    rw [show g⁻¹ * t * z₁ * (g⁻¹ * t)⁻¹ = g⁻¹ * (t * z₁ * t⁻¹) * g by group, ← hg]
    group
  have hz₁z : ∀ g : X, g * z * g⁻¹ ≠ z₁ := by
    intro g hg
    apply hD.fd.not_conj_z g⁻¹
    rw [← hg]
    group
  obtain ⟨g₂, hg₂⟩ := hD.exists_conj_alpha_mul hnβ hℓV hℓ2 hD.z₂_ne_one hz₂2
    (fun v hv => hD.comm_z₂ hv) hz₂z hℓn
  have hℓtV := hD.conj_t_mem_V₀ hℓV
  have hℓt2 : t * ℓ * t⁻¹ * (t * ℓ * t⁻¹) = z₁ := by
    rw [show t * ℓ * t⁻¹ * (t * ℓ * t⁻¹) = t * (ℓ * ℓ) * t⁻¹ by group, hℓ2, htt]
  have hℓtn : ∀ v ∈ 𝒱 ⊓ centralizer {z₁}, v * (t * ℓ * t⁻¹) * v⁻¹ = t * ℓ * t⁻¹ ∨
      v * (t * ℓ * t⁻¹) * v⁻¹ = t * ℓ * t⁻¹ * z₁ := by
    intro v hv
    have hv' : t⁻¹ * v * t ∈ 𝒱 ⊓ centralizer {z₁} := by
      have h1 := hD.conj_t_mem_V₀ hv
      rwa [show t * v * t⁻¹ = t⁻¹ * v * t by
        rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right hD.t_mul_t]] at h1
    have hconj : v * (t * ℓ * t⁻¹) * v⁻¹ = t * ((t⁻¹ * v * t) * ℓ * (t⁻¹ * v * t)⁻¹) * t⁻¹ := by
      group
    rcases hℓn _ hv' with h1 | h1 <;> rw [hconj, h1]
    · left; rfl
    · right
      conv_rhs => rw [← htt]
      group
  obtain ⟨g₁, hg₁⟩ := hD.exists_conj_alpha_mul hnβ hℓtV hℓt2 hD.z₁_ne_one hD.z₁_mul_z₁
    (fun v hv => mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hv).2) hz₁z hℓtn
  obtain ⟨g, -, -, hgα, -, -, hgX⟩ := hD.exists_conj_x hnβ
  obtain ⟨hfus, -, -⟩ := hD.fd.fusion hnβ
  have key : ∀ c : X, c ∈ closure {α, z₁, t * z₁ * t⁻¹} → c ≠ 1 →
      (∃ g' : X, g' * α * g'⁻¹ = α * c) → g⁻¹ * (α * c) * g = t * z := by
    rintro c hcX hc1 ⟨g', hg'⟩
    have hmem : α * c ∈ closure {α, z₁, t * z₁ * t⁻¹} := mul_mem (subset_closure (by simp)) hcX
    rw [← hgX] at hmem
    obtain ⟨x, hxX, hx⟩ := hmem
    have hx' : x = g⁻¹ * (α * c) * g := by
      have hx'' : g * x * g⁻¹ = α * c := hx
      rw [← hx'']
      group
    have hconj : (g⁻¹ * g' * g) * t * (g⁻¹ * g' * g)⁻¹ = x := by
      rw [hx', ← hg', ← hgα]
      group
    rcases hfus _ (by rw [hconj]; exact hxX) with h | h <;> rw [hconj] at h
    · exfalso
      apply hc1
      have h2 : α * c = α := by
        have h3 : g⁻¹ * (α * c) * g = t := by rw [← hx']; exact h
        calc α * c = g * (g⁻¹ * (α * c) * g) * g⁻¹ := by group
          _ = g * t * g⁻¹ := by rw [h3]
          _ = α := hgα
      exact mul_left_cancel (h2.trans (mul_one α).symm)
    · rw [← hx', h]
  have h1 := key z₁ (subset_closure (by simp)) hD.z₁_ne_one ⟨g₁, hg₁⟩
  have h2 := key (t * z₁ * t⁻¹) (subset_closure (by simp)) hD.z₂_ne_one ⟨g₂, hg₂⟩
  apply hD.fd.z₁_ne
  have h3 : α * z₁ = α * (t * z₁ * t⁻¹) := by
    calc α * z₁ = g * (g⁻¹ * (α * z₁) * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * (α * (t * z₁ * t⁻¹)) * g) * g⁻¹ := by rw [h1, h2]
      _ = α * (t * z₁ * t⁻¹) := by group
  exact mul_left_cancel h3

end Data415B

end CFSG.ComponentClassification.HarrisLit
