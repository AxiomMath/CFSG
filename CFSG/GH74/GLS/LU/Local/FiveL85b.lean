module

public import CFSG.GH74.GLS.LU.Local.FiveL85a

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L85b

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg3.z_inv_Y (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : ∀ y ∈ Y, z * y * z⁻¹ = y⁻¹ := by
  intro y hy
  have hu : u * y * u⁻¹ = y⁻¹ := c.b83.u_inv y (Subgroup.mem_sup_right hy)
  have hzu : y * (z * u) = (z * u) * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (c.b83.Y_syl.1 hy)
  have hu2 : u * u = 1 := c.hs.u_sq
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hu2' : u⁻¹ * u⁻¹ = 1 := by rw [hu']; exact hu2
  calc z * y * z⁻¹ = (z * u) * (u * y * u⁻¹) * (z * u)⁻¹ := by
        calc z * y * z⁻¹ = z * (u * u) * y * (u⁻¹ * u⁻¹) * z⁻¹ := by rw [hu2, hu2']; group
          _ = (z * u) * (u * y * u⁻¹) * (z * u)⁻¹ := by group
    _ = (z * u) * y⁻¹ * (z * u)⁻¹ := by rw [hu]
    _ = y⁻¹ := by
        have h1 : y⁻¹ * (z * u) = (z * u) * y⁻¹ := by
          calc y⁻¹ * (z * u) = (y⁻¹ * (z * u) * y) * y⁻¹ := by group
            _ = (y⁻¹ * (y * (z * u))) * y⁻¹ := by rw [hzu]; group
            _ = (z * u) * y⁻¹ := by group
        calc (z * u) * y⁻¹ * (z * u)⁻¹ = (y⁻¹ * (z * u)) * (z * u)⁻¹ := by rw [h1]
          _ = y⁻¹ := by group

omit [Finite G] in
theorem mem_of_inv_sq_mem {P : Subgroup G} {w : G} (h5 : w ^ 5 = 1) (h : w⁻¹ * w⁻¹ ∈ P) :
    w ∈ P := by
  have : w = ((w⁻¹ * w⁻¹)⁻¹) ^ 3 := by
    calc w = w ^ 5 * w := by rw [h5, one_mul]
      _ = ((w⁻¹ * w⁻¹)⁻¹) ^ 3 := by group
  rw [this]
  exact pow_mem (inv_mem h) 3

theorem Cfg3.Y_le_M (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    Y ≤ normalizer ((XB t X₁ : Subgroup G) : Set G) :=
  le_normalizer_of_commute (fun a ha b hb => (c.XX_comm b ((le_sup_right : XB t X₁ ≤ XX t X₁) hb) a ha).symm)

theorem Cfg3.Y_le_RR (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : Y ≤ RR t X₁ := by
  intro y hy
  have hyM : y ∈ RR t X₁ ⊔ K₁ ⊔ H := by rw [← c.N_X2_eq]; exact c.Y_le_M hy
  have hnormH : ∀ l ∈ H, ∀ e ∈ RR t X₁ ⊔ K₁, l * e * l⁻¹ ∈ RR t X₁ ⊔ K₁ := by
    intro l hl e he
    have hcj : cjL l (RR t X₁ ⊔ K₁) = RR t X₁ ⊔ K₁ := by
      rw [cjL_sup, cjL_eq_of_mem_normalizer (normalizer_le_normalizer_RR t X₁
        (c.H_le_normalizer_X2 hl)), (c.b66.H_normK l hl).1]
    have := mem_cjL_self (g := l) he
    rwa [hcj] at this
  have hnormK : ∀ k ∈ K₁, ∀ r ∈ RR t X₁, k * r * k⁻¹ ∈ RR t X₁ := by
    intro k hk r hr
    exact (Subgroup.mem_normalizer_iff.mp (c.K1_le_normalizer_RR hk) r).mp hr
  obtain ⟨e, he, h, hh, rfl⟩ := mem_sup_of_normalizes hnormH hyM
  obtain ⟨r, hr, k, hk, rfl⟩ := mem_sup_of_normalizes hnormK he
  have hzk : z * k = k * z := (c.hc.cz₁ hk).symm
  have hzh : z * h = h * z := ((c.b66.H_cent h hh).1).symm
  have hinv := c.z_inv_Y _ hy
  have hzr : z * r * z⁻¹ ∈ RR t X₁ :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_RR t X₁ c.z_mem_M) r).mp hr
  have h1 : z * (r * k * h) * z⁻¹ = (z * r * z⁻¹) * k * h := by
    calc z * (r * k * h) * z⁻¹ = (z * r * z⁻¹) * (z * k * z⁻¹) * (z * h * z⁻¹) := by group
      _ = (z * r * z⁻¹) * k * h := by
          rw [show z * k * z⁻¹ = k by rw [hzk]; group, show z * h * z⁻¹ = h by rw [hzh]; group]
  have h2 : (r * k * h)⁻¹ * (r * k * h)⁻¹ ∈ RR t X₁ := by
    have : (r * k * h)⁻¹ * (r * k * h)⁻¹ = (z * r * z⁻¹) * r⁻¹ := by
      calc (r * k * h)⁻¹ * (r * k * h)⁻¹ = (z * (r * k * h) * z⁻¹) * (r * k * h)⁻¹ := by rw [hinv]
        _ = (z * r * z⁻¹) * k * h * (r * k * h)⁻¹ := by rw [h1]
        _ = (z * r * z⁻¹) * r⁻¹ := by group
    rw [this]; exact mul_mem hzr (inv_mem hr)
  have h5 : (r * k * h) ^ 5 = 1 := c.b83.Y_ab.2 _ hy
  exact mem_of_inv_sq_mem h5 h2

theorem card_le_of_five_le {P C : Subgroup G} (hP : IsPGroup 5 ↥P) (hPC : P ≤ C)
    (hC : Nat.card ↥C = 28800) : Nat.card ↥P ≤ 25 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hdvd : Nat.card ↥P ∣ 28800 := hC ▸ Subgroup.card_dvd_of_le hPC
  rw [hn] at hdvd ⊢
  by_contra hlt
  have h3 : 3 ≤ n := by
    by_contra h
    have h' : n < 3 := Nat.lt_of_not_ge h
    interval_cases n <;> simp at hlt
  have : 5 ^ 3 ∣ 5 ^ n := pow_dvd_pow 5 h3
  have := this.trans hdvd
  omega

theorem Cfg2.card_Cu (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    Nat.card ↥(centralizer ({u} : Set G)) = 28800 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp c.hs.u_conj
  have : cjL g (centralizer ({z} : Set G)) = centralizer ({u} : Set G) := by
    ext x
    rw [mem_cjL, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← hg]
    constructor
    · intro h
      calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
        _ = (g * z * g⁻¹) * x := by group
    · intro h
      calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [h]
        _ = z * (g⁻¹ * x * g) := by group
  rw [← this, card_cjL]
  exact c.b82.card_C

theorem Cfg3.cjL_w₁_RR (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    cjL w₁ (RR t X₁) = RR t X₁ :=
  cjL_eq_of_mem_normalizer (c.K1_le_normalizer_RR c.b66.w₁_mem)

theorem Cfg3.card_Yw (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : Nat.card ↥(cjL w₁ Y) = 25 :=
  (card_cjL w₁ Y).trans c.b83.Y_card

theorem Cfg3.Yw_eq (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    cjL w₁ Y = centralizer ({u} : Set G) ⊓ RR t X₁ := by
  have hle : cjL w₁ Y ≤ centralizer ({u} : Set G) ⊓ RR t X₁ := by
    refine le_inf ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : (MulAut.conj w₁).toMonoidHom y = w₁ * y * w₁⁻¹ := by simp [MulAut.conj_apply]
      rw [hy']
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have h1 : y * (z * u) = (z * u) * y :=
        Subgroup.mem_centralizer_singleton_iff.mp (c.b83.Y_syl.1 hy)
      have h2 : w₁ * (z * u) * w₁⁻¹ = u := by
        have e : w₁ * (z * u) * w₁⁻¹ = (w₁ * z * w₁⁻¹) * (w₁ * u * w₁⁻¹) := by group
        rw [e, c.w₁_z, c.b66.w₁_u]
        calc z * (u * z) = (z * u) * z := by group
          _ = (u * z) * z := by rw [c.hs.zu_comm]
          _ = u * (z * z) := by group
          _ = u := by rw [c.hs.z_sq, mul_one]
      calc w₁ * y * w₁⁻¹ * u = w₁ * y * w₁⁻¹ * (w₁ * (z * u) * w₁⁻¹) := by rw [h2]
        _ = w₁ * (y * (z * u)) * w₁⁻¹ := by group
        _ = w₁ * ((z * u) * y) * w₁⁻¹ := by rw [h1]
        _ = (w₁ * (z * u) * w₁⁻¹) * (w₁ * y * w₁⁻¹) := by group
        _ = u * (w₁ * y * w₁⁻¹) := by rw [h2]
    · have h1 : cjL w₁ Y ≤ cjL w₁ (RR t X₁) := cjL_mono w₁ c.Y_le_RR
      rwa [c.cjL_w₁_RR] at h1
  have hP : IsPGroup 5 ↥(centralizer ({u} : Set G) ⊓ RR t X₁ : Subgroup G) :=
    (RR_pGroup t X₁).to_le inf_le_right
  have hcard := card_le_of_five_le hP (inf_le_left : centralizer ({u} : Set G) ⊓ RR t X₁ ≤ _)
    c.card_Cu
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [c.card_Yw]; exact hcard)

end L85b

end CFSG.GH74.GLS.LU.Local.Five
