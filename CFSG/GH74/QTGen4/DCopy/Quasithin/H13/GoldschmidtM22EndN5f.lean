module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN4d
public import CFSG.Quasithin.H13.GoldschmidtM22EndN5e
public import CFSG.Quasithin.H13.GoldschmidtM22EndS3b

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace KData

variable {g : G} {D : Subgroup G} (hk : KData T L V g D) (h : Hyp6Sec2 G T M L V)
  (P : PsiData T L V 3) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)

include hk P h hZ in

theorem exists_x_F4 (h6210 : Stmt6_2_10_F4) :
    ∃ (a : ↥(HH T)) (x : G), (a : G) ∈ V ∧ (a : G) ∉ CHU T L V ∧
      P.ψ ⟨g, hk.g_mem⟩ * P.ψ a ≠ P.ψ a * P.ψ ⟨g, hk.g_mem⟩ ∧ (a : G) ^ 2 = 1 ∧
      x ∈ V ⊔ conjSubgroup V g ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧ (a : G) * x * (a : G)⁻¹ = x⁻¹ ∧
      x ∉ Subgroup.normalizer (V : Set G) := by
  obtain ⟨a, haV, haC, hg⟩ := exists_a_noncomm_F4 hk h P hZ h6210
  obtain ⟨hτ, hNa⟩ := P.swap_norm a haV haC
  have hτ2 : (P.ψ a).support.card = 2 := Equiv.Perm.card_support_eq_two.mpr hτ
  set g' : ↥(HH T) := ⟨g, hk.g_mem⟩ with hg'
  have ha2 : (a : G) ^ 2 = 1 := h.toHyp611.isElemAbelian.2 a haV
  have haa : (a : G) * (a : G) = 1 := by rw [← pow_two]; exact ha2
  set b' : ↥(HH T) := g'⁻¹ * a * g' with hb'
  set b : G := (b' : G) with hb
  have hbVg : b ∈ conjSubgroup V g := by
    refine mem_conjSubgroup_iff.mpr ?_
    have e : (g : G) * b * (g : G)⁻¹ = (a : G) := by
      simp [hb, hb', hg']
      group
    rw [e]
    exact haV
  have hbb : b * b = 1 := by
    have : b * b = (g : G)⁻¹ * ((a : G) * (a : G)) * g := by simp [hb, hb', hg']; group
    rw [this, haa]
    group
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  set x₀' : ↥(HH T) := a * b' with hx₀'
  set x₀ : G := (x₀' : G) with hx₀
  have hx₀K : x₀ ∈ V ⊔ conjSubgroup V g := Subgroup.mul_mem_sup haV hbVg
  have hinv : (a : G) * x₀ * (a : G)⁻¹ = x₀⁻¹ := by
    have e : x₀ = (a : G) * b := rfl
    calc (a : G) * x₀ * (a : G)⁻¹ = ((a : G) * (a : G)) * b * (a : G)⁻¹ := by rw [e]; group
      _ = b * (a : G)⁻¹ := by rw [haa, one_mul]
      _ = b⁻¹ * (a : G)⁻¹ := by rw [hbinv]
      _ = x₀⁻¹ := by rw [e, mul_inv_rev]

  have hψb : P.ψ b' = (P.ψ g')⁻¹ * P.ψ a * P.ψ g' := by
    rw [hb', map_mul, map_mul, map_inv]
  have hψx₀ : P.ψ x₀' = P.ψ a * ((P.ψ g')⁻¹ * P.ψ a * P.ψ g') := by
    rw [hx₀', map_mul, hψb]
  obtain ⟨hπ3, hπ1⟩ := perm3_prod_order _ _ hτ2 hg
  have hπ4 := perm3_prod_pow_four _ _ hτ2 hg
  have hπnc := perm3_prod_noncomm _ _ hτ2 hg

  have hx₀3D : x₀ ^ 3 ∈ D := by
    have h1 : P.ψ (x₀' ^ 3) = 1 := by rw [map_pow, hψx₀]; exact hπ3
    have h2 : x₀ ^ 3 ∈ CHU T L V := (P.ker _).mp h1
    rw [hk.D_eq]
    exact ⟨(V ⊔ conjSubgroup V g).pow_mem hx₀K 3, h2⟩
  have hx₀12 : x₀ ^ 12 = 1 := by
    have := hk.pow_four_eq_one hZ hx₀3D
    rw [← pow_mul] at this
    exact this
  refine ⟨a, x₀ ^ 4, haV, haC, hg, ha2, (V ⊔ conjSubgroup V g).pow_mem hx₀K 4, ?_, ?_, ?_, ?_⟩
  · rw [← pow_mul]
    exact hx₀12
  · intro hx1
    have h1 : P.ψ (x₀' ^ 4) = 1 := by
      have : (x₀' ^ 4 : ↥(HH T)) = 1 := Subtype.ext (by simpa using hx1)
      rw [this, map_one]
    rw [map_pow, hψx₀, hπ4] at h1
    exact hπ1 h1
  · calc (a : G) * x₀ ^ 4 * (a : G)⁻¹ = ((a : G) * x₀ * (a : G)⁻¹) ^ 4 := (conj_pow).symm
      _ = (x₀ ^ 4)⁻¹ := by rw [hinv, inv_pow]
  · intro hN
    have hc := (hNa (x₀' ^ 4)).mp (by simpa using hN)
    rw [map_pow, hψx₀, hπ4] at hc
    exact hπnc hc

end KData

end CFSG.Quasithin.H13.GM22
