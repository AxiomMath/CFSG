module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN3e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN3c

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace PsiData

variable (P : PsiData T L V 3) (h : Hyp6Sec2 G T M L V)

include P h in

theorem kData_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h621 : Stmt6_2_1_F4)
    (h626 : Stmt6_2_6_F4) (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) :
    ∃ (g : G) (D : Subgroup G), KData T L V g D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, g, haV, haC, hg⟩ := P.exists_pair_F4 h hZ h6210
  have hτ2 : (P.ψ a).support.card = 2 :=
    Equiv.Perm.card_support_eq_two.mpr (P.swap_norm a haV haC).1
  have hg' : P.ψ g * P.ψ a ≠ P.ψ a * P.ψ g := fun hc => hg hc
  have hc2 := P.case2_F4 h hZ h621 h626 h6210 h6211 a g haV haC hg
  have hK := P.KK_eq_sup a g haV haC hg
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, Y = V ⊔ conjSubgroup V (g : G) := ⟨_, rfl⟩
  have hex : ∃ D : Subgroup G, D ≤ Y ∧ Y ≤ Subgroup.normalizer (D : Set G) ∧
      E2.IsExtraspecialPlus 2 D ∧ ∃ φ : ↥Y →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
        φ.ker = D.subgroupOf Y := by
    subst hY
    exact hc2.exists_D
  obtain ⟨D, hDY, hYN, hext, φ, hφs, hφk⟩ := hex
  have hK' : KK T V = Y := hK.trans hY.symm
  have hCHU : CHU T L V = pCoreOf 2 (HH T) := (h6212 G T M L V h).2.2
  have : CFSG.IsExtraspecial 2 ↥D := hext.1
  have hpD : IsPGroup 2 ↥D := CFSG.IsExtraspecial.isPGroup 2 ↥D
  have hKH : Y ≤ HH T := by
    rw [← hK']
    exact KK_le_HH h hZ
  have hHY : HH T ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← hK']
    exact le_normalizer_conjClosure V (HH T)
  have hDH : D ≤ HH T := hDY.trans hKH

  have hDpc : D = pCoreOf 2 Y := by
    refine le_antisymm (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDY hYN hpD) ?_
    intro y hy
    have hyY : y ∈ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y hy
    set y' : ↥Y := ⟨y, hyY⟩ with hy'
    have h1 : φ y' = 1 := by
      refine perm3_normal_two _ fun κ => ?_
      obtain ⟨x, rfl⟩ := hφs κ
      have hxy : (x : G) * y * (x : G)⁻¹ ∈ pCoreOf 2 Y := by
        have := Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y x.2) y
        exact this.mp hy
      have hw : y * ((x : G) * y * (x : G)⁻¹) ∈ pCoreOf 2 Y := (pCoreOf 2 Y).mul_mem hy hxy
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y ⟨_, hw⟩
      have hk' : (y' * (x * y' * x⁻¹)) ^ 2 ^ k = 1 := by
        apply Subtype.ext
        simpa using congrArg Subtype.val hk
      have := congrArg φ hk'
      simp only [map_pow, map_mul, map_inv, map_one] at this
      exact perm3_sq_of_pow_two_pow _ k this
    have h2 : y' ∈ φ.ker := h1
    rw [hφk, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hHD : HH T ≤ Subgroup.normalizer (D : Set G) := by
    rw [hDpc]
    exact hHY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)

  have hDeq : D = Y ⊓ CHU T L V := by
    refine le_antisymm (le_inf hDY ?_) ?_
    · rw [hCHU]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDH hHD hpD
    · rw [hDpc]
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (HH T)).to_le (inf_le_right.trans hCHU.le))
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y
      have h2 := Subgroup.mem_normalizer_iff.mp (HH_le_normalizer_CHU h hZ (hKH hx)) y
      simp only [Subgroup.mem_inf]
      rw [h1, h2]

  have hZVg : quasithinOmegaOneCenter T ≤ V ⊓ conjSubgroup V (g : G) := by
    refine le_inf (Z_le_V h hZ) fun z hz => ?_
    refine mem_conjSubgroup_iff.mpr ?_
    have : (g : G) * z * (g : G)⁻¹ = z := by
      rw [Z_central T g.2 hz]
      group
    rw [this]
    exact Z_le_V h hZ hz
  have hinter : V ⊓ conjSubgroup V (g : G) = quasithinOmegaOneCenter T :=
    (Subgroup.eq_of_le_of_card_ge hZVg (by rw [hc2.card_inter, hZ])).symm
  have hZY : quasithinOmegaOneCenter T ≤ Y := by
    rw [hY]
    exact hZVg.trans (inf_le_left.trans le_sup_left)

  have hZD : quasithinOmegaOneCenter T ≤ D := by
    intro z hz
    set z' : ↥Y := ⟨z, hZY hz⟩ with hz'
    have h1 : φ z' = 1 := by
      refine perm3_center_trivial _ fun t => ?_
      obtain ⟨x, rfl⟩ := hφs t
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Z_central T (hKH x.2) hz)
    have h2 : z' ∈ φ.ker := h1
    rw [hφk, Subgroup.mem_subgroupOf] at h2
    exact h2

  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (D : Set G) := by
    intro z hz
    refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
    exact Z_central T (hDH hd) hz
  have hcenter : D ⊓ Subgroup.centralizer (D : Set G) = quasithinOmegaOneCenter T := by
    refine (Subgroup.eq_of_le_of_card_ge (le_inf hZD hZC) (le_of_eq ?_)).symm
    rw [card_inf_centralizer_eq_card_center, CFSG.IsExtraspecial.center_order_p 2 ↥D, hZ]

  have hHeq : ∀ x ∈ HH T, ∃ k ∈ Y, ∃ c ∈ CHU T L V, x = k * c := by
    intro x hx
    have key : ∀ k : ↥(HH T), (k : G) ∈ Y → P.ψ k = P.ψ ⟨x, hx⟩ →
        ∃ k' ∈ Y, ∃ c ∈ CHU T L V, x = k' * c := by
      intro k hk hψ
      refine ⟨(k : G), hk, (((k⁻¹ * ⟨x, hx⟩ : ↥(HH T))) : G), (P.ker _).mp ?_, ?_⟩
      · rw [map_mul, map_inv, hψ, inv_mul_cancel]
      · simp
    have haY : (a : G) ∈ Y := by
      rw [hY]
      exact Subgroup.mem_sup_left haV
    have hcY : ((g⁻¹ * a * g : ↥(HH T)) : G) ∈ Y := by
      rw [hY]
      refine Subgroup.mem_sup_right (mem_conjSubgroup_iff.mpr ?_)
      have e : (g : G) * ((g : G)⁻¹ * (a : G) * (g : G)) * (g : G)⁻¹ = (a : G) := by group
      show (g : G) * ((g : G)⁻¹ * (a : G) * (g : G)) * (g : G)⁻¹ ∈ V
      rw [e]
      exact haV
    rcases perm3_gen_conj (P.ψ a) (P.ψ g) (P.ψ ⟨x, hx⟩) hτ2 hg' with h0 | h1 | h2 | h3 | h4 | h5
    · exact key 1 (by simp) (by rw [map_one, h0])
    · exact key a haY h1.symm
    · exact key (g⁻¹ * a * g) hcY (by rw [map_mul, map_mul, map_inv]; exact h2.symm)
    · exact key (a * (g⁻¹ * a * g)) (Y.mul_mem haY hcY)
        (by rw [map_mul, map_mul, map_mul, map_inv]; exact h3.symm)
    · exact key ((g⁻¹ * a * g) * a) (Y.mul_mem hcY haY)
        (by rw [map_mul, map_mul, map_mul, map_inv]; exact h4.symm)
    · exact key (a * (g⁻¹ * a * g) * a) (Y.mul_mem (Y.mul_mem haY hcY) haY)
        (by rw [map_mul, map_mul, map_mul, map_mul, map_inv]; exact h5.symm)
  subst hY
  exact ⟨(g : G), D, { g_mem := g.2
                       g_not_mem := fun hN => hg (((P.swap_norm a haV haC).2 g).mp hN)
                       K_eq := hK'
                       H_le_normalizer_K := hHY
                       K_le_HH := hKH
                       D_le_K := hDY
                       K_le_normalizer_D := hYN
                       extra := hext
                       quot := ⟨φ, hφs, hφk⟩
                       H_le_normalizer_D := hHD
                       D_eq := hDeq
                       inter_eq := hinter
                       Z_le_D := hZD
                       center_eq := hcenter
                       H_eq := hHeq
                       case2 := hc2 }⟩

end PsiData

end CFSG.Quasithin.H13.GM22
