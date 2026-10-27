module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseBS5b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBSetup
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBCover
public section
namespace CFSG.Quasithin.H13.GM22
open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin
variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
namespace BCtx_F4
variable {T M L V : Subgroup G} {g : G} {D : Subgroup G} (c : BCtx_F4 T M L V g D)
include c in
theorem V_le_L : V ≤ L := by
  have hVT : V ≤ Subgroup.normalizer (L : Set G) := fun v hv =>
    c.N_le_normalizer_L (c.T_le_N (c.h.toHyp611.le_T hv))
  have h1 : ⁅V, L⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have h2 : v * l * v⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hVT hv) l).mp hl
    have : v * l * v⁻¹ * l⁻¹ ∈ L := L.mul_mem h2 (L.inv_mem hl)
    simpa [commutatorElement_def] using this
  rw [c.h.comm_eq] at h1
  exact h1
include c in
theorem sign_rho_L : ∀ l ∈ L, Equiv.Perm.sign (c.ρ l) = 1 :=
  c.ρ.sign_eq_one_of_mem c.L_le_N c.L_perfect
include c in
theorem exists_rho_L : ∀ σ ∈ alternatingGroup (Fin 5), ∃ l ∈ L, c.ρ l = σ :=
  c.ρ.exists_eq_of_alternating c.L_le_N c.N_le_normalizer_L c.L_perfect
    c.h.natural.not_le_centralizer
include c in
theorem exists_a₁ : ∃ a ∈ conjSubgroup V g ⊓ CHU T L V, a ∈ Subgroup.normalizer (V : Set G) ∧
    Equiv.Perm.sign (c.ρ a) = -1 ∧ a ^ 2 = 1 := by
  obtain ⟨a, haX, hs⟩ := c.ρ.exists_odd_of_not_le c.L_le_N c.exists_rho_L
    c.hk.kData.case2.not_le
  obtain ⟨haVg, haN⟩ := Subgroup.mem_inf.mp haX
  have h1 : a ∈ conjSubgroup V g ⊓ CHU T L V := by
    rw [← c.hk.kData.conj_inf_normalizer_eq_F4 c.h c.P c.hZ c.hl.h6210 c.hl.h6211]
    exact haX
  refine ⟨a, h1, haN, hs, ?_⟩
  have hv : g * a * g⁻¹ ∈ V := mem_conjSubgroup_iff.mp haVg
  have h2 := c.h.toHyp611.isElemAbelian.2 _ hv
  rw [conj_pow] at h2
  simpa using h2
include c in
theorem T_conj_D {t d : G} (ht : t ∈ T) (hd : d ∈ D) : t * d * t⁻¹ ∈ D :=
  (Subgroup.mem_normalizer_iff.mp (c.hk.kData.H_le_normalizer_D (T_le_HH T ht)) d).mp hd
include c in
theorem exists_T_L_of_even {t : G} (ht : t ∈ T) (hs : Equiv.Perm.sign (c.ρ t) = 1) :
    ∃ l ∈ T ⊓ L, c.ρ l = c.ρ t := by
  obtain ⟨l, hl, hlt⟩ := c.exists_rho_L (c.ρ t) (Equiv.Perm.mem_alternatingGroup.mpr hs)
  have hq : t⁻¹ * l ∈ Subgroup.centralizer (V : Set G) :=
    (c.ρ.eq_iff (c.T_le_N ht) (c.L_le_N hl)).mp hlt.symm
  refine ⟨l, ⟨?_, hl⟩, hlt⟩
  have : t * (t⁻¹ * l) ∈ T := T.mul_mem ht (c.Q_le_T hq)
  simpa using this
include c in
theorem isPGroup_range : IsPGroup 2 (c.ρ.restr c.T_le_N).range := by
  rintro ⟨_, x, rfl⟩
  obtain ⟨k, hk⟩ := c.h.sylow.1 x
  exact ⟨k, Subtype.ext (by simpa [← map_pow] using congrArg (c.ρ.restr c.T_le_N) hk)⟩
include c in
theorem card_rho_T : Nat.card (c.ρ.restr c.T_le_N).range = 8 := by
  have hdvd : Nat.card (c.ρ.restr c.T_le_N).range ∣ 8 :=
    card_dvd_eight_of_isPGroup _ c.isPGroup_range
  have hN : Nat.card (Subgroup.centralizer (V : Set G)) * 120 =
      Nat.card (Subgroup.normalizer (V : Set G)) := by
    have h1 := c.ρ.card_inf_mul_card_range (le_refl (Subgroup.normalizer (V : Set G)))
    rw [inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)] at h1
    have : (c.ρ.restr (le_refl (Subgroup.normalizer (V : Set G)))).range = ⊤ :=
      MonoidHom.range_eq_top.mpr fun σ => by
        obtain ⟨x, hx, hσ⟩ := c.ρ.exists_eq σ
        exact ⟨⟨x, hx⟩, by rw [PermRho.restr_apply]; exact hσ⟩
    rw [this, Subgroup.card_top, card_perm_fin_five] at h1
    exact h1
  have hT : Nat.card (Subgroup.centralizer (V : Set G)) * Nat.card (c.ρ.restr c.T_le_N).range =
      Nat.card T := by
    have h1 := c.ρ.card_inf_mul_card_range c.T_le_N
    rwa [inf_eq_right.mpr c.Q_le_T] at h1
  have hidx : (T.relIndex (Subgroup.normalizer (V : Set G))) * Nat.card T =
      Nat.card (Subgroup.normalizer (V : Set G)) := by
    have h1 := Subgroup.relIndex_mul_card (H := T) (K := Subgroup.normalizer (V : Set G))
    rwa [inf_eq_left.mpr c.T_le_N] at h1
  have hodd : ¬ 2 ∣ T.relIndex (Subgroup.normalizer (V : Set G)) := by
    rw [c.hk.normalizer_eq]
    exact c.h.faithful.1.2.2.1
  have hQpos : 0 < Nat.card (Subgroup.centralizer (V : Set G)) := Nat.card_pos
  have h120 : T.relIndex (Subgroup.normalizer (V : Set G)) *
      Nat.card (c.ρ.restr c.T_le_N).range = 120 := by
    have h2 : Nat.card (Subgroup.centralizer (V : Set G)) *
        (T.relIndex (Subgroup.normalizer (V : Set G)) *
          Nat.card (c.ρ.restr c.T_le_N).range) =
        Nat.card (Subgroup.centralizer (V : Set G)) * 120 := by
      rw [hN, ← hidx, ← hT]
      ring
    exact Nat.eq_of_mul_eq_mul_left hQpos h2
  have hle : Nat.card (c.ρ.restr c.T_le_N).range ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card (c.ρ.restr c.T_le_N).range := Nat.card_pos
  generalize Nat.card (c.ρ.restr c.T_le_N).range = r at *
  generalize T.relIndex (Subgroup.normalizer (V : Set G)) = i at *
  interval_cases r <;> omega
include c in
theorem exists_noncomm {a : G} (haT : a ∈ T) (has : Equiv.Perm.sign (c.ρ a) = -1)
    (ha2 : c.ρ a * c.ρ a = 1) :
    ∃ t ∈ T ⊓ L, c.ρ t * c.ρ a ≠ c.ρ a * c.ρ t := by
  by_contra hcon
  push Not at hcon
  have haN := c.T_le_N haT
  have heven : ∀ t ∈ T, Equiv.Perm.sign (c.ρ t) = 1 → c.ρ t * c.ρ a = c.ρ a * c.ρ t := by
    intro t ht hs
    obtain ⟨l, hl, hlt⟩ := c.exists_T_L_of_even ht hs
    rw [← hlt]
    exact hcon l hl
  have hall : ∀ t ∈ T, c.ρ a * c.ρ t = c.ρ t * c.ρ a := by
    intro t ht
    rcases Int.units_eq_one_or (Equiv.Perm.sign (c.ρ t)) with hs | hs
    · exact (heven t ht hs).symm
    · have hat : a * t ∈ T := T.mul_mem haT ht
      have hs' : Equiv.Perm.sign (c.ρ (a * t)) = 1 := by
        rw [c.ρ.apply_mul haN (c.T_le_N ht), map_mul, has, hs]
        rfl
      have h1 := heven (a * t) hat hs'
      rw [c.ρ.apply_mul haN (c.T_le_N ht)] at h1
      have h2 : c.ρ a * c.ρ t * c.ρ a = c.ρ t := by
        rw [h1, ← mul_assoc, ha2, one_mul]
      calc c.ρ a * c.ρ t = c.ρ a * c.ρ t * (c.ρ a * c.ρ a) := by rw [ha2, mul_one]
        _ = (c.ρ a * c.ρ t * c.ρ a) * c.ρ a := by rw [mul_assoc (c.ρ a * c.ρ t)]
        _ = c.ρ t * c.ρ a := by rw [h2]
  obtain ⟨x, y, hxy, hτ⟩ := perm5_isSwap_of_odd_involution ha2 has
  have hle : (c.ρ.restr c.T_le_N).range ≤
      Subgroup.centralizer ({c.ρ a} : Set (Equiv.Perm (Fin 5))) := by
    rintro _ ⟨t, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [PermRho.restr_apply]
    exact hall t t.2
  have hd := Subgroup.card_dvd_of_le hle
  rw [c.card_rho_T, hτ, card_centralizer_swap x y hxy] at hd
  norm_num at hd
end BCtx_F4
end CFSG.Quasithin.H13.GM22
