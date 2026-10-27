module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5T
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem516

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Setting

variable {G : Type} [Group G]

namespace Setting518D5

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D D₃ D₅ : Subgroup G} {n : ℕ}
  (s : Setting518D5 G T M L V H B D D₃ D₅ n)
include s

theorem normalizer_le_Mp_F4 (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first_F4) {R : Subgroup G}
    (hR1 : R ≠ ⊥) (hRT : R ≤ T) (hTKR : T ⊓ oTwoUpper H ≤ R)
    (hTR : T ≤ Subgroup.normalizer (R : Set G)) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  have hh := h.hyp.toHyp5_0_1
  have hR2 : IsPGroup 2 R := hh.sylow.1.to_le hRT
  have hO : pCoreOf 2 (Subgroup.normalizer (R : Set G)) ≠ ⊥ := by
    intro h0
    apply hR1
    have hle : R ≤ pCoreOf 2 (Subgroup.normalizer (R : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hR2
    rw [h0] at hle
    exact le_bot_iff.mp hle
  have hM₀ : InH T (Subgroup.normalizer (R : Set G)) := ⟨hTR, hO⟩
  have hu : ∃ N : Subgroup G, IsUniqueMaxOver H T N := by
    obtain ⟨S, hS⟩ := exists_sylow_coe_eq hh.sylow
    have hstar : IsHStar (S : Subgroup G) M H := hS ▸ h.hyp.hStar
    have hTM : (S : Subgroup G) ≤ M := hS ▸ hh.T_le
    exact ⟨H ⊓ M, hS ▸ hstar.isUniqueMaxOver S hTM⟩
  have hTS : IsSylowTwoOf T (oTwoUpper H ⊔ T) := hh.isSylowTwoOf le_sup_right
  have hRS : IsSylowTwoOf R (oTwoUpper H ⊔ R) :=
    isSylowTwoOf_sup_of_inf_le hRT h.T_le_Mp (by rw [inf_comm]; exact hTKR) hTS
  obtain ⟨R₀, hR₀1, hR₀R, hR₀N⟩ := h311 G T hh.simple hh.nonabelian hh.qtke hh.sylow _ H R
    hM₀ h.hyp.hStar.1 hu hR1 hRT hRS le_rfl
  have hloc : IsTwoLocal (Subgroup.normalizer (R₀ : Set G)) := ⟨R₀, hR₀1, hR2.to_le hR₀R, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hHM' : H ≤ M' := le_sup_right.trans (hR₀N.trans hle)
  have hM'eq := (h.isUniqueM_F4 h5114).2 M' ⟨hM', hHM'⟩
  rw [← hM'eq]
  exact le_sup_left.trans (hR₀N.trans hle)

end Setting518D5

end Setting

end CFSG.Quasithin.H13
