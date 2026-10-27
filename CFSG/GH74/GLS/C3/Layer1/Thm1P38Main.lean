module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P38Gen
public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RStmt

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P38

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1

theorem thm1_L38_of_rel
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hP31s : B_thm1_P31s_rel) (hP31c : B_thm1_P31c_rel) (h35 : B_thm1_L35_rel)
    (h36 : B_thm1_L36_rel) (h37 : B_thm1_L37_rel) : B_thm1_L38_rel := by
  intro G _ _ hG hNo x y K T V W f z cfg hVW S a hS hTS haS haN haT ha2 h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f', hf'3, hf'mem, hspec⟩ := exists_special cfg.fmax cfg.mem
  have hcard : twoPartCard (centralizer ({f'} : Set G)) = Nat.card ↥V := by
    have h1 := hf'3.2 x y K f cfg.fmax.1
    have h2 := cfg.fmax.2 x y K f' hf'3.1
    have h3 : twoPartCard (centralizer ({f} : Set G)) = Nat.card ↥V := cfg.sylowV.card_eq.symm
    omega
  have hCT : IsPGroup 2 ↥(T ⊓ centralizer ({f'} : Set G)) :=
    cfg.setup.sylowT.isPGroup.to_inf_left
  obtain ⟨V', hV'le, hV'N, hV'p, hV'idx⟩ :=
    P34.exists_sylow_ge (N := centralizer ({f'} : Set G)) inf_le_right hCT
  have hV' : IsSylowOf 2 V' (centralizer ({f'} : Set G)) :=
    isSylowOf_iff.2 ⟨hV'N, hV'p, hV'idx⟩
  obtain ⟨W', hW'le, -, hW'p, hW'idx⟩ :=
    P34.exists_sylow_ge (N := (⊤ : Subgroup G)) le_top hV'.isPGroup
  have hW' : IsSylowOf 2 W' ⊤ := isSylowOf_iff.2 ⟨le_top, hW'p, hW'idx⟩
  have cfg' : Cfg3 x y K T V' W' f' z :=
    ⟨hf'3, cfg.setup, hf'mem, cfg.z_mem, hV', fun t ht hc => hV'le ⟨ht, mem_centralizer_singleton_iff.2 hc.symm⟩, hW', hW'le⟩
  have hV'W' : V' ≠ W' := by
    intro h
    have hltVW : Nat.card ↥V < Nat.card ↥W := by
      by_contra hge
      push Not at hge
      exact hVW (Subgroup.eq_of_le_of_card_ge cfg.V_le_W hge)
    have h1 : Nat.card ↥V' = Nat.card ↥V := by
      rw [hV'.card_eq]
      exact hcard
    have h2 : Nat.card ↥W' = Nat.card ↥W := by
      rw [hW'.card_eq, cfg.sylowW.card_eq]
    rw [h] at h1
    omega
  have E : Env37 x y K T V' W' f' z :=
    env37_of_rel h2hb h102 hL34 hP31s hP31c h35 hG hNo cfg' hV'W' h5
  obtain ⟨⟨hJa, hJb⟩, hJc, hJd⟩ := h37 G hG hNo x y K T V' W' f' z cfg' hspec hV'W' h5
  have D : L37Data x K T f' z := ⟨hJa, hJb, hJc, hJd⟩
  have hle : Nat.card ↥V' ≤ Nat.card ↥T := by
    rcases h36 G hG hNo x y K T V' W' f' z cfg' h5 with h | h
    · exact absurd h hV'W'
    · exact h
  have hnc : ¬ ∀ t ∈ T, t * f' = f' * t := E.not_central_f D hle hS hTS haS haN haT ha2
  have hlt : Nat.card ↥T < twoPartCard (centralizer ({z} : Set G)) :=
    Env37.lt_twoPart_of_ssup hS hTS haS haT (fun t ht => E.hzc t ht) (by
      have := E.normalizes_z D a haN
      calc a * z = (a * z * a⁻¹) * a := by group
        _ = z * a := by rw [this])
  have hax : a * x * a⁻¹ = x * z := E.a_x_conj D hnc hS hTS haS haN haT ha2
  exact ⟨⟨E.zCenter_T_eq hnc, E.card_T_eq D hnc⟩,
    ⟨E.hgen D hle hlt hax, E.not_normal_P₀ D hle hS hTS haS haN haT ha2⟩,
    ⟨E.normalizer_S_eq D hnc hS hTS haS haN haT ha2, hax⟩⟩

end CFSG.GH74.GLS.C3.Layer1.Thm1P38
