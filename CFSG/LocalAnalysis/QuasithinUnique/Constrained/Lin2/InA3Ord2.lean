module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Inv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Orders

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

namespace Lin2Hyp

section Ord

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem S_le_normalizer_U : S ≤ Subgroup.normalizer (blockU L : Set G) := fun s hs => by
  have := hcfg.H_le_normalizer_Q (hcfg.S_le_H hs)
  rwa [← E.UQ hcfg] at this

theorem R_le_normalizer_U : thompsonJ S ≤ Subgroup.normalizer (blockU L : Set G) :=
  (thompsonJ_le_self S).trans (E.S_le_normalizer_U hcfg)

theorem R_le_normalizer_Z {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) :
    thompsonJ S ≤ Subgroup.normalizer (Z : Set G) := fun _ hc =>
  Subgroup.centralizer_le_normalizer (Z : Set G) (lin2Z_centralized E.h16 hcfg hZ hc)

theorem conj_involution_mem {s x : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1)
    (hx : x ∈ T) :
    x * s * x⁻¹ ∈ S ∧ x * s * x⁻¹ ∉ thompsonJ S ∧ (x * s * x⁻¹) ^ 2 = 1 := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp (E.TnS hcfg hx) s).mp hs, fun h => hsR ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (E.TnR hcfg hx) s).mpr h
  · have : (x * s * x⁻¹) ^ 2 = x * s ^ 2 * x⁻¹ := by simp only [pow_two]; group
    rw [this, hs2]; simp

theorem card_Z_inf_centralizer {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) {s : G}
    (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) :
    Nat.card (Z ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) = 2 ^ (n / 2) := by
  obtain ⟨f₀, -, -, -, -, hconj, hcZ, -⟩ := E.exists_f₀ hcfg
  obtain ⟨c, hc, rfl⟩ := hconj s hs hsR hs2
  rw [card_inf_centralizer_conj (E.R_le_normalizer_Z hcfg hZ hc), hZ]
  exact hcZ

theorem card_R_inf_centralizer {s : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) :
    (centerOf L = ⊥ →
      Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) =
        2 ^ (3 * n / 2)) ∧
    (centerOf L ≠ ⊥ →
      Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) = 2 ^ (2 * n)) := by
  obtain ⟨f₀, -, -, -, -, hconj, -, hR1, hR2, -⟩ := E.exists_f₀ hcfg
  obtain ⟨c, hc, rfl⟩ := hconj s hs hsR hs2
  rw [card_inf_centralizer_conj (Subgroup.le_normalizer hc)]
  exact ⟨hR1, hR2⟩

theorem card_U : Nat.card (blockU L) = 2 ^ (2 * n) * Nat.card (centerOf L) := by
  rw [lin2_card_U hcfg.lin2, blockZ_eq_centerOf hcfg.charTwo_L (E.OL hcfg)]

theorem card_centerOf_L (hc : centerOf L ≠ ⊥) : Nat.card (centerOf L) = 2 ^ n := by
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  rcases (E.ZLcases hcfg x hx hxS).2 with h | ⟨-, h, -⟩
  · exact absurd h hc
  · exact h

theorem card_conjR_U_inf_centralizer {s x : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S)
    (hs2 : s ^ 2 = 1) (hx : x ∈ T) :
    Nat.card (conjR (blockU L) x ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) =
      Nat.card (blockU L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) := by
  obtain ⟨hs'S, hs'R, hs'2⟩ := E.conj_involution_mem hcfg hs hsR hs2 hx
  obtain ⟨f₀, -, -, -, -, hconj, -⟩ := E.exists_f₀ hcfg
  rw [conjR_inf_centralizer, card_conjR]
  obtain ⟨c₁, hc₁, hc₁s⟩ := hconj s hs hsR hs2
  obtain ⟨c₂, hc₂, hc₂s⟩ := hconj _ hs'S hs'R hs'2
  have hcc : (c₁⁻¹ * c₂)⁻¹ * s * (c₁⁻¹ * c₂) = x * s * x⁻¹ := by
    rw [← hc₂s, ← hc₁s]; group
  rw [← hcc]
  exact card_inf_centralizer_conj
    (E.R_le_normalizer_U hcfg ((thompsonJ S).mul_mem ((thompsonJ S).inv_mem hc₁) hc₂))

theorem U_s_card {s x : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) (hx : x ∈ T)
    (hxS : x ∉ S) :
    Nat.card (blockU L) =
        Nat.card (blockU L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) ^ 2 ∧
      ((blockU L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) *
          ((conjR (blockU L) x ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) =
        ((thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) ∧
      Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) *
          Nat.card (centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) =
        Nat.card (blockU L) := by
  set R := thompsonJ S with hR
  set U := blockU L with hU
  set C := Subgroup.centralizer ({s} : Set G) with hC
  obtain ⟨hRU', hUV⟩ := E.RUU hcfg hx hxS
  have hRU : R = U ⊔ conjR U x := hRU'
  obtain ⟨hUe, -, -⟩ := E.elemU hcfg hx hxS
  have hsU : s ∈ Subgroup.normalizer (U : Set G) := E.S_le_normalizer_U hcfg hs
  obtain ⟨hs'S, hs'R, hs'2⟩ := E.conj_involution_mem hcfg hs hsR hs2 hx
  obtain ⟨f₀, -, -, -, hev, hconj, -⟩ := E.exists_f₀ hcfg
  obtain ⟨m, hm⟩ := hev
  have hsymm := E.card_conjR_U_inf_centralizer hcfg hs hsR hs2 hx
  have hUR : U ⊓ C ≤ R := by rw [hRU]; exact inf_le_left.trans le_sup_left
  have hVR : conjR U x ⊓ C ≤ R := by rw [hRU]; exact inf_le_left.trans le_sup_right
  have hUcard : Nat.card U = 2 ^ (2 * n) * Nat.card (centerOf L) := E.card_U hcfg
  have hZdef : (lin2Z L R) = lin2Z L R := rfl
  have hnum : Nat.card (R ⊓ C : Subgroup G) *
      Nat.card (U ⊓ conjR U x ⊓ C : Subgroup G) ≤ Nat.card U := by
    rw [hUV]
    rcases lin2Z_cases (Z := lin2Z L R) rfl with ⟨hc, hZR⟩ | ⟨hc, hZL⟩
    ·
      have h1 := (E.card_R_inf_centralizer hcfg hs hsR hs2).1 hc
      have h2 := E.card_Z_inf_centralizer hcfg (Z := lin2Z L R) rfl hs hsR hs2
      rw [hZR] at h2
      rw [h1, h2, hUcard, hc, Subgroup.card_bot, mul_one, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    ·
      have h1 := (E.card_R_inf_centralizer hcfg hs hsR hs2).2 hc
      have hZ16 := E.Zbasic hcfg (Z := lin2Z L R) rfl
      rcases E.Zcases hcfg (Z := lin2Z L R) rfl hx hxS with ⟨hc', -⟩ | ⟨-, hZR2, hZinf⟩
      · exact absurd hc' hc
      · have hZ1 : Nat.card (conjR (lin2Z L R) x ⊓ C : Subgroup G) = 2 ^ (n / 2) := by
          rw [hC, conjR_inf_centralizer, card_conjR]
          exact E.card_Z_inf_centralizer hcfg (Z := lin2Z L R) rfl hs'S hs'R hs'2
        have hZ0 := E.card_Z_inf_centralizer hcfg (Z := lin2Z L R) rfl hs hsR hs2
        have hZle : lin2Z L R ≤ centerOf R := lin2Z_le_centerOf E.h16 hcfg rfl
        have hZxle : conjR (lin2Z L R) x ≤ centerOf R := hZR2 ▸ le_sup_right
        have hcomm : ∀ a ∈ lin2Z L R, ∀ b ∈ conjR (lin2Z L R) x, a * b = b * a := fun a ha b hb =>
          (Subgroup.mem_centralizer_iff.mp (hZle ha).2 b (hZxle hb).1).symm
        have hsZ : s ∈ Subgroup.normalizer ((lin2Z L R : Subgroup G) : Set G) := hZ16.2.2 hs
        have hsZx : s ∈ Subgroup.normalizer ((conjR (lin2Z L R) x : Subgroup G) : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro y
          rw [mem_conjR, mem_conjR]
          have h' := Subgroup.mem_normalizer_iff.mp (hZ16.2.2 hs'S) (x * y * x⁻¹)
          have e : x * (s * y * s⁻¹) * x⁻¹ = (x * s * x⁻¹) * (x * y * x⁻¹) * (x * s * x⁻¹)⁻¹ := by
            group
          rw [e]
          exact h'
        have h3 := card_inf_centralizer_sup_le hcomm hZinf hsZ hsZx
        rw [← hZR2, hZ0, hZ1] at h3
        have hcL : Nat.card (centerOf L) = 2 ^ n := by rw [← hZL]; exact hZ16.2.1
        have h4 : Nat.card (centerOf R ⊓ C : Subgroup G) ≤ 2 ^ n := by
          refine h3.trans (le_of_eq ?_)
          rw [← pow_add]
          congr 1
          omega
        rw [h1, hUcard, hcL]
        exact Nat.mul_le_mul_left _ h4
  obtain ⟨h1, h2, h3⟩ := card_sq_eq_and_mul_eq hUe hsU hs2 hsymm hUR hVR hnum
  refine ⟨h1, h2, ?_⟩
  rw [← hUV]
  exact h3

theorem U_s_values {s x : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) (hx : x ∈ T)
    (hxS : x ∉ S) :
    (centerOf L = ⊥ →
      Nat.card (blockU L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) = 2 ^ n ∧
        Nat.card (centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) =
          2 ^ (n / 2)) ∧
    (centerOf L ≠ ⊥ →
      Nat.card (blockU L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) = 2 ^ (3 * n / 2) ∧
        Nat.card (centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) =
          2 ^ n) := by
  obtain ⟨h1, -, h3⟩ := E.U_s_card hcfg hs hsR hs2 hx hxS
  obtain ⟨f₀, -, -, -, hev, -⟩ := E.exists_f₀ hcfg
  obtain ⟨m, hm⟩ := hev
  have hRc := E.card_R_inf_centralizer hcfg hs hsR hs2
  have hUc := E.card_U hcfg
  have hsq : ∀ a b : ℕ, a ^ 2 = b ^ 2 → a = b := fun a b h => Nat.pow_left_injective (by norm_num) h
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [hRc.1 hc, hUc, hc, Subgroup.card_bot, mul_one] at h3
    rw [hUc, hc, Subgroup.card_bot, mul_one] at h1
    refine ⟨hsq _ _ (by rw [← h1, ← pow_mul, mul_comm]), ?_⟩
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ (3 * n / 2) by positivity)
    rw [h3, ← pow_add]
    congr 1
    omega
  · rw [hRc.2 hc, hUc, E.card_centerOf_L hcfg hc] at h3
    rw [hUc, E.card_centerOf_L hcfg hc] at h1
    have ha : Nat.card (blockU L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) =
        2 ^ (3 * n / 2) := by
      apply hsq
      rw [← h1, ← pow_mul, ← pow_add]
      congr 1
      omega
    refine ⟨ha, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ (2 * n) by positivity)
    rw [h3, ← pow_add]

end Ord

end Lin2Hyp

end CFSG.QuasithinUnique.Lin2
