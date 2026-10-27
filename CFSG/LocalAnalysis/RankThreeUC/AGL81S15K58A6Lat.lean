module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K58SylLat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K58Lattice
public import CFSG.Quasithin.Background.SmithC27RLieA6
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.A6Core

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K58Proof

open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252.A6

theorem sylLatAt_alt6 :
    SylLatAt (D0.subgroupOf A6s) (Sa.subgroupOf A6s) (Sb.subgroupOf A6s) 15 := by
  have : IsSimpleGroup ↥A6s := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isSimpleGroup_alt6
  have hA6 : Nat.card ↥A6s = 360 := card_A6
  have hidx : ∀ {H : Subgroup (Equiv.Perm (Fin 6))}, H ≤ A6s →
      Nat.card H * (H.subgroupOf A6s).index = 360 := fun hH => by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hH).toEquiv, card_mul_index, hA6]
  have hiD : (D0.subgroupOf A6s).index = 45 := by
    have h := hidx D0_le_A6
    rw [card_D0] at h
    omega
  have hiA : (Sa.subgroupOf A6s).index = 15 := by
    have h := hidx Sa_le_A6
    rw [CFSG.Quasithin.GoldS146R.card_Sa] at h
    omega
  have hiB : (Sb.subgroupOf A6s).index = 15 := by
    have h := hidx Sb_le_A6
    rw [CFSG.Quasithin.GoldS146R.card_Sb] at h
    omega
  have hlat : ∀ Y : Subgroup ↥A6s, D0.subgroupOf A6s ≤ Y →
      Y = D0.subgroupOf A6s ∨ Y = Sa.subgroupOf A6s ∨ Y = Sb.subgroupOf A6s ∨ Y = ⊤ := by
    intro Y hDY
    have hD : D0 ≤ Y.map A6s.subtype := fun d hd =>
      ⟨⟨d, D0_le_A6 hd⟩, hDY (by rwa [mem_subgroupOf]), rfl⟩
    have hA : Y.map A6s.subtype ≤ A6s := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hY : (Y.map A6s.subtype).subgroupOf A6s = Y :=
      comap_map_eq_self_of_injective A6s.subtype_injective Y
    rcases six_overgroups _ hD hA with h | h | h | h <;> rw [← hY, h]
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (subgroupOf_self A6s)))
  have hDA : D0.subgroupOf A6s ≤ Sa.subgroupOf A6s := fun x hx => D0_le_Sa hx
  have hDB : D0.subgroupOf A6s ≤ Sb.subgroupOf A6s := fun x hx => D0_le_Sb hx
  have hlt : 15 < (D0.subgroupOf A6s).index := by rw [hiD]; norm_num
  exact
    { le_A := hDA
      le_B := hDB
      lattice := hlat
      index_A := hiA
      index_B := hiB
      lt_index := hlt
      one_lt := by norm_num
      normalizer_eq :=
        CFSG.Quasithin.SmithC27.normalizer_eq_of_isSylowTwoOf_alt6
          CFSG.Quasithin.GoldS146R.isSylowTwoOf_D0
      normalizer_A := normalizer_eq_self_of_lattice hlat hiA hiB hlt (by norm_num) hDA hiA
      normalizer_B := normalizer_eq_self_of_lattice hlat hiA hiB hlt (by norm_num) hDB hiB }

theorem sylLat_alt6 : SylLat ↥(alternatingGroup (Fin 6)) 15 :=
  SylLat.of_sylLatAt CFSG.Quasithin.GoldS146R.isSylowTwoOf_D0 sylLatAt_alt6

theorem sylLat_of_alt6 {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 6)) : SylLat Y 15 :=
  SylLat.of_mulEquiv e sylLat_alt6

end CFSG.LocalAnalysis.RankThreeUC.S15.K58Proof
