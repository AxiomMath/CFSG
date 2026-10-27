module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136c
public import CFSG.Quasithin.Background.F9Sixteen

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Quasithin.E3

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem hypF98_G1_F4 (h1323 : Input1323Two_F4) (h1336 : Input1336_F4)
    (h24 : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
      ⁅V, conjSub g⁻¹ V⁆ = ⊥) :
    HypF98 T V L S.V1 S.V3 S.G1 where
  toHypF91 := S.hypF91_F4 h1323 (S.G1_mem_Hz_F4 h1336)
  weak_f := fun g hg => by
    by_cases hgN : g ∈ Subgroup.normalizer (V : Set G)
    · rw [conjSub_self_of_mem (Subgroup.inv_mem _ hgN),
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
    · have hne : V ⊓ conjSub g⁻¹ V ≠ ⊥ := by
        intro h
        have : S.z ∈ V ⊓ conjSub g⁻¹ V := ⟨S.z_mem_V, hg (Subgroup.mem_zpowers _)⟩
        rw [h] at this
        exact S.z_ne_one (Subgroup.mem_bot.mp this)
      exact h24 g hgN hne
  case_g := Or.inl (by
    have h1 : ⁅V, S.G1 ⊓ Subgroup.centralizer (S.V3 : Set G)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
        h1323 G T L V S (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hx).2)
      exact S.mem_centralizer_V_of_V3 hxN (Subgroup.mem_inf.mp hx).2
    rw [h1]
    exact bot_le)

end Setting

@[expose] def Fin136_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) →
    (∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
      (∃ u : ↥V, u ≠ 1 ∧ IsSing (S.frame.ψ u) ∧
        V ⊓ conjSub g⁻¹ V = Subgroup.zpowers (u : G)) ∧ ⁅V, conjSub g⁻¹ V⁆ = ⊥) →
    rParam V = 3 → 1 < wParam T V →
    (∀ H : Subgroup G, InH T H → ¬ H ≤ Subgroup.normalizer (L : Set G) → 1 < E1.nParam H) →
    (∀ H : Subgroup G, InH T H → Group.IsSolvable ↥H → H ≤ Subgroup.normalizer (L : Set G)) →
    (∀ H ∈ S.Hz, ∀ K ∈ cComp H, ¬ K ≤ Subgroup.normalizer (L : Set G)) →
    (∀ hE : IsElemAbelian 2 (tildeOf S.V1 (conjClosure S.V3 S.G1)),
      qInt (tildeOf S.V1 S.G1) (tildeOf S.V1 (conjClosure S.V3 S.G1)) hE ≤ 2) →
      False

theorem end136_of_F4 (h1323 : Input1323Two_F4) (h1336 : Input1336_F4) (h1338 : A6.Stmt13_3_8_F4)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfin : Fin136_F4) :
    End136_F4 := by
  intro G _ _ T L V S hab h24 hr hw hn hsolv
  have hF98 := S.hypF98_G1_F4 h1323 h1336 fun g hg hne => (h24 g hg hne).2
  exact hfin G T L V S hab h24 hr hw hn hsolv
    (fun H hH K hK => S.lemma_13_6_26_one_F4 h1338 h37 h38 hH hK) (fun _ => hF98.F916_3.1)

end CFSG.Quasithin.H13.A5
