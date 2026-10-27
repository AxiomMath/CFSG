module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEBaum
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEStep1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def Lemma246Double : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    conjJoin S L ≠ L → (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
      Subgroup.normalizer (pCoreOf 2 H : Set G) ≤ Subgroup.normalizer (conjJoin S L : Set G)

section Base

variable {G : Type} [Group G] [Finite G]

structure S2Base (T M H S L D : Subgroup G) (n : ℕ) (t : G) (M₀ : Subgroup G) (x₀ : G) (q : ℕ)
    (W : Subgroup G) : Prop where
  cfg : Lin2Cfg2 G T M H S L n D
  su : AppE.Setup T M H S L n t M₀ x₀ q W

theorem Lin2Cfg2.exists_base {T M H S L D : Subgroup G} {n : ℕ} (h : Lin2Cfg2 G T M H S L n D) :
    ∃ (t : G) (M₀ : Subgroup G) (x₀ : G) (q : ℕ) (W : Subgroup G),
      S2Base T M H S L D n t M₀ x₀ q W := by
  obtain ⟨t, ⟨Dbl⟩⟩ := AppE.exists_dbl h.cs h.one_lt h.lin2 h.double
  obtain ⟨M₀, hSM, hMT, h2⟩ := C56.exists_index_two h.cs
  obtain ⟨q, W, hloc⟩ := Dbl.loc
  obtain ⟨x, hx, hxS, hgood⟩ := Dbl.exists_good hSM hMT h2 hloc
  exact ⟨t, M₀, x, q, W, ⟨h, ⟨Dbl, hSM, hMT, h2, hx, hxS, hloc, hgood⟩⟩⟩

namespace S2Base

variable {T M H S L D : Subgroup G} {n : ℕ} {t : G} {M₀ : Subgroup G} {x₀ : G} {q : ℕ}
  {W : Subgroup G} (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem dbl : AppE.Dbl T M H S L n t := B.su.D

theorem cs : ConstrainedSetting G T M H S L := B.cfg.cs

theorem hn : 2 ≤ n := B.dbl.hn

theorem hlin : IsLin2Type L n := B.cfg.lin2

theorem hlin₂ : IsLin2Type (conjR L t) n := B.dbl.hlin₂

theorem hL : IsShort2 L := B.dbl.hL

theorem hL₂ : IsShort2 (conjR L t) := B.dbl.hL₂

theorem ht : t ∈ S := B.dbl.ht

theorem hne : conjR L t ≠ L := B.dbl.hne

theorem hjoin : conjJoin S L = L ⊔ conjR L t := B.dbl.hjoin

theorem comm_elem : ∀ a ∈ L, ∀ b ∈ conjR L t, a * b = b * a := B.dbl.comm_elem

theorem hSM : S ≤ M₀ := B.su.hSM

theorem hMT : M₀ ≤ T := B.su.hMT

theorem h2 : S.relIndex M₀ = 2 := B.su.h2

theorem hx₀ : x₀ ∈ M₀ := B.su.hx

theorem hx₀S : x₀ ∉ S := B.su.hxS

theorem S_le_T : S ≤ T := B.cs.le_T

theorem sylow : IsSylowTwoOf S H := B.cs.sylow

theorem H_eq : H = conjJoin S L ⊔ S := B.cs.eq_join

theorem S_le_M : S ≤ M := B.S_le_T.trans B.cs.setting.le

theorem T_isPGroup : IsPGroup 2 T := B.cs.setting.isPGroup

theorem L₀_le_H : conjJoin S L ≤ H := B.H_eq ▸ le_sup_left

theorem S_le_H : S ≤ H := B.H_eq ▸ le_sup_right

end S2Base

end Base

end CFSG.QuasithinUnique.Lin2
