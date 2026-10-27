module

public import CFSG.CGT.PushingUpLit.T2KSW.Defs
public import CFSG.CGT.PushingUpLit.A78.Cfg

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K CFSG.CGT.PushingUpLit.T2KSW
open CFSG.CGT.PushingUpLit.A78
open CFSG.Assembly.RankThreeEven (projSL projSp)

structure Sec4Core (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) : Prop where
  hyp : T2Hyp G L M n
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M
  sylowG : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤
  noG4 : ¬ CFSG.GH74.SectionalTwoRankLE G 4
  noL3 : ¬ Nonempty (G ≃* projSL 3 (GaloisField 2 n))
  S_elem : CFSG.Open.IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))
  N_T : Subgroup.normalizer (T : Set G) ≤ M
  N_J : Subgroup.normalizer (CFSG.Quasithin.thompsonJ T : Set G) ≤ M

theorem sec4Core_of_sec4 {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}
    (h : Sec4 G L M T n) : Sec4Core G L M T n :=
  ⟨h.hyp, h.sylow, h.sylowG, h.noG4, h.noL3, h.S_elem, h.N_T, h.N_J⟩

@[expose] def EWeaklyClosed {G : Type} [Group G] (L T : Subgroup G) : Prop :=
  ∀ g : G, (Ec L T).map (MulAut.conj g).toMonoidHom ≤ T →
    (Ec L T).map (MulAut.conj g).toMonoidHom = Ec L T

@[expose] def Phase0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ), Sec4 G L M T n →
    Ec L T ≠ ⊥ → ClassLETwo T → EWeaklyClosed L T → False

@[expose] def PhaseL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ), Sec4 G L M T n →
    Ec L T ≠ ⊥ → ClassLETwo T → ¬ EWeaklyClosed L T →
      ∃ L₂ : Subgroup G, A78Cfg G L L₂ T n ∧
        oTwoIn (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∧
        oTwoIn (L ⊔ T) ⊔ oTwoIn (L₂ ⊔ T) = T

@[expose] def A78SylowSp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L₁ L₂ T : Subgroup G) (e : ℕ), A78Cfg G L₁ L₂ T e →
    CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
    oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) ≠ ⊥ →
    oTwoIn (L₁ ⊔ T) ⊔ oTwoIn (L₂ ⊔ T) = T →
      Nonempty (G ≃* projSp 2 (GaloisField 2 e))

theorem print55ClassTwo_of_phases (h0 : Phase0) (hL : PhaseL) (hP : A78SylowSp4) :
    Print55ClassTwo := by
  intro G _ _ L M T n hs hE hc
  by_cases hw : EWeaklyClosed L T
  · exact h0 G L M T n hs hE hc hw
  · obtain ⟨L₂, hcfg, hZ, hJT⟩ := hL G L M T n hs hE hc hw
    exact hs.noSp4 (hP G L L₂ T n hcfg hs.sylowG hZ hJT)

end CFSG.CGT.PushingUpLit.C2L
