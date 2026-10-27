module

public import CFSG.GF2Type.Aschbacher1976Full.HSGL3Simple
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG.ComponentClassification.GHarris

theorem nonempty_mulAut_mulEquiv_GL3 {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 8)
    (hcomm : ∀ a b : V, a * b = b * a) (hsq : ∀ v : V, v * v = 1) :
    Nonempty (MulAut V ≃* GL (Fin 3) (ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := V) (p := 2) (n := 3)
    hcomm (fun a => by rw [pow_two, hsq]) (by rw [hV]; norm_num)
  exact ⟨CFSG.SectionRank.Ccomm.elemAutEquivGL e⟩

theorem card_mulAut_eq_168 {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 8)
    (hcomm : ∀ a b : V, a * b = b * a) (hsq : ∀ v : V, v * v = 1) :
    Nat.card (MulAut V) = 168 := by
  obtain ⟨f⟩ := nonempty_mulAut_mulEquiv_GL3 hV hcomm hsq
  rw [Nat.card_congr f.toEquiv]
  exact card_GL32_gh

theorem dvd_56_of_dvd_14 {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 8)
    (hcomm : ∀ a b : V, a * b = b * a) (hsq : ∀ v : V, v * v = 1)
    (X : Subgroup (MulAut V)) (h : 14 ∣ Nat.card X) : Nat.card X = 168 := by
  obtain ⟨f⟩ := nonempty_mulAut_mulEquiv_GL3 hV hcomm hsq
  haveI := isSimpleGroup_GL32_gh
  have hY : Nat.card (X.map f.toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective f.injective
  have htop := eq_top_of_dvd_fourteen_simple168 card_GL32_gh (X := X.map f.toMonoidHom) (hY ▸ h)
  rw [← hY, htop, Subgroup.card_top]
  exact card_GL32_gh

theorem eq_top_of_dvd_14 {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 8)
    (hcomm : ∀ a b : V, a * b = b * a) (hsq : ∀ v : V, v * v = 1)
    (X : Subgroup (MulAut V)) (h : 14 ∣ Nat.card X) : X = ⊤ :=
  Subgroup.eq_top_of_card_eq X
    ((dvd_56_of_dvd_14 hV hcomm hsq X h).trans (card_mulAut_eq_168 hV hcomm hsq).symm)

theorem exists_GL32_of_dvd_14_index {G : Type*} [Group G] [Finite G] {V : Subgroup G}
    (hV : CFSG.Open.IsElemAbelian 2 V) (h8 : Nat.card V = 8)
    (h14 : 14 ∣ ((Subgroup.centralizer (V : Set G)).subgroupOf
      (Subgroup.normalizer (V : Set G))).index) :
    ∃ θ : ↥(Subgroup.normalizer (V : Set G)) →* GL (Fin 3) (ZMod 2), Function.Surjective θ ∧
      θ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G)) := by
  have hX : Nat.card V.normalizerMonoidHom.range = ((Subgroup.centralizer (V : Set G)).subgroupOf
      (Subgroup.normalizer (V : Set G))).index := by
    rw [← Subgroup.index_ker, V.normalizerMonoidHom_ker]
  have h168 := dvd_56_of_dvd_14 (V := ↥V) h8 (fun a b => hV.1.is_comm.comm a b)
    (fun a => by rw [← pow_two]; exact Subtype.ext (hV.2 a a.2)) V.normalizerMonoidHom.range
    (hX ▸ h14)
  refine exists_GL32_of_dvd_index hV h8 ?_
  rw [← hX, h168]
  norm_num

end CFSG.GF2Type.Aschbacher1976Full.HS
