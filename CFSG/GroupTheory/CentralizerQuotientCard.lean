module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem card_centralizer_eq_card_inf_mul_card_quotient (p : ℕ) [Fact p.Prime]
    {N : Subgroup G} [hN : N.Normal] {x : G} (hx : IsPGroup p (Subgroup.zpowers x))
    (hcop : Nat.Coprime p (Nat.card N)) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ N) *
        Nat.card (Subgroup.centralizer ({(x : G ⧸ N)} : Set (G ⧸ N))) := by
  haveI hT : Fact (IsPGroup p ↥(Subgroup.zpowers x)) := ⟨hx⟩
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hmap : Subgroup.centralizer
        (((Subgroup.zpowers x).map q : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
      (Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)).map q :=
    centralizer_map_quotient_eq_map_centralizer (G := G) p (Subgroup.zpowers x) N hN hcop
  have hcent_zpow : ∀ {K : Type} [Group K] (y : K),
      Subgroup.centralizer ((Subgroup.zpowers y : Subgroup K) : Set K) =
        Subgroup.centralizer ({y} : Set K) := by
    intro K _ y
    ext z
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h; exact (h y (Subgroup.mem_zpowers y)).symm
    · intro h w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (((commute_iff_eq z y).mpr h).zpow_right n |>.eq).symm
  have hcent : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := hcent_zpow x
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let f : ↥C →* G ⧸ N := q.comp C.subtype
  have hrange : f.range = Subgroup.centralizer ({(x : G ⧸ N)} : Set (G ⧸ N)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    change C.map q = _
    rw [show C = Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) by
      rw [hcent]]
    rw [← hmap]
    have hmap' : (Subgroup.zpowers x).map q = Subgroup.zpowers ((x : G ⧸ N)) := by
      rw [MonoidHom.map_zpowers q x]
      rfl
    rw [hmap']
    exact hcent_zpow (q x)
  have hker : f.ker = N.subgroupOf C := by
    ext y
    simp [f, q, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcard := Subgroup.card_ker_mul_card_range f
  have hker_eq : f.ker = (C ⊓ N).subgroupOf C := by
    rw [hker]
    ext z
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨z.2, h⟩, fun h => h.2⟩
  have hkercard : Nat.card f.ker = Nat.card ↥(C ⊓ N) := by
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ⊓ N ≤ C)).toEquiv
  calc Nat.card (Subgroup.centralizer ({x} : Set G))
      = Nat.card C := rfl
    _ = Nat.card f.ker * Nat.card f.range := hcard.symm
    _ = Nat.card ↥(C ⊓ N) * Nat.card (Subgroup.centralizer ({(x : G ⧸ N)} : Set (G ⧸ N))) := by
        rw [hkercard, hrange]

end CFSG
