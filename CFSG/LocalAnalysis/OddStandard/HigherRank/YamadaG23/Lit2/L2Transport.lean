module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitTransport

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem l2z4_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (h : L2Z4Type S') :
    L2Z4Type S := by
  unfold L2Z4Type at h ⊢
  rcases h with h | h | ⟨n, p, f, hn, hq, hm⟩ | ⟨n, p, f, hn, hq, hm⟩ |
    ⟨n, p, f, hn, hq, hm⟩ | ⟨n, p, f, hn, hq, hm⟩
  · exact Or.inl (lit_isSporadic_of_mulEquiv e h)
  · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h))
  · exact Or.inr (Or.inr (Or.inl
      ⟨n, p, f, hn, hq, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨n, p, f, hn, hq, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨n, p, f, hn, hq, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨n, p, f, hn, hq, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm⟩))))

private lemma centIn_map_subtype_gen {Λ : Type} [Group Λ] (K : Subgroup Λ) (H : Subgroup ↥K) :
    centIn K (H.map K.subtype) = (centralizer (H : Set ↥K)).map K.subtype := by
  ext c
  constructor
  · rintro ⟨hcG, hcC⟩
    rw [Subgroup.mem_map]
    refine ⟨⟨c, hcG⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    apply Subtype.ext
    have hmem : (a : Λ) ∈ (H.map K.subtype : Set Λ) := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have h := hcC (a : Λ) hmem
    simpa using h
  · rintro hc
    rcases Subgroup.mem_map.mp hc with ⟨d, hd, rfl⟩
    refine ⟨d.2, ?_⟩
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    have hda := (Subgroup.mem_centralizer_iff.mp hd) a ha
    simpa using congrArg (fun y : ↥K => (y : Λ)) hda

private lemma isElemAbelian_top_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {p : ℕ} (h : CFSG.Open.IsElemAbelian p (⊤ : Subgroup B)) :
    CFSG.Open.IsElemAbelian p (⊤ : Subgroup A) := by
  constructor
  · rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    exact e.injective (by
      change e (a.1 * b.1) = e (b.1 * a.1)
      rw [map_mul, map_mul]
      have hc := isMulCommutative_iff.mp h.1 ⟨e a.1, Subgroup.mem_top _⟩
        ⟨e b.1, Subgroup.mem_top _⟩
      simpa using congrArg Subtype.val hc)
  · intro x _
    have hx := h.2 (e x) (Subgroup.mem_top (e x))
    exact e.injective (by rw [map_pow, map_one]; exact hx)

theorem l2_E_sub {G : Type} [Group G] {M E : Subgroup G} (hEM : E ≤ M) (hE : IsE 4 ↥E) :
    IsE 4 ↥(E.subgroupOf M) := by
  let e : ↥(E.subgroupOf M) ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEM
  exact ⟨isElemAbelian_top_of_mulEquiv e hE.1, (Nat.card_congr e.toEquiv).trans hE.2⟩

theorem l2_sylow_top {G : Type} [Group G] {M E : Subgroup G} (hEM : E ≤ M)
    (hS : IsSylowIn 2 (centIn M E) E) :
    IsSylowIn 2 (centIn ⊤ (E.subgroupOf M)) (E.subgroupOf M) := by
  let E' : Subgroup ↥M := E.subgroupOf M
  let e : ↥E' ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEM
  have hE'_map : E'.map M.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEM
  have hcent : (centIn ⊤ E').map M.subtype = centIn M E := by
    have h := centIn_map_subtype_gen M E'
    rw [hE'_map] at h
    rw [h]
    rw [Subgroup.map_subtype_inj]
    simp [centIn]
  have hle : E' ≤ centIn ⊤ E' := by
    intro x hx
    refine ⟨Subgroup.mem_top x, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hxG : (x : G) ∈ E := hx
    have hyG : (y : G) ∈ E := hy
    have hxcent : (x : G) ∈ centralizer (E : Set G) :=
      (Subgroup.mem_inf.mp (hS.1 hxG)).2
    have hcomm := (Subgroup.mem_centralizer_iff.mp hxcent) (y : G) hyG
    exact Subtype.ext (by simpa using hcomm)
  have hp : IsPGroup 2 ↥E' := hS.2.1.of_equiv e.symm
  have hrel : ¬ 2 ∣ E'.relIndex (centIn ⊤ E') := by
    rw [← Subgroup.relIndex_map_map_of_injective E' (centIn ⊤ E') M.subtype_injective,
      hE'_map, hcent]
    exact hS.2.2
  exact ⟨hle, hp, hrel⟩

theorem l2_catalog_sub {Γ : Type} [Group Γ] {Gh : Subgroup Γ}
    (h : ∀ H : Subgroup Γ, H ≤ Gh → CFSG.IsQuasisimple ↥H →
      CFSG.Blueprint.Catalog (↥H ⧸ center ↥H)) (H : Subgroup ↥Gh) (hq : CFSG.IsQuasisimple ↥H) :
    CFSG.Blueprint.Catalog (↥H ⧸ center ↥H) := by
  let H' : Subgroup Γ := H.map Gh.subtype
  have hH'le : H' ≤ Gh := Subgroup.map_subtype_le H
  let e : ↥H ≃* ↥H' := Subgroup.equivMapOfInjective H Gh.subtype Gh.subtype_injective
  have hq' : CFSG.IsQuasisimple ↥H' := lit_isQuasisimple_of_mulEquiv e hq
  have hcat : CFSG.Blueprint.Catalog (↥H' ⧸ center ↥H') := h H' hH'le hq'
  have e' : (↥H ⧸ center ↥H) ≃* (↥H' ⧸ center ↥H') :=
    QuotientGroup.congr (Subgroup.center ↥H) (Subgroup.center ↥H') e (Subgroup.map_center_eq e)
  exact CFSG.SectionRank.catalog_of_mulEquiv e' hcat

end CFSG.OddStandard.HigherRank.YamadaG23
