module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Setting3
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma exists_conjSub_inv_le_of_sylow {H T E : Subgroup G} (hT : IsSylowIn 2 H T)
    (hEH : E ≤ H) (hE : IsPGroup 2 E) : ∃ c : G, conjSub c⁻¹ E ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsub_pg : IsPGroup 2 (T.subgroupOf H) := hT.2.1.comap_subtype
  have hTsub_ne : ¬ 2 ∣ (T.subgroupOf H).index := by
    simpa only [Subgroup.relIndex] using hT.2.2
  let P : Sylow 2 ↥H := hTsub_pg.toSylow hTsub_ne
  have hPcoe : (P : Subgroup ↥H) = T.subgroupOf H := rfl
  haveI : Finite (Sylow 2 ↥H) := Sylow.finite_of_finiteIndex P
  have hEsub_pg : IsPGroup 2 (E.subgroupOf H) := hE.comap_subtype
  obtain ⟨Q, hQ⟩ := hEsub_pg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (M := ↥H) P Q
  refine ⟨(c : G), ?_⟩
  intro x hx
  rw [conjSub, Subgroup.mem_map] at hx
  obtain ⟨e, he, rfl⟩ := hx
  have heH : e ∈ H := hEH he
  have heQ : (⟨e, heH⟩ : ↥H) ∈ (Q : Subgroup ↥H) :=
    hQ (Subgroup.mem_subgroupOf.mpr he)
  have hmem : (⟨e, heH⟩ : ↥H) ∈ ((c • P : Sylow 2 ↥H) : Subgroup ↥H) := by
    rw [hc]; exact heQ
  rw [Sylow.coe_subgroup_smul] at hmem
  have h2 := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hmem
  rw [hPcoe] at h2
  have h3 : (((MulAut.conj c)⁻¹ • (⟨e, heH⟩ : ↥H) : ↥H) : G) =
      (c : G)⁻¹ * e * (c : G) := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
    simp
  have h4 : (c : G)⁻¹ * e * (c : G) ∈ T := h3 ▸ Subgroup.mem_subgroupOf.mp h2
  simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h4

theorem y7n_mH_le {s : Setting3 G L} {e : Setting3.Ext s} (hDef : e.FactDef)
    (hRT : s.R ≠ s.T) :
    ∀ E : Subgroup G, E ≤ centralizer ({s.t} : Set G) → IsElemAbelian 2 E →
      Nat.card E ≤ 32 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E hEH hEab
  obtain ⟨c, hFT⟩ := exists_conjSub_inv_le_of_sylow s.sylow_T hEH hEab.isPGroup
  set F : Subgroup G := conjSub c⁻¹ E with hFdef
  have hFab : IsElemAbelian 2 F := by
    rw [hFdef]; exact hEab.map (MulAut.conj c⁻¹).toMonoidHom
  have hFcard : Nat.card F = Nat.card E := by
    rw [hFdef, conjSub]
    exact Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  suffices Nat.card F ≤ 32 by
    calc Nat.card E = Nat.card F := hFcard.symm
      _ ≤ 32 := this
  have hSσ_sylow : IsSylowIn 2 ⊤ s.fr'.Sσ := s.facts.1.2.2
  have hSσ_notdvd : ¬ 2 ∣ s.fr'.Sσ.index := by
    simpa [Subgroup.relIndex_top_right] using hSσ_sylow.2.2
  let P : Sylow 2 (MulAut (L ⧸ center L)) := hSσ_sylow.2.1.toSylow hSσ_notdvd
  have hPcoe : (P : Subgroup (MulAut (L ⧸ center L))) = s.fr'.Sσ :=
    IsPGroup.toSylow_coe _ _
  obtain ⟨hN, hPiso⟩ := (hDef.1 hRT).1
  let Nz : Subgroup ↥s.T := (zpowers s.t).subgroupOf s.T
  haveI : Nz.Normal := hN
  let π : ↥s.T →* ↥s.T ⧸ Nz := QuotientGroup.mk' Nz
  obtain ⟨φ⟩ := hPiso P
  set E'' : Subgroup ↥s.T := F.subgroupOf s.T with hE''def
  set Ē : Subgroup (↥s.T ⧸ Nz) := E''.map π with hĒdef
  set A : Subgroup (MulAut (L ⧸ center L)) :=
    (Ē.map φ.toMonoidHom).map (P : Subgroup (MulAut (L ⧸ center L))).subtype with hAdef
  have hE''ab : IsElemAbelian 2 E'' := by rw [hE''def]; exact hFab.subgroupOf s.T
  have hĒab : IsElemAbelian 2 Ē := by rw [hĒdef]; exact hE''ab.map π
  have hAab : IsElemAbelian 2 A := by
    rw [hAdef]
    exact (hĒab.map φ.toMonoidHom).map (P : Subgroup (MulAut (L ⧸ center L))).subtype
  have hA_le : A ≤ s.fr'.Sσ := by
    rw [hAdef]
    exact (Subgroup.map_subtype_le _).trans (le_of_eq hPcoe)
  have hA16 : Nat.card A ≤ 16 :=
    s.facts.2.2.2.2.1.2.2.2.2.1 A hA_le hAab.1
  have hcardA : Nat.card A = Nat.card Ē := by
    rw [hAdef, Subgroup.card_subtype, Subgroup.card_map_of_injective φ.injective]
  have hĒcard : Nat.card Ē ≤ 16 := by
    have := hA16
    rwa [hcardA] at this
  let f : ↥E'' →* ↥s.T ⧸ Nz := π.comp E''.subtype
  have hrange : f.range = Ē := by
    have h := MonoidHom.range_comp π E''.subtype
    rw [Subgroup.range_subtype] at h
    exact h
  let g : f.ker → Nz := fun x =>
    ⟨(x.1.1 : ↥s.T), by
      have hx1 : π (x.1.1 : ↥s.T) = 1 := by
        change f x.1 = 1
        exact x.2
      have hx2 : (x.1.1 : ↥s.T) ∈ π.ker := (MonoidHom.mem_ker (f := π)).mp hx1
      rwa [show π.ker = Nz from QuotientGroup.ker_mk' Nz] at hx2⟩
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have h1 : (x.1.1 : ↥s.T) = (y.1.1 : ↥s.T) := by
      have := congrArg Subtype.val hxy
      simpa [g] using this
    exact Subtype.ext (Subtype.ext h1)
  have hker_le : Nat.card f.ker ≤ 2 := by
    have h1 : Nat.card f.ker ≤ Nat.card Nz := Nat.card_le_card_of_injective g hg_inj
    have h2 : Nat.card Nz ≤ 2 := by
      have hmap : Nat.card (Nz.map s.T.subtype) = Nat.card Nz :=
        Subgroup.card_map_of_injective s.T.subtype_injective
      have hle : Nz.map s.T.subtype ≤ zpowers s.t := by
        rw [show Nz = (zpowers s.t).subgroupOf s.T from rfl,
          Subgroup.subgroupOf_map_subtype]
        exact inf_le_left
      have hcard : Nat.card (Nz.map s.T.subtype) ≤ Nat.card (zpowers s.t) :=
        Subgroup.card_le_of_le hle
      rw [hmap, Nat.card_zpowers, s.t_order] at hcard
      exact hcard
    omega
  have hcard : Nat.card E'' = Nat.card Ē * Nat.card f.ker := by
    have h1 : Nat.card (↥E'' ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, h1, hrange]
  have hFE'' : Nat.card F = Nat.card E'' := by
    rw [hE''def]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFT).toEquiv).symm
  calc Nat.card F = Nat.card E'' := hFE''
    _ = Nat.card Ē * Nat.card f.ker := hcard
    _ ≤ 16 * 2 := Nat.mul_le_mul hĒcard hker_le
    _ = 32 := by norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
