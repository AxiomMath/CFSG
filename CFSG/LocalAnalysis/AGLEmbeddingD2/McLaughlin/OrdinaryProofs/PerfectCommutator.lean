module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

theorem three_subgroups_mod_normal {H : Type*} [Group H] {A B C K : Subgroup H} [K.Normal]
    (hAB : ⁅⁅A, B⁆, C⁆ ≤ K) (hBC : ⁅⁅B, C⁆, A⁆ ≤ K) : ⁅⁅C, A⁆, B⁆ ≤ K := by
  have key : ∀ X : Subgroup H, X ≤ K ↔ X.map (QuotientGroup.mk' K) = ⊥ := fun X => by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [key] at hAB hBC ⊢
  simp only [Subgroup.map_commutator] at hAB hBC ⊢
  exact Subgroup.commutator_commutator_eq_bot_of_rotate hAB hBC

theorem commutator_commutator_eq_of_perfect {G : Type*} [Group G] {N L : Subgroup G}
    (hL : ⁅L, L⁆ = L) (hNL : N ≤ L) (hN : L ≤ Subgroup.normalizer (N : Set G)) :
    ⁅⁅N, L⁆, L⁆ = ⁅N, L⁆ := by
  have hNn : (N.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hN
  have hLt : (⊤ : Subgroup L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hLtop : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
    apply Subgroup.map_injective (f := L.subtype) Subtype.val_injective
    rw [Subgroup.map_commutator, hLt, hL]
  have hcore : (⁅N.subgroupOf L, (⊤ : Subgroup L)⁆ : Subgroup L) ≤
      ⁅⁅N.subgroupOf L, (⊤ : Subgroup L)⁆, (⊤ : Subgroup L)⁆ := by
    have hAB : ⁅⁅(⊤ : Subgroup L), N.subgroupOf L⁆, (⊤ : Subgroup L)⁆ ≤
        ⁅⁅N.subgroupOf L, (⊤ : Subgroup L)⁆, (⊤ : Subgroup L)⁆ :=
      le_of_eq (by rw [Subgroup.commutator_comm (⊤ : Subgroup L) (N.subgroupOf L)])
    have hBC : ⁅⁅N.subgroupOf L, (⊤ : Subgroup L)⁆, (⊤ : Subgroup L)⁆ ≤
        ⁅⁅N.subgroupOf L, (⊤ : Subgroup L)⁆, (⊤ : Subgroup L)⁆ := le_rfl
    have h3 := three_subgroups_mod_normal (A := (⊤ : Subgroup L)) (B := N.subgroupOf L)
      (C := (⊤ : Subgroup L))
      (K := ⁅⁅N.subgroupOf L, (⊤ : Subgroup L)⁆, (⊤ : Subgroup L)⁆) hAB hBC
    rw [hLtop, Subgroup.commutator_comm (⊤ : Subgroup L) (N.subgroupOf L)] at h3
    exact h3
  have hEq : (⁅N.subgroupOf L, (⊤ : Subgroup L)⁆ : Subgroup L) =
      ⁅⁅N.subgroupOf L, (⊤ : Subgroup L)⁆, (⊤ : Subgroup L)⁆ :=
    le_antisymm hcore (Subgroup.commutator_le_left _ _)
  have hmapN : (N.subgroupOf L).map L.subtype = N := Subgroup.map_subgroupOf_eq_of_le hNL
  have hmapM : (⁅N.subgroupOf L, (⊤ : Subgroup L)⁆ : Subgroup L).map L.subtype = ⁅N, L⁆ := by
    rw [Subgroup.map_commutator, hmapN, hLt]
  have hmapK : (⁅⁅N.subgroupOf L, (⊤ : Subgroup L)⁆, (⊤ : Subgroup L)⁆ : Subgroup L).map
      L.subtype = ⁅⁅N, L⁆, L⁆ := by
    rw [Subgroup.map_commutator, hmapM, hLt]
  have hEq' := congrArg (Subgroup.map L.subtype) hEq
  rw [hmapM, hmapK] at hEq'
  exact hEq'.symm

theorem commutator_blockU_eq {G : Type*} [Group G] {L : Subgroup G} (hL : ⁅L, L⁆ = L) :
    ⁅CFSG.QuasithinUnique.blockU L, L⁆ = CFSG.QuasithinUnique.blockU L := by
  have hset : CFSG.Open.pCore 2 L = sSup {N : Subgroup L | N.Normal ∧ IsPGroup 2 N} := rfl
  have hQn : (CFSG.Open.pCore 2 L).Normal := by
    rw [hset]
    exact Subgroup.sSup_normal _ fun N hN => hN.1
  have hNL : CFSG.Open.pCoreOf 2 L ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hsub : ∀ g ∈ L, ∀ h ∈ CFSG.Open.pCoreOf 2 L, g * h * g⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    intro g hg h hh
    obtain ⟨k, hk, rfl⟩ := hh
    exact ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, hQn.conj_mem k hk ⟨g, hg⟩, by simp⟩
  have hN : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hsub g hg h, fun hh => ?_⟩
    simpa [mul_assoc] using hsub g⁻¹ (L.inv_mem hg) _ hh
  exact commutator_commutator_eq_of_perfect hL hNL hN

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

end
