module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Borel1

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

omit [Finite G] in
theorem S_le_normalizer_inf_conjJoin (S L : Subgroup G) :
    S ≤ Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G) := by
  intro s hs
  rw [← conjR_eq_self_iff, conjR_inf, conjR_eq_of_mem_normalizer (Subgroup.le_normalizer hs),
    conjR_eq_of_mem_normalizer (S_le_normalizer_conjJoin' S L hs)]

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem N_P_le_M :
    conjJoin S L ⊓ Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G) ≤ M := by
  obtain ⟨F, _, _, ⟨A⟩⟩ := B.coord₁
  set K' : Subgroup G :=
    conjJoin S L ⊓ Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G) with hK'
  have hSK : S ≤ Subgroup.normalizer (K' : Set G) := by
    intro s hs
    rw [← conjR_eq_self_iff, hK', conjR_inf, ← conjR_normalizer,
      conjR_eq_of_mem_normalizer (S_le_normalizer_conjJoin' S L hs),
      conjR_eq_of_mem_normalizer (S_le_normalizer_inf_conjJoin S L hs)]
  have hKH : K' ≤ H := inf_le_left.trans B.L₀_le_H
  have hXH : K' ⊔ S ≤ H := sup_le hKH B.S_le_H
  have hLL₀ : L ≤ conjJoin S L := B.hjoin ▸ le_sup_left
  have hXne : K' ⊔ S ≠ H := by
    intro hX
    apply A.not_le_normalizer
    intro ℓ hℓ
    have hℓX : ℓ ∈ K' ⊔ S := hX ▸ B.L₀_le_H (hLL₀ hℓ)
    obtain ⟨k, hk, s, hs, rfl⟩ := (mem_sup_iff_of_le_normalizer hSK).1 hℓX
    have hsL₀ : s ∈ conjJoin S L := by
      have := (conjJoin S L).mul_mem ((conjJoin S L).inv_mem hk.1) (hLL₀ hℓ)
      simpa using this
    have hsK : s ∈ K' := ⟨hsL₀, Subgroup.le_normalizer ⟨hs, hsL₀⟩⟩
    have hℓK : k * s ∈ K' := K'.mul_mem hk hsK
    have hP : conjR ((S ⊓ conjJoin S L) ⊓ L) (k * s) = (S ⊓ conjJoin S L) ⊓ L := by
      rw [conjR_inf, conjR_eq_of_mem_normalizer hℓK.2,
        conjR_eq_of_mem_normalizer (Subgroup.le_normalizer hℓ)]
    rw [B.P_inf_L] at hP
    exact conjR_eq_self_iff.1 hP
  exact le_sup_left.trans (B.cs.maxInf (K' ⊔ S) le_sup_right (lt_of_le_of_ne hXH hXne))

theorem isSylowTwoOf_P_inf_M : IsSylowTwoOf (S ⊓ conjJoin S L) (conjJoin S L ⊓ M) :=
  isSylowTwoOf_of_le_of_le B.isSylowTwoOf_S_inf_L₀
    (le_inf inf_le_right (inf_le_left.trans B.S_le_M)) inf_le_left

theorem inf_M_decomp : D ⊓ (S ⊓ conjJoin S L) = ⊥ ∧ (S ⊓ conjJoin S L) ⊔ D = conjJoin S L ⊓ M ∧
    ∀ k ∈ conjJoin S L ⊓ M, ∃ p ∈ S ⊓ conjJoin S L, ∃ d ∈ D, k = p * d :=
  hall_sylow_decomp' B.isSylowTwoOf_P_inf_M B.cfg.hall B.D_le_normalizer_P

theorem inf_M_eq : conjJoin S L ⊓ M =
    conjJoin S L ⊓ Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G) := by
  apply le_antisymm
  · intro k hk
    refine ⟨hk.1, ?_⟩
    obtain ⟨p, hp, d, hd, rfl⟩ := B.inf_M_decomp.2.2 k hk
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hp) (B.D_le_normalizer_P hd)
  · exact fun k hk => ⟨hk.1, B.N_P_le_M hk⟩

theorem P_le_inf_M : S ⊓ conjJoin S L ≤ conjJoin S L ⊓ M :=
  le_inf inf_le_right (inf_le_left.trans B.S_le_M)

end S2Base

end CFSG.QuasithinUnique.Lin2
