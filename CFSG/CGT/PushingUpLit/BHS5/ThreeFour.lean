module

public import CFSG.CGT.PushingUpLit.BHS.HomTransfer

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.CGT.PushingUpLit.BHS

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

theorem MinPar.map_of_ker_le (f : G →* H) {P T M : Subgroup G} (h : MinPar P T M)
    (hker : f.ker ⊓ P ≤ M) : MinPar (P.map f) (T.map f) (M.map f) where
  syl := isSylowOf_map f h.syl
  not_normal := by
    intro hn
    set K : Subgroup G := P ⊓ (T.map f).comap f with hK
    have hKP : K ≤ P := inf_le_left
    have hTK : T ≤ K := fun t ht => ⟨h.T_le ht, Subgroup.mem_map_of_mem f ht⟩
    have hKn : P ≤ Subgroup.normalizer (K : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      have hfg := Subgroup.mem_normalizer_iff.1 (hn (Subgroup.mem_map_of_mem f hg))
      intro x
      simp only [hK, Subgroup.mem_inf, Subgroup.mem_comap, map_mul, map_inv]
      constructor
      · rintro ⟨hx1, hx2⟩
        exact ⟨P.mul_mem (P.mul_mem hg hx1) (P.inv_mem hg), (hfg _).1 hx2⟩
      · rintro ⟨hx1, hx2⟩
        refine ⟨?_, (hfg _).2 hx2⟩
        have := P.mul_mem (P.mul_mem (P.inv_mem hg) hx1) hg
        simpa [mul_assoc] using this
    have hKM : K ≤ M := by
      intro k hk
      obtain ⟨t, ht, htk⟩ := hk.2
      have h1 : k * t⁻¹ ∈ f.ker ⊓ P :=
        ⟨by simp [htk], P.mul_mem hk.1 (P.inv_mem (h.T_le ht))⟩
      have := M.mul_mem (hker h1) (h.le_M ht)
      simpa using this
    have h33 := three_three_a h.syl h.lt_P h.max hKP hKn hKM
    have hKT : K ⊓ T = T := inf_eq_right.2 hTK
    rw [hKT] at h33
    exact h.not_normal h33
  le_M := Subgroup.map_mono h.le_M
  lt_P := (map_maximal f h.lt_P (fun X hMX hXP => h.maximal hMX hXP) hker).1
  max := by
    intro X hTX hXP
    set Y : Subgroup G := P ⊓ X.comap f with hY
    have hTY : T ≤ Y := fun t ht => ⟨h.T_le ht, hTX (Subgroup.mem_map_of_mem f ht)⟩
    have hYP : Y < P := by
      refine lt_of_le_of_ne inf_le_left fun heq => hXP.not_ge ?_
      rintro _ ⟨p, hp, rfl⟩
      have : p ∈ Y := heq ▸ hp
      exact this.2
    have hYM := h.max Y hTY hYP
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hXP.le hx
    exact ⟨p, hYM ⟨hp, hx⟩, rfl⟩

theorem pCoreOf_map_eq_bot_of_ker_le (f : G →* H) {P T M : Subgroup G} (h : MinPar P T M)
    (hker : f.ker ⊓ P ≤ M) (hO2 : pCoreOf 2 P ≤ f.ker) : pCoreOf 2 (P.map f) = ⊥ := by
  have hNP : f.ker ⊓ P ≤ P := inf_le_right
  have hNn := normalizer_ker_inf f P
  have hnot : ¬ P ≤ T ⊔ f.ker ⊓ P := by
    intro hle
    have hTN : T ⊔ f.ker ⊓ P ≤ M := sup_le h.le_M hker
    exact h.lt_P.not_ge (hle.trans hTN)
  exact pCoreOf_map_eq_bot f h hNP hNn inf_le_left le_rfl hnot
    (fun x hx => ⟨hO2 hx, pCoreOf_le 2 P hx⟩)

end CFSG.CGT.PushingUpLit.BHS5
