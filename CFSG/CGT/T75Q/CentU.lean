module

public import CFSG.CGT.T75Q.Comp
public import CFSG.CGT.T75Q.CentAdj
public import CFSG.CGT.T75Q.Endgame
public import CFSG.CGT.Timmesfeld75.Sec6Four
public import CFSG.CGT.Timmesfeld75.Sec66Stmt

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75P

variable {G : Type} [Group G]

@[expose] def uadj (T : Subgroup G) : Subgroup G :=
  T ⊔ ⨆ (k : G) (_ : conjSubgroup k T ≠ T ∧ normIn (conjSubgroup k T) T ≠ ⊥), conjSubgroup k T

theorem T_le_uadj (T : Subgroup G) : T ≤ uadj T := le_sup_left

theorem adj_le_uadj {T : Subgroup G} {k : G} (hne : conjSubgroup k T ≠ T)
    (hbot : normIn (conjSubgroup k T) T ≠ ⊥) : conjSubgroup k T ≤ uadj T :=
  le_sup_of_le_right (le_iSup₂_of_le k ⟨hne, hbot⟩ le_rfl)

section Main

variable {T T₁ : Subgroup G} {n : ℕ}

theorem two_dvd_card_of_ctx (hc : Sec6Ctx T T₁ n 1) (hn : 1 ≤ n) : 2 ∣ Nat.card T := by
  rw [hc.hT]
  exact dvd_pow (by norm_num) (by omega)

theorem exists_ne_one_of_ctx (hc : Sec6Ctx T T₁ n 1) : ∃ t ∈ T, t ≠ 1 := by
  have h4 := hc.hy.card
  by_contra hcon
  push Not at hcon
  have hT : T = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    exact Subgroup.mem_bot.2 (hcon t ht)
  rw [hT, Subgroup.card_bot] at h4
  omega

theorem h66_of_ctx (h66 : Sec66) (hc : Sec6Ctx T T₁ n 1) :
    ∀ x ∈ classD T, ∀ y ∈ classD T, orderOf (x * y) = 4 → (x * y) ^ 2 ∈ classD T :=
  fun x hx y hy h4 => h66 G T T₁ n 1 hc x hx y hy h4

theorem gammaD_le_centralizer (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) (h66 : Sec66)
    (hc : Sec6Ctx T T₁ n 1) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1) {k : ℕ}
    (ch : TransvChain n k) (hn : 3 ≤ n) {c : G}
    (hcC : c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) :
    ∀ d ∈ gammaD T, c * d = d * c := by
  have : Finite G := hc.finite
  obtain ⟨hTH, -, -⟩ := hSub_data T T₁
  have hWC : IsWC T := hc.hy.pair.wc
  have hcT : ∀ t ∈ T, c * t = t * c := fun t ht =>
    (Subgroup.mem_centralizer_iff.1 hcC t (hTH ht)).symm
  have hadjC : ∀ k' : G, conjSubgroup k' T ≠ T → normIn (conjSubgroup k' T) T ≠ ⊥ →
      ∀ u ∈ conjSubgroup k' T, c * u = u * c := by
    intro k' hne hbot' u hu
    have hbot : normIn T (conjSubgroup k' T) ≠ ⊥ := normIn_ne_bot_of_conj hWC hne hbot'
    have := centralizer_hSub_le_centralizer_adj h1 h62 h63 hc hnat ch hn hne hbot hcC
    exact (Subgroup.mem_centralizer_iff.1 this u hu).symm
  have hN : ∀ x ∈ normD T, x ∈ DeltaOf T (uadj T) :=
    hN_of_adj hWC hc.hS (T_le_uadj T) fun _ hne hbot' => adj_le_uadj hne hbot'
  have hUY : uadj T ≤ Subgroup.closure {d | d ∈ classD T ∧ c * d = d * c} := by
    refine sup_le ?_ (iSup₂_le fun k' hk' => ?_)
    · intro t ht
      by_cases ht1 : t = 1
      · rw [ht1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨mem_classD_of_mem ht ht1, hcT t ht⟩
    · intro u hu
      by_cases hu1 : u = 1
      · rw [hu1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure
          ⟨mem_classD_of_mem_conjSubgroup hu hu1, hadjC k' hk'.1 hk'.2 u hu⟩
  intro d hd
  obtain ⟨-, t, ht, ht1, hpath⟩ := hd
  induction hpath with
  | refl => exact hcT t ht
  | tail _ hbc ih =>
    exact closed_CD hWC hN (h66_of_ctx h66 hc) (T_le_uadj T) (exists_ne_one_of_ctx hc) hcT hUY
      hbc.1 ih hbc.2.1 hbc.2.2.symm

theorem hSub_le_ugen (hc : Sec6Ctx T T₁ n 1) (hn : 1 ≤ n) :
    hSub T (normIn T₁ T) ≤ ugen T := by
  have : Finite G := hc.finite
  have hWC : IsWC T := hc.hy.pair.wc
  refine hc.hSub_le_closure.trans ((Subgroup.closure_le _).2 fun x hx => ?_)
  exact gammaD_subset_ugen (normD_subset_gammaD hWC (two_dvd_card_of_ctx hc hn) hx)

theorem centralizer_hSub_eq_centralizer_ugen (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (h66 : Sec66) (hc : Sec6Ctx T T₁ n 1) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1)
    {k : ℕ} (ch : TransvChain n k) (hn : 3 ≤ n) :
    Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) =
      Subgroup.centralizer (ugen T : Set G) := by
  apply le_antisymm
  · intro c hcC
    have hle : ugen T ≤ Subgroup.centralizer ({c} : Set G) := by
      rw [ugen, Subgroup.closure_le]
      intro d hd
      exact Subgroup.mem_centralizer_singleton_iff.2
        (gammaD_le_centralizer h1 h62 h63 h66 hc hnat ch hn hcC d hd).symm
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hu)
  · exact Subgroup.centralizer_le (hSub_le_ugen hc (by omega))

theorem endHyp_ugen (hc : Sec6Ctx T T₁ n 1) (h66 : Sec66) (hn : 1 ≤ n)
    (hF1 : ∀ c ∈ Subgroup.centralizer (ugen T : Set G), c ≠ 1 → ∀ d ∈ classD T,
      c * d = d * c → d ∈ ugen T)
    (hZ : ∀ c ∈ ugen T ⊓ Subgroup.centralizer (ugen T : Set G), c * c = 1 → c = 1) :
    EndHyp T (ugen T) := by
  have : Finite G := hc.finite
  have hWC : IsWC T := hc.hy.pair.wc
  have hT2 := two_dvd_card_of_ctx hc hn
  have hT1 := exists_ne_one_of_ctx hc
  have hN := hN_ugen hWC hc.hS hT2
  have h66' := h66_of_ctx h66 hc
  refine ⟨hWC, h66', fun d hd hdU x hx hxd => ugen_closed hWC hN h66' hT1 hd hdU hx hxd, hF1, hZ,
    fun g h d hd hg hh => ?_, fun g d hd hdU hdg => ?_⟩
  · rw [conjSubgroup_ugen_eq hWC hN h66' hT1 hd hg hh]
  · have h1 : d ∈ conjSubgroup 1 (ugen T) := by rwa [conjSubgroup_one]
    rw [conjSubgroup_ugen_eq hWC hN h66' hT1 hd hdg h1, conjSubgroup_one]

end Main

end CFSG.CGT.T75Q
