module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Overgroups
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverSmall

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup CFSG.Open

variable {α : Type} [Fintype α] [DecidableEq α]

private theorem ao10_apply_eq_iff {σ : Perm α} {ω : α} (hσ : σ ω = ω) (x : α) :
    σ x = ω ↔ x = ω := by
  constructor
  · intro h
    apply σ.injective
    rw [h, hσ]
  · rintro rfl
    exact hσ

private theorem ao10_stab_fix {ω : α}
    (g : ↥(MulAction.stabilizer (↥(alternatingGroup α)) ω)) :
    (g.1 : Perm α) ω = ω :=
  MulAction.mem_stabilizer_iff.mp g.2

private def ao10_restr {ω : α}
    (g : ↥(MulAction.stabilizer (↥(alternatingGroup α)) ω)) : Perm {x // x ≠ ω} :=
  Equiv.Perm.subtypePerm (p := fun x => x ≠ ω) (g.1 : Perm α)
    (fun x => not_congr (ao10_apply_eq_iff (ao10_stab_fix g) x))

private theorem ao10_ofSubtype_restr {ω : α}
    (g : ↥(MulAction.stabilizer (↥(alternatingGroup α)) ω)) :
    Equiv.Perm.ofSubtype (ao10_restr g) = (g.1 : Perm α) := by
  unfold ao10_restr
  refine Equiv.Perm.ofSubtype_subtypePerm _ ?_
  intro x hx hxω
  exact hx (by rw [hxω]; exact ao10_stab_fix g)

private theorem ao10_sign_restr {ω : α}
    (g : ↥(MulAction.stabilizer (↥(alternatingGroup α)) ω)) :
    Equiv.Perm.sign (ao10_restr g) = 1 := by
  have h := Equiv.Perm.sign_ofSubtype (ao10_restr g)
  rw [ao10_ofSubtype_restr] at h
  rw [← h]
  exact Equiv.Perm.mem_alternatingGroup.mp g.1.2

private theorem ao10_restr_mem {ω : α}
    (g : ↥(MulAction.stabilizer (↥(alternatingGroup α)) ω)) :
    ao10_restr g ∈ alternatingGroup {x // x ≠ ω} :=
  Equiv.Perm.mem_alternatingGroup.mpr (ao10_sign_restr g)

private def ao10_fwd {ω : α}
    (g : ↥(MulAction.stabilizer (↥(alternatingGroup α)) ω)) :
    ↥(alternatingGroup {x // x ≠ ω}) :=
  ⟨ao10_restr g, ao10_restr_mem g⟩

private theorem ao10_ofSubtype_mem {ω : α} (τ : ↥(alternatingGroup {x // x ≠ ω})) :
    Equiv.Perm.ofSubtype τ.1 ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
  exact Equiv.Perm.mem_alternatingGroup.mp τ.2

private theorem ao10_ofSubtype_fix {ω : α} (τ : Perm {x // x ≠ ω}) :
    Equiv.Perm.ofSubtype τ ω = ω :=
  Equiv.Perm.ofSubtype_apply_of_not_mem τ (fun h => h rfl)

private def ao10_bwd {ω : α} (τ : ↥(alternatingGroup {x // x ≠ ω})) :
    ↥(MulAction.stabilizer (↥(alternatingGroup α)) ω) :=
  ⟨⟨Equiv.Perm.ofSubtype τ.1, ao10_ofSubtype_mem τ⟩,
    MulAction.mem_stabilizer_iff.mpr (ao10_ofSubtype_fix τ.1)⟩

private theorem ao10_left {ω : α}
    (g : ↥(MulAction.stabilizer (↥(alternatingGroup α)) ω)) :
    ao10_bwd (ao10_fwd g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  exact ao10_ofSubtype_restr g

private theorem ao10_right {ω : α} (τ : ↥(alternatingGroup {x // x ≠ ω})) :
    ao10_fwd (ao10_bwd τ) = τ := by
  apply Subtype.ext
  exact Equiv.Perm.subtypePerm_ofSubtype τ.1

private theorem ao10_mul {ω : α}
    (g h : ↥(MulAction.stabilizer (↥(alternatingGroup α)) ω)) :
    ao10_fwd (g * h) = ao10_fwd g * ao10_fwd h := by
  apply Subtype.ext
  exact Equiv.ext fun x => Subtype.ext rfl

theorem stab_alt_equiv (ω : α) :
    Nonempty (↥(MulAction.stabilizer (↥(alternatingGroup α)) ω) ≃*
      alternatingGroup {x // x ≠ ω}) :=
  ⟨{ toFun := ao10_fwd
     invFun := ao10_bwd
     left_inv := ao10_left
     right_inv := ao10_right
     map_mul' := ao10_mul }⟩

private theorem ao10_card {m : ℕ} (ω : Fin m) :
    Fintype.card {x : Fin m // x ≠ ω} = m - 1 := by
  have h1 : Fintype.card {x : Fin m // x ≠ ω} =
      Fintype.card (Fin m) - Fintype.card {x : Fin m // x = ω} :=
    Fintype.card_subtype_compl (fun x : Fin m => x = ω)
  rw [Fintype.card_subtype_eq ω, Fintype.card_fin] at h1
  exact h1

theorem stab_alt_equiv_fin {m : ℕ} (ω : Fin m) :
    Nonempty (↥(MulAction.stabilizer (↥(alternatingGroup (Fin m))) ω) ≃*
      alternatingGroup (Fin (m - 1))) := by
  obtain ⟨φ⟩ := stab_alt_equiv ω
  exact ⟨φ.trans (Equiv.altCongrHom (Fintype.equivFinOfCardEq (ao10_card ω)))⟩

theorem isSylowTwoOf_of_top {G : Type} [Group G] [Finite G] {T L : Subgroup G}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hTL : T ≤ L) :
    CFSG.QuasithinUnique.IsSylowTwoOf T L := by
  obtain ⟨-, hp, hodd⟩ := hT
  have h1 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
  have h2 : T.relIndex L * L.index = T.index := Subgroup.relIndex_mul_index hTL
  refine ⟨hTL, hp, fun h => hodd ?_⟩
  rw [h1, ← h2]
  exact Dvd.dvd.mul_right h L.index

private theorem ao11_even {Γ : Type} [Group Γ] [Finite Γ] {k : ℕ} (hk : 10 ≤ k) (hkev : Even k)
    (L T X K : Subgroup Γ) (eL : ↥L ≃* alternatingGroup (Fin k))
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T L) (hTX : T ≤ X) (hXL : X ≤ L) (hKX : K ≤ X)
    (hsub : CFSG.Open.IsSubnormal K X) (hK : CFSG.IsQuasisimple ↥K) :
    ∃ n, n ≤ k ∧ Nonempty (↥K ≃* alternatingGroup (Fin n)) := by
  obtain ⟨n, hnk, hIso⟩ := CFSG.QuasithinUnique.L246C127.alt_overgroups_even L T X K hk hkev
    ⟨eL⟩ hT hTX hXL hKX hsub (Or.inl hK)
  exact ⟨n, hnk, hIso⟩

private theorem ao11_eight {Γ : Type} [Group Γ] [Finite Γ]
    (L T X K : Subgroup Γ) (eL : ↥L ≃* alternatingGroup (Fin 8))
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T L) (hTX : T ≤ X) (hXL : X ≤ L) (hKX : K ≤ X)
    (hsub : CFSG.Open.IsSubnormal K X) (hK : CFSG.IsQuasisimple ↥K) :
    Nonempty (↥K ≃* alternatingGroup (Fin 8)) := by
  have hKL : K ≤ L := hKX.trans hXL
  have h5 : 5 ≤ Nat.card (Fin 8) := by simp
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup h5
  haveI hLs : IsSimpleGroup ↥L := eL.isSimpleGroup
  by_cases hXL' : X = L
  ·
    have hsubL : CFSG.Open.IsSubnormal K L := by
      rw [← hXL']
      exact hsub
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsubL hLs with h | h
    · exfalso
      have hnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK
      exact (Subgroup.nontrivial_iff_ne_bot K).1 hnt h
    · exact ⟨(MulEquiv.subgroupCongr h).trans eL⟩
  ·
    exfalso
    have hY : X.subgroupOf L ≠ ⊤ := fun htop =>
      hXL' (le_antisymm hXL (Subgroup.subgroupOf_eq_top.1 htop))
    have hOv : CFSG.QuasithinUnique.Bridge.Over.Overgroups ↥L :=
      CFSG.QuasithinUnique.Bridge.Over.Overgroups.of_mulEquiv eL.symm
        CFSG.QuasithinUnique.Bridge.Over.overgroups_alt_eight
    have hT' : CFSG.QuasithinUnique.IsSylowTwoOf (T.subgroupOf L) ⊤ := by
      refine ⟨le_top, ?_, ?_⟩
      · exact hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
      · change ¬ 2 ∣ (T.subgroupOf L).relIndex ⊤
        rw [Subgroup.relIndex_top_right]
        exact hT.2.2
    have hTY : T.subgroupOf L ≤ X.subgroupOf L := Subgroup.subgroupOf_mono L hTX
    have hKY : K.subgroupOf L ≤ X.subgroupOf L := Subgroup.subgroupOf_mono L hKX
    have hcharTwo := hOv (T.subgroupOf L) (X.subgroupOf L) hT' hTY hY
    have hsubK : CFSG.Open.IsSubnormal (K.subgroupOf L) (X.subgroupOf L) :=
      CFSG.Quasithin.A3.subnormal_comap L.subtype hsub
    have hqK : CFSG.IsQuasisimple ↥(K.subgroupOf L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL).symm hK
    exact CFSG.QuasithinUnique.Bridge.Over.false_of_charTwo hcharTwo hKY hsubK (Or.inl hqK)

theorem case_fix {m : ℕ} (hm : 9 ≤ m) (hmodd : Odd m)
    {T X K : Subgroup ↥(alternatingGroup (Fin m))} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    {ω : Fin m} (hTω : ∀ t ∈ T, (t : Perm (Fin m)) ω = ω) (hTX : T ≤ X) (hKX : K ≤ X)
    (hsub : CFSG.Open.IsSubnormal K X) (hK : CFSG.IsQuasisimple ↥K)
    (hKω : ∀ k ∈ K, (k : Perm (Fin m)) ω = ω) :
    ∃ n, n ≤ m ∧ Nonempty (↥K ≃* alternatingGroup (Fin n)) := by
  obtain ⟨eL⟩ := stab_alt_equiv_fin ω
  obtain ⟨L₀, hL₀⟩ : ∃ L : Subgroup ↥(alternatingGroup (Fin m)),
      L = MulAction.stabilizer (↥(alternatingGroup (Fin m))) ω := ⟨_, rfl⟩
  have hmem : ∀ x : ↥(alternatingGroup (Fin m)), x ∈ L₀ ↔ (x : Perm (Fin m)) ω = ω := by
    intro x
    subst hL₀
    exact Iff.rfl
  have eL' : ↥L₀ ≃* alternatingGroup (Fin (m - 1)) := by
    subst hL₀
    exact eL
  have hTL₀ : T ≤ L₀ := fun t ht => (hmem t).2 (hTω t ht)
  have hKL₀ : K ≤ L₀ := fun k hk => (hmem k).2 (hKω k hk)
  have hTL : CFSG.QuasithinUnique.IsSylowTwoOf T L₀ := isSylowTwoOf_of_top hT hTL₀
  have hTX₀ : T ≤ X ⊓ L₀ := le_inf hTX hTL₀
  have hKX₀ : K ≤ X ⊓ L₀ := le_inf hKX hKL₀
  have hsub₀ : CFSG.Open.IsSubnormal K (X ⊓ L₀) := by
    have h := CFSG.Quasithin.B113.isSubnormal_inf_of_le hsub (inf_le_left : X ⊓ L₀ ≤ X)
    rwa [inf_eq_right.2 hKX₀] at h
  rcases Nat.lt_or_ge m 11 with hlt | hge
  ·
    obtain rfl : m = 9 := by
      obtain ⟨j, hj⟩ := hmodd
      omega
    have eL8 : ↥L₀ ≃* alternatingGroup (Fin 8) := eL'
    exact ⟨8, by norm_num, ao11_eight L₀ T (X ⊓ L₀) K eL8 hTL hTX₀ inf_le_right hKX₀ hsub₀ hK⟩
  ·
    have hmev : Even (m - 1) := by
      obtain ⟨j, hj⟩ := hmodd
      exact ⟨j, by omega⟩
    obtain ⟨n, hn, hI⟩ := ao11_even (k := m - 1) (by omega) hmev L₀ T (X ⊓ L₀) K eL' hTL
      hTX₀ inf_le_right hKX₀ hsub₀ hK
    exact ⟨n, by omega, hI⟩

end CFSG.QuasithinUnique.L246C127.AltBig
