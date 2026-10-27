module

public import CFSG.Literature.GL52LocalCheck
public import CFSG.Literature.GL52Counts
public import CFSG.Literature.GL52Group

public section

namespace CFSG.Literature.GL52

open CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

theorem rep_tbl' (g : G) : Rep 31 (tbl g) (glPerm g) := (rep_iff_rep_glPerm _ _).1 (rep_tbl g)

theorem orderOf_of_tbl {g : G} {m : ℕ} (hm : 0 < m) (h : ordTest 31 m (tbl g) = true) :
    orderOf g = m := by
  rw [← orderOf_glPerm]
  exact (ordTest_iff' (rep_tbl' g) hm).1 h

theorem fixCount_eq_fpT (g : G) : fixCount g = fpT (tbl g) := (fpT_eq_card _ _ (rep_tbl' g)).symm

theorem commute_of_cmtT {g h : G} (hc : cmtT (tbl g) (tbl h) = true) : g * h = h * g :=
  (glPerm_comm_iff g h).1 ((cmtT_iff (rep_tbl' g) (rep_tbl' h)).1 hc)

theorem commDim_eq_of_fixCount {x : G} {d k : ℕ} (hk : 1 + k = 2 ^ (5 - d)) (hd : d ≤ 5)
    (h : fixCount x = k) : commDim x = d := by
  have h1 := two_pow_commDim x
  rw [h, hk] at h1
  have h2 := Nat.pow_right_injective (le_refl 2) h1
  have h3 : commDim x ≤ 5 := by
    exact Matrix.rank_le_width ((x : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1)
  omega

theorem commute_of_all {l : List G} {x : G} (h : l.all (fun g => cmtT (tbl g) (tbl x)) = true) :
    ∀ g ∈ l, g * x = x * g := by
  rw [List.all_eq_true] at h
  exact fun g hg => commute_of_cmtT (h g hg)

theorem orderOf_tau1
    : orderOf glTau1 = 3 := orderOf_of_tbl (by norm_num) orders_check.2.2.1
theorem orderOf_tau2
    : orderOf glTau2 = 3 := orderOf_of_tbl (by norm_num) orders_check.2.2.2.1
theorem fixCount_tau1
    : fixCount glTau1 = 1 := by rw [fixCount_eq_fpT]; exact fix_check.2.2.1
theorem fixCount_tau2
    : fixCount glTau2 = 7 := by rw [fixCount_eq_fpT]; exact fix_check.2.2.2

theorem inf_eq_bot_of_not_mem {x : G} {p : ℕ} (hp : p.Prime) (hx : orderOf x = p)
    {K : Subgroup G} (hK : x ∉ K) : Subgroup.zpowers x ⊓ K = ⊥ := by
  have hd := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers x ⊓ K ≤ Subgroup.zpowers x)
  rw [Nat.card_zpowers, hx] at hd
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    apply hK
    have he : Subgroup.zpowers x ⊓ K = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, Nat.card_zpowers, hx])
    exact (he ▸ inf_le_right : Subgroup.zpowers x ≤ K) (Subgroup.mem_zpowers x)

theorem zpowers_le_centralizer (x : G) : Subgroup.zpowers x ≤ Subgroup.centralizer {x} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.closure_le, Set.singleton_subset_iff,
    SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]

theorem lkHom_range_le_centralizer {Q : Type*} [Group Q] {K : Type} [DecidableEq K]
    {gs : List G} {key : Q → K} {L : List (K × List ℤ)} (h : lkMulOK gs key L) {x : G}
    (hc : gs.all (fun g => cmtT (tbl g) (tbl x)) = true) :
    (lkHom gs key L h).range ≤ Subgroup.centralizer {x} :=
  lkHom_range_le gs key L h fun g hg => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_of_all hc g hg

abbrev subK1 : Subgroup G := homK1.range

abbrev subK2 : Subgroup G := homK2.range

theorem tau1_not_mem :
    glTau1 ∉ subK1 := by
  rintro ⟨σ, hσ⟩
  have h1 := rep_lkTable gensK1 keyA5 tblA5 σ
  rw [← lkHom_apply _ _ _ mulOK_K1] at h1
  change Rep 31 _ (homK1 σ) at h1
  rw [hσ] at h1
  have := (tblEq_iff_eq' ((rep_iff_rep_glPerm _ _).1 h1) (rep_tbl' glTau1)).2 rfl
  have hc : tblEq 31 (lkTable gensK1 keyA5 tblA5 σ) (tbl glTau1) = false := notMem_check.1 σ
  rw [hc] at this
  exact Bool.false_ne_true this

theorem tau2_not_mem :
    glTau2 ∉ subK2 := by
  rintro ⟨σ, hσ⟩
  have h1 := rep_lkTable gensK2 keyGL3 tblGL3 σ
  rw [← lkHom_apply _ _ _ mulOK_K2] at h1
  change Rep 31 _ (homK2 σ) at h1
  rw [hσ] at h1
  have := (tblEq_iff_eq' ((rep_iff_rep_glPerm _ _).1 h1) (rep_tbl' glTau2)).2 rfl
  have hc : tblEq 31 (lkTable gensK2 keyGL3 tblGL3 σ) (tbl glTau2) = false := notMem_check.2 σ
  rw [hc] at this
  exact Bool.false_ne_true this

theorem card_subK1 : Nat.card subK1 = 60 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective homK1_injective).toEquiv,
    nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem card_subK2 : Nat.card subK2 = 168 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective homK2_injective).toEquiv]
  exact CFSG.LocalAnalysis.ComponentInitial.card_GL_three_zmod_two

theorem tau1_structure :
    subK1 ≤ Subgroup.centralizer {glTau1} ∧ Subgroup.zpowers glTau1 ⊓ subK1 = ⊥ ∧
      Subgroup.zpowers glTau1 ⊔ subK1 = Subgroup.centralizer {glTau1} ∧
      Nonempty (subK1 ≃* alternatingGroup (Fin 5)) := by
  have hle : subK1 ≤ Subgroup.centralizer {glTau1} :=
    lkHom_range_le_centralizer mulOK_K1 comm_check.2.1
  have hinf := inf_eq_bot_of_not_mem Nat.prime_three orderOf_tau1 tau1_not_mem
  refine ⟨hle, hinf, sup_eq_of_card (zpowers_le_centralizer _) hle hinf ?_,
    ⟨(MonoidHom.ofInjective homK1_injective).symm⟩⟩
  rw [card_centralizer_tau1, Nat.card_zpowers, orderOf_tau1, card_subK1]

theorem tau2_structure :
    subK2 ≤ Subgroup.centralizer {glTau2} ∧ Subgroup.zpowers glTau2 ⊓ subK2 = ⊥ ∧
      Subgroup.zpowers glTau2 ⊔ subK2 = Subgroup.centralizer {glTau2} ∧
      Nonempty (subK2 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) ∧
      Nonempty (subK2 ≃* GL (Fin 3) (ZMod 2)) := by
  have hle : subK2 ≤ Subgroup.centralizer {glTau2} :=
    lkHom_range_le_centralizer mulOK_K2 comm_check.2.2.1
  have hinf := inf_eq_bot_of_not_mem Nat.prime_three orderOf_tau2 tau2_not_mem
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  refine ⟨hle, hinf, sup_eq_of_card (zpowers_le_centralizer _) hle hinf ?_,
    ⟨(MonoidHom.ofInjective homK2_injective).symm.trans e⟩,
    ⟨(MonoidHom.ofInjective homK2_injective).symm⟩⟩
  rw [card_centralizer_tau2, Nat.card_zpowers, orderOf_tau2, card_subK2]

end CFSG.Literature.GL52
