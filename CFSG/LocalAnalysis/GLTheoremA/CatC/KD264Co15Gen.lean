module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporHN3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem glaPComponent_of_simple_bound {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {C F L : Subgroup G} (hFC : F ≤ C) (hFcen : ∀ f ∈ F, ∀ c ∈ C, f * c = c * f) (hLC : L ≤ C)
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hcard : Nat.card C ≤ Nat.card F * Nat.card L) (hpL : p ∣ Nat.card L) :
    GLAPComponent p C L := by
  haveI := hs
  have hFN : F ≤ Subgroup.normalizer (L : Set G) := by
    intro f hf
    have hc : ∀ l ∈ L, f * l * f⁻¹ = l := fun l hl => by rw [hFcen f hf l (hLC hl)]; group
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl; rw [hc l hl]; exact hl
    · intro hl
      have e := hFcen f hf _ (hLC hl)
      have : f * l * f⁻¹ = l := by
        have h2 : f * (f * l * f⁻¹) = f * l := by rw [e]; group
        exact mul_left_cancel h2
      rw [this] at hl
      exact hl
  have hinf : Nat.card ↥(F ⊓ L) = 1 := by
    suffices hb : F ⊓ L = ⊥ by rw [hb, Subgroup.card_bot]
    refine (eq_bot_iff (a := F ⊓ L)).2 fun x hx => ?_
    obtain ⟨hxF, hxL⟩ := Subgroup.mem_inf.1 hx
    have hmem : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (hFcen x hxF b (hLC b.2)).symm
    rw [Seven.center_eq_bot_of_simple hnab, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)
  have hprod := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer hFN
  rw [hinf, mul_one] at hprod
  have hsup : F ⊔ L = C :=
    Subgroup.eq_of_le_of_card_ge (sup_le hFC hLC) (by rw [hprod]; exact hcard)
  have hCN : C ≤ Subgroup.normalizer (L : Set G) := hsup ▸ sup_le hFN Subgroup.le_normalizer
  have hperf : commutator ↥L = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥L) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [← commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    · exact h
  exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp
    (Seven.isQuasisimple_of_simple hperf hnab) hpL hLC
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hLC).2 hCN)

theorem isSimpleGroup_of_perfect_card_sixty {H : Type} [Group H] [Finite H]
    (hperf : commutator H = ⊤) (h60 : Nat.card H = 60) : IsSimpleGroup H := by
  have hnt : Nontrivial H := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨N, hNn, hNt, hmax⟩ :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148K.exists_maximal_normal_ne_top H hnt
  haveI := hNn
  have hntQ : Nontrivial (H ⧸ N) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hNt
    rw [eq_top_iff]
    intro x _
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  haveI hs : IsSimpleGroup (H ⧸ N) := Seven.isSimpleGroup_quotient_of_max hntQ hmax
  have hperfQ : commutator (H ⧸ N) = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N), ← Subgroup.map_commutator, ← commutator_def, hperf]
  have hnab : ∃ a b : H ⧸ N, a * b ≠ b * a := Seven.exists_not_comm_of_perfect hperfQ hntQ
  have hns : ¬ Group.IsSolvable (H ⧸ N) := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 h) a b)
  have hge : 60 ≤ Nat.card (H ⧸ N) := by
    by_contra h
    exact hns (CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega))
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hN0 : 0 < Nat.card N := Nat.card_pos
  have hN1 : Nat.card N = 1 := by
    rw [h60] at hcard
    nlinarith
  have hNbot : N = ⊥ := (Subgroup.eq_bot_iff_card N).2 hN1
  subst hNbot
  exact (QuotientGroup.quotientBot (G := H)).symm.isSimpleGroup

theorem le_of_comm_of_card {G : Type} [Group G] [Finite G] {p m : ℕ} {Q A0 A : Subgroup G}
    (hidx : A0.relIndex Q = p) (hp0 : p ≠ 0) (hAQ : A ≤ Q)
    (hcen : ∀ r ∈ Q, r ∉ A0 → Nat.card ↥(A0 ⊓ Subgroup.centralizer ({r} : Set G)) ≤ m)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hbig : p * m < Nat.card A) : A ≤ A0 := by
  intro r hr
  by_contra hnot
  have hle : A0 ⊓ A ≤ A0 ⊓ Subgroup.centralizer ({r} : Set G) := fun x hx =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, Subgroup.mem_centralizer_singleton_iff.2
      (hA x (Subgroup.mem_inf.1 hx).2 r hr)⟩
  have h1 : Nat.card ↥(A0 ⊓ A) ≤ m :=
    (Subgroup.card_le_of_le hle).trans (hcen r (hAQ hr) hnot)
  have h2 : A0.relIndex A ≤ p := by
    rw [← hidx]
    exact Subgroup.relIndex_le_of_le_right hAQ (by rw [hidx]; exact hp0)
  have h3 := Subgroup.relIndex_mul_card A0 A
  have : Nat.card A ≤ p * m := by
    rw [← h3]
    exact Nat.mul_le_mul h2 h1
  omega

theorem exists_conj_le_of_full {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q A : Subgroup G} (hQ : Nat.card Q = p ^ (Nat.card G).factorization p) (hA : IsPGroup p A) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ Q := by
  obtain ⟨P, hAP⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P (Sylow.ofCard Q hQ)
  refine ⟨g, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have : g * a * g⁻¹ ∈ ((g • P : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨a, hAP ha, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  rw [hg] at this
  exact this

theorem card_inf_centralizer_le {G : Type} [Group G] [Finite G] {A0 : Subgroup G} {r : G}
    {n : ℕ} (e : ℕ → G) (hcov : ∀ x ∈ A0, ∃ k < n, e k = x) (S : Finset ℕ)
    (hmem : ∀ k < n, e k * r = r * e k → k ∈ S) :
    Nat.card ↥(A0 ⊓ Subgroup.centralizer ({r} : Set G)) ≤ S.card := by
  classical
  have hsub : ((A0 ⊓ Subgroup.centralizer ({r} : Set G) : Subgroup G) : Set G) ⊆
      ((S.image e : Finset G) : Set G) := by
    intro x hx
    obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨k, hk, rfl⟩ := hcov x hxA
    rw [Finset.coe_image]
    exact ⟨k, hmem k hk (Subgroup.mem_centralizer_singleton_iff.1 hxC), rfl⟩
  calc Nat.card ↥(A0 ⊓ Subgroup.centralizer ({r} : Set G))
      = ((A0 ⊓ Subgroup.centralizer ({r} : Set G) : Subgroup G) : Set G).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ((S.image e : Finset G) : Set G).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (S.image e).card := Set.ncard_coe_finset _
    _ ≤ S.card := Finset.card_image_le

theorem comp_of_perfect_sixty {G : Type} [Group G] [Finite G] {F L : Subgroup G}
    (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hLC : L ≤ Subgroup.centralizer (F : Set G))
    (hperf : L ≤ ⁅L, L⁆) (h60 : Nat.card L = 60)
    (hcard : Nat.card (Subgroup.centralizer (F : Set G)) ≤ Nat.card F * 60) :
    GLAPComponent 5 (Subgroup.centralizer (F : Set G)) L := by
  have hperfL : commutator ↥L = ⊤ := Seven.commutator_eq_top_of_le hperf
  haveI hs : IsSimpleGroup ↥L := isSimpleGroup_of_perfect_card_sixty hperfL h60
  have hnt : Nontrivial ↥L := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  refine glaPComponent_of_simple_bound (F := F) (L := L) Nat.prime_five ?_ ?_ hLC hs
    (Seven.exists_not_comm_of_perfect hperfL hnt) (by rw [h60]; exact hcard)
    (by rw [h60]; norm_num)
  · intro f hf
    exact Subgroup.mem_centralizer_iff.2 fun h hh => hFab h hh f hf
  · intro f hf c hc
    exact Subgroup.mem_centralizer_iff.1 hc f hf

theorem kd264RowData_of_A0 {G : Type} [Group G] [Finite G] {Q A0 F1 F2 : Subgroup G}
    (hQ : Nat.card Q = 5 ^ (Nat.card G).factorization 5) (hidx : A0.relIndex Q = 5)
    (hA0 : IsElemAbelian 5 A0) (hA0c : Nat.card A0 = 125)
    (hcen : ∀ r ∈ Q, r ∉ A0 → Nat.card ↥(A0 ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 5)
    (hF1 : F1 ≤ A0) (hF1c : Nat.card F1 = 5)
    (hJ1 : ∃ J : Subgroup G, GLAPComponent 5 (Subgroup.centralizer (F1 : Set G)) J)
    (hF2 : F2 ≤ A0) (hF2c : Nat.card F2 = 25)
    (hJ2 : ∃ J : Subgroup G, GLAPComponent 5 (Subgroup.centralizer (F2 : Set G)) J) :
    KD264RowData 5 G := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro A hA hmax k hk1 hk2 _
  have h125 : 125 ≤ Nat.card A := hA0c ▸ hmax _ hA0
  obtain ⟨g, hg⟩ := exists_conj_le_of_full hQ (isPGroup_of_isElemAbelian hA)
  have hA'el : IsElemAbelian 5 (A.map (MulAut.conj g).toMonoidHom) := hA.map _
  have hA'card : Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hA'le : A.map (MulAut.conj g).toMonoidHom ≤ A0 := le_of_comm_of_card hidx (by norm_num) hg
    hcen (fun x hx y hy => congrArg Subtype.val (hA'el.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (by rw [hA'card]; omega)
  have hA'eq : A.map (MulAut.conj g).toMonoidHom = A0 :=
    Subgroup.eq_of_le_of_card_ge hA'le (by rw [hA0c, hA'card]; exact h125)
  obtain ⟨F0, hF0, hF0c, J, hJ⟩ : ∃ F0 : Subgroup G, F0 ≤ A0 ∧ Nat.card F0 = 5 ^ k ∧
      ∃ J : Subgroup G, GLAPComponent 5 (Subgroup.centralizer (F0 : Set G)) J := by
    interval_cases k
    · exact ⟨F1, hF1, by rw [hF1c, pow_one], hJ1⟩
    · exact ⟨F2, hF2, by rw [hF2c]; norm_num, hJ2⟩
  refine ⟨F0.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, J.map (MulAut.conj g⁻¹).toMonoidHom, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxA' : x ∈ A.map (MulAut.conj g).toMonoidHom := hA'eq ▸ hF0 hx
    obtain ⟨a, ha, rfl⟩ := hxA'
    show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ ∈ A
    have e : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := by group
    rw [e]
    exact ha
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hF0c]
  · rw [← HN3.map_conj_centralizer_sub]
    exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_five
      (MulAut.conj g⁻¹) hJ

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15
