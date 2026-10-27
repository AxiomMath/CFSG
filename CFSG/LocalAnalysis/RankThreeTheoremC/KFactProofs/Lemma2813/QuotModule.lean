module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.FixPoints
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

section A2

theorem qm_GL32_isPerfect : Group.IsPerfect GL32 := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  exact Group.IsPerfect.ofSurjective (f := (slEquivGL 3).toMonoidHom) (slEquivGL 3).surjective

theorem qm_hom_zero {A : Type*} [AddCommGroup A] (c : GL32 → A)
    (hc : ∀ g h, c (g * h) = c g + c h) (g : GL32) : c g = 0 := by
  have h1 : c 1 = 0 := by
    have h := hc 1 1
    rw [mul_one] at h
    exact add_left_cancel (a := c 1) (by rw [add_zero]; exact h.symm)
  let f : GL32 →* Multiplicative A :=
    { toFun := fun g => Multiplicative.ofAdd (c g)
      map_one' := by
        show Multiplicative.ofAdd (c 1) = Multiplicative.ofAdd 0
        rw [h1]
      map_mul' := fun g h => congrArg Multiplicative.ofAdd (hc g h) }
  have hle : commutator GL32 ≤ f.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  have hmem : g ∈ commutator GL32 := by
    rw [Group.isPerfect_def.mp qm_GL32_isPerfect]
    exact mem_top g
  have hg : f g = 1 := hle hmem
  exact congrArg Multiplicative.toAdd hg

@[expose] noncomputable def qm_qend {N : Type} [AddCommGroup N] [DistribMulAction GL32 N]
    (g : GL32) :
    N ⧸ fixSub N ⊤ →+ N ⧸ fixSub N ⊤ :=
  QuotientAddGroup.map (fixSub N ⊤) (fixSub N ⊤) (DistribSMul.toAddMonoidHom N g)
    (fun x hx => by
      show g • x ∈ fixSub N ⊤
      rw [(mem_fixSub).1 hx g (mem_top g)]
      exact hx)

theorem qm_qend_mk {N : Type} [AddCommGroup N] [DistribMulAction GL32 N] (g : GL32) (n : N) :
    qm_qend g (QuotientAddGroup.mk n : N ⧸ fixSub N ⊤) = QuotientAddGroup.mk (g • n) :=
  rfl

theorem qm_qend_one {N : Type} [AddCommGroup N] [DistribMulAction GL32 N]
    (x : N ⧸ fixSub N ⊤) : qm_qend 1 x = x := by
  induction x using QuotientAddGroup.induction_on with
  | H n => rw [qm_qend_mk, one_smul]

theorem qm_qend_mul {N : Type} [AddCommGroup N] [DistribMulAction GL32 N] (g h : GL32)
    (x : N ⧸ fixSub N ⊤) : qm_qend (g * h) x = qm_qend g (qm_qend h x) := by
  induction x using QuotientAddGroup.induction_on with
  | H n => rw [qm_qend_mk, qm_qend_mk, qm_qend_mk, mul_smul]

theorem qm_mem_fixSub_top {N : Type} [AddCommGroup N] [DistribMulAction GL32 N] (n : N)
    (h : ∀ g : GL32, g • n - n ∈ fixSub N ⊤) : n ∈ fixSub N ⊤ := by
  have hc : ∀ g h' : GL32, (g * h') • n - n = (g • n - n) + (h' • n - n) := by
    intro g h'
    have h1 : g • (h' • n - n) = h' • n - n := (mem_fixSub.1 (h h')) g (mem_top g)
    rw [smul_sub] at h1
    rw [mul_smul]
    calc g • h' • n - n = (g • h' • n - g • n) + (g • n - n) := by abel
      _ = (h' • n - n) + (g • n - n) := by rw [h1]
      _ = (g • n - n) + (h' • n - n) := by abel
  have h0 := qm_hom_zero (A := fixSub N ⊤) (fun g => ⟨g • n - n, h g⟩)
    (fun g h' => Subtype.ext (hc g h'))
  intro g _
  have := congrArg Subtype.val (h0 g)
  exact sub_eq_zero.1 this

theorem exists_quot_module {N : Type} [AddCommGroup N] [Finite N] [DistribMulAction GL32 N]
    (h2 : ∀ n : N, n + n = 0) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Finite M) (_ : DistribMulAction GL32 M) (π : N →+ M),
      Function.Surjective π ∧ (∀ n, π n = 0 ↔ n ∈ fixSub N ⊤) ∧
      (∀ (g : GL32) (n : N), π (g • n) = g • π n) ∧ (∀ m : M, m + m = 0) ∧
      (∀ m : M, (∀ g : GL32, g • m = m) → m = 0) := by
  letI : DistribMulAction GL32 (N ⧸ fixSub N ⊤) :=
    { smul := fun g x => qm_qend g x
      one_smul := qm_qend_one
      mul_smul := qm_qend_mul
      smul_zero := fun g => map_zero (qm_qend g)
      smul_add := fun g x y => map_add (qm_qend g) x y }
  have hsmul : ∀ (g : GL32) (n : N),
      g • (QuotientAddGroup.mk n : N ⧸ fixSub N ⊤) = QuotientAddGroup.mk (g • n) :=
    fun g n => rfl
  refine ⟨N ⧸ fixSub N ⊤, inferInstance, inferInstance, inferInstance, QuotientAddGroup.mk' _,
    QuotientAddGroup.mk'_surjective _, fun n => ?_, fun g n => rfl, fun m => ?_, fun m hm => ?_⟩
  · exact QuotientAddGroup.eq_zero_iff n
  · induction m using QuotientAddGroup.induction_on with
    | H n =>
      rw [← QuotientAddGroup.mk_add, h2, QuotientAddGroup.mk_zero]
  · induction m using QuotientAddGroup.induction_on with
    | H n =>
      rw [QuotientAddGroup.eq_zero_iff]
      refine qm_mem_fixSub_top n fun g => ?_
      have h3 := hm g
      rw [hsmul] at h3
      exact QuotientAddGroup.eq_iff_sub_mem.1 h3

theorem quot_index_le {N M : Type} [AddCommGroup N] [Finite N] [DistribMulAction GL32 N]
    [AddCommGroup M] [Finite M] [DistribMulAction GL32 M] {π : N →+ M}
    (hπs : Function.Surjective π) (hπk : ∀ n, π n = 0 ↔ n ∈ fixSub N ⊤)
    (hπe : ∀ (g : GL32) (n : N), π (g • n) = g • π n) (H : Subgroup GL32) :
    Nat.card M * Nat.card (fixSub N H) ≤ Nat.card N * Nat.card (fixSub M H) := by
  let φ : fixSub N H →+ fixSub M H :=
    (π.comp (fixSub N H).subtype).codRestrict (fixSub M H) (fun x g hg => by
      show g • π x = π x
      rw [← hπe, x.2 g hg])
  have h1 := AddSubgroup.card_ker_mul_card_range φ
  have hker : Nat.card φ.ker ≤ Nat.card (fixSub N ⊤) := by
    have hmem : ∀ x : φ.ker, (x.1 : N) ∈ fixSub N ⊤ := fun x => by
      have h0 : φ x.1 = 0 := x.2
      have h3 : π (x.1 : N) = 0 := congrArg Subtype.val h0
      exact (hπk _).1 h3
    refine Nat.card_le_card_of_injective (fun x => (⟨(x.1 : N), hmem x⟩ : fixSub N ⊤)) ?_
    intro x y hxy
    have h3 : (x.1 : N) = (y.1 : N) := by
      have := congrArg Subtype.val hxy
      exact this
    exact Subtype.ext (Subtype.ext h3)
  have hrange : Nat.card φ.range ≤ Nat.card (fixSub M H) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have h2 : Nat.card (fixSub N ⊤) * Nat.card M = Nat.card N := by
    have h3 := AddSubgroup.card_ker_mul_card_of_surjective hπs
    have h4 : π.ker = fixSub N ⊤ := by
      ext n
      exact hπk n
    rw [h4] at h3
    exact h3
  calc Nat.card M * Nat.card (fixSub N H)
      = Nat.card M * (Nat.card φ.ker * Nat.card φ.range) := by rw [h1]
    _ ≤ Nat.card M * (Nat.card (fixSub N ⊤) * Nat.card (fixSub M H)) := by gcongr
    _ = (Nat.card (fixSub N ⊤) * Nat.card M) * Nat.card (fixSub M H) := by ring
    _ = Nat.card N * Nat.card (fixSub M H) := by rw [h2]

theorem card_commSub_le_of_quot {N M : Type} [AddCommGroup N] [Finite N] [DistribMulAction GL32 N]
    [AddCommGroup M] [Finite M] [DistribMulAction GL32 M] {π : N →+ M}
    (hπk : ∀ n, π n = 0 ↔ n ∈ fixSub N ⊤) (hπe : ∀ (g : GL32) (n : N), π (g • n) = g • π n)
    (h2 : ∀ n : N, n + n = 0) {d : GL32} (hd : orderOf d = 3) :
    Nat.card (commSub N (zpowers d)) ≤ Nat.card (commSub M (zpowers d)) := by
  have hle : commSub N (zpowers d) ≤ (commSub M (zpowers d)).comap π := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨g, hg, n, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, map_sub, hπe]
    exact AddSubgroup.subset_closure ⟨g, hg, π n, rfl⟩
  refine Nat.card_le_card_of_injective
    (fun x : commSub N (zpowers d) => (⟨π x.1, hle x.2⟩ : commSub M (zpowers d))) ?_
  intro a b hab
  have hab' : π a.1 = π b.1 := congrArg Subtype.val hab
  have hmem : a.1 - b.1 ∈ commSub N (zpowers d) ⊓ fixSub N (zpowers d) :=
    AddSubgroup.mem_inf.2 ⟨AddSubgroup.sub_mem _ a.2 b.2,
      fixSub_mono (M := N) (le_top : zpowers d ≤ ⊤)
        ((hπk _).1 (by rw [map_sub, hab', sub_self]))⟩
  rw [commSub_inf_fixSub h2 hd, AddSubgroup.mem_bot] at hmem
  exact Subtype.ext (sub_eq_zero.1 hmem)

theorem smul_ne_of_quot {N M : Type} [AddCommGroup N] [Finite N] [DistribMulAction GL32 N]
    [AddCommGroup M] [Finite M] [DistribMulAction GL32 M] {π : N →+ M}
    (hπk : ∀ n, π n = 0 ↔ n ∈ fixSub N ⊤) (hπe : ∀ (g : GL32) (n : N), π (g • n) = g • π n)
    (h2 : ∀ n : N, n + n = 0) {d : GL32} (hd : orderOf d = 3) {n : N} (hn : d • n ≠ n) :
    d • π n ≠ π n := by
  intro hdn
  apply hn
  have h0 : π (d • n - n) = 0 := by rw [map_sub, hπe, hdn, sub_self]
  have hmem : d • n - n ∈ commSub N (zpowers d) ⊓ fixSub N (zpowers d) :=
    AddSubgroup.mem_inf.2 ⟨AddSubgroup.subset_closure ⟨d, mem_zpowers d, n, rfl⟩,
      fixSub_mono (M := N) (le_top : zpowers d ≤ ⊤) ((hπk _).1 h0)⟩
  rw [commSub_inf_fixSub h2 hd, AddSubgroup.mem_bot] at hmem
  exact sub_eq_zero.1 hmem

end A2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
