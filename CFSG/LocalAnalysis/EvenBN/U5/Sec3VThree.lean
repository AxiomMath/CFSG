module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3VTwo

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem mem_centralizer_of_displacement [Finite G] {A X N : Subgroup G} {c : G}
    (hA : IsPGroup 2 A) (hX : Odd (Nat.card X)) (hXA : X ≤ normalizer (A : Set G))
    (hn : A ≤ normalizer ((A ⊓ centralizer (X : Set G) : Subgroup G) : Set G))
    (hcX : c ∈ centralizer (X : Set G)) (hNA : ∀ n ∈ N, ∀ a ∈ A, n * a = a * n)
    (hXN : ∀ x ∈ X, ∀ n ∈ N, x * n = n * x) (hδ : ∀ a ∈ A, a⁻¹ * (c * a * c⁻¹) ∈ N)
    (hfix : ∀ a ∈ A ⊓ centralizer (X : Set G), c * a = a * c) :
    c ∈ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX2 : ¬ 2 ∣ Nat.card X := fun h2 => (Nat.not_even_iff_odd.2 hX) (even_iff_two_dvd.2 h2)
  obtain ⟨hsup, -⟩ := yamada_sup_eq hA hX2 hXA hn
  have hmul : ∀ a ∈ A, ∀ b ∈ A, (a * b)⁻¹ * (c * (a * b) * c⁻¹) =
      (a⁻¹ * (c * a * c⁻¹)) * (b⁻¹ * (c * b * c⁻¹)) := by
    intro a ha b hb
    have e : (a * b)⁻¹ * (c * (a * b) * c⁻¹) =
        b⁻¹ * (a⁻¹ * (c * a * c⁻¹)) * b * (b⁻¹ * (c * b * c⁻¹)) := by group
    rw [e, mul_assoc b⁻¹, hNA _ (hδ a ha) b hb, inv_mul_cancel_left]
  have hinv : ∀ a ∈ A, a⁻¹⁻¹ * (c * a⁻¹ * c⁻¹) = (a⁻¹ * (c * a * c⁻¹))⁻¹ := by
    intro a ha
    have h1 := hmul a ha a⁻¹ (inv_mem ha)
    rw [mul_inv_cancel, inv_one, one_mul, mul_one, mul_inv_cancel] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hcomm : ⁅X, A⁆ ≤ centralizer ({c} : Set G) := by
    refine commutator_le.2 fun x hx a ha => ?_
    have hxa : x * a * x⁻¹ ∈ A := (mem_normalizer_iff.1 (hXA hx) a).1 ha
    have hcx : c * x = x * c := (mem_centralizer_iff.1 hcX x hx).symm
    have hconj : (x * a * x⁻¹)⁻¹ * (c * (x * a * x⁻¹) * c⁻¹) = a⁻¹ * (c * a * c⁻¹) := by
      have hc' : x⁻¹ * c * x = c := by rw [mul_assoc, hcx, inv_mul_cancel_left]
      have e : (x * a * x⁻¹)⁻¹ * (c * (x * a * x⁻¹) * c⁻¹) =
          x * (a⁻¹ * ((x⁻¹ * c * x) * a * (x⁻¹ * c * x)⁻¹)) * x⁻¹ := by group
      rw [e, hc', hXN x hx _ (hδ a ha), mul_inv_cancel_right]
    have key : (⁅x, a⁆)⁻¹ * (c * ⁅x, a⁆ * c⁻¹) = 1 := by
      rw [commutatorElement_def, hmul _ hxa _ (inv_mem ha), hconj, hinv a ha, mul_inv_cancel]
    rw [mem_centralizer_singleton_iff]
    have e : c * ⁅x, a⁆ * c⁻¹ = ⁅x, a⁆ := (inv_mul_eq_one.1 key).symm
    calc ⁅x, a⁆ * c = c * ⁅x, a⁆ * c⁻¹ * c := by rw [e]
      _ = c * ⁅x, a⁆ := by group
  have hle : A ≤ centralizer ({c} : Set G) := by
    rw [← hsup]
    refine sup_le (fun a ha => mem_centralizer_singleton_iff.2 (hfix a ha).symm) hcomm
  exact mem_centralizer_iff.2 fun a ha => mem_centralizer_singleton_iff.1 (hle ha)

end Generic

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem I₅sub_le_I₃sub : I₅sub h ≤ I₃sub h := fun t ht => by
  obtain ⟨htI, h1, h2⟩ := mem_I₅sub.1 ht
  exact mem_I₃sub.2 ⟨htI, h1.trans h2⟩

theorem ZPsub_le_patSub_I₅ : ZPsub h ≤ patSub h sI₅ isPattern_sI₅ :=
  patSub_mono _ _ (by decide)

theorem mat_zf₁_of_patSub_I₅ {g : hypSU h 2 1} (hg : g ∈ patSub h sI₅ isPattern_sI₅) :
    mat g ιz ιf₁ = h.bar (mat g ιe₁ ιz) := by
  obtain ⟨hgU, a1, -⟩ := mem_patSub_sI₅.1 hg
  rw [(U_rel hgU).2.2.1, a1, map_zero, zero_mul, add_zero]

theorem mem_ZPsub_of_patSub_I₅ {g : hypSU h 2 1} (hg : g ∈ patSub h sI₅ isPattern_sI₅)
    (h0 : mat g ιe₁ ιz = 0) : g ∈ ZPsub h := by
  obtain ⟨hgU, a1, a2, a3, a4, a5, a6, a7⟩ := mem_patSub_sI₅.1 hg
  refine mem_ZPsub.2 ⟨hgU, a1, a2, h0, ?_, a3, a4, a5, a6, a7⟩
  rw [mat_zf₁_of_patSub_I₅ hg, h0, map_zero]

theorem mul_inv_mem_ZPsub_of_patSub_I₅ {g g' : hypSU h 2 1}
    (hg : g ∈ patSub h sI₅ isPattern_sI₅) (hg' : g' ∈ patSub h sI₅ isPattern_sI₅)
    (he : mat g ιe₁ ιz = mat g' ιe₁ ιz) : g * g'⁻¹ ∈ ZPsub h := by
  have := h.charP
  refine mem_ZPsub_of_patSub_I₅ (mul_mem hg (inv_mem hg')) ?_
  obtain ⟨-, x2, -⟩ := mulInv_entries (patSub_le_U _ _ hg) (patSub_le_U _ _ hg')
  obtain ⟨-, a1, -⟩ := mem_patSub_sI₅.1 hg
  rw [x2, mat_zf₁_of_patSub_I₅ hg', h.bar_bar, a1, zero_mul, add_zero, he]
  exact CharTwo.add_self_eq_zero _

theorem exists_torus_conj_patSub_I₅ {g g' : hypSU h 2 1} (hg : g ∈ patSub h sI₅ isPattern_sI₅)
    (hg' : g' ∈ patSub h sI₅ isPattern_sI₅) (hg1 : mat g ιe₁ ιz ≠ 0)
    (hg1' : mat g' ιe₁ ιz ≠ 0) : ∃ t ∈ Isub h, g' * (t * g * t⁻¹)⁻¹ ∈ ZPsub h := by
  set l := mat g' ιe₁ ιz / mat g ιe₁ ιz with hl
  have hl0 : l ≠ 0 := div_ne_zero hg1' hg1
  obtain ⟨t, ht, e1, -, e3, -, -⟩ := exists_torus h hl0 (inv_ne_zero hl0)
  refine ⟨t, ht, mul_inv_mem_ZPsub_of_patSub_I₅ hg' (torus_conj_mem_patSub _ ht hg) ?_⟩
  have hbar0 : h.bar l ≠ 0 := (map_ne_zero h.bar).2 hl0
  rw [torus_conj_apply ht, e1, e3, map_inv₀, mul_inv_cancel₀ hbar0, mul_inv_cancel₀ hl0,
    div_one, inv_one, mul_one, hl]
  field_simp

theorem card_patSub_I₅ : Nat.card (patSub h sI₅ isPattern_sI₅) = (2 ^ f) ^ 3 := by
  have hc := card_eq_mul_of_coord (H := patSub h sI₅ isPattern_sI₅) (N := ZPsub h)
    ZPsub_le_patSub_I₅ (fun g => mat g ιe₁ ιz)
    (fun x hx y hy => by
      rw [mul_e₁z (patSub_le_U _ _ hx) (patSub_le_U _ _ hy), (mem_patSub_sI₅.1 hx).2.1,
        zero_mul, add_zero])
    (fun x hx => ⟨fun e => mem_ZPsub_of_patSub_I₅ hx e, fun hz => (mem_ZPsub.1 hz).2.2.2.1⟩)
    (fun u => by
      obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := u * h.bar u)
        (by rw [map_mul, h.bar_bar, mul_comm])
      obtain ⟨g, hg, hgu, -⟩ := exists_rootI₅ h hc
      exact ⟨g, hg, hgu⟩)
  rw [hc, card_ZPsub]
  ring

theorem exists_not_comm_patSub_I₅ :
    ∃ g ∈ patSub h sI₅ isPattern_sI₅, ∃ g' ∈ patSub h sI₅ isPattern_sI₅, g * g' ≠ g' * g := by
  have := h.charP
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := 1 * h.bar 1) (by rw [map_mul, h.bar_bar, mul_comm])
  obtain ⟨c', hc'⟩ := trace_surj (hK := h) (a := ω * h.bar ω)
    (by rw [map_mul, h.bar_bar, mul_comm])
  obtain ⟨g, hg, hg1, -⟩ := exists_rootI₅ h hc
  obtain ⟨g', hg', hg'1, -⟩ := exists_rootI₅ h hc'
  refine ⟨g, hg, g', hg', fun e => hω ?_⟩
  have e1 := congrFun (congrFun (congrArg mat e) ιe₁) ιf₁
  rw [mul_e₁f₁ (patSub_le_U _ _ hg) (patSub_le_U _ _ hg'),
    mul_e₁f₁ (patSub_le_U _ _ hg') (patSub_le_U _ _ hg), mat_zf₁_of_patSub_I₅ hg,
    mat_zf₁_of_patSub_I₅ hg', (mem_patSub_sI₅.1 hg).2.1, (mem_patSub_sI₅.1 hg').2.1,
    (mem_patSub_sI₅.1 hg).2.2.2.2.2.1, (mem_patSub_sI₅.1 hg').2.2.2.2.2.1, hg1, hg'1,
    map_one] at e1
  linear_combination e1

theorem mem_ZPsub_of_comm_patSub_I₅ {g : hypSU h 2 1} (hg : g ∈ patSub h sI₅ isPattern_sI₅)
    (hc : ∀ g' ∈ patSub h sI₅ isPattern_sI₅, g * g' = g' * g) : g ∈ ZPsub h := by
  have := h.charP
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  have key : ∀ a' : K, mat g ιe₁ ιz * h.bar a' = a' * h.bar (mat g ιe₁ ιz) := by
    intro a'
    obtain ⟨c, hc'⟩ := trace_surj (hK := h) (a := a' * h.bar a')
      (by rw [map_mul, h.bar_bar, mul_comm])
    obtain ⟨g', hg', hg'1, -⟩ := exists_rootI₅ h hc'
    have e1 := congrFun (congrFun (congrArg mat (hc g' hg')) ιe₁) ιf₁
    rw [mul_e₁f₁ (patSub_le_U _ _ hg) (patSub_le_U _ _ hg'),
      mul_e₁f₁ (patSub_le_U _ _ hg') (patSub_le_U _ _ hg), mat_zf₁_of_patSub_I₅ hg,
      mat_zf₁_of_patSub_I₅ hg', (mem_patSub_sI₅.1 hg).2.1, (mem_patSub_sI₅.1 hg').2.1,
      (mem_patSub_sI₅.1 hg).2.2.2.2.2.1, (mem_patSub_sI₅.1 hg').2.2.2.2.2.1, hg'1] at e1
    linear_combination e1
  refine mem_ZPsub_of_patSub_I₅ hg ?_
  have k1 := key 1
  rw [map_one, mul_one, one_mul] at k1
  have k2 := key ω
  rw [← k1] at k2
  exact eq_zero_of_mul_bar hω k2

end Model

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

omit [Finite G] in
theorem I₅_le_I₃ (d : Data G h) : d.I₅ ≤ d.I₃ := d.pull_mono I₅sub_le_I₃sub

omit [Finite G] in
theorem I₅_le_I (d : Data G h) : d.I₅ ≤ d.I := d.pull_mono (torusEq_le _)

theorem Hyp.P_inf_centralizer_I₅ (hd : d.Hyp) :
    d.P ⊓ centralizer (d.I₅ : Set G) = d.pull (patSub h sI₅ isPattern_sI₅) := by
  rw [Data.I₅, ← d.pull_U_inf_centralizer (X := I₅sub h) (torusEq_le _),
    U_inf_centralizer_I₅ hd.two_le]

theorem Hyp.Zp_le_C₅ (hd : d.Hyp) : d.Zp ≤ d.P ⊓ centralizer (d.I₅ : Set G) := by
  rw [hd.P_inf_centralizer_I₅]
  exact d.pull_mono ZPsub_le_patSub_I₅

theorem Hyp.card_C₅ (hd : d.Hyp) :
    Nat.card (d.P ⊓ centralizer (d.I₅ : Set G) : Subgroup G) = (2 ^ f) ^ 3 := by
  rw [hd.P_inf_centralizer_I₅, d.card_pull (patSub_le_U _ _), card_patSub_I₅]

omit [Finite G] in
theorem I_le_normalizer_C₅ (d : Data G h) :
    d.I ≤ normalizer ((d.P ⊓ centralizer (d.I₅ : Set G) : Subgroup G) : Set G) := by
  intro i hi
  refine mem_normalizer_inf (d.I_le_normalizer_P hi)
    (Prelim.normalizer_le_normalizer_centralizer d.I₅ ?_)
  exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun j hj =>
    d.I_comm (d.I₅_le_I hj) hi)

theorem Hyp.exists_I_conj_C₅ (hd : d.Hyp) {a a' : G}
    (ha : a ∈ d.P ⊓ centralizer (d.I₅ : Set G)) (ha' : a' ∈ d.P ⊓ centralizer (d.I₅ : Set G))
    (ha1 : a ∉ d.Zp) (ha1' : a' ∉ d.Zp) : ∃ i ∈ d.I, ∃ z ∈ d.Zp, a' = z * (i * a * i⁻¹) := by
  rw [hd.P_inf_centralizer_I₅] at ha ha'
  obtain ⟨g, hg, rfl⟩ := ha
  obtain ⟨g', hg', rfl⟩ := ha'
  have hg1 : mat g ιe₁ ιz ≠ 0 := fun e => ha1 ⟨g, mem_ZPsub_of_patSub_I₅ hg e, rfl⟩
  have hg1' : mat g' ιe₁ ιz ≠ 0 := fun e => ha1' ⟨g', mem_ZPsub_of_patSub_I₅ hg' e, rfl⟩
  obtain ⟨t, ht, hz⟩ := exists_torus_conj_patSub_I₅ hg hg' hg1 hg1'
  refine ⟨d.η t, ⟨t, ht, rfl⟩, d.η (g' * (t * g * t⁻¹)⁻¹), ⟨_, hz, rfl⟩, ?_⟩
  simp only [map_mul, map_inv]
  group

theorem Hyp.exists_not_comm_C₅ (hd : d.Hyp) :
    ∃ a ∈ d.P ⊓ centralizer (d.I₅ : Set G), ∃ b ∈ d.P ⊓ centralizer (d.I₅ : Set G),
      a * b ≠ b * a := by
  obtain ⟨g, hg, g', hg', hne⟩ := exists_not_comm_patSub_I₅ (h := h)
  rw [hd.P_inf_centralizer_I₅]
  refine ⟨d.η g, ⟨g, hg, rfl⟩, d.η g', ⟨g', hg', rfl⟩, fun e => hne ?_⟩
  refine d.η_injOn (mul_mem (patSub_le_U _ _ hg) (patSub_le_U _ _ hg'))
    (mul_mem (patSub_le_U _ _ hg') (patSub_le_U _ _ hg)) ?_
  rw [map_mul, map_mul, e]

theorem Hyp.mem_Zp_of_comm_C₅ (hd : d.Hyp) {a : G} (ha : a ∈ d.P ⊓ centralizer (d.I₅ : Set G))
    (hc : ∀ b ∈ d.P ⊓ centralizer (d.I₅ : Set G), a * b = b * a) : a ∈ d.Zp := by
  rw [hd.P_inf_centralizer_I₅] at ha hc
  obtain ⟨g, hg, rfl⟩ := ha
  refine ⟨g, mem_ZPsub_of_comm_patSub_I₅ hg fun g' hg' => ?_, rfl⟩
  refine d.η_injOn (mul_mem (patSub_le_U _ _ hg) (patSub_le_U _ _ hg'))
    (mul_mem (patSub_le_U _ _ hg') (patSub_le_U _ _ hg)) ?_
  rw [map_mul, map_mul]
  exact hc _ ⟨g', hg', rfl⟩

theorem Hyp.t_mem_centralizer_I₅ (hd : d.Hyp) : d.t ∈ centralizer (d.I₅ : Set G) :=
  mem_centralizer_iff.2 fun _ hs => hd.comm_t (d.pull_le_L _ hs)

theorem Hyp.tP_inf_centralizer_I₅ (hd : d.Hyp) :
    d.tP ⊓ centralizer (d.I₅ : Set G) = zpowers d.t ⊔ (d.P ⊓ centralizer (d.I₅ : Set G)) := by
  refine le_antisymm (fun x hx => ?_) (sup_le (le_inf (zpowers_le.2 (mem_sup_left
    (mem_zpowers _))) (zpowers_le.2 hd.t_mem_centralizer_I₅)) (inf_le_inf_right _ le_sup_right))
  obtain ⟨hxP, hxc⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨p, hp, rfl | rfl⟩ := hd.exists_of_mem_zpowers_sup d.P_le_L hxP
  · exact mem_sup_right ⟨hp, hxc⟩
  · refine mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right ⟨hp, ?_⟩)
    have := mul_mem (inv_mem hd.t_mem_centralizer_I₅) hxc
    rwa [inv_mul_cancel_left] at this

theorem Hyp.CB₄I₃_le_normalizer_tC₅ (hd : d.Hyp) :
    d.CB₄I₃ ≤ normalizer
      ((zpowers d.t ⊔ (d.P ⊓ centralizer (d.I₅ : Set G)) : Subgroup G) : Set G) := by
  intro c hc
  rw [← hd.tP_inf_centralizer_I₅]
  refine mem_normalizer_inf (hd.B₄_le_normalizer_tP hc.1)
    (Prelim.normalizer_le_normalizer_centralizer d.I₅ (Subgroup.centralizer_le_normalizer _ ?_))
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 d.I₅_le_I₃) hc.2

omit [Finite G] in
theorem fix_mul_tP (d : Data G h) {B : Subgroup G} {u v : G} (hu : u ∈ d.tP) (hv : v ∈ d.tP)
    (hfu : ∀ b ∈ B, u⁻¹ * (b * u * b⁻¹) ∈ d.ZtP) (hfv : ∀ b ∈ B, v⁻¹ * (b * v * b⁻¹) ∈ d.ZtP) :
    (∀ b ∈ B, (u * v)⁻¹ * (b * (u * v) * b⁻¹) ∈ d.ZtP) ∧
      ∀ b ∈ B, u⁻¹⁻¹ * (b * u⁻¹ * b⁻¹) ∈ d.ZtP := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have e : (u * v)⁻¹ * (b * (u * v) * b⁻¹) =
        v⁻¹ * (u⁻¹ * (b * u * b⁻¹)) * v * (v⁻¹ * (b * v * b⁻¹)) := by group
    have hm : v⁻¹ * (u⁻¹ * (b * u * b⁻¹)) * v = u⁻¹ * (b * u * b⁻¹) := by
      rw [mul_assoc, ← d.comm_ZtP hv (hfu b hb), inv_mul_cancel_left]
    rw [e, hm]
    exact mul_mem (hfu b hb) (hfv b hb)
  · have e : u⁻¹⁻¹ * (b * u⁻¹ * b⁻¹) = u * (u⁻¹ * (b * u * b⁻¹))⁻¹ * u⁻¹ := by group
    rw [e, d.comm_ZtP hu (inv_mem (hfu b hb)), mul_inv_cancel_right]
    exact inv_mem (hfu b hb)

theorem Hyp.commutator_CB₄I₃_C₅_mem (hd : d.Hyp) {w : G}
    (hw : w ∈ zpowers d.t ⊔ (d.P ⊓ centralizer (d.I₅ : Set G))) :
    ∀ b ∈ d.CB₄I₃, w⁻¹ * (b * w * b⁻¹) ∈ d.ZtP := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := d.P ⊓ centralizer (d.I₅ : Set G) with hA
  have hAL : A ≤ d.L := inf_le_left.trans d.P_le_L
  have hYtP : zpowers d.t ⊔ A ≤ d.tP := sup_le_sup_left inf_le_left _
  have hB₄2 : IsPGroup 2 d.B₄ := by
    rw [B₄_eq_oTwo]
    exact CFSG.EvenSmallLie.UnitarySix.YamadaD.isPGroup_oTwo _
  have htP2 : IsPGroup 2 d.tP := hd.isPGroup_T.to_le hd.tP_le_T
  have hZtP_le : d.ZtP ≤ zpowers d.t ⊔ A := by
    rw [hd.ZtP_eq]
    exact sup_le_sup_left hd.Zp_le_C₅ _
  have hfixZ : ∀ z ∈ d.ZtP, ∀ b ∈ d.CB₄I₃, z⁻¹ * (b * z * b⁻¹) ∈ d.ZtP := fun z hz b hb =>
    mul_mem (inv_mem hz) ((mem_normalizer_iff.1 (d.B₄_le hb.1) z).1 hz)
  have hne : ¬ zpowers d.t ⊔ A ≤ d.ZtP := by
    intro hle
    obtain ⟨a, haA, b, hbA, hne⟩ := hd.exists_not_comm_C₅
    have haZ : a ∈ d.Zp := by
      rw [← hd.ZtP_inf_P]
      exact ⟨hle (mem_sup_right haA), haA.1⟩
    exact hne (mem_centralizer_iff.1
      ((d.sec2_2_three.2.2.2.2 ▸ haZ : a ∈ CFSG.centerIn d.P).2) b hbA.1).symm
  obtain ⟨x₀, hx₀, hx₀Z, hfix₀⟩ := exists_mem_forall_conj_mem_of_isPGroup
    (hB₄2.to_le d.CB₄I₃_le) (htP2.to_le hYtP) hZtP_le hne hd.CB₄I₃_le_normalizer_tC₅
    (fun b hb => d.B₄_le hb.1) fun u hu => d.normalizer_tP_le_normalizer_ZtP
      (le_normalizer (hYtP hu))
  have hfix : ∀ u ∈ zpowers d.t ⊔ A, ∀ v ∈ zpowers d.t ⊔ A,
      (∀ b ∈ d.CB₄I₃, u⁻¹ * (b * u * b⁻¹) ∈ d.ZtP) →
        (∀ b ∈ d.CB₄I₃, v⁻¹ * (b * v * b⁻¹) ∈ d.ZtP) →
          ∀ b ∈ d.CB₄I₃, (u * v)⁻¹ * (b * (u * v) * b⁻¹) ∈ d.ZtP :=
    fun u hu v hv hfu hfv => (d.fix_mul_tP (hYtP hu) (hYtP hv) hfu hfv).1
  obtain ⟨y, hy, hx₀y⟩ : ∃ y ∈ A, ∃ u ∈ zpowers d.t, x₀ = u * y := by
    obtain ⟨y, hy, hx₀y | hx₀y⟩ := hd.exists_of_mem_zpowers_sup hAL hx₀
    · exact ⟨y, hy, 1, one_mem _, by rw [hx₀y, one_mul]⟩
    · exact ⟨y, hy, d.t, mem_zpowers _, hx₀y⟩
  obtain ⟨u, hu, rfl⟩ := hx₀y
  have huZ : u ∈ d.ZtP := hd.ZtP_eq ▸ mem_sup_left hu
  have hfy : ∀ b ∈ d.CB₄I₃, y⁻¹ * (b * y * b⁻¹) ∈ d.ZtP := by
    have e : y = u⁻¹ * (u * y) := by group
    rw [e]
    exact hfix _ (hZtP_le (inv_mem huZ)) _ hx₀ (hfixZ _ (inv_mem huZ)) hfix₀
  have hy1 : y ∉ d.Zp := fun hyZ => hx₀Z (mul_mem huZ (hd.ZtP_eq ▸ mem_sup_right hyZ))
  have hfA : ∀ a ∈ A, ∀ b ∈ d.CB₄I₃, a⁻¹ * (b * a * b⁻¹) ∈ d.ZtP := by
    intro a ha
    by_cases haZ : a ∈ d.Zp
    · exact hfixZ a (hd.ZtP_eq ▸ mem_sup_right haZ)
    obtain ⟨i, hi, z, hz, rfl⟩ := hd.exists_I_conj_C₅ hy ha hy1 haZ
    have hiy : i * y * i⁻¹ ∈ A := (mem_normalizer_iff.1 (d.I_le_normalizer_C₅ hi) y).1 hy
    have hfiy : ∀ b ∈ d.CB₄I₃, (i * y * i⁻¹)⁻¹ * (b * (i * y * i⁻¹) * b⁻¹) ∈ d.ZtP := by
      intro b hb
      have hiH := hd.I_le_H hi
      have hb' : i⁻¹ * b * i ∈ d.CB₄I₃ := by
        have := (mem_normalizer_iff.1 (hd.I_le_normalizer_CB₄I₃ (inv_mem hi)) b).1 hb
        rwa [inv_inv] at this
      have e : (i * y * i⁻¹)⁻¹ * (b * (i * y * i⁻¹) * b⁻¹) =
          i * (y⁻¹ * ((i⁻¹ * b * i) * y * (i⁻¹ * b * i)⁻¹)) * i⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.1 hiH.1 _).1 (hfy _ hb')
    have hzZ : z ∈ d.ZtP := hd.ZtP_eq ▸ mem_sup_right hz
    exact hfix _ (hZtP_le hzZ) _ (mem_sup_right hiy) (hfixZ z hzZ) hfiy
  obtain ⟨a, ha, hwa | hwa⟩ := hd.exists_of_mem_zpowers_sup hAL hw <;> rw [hwa]
  · exact hfA a ha
  · exact hfix _ (hZtP_le hd.t_mem_ZtP) _ (mem_sup_right ha) (hfixZ _ hd.t_mem_ZtP) (hfA a ha)

theorem Hyp.C₅_inf_centralizer_I₃ (hd : d.Hyp) :
    (d.P ⊓ centralizer (d.I₅ : Set G)) ⊓ centralizer (d.I₃ : Set G) = d.Zp := by
  refine le_antisymm ?_ (le_inf hd.Zp_le_C₅ (fun z hz => mem_centralizer_iff.2 fun s hs =>
    (mem_centralizer_iff.1 (hd.I₃_le_centralizer_Zp hs) z hz).symm))
  rw [(d.sec2_1_two hd.two_le).1]
  exact inf_le_inf_right _ inf_le_left

omit [Finite G] in
theorem P_le_normalizer_Zp (d : Data G h) : d.P ≤ normalizer (d.Zp : Set G) := fun p hp =>
  Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun z hz =>
    (mem_centralizer_iff.1 ((d.sec2_2_three.2.2.2.2 ▸ hz : z ∈ CFSG.centerIn d.P).2) p hp).symm)

theorem Hyp.CB₄I₃_le_centralizer_C₅ (hd : d.Hyp) :
    d.CB₄I₃ ≤ centralizer ((d.P ⊓ centralizer (d.I₅ : Set G) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro c hc
  have hC5 := hd.C₅_inf_centralizer_I₃
  refine mem_centralizer_of_displacement (A := d.P ⊓ centralizer (d.I₅ : Set G)) (X := d.I₃)
    (N := d.ZtP) (d.isPGroup_P.to_le inf_le_left)
    (Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le d.I₃_le_I))
    (fun i hi => d.I_le_normalizer_C₅ (d.I₃_le_I hi)) ?_ hc.2
    (fun n hn a ha => (d.comm_ZtP (mem_sup_right ha.1) hn).symm)
    (fun i hi n hn => (mem_centralizer_iff.1 (hd.I₃_le_centralizer_ZtP hi) n hn).symm)
    (fun a ha => hd.commutator_CB₄I₃_C₅_mem (mem_sup_right ha) c hc) ?_
  · rw [hC5]
    exact fun a ha => d.P_le_normalizer_Zp ha.1
  · intro a ha
    rw [hC5] at ha
    exact (mem_centralizer_iff.1 (hd.two_core_B₄.1 hc.1) a ha).symm

theorem Hyp.CB₄I₃_le_centralizer_A₂ (hd : d.Hyp) : d.CB₄I₃ ≤ centralizer (d.A₂ : Set G) := by
  intro c hc
  rw [(d.sec2_1_two hd.two_le).2.2.2.2.2.1]
  exact mem_centralizer_sup (mem_centralizer_sup (hd.CB₄I₃_le_centralizer_Z₂p hc)
    (hd.CB₄I₃_le_centralizer_Z₂p_s hc)) (hd.CB₄I₃_le_centralizer_C₅ hc)

theorem Hyp.B₄_eq_CB₄I₃_sup_A₂ (hd : d.Hyp) : d.B₄ = d.CB₄I₃ ⊔ d.A₂ := by
  rw [hd.B₄_eq_V_sup_B₂, hd.CB₄I₃_eq, Data.B₂, sup_assoc]

theorem Hyp.A₂_le_normalizer_CB₄I₃ (hd : d.Hyp) : d.A₂ ≤ normalizer (d.CB₄I₃ : Set G) :=
  fun a ha => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun _ hc =>
    (mem_centralizer_iff.1 (hd.CB₄I₃_le_centralizer_A₂ hc) a ha).symm)

theorem Hyp.B₄_inf_centralizer_A₂ (hd : d.Hyp) :
    d.B₄ ⊓ centralizer (d.A₂ : Set G) = d.CB₄I₃ := by
  refine le_antisymm (fun x hx => ?_) (le_inf d.CB₄I₃_le hd.CB₄I₃_le_centralizer_A₂)
  obtain ⟨hxB, hxc⟩ := Subgroup.mem_inf.1 hx
  rw [hd.B₄_eq_CB₄I₃_sup_A₂] at hxB
  obtain ⟨c, hc, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hd.A₂_le_normalizer_CB₄I₃
    hxB
  have haZ : a ∈ d.Zp := by
    rw [← d.sec2_2_three.2.2.2.1]
    refine ⟨ha, ?_⟩
    have := mul_mem (inv_mem (hd.CB₄I₃_le_centralizer_A₂ hc)) hxc
    rwa [inv_mul_cancel_left] at this
  exact mul_mem hc (hd.Zp_le_CB₄I₃ haZ)

theorem Hyp.normalizer_ZtP_le_normalizer_CB₄I₃ (hd : d.Hyp) :
    normalizer (d.ZtP : Set G) ≤ normalizer (d.CB₄I₃ : Set G) := by
  have hB₄ : d.B₄ ≤ normalizer (d.CB₄I₃ : Set G) := by
    rw [hd.B₄_eq_CB₄I₃_sup_A₂]
    exact sup_le le_normalizer hd.A₂_le_normalizer_CB₄I₃
  intro g hg
  obtain ⟨x, hx, c, hc, rfl⟩ := hd.sec3_2.2.1 g hg
  refine mul_mem (hB₄ hx) ?_
  rw [← hd.B₄_inf_centralizer_A₂]
  exact mem_normalizer_inf (d.le_normalizer_B₄ hc.1)
    (Prelim.normalizer_le_normalizer_centralizer d.A₂
      (mem_normalizer_of_conj_le fun a ha => hd.conj_mem_A₂ hc.1 hc.2 ha))

theorem Hyp.CB₄I₃_inf_tP (hd : d.Hyp) : d.CB₄I₃ ⊓ d.tP = d.ZtP := by
  refine le_antisymm (fun x hx => ?_) (le_inf (hd.CB₄I₃_inf_B₂ ▸ inf_le_left)
    fun z hz => hz.1)
  have hxB₂ : x ∈ d.B₂ := by
    rw [← hd.two_core_B₄.2.2.1]
    exact ⟨hx.1.1, hd.tP_le_centralizer hx.2⟩
  rw [← hd.CB₄I₃_inf_B₂]
  exact ⟨hx.1, hxB₂⟩

theorem Hyp.CB₄I₃_le_centralizer_P (hd : d.Hyp) : d.CB₄I₃ ≤ centralizer (d.P : Set G) := by
  intro c hc
  have hPN : d.P ≤ normalizer (d.CB₄I₃ : Set G) := fun p hp =>
    hd.normalizer_ZtP_le_normalizer_CB₄I₃ (d.tP_le_normalizer_ZtP (mem_sup_right hp))
  have hZ := (d.sec2_1_two hd.two_le).1
  refine mem_centralizer_of_displacement (A := d.P) (X := d.I₃) (N := d.ZtP) d.isPGroup_P
    (Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le d.I₃_le_I))
    (fun i hi => d.I_le_normalizer_P (d.I₃_le_I hi)) ?_ hc.2
    (fun n hn a ha => (d.comm_ZtP (mem_sup_right ha) hn).symm)
    (fun i hi n hn => (mem_centralizer_iff.1 (hd.I₃_le_centralizer_ZtP hi) n hn).symm)
    (fun p hp => ?_) ?_
  · rw [← hZ]
    exact d.P_le_normalizer_Zp
  · rw [← hd.CB₄I₃_inf_tP]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 := (mem_normalizer_iff.1 (hPN (inv_mem hp)) c).1 hc
      rw [inv_inv] at h1
      have e : p⁻¹ * (c * p * c⁻¹) = p⁻¹ * c * p * c⁻¹ := by group
      rw [e]
      exact mul_mem h1 (inv_mem hc)
    · have hptP : p ∈ d.tP := mem_sup_right hp
      exact mul_mem (inv_mem hptP) ((mem_normalizer_iff.1 (hd.B₄_le_normalizer_tP hc.1) p).1 hptP)
  · intro a ha
    rw [← hZ] at ha
    exact (mem_centralizer_iff.1 (hd.two_core_B₄.1 hc.1) a ha).symm

theorem Hyp.card_V_sup_C₅ (hd : d.Hyp) :
    d.V ⊓ (d.P ⊓ centralizer (d.I₅ : Set G)) = d.Zp ∧
      Nat.card (d.V ⊔ (d.P ⊓ centralizer (d.I₅ : Set G)) : Subgroup G) = (2 ^ f) ^ 4 := by
  have hinf : d.V ⊓ (d.P ⊓ centralizer (d.I₅ : Set G)) = d.Zp := by
    refine le_antisymm ?_ (le_inf hd.Zp_le_V hd.Zp_le_C₅)
    rw [← hd.V_inf_centralizer_t]
    exact inf_le_inf_left _ fun x hx => hd.L_le_centralizer (d.P_le_L hx.1)
  refine ⟨hinf, ?_⟩
  have hN : d.P ⊓ centralizer (d.I₅ : Set G) ≤ normalizer (d.V : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun v hv =>
      (mem_centralizer_iff.1 (hd.CB₄I₃_le_centralizer_C₅ (hd.V_le_CB₄I₃ hv)) a ha).symm)
  have h1 := card_sup_mul_card_inf_eq hN
  rw [hinf, hd.card_V, hd.card_C₅, d.card_Zp] at h1
  have e : (2 ^ f) ^ 2 * (2 ^ f) ^ 3 = (2 ^ f) ^ 4 * 2 ^ f := by ring
  rw [e] at h1
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h1

end Data

end CFSG.LocalAnalysis.EvenBN.U5
