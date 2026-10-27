module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Squares
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.QuasithinUnique.C1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5 Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_mem_of_noTwoQuotient {L M N : Subgroup G}
    (hL : ∀ (N' : Subgroup L) [N'.Normal], IsPGroup 2 (L ⧸ N') → N' = ⊤)
    (hM : IsPGroup 2 M) (hNnorm : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N)
    (hLM : ∀ l ∈ L, ∀ w ∈ M, l * w * l⁻¹ * w⁻¹ ∈ N) {y : G}
    (hy : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ M) : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ N := by
  have hnorm : (N.subgroupOf M).Normal := by
    refine ⟨fun n hn m => ?_⟩
    have := hNnorm (m : G) m.2 (n : G) hn
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  let f : L → M ⧸ N.subgroupOf M := fun l =>
    QuotientGroup.mk ⟨y * (l : G) * y⁻¹ * (l : G)⁻¹, hy l l.2⟩
  have hf : ∀ a b, f (a * b) = f a * f b := by
    intro l l'
    show QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hw := hy l' l'.2
    have h1 := hLM l l.2 _ (M.inv_mem hw)
    have e : ((y * ((l : G) * (l' : G)) * y⁻¹ * ((l : G) * (l' : G))⁻¹))⁻¹ *
        ((y * (l : G) * y⁻¹ * (l : G)⁻¹) * (y * (l' : G) * y⁻¹ * (l' : G)⁻¹)) =
        (l : G) * (y * (l' : G) * y⁻¹ * (l' : G)⁻¹)⁻¹ * (l : G)⁻¹ *
          (y * (l' : G) * y⁻¹ * (l' : G)⁻¹)⁻¹⁻¹ := by
      group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact h1
  let ψ : L →* M ⧸ N.subgroupOf M := MonoidHom.mk' f hf
  have hker : ψ.ker = ⊤ := by
    apply hL
    have hp : IsPGroup 2 (M ⧸ N.subgroupOf M) := hM.to_quotient _
    have e := QuotientGroup.quotientKerEquivRange ψ
    exact (hp.to_subgroup ψ.range).of_equiv e.symm
  intro l hl
  have h1 : ψ ⟨l, hl⟩ = 1 := by
    have : (⟨l, hl⟩ : L) ∈ ψ.ker := by rw [hker]; trivial
    exact this
  have h2 : (⟨y * l * y⁻¹ * l⁻¹, hy l hl⟩ : M) ∈ N.subgroupOf M :=
    (QuotientGroup.eq_one_iff _).mp h1
  exact h2

theorem blockQ_isPGroup [Finite G] (L : Subgroup G) : IsPGroup 2 (blockQ L) :=
  CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L

theorem le_normalizer_blockQ [Finite G] (L : Subgroup G) : L ≤ normalizer (blockQ L : Set G) :=
  CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L

theorem blockQ_le (L : Subgroup G) : blockQ L ≤ L :=
  CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L

theorem le_normalizer_blockU [Finite G] (L : Subgroup G) : L ≤ normalizer (blockU L : Set G) := by
  intro g hg
  rw [← conjSubgroup_eq_iff_mem_normalizer, blockU, conjSubgroup_commutator,
    conjSubgroup_eq_self (le_normalizer_blockQ L hg),
    conjSubgroup_eq_self (Subgroup.le_normalizer hg)]

theorem commutator_blockU_le [Finite G] (L : Subgroup G) : ⁅blockU L, L⁆ ≤ blockU L := by
  rw [Subgroup.commutator_le]
  intro u hu l hl
  have h1 : l * u⁻¹ * l⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.mp
    (le_normalizer_blockU L hl) u⁻¹).mp (inv_mem hu)
  have : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact Subgroup.mul_mem _ hu h1

variable {L : Subgroup G}

theorem blockU_le_blockQ (hL : IsShort2 L) : blockU L ≤ blockQ L := fun _ hx =>
  (hL.2.2.1.1 hx).1

theorem blockU_comm (hL : IsShort2 L) : ∀ u ∈ blockU L, ∀ q ∈ blockQ L, u * q = q * u :=
  fun _ hu q hq => ((Subgroup.mem_centralizer_iff.mp (hL.2.2.1.1 hu).2) q hq).symm

theorem blockU_sq (hL : IsShort2 L) : ∀ u ∈ blockU L, u ^ 2 = 1 := hL.2.2.1.2

theorem elemAb2_blockU (hL : IsShort2 L) : ElemAb2 (blockU L) :=
  ⟨fun a ha b hb => blockU_comm hL a ha b (blockU_le_blockQ hL hb), blockU_sq hL⟩

theorem isPGroup_blockU (hL : IsShort2 L) : IsPGroup 2 (blockU L) := fun g =>
  ⟨1, Subtype.ext (by simpa using blockU_sq hL g g.2)⟩

theorem commutator_mem_blockU {a l : G} (ha : a ∈ blockQ L) (hl : l ∈ L) :
    a * l * a⁻¹ * l⁻¹ ∈ blockU L :=
  Subgroup.commutator_mem_commutator ha hl

theorem commutator_mem_blockU' {l w : G} (hl : l ∈ L) (hw : w ∈ blockQ L) :
    l * w * l⁻¹ * w⁻¹ ∈ blockU L := by
  have : ⁅l, w⁆ ∈ ⁅L, blockQ L⁆ := Subgroup.commutator_mem_commutator hl hw
  rw [Subgroup.commutator_comm] at this
  exact this

theorem commutator_blockU [Finite G] (hL : IsShort2 L) : ⁅blockU L, L⁆ = blockU L := by
  refine le_antisymm (commutator_blockU_le L) ?_
  show ⁅blockQ L, L⁆ ≤ _
  rw [Subgroup.commutator_le]
  intro a ha l hl
  refine commutator_mem_of_noTwoQuotient (L := L) (M := blockU L) (N := ⁅blockU L, L⁆)
    hL.1 (isPGroup_blockU hL) ?_ ?_ ?_ l hl
  · intro m hm n hn
    have hn' : n ∈ blockU L := commutator_blockU_le L hn
    have := (elemAb2_blockU hL).1 m hm n hn'
    rw [this]; simpa using hn
  · intro l hl w hw
    have : ⁅l, w⁆ ∈ ⁅L, blockU L⁆ := Subgroup.commutator_mem_commutator hl hw
    rw [Subgroup.commutator_comm] at this
    exact this
  · intro l hl
    exact commutator_mem_blockU ha hl

theorem commutator_mem_blockU_of_mem_blockQ [Finite G] (hL : IsShort2 L) {y : G}
    (hy : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ blockQ L) : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ blockU L := by
  refine commutator_mem_of_noTwoQuotient (L := L) (M := blockQ L) (N := blockU L)
    hL.1 (blockQ_isPGroup L) ?_ ?_ hy
  · intro m hm n hn
    have := blockU_comm hL n hn m hm
    rw [← this, mul_inv_cancel_right]
    exact hn
  · intro l hl w hw
    exact commutator_mem_blockU' hl hw


theorem le_pCoreOf_of_normalized {N K : Subgroup G} (hNK : N ≤ K)
    (hK : K ≤ normalizer (N : Set G)) (hN : IsPGroup 2 N) : N ≤ pCoreOf 2 K :=
  CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 N K hNK
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hK) hN

theorem exists_pow_eq_one_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) {y : G} (hy : y ∈ P) :
    ∃ k : ℕ, y ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer, conjSubgroup_sup, conjSubgroup_eq_self hA,
    conjSubgroup_eq_self hB]

theorem mem_normalizer_blockQ {g : G} (hg : g ∈ normalizer (L : Set G)) :
    g ∈ normalizer (blockQ L : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer, blockQ, conjSubgroup_pCoreOf, conjSubgroup_eq_self hg]

theorem mem_normalizer_blockU {g : G} (hg : g ∈ normalizer (L : Set G)) :
    g ∈ normalizer (blockU L : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer, blockU, conjSubgroup_commutator,
    conjSubgroup_eq_self hg, conjSubgroup_eq_self (mem_normalizer_blockQ hg)]

theorem mem_normalizer_blockZ {g : G} (hg : g ∈ normalizer (L : Set G)) :
    g ∈ normalizer (blockZ L : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer, blockZ, conjSubgroup_inf, conjSubgroup_centralizer,
    conjSubgroup_eq_self hg, conjSubgroup_eq_self (mem_normalizer_blockU hg)]

theorem inf_centralizer_blockU_le [Finite G] (hL : IsShort2 L) :
    L ⊓ centralizer (blockU L : Set G) ≤ blockQ L := by
  set C := L ⊓ centralizer (blockU L : Set G) with hC
  have hCL : C ≤ L := inf_le_left
  have hsq : ∀ c ∈ C, c * c ∈ blockQ L := by
    intro c hc
    have hcL : c ∈ L := hc.1
    have hcent : c * c ∈ centralizer (blockQ L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      set u := c * q * c⁻¹ * q⁻¹ with hu
      have huU : u ∈ blockU L := commutator_mem_blockU' hcL hq
      have h1 : u * c = c * u := Subgroup.mem_centralizer_iff.mp hc.2 u huU
      have h1' : c * u * c⁻¹ = u := by rw [← h1]; group
      have h2 : u * u = 1 := by rw [← pow_two]; exact blockU_sq hL u huU
      have hcq : c * q * c⁻¹ = u * q := by rw [hu]; group
      have key : c * c * q * (c⁻¹ * c⁻¹) = q := by
        calc c * c * q * (c⁻¹ * c⁻¹) = c * (c * q * c⁻¹) * c⁻¹ := by group
          _ = c * (u * q) * c⁻¹ := by rw [hcq]
          _ = (c * u * c⁻¹) * (c * q * c⁻¹) := by group
          _ = u * (u * q) := by rw [h1', hcq]
          _ = (u * u) * q := by group
          _ = q := by rw [h2]; group
      calc q * (c * c) = (c * c * q * (c⁻¹ * c⁻¹)) * (c * c) := by rw [key]
        _ = c * c * q := by group
    exact hL.2.1 ⟨mul_mem hcL hcL, hcent⟩
  have hCN : C ≤ normalizer (blockQ L : Set G) := hCL.trans (le_normalizer_blockQ L)
  have hX2 : IsPGroup 2 (C ⊔ blockQ L : Subgroup G) := by
    intro g
    obtain ⟨c, hc, q, hq, hg⟩ := mem_sup_of_le_normalizer hCN g.2
    have hcq : (g : G) * g ∈ blockQ L := by
      rw [hg]
      have e : c * q * (c * q) = (c * c) * (c⁻¹ * q * c) * q := by group
      rw [e]
      refine mul_mem (mul_mem (hsq c hc) ?_) hq
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_blockQ L (inv_mem hc.1)) q).mp hq
      simpa using this
    obtain ⟨m, hm⟩ := blockQ_isPGroup L ⟨_, hcq⟩
    refine ⟨m + 1, Subtype.ext ?_⟩
    have hm' : ((g : G) * g) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    calc ((g ^ 2 ^ (m + 1) : (C ⊔ blockQ L : Subgroup G)) : G) = ((g : G) * g) ^ 2 ^ m := by
          rw [Subgroup.coe_pow, pow_succ', pow_mul, sq]
      _ = 1 := hm'
      _ = ((1 : (C ⊔ blockQ L : Subgroup G)) : G) := rfl
  have hCQ : ∀ g ∈ L, g ∈ normalizer ((C : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg)
      (mem_normalizer_centralizer (le_normalizer_blockU L hg))
  have hLX : L ≤ normalizer ((C ⊔ blockQ L : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_sup (hCQ g hg) (le_normalizer_blockQ L hg)
  exact le_sup_left.trans (le_pCoreOf_of_normalized (sup_le hCL (blockQ_le L)) hLX hX2)

theorem commutator_mul_of_comm {U : Subgroup G} (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) {y : G}
    (hy : y ∈ normalizer (U : Set G)) {u v : G} (hu : u ∈ U) (hv : v ∈ U) :
    y * (u * v) * y⁻¹ * (u * v)⁻¹ = (y * u * y⁻¹ * u⁻¹) * (y * v * y⁻¹ * v⁻¹) := by
  have hb : y * v * y⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hy v).mp hv
  have key : u⁻¹ * (y * v * y⁻¹ * v⁻¹) = (y * v * y⁻¹ * v⁻¹) * u⁻¹ :=
    hU _ (inv_mem hu) _ (mul_mem hb (inv_mem hv))
  calc y * (u * v) * y⁻¹ * (u * v)⁻¹
      = (y * u * y⁻¹) * ((y * v * y⁻¹ * v⁻¹) * u⁻¹) := by group
    _ = (y * u * y⁻¹) * (u⁻¹ * (y * v * y⁻¹ * v⁻¹)) := by rw [key]
    _ = (y * u * y⁻¹ * u⁻¹) * (y * v * y⁻¹ * v⁻¹) := by group

theorem commutator_inv_of_comm {U : Subgroup G} (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) {y : G}
    (hy : y ∈ normalizer (U : Set G)) {u : G} (hu : u ∈ U) :
    y * u⁻¹ * y⁻¹ * u⁻¹⁻¹ = (y * u * y⁻¹ * u⁻¹)⁻¹ := by
  have h1 := commutator_mul_of_comm hU hy (inv_mem hu) hu
  simp only [inv_mul_cancel, mul_one, inv_one, mul_inv_cancel] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem iterate_commutator_formula {U : Subgroup G} (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hU2 : ∀ a ∈ U, a ^ 2 = 1) {y : G} (hy : y ∈ normalizer (U : Set G)) (j : ℕ) :
    ∀ u ∈ U, y ^ 2 ^ j * u * (y ^ 2 ^ j)⁻¹ =
      u * (fun v : G => y * v * y⁻¹ * v⁻¹)^[2 ^ j] u := by
  have hθ : ∀ v ∈ U, y * v * y⁻¹ * v⁻¹ ∈ U := fun v hv =>
    mul_mem ((Subgroup.mem_normalizer_iff.mp hy v).mp hv) (inv_mem hv)
  have hit : ∀ (m : ℕ), ∀ v ∈ U, (fun v : G => y * v * y⁻¹ * v⁻¹)^[m] v ∈ U := by
    intro m
    induction m with
    | zero => intro v hv; simpa using hv
    | succ m ih =>
      intro v hv
      rw [Function.iterate_succ_apply]
      exact ih _ (hθ v hv)
  induction j with
  | zero =>
    intro u hu
    have hu' : y * u * y⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hy u).mp hu
    have hc : u * (y * u * y⁻¹) = (y * u * y⁻¹) * u := hU _ hu _ hu'
    simp only [pow_zero, pow_one, Function.iterate_one]
    calc y * u * y⁻¹ = (y * u * y⁻¹) * u * u⁻¹ := by group
      _ = u * (y * u * y⁻¹) * u⁻¹ := by rw [← hc]
      _ = u * (y * u * y⁻¹ * u⁻¹) := by group
  | succ j ih =>
    intro u hu
    set v := (fun v : G => y * v * y⁻¹ * v⁻¹)^[2 ^ j] u with hv
    have hvU : v ∈ U := hit _ u hu
    have hv2 : v * v = 1 := by rw [← pow_two]; exact hU2 v hvU
    have e1 : y ^ 2 ^ (j + 1) = y ^ 2 ^ j * y ^ 2 ^ j := by
      rw [pow_succ, pow_mul, sq]
    have e2 : (fun v : G => y * v * y⁻¹ * v⁻¹)^[2 ^ (j + 1)] u =
        (fun v : G => y * v * y⁻¹ * v⁻¹)^[2 ^ j] v := by
      rw [pow_succ, mul_two, Function.iterate_add_apply]
    have ihu := ih u hu
    have ihv := ih v hvU
    calc y ^ 2 ^ (j + 1) * u * (y ^ 2 ^ (j + 1))⁻¹
        = y ^ 2 ^ j * (y ^ 2 ^ j * u * (y ^ 2 ^ j)⁻¹) * (y ^ 2 ^ j)⁻¹ := by rw [e1]; group
      _ = y ^ 2 ^ j * (u * v) * (y ^ 2 ^ j)⁻¹ := by rw [ihu]
      _ = (y ^ 2 ^ j * u * (y ^ 2 ^ j)⁻¹) * (y ^ 2 ^ j * v * (y ^ 2 ^ j)⁻¹) := by group
      _ = (u * v) * (v * (fun v : G => y * v * y⁻¹ * v⁻¹)^[2 ^ j] v) := by rw [ihu, ihv]
      _ = u * (v * v) * (fun v : G => y * v * y⁻¹ * v⁻¹)^[2 ^ j] v := by group
      _ = u * (fun v : G => y * v * y⁻¹ * v⁻¹)^[2 ^ (j + 1)] u := by rw [hv2, e2]; group

theorem exists_mem_diff_commutator_mem {U Z : Subgroup G}
    (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU2 : ∀ a ∈ U, a ^ 2 = 1) {y : G}
    (hy : y ∈ normalizer (U : Set G)) (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1) (hne : ∃ u ∈ U, u ∉ Z) :
    ∃ u ∈ U, u ∉ Z ∧ y * u * y⁻¹ * u⁻¹ ∈ Z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u₀, hu₀, hu₀Z⟩ := hne
  obtain ⟨k, hk⟩ := hy2
  have hθ : ∀ v ∈ U, y * v * y⁻¹ * v⁻¹ ∈ U := fun v hv =>
    mul_mem ((Subgroup.mem_normalizer_iff.mp hy v).mp hv) (inv_mem hv)
  have hnot : ∀ j : ℕ, (fun v : G => y * v * y⁻¹ * v⁻¹)^[j] u₀ ∈ U ∧
      (fun v : G => y * v * y⁻¹ * v⁻¹)^[j] u₀ ∉ Z := by
    intro j
    induction j with
    | zero => exact ⟨hu₀, hu₀Z⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨hθ _ ih.1, hcon _ ih.1 ih.2⟩
  have hform := iterate_commutator_formula hU hU2 hy k u₀ hu₀
  rw [hk] at hform
  have h1 : (fun v : G => y * v * y⁻¹ * v⁻¹)^[2 ^ k] u₀ = 1 := by
    have : u₀ = u₀ * (fun v : G => y * v * y⁻¹ * v⁻¹)^[2 ^ k] u₀ := by simpa using hform
    exact (mul_eq_left.mp this.symm)
  exact (hnot (2 ^ k)).2 (h1 ▸ Z.one_mem)


theorem exists_pow_mem_of_mem_sup {L R : Subgroup G} (hR : IsPGroup 2 R)
    (hRN : R ≤ normalizer (L : Set G)) {g : G} (hg : g ∈ L ⊔ R) : ∃ k : ℕ, g ^ 2 ^ k ∈ L := by
  rw [sup_comm] at hg
  obtain ⟨r, hr, l, hl, rfl⟩ := mem_sup_of_le_normalizer hRN hg
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hR hr
  have hpow : ∀ n : ℕ, ∃ l' ∈ L, (r * l) ^ n = r ^ n * l' := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨l', hl', he⟩ := ih
      refine ⟨(r⁻¹ * l' * r) * l, mul_mem ?_ hl, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hRN (inv_mem hr)) l').mp hl'
        simpa using this
      · rw [pow_succ, he]; simp [pow_succ, mul_assoc]
  obtain ⟨l', hl', he⟩ := hpow (2 ^ k)
  exact ⟨k, by rw [he, hk, one_mul]; exact hl'⟩

theorem commutator_conj_blockU [Finite G] (hL : IsShort2 L) {y l u : G}
    (hyU : y ∈ normalizer (blockU L : Set G)) (hl : l ∈ L)
    (hc : y * l * y⁻¹ * l⁻¹ ∈ blockQ L) (hu : u ∈ blockU L) :
    y * (l * u * l⁻¹) * y⁻¹ * (l * u * l⁻¹)⁻¹ = l * (y * u * y⁻¹ * u⁻¹) * l⁻¹ := by
  set c := y * l * y⁻¹ * l⁻¹ with hcdef
  have hcl : y * l * y⁻¹ = c * l := by rw [hcdef]; group
  have hu' : y * u * y⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.mp hyU u).mp hu
  have hw : l * (y * u * y⁻¹) * l⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_blockU L hl) _).mp hu'
  have hcw : l * (y * u * y⁻¹) * l⁻¹ * c = c * (l * (y * u * y⁻¹) * l⁻¹) :=
    blockU_comm hL _ hw c hc
  have e : c * (l * (y * u * y⁻¹) * l⁻¹) * c⁻¹ = l * (y * u * y⁻¹) * l⁻¹ := by
    rw [← hcw]; group
  calc y * (l * u * l⁻¹) * y⁻¹ * (l * u * l⁻¹)⁻¹
      = (y * l * y⁻¹) * (y * u * y⁻¹) * (y * l * y⁻¹)⁻¹ * (l * u⁻¹ * l⁻¹) := by group
    _ = (c * l) * (y * u * y⁻¹) * (c * l)⁻¹ * (l * u⁻¹ * l⁻¹) := by rw [hcl]
    _ = c * (l * (y * u * y⁻¹) * l⁻¹) * c⁻¹ * (l * u⁻¹ * l⁻¹) := by group
    _ = (l * (y * u * y⁻¹) * l⁻¹) * (l * u⁻¹ * l⁻¹) := by rw [e]
    _ = l * (y * u * y⁻¹ * u⁻¹) * l⁻¹ := by group

theorem commute_blockU_of_mem [Finite G] (hL : IsShort2 L) {y : G}
    (hyN : y ∈ normalizer (L : Set G)) (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1)
    (hyL : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ blockQ L) : ∀ u ∈ blockU L, u * y = y * u := by
  have hyU : y ∈ normalizer (blockU L : Set G) := mem_normalizer_blockU hyN
  have hyZ : y ∈ normalizer (blockZ L : Set G) := mem_normalizer_blockZ hyN
  have hUab := (elemAb2_blockU hL).1
  have hU2 := blockU_sq hL
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have hZc : ∀ z ∈ blockZ L, ∀ l ∈ L, l * z * l⁻¹ = z := by
    intro z hz l hl
    have := Subgroup.mem_centralizer_iff.mp hz.2 l hl
    rw [this]; group
  let W : Subgroup G :=
    { carrier := {u | u ∈ blockU L ∧ y * u * y⁻¹ * u⁻¹ ∈ blockZ L}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        rw [commutator_mul_of_comm hUab hyU ha hb]
        exact mul_mem ha' hb'
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        rw [commutator_inv_of_comm hUab hyU ha]
        exact inv_mem ha' }
  have hZW : blockZ L ≤ W := fun z hz => ⟨hZU hz, by
    have h1 : y * z * y⁻¹ ∈ blockZ L := (Subgroup.mem_normalizer_iff.mp hyZ z).mp hz
    exact mul_mem h1 (inv_mem hz)⟩
  have hWU : W ≤ blockU L := fun u hu => hu.1
  have fwd : ∀ l ∈ L, ∀ x ∈ W, l * x * l⁻¹ ∈ W := by
    rintro l hl x ⟨hx, hx'⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_blockU L hl) x).mp hx, ?_⟩
    show y * (l * x * l⁻¹) * y⁻¹ * (l * x * l⁻¹)⁻¹ ∈ blockZ L
    rw [commutator_conj_blockU hL hyU hl (hyL l hl) hx, hZc _ hx' l hl]
    exact hx'
  have hLW : L ≤ normalizer (W : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => fwd l hl x hx
    · intro hx
      have := fwd l⁻¹ (inv_mem hl) _ hx
      simpa [mul_assoc] using this
  have hne : ∃ u ∈ blockU L, u ∉ blockZ L :=
    (IsConcreteLE.lt_iff_le_and_exists.mp hL.2.2.2.2.1).2
  obtain ⟨u₁, hu₁, hu₁Z, hu₁c⟩ := exists_mem_diff_commutator_mem hUab hU2 hyU hy2 hne
  have hWU' : W = blockU L := by
    rcases hL.2.2.2.2.2 W hZW hWU hLW with h | h
    · exfalso
      have : u₁ ∈ W := ⟨hu₁, hu₁c⟩
      rw [h] at this
      exact hu₁Z this
    · exact h
  have hcomZ : ∀ u ∈ blockU L, y * u * y⁻¹ * u⁻¹ ∈ blockZ L := by
    intro u hu
    have : u ∈ W := by rw [hWU']; exact hu
    exact this.2
  have hle : blockU L ≤ Subgroup.centralizer ({y} : Set G) := by
    refine le_trans (commutator_blockU hL).ge ?_
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have hu_inv : u⁻¹ ∈ blockU L := inv_mem hu
    have hv : l * u⁻¹ * l⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_blockU L hl) _).mp hu_inv
    have e1 : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    have e2 := commutator_mul_of_comm hUab hyU hu hv
    rw [commutator_conj_blockU hL hyU hl (hyL l hl) hu_inv,
      hZc _ (hcomZ _ hu_inv) l hl, commutator_inv_of_comm hUab hyU hu] at e2
    have e3 : y * (u * (l * u⁻¹ * l⁻¹)) * y⁻¹ * (u * (l * u⁻¹ * l⁻¹))⁻¹ = 1 := by
      rw [e2]; group
    rw [e1, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have : h * (u * (l * u⁻¹ * l⁻¹)) * h⁻¹ = u * (l * u⁻¹ * l⁻¹) := by
      have := e3
      calc h * (u * (l * u⁻¹ * l⁻¹)) * h⁻¹
          = (h * (u * (l * u⁻¹ * l⁻¹)) * h⁻¹ * (u * (l * u⁻¹ * l⁻¹))⁻¹) *
              (u * (l * u⁻¹ * l⁻¹)) := by group
        _ = u * (l * u⁻¹ * l⁻¹) := by rw [this, one_mul]
    calc h * (u * (l * u⁻¹ * l⁻¹)) = (h * (u * (l * u⁻¹ * l⁻¹)) * h⁻¹) * h := by group
      _ = (u * (l * u⁻¹ * l⁻¹)) * h := by rw [this]
  intro u hu
  have := Subgroup.mem_centralizer_iff.mp (hle hu) y (Set.mem_singleton y)
  exact this.symm

theorem commutator_mem_blockQ_of_mem_pCoreOf [Finite G] {H : Subgroup G} (hLH : L ≤ H)
    (hHN : H ≤ normalizer (L : Set G)) {y : G} (hy : y ∈ pCoreOf 2 H) {l : G} (hl : l ∈ L) :
    y * l * y⁻¹ * l⁻¹ ∈ blockQ L := by
  have hPnorm : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hP2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hyN : y ∈ normalizer (L : Set G) :=
    hHN (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H hy)
  have h1 : y * l * y⁻¹ * l⁻¹ ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp hyN l).mp hl
    exact mul_mem this (inv_mem hl)
  have h2 : y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 H := by
    have h3 : l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (hPnorm (hLH hl)) y⁻¹).mp (inv_mem hy)
    have : y * l * y⁻¹ * l⁻¹ = y * (l * y⁻¹ * l⁻¹) := by group
    rw [this]
    exact mul_mem hy h3
  have hLP : L ⊓ pCoreOf 2 H ≤ blockQ L := by
    refine le_pCoreOf_of_normalized inf_le_left ?_ (hP2.to_le inf_le_right)
    intro g hg
    exact mem_normalizer_inf (Subgroup.le_normalizer hg) (hPnorm (hLH hg))
  exact hLP ⟨h1, h2⟩

theorem inf_centralizer_blockU_eq [Finite G] (hL : IsShort2 L) {H : Subgroup G} (hLH : L ≤ H)
    (hHN : H ≤ normalizer (L : Set G)) (hH2 : ∀ g ∈ H, ∃ k : ℕ, g ^ 2 ^ k ∈ L) :
    H ⊓ centralizer (blockU L : Set G) = pCoreOf 2 H := by
  have hPH : pCoreOf 2 H ≤ H := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H
  have hP2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  refine le_antisymm ?_ ?_
  ·
    set C := H ⊓ centralizer (blockU L : Set G) with hC
    have hC2 : IsPGroup 2 C := by
      intro g
      obtain ⟨m, hm⟩ := hH2 g (g.2.1)
      have hgm : (g : G) ^ 2 ^ m ∈ C := pow_mem g.2 _
      have hgmQ : (g : G) ^ 2 ^ m ∈ blockQ L :=
        inf_centralizer_blockU_le hL ⟨hm, hgm.2⟩
      obtain ⟨j, hj⟩ := exists_pow_eq_one_of_isPGroup (blockQ_isPGroup L) hgmQ
      refine ⟨m + j, Subtype.ext ?_⟩
      calc ((g ^ 2 ^ (m + j) : C) : G) = ((g : G) ^ 2 ^ m) ^ 2 ^ j := by
            rw [Subgroup.coe_pow, ← pow_mul, ← pow_add]
        _ = 1 := hj
        _ = ((1 : C) : G) := rfl
    have hCnorm : H ≤ normalizer (C : Set G) := fun g hg =>
      mem_normalizer_inf (Subgroup.le_normalizer hg)
        (mem_normalizer_centralizer (mem_normalizer_blockU (hHN hg)))
    exact le_pCoreOf_of_normalized inf_le_left hCnorm hC2
  · intro y hy
    refine ⟨hPH hy, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hyN : y ∈ normalizer (L : Set G) := hHN (hPH hy)
    have hy2 := exists_pow_eq_one_of_isPGroup hP2 hy
    have hyL : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ blockQ L := fun l hl =>
      commutator_mem_blockQ_of_mem_pCoreOf hLH hHN hy hl
    exact commute_blockU_of_mem hL hyN hy2 hyL u hu


theorem mem_blockQ_of_mul_mem [Finite G] (hL : IsShort2 L) {L' Mx : Subgroup G}
    (hc : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) (hMx2 : IsPGroup 2 Mx)
    (hLMx : L ≤ normalizer (Mx : Set G)) {a b : G} (ha : a ∈ L) (hb : b ∈ L')
    (hab : a * b ∈ Mx) : a ∈ blockQ L := by
  let M₁ : Subgroup G :=
    { carrier := {a | a ∈ L ∧ ∃ b ∈ L', a * b ∈ Mx}
      mul_mem' := by
        rintro a₁ a₂ ⟨ha₁, b₁, hb₁, h₁⟩ ⟨ha₂, b₂, hb₂, h₂⟩
        refine ⟨mul_mem ha₁ ha₂, b₁ * b₂, mul_mem hb₁ hb₂, ?_⟩
        have h12 := hc a₂ ha₂ b₁ hb₁
        have e : a₁ * a₂ * (b₁ * b₂) = (a₁ * b₁) * (a₂ * b₂) := by
          calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
            _ = a₁ * (b₁ * a₂) * b₂ := by rw [h12]
            _ = (a₁ * b₁) * (a₂ * b₂) := by group
        rw [e]
        exact mul_mem h₁ h₂
      one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, b, hb, h⟩
        refine ⟨inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        have e : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
          have := hc a ha b hb
          calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
            _ = (a * b)⁻¹ := by rw [← this]
        rw [e]
        exact inv_mem h }
  have hM₁L : M₁ ≤ L := fun x hx => hx.1
  have hM₁2 : IsPGroup 2 M₁ := by
    intro g
    obtain ⟨hgL, b', hb', hgb⟩ := g.2
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hMx2 hgb
    have hcomm : Commute (g : G) b' := hc g hgL b' hb'
    have h1 : (g : G) ^ 2 ^ k * b' ^ 2 ^ k = 1 := by
      rw [← hcomm.mul_pow]
      exact hk
    have h2 : (g : G) ^ 2 ^ k = (b' ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3' : (g : G) ^ 2 ^ k ∈ centralizer (blockQ L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [h2]
      exact hc x (blockQ_le L hx) _ (inv_mem (pow_mem hb' _))
    have h3 : (g : G) ^ 2 ^ k ∈ blockQ L := hL.2.1 ⟨pow_mem hgL _, h3'⟩
    obtain ⟨j, hj⟩ := exists_pow_eq_one_of_isPGroup (blockQ_isPGroup L) h3
    refine ⟨k + j, Subtype.ext ?_⟩
    calc ((g ^ 2 ^ (k + j) : M₁) : G) = ((g : G) ^ 2 ^ k) ^ 2 ^ j := by
          rw [Subgroup.coe_pow, ← pow_mul, ← pow_add]
      _ = 1 := hj
      _ = ((1 : M₁) : G) := rfl
  have hfwd : ∀ l ∈ L, ∀ x ∈ M₁, l * x * l⁻¹ ∈ M₁ := by
    rintro l hl x ⟨hxL, b', hb', hxb⟩
    refine ⟨mul_mem (mul_mem hl hxL) (inv_mem hl), b', hb', ?_⟩
    have hlb : l * b' = b' * l := hc l hl b' hb'
    have hlb' : l⁻¹ * b' = b' * l⁻¹ := by
      calc l⁻¹ * b' = l⁻¹ * (b' * l) * l⁻¹ := by group
        _ = l⁻¹ * (l * b') * l⁻¹ := by rw [hlb]
        _ = b' * l⁻¹ := by group
    have e : l * x * l⁻¹ * b' = l * (x * b') * l⁻¹ := by
      calc l * x * l⁻¹ * b' = l * x * (l⁻¹ * b') := by group
        _ = l * x * (b' * l⁻¹) := by rw [hlb']
        _ = l * (x * b') * l⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hLMx hl) _).mp hxb
  have hLM₁ : L ≤ normalizer (M₁ : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hfwd l hl x hx, fun h => by simpa [mul_assoc] using hfwd l⁻¹ (inv_mem hl) _ h⟩
  exact le_pCoreOf_of_normalized hM₁L hLM₁ hM₁2 ⟨ha, b, hb, hab⟩

theorem commutator_mem_blockU_double [Finite G] (hL : IsShort2 L) {L' H : Subgroup G}
    (hc : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) (hLH : L ≤ H)
    (hHN : H ≤ normalizer ((L ⊔ L' : Subgroup G) : Set G)) {p : G} (hp : p ∈ pCoreOf 2 H)
    {l : G} (hl : l ∈ L) : p * l * p⁻¹ * l⁻¹ ∈ blockU L := by
  have hPH : pCoreOf 2 H ≤ H := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H
  have hPnorm : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hP2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  set M : Subgroup G := pCoreOf 2 H ⊓ (L ⊔ L') with hMdef
  have hM2 : IsPGroup 2 M := hP2.to_le inf_le_left
  have hLK : L ≤ L ⊔ L' := le_sup_left
  have hLMnorm : L ≤ normalizer (M : Set G) := fun g hg =>
    mem_normalizer_inf (hPnorm (hLH hg)) (Subgroup.le_normalizer (hLK hg))
  have hsplit : ∀ w ∈ M, ∃ a ∈ blockQ L, ∃ b ∈ L', w = a * b := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc hw.2
    exact ⟨a, mem_blockQ_of_mul_mem hL hc hM2 hLMnorm ha hb hw, b, hb, rfl⟩
  refine commutator_mem_of_noTwoQuotient (L := L) (M := M) (N := blockU L) hL.1 hM2 ?_ ?_
    (y := p) ?_ l hl
  · intro m hm n hn
    obtain ⟨a, ha, b, hb, rfl⟩ := hsplit m hm
    have h1 : n * b = b * n := hc n ((blockU_le_blockQ hL).trans (blockQ_le L) hn) b hb
    have h2 : n * a = a * n := blockU_comm hL n hn a ha
    have : a * b * n * (a * b)⁻¹ = n := by
      calc a * b * n * (a * b)⁻¹ = a * (b * n) * b⁻¹ * a⁻¹ := by group
        _ = a * (n * b) * b⁻¹ * a⁻¹ := by rw [h1]
        _ = a * n * a⁻¹ := by group
        _ = n := by rw [← h2]; group
    rw [this]
    exact hn
  · intro l' hl' w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hsplit w hw
    have hlb : l' * b = b * l' := hc l' hl' b hb
    have : l' * (a * b) * l'⁻¹ * (a * b)⁻¹ = l' * a * l'⁻¹ * a⁻¹ := by
      calc l' * (a * b) * l'⁻¹ * (a * b)⁻¹ = l' * a * (b * l'⁻¹) * b⁻¹ * a⁻¹ := by group
        _ = l' * a * (l'⁻¹ * b) * b⁻¹ * a⁻¹ := by
            have : b * l'⁻¹ = l'⁻¹ * b := by
              calc b * l'⁻¹ = l'⁻¹ * (l' * b) * l'⁻¹ := by group
                _ = l'⁻¹ * (b * l') * l'⁻¹ := by rw [hlb]
                _ = l'⁻¹ * b := by group
            rw [this]
        _ = l' * a * l'⁻¹ * a⁻¹ := by group
    rw [this]
    exact commutator_mem_blockU' hl' ha
  · intro l' hl'
    refine ⟨?_, ?_⟩
    · have h3 : l' * p⁻¹ * l'⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (hPnorm (hLH hl')) p⁻¹).mp (inv_mem hp)
      have : p * l' * p⁻¹ * l'⁻¹ = p * (l' * p⁻¹ * l'⁻¹) := by group
      rw [this]
      exact mul_mem hp h3
    · have hpK : p * l' * p⁻¹ ∈ L ⊔ L' := (Subgroup.mem_normalizer_iff.mp (hHN (hPH hp)) l').mp
        (hLK hl')
      exact Subgroup.mul_mem _ hpK (Subgroup.inv_mem _ (hLK hl'))

end CFSG.QuasithinUnique.C1
