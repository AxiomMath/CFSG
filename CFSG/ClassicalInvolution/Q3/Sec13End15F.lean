module

public import CFSG.ClassicalInvolution.Q3.Sec13End15D
public import CFSG.ClassicalInvolution.Q3.Sec13EndPolar
import CFSG.ClassicalInvolution.Q3.Q3T6DConj

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem mem_normalizer_comm (h : EndHyp Ω) (h9 : Perp9 Ω) {M M' : Subgroup G} (hM : M ∈ Ω)
    (hM' : M' ∈ Ω) {b b' : G} (hb : IsUniqueInvolution M b) (hb' : IsUniqueInvolution M' b') :
    b' ∈ Subgroup.normalizer (M : Set G) ↔ b ∈ Subgroup.normalizer (M' : Set G) := by
  have key : ∀ {A B : Subgroup G}, A ∈ Ω → B ∈ Ω → ∀ {c c' : G}, IsUniqueInvolution A c →
      IsUniqueInvolution B c' → c' ∈ Subgroup.normalizer (A : Set G) →
        c ∈ Subgroup.normalizer (B : Set G) := by
    intro A B hA hB c c' hc hc' hN
    rcases h.mem_omegaStarNbr_or_twinSet h9 hA hB hc' hN with hstar | ⟨-, w, hw, hwB⟩
    · exact Q3T6D.mem_normalizer_of_mem_omegaStarNbr h.thmD.hyp
        (Q3T6.Mu.omegaStarNbr_symm h.thmD.hyp hA hB hstar) hc
    · rw [hc.eq hw]
      exact Subgroup.le_normalizer hwB.mem
  exact ⟨key hM hM' hb hb', key hM' hM hb' hb⟩

theorem normalizer_eq_of_involution_eq (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    {M M' : Subgroup G} (hM : M ∈ Ω) (hM' : M' ∈ Ω) {b : G} (hb : IsUniqueInvolution M b)
    (hb' : IsUniqueInvolution M' b) :
    Subgroup.normalizer (M : Set G) = Subgroup.normalizer (M' : Set G) := by
  clear h9
  obtain ⟨L', hne, hT⟩ := h.twinSet_pair s hM
  have hmem : M' ∈ twinSet Ω M := ⟨hM', b, hb, hb'⟩
  rw [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with e | e
  · rw [e]
  · have hT' : twinSet Ω M = {M, M'} := by rw [hT, e]
    have hne' : M ≠ M' := fun e2 => hne (e.symm.trans e2.symm)
    exact (h.normalizer_twin (⟨hM, hb, hT', hne'⟩ : TwinSit Ω M M' b)).1

@[expose] def zGroupCommGroup (h : EndHyp Ω) (h9 : Perp9 Ω) : CommGroup (zGroup Ω) :=
  { (inferInstance : Group (zGroup Ω)) with
    mul_comm := fun a b => Subtype.ext (h.zGroup_comm h9 a a.2 b b.2) }

end EndHyp

instance zGroupCommGroupOfFact {Ω : Set (Subgroup G)} [hh : Fact (EndHyp Ω)]
    [h9 : Fact (Perp9 Ω)] : CommGroup (zGroup Ω) :=
  hh.out.zGroupCommGroup h9.out

@[expose] def zPoints (Ω : Set (Subgroup G)) : Set (zGroup Ω) := {x | x.1 ∈ zSet Ω}

open Classical in
@[expose] noncomputable def bnorm (M : Subgroup G) (d : G) : ZMod 2 :=
  if d ∈ Subgroup.normalizer (M : Set G) then 0 else 1

open Classical in
@[expose] noncomputable def betaPt (Ω : Set (Subgroup G)) (b d : G) : ZMod 2 :=
  if hb : ∃ M ∈ Ω, IsUniqueInvolution M b then bnorm hb.choose d else 0

private theorem e15f_mem_zGroup {Ω : Set (Subgroup G)} {L : Subgroup G} {u : G}
    (hL : L ∈ Ω) (hu : IsUniqueInvolution L u) : u ∈ zGroup Ω :=
  Subgroup.subset_closure ⟨L, hL, hu⟩

private theorem e15f_map_one {V : Type*} [Group V] {F : V → ZMod 2}
    (hF : ∀ x y, F (x * y) = F x + F y) : F 1 = 0 := by
  have e : F 1 = F 1 + F 1 := by
    have h := hF 1 1
    rwa [mul_one] at h
  have key : ∀ t : ZMod 2, t = t + t → t = 0 := by decide
  exact key _ e

private theorem e15f_map_inv {V : Type*} [Group V] {F : V → ZMod 2}
    (hF : ∀ x y, F (x * y) = F x + F y) (y : V) : F y⁻¹ = F y := by
  have e : 0 = F y⁻¹ + F y := by
    have h := hF y⁻¹ y
    rwa [inv_mul_cancel, e15f_map_one hF] at h
  have key : ∀ p q : ZMod 2, 0 = p + q → p = q := by decide
  exact key _ _ e

private theorem e15f_symm {V : Type*} [Group V] {bf : V → V → ZMod 2}
    (hL : ∀ a a' b : V, bf (a * a') b = bf a b + bf a' b)
    (hR : ∀ a b b' : V, bf a (b * b') = bf a b + bf a b') (halt : ∀ a : V, bf a a = 0)
    (a b : V) : bf a b = bf b a := by
  have h := halt (a * b)
  simp only [hL, hR, halt, zero_add, add_zero] at h
  have key : ∀ p q : ZMod 2, p + q = 0 → p = q := by decide
  exact key _ _ h

private theorem e15f_closure_zPoints (Ω : Set (Subgroup G)) :
    Subgroup.closure (zPoints Ω) = ⊤ :=
  Subgroup.closure_closure_coe_preimage (k := zSet Ω)

private theorem e15f_eq_of_eq_on_zPoints {Ω : Set (Subgroup G)}
    (hgen : Subgroup.closure (zPoints Ω) = ⊤) {F F' : zGroup Ω → ZMod 2}
    (hF : ∀ x y, F (x * y) = F x + F y) (hF' : ∀ x y, F' (x * y) = F' x + F' y)
    (h : ∀ x ∈ zPoints Ω, F x = F' x) (x : zGroup Ω) : F x = F' x := by
  have hx : x ∈ Subgroup.closure (zPoints Ω) := by
    rw [hgen]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => rw [e15f_map_one hF, e15f_map_one hF']
  | mul y z _ _ hy hz => rw [hF, hF', hy, hz]
  | inv y _ hy => rw [e15f_map_inv hF, e15f_map_inv hF', hy]

private theorem e15f_conj_mem {Ω : Set (Subgroup G)} (h : EndHyp Ω) (g : G) {a : G}
    (ha : a ∈ zGroup Ω) : g * a * g⁻¹ ∈ zGroup Ω :=
  (zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant).conj_mem a ha g

private def e15f_cj {Ω : Set (Subgroup G)} (h : EndHyp Ω) (g : G) (a : zGroup Ω) :
    zGroup Ω :=
  ⟨g * a.1 * g⁻¹, e15f_conj_mem h g a.2⟩

private theorem e15f_cj_val {Ω : Set (Subgroup G)} (h : EndHyp Ω) (g : G) (a : zGroup Ω) :
    (e15f_cj h g a).1 = g * a.1 * g⁻¹ :=
  rfl

private theorem e15f_normalizer_conj (g d : G) (A : Subgroup G) :
    g * d * g⁻¹ ∈ Subgroup.normalizer (conjSub g A : Set G) ↔
      d ∈ Subgroup.normalizer (A : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq, mem_normalizer_iff_conjSub_eq]
  have e : conjSub (g * d * g⁻¹) (conjSub g A) = conjSub g (conjSub d A) := by
    rw [conjSub_mul, conjSub_mul, conjSub_inv_conjSub]
  rw [e]
  exact (conjSub_injective g).eq_iff

private theorem e15f_bnorm_eq_zero_iff (M : Subgroup G) (d : G) :
    bnorm M d = 0 ↔ d ∈ Subgroup.normalizer (M : Set G) := by
  unfold bnorm
  by_cases hd : d ∈ Subgroup.normalizer (M : Set G)
  · rw [if_pos hd]
    exact ⟨fun _ => hd, fun _ => rfl⟩
  · rw [if_neg hd]
    exact ⟨fun h1 => absurd h1 (by decide), fun h1 => absurd h1 hd⟩

private theorem e15f_conj_mem_twinSet {Ω : Set (Subgroup G)} (h : EndHyp Ω) (h9 : Perp9 Ω)
    {M : Subgroup G} (hM : M ∈ Ω) {b : G} (hb : IsUniqueInvolution M b) {d : G}
    (hd : d ∈ zGroup Ω) : conjSub d M ∈ twinSet Ω M := by
  have hc : d * b = b * d := h.zGroup_comm h9 d hd b (e15f_mem_zGroup hM hb)
  have hconj := hb.conj d
  have e : d * b * d⁻¹ = b := by rw [hc, mul_inv_cancel_right]
  rw [e] at hconj
  exact ⟨h.thmD.hyp.conjInvariant d M hM, b, hb, hconj⟩

open Classical in
private theorem e15f_bnorm_mul {Ω : Set (Subgroup G)} (h : EndHyp Ω) (h9 : Perp9 Ω)
    {M L' : Subgroup G} {b : G} (hM : M ∈ Ω) (hbM : IsUniqueInvolution M b) (hne : L' ≠ M)
    (hT : twinSet Ω M = {M, L'}) {d d' : G} (hd : d ∈ zGroup Ω) (hd' : d' ∈ zGroup Ω) :
    bnorm M (d * d') = bnorm M d + bnorm M d' := by
  have hsub : ∀ x ∈ zGroup Ω, conjSub x M = M ∨ conjSub x M = L' := fun x hx => by
    have hm := e15f_conj_mem_twinSet h h9 hM hbM hx
    rw [hT] at hm
    exact hm
  have hsq : ∀ x ∈ zGroup Ω, ∀ A B : Subgroup G, conjSub x A = B → conjSub x B = A := by
    intro x hx A B hAB
    rw [← hAB, ← conjSub_mul, h.zGroup_mul_self h9 x hx, conjSub_one]
  have hbn : ∀ x : G, bnorm M x = if conjSub x M = M then 0 else 1 := by
    intro x
    unfold bnorm
    by_cases hx : x ∈ Subgroup.normalizer (M : Set G)
    · rw [if_pos hx, if_pos (mem_normalizer_iff_conjSub_eq.mp hx)]
    · rw [if_neg hx, if_neg (fun h' => hx (mem_normalizer_iff_conjSub_eq.mpr h'))]
  rw [hbn, hbn, hbn]
  rcases hsub d hd with h1 | h1 <;> rcases hsub d' hd' with h2 | h2
  · have h3 : conjSub (d * d') M = M := by rw [conjSub_mul, h2, h1]
    rw [if_pos h3, if_pos h1, if_pos h2]
    decide
  · have h3 : conjSub (d * d') M ≠ M := by
      rw [conjSub_mul, h2]
      intro h4
      have h5 := hsq d hd L' M h4
      rw [h1] at h5
      exact hne h5.symm
    have h6 : ¬ conjSub d' M = M := by
      rw [h2]
      exact hne
    rw [if_neg h3, if_pos h1, if_neg h6]
    decide
  · have h3 : conjSub (d * d') M ≠ M := by
      rw [conjSub_mul, h2, h1]
      exact hne
    have h6 : ¬ conjSub d M = M := by
      rw [h1]
      exact hne
    rw [if_neg h3, if_neg h6, if_pos h2]
    decide
  · have h3 : conjSub (d * d') M = M := by
      rw [conjSub_mul, h2]
      exact hsq d hd M L' h1
    have h6 : ¬ conjSub d M = M := by
      rw [h1]
      exact hne
    have h7 : ¬ conjSub d' M = M := by
      rw [h2]
      exact hne
    rw [if_pos h3, if_neg h6, if_neg h7]
    decide

private noncomputable def e15f_beta (Ω : Set (Subgroup G)) (a x : zGroup Ω) : ZMod 2 :=
  betaPt Ω a.1 x.1

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem betaPt_eq (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z) {M : Subgroup G}
    (hM : M ∈ Ω) {b : G} (hb : IsUniqueInvolution M b) (d : G) :
    betaPt Ω b d = bnorm M d := by
  have hex : ∃ M₀ ∈ Ω, IsUniqueInvolution M₀ b := ⟨M, hM, hb⟩
  obtain ⟨hM₀, hb₀⟩ := hex.choose_spec
  have hN := h.normalizer_eq_of_involution_eq h9 s hM₀ hM hb₀ hb
  unfold betaPt
  rw [dif_pos hex]
  unfold bnorm
  rw [hN]

theorem betaPt_mul (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {b : G} (hb : b ∈ zSet Ω) {d d' : G} (hd : d ∈ zGroup Ω)
    (hd' : d' ∈ zGroup Ω) : betaPt Ω b (d * d') = betaPt Ω b d + betaPt Ω b d' := by
  clear h13
  obtain ⟨B, hB, hbB⟩ := hb
  obtain ⟨L', hne, hT⟩ := h.twinSet_pair s hB
  rw [h.betaPt_eq h9 s hB hbB, h.betaPt_eq h9 s hB hbB, h.betaPt_eq h9 s hB hbB]
  exact e15f_bnorm_mul h h9 hB hbB hne hT hd hd'

theorem betaPt_self (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z) {b : G}
    (hb : b ∈ zSet Ω) : betaPt Ω b b = 0 := by
  obtain ⟨B, hB, hbB⟩ := hb
  rw [h.betaPt_eq h9 s hB hbB b]
  exact (e15f_bnorm_eq_zero_iff B b).mpr (Subgroup.le_normalizer hbB.mem)

private theorem e15f_betaPt_conj (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z) (g : G)
    {b : G} (hb : b ∈ zSet Ω) (d : G) :
    betaPt Ω (g * b * g⁻¹) (g * d * g⁻¹) = betaPt Ω b d := by
  obtain ⟨B, hB, hbB⟩ := hb
  rw [h.betaPt_eq h9 s (h.thmD.hyp.conjInvariant g B hB) (hbB.conj g) (g * d * g⁻¹),
    h.betaPt_eq h9 s hB hbB d]
  unfold bnorm
  by_cases hd : d ∈ Subgroup.normalizer (B : Set G)
  · rw [if_pos hd, if_pos ((e15f_normalizer_conj g d B).mpr hd)]
  · rw [if_neg hd, if_neg (fun h' => hd ((e15f_normalizer_conj g d B).mp h'))]

theorem betaPt_symm (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z) {a b : G}
    (ha : a ∈ zSet Ω) (hb : b ∈ zSet Ω) : betaPt Ω b a = betaPt Ω a b := by
  obtain ⟨A, hA, hau⟩ := ha
  obtain ⟨B, hB, hbu⟩ := hb
  have hiff := h.mem_normalizer_comm h9 hB hA hbu hau
  rw [h.betaPt_eq h9 s hB hbu a, h.betaPt_eq h9 s hA hau b]
  unfold bnorm
  by_cases hd : a ∈ Subgroup.normalizer (B : Set G)
  · rw [if_pos hd, if_pos (hiff.mp hd)]
  · rw [if_neg hd, if_neg (fun h' => hd (hiff.mpr h'))]

end EndHyp

structure IsEndForm (Ω : Set (Subgroup G)) (bf : zGroup Ω → zGroup Ω → ZMod 2) : Prop where
  mul_left : ∀ a a' b : zGroup Ω, bf (a * a') b = bf a b + bf a' b
  mul_right : ∀ a b b' : zGroup Ω, bf a (b * b') = bf a b + bf a b'
  alt : ∀ a : zGroup Ω, bf a a = 0
  nondeg : ∀ a : zGroup Ω, (∀ b : zGroup Ω, bf a b = 0) → a = 1
  conj : ∀ (g : G) (a b a' b' : zGroup Ω), a'.1 = g * a.1 * g⁻¹ → b'.1 = g * b.1 * g⁻¹ →
    bf a' b' = bf a b
  spec : ∀ M ∈ Ω, ∀ b : zGroup Ω, IsUniqueInvolution M b.1 → ∀ a : zGroup Ω,
    bf a b = 0 ↔ a.1 ∈ Subgroup.normalizer (M : Set G)

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem exists_biadditive (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) :
    ∃ bf : zGroup Ω → zGroup Ω → ZMod 2,
      (∀ a a' b : zGroup Ω, bf (a * a') b = bf a b + bf a' b) ∧
      (∀ a b b' : zGroup Ω, bf a (b * b') = bf a b + bf a b') ∧ (∀ a : zGroup Ω, bf a a = 0) ∧
      (∀ (g : G) (a b a' b' : zGroup Ω), a'.1 = g * a.1 * g⁻¹ → b'.1 = g * b.1 * g⁻¹ →
        bf a' b' = bf a b) ∧
      ∀ M ∈ Ω, ∀ b : zGroup Ω, IsUniqueInvolution M b.1 → ∀ a : zGroup Ω,
        bf a b = 0 ↔ a.1 ∈ Subgroup.normalizer (M : Set G) := by
  obtain ⟨B, hB1₀, hB2₀, hB3₀, hB4⟩ := @Polar.exists_form_of_symmetric (zGroup Ω)
    (h.zGroupCommGroup h9) (zPoints Ω) (e15f_closure_zPoints Ω)
    (fun a => Subtype.ext (h.zGroup_mul_self h9 a.1 a.2)) (e15f_beta Ω)
    (fun a ha b b' => h.betaPt_mul h9 s h13 (b := a.1) ha (d := b.1) (d' := b'.1) b.2 b'.2)
    (fun a ha b hb => (h.betaPt_symm h9 s (a := a.1) (b := b.1) ha hb).symm)
    (fun a ha => h.betaPt_self h9 s (b := a.1) ha)
  have hB1 : ∀ a a' b : zGroup Ω, B (a * a') b = B a b + B a' b := hB1₀
  have hB2 : ∀ a b b' : zGroup Ω, B a (b * b') = B a b + B a b' := hB2₀
  have hB3 : ∀ a : zGroup Ω, B a a = 0 := hB3₀
  have hsymm : ∀ a b, B a b = B b a := fun a b => e15f_symm (bf := B) hB1 hB2 hB3 a b
  have hcj_pts : ∀ g : G, ∀ a ∈ zPoints Ω, e15f_cj h g a ∈ zPoints Ω := by
    intro g a ha
    obtain ⟨A, hA, hau⟩ := ha
    exact ⟨conjSub g A, h.thmD.hyp.conjInvariant g A hA, hau.conj g⟩
  have hcj_mul : ∀ (g : G) (a b : zGroup Ω),
      e15f_cj h g (a * b) = e15f_cj h g a * e15f_cj h g b := by
    intro g a b
    apply Subtype.ext
    simp only [e15f_cj, Subgroup.coe_mul]
    group
  have hpts : ∀ g : G, ∀ a ∈ zPoints Ω, ∀ b : zGroup Ω,
      B (e15f_cj h g a) (e15f_cj h g b) = B a b := by
    intro g a ha b
    rw [hB4 _ (hcj_pts g a ha), hB4 a ha]
    exact h.e15f_betaPt_conj h9 s g (b := a.1) ha b.1
  have step1 : ∀ g : G, ∀ a ∈ zPoints Ω, ∀ b : zGroup Ω,
      B (e15f_cj h g a) (e15f_cj h g b) = B a b := by
    intro g a ha b
    exact e15f_eq_of_eq_on_zPoints (e15f_closure_zPoints Ω)
      (F := fun x => B (e15f_cj h g a) (e15f_cj h g x)) (F' := fun x => B a x)
      (fun x y => by simp only [hcj_mul, hB2]) (fun x y => hB2 a x y)
      (fun x _ => hpts g a ha x) b
  have hall : ∀ (g : G) (a b : zGroup Ω), B (e15f_cj h g a) (e15f_cj h g b) = B a b := by
    intro g a b
    exact e15f_eq_of_eq_on_zPoints (e15f_closure_zPoints Ω)
      (F := fun x => B (e15f_cj h g x) (e15f_cj h g b)) (F' := fun x => B x b)
      (fun x y => by simp only [hcj_mul, hB1]) (fun x y => hB1 x y b)
      (fun x hx => step1 g x hx b) a
  refine ⟨B, hB1, hB2, hB3, ?_, ?_⟩
  · intro g a b a' b' ha hb
    rw [show a' = e15f_cj h g a from Subtype.ext ha,
      show b' = e15f_cj h g b from Subtype.ext hb]
    exact hall g a b
  · intro M hM b hb a
    have hbS : b ∈ zPoints Ω := ⟨M, hM, hb⟩
    rw [hsymm a b, hB4 b hbS a]
    unfold e15f_beta
    rw [h.betaPt_eq h9 s hM hb a.1]
    exact e15f_bnorm_eq_zero_iff M a.1

theorem nondeg_of_biadditive (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (bf : zGroup Ω → zGroup Ω → ZMod 2)
    (hmulL : ∀ a a' b : zGroup Ω, bf (a * a') b = bf a b + bf a' b)
    (hmul : ∀ a b b' : zGroup Ω, bf a (b * b') = bf a b + bf a b')
    (hinv : ∀ (g : G) (a b a' b' : zGroup Ω), a'.1 = g * a.1 * g⁻¹ → b'.1 = g * b.1 * g⁻¹ →
      bf a' b' = bf a b)
    (hspec : ∀ M ∈ Ω, ∀ b : zGroup Ω, IsUniqueInvolution M b.1 → ∀ a : zGroup Ω,
      bf a b = 0 ↔ a.1 ∈ Subgroup.normalizer (M : Set G)) :
    ∀ a : zGroup Ω, (∀ b : zGroup Ω, bf a b = 0) → a = 1 := by
  clear hmul
  have hone : ∀ b : zGroup Ω, bf 1 b = 0 := fun b =>
    e15f_map_one (F := fun x => bf x b) (fun x y => hmulL x y b)
  have hinvL : ∀ a b : zGroup Ω, bf a⁻¹ b = bf a b := fun a b =>
    e15f_map_inv (F := fun x => bf x b) (fun x y => hmulL x y b) a
  have hconjR : ∀ (g : G) (a : zGroup Ω), (∀ b, bf a b = 0) →
      ∀ b : zGroup Ω, bf (e15f_cj h g a) b = 0 := by
    intro g a ha b
    have hcond : b.1 = g * (e15f_cj h g⁻¹ b).1 * g⁻¹ := by
      rw [e15f_cj_val]
      group
    rw [hinv g a (e15f_cj h g⁻¹ b) (e15f_cj h g a) b rfl hcond]
    exact ha _
  have hnopt : ∀ p : zGroup Ω, p.1 ∈ zSet Ω → (∀ b, bf p b = 0) → False := by
    intro p hp hpR
    have hpts : ∀ x : zGroup Ω, x.1 ∈ zSet Ω → ∀ b, bf x b = 0 := by
      intro x hx
      obtain ⟨L, hL, hLp⟩ := hp
      obtain ⟨M, hM, hMx⟩ := hx
      obtain ⟨g, hg⟩ := h.thmD.trans L hL M hM
      have hc : IsUniqueInvolution M (g * p.1 * g⁻¹) := by
        rw [← hg]
        exact hLp.conj g
      have hxg : x = e15f_cj h g p := Subtype.ext (hMx.eq hc)
      rw [hxg]
      exact hconjR g p hpR
    have hdall : ∀ d : zGroup Ω, ∀ b, bf d b = 0 := by
      intro d
      have hd : d ∈ Subgroup.closure (zPoints Ω) := by
        rw [e15f_closure_zPoints]
        exact Subgroup.mem_top d
      induction hd using Subgroup.closure_induction with
      | mem x hx => exact hpts x hx
      | one => exact hone
      | mul x y _ _ hx hy => exact fun b => by rw [hmulL, hx b, hy b, add_zero]
      | inv x _ hx => exact fun b => by rw [hinvL, hx b]
    obtain ⟨d₀, hd₀, hsw⟩ := h.exists_mem_zGroup_swap h9 s h13
    have hdN := (hspec K s.mem ⟨z, e15f_mem_zGroup s.mem s.isInv⟩ s.isInv ⟨d₀, hd₀⟩).mp
      (hdall ⟨d₀, hd₀⟩ _)
    have hK : conjSub d₀ K = K := mem_normalizer_iff_conjSub_eq.mp hdN
    exact s.ne (hK.symm.trans hsw)
  have hcomm : ∀ (L : Subgroup G), L ∈ Ω → ∀ r : zGroup Ω, (∀ b, bf r b = 0) →
      ∀ l ∈ L, l * r.1 = r.1 * l := by
    intro L hL r hr l hl
    obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hL
    have huD : u ∈ zGroup Ω := e15f_mem_zGroup hL hu
    have hrN : r.1 ∈ Subgroup.normalizer (L : Set G) :=
      (hspec L hL ⟨u, huD⟩ hu r).mp (hr _)
    have hcL : l * r.1 * l⁻¹ * r.1⁻¹ ∈ L := by
      have h1 : r.1 * l⁻¹ * r.1⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hrN l⁻¹).mp (L.inv_mem hl)
      have e : l * r.1 * l⁻¹ * r.1⁻¹ = l * (r.1 * l⁻¹ * r.1⁻¹) := by group
      rw [e]
      exact L.mul_mem hl h1
    have hcD : l * r.1 * l⁻¹ * r.1⁻¹ ∈ zGroup Ω :=
      (zGroup Ω).mul_mem (e15f_conj_mem h l r.2) ((zGroup Ω).inv_mem r.2)
    have hcR : ∀ b, bf ⟨l * r.1 * l⁻¹ * r.1⁻¹, hcD⟩ b = 0 := by
      have e : (⟨l * r.1 * l⁻¹ * r.1⁻¹, hcD⟩ : zGroup Ω) = e15f_cj h l r * r⁻¹ := rfl
      rw [e]
      intro b
      rw [hmulL, hconjR l r hr b, hinvL, hr b, add_zero]
    have hsq : (l * r.1 * l⁻¹ * r.1⁻¹) * (l * r.1 * l⁻¹ * r.1⁻¹) = 1 :=
      h.zGroup_mul_self h9 _ hcD
    rcases hu.unique _ hcL hsq with h1 | h1
    · calc l * r.1 = (l * r.1 * l⁻¹ * r.1⁻¹) * (r.1 * l) := by group
        _ = r.1 * l := by rw [h1, one_mul]
    · exfalso
      have hpu : (⟨u, huD⟩ : zGroup Ω) = ⟨l * r.1 * l⁻¹ * r.1⁻¹, hcD⟩ :=
        Subtype.ext h1.symm
      exact hnopt ⟨u, huD⟩ ⟨L, hL, hu⟩ (by rw [hpu]; exact hcR)
  intro r hr
  have hcent : ∀ L ∈ Ω, L ≤ Subgroup.centralizer ({r.1} : Set G) := by
    intro L hL l hl
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm L hL r hr l hl)
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({r.1} : Set G) := by
    have hp := pSpan_le hcent
    rwa [h.thmD.gen] at hp
  have hc : r.1 ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top g))
  rw [h.center, Subgroup.mem_bot] at hc
  exact Subtype.ext hc

end EndHyp

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem exists_endForm (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) : ∃ bf : zGroup Ω → zGroup Ω → ZMod 2, IsEndForm Ω bf := by
  obtain ⟨bf, hL, hR, halt, hinv, hspec⟩ := h.exists_biadditive h9 s h13
  exact ⟨bf, hL, hR, halt, h.nondeg_of_biadditive h9 s h13 bf hL hR hinv hspec, hinv, hspec⟩

end EndHyp

namespace IsEndForm

variable {Ω : Set (Subgroup G)} {bf : zGroup Ω → zGroup Ω → ZMod 2}

theorem symm (hbf : IsEndForm Ω bf) (a b : zGroup Ω) : bf a b = bf b a :=
  e15f_symm (bf := bf) (fun a a' b => hbf.mul_left a a' b)
    (fun a b b' => hbf.mul_right a b b') hbf.alt a b

theorem eq_of_forall_eq (hbf : IsEndForm Ω bf) {a a' : zGroup Ω}
    (h : ∀ b : zGroup Ω, bf b a = bf b a') : a = a' := by
  have hc : ∀ b : zGroup Ω, bf b (a * a'⁻¹) = 0 := fun b => by
    have hinvb : bf b a'⁻¹ = bf b a' :=
      e15f_map_inv (F := fun x => bf b x) (fun x y => hbf.mul_right b x y) a'
    have key : ∀ p : ZMod 2, p + p = 0 := by decide
    rw [hbf.mul_right, hinvb, ← h b]
    exact key _
  have hc' : a * a'⁻¹ = 1 := hbf.nondeg _ (fun b => by rw [hbf.symm]; exact hc b)
  exact mul_inv_eq_one.mp hc'

theorem sympForm [Fact (EndHyp Ω)] [Fact (Perp9 Ω)] (hbf : IsEndForm Ω bf) :
    Polar.SympForm bf :=
  { sq_eq_one := fun a =>
      Subtype.ext ((Fact.out : EndHyp Ω).zGroup_mul_self (Fact.out : Perp9 Ω) a.1 a.2)
    mul_left := hbf.mul_left
    mul_right := hbf.mul_right
    alt := hbf.alt
    nondeg := hbf.nondeg }

end IsEndForm

end CFSG.ClassicalInvolution.Q3.Sec13
