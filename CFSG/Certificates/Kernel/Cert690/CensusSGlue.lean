module

public import CFSG.Certificates.Kernel.Cert690.CensusSBaseSound
public import CFSG.Certificates.Kernel.Cert690.CensusSMax
public import CFSG.Certificates.Kernel.Cert690.CBaseSound
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Good
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Interface
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.MainFacts

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.C690S

open CFSG.KC.C690 CFSG.KC.Enum CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.O62

theorem cd_mul {x y : V₀ ≃ₗ[ZMod 2] V₀} {a b : ℕ} (hx : Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) a)
    (hy : Code.HasCode (y : V₀ →ₗ[ZMod 2] V₀) b) :
    Code.HasCode ((x * y : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) (mulF a b) := by
  rw [mulF_eq]
  exact hx.mul hy

theorem cd_one : Code.HasCode ((1 : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) oneF := by
  rw [oneF_eq]
  exact Code.hasCode_one

theorem cd_inv {x : V₀ ≃ₗ[ZMod 2] V₀} {a b : ℕ} (hx : Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) a)
    (h : mulF a b = oneF) : Code.HasCode ((x⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) b :=
  hasCode_inv_of_mul_eq_one hx (by rw [← mulF_eq, h, oneF_eq])

theorem mulF_lt (a b : ℕ) : mulF a b < 2 ^ 36 := by
  rw [mulF_eq]
  exact Code.mul_lt _ _

theorem oneF_lt : oneF < 2 ^ 36 := by
  rw [oneF_eq]
  decide

theorem actS_eq (m v : ℕ) : actS m v = Code.act m v := (act_eq_actF m v).symm

theorem actS_lt (m v : ℕ) : actS m v < 64 := by
  rw [actS_eq]
  exact Code.act_lt _ _

theorem cd_vec {x : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ} (hx : Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) m)
    (v : ℕ) : x (Code.vec v) = Code.vec (actS m v) := by
  rw [actS_eq]
  exact apply_vec_of_hasCode hx v

theorem fix_iff {x : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ} (hx : Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) m)
    {b : ℕ} (hb : b < 64) : actS m b = b ↔ x (Code.vec b) = Code.vec b := by
  rw [cd_vec hx]
  exact ⟨fun h => by rw [h], fun h => vec_injective_of_lt (actS_lt _ _) hb h⟩

theorem cd_wvS {Lx : ℕ → V₀ ≃ₗ[ZMod 2] V₀} {L : ℕ → ℕ} :
    ∀ (w : List ℕ) {x : V₀ ≃ₗ[ZMod 2] V₀} {a : ℕ},
      (∀ q ∈ w, Code.HasCode (Lx q : V₀ →ₗ[ZMod 2] V₀) (L q)) →
      Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) a →
      Code.HasCode ((x * (w.map Lx).prod : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) (wvS L w a)
  | [], x, a, _, hx => by
    rw [List.map_nil, List.prod_nil, mul_one]
    exact hx
  | q :: w, x, a, hw, hx => by
    have e : wvS L (q :: w) a = wvS L w (mulF a (L q)) := by
      change strictN (mulF a (L q)) (wvS L w) = _
      rw [strictN_eqS]
    rw [e, List.map_cons, List.prod_cons, ← mul_assoc]
    exact cd_wvS w (fun q' hq' => hw q' (List.mem_cons_of_mem _ hq'))
      (cd_mul hx (hw q List.mem_cons_self))

theorem cd_wiS {Lx : ℕ → V₀ ≃ₗ[ZMod 2] V₀} {L : ℕ → ℕ} :
    ∀ (w : List ℕ) {x : V₀ ≃ₗ[ZMod 2] V₀} {a : ℕ},
      (∀ q ∈ w, Code.HasCode (Lx q : V₀ →ₗ[ZMod 2] V₀) (L q)) →
      Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) a →
      Code.HasCode (((w.map Lx).reverse.prod * x : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
        (wiS L w a)
  | [], x, a, _, hx => by
    rw [List.map_nil, List.reverse_nil, List.prod_nil, one_mul]
    exact hx
  | q :: w, x, a, hw, hx => by
    have e : wiS L (q :: w) a = wiS L w (mulF (L q) a) := by
      change strictN (mulF (L q) a) (wiS L w) = _
      rw [strictN_eqS]
    rw [e, List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, mul_assoc]
    exact cd_wiS w (fun q' hq' => hw q' (List.mem_cons_of_mem _ hq'))
      (cd_mul (hw q List.mem_cons_self) hx)

theorem prod_inv_eq (Lx : ℕ → V₀ ≃ₗ[ZMod 2] V₀) (w : List ℕ) :
    ((w.map Lx).prod)⁻¹ = (w.map fun q => (Lx q)⁻¹).reverse.prod := by
  rw [List.prod_inv_reverse, List.map_map]
  rfl

theorem pow2_rec {x : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ} (hx : Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) m) :
    ∀ n, Code.HasCode ((x ^ (2 ^ n) : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
      (Nat.rec (motive := fun _ => Nat) m (fun _ ih => strictN ih fun y => mulF y y) n)
  | 0 => by rw [pow_zero, pow_one]; exact hx
  | n + 1 => by
    change Code.HasCode _ (strictN (Nat.rec (motive := fun _ => Nat) m
      (fun _ ih => strictN ih fun y => mulF y y) n) fun y => mulF y y)
    rw [strictN_eqS, pow_succ, pow_mul, pow_two]
    exact cd_mul (pow2_rec hx n) (pow2_rec hx n)

theorem cd_pow128 {x : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ} (hx : Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) m) :
    Code.HasCode ((x ^ 128 : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) (pow128 m) :=
  pow2_rec hx 7

theorem pow128_lt (m : ℕ) : pow128 m < 2 ^ 36 := by
  change strictN (Nat.rec (motive := fun _ => Nat) m (fun _ ih => strictN ih fun y => mulF y y) 6)
    (fun y => mulF y y) < 2 ^ 36
  rw [strictN_eqS]
  exact mulF_lt _ _

theorem forall₂_mem_left {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | [], [], .nil, _, ha => absurd ha List.not_mem_nil
  | x :: _, y :: _, .cons hxy h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, List.mem_cons_self, hxy⟩
    · obtain ⟨b, hb, hab⟩ := forall₂_mem_left h a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem forall₂_mem_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | [], [], .nil, _, hb => absurd hb List.not_mem_nil
  | x :: _, y :: _, .cons hxy h, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨x, List.mem_cons_self, hxy⟩
    · obtain ⟨a, ha, hab⟩ := forall₂_mem_right h b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

theorem forall₂_getD {α β : Type*} {R : α → β → Prop} (d₁ : α) (d₂ : β) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ q < l₁.length,
      R (l₁.getD q d₁) (l₂.getD q d₂)
  | [], [], .nil, q, hq => absurd hq (Nat.not_lt_zero _)
  | _ :: _, _ :: _, .cons hxy h, q, hq => by
    cases q with
    | zero => exact hxy
    | succ q =>
      simp only [List.getD_cons_succ]
      exact forall₂_getD d₁ d₂ h q (by simpa using hq)

theorem getD_mem_of_lt {l : List ℕ} {q : ℕ} (h : q < l.length) (d : ℕ) : l.getD q d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

variable {minus : Bool} {D : GrpData} (hD : GrpFacts minus D) {G : GK}

@[expose] noncomputable def eltC (hD : GrpFacts minus D) (G : GK) (c : ℕ) :
    V₀ ≃ₗ[ZMod 2] V₀ :=
  hD.elt (G.ix c)

include hD in
theorem cd_eltC (hR : GRel D G) {c : ℕ} (h : InOS G c) :
    Code.HasCode (eltC hD G c : V₀ →ₗ[ZMod 2] V₀) c ∧ eltC hD G c ∈ O₀ minus ∧ c < 2 ^ 36 := by
  have hi : G.ix c < D.O.size := by rw [hR.size]; exact h.1
  have he : D.O[G.ix c]! = c := (hR.get _).trans h.2
  have hc := hD.hasCode_elt hi
  have hl := hD.code_lt hi
  rw [he] at hc hl
  exact ⟨hc, hD.elt_mem_O₀ hi, hl⟩

structure LFacts (L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) (lg lc : List ℕ) : Prop where
  mem : ∀ x, x ∈ L ↔ ∃ c ∈ lc, Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c
  lt : ∀ c ∈ lc, c < 2 ^ 36
  le : L ≤ Subgroup.closure
    {x : V₀ ≃ₗ[ZMod 2] V₀ | ∃ c ∈ lg, Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c}
  gen : ∀ c ∈ lg, ∃ x ∈ L, Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c

theorem norS_iff_mem {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {lg lc : List ℕ} (hL : LFacts L lg lc)
    {X : V₀ ≃ₗ[ZMod 2] V₀} {x xi : ℕ} (hx : Code.HasCode (X : V₀ →ₗ[ZMod 2] V₀) x)
    (hxi : Code.HasCode ((X⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) xi) :
    NorS lg lc x xi ↔ X ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
  have : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  constructor
  · intro h
    have hmap : ∀ z ∈ L, X * z * X⁻¹ ∈ L := by
      intro z hz
      have hz' := hL.le hz
      clear hz
      induction hz' using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨c, hc, hyc⟩ := hy
        exact (hL.mem _).mpr ⟨_, h c hc, cd_mul (cd_mul hx hyc) hxi⟩
      | one =>
        rw [mul_one, mul_inv_cancel]
        exact L.one_mem
      | mul a b _ _ ha hb =>
        have e : X * (a * b) * X⁻¹ = (X * a * X⁻¹) * (X * b * X⁻¹) := by group
        rw [e]
        exact L.mul_mem ha hb
      | inv a _ ha =>
        have e : X * a⁻¹ * X⁻¹ = (X * a * X⁻¹)⁻¹ := by group
        rw [e]
        exact L.inv_mem ha
    have hmap_le : L.map (MulAut.conj X).toMonoidHom ≤ L := by
      rintro z ⟨y, hy, rfl⟩
      exact hmap y hy
    have heq : L.map (MulAut.conj X).toMonoidHom = L := by
      refine eq_of_le_of_natCard hmap_le ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj X).injective]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  · intro hn c hc
    obtain ⟨y, hy, hyc⟩ := hL.gen c hc
    obtain ⟨c', hc', hcd⟩ := (hL.mem _).mp ((Subgroup.mem_normalizer_iff.mp hn y).mp hy)
    rw [Code.HasCode.code_eq (cd_mul (cd_mul hx hyc) hxi) hcd (mulF_lt _ _) (hL.lt c' hc')]
    exact hc'

theorem mem_centralizer_of_comm {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {lg lc : List ℕ}
    (hL : LFacts L lg lc) {X : V₀ ≃ₗ[ZMod 2] V₀} {x : ℕ}
    (hx : Code.HasCode (X : V₀ →ₗ[ZMod 2] V₀) x) (h : ∀ y ∈ lg, mulF x y = mulF y x) :
    X ∈ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hc : Commute z X := by
    have hz' := hL.le hz
    clear hz
    induction hz' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, hc, hyc⟩ := hy
      have h1 := cd_mul hx hyc
      rw [h c hc] at h1
      exact (Code.HasCode.eq_of_equiv h1 (cd_mul hyc hx)).symm
    | one => exact Commute.one_left X
    | mul a b _ _ ha hb => exact ha.mul_left hb
    | inv a _ ha => exact ha.inv_left
  exact hc.eq

theorem not_goodElt_of_badS {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {lg lc : List ℕ}
    (hL : LFacts L lg lc) {b : ℕ} (hb : b < 64) {X : V₀ ≃ₗ[ZMod 2] V₀} {x xi : ℕ}
    (hx : Code.HasCode (X : V₀ →ₗ[ZMod 2] V₀) x)
    (hxi : Code.HasCode ((X⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) xi)
    (hbad : BadS b lg lc x xi) : ¬ GoodElt minus L (Code.vec b) X := by
  rintro ⟨-, hfix, hcen⟩
  rcases hbad with h | ⟨hcomm, hpow⟩
  · apply h
    rw [fix_iff hx hb, norS_iff_mem hL hx hxi]
    exact hfix
  · apply hpow
    have h1 := hcen (mem_centralizer_of_comm hL hx hcomm)
    have h2 := cd_pow128 hx
    rw [h1] at h2
    exact Code.HasCode.code_eq h2 cd_one (pow128_lt x) oneF_lt

theorem stab_orbit {O : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} (e : V₀) (n : ℕ)
    (s : ℕ → V₀ ≃ₗ[ZMod 2] V₀) (hs : ∀ k < n, s k ∈ O ∧ s k e = e)
    (hinj : ∀ i < n, ∀ j < n, s i = s j → i = j) (Y : Finset V₀)
    (hY : ∀ y ∈ Y, ∃ t ∈ O, t e = y) (hcard : n * Y.card = Nat.card O) :
    (∀ y ∈ O, y e = e → ∃ k < n, y = s k) ∧ (∀ y ∈ O, y e ∈ Y) := by
  classical
  have : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  let st := MulAction.stabilizer O e
  have h1 : Nat.card st * st.index = Nat.card O := Subgroup.card_mul_index st
  have h2 : st.index = Nat.card (MulAction.orbit O e) := MulAction.index_stabilizer O e
  let f : Fin n → st := fun k => ⟨⟨s k, (hs k k.2).1⟩, by
    rw [MulAction.mem_stabilizer_iff]
    exact (hs k k.2).2⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    have : s i = s j := congrArg (fun z : st => ((z : O) : V₀ ≃ₗ[ZMod 2] V₀)) hij
    exact Fin.ext (hinj i i.2 j j.2 this)
  have hst : n ≤ Nat.card st := by
    simpa using Nat.card_le_card_of_injective f hfinj
  have hsub : (Y : Set V₀) ⊆ MulAction.orbit O e := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hY y hy
    exact ⟨⟨t, ht⟩, rfl⟩
  have hor : Y.card ≤ Nat.card (MulAction.orbit O e) := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hpos : 0 < Nat.card O := Nat.card_pos
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, zero_mul] at hcard; omega
    · exact h
  have hYp : 0 < Y.card := by
    rcases Nat.eq_zero_or_pos Y.card with h | h
    · rw [h, mul_zero] at hcard; omega
    · exact h
  have hprod : Nat.card st * Nat.card (MulAction.orbit O e) = n * Y.card := by
    rw [← h2, h1, hcard]
  have hb : Nat.card (MulAction.orbit O e) = Y.card := by
    have : n * Nat.card (MulAction.orbit O e) ≤ n * Y.card := by
      rw [← hprod]
      exact Nat.mul_le_mul_right _ hst
    exact le_antisymm (Nat.le_of_mul_le_mul_left this hn) hor
  have ha : Nat.card st = n := by
    rw [hb] at hprod
    exact Nat.eq_of_mul_eq_mul_right hYp hprod
  have hbij : Function.Bijective f :=
    hfinj.bijective_of_nat_card_le (by rw [ha, Nat.card_eq_fintype_card, Fintype.card_fin])
  have hYeq : (Y : Set V₀) = MulAction.orbit O e := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, hb, Set.ncard_coe_finset]
  refine ⟨fun y hy hye => ?_, fun y hy => ?_⟩
  · have hmem : (⟨y, hy⟩ : O) ∈ st := by
      rw [MulAction.mem_stabilizer_iff]
      exact hye
    obtain ⟨k, hk⟩ := hbij.2 ⟨⟨y, hy⟩, hmem⟩
    refine ⟨k, k.2, ?_⟩
    have := congrArg (fun z : st => ((z : O) : V₀ ≃ₗ[ZMod 2] V₀)) hk
    exact this.symm
  · have : y e ∈ MulAction.orbit O e := ⟨⟨y, hy⟩, rfl⟩
    rw [← hYeq] at this
    exact this

structure SFacts (minus : Bool) (D : GrpData) (G : GK) (B : SBase) : Prop where
  rel : GRel D G
  stab : ∀ k < B.nS, actS (fS B.spk k) B.b = B.b ∧ InOS G (fS B.spk k) ∧
    (k + 1 < B.nS → fS B.spk k < fS B.spk (k + 1))
  tp : ∀ p ∈ B.sing, InOS G (B.tpT.getD p 0) ∧ actS (B.tpT.getD p 0) B.b = p ∧
    mulF (B.tpT.getD p 0) (B.tpI.getD p 0) = oneF
  fg : ∀ gs ∈ B.fg, ∀ x ∈ gs, InOS G x
  card : B.nS * B.sing.length = Nat.card (O₀ minus)
  nodup : B.sing.Nodup
  sing_lt : ∀ p ∈ B.sing, p < 64
  b_lt : B.b < 64

theorem inOS_of_mem_gensS {B : SBase} (hfg : ∀ gs ∈ B.fg, ∀ x ∈ gs, InOS G x) {g c : ℕ}
    (hc : c ∈ gensS B g) : InOS G c := by
  unfold gensS at hc
  by_cases hg : g < B.fg.length
  · rw [List.getD_eq_getElem _ _ hg] at hc
    exact hfg _ (List.getElem_mem hg) c hc
  · rw [List.getD_eq_default _ _ (by omega)] at hc
    exact absurd hc List.not_mem_nil

@[expose] noncomputable def subF (hD : GrpFacts minus D) (G : GK) (B : SBase) (g : ℕ) :
    Subgroup (V₀ ≃ₗ[ZMod 2] V₀) :=
  Subgroup.closure {x | ∃ c ∈ gensS B g, eltC hD G c = x}

theorem eltC_mem_subF {B : SBase} {g c : ℕ} (hc : c ∈ gensS B g) :
    eltC hD G c ∈ subF hD G B g :=
  Subgroup.subset_closure ⟨c, hc, rfl⟩

theorem wv_mem (hR : GRel D G) {B : SBase} (hfg : ∀ gs ∈ B.fg, ∀ x ∈ gs, InOS G x) {g : ℕ}
    {w : List ℕ} (hw : ∀ q ∈ w, q < (gensS B g).length) :
    ∃ x ∈ subF hD G B g,
      Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) (wvS (nthS 0 (gensS B g)) w oneF) := by
  have hL : ∀ q ∈ w, Code.HasCode (eltC hD G ((gensS B g).getD q 0) : V₀ →ₗ[ZMod 2] V₀)
      (nthS 0 (gensS B g) q) := by
    intro q hq
    rw [nthS_eq]
    exact (cd_eltC hD hR (inOS_of_mem_gensS hfg (getD_mem_of_lt (hw q hq) 0))).1
  have h := cd_wvS w hL cd_one
  rw [one_mul] at h
  refine ⟨_, list_prod_mem ?_, h⟩
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  exact eltC_mem_subF hD (getD_mem_of_lt (hw q hq) 0)

theorem cList_mem (S : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) (wv : List ℕ)
    (hwv : ∀ c ∈ wv, ∃ x ∈ S, Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c) :
    ∀ (cpar : List (ℕ × ℕ)) (C : List ℕ),
      (∀ c ∈ C, ∃ x ∈ S, Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c) →
      (∀ j (hj : j < cpar.length), cpar[j].1 < C.length + j ∧ cpar[j].2 < wv.length) →
      ∀ c ∈ cpar.foldl (fun C pq => C ++ [mulF (C.getD pq.1 0) (wv.getD pq.2 0)]) C,
        ∃ x ∈ S, Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c
  | [], _, hC, _ => hC
  | pq :: cpar, C, hC, hp => by
    rw [List.foldl_cons]
    have h0 := hp 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    obtain ⟨x, hx, hxc⟩ := hC _ (getD_mem_of_lt h0.1 0)
    obtain ⟨y, hy, hyc⟩ := hwv _ (getD_mem_of_lt h0.2 0)
    refine cList_mem S wv hwv cpar _ ?_ ?_
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hC c hc
      · rw [List.mem_singleton] at hc
        rw [hc]
        exact ⟨x * y, S.mul_mem hx hy, cd_mul hxc hyc⟩
    · intro j hj
      have := hp (j + 1) (by simpa using hj)
      simp only [List.getElem_cons_succ] at this
      simp only [List.length_append, List.length_singleton]
      omega

theorem mat_zero : Code.mat 0 = 0 := by
  ext i j
  simp [Code.mat, Code.bitZ]

theorem vec_zero' : Code.vec 0 = 0 := by
  funext i
  simp [Code.vec, Code.bitZ]

theorem not_cd_mulF_zero {y : V₀ ≃ₗ[ZMod 2] V₀} {u : ℕ}
    (h : Code.HasCode (y : V₀ →ₗ[ZMod 2] V₀) (mulF u 0)) : False := by
  have hm : Code.mat (mulF u 0) = 0 := by rw [mulF_eq, Code.mat_mul, mat_zero, mul_zero]
  have hz : (y : V₀ →ₗ[ZMod 2] V₀) = 0 :=
    LinearMap.toMatrix'.injective (by rw [h, hm, map_zero])
  have h1 : y (Code.vec 1) = y 0 := by
    rw [map_zero, ← LinearEquiv.coe_coe, hz, LinearMap.zero_apply]
  have h2 : Code.vec 1 = Code.vec 0 := by rw [vec_zero']; exact y.injective h1
  exact absurd (vec_injective_of_lt (by norm_num) (by norm_num) h2) (by norm_num)

theorem vec_foldr {gens : List ℕ} (hR : GRel D G) (hgens : ∀ c ∈ gens, InOS G c) (p : ℕ) :
    ∀ js : List ℕ, (∀ j ∈ js, j < gens.length) →
      Code.vec (js.foldr (fun j v => actS (gens.getD j 0) v) p) =
        (js.map fun j => eltC hD G (gens.getD j 0)).prod (Code.vec p)
  | [], _ => by
    rw [List.foldr_nil, List.map_nil, List.prod_nil]
    rfl
  | j :: js, hjs => by
    rw [List.foldr_cons, List.map_cons, List.prod_cons, LinearEquiv.mul_apply,
      ← vec_foldr hR hgens p js (fun j' hj' => hjs j' (List.mem_cons_of_mem _ hj')),
      cd_vec (cd_eltC hD hR (hgens _ (getD_mem_of_lt (hjs j List.mem_cons_self) 0))).1]

@[expose] noncomputable def vidx (v : V₀) : ℕ := Classical.choose (exists_vec v)

theorem vidx_vec {p : ℕ} (hp : p < 64) : vidx (Code.vec p) = p :=
  vec_injective_of_lt (Classical.choose_spec (exists_vec (Code.vec p))).1 hp
    (Classical.choose_spec (exists_vec (Code.vec p))).2

@[expose] noncomputable def tpE (hD : GrpFacts minus D) (G : GK) (B : SBase) (v : V₀) :
    V₀ ≃ₗ[ZMod 2] V₀ :=
  eltC hD G (B.tpT.getD (vidx v) 0)

theorem strict_lt {B : SBase} (hS : SFacts minus D G B) {i j : ℕ} (hij : i < j)
    (hj : j < B.nS) : fS B.spk i < fS B.spk j := by
  induction j with
  | zero => exact absurd hij (Nat.not_lt_zero _)
  | succ j ih =>
    have hstep := (hS.stab j (by omega)).2.2 hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · exact (ih h (by omega)).trans hstep
    · rw [h]
      exact hstep

theorem stab_eq {B : SBase} (hS : SFacts minus D G B) :
    (∀ y ∈ O₀ minus, y (Code.vec B.b) = Code.vec B.b →
      ∃ k < B.nS, y = eltC hD G (fS B.spk k)) ∧
    (∀ y ∈ O₀ minus, ∃ q ∈ B.sing, y (Code.vec B.b) = Code.vec q) := by
  classical
  have hsc := fun k (hk : k < B.nS) => cd_eltC hD hS.rel (hS.stab k hk).2.1
  have hnd : (B.sing.map Code.vec).Nodup :=
    List.Nodup.map_on (fun x hx y hy h => vec_injective_of_lt (hS.sing_lt x hx)
      (hS.sing_lt y hy) h) hS.nodup
  obtain ⟨h1, h2⟩ := stab_orbit (O := O₀ minus) (Code.vec B.b) B.nS
    (fun k => eltC hD G (fS B.spk k))
    (fun k hk => ⟨(hsc k hk).2.1, by rw [cd_vec (hsc k hk).1, (hS.stab k hk).1]⟩)
    (fun i hi j hj hij => by
      have e : fS B.spk i = fS B.spk j := Code.HasCode.code_eq (hsc i hi).1
        (by rw [hij]; exact (hsc j hj).1) (hsc i hi).2.2 (hsc j hj).2.2
      rcases lt_trichotomy i j with h | h | h
      · exact absurd e (strict_lt hS h hj).ne
      · exact h
      · exact absurd e (strict_lt hS h hi).ne')
    (B.sing.map Code.vec).toFinset
    (fun y hy => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
      have ht := hS.tp p hp
      exact ⟨_, (cd_eltC hD hS.rel ht.1).2.1, by rw [cd_vec (cd_eltC hD hS.rel ht.1).1, ht.2.1]⟩)
    (by rw [List.toFinset_card_of_nodup hnd, List.length_map]; exact hS.card)
  refine ⟨h1, fun y hy => ?_⟩
  obtain ⟨q, hq, e⟩ := List.mem_map.mp (List.mem_toFinset.mp (h2 y hy))
  exact ⟨q, hq, e.symm⟩

theorem exists_over {B : SBase} (hS : SFacts minus D G B) {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    {ci : ℕ} (hL : LFacts L (B.LG.getD ci []) (B.LC.getD ci [])) {g : ℕ} {ginv : List ℕ}
    {wg : List (List ℕ)} {cpar : List (ℕ × ℕ)} {T : List (ℕ × ℕ)} {reps : List ℕ}
    {recs : List (List (List ℕ × List (List ℕ)))}
    {cls : List ℕ × List (List ℕ) × List (List ℕ)}
    (hF : CheckFFacts B g ginv wg cpar T reps recs cls) (hci : B.fc.getD g 0 = ci)
    (H' : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) (hle : subF hD G B g ≤ H')
    (hgood : ∀ x ∈ H', GoodElt minus L (Code.vec B.b) x)
    (hh : ∃ h ∈ H', h ∉ subF hD G B g) :
    ∃ k', g < k' ∧ k' < B.nF ∧ B.fc.getD k' 0 = ci ∧
      ∃ n ∈ censusN minus L (Code.vec B.b), ∀ x ∈ subF hD G B k', n * x * n⁻¹ ∈ H' := by
  classical
  obtain ⟨hstab, horbit⟩ := stab_eq hD hS
  have hR := hS.rel
  have hgens : ∀ c ∈ gensS B g, InOS G c := fun c hc => inOS_of_mem_gensS hS.fg hc
  have hsc := fun k (hk : k < B.nS) => cd_eltC hD hR (hS.stab k hk).2.1
  have hwv : ∀ c ∈ wg.map (fun w => wvS (nthS 0 (gensS B g)) w oneF),
      ∃ x ∈ subF hD G B g, Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c := by
    intro c hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
    exact wv_mem hD hR hS.fg (fun q hq => hF.cover.letters w hw q hq)
  have hC : ∀ c ∈ cListS (wg.map fun w => wvS (nthS 0 (gensS B g)) w oneF) cpar,
      ∃ x ∈ subF hD G B g, Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c := by
    refine cList_mem _ _ hwv cpar [oneF] ?_ ?_
    · intro c hc
      rw [List.mem_singleton] at hc
      rw [hc]
      exact ⟨1, Subgroup.one_mem _, cd_one⟩
    · intro j hj
      have := hF.cover.par j hj
      rw [List.length_map, List.length_singleton]
      omega
  have hcov : ∀ y ∈ O₀ minus, y • Code.vec B.b = Code.vec B.b →
      ∃ u ∈ {u | ∃ t ∈ T, eltC hD G (fS B.spk t.1) = u}, ∃ c ∈ subF hD G B g, y = u * c := by
    intro y hy hye
    rw [LinearEquiv.smul_def] at hye
    obtain ⟨ρ, hρ, hyρ⟩ := hstab y hy hye
    obtain ⟨t, ht, k, hk⟩ := hF.cover.cover ρ hρ
    have ht1 := (hF.cover.tr t ht).1
    have h1 : Code.HasCode (y : V₀ →ₗ[ZMod 2] V₀) (fS B.spk ρ) := by
      rw [hyρ]
      exact (hsc ρ hρ).1
    rw [hk] at h1
    by_cases hkl : k < (cListS (wg.map fun w => wvS (nthS 0 (gensS B g)) w oneF) cpar).length
    · obtain ⟨x, hx, hxc⟩ := hC _ (getD_mem_of_lt hkl 0)
      exact ⟨_, ⟨t, ht, rfl⟩, x, hx, Code.HasCode.eq_of_equiv h1 (cd_mul (hsc t.1 ht1).1 hxc)⟩
    · rw [List.getD_eq_default _ _ (by omega)] at h1
      exact (not_cd_mulF_zero h1).elim
  have horb : ∀ q ∈ {v | ∃ q ∈ B.sing, Code.vec q = v},
      ∃ p ∈ {v | ∃ p ∈ reps, Code.vec p = v}, ∃ f ∈ subF hD G B g, q = f • p := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨p, hp, js, hjs, hqe⟩ := hF.orbChain q hq
    refine ⟨_, ⟨p, hp, rfl⟩, (js.map fun j => eltC hD G ((gensS B g).getD j 0)).prod,
      list_prod_mem ?_, ?_⟩
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact eltC_mem_subF hD (getD_mem_of_lt (hjs j hj) 0)
    · rw [LinearEquiv.smul_def, hqe]
      exact vec_foldr hD hR hgens p js hjs
  have hY : ∀ h ∈ O₀ minus, h • Code.vec B.b ∈ {v | ∃ q ∈ B.sing, Code.vec q = v} := by
    intro h hh
    obtain ⟨q, hq, e⟩ := horbit h hh
    exact ⟨q, hq, e.symm⟩
  have htp : ∀ p ∈ {v | ∃ p ∈ reps, Code.vec p = v}, tpE hD G B p ∈ O₀ minus ∧
      tpE hD G B p • Code.vec B.b = p := by
    rintro _ ⟨p, hp, rfl⟩
    have hps := hF.repsSing p hp
    have ht := hS.tp p hps
    have hc := cd_eltC hD hR ht.1
    unfold tpE
    rw [vidx_vec (hS.sing_lt p hps), LinearEquiv.smul_def, cd_vec hc.1, ht.2.1]
    exact ⟨hc.2.1, rfl⟩
  obtain ⟨h, hh1, hh2⟩ := hh
  have hH'O : H' ≤ O₀ minus := fun x hx => (hgood x hx).1
  obtain ⟨_, ⟨p, hp, rfl⟩, _, ⟨t, ht, rfl⟩, hrH, hrF⟩ :=
    exists_rep_of_cover hle hH'O (Code.vec B.b) _ _ (tpE hD G B) _ hY horb htp hcov hh1 hh2
  have hps := hF.repsSing p hp
  have htpp := hS.tp p hps
  have hcp := cd_eltC hD hR htpp.1
  have ht1 := hF.cover.tr t ht
  unfold tpE at hrH hrF
  rw [vidx_vec (hS.sing_lt p hps)] at hrH hrF
  obtain ⟨rs, -, hrsOK⟩ := forall₂_mem_left hF.recsOK p hp
  obtain ⟨e, -, hrec⟩ := forall₂_mem_left hrsOK t ht
  have hcand : candS B g = ci := hci
  have hlg : lgS B g = B.LG.getD ci [] := by unfold lgS; rw [hcand]
  have hlc : lcS B g = B.LC.getD ci [] := by unfold lcS; rw [hcand]
  rw [hcand, hlg, hlc] at hrec
  set R := eltC hD G (B.tpT.getD p 0) * eltC hD G (fS B.spk t.1) with hRdef
  have hRc : Code.HasCode (R : V₀ →ₗ[ZMod 2] V₀)
      (mulF (B.tpT.getD p 0) (fS B.spk t.1)) := cd_mul hcp.1 (hsc t.1 ht1.1).1
  have hRi : Code.HasCode ((R⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
      (mulF (fS B.spk t.2) (B.tpI.getD p 0)) := by
    rw [hRdef, mul_inv_rev]
    exact cd_mul (cd_inv (hsc t.1 ht1.1).1 ht1.2.2) (cd_inv hcp.1 htpp.2.2)
  let Lx : ℕ → V₀ ≃ₗ[ZMod 2] V₀ := fun q =>
    if q < (gensS B g).length then eltC hD G ((gensS B g).getD q 0) else R
  have hLx : ∀ q, Code.HasCode (Lx q : V₀ →ₗ[ZMod 2] V₀)
      (letS (gensS B g) (gensS B g).length (mulF (B.tpT.getD p 0) (fS B.spk t.1)) q) := by
    intro q
    rw [letS_eq]
    by_cases hq : q < (gensS B g).length
    · simp only [Lx, if_pos hq]
      exact (cd_eltC hD hR (hgens _ (getD_mem_of_lt hq 0))).1
    · simp only [Lx, if_neg hq]
      exact hRc
  have hLxi : ∀ q, Code.HasCode (((Lx q)⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
      (letS ginv (gensS B g).length (mulF (fS B.spk t.2) (B.tpI.getD p 0)) q) := by
    intro q
    rw [letS_eq]
    by_cases hq : q < (gensS B g).length
    · simp only [Lx, if_pos hq]
      exact cd_inv (cd_eltC hD hR (hgens _ (getD_mem_of_lt hq 0))).1
        (forall₂_getD 0 0 hF.inv q hq)
    · simp only [Lx, if_neg hq]
      exact hRi
  have hLxH : ∀ q, Lx q ∈ H' := by
    intro q
    by_cases hq : q < (gensS B g).length
    · simp only [Lx, if_pos hq]
      exact hle (eltC_mem_subF hD (getD_mem_of_lt hq 0))
    · simp only [Lx, if_neg hq]
      exact hrH
  have hword : ∀ w : List ℕ, (w.map Lx).prod ∈ H' ∧
      Code.HasCode (((w.map Lx).prod : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
        (wvS (letS (gensS B g) (gensS B g).length (mulF (B.tpT.getD p 0) (fS B.spk t.1))) w
          oneF) := by
    intro w
    refine ⟨list_prod_mem fun x hx => ?_, ?_⟩
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
      exact hLxH q
    · have h := cd_wvS w (fun q _ => hLx q) cd_one
      rw [one_mul] at h
      exact h
  rcases hrec with ⟨-, -, hbad⟩ | ⟨-, hgk, hknF, hfck, hρ, hρ', hmul, hnor, hws⟩ | ⟨-, hr1⟩
  ·
    exfalso
    have hXi : Code.HasCode
        ((((e.2.getD 0 []).map Lx).prod⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
        (wiS (letS ginv (gensS B g).length (mulF (fS B.spk t.2) (B.tpI.getD p 0)))
          (e.2.getD 0 []) oneF) := by
      rw [prod_inv_eq]
      have h := cd_wiS (Lx := fun q => (Lx q)⁻¹) (e.2.getD 0 []) (fun q _ => hLxi q) cd_one
      rw [mul_one] at h
      exact h
    exact not_goodElt_of_badS hL hS.b_lt (hword _).2 hXi hbad (hgood _ (hword _).1)
  ·
    have hnc := (hsc _ hρ).1
    have hni : Code.HasCode (((eltC hD G (fS B.spk (e.1.getD 2 0)))⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) :
        V₀ →ₗ[ZMod 2] V₀) (fS B.spk (e.1.getD 3 0)) := cd_inv hnc hmul
    have hn : eltC hD G (fS B.spk (e.1.getD 2 0)) ∈ censusN minus L (Code.vec B.b) :=
      mem_censusN.mpr ⟨(hsc _ hρ).2.1, (fix_iff hnc hS.b_lt).mp (hS.stab _ hρ).1,
        (norS_iff_mem hL hnc hni).mp hnor⟩
    refine ⟨_, hgk, hknF, hfck, _, hn, fun x hx => ?_⟩
    have hcl : subF hD G B (e.1.getD 1 0) ≤
        H'.comap (MulAut.conj (eltC hD G (fS B.spk (e.1.getD 2 0)))).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨c, hc, rfl⟩
      obtain ⟨w, -, hwx⟩ := forall₂_mem_right hws c hc
      have hcc := cd_eltC hD hR (inOS_of_mem_gensS hS.fg hc)
      have h1 := cd_mul (cd_mul hnc hcc.1) hni
      rw [← hwx.2] at h1
      change _ * _ * _⁻¹ ∈ H'
      rw [Code.HasCode.eq_of_equiv h1 (hword w).2]
      exact (hword w).1
    exact hcl hx
  ·
    exfalso
    rw [hr1] at hRc
    exact hrF (by rw [Code.HasCode.eq_of_equiv hRc cd_one]; exact Subgroup.one_mem _)

theorem exists_conj_subF {B : SBase} (hS : SFacts minus D G B)
    {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {ci : ℕ}
    (hL : LFacts L (B.LG.getD ci []) (B.LC.getD ci []))
    (hfirst : ∃ g < B.nF, B.fc.getD g 0 = ci ∧ ∀ x ∈ B.fg.getD g [], x ∈ B.LC.getD ci [])
    (hF : ∀ g < B.nF, ∃ ginv wg cpar T reps recs cls,
      CheckFFacts B g ginv wg cpar T reps recs cls)
    {H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} (hHO : H ≤ O₀ minus)
    (hC : CensusCond minus H L (Code.vec B.b)) :
    ∃ k < B.nF, B.fc.getD k 0 = ci ∧ ∃ n ∈ censusN minus L (Code.vec B.b),
      ∀ x, x ∈ H ↔ n⁻¹ * x * n ∈ subF hD G B k := by
  refine maximality_by_index H (censusN minus L (Code.vec B.b)) (GoodElt minus L (Code.vec B.b))
    (subF hD G B) (fun k => B.fc.getD k 0 = ci) B.nF
    (fun _ hh => goodElt_of_censusCond hHO hC hh) (fun _ hn _ hx => goodElt_conj hn hx) ?_ ?_
  · obtain ⟨g, hg, hgc, hgL⟩ := hfirst
    refine ⟨g, hg, hgc, 1, Subgroup.one_mem _, fun x hx => ?_⟩
    rw [one_mul, inv_one, mul_one]
    have hle : subF hD G B g ≤ L := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨c, hc, rfl⟩
      exact (hL.mem _).mpr ⟨c, hgL c hc, (cd_eltC hD hS.rel (inOS_of_mem_gensS hS.fg hc)).1⟩
    exact hC.1 (hle hx)
  · intro k hk hA H' hle hgood hh
    obtain ⟨ginv, wg, cpar, T, reps, recs, cls, hFk⟩ := hF k hk
    exact exists_over hD hS hL hFk hA H' hle hgood hh

theorem subProds_mem (K : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) :
    ∀ (lg W : List ℕ), (∀ c ∈ lg, ∃ y ∈ K, Code.HasCode (y : V₀ →ₗ[ZMod 2] V₀) c) →
      (∀ w ∈ W, ∃ y ∈ K, Code.HasCode (y : V₀ →ₗ[ZMod 2] V₀) w) →
      ∀ w ∈ List.rec (motive := fun _ => List ℕ → List ℕ) (fun W => W)
        (fun x _ ih W => ih (List.append W (List.map (fun w => mulF w x) W))) lg W,
        ∃ y ∈ K, Code.HasCode (y : V₀ →ₗ[ZMod 2] V₀) w
  | [], _, _, hW => hW
  | x :: lg, W, hlg, hW => by
    refine subProds_mem K lg _ (fun c hc => hlg c (List.mem_cons_of_mem _ hc)) ?_
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hW w hw
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
      obtain ⟨y, hy, hyc⟩ := hW w' hw'
      obtain ⟨z, hz, hzc⟩ := hlg x List.mem_cons_self
      exact ⟨y * z, K.mul_mem hy hz, cd_mul hyc hzc⟩

theorem lt_of_mem_llist {minus : Bool} (hb : censusBase minus () = true) {A : Array ℕ}
    (hA : A ∈ (ldata minus ()).Llist) {i : ℕ} (hi : i ∈ A) :
    i < (grpData minus ()).O.size := by
  unfold censusBase censusBaseOf at hb
  simp only [Bool.and_eq_true, Array.all_eq_true'] at hb
  have h := hb.2.2.1.1.1.2 A hA
  unfold lOK at h
  simp only [Bool.and_eq_true, Array.all_eq_true', decide_eq_true_eq] at h
  exact (h.1.1.2 i hi).1.1

theorem lFacts_of {minus : Bool} (hb : censusBase minus () = true) {G : GK}
    (hR : GRel (grpData minus ()) G) {cs : List ℕ} {B : SBase}
    (hcand : List.Forall₂ (fun c p => (∀ x ∈ p.1, x ∈ p.2) ∧ (∀ x ∈ p.2, x ∈ subProds p.1) ∧
      List.Forall₂ (fun x i => x = G.getO i) p.2 ((ldata minus ()).Llist[c]!).toList) cs
      (B.LG.zip B.LC))
    (hLG : B.LG.length = B.LC.length) {ci : ℕ} (hci : ci < cs.length)
    {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (hL : ∀ x, x ∈ L ↔ InCodeList minus ((ldata minus ()).Llist[cs.getD ci 0]!) x) :
    LFacts L (B.LG.getD ci []) (B.LC.getD ci []) := by
  have hD := grpFacts_of_censusBase hb
  have hlen := hcand.length_eq
  have hzl : ci < (B.LG.zip B.LC).length := by rw [← hlen]; exact hci
  have hz : (B.LG.zip B.LC).getD ci ([], []) = (B.LG.getD ci [], B.LC.getD ci []) := by
    rw [List.length_zip] at hzl
    rw [List.getD_eq_getElem _ _ (by rw [List.length_zip]; exact hzl), List.getElem_zip,
      List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  have hc := forall₂_getD 0 ([], []) hcand ci hci
  rw [hz] at hc
  obtain ⟨hsub, hprod, hcodes⟩ := hc
  have hAmem : (ldata minus ()).Llist[cs.getD ci 0]! ∈ (ldata minus ()).Llist ∨
      (ldata minus ()).Llist[cs.getD ci 0]! = #[] := by
    by_cases h : cs.getD ci 0 < (ldata minus ()).Llist.size
    · left
      rw [getElem!_pos (ldata minus ()).Llist (cs.getD ci 0) h]
      exact Array.getElem_mem h
    · right
      rw [getElem!_neg (ldata minus ()).Llist (cs.getD ci 0) h]
      rfl
  have hilt : ∀ i ∈ ((ldata minus ()).Llist[cs.getD ci 0]!).toList,
      i < (grpData minus ()).O.size := by
    intro i hi
    rcases hAmem with hA | hA
    · exact lt_of_mem_llist hb hA (Array.mem_toList_iff.mp hi)
    · rw [hA] at hi
      exact absurd hi List.not_mem_nil
  have hmem : ∀ x, x ∈ L ↔ ∃ c ∈ B.LC.getD ci [], Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c := by
    intro x
    rw [hL x]
    constructor
    · rintro ⟨i, hi, -, hxc⟩
      obtain ⟨c, hc, hci'⟩ := forall₂_mem_right hcodes i (Array.mem_toList_iff.mpr hi)
      rw [hR.get i, ← hci'] at hxc
      exact ⟨c, hc, hxc⟩
    · rintro ⟨c, hc, hxc⟩
      obtain ⟨i, hi, hci'⟩ := forall₂_mem_left hcodes c hc
      refine ⟨i, Array.mem_toList_iff.mp hi, hilt i hi, ?_⟩
      rw [hR.get i, ← hci']
      exact hxc
  have hlt : ∀ c ∈ B.LC.getD ci [], c < 2 ^ 36 := by
    intro c hc
    obtain ⟨i, hi, hci'⟩ := forall₂_mem_left hcodes c hc
    rw [hci', ← hR.get i]
    exact hD.code_lt (hilt i hi)
  have hgen : ∀ c ∈ B.LG.getD ci [], ∃ x ∈ L, Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c := by
    intro c hc
    obtain ⟨i, hi, hci'⟩ := forall₂_mem_left hcodes c (hsub c hc)
    have hil := hilt i hi
    have hcd : Code.HasCode (hD.elt i : V₀ →ₗ[ZMod 2] V₀) c := by
      rw [hci', ← hR.get i]
      exact hD.hasCode_elt hil
    exact ⟨hD.elt i, (hmem _).mpr ⟨c, hsub c hc, hcd⟩, hcd⟩
  refine ⟨hmem, hlt, fun x hx => ?_, hgen⟩
  obtain ⟨c, hc, hxc⟩ := (hmem x).mp hx
  obtain ⟨y, hy, hyc⟩ := subProds_mem (Subgroup.closure
      {x : V₀ ≃ₗ[ZMod 2] V₀ | ∃ c ∈ B.LG.getD ci [], Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c})
    (B.LG.getD ci []) [oneF]
    (fun c hc => by
      obtain ⟨x, -, hxc⟩ := hgen c hc
      exact ⟨x, Subgroup.subset_closure ⟨c, hc, hxc⟩, hxc⟩)
    (by
      intro w hw
      rw [List.mem_singleton] at hw
      rw [hw]
      exact ⟨1, Subgroup.one_mem _, cd_one⟩) c (hprod c hc)
  rw [Code.HasCode.eq_of_equiv hxc hyc]
  exact hy

end CFSG.KC.C690S

end
