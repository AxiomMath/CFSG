module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H611A

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem alpha_mem_Zg {α : G} (hα : AlphaSpec S z t α) :
    α ∈ (zpowers α ⊔ zpowers t : Subgroup G) := (h.mem_Zg hα).2 (Or.inr (Or.inr (Or.inl rfl)))

theorem t_mem_Zg {α : G} (hα : AlphaSpec S z t α) :
    t ∈ (zpowers α ⊔ zpowers t : Subgroup G) := (h.mem_Zg hα).2 (Or.inr (Or.inl rfl))

theorem cmt_inv_left {α : G} (hα : AlphaSpec S z t α) {q r : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hr : r ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    q⁻¹ * r * q⁻¹⁻¹ * r⁻¹ = (q * r * q⁻¹ * r⁻¹)⁻¹ := by
  have := h.cmt_mul_left hα hq (inv_mem hq) hr
  have h2 : (q * r * q⁻¹ * r⁻¹) * (q⁻¹ * r * q⁻¹⁻¹ * r⁻¹) = 1 := by
    rw [← this]
    group
  exact eq_inv_of_mul_eq_one_right h2

@[expose] noncomputable def Wsub {α : G} (hα : AlphaSpec S z t α) (A : Subgroup G) :
    Subgroup G where
  carrier := {q | q ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ∧
    ∀ e ∈ E, q * e * q⁻¹ * e⁻¹ ∈ A}
  mul_mem' := by
    rintro q q' ⟨hq, hqe⟩ ⟨hq', hq'e⟩
    refine ⟨mul_mem hq hq', fun e he => ?_⟩
    rw [h.cmt_mul_left hα hq hq' (h.E_le_Qs hα he)]
    exact mul_mem (hqe e he) (hq'e e he)
  one_mem' := ⟨one_mem _, fun e he => by simp⟩
  inv_mem' := by
    rintro q ⟨hq, hqe⟩
    refine ⟨inv_mem hq, fun e he => ?_⟩
    rw [h.cmt_inv_left hα hq (h.E_le_Qs hα he)]
    exact A.inv_mem (hqe e he)

structure ZInv {α : G} (_hα : AlphaSpec S z t α) (ζ₀ : G) : Prop where
  mem : ζ₀ ∈ (zpowers α ⊔ zpowers t : Subgroup G)
  sq : ζ₀ * ζ₀ = 1
  ne : ζ₀ ≠ 1

@[expose] def IsLift {α : G} (hα : AlphaSpec S z t α) (ζ₀ x w : G) : Prop :=
  w ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ∧
    ∀ e ∈ E, w * e * w⁻¹ * e⁻¹ = iota ζ₀ (x * e * x⁻¹ * e⁻¹)

theorem isLift_mul {α : G} (hα : AlphaSpec S z t α) {ζ₀ x x' w w' : G} (hζ : ζ₀ * ζ₀ = 1)
    (hx : x ∈ E) (hx' : x' ∈ E) (hw : IsLift h hα ζ₀ x w) (hw' : IsLift h hα ζ₀ x' w') :
    IsLift h hα ζ₀ (x * x') (w * w') := by
  refine ⟨mul_mem hw.1 hw'.1, fun e he => ?_⟩
  rw [h.cmt_mul_left hα hw.1 hw'.1 (h.E_le_Qs hα he), hw.2 e he, hw'.2 e he,
    h.cmt_mul_left hα (h.E_le_Qs hα hx) (h.E_le_Qs hα hx') (h.E_le_Qs hα he),
    iota_mul hζ h.t_ne h.t_sq (h.oe.econfig.comm x hx e he) (h.oe.econfig.comm x' hx' e he)]

theorem isLift_inv {α : G} (hα : AlphaSpec S z t α) {ζ₀ x w : G} (hζ : ζ₀ * ζ₀ = 1)
    (hx : x ∈ E) (hw : IsLift h hα ζ₀ x w) : IsLift h hα ζ₀ x⁻¹ w⁻¹ := by
  refine ⟨inv_mem hw.1, fun e he => ?_⟩
  rw [h.cmt_inv_left hα hw.1 (h.E_le_Qs hα he), h.cmt_inv_left hα (h.E_le_Qs hα hx)
    (h.E_le_Qs hα he), hw.2 e he]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  rcases h.oe.econfig.comm x hx e he with h1 | h1
  · rw [h1]; simp [iota_one]
  · rw [h1, hti, iota_of_ne h.t_ne]
    exact inv_eq_of_mul_eq_one_right hζ

theorem isLift_unique {α : G} (hα : AlphaSpec S z t α) {ζ₀ x w w' : G}
    (hw : IsLift h hα ζ₀ x w) (hw' : IsLift h hα ζ₀ x w') :
    w⁻¹ * w' ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
  have hu : w⁻¹ * w' ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := mul_mem (inv_mem hw.1) hw'.1
  have hcomm : ∀ e ∈ E, (w⁻¹ * w') * e = e * (w⁻¹ * w') := by
    intro e he
    apply cmt_eq_one_iff.1
    rw [h.cmt_mul_left hα (inv_mem hw.1) hw'.1 (h.E_le_Qs hα he),
      h.cmt_inv_left hα hw.1 (h.E_le_Qs hα he), hw.2 e he, hw'.2 e he, inv_mul_cancel]
  exact (h.mem_Zg hα).2 (h.QF_cent_E hα hu hcomm)

theorem isLift_of_mem_Zg {α : G} (hα : AlphaSpec S z t α) (ζ₀ : G) {a : G}
    (ha : a ∈ (zpowers α ⊔ zpowers t : Subgroup G)) : IsLift h hα ζ₀ 1 a := by
  refine ⟨(h.Zg_cent_Q hα ha).1, fun e he => ?_⟩
  rw [cmt_eq_one_iff.2 (h.Zg_comm_E hα ha he)]
  simp [iota_one]

theorem mem_Zg_of_isLift_one {α : G} (hα : AlphaSpec S z t α) {ζ₀ w : G}
    (hw : IsLift h hα ζ₀ 1 w) : w ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
  have hcomm : ∀ e ∈ E, w * e = e * w := by
    intro e he
    apply cmt_eq_one_iff.1
    rw [hw.2 e he]
    simp [iota_one]
  exact (h.mem_Zg hα).2 (h.QF_cent_E hα hw.1 hcomm)

theorem isLift_conj_W {α : G} (hα : AlphaSpec S z t α) {ζ₀ b x w : G}
    (hb : b ∈ L ⊓ centralizer ({t} : Set G)) (hx : x ∈ E) (hw : IsLift h hα ζ₀ x w) :
    IsLift h hα ζ₀ (b * x * b⁻¹) (b * w * b⁻¹) := by
  refine ⟨h.W_norm_Qs hα hb hw.1, fun e he => ?_⟩
  have he' : b⁻¹ * e * b ∈ E := by
    have := h.W_norm_E (inv_mem hb) he
    simpa using this
  rw [h.chi_conj_W hα hb hw.1 he, hw.2 _ he']
  congr 1
  have hcm : x * (b⁻¹ * e * b) * x⁻¹ * (b⁻¹ * e * b)⁻¹ = 1 ∨
      x * (b⁻¹ * e * b) * x⁻¹ * (b⁻¹ * e * b)⁻¹ = t := h.oe.econfig.comm x hx _ he'
  have hbt : b * t = t * b := mem_centralizer_singleton_iff.1 hb.2
  have hconj : b * x * b⁻¹ * e * (b * x * b⁻¹)⁻¹ * e⁻¹ =
      b * (x * (b⁻¹ * e * b) * x⁻¹ * (b⁻¹ * e * b)⁻¹) * b⁻¹ := by group
  rw [hconj]
  rcases hcm with h1 | h1
  · rw [h1]; simp
  · rw [h1, hbt]; group

theorem isLift_mem_Wsub {α : G} (hα : AlphaSpec S z t α) {ζ₀ x w : G} {A : Subgroup G}
    (hA : ζ₀ ∈ A) (hw : IsLift h hα ζ₀ x w) : w ∈ Wsub h hα A := by
  refine ⟨hw.1, fun e he => ?_⟩
  rw [hw.2 e he]
  rcases iota_mem ζ₀ (x * e * x⁻¹ * e⁻¹) with h1 | h1
  · rw [h1]; exact one_mem _
  · rw [h1]; exact hA

theorem exists_isLift (hM : OuterMFacts E S z t) {α : G} (hα : AlphaSpec S z t α) {ζ₀ : G}
    (hζ₀ : ZInv hα ζ₀) {a b c d : G}
    (hE : Subgroup.closure ({a, b, c, d} : Set G) = E) (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E)
    (hd : d ∈ E) {x : G} (hx : x ∈ E) : ∃ w, IsLift h hα ζ₀ x w := by
  have hZ : ∀ g : G, iota ζ₀ g ∈ (zpowers α ⊔ zpowers t : Subgroup G) := fun g => by
    rcases iota_mem ζ₀ g with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact hζ₀.mem
  obtain ⟨w, hw, h1, h2, h3, h4⟩ := h.Phi4_surj hM hα hE ha hb hc hd
    (iota ζ₀ (x * a * x⁻¹ * a⁻¹)) (iota ζ₀ (x * b * x⁻¹ * b⁻¹)) (iota ζ₀ (x * c * x⁻¹ * c⁻¹))
    (iota ζ₀ (x * d * x⁻¹ * d⁻¹)) (hZ _) (hZ _) (hZ _) (hZ _)
  refine ⟨w, hw, ?_⟩
  refine eq_on_closure (s := ({a, b, c, d} : Set G)) hE (f := fun e => w * e * w⁻¹ * e⁻¹)
    (f' := fun e => iota ζ₀ (x * e * x⁻¹ * e⁻¹)) ?_ ?_ ?_
  · intro e he e' he'
    exact h.cmt_mul_right hα hw (h.E_le_Qs hα he) (h.E_le_Qs hα he')
  · intro e he e' he'
    show iota ζ₀ (x * (e * e') * x⁻¹ * (e * e')⁻¹) = _
    rw [h.cmt_mul_right hα (h.E_le_Qs hα hx) (h.E_le_Qs hα he) (h.E_le_Qs hα he')]
    exact iota_mul hζ₀.sq h.t_ne h.t_sq (h.oe.econfig.comm x hx e he)
      (h.oe.econfig.comm x hx e' he')
  · intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4]

@[expose] noncomputable def thetaHom {α : G} (hα : AlphaSpec S z t α) {ζ₀ : G}
    (hζ₀ : ZInv hα ζ₀) {g : G} (hg : g ∈ E) : ↥E →* ↥(zpowers ζ₀) where
  toFun x := ⟨iota ζ₀ ((x : G) * g * (x : G)⁻¹ * g⁻¹), by
    rcases iota_mem ζ₀ ((x : G) * g * (x : G)⁻¹ * g⁻¹) with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact mem_zpowers ζ₀⟩
  map_one' := Subtype.ext (by simp [iota_one])
  map_mul' x y := Subtype.ext (by
    show iota ζ₀ (((x * y : ↥E) : G) * g * ((x * y : ↥E) : G)⁻¹ * g⁻¹) = _
    rw [show ((x * y : ↥E) : G) = (x : G) * (y : G) from rfl,
      h.cmt_mul_left hα (h.E_le_Qs hα x.2) (h.E_le_Qs hα y.2) (h.E_le_Qs hα hg)]
    exact iota_mul hζ₀.sq h.t_ne h.t_sq (h.oe.econfig.comm x x.2 g hg)
      (h.oe.econfig.comm y y.2 g hg))

@[expose] noncomputable def Theta4 {α : G} (hα : AlphaSpec S z t α) {ζ₀ : G}
    (hζ₀ : ZInv hα ζ₀) {a b c d : G} (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E) (hd : d ∈ E) :
    ↥E →* ↥(zpowers ζ₀) × ↥(zpowers ζ₀) × ↥(zpowers ζ₀) × ↥(zpowers ζ₀) :=
  (h.thetaHom hα hζ₀ ha).prod ((h.thetaHom hα hζ₀ hb).prod ((h.thetaHom hα hζ₀ hc).prod
    (h.thetaHom hα hζ₀ hd)))

omit [Finite G] h in
theorem card_zpowers_ZInv {α : G} {hα : AlphaSpec S z t α} {ζ₀ : G} (hζ₀ : ZInv hα ζ₀) :
    Nat.card (zpowers ζ₀) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hζ₀.sq) hζ₀.ne]

theorem Theta4_surj {α : G} (hα : AlphaSpec S z t α) {ζ₀ : G} (hζ₀ : ZInv hα ζ₀) {a b c d : G}
    (hE : Subgroup.closure ({a, b, c, d} : Set G) = E) (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E)
    (hd : d ∈ E) : Function.Surjective (h.Theta4 hα hζ₀ ha hb hc hd) := by
  set f := h.Theta4 hα hζ₀ ha hb hc hd with hf
  have hfx : ∀ x : ↥E, f x =
      (⟨iota ζ₀ ((x : G) * a * (x : G)⁻¹ * a⁻¹), (h.thetaHom hα hζ₀ ha x).2⟩,
        ⟨iota ζ₀ ((x : G) * b * (x : G)⁻¹ * b⁻¹), (h.thetaHom hα hζ₀ hb x).2⟩,
        ⟨iota ζ₀ ((x : G) * c * (x : G)⁻¹ * c⁻¹), (h.thetaHom hα hζ₀ hc x).2⟩,
        ⟨iota ζ₀ ((x : G) * d * (x : G)⁻¹ * d⁻¹), (h.thetaHom hα hζ₀ hd x).2⟩) :=
    fun x => rfl
  have htE : zpowers t ≤ E := zpowers_le.2 h.t_mem_E
  have hker : f.ker = (zpowers t).subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hfx]
    constructor
    · intro h0
      have h1 := congrArg (fun p => ((p.1 : ↥(zpowers ζ₀)) : G)) h0
      have h2 := congrArg (fun p => ((p.2.1 : ↥(zpowers ζ₀)) : G)) h0
      have h3 := congrArg (fun p => ((p.2.2.1 : ↥(zpowers ζ₀)) : G)) h0
      have h4 := congrArg (fun p => ((p.2.2.2 : ↥(zpowers ζ₀)) : G)) h0
      simp only [Prod.fst_one, Prod.snd_one, Subgroup.coe_one] at h1 h2 h3 h4
      rw [iota_eq_one_iff hζ₀.ne] at h1 h2 h3 h4
      have hcl : Subgroup.closure ({a, b, c, d} : Set G) ≤ centralizer ({(x : G)} : Set G) := by
        rw [Subgroup.closure_le]
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        rcases hg with rfl | rfl | rfl | rfl
        · exact (cmt_eq_one_iff.1 h1).symm
        · exact (cmt_eq_one_iff.1 h2).symm
        · exact (cmt_eq_one_iff.1 h3).symm
        · exact (cmt_eq_one_iff.1 h4).symm
      have hcent : ∀ e ∈ E, e * (x : G) = (x : G) * e := by
        intro e he
        rw [← hE] at he
        have := hcl he
        rwa [mem_centralizer_singleton_iff] at this
      have hx1 := h.oe.econfig.center x x.2 (fun e he => hcent e he)
      rcases hx1 with h5 | h5
      · rw [h5]; exact one_mem _
      · rw [h5]; exact mem_zpowers t
    · intro hxt
      rcases mem_zpowers_sq_eq_one h.t_sq hxt with h5 | h5
      · have hc' : ∀ e ∈ E, (x : G) * e * (x : G)⁻¹ * e⁻¹ = 1 := fun e he => by
          rw [h5]; simp
        refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_)
          (Subtype.ext ?_)))
        · simp [hc' a ha, iota_one]
        · simp [hc' b hb, iota_one]
        · simp [hc' c hc, iota_one]
        · simp [hc' d hd, iota_one]
      · have hc' : ∀ e ∈ E, (x : G) * e * (x : G)⁻¹ * e⁻¹ = 1 := fun e he =>
          cmt_eq_one_iff.2 (by rw [h5]; exact h.t_comm_E e he |>.symm)
        refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_)
          (Subtype.ext ?_)))
        · simp [hc' a ha, iota_one]
        · simp [hc' b hb, iota_one]
        · simp [hc' c hc, iota_one]
        · simp [hc' d hd, iota_one]
  have hcardker : Nat.card f.ker = 2 := by
    rw [hker]
    have h2 : Nat.card (zpowers t) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [Nat.card_zpowers, h.oe.cfg.t_order']
    rw [← h2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe htE).toEquiv
  have hidx := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hcardker, h.wf.card_E] at hidx
  have hrange : Nat.card f.range = 16 := by omega
  have htarget : Nat.card (↥(zpowers ζ₀) × ↥(zpowers ζ₀) × ↥(zpowers ζ₀) × ↥(zpowers ζ₀)) = 16 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, card_zpowers_ZInv hζ₀]
  have htop : f.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, htarget])
  exact MonoidHom.range_eq_top.1 htop

theorem exists_isLift_of_mem_Wsub {α : G} (hα : AlphaSpec S z t α) {ζ₀ : G} (hζ₀ : ZInv hα ζ₀)
    {a b c d : G} (hE : Subgroup.closure ({a, b, c, d} : Set G) = E) (ha : a ∈ E) (hb : b ∈ E)
    (hc : c ∈ E) (hd : d ∈ E) {w : G} (hw : w ∈ Wsub h hα (zpowers ζ₀)) :
    ∃ x ∈ E, IsLift h hα ζ₀ x w := by
  obtain ⟨x, hx⟩ := h.Theta4_surj hα hζ₀ hE ha hb hc hd
    (⟨_, hw.2 a ha⟩, ⟨_, hw.2 b hb⟩, ⟨_, hw.2 c hc⟩, ⟨_, hw.2 d hd⟩)
  have e1 := congrArg (fun p => ((p.1 : ↥(zpowers ζ₀)) : G)) hx
  have e2 := congrArg (fun p => ((p.2.1 : ↥(zpowers ζ₀)) : G)) hx
  have e3 := congrArg (fun p => ((p.2.2.1 : ↥(zpowers ζ₀)) : G)) hx
  have e4 := congrArg (fun p => ((p.2.2.2 : ↥(zpowers ζ₀)) : G)) hx
  refine ⟨(x : G), x.2, hw.1, ?_⟩
  refine eq_on_closure (s := ({a, b, c, d} : Set G)) hE (f := fun e => w * e * w⁻¹ * e⁻¹)
    (f' := fun e => iota ζ₀ ((x : G) * e * (x : G)⁻¹ * e⁻¹)) ?_ ?_ ?_
  · intro e he e' he'
    exact h.cmt_mul_right hα hw.1 (h.E_le_Qs hα he) (h.E_le_Qs hα he')
  · intro e he e' he'
    show iota ζ₀ ((x : G) * (e * e') * (x : G)⁻¹ * (e * e')⁻¹) = _
    rw [h.cmt_mul_right hα (h.E_le_Qs hα x.2) (h.E_le_Qs hα he) (h.E_le_Qs hα he')]
    exact iota_mul hζ₀.sq h.t_ne h.t_sq (h.oe.econfig.comm x x.2 e he)
      (h.oe.econfig.comm x x.2 e' he')
  · intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl
    exacts [e1.symm, e2.symm, e3.symm, e4.symm]

theorem exists_anticomm_E2 : ∃ x ∈ E2 E t, ∃ y ∈ E2 E t, x * y ≠ y * x := by
  have hc := h.ef.card_two
  have hne : ({e : G | e ∈ E ∧ e * e = 1 ∧ e ≠ 1 ∧ e ≠ t} : Set G).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Set.ncard_empty] at hc
    omega
  obtain ⟨x, hx⟩ := hne
  have h8 := h.ef.anti_two x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  have hne2 : ({y : G | y ∈ E ∧ y * y = 1 ∧ y ≠ 1 ∧ y ≠ t ∧ y * x ≠ x * y} : Set G).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Set.ncard_empty] at h8
    omega
  obtain ⟨y, hy⟩ := hne2
  exact ⟨x, hx, y, ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1⟩, fun hxy => hy.2.2.2.2 hxy.symm⟩

theorem E2_comm_cases {x y : G} (hx : x ∈ E2 E t) (hy : y ∈ E2 E t) (hxy : x * y = y * x) :
    y = x ∨ y = x * t := by
  classical
  have hxE : x ∈ E := hx.1
  have hxt : x * t = t * x := h.t_comm_E x hxE
  have hTc : (E2 E t).ncard = 10 := h.ef.card_two
  set A : Set G := {y : G | y ∈ E ∧ y * y = 1 ∧ y ≠ 1 ∧ y ≠ t ∧ y * x ≠ x * y} with hA
  have hAT : A ⊆ E2 E t := fun y hy => ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1⟩
  have hAc : A.ncard = 8 := h.ef.anti_two x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  have hdiff : (E2 E t \ A).ncard = 2 := by rw [Set.ncard_sdiff hAT, hTc, hAc]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  have hxtT : x * t ∈ E2 E t := by
    refine ⟨mul_mem hxE h.t_mem_E, ?_, ?_, ?_⟩
    · calc x * t * (x * t) = x * (t * x) * t := by group
        _ = x * (x * t) * t := by rw [← hxt]
        _ = (x * x) * (t * t) := by group
        _ = 1 := by rw [hx.2.1, h.t_sq, one_mul]
    · intro h1
      apply hx.2.2.2
      have := eq_inv_of_mul_eq_one_left h1
      rw [this, hti]
    · intro h1
      exact hx.2.2.1 (mul_eq_right.1 h1)
  have hxxt : x ≠ x * t := fun h1 => h.t_ne (mul_eq_left.1 h1.symm)
  have hsub : ({x, x * t} : Set G) ⊆ E2 E t \ A := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact ⟨hx, fun hA' => hA'.2.2.2.2 rfl⟩
    · refine ⟨hxtT, fun hA' => hA'.2.2.2.2 ?_⟩
      calc x * t * x = x * (t * x) := by group
        _ = x * (x * t) := by rw [← hxt]
  have heq : ({x, x * t} : Set G) = E2 E t \ A :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_pair hxxt, hdiff]) (Set.toFinite _)
  have hyTA : y ∈ E2 E t \ A := ⟨hy, fun hyA => hyA.2.2.2.2 hxy.symm⟩
  rw [← heq] at hyTA
  simpa using hyTA

theorem closure_E2_eq : Subgroup.closure (E2 E t) = E := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact h.E2_sub
  · obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ := h.exists_anticomm_E2
    have ht : t ∈ Subgroup.closure (E2 E t) := by
      have hc := h.oe.econfig.comm x₀ hx₀.1 y₀ hy₀.1
      have h1 : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ ≠ 1 := fun h1 => hxy (cmt_eq_one_iff.1 h1)
      have h2 : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ = t := hc.resolve_left h1
      have h3 : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ ∈ Subgroup.closure (E2 E t) :=
        mul_mem (mul_mem (mul_mem (Subgroup.subset_closure hx₀) (Subgroup.subset_closure hy₀))
          (inv_mem (Subgroup.subset_closure hx₀))) (inv_mem (Subgroup.subset_closure hy₀))
      rwa [h2] at h3
    intro e he
    rw [h.oe.econfig.gen] at he
    have hle : Subgroup.closure {e : G | e ∈ E ∧ e * e = 1 ∧ e ≠ 1} ≤
        Subgroup.closure (E2 E t) := by
      rw [Subgroup.closure_le]
      intro e he
      by_cases het : e = t
      · rw [het]; exact ht
      · exact Subgroup.subset_closure ⟨he.1, he.2.1, he.2.2, het⟩
    exact hle he

theorem cmt_mul_central {α : G} (hα : AlphaSpec S z t α) {q r u u' : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hr : r ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hu : u ∈ (zpowers α ⊔ zpowers t : Subgroup G))
    (hu' : u' ∈ (zpowers α ⊔ zpowers t : Subgroup G)) :
    (q * u) * (r * u') * (q * u)⁻¹ * (r * u')⁻¹ = q * r * q⁻¹ * r⁻¹ := by
  have huQ := (h.Zg_cent_Q hα hu).1
  have hu'Q := (h.Zg_cent_Q hα hu').1
  have h1 : u * (r * u') * u⁻¹ * (r * u')⁻¹ = 1 := by
    apply cmt_eq_one_iff.2
    exact ((h.Zg_cent_Q hα hu).2 _ (mul_mem hr hu'Q))
  have h2 : q * u' * q⁻¹ * u'⁻¹ = 1 := by
    apply cmt_eq_one_iff.2
    exact ((h.Zg_cent_Q hα hu').2 q hq).symm
  rw [h.cmt_mul_left hα hq huQ (mul_mem hr hu'Q), h1, mul_one,
    h.cmt_mul_right hα hq hr hu'Q, h2, mul_one]

theorem isLift_of_mul_t {α : G} (hα : AlphaSpec S z t α) {ζ₀ x w : G} (_hx : x ∈ E)
    (hw : IsLift h hα ζ₀ (x * t) w) : IsLift h hα ζ₀ x w := by
  refine ⟨hw.1, fun e he => ?_⟩
  rw [hw.2 e he]
  congr 1
  have hte : t * e = e * t := (h.t_comm_E e he).symm
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  calc x * t * e * (x * t)⁻¹ * e⁻¹ = x * (t * e) * t⁻¹ * x⁻¹ * e⁻¹ := by group
    _ = x * (e * t) * t⁻¹ * x⁻¹ * e⁻¹ := by rw [hte]
    _ = x * e * x⁻¹ * e⁻¹ := by group

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
