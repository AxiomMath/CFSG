module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSimple

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Quasithin Subgroup
open scoped commutatorElement

variable {V : Type} [CommGroup V]

theorem cg_eq_of_add {a b : V} (h : Additive.ofMul a = Additive.ofMul b) : a = b :=
  Additive.ofMul.injective h

theorem flag_trivial {L : Subgroup (MulAut V)} (hperf : _root_.commutator ↥L = ⊤)
    {W₀ W₁ M : Subgroup V} (hM : ∀ g ∈ L, ∀ m ∈ M, g m ∈ M)
    (hW₀ : ∀ g ∈ L, ∀ w ∈ W₀, g w ∈ W₀)
    (h1 : ∀ g ∈ L, ∀ m ∈ M, g m * m⁻¹ ∈ W₁)
    (h0 : ∀ g ∈ L, ∀ w ∈ W₁, g w * w⁻¹ ∈ W₀) :
    ∀ g ∈ L, ∀ m ∈ M, g m * m⁻¹ ∈ W₀ := by
  let N : Subgroup ↥L :=
    { carrier := {g | ∀ m ∈ M, (g : MulAut V) m * m⁻¹ ∈ W₀}
      one_mem' := fun m _ => by simp
      mul_mem' := by
        intro g h hg hh m hm
        have e : ((g : MulAut V) * (h : MulAut V)) m * m⁻¹ =
            (g : MulAut V) ((h : MulAut V) m * m⁻¹) * ((g : MulAut V) m * m⁻¹) := by
          apply cg_eq_of_add
          simp only [MulAut.mul_apply, map_mul, map_inv, ofMul_mul, ofMul_inv]
          abel
        show ((g : MulAut V) * (h : MulAut V)) m * m⁻¹ ∈ W₀
        rw [e]
        exact W₀.mul_mem (hW₀ g g.2 _ (hh m hm)) (hg m hm)
      inv_mem' := by
        intro g hg m hm
        have hm' : (g : MulAut V)⁻¹ m ∈ M := hM _ (L.inv_mem g.2) m hm
        have := hg _ hm'
        have e : ((g : MulAut V)⁻¹ : MulAut V) m * m⁻¹ =
            (((g : MulAut V) ((g : MulAut V)⁻¹ m) * ((g : MulAut V)⁻¹ m)⁻¹))⁻¹ := by
          apply cg_eq_of_add
          simp only [MulAut.apply_inv_self, ofMul_mul, ofMul_inv]
          abel
        show ((g : MulAut V)⁻¹) m * m⁻¹ ∈ W₀
        rw [e]
        exact W₀.inv_mem this }
  have hcomm : ∀ g ∈ L, ∀ h ∈ L, ∀ u ∈ M,
      (g * h : MulAut V) u * ((h * g : MulAut V) u)⁻¹ ∈ W₀ := by
    intro g hg h hh u hu
    have ag := h1 g hg u hu
    have ah := h1 h hh u hu
    have bg := h0 g hg _ ah
    have bh := h0 h hh _ ag
    have e : (g * h : MulAut V) u * ((h * g : MulAut V) u)⁻¹ =
        (g (h u * u⁻¹) * (h u * u⁻¹)⁻¹) * (h (g u * u⁻¹) * (g u * u⁻¹)⁻¹)⁻¹ := by
      apply cg_eq_of_add
      simp only [MulAut.mul_apply, map_mul, map_inv, ofMul_mul, ofMul_inv]
      abel
    rw [e]
    exact W₀.mul_mem bg (W₀.inv_mem bh)
  have hN : _root_.commutator ↥L ≤ N := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g _ h _ m hm
    have hu : ((h : MulAut V) * (g : MulAut V))⁻¹ m ∈ M :=
      hM _ (L.inv_mem (L.mul_mem h.2 g.2)) m hm
    have := hcomm g g.2 h h.2 _ hu
    have e0 : ((⁅g, h⁆ : ↥L) : MulAut V) = ((g : MulAut V) * (h : MulAut V)) *
        ((h : MulAut V) * (g : MulAut V))⁻¹ := by
      simp [commutatorElement_def, mul_inv_rev, mul_assoc]
    have e : ((⁅g, h⁆ : ↥L) : MulAut V) m = ((g * h : MulAut V)) (((h * g : MulAut V))⁻¹ m) := by
      rw [e0]; rfl
    have e2 : ((h * g : MulAut V)) (((h * g : MulAut V))⁻¹ m) = m := by simp
    show ((⁅g, h⁆ : ↥L) : MulAut V) m * m⁻¹ ∈ W₀
    rw [e]
    rw [e2] at this
    exact this
  intro g hg m hm
  have : (⟨g, hg⟩ : ↥L) ∈ N := by
    rw [hperf] at hN
    exact hN (Subgroup.mem_top _)
  exact this m hm

theorem isU4_simple {n : ℕ} {L : Subgroup (MulAut V)} (h : IsU4Group n L) :
    IsSimpleGroup ↥L ∧ ∃ a b : ↥L, a * b ≠ b * a := by
  obtain ⟨d, ⟨q, hq2, hqn, hd⟩, ⟨e⟩⟩ := h
  haveI := u4Group_isSimple hq2 hd
  have hs : IsSimpleGroup ↥L := e.isSimpleGroup
  refine ⟨hs, ?_⟩
  obtain ⟨a, b, hab⟩ := u4Group_nonabelian hq2 hd
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem commutator_eq_top_of_simple {L : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥L)
    (hna : ∃ a b : ↥L, a * b ≠ b * a) : _root_.commutator ↥L = ⊤ := by
  rcases hs.eq_bot_or_eq_top_of_normal (_root_.commutator ↥L) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have : ⁅a, b⁆ ∈ _root_.commutator ↥L := Subgroup.commutator_mem_commutator trivial trivial
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact hab this
  · exact h

@[expose] def XInv (L A : Subgroup (MulAut V)) (Z : Subgroup V) : Prop :=
  L ≤ stabSub Z ∧ A ≤ stabSub Z

@[expose] def LTrivOn (L : Subgroup (MulAut V)) (Z' Z : Subgroup V) : Prop :=
  ∀ g ∈ L, ∀ z ∈ Z, g z * z⁻¹ ∈ Z'

@[expose] def IsXChief (L A : Subgroup (MulAut V)) (Z' Z : Subgroup V) : Prop :=
  XInv L A Z' ∧ XInv L A Z ∧ Z' < Z ∧ ∀ W, XInv L A W → Z' ≤ W → W ≤ Z → W = Z' ∨ W = Z

theorem XInv.inf {L A : Subgroup (MulAut V)} {Z Z' : Subgroup V} (h : XInv L A Z)
    (h' : XInv L A Z') : XInv L A (Z ⊓ Z') := by
  refine ⟨fun g hg u => ?_, fun g hg u => ?_⟩
  · rw [Subgroup.mem_inf, Subgroup.mem_inf, h.1 hg u, h'.1 hg u]
  · rw [Subgroup.mem_inf, Subgroup.mem_inf, h.2 hg u, h'.2 hg u]

theorem XInv.bot (L A : Subgroup (MulAut V)) : XInv L A (⊥ : Subgroup V) :=
  ⟨fun g _ u => by simp [Subgroup.mem_bot], fun g _ u => by simp [Subgroup.mem_bot]⟩

theorem mem_of_stab {g : MulAut V} {Z : Subgroup V} (hg : g ∈ stabSub Z) {z : V} (hz : z ∈ Z) :
    g z ∈ Z := (hg z).2 hz

theorem mem_stabSub_of_inv {Z : Subgroup V} {g : MulAut V} (h1 : ∀ z ∈ Z, g z ∈ Z)
    (h2 : ∀ z ∈ Z, g⁻¹ z ∈ Z) : g ∈ stabSub Z := fun u =>
  ⟨fun hu => by simpa using h2 _ hu, fun hu => h1 _ hu⟩

theorem commV_stab {L : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut V))) : g ∈ stabSub (commV L) := by
  have key : ∀ g' ∈ Subgroup.normalizer (L : Set (MulAut V)), ∀ z ∈ commV L, g' z ∈ commV L := by
    intro g' hg' z hz
    refine Subgroup.closure_induction (p := fun z _ => g' z ∈ commV L) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨x, hx, v, rfl⟩
      refine Subgroup.subset_closure ⟨g' * x * g'⁻¹, ?_, g' v, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hg' x).mp hx
      · simp
    · simp
    · intro a b _ _ ha hb
      rw [map_mul]
      exact (commV L).mul_mem ha hb
    · intro a _ ha
      rw [map_inv]
      exact (commV L).inv_mem ha
  exact mem_stabSub_of_inv (key g hg) (key g⁻¹ ((Subgroup.normalizer _).inv_mem hg))

theorem le_normalizer_self (L : Subgroup (MulAut V)) : L ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
  Subgroup.le_normalizer

theorem xInv_commV {L A : Subgroup (MulAut V)} (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    XInv L A (commV L) :=
  ⟨fun _ hg => commV_stab (le_normalizer_self L hg), fun _ hg => commV_stab (hAL hg)⟩

theorem commSub_commV {L : Subgroup (MulAut V)} (hperf : _root_.commutator ↥L = ⊤) :
    commSub (commV L) L = commV L := by
  have hinvU : ∀ x ∈ L, ∀ w ∈ commV L, x w ∈ commV L := fun x hx w hw =>
    (commV_stab (le_normalizer_self L hx) w).2 hw
  apply le_antisymm (commSub_le_of_invariant hinvU)
  have hinvU' : ∀ g ∈ L, ∀ w ∈ commSub (commV L) L, g w ∈ commSub (commV L) L := by
    intro g hg w hw
    refine Subgroup.closure_induction (p := fun w _ => g w ∈ commSub (commV L) L) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨x, hx, u, hu, rfl⟩
      refine Subgroup.subset_closure ⟨g * x * g⁻¹, ?_, g u, hinvU g hg u hu, ?_⟩
      · exact L.mul_mem (L.mul_mem hg hx) (L.inv_mem hg)
      · simp
    · simp
    · intro a b _ _ ha hb
      rw [map_mul]; exact (commSub (commV L) L).mul_mem ha hb
    · intro a _ ha
      rw [map_inv]; exact (commSub (commV L) L).inv_mem ha
  have hflag := flag_trivial hperf (W₀ := commSub (commV L) L) (W₁ := commV L) (M := ⊤)
    (fun g _ m _ => trivial) hinvU'
    (fun g hg m _ => Subgroup.subset_closure ⟨g, hg, m, rfl⟩)
    (fun g hg w hw => Subgroup.subset_closure ⟨g, hg, w, hw, rfl⟩)
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  exact hflag x hx v trivial

@[expose] def cenD (L A : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  A ⊓ Subgroup.centralizer (L : Set (MulAut V))

theorem cenD_le (L A : Subgroup (MulAut V)) : cenD L A ≤ A := inf_le_left

theorem cenD_comm {L A : Subgroup (MulAut V)} {d l : MulAut V} (hd : d ∈ cenD L A) (hl : l ∈ L) :
    l * d = d * l :=
  Subgroup.mem_centralizer_iff.mp hd.2 l hl

theorem mem_stabSub_fixV_of_comm {D : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ d ∈ D, g * d = d * g) : g ∈ stabSub (fixV D) := by
  have key : ∀ g' : MulAut V, (∀ d ∈ D, g' * d = d * g') → ∀ v ∈ fixV D, g' v ∈ fixV D := by
    intro g' hg' v hv d hd
    have := congrArg (fun φ : MulAut V => φ v) (hg' d hd)
    simp only [MulAut.mul_apply] at this
    rw [← this, hv d hd]
  refine mem_stabSub_of_inv (key g hg) (key g⁻¹ (fun d hd => ?_))
  have := hg d hd
  calc g⁻¹ * d = g⁻¹ * (d * g) * g⁻¹ := by group
    _ = g⁻¹ * (g * d) * g⁻¹ := by rw [this]
    _ = d * g⁻¹ := by group

theorem xInv_fixV_cenD {L A : Subgroup (MulAut V)} (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    XInv L A (fixV (cenD L A)) :=
  ⟨fun g hg => mem_stabSub_fixV_of_comm fun d hd => cenD_comm hd hg,
   fun g hg => mem_stabSub_fixV_of_comm fun d hd => hAcomm g hg d (cenD_le L A hd)⟩

theorem inf_centSec_le_cenD {L A : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥L)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V))) {Z' Z : Subgroup V} (hZ'Z : Z' ≤ Z)
    (hLZ : L ≤ stabSub Z) (hLZ' : L ≤ stabSub Z') (hnc : ¬ LTrivOn L Z' Z) :
    A ⊓ centSec Z Z' ≤ cenD L A := by
  let K : Subgroup ↥L := (L ⊓ centSec Z Z').subgroupOf L
  have hKn : K.Normal := ⟨fun k hk g => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hk ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hk.1) (L.inv_mem g.2), ?_, ?_⟩
    · exact (stabSub Z).mul_mem ((stabSub Z).mul_mem (hLZ g.2) hk.2.1)
        ((stabSub Z).inv_mem (hLZ g.2))
    · intro z hz
      have hz1 : (g : MulAut V)⁻¹ z ∈ Z := mem_of_stab (hLZ (L.inv_mem g.2)) hz
      have h1 := hk.2.2 _ hz1
      have h2 := mem_of_stab (hLZ' g.2) h1
      have e : ((g : MulAut V) * (k : MulAut V) * (g : MulAut V)⁻¹) z * z⁻¹ =
          (g : MulAut V) ((k : MulAut V) ((g : MulAut V)⁻¹ z) * ((g : MulAut V)⁻¹ z)⁻¹) := by
        simp
      show ((g : MulAut V) * (k : MulAut V) * (g : MulAut V)⁻¹) z * z⁻¹ ∈ Z'
      rw [e]; exact h2⟩
  haveI := hKn
  have hKbot : K = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal K with h | h
    · exact h
    · exfalso
      apply hnc
      intro g hg z hz
      have : (⟨g, hg⟩ : ↥L) ∈ K := by rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).2.2 z hz
  intro a ha
  refine ⟨ha.1, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  have hainv : a⁻¹ ∈ centSec Z Z' := (centSec Z Z').inv_mem ha.2
  have haN : a⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
    (Subgroup.normalizer _).inv_mem (hAL ha.1)
  have hcL : a⁻¹ * l⁻¹ * a * l ∈ L := by
    have h1 : a⁻¹ * l⁻¹ * (a⁻¹)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp haN l⁻¹).mp (L.inv_mem hl)
    have : a⁻¹ * l⁻¹ * a * l = (a⁻¹ * l⁻¹ * (a⁻¹)⁻¹) * l := by group
    rw [this]; exact L.mul_mem h1 hl
  have hcK : (⟨a⁻¹ * l⁻¹ * a * l, hcL⟩ : ↥L) ∈ K := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨hcL, ?_, ?_⟩
    · exact (stabSub Z).mul_mem ((stabSub Z).mul_mem ((stabSub Z).mul_mem
        ((stabSub Z).inv_mem ha.2.1) ((stabSub Z).inv_mem (hLZ hl))) ha.2.1) (hLZ hl)
    · intro z hz
      have hz₁ : l z ∈ Z := mem_of_stab (hLZ hl) hz
      have ht' : a (l z) * (l z)⁻¹ ∈ Z' := ha.2.2 (l z) hz₁
      have hlt' : l⁻¹ (a (l z) * (l z)⁻¹) ∈ Z' := mem_of_stab (hLZ' (L.inv_mem hl)) ht'
      have e1 : l⁻¹ (a (l z)) = l⁻¹ (a (l z) * (l z)⁻¹) * z := by
        simp
      have h4a : a⁻¹ (l⁻¹ (a (l z) * (l z)⁻¹)) * (l⁻¹ (a (l z) * (l z)⁻¹))⁻¹ ∈ Z' :=
        hainv.2 _ (hZ'Z hlt')
      have h4 : a⁻¹ (l⁻¹ (a (l z) * (l z)⁻¹)) ∈ Z' := by
        have := Z'.mul_mem h4a hlt'
        rwa [inv_mul_cancel_right] at this
      have h5 : a⁻¹ z * z⁻¹ ∈ Z' := hainv.2 z hz
      have e2 : (a⁻¹ * l⁻¹ * a * l) z * z⁻¹ =
          a⁻¹ (l⁻¹ (a (l z) * (l z)⁻¹)) * (a⁻¹ z * z⁻¹) := by
        simp only [MulAut.mul_apply]
        rw [e1, map_mul, mul_assoc]
      show (a⁻¹ * l⁻¹ * a * l) z * z⁻¹ ∈ Z'
      rw [e2]
      exact Z'.mul_mem h4 h5
  have hc1 : a⁻¹ * l⁻¹ * a * l = 1 := by
    have := hcK
    rw [hKbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  calc l * a = (l * a) * (a⁻¹ * l⁻¹ * a * l) := by rw [hc1, mul_one]
    _ = a * l := by group

end CFSG.LocalAnalysis.RankThreeUC
