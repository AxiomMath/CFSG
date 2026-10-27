module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSMCheck
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCore
import CFSG.ClassicalInvolution.Q3.ONanTA3SmallVerdictSound
import CFSG.ClassicalInvolution.Asc77.AscCX8D

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

set_option linter.unusedSectionVars false

theorem q8List_map {G H : Type} [Group G] [Group H] (f : G →* H) (t a b : G) :
    q8List (f t) (f a) (f b) = (q8List t a b).map f := by
  simp [q8List, map_mul]

theorem mem_q8List_map_iff {G H : Type} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {t a b x : G} :
    f x ∈ q8List (f t) (f a) (f b) ↔ x ∈ q8List t a b := by
  rw [q8List_map]
  exact List.mem_map_of_injective hf

theorem mem_q8List_conj_iff {G : Type} [Group G] (g t a b x : G) :
    g * x * g⁻¹ ∈ q8List (g * t * g⁻¹) (g * a * g⁻¹) (g * b * g⁻¹) ↔ x ∈ q8List t a b := by
  let f : G →* G := (MulAut.conj g).toMonoidHom
  have hfi : Function.Injective f := (MulAut.conj g).injective
  exact mem_q8List_map_iff (f := f) hfi

theorem conj_mem_of_mem_q8List {G : Type} [Group G] {H : Subgroup G} {g t a b : G}
    (ht : g * t * g⁻¹ ∈ H) (ha : g * a * g⁻¹ ∈ H) (hb : g * b * g⁻¹ ∈ H) {y : G}
    (hy : y ∈ q8List t a b) : g * y * g⁻¹ ∈ H := by
  have hm : ∀ x z : G, g * (x * z) * g⁻¹ = (g * x * g⁻¹) * (g * z * g⁻¹) := fun x z => by group
  simp only [q8List, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact ha
  · exact ht
  · rw [hm]; exact H.mul_mem ht ha
  · exact hb
  · rw [hm]; exact H.mul_mem hb ha
  · rw [hm]; exact H.mul_mem hb ht
  · rw [hm, hm]; exact H.mul_mem hb (H.mul_mem ht ha)

section Sound

variable {G M : Type} [Group G] [Group M] [DecidableEq M] {ι : G →* M}
  (hι : Function.Injective ι) {L : List M} (hL : ∀ m, m ∈ L ↔ ∃ y, ι y = m)

include hι hL in
theorem nq_of_nqCheck {inX : M → Bool} {X : Subgroup G} [hXn : X.Normal]
    (hX : ∀ y : G, inX (ι y) = true ↔ y ∈ X) {reps : List M} (h : nqCheck inX L reps = true)
    {t a b : G} (ht : orderOf t = 2) (haa : a * a = t) (hbb : b * b = t)
    (hba : b * a = t * a * b) :
    a ∈ X ∧ b ∈ X ∧ ∀ c : G, c * t = t * c → c ∈ X →
      c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b := by
  have hcov : coverB reps L = true := (Bool.and_eq_true_iff.1 h).1
  have hall : ∀ r ∈ reps, nqAt inX r (centB L r) = true := fun r hr =>
    List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).2 r hr
  obtain ⟨r, hr, g, hg⟩ := cover_of_coverB hι hL hcov ht
  have hm : ∀ x z : G, (g * x * g⁻¹) * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := fun x z => by group
  have hconjX : ∀ x : G, g * x * g⁻¹ ∈ X → x ∈ X := fun x hx => by
    have h1 := hXn.conj_mem _ hx g⁻¹
    simpa [mul_assoc] using h1
  have ha2 : (g * a * g⁻¹) * (g * a * g⁻¹) = r := by rw [hm, haa, hg]
  have hb2 : (g * b * g⁻¹) * (g * b * g⁻¹) = r := by rw [hm, hbb, hg]
  have hba' : (g * b * g⁻¹) * (g * a * g⁻¹) = r * (g * a * g⁻¹) * (g * b * g⁻¹) := by
    rw [hm, hba, ← hg, hm, hm]
  have hcomm : ∀ x : G, x * x = r → x * r = r * x := fun x hx => by
    rw [← hx]
    group
  have haC : ι (g * a * g⁻¹) ∈ centB L (ι r) :=
    (mem_centB hι hL).2 ⟨_, hcomm _ ha2, rfl⟩
  have hbC : ι (g * b * g⁻¹) ∈ centB L (ι r) :=
    (mem_centB hι hL).2 ⟨_, hcomm _ hb2, rfl⟩
  have h1 := hall (ι r) hr
  unfold nqAt at h1
  rw [List.all_eq_true] at h1
  have h2 := h1 _ (List.mem_filter.2 ⟨haC, decide_eq_true (by rw [← map_mul, ha2])⟩)
  rw [List.all_eq_true] at h2
  have h3 := h2 _ (List.mem_filter.2 ⟨hbC, decide_eq_true (by rw [← map_mul, hb2])⟩)
  have hrel : ι (g * b * g⁻¹) * ι (g * a * g⁻¹) =
      ι r * ι (g * a * g⁻¹) * ι (g * b * g⁻¹) := by
    simp only [← map_mul, hba']
  rw [decide_eq_true hrel, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Bool.and_eq_true] at h3
  obtain ⟨⟨hXa, hXb⟩, hc⟩ := h3
  refine ⟨hconjX a ((hX _).1 hXa), hconjX b ((hX _).1 hXb), fun c hct hcX => ?_⟩
  have hc'X : g * c * g⁻¹ ∈ X := hXn.conj_mem c hcX g
  have hc'r : (g * c * g⁻¹) * r = r * (g * c * g⁻¹) := by
    rw [← hg, hm, hm, hct]
  have hcC : ι (g * c * g⁻¹) ∈ centB L (ι r) := (mem_centB hι hL).2 ⟨_, hc'r, rfl⟩
  rw [List.all_eq_true] at hc
  have h4 := hc _ hcC
  rw [(hX _).2 hc'X, Bool.not_true, Bool.false_or, Bool.and_eq_true, memB_iff, memB_iff,
    q8B_eq] at h4
  obtain ⟨h5, h6⟩ := h4
  have hc3 : ∀ x : G, (g * c * g⁻¹) * (g * x * g⁻¹) * (g * c * g⁻¹)⁻¹ = g * (c * x * c⁻¹) * g⁻¹ :=
    fun x => by group
  rw [← map_inv, ← map_mul, ← map_mul, List.mem_map_of_injective hι, hc3, ← hg,
    mem_q8List_conj_iff] at h5 h6
  exact ⟨h5, h6⟩

end Sound

theorem nq_comap {Y G : Type} [Group Y] [Group G] {f : Y →* G} (hf : Function.Injective f)
    {X : Subgroup G}
    (hG : ∀ t a b : G, orderOf t = 2 → a * a = t → b * b = t → b * a = t * a * b →
      a ∈ X ∧ b ∈ X ∧ ∀ c : G, c * t = t * c → c ∈ X →
        c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b)
    {t : Y} (ht : orderOf t = 2) (a b : Y) (haa : a * a = t) (hbb : b * b = t)
    (hba : b * a = t * a * b) :
    a ∈ X.comap f ∧ b ∈ X.comap f ∧ ∀ c : Y, c * t = t * c → c ∈ X.comap f →
      c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b := by
  have ht' : orderOf (f t) = 2 := by rw [orderOf_injective f hf]; exact ht
  obtain ⟨ha, hb, hc⟩ := hG (f t) (f a) (f b) ht' (by rw [← map_mul, haa])
    (by rw [← map_mul, hbb]) (by simp only [← map_mul, hba])
  refine ⟨ha, hb, fun c hct hcX => ?_⟩
  obtain ⟨h1, h2⟩ := hc (f c) (by rw [← map_mul, hct, map_mul]) hcX
  rw [← map_inv, ← map_mul, ← map_mul, mem_q8List_map_iff hf] at h1 h2
  exact ⟨h1, h2⟩

section Twin


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem false_of_normalQ8 (h : PerpHypS n Y R S t) {X : Subgroup Y} [hXn : X.Normal]
    (hnq : ∀ a b : Y, a * a = t → b * b = t → b * a = t * a * b →
      a ∈ X ∧ b ∈ X ∧ ∀ c : Y, c * t = t * c → c ∈ X →
        c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b) : False := by
  classical
  have hz : IsUniqueInvolution (tightCore R) t := uniqueInv_core h
  obtain ⟨e⟩ := h.core.q8
  set S' : Subgroup Y := (S : Subgroup R).map R.subtype with hS'
  let φ : QuaternionGroup 2 →* Y :=
    R.subtype.comp ((S : Subgroup R).subtype.comp e.symm.toMonoidHom)
  have hφ : Function.Injective φ :=
    Subtype.val_injective.comp (Subtype.val_injective.comp e.symm.injective)
  have hφS : ∀ w, φ w ∈ S' := fun w => ⟨(e.symm w : R), (e.symm w).2, rfl⟩
  have hSφ : ∀ y ∈ S', ∃ w, φ w = y := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨e ⟨x, hx⟩, by simp [φ]⟩
  have hS'K : S' ≤ tightCore R := h.core.datum.sylow_core.1
  have ht : φ (QuaternionGroup.a 2) = t := by
    have h2 : φ (QuaternionGroup.a 2) * φ (QuaternionGroup.a 2) = 1 := by
      rw [← map_mul, show (QuaternionGroup.a 2 * QuaternionGroup.a 2 : QuaternionGroup 2) = 1 by
        decide, map_one]
    have h1 : φ (QuaternionGroup.a 2) ≠ 1 := fun h' =>
      absurd (hφ (h'.trans (map_one φ).symm)) (by decide)
    exact (hz.unique _ (hS'K (hφS _)) h2).resolve_left h1
  obtain ⟨a₀, ha₀⟩ : ∃ x : Y, x = φ (QuaternionGroup.a 1) := ⟨_, rfl⟩
  obtain ⟨b₀, hb₀⟩ : ∃ x : Y, x = φ (QuaternionGroup.xa 0) := ⟨_, rfl⟩
  have hq : q8List t a₀ b₀ = (q8List (QuaternionGroup.a 2) (QuaternionGroup.a 1)
      (QuaternionGroup.xa 0)).map φ := by
    rw [← ht, ha₀, hb₀, q8List_map]
  have haa : a₀ * a₀ = t := by
    rw [ha₀, ← ht, ← map_mul]
    exact congrArg φ (by decide)
  have hbb : b₀ * b₀ = t := by
    rw [hb₀, ← ht, ← map_mul]
    exact congrArg φ (by decide)
  have hba : b₀ * a₀ = t * a₀ * b₀ := by
    rw [ha₀, hb₀, ← ht, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg φ (by decide)
  have hall8 : ∀ w : QuaternionGroup 2,
      w ∈ q8List (QuaternionGroup.a 2) (QuaternionGroup.a 1) (QuaternionGroup.xa 0) := by
    decide
  have hSq : ∀ y ∈ S', y ∈ q8List t a₀ b₀ := by
    intro y hy
    obtain ⟨w, rfl⟩ := hSφ y hy
    rw [hq]
    exact List.mem_map_of_mem (hall8 w)
  have hqS : ∀ y ∈ q8List t a₀ b₀, y ∈ S' := by
    intro y hy
    rw [hq, List.mem_map] at hy
    obtain ⟨w, -, rfl⟩ := hy
    exact hφS w
  obtain ⟨haX, hbX, hcn⟩ := hnq a₀ b₀ haa hbb hba
  have htX : t ∈ X := haa ▸ X.mul_mem haX haX
  have hS'X : S' ≤ X := fun y hy => by
    have h1 := conj_mem_of_mem_q8List (H := X) (g := 1) (by simpa using htX)
      (by simpa using haX) (by simpa using hbX) (hSq y hy)
    simpa using h1
  have hKX : tightCore R ≤ X := by
    unfold tightCore
    rw [Subgroup.closure_le]
    rintro x ⟨hxR, hx2⟩
    have hxK : x ∈ tightCore R := Subgroup.subset_closure ⟨hxR, hx2⟩
    obtain ⟨c, -, hc⟩ := CX.exists_conj_le_of_isSylow2In h.core.datum.sylow_core hx2
      (Subgroup.zpowers_le.mpr hxK)
    have h1 := hXn.conj_mem _ (hS'X (hc x (Subgroup.mem_zpowers x))) c
    simpa [mul_assoc] using h1
  have hXall : ∀ g : Y, g ∈ X := by
    intro g
    have hle : (⨆ y : Y, conjSub y (tightCore R)) ≤ X := iSup_le fun y => by
      intro z hz
      rw [mem_conjSub_iff] at hz
      have h1 := hXn.conj_mem _ (hKX hz) y
      simpa [mul_assoc] using h1
    have hgen : (⨆ y : Y, conjSub y (tightCore R)) = ⊤ := h.core.gen
    rw [hgen] at hle
    exact hle (Subgroup.mem_top g)
  obtain ⟨g, hgc, hne, hgΩ, -⟩ := exists_twin h
  have hgc' : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp hgc
  have hgt : g⁻¹ * t = t * g⁻¹ := by
    calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hgc']
      _ = t * g⁻¹ := by group
  obtain ⟨h5, h6⟩ := hcn g⁻¹ hgt (hXall _)
  have hti : g⁻¹ * t * g⁻¹⁻¹ = t := by rw [hgt]; group
  have htS : t ∈ S' := h.core.datum.mem
  have hS'K' : S' ≤ conjSub g (tightCore R) := by
    intro y hy
    rw [mem_conjSub_iff]
    have h7 := conj_mem_of_mem_q8List (H := S') (g := g⁻¹) (by rw [hti]; exact htS) (hqS _ h5) (hqS _ h6)
      (hSq y hy)
    simpa using hS'K h7
  have hcard : Nat.card S' = 8 := by
    have e1 : Nat.card S' = Nat.card (S : Subgroup R) :=
      Nat.card_congr (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
        R.subtype_injective).symm.toEquiv
    rw [e1, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hdvd : 2 ^ 3 ∣ Nat.card ↥(tightCore R ⊓ conjSub g (tightCore R)) := by
    have h1 := Subgroup.card_dvd_of_le (le_inf hS'K hS'K')
    rw [hcard] at h1
    exact h1
  have h4 := (h.core.hyp.omega4 (tightCore R) (CoreAssembly.mem_conjClass_self _) _ hgΩ
    (Ne.symm hne)).1
  have h3 := (padicValNat_dvd_iff_le (p := 2) Nat.card_pos.ne').mp hdvd
  omega

theorem false_of_nqCheck (h : PerpHypS n Y R S t) {A M : Type} [Group A] [Group M]
    [DecidableEq M] {ι : A →* M} (hι : Function.Injective ι) {L : List M}
    (hL : ∀ m, m ∈ L ↔ ∃ y, ι y = m) {inX : M → Bool} {X : Subgroup A} [X.Normal]
    (hX : ∀ y : A, inX (ι y) = true ↔ y ∈ X) {reps : List M} (hc : nqCheck inX L reps = true)
    {f : Y →* A} (hf : Function.Injective f) : False :=
  false_of_normalQ8 h (X := X.comap f)
    (nq_comap hf (fun _ _ _ ht haa hbb hba => nq_of_nqCheck hι hL hX hc ht haa hbb hba)
      h.core.datum.order)

theorem false_of_nqCheck_top (h : PerpHypS n Y R S t) {A M : Type} [Group A] [Group M]
    [DecidableEq M] {ι : A →* M} (hι : Function.Injective ι) {L : List M}
    (hL : ∀ m, m ∈ L ↔ ∃ y, ι y = m) {reps : List M}
    (hc : nqCheck (fun _ => true) L reps = true) {f : Y →* A} (hf : Function.Injective f) :
    False :=
  false_of_nqCheck h hι hL (X := ⊤) (fun _ => iff_of_true rfl (Subgroup.mem_top _)) hc hf

end Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM
