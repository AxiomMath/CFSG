module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivAb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_commutatorHom {W : Subgroup G} (hW : ∀ x ∈ W, ∀ x' ∈ W, x * x' = x' * x)
    {r : G} (hr : r ∈ normalizer (W : Set G)) :
    ∃ δ : ↥W →* ↥W, ∀ w : ↥W, (δ w : G) = r⁻¹ * (w : G)⁻¹ * r * w := by
  have hc : ∀ w ∈ W, r⁻¹ * w⁻¹ * r ∈ W := fun w hw => by
    have := (mem_normalizer_iff.mp (inv_mem hr) _).mp (W.inv_mem hw)
    simpa using this
  refine ⟨MonoidHom.mk' (fun w => ⟨r⁻¹ * (w : G)⁻¹ * r * w, W.mul_mem (hc w w.2) w.2⟩)
    fun a b => Subtype.ext ?_, fun w => rfl⟩
  show r⁻¹ * ((a : G) * b)⁻¹ * r * (a * b) =
    (r⁻¹ * (a : G)⁻¹ * r * a) * (r⁻¹ * (b : G)⁻¹ * r * b)
  have h1 := hW _ (hc b b.2) _ (hc a a.2)
  have h2 := hW _ a.2 _ (hc b b.2)
  calc r⁻¹ * ((a : G) * b)⁻¹ * r * (a * b)
      = (r⁻¹ * (b : G)⁻¹ * r) * (r⁻¹ * (a : G)⁻¹ * r) * a * b := by group
    _ = (r⁻¹ * (a : G)⁻¹ * r) * (r⁻¹ * (b : G)⁻¹ * r) * a * b := by rw [h1]
    _ = (r⁻¹ * (a : G)⁻¹ * r) * ((r⁻¹ * (b : G)⁻¹ * r) * a) * b := by group
    _ = (r⁻¹ * (a : G)⁻¹ * r) * (a * (r⁻¹ * (b : G)⁻¹ * r)) * b := by rw [← h2]
    _ = (r⁻¹ * (a : G)⁻¹ * r * a) * (r⁻¹ * (b : G)⁻¹ * r * b) := by group

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem exists_eq_mul_of_mem_sec2P {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
    (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
    (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) {p : G} (hp : p ∈ sec2P E) :
    ∃ w ∈ sec2W A E y, ∃ r ∈ R, p = w * r := by
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  obtain ⟨-, hUW, -, -, hWEP, hPW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hEP : E ≤ sec2P E := (isElemQuot_sec2P h11 hE16 hF hL hodd).1
  have hp' : p ∈ ((sec2W A E y ⊔ E : Subgroup G) : Set G) := by rw [hWEP]; exact hp
  rw [coe_mul_of_right_le_normalizer_left _ _ (hEP.trans hPW)] at hp'
  obtain ⟨w, hw, e, he, hwe⟩ := hp'
  have hwe' : w * e = p := hwe
  obtain ⟨u, hu, r, hr, rfl⟩ := hD.eq_mul e he
  exact ⟨w * u, mul_mem hw (hUW hu), r, hr, by rw [← hwe', mul_assoc]⟩

theorem sec2W_inf_centralizer_eq {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
    (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
    (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) (hW : IsElemAbelian 2 (sec2W A E y))
    {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    sec2W A E y ⊓ centralizer ({r} : Set G) = E ⊓ A := by
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  obtain ⟨-, hUW, hWP, -, -, hPW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hEP : E ≤ sec2P E := (isElemQuot_sec2P h11 hE16 hF hL hodd).1
  have hWc : ∀ x ∈ sec2W A E y, ∀ x' ∈ sec2W A E y, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hW.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have hrE : r ∈ E := hF.R_le_E hr
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hF.sylowR.le hF.sylowR.isPGroup hodd
  have hrA : r ∉ E ⊓ A := fun h => hr1 (by
    have h1 : r ∈ R ⊓ A := ⟨hr, h.2⟩
    rwa [hRA1, mem_bot] at h1)
  obtain ⟨δ, hδ⟩ := exists_commutatorHom hWc (hPW (hEP hrE))
  have hUle : E ⊓ A ≤ sec2W A E y ⊓ centralizer ({r} : Set G) := le_inf hUW fun u hu =>
    mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff.mp hx]
      exact hD.comm r hrE u hu.1
  refine (eq_of_le_of_card_ge hUle ?_).symm
  have h1 : Nat.card (sec2W A E y ⊓ centralizer ({r} : Set G) : Subgroup G) ≤
      Nat.card δ.ker := by
    refine Nat.card_le_card_of_injective (fun x => ⟨⟨x, x.2.1⟩, ?_⟩) fun a b hab => ?_
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hδ]
      have hc : r * (x : G) = x * r := mem_centralizer_iff.mp x.2.2 r (Set.mem_singleton r)
      show r⁻¹ * (x : G)⁻¹ * r * x = 1
      calc r⁻¹ * (x : G)⁻¹ * r * x = r⁻¹ * (x : G)⁻¹ * (r * x) := by group
        _ = 1 := by rw [hc]; group
    · have h := congrArg Subtype.val (congrArg Subtype.val hab)
      exact Subtype.ext h
  have hsurj : ∀ u ∈ E ⊓ A, ∃ w : ↥(sec2W A E y), (δ w : G) = u := by
    intro u hu
    obtain ⟨p, hp, hpr⟩ := exists_conj_eq_mul h11 hE16 hF hL hodd hrE hrA hu
    obtain ⟨w, hw, s, hs, rfl⟩ :=
      exists_eq_mul_of_mem_sec2P h11 hE16 hF hL hodd hyA hyE hyU hy3 hp
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [hδ]
    have hwr : w⁻¹ * r * w ∈ E := by
      have := (mem_normalizer_iff.mp (inv_mem (Sec2.sec2P_le E (hWP hw))) r).mp hrE
      simpa using this
    have hc := hD.comm _ hwr s (hF.R_le_E hs)
    have hs' : s⁻¹ * (w⁻¹ * r * w) * s = w⁻¹ * r * w := by
      calc s⁻¹ * (w⁻¹ * r * w) * s = s⁻¹ * ((w⁻¹ * r * w) * s) := by group
        _ = s⁻¹ * (s * (w⁻¹ * r * w)) := by rw [hc]
        _ = w⁻¹ * r * w := by group
    have hwru : w⁻¹ * r * w = r * u := by
      rw [← hpr, ← hs']
      group
    show r⁻¹ * w⁻¹ * r * w = u
    calc r⁻¹ * w⁻¹ * r * w = r⁻¹ * (w⁻¹ * r * w) := by group
      _ = u := by rw [hwru]; group
  have h2 : (E ⊓ A).subgroupOf (sec2W A E y) ≤ δ.range := fun x hx => by
    obtain ⟨w, hw⟩ := hsurj x (mem_subgroupOf.mp hx)
    exact ⟨w, Subtype.ext hw⟩
  have h2' : Nat.card (E ⊓ A : Subgroup G) ≤ Nat.card δ.range := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hUW).toEquiv]
    exact card_le_of_le h2
  have h3 := card_ker_mul_card_range δ
  rw [card_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3] at h3
  rw [card_inf_left hF hodd] at h2' ⊢
  have h4 : Nat.card δ.ker * 16 ≤ 256 := h3 ▸ Nat.mul_le_mul_left _ h2'
  omega

theorem sec2W_inf_centralizer_eq_of_mem (hT : ¬ E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E)) {y : G}
    (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
    (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
    (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) (hW : IsElemAbelian 2 (sec2W A E y))
    (hW₁ : conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E ≤ sec2W A E y) {f : G} (hf : f ∈ F ⊓ A)
    (hfE : f ∉ E) :
    sec2W A E y ⊓ centralizer ({f} : Set G) = conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E := by
  obtain ⟨hD, T₀, hT₀⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  obtain ⟨r, hr, hr1⟩ := hD.exists_ne_one
  obtain ⟨-, -, hWP, -, -, hPW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hEP : E ≤ sec2P E := (isElemQuot_sec2P h11 hE16 hF hL hodd).1
  have hCr := sec2W_inf_centralizer_eq h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hr hr1
  have hWc : ∀ x ∈ sec2W A E y, ∀ x' ∈ sec2W A E y, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hW.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have hFc : ∀ x ∈ F, ∀ x' ∈ F, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have hfr : Commute f r := hFc f hf.1 r (hF.R_le_F hr)
  have hrE : r ∈ E := hF.R_le_E hr
  have hel := isElemAbelian_conjClosure_inf_sec2P h11 hE16 hF hL hodd hT
  have hle : conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E ≤
      sec2W A E y ⊓ centralizer ({f} : Set G) :=
    le_inf hW₁ fun w hw => mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff.mp hx]
      have h1 := conj_eq_inv_of_mem_conjClosure_inf_sec2P h11 hE16 hF hL hodd hT hf hfE hw
      have h2 : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hel.2 w hw)
      rw [h2] at h1
      calc f * w = f * w * f⁻¹ * f := by group
        _ = w * f := by rw [h1]
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [card_conjClosure_inf_sec2P h11 hE16 hF hL hodd hT]
  set X := sec2W A E y ⊓ centralizer ({f} : Set G) with hX
  have hXc : ∀ x ∈ X, ∀ x' ∈ X, x * x' = x' * x := fun x hx x' hx' => hWc x hx.1 x' hx'.1
  have hrf : r ∈ centralizer ({f} : Set G) := mem_centralizer_iff.mpr fun x hx => by
    rw [Set.mem_singleton_iff.mp hx]
    exact hfr
  have hrX : r ∈ normalizer (X : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hPW (hEP hrE), le_normalizer hrf⟩
  obtain ⟨δ, hδ⟩ := exists_commutatorHom hXc hrX
  have hUZ : ∀ u ∈ E ⊓ A, f * u = u * f → u ∈ sec2Z A E F := fun u hu hfu => by
    by_contra huZ
    exact hfE (mem_of_mem_F_of_commute h11 hE16 hF hL hodd hf.1 hu huZ hfu)
  have hker : Nat.card δ.ker ≤ 4 := by
    rw [← hF.card_sec2Z hodd]
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : ↥X) : G), ?_⟩) fun a b hab => ?_
    · have hk := k.2
      rw [MonoidHom.mem_ker] at hk
      have h1 : r⁻¹ * ((k : ↥X) : G)⁻¹ * r * (k : ↥X) = 1 := by
        have := congrArg Subtype.val hk
        rwa [hδ] at this
      have hkr : ((k : ↥X) : G) ∈ sec2W A E y ⊓ centralizer ({r} : Set G) := by
        refine ⟨(k : ↥X).2.1, mem_centralizer_iff.mpr fun x hx => ?_⟩
        rw [Set.mem_singleton_iff.mp hx]
        calc r * ((k : ↥X) : G) = r * (k : ↥X) * (r⁻¹ * ((k : ↥X) : G)⁻¹ * r * (k : ↥X))⁻¹ := by
              rw [h1, inv_one, mul_one]
          _ = (k : ↥X) * r := by group
      rw [hCr] at hkr
      exact hUZ _ hkr (mem_centralizer_iff.mp (k : ↥X).2.2 f (Set.mem_singleton f))
    · have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
  have hrange : Nat.card δ.range ≤ 4 := by
    rw [← hF.card_sec2Z hodd]
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : ↥X) : G), ?_⟩) fun a b hab => ?_
    · obtain ⟨x, hx⟩ := k.2
      have h1 : ((k : ↥X) : G) = r⁻¹ * (x : G)⁻¹ * r * x := by rw [← hδ, hx]
      rw [h1]
      refine hUZ _ (hD.commutator_mem hT₀ hCE hF.elemE hrE (hWP x.2.1)) ?_
      have hfx : Commute f x := mem_centralizer_iff.mp x.2.2 f (Set.mem_singleton f)
      exact ((hfr.inv_right.mul_right hfx.inv_right).mul_right hfr).mul_right hfx
    · have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
  calc Nat.card ↥X = Nat.card δ.ker * Nat.card δ.range := (card_ker_mul_card_range δ).symm
    _ ≤ 4 * 4 := Nat.mul_le_mul hker hrange

theorem eq_sec2W_of_le {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
    (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
    (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) (hW : IsElemAbelian 2 (sec2W A E y))
    {X : Subgroup G} (hXP : X ≤ sec2P E) (hX : ∀ x ∈ X, ∀ x' ∈ X, x * x' = x' * x)
    (hX256 : Nat.card X = 256) : X = sec2W A E y := by
  obtain ⟨-, -, hWP, -, -, hPW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  obtain ⟨hEP, hPidx, -⟩ := isElemQuot_sec2P h11 hE16 hF hL hodd
  have hW256 := card_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hWc : ∀ x ∈ sec2W A E y, ∀ x' ∈ sec2W A E y, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hW.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have hP : Nat.card (sec2P E) = 1024 := by
    have h := relIndex_mul_card E (sec2P E)
    rw [inf_eq_left.mpr hEP, hPidx, hF.cardE] at h
    omega
  suffices hXW : X ≤ sec2W A E y from eq_of_le_of_card_ge hXW (by rw [hX256, hW256])
  intro x hxX
  by_contra hxW
  obtain ⟨w, hw, r, hr, rfl⟩ :=
    exists_eq_mul_of_mem_sec2P h11 hE16 hF hL hodd hyA hyE hyU hy3 (hXP hxX)
  have hr1 : r ≠ 1 := fun h => hxW (by rw [h, mul_one]; exact hw)
  have hCr := sec2W_inf_centralizer_eq h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hr hr1
  have hle : X ⊓ sec2W A E y ≤ E ⊓ A := by
    rw [← hCr]
    intro v hv
    refine ⟨hv.2, mem_centralizer_iff.mpr fun z hz => ?_⟩
    rw [Set.mem_singleton_iff.mp hz]
    have h1 := hX _ hxX v hv.1
    have h2 := hWc w hw v hv.2
    calc r * v = w⁻¹ * ((w * r) * v) := by group
      _ = w⁻¹ * (v * (w * r)) := by rw [h1]
      _ = w⁻¹ * ((v * w) * r) := by group
      _ = w⁻¹ * ((w * v) * r) := by rw [h2]
      _ = v * r := by group
  have hprod := card_sup_mul_card_inf_of_le_normalizer_left (X := X) (N := sec2W A E y)
    (hXP.trans hPW)
  have h1 : Nat.card (X ⊔ sec2W A E y : Subgroup G) ≤ 1024 :=
    (card_le_of_le (sup_le hXP hWP)).trans hP.le
  have h2 : Nat.card (X ⊓ sec2W A E y : Subgroup G) ≤ 16 :=
    (card_le_of_le hle).trans (card_inf_left hF hodd).le
  have h3 := Nat.mul_le_mul h1 h2
  rw [hprod, hX256, hW256] at h3
  norm_num at h3

theorem normalizer_sec2P_le_normalizer_sec2W {y : G} (hyA : y ∈ A)
    (hyE : y ∈ normalizer (E : Set G)) (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
    (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) (hW : IsElemAbelian 2 (sec2W A E y)) :
    normalizer (sec2P E : Set G) ≤ normalizer (sec2W A E y : Set G) := fun n hn => by
  obtain ⟨-, -, hWP, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hWc : ∀ x ∈ sec2W A E y, ∀ x' ∈ sec2W A E y, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hW.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  refine AS76b.mem_normalizer_of_map_conj_le (le_of_eq ?_)
  refine eq_sec2W_of_le h11 hE16 hF hL hodd hyA hyE hyU hy3 hW ?_ ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact (mem_normalizer_iff.mp hn w).mp (hWP hw)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc n * a * n⁻¹ * (n * b * n⁻¹) = n * (a * b) * n⁻¹ := by group
      _ = n * (b * a) * n⁻¹ := by rw [hWc a ha b hb]
      _ = n * b * n⁻¹ * (n * a * n⁻¹) := by group
  · rw [card_map_of_injective (fun a b h => by simpa using h),
      card_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3]

theorem mem_of_mem_sec2P_of_mul_self_eq_one {y : G} (hyA : y ∈ A)
    (hyE : y ∈ normalizer (E : Set G)) (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
    (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) (hW : IsElemAbelian 2 (sec2W A E y))
    {x : G} (hx : x ∈ sec2P E) (hxW : x ∉ sec2W A E y) (hx2 : x * x = 1) : x ∈ E := by
  obtain ⟨w, hw, r, hr, rfl⟩ := exists_eq_mul_of_mem_sec2P h11 hE16 hF hL hodd hyA hyE hyU hy3 hx
  have hr1 : r ≠ 1 := fun h => hxW (by rw [h, mul_one]; exact hw)
  have hCr := sec2W_inf_centralizer_eq h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hr hr1
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hW.2 w hw)
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hF.elemR.2 r hr)
  have hwr : w ∈ sec2W A E y ⊓ centralizer ({r} : Set G) := by
    refine ⟨hw, mem_centralizer_iff.mpr fun z hz => ?_⟩
    rw [Set.mem_singleton_iff.mp hz]
    calc r * w = w⁻¹ * ((w * r) * (w * r)) * r⁻¹ := by group
      _ = w⁻¹ * r⁻¹ := by rw [hx2, mul_one]
      _ = w * r := by rw [hwinv, hrinv]
  rw [hCr] at hwr
  exact E.mul_mem hwr.1 (hF.R_le_E hr)

theorem normalizer_sec2P_le_normalizer {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
    (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
    (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) (hW : IsElemAbelian 2 (sec2W A E y)) :
    normalizer (sec2P E : Set G) ≤ normalizer (E : Set G) := fun n hn => by
  have hnW := normalizer_sec2P_le_normalizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hn
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  obtain ⟨-, -, -, hWE, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hEP : E ≤ sec2P E := (isElemQuot_sec2P h11 hE16 hF hL hodd).1
  obtain ⟨r, hr, hr1⟩ := hD.exists_ne_one
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hF.sylowR.le hF.sylowR.isPGroup hodd
  have hrU : r ∉ E ⊓ A := fun h => hr1 (by
    have h1 : r ∈ R ⊓ A := ⟨hr, h.2⟩
    rwa [hRA1, mem_bot] at h1)
  have key : ∀ e ∈ E, e ∉ E ⊓ A → n * e * n⁻¹ ∈ E := fun e he heU => by
    refine mem_of_mem_sec2P_of_mul_self_eq_one h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
      ((mem_normalizer_iff.mp hn e).mp (hEP he)) (fun h => heU ?_) ?_
    · rw [← hWE]
      exact ⟨(mem_normalizer_iff.mp hnW e).mpr h, he⟩
    · have he2 : e * e = 1 := by rw [← sq]; exact hF.elemE.2 e he
      calc n * e * n⁻¹ * (n * e * n⁻¹) = n * (e * e) * n⁻¹ := by group
        _ = 1 := by rw [he2]; group
  refine AS76b.mem_normalizer_of_map_conj_le ?_
  rintro _ ⟨e, he, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  by_cases heU : e ∈ E ⊓ A
  · have herU : e * r ∉ E ⊓ A := fun h => hrU (by
      simpa using (E ⊓ A).mul_mem ((E ⊓ A).inv_mem heU) h)
    have h1 := key (e * r) (E.mul_mem he (hF.R_le_E hr)) herU
    have h2 := key r (hF.R_le_E hr) hrU
    have h3 : n * e * n⁻¹ = (n * (e * r) * n⁻¹) * (n * r * n⁻¹)⁻¹ := by group
    rw [h3]
    exact E.mul_mem h1 (E.inv_mem h2)
  · exact key e he heU

theorem sec2W_structure_of_not_le (hT : ¬ E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E)) :
    ∃ y ∈ A, y ∈ normalizer (E : Set G) ∧ (∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1) ∧
      (∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) ∧ IsElemAbelian 2 (sec2W A E y) ∧
      Nat.card (sec2W A E y) = 256 ∧ sec2W A E y ⊓ E = E ⊓ A ∧ sec2W A E y ⊔ E = sec2P E ∧
      conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E ≤ sec2W A E y ∧
      (∀ r ∈ R, r ≠ 1 → sec2W A E y ⊓ centralizer ({r} : Set G) = E ⊓ A) ∧
      (∀ f ∈ F ⊓ A, f ∉ E →
        sec2W A E y ⊓ centralizer ({f} : Set G) = conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E) ∧
      normalizer (sec2P E : Set G) ≤ normalizer (sec2W A E y : Set G) ⊓ normalizer (E : Set G) := by
  obtain ⟨y, hyA, hyE, hyU, hy3, hW₁, hW⟩ := exists_isElemAbelian_sec2W h11 hE16 hF hL hodd hT
  obtain ⟨-, -, -, hWE, hWEP, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  exact ⟨y, hyA, hyE, hyU, hy3, hW, card_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3, hWE, hWEP,
    hW₁, fun r hr hr1 => sec2W_inf_centralizer_eq h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hr hr1,
    fun f hf hfE =>
      sec2W_inf_centralizer_eq_of_mem h11 hE16 hF hL hodd hT hyA hyE hyU hy3 hW hW₁ hf hfE,
    fun n hn => ⟨normalizer_sec2P_le_normalizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hn,
      normalizer_sec2P_le_normalizer h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hn⟩⟩

end Frame

end CFSG.ComponentClassification.AS81
