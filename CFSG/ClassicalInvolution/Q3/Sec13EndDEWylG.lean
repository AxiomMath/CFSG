module

public import CFSG.ClassicalInvolution.Q3.Sec13EndDEWylE
public import CFSG.ClassicalInvolution.Q3.Sec13EndDEWylF
public import CFSG.ClassicalInvolution.Q3.TL4D1MAGLB

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

@[expose] def IsDewPoint {Ω : Set (Subgroup G)} (S : TwinShift Ω) (b : Lab2)
    (X : Set (Subgroup G)) : Prop :=
  X ⊆ Ω ∧ (∀ K ∈ X, S.shift b K ∈ X) ∧ (∀ K ∈ Ω, (twinSet Ω K ∩ X).ncard = 2) ∧
    ∀ K ∈ X, ∀ L ∈ X, ∀ u v : G, DewPair Ω K L u v → dewStar K L ∈ X

@[expose] def dewPts {Ω : Set (Subgroup G)} (S : TwinShift Ω) (b : Lab2) : Set (Set (Subgroup G)) :=
  {X | IsDewPoint S b X}

@[expose] def dewQb (b m : Lab2) : ZMod 2 := if m = 0 ∨ m = b then 0 else 1

theorem dewQb_add (b m m' : Lab2) (hb : b ≠ 0) :
    dewQb b (m + m') = dewQb b m + dewQb b m' := by
  revert b m m'
  decide

open Classical in
@[expose] noncomputable def dewDefect {Ω : Set (Subgroup G)} (S : TwinShift Ω) (b : Lab2)
    (K L M : Subgroup G) : ZMod 2 :=
  if hm : ∃ m : Lab2, dewStar K L = S.shift m M then dewQb b hm.choose else 0

structure DewPointCoord {Ω : Set (Subgroup G)} (S : TwinShift Ω) (b : Lab2) where
  coord : Set (Subgroup G) → G → ZMod 2
  bijOn : Set.BijOn coord (dewPts S b) (DE2Hyp.deq2Dual Ω)
  qAct : ∀ q ∈ pCore 2 G, ∀ X ∈ dewPts S b,
    coord (conjSub q '' X) = coord X + fun x => dewQb b (S.lam q x)
  gAct : ∀ g : G, ∃ f₀ ∈ DE2Hyp.deq2Dual Ω, ∀ X ∈ dewPts S b,
    coord (conjSub g '' X) = (fun x => coord X (g⁻¹ * x * g)) + f₀
  memberFix : ∀ K ∈ Ω, ∀ X ∈ dewPts S b, K ∈ X → ∀ k ∈ K, coord (conjSub k '' X) = coord X
  memberAct : ∀ K ∈ Ω, ∀ u : G, IsUniqueInvolution K u → ∀ φ ∈ DE2Hyp.deq2Dual Ω, ∀ k ∈ K,
    IsElationOf Ω u φ k → ∀ X ∈ dewPts S b, K ∉ X → coord (conjSub k '' X) = coord X + φ

structure AGLPts {Ω : Set (Subgroup G)} (S : TwinShift Ω) (b : Lab2) where
  lab : Set (Subgroup G) → Fin 8
  σ : G →* Equiv.Perm (Fin 8)
  bijOn : Set.BijOn lab (dewPts S b) Set.univ
  equivariant : ∀ g : G, ∀ X ∈ dewPts S b, lab (conjSub g '' X) = σ g (lab X)
  ker_eq : σ.ker = dewA S b
  range_eq : σ.range = AE.agl32
  plane : ∀ K ∈ Ω, ∃ α ∈ AE.e29Sets, (α : Set (Fin 8)) = lab '' {X | X ∈ dewPts S b ∧ K ∉ X}
  plane_surj : ∀ α ∈ AE.e29Sets, ∃ K ∈ Ω,
    (α : Set (Fin 8)) = lab '' {X | X ∈ dewPts S b ∧ K ∉ X}

theorem dewG_defect_eq {Ω : Set (Subgroup G)} (S : TwinShift Ω) (b : Lab2) {K L M : Subgroup G}
    {m : Lab2}
    (hM : M ∈ Ω) (hm : dewStar K L = S.shift m M) : dewDefect S b K L M = dewQb b m := by
  unfold dewDefect
  have hex : ∃ m' : Lab2, dewStar K L = S.shift m' M := ⟨m, hm⟩
  rw [dif_pos hex]
  have h1 : hex.choose = m := S.shift_injective hM (hex.choose_spec.symm.trans hm)
  rw [h1]

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

theorem lab2_add_self : ∀ m : Lab2, m + m = 0 := by decide

theorem dewQb_eq_zero_iff (b m : Lab2) : dewQb b m = 0 ↔ m = 0 ∨ m = b := by
  unfold dewQb
  split_ifs with hm
  · exact ⟨fun _ => hm, fun _ => rfl⟩
  · exact ⟨fun h1 => absurd h1 one_ne_zero, fun h1 => absurd h1 hm⟩

theorem dewQb_zero (b : Lab2) : dewQb b 0 = 0 := by
  rw [dewQb_eq_zero_iff]
  exact Or.inl rfl

theorem lab2_exists_dewQb_one : ∀ b : Lab2, b ≠ 0 → ∃ m : Lab2, dewQb b m = 1 := by decide

open Classical in
@[expose] noncomputable def dewEps (X Y : Set (Subgroup G)) (x : G) : ZMod 2 :=
  if ∃ L ∈ X, IsUniqueInvolution L x ∧ L ∉ Y then 1 else 0

theorem dewEps_eq_one_iff {X Y : Set (Subgroup G)} {x : G} :
    dewEps X Y x = 1 ↔ ∃ L ∈ X, IsUniqueInvolution L x ∧ L ∉ Y := by
  unfold dewEps
  split_ifs with h1
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 zero_ne_one, fun hn => absurd hn h1⟩

theorem dewEps_eq_zero_iff {X Y : Set (Subgroup G)} {x : G} :
    dewEps X Y x = 0 ↔ ¬ ∃ L ∈ X, IsUniqueInvolution L x ∧ L ∉ Y := by
  unfold dewEps
  split_ifs with h1
  · exact ⟨fun h0 => absurd h0 one_ne_zero, fun hn => absurd h1 hn⟩
  · exact ⟨fun _ => h1, fun _ => rfl⟩

theorem conjSub_eq_self_of_mem_normalizer {k : G} {L : Subgroup G}
    (hk : k ∈ Subgroup.normalizer (L : Set G)) : conjSub k L = L := by
  ext x
  rw [mem_conjSub_iff]
  have := Subgroup.mem_normalizer_iff.mp hk (k⁻¹ * x * k)
  rw [show k * (k⁻¹ * x * k) * k⁻¹ = x by group] at this
  exact this

theorem mem_normalizer_of_conjSub_eq {k : G} {L : Subgroup G} (hk : conjSub k L = L) :
    k ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := (mem_conjSub_iff (n := k) (K := L) (x := k * x * k⁻¹))
  rw [hk, show k⁻¹ * (k * x * k⁻¹) * k = x by group] at h1
  exact h1.symm

theorem mem_conjSub_image_iff {q : G} {X : Set (Subgroup G)} {L : Subgroup G} :
    L ∈ conjSub q '' X ↔ conjSub q⁻¹ L ∈ X := by
  constructor
  · rintro ⟨L', hL', rfl⟩
    rwa [conjSub_inv_conjSub]
  · intro hL
    exact ⟨conjSub q⁻¹ L, hL, conjSub_conjSub_inv q L⟩

theorem conjSub_image_mul (q a : G) (X : Set (Subgroup G)) :
    conjSub (q * a) '' X = conjSub q '' (conjSub a '' X) := by
  simp only [Set.image_image, conjSub_mul]

namespace DE4Hyp

variable {Ω : Set (Subgroup G)} (h : DE4Hyp Ω)
include h

theorem dewDefect_comm (S : TwinShift Ω) (b : Lab2) {K L M : Subgroup G} {u v : G}
    (sp : DewPair Ω K L u v) : dewDefect S b K L M = dewDefect S b L K M := by
  unfold dewDefect
  rw [h.dewStar_comm sp]

theorem dewDefect_swap (S : TwinShift Ω) (b : Lab2) {K L M : Subgroup G} {u v : G}
    (sp : DewPair Ω K L u v) (hM : M ∈ dew1V Ω (u * v)) :
    dewDefect S b K L M = dewDefect S b K M L := by
  have hMΩ : M ∈ Ω := hM.1
  have hJ : dewStar K L ∈ twinSet Ω M := by
    rw [← dew1V_eq_twinSet hMΩ hM.2]
    exact h.dewStar_mem_dew1V sp
  obtain ⟨m, hm, -⟩ := h.exists_unique_shift S hMΩ hJ
  have hne : u ≠ u * v := fun h1 =>
    sp.invL.ne_one (mul_left_cancel (by rw [mul_one]; exact h1.symm))
  have spKM : DewPair Ω K M u (u * v) := ⟨sp.memK, hMΩ, sp.invK, hM.2, hne⟩
  have h2 : dewStar K (S.shift m M) = S.shift m (dewStar K M) := by
    have e := h.dewStar_shift S spKM 0 m
    rwa [S.shift_zero K sp.memK, zero_add] at e
  have hL : L = S.shift m (dewStar K M) := by
    rw [← h.dewStar_dewStar sp, ← hm, h2]
  have hKM : dewStar K M = S.shift m L := by
    rw [hL, S.shift_shift_self m (h.dewStar_mem_dew1V spKM).1]
  rw [dewG_defect_eq S b hMΩ hm.symm, dewG_defect_eq S b sp.memL hKM]

theorem dewDefect_conj (S : TwinShift Ω) (b : Lab2) {K L M : Subgroup G} {u v : G}
    (sp : DewPair Ω K L u v) (hM : M ∈ dew1V Ω (u * v)) (g : G) :
    dewDefect S b (conjSub g K) (conjSub g L) (conjSub g M) = dewDefect S b K L M := by
  have hMΩ : M ∈ Ω := hM.1
  have hJ : dewStar K L ∈ twinSet Ω M := by
    rw [← dew1V_eq_twinSet hMΩ hM.2]
    exact h.dewStar_mem_dew1V sp
  obtain ⟨m, hm, -⟩ := h.exists_unique_shift S hMΩ hJ
  have e1 : dewStar (conjSub g K) (conjSub g L) = S.shift m (conjSub g M) := by
    rw [← h.conjSub_dewStar sp g, ← hm]
    exact (S.shift_conj m g M hMΩ).symm
  rw [dewG_defect_eq S b (S.conj_mem g M hMΩ) e1, dewG_defect_eq S b hMΩ hm.symm]

theorem pt_twin_inter (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {M : Subgroup G} (hM : M ∈ X) :
    twinSet Ω M ∩ X = {M, S.shift b M} := by
  have hMΩ : M ∈ Ω := hX.1 hM
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hMΩ
  have hne : M ≠ S.shift b M := fun e => hb (S.shift_free b M hMΩ e.symm)
  have hsub : ({M, S.shift b M} : Set (Subgroup G)) ⊆ twinSet Ω M ∩ X := by
    intro N hN
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl
    · exact ⟨⟨hMΩ, z, hz, hz⟩, hM⟩
    · exact ⟨S.shift_mem b M hMΩ, hX.2.1 M hM⟩
  have hle : (twinSet Ω M ∩ X).ncard ≤ ({M, S.shift b M} : Set (Subgroup G)).ncard := by
    rw [Set.ncard_pair hne, hX.2.2.1 M hMΩ]
  exact (Set.eq_of_subset_of_ncard_le hsub hle).symm

theorem pt_shift_mem (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {M : Subgroup G} (hM : M ∈ X) (m : Lab2) :
    S.shift m M ∈ X ↔ dewQb b m = 0 := by
  have hMΩ : M ∈ Ω := hX.1 hM
  rw [dewQb_eq_zero_iff]
  constructor
  · intro hmX
    have hmem : S.shift m M ∈ twinSet Ω M ∩ X := ⟨S.shift_mem m M hMΩ, hmX⟩
    rw [h.pt_twin_inter S hb hX hM] at hmem
    rcases hmem with h1 | h1
    · exact Or.inl (S.shift_free m M hMΩ h1)
    · exact Or.inr (S.shift_injective hMΩ h1)
  · rintro (h0 | h0)
    · rw [h0, S.shift_zero M hMΩ]
      exact hM
    · rw [h0]
      exact hX.2.1 M hM

theorem pt_exists_mem (S : TwinShift Ω) {b : Lab2} {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {x : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1) :
    ∃ L ∈ X, IsUniqueInvolution L x := by
  obtain ⟨K, hK⟩ := h.exists_mem_dew1V hx hx1
  have hne : (twinSet Ω K ∩ X).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hX.2.2.1 K hK.1]; norm_num)
  obtain ⟨L, hLtw, hLX⟩ := hne
  obtain ⟨-, z, hKz, hLz⟩ := hLtw
  exact ⟨L, hLX, by rw [← hK.2.eq hKz] at hLz; exact hLz⟩

theorem pt_eq_of_subset (S : TwinShift Ω) {b : Lab2} {X Y : Set (Subgroup G)}
    (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) (hXY : X ⊆ Y) : X = Y := by
  ext M
  refine ⟨fun hM => hXY hM, fun hMY => ?_⟩
  have hMΩ : M ∈ Ω := hY.1 hMY
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hMΩ
  have hfin : (twinSet Ω M ∩ Y).Finite := Set.toFinite _
  have hsub : twinSet Ω M ∩ X ⊆ twinSet Ω M ∩ Y := Set.inter_subset_inter_right _ hXY
  have hle : (twinSet Ω M ∩ Y).ncard ≤ (twinSet Ω M ∩ X).ncard := by
    rw [hX.2.2.1 M hMΩ, hY.2.2.1 M hMΩ]
  have heq := Set.eq_of_subset_of_ncard_le hsub hle hfin
  have hMt : M ∈ twinSet Ω M ∩ Y := ⟨⟨hMΩ, z, hz, hz⟩, hMY⟩
  rw [← heq] at hMt
  exact hMt.2

theorem mem_iff_dewEps (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) {K : Subgroup G} {x : G} (hK : K ∈ X)
    (hKx : IsUniqueInvolution K x) : K ∈ Y ↔ dewEps X Y x = 0 := by
  rw [dewEps_eq_zero_iff]
  constructor
  · rintro hKY ⟨L, hLX, hLx, hLY⟩
    have hL : L ∈ twinSet Ω K ∩ X := ⟨⟨hX.1 hLX, x, hKx, hLx⟩, hLX⟩
    rw [h.pt_twin_inter S hb hX hK] at hL
    rcases hL with rfl | rfl
    · exact hLY hKY
    · exact hLY (hY.2.1 K hKY)
  · intro hn
    by_contra hKY
    exact hn ⟨K, hK, hKx, hKY⟩

theorem exists_label (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) {K : Subgroup G} {x : G} (hK : K ∈ X)
    (hKx : IsUniqueInvolution K x) :
    ∃ m : Lab2, S.shift m K ∈ Y ∧ dewQb b m = dewEps X Y x := by
  have hKΩ : K ∈ Ω := hX.1 hK
  have hxD : x ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hKΩ hKx
  rcases zmod2_cases (dewEps X Y x) with hε | hε
  · refine ⟨0, ?_, ?_⟩
    · rw [S.shift_zero K hKΩ]
      exact (h.mem_iff_dewEps S hb hX hY hK hKx).mpr hε
    · rw [hε, dewQb_zero]
  · obtain ⟨N, hNY, hNx⟩ := h.pt_exists_mem S hY hxD hKx.ne_one
    have hNtw : N ∈ twinSet Ω K := ⟨hY.1 hNY, x, hKx, hNx⟩
    obtain ⟨m, hm, -⟩ := h.exists_unique_shift S hKΩ hNtw
    have hNX : N ∉ X := fun hNX => by
      have := (h.mem_iff_dewEps S hb hX hY hNX hNx).mp hNY
      rw [hε] at this
      exact one_ne_zero this
    refine ⟨m, by rw [hm]; exact hNY, ?_⟩
    rw [hε]
    rcases zmod2_cases (dewQb b m) with h0 | h1
    · exfalso
      apply hNX
      rw [← hm]
      exact (h.pt_shift_mem S hb hX hK m).mpr h0
    · exact h1

theorem mem_iff_of_dewEps_eq_one (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) {x : G} (hε : dewEps X Y x = 1)
    {y : Subgroup G} (hy : y ∈ Ω) (hyx : IsUniqueInvolution y x) : y ∈ X ↔ y ∉ Y := by
  obtain ⟨L, hLX, hLx, -⟩ := dewEps_eq_one_iff.mp hε
  have hLΩ : L ∈ Ω := hX.1 hLX
  have hxD : x ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hy hyx
  constructor
  · intro hyX hyY
    have h0 := (h.mem_iff_dewEps S hb hX hY hyX hyx).mp hyY
    rw [hε] at h0
    exact one_ne_zero h0
  · intro hyY
    by_contra hyX
    apply hyY
    obtain ⟨m, hm, -⟩ := h.exists_unique_shift S hLΩ (show y ∈ twinSet Ω L from ⟨hy, x, hLx, hyx⟩)
    have hm1 : dewQb b m = 1 := by
      rcases zmod2_cases (dewQb b m) with h0 | h1
      · exfalso
        apply hyX
        rw [← hm]
        exact (h.pt_shift_mem S hb hX hLX m).mpr h0
      · exact h1
    obtain ⟨N, hNY, hNx⟩ := h.pt_exists_mem S hY hxD hyx.ne_one
    have hNtw : N ∈ twinSet Ω L := ⟨hY.1 hNY, x, hLx, hNx⟩
    obtain ⟨m', hm', -⟩ := h.exists_unique_shift S hLΩ hNtw
    have hm'1 : dewQb b m' = 1 := by
      rcases zmod2_cases (dewQb b m') with h0 | h1
      · exfalso
        have hNX : N ∈ X := by
          rw [← hm']
          exact (h.pt_shift_mem S hb hX hLX m').mpr h0
        have h2 := (h.mem_iff_dewEps S hb hX hY hNX hNx).mp hNY
        rw [hε] at h2
        exact one_ne_zero h2
      · exact h1
    have hyN : S.shift (m + m') N = y := by
      rw [← hm', ← S.shift_add (m + m') m' L hLΩ, add_assoc, lab2_add_self, add_zero, hm]
    rw [← hyN]
    apply (h.pt_shift_mem S hb hY hNY (m + m')).mpr
    rw [dewQb_add b m m' hb, hm1, hm'1]
    decide

theorem dewEps_mul (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) {x y : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1)
    (hy : y ∈ zGroup Ω) (hy1 : y ≠ 1) (hxy : x ≠ y) :
    dewEps X Y (x * y) = dewEps X Y x + dewEps X Y y := by
  obtain ⟨K, hKX, hKx⟩ := h.pt_exists_mem S hX hx hx1
  obtain ⟨L, hLX, hLy⟩ := h.pt_exists_mem S hX hy hy1
  obtain ⟨mx, hKY, hmx⟩ := h.exists_label S hb hX hY hKX hKx
  obtain ⟨my, hLY, hmy⟩ := h.exists_label S hb hX hY hLX hLy
  have hKΩ : K ∈ Ω := hX.1 hKX
  have hLΩ : L ∈ Ω := hX.1 hLX
  have spKL : DewPair Ω K L x y := ⟨hKΩ, hLΩ, hKx, hLy, hxy⟩
  have hMX : dewStar K L ∈ X := hX.2.2.2 K hKX L hLX x y spKL
  have hMΩ : dewStar K L ∈ Ω := (h.dewStar_mem_dew1V spKL).1
  have hMinv : IsUniqueInvolution (dewStar K L) (x * y) := (h.dewStar_mem_dew1V spKL).2
  have hKLY : S.shift (mx + my) (dewStar K L) ∈ Y := by
    rw [← h.dewStar_shift S spKL mx my]
    exact hY.2.2.2 _ hKY _ hLY x y (h.dewPair_shift S spKL mx my)
  have hMiff : dewStar K L ∈ Y ↔ dewQb b (mx + my) = 0 := by
    constructor
    · intro hMY
      exact (h.pt_shift_mem S hb hY hMY (mx + my)).mp hKLY
    · intro h0
      rcases (dewQb_eq_zero_iff b (mx + my)).mp h0 with hn | hn
      · rw [hn, S.shift_zero _ hMΩ] at hKLY
        exact hKLY
      · rw [hn] at hKLY
        have h2 := hY.2.1 _ hKLY
        rwa [S.shift_shift_self b hMΩ] at h2
  have hε : dewEps X Y (x * y) = 0 ↔ dewStar K L ∈ Y :=
    (h.mem_iff_dewEps S hb hX hY hMX hMinv).symm
  rw [dewQb_add b mx my hb, hmx, hmy] at hMiff
  have key : ∀ a c : ZMod 2, (a = 0 ↔ c = 0) → a = c := by decide
  exact key _ _ (hε.trans hMiff)

theorem dewEps_mem_dual (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) :
    dewEps X Y ∈ DE2Hyp.deq2Dual Ω := by
  have h1 : dewEps X Y 1 = 0 := by
    rw [dewEps_eq_zero_iff]
    rintro ⟨L, -, hL, -⟩
    exact hL.ne_one rfl
  refine ⟨h1, fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [dewEps_eq_zero_iff]
    rintro ⟨L, hLX, hL, -⟩
    exact hx (dew1_involution_mem h.toDEHyp (hX.1 hLX) hL)
  · rcases eq_or_ne x 1 with rfl | hx1
    · rw [one_mul, h1, zero_add]
    rcases eq_or_ne y 1 with rfl | hy1
    · rw [mul_one, h1, add_zero]
    rcases eq_or_ne x y with rfl | hxy
    · rw [h.zGroup_mul_self x hx, h1, zmod2_add_self]
    · exact h.dewEps_mul S hb hX hY hx hx1 hy hy1 hxy

theorem dewStar_not_mem (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {K L : Subgroup G} {u v : G} (hKX : K ∉ X) (sp : DewPair Ω K L u v)
    (hL : L ∈ X) : dewStar K L ∉ X := by
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp sp.memK sp.invK
  obtain ⟨K', hK'X, hK'u⟩ := h.pt_exists_mem S hX huD sp.invK.ne_one
  have hK'Ω : K' ∈ Ω := hX.1 hK'X
  have hKtw : K ∈ twinSet Ω K' := ⟨sp.memK, u, hK'u, sp.invK⟩
  obtain ⟨m, hm, -⟩ := h.exists_unique_shift S hK'Ω hKtw
  have hm1 : dewQb b m = 1 := by
    rcases zmod2_cases (dewQb b m) with h0 | h1
    · exfalso
      apply hKX
      rw [← hm]
      exact (h.pt_shift_mem S hb hX hK'X m).mpr h0
    · exact h1
  have spK'L : DewPair Ω K' L u v := ⟨hK'Ω, sp.memL, hK'u, sp.invL, sp.ne⟩
  have hdew : dewStar K L = S.shift m (dewStar K' L) := by
    have e := h.dewStar_shift S spK'L m 0
    rw [S.shift_zero L sp.memL, add_zero, hm] at e
    exact e
  have hM' : dewStar K' L ∈ X := hX.2.2.2 K' hK'X L hL u v spK'L
  intro hKL
  rw [hdew] at hKL
  have h2 := (h.pt_shift_mem S hb hX hM' m).mp hKL
  rw [hm1] at h2
  exact one_ne_zero h2

theorem conjSub_eq_of_mem_of_not_mem (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    {X : Set (Subgroup G)} (hX : IsDewPoint S b X) {K : Subgroup G} {u : G} (hK : K ∈ Ω)
    (hKu : IsUniqueInvolution K u) (hKX : K ∉ X) {k : G} (hk : k ∈ K) {L : Subgroup G}
    (hL : L ∈ X) {v : G} (hLv : IsUniqueInvolution L v) (hc : conjSub k L ∈ X) :
    conjSub k L = L := by
  by_cases huv : u = v
  · subst huv
    exact conjSub_eq_self_of_mem_normalizer ((h.le_normalizer_of_dew1V hK hKu ⟨hX.1 hL, hLv⟩) hk)
  · have sp : DewPair Ω K L u v := ⟨hK, hX.1 hL, hKu, hLv, huv⟩
    rcases h.conjSub_eq_or_dewStar sp hk with h1 | h1
    · exact h1
    · rw [h1] at hc
      exact absurd hc (h.dewStar_not_mem S hb hX hKX sp hL)

omit h in
theorem dchoice_conj_pow (g x : G) (i j : ℕ) :
    g ^ i * (g ^ j * x * (g ^ j)⁻¹) * (g ^ i)⁻¹ = g ^ (i + j) * x * (g ^ (i + j))⁻¹ := by
  rw [pow_add]
  group

omit h in
theorem dchoice_free {g x₀ y : G} (hg : orderOf g = 7) (hy : y ∈ zGroup Ω) (hy1 : y ≠ 1)
    (hyx : y ≠ x₀) (hsurj : ∀ z ∈ zGroup Ω, z ≠ 1 → ∃ i : ℕ, g ^ i * x₀ * (g ^ i)⁻¹ = z)
    (i j : ℕ) (hij : g ^ i * x₀ * (g ^ i)⁻¹ = g ^ j * x₀ * (g ^ j)⁻¹) : g ^ i = g ^ j := by
  by_contra hne
  have hw1 : (g ^ j)⁻¹ * g ^ i ≠ 1 := fun h1 => hne (inv_mul_eq_one.mp h1).symm
  have hcomm : (g ^ j)⁻¹ * g ^ i * x₀ = x₀ * ((g ^ j)⁻¹ * g ^ i) := by
    have e : g ^ i * x₀ = g ^ j * x₀ * (g ^ j)⁻¹ * g ^ i := by
      rw [← hij, inv_mul_cancel_right]
    rw [mul_assoc, e]
    group
  have hwmem : (g ^ j)⁻¹ * g ^ i ∈ Subgroup.zpowers g :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) j))
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) i)
  have hord : orderOf ((g ^ j)⁻¹ * g ^ i) = 7 := by
    have hdvd := orderOf_dvd_of_mem_zpowers hwmem
    rw [hg] at hdvd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hw1
    · exact h1
  have hle : Subgroup.zpowers ((g ^ j)⁻¹ * g ^ i) ≤ Subgroup.zpowers g :=
    Subgroup.zpowers_le.mpr hwmem
  have hcard : Nat.card (Subgroup.zpowers g) ≤
      Nat.card (Subgroup.zpowers ((g ^ j)⁻¹ * g ^ i)) :=
    le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hg, hord])
  have heq : Subgroup.zpowers ((g ^ j)⁻¹ * g ^ i) = Subgroup.zpowers g :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  have hgw : g ∈ Subgroup.zpowers ((g ^ j)⁻¹ * g ^ i) := by
    rw [heq]
    exact Subgroup.mem_zpowers g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgw
  have hgc : Commute g x₀ := by
    rw [← hk]
    exact (show Commute ((g ^ j)⁻¹ * g ^ i) x₀ from hcomm).zpow_left k
  obtain ⟨i', hi'⟩ := hsurj y hy hy1
  apply hyx
  rw [← hi']
  have hc : g ^ i' * x₀ = x₀ * g ^ i' := (hgc.pow_left i' : Commute (g ^ i') x₀)
  rw [hc, mul_inv_cancel_right]

omit h in
theorem dchoice_pair {c : G → Subgroup G} (hc : ∀ x ∈ zGroup Ω, x ≠ 1 → c x ∈ dew1V Ω x)
    {u v : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) (hv : v ∈ zGroup Ω) (hv1 : v ≠ 1)
    (huv : u ≠ v) : DewPair Ω (c u) (c v) u v :=
  ⟨(hc u hu hu1).1, (hc v hv hv1).1, (hc u hu hu1).2, (hc v hv hv1).2, huv⟩

omit h in
theorem dchoice_mem_add (b x y : Lab2) (hx : x = 0 ∨ x = b) (hy : y = 0 ∨ y = b) :
    x + y = 0 ∨ x + y = b := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
  · exact Or.inl (zero_add 0)
  · exact Or.inr (zero_add b)
  · exact Or.inr (add_zero b)
  · exact Or.inl (lab2_add_self b)

omit h in
theorem dchoice_sum3 (b e e' n : Lab2) (he : e = 0 ∨ e = b) (he' : e' = 0 ∨ e' = b)
    (hn : n = 0 ∨ n = b) : e + e' + n = 0 ∨ e + e' + n = b :=
  dchoice_mem_add b (e + e') n (dchoice_mem_add b e e' he he') hn

theorem dchoice_mul_ne_one {u v : G} (hv : v ∈ zGroup Ω) (huv : u ≠ v) : u * v ≠ 1 := by
  intro e
  apply huv
  rw [eq_inv_of_mul_eq_one_left e, inv_eq_of_mul_eq_one_right (h.zGroup_mul_self v hv)]

omit h in
theorem dchoice_equiv {c : G → Subgroup G} {g x₀ : G} {K₀ : Subgroup G}
    (hcψ : ∀ i : ℕ, c (g ^ i * x₀ * (g ^ i)⁻¹) = conjSub (g ^ i) K₀)
    (hsurj : ∀ z ∈ zGroup Ω, z ≠ 1 → ∃ i : ℕ, g ^ i * x₀ * (g ^ i)⁻¹ = z) (i : ℕ) :
    ∀ u ∈ zGroup Ω, u ≠ 1 → c (g ^ i * u * (g ^ i)⁻¹) = conjSub (g ^ i) (c u) := by
  intro u hu hu1
  obtain ⟨j, rfl⟩ := hsurj u hu hu1
  rw [dchoice_conj_pow, hcψ, hcψ, ← conjSub_mul, ← pow_add]

theorem dchoice_mem {c : G → Subgroup G} {g x₀ : G} {K₀ : Subgroup G} (hK₀Ω : K₀ ∈ Ω)
    (hK₀ : IsUniqueInvolution K₀ x₀)
    (hcψ : ∀ i : ℕ, c (g ^ i * x₀ * (g ^ i)⁻¹) = conjSub (g ^ i) K₀)
    (hsurj : ∀ z ∈ zGroup Ω, z ≠ 1 → ∃ i : ℕ, g ^ i * x₀ * (g ^ i)⁻¹ = z) :
    ∀ x ∈ zGroup Ω, x ≠ 1 → c x ∈ dew1V Ω x := by
  intro x hx hx1
  obtain ⟨i, rfl⟩ := hsurj x hx hx1
  rw [hcψ i]
  exact ⟨h.hyp.conjInvariant _ K₀ hK₀Ω, hK₀.conj _⟩

omit h in
theorem dchoice_shift_inv (S : TwinShift Ω) {x : G} {K : Subgroup G}
    (hK : IsUniqueInvolution K x) (hKΩ : K ∈ Ω) (k : Lab2) :
    IsUniqueInvolution (S.shift k K) x := by
  obtain ⟨-, w, hw, hkw⟩ := S.shift_mem k K hKΩ
  rw [hK.eq hw]
  exact hkw

theorem dchoice_swap (S : TwinShift Ω) (b : Lab2) {c : G → Subgroup G}
    (hc : ∀ x ∈ zGroup Ω, x ≠ 1 → c x ∈ dew1V Ω x) {u v : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1)
    (hv : v ∈ zGroup Ω) (hv1 : v ≠ 1) (huv : u ≠ v) :
    dewDefect S b (c u) (c (u * v)) (c v) = dewDefect S b (c u) (c v) (c (u * v)) :=
  (h.dewDefect_swap S b (dchoice_pair hc hu hu1 hv hv1 huv)
    (hc (u * v) ((zGroup Ω).mul_mem hu hv) (h.dchoice_mul_ne_one hv huv))).symm

theorem dchoice_symm (S : TwinShift Ω) (b : Lab2) {c : G → Subgroup G}
    (hc : ∀ x ∈ zGroup Ω, x ≠ 1 → c x ∈ dew1V Ω x) {u v : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1)
    (hv : v ∈ zGroup Ω) (hv1 : v ≠ 1) (huv : u ≠ v) :
    dewDefect S b (c u) (c v) (c (u * v)) = dewDefect S b (c v) (c u) (c (v * u)) := by
  rw [h.zGroup_comm v hv u hu]
  exact h.dewDefect_comm S b (dchoice_pair hc hu hu1 hv hv1 huv)

theorem dchoice_shift3 (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K L M : Subgroup G} {u v : G}
    (sp : DewPair Ω K L u v) (hM : M ∈ dew1V Ω (u * v)) (m m' m'' : Lab2) :
    dewDefect S b (S.shift m K) (S.shift m' L) (S.shift m'' M) =
      dewDefect S b K L M + dewQb b m + dewQb b m' + dewQb b m'' := by
  have hMΩ : M ∈ Ω := hM.1
  have hJ : dewStar K L ∈ twinSet Ω M := by
    rw [← dew1V_eq_twinSet hMΩ hM.2]
    exact h.dewStar_mem_dew1V sp
  obtain ⟨n, hn, -⟩ := h.exists_unique_shift S hMΩ hJ
  have hdew : dewStar (S.shift m K) (S.shift m' L) =
      S.shift (m + m' + n + m'') (S.shift m'' M) := by
    rw [h.dewStar_shift S sp m m', ← hn, ← S.shift_add (m + m') n M hMΩ,
      ← S.shift_add (m + m' + n + m'') m'' M hMΩ, add_assoc (m + m' + n) m'' m'',
      lab2_add_self, add_zero]
  have h1 := dewG_defect_eq S b (S.shift_mem m'' M hMΩ).1 hdew
  have h2 := dewG_defect_eq S b hMΩ hn.symm
  rw [h1, h2, dewQb_add b _ _ hb, dewQb_add b _ _ hb, dewQb_add b _ _ hb]
  ring

theorem dchoice_nine (S : TwinShift Ω) (b : Lab2) {c : G → Subgroup G} {u₀ v₀ A B : G}
    (hc : ∀ x ∈ zGroup Ω, x ≠ 1 → c x ∈ dew1V Ω x)
    (hu₀ : u₀ ∈ zGroup Ω) (hu₀1 : u₀ ≠ 1) (hv₀ : v₀ ∈ zGroup Ω) (hv₀1 : v₀ ≠ 1)
    (huv₀ : u₀ ≠ v₀) (hAB : A ≠ B) (hAmem : A = u₀ ∨ A = v₀ ∨ A = u₀ * v₀)
    (hBmem : B = u₀ ∨ B = v₀ ∨ B = u₀ * v₀) :
    dewDefect S b (c A) (c B) (c (A * B)) = dewDefect S b (c u₀) (c v₀) (c (u₀ * v₀)) := by
  have hC : u₀ * v₀ ∈ zGroup Ω := (zGroup Ω).mul_mem hu₀ hv₀
  have hC1 : u₀ * v₀ ≠ 1 := h.dchoice_mul_ne_one hv₀ huv₀
  have e0 : u₀ * (u₀ * v₀) = v₀ := by
    rw [← mul_assoc, h.zGroup_mul_self u₀ hu₀, one_mul]
  have e1 : v₀ * (u₀ * v₀) = u₀ := by
    rw [h.zGroup_comm u₀ hu₀ v₀ hv₀, ← mul_assoc, h.zGroup_mul_self v₀ hv₀, one_mul]
  have hne2 : u₀ ≠ u₀ * v₀ := fun e => hv₀1 (mul_left_cancel (e.symm.trans (mul_one u₀).symm))
  have hne3 : v₀ ≠ u₀ * v₀ := fun e => hu₀1 (mul_right_cancel (e.symm.trans (one_mul v₀).symm))
  have k3 : dewDefect S b (c u₀) (c (u₀ * v₀)) (c (u₀ * (u₀ * v₀))) =
      dewDefect S b (c u₀) (c v₀) (c (u₀ * v₀)) := by
    rw [e0]
    exact h.dchoice_swap S b hc hu₀ hu₀1 hv₀ hv₀1 huv₀
  have k6 : dewDefect S b (c v₀) (c (u₀ * v₀)) (c (v₀ * (u₀ * v₀))) =
      dewDefect S b (c u₀) (c v₀) (c (u₀ * v₀)) := by
    rw [e1, h.zGroup_comm u₀ hu₀ v₀ hv₀, h.dchoice_swap S b hc hv₀ hv₀1 hu₀ hu₀1 huv₀.symm]
    exact (h.dewDefect_comm S b (dchoice_pair hc hu₀ hu₀1 hv₀ hv₀1 huv₀)).symm
  rcases hAmem with hA' | hA' | hA' <;> rcases hBmem with hB' | hB' | hB'
  · exact absurd (hA'.trans hB'.symm) hAB
  · rw [hA', hB']
  · rw [hA', hB']
    exact k3
  · rw [hA', hB']
    exact (h.dchoice_symm S b hc hu₀ hu₀1 hv₀ hv₀1 huv₀).symm
  · exact absurd (hA'.trans hB'.symm) hAB
  · rw [hA', hB']
    exact k6
  · rw [hA', hB']
    exact (h.dchoice_symm S b hc hu₀ hu₀1 hC hC1 hne2).symm.trans k3
  · rw [hA', hB']
    exact (h.dchoice_symm S b hc hv₀ hv₀1 hC hC1 hne3).symm.trans k6
  · exact absurd (hA'.trans hB'.symm) hAB

theorem dchoice_inv (S : TwinShift Ω) (b : Lab2) {c : G → Subgroup G} {g : G}
    (hc : ∀ x ∈ zGroup Ω, x ≠ 1 → c x ∈ dew1V Ω x)
    (hequiv : ∀ i : ℕ, ∀ u ∈ zGroup Ω, u ≠ 1 →
      c (g ^ i * u * (g ^ i)⁻¹) = conjSub (g ^ i) (c u))
    (i : ℕ) {u v : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) (hv : v ∈ zGroup Ω) (hv1 : v ≠ 1)
    (huv : u ≠ v) :
    dewDefect S b (c (g ^ i * u * (g ^ i)⁻¹)) (c (g ^ i * v * (g ^ i)⁻¹))
        (c (g ^ i * u * (g ^ i)⁻¹ * (g ^ i * v * (g ^ i)⁻¹))) =
      dewDefect S b (c u) (c v) (c (u * v)) := by
  have huvD : u * v ∈ zGroup Ω := (zGroup Ω).mul_mem hu hv
  have huv1 : u * v ≠ 1 := h.dchoice_mul_ne_one hv huv
  have e : g ^ i * u * (g ^ i)⁻¹ * (g ^ i * v * (g ^ i)⁻¹) =
      g ^ i * (u * v) * (g ^ i)⁻¹ := by
    group
  rw [e, hequiv i u hu hu1, hequiv i v hv hv1, hequiv i (u * v) huvD huv1]
  exact h.dewDefect_conj S b (dchoice_pair hc hu hu1 hv hv1 huv) (hc (u * v) huvD huv1) (g ^ i)

theorem exists_choice_const_defect (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) :
    ∃ (c : G → Subgroup G) (κ₀ : ZMod 2), (∀ x ∈ zGroup Ω, x ≠ 1 → c x ∈ dew1V Ω x) ∧
      ∀ u ∈ zGroup Ω, ∀ v ∈ zGroup Ω, u ≠ 1 → v ≠ 1 → u ≠ v →
        dewDefect S b (c u) (c v) (c (u * v)) = κ₀ := by
  obtain ⟨g, hg7, hT2, hT3⟩ := h.exists_order_seven
  obtain ⟨e, he⟩ := h.exists_basis
  have hx₀ : e 0 ∈ zGroup Ω := he.mem 0
  have hx₀1 : e 0 ≠ 1 := he.ne0
  have hy : e 1 ∈ zGroup Ω := he.mem 1
  have hy1 : e 1 ≠ 1 := he.ne1.1
  have hyx : e 1 ≠ e 0 := he.ne1.2
  obtain ⟨K₀, hK₀⟩ := h.exists_mem_dew1V hx₀ hx₀1
  have hsurj : ∀ z ∈ zGroup Ω, z ≠ 1 → ∃ i : ℕ, g ^ i * e 0 * (g ^ i)⁻¹ = z :=
    fun z hz hz1 => hT2 (e 0) hx₀ hx₀1 z hz hz1
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ → G, ∀ i, ψ i = g ^ i * e 0 * (g ^ i)⁻¹ :=
    ⟨fun i => g ^ i * e 0 * (g ^ i)⁻¹, fun i => rfl⟩
  have hfreeψ : ∀ i j : ℕ, ψ i = ψ j → g ^ i = g ^ j := by
    intro i j hij
    rw [hψ i, hψ j] at hij
    exact dchoice_free hg7 hy hy1 hyx hsurj i j hij
  obtain ⟨c, hcdef⟩ : ∃ c : G → Subgroup G,
      ∀ x, c x = conjSub (g ^ Function.invFun ψ x) K₀ :=
    ⟨fun x => conjSub (g ^ Function.invFun ψ x) K₀, fun x => rfl⟩
  have hcψ : ∀ i : ℕ, c (g ^ i * e 0 * (g ^ i)⁻¹) = conjSub (g ^ i) K₀ := by
    intro i
    have hpsi : ψ (Function.invFun ψ (ψ i)) = ψ i := Function.invFun_eq ⟨i, rfl⟩
    rw [← hψ i, hcdef, hfreeψ _ _ hpsi]
  have hcmem : ∀ x ∈ zGroup Ω, x ≠ 1 → c x ∈ dew1V Ω x :=
    h.dchoice_mem hK₀.1 hK₀.2 hcψ hsurj
  have hequiv : ∀ i : ℕ, ∀ u ∈ zGroup Ω, u ≠ 1 →
      c (g ^ i * u * (g ^ i)⁻¹) = conjSub (g ^ i) (c u) :=
    fun i => dchoice_equiv hcψ hsurj i
  refine ⟨c, dewDefect S b (c (e 0)) (c (e 1)) (c (e 0 * e 1)), hcmem, ?_⟩
  intro u hu v hv hu1 hv1 huv
  obtain ⟨i, hset⟩ := hT3 u hu v hv hu1 hv1 huv (e 0) hx₀ (e 1) hy hx₀1 hy1 hyx.symm
  have hA : g ^ i * u * (g ^ i)⁻¹ ∈ ({e 0, e 1, e 0 * e 1} : Set G) := by
    rw [← hset]
    exact Set.mem_insert _ _
  have hB : g ^ i * v * (g ^ i)⁻¹ ∈ ({e 0, e 1, e 0 * e 1} : Set G) := by
    rw [← hset]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
  have hAB : g ^ i * u * (g ^ i)⁻¹ ≠ g ^ i * v * (g ^ i)⁻¹ := by
    intro e'
    apply huv
    calc u = (g ^ i)⁻¹ * (g ^ i * u * (g ^ i)⁻¹) * g ^ i := by group
      _ = (g ^ i)⁻¹ * (g ^ i * v * (g ^ i)⁻¹) * g ^ i := by rw [e']
      _ = v := by group
  exact (h.dchoice_inv S b hcmem hequiv i hu hu1 hv hv1 huv).symm.trans
    (h.dchoice_nine S b hcmem hx₀ hx₀1 hy hy1 hyx.symm hAB hA hB)

theorem exists_dewPoint (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) :
    ∃ X, IsDewPoint S b X := by
  obtain ⟨c, κ₀, hc1, hc2⟩ := h.exists_choice_const_defect S hb
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : Lab2, dewQb b m₁ = κ₀ := by
    rcases zmod2_cases κ₀ with h0 | h0
    · exact ⟨0, by rw [dewQb_zero, h0]⟩
    · obtain ⟨m, hm⟩ := lab2_exists_dewQb_one b hb
      exact ⟨m, by rw [hm, h0]⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : G → Subgroup G, ∀ x, cc x = S.shift m₁ (c x) :=
    ⟨fun x => S.shift m₁ (c x), fun x => rfl⟩
  have hccmem : ∀ x ∈ zGroup Ω, x ≠ 1 → cc x ∈ dew1V Ω x := by
    intro x hx hx1
    have hcx := hc1 x hx hx1
    rw [hcc x, dew1V_eq_twinSet hcx.1 hcx.2]
    exact S.shift_mem m₁ (c x) hcx.1
  have hccdef : ∀ u ∈ zGroup Ω, ∀ v ∈ zGroup Ω, u ≠ 1 → v ≠ 1 → u ≠ v →
      dewDefect S b (cc u) (cc v) (cc (u * v)) = 0 := by
    intro u hu v hv hu1 hv1 huv
    have huvD : u * v ∈ zGroup Ω := (zGroup Ω).mul_mem hu hv
    have huv1 : u * v ≠ 1 := h.dchoice_mul_ne_one hv huv
    rw [hcc u, hcc v, hcc (u * v),
      h.dchoice_shift3 S hb (dchoice_pair hc1 hu hu1 hv hv1 huv) (hc1 (u * v) huvD huv1)
        m₁ m₁ m₁,
      hc2 u hu v hv hu1 hv1 huv, hm₁]
    rw [show κ₀ + κ₀ + κ₀ + κ₀ = (κ₀ + κ₀) + (κ₀ + κ₀) by ring, zmod2_add_self]
  obtain ⟨X, hX⟩ : ∃ X : Set (Subgroup G), ∀ K, K ∈ X ↔
      ∃ x ∈ zGroup Ω, x ≠ 1 ∧ ∃ k : Lab2, (k = 0 ∨ k = b) ∧ K = S.shift k (cc x) :=
    ⟨{K | ∃ x ∈ zGroup Ω, x ≠ 1 ∧ ∃ k : Lab2, (k = 0 ∨ k = b) ∧ K = S.shift k (cc x)},
      fun K => Iff.rfl⟩
  refine ⟨X, ?_⟩
  unfold IsDewPoint
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨x, hx, hx1, k, -, rfl⟩ := (hX K).1 hK
    exact (S.shift_mem k (cc x) (hccmem x hx hx1).1).1
  · intro K hK
    obtain ⟨x, hx, hx1, k, hk, rfl⟩ := (hX K).1 hK
    refine (hX _).2 ⟨x, hx, hx1, b + k, ?_, (S.shift_add b k (cc x) (hccmem x hx hx1).1).symm⟩
    rcases hk with hk | hk
    · exact Or.inr (by rw [hk, add_zero])
    · exact Or.inl (by rw [hk, lab2_add_self])
  · intro K hK
    obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hK
    have hzD : z ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hz
    have hz1 : z ≠ 1 := hz.ne_one
    have hcz := hccmem z hzD hz1
    have htw : twinSet Ω K = dew1V Ω z := (dew1V_eq_twinSet hK hz).symm
    have hne : S.shift 0 (cc z) ≠ S.shift b (cc z) := by
      intro e
      rw [S.shift_zero _ hcz.1] at e
      exact hb (S.shift_free b (cc z) hcz.1 e.symm)
    have hset : twinSet Ω K ∩ X = {S.shift 0 (cc z), S.shift b (cc z)} := by
      ext J
      constructor
      · rintro ⟨hJtw, hJX⟩
        obtain ⟨x, hx, hx1, k, hk, rfl⟩ := (hX _).1 hJX
        rw [htw] at hJtw
        have hxz : x = z :=
          (dchoice_shift_inv S (hccmem x hx hx1).2 (hccmem x hx hx1).1 k).eq hJtw.2
        rcases hk with hk | hk
        · rw [hxz, hk]
          exact Set.mem_insert _ _
        · rw [hxz, hk]
          exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      · intro hJ
        rcases hJ with rfl | rfl
        · refine ⟨?_, (hX _).2 ⟨z, hzD, hz1, 0, Or.inl rfl, rfl⟩⟩
          rw [htw]
          exact ⟨(S.shift_mem 0 (cc z) hcz.1).1, dchoice_shift_inv S hcz.2 hcz.1 0⟩
        · refine ⟨?_, (hX _).2 ⟨z, hzD, hz1, b, Or.inr rfl, rfl⟩⟩
          rw [htw]
          exact ⟨(S.shift_mem b (cc z) hcz.1).1, dchoice_shift_inv S hcz.2 hcz.1 b⟩
    rw [hset, Set.ncard_pair hne]
  · intro K hK L hL u v sp
    obtain ⟨x, hx, hx1, ε, hε, rfl⟩ := (hX _).1 hK
    obtain ⟨y, hy, hy1, ε', hε', rfl⟩ := (hX _).1 hL
    have hxu : x = u :=
      (dchoice_shift_inv S (hccmem x hx hx1).2 (hccmem x hx hx1).1 ε).eq sp.invK
    have hyv : y = v :=
      (dchoice_shift_inv S (hccmem y hy hy1).2 (hccmem y hy hy1).1 ε').eq sp.invL
    rw [← hxu, ← hyv] at sp
    have sp0 : DewPair Ω (cc x) (cc y) x y :=
      ⟨(hccmem x hx hx1).1, (hccmem y hy hy1).1, (hccmem x hx hx1).2, (hccmem y hy hy1).2, sp.ne⟩
    have hxyD : x * y ∈ zGroup Ω := (zGroup Ω).mul_mem hx hy
    have hxy1 : x * y ≠ 1 := h.dchoice_mul_ne_one hy sp.ne
    have hMmem : dewStar (cc x) (cc y) ∈ twinSet Ω (cc (x * y)) := by
      rw [← dew1V_eq_twinSet (hccmem (x * y) hxyD hxy1).1 (hccmem (x * y) hxyD hxy1).2]
      exact h.dewStar_mem_dew1V sp0
    obtain ⟨n, hn, -⟩ := h.exists_unique_shift S (hccmem (x * y) hxyD hxy1).1 hMmem
    have hdn : dewQb b n = 0 := by
      rw [← dewG_defect_eq S b (hccmem (x * y) hxyD hxy1).1 hn.symm]
      exact hccdef x hx y hy hx1 hy1 sp.ne
    refine (hX _).2 ⟨x * y, hxyD, hxy1, ε + ε' + n,
      dchoice_sum3 b ε ε' n hε hε' ((dewQb_eq_zero_iff b n).mp hdn), ?_⟩
    rw [h.dewStar_shift S sp0 ε ε', ← hn, S.shift_add (ε + ε') n (cc (x * y))
      (hccmem (x * y) hxyD hxy1).1]

theorem isDewPoint_conjSub (S : TwinShift Ω) {b : Lab2} {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) (g : G) : IsDewPoint S b (conjSub g '' X) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨K, hK, rfl⟩
    exact S.conj_mem g K (hX.1 hK)
  · rintro _ ⟨K, hK, rfl⟩
    exact ⟨S.shift b K, hX.2.1 K hK, (S.shift_conj b g K (hX.1 hK)).symm⟩
  · intro K hK
    have hK' : conjSub g⁻¹ K ∈ Ω := S.conj_mem g⁻¹ K hK
    have hTw : conjSub g '' twinSet Ω (conjSub g⁻¹ K) = twinSet Ω K := by
      rw [h.det_tw_image_twinSet g (conjSub g⁻¹ K), conjSub_conjSub_inv]
    have hI : twinSet Ω K ∩ conjSub g '' X = conjSub g '' (twinSet Ω (conjSub g⁻¹ K) ∩ X) := by
      rw [Set.image_inter (conjSub_injective g), hTw]
    rw [hI, Set.ncard_image_of_injective _ (conjSub_injective g)]
    exact hX.2.2.1 _ hK'
  · rintro _ ⟨K₁, hK₁, rfl⟩ _ ⟨L₁, hL₁, rfl⟩ u v sp
    have hK₁u : IsUniqueInvolution K₁ (g⁻¹ * u * g) := by
      have := sp.invK.conj g⁻¹
      rwa [conjSub_inv_conjSub, inv_inv] at this
    have hL₁v : IsUniqueInvolution L₁ (g⁻¹ * v * g) := by
      have := sp.invL.conj g⁻¹
      rwa [conjSub_inv_conjSub, inv_inv] at this
    have hne : g⁻¹ * u * g ≠ g⁻¹ * v * g := by
      intro e
      apply sp.ne
      calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
        _ = g * (g⁻¹ * v * g) * g⁻¹ := by rw [e]
        _ = v := by group
    have sp₁ : DewPair Ω K₁ L₁ (g⁻¹ * u * g) (g⁻¹ * v * g) :=
      ⟨hX.1 hK₁, hX.1 hL₁, hK₁u, hL₁v, hne⟩
    exact ⟨dewStar K₁ L₁, hX.2.2.2 K₁ hK₁ L₁ hL₁ _ _ sp₁, h.conjSub_dewStar sp₁ g⟩

theorem conjSub_mem_iff (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {q : G} (hq : q ∈ pCore 2 G) {K : Subgroup G} (hK : K ∈ X) {x : G}
    (hKx : K ∈ dew1V Ω x) : conjSub q K ∈ X ↔ dewQb b (S.lam q x) = 0 := by
  rw [h.lam_spec S hq hKx]
  exact h.pt_shift_mem S hb hX hK _

theorem conjSub_image_eq_iff (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {q : G} (hq : q ∈ pCore 2 G) :
    conjSub q '' X = X ↔ q ∈ dewA S b := by
  rw [h.mem_dewA_iff S b hq]
  constructor
  · intro hfix x
    by_cases hx : x ∈ zGroup Ω ∧ x ≠ 1
    · obtain ⟨L, hLX, hLx⟩ := h.pt_exists_mem S hX hx.1 hx.2
      have hc : conjSub q L ∈ conjSub q '' X := Set.mem_image_of_mem _ hLX
      rw [hfix] at hc
      rw [h.lam_spec S hq (show L ∈ dew1V Ω x from ⟨hX.1 hLX, hLx⟩)] at hc
      exact (dewQb_eq_zero_iff b _).mp ((h.pt_shift_mem S hb hX hLX _).mp hc)
    · have hx' : x ∉ zGroup Ω ∨ x = 1 := by
        by_cases hD : x ∈ zGroup Ω
        · exact Or.inr (by by_contra h1; exact hx ⟨hD, h1⟩)
        · exact Or.inl hD
      rw [h.lam_eq_zero_of_not_mem S hx']
      exact Or.inl rfl
  · intro hall
    apply h.pt_eq_of_subset S (h.isDewPoint_conjSub S hX q) hX
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨x, hx⟩ := h.exists_isUniqueInvolution (hX.1 hL)
    rw [h.lam_spec S hq (show L ∈ dew1V Ω x from ⟨hX.1 hL, hx⟩)]
    exact (h.pt_shift_mem S hb hX hL _).mpr ((dewQb_eq_zero_iff b _).mpr (hall x))

theorem conjSub_pCore_image_eq (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) {m₀ : Lab2} (hm₀ : dewQb b m₀ = 1)
    {q : G} (hq : q ∈ pCore 2 G) (hlam : ∀ x, S.lam q x = dewEps X Y x • m₀) :
    conjSub q '' X = Y := by
  apply h.pt_eq_of_subset S (h.isDewPoint_conjSub S hX q) hY
  rintro _ ⟨L, hL, rfl⟩
  obtain ⟨x, hx⟩ := h.exists_isUniqueInvolution (hX.1 hL)
  have hLΩ : L ∈ Ω := hX.1 hL
  rw [h.lam_spec S hq (show L ∈ dew1V Ω x from ⟨hLΩ, hx⟩), hlam x]
  rcases zmod2_cases (dewEps X Y x) with hε | hε
  · rw [hε, zero_smul, S.shift_zero L hLΩ]
    exact (h.mem_iff_dewEps S hb hX hY hL hx).mpr hε
  · rw [hε, one_smul]
    obtain ⟨m, hmY, hm⟩ := h.exists_label S hb hX hY hL hx
    rw [hε] at hm
    have hsh : S.shift m₀ L = S.shift (m₀ + m) (S.shift m L) := by
      rw [S.shift_add m₀ m (S.shift m L) (hY.1 hmY), S.shift_shift_self m hLΩ]
    rw [hsh]
    apply (h.pt_shift_mem S hb hY hmY (m₀ + m)).mpr
    rw [dewQb_add b m₀ m hb, hm₀, hm]
    exact zmod2_add_self 1

theorem exists_pCore_conjSub_image (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    {X Y : Set (Subgroup G)} (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) :
    ∃ q ∈ pCore 2 G, conjSub q '' X = Y := by
  obtain ⟨m₀, hm₀⟩ := lab2_exists_dewQb_one b hb
  have hF : (fun x => dewEps X Y x • m₀) ∈ dewDual2 Ω := by
    obtain ⟨h0, hD, hadd⟩ := h.dewEps_mem_dual S hb hX hY
    refine ⟨by simp only [h0, zero_smul], fun x hx => by simp only [hD x hx, zero_smul], ?_⟩
    intro x hx y hy
    simp only [hadd x hx y hy, add_smul]
  obtain ⟨q, hq, hlam⟩ := h.lam_surj S hF
  exact ⟨q, hq, h.conjSub_pCore_image_eq S hb hX hY hm₀ hq (fun x => hlam x)⟩

omit h in
theorem dcount_card_mul {H Stab : Subgroup G} (hS : Stab ≤ H) {α : Type} (φ : H → α)
    (hφ : ∀ x y : H, φ x = φ y ↔ ((x⁻¹ * y : H) : G) ∈ Stab) :
    Nat.card H = (Set.range φ).ncard * Nat.card Stab := by
  let s : Subgroup H := Stab.subgroupOf H
  have hA : Nat.card H = Nat.card (H ⧸ s) * Nat.card s :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup s
  have hB : Nat.card s = Nat.card Stab :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  let f : H ⧸ s → Set.range φ := Quotient.lift (fun x => ⟨φ x, x, rfl⟩) (by
    intro a b hab
    apply Subtype.ext
    exact (hφ a b).mpr (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab)))
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
      have h1 : φ a = φ b := congrArg Subtype.val hpq
      exact QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ((hφ a b).mp h1))
    · rintro ⟨Y, x, rfl⟩
      exact ⟨QuotientGroup.mk x, rfl⟩
  have hC : Nat.card (H ⧸ s) = (Set.range φ).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.ofBijective f hf)
  rw [hA, hB, hC]

omit h in
theorem dcount_image_eq_iff {X : Set (Subgroup G)} (a c : G) :
    conjSub a '' X = conjSub c '' X ↔ conjSub (a⁻¹ * c) '' X = X := by
  have key : conjSub c '' X = conjSub a '' (conjSub (a⁻¹ * c) '' X) := by
    rw [Set.image_image]
    simp only [← conjSub_mul, mul_inv_cancel_left]
  rw [key, Set.image_eq_image (conjSub_injective a)]
  exact eq_comm

theorem dcount_exists_not_mem (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G}
    (hK : K ∈ Ω) {u : G} (hKu : IsUniqueInvolution K u) :
    ∃ Z, IsDewPoint S b Z ∧ K ∉ Z := by
  obtain ⟨Y₀, hY₀⟩ := h.exists_dewPoint S hb
  by_cases hKY : K ∈ Y₀
  · have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hKu
    obtain ⟨f, hf, hfu⟩ := h.exists_dual_ne huD (zGroup Ω).one_mem hKu.ne_one
    have hf1 : f 1 = 0 := hf.1
    have hfu1 : f u = 1 := by
      rcases zmod2_cases (f u) with h0 | h0
      · exact absurd (h0.trans hf1.symm) hfu
      · exact h0
    obtain ⟨m₀, hm₀⟩ := lab2_exists_dewQb_one b hb
    have hF : (fun x => f x • m₀) ∈ dewDual2 Ω := by
      refine ⟨?_, ?_, ?_⟩
      · simp only [hf1, zero_smul]
      · intro x hx
        simp only [hf.2.1 x hx, zero_smul]
      · intro x hx y hy
        simp only [hf.2.2 x hx y hy, add_smul]
    obtain ⟨p, hp, hpF⟩ := h.lam_surj S hF
    have hpu : dewQb b (S.lam p u) = 1 := by
      rw [hpF u]
      simp only [hfu1, one_smul]
      exact hm₀
    refine ⟨conjSub p⁻¹ '' Y₀, h.isDewPoint_conjSub S hY₀ p⁻¹, ?_⟩
    rintro ⟨L, hLY, hL⟩
    have hpK : conjSub p K ∈ Y₀ := by
      have e : conjSub p K = L := by
        rw [← hL, conjSub_conjSub_inv]
      rw [e]
      exact hLY
    have h0 := (h.conjSub_mem_iff S hb hY₀ hp hKY (show K ∈ dew1V Ω u from ⟨hK, hKu⟩)).mp hpK
    rw [hpu] at h0
    exact one_ne_zero h0
  · exact ⟨Y₀, hY₀, hKY⟩

theorem dcount_stab_iff (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G} (hK : K ∈ Ω)
    {u : G} (hKu : IsUniqueInvolution K u) {X : Set (Subgroup G)} (hX : IsDewPoint S b X)
    (hKX : K ∉ X) {z : G} (hz : z ∈ K) :
    conjSub z '' X = X ↔ z ∈ Subgroup.zpowers u := by
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hKu
  constructor
  · intro hfix
    have hzC : z ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1, one_mul, mul_one]
      obtain ⟨L, hLX, hLx⟩ := h.pt_exists_mem S hX hx hx1
      have hcL : conjSub z L ∈ X := by
        have hmem := Set.mem_image_of_mem (conjSub z) hLX
        rwa [hfix] at hmem
      have hzL : conjSub z L = L :=
        h.conjSub_eq_of_mem_of_not_mem S hb hX hK hKu hKX hz hLX hLx hcL
      have hxz : z⁻¹ * x * z ∈ L := by
        have hxL : x ∈ conjSub z L := by
          rw [hzL]
          exact hLx.mem
        exact mem_conjSub_iff.mp hxL
      have hsq : (z⁻¹ * x * z) * (z⁻¹ * x * z) = 1 := by
        calc (z⁻¹ * x * z) * (z⁻¹ * x * z) = z⁻¹ * (x * x) * z := by group
          _ = 1 := by rw [hLx.sq]; group
      have heq : z⁻¹ * x * z = x := by
        rcases hLx.unique _ hxz hsq with h1 | h1
        · exfalso
          apply hx1
          calc x = z * (z⁻¹ * x * z) * z⁻¹ := by group
            _ = 1 := by rw [h1]; group
        · exact h1
      calc x * z = z * (z⁻¹ * x * z) := by group
        _ = z * x := by rw [heq]
    have hzK : z ∈ K ⊓ Subgroup.centralizer (zGroup Ω : Set G) := ⟨hz, hzC⟩
    rw [h.inf_centralizer_zGroup hK hKu] at hzK
    exact hzK
  · intro hzu
    have hzD : z ∈ zGroup Ω := (Subgroup.zpowers_le.mpr huD) hzu
    have hzA : z ∈ dewA S b := h.zGroup_le_dewA S b hzD
    exact (h.conjSub_image_eq_iff S hb hX (dewA_le_pCore S b hzA)).mpr hzA

theorem ncard_dewPts (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) : (dewPts S b).ncard = 8 := by
  obtain ⟨X₀, hX₀⟩ := h.exists_dewPoint S hb
  let φ : pCore 2 G → Set (Subgroup G) := fun x => conjSub (x : G) '' X₀
  have hφ : ∀ x y : pCore 2 G, φ x = φ y ↔ ((x⁻¹ * y : pCore 2 G) : G) ∈ dewA S b := by
    intro x y
    rw [show ((x⁻¹ * y : pCore 2 G) : G) = (x : G)⁻¹ * (y : G) from rfl]
    show conjSub (x : G) '' X₀ = conjSub (y : G) '' X₀ ↔ _
    rw [dcount_image_eq_iff]
    exact h.conjSub_image_eq_iff S hb hX₀ ((pCore 2 G).mul_mem ((pCore 2 G).inv_mem x.2) y.2)
  have hrange : Set.range φ = dewPts S b := by
    ext Y
    constructor
    · rintro ⟨x, rfl⟩
      exact h.isDewPoint_conjSub S hX₀ (x : G)
    · intro hY
      obtain ⟨q, hq, hqY⟩ :=
        h.exists_pCore_conjSub_image S hb hX₀ (show IsDewPoint S b Y from hY)
      exact ⟨⟨q, hq⟩, hqY⟩
  have key := dcount_card_mul (H := pCore 2 G) (Stab := dewA S b) (dewA_le_pCore S b) φ hφ
  rw [h.card_pCore_eq, h.card_dewA S hb, hrange] at key
  omega

theorem forall_conjSub_image_eq_iff_mem (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    {X : Set (Subgroup G)} (hX : IsDewPoint S b X) {K : Subgroup G} (hK : K ∈ Ω) :
    (∀ k ∈ K, conjSub k '' X = X) ↔ K ∈ X := by
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hu
  constructor
  · intro hall
    by_contra hKX
    obtain ⟨k, hkK, hkC⟩ : ∃ k ∈ K, k ∉ Subgroup.centralizer (zGroup Ω : Set G) := by
      by_contra hcon
      push Not at hcon
      have hle : K ≤ Subgroup.centralizer (zGroup Ω : Set G) := fun k hk => hcon k hk
      have h1 : K ⊓ Subgroup.centralizer (zGroup Ω : Set G) = K := inf_eq_left.mpr hle
      rw [h.inf_centralizer_zGroup hK hu] at h1
      have h2 : Nat.card ↥(Subgroup.zpowers u) = Nat.card ↥K :=
        congrArg (fun H : Subgroup G => Nat.card ↥H) h1
      rw [h.card K hK, card_zpowers_of_involution hu.sq hu.ne_one] at h2
      norm_num at h2
    obtain ⟨x, hxD, hkx⟩ : ∃ x ∈ zGroup Ω, k * x ≠ x * k := by
      by_contra hc
      push Not at hc
      exact hkC (Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm)
    have hx1 : x ≠ 1 := by
      intro e
      rw [e] at hkx
      exact hkx (by group)
    have hxu : x ≠ u := by
      intro e
      rw [e] at hkx
      rcases h.conj_eq_or_mul hK hu hkK huD with h1 | h1
      · apply hkx
        calc k * u = (k * u * k⁻¹) * k := by group
          _ = u * k := by rw [h1]
      · rw [hu.sq] at h1
        apply hu.ne_one
        calc u = k⁻¹ * (k * u * k⁻¹) * k := by group
          _ = k⁻¹ * 1 * k := by rw [h1]
          _ = 1 := by group
    obtain ⟨L, hLX, hLx⟩ := h.pt_exists_mem S hX hxD hx1
    have hc : conjSub k L ∈ conjSub k '' X := Set.mem_image_of_mem _ hLX
    rw [hall k hkK] at hc
    have e1 := h.conjSub_eq_of_mem_of_not_mem S hb hX hK hu hKX hkK hLX hLx hc
    have hn := mem_normalizer_of_conjSub_eq e1
    have sp : DewPair Ω K L u x := ⟨hK, hX.1 hLX, hu, hLx, fun e => hxu e.symm⟩
    exact hkx ((h.mem_normalizer_iff_commute sp hkK).mp hn)
  · intro hKX k hkK
    apply h.pt_eq_of_subset S (h.isDewPoint_conjSub S hX k) hX
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨v, hv⟩ := h.exists_isUniqueInvolution (hX.1 hL)
    by_cases huv : u = v
    · subst huv
      have hn : k ∈ Subgroup.normalizer (L : Set G) :=
        h.le_normalizer_of_dew1V hK hu (show L ∈ dew1V Ω u from ⟨hX.1 hL, hv⟩) hkK
      rw [conjSub_eq_self_of_mem_normalizer hn]
      exact hL
    · have sp : DewPair Ω K L u v := ⟨hK, hX.1 hL, hu, hv, huv⟩
      rcases h.conjSub_eq_or_dewStar sp hkK with h1 | h1
      · rw [h1]
        exact hL
      · rw [h1]
        exact hX.2.2.2 K hKX L hL u v sp

theorem dq_mem_image_iff (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {K : Subgroup G} {u : G} (hK : K ∈ Ω)
    (hKu : IsUniqueInvolution K u) (hKX : K ∉ X) {φ : G → ZMod 2} {k : G} (hk : k ∈ K)
    (hkφ : IsElationOf Ω u φ k) {L : Subgroup G} (hL : L ∈ X) {x : G}
    (hLx : IsUniqueInvolution L x) : L ∈ conjSub k '' X ↔ φ x = 0 := by
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hKu
  have hLΩ : L ∈ Ω := hX.1 hL
  have hxD : x ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hLΩ hLx
  have hk' : k⁻¹ ∈ K := K.inv_mem hk
  have hφu : φ u = 0 := by
    by_contra hne
    have e := hkφ u huD
    rw [if_neg hne, hKu.sq] at e
    apply hKu.ne_one
    calc u = k⁻¹ * (k * u * k⁻¹) * k := by group
      _ = 1 := by rw [e]; group
  rw [mem_conjSub_image_iff]
  by_cases hxu : x = u
  · have hn : k⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      h.le_normalizer_of_dew1V hK hKu (show L ∈ dew1V Ω u from ⟨hLΩ, by rw [← hxu]; exact hLx⟩) hk'
    rw [conjSub_eq_self_of_mem_normalizer hn]
    exact ⟨fun _ => by rw [hxu]; exact hφu, fun _ => hL⟩
  · have sp : DewPair Ω K L u x := ⟨hK, hLΩ, hKu, hLx, fun e => hxu e.symm⟩
    constructor
    · intro hmem
      have e1 := h.conjSub_eq_of_mem_of_not_mem S hb hX hK hKu hKX hk' hL hLx hmem
      have hcomm := (h.mem_normalizer_iff_commute sp hk').mp (mem_normalizer_of_conjSub_eq e1)
      have hconj : k * x * k⁻¹ = x := by
        calc k * x * k⁻¹ = k * (x * k⁻¹) := by group
          _ = k * (k⁻¹ * x) := by rw [hcomm]
          _ = x := by group
      by_contra hφx
      have h1 : φ x = 1 := (zmod2_cases (φ x)).resolve_left hφx
      have e := hkφ x hxD
      rw [if_neg (show ¬ (φ x = 0) from by rw [h1]; exact one_ne_zero), hconj] at e
      apply hKu.ne_one
      calc u = (u * x) * x⁻¹ := by group
        _ = x * x⁻¹ := by rw [← e]
        _ = 1 := by group
    · intro hφx
      have e := hkφ x hxD
      rw [if_pos hφx] at e
      have hcomm : k⁻¹ * x = x * k⁻¹ := by
        calc k⁻¹ * x = k⁻¹ * (k * x * k⁻¹) := by rw [e]
          _ = x * k⁻¹ := by group
      have hn : k⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
        (h.mem_normalizer_iff_commute sp hk').mpr hcomm
      rw [conjSub_eq_self_of_mem_normalizer hn]
      exact hL

theorem exists_mem_conjSub_image (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    {X Y : Set (Subgroup G)} (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) {K : Subgroup G}
    (hK : K ∈ Ω) (hKX : K ∉ X) (hKY : K ∉ Y) : ∃ k ∈ K, conjSub k '' X = Y := by
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hu
  have hεu : dewEps X Y u = 0 := by
    rcases zmod2_cases (dewEps X Y u) with h0 | h1
    · exact h0
    · exact absurd ((h.mem_iff_of_dewEps_eq_one S hb hX hY h1 hK hu).mpr hKY) hKX
  obtain ⟨k, hkK, hkφ⟩ := h.exists_mem_isElationOf hK hu (h.dewEps_mem_dual S hb hX hY) hεu
  refine ⟨k, hkK, ?_⟩
  apply h.pt_eq_of_subset S (h.isDewPoint_conjSub S hX k) hY
  rintro _ ⟨L, hL, rfl⟩
  obtain ⟨x, hx⟩ := h.exists_isUniqueInvolution (hX.1 hL)
  have hLΩ : L ∈ Ω := hX.1 hL
  have hxD : x ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hLΩ hx
  have hkx := hkφ x hxD
  rcases zmod2_cases (dewEps X Y x) with hε | hε
  · have hLY : L ∈ Y := (h.mem_iff_dewEps S hb hX hY hL hx).mpr hε
    rw [if_pos hε] at hkx
    have hn : k ∈ Subgroup.normalizer (L : Set G) := by
      by_cases hxu : x = u
      · have hLu : L ∈ dew1V Ω u := ⟨hLΩ, by rw [← hxu]; exact hx⟩
        exact h.le_normalizer_of_dew1V hK hu hLu hkK
      · have sp : DewPair Ω K L u x := ⟨hK, hLΩ, hu, hx, fun e => hxu e.symm⟩
        refine (h.mem_normalizer_iff_commute sp hkK).mpr ?_
        calc k * x = (k * x * k⁻¹) * k := by group
          _ = x * k := by rw [hkx]
    rw [conjSub_eq_self_of_mem_normalizer hn]
    exact hLY
  · have hxu : x ≠ u := fun e => by
      rw [e, hεu] at hε
      exact zero_ne_one hε
    have sp : DewPair Ω K L u x := ⟨hK, hLΩ, hu, hx, fun e => hxu e.symm⟩
    rw [if_neg (show ¬ (dewEps X Y x = 0) from by rw [hε]; exact one_ne_zero)] at hkx
    have hnotn : conjSub k L ≠ L := by
      intro e
      have hn := mem_normalizer_of_conjSub_eq e
      have hc := (h.mem_normalizer_iff_commute sp hkK).mp hn
      have hconj : k * x * k⁻¹ = x := by
        calc k * x * k⁻¹ = (x * k) * k⁻¹ := by rw [hc]
          _ = x := by group
      rw [hconj] at hkx
      apply hu.ne_one
      calc u = (u * x) * x⁻¹ := by group
        _ = x * x⁻¹ := by rw [← hkx]
        _ = 1 := by group
    have hdew : conjSub k L = dewStar K L := by
      rcases h.conjSub_eq_or_dewStar sp hkK with h1 | h1
      · exact absurd h1 hnotn
      · exact h1
    have hnX : dewStar K L ∉ X := h.dewStar_not_mem S hb hX hKX sp hL
    have hyΩ : dewStar K L ∈ Ω := (h.dewStar_mem_dew1V sp).1
    have hyuv : IsUniqueInvolution (dewStar K L) (u * x) := (h.dewStar_mem_dew1V sp).2
    have hux : u ≠ x := fun e => hxu e.symm
    have hε' : dewEps X Y (u * x) = 1 := by
      rw [h.dewEps_mul S hb hX hY huD hu.ne_one hxD hx.ne_one hux, hεu, hε, zero_add]
    have hiff := h.mem_iff_of_dewEps_eq_one S hb hX hY hε' hyΩ hyuv
    have hYmem : dewStar K L ∈ Y := by
      by_contra hc
      exact hnX (hiff.mpr hc)
    rw [hdew]
    exact hYmem

theorem ncard_dewPts_mem (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G}
    (hK : K ∈ Ω) : {X | X ∈ dewPts S b ∧ K ∈ X}.ncard = 4 := by
  obtain ⟨u, hKu⟩ := h.exists_isUniqueInvolution hK
  obtain ⟨X₀, hX₀, hKX₀⟩ := h.dcount_exists_not_mem S hb hK hKu
  let φ : K → Set (Subgroup G) := fun k => conjSub (k : G) '' X₀
  have hφ : ∀ x y : K, φ x = φ y ↔ ((x⁻¹ * y : K) : G) ∈ Subgroup.zpowers u := by
    intro x y
    rw [show ((x⁻¹ * y : K) : G) = (x : G)⁻¹ * (y : G) from rfl]
    show conjSub (x : G) '' X₀ = conjSub (y : G) '' X₀ ↔ _
    rw [dcount_image_eq_iff]
    exact h.dcount_stab_iff S hb hK hKu hX₀ hKX₀ (K.mul_mem (K.inv_mem x.2) y.2)
  have hrange : Set.range φ = {X | X ∈ dewPts S b ∧ K ∉ X} := by
    ext Y
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨h.isDewPoint_conjSub S hX₀ (x : G), ?_⟩
      rintro ⟨L, hL, hLK⟩
      have hLK' : L = K :=
        conjSub_injective (x : G) (hLK.trans (conjSub_eq_self_of_mem x.2).symm)
      rw [hLK'] at hL
      exact hKX₀ hL
    · rintro ⟨hY, hKY⟩
      obtain ⟨k, hk, hkY⟩ :=
        h.exists_mem_conjSub_image S hb hX₀ (show IsDewPoint S b Y from hY) hK hKX₀ hKY
      exact ⟨⟨k, hk⟩, hkY⟩
  have hcard := dcount_card_mul (H := K) (Stab := Subgroup.zpowers u)
    (Subgroup.zpowers_le.mpr hKu.mem) φ hφ
  rw [h.card K hK, Nat.card_zpowers,
    orderOf_eq_prime (show u ^ 2 = 1 by rw [pow_two]; exact hKu.sq) hKu.ne_one, hrange] at hcard
  have hA : {X | X ∈ dewPts S b ∧ K ∉ X}.ncard = 4 := by omega
  have hunion : {X | X ∈ dewPts S b ∧ K ∈ X} ∪ {X | X ∈ dewPts S b ∧ K ∉ X} = dewPts S b := by
    ext X
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨hX, -⟩ | ⟨hX, -⟩) <;> exact hX
    · intro hX
      by_cases hKX : K ∈ X
      · exact Or.inl ⟨hX, hKX⟩
      · exact Or.inr ⟨hX, hKX⟩
  have hdisj : Disjoint {X | X ∈ dewPts S b ∧ K ∈ X} {X | X ∈ dewPts S b ∧ K ∉ X} := by
    rw [Set.disjoint_left]
    rintro X ⟨-, h1⟩ ⟨-, h2⟩
    exact h2 h1
  have hsum := Set.ncard_union_eq hdisj
  rw [hunion, h.ncard_dewPts S hb, hA] at hsum
  omega

theorem dq_indep (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {c₀ : Set (Subgroup G)}
    (hc₀ : IsDewPoint S b c₀) {q q' : G} (hq : q ∈ pCore 2 G) (hq' : q' ∈ pCore 2 G)
    (e : conjSub q '' c₀ = conjSub q' '' c₀) (x : G) :
    dewQb b (S.lam q x) = dewQb b (S.lam q' x) := by
  have hfix : conjSub (q⁻¹ * q') '' c₀ = c₀ := by
    calc conjSub (q⁻¹ * q') '' c₀ = conjSub q⁻¹ '' (conjSub q' '' c₀) :=
          conjSub_image_mul _ _ _
      _ = conjSub q⁻¹ '' (conjSub q '' c₀) := by rw [e]
      _ = conjSub (q⁻¹ * q) '' c₀ := (conjSub_image_mul _ _ _).symm
      _ = c₀ := by
        rw [inv_mul_cancel]
        have h1 : conjSub (1 : G) = fun K => K := funext conjSub_one
        rw [h1, Set.image_id']
  have hainv : q⁻¹ * q' ∈ pCore 2 G := (pCore 2 G).mul_mem ((pCore 2 G).inv_mem hq) hq'
  have ha : q⁻¹ * q' ∈ dewA S b := (h.conjSub_image_eq_iff S hb hc₀ hainv).mp hfix
  have h0 : dewQb b (S.lam (q⁻¹ * q') x) = 0 :=
    (dewQb_eq_zero_iff b _).mpr ((h.mem_dewA_iff S b hainv).mp ha x)
  have hsplit : S.lam q' x = S.lam q x + S.lam (q⁻¹ * q') x := by
    have := h.lam_mul S hq hainv x
    rwa [show q * (q⁻¹ * q') = q' by group] at this
  rw [hsplit, dewQb_add b _ _ hb, h0, add_zero]

theorem dq_lam_eq_dewEps (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) {q : G} (hq : q ∈ pCore 2 G)
    (hqXY : conjSub q '' X = Y) (x : G) : dewQb b (S.lam q x) = dewEps X Y x := by
  by_cases hex : ∃ L ∈ X, IsUniqueInvolution L x
  · obtain ⟨L, hLX, hLx⟩ := hex
    have hmem : L ∈ dew1V Ω x := ⟨hX.1 hLX, hLx⟩
    have hiff : L ∈ Y ↔ dewQb b (S.lam q x) = 0 := by
      rw [← hqXY, mem_conjSub_image_iff, h.lam_spec S ((pCore 2 G).inv_mem hq) hmem,
        h.pt_shift_mem S hb hX hLX, h.lam_inv S hq x]
    rcases zmod2_cases (dewEps X Y x) with h0 | h1
    · rw [h0]
      exact hiff.mp ((h.mem_iff_dewEps S hb hX hY hLX hLx).mpr h0)
    · rw [h1]
      rcases zmod2_cases (dewQb b (S.lam q x)) with g0 | g1
      · exfalso
        have h2 := (h.mem_iff_dewEps S hb hX hY hLX hLx).mp (hiff.mpr g0)
        rw [h1] at h2
        exact one_ne_zero h2
      · exact g1
  · have h0 : dewEps X Y x = 0 :=
      dewEps_eq_zero_iff.mpr (fun hc => by obtain ⟨L, hLX, hLx, -⟩ := hc; exact hex ⟨L, hLX, hLx⟩)
    rw [h0]
    have hx : x ∉ zGroup Ω ∨ x = 1 := by
      by_cases hD : x ∈ zGroup Ω
      · right
        by_contra hx1
        obtain ⟨L, hLX, hLx⟩ := h.pt_exists_mem S hX hD hx1
        exact hex ⟨L, hLX, hLx⟩
      · exact Or.inl hD
    rw [h.lam_eq_zero_of_not_mem S hx]
    exact dewQb_zero b

theorem exists_pointCoord (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) :
    Nonempty (DewPointCoord S b) := by
  classical
  obtain ⟨c₀, hc₀⟩ := h.exists_dewPoint S hb
  obtain ⟨m₀, hm₀⟩ := lab2_exists_dewQb_one b hb
  have hex : ∀ X : Set (Subgroup G), ∃ q : G,
      X ∈ dewPts S b → q ∈ pCore 2 G ∧ conjSub q '' c₀ = X := by
    intro X
    by_cases hX : X ∈ dewPts S b
    · obtain ⟨q, hq, hqX⟩ := h.exists_pCore_conjSub_image S hb hc₀ hX
      exact ⟨q, fun _ => ⟨hq, hqX⟩⟩
    · exact ⟨1, fun h1 => absurd h1 hX⟩
  choose qOf hqOf using hex
  have hcoord : ∀ X ∈ dewPts S b, ∀ q ∈ pCore 2 G, conjSub q '' c₀ = X →
      ∀ x, dewQb b (S.lam (qOf X) x) = dewQb b (S.lam q x) := by
    intro X hX q hq hqX x
    exact h.dq_indep S hb hc₀ (hqOf X hX).1 hq ((hqOf X hX).2.trans hqX.symm) x
  let coord : Set (Subgroup G) → G → ZMod 2 := fun X x => dewQb b (S.lam (qOf X) x)
  have hcoordMem : ∀ X ∈ dewPts S b, coord X ∈ DE2Hyp.deq2Dual Ω := by
    intro X hX
    obtain ⟨F1, Fo, Fadd⟩ := h.lam_mem_dual S (hqOf X hX).1
    refine ⟨?_, fun x hx => ?_, fun x hx y hy => ?_⟩
    · show dewQb b (S.lam (qOf X) 1) = 0
      rw [F1, dewQb_zero]
    · show dewQb b (S.lam (qOf X) x) = 0
      rw [Fo x hx, dewQb_zero]
    · show dewQb b (S.lam (qOf X) (x * y)) =
        dewQb b (S.lam (qOf X) x) + dewQb b (S.lam (qOf X) y)
      rw [Fadd x hx y hy, dewQb_add b _ _ hb]
  have hbij : Set.BijOn coord (dewPts S b) (DE2Hyp.deq2Dual Ω) := by
    refine ⟨fun X hX => hcoordMem X hX, ?_, ?_⟩
    · intro X hX Y hY hXY
      have hXY' : ∀ x, dewQb b (S.lam (qOf X) x) = dewQb b (S.lam (qOf Y) x) :=
        fun x => congrFun hXY x
      have hqX := hqOf X hX
      have hqY := hqOf Y hY
      have hainv : (qOf X)⁻¹ * qOf Y ∈ pCore 2 G :=
        (pCore 2 G).mul_mem ((pCore 2 G).inv_mem hqX.1) hqY.1
      have hdewA : (qOf X)⁻¹ * qOf Y ∈ dewA S b := by
        rw [h.mem_dewA_iff S b hainv]
        intro x
        apply (dewQb_eq_zero_iff b _).mp
        rw [h.lam_mul S ((pCore 2 G).inv_mem hqX.1) hqY.1 x, h.lam_inv S hqX.1 x,
          dewQb_add b _ _ hb, ← hXY' x]
        exact zmod2_add_self _
      have hfix : conjSub ((qOf X)⁻¹ * qOf Y) '' c₀ = c₀ :=
        (h.conjSub_image_eq_iff S hb hc₀ hainv).mpr hdewA
      have hYX : conjSub (qOf Y) '' c₀ = conjSub (qOf X) '' c₀ := by
        rw [← mul_inv_cancel_left (qOf X) (qOf Y), conjSub_image_mul, hfix]
      exact hqX.2.symm.trans (hYX.symm.trans hqY.2)
    · intro F hF
      have hF' : (fun x => F x • m₀) ∈ dewDual2 Ω := by
        obtain ⟨h0, hD, hadd⟩ := hF
        refine ⟨by simp only [h0, zero_smul], fun x hx => by simp only [hD x hx, zero_smul], ?_⟩
        intro x hx y hy
        simp only [hadd x hx y hy, add_smul]
      obtain ⟨q, hq, hlam⟩ := h.lam_surj S hF'
      have hY' : conjSub q '' c₀ ∈ dewPts S b := h.isDewPoint_conjSub S hc₀ q
      refine ⟨conjSub q '' c₀, hY', ?_⟩
      funext x
      have hl : S.lam q x = F x • m₀ := hlam x
      show dewQb b (S.lam (qOf (conjSub q '' c₀)) x) = F x
      rw [hcoord (conjSub q '' c₀) hY' q hq rfl x, hl]
      rcases zmod2_cases (F x) with h0 | h1
      · rw [h0, zero_smul, dewQb_zero]
      · rw [h1, one_smul, hm₀]
  have hqAct : ∀ q ∈ pCore 2 G, ∀ X ∈ dewPts S b,
      coord (conjSub q '' X) = coord X + fun x => dewQb b (S.lam q x) := by
    intro q hq X hX
    have hqX := hqOf X hX
    have hXq : conjSub q '' X ∈ dewPts S b := h.isDewPoint_conjSub S hX q
    have hqq : q * qOf X ∈ pCore 2 G := (pCore 2 G).mul_mem hq hqX.1
    have himg : conjSub (q * qOf X) '' c₀ = conjSub q '' X := by
      rw [conjSub_image_mul, hqX.2]
    funext x
    show dewQb b (S.lam (qOf (conjSub q '' X)) x) =
      dewQb b (S.lam (qOf X) x) + dewQb b (S.lam q x)
    rw [hcoord (conjSub q '' X) hXq (q * qOf X) hqq himg x, h.lam_mul S hq hqX.1 x,
      dewQb_add b _ _ hb, add_comm]
  have hgAct : ∀ g : G, ∃ f₀ ∈ DE2Hyp.deq2Dual Ω, ∀ X ∈ dewPts S b,
      coord (conjSub g '' X) = (fun x => coord X (g⁻¹ * x * g)) + f₀ := by
    intro g
    haveI : (pCore 2 G).Normal := CFSG.pCore_normal
    have hY₀ : conjSub g '' c₀ ∈ dewPts S b := h.isDewPoint_conjSub S hc₀ g
    refine ⟨coord (conjSub g '' c₀), hcoordMem _ hY₀, ?_⟩
    intro X hX
    have hqX := hqOf X hX
    have hq' : g * qOf X * g⁻¹ ∈ pCore 2 G :=
      (inferInstance : (pCore 2 G).Normal).conj_mem _ hqX.1 g
    have hgX : conjSub g '' X = conjSub (g * qOf X * g⁻¹) '' (conjSub g '' c₀) := by
      rw [← conjSub_image_mul (g * qOf X * g⁻¹) g c₀,
        show g * qOf X * g⁻¹ * g = g * qOf X by group, conjSub_image_mul g (qOf X) c₀, hqX.2]
    funext x
    have hconj : S.lam (g * qOf X * g⁻¹) x = S.lam (qOf X) (g⁻¹ * x * g) := by
      have := h.lam_conj S hqX.1 g (g⁻¹ * x * g)
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
    have e := hqAct _ hq' _ hY₀
    rw [hgX, e]
    show coord (conjSub g '' c₀) x + dewQb b (S.lam (g * qOf X * g⁻¹) x) =
      coord X (g⁻¹ * x * g) + coord (conjSub g '' c₀) x
    rw [hconj]
    exact add_comm _ _
  have hmemFix : ∀ K ∈ Ω, ∀ X ∈ dewPts S b, K ∈ X → ∀ k ∈ K,
      coord (conjSub k '' X) = coord X := by
    intro K hK X hX hKX k hk
    rw [(h.forall_conjSub_image_eq_iff_mem S hb hX hK).mpr hKX k hk]
  have hmemAct : ∀ K ∈ Ω, ∀ u : G, IsUniqueInvolution K u → ∀ φ ∈ DE2Hyp.deq2Dual Ω, ∀ k ∈ K,
      IsElationOf Ω u φ k → ∀ X ∈ dewPts S b, K ∉ X →
        coord (conjSub k '' X) = coord X + φ := by
    intro K hK u hKu φ hφ k hk hkφ X hX hKX
    have hY : conjSub k '' X ∈ dewPts S b := h.isDewPoint_conjSub S hX k
    obtain ⟨q, hq, hqXY⟩ := h.exists_pCore_conjSub_image S hb hX hY
    have hiffx : ∀ x, dewEps X (conjSub k '' X) x = 0 ↔ φ x = 0 := by
      intro x
      by_cases hex : ∃ L ∈ X, IsUniqueInvolution L x
      · obtain ⟨L, hLX, hLx⟩ := hex
        rw [← h.mem_iff_dewEps S hb hX hY hLX hLx]
        exact h.dq_mem_image_iff S hb hX hK hKu hKX hk hkφ hLX hLx
      · have h0 : dewEps X (conjSub k '' X) x = 0 :=
          dewEps_eq_zero_iff.mpr fun hc => by
            obtain ⟨L, hLX, hLx, -⟩ := hc
            exact hex ⟨L, hLX, hLx⟩
        have hφ0 : φ x = 0 := by
          by_cases hD : x ∈ zGroup Ω
          · by_cases hx1 : x = 1
            · rw [hx1]
              exact hφ.1
            · exfalso
              obtain ⟨L, hLX, hLx⟩ := h.pt_exists_mem S hX hD hx1
              exact hex ⟨L, hLX, hLx⟩
          · exact hφ.2.1 x hD
        exact iff_of_true h0 hφ0
    have hεφ : dewEps X (conjSub k '' X) = φ := by
      funext x
      by_cases h0 : dewEps X (conjSub k '' X) x = 0
      · exact h0.trans ((hiffx x).mp h0).symm
      · have h2 : φ x = 1 := by
          rcases zmod2_cases (φ x) with h3 | h3
          · exact absurd ((hiffx x).mpr h3) h0
          · exact h3
        exact ((zmod2_cases _).resolve_left h0).trans h2.symm
    rw [← hqXY, hqAct q hq X hX]
    congr 1
    funext x
    rw [h.dq_lam_eq_dewEps S hb hX hY hq hqXY x]
    exact congrFun hεφ x
  exact ⟨⟨coord, hbij, hqAct, hgAct, hmemFix, hmemAct⟩⟩

theorem forall_conjSub_image_eq_iff (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) (g : G) :
    (∀ X ∈ dewPts S b, conjSub g '' X = X) ↔ g ∈ dewA S b := by
  classical
  obtain ⟨C⟩ := h.exists_pointCoord S hb
  constructor
  · intro hall
    obtain ⟨X₀, hX₀, hX₀0⟩ : ∃ X₀ ∈ dewPts S b, C.coord X₀ = 0 := by
      have : (0 : G → ZMod 2) ∈ DE2Hyp.deq2Dual Ω :=
        ⟨rfl, fun _ _ => rfl, fun _ _ _ _ => by simp⟩
      exact C.bijOn.surjOn this
    obtain ⟨f₀, hf₀, hg⟩ := C.gAct g
    have hf₀0 : f₀ = 0 := by
      have := hg X₀ hX₀
      rw [hall X₀ hX₀, hX₀0] at this
      funext x
      have := congrFun this x
      simpa using this.symm
    have hfix : ∀ X ∈ dewPts S b, ∀ x, C.coord X (g⁻¹ * x * g) = C.coord X x := by
      intro X hX x
      have := congrFun (hg X hX) x
      rw [hall X hX, hf₀0] at this
      simpa using this.symm
    have hgC : g ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
      by_contra hne
      have hd' : g⁻¹ * d * g ∈ zGroup Ω := by
        have := h.zGroup_normal.conj_mem d hd g⁻¹
        simpa using this
      have hne' : d ≠ g⁻¹ * d * g := by
        intro h1
        apply hne
        calc d * g = g * (g⁻¹ * d * g) := by group
          _ = g * d := by rw [← h1]
      obtain ⟨f, hf, hfne⟩ := h.exists_dual_ne hd hd' hne'
      obtain ⟨X, hX, hXf⟩ := C.bijOn.surjOn hf
      have := hfix X hX d
      rw [hXf] at this
      exact hfne this.symm
    have hgQ : g ∈ pCore 2 G := by
      rw [← h.centralizer_zGroup_eq_pCore]
      exact hgC
    exact (h.conjSub_image_eq_iff S hb hX₀ hgQ).mp (hall X₀ hX₀)
  · intro hg X hX
    exact (h.conjSub_image_eq_iff S hb hX (dewA_le_pCore S b hg)).mpr hg

omit h in
theorem dagl_zmod_add_eq_zero_iff : ∀ x y : ZMod 2, x + y = 0 ↔ y = x := by decide

omit h in
theorem dagl_zmod_ne_iff : ∀ y c : ZMod 2, y ≠ c ↔ y = c + 1 := by decide

omit h in
theorem dagl_zmod_eq_of_ne : ∀ c c₁ : ZMod 2, c ≠ c₁ + 1 → c = c₁ := by decide

omit h in
theorem dagl_flip_key : ∀ b m n : Lab2, b ≠ 0 → dewQb b m = 1 → dewQb b n = 1 →
    m = n ∨ m = b + n := by decide

theorem dagl_zero_mem : (0 : G → ZMod 2) ∈ DE2Hyp.deq2Dual Ω :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ _ => by simp⟩

theorem dagl_coord_e8Coord {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e)
    {F : G → ZMod 2} (hF : F ∈ DE2Hyp.deq2Dual Ω) (v : Fin 3 → ZMod 2) :
    F (TL4.e8Coord e v) = v ⬝ᵥ fun i => F (e i) := by
  have hpow : ∀ x ∈ zGroup Ω, ∀ n : ℕ, F (x ^ n) = (n : ZMod 2) * F x := by
    intro x hx n
    induction n with
    | zero => rw [pow_zero, hF.1]; simp
    | succ n ih =>
      rw [pow_succ, hF.2.2 _ ((zGroup Ω).pow_mem hx n) x hx, ih]
      push_cast
      ring
  have hm : ∀ k, F (e k ^ (v k).val) = v k * F (e k) := by
    intro k
    rw [hpow _ (he.mem k), ZMod.natCast_zmod_val]
  have h0 : e 0 ^ (v 0).val ∈ zGroup Ω := (zGroup Ω).pow_mem (he.mem 0) _
  have h1 : e 1 ^ (v 1).val ∈ zGroup Ω := (zGroup Ω).pow_mem (he.mem 1) _
  have h2 : e 2 ^ (v 2).val ∈ zGroup Ω := (zGroup Ω).pow_mem (he.mem 2) _
  have h01 : e 0 ^ (v 0).val * e 1 ^ (v 1).val ∈ zGroup Ω := (zGroup Ω).mul_mem h0 h1
  unfold TL4.e8Coord
  rw [hF.2.2 _ h01 _ h2, hF.2.2 _ h0 _ h1, hm 0, hm 1, hm 2]
  simp [dotProduct, Fin.sum_univ_three]

theorem dagl_coord_ext {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e)
    {F F' : G → ZMod 2} (hF : F ∈ DE2Hyp.deq2Dual Ω) (hF' : F' ∈ DE2Hyp.deq2Dual Ω)
    (hFe : ∀ i, F (e i) = F' (e i)) : F = F' := by
  funext x
  by_cases hx : x ∈ zGroup Ω
  · obtain ⟨v, rfl⟩ := TL4.exists_e8Coord_eq he hx
    rw [h.dagl_coord_e8Coord he hF, h.dagl_coord_e8Coord he hF']
    simp only [hFe]
  · rw [hF.2.1 x hx, hF'.2.1 x hx]

theorem dagl_exists_coord {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e)
    (w : Fin 3 → ZMod 2) : ∃ F ∈ DE2Hyp.deq2Dual Ω, ∀ i, F (e i) = w i := by
  classical
  let ψ : G → Fin 3 → ZMod 2 := fun x =>
    if hx : x ∈ zGroup Ω then (TL4.exists_e8Coord_eq he hx).choose else 0
  have hψe : ∀ x (hx : x ∈ zGroup Ω), TL4.e8Coord e (ψ x) = x := by
    intro x hx
    simp only [ψ, dif_pos hx]
    exact (TL4.exists_e8Coord_eq he hx).choose_spec
  have hψ : ∀ v, ψ (TL4.e8Coord e v) = v := by
    intro v
    apply TL4.e8Coord_injective he
    exact hψe _ (TL4.e8Coord_mem he v)
  have hadd : ∀ x y, x ∈ zGroup Ω → y ∈ zGroup Ω → ψ (x * y) = ψ x + ψ y := by
    intro x y hx hy
    have hxy : x * y = TL4.e8Coord e (ψ x + ψ y) := by
      rw [TL4.e8Coord_add he, hψe x hx, hψe y hy]
    rw [hxy, hψ]
  have h1 : ψ 1 = 0 := by
    have := hψ 0
    rwa [TL4.e8Coord_zero] at this
  refine ⟨fun x => if x ∈ zGroup Ω then ψ x ⬝ᵥ w else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp [h1]
  · intro x hx
    simp [hx]
  · intro x hx y hy
    simp only [if_pos ((zGroup Ω).mul_mem hx hy), if_pos hx, if_pos hy]
    rw [hadd x y hx hy, add_dotProduct]
  · intro i
    have hi : ψ (e i) = Pi.single i 1 := by
      have := hψ (Pi.single i 1)
      rwa [TL4.e8Coord_single] at this
    simp [if_pos (he.mem i), hi, single_dotProduct]

theorem dagl_lab_bijOn {S : TwinShift Ω} {b : Lab2} (C : DewPointCoord S b) {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) {lab : Set (Subgroup G) → Fin 8}
    (hlab : ∀ X, lab X = TL4.binIdx (fun i => C.coord X (e i))) :
    Set.BijOn lab (dewPts S b) Set.univ := by
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · intro X hX Y hY hXY
    rw [hlab, hlab] at hXY
    have hv : (fun i => C.coord X (e i)) = fun i => C.coord Y (e i) := by
      have := congrArg TL4.bin hXY
      rwa [TL4.bin_binIdx, TL4.bin_binIdx] at this
    exact C.bijOn.injOn hX hY
      (h.dagl_coord_ext he (C.bijOn.mapsTo hX) (C.bijOn.mapsTo hY) (fun i => congrFun hv i))
  · intro i _
    obtain ⟨F, hF, hFi⟩ := h.dagl_exists_coord he (TL4.bin i)
    obtain ⟨X, hX, hXF⟩ := C.bijOn.surjOn hF
    refine ⟨X, hX, ?_⟩
    have hfun : (fun j => C.coord X (e j)) = TL4.bin i := by
      funext j
      rw [hXF, hFi]
    rw [hlab, hfun, TL4.binIdx_bin]

theorem dagl_coord_u {S : TwinShift Ω} {b : Lab2} (C : DewPointCoord S b) {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) {X : Set (Subgroup G)} (hX : X ∈ dewPts S b)
    (a : Fin 3 → ZMod 2) :
    C.coord X (TL4.e8Coord e a) = a ⬝ᵥ fun i => C.coord X (e i) :=
  h.dagl_coord_e8Coord he (C.bijOn.mapsTo hX) a

theorem dagl_mem_iff_coord {S : TwinShift Ω} {b : Lab2} (hb : b ≠ 0) (C : DewPointCoord S b)
    {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u) :
    ∃ c : ZMod 2, ∀ X ∈ dewPts S b, (K ∈ X ↔ C.coord X u = c) := by
  have huD : u ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨K, hK, hu⟩)
  obtain ⟨X₀, hX₀, hc₀⟩ := C.bijOn.surjOn h.dagl_zero_mem
  obtain ⟨K₀, hK₀X₀, hK₀u⟩ := h.pt_exists_mem S hX₀ huD hu.ne_one
  have hK₀ : K₀ ∈ Ω := hX₀.1 hK₀X₀
  obtain ⟨m, hm, -⟩ := h.exists_unique_shift S hK₀ ⟨hK, u, hK₀u, hu⟩
  refine ⟨dewQb b m, fun X hX => ?_⟩
  obtain ⟨q, hq, rfl⟩ := h.exists_pCore_conjSub_image S hb hX₀ hX
  have hcoord : C.coord (conjSub q '' X₀) u = dewQb b (S.lam q u) := by
    rw [C.qAct q hq X₀ hX₀, hc₀]
    simp
  have hq' : q⁻¹ ∈ pCore 2 G := (pCore 2 G).inv_mem hq
  have hconj : conjSub q⁻¹ K = S.shift (m + S.lam q u) K₀ := by
    rw [← hm, ← S.shift_conj m q⁻¹ K₀ hK₀,
      h.lam_spec S hq' (show K₀ ∈ dew1V Ω u from ⟨hK₀, hK₀u⟩), h.lam_inv S hq u,
      S.shift_add m _ K₀ hK₀]
  have hmem : K ∈ conjSub q '' X₀ ↔ conjSub q⁻¹ K ∈ X₀ := by
    constructor
    · rintro ⟨L, hL, rfl⟩
      rw [conjSub_inv_conjSub]
      exact hL
    · intro hL
      exact ⟨conjSub q⁻¹ K, hL, conjSub_conjSub_inv q K⟩
  rw [hcoord, hmem, hconj, h.pt_shift_mem S hb hX₀ hK₀X₀, dewQb_add b m _ hb]
  exact dagl_zmod_add_eq_zero_iff _ _

theorem dagl_shift_flip {S : TwinShift Ω} {b : Lab2} (hb : b ≠ 0) {K : Subgroup G} (hK : K ∈ Ω)
    {u : G} (hu : IsUniqueInvolution K u) {m : Lab2} (hm : dewQb b m = 1)
    {X : Set (Subgroup G)} (hX : X ∈ dewPts S b) : S.shift m K ∈ X ↔ K ∉ X := by
  have hX' : IsDewPoint S b X := hX
  have huD : u ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨K, hK, hu⟩)
  by_cases hKX : K ∈ X
  · constructor
    · intro h1
      exfalso
      have hmem : S.shift m K ∈ twinSet Ω K ∩ X := ⟨S.shift_mem m K hK, h1⟩
      rw [h.pt_twin_inter S hb hX' hKX] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h2 | h2
      · have hm0 : m = 0 := S.shift_injective hK (h2.trans (S.shift_zero K hK).symm)
        rw [hm0, dewQb_zero] at hm
        exact zero_ne_one hm
      · have hmb : m = b := S.shift_injective hK h2
        have h0 : dewQb b b = 0 := (dewQb_eq_zero_iff b b).mpr (Or.inr rfl)
        rw [hmb, h0] at hm
        exact zero_ne_one hm
    · intro hn
      exact absurd hKX hn
  · have hsh : S.shift m K ∈ X := by
      obtain ⟨M, hMX, hMu⟩ := h.pt_exists_mem S hX' huD hu.ne_one
      have hMΩ : M ∈ Ω := hX'.1 hMX
      obtain ⟨n, hn, -⟩ := h.exists_unique_shift S hK ⟨hMΩ, u, hu, hMu⟩
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [S.shift_zero K hK] at hn
        exact hKX (by rw [hn]; exact hMX)
      have hnb : n ≠ b := by
        intro hnb
        rw [hnb] at hn
        apply hKX
        have hbM : S.shift b M = K := by rw [← hn, S.shift_shift_self b hK]
        rw [← hbM]
        exact hX'.2.1 M hMX
      have hn1 : dewQb b n = 1 := by
        rcases zmod2_cases (dewQb b n) with h0 | h0
        · rw [dewQb_eq_zero_iff] at h0
          rcases h0 with h0 | h0
          · exact absurd h0 hn0
          · exact absurd h0 hnb
        · exact h0
      rcases dagl_flip_key b m n hb hm hn1 with h1 | h1
      · rw [h1, hn]
        exact hMX
      · rw [h1, S.shift_add b n K hK, hn]
        exact hX'.2.1 M hMX
    exact ⟨fun _ => hKX, fun _ => hsh⟩

theorem dagl_image_eq {S : TwinShift Ω} {b : Lab2} (C : DewPointCoord S b) {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) {lab : Set (Subgroup G) → Fin 8}
    (hlab : ∀ X, lab X = TL4.binIdx (fun i => C.coord X (e i)))
    (hbij : Set.BijOn lab (dewPts S b) Set.univ)
    {K : Subgroup G} {u : G} {a : Fin 3 → ZMod 2} (hua : TL4.e8Coord e a = u) {c : ZMod 2}
    (hc : ∀ X ∈ dewPts S b, (K ∉ X ↔ C.coord X u = c)) :
    lab '' {X | X ∈ dewPts S b ∧ K ∉ X} = ↑(TL4.hplane a c) := by
  have hcoordu : ∀ X ∈ dewPts S b, C.coord X u = a ⬝ᵥ fun i => C.coord X (e i) := by
    intro X hX
    rw [← hua]
    exact h.dagl_coord_u C he hX a
  ext x
  constructor
  · rintro ⟨X, ⟨hX, hKX⟩, rfl⟩
    simp only [Finset.mem_coe, TL4.hplane, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hlab, TL4.bin_binIdx, ← hcoordu X hX]
    exact (hc X hX).mp hKX
  · intro hx
    obtain ⟨X, hX, hXx⟩ := hbij.surjOn (Set.mem_univ x)
    refine ⟨X, ⟨hX, ?_⟩, hXx⟩
    rw [hc X hX, hcoordu X hX]
    have hx' : a ⬝ᵥ TL4.bin x = c := by
      simp only [Finset.mem_coe, TL4.hplane, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx
    have hbx : TL4.bin x = fun i => C.coord X (e i) := by
      rw [← hXx, hlab, TL4.bin_binIdx]
    rw [← hbx]
    exact hx'

theorem dagl_plane {S : TwinShift Ω} {b : Lab2} (hb : b ≠ 0) (C : DewPointCoord S b)
    {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) {lab : Set (Subgroup G) → Fin 8}
    (hlab : ∀ X, lab X = TL4.binIdx (fun i => C.coord X (e i)))
    (hbij : Set.BijOn lab (dewPts S b) Set.univ) :
    ∀ K ∈ Ω, ∃ α ∈ AE.e29Sets, (α : Set (Fin 8)) = lab '' {X | X ∈ dewPts S b ∧ K ∉ X} := by
  intro K hK
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
  have huD : u ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨K, hK, hu⟩)
  obtain ⟨a, hua⟩ := TL4.exists_e8Coord_eq he huD
  have ha : a ≠ 0 := by
    rintro rfl
    apply hu.ne_one
    rw [← hua, TL4.e8Coord_zero]
  obtain ⟨c₁, hc₁⟩ := h.dagl_mem_iff_coord hb C hK hu
  refine ⟨TL4.hplane a (c₁ + 1), TL4.hplane_mem a ha _, ?_⟩
  refine (h.dagl_image_eq C he hlab hbij hua (c := c₁ + 1) ?_).symm
  intro X hX
  exact (not_congr (hc₁ X hX)).trans (dagl_zmod_ne_iff _ _)

theorem dagl_plane_surj {S : TwinShift Ω} {b : Lab2} (hb : b ≠ 0) (C : DewPointCoord S b)
    {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) {lab : Set (Subgroup G) → Fin 8}
    (hlab : ∀ X, lab X = TL4.binIdx (fun i => C.coord X (e i)))
    (hbij : Set.BijOn lab (dewPts S b) Set.univ) :
    ∀ α ∈ AE.e29Sets, ∃ K ∈ Ω, (α : Set (Fin 8)) = lab '' {X | X ∈ dewPts S b ∧ K ∉ X} := by
  intro α hα
  obtain ⟨a, ha, c, rfl⟩ := TL4.exists_hplane (show α ∈ AE.affinePlanes from hα)
  have huD : TL4.e8Coord e a ∈ zGroup Ω := TL4.e8Coord_mem he a
  have hu1 : TL4.e8Coord e a ≠ 1 := by
    intro h1
    apply ha
    apply TL4.e8Coord_injective he
    rw [h1, TL4.e8Coord_zero]
  obtain ⟨K₁, hK₁, hK₁u⟩ := (h.mem_zGroup_iff.mp huD).resolve_left hu1
  obtain ⟨c₁, hc₁⟩ := h.dagl_mem_iff_coord hb C hK₁ hK₁u
  by_cases hcc : c = c₁ + 1
  · refine ⟨K₁, hK₁, (h.dagl_image_eq C he hlab hbij rfl (c := c) ?_).symm⟩
    intro X hX
    rw [hcc]
    exact (not_congr (hc₁ X hX)).trans (dagl_zmod_ne_iff _ _)
  · have hc' : c = c₁ := dagl_zmod_eq_of_ne c c₁ hcc
    obtain ⟨m, hm⟩ := lab2_exists_dewQb_one b hb
    refine ⟨S.shift m K₁, (S.shift_mem m K₁ hK₁).1,
      (h.dagl_image_eq C he hlab hbij rfl (c := c) ?_).symm⟩
    intro X hX
    have key : S.shift m K₁ ∉ X ↔ K₁ ∈ X := by
      rw [h.dagl_shift_flip hb hK₁ hK₁u hm hX, not_not]
    rw [key, hc₁ X hX, hc']

omit h in
theorem dagl_image_conjSub_mul (g g' : G) (Z : Set (Subgroup G)) :
    conjSub g '' (conjSub g' '' Z) = conjSub (g * g') '' Z := by
  rw [Set.image_image]
  congr 1
  funext K
  exact (conjSub_mul g g' K).symm

omit h in
theorem dagl_image_conjSub_mul_self (g g' : G) (Z : Set (Subgroup G)) (hg : g * g' = 1) :
    conjSub g '' (conjSub g' '' Z) = Z := by
  have h1 : conjSub (g * g') = id := funext fun K => by simp [hg, conjSub_one]
  rw [dagl_image_conjSub_mul, h1, Set.image_id]

theorem dagl_exists_sigma {S : TwinShift Ω} {b : Lab2} {lab : Set (Subgroup G) → Fin 8}
    (hbij : Set.BijOn lab (dewPts S b) Set.univ) :
    ∃ σ : G →* Equiv.Perm (Fin 8), ∀ g : G, ∀ X ∈ dewPts S b,
      lab (conjSub g '' X) = σ g (lab X) := by
  classical
  haveI : Nonempty (Set (Subgroup G)) := ⟨∅⟩
  obtain ⟨inv, hinv1, hinv2⟩ : ∃ inv : Fin 8 → Set (Subgroup G),
      (∀ X ∈ dewPts S b, inv (lab X) = X) ∧ ∀ i, inv i ∈ dewPts S b ∧ lab (inv i) = i :=
    ⟨Function.invFunOn lab (dewPts S b),
      fun X hX => hbij.injOn.leftInvOn_invFunOn hX,
      fun i => Function.invFunOn_pos (hbij.surjOn (Set.mem_univ i))⟩
  have hmem : ∀ g i, conjSub g '' inv i ∈ dewPts S b :=
    fun g i => h.isDewPoint_conjSub S (hinv2 i).1 g
  let τ : G → Equiv.Perm (Fin 8) := fun g =>
    { toFun := fun i => lab (conjSub g '' inv i)
      invFun := fun i => lab (conjSub g⁻¹ '' inv i)
      left_inv := fun i => by
        show lab (conjSub g⁻¹ '' inv (lab (conjSub g '' inv i))) = i
        rw [hinv1 _ (hmem g i), dagl_image_conjSub_mul_self g⁻¹ g _ (inv_mul_cancel g),
          (hinv2 i).2]
      right_inv := fun i => by
        show lab (conjSub g '' inv (lab (conjSub g⁻¹ '' inv i))) = i
        rw [hinv1 _ (hmem g⁻¹ i), dagl_image_conjSub_mul_self g g⁻¹ _ (mul_inv_cancel g),
          (hinv2 i).2] }
  have hmul : ∀ g g' : G, τ (g * g') = τ g * τ g' := by
    intro g g'
    refine Equiv.ext fun i => ?_
    show lab (conjSub (g * g') '' inv i) = lab (conjSub g '' inv (lab (conjSub g' '' inv i)))
    rw [hinv1 _ (hmem g' i), dagl_image_conjSub_mul]
  refine ⟨MonoidHom.mk' τ hmul, fun g X hX => ?_⟩
  show lab (conjSub g '' X) = lab (conjSub g '' inv (lab X))
  rw [hinv1 X hX]

theorem dagl_sigma_image {S : TwinShift Ω} {b : Lab2} {lab : Set (Subgroup G) → Fin 8}
    (hbij : Set.BijOn lab (dewPts S b) Set.univ) {σ : G →* Equiv.Perm (Fin 8)}
    (hσ : ∀ g : G, ∀ X ∈ dewPts S b, lab (conjSub g '' X) = σ g (lab X))
    (g : G) (K : Subgroup G) :
    σ g '' (lab '' {X | X ∈ dewPts S b ∧ K ∉ X}) =
      lab '' {X | X ∈ dewPts S b ∧ conjSub g K ∉ X} := by
  ext i
  constructor
  · rintro ⟨_, ⟨X, ⟨hX, hKX⟩, rfl⟩, rfl⟩
    refine ⟨conjSub g '' X, ⟨h.isDewPoint_conjSub S hX g, ?_⟩, hσ g X hX⟩
    rintro ⟨L, hL, hLK⟩
    have hLK' : L = K := conjSub_injective g hLK
    exact hKX (hLK' ▸ hL)
  · rintro ⟨Y, ⟨hY, hKY⟩, rfl⟩
    have hX : conjSub g⁻¹ '' Y ∈ dewPts S b := h.isDewPoint_conjSub S hY g⁻¹
    refine ⟨lab (conjSub g⁻¹ '' Y), ⟨conjSub g⁻¹ '' Y, ⟨hX, ?_⟩, rfl⟩, ?_⟩
    · rintro ⟨L, hL, hLK⟩
      apply hKY
      rw [← hLK, conjSub_conjSub_inv]
      exact hL
    · rw [← hσ g _ hX, dagl_image_conjSub_mul_self g g⁻¹ Y (mul_inv_cancel g)]

theorem dagl_sigma_mem {S : TwinShift Ω} {b : Lab2} {lab : Set (Subgroup G) → Fin 8}
    (hbij : Set.BijOn lab (dewPts S b) Set.univ) {σ : G →* Equiv.Perm (Fin 8)}
    (hσ : ∀ g : G, ∀ X ∈ dewPts S b, lab (conjSub g '' X) = σ g (lab X))
    (hplane : ∀ K ∈ Ω, ∃ α ∈ AE.e29Sets,
      (α : Set (Fin 8)) = lab '' {X | X ∈ dewPts S b ∧ K ∉ X})
    (hsurj : ∀ α ∈ AE.e29Sets, ∃ K ∈ Ω,
      (α : Set (Fin 8)) = lab '' {X | X ∈ dewPts S b ∧ K ∉ X})
    (g : G) : σ g ∈ AE.agl32 := by
  have key : ∀ g' : G, ∀ s ∈ AE.affinePlanes, s.map (σ g').toEmbedding ∈ AE.affinePlanes := by
    intro g' s hs
    obtain ⟨K, hK, hsK⟩ := hsurj s hs
    obtain ⟨α, hα, hαK⟩ := hplane (conjSub g' K) (S.conj_mem g' K hK)
    have hcoe : ((s.map (σ g').toEmbedding : Finset (Fin 8)) : Set (Fin 8)) =
        (α : Set (Fin 8)) := by
      rw [Finset.coe_map, Equiv.coe_toEmbedding, hsK, h.dagl_sigma_image hbij hσ g' K, hαK]
    have heq : s.map (σ g').toEmbedding = α := Finset.coe_injective hcoe
    rw [heq]
    exact hα
  show ∀ s ∈ AE.affinePlanes, s.map (σ g).toEmbedding ∈ AE.affinePlanes ∧
    s.map (σ g)⁻¹.toEmbedding ∈ AE.affinePlanes
  intro s hs
  refine ⟨key g s hs, ?_⟩
  rw [← map_inv σ g]
  exact key g⁻¹ s hs

theorem dagl_card_agl32 : Nat.card AE.agl32 = 1344 := by
  have hbij : Function.Bijective (fun p : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ×
      (Fin 3 → ZMod 2) => (⟨TL4.aperm p.1 p.2, TL4.aperm_mem_agl32 p.1 p.2⟩ : AE.agl32)) := by
    constructor
    · rintro ⟨A, b⟩ ⟨A', b'⟩ hAb
      have hv : TL4.aperm A b = TL4.aperm A' b' := congrArg Subtype.val hAb
      obtain ⟨h1, h2⟩ := TL4.aperm_inj hv
      rw [h1, h2]
    · rintro ⟨σ, hσ⟩
      obtain ⟨A, b, hAb⟩ := TL4.exists_aperm_eq hσ
      exact ⟨(A, b), Subtype.ext hAb⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, TL4.card_sl3Two, Nat.card_fun]
  simp

theorem exists_aglPts (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) : Nonempty (AGLPts S b) := by
  obtain ⟨C⟩ := h.exists_pointCoord S hb
  obtain ⟨e, he⟩ := h.exists_basis
  obtain ⟨lab, hlab⟩ : ∃ lab : Set (Subgroup G) → Fin 8,
      ∀ X, lab X = TL4.binIdx (fun i => C.coord X (e i)) :=
    ⟨fun X => TL4.binIdx (fun i => C.coord X (e i)), fun X => rfl⟩
  have hbij : Set.BijOn lab (dewPts S b) Set.univ := h.dagl_lab_bijOn C he hlab
  obtain ⟨σ, hσ⟩ := h.dagl_exists_sigma hbij
  have hplane := h.dagl_plane hb C he hlab hbij
  have hsurj := h.dagl_plane_surj hb C he hlab hbij
  have hker : σ.ker = dewA S b := by
    ext g
    rw [MonoidHom.mem_ker, ← h.forall_conjSub_image_eq_iff S hb g]
    constructor
    · intro hg X hX
      have hgX : lab (conjSub g '' X) = lab X := by
        rw [hσ g X hX, hg, Equiv.Perm.one_apply]
      exact hbij.injOn (h.isDewPoint_conjSub S hX g) hX hgX
    · intro hfix
      refine Equiv.ext fun i => ?_
      obtain ⟨X, hX, rfl⟩ := hbij.surjOn (Set.mem_univ i)
      rw [Equiv.Perm.one_apply, ← hσ g X hX, hfix X hX]
  have hG : Nat.card G = 512 * 168 := by
    have hidx := Subgroup.card_mul_index (Subgroup.centralizer (zGroup Ω : Set G))
    rw [h.index_centralizer_zGroup, h.centralizer_zGroup_eq_pCore, h.card_pCore_eq] at hidx
    omega
  have hrange : σ.range = AE.agl32 := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨g, rfl⟩
      exact h.dagl_sigma_mem hbij hσ hplane hsurj g
    · have hk := Subgroup.card_mul_index σ.ker
      rw [Subgroup.index_ker, hker, h.card_dewA S hb, hG] at hk
      have hA := h.dagl_card_agl32
      omega
  exact ⟨⟨lab, σ, hbij, hσ, hker, hrange, hplane, hsurj⟩⟩

end DE4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
