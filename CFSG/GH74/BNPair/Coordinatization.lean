module

public import CFSG.GH74.BNPair.Transfer
public import CFSG.GH74.BNPair.WeylIso

public noncomputable section

namespace CFSG.GH74.BNPair

universe u

open scoped Pointwise

namespace RankTwoSystem

variable {X X' : Type u} [Group X] [Group X'] {n : ℕ}

@[expose] def cuU (D : RankTwoSystem X n) (x : X) : D.U :=
  ⟨D.cu x, D.cu_mem_U x⟩

theorem mem_pgen_iff (D : RankTwoSystem X n) (i : Bool) {x : X} :
    x ∈ pgen D.B D.N D.w₁ D.w₂ i ↔ x ∈ D.B ∨ x ∈ dc D.B D.N (gen D.w₁ D.w₂ i) :=
  mem_parabolic_single_iff D.isTits (D.rank2.gen_mem i)

theorem B_le_pgen (D : RankTwoSystem X n) (i : Bool) {x : X} (hx : x ∈ D.B) :
    x ∈ pgen D.B D.N D.w₁ D.w₂ i :=
  (D.mem_pgen_iff i).2 (Or.inl hx)

open Classical in
theorem ell_lt_or_gt (D : RankTwoSystem X n) (i : Bool) (w : D.Weyl) :
    wordLength (({D.w₁, D.w₂} : Finset D.Weyl) : Set D.Weyl) (gen D.w₁ D.w₂ i * w) <
        wordLength (({D.w₁, D.w₂} : Finset D.Weyl) : Set D.Weyl) w ∨
      wordLength (({D.w₁, D.w₂} : Finset D.Weyl) : Set D.Weyl) w <
        wordLength (({D.w₁, D.w₂} : Finset D.Weyl) : Set D.Weyl) (gen D.w₁ D.w₂ i * w) := by
  rw [D.rank2.gens]
  have hs : gen D.w₁ D.w₂ i = D.w₁ ∨ gen D.w₁ D.w₂ i = D.w₂ := by
    cases i
    · exact Or.inr rfl
    · exact Or.inl rfl
  rcases D.rank2.dih.ell_gen_mul hs w with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end RankTwoSystem

namespace RankTwoSystem.Transfer

variable {X X' : Type u} [Group X] [Group X'] {n : ℕ} {D : RankTwoSystem X n}
  {D' : RankTwoSystem X' n} (T : Transfer D D')

@[expose] def Φ (x : X) : X' :=
  (D'.lift (T.ι (D.bw x)) : X') * ((T.φ (D.cuU x) : D'.U) : X')

theorem Φ_eq {x : X} {w : D.Weyl} {u : D.U} (hbw : D.bw x = w) (hcu : D.cu x = (u : X)) :
    T.Φ x = (D'.lift (T.ι w) : X') * ((T.φ u : D'.U) : X') := by
  have : D.cuU x = u := Subtype.ext hcu
  unfold Φ
  rw [hbw, this]

theorem Φ_mul_left {b : X} (hb : b ∈ D.B) (x : X) : T.Φ (b * x) = T.Φ x :=
  T.Φ_eq (D.bw_mul_left hb x) (D.cu_mul_left hb x)

theorem Φ_coord (x : X) :
    D'.bw (T.Φ x) = T.ι (D.bw x) ∧ D'.cu (T.Φ x) = ((T.φ (D.cuU x) : D'.U) : X') := by
  have hu : ((T.φ (D.cuU x) : D'.U) : X') ∈ D'.UwMinus (D'.lift (T.ι (D.bw x))) :=
    (T.UwMinus_iff (D.bw x) (D.cuU x)).1 (D.cu_mem x)
  have := D'.bw_cu_mk (w := T.ι (D.bw x)) (b := 1) D'.B.one_mem hu
  rw [one_mul] at this
  exact this

theorem exists_Φ_eq (y' : X') : ∃ x : X, y' * (T.Φ x)⁻¹ ∈ D'.B := by
  obtain ⟨b', hb', hy'⟩ := D'.exists_eq y'
  have hu' : D'.cu y' ∈ D'.UwMinus (D'.lift (D'.bw y')) := D'.cu_mem y'
  set w' := D'.bw y' with hw'
  have hw : T.ι (T.ι.symm w') = w' := Equiv.apply_symm_apply _ _
  set u : D.U := T.φ.symm ⟨D'.cu y', D'.cu_mem_U y'⟩ with hu_def
  have hφu : T.φ u = ⟨D'.cu y', D'.cu_mem_U y'⟩ := by rw [hu_def, MulEquiv.apply_symm_apply]
  have hu : (u : X) ∈ D.UwMinus (D.lift (T.ι.symm w')) := by
    rw [T.UwMinus_iff, hφu, hw]
    exact hu'
  obtain ⟨hbw, hcu⟩ := D.bw_cu_mk (w := T.ι.symm w') (b := 1) D.B.one_mem hu
  rw [one_mul] at hbw hcu
  refine ⟨(D.lift (T.ι.symm w') : X) * u, ?_⟩
  rw [T.Φ_eq hbw hcu, hw, hφu]
  have e : y' * ((D'.lift w' : X') * D'.cu y')⁻¹ = b' := by
    calc y' * ((D'.lift w' : X') * D'.cu y')⁻¹
        = (b' * (D'.lift w' : X') * D'.cu y') * ((D'.lift w' : X') * D'.cu y')⁻¹ := by
          rw [← hy']
      _ = b' := by group
  exact e ▸ hb'

theorem Φ_symm_Φ (x : X) : T.symm.Φ (T.Φ x) * x⁻¹ ∈ D.B := by
  rw [D.mul_inv_mem_B_iff]
  obtain ⟨h1, h2⟩ := T.Φ_coord x
  obtain ⟨h3, h4⟩ := T.symm.Φ_coord (T.Φ x)
  refine ⟨?_, ?_⟩
  · rw [h3, h1]
    exact Equiv.symm_apply_apply _ _
  · rw [h4]
    have : D'.cuU (T.Φ x) = T.φ (D.cuU x) := Subtype.ext h2
    rw [this]
    exact congrArg Subtype.val (T.φ.symm_apply_apply _)

theorem key (i : Bool) (x : X) :
    ∃ g : X, g * x⁻¹ ∈ pgen D.B D.N D.w₁ D.w₂ i ∧ D.bw g = gen D.w₁ D.w₂ i * D.bw x ∧
      T.Φ g * (T.Φ x)⁻¹ ∈ pgen D'.B D'.N D'.w₁ D'.w₂ i := by
  have hss : gen D.w₁ D.w₂ i * gen D.w₁ D.w₂ i = 1 := D.isTits.mul_self_gen (D.rank2.gen_mem i)
  set s := gen D.w₁ D.w₂ i with hs_def
  set s' := gen D'.w₁ D'.w₂ i with hs'_def
  obtain ⟨b₀, hb₀, hxe⟩ := D.exists_eq x
  have hcu : D.cu x ∈ D.UwMinus (D.lift (D.bw x)) := D.cu_mem x
  set w := D.bw x with hw_def
  set w'' := s * w with hw''
  have hsw : s * w'' = w := by rw [hw'', ← mul_assoc, hss, one_mul]
  obtain ⟨e, he, u'', hu'', hdec⟩ := D.U_eq_mul' (D.lift w'') (D.cu x) hcu.1
  set ms : D.N := D.lift s with hms
  set nn : D.N := D.lift w'' with hnn
  have hl : ((ms * nn : D.N) : D.Weyl) = w := by
    rw [QuotientGroup.mk_mul, hms, hnn, D.lift_mk, D.lift_mk]
    exact hsw
  have hh : (D.lift w : X)⁻¹ * ((ms * nn : D.N) : X) ∈ D.B :=
    mk_eq_mk_iff.1 ((D.lift_mk w).trans hl.symm)
  have hhN : (D.lift w : X)⁻¹ * ((ms * nn : D.N) : X) ∈ D.N :=
    D.N.mul_mem (D.N.inv_mem (D.lift w).2) (ms * nn).2
  set h : X := (D.lift w : X)⁻¹ * ((ms * nn : D.N) : X) with hh_def
  have hlw : (D.lift w : X) = (ms : X) * (nn : X) * h⁻¹ := by
    rw [hh_def, Subgroup.coe_mul]
    group
  have hxe' : x = b₀ * ((ms : X) * (nn : X) * h⁻¹) * (e * u'') := by
    calc x = b₀ * (D.lift w : X) * D.cu x := hxe
      _ = b₀ * ((ms : X) * (nn : X) * h⁻¹) * (e * u'') := by rw [hlw, hdec]
  have hmem1 : (nn : X) * h⁻¹ * (nn : X)⁻¹ ∈ D.B ⊓ D.N :=
    D.conj_cartan_mem nn (Subgroup.inv_mem _ (⟨hh, hhN⟩ : h ∈ D.B ⊓ D.N))
  set b₁ : X := (nn : X) * h⁻¹ * (nn : X)⁻¹ * ((nn : X) * e * (nn : X)⁻¹) with hb₁_def
  have hb₁ : b₁ ∈ D.B := D.B.mul_mem hmem1.1 (D.U_le_B he.2)
  set p : X := b₀ * (ms : X) * b₁ with hp_def
  set g : X := (nn : X) * u'' with hg_def
  have hxg : x = p * g := by
    rw [hxe']
    simp only [hp_def, hg_def, hb₁_def]
    group
  have hp : p ∈ dc D.B D.N s :=
    (mem_dc_of_lift (n := ms) (D.lift_mk s)).2 ⟨b₀, hb₀, b₁, hb₁, rfl⟩
  have hgx : g * x⁻¹ = p⁻¹ := by
    have : g * x⁻¹ = g * (p * g)⁻¹ := by rw [← hxg]
    rw [this]
    group
  have hgbw : D.bw g = w'' ∧ D.cu g = u'' := by
    have := D.bw_cu_mk (w := w'') (b := 1) D.B.one_mem hu''
    rw [one_mul] at this
    exact this
  refine ⟨g, ?_, hgbw.1, ?_⟩
  · rw [hgx]
    exact Subgroup.inv_mem _ ((D.mem_pgen_iff i).2 (Or.inr hp))
  set ms' : D'.N := D'.lift s' with hms'
  set nn' : D'.N := D'.lift (T.ι w'') with hnn'
  have hl' : ((ms' * nn' : D'.N) : D'.Weyl) = T.ι w := by
    rw [QuotientGroup.mk_mul, hms', hnn', D'.lift_mk, D'.lift_mk, ← T.ι_gen i w'' , hsw]
  have hh' : (D'.lift (T.ι w) : X')⁻¹ * ((ms' * nn' : D'.N) : X') ∈ D'.B :=
    mk_eq_mk_iff.1 ((D'.lift_mk _).trans hl'.symm)
  have hhN' : (D'.lift (T.ι w) : X')⁻¹ * ((ms' * nn' : D'.N) : X') ∈ D'.N :=
    D'.N.mul_mem (D'.N.inv_mem (D'.lift (T.ι w)).2) (ms' * nn').2
  set h' : X' := (D'.lift (T.ι w) : X')⁻¹ * ((ms' * nn' : D'.N) : X') with hh'_def
  have hlw' : (D'.lift (T.ι w) : X') = (ms' : X') * (nn' : X') * h'⁻¹ := by
    rw [hh'_def, Subgroup.coe_mul]
    group
  have hmem1' : (nn' : X') * h'⁻¹ * (nn' : X')⁻¹ ∈ D'.B ⊓ D'.N :=
    D'.conj_cartan_mem nn' (Subgroup.inv_mem _ (⟨hh', hhN'⟩ : h' ∈ D'.B ⊓ D'.N))
  have heU : e ∈ D.U := he.1
  have hu''U : u'' ∈ D.U := hu''.1
  have hφe : ((T.φ ⟨e, heU⟩ : D'.U) : X') ∈ D'.UwPlus (D'.lift (T.ι w'')) :=
    (T.UwPlus_iff w'' ⟨e, heU⟩).1 he
  set φe : X' := ((T.φ ⟨e, heU⟩ : D'.U) : X') with hφe_def
  set φu : X' := ((T.φ ⟨u'', hu''U⟩ : D'.U) : X') with hφu_def
  have hΦg : T.Φ g = (nn' : X') * φu := T.Φ_eq (u := ⟨u'', hu''U⟩) hgbw.1 hgbw.2
  have hΦx : T.Φ x = (D'.lift (T.ι w) : X') * (φe * φu) := by
    have h1 : D.cuU x = ⟨e, heU⟩ * ⟨u'', hu''U⟩ := Subtype.ext hdec
    unfold Φ
    rw [h1, map_mul]
    rfl
  set b₂ : X' := (nn' : X') * h'⁻¹ * (nn' : X')⁻¹ * ((nn' : X') * φe * (nn' : X')⁻¹) with hb₂_def
  have hb₂ : b₂ ∈ D'.B := D'.B.mul_mem hmem1'.1 (D'.U_le_B hφe.2)
  have hq : T.Φ x * (T.Φ g)⁻¹ = (ms' : X') * b₂ := by
    rw [hΦg, hΦx, hlw', hb₂_def]
    group
  have hqmem : (ms' : X') * b₂ ∈ dc D'.B D'.N s' :=
    (mem_dc_of_lift (n := ms') (D'.lift_mk s')).2 ⟨1, D'.B.one_mem, b₂, hb₂, by simp⟩
  have : T.Φ g * (T.Φ x)⁻¹ = ((ms' : X') * b₂)⁻¹ := by
    rw [← hq]
    group
  rw [this]
  exact Subgroup.inv_mem _ ((D'.mem_pgen_iff i).2 (Or.inr hqmem))

open Classical in
theorem step (i : Bool) {x y : X} (h : y * x⁻¹ ∈ pgen D.B D.N D.w₁ D.w₂ i) :
    T.Φ y * (T.Φ x)⁻¹ ∈ pgen D'.B D'.N D'.w₁ D'.w₂ i := by
  have hs := D.rank2.gen_mem i
  have hss : gen D.w₁ D.w₂ i * gen D.w₁ D.w₂ i = 1 := D.isTits.mul_self_gen hs
  set s := gen D.w₁ D.w₂ i with hs_def
  have hy : y = (y * x⁻¹) * x := by group
  have hinv : x * y⁻¹ ∈ pgen D.B D.N D.w₁ D.w₂ i := by
    have := Subgroup.inv_mem _ h
    simpa using this
  have hΦinv : ∀ {a b : X}, T.Φ a * (T.Φ b)⁻¹ ∈ pgen D'.B D'.N D'.w₁ D'.w₂ i →
      T.Φ b * (T.Φ a)⁻¹ ∈ pgen D'.B D'.N D'.w₁ D'.w₂ i := by
    intro a b hab
    have := Subgroup.inv_mem _ hab
    simpa using this
  rcases (D.mem_pgen_iff i).1 h with hB | hdc
  · have : T.Φ y = T.Φ x := by
      rw [hy]
      exact T.Φ_mul_left hB x
    rw [this, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hmul : y ∈ dc D.B D.N s * dc D.B D.N (D.bw x) :=
    Set.mem_mul.2 ⟨y * x⁻¹, hdc, x, D.mem_dc_bw x, by group⟩
  rcases D.ell_lt_or_gt i (D.bw x) with hlen | hlen
  ·
    obtain ⟨gx, hgx1, hgx2, hgx3⟩ := T.key i x
    have hyc : y ∈ dc D.B D.N (s * D.bw x) ∪ dc D.B D.N (D.bw x) :=
      D.isTits.bnCore.mul_subset s (Finset.mem_coe.2 hs) (D.bw x) hmul
    have hgxdc : gx ∈ dc D.B D.N (s * D.bw x) := by
      rw [← hgx2]
      exact D.mem_dc_bw gx
    rcases hyc with hy1 | hy2
    · have hbB := WPos.panel_unique D.isTits hs hlen (x := 1) (y := x) (z := gx) (z' := y)
        hgx1 h (by simpa [WPos] using hgxdc) (by simpa [WPos] using hy1)
      have hΦ : T.Φ y = T.Φ gx := by
        have e : y = (y * gx⁻¹) * gx := by group
        rw [e]
        exact T.Φ_mul_left hbB gx
      rw [hΦ]
      exact hgx3
    · have hbwy : D.bw y = D.bw x := D.bw_eq hy2
      obtain ⟨gy, hgy1, hgy2, hgy3⟩ := T.key i y
      have hgygx : gy * x⁻¹ ∈ pgen D.B D.N D.w₁ D.w₂ i := by
        have := Subgroup.mul_mem _ hgy1 h
        simpa [mul_assoc] using this
      have hgydc : gy ∈ dc D.B D.N (s * D.bw x) := by
        rw [← hbwy, ← hgy2]
        exact D.mem_dc_bw gy
      have hbB := WPos.panel_unique D.isTits hs hlen (x := 1) (y := x) (z := gx) (z' := gy)
        hgx1 hgygx (by simpa [WPos] using hgxdc) (by simpa [WPos] using hgydc)
      have hΦ : T.Φ gy = T.Φ gx := by
        have e : gy = (gy * gx⁻¹) * gx := by group
        rw [e]
        exact T.Φ_mul_left hbB gx
      have h1 := hΦinv hgy3
      rw [hΦ] at h1
      have := Subgroup.mul_mem _ h1 hgx3
      simpa [mul_assoc] using this
  ·
    have hysub : y ∈ dc D.B D.N (s * D.bw x) :=
      D.isTits.bnCore.mul_subset_of_lt (Finset.mem_coe.2 hs) (D.isTits.mem_closure (D.bw x)) hlen
        hmul
    have hbwy : D.bw y = s * D.bw x := D.bw_eq hysub
    obtain ⟨gy, hgy1, hgy2, hgy3⟩ := T.key i y
    have hgy_w : D.bw gy = D.bw x := by
      rw [hgy2, hbwy, ← mul_assoc, hss, one_mul]
    have hlen2 : wordLength (({D.w₁, D.w₂} : Finset D.Weyl) : Set D.Weyl) (s * D.bw y) <
        wordLength (({D.w₁, D.w₂} : Finset D.Weyl) : Set D.Weyl) (D.bw y) := by
      rw [hbwy, ← mul_assoc, hss, one_mul]
      exact hlen
    have hxdc : x ∈ dc D.B D.N (s * D.bw y) := by
      rw [hbwy, ← mul_assoc, hss, one_mul]
      exact D.mem_dc_bw x
    have hgydc : gy ∈ dc D.B D.N (s * D.bw y) := by
      rw [hbwy, ← mul_assoc, hss, one_mul, ← hgy_w]
      exact D.mem_dc_bw gy
    have hbB := WPos.panel_unique D.isTits hs hlen2 (x := 1) (y := y) (z := x) (z' := gy)
      hinv hgy1 (by simpa [WPos] using hxdc) (by simpa [WPos] using hgydc)
    have hΦ : T.Φ gy = T.Φ x := by
      have e : gy = (gy * x⁻¹) * x := by group
      rw [e]
      exact T.Φ_mul_left hbB x
    rw [hΦ] at hgy3
    exact hΦinv hgy3

theorem step_iff (i : Bool) {x y : X} :
    y * x⁻¹ ∈ pgen D.B D.N D.w₁ D.w₂ i ↔
      T.Φ y * (T.Φ x)⁻¹ ∈ pgen D'.B D'.N D'.w₁ D'.w₂ i := by
  refine ⟨T.step i, fun h => ?_⟩
  have h1 := T.symm.step i h
  have hx := T.Φ_symm_Φ x
  have hy := T.Φ_symm_Φ y
  set a := T.symm.Φ (T.Φ y)
  set b := T.symm.Φ (T.Φ x)
  have e : y * x⁻¹ = (a * y⁻¹)⁻¹ * (a * b⁻¹) * (b * x⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (D.B_le_pgen i (D.B.inv_mem hy)) h1)
    (D.B_le_pgen i hx)

end RankTwoSystem.Transfer

namespace RankTwoSystem

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem exists_vtx_rep (v : D.Vertex) :
    ∃ x : X, v = vtx D.B D.N D.w₁ D.w₂ (vtype D.B D.N D.w₁ D.w₂ v) x := by
  obtain ⟨i, x, rfl⟩ := exists_vtx v
  exact ⟨x, by rw [D.rank2.vtype_vtx]⟩

theorem adj_iff {u v : D.Vertex} :
    D.graph.Adj u v ↔ ∃ (i : Bool) (z : X), u = vtx D.B D.N D.w₁ D.w₂ i z ∧
      v = vtx D.B D.N D.w₁ D.w₂ (!i) z := by
  constructor
  · intro h
    obtain ⟨z, hzu, hzv⟩ := h.2
    refine ⟨vtype D.B D.N D.w₁ D.w₂ u, z, D.rank2.eq_vtx_of_mem hzu, ?_⟩
    exact D.rank2.eq_vtx_not_of_adj h hzv
  · rintro ⟨i, z, rfl, rfl⟩
    refine ⟨?_, z, mem_self_vtx, mem_self_vtx⟩
    intro h
    have := D.rank2.vtx_type_eq h
    cases i <;> simp at this

end RankTwoSystem

namespace RankTwoSystem.Transfer

variable {X X' : Type u} [Group X] [Group X'] {n : ℕ} {D : RankTwoSystem X n}
  {D' : RankTwoSystem X' n} (T : Transfer D D')

@[expose] def Ψ (v : D.Vertex) : D'.Vertex :=
  vtx D'.B D'.N D'.w₁ D'.w₂ (vtype D.B D.N D.w₁ D.w₂ v)
    (T.Φ (Classical.choose (D.exists_vtx_rep v)))

theorem Ψ_vtx (i : Bool) (x : X) :
    T.Ψ (vtx D.B D.N D.w₁ D.w₂ i x) = vtx D'.B D'.N D'.w₁ D'.w₂ i (T.Φ x) := by
  set v := vtx D.B D.N D.w₁ D.w₂ i x with hv
  have hty : vtype D.B D.N D.w₁ D.w₂ v = i := D.rank2.vtype_vtx i x
  have hx₀ := Classical.choose_spec (D.exists_vtx_rep v)
  set x₀ := Classical.choose (D.exists_vtx_rep v) with hx₀_def
  rw [hty] at hx₀
  have hmem : x ∈ ((vtx D.B D.N D.w₁ D.w₂ i x₀ : D.Vertex) : Set X) := by
    rw [← hx₀]
    exact mem_self_vtx
  have h1 := mem_vtx.1 hmem
  have h2 := T.step i h1
  have e : vtx D'.B D'.N D'.w₁ D'.w₂ (vtype D.B D.N D.w₁ D.w₂ v) (T.Φ x₀) =
      vtx D'.B D'.N D'.w₁ D'.w₂ i (T.Φ x₀) := by rw [hty]
  exact e.trans (vtx_eq_vtx h2).symm

theorem Ψ_injective : Function.Injective T.Ψ := by
  intro u v huv
  obtain ⟨i, x, rfl⟩ := exists_vtx u
  obtain ⟨j, y, rfl⟩ := exists_vtx v
  rw [T.Ψ_vtx, T.Ψ_vtx] at huv
  have hij : i = j := D'.rank2.vtx_type_eq huv
  subst hij
  have hmem : T.Φ x ∈ ((vtx D'.B D'.N D'.w₁ D'.w₂ i (T.Φ y) : D'.Vertex) : Set X') := by
    rw [← huv]
    exact mem_self_vtx
  have h1 := mem_vtx.1 hmem
  have h2 := (T.step_iff i).2 h1
  exact vtx_eq_vtx h2

theorem Ψ_surjective : Function.Surjective T.Ψ := by
  intro v'
  obtain ⟨j, y', rfl⟩ := exists_vtx v'
  obtain ⟨x, hx⟩ := T.exists_Φ_eq y'
  refine ⟨vtx D.B D.N D.w₁ D.w₂ j x, ?_⟩
  rw [T.Ψ_vtx]
  exact (vtx_eq_vtx (D'.B_le_pgen j hx)).symm

theorem adj_Ψ_iff {a b : D.Vertex} : D'.graph.Adj (T.Ψ a) (T.Ψ b) ↔ D.graph.Adj a b := by
  constructor
  · intro h
    obtain ⟨i, z', h1, h2⟩ := D'.adj_iff.1 h
    obtain ⟨x, hx⟩ := T.exists_Φ_eq z'
    have e1 : T.Ψ a = T.Ψ (vtx D.B D.N D.w₁ D.w₂ i x) := by
      rw [h1, T.Ψ_vtx]
      exact vtx_eq_vtx (D'.B_le_pgen i hx)
    have e2 : T.Ψ b = T.Ψ (vtx D.B D.N D.w₁ D.w₂ (!i) x) := by
      rw [h2, T.Ψ_vtx]
      exact vtx_eq_vtx (D'.B_le_pgen (!i) hx)
    exact D.adj_iff.2 ⟨i, x, T.Ψ_injective e1, T.Ψ_injective e2⟩
  · intro h
    obtain ⟨i, z, rfl, rfl⟩ := D.adj_iff.1 h
    rw [T.Ψ_vtx, T.Ψ_vtx]
    exact D'.adj_iff.2 ⟨i, T.Φ z, rfl, rfl⟩

@[expose] def graphIso : D.graph ≃g D'.graph :=
  ⟨Equiv.ofBijective T.Ψ ⟨T.Ψ_injective, T.Ψ_surjective⟩, fun {_ _} => T.adj_Ψ_iff⟩

end RankTwoSystem.Transfer

theorem coordIso : CoordIso.{u} := by
  intro X X' _ _ n D D' φ hφ
  obtain ⟨ι, h1, h2, h3, h4⟩ := D.rank2.dih.exists_weylIso D'.rank2.dih
  exact ⟨(⟨φ, hφ, ι, h1, h2, h3, h4⟩ : RankTwoSystem.Transfer D D').graphIso⟩

theorem theorem30_4 : Theorem30_4.{u} :=
  theorem30_4_of_coordIso coordIso

end CFSG.GH74.BNPair
