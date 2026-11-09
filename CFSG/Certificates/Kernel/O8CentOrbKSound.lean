module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Native

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2

@[expose] def orbCertK (E : Enum) (b : ℕ) (rs cs : Array ℕ) : Bool :=
  rs.size == cs.size && sortedK cs &&
    (List.range cs.size).all fun i => decide (cs.getD i 0 < 2 ^ 144) &&
      memK E.keys (rs.getD i 0) && mulK (cs.getD i 0) (rs.getD i 0) == mulK (rs.getD i 0) b

theorem centInCheck_of_orbCertK {gs gs₂ : Array (ℕ × ℕ)} {E E₂ : Enum} {b b' : ℕ}
    {rs cs : Array ℕ} (hE : enumOK gs E = true) (hE₂ : enumOK gs₂ E₂ = true)
    (hsz : E₂.keys.size < 2 ^ 64) (hb : invPair b b' = true) (hin : gensIn gs₂ E = true)
    (hc : commGens gs₂ b = true) (ho : orbCertK E b rs cs = true)
    (hcard : E.keys.size ≤ cs.size * E₂.keys.size) : centInCheck E b E₂ = true := by
  obtain ⟨y, hy⟩ : ∃ y, Rep b y := ⟨_, rep_glOf hb⟩
  have hg₂ := (Enum.of_enumOK hE₂).1
  obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup (grpOf gs), Z = (Subgroup.centralizer {y}).subgroupOf _ :=
    ⟨_, rfl⟩
  have hKH : grpOf gs₂ ≤ grpOf gs := grpOf_le_of_gensIn hg₂ hE hin
  have hmemZ : ∀ x : grpOf gs, y * x = x * y → x ∈ Z := by
    intro x hx
    rw [hZdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hx
  have hKZ : (grpOf gs₂).subgroupOf (grpOf gs) ≤ Z := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    exact hmemZ x (commute_of_commGens hg₂ hy hc _ hx)
  simp only [orbCertK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at ho
  obtain ⟨⟨-, hs⟩, hall⟩ := ho
  have hrep : ∀ i : Fin cs.size, ∃ x ∈ grpOf gs, Rep (rs.getD i 0) x :=
    fun i => Enum.rep_of_memK hE (hall i i.2).1.2
  choose f hf using hrep
  have hconj : ∀ i : Fin cs.size,
      toMatK (cs.getD i 0) = ((f i * y * (f i)⁻¹ : GL12) : Mat12) := by
    intro i
    have e := congrArg toMatK (hall i i.2).2
    have h1 : toMatK (rs.getD i 0) = (f i : Mat12) := (hf i).2
    have h2 : toMatK b = (y : Mat12) := hy
    rw [toMatK_mulK, toMatK_mulK, h1, h2] at e
    rw [Units.val_mul, Units.val_mul, ← e, mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, mul_one]
  have hF : Function.Injective
      fun i : Fin cs.size => ((⟨f i, (hf i).1⟩ : grpOf gs) : grpOf gs ⧸ Z) := by
    intro i j e
    rw [QuotientGroup.eq, hZdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at e
    have e2 : y * ((f i)⁻¹ * f j) = (f i)⁻¹ * f j * y := e y (Set.mem_singleton y)
    have e3 : f i * y * (f i)⁻¹ = f j * y * (f j)⁻¹ :=
      calc f i * y * (f i)⁻¹ = f i * (y * ((f i)⁻¹ * f j)) * (f j)⁻¹ := by group
        _ = f i * ((f i)⁻¹ * f j * y) * (f j)⁻¹ := by rw [e2]
        _ = f j * y * (f j)⁻¹ := by group
    have e4 : cs.getD i 0 = cs.getD j 0 :=
      eq_of_toMatK_eq (hall i i.2).1.1 (hall j j.2).1.1 (by rw [hconj i, hconj j, e3])
    rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
    · exact absurd e4 (Enum.lt_of_sortedK hs hij j.2).ne
    · exact Fin.ext hij
    · exact absurd e4 (Enum.lt_of_sortedK hs hij i.2).ne'
  have hidx : cs.size ≤ Z.index := by
    have := Nat.card_le_card_of_injective _ hF
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have hmul := Subgroup.card_mul_index Z
  rw [Enum.card_eq hE] at hmul
  have hpos : 0 < Z.index := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have h1 := Enum.card_eq hE
    have h2 := Nat.card_pos (α := grpOf gs)
    rw [h0, mul_zero] at hmul
    omega
  have hK' : Nat.card ((grpOf gs₂).subgroupOf (grpOf gs)) = E₂.keys.size := by
    rw [← Enum.card_eq hE₂]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hZle : Nat.card Z ≤ E₂.keys.size := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card Z * Z.index = E.keys.size := hmul
      _ ≤ cs.size * E₂.keys.size := hcard
      _ ≤ Z.index * E₂.keys.size := Nat.mul_le_mul_right _ hidx
      _ = E₂.keys.size * Z.index := Nat.mul_comm _ _
  have hZ : (grpOf gs₂).subgroupOf (grpOf gs) = Z :=
    Subgroup.eq_of_le_of_card_ge hKZ (by rw [hK']; exact hZle)
  simp only [centInCheck, Array.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
  intro i hi
  rw [← getD_mem hi]
  by_cases hcm : mulK (E.keys.getD i 0) b = mulK b (E.keys.getD i 0)
  · right
    obtain ⟨x, hx, hr⟩ := Enum.exists_mem hE i hi
    have hxy : x * y = y * x := (hr.mul hy).unique (by rw [hcm]; exact hy.mul hr)
    have hxZ := hmemZ ⟨x, hx⟩ hxy.symm
    rw [← hZ, Subgroup.mem_subgroupOf] at hxZ
    exact Enum.memK_of_mem' hE₂ hsz hxZ hr (Enum.key_lt hE hi)
  · left
    exact hcm

end CFSG.KC.O8
