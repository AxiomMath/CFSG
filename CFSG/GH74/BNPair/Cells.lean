module

public import CFSG.GH74.BNPair.Eq305
public import CFSG.GH74.BNPair.Lemma309

public noncomputable section

namespace CFSG.GH74.BNPair

universe u

open scoped Pointwise

namespace RankTwoSystem

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

@[expose] def lift (w : D.Weyl) : D.N :=
  Classical.choose (QuotientGroup.mk_surjective w)

theorem lift_mk (w : D.Weyl) : ((D.lift w : D.N) : D.Weyl) = w :=
  Classical.choose_spec (QuotientGroup.mk_surjective w)

@[expose] def Vm : Subgroup X :=
  Classical.choose D.Uminus_isSubgroup

theorem coe_Vm : (D.Vm : Set X) = D.Uminus :=
  Classical.choose_spec D.Uminus_isSubgroup

theorem mem_Vm_iff {x : X} : x ∈ D.Vm ↔ x ∈ D.Uminus := by
  rw [← SetLike.mem_coe, D.coe_Vm]

@[expose] def UwMinusSub (m : D.N) : Subgroup X where
  carrier := D.UwMinus m
  mul_mem' := by
    rintro a b ⟨haU, ha⟩ ⟨hbU, hb⟩
    refine ⟨D.U.mul_mem haU hbU, ?_⟩
    rw [← D.mem_Vm_iff] at ha hb ⊢
    have e : (m : X) * (a * b) * (m : X)⁻¹ = ((m : X) * a * (m : X)⁻¹) * ((m : X) * b * (m : X)⁻¹) := by
      group
    rw [e]
    exact D.Vm.mul_mem ha hb
  one_mem' := by
    refine ⟨D.U.one_mem, ?_⟩
    rw [← D.mem_Vm_iff]
    simp
  inv_mem' := by
    rintro a ⟨haU, ha⟩
    refine ⟨D.U.inv_mem haU, ?_⟩
    rw [← D.mem_Vm_iff] at ha ⊢
    have e : (m : X) * a⁻¹ * (m : X)⁻¹ = ((m : X) * a * (m : X)⁻¹)⁻¹ := by group
    rw [e]
    exact D.Vm.inv_mem ha

@[expose] def UwPlusSub (m : D.N) : Subgroup X where
  carrier := D.UwPlus m
  mul_mem' := by
    rintro a b ⟨haU, ha⟩ ⟨hbU, hb⟩
    refine ⟨D.U.mul_mem haU hbU, ?_⟩
    have e : (m : X) * (a * b) * (m : X)⁻¹ = ((m : X) * a * (m : X)⁻¹) * ((m : X) * b * (m : X)⁻¹) := by
      group
    rw [e]
    exact D.U.mul_mem ha hb
  one_mem' := ⟨D.U.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨haU, ha⟩
    refine ⟨D.U.inv_mem haU, ?_⟩
    have e : (m : X) * a⁻¹ * (m : X)⁻¹ = ((m : X) * a * (m : X)⁻¹)⁻¹ := by group
    rw [e]
    exact D.U.inv_mem ha

theorem mem_UwMinus_iff {m : D.N} {x : X} :
    x ∈ D.UwMinus m ↔ x ∈ D.U ∧ (m : X) * x * (m : X)⁻¹ ∈ D.Vm := by
  rw [D.mem_Vm_iff]
  rfl

theorem UwMinus_le_U {m : D.N} {x : X} (hx : x ∈ D.UwMinus m) : x ∈ D.U := hx.1

theorem UwPlus_le_U {m : D.N} {x : X} (hx : x ∈ D.UwPlus m) : x ∈ D.U := hx.1

theorem eq_one_of_mem_U_Vm {z : X} (hzB : z ∈ D.B) (hz : z ∈ D.Vm) : z = 1 :=
  D.roots.meet_one z hzB ((D.mem_Vm_iff).1 hz)

theorem U_eq_mul (m : D.N) : ∀ x ∈ D.U, ∃ a ∈ D.UwMinus m, ∃ c ∈ D.UwPlus m, x = a * c := by
  intro x hx
  have hn := D.three_le
  obtain ⟨t, ht, hw | hw⟩ := D.rank2.dih.exists_altWord (m : D.Weyl)
  · obtain ⟨h1, h2⟩ := D.eq30_5_A ht m hw
    obtain ⟨a, ha, c, hc, rfl⟩ := U_decomp ht x hx
    exact ⟨a, by rw [h1]; exact ha, c, by rw [h2]; exact hc, rfl⟩
  · obtain ⟨h1, h2⟩ := D.eq30_5_B ht m hw
    obtain ⟨a, ha, c, hc, hxinv⟩ := U_decomp' ht x⁻¹ (D.U.inv_mem hx)
    have hc' : c ∈ D.UwMinus m := by
      rw [h1, ← chainProd_intList_reverse D (by omega) le_rfl]
      exact hc
    have ha' : a ∈ D.UwPlus m := by
      rw [h2, ← chainProd_intList_reverse D (by omega) (by omega)]
      exact ha
    refine ⟨c⁻¹, (D.UwMinusSub m).inv_mem hc', a⁻¹, (D.UwPlusSub m).inv_mem ha', ?_⟩
    have : x = (a * c)⁻¹ := by rw [← hxinv]; simp
    rw [this, mul_inv_rev]

theorem U_eq_mul' (m : D.N) : ∀ x ∈ D.U, ∃ c ∈ D.UwPlus m, ∃ a ∈ D.UwMinus m, x = c * a := by
  intro x hx
  obtain ⟨a, ha, c, hc, hxinv⟩ := D.U_eq_mul m x⁻¹ (D.U.inv_mem hx)
  refine ⟨c⁻¹, (D.UwPlusSub m).inv_mem hc, a⁻¹, (D.UwMinusSub m).inv_mem ha, ?_⟩
  have : x = (a * c)⁻¹ := by rw [← hxinv]; simp
  rw [this, mul_inv_rev]

theorem mem_dc_iff_coord (m : D.N) {w : D.Weyl} (hm : (m : D.Weyl) = w) {x : X} :
    x ∈ dc D.B D.N w ↔ ∃ b ∈ D.B, ∃ u ∈ D.UwMinus m, x = b * (m : X) * u := by
  constructor
  · intro hx
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_dc_of_lift hm).1 hx
    have hb₂' : b₂ ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb₂
    obtain ⟨h, hh, u₀, hu₀, rfl⟩ := Set.mem_mul.1 hb₂'
    obtain ⟨c, hc, a, ha, rfl⟩ := D.U_eq_mul' m u₀ hu₀
    refine ⟨b₁ * ((m : X) * h * (m : X)⁻¹) * ((m : X) * c * (m : X)⁻¹), ?_, a, ha, ?_⟩
    · exact D.B.mul_mem (D.B.mul_mem hb₁ (D.conj_cartan_mem m hh).1) (D.U_le_B hc.2)
    · group
  · rintro ⟨b, hb, u, hu, rfl⟩
    exact (mem_dc_of_lift hm).2 ⟨b, hb, u, D.U_le_B hu.1, rfl⟩

theorem coord_unique (m : D.N) {b b' u u' : X} (hb : b ∈ D.B) (hb' : b' ∈ D.B)
    (hu : u ∈ D.UwMinus m) (hu' : u' ∈ D.UwMinus m)
    (h : b * (m : X) * u = b' * (m : X) * u') : u = u' := by
  have h1 : (m : X) * (u * u'⁻¹) * (m : X)⁻¹ = b⁻¹ * b' := by
    have : (m : X) * u = b⁻¹ * b' * (m : X) * u' := by
      calc (m : X) * u = b⁻¹ * (b * (m : X) * u) := by group
        _ = b⁻¹ * (b' * (m : X) * u') := by rw [h]
        _ = b⁻¹ * b' * (m : X) * u' := by group
    calc (m : X) * (u * u'⁻¹) * (m : X)⁻¹ = ((m : X) * u) * u'⁻¹ * (m : X)⁻¹ := by group
      _ = (b⁻¹ * b' * (m : X) * u') * u'⁻¹ * (m : X)⁻¹ := by rw [this]
      _ = b⁻¹ * b' := by group
  have hmem : u * u'⁻¹ ∈ D.UwMinus m :=
    (D.UwMinusSub m).mul_mem hu ((D.UwMinusSub m).inv_mem hu')
  have hmem2 := (D.mem_UwMinus_iff).1 hmem
  rw [h1] at hmem2
  have h3 := D.eq_one_of_mem_U_Vm (D.B.mul_mem (D.B.inv_mem hb) hb') hmem2.2
  have h4 : u * u'⁻¹ = 1 := by
    have : u * u'⁻¹ = (m : X)⁻¹ * ((m : X) * (u * u'⁻¹) * (m : X)⁻¹) * (m : X) := by group
    rw [this, h1, h3]
    group
  exact mul_inv_eq_one.1 h4

theorem exists_dc (x : X) : ∃ w : D.Weyl, x ∈ dc D.B D.N w := by
  have : x ∈ ⋃ w : D.Weyl, dc D.B D.N w := D.isTits.iUnion_dc ▸ Set.mem_univ x
  simpa using this

@[expose] def bw (x : X) : D.Weyl :=
  Classical.choose (D.exists_dc x)

theorem mem_dc_bw (x : X) : x ∈ dc D.B D.N (D.bw x) :=
  Classical.choose_spec (D.exists_dc x)

theorem bw_eq {x : X} {w : D.Weyl} (hx : x ∈ dc D.B D.N w) : D.bw x = w :=
  D.isTits.dc_injective (dc_eq_of_mem (D.mem_dc_bw x) hx)

theorem exists_coord (x : X) :
    ∃ u ∈ D.UwMinus (D.lift (D.bw x)), ∃ b ∈ D.B, x = b * (D.lift (D.bw x) : X) * u := by
  obtain ⟨b, hb, u, hu, hxe⟩ :=
    (D.mem_dc_iff_coord (D.lift (D.bw x)) (D.lift_mk (D.bw x))).1 (D.mem_dc_bw x)
  exact ⟨u, hu, b, hb, hxe⟩

@[expose] def cu (x : X) : X :=
  Classical.choose (D.exists_coord x)

theorem cu_mem (x : X) : D.cu x ∈ D.UwMinus (D.lift (D.bw x)) :=
  (Classical.choose_spec (D.exists_coord x)).1

theorem exists_eq (x : X) : ∃ b ∈ D.B, x = b * (D.lift (D.bw x) : X) * D.cu x :=
  (Classical.choose_spec (D.exists_coord x)).2

theorem cu_mem_U (x : X) : D.cu x ∈ D.U := (D.cu_mem x).1

theorem bw_cu_mk {w : D.Weyl} {b u : X} (hb : b ∈ D.B) (hu : u ∈ D.UwMinus (D.lift w)) :
    D.bw (b * (D.lift w : X) * u) = w ∧ D.cu (b * (D.lift w : X) * u) = u := by
  have hx : b * (D.lift w : X) * u ∈ dc D.B D.N w :=
    (D.mem_dc_iff_coord (D.lift w) (D.lift_mk w)).2 ⟨b, hb, u, hu, rfl⟩
  have hbw := D.bw_eq hx
  refine ⟨hbw, ?_⟩
  obtain ⟨b₀, hb₀, hxe⟩ := D.exists_eq (b * (D.lift w : X) * u)
  have hcu := D.cu_mem (b * (D.lift w : X) * u)
  rw [hbw] at hxe hcu
  exact (D.coord_unique (D.lift w) hb hb₀ hu hcu hxe).symm

theorem bw_mul_left {b : X} (hb : b ∈ D.B) (x : X) : D.bw (b * x) = D.bw x := by
  obtain ⟨b₀, hb₀, hxe⟩ := D.exists_eq x
  have e : b * x = (b * b₀) * (D.lift (D.bw x) : X) * D.cu x := by
    calc b * x = b * (b₀ * (D.lift (D.bw x) : X) * D.cu x) := by rw [← hxe]
      _ = (b * b₀) * (D.lift (D.bw x) : X) * D.cu x := by group
  rw [e]
  exact (D.bw_cu_mk (w := D.bw x) (D.B.mul_mem hb hb₀) (D.cu_mem x)).1

theorem cu_mul_left {b : X} (hb : b ∈ D.B) (x : X) : D.cu (b * x) = D.cu x := by
  obtain ⟨b₀, hb₀, hxe⟩ := D.exists_eq x
  have e : b * x = (b * b₀) * (D.lift (D.bw x) : X) * D.cu x := by
    calc b * x = b * (b₀ * (D.lift (D.bw x) : X) * D.cu x) := by rw [← hxe]
      _ = (b * b₀) * (D.lift (D.bw x) : X) * D.cu x := by group
  rw [e]
  exact (D.bw_cu_mk (w := D.bw x) (D.B.mul_mem hb hb₀) (D.cu_mem x)).2

theorem mul_inv_mem_B_iff {x y : X} : x * y⁻¹ ∈ D.B ↔ D.bw x = D.bw y ∧ D.cu x = D.cu y := by
  constructor
  · intro h
    have hx : x = (x * y⁻¹) * y := by group
    refine ⟨?_, ?_⟩
    · rw [hx, D.bw_mul_left h]
    · rw [hx, D.cu_mul_left h]
  · rintro ⟨h1, h2⟩
    obtain ⟨b₁, hb₁, hx⟩ := D.exists_eq x
    obtain ⟨b₂, hb₂, hy⟩ := D.exists_eq y
    rw [hx, hy, h1, h2]
    have : b₁ * (D.lift (D.bw y) : X) * D.cu y * (b₂ * (D.lift (D.bw y) : X) * D.cu y)⁻¹ =
        b₁ * b₂⁻¹ := by group
    rw [this]
    exact D.B.mul_mem hb₁ (D.B.inv_mem hb₂)

end RankTwoSystem

end CFSG.GH74.BNPair
