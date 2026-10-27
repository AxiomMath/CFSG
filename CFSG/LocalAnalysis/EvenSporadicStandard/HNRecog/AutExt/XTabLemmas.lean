module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XModelCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XAutDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def IsBase01 (K : Subgroup (Equiv.Perm (Fin 1408))) : Prop :=
  ∀ g ∈ K, idx 1408 g 0 = 0 → idx 1408 g 1 = 1 → g = 1

theorem ap_ap_rep {x y : Table} {g h : Equiv.Perm (Fin 1408)} (hx : Rep 1408 x g)
    (hy : Rep 1408 y h) {i : ℕ} (hi : i < 1408) : ap x (ap y i) = idx 1408 (g * h) i := by
  rw [hy i hi, hx _ (idx_lt h hi), idx_mul]

theorem eq_of_base01 {K : Subgroup (Equiv.Perm (Fin 1408))} (hK : IsBase01 K)
    {a b : Equiv.Perm (Fin 1408)} (ha : a ∈ K) (hb : b ∈ K) (h0 : idx 1408 a 0 = idx 1408 b 0)
    (h1 : idx 1408 a 1 = idx 1408 b 1) : a = b := by
  have key : a⁻¹ * b = 1 := by
    refine hK _ (K.mul_mem (K.inv_mem ha) hb) ?_ ?_
    · rw [idx_mul, ← h0, idx_inv_idx]
    · rw [idx_mul, ← h1, idx_inv_idx]
  exact inv_mul_eq_one.mp key

theorem isBase01_of_xBaseOK {Xl : Array Table} {K : Subgroup (Equiv.Perm (Fin 1408))}
    (hE : IsEnumSet 1408 Xl (K : Set (Equiv.Perm (Fin 1408)))) (h : xBaseOK Xl = true) :
    IsBase01 K := by
  intro g hg h0 h1
  obtain ⟨k, hk, hrep⟩ := hE.cov g hg
  have hall := Array.all_eq_true'.1 h (Xl[k]!) (getElem!_mem_array hk)
  have e0 : ap Xl[k]! 0 = 0 := by rw [hrep 0 (by norm_num), h0]
  have e1 : ap Xl[k]! 1 = 1 := by rw [hrep 1 (by norm_num), h1]
  simp only [e0, e1, bne_self_eq_false, Bool.false_or] at hall
  exact (tblEq_idT_iff (by norm_num) hrep).1 hall

theorem commB_iff {K : Subgroup (Equiv.Perm (Fin 1408))} (hK : IsBase01 K) {x y : Table}
    {g h : Equiv.Perm (Fin 1408)} (hx : Rep 1408 x g) (hy : Rep 1408 y h) (hg : g ∈ K)
    (hh : h ∈ K) : commB x y = true ↔ g * h = h * g := by
  have e : ∀ i < 1408, ap x (ap y i) = idx 1408 (g * h) i ∧ ap y (ap x i) = idx 1408 (h * g) i :=
    fun i hi => ⟨ap_ap_rep hx hy hi, ap_ap_rep hy hx hi⟩
  rw [commB, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, (e 0 (by norm_num)).1,
    (e 0 (by norm_num)).2, (e 1 (by norm_num)).1, (e 1 (by norm_num)).2]
  constructor
  · rintro ⟨h0, h1⟩
    exact eq_of_base01 hK (K.mul_mem hg hh) (K.mul_mem hh hg) h0 h1
  · intro hgh
    rw [hgh]
    exact ⟨rfl, rfl⟩

theorem commB3_iff {K : Subgroup (Equiv.Perm (Fin 1408))} (hK : IsBase01 K) {u m t : Table}
    {g h k : Equiv.Perm (Fin 1408)} (hu : Rep 1408 u g) (hm : Rep 1408 m h) (ht : Rep 1408 t k)
    (hg : g ∈ K) (hh : h ∈ K) (hk : k ∈ K) :
    commB3 u m t = true ↔ g * h * k = k * (g * h) := by
  have e : ∀ i < 1408, ap u (ap m (ap t i)) = idx 1408 (g * h * k) i ∧
      ap t (ap u (ap m i)) = idx 1408 (k * (g * h)) i := by
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [ht i hi, hm _ (idx_lt k hi), hu _ (idx_lt h (idx_lt k hi)), idx_mul, idx_mul]
    · rw [hm i hi, hu _ (idx_lt h hi), ht _ (idx_lt g (idx_lt h hi)), idx_mul, idx_mul]
  rw [commB3, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, (e 0 (by norm_num)).1,
    (e 0 (by norm_num)).2, (e 1 (by norm_num)).1, (e 1 (by norm_num)).2]
  constructor
  · rintro ⟨h0, h1⟩
    exact eq_of_base01 hK (K.mul_mem (K.mul_mem hg hh) hk) (K.mul_mem hk (K.mul_mem hg hh)) h0 h1
  · intro hgh
    rw [hgh]
    exact ⟨rfl, rfl⟩

theorem order3OK_iff {y : Table} {g : Equiv.Perm (Fin 1408)} (hy : Rep 1408 y g) :
    order3OK 1408 y = true ↔ g ^ 3 = 1 := by
  constructor
  · intro h
    have h3 := idx_cube_of_order3OK hy h
    apply perm_faithful
    intro i
    apply Fin.ext
    have := h3 i.val i.2
    rw [idx_of_lt _ i.2] at this
    simpa using this
  · intro h
    rw [order3OK, allIn_eq_true]
    intro i _ hi
    rw [beq_iff_eq, hy i hi, hy _ (idx_lt g hi), hy _ (idx_lt g (idx_lt g hi)), ← idx_mul,
      ← idx_mul, ← pow_three', h, idx_one]

theorem invoOK_iff {y : Table} {g : Equiv.Perm (Fin 1408)} (hy : Rep 1408 y g) :
    invoOK 1408 y = true ↔ g ^ 2 = 1 := by
  constructor
  · exact sq_eq_one_of_invoOK hy
  · intro h
    rw [invoOK, allIn_eq_true]
    intro i _ hi
    rw [beq_iff_eq, hy i hi, hy _ (idx_lt g hi), ← idx_mul, ← pow_two, h, idx_one]

theorem rep_commTab {x xi y yi : Table} {g h : Equiv.Perm (Fin 1408)} (hx : Rep 1408 x g)
    (hxi : Rep 1408 xi g⁻¹) (hy : Rep 1408 y h) (hyi : Rep 1408 yi h⁻¹) :
    Rep 1408 (commTab x xi y yi) (g * h * g⁻¹ * h⁻¹) :=
  Rep.compT (Rep.compT (Rep.compT hx hy) hxi) hyi

theorem rep_relAT {x xi y yi : Table} {g h : Equiv.Perm (Fin 1408)} (hx : Rep 1408 x g)
    (hxi : Rep 1408 xi g⁻¹) (hy : Rep 1408 y h) (hyi : Rep 1408 yi h⁻¹) :
    Rep 1408 (relAT x xi y yi) (relA g h) := by
  unfold relAT relA
  exact Rep.compT (Rep.compT (Rep.compT (Rep.compT (Rep.compT (Rep.compT (Rep.compT
    (Rep.compT (Rep.compT (Rep.compT (Rep.compT (Rep.compT (Rep.compT hx hx) hy) hxi) hyi) hx)
    hy) hxi) hxi) hy) hxi) hy) hxi) hyi

theorem exists_conj_of_memT (H : Subgroup (Equiv.Perm (Fin 1408))) {gens gensInv : Array Table}
    {gg : ℕ → Equiv.Perm (Fin 1408)}
    (hg : ∀ l < gens.size, Rep 1408 gens[l]! (gg l) ∧ Rep 1408 gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ H)
    {x : Table} {xg : Equiv.Perm (Fin 1408)} (hx : Rep 1408 x xg) {elts : Array Table}
    {par lab : Array ℕ} (h : conjTreeOK 1408 gens gensInv x elts par lab = true) {t : Table}
    {g : Equiv.Perm (Fin 1408)} (ht : Rep 1408 t g) (hm : memT 1408 elts t = true) :
    ∃ c ∈ H, g = c * xg * c⁻¹ := by
  rw [memT, Array.any_eq_true'] at hm
  obtain ⟨T, hT, hTt⟩ := hm
  obtain ⟨k, hk, hkT⟩ := Array.getElem_of_mem hT
  have hkT' : elts[k]! = T := by rw [getElem!_pos elts k hk, hkT]
  obtain ⟨c, hc, hrep⟩ := conjTreeOK_spec H hg hx h k hk
  refine ⟨c, hc, ?_⟩
  have hT' : tblEq 1408 t elts[k]! = true := by rw [hkT']; exact hTt
  exact rep_unique ht (rep_of_tblEq hrep hT')

end CFSG.EvenSporadicStandard.HNRecog.Section4.XModel
