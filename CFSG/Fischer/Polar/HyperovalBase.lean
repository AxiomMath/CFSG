
module

public import CFSG.Fischer.Polar.LocalSetsBase
public import CFSG.Fischer.Polar.PerpPerpBase
import all CFSG.Fischer.F4
public import Certificates.Data.CFSGNative.Fischer.Xi22
public import Certificates.Data.CFSGNative.Fischer.Polar
public import Certificates.Data.CFSGNative.F4.T46Simple
public import CFSG.Fischer.UnitaryAction
public import Certificates.Data.CFSGNative.Fi22.Local
public import Certificates.Data.Kernel.Fi22.Orb

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs perpTab
  perpLists lineTab lamTab gWords hypEnum t46XT t46YT famIndex

local notation "PT" => perpTab ()
local notation "LAM" => lamTab ()
local notation "CT" => mkCtx (perpTab ()) (gWords ()) (lamTab ())
local notation "HU" => Prod.fst (hypEnum 1) ++ Prod.fst (hypEnum 2) ++ Prod.fst (hypEnum 3)
local notation "IX" =>
  famIndex (Prod.fst (hypEnum 1) ++ Prod.fst (hypEnum 2) ++ Prod.fst (hypEnum 3))

private theorem ite_code_eq : ∀ x : F4,
    (if (x.code.val == 0) = true then 0 else 1) = (if x ≠ 0 then 1 else 0) := by decide

theorem nzC_codeOf (v : Fin 6 → F4) : nzC (codeOf v) = weight v := by
  have e0 : coord (codeOf v) 0 = (v 0).code.val := coord_codeOf v 0
  have e1 : coord (codeOf v) 1 = (v 1).code.val := coord_codeOf v 1
  have e2 : coord (codeOf v) 2 = (v 2).code.val := coord_codeOf v 2
  have e3 : coord (codeOf v) 3 = (v 3).code.val := coord_codeOf v 3
  have e4 : coord (codeOf v) 4 = (v 4).code.val := coord_codeOf v 4
  have e5 : coord (codeOf v) 5 = (v 5).code.val := coord_codeOf v 5
  unfold nzC weight
  rw [Finset.card_filter, Fin.sum_univ_six, e0, e1, e2, e3, e4, e5, ite_code_eq, ite_code_eq,
    ite_code_eq, ite_code_eq, ite_code_eq, ite_code_eq]

theorem prodCoordC_codeOf (v : Fin 6 → F4) : prodCoordC (codeOf v) = (∏ k, v k).code.val := by
  have e0 : coord (codeOf v) 0 = (v 0).code.val := coord_codeOf v 0
  have e1 : coord (codeOf v) 1 = (v 1).code.val := coord_codeOf v 1
  have e2 : coord (codeOf v) 2 = (v 2).code.val := coord_codeOf v 2
  have e3 : coord (codeOf v) 3 = (v 3).code.val := coord_codeOf v 3
  have e4 : coord (codeOf v) 4 = (v 4).code.val := coord_codeOf v 4
  have e5 : coord (codeOf v) 5 = (v 5).code.val := coord_codeOf v 5
  unfold prodCoordC
  rw [Fin.prod_univ_six, e0, e1, e2, e3, e4, e5, code_mul, code_mul, code_mul, code_mul, code_mul]

private theorem code_ω_pow : ∀ i : Fin 3, (F4.ω ^ (i : ℕ)).code.val = i.val + 1 := by decide

theorem ω_pow_iff {x : F4} (i : Fin 3) : x.code.val = i.val + 1 ↔ x = F4.ω ^ (i : ℕ) := by
  rw [← code_ω_pow i]
  exact ⟨code_inj, fun h => by rw [h]⟩

theorem flagSet_rootFlags (i : Fin 3) : flagSet (rootFlags (i.val + 1)) = hypRoot i := by
  ext p
  rw [mem_flagSet]
  unfold rootFlags
  rw [getElem!_pos _ p.val (by simp), Array.getElem_ofFn]
  simp only [uPts_get, nzC_codeOf, prodCoordC_codeOf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    ω_pow_iff]
  rfl

@[expose] noncomputable def hypGen (l : ℕ) : Equiv.Perm (Fin 693) := if l = 0 then t46x else t46y

theorem hypGen_mem (l : ℕ) : hypGen l ∈ T46 := by
  unfold hypGen
  split
  · exact t46x_mem
  · exact t46y_mem

theorem hypGens_get_zero : (hypGens ())[0]! = t46XT := rfl

theorem hypGens_get_one : (hypGens ())[1]! = t46YT := rfl

theorem rep_hypGens {l : ℕ} (hl : l < 2) : Rep 693 (hypGens ())[l]! (hypGen l) := by
  interval_cases l
  · rw [hypGens_get_zero]; exact rep_t46x
  · rw [hypGens_get_one]; exact rep_t46y

structure HypOrbitFacts (R : Flags) (o : Array Flags × Array Nat × Array Nat) : Prop where
  inv : ∀ l < 2, invOK 693 (hypGens ())[l]! (hypGensInv ())[l]! = true
  size : o.1.size = 1408
  root : o.1[0]! = R
  card : ∀ k < 1408, (members o.1[k]!).length = 126
  tree : ∀ k, 1 ≤ k → k < 1408 → o.2.1[k]! < k ∧ o.2.2[k]! < 2 ∧
    o.1[k]! = imgFlags (hypGensInv ())[o.2.2[k]!]! o.1[o.2.1[k]!]!
  closed : ∀ k < 1408, ∀ l < 2, ∃ i < 1408, o.1[i]! = imgFlags (hypGensInv ())[l]! o.1[k]!

theorem hypOrbitFacts_of {R : Flags} {o : Array Flags × Array Nat × Array Nat}
    {ix : Std.HashMap (Array UInt64) ℕ} {off : ℕ}
    (h : hypOrbitOK R (hypGens ()) (hypGensInv ()) o ix off = true) : HypOrbitFacts R o := by
  unfold hypOrbitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hi0⟩, hi1⟩, hs⟩, -⟩, -⟩, hr⟩, hc⟩, ht⟩, hcl⟩ := h
  refine ⟨fun l hl => ?_, hs, hr, fun k hk => ?_, fun k hk1 hk => ?_, fun k hk l hl => ?_⟩
  · interval_cases l
    · exact hi0
    · exact hi1
  · have := (allIn_eq_true.1 hc) k (Nat.zero_le _) hk
    rwa [beq_iff_eq] at this
  · have := (allIn_eq_true.1 ht) k hk1 hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 hcl) k (Nat.zero_le _) hk)) l (Nat.zero_le _) hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    exact ⟨_, by omega, h3⟩

@[expose] def hypSet (i : Fin 3) (k : ℕ) : Set (Fin 693) := flagSet (hypEnum (i.val + 1)).1[k]!

@[expose] def hypList (i : Fin 3) : List (Set (Fin 693)) :=
  (hypEnum (i.val + 1)).1.toList.map flagSet

theorem image_mem_hypOrbit {g : Equiv.Perm (Fin 693)} (hg : g ∈ T46) {i : Fin 3}
    {O : Set (Fin 693)} (hO : O ∈ hypOrbit i) : ⇑g '' O ∈ hypOrbit i := by
  obtain ⟨h, hh, rfl⟩ := hO
  refine ⟨g * h, T46.mul_mem hg hh, ?_⟩
  rw [Set.image_image]
  rfl

theorem image_mul (g h : Equiv.Perm (Fin 693)) (O : Set (Fin 693)) :
    ⇑(g * h) '' O = ⇑g '' (⇑h '' O) := by
  rw [Equiv.Perm.coe_mul, Set.image_comp]

theorem t46x_inv : t46x⁻¹ = t46x :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, t46x_sq])

theorem t46y_inv : t46y⁻¹ = t46y * t46y :=
  inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← pow_three', t46y_cube])

theorem tvP_image_mem_hypOrbit {i : Fin 3} {O : Set (Fin 693)} (hO : O ∈ hypOrbit i)
    (p : Fin 693) : tvP p '' O ∈ hypOrbit i :=
  image_mem_hypOrbit (tvP_mem p) hO

theorem hypOrbit_subset_of_invariant
    {𝒮 : Set (Set (Fin 693))}
    (h𝒮 : ∀ O ∈ 𝒮, ∀ p, tvP p '' O ∈ 𝒮) {i : Fin 3} {O : Set (Fin 693)} (hO : O ∈ 𝒮)
    (hOi : O ∈ hypOrbit i) : hypOrbit i ⊆ 𝒮 := by
  have key : ∀ g ∈ Subgroup.closure (Set.range tvP), ∀ Q ∈ 𝒮, ⇑g '' Q ∈ 𝒮 := by
    intro g hg
    induction hg using Subgroup.closure_induction_left with
    | one => intro Q hQ; simpa using hQ
    | mul_left x hx y _ ih =>
      obtain ⟨p, rfl⟩ := hx
      intro Q hQ
      rw [image_mul]
      exact h𝒮 _ (ih Q hQ) p
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨p, rfl⟩ := hx
      intro Q hQ
      rw [tvP_inv, image_mul]
      exact h𝒮 _ (ih Q hQ) p
  intro Q hQ
  obtain ⟨g, hg, rfl⟩ := hOi
  obtain ⟨g', hg', rfl⟩ := hQ
  have : ⇑g' '' hypRoot i = ⇑(g' * g⁻¹) '' (⇑g '' hypRoot i) := by
    rw [image_mul, Set.image_image, Set.image_image]
    simp [perm_inv_apply_self]
  rw [this]
  exact key _ (by rw [← T46_eq_closure]; exact T46.mul_mem hg' (T46.inv_mem hg)) _ hO

@[expose] def startX (j : ℕ) : Flags :=
  Array.ofFn (n := 693) fun p => ((CT).P[0]!)[p.val]! && !((CT).lam[j]!)[p.val]!

theorem image_inv_image (g : Equiv.Perm (Fin 693)) (O : Set (Fin 693)) :
    ⇑g '' (⇑g⁻¹ '' O) = O := by
  rw [Set.image_image]
  simp

theorem eq_of_length_le_one {α : Type*} {l : List α} (h : l.length ≤ 1) {a b : α} (ha : a ∈ l)
    (hb : b ∈ l) : a = b := by
  match l, h, ha, hb with
  | [_], _, ha, hb => rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb]
  | [], _, ha, _ => exact absurd ha List.not_mem_nil
  | _ :: _ :: _, h, _, _ => simp at h

end CFSG.Fischer
