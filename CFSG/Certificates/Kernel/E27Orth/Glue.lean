module

public import CFSG.Certificates.Kernel.E27Orth.OrthSound

public section

namespace CFSG.KD.E27Orth

open CFSG.KC.Enum CFSG.KC.E27Orth CFSG.KC.Misc.G24 CFSG.KC.Misc.Spec Subgroup Matrix
open CFSG.HardMathSupport.Foote.E27 CFSG.Assembly.LowTwoRank

@[expose] def eMc (m : ℕ) : (Fin m ⊕ Fin m ⊕ Fin 2) ≃ Fin (m + (m + 2)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

@[expose] def ePc (r : ℕ) : (Fin r ⊕ Fin r) ≃ Fin (r + r) := finSumFinEquiv

@[expose] def umM (m : ℕ) : Fin m ⊕ Fin m ⊕ Fin 2 → Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2
  | .inl i, .inr (.inl j) => if i = j then 1 else 0
  | .inr (.inr i), .inr (.inr j) => if i ≤ j then 1 else 0
  | _, _ => 0

@[expose] def umP (r : ℕ) : Fin r ⊕ Fin r → Fin r ⊕ Fin r → ZMod 2
  | .inl i, .inr j => if i = j then 1 else 0
  | _, _ => 0

theorem qf_reindex {ι : Type} [Fintype ι] {n : ℕ} (e : ι ≃ Fin n)
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (v : ι → ZMod 2) :
    qf M (v ∘ e.symm) = ∑ a, v a * ∑ b, M (e a) (e b) * v b := by
  unfold qf
  simp only [dotProduct, mulVec, Function.comp_apply]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Equiv.symm_apply_apply, ← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply]

theorem quadMinus_eq {m n : ℕ} (e : (Fin m ⊕ Fin m ⊕ Fin 2) ≃ Fin n) (U : ℕ)
    (hU : ∀ a b, pkMat n U (e a) (e b) = umM m a b) (v : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :
    CFSG.MatrixModel.minusQuadCore m (ZMod 2) 1 1 v = qf (pkMat n U) (v ∘ e.symm) := by
  rw [qf_reindex]
  simp only [hU]
  have h1 : ∀ x : ZMod 2, x * x = x := by decide
  have h2 : ∀ x : ZMod 2, x ^ 2 = x := by decide
  simp [CFSG.MatrixModel.minusQuadCore, Fintype.sum_sum_type, umM, Fin.sum_univ_two]
  simp only [mul_add, h1, h2]
  ring

theorem quadPlus_eq {r n : ℕ} (e : (Fin r ⊕ Fin r) ≃ Fin n) (U : ℕ)
    (hU : ∀ a b, pkMat n U (e a) (e b) = umP r a b) (v : Fin r ⊕ Fin r → ZMod 2) :
    CFSG.MatrixModel.plusQuadCore r (ZMod 2) v = qf (pkMat n U) (v ∘ e.symm) := by
  rw [qf_reindex]
  simp only [hU]
  simp [CFSG.MatrixModel.plusQuadCore, Fintype.sum_sum_type, umP]

theorem card_fix_reindex {ι : Type} [Fintype ι] {n : ℕ} (e : ι ≃ Fin n)
    (M : Matrix ι ι (ZMod 2)) :
    Nat.card {v : Fin n → ZMod 2 // M.submatrix e.symm e.symm *ᵥ v = v} =
      Nat.card {w : ι → ZMod 2 // M *ᵥ w = w} := by
  refine (Nat.card_congr (Equiv.subtypeEquiv (e.arrowCongr (Equiv.refl _)) fun w => ?_)).symm
  have hw : e.arrowCongr (Equiv.refl _) w = w ∘ e.symm := rfl
  rw [hw, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_assoc,
    Equiv.symm_comp_self, Function.comp_id]
  constructor
  · intro h
    rw [h]
  · intro h
    funext x
    have := congrFun h (e x)
    simpa using this

section Glue

variable {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2) {n : ℕ}
  (e : ι ≃ Fin n)

theorem omega_le_orthN : StatedOmega Q ≤ OrthN Q :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact (OrthN Q).mul_mem ((OrthN Q).mul_mem ((OrthN Q).mul_mem ha hb) ((OrthN Q).inv_mem ha))
      ((OrthN Q).inv_mem hb)

@[expose] noncomputable def matOmK : ↥(StatedOmega Q) →* Matrix (Fin n) (Fin n) (ZMod 2) :=
  (matO Q e).comp (Subgroup.inclusion (omega_le_orthN Q))

theorem matOmK_injective : Function.Injective (matOmK Q e) := fun _ _ h =>
  Subgroup.inclusion_injective _ (matO_injective Q e h)

theorem fixG_matOmK (x : ↥(StatedOmega Q)) :
    fixG (matOmK Q e) x = Nat.card {w : ι → ZMod 2 // ((x : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w = w} :=
  card_fix_reindex e _

theorem lt_mul_of {N m j i : ℕ} (hj : j < m) (hi : i < N) : N * j + i < N * m :=
  calc N * j + i < N * j + N := by omega
    _ = N * (j + 1) := by ring
    _ ≤ N * m := Nat.mul_le_mul_left _ hj

variable {U : ℕ} (hQ : ∀ v, Q v = qf (pkMat n U) (v ∘ e.symm))
include hQ

theorem gens_omega {m : ℕ} {G Y Yi : ℕ → ℕ} (hom : allN m (fun j => omI n U (G j) (Y j) (Yi j)) = true) :
    ∃ g : ℕ → ↥(OrthN Q), ∀ j < m, matO Q e (g j) = pkMat n (G j) ∧
      ((g j : GL ι (ZMod 2)) ∈ StatedOmega Q) := by
  have hex : ∀ j, j < m → ∃ x : ↥(OrthN Q), matO Q e x = pkMat n (G j) ∧
      (x : GL ι (ZMod 2)) ∈ StatedOmega Q := fun j hj =>
    om_sound Q e hQ (CFSG.KS.allN_spec hom j hj)
  choose! g hg using hex
  exact ⟨g, hg⟩

theorem tc_glue (hn : 0 < n) {m N c0 nF : ℕ} {G Y Yi E Tr Ss Lf F Fm Pw : ℕ → ℕ} (hN : 0 < N)
    (hom : allN m (fun j => omI n U (G j) (Y j) (Yi j)) = true)
    (hbase : baseI (cnF2 n) (oneF2 n) m G = true)
    (htree : allN N (treeI (mulF2 n) (cnF2 n) (oneF2 n) m G E Tr) = true)
    (hkey : allN N (keyI N E Ss) = true)
    (hleft : allN (N * m) (leftI (mulF2 n) N G E Lf) = true)
    (hcen : allN N (cenI n (oneF2 n) m c0 G E) = true)
    (hfs : allN N (fsI n (oneF2 n) c0 nF E F Fm) = true)
    (hpair : allN (nF * nF) (pairI n (oneF2 n) c0 nF E F Pw) = true) :
    ∃ S : Subgroup ↥(StatedOmega Q), Nat.card S = N ∧
      (∀ c ∈ S, c ≠ 1 → (∀ s ∈ S, s * c = c * s) →
        Nat.card {v : ι → ZMod 2 // ((c : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ v = v} = c0) ∧
      (∀ a ∈ S, ∀ b ∈ S, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → a ≠ 1 → b ∉ zpowers a →
        ∃ i j : ℕ, a ^ i * b ^ j ≠ 1 ∧ Nat.card {v : ι → ZMod 2 //
          (((a ^ i * b ^ j : ↥(StatedOmega Q)) : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ v = v} ≠
            c0) := by
  obtain ⟨g₀, hg₀⟩ := gens_omega Q e hQ hom
  let g : ℕ → ↥(StatedOmega Q) := fun j =>
    if h : j < m then ⟨(g₀ j : GL ι (ZMod 2)), (hg₀ j h).2⟩ else 1
  have hg : ∀ j < m, matOmK Q e (g j) = pkMat n (G j) := by
    intro j hj
    simp only [g, dif_pos hj]
    exact (hg₀ j hj).1
  have hρ := matOmK_injective Q e
  have hone := pkMat_oneF2 n
  have htree' := CFSG.KS.allN_spec htree
  obtain ⟨X, hX, hinj⟩ := tab_tree (encF2 n) hρ hone hg hbase htree' (CFSG.KS.allN_spec hkey)
  have hsurj := tab_left (encF2 n) hρ hone hN hg hbase htree'
    (fun j hj i hi => CFSG.KS.allN_spec hleft _ (lt_mul_of hj hi)) hX
  refine ⟨gS m g, card_of_tab (fun i hi => (hX i hi).1) hinj hsurj, fun c hc h1 hcom => ?_,
    fun a ha b hb ha3 hb3 hab ha1 hbz => ?_⟩
  · rw [← fixG_matOmK Q e]
    exact cen_sound hn hρ hone hX hsurj (fun j hj => ⟨subset_closure ⟨j, hj, rfl⟩, hg j hj⟩)
      (CFSG.KS.allN_spec hcen) c hc h1 hcom
  · obtain ⟨i, j, h1, h2⟩ := pair_sound hn hρ hone (baseI_spec hbase).1
      (fun i hi => (treeI_spec (htree' i hi)).1) hX hsurj (CFSG.KS.allN_spec hfs)
      (CFSG.KS.allN_spec hpair) a ha b hb ha3 hb3 hab ha1 hbz
    exact ⟨i, j, h1, by rwa [← fixG_matOmK Q e]⟩

theorem kill_glue {m N k nR : ℕ} {G Y Yi E Tr Ss Lf W Rp Cm : ℕ → ℕ} (hN : N = 3 ^ k)
    (hom : allN m (fun j => omI n U (G j) (Y j) (Yi j)) = true)
    (hbase : baseI (cnF2 n) (oneF2 n) m G = true)
    (htree : allN N (treeI (mulF2 n) (cnF2 n) (oneF2 n) m G E Tr) = true)
    (hkey : allN N (keyI N E Ss) = true)
    (hleft : allN (N * m) (leftI (mulF2 n) N G E Lf) = true)
    (hconj : allN N (conjI (mulF2 n) N nR E Rp W) = true)
    (hrep : allN nR (repI (mulF2 n) (cnF2 n) (oneF2 n) N 81 E Rp Cm) = true) :
    ∃ S : Subgroup ↥(StatedOmega Q), Nat.card S = N ∧
      ∀ s ∈ S, orderOf s = 3 → 81 ∣ Nat.card ↥(S ⊓ centralizer ({s} : Set ↥(StatedOmega Q))) := by
  obtain ⟨g₀, hg₀⟩ := gens_omega Q e hQ hom
  let g : ℕ → ↥(StatedOmega Q) := fun j =>
    if h : j < m then ⟨(g₀ j : GL ι (ZMod 2)), (hg₀ j h).2⟩ else 1
  have hg : ∀ j < m, matOmK Q e (g j) = pkMat n (G j) := by
    intro j hj
    simp only [g, dif_pos hj]
    exact (hg₀ j hj).1
  have hρ := matOmK_injective Q e
  have hone := pkMat_oneF2 n
  have htree' := CFSG.KS.allN_spec htree
  have hN0 : 0 < N := by rw [hN]; positivity
  obtain ⟨X, hX, hinj⟩ := tab_tree (encF2 n) hρ hone hg hbase htree' (CFSG.KS.allN_spec hkey)
  have hsurj := tab_left (encF2 n) hρ hone hN0 hg hbase htree'
    (fun j hj i hi => CFSG.KS.allN_spec hleft _ (lt_mul_of hj hi)) hX
  have hcard := card_of_tab (fun i hi => (hX i hi).1) hinj hsurj
  refine ⟨gS m g, hcard, fun s hs h3 => ?_⟩
  have h81 := kill_sound (encF2 n) hρ hone (baseI_spec hbase).1
    (fun i hi => (treeI_spec (htree' i hi)).1) hX hinj hsurj (CFSG.KS.allN_spec hconj)
    (CFSG.KS.allN_spec hrep) s hs (h3 ▸ pow_orderOf_eq_one s)
  exact dvd81_of_le (hcard.trans hN) inf_le_left h81

theorem cover_glue {m mB N NB nW : ℕ}
    {G Y Yi E Tr Ss Lf GB YB YBi EB TrB SB LfB Wg Wgi Cv : ℕ → ℕ} (hN : 0 < N) (hNB : 0 < NB)
    (hom : allN m (fun j => omI n U (G j) (Y j) (Yi j)) = true)
    (hbase : baseI (cnF2 n) (oneF2 n) m G = true)
    (htree : allN N (treeI (mulF2 n) (cnF2 n) (oneF2 n) m G E Tr) = true)
    (hkey : allN N (keyI N E Ss) = true)
    (hleft : allN (N * m) (leftI (mulF2 n) N G E Lf) = true)
    (homB : allN mB (fun j => omI n U (GB j) (YB j) (YBi j)) = true)
    (hbaseB : baseI (cnF2 n) (oneF2 n) mB GB = true)
    (htreeB : allN NB (treeI (mulF2 n) (cnF2 n) (oneF2 n) mB GB EB TrB) = true)
    (hkeyB : allN NB (keyI NB EB SB) = true)
    (hleftB : allN (NB * mB) (leftI (mulF2 n) NB GB EB LfB) = true)
    (hcomm : allN (mB * mB) (commI n mB GB) = true)
    (hwit : allN nW (fun w => orthI n U (Wg w) (Wgi w)) = true)
    (hcov : allN N (coverI n (oneF2 n) NB nW E EB Wg Cv) = true) :
    ∃ S₀ B₀ : Subgroup ↥(OrthN Q), Nat.card S₀ = N ∧ Nat.card B₀ = NB ∧
      S₀ ≤ (StatedOmega Q).subgroupOf (OrthN Q) ∧ B₀ ≤ (StatedOmega Q).subgroupOf (OrthN Q) ∧
      (∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x) ∧
      ∀ s ∈ S₀, s ^ 3 = 1 → s ≠ 1 → ∃ x : ↥(OrthN Q), x * s * x⁻¹ ∈ B₀ := by
  obtain ⟨g, hg⟩ := gens_omega Q e hQ hom
  obtain ⟨gb, hgb⟩ := gens_omega Q e hQ homB
  have hρ := matO_injective Q e
  have hone := pkMat_oneF2 n
  have htree' := CFSG.KS.allN_spec htree
  have htreeB' := CFSG.KS.allN_spec htreeB
  obtain ⟨X, hX, hinj⟩ := tab_tree (encF2 n) hρ hone (fun j hj => (hg j hj).1) hbase htree'
    (CFSG.KS.allN_spec hkey)
  have hsurj := tab_left (encF2 n) hρ hone hN (fun j hj => (hg j hj).1) hbase htree'
    (fun j hj i hi => CFSG.KS.allN_spec hleft _ (lt_mul_of hj hi)) hX
  obtain ⟨XB, hXB, hinjB⟩ := tab_tree (encF2 n) hρ hone (fun j hj => (hgb j hj).1) hbaseB htreeB'
    (CFSG.KS.allN_spec hkeyB)
  have hsurjB := tab_left (encF2 n) hρ hone hNB (fun j hj => (hgb j hj).1) hbaseB htreeB'
    (fun j hj i hi => CFSG.KS.allN_spec hleftB _ (lt_mul_of hj hi)) hXB
  have hle : ∀ {k : ℕ} {h : ℕ → ↥(OrthN Q)},
      (∀ j < k, (h j : GL ι (ZMod 2)) ∈ StatedOmega Q) →
        gS k h ≤ (StatedOmega Q).subgroupOf (OrthN Q) := by
    intro k h hk
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (hk j hj)
  refine ⟨gS m g, gS mB gb, card_of_tab (fun i hi => (hX i hi).1) hinj hsurj,
    card_of_tab (fun i hi => (hXB i hi).1) hinjB hsurjB, hle fun j hj => (hg j hj).2,
    hle fun j hj => (hgb j hj).2, comm_sound hρ (fun j hj => (hgb j hj).1)
      (CFSG.KS.allN_spec hcomm), ?_⟩
  exact cover_sound hρ hone (baseI_spec hbase).1 hX hsurj hXB
    (fun w hw => orth_sound Q e hQ (CFSG.KS.allN_spec hwit w hw)) (CFSG.KS.allN_spec hcov)

end Glue

end CFSG.KD.E27Orth

end
