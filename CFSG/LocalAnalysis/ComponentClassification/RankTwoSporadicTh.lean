module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Th

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open scoped commutatorElement

section Reps

variable {G : Type*} [Group G] {H : Subgroup G} {a : ↥H} {M : Subgroup ↥H} {R : Set ↥H}

theorem yWitness_top_of_map_conj {E : Subgroup ↥H} (g : ↥H)
    (h : YWitness (⊤ : Subgroup ↥H) (E.map (MulAut.conj g).toMonoidHom)) :
    YWitness (⊤ : Subgroup ↥H) E := by
  rwa [← map_conj_eq_of_normal (inferInstance : (⊤ : Subgroup ↥H).Normal) g,
    yWitness_map_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective] at h

theorem yWitness_of_mem_rep (ha1 : a ≠ 1) (hM : centralizer {a} = M)
    (hwit : ∀ r ∈ R, ∃ c ∈ ⁅M, M⁆, 4 ∣ orderOf ⁅r, c⁆) {E : Subgroup ↥H} {r : ↥H} (haE : a ∈ E)
    (hr : r ∈ R) (hrE : r ∈ E) : YWitness (⊤ : Subgroup ↥H) E := by
  obtain ⟨c, hc, h4⟩ := hwit r hr
  refine Or.inl ⟨⁅r, c⁆, commutator_mem_commutator hrE ?_, h4⟩
  have hle : centDer (⊤ : Subgroup ↥H) a ≤ gammaE ⊤ E :=
    le_iSup₂_of_le a haE (le_iSup_of_le ha1 le_rfl)
  refine hle ?_
  show c ∈ ⁅(⊤ : Subgroup ↥H) ⊓ centralizer {a}, (⊤ : Subgroup ↥H) ⊓ centralizer {a}⁆
  rwa [top_inf_eq, hM]

variable [Finite G]

theorem yWitness_of_mem_centralizer_reps (ha : orderOf a = 2) (hM : centralizer {a} = M)
    (hreps : ∀ m ∈ M, orderOf m = 2 → m ≠ a → ∃ g ∈ M, ∃ r ∈ R, g * m * g⁻¹ = r)
    (hwit : ∀ r ∈ R, ∃ c ∈ ⁅M, M⁆, 4 ∣ orderOf ⁅r, c⁆) {E : Subgroup ↥H}
    (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) (haE : a ∈ E) :
    YWitness (⊤ : Subgroup ↥H) E := by
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; exact absurd ha (by norm_num)
  obtain ⟨b, hbE, hba⟩ : ∃ b ∈ E, b ∉ zpowers a := by
    by_contra hcon
    push Not at hcon
    have hcard := card_le_of_le (show E ≤ zpowers a from hcon)
    rw [Nat.card_zpowers, ha] at hcard
    omega
  have hb1 : b ≠ 1 := fun h => hba (h ▸ one_mem _)
  have hbne : b ≠ a := fun h => hba (h ▸ mem_zpowers a)
  have hb2 : orderOf b = 2 := orderOf_eq_prime (hE.2 b hbE) hb1
  have hbM : b ∈ M := by
    rw [← hM, mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨b, hbE⟩ ⟨a, haE⟩)
  obtain ⟨g, hgM, r, hr, hgr⟩ := hreps b hbM hb2 hbne
  have hga : g * a * g⁻¹ = a := by
    have hgC : g ∈ centralizer ({a} : Set ↥H) := by rw [hM]; exact hgM
    rw [mem_centralizer_singleton_iff.mp hgC, mul_inv_cancel_right]
  apply yWitness_top_of_map_conj g
  refine yWitness_of_mem_rep ha1 hM hwit (r := r) ?_ hr ?_
  · exact ⟨a, haE, hga⟩
  · exact ⟨b, hbE, hgr⟩

theorem yCensus_top_of_reps (ha : orderOf a = 2) (hfus : ∀ t : ↥H, orderOf t = 2 → IsConj a t)
    (hM : centralizer {a} = M)
    (hreps : ∀ m ∈ M, orderOf m = 2 → m ≠ a → ∃ g ∈ M, ∃ r ∈ R, g * m * g⁻¹ = r)
    (hwit : ∀ r ∈ R, ∃ c ∈ ⁅M, M⁆, 4 ∣ orderOf ⁅r, c⁆) :
    YCensus (⊤ : Subgroup ↥H) (fun _ => False) := by
  intro E hE hE4 _
  obtain ⟨e, heE, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (hcon x hx)
    rw [hbot, card_bot] at hE4
    omega
  have he2 : orderOf e = 2 := orderOf_eq_prime (hE.2 e heE) he1
  obtain ⟨g, hg⟩ := isConj_iff.mp (hfus e he2)
  apply yWitness_top_of_map_conj g⁻¹
  refine yWitness_of_mem_centralizer_reps ha hM hreps hwit (isElemAbelian_map hE _)
    (by rwa [card_map_of_injective (MulAut.conj g⁻¹).injective]) ⟨e, heE, ?_⟩
  show g⁻¹ * e * g⁻¹⁻¹ = a
  rw [← hg]
  group

omit [Finite G] in
theorem reps_of_three (hM : centralizer {a} = M) {r₁ r₂ : ↥H}
    (h3 : ∀ m ∈ M, orderOf m = 2 →
      ∃ g ∈ M, g * m * g⁻¹ = a ∨ g * m * g⁻¹ = r₁ ∨ g * m * g⁻¹ = r₂) :
    ∀ m ∈ M, orderOf m = 2 → m ≠ a → ∃ g ∈ M, ∃ r ∈ ({r₁, r₂} : Set ↥H), g * m * g⁻¹ = r := by
  intro m hm h2 hma
  obtain ⟨g, hgM, h | h | h⟩ := h3 m hm h2
  · exfalso
    apply hma
    have hgC : g ∈ centralizer ({a} : Set ↥H) := by rw [hM]; exact hgM
    have hga : g * a = a * g := mem_centralizer_singleton_iff.mp hgC
    calc m = g⁻¹ * (g * m * g⁻¹) * g := by group
      _ = g⁻¹ * a * g := by rw [h]
      _ = a := by rw [mul_assoc, ← hga, ← mul_assoc, inv_mul_cancel, one_mul]
  · exact ⟨g, hgM, r₁, Or.inl rfl, h⟩
  · exact ⟨g, hgM, r₂, Or.inr rfl, h⟩

omit [Finite G] in
theorem mul_pow_eq_pow_mul {b : ↥H} (h : a * b = b * a) (n : ℕ) : b * a ^ n = a ^ n * b := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc b * a ^ (n + 1) = b * a ^ n * a := by rw [pow_succ, mul_assoc]
      _ = a ^ n * (b * a) := by rw [ih, mul_assoc]
      _ = a ^ (n + 1) * b := by rw [← h, pow_succ, mul_assoc]

omit [Finite G] in
theorem pow_val_add_of_mul_self (ha : a * a = 1) (s t : ZMod 2) :
    a ^ s.val * a ^ t.val = a ^ (s + t).val := by
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases s with rfl | rfl <;>
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases t with rfl | rfl
  · simp
  · simp
  · simp
  · have h11 : (1 + 1 : ZMod 2) = 0 := by decide
    rw [h11]
    simp [CFSG.Certificates.ExtraspecialNF.val_one_two, ha]

omit [Finite G] in
theorem coe_commutatorElement {K : Subgroup ↥H} (g h : ↥K) :
    ((⁅g, h⁆ : ↥K) : ↥H) = ⁅(g : ↥H), (h : ↥H)⁆ := by
  simp [commutatorElement_def]

omit [Finite G] in
theorem coe_commutatorElement' {K : Subgroup G} (g h : ↥K) :
    ((⁅g, h⁆ : ↥K) : G) = ⁅(g : G), (h : G)⁆ := by
  simp [commutatorElement_def]

end Reps

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.InvRep

theorem center_J :
    center ↥J = ⊥ := by
  have : IsSimpleGroup ↥J := Kernel.isSimpleGroup_J th_kernel_facts
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥J) with h | h
  · exact h
  · exfalso
    let _ : CommGroup ↥J :=
      { (inferInstance : Group ↥J) with
        mul_comm := fun a b => mem_center_iff.mp (h ▸ mem_top b) a }
    have hp := IsSimpleGroup.prime_card (α := ↥J)
    rw [natCard_J] at hp
    exact absurd hp (by norm_num)

theorem thAutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .Th) ↥J (J.subgroupOf J) := by
  refine Cert.autModel_of_allInner (P := J) (X₀ := Blueprint.NativeSporadic.Carrier .Th)
    thEquivJ.symm center_J fun α => ?_
  have hα : α ∈ OuterAutomorphisms.inner ↥J := by
    rw [CFSG.Sporadic.ThSchreier.inner_J]
    trivial
  obtain ⟨g, hg⟩ := hα
  exact ⟨g, hg.symm⟩

theorem nf_eq_zpow_mul (s : ZMod 2) (v : Fin 8 → ZMod 2) :
    nf s v = z ^ s.val * nf 0 v := by
  simp [nf]

theorem zpow_mul_nf (s t : ZMod 2)
    (v : Fin 8 → ZMod 2) : z ^ s.val * nf t v = nf (s + t) v := by
  rw [nf_eq_zpow_mul t, ← mul_assoc, pow_val_add_of_mul_self z_mul_self, ← nf_eq_zpow_mul]

theorem conj_nf_x (s : ZMod 2)
    (v : Fin 8 → ZMod 2) : ∃ t, x * nf s v * x⁻¹ = nf t (Matrix.mulVec B1 v) := by
  obtain ⟨t, ht⟩ := conj_nf_zero x xz xv x_conj_q v
  have hw : (fun k => ∑ i, v i * xv i k) = Matrix.mulVec B1 v := by
    funext k
    simp [Matrix.mulVec, dotProduct, B1, mul_comm]
  rw [hw] at ht
  refine ⟨s + t, ?_⟩
  have hc : x * z ^ s.val = z ^ s.val * x := mul_pow_eq_pow_mul z_mul_x s.val
  calc x * nf s v * x⁻¹ = x * z ^ s.val * nf 0 v * x⁻¹ := by
        rw [nf_eq_zpow_mul s v]; simp only [mul_assoc]
    _ = z ^ s.val * (x * nf 0 v * x⁻¹) := by rw [hc]; group
    _ = nf (s + t) (Matrix.mulVec B1 v) := by rw [ht, zpow_mul_nf]

theorem conj_nf_y (s : ZMod 2)
    (v : Fin 8 → ZMod 2) : ∃ t, y * nf s v * y⁻¹ = nf t (Matrix.mulVec B2 v) := by
  obtain ⟨t, ht⟩ := conj_nf_zero y yz yv y_conj_q v
  have hw : (fun k => ∑ i, v i * yv i k) = Matrix.mulVec B2 v := by
    funext k
    simp [Matrix.mulVec, dotProduct, B2, mul_comm]
  rw [hw] at ht
  refine ⟨s + t, ?_⟩
  have hc : y * z ^ s.val = z ^ s.val * y := mul_pow_eq_pow_mul z_mul_y s.val
  calc y * nf s v * y⁻¹ = y * z ^ s.val * nf 0 v * y⁻¹ := by
        rw [nf_eq_zpow_mul s v]; simp only [mul_assoc]
    _ = z ^ s.val * (y * nf 0 v * y⁻¹) := by rw [hc]; group
    _ = nf (s + t) (Matrix.mulVec B2 v) := by rw [ht, zpow_mul_nf]

@[expose] def wordVec : List Gen → (Fin 8 → ZMod 2) → (Fin 8 → ZMod 2)
  | [], v => v
  | l :: w, v => Matrix.mulVec (Gen.eval B1 B2 l) (wordVec w v)

theorem conj_nf_wordProd
    (w : List Gen) (s : ZMod 2) (v : Fin 8 → ZMod 2) :
    ∃ t, wordProd w * nf s v * (wordProd w)⁻¹ = nf t (wordVec w v) := by
  induction w generalizing s v with
  | nil => exact ⟨s, by simp [wordProd, wordVec]⟩
  | cons l w ih =>
    obtain ⟨t, ht⟩ := ih s v
    have hl : wordProd (l :: w) = Gen.eval x y l * wordProd w := by
      simp [wordProd]
    have e : Gen.eval x y l * wordProd w * nf s v * (Gen.eval x y l * wordProd w)⁻¹ =
        Gen.eval x y l * (wordProd w * nf s v * (wordProd w)⁻¹) * (Gen.eval x y l)⁻¹ := by
      group
    rw [hl, e, ht]
    cases l
    · exact conj_nf_x t (wordVec w v)
    · exact conj_nf_y t (wordVec w v)

@[expose] def wc1 : List Gen := [.x, .y, .y, .x, .y, .y, .y, .y, .y, .y, .y, .y, .y, .y]

theorem comm_eq_wordProd :
    ⁅x, y * y⁆ = wordProd wc1 := by
  rw [commutatorElement_def, x_inv, mul_inv_rev, y_inv]
  simp [wordProd, wc1, Gen.eval, pow_succ, mul_assoc]

theorem wordVec_wc1 : wordVec wc1 (Pi.single 0 1) = ![0, 0, 0, 0, 1, 1, 0, 0] := by
  have h0 : (Pi.single 0 1 : Fin 8 → ZMod 2) = ![1, 0, 0, 0, 0, 0, 0, 0] := by decide
  have s1 : Matrix.mulVec B2 ![1, 0, 0, 0, 0, 0, 0, 0] = ![0, 1, 0, 0, 0, 0, 0, 0] := by decide
  have s2 : Matrix.mulVec B2 ![0, 1, 0, 0, 0, 0, 0, 0] = ![0, 1, 1, 0, 1, 0, 0, 1] := by decide
  have s3 : Matrix.mulVec B2 ![0, 1, 1, 0, 1, 0, 0, 1] = ![1, 1, 0, 1, 0, 1, 1, 0] := by decide
  have s4 : Matrix.mulVec B2 ![1, 1, 0, 1, 0, 1, 1, 0] = ![0, 0, 0, 0, 1, 0, 0, 0] := by decide
  have s5 : Matrix.mulVec B2 ![0, 0, 0, 0, 1, 0, 0, 0] = ![0, 0, 1, 0, 0, 0, 0, 0] := by decide
  have s6 : Matrix.mulVec B2 ![0, 0, 1, 0, 0, 0, 0, 0] = ![1, 0, 0, 0, 0, 0, 0, 0] := by decide
  have s11 : Matrix.mulVec B1 ![0, 0, 0, 0, 1, 0, 0, 0] = ![0, 0, 0, 0, 0, 0, 1, 0] := by decide
  have s12 : Matrix.mulVec B2 ![0, 0, 0, 0, 0, 0, 1, 0] = ![0, 1, 0, 0, 1, 0, 1, 0] := by decide
  have s13 : Matrix.mulVec B2 ![0, 1, 0, 0, 1, 0, 1, 0] = ![0, 0, 0, 0, 0, 0, 1, 1] := by decide
  have s14 : Matrix.mulVec B1 ![0, 0, 0, 0, 0, 0, 1, 1] = ![0, 0, 0, 0, 1, 1, 0, 0] := by decide
  simp only [wc1, wordVec, Gen.eval]
  rw [h0, s1, s2, s3, s4, s5, s6, s1, s2, s3, s4, s11, s12, s13, s14]

theorem orderOf_comm_q0 :
    orderOf ⁅q 0, ⁅x, y * y⁆⁆ = 4 := by
  obtain ⟨t, ht⟩ := conj_nf_wordProd wc1 0 (Pi.single 0 1)
  rw [wordVec_wc1] at ht
  have hq0 : q 0 = nf 0 (Pi.single 0 1) := by
    rw [nf_eq_generic, CFSG.Certificates.ExtraspecialNF.nf_single]
  have hq0inv : (q 0)⁻¹ = q 0 := inv_eq_of_mul_eq_one_right (q_mul_self 0)
  have hcomm : ⁅q 0, ⁅x, y * y⁆⁆ = nf (0 + t + CFSG.Certificates.ExtraspecialNF.collect c (Pi.single 0 1)
      ![0, 0, 0, 0, 1, 1, 0, 0]) (Pi.single 0 1 + ![0, 0, 0, 0, 1, 1, 0, 0]) := by
    rw [commutatorElement_def (q 0), comm_eq_wordProd, hq0inv]
    have e : q 0 * wordProd wc1 * q 0 * (wordProd wc1)⁻¹ =
        q 0 * (wordProd wc1 * q 0 * (wordProd wc1)⁻¹) := by group
    rw [e, hq0, ht, nf_eq_generic, nf_eq_generic, nf_eq_generic,
      CFSG.Certificates.ExtraspecialNF.nf_mul_nf symplectic_rel]
  have hsq : ⁅q 0, ⁅x, y * y⁆⁆ ^ 2 = z := by
    rw [hcomm, nf_sq]
    have hqf : CFSG.Certificates.ExtraspecialNF.qf c ((Pi.single 0 1 : Fin 8 → ZMod 2) +
        ![0, 0, 0, 0, 1, 1, 0, 0]) = 1 := by decide
    rw [hqf, CFSG.Certificates.ExtraspecialNF.val_one_two, pow_one]
  have h1 : ¬ ⁅q 0, ⁅x, y * y⁆⁆ ^ 2 ^ 1 = 1 := by
    rw [pow_one, hsq]
    exact z_ne_one
  have h2 : ⁅q 0, ⁅x, y * y⁆⁆ ^ 2 ^ (1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hsq, sq, z_mul_self]
  exact orderOf_eq_prime_pow h1 h2

theorem orderOf_comm_perm :
    orderOf ⁅aPerm, ⁅bPerm, bPerm * (bPerm * (aPerm * 1))⁆⁆ = 4 := by
  have h1 : ¬ ⁅aPerm, ⁅bPerm, bPerm * (bPerm * (aPerm * 1))⁆⁆ ^ 2 ^ 1 = 1 := by decide +kernel
  have h2 : ⁅aPerm, ⁅bPerm, bPerm * (bPerm * (aPerm * 1))⁆⁆ ^ 2 ^ (1 + 1) = 1 := by
    decide +kernel
  exact orderOf_eq_prime_pow h1 h2

theorem four_dvd_orderOf_comm_x :
    4 ∣ orderOf ⁅x, ⁅y, wordProd [.y, .y, .x]⁆⁆ := by
  set m : ↥M := ⁅genM .x, ⁅genM .y, wordM [.y, .y, .x]⁆⁆ with hm
  have hmJ : (m : J) = ⁅x, ⁅y, wordProd [.y, .y, .x]⁆⁆ := by
    rw [hm, coe_commutatorElement, coe_commutatorElement]
    rfl
  have hk : ((kap m : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)) =
      ⁅aPerm, ⁅bPerm, bPerm * (bPerm * (aPerm * 1))⁆⁆ := by
    rw [hm, map_commutatorElement, map_commutatorElement, coe_commutatorElement',
      coe_commutatorElement', kap_genM, kap_genM, kap_wordM]
    rfl
  have h4 : orderOf (kap m) = 4 := by
    rw [← Subgroup.orderOf_coe, hk, orderOf_comm_perm]
  rw [← hmJ, Subgroup.orderOf_coe, ← h4]
  exact orderOf_map_dvd kap m

theorem th_yCensus :
    YCensus (⊤ : Subgroup ↥J) (fun _ => False) := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact z_mul_self) z_ne_one
  have ha2 : orderOf a = 2 := by rw [← z_eq_a]; exact hz2
  have hM : centralizer ({a} : Set ↥J) = M := Kernel.centralizer_a_eq_M th_kernel_facts
  refine yCensus_top_of_reps (H := J) (a := a) (M := M) (R := {q 0, x}) ha2
    all_involutions_conjugate hM ?_ ?_
  · refine reps_of_three hM fun m hm h2 => ?_
    obtain ⟨g, hgM, h⟩ := max3_involution_representatives m hm h2
    rw [z_eq_a] at h
    exact ⟨g, hgM, h⟩
  · rintro r (rfl | rfl)
    · refine ⟨⁅x, y * y⁆, commutator_mem_commutator x_mem_M (mul_mem y_mem_M y_mem_M), ?_⟩
      exact orderOf_comm_q0.symm ▸ dvd_refl 4
    · exact ⟨⁅y, wordProd [.y, .y, .x]⁆,
        commutator_mem_commutator y_mem_M (wordProd_mem_M _), four_dvd_orderOf_comm_x⟩

theorem sporadicCaseOdd_Th
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .Th := by
  have hX : J.subgroupOf J = ⊤ := subgroupOf_self _
  refine sporadicCaseOdd_of_yCensus h32 h33 thAutModel ?_
  rw [hX]
  exact th_yCensus

end CFSG.ComponentClassification.RankTwoSporadic.Th
