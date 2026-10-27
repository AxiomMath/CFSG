module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711e
public import Certificates.Certificate271103
public import Certificates.Certificate271104

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA

section Unique

theorem eq_of_isElemAbelian_of_le_sup {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E P W : Subgroup G} {q : G} (hq : q ^ p = 1)
    (hqN : q ∈ Subgroup.normalizer (E : Set G)) (hP : P = Subgroup.zpowers q ⊔ E)
    (hPc : Nat.card P = p ^ 4) (hEc : Nat.card E = p ^ 3) (hE : IsElemAbelian p E)
    (hfix : ∀ j : ℕ, 0 < j → j < p →
      Nat.card ↥(E ⊓ Subgroup.centralizer ({q ^ j} : Set G)) ≤ p)
    (hWP : W ≤ P) (hW : IsElemAbelian p W) (hWc : p ^ 3 ≤ Nat.card W) : W = E := by
  by_contra hne
  have hWE : ¬ W ≤ E := fun h => hne (Subgroup.eq_of_le_of_card_ge h (hEc ▸ hWc))
  obtain ⟨w, hwW, hwE⟩ := Set.not_subset.1 hWE
  have hEP : E ≤ P := hP ▸ le_sup_right
  have hzN : Subgroup.zpowers q ≤ Subgroup.normalizer (E : Set G) := Subgroup.zpowers_le.2 hqN
  have hwP : w ∈ ((Subgroup.zpowers q ⊔ E : Subgroup G) : Set G) := hP ▸ hWP hwW
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzN] at hwP
  obtain ⟨x, hx, e, he, rfl⟩ := Set.mem_mul.1 hwP
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hq1 : orderOf q ∣ p := orderOf_dvd_of_pow_eq_one hq
  set j : ℕ := (k % (p : ℤ)).toNat with hj
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hkj : q ^ k = q ^ j := by
    have h1 : q ^ k = q ^ (k % (p : ℤ)) := by
      conv_lhs => rw [← Int.mul_ediv_add_emod k (p : ℤ)]
      rw [zpow_add, zpow_mul, zpow_natCast, hq, one_zpow, one_mul]
    rw [h1, hj, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k hp0.ne')]
  have hjp : j < p := by
    have h1 := Int.emod_lt_of_pos k hp0
    have h2 := Int.emod_nonneg k hp0.ne'
    omega
  have hj0 : 0 < j := by
    by_contra h0
    have hj0' : j = 0 := by omega
    apply hwE
    rw [hkj, hj0', pow_zero, one_mul]
    exact he
  have hcomm : ∀ y ∈ W ⊓ E, y * q ^ j = q ^ j * y := by
    intro y hy
    obtain ⟨hyW, hyE⟩ := Subgroup.mem_inf.1 hy
    have h1 : y * (q ^ k * e) = q ^ k * e * y := isElemAbelian_commute hW hyW hwW
    have h2 : y * e = e * y := isElemAbelian_commute hE hyE he
    rw [hkj] at h1
    have h3 : y * q ^ j * e = q ^ j * y * e := by
      calc y * q ^ j * e = y * (q ^ j * e) := by group
        _ = q ^ j * e * y := h1
        _ = q ^ j * (e * y) := by group
        _ = q ^ j * (y * e) := by rw [h2]
        _ = q ^ j * y * e := by group
    exact mul_right_cancel h3
  have hle : W ⊓ E ≤ E ⊓ Subgroup.centralizer ({q ^ j} : Set G) := by
    intro y hy
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hy).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm y hy
  have hsmall : Nat.card ↥(W ⊓ E) ≤ p := (Subgroup.card_le_of_le hle).trans (hfix j hj0 hjp)
  have e1 := Subgroup.relIndex_mul_card (H := W) (K := P)
  have e2 := Subgroup.relIndex_mul_card (H := E) (K := P)
  have e3 := Subgroup.relIndex_mul_card (H := W ⊓ E) (K := P)
  have hle3 := Subgroup.relIndex_inf_le (H := W) (K := E) (L := P)
  rw [inf_eq_left.2 hWP, hPc] at e1
  rw [inf_eq_left.2 hEP, hPc, hEc] at e2
  rw [inf_eq_left.2 (inf_le_left.trans hWP), hPc] at e3
  have hx1 : W.relIndex P ≤ p := by
    have : W.relIndex P * p ^ 3 ≤ p * p ^ 3 := by
      calc W.relIndex P * p ^ 3 ≤ W.relIndex P * Nat.card W := Nat.mul_le_mul_left _ hWc
        _ = p ^ 4 := e1
        _ = p * p ^ 3 := by ring
    exact Nat.le_of_mul_le_mul_right this (pow_pos hp.pos 3)
  have hx2 : E.relIndex P = p := by
    have : E.relIndex P * p ^ 3 = p * p ^ 3 := by rw [e2]; ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 3) this
  have : p ^ 4 ≤ p ^ 3 := by
    calc p ^ 4 = (W ⊓ E).relIndex P * Nat.card ↥(W ⊓ E) := e3.symm
      _ ≤ (W.relIndex P * E.relIndex P) * p := Nat.mul_le_mul hle3 hsmall
      _ ≤ (p * p) * p := by rw [hx2]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hx1)
      _ = p ^ 3 := by ring
  exact absurd ((Nat.pow_le_pow_iff_right hp.one_lt).1 this) (by norm_num)

end Unique

section NeBot

variable {X : Type} [Group X] {p : ℕ}

theorem ne_bot_of_nonabelian [Finite X] (hp : p.Prime) {L B : Subgroup X} (hB : IsElemAbelian p B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X))
    (hB4 : 4 ≤ CFSG.Open.pRank p B) {G : Type} [Group G] [Finite G]
    (τ₀ : (↥L ⧸ Subgroup.center ↥L) ≃* G) {P : Subgroup G} (hP4 : Nat.card P = p ^ 4)
    (hconj : ∀ A : Subgroup G, IsPGroup p A → ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ P)
    (hnab : ∃ x ∈ P, ∃ y ∈ P, ¬ Commute x y) :
    B ⊓ Subgroup.centralizer (L : Set X) ≠ ⊥ := by
  intro hB0
  set R := (Inputs2711d.barHom hin).range with hRdef
  have hRel : IsElemAbelian p R := Inputs2711d.isElemAbelian_range_barHom hB hin
  set A : Subgroup G := R.map τ₀.toMonoidHom with hA
  have hAel : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hRel _
  have hAc : Nat.card A = Nat.card R := Subgroup.card_map_of_injective τ₀.injective
  have hRB := Inputs2711d.card_range_barHom_mul hin
  rw [hB0, Subgroup.card_bot, mul_one] at hRB
  have hBc : p ^ 4 ≤ Nat.card B := by
    rw [Inputs27.card_eq_pow_pRank hp hB]
    exact Nat.pow_le_pow_right hp.pos hB4
  obtain ⟨g, hg⟩ := hconj A (CFSG.Open.IsElemAbelian.isPGroup hAel)
  have hgc : Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
    CFSG.RankThree.Asc83Table.card_map_conj g A
  have heq : A.map (MulAut.conj g).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hg (by rw [hP4, hgc, hAc, hRB]; exact hBc)
  have hel : IsElemAbelian p P := heq ▸ CFSG.SectionRank.isElemAbelian_map hAel _
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  exact hxy (isElemAbelian_commute hel hx hy)

end NeBot

section PairCo1

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness
  CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.AGLEmbedding
  CFSG.AGLEmbedding.R3
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)

@[expose] def co1Mq : Matrix (Fin 3) (Fin 3) (ZMod 5) := !![1, 2, 2; 0, 1, 1; 0, 0, 1]

theorem zmod5_fixed_of_unitriangular {a b d : ZMod 5} (ha : a ≠ 0) (hd : d ≠ 0) {c : Fin 3 → ZMod 5}
    (h : (!![1, a, b; 0, 1, d; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 5)).mulVec c = c) :
    c 1 = 0 ∧ c 2 = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail] at h0 h1
  have hc2 : c 2 = 0 := by
    rcases h1 with h' | h'
    · exact absurd h' hd
    · exact h'
  refine ⟨?_, hc2⟩
  have : a * c 1 = 0 := by rw [hc2] at h0; linear_combination h0
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd h' ha
  · exact h'

theorem co1Mq_pow_fixed (j : ℕ) (hj0 : 0 < j) (hj5 : j < 5) {c : Fin 3 → ZMod 5}
    (hc : (co1Mq ^ j).mulVec c = c) : c 1 = 0 ∧ c 2 = 0 := by
  interval_cases j
  · have hM : co1Mq ^ 1 = !![1, 2, 2; 0, 1, 1; 0, 0, 1] := by decide
    rw [hM] at hc
    exact zmod5_fixed_of_unitriangular (by decide) (by decide) hc
  · have hM : co1Mq ^ 2 = !![1, 4, 1; 0, 1, 2; 0, 0, 1] := by decide
    rw [hM] at hc
    exact zmod5_fixed_of_unitriangular (by decide) (by decide) hc
  · have hM : co1Mq ^ 3 = !![1, 1, 2; 0, 1, 3; 0, 0, 1] := by decide
    rw [hM] at hc
    exact zmod5_fixed_of_unitriangular (by decide) (by decide) hc
  · have hM : co1Mq ^ 4 = !![1, 3, 0; 0, 1, 4; 0, 0, 1] := by decide
    rw [hM] at hc
    exact zmod5_fixed_of_unitriangular (by decide) (by decide) hc

theorem card_inf_centralizer_le_of_actsBy {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    (D : ModuleSpec X p) {g : X} {A : Matrix (Fin D.n) (Fin D.n) (ZMod p)} (hg : ActsBy D g A)
    (i₀ : Fin D.n)
    (hA : ∀ c c' : Fin D.n → ZMod p, A.mulVec c = c → A.mulVec c' = c' → c i₀ = c' i₀ → c = c') :
    Nat.card ↥(D.span ⊓ Subgroup.centralizer ({g} : Set X)) ≤ p := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hmem : ∀ x : ↥(D.span ⊓ Subgroup.centralizer ({g} : Set X)),
      ∃ c : Fin D.n → ZMod p, D.elt c = x ∧ A.mulVec c = c := by
    intro x
    obtain ⟨hxE, hxC⟩ := Subgroup.mem_inf.1 x.2
    obtain ⟨c, hc⟩ := D.exists_elt hxE
    refine ⟨c, hc, ?_⟩
    have h1 := conj_elt D hg c
    have h2 : (x : X) * g = g * x := Subgroup.mem_centralizer_singleton_iff.1 hxC
    have h3 : g * D.elt c * g⁻¹ = D.elt c := by
      rw [hc, ← h2]; group
    rw [h3] at h1
    exact D.elt_injective h1.symm
  choose cf hcf using hmem
  have hinj : Function.Injective fun x => cf x i₀ := by
    intro x y hxy
    have hc := hA _ _ (hcf x).2 (hcf y).2 hxy
    apply Subtype.ext
    rw [← (hcf x).1, ← (hcf y).1, hc]
  have h1 := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_zmod] at h1

theorem co1_gen_data :
    ∃ (E : Subgroup NativeSporadic.Co1) (q : NativeSporadic.Co1) (S : Set NativeSporadic.Co1),
      IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 3 ∧ q ^ 5 = 1 ∧
      q ∈ Subgroup.normalizer (E : Set NativeSporadic.Co1) ∧
      IsPGroup 5 ↥(Subgroup.zpowers q ⊔ E) ∧ (∃ e ∈ E, ¬ Commute q e) ∧
      (∀ j : ℕ, 0 < j → j < 5 →
        Nat.card ↥(E ⊓ Subgroup.centralizer ({q ^ j} : Set NativeSporadic.Co1)) ≤ 5) ∧
      Subgroup.closure S = ⊤ ∧
      ∀ s ∈ S, ∃ f ∈ E, f ≠ 1 ∧ Commute s f ∧ ∃ m, s ^ m = 1 ∧ ¬ 5 ∣ m := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h : co1GenCheck = true := Certificates.certificate271103
  unfold co1GenCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hgen, hpcwf⟩, hcov⟩ := h
  obtain ⟨hC, hclos, hgens⟩ := genCheck_sound (spec2 24) hgen
  have hex : ∀ f ∈ co1GenExtra, f ∈ co1GenData.mcert.facts := fun f hf =>
    List.mem_append_right _ hf
  have hmodf : ∀ f ∈ Mod.facts 5 co1Mod, f ∈ co1GenData.mcert.facts := fun f hf =>
    hex f (List.mem_append_left _ (List.mem_append_left _ hf))
  have hpcf : ∀ pc ∈ co1Pcs, ∀ f ∈ pc.facts 5, f ∈ co1GenData.mcert.facts := fun pc hpc f hf =>
    hex f (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨pc, hpc, hf⟩)))
  have hlast : ∀ f ∈ ([.ne [(537, 1), (535, 1)] [(535, 1), (537, 1)] 0,
      .eq [(542, 1)] [(534, 4), (535, 3), (536, 3)], .eq [(546, 1)] [(534, 4), (535, 4), (536, 2)],
      .ne [(542, 1)] [] 0, .ne [(546, 1)] [] 0] : List MFact), f ∈ co1GenData.mcert.facts :=
    fun f hf => hex f (List.mem_append_right _ hf)
  have hindep : ∀ v ∈ nonzeroTriples 5, ∃ q ∈ co1Mod.indep,
      q.1 = v.1 ∧ q.2.1 = v.2.1 ∧ q.2.2.1 = v.2.2 := by
    intro v hv
    obtain ⟨q, hq, hqv⟩ := List.any_eq_true.1 (List.all_eq_true.1 hcov v hv)
    simp only [Bool.and_eq_true, beq_iff_eq] at hqv
    exact ⟨q, hq, hqv.1.1, hqv.1.2, hqv.2⟩
  obtain ⟨DS₀, hn3, hact, hspan⟩ := exists_moduleSpec_core (spec2 24) hC co1Mod hmodf hindep
  obtain ⟨n, m, a, g, M, hcomm, hpw, hind, hac⟩ := DS₀
  simp only at hn3
  subst hn3
  set DS : ModuleSpec NativeSporadic.Co1 5 := ⟨3, m, a, g, M, hcomm, hpw, hind, hac⟩ with hDS
  have hqact : (⟨537, 5, [1, 2, 2, 0, 1, 1, 0, 0, 1]⟩ : Act) ∈ co1Mod.acts := by
    simp [co1Mod]
  obtain ⟨jq, hjq, hMq⟩ := hact _ hqact
  set q := regUnit (spec2 24) hC 537 with hqdef
  set E : Subgroup NativeSporadic.Co1 := DS.span with hE
  have hEc : Nat.card E = 5 ^ 3 := DS.card_span Nat.prime_five
  have hEel : IsElemAbelian 5 E := ⟨⟨⟨fun a b => Subtype.ext (DS.mul_comm_of_mem a.2 b.2)⟩⟩,
    fun x hx => DS.pow_eq_one_of_mem hx⟩
  have hbasis : ∀ r ∈ [534, 535, 536], regUnit (spec2 24) hC r ∈ E := by
    intro r hr
    rw [hspan]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact Subgroup.subset_closure ⟨1, rfl⟩
    · exact Subgroup.subset_closure ⟨2, rfl⟩
  obtain ⟨pcq, hpcq, hpcqr, hpcqo⟩ : ∃ pc ∈ co1Pcs, pc.reg = 537 ∧ pc.ord = 5 :=
    ⟨_, List.mem_cons_self, rfl, rfl⟩
  have hq537 : MFact.ord 537 5 ∈ co1GenData.mcert.facts := by
    have := hpcf pcq hpcq (.ord pcq.reg pcq.ord) (by simp [Pc.facts])
    rwa [hpcqr, hpcqo] at this
  have hfixo : ∀ r ∈ [542, 546], MFact.ord r 5 ∈ co1GenData.mcert.facts := by
    intro r hr
    have hfx : co1GenData.fixOrd = [(542, 5), (546, 5)] := rfl
    have hmem : MFact.ord r 5 ∈ co1GenData.fixOrd.map (fun q => MFact.ord q.1 q.2) := by
      rw [hfx]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hmem)))
  have hord : ∀ r ∈ [534, 535, 536, 537, 542, 546],
      ∃ e, MFact.ord r e ∈ co1GenData.mcert.facts := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨5, basis_ord co1Mod hmodf 0⟩
    · exact ⟨5, basis_ord co1Mod hmodf 1⟩
    · exact ⟨5, basis_ord co1Mod hmodf 2⟩
    · exact ⟨5, hq537⟩
    · exact ⟨5, hfixo 542 (by simp)⟩
    · exact ⟨5, hfixo 546 (by simp)⟩
  have hHO : ∀ w : Word, (∀ x ∈ w, x.1 ∈ [534, 535, 536, 537, 542, 546]) →
      HasOrd co1GenData.mcert w := fun w hw x hx => hord _ (hw x hx)
  have hq5 : q ^ 5 = 1 := regUnit_pow (spec2 24) hC hq537
  have hMeq : DS.M jq = co1Mq := by
    ext k i
    rw [hMq k i]
    fin_cases k <;> fin_cases i <;> rfl
  have hqA : ActsBy DS q co1Mq := hMeq ▸ hjq ▸ actsBy_g DS jq
  have hqN : q ∈ Subgroup.normalizer (E : Set NativeSporadic.Co1) := by
    have hfin : Nat.card ↥(Subgroup.closure (Set.range DS.a)) ≠ 0 := by
      rw [show Subgroup.closure (Set.range DS.a) = E from rfl, hEc]
      norm_num
    haveI : Finite ↥(Subgroup.closure (Set.range DS.a)) := Nat.finite_of_card_ne_zero hfin
    show q ∈ Subgroup.normalizer (Subgroup.closure (Set.range DS.a) : Set NativeSporadic.Co1)
    refine CFSG.RankThree.Asc83Table.mem_normalizer_closure_of_conj_mem fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    have h1 := DS.elt_col jq i
    rw [hjq] at h1
    rw [← h1]
    exact DS.elt_mem _
  have hchain := chain_isPGroup (spec2 24) hC (p := 5) co1Pcs hpcwf hpcf
  have hregs : ∀ r ∈ [537, 534, 535, 536], ∃ pc ∈ co1Pcs, pc.reg = r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)), rfl⟩
  have hinS : ∀ r ∈ [537, 534, 535, 536], regUnit (spec2 24) hC r ∈
      Subgroup.closure {u | ∃ pc ∈ co1Pcs, u = regUnit (spec2 24) hC pc.reg} := by
    intro r hr
    obtain ⟨pc, hpc, hpcr⟩ := hregs r hr
    exact Subgroup.subset_closure ⟨pc, hpc, by rw [hpcr]⟩
  have hPeq : Subgroup.closure {u | ∃ pc ∈ co1Pcs, u = regUnit (spec2 24) hC pc.reg} =
      Subgroup.zpowers q ⊔ E := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro u ⟨pc, hpc, rfl⟩
      simp only [co1Pcs, List.mem_cons, List.not_mem_nil, or_false] at hpc
      rcases hpc with rfl | rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (hbasis 534 (by simp))
      · exact Subgroup.mem_sup_right (hbasis 535 (by simp))
      · exact Subgroup.mem_sup_right (hbasis 536 (by simp))
    · refine sup_le (Subgroup.zpowers_le.2 (hinS 537 (by simp))) ?_
      rw [hspan, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hinS 534 (by simp)
      · exact hinS 535 (by simp)
      · exact hinS 536 (by simp)
  have hPp : IsPGroup 5 ↥(Subgroup.zpowers q ⊔ E) := hPeq ▸ hchain
  have hnab : ∃ e ∈ E, ¬ Commute q e := by
    have hw1 : HasOrd co1GenData.mcert [(537, 1), (535, 1)] := by
      refine hHO _ fun x hx => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp
    have hw2 : HasOrd co1GenData.mcert [(535, 1), (537, 1)] := by
      refine hHO _ fun x hx => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp
    refine ⟨_, hbasis 535 (by simp), fun hc => ?_⟩
    have hne := regUnit_ne (spec2 24) hC
      (hlast (.ne [(537, 1), (535, 1)] [(535, 1), (537, 1)] 0) (by simp)) hw1 hw2
    apply hne
    simp only [wordUnit, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, pow_one,
      mul_one]
    exact hc.eq
  have hfix : ∀ j : ℕ, 0 < j → j < 5 →
      Nat.card ↥(E ⊓ Subgroup.centralizer ({q ^ j} : Set NativeSporadic.Co1)) ≤ 5 := by
    intro j hj0 hj5
    refine card_inf_centralizer_le_of_actsBy DS (actsBy_pow DS hqA j) 0 fun c c' hc hc' h0 => ?_
    have hx := co1Mq_pow_fixed j hj0 hj5 hc
    have hy := co1Mq_pow_fixed j hj0 hj5 hc'
    funext i
    fin_cases i
    · exact h0
    · exact hx.1.trans hy.1.symm
    · exact hx.2.trans hy.2.symm
  have hf : ∀ r ∈ [542, 546], regUnit (spec2 24) hC r ∈ E ∧ regUnit (spec2 24) hC r ≠ 1 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨?_, regUnit_ne_one' (spec2 24) hC (hlast (.ne [(542, 1)] [] 0) (by simp))
        (hHO _ (by simp))⟩
      rw [regUnit_eq' (spec2 24) hC (hlast (.eq [(542, 1)] [(534, 4), (535, 3), (536, 3)])
        (by simp)) (hHO _ (by simp)) (hHO _ (by simp))]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup (spec2 24) hC E _ fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hbasis 534 (by simp)
        · exact hbasis 535 (by simp)
        · exact hbasis 536 (by simp)
    · refine ⟨?_, regUnit_ne_one' (spec2 24) hC (hlast (.ne [(546, 1)] [] 0) (by simp))
        (hHO _ (by simp))⟩
      rw [regUnit_eq' (spec2 24) hC (hlast (.eq [(546, 1)] [(534, 4), (535, 4), (536, 2)])
        (by simp)) (hHO _ (by simp)) (hHO _ (by simp))]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup (spec2 24) hC E _ fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hbasis 534 (by simp)
        · exact hbasis 535 (by simp)
        · exact hbasis 536 (by simp)
  refine ⟨E, q, {v | ∃ g ∈ co1GenData.gens, v = regUnit (spec2 24) hC g.reg}, hEel, hEc, hq5, hqN,
    hPp, hnab, hfix, hclos, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨hcomm, hpow, hndvd⟩ := hgens g hg
  have hgl : co1GenData.gens =
      [⟨538, 8, [542]⟩, ⟨539, 12, [542]⟩, ⟨540, 8, [546]⟩, ⟨541, 7, [546]⟩] := rfl
  rw [hgl] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨_, (hf 542 (by simp)).1, (hf 542 (by simp)).2, hcomm 542 (by simp), _, hpow, hndvd⟩
  · exact ⟨_, (hf 542 (by simp)).1, (hf 542 (by simp)).2, hcomm 542 (by simp), _, hpow, hndvd⟩
  · exact ⟨_, (hf 546 (by simp)).1, (hf 546 (by simp)).2, hcomm 546 (by simp), _, hpow, hndvd⟩
  · exact ⟨_, (hf 546 (by simp)).1, (hf 546 (by simp)).2, hcomm 546 (by simp), _, hpow, hndvd⟩

theorem sporPairCase_Co1_five
    (hBr : SporadicBridges) : Inputs2711c.SporPairCase .Co1 5 := by
  intro X _ _ hp _ L B _ hLq hB _ _ hrk4 _ _ _ hC1 hname hin _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨σ⟩ := hname
  obtain ⟨β⟩ := hBr .Co1
  haveI : Finite NativeSporadic.Co1 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨E, q, S, hE, hEc, hq5, hqN, hPp, hnab, hfix, hS, hSf⟩ := co1_gen_data
  set P : Subgroup NativeSporadic.Co1 := Subgroup.zpowers q ⊔ E with hPdef
  have hEP : E ≤ P := le_sup_right
  have hqP : q ∈ P := Subgroup.mem_sup_left (Subgroup.mem_zpowers q)
  have hqE : q ∉ E := by
    intro hq
    obtain ⟨e, he, hqe⟩ := hnab
    exact hqe (isElemAbelian_commute hE hq he)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hPp
  have hk4 : 4 ≤ k := by
    by_contra h
    have hle : Nat.card P ≤ Nat.card E := by
      rw [hk, hEc]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact hqE ((Subgroup.eq_of_le_of_card_ge hEP hle) ▸ hqP)
  have hk4' : k ≤ 4 := by
    have hdvd : 5 ^ k ∣ 5 ^ 4 * 6652442890469376 := by
      rw [← hk, show 5 ^ 4 * 6652442890469376 = 4157776806543360000 by norm_num,
        ← CFSG.Sporadic.Co1.card_Co1]
      exact Subgroup.card_subgroup_dvd_card P
    have hcop : Nat.Coprime (5 ^ k) 6652442890469376 :=
      Nat.Coprime.pow_left k (by norm_num)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hcop.dvd_of_dvd_mul_right hdvd)
  have hPc : Nat.card P = 5 ^ 4 := by rw [hk, show k = 4 by omega]
  have hsyl : Nat.card P = 5 ^ (Nat.card NativeSporadic.Co1).factorization 5 := by
    rw [hPc, CFSG.Sporadic.Co1.card_Co1, factorization_eq_of_eq Nat.prime_five
      (show 4157776806543360000 = 5 ^ 4 * 6652442890469376 by norm_num) (by norm_num)]
  have huniq : ∀ W : Subgroup NativeSporadic.Co1, W ≤ P → IsElemAbelian 5 W →
      5 ^ 3 ≤ Nat.card W → W = E := fun W hWP hW hWc =>
    eq_of_isElemAbelian_of_le_sup Nat.prime_five hq5 hqN rfl hPc hEc hE hfix hWP hW hWc
  have hconjP : ∀ A : Subgroup NativeSporadic.Co1, IsPGroup 5 A →
      ∃ g : NativeSporadic.Co1, A.map (MulAut.conj g).toMonoidHom ≤ P := fun A hA =>
    exists_map_conj_le hsyl hA
  have hB0 : B ⊓ Subgroup.centralizer (L : Set X) ≠ ⊥ := by
    refine ne_bot_of_nonabelian (G := NativeSporadic.Co1) (P := P) hp hB hin hrk4 ?_ ?_ ?_ ?_
    · exact σ.trans β.symm
    · exact hPc
    · exact hconjP
    · obtain ⟨e, he, hqe⟩ := hnab
      exact ⟨q, hqP, e, hEP he, hqe⟩
  have hB₀el : IsElemAbelian 5 (B ⊓ Subgroup.centralizer (L : Set X)) :=
    isElemAbelian_mono hB inf_le_left
  have hB₀c : Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) = 5 := by
    have h1 := Inputs27.card_eq_pow_pRank hp hB₀el
    have h2 : Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) ≠ 1 := fun h =>
      hB0 (Subgroup.card_eq_one.1 h)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hC1 with h | h
    · rw [h1, h, pow_zero] at h2
      exact absurd rfl h2
    · rw [h1, h, pow_one]
  have hBc : 625 ≤ Nat.card B := by
    rw [Inputs27.card_eq_pow_pRank hp hB]
    calc 625 = 5 ^ 4 := by norm_num
      _ ≤ 5 ^ CFSG.Open.pRank 5 B := Nat.pow_le_pow_right (by norm_num) hrk4
  have hR := Inputs2711d.card_range_barHom_mul hin
  rw [hB₀c] at hR
  have hR125 : 125 ≤ Nat.card (Inputs2711d.barHom hin).range := by omega
  refine eq_gammaTwo_of_conj_rankOne (G := NativeSporadic.Co1) (W := E) (S := S) hp hLq hB hin hB0
    ?_ ?_ ?_ ?_ ?_
  · exact σ.trans β.symm
  · intro A hA hAc
    have hA' : IsElemAbelian 5 A :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 5 A).1 hA
    obtain ⟨g, hg⟩ := hconjP A (CFSG.Open.IsElemAbelian.isPGroup hA')
    refine ⟨g, le_of_eq (huniq _ hg (CFSG.SectionRank.isElemAbelian_map hA' _) ?_)⟩
    rw [card_map_conj, ← hEc]
    exact hAc
  · rw [hEc]
    exact hR125
  · exact hS
  · exact hSf

end PairCo1

section UniqueFour

theorem eq_of_isElemAbelian_of_fixed {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E P W : Subgroup G} (hEP : E ≤ P) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 4)
    (hPc : Nat.card P = p ^ 6)
    (hfix : ∀ w ∈ P, w ∉ E → Nat.card ↥(E ⊓ Subgroup.centralizer ({w} : Set G)) ≤ p ^ 2)
    {x y : G} (hx : x ∈ P) (hy : y ∈ P)
    (hxy : Nat.card ↥(E ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)) ≤ p)
    (hWP : W ≤ P) (hW : IsElemAbelian p W) (hWc : p ^ 4 ≤ Nat.card W) : W = E := by
  by_contra hne
  have hWE : ¬ W ≤ E := fun h => hne (Subgroup.eq_of_le_of_card_ge h (hEc ▸ hWc))
  obtain ⟨w, hwW, hwE⟩ := Set.not_subset.1 hWE
  have hle : W ⊓ E ≤ E ⊓ Subgroup.centralizer ({w} : Set G) := by
    intro z hz
    obtain ⟨hzW, hzE⟩ := Subgroup.mem_inf.1 hz
    refine Subgroup.mem_inf.2 ⟨hzE, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute hW hzW hwW
  have hsmall : Nat.card ↥(W ⊓ E) ≤ p ^ 2 :=
    (Subgroup.card_le_of_le hle).trans (hfix w (hWP hwW) hwE)
  have e1 := Subgroup.relIndex_mul_card (H := W) (K := W ⊔ E)
  have e2 := Subgroup.relIndex_mul_card (H := E) (K := W ⊔ E)
  have e3 := Subgroup.relIndex_mul_card (H := W ⊓ E) (K := W ⊔ E)
  have hle3 := Subgroup.relIndex_inf_le (H := W) (K := E) (L := W ⊔ E)
  rw [inf_eq_left.2 le_sup_left] at e1
  rw [inf_eq_left.2 le_sup_right] at e2
  rw [inf_eq_left.2 (inf_le_left.trans le_sup_left)] at e3
  have hNpos : 0 < Nat.card ↥(W ⊔ E) := Nat.card_pos
  have hprod : Nat.card W * Nat.card E ≤ Nat.card ↥(W ⊔ E) * Nat.card ↥(W ⊓ E) := by
    have h1 : Nat.card ↥(W ⊔ E) * (Nat.card W * Nat.card E) ≤
        Nat.card ↥(W ⊔ E) * (Nat.card ↥(W ⊔ E) * Nat.card ↥(W ⊓ E)) := by
      calc Nat.card ↥(W ⊔ E) * (Nat.card W * Nat.card E)
          = (W ⊓ E).relIndex (W ⊔ E) * Nat.card ↥(W ⊓ E) * Nat.card W * Nat.card E := by
            rw [e3]; ring
        _ ≤ (W.relIndex (W ⊔ E) * E.relIndex (W ⊔ E)) * Nat.card ↥(W ⊓ E) * Nat.card W *
            Nat.card E := by gcongr
        _ = (W.relIndex (W ⊔ E) * Nat.card W) * (E.relIndex (W ⊔ E) * Nat.card E) *
            Nat.card ↥(W ⊓ E) := by ring
        _ = Nat.card ↥(W ⊔ E) * (Nat.card ↥(W ⊔ E) * Nat.card ↥(W ⊓ E)) := by
            rw [e1, e2]; ring
    exact Nat.le_of_mul_le_mul_left h1 hNpos
  have hsupP : W ⊔ E ≤ P := sup_le hWP hEP
  have hNle : Nat.card ↥(W ⊔ E) ≤ p ^ 6 := hPc ▸ Subgroup.card_le_of_le hsupP
  have hp8 : p ^ 8 ≤ Nat.card ↥(W ⊔ E) * Nat.card ↥(W ⊓ E) := by
    calc p ^ 8 = p ^ 4 * p ^ 4 := by ring
      _ ≤ Nat.card W * Nat.card E := by rw [hEc]; exact Nat.mul_le_mul_right _ hWc
      _ ≤ _ := hprod
  have hppos : 0 < p := hp.pos
  have hN6 : p ^ 6 ≤ Nat.card ↥(W ⊔ E) := by
    by_contra hlt
    have h1 : Nat.card ↥(W ⊔ E) * Nat.card ↥(W ⊓ E) < p ^ 6 * p ^ 2 :=
      calc Nat.card ↥(W ⊔ E) * Nat.card ↥(W ⊓ E) ≤ Nat.card ↥(W ⊔ E) * p ^ 2 :=
            Nat.mul_le_mul_left _ hsmall
        _ < p ^ 6 * p ^ 2 := Nat.mul_lt_mul_of_pos_right (not_le.1 hlt) (pow_pos hppos 2)
    have h2 : p ^ 6 * p ^ 2 = p ^ 8 := by ring
    omega
  have hsupeq : W ⊔ E = P := Subgroup.eq_of_le_of_card_ge hsupP (hPc ▸ hN6)
  have hbig : p ^ 2 ≤ Nat.card ↥(W ⊓ E) := by
    by_contra hlt
    have h1 : Nat.card ↥(W ⊔ E) * Nat.card ↥(W ⊓ E) < p ^ 6 * p ^ 2 :=
      calc Nat.card ↥(W ⊔ E) * Nat.card ↥(W ⊓ E) ≤ p ^ 6 * Nat.card ↥(W ⊓ E) :=
            Nat.mul_le_mul_right _ hNle
        _ < p ^ 6 * p ^ 2 := Nat.mul_lt_mul_of_pos_left (not_le.1 hlt) (pow_pos hppos 6)
    have h2 : p ^ 6 * p ^ 2 = p ^ 8 := by ring
    omega
  have hcen : W ⊓ E ≤ E ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G) := by
    intro z hz
    obtain ⟨hzW, hzE⟩ := Subgroup.mem_inf.1 hz
    have hPC : P ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [← hsupeq]
      refine sup_le (fun v hv => ?_) (fun v hv => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact isElemAbelian_commute hW hv hzW
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact isElemAbelian_commute hE hv hzE
    have hzx : z * x = x * z := (Subgroup.mem_centralizer_singleton_iff.1 (hPC hx)).symm
    have hzy : z * y = y * z := (Subgroup.mem_centralizer_singleton_iff.1 (hPC hy)).symm
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hzE, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hzx
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hzy
  have h1 := (Subgroup.card_le_of_le hcen).trans hxy
  have h2 : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end UniqueFour

section Cosets

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3

variable {X : Type} [Group X] {p : ℕ} [Fact p.Prime]

theorem exists_eq_mul_of_actsBy [Finite X] (D : ModuleSpec X p) (P : Subgroup X)
    (hEP : D.span ≤ P) {k : ℕ} (g : Fin k → X) (A : Fin k → Matrix (Fin D.n) (Fin D.n) (ZMod p))
    (hg : ∀ a, g a ∈ P) (hA : ∀ a, ActsBy D (g a) (A a))
    (hd : ∀ a b : Fin k, a ≠ b → A a ≠ A b) (hP : Nat.card P ≤ k * Nat.card D.span) :
    ∀ w ∈ P, ∃ a, ∃ e ∈ D.span, w = g a * e := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let f : Fin k × D.span → P := fun x =>
    ⟨g x.1 * (x.2 : X), P.mul_mem (hg x.1) (hEP x.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, e⟩ ⟨b, e'⟩ h
    have h' : g a * (e : X) = g b * (e' : X) := congrArg Subtype.val h
    have hab : a = b := by
      by_contra hne
      apply hd a b hne
      ext r i
      have hcol : g a * D.a i * (g a)⁻¹ = g b * D.a i * (g b)⁻¹ := by
        have hga : g a = g b * ((e' : X) * (e : X)⁻¹) := by
          rw [← mul_assoc]
          exact eq_mul_inv_of_mul_eq h'
        have hc : ((e' : X) * (e : X)⁻¹) * D.a i = D.a i * ((e' : X) * (e : X)⁻¹) :=
          D.mul_comm_of_mem (D.span.mul_mem e'.2 (D.span.inv_mem e.2)) (D.a_mem_span i)
        calc g a * D.a i * (g a)⁻¹
            = g b * (((e' : X) * (e : X)⁻¹) * D.a i * ((e' : X) * (e : X)⁻¹)⁻¹) *
                (g b)⁻¹ := by rw [hga]; group
          _ = g b * D.a i * (g b)⁻¹ := by rw [hc]; group
      have hsa := conj_elt D (hA a) (Pi.single i 1)
      have hsb := conj_elt D (hA b) (Pi.single i 1)
      rw [D.elt_single i] at hsa hsb
      have h2 := congrFun (D.elt_injective (hsa.symm.trans (hcol.trans hsb))) r
      simpa [Matrix.mulVec_single] using h2
    subst hab
    have : (e : X) = e' := mul_left_cancel h'
    exact Prod.ext rfl (Subtype.ext this)
  have hcard : Nat.card P ≤ Nat.card (Fin k × D.span) := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
    exact hP
  have hbij := hf.bijective_of_nat_card_le hcard
  intro w hw
  obtain ⟨⟨a, e⟩, he⟩ := hbij.2 ⟨w, hw⟩
  exact ⟨a, e, e.2, (congrArg Subtype.val he).symm⟩

theorem exists_fixed_of_mem_centralizer (D : ModuleSpec X p) {g : X}
    {A : Matrix (Fin D.n) (Fin D.n) (ZMod p)} (hg : ActsBy D g A) {x : X} (hxE : x ∈ D.span)
    (hxC : x ∈ Subgroup.centralizer ({g} : Set X)) :
    ∃ c : Fin D.n → ZMod p, D.elt c = x ∧ A.mulVec c = c := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨c, hc⟩ := D.exists_elt hxE
  refine ⟨c, hc, ?_⟩
  have h1 := conj_elt D hg c
  have h2 : x * g = g * x := Subgroup.mem_centralizer_singleton_iff.1 hxC
  have h3 : g * D.elt c * g⁻¹ = D.elt c := by
    rw [hc, ← h2]; group
  rw [h3] at h1
  exact D.elt_injective h1.symm

theorem card_inf_centralizer_le_sq_of_actsBy (D : ModuleSpec X p) {g : X}
    {A : Matrix (Fin D.n) (Fin D.n) (ZMod p)} (hg : ActsBy D g A) (i₀ i₁ : Fin D.n)
    (hA : ∀ c c' : Fin D.n → ZMod p, A.mulVec c = c → A.mulVec c' = c' → c i₀ = c' i₀ →
      c i₁ = c' i₁ → c = c') :
    Nat.card ↥(D.span ⊓ Subgroup.centralizer ({g} : Set X)) ≤ p ^ 2 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hmem : ∀ x : ↥(D.span ⊓ Subgroup.centralizer ({g} : Set X)),
      ∃ c : Fin D.n → ZMod p, D.elt c = x ∧ A.mulVec c = c := fun x =>
    exists_fixed_of_mem_centralizer D hg (Subgroup.mem_inf.1 x.2).1 (Subgroup.mem_inf.1 x.2).2
  choose cf hcf using hmem
  have hinj : Function.Injective fun x => (cf x i₀, cf x i₁) := by
    intro x y hxy
    have hc := hA _ _ (hcf x).2 (hcf y).2 (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
    apply Subtype.ext
    rw [← (hcf x).1, ← (hcf y).1, hc]
  have h1 := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_zmod, ← sq] at h1

theorem card_inf_centralizer_two_le_of_actsBy (D : ModuleSpec X p) {g h : X}
    {A B : Matrix (Fin D.n) (Fin D.n) (ZMod p)} (hg : ActsBy D g A) (hh : ActsBy D h B)
    (i₀ : Fin D.n)
    (hAB : ∀ c c' : Fin D.n → ZMod p, A.mulVec c = c → B.mulVec c = c → A.mulVec c' = c' →
      B.mulVec c' = c' → c i₀ = c' i₀ → c = c') :
    Nat.card ↥(D.span ⊓ Subgroup.centralizer ({g} : Set X) ⊓
      Subgroup.centralizer ({h} : Set X)) ≤ p := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hmem : ∀ x : ↥(D.span ⊓ Subgroup.centralizer ({g} : Set X) ⊓
      Subgroup.centralizer ({h} : Set X)),
      ∃ c : Fin D.n → ZMod p, D.elt c = x ∧ A.mulVec c = c ∧ B.mulVec c = c := by
    intro x
    obtain ⟨hx1, hxh⟩ := Subgroup.mem_inf.1 x.2
    obtain ⟨hxE, hxg⟩ := Subgroup.mem_inf.1 hx1
    obtain ⟨c, hc, hAc⟩ := exists_fixed_of_mem_centralizer D hg hxE hxg
    obtain ⟨c', hc', hBc'⟩ := exists_fixed_of_mem_centralizer D hh hxE hxh
    have hcc : c = c' := D.elt_injective (hc.trans hc'.symm)
    exact ⟨c, hc, hAc, hcc ▸ hBc'⟩
  choose cf hcf using hmem
  have hinj : Function.Injective fun x => cf x i₀ := by
    intro x y hxy
    have hc := hAB _ _ (hcf x).2.1 (hcf x).2.2 (hcf y).2.1 (hcf y).2.2 hxy
    apply Subtype.ext
    rw [← (hcf x).1, ← (hcf y).1, hc]
  have h1 := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_zmod] at h1

end Cosets

section GammaPlanes

variable {X : Type} [Group X] {p : ℕ}

theorem isElemAbelian_sup_of_forall_commute {G : Type} [Group G] {H K : Subgroup G}
    (hH : IsElemAbelian p H) (hK : IsElemAbelian p K) (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) :
    IsElemAbelian p (H ⊔ K) := by
  have hcomm : ∀ a ∈ (H : Set G) ∪ K, ∀ b ∈ (H : Set G) ∪ K, a * b = b * a := by
    rintro a (ha | ha) b (hb | hb)
    · exact isElemAbelian_commute hH ha hb
    · exact hc a ha b hb
    · exact (hc b hb a ha).symm
    · exact isElemAbelian_commute hK ha hb
  have hsup : H ⊔ K = Subgroup.closure ((H : Set G) ∪ K) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hmc : IsMulCommutative (Subgroup.closure ((H : Set G) ∪ K)) :=
    Subgroup.isMulCommutative_closure (fun a ha b hb _ => hcomm a ha b hb)
  have hab : ∀ a ∈ Subgroup.closure ((H : Set G) ∪ K), ∀ b ∈ Subgroup.closure ((H : Set G) ∪ K),
      a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Subgroup.closure ((H : Set G) ∪ K)) ⟨b, hb⟩)
  rw [hsup]
  refine ⟨hmc, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem _ h =>
    rcases h with h | h
    · exact hH.2 _ h
    · exact hK.2 _ h
  | one => exact one_pow p
  | mul a b ha hb h₁ h₂ => rw [(show Commute a b from hab a ha b hb).mul_pow, h₁, h₂, one_mul]
  | inv a _ h => rw [inv_pow, h, inv_one]

theorem card_le_card_range_barHom [Finite X] {L B : Subgroup X} (hB : IsElemAbelian p B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X))
    (hmax : ∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B)
    (hZ : Subgroup.center ↥L = ⊥) {G : Type} [Group G] (τ₀ : (↥L ⧸ Subgroup.center ↥L) ≃* G)
    {T : Subgroup G} (hT : IsElemAbelian p T) :
    Nat.card T ≤ Nat.card (Inputs2711d.barHom hin).range := by
  set θ : G ≃* ↥L := τ₀.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot) with hθ
  set TL : Subgroup X := (T.map θ.toMonoidHom).map L.subtype with hTL
  set B₀ : Subgroup X := B ⊓ Subgroup.centralizer (L : Set X) with hB₀
  have hTLc : Nat.card TL = Nat.card T := by
    rw [hTL, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective θ.injective]
  have hTLel : IsElemAbelian p TL :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hT _) _
  have hTLL : TL ≤ L := Subgroup.map_subtype_le _
  have hB₀el : IsElemAbelian p B₀ := isElemAbelian_mono hB inf_le_left
  have hcomm : ∀ a ∈ TL, ∀ c ∈ B₀, a * c = c * a := fun a ha c hc =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 a (hTLL ha)
  have hinf : TL ⊓ B₀ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzT, hzB⟩ := Subgroup.mem_inf.1 hz
    have hzL : z ∈ L := hTLL hzT
    have hzZ : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hzB).2 g g.2)
    rw [hZ, Subgroup.mem_bot] at hzZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hzZ
  have hAc : Nat.card ↥(TL ⊔ B₀) = Nat.card T * Nat.card B₀ := by
    have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute TL B₀ hcomm).1
    rw [hinf, Subgroup.card_bot, mul_one, hTLc] at h
    exact h
  have hAle : TL ⊔ B₀ ≤ B ⊔ L := sup_le (hTLL.trans le_sup_right) (inf_le_left.trans le_sup_left)
  have hAel : IsElemAbelian p (TL ⊔ B₀) := isElemAbelian_sup_of_forall_commute hTLel hB₀el hcomm
  have h1 := hmax _ hAle hAel
  rw [hAc, ← Inputs2711d.card_range_barHom_mul hin] at h1
  exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos

theorem eq_gammaTwo_of_conj_planes [Finite X] (hp : p.Prime) {L B : Subgroup X}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hB : IsElemAbelian p B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X))
    {G : Type} [Group G] [Finite G] (τ₀ : (↥L ⧸ Subgroup.center ↥L) ≃* G) {T : Subgroup G}
    (hconj : ∀ A : Subgroup G, IsElemAbelian p A → Nat.card T ≤ Nat.card A →
      ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ T)
    (hTc : Nat.card T ≤ Nat.card (Inputs2711d.barHom hin).range) {S : Set G}
    (hS : Subgroup.closure S = ⊤)
    (hSl : ∀ s ∈ S, ∃ f₁ ∈ T, ∃ f₂ ∈ T, f₁ ≠ 1 ∧ f₂ ∉ Subgroup.zpowers f₁ ∧ Commute s f₁ ∧
      Commute s f₂ ∧ ∃ m, s ^ m = 1 ∧ ¬ p ∣ m) :
    L = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      L ⊓ Subgroup.normalizer (U : Set X) := by
  set R := (Inputs2711d.barHom hin).range with hRdef
  have hRel : IsElemAbelian p R := Inputs2711d.isElemAbelian_range_barHom hB hin
  set A : Subgroup G := R.map τ₀.toMonoidHom with hA
  have hAel : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hRel _
  have hAc : Nat.card A = Nat.card R := Subgroup.card_map_of_injective τ₀.injective
  obtain ⟨g, hg⟩ := hconj A hAel (hAc ▸ hTc)
  set τ : (↥L ⧸ Subgroup.center ↥L) ≃* G := τ₀.trans (MulAut.conj g) with hτdef
  have hτ : R.map τ.toMonoidHom = A.map (MulAut.conj g).toMonoidHom := by
    rw [hA, Subgroup.map_map]
    rfl
  have hWeq : R.map τ.toMonoidHom = T := by
    rw [hτ]
    refine Subgroup.eq_of_le_of_card_ge hg ?_
    rw [CFSG.RankThree.Asc83Table.card_map_conj, hAc]
    exact hTc
  refine eq_gammaTwo_of_gen hp hLq hB hin τ hS fun s hs => ?_
  obtain ⟨f₁, hf₁T, f₂, hf₂T, hf₁, hf₂, hs₁, hs₂, m, hm, hpm⟩ := hSl s hs
  rw [← hWeq] at hf₁T hf₂T
  obtain ⟨r₁, ⟨b₁, rfl⟩, hb₁⟩ := hf₁T
  obtain ⟨r₂, ⟨b₂, rfl⟩, hb₂⟩ := hf₂T
  have hτ₁ : τ (Inputs2711d.barHom hin b₁) = f₁ := hb₁
  have hτ₂ : τ (Inputs2711d.barHom hin b₂) = f₂ := hb₂
  have hb₁1 : Inputs2711d.barHom hin b₁ ≠ 1 := fun h => hf₁ (by rw [← hτ₁, h, map_one])
  have hb₂z : Inputs2711d.barHom hin b₂ ∉ Subgroup.zpowers (Inputs2711d.barHom hin b₁) := by
    intro h
    apply hf₂
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    rw [← hτ₂, ← hk, map_zpow, hτ₁]
    exact Subgroup.zpow_mem_zpowers _ k
  obtain ⟨U, hUB, hU2, hU⟩ := exists_rankTwo_of_pair hp hB hin b₁ b₂ hb₁1 hb₂z
  refine ⟨U, hUB, hU2, fun u => ?_, m, hm, hpm⟩
  have hmem := Subgroup.mem_map_of_mem τ.toMonoidHom (hU u)
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmem
  exact commute_of_mem_sup_zpowers (hτ₁ ▸ hs₁) (hτ₂ ▸ hs₂) hmem

end GammaPlanes

section PairHN

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness
  CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.AGLEmbedding
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaHN
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)

@[expose] def hnM1 : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![1, 1, 0, 2; 0, 1, 0, 2; 0, 0, 1, 2; 0, 0, 0, 1]

@[expose] def hnM2 : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![1, 0, 2, 2; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]

theorem hnM_distinct : ∀ a b : Fin 9, a ≠ b →
    hnM1 ^ (a.val / 3) * hnM2 ^ (a.val % 3) ≠ hnM1 ^ (b.val / 3) * hnM2 ^ (b.val % 3) := by
  decide

theorem hnM_fixed : ∀ a : Fin 9, a ≠ 0 → ∀ d0 d1 d2 d3 : ZMod 3,
    (hnM1 ^ (a.val / 3) * hnM2 ^ (a.val % 3)).mulVec ![d0, d1, d2, d3] = ![d0, d1, d2, d3] →
    d0 = 0 → (if a.val < 3 then d1 else d2) = 0 → d1 = 0 ∧ d2 = 0 ∧ d3 = 0 := by
  decide

theorem hnM_common : ∀ d0 d1 d2 d3 : ZMod 3,
    hnM1.mulVec ![d0, d1, d2, d3] = ![d0, d1, d2, d3] →
    hnM2.mulVec ![d0, d1, d2, d3] = ![d0, d1, d2, d3] → d0 = 0 → d1 = 0 ∧ d2 = 0 ∧ d3 = 0 := by
  decide

theorem zmod3_vec_four_eq (d : Fin 4 → ZMod 3) : ![d 0, d 1, d 2, d 3] = d := by
  funext k
  fin_cases k <;> rfl

theorem actMatN_hnMod_zero : actMatN 3 4 (hnMod.acts.getD 0 default) = hnM1 := by
  decide

theorem actMatN_hnMod_one : actMatN 3 4 (hnMod.acts.getD 1 default) = hnM2 := by
  decide

theorem hnMq_det (a : Fin 9) (ha : a ≠ 0) (c c' : Fin 4 → ZMod 3)
    (hc : (hnM1 ^ (a.val / 3) * hnM2 ^ (a.val % 3)).mulVec c = c)
    (hc' : (hnM1 ^ (a.val / 3) * hnM2 ^ (a.val % 3)).mulVec c' = c') (h0 : c 0 = c' 0)
    (h1 : c (if a.val < 3 then 1 else 2) = c' (if a.val < 3 then 1 else 2)) : c = c' := by
  set d := c - c' with hd
  have hdf : (hnM1 ^ (a.val / 3) * hnM2 ^ (a.val % 3)).mulVec d = d := by
    rw [hd, Matrix.mulVec_sub, hc, hc']
  have hd0 : d 0 = 0 := by rw [hd, Pi.sub_apply, h0, sub_self]
  have hd1 : (if a.val < 3 then d 1 else d 2) = 0 := by
    split_ifs with h
    · rw [if_pos h] at h1
      rw [hd, Pi.sub_apply, h1, sub_self]
    · rw [if_neg h] at h1
      rw [hd, Pi.sub_apply, h1, sub_self]
  rw [← zmod3_vec_four_eq d] at hdf
  obtain ⟨e1, e2, e3⟩ := hnM_fixed a ha (d 0) (d 1) (d 2) (d 3) hdf hd0 hd1
  have hd' : d = 0 := by
    rw [← zmod3_vec_four_eq d, hd0, e1, e2, e3]
    funext k
    fin_cases k <;> rfl
  exact sub_eq_zero.1 hd'

theorem hnM_common_det (c c' : Fin 4 → ZMod 3) (hc₁ : hnM1.mulVec c = c) (hc₂ : hnM2.mulVec c = c)
    (hc₁' : hnM1.mulVec c' = c') (hc₂' : hnM2.mulVec c' = c') (h0 : c 0 = c' 0) : c = c' := by
  set d := c - c' with hd
  have hd₁ : hnM1.mulVec d = d := by rw [hd, Matrix.mulVec_sub, hc₁, hc₁']
  have hd₂ : hnM2.mulVec d = d := by rw [hd, Matrix.mulVec_sub, hc₂, hc₂']
  have hd0 : d 0 = 0 := by rw [hd, Pi.sub_apply, h0, sub_self]
  rw [← zmod3_vec_four_eq d] at hd₁ hd₂
  obtain ⟨e1, e2, e3⟩ := hnM_common (d 0) (d 1) (d 2) (d 3) hd₁ hd₂ hd0
  have hd' : d = 0 := by
    rw [← zmod3_vec_four_eq d, hd0, e1, e2, e3]
    funext k
    fin_cases k <;> rfl
  exact sub_eq_zero.1 hd'

theorem hn_conj_of_facts [Fact (Nat.Prime 3)] {C : MCert}
    (hC : mcertCheck (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 C = true)
    (hf : ∀ f ∈ hnMod.facts 3, f ∈ C.facts) (hw : hnMod.wf 3 = true)
    (hpcwf : pcWf (hnTops ++ hnMod.basisPc 3) = true)
    (hpcf : ∀ q ∈ hnTops ++ hnMod.basisPc 3, ∀ f ∈ q.facts 3, f ∈ C.facts) :
    ∀ A : Subgroup NativeSporadic.HN, IsElemAbelian 3 A → 3 ^ 4 ≤ Nat.card A →
      ∃ g : NativeSporadic.HN, A.map (MulAut.conj g).toMonoidHom ≤
        (NMod.spec (specP 5 133) hC hnMod hf hw).span := by
  have hN : Nat.card NativeSporadic.HN = 273030912000000 := CFSG.Sporadic.HN.card_HN
  haveI : Finite NativeSporadic.HN := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  set DS := NMod.spec (specP 5 133) hC hnMod hf hw with hDS
  set P : Subgroup NativeSporadic.HN :=
    Subgroup.closure {u | ∃ q ∈ hnTops ++ hnMod.basisPc 3, u = regUnit (specP 5 133) hC q.reg}
    with hP
  have hPgrp : IsPGroup 3 P := chain_isPGroup (specP 5 133) hC _ hpcwf hpcf
  have hspanP : DS.span ≤ P := by
    rw [ModuleSpec.span, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨q, hq, hqreg⟩ : ∃ q ∈ hnMod.basisPc 3, q.reg = hnMod.basis.getD i.val 0 :=
      ⟨_, List.mem_map.2 ⟨i.val, List.mem_range.2 i.2, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨q, List.mem_append.2 (Or.inr hq), by rw [hqreg]; rfl⟩
  have ht0 : 0 < hnTops.length := by decide
  have ht1 : 1 < hnTops.length := by decide
  have hq₁P : regUnit (specP 5 133) hC 13 ∈ P :=
    Subgroup.subset_closure ⟨hnTops[0]'ht0, List.mem_append_left _ (List.getElem_mem ht0), rfl⟩
  have hq₂P : regUnit (specP 5 133) hC 15 ∈ P :=
    Subgroup.subset_closure ⟨hnTops[1]'ht1, List.mem_append_left _ (List.getElem_mem ht1), rfl⟩
  have hA₁ : ActsBy DS (regUnit (specP 5 133) hC 13) hnM1 := by
    have h := actsBy_g DS ⟨0, (by decide : 0 < hnMod.acts.length)⟩
    rwa [show DS.M ⟨0, (by decide : 0 < hnMod.acts.length)⟩ = hnM1 from actMatN_hnMod_zero] at h
  have hA₂ : ActsBy DS (regUnit (specP 5 133) hC 15) hnM2 := by
    have h := actsBy_g DS ⟨1, (by decide : 1 < hnMod.acts.length)⟩
    rwa [show DS.M ⟨1, (by decide : 1 < hnMod.acts.length)⟩ = hnM2 from actMatN_hnMod_one] at h
  set q₁ := regUnit (specP 5 133) hC 13 with hq₁
  set q₂ := regUnit (specP 5 133) hC 15 with hq₂
  set gq : Fin 9 → NativeSporadic.HN := fun a => q₁ ^ (a.val / 3) * q₂ ^ (a.val % 3) with hgqdef
  have hgq : ∀ a, gq a ∈ P := fun a => P.mul_mem (P.pow_mem hq₁P _) (P.pow_mem hq₂P _)
  have hAq : ∀ a : Fin 9, ActsBy DS (gq a) (hnM1 ^ (a.val / 3) * hnM2 ^ (a.val % 3)) := fun a =>
    actsBy_mul DS (actsBy_pow DS hA₁ _) (actsBy_pow DS hA₂ _)
  have hcs : Nat.card DS.span = 3 ^ 4 := DS.card_span Nat.prime_three
  have hlow : 9 * 3 ^ 4 ≤ Nat.card P := by
    have h := card_ge_of_actsBy DS P hspanP gq
      (fun a : Fin 9 => hnM1 ^ (a.val / 3) * hnM2 ^ (a.val % 3)) hgq hAq hnM_distinct
    rwa [hcs] at h
  have hPc : Nat.card P = 3 ^ 6 := by
    obtain ⟨k, hk⟩ := hPgrp.exists_card_eq
    have hdvd : 3 ^ k ∣ 3 ^ 6 * 374528000000 := by
      rw [← hk, show 3 ^ 6 * 374528000000 = 273030912000000 by norm_num, ← hN]
      exact Subgroup.card_subgroup_dvd_card P
    have hcop : Nat.Coprime (3 ^ k) 374528000000 := Nat.Coprime.pow_left k (by norm_num)
    have hk6 : k ≤ 6 :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hcop.dvd_of_dvd_mul_right hdvd)
    have hk6' : 6 ≤ k := by
      have h1 : 3 ^ 6 ≤ 3 ^ k := by
        rw [← hk]
        calc 3 ^ 6 = 9 * 3 ^ 4 := by norm_num
          _ ≤ _ := hlow
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    rw [hk, show k = 6 by omega]
  have hsyl : Nat.card P = 3 ^ (Nat.card NativeSporadic.HN).factorization 3 := by
    rw [hPc, hN, factorization_eq_of_eq Nat.prime_three
      (show 273030912000000 = 3 ^ 6 * 374528000000 by norm_num) (by norm_num)]
  have hcos := exists_eq_mul_of_actsBy DS P hspanP gq
    (fun a : Fin 9 => hnM1 ^ (a.val / 3) * hnM2 ^ (a.val % 3)) hgq hAq hnM_distinct
    (by rw [hPc, hcs]; norm_num)
  have hfix : ∀ w ∈ P, w ∉ DS.span →
      Nat.card ↥(DS.span ⊓ Subgroup.centralizer ({w} : Set NativeSporadic.HN)) ≤ 3 ^ 2 := by
    intro w hw hwE
    obtain ⟨a, e, he, rfl⟩ := hcos w hw
    have ha : a ≠ 0 := by
      rintro rfl
      apply hwE
      have h1 : gq 0 = 1 := by simp [hgqdef]
      rw [h1, one_mul]
      exact he
    have hle : DS.span ⊓ Subgroup.centralizer ({gq a * e} : Set NativeSporadic.HN) ≤
        DS.span ⊓ Subgroup.centralizer ({gq a} : Set NativeSporadic.HN) := by
      intro x hx
      obtain ⟨hxE, hxC⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_inf.2 ⟨hxE, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
      have hxe : x * e = e * x := DS.mul_comm_of_mem hxE he
      calc x * gq a = (x * (gq a * e)) * e⁻¹ := by group
        _ = (gq a * e * x) * e⁻¹ := by rw [hxC]
        _ = gq a * (e * x) * e⁻¹ := by group
        _ = gq a * (x * e) * e⁻¹ := by rw [← hxe]
        _ = gq a * x := by group
    refine (Subgroup.card_le_of_le hle).trans ?_
    exact card_inf_centralizer_le_sq_of_actsBy DS (hAq a) (0 : Fin 4)
      (if a.val < 3 then (1 : Fin 4) else (2 : Fin 4)) (hnMq_det a ha)
  have hxy := card_inf_centralizer_two_le_of_actsBy DS hA₁ hA₂ (0 : Fin 4) hnM_common_det
  have hEel : IsElemAbelian 3 DS.span := ⟨inferInstance, fun x hx => DS.pow_eq_one_of_mem hx⟩
  intro A hA hAc
  obtain ⟨g, hg⟩ := exists_map_conj_le hsyl (CFSG.Open.IsElemAbelian.isPGroup hA)
  refine ⟨g, le_of_eq ?_⟩
  exact eq_of_isElemAbelian_of_fixed Nat.prime_three hspanP hEel hcs hPc hfix hq₁P hq₂P hxy hg
    (CFSG.SectionRank.isElemAbelian_map hA _) (by rw [card_map_conj]; exact hAc)

theorem regUnit_mem_span_of_eq_word [Fact (Nat.Prime 3)] {C : MCert}
    {hC : mcertCheck (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 C = true}
    {hf : ∀ f ∈ hnMod.facts 3, f ∈ C.facts} {hw : hnMod.wf 3 = true} {r e : ℕ} {l : List ℕ}
    (hord : MFact.ord r e ∈ C.facts) (heq : MFact.eq [(r, 1)] (hnMod.word l) ∈ C.facts) :
    regUnit (specP 5 133) hC r ∈ (NMod.spec (specP 5 133) hC hnMod hf hw).span := by
  have hw' : HasOrd C (hnMod.word l) := hasOrd_word_N hf l
  have hr : HasOrd C [(r, 1)] := fun q hq => by
    rw [List.mem_singleton] at hq
    rw [hq]
    exact ⟨e, hord⟩
  rw [regUnit_eq' (specP 5 133) hC heq hr hw']
  refine CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup (specP 5 133) hC _ _ fun q hq => ?_
  simp only [NMod.word, List.mem_map, List.mem_range] at hq
  obtain ⟨k, hk, rfl⟩ := hq
  exact (NMod.spec (specP 5 133) hC hnMod hf hw).a_mem_span ⟨k, hk⟩

theorem sporPairCase_HN_three_of_data
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges)
    (hdata : ∃ (E : Subgroup NativeSporadic.HN) (S : Set NativeSporadic.HN), IsElemAbelian 3 E ∧
      (∀ A : Subgroup NativeSporadic.HN, IsElemAbelian 3 A → Nat.card E ≤ Nat.card A →
        ∃ g : NativeSporadic.HN, A.map (MulAut.conj g).toMonoidHom ≤ E) ∧
      Subgroup.closure S = ⊤ ∧
      ∀ s ∈ S, ∃ f₁ ∈ E, ∃ f₂ ∈ E, f₁ ≠ 1 ∧ f₂ ∉ Subgroup.zpowers f₁ ∧ Commute s f₁ ∧
        Commute s f₂ ∧ ∃ m, s ^ m = 1 ∧ ¬ 3 ∣ m) :
    Inputs2711c.SporPairCase .HN 3 := by
  intro X _ _ hp _ L B _ hLq hB _ hmax _ _ _ _ _ hname hin _ _ _ _ _ _ _ _ _ _ _ _
  have hname' := hname
  obtain ⟨eS⟩ := hname'
  obtain ⟨σ⟩ := hname
  obtain ⟨β⟩ := hBr .HN
  have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := by
    have h := CFSG.HardMathSupport.Dickson.I271.card_center_dvd_multiplier hSpM hLq .HN eS
    have h1 :
        CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.sporadicMultiplierOrder .HN = 1 := by
      decide
    rw [h1] at h
    exact Nat.dvd_one.1 h
  have hZ : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
  haveI : Finite NativeSporadic.HN :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.HN.card_HN]; norm_num)
  obtain ⟨E, S, hE, hconj, hS, hSl⟩ := hdata
  have hTc : Nat.card E ≤ Nat.card (Inputs2711d.barHom hin).range := by
    refine card_le_card_range_barHom (G := NativeSporadic.HN) hB hin hmax hZ ?_ hE
    exact σ.trans β.symm
  refine eq_gammaTwo_of_conj_planes (G := NativeSporadic.HN) (T := E) (S := S) hp hLq hB hin ?_
    ?_ ?_ ?_ ?_
  · exact σ.trans β.symm
  · exact hconj
  · exact hTc
  · exact hS
  · exact hSl

theorem hn_gen_data :
    ∃ (E : Subgroup NativeSporadic.HN) (S : Set NativeSporadic.HN), IsElemAbelian 3 E ∧
      (∀ A : Subgroup NativeSporadic.HN, IsElemAbelian 3 A → Nat.card E ≤ Nat.card A →
        ∃ g : NativeSporadic.HN, A.map (MulAut.conj g).toMonoidHom ≤ E) ∧
      Subgroup.closure S = ⊤ ∧
      ∀ s ∈ S, ∃ f₁ ∈ E, ∃ f₂ ∈ E, f₁ ≠ 1 ∧ f₂ ∉ Subgroup.zpowers f₁ ∧ Commute s f₁ ∧
        Commute s f₂ ∧ ∃ m, s ^ m = 1 ∧ ¬ 3 ∣ m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : hnGenCheck = true := Certificates.certificate271104
  unfold hnGenCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hgen, hw⟩, hpcwf⟩ := h
  obtain ⟨hC, hclos, hgens⟩ := genCheck_sound (specP 5 133) hgen
  have hex : ∀ f ∈ hnGenExtra, f ∈ hnGenData.mcert.facts := fun f hf =>
    List.mem_append_right _ hf
  have hf : ∀ f ∈ hnMod.facts 3, f ∈ hnGenData.mcert.facts := fun f hf' =>
    hex f (List.mem_append_left _ (List.mem_append_left _ hf'))
  have hpcf : ∀ q ∈ hnTops ++ hnMod.basisPc 3, ∀ f ∈ q.facts 3, f ∈ hnGenData.mcert.facts :=
    fun q hq f hqf =>
      hex f (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨q, hq, hqf⟩)))
  have hhead : ∀ f ∈ ([.eq [(389, 1)] (hnMod.word [0, 0, 0, 1]),
      .eq [(391, 1)] (hnMod.word [1, 1, 1, 2]), .eq [(396, 1)] (hnMod.word [1, 0, 0, 1]),
      .eq [(399, 1)] (hnMod.word [0, 0, 2, 2]), .ne [(389, 1)] [] 0, .ne [(391, 1)] [] 0,
      .ne [(391, 1)] [(389, 1)] 0, .ne [(391, 1)] [(389, 2)] 0, .ne [(396, 1)] [] 0,
      .ne [(399, 1)] [] 0, .ne [(399, 1)] [(396, 1)] 0, .ne [(399, 1)] [(396, 2)] 0] :
      List MFact), f ∈ hnGenData.mcert.facts :=
    fun f hf' => hex f (List.mem_append_right _ hf')
  have hconj := hn_conj_of_facts hC hf hw hpcwf hpcf
  set DS := NMod.spec (specP 5 133) hC hnMod hf hw with hDS
  have hcs : Nat.card DS.span = 3 ^ 4 := DS.card_span Nat.prime_three
  have hEel : IsElemAbelian 3 DS.span := ⟨inferInstance, fun x hx => DS.pow_eq_one_of_mem hx⟩
  have hfixo : ∀ r ∈ [389, 391, 396, 399], MFact.ord r 3 ∈ hnGenData.mcert.facts := by
    intro r hr
    have hfix : hnGenData.fixOrd = [(389, 3), (391, 3), (396, 3), (399, 3)] := rfl
    have hmem : MFact.ord r 3 ∈ hnGenData.fixOrd.map (fun q => MFact.ord q.1 q.2) := by
      rw [hfix]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hmem)))
  have hHO1 : ∀ r ∈ [389, 391, 396, 399], ∀ e : ℕ, HasOrd hnGenData.mcert [(r, e)] := by
    intro r hr e q hq
    rw [List.mem_singleton] at hq
    rw [hq]
    exact ⟨3, hfixo r hr⟩
  have hspan : ∀ r ∈ [389, 391, 396, 399], ∀ l : List ℕ,
      MFact.eq [(r, 1)] (hnMod.word l) ∈ hnGenData.mcert.facts →
      regUnit (specP 5 133) hC r ∈ DS.span := fun r hr l hl =>
    regUnit_mem_span_of_eq_word (hfixo r hr) hl
  have hpair : ∀ r s : ℕ, r ∈ [389, 391, 396, 399] → s ∈ [389, 391, 396, 399] →
      ∀ t₁ t₂ t₃ t₄ : ℕ,
      MFact.ne [(r, 1)] [] t₁ ∈ hnGenData.mcert.facts →
      MFact.ne [(s, 1)] [] t₂ ∈ hnGenData.mcert.facts →
      MFact.ne [(s, 1)] [(r, 1)] t₃ ∈ hnGenData.mcert.facts →
      MFact.ne [(s, 1)] [(r, 2)] t₄ ∈ hnGenData.mcert.facts →
      regUnit (specP 5 133) hC r ≠ 1 ∧
        regUnit (specP 5 133) hC s ∉ Subgroup.zpowers (regUnit (specP 5 133) hC r) := by
    intro r s hr hs t₁ t₂ t₃ t₄ h1 h2 h3 h4
    have hr1 : regUnit (specP 5 133) hC r ≠ 1 :=
      regUnit_ne_one' (specP 5 133) hC h1 (hHO1 r hr 1)
    refine ⟨hr1, fun hmem => ?_⟩
    have hr3 : regUnit (specP 5 133) hC r ^ 3 = 1 := regUnit_pow (specP 5 133) hC (hfixo r hr)
    rcases mem_zpowers_of_pow_three hr3 hr1 hmem with h | h | h
    · exact regUnit_ne_one' (specP 5 133) hC h2 (hHO1 s hs 1) h
    · exact regUnit_ne_pow' (specP 5 133) hC h3 (hHO1 s hs 1) (hHO1 r hr 1)
        (h.trans (pow_one _).symm)
    · exact regUnit_ne_pow' (specP 5 133) hC h4 (hHO1 s hs 1) (hHO1 r hr 2) h
  have hT1 : regUnit (specP 5 133) hC 389 ∈ DS.span :=
    hspan 389 (by simp) [0, 0, 0, 1] (hhead _ (by simp))
  have hT2 : regUnit (specP 5 133) hC 391 ∈ DS.span :=
    hspan 391 (by simp) [1, 1, 1, 2] (hhead _ (by simp))
  have hT3 : regUnit (specP 5 133) hC 396 ∈ DS.span :=
    hspan 396 (by simp) [1, 0, 0, 1] (hhead _ (by simp))
  have hT4 : regUnit (specP 5 133) hC 399 ∈ DS.span :=
    hspan 399 (by simp) [0, 0, 2, 2] (hhead _ (by simp))
  obtain ⟨h1, h2⟩ := hpair 389 391 (by simp) (by simp) 0 0 0 0
    (hhead _ (by simp)) (hhead _ (by simp)) (hhead _ (by simp)) (hhead _ (by simp))
  obtain ⟨h3, h4⟩ := hpair 396 399 (by simp) (by simp) 0 0 0 0
    (hhead _ (by simp)) (hhead _ (by simp)) (hhead _ (by simp)) (hhead _ (by simp))
  refine ⟨DS.span, {v | ∃ g ∈ hnGenData.gens, v = regUnit (specP 5 133) hC g.reg}, hEel,
    fun A hA hAc => hconj A hA (hcs ▸ hAc), hclos, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨hcomm, hpow, hndvd⟩ := hgens g hg
  have hgl : hnGenData.gens = [⟨385, 5, [389, 391]⟩, ⟨386, 5, [389, 391]⟩, ⟨387, 4, [396, 399]⟩,
      ⟨388, 5, [396, 399]⟩] := rfl
  rw [hgl] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨_, hT1, _, hT2, h1, h2, hcomm 389 (by simp), hcomm 391 (by simp), _, hpow, hndvd⟩
  · exact ⟨_, hT1, _, hT2, h1, h2, hcomm 389 (by simp), hcomm 391 (by simp), _, hpow, hndvd⟩
  · exact ⟨_, hT3, _, hT4, h3, h4, hcomm 396 (by simp), hcomm 399 (by simp), _, hpow, hndvd⟩
  · exact ⟨_, hT3, _, hT4, h3, h4, hcomm 396 (by simp), hcomm 399 (by simp), _, hpow, hndvd⟩

theorem sporPairCase_HN_three
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) : Inputs2711c.SporPairCase .HN 3 :=
  sporPairCase_HN_three_of_data hSpM hBr hn_gen_data

end PairHN

section Residual

open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)

theorem sporPairsResidual2_holds
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) : Inputs2711d.SporPairsResidual2 where
  J3_three_B0 := sporPairCase_J3_three_of_ne_bot hBr
  ONan_three := sporPairCase_ONan_three hBr
  HN_three := sporPairCase_HN_three hSpM hBr
  Co1_five := sporPairCase_Co1_five hBr

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e
