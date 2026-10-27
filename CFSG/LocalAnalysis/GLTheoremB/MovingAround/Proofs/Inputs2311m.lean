module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311k2
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4OddMinus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Three4
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Statements
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Closing
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Top
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4MaxBase
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLiePGL
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SPGL
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCrossLin
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofHighWit

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311m

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c CFSG.RankThree.PartOne.CTP

section Normalizer

variable {G : Type*} [Group G]

theorem mulAut_congr_conj_eq_conj_conj_inputs2311m (c : G) :
    (MulAut.congr (MulAut.conj c)).toMonoidHom = (MulAut.conj (MulAut.conj c)).toMonoidHom := by
  ext φ y
  rfl

theorem mem_normalizer_uniPlaneClosure_of_map_eq (r : ℕ) {E : Subgroup (MulAut G)} {c : G}
    (hc : E.map (MulAut.conj (MulAut.conj c)).toMonoidHom = E) :
    c ∈ Subgroup.normalizer (uniPlaneClosure r E : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h := uniPlaneClosure_map_congr (MulAut.conj c) r E
  rw [mulAut_congr_conj_eq_conj_conj_inputs2311m, hc] at h
  exact h.symm

theorem closure_pair_inv_mul_inputs2311m {M : Type*} [Group M] (a b : M) :
    Subgroup.closure {b⁻¹ * a, b} = Subgroup.closure {a, b} := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · have e : y = b * (b⁻¹ * y) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)

theorem map_closure_pair_eq_inputs2311m {M : Type*} [Group M] (φ : M →* M) {a b : M}
    (ha : φ a = a ∨ φ a = b⁻¹ * a) (hb : φ b = b) :
    (Subgroup.closure {a, b}).map φ = Subgroup.closure {a, b} := by
  rw [MonoidHom.map_closure, Set.image_pair, hb]
  rcases ha with ha | ha
  · rw [ha]
  · rw [ha, closure_pair_inv_mul_inputs2311m]

theorem conj_mul_conj_inv_eq_inputs2311m (α : MulAut G) (c : G) :
    MulAut.conj c * α * (MulAut.conj c)⁻¹ = MulAut.conj (c * (α c)⁻¹) * α := by
  ext y
  have h1 : (MulAut.conj c)⁻¹ y = c⁻¹ * y * c := by
    rw [← map_inv, MulAut.conj_apply, inv_inv]
  simp only [MulAut.mul_apply, h1, MulAut.conj_apply]
  simp only [map_mul, map_inv]
  group

end Normalizer

section Coprime

theorem le_uniPlaneClosure_of_invariant_pGroup {G : Type*} [Group G] [Finite G] {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hpr : p ≠ r) {E : Subgroup (MulAut G)} [hEa : CFSG.IsElementaryAbelian p ↥E]
    (hcard : p ^ 2 ≤ Nat.card ↥E) {R : Subgroup G} (hR : IsPGroup r ↥R)
    (hinv : ∀ e ∈ E, R.map (e : MulAut G).toMonoidHom = R) :
    R ≤ uniPlaneClosure r E := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with
      mul_comm := fun a b => hEa.toIsMulCommutative.is_comm.comm a b }
  haveI : Finite (MulAut G) := inferInstance
  set α : ↥E →* MulAut G := E.subtype with hα
  have hαR : CFSG.SolvableSignalizer.IsInvariant α R := fun a => hinv (a : MulAut G) a.2
  set β := CFSG.SolvableSignalizer.restrictAction α R hαR with hβ
  have hcop : ¬ p ∣ Nat.card ↥R := by
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    rw [hk]
    intro h
    exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow h))
  have htop := CFSG.SolvableSignalizer.iSup_fixedSubgroup_eq_top p hp β hcard hcop
  have hle : (⨆ (a : ↥E) (_ : a ≠ 1), CFSG.SolvableSignalizer.fixedSubgroup β a) ≤
      (uniPlaneClosure r E).comap R.subtype := by
    refine iSup₂_le fun a ha z hz => ?_
    rw [CFSG.SolvableSignalizer.mem_fixedSubgroup] at hz
    have hz' : (a : MulAut G) (z : G) = z := by
      have := congrArg Subtype.val hz
      simpa [hβ, hα] using this
    obtain ⟨n, hn⟩ := hR z
    refine mem_uniPlaneClosure a.2 (fun h => ha (Subtype.ext h)) hz' (n := n) ?_
    have := congrArg Subtype.val hn
    simpa using this
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥R) ∈ (⨆ (a : ↥E) (_ : a ≠ 1), CFSG.SolvableSignalizer.fixedSubgroup β a) := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hle hy'

theorem subgroupOf_sup_subgroupOf_eq_top_inputs2311m {M : Type*} [Group M] (A B : Subgroup M) :
    A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
  apply Subgroup.map_injective (A ⊔ B).subtype_injective
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 le_sup_left, inf_eq_left.2 le_sup_right, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

end Coprime

section PGL

open CFSG.RankThree.PartTwo CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

variable {G : Type} [Group G]

theorem exists_rGen_escape_of_isPGLPiThree {α : MulAut G} {q r : ℕ} (hq5 : 5 ≤ q)
    (hC : IsPGLPiThree ↥(fixedSubgroup α) q) (hr : r.Prime) (hr3 : r ≠ 3) (hrq : r ∣ q)
    {x : G} (hx : α x = x) (hx3 : x ^ 3 = 1) :
    (∃ w : G, α w = w ∧ w * x = x * w ∧ ∀ y : G, α y = y →
      y ∈ Subgroup.closure ({y : G | α y = y ∧ ∃ n : ℕ, y ^ (r ^ n) = 1} ∪ {w})) ∧
    (∃ y₀ : G, α y₀ = y₀ ∧ y₀ ≠ 1 ∧ ∃ n : ℕ, y₀ ^ (r ^ n) = 1) ∧
    ¬ IsSimpleGroup ↥(fixedSubgroup α) := by
  classical
  obtain ⟨π, p, f, K, _, hK, rfl, hmod, ⟨e⟩⟩ := hC
  have := hK.finite
  haveI : Fact r.Prime := ⟨hr⟩
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  set P := CFSG.PGLModel.projImage (Sec4.glPi π 3 (p ^ f) K) with hP
  set S := CFSG.PGLModel.projImage (Sec4.slPi π 3 (p ^ f) K) with hS
  have hSP : S ≤ P := Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  set M : Subgroup ↥P := S.subgroupOf P with hM
  have hq2 : 2 < p ^ f := by omega
  have hcardP : Nat.card ↥P = 3 * Nat.card ↥S := Sec13.Ronan138S.card_projImage_glPi_eq hK hmod
  have hcardM : Nat.card ↥M = Nat.card ↥S := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv
  have hS0 : 0 < Nat.card ↥S := Nat.card_pos
  have hMtop : M ≠ ⊤ := by
    intro h
    have h1 : Nat.card ↥M = Nat.card ↥P := by rw [h]; exact Subgroup.card_top
    omega
  have hrS : r ∣ Nat.card ↥S := by
    have h1 := Sec13.card_projImage_slPi_mul_three hK hmod
    have h2 : r ∣ (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1) :=
      Dvd.dvd.mul_right (Dvd.dvd.mul_right (hrq.trans (dvd_pow_self _ (by norm_num))) _) _
    rw [← h1] at h2
    rcases (Nat.Prime.dvd_mul hr).1 h2 with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h) hr3
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' r hrS
  have hy₀1 : y₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy₀
    exact hr.one_lt.ne hy₀
  have hcube : ∀ z ∈ P, z ^ 3 ∈ S := fun z hz => Sec4.RonanK429Lie.pow_three_mem_projImage_slPi hK hz
  have hrM : ∀ z : ↥P, (∃ n : ℕ, z ^ (r ^ n) = 1) → z ∈ M := by
    rintro z ⟨n, hn⟩
    have hcop : Nat.Coprime 3 (orderOf z) := by
      refine Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hn) (Nat.Coprime.pow_right n ?_)
      rw [Nat.coprime_primes Nat.prime_three hr]
      exact Ne.symm hr3
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [hM, Subgroup.mem_subgroupOf, ← hm, Subgroup.coe_pow, Subgroup.coe_pow]
    exact Subgroup.pow_mem _ (hcube _ z.2) m
  haveI hSs : IsSimpleGroup ↥S := Sec4.RonanK429Lie.isSimpleGroup_projImage_slPi hK (Or.inr hq2)
  haveI hMs : IsSimpleGroup ↥M := MulEquiv.isSimpleGroup (Subgroup.subgroupOfEquivOfLe hSP)
  set Rset : Set ↥P := {z | ∃ n : ℕ, z ^ (r ^ n) = 1} with hRset
  set Rgp : Subgroup ↥P := Subgroup.closure Rset with hRgp
  have hRn : Rgp.Normal := by
    refine ⟨fun z hz g => ?_⟩
    have hle : Rgp.map (MulAut.conj g).toMonoidHom ≤ Rgp := by
      rw [hRgp, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, ⟨n, hn⟩, rfl⟩
      refine Subgroup.subset_closure ⟨n, ?_⟩
      show (MulAut.conj g).toMonoidHom y ^ (r ^ n) = 1
      rw [← map_pow, hn, map_one]
    exact hle ⟨z, hz, rfl⟩
  have hy₀P : (⟨(y₀ : Matrix.ProjGenLinGroup (Fin 3) K), hSP y₀.2⟩ : ↥P) ∈ Rset := by
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    show (y₀ : Matrix.ProjGenLinGroup (Fin 3) K) ^ r = 1
    rw [← Subgroup.coe_pow, ← hy₀, pow_orderOf_eq_one, Subgroup.coe_one]
  have hMR : M ≤ Rgp := by
    have hRM : Rgp ≤ M := by
      rw [hRgp, Subgroup.closure_le]
      intro z hz
      exact hrM z hz
    have hN : (Rgp.subgroupOf M).Normal := inferInstance
    rcases hN.eq_bot_or_eq_top with h | h
    · exfalso
      have hmem : (⟨⟨(y₀ : Matrix.ProjGenLinGroup (Fin 3) K), hSP y₀.2⟩, hrM _ hy₀P⟩ : ↥M) ∈
          Rgp.subgroupOf M := Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure hy₀P)
      rw [h, Subgroup.mem_bot] at hmem
      apply hy₀1
      apply Subtype.ext
      have := congrArg (fun u : ↥M => ((u : ↥P) : Matrix.ProjGenLinGroup (Fin 3) K)) hmem
      simpa using this
    · intro z hz
      have : (⟨z, hz⟩ : ↥M) ∈ Rgp.subgroupOf M := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
  set xP : ↥P := e ⟨x, mem_fixedSubgroup.2 hx⟩ with hxP
  have hxP3 : xP ^ 3 = 1 := by
    rw [hxP, ← map_pow]
    have : (⟨x, mem_fixedSubgroup.2 hx⟩ : ↥(fixedSubgroup α)) ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  obtain ⟨wP, hwM, hwx⟩ : ∃ wP : ↥P, wP ∉ M ∧ wP * xP = xP * wP := by
    by_cases hxM : xP ∈ M
    · by_cases hx1 : xP = 1
      · obtain ⟨wP, hwP⟩ : ∃ wP : ↥P, wP ∉ M := by
          by_contra hcon
          push Not at hcon
          exact hMtop (eq_top_iff.2 fun z _ => hcon z)
        exact ⟨wP, hwP, by rw [hx1, mul_one, one_mul]⟩
      · have hxS : (xP : Matrix.ProjGenLinGroup (Fin 3) K) ∈ S := Subgroup.mem_subgroupOf.1 hxM
        have hxS3 : (xP : Matrix.ProjGenLinGroup (Fin 3) K) ^ 3 = 1 := by
          rw [← Subgroup.coe_pow, hxP3, Subgroup.coe_one]
        have hxS1 : (xP : Matrix.ProjGenLinGroup (Fin 3) K) ≠ 1 := fun h => hx1 (Subtype.ext h)
        obtain ⟨w, hwP, hwS, hwc⟩ := escape_projImage_slPi hK hmod hxS hxS3 hxS1
        exact ⟨⟨w, hwP⟩, fun h => hwS (Subgroup.mem_subgroupOf.1 h), Subtype.ext hwc⟩
    · exact ⟨xP, hxM, rfl⟩
  set G₀ : Subgroup ↥P := Subgroup.closure ((M : Set ↥P) ∪ {wP}) with hG₀
  have hMG₀ : M ≤ G₀ := fun z hz => Subgroup.subset_closure (Or.inl hz)
  have hwG₀ : wP ∈ G₀ := Subgroup.subset_closure (Or.inr rfl)
  have hG₀top : G₀ = ⊤ := by
    have hlt : M < G₀ := lt_of_le_of_ne hMG₀ fun h => hwM (h ▸ hwG₀)
    have h1 : Nat.card ↥M ∣ Nat.card ↥G₀ := Subgroup.card_dvd_of_le hMG₀
    have h2 : Nat.card ↥G₀ ∣ Nat.card ↥P := Subgroup.card_subgroup_dvd_card G₀
    have h3 : Nat.card ↥M < Nat.card ↥G₀ := Subgroup.card_lt_of_lt hlt
    obtain ⟨k, hk⟩ := h1
    rw [hk, hcardP, ← hcardM] at h2
    rw [hk] at h3
    have hM0 : 0 < Nat.card ↥M := Nat.card_pos
    have hk3 : k ∣ 3 := by
      rw [mul_comm 3] at h2
      exact Nat.dvd_of_mul_dvd_mul_left hM0 h2
    have hk1 : 1 < k := by
      by_contra hk1
      push Not at hk1
      interval_cases k
      · omega
      · omega
    have hk3' : k = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hk3 with h | h
      · omega
      · exact h
    apply Subgroup.eq_top_of_card_eq
    rw [hk, hk3', hcardP, ← hcardM, mul_comm]
  set ψ : ↥P →* G := (fixedSubgroup α).subtype.comp e.symm.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := (fixedSubgroup α).subtype_injective.comp e.symm.injective
  have hψfix : ∀ z : ↥P, α (ψ z) = ψ z := fun z => (e.symm z).2
  have hψx : ψ xP = x := by
    simp [hψ, hxP]
  refine ⟨⟨ψ wP, hψfix wP, ?_, fun y hy => ?_⟩, ⟨ψ ⟨(y₀ : Matrix.ProjGenLinGroup (Fin 3) K), hSP y₀.2⟩,
    hψfix _, ?_, ?_⟩, ?_⟩
  · rw [← hψx, ← map_mul, ← map_mul, hwx]
  ·
    have hyP : e ⟨y, mem_fixedSubgroup.2 hy⟩ ∈ Subgroup.closure (Rset ∪ {wP}) := by
      have h1 : G₀ ≤ Subgroup.closure (Rset ∪ {wP}) := by
        rw [hG₀, Subgroup.closure_le]
        rintro z (hz | hz)
        · exact Subgroup.closure_mono Set.subset_union_left (hMR hz)
        · exact Subgroup.subset_closure (Or.inr hz)
      exact h1 (hG₀top ▸ Subgroup.mem_top _)
    have h2 := Subgroup.mem_map_of_mem ψ hyP
    rw [MonoidHom.map_closure] at h2
    have hψy : ψ (e ⟨y, mem_fixedSubgroup.2 hy⟩) = y := by simp [hψ]
    rw [hψy] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨z, hz | hz, rfl⟩
    · obtain ⟨n, hn⟩ := hz
      exact Or.inl ⟨hψfix z, n, by rw [← map_pow, hn, map_one]⟩
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Or.inr rfl
  · intro h
    apply hy₀1
    apply Subtype.ext
    have h1 : (⟨(y₀ : Matrix.ProjGenLinGroup (Fin 3) K), hSP y₀.2⟩ : ↥P) = 1 :=
      hψinj (h.trans (map_one ψ).symm)
    have := congrArg Subtype.val h1
    simpa using this
  · obtain ⟨n, hn⟩ := hy₀P
    exact ⟨n, by rw [← map_pow, hn, map_one]⟩
  ·
    intro hsimp
    haveI : IsSimpleGroup ↥P := MulEquiv.isSimpleGroup e.symm
    have hMn : M.Normal := by
      rw [hM, ← Sec13.commutator_projImage_glPi hK hq2]
      infer_instance
    rcases hMn.eq_bot_or_eq_top with h | h
    · have hmem := hrM _ hy₀P
      rw [h, Subgroup.mem_bot] at hmem
      apply hy₀1
      apply Subtype.ext
      have := congrArg Subtype.val hmem
      simpa using this
    · exact hMtop h

end PGL


section D4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem frameD_mul_inv_gammaP_frameD {B : SL2 K} (hB3 : B ^ 3 = 1) :
    frameD K B * (gammaP K B (frameD K B))⁻¹ = (frameDiag B)⁻¹ := by
  have hα : gammaP K B (frameD K B) = frameK₁ K B * (frameK₂ K B)⁻¹ := by
    rw [frameD, map_mul, map_inv, gammaP_frameK₂, gammaP_frameK₃]
  have hc32 : Commute (frameK₃ K B) (frameK₂ K B) := (frameK_commute B B).2.2
  have hk2 : frameK₂ K B ^ 3 = 1 := by rw [← map_pow, hB3, map_one]
  have hk2' : frameK₂ K B * frameK₂ K B = (frameK₂ K B)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [mul_assoc, ← pow_three, hk2]
  rw [hα, frameD, frameDiag]
  calc frameK₂ K B * (frameK₃ K B)⁻¹ * (frameK₁ K B * (frameK₂ K B)⁻¹)⁻¹
      = frameK₂ K B * ((frameK₃ K B)⁻¹ * frameK₂ K B) * (frameK₁ K B)⁻¹ := by group
    _ = frameK₂ K B * (frameK₂ K B * (frameK₃ K B)⁻¹) * (frameK₁ K B)⁻¹ := by
        rw [hc32.inv_left.eq]
    _ = (frameK₂ K B * frameK₂ K B) * (frameK₃ K B)⁻¹ * (frameK₁ K B)⁻¹ := by group
    _ = (frameK₂ K B)⁻¹ * (frameK₃ K B)⁻¹ * (frameK₁ K B)⁻¹ := by rw [hk2']
    _ = (frameK₁ K B * frameK₃ K B * frameK₂ K B)⁻¹ := by group

theorem commute_frameD_frameDiag (B : SL2 K) : Commute (frameD K B) (frameDiag B) := by
  obtain ⟨c13, c12, c32⟩ := frameK_commute (K := K) B B
  have h2 : Commute (frameK₂ K B) (frameK₁ K B * frameK₃ K B * frameK₂ K B) :=
    (c12.symm.mul_right c32.symm).mul_right (Commute.refl _)
  have h3 : Commute (frameK₃ K B) (frameK₁ K B * frameK₃ K B * frameK₂ K B) :=
    (c13.symm.mul_right (Commute.refl _)).mul_right c32
  rw [frameD, frameDiag]
  exact h2.mul_left h3.inv_left

theorem uniPlaneClosure_eq_top_frameDiag [Finite K] (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3)
    (hK5 : 5 ≤ Nat.card K) {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))}
    (hαE : gammaP K (orderThreeSL K) ∈ E)
    (hΔE : MulAut.conj (frameDiag (orderThreeSL K)) ∈ E) :
    uniPlaneClosure (ringChar K) E = ⊤ := by
  classical
  have hB3 : orderThreeSL K ^ 3 = 1 := orderThreeSL_pow_three K
  have hrp : (ringChar K).Prime := by
    have := Fintype.ofFinite K
    obtain ⟨n, hp, -⟩ := FiniteField.card K (ringChar K)
    exact hp
  have hrK : ringChar K ∣ Nat.card K := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.pos.ne'
  set E' : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)) :=
    Subgroup.closure {gammaP K (orderThreeSL K), MulAut.conj (frameDiag (orderThreeSL K))} with hE'
  have hE'E : E' ≤ E := by
    rw [hE', Subgroup.closure_le]
    rintro φ (rfl | rfl)
    · exact hαE
    · exact hΔE
  have hmono : uniPlaneClosure (ringChar K) E' ≤ uniPlaneClosure (ringChar K) E :=
    Subgroup.closure_mono fun s ⟨φ, hφ, hφ1, hφs, n, hn⟩ => ⟨φ, hE'E hφ, hφ1, hφs, n, hn⟩
  suffices h : uniPlaneClosure (ringChar K) E' = ⊤ by
    rw [eq_top_iff, ← h]
    exact hmono
  set H := uniPlaneClosure (ringChar K) E' with hH
  have hαΔ : gammaP K (orderThreeSL K) (frameDiag (orderThreeSL K)) = frameDiag (orderThreeSL K) :=
    gammaP_frameDiag _ _
  have hΔ3 : frameDiag (orderThreeSL K) ^ 3 = 1 := by
    rw [← frameDiagHom_apply, ← map_pow, hB3, map_one]
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd.d4GraphA2FixIsoOdd_holds K hK2
    hK3 hK5 (orderThreeSL K) hB3 (orderThreeSL_ne_one K)
  obtain ⟨⟨w, hαw, hwΔ, hgen⟩, ⟨y₀, hαy₀, hy₀1, hy₀r⟩, hns⟩ :=
    exists_rGen_escape_of_isPGLPiThree hK5 hfix hrp hK3 hrK hαΔ hΔ3
  haveI hGs : IsSimpleGroup ↥(adjointGroup Tag.D4 K) :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.isSimpleGroup_adjointGroup_D4 K
  have hα1 : gammaP K (orderThreeSL K) ≠ 1 := by
    intro h
    apply hns
    have htop : fixedSubgroup (gammaP K (orderThreeSL K)) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [mem_fixedSubgroup, h]
      rfl
    rw [htop]
    exact MulEquiv.isSimpleGroup Subgroup.topEquiv
  have hαE' : gammaP K (orderThreeSL K) ∈ E' := Subgroup.subset_closure (by simp)
  have hrH : ∀ y, gammaP K (orderThreeSL K) y = y → (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) → y ∈ H := by
    rintro y hy ⟨n, hn⟩
    exact mem_uniPlaneClosure hαE' hα1 hy hn
  have hNw : w ∈ Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K)) := by
    refine mem_normalizer_uniPlaneClosure_of_map_eq _ ?_
    refine map_closure_pair_eq_inputs2311m _ (Or.inl ?_) ?_
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_mul_conj_inv_eq_inputs2311m, hαw, mul_inv_cancel, map_one, one_mul]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← map_inv, ← map_mul, ← map_mul, hwΔ, mul_inv_cancel_right]
  have hNd : frameD K (orderThreeSL K) ∈ Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K)) := by
    refine mem_normalizer_uniPlaneClosure_of_map_eq _ ?_
    refine map_closure_pair_eq_inputs2311m _ (Or.inr ?_) ?_
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_mul_conj_inv_eq_inputs2311m, frameD_mul_inv_gammaP_frameD hB3, map_inv]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← map_inv, ← map_mul, ← map_mul, (commute_frameD_frameDiag (orderThreeSL K)).eq,
        mul_inv_cancel_right]
  have hNC : fixedSubgroup (gammaP K (orderThreeSL K)) ≤
      Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K)) := by
    intro y hy
    refine (Subgroup.closure_le _).2 ?_ (hgen y hy)
    rintro z (⟨hz, hzn⟩ | hz)
    · exact Subgroup.le_normalizer (hrH z hz hzn)
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hNw
  have hNtop : Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K)) = ⊤ := by
    rw [eq_top_iff, ← closure_fixedSubgroup_frameD
      (A2NonsplitGen.d4GraphA2FrameGen_of A2NonsplitGen.frameTopRootsMem_holds
          A2NonsplitGen.frameClosing_holds) hK3
      (by omega), Subgroup.closure_le]
    rintro g (hg | hg)
    · exact hNC hg
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact hNd
  have hHn : H.Normal := Subgroup.normalizer_eq_top_iff.1 hNtop
  rcases hHn.eq_bot_or_eq_top with h | h
  · exfalso
    have hy := hrH y₀ hαy₀ hy₀r
    rw [h, Subgroup.mem_bot] at hy
    exact hy₀1 hy
  · exact h

end D4

section Cat

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

@[expose] def D4GraphA2FramePlane
    (d : TauCeti.ValidLieTypeIndex) (p : ℕ) (E : Subgroup (MulAut (Cat d))) : Prop :=
  p = 3 ∧ d.1.characteristic ≠ 2 ∧ ∃ q : TauCeti.PrimePower, d.1 = .D 4 q ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.card ∧
      ∃ e : Cat d ≃* ↥(adjointGroup Tag.D4 K),
        gammaP K (orderThreeSL K) ∈ E.map (MulAut.congr e).toMonoidHom ∧
        MulAut.conj (frameDiag (orderThreeSL K)) ∈ E.map (MulAut.congr e).toMonoidHom

@[expose] def TrialityBorelPairPlane
    (d : TauCeti.ValidLieTypeIndex) (_p : ℕ) (E : Subgroup (MulAut (Cat d))) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (q.p ^ q.exponent) ^ 3 ∧
      ∃ e : Cat d ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom,
          ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
              (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
            (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
              (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
          ((graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
              (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
            (graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
              (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

@[expose] def D4PlanesRest2 :
    Prop :=
  UniSeitzPlanes fun d p E => Inputs2311g.OddCpfRest4 d p E ∧ ¬ InnerPlane d p E ∧
    ¬ Inputs2311k.D4GraphG2Plane d p E ∧ ¬ D4GraphA2FramePlane d p E ∧ ¬ TrialityBorelPairPlane d p E

set_option linter.unusedSectionVars false


theorem uniSeitzPlanes_dFour_graphA2Frame :
    UniSeitzPlanes fun d p E => D4GraphA2FramePlane d p E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨rfl, hchar2, q, rfl, K, _, _, hK, e, hαE, hΔE⟩
  have hchar : (TauCeti.LieTypeIndex.D 4 q).characteristic = q.p := by
    simp [TauCeti.LieTypeIndex.characteristic_D]
  have hK' : Nat.card K = q.p ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def]
  haveI : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      q.exponent_pos hK'
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hq2 : q.p ≠ 2 := fun h => hchar2 (by rw [hchar, h])
  have hq3 : q.p ≠ 3 := fun h => hpd (by rw [hchar, h])
  have h5 : 5 ≤ Nat.card K := by
    have h5 : 5 ≤ q.p := by
      have := q.prime_p.two_le
      have h4' : q.p ≠ 4 := fun h => by
        have := q.prime_p
        rw [h] at this
        norm_num at this
      omega
    rw [hK']
    calc 5 ≤ q.p := h5
      _ = q.p ^ 1 := (pow_one _).symm
      _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos q.exponent_pos
  have htop := uniPlaneClosure_eq_top_frameDiag (by rw [hring]; exact hq2) (by rw [hring]; exact hq3) h5
    hαE hΔE
  rw [hring] at htop
  rw [hchar, ← uniPlaneGen_map_congr e]
  exact htop

theorem uniSeitzPlanes_triality_borelPair :
    UniSeitzPlanes fun d p E => TrialityBorelPairPlane d p E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨q, rfl, K, _, _, σ, hK, e, hB⟩
  have hchar : (TauCeti.LieTypeIndex.trialityD4 q).characteristic = q.p := by
    simp [TauCeti.LieTypeIndex.characteristic_trialityD4]
  have hK3 : Nat.card K = q.p ^ (q.exponent * 3) := by rw [hK, pow_mul]
  haveI : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      (by have := q.exponent_pos; omega) hK3
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpq : p ≠ q.p := fun h => hpd (h.trans hchar.symm)
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hE'el : IsElemAbelian p (E.map (MulAut.congr e).toMonoidHom) := isElemAbelian_map_congr e hE
  have hE'c : Nat.card ↥(E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hc]
  haveI : CFSG.IsElementaryAbelian p ↥(E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr hE'el
  have hposp : IsPGroup q.p ↥((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    isPGroup_graphFixedPosUnipotent_subgroupOf q.p
  have hnegp : IsPGroup q.p ↥((graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    have h1 := Inputs2311g.isPGroup_negUnipotent_excD4 (K := K) q.p TwistTag.D4.tag
    exact (h1.to_le (inf_le_left : graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom ≤ _)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (graphFixedNegUnipotent_le_graphFixedRootGroup TwistTag.D4 K
        σ.toRingHom)).symm
  have hpos := le_uniPlaneClosure_of_invariant_pGroup hp q.prime_p hpq hE'c.ge hposp
    (fun φ hφ => (hB φ hφ).1)
  have hneg := le_uniPlaneClosure_of_invariant_pGroup hp q.prime_p hpq hE'c.ge hnegp
    (fun φ hφ => (hB φ hφ).2)
  have hsup : (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊔
      (graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊤ :=
    subgroupOf_sup_subgroupOf_eq_top_inputs2311m _ _
  have htop : uniPlaneClosure q.p (E.map (MulAut.congr e).toMonoidHom) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le hpos hneg
  rw [hchar, ← uniPlaneGen_map_congr e]
  exact htop

theorem d4PlanesRest_of_rest2 (h : D4PlanesRest2) : Inputs2311k.D4PlanesRest := by
  intro d p hp hp2 hpd hex E hE hc ⟨hR, hin, hg⟩
  by_cases hf : D4GraphA2FramePlane d p E
  · exact uniSeitzPlanes_dFour_graphA2Frame d p hp hp2 hpd hex E hE hc hf
  · by_cases hb : TrialityBorelPairPlane d p E
    · exact uniSeitzPlanes_triality_borelPair d p hp hp2 hpd hex E hE hc hb
    · exact h d p hp hp2 hpd hex E hE hc ⟨hR, hin, hg, hf, hb⟩

end Cat

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311m
