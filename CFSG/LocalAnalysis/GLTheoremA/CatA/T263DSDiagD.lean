module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSDiagC
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262List
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Quot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSDiagB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator

theorem t263_diag_abstract {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Type} [Group A] [Finite A]
    {M B J W : Subgroup A} (hMB : M ⊔ B = ⊤) (hBel : IsElemAbelian p B)
    (hBM : B ≤ Subgroup.normalizer (M : Set A)) (hJ : GLAPComponent p M J)
    (hWJ : W ≤ J) (hW2 : IsPGroup 2 W)
    (hWB : B ⊓ Subgroup.normalizer (J : Set A) ≤ Subgroup.normalizer (W : Set A))
    (hWnc : ¬ W ≤ GLAPPrimeCoreOf p J) :
    ∃ D I : Subgroup A, D ≤ B ∧ GLAPComponent p (M ⊓ Subgroup.centralizer (D : Set A)) I ∧
      B ≤ Subgroup.normalizer (I : Set A) ∧ CFSG.Open.IsQuasisimple (PQuot p I) ∧
      Nonempty (PSimple p I ≃* PSimple p J) ∧
      ∃ T : Subgroup A, T ≤ I ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set A) ∧
        ¬ T ≤ GLAPPrimeCoreOf p I := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hMn : M.Normal := by
    refine Subgroup.normalizer_eq_top_iff.1 ?_
    rw [eq_top_iff, ← hMB]
    exact sup_le (Subgroup.le_normalizer) hBM
  set N : Subgroup A := GLAPPrimeCoreOf p M with hNdef
  have hNnorm : N.Normal := by
    refine Subgroup.normalizer_eq_top_iff.1 ?_
    rw [eq_top_iff, ← hMB]
    exact sup_le (le_normalizer_glaPPrimeCoreOf p M)
      (hBM.trans (CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_glaPPrimeCoreOf p M))
  haveI := hNnorm
  let π : A →* A ⧸ N := QuotientGroup.mk' N
  have hker : ¬ p ∣ Nat.card π.ker := by
    rw [QuotientGroup.ker_mk']
    exact not_dvd_card_glaPPrimeCoreOf hp M
  have hcop : ∀ Y₀ : Subgroup A, Nat.Coprime p (Nat.card ↥(Y₀ ⊓ π.ker)) :=
    CFSG.LocalAnalysis.GLTheoremA.S267.coprime_inf_ker hp π hker
  set B₁ : Subgroup A := B ⊓ Subgroup.normalizer (J : Set A) with hB₁
  obtain ⟨F, hFB, -, hB₁F, hsup⟩ :=
    CFSG.SignalizerFunctorTheorem.exists_complement_containing hp hBel (E := B₁) (R := ⊥)
      inf_le_left bot_le (inf_bot_eq B₁)
  have hFel : IsElemAbelian p F := isElemAbelian_mono hBel hFB
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => isElemAbelian_commute hBel hx hy
  set E' : Subgroup (A ⧸ N) := F.map π with hE'
  have hE'el : IsElemAbelian p E' := CFSG.SectionRank.isElemAbelian_map hFel π
  set J' : Subgroup (A ⧸ N) := J.map π with hJ'
  set Yb : Subgroup (A ⧸ N) := M.map π with hYb
  have hJ'p : GLAPComponent p Yb J' := glaPComponent_map hp π (hcop M) hJ
  have hYbcore : GLAPPrimeCoreOf p Yb = ⊥ := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.S267.map_glaPPrimeCoreOf hp π hker M]
    exact QuotientGroup.map_mk'_self N
  have hJ'c : IsComponentOf J' Yb := t263_isComponentOf_of_core_bot hYbcore hJ'p
  have hYbn : Yb.Normal := hMn.map π (QuotientGroup.mk'_surjective N)
  have hYbsn : IsSubnormal Yb ⊤ := isSubnormal_of_normal hYbn
  have hJ'top : IsComponentOf J' ⊤ := ⟨le_top, isSubnormal_trans' hJ'c.2.1 hYbsn, hJ'c.2.2⟩
  have hJ'core : GLAPPrimeCore p ↥J' = ⊥ := by
    have h1 := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hJ'c.2.1
    rw [hYbcore, inf_bot_eq] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ J'.subtype_injective).1 h1.symm
  have hdvdJ' : p ∣ Nat.card (↥J' ⧸ Subgroup.center ↥J') := by
    obtain ⟨e⟩ := t263_pSimple_core_bot_nonempty hJ'core
    have h1 := CFSG.LocalAnalysis.GLTheoremA.S262.prime_dvd_card_pSimple hp hJ'p
    rwa [Nat.card_congr e.toEquiv] at h1
  have hfree : ∀ e ∈ E', e ≠ 1 → GLBConj e J' ≠ J' := by
    rintro _ ⟨f, hfF, rfl⟩ hne hconj
    have hfB : f ∈ B := hFB hfF
    have hf1 : f ≠ 1 := fun h => hne (by rw [h, map_one])
    have hfnot : f ∉ Subgroup.normalizer (J : Set A) := by
      intro hfn
      have h1 : f ∈ B₁ ⊓ F := ⟨⟨hfB, hfn⟩, hfF⟩
      rw [hB₁F, Subgroup.mem_bot] at h1
      exact hf1 h1
    apply hfnot
    have hfM : f ∈ Subgroup.normalizer (M : Set A) := hBM hfB
    have h1 : GLAPComponent p M (GLBConj f J) := by
      have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ f
      rwa [gLBConj_eq_of_mem_normalizer hfM] at this
    have himg : (GLBConj f J).map π = J.map π := by
      rw [CFSG.LocalAnalysis.GLTheoremA.S267.map_gLBConj]
      exact hconj
    have h2 := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_eq_of_map_eq hp π (hcop M) h1 hJ himg
    rw [mem_normalizer_iff_gLBConj_eq]
    exact h2
  obtain ⟨d, hd⟩ := t263_diag_data hE'el hJ'top hfree
  set Δ : Subgroup (A ⧸ N) := d.range with hΔ
  have hΔcore : GLAPPrimeCore p ↥Δ = ⊥ := hd.core_eq_bot hp hJ'top.2.2 hJ'core hdvdJ'
  have hdvdΔ : p ∣ Nat.card (↥Δ ⧸ Subgroup.center ↥Δ) := by
    obtain ⟨e⟩ := hd.centerQuot_nonempty hJ'top.2.2
    rwa [Nat.card_congr e.toEquiv] at hdvdJ'
  have hΔE : ∀ e ∈ E', e ∈ Subgroup.normalizer (Δ : Set (A ⧸ N)) := fun e he => hd.le_normalizer hE'el he
  have hΔB₁ : ∀ b ∈ B₁, π b ∈ Subgroup.normalizer (Δ : Set (A ⧸ N)) := by
    rintro b ⟨hbB, hbJ⟩
    have hbJ' : π b ∈ Subgroup.normalizer (J' : Set (A ⧸ N)) := by
      rw [mem_normalizer_iff_gLBConj_eq, ← CFSG.LocalAnalysis.GLTheoremA.S267.map_gLBConj,
        gLBConj_eq_of_mem_normalizer hbJ]
    have hbE : π b ∈ Subgroup.centralizer (E' : Set (A ⧸ N)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨f, hfF, rfl⟩
      rw [← map_mul, ← map_mul, hBc f (hFB hfF) b hbB]
    exact hd.mem_normalizer (t263_mem_normalizer_diagK_of hbJ' hbE) hbE
  have hBΔ : B.map π ≤ Subgroup.normalizer (Δ : Set (A ⧸ N)) := by
    rw [← hsup, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      exact hΔB₁ b hb
    · rintro _ ⟨f, hf, rfl⟩
      exact hΔE _ ⟨f, hf, rfl⟩
  have hdiagK : diagK E' J' ≤ Yb := by
    refine iSup₂_le fun e he => ?_
    calc GLBConj e J' ≤ GLBConj e Yb := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono e hJ'c.1
      _ = Yb := gLBConj_eq_of_mem_normalizer
          (Subgroup.normalizer_eq_top_iff.2 hYbn ▸ Subgroup.mem_top e)
  have hΔle : Δ ≤ Yb ⊓ Subgroup.centralizer (E' : Set (A ⧸ N)) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨hdiagK (hd.mem x).1, (hd.mem x).2.1⟩
  have hΔsn : IsSubnormal Δ (Yb ⊓ Subgroup.centralizer (E' : Set (A ⧸ N))) :=
    isSubnormal_of_le_of_le hd.sub hΔle inf_le_right
  have hΔcomp : GLAPComponent p (Yb ⊓ Subgroup.centralizer (E' : Set (A ⧸ N))) Δ :=
    CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hp hΔsn hd.quasi hdvdΔ
  have hBp : IsPGroup p ↥B := isPGroup_of_isElemAbelian hBel
  obtain ⟨I, hI, hImap, hBI⟩ := CFSG.LocalAnalysis.GLTheoremA.S267.exists_glaPComponent_lift_invariant hp π hker
    (M := M) (B₁ := B) hBp hBM hBc (D' := E') (Subgroup.map_mono hFB) hΔcomp hBΔ
  refine ⟨B ⊓ E'.comap π, I, inf_le_left, hI, hBI,
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hI, ?_, ?_⟩
  ·
    have h1 : Nonempty (PSimple p I ≃* PSimple p (I.map π)) := t263_pSimple_map_nonempty hp π I (hcop I)
    rw [hImap] at h1
    have h2 : Nonempty (PSimple p J ≃* PSimple p (J.map π)) := t263_pSimple_map_nonempty hp π J (hcop J)
    obtain ⟨e1⟩ := h1
    obtain ⟨e2⟩ := h2
    obtain ⟨e3⟩ := t263_pSimple_core_bot_nonempty hΔcore
    obtain ⟨e4⟩ := t263_pSimple_core_bot_nonempty hJ'core
    obtain ⟨e5⟩ := hd.centerQuot_nonempty hJ'top.2.2
    exact ⟨e1.trans (e3.trans (e5.symm.trans (e4.symm.trans e2.symm)))⟩
  ·
    have hWne : W.map π ≠ ⊥ := by
      intro h
      apply hWnc
      exact (le_inf hWJ ((Subgroup.map_eq_bot_iff W).1 h)).trans
        (CFSG.LocalAnalysis.GLTheoremA.S267.inf_ker_le_glaPPrimeCoreOf hp π hker J)
    set W' : Subgroup (A ⧸ N) := W.map π with hW'
    have hW'J' : W' ≤ J' := Subgroup.map_mono hWJ
    set Wj : Subgroup ↥J' := W'.subgroupOf J' with hWj
    have hWj2 : IsPGroup 2 ↥Wj := (hW2.map π).comap_subtype
    set V : Subgroup (A ⧸ N) := Wj.map d with hV
    have hV2 : IsPGroup 2 ↥V := hWj2.map d
    have hVΔ : V ≤ Δ := Subgroup.map_le_range d Wj
    have hVne : V ≠ ⊥ := by
      intro hV0
      have hWjd : Wj ≤ d.ker := (Subgroup.map_eq_bot_iff Wj).1 hV0
      have hWjc : Wj ≤ Subgroup.center ↥J' := hWjd.trans hd.ker
      have hZp : IsPGroup p ↥(Subgroup.center ↥J') :=
        CFSG.HardMathSupport.Solomon.Coordinator.isPGroup_center_of_pPrimeCore_eq_bot hp hJ'core
      have hWjbot : Wj = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro w hw
        obtain ⟨k, hk⟩ := hWj2 ⟨w, hw⟩
        obtain ⟨a, ha⟩ := hZp ⟨w, hWjc hw⟩
        exact t263_eq_one_of_pow_pow hp hp2 (congrArg Subtype.val ha) (congrArg Subtype.val hk)
      apply hWne
      rw [← Subgroup.map_subgroupOf_eq_of_le hW'J', ← hWj, hWjbot, Subgroup.map_bot]
    have hVB₁ : ∀ b ∈ B₁, π b ∈ Subgroup.normalizer (V : Set (A ⧸ N)) := by
      rintro b ⟨hbB, hbJ⟩
      have hbJ' : π b ∈ Subgroup.normalizer (J' : Set (A ⧸ N)) := by
        rw [mem_normalizer_iff_gLBConj_eq, ← CFSG.LocalAnalysis.GLTheoremA.S267.map_gLBConj,
          gLBConj_eq_of_mem_normalizer hbJ]
      have hbE : π b ∈ Subgroup.centralizer (E' : Set (A ⧸ N)) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨f, hfF, rfl⟩
        rw [← map_mul, ← map_mul, hBc f (hFB hfF) b hbB]
      have hbW : b ∈ Subgroup.normalizer (W : Set A) := hWB ⟨hbB, hbJ⟩
      have hπbW : π b ∈ Subgroup.normalizer (W' : Set (A ⧸ N)) :=
        Subgroup.le_normalizer_map π ⟨b, hbW, rfl⟩
      apply Subgroup.mem_normalizer_fintype
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := hWj2 ⟨y, hy⟩
      have hyk : y ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      have hmem : (π b) * (y : A ⧸ N) * (π b)⁻¹ ∈ J' := (Subgroup.mem_normalizer_iff.1 hbJ' _).1 y.2
      have hmemW : (π b) * (y : A ⧸ N) * (π b)⁻¹ ∈ W' :=
        (Subgroup.mem_normalizer_iff.1 hπbW _).1 (Subgroup.mem_subgroupOf.1 hy)
      have h3 := hd.equivariant hp hp2 hJ'core hbJ' hbE y k hyk
      rw [← h3]
      exact ⟨⟨_, hmem⟩, Subgroup.mem_subgroupOf.2 hmemW, rfl⟩
    have hVB : B.map π ≤ Subgroup.normalizer (V : Set (A ⧸ N)) := by
      rw [← hsup, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨b, hb, rfl⟩
        exact hVB₁ b hb
      · rintro _ ⟨f, hf, rfl⟩
        apply Subgroup.mem_normalizer_fintype
        intro v hv
        have hvC := (hΔle (hVΔ hv)).2
        have h4 : π f * v = v * π f := Subgroup.mem_centralizer_iff.1 hvC (π f) ⟨f, hf, rfl⟩
        have h4' : π f * v * (π f)⁻¹ = v := by rw [mul_inv_eq_iff_eq_mul]; exact h4
        rw [h4']
        exact hv
    set P : Subgroup A := I ⊓ V.comap π with hP
    have hPmap : P.map π = V := by
      apply le_antisymm
      · rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
        exact hx
      · intro v hv
        have hvΔ : v ∈ I.map π := by rw [hImap]; exact hVΔ hv
        obtain ⟨i, hiI, rfl⟩ := hvΔ
        exact ⟨i, ⟨hiI, hv⟩, rfl⟩
    have hBP : B ≤ Subgroup.normalizer (P : Set A) := by
      intro b hb
      have hbV : π b ∈ Subgroup.normalizer (V : Set (A ⧸ N)) := hVB ⟨b, hb, rfl⟩
      refine CFSG.LocalAnalysis.GLTheoremB.mem_normalizer_inf (hBI hb) ?_
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h5 := Subgroup.mem_normalizer_iff.1 hbV (π x)
      simp only [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv]
      exact h5
    have hcopP : Nat.Coprime p (Nat.card ↥P) := by
      have hsurj := π.subgroupMap_surjective P
      have h1 := Subgroup.card_ker_mul_card_range (π.subgroupMap P)
      have hrange : Nat.card ↥(π.subgroupMap P).range = Nat.card ↥(P.map π) := by
        rw [MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.card_top]
      have hcardV : Nat.card ↥(P.map π) = Nat.card ↥V := by rw [hPmap]
      rw [hrange, hcardV] at h1
      rw [← h1]
      refine Nat.Coprime.mul_right
        (CFSG.LocalAnalysis.GLTheoremB.coprime_card_ker_subgroupMap π P (hcop P)) ?_
      obtain ⟨a, ha⟩ := hV2.exists_card_eq
      rw [ha]
      exact Nat.Coprime.pow_right a ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    obtain ⟨Q, hQ⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow p 2 hp
      Nat.prime_two B P hBp hBP hcopP
    set T : Subgroup A := (Q : Subgroup ↥P).map P.subtype with hT
    have hTP : T ≤ P := Subgroup.map_subtype_le _
    refine ⟨T, hTP.trans inf_le_left, (Q.isPGroup').map P.subtype, hQ, ?_⟩
    intro hTO
    have hTmap : T.map π = V := (t263_sylow_map_eq π P (by rw [hPmap]; exact hV2) Q).trans hPmap
    have h1 : T.map π ≤ (GLAPPrimeCoreOf p I).map π := Subgroup.map_mono hTO
    rw [CFSG.LocalAnalysis.GLTheoremA.S267.map_glaPPrimeCoreOf hp π hker I, hImap, hTmap] at h1
    have hΔbot : GLAPPrimeCoreOf p Δ = ⊥ := by
      show (GLAPPrimeCore p ↥Δ).map Δ.subtype = ⊥
      rw [hΔcore, Subgroup.map_bot]
    rw [hΔbot, le_bot_iff] at h1
    exact hVne h1

end CFSG.LocalAnalysis.GLTheoremA.T263

end
