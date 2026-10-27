module

import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneHallHigman
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneCentralizer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneInner
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneComponents
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneCenter
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.GroupTheory.CentralExtensionPGroup
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.RankThree.SubgroupLists.SchurCommutant

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open Matrix Subgroup
open scoped MatrixGroups

private abbrev Mat4 (p : ℕ) := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod p)

private theorem pow_prime_eq_one_of_mem {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} {x : ↥G} {k : ℕ}
    (hx : x ^ p ^ k = 1) : x ^ p = 1 := by
  have hσ : Fintype.card (Fin 2 ⊕ Fin 2) < p := by
    have h4 : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by
      rw [Fintype.card_sum]
      norm_num
    omega
  exact pow_prime_eq_one_of_card_lt hσ hx

private theorem commute_sylow_two_of_odd_card {M : Type*} [Group M] [Finite M]
    (hM : Odd (Nat.card M)) (S : Sylow 2 M) :
    ∀ a ∈ (S : Subgroup M), ∀ b ∈ (S : Subgroup M), a * b = b * a := by
  have hone : ∀ x ∈ (S : Subgroup M), x = 1 := by
    intro x hx
    let xS : ↥(S : Subgroup M) := ⟨x, hx⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)
      (G := ↥(S : Subgroup M))).mp S.isPGroup' xS
    have hkx : orderOf x = 2 ^ k := by
      rw [← Subgroup.orderOf_coe xS] at hk
      simpa [xS] using hk
    have hdvdS : orderOf x ∣ Nat.card ↥(S : Subgroup M) :=
      Subgroup.orderOf_dvd_natCard (S : Subgroup M) hx
    have hdvdM : Nat.card ↥(S : Subgroup M) ∣ Nat.card M :=
      Subgroup.card_subgroup_dvd_card (S : Subgroup M)
    rw [hkx] at hdvdS
    have hk0 : k = 0 := by
      by_contra hkne
      exact hM.not_two_dvd_nat (dvd_trans (dvd_pow_self 2 hkne)
        (dvd_trans hdvdS hdvdM))
    exact orderOf_eq_one_iff.mp (by rw [hkx, hk0, pow_zero])
  intro a ha b hb
  simp [hone a ha, hone b hb]

private theorem fittingSubgroup_le_center {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} (hG : oPPrimeHull p G = G)
    (hO : CFSG.pCore p ↥G = ⊥) (hO2 : CFSG.pCore 2 ↥G ≤ Subgroup.center ↥G) :
    CFSG.fittingSubgroup ↥G ≤ Subgroup.center ↥G := by
  classical
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun q => ?_
  have hqprime : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
  haveI : Fact (q : ℕ).Prime := ⟨hqprime⟩
  by_cases hq2 : (q : ℕ) = 2
  · rw [hq2]
    exact hO2
  by_cases hqp : (q : ℕ) = p
  · rw [hqp, hO]
    exact bot_le
  · have hqodd : Odd (q : ℕ) := hqprime.odd_of_ne_two hq2
    let M : Subgroup ↥G := CFSG.pCore (q : ℕ) ↥G
    have hMn : M.Normal := CFSG.pCore_normal
    haveI : M.Normal := hMn
    have hMp : IsPGroup (q : ℕ) ↥M := CFSG.pCore_isPGroup
    have hMsolv : Group.IsSolvable ↥M :=
      @IsNilpotent.to_isSolvable _ _ hMp.isNilpotent
    have hcardM : Odd (Nat.card ↥M) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := (q : ℕ)) (G := ↥M)).mp hMp
      rw [hn]
      exact hqodd.pow
    have hM2 : p = 5 → ∀ S : Sylow 2 ↥M, ∀ a ∈ (S : Subgroup ↥M),
        ∀ b ∈ (S : Subgroup ↥M), a * b = b * a :=
      fun _ S => commute_sylow_two_of_odd_card hcardM S
    exact le_center_of_solvable_normal (p := p) hp5 (σ := Fin 2 ⊕ Fin 2)
      (by simp [Fintype.card_sum]) hG hO M hMsolv hM2

private theorem exists_ne_commute_of_isIrreducibleOn {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} (hG : oPPrimeHull p G = G)
    (hirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G) :
    ∃ a b : ↥G, a * b ≠ b * a := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative ↥G := ⟨⟨hcon⟩⟩
  have hO : CFSG.pCore p ↥G = ⊥ := pCore_eq_bot_of_isIrreducibleOn hirr
  have hPtop : IsPGroup p (⊤ : Subgroup ↥G) := by
    have h := CFSG.GroupTheory.isPGroup_closure_of_isNilpotent (p := p) (Y := ↥G)
      (S := {x : ↥G | x ∈ (⊤ : Subgroup ↥G) ∧ ∃ k, orderOf x = p ^ k}) ?_
    · rwa [show Subgroup.closure {x : ↥G | x ∈ (⊤ : Subgroup ↥G) ∧
          ∃ k, orderOf x = p ^ k} = oPPrimeHull p (⊤ : Subgroup ↥G) from rfl,
        oPPrimeHull_top_of_eq hG] at h
    · rintro x ⟨-, k, hk⟩
      exact ⟨k, by rw [← hk]; exact pow_orderOf_eq_one x⟩
  have hle : (⊤ : Subgroup ↥G) ≤ CFSG.pCore p ↥G :=
    le_sSup ⟨inferInstance, hPtop⟩
  rw [hO] at hle
  have hbot : (⊤ : Subgroup ↥G) = ⊥ := le_bot_iff.mp hle
  have hone : ∀ x : ↥G, x = 1 := fun x =>
    (Subgroup.eq_bot_iff_forall (⊤ : Subgroup ↥G)).mp hbot x (Subgroup.mem_top x)
  have hGLbot : G = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact congrArg Subtype.val (hone ⟨x, hx⟩)
  have hred : ¬ CFSG.RankThree.SubgroupLists.IsIrreducibleOn G := by
    rw [hGLbot]
    refine CFSG.RankThree.SubgroupLists.not_irreducibleOn_of_forall_scalar
      (K := ZMod p) (σ := Fin 2 ⊕ Fin 2) (by simp [Fintype.card_sum]) ?_
    intro g hg
    rw [Subgroup.mem_bot] at hg
    subst hg
    exact ⟨1, by ext i j; simp [Matrix.scalar_apply]⟩
  exact hred hirr

private theorem normal_of_isComponent {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))}
    (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod p)) (hG : oPPrimeHull p G = G)
    {L : Subgroup ↥G} (hL : CFSG.IsComponent L) : L.Normal := by
  have hcard : Nat.card ↥G < 60 ^ p :=
    lt_of_le_of_lt (Subgroup.card_le_of_le hGS) (card_statedSp_lt_sixty_pow hp5)
  have hN : Subgroup.normalizer (L : Set ↥G) = ⊤ := by
    rw [eq_top_iff, ← oPPrimeHull_top_of_eq hG, oPPrimeHull]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro x ⟨-, k, hk⟩
    have hx : x ^ p = 1 := pow_prime_eq_one_of_mem hp5 (by rw [← hk]; exact pow_orderOf_eq_one x)
    change x ∈ Subgroup.normalizer (L : Set ↥G)
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      exact conj_mem_of_isComponent Fact.out hcard hL hx l hl
    · intro hl
      have hxinv : (x⁻¹) ^ p = 1 := by rw [inv_pow, hx, inv_one]
      have h := conj_mem_of_isComponent Fact.out hcard hL hxinv (x * l * x⁻¹) hl
      simpa [mul_assoc] using h
  exact (Subgroup.normalizer_eq_top_iff).mp hN

private def fixedBySubmodule {p : ℕ} (L : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))) :
    Submodule (ZMod p) ((Fin 2 ⊕ Fin 2) → ZMod p) where
  carrier := {v | ∀ g ∈ L,
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod p)) *ᵥ v = v}
  zero_mem' := by intro g hg; simp
  add_mem' := by
    intro u v hu hv g hg
    rw [Matrix.mulVec_add, hu g hg, hv g hg]
  smul_mem' := by
    intro a v hv g hg
    rw [Matrix.mulVec_smul, hv g hg]

private theorem fixedBySubmodule_invariant {p : ℕ} [Fact p.Prime]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} {L : Subgroup ↥G} (hLnormal : L.Normal) :
    ∀ h ∈ G, ∀ v ∈ fixedBySubmodule (L.map G.subtype),
      (h : Mat4 p) *ᵥ v ∈ fixedBySubmodule (L.map G.subtype) := by
  intro h hh v hv g hg
  let hG : ↥G := ⟨h, hh⟩
  obtain ⟨l, hl, rfl⟩ := hg
  have hmem : hG⁻¹ * l * hG ∈ L := hLnormal.conj_mem l hl hG⁻¹
  have hstepGL : (l : GL (Fin 2 ⊕ Fin 2) (ZMod p)) * h =
      h * ((hG⁻¹ * l * hG : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod p)) := by
    have hconj : ((hG⁻¹ * l * hG : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod p)) =
        (h : GL (Fin 2 ⊕ Fin 2) (ZMod p))⁻¹ * (l : GL (Fin 2 ⊕ Fin 2) (ZMod p)) * h := by
      simp [hG, map_mul]
    rw [hconj]
    group
  have hstep : (↑(G.subtype l) : Mat4 p) * (h : Mat4 p) =
      (h : Mat4 p) * (((hG⁻¹ * l * hG : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod p)) : Mat4 p) := by
    simpa using congrArg (fun z : GL (Fin 2 ⊕ Fin 2) (ZMod p) => (z : Mat4 p)) hstepGL
  calc
    (↑(G.subtype l) : Mat4 p) *ᵥ ((h : Mat4 p) *ᵥ v)
        = ((↑(G.subtype l) : Mat4 p) * (h : Mat4 p)) *ᵥ v := Matrix.mulVec_mulVec v _ _
    _ = ((h : Mat4 p) *
          (((hG⁻¹ * l * hG : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod p)) : Mat4 p)) *ᵥ v := by
          rw [hstep]
    _ = (h : Mat4 p) *ᵥ ((((hG⁻¹ * l * hG : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod p)) : Mat4 p) *ᵥ v) :=
          (Matrix.mulVec_mulVec v _ _).symm
    _ = (h : Mat4 p) *ᵥ v := by
          have hfix := hv (⟨(hG⁻¹ * l * hG : ↥G),
            Subgroup.mem_map_of_mem G.subtype hmem⟩ : ↥(L.map G.subtype))
            (Subgroup.mem_map_of_mem G.subtype hmem)
          rw [show (((hG⁻¹ * l * hG : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod p)) : Mat4 p) *ᵥ v = v
            from by simpa using hfix]

private theorem fixedBySubmodule_eq_bot {p : ℕ} [Fact p.Prime]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))}
    (hirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G)
    {L : Subgroup ↥G} (hLnormal : L.Normal) (hLne : L ≠ ⊥) :
    fixedBySubmodule (L.map G.subtype) = ⊥ := by
  classical
  have hWinv : ∀ h ∈ G, ∀ v ∈ fixedBySubmodule (L.map G.subtype),
      (h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod p)) *ᵥ v ∈
        fixedBySubmodule (L.map G.subtype) :=
    fixedBySubmodule_invariant (G := G) (L := L) hLnormal
  rcases hirr _ hWinv with h | h
  · exact h
  · exfalso
    obtain ⟨l, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hLne
    have hl1' : (l : ↥G) ≠ 1 := fun hl => hl1 (Subtype.ext hl)
    have hfix : ((l : GL (Fin 2 ⊕ Fin 2) (ZMod p)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod p)) = 1 := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      have hv : v ∈ fixedBySubmodule (L.map G.subtype) := by
        rw [h]
        exact Submodule.mem_top
      have := hv _ (Subgroup.mem_map_of_mem G.subtype l.2)
      simpa [Matrix.toLin'_apply] using this
    exact hl1' (Subtype.ext (Units.ext hfix))

private theorem eq_one_of_mem_centralizer_of_pow {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))}
    (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod p))
    (hirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G)
    {L : Subgroup ↥G} (hL : CFSG.IsComponent L) (hLnormal : L.Normal)
    {c : ↥G} (hc : c ∈ Subgroup.centralizer (L : Set ↥G)) {k : ℕ}
    (hck : c ^ p ^ k = 1) : c = 1 := by
  classical
  have hLne : L ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot L).mp (CFSG.LocalCores.isQuasisimple_nontrivial hL.1)
  have hbot : fixedBySubmodule (L.map G.subtype) = ⊥ :=
    fixedBySubmodule_eq_bot hirr hLnormal hLne
  have hfix : ∀ v : Fin 2 ⊕ Fin 2 → ZMod p,
      (∀ g ∈ L.map G.subtype,
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod p)) *ᵥ v = v) → v = 0 := by
    intro v hv
    have hvW : v ∈ fixedBySubmodule (L.map G.subtype) := hv
    rw [hbot] at hvW
    exact (Submodule.mem_bot (R := ZMod p)).mp hvW
  have hLq : CFSG.IsQuasisimple ↥(L.map G.subtype) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (L.equivMapOfInjective G.subtype G.subtype_injective) hL.1
  have hLS : L.map G.subtype ≤ CFSG.Open.StatedSp 2 (ZMod p) :=
    (Subgroup.map_subtype_le L).trans hGS
  have hcSp : (c : GL (Fin 2 ⊕ Fin 2) (ZMod p)) ∈ CFSG.Open.StatedSp 2 (ZMod p) :=
    hGS c.2
  have hck' : (c : GL (Fin 2 ⊕ Fin 2) (ZMod p)) ^ p ^ k = 1 :=
    congrArg (fun z : ↥G => (z : GL (Fin 2 ⊕ Fin 2) (ZMod p))) hck
  have hcomm : ∀ g ∈ L.map G.subtype,
      (c : GL (Fin 2 ⊕ Fin 2) (ZMod p)) * g = g * (c : GL (Fin 2 ⊕ Fin 2) (ZMod p)) := by
    rintro g ⟨l, hl, rfl⟩
    have h := (Subgroup.mem_centralizer_iff.mp hc l hl).symm
    exact congrArg (fun z : ↥G => (z : GL (Fin 2 ⊕ Fin 2) (ZMod p))) h
  exact Subtype.ext (eq_one_of_commute_of_perfect (by omega : p ≠ 2) hLS hLq.1 hfix hcSp hck'
    hcomm)

private theorem mem_centralizer_sup_of_isInner {p : ℕ} [Fact p.Prime]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} {L : Subgroup ↥G} [hLnormal : L.Normal]
    {x : ↥G}
    (hinner : ∃ y : ↥(L.map G.subtype),
      MulAut.congr (L.equivMapOfInjective G.subtype G.subtype_injective)
        (MulAut.conjNormal (H := L) x) = MulAut.conj y) :
    x ∈ Subgroup.centralizer (L : Set ↥G) ⊔ L := by
  classical
  obtain ⟨y, hy⟩ := hinner
  let e : ↥L ≃* ↥(L.map G.subtype) := L.equivMapOfInjective G.subtype G.subtype_injective
  let l : ↥L := e.symm y
  have hyl : e l = y := e.apply_symm_apply y
  have hinner_m : ∀ m : ↥L, x * m * x⁻¹ = (l : ↥G) * m * (l : ↥G)⁻¹ := by
    intro m
    have hαe : MulAut.congr e (MulAut.conjNormal (H := L) x) (e m) =
        e (MulAut.conjNormal (H := L) x m) := by
      simp [MulAut.congr_apply]
    have h := congrArg (fun τ : MulAut ↥(L.map G.subtype) => τ (e m)) hy
    rw [hαe] at h
    have h2 := congrArg (fun z : ↥(L.map G.subtype) =>
      (z : GL (Fin 2 ⊕ Fin 2) (ZMod p))) h
    have hyval : (y : GL (Fin 2 ⊕ Fin 2) (ZMod p)) = (l : GL (Fin 2 ⊕ Fin 2) (ZMod p)) := by
      rw [← hyl]
      rfl
    apply Subtype.ext
    simpa [e, hyval, MulAut.conjNormal_apply, MulAut.conj_apply] using h2
  have hc : (l : ↥G)⁻¹ * x ∈ Subgroup.centralizer (L : Set ↥G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h := hinner_m ⟨m, hm⟩
    calc
      (m : ↥G) * ((l : ↥G)⁻¹ * x) =
          (l : ↥G)⁻¹ * ((l : ↥G) * (m : ↥G) * (l : ↥G)⁻¹) * x := by group
      _ = (l : ↥G)⁻¹ * (x * (m : ↥G) * x⁻¹) * x := by rw [h]
      _ = ((l : ↥G)⁻¹ * x) * (m : ↥G) := by group
  have hx' : x = (l : ↥G) * ((l : ↥G)⁻¹ * x) := by group
  rw [hx', sup_comm]
  exact Subgroup.mul_mem_sup l.2 hc

private theorem quasisimple_of_card_eq_statedSp {p : ℕ} [Fact p.Prime]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))}
    (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod p)) {L : Subgroup ↥G} (hL : CFSG.IsComponent L)
    (hcard : Nat.card ↥L = Nat.card ↥(CFSG.Open.StatedSp 2 (ZMod p))) :
    CFSG.IsQuasisimple ↥G := by
  have hL'card : Nat.card ↥(L.map G.subtype) =
      Nat.card ↥(CFSG.Open.StatedSp 2 (ZMod p)) := by
    rw [Subgroup.card_map_of_injective G.subtype_injective]
    exact hcard
  have hL'le : L.map G.subtype ≤ CFSG.Open.StatedSp 2 (ZMod p) :=
    (Subgroup.map_subtype_le L).trans hGS
  have hL'top : L.map G.subtype = CFSG.Open.StatedSp 2 (ZMod p) :=
    Subgroup.eq_of_le_of_card_ge hL'le hL'card.ge
  have hGtop : G = CFSG.Open.StatedSp 2 (ZMod p) := by
    refine le_antisymm hGS ?_
    rw [← hL'top]
    exact Subgroup.map_subtype_le L
  have hLtop : L = ⊤ := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype, hL'top, hGtop]
  have hq : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥G) := hLtop ▸ hL.1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv hq

private theorem subsingleton_of_oPPrimeHull_top_eq_of_not_dvd_card {p : ℕ} [Fact p.Prime]
    {Q : Type*} [Group Q] [Finite Q] (hgen : oPPrimeHull p (⊤ : Subgroup Q) = ⊤)
    (hcop : ¬ p ∣ Nat.card Q) : Subsingleton Q := by
  have hpcop : Nat.Coprime p (Nat.card Q) :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hcop
  have hbot : oPPrimeHull p (⊤ : Subgroup Q) = ⊥ := by
    rw [oPPrimeHull]
    refine le_bot_iff.mp (Subgroup.closure_le _ |>.mpr ?_)
    rintro x ⟨-, k, hk⟩
    have hdvd1 : orderOf x ∣ p ^ k := by rw [hk]
    have hdvd2 : orderOf x ∣ Nat.card ↥(⊤ : Subgroup Q) :=
      Subgroup.orderOf_dvd_natCard ⊤ (Subgroup.mem_top x)
    rw [Subgroup.card_top] at hdvd2
    have hcop' : Nat.Coprime (p ^ k) (Nat.card Q) := hpcop.pow_left k
    have hg : orderOf x ∣ Nat.gcd (p ^ k) (Nat.card Q) := Nat.dvd_gcd hdvd1 hdvd2
    rw [hcop'.gcd_eq_one] at hg
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg))
  exact (Subgroup.subsingleton_iff).mp (subsingleton_of_top_eq_bot (hgen.symm.trans hbot))

private theorem eq_top_of_centralizer_sup_eq_top {p : ℕ} [Fact p.Prime]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} (hG : oPPrimeHull p G = G)
    {L : Subgroup ↥G} [L.Normal]
    (hsup : Subgroup.centralizer (L : Set ↥G) ⊔ L = ⊤)
    (hCone : ∀ c ∈ Subgroup.centralizer (L : Set ↥G), ∀ k, c ^ p ^ k = 1 → c = 1) :
    L = ⊤ := by
  classical
  let C : Subgroup ↥G := Subgroup.centralizer (L : Set ↥G)
  have hpC : ¬ p ∣ Nat.card ↥C := by
    intro hdvd
    obtain ⟨c, hcorder⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) p hdvd
    have hc : (c : ↥G) ^ p = 1 := by
      have h := pow_orderOf_eq_one c
      rw [hcorder] at h
      simpa using congrArg (fun z : ↥C => (z : ↥G)) h
    have h1 : (c : ↥G) = 1 := hCone (c : ↥G) c.2 1 (by simpa using hc)
    have hc1 : c = 1 := Subtype.ext h1
    rw [hc1, orderOf_one] at hcorder
    exact (Fact.out : p.Prime).one_lt.ne' hcorder.symm
  let Q := ↥G ⧸ L
  let π : ↥G →* Q := QuotientGroup.mk' L
  have hQgen : oPPrimeHull p (⊤ : Subgroup Q) = ⊤ := by
    have h := oPPrimeHull_map_eq (p := p) (f := π) (oPPrimeHull_top_of_eq hG)
    rwa [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective L)] at h
  have hCmap : C.map π = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective L y
    have hx : x ∈ L ⊔ C := by
      rw [sup_comm, hsup]
      exact Subgroup.mem_top x
    obtain ⟨l, hl, c, hc, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := L) (t := C)).mp hx
    have hl1 : π l = 1 := (QuotientGroup.eq_one_iff (N := L) l).mpr hl
    refine Subgroup.mem_map.mpr ⟨c, hc, ?_⟩
    rw [map_mul, hl1, one_mul]
  have hpCmap : ¬ p ∣ Nat.card ↥(C.map π) := fun h =>
    hpC (h.trans (Subgroup.card_map_dvd C π))
  have hpQ : ¬ p ∣ Nat.card Q := by
    intro h
    apply hpCmap
    rw [hCmap, Subgroup.card_top]
    exact h
  have hQsub : Subsingleton Q :=
    subsingleton_of_oPPrimeHull_top_eq_of_not_dvd_card hQgen hpQ
  exact (QuotientGroup.subsingleton_iff (N := L)).mp hQsub


private theorem mem_centralizer_sup_of_pow_prime_eq_one {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))}
    (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod p))
    {L : Subgroup ↥G} (hL : CFSG.IsComponent L) (hLnormal : L.Normal)
    (hcard : Nat.card ↥L ≠ Nat.card ↥(CFSG.Open.StatedSp 2 (ZMod p)))
    {x : ↥G} (hx : x ^ p = 1) :
    x ∈ Subgroup.centralizer (L : Set ↥G) ⊔ L := by
  classical
  haveI : L.Normal := hLnormal
  let e : ↥L ≃* ↥(L.map G.subtype) := L.equivMapOfInjective G.subtype G.subtype_injective
  let α : MulAut ↥(L.map G.subtype) :=
    MulAut.congr e (MulAut.conjNormal (H := L) x)
  have hα : α ^ p = 1 := by
    dsimp only [α]
    rw [← map_pow, ← map_pow, hx, map_one, map_one]
  have hLS : L.map G.subtype ≤ CFSG.Open.StatedSp 2 (ZMod p) :=
    (Subgroup.map_subtype_le L).trans hGS
  have hLq : CFSG.IsQuasisimple ↥(L.map G.subtype) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hL.1
  rcases exists_conj_of_pow_eq_one hp5 hLS hLq α hα with hinner | hcard'
  · exact mem_centralizer_sup_of_isInner hinner
  · exact absurd (by rwa [Subgroup.card_map_of_injective G.subtype_injective] at hcard') hcard

theorem isQuasisimple_of_pCore_two_le_center {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod p))
    (hG : oPPrimeHull p G = G) (hirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G)
    (hO2 : CFSG.pCore 2 ↥G ≤ Subgroup.center ↥G) : CFSG.IsQuasisimple ↥G := by
  classical
  have hO : CFSG.pCore p ↥G = ⊥ := pCore_eq_bot_of_isIrreducibleOn hirr
  have hF : CFSG.fittingSubgroup ↥G ≤ Subgroup.center ↥G :=
    fittingSubgroup_le_center hp5 hG hO hO2
  have hnab : ∃ a b : ↥G, a * b ≠ b * a :=
    exists_ne_commute_of_isIrreducibleOn hp5 hG hirr
  obtain ⟨L, hL⟩ := exists_isComponent_of_fittingSubgroup_le_center hF hnab
  have hLnormal : L.Normal := normal_of_isComponent hp5 hGS hG hL
  haveI : L.Normal := hLnormal
  by_cases hcard : Nat.card ↥L = Nat.card ↥(CFSG.Open.StatedSp 2 (ZMod p))
  · exact quasisimple_of_card_eq_statedSp hGS hL hcard
  · let C : Subgroup ↥G := Subgroup.centralizer (L : Set ↥G)
    have hmem : ∀ x : ↥G, x ^ p = 1 → x ∈ C ⊔ L := fun x hx =>
      mem_centralizer_sup_of_pow_prime_eq_one hp5 hGS hL hLnormal hcard hx
    have htop : (⊤ : Subgroup ↥G) ≤ C ⊔ L := by
      rw [← oPPrimeHull_top_of_eq hG, oPPrimeHull]
      refine Subgroup.closure_le _ |>.mpr ?_
      rintro x ⟨-, k, hk⟩
      exact hmem x (pow_prime_eq_one_of_mem hp5 (by rw [← hk]; exact pow_orderOf_eq_one x))
    have hsup : C ⊔ L = ⊤ := top_unique htop
    have hCone : ∀ c ∈ C, ∀ k, c ^ p ^ k = 1 → c = 1 := fun c hc k hck =>
      eq_one_of_mem_centralizer_of_pow hp5 hGS hirr hL hLnormal hc hck
    have hLtop : L = ⊤ := eq_top_of_centralizer_sup_eq_top hG hsup hCone
    have hq : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥G) := hLtop ▸ hL.1
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv hq

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
