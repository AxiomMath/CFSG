module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.HardMathSupport.Lang.Proving.CubeClassCyclic
public import CFSG.RankThree.PartOne.KF.ClsSUQuot
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Assembly CFSG.RankThree.PartTwo.Census


theorem exists_elemAbelian_le_normalizer_statedSU
    {F : Type} [Field F] [Finite F] {n d : ℕ}
    (hFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F)
    [CharP F 2] {r k : ℕ} (hr : r.Prime) (hrq : r ∣ 2 ^ n + 1)
    (hk : k + 2 < d) (hcen : k + 3 < d ∨ ¬ r ∣ d) (hk1 : 1 ≤ k + 1) :
    ∃ (X E : Subgroup (StatedProj (StatedSU d (2 ^ n) F))),
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian r E ∧ Nat.card E = r ^ (k + 1) ∧
        E ≤ Subgroup.normalizer (X : Set (StatedProj (StatedSU d (2 ^ n) F))) := by
  have hloc := CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus hFD hr hrq hk hcen
  obtain ⟨U, hU2, hU0, E, hEN, hEel, hEcard⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank hr hk1 hloc
  exact ⟨U, E, hU0, hU2, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r E).1 hEel,
    hEcard, hEN⟩

theorem le_evenRank_of_quotient_of_le_localRank {G : Type} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrN : ¬ r ∣ Nat.card N) (hk1 : 1 ≤ k)
    (h : k ≤ CFSG.Assembly.RankThreeEven.localRank r (G ⧸ N)) : k ≤ evenRank G := by
  obtain ⟨U, hU2, hU0, E, hEN, hEel, hEcard⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank hr hk1 h
  exact le_evenRank_of_quotient hr hr2 hrN hU0 hU2
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r E).1 hEel) hEcard hEN

theorem le_localRank_statedSU_quot_pow
    {F : Type} [Field F] [Finite F] {p f d r s : ℕ}
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F) [CharP F 2]
    (hr : r.Prime) (hd3 : 3 ≤ d)
    (hrq : r ^ (s + 1) ∣ p ^ f + 1)
    (hgd : Nat.gcd d (r ^ (s + 1)) = r ^ s)
    (N : Subgroup (StatedSU d (p ^ f) F)) [N.Normal]
    (hN : N ≤ (StatedScalars (Fin d) F).subgroupOf (StatedSU d (p ^ f) F)) :
    d - 2 ≤ CFSG.Assembly.RankThreeEven.localRank r
      (↥(StatedSU d (p ^ f) F) ⧸ N) := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hd2 : 2 ≤ d := by omega
  set k := d - 3 with hk
  have hk2 : k + 2 < d := by omega
  have hk1 : k + 1 = d - 2 := by omega
  have hdvdF : r ^ (s + 1) ∣ Nat.card F - 1 := by
    rw [h.card, pow_mul', sq,
      show p ^ f * p ^ f - 1 = p ^ f * p ^ f - 1 * 1 by rw [mul_one],
      Nat.mul_self_sub_mul_self_eq]
    exact dvd_mul_of_dvd_left hrq _
  haveI : NeZero r := ⟨hr.ne_zero⟩
  haveI : NeZero (r ^ (s + 1)) := ⟨pow_ne_zero _ hr.ne_zero⟩
  have hμ : Nat.card (rootsOfUnity (r ^ (s + 1)) F) = r ^ (s + 1) :=
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd hdvdF
  set μ := rootsOfUnity (r ^ (s + 1)) F
  set incl := μ.subtype
  set u : (Fin (k + 1) → μ) →* (Fin d → μ) := (torusEntries μ (k + 2) d).comp (dupHom μ k)
  set dχ : (Fin (k + 1) → μ) →* (Fin d → Fˣ) := (incl.compLeft (Fin d)).comp u
  set ψ := (diagGL d F).comp dχ
  have hdχ : ∀ σ i, dχ σ i = incl (u σ i) := fun _ _ => rfl
  have hdr : ∀ σ i, (dχ σ i : F) ^ (r ^ (s + 1)) = 1 := by
    intro σ i
    rw [hdχ, ← Units.val_pow_eq_pow_val, ← map_pow,
      CFSG.RankThree.PartTwo.Census.rootsOfUnity_pow_eq_one, map_one, Units.val_one]
  have hcoe : ∀ σ, ((ψ σ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal fun i => (dχ σ i : F) := fun _ => rfl
  have hmem : ∀ σ, ψ σ ∈ StatedSU d (p ^ f) F := by
    intro σ
    refine (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
    · rw [hcoe, Matrix.det_diagonal, ← Units.coe_prod]
      have hprod : ∏ i, dχ σ i =
          incl (∏ i, torusEntries μ (k + 2) d (dupHom μ k σ) i) := by
        rw [map_prod]
        rfl
      rw [hprod, CFSG.RankThree.PartTwo.Census.prod_torusEntries hk2, map_one, Units.val_one]
    · rw [hcoe, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      refine congrArg Matrix.diagonal (funext fun i => ?_)
      obtain ⟨m, hm⟩ := hrq
      rw [h.bar_apply, ← pow_succ, hm, pow_mul, hdr, one_pow]
  set ψ' : (Fin (k + 1) → μ) →* StatedSU d (p ^ f) F := ψ.codRestrict _ hmem
  have hψ' : Function.Injective ψ' := by
    intro σ τ hστ
    have h1 : ψ σ = ψ τ := congrArg Subtype.val hστ
    have h2 : dχ σ = dχ τ := by
      funext i
      have := congrArg (fun A : GL (Fin d) F => (A : Matrix (Fin d) (Fin d) F) i i) h1
      rw [hcoe σ, hcoe τ, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at this
      exact Units.ext this
    have h3 : u σ = u τ := funext fun i => Subtype.ext (congrFun h2 i)
    exact dupHom_injective k (torusEntries_injective hk2.le h3)
  set t : StatedSU d (p ^ f) F := ⟨swapGL hd2, swapGL_mem_statedSU h hd2⟩
  set π : StatedSU d (p ^ f) F →* (↥(StatedSU d (p ^ f) F) ⧸ N) := QuotientGroup.mk' N
  set Ψ : (Fin (k + 1) → μ) →* (↥(StatedSU d (p ^ f) F) ⧸ N) := π.comp ψ'
  set K' : Subgroup (Fin (k + 1) → μ) := Ψ.ker
  set powB : (Fin (k + 1) → μ) →* (Fin (k + 1) → μ) := powMonoidHom r
  set C : Subgroup (Fin (k + 1) → μ) := K'.comap powB
  have hK'leRange : K' ≤ powB.range := by
    intro b hb
    have hbker : Ψ b = 1 := hb
    have hbN : ψ' b ∈ N := by
      have h1 : π (ψ' b) = 1 := hbker
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hbS : ψ' b ∈ (StatedScalars (Fin d) F).subgroupOf (StatedSU d (p ^ f) F) :=
      hN hbN
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hbS
    have hc' : Matrix.GeneralLinearGroup.scalar (Fin d) c = ψ b := hc
    have hci : ∀ i : Fin d, (c : F) = (dχ b i : F) := by
      intro i
      have h := congrArg (fun A : GL (Fin d) F => (A : Matrix (Fin d) (Fin d) F) i i) hc'
      simpa only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq, hcoe] using h
    have hcd : c ^ d = 1 := by
      have hdet := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mp (ψ' b).2 |>.1
      change ((ψ b : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det = 1 at hdet
      rw [← hc', Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
      exact Units.ext hdet
    have hcpow : c ^ (r ^ (s + 1)) = 1 := by
      have h1 := hdr b ⟨0, by omega⟩
      rw [← hci ⟨0, by omega⟩] at h1
      exact Units.ext h1
    have hcr : c ^ (r ^ s) = 1 := by
      have hg := (pow_gcd_eq_one).mpr ⟨hcd, hcpow⟩
      rwa [hgd] at hg
    have hcμ : c ∈ μ := by
      have h0 : c = incl (u b ⟨0, by omega⟩) := Units.ext (hci ⟨0, by omega⟩)
      rw [h0]
      exact (u b ⟨0, by omega⟩).2
    let cμ : μ := ⟨c, hcμ⟩
    have hcμpow : cμ ^ (r ^ s) = 1 := by
      apply Subtype.ext
      simpa using hcr
    have hcardμ : Nat.card μ = r * r ^ s := by
      rw [hμ, pow_succ, mul_comm]
    obtain ⟨η, hη⟩ := CFSG.HardMathSupport.Lang.Proving.exists_pow_eq_of_pow_eq_one
      hcardμ hr.pos cμ hcμpow
    have hb_eq : ∀ i : Fin (k + 1), b i = cμ := by
      intro i
      have hj : i.val + 1 < d := by omega
      have hjk : i.val + 1 < k + 2 := by omega
      have h1 : dχ b ⟨i.val + 1, hj⟩ = incl cμ := by
        have h := hci ⟨i.val + 1, hj⟩
        exact Units.ext h.symm
      have h2 : u b ⟨i.val + 1, hj⟩ = cμ := by
        have h := h1
        change incl (u b ⟨i.val + 1, hj⟩) = incl cμ at h
        exact Subtype.ext h
      have h3 : u b ⟨i.val + 1, hj⟩ = dupHom μ k b ⟨i.val + 1, hjk⟩ := by
        rw [show u = (torusEntries μ (k + 2) d).comp (dupHom μ k) from rfl,
          MonoidHom.comp_apply]
        exact CFSG.RankThree.PartTwo.Census.torusEntries_of_lt _ hjk
      have h4 : dupHom μ k b ⟨i.val + 1, hjk⟩ = b i := by
        rw [CFSG.RankThree.PartTwo.Census.dupHom_apply]
        congr 1
      rw [← h4, ← h3]
      exact h2
    refine MonoidHom.mem_range.mpr ⟨fun _ => η, ?_⟩
    funext i
    simp only [powB, powMonoidHom_apply, Pi.pow_apply]
    rw [hb_eq i, ← hη]
  have hK'leC : K' ≤ C := by
    intro b hb
    rw [Subgroup.mem_comap]
    exact K'.pow_mem hb r
  have hsubμ : rootsOfUnity r F ≤ μ := by
    intro ζ hζ
    rw [mem_rootsOfUnity] at hζ ⊢
    rw [pow_succ', pow_mul, hζ, one_pow]
  have hkerBcard : Nat.card powB.ker = r ^ (k + 1) := by
    let j : rootsOfUnity r F →* μ := Subgroup.inclusion hsubμ
    have hμr : Nat.card (rootsOfUnity r F) = r := by
      refine CFSG.LinearGroups.card_rootsOfUnity_of_dvd ?_
      exact (dvd_pow_self r (by omega : s + 1 ≠ 0)).trans hdvdF
    have hcard : Nat.card powB.ker = Nat.card (Fin (k + 1) → rootsOfUnity r F) := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun x i => ⟨(x : Fin (k + 1) → μ) i, ?_⟩
          invFun := fun y => ⟨fun i => j (y i), ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · rw [mem_rootsOfUnity]
        have hx : (x : Fin (k + 1) → μ) ^ r = 1 := by
          have hx' : powB (x : Fin (k + 1) → μ) = 1 := x.2
          simpa [powB] using hx'
        have hxi := congrFun hx i
        exact congrArg (fun z : μ => (z : Fˣ)) hxi
      · rw [MonoidHom.mem_ker]
        rw [show powB (fun i => j (y i)) = (fun i => j (y i)) ^ r from rfl]
        funext i
        rw [Pi.pow_apply]
        apply Subtype.ext
        have hy : (((y i : rootsOfUnity r F) : Fˣ)) ^ r = 1 :=
          (mem_rootsOfUnity r ((y i : rootsOfUnity r F) : Fˣ)).mp (y i).2
        simpa [j] using hy
      · intro x
        apply Subtype.ext
        ext i
        simp [j]
      · intro y
        funext i
        apply Subtype.ext
        simp [j]
    rw [hcard, Nat.card_fun, hμr]
    simp
  have hker_le_C : powB.ker ≤ C := by
    intro x hx
    rw [Subgroup.mem_comap]
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    exact K'.one_mem
  have hCcard : Nat.card C = r ^ (k + 1) * Nat.card K' := by
    have hmapC : C.map powB = K' := by
      rw [Subgroup.map_comap_eq, inf_eq_right]
      exact hK'leRange
    have hker : (powB.comp C.subtype).ker = powB.ker.subgroupOf C := by
      ext x
      rfl
    have hcard := Subgroup.card_ker_mul_card_range (powB.comp C.subtype)
    have hker_card : Nat.card (powB.ker.subgroupOf C) = Nat.card powB.ker :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le_C).toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmapC, hker, hker_card,
      hkerBcard] at hcard
    exact hcard.symm
  have hkerCcard : Nat.card (K'.subgroupOf C) = Nat.card K' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'leC).toEquiv
  set E : Subgroup (↥(StatedSU d (p ^ f) F) ⧸ N) := C.map Ψ
  have hEcard : Nat.card E = r ^ (k + 1) := by
    have hker : (Ψ.comp C.subtype).ker = K'.subgroupOf C := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
      rfl
    have hrange : (Ψ.comp C.subtype).range = E := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hcard := Subgroup.card_ker_mul_card_range (Ψ.comp C.subtype)
    rw [hker, hkerCcard, hrange, hCcard] at hcard
    have hcard' : Nat.card E * Nat.card K' = r ^ (k + 1) * Nat.card K' := by
      rw [mul_comm (Nat.card E)]
      exact hcard
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard'
  have hEelem : IsElemAbelian r E := by
    refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
    · intro a b
      obtain ⟨σ, hσC, hσ⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨τ, hτC, hτ⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      change (a : ↥(StatedSU d (p ^ f) F) ⧸ N) * (b : ↥(StatedSU d (p ^ f) F) ⧸ N) =
        (b : ↥(StatedSU d (p ^ f) F) ⧸ N) * (a : ↥(StatedSU d (p ^ f) F) ⧸ N)
      rw [show (a : ↥(StatedSU d (p ^ f) F) ⧸ N) = Ψ σ from hσ.symm,
        show (b : ↥(StatedSU d (p ^ f) F) ⧸ N) = Ψ τ from hτ.symm]
      show Ψ σ * Ψ τ = Ψ τ * Ψ σ
      rw [← map_mul, ← map_mul, mul_comm σ τ]
    · intro x hx
      obtain ⟨σ, hσC, hσ⟩ := Subgroup.mem_map.mp hx
      rw [show x = Ψ σ from hσ.symm]
      show (Ψ σ) ^ r = 1
      rw [← map_pow]
      have hmem : powB σ ∈ K' := hσC
      have hmem' : σ ^ r ∈ K' := by simpa [powB] using hmem
      rw [MonoidHom.mem_ker] at hmem'
      exact hmem'
  have htN : t ∉ N := by
    intro htN
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp (hN htN)
    have := congrArg (fun A : GL (Fin d) F => (A : Matrix (Fin d) (Fin d) F)
      ⟨0, by omega⟩ ⟨1, by omega⟩) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, t, coe_swapGL,
      swapBlock, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply] at this
    simp at this
  have ht2 : t ^ 2 ∈ N := by
    rw [show t ^ 2 = 1 from Subtype.ext (Units.ext (by
      rw [pow_two]
      exact one_add_mul_one_add (swapBlock_mul_self hd2)))]
    exact N.one_mem
  have hEt : ∀ x ∈ E, x * π t = π t * x := by
    intro x hx
    obtain ⟨σ, hσC, rfl⟩ := Subgroup.mem_map.mp hx
    show π (ψ' σ) * π t = π t * π (ψ' σ)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change ((ψ σ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) * (1 + swapBlock d F) =
      (1 + swapBlock d F) * ((ψ σ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
    rw [hcoe]
    refine diagonal_mul_swap fun i j hi hj => ?_
    have key : ∀ l : Fin d, l.val < 2 → (dχ σ l : F) = ((incl (σ ⟨0, by omega⟩) : Fˣ) : F) := by
      intro l hl
      rw [hdχ]
      change ((incl (u σ l) : Fˣ) : F) = _
      rw [show u σ l = torusEntries μ (k + 2) d (dupHom μ k σ) l from rfl,
        CFSG.RankThree.PartTwo.Census.torusEntries_of_lt _ (by omega),
        CFSG.RankThree.PartTwo.Census.dupHom_apply]
      congr 3
      ext
      simp only
      omega
    rw [key i hi, key j hj]
  have hloc := CFSG.RankThree.PartTwo.Census.le_localRank_of_commute_involution hr
    (CFSG.RankThree.PartTwo.Census.orderOf_mk_eq_two N htN ht2) hEelem hEcard hEt
  omega



theorem exists_surjective_center_quotient_two
    {P SU G : Type} [Group P] [Finite P] [Group SU] [Finite SU] [Group G] [Finite G]
    [Group.IsPerfect P] [Group.IsPerfect SU] [Group.IsPerfect G]
    {pSU : SU →* P} (hpSU : Function.Surjective pSU) (hkSU : pSU.ker ≤ Subgroup.center SU)
    {pG : G →* P} (hpG : Function.Surjective pG) (hkG : pG.ker ≤ Subgroup.center G)
    {e : ℕ} (hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier P) =
      Nat.card pSU.ker * e) (he : e ∣ 4) :
    ∃ (N : Subgroup G) (_ : N.Normal), IsPGroup 2 N ∧
      ∃ (φ : SU →* G ⧸ N), Function.Surjective φ ∧ φ.ker ≤ Subgroup.center SU := by
  classical
  let H := CFSG.RankThree.PerfectCover.HopfCover P
  haveI : Finite H := CFSG.RankThree.PerfectCover.finite_hopfCover (X := P) inferInstance
  obtain ⟨-, hSU, hcompSU, -, hsurjSU, hmapSU, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier pSU hpSU hkSU
  obtain ⟨-, hG, hcompG, -, hsurjG, hmapG, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier pG hpG hkG
  let B : Subgroup H := hSU.ker
  haveI hBnorm : B.Normal := MonoidHom.normal_ker hSU
  have hBleM : B ≤ CFSG.RankThree.PerfectCover.hopfMultiplier P := by
    intro b hb
    change (CFSG.RankThree.PerfectCover.hopfCoverMap P) b = 1
    rw [← hcompSU, MonoidHom.comp_apply, hb, map_one]
  haveI hMnorm : (CFSG.RankThree.PerfectCover.hopfMultiplier P).Normal :=
    Subgroup.normal_of_le_center CFSG.RankThree.PerfectCover.hopfMultiplier_le_center
  have h1 : Nat.card H = Nat.card P * Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier P) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.RankThree.PerfectCover.hopfMultiplier P)]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (CFSG.RankThree.PerfectCover.hopfCoverMap P)
      CFSG.RankThree.PerfectCover.hopfCoverMap_surjective)
  have h2 : Nat.card H = Nat.card SU * Nat.card B := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup B]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective hSU hsurjSU)
  have h3 : Nat.card SU = Nat.card P * Nat.card pSU.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup pSU.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective pSU hpSU)
  have hBcard : Nat.card B = e := by
    have h4 : Nat.card P * Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier P) =
        Nat.card P * (Nat.card pSU.ker * Nat.card B) := by
      rw [← h1, h2, h3, mul_assoc]
    rw [hM] at h4
    have h6 := Nat.mul_left_cancel (Nat.card_pos (α := P)) h4
    exact (Nat.mul_left_cancel (Nat.card_pos (α := pSU.ker)) h6).symm
  have hB2 : IsPGroup 2 B := by
    have he2 : ∃ j, e = 2 ^ j := by
      have he4 : e ≤ 4 := Nat.le_of_dvd (by norm_num) he
      have hpos : 0 < e := Nat.pos_of_dvd_of_pos he (by norm_num)
      interval_cases e
      · exact ⟨0, by norm_num⟩
      · exact ⟨1, by norm_num⟩
      · exact absurd he (by norm_num)
      · exact ⟨2, by norm_num⟩
    obtain ⟨j, hj⟩ := he2
    exact IsPGroup.of_card (n := j) (by rw [hBcard, hj])
  let N : Subgroup G := B.map hG
  have hNle : N ≤ Subgroup.center G := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hsurjG g
    have hbM : b ∈ CFSG.RankThree.PerfectCover.hopfMultiplier P := hBleM hb
    have hbc : b ∈ Subgroup.center H :=
      CFSG.RankThree.PerfectCover.hopfMultiplier_le_center hbM
    have hbc' := Subgroup.mem_center_iff.mp hbc
    rw [← map_mul, ← map_mul, hbc' y]
  haveI hNnorm : N.Normal := Subgroup.normal_of_le_center hNle
  have hN2 : IsPGroup 2 N := hB2.map hG
  refine ⟨N, hNnorm, hN2, ?_⟩
  let q : H ⧸ B →* G ⧸ N := QuotientGroup.map B N hG (by
    intro x hx
    exact Subgroup.mem_map_of_mem hG hx)
  let eB : H ⧸ B ≃* SU := QuotientGroup.quotientKerEquivOfSurjective hSU hsurjSU
  let φ : SU →* G ⧸ N := q.comp eB.symm.toMonoidHom
  have hφsurj : Function.Surjective φ := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective (s := N) x
    obtain ⟨y, rfl⟩ := hsurjG g
    exact ⟨eB (QuotientGroup.mk y), by
      show q (eB.symm (eB (QuotientGroup.mk y))) = QuotientGroup.mk (hG y)
      rw [MulEquiv.symm_apply_apply]
      exact QuotientGroup.map_mk B N hG _ y⟩
  have hcenter : Subgroup.map hSU (Subgroup.center H) ≤ Subgroup.center SU := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨w, rfl⟩ := hsurjSU s
    have hz' := Subgroup.mem_center_iff.mp hz
    rw [← map_mul, ← map_mul, hz' w]
  have hkerG : hG.ker ≤ CFSG.RankThree.PerfectCover.hopfMultiplier P := by
    intro z hz
    change (CFSG.RankThree.PerfectCover.hopfCoverMap P) z = 1
    rw [← hcompG, MonoidHom.comp_apply, hz, map_one]
  have hφker : φ.ker ≤ Subgroup.center SU := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    obtain ⟨y, rfl⟩ := eB.surjective x
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective (s := B) y
    have hqy : q (QuotientGroup.mk w) = 1 := by simpa [φ] using hx
    have hmem : hG w ∈ N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.map_mk B N hG _ w]
      exact hqy
    obtain ⟨b, hb, hbval⟩ := Subgroup.mem_map.1 hmem
    have hyb : w * b⁻¹ ∈ Subgroup.center H :=
      CFSG.RankThree.PerfectCover.hopfMultiplier_le_center
        (hkerG (by rw [MonoidHom.mem_ker, map_mul, map_inv, hbval, mul_inv_cancel]))
    have hsub : hSU w = hSU (w * b⁻¹) := by
      rw [map_mul, map_inv, show hSU b = 1 from hb, inv_one, mul_one]
    show (eB (QuotientGroup.mk w) : SU) ∈ Subgroup.center SU
    rw [show (eB (QuotientGroup.mk w) : SU) = hSU w from rfl, hsub]
    exact hcenter (Subgroup.mem_map_of_mem hSU hyb)
  exact ⟨φ, hφsurj, hφker⟩

private theorem psu_exceptional_dvd_four (d n : ℕ) :
    (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU d 2 n).1 *
      (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU d 2 n).2 ∣ 4 := by
  by_cases hd4 : d = 4
  · subst hd4
    by_cases hn1 : n = 1
    · subst hn1; norm_num [CFSG.Blueprint.Multiplier.exceptionalOrders]
    · simp [CFSG.Blueprint.Multiplier.exceptionalOrders, hn1]
  · by_cases hd6 : d = 6
    · subst hd6
      by_cases hn1 : n = 1
      · subst hn1; norm_num [CFSG.Blueprint.Multiplier.exceptionalOrders]
      · simp [CFSG.Blueprint.Multiplier.exceptionalOrders, hn1]
    · simp [CFSG.Blueprint.Multiplier.exceptionalOrders, hd4, hd6]

private theorem card_hopfMultiplier_statedSU {F : Type} [Field F] [Finite F] {d n : ℕ}
    (hLie : CFSG.Blueprint.LieModel (StatedProj (StatedSU d (2 ^ n) F)) .PSU d 2 n) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedSU d (2 ^ n) F))) =
      Nat.gcd d (2 ^ n + 1) *
        ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSU d 2 n).1 *
          (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU d 2 n).2) := by
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    (StatedProj (StatedSU d (2 ^ n) F)) .PSU d 2 n hLie
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
      (StatedProj (StatedSU d (2 ^ n) F))).toEquiv,
    Nat.card_congr eM.toEquiv,
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional']
  norm_num [CFSG.Blueprint.Multiplier.genericOrders]

private theorem card_ker_statedProj {F : Type} [Field F] [Finite F] {n d : ℕ}
    (hFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F) (hd1 : 1 ≤ d) :
    Nat.card (QuotientGroup.mk'
      ((StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F))).ker =
      Nat.gcd d (2 ^ n + 1) := by
  rw [QuotientGroup.ker_mk']
  have h := CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars hFD (n := d) hd1
  rwa [CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq hFD hd1] at h

theorem exists_prime_factorization_lt_of_not_dvd {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0)
    (hnot : ¬ n ∣ d) : ∃ r : ℕ, r.Prime ∧ d.factorization r < n.factorization r := by
  by_contra h
  push Not at h
  have hle : n.factorization ≤ d.factorization := fun p => by
    by_cases hp : p.Prime
    · exact h p hp
    · rw [show n.factorization p = 0 from
          (Nat.factorization_eq_zero_iff n p).mpr (Or.inl hp),
        show d.factorization p = 0 from
          (Nat.factorization_eq_zero_iff d p).mpr (Or.inl hp)]
  exact hnot ((Nat.factorization_le_iff_dvd hn hd).mp hle)

theorem gcd_pow_factorization_succ {d r : ℕ} (hd : d ≠ 0) (hr : r.Prime) :
    Nat.gcd d (r ^ (d.factorization r + 1)) = r ^ d.factorization r := by
  set s := d.factorization r
  have h1 : r ^ s ∣ d := (Nat.Prime.pow_dvd_iff_le_factorization hr hd).mpr le_rfl
  set g := Nat.gcd d (r ^ (s + 1))
  have hgdvd : g ∣ r ^ (s + 1) := Nat.gcd_dvd_right _ _
  obtain ⟨j, -, hgj⟩ := (Nat.dvd_prime_pow hr).mp hgdvd
  have hjd : r ^ j ∣ d := hgj ▸ Nat.gcd_dvd_left _ _
  have hjle' : j ≤ s := (Nat.Prime.pow_dvd_iff_le_factorization hr hd).mp hjd
  have hsdvdg : r ^ s ∣ g := Nat.dvd_gcd h1 (Nat.pow_dvd_pow r (by omega))
  rw [hgj] at hsdvdg
  have hsj : s ≤ j := by
    rw [Nat.Prime.pow_dvd_iff_le_factorization hr (pow_ne_zero _ hr.ne_zero),
      Nat.Prime.factorization_pow hr] at hsdvdg
    simpa using hsdvdg
  rw [hgj, show j = s by omega]

private theorem le_evenRank_of_statedSU_unitary_pow
    {K F : Type} [Group K] [Finite K] [Field F] [Finite F]
    {d n : ℕ} (hcardF : Nat.card F = (2 ^ n) ^ 2) (hn1 : 1 ≤ n) (hd3 : 3 ≤ d)
    (hne : (d, 2 ^ n) ≠ (3, 2))
    (θ : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU d (2 ^ n) F))
    (hLie : CFSG.Blueprint.LieModel (StatedProj (StatedSU d (2 ^ n) F)) .PSU d 2 n)
    (hKperf : Group.IsPerfect K)
    {r s : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ^ (s + 1) ∣ 2 ^ n + 1)
    (hgd : Nat.gcd d (r ^ (s + 1)) = r ^ s) :
    d - 2 ≤ evenRank K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hcardF
  have hFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, hn1, by rw [hcardF, ← pow_mul, mul_comm]⟩
  have hperfSU : Group.IsPerfect (StatedSU d (2 ^ n) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcardF hd3 hne
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSU d (2 ^ n) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 n hcardF d hd3 hne
  have hZeq : Subgroup.center (StatedSU d (2 ^ n) F) =
      (StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU hperfSU hsimpleP).2
  haveI : Group.IsPerfect (StatedProj (StatedSU d (2 ^ n) F)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk'
      ((StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F)))
      (QuotientGroup.mk'_surjective _)
  let S : Subgroup (StatedSU d (2 ^ n) F) :=
    (StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F)
  let pSU : StatedSU d (2 ^ n) F →* StatedProj (StatedSU d (2 ^ n) F) :=
    QuotientGroup.mk' S
  have hpSU : Function.Surjective pSU := QuotientGroup.mk'_surjective S
  have hkSU : pSU.ker ≤ Subgroup.center (StatedSU d (2 ^ n) F) := by
    rw [show pSU.ker = S from QuotientGroup.ker_mk' S, hZeq]
  let pK : K →* StatedProj (StatedSU d (2 ^ n) F) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hpK : Function.Surjective pK :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkK : pK.ker ≤ Subgroup.center K := by
    have h : pK.ker = Subgroup.center K := by
      rw [show pK = θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) from rfl,
        MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
    rw [h]
  have hMtable := card_hopfMultiplier_statedSU (F := F) (d := d) (n := n) hLie
  have hker := card_ker_statedProj (F := F) (n := n) (d := d) hFD (by omega)
  have he := psu_exceptional_dvd_four d n
  obtain ⟨N, hNnorm, hN2, φ, hφsurj, hφker⟩ :=
    exists_surjective_center_quotient_two hpSU hkSU hpK hkK
      (e := (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU d 2 n).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU d 2 n).2)
      (by rw [hMtable, hker]) he
  have hφker' : φ.ker ≤ S := by
    dsimp only [S]
    rw [← hZeq]
    exact hφker
  have hlocSU : d - 2 ≤ CFSG.Assembly.RankThreeEven.localRank r
      (↥(StatedSU d (2 ^ n) F) ⧸ φ.ker) :=
    le_localRank_statedSU_quot_pow (F := F) (p := 2) (f := n) hFD hr hd3 hrq hgd
      φ.ker hφker'
  have hloc : d - 2 ≤ CFSG.Assembly.RankThreeEven.localRank r (K ⧸ N) := by
    let e := QuotientGroup.quotientKerEquivOfSurjective φ hφsurj
    rw [localRank_eq_of_mulEquiv e hr] at hlocSU
    exact hlocSU
  have hrN : ¬ r ∣ Nat.card N := by
    intro hdvd
    obtain ⟨j, hj⟩ := hN2.exists_card_eq
    rw [hj] at hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdvd))
  exact le_evenRank_of_quotient_of_le_localRank hr hr2 hrN (by omega) hloc

private theorem le_evenRank_of_statedSU_unitary
    {K F : Type} [Group K] [Finite K] [Field F] [Finite F]
    {d n : ℕ} (hcardF : Nat.card F = (2 ^ n) ^ 2) (hn1 : 1 ≤ n) (hd3 : 3 ≤ d)
    (hne : (d, 2 ^ n) ≠ (3, 2))
    (θ : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU d (2 ^ n) F))
    (hLie : CFSG.Blueprint.LieModel (StatedProj (StatedSU d (2 ^ n) F)) .PSU d 2 n)
    (hKperf : Group.IsPerfect K)
    {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ 2 ^ n + 1)
    (hk : k + 2 < d) (hcen : k + 3 < d ∨ ¬ r ∣ d) (hk1 : 1 ≤ k + 1) :
    k + 1 ≤ evenRank K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hcardF
  have hFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, hn1, by rw [hcardF, ← pow_mul, mul_comm]⟩
  have hperfSU : Group.IsPerfect (StatedSU d (2 ^ n) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcardF hd3 hne
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSU d (2 ^ n) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 n hcardF d hd3 hne
  have hZeq : Subgroup.center (StatedSU d (2 ^ n) F) =
      (StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU hperfSU hsimpleP).2
  haveI : Group.IsPerfect (StatedProj (StatedSU d (2 ^ n) F)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk'
      ((StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F)))
      (QuotientGroup.mk'_surjective _)
  let S : Subgroup (StatedSU d (2 ^ n) F) :=
    (StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F)
  let pSU : StatedSU d (2 ^ n) F →* StatedProj (StatedSU d (2 ^ n) F) :=
    QuotientGroup.mk' S
  have hpSU : Function.Surjective pSU := QuotientGroup.mk'_surjective S
  have hkSU : pSU.ker ≤ Subgroup.center (StatedSU d (2 ^ n) F) := by
    rw [show pSU.ker = S from QuotientGroup.ker_mk' S, hZeq]
  let pK : K →* StatedProj (StatedSU d (2 ^ n) F) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hpK : Function.Surjective pK :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkK : pK.ker ≤ Subgroup.center K := by
    have h : pK.ker = Subgroup.center K := by
      rw [show pK = θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) from rfl,
        MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
    rw [h]
  have hMtable := card_hopfMultiplier_statedSU (F := F) (d := d) (n := n) hLie
  have hker := card_ker_statedProj (F := F) (n := n) (d := d) hFD (by omega)
  have he := psu_exceptional_dvd_four d n
  obtain ⟨N, hNnorm, hN2, φ, hφsurj, hφker⟩ :=
    exists_surjective_center_quotient_two hpSU hkSU hpK hkK
      (e := (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU d 2 n).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU d 2 n).2)
      (by rw [hMtable, hker]) he
  have hφker' : φ.ker ≤ S := by
    dsimp only [S]
    rw [← hZeq]
    exact hφker
  have hloc : k + 1 ≤ CFSG.Assembly.RankThreeEven.localRank r (K ⧸ N) :=
    CFSG.RankThree.PartOne.KFU.le_localRank_of_surjective_statedSU_torus hFD hr hrq hk hcen
      φ hφsurj hφker'
  have hrN : ¬ r ∣ Nat.card N := by
    intro hdvd
    obtain ⟨j, hj⟩ := hN2.exists_card_eq
    rw [hj] at hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdvd))
  exact le_evenRank_of_quotient_of_le_localRank hr hr2 hrN hk1 hloc

theorem rk2_low_twa_two (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twA) :
    lab.rank - 2 ≤ evenRank K := by
  obtain ⟨hQ, hlab, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  obtain ⟨t, l, n⟩ := lab
  simp only at htag
  subst htag
  simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
  obtain ⟨hn1, hl2, hl2n⟩ := hlab
  rcases lt_or_ge l 3 with hl3 | hl3
  ·
    have hl : l = 2 := by omega
    subst hl
    simp
  · have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU (l + 1) 2 n := by
      simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
        CFSG.StandardType.markRank, CFSG.StandardType.markChar,
        CFSG.StandardType.markDeg] using hM
    obtain ⟨-, F, hFld, hFin, hFcard, ⟨θ⟩⟩ := hM'.statedClassicalModel (by decide)
    letI : Field F := hFld
    letI : Finite F := hFin
    have hne : (l + 1, 2 ^ n) ≠ (3, 2) := by
      intro h
      have h1 : l + 1 = 3 := congrArg Prod.fst h
      have h2 : 2 ^ n = 2 := congrArg Prod.snd h
      have hl : l = 2 := by omega
      have hn2 : 2 ≤ n := hl2n hl
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      rw [h2] at h4
      omega
    have hd3 : 3 ≤ l + 1 := by omega
    obtain ⟨r, hr, hr2, hrq⟩ :=
      CFSG.RankThree.PartTwo.Census.exists_odd_prime_dvd_two_pow_add_one hn1
    have hk : l - 3 + 2 < l + 1 := by omega
    have hcen : l - 3 + 3 < l + 1 ∨ ¬ r ∣ l + 1 := Or.inl (by omega)
    have hk1 : 1 ≤ l - 3 + 1 := by omega
    have hbound := le_evenRank_of_statedSU_unitary hFcard hn1 hd3 hne θ
      (hM'.of_mulEquiv θ) hQ'.1 hr hr2 hrq hk hcen hk1
    show l - 2 ≤ evenRank K
    omega

theorem rk2_low_twa_one (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twA)
    (hnot : ¬ (2 ^ lab.n + 1 ∣ lab.rank + 1)) :
    lab.rank - 1 ≤ evenRank K := by
  obtain ⟨hQ, hlab, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  obtain ⟨t, l, n⟩ := lab
  simp only at htag
  subst htag
  simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
  obtain ⟨hn1, hl2, hl2n⟩ := hlab
  have hdpos : l + 1 ≠ 0 := by omega
  have hnpos : 2 ^ n + 1 ≠ 0 := by positivity
  obtain ⟨r, hr, hlt⟩ :=
    exists_prime_factorization_lt_of_not_dvd hdpos hnpos hnot
  let s := (l + 1).factorization r
  have hrq : r ^ (s + 1) ∣ 2 ^ n + 1 :=
    (Nat.Prime.pow_dvd_iff_le_factorization hr hnpos).mpr (by omega)
  have hgd : Nat.gcd (l + 1) (r ^ (s + 1)) = r ^ s :=
    gcd_pow_factorization_succ hdpos hr
  have hrdvd : r ∣ 2 ^ n + 1 :=
    (dvd_pow_self r (by omega : s + 1 ≠ 0)).trans hrq
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hodd : Odd (2 ^ n + 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact ⟨2 ^ m, by ring⟩
    have h2 : (2 ^ n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hrdvd
    rw [Nat.odd_iff.mp hodd] at h2
    exact Nat.one_ne_zero h2
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU (l + 1) 2 n := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg] using hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨θ⟩⟩ := hM'.statedClassicalModel (by decide)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hne : (l + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 : l + 1 = 3 := congrArg Prod.fst h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have hl : l = 2 := by omega
    have hn2 : 2 ≤ n := hl2n hl
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    rw [h2] at h4
    omega
  have hd3 : 3 ≤ l + 1 := by omega
  have hbound := le_evenRank_of_statedSU_unitary_pow hFcard hn1 hd3 hne θ
    (hM'.of_mulEquiv θ) hQ'.1 hr hr2 hrq hgd
  show l - 1 ≤ evenRank K
  omega

theorem rk2_low_twd_three (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twD) (hr3 : lab.rank = 3) :
    2 ≤ evenRank K := by
  obtain ⟨hQ, hlab, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  obtain ⟨t, l, n⟩ := lab
  simp only at htag hr3
  subst htag
  subst hr3
  simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
  have hn1 : 1 ≤ n := hlab.1
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU 4 2 n := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg] using hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨θ⟩⟩ := hM'.statedClassicalModel (by decide)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hne : (4, 2 ^ n) ≠ (3, 2) := by
    intro h
    exact absurd (congrArg Prod.fst h) (by norm_num)
  obtain ⟨r, hr, hr2, hrq⟩ :=
      CFSG.RankThree.PartTwo.Census.exists_odd_prime_dvd_two_pow_add_one hn1
  have hk : 1 + 2 < 4 := by norm_num
  have hcen : 1 + 3 < 4 ∨ ¬ r ∣ 4 := by
    right
    intro hdvd
    have h2 : r ∣ 2 := by
      have h4 : r ∣ 2 ^ 2 := by simpa using hdvd
      exact hr.dvd_of_dvd_pow h4
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
  have hk1 : 1 ≤ 1 + 1 := by norm_num
  exact le_evenRank_of_statedSU_unitary hFcard hn1 (by norm_num) hne θ
    (hM'.of_mulEquiv θ) hQ'.1 hr hr2 hrq hk hcen hk1

end CFSG.LocalAnalysis.GLTheoremA
