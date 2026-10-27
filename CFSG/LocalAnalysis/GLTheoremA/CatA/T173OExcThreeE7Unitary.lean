module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE7Frame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE7Eichler

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.OrthBlk
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCOrthogonalD4 CFSG.RankThree.PartOne.KCPrimary CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
  CFSG.LocalAnalysis.GLTheoremA.T173M CFSG.LocalAnalysis.GLTheoremA.T173U

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

private theorem blockDet_pow_eq_one {x g : V ≃ₗ[F] V} {h : F[X]} (hg : g ∈ supportedBlock Q x h)
    (hgp : g ^ p = 1) : blockDet Q x h ⟨g, hg⟩ ^ p = 1 := by
  rw [← map_pow, show (⟨g, hg⟩ : ↥(supportedBlock Q x h)) ^ p = 1 from Subtype.ext hgp, map_one]

theorem exists_mul_pow_mem_specialBlock {x a b : V ≃ₗ[F] V} {h : F[X]} (hh : Irreducible h)
    (hp : p.Prime) (ha : a ∈ supportedBlock Q x h) (hb : b ∈ supportedBlock Q x h)
    (hap : a ^ p = 1) (hbp : b ^ p = 1) (hbS : b ∉ specialBlock Q x h) :
    ∃ i : ℕ, i < p ∧ a * b ^ i ∈ specialBlock Q x h := by
  classical
  haveI : Fact (Irreducible h) := ⟨hh⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fintype (rootsOfUnity p (AdjoinRoot h)) := Fintype.ofFinite _
  have hdet_a : blockDet Q x h ⟨a, ha⟩ ^ p = 1 := blockDet_pow_eq_one ha hap
  have hdet_b : blockDet Q x h ⟨b, hb⟩ ^ p = 1 := blockDet_pow_eq_one hb hbp
  have hdet_b1 : blockDet Q x h ⟨b, hb⟩ ≠ 1 := fun h1 =>
    hbS (mem_specialBlock.mpr ⟨hb, h1⟩)
  let α : rootsOfUnity p (AdjoinRoot h) := rootsOfUnity.mkOfPowEq _ hdet_a
  let γ : rootsOfUnity p (AdjoinRoot h) := rootsOfUnity.mkOfPowEq _ hdet_b
  have hα : ((α : (AdjoinRoot h)ˣ) : AdjoinRoot h) = blockDet Q x h ⟨a, ha⟩ := rfl
  have hγ : ((γ : (AdjoinRoot h)ˣ) : AdjoinRoot h) = blockDet Q x h ⟨b, hb⟩ := rfl
  have hγne : γ ≠ 1 := by
    intro h1
    refine hdet_b1 ?_
    have h2 := congrArg (fun z : rootsOfUnity p (AdjoinRoot h) =>
      ((z : (AdjoinRoot h)ˣ) : AdjoinRoot h)) h1
    simpa [hγ] using h2
  have hγp : γ ^ p = 1 := Subtype.ext γ.2
  have hordγ : orderOf γ = p := orderOf_eq_prime hγp hγne
  have hcard : Nat.card (rootsOfUnity p (AdjoinRoot h)) = p := by
    refine le_antisymm (card_rootsOfUnity _ _) ?_
    calc p = orderOf γ := hordγ.symm
      _ ≤ Nat.card (rootsOfUnity p (AdjoinRoot h)) := orderOf_le_card
  have hinj : Set.InjOn (fun i : ℕ => α * γ ^ i) ↑(Finset.range p) := by
    intro i hi j hj hij
    have hi' : i < orderOf γ := by rw [hordγ]; exact Finset.mem_range.1 hi
    have hj' : j < orderOf γ := by rw [hordγ]; exact Finset.mem_range.1 hj
    exact pow_injOn_Iio_orderOf hi' hj' (mul_left_cancel hij)
  have hT : (Finset.range p).image (fun i : ℕ => α * γ ^ i) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← Nat.card_eq_fintype_card, hcard]
  obtain ⟨i, hi, hprod⟩ : ∃ i ∈ Finset.range p, α * γ ^ i = 1 := by
    have h1 : (1 : rootsOfUnity p (AdjoinRoot h)) ∈
        (Finset.range p).image (fun i : ℕ => α * γ ^ i) := by
      rw [hT]; exact Finset.mem_univ 1
    obtain ⟨i, hi, hii⟩ := Finset.mem_image.1 h1
    exact ⟨i, hi, hii⟩
  have hmem : a * b ^ i ∈ supportedBlock Q x h :=
    Subgroup.mul_mem (supportedBlock Q x h) ha (Subgroup.pow_mem (supportedBlock Q x h) hb i)
  refine ⟨i, Finset.mem_range.1 hi, mem_specialBlock.mpr ⟨hmem, ?_⟩⟩
  have hcoe : (⟨a * b ^ i, hmem⟩ : ↥(supportedBlock Q x h))
      = ⟨a, ha⟩ * ⟨b, hb⟩ ^ i := Subtype.ext rfl
  rw [hcoe, map_mul, map_pow]
  have h2 := congrArg (fun z : rootsOfUnity p (AdjoinRoot h) =>
    ((z : (AdjoinRoot h)ˣ) : AdjoinRoot h)) hprod
  simpa [hα, hγ] using h2

theorem mem_supportedBlock_of_fullSupport {n : ℕ} (hdim : Module.finrank F V = 2 * n)
    {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb)
    (hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V)) {h : F[X]}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap)
    (hUh : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) {b : ↥(orthDerived Q)}
    (hb : b ∈ Bb) : (b : V ≃ₗ[F] V) ∈ supportedBlock Q (d : V ≃ₗ[F] V) h := by
  have hVh : primaryComponent (d : V ≃ₗ[F] V).toLinearMap h = ⊤ := by
    rw [eq_top_iff, ← T173M.iSup_eq_top_of_finrank hF.toIsPlaneSystem hdim]
    exact iSup_le hUh
  have hbot : othersSpace (d : V ≃ₗ[F] V).toLinearMap h = ⊥ := by
    unfold othersSpace
    refine iSup_eq_bot.2 fun k => iSup_eq_bot.2 fun hk => ?_
    have hdisj := disjoint_primaryComponent_of_ne hx hh hk.1 (Ne.symm hk.2.1)
    rw [disjoint_iff, hVh, top_inf_eq] at hdisj
    exact hdisj
  refine mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr ⟨?_, ?_⟩, ?_⟩
  · intro v
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (orthDerived_le_orthogonalGroup b.2) v
  · intro v
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
      (T173M.mul_comm_of_mem_torus hF hb hd)
    exact congrFun (congrArg (fun z : V ≃ₗ[F] V => (z : V → V)) h) v
  · intro v hv
    rw [hbot] at hv
    rw [(Submodule.mem_bot F).1 hv, map_zero]

theorem eichler_mem_specialBlock_of_mem_primaryComponent
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1) {u : V}
    (hu : u ∈ primaryComponent x.toLinearMap h) (hu0 : u ≠ 0) (hQu : Q u = 0) :
    QuadraticMap.polar Q u (x u) = 0 ∧ eichler Q u (x u) ∈ specialBlock Q x h ∧
      eichler Q u (x u) ≠ 1 := by
  have h1 : x u ∈ rootSet Q (specialBlock Q x h) u := by
    have h := T173U.aeval_mem_rootSet_specialBlock hp hp2 hpq hx hh hh1 hu hQu (X : F[X])
    rwa [Polynomial.aeval_X] at h
  refine ⟨h1.1, h1.2, fun hE1 => ?_⟩
  obtain ⟨c, hc⟩ := (eichler_eq_one_iff hQ hQu hu0 h1.1).1 hE1
  have hiter : ∀ k : ℕ, (x ^ k) u = (c ^ k) • u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hc, smul_smul, pow_succ]
  have hcp : c ^ p = 1 := by
    have h1 : (x ^ p) u = c ^ p • u := hiter p
    rw [hx.pow_eq_one] at h1
    have h2 : u = c ^ p • u := h1
    have hzero : (c ^ p - 1) • u = 0 := by
      rw [sub_smul, one_smul, ← h2, sub_self]
    rcases smul_eq_zero.1 hzero with h0 | h0
    · exact sub_eq_zero.1 h0
    · exact absurd h0 hu0
  have hc1 : c = 1 := eq_one_of_pow_eq_one_of_dvd_card_add_one hp hp2 hpq hcp
  exact hu0 (eq_zero_of_mem_primaryComponent_of_apply_eq hh hh1 hu (by rw [hc, hc1, one_smul]))

private theorem pow_eq_one_of_frame {n : ℕ} {U : Fin n → Submodule F V}
    {e : Fin n → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb)
    (i : Fin n) : ((e i : V ≃ₗ[F] V)) ^ p = 1 := by
  have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
    (hF.orderOf_eq i ▸ pow_orderOf_eq_one (e i))
  simpa using h

private theorem mem_sup_of_mem_normalizer_of_not_mem_specialBlock {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hp : p.Prime) {U : Fin n → Submodule F V}
    {e : Fin n → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb) (hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V)) {h : F[X]}
    (hirr : Irreducible h) (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap)
    (hUh : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h)
    {T : Subgroup ↥(orthDerived Q)} {k i : Fin n}
    (hk : (e k : V ≃ₗ[F] V) ∉ specialBlock Q (d : V ≃ₗ[F] V) h)
    (hkT : e k ∈ Subgroup.normalizer (T : Set ↥(orthDerived Q))) :
    e i ∈ (Bb ⊓ (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) ⊔
      (Bb ⊓ Subgroup.normalizer (T : Set ↥(orthDerived Q))) := by
  by_cases hi : (e i : V ≃ₗ[F] V) ∈ specialBlock Q (d : V ≃ₗ[F] V) h
  · exact Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hF.mem i, Subgroup.mem_subgroupOf.2 hi⟩)
  · obtain ⟨m, -, hdet⟩ := exists_mul_pow_mem_specialBlock hirr hp
      (mem_supportedBlock_of_fullSupport hdim hF hd hx hh hUh (hF.mem i))
      (mem_supportedBlock_of_fullSupport hdim hF hd hx hh hUh (hF.mem k))
      (pow_eq_one_of_frame hF i) (pow_eq_one_of_frame hF k) hk
    set g : ↥(orthDerived Q) := e i * (e k) ^ m with hgm
    have hgsb : (g : V ≃ₗ[F] V) ∈ specialBlock Q (d : V ≃ₗ[F] V) h := by
      rw [hgm]
      simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using hdet
    have hgL : g ∈ Bb ⊓ (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q) :=
      Subgroup.mem_inf.2 ⟨Subgroup.mul_mem Bb (hF.mem i) (Subgroup.pow_mem Bb (hF.mem k) m),
        Subgroup.mem_subgroupOf.2 hgsb⟩
    have hkN : (e k) ^ m ∈ Bb ⊓ Subgroup.normalizer (T : Set ↥(orthDerived Q)) :=
      Subgroup.mem_inf.2 ⟨Subgroup.pow_mem Bb (hF.mem k) m, Subgroup.pow_mem _ hkT m⟩
    have hei : e i = g * ((e k) ^ m)⁻¹ := by
      rw [hgm]; group
    rw [hei]
    exact Subgroup.mul_mem_sup hgL (Subgroup.inv_mem _ hkN)

private theorem exists_twoGroup_centralized_of_fullSupport
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (hd1 : d ≠ 1) {h : F[X]}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) (k : Fin n) :
    ∃ T : Subgroup ↥(orthDerived Q), T ≠ ⊥ ∧ IsPGroup 2 T ∧
      T ≤ (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q) ∧
      e k ∈ Subgroup.centralizer (T : Set ↥(orthDerived Q)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hVh : primaryComponent (d : V ≃ₗ[F] V).toLinearMap h = ⊤ := by
    rw [eq_top_iff, ← T173M.iSup_eq_top_of_finrank hF.toIsPlaneSystem hdim]
    exact iSup_le hUh
  have hdimk : Module.finrank F (polarPerp Q (U k)) = 2 * n - 2 := by
    rw [finrank_polarPerp hQ (U k), hF.finrank_eq k, hdim]
  have h3 : 3 ≤ Module.finrank F (polarPerp Q (U k)) := by rw [hdimk]; omega
  obtain ⟨u, huW, hu0, hQu⟩ := exists_singular_of_three_le_any (Q := Q) h3
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d
      (orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1)
  obtain ⟨huw, hEs, hE1⟩ := eichler_mem_specialBlock_of_mem_primaryComponent hQ hp hp2 hpq hx hh
    hh1 (by rw [hVh]; exact Submodule.mem_top) hu0 hQu
  have hE : eichler Q u ((d : V ≃ₗ[F] V) u) ∈ orthDerived Q :=
    eichler_mem_orthDerived hQ hn hdim u ((d : V ≃ₗ[F] V) u)
  obtain ⟨hTne, hT2⟩ := zpowers_eichler_ne_bot_and_isPGroup hQu huw hE hE1
  have hcomm : Commute (e k : V ≃ₗ[F] V) (eichler Q u ((d : V ≃ₗ[F] V) u)) := by
    have h1 : (e k : V ≃ₗ[F] V) u = u := hF.apply_of_perp k u huW
    have hcd : (e k : V ≃ₗ[F] V) * (d : V ≃ₗ[F] V) = (d : V ≃ₗ[F] V) * (e k : V ≃ₗ[F] V) :=
      congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
        (T173M.mul_comm_of_mem_torus hF (hF.mem k) hd)
    have h2 : (e k : V ≃ₗ[F] V) ((d : V ≃ₗ[F] V) u) = (d : V ≃ₗ[F] V) u := by
      rw [← LinearEquiv.mul_apply, hcd, LinearEquiv.mul_apply, h1]
    have h3 : (e k : V ≃ₗ[F] V) * eichler Q u ((d : V ≃ₗ[F] V) u) * (e k : V ≃ₗ[F] V)⁻¹
        = eichler Q u ((d : V ≃ₗ[F] V) u) := by
      rw [eichler_conj (orthDerived_le_orthogonalGroup (e k).2) u ((d : V ≃ₗ[F] V) u), h1, h2]
    have h4 : (e k : V ≃ₗ[F] V) * eichler Q u ((d : V ≃ₗ[F] V) u)
        = ((e k : V ≃ₗ[F] V) * eichler Q u ((d : V ≃ₗ[F] V) u)
          * (e k : V ≃ₗ[F] V)⁻¹) * (e k : V ≃ₗ[F] V) := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    show (e k : V ≃ₗ[F] V) * eichler Q u ((d : V ≃ₗ[F] V) u)
      = eichler Q u ((d : V ≃ₗ[F] V) u) * (e k : V ≃ₗ[F] V)
    rw [h4, h3]
  refine ⟨Subgroup.zpowers ⟨eichler Q u ((d : V ≃ₗ[F] V) u), hE⟩, hTne, hT2, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_subgroupOf.2 hEs
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine Subtype.ext ?_
    have hgm : (g : V ≃ₗ[F] V) = (eichler Q u ((d : V ≃ₗ[F] V) u)) ^ m := by
      rw [← hm]
      rfl
    show (g : V ≃ₗ[F] V) * (e k : V ≃ₗ[F] V) = (e k : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V)
    rw [hgm]
    exact ((hcomm.zpow_right m).eq).symm

theorem exists_twoGroup_decomp_fullSupport (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (hd1 : d ≠ 1) {h : F[X]} (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap)
    (hh1 : h ≠ X - 1) (hUh : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) :
    ∃ T : Subgroup ↥(orthDerived Q), T ≠ ⊥ ∧ IsPGroup 2 T ∧
      T ≤ (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q) ∧
      Bb = (Bb ⊓ (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) ⊔
        (Bb ⊓ Subgroup.normalizer (T : Set ↥(orthDerived Q))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d
      (orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1)
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  by_cases hex : ∃ k : Fin n, (e k : V ≃ₗ[F] V) ∉ specialBlock Q (d : V ≃ₗ[F] V) h
  · obtain ⟨k, hk⟩ := hex
    obtain ⟨T, hTne, hT2, hTL, hkc⟩ :=
      exists_twoGroup_centralized_of_fullSupport hQ hdim hn hp hp2 hpq hF hd hd1 hh hh1 hUh k
    have hkT : e k ∈ Subgroup.normalizer (T : Set ↥(orthDerived Q)) :=
      Subgroup.centralizer_le_normalizer _ hkc
    refine ⟨T, hTne, hT2, hTL, le_antisymm ?_ (sup_le inf_le_left inf_le_left)⟩
    have hgen : Subgroup.closure (Set.range e) ≤
        (Bb ⊓ (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) ⊔
          (Bb ⊓ Subgroup.normalizer (T : Set ↥(orthDerived Q))) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro - ⟨i, rfl⟩
      exact mem_sup_of_mem_normalizer_of_not_mem_specialBlock (U := U) (e := e) (Bb := Bb)
        (d := d) (h := h) (T := T) (k := k) (i := i) hdim hp hF hd hx hirr hh hUh hk hkT
    rwa [hF.closure_eq] at hgen
  · push Not at hex
    obtain ⟨T, hTne, hT2, hTL, -⟩ :=
      exists_twoGroup_centralized_of_fullSupport hQ hdim hn hp hp2 hpq hF hd hd1 hh hh1 hUh
        ⟨0, by omega⟩
    have hL : Bb ≤ (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q) := by
      rw [← hF.closure_eq, Subgroup.closure_le]
      rintro - ⟨i, rfl⟩
      exact Subgroup.mem_subgroupOf.2 (hex i)
    have hle : Bb ⊓ Subgroup.normalizer (T : Set ↥(orthDerived Q)) ≤
        Bb ⊓ (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q) :=
      le_inf (fun x hx' => (Subgroup.mem_inf.1 hx').1)
        (fun x hx' => hL (Subgroup.mem_inf.1 hx').1)
    refine ⟨T, hTne, hT2, hTL, ?_⟩
    calc Bb = Bb ⊓ (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q) :=
          le_antisymm (fun x hx' => Subgroup.mem_inf.2 ⟨hx', hL hx'⟩) inf_le_left
      _ = (Bb ⊓ (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) ⊔
            (Bb ⊓ Subgroup.normalizer (T : Set ↥(orthDerived Q))) := (sup_eq_left.2 hle).symm

theorem exists_twoGroup_decomp_of_full_rank (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {Bb : Subgroup ↥(orthDerived Q)} (hBb : IsElemAbelian p Bb)
    (hcard : p ^ n ≤ Nat.card Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb) (hd1 : d ≠ 1)
    {L : Subgroup ↥(orthDerived Q)}
    (hL : IsComponentOf L (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))))
    (hcd : Bb ⊓ Subgroup.centralizer (L : Set ↥(orthDerived Q)) = Subgroup.zpowers d) :
    ∃ T : Subgroup ↥(orthDerived Q), T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ L ∧
      Bb = (Bb ⊓ L) ⊔ (Bb ⊓ Subgroup.normalizer (T : Set ↥(orthDerived Q))) := by
  obtain ⟨-, U, e, hF⟩ := exists_planeFrame_of_pow_le_card hQ hdim hp hp2 hpq hBb hcard
  rcases standard_dichotomy_full hQ hdim hn hp hp2 hpq hF hd hd1 hL hcd with
    ⟨j, hdj, hfs, hLeq⟩ | ⟨h, hh, hh1, hUh, hLeq⟩
  · subst hLeq
    exact exists_twoGroup_decomp_weightOne hQ hdim hn hp hp2 hpq hF hd hd1 hdj hfs
  · subst hLeq
    exact exists_twoGroup_decomp_fullSupport hQ hdim (by omega) hp hp2 hpq hF hd hd1 hh hh1 hUh

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
