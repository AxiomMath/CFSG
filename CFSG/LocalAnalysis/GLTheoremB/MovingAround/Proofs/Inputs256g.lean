module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256e2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311d2
public import CFSG.ClassicalGroups.UnitaryFlag.GramSURootGen
public import CFSG.LieType.SeitzGeneration.UnitaryNonabPlane

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256g

open CFSG.Open CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c (UniPlaneGen uniPlaneClosure
  mem_uniPlaneClosure)

section RSub

variable {S : Type*} [Group S] [Finite S]

theorem not_dvd_card_of_forall_pow {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    {H : Subgroup S} (hH : ∀ s ∈ H, ∃ m : ℕ, s ^ (r ^ m) = 1) : ¬ p ∣ Nat.card H := by
  intro hd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨m, hm⟩ := hH g g.2
  have h1 : orderOf g ∣ r ^ m := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hm))
  rw [hg] at h1
  exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow h1))

theorem uniPlaneGen_of_rSubgroups {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (𝓗 : Set (Subgroup S)) (hr' : ∀ H ∈ 𝓗, ∀ s ∈ H, ∃ m : ℕ, s ^ (r ^ m) = 1)
    (hstab : ∀ H ∈ 𝓗, ∀ e ∈ E, ∀ s ∈ H, e s ∈ H) (hgen : ⨆ H ∈ 𝓗, H = ⊤) :
    UniPlaneGen r E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CFSG.IsElementaryAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mpr hE
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.ne_zero)
  rw [UniPlaneGen, eq_top_iff, ← hgen]
  refine iSup₂_le fun H hH => ?_
  have hpH : ¬ p ∣ Nat.card H := not_dvd_card_of_forall_pow hp hr hpr (hr' H hH)
  letI : MulDistribMulAction E H :=
    { smul := fun e s => ⟨(e : MulAut S) s, hstab H hH e e.2 s s.2⟩
      one_smul := fun s => Subtype.ext rfl
      mul_smul := fun e e' s => Subtype.ext rfl
      smul_mul := fun e s t => Subtype.ext (map_mul (e : MulAut S) (s : S) t)
      smul_one := fun e => Subtype.ext (map_one (e : MulAut S)) }
  have hgen' := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := E) (H := H)
    (by rw [hc]) hpH
  intro s hs
  have hmem : (⟨s, hs⟩ : H) ∈ ⨆ (a : E) (_ : a ≠ 1),
      CFSG.fixedPointSubgroup (Subgroup.zpowers a) H := by
    rw [hgen']; exact Subgroup.mem_top _
  have hle : (⨆ (a : E) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) H) ≤
      (uniPlaneClosure r E).comap H.subtype := by
    refine iSup₂_le fun a ha => fun t ht => ?_
    have hfix : a • t = t := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a t).1 ht
    have hfix' : (a : MulAut S) (t : S) = t := congrArg Subtype.val hfix
    obtain ⟨m, hm⟩ := hr' H hH t t.2
    exact mem_uniPlaneClosure a.2 (fun h1 => ha (Subtype.ext h1)) hfix' hm
  exact hle hmem

end RSub

section Model

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem sUid_eq_gramSU (h : UnitaryFieldData ℓ f K) :
    SUid (unitaryInvolution K ℓ f) n = gramSU h (idGram K n) :=
  (SUid_eq_statedSU h.card_eq_sq n).trans (unitarySU_eq_gramSU h n)

@[expose] noncomputable def suP (h : UnitaryFieldData ℓ f K) :
    SUid (unitaryInvolution K ℓ f) n →* primeFormP h (idGram K n) :=
  (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).comp
    (MulEquiv.subgroupCongr (sUid_eq_gramSU (n := n) h)).toMonoidHom

theorem suP_apply (h : UnitaryFieldData ℓ f K) (g : SUid (unitaryInvolution K ℓ f) n) :
    suP h g = ((⟨(g : GL (Fin n) K), (sUid_eq_gramSU h) ▸ g.2⟩ : gramSU h (idGram K n)) :
      primeFormP h (idGram K n)) := rfl

theorem suP_surjective (h : UnitaryFieldData ℓ f K) : Function.Surjective (suP (n := n) h) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  refine ⟨⟨(g : GL (Fin n) K), (sUid_eq_gramSU h).symm ▸ g.2⟩, ?_⟩
  rfl

theorem primeFormConjHom_suP (h : UnitaryFieldData ℓ f K) (A : primeFormUnitary h (idGram K n))
    (g : SUid (unitaryInvolution K ℓ f) n) (g' : SUid (unitaryInvolution K ℓ f) n)
    (hg' : (g' : GL (Fin n) K) = A * g * (A : GL (Fin n) K)⁻¹) :
    primeFormConjHom h (idGram K n) A (suP h g) = suP h g' := by
  rw [suP_apply, suP_apply, primeFormConjHom_mk]
  congr 1
  exact Subtype.ext hg'.symm

theorem mem_comap_of_rcent (h : UnitaryFieldData ℓ f K)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (A : primeFormUnitary h (idGram K n))
    (hAE : primeFormConjHom h (idGram K n) A ∈ E) (hA1 : primeFormConjHom h (idGram K n) A ≠ 1)
    (g : SUid (unitaryInvolution K ℓ f) n)
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hgr : g ^ ringChar K = 1) :
    g ∈ (uniPlaneClosure ℓ E).comap (suP h) := by
  rw [Subgroup.mem_comap]
  have hfix : primeFormConjHom h (idGram K n) A (suP h g) = suP h g := by
    refine primeFormConjHom_suP h A g g ?_
    have h1 : (g : GL (Fin n) K) * A = A * g := Units.ext (by simpa using hg)
    rw [← h1, mul_inv_cancel_right]
  have hgℓ : g ^ ℓ = 1 := by rwa [ringChar.eq K ℓ] at hgr
  refine mem_uniPlaneClosure hAE hA1 hfix (n := 1) ?_
  rw [pow_one, ← map_pow, hgℓ, map_one]

theorem uniPlaneGen_of_comap_eq_top (h : UnitaryFieldData ℓ f K)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (uniPlaneClosure ℓ E).comap (suP h) = ⊤) : UniPlaneGen ℓ E := by
  rw [UniPlaneGen, eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := suP_surjective h x
  have : g ∈ (uniPlaneClosure ℓ E).comap (suP h) := hH ▸ Subgroup.mem_top g
  exact this

end Model

section RCentDef

open CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {n : ℕ}

@[expose] def RCent {σ : K ≃+* K} (H : Subgroup (SUid σ n)) (L : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ g : SUid σ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * L =
    L * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ^ ringChar K = 1 → g ∈ H

end RCentDef

section Toral

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.CTP CFSG.LieType.BorelTits

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem uniClosure_unitarySU_of_dvd_add_one_gu (h : UnitaryFieldData ℓ f K)
    (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2)
    (G : Subgroup (primeFormUnitary h (idGram K (n + 1))))
    (hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) (hexp : ∀ x ∈ G, x ^ p = 1)
    (hcard : Nat.card G = p ^ 2) :
    Subgroup.closure {g : unitarySU ℓ f K (n + 1) |
      ∃ x ∈ G, x ≠ 1 ∧ (g : GL (Fin (n + 1)) K) * (x : GL (Fin (n + 1)) K) =
        (x : GL (Fin (n + 1)) K) * (g : GL (Fin (n + 1)) K) ∧ g ^ ringChar K = 1} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h hp hpq G hcomm hexp
  let Pg : GL (Fin (n + 1)) K := (P : GL (Fin (n + 1)) K)
  let Dg : G → GL (Fin (n + 1)) K := fun x =>
    Pg⁻¹ * ((x : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) * Pg
  have hdiag : ∀ x : G,
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K).IsDiag :=
    fun x => hP _ x.2
  have hDmul : ∀ x y : G, Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin (n + 1) → G →* K := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiag x) c }
  have hnz : ∀ (x : G) (c : Fin (n + 1)),
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c ≠ 0 := by
    intro x c
    have h1 : (((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
        (((Dg x)⁻¹ : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiag x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hexpE : ∀ x : G, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hcommblock : ∀ i : Fin n, ∃ x : G, x ≠ 1 ∧ ∀ A : Matrix (Fin 2) (Fin 2) K,
      blockMat (n + 1) i A * ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
          blockMat (n + 1) i A := by
    intro i
    obtain ⟨x, hx1, -, hxeq⟩ := exists_ne_one_hom_eq hp hexpE hcard (χ i.castSucc) (χ i.succ)
    refine ⟨x, hx1, fun A => ?_⟩
    have hD : ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        Matrix.diagonal (fun c => ((Dg x : GL (Fin (n + 1)) K) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c) := ((hdiag x).diagonal_diag).symm
    rw [hD]
    exact blockMat_mul_diagonal_comm (by omega) _ (hnz x) i.castSucc i.succ (by simp) (by simp)
      hxeq A
  let φ := conjSU h P
  set S := Subgroup.closure {g : unitarySU ℓ f K (n + 1) |
      ∃ x ∈ G, x ≠ 1 ∧ (g : GL (Fin (n + 1)) K) * (x : GL (Fin (n + 1)) K) =
        (x : GL (Fin (n + 1)) K) * (g : GL (Fin (n + 1)) K) ∧ g ^ ringChar K = 1} with hS
  have hblock : ∀ (i : Fin n) (y : unitarySU ℓ f K (n + 1)) (A : Matrix (Fin 2) (Fin 2) K),
      (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) = blockMat (n + 1) i A → y ^ ringChar K = 1 →
        φ y ∈ S := by
    intro i y A hA hyr
    obtain ⟨x, hx1, hxc⟩ := hcommblock i
    refine Subgroup.subset_closure ⟨(x : primeFormUnitary h (idGram K (n + 1))), x.2,
      fun h1 => hx1 (Subtype.ext h1), ?_, by rw [← map_pow, hyr, map_one]⟩
    have hYD : ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x =
        Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) := by
      apply Units.ext
      simp only [Units.val_mul]
      rw [hA]
      exact hxc A
    have hxeq : ((x : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) =
        Pg * Dg x * Pg⁻¹ := by
      simp [Dg, mul_assoc]
    show Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
        ((x : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) =
      ((x : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) *
        (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹)
    rw [hxeq]
    calc Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
          (Pg * Dg x * Pg⁻¹)
        = Pg * (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x) * Pg⁻¹ := by group
      _ = Pg * (Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)) * Pg⁻¹ := by
        rw [hYD]
      _ = Pg * Dg x * Pg⁻¹ *
          (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹) := by group
  let ε : Su K ℓ f (n + 1) ≃* unitarySU ℓ f K (n + 1) :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq (n + 1))
  let ι : Fin n → (Su K ℓ f 2 →* unitarySU ℓ f K (n + 1)) := fun i =>
    ε.toMonoidHom.comp (blockEmb2 K ℓ f n i)
  have hgen : ⨆ i : Fin n, (ι i).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := ℓ) (f := f) h.card_eq_sq hq n
    have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
    simpa [ι, MonoidHom.range_comp] using h2
  have hsu2 := Inputs2311d.closure_pow_ringChar_su_two (K := K) (p := ℓ) (f := f) h.card_eq_sq
  have hle' : (⨆ i : Fin n, (ι i).range).map φ.toMonoidHom ≤ S := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rw [MonoidHom.range_eq_map, ← hsu2, MonoidHom.map_closure, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine hblock i _ ((a : Su K ℓ f 2) : GL (Fin 2) K) rfl ?_
    rw [← map_pow, ha, map_one]
  rw [hgen, Subgroup.map_top_of_surjective _ φ.surjective] at hle'
  exact top_unique hle'

theorem eq_top_of_abelian_pth_r [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) (hn : 2 ≤ n) {x y : GL (Fin n) K}
    (hx : x ∈ primeFormUnitary h (idGram K n)) (hy : y ∈ primeFormUnitary h (idGram K n))
    (hxy : x * y = y * x) (hx1 : x ^ p = 1) (hy1 : y ^ p = 1)
    (hind : ∀ a b : ℕ, x ^ a * y ^ b = 1 → p ∣ a ∧ p ∣ b)
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) n)}
    (hH : ∀ a b : ℕ, ¬ (p ∣ a ∧ p ∣ b) →
      RCent H ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : H = ⊤ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  classical
  let X : primeFormUnitary h (idGram K (m + 1)) := ⟨x, hx⟩
  let Y : primeFormUnitary h (idGram K (m + 1)) := ⟨y, hy⟩
  have hXY : Commute X Y := Subtype.ext hxy
  have hX : X ^ p = 1 := Subtype.ext (by simpa [X] using hx1)
  have hY : Y ^ p = 1 := Subtype.ext (by simpa [Y] using hy1)
  have hind' : ∀ a b : ℕ, X ^ a * Y ^ b = 1 → p ∣ a ∧ p ∣ b := by
    intro a b hab
    apply hind a b
    have := congrArg Subtype.val hab
    simpa [X, Y] using this
  have htop := uniClosure_unitarySU_of_dvd_add_one_gu h hp hpq hq
    (commPairSubgroupP hp hXY hX hY) (commPairSubgroupP_comm hp hXY hX hY)
    (commPairSubgroupP_exp hp hXY hX hY) (card_commPairSubgroupP hp hXY hX hY hind')
  let ε : SUid (unitaryInvolution K ℓ f) (m + 1) ≃* unitarySU ℓ f K (m + 1) :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq (m + 1))
  let Hc : Subgroup (unitarySU ℓ f K (m + 1)) := H.comap ε.symm.toMonoidHom
  have hsub : ∀ g : unitarySU ℓ f K (m + 1),
      (∃ x' ∈ commPairSubgroupP hp hXY hX hY, x' ≠ 1 ∧
        (g : GL (Fin (m + 1)) K) * (x' : GL (Fin (m + 1)) K) =
          (x' : GL (Fin (m + 1)) K) * (g : GL (Fin (m + 1)) K) ∧ g ^ ringChar K = 1) → g ∈ Hc := by
    rintro g ⟨x', hx'G, hx'1, hcg, hgr⟩
    obtain ⟨a, b, hab⟩ := hx'G
    have hnd : ¬ (p ∣ a ∧ p ∣ b) := by
      rintro ⟨ha, hb⟩
      apply hx'1
      rw [hab, pow_eq_one_of_dvd_pow_eq_one_p hX ha, pow_eq_one_of_dvd_pow_eq_one_p hY hb, one_mul]
    have hx'GL : ((x' : primeFormUnitary h (idGram K (m + 1))) : GL (Fin (m + 1)) K) =
        x ^ a * y ^ b := by
      rw [hab]; simp [X, Y]
    have hcomm' : ((g : GL (Fin (m + 1)) K)) * (x ^ a * y ^ b) =
        (x ^ a * y ^ b) * ((g : GL (Fin (m + 1)) K)) := by
      rw [← hx'GL]; exact hcg
    have hmat : ((g : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        ((x ^ a * y ^ b : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        ((x ^ a * y ^ b : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
          ((g : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm']
    have hgr' : (ε.symm g) ^ ringChar K = 1 := by rw [← map_pow, hgr, map_one]
    show ε.symm g ∈ H
    exact hH a b hnd (ε.symm g) hmat hgr'
  have hHc : Hc = ⊤ := by
    rw [eq_top_iff, ← htop, Subgroup.closure_le]
    intro g hg
    exact hsub g hg
  rw [eq_top_iff]
  intro g _
  have hgc : ε g ∈ Hc := hHc ▸ Subgroup.mem_top _
  simpa [Hc] using hgc

end Toral

section MixR

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.LieType.SeitzGeneration.Mixing

variable {ℓ f : ℕ} {K : Type*} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type*}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem exists_mixing_element_of_selfDual_r (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hx : x ∈ sesqUnitaryGroup B) (hsq : Squarefree (minpoly K (x : Module.End K V)))
    {a : primaryFactors (x : Module.End K V)} (hself : dualPoly hK.bar (a : K[X]) = a)
    (hdeg : 2 ≤ (a : K[X]).natDegree) {S₁ S₂ : Submodule K V}
    (hS₁ : ∀ s ∈ S₁, (x : Module.End K V) s ∈ S₁) (hS₂ : ∀ s ∈ S₂, (x : Module.End K V) s ∈ S₂)
    (horth : ∀ s ∈ S₁, ∀ t ∈ S₂, B s t = 0) (hnd₁ : (B.domRestrict₁₂ S₁ S₁).SeparatingLeft)
    (hnd₂ : (B.domRestrict₁₂ S₂ S₂).SeparatingLeft)
    (hKI : ∀ w ∈ S₂, w ≠ 0 → ∃ w₀ ∈ S₂, B w₀ w₀ = 0 ∧ B w w₀ ≠ 0)
    {u w : V} (hu : u ∈ S₁) (hua : u ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hu0 : u ≠ 0) (hw : w ∈ S₂) (hwa : w ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hw0 : w ≠ 0) :
    ∃ g : LinearMap.GeneralLinearGroup K V, g ∈ unitaryCentralizer B x ∧
      LinearMap.det (g : Module.End K V) = 1 ∧ g ^ ringChar K = 1 ∧ ∃ w₀ ∈ S₂, w₀ ≠ 0 ∧ B w₀ w₀ = 0 ∧
        ∃ u'' ∈ S₁, ∃ w'' ∈ S₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧ (g : Module.End K V) w₀ = u'' + w'' := by
  classical
  have := hK.finite
  have H : UnitaryPrimaryData hK.bar B x := ⟨hK.bar_bar, hB, hBl, hx, hsq⟩
  obtain ⟨hodd, hE, hbarE, hadj, Hf, hsymmF, hsep, htrace, -, φ, hφ1, hφdet⟩ :=
    selfDualPrimaryBlock H a hself
  have haX : (a : K[X]) ∈ primaryFactors (x : Module.End K V) := a.2
  have hsymm : ∀ s t : primaryComponent (x : Module.End K V) (a : K[X]),
      hE.bar (Hf s t) = Hf t s := fun s t => hsymmF.eq s t
  have hbarne : ∃ s : AdjoinRoot (a : K[X]), hE.bar s ≠ s := hE.exists_bar_ne
  have hεa : primaryProjection (x : Module.End K V) (a : K[X]) =
      primaryProjection (x : Module.End K V) (dualPoly hK.bar (a : K[X])) := by
    rw [hself]
  have hεadj : ∀ v t : V, B (primaryProjection (x : Module.End K V) (a : K[X]) v) t =
      B v (primaryProjection (x : Module.End K V) (a : K[X]) t) := by
    intro v t
    rw [H.adj_spec, adj_primaryProjection H haX, ← hεa]
  have hBtr : ∀ s t : primaryComponent (x : Module.End K V) (a : K[X]),
      B (s : V) (t : V) = Algebra.trace K (AdjoinRoot (a : K[X])) (Hf s t) := fun s t => by
    simpa using (htrace s t 1).symm
  have hHorth : ∀ s t : primaryComponent (x : Module.End K V) (a : K[X]), (s : V) ∈ S₁ →
      (t : V) ∈ S₂ → Hf s t = 0 := by
    intro s t hs ht
    refine eq_zero_of_trace_mul_eq_zero (a : K[X]) (Hf s t) fun c => ?_
    rw [htrace s t c]
    exact horth _ hs _ (coe_smul_mem_of_stable hS₂ c t ht)
  have hex : ∀ S : Submodule K V, (∀ s ∈ S, (x : Module.End K V) s ∈ S) →
      (B.domRestrict₁₂ S S).SeparatingLeft →
      ∀ v : primaryComponent (x : Module.End K V) (a : K[X]), (v : V) ∈ S → v ≠ 0 →
        ∃ z : primaryComponent (x : Module.End K V) (a : K[X]), (z : V) ∈ S ∧ Hf z z ≠ 0 := by
    intro S hS hnd v hvS hv0
    obtain ⟨s, hs, hBs⟩ : ∃ s ∈ S, B (v : V) s ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hv0 (Subtype.ext ?_)
      have := hnd ⟨(v : V), hvS⟩ (fun y => by
        rw [LinearMap.domRestrict₁₂_apply]
        exact hcon y y.2)
      have h0 : ((⟨(v : V), hvS⟩ : S) : V) = ((0 : S) : V) := congrArg Subtype.val this
      simpa using h0
    set y₁ : primaryComponent (x : Module.End K V) (a : K[X]) :=
      ⟨primaryProjection (x : Module.End K V) (a : K[X]) s,
        primaryProjection_mem hsq haX s⟩ with hy₁
    have hy₁S : (y₁ : V) ∈ S := KCUnitaryMixing.aeval_apply_mem hS _ hs
    have h1 : B (y₁ : V) (v : V) = B s (v : V) := by
      rw [hy₁]
      change B (primaryProjection (x : Module.End K V) (a : K[X]) s) (v : V) = _
      rw [hεadj, primaryProjection_of_mem hsq haX v.2]
    have h2 : B (v : V) (y₁ : V) = B (v : V) s := by
      rw [← hB.eq, h1, hB.eq]
    have hz : Hf v y₁ ≠ 0 := by
      intro h0
      apply hBs
      rw [← h2, hBtr, h0, map_zero]
    exact exists_anisotropic_of_pairing Hf hsymm hbarne
      { carrier := {z | (z : V) ∈ S}
        add_mem' := fun {a b} ha hb => S.add_mem ha hb
        zero_mem' := S.zero_mem
        smul_mem' := fun c z hz => coe_smul_mem_of_stable hS c z hz } hvS hy₁S hz
  obtain ⟨z₁, hz₁S, hz₁⟩ := hex S₁ hS₁ hnd₁ ⟨u, hua⟩ hu
    (fun h => hu0 (by simpa using congrArg Subtype.val h))
  obtain ⟨z₂, hz₂S, hz₂⟩ := hex S₂ hS₂ hnd₂ ⟨w, hwa⟩ hw
    (fun h => hw0 (by simpa using congrArg Subtype.val h))
  have hz₁0 : z₁ ≠ 0 := fun h => hz₁ (by rw [h]; simp)
  have hz₂0 : z₂ ≠ 0 := fun h => hz₂ (by rw [h]; simp)
  have ht₁ : hE.bar (Hf z₁ z₁) = Hf z₁ z₁ := hsymm z₁ z₁
  have ht₂ : hE.bar (Hf z₂ z₂) = Hf z₂ z₂ := hsymm z₂ z₂
  have hmem : (-(Hf z₂ z₂) / Hf z₁ z₁ : AdjoinRoot (a : K[X])) ∈ hE.fixedField := by
    rw [hE.mem_fixedField, map_div₀, map_neg, ht₁, ht₂]
  obtain ⟨lam, hlam⟩ := hE.normHom_surjective ⟨_, hmem⟩
  have hlam' : lam * hE.bar lam = -(Hf z₂ z₂) / Hf z₁ z₁ := by
    have := congrArg Subtype.val hlam
    simpa [UnitaryFieldData.norm] using this
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hlam'
    exact (div_ne_zero (neg_ne_zero.mpr hz₂) hz₁) hlam'.symm
  have hnorm : Hf (lam • z₁) (lam • z₁) = -(Hf z₂ z₂) := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc lam * (hE.bar lam * Hf z₁ z₁) = (lam * hE.bar lam) * Hf z₁ z₁ := by ring
      _ = -(Hf z₂ z₂) := by rw [hlam']; field_simp
  have hlz₁S : ((lam • z₁ : primaryComponent (x : Module.End K V) (a : K[X])) : V) ∈ S₁ :=
    coe_smul_mem_of_stable hS₁ lam z₁ hz₁S
  have hH12 : Hf (lam • z₁) z₂ = 0 := hHorth _ _ hlz₁S hz₂S
  have hH21 : Hf z₂ (lam • z₁) = 0 := by
    rw [← hsymm, hH12, map_zero]
  have hee : Hf (lam • z₁ + z₂) (lam • z₁ + z₂) = 0 := by
    simp only [map_add, LinearMap.add_apply, hnorm, hH12, hH21]
    ring
  have hz₂V : (z₂ : V) ≠ 0 := fun h => hz₂0 (Subtype.ext h)
  obtain ⟨w₀, hw₀S, hw₀i, hBw₀⟩ := hKI (z₂ : V) hz₂S hz₂V
  set ω : primaryComponent (x : Module.End K V) (a : K[X]) :=
    ⟨primaryProjection (x : Module.End K V) (a : K[X]) w₀, primaryProjection_mem hsq haX w₀⟩
    with hω
  have hωS : (ω : V) ∈ S₂ := KCUnitaryMixing.aeval_apply_mem hS₂ _ hw₀S
  have hBω : B (z₂ : V) (ω : V) = B (z₂ : V) w₀ := by
    rw [hω]
    change B (z₂ : V) (primaryProjection (x : Module.End K V) (a : K[X]) w₀) = _
    rw [← hεadj, primaryProjection_of_mem hsq haX z₂.2]
  have hh₀ : Hf z₂ ω ≠ 0 := by
    intro h0
    apply hBw₀
    rw [← hBω, hBtr, h0, map_zero]
  have hH1ω : Hf (lam • z₁) ω = 0 := hHorth _ _ hlz₁S hωS
  have hHeω : Hf (lam • z₁ + z₂) ω = Hf z₂ ω := by
    rw [map_add, LinearMap.add_apply, hH1ω, zero_add]
  have hc : ∃ c₁ c₂ : AdjoinRoot (a : K[X]), hE.bar c₁ = -c₁ ∧ hE.bar c₂ = -c₂ ∧ c₁ ≠ 0 ∧
      c₂ ≠ 0 ∧ c₁ ≠ c₂ := by
    have := hE.finite
    have hq : 3 ≤ ℓ ^ (f * (a : K[X]).natDegree) := by
      have hℓ2 := hK.prime.two_le
      have hf1 := hK.one_le
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ2 2
        _ ≤ ℓ ^ (f * (a : K[X]).natDegree) :=
          Nat.pow_le_pow_right (by omega) (by nlinarith)
    have hcard : 2 < (hE.traceZero : Set (AdjoinRoot (a : K[X]))).ncard := by
      rw [← Nat.card_coe_set_eq]
      change 2 < Nat.card hE.traceZero
      rw [hE.card_traceZero]
      omega
    obtain ⟨c₁, c₂, c₃, h₁, h₂, h₃, h12, h13, h23⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).1 hcard
    have hbar : ∀ c ∈ hE.traceZero, hE.bar c = -c := fun c hc => by
      have := hE.mem_traceZero.mp hc
      rw [UnitaryFieldData.trace] at this
      linear_combination this
    by_cases h0₁ : c₁ = 0
    · exact ⟨c₂, c₃, hbar _ h₂, hbar _ h₃, fun h => h12 (h0₁.trans h.symm),
        fun h => h13 (h0₁.trans h.symm), h23⟩
    · by_cases h0₂ : c₂ = 0
      · exact ⟨c₁, c₃, hbar _ h₁, hbar _ h₃, h0₁, fun h => h23 (h0₂.trans h.symm), h13⟩
      · exact ⟨c₁, c₂, hbar _ h₁, hbar _ h₂, h0₁, h0₂, h12⟩
  obtain ⟨c₁, c₂, hc₁, hc₂, hc₁0, hc₂0, hc12⟩ := hc
  have hw₀0 : w₀ ≠ 0 := by
    rintro rfl
    exact hBw₀ (by simp)
  have hmain : ∀ c : AdjoinRoot (a : K[X]), hE.bar c = -c → ∃ g : LinearMap.GeneralLinearGroup K V,
      g ∈ unitaryCentralizer B x ∧ LinearMap.det (g : Module.End K V) = 1 ∧ g ^ ringChar K = 1 ∧
        (g : Module.End K V) w₀ = w₀ +
          (((c * Hf z₂ ω) • (lam • z₁ + z₂) : primaryComponent (x : Module.End K V) (a : K[X])) :
            V) := by
    intro c hc
    have hfv : (c • Hf (lam • z₁ + z₂)) (lam • z₁ + z₂) = 0 := by
      rw [LinearMap.smul_apply, hee, smul_zero]
    let γ : primaryComponent (x : Module.End K V) (a : K[X]) ≃ₗ[AdjoinRoot (a : K[X])]
        primaryComponent (x : Module.End K V) (a : K[X]) := LinearEquiv.transvection hfv
    have hγapply : ∀ y, γ y = y + (c * Hf (lam • z₁ + z₂) y) • (lam • z₁ + z₂) := fun y => rfl
    have hγiso : ∀ y z, Hf (γ y) (γ z) = Hf y z := fun y z => by
      rw [hγapply, hγapply]
      exact transvection_isometry Hf hsymm hee hc y z
    let γg : blockGL (x : Module.End K V) (a : K[X]) :=
      LinearMap.GeneralLinearGroup.ofLinearEquiv γ
    have hγmem : γg ∈ sesqUnitaryGroup Hf := fun y z => hγiso y z
    have hγdet : LinearMap.det ((γg : blockGL (x : Module.End K V) (a : K[X])) :
        Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) =
        1 := by
      have h1 := LinearEquiv.transvection.det_eq_one hfv
      rw [← Units.val_inj, LinearEquiv.coe_det, Units.val_one] at h1
      exact h1
    have hγspec : γg ∈ sesqSpecialUnitaryGroup Hf := mem_sesqSpecialUnitaryGroup.mpr ⟨hγmem, hγdet⟩
    set g := φ.symm ⟨γg, hγmem⟩ with hg
    have hcast : ((ringChar K : ℕ) : AdjoinRoot (a : K[X])) = 0 := by
      rw [← map_natCast (algebraMap K (AdjoinRoot (a : K[X]))), ringChar.Nat.cast_ringChar, map_zero]
    have hγr : (⟨γg, hγmem⟩ : sesqUnitaryGroup Hf) ^ ringChar K = 1 :=
      Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d.ofLinearEquiv_transvection_pow_eq_one
          hfv hcast)
    have hgr : g ^ ringChar K = 1 := by rw [hg, ← map_pow, hγr, map_one]
    refine ⟨(g : LinearMap.GeneralLinearGroup K V), g.2.1, hφdet g ?_, ?_, ?_⟩
    · rw [hg, MulEquiv.apply_symm_apply]
      exact hγspec
    · rw [← SubgroupClass.coe_pow, hgr, OneMemClass.coe_one]
    · have h1 := apply_of_supported hsq haX g.2 w₀
      have h3 := hφ1 g (primaryProjection (x : Module.End K V) (a : K[X]) w₀)
        (primaryProjection_mem hsq haX w₀)
      have h4 : φ g = ⟨γg, hγmem⟩ := by rw [hg, MulEquiv.apply_symm_apply]
      rw [h4] at h3
      have h5 : ((γ ω : primaryComponent (x : Module.End K V) (a : K[X])) : V) =
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
            (primaryProjection (x : Module.End K V) (a : K[X]) w₀) := h3
      rw [h1, ← h5, hγapply, hHeω]
      change w₀ + (((ω + (c * Hf z₂ ω) • (lam • z₁ + z₂) :
        primaryComponent (x : Module.End K V) (a : K[X])) : V) - (ω : V)) = _
      rw [Submodule.coe_add]
      abel
  have hpart : ∀ c : AdjoinRoot (a : K[X]), c ≠ 0 →
      (((c * Hf z₂ ω) • (lam • z₁) : primaryComponent (x : Module.End K V) (a : K[X])) : V) ∈ S₁ ∧
      (((c * Hf z₂ ω) • (lam • z₁) : primaryComponent (x : Module.End K V) (a : K[X])) : V) ≠ 0 ∧
      (((c * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) : V) ∈ S₂ := by
    intro c hc0
    refine ⟨coe_smul_mem_of_stable hS₁ _ _ hlz₁S, fun h => ?_,
      coe_smul_mem_of_stable hS₂ _ _ hz₂S⟩
    exact smul_ne_zero (mul_ne_zero hc0 hh₀) (smul_ne_zero hlam0 hz₁0) (Subtype.ext h)
  have hsplit : ∀ c : AdjoinRoot (a : K[X]),
      (((c * Hf z₂ ω) • (lam • z₁ + z₂) : primaryComponent (x : Module.End K V) (a : K[X])) : V) =
        (((c * Hf z₂ ω) • (lam • z₁) : primaryComponent (x : Module.End K V) (a : K[X])) : V) +
        (((c * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) : V) := by
    intro c
    rw [smul_add, Submodule.coe_add]
  have hfin : ∀ c : AdjoinRoot (a : K[X]), hE.bar c = -c → c ≠ 0 →
      w₀ + (((c * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) : V) ≠ 0 →
      ∃ g : LinearMap.GeneralLinearGroup K V, g ∈ unitaryCentralizer B x ∧
        LinearMap.det (g : Module.End K V) = 1 ∧ g ^ ringChar K = 1 ∧ ∃ w₀ ∈ S₂, w₀ ≠ 0 ∧ B w₀ w₀ = 0 ∧
          ∃ u'' ∈ S₁, ∃ w'' ∈ S₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧
            (g : Module.End K V) w₀ = u'' + w'' := by
    intro c hc hc0 hne
    obtain ⟨g, hg1, hg2, hgr, hg3⟩ := hmain c hc
    obtain ⟨hp1, hp2, hp3⟩ := hpart c hc0
    refine ⟨g, hg1, hg2, hgr, w₀, hw₀S, hw₀0, hw₀i, _, hp1, w₀ + _, S₂.add_mem hw₀S hp3, hp2, hne, ?_⟩
    rw [hg3, hsplit]
    abel
  by_cases h1 : w₀ + (((c₁ * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) :
      V) = 0
  · by_cases h2 : w₀ + (((c₂ * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) :
        V) = 0
    · exfalso
      have e1 := eq_neg_of_add_eq_zero_right h1
      have e2 := eq_neg_of_add_eq_zero_right h2
      have h0 : (((c₁ - c₂) * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) =
          0 := by
        apply Subtype.ext
        rw [sub_mul, sub_smul, Submodule.coe_sub, e1, e2, sub_self]
        rfl
      exact smul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hc12) hh₀) hz₂0 h0
    · exact hfin c₂ hc₂ hc₂0 h2
  · exact hfin c₁ hc₁ hc₁0 h1

end MixR

section NonPthR

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.LieType.SeitzGeneration.NonPth

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem isCenter_of_eigen_matrix_r {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c)
    {H : Subgroup (SUid σ n)} {Y : Matrix (Fin n) (Fin n) K} (hH : RCent H Y)
    (hY : ∀ u w, herm σ (Y *ᵥ u) (Y *ᵥ w) = herm σ u w)
    {v : Fin n → K} (hv : herm σ v v = 0) {l : K} (hl : σ l * l = 1) (hYv : Y *ᵥ v = l • v) :
    Centers.IsCenter H v := by
  refine ⟨hv, fun c hc => ⟨tv hσ hv hc, hH _ ?_ (Inputs2311d.tv_pow_ringChar hσ hv hc),
    tv_smul hσ hv hc⟩⟩
  have hT : ∀ w, ((tv hσ hv hc : SUid σ n) : GL (Fin n) K) *ᵥ w = w + (c * herm σ v w) • v :=
    fun w => tv_smul hσ hv hc w
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  set u : Fin n → K := Pi.single i 1
  have h1 : herm σ v (Y *ᵥ u) = l * herm σ v u := by
    have h := hY v u
    rw [hYv, herm_smul_left] at h
    calc herm σ v (Y *ᵥ u) = l * (σ l * herm σ v (Y *ᵥ u)) := by
          linear_combination (-(herm σ v (Y *ᵥ u))) * hl
      _ = l * herm σ v u := by rw [h]
  rw [hT, hT, Matrix.mulVec_add, Matrix.mulVec_smul, hYv, h1, smul_smul]
  congr 2
  ring

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem exists_mixing_of_nonpth_r (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    {x : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n)) {α : K}
    (hx3 : ((x ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hcx : ¬ ∃ μ : K, μ ^ p = α) {S₁ S₂ : Submodule K (Fin n → K)}
    (hS₁ : ∀ s ∈ S₁, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ s ∈ S₁)
    (hS₂ : ∀ s ∈ S₂, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ s ∈ S₂)
    (horth : ∀ s ∈ S₁, ∀ t ∈ S₂, herm (unitaryInvolution K ℓ f) s t = 0)
    (hnd₁ : ((idForm h n).domRestrict₁₂ S₁ S₁).SeparatingLeft)
    (hnd₂ : ((idForm h n).domRestrict₁₂ S₂ S₂).SeparatingLeft)
    (hKI : ∀ w ∈ S₂, w ≠ 0 → ∃ w₀ ∈ S₂, herm (unitaryInvolution K ℓ f) w₀ w₀ = 0 ∧
      herm (unitaryInvolution K ℓ f) w w₀ ≠ 0)
    {u w : Fin n → K} (hu : u ∈ S₁) (hu0 : u ≠ 0) (hw : w ∈ S₂) (hw0 : w ≠ 0) :
    ∃ g : SUid (unitaryInvolution K ℓ f) n,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
        (x : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      g ^ ringChar K = 1 ∧
      ∃ w₀ ∈ S₂, w₀ ≠ 0 ∧ herm (unitaryInvolution K ℓ f) w₀ w₀ = 0 ∧
        ∃ u'' ∈ S₁, ∃ w'' ∈ S₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧ g • w₀ = u'' + w'' := by
  classical
  set σ := unitaryInvolution K ℓ f with hσdef
  set B := idForm h n with hBdef
  have hBsymm : B.IsSymm := idForm_isSymm h n
  set xl : LinearMap.GeneralLinearGroup K (Fin n → K) := Matrix.GeneralLinearGroup.toLin x
    with hxl
  have hxmem : xl ∈ sesqUnitaryGroup B := (toLin_mem_sesqUnitaryGroup_iff x).mpr hx
  have hxend : (xl : Module.End K (Fin n → K)) = Matrix.toLin' (x : Matrix (Fin n) (Fin n) K) :=
    rfl
  have hxlp : (xl : Module.End K (Fin n → K)) ^ p =
      algebraMap K (Module.End K (Fin n → K)) α := by
    have h1 : ((x : Matrix (Fin n) (Fin n) K)) ^ p = α • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hx3
    have h2 := congrArg Matrix.toLinAlgEquiv' h1
    rw [map_pow, map_smul, map_one] at h2
    rw [hxend, Algebra.algebraMap_eq_smul_one]
    exact h2
  have : Nontrivial (Fin n → K) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hu0 (Subsingleton.elim _ _)
  have hmin : minpoly K (xl : Module.End K (Fin n → K)) = X ^ p - C α :=
    minpoly_eq_X_pow_sub_C hp hxlp hcx
  have hirr : Irreducible (X ^ p - C α : K[X]) := irreducible_X_pow_sub_C hp hcx
  have hsq : Squarefree (minpoly K (xl : Module.End K (Fin n → K))) := by
    rw [hmin]; exact hirr.squarefree
  let a : primaryFactors (xl : Module.End K (Fin n → K)) :=
    ⟨X ^ p - C α, by
      rw [mem_primaryFactors]
      exact ⟨hirr, monic_X_pow_sub_C _ hp.ne_zero, by rw [hmin]⟩⟩
  have hdeg : 2 ≤ (a : K[X]).natDegree := by
    simpa [a, natDegree_X_pow_sub_C] using hp.two_le
  have H : UnitaryPrimaryData h.bar B xl := ⟨h.bar_bar, hBsymm, idForm_separatingLeft h n, hxmem, hsq⟩
  have hself : dualPoly h.bar (a : K[X]) = a := by
    have hmem := dualPoly_mem_primaryFactors H a.2
    obtain ⟨hirr', hmon', hdvd'⟩ := mem_primaryFactors.mp hmem
    rw [hmin] at hdvd'
    exact Polynomial.eq_of_monic_of_associated hmon' (monic_X_pow_sub_C _ hp.ne_zero)
      (hirr'.associated_of_dvd hirr hdvd')
  have hcomp : ∀ v : Fin n → K,
      v ∈ primaryComponent (xl : Module.End K (Fin n → K)) (a : K[X]) := by
    intro v
    rw [mem_primaryComponent]
    have h0 : aeval (xl : Module.End K (Fin n → K)) (X ^ p - C α : K[X]) = 0 := by
      simp [hxlp]
    show aeval (xl : Module.End K (Fin n → K)) (X ^ p - C α : K[X]) v = 0
    rw [h0]; rfl
  have hS₁' : ∀ s ∈ S₁, (xl : Module.End K (Fin n → K)) s ∈ S₁ := fun s hs => by
    rw [hxend, Matrix.toLin'_apply]; exact hS₁ s hs
  have hS₂' : ∀ s ∈ S₂, (xl : Module.End K (Fin n → K)) s ∈ S₂ := fun s hs => by
    rw [hxend, Matrix.toLin'_apply]; exact hS₂ s hs
  have horth' : ∀ s ∈ S₁, ∀ t ∈ S₂, B s t = 0 := fun s hs t ht => by
    rw [hBdef, Nonsplit.idForm_eq_herm h]; exact horth s hs t ht
  have hKI' : ∀ w ∈ S₂, w ≠ 0 → ∃ w₀ ∈ S₂, B w₀ w₀ = 0 ∧ B w w₀ ≠ 0 := by
    intro w hw hw0
    obtain ⟨w₀, hw₀, h1, h2⟩ := hKI w hw hw0
    exact ⟨w₀, hw₀, by rw [hBdef, Nonsplit.idForm_eq_herm h]; exact h1,
      by rw [hBdef, Nonsplit.idForm_eq_herm h]; exact h2⟩
  obtain ⟨g, hg, hgdet, hgr, w₀, hw₀, hw₀0, hw₀i, u'', hu'', w'', hw'', hu''0, hw''0, hgw⟩ :=
    exists_mixing_element_of_selfDual_r (a := a) hBsymm (idForm_separatingLeft h n) hxmem hsq hself
      hdeg hS₁' hS₂' horth' hnd₁ hnd₂ hKI' hu (hcomp u) hu0 hw (hcomp w) hw0
  have hgsesq := (mem_unitaryCentralizer.mp hg).1
  have hgcomm := (mem_unitaryCentralizer.mp hg).2
  set gm : GL (Fin n) K := Matrix.GeneralLinearGroup.toLin.symm g with hgmdef
  have hgm : ∀ v, (gm : Matrix (Fin n) (Fin n) K) *ᵥ v = (g : Module.End K (Fin n → K)) v := by
    intro v
    have h1 : (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm g) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) = g := MulEquiv.apply_symm_apply _ g
    have h2 := congrArg (fun φ : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (φ : Module.End K (Fin n → K)) v) h1
    have h3 : ((Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm g) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) v =
        (Matrix.GeneralLinearGroup.toLin.symm g : Matrix (Fin n) (Fin n) K) *ᵥ v :=
      Matrix.GeneralLinearGroup.toLin_apply _ v
    exact h3.symm.trans h2
  have hgend : (g : Module.End K (Fin n → K)) = Matrix.toLin' (gm : Matrix (Fin n) (Fin n) K) :=
    LinearMap.ext fun v => by rw [Matrix.toLin'_apply, hgm]
  let gS : SUid σ n := ⟨gm, (mem_SUid_iff σ).mpr ⟨by
      rw [← LinearMap.det_toLin', ← hgend]; exact hgdet,
    fun v w => by
      rw [hgm, hgm, ← Nonsplit.idForm_eq_herm h, ← Nonsplit.idForm_eq_herm h]
      exact hgsesq v w⟩⟩
  have hgS : ∀ v, gS • v = (g : Module.End K (Fin n → K)) v := fun v => hgm v
  refine ⟨gS, ?_, ?_, w₀, hw₀, hw₀0, ?_, u'', hu'', w'', hw'', hu''0, hw''0, ?_⟩
  ·
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
    have := hgcomm.eq
    rw [hgend, hxend] at this
    exact this
  ·
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    show gm ^ ringChar K = 1
    rw [hgmdef, ← map_pow, hgr, map_one]
  · rw [← Nonsplit.idForm_eq_herm h]; exact hw₀i
  · rw [hgS]; exact hgw

theorem eq_top_of_nonpth_pair_r (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) {x y : GL (Fin n) K}
    (hx : x ∈ primeFormUnitary h (idGram K n))
    (hy : y ∈ primeFormUnitary h (idGram K n)) (hxy : x * y = y * x) {α : K}
    (hx3 : ((x ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hcx : ¬ ∃ μ : K, μ ^ p = α)
    (hy3 : ((y ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1)
    (hy1 : ∀ c : K, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1)
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) n)}
    (hHx : RCent H (x : Matrix (Fin n) (Fin n) K))
    (hHy : RCent H (y : Matrix (Fin n) (Fin n) K)) : H = ⊤ := by
  classical
  obtain ⟨ζ, hζ, hζN⟩ := exists_primitive_prime_root_bar h hp hpq
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hσ : IsUnitaryInvolution (unitaryInvolution K ℓ f) := Nonsplit.isUnitaryInvolution h
  have hσb : ∀ c, unitaryInvolution K ℓ f c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  obtain ⟨s₀, hs₀0, hs₀⟩ := Nonsplit.exists_norm_ne_one h hq
  set B := idForm h n with hBdef
  set xm : Matrix (Fin n) (Fin n) K := (x : Matrix (Fin n) (Fin n) K) with hxm
  set ym : Matrix (Fin n) (Fin n) K := (y : Matrix (Fin n) (Fin n) K) with hym
  have hyB : ∀ u v, B (Matrix.toLin' ym u) (Matrix.toLin' ym v) = B u v := fun u v =>
    mem_sesqUnitaryGroup.mp ((toLin_mem_sesqUnitaryGroup_iff y).mpr hy) u v
  have hyU : ∀ u w, herm (unitaryInvolution K ℓ f) (ym *ᵥ u) (ym *ᵥ w) =
      herm (unitaryInvolution K ℓ f) u w := fun u w => by
    have := hyB u w
    rw [hBdef, Nonsplit.idForm_eq_herm h, Nonsplit.idForm_eq_herm h] at this
    simpa [Matrix.toLin'_apply] using this
  set xT : Module.End K (Fin n → K) := Matrix.toLin' xm with hxT
  set yT : Module.End K (Fin n → K) := Matrix.toLin' ym with hyT
  have hxT3 : xT ^ p = algebraMap K (Module.End K (Fin n → K)) α := by
    have h1 : xm ^ p = α • 1 := by rw [hxm, ← Units.val_pow_eq_pow_val]; exact hx3
    have h2 := congrArg Matrix.toLinAlgEquiv' h1
    rw [map_pow, map_smul, map_one] at h2
    rw [hxT, Algebra.algebraMap_eq_smul_one]
    exact h2
  have hyT3 : yT ^ p = algebraMap K (Module.End K (Fin n → K)) (1 ^ p) := by
    have h1 : ym ^ p = 1 := by rw [hym, ← Units.val_pow_eq_pow_val]; exact hy3
    have h2 := congrArg Matrix.toLinAlgEquiv' h1
    rw [map_pow, map_one] at h2
    rw [one_pow, map_one]
    exact h2
  have hcomm : xT * yT = yT * xT := by
    have h1 : Matrix.toLin' (xm * ym) = Matrix.toLin' (ym * xm) := by
      rw [hxm, hym, ← Units.val_mul, ← Units.val_mul, hxy]
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul] at h1
    exact h1
  have hsup0 := iSup_eigenspace_eq_top_p hp hpK hζ one_ne_zero hyT3
  simp only [one_mul] at hsup0
  let V : Fin p → Submodule K (Fin n → K) := fun j => Module.End.eigenspace yT (ζ ^ (j : ℕ))
  have hsup : ⨆ j, V j = ⊤ := hsup0
  have hmemV : ∀ j v, v ∈ V j ↔ yT v = ζ ^ (j : ℕ) • v := fun j v =>
    Module.End.mem_eigenspace_iff
  have hstab : ∀ j, ∀ s ∈ V j, xT s ∈ V j := by
    intro j s hs
    rw [hmemV] at hs ⊢
    have h1 := congrArg (fun T : Module.End K (Fin n → K) => T s) hcomm
    simp only [Module.End.mul_apply] at h1
    rw [← h1, hs, map_smul]
  have hbar_pow : ∀ k : ℕ, h.bar (ζ ^ k) * ζ ^ k = 1 := fun k => by
    rw [map_pow, ← mul_pow, hζN, one_pow]
  have hlam_ne : ∀ i j : Fin p, i ≠ j → h.bar (ζ ^ (i : ℕ)) * ζ ^ (j : ℕ) ≠ 1 := by
    intro i j hij he
    have key : ζ ^ (j : ℕ) = ζ ^ (i : ℕ) := by
      linear_combination (-(ζ ^ (j : ℕ))) * hbar_pow i + (ζ ^ (i : ℕ)) * he
    have hji := hζ.pow_inj j.2 i.2 key
    exact hij (Fin.ext hji.symm)
  have hV_orth : ∀ i j : Fin p, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j, B u v = 0 := by
    intro i j hij u hu v hv
    exact NonCube.eigen_orthogonal hyB (hlam_ne i j hij) ((hmemV i u).mp hu)
      ((hmemV j v).mp hv)
  have hnd : ∀ j : Fin p, (B.domRestrict₁₂ (V j) (V j)).SeparatingLeft := fun j =>
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) V hV_orth hsup j
  have hdim : ∀ j, V j ≠ ⊥ → p ≤ Module.finrank K (V j) := fun j hj =>
    p_le_finrank_of_stable hp hxT3 hcx (hstab j) hj
  have hON : ∀ j, V j ≠ ⊥ → Centers.HasONBasis (unitaryInvolution K ℓ f) (V j) := fun j hj =>
    Nonsplit.hasONBasis_of_separatingLeft h (V j) (hnd j)
      (Or.inr ⟨by have := hdim j hj; omega, s₀, hs₀0, by rw [hσb]; exact hs₀⟩)
  have hVdisj : ∀ i j : Fin p, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    rw [Submodule.disjoint_def]
    intro v hvi hvj
    have h1 := (hmemV i v).mp hvi
    have h2 := (hmemV j v).mp hvj
    have h3 : (ζ ^ (i : ℕ) - ζ ^ (j : ℕ)) • v = 0 := by
      rw [sub_smul, ← h1, ← h2, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exfalso
      apply hlam_ne i j hij
      rw [sub_eq_zero.mp h4]
      exact hbar_pow j
    · exact h4
  have hpair : ∃ i j : Fin p, i ≠ j ∧ V i ≠ ⊥ ∧ V j ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hj₀ : ∃ j₀ : Fin p, ∀ j, j ≠ j₀ → V j = ⊥ := by
      by_cases hex : ∃ j₀, V j₀ ≠ ⊥
      · obtain ⟨j₀, hj₀⟩ := hex
        exact ⟨j₀, fun j hj => hcon j₀ j (Ne.symm hj) hj₀⟩
      · push Not at hex
        exact ⟨⟨0, hp.pos⟩, fun j _ => hex j⟩
    obtain ⟨j₀, hj₀⟩ := hj₀
    have hall : ∀ v, yT v = ζ ^ (j₀ : ℕ) • v := by
      intro v
      have hv : v ∈ ⨆ j, V j := by rw [hsup]; exact Submodule.mem_top
      have hle : (⨆ j, V j) ≤ V j₀ := iSup_le fun j => by
        by_cases hj : j = j₀
        · rw [hj]
        · rw [hj₀ j hj]; exact bot_le
      exact (hmemV j₀ v).mp (hle hv)
    apply hy1 (ζ ^ (j₀ : ℕ))
    refine Matrix.ext_of_mulVec_single fun i => ?_
    have := hall (Pi.single i 1)
    rw [hyT, Matrix.toLin'_apply] at this
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    exact this
  obtain ⟨i₀, j₀, hij₀, hi₀, hj₀⟩ := hpair
  let W : {j : Fin p // V j ≠ ⊥} → Submodule K (Fin n → K) := fun i => V i.1
  have hAll : ∀ j, Centers.AllCenters H (V j) := by
    intro j v hv hvi
    have hyv : ym *ᵥ v = ζ ^ (j : ℕ) • v := by
      have := (hmemV j v).mp hv
      rwa [hyT, Matrix.toLin'_apply] at this
    have hl : unitaryInvolution K ℓ f (ζ ^ (j : ℕ)) * ζ ^ (j : ℕ) = 1 := by
      rw [hσb]; exact hbar_pow j
    exact isCenter_of_eigen_matrix_r hσ.invol hHy hyU hvi hl hyv
  have hWorth : ∀ i j : {j : Fin p // V j ≠ ⊥}, i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j,
      herm (unitaryInvolution K ℓ f) u v = 0 := by
    intro i j hij u hu v hv
    have hne : i.1 ≠ j.1 := fun h' => hij (Subtype.ext h')
    rw [← Nonsplit.idForm_eq_herm h]
    exact hV_orth i.1 j.1 hne u hu v hv
  have hWtop : ⨆ i : {j : Fin p // V j ≠ ⊥}, W i = ⊤ := by
    rw [eq_top_iff, ← hsup]
    refine iSup_le fun j => ?_
    by_cases hj : V j = ⊥
    · rw [hj]; exact bot_le
    · exact le_iSup_of_le ⟨j, hj⟩ le_rfl
  have hstab' : ∀ j, ∀ s ∈ V j, xm *ᵥ s ∈ V j := fun j s hs => by
    have := hstab j s hs
    rwa [hxT, Matrix.toLin'_apply] at this
  have hmix : ∀ i j : {j : Fin p // V j ≠ ⊥}, i ≠ j → ∃ w₁ ∈ W i, ∃ w₂ ∈ W j,
      w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ Centers.IsCenter H (w₁ + w₂) := by
    intro i j hij
    have hne : i.1 ≠ j.1 := fun h' => hij (Subtype.ext h')
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot i.2
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot j.2
    have hKI : ∀ w ∈ V j.1, w ≠ 0 → ∃ w₀ ∈ V j.1, herm (unitaryInvolution K ℓ f) w₀ w₀ = 0 ∧
        herm (unitaryInvolution K ℓ f) w w₀ ≠ 0 :=
      fun w hw hw0 => Nonsplit.exists_isotropic_pairing hσ (hON j.1 j.2) hw hw0
    obtain ⟨g, hgx, hgr, w₀, hw₀, hw₀0, hw₀i, u'', hu'', w'', hw'', hu''0, hw''0, hgw⟩ :=
      exists_mixing_of_nonpth_r h hp hx hx3 hcx (hstab' i.1) (hstab' j.1)
        (fun s hs t ht => by
          rw [← Nonsplit.idForm_eq_herm h]; exact hV_orth i.1 j.1 hne s hs t ht)
        (hnd i.1) (hnd j.1) hKI hu hu0 hw hw0
    have hgH : g ∈ H := hHx g hgx hgr
    have hC : Centers.IsCenter H w₀ := hAll j.1 w₀ hw₀ hw₀i
    have hCg := hC.map hgH
    rw [hgw] at hCg
    exact ⟨u'', hu'', w'', hw'', hu''0, hw''0, hCg⟩
  have hn4 : 4 ≤ n := by
    have h1 := hdim i₀ hi₀
    have h2 := hdim j₀ hj₀
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq (V i₀) (V j₀)
    rw [(hVdisj i₀ j₀ hij₀).eq_bot, finrank_bot] at h3
    have h4 := Submodule.finrank_le (V i₀ ⊔ V j₀)
    rw [Module.finrank_fin_fun] at h4
    omega
  have : Nonempty {j : Fin p // V j ≠ ⊥} := ⟨⟨i₀, hi₀⟩⟩
  exact Centers.eq_top_of_blocks hσ hn4 W (fun i => hON i.1 i.2) hWorth (fun i => hAll i.1) hmix
    hWtop

end NonPthR

section Opposite

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.CTP

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem exists_stable_compl_gl [Finite K] {A : Subgroup (GL (Fin n) K)} (hA : (Nat.card A : K) ≠ 0)
    {X : Submodule K (Fin n → K)}
    (hX : ∀ g ∈ A, ∀ x ∈ X, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ X) :
    ∃ X' : Submodule K (Fin n → K), IsCompl X X' ∧
      ∀ g ∈ A, ∀ x ∈ X', ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ X' := by
  have : NeZero (Nat.card A : K) := ⟨hA⟩
  let ρ : Representation K A (Fin n → K) :=
    { toFun := fun g => Matrix.toLin' (((g : A) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      map_one' := by simp; rfl
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul, Units.val_mul, Matrix.toLin'_mul]
        rfl }
  let τ : Subrepresentation ρ := ⟨X, fun g v hv => hX g g.2 v hv⟩
  obtain ⟨τ', hτ'⟩ := exists_isCompl τ
  refine ⟨τ'.toSubmodule, ⟨?_, ?_⟩, fun x hx w hw => τ'.apply_mem_toSubmodule ⟨x, hx⟩ hw⟩
  · rw [disjoint_iff]
    have := congrArg Subrepresentation.toSubmodule (disjoint_iff.1 hτ'.1)
    exact this
  · rw [codisjoint_iff]
    have := congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 hτ'.2)
    exact this

theorem stable_hermOrth_gl {A : Subgroup (GL (Fin n) K)}
    (hiso : ∀ g ∈ A, ∀ x y, herm σ (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) = herm σ x y)
    {X : Submodule K (Fin n → K)}
    (hX : ∀ g ∈ A, ∀ x ∈ X, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ X) :
    ∀ g ∈ A, ∀ v ∈ hermOrth σ X, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ hermOrth σ X := by
  intro g hg v hv w hw
  have hw' : (((g⁻¹ : GL (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ X :=
    hX g⁻¹ (A.inv_mem hg) w hw
  have hgg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((((g⁻¹ : GL (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  calc herm σ w (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
      = herm σ (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          ((((g⁻¹ : GL (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w))
          (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) := by rw [hgg]
    _ = herm σ ((((g⁻¹ : GL (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) v :=
        hiso g hg _ _
    _ = 0 := hv _ hw'

theorem exists_opposite_gl [Finite K] (hσ : IsUnitaryInvolution σ) {A : Subgroup (GL (Fin n) K)}
    (hA : (Nat.card A : K) ≠ 0)
    (hiso : ∀ g ∈ A, ∀ x y, herm σ (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) = herm σ x y)
    {W : Submodule K (Fin n → K)} (hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0)
    (hWs : ∀ g ∈ A, ∀ w ∈ W, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) :
    ∃ W' : Submodule K (Fin n → K), (∀ x ∈ W', ∀ y ∈ W', herm σ x y = 0) ∧
      IsCompl (hermOrth σ W) W' ∧
        ∀ g ∈ A, ∀ w ∈ W', ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W' := by
  classical
  have hWP : ∀ w ∈ W, w ∈ hermOrth σ W := fun w hw x hx => hW x hx w hw
  obtain ⟨C₀, hC₀, hC₀s⟩ := exists_stable_compl_gl hA (stable_hermOrth_gl hiso hWs)
  have hC₀P := stable_hermOrth_gl hiso hC₀s
  have hfin1 := finrank_hermOrth_add σ hσ.invol W
  have hfin2 := finrank_hermOrth_add σ hσ.invol C₀
  have hfin3 : Module.finrank K (hermOrth σ W) + Module.finrank K C₀ = n := by
    simpa using Submodule.finrank_add_eq_of_isCompl hC₀
  have hdisj : Disjoint W (hermOrth σ C₀) := by
    rw [Submodule.disjoint_def]
    intro w hw hwC
    refine eq_zero_of_herm σ fun y => ?_
    have hy : y ∈ hermOrth σ W ⊔ C₀ := by rw [hC₀.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
    rw [herm_add_right, hu w hw, herm_eq_zero_comm σ hσ.invol (hwC c hc), add_zero]
  have hWC : IsCompl W (hermOrth σ C₀) := by
    refine (Submodule.isCompl_iff_disjoint W (hermOrth σ C₀) ?_).2 hdisj
    simp only [Module.finrank_fin_fun]
    omega
  set P : (Fin n → K) →ₗ[K] (Fin n → K) := W.projection (hermOrth σ C₀) hWC with hPdef
  have hP1 : ∀ v, P v ∈ W := fun v => Submodule.projection_apply_mem hWC v
  have hP2 : ∀ v, v - P v ∈ hermOrth σ C₀ := fun v => Submodule.sub_projection_mem hWC v
  have hPW : ∀ w ∈ W, P w = w := fun w hw => Submodule.projection_apply_of_mem_left hWC hw
  have hPC : ∀ z ∈ hermOrth σ C₀, P z = 0 := fun z hz =>
    Submodule.projection_apply_of_mem_right hWC hz
  have hPg : ∀ g ∈ A, ∀ v, P (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ P v := by
    intro g hg v
    have hv : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ P v +
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (v - P v) := by
      rw [← Matrix.mulVec_add]; congr 1; abel
    rw [hv, map_add, hPW _ (hWs g hg _ (hP1 v)), hPC _ (hC₀P g hg _ (hP2 v)), add_zero]
  obtain ⟨κ, hκ⟩ := hσ.trace_surj 1 (map_one σ)
  have hcc : ∀ c₁ ∈ C₀, ∀ c₂ ∈ C₀, herm σ c₁ (P c₂) = herm σ c₁ c₂ := by
    intro c₁ hc₁ c₂ _
    have := hP2 c₂ c₁ hc₁
    rw [herm_sub_right, sub_eq_zero] at this
    exact this.symm
  refine ⟨C₀.map (LinearMap.id - κ • P), ?_, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩
    have e1 := hcc c₁ hc₁ c₂ hc₂
    have e2 : herm σ (P c₁) c₂ = herm σ c₁ c₂ := by
      rw [herm_conj σ hσ.invol c₂ (P c₁), hcc c₂ hc₂ c₁ hc₁, ← herm_conj σ hσ.invol c₂ c₁]
    have e3 := hW _ (hP1 c₁) _ (hP1 c₂)
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, herm_sub_left,
      herm_sub_right, herm_smul_left, herm_smul_right, e1, e2, e3]
    linear_combination (-(herm σ c₁ c₂)) * hκ
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro x ⟨hx, c, hc, rfl⟩
    have hcP : c ∈ hermOrth σ W := by
      have h1 : c = (c - κ • P c) + κ • P c := by abel
      rw [h1]
      exact (hermOrth σ W).add_mem (by simpa using hx)
        ((hermOrth σ W).smul_mem _ (hWP _ (hP1 c)))
    have hc0 : c = 0 := Submodule.disjoint_def.1 hC₀.disjoint c hcP hc
    simp [hc0]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v ∈ hermOrth σ W ⊔ C₀ := by rw [hC₀.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    refine Submodule.mem_sup.2 ⟨u + κ • P c, ?_, c - κ • P c, ⟨c, hc, rfl⟩, by abel⟩
    exact (hermOrth σ W).add_mem hu ((hermOrth σ W).smul_mem _ (hWP _ (hP1 c)))
  · rintro g hg _ ⟨c, hc, rfl⟩
    refine ⟨((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c, hC₀s g hg c hc, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, Matrix.mulVec_sub,
      hPg g hg, Matrix.mulVec_smul]

theorem uRad_conj_mem_gl {W : Submodule K (Fin n → K)} {hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0}
    {e : GL (Fin n) K}
    (hiso : ∀ x y, herm σ ((e : Matrix (Fin n) (Fin n) K) *ᵥ x) ((e : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      herm σ x y)
    (he : ∀ w ∈ W, (e : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    (he' : ∀ w ∈ W, ((e⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    {g g' : SUid σ n} (hg : g ∈ uRad σ W hW) (hg' : (g' : GL (Fin n) K) = e * g * e⁻¹) :
    g' ∈ uRad σ W hW := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hmul : ∀ x : Fin n → K, g' • x = (e : Matrix (Fin n) (Fin n) K) *ᵥ (g • (((e⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ x)) := fun x => by
    show ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x = _
    rw [hg', Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rfl
  have hee : ∀ x : Fin n → K, (e : Matrix (Fin n) (Fin n) K) *ᵥ (((e⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hee' : ∀ x : Fin n → K, ((e⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((e : Matrix (Fin n) (Fin n) K) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hiso' : ∀ x y, herm σ (((e⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
      (((e⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) = herm σ x y := fun x y => by
    rw [← hiso, hee, hee]
  have hP : ∀ v ∈ hermOrth σ W, (e : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ hermOrth σ W := by
    intro v hv w hw
    calc herm σ w ((e : Matrix (Fin n) (Fin n) K) *ᵥ v)
        = herm σ ((e : Matrix (Fin n) (Fin n) K) *ᵥ (((e⁻¹ : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *ᵥ w)) ((e : Matrix (Fin n) (Fin n) K) *ᵥ v) := by rw [hee]
      _ = herm σ (((e⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) v := hiso _ _
      _ = 0 := hv _ (he' w hw)
  have hP' : ∀ v ∈ hermOrth σ W, ((e⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
      hermOrth σ W := by
    intro v hv w hw
    calc herm σ w (((e⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
        = herm σ (((e⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            ((e : Matrix (Fin n) (Fin n) K) *ᵥ w)) (((e⁻¹ : GL (Fin n) K) :
              Matrix (Fin n) (Fin n) K) *ᵥ v) := by rw [hee']
      _ = herm σ ((e : Matrix (Fin n) (Fin n) K) *ᵥ w) v := hiso' _ _
      _ = 0 := hv _ (he w hw)
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hmul]
    have h2 := hP _ (hg1 (((e⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x))
    rw [Matrix.mulVec_sub, hee] at h2
    exact h2
  · rw [hmul]
    have h2 := he _ (hg2 _ (hP' x hx))
    rw [Matrix.mulVec_sub, hee] at h2
    exact h2
  · rw [hmul, hg3 _ (he' x hx), hee]

theorem pow_ringChar_eq_one_of_mem_uRad {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hℓ2 : ℓ ≠ 2)
    {W : Submodule K (Fin n → K)} {hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0} {g : SUid σ n}
    (hg : g ∈ uRad σ W hW) : g ^ ringChar K = 1 := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hℓ : ringChar K = ℓ := ringChar.eq K ℓ
  set N : Module.End K (Fin n → K) := actU σ n g - 1 with hNdef
  have hNx : ∀ x, N x = g • x - x := fun x => by
    simp [hNdef, CFSG.LieType.SeitzGeneration.actU_apply]
  have hN3 : N * N * N = 0 := by
    refine LinearMap.ext fun x => ?_
    have h1 : N x ∈ hermOrth σ W := by rw [hNx]; exact hg1 x
    have h2 : N (N x) ∈ W := by rw [hNx]; exact hg2 _ h1
    have h3 : N (N (N x)) = 0 := by rw [hNx, hg3 _ h2, sub_self]
    simpa using h3
  have hg1' : actU σ n g = 1 + N := by rw [hNdef]; abel
  have hℓcast : ((ℓ : ℕ) : K) = 0 := CharP.cast_eq_zero K ℓ
  have hℓ3 : 2 < ℓ := lt_of_le_of_ne (Fact.out : ℓ.Prime).two_le (Ne.symm hℓ2)
  have hchoose : ((ℓ.choose 2 : ℕ) : K) = 0 := by
    rw [CharP.cast_eq_zero_iff K ℓ]
    exact Nat.Prime.dvd_choose_self Fact.out two_ne_zero hℓ3
  have hpow : actU σ n (g ^ ringChar K) = 1 := by
    rw [hℓ, map_pow, hg1', unip_pow_of_cube_eq_zero (K := K) hN3 ℓ, hℓcast, hchoose, zero_smul,
      zero_smul, add_zero, add_zero]
  refine ext_smul σ fun v => ?_
  rw [one_smul]
  exact LinearMap.congr_fun hpow v

end Opposite

section Lifts

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem eq_scalar_of_conj_eq_one (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (A : primeFormUnitary h (idGram K n)) (hA : primeFormConjHom h (idGram K n) A = 1) :
    ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      (A : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have h1 := (primeFormPsi_eq_one_iff h hC hn ⟨A, 1⟩).1
    (by rw [primeFormPsi_apply, map_one, mul_one]; exact hA)
  exact h1.2

theorem coe_scalar_gl (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (c : K) • 1 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul,
    Matrix.mul_one]

theorem scalar_mem_primeFormUnitary (h : UnitaryFieldData ℓ f K) {c : Kˣ} (hc : h.norm (c : K) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary, coe_scalar_gl]
  have h1 : (((c : K) • (1 : Matrix (Fin n) (Fin n) K)).map h.bar)ᵀ =
      h.bar (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply, hij, Ne.symm hij]
  rw [h1]
  have hc' : h.bar (c : K) * (c : K) = 1 := by rw [mul_comm]; exact hc
  simp only [idGram, Units.val_one, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul,
    hc', one_smul]

theorem conj_scalar_eq_one (h : UnitaryFieldData ℓ f K) (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    primeFormConjHom h (idGram K n) A = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  congr 1
  refine Subtype.ext ?_
  change (A : GL (Fin n) K) * (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = g
  rw [hA, ← (commute_scalar c (g : GL (Fin n) K)).eq, mul_inv_cancel_right]

theorem mem_of_conj_mem_of_sup_eq (h : UnitaryFieldData ℓ f K)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} {X Y : primeFormUnitary h (idGram K n)}
    (hgen : Subgroup.zpowers (primeFormConjHom h (idGram K n) X) ⊔
      Subgroup.zpowers (primeFormConjHom h (idGram K n) Y) = E)
    {S : Subgroup (primeFormUnitary h (idGram K n))}
    (hS : ∀ A, primeFormConjHom h (idGram K n) A = 1 → A ∈ S) (hX : X ∈ S) (hY : Y ∈ S)
    {A : primeFormUnitary h (idGram K n)} (hA : primeFormConjHom h (idGram K n) A ∈ E) : A ∈ S := by
  have hle : E ≤ S.map (primeFormConjHom h (idGram K n)) := by
    rw [← hgen]
    exact sup_le (Subgroup.zpowers_le.2 ⟨X, hX, rfl⟩) (Subgroup.zpowers_le.2 ⟨Y, hY, rfl⟩)
  obtain ⟨B, hB, hBA⟩ := hle hA
  have h1 : primeFormConjHom h (idGram K n) (A * B⁻¹) = 1 := by
    rw [map_mul, map_inv, hBA, mul_inv_cancel]
  have h2 := hS _ h1
  have h3 : A = (A * B⁻¹) * B := by group
  rw [h3]
  exact S.mul_mem h2 hB

theorem exists_pow_eq_smul_of_conj (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) {p : ℕ}
    (A : primeFormUnitary h (idGram K n)) (hA : (primeFormConjHom h (idGram K n) A) ^ p = 1) :
    ∃ α : K, α ≠ 0 ∧
      ((((A : GL (Fin n) K)) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1 := by
  obtain ⟨c, -, hc⟩ := eq_scalar_of_conj_eq_one h hn (A ^ p) (by rw [map_pow, hA])
  refine ⟨(c : K), c.ne_zero, ?_⟩
  rw [← coe_scalar_gl, ← hc]
  rfl

theorem exists_smul_comm_of_conj (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (A B : primeFormUnitary h (idGram K n))
    (hAB : primeFormConjHom h (idGram K n) A * primeFormConjHom h (idGram K n) B =
      primeFormConjHom h (idGram K n) B * primeFormConjHom h (idGram K n) A) :
    ∃ c : K, ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨c, -, hc⟩ := eq_scalar_of_conj_eq_one h hn (B * A * B⁻¹ * A⁻¹)
    (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hAB]; group)
  refine ⟨(c : K), ?_⟩
  have h1 : (B : GL (Fin n) K) * A = Matrix.GeneralLinearGroup.scalar (Fin n) c * (A * B) := by
    rw [← hc]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h1
  simp only [Units.val_mul, coe_scalar_gl, Matrix.smul_mul, Matrix.one_mul] at h2
  exact h2

end Lifts

section HeisIso

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.SeitzGeneration.NonPth

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem herm_eq_zero_of_mem_span {σ : K ≃+* K} {S : Set (Fin n → K)}
    (hS : ∀ s ∈ S, ∀ t ∈ S, herm σ s t = 0) {x y : Fin n → K} (hx : x ∈ Submodule.span K S)
    (hy : y ∈ Submodule.span K S) : herm σ x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem s hs =>
    induction hy using Submodule.span_induction with
    | mem t ht => exact hS s hs t ht
    | zero => simp [herm]
    | add a b _ _ ha hb => rw [herm_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [herm_smul_right, ha, mul_zero]
  | zero => simp [herm]
  | add a b _ _ ha hb => rw [herm_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [herm_smul_left, ha, mul_zero]

theorem exists_isotropic_of_two_le [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    (V : Submodule K (Fin n → K)) (hV : ((idForm h n).domRestrict₁₂ V V).SeparatingLeft)
    (h2 : 2 ≤ Module.finrank K V) :
    ∃ v ∈ V, v ≠ 0 ∧ herm (unitaryInvolution K ℓ f) v v = 0 := by
  classical
  have hσ : IsUnitaryInvolution (unitaryInvolution K ℓ f) := Nonsplit.isUnitaryInvolution h
  have hB : (idForm h n).IsSymm := idForm_isSymm h n
  obtain ⟨b, hb⟩ := h.exists_orthonormal_basis (hB.domRestrict V) hV
  set x : Fin (Module.finrank K V) → Fin n → K := fun i => (b i : Fin n → K) with hxdef
  have hx : ∀ i j, herm (unitaryInvolution K ℓ f) (x i) (x j) = if i = j then 1 else 0 := by
    intro i j
    have := hb i j
    rw [LinearMap.domRestrict₁₂_apply, Nonsplit.idForm_eq_herm] at this
    exact this
  obtain ⟨a, ha0, ha⟩ := Centers.exists_isotropic_ne_zero hσ h2
  refine ⟨Centers.orthoEmb x a, ?_, ?_, ?_⟩
  · rw [Centers.orthoEmb_apply]
    exact V.sum_mem fun i _ => V.smul_mem _ (b i).2
  · intro h0
    apply ha0
    refine eq_zero_of_herm (unitaryInvolution K ℓ f) fun d => ?_
    rw [← Centers.herm_orthoEmb hx, h0]
    simp [herm]
  · rw [Centers.herm_orthoEmb hx]
    exact ha

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem exists_isotropic_of_heis (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1)
    (hn : 3 ≤ n) (hnp : n ≠ p) {X Y : GL (Fin n) K}
    (hX : X ∈ primeFormUnitary h (idGram K n)) (hY : Y ∈ primeFormUnitary h (idGram K n))
    {α c : K} (hα : α ≠ 0) (hXp : ((X ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hYp : Y ^ p = 1)
    (hc : (Y : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) =
      c • ((X : Matrix (Fin n) (Fin n) K) * (Y : Matrix (Fin n) (Fin n) K))) (hc1 : c ≠ 1) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, herm (unitaryInvolution K ℓ f) x y = 0) ∧
      (∀ w ∈ W, (X : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) ∧
      (∀ w ∈ W, (Y : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  set σ := unitaryInvolution K ℓ f with hσdef
  have hσb : ∀ c, σ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  set B := idForm h n with hBdef
  set xm : Matrix (Fin n) (Fin n) K := (X : Matrix (Fin n) (Fin n) K) with hxm
  set ym : Matrix (Fin n) (Fin n) K := (Y : Matrix (Fin n) (Fin n) K) with hym
  have hcp : c ^ p = 1 := pow_eq_one_of_smul_comm_p hn0 hα hXp hc
  have hζ : IsPrimitiveRoot c p := by
    rw [← orderOf_eq_prime hcp hc1]
    exact IsPrimitiveRoot.orderOf c
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  have hpn : p ∣ n := by
    have hdet := congrArg Matrix.det hc
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin] at hdet
    have hD : xm.det * ym.det ≠ 0 :=
      mul_ne_zero ((Matrix.isUnit_iff_isUnit_det _).1 X.isUnit).ne_zero
        ((Matrix.isUnit_iff_isUnit_det _).1 Y.isUnit).ne_zero
    have hcn : c ^ n = 1 := by
      apply mul_right_cancel₀ hD
      linear_combination -hdet
    exact hζ.dvd_of_pow_eq_one n hcn
  have hxB : ∀ u v, B (Matrix.toLin' xm u) (Matrix.toLin' xm v) = B u v := fun u v =>
    mem_sesqUnitaryGroup.mp ((toLin_mem_sesqUnitaryGroup_iff X).mpr hX) u v
  have hyB : ∀ u v, B (Matrix.toLin' ym u) (Matrix.toLin' ym v) = B u v := fun u v =>
    mem_sesqUnitaryGroup.mp ((toLin_mem_sesqUnitaryGroup_iff Y).mpr hY) u v
  have hxU : ∀ u w, herm σ (xm *ᵥ u) (xm *ᵥ w) = herm σ u w := fun u w => by
    have := hxB u w
    rw [hBdef, Nonsplit.idForm_eq_herm h, Nonsplit.idForm_eq_herm h] at this
    simpa [Matrix.toLin'_apply] using this
  have hxUk : ∀ k : ℕ, ∀ u w, herm σ (xm ^ k *ᵥ u) (xm ^ k *ᵥ w) = herm σ u w := by
    intro k
    induction k with
    | zero => intro u w; simp
    | succ k ih =>
      intro u w
      rw [pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih, hxU]
  set yT : Module.End K (Fin n → K) := Matrix.toLin' ym with hyT
  have hyT3 : yT ^ p = algebraMap K (Module.End K (Fin n → K)) (1 ^ p) := by
    have h1 : ym ^ p = 1 := by rw [hym, ← Units.val_pow_eq_pow_val, hYp, Units.val_one]
    have h2 := congrArg Matrix.toLinAlgEquiv' h1
    rw [map_pow, map_one] at h2
    rw [one_pow, map_one]
    exact h2
  have hsup0 := iSup_eigenspace_eq_top_p hp hpK hζ one_ne_zero hyT3
  simp only [one_mul] at hsup0
  let V : Fin p → Submodule K (Fin n → K) := fun j => Module.End.eigenspace yT (c ^ (j : ℕ))
  have hsup : ⨆ j, V j = ⊤ := hsup0
  have hmemV : ∀ j v, v ∈ V j ↔ ym *ᵥ v = c ^ (j : ℕ) • v := fun j v => by
    rw [Module.End.mem_eigenspace_iff, hyT, Matrix.toLin'_apply]
  have hcN : h.bar c * c = 1 := by
    rw [h.bar_apply, ← pow_succ]
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, hcp, one_pow]
  have hbar_pow : ∀ k : ℕ, h.bar (c ^ k) * c ^ k = 1 := fun k => by
    rw [map_pow, ← mul_pow, hcN, one_pow]
  have hlam_ne : ∀ i j : ℕ, i < p → j < p → i ≠ j → h.bar (c ^ i) * c ^ j ≠ 1 := by
    intro i j hi hj hij he
    have key : c ^ j = c ^ i := by
      linear_combination (-(c ^ j)) * hbar_pow i + (c ^ i) * he
    exact hij (hζ.pow_inj hi hj key.symm)
  have horth : ∀ (i j : ℕ) (u v : Fin n → K), i < p → j < p → i ≠ j → ym *ᵥ u = c ^ i • u →
      ym *ᵥ v = c ^ j • v → herm σ u v = 0 := by
    intro i j u v hi hj hij hu hv
    have := NonCube.eigen_orthogonal hyB (hlam_ne i j hi hj hij)
      (u := u) (v := v) (by rw [Matrix.toLin'_apply]; exact hu) (by rw [Matrix.toLin'_apply]; exact hv)
    rw [hBdef, Nonsplit.idForm_eq_herm h] at this
    exact this
  have hV_orth : ∀ i j : Fin p, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j, B u v = 0 := by
    intro i j hij u hu v hv
    rw [hBdef, Nonsplit.idForm_eq_herm h]
    exact horth i j u v i.2 j.2 (fun h' => hij (Fin.ext h')) ((hmemV i u).1 hu) ((hmemV j v).1 hv)
  have hnd : ∀ j : Fin p, (B.domRestrict₁₂ (V j) (V j)).SeparatingLeft := fun j =>
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) V hV_orth hsup j
  have hYXk : ∀ (k : ℕ) (v : Fin n → K) (lam : K), ym *ᵥ v = lam • v →
      ym *ᵥ (xm ^ k *ᵥ v) = (c ^ k * lam) • (xm ^ k *ᵥ v) := by
    intro k
    induction k with
    | zero => intro v lam hv; simpa using hv
    | succ k ih =>
      intro v lam hv
      have h1 : ym *ᵥ (xm *ᵥ (xm ^ k *ᵥ v)) = c • (xm *ᵥ (ym *ᵥ (xm ^ k *ᵥ v))) := by
        rw [Matrix.mulVec_mulVec, hym, hxm, hc, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
      rw [pow_succ', ← Matrix.mulVec_mulVec, h1, ih v lam hv, Matrix.mulVec_smul, smul_smul, pow_succ']
      ring_nf
  have hbig : ∃ j : Fin p, 2 ≤ Module.finrank K (V j) := by
    by_contra hcon
    push Not at hcon
    have hle1 : ∀ j : Fin p, ∃ v : Fin n → K, ∀ w ∈ V j, ∃ a : K, a • v = w := by
      intro j
      have h1 : Module.finrank K (V j) ≤ 1 := by have := hcon j; omega
      obtain ⟨v, hv⟩ := finrank_le_one_iff.mp h1
      refine ⟨(v : Fin n → K), fun w hw => ?_⟩
      obtain ⟨a, ha⟩ := hv ⟨w, hw⟩
      exact ⟨a, by simpa using congrArg Subtype.val ha⟩
    choose vj hvj using hle1
    have htop : (⊤ : Submodule K (Fin n → K)) ≤ Submodule.span K (Set.range vj) := by
      rw [← hsup]
      refine iSup_le fun j => fun w hw => ?_
      obtain ⟨a, ha⟩ := hvj j w hw
      rw [← ha]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hnle : n ≤ p := by
      calc n = Module.finrank K (Fin n → K) := (Module.finrank_fin_fun K).symm
        _ = Module.finrank K (⊤ : Submodule K (Fin n → K)) := by rw [finrank_top]
        _ ≤ Module.finrank K (Submodule.span K (Set.range vj)) := Submodule.finrank_mono htop
        _ ≤ Fintype.card (Fin p) := finrank_range_le_card vj
        _ = p := Fintype.card_fin p
    exact hnp (le_antisymm hnle (Nat.le_of_dvd hn0 hpn))
  obtain ⟨j₀, hj₀⟩ := hbig
  obtain ⟨v, hvV, hv0, hvi⟩ := exists_isotropic_of_two_le h (V j₀) (hnd j₀) hj₀
  have hvY : ym *ᵥ v = c ^ (j₀ : ℕ) • v := (hmemV j₀ v).1 hvV
  set vk : Fin p → (Fin n → K) := fun k => xm ^ (k : ℕ) *ᵥ v with hvk
  set W : Submodule K (Fin n → K) := Submodule.span K (Set.range vk) with hWdef
  have hvW : v ∈ W := by
    have h0 : vk ⟨0, hp.pos⟩ = v := by simp [hvk]
    rw [← h0]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hvkY : ∀ k : Fin p, ym *ᵥ vk k = (c ^ ((k : ℕ) + j₀)) • vk k := by
    intro k
    rw [hvk, hYXk k v _ hvY, ← pow_add]
  refine ⟨W, fun hW => hv0 (by simpa [hW] using hvW), ?_, ?_, ?_⟩
  ·
    refine fun x hx y hy => herm_eq_zero_of_mem_span ?_ hx hy
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    by_cases hkl : k = l
    · subst hkl
      rw [hvk, hxUk]
      exact hvi
    ·
      have hk := hvkY k
      have hl := hvkY l
      have hmod : ∀ m : ℕ, c ^ m = c ^ (m % p) := fun m => by
        conv_lhs => rw [← Nat.mod_add_div m p, pow_add, pow_mul, hcp, one_pow, mul_one]
      rw [hmod] at hk hl
      refine horth _ _ _ _ (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos) ?_ hk hl
      intro hmeq
      apply hkl
      have h1 : ((k : ℕ) + j₀) % p = ((l : ℕ) + j₀) % p := hmeq
      have h2 : (k : ℕ) % p = (l : ℕ) % p := by
        have := Nat.ModEq.add_right_cancel' (j₀ : ℕ) h1
        exact this
      rw [Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt l.2] at h2
      exact Fin.ext h2
  ·
    have hle : W ≤ W.comap (Matrix.mulVecLin xm) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      have hstep : xm *ᵥ vk k = xm ^ ((k : ℕ) + 1) *ᵥ v := by
        rw [hvk, pow_succ', ← Matrix.mulVec_mulVec]
      rw [hstep]
      by_cases hk : (k : ℕ) + 1 < p
      · exact Submodule.subset_span ⟨⟨(k : ℕ) + 1, hk⟩, rfl⟩
      · have hkp : (k : ℕ) + 1 = p := by omega
        have hXp' : xm ^ p = α • 1 := by rw [hxm, ← Units.val_pow_eq_pow_val]; exact hXp
        rw [hkp, hXp', Matrix.smul_mulVec, Matrix.one_mulVec]
        exact W.smul_mem _ hvW
    exact fun w hw => hle hw
  ·
    have hle : W ≤ W.comap (Matrix.mulVecLin ym) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      rw [hvkY k]
      exact W.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
    exact fun w hw => hle hw

end HeisIso

section ParabolicGen

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.RankThree.PartOne.CTP

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem natCast_card_lifts_ne_zero (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hp : p.Prime)
    (hpℓ : p ≠ ℓ) {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : ∀ e ∈ E, e ^ p = 1) :
    ((Nat.card ((E.comap (primeFormConjHom h (idGram K n))).map
      (primeFormUnitary h (idGram K n)).subtype) : ℕ) : K) ≠ 0 := by
  classical
  have hℓ : (ℓ).Prime := Fact.out
  rw [Ne, CharP.cast_eq_zero_iff K ℓ]
  intro hd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' ℓ hd
  obtain ⟨A, hA, hAg⟩ := g.2
  have hgℓ : g ^ ℓ = 1 := by have := pow_orderOf_eq_one g; rwa [hg] at this
  have hAℓ : A ^ ℓ = 1 := by
    apply Subtype.ext
    have h1 := congrArg Subtype.val hgℓ
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    have h2 : (A : GL (Fin n) K) = (g : GL (Fin n) K) := hAg
    rw [h2, h1]
  have hcA : primeFormConjHom h (idGram K n) A = 1 := by
    have h1 : (primeFormConjHom h (idGram K n) A) ^ ℓ = 1 := by rw [← map_pow, hAℓ, map_one]
    have h2 : (primeFormConjHom h (idGram K n) A) ^ p = 1 := hE _ hA
    have h3 : orderOf (primeFormConjHom h (idGram K n) A) ∣ Nat.gcd ℓ p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [(Nat.coprime_primes hℓ hp).2 (Ne.symm hpℓ)] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  obtain ⟨u, -, hu⟩ := eq_scalar_of_conj_eq_one h hn A hcA
  have huℓ : (u : K) ^ ℓ = 1 := by
    have h1 := congrArg (fun B : primeFormUnitary h (idGram K n) =>
      (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩)) hAℓ
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, Units.val_one, Matrix.one_apply_eq] at h1
    rw [hu, ← map_pow, coe_scalar_gl] at h1
    simpa using h1
  have hu1 : (u : K) = 1 := by
    have h1 : ((u : K) - 1) ^ ℓ = 0 := by rw [sub_pow_char, one_pow, huℓ, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff hℓ.ne_zero |>.1 h1)
  have hg1 : g = 1 := by
    apply Subtype.ext
    rw [OneMemClass.coe_one, ← hAg]
    show (A : GL (Fin n) K) = 1
    rw [hu]
    apply Units.ext
    rw [coe_scalar_gl, hu1, one_smul, Units.val_one]
  rw [hg1, orderOf_one] at hg
  exact hℓ.one_lt.ne hg

theorem uniPlaneGen_of_isotropic (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ ≠ 2) (hn : 3 ≤ n)
    (hp : p.Prime) (hpℓ : p ≠ ℓ) {E : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2) (hD : E ≤ primeFormD h (idGram K n))
    {W : Submodule K (Fin n → K)} (hW0 : W ≠ ⊥)
    (hWiso : ∀ x ∈ W, ∀ y ∈ W, herm (unitaryInvolution K ℓ f) x y = 0)
    (hWs : ∀ A : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) A ∈ E →
      ∀ w ∈ W, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) :
    UniPlaneGen ℓ E := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set σ := unitaryInvolution K ℓ f with hσdef
  have hσ : IsUnitaryInvolution σ := Nonsplit.isUnitaryInvolution h
  have hq : ℓ ^ f ≠ 2 := by
    intro h2
    have hodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
    rw [h2] at hodd
    exact (by decide : ¬ Odd 2) hodd
  have hiso : ∀ A : primeFormUnitary h (idGram K n), ∀ x y,
      herm σ (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
        (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) = herm σ x y := by
    intro A x y
    have := mem_sesqUnitaryGroup.mp ((toLin_mem_sesqUnitaryGroup_iff (A : GL (Fin n) K)).mpr A.2) x y
    rw [Nonsplit.idForm_eq_herm h, Nonsplit.idForm_eq_herm h] at this
    simpa [Matrix.toLin'_apply] using this
  set Ag : Subgroup (GL (Fin n) K) := (E.comap (primeFormConjHom h (idGram K n))).map
    (primeFormUnitary h (idGram K n)).subtype with hAg
  have hAiso : ∀ g ∈ Ag, ∀ x y, herm σ (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) = herm σ x y := by
    rintro _ ⟨A, -, rfl⟩ x y
    exact hiso A x y
  have hAs : ∀ g ∈ Ag, ∀ w ∈ W, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
    rintro _ ⟨A, hA, rfl⟩ w hw
    exact hWs A hA w hw
  obtain ⟨W', hW'iso, hcompl, hW's⟩ := exists_opposite_gl hσ
    (natCast_card_lifts_ne_zero h hn hp hpℓ hE.2) hAiso hWiso hAs
  have hW's' : ∀ A : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) A ∈ E →
      ∀ w ∈ W', ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W' :=
    fun A hA w hw => hW's _ ⟨A, hA, rfl⟩ w hw
  have hconj : ∀ {X : Submodule K (Fin n → K)} (hX : ∀ x ∈ X, ∀ y ∈ X, herm σ x y = 0),
      (∀ A : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) A ∈ E →
        ∀ w ∈ X, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ X) →
      ∀ e ∈ E, ∀ s ∈ (uRad σ X hX).map (suP h), e s ∈ (uRad σ X hX).map (suP h) := by
    intro X hX hXs e he s hs
    obtain ⟨A, rfl⟩ := hD he
    obtain ⟨g, hg, rfl⟩ := hs
    have hmem : (A : GL (Fin n) K) * (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ ∈
        SUid (unitaryInvolution K ℓ f) n :=
      (sUid_eq_gramSU h).ge (conj_mem_gramSU h (idGram K n) A.2 ((sUid_eq_gramSU h).le g.2))
    have hAinv : primeFormConjHom h (idGram K n) A⁻¹ ∈ E := by
      rw [map_inv]; exact E.inv_mem he
    have he' : ∀ w ∈ X, ((((A : GL (Fin n) K))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ X := by
      intro w hw
      rw [← Subgroup.coe_inv]
      exact hXs A⁻¹ hAinv w hw
    refine ⟨⟨_, hmem⟩, uRad_conj_mem_gl (hiso A) (hXs A he) he' hg rfl, ?_⟩
    exact (primeFormConjHom_suP h A g ⟨_, hmem⟩ rfl).symm
  have hr : ∀ {X : Submodule K (Fin n → K)} (hX : ∀ x ∈ X, ∀ y ∈ X, herm σ x y = 0),
      ∀ s ∈ (uRad σ X hX).map (suP h), ∃ m : ℕ, s ^ (ℓ ^ m) = 1 := by
    rintro X hX _ ⟨g, hg, rfl⟩
    refine ⟨1, ?_⟩
    have h1 := pow_ringChar_eq_one_of_mem_uRad hℓ2 hg
    have h2 : g ^ ℓ = 1 := by rwa [ringChar.eq K ℓ] at h1
    rw [pow_one, ← map_pow, h2, map_one]
  have hgen : (uRad σ W hWiso).map (suP h) ⊔ (uRad σ W' hW'iso).map (suP h) = ⊤ := by
    set L := (uRad σ W hWiso).map (suP h) ⊔ (uRad σ W' hW'iso).map (suP h) with hL
    obtain ⟨s₀, hs₀0, hs₀⟩ := Nonsplit.exists_norm_ne_one h hq
    have htop : L.comap (suP h) = ⊤ :=
      eq_top_of_uRad_of_opposite hσ (by omega)
        (fun _ => ⟨s₀, hs₀0, by rw [Nonsplit.unitaryInvolution_eq_bar h]; exact hs₀⟩) hW0 hWiso
        hW'iso hcompl
        (fun q hq => Subgroup.mem_comap.2 (Subgroup.mem_sup_left ⟨q, hq, rfl⟩))
        (fun q hq => Subgroup.mem_comap.2 (Subgroup.mem_sup_right ⟨q, hq, rfl⟩))
    rw [← Subgroup.map_comap_eq_self_of_surjective (suP_surjective h) L, htop,
      Subgroup.map_top_of_surjective _ (suP_surjective h)]
  refine uniPlaneGen_of_rSubgroups hp hℓ hpℓ hE hc
    {(uRad σ W hWiso).map (suP h), (uRad σ W' hW'iso).map (suP h)} ?_ ?_ ?_
  · rintro H (rfl | rfl)
    · exact hr hWiso
    · exact hr hW'iso
  · rintro H (rfl | rfl)
    · exact hconj hWiso hWs
    · exact hconj hW'iso hW's'
  · rw [iSup_insert, iSup_singleton]
    exact hgen

end ParabolicGen

section InnDiag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem ne_one_of_indep {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {x y : G}
    (hind : ∀ i j : ℕ, x ^ i * y ^ j = 1 → p ∣ i ∧ p ∣ j) : x ≠ 1 := by
  intro h1
  have := (hind 1 0 (by rw [h1]; simp)).1
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

theorem notMem_zpowers_of_indep {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {x y : G}
    (hx : x ^ p = 1) (hind : ∀ i j : ℕ, x ^ i * y ^ j = 1 → p ∣ i ∧ p ∣ j) :
    y ∉ Subgroup.zpowers x := by
  intro hmem
  obtain ⟨m, hm⟩ := (mem_zpowers_iff_exists_pow_p hp.pos hx).1 hmem
  have h1 : x ^ ((p - 1) * m) * y ^ 1 = 1 := by
    rw [pow_one, ← hm, ← pow_add, show (p - 1) * m + m = p * m by
      have := hp.one_lt
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left m (by omega))],
      pow_mul, hx, one_pow]
  exact hp.one_lt.ne' (Nat.dvd_one.1 (hind _ _ h1).2)

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem rcent_word (h : UnitaryFieldData ℓ f K) {E : Subgroup (MulAut (primeFormP h (idGram K n)))}
    {X Y : primeFormUnitary h (idGram K n)} (hXE : primeFormConjHom h (idGram K n) X ∈ E)
    (hYE : primeFormConjHom h (idGram K n) Y ∈ E)
    (hind : ∀ i j : ℕ, (primeFormConjHom h (idGram K n) X) ^ i *
      (primeFormConjHom h (idGram K n) Y) ^ j = 1 → p ∣ i ∧ p ∣ j)
    (i j : ℕ) (hij : ¬ (p ∣ i ∧ p ∣ j)) :
    RCent ((uniPlaneClosure ℓ E).comap (suP h))
      ((((X : GL (Fin n) K) ^ i * (Y : GL (Fin n) K) ^ j : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
  intro g hg hgr
  refine mem_comap_of_rcent h (X ^ i * Y ^ j) ?_ ?_ g ?_ hgr
  · rw [map_mul, map_pow, map_pow]
    exact E.mul_mem (E.pow_mem hXE i) (E.pow_mem hYE j)
  · rw [map_mul, map_pow, map_pow]
    exact fun h1 => hij (hind i j h1)
  · simpa only [Subgroup.coe_mul, SubgroupClass.coe_pow] using hg

theorem uniPlaneGen_of_pair (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ ≠ 2) (hn : 3 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpq : p ∣ ℓ ^ f + 1)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hD : E ≤ primeFormD h (idGram K n))
    (X Y : primeFormUnitary h (idGram K n))
    (hXE : primeFormConjHom h (idGram K n) X ∈ E) (hYE : primeFormConjHom h (idGram K n) Y ∈ E)
    (hind : ∀ i j : ℕ, (primeFormConjHom h (idGram K n) X) ^ i *
      (primeFormConjHom h (idGram K n) Y) ^ j = 1 → p ∣ i ∧ p ∣ j)
    {α c : K} (hα : α ≠ 0)
    (hXp : ((((X : GL (Fin n) K)) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hYp : (Y : GL (Fin n) K) ^ p = 1)
    (hYX : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    UniPlaneGen ℓ E ∨ (n = p ∧ X * Y ≠ Y * X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hℓ : ℓ.Prime := Fact.out
  have hn0 : 0 < n := by omega
  have hq : ℓ ^ f ≠ 2 := by
    intro h2
    have hodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
    rw [h2] at hodd
    exact (by decide : ¬ Odd 2) hodd
  have hp1 : ¬ p ∣ 1 := fun hd => hp.one_lt.ne' (Nat.dvd_one.mp hd)
  set H := (uniPlaneClosure ℓ E).comap (suP h) with hHdef
  by_cases hc1 : c = 1
  · subst hc1
    have hcomm : (X : GL (Fin n) K) * Y = Y * X :=
      Units.ext (by rw [Units.val_mul, Units.val_mul, hYX, one_smul])
    by_cases hμ : ∃ μ : K, μ ^ p = α
    ·
      obtain ⟨μ, hμp⟩ := hμ
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero] at hμp
        exact hα hμp.symm
      have hαN : h.bar α * α = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) X.2 hXp
      have hμN : h.bar μ * μ = 1 :=
        bar_mul_eq_one_of_pow_eq h hp hp2 hpq hμ0 hμp (planeW_pow_card_succ h hαN)
      set u : Kˣ := Units.mk0 μ⁻¹ (inv_ne_zero hμ0) with hu
      have huN : h.norm (u : K) = 1 := by
        rw [UnitaryFieldData.norm, hu, Units.val_mk0, map_inv₀, ← mul_inv, mul_comm, hμN, inv_one]
      set X' : primeFormUnitary h (idGram K n) :=
        ⟨Matrix.GeneralLinearGroup.scalar (Fin n) u * X,
          mul_mem (scalar_mem_primeFormUnitary h huN) X.2⟩ with hX'
      have hX'M : ((X' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          μ⁻¹ • ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        simp only [hX', Units.val_mul, coe_scalar_gl, Matrix.smul_mul, Matrix.one_mul, hu,
          Units.val_mk0]
      have hcX' : primeFormConjHom h (idGram K n) X' = primeFormConjHom h (idGram K n) X := by
        have h1 : X' = ⟨_, scalar_mem_primeFormUnitary h huN⟩ * X := rfl
        rw [h1, map_mul, conj_scalar_eq_one h _ rfl, one_mul]
      have hXM : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1 := by
        rw [← Units.val_pow_eq_pow_val]; exact hXp
      have hX'p : (X' : GL (Fin n) K) ^ p = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, hX'M, smul_pow, hXM, smul_smul, inv_pow, hμp,
          inv_mul_cancel₀ hα, one_smul, Units.val_one]
      have hX'Y : (X' : GL (Fin n) K) * Y = Y * X' := by
        show Matrix.GeneralLinearGroup.scalar (Fin n) u * (X : GL (Fin n) K) * Y =
          Y * (Matrix.GeneralLinearGroup.scalar (Fin n) u * X)
        calc Matrix.GeneralLinearGroup.scalar (Fin n) u * (X : GL (Fin n) K) * Y
            = Matrix.GeneralLinearGroup.scalar (Fin n) u * ((X : GL (Fin n) K) * Y) := mul_assoc _ _ _
          _ = Matrix.GeneralLinearGroup.scalar (Fin n) u * ((Y : GL (Fin n) K) * X) := by rw [hcomm]
          _ = (Matrix.GeneralLinearGroup.scalar (Fin n) u * (Y : GL (Fin n) K)) * X :=
              (mul_assoc _ _ _).symm
          _ = ((Y : GL (Fin n) K) * Matrix.GeneralLinearGroup.scalar (Fin n) u) * X := by
              rw [(commute_scalar u (Y : GL (Fin n) K)).eq]
          _ = (Y : GL (Fin n) K) * (Matrix.GeneralLinearGroup.scalar (Fin n) u * X) := mul_assoc _ _ _
      have hind' : ∀ i j : ℕ, (primeFormConjHom h (idGram K n) X') ^ i *
          (primeFormConjHom h (idGram K n) Y) ^ j = 1 → p ∣ i ∧ p ∣ j := by
        rw [hcX']; exact hind
      have hindGL : ∀ a b : ℕ, (X' : GL (Fin n) K) ^ a * (Y : GL (Fin n) K) ^ b = 1 →
          p ∣ a ∧ p ∣ b := by
        intro a b hab
        apply hind' a b
        have h1 : X' ^ a * Y ^ b = 1 := Subtype.ext (by
          simpa only [Subgroup.coe_mul, SubgroupClass.coe_pow, OneMemClass.coe_one] using hab)
        rw [← map_pow, ← map_pow, ← map_mul, h1, map_one]
      left
      exact uniPlaneGen_of_comap_eq_top h (eq_top_of_abelian_pth_r h hp hpq hq (by omega) X'.2 Y.2
        hX'Y hX'p hYp hindGL (fun a b hab => rcent_word h (hcX' ▸ hXE) hYE hind' a b hab))
    ·
      have hY1 : ∀ c' : K, ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c' • 1 := by
        intro c' hc'
        have hc'0 : c' ≠ 0 := by
          rintro rfl
          have h1 : (((Y : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          rw [hc', zero_smul, Matrix.mul_zero] at h1
          exact zero_ne_one (congrFun (congrFun h1 ⟨0, hn0⟩) ⟨0, hn0⟩)
        have hYs : (Y : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c' hc'0) :=
          Units.ext (by rw [coe_scalar_gl, Units.val_mk0, hc'])
        exact hp1 (hind 0 1 (by rw [conj_scalar_eq_one h Y hYs]; simp)).2
      have hYp' : ((((Y : GL (Fin n) K)) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
        rw [hYp, Units.val_one]
      have hcX : RCent H ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        have := rcent_word h hXE hYE hind 1 0 (fun hd => hp1 hd.1)
        simpa using this
      have hcY : RCent H ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        have := rcent_word h hXE hYE hind 0 1 (fun hd => hp1 hd.2)
        simpa using this
      left
      exact uniPlaneGen_of_comap_eq_top h (eq_top_of_nonpth_pair_r h hp hp2 hpq hq X.2 Y.2 hcomm hXp
        hμ hYp' hY1 hcX hcY)
  · by_cases hnp : n = p
    · right
      refine ⟨hnp, fun hXY => hc1 ?_⟩
      have h1 : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [← Units.val_mul, ← Units.val_mul]
        exact congrArg (fun g : primeFormUnitary h (idGram K n) => ((g : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) hXY.symm
      rw [hYX] at h1
      have hM : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ 0 := by
        intro h0
        have h2 : (((X * Y : GL (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((((X * Y : GL (Fin n) K))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [Units.val_mul, h0, Matrix.zero_mul] at h2
        exact zero_ne_one (congrFun (congrFun h2 ⟨0, hn0⟩) ⟨0, hn0⟩)
      have h3 : (c - 1) • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 0 := by
        rw [sub_smul, one_smul, h1, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hM)
    · left
      obtain ⟨W, hW0, hWiso, hWX, hWY⟩ :=
        exists_isotropic_of_heis h hp hpq hn hnp X.2 Y.2 hα hXp hYp hYX hc1
      refine uniPlaneGen_of_isotropic h hℓ2 hn hp hpℓ hE hc hD hW0 hWiso ?_
      intro A hA
      let S : Subgroup (primeFormUnitary h (idGram K n)) :=
        (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256e.stabSubGL' W).comap
          (primeFormUnitary h (idGram K n)).subtype
      have hcXp : (primeFormConjHom h (idGram K n) X) ^ p = 1 := hE.2 _ hXE
      have hgen : Subgroup.zpowers (primeFormConjHom h (idGram K n) X) ⊔
          Subgroup.zpowers (primeFormConjHom h (idGram K n) Y) = E :=
        zpowers_sup_zpowers_eq_of_card_sq hp hE.2 hc hXE (ne_one_of_indep hp hind) hYE
          (notMem_zpowers_of_indep hp hcXp hind)
      have hS : ∀ B, primeFormConjHom h (idGram K n) B = 1 → B ∈ S := by
        intro B hB
        obtain ⟨u, -, hu⟩ := eq_scalar_of_conj_eq_one h hn B hB
        refine ⟨fun w hw => ?_, fun w hw => ?_⟩
        · show ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W
          rw [hu, coe_scalar_gl, Matrix.smul_mulVec, Matrix.one_mulVec]
          exact W.smul_mem _ hw
        · show ((((B : GL (Fin n) K))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W
          rw [hu, ← map_inv, coe_scalar_gl, Matrix.smul_mulVec, Matrix.one_mulVec]
          exact W.smul_mem _ hw
      have hXs : X ∈ S := by
        have hXp' : (X : GL (Fin n) K) ^ p =
            Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 α hα) :=
          Units.ext (by rw [hXp, coe_scalar_gl, Units.val_mk0])
        exact ⟨hWX, inv_mulVec_mem_of_pow_scalar hp.pos hXp' hWX⟩
      have hYs : Y ∈ S := by
        have hYp' : (Y : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) 1 := by
          rw [hYp, map_one]
        exact ⟨hWY, inv_mulVec_mem_of_pow_scalar hp.pos hYp' hWY⟩
      exact (mem_of_conj_mem_of_sup_eq h hgen hS hXs hYs hA).1

end InnDiag

section FieldOuter

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem map_suSub_le_uniPlaneClosure_of_ne (h : UnitaryFieldData ℓ f K) (hn : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) (hnq : (n, ℓ ^ (f / p)) ≠ (3, 2))
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (N : primeFormUnitary h (idGram K n))
    {e : MulAut (primeFormP h (idGram K n))} (he : e ∈ E) (he1 : e ≠ 1)
    (heN : e * primeFormConjHom h (idGram K n) N =
      primeFormConjHom h (idGram K n) N * primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) :
    ((suSub h (fixSubfield_unitaryFieldData h hp hp2 hσ) (fixSubfield_unitaryFieldData_bar h hp hp2 hσ)
        n).map (primeFormConjSU h _ N).toMonoidHom).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) ≤ uniPlaneClosure ℓ E := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  have hnq' : (m + 1, ℓ ^ (f / p)) ≠ (3, 2) := hnq
  have hgen₀ := CFSG.ClassicalGroups.UnitaryFlag.closure_pow_ringChar_gramSU_of_ne
    (n := m + 1) h₀ hnq'
  have hchar : ringChar (fixSubfield σ) = ℓ := by
    have : CharP (fixSubfield σ) ℓ := inferInstance
    exact ringChar.eq _ _
  set mk := QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K (m + 1))) (m + 1)) with hmk
  have hT : suSub h h₀ hbar (m + 1) = Subgroup.closure ((subfieldSU h h₀ hbar (m + 1)) ''
      {g | g ^ ringChar (fixSubfield σ) = 1}) := by
    rw [suSub, MonoidHom.range_eq_map, ← hgen₀, MonoidHom.map_closure]
  rw [hT, MonoidHom.map_closure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
  set y : primeFormP h (idGram K (m + 1)) := mk (subfieldSU h h₀ hbar (m + 1) g) with hy
  have hyR : y ∈ (subfieldPSU h h₀ hbar (m + 1)).range := ⟨(g : primeFormP h₀ _), rfl⟩
  have hfy : primeFormFieldHom h (isPrimeFormGram_one (n := m + 1)) σ y = y :=
    primeFormFieldHom_apply_of_mem_range h (m + 1) h₀ hbar (fun c hc => hc) hyR
  have hconj : mk ((primeFormConjSU h _ N).toMonoidHom (subfieldSU h h₀ hbar (m + 1) g)) =
      primeFormConjHom h (idGram K (m + 1)) N y := by
    rw [hy, hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, primeFormConjHom_mk]
    rfl
  rw [SetLike.mem_coe, hconj]
  have hfix : e (primeFormConjHom h (idGram K (m + 1)) N y) =
      primeFormConjHom h (idGram K (m + 1)) N y := by
    have h1 := congrArg (fun φ : MulAut (primeFormP h (idGram K (m + 1))) => φ y) heN
    simp only [MulAut.mul_apply] at h1
    rw [h1, hfy]
  refine mem_uniPlaneClosure he he1 hfix (n := 1) ?_
  have hgℓ : g ^ ℓ = 1 := by rwa [hchar] at hg
  rw [pow_one, ← map_pow, hy, ← map_pow, ← map_pow, hgℓ, map_one, map_one, map_one]

theorem map_suSub_le_uniPlaneClosure (h : UnitaryFieldData ℓ f K) (hn : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) (hq₀ : ℓ ^ (f / p) ≠ 2)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (N : primeFormUnitary h (idGram K n))
    {e : MulAut (primeFormP h (idGram K n))} (he : e ∈ E) (he1 : e ≠ 1)
    (heN : e * primeFormConjHom h (idGram K n) N =
      primeFormConjHom h (idGram K n) N * primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) :
    ((suSub h (fixSubfield_unitaryFieldData h hp hp2 hσ) (fixSubfield_unitaryFieldData_bar h hp hp2 hσ)
        n).map (primeFormConjSU h _ N).toMonoidHom).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) ≤ uniPlaneClosure ℓ E :=
  map_suSub_le_uniPlaneClosure_of_ne h hn hp hp2 hσ (fun h => hq₀ (congrArg Prod.snd h)) N he he1 heN

theorem uniPlaneGen_field_outer (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ ≠ 2)
    (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hD : ¬ E ≤ primeFormD h (idGram K n)) : UniPlaneGen ℓ E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hℓ : ℓ.Prime := Fact.out
  have hodd : ∀ m : ℕ, ℓ ^ m ≠ 2 := fun m h2 => by
    have hodd : Odd (ℓ ^ m) := (hℓ.odd_of_ne_two hℓ2).pow
    rw [h2] at hodd
    exact (by decide : ¬ Odd 2) hodd
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h3 => hodd f h3.2
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  set φF := primeFormFieldFactor h hC hn hne with hφF
  have hker : φF.ker = primeFormD h (idGram K n) := ker_primeFormFieldFactor h hC hn hne
  have hφD : ∀ x, φF x = 1 ↔ x ∈ primeFormD h (idGram K n) := fun x => by
    rw [← hker, MonoidHom.mem_ker]
  have hφf : ∀ τ : K ≃+* K, φF (primeFormFieldHom h hC τ) = τ := fun τ => by
    have := primeFormFieldFactor_apply h hC hn hne 1 τ
    rwa [map_one, one_mul] at this
  have hcyc : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hℓ K h.card).2
  have hfinAut : Finite (K ≃+* K) := Finite.of_injective (fun φ : K ≃+* K => (φ : K → K))
    DFunLike.coe_injective
  obtain ⟨a, haE, haD⟩ : ∃ a ∈ E, a ∉ primeFormD h (idGram K n) := by
    by_contra hcon
    push Not at hcon
    exact hD hcon
  have hap : a ^ p = 1 := hE.2 a haE
  have ha1 : a ≠ 1 := fun h1 => haD (h1 ▸ (primeFormD h (idGram K n)).one_mem)
  have hσ1 : φF a ≠ 1 := fun h1 => haD ((hφD a).1 h1)
  have hσord : orderOf (φF a) = p := orderOf_eq_prime (by rw [← map_pow, hap, map_one]) hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hne hp hp2 hpℓ a
      (orderOf_eq_prime hap ha1) _ rfl hσord
  set σ := φF a with hσdef
  set c₀ : MulAut (primeFormP h (idGram K n)) := primeFormConjHom h (idGram K n) M with hc₀
  set E' := E.map (MulAut.congr c₀⁻¹).toMonoidHom with hE'def
  suffices hE' : UniPlaneGen ℓ E' from (Inputs2311c.uniPlaneGen_map_congr c₀⁻¹ ℓ E).1 hE'
  have hE'el : IsElemAbelian p E' := isElemAbelian_map_congr c₀⁻¹ hE
  have hE'c : Nat.card E' = p ^ 2 := (card_map_congr c₀⁻¹ E).trans hc
  have hcongr : ∀ φ : MulAut (primeFormP h (idGram K n)), MulAut.congr c₀⁻¹ φ = c₀⁻¹ * φ * c₀ :=
    fun φ => rfl
  set fσ := primeFormFieldHom h hC σ with hfσ
  have hfσE : fσ ∈ E' := ⟨a, haE, by rw [MulEquiv.coe_toMonoidHom, hcongr]; exact hM⟩
  have hfσ1 : fσ ≠ 1 := fun h1 => hσ1 (by rw [← hφf σ, ← hfσ, h1, map_one])
  obtain ⟨b, hbE, hbz⟩ := exists_notMem_zpowers_of_card_sq hp hE'el.2 hE'c hfσE hfσ1
  have hbp : b ^ p = 1 := hE'el.2 b hbE
  have hτp : (φF b) ^ p = 1 := by rw [← map_pow, hbp, map_one]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
    (mem_zpowers_of_pow_eq_one_of_isCyclic hp hσord hτp)
  set cA := b * fσ ^ (-j) with hcAdef
  have hcAE : cA ∈ E' := E'.mul_mem hbE (E'.zpow_mem hfσE _)
  have hcAD : cA ∈ primeFormD h (idGram K n) := by
    rw [← hφD, hcAdef, map_mul, map_zpow, hφf, ← hj, ← _root_.zpow_add, add_neg_cancel,
      zpow_zero]
  have hcA1 : cA ≠ 1 := by
    intro h1
    apply hbz
    have : b = fσ ^ j := by
      rw [hcAdef, mul_eq_one_iff_eq_inv, ← _root_.zpow_neg, neg_neg] at h1
      exact h1
    rw [this]
    exact Subgroup.zpow_mem_zpowers _ _
  obtain ⟨A, hA⟩ := hcAD
  set e₂ := cA * fσ with he₂def
  have he₂E : e₂ ∈ E' := E'.mul_mem hcAE hfσE
  have he₂φ : φF e₂ = σ := by
    rw [he₂def, map_mul, (hφD cA).2 (by rw [← hA]; exact ⟨A, rfl⟩), one_mul, hφf]
  have he₂1 : e₂ ≠ 1 := fun h1 => hσ1 (by rw [← he₂φ, h1, map_one])
  have he₂ord : orderOf e₂ = p := orderOf_eq_prime (hE'el.2 e₂ he₂E) he₂1
  obtain ⟨hpf, -, -, -, -, N, hN⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hne hp hp2 hpℓ e₂
      he₂ord σ he₂φ hσord
  have hN' : (primeFormConjHom h (idGram K n) N)⁻¹ * e₂ * primeFormConjHom h (idGram K n) N = fσ := hN
  have hNe : e₂ * primeFormConjHom h (idGram K n) N = primeFormConjHom h (idGram K n) N * fσ := by
    rw [← hN']; group
  have h1N : fσ * primeFormConjHom h (idGram K n) 1 = primeFormConjHom h (idGram K n) 1 * fσ := by
    rw [map_one, mul_one, one_mul]
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσord with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσord
  set T := suSub h h₀ hbar n with hTdef
  have hq₀ : ℓ ^ (f / p) ≠ 2 := hodd _
  have hfeq : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
  set mk := QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) with hmk
  by_cases hTN : T.map (primeFormConjSU h _ N).toMonoidHom ≠ T
  ·
    have hpair := subfieldPairSUOdd_of_ne_two ℓ f (f / p) K h (fixSubfield σ) h₀ hbar p hp hp2 hfeq hq₀
      n hn N hTN
    have hle1 : (T.map (primeFormConjSU h _ (1 : primeFormUnitary h (idGram K n))).toMonoidHom).map mk ≤
        uniPlaneClosure ℓ E' :=
      map_suSub_le_uniPlaneClosure h (by omega) hp hp2 hσord hq₀ 1 hfσE hfσ1 h1N
    have hle2 : (T.map (primeFormConjSU h _ N).toMonoidHom).map mk ≤ uniPlaneClosure ℓ E' :=
      map_suSub_le_uniPlaneClosure h (by omega) hp hp2 hσord hq₀ N he₂E he₂1 hNe
    have hT1 : T.map (primeFormConjSU h _ (1 : primeFormUnitary h (idGram K n))).toMonoidHom = T := by
      have : (primeFormConjSU h _ (1 : primeFormUnitary h (idGram K n))).toMonoidHom =
          MonoidHom.id _ := by
        refine MonoidHom.ext fun g => Subtype.ext ?_
        change ((1 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) * (g : GL (Fin n) K) *
          ((1 : primeFormUnitary h (idGram K n)) : GL (Fin n) K)⁻¹ = g
        simp
      rw [this, Subgroup.map_id]
    rw [hT1] at hle1
    rw [UniPlaneGen, eq_top_iff]
    intro x _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hg : g ∈ Subgroup.closure ((T : Set (gramSU h (idGram K n))) ∪
        (T.map (primeFormConjSU h _ N).toMonoidHom : Set (gramSU h (idGram K n)))) := by
      rw [hpair]; exact Subgroup.mem_top g
    rw [← Subgroup.sup_eq_closure] at hg
    have h2 := Subgroup.mem_map_of_mem mk hg
    rw [Subgroup.map_sup] at h2
    exact (sup_le hle1 hle2) h2
  ·
    push Not at hTN
    exfalso
    apply hcA1
    have hrange := range_subfieldPSU_eq_map h h₀ hbar n
    rw [← hTdef] at hrange
    have hfixR : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, fσ x = x := fun x hx =>
      primeFormFieldHom_apply_of_mem_range h n h₀ hbar (fun c hc => hc) hx
    have hTN' : T.map (primeFormConjSU h _ N⁻¹).toMonoidHom = T := by
      conv_lhs => rw [← hTN]
      rw [Subgroup.map_map]
      have : (primeFormConjSU h _ N⁻¹).toMonoidHom.comp (primeFormConjSU h _ N).toMonoidHom =
          MonoidHom.id _ := by
        refine MonoidHom.ext fun g => Subtype.ext ?_
        change ((N⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K) *
          (((N : GL (Fin n) K)) * (g : GL (Fin n) K) * (N : GL (Fin n) K)⁻¹) *
            ((N⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K)⁻¹ = g
        simp only [Subgroup.coe_inv, inv_inv]
        group
      rw [this, Subgroup.map_id]
    have hNinv : ∀ x ∈ (subfieldPSU h h₀ hbar n).range,
        (primeFormConjHom h (idGram K n) N)⁻¹ x ∈ (subfieldPSU h h₀ hbar n).range := by
      intro x hx
      rw [hrange] at hx ⊢
      obtain ⟨s, hs, rfl⟩ := hx
      refine ⟨(primeFormConjSU h _ N⁻¹) s, ?_, ?_⟩
      · rw [← hTN']; exact ⟨s, hs, rfl⟩
      · rw [← map_inv]
        change mk (primeFormConjSU h _ N⁻¹ s) = primeFormConjHom h (idGram K n) N⁻¹ (mk s)
        rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, primeFormConjHom_mk]
        rfl
    have hfixA : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, cA x = x := by
      intro x hx
      have hx' := hNinv x hx
      have he₂x : e₂ x = x := by
        have h1 : e₂ = primeFormConjHom h (idGram K n) N * fσ * (primeFormConjHom h (idGram K n) N)⁻¹ := by
          rw [← hN']; group
        rw [h1, MulAut.mul_apply, MulAut.mul_apply, hfixR _ hx', ← MulAut.mul_apply, mul_inv_cancel,
          MulAut.one_apply]
      have hfx : fσ⁻¹ x = x := by
        conv_lhs => rw [← hfixR x hx]
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      have h2 : cA = e₂ * fσ⁻¹ := by rw [he₂def]; group
      rw [h2, MulAut.mul_apply, hfx, he₂x]
    obtain ⟨τ', -, hτ'⟩ := eq_primeFormFieldHom_of_fix h n h₀ hbar hn hne
      (fun h3 => hq₀ h3.2) cA hfixA
    have hτ'1 : τ' = 1 := by
      have h1 : φF cA = 1 := (hφD cA).2 (by rw [← hA]; exact ⟨A, rfl⟩)
      rw [hτ', hφf] at h1
      exact h1
    rw [hτ', hτ'1, map_one]

end FieldOuter

section Main

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem uniPlaneGen_inndiag (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ ≠ 2) (hn : 3 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpq : p ∣ ℓ ^ f + 1)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hD : E ≤ primeFormD h (idGram K n)) :
    UniPlaneGen ℓ E ∨ (n = p ∧ ∃ A B : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) A ∈ E ∧ primeFormConjHom h (idGram K n) B ∈ E ∧
        A * B ≠ B * A) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  obtain ⟨x, hxE, y, hyE, hy1, hxy⟩ := exists_independent_pair hp E hE.2 hc
  obtain ⟨A, rfl⟩ := hD hxE
  obtain ⟨B, rfl⟩ := hD hyE
  set cA := primeFormConjHom h (idGram K n) A with hcA
  set cB := primeFormConjHom h (idGram K n) B with hcB
  obtain ⟨α, hα, hAp⟩ := exists_pow_eq_smul_of_conj h hn A (hE.2 _ hxE)
  obtain ⟨β, hβ, hBp⟩ := exists_pow_eq_smul_of_conj h hn B (hE.2 _ hyE)
  have hcomm : cA * cB = cB * cA :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hxE⟩ ⟨_, hyE⟩)
  obtain ⟨c, hBA⟩ := exists_smul_comm_of_conj h hn A B hcomm
  have hcp : c ^ p = 1 := pow_eq_one_of_smul_comm_p hn0 hα hAp hBA
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hcp
    exact zero_ne_one hcp
  have hindAB : ∀ i j : ℕ, cA ^ i * cB ^ j = 1 → p ∣ i ∧ p ∣ j := fun i j hij =>
    dvd_of_pow_mul_pow_eq_one_p hp (hE.2 _ hxE) (hE.2 _ hyE) hy1 hxy hij
  have hcAB : Commute cA cB := hcomm
  have hpK : p ∣ Nat.card K - 1 := by
    have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
    have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hl
    have key : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      have h2 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hl _)
      zify [hq1, h2]
      ring
    rw [h.card_eq_sq, key]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨a, b, hab, ν, hν⟩ := exists_pth_power_word hp hpK hα hβ
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hν
    exact mul_ne_zero (pow_ne_zero _ hα) (pow_ne_zero _ hβ) hν.symm
  have hαN : h.bar α * α = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) A.2 hAp
  have hβN : h.bar β * β = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) B.2 hBp
  have hαβN : (α ^ a * β ^ b) ^ (ℓ ^ f + 1) = 1 := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul, pow_mul,
      planeW_pow_card_succ h hαN, planeW_pow_card_succ h hβN, one_pow, one_pow, one_mul]
  have hνN : h.bar ν * ν = 1 := bar_mul_eq_one_of_pow_eq h hp hp2 hpq hν0 hν hαβN
  set u : Kˣ := Units.mk0 ν⁻¹ (inv_ne_zero hν0) with hu
  have huN : h.norm (u : K) = 1 := by
    rw [UnitaryFieldData.norm, hu, Units.val_mk0, map_inv₀, ← mul_inv, mul_comm, hνN, inv_one]
  set S : primeFormUnitary h (idGram K n) :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin n) u, scalar_mem_primeFormUnitary h huN⟩ with hS
  have hcS : primeFormConjHom h (idGram K n) S = 1 := conj_scalar_eq_one h S rfl
  set Y₀ : primeFormUnitary h (idGram K n) := S * (A ^ a * B ^ b) with hY₀
  have hY₀E : primeFormConjHom h (idGram K n) Y₀ ∈ E := by
    rw [hY₀, map_mul, hcS, one_mul, map_mul, map_pow, map_pow]
    exact E.mul_mem (E.pow_mem hxE a) (E.pow_mem hyE b)
  have hcY₀ : primeFormConjHom h (idGram K n) Y₀ = cA ^ a * cB ^ b := by
    rw [hY₀, map_mul, hcS, one_mul, map_mul, map_pow, map_pow]
  have hAM : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1 := by
    rw [← Units.val_pow_eq_pow_val]; exact hAp
  have hBM : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1 := by
    rw [← Units.val_pow_eq_pow_val]; exact hBp
  have hY₀M : ((Y₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ν⁻¹ • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ a *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ b) := by
    simp only [hY₀, hS, Subgroup.coe_mul, SubgroupClass.coe_pow, Units.val_mul,
      Units.val_pow_eq_pow_val, coe_scalar_gl, hu, Units.val_mk0, Matrix.smul_mul, Matrix.one_mul]
  have hY₀p : (Y₀ : GL (Fin n) K) ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hY₀M, smul_pow, pow_word_p hp hp2 hAM hBM hBA hcp a b, ← hν,
      smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hν0), one_smul, Units.val_one]
  by_cases hpb : p ∣ b
  ·
    have hpa : ¬ p ∣ a := fun hpa => hab ⟨hpa, hpb⟩
    have hind : ∀ i j : ℕ, cB ^ i * (primeFormConjHom h (idGram K n) Y₀) ^ j = 1 →
        p ∣ i ∧ p ∣ j := by
      intro i j hij
      rw [hcY₀, pow_mul_pow_pow_of_comm hcAB a b j] at hij
      have h1 : cA ^ (a * j) * cB ^ (i + b * j) = 1 := by
        rw [← hij, pow_add]
        calc cA ^ (a * j) * (cB ^ i * cB ^ (b * j)) = cB ^ i * (cA ^ (a * j) * cB ^ (b * j)) := by
              rw [← mul_assoc, ← mul_assoc, ((hcAB.pow_pow (a * j) i).eq)]
          _ = _ := rfl
      obtain ⟨h2, h3⟩ := hindAB _ _ h1
      have hj : p ∣ j := ((Nat.Prime.dvd_mul hp).1 h2).resolve_left hpa
      exact ⟨(Nat.dvd_add_right (dvd_mul_of_dvd_right hj b)).1 (by rw [add_comm]; exact h3), hj⟩
    have hYB : ((Y₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (c ^ a)⁻¹ • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Y₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      rw [hY₀M, Matrix.smul_mul, planeW_comm_caseII hBA hc0 a b, Matrix.mul_smul, smul_comm]
    rcases uniPlaneGen_of_pair h hℓ2 hn hp hp2 hpℓ hpq hE hc (by exact hD) B Y₀ hyE hY₀E hind hβ hBp hY₀p
        hYB with hU | ⟨hnp, hne⟩
    · exact Or.inl hU
    · exact Or.inr ⟨hnp, B, Y₀, hyE, hY₀E, hne⟩
  ·
    have hind : ∀ i j : ℕ, cA ^ i * (primeFormConjHom h (idGram K n) Y₀) ^ j = 1 →
        p ∣ i ∧ p ∣ j := by
      intro i j hij
      rw [hcY₀, pow_mul_pow_pow_of_comm hcAB a b j, ← mul_assoc, ← pow_add] at hij
      obtain ⟨h2, h3⟩ := hindAB _ _ hij
      have hj : p ∣ j := ((Nat.Prime.dvd_mul hp).1 h3).resolve_left hpb
      exact ⟨(Nat.dvd_add_left (dvd_mul_of_dvd_right hj a)).1 h2, hj⟩
    have hYA : ((Y₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        c ^ b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Y₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      rw [hY₀M, Matrix.smul_mul, planeW_comm_caseI hBA a b, Matrix.mul_smul, smul_comm]
    rcases uniPlaneGen_of_pair h hℓ2 hn hp hp2 hpℓ hpq hE hc (by exact hD) A Y₀ hxE hY₀E hind hα hAp hY₀p
        hYA with hU | ⟨hnp, hne⟩
    · exact Or.inl hU
    · exact Or.inr ⟨hnp, A, Y₀, hxE, hY₀E, hne⟩

theorem uniPlaneGen_psu (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ ≠ 2)
    (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpq : p ∣ ℓ ^ f + 1)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) :
    UniPlaneGen ℓ E ∨ (E ≤ primeFormD h (idGram K n) ∧ n = p ∧ ∃ A B : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) A ∈ E ∧ primeFormConjHom h (idGram K n) B ∈ E ∧
        A * B ≠ B * A) := by
  by_cases hD : E ≤ primeFormD h (idGram K n)
  · rcases uniPlaneGen_inndiag h hℓ2 hn hp hp2 hpℓ hpq hE hc hD with hU | hH
    · exact Or.inl hU
    · exact Or.inr ⟨hD, hH⟩
  · exact Or.inl (uniPlaneGen_field_outer h hℓ2 hn hp hp2 hpℓ hE hc hD)

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256g

end
