module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement MatrixGroups Finset

variable {d : ℕ} {F : Type} [Field F]

private lemma t173UniComb_diag_eq (P : GL (Fin d) F) {G : Subgroup (GL (Fin d) F)}
    (hdiag : MDiagAt d F P G) {A : GL (Fin d) F} (hA : A ∈ G) :
    ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun i => MWt P A i) := by
  obtain ⟨D, hD⟩ := hdiag A hA
  rw [hD]
  congr 1
  funext i
  rw [MWt, hD, Matrix.diagonal_apply_eq]

private lemma t173UniComb_mwt_mul (P : GL (Fin d) F) {G : Subgroup (GL (Fin d) F)}
    (hdiag : MDiagAt d F P G) {A B : GL (Fin d) F} (hA : A ∈ G) (hB : B ∈ G) (i : Fin d) :
    MWt P (A * B) i = MWt P A i * MWt P B i := by
  have hAB : ((P * (A * B) * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        ((P * B * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
    rw [← Units.val_mul]
    congr 1
    group
  have hprod : ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        ((P * B * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun i => MWt P A i * MWt P B i) := by
    rw [t173UniComb_diag_eq P hdiag hA, t173UniComb_diag_eq P hdiag hB,
      Matrix.diagonal_mul_diagonal]
  show ((P * (A * B) * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i =
    ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i *
      ((P * B * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i
  rw [hAB, hprod, Matrix.diagonal_apply_eq]
  rfl

private lemma t173UniComb_mwt_pow (P : GL (Fin d) F) {G : Subgroup (GL (Fin d) F)}
    (hdiag : MDiagAt d F P G) {A : GL (Fin d) F} (hA : A ∈ G) (k : ℕ) (i : Fin d) :
    MWt P (A ^ k) i = (MWt P A i) ^ k := by
  induction k with
  | zero => simp [MWt]
  | succ k ih =>
      rw [pow_succ, t173UniComb_mwt_mul P hdiag (G.pow_mem hA k) hA i, ih, pow_succ]

private lemma t173UniComb_mwt_pow_eq_one {p : ℕ} (P : GL (Fin d) F) {G : Subgroup (GL (Fin d) F)}
    (hdiag : MDiagAt d F P G) {A : GL (Fin d) F} (hA : A ∈ G) (hpA : A ^ p = 1) (i : Fin d) :
    (MWt P A i) ^ p = 1 := by
  have h2 : MWt P (A ^ p) i = 1 := by rw [hpA, MWt]; simp
  rwa [t173UniComb_mwt_pow P hdiag hA p i] at h2

private lemma t173UniComb_mwt_ne_zero (P : GL (Fin d) F) {G : Subgroup (GL (Fin d) F)}
    (hdiag : MDiagAt d F P G) {A : GL (Fin d) F} (hA : A ∈ G) (i : Fin d) :
    MWt P A i ≠ 0 := by
  intro h0
  have hdet : ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det ≠ 0 :=
    (P * A * P⁻¹).det_ne_zero
  rw [t173UniComb_diag_eq P hdiag hA, Matrix.det_diagonal] at hdet
  exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) h0)

private noncomputable def t173UniComb_wgt (P : GL (Fin d) F) {G : Subgroup (GL (Fin d) F)}
    (hdiag : MDiagAt d F P G) : ↥G →* (Fin d → Fˣ) where
  toFun A := fun i => Units.mk0 (MWt P (A : GL (Fin d) F) i)
    (t173UniComb_mwt_ne_zero P hdiag A.2 i)
  map_one' := by
    ext i
    simp only [Units.val_mk0, Pi.one_apply]
    rw [MWt]
    simp
  map_mul' A B := by
    ext i
    simp only [Units.val_mk0, Pi.mul_apply, Units.val_mul]
    exact t173UniComb_mwt_mul P hdiag A.2 B.2 i

private def t173UniComb_muP (p : ℕ) (F : Type) [Field F] : Subgroup Fˣ where
  carrier := {c | c ^ p = 1}
  mul_mem' := by
    intro a b ha hb
    show (a * b) ^ p = 1
    rw [mul_pow, ha, hb, mul_one]
  one_mem' := by
    show (1 : Fˣ) ^ p = 1
    simp
  inv_mem' := by
    intro a ha
    show (a⁻¹) ^ p = 1
    rw [inv_pow, ha, inv_one]

private lemma t173UniComb_p_dvd_card_units {p n : ℕ} (hpq : p ∣ 2 ^ n + 1)
    (hF : Nat.card F = (2 ^ n) ^ 2) : p ∣ Nat.card Fˣ := by
  rw [Nat.card_units, hF]
  have h0 : ((2 ^ n + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpq
  have h1 : ((2 ^ n : ℕ) : ZMod p) = -1 := by
    have h : ((2 ^ n : ℕ) : ZMod p) + 1 = 0 := by simpa using h0
    exact eq_neg_iff_add_eq_zero.mpr h
  have h2 : (((2 ^ n) ^ 2 : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_pow, h1]
    ring
  have h3 : (((2 ^ n) ^ 2 - 1 : ℕ) : ZMod p) = 0 := by
    have hle : 1 ≤ (2 ^ n) ^ 2 := by
      have : 0 < (2 ^ n) ^ 2 := by positivity
      omega
    rw [Nat.cast_sub hle, h2]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp h3

private lemma t173UniComb_card_muP [Finite F] {p n : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hF : Nat.card F = (2 ^ n) ^ 2) : p ≤ Nat.card (t173UniComb_muP p F) := by
  have hpdvd : p ∣ Nat.card Fˣ := t173UniComb_p_dvd_card_units hpq hF
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, haord⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hpdvd
  have hmem : a ∈ t173UniComb_muP p F := by
    show a ^ p = 1
    rw [← orderOf_dvd_iff_pow_eq_one, haord]
  have hle : Subgroup.zpowers a ≤ t173UniComb_muP p F := Subgroup.zpowers_le.mpr hmem
  calc p = orderOf a := haord.symm
    _ = Nat.card (Subgroup.zpowers a) := (Nat.card_zpowers a).symm
    _ ≤ Nat.card (t173UniComb_muP p F) :=
        Nat.card_le_card_of_injective (fun x : ↥(Subgroup.zpowers a) =>
          (⟨x.1, hle x.2⟩ : t173UniComb_muP p F))
          (fun x y hxy => Subtype.ext
            (congrArg (fun z : t173UniComb_muP p F => (z : Fˣ)) hxy))

private noncomputable def t173UniComb_powHom (p : ℕ) {G : Subgroup (GL (Fin d) F)}
    (hcomm : ∀ A ∈ G, ∀ B ∈ G, A * B = B * A) : ↥G →* ↥G where
  toFun A := ⟨(A : GL (Fin d) F) ^ p, G.pow_mem A.2 p⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' A B := by
    apply Subtype.ext
    show ((A : GL (Fin d) F) * (B : GL (Fin d) F)) ^ p =
      (A : GL (Fin d) F) ^ p * (B : GL (Fin d) F) ^ p
    exact Commute.mul_pow (hcomm (A : GL (Fin d) F) A.2 (B : GL (Fin d) F) B.2) p

private lemma t173UniComb_card_ker [Finite F] {p n d : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hd : 1 ≤ d)
    {G : Subgroup (GL (Fin d) F)} (hZG : LargeEvenScalars (Fin d) F ≤ G)
    (htor : MToral p d F G)
    (hrank : p ^ max 3 (d - 3) ≤ (LargeEvenScalars (Fin d) F).relIndex G) :
    p ^ (max 3 (d - 3) + 1) ≤ Nat.card (t173UniComb_powHom (G := G) p htor.1).ker := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite ↥G := Subtype.finite
  set sc := LargeEvenScalars (Fin d) F with hsc
  set scG := sc.subgroupOf G with hscG
  set Λ := (t173UniComb_powHom (G := G) p htor.1).ker with hΛ
  haveI : Finite ↥Λ := Subtype.finite
  let πΛ : ↥Λ →* ↥G ⧸ scG := (QuotientGroup.mk' scG).comp Λ.subtype
  have hscalar : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ sc := by
    intro c
    rw [hsc, largeEvenScalars_def]
    exact MonoidHom.mem_range.mpr ⟨c, rfl⟩
  have hsurj : Function.Surjective πΛ := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective scG q
    obtain ⟨a, ha⟩ := htor.2 g g.2
    have hsa : Matrix.GeneralLinearGroup.scalar (Fin d) a ∈ G := hZG (hscalar a)
    let l : ↥G := ⟨Matrix.GeneralLinearGroup.scalar (Fin d) a * (g : GL (Fin d) F),
      G.mul_mem hsa g.2⟩
    have hl : l ∈ Λ := by
      rw [hΛ]
      show l ^ p = 1
      apply Subtype.ext
      show (Matrix.GeneralLinearGroup.scalar (Fin d) a * (g : GL (Fin d) F)) ^ p = 1
      exact ha
    refine ⟨⟨l, hl⟩, ?_⟩
    show QuotientGroup.mk' scG l = QuotientGroup.mk' scG g
    have hsplit : (⟨Matrix.GeneralLinearGroup.scalar (Fin d) a, hsa⟩ : ↥G) * g = l := rfl
    rw [← hsplit, map_mul]
    have hs1 : QuotientGroup.mk' scG
        (⟨Matrix.GeneralLinearGroup.scalar (Fin d) a, hsa⟩ : ↥G) = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).mpr (by
        rw [hscG, Subgroup.mem_subgroupOf]
        exact hscalar a)
    rw [hs1, one_mul]
  have hker_card : p ≤ Nat.card πΛ.ker := by
    refine (t173UniComb_card_muP hp hpq hF).trans ?_
    let f : t173UniComb_muP p F → πΛ.ker := fun c => by
      refine ⟨⟨⟨Matrix.GeneralLinearGroup.scalar (Fin d) (c : Fˣ),
        hZG (hscalar (c : Fˣ))⟩, ?_⟩, ?_⟩
      · rw [hΛ]
        show (⟨Matrix.GeneralLinearGroup.scalar (Fin d) (c : Fˣ),
          hZG (hscalar (c : Fˣ))⟩ : ↥G) ^ p = 1
        apply Subtype.ext
        show (Matrix.GeneralLinearGroup.scalar (Fin d) (c : Fˣ) : GL (Fin d) F) ^ p = 1
        have hpow : (Matrix.GeneralLinearGroup.scalar (Fin d) (c : Fˣ) : GL (Fin d) F) ^ p =
            Matrix.GeneralLinearGroup.scalar (Fin d) ((c : Fˣ) ^ p) :=
          (map_pow (Matrix.GeneralLinearGroup.scalar (Fin d)) (c : Fˣ) p).symm
        rw [hpow, show (c : Fˣ) ^ p = 1 from c.2]
        simp
      · show QuotientGroup.mk' scG ⟨Matrix.GeneralLinearGroup.scalar (Fin d) (c : Fˣ),
          hZG (hscalar (c : Fˣ))⟩ = 1
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).mpr (by
          rw [hscG, Subgroup.mem_subgroupOf]
          exact hscalar (c : Fˣ))
    have hf_inj : Function.Injective f := by
      intro c c' h
      have h2 : Matrix.GeneralLinearGroup.scalar (Fin d) (c : Fˣ) =
          Matrix.GeneralLinearGroup.scalar (Fin d) (c' : Fˣ) := by
        have := congrArg (fun x : πΛ.ker => (((x : ↥Λ) : ↥G) : GL (Fin d) F)) h
        exact this
      refine Subtype.ext ?_
      apply Units.ext
      have hmat : Matrix.scalar (Fin d) ((c : Fˣ) : F) =
          Matrix.scalar (Fin d) ((c' : Fˣ) : F) := by
        have := congrArg (fun M : GL (Fin d) F => (M : Matrix (Fin d) (Fin d) F)) h2
        simpa [Matrix.GeneralLinearGroup.coe_scalar] using this
      exact (Matrix.scalar_inj).mp hmat
    haveI : Finite πΛ.ker := Subtype.finite
    exact Nat.card_le_card_of_injective f hf_inj
  have hmain : Nat.card ↥Λ = Nat.card πΛ.ker * scG.index := by
    have h := Subgroup.card_ker_mul_card_range πΛ
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      ← Subgroup.index_eq_card] at h
    exact h.symm
  have hge : p * scG.index ≤ Nat.card ↥Λ := by
    rw [hmain]
    exact Nat.mul_le_mul_right _ hker_card
  calc p ^ (max 3 (d - 3) + 1) = p * p ^ max 3 (d - 3) := by rw [pow_succ, mul_comm]
    _ ≤ p * sc.relIndex G := Nat.mul_le_mul_left p hrank
    _ = p * scG.index := rfl
    _ ≤ Nat.card ↥Λ := hge

private lemma t173UniComb_exists_separating [Finite F] {p n d : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hF : Nat.card F = (2 ^ n) ^ 2) (hd : 5 ≤ d)
    (P : GL (Fin d) F) {G : Subgroup (GL (Fin d) F)}
    (hZG : LargeEvenScalars (Fin d) F ≤ G) (htor : MToral p d F G) (hdiag : MDiagAt d F P G)
    (hrank : p ^ max 3 (d - 3) ≤ (LargeEvenScalars (Fin d) F).relIndex G)
    (a a' : Fin d) (haa : a ≠ a') (hpair : ∀ A ∈ G, MWt P A a = MWt P A a')
    (I : Finset (Fin d)) (hI4 : 4 ≤ I.card) (haI : a ∉ I) (ha'I : a' ∉ I) :
    ∃ A ∈ G, A ^ p = 1 ∧ (∀ i, i ∉ I → MWt P A i = 1) ∧
      (∏ i ∈ I, MWt P A i = 1) ∧ ∃ s ∈ I, ∃ t ∈ I, s ≠ t ∧ MWt P A s ≠ MWt P A t := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (t173UniComb_muP p F) := Fintype.ofFinite _
  haveI : IsCyclic Fˣ := inferInstance
  have hIle : I.card ≤ d := by simpa using I.card_le_univ
  have hIlt : I.card < d := by
    have hsub : I ⊆ Finset.univ.erase a := by
      intro i hi
      rw [Finset.mem_erase]
      exact ⟨fun h => haI (h ▸ hi), Finset.mem_univ i⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin] at hle
    omega
  let Λ := (t173UniComb_powHom (G := G) p htor.1).ker
  let wΛ : ↥Λ →* (Fin d → Fˣ) := (t173UniComb_wgt P hdiag).comp Λ.subtype
  have hwΛ : ∀ (A : ↥Λ) (i : Fin d), ((wΛ A i : Fˣ) : F) = MWt P (A : GL (Fin d) F) i := by
    intro A i
    simp [wΛ, t173UniComb_wgt, Units.val_mk0]
  have hΛpow : ∀ (A : ↥Λ), (A : GL (Fin d) F) ^ p = 1 := by
    intro A
    exact congrArg Subtype.val (show (A : ↥G) ^ p = 1 from A.2)
  have hwΛ_pow : ∀ (A : ↥Λ) (i : Fin d), (wΛ A i) ^ p = 1 := by
    intro A i
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    rw [hwΛ A i]
    exact t173UniComb_mwt_pow_eq_one P hdiag (A : ↥G).2 (hΛpow A) i
  let J : Type := {i : Fin d // i ∉ I ∧ i ≠ a}
  have hJcard : Fintype.card J = d - I.card - 1 := by
    have h1 : Fintype.card J = (Finset.univ.filter (fun i : Fin d => i ∉ I ∧ i ≠ a)).card := by
      rw [Fintype.card_subtype]
    rw [h1]
    have h2 : (Finset.univ.filter (fun i : Fin d => i ∉ I ∧ i ≠ a)) =
        (Finset.univ \ I).erase a := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        Finset.mem_sdiff]
      tauto
    rw [h2, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haI⟩),
      Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ, Fintype.card_fin]
  have hprod_mem : ∀ A : ↥Λ, (∏ i ∈ I, wΛ A i) ∈ t173UniComb_muP p F :=
    fun A => (t173UniComb_muP p F).prod_mem (fun i _ => hwΛ_pow A i)
  let χ : ↥Λ →* (J → t173UniComb_muP p F) × t173UniComb_muP p F :=
    { toFun := fun A => (fun j => ⟨wΛ A j.1, hwΛ_pow A j.1⟩,
        ⟨∏ i ∈ I, wΛ A i, hprod_mem A⟩)
      map_one' := by
        apply Prod.ext
        · funext j; exact Subtype.ext (by simp [wΛ])
        · exact Subtype.ext (by simp)
      map_mul' := fun A B => by
        apply Prod.ext
        · funext j; exact Subtype.ext (by simp [wΛ, map_mul])
        · exact Subtype.ext (by simp [wΛ, map_mul, Finset.prod_mul_distrib]) }
  have hres_one : ∀ (A : ↥Λ) (j : J), A ∈ χ.ker → wΛ A j.1 = 1 := by
    intro A j hA
    have h := congrArg (fun z : (J → t173UniComb_muP p F) × t173UniComb_muP p F => z.1 j)
      (MonoidHom.mem_ker.mp hA)
    simpa [χ] using congrArg (fun u : t173UniComb_muP p F => (u : Fˣ)) h
  have hprod_one : ∀ (A : ↥Λ), A ∈ χ.ker → (∏ i ∈ I, wΛ A i) = 1 := by
    intro A hA
    have h := congrArg (fun z : (J → t173UniComb_muP p F) × t173UniComb_muP p F => z.2)
      (MonoidHom.mem_ker.mp hA)
    simpa [χ] using congrArg (fun u : t173UniComb_muP p F => (u : Fˣ)) h
  have hweights_of_ker : ∀ (A : ↥Λ), A ∈ χ.ker → ∀ i, i ∉ I → MWt P (A : GL (Fin d) F) i = 1 := by
    intro A hA i hi
    by_cases hia : i = a
    · subst hia
      have h1 : wΛ A (Subtype.mk a' (And.intro ha'I haa.symm) : J) = 1 :=
        hres_one A (Subtype.mk a' (And.intro ha'I haa.symm) : J) hA
      have h2 : MWt P (A : GL (Fin d) F) a' = 1 := by
        rw [← hwΛ A a']
        exact congrArg (fun u : Fˣ => (u : F)) h1
      rw [hpair (A : GL (Fin d) F) (A : ↥G).2]
      exact h2
    · have h1 : wΛ A (Subtype.mk i (And.intro hi hia) : J) = 1 :=
        hres_one A (Subtype.mk i (And.intro hi hia) : J) hA
      rw [← hwΛ A i]
      exact congrArg (fun u : Fˣ => (u : F)) h1
  have hprod_of_ker : ∀ (A : ↥Λ), A ∈ χ.ker → (∏ i ∈ I, MWt P (A : GL (Fin d) F) i) = 1 := by
    intro A hA
    have h1 : (∏ i ∈ I, wΛ A i) = 1 := hprod_one A hA
    have h2 : ((∏ i ∈ I, wΛ A i : Fˣ) : F) = 1 := by rw [h1]; rfl
    simpa only [Units.coe_prod, hwΛ A] using h2
  have hmu_le : Nat.card (t173UniComb_muP p F) ≤ p := by
    haveI : Fintype Fˣ := Fintype.ofFinite _
    have h := IsCyclic.card_pow_eq_one_le (α := Fˣ) (n := p) hp.pos
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simpa [t173UniComb_muP] using h
  have hχrange_le : Nat.card χ.range ≤ p ^ (d - I.card) := by
    have h1 : Nat.card χ.range ≤ Nat.card ((J → t173UniComb_muP p F) × t173UniComb_muP p F) :=
      Nat.card_le_card_of_injective (fun x : χ.range => (x.1 : (J → t173UniComb_muP p F) × _))
        (fun x y hxy => Subtype.ext hxy)
    have h2 : Nat.card ((J → t173UniComb_muP p F) × t173UniComb_muP p F) =
        Nat.card (t173UniComb_muP p F) ^ Fintype.card J * Nat.card (t173UniComb_muP p F) := by
      rw [Nat.card_prod, Nat.card_fun,
        show Nat.card J = Fintype.card J from Nat.card_eq_fintype_card]
    rw [h2, hJcard] at h1
    refine h1.trans ?_
    have h3 : p ^ (d - I.card - 1) * p = p ^ (d - I.card) := by
      rw [← pow_succ]
      congr 1
      omega
    calc Nat.card (t173UniComb_muP p F) ^ (d - I.card - 1) * Nat.card (t173UniComb_muP p F)
        ≤ p ^ (d - I.card - 1) * p :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hmu_le _) hmu_le
      _ = p ^ (d - I.card) := h3
  have hΛcard : p ^ (max 3 (d - 3) + 1) ≤ Nat.card ↥Λ := by
    simpa [Λ] using t173UniComb_card_ker (F := F) hp hpq hF (by omega : 1 ≤ d) hZG htor hrank
  have hker_ge : p ^ 2 ≤ Nat.card χ.ker := by
    have hcard := Subgroup.card_ker_mul_card_range χ
    have hexp : 2 + (d - I.card) ≤ max 3 (d - 3) + 1 := by omega
    have hpow : p ^ 2 * p ^ (d - I.card) ≤ p ^ (max 3 (d - 3) + 1) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right hp.pos hexp
    have h2 : Nat.card ↥Λ ≤ Nat.card χ.ker * p ^ (d - I.card) := by
      rw [← hcard]
      exact Nat.mul_le_mul_left _ hχrange_le
    have h1 : p ^ 2 * p ^ (d - I.card) ≤ Nat.card χ.ker * p ^ (d - I.card) :=
      (hpow.trans hΛcard).trans h2
    exact Nat.le_of_mul_le_mul_right h1 (pow_pos hp.pos _)
  have hnotall : ∃ A : ↥Λ, A ∈ χ.ker ∧
      ¬ (∀ i ∈ I, ∀ j ∈ I, MWt P (A : GL (Fin d) F) i = MWt P (A : GL (Fin d) F) j) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
    have hinj : Nat.card χ.ker ≤ Nat.card (t173UniComb_muP p F) := by
      refine Nat.card_le_card_of_injective
        (fun A : χ.ker => (⟨Units.mk0 (MWt P (A.1 : GL (Fin d) F) i₀)
            (t173UniComb_mwt_ne_zero P hdiag (A.1 : ↥G).2 i₀),
          by
            apply Units.ext
            simpa using
              t173UniComb_mwt_pow_eq_one P hdiag (A.1 : ↥G).2 (hΛpow A.1) i₀⟩ :
            t173UniComb_muP p F)) ?_
      intro A B hAB
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      have hA1 := hweights_of_ker A.1 A.2
      have hB1 := hweights_of_ker B.1 B.2
      have hconj : P * (A.1 : GL (Fin d) F) * P⁻¹ = P * (B.1 : GL (Fin d) F) * P⁻¹ := by
        apply Units.ext
        rw [t173UniComb_diag_eq P hdiag (A.1 : ↥G).2, t173UniComb_diag_eq P hdiag (B.1 : ↥G).2]
        congr 1
        funext i
        by_cases hi : i ∈ I
        · rw [hcon A.1 A.2 i hi i₀ hi₀, hcon B.1 B.2 i hi i₀ hi₀]
          simpa using congrArg (fun z : t173UniComb_muP p F => ((z : Fˣ) : F)) hAB
        · rw [hA1 i hi, hB1 i hi]
      have := congrArg (fun M : GL (Fin d) F => P⁻¹ * M * P) hconj
      rw [show P⁻¹ * (P * (A.1 : GL (Fin d) F) * P⁻¹) * P = (A.1 : GL (Fin d) F) by group,
        show P⁻¹ * (P * (B.1 : GL (Fin d) F) * P⁻¹) * P = (B.1 : GL (Fin d) F) by group] at this
      exact this
    have h2p : p ^ 2 ≤ p := hker_ge.trans (hinj.trans hmu_le)
    have hpgt : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  obtain ⟨A, hAker, hnonconst⟩ := hnotall
  push Not at hnonconst
  obtain ⟨s, hs, t, ht, hst⟩ := hnonconst
  have hstne : s ≠ t := fun h => hst (by rw [h])
  exact ⟨(A : GL (Fin d) F), (A : ↥G).2, hΛpow A, hweights_of_ker A hAker,
    hprod_of_ker A hAker, s, hs, t, ht, hstne, hst⟩

theorem uni_comb {p n d : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d)
    (hd : 5 ≤ d) (P : GL (Fin d) F) {G : Subgroup (GL (Fin d) F)}
    (hZG : LargeEvenScalars (Fin d) F ≤ G) (hel : MElemMod p d F G) (htor : MToral p d F G)
    (hdiag : MDiagAt d F P G)
    (hrank : p ^ max 3 (d - 3) ≤ (LargeEvenScalars (Fin d) F).relIndex G)
    (a a' : Fin d) (haa : a ≠ a') (hpair : ∀ A ∈ G, MWt P A a = MWt P A a')
    (I : Finset (Fin d)) (hI2 : 2 ≤ I.card) (hI3 : I.card ≤ 3 → 2 ≤ n)
    (A₀ : GL (Fin d) F) (hA₀ : A₀ ∈ G) (hlev : ∃ i₀ ∈ I, ∀ i, i ∈ I ↔ MWt P A₀ i = MWt P A₀ i₀)
    (hD : ∀ A ∈ G, (∀ i ∈ I, ∀ j ∈ I, MWt P A i = MWt P A j) →
      ∃ (c : Fˣ) (k : ℕ), A = Matrix.GeneralLinearGroup.scalar (Fin d) c * A₀ ^ k)
    (hsing : 2 ≤ n → ∀ i j : Fin d, i ∉ I → j ∉ I → i ≠ j → MWt P A₀ i ≠ MWt P A₀ j) :
    ∃ s t : Fin d, s ∈ I ∧ t ∈ I ∧ s ≠ t ∧
      ((∀ A ∈ G, MWt P A s = MWt P A t) ∨
        ∃ A ∈ G, (P * A * P⁻¹) ∈ UniBlockSet n d F I ∧ A ^ p = 1 ∧ MWt P A s ≠ MWt P A t) := by
  by_cases haI : a ∈ I
  · obtain ⟨i₀, hi₀, hiff⟩ := hlev
    have ha'I : a' ∈ I := by
      rw [hiff a']
      rw [← hpair A₀ hA₀]
      exact (hiff a).1 haI
    exact ⟨a, a', haI, ha'I, haa, Or.inl (fun A hA => hpair A hA)⟩
  · obtain ⟨i₀, hi₀, hiff⟩ := hlev
    have ha'I : a' ∉ I := by
      intro h
      apply haI
      rw [hiff a]
      rw [hpair A₀ hA₀]
      exact (hiff a').1 h
    by_cases hn2 : 2 ≤ n
    · exact absurd (hpair A₀ hA₀) (hsing hn2 a a' haI ha'I haa)
    · have hI4 : 4 ≤ I.card := by
        by_contra h
        exact hn2 (hI3 (by omega))
      obtain ⟨A, hAG, hAp, hw1, hwp, s, hs, t, ht, hst, hwt⟩ :=
        t173UniComb_exists_separating hp hpq hF hd P hZG htor hdiag hrank a a' haa hpair I hI4
          haI ha'I
      refine ⟨s, t, hs, ht, hst, Or.inr ⟨A, hAG, ?_, hAp, hwt⟩⟩
      have hdiagA := t173UniComb_diag_eq P hdiag hAG
      refine ⟨?_, ?_⟩
      · rw [show UniSU n d F = StatedSU d (2 ^ n) F from rfl,
          CFSG.PGLModel.statedSU_eq_closure_det]
        apply Subgroup.subset_closure
        refine ⟨?_, ?_⟩
        · apply Units.ext
          show ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det = 1
          rw [hdiagA, Matrix.det_diagonal]
          rw [← Finset.prod_subset (Finset.subset_univ I) (fun x _ hx => hw1 x hx)]
          exact hwp
        · rw [hdiagA, Matrix.diagonal_map (f := fun x : F => x ^ (2 ^ n))
              (by norm_num : (0 : F) ^ (2 ^ n) = 0),
            Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
          rw [show (fun i => (MWt P A i) ^ (2 ^ n) * MWt P A i) = fun _ => (1 : F) from by
            funext i
            obtain ⟨k, hk⟩ := hpq
            have hpw : (MWt P A i) ^ p = 1 := t173UniComb_mwt_pow_eq_one P hdiag hAG hAp i
            calc (MWt P A i) ^ (2 ^ n) * MWt P A i = (MWt P A i) ^ (2 ^ n + 1) := by
                  rw [pow_succ]
              _ = (MWt P A i) ^ (p * k) := by rw [hk]
              _ = ((MWt P A i) ^ p) ^ k := by rw [pow_mul]
              _ = 1 := by rw [hpw, one_pow]]
          rw [Matrix.diagonal_one]
      · intro i j hij
        rw [hdiagA]
        by_cases h : i = j
        · subst h
          rw [Matrix.diagonal_apply_eq, if_pos rfl]
          exact hw1 i (hij.elim id id)
        · rw [Matrix.diagonal_apply_ne _ h, if_neg h]

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
