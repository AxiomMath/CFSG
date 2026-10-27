module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcF4Cent
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcE6W
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcCentTwAbstract
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralRankOne
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedTorus

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ExceptionalOrders
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross (mactC mactCHom mactC_one mactC_mul mactC_add mactC_one_sub mactC_vecTC vecTC)

section TwE6

variable (K : Type) [Field K] [Finite K] (σ : K →+* K)

@[expose] def Cq (q : ℕ) : Subgroup Kˣ := (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker

theorem card_Cq {q : ℕ} (hq : 1 < q) (hK : Nat.card K = q ^ 2) : Nat.card (Cq K q) = q - 1 := by
  rw [Cq, IsCyclic.card_powMonoidHom_ker, Nat.card_units, hK]
  refine Nat.gcd_eq_right ?_
  have : q - 1 ∣ q ^ 2 - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 2
  exact this

theorem sigma_Cq {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) {x : Kˣ} (hx : x ∈ Cq K q) :
    Units.map σ.toMonoidHom x = x := by
  have h1 : x ^ q = x := by
    have h2 : x ^ (q - 1) = 1 := hx
    calc x ^ q = x ^ (q - 1 + 1) := by rw [Nat.sub_add_cancel hq.le]
      _ = x := by rw [pow_succ, h2, one_mul]
  refine Units.ext ?_
  rw [Units.coe_map]
  show σ (x : K) = x
  rw [hσ, ← Units.val_pow_eq_pow_val, h1]

@[expose] def oi (k : Fin 6) : Fin 4 := TwistTag.orbitIndex TwistTag.E6 k

@[expose] def unfoldE (q : ℕ) : (Fin 4 → ↥(Cq K q)) →* (Fin 6 → Kˣ) where
  toFun t k := (t (oi k) : Kˣ)
  map_one' := by funext k; rfl
  map_mul' s t := by funext k; rfl

theorem unfoldE_mem_compat {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (t : Fin 4 → ↥(Cq K q)) :
    unfoldE K q t ∈ compatSubgroup (t := TwistTag.E6) σ := by
  intro i
  show (t (oi (TwistTag.E6.perm i)) : Kˣ) = Units.map σ.toMonoidHom (t (oi i))
  have : oi (TwistTag.E6.perm i) = oi i := TwistTag.orbitIndex_perm TwistTag.E6 i
  rw [this, sigma_Cq K σ hq hσ (t _).2]

noncomputable abbrev N1 : Subgroup (ModGL Tag.E6 K) := graphFixedRootMonomial TwistTag.E6 K σ

theorem torusCoord_unfold_mem_N1 {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q)
    (t : Fin 4 → ↥(Cq K q)) :
    (torusCoordHom Tag.E6 K (unfoldE K q t) : ModGL Tag.E6 K) ∈ N1 K σ :=
  CFSG.RankThree.Chevalley.graphFixedRootTorus_le_graphFixedRootMonomial (t := TwistTag.E6) (K := K) (σ := σ)
    (compatTorus_le_graphFixedRootTorus σ
      ((mem_compatTorus σ).2 ⟨_, unfoldE_mem_compat K σ hq hσ t, rfl⟩))

@[expose] noncomputable def iota0 {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) :
    (Fin 4 → ↥(Cq K q)) →* ↥(N1 K σ) :=
  MonoidHom.codRestrict
    (((torusGroup Tag.E6 K).subtype).comp ((torusCoordHom Tag.E6 K).comp (unfoldE K q)))
    (N1 K σ) (fun t => torusCoord_unfold_mem_N1 K σ hq hσ t)

@[expose] def Mfold : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -2, 0; 0, -1, 2, -1; 0, 0, -1, 2]

@[expose] def MfoldInv : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 3, 4, 2; 3, 6, 8, 4; 2, 4, 6, 3; 1, 2, 3, 2]

theorem Mfold_mul : Mfold * MfoldInv = 1 := by decide +kernel

@[expose] def AcE6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, 0, -1, 0, 0, 0; 0, 2, 0, -1, 0, 0; -1, 0, 2, -1, 0, 0; 0, -1, -1, 2, -1, 0;
     0, 0, 0, -1, 2, -1; 0, 0, 0, 0, -1, 2]

theorem cartanE6_apply : ∀ i j : Fin 6, Tag.E6.cartan i j = AcE6 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def repE : Fin 4 → Fin 6 := ![0, 2, 3, 1]

theorem sum_fiber_eq : ∀ a b : Fin 4,
    ∑ i ∈ Finset.univ.filter (fun i : Fin 6 => oi i = b), AcE6 i (repE a) = Mfold b a := by
  decide +kernel

theorem prod_fold {G : Type*} [CommGroup G] (a : Fin 4) (t : Fin 4 → G) :
    ∏ i : Fin 6, t (oi i) ^ (Tag.E6.cartan i (repE a)) = ∏ b : Fin 4, t b ^ Mfold b a := by
  rw [← Finset.prod_fiberwise Finset.univ oi
    (fun i => t (oi i) ^ (Tag.E6.cartan i (repE a)))]
  refine Finset.prod_congr rfl fun b _ => ?_
  have h1 : ∀ i ∈ Finset.univ.filter (fun i : Fin 6 => oi i = b),
      t (oi i) ^ (Tag.E6.cartan i (repE a)) = t b ^ (Tag.E6.cartan i (repE a)) := fun i hi => by
    rw [(Finset.mem_filter.1 hi).2]
  rw [Finset.prod_congr rfl h1, prod_zpow_sum_aux]
  congr 1
  simp only [cartanE6_apply]
  exact sum_fiber_eq a b

theorem iota0_injective {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) :
    Function.Injective (iota0 K σ hq hσ) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have h0 : (torusCoordHom Tag.E6 K (unfoldE K q t) : ModGL Tag.E6 K) = 1 :=
    congrArg Subtype.val ht
  have h1 : torusCoordHom Tag.E6 K (unfoldE K q t) = 1 := Subtype.ext h0
  have h2 := (torusCoordHom_eq_one_iff (τ := Tag.E6) (K := K) (unfoldE K q t)).1 h1
  have h3 : ∀ a : Fin 4, ∏ b : Fin 4, ((t b : Kˣ)) ^ Mfold b a = 1 := fun a => by
    have h5 : ∏ i : Fin 6, (unfoldE K q t i) ^ Tag.E6.cartan i (repE a) = 1 :=
      congrFun h2 (repE a)
    rw [← prod_fold a (fun b => (t b : Kˣ))]
    exact h5
  have h4 := eq_one_of_prod_zpow_eq_one Mfold_mul h3
  funext b
  exact Subtype.ext (congrFun h4 b)

theorem exists_wordW (τ : Tag) (w : WeylGroup τ) : ∃ l : List (Fin τ.rank), w = wordW τ l :=
  (coxeterSystem τ).wordProd_surjective w |>.imp fun l hl => hl.symm

@[expose] noncomputable def latMat (τ : Tag) (w : WeylGroup τ) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  Matrix.of fun i j => (w • (Pi.single j 1 : Fin τ.rank → ℤ)) i

theorem smul_eq_mulVec' (τ : Tag) (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (wordW τ l) • v = ((l.map (Smat τ)).prod).mulVec v := wordSmul τ l v

theorem latMat_wordW (τ : Tag) (l : List (Fin τ.rank)) :
    latMat τ (wordW τ l) = (l.map (Smat τ)).prod := by
  ext i j
  simp only [latMat, Matrix.of_apply, smul_eq_mulVec', Matrix.mulVec, dotProduct, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem N1_mem_adjoint (g : ↥(N1 K σ)) : (g : ModGL Tag.E6 K) ∈ adjointGroup Tag.E6 K :=
  (graphFixedRootGroup_le TwistTag.E6 K σ (graphFixedRootMonomial_le TwistTag.E6 K σ g.2)).1

theorem N1_mem_monomial (g : ↥(N1 K σ)) : (g : ModGL Tag.E6 K) ∈ monomialSubgroup Tag.E6 K :=
  graphFixedMonomial_le_monomialSubgroup TwistTag.E6 K σ g.2.1

@[expose] noncomputable def jHom : ↥(N1 K σ) →* ↥(monomialSub Tag.E6 K) where
  toFun g := ⟨⟨g.1, N1_mem_adjoint K σ g⟩, N1_mem_monomial K σ g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem jHom_coe (g : ↥(N1 K σ)) :
    monoι Tag.E6 K (jHom K σ g) = (g : ModGL Tag.E6 K) := rfl

@[expose] noncomputable def psi1 : ↥(N1 K σ) →* WeylGroup Tag.E6 :=
  graphFixedRootWeylHom TwistTag.E6 K σ

theorem psi1_eq (g : ↥(N1 K σ)) :
    monomialSubHom (τ := Tag.E6) (K := K) (jHom K σ g) = psi1 K σ g := rfl

theorem psi1_mem (g : ↥(N1 K σ)) : psi1 K σ g ∈ relWeylTwist TwistTag.E6 := by
  have : psi1 K σ g ∈ (graphFixedRootWeylHom TwistTag.E6 K σ).range := MonoidHom.mem_range.2 ⟨g, rfl⟩
  rwa [graphFixedRootWeylHom_range] at this

theorem jHom_iota0 {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (t : Fin 4 → ↥(Cq K q)) :
    jHom K σ (iota0 K σ hq hσ t) = torusN Tag.E6 K (unfoldE K q t) := by
  apply monoι_injective Tag.E6 K
  rw [jHom_coe]
  exact (monoι_torusN Tag.E6 K _).symm

theorem psi1_iota0 {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (t : Fin 4 → ↥(Cq K q)) :
    psi1 K σ (iota0 K σ hq hσ t) = 1 := by
  rw [← psi1_eq, jHom_iota0]
  exact psi_torusN Tag.E6 K _

theorem conj_coord_word (g : ↥(N1 K σ)) (l : List (Fin Tag.E6.rank))
    (hl : psi1 K σ g = wordW Tag.E6 l) (c : Fin Tag.E6.rank → Kˣ) :
    (g : ModGL Tag.E6 K) * (torusCoordHom Tag.E6 K c : ModGL Tag.E6 K) * (g : ModGL Tag.E6 K)⁻¹ =
      (torusCoordHom Tag.E6 K (mact K (RM6 l) c) : ModGL Tag.E6 K) := by
  have h := conj_N_word Tag.E6 K l ((psi1_eq K σ g).trans hl) c
  have h2 := congrArg (monoι Tag.E6 K) h
  rw [map_mul, map_mul, map_inv, jHom_coe, monoι_torusN, monoι_torusN] at h2
  exact h2

theorem prod_zpow_fiber {G : Type*} [CommGroup G] (c : Fin 4 → G) (e : Fin 6 → ℤ) :
    ∏ j : Fin 6, c (oi j) ^ e j =
      ∏ b : Fin 4, c b ^ (∑ j ∈ Finset.univ.filter (fun j : Fin 6 => oi j = b), e j) := by
  rw [← Finset.prod_fiberwise Finset.univ oi (fun j => c (oi j) ^ e j)]
  refine Finset.prod_congr rfl fun b _ => ?_
  have h1 : ∀ j ∈ Finset.univ.filter (fun j : Fin 6 => oi j = b),
      c (oi j) ^ e j = c b ^ e j := fun j hj => by rw [(Finset.mem_filter.1 hj).2]
  rw [Finset.prod_congr rfl h1, prod_zpow_sum_aux]

theorem mact_unfold {q : ℕ} (M : Matrix (Fin 6) (Fin 6) ℤ) (Mb : Matrix (Fin 4) (Fin 4) ℤ)
    (h : ∀ k b, ∑ j ∈ Finset.univ.filter (fun j : Fin 6 => oi j = b), M k j = Mb (oi k) b)
    (t : Fin 4 → ↥(Cq K q)) :
    mact K M (unfoldE K q t) = unfoldE K q (mactC Mb t) := by
  funext k
  show ∏ j : Fin 6, ((t (oi j) : Kˣ)) ^ M k j = ((∏ b : Fin 4, t b ^ Mb (oi k) b : ↥(Cq K q)) : Kˣ)
  rw [prod_zpow_fiber (fun b => (t b : Kˣ)) (M k)]
  have := map_prod (Cq K q).subtype (fun b => t b ^ Mb (oi k) b) Finset.univ
  simp only [h k]
  simpa [map_zpow] using this.symm

theorem fold_cond (g : ↥(N1 K σ)) (l : List (Fin Tag.E6.rank)) (lb : List (Fin Tag.F4.rank))
    (hl : psi1 K σ g = wordW Tag.E6 l)
    (hlb : foldedWeylEquiv TwistTag.E6 ⟨psi1 K σ g, psi1_mem K σ g⟩ = wordW Tag.F4 lb) :
    ∀ (k : Fin 6) (b : Fin 4),
      ∑ j ∈ Finset.univ.filter (fun j : Fin 6 => oi j = b), RM6 l k j =
        ((lb.map (Smat Tag.F4)).prod) (oi k) b := by
  intro k b
  have h := smul_foldMap_foldedWeylEquiv TwistTag.E6 ⟨psi1 K σ g, psi1_mem K σ g⟩
    (Pi.single b 1 : Fin TwistTag.E6.foldedTag.rank → ℤ)
  have hcoe : ((⟨psi1 K σ g, psi1_mem K σ g⟩ : relWeylTwist TwistTag.E6) :
      WeylGroup TwistTag.E6.tag) = wordW TwistTag.E6.tag l := hl
  have hlb' : foldedWeylEquiv TwistTag.E6 ⟨psi1 K σ g, psi1_mem K σ g⟩ =
      wordW TwistTag.E6.foldedTag lb := hlb
  rw [hcoe, hlb'] at h
  have e1 : (wordW TwistTag.E6.tag l) • TwistTag.E6.foldMap (Pi.single b 1) =
      (SM6 l).mulVec (TwistTag.E6.foldMap (Pi.single b 1)) :=
    smul_eq_mulVec' TwistTag.E6.tag l _
  have e2 : TwistTag.E6.foldMap ((wordW TwistTag.E6.foldedTag lb) •
      (Pi.single b 1 : Fin TwistTag.E6.foldedTag.rank → ℤ)) =
      TwistTag.E6.foldMap ((SM lb).mulVec (Pi.single b 1)) :=
    congrArg _ (smul_eq_mulVec' TwistTag.E6.foldedTag lb _)
  rw [e1, e2] at h
  have h2 := congrFun h k
  have hfm1 : ∀ x : Fin 6, TwistTag.E6.foldMap (Pi.single b 1) x =
      if oi x = b then 1 else 0 := fun x =>
    (TwistTag.foldMap_apply_apply TwistTag.E6 (Pi.single b 1) x).trans (by
      exact Pi.single_apply b (1 : ℤ) _)
  have hfm2 : TwistTag.E6.foldMap ((SM lb).mulVec (Pi.single b 1)) k = SM lb (oi k) b :=
    (TwistTag.foldMap_apply_apply TwistTag.E6 _ k).trans (by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, oi])
  simp only [Matrix.mulVec, dotProduct] at h2
  rw [hfm2] at h2
  calc ∑ j ∈ Finset.univ.filter (fun j : Fin 6 => oi j = b), RM6 l k j
      = ∑ j : Fin 6, SM6 l k j * TwistTag.E6.foldMap (Pi.single b 1) j := by
        rw [RM6_eq_SM6, Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hfm1 j]
        split_ifs <;> simp
    _ = SM lb (oi k) b := h2

@[expose] noncomputable def foldEquiv : ↥(relWeylTwist TwistTag.E6) ≃* WeylGroup Tag.F4 :=
  foldedWeylEquiv TwistTag.E6

@[expose] noncomputable def foldMat (w : WeylGroup TwistTag.E6.tag) :
    Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  open Classical in
  if h : w ∈ relWeylTwist TwistTag.E6 then latMat Tag.F4 (foldEquiv ⟨w, h⟩) else 1

theorem foldMat_of_mem {w : WeylGroup TwistTag.E6.tag} (h : w ∈ relWeylTwist TwistTag.E6) :
    foldMat w = latMat Tag.F4 (foldEquiv ⟨w, h⟩) := by
  unfold foldMat
  rw [dif_pos h]

theorem conj_iota0 {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (g : ↥(N1 K σ))
    (t : Fin 4 → ↥(Cq K q)) :
    g * iota0 K σ hq hσ t * g⁻¹ = iota0 K σ hq hσ (mactC (foldMat (psi1 K σ g)) t) := by
  obtain ⟨l, hl⟩ := exists_wordW Tag.E6 (psi1 K σ g)
  obtain ⟨lb, hlb⟩ := exists_wordW Tag.F4 (foldEquiv ⟨psi1 K σ g, psi1_mem K σ g⟩)
  have hfm : foldMat (psi1 K σ g) = (lb.map (Smat Tag.F4)).prod := by
    rw [foldMat_of_mem (psi1_mem K σ g), hlb, latMat_wordW]
  apply Subtype.ext
  have h1 := conj_coord_word K σ g l hl (unfoldE K q t)
  have h2 : mact K (RM6 l) (unfoldE K q t) = unfoldE K q (mactC (SM lb) t) :=
    mact_unfold K (RM6 l) (SM lb) (fold_cond K σ g l lb hl hlb) t
  have h3 := congrArg (fun c => (torusCoordHom Tag.E6 K c : ModGL Tag.E6 K)) h2
  show (g : ModGL Tag.E6 K) * (torusCoordHom Tag.E6 K (unfoldE K q t) : ModGL Tag.E6 K) *
      (g : ModGL Tag.E6 K)⁻¹ = (torusCoordHom Tag.E6 K (unfoldE K q (mactC (foldMat (psi1 K σ g)) t)) :
        ModGL Tag.E6 K)
  rw [hfm]
  exact h1.trans h3

end TwE6

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
