module

public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Filter.ClassicalOdd.Symplectic
public import CFSG.GH74.L5U5.Models

public section

namespace CFSG.GH74.Generic

open CFSG.Assembly.LowTwoRank CFSG.GH74.Filter.ClassicalOdd CFSG.GH74.L5U5
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

theorem rankCertified_of_section {G : Type} [Group G] [Finite G] {K A : Type} [Group K] [Finite K]
    [Group A] (α : K →* G) (β : K →* A) (hβ : Function.Surjective β)
    (hcomm : ∀ a b : A, a * b = b * a) (hsq : ∀ a : A, a ^ 2 = 1) {r : ℕ}
    (hcard : 2 ^ r < Nat.card A) (hker : α.ker ≤ β.ker) : RankCertified G r :=
  rankCertified_of_not_sectionalTwoRankLE
    (not_sectionalTwoRankLE_of_surjection r α β hβ hcomm hsq hcard hker)

theorem rankCertified_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    [Finite F] {H : Subgroup (GL ι F)} {K A : Type} [Group K] [Finite K] [Group A]
    (α : K →* GL ι F) (hα : ∀ k, α k ∈ H) (β : K →* A) (hβ : Function.Surjective β)
    (hcomm : ∀ a b : A, a * b = b * a) (hsq : ∀ a : A, a ^ 2 = 1) {r : ℕ}
    (hcard : 2 ^ r < Nat.card A)
    (hscal : ∀ (k : K) (c : F), (α k : Matrix ι ι F) = scalar ι c → β k = 1) :
    RankCertified (StatedProj H) r := by
  refine rankCertified_of_section
    ((QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H)).comp (α.codRestrict H hα)) β hβ hcomm
    hsq hcard fun k hk => ?_
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hk
  obtain ⟨c, hc⟩ := hk
  refine MonoidHom.mem_ker.2 (hscal k (c : F) ?_)
  rw [← GeneralLinearGroup.coe_scalar, hc]
  rfl

theorem rankCertified_of_ker_pm {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    [Finite F] {S : Subgroup (GL ι F)} {K : Type} [Group K] (π : S →* K)
    (hker : ∀ g ∈ π.ker, (g : GL ι F) = 1 ∨ (g : GL ι F) = -1) {Kd A : Type} [Group Kd]
    [Finite Kd] [Group A] (α : Kd →* GL ι F) (hα : ∀ k, α k ∈ S) (β : Kd →* A)
    (hβ : Function.Surjective β) (hcomm : ∀ a b : A, a * b = b * a)
    (hsq : ∀ a : A, a ^ 2 = 1) {r : ℕ} (hcard : 2 ^ r < Nat.card A)
    (hscal : ∀ (k : Kd) (c : F), (c = 1 ∨ c = -1) → (α k : Matrix ι ι F) = scalar ι c →
      β k = 1) : RankCertified K r := by
  have hSfin : Finite S := inferInstance
  have hrfin : Finite π.range :=
    Finite.of_surjective π.rangeRestrict π.rangeRestrict_surjective
  refine RankCertified.of_subgroup (K := π.range)
    (rankCertified_of_section (π.rangeRestrict.comp (α.codRestrict S hα)) β hβ hcomm hsq hcard ?_)
  intro k hk
  have hk' : π ⟨α k, hα k⟩ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
  rcases hker _ (MonoidHom.mem_ker.2 hk') with h | h
  · refine MonoidHom.mem_ker.2 (hscal k 1 (Or.inl rfl) ?_)
    have h' : (α k : GL ι F) = 1 := h
    rw [h', Units.val_one, map_one]
  · refine MonoidHom.mem_ker.2 (hscal k (-1) (Or.inr rfl) ?_)
    have h' : (α k : GL ι F) = -1 := h
    rw [h', Units.val_neg, Units.val_one, map_neg, map_one]

theorem card_V4_sq : Nat.card (V4 × V4) = 16 := by
  simp [Nat.card_eq_fintype_card]

theorem card_mod_two_of_ringChar_ne_two {F : Type} [Field F] [Finite F] (h : ringChar F ≠ 2) :
    Nat.card F % 2 = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have h1 := FiniteField.odd_card_of_char_ne_two h
  rwa [← Nat.card_eq_fintype_card] at h1

theorem ringChar_ne_two_of_dvd_four {F : Type} [Field F] [Finite F] (h4 : 4 ∣ Nat.card F - 1) :
    ringChar F ≠ 2 := by
  intro h2
  have : Fintype F := Fintype.ofFinite F
  have h0 := FiniteField.even_card_iff_char_two.1 h2
  rw [← Nat.card_eq_fintype_card] at h0
  have hpos : 0 < Nat.card F := Nat.card_pos
  omega

theorem exists_unitary_quatRep {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hp2 : p ≠ 2) (hF : Nat.card F = (p ^ f) ^ 2) :
    ∃ Q : QuatRep F, ∀ g, IsUni (iterateFrobenius F p f) (Q.ρ g) := by
  have hK2 : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  obtain ⟨a, b, ha, hb, hab⟩ := exists_quat_unitary hp2 hF
  have hσ : ∀ x, iterateFrobenius F p f x = x ^ (p ^ f) :=
    CFSG.SectionRank.ClassicalOdd.frob_apply
  exact ⟨QuatRep.ofSq hK2 hab, fun g =>
    isUni_quatHom hab (by rw [hσ]; exact ha) (by rw [hσ]; exact hb) g⟩

theorem mem_statedSU_of_isUni {F : Type} [Field F] {n q : ℕ} {σ : F →+* F}
    (hσ : ∀ x, σ x = x ^ q) (A : GL (Fin n) F) (hdet : (A : Matrix (Fin n) (Fin n) F).det = 1)
    (hA : IsUni σ (A : Matrix (Fin n) (Fin n) F)) : A ∈ StatedSU n q F := by
  have hfun : (fun x : F => x ^ q) = σ := funext fun x => (hσ x).symm
  refine Subgroup.subset_closure ⟨hdet, ?_⟩
  change ((A : Matrix (Fin n) (Fin n) F).map (fun x => x ^ q))ᵀ * (A : Matrix (Fin n) (Fin n) F) = 1
  rw [hfun]
  exact hA

section Hom

variable {F : Type} [Field F]

@[expose] def alphaQ2 (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) :
    Q8 × Q8 →* Matrix (Fin (2 + 2)) (Fin (2 + 2)) F where
  toFun g := diagBlock (ρ g.1) (ρ g.2)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, map_one]
    exact diagBlock_one
  map_mul' g h := by
    rw [diagBlock_mul]
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]

theorem alphaQ2_apply (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (g : Q8 × Q8) :
    alphaQ2 ρ g = diagBlock (ρ g.1) (ρ g.2) := rfl

theorem det_alphaQ2 {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F} (hρ : ∀ g, (ρ g).det = 1)
    (g : Q8 × Q8) : (alphaQ2 ρ g).det = 1 := by
  simp only [alphaQ2_apply, det_diagBlock, hρ, mul_one]

theorem alphaQ2_scalar (Q : QuatRep F) (g : Q8 × Q8) (c : F)
    (h : alphaQ2 Q.ρ g = scalar (Fin (2 + 2)) c) : q8Frattini g.1 = 1 ∧ q8Frattini g.2 = 1 := by
  rw [alphaQ2_apply] at h
  obtain ⟨h1, h2⟩ := eq_scalar_of_diagBlock_eq h
  exact ⟨(Q.scalar_eq _ _ h1).1, (Q.scalar_eq _ _ h2).1⟩

theorem isUni_alphaQ2 {σ : F →+* F} {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F}
    (hρ : ∀ g, IsUni σ (ρ g)) (g : Q8 × Q8) : IsUni σ (alphaQ2 ρ g) := by
  rw [alphaQ2_apply]
  exact (hρ _).diagBlock (hρ _)

@[expose] def alphaQ2One (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) :
    Q8 × Q8 →* Matrix (Fin (2 + 2 + 1)) (Fin (2 + 2 + 1)) F where
  toFun g := diagBlock (diagBlock (ρ g.1) (ρ g.2)) (1 : Matrix (Fin 1) (Fin 1) F)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, map_one]
    rw [diagBlock_one, diagBlock_one]
  map_mul' g h := by
    rw [diagBlock_mul, diagBlock_mul, mul_one]
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]

theorem alphaQ2One_apply (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (g : Q8 × Q8) :
    alphaQ2One ρ g = diagBlock (diagBlock (ρ g.1) (ρ g.2)) (1 : Matrix (Fin 1) (Fin 1) F) := rfl

theorem det_alphaQ2One {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F} (hρ : ∀ g, (ρ g).det = 1)
    (g : Q8 × Q8) : (alphaQ2One ρ g).det = 1 := by
  simp only [alphaQ2One_apply, det_diagBlock, hρ, det_one, mul_one]

theorem alphaQ2One_scalar (Q : QuatRep F) (g : Q8 × Q8) (c : F)
    (h : alphaQ2One Q.ρ g = scalar (Fin (2 + 2 + 1)) c) :
    q8Frattini g.1 = 1 ∧ q8Frattini g.2 = 1 := by
  rw [alphaQ2One_apply] at h
  obtain ⟨h12, -⟩ := eq_scalar_of_diagBlock_eq h
  obtain ⟨h1, h2⟩ := eq_scalar_of_diagBlock_eq h12
  exact ⟨(Q.scalar_eq _ _ h1).1, (Q.scalar_eq _ _ h2).1⟩

theorem isUni_alphaQ2One {σ : F →+* F} {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F}
    (hρ : ∀ g, IsUni σ (ρ g)) (g : Q8 × Q8) : IsUni σ (alphaQ2One ρ g) := by
  rw [alphaQ2One_apply]
  exact ((hρ _).diagBlock (hρ _)).diagBlock IsUni.one

end Hom

theorem rankCertified_PSL4 {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    RankCertified (StatedProj (StatedSL 4 F)) 3 := by
  obtain ⟨Q⟩ := exists_quatRep hF
  refine rankCertified_statedProj (A := V4 × V4) (alphaQ2 Q.ρ).toHomUnits (fun k => ?_)
    (q8Frattini.prodMap q8Frattini) (q8Frattini_surjective.prodMap q8Frattini_surjective)
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_sq]; norm_num) ?_
  · exact Subgroup.subset_closure (det_alphaQ2 Q.det_eq k)
  · intro k c h
    obtain ⟨h1, h2⟩ := alphaQ2_scalar Q k c h
    exact Prod.ext h1 h2

theorem rankCertified_PSL5 {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    RankCertified (StatedProj (StatedSL 5 F)) 3 := by
  obtain ⟨Q⟩ := exists_quatRep hF
  refine rankCertified_statedProj (A := V4 × V4) (alphaQ2One Q.ρ).toHomUnits (fun k => ?_)
    (q8Frattini.prodMap q8Frattini) (q8Frattini_surjective.prodMap q8Frattini_surjective)
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_sq]; norm_num) ?_
  · exact Subgroup.subset_closure (det_alphaQ2One Q.det_eq k)
  · intro k c h
    obtain ⟨h1, h2⟩ := alphaQ2One_scalar Q k c h
    exact Prod.ext h1 h2

theorem rankCertified_PSU4 {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 2 = 1) : RankCertified (StatedProj (StatedSU 4 q F)) 3 := by
  obtain ⟨p, f, _, _, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (Nat.odd_iff.2 hq).pow
  have hp2 : p ≠ 2 := prime_ne_two_of_odd_card hodd
  obtain ⟨Q, hQ⟩ := exists_unitary_quatRep hp2 hF
  have hσ : ∀ x, iterateFrobenius F p f x = x ^ (p ^ f) :=
    CFSG.SectionRank.ClassicalOdd.frob_apply
  refine rankCertified_statedProj (A := V4 × V4) (alphaQ2 Q.ρ).toHomUnits (fun k => ?_)
    (q8Frattini.prodMap q8Frattini) (q8Frattini_surjective.prodMap q8Frattini_surjective)
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_sq]; norm_num) ?_
  · exact mem_statedSU_of_isUni hσ _ (det_alphaQ2 Q.det_eq k) (isUni_alphaQ2 hQ k)
  · intro k c h
    obtain ⟨h1, h2⟩ := alphaQ2_scalar Q k c h
    exact Prod.ext h1 h2

theorem rankCertified_PSU5 {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 2 = 1) : RankCertified (StatedProj (StatedSU 5 q F)) 3 := by
  obtain ⟨p, f, _, _, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (Nat.odd_iff.2 hq).pow
  have hp2 : p ≠ 2 := prime_ne_two_of_odd_card hodd
  obtain ⟨Q, hQ⟩ := exists_unitary_quatRep hp2 hF
  have hσ : ∀ x, iterateFrobenius F p f x = x ^ (p ^ f) :=
    CFSG.SectionRank.ClassicalOdd.frob_apply
  refine rankCertified_statedProj (A := V4 × V4) (alphaQ2One Q.ρ).toHomUnits (fun k => ?_)
    (q8Frattini.prodMap q8Frattini) (q8Frattini_surjective.prodMap q8Frattini_surjective)
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_sq]; norm_num) ?_
  · exact mem_statedSU_of_isUni hσ _ (det_alphaQ2One Q.det_eq k) (isUni_alphaQ2One hQ k)
  · intro k c h
    obtain ⟨h1, h2⟩ := alphaQ2One_scalar Q k c h
    exact Prod.ext h1 h2

theorem rankCertified_PSp4 {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    RankCertified (StatedProj (StatedSp 2 F)) 3 := by
  obtain ⟨Q⟩ := exists_quatRep hF
  have hV : ∀ x : V4, x ^ 2 = 1 := by decide
  refine rankCertified_statedProj (A := Fin 2 → V4) (alphaSp Q.ρ (Fin 2)).toHomUnits
    (fun k => ?_) (MonoidHom.compLeft q8Frattini (Fin 2)) ?_
    (fun a b => funext fun i => mul_comm (a i) (b i)) (fun a => funext fun i => hV (a i)) ?_ ?_
  · exact Subgroup.subset_closure (planeDiag_symplectic _ fun i => Q.det_eq _)
  · intro b
    exact ⟨fun i => (q8Frattini_surjective (b i)).choose,
      funext fun i => (q8Frattini_surjective (b i)).choose_spec⟩
  · rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, card_V4]
    norm_num
  · intro k c h
    funext i
    exact (Q.scalar_eq _ _ (planeDiag_eq_scalar (fun i => Q.ρ (k i)) c h i)).1

section Cyclic

variable {F : Type} [Field F]

@[expose] def alphaC (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (χ : Multiplicative (ZMod 4) →* Fˣ) :
    (Q8 × Q8) × Multiplicative (ZMod 4) →* Matrix (Fin (2 + 2)) (Fin (2 + 2)) F where
  toFun g := diagBlock (((χ g.2 : Fˣ) : F) • ρ g.1.1) (((χ g.2 : Fˣ) : F) • ρ g.1.2)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, map_one, Units.val_one, one_smul]
    exact diagBlock_one
  map_mul' g h := by
    rw [diagBlock_mul]
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

theorem alphaC_apply (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (χ : Multiplicative (ZMod 4) →* Fˣ)
    (g : (Q8 × Q8) × Multiplicative (ZMod 4)) :
    alphaC ρ χ g =
      diagBlock (((χ g.2 : Fˣ) : F) • ρ g.1.1) (((χ g.2 : Fˣ) : F) • ρ g.1.2) := rfl

theorem det_alphaC {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F} (hρ : ∀ g, (ρ g).det = 1)
    (χ : Multiplicative (ZMod 4) →* Fˣ) (hχ : ∀ k, ((χ k : Fˣ) : F) ^ 4 = 1)
    (g : (Q8 × Q8) × Multiplicative (ZMod 4)) : (alphaC ρ χ g).det = 1 := by
  rw [alphaC_apply, det_diagBlock, det_smul, det_smul, hρ, hρ]
  simp only [Fintype.card_fin, mul_one]
  linear_combination hχ g.2

theorem isUni_alphaC {σ : F →+* F} {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F}
    (hρ : ∀ g, IsUni σ (ρ g)) (χ : Multiplicative (ZMod 4) →* Fˣ)
    (hχ : ∀ k, σ ((χ k : Fˣ) : F) * ((χ k : Fˣ) : F) = 1)
    (g : (Q8 × Q8) × Multiplicative (ZMod 4)) : IsUni σ (alphaC ρ χ g) := by
  rw [alphaC_apply]
  exact IsUni.diagBlock ((hρ _).smul (hχ _)) ((hρ _).smul (hχ _))

theorem alphaC_scalar (Q : QuatRep F) (χ : Multiplicative (ZMod 4) →* Fˣ)
    (hχ : ∀ k, ((χ k : Fˣ) : F) ^ 2 = 1 → zRed 4 (by decide) k = 1)
    (g : (Q8 × Q8) × Multiplicative (ZMod 4)) (c : F) (hc : c = 1 ∨ c = -1)
    (h : alphaC Q.ρ χ g = scalar (Fin (2 + 2)) c) :
    q8Frattini g.1.1 = 1 ∧ q8Frattini g.1.2 = 1 ∧ zRed 4 (by decide) g.2 = 1 := by
  rw [alphaC_apply] at h
  obtain ⟨h1, h2⟩ := eq_scalar_of_diagBlock_eq h
  have ht0 : ((χ g.2 : Fˣ) : F) ≠ 0 := Units.ne_zero _
  set t : F := ((χ g.2 : Fˣ) : F) with ht
  have hx : Q.ρ g.1.1 = scalar (Fin 2) (t⁻¹ * c) := by
    rw [← smul_scalar_fin_two, ← h1, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  have hy : Q.ρ g.1.2 = scalar (Fin 2) (t⁻¹ * c) := by
    rw [← smul_scalar_fin_two, ← h2, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  obtain ⟨hx1, hx2⟩ := Q.scalar_eq _ _ hx
  obtain ⟨hy1, -⟩ := Q.scalar_eq _ _ hy
  refine ⟨hx1, hy1, hχ _ ?_⟩
  have hc2 : c ^ 2 = 1 := by rcases hc with rfl | rfl <;> norm_num
  have hs2 : (t⁻¹ * c) ^ 2 = 1 := by rcases hx2 with h' | h' <;> rw [h'] <;> norm_num
  calc t ^ 2 = t ^ 2 * (t⁻¹ * c) ^ 2 := by rw [hs2, mul_one]
    _ = c ^ 2 := by field_simp
    _ = 1 := hc2

end Cyclic

theorem rankCertified_SL4_quotient {F : Type} [Field F] [Finite F] (h4 : 4 ∣ Nat.card F - 1)
    {K : Type} [Group K] (π : StatedSL 4 F →* K)
    (hker : ∀ g ∈ π.ker, (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = -1) :
    RankCertified K 4 := by
  have hF : ringChar F ≠ 2 := ringChar_ne_two_of_dvd_four h4
  obtain ⟨Q⟩ := exists_quatRep hF
  obtain ⟨u, hu⟩ := exists_units_orderOf (F := F) (d := 4) h4
  have hu4 : u ^ 4 = 1 := hu ▸ pow_orderOf_eq_one u
  have hχ4 : ∀ k, (((zChar u 4 hu4) k : Fˣ) : F) ^ 4 = 1 := fun k => by
    rw [← Units.val_pow_eq_pow_val]
    change (((u ^ (Multiplicative.toAdd k).val) ^ 4 : Fˣ) : F) = 1
    rw [← pow_mul, mul_comm, pow_mul, hu4, one_pow, Units.val_one]
  have hχ2 : ∀ k, (((zChar u 4 hu4) k : Fˣ) : F) ^ 2 = 1 → zRed 4 (by decide) k = 1 :=
    fun k hk => (zRed_eq_one_iff 4 _ k).2
      (zChar_pow_imp (m := 2) rfl (by norm_num) hu hu4 k hk)
  refine rankCertified_of_ker_pm (A := (V4 × V4) × Multiplicative (ZMod 2)) π hker
    (alphaC Q.ρ (zChar u 4 hu4)).toHomUnits (fun k => ?_)
    ((q8Frattini.prodMap q8Frattini).prodMap (zRed 4 (by decide)))
    ((q8Frattini_surjective.prodMap q8Frattini_surjective).prodMap
      (zRed_surjective 4 (by decide)))
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_sq_V2]; norm_num) ?_
  · exact Subgroup.subset_closure (det_alphaC Q.det_eq _ hχ4 k)
  · intro k c hc h
    obtain ⟨h1, h2, h3⟩ := alphaC_scalar Q (zChar u 4 hu4) hχ2 k c hc h
    exact Prod.ext (Prod.ext h1 h2) h3

theorem rankCertified_SU4_quotient {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 3) {K : Type} [Group K] (π : StatedSU 4 q F →* K)
    (hker : ∀ g ∈ π.ker, (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = -1) :
    RankCertified K 4 := by
  obtain ⟨p, f, _, _, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hodd : Odd (Nat.card F) := by
    rw [hF]; exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  have hp2 : p ≠ 2 := prime_ne_two_of_odd_card hodd
  obtain ⟨Q, hQ⟩ := exists_unitary_quatRep hp2 hF
  have hσ : ∀ x, iterateFrobenius F p f x = x ^ (p ^ f) :=
    CFSG.SectionRank.ClassicalOdd.frob_apply
  have h4 : 4 ∣ Nat.card F - 1 := by
    have : (p ^ f) ^ 2 % 4 = 1 := by rw [Nat.pow_mod, hq]
    omega
  obtain ⟨u, hu⟩ := exists_units_orderOf (F := F) (d := 4) h4
  have hun : iterateFrobenius F p f (u : F) * u = 1 := by
    have h1 : u ^ (p ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hu]; omega)
    rw [hσ, ← pow_succ]
    simpa using congrArg Units.val h1
  have hu4 : u ^ 4 = 1 := hu ▸ pow_orderOf_eq_one u
  have hχ4 : ∀ k, (((zChar u 4 hu4) k : Fˣ) : F) ^ 4 = 1 := fun k => by
    rw [← Units.val_pow_eq_pow_val]
    change (((u ^ (Multiplicative.toAdd k).val) ^ 4 : Fˣ) : F) = 1
    rw [← pow_mul, mul_comm, pow_mul, hu4, one_pow, Units.val_one]
  have hχσ : ∀ k, iterateFrobenius F p f (((zChar u 4 hu4) k : Fˣ) : F) *
      (((zChar u 4 hu4) k : Fˣ) : F) = 1 := fun k => by
    change iterateFrobenius F p f ((u ^ (Multiplicative.toAdd k).val : Fˣ) : F) *
      ((u ^ (Multiplicative.toAdd k).val : Fˣ) : F) = 1
    rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hun, one_pow]
  have hχ2 : ∀ k, (((zChar u 4 hu4) k : Fˣ) : F) ^ 2 = 1 → zRed 4 (by decide) k = 1 :=
    fun k hk => (zRed_eq_one_iff 4 _ k).2
      (zChar_pow_imp (m := 2) rfl (by norm_num) hu hu4 k hk)
  refine rankCertified_of_ker_pm (A := (V4 × V4) × Multiplicative (ZMod 2)) π hker
    (alphaC Q.ρ (zChar u 4 hu4)).toHomUnits (fun k => ?_)
    ((q8Frattini.prodMap q8Frattini).prodMap (zRed 4 (by decide)))
    ((q8Frattini_surjective.prodMap q8Frattini_surjective).prodMap
      (zRed_surjective 4 (by decide)))
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_sq_V2]; norm_num) ?_
  · exact mem_statedSU_of_isUni hσ _ (det_alphaC Q.det_eq _ hχ4 k) (isUni_alphaC hQ _ hχσ k)
  · intro k c hc h
    obtain ⟨h1, h2, h3⟩ := alphaC_scalar Q (zChar u 4 hu4) hχ2 k c hc h
    exact Prod.ext (Prod.ext h1 h2) h3

theorem cover_central_iff {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {H : Subgroup (GL ι F)} {K : Type*} [Group K]
    (e : K ⧸ Subgroup.center K ≃* StatedProj H) (π : H →* K)
    (hcompat : ∀ g, e (QuotientGroup.mk (π g)) = QuotientGroup.mk g) (g : H) :
    π g ∈ Subgroup.center K ↔ ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar ι c = (g : GL ι F) := by
  have h1 : (QuotientGroup.mk (π g) : K ⧸ Subgroup.center K) = 1 ↔ π g ∈ Subgroup.center K :=
    QuotientGroup.eq_one_iff _
  have h2 : (QuotientGroup.mk g : StatedProj H) = 1 ↔ g ∈ (StatedScalars ι F).subgroupOf H :=
    QuotientGroup.eq_one_iff _
  rw [← h1, ← e.map_eq_one_iff, hcompat, h2, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range]

section Cover

variable {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)} {K : Type*} [Group K]

theorem units_sq_eq_one_iff (c : Fˣ) : c ^ 2 = 1 ↔ c = 1 ∨ c = -1 := by
  constructor
  · intro h
    have h' : (c : F) * c = 1 := by
      have := congrArg (fun u : Fˣ => (u : F)) h
      simpa [sq] using this
    rcases mul_self_eq_one_iff.1 h' with h2 | h2
    · exact Or.inl (Units.ext h2)
    · exact Or.inr (Units.ext (by simpa using h2))
  · rintro (rfl | rfl) <;> simp

theorem cover_exists_scalar_ne_one (π : S →* K) (hπ : Function.Surjective π)
    (hcen : ∀ g : S, π g ∈ Subgroup.center K ↔
      ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c = (g : GL (Fin 4) F))
    (hZ : Subgroup.center K ≠ ⊥) :
    ∃ g : S, (∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c = (g : GL (Fin 4) F)) ∧
      π g ≠ 1 := by
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ
  obtain ⟨g, rfl⟩ := hπ z
  exact ⟨g, (hcen g).1 hz, fun h => hz1 (Subtype.ext h)⟩

theorem cover_ker_pm (π : S →* K) (hπ : Function.Surjective π)
    (hcen : ∀ g : S, π g ∈ Subgroup.center K ↔
      ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c = (g : GL (Fin 4) F))
    (hZ : Subgroup.center K ≠ ⊥)
    (hsc : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ S → c ^ 4 = 1) :
    ∀ g ∈ π.ker, (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = -1 := by
  intro g hg
  have hg1 : π g = 1 := hg
  obtain ⟨c, hc⟩ := (hcen g).1 (by rw [hg1]; exact one_mem _)
  have hcS : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ S := by rw [hc]; exact g.2
  have hc4 : c ^ 4 = 1 := hsc c hcS
  by_cases hc1 : c = 1
  · left
    rw [← hc, hc1, map_one]
  by_cases hc2 : c = -1
  · right
    rw [← hc, hc2]
    exact scalar_neg_one_eq 4
  exfalso
  have hnot : ¬ c ^ 2 ^ 1 = 1 := by
    intro h
    rw [pow_one] at h
    rcases (units_sq_eq_one_iff c).1 h with h | h
    · exact hc1 h
    · exact hc2 h
  have hord : orderOf c = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) hnot (by simpa using hc4)
    simpa using this
  have hprim : IsPrimitiveRoot c 4 := by
    have := IsPrimitiveRoot.orderOf c
    rwa [hord] at this
  obtain ⟨g₁, ⟨c₁, hc₁⟩, hπg₁⟩ := cover_exists_scalar_ne_one π hπ hcen hZ
  have hc₁S : Matrix.GeneralLinearGroup.scalar (Fin 4) c₁ ∈ S := by rw [hc₁]; exact g₁.2
  have hc₁4 : c₁ ^ 4 = 1 := hsc c₁ hc₁S
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 4 c₁).2 hc₁4)
  apply hπg₁
  have hg₁ : g₁ = g ^ i := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← hc₁, ← hi, map_pow]
  rw [hg₁, map_pow, hg1, one_pow]

theorem cover_injective (π : S →* K) (hπ : Function.Surjective π)
    (hcen : ∀ g : S, π g ∈ Subgroup.center K ↔
      ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c = (g : GL (Fin 4) F))
    (hZ : Subgroup.center K ≠ ⊥)
    (hsc : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ S → c = 1 ∨ c = -1) :
    Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro g hg1
  obtain ⟨c, hc⟩ := (hcen g).1 (by rw [hg1]; exact one_mem _)
  have hcS : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ S := by rw [hc]; exact g.2
  obtain ⟨g₁, ⟨c₁, hc₁⟩, hπg₁⟩ := cover_exists_scalar_ne_one π hπ hcen hZ
  have hc₁S : Matrix.GeneralLinearGroup.scalar (Fin 4) c₁ ∈ S := by rw [hc₁]; exact g₁.2
  rcases hsc c hcS with rfl | rfl
  · have h1 : (g : GL (Fin 4) F) = 1 := by rw [← hc, map_one]
    exact Subtype.ext h1
  · exfalso
    apply hπg₁
    rcases hsc c₁ hc₁S with rfl | rfl
    · have h1 : (g₁ : GL (Fin 4) F) = 1 := by rw [← hc₁, map_one]
      have hg₁ : g₁ = 1 := Subtype.ext h1
      rw [hg₁, map_one]
    · have : g₁ = g := Subtype.ext (hc₁.symm.trans hc)
      rw [this, hg1]

end Cover

theorem pow_four_eq_one_of_scalar_mem_statedSL {F : Type} [Field F] (c : Fˣ)
    (h : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSL 4 F) : c ^ 4 = 1 := by
  rw [statedSL_eq_detOne, mem_detOne] at h
  have hdet : (c : F) ^ 4 = 1 := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] using h
  exact Units.ext (by simpa using hdet)

theorem cover_branch_SL4 {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F]
    (hF2 : ringChar F ≠ 2) (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSL 4 F))
    (π : StatedSL 4 F →* K) (hπ : Function.Surjective π)
    (hcompat : ∀ g, e (QuotientGroup.mk (π g)) = QuotientGroup.mk g)
    (hZ : Subgroup.center K ≠ ⊥) :
    (Nat.card F % 4 = 3 ∧ Nonempty (K ≃* StatedSL 4 F)) ∨
      (Nat.card F % 4 = 1 ∧ RankCertified K 4) := by
  have hcen := cover_central_iff e π hcompat
  have hsc : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSL 4 F → c ^ 4 = 1 :=
    fun c h => pow_four_eq_one_of_scalar_mem_statedSL c h
  have hodd := card_mod_two_of_ringChar_ne_two hF2
  have hmod : Nat.card F % 4 = 3 ∨ Nat.card F % 4 = 1 := by omega
  rcases hmod with h3 | h1
  · refine Or.inl ⟨h3, ⟨(MulEquiv.ofBijective π ⟨?_, hπ⟩).symm⟩⟩
    refine cover_injective π hπ hcen hZ fun c hc => ?_
    exact (units_pow_four_eq_one_iff h3 c).1 (hsc c hc)
  · exact Or.inr ⟨h1, rankCertified_SL4_quotient (by omega) π (cover_ker_pm π hπ hcen hZ hsc)⟩

theorem cover_branch_SU4 {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (hq : q % 2 = 1)
    (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU 4 q F))
    (π : StatedSU 4 q F →* K) (hπ : Function.Surjective π)
    (hcompat : ∀ g, e (QuotientGroup.mk (π g)) = QuotientGroup.mk g)
    (hZ : Subgroup.center K ≠ ⊥) :
    (q % 4 = 1 ∧ Nonempty (K ≃* StatedSU 4 q F)) ∨ (q % 4 = 3 ∧ RankCertified K 4) := by
  obtain ⟨p, f, hp, _, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hcen := cover_central_iff e π hcompat
  have hsc : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSU 4 (p ^ f) F →
      c ^ 4 = 1 ∧ c ^ (p ^ f + 1) = 1 := fun c h =>
    (CFSG.LinearGroups.scalar_mem_statedSU_iff hp.out hF (by norm_num) c).1 h
  have hmod : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by omega
  rcases hmod with h1 | h3
  · refine Or.inl ⟨h1, ⟨(MulEquiv.ofBijective π ⟨?_, hπ⟩).symm⟩⟩
    refine cover_injective π hπ hcen hZ fun c hc => ?_
    exact units_eq_one_or_neg_one_of_unitary h1 c (hsc c hc).1 (hsc c hc).2
  · exact Or.inr ⟨h3, rankCertified_SU4_quotient hF h3 π
      (cover_ker_pm π hπ hcen hZ fun c hc => (hsc c hc).1)⟩

section SpFrame

variable {F : Type} [Field F]

@[expose] def swap2 : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 0]

theorem swap2_mul_self : (swap2 : Matrix (Fin 2) (Fin 2) F) * swap2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2, Matrix.mul_apply, Fin.sum_univ_two]

theorem swap2_transpose : (swap2 : Matrix (Fin 2) (Fin 2) F)ᵀ = swap2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2]

theorem swap2_mul_diagonal (d : Fin 2 → F) :
    swap2 * diagonal d = diagonal ![d 1, d 0] * swap2 := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [swap2]

theorem swap2_mul_diagonal_mul (d : Fin 2 → F) :
    swap2 * diagonal d * swap2 = diagonal ![d 1, d 0] := by
  rw [swap2_mul_diagonal, Matrix.mul_assoc, swap2_mul_self, Matrix.mul_one]

@[expose] def alphaSp2 (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) :
    Q8 × Q8 →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F where
  toFun g := planeDiag ![ρ g.1, ρ g.2]
  map_one' := by
    have : (![ρ (1 : Q8 × Q8).1, ρ (1 : Q8 × Q8).2] : Fin 2 → Matrix (Fin 2) (Fin 2) F) =
        fun _ => 1 := by
      funext i
      fin_cases i <;> simp
    rw [this]
    exact planeDiag_one
  map_mul' g h := by
    rw [planeDiag_mul]
    congr 1
    funext i
    fin_cases i <;> simp

theorem alphaSp2_apply (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (g : Q8 × Q8) :
    alphaSp2 ρ g = planeDiag ![ρ g.1, ρ g.2] := rfl

theorem planeDiag_inj {X Y : Fin 2 → Matrix (Fin 2) (Fin 2) F} (h : planeDiag X = planeDiag Y) :
    X = Y := by
  funext i
  have h00 := congrFun (congrFun h (Sum.inl i)) (Sum.inl i)
  have h01 := congrFun (congrFun h (Sum.inl i)) (Sum.inr i)
  have h10 := congrFun (congrFun h (Sum.inr i)) (Sum.inl i)
  have h11 := congrFun (congrFun h (Sum.inr i)) (Sum.inr i)
  simp [planeDiag] at h00 h01 h10 h11
  ext a b
  fin_cases a <;> fin_cases b <;> simp [h00, h01, h10, h11]

@[expose] def spSwapMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := fromBlocks swap2 0 0 swap2

theorem spSwapMat_mul_self : (spSwapMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * spSwapMat =
    1 := by
  rw [spSwapMat, fromBlocks_multiply]
  simp [swap2_mul_self, fromBlocks_one]

theorem spSwapMat_symplectic :
    (spSwapMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * fromBlocks 0 1 (-1) 0 * spSwapMat =
      fromBlocks 0 1 (-1) 0 := by
  rw [spSwapMat, fromBlocks_transpose, swap2_transpose, transpose_zero, fromBlocks_multiply,
    fromBlocks_multiply]
  simp [swap2_mul_self]

theorem spSwapMat_mul_planeDiag_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    (spSwapMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * planeDiag ![A, B] * spSwapMat =
      planeDiag ![B, A] := by
  rw [spSwapMat, planeDiag, planeDiag, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, swap2_mul_diagonal_mul]
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;>
    (congr 1; funext i; fin_cases i <;> rfl)

@[expose] def spSwapGL : GL (Fin 2 ⊕ Fin 2) F :=
  ⟨spSwapMat, spSwapMat, spSwapMat_mul_self, spSwapMat_mul_self⟩

end SpFrame

theorem exists_q8q8_Sp4 {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    ∃ φ : Q8 × Q8 →* StatedSp 2 F, Function.Injective φ ∧
      ∃ w : StatedSp 2 F, w * w = 1 ∧ ∀ g h : Q8, w * φ (g, h) * w⁻¹ = φ (h, g) := by
  obtain ⟨a, b, hab⟩ := (odd_field_two_dimensional_quaternion_matrices hF).1
  have hinj : Function.Injective (QuatRep.ofSq hF hab).ρ := fun g g' hgg' =>
    quatHom_injective hF hab (Subtype.ext hgg')
  have hmem : ∀ g : Q8 × Q8, (alphaSp2 (QuatRep.ofSq hF hab).ρ).toHomUnits g ∈ StatedSp 2 F :=
    fun g => Subgroup.subset_closure (planeDiag_symplectic _ fun i => by
      fin_cases i <;> exact (QuatRep.ofSq hF hab).det_eq _)
  let φ : Q8 × Q8 →* StatedSp 2 F :=
    (alphaSp2 (QuatRep.ofSq hF hab).ρ).toHomUnits.codRestrict (StatedSp 2 F) hmem
  let w : StatedSp 2 F := ⟨spSwapGL, Subgroup.subset_closure spSwapMat_symplectic⟩
  have hww : w * w = 1 := Subtype.ext (Units.ext spSwapMat_mul_self)
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  refine ⟨φ, ?_, w, hww, fun g h => ?_⟩
  · intro x y hxy
    have h1 : alphaSp2 (QuatRep.ofSq hF hab).ρ x = alphaSp2 (QuatRep.ofSq hF hab).ρ y :=
      congrArg (fun z : StatedSp 2 F =>
        ((z : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hxy
    have h2 := planeDiag_inj h1
    exact Prod.ext (hinj (congrFun h2 0)) (hinj (congrFun h2 1))
  · rw [hwinv]
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact spSwapMat_mul_planeDiag_mul _ _

end CFSG.GH74.Generic
