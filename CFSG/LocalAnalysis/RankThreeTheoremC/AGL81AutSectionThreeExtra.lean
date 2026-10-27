module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Det
import CFSG.ClassicalInvolution.Q3.Lift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree

open Matrix
open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.SectionRank.Ccomm
open scoped commutatorElement

theorem det_eq_one_of_fixes_center_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (hc : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G)
    (hpow : ∀ z ∈ Subgroup.center G, z ^ p = 1)
    (hnc : ∃ a b : G, a * b ≠ b * a)
    (e : G ⧸ Subgroup.center G ≃* Multiplicative (Fin 2 → ZMod p)) (σ : MulAut G)
    (hσ : ∀ c ∈ Subgroup.center G, σ c = c) :
    ((elemAutEquivGL e (autQuotient (Subgroup.center G) σ) : GL (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
  letI : (Subgroup.center G).Characteristic := Subgroup.centerCharacteristic
  have hp := (Fact.out : p.Prime)
  obtain ⟨a, ha⟩ : ∃ a : G, e (a : G ⧸ Subgroup.center G) =
      Multiplicative.ofAdd (Pi.single 0 1) := by
    obtain ⟨q, hq⟩ := e.surjective (Multiplicative.ofAdd (Pi.single 0 1))
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨a, hq⟩
  obtain ⟨b, hb⟩ : ∃ b : G, e (b : G ⧸ Subgroup.center G) =
      Multiplicative.ofAdd (Pi.single 1 1) := by
    obtain ⟨q, hq⟩ := e.surjective (Multiplicative.ofAdd (Pi.single 1 1))
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨b, hq⟩
  set A : Matrix (Fin 2) (Fin 2) (ZMod p) :=
    ((elemAutEquivGL e (autQuotient (Subgroup.center G) σ) : GL (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) with hA
  set c : G := ⁅a, b⁆ with hcdef
  have hcZ : c ∈ Subgroup.center G := hc a b
  have hc1 : c ≠ 1 := by
    intro hc1
    obtain ⟨u, v, huv⟩ := hnc
    apply huv
    have := commutator_coord hc e a b ha hb u v
    rw [← hcdef, hc1, one_pow, inv_one, one_pow, one_mul] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hco : orderOf c = p := orderOf_eq_prime (hpow c hcZ) hc1
  have hσa : Multiplicative.toAdd (e ((σ a : G) : G ⧸ Subgroup.center G)) =
      A.mulVec (Pi.single 0 1) := by
    rw [← autQuotient_mk, ← elemAutEquivGL_mulVec e _ (a : G ⧸ Subgroup.center G), ha]
    rfl
  have hσb : Multiplicative.toAdd (e ((σ b : G) : G ⧸ Subgroup.center G)) =
      A.mulVec (Pi.single 1 1) := by
    rw [← autQuotient_mk, ← elemAutEquivGL_mulVec e _ (b : G ⧸ Subgroup.center G), hb]
    rfl
  have key := commutator_coord hc e a b ha hb (σ a) (σ b)
  rw [hσa, hσb, ← hcdef, ← map_commutatorElement, hσ c hcZ] at key
  have h00 : A.mulVec (Pi.single 0 1) 0 = A 0 0 := by simp [Matrix.col_apply]
  have h10 : A.mulVec (Pi.single 0 1) 1 = A 1 0 := by simp [Matrix.col_apply]
  have h01 : A.mulVec (Pi.single 1 1) 0 = A 0 1 := by simp [Matrix.col_apply]
  have h11 : A.mulVec (Pi.single 1 1) 1 = A 1 1 := by simp [Matrix.col_apply]
  rw [h00, h10, h01, h11] at key
  set M : ℕ := (A 0 0).val * (A 1 1).val with hM
  set N : ℕ := (A 1 0).val * (A 0 1).val with hN
  have hzpow : c ^ ((M : ℤ) - N - 1) = 1 := by
    rw [_root_.zpow_sub, zpow_one, _root_.zpow_sub, zpow_natCast, zpow_natCast, ← inv_pow]
    rw [← key, mul_inv_cancel]
  have hdvd := orderOf_dvd_iff_zpow_eq_one.mpr hzpow
  rw [hco] at hdvd
  have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
  push_cast at hzero
  rw [hM, hN] at hzero
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val] at hzero
  rw [Matrix.det_fin_two]
  linear_combination hzero

theorem matrix_pow_twelve_of_det_one (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hA : A.det = 1) :
    A ^ 12 = 1 := by
  let S : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨A, hA⟩
  have hS : S ^ 12 = 1 :=
    CFSG.ClassicalInvolution.Q3.pow_twelve_of_equiv_sl2Three (MulEquiv.refl _) S
  have h := congrArg (fun T : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) =>
    (T : Matrix (Fin 2) (Fin 2) (ZMod 3))) hS
  rw [Matrix.SpecialLinearGroup.coe_pow] at h
  simpa [S] using h

variable {G : Type*} [Group G] [Finite G] {D : Subgroup G}

private theorem center_eq_centralizer_subgroupOf :
    Subgroup.center ↥D = (Subgroup.centralizer (D : Set G)).subgroupOf D := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩)
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext
      ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hx)) (g : G) g.2)

private theorem card_center_quotient_eq_nine
    (hidx : (Subgroup.centralizer (D : Set G)).relIndex D = 9) :
    Nat.card (↥D ⧸ Subgroup.center ↥D) = 9 := by
  rw [center_eq_centralizer_subgroupOf (D := D), ← Subgroup.index_eq_card]
  exact hidx

private theorem pow_three_center_quotient (hexp : ∀ x ∈ D, x ^ 3 = 1) :
    ∀ q : ↥D ⧸ Subgroup.center ↥D, q ^ 3 = 1 := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← QuotientGroup.mk_pow, show (x : ↥D) ^ 3 = 1 from Subtype.ext (hexp (x : G) x.2)]
  exact QuotientGroup.mk_one _

private theorem comm_center_quotient
    (hcl : ∀ x ∈ D, ∀ x' ∈ D, ⁅x, x'⁆ ∈ Subgroup.centralizer (D : Set G)) :
    ∀ q r : ↥D ⧸ Subgroup.center ↥D, q * r = r * q := by
  intro q r
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective r
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have hmem : ⁅y⁻¹, x⁻¹⁆ ∈ Subgroup.center ↥D := by
    rw [center_eq_centralizer_subgroupOf (D := D), Subgroup.mem_subgroupOf]
    exact hcl (y : G)⁻¹ (D.inv_mem y.2) (x : G)⁻¹ (D.inv_mem x.2)
  have heq : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [heq]
  exact hmem

private theorem exists_not_comm_of_card_center_quotient_eq_nine
    (hidx9 : Nat.card (↥D ⧸ Subgroup.center ↥D) = 9) :
    ∃ a b : ↥D, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have htop : Subgroup.center ↥D = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    rw [Subgroup.mem_center_iff]
    intro y
    exact (h x y).symm
  have hcard : Nat.card (↥D ⧸ Subgroup.center ↥D) = 1 := by
    rw [htop, ← Subgroup.index_eq_card]
    exact Subgroup.index_top
  omega

private theorem exists_coord_center_quotient
    (hidx : (Subgroup.centralizer (D : Set G)).relIndex D = 9)
    (hexp : ∀ x ∈ D, x ^ 3 = 1)
    (hcl : ∀ x ∈ D, ∀ x' ∈ D, ⁅x, x'⁆ ∈ Subgroup.centralizer (D : Set G)) :
    Nonempty (↥D ⧸ Subgroup.center ↥D ≃* Multiplicative (Fin 2 → ZMod 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := card_center_quotient_eq_nine (D := D) hidx
  refine CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (comm_center_quotient (D := D) hcl) (pow_three_center_quotient (D := D) hexp) ?_
  rw [hcard]
  norm_num

private theorem commutator_mem_center_of_classTwo
    (hcl : ∀ x ∈ D, ∀ x' ∈ D, ⁅x, x'⁆ ∈ Subgroup.centralizer (D : Set G)) :
    ∀ a b : ↥D, ⁅a, b⁆ ∈ Subgroup.center ↥D := by
  intro a b
  rw [Subgroup.mem_center_iff]
  intro c
  apply Subtype.ext
  have hmem := hcl (a : G) a.2 (b : G) b.2
  have hcomm := Subgroup.mem_centralizer_iff.mp hmem (c : G) c.2
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def] using hcomm

private theorem normalizer_aut_fixes_center {y : G}
    (hy : y ∈ Subgroup.normalizer (D : Set G))
    (hyZ : ∀ z ∈ D, z ∈ Subgroup.centralizer (D : Set G) → y * z = z * y) :
    ∀ c ∈ Subgroup.center ↥D, D.normalizerMonoidHom ⟨y, hy⟩ c = c := by
  intro c hc
  have hcC : (c : G) ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨d, hd⟩)
  have hcomm : y * (c : G) = (c : G) * y := hyZ (c : G) c.2 hcC
  apply Subtype.ext
  change y * (c : G) * y⁻¹ = (c : G)
  rw [hcomm]
  group

private theorem autQuotient_center_pow_twelve_eq_one
    (hcD : ∀ a b : ↥D, ⁅a, b⁆ ∈ Subgroup.center ↥D)
    (hZexp : ∀ z ∈ Subgroup.center ↥D, z ^ 3 = 1)
    (hnc : ∃ a b : ↥D, a * b ≠ b * a)
    (e : ↥D ⧸ Subgroup.center ↥D ≃* Multiplicative (Fin 2 → ZMod 3))
    {σ : MulAut ↥D} (hσ : ∀ c ∈ Subgroup.center ↥D, σ c = c) :
    autQuotient (Subgroup.center ↥D) σ ^ 12 = 1 := by
  letI : (Subgroup.center ↥D).Characteristic := Subgroup.centerCharacteristic
  have hdet := det_eq_one_of_fixes_center_of_pow_eq_one (p := 3) (G := ↥D) hcD hZexp hnc e σ hσ
  let A : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
    ((elemAutEquivGL e (autQuotient (Subgroup.center ↥D) σ) : GL (Fin 2) (ZMod 3)) :
      Matrix (Fin 2) (Fin 2) (ZMod 3))
  have hA12 : A ^ 12 = 1 := matrix_pow_twelve_of_det_one A hdet
  apply (elemAutEquivGL e).injective
  rw [map_pow, map_one]
  apply Units.ext
  change A ^ 12 = 1
  exact hA12

private theorem autQuotient_center_pow_thirtySix_eq_one
    (hZexp : ∀ z ∈ Subgroup.center ↥D, z ^ 3 = 1)
    {σ : MulAut ↥D} (hσ : ∀ c ∈ Subgroup.center ↥D, σ c = c)
    (hσ12 : autQuotient (Subgroup.center ↥D) σ ^ 12 = 1) :
    σ ^ 36 = 1 := by
  letI : (Subgroup.center ↥D).Characteristic := Subgroup.centerCharacteristic
  let α : MulAut ↥D := σ ^ 12
  have hαZ : ∀ z ∈ Subgroup.center ↥D, α z = z := by
    intro z hz
    change (σ ^ 12) z = z
    have hpow : ∀ n : ℕ, (σ ^ n) z = z := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hσ z hz, ih]
    exact hpow 12
  have hαquot : ∀ x : ↥D, x⁻¹ * α x ∈ Subgroup.center ↥D := by
    intro x
    have hσ12ker : σ ^ 12 ∈ (autQuotient (Subgroup.center ↥D)).ker := by
      rw [MonoidHom.mem_ker, map_pow, hσ12]
    exact (mem_ker_autQuotient (Subgroup.center ↥D)).mp hσ12ker x
  have hα3 : α ^ 3 = 1 := by
    ext x
    obtain ⟨z, hz, hx⟩ : ∃ z ∈ Subgroup.center ↥D, α x = x * z := by
      refine ⟨x⁻¹ * α x, hαquot x, ?_⟩
      group
    have hαz : α z = z := hαZ z hz
    have hαZpow : ∀ n : ℕ, (α ^ n) z = z := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hαz, ih]
    have hpow : ∀ n : ℕ, (α ^ n) x = x * z ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, MulAut.mul_apply, hx, map_mul, hαZpow n, ih, pow_succ]
          group
    have h3 := hpow 3
    rw [hZexp z hz] at h3
    simpa using h3
  rw [show (36 : ℕ) = 12 * 3 by norm_num, pow_mul]
  exact hα3

theorem pow_thirtySix_commute_of_normalizer (hexp : ∀ x ∈ D, x ^ 3 = 1)
    (hcl : ∀ x ∈ D, ∀ x' ∈ D, ⁅x, x'⁆ ∈ Subgroup.centralizer (D : Set G))
    (hidx : (Subgroup.centralizer (D : Set G)).relIndex D = 9)
    {y : G} (hy : y ∈ Subgroup.normalizer (D : Set G))
    (hyZ : ∀ z ∈ D, z ∈ Subgroup.centralizer (D : Set G) → y * z = z * y) :
    ∀ x ∈ D, y ^ 36 * x = x * y ^ 36 := by
  classical
  letI : (Subgroup.center ↥D).Characteristic := Subgroup.centerCharacteristic
  obtain ⟨e⟩ := exists_coord_center_quotient (D := D) hidx hexp hcl
  have hnc := exists_not_comm_of_card_center_quotient_eq_nine (D := D)
    (card_center_quotient_eq_nine (D := D) hidx)
  let yN : Subgroup.normalizer (D : Set G) := ⟨y, hy⟩
  let σ : MulAut ↥D := D.normalizerMonoidHom yN
  have hcD := commutator_mem_center_of_classTwo (D := D) hcl
  have hZexp : ∀ z ∈ Subgroup.center ↥D, z ^ 3 = 1 :=
    fun z hz => Subtype.ext (hexp (z : G) z.2)
  have hfix : ∀ c ∈ Subgroup.center ↥D, σ c = c :=
    normalizer_aut_fixes_center (D := D) hy hyZ
  have hσ12 := autQuotient_center_pow_twelve_eq_one (D := D) hcD hZexp hnc e hfix
  have hσ36 := autQuotient_center_pow_thirtySix_eq_one (D := D) hZexp hfix hσ12
  intro x hx
  let xD : ↥D := ⟨x, hx⟩
  have hxfix : (σ ^ 36) xD = xD := by rw [hσ36]; rfl
  have hamb : y ^ 36 * x * (y ^ 36)⁻¹ = x := by
    have h1 : (σ ^ 36) xD = xD := hxfix
    have h1v := congrArg Subtype.val h1
    have hσdef : σ = D.normalizerMonoidHom yN := rfl
    rw [hσdef] at h1v
    have hmap : (D.normalizerMonoidHom yN) ^ 36 = D.normalizerMonoidHom (yN ^ 36) :=
      (map_pow (D.normalizerMonoidHom) yN 36).symm
    rw [hmap, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1v
    simpa [yN, Subgroup.coe_pow] using h1v
  calc y ^ 36 * x = (y ^ 36 * x * (y ^ 36)⁻¹) * y ^ 36 := by group
    _ = x * y ^ 36 := by rw [hamb]

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree
