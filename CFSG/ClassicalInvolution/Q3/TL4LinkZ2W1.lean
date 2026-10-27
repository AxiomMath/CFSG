module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W0
public import CFSG.GH74.KGroups.PSLN
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G3Defs
public import CFSG.ClassicalInvolution.Q3.TL4MF163Psl

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.Blueprint
open scoped commutatorElement

section Setup

theorem exists_psl2_setup {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup ↥(genFittingFStar X))
    {p f : ℕ} (hp2 : p ≠ 2) (hl : LieModel (TL4.FStarQuot X) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧ 4 ≤ p ^ f ∧ p.Prime ∧
      Subgroup.centralizer ((genFittingFStar X : Subgroup X) : Set X) = ⊥ ∧
      Nonempty (↥(genFittingFStar X) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  obtain ⟨hp, h4, F, _, _, hFcard, ⟨e⟩⟩ := TL4.MF163.psl2_of_lieModel hl
  have := hs
  refine ⟨F, inferInstance, inferInstance, hFcard, h4, hp, ?_⟩
  set N := genFittingFStar X with hN
  have hnab : ∃ a b : N, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ :=
      ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian F
        (by omega) (by omega)
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm x)
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (e.symm y)
    refine ⟨a, b, fun hab => hxy ?_⟩
    have := congrArg (fun g => e (QuotientGroup.mk g : TL4.FStarQuot X)) hab
    simp only [QuotientGroup.mk_mul, map_mul] at this
    rwa [ha, hb, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  have hZ : Subgroup.center N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  exact ⟨CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot hnab,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e⟩⟩

end Setup

section L33

section Certificate43

private local instance : DecidableEq (Equiv.Perm (Fin 3)) := Fintype.decidableEqEquivFintype

private theorem certificate43_local :
      ∀ s t : Equiv.Perm (Fin 3),
        (s ≠ 1 ∧ s ^ 2 = 1) → (t ≠ 1 ∧ t ^ 2 = 1) → s ≠ t →
          (s * t) ^ 3 = 1 ∧ s * t ≠ 1 := by
  decide +kernel

end Certificate43

theorem sl3_three_center_eq_bot :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = ⊥ := by
  ext A
  rw [Subgroup.mem_bot, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have h1 : r = 1 := by
      have key : ∀ r : ZMod 3, r ^ 3 = 1 → r = 1 := by decide
      exact key r (by simpa using hr)
    subst h1
    apply Subtype.ext
    rw [← hA]
    simp
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

theorem card_psl3_three :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) = 5616 := by
  rw [CFSG.GH74.KGroups.PSLN.card_psl_of_center_bot sl3_three_center_eq_bot,
    Matrix.card_SL_field 3]
  norm_num [ZMod.card, Fin.prod_univ_three]

theorem psl3_three_of_lieModel {M : Type} [Group M] (h : LieModel M .PSL 3 3 1) :
    Nonempty (M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.GH74.KGroups.PSLN.psl_equiv_of_lieModel (F := ZMod 3) 3 3 1 (by norm_num)
    (by rw [Nat.card_zmod, pow_one]) h

theorem isSimpleGroup_of_lieModel_L33 {M : Type} [Group M] (h : LieModel M .PSL 3 3 1) :
    IsSimpleGroup M := by
  obtain ⟨e⟩ := psl3_three_of_lieModel h
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 3 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  exact e.isSimpleGroup

theorem eq_one_of_perfect_comm {G : Type*} [Group G] (hperf : commutator G = ⊤)
    (hcomm : ∀ a b : G, a * b = b * a) (g : G) : g = 1 := by
  have hle : commutator G ≤ ⊥ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, hcomm a b, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  rw [hperf, le_bot_iff] at hle
  have hg := Subgroup.mem_top g
  rwa [hle, Subgroup.mem_bot] at hg

theorem not_perfect_of_surjective_comm {G A : Type*} [Group G] [CommGroup A] (φ : G →* A)
    (hφ : Function.Surjective φ) {a : A} (ha : a ≠ 1) : commutator G ≠ ⊤ := by
  intro hperf
  have hle := Abelianization.commutator_subset_ker φ
  rw [hperf, top_le_iff] at hle
  obtain ⟨x, rfl⟩ := hφ a
  exact ha ((MonoidHom.mem_ker).mp (hle ▸ Subgroup.mem_top x))

@[expose] def dihedralParity (n : ℕ) : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun
    | .r _ => 1
    | .sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (a | a) (b | b) <;> simp only [DihedralGroup.r_mul_r,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    · rfl
    · exact (one_mul _).symm
    · exact (mul_one _).symm
    · change Multiplicative.ofAdd (0 : ZMod 2) = Multiplicative.ofAdd (1 + 1)
      decide

theorem dihedral_not_perfect (n : ℕ) : commutator (DihedralGroup n) ≠ ⊤ := by
  refine not_perfect_of_surjective_comm (dihedralParity n) ?_
    (a := Multiplicative.ofAdd (1 : ZMod 2)) (by decide)
  intro a
  have ha : a = 1 ∨ a = Multiplicative.ofAdd 1 := by
    revert a
    decide
  rcases ha with rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨DihedralGroup.sr 0, rfl⟩

theorem pgl2_not_perfect {K : Type} [Field K] [Finite K]
    (hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K)) :
    commutator (Matrix.ProjGenLinGroup (Fin 2) K) ≠ ⊤ := by
  intro hperf
  have hle := CFSG.GorensteinWalter.pgl2_commutator_le_psl2_range K
  rw [hperf, top_le_iff] at hle
  have h1 : Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) ≤
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
    rw [← Subgroup.card_top (G := Matrix.ProjGenLinGroup (Fin 2) K), ← hle]
    exact Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  rw [CFSG.GorensteinWalter.pgl2_card_formula, CFSG.GorensteinWalter.psl2_card_formula K hK]
    at h1
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hpos : 0 < Nat.card K * (Nat.card K ^ 2 - 1) := by
    apply Nat.mul_pos (by omega)
    have : 4 ≤ Nat.card K ^ 2 := by nlinarith
    omega
  have := Nat.div_lt_self hpos (by norm_num : 1 < 2)
  omega

theorem psl2_order_ne_5616 {x : ℕ} (hx : 3 ≤ x) : x * (x ^ 2 - 1) / 2 ≠ 5616 := by
  intro h
  rcases le_or_gt x 22 with hle | hgt
  · interval_cases x <;> norm_num at h
  · have h1 : 528 ≤ x ^ 2 - 1 := by
      have : 529 ≤ x ^ 2 := by nlinarith
      omega
    have h2 : 23 * 528 ≤ x * (x ^ 2 - 1) := Nat.mul_le_mul (by omega) h1
    omega

theorem psl2_not_onto_5616 {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hF : Nat.card F = p ^ f) {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hQ : Nat.card Q = 5616) (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (π : ↥H →* Q) (hπ : Function.Surjective π) : False := by
  have hQnc : ∃ a b : Q, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let G' : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcon }
    have hpr : (Nat.card Q).Prime := @IsSimpleGroup.prime_card Q G' ‹IsSimpleGroup Q›
    rw [hQ] at hpr
    exact absurd hpr (by norm_num)
  have hQperf : commutator Q = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hQnc
      have hmem : ⁅a, b⁆ ∈ commutator Q :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hab hmem
    · exact h
  have hQ1 : ∃ q : Q, q ≠ 1 := by
    obtain ⟨a, b, hab⟩ := hQnc
    by_cases ha : a = 1
    · exact ⟨b, fun hb => hab (by rw [ha, hb])⟩
    · exact ⟨a, ha⟩
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    obtain ⟨k, hk⟩ := hpodd
    omega
  induction hn : Nat.card H using Nat.strong_induction_on generalizing H with
  | _ n ih =>
  have hHbig : 5616 ≤ Nat.card H := hQ ▸ Nat.card_le_card_of_surjective π hπ
  by_cases hperf : commutator ↥H = ⊤
  · have := certificate43_local
    rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
      hE | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
        ⟨m, t, -, -, N, C, hN, hNe, -, hC, -, -, hNC⟩ | ⟨m, hm, hmf, ⟨e⟩⟩ | ⟨m, hm, hmf, ⟨e⟩⟩
    · have h1 := eq_one_of_perfect_comm hperf (fun a b => hE.toIsMulCommutative.is_comm.comm a b)
      have : Nat.card H = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by rw [h1 a, h1 b]⟩,
        ⟨1⟩⟩
      omega
    · let : CommGroup H := IsCyclic.commGroup
      have h1 := eq_one_of_perfect_comm hperf (fun a b => mul_comm a b)
      have : Nat.card H = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by rw [h1 a, h1 b]⟩,
        ⟨1⟩⟩
      omega
    · apply dihedral_not_perfect z
      have h1 := Subgroup.map_commutator (⊤ : Subgroup H) ⊤ e.toMonoidHom
      rw [← commutator_def, hperf, Subgroup.map_top_of_surjective _ e.surjective] at h1
      rw [commutator_def]
      exact h1.symm
    · have : Nat.card H = 12 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        rfl
      omega
    · have : Nat.card H = 24 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
          Fintype.card_fin]
        rfl
      omega
    · have : Nat.card H = 60 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        rfl
      omega
    ·
      have hNcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := fun a ha b hb =>
        congrArg Subtype.val (hNe.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      have hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
        intro a ha b hb
        let : CommGroup C := IsCyclic.commGroup
        exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : C) ⟨b, hb⟩)
      have hcomm : commutator H ≤ N := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        obtain ⟨n₁, hn₁, c₁, hc₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp
          (hNC ▸ Subgroup.mem_top a)
        obtain ⟨n₂, hn₂, c₂, hc₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp
          (hNC ▸ Subgroup.mem_top b)
        have h1 : QuotientGroup.mk' N n₁ = 1 := (QuotientGroup.eq_one_iff n₁).mpr hn₁
        have h2 : QuotientGroup.mk' N n₂ = 1 := (QuotientGroup.eq_one_iff n₂).mpr hn₂
        have hq : QuotientGroup.mk' N ⁅n₁ * c₁, n₂ * c₂⁆ = 1 := by
          rw [map_commutatorElement, map_mul, map_mul, h1, h2,
            one_mul, one_mul, ← map_commutatorElement, commutatorElement_def,
            hCcomm c₁ hc₁ c₂ hc₂, mul_inv_cancel_right, mul_inv_cancel, map_one]
        exact (QuotientGroup.eq_one_iff _).mp hq
      rw [hperf, top_le_iff] at hcomm
      have h1 := eq_one_of_perfect_comm hperf fun a b =>
        hNcomm a (hcomm ▸ Subgroup.mem_top a) b (hcomm ▸ Subgroup.mem_top b)
      have : Nat.card H = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by rw [h1 a, h1 b]⟩,
        ⟨1⟩⟩
      omega
    ·
      have hgcard : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
      have hpm : 3 ≤ p ^ m := (Nat.le_self_pow hm p).trans' hp3
      have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p m)) :=
        ⟨p, m, Fact.out, hpodd, Nat.one_le_iff_ne_zero.mpr hm, hgcard⟩
      have hHcard : Nat.card H = p ^ m * ((p ^ m) ^ 2 - 1) / 2 := by
        rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.psl2_card_formula _ hodd, hgcard]
      by_cases hpm3 : p ^ m = 3
      · rw [hHcard, hpm3] at hHbig
        norm_num at hHbig
      · have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m)) :=
          CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl
            (Or.inr (by rw [hgcard]; omega)) (Or.inr (by rw [hgcard]; exact hpm3))
        have : IsSimpleGroup H := e.isSimpleGroup
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hker | hker
        · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hker
          have hbij := Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩)
          exact psl2_order_ne_5616 hpm (by rw [← hHcard, hbij, hQ])
        · obtain ⟨q, hq⟩ := hQ1
          obtain ⟨x, rfl⟩ := hπ q
          exact hq ((MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top x))
    ·
      have hgcard : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
      have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p m)) :=
        ⟨p, m, Fact.out, hpodd, Nat.one_le_iff_ne_zero.mpr hm, hgcard⟩
      apply pgl2_not_perfect hodd
      have h1 := Subgroup.map_commutator (⊤ : Subgroup H) ⊤ e.toMonoidHom
      rw [← commutator_def, hperf, Subgroup.map_top_of_surjective _ e.surjective] at h1
      rw [commutator_def]
      exact h1.symm
  ·
    set D := commutator ↥H with hD
    let H' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := D.map H.subtype
    let e : ↥D ≃* ↥H' := D.equivMapOfInjective H.subtype H.subtype_injective
    have hlt : Nat.card H' < n := by
      rw [← hn, ← Nat.card_congr e.toEquiv]
      exact (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hperf)).trans_eq Subgroup.card_top
    have hsurj : Function.Surjective (π.comp (D.subtype.comp e.symm.toMonoidHom)) := by
      intro q
      have hq : q ∈ (D.map π) := by
        rw [hD, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hπ,
          ← commutator_def, hQperf]
        exact Subgroup.mem_top q
      obtain ⟨d, hd, rfl⟩ := hq
      exact ⟨e ⟨d, hd⟩, by simp⟩
    exact ih _ hlt H' _ hsurj rfl

end L33

section Emb

open CFSG.GorensteinWalter

theorem mulAut_congr_conj {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) := by
  apply MulEquiv.ext
  intro b
  simp [MulAut.congr_apply, MulAut.conj_apply]

variable {X : Type} [Group X] [Finite X]

noncomputable def restrictHom {N : Subgroup X} [N.Normal] [IsSimpleGroup N]
    (hC : Subgroup.centralizer (N : Set X) = ⊥) : MulAut X →* MulAut N where
  toFun β := TL4.MF163.restrictAut β (TL4.MF163.map_eq_of_centralizer_eq_bot hC β)
  map_one' := MulEquiv.ext fun n => Subtype.ext (by rw [TL4.MF163.coe_restrictAut]; rfl)
  map_mul' β γ := MulEquiv.ext fun n => Subtype.ext (by
    rw [TL4.MF163.coe_restrictAut, MulAut.mul_apply, MulAut.mul_apply,
      TL4.MF163.coe_restrictAut, TL4.MF163.coe_restrictAut])

theorem coe_restrictHom {N : Subgroup X} [N.Normal] [IsSimpleGroup N]
    (hC : Subgroup.centralizer (N : Set X) = ⊥) (β : MulAut X) (n : N) :
    ((restrictHom hC β n : N) : X) = β n :=
  TL4.MF163.coe_restrictAut _ _ n

theorem restrictHom_injective {N : Subgroup X} [N.Normal] [IsSimpleGroup N]
    (hC : Subgroup.centralizer (N : Set X) = ⊥) : Function.Injective (restrictHom hC) := by
  intro β γ h
  refine TL4.MF163.eq_of_eqOn hC (TL4.MF163.map_eq_of_centralizer_eq_bot hC γ) fun n hn => ?_
  have h1 := congrArg (fun φ : MulAut N => ((φ ⟨n, hn⟩ : N) : X)) h
  simpa only [coe_restrictHom] using h1

theorem restrictHom_conj {N : Subgroup X} [N.Normal] [IsSimpleGroup N]
    (hC : Subgroup.centralizer (N : Set X) = ⊥) (n : N) :
    restrictHom hC (MulAut.conj (n : X)) = MulAut.conj n :=
  MulEquiv.ext fun m => Subtype.ext (by
    rw [coe_restrictHom, MulAut.conj_apply, MulAut.conj_apply]
    rfl)

structure PGamEmb (X : Type) [Group X] (F : Type) [Field F] where
  ρ : MulAut X →* PGammaL2 F
  inj : Function.Injective ρ
  inner : ∀ n ∈ genFittingFStar X, ∃ g : PSL2 F,
    ρ (MulAut.conj n) = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL g)
  onto : ∀ g : PSL2 F, ∃ n ∈ genFittingFStar X,
    ρ (MulAut.conj n) = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL g)
  conjInj : Function.Injective (MulAut.conj : X →* MulAut X)

theorem exists_pgamEmb (hs : IsSimpleGroup ↥(genFittingFStar X)) {p f : ℕ} (hp2 : p ≠ 2)
    (hl : LieModel (TL4.FStarQuot X) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧ p.Prime ∧ 4 ≤ p ^ f ∧
      Nonempty (PGamEmb X F) := by
  obtain ⟨F, _, _, hF, h4, hp, hC, ⟨ψ⟩⟩ := exists_psl2_setup hs hp2 hl
  refine ⟨F, inferInstance, inferInstance, hF, hp, h4, ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at h4
    · exact h
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf1, hF⟩
  have hcard : 3 < Nat.card F := by omega
  have := hs
  have hNn : (genFittingFStar X).Normal := CFSG.ClassicalInvolution.genFittingFStar_normal X
  let θ : PGammaL2 F ≃* MulAut (PSL2 F) := MulEquiv.ofBijective
    (pGammaL2ToMulAutPSL2 F hK hcard) ⟨pGammaL2ToMulAutPSL2_injective F hK hcard,
      pGammaL2ToMulAutPSL2_surjective F hF hK hcard⟩
  have hθ : ∀ g : PSL2 F, θ.symm (MulAut.conj g) =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL g) := by
    intro g
    apply θ.injective
    rw [MulEquiv.apply_symm_apply]
    change MulAut.conj g = pGammaL2ToMulAutPSL2 F hK hcard _
    rw [pGammaL2ToMulAutPSL2_inl, pgl2InnerAutPSL2_toPGL]
  let ρ : MulAut X →* PGammaL2 F :=
    θ.symm.toMonoidHom.comp ((MulAut.congr ψ).toMonoidHom.comp (restrictHom hC))
  have hρ : ∀ n : genFittingFStar X, ρ (MulAut.conj (n : X)) =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (ψ n)) := by
    intro n
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, restrictHom_conj,
      mulAut_congr_conj, hθ]
  refine ⟨⟨ρ, ?_, fun n hn => ⟨ψ ⟨n, hn⟩, hρ ⟨n, hn⟩⟩, fun g => ?_, ?_⟩⟩
  · exact θ.symm.injective.comp ((MulAut.congr ψ).injective.comp (restrictHom_injective hC))
  · refine ⟨(ψ.symm g : X), (ψ.symm g).2, ?_⟩
    rw [hρ, MulEquiv.apply_symm_apply]
  · intro x y hxy
    have h1 : x⁻¹ * y ∈ Subgroup.centralizer ((genFittingFStar X : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n _
      have h3 := congrArg (fun φ : MulAut X => φ n) hxy
      simp only [MulAut.conj_apply] at h3
      calc n * (x⁻¹ * y) = x⁻¹ * (x * n * x⁻¹) * y := by group
        _ = x⁻¹ * (y * n * y⁻¹) * y := by rw [h3]
        _ = x⁻¹ * y * n := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1

theorem PGamEmb.right_sq {F : Type} [Field F] (E : PGamEmb X F)
    (hidx : (genFittingFStar X).index ≤ 2) (x : X) :
    (E.ρ (MulAut.conj x)).right * (E.ρ (MulAut.conj x)).right = 1 := by
  have hx2 : x * x ∈ genFittingFStar X := by
    rcases (by omega : (genFittingFStar X).index = 1 ∨ (genFittingFStar X).index = 2 ∨
        (genFittingFStar X).index = 0) with h | h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      exact Subgroup.mem_top _
    · exact Subgroup.mul_self_mem_of_index_two h x
    · exact absurd h Subgroup.index_ne_zero_of_finite
  obtain ⟨g, hg⟩ := E.inner _ hx2
  rw [← SemidirectProduct.mul_right, ← map_mul, ← map_mul, hg]
  rfl

end Emb

section FieldAut

theorem ringEquiv_pow_eq_one {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]
    (hF : Nat.card F = p ^ f) (σ : F ≃+* F) : σ ^ f = 1 := by
  have := Fintype.ofFinite F
  have hcardF : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F p := charP_of_card_eq_prime_pow hcardF
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let e : (F ≃+* F) ≃* (F ≃ₐ[ZMod p] F) := {
    toFun := fun τ =>
      AlgEquiv.ofRingEquiv (f := τ) (by
        intro x
        have h :
            (τ.toRingHom.comp (algebraMap (ZMod p) F) : ZMod p →+* F) =
              algebraMap (ZMod p) F :=
          RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
    invFun := fun τ => τ.toRingEquiv
    left_inv := by intro τ; ext x; rfl
    right_inv := by intro τ; ext x; rfl
    map_mul' := by intro τ υ; ext x; rfl }
  have hfin : Module.finrank (ZMod p) F = f := by
    have h : Fintype.card F = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) F :=
      Module.card_eq_pow_finrank
    rw [hcardF, ZMod.card] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 (e σ)
  have hfrob : FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F ^ f = 1 := by
    rw [← hfin, ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
    exact pow_orderOf_eq_one _
  have h1 : e (σ ^ f) = 1 := by
    rw [map_pow]
    change (e σ) ^ f = 1
    rw [← hn]
    dsimp only
    rw [← pow_mul, mul_comm, pow_mul, hfrob, one_pow]
  exact e.injective (h1.trans (map_one e).symm)

theorem sq_eq_one_of_pow_two_pow {G : Type*} [Group G] {σ : G} {f k : ℕ} (hf : f % 4 = 2)
    (hσf : σ ^ f = 1) (hσk : σ ^ 2 ^ k = 1) : σ ^ 2 = 1 := by
  have h : σ ^ Nat.gcd (2 ^ k) f = 1 := pow_gcd_eq_one.2 ⟨hσk, hσf⟩
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Nat.gcd_dvd_left (2 ^ k) f)
  have hg : Nat.gcd (2 ^ k) f ∣ 2 := by
    rw [hjeq]
    rcases j with _ | _ | j
    · norm_num
    · norm_num
    · exfalso
      have h4 : 4 ∣ f := by
        have := Nat.gcd_dvd_right (2 ^ k) f
        rw [hjeq] at this
        exact (Dvd.intro (2 ^ j) (by ring)).trans this
      omega
  obtain ⟨m, hm⟩ := hg
  rw [hm, pow_mul, h, one_pow]

theorem mod_four_of_pow_mod_sixteen {p f : ℕ} (hp : Odd p) (hf : Even f) (h9 : p ^ f % 16 = 9) :
    f % 4 = 2 := by
  obtain ⟨g, rfl⟩ := hf
  rcases Nat.even_or_odd g with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · exfalso
    have : p ^ (h + h + (h + h)) = (p ^ 4) ^ h := by rw [← pow_mul]; ring_nf
    rw [this, Nat.pow_mod] at h9
    have hp4 : p ^ 4 % 16 = 1 := by
      obtain ⟨k, rfl⟩ := hp
      have hev : Even (k * (3 * k + 1)) := by
        rcases Nat.even_or_odd k with hk | hk
        · exact Nat.even_mul.mpr (Or.inl hk)
        · refine Nat.even_mul.mpr (Or.inr ?_)
          obtain ⟨t, rfl⟩ := hk
          exact ⟨3 * t + 2, by ring⟩
      obtain ⟨r, hr⟩ := hev
      have : (2 * k + 1) ^ 4 = 16 * (k ^ 4 + 2 * k ^ 3 + r) + 1 := by
        calc (2 * k + 1) ^ 4 = 16 * (k ^ 4 + 2 * k ^ 3) + 8 * (k * (3 * k + 1)) + 1 := by ring
          _ = 16 * (k ^ 4 + 2 * k ^ 3 + r) + 1 := by rw [hr]; ring
      omega
    rw [hp4, one_pow] at h9
    norm_num at h9
  · omega

end FieldAut

section Quat

open CFSG.GorensteinWalter

variable {F : Type} [Field F] [Finite F]

theorem inl_inj' {a b : PGL2 F} (h : (SemidirectProduct.inl a : PGammaL2 F) = SemidirectProduct.inl b) :
    a = b :=
  SemidirectProduct.inl_injective h

theorem q8_outside : ∀ c g : QuaternionGroup 2, c ^ 2 = QuaternionGroup.a 2 →
    ¬ (g = 1 ∨ g = c ∨ g = QuaternionGroup.a 2 ∨ g = c⁻¹) →
      g * c * g⁻¹ = c⁻¹ ∧ g ^ 2 = QuaternionGroup.a 2 := by
  decide

theorem q8_inverter_outside : ∀ c y : QuaternionGroup 2, c ^ 2 = QuaternionGroup.a 2 →
    y * c * y⁻¹ = c⁻¹ → ¬ (y = 1 ∨ y = c ∨ y = QuaternionGroup.a 2 ∨ y = c⁻¹) := by
  decide

theorem q8_a_two_comm : ∀ g : QuaternionGroup 2,
    g * QuaternionGroup.a 2 = QuaternionGroup.a 2 * g := by
  decide

theorem exists_pgl_quat (hK : IsOddPrimePower (Nat.card F)) (h2 : (2 : F) ≠ 0)
    (ρ : QuaternionGroup 2 →* PGammaL2 F) (hρ : Function.Injective ρ) :
    ∃ c₀ : QuaternionGroup 2, c₀ ^ 2 = QuaternionGroup.a 2 ∧ (ρ c₀).right = 1 ∧
      ∀ g, (ρ g).right = 1 → g = 1 ∨ g = c₀ ∨ g = QuaternionGroup.a 2 ∨ g = c₀⁻¹ := by
  have : IsCyclic (F ≃+* F) := TL4.MF163.ringAut_isCyclic F hK
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  have hr2 : ∀ g : QuaternionGroup 2, g ^ 2 = QuaternionGroup.a 2 →
      (ρ g).right * (ρ g).right = 1 := by
    intro g hg
    rw [← SemidirectProduct.mul_right, ← map_mul, ← sq, hg, TL4.MF163.right_a_two hK]
  obtain ⟨c₀, hc₀, hc₀r⟩ : ∃ c₀ : QuaternionGroup 2, c₀ ^ 2 = QuaternionGroup.a 2 ∧
      (ρ c₀).right = 1 := by
    by_cases h1 : (ρ (QuaternionGroup.a 1)).right = 1
    · exact ⟨QuaternionGroup.a 1, by decide, h1⟩
    by_cases h2' : (ρ (QuaternionGroup.xa 0)).right = 1
    · exact ⟨QuaternionGroup.xa 0, by decide, h2'⟩
    refine ⟨QuaternionGroup.a 1 * QuaternionGroup.xa 0, by decide, ?_⟩
    have he := TL4.MF163.eq_of_mul_self_eq_one (hr2 _ (by decide)) (hr2 _ (by decide)) h1 h2'
    rw [map_mul, SemidirectProduct.mul_right, he, ← SemidirectProduct.mul_right, ← map_mul,
      ← sq, show (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 by decide,
      TL4.MF163.right_a_two hK]
  refine ⟨c₀, hc₀, hc₀r, fun g hg => ?_⟩
  by_contra hng
  obtain ⟨hinv, hsq⟩ := q8_outside c₀ g hc₀ hng
  have hge := TL4.MF163.eq_inl_of_right_eq_one hg
  have hce := TL4.MF163.eq_inl_of_right_eq_one hc₀r
  have hz : ρ (QuaternionGroup.a 2) ≠ 1 := fun h =>
    absurd (hρ (h.trans (map_one ρ).symm)) (by decide)
  have hc2 : (ρ c₀).left ^ 2 ≠ 1 := by
    intro h1
    apply hz
    rw [← hc₀, map_pow, hce, ← map_pow, h1, map_one]
  have hc4 : (ρ c₀).left ^ 4 = 1 := by
    have h5 : (SemidirectProduct.inl ((ρ c₀).left ^ 4) : PGammaL2 F) = SemidirectProduct.inl 1 := by
      rw [map_pow, ← hce, ← map_pow, show c₀ ^ 4 = (c₀ ^ 2) ^ 2 by rw [← pow_mul], hc₀,
        show (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 by decide, map_one, map_one]
    exact SemidirectProduct.inl_injective h5
  have hinvL : (ρ g).left * (ρ c₀).left * ((ρ g).left)⁻¹ = ((ρ c₀).left)⁻¹ := by
    apply inl_inj'
    rw [map_mul, map_mul, map_inv, map_inv, ← hge, ← hce, ← map_inv, ← map_inv, ← map_mul,
      ← map_mul, hinv]
  have hw := TL4.MF163.pgl2_mul_self_of_inv h2 hc2 hc4 hinvL
  apply hz
  rw [← hsq, map_pow, hge, sq, ← map_mul, hw, map_one]

@[expose] def q8Eval (u v : QuaternionGroup 2) : QuaternionGroup 2 → QuaternionGroup 2
  | .a k => u ^ k.val
  | .xa k => v * u ^ k.val

theorem eq_q8Eval (φ : QuaternionGroup 2 →* QuaternionGroup 2) (g : QuaternionGroup 2) :
    φ g = q8Eval (φ (QuaternionGroup.a 1)) (φ (QuaternionGroup.xa 0)) g := by
  cases g with
  | a k =>
    have : QuaternionGroup.a k = (QuaternionGroup.a 1 : QuaternionGroup 2) ^ k.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    change φ (QuaternionGroup.a k) = φ (QuaternionGroup.a 1) ^ k.val
    rw [this, map_pow]
  | xa k =>
    have : QuaternionGroup.xa k =
        (QuaternionGroup.xa 0 : QuaternionGroup 2) * (QuaternionGroup.a 1) ^ k.val := by
      rw [QuaternionGroup.a_one_pow, QuaternionGroup.xa_mul_a, ZMod.natCast_zmod_val, zero_add]
    change φ (QuaternionGroup.xa k) = φ (QuaternionGroup.xa 0) * φ (QuaternionGroup.a 1) ^ k.val
    rw [this, map_mul, map_pow]

theorem q8Eval_pow_four : ∀ u v c : QuaternionGroup 2,
    (∀ g h, q8Eval u v (g * h) = q8Eval u v g * q8Eval u v h) → c ^ 2 = QuaternionGroup.a 2 →
      (q8Eval u v c = c ∨ q8Eval u v c = c⁻¹) →
        ∀ g, q8Eval u v (q8Eval u v (q8Eval u v (q8Eval u v g))) = g := by
  decide

theorem q8_aut_pow_four (φ : QuaternionGroup 2 →* QuaternionGroup 2) {c : QuaternionGroup 2}
    (hc : c ^ 2 = QuaternionGroup.a 2) (hφc : φ c = c ∨ φ c = c⁻¹) (g : QuaternionGroup 2) :
    φ (φ (φ (φ g))) = g := by
  have hev := eq_q8Eval φ
  rw [hev (φ (φ (φ g))), hev (φ (φ g)), hev (φ g), hev g]
  refine q8Eval_pow_four _ _ c (fun g h => ?_) hc ?_ g
  · rw [← hev, ← hev, ← hev, map_mul]
  · rw [← hev]
    exact hφc

end Quat

section PiFacts

open CFSG.GorensteinWalter

variable {F : Type} [Field F] [Finite F]

theorem pgl2_eq_of_comm_four (h2 : (2 : F) ≠ 0) {c g : PGL2 F} (hc2 : c ^ 2 ≠ 1)
    (hc4 : c ^ 4 = 1) (hgc : g * c = c * g) (hg2 : g ^ 2 ≠ 1) (hg4 : g ^ 4 = 1) :
    g = c ∨ g = c⁻¹ := by
  have hcomm : Commute g c := hgc
  have hsq : g ^ 2 = c ^ 2 := by
    rcases TL4.MF163.pgl2_eq_of_comm h2 hc2 hc4 (b := g ^ 2) (hcomm.pow_left 2).eq
        (by rw [← pow_add]; exact hg4) with h | h
    · exact absurd h hg2
    · exact h
  have hh : (g * c⁻¹) * (g * c⁻¹) = 1 := by
    have hci : g * c⁻¹ = c⁻¹ * g := hcomm.inv_right.eq
    calc (g * c⁻¹) * (g * c⁻¹) = g * (c⁻¹ * g) * c⁻¹ := by group
      _ = g * (g * c⁻¹) * c⁻¹ := by rw [← hci]
      _ = g ^ 2 * (c ^ 2)⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hsq, mul_inv_cancel]
  rcases TL4.MF163.pgl2_eq_of_comm h2 hc2 hc4 (b := g * c⁻¹)
      ((hcomm.mul_left (Commute.inv_left (Commute.refl c))).eq) hh with h | h
  · left
    rw [mul_inv_eq_one] at h
    exact h
  · right
    rw [mul_inv_eq_iff_eq_mul, ← pow_succ] at h
    rw [h]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hc4)

theorem pgl2_eq_of_comm_quat (h2 : (2 : F) ≠ 0) {c g : PGL2 F} {y : PGammaL2 F}
    (hc2 : c ^ 2 ≠ 1) (hc4 : c ^ 4 = 1)
    (hy : y * SemidirectProduct.inl c * y⁻¹ = (SemidirectProduct.inl c)⁻¹)
    (hgc : g * c = c * g) (hgy : SemidirectProduct.inl g * y = y * SemidirectProduct.inl g)
    {k : ℕ} (hgk : g ^ 2 ^ k = 1) : g = 1 ∨ g = c ^ 2 := by
  by_cases hg2 : g ^ 2 = 1
  · exact TL4.MF163.pgl2_eq_of_comm h2 hc2 hc4 hgc (by rw [← sq]; exact hg2)
  exfalso
  obtain ⟨j, hj⟩ : ∃ j, orderOf g = 2 ^ j := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hgk)
    exact ⟨j, hj⟩
  have hj2 : 2 ≤ j := by
    by_contra hlt
    apply hg2
    have : orderOf g ∣ 2 := by
      rw [hj]
      exact (pow_dvd_pow 2 (show j ≤ 1 by omega)).trans (by norm_num)
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hcomm : Commute g c := hgc
  have hg4 : (g ^ 2 ^ (j - 2)) ^ 4 = 1 := by
    rw [← pow_mul, show 2 ^ (j - 2) * 4 = 2 ^ j by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega, ← hj]
    exact pow_orderOf_eq_one g
  have hg2' : (g ^ 2 ^ (j - 2)) ^ 2 ≠ 1 := by
    intro h
    rw [← pow_mul] at h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hj, show 2 ^ (j - 2) * 2 = 2 ^ (j - 1) by
      rw [← pow_succ]; congr 1; omega] at h1
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 h1
    omega
  have hy' : SemidirectProduct.inl (g ^ 2 ^ (j - 2)) * y =
      y * SemidirectProduct.inl (g ^ 2 ^ (j - 2)) := by
    rw [map_pow]
    exact (Commute.pow_left hgy _).eq
  have hfix : y * SemidirectProduct.inl c * y⁻¹ = SemidirectProduct.inl c := by
    rcases pgl2_eq_of_comm_four h2 hc2 hc4 (hcomm.pow_left _).eq hg2' hg4 with h | h
    · rw [h] at hy'
      rw [← hy', mul_inv_cancel_right]
    · rw [h, map_inv] at hy'
      have h3 := congrArg (·⁻¹) hy'
      simp only [mul_inv_rev, inv_inv] at h3
      calc y * SemidirectProduct.inl c * y⁻¹ = y * (SemidirectProduct.inl c * y⁻¹) := by group
        _ = y * (y⁻¹ * SemidirectProduct.inl c) := by rw [h3]
        _ = SemidirectProduct.inl c := by group
  rw [hfix] at hy
  apply hc2
  apply inl_inj'
  rw [map_pow, sq, map_one]
  nth_rewrite 2 [hy]
  exact mul_inv_cancel _

theorem q8_exists_inverter : ∀ c : QuaternionGroup 2, c ^ 2 = QuaternionGroup.a 2 →
    ∃ y : QuaternionGroup 2, y * c * y⁻¹ = c⁻¹ := by
  decide

theorem right_pow (b : PGammaL2 F) (n : ℕ) : (b ^ n).right = b.right ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, SemidirectProduct.mul_right, ih, pow_succ]

theorem conj_pow_eq {G : Type*} [Group G] (b x : G) (φ : G → G) (hφ : ∀ x, b * x * b⁻¹ = φ x)
    (n : ℕ) : b ^ n * x * (b ^ n)⁻¹ = φ^[n] x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ← ih, ← hφ x, pow_succ]
    group

theorem pi_facts (hK : IsOddPrimePower (Nat.card F)) (h2 : (2 : F) ≠ 0)
    (ρ : QuaternionGroup 2 →* PGammaL2 F) (hρ : Function.Injective ρ) {b : PGammaL2 F}
    (hbr : b.right * b.right = 1) {k : ℕ} (hbk : b ^ 2 ^ k = 1)
    (hb : ∀ g, ∃ h, b * ρ g * b⁻¹ = ρ h) :
    b ^ 8 = 1 ∧ (b ^ 4 = 1 → b ^ 2 = 1 ∨ b ^ 2 = ρ (QuaternionGroup.a 2)) := by
  classical
  obtain ⟨c₀, hc₀, hc₀r, hcpgl⟩ := exists_pgl_quat hK h2 ρ hρ
  let φf : QuaternionGroup 2 → QuaternionGroup 2 := fun g => Classical.choose (hb g)
  have hφf : ∀ g, ρ (φf g) = b * ρ g * b⁻¹ := fun g => (Classical.choose_spec (hb g)).symm
  let φ : QuaternionGroup 2 →* QuaternionGroup 2 :=
    { toFun := φf
      map_one' := hρ (by rw [hφf, map_one, mul_one, mul_inv_cancel])
      map_mul' := fun g h => hρ (by rw [map_mul, hφf, hφf, hφf, map_mul]; group) }
  have hφ : ∀ g, ρ (φ g) = b * ρ g * b⁻¹ := hφf
  have hz : ρ (QuaternionGroup.a 2) ≠ 1 := fun h =>
    absurd (hρ (h.trans (map_one ρ).symm)) (by decide)
  have hφc : φ c₀ = c₀ ∨ φ c₀ = c₀⁻¹ := by
    have hr : (ρ (φ c₀)).right = 1 := by
      rw [hφ, SemidirectProduct.mul_right, SemidirectProduct.mul_right, hc₀r,
        SemidirectProduct.inv_right, mul_one, mul_inv_cancel]
    have hsq : φ c₀ ^ 2 ≠ 1 := by
      intro h
      apply hz
      have : ρ (φ (QuaternionGroup.a 2)) = 1 := by rw [← hc₀, map_pow, h, map_one]
      rw [hφ] at this
      calc ρ (QuaternionGroup.a 2) = b⁻¹ * (b * ρ (QuaternionGroup.a 2) * b⁻¹) * b := by group
        _ = 1 := by rw [this]; group
    rcases hcpgl _ hr with h | h | h | h
    · exact absurd (by rw [h, one_pow]) hsq
    · exact Or.inl h
    · exact absurd (by rw [h]; decide) hsq
    · exact Or.inr h
  have hiter : ∀ (n : ℕ) (g : QuaternionGroup 2), b ^ n * ρ g * (b ^ n)⁻¹ = ρ ((⇑φ)^[n] g) := by
    intro n g
    have h1 := conj_pow_eq b (ρ g) (fun x => b * x * b⁻¹) (fun _ => rfl) n
    rw [h1]
    clear h1
    induction n generalizing g with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hφ]
      exact ih (φ g)
  have hb4c : ∀ g, b ^ 4 * ρ g = ρ g * b ^ 4 := by
    intro g
    have h1 := hiter 4 g
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply] at h1
    rw [q8_aut_pow_four φ hc₀ hφc g] at h1
    calc b ^ 4 * ρ g = b ^ 4 * ρ g * (b ^ 4)⁻¹ * b ^ 4 := by group
      _ = ρ g * b ^ 4 := by rw [h1]
  have hb4r : (b ^ 4).right = 1 := by
    rw [right_pow, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, show b.right ^ 2 = 1 by rw [sq, hbr],
      one_pow]
  have hb4e := TL4.MF163.eq_inl_of_right_eq_one hb4r
  have hce := TL4.MF163.eq_inl_of_right_eq_one hc₀r
  set c := (ρ c₀).left with hcdef
  have hc2 : c ^ 2 ≠ 1 := by
    intro h1
    apply hz
    rw [← hc₀, map_pow, hce, ← map_pow, h1, map_one]
  have hc4 : c ^ 4 = 1 := by
    apply inl_inj'
    rw [map_pow, ← hce, ← map_pow, show c₀ ^ 4 = (c₀ ^ 2) ^ 2 by rw [← pow_mul], hc₀,
      show (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 by decide, map_one, map_one]
  obtain ⟨y₀, hy₀⟩ := q8_exists_inverter c₀ hc₀
  have hy : ρ y₀ * SemidirectProduct.inl c * (ρ y₀)⁻¹ = (SemidirectProduct.inl c)⁻¹ := by
    rw [← hce, ← map_inv, ← map_mul, ← map_mul, hy₀, map_inv]
  have hb4 : b ^ 4 = 1 ∨ b ^ 4 = ρ (QuaternionGroup.a 2) := by
    have hgc : (b ^ 4).left * c = c * (b ^ 4).left := by
      apply inl_inj'
      rw [map_mul, map_mul, ← hb4e, ← hce]
      exact hb4c c₀
    have hgy : SemidirectProduct.inl (b ^ 4).left * ρ y₀ = ρ y₀ * SemidirectProduct.inl (b ^ 4).left := by
      rw [← hb4e]
      exact hb4c y₀
    have hgk : (b ^ 4).left ^ 2 ^ k = 1 := by
      apply inl_inj'
      rw [map_pow, ← hb4e, ← pow_mul, mul_comm, pow_mul, hbk, one_pow, map_one]
    rcases pgl2_eq_of_comm_quat h2 hc2 hc4 hy hgc hgy hgk with h | h
    · left
      rw [hb4e, h, map_one]
    · right
      rw [hb4e, h, map_pow, ← hce, ← map_pow, hc₀]
  refine ⟨?_, fun h4 => ?_⟩
  · rcases hb4 with h | h
    · rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, h, one_pow]
    · rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, h, ← map_pow,
        show (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 by decide, map_one]
  ·
    have hb2r : (b ^ 2).right = 1 := by rw [right_pow, sq, hbr]
    have hb2e := TL4.MF163.eq_inl_of_right_eq_one hb2r
    have hφφ : φ (φ c₀) = c₀ := by
      rcases hφc with h | h
      · rw [h, h]
      · rw [h, map_inv, h, inv_inv]
    have hwc : (b ^ 2).left * c = c * (b ^ 2).left := by
      apply inl_inj'
      rw [map_mul, map_mul, ← hb2e, ← hce]
      have h1 := hiter 2 c₀
      simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, hφφ] at h1
      calc b ^ 2 * ρ c₀ = b ^ 2 * ρ c₀ * (b ^ 2)⁻¹ * b ^ 2 := by group
        _ = ρ c₀ * b ^ 2 := by rw [h1]
    have hww : (b ^ 2).left * (b ^ 2).left = 1 := by
      apply inl_inj'
      rw [map_mul, ← hb2e, ← pow_add, h4, map_one]
    rcases TL4.MF163.pgl2_eq_of_comm h2 hc2 hc4 hwc hww with h | h
    · left
      rw [hb2e, h, map_one]
    · right
      rw [hb2e, h, map_pow, ← hce, ← map_pow, hc₀]

end PiFacts

section OutFacts

open CFSG.GorensteinWalter

variable {F : Type} [Field F] [Finite F]

noncomputable abbrev pslRange (F : Type) [Field F] : Subgroup (PGL2 F) :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range

theorem fieldAut_mem_pslRange_iff (σ : F ≃+* F) (x : PGL2 F) :
    pgl2FieldAut F σ x ∈ pslRange F ↔ x ∈ pslRange F := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨psl2FieldAut F σ⁻¹ y, ?_⟩
    rw [psl2FieldAut_toPGL, hy, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      MulAut.one_apply]
  · rintro ⟨y, rfl⟩
    exact ⟨psl2FieldAut F σ y, psl2FieldAut_toPGL σ y⟩

theorem left_mul_mem_iff (hK : IsOddPrimePower (Nat.card F)) (x y : PGammaL2 F) :
    (x * y).left ∈ pslRange F ↔ (x.left ∈ pslRange F ↔ y.left ∈ pslRange F) := by
  rw [SemidirectProduct.mul_left, Subgroup.mul_mem_iff_of_index_two
    (pgl2_psl2Range_index_eq_two F hK), fieldAut_mem_pslRange_iff]

theorem left_inv_mem_iff (x : PGammaL2 F) :
    (x⁻¹).left ∈ pslRange F ↔ x.left ∈ pslRange F := by
  rw [SemidirectProduct.inv_left, fieldAut_mem_pslRange_iff, inv_mem_iff]

theorem pgammaL2_commutator_mem (hK : IsOddPrimePower (Nat.card F)) (a b : PGammaL2 F) :
    ∃ g : PSL2 F, a * b * a⁻¹ * b⁻¹ =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL g) := by
  have : IsCyclic (F ≃+* F) := TL4.MF163.ringAut_isCyclic F hK
  have hcomm : ∀ x y : F ≃+* F, x * y = y * x := fun x y => IsCyclic.commGroup.mul_comm x y
  have hr : (a * b * a⁻¹ * b⁻¹).right = 1 := by
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right]
    rw [hcomm a.right b.right]
    group
  have hl : (a * b * a⁻¹ * b⁻¹).left ∈ pslRange F := by
    rw [left_mul_mem_iff hK, left_mul_mem_iff hK, left_mul_mem_iff hK, left_inv_mem_iff,
      left_inv_mem_iff]
    tauto
  obtain ⟨g, hg⟩ := hl
  exact ⟨g, by rw [TL4.MF163.eq_inl_of_right_eq_one hr, ← hg]⟩

theorem mul_inv_mem_of_not_mem (hK : IsOddPrimePower (Nat.card F))
    (Xt : Subgroup (PGammaL2 F)) (hS : ∀ s ∈ pslRange F, SemidirectProduct.inl s ∈ Xt)
    {x₀ : PGammaL2 F} (hx₀ : x₀ ∈ Xt) (hx₀r : x₀.right ≠ 1) (hx₀r2 : x₀.right * x₀.right = 1)
    {a b : PGammaL2 F} (ha : a ∉ Xt) (hb : b ∉ Xt) (har : a.right * a.right = 1)
    (hbr : b.right * b.right = 1) (hna : a * x₀ * a⁻¹ ∈ Xt) (hnb : b * x₀ * b⁻¹ ∈ Xt) :
    a * b⁻¹ ∈ Xt := by
  have : IsCyclic (F ≃+* F) := TL4.MF163.ringAut_isCyclic F hK
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  have hmemS : ∀ y : PGammaL2 F, y.right = 1 → y.left ∈ pslRange F → y ∈ Xt := by
    intro y hy hyl
    rw [TL4.MF163.eq_inl_of_right_eq_one hy]
    exact hS _ hyl
  have hout : ∀ y : PGammaL2 F, y ∉ Xt → y.right = 1 → y.left ∉ pslRange F :=
    fun y hy hyr hyl => hy (hmemS y hyr hyl)
  have hred : ∀ y : PGammaL2 F, y ∉ Xt → y.right * y.right = 1 →
      ∃ y' : PGammaL2 F, y'.right = 1 ∧ y'.left ∉ pslRange F ∧
        (y = y' ∨ y = y' * x₀) := by
    intro y hy hyr
    by_cases h1 : y.right = 1
    · exact ⟨y, h1, hout y hy h1, Or.inl rfl⟩
    · have heq : y.right = x₀.right := TL4.MF163.eq_of_mul_self_eq_one hyr hx₀r2 h1 hx₀r
      have hr : (y * x₀⁻¹).right = 1 := by
        rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right, heq, mul_inv_cancel]
      refine ⟨y * x₀⁻¹, hr, hout _ (fun hm => hy ?_) hr, Or.inr (by group)⟩
      have := Xt.mul_mem hm hx₀
      rwa [inv_mul_cancel_right] at this
  obtain ⟨a', ha'r, ha'l, ha'⟩ := hred a ha har
  obtain ⟨b', hb'r, hb'l, hb'⟩ := hred b hb hbr
  have hab : a' * b'⁻¹ ∈ Xt := by
    refine hmemS _ (by rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right, ha'r, hb'r,
      inv_one, mul_one]) ?_
    rw [left_mul_mem_iff hK, left_inv_mem_iff]
    tauto
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
  · rw [ha', hb']
    exact hab
  · have h1 : b' * x₀⁻¹ * b'⁻¹ ∈ Xt := by
      have h2 : b * x₀ * b⁻¹ = b' * x₀ * b'⁻¹ := by rw [hb']; group
      have h3 := Xt.inv_mem (h2 ▸ hnb)
      have h4 : (b' * x₀ * b'⁻¹)⁻¹ = b' * x₀⁻¹ * b'⁻¹ := by group
      rwa [h4] at h3
    rw [ha', hb', show a' * (b' * x₀)⁻¹ = (a' * b'⁻¹) * (b' * x₀⁻¹ * b'⁻¹) by group]
    exact Xt.mul_mem hab h1
  · have h1 : a' * x₀ * a'⁻¹ ∈ Xt := by
      have h2 : a * x₀ * a⁻¹ = a' * x₀ * a'⁻¹ := by rw [ha']; group
      exact h2 ▸ hna
    rw [ha', hb', show a' * x₀ * b'⁻¹ = (a' * x₀ * a'⁻¹) * (a' * b'⁻¹) by group]
    exact Xt.mul_mem h1 hab
  · rw [ha', hb', show a' * x₀ * (b' * x₀)⁻¹ = a' * b'⁻¹ by group]
    exact hab

end OutFacts

section Coord

open CFSG.GorensteinWalter

variable {F : Type} [Field F]

@[expose] noncomputable def glD (x : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(x : F), 0; 0, 1] (by simp)

@[expose] noncomputable def glA (x : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, (x : F); 1, 0] (by simp)

@[expose] noncomputable def pD (x : Fˣ) : PGL2 F := Matrix.ProjGenLinGroup.mk (glD x)

@[expose] noncomputable def pA (x : Fˣ) : PGL2 F := Matrix.ProjGenLinGroup.mk (glA x)

theorem glD_val (x : Fˣ) : ((glD x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![(x : F), 0; 0, 1] := rfl

theorem glA_val (x : Fˣ) : ((glA x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![0, (x : F); 1, 0] := rfl

theorem scalar_val' (u : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(u : F), 0; 0, (u : F)] := by
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem pD_mul (x y : Fˣ) : pD x * pD y = pD (x * y) := by
  rw [pD, pD, pD, ← map_mul]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.coe_mul, glD_val, glD_val, glD_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem pD_one : pD (1 : Fˣ) = 1 := by
  rw [pD, ← Matrix.ProjGenLinGroup.mk_one]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [glD_val]
  fin_cases i <;> fin_cases j <;> simp

theorem pD_pow (x : Fˣ) (n : ℕ) : pD x ^ n = pD (x ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pD_one]
  | succ n ih => rw [pow_succ, ih, pD_mul, pow_succ]

theorem pD_eq_iff {x y : Fˣ} : pD x = pD y ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [pD, pD, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  have h00 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) hu
  have h11 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 1 1) hu
  simp only [Matrix.GeneralLinearGroup.coe_mul, glD_val, scalar_val', Matrix.mul_apply,
    Fin.sum_univ_two] at h00 h11
  simp at h00 h11
  apply Units.ext
  rw [← h00, h11, Units.val_one, mul_one]

theorem pD_eq_one_iff {x : Fˣ} : pD x = 1 ↔ x = 1 := by
  rw [← pD_one, pD_eq_iff]

theorem pA_mul_pA (x y : Fˣ) : pA x * pA y = pD (x * y⁻¹) := by
  rw [pA, pA, pD, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨y⁻¹, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, glA_val, glA_val,
    scalar_val', glD_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem pD_mul_pA (x y : Fˣ) : pD x * pA y = pA (x * y) := by
  rw [pA, pA, pD, ← map_mul]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.coe_mul, glD_val, glA_val, glA_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem pA_mul_pD (x y : Fˣ) : pA x * pD y = pA (x * y⁻¹) := by
  rw [pA, pA, pD, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨y⁻¹, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, glA_val, glD_val,
    scalar_val', glA_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem pA_eq_iff {x y : Fˣ} : pA x = pA y ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [pA, pA, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  have h01 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) hu
  have h10 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 1 0) hu
  simp only [Matrix.GeneralLinearGroup.coe_mul, glA_val, scalar_val', Matrix.mul_apply,
    Fin.sum_univ_two] at h01 h10
  simp at h01 h10
  apply Units.ext
  rw [← h01, h10, Units.val_one, mul_one]

theorem pA_mul_self (x : Fˣ) : pA x * pA x = 1 := by
  rw [pA_mul_pA, mul_inv_cancel, pD_one]

theorem comm_pD_neg_one (h2 : (2 : F) ≠ 0) {g : PGL2 F} (hg : g * pD (-1) = pD (-1) * g) :
    (∃ x, g = pD x) ∨ ∃ x, g = pA x := by
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk G => ?_
  rw [pD, ← map_mul, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hg
  obtain ⟨u, hu⟩ := hg
  have hdet := (Matrix.GeneralLinearGroup.det G).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at hdet
  have e00 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) hu
  have e01 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) hu
  have e10 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 1 0) hu
  have e11 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 1 1) hu
  simp only [Matrix.GeneralLinearGroup.coe_mul, glD_val, scalar_val', Matrix.mul_apply,
    Fin.sum_univ_two] at e00 e01 e10 e11
  simp at e00 e01 e10 e11
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  by_cases ha : (G : Matrix (Fin 2) (Fin 2) F) 0 0 = 0
  ·
    right
    have hb : (G : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := by
      intro hb
      apply hdet
      rw [ha, hb]
      ring
    have hc : (G : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      intro hc
      apply hdet
      rw [ha, hc]
      ring
    have hu1 : (u : F) = -1 := by
      have : (G : Matrix (Fin 2) (Fin 2) F) 0 1 * ((u : F) + 1) = 0 := by linear_combination e01
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hb
      · linear_combination h
    have hd : (G : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
      have : (G : Matrix (Fin 2) (Fin 2) F) 1 1 * 2 = 0 := by
        rw [hu1] at e11; linear_combination -e11
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h h2
    refine ⟨Units.mk0 ((G : Matrix (Fin 2) (Fin 2) F) 0 1 / (G : Matrix (Fin 2) (Fin 2) F) 1 0)
      (div_ne_zero hb hc), ?_⟩
    rw [pA, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 ((G : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹ (inv_ne_zero hc),
      Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_mul, scalar_val', glA_val]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hd, hc] <;>
      field_simp
  ·
    left
    have hu1 : (u : F) = 1 := by
      have : (G : Matrix (Fin 2) (Fin 2) F) 0 0 * ((u : F) - 1) = 0 := by linear_combination e00
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h ha
      · linear_combination h
    have hb : (G : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      have : (G : Matrix (Fin 2) (Fin 2) F) 0 1 * 2 = 0 := by
        rw [hu1] at e01; linear_combination e01
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h h2
    have hc : (G : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have : (G : Matrix (Fin 2) (Fin 2) F) 1 0 * 2 = 0 := by
        rw [hu1] at e10; linear_combination -e10
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h h2
    have hd : (G : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
      intro hd
      apply hdet
      rw [hb, hd]
      ring
    refine ⟨Units.mk0 ((G : Matrix (Fin 2) (Fin 2) F) 0 0 / (G : Matrix (Fin 2) (Fin 2) F) 1 1)
      (div_ne_zero ha hd), ?_⟩
    rw [pD, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 ((G : Matrix (Fin 2) (Fin 2) F) 1 1)⁻¹ (inv_ne_zero hd),
      Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_mul, scalar_val', glD_val]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb, hc, hd] <;>
      field_simp

theorem fieldAut_pD (σ : F ≃+* F) (x : Fˣ) :
    pgl2FieldAut F σ (pD x) = pD (Units.map σ.toRingHom.toMonoidHom x) := by
  change pgl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (glD x)) =
    Matrix.ProjGenLinGroup.mk (glD _)
  rw [pgl2RingEquiv_mk]
  change Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [glD_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map, glD_val]

theorem fieldAut_pA (σ : F ≃+* F) (x : Fˣ) :
    pgl2FieldAut F σ (pA x) = pA (Units.map σ.toRingHom.toMonoidHom x) := by
  change pgl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (glA x)) =
    Matrix.ProjGenLinGroup.mk (glA _)
  rw [pgl2RingEquiv_mk]
  change Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [glA_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map, glA_val]

theorem pD_neg_one_mem (i : Fˣ) (hi : i ^ 2 = -1) :
    ∃ g : PSL2 F, Matrix.ProjectiveSpecialLinearGroup.toPGL g = pD (-1) := by
  have hdet : (!![(i : F), 0; 0, -(i : F)]).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have : ((i : F)) ^ 2 = -1 := by simpa using congrArg Units.val hi
    linear_combination -this
  let S : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![(i : F), 0; 0, -(i : F)], hdet⟩
  refine ⟨(S : PSL2 F), ?_⟩
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, pD, eq_comm,
    Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨-i, Matrix.GeneralLinearGroup.ext fun a b => ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_mul, scalar_val', glD_val,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  change _ = (!![(i : F), 0; 0, -(i : F)] : Matrix (Fin 2) (Fin 2) F) a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem pA_one_mem (i : Fˣ) (hi : i ^ 2 = -1) :
    ∃ g : PSL2 F, Matrix.ProjectiveSpecialLinearGroup.toPGL g = pA 1 := by
  have hdet : (!![0, (i : F); (i : F), 0]).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have : ((i : F)) ^ 2 = -1 := by simpa using congrArg Units.val hi
    linear_combination -this
  let S : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![0, (i : F); (i : F), 0], hdet⟩
  refine ⟨(S : PSL2 F), ?_⟩
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, pA, eq_comm,
    Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨i, Matrix.GeneralLinearGroup.ext fun a b => ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_mul, scalar_val', glA_val,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  change _ = (!![0, (i : F); (i : F), 0] : Matrix (Fin 2) (Fin 2) F) a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end Coord

section Mod16

variable {F : Type} [Field F] [Finite F]

theorem exists_sq_eq_neg_one_units (h4 : 4 ∣ Nat.card Fˣ) : ∃ i : Fˣ, i ^ 2 = -1 := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf ζ = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hζ
  obtain ⟨n, hn⟩ := h4
  have hpos : 0 < Nat.card Fˣ := Nat.card_pos
  refine ⟨ζ ^ n, ?_⟩
  have h1 : (ζ ^ n) ^ 2 ≠ 1 := by
    rw [← pow_mul]
    intro h
    have h3 := orderOf_dvd_of_pow_eq_one h
    rw [hord, hn] at h3
    have := Nat.le_of_dvd (by omega) h3
    omega
  have h2' : ((ζ ^ n) ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_mul, show n * (2 * 2) = Nat.card Fˣ by rw [hn]; ring, ← hord,
      pow_orderOf_eq_one]
  have key : ∀ u : Fˣ, u ^ 2 = 1 → u = 1 ∨ u = -1 := by
    intro u hu
    have h5 : (u : F) * u = 1 := by
      have := congrArg Units.val hu
      simpa [sq] using this
    rcases mul_self_eq_one_iff.mp h5 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by simp [h]))
  rcases key _ h2' with h | h
  · exact absurd h h1
  · exact h

theorem neg_one_ne_one_units (h2 : (2 : F) ≠ 0) : (-1 : Fˣ) ≠ 1 := by
  intro h
  have h1 := congrArg Units.val h
  simp only [Units.val_neg, Units.val_one] at h1
  apply h2
  linear_combination -h1

theorem exists_zpow_of_involution (φ : F ≃+* F) (hφ : φ * φ = 1) :
    ∃ k : ℤ, (∀ g : Fˣ, Units.map φ.toRingHom.toMonoidHom g = g ^ k) ∧
      (Nat.card Fˣ : ℤ) ∣ k * k - 1 := by
  obtain ⟨k, hk⟩ := MonoidHom.map_cyclic (Units.map φ.toRingHom.toMonoidHom)
  refine ⟨k, hk, ?_⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf ζ = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hζ
  rw [← hord, orderOf_dvd_iff_zpow_eq_one]
  have h1 : Units.map φ.toRingHom.toMonoidHom (Units.map φ.toRingHom.toMonoidHom ζ) = ζ := by
    apply Units.ext
    have := DFunLike.congr_fun hφ (ζ : F)
    simpa [RingAut.mul_apply] using this
  rw [hk, hk, ← zpow_mul] at h1
  rw [zpow_sub, zpow_one, h1, mul_inv_cancel]

theorem eight_dvd_add_one {k : ℤ} (h16 : (16 : ℤ) ∣ k * k - 1) (h4 : (4 : ℤ) ∣ k + 1) :
    (8 : ℤ) ∣ k + 1 := by
  obtain ⟨j, hj⟩ := h4
  have hk : k * k - 1 = 16 * (j * j) - 8 * j := by
    have : k = 4 * j - 1 := by linarith
    rw [this]; ring
  have h8 : (16 : ℤ) ∣ 8 * j := by
    have := dvd_sub (dvd_mul_right (16 : ℤ) (j * j)) (hk ▸ h16)
    simpa using this
  omega

theorem eight_dvd_sub_one {k : ℤ} (h16 : (16 : ℤ) ∣ k * k - 1) (h4 : (4 : ℤ) ∣ k - 1) :
    (8 : ℤ) ∣ k - 1 := by
  obtain ⟨j, hj⟩ := h4
  have hk : k * k - 1 = 16 * (j * j) + 8 * j := by
    have : k = 4 * j + 1 := by linarith
    rw [this]; ring
  have h8 : (16 : ℤ) ∣ 8 * j := by
    have := dvd_sub (hk ▸ h16) (dvd_mul_right (16 : ℤ) (j * j))
    simpa using this
  omega

theorem orderOf_eq_four_of_sq (h2 : (2 : F) ≠ 0) {x₀ : Fˣ} (hx₀ : x₀ ^ 2 = -1) :
    orderOf x₀ = 4 := by
  have hx4 : x₀ ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hx₀]
    norm_num
  have hx2 : x₀ ^ 2 ≠ 1 := by rw [hx₀]; exact neg_one_ne_one_units h2
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hx2) (by simpa using hx4)

theorem order_contra_diag (h2 : (2 : F) ≠ 0) (h16 : 16 ∣ Nat.card Fˣ) (φ : F ≃+* F)
    (hφ : φ * φ = 1) {x₀ ν : Fˣ} (hx₀ : x₀ ^ 2 = -1)
    (hx : Units.map φ.toRingHom.toMonoidHom x₀ = x₀⁻¹)
    (hν : Units.map φ.toRingHom.toMonoidHom ν = -ν⁻¹) {m : ℕ} (hm : Odd m) :
    (Units.map φ.toRingHom.toMonoidHom ν * ν⁻¹) ^ (4 * m) ≠ 1 := by
  obtain ⟨k, hk, hdiv⟩ := exists_zpow_of_involution φ hφ
  have h16' : (16 : ℤ) ∣ k * k - 1 := (Int.natCast_dvd_natCast.mpr h16).trans hdiv
  rw [hk] at hx hν
  have hx1 : x₀ ^ (k + 1) = 1 := by rw [zpow_add_one, hx, inv_mul_cancel]
  have h4 : (4 : ℤ) ∣ k + 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr hx1
    rw [orderOf_eq_four_of_sq h2 hx₀] at this
    exact_mod_cast this
  obtain ⟨t, ht⟩ := eight_dvd_add_one h16' h4
  have hν1 : ν ^ (k + 1) = -1 := by rw [zpow_add_one, hν, neg_mul, inv_mul_cancel]
  rw [hk]
  intro hc
  have hc' : ν ^ ((k - 1) * (4 * m : ℕ)) = 1 := by
    rw [zpow_mul, zpow_sub_one, zpow_natCast]
    exact hc
  have hν2 : ν ^ ((k + 1) * (4 * m : ℕ)) = 1 := by
    rw [zpow_mul, hν1, zpow_natCast, show 4 * m = 2 * (2 * m) by ring, pow_mul]
    norm_num
  have h8m : ν ^ ((8 * m : ℕ) : ℤ) = 1 := by
    have : ((8 * m : ℕ) : ℤ) = (k + 1) * (4 * m : ℕ) - (k - 1) * (4 * m : ℕ) := by
      push_cast; ring
    rw [this, zpow_sub, hν2, hc', mul_inv_cancel]
  have hmk : ν ^ ((m : ℤ) * (k + 1)) = 1 := by
    rw [ht, show (m : ℤ) * (8 * t) = ((8 * m : ℕ) : ℤ) * t by push_cast; ring, zpow_mul, h8m,
      one_zpow]
  rw [mul_comm, zpow_mul, hν1, zpow_natCast, hm.neg_one_pow] at hmk
  exact neg_one_ne_one_units h2 hmk

theorem order_contra_anti (h2 : (2 : F) ≠ 0) (h16 : 16 ∣ Nat.card Fˣ) (φ : F ≃+* F)
    (hφ : φ * φ = 1) {x₀ ν : Fˣ} (hx₀ : x₀ ^ 2 = -1)
    (hx : Units.map φ.toRingHom.toMonoidHom x₀ = x₀)
    (hν : Units.map φ.toRingHom.toMonoidHom ν = -ν) {m : ℕ} (hm : Odd m) :
    (ν * Units.map φ.toRingHom.toMonoidHom ν) ^ (4 * m) ≠ 1 := by
  obtain ⟨k, hk, hdiv⟩ := exists_zpow_of_involution φ hφ
  have h16' : (16 : ℤ) ∣ k * k - 1 := (Int.natCast_dvd_natCast.mpr h16).trans hdiv
  rw [hk] at hx hν
  have hx1 : x₀ ^ (k - 1) = 1 := by rw [zpow_sub_one, hx, mul_inv_cancel]
  have h4 : (4 : ℤ) ∣ k - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr hx1
    rw [orderOf_eq_four_of_sq h2 hx₀] at this
    exact_mod_cast this
  obtain ⟨t, ht⟩ := eight_dvd_sub_one h16' h4
  have hν1 : ν ^ (k - 1) = -1 := by rw [zpow_sub_one, hν, neg_mul, mul_inv_cancel]
  rw [hk]
  intro hc
  have hc' : ν ^ ((k + 1) * (4 * m : ℕ)) = 1 := by
    rw [zpow_mul, zpow_add_one, mul_comm, zpow_natCast]
    exact hc
  have hν2 : ν ^ ((k - 1) * (4 * m : ℕ)) = 1 := by
    rw [zpow_mul, hν1, zpow_natCast, show 4 * m = 2 * (2 * m) by ring, pow_mul]
    norm_num
  have h8m : ν ^ ((8 * m : ℕ) : ℤ) = 1 := by
    have : ((8 * m : ℕ) : ℤ) = (k + 1) * (4 * m : ℕ) - (k - 1) * (4 * m : ℕ) := by
      push_cast; ring
    rw [this, zpow_sub, hν2, hc', mul_inv_cancel]
  have hmk : ν ^ ((m : ℤ) * (k - 1)) = 1 := by
    rw [ht, show (m : ℤ) * (8 * t) = ((8 * m : ℕ) : ℤ) * t by push_cast; ring, zpow_mul, h8m,
      one_zpow]
  rw [mul_comm, zpow_mul, hν1, zpow_natCast, hm.neg_one_pow] at hmk
  exact neg_one_ne_one_units h2 hmk

end Mod16

section Mod16Elt

open CFSG.GorensteinWalter

variable {F : Type} [Field F] [Finite F]

theorem inl_mul_left (A : PGL2 F) (w : PGammaL2 F) :
    (SemidirectProduct.inl A * w).left = A * w.left := by
  rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one,
    MulAut.one_apply]

theorem inl_mul_right (A : PGL2 F) (w : PGammaL2 F) :
    (SemidirectProduct.inl A * w).right = w.right := by
  rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]

theorem mul_inl_left (w : PGammaL2 F) (A : PGL2 F) :
    (w * SemidirectProduct.inl A).left = w.left * pgl2FieldAut F w.right A := by
  rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl]

theorem pD_inv (x : Fˣ) : (pD x)⁻¹ = pD x⁻¹ :=
  (eq_inv_of_mul_eq_one_left (by rw [pD_mul, inv_mul_cancel, pD_one])).symm

theorem units_map_neg_one (φ : F ≃+* F) : Units.map φ.toRingHom.toMonoidHom (-1 : Fˣ) = -1 := by
  apply Units.ext
  simp

theorem exists_large_order {X : Type} [Group X] [Finite X] (E : PGamEmb X F)
    (hidx : (genFittingFStar X).index ≤ 2) (hK : IsOddPrimePower (Nat.card F)) (h2 : (2 : F) ≠ 0)
    (h16 : 16 ∣ Nat.card Fˣ) {i : Fˣ} (hi : i ^ 2 = -1) (P : Subgroup X)
    (e : ↥P ≃* QuaternionGroup 2)
    (hz : E.ρ (MulAut.conj ((e.symm (QuaternionGroup.a 2) : ↥P) : X)) =
      SemidirectProduct.inl (pD (-1))) :
    ∃ xa : X, xa * ((e.symm (QuaternionGroup.a 2) : ↥P) : X) =
        ((e.symm (QuaternionGroup.a 2) : ↥P) : X) * xa ∧
      ∀ m : ℕ, Odd m → E.ρ (MulAut.conj xa) ^ (8 * m) ≠ 1 := by
  set z : X := ((e.symm (QuaternionGroup.a 2) : ↥P) : X) with hzdef
  let ρ' : QuaternionGroup 2 →* PGammaL2 F :=
    E.ρ.comp (MulAut.conj.comp (P.subtype.comp e.symm.toMonoidHom))
  have hρ' : Function.Injective ρ' :=
    E.inj.comp (E.conjInj.comp (Subtype.val_injective.comp e.symm.injective))
  have hρz : ρ' (QuaternionGroup.a 2) = SemidirectProduct.inl (pD (-1)) := hz
  obtain ⟨c₀, hc₀, hc₀r, hcpgl⟩ := exists_pgl_quat hK h2 ρ' hρ'
  have hce := TL4.MF163.eq_inl_of_right_eq_one hc₀r
  set c := (ρ' c₀).left with hcdef
  have hcc : c * c = pD (-1) := by
    apply inl_inj'
    rw [map_mul, ← hce, ← map_mul, ← sq, hc₀, hρz]
  obtain ⟨x₀, hx₀c, hx₀⟩ : ∃ x₀ : Fˣ, c = pD x₀ ∧ x₀ ^ 2 = -1 := by
    rcases comm_pD_neg_one h2 (g := c) (by rw [← hcc, mul_assoc]) with ⟨x, hx⟩ | ⟨x, hx⟩
    · refine ⟨x, hx, ?_⟩
      rw [hx, pD_mul] at hcc
      rw [sq]
      exact pD_eq_iff.mp hcc
    · exfalso
      rw [hx, pA_mul_self] at hcc
      exact neg_one_ne_one_units h2 (pD_eq_one_iff.mp hcc.symm)
  obtain ⟨y₀, hy₀⟩ := q8_exists_inverter c₀ hc₀
  have hy₀out := q8_inverter_outside c₀ y₀ hc₀ hy₀
  have hy₀2 : y₀ ^ 2 = QuaternionGroup.a 2 := (q8_outside c₀ y₀ hc₀ hy₀out).2
  set y := ρ' y₀ with hydef
  set φ := y.right with hφdef
  set Y := y.left with hYdef
  have hφ2 : φ * φ = 1 := E.right_sq hidx _
  have hyφ : (y * y).right = 1 := by rw [SemidirectProduct.mul_right, hφ2]
  have hyz : y * SemidirectProduct.inl (pD (-1)) = SemidirectProduct.inl (pD (-1)) * y := by
    rw [← hρz, hydef, ← map_mul, ← map_mul, q8_a_two_comm]
  have hyy : y * y = SemidirectProduct.inl (pD (-1)) := by
    rw [← hρz, hydef, ← map_mul, ← sq, hy₀2]
  have hyc : y * SemidirectProduct.inl c = SemidirectProduct.inl c⁻¹ * y := by
    rw [← hce, map_inv, ← hce, hydef, ← map_inv, ← map_mul, ← map_mul,
      show y₀ * c₀ = c₀⁻¹ * y₀ by rw [← hy₀]; group]
  have hYz : Y * pD (-1) = pD (-1) * Y := by
    have h1 := congrArg SemidirectProduct.left hyz
    rw [mul_inl_left, inl_mul_left, fieldAut_pD, units_map_neg_one] at h1
    exact h1
  have hYY : Y * pgl2FieldAut F φ Y = pD (-1) := by
    have h1 := congrArg SemidirectProduct.left hyy
    rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl] at h1
    exact h1
  have hYc : Y * pgl2FieldAut F φ c = c⁻¹ * Y := by
    have h1 := congrArg SemidirectProduct.left hyc
    rw [mul_inl_left, inl_mul_left] at h1
    exact h1
  obtain ⟨w₁, hw₁⟩ := pA_one_mem i hi
  obtain ⟨n₁, -, hn₁⟩ := E.onto w₁
  rw [hw₁] at hn₁
  set a := SemidirectProduct.inl (pA 1) * y with hadef
  have hxa : E.ρ (MulAut.conj (n₁ * ((e.symm y₀ : ↥P) : X))) = a := by
    rw [map_mul, map_mul, hn₁]
    rfl
  have hal : a.left = pA 1 * Y := inl_mul_left _ _
  have har : a.right = φ := inl_mul_right _ _
  have haa : (a * a).right = 1 := by rw [SemidirectProduct.mul_right, har, hφ2]
  have haae := TL4.MF163.eq_inl_of_right_eq_one haa
  have hAz : pA (1 : Fˣ) * pD (-1 : Fˣ) = pD (-1 : Fˣ) * pA (1 : Fˣ) := by
    rw [pA_mul_pD, pD_mul_pA, inv_neg_one, one_mul, mul_one]
  have haz : a * SemidirectProduct.inl (pD (-1)) = SemidirectProduct.inl (pD (-1)) * a := by
    rw [hadef, mul_assoc, hyz, ← mul_assoc, ← map_mul, hAz, map_mul, mul_assoc]
  obtain ⟨xa, hxa'⟩ : ∃ xa : X, E.ρ (MulAut.conj xa) = a := ⟨_, hxa⟩
  clear hxa
  refine ⟨xa, ?_, fun m hm => ?_⟩
  · apply E.conjInj
    apply E.inj
    rw [show MulAut.conj (xa * z) = MulAut.conj xa * MulAut.conj z from map_mul _ _ _,
      show MulAut.conj (z * xa) = MulAut.conj z * MulAut.conj xa from map_mul _ _ _,
      map_mul, map_mul, hxa', hz, haz]
  · rw [hxa']
    have hpow : a ^ (8 * m) = (a * a) ^ (4 * m) := by
      rw [← sq, ← pow_mul]
      ring_nf
    rw [hpow, haae]
    intro hc
    rw [← map_pow] at hc
    have hc' : (a * a).left ^ (4 * m) = 1 := by
      have := congrArg SemidirectProduct.left hc
      rwa [SemidirectProduct.left_inl, SemidirectProduct.one_left] at this
    have hφu : ∀ x : Fˣ, pgl2FieldAut F φ (pD x) = pD (Units.map φ.toRingHom.toMonoidHom x) :=
      fun x => fieldAut_pD φ x
    rcases comm_pD_neg_one h2 hYz with ⟨ν, hν⟩ | ⟨ν, hν⟩
    ·
      have hνν : Units.map φ.toRingHom.toMonoidHom ν = -ν⁻¹ := by
        rw [hν, hφu, pD_mul] at hYY
        have h3 := pD_eq_iff.mp hYY
        calc Units.map φ.toRingHom.toMonoidHom ν = ν⁻¹ * (ν * Units.map φ.toRingHom.toMonoidHom ν) := by
              group
          _ = -ν⁻¹ := by rw [h3]; simp
      have hxx : Units.map φ.toRingHom.toMonoidHom x₀ = x₀⁻¹ := by
        rw [hν, hx₀c, hφu, pD_mul, pD_inv, pD_mul] at hYc
        have h3 := pD_eq_iff.mp hYc
        calc Units.map φ.toRingHom.toMonoidHom x₀ = ν⁻¹ * (ν * Units.map φ.toRingHom.toMonoidHom x₀) := by
              group
          _ = x₀⁻¹ := by rw [h3, mul_comm x₀⁻¹ ν, inv_mul_cancel_left]
      have hleft : (a * a).left = pD (Units.map φ.toRingHom.toMonoidHom ν * ν⁻¹) := by
        rw [SemidirectProduct.mul_left, hal, har, map_mul, fieldAut_pA, hν, hφu, pA_mul_pD,
          pA_mul_pD, pA_mul_pA, map_one, one_mul, one_mul, inv_inv, mul_comm]
      rw [hleft, pD_pow, pD_eq_one_iff] at hc'
      exact order_contra_diag h2 h16 φ hφ2 hx₀ hxx hνν hm hc'
    ·
      have hνν : Units.map φ.toRingHom.toMonoidHom ν = -ν := by
        rw [hν, fieldAut_pA, pA_mul_pA] at hYY
        have h3 := pD_eq_iff.mp hYY
        calc Units.map φ.toRingHom.toMonoidHom ν =
              (ν * (Units.map φ.toRingHom.toMonoidHom ν)⁻¹)⁻¹ * ν := by group
          _ = -ν := by rw [h3]; simp
      have hxx : Units.map φ.toRingHom.toMonoidHom x₀ = x₀ := by
        rw [hν, hx₀c, hφu, pA_mul_pD, pD_inv, pD_mul_pA, pA_eq_iff] at hYc
        calc Units.map φ.toRingHom.toMonoidHom x₀ =
              ((ν * (Units.map φ.toRingHom.toMonoidHom x₀)⁻¹)⁻¹ * ν) := by group
          _ = x₀ := by
            rw [hYc, mul_inv_rev, inv_inv, mul_comm ν⁻¹ x₀, mul_assoc, inv_mul_cancel, mul_one]
      have hleft : (a * a).left = pD (ν * Units.map φ.toRingHom.toMonoidHom ν)⁻¹ := by
        rw [SemidirectProduct.mul_left, hal, har, map_mul, fieldAut_pA, hν, fieldAut_pA,
          pA_mul_pA, pA_mul_pA, map_one, one_mul, one_mul, pD_mul, mul_inv]
      rw [hleft, ← pD_inv, inv_pow, inv_eq_one, pD_pow, pD_eq_one_iff] at hc'
      exact order_contra_anti h2 h16 φ hφ2 hx₀ hxx hνν hm hc'

theorem tight_pow_eight {X : Type} [Group X] [Finite X] (E : PGamEmb X F)
    (hidx : (genFittingFStar X).index ≤ 2) (hK : IsOddPrimePower (Nat.card F)) (h2 : (2 : F) ≠ 0)
    {Φ : Set (Subgroup X)} (hR : TypeRFam 3 Φ) {M : Subgroup X} (hM : M ∈ Φ) {z : X}
    (hz : IsUniqueInvolution M z) {x : X} (hxz : x * z = z * x) {j : ℕ} (hxj : x ^ 2 ^ j = 1) :
    E.ρ (MulAut.conj x) ^ 8 = 1 := by
  have hxN : x ∈ Subgroup.normalizer (M : Set X) :=
    hR.tight M hM z hz (Subgroup.mem_centralizer_singleton_iff.mpr hxz)
  have hW : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨j, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxj, one_zpow]
  obtain ⟨R, hRM, hfix⟩ := CFSG.ClassicalInvolution.Asc77.T3.exists_sylow_normalized hW
    (Subgroup.zpowers_le.mpr hxN)
  obtain ⟨eR⟩ := hR.quat M hM R hRM
  have eR' : ↥R ≃* QuaternionGroup 2 := eR
  let ρR : QuaternionGroup 2 →* PGammaL2 F :=
    E.ρ.comp (MulAut.conj.comp (R.subtype.comp eR'.symm.toMonoidHom))
  have hρR : Function.Injective ρR :=
    E.inj.comp (E.conjInj.comp (Subtype.val_injective.comp eR'.symm.injective))
  have hb : ∀ g, ∃ h, E.ρ (MulAut.conj x) * ρR g * (E.ρ (MulAut.conj x))⁻¹ = ρR h := by
    intro g
    have hmem : x * ((eR'.symm g : ↥R) : X) * x⁻¹ ∈ R := by
      have := Generic.conj_mem_conjSub (n := x) (eR'.symm g).2
      rwa [hfix x (Subgroup.mem_zpowers x)] at this
    refine ⟨eR' ⟨_, hmem⟩, ?_⟩
    simp only [ρR, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype]
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
  have hbk : E.ρ (MulAut.conj x) ^ 2 ^ j = 1 := by rw [← map_pow, ← map_pow, hxj, map_one, map_one]
  exact (pi_facts hK h2 ρR hρR (E.right_sq hidx x) hbk hb).1

end Mod16Elt

section Assembly

open CFSG.GorensteinWalter

theorem field_facts {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (h4 : 4 ≤ p ^ f) :
    IsOddPrimePower (Nat.card F) ∧ (2 : F) ≠ 0 := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at h4
    · exact h
  refine ⟨⟨p, f, hp, hp.odd_of_ne_two hp2, hf1, hF⟩, ?_⟩
  have := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  intro h0
  have h1 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h0
  rw [CharP.cast_eq_zero_iff F p 2] at h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)

variable {X : Type} [Group X]

theorem mulAut_mul_conj_mul_inv (β : MulAut X) (x : X) :
    β * MulAut.conj x * β⁻¹ = MulAut.conj (β x) := by
  apply MulEquiv.ext
  intro y
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.apply_inv_self]

end Assembly

theorem odd_sq_mod_sixteen {q : ℕ} (hq : Odd q) : q ^ 2 % 16 = 1 ∨ q ^ 2 % 16 = 9 := by
  rw [Nat.pow_mod]
  have h1 : q % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h3 : (q % 16) % 2 = 1 := by
    have := Nat.odd_iff.mp hq
    omega
  generalize q % 16 = r at h1 h3 ⊢
  interval_cases r <;> simp_all

theorem modelL2Q8Mod16_proved :
    ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), LieLinkSection Φ →
      IsSimpleGroup ↥(genFittingFStar X) → (genFittingFStar X).index ≤ 2 →
      ∀ p f : ℕ, p.Prime → p ≠ 2 → Even f → LieModel (FStarQuot X) .PSL 2 p f → p ^ f % 16 = 9 := by
  intro X _ _ Φ hΦ hs hidx p f hp hp2 hf hl
  obtain ⟨hR, -, hgen, -⟩ := hΦ
  obtain ⟨g, rfl⟩ := hf
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hsq : p ^ (g + g) % 16 = 1 ∨ p ^ (g + g) % 16 = 9 := by
    rw [← two_mul, mul_comm, pow_mul]
    exact odd_sq_mod_sixteen hpodd.pow
  rcases hsq with h1 | h9
  swap
  · exact h9
  exfalso
  obtain ⟨F, _, _, hF, -, h4, ⟨E⟩⟩ := exists_pgamEmb hs hp2 hl
  obtain ⟨hK, h2⟩ := field_facts hp hp2 hF h4
  have : Fact p.Prime := ⟨hp⟩
  have h16 : 16 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have : 1 ≤ p ^ (g + g) := Nat.one_le_pow _ _ hp.pos
    omega
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one_units ((by norm_num : 4 ∣ 16).trans h16)
  obtain ⟨M₀, hM₀⟩ : Φ.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hbot : omegaGen Φ = ⊥ := by
      rw [omegaGen, hne]
      simp
    rw [hgen] at hbot
    have := hs.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(genFittingFStar X))
    apply hx
    apply Subtype.ext
    have hx' : (x : X) ∈ (⊤ : Subgroup X) := Subgroup.mem_top _
    rw [hbot, Subgroup.mem_bot] at hx'
    exact hx'
  obtain ⟨⟨z₀, hz₀⟩, -⟩ := hR.hyp.omega1 M₀ hM₀
  have hsqN : ∀ x : X, x * x ∈ genFittingFStar X := by
    intro x
    rcases (by omega : (genFittingFStar X).index = 1 ∨ (genFittingFStar X).index = 2 ∨
        (genFittingFStar X).index = 0) with h | h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      exact Subgroup.mem_top _
    · exact Subgroup.mul_self_mem_of_index_two h x
    · exact absurd h Subgroup.index_ne_zero_of_finite
  have hinv : ∀ (L : Subgroup X) (w : X), IsUniqueInvolution L w → ∀ (Q : Subgroup X)
      (eQ : ↥Q ≃* QuaternionGroup 2), Q ≤ L → ((eQ.symm (QuaternionGroup.a 2) : ↥Q) : X) = w := by
    intro L w hw Q eQ hQL
    rcases hw.unique _ (hQL (eQ.symm (QuaternionGroup.a 2)).2) (by
        rw [← Subgroup.coe_mul, ← map_mul,
          show (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 by decide,
          map_one, Subgroup.coe_one]) with h | h
    · exfalso
      have h3 : eQ.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h
      rw [MulEquiv.symm_apply_eq, map_one] at h3
      exact absurd h3 (by decide)
    · exact h
  have hz₀N : z₀ ∈ genFittingFStar X := by
    obtain ⟨-, P₀, hP₀, -⟩ := hR.hyp.omega1 M₀ hM₀
    obtain ⟨e₀⟩ := hR.quat M₀ hM₀ P₀ hP₀
    have e₀' : ↥P₀ ≃* QuaternionGroup 2 := e₀
    rw [← hinv M₀ z₀ hz₀ P₀ e₀' hP₀.1,
      show (QuaternionGroup.a 2 : QuaternionGroup 2) = QuaternionGroup.a 1 * QuaternionGroup.a 1
        by decide, map_mul, Subgroup.coe_mul]
    exact hsqN _
  obtain ⟨g₀, hg₀⟩ := E.inner z₀ hz₀N
  obtain ⟨s₀, hs₀⟩ := pD_neg_one_mem i hi
  have hg₀inv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution g₀ := by
    refine ⟨fun h => hz₀.ne_one ?_, ?_⟩
    · apply E.conjInj
      apply E.inj
      rw [hg₀, h, map_one, map_one, map_one, map_one]
    · apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      apply inl_inj'
      rw [map_one, map_one, map_pow, map_pow, ← hg₀, ← map_pow, ← map_pow, sq, hz₀.sq, map_one,
        map_one]
  have hs₀inv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s₀ := by
    refine ⟨fun h => ?_, ?_⟩
    · rw [h, map_one] at hs₀
      exact neg_one_ne_one_units h2 (pD_eq_one_iff.mp hs₀.symm)
    · apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      rw [map_pow, hs₀, pD_pow, map_one, show ((-1 : Fˣ)) ^ 2 = 1 by norm_num, pD_one]
  obtain ⟨gc, hgc⟩ := CFSG.GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power F hK g₀
    s₀ hg₀inv hs₀inv
  obtain ⟨n, -, hn⟩ := E.onto gc
  set M := Generic.conjSub n M₀ with hMdef
  have hM : M ∈ Φ := hR.hyp.conjInvariant n M₀ hM₀
  have hz : IsUniqueInvolution M (n * z₀ * n⁻¹) := hz₀.conj n
  have hzρ : E.ρ (MulAut.conj (n * z₀ * n⁻¹)) = SemidirectProduct.inl (pD (-1)) := by
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hn, hg₀, ← map_inv, ← map_mul,
      ← map_mul, ← map_inv, ← map_mul, ← map_mul, hgc, hs₀]
  obtain ⟨-, P, hP, -⟩ := hR.hyp.omega1 M hM
  obtain ⟨eP⟩ := hR.quat M hM P hP
  have e : ↥P ≃* QuaternionGroup 2 := eP
  have hze : ((e.symm (QuaternionGroup.a 2) : ↥P) : X) = n * z₀ * n⁻¹ :=
    hinv M _ hz P e hP.1
  obtain ⟨xa, hxaz, hxa⟩ := exists_large_order E hidx hK h2 h16 hi P e (by rw [hze]; exact hzρ)
  rw [hze] at hxaz
  obtain ⟨j, m₀, hm₀, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos xa).ne'
  have hx'j : (xa ^ m₀) ^ 2 ^ j = 1 := by
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hx'z : xa ^ m₀ * (n * z₀ * n⁻¹) = (n * z₀ * n⁻¹) * xa ^ m₀ :=
    ((Commute.pow_left hxaz m₀) : Commute _ _).eq
  have h8 := tight_pow_eight E hidx hK h2 hR hM hz hx'z hx'j
  apply hxa m₀ hm₀
  rw [map_pow, map_pow, ← pow_mul] at h8
  rw [← h8]
  ring_nf

theorem modelPiL2_proved :
    ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup ↥(genFittingFStar X) →
      (genFittingFStar X).index ≤ 2 → ∀ p f : ℕ, p.Prime → p ≠ 2 → Even f → p ^ f % 16 = 9 →
        LieModel (FStarQuot X) .PSL 2 p f →
        ∀ (P : Subgroup X) (e : ↥P ≃* QuaternionGroup 2) (β : MulAut X), (∀ x ∈ P, β x ∈ P) →
          (∃ k : ℕ, β ^ 2 ^ k = 1) →
            β ^ 8 = 1 ∧ (β ^ 4 = 1 →
              β ^ 2 = 1 ∨ β ^ 2 = MulAut.conj ((e.symm (QuaternionGroup.a 2) : ↥P) : X)) := by
  intro X _ _ hs _ p f hp hp2 hf h9 hl P e β hβP hβ2
  obtain ⟨F, _, _, hF, -, h4, ⟨E⟩⟩ := exists_pgamEmb hs hp2 hl
  obtain ⟨hK, h2⟩ := field_facts hp hp2 hF h4
  have : Fact p.Prime := ⟨hp⟩
  have hf4 := mod_four_of_pow_mod_sixteen (hp.odd_of_ne_two hp2) hf h9
  let ρ' : QuaternionGroup 2 →* GorensteinWalter.PGammaL2 F :=
    E.ρ.comp (MulAut.conj.comp (P.subtype.comp e.symm.toMonoidHom))
  have hρ' : Function.Injective ρ' :=
    E.inj.comp (E.conjInj.comp (Subtype.val_injective.comp e.symm.injective))
  obtain ⟨k, hk⟩ := hβ2
  have hbk : E.ρ β ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have hbr : (E.ρ β).right * (E.ρ β).right = 1 := by
    rw [← sq]
    refine sq_eq_one_of_pow_two_pow (k := k) hf4 (ringEquiv_pow_eq_one hF _) ?_
    rw [← right_pow, hbk]
    rfl
  have hb : ∀ g, ∃ h, E.ρ β * ρ' g * (E.ρ β)⁻¹ = ρ' h := by
    intro g
    refine ⟨e ⟨β (e.symm g), hβP _ (e.symm g).2⟩, ?_⟩
    simp only [ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype]
    rw [← map_inv, ← map_mul, ← map_mul, mulAut_mul_conj_mul_inv]
  obtain ⟨h8, h4'⟩ := pi_facts hK h2 ρ' hρ' hbr hbk hb
  refine ⟨E.inj (by rw [map_pow, h8, map_one]), fun hβ4 => ?_⟩
  rcases h4' (by rw [← map_pow, hβ4, map_one]) with h | h
  · exact Or.inl (E.inj (by rw [map_pow, h, map_one]))
  · exact Or.inr (E.inj (by rw [map_pow, h]; rfl))

theorem modelOutL2_proved :
    ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup ↥(genFittingFStar X) →
      (genFittingFStar X).index ≤ 2 → ∀ p f : ℕ, p.Prime → p ≠ 2 → Even f → p ^ f % 16 = 9 →
        LieModel (FStarQuot X) .PSL 2 p f → ∀ P : Subgroup X, Nonempty (↥P ≃* QuaternionGroup 2) →
          (∀ α β : MulAut X, ∃ w : X, α * β * α⁻¹ * β⁻¹ = MulAut.conj w) ∧
          ∀ α β : MulAut X, (∃ k : ℕ, α ^ 2 ^ k = 1) → (∃ k : ℕ, β ^ 2 ^ k = 1) →
            (¬ ∃ w : X, α = MulAut.conj w) → (¬ ∃ w : X, β = MulAut.conj w) →
              ∃ w : X, α * β⁻¹ = MulAut.conj w := by
  intro X _ _ hs hidx p f hp hp2 hf h9 hl P ⟨e⟩
  obtain ⟨F, _, _, hF, -, h4, ⟨E⟩⟩ := exists_pgamEmb hs hp2 hl
  obtain ⟨hK, h2⟩ := field_facts hp hp2 hF h4
  have : Fact p.Prime := ⟨hp⟩
  have hf4 := mod_four_of_pow_mod_sixteen (hp.odd_of_ne_two hp2) hf h9
  refine ⟨fun α β => ?_, fun α β hα hβ hαo hβo => ?_⟩
  · obtain ⟨g, hg⟩ := pgammaL2_commutator_mem hK (E.ρ α) (E.ρ β)
    obtain ⟨n, -, hn⟩ := E.onto g
    refine ⟨n, E.inj ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg, hn]
  · let Xt : Subgroup (GorensteinWalter.PGammaL2 F) := (E.ρ.comp MulAut.conj).range
    have hS : ∀ s ∈ pslRange F, SemidirectProduct.inl s ∈ Xt := by
      rintro _ ⟨g, rfl⟩
      obtain ⟨n, -, hn⟩ := E.onto g
      exact ⟨n, hn⟩
    have hnorm : ∀ γ : MulAut X, ∀ x ∈ Xt, E.ρ γ * x * (E.ρ γ)⁻¹ ∈ Xt := by
      rintro γ _ ⟨w, rfl⟩
      refine ⟨γ w, ?_⟩
      simp only [MonoidHom.comp_apply]
      rw [← mulAut_mul_conj_mul_inv, map_mul, map_mul, map_inv]
    let ρ' : QuaternionGroup 2 →* GorensteinWalter.PGammaL2 F :=
      E.ρ.comp (MulAut.conj.comp (P.subtype.comp e.symm.toMonoidHom))
    have hρ' : Function.Injective ρ' :=
      E.inj.comp (E.conjInj.comp (Subtype.val_injective.comp e.symm.injective))
    obtain ⟨c₀, hc₀, -, hcpgl⟩ := exists_pgl_quat hK h2 ρ' hρ'
    obtain ⟨y₀, hy₀⟩ := q8_exists_inverter c₀ hc₀
    have hx₀ : ρ' y₀ ∈ Xt := ⟨((e.symm y₀ : ↥P) : X), rfl⟩
    have hx₀r : (ρ' y₀).right ≠ 1 := fun h =>
      q8_inverter_outside c₀ y₀ hc₀ hy₀ (hcpgl y₀ h)
    have hx₀r2 : (ρ' y₀).right * (ρ' y₀).right = 1 := E.right_sq hidx _
    have hright : ∀ γ : MulAut X, (∃ k : ℕ, γ ^ 2 ^ k = 1) →
        (E.ρ γ).right * (E.ρ γ).right = 1 := by
      rintro γ ⟨k, hk⟩
      rw [← sq]
      refine sq_eq_one_of_pow_two_pow (k := k) hf4 (ringEquiv_pow_eq_one hF _) ?_
      rw [← right_pow, ← map_pow, hk, map_one]
      rfl
    have hout : ∀ γ : MulAut X, (¬ ∃ w : X, γ = MulAut.conj w) → E.ρ γ ∉ Xt := by
      rintro γ hγ ⟨w, hw⟩
      exact hγ ⟨w, E.inj hw.symm⟩
    obtain ⟨w, hw⟩ := mul_inv_mem_of_not_mem hK Xt hS hx₀ hx₀r hx₀r2 (hout α hαo) (hout β hβo)
      (hright α hα) (hright β hβ) (hnorm α _ hx₀) (hnorm β _ hx₀)
    refine ⟨w, E.inj ?_⟩
    rw [map_mul, map_inv]
    exact hw.symm

theorem modelL33NotSectionL2_proved :
    ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup ↥(genFittingFStar X) →
      (genFittingFStar X).index ≤ 2 → ∀ p f : ℕ, p.Prime → p ≠ 2 → Even f →
        LieModel (FStarQuot X) .PSL 2 p f →
        ∀ (A : Subgroup X) (B : Subgroup ↥A) (_ : B.Normal), ¬ LieModel (↥A ⧸ B) .PSL 3 3 1 := by
  intro X _ _ hs hidx p f hp hp2 _ hl A B hB hL
  obtain ⟨F, _, _, hF, -, -, -, ⟨ψ⟩⟩ := exists_psl2_setup hs hp2 hl
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have := isSimpleGroup_of_lieModel_L33 hL
  have hcard : Nat.card (↥A ⧸ B) = 5616 := by
    obtain ⟨e⟩ := psl3_three_of_lieModel hL
    rw [Nat.card_congr e.toEquiv, card_psl3_three]
  set N := genFittingFStar X with hNdef
  have hNn : N.Normal := CFSG.ClassicalInvolution.genFittingFStar_normal X
  let K : Subgroup ↥N := A.subgroupOf N
  let ι : ↥K →* ↥A :=
    { toFun := fun k => ⟨((k : ↥N) : X), k.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let π' : ↥K →* ↥A ⧸ B := (QuotientGroup.mk' B).comp ι
  have hsurj : Function.Surjective π' := by
    have hRn : ((N.subgroupOf A).map (QuotientGroup.mk' B)).Normal :=
      (hNn.subgroupOf A).map _ (QuotientGroup.mk'_surjective B)
    have hRle : (N.subgroupOf A).map (QuotientGroup.mk' B) ≤ π'.range := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨⟨⟨(a : X), ha⟩, a.2⟩, rfl⟩
    have := hRn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf A).map (QuotientGroup.mk' B))
      with h | h
    · exfalso
      have hle : N.subgroupOf A ≤ B := by
        intro a ha
        have : QuotientGroup.mk' B a = 1 := by
          have hm : QuotientGroup.mk' B a ∈ (N.subgroupOf A).map (QuotientGroup.mk' B) :=
            ⟨a, ha, rfl⟩
          rwa [h, Subgroup.mem_bot] at hm
        exact (QuotientGroup.eq_one_iff a).mp this
      have h1 : B.index ∣ (N.subgroupOf A).index := Subgroup.index_dvd_of_le hle
      have h2 : (N.subgroupOf A).index ∣ N.index := Subgroup.relIndex_dvd_index_of_normal N A
      have h3 : B.index = 5616 := by rw [Subgroup.index_eq_card, hcard]
      have h4 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h4) (h1.trans h2)
      omega
    · intro q
      have hq : q ∈ π'.range := hRle (h ▸ Subgroup.mem_top q)
      obtain ⟨k, hk⟩ := hq
      exact ⟨k, hk⟩
  let H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := K.map ψ.toMonoidHom
  let eH : ↥K ≃* ↥H := K.equivMapOfInjective ψ.toMonoidHom ψ.injective
  exact psl2_not_onto_5616 hpodd hF hcard H (π'.comp eH.symm.toMonoidHom)
    (hsurj.comp eH.symm.surjective)

theorem modelCardL33_proved : ∀ (M : Type) [Group M], LieModel M .PSL 3 3 1 → Nat.card M = 5616 := by
  intro M _ hM
  obtain ⟨e⟩ := psl3_three_of_lieModel hM
  rw [Nat.card_congr e.toEquiv, card_psl3_three]

@[expose] def GapTwinE4Sp62 : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (Φ : Set (Subgroup W)) (K K' : Subgroup W) (k k' : W)
    (σ : MulAut W), TwinSProp3 Φ K K' k k' σ →
      ∀ (Q : Type) [Group Q] (f : W →* Q), Function.Surjective f → IsPGroup 2 ↥f.ker →
        LieModel Q .PSp 3 2 1 → False

@[expose] def GapTwinE4O8p2 : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (Φ : Set (Subgroup W)) (K K' : Subgroup W) (k k' : W),
    TwinBase3 Φ K K' k k' →
      ∀ (Q : Type) [Group Q] (f : W →* Q), Function.Surjective f → IsPGroup 2 ↥f.ker →
        LieModel Q .POmegaPlus 4 2 1 →
          ∃ (P₂ : Subgroup W) (L₁ L₂ L₃ : Subgroup W), IsPGroup 2 ↥P₂ ∧ L₁ ∈ Φ ∧ L₂ ∈ Φ ∧
            L₃ ∈ Φ ∧ L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₂ ≠ L₃ ∧ 2 < Nat.card ↥(L₁ ⊓ P₂) ∧
              2 < Nat.card ↥(L₂ ⊓ P₂) ∧ 2 < Nat.card ↥(L₃ ⊓ P₂)

@[expose] def GapOmegaSmall : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (Φ : Set (Subgroup W)) (K K' : Subgroup W) (k k' : W)
    (σ : MulAut W), TwinSProp3 Φ K K' k k' σ →
      ∀ (N : Subgroup W) (_ : N.Normal), N = Subgroup.zpowers (k * k') →
        (LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) .PSp 2 3 1 ∨
          LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) .PSU 4 3 1 ∨
          LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) .POmegaOdd 3 3 1 ∨
          LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) .POmegaMinus 4 3 1) → False

@[expose] def GapOmegaL43 : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (Φ : Set (Subgroup W)) (K K' : Subgroup W) (k k' : W)
    (σ : MulAut W), TwinSProp3 Φ K K' k k' σ →
      ∀ (N : Subgroup W) (_ : N.Normal), N = Subgroup.zpowers (k * k') →
        LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) .PSL 4 3 1 →
          ∃ (B : Subgroup ↥(fixSylGen Φ σ)) (_ : B.Normal),
            LieModel (↥(fixSylGen Φ σ) ⧸ B) .PSL 3 3 1

structure Z2GapFacts : Prop where
  sp62 : GapTwinE4Sp62
  o8p2 : GapTwinE4O8p2
  small : GapOmegaSmall
  orth : OrthThreeCommutingFacts
  l43 : GapOmegaL43

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
