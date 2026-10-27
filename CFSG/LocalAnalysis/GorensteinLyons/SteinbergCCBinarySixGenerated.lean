module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixMaximalElementaryRadicals
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBMFrattiniGeneratorBound
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup Module Matrix
open scoped commutatorElement Pointwise
open LinearMap (BilinForm)

namespace BinarySixGenerators

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix CFSG.LargeEvenClassification.Helpers

theorem le_of_two_pow_le {k m : ℕ} (h : 2 ^ k ≤ 2 ^ m) : k ≤ m :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem lt_of_two_pow_lt {k m : ℕ} (h : 2 ^ k < 2 ^ m) : k < m :=
  (Nat.pow_lt_pow_iff_right (by norm_num)).mp h

theorem card_frattini_quotient_le_four {X : Type*} [Group X] [Finite X] (hX : IsPGroup 2 X)
    (ι : X →* GL (Fin 3) (ZMod 2)) (hι : Function.Injective ι)
    (hU : ι.range ≤ unitriangularGL 3 (ZMod 2)) : Nat.card (X ⧸ frattini X) ≤ 4 := by
  have hXA : Nat.card X = Nat.card ι.range := (Nat.card_range_of_injective hι).symm
  have hX8 : Nat.card X ≤ 8 := by
    rw [hXA]
    exact (Subgroup.card_le_of_le hU).trans card_unitriangularGL_le
  have hidx : Nat.card (X ⧸ frattini X) ≤ Nat.card X :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card (frattini X))
  by_cases h4 : Nat.card X ≤ 4
  · exact hidx.trans h4
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hX
    have hk3 : k = 3 := by
      rw [hk] at hX8 h4
      have h1 : k ≤ 3 := le_of_two_pow_le (m := 3) (by simpa using hX8)
      have h2 : 2 < k := lt_of_two_pow_lt (k := 2) (by simpa using (not_le.mp h4))
      omega
    have hrange : ι.range = unitriangularGL 3 (ZMod 2) :=
      Subgroup.eq_of_le_of_card_ge hU (by rw [← hXA, hk, hk3]; exact card_unitriangularGL_le)
    have hnc : ∃ a b : X, a * b ≠ b * a := by
      by_contra h
      push Not at h
      apply not_commute_unitriangularGL
      intro x hx y hy
      rw [← hrange] at hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      rw [← map_mul, ← map_mul, h a b]
    obtain ⟨a, b, hab⟩ := hnc
    have : Fact (IsPGroup 2 X) := ⟨hX⟩
    have hΦ : frattini X ≠ ⊥ := by
      intro hbot
      have hc : ⁅a, b⁆ ∈ frattini X :=
        CFSG.commutator_le_frattini_of_isPGroup (p := 2)
          (Subgroup.commutator_mem_commutator (mem_top a) (mem_top b))
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hab hc
    have h2 : 2 ≤ Nat.card (frattini X) := by
      have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hΦ
      omega
    have hmul : Nat.card (frattini X) * (frattini X).index = 8 := by
      rw [(frattini X).card_mul_index, hk, hk3]
      norm_num
    have h8 : 2 * (frattini X).index ≤ 8 := by
      rw [← hmul]
      exact Nat.mul_le_mul_right _ h2
    show (frattini X).index ≤ 4
    omega

theorem core {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (ι : G →* StatedSp 3 (ZMod 2)) (hι : Function.Injective ι)
    (hU : ι.range ≤ unipotent 3 (ZMod 2)) :
    ∃ d : ℕ, Nat.card (G ⧸ frattini G) = 2 ^ d ∧ d ≤ 6 ∧
      ∃ S : Finset G, S.card ≤ 6 ∧ closure (S : Set G) = ⊤ := by
  classical
  have hstab : ∀ g : G, ι g ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3) := fun g =>
    unipotent_le_stabilizer (hU ⟨g, rfl⟩)
  let f : G →* GL (Fin 3) (ZMod 2) := (lagrangianLevi 3).comp (ι.codRestrict _ hstab)
  have hfapp : ∀ g : G, f g = lagrangianLevi 3 ⟨ι g, hstab g⟩ := fun g => rfl
  have hK : ∀ x : G, x ∈ f.ker ↔ ι x ∈ (tauSym 3).range := by
    intro x
    rw [MonoidHom.mem_ker, hfapp, ← MonoidHom.mem_ker, ker_lagrangianLevi,
      Subgroup.mem_subgroupOf]
  have hfU : ∀ g : G, f g ∈ unitriangularGL 3 (ZMod 2) := fun g =>
    lagrangianLevi_mem_unitriangularGL (hU ⟨g, rfl⟩)
  have hKcomm : ∀ x ∈ f.ker, ∀ y ∈ f.ker, x * y = y * x := by
    intro x hx y hy
    obtain ⟨B, hB⟩ := (hK x).mp hx
    obtain ⟨C, hC⟩ := (hK y).mp hy
    apply hι
    rw [map_mul, map_mul, ← hB, ← hC, ← map_mul, ← map_mul, mul_comm]
  have hK64 : Nat.card f.ker ≤ 64 := by
    let j : f.ker →* (tauSym 3).range :=
      (ι.comp f.ker.subtype).codRestrict _ fun x => (hK x).mp x.2
    have hj : Function.Injective j := fun x y h =>
      Subtype.ext (hι (congrArg Subtype.val h))
    have := Nat.card_le_card_of_injective j hj
    rwa [card_range_tauSym 3] at this
  obtain ⟨-, -, hDN, -, dP, dQ, dN, hdP, hdQ, hdN, hle, S, hS, hSc⟩ :=
    p_group_Frattini_coinvariant_generator_bound hG f.ker rfl
  set D : Subgroup G := (frattini f.ker).map f.ker.subtype ⊔ ⁅f.ker, ⊤⁆ with hDdef
  have hquot : Nat.card (f.ker ⧸ D.subgroupOf f.ker) ≤ Nat.card f.ker :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
  have hdQ2 : dQ ≤ 2 := by
    have hι' : Function.Injective (QuotientGroup.kerLift f) := QuotientGroup.kerLift_injective f
    have hrange : (QuotientGroup.kerLift f).range ≤ unitriangularGL 3 (ZMod 2) := by
      rintro _ ⟨x, rfl⟩
      induction x using QuotientGroup.induction_on with
      | H g => exact hfU g
    have h4 := card_frattini_quotient_le_four (hG.to_quotient _) _ hι' hrange
    rw [hdQ] at h4
    exact le_of_two_pow_le (m := 2) (by simpa using h4)
  by_cases htriv : ∀ g : G, g ∈ f.ker
  ·
    have htop : f.ker = ⊤ := eq_top_iff.mpr fun g _ => htriv g
    have hdQ0 : dQ = 0 := by
      have h1 : Nat.card (G ⧸ f.ker) = 1 := by
        rw [← Subgroup.index, htop, Subgroup.index_top]
      have h2 : Nat.card ((G ⧸ f.ker) ⧸ frattini (G ⧸ f.ker)) ≤ Nat.card (G ⧸ f.ker) :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
      rw [hdQ, h1] at h2
      by_contra h0
      have := Nat.one_lt_two_pow h0
      omega
    have hdN6 : dN ≤ 6 := by
      have h1 := hquot.trans hK64
      rw [hdN] at h1
      exact le_of_two_pow_le (m := 6) (by simpa using h1)
    exact ⟨dP, hdP, by omega, S, by omega, hSc⟩
  ·
    push Not at htriv
    obtain ⟨a, ha⟩ := htriv
    have hfa : f a ≠ 1 := fun h => ha (MonoidHom.mem_ker.mpr h)
    have hmem : ∀ k : f.ker, ⁅(k : G), a⁆ ∈ f.ker := by
      intro k
      rw [commutatorElement_def]
      have h1 : a * (k : G)⁻¹ * a⁻¹ ∈ f.ker :=
        (MonoidHom.normal_ker f).conj_mem _ (f.ker.inv_mem k.2) a
      have := f.ker.mul_mem k.2 h1
      simpa only [mul_assoc] using this
    let φ : f.ker →* f.ker := MonoidHom.mk' (fun k => ⟨⁅(k : G), a⁆, hmem k⟩) (by
      intro k l
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have hl := hmem l
      have hk := hmem k
      have h1 : (k : G) * ⁅(l : G), a⁆ * (k : G)⁻¹ = ⁅(l : G), a⁆ := by
        rw [hKcomm _ k.2 _ hl, mul_inv_cancel_right]
      calc ⁅(k : G) * l, a⁆ = ((k : G) * ⁅(l : G), a⁆ * (k : G)⁻¹) * ⁅(k : G), a⁆ := by
            simp only [commutatorElement_def]
            group
        _ = ⁅(l : G), a⁆ * ⁅(k : G), a⁆ := by rw [h1]
        _ = ⁅(k : G), a⁆ * ⁅(l : G), a⁆ := hKcomm _ hl _ hk)
    have hφD : φ.range ≤ D.subgroupOf f.ker := by
      rintro _ ⟨k, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact mem_sup_right (Subgroup.commutator_mem_commutator k.2 (mem_top a))
    have hidx : Nat.card (f.ker ⧸ D.subgroupOf f.ker) ≤ Nat.card φ.ker := by
      have h1 : (D.subgroupOf f.ker).index ≤ φ.range.index :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
          (Subgroup.index_dvd_of_le hφD)
      have h2 : Nat.card φ.ker * Nat.card φ.range = Nat.card f.ker := by
        rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm,
          ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
      have h3 : Nat.card φ.range * φ.range.index = Nat.card f.ker := φ.range.card_mul_index
      have h4 : φ.range.index = Nat.card φ.ker := by
        have hpos : 0 < Nat.card φ.range := Nat.card_pos
        rw [← h2, mul_comm] at h3
        exact Nat.eq_of_mul_eq_mul_right hpos h3
      calc Nat.card (f.ker ⧸ D.subgroupOf f.ker) = (D.subgroupOf f.ker).index := rfl
        _ ≤ φ.range.index := h1
        _ = Nat.card φ.ker := h4
    have hC16 : Nat.card φ.ker ≤ 16 := by
      let A : Matrix (Fin 3) (Fin 3) (ZMod 2) := (f a : Matrix (Fin 3) (Fin 3) (ZMod 2))
      have hAU : IsUnitriangular A := hfU a
      have hA1 : A ≠ 1 := fun h => hfa (Units.ext h)
      have hcoord : ∀ k : φ.ker, ∃ B : Multiplicative (binarySymMatrices 3),
          ι ((k : f.ker) : G) = tauSym 3 B := by
        intro k
        obtain ⟨B, hB⟩ := (hK _).mp (k : f.ker).2
        exact ⟨B, hB.symm⟩
      choose B hB using hcoord
      have hfix : ∀ k : φ.ker, A * ((B k).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Aᵀ =
          ((B k).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
        intro k
        have hk1 : ⁅((k : f.ker) : G), a⁆ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp k.2)
        have hcomm : ι a * ι ((k : f.ker) : G) * (ι a)⁻¹ = ι ((k : f.ker) : G) := by
          rw [commutatorElement_eq_one_iff_mul_comm] at hk1
          rw [← map_mul, ← hk1, map_mul, mul_inv_cancel_right]
        have h1 := conj_tauSym_of_mem_stabilizer (hstab a) (B k)
        rw [← hB k, hcomm, hB k] at h1
        have h2 := congrArg (fun C : Multiplicative (binarySymMatrices 3) =>
          ((Multiplicative.toAdd C : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)))
          (tauSym_injective h1)
        simp only [toAdd_ofAdd] at h2
        exact h2.symm
      let T : Finset SixBits := Finset.univ.filter fun x : SixBits =>
        A * symMat x * Aᵀ = symMat x
      have hmemT : ∀ k : φ.ker, symCoord ((B k).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ T := by
        intro k
        rw [Finset.mem_filter, symMat_symCoord (binarySym_transpose _)]
        exact ⟨Finset.mem_univ _, hfix k⟩
      have hinj : Function.Injective fun k : φ.ker => (⟨_, hmemT k⟩ : T) := by
        intro k l h
        have h1 := congrArg (fun x : T => symMat x.1) h
        simp only [symMat_symCoord (binarySym_transpose _)] at h1
        have h2 : B k = B l := Multiplicative.toAdd.injective (Subtype.ext h1)
        apply Subtype.ext
        apply Subtype.ext
        apply hι
        rw [hB k, hB l, h2]
      calc Nat.card φ.ker ≤ Nat.card T := Nat.card_le_card_of_injective _ hinj
        _ = T.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        _ ≤ 16 := card_fixed_le_sixteen hAU hA1
    have hdN4 : dN ≤ 4 := by
      have h1 := hidx.trans hC16
      rw [hdN] at h1
      exact le_of_two_pow_le (m := 4) (by simpa using h1)
    exact ⟨dP, hdP, by omega, S, by omega, hSc⟩

end BinarySixGenerators

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix CFSG.LargeEvenClassification.Helpers
  BinarySixGenerators in
theorem binary_symplectic_six_subgroup_six_generated {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (hV : finrank (ZMod 2) V = 6)
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (P : Subgroup (bilinIsometryGroup b)) (hP : IsPGroup 2 P) :
    pGeneratorRank 2 P ≤ 6 ∧ (∃ S : Finset P, S.card ≤ 6 ∧ closure (S : Set P) = ⊤) ∧
      ∀ (L : Subgroup P) [L.Normal], IsElementaryAbelian 2 (P ⧸ L) →
        Nat.card (P ⧸ L) ≤ 2 ^ 6 := by
  classical
  obtain ⟨e, he⟩ := exists_isSymplecticBasis hb hnd (n := 3) (by rw [hV])
  have : Finite (bilinIsometryGroup b) := finite_bilinIsometryGroup he
  let ι₀ : P →* StatedSp 3 (ZMod 2) := (spCoord he).toMonoidHom.comp P.subtype
  have hι₀ : Function.Injective ι₀ := (spCoord he).injective.comp P.subtype_injective
  have hA : IsPGroup 2 ι₀.range := hP.of_surjective ι₀.rangeRestrict ι₀.rangeRestrict_surjective
  obtain ⟨Syl, hSyl⟩ := hA.exists_le_sylow
  obtain ⟨U, hU⟩ := exists_sylow_unipotent (K := ZMod 2) 2 3
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq (StatedSp 3 (ZMod 2)) U Syl
  let ι : P →* StatedSp 3 (ZMod 2) := (MulAut.conj s⁻¹).toMonoidHom.comp ι₀
  have hι : Function.Injective ι := (MulAut.conj s⁻¹).injective.comp hι₀
  have hιU : ι.range ≤ unipotent 3 (ZMod 2) := by
    rintro _ ⟨x, rfl⟩
    have h1 : ι₀ x ∈ (Syl : Subgroup (StatedSp 3 (ZMod 2))) := hSyl ⟨x, rfl⟩
    have h2 : MulAut.conj s • (U : Subgroup (StatedSp 3 (ZMod 2))) =
        (Syl : Subgroup (StatedSp 3 (ZMod 2))) :=
      congrArg (fun Q : Sylow 2 (StatedSp 3 (ZMod 2)) => (Q : Subgroup (StatedSp 3 (ZMod 2)))) hs
    rw [← h2, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hU, MulAut.smul_def,
      MulAut.conj_inv_apply] at h1
    have hx : ι x = s⁻¹ * ι₀ x * s := by
      simp only [ι, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
    rw [hx]
    exact h1
  obtain ⟨d, hd, hd6, S, hS, hSc⟩ := core hP ι hι hιU
  have hdP : pGeneratorRank 2 P = d := by
    rw [pGeneratorRank, hd, Nat.log_pow (by norm_num)]
  refine ⟨hdP ▸ hd6, ⟨S, hS, hSc⟩, fun L _ hEA => ?_⟩
  have hle : frattini P ≤ L := CFSG.SectionRank.Ccomm.frattini_le_of_quotient_elementary (p := 2)
    L (fun a b => hEA.is_comm.comm a b)
    (fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hEA.exponent_dvd_p a)
  have h1 : L.index ∣ (frattini P).index := Subgroup.index_dvd_of_le hle
  have h2 : (frattini P).index = 2 ^ d := hd
  calc Nat.card (P ⧸ L) = L.index := rfl
    _ ≤ (frattini P).index := Nat.le_of_dvd (by rw [h2]; positivity) h1
    _ = 2 ^ d := h2
    _ ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hd6

end CFSG.LocalAnalysis.GorensteinLyons
