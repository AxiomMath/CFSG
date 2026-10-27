module

public import CFSG.Quasithin.Background.C1GNDefs
import CFSG.Quasithin.Background.C126NatFstarAux
import CFSG.Quasithin.Background.C1PackNat
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieSub
import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35K6bA
public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement Matrix

variable {Ω : Type} [Group Ω]

@[expose] def gomiV (G : Subgroup Ω) : Subgroup Ω := omegaOneCenterOf (pCoreOf 2 G)

structure IsGomiQ (S G : Subgroup Ω) : Prop where
  sylow : IsSylowTwoOf S G
  charTwo : CharTwo G
  natural : ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ m ∧
    ∃ α : G →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective α ∧
      α.ker = (Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf G ∧
    ∃ β : ↥(⁅gomiV G, G⁆ : Subgroup Ω) →* Multiplicative (Fin 2 → F), Function.Surjective β ∧
      β.ker = (⁅gomiV G, G⁆ ⊓ Subgroup.centralizer (G : Set Ω)).subgroupOf ⁅gomiV G, G⁆ ∧
      ∀ (g : G) (u v : ↥(⁅gomiV G, G⁆ : Subgroup Ω)), (v : Ω) = g * u * g⁻¹ →
        Multiplicative.toAdd (β v) =
          (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))
  sylowCent : IsSylowTwoOf (pCoreOf 2 G) (G ⊓ Subgroup.centralizer (gomiV G : Set Ω))
  not_commutator_le : ¬ ⁅pCoreOf 2 G, twoResidual G⁆ ≤ gomiV G
  uniqueMax : ∃ M : Subgroup Ω, IsUniqueMaxOver G S M
  le_conjClosure_baum : G ≤ conjClosure (baum S) G

@[expose] def IsGomiCharPair (S S₁ S₂ : Subgroup Ω) : Prop :=
  S₁ ≤ S ∧ (S₁.subgroupOf S).Characteristic ∧ S₂ ≤ S ∧ (S₂.subgroupOf S).Characteristic ∧
    ∀ (Ω' : Type) [Group Ω'] [Finite Ω'] (G : Subgroup Ω') (ι : ↥S →* Ω'),
      Function.Injective ι → IsGomiQ ι.range G →
        G ≤ Subgroup.normalizer (((S₁.subgroupOf S).map ι : Subgroup Ω') : Set Ω') ∨
        G ≤ Subgroup.normalizer (((S₂.subgroupOf S).map ι : Subgroup Ω') : Set Ω')

@[expose] def IsGomiCharPairGN (S S₁ S₂ : Subgroup Ω) : Prop :=
  IsGomiCharPair S S₁ S₂ ∧ S₁ ≠ ⊥ ∧ S₂ ≠ ⊥ ∧ S₁ ≤ omegaOneCenterOf S

theorem IsGomiCharPairGN.map_mulEquiv {S S₁ S₂ : Subgroup Ω} (h : IsGomiCharPairGN S S₁ S₂)
    (φ : Ω ≃* Ω) :
    IsGomiCharPairGN (S.map φ.toMonoidHom) (S₁.map φ.toMonoidHom) (S₂.map φ.toMonoidHom) := by
  obtain ⟨⟨hS₁, hc₁, hS₂, hc₂, hall⟩, h₁, h₂, hZ⟩ := h
  let ψ : ↥S ≃* ↥(S.map φ.toMonoidHom) := S.equivMapOfInjective φ.toMonoidHom φ.injective
  have hψ : ∀ X : Subgroup Ω, (X.subgroupOf S).map ψ.toMonoidHom =
      (X.map φ.toMonoidHom).subgroupOf (S.map φ.toMonoidHom) := by
    intro X
    ext y
    obtain ⟨x, rfl⟩ := ψ.surjective y
    refine (Subgroup.mem_map_iff_mem (f := ψ.toMonoidHom) ψ.injective).trans ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective).symm
  have hchar : ∀ X : Subgroup Ω, (X.subgroupOf S).Characteristic →
      ((X.map φ.toMonoidHom).subgroupOf (S.map φ.toMonoidHom)).Characteristic := by
    intro X hX
    rw [← hψ]
    refine Subgroup.characteristic_iff_map_eq.mpr fun σ => ?_
    have h := Subgroup.characteristic_iff_map_eq.mp hX ((ψ.trans σ).trans ψ.symm)
    rw [Subgroup.map_map]
    calc (X.subgroupOf S).map (σ.toMonoidHom.comp ψ.toMonoidHom)
        = ((X.subgroupOf S).map ((ψ.trans σ).trans ψ.symm).toMonoidHom).map ψ.toMonoidHom := by
          rw [Subgroup.map_map]
          congr 1
          refine MonoidHom.ext fun x => ?_
          show σ (ψ x) = ψ (ψ.symm (σ (ψ x)))
          exact (ψ.apply_symm_apply _).symm
      _ = (X.subgroupOf S).map ψ.toMonoidHom := by rw [h]
  refine ⟨⟨Subgroup.map_mono hS₁, hchar S₁ hc₁, Subgroup.map_mono hS₂, hchar S₂ hc₂, ?_⟩,
    fun h0 => h₁ ((Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h0),
    fun h0 => h₂ ((Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h0),
    (Subgroup.map_mono hZ).trans (omegaOneCenterOf_map_mulEquiv φ S).le⟩
  intro Ω' _ _ G ι hι hQ
  have hrange : (ι.comp ψ.toMonoidHom).range = ι.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.surjective, ← MonoidHom.range_eq_map]
  have hmap : ∀ X : Subgroup Ω, (X.subgroupOf S).map (ι.comp ψ.toMonoidHom) =
      ((X.map φ.toMonoidHom).subgroupOf (S.map φ.toMonoidHom)).map ι := fun X => by
    rw [← hψ, Subgroup.map_map]
  rcases hall Ω' G (ι.comp ψ.toMonoidHom) (hι.comp ψ.injective) (hrange ▸ hQ) with h1 | h2
  · exact Or.inl (hmap S₁ ▸ h1)
  · exact Or.inr (hmap S₂ ▸ h2)

private theorem charPair_le_normalizer_commutator {H₁ H₂ K : Subgroup Ω}
    (h₁ : K ≤ Subgroup.normalizer (H₁ : Set Ω)) (h₂ : K ≤ Subgroup.normalizer (H₂ : Set Ω)) :
    K ≤ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup Ω) : Set Ω) := by
  have key : ∀ g ∈ K, ∀ x ∈ ⁅H₁, H₂⁆, g * x * g⁻¹ ∈ ⁅H₁, H₂⁆ := by
    intro g hg x hx
    have : (⁅H₁, H₂⁆).map (MulAut.conj g).toMonoidHom ≤ ⁅H₁, H₂⁆ := by
      rw [Subgroup.map_commutator]
      apply Subgroup.commutator_mono
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 (h₁ hg) y).1 hy
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 (h₂ hg) y).1 hy
    exact this ⟨x, hx, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (K.inv_mem hg) _ hx
  simpa [mul_assoc] using this

section Parabolic

variable [Finite Ω]

private theorem charPair_sl2_mem_of_sq {F : Type} [Field F] [Fintype F]
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [A.Normal] (hodd : ¬ 2 ∣ A.index)
    {x : Matrix.SpecialLinearGroup (Fin 2) F} (hx : x ^ 2 = 1) : x ∈ A := by
  have h1 : orderOf (QuotientGroup.mk x : Matrix.SpecialLinearGroup (Fin 2) F ⧸ A) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one])
  have h2 : orderOf (QuotientGroup.mk x : Matrix.SpecialLinearGroup (Fin 2) F ⧸ A) ∣ A.index :=
    orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h
    exact h
  · rw [h] at h2
    exact absurd h2 hodd

private theorem charPair_sl2_no_normal_sylow {F : Type} [Field F] [Fintype F] [CharP F 2]
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [A.Normal] (hA2 : IsPGroup 2 A)
    (hodd : ¬ 2 ∣ A.index) : False := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  let u : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let l : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hu : u ^ 2 = 1 := by
    apply Subtype.ext
    show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) ^ 2 = 1
    rw [sq, Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [h11]
  have hl : l ^ 2 = 1 := by
    apply Subtype.ext
    show (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) ^ 2 = 1
    rw [sq, Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [h11]
  have hm : ((u * l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; 1, 1] := by
    show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 1, 1] = _
    rw [Matrix.mul_fin_two]
    simp [h11]
  have hw3 : (u * l) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hm, pow_three, Matrix.mul_fin_two,
      Matrix.mul_fin_two, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
    simp [h11]
  have hw1 : u * l ≠ 1 := by
    intro h
    rw [h, Matrix.SpecialLinearGroup.coe_one] at hm
    have := congrFun (congrFun hm 0) 0
    simp at this
  have hw : u * l ∈ A :=
    A.mul_mem (charPair_sl2_mem_of_sq A hodd hu) (charPair_sl2_mem_of_sq A hodd hl)
  obtain ⟨k, hk⟩ := hA2 ⟨u * l, hw⟩
  have hk' : (u * l) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hord : orderOf (u * l) = 1 :=
    Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hw3)
      (orderOf_dvd_of_pow_eq_one hk'))
  exact hw1 (orderOf_eq_one_iff.mp hord)

omit [Finite Ω] in
private theorem IsGomiQ.not_le_normalizer {S G : Subgroup Ω} (h : IsGomiQ S G) :
    ¬ G ≤ Subgroup.normalizer (S : Set Ω) := by
  intro hGS
  obtain ⟨m, F, iF, iFt, hF, α, hαs, -, -⟩ := h.natural
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hSn : (S.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.sylow.1).mpr hGS
  have : ((S.subgroupOf G).map α).Normal := hSn.map α hαs
  exact charPair_sl2_no_normal_sylow ((S.subgroupOf G).map α)
    (h.sylow.2.1.comap_subtype.map α)
    (fun h2 => h.sylow.2.2 (h2.trans (Subgroup.index_map_dvd _ hαs)))

omit [Finite Ω] in
theorem IsGomiQ.isMinParabolicOf {S G : Subgroup Ω} (h : IsGomiQ S G) :
    IsMinParabolicOf G G := by
  obtain ⟨M, hM⟩ := h.uniqueMax
  have hnn := h.not_le_normalizer
  refine ⟨S, h.sylow, ⟨le_rfl, lt_of_le_of_ne h.sylow.1 ?_, ?_⟩, hnn⟩
  · rintro rfl
    exact hnn Subgroup.le_normalizer
  · show (maxOver G S).ncard = 1
    rw [show maxOver G S = {M} from hM]
    exact Set.ncard_singleton M

end Parabolic

section Centralizer

variable [Finite Ω]

omit [Finite Ω] in
private theorem charPair_omegaOneCenterOf_le_centerOf (X : Subgroup Ω) :
    omegaOneCenterOf X ≤ centerOf X :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

omit [Finite Ω] in
private theorem charPair_le_normalizer_gomiV (G : Subgroup Ω) :
    G ≤ Subgroup.normalizer (gomiV G : Set Ω) := by
  have hGQ : G ≤ Subgroup.normalizer (pCoreOf 2 G : Set Ω) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G
  have key : ∀ g ∈ G, ∀ x ∈ gomiV G, g * x * g⁻¹ ∈ gomiV G := by
    intro g hg x hx
    have hsub : (gomiV G).map (MulAut.conj g).toMonoidHom ≤ gomiV G := by
      show (Subgroup.closure _).map _ ≤ _
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨y, ⟨⟨hyQ, hyC⟩, hy2⟩, rfl⟩
      refine ⟨⟨(Subgroup.mem_normalizer_iff.mp (hGQ hg) y).mp hyQ,
        Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩, ?_⟩
      · have hq' : g⁻¹ * q * g ∈ pCoreOf 2 G := by
          have := (Subgroup.mem_normalizer_iff.mp (hGQ (G.inv_mem hg)) q).mp hq
          simpa using this
        have hc := Subgroup.mem_centralizer_iff.mp hyC _ hq'
        show q * (g * y * g⁻¹) = g * y * g⁻¹ * q
        calc q * (g * y * g⁻¹) = g * ((g⁻¹ * q * g) * y) * g⁻¹ := by group
          _ = g * (y * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
          _ = g * y * g⁻¹ * q := by group
      · show (g * y * g⁻¹) ^ 2 = 1
        rw [conj_pow, hy2]
        group
    exact hsub ⟨x, hx, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (G.inv_mem hg) _ hx
  simpa [mul_assoc] using this

omit [Finite Ω] in
private theorem charPair_le_normalizer_vZ (S G : Subgroup Ω) :
    G ≤ Subgroup.normalizer (VZ S G : Set Ω) := by
  have key : ∀ g ∈ G, ∀ x ∈ VZ S G, g * x * g⁻¹ ∈ VZ S G := by
    intro g hg x hx
    have hsub : (VZ S G).map (MulAut.conj g).toMonoidHom ≤ VZ S G := by
      show (Subgroup.closure _).map _ ≤ _
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨y, ⟨h', hh', z, hz, rfl⟩, rfl⟩
      exact ⟨g * h', G.mul_mem hg hh', z, hz, by
        show g * h' * z * (g * h')⁻¹ = g * (h' * z * h'⁻¹) * g⁻¹
        group⟩
    exact hsub ⟨x, hx, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (G.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem IsGomiQ.omegaOneCenterOf_le_gomiV {S G : Subgroup Ω} (h : IsGomiQ S G) :
    omegaOneCenterOf S ≤ gomiV G := by
  have hQS : pCoreOf 2 G ≤ S := B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow
  apply Subgroup.closure_mono
  rintro x ⟨⟨hxS, hxC⟩, hx2⟩
  exact ⟨⟨h.charTwo ⟨h.sylow.1 hxS, Subgroup.centralizer_le hQS hxC⟩,
    Subgroup.centralizer_le hQS hxC⟩, hx2⟩

theorem IsGomiQ.vZ_le_gomiV {S G : Subgroup Ω} (h : IsGomiQ S G) : VZ S G ≤ gomiV G := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, z, hz, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (charPair_le_normalizer_gomiV G hg) z).mp
    (h.omegaOneCenterOf_le_gomiV hz)

private theorem charPair_card_eq_two {F : Type} [Field F] [Fintype F] {m : ℕ}
    (hF : Fintype.card F = 2 ^ m) (h4 : ¬ 4 ≤ Nat.card F) : Fintype.card F = 2 := by
  have h1 : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card] at h4
  rw [hF] at h1 h4 ⊢
  rcases m with _ | _ | m
  · norm_num at h1
  · rfl
  · exfalso
    apply h4
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem charPair_sl2_pow_mem {F : Type} [Field F] [Fintype F] [CharP F 2] {m : ℕ}
    (hF : Fintype.card F = 2 ^ m)
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [A.Normal] (hA : A ≠ ⊥)
    (x : Matrix.SpecialLinearGroup (Fin 2) F) : ∃ n : ℕ, x ^ 2 ^ n ∈ A := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  by_cases h4 : 4 ≤ Nat.card F
  · refine ⟨0, ?_⟩
    rw [pow_zero, pow_one]
    have hq := CFSG.Quasithin.C126.Nat.isQuasisimple_sl2 h4
    have hZ : ∀ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F), z = 1 := by
      intro z hz
      obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
      have hr2 : r ^ 2 = 1 := by simpa using hr
      have hr1 : r = 1 := by
        have h0 : (r + 1) ^ 2 = 0 := by
          rw [add_sq, hr2, h2]
          simp [CharTwo.add_self_eq_zero]
        have h0' := (pow_eq_zero_iff two_ne_zero).mp h0
        rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h0'
        exact h0'
      apply Subtype.ext
      rw [← hrz, hr1]
      simp
    have hn : (A.map (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))).Normal :=
      (inferInstance : A.Normal).map _ (QuotientGroup.mk'_surjective _)
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) := hq.2.1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (A.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))))
      with h0 | h1
    · exfalso
      apply ha1'
      apply hZ
      have hm : QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) a ∈
          A.map (QuotientGroup.mk' _) := ⟨a, haA, rfl⟩
      rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
      exact hm
    · have hm : QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) x ∈
          A.map (QuotientGroup.mk' _) := by
        rw [h1]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := hm
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
      have hyx' := hZ _ hyx
      rw [inv_mul_eq_one] at hyx'
      rw [← hyx']
      exact hy
  · have hcard2 : Fintype.card F = 2 := charPair_card_eq_two hF h4
    let e : ZMod 2 ≃+* F := ZMod.ringEquiv F hcard2
    let E : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) →* Matrix.SpecialLinearGroup (Fin 2) F :=
      Matrix.SpecialLinearGroup.map e.toRingHom
    let E' : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
      Matrix.SpecialLinearGroup.map e.symm.toRingHom
    have hEE' : ∀ y, E (E' y) = y := fun y => by
      apply Subtype.ext
      ext i j
      show e (e.symm ((y : Matrix (Fin 2) (Fin 2) F) i j)) = (y : Matrix (Fin 2) (Fin 2) F) i j
      exact e.apply_symm_apply _
    have hdec : ∀ b z : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), b ≠ 1 →
        z ^ 2 = 1 ∨ ∃ c d : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
          z = c * b * c⁻¹ * (d * b * d⁻¹) := by decide
    have hEa : E' a ≠ 1 := fun h => ha1' (by rw [← hEE' a, h, map_one])
    rcases hdec (E' a) (E' x) hEa with hx2 | ⟨c, d, hcd⟩
    · refine ⟨1, ?_⟩
      rw [pow_one, ← hEE' x, ← map_pow, hx2, map_one]
      exact A.one_mem
    · refine ⟨0, ?_⟩
      rw [pow_zero, pow_one, ← hEE' x, hcd, map_mul, map_mul, map_mul, map_mul, map_mul,
        map_inv, map_inv, hEE' a]
      exact A.mul_mem ((inferInstance : A.Normal).conj_mem _ haA _)
        ((inferInstance : A.Normal).conj_mem _ haA _)

theorem IsGomiQ.inf_centralizer_vZ_le {S G : Subgroup Ω} (h : IsGomiQ S G)
    (hZ : ¬ G ≤ Subgroup.centralizer (omegaOneCenterOf S : Set Ω)) :
    G ⊓ Subgroup.centralizer (VZ S G : Set Ω) ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
  obtain ⟨m, F, iF, iFt, hF, α, hαs, hαk, -⟩ := h.natural
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  set K := G ⊓ Subgroup.centralizer (VZ S G : Set Ω) with hKdef
  have hKG : K ≤ G := inf_le_left
  have hVV : VZ S G ≤ gomiV G := h.vZ_le_gomiV
  have hGV0 := charPair_le_normalizer_vZ S G
  have hkerK : ∀ g : G, α g = 1 → (g : Ω) ∈ K := fun g hg => by
    have h1 : g ∈ α.ker := hg
    rw [hαk, Subgroup.mem_subgroupOf] at h1
    exact ⟨g.2, Subgroup.centralizer_le hVV h1⟩
  have hKn : (K.subgroupOf G).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKG]
    intro k g hk hg
    refine ⟨G.mul_mem (G.mul_mem hg hk.1) (G.inv_mem hg),
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : g⁻¹ * v * g ∈ VZ S G := by
      have := (Subgroup.mem_normalizer_iff.mp (hGV0 (G.inv_mem hg)) v).mp hv
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hk.2 _ hv'
    calc v * (g * k * g⁻¹) = g * ((g⁻¹ * v * g) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * v * g)) * g⁻¹ := by rw [hc]
      _ = g * k * g⁻¹ * v := by group
  by_contra hne
  obtain ⟨k, hkK, hkC⟩ := SetLike.not_le_iff_exists.mp hne
  have hAne : (K.subgroupOf G).map α ≠ ⊥ := by
    intro hbot
    have hm : α ⟨k, hkK.1⟩ ∈ (K.subgroupOf G).map α := ⟨⟨k, hkK.1⟩, hkK, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hm
    have h1 : (⟨k, hkK.1⟩ : G) ∈ α.ker := hm
    rw [hαk, Subgroup.mem_subgroupOf] at h1
    exact hkC h1
  have : ((K.subgroupOf G).map α).Normal := hKn.map α hαs
  have hpow : ∀ g : G, ∃ n : ℕ, g ^ 2 ^ n ∈ K.subgroupOf G := by
    intro g
    obtain ⟨n, k', hk', hk'e⟩ := charPair_sl2_pow_mem hF _ hAne (α g)
    refine ⟨n, ?_⟩
    have hker : α (g ^ 2 ^ n * k'⁻¹) = 1 := by
      rw [map_mul, map_pow, map_inv, hk'e, mul_inv_cancel]
    have hmem : g ^ 2 ^ n * k'⁻¹ ∈ K.subgroupOf G := hkerK _ hker
    have := (K.subgroupOf G).mul_mem hmem hk'
    simpa using this
  have hSK : ∀ g ∈ G, ∃ s ∈ S, s⁻¹ * g ∈ K := by
    have hq2 : IsPGroup 2 (↥G ⧸ K.subgroupOf G) := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨n, hn⟩ := hpow g
      exact ⟨n, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hn⟩
    set π := QuotientGroup.mk' (K.subgroupOf G) with hπ
    have hidx : ((S.subgroupOf G).map π).index = 1 := by
      have h1 : ((S.subgroupOf G).map π).index ∣ (S.subgroupOf G).index :=
        Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
      obtain ⟨a, ha⟩ := hq2.exists_card_eq
      have h2 : ((S.subgroupOf G).map π).index ∣ 2 ^ a :=
        ha ▸ Subgroup.index_dvd_card _
      have hodd : ¬ 2 ∣ ((S.subgroupOf G).map π).index := fun h' => h.sylow.2.2 (h'.trans h1)
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
      rw [hb] at hodd ⊢
      rcases b with _ | b
      · rfl
      · exact absurd (dvd_pow_self 2 (Nat.succ_ne_zero b)) hodd
    have htop := Subgroup.index_eq_one.mp hidx
    intro g hg
    have hmem : π ⟨g, hg⟩ ∈ (S.subgroupOf G).map π := htop ▸ Subgroup.mem_top _
    obtain ⟨s, hs, hse⟩ := hmem
    refine ⟨(s : Ω), hs, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hse
    exact hse
  apply hZ
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨s, hs, hsg⟩ := hSK g hg
  have hzV : z ∈ VZ S G := Subgroup.subset_closure ⟨1, G.one_mem, z, hz, by group⟩
  have hk : z * (s⁻¹ * g) = (s⁻¹ * g) * z := Subgroup.mem_centralizer_iff.mp hsg.2 z hzV
  have hs' : s * z = z * s :=
    Subgroup.mem_centralizer_iff.mp (charPair_omegaOneCenterOf_le_centerOf S hz).2 s hs
  calc z * g = z * s * (s⁻¹ * g) := by group
    _ = s * (z * (s⁻¹ * g)) := by rw [← hs', mul_assoc]
    _ = s * ((s⁻¹ * g) * z) := by rw [hk]
    _ = g * z := by group

end Centralizer

section Natural

variable [Finite Ω]

private theorem charPair_exists_sl2_mulVec_eq {F : Type} [Field F] {w t : Fin 2 → F}
    (hw : w ≠ 0) (ht : t ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F, (A : Matrix (Fin 2) (Fin 2) F) *ᵥ w = t := by
  have key : ∀ v : Fin 2 → F, v ≠ 0 → ∃ B : Matrix.SpecialLinearGroup (Fin 2) F,
      (B : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = v := by
    intro v hv
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
      refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], by simp [Matrix.det_fin_two, h1]⟩, ?_⟩
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
    · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [Matrix.det_fin_two, h0]⟩, ?_⟩
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  obtain ⟨B, hB⟩ := key w hw
  obtain ⟨C, hC⟩ := key t ht
  refine ⟨C * B⁻¹, ?_⟩
  rw [← hB, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_assoc,
    inv_mul_cancel, mul_one, hC]

omit [Finite Ω] in
private theorem charPair_exists_autOn_equiv {X : Type*} [Group X] {G V : Subgroup Ω}
    (hGV : G ≤ Subgroup.normalizer (V : Set Ω)) (α : ↥G →* X) (hα : Function.Surjective α)
    (hker : α.ker = (Subgroup.centralizer (V : Set Ω)).subgroupOf G) :
    ∃ ι : ↥(autOn G V) ≃* X, ∀ (g : Ω) (hg : g ∈ G),
      ι ⟨conjAct V ⟨g, hGV hg⟩, ⟨⟨g, hGV hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩⟩ =
        α ⟨g, hg⟩ := by
  let φ : ↥G →* ↥(autOn G V) :=
    ((conjAct V).comp (Subgroup.inclusion hGV)).codRestrict (autOn G V)
      (fun g => ⟨⟨g, hGV g.2⟩, Subgroup.mem_subgroupOf.2 g.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    rintro ⟨_, ⟨n, hn, rfl⟩⟩
    exact ⟨⟨n, Subgroup.mem_subgroupOf.mp hn⟩, rfl⟩
  have hφk : φ.ker = α.ker := by
    rw [hker]
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : conjAct V ⟨g, hGV g.2⟩ = 1 := congrArg Subtype.val h1
      exact (CFSG.Quasithin.AutOn.conjAct_eq_one_iff _).mp h2
    · intro h1
      exact Subtype.ext ((CFSG.Quasithin.AutOn.conjAct_eq_one_iff ⟨(g : Ω), hGV g.2⟩).mpr h1)
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hφk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)), fun g hg => ?_⟩
  have hφg : φ ⟨g, hg⟩ =
      ⟨conjAct V ⟨g, hGV hg⟩, ⟨⟨g, hGV hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩⟩ := rfl
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm (φ ⟨g, hg⟩) =
      ((⟨g, hg⟩ : ↥G) : ↥G ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    exact (QuotientGroup.kerLift_mk φ ⟨g, hg⟩).symm
  rw [← hφg, MulEquiv.trans_apply, MulEquiv.trans_apply, h1,
    QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk α ⟨g, hg⟩

omit [Finite Ω] in
private theorem charPair_isNatL2Section_of {K C W₁ W₀ : Subgroup Ω} {n : ℕ} {F : Type}
    [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    (α : ↥K →* Matrix.SpecialLinearGroup (Fin 2) F) (hαk : α.ker = C.subgroupOf K)
    (hαr : α.range = commutator (Matrix.SpecialLinearGroup (Fin 2) F))
    (β : ↥W₁ →* Multiplicative (Fin 2 → F)) (hβs : Function.Surjective β)
    (hβk : β.ker = W₀.subgroupOf W₁)
    (hβe : ∀ (k : K) (u v : W₁), (v : Ω) = k * u * k⁻¹ →
      Multiplicative.toAdd (β v) =
        (α k : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) :
    IsNatL2Section K C W₁ W₀ n :=
  ⟨F, inferInstance, inferInstance, hF, α, hαk, hαr, β, hβs, hβk, hβe⟩

private theorem IsGomiQ.hasNaturalFstar_of_four_le {S G : Subgroup Ω} (h : IsGomiQ S G)
    (hC : G ⊓ Subgroup.centralizer (VZ S G : Set Ω) ≤ Subgroup.centralizer (gomiV G : Set Ω))
    {m : ℕ} {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ m)
    (h4 : 4 ≤ Nat.card F) (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαs : Function.Surjective α)
    (hαk : α.ker = (Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf G)
    (β : ↥(⁅gomiV G, G⁆ : Subgroup Ω) →* Multiplicative (Fin 2 → F))
    (hβk : β.ker = (⁅gomiV G, G⁆ ⊓ Subgroup.centralizer (G : Set Ω)).subgroupOf ⁅gomiV G, G⁆)
    (hβe : ∀ (g : G) (u v : ↥(⁅gomiV G, G⁆ : Subgroup Ω)), (v : Ω) = g * u * g⁻¹ →
      Multiplicative.toAdd (β v) =
        (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) :
    HasNaturalFstar G (VZ S G) := by
  have hGV0 := charPair_le_normalizer_vZ S G
  have hVV := h.vZ_le_gomiV
  have hαk0 : α.ker = (Subgroup.centralizer (VZ S G : Set Ω)).subgroupOf G := by
    rw [hαk]
    ext g
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun hg => Subgroup.centralizer_le hVV hg, fun hg => hC ⟨g.2, hg⟩⟩
  obtain ⟨ι, -⟩ := charPair_exists_autOn_equiv hGV0 α hαs hαk0
  have hK : fstarPre G (VZ S G) = G :=
    CFSG.Quasithin.C126.Nat.fstarPre_eq_of_generalizedFitting_eq_top hGV0
      (CFSG.Quasithin.C126.Nat.generalizedFitting_eq_top_of_equiv_sl2 h4 ι)
  have hm : 1 ≤ m := by
    rcases m with _ | m
    · exfalso
      have h1 : 1 < Fintype.card F := Fintype.one_lt_card
      rw [hF, pow_zero] at h1
      exact lt_irrefl _ h1
    · omega
  refine ⟨m, hm, ?_⟩
  rw [hK]
  have hWW : (⁅VZ S G, G⁆ : Subgroup Ω) ≤ ⁅gomiV G, G⁆ := Subgroup.commutator_mono hVV le_rfl
  have hWn : G ≤ Subgroup.normalizer ((⁅VZ S G, G⁆ : Subgroup Ω) : Set Ω) :=
    charPair_le_normalizer_commutator hGV0 Subgroup.le_normalizer
  obtain ⟨β', hβ'⟩ : ∃ β' : ↥(⁅VZ S G, G⁆ : Subgroup Ω) →* Multiplicative (Fin 2 → F),
      ∀ u, β' u = β (Subgroup.inclusion hWW u) :=
    ⟨β.comp (Subgroup.inclusion hWW), MonoidHom.comp_apply β (Subgroup.inclusion hWW)⟩
  have hker : ∀ u : ↥(⁅VZ S G, G⁆ : Subgroup Ω),
      β' u = 1 ↔ (u : Ω) ∈ Subgroup.centralizer (G : Set Ω) := by
    intro u
    rw [hβ', ← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    exact ⟨fun hx => (Subgroup.mem_inf.mp hx).2, fun hx => Subgroup.mem_inf.mpr ⟨hWW u.2, hx⟩⟩
  have hβ'e : ∀ (g : G) (u v : ↥(⁅VZ S G, G⁆ : Subgroup Ω)), (v : Ω) = g * u * g⁻¹ →
      Multiplicative.toAdd (β' v) =
        (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β' u)) := by
    intro g u v huv
    rw [hβ', hβ']
    exact hβe g _ _ (by rw [Subgroup.coe_inclusion, Subgroup.coe_inclusion]; exact huv)
  refine charPair_isNatL2Section_of hF α hαk0 ?_ β' ?_ ?_ hβ'e
  · rw [MonoidHom.range_eq_top.mpr hαs, CFSG.Quasithin.C126.Nat.commutator_sl2_eq_top h4]
  ·
    have hne : ∃ u : ↥(⁅VZ S G, G⁆ : Subgroup Ω), β' u ≠ 1 := by
      by_contra hall
      push Not at hall
      have hWC : (⁅VZ S G, G⁆ : Subgroup Ω) ≤ Subgroup.centralizer (G : Set Ω) :=
        fun x hx => (hker ⟨x, hx⟩).mp (hall ⟨x, hx⟩)
      have h3 : ⁅⁅G, G⁆, VZ S G⁆ = ⊥ := by
        have h0 : ⁅⁅VZ S G, G⁆, G⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hWC
        refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
        · rw [Subgroup.commutator_comm G (VZ S G)]
          exact h0
        · exact h0
      have hGG : ⁅G, G⁆ ≤ Subgroup.centralizer (VZ S G : Set Ω) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
      have hcomm : commutator ↥G ≤ α.ker := by
        rw [hαk0]
        intro x hx
        rw [Subgroup.mem_subgroupOf]
        apply hGG
        have : (x : Ω) ∈ (commutator ↥G).map G.subtype := ⟨x, hx, rfl⟩
        rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype] at this
      have htop : (commutator ↥G).map α = ⊤ := by
        rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective α hαs,
          ← commutator_def, CFSG.Quasithin.C126.Nat.commutator_sl2_eq_top h4]
      have hbot : (commutator ↥G).map α = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        exact hcomm hx
      obtain ⟨u, hu⟩ := charPair_exists_sl2_mulVec_eq (F := F) (w := ![1, 0]) (t := ![0, 1])
        (by simp [funext_iff, Fin.forall_fin_two]) (by simp [funext_iff, Fin.forall_fin_two])
      have h1 : u ∈ (commutator ↥G).map α := htop ▸ Subgroup.mem_top u
      rw [hbot, Subgroup.mem_bot] at h1
      rw [h1, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at hu
      simp [funext_iff, Fin.forall_fin_two] at hu
    obtain ⟨u, hu⟩ := hne
    intro t
    by_cases ht : t = 1
    · exact ⟨1, by rw [map_one, ht]⟩
    · have hu' : Multiplicative.toAdd (β' u) ≠ 0 := fun h0 => hu (by
        rw [← ofAdd_toAdd (β' u), h0, ofAdd_zero])
      have ht' : Multiplicative.toAdd t ≠ 0 := fun h0 => ht (by
        rw [← ofAdd_toAdd t, h0, ofAdd_zero])
      obtain ⟨A, hA⟩ := charPair_exists_sl2_mulVec_eq hu' ht'
      obtain ⟨g, hg⟩ := hαs A
      have hmem : (g : Ω) * u * (g : Ω)⁻¹ ∈ (⁅VZ S G, G⁆ : Subgroup Ω) :=
        (Subgroup.mem_normalizer_iff.mp (hWn g.2) u).mp u.2
      refine ⟨⟨_, hmem⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [hβ'e g u ⟨_, hmem⟩ rfl, hg, hA]
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
    exact ⟨fun hx => Subgroup.mem_inf.mpr ⟨x.2, hx⟩, fun hx => (Subgroup.mem_inf.mp hx).2⟩

omit [Finite Ω] in
private theorem charPair_gomiV_comm {G : Subgroup Ω} {a b : Ω} (ha : a ∈ gomiV G)
    (hb : b ∈ gomiV G) : a * b = b * a :=
  Subgroup.mem_centralizer_iff.mp (charPair_omegaOneCenterOf_le_centerOf _ hb).2 a
    (charPair_omegaOneCenterOf_le_centerOf _ ha).1

omit [Finite Ω] in
private theorem charPair_gomiV_inv {G : Subgroup Ω} {x : Ω} (hx : x ∈ gomiV G) : x⁻¹ = x := by
  have hsq : x ^ 2 = 1 := by
    change x ∈ Subgroup.closure _ at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hy.2
    | one => exact one_pow 2
    | mul a b ha hb iha ihb =>
      rw [Commute.mul_pow (charPair_gomiV_comm ha hb) 2, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  exact inv_eq_of_mul_eq_one_left (by rw [← sq, hsq])

private theorem charPair_transport_two {X W : Type*} [Group X] [Group W] {F : Type} [Field F]
    [Fintype F] (h2 : Fintype.card F = 2) (α : X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαs : Function.Surjective α) (β : W →* Multiplicative (Fin 2 → F)) :
    ∃ (α₂ : X →* C1Pack.SL2F2) (β₂ : W →* Multiplicative (Fin 2 → ZMod 2)),
      Function.Surjective α₂ ∧ α₂.ker = α.ker ∧ β₂.ker = β.ker ∧
      ∀ (g : X) (u v : W), Multiplicative.toAdd (β v) =
          (α g : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β u) →
        Multiplicative.toAdd (β₂ v) =
          (α₂ g : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ Multiplicative.toAdd (β₂ u) := by
  have : CharP F 2 := charP_of_card_eq_prime h2
  let e : F ≃+* ZMod 2 := (ZMod.ringEquiv F h2).symm
  let E : Matrix.SpecialLinearGroup (Fin 2) F →* C1Pack.SL2F2 :=
    Matrix.SpecialLinearGroup.map e.toRingHom
  let E' : C1Pack.SL2F2 →* Matrix.SpecialLinearGroup (Fin 2) F :=
    Matrix.SpecialLinearGroup.map e.symm.toRingHom
  have hEE' : ∀ y, E (E' y) = y := fun y => by
    apply Subtype.ext
    ext i j
    show e (e.symm ((y : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j)) =
      (y : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j
    exact e.apply_symm_apply _
  have hE'E : ∀ y, E' (E y) = y := fun y => by
    apply Subtype.ext
    ext i j
    show e.symm (e ((y : Matrix (Fin 2) (Fin 2) F) i j)) = (y : Matrix (Fin 2) (Fin 2) F) i j
    exact e.symm_apply_apply _
  have hE1 : ∀ y, E y = 1 → y = 1 := fun y hy => by rw [← hE'E y, hy, map_one]
  let B : Multiplicative (Fin 2 → F) →* Multiplicative (Fin 2 → ZMod 2) :=
    AddMonoidHom.toMultiplicative ((e.toAddMonoidHom).compLeft (Fin 2))
  have hB : ∀ w, Multiplicative.toAdd (B w) = fun i => e (Multiplicative.toAdd w i) :=
    fun w => rfl
  refine ⟨E.comp α, B.comp β, ?_, ?_, ?_, ?_⟩
  · intro s
    obtain ⟨g, hg⟩ := hαs (E' s)
    exact ⟨g, by rw [MonoidHom.comp_apply, hg, hEE']⟩
  · ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact ⟨hE1 _, fun h => by rw [h, map_one]⟩
  · ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    refine ⟨fun h => ?_, fun h => by rw [h, map_one]⟩
    apply Multiplicative.toAdd.injective
    funext i
    have := congrFun (congrArg Multiplicative.toAdd h) i
    rw [hB] at this
    simpa using this
  · intro g u v huv
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hB, hB, huv]
    funext i
    simp [E, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem IsGomiQ.hasNaturalFstar_of_sl2F2 {S G : Subgroup Ω} (h : IsGomiQ S G)
    (hC : G ⊓ Subgroup.centralizer (VZ S G : Set Ω) ≤ Subgroup.centralizer (gomiV G : Set Ω))
    (α : ↥G →* C1Pack.SL2F2) (hαs : Function.Surjective α)
    (hαk : α.ker = (Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf G)
    (β : ↥(⁅gomiV G, G⁆ : Subgroup Ω) →* Multiplicative (Fin 2 → ZMod 2))
    (hβk : β.ker = (⁅gomiV G, G⁆ ⊓ Subgroup.centralizer (G : Set Ω)).subgroupOf ⁅gomiV G, G⁆)
    (hβe : ∀ (g : G) (u v : ↥(⁅gomiV G, G⁆ : Subgroup Ω)), (v : Ω) = g * u * g⁻¹ →
      Multiplicative.toAdd (β v) =
        (α g : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec (Multiplicative.toAdd (β u))) :
    HasNaturalFstar G (VZ S G) := by
  have hGV0 := charPair_le_normalizer_vZ S G
  have hVV := h.vZ_le_gomiV
  have hαk0 : α.ker = (Subgroup.centralizer (VZ S G : Set Ω)).subgroupOf G := by
    rw [hαk]
    ext g
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun hg => Subgroup.centralizer_le hVV hg, fun hg => hC ⟨g.2, hg⟩⟩
  obtain ⟨ι, hι⟩ := charPair_exists_autOn_equiv hGV0 α hαs hαk0
  have hKG : fstarPre G (VZ S G) ≤ G := inf_le_left
  have hKiff : ∀ g : ↥G, (g : Ω) ∈ fstarPre G (VZ S G) ↔ α g ^ 3 = 1 := fun g => by
    rw [C1Pack.mem_fstarPre_iff hGV0 ι g.2, hι, C1Pack.commutator_sl2_eq, C1Pack.mem_sl2A3]
  refine ⟨1, le_rfl, ?_⟩
  obtain ⟨αK, hαK⟩ : ∃ αK : ↥(fstarPre G (VZ S G)) →* C1Pack.SL2F2,
      ∀ k, αK k = α (Subgroup.inclusion hKG k) :=
    ⟨α.comp (Subgroup.inclusion hKG), MonoidHom.comp_apply α (Subgroup.inclusion hKG)⟩
  have hαKg : ∀ (g : ↥G) (hg : (g : Ω) ∈ fstarPre G (VZ S G)), αK ⟨g, hg⟩ = α g :=
    fun g hg => by
      rw [hαK]
      exact congrArg α (Subtype.ext (Subgroup.coe_inclusion hKG _))
  have hαKk : αK.ker =
      (Subgroup.centralizer (VZ S G : Set Ω)).subgroupOf (fstarPre G (VZ S G)) := by
    ext k
    rw [MonoidHom.mem_ker, hαK, ← MonoidHom.mem_ker, hαk0, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hαKr : αK.range = commutator C1Pack.SL2F2 := by
    rw [C1Pack.commutator_sl2_eq]
    ext s
    rw [MonoidHom.mem_range, C1Pack.mem_sl2A3]
    constructor
    · rintro ⟨k, rfl⟩
      rw [hαK]
      exact (hKiff _).mp (by rw [Subgroup.coe_inclusion]; exact k.2)
    · intro hs
      obtain ⟨g, rfl⟩ := hαs s
      exact ⟨⟨g, (hKiff g).mpr hs⟩, hαKg g _⟩
  have hWW : (⁅VZ S G, fstarPre G (VZ S G)⁆ : Subgroup Ω) ≤ ⁅gomiV G, G⁆ :=
    Subgroup.commutator_mono hVV hKG
  have hWn : fstarPre G (VZ S G) ≤
      Subgroup.normalizer ((⁅VZ S G, fstarPre G (VZ S G)⁆ : Subgroup Ω) : Set Ω) :=
    charPair_le_normalizer_commutator (hKG.trans hGV0) Subgroup.le_normalizer
  obtain ⟨βK, hβK⟩ : ∃ βK : ↥(⁅VZ S G, fstarPre G (VZ S G)⁆ : Subgroup Ω) →*
      Multiplicative (Fin 2 → ZMod 2), ∀ u, βK u = β (Subgroup.inclusion hWW u) :=
    ⟨β.comp (Subgroup.inclusion hWW), MonoidHom.comp_apply β (Subgroup.inclusion hWW)⟩
  have hβKe : ∀ (k : ↥(fstarPre G (VZ S G)))
      (u v : ↥(⁅VZ S G, fstarPre G (VZ S G)⁆ : Subgroup Ω)), (v : Ω) = k * u * k⁻¹ →
      Multiplicative.toAdd (βK v) =
        (αK k : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec (Multiplicative.toAdd (βK u)) := by
    intro k u v huv
    rw [hβK, hβK, hαK]
    refine hβe _ _ _ ?_
    simpa only [Subgroup.coe_inclusion, Subgroup.coe_inv] using huv
  have hβKker : ∀ u : ↥(⁅VZ S G, fstarPre G (VZ S G)⁆ : Subgroup Ω),
      βK u = 1 ↔ (u : Ω) ∈ Subgroup.centralizer (fstarPre G (VZ S G) : Set Ω) := by
    intro u
    constructor
    · intro hu
      rw [hβK, ← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at hu
      exact Subgroup.centralizer_le hKG (Subgroup.mem_inf.mp hu).2
    · intro hu
      have hfix : ∀ x : Fin 2 → ZMod 2, (∀ s : C1Pack.SL2F2, s ^ 3 = 1 →
          (s : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ x = x) → x = 0 := by decide
      have h0 : Multiplicative.toAdd (βK u) = 0 := by
        refine hfix _ fun s hs => ?_
        obtain ⟨g, rfl⟩ := hαs s
        have hgK : (g : Ω) ∈ fstarPre G (VZ S G) := (hKiff g).mpr hs
        have hc := Subgroup.mem_centralizer_iff.mp hu (g : Ω) hgK
        have := hβKe ⟨g, hgK⟩ u u (by
          simp only [Subgroup.coe_inv]
          rw [hc, mul_inv_cancel_right])
        rw [hαKg] at this
        exact this.symm
      rw [← ofAdd_toAdd (βK u), h0, ofAdd_zero]
  have hβKk : βK.ker = (⁅VZ S G, fstarPre G (VZ S G)⁆ ⊓
      Subgroup.centralizer (fstarPre G (VZ S G) : Set Ω)).subgroupOf
        ⁅VZ S G, fstarPre G (VZ S G)⁆ := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hβKker]
    exact ⟨fun hu => Subgroup.mem_inf.mpr ⟨u.2, hu⟩, fun hu => (Subgroup.mem_inf.mp hu).2⟩
  have hne : ∃ u, βK u ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨s₀, hs₀3, hs₀1⟩ : ∃ s : C1Pack.SL2F2, s ^ 3 = 1 ∧ s ≠ 1 := by decide
    obtain ⟨g, hg⟩ := hαs s₀
    have hgK : (g : Ω) ∈ fstarPre G (VZ S G) := (hKiff g).mpr (hg ▸ hs₀3)
    have hg2 : ∀ v ∈ VZ S G, v * (g : Ω) ^ 2 = (g : Ω) ^ 2 * v := by
      intro v hv
      have hw : ⁅v, (g : Ω)⁆ ∈ (⁅VZ S G, fstarPre G (VZ S G)⁆ : Subgroup Ω) :=
        Subgroup.commutator_mem_commutator hv hgK
      have hwc : (g : Ω) * ⁅v, (g : Ω)⁆ = ⁅v, (g : Ω)⁆ * (g : Ω) :=
        Subgroup.mem_centralizer_iff.mp ((hβKker ⟨_, hw⟩).mp (hall ⟨_, hw⟩)) (g : Ω) hgK
      have ha : (g : Ω) * v * (g : Ω)⁻¹ ∈ VZ S G :=
        (Subgroup.mem_normalizer_iff.mp (hGV0 g.2) v).mp hv
      have hb : (g : Ω) * ((g : Ω) * v * (g : Ω)⁻¹) * (g : Ω)⁻¹ ∈ VZ S G :=
        (Subgroup.mem_normalizer_iff.mp (hGV0 g.2) _).mp ha
      have hconj : (g : Ω) * ⁅v, (g : Ω)⁆ * (g : Ω)⁻¹ = ⁅v, (g : Ω)⁆ := by
        rw [hwc, mul_inv_cancel_right]
      have hab : ((g : Ω) * v * (g : Ω)⁻¹) *
          ((g : Ω) * ((g : Ω) * v * (g : Ω)⁻¹) * (g : Ω)⁻¹)⁻¹ =
            v * ((g : Ω) * v * (g : Ω)⁻¹)⁻¹ := by
        calc _ = (g : Ω) * ⁅v, (g : Ω)⁆ * (g : Ω)⁻¹ := by
                simp only [commutatorElement_def]
                group
          _ = ⁅v, (g : Ω)⁆ := hconj
          _ = _ := by
                simp only [commutatorElement_def]
                group
      rw [charPair_gomiV_inv (hVV hb), charPair_gomiV_inv (hVV ha),
        charPair_gomiV_comm (hVV hv) (hVV ha)] at hab
      have hbv := mul_left_cancel hab
      calc v * (g : Ω) ^ 2 = (g : Ω) * ((g : Ω) * v * (g : Ω)⁻¹) * (g : Ω)⁻¹ * (g : Ω) ^ 2 := by
            rw [hbv]
        _ = (g : Ω) ^ 2 * v := by rw [sq]; group
    have hg3 : (g : Ω) ^ 3 ∈ Subgroup.centralizer (VZ S G : Set Ω) := by
      have h3 : g ^ 3 ∈ α.ker := by rw [MonoidHom.mem_ker, map_pow, hg, hs₀3]
      rw [hαk0, Subgroup.mem_subgroupOf, Subgroup.coe_pow] at h3
      exact h3
    have hg2c : (g : Ω) ^ 2 ∈ Subgroup.centralizer (VZ S G : Set Ω) :=
      Subgroup.mem_centralizer_iff.mpr fun v hv => hg2 v hv
    have hgc : (g : Ω) ∈ Subgroup.centralizer (VZ S G : Set Ω) := by
      have hgg : (g : Ω) = (g : Ω) ^ 3 * ((g : Ω) ^ 2)⁻¹ := by group
      rw [hgg]
      exact Subgroup.mul_mem _ hg3 (Subgroup.inv_mem _ hg2c)
    have hk : g ∈ α.ker := by
      rw [hαk0, Subgroup.mem_subgroupOf]
      exact hgc
    exact hs₀1 (hg.symm.trans (MonoidHom.mem_ker.mp hk))
  have hβKs : Function.Surjective βK := by
    obtain ⟨u, hu⟩ := hne
    have htrans : ∀ x y : Fin 2 → ZMod 2, x ≠ 0 → y ≠ 0 → ∃ s : C1Pack.SL2F2,
        s ^ 3 = 1 ∧ (s : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ x = y := by decide
    intro t
    by_cases ht : t = 1
    · exact ⟨1, by rw [map_one, ht]⟩
    · have hu' : Multiplicative.toAdd (βK u) ≠ 0 := fun h0 => hu (by
        rw [← ofAdd_toAdd (βK u), h0, ofAdd_zero])
      have ht' : Multiplicative.toAdd t ≠ 0 := fun h0 => ht (by
        rw [← ofAdd_toAdd t, h0, ofAdd_zero])
      obtain ⟨s, hs3, hs⟩ := htrans _ _ hu' ht'
      obtain ⟨g, rfl⟩ := hαs s
      have hgK : (g : Ω) ∈ fstarPre G (VZ S G) := (hKiff g).mpr hs3
      have hmem : (g : Ω) * u * (g : Ω)⁻¹ ∈ (⁅VZ S G, fstarPre G (VZ S G)⁆ : Subgroup Ω) :=
        (Subgroup.mem_normalizer_iff.mp (hWn hgK) u).mp u.2
      refine ⟨⟨_, hmem⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [hβKe ⟨g, hgK⟩ u ⟨_, hmem⟩ rfl, hαKg, hs]
  exact charPair_isNatL2Section_of (by rw [ZMod.card, pow_one]) αK hαKk hαKr βK hβKs hβKk hβKe

end Natural

theorem IsGomiQ.inClassG [Finite Ω] {S G : Subgroup Ω} (h : IsGomiQ S G)
    (hZ : ¬ G ≤ Subgroup.centralizer (omegaOneCenterOf S : Set Ω)) : InClassG G S := by
  refine ⟨h.sylow, h.charTwo, h.isMinParabolicOf, ?_⟩
  have hC := h.inf_centralizer_vZ_le hZ
  obtain ⟨m, F, _, _, hF, α, hαs, hαk, β, -, hβk, hβe⟩ := h.natural
  by_cases h4 : 4 ≤ Nat.card F
  · exact h.hasNaturalFstar_of_four_le hC hF h4 α hαs hαk β hβk hβe
  · obtain ⟨α₂, β₂, hα₂s, hα₂k, hβ₂k, hβ₂e⟩ :=
      charPair_transport_two (charPair_card_eq_two hF h4) α hαs β
    exact h.hasNaturalFstar_of_sl2F2 hC α₂ hα₂s (hα₂k.trans hαk) β₂ (hβ₂k.trans hβk)
      fun g u v huv => hβ₂e g u v (hβe g u v huv)

section Block

private theorem charPair_commutator_le [Finite Ω] {Q L : Subgroup Ω} (hQ : IsPGroup 2 Q)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set Ω))
    (hL : ∀ (N : Subgroup L) [N.Normal], IsPGroup 2 (L ⧸ N) → N = ⊤) :
    ⁅Q, L⁆ ≤ ⁅⁅Q, L⁆, L⁆ := by
  have hLN : L ≤ Subgroup.normalizer ((⁅⁅Q, L⁆, L⁆ : Subgroup Ω) : Set Ω) :=
    Subgroup.normalizer_commutator_ge_right _ _
  let K : Subgroup Ω :=
    { carrier := {l | l ∈ L ∧ ∀ q ∈ Q, ⁅q, l⁆ ∈ ⁅⁅Q, L⁆, L⁆}
      one_mem' := ⟨L.one_mem, fun q _ => by
        rw [commutatorElement_one_right]
        exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨L.mul_mem ha hb, fun q hq => ?_⟩
        have he : ⁅q, a * b⁆ = ⁅q, a⁆ * (a * ⁅q, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [he]
        exact Subgroup.mul_mem _ (ha' q hq)
          ((Subgroup.mem_normalizer_iff.mp (hLN ha) _).mp (hb' q hq))
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨L.inv_mem ha, fun q hq => ?_⟩
        have he : ⁅q, a⁻¹⁆ = a⁻¹ * ⁅q, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [he]
        exact (Subgroup.mem_normalizer_iff.mp (hLN (L.inv_mem ha)) _).mp
          (Subgroup.inv_mem _ (ha' q hq)) }
  have hLK : L ≤ K := by
    refine (CFSG.QuasithinUnique.Vol2Native.L239.Lie.le_closure_odd_of_no_two_quotient
      hL).trans ((Subgroup.closure_le K).mpr ?_)
    rintro x ⟨hxL, hx⟩
    refine ⟨hxL, fun q hq => ?_⟩
    exact CFSG.Quasithin.F53.Stellmacher.S35.K6b.comm_mem_of_odd hQ hLQ hxL
      (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hx)) (pow_orderOf_eq_one x) hq
  rw [Subgroup.commutator_le]
  intro q hq l hl
  exact (hLK hl).2 q hq

theorem commutator_pCoreOf_twoResidual_le_gomiV [Finite Ω] {G : Subgroup Ω}
    (h : IsBlock2 G (twoResidual G)) : ⁅pCoreOf 2 G, twoResidual G⁆ ≤ gomiV G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨h1, -, ⟨hUQ, hU2⟩, -, hZU, hirr⟩, hLG, -⟩ := h
  set L := twoResidual G with hLdef
  set Q := pCoreOf 2 G with hQdef
  have hGL : G ≤ Subgroup.normalizer (L : Set Ω) := le_normalizer_twoResidual G
  have hGQ : G ≤ Subgroup.normalizer (Q : Set Ω) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G
  have hQG : Q ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hGQL : G ≤ Subgroup.normalizer (blockQ L : Set Ω) :=
    hGL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hQLL : blockQ L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hQL2 : IsPGroup 2 (blockQ L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hQLQ : blockQ L ≤ Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQLL.trans hLG) hGQL hQL2
  have hLQL : L ≤ Subgroup.normalizer (blockQ L : Set Ω) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hLQ : L ≤ Subgroup.normalizer (Q : Set Ω) := hLG.trans hGQ
  have hcommQ : ⁅Q, L⁆ ≤ blockQ L := by
    have h1' : ⁅Q, L⁆ ≤ L :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp (hQG.trans hGL)
    have h2' : ⁅Q, L⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_left.mp hLQ
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h1'
      (Subgroup.normalizer_commutator_ge_right Q L) (hQ2.to_le h2')
  have hQLU : ⁅Q, L⁆ ≤ blockU L :=
    (charPair_commutator_le hQ2 hLQ h1).trans (Subgroup.commutator_mono hcommQ le_rfl)
  have hUQL : blockU L ≤ blockQ L := fun x hx => (hUQ hx).1
  have hUC : ∀ u ∈ blockU L, ∀ k ∈ blockQ L, k * u = u * k := fun u hu k hk =>
    Subgroup.mem_centralizer_iff.mp (hUQ hu).2 k hk
  have hUab : ∀ u ∈ blockU L, ∀ v ∈ blockU L, u * v = v * u := fun u hu v hv =>
    (hUC u hu v (hUQL hv)).symm
  have hUQ' : blockU L ≤ Q := hUQL.trans hQLQ
  have hZUle : blockZ L ≤ blockU L := inf_le_left
  have hZL : ∀ z ∈ blockZ L, ∀ l ∈ L, l * z = z * l := fun z hz l hl =>
    Subgroup.mem_centralizer_iff.mp hz.2 l hl
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set Ω) :=
    Subgroup.normalizer_commutator_ge_right _ _
  have hQU : Q ≤ Subgroup.normalizer (blockU L : Set Ω) :=
    charPair_le_normalizer_commutator (hQG.trans hGQL) (hQG.trans hGL)
  have hUL : blockU L ≤ ⁅blockU L, L⁆ := charPair_commutator_le hQL2 hLQL h1
  have hconjZL : ∀ l ∈ L, ∀ z ∈ blockZ L, l * z * l⁻¹ = z := fun l hl z hz => by
    rw [hZL z hz l hl, mul_inv_cancel_right]
  have hconjZQ : ∀ y ∈ Q, ∀ z ∈ blockZ L, y * z * y⁻¹ ∈ blockZ L := by
    intro y hy z hz
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hQU hy) z).mp hz.1,
      Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hl' : y⁻¹ * l * y ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hQG.trans hGL (Q.inv_mem hy)) l).mp hl
      simpa using this
    have hc := hZL z hz _ hl'
    calc l * (y * z * y⁻¹) = y * ((y⁻¹ * l * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * l * y)) * y⁻¹ := by rw [hc]
      _ = y * z * y⁻¹ * l := by group
  have h4a : ∀ u ∈ blockU L, ∀ y ∈ Q, ⁅u, y⁆ ∈ blockZ L := by
    let F : Subgroup Ω :=
      { carrier := {u | u ∈ blockU L ∧ ∀ y ∈ Q, ⁅u, y⁆ ∈ blockZ L}
        one_mem' := ⟨Subgroup.one_mem _, fun y _ => by
          rw [commutatorElement_one_left]
          exact Subgroup.one_mem _⟩
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨Subgroup.mul_mem _ ha hb, fun y hy => ?_⟩
          have he : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
            simp only [commutatorElement_def]
            group
          have hc : a * ⁅b, y⁆ * a⁻¹ = ⁅b, y⁆ := by
            rw [hUab a ha _ (hZUle (hb' y hy)), mul_inv_cancel_right]
          rw [he, hc]
          exact Subgroup.mul_mem _ (hb' y hy) (ha' y hy)
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨Subgroup.inv_mem _ ha, fun y hy => ?_⟩
          have he : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a := by
            simp only [commutatorElement_def]
            group
          have hz : ⁅a, y⁆⁻¹ ∈ blockZ L := Subgroup.inv_mem _ (ha' y hy)
          have hc : a⁻¹ * ⁅a, y⁆⁻¹ * a = ⁅a, y⁆⁻¹ := by
            rw [hUab _ (Subgroup.inv_mem _ ha) _ (hZUle hz), inv_mul_cancel_right]
          rw [he, hc]
          exact hz }
    have hZF : blockZ L ≤ F := fun z hz => ⟨hZUle hz, fun y hy => by
      have he : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [he]
      exact Subgroup.mul_mem _ hz (hconjZQ y hy _ (Subgroup.inv_mem _ hz))⟩
    have hFU : F ≤ blockU L := fun u hu => hu.1
    have hLF : L ≤ Subgroup.normalizer (F : Set Ω) := by
      have key : ∀ l ∈ L, ∀ u ∈ F, l * u * l⁻¹ ∈ F := by
        rintro l hl u ⟨hu, hu'⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp (hLU hl) u).mp hu, fun y hy => ?_⟩
        have hy' : l⁻¹ * y * l ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.mp (hLQ (L.inv_mem hl)) y).mp hy
          simpa using this
        have he : ⁅l * u * l⁻¹, y⁆ = l * ⁅u, l⁻¹ * y * l⁆ * l⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [he, hconjZL l hl _ (hu' _ hy')]
        exact hu' _ hy'
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨key l hl x, fun hx => ?_⟩
      have := key l⁻¹ (L.inv_mem hl) _ hx
      simpa [mul_assoc] using this
    rcases hirr F hZF hFU hLF with hF | hF
    · exfalso
      have hZQ : blockZ L ≤ Q := hZUle.trans hUQ'
      have hQZ' : Q ≤ Subgroup.normalizer (blockZ L : Set Ω) := fun y hy =>
        Subgroup.mem_normalizer_iff.mpr fun z => ⟨hconjZQ y hy z, fun hz => by
          have := hconjZQ y⁻¹ (Q.inv_mem hy) _ hz
          simpa [mul_assoc] using this⟩
      have : ((blockZ L).subgroupOf Q).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hZQ).mpr hQZ'
      have hUn : ((blockU L).subgroupOf Q).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hUQ').mpr hQU
      have : Group.IsNilpotent (↥Q ⧸ (blockZ L).subgroupOf Q) :=
        (hQ2.to_quotient _).isNilpotent
      set π := QuotientGroup.mk' ((blockZ L).subgroupOf Q) with hπ
      have : (((blockU L).subgroupOf Q).map π).Normal :=
        hUn.map π (QuotientGroup.mk'_surjective _)
      have hne : ((blockU L).subgroupOf Q).map π ≠ ⊥ := by
        obtain ⟨u, hu, huZ⟩ := SetLike.exists_of_lt hZU
        intro hbot
        have hmem : π ⟨u, hUQ' hu⟩ ∈ ((blockU L).subgroupOf Q).map π :=
          ⟨⟨u, hUQ' hu⟩, hu, rfl⟩
        rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hmem
        exact huZ hmem
      obtain ⟨⟨x, hxU, hxZ⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
        (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
      obtain ⟨q, hq, rfl⟩ := hxU
      have hqF : (q : Ω) ∈ F := by
        refine ⟨hq, fun y hy => ?_⟩
        have hc : ⁅π q, π ⟨y, hy⟩⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact ((Subgroup.mem_center_iff.mp hxZ) (π ⟨y, hy⟩)).symm
        rw [← map_commutatorElement, hπ, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hc
        exact hc
      rw [hF] at hqF
      apply hx1
      apply Subtype.ext
      show π q = 1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hqF
    · intro u hu y hy
      have hu' : u ∈ F := by
        rw [hF]
        exact hu
      exact hu'.2 y hy
  have h4b : ∀ u ∈ blockU L, ∀ y ∈ Q, y * u = u * y := by
    intro u hu y hy
    have hφmul : ∀ a ∈ blockU L, ∀ b ∈ blockU L, ⁅a * b, y⁆ = ⁅b, y⁆ * ⁅a, y⁆ := by
      intro a ha b hb
      have he : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
        simp only [commutatorElement_def]
        group
      rw [he, hUab a ha _ (hZUle (h4a b hb y hy)), mul_inv_cancel_right]
    have hφconj : ∀ l ∈ L, ∀ a ∈ blockU L, ⁅l * a * l⁻¹, y⁆ = ⁅a, y⁆ := by
      intro l hl a ha
      have hy' : l⁻¹ * y * l ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp (hLQ (L.inv_mem hl)) y).mp hy
        simpa using this
      have he : ⁅l * a * l⁻¹, y⁆ = l * ⁅a, l⁻¹ * y * l⁆ * l⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [he, hconjZL l hl _ (h4a a ha _ hy')]
      have hk : y⁻¹ * l⁻¹ * y * l ∈ blockQ L := by
        have hm := Subgroup.commutator_mem_commutator (Q.inv_mem hy) (L.inv_mem hl)
        have hk' : ⁅y⁻¹, l⁻¹⁆ = y⁻¹ * l⁻¹ * y * l := by
          simp only [commutatorElement_def, inv_inv]
        rw [hk'] at hm
        exact hcommQ hm
      have hkc := hUC a⁻¹ (Subgroup.inv_mem _ ha) _ hk
      have hl' : l⁻¹ * y * l = y * (y⁻¹ * l⁻¹ * y * l) := by group
      rw [hl']
      calc ⁅a, y * (y⁻¹ * l⁻¹ * y * l)⁆
          = a * y * ((y⁻¹ * l⁻¹ * y * l) * a⁻¹) * (y⁻¹ * l⁻¹ * y * l)⁻¹ * y⁻¹ := by
            simp only [commutatorElement_def]
            group
        _ = a * y * (a⁻¹ * (y⁻¹ * l⁻¹ * y * l)) * (y⁻¹ * l⁻¹ * y * l)⁻¹ * y⁻¹ := by
            rw [hkc]
        _ = ⁅a, y⁆ := by
            simp only [commutatorElement_def]
            group
    have hgen : ∀ a ∈ blockU L, ∀ l ∈ L, ⁅⁅a, l⁆, y⁆ = 1 := by
      intro a ha l hl
      have hw : l * a⁻¹ * l⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (hLU hl) _).mp (Subgroup.inv_mem _ ha)
      have he : ⁅a, l⁆ = a * (l * a⁻¹ * l⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [he, hφmul a ha _ hw, hφconj l hl _ (Subgroup.inv_mem _ ha)]
      have h0 := hφmul a ha a⁻¹ (Subgroup.inv_mem _ ha)
      rw [mul_inv_cancel, commutatorElement_one_left] at h0
      exact h0.symm
    have hcen : ⁅blockU L, L⁆ ≤ Subgroup.centralizer ({y} : Set Ω) := by
      rw [Subgroup.commutator_le]
      intro a ha l hl
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((commutatorElement_eq_one_iff_mul_comm.mp (hgen a ha l hl))).symm
    exact (Subgroup.mem_centralizer_iff.mp (hcen (hUL hu))) y rfl
  refine hQLU.trans fun x hx => ?_
  apply Subgroup.subset_closure
  refine ⟨⟨hUQ' hx, Subgroup.mem_centralizer_iff.mpr fun y hy => h4b x hx y hy⟩, hU2 x hx⟩

theorem IsGomiQ.not_isL2OrA3Block [Finite Ω] {S G : Subgroup Ω} (h : IsGomiQ S G) :
    ¬ IsL2OrA3Block G (twoResidual G) :=
  fun hb => h.not_commutator_le (commutator_pCoreOf_twoResidual_le_gomiV hb.1)

end Block

end CFSG.GroupTheory

end
