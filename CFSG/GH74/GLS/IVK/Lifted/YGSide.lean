module

public import CFSG.GH74.GLS.IVK.Lifted.YImg
public import CFSG.GH74.GLS.IVK.Lifted.Lem13a52
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue73
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Prop66

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped commutatorElement

section Img

variable {G : Type} [Group G] {X : Subgroup G} {H : Type} [Group H]

@[expose] def imgT (π : ↥X →* H) (T : Subgroup G) : Subgroup H := (T.subgroupOf X).map π

theorem mem_imgT (π : ↥X →* H) {T : Subgroup G} {a : H} :
    a ∈ imgT π T ↔ ∃ s : ↥X, (s : G) ∈ T ∧ π s = a := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩

theorem imgT_sup (π : ↥X →* H) {T₁ T₂ : Subgroup G} (h₁ : T₁ ≤ X) (h₂ : T₂ ≤ X) :
    imgT π (T₁ ⊔ T₂) = imgT π T₁ ⊔ imgT π T₂ := by
  unfold imgT
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

theorem imgT_zpowers (π : ↥X →* H) {t : G} (ht : t ∈ X) :
    imgT π (zpowers t) = zpowers (π ⟨t, ht⟩) := by
  ext a
  rw [mem_imgT, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hs
    refine ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
    apply Subtype.ext
    simpa using hk
  · rintro ⟨k, rfl⟩
    refine ⟨⟨t, ht⟩ ^ k, ?_, by rw [map_zpow]⟩
    show ((⟨t, ht⟩ ^ k : ↥X) : G) ∈ zpowers t
    rw [Subgroup.coe_zpow]
    exact zpow_mem_zpowers t k

theorem imgT_swap (π : ↥X →* H) (hπ : Function.Surjective π) (T : Subgroup G) {t : G} (ht : t ∈ X)
    (htt : t * t = 1) :
    swapSub (imgT π T) (π ⟨t, ht⟩) = imgT π (swapSub T t) := by
  have htt' : (⟨t, ht⟩ : ↥X) * ⟨t, ht⟩ = 1 := Subtype.ext htt
  have h1 := swapSub_map π hπ (T.subgroupOf X) htt'
  have h2 : (swapSub T t).subgroupOf X = swapSub (T.subgroupOf X) ⟨t, ht⟩ := by
    ext x
    rfl
  unfold imgT
  rw [h2]
  exact h1

end Img

section PhiW

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ} {w : G}

theorem phi_w_facts (h44 : II4_44) (hII : II4_4_4_center) (hC : Cfg7 G z S K₁ K₂ t u q)
    (hconcl : Concl72abcf z S K₁ K₂ t q w) (hw1 : w ≠ 1) {A : Subgroup G} (hAc : A = K₁ ∨ A = K₂)
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Hat A ≃* SpecialLinearGroup (Fin 2) F) (hwNA : w ∈ normalizer (A : Set G)) :
    phi A w hwNA ∉ innOf (Hat A) ∧
      (gammaOf hodd h3 (MulAut.congr e (phi A w hwNA))).right = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hC.std.std
  have hM := m4_of_std hII hstd
  obtain ⟨hwS, hw12, htw, ⟨hPY, hSPY⟩, hS1, hint, hpgl⟩ := hconcl
  have hw2 : orderOf w = 2 := hw12.resolve_left hw1
  have hww : w * w = 1 := mul_self_eq_one_of_orderOf_eq_two hw2
  have hz2 : orderOf z = 2 := hstd.orderOf_z
  have hAmem : A ∈ ({K₁, K₂} : Set (Subgroup G)) := by simpa using hAc
  have hOK := std4_hatOK h44 hstd hAmem
  have hKz : A ≤ centralizer ({z} : Set G) := by
    rcases hAc with rfl | rfl
    · exact hM.K₁_le
    · exact hM.K₂_le
  have hzA : z ∈ A := hM.z_mem_comp hAc
  have hmQA : pRank 2 ↥(Qof S A) = 1 := by
    rcases hAc with rfl | rfl
    · exact hC.std.b₁
    · exact hC.std.b₂
  have hzP : z ∈ Pz S z := by
    rw [CFSG.GH74.GLS.Stage1.Thm3.Sec4.Pz_eq hstd]
    exact hM.z_mem_P
  have hα1 : phi A w hwNA ≠ 1 := by
    intro h1
    have hwc : w ∈ cSec A := (phi_eq_one_iff A hwNA).1 h1
    have hwz : w = z := eq_z_of_mem_Qof hM hAc hmQA hz2 ⟨hwS, hwc⟩ hw2
    have h2 : z ∈ Pz S z ⊓ Ysub t w := ⟨hzP, hwz ▸ mem_sup_right (mem_zpowers w)⟩
    rw [hPY, Subgroup.mem_bot] at h2
    rw [h2, orderOf_one] at hz2
    omega
  have hαf : (gammaOf hodd h3 (MulAut.congr e (phi A w hwNA))).right = 1 := by
    by_contra hσ
    have hφ2 : phi A w hwNA * phi A w hwNA = 1 := phi_mul_self A hwNA hww
    have hα2 : MulAut.congr e (phi A w hwNA) * MulAut.congr e (phi A w hwNA) = 1 := by
      rw [← map_mul, hφ2, map_one]
    have hF : InducesFAut w A := ⟨hwNA, hOK.quasi, hOK.kgrp, hOK.rank, exists_pow_two_orderOf hφ2,
      fixedCond_of_congr e (fixedCond_of_field_part hodd h3 _ hα2 hσ)⟩
    have hwc : w ∈ cSec A := by
      rcases hAc with rfl | rfl
      · exact hC.std.a₁ w hwS hF
      · exact hC.std.a₂ w hwS hF
    exact hα1 ((phi_eq_one_iff A hwNA).2 hwc)
  have hq : HatSL2 A q := by
    rcases hAc with rfl | rfl
    · exact hC.ch.hq₁
    · exact hC.ch.hq₂
  exact ⟨phi_not_inner_of_pglQuot hq hzA hKz hz2 hOK.sl2.2 hwNA (hpgl hw1 A hAmem), hαf⟩

end PhiW

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ} {w : G}

omit [Finite G] in
theorem oz_subgroupOf_normal {X : Subgroup G} (hX : X ≤ Cz z) : ((Oz z).subgroupOf X).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact Oz_conj (hX g.2) hn⟩

theorem yconf_of_G (h44 : II4_44) (hII : II4_4_4_center) (hC : Cfg7 G z S K₁ K₂ t u q)
    (hconcl : Concl72abcf z S K₁ K₂ t q w) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (eG : Hat K₁ ≃* SpecialLinearGroup (Fin 2) F)
    [hn : ((Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)).Normal] :
    ∃ c : YConf F hodd h3 (↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)),
      (∀ s : ↥(K₁ ⊔ K₂ ⊔ S), (s : G) = t →
        (QuotientGroup.mk s : ↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)) = c.τ) ∧
      (∀ s : ↥(K₁ ⊔ K₂ ⊔ S), (s : G) = w →
        (QuotientGroup.mk s : ↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)) = c.ω) ∧
      c.X = ⊤ ∧
      (∀ a, a ∈ c.P ↔ ∃ s : ↥(K₁ ⊔ K₂ ⊔ S), (s : G) ∈ Pz S z ∧
        (QuotientGroup.mk s : ↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)) = a) ∧
      (∀ a, a ∈ c.P ⊔ zpowers c.τ ⊔ zpowers c.ω ↔ ∃ s : ↥(K₁ ⊔ K₂ ⊔ S), (s : G) ∈ S ∧
        (QuotientGroup.mk s : ↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)) = a) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hC.std.std
  have hM := hC.m4 hII
  have hK₁m : K₁ ∈ ({K₁, K₂} : Set (Subgroup G)) := Set.mem_insert _ _
  have hK₂m : K₂ ∈ ({K₁, K₂} : Set (Subgroup G)) := Set.mem_insert_of_mem _ rfl
  have hpc₁ : IsPCompIn 2 (Cz z) K₁ := hstd.comp_isPCompIn (Or.inl rfl)
  have hpc₂ : IsPCompIn 2 (Cz z) K₂ := hstd.comp_isPCompIn (Or.inr rfl)
  set X : Subgroup G := K₁ ⊔ K₂ ⊔ S with hXdef
  set N₀ : Subgroup ↥X := (Oz z).subgroupOf X with hN₀
  let π : ↥X →* ↥X ⧸ N₀ := QuotientGroup.mk' N₀
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N₀
  have hπker : ∀ s : ↥X, π s = 1 ↔ (s : G) ∈ Oz z := fun s => by
    show (QuotientGroup.mk s : ↥X ⧸ N₀) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact Iff.rfl
  obtain ⟨hwS, hw12, htw, ⟨hPY, hSPY⟩, hS1, hint, hpgl⟩ := id hconcl
  have hK₁X : K₁ ≤ X := le_sup_left.trans le_sup_left
  have hK₂X : K₂ ≤ X := le_sup_right.trans le_sup_left
  have hSX : S ≤ X := le_sup_right
  have htS : t ∈ S := hC.ch.t_mem
  have htX : t ∈ X := hSX htS
  have hwX : w ∈ X := hSX hwS
  have hzK₁ : z ∈ K₁ := hM.z_mem_comp (Or.inl rfl)
  have hzK₂ : z ∈ K₂ := hM.z_mem_comp (Or.inr rfl)
  have hzX : z ∈ X := hK₁X hzK₁
  have htt : t * t = 1 := hC.t_sq
  have hww : w * w = 1 := by
    rcases hw12 with h | h
    · rw [h]
      simp
    · exact mul_self_eq_one_of_orderOf_eq_two h
  have hz2 : z * z = 1 := hM.z_sq
  have hz1 : z ≠ 1 := hM.z_ne
  have hKC : K₁ ≤ Cz z := hM.K₁_le
  have hK₂C : K₂ ≤ Cz z := hM.K₂_le
  have hSC : S ≤ Cz z := hM.S_syl.1
  have hXC : X ≤ Cz z := sup_le (sup_le hKC hK₂C) hSC
  let t0 : ↥X := ⟨t, htX⟩
  let w0 : ↥X := ⟨w, hwX⟩
  let z0 : ↥X := ⟨z, hzX⟩
  have ht0 : t0 * t0 = 1 := Subtype.ext htt
  have hw0 : w0 * w0 = 1 := Subtype.ext hww
  have hswK : swapSub K₁ t = K₂ := Subgroup.ext (fun x => (hC.mem_K₂_iff x).symm)
  have hA₂ : swapSub (imgT π K₁) (π t0) = imgT π K₂ := by
    rw [imgT_swap π hπ K₁ htX htt, hswK]
  have hτ : π t0 * π t0 = 1 := by
    rw [← map_mul, ht0, map_one]
  have hω : π w0 * π w0 = 1 := by
    rw [← map_mul, hw0, map_one]
  have hτω : π t0 * π w0 = π w0 * π t0 := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext htw
  have hwN : w ∈ normalizer (K₁ : Set G) := by
    have : w ∈ S1 S K₁ := by
      rw [hS1]
      exact mem_sup_right (mem_zpowers w)
    exact this.2
  have hωA : ∀ a ∈ imgT π K₁, π w0 * a * (π w0)⁻¹ ∈ imgT π K₁ := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := (mem_imgT π).1 ha
    refine (mem_imgT π).2 ⟨w0 * s * w0⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    show w * (s : G) * w⁻¹ ∈ K₁
    exact (Subgroup.mem_normalizer_iff.1 hwN s).1 hs
  have hωN : π w0 ∈ normalizer ((imgT π K₁ : Subgroup (↥X ⧸ N₀)) : Set (↥X ⧸ N₀)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨hωA a, fun ha => ?_⟩
    have h1 := hωA _ ha
    have e : π w0 * (π w0 * a * (π w0)⁻¹) * (π w0)⁻¹ = a := by
      calc π w0 * (π w0 * a * (π w0)⁻¹) * (π w0)⁻¹ =
          (π w0 * π w0) * a * (π w0 * π w0)⁻¹ := by group
        _ = a := by rw [hω]; group
    rw [e] at h1
    exact h1
  have hbr : ∀ a ∈ K₁, ∀ b ∈ K₂, ⁅b, a⁆ ∈ Oz z := fun a ha b hb =>
    pPrimeCoreOf_le_Oz hpc₂ ((hM.cs₂ ha).2.2 b hb)
  have hcomm : ∀ a ∈ imgT π K₁, ∀ b ∈ swapSub (imgT π K₁) (π t0), a * b = b * a := by
    intro a ha b hb
    rw [hA₂] at hb
    obtain ⟨s₁, hs₁, rfl⟩ := (mem_imgT π).1 ha
    obtain ⟨s₂, hs₂, rfl⟩ := (mem_imgT π).1 hb
    rw [← map_mul, ← map_mul]
    show (QuotientGroup.mk (s₁ * s₂) : ↥X ⧸ N₀) = QuotientGroup.mk (s₂ * s₁)
    rw [QuotientGroup.eq]
    show (((s₁ * s₂)⁻¹ * (s₂ * s₁) : ↥X) : G) ∈ Oz z
    have h1 := hbr (s₁ : G)⁻¹ (K₁.inv_mem hs₁) (s₂ : G)⁻¹ (K₂.inv_mem hs₂)
    have e : (((s₁ * s₂)⁻¹ * (s₂ * s₁) : ↥X) : G) = ⁅(s₂ : G)⁻¹, (s₁ : G)⁻¹⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h1
  have hzC1 : ∀ s ∈ K₁, (s : G) * z = z * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.1 (hKC hs)
  have hζ₁ : π z0 ∈ imgT π K₁ := (mem_imgT π).2 ⟨z0, hzK₁, rfl⟩
  have hζ₂ : π z0 ∈ swapSub (imgT π K₁) (π t0) := by
    rw [hA₂]
    exact (mem_imgT π).2 ⟨z0, hzK₂, rfl⟩
  have hζc : ∀ a ∈ imgT π K₁, a * π z0 = π z0 * a := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := (mem_imgT π).1 ha
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzC1 s hs)
  have hζ1 : π z0 ≠ 1 := by
    intro h
    have hzO : z ∈ Oz z := (hπker z0).1 h
    exact hz1 (eq_one_of_sq_eq_one_of_odd card_Oz_odd hzO hz2)
  let ρ₁ : ↥K₁ →* ↥(imgT π K₁) :=
    (π.subgroupMap (K₁.subgroupOf X)).comp (Subgroup.subgroupOfEquivOfLe hK₁X).symm.toMonoidHom
  have hρ₁ : ∀ k : ↥K₁, (((ρ₁ k : ↥(imgT π K₁)) : ↥X ⧸ N₀)) = π ⟨(k : G), hK₁X k.2⟩ := fun k => rfl
  have hρ₁surj : Function.Surjective ρ₁ :=
    (MonoidHom.subgroupMap_surjective π (K₁.subgroupOf X)).comp
      (Subgroup.subgroupOfEquivOfLe hK₁X).symm.surjective
  have hρker : ρ₁.ker = pPrimeCore 2 ↥K₁ := by
    ext k
    rw [MonoidHom.mem_ker]
    have h1 : ρ₁ k = 1 ↔ π ⟨(k : G), hK₁X k.2⟩ = 1 := by
      constructor
      · intro h
        have := congrArg Subtype.val h
        exact this
      · intro h
        exact Subtype.ext h
    rw [h1, hπker]
    have h2 : k ∈ pPrimeCore 2 ↥K₁ ↔ (k : G) ∈ pPrimeCoreOf 2 K₁ := by
      rw [← hatMk_eq_one_iff K₁ k]
      exact (QuotientGroup.eq_one_iff k).symm
    rw [h2]
    constructor
    · intro h
      exact inf_Oz_le hpc₁ ⟨k.2, h⟩
    · intro h
      exact pPrimeCoreOf_le_Oz hpc₁ h
  let iA : Hat K₁ ≃* ↥(imgT π K₁) :=
    (QuotientGroup.quotientMulEquivOfEq hρker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ₁ hρ₁surj)
  have hiA : ∀ k : ↥K₁, iA (hatMk K₁ k) = ρ₁ k := fun k => rfl
  let e : ↥(imgT π K₁) ≃* SpecialLinearGroup (Fin 2) F := iA.symm.trans eG
  have hphi : MulAut.congr iA (phi K₁ w hwN) = TwoThin.conjAut hωN := by
    apply MulEquiv.ext
    intro a
    obtain ⟨y, rfl⟩ := iA.surjective a
    obtain ⟨k, rfl⟩ := hatMk_surjective K₁ y
    apply Subtype.ext
    show ((iA ((phi K₁ w hwN) (iA.symm (iA (hatMk K₁ k)))) : ↥(imgT π K₁)) : ↥X ⧸ N₀) =
      π w0 * ((iA (hatMk K₁ k) : ↥(imgT π K₁)) : ↥X ⧸ N₀) * (π w0)⁻¹
    rw [MulEquiv.symm_apply_apply, phi_mk, hiA, hiA, hρ₁, hρ₁]
    show π ⟨w * (k : G) * w⁻¹, _⟩ = π w0 * π ⟨(k : G), _⟩ * (π w0)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hout : π w0 ≠ 1 → TwoThin.conjAut hωN ∉ innOf ↥(imgT π K₁) ∧
      (gammaOf hodd h3 (MulAut.congr e (TwoThin.conjAut hωN))).right = 1 := by
    intro hω1
    have hw1 : w ≠ 1 := fun h => hω1 (by
      have : w0 = 1 := Subtype.ext h
      rw [this, map_one])
    obtain ⟨hin, hf⟩ := phi_w_facts h44 hII hC hconcl hw1 (A := K₁) (Or.inl rfl) hodd h3 eG hwN
    refine ⟨?_, ?_⟩
    · intro hα
      apply hin
      have : phi K₁ w hwN = MulAut.congr iA.symm (TwoThin.conjAut hωN) := by
        rw [← hphi]
        apply MulEquiv.ext
        intro x
        simp
      rw [this]
      obtain ⟨a, ha⟩ := hα
      refine ⟨iA.symm a, ?_⟩
      rw [← ha, mulAut_congr_conj]
    · have : MulAut.congr e (TwoThin.conjAut hωN) = MulAut.congr eG (phi K₁ w hwN) := by
        rw [← hphi]
        apply MulEquiv.ext
        intro x
        simp [e]
      rw [this]
      exact hf
  have hP₁ : IsSylowOf 2 (imgT π (Pof S K₁)) (imgT π K₁) := by
    obtain ⟨P, hP⟩ := std4_exists_sylow_P hstd (Or.inl rfl : K₁ = K₁ ∨ K₁ = K₂)
    refine ⟨P.mapSurjective hρ₁surj, ?_⟩
    ext a
    rw [Sylow.coe_mapSurjective, mem_imgT π]
    constructor
    · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
      have hkP : (k : G) ∈ S ⊓ K₁ := by
        rw [← hP]
        exact ⟨k, hk, rfl⟩
      exact ⟨⟨(k : G), hK₁X k.2⟩, hkP, (hρ₁ k).symm⟩
    · rintro ⟨s, hs, rfl⟩
      have hs' : (s : G) ∈ (P : Subgroup ↥K₁).map K₁.subtype := by
        rw [hP]
        exact hs
      obtain ⟨k, hk, hks⟩ := hs'
      refine ⟨ρ₁ k, ⟨k, hk, rfl⟩, ?_⟩
      show ((ρ₁ k : ↥(imgT π K₁)) : ↥X ⧸ N₀) = π s
      rw [hρ₁]
      congr 1
      exact Subtype.ext hks
  have hωP : ∀ x ∈ imgT π (Pof S K₁), π w0 * x * (π w0)⁻¹ ∈ imgT π (Pof S K₁) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := (mem_imgT π).1 hx
    refine (mem_imgT π).2 ⟨w0 * s * w0⁻¹, ⟨?_, ?_⟩, by rw [map_mul, map_mul, map_inv]⟩
    · exact S.mul_mem (S.mul_mem hwS hs.1) (S.inv_mem hwS)
    · exact (Subgroup.mem_normalizer_iff.1 hwN s).1 hs.2
  have hKgN : X ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := fun x hx =>
    M.mem_normalizer_of_both (fun y hy => hM.C_norm_K (hXC hx) hy)
      (fun y hy => hM.C_norm_K' (hXC hx) hy)
  have hKgX : K₁ ⊔ K₂ ≤ X := le_sup_left
  have hKgnormal : ((K₁ ⊔ K₂).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKgX).2 hKgN
  have hS'p : IsPGroup 2 ↥(S.subgroupOf X) := hM.S_pgroup.comap_subtype (K := X)
  have htop : (⊤ : Subgroup ↥X) = (K₁ ⊔ K₂).subgroupOf X ⊔ S.subgroupOf X := by
    rw [← Subgroup.subgroupOf_sup hKgX hSX, ← hXdef]
    exact (Subgroup.subgroupOf_self X).symm
  have hOK : ∀ x : ↥X, (x : G) ∈ Oz z → (x : G) ∈ K₁ ⊔ K₂ := by
    intro x hx
    have hodd' : Odd (orderOf x) := by
      rw [← Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat card_Oz_odd (Subgroup.orderOf_dvd_natCard (Oz z) hx)
    have hxs : x ∈ (K₁ ⊔ K₂).subgroupOf X ⊔ S.subgroupOf X := htop ▸ Subgroup.mem_top x
    exact mem_of_odd_of_mem_sup hS'p hxs hodd'
  have hPz : Pz S z = S ⊓ (K₁ ⊔ K₂) := CFSG.GH74.GLS.Stage1.Thm3.Sec4.Pz_eq hstd
  have hYS : Ysub t w ≤ S := by
    calc Ysub t w ≤ Pz S z ⊔ Ysub t w := le_sup_right
      _ = S := hSPY.symm
  have hKY : ∀ y ∈ Ysub t w, y ∈ K₁ ⊔ K₂ → y = 1 := by
    intro y hy hyK
    have : y ∈ Pz S z ⊓ Ysub t w := ⟨by rw [hPz]; exact ⟨hYS hy, hyK⟩, hy⟩
    rw [hPY] at this
    exact Subgroup.mem_bot.1 this
  have htX' : zpowers t ≤ X := zpowers_le.2 htX
  have hwX' : zpowers w ≤ X := zpowers_le.2 hwX
  have hYX : Ysub t w ≤ X := hYS.trans hSX
  have hY : zpowers (π t0) ⊔ zpowers (π w0) = imgT π (Ysub t w) := by
    rw [Ysub, imgT_sup π htX' hwX', imgT_zpowers π htX, imgT_zpowers π hwX]
  have hBY : (imgT π K₁ ⊔ swapSub (imgT π K₁) (π t0)) ⊓ (zpowers (π t0) ⊔ zpowers (π w0)) = ⊥ := by
    rw [hA₂, ← imgT_sup π hK₁X hK₂X, hY]
    refine eq_bot_iff.2 (fun h hh => ?_)
    obtain ⟨a, haK, hah⟩ := (mem_imgT π).1 hh.1
    obtain ⟨b, hbY, hbh⟩ := (mem_imgT π).1 hh.2
    have h1 : π (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hah, hbh, inv_mul_cancel]
    have h2 : ((a⁻¹ * b : ↥X) : G) ∈ Oz z := (hπker _).1 h1
    have h3' : ((a⁻¹ * b : ↥X) : G) ∈ K₁ ⊔ K₂ := hOK _ h2
    have h4 : (b : G) ∈ K₁ ⊔ K₂ := by
      have : (b : G) = (a : G) * ((a⁻¹ * b : ↥X) : G) := by
        simp
      rw [this]
      exact mul_mem haK h3'
    have h5 : (b : G) = 1 := hKY _ hbY h4
    have h6 : b = 1 := Subtype.ext h5
    rw [← hbh, h6, map_one]
    exact Subgroup.one_mem _
  have hPzsup : Pz S z = Pof S K₁ ⊔ Pof S K₂ :=
    (CFSG.GH74.GLS.Stage1.Thm3.Sec4.Pz_eq hstd).trans (R2.Pm_eq_sup hM)
  have hP₁X : Pof S K₁ ≤ X := inf_le_left.trans hSX
  have hP₂X : Pof S K₂ ≤ X := inf_le_left.trans hSX
  have hPzX : Pz S z ≤ X := by
    rw [hPzsup]
    exact sup_le hP₁X hP₂X
  have hswP : swapSub (Pof S K₁) t = Pof S K₂ := by
    ext x
    rw [mem_swapSub]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, (hC.mem_K₂_iff x).2 h2⟩
      have h3' := S.mul_mem (S.mul_mem (S.inv_mem htS) h1) htS
      have e' : t⁻¹ * (t * x * t⁻¹) * t = x := by group
      rw [e'] at h3'
      exact h3'
    · rintro ⟨h1, h2⟩
      exact ⟨S.mul_mem (S.mul_mem htS h1) (S.inv_mem htS), (hC.mem_K₂_iff x).1 h2⟩
  have hPzK : Pz S z ≤ K₁ ⊔ K₂ := by
    rw [hPz]
    exact inf_le_right
  have hSsup : S = Pz S z ⊔ zpowers t ⊔ zpowers w := by
    rw [sup_assoc]
    exact hSPY
  have hXeq : K₁ ⊔ K₂ ⊔ zpowers t ⊔ zpowers w = X := by
    apply le_antisymm
    · exact sup_le (sup_le hKgX htX') hwX'
    · apply sup_le
      · exact le_sup_left.trans le_sup_left
      · calc S = Pz S z ⊔ zpowers t ⊔ zpowers w := hSsup
          _ ≤ K₁ ⊔ K₂ ⊔ zpowers t ⊔ zpowers w :=
            sup_le_sup_right (sup_le_sup_right hPzK _) _
  have hImgX : imgT π X = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨s, rfl⟩ := hπ a
    exact (mem_imgT π).2 ⟨s, s.2, rfl⟩
  refine ⟨⟨imgT π K₁, imgT π (Pof S K₁), π t0, π w0, π z0, e, TwoThin.conjAut hωN, hτ, hω, hτω,
    fun a => rfl, hcomm, hζ₁, hζ₂, hζc, hζ1, hP₁, hωP, hBY, hout⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have : s = t0 := Subtype.ext hs
    rw [this]
    rfl
  · intro s hs
    have : s = w0 := Subtype.ext hs
    rw [this]
    rfl
  · show (imgT π K₁ ⊔ swapSub (imgT π K₁) (π t0)) ⊔ zpowers (π t0) ⊔ zpowers (π w0) = ⊤
    rw [hA₂, ← imgT_sup π hK₁X hK₂X, ← imgT_zpowers π htX, ← imgT_zpowers π hwX,
      ← imgT_sup π hKgX htX', ← imgT_sup π (sup_le hKgX htX') hwX', hXeq, hImgX]
  · intro a
    show a ∈ imgT π (Pof S K₁) ⊔ swapSub (imgT π (Pof S K₁)) (π t0) ↔ _
    rw [imgT_swap π hπ (Pof S K₁) htX htt, hswP, ← imgT_sup π hP₁X hP₂X, ← hPzsup]
    exact mem_imgT π
  · intro a
    show a ∈ (imgT π (Pof S K₁) ⊔ swapSub (imgT π (Pof S K₁)) (π t0)) ⊔ zpowers (π t0) ⊔
      zpowers (π w0) ↔ _
    rw [imgT_swap π hπ (Pof S K₁) htX htt, hswP, ← imgT_sup π hP₁X hP₂X, ← hPzsup,
      ← imgT_zpowers π htX, ← imgT_zpowers π hwX, ← imgT_sup π hPzX htX',
      ← imgT_sup π (sup_le hPzX htX') hwX', ← hSsup]
    exact mem_imgT π

end Main

end CFSG.GH74.GLS.IVK.Lifted
