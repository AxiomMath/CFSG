module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrCE0
public import CFSG.GF2Type.Aschbacher1976Full.HSGL3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma isE_three_comm {A : Type} [Group A] (hA : IsE 3 A) : ∀ a b : A, a * b = b * a := by
  haveI : IsMulCommutative (⊤ : Subgroup A) := hA.1.1
  intro a b
  exact congrArg Subtype.val (mul_comm' (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup A))
    ⟨b, Subgroup.mem_top b⟩)

private lemma exists_ne_three {F : Type} [Finite F] (hcard : 4 ≤ Nat.card F) (x y z : F) :
    ∃ w : F, w ≠ x ∧ w ≠ y ∧ w ≠ z := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hcard' : 4 ≤ Fintype.card F := by rwa [Fintype.card_eq_nat_card]
  have h3 : ({x, y, z} : Finset F).card ≤ 3 := Finset.card_le_three
  have hsne : ({x, y, z} : Finset F) ≠ ⊤ := by
    intro h
    have hc : ({x, y, z} : Finset F).card = Fintype.card F := by rw [h]; simp
    omega
  obtain ⟨w, hw⟩ := SetLike.exists_not_mem_of_ne_top ({x, y, z} : Finset F) hsne
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  exact ⟨w, hw.1, hw.2.1, hw.2.2⟩

private def linearEquivToMulAut {F : Type} [CommGroup F] [Module (ZMod 2) (Additive F)]
    (E : Additive F ≃ₗ[ZMod 2] Additive F) : MulAut F where
  toFun x := (E (Additive.ofMul x)).toMul
  invFun x := (E.symm (Additive.ofMul x)).toMul
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp [ofMul_mul, toMul_add]

@[simp]
private lemma linearEquivToMulAut_apply {F : Type} [CommGroup F] [Module (ZMod 2) (Additive F)]
    (E : Additive F ≃ₗ[ZMod 2] Additive F) (x : F) :
    linearEquivToMulAut E x = (E (Additive.ofMul x)).toMul := rfl

private lemma exists_basis_pair {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (hfin : Module.finrank (ZMod 2) A = 3) {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) : ∃ B : Basis (Fin 3) (ZMod 2) A, B 0 = a ∧ B 1 = b := by
  have hli2 : LinearIndependent (ZMod 2) ![a, b] := by
    rw [LinearIndependent.pair_iff' ha]
    intro c
    have hc : c = 0 ∨ c = 1 := by
      have h : c.val = 0 ∨ c.val = 1 := by have := c.val_lt; omega
      rcases h with h | h
      · left; exact (ZMod.val_eq_zero c).mp h
      · right
        rw [← ZMod.natCast_zmod_val c, h]
        norm_num
    rcases hc with rfl | rfl
    · simpa using (Ne.symm hb)
    · simpa using hab
  have hproper : Submodule.span (ZMod 2) (Set.range ![a, b]) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have h1 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (Set.range ![a, b])) = 2 := by
      rw [finrank_span_eq_card hli2]; simp
    rw [htop] at h1
    have : Module.finrank (ZMod 2) A = 2 := by simpa using h1
    omega
  obtain ⟨c, -, hc⟩ := SetLike.exists_of_lt hproper
  have hli3 : LinearIndependent (ZMod 2) (Fin.snoc ![a, b] c) :=
    LinearIndependent.finSnoc hli2 hc
  have hcard : Fintype.card (Fin 3) = Module.finrank (ZMod 2) A := by simp [hfin]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli3 hcard, ?_, ?_⟩
  · simp
  · simp

private theorem mulAut_trans2 {F : Type} [Group F] (hF : IsE 3 F) {a b a' b' : F}
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (ha' : a' ≠ 1) (hb' : b' ≠ 1) (hab' : a' ≠ b') :
    ∃ α : MulAut F, α a = a' ∧ α b = b' := by
  have hcomm := isE_three_comm hF
  letI : CommGroup F := { ‹Group F› with mul_comm := hcomm }
  have h2 : ∀ x : F, x ^ 2 = 1 := fun x => hF.1.2 x trivial
  letI : Module (ZMod 2) (Additive F) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      rw [← toMul_eq_one, toMul_nsmul, h2]
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF.2]; norm_num)
  haveI : Fintype (Additive F) := Fintype.ofFinite (Additive F)
  have hcardV : Fintype.card (Additive F) = 8 := by
    rw [Fintype.card_eq_nat_card, ← Nat.card_congr Additive.ofMul, hF.2]
    norm_num
  have hfr := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive F)
  rw [hcardV, ZMod.card] at hfr
  have hfin : Module.finrank (ZMod 2) (Additive F) = 3 := by
    have h : (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive F) = 2 ^ 3 := by
      rw [← hfr]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
  have ha0 : Additive.ofMul a ≠ 0 := fun h => ha (ofMul_eq_zero.mp h)
  have hb0 : Additive.ofMul b ≠ 0 := fun h => hb (ofMul_eq_zero.mp h)
  have hab0 : Additive.ofMul a ≠ Additive.ofMul b :=
    fun h => hab (Additive.ofMul.injective h)
  obtain ⟨B, hB0, hB1⟩ := exists_basis_pair hfin ha0 hb0 hab0
  have ha0' : Additive.ofMul a' ≠ 0 := fun h => ha' (ofMul_eq_zero.mp h)
  have hb0' : Additive.ofMul b' ≠ 0 := fun h => hb' (ofMul_eq_zero.mp h)
  have hab0' : Additive.ofMul a' ≠ Additive.ofMul b' :=
    fun h => hab' (Additive.ofMul.injective h)
  obtain ⟨B', hB0', hB1'⟩ := exists_basis_pair hfin ha0' hb0' hab0'
  refine ⟨linearEquivToMulAut (B.equiv B' (Equiv.refl (Fin 3))), ?_, ?_⟩
  · rw [linearEquivToMulAut_apply, ← hB0, Basis.equiv_apply, Equiv.refl_apply, hB0']; rfl
  · rw [linearEquivToMulAut_apply, ← hB1, Basis.equiv_apply, Equiv.refl_apply, hB1']; rfl

private theorem mulAut_trans1 {F : Type} [Group F] (hF : IsE 3 F) {a a' : F}
    (ha : a ≠ 1) (ha' : a' ≠ 1) : ∃ α : MulAut F, α a = a' := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF.2]; norm_num)
  have hcard : 4 ≤ Nat.card F := by rw [hF.2]; norm_num
  obtain ⟨b, hb1, hba, -⟩ := exists_ne_three hcard 1 a 1
  obtain ⟨b', hb'1, hb'a', -⟩ := exists_ne_three hcard 1 a' 1
  obtain ⟨α, hα, -⟩ := mulAut_trans2 hF ha hb1 (Ne.symm hba) ha' hb'1 (Ne.symm hb'a')
  exact ⟨α, hα⟩

theorem y54_centIn_L_F {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    centIn L s.fr.F = s.fr.F := by
  have h : centIn L s.fr.F = zL L ⊔ s.fr.F := hH.hLF.fact18.2.2.2.1
  rw [h, f3_zL_eq_bot hH, bot_sup_eq]

theorem y54_card_N {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Nat.card ↥(normIn L s.fr.F) = 1344 := by
  have hFE : IsE 3 ↥s.fr.F := s3_isE3_F hH.hS hH.hZ hH.hOut s
  have hFL : s.fr.F ≤ L := (s3_F_le_A s).trans (s3_A_le_L s)
  have hFN : s.fr.F ≤ normIn L s.fr.F := le_inf hFL Subgroup.le_normalizer
  obtain ⟨hN, hP⟩ := hH.hLF.fact18.2.2.2.2.1
  letI := hN
  obtain ⟨e⟩ := hP
  have hquot : Nat.card
      (↥(normIn L s.fr.F) ⧸ (zL L ⊔ s.fr.F).subgroupOf (normIn L s.fr.F)) = 168 := by
    rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
    decide
  have hsle : zL L ⊔ s.fr.F ≤ normIn L s.fr.F := by
    rw [f3_zL_eq_bot hH, bot_sup_eq]
    exact hFN
  have hK : Nat.card ↥((zL L ⊔ s.fr.F).subgroupOf (normIn L s.fr.F)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsle).toEquiv, f3_zL_eq_bot hH, bot_sup_eq]
    simpa using hFE.2
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((zL L ⊔ s.fr.F).subgroupOf (normIn L s.fr.F))
  rw [hquot, hK] at h
  omega

theorem y54_aut_surj {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    (α : MulAut ↥s.fr.F) :
    ∃ n ∈ normIn L s.fr.F, ∀ f : ↥s.fr.F, ((α f : ↥s.fr.F) : G) = n * (f : G) * n⁻¹ := by
  have hFE : IsE 3 ↥s.fr.F := s3_isE3_F hH.hS hH.hZ hH.hOut s
  have hFL : s.fr.F ≤ L := (s3_F_le_A s).trans (s3_A_le_L s)
  have hFN : s.fr.F ≤ normIn L s.fr.F := le_inf hFL Subgroup.le_normalizer
  have hV : Nat.card ↥s.fr.F = 8 := by simpa using hFE.2
  have hcomm : ∀ a b : ↥s.fr.F, a * b = b * a := isE_three_comm hFE
  have hsq : ∀ v : ↥s.fr.F, v * v = 1 := fun v => by
    simpa [pow_two] using hFE.1.2 v (Subgroup.mem_top v)
  have hcardAut : Nat.card (MulAut ↥s.fr.F) = 168 :=
    CFSG.GF2Type.Aschbacher1976Full.HS.card_mulAut_eq_168 hV hcomm hsq
  haveI : Finite (MulAut ↥s.fr.F) :=
    Nat.finite_of_card_ne_zero (by rw [hcardAut]; norm_num)
  let ρ : ↥(normIn L s.fr.F) →* MulAut ↥s.fr.F :=
    (Subgroup.normalizerMonoidHom s.fr.F).comp (Subgroup.inclusion inf_le_right)
  have hρ : ∀ (n : ↥(normIn L s.fr.F)) (f : ↥s.fr.F),
      ((ρ n f : ↥s.fr.F) : G) = (n : G) * (f : G) * (n : G)⁻¹ := by
    intro n f
    simp only [ρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom]
    rfl
  have hker : ρ.ker = s.fr.F.subgroupOf (normIn L s.fr.F) := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hn
      have hcomm : ∀ f ∈ s.fr.F, (n : G) * f = f * (n : G) := by
        intro f hf
        have h1 : (n : G) * f * (n : G)⁻¹ = f := by
          have h2 : ((ρ n ⟨f, hf⟩ : ↥s.fr.F) : G) = f := by
            have h3 : ρ n ⟨f, hf⟩ = ⟨f, hf⟩ := by rw [hn]; rfl
            simpa using congrArg (fun x : ↥s.fr.F => (x : G)) h3
          rwa [hρ n ⟨f, hf⟩] at h2
        calc (n : G) * f = (n : G) * f * (n : G)⁻¹ * (n : G) := by group
          _ = f * (n : G) := by rw [h1]
      have hmem : (n : G) ∈ centIn L s.fr.F := by
        refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp n.2).1, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        exact (hcomm f hf).symm
      rwa [y54_centIn_L_F hH] at hmem
    · intro hn
      apply MulEquiv.ext
      intro f
      apply Subtype.ext
      rw [hρ n f]
      have hc : (n : G) * (f : G) = (f : G) * (n : G) :=
        congrArg Subtype.val (isE_three_comm hFE (⟨(n : G), hn⟩ : ↥s.fr.F) f)
      show (n : G) * (f : G) * (n : G)⁻¹ = (f : G)
      rw [hc]
      group
  have hcardker : Nat.card ↥ρ.ker = 8 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv]
    simpa using hFE.2
  have hrange : Nat.card ↥ρ.range = 168 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    have hq : Nat.card (↥(normIn L s.fr.F) ⧸ ρ.ker) = Nat.card ↥ρ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    rw [hq, hcardker, y54_card_N hH] at h
    omega
  have htop : ρ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hrange, hcardAut]
  obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp (by rw [htop]; exact Subgroup.mem_top α)
  exact ⟨n, n.2, fun f => by
    have hf : ρ n f = α f := by rw [hn]
    simpa [hf] using hρ n f⟩

theorem y54_trans1 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ a ∈ s.fr.F, ∀ a' ∈ s.fr.F, a ≠ 1 → a' ≠ 1 → ∃ n ∈ normIn L s.fr.F, n * a * n⁻¹ = a' := by
  have hFE : IsE 3 ↥s.fr.F := s3_isE3_F hH.hS hH.hZ hH.hOut s
  intro a ha a' ha' ha1 ha'1
  obtain ⟨α, hα⟩ := mulAut_trans1 hFE (a := ⟨a, ha⟩) (a' := ⟨a', ha'⟩)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => ha'1 (congrArg Subtype.val h))
  obtain ⟨n, hn, hconj⟩ := y54_aut_surj hH α
  exact ⟨n, hn, by
    have h := hconj ⟨a, ha⟩
    rw [hα] at h
    simpa using h.symm⟩

theorem y54_trans2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ a ∈ s.fr.F, ∀ b ∈ s.fr.F, ∀ a' ∈ s.fr.F, ∀ b' ∈ s.fr.F, a ≠ 1 → b ≠ 1 → a ≠ b → a' ≠ 1 →
      b' ≠ 1 → a' ≠ b' → ∃ n ∈ normIn L s.fr.F, n * a * n⁻¹ = a' ∧ n * b * n⁻¹ = b' := by
  have hFE : IsE 3 ↥s.fr.F := s3_isE3_F hH.hS hH.hZ hH.hOut s
  intro a ha b hb a' ha' b' hb' ha1 hb1 hab ha'1 hb'1 hab'
  obtain ⟨α, hαa, hαb⟩ := mulAut_trans2 hFE (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    (a' := ⟨a', ha'⟩) (b' := ⟨b', hb'⟩)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
    (fun h => hab (congrArg Subtype.val h)) (fun h => ha'1 (congrArg Subtype.val h))
    (fun h => hb'1 (congrArg Subtype.val h)) (fun h => hab' (congrArg Subtype.val h))
  obtain ⟨n, hn, hconj⟩ := y54_aut_surj hH α
  refine ⟨n, hn, ?_, ?_⟩
  · have h := hconj ⟨a, ha⟩
    rw [hαa] at h
    simpa using h.symm
  · have h := hconj ⟨b, hb⟩
    rw [hαb] at h
    simpa using h.symm

end CFSG.OddStandard.HigherRank.YamadaG23
