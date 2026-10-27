module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54GL
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Card
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56P

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma mul_comm_of_isE {F : Type} [Group F] (hF : IsE 3 F) : ∀ a b : F, a * b = b * a := by
  haveI : IsMulCommutative (⊤ : Subgroup F) := hF.1.1
  exact fun a b => congrArg Subtype.val (mul_comm' (M := (⊤ : Subgroup F))
    ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩)

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

private lemma linIndep_pair {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] {a b : A}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) : LinearIndependent (ZMod 2) ![a, b] := by
  rw [LinearIndependent.pair_iff' ha]
  intro u
  have hu : u = 0 ∨ u = 1 := by
    have h : u.val = 0 ∨ u.val = 1 := by have := u.val_lt; omega
    rcases h with h | h
    · left; exact (ZMod.val_eq_zero u).mp h
    · right; rw [← ZMod.natCast_zmod_val u, h]; norm_num
  rcases hu with rfl | rfl
  · simpa using (Ne.symm hb)
  · simpa using hab

private lemma notMem_span_pair {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] {a b c : A}
    (hc : c ≠ 0) (hac : c ≠ a) (hbc : c ≠ b) (habc : c ≠ a + b) :
    c ∉ Submodule.span (ZMod 2) (Set.range ![a, b]) := by
  have hr : Set.range (![a, b] : Fin 2 → A) = ({a, b} : Set A) := by
    ext x; simp [Fin.exists_fin_two, or_comm, or_left_comm, or_assoc]
  rw [hr, Submodule.mem_span_pair]
  rintro ⟨u, v, huv⟩
  have h01 : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by
    intro w
    have h : w.val = 0 ∨ w.val = 1 := by have := w.val_lt; omega
    rcases h with h | h
    · left; exact (ZMod.val_eq_zero w).mp h
    · right; rw [← ZMod.natCast_zmod_val w, h]; norm_num
  rcases h01 u with rfl | rfl <;> rcases h01 v with rfl | rfl <;>
    simp only [zero_smul, one_smul, zero_add, add_zero] at huv
  · exact hc huv.symm
  · exact hbc huv.symm
  · exact hac huv.symm
  · exact habc huv.symm

private lemma exists_basis3 {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (hfin : Module.finrank (ZMod 2) A = 3) {a b c : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hnot : c ∉ Submodule.span (ZMod 2) (Set.range ![a, b])) :
    ∃ B : Basis (Fin 3) (ZMod 2) A, B 0 = a ∧ B 1 = b ∧ B 2 = c := by
  have hli3 : LinearIndependent (ZMod 2) ![a, b, c] := by
    simpa using LinearIndependent.finSnoc (v := ![a, b]) (x := c) (linIndep_pair ha hb hab) hnot
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli3 (by simp [hfin]), by simp, by simp, by simp⟩

private theorem mulAut_triple {F : Type} [Group F] (hF : IsE 3 F)
    {a b c a' b' c' : F} (ha : a ≠ 1) (hb : b ≠ 1) (hc : c ≠ 1)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (habc : a * b ≠ c)
    (ha' : a' ≠ 1) (hb' : b' ≠ 1) (hc' : c' ≠ 1)
    (hab' : a' ≠ b') (hac' : a' ≠ c') (hbc' : b' ≠ c') (habc' : a' * b' ≠ c') :
    ∃ α : MulAut F, α a = a' ∧ α b = b' ∧ α c = c' := by
  have hcomm := mul_comm_of_isE hF
  letI : CommGroup F := { ‹Group F› with mul_comm := hcomm }
  have h2 : ∀ x : F, x ^ 2 = 1 := fun x => hF.1.2 x trivial
  letI : Module (ZMod 2) (Additive F) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [← toMul_eq_one, toMul_nsmul, h2]
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF.2]; norm_num)
  haveI : Fintype (Additive F) := Fintype.ofFinite (Additive F)
  have hcardV : Fintype.card (Additive F) = 8 := by
    rw [Fintype.card_eq_nat_card, ← Nat.card_congr Additive.ofMul, hF.2]; norm_num
  have hfr := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive F)
  rw [hcardV, ZMod.card] at hfr
  have hfin : Module.finrank (ZMod 2) (Additive F) = 3 := by
    have h : (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive F) = 2 ^ 3 := by rw [← hfr]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
  have hspan : ∀ {x y z : F}, x ≠ 1 → y ≠ 1 → z ≠ 1 → x ≠ y → x ≠ z → y ≠ z → x * y ≠ z →
      Additive.ofMul z ∉ Submodule.span (ZMod 2)
        (Set.range ![Additive.ofMul x, Additive.ofMul y]) :=
    fun {x y z} hx hy hz hxy hxz hyz hxyz =>
      notMem_span_pair (a := Additive.ofMul x) (b := Additive.ofMul y)
        (fun h => hz (ofMul_eq_zero.mp h)) (fun h => hxz (Additive.ofMul.injective h).symm)
        (fun h => hyz (Additive.ofMul.injective h).symm)
        (fun h => hxyz (Additive.ofMul.injective (ofMul_mul x y |>.trans h.symm)))
  obtain ⟨B, hB0, hB1, hB2⟩ := exists_basis3 hfin (a := Additive.ofMul a) (b := Additive.ofMul b)
    (c := Additive.ofMul c) (fun h => ha (ofMul_eq_zero.mp h))
    (fun h => hb (ofMul_eq_zero.mp h)) (fun h => hab (Additive.ofMul.injective h))
    (hspan ha hb hc hab hac hbc habc)
  obtain ⟨B', hB0', hB1', hB2'⟩ := exists_basis3 hfin (a := Additive.ofMul a')
    (b := Additive.ofMul b') (c := Additive.ofMul c') (fun h => ha' (ofMul_eq_zero.mp h))
    (fun h => hb' (ofMul_eq_zero.mp h)) (fun h => hab' (Additive.ofMul.injective h))
    (hspan ha' hb' hc' hab' hac' hbc' habc')
  refine ⟨linearEquivToMulAut (B.equiv B' (Equiv.refl (Fin 3))), ?_, ?_, ?_⟩
  · rw [linearEquivToMulAut_apply, ← hB0, Basis.equiv_apply, Equiv.refl_apply, hB0']; rfl
  · rw [linearEquivToMulAut_apply, ← hB1, Basis.equiv_apply, Equiv.refl_apply, hB1']; rfl
  · rw [linearEquivToMulAut_apply, ← hB2, Basis.equiv_apply, Equiv.refl_apply, hB2']; rfl

private theorem isCoatom_subgroupOf_of_isMaximalIn {Γ : Type} [Group Γ] {V M : Subgroup Γ}
    (h : IsMaximalIn V M) : IsCoatom (M.subgroupOf V) := by
  rw [isCoatom_iff_ge_of_le]
  refine ⟨?_, ?_⟩
  · intro htop
    apply h.1.2
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥V) ∈ M.subgroupOf V := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp hmem
  · intro K hKne hMK
    by_contra hKM
    obtain ⟨k, hkK, hkM⟩ := SetLike.not_le_iff_exists.mp hKM
    let N : Subgroup Γ := K.map V.subtype
    have hNV : N ≤ V := by rintro x ⟨y, -, rfl⟩; exact y.2
    have hMN : M ≤ N := by
      intro m hm
      exact Subgroup.mem_map.mpr ⟨⟨m, h.1.1 hm⟩, hMK (Subgroup.mem_subgroupOf.mpr hm), rfl⟩
    have hkN : ((k : ↥V) : Γ) ∈ N := Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩
    have hkM' : ((k : ↥V) : Γ) ∉ M := fun hm => hkM (Subgroup.mem_subgroupOf.mpr hm)
    have hlt : M < N := lt_of_le_of_ne hMN fun heq => hkM' (heq ▸ hkN)
    have hKN : N.subgroupOf V = K := by
      rw [← Subgroup.comap_subtype]
      exact K.comap_map_eq_self_of_injective Subtype.coe_injective
    exact hKne (by rw [← hKN, h.2 N hlt hNV, Subgroup.subgroupOf_self])

private def y56Conj (s : Setting3 G L) : ↥(normIn L s.fr.E) →* MulAut ↥s.fr.E :=
  (Subgroup.normalizerMonoidHom s.fr.E).comp (Subgroup.inclusion inf_le_right)

private lemma y56Conj_apply (s : Setting3 G L) (n : ↥(normIn L s.fr.E)) (f : ↥s.fr.E) :
    ((y56Conj s n f : ↥s.fr.E) : G) = (n : G) * (f : G) * (n : G)⁻¹ := by
  simp only [y56Conj, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom]
  rfl

private lemma y56_h0_mem_normalizer_E {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.h₀ ∈ Subgroup.normalizer (s.fr.E : Set G) := by
  have hE : IsE 3 ↥s.fr.E := y56_E_isE3 hH
  have hAT1 : s.fr.A ≤ e.T₁ := hH.h32.1.1
  have hSN : s.fr.S ≤ Subgroup.normalizer (s.fr.A : Set G) :=
    hH.h32.2.1.1.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hAT1).mp hH.h32.1.2)
  have hBmax : IsMaximalIn s.fr.S s.fr.B := hH.hLF.fact14.2.2.1.2.2.1
  have hcoatom : IsCoatom (s.fr.B.subgroupOf s.fr.S) := isCoatom_subgroupOf_of_isMaximalIn hBmax
  haveI : Group.IsNilpotent ↥s.fr.S := (s3_isPGroup_S s).isNilpotent
  have hBnorm : (s.fr.B.subgroupOf s.fr.S).Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom (s.fr.B.subgroupOf s.fr.S)
      (Group.normalizerCondition_of_isNilpotent (G := ↥s.fr.S)) hcoatom
  have hBN : s.fr.S ≤ Subgroup.normalizer (s.fr.B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (s3_B_le_S s)).mp hBnorm
  have hFN : s.fr.S ≤ Subgroup.normalizer (s.fr.F : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer ((s3_F_le_A s).trans (s3_A_le_S s))).mp
      hH.hLF.fact14.2.2.2.2.1.1.1
  have h0S : s.fr.h₀ ∈ s.fr.S := Subgroup.subset_closure (by simp)
  have h0NA : s.fr.h₀ ∈ Subgroup.normalizer (s.fr.A : Set G) := hSN h0S
  have h0NB : s.fr.h₀ ∈ Subgroup.normalizer (s.fr.B : Set G) := hBN h0S
  have h0NAB : s.fr.h₀ ∈ Subgroup.normalizer ((s.fr.A ⊓ s.fr.B : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    exact fun x => ⟨fun hx => Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp h0NA x).mp (Subgroup.mem_inf.mp hx).1,
         (Subgroup.mem_normalizer_iff.mp h0NB x).mp (Subgroup.mem_inf.mp hx).2⟩,
      fun hx => Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp h0NA x).mpr (Subgroup.mem_inf.mp hx).1,
         (Subgroup.mem_normalizer_iff.mp h0NB x).mpr (Subgroup.mem_inf.mp hx).2⟩⟩
  have hset : maxElemAbelian (s.fr.A ⊓ s.fr.B) = {s.fr.E, s.fr.F} :=
    hH.hLF.fact14.2.2.2.1.2.2.1
  have hEmem : s.fr.E ∈ maxElemAbelian (s.fr.A ⊓ s.fr.B) := by rw [hset]; simp
  have hT : (s.fr.A ⊓ s.fr.B).map (MulAut.conj s.fr.h₀).toMonoidHom = s.fr.A ⊓ s.fr.B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp h0NAB
  have hconjmem : conjSub s.fr.h₀ s.fr.E ∈ maxElemAbelian (s.fr.A ⊓ s.fr.B) := by
    have h := maxElemAbelian_map (f := (MulAut.conj s.fr.h₀).toMonoidHom)
      (MulAut.conj s.fr.h₀).injective (s.fr.A ⊓ s.fr.B)
    rw [hT] at h
    have hmem := Set.mem_image_of_mem (Subgroup.map (MulAut.conj s.fr.h₀).toMonoidHom) hEmem
    rw [← h] at hmem
    exact hmem
  have hpair : conjSub s.fr.h₀ s.fr.E = s.fr.E ∨ conjSub s.fr.h₀ s.fr.E = s.fr.F := by
    rw [hset] at hconjmem; simpa using hconjmem
  have hFfix : conjSub s.fr.h₀ s.fr.F = s.fr.F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hFN h0S)
  have hEneF : s.fr.E ≠ s.fr.F := by
    intro h
    have hEF : s.fr.E ⊓ s.fr.F = cen s.fr.B := hH.hLF.fact14.2.2.2.1.2.2.2
    have h1 : s.fr.E = cen s.fr.B := by rw [← hEF, h, inf_idem]
    have hcard : Nat.card ↥s.fr.E = Nat.card ↥(cen s.fr.B) :=
      congrArg (fun X : Subgroup G => Nat.card ↥X) h1
    have h8 : Nat.card ↥s.fr.E = 8 := hE.2
    have h4 : Nat.card ↥(cen s.fr.B) = 4 := by
      have h := (f3_V_isE2 hH).2; norm_num at h; exact h
    omega
  have hEfix : conjSub s.fr.h₀ s.fr.E = s.fr.E := by
    rcases hpair with h | h
    · exact h
    · exact absurd (Subgroup.map_injective (MulAut.conj s.fr.h₀).injective (h.trans hFfix.symm))
        hEneF
  simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEfix

private lemma y56_mem_Z_iff {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {u : G} :
    u ∈ s.fr.Z ↔ u = 1 ∨ u = s.fr.z := by
  classical
  rw [SFrame.Z, mem_zpowers_iff_mem_range_orderOf, s3_z_order s (lfactsA_of_setting hH.hS hH.hZ s)]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by simp⟩
    · exact ⟨1, by norm_num, by simp⟩

theorem y56_centIn_L_E {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    centIn L s.fr.E = s.fr.E := by
  rw [hH.hLF.fact18.2.2.1.1, f3_zL_eq_bot hH, bot_sup_eq]

theorem y56_A_le_NE {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.A ≤ normIn L s.fr.E := by
  have hA : LFactsA s := lfactsA_of_setting hH.hS hH.hZ s
  refine le_inf (s3_A_le_L s) fun a ha => ?_
  change a ∈ Subgroup.normalizer (s.fr.E : Set G)
  rw [Subgroup.mem_normalizer_iff]
  refine fun f => ⟨fun hf => ?_, fun hf => ?_⟩
  · have heq : a * f * a⁻¹ = ⁅a, f⁆ * f := by rw [commutatorElement_def]; group
    rw [heq]
    exact s.fr.E.mul_mem (s3_Z_le_E s (hA.comm_A a ha f (s3_E_le_A s hf))) hf
  · have hcomm : ⁅a⁻¹, a * f * a⁻¹⁆ ∈ s.fr.Z :=
      hA.comm_A a⁻¹ (s.fr.A.inv_mem ha) (a * f * a⁻¹) (s3_E_le_A s hf)
    have heq : a⁻¹ * (a * f * a⁻¹) * a = ⁅a⁻¹, a * f * a⁻¹⁆ * (a * f * a⁻¹) := by
      rw [commutatorElement_def]; group
    have hfeq : f = a⁻¹ * (a * f * a⁻¹) * a := by group
    rw [hfeq, heq]
    exact s.fr.E.mul_mem (s3_Z_le_E s hcomm) hf

theorem y56_S_le_NE {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.S ≤ normIn L s.fr.E := by
  refine le_inf (s3_S_le_L s) ?_
  change closure ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂, s.fr.h₀} : Set G) ≤
    Subgroup.normalizer (s.fr.E : Set G)
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact (Subgroup.mem_inf.mp (y56_A_le_NE hH (s3_a₁_mem_A s))).2
  · exact (Subgroup.mem_inf.mp (y56_A_le_NE hH (s3_b₁_mem_A s))).2
  · exact (Subgroup.mem_inf.mp (y56_A_le_NE hH (s3_a₂_mem_A s))).2
  · exact (Subgroup.mem_inf.mp (y56_A_le_NE hH (s3_b₂_mem_A s))).2
  · exact y56_h0_mem_normalizer_E hH

theorem y56_B_le_NE {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.B ≤ normIn L s.fr.E :=
  (s3_B_le_S s).trans (y56_S_le_NE hH)

theorem y56_NE_le_Cz {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ n ∈ normIn L s.fr.E, n * s.fr.z * n⁻¹ = s.fr.z := by
  intro n hn
  have hnA : n ∈ normIn L s.fr.A := hH.hLF.fact18.2.2.1.2.1 hn
  rw [hH.hLF.fact18.1.1] at hnA
  have hc : n * s.fr.z = s.fr.z * n :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hnA).2 s.fr.z (by simp)).symm
  calc n * s.fr.z * n⁻¹ = s.fr.z * n * n⁻¹ := by rw [hc]
    _ = s.fr.z := by group

theorem y56_card_A {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Nat.card ↥s.fr.A = 32 :=
  (lfactsA_of_setting hH.hS hH.hZ s).card_A

theorem y56_card_NE {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Nat.card ↥(normIn L s.fr.E) = 192 := by
  have hA : s.fr.A ≤ normIn L s.fr.E := y56_A_le_NE hH
  obtain ⟨hN, hP⟩ := hH.hLF.fact18.2.2.1.2.2.1
  letI := hN
  obtain ⟨e⟩ := hP
  have hquot : Nat.card
      (↥(normIn L s.fr.E) ⧸ (zL L ⊔ s.fr.A).subgroupOf (normIn L s.fr.E)) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]; decide
  have hsle : zL L ⊔ s.fr.A ≤ normIn L s.fr.E := by rw [f3_zL_eq_bot hH, bot_sup_eq]; exact hA
  have hK : Nat.card ↥((zL L ⊔ s.fr.A).subgroupOf (normIn L s.fr.E)) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsle).toEquiv, f3_zL_eq_bot hH, bot_sup_eq]
    exact y56_card_A hH
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((zL L ⊔ s.fr.A).subgroupOf (normIn L s.fr.E))
  rw [hquot, hK] at h
  omega

theorem y56_NE_trans {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ u ∈ s.fr.E, u ≠ 1 → u ≠ s.fr.z → ∀ v ∈ s.fr.E, v ≠ 1 → v ≠ s.fr.z →
      ∃ n ∈ normIn L s.fr.E, n * u * n⁻¹ = v := by
  intro u hu hu1 huz v hv hv1 hvz
  exact hH.hLF.fact18.2.2.1.2.2.2.1 u hu
    (fun h => ((y56_mem_Z_iff hH).mp h).elim hu1 huz) v hv
    (fun h => ((y56_mem_Z_iff hH).mp h).elim hv1 hvz)

theorem y56_aut_surj {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    (α : MulAut ↥s.fr.E) (hα : ∀ f : ↥s.fr.E, (f : G) = s.fr.z → ((α f : ↥s.fr.E) : G) = s.fr.z) :
    ∃ n ∈ normIn L s.fr.E, ∀ f : ↥s.fr.E, ((α f : ↥s.fr.E) : G) = n * (f : G) * n⁻¹ := by
  classical
  have hE : IsE 3 ↥s.fr.E := y56_E_isE3 hH
  have hEN : s.fr.E ≤ normIn L s.fr.E := le_inf (y56_E_le_L s) Subgroup.le_normalizer
  let ρ := y56Conj s
  have hρ := y56Conj_apply s
  have hker : ρ.ker = s.fr.E.subgroupOf (normIn L s.fr.E) := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · have hcomm : ∀ f ∈ s.fr.E, (n : G) * f = f * (n : G) := by
        intro f hf
        have h1 : (n : G) * f * (n : G)⁻¹ = f := by
          have h2 : ((ρ n ⟨f, hf⟩ : ↥s.fr.E) : G) = f := by
            simpa using congrArg (fun x : ↥s.fr.E => (x : G))
              (show ρ n ⟨f, hf⟩ = ⟨f, hf⟩ by rw [hn]; rfl)
          rwa [hρ n ⟨f, hf⟩] at h2
        calc (n : G) * f = (n : G) * f * (n : G)⁻¹ * (n : G) := by group
          _ = f * (n : G) := by rw [h1]
      have hmem : (n : G) ∈ centIn L s.fr.E := by
        refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp n.2).1, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        exact fun f hf => (hcomm f hf).symm
      rwa [y56_centIn_L_E hH] at hmem
    · apply MulEquiv.ext
      intro f
      apply Subtype.ext
      rw [hρ n f]
      have hc : (n : G) * (f : G) = (f : G) * (n : G) := y56_E_comm hH (n : G) hn (f : G) f.2
      show (n : G) * (f : G) * (n : G)⁻¹ = (f : G)
      rw [hc]; group
  have hcardker : Nat.card ↥ρ.ker = 8 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv]; simpa using hE.2
  have hrange : Nat.card ↥ρ.range = 24 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    have hq : Nat.card (↥(normIn L s.fr.E) ⧸ ρ.ker) = Nat.card ↥ρ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    rw [hq, hcardker, y56_card_NE hH] at h
    omega
  let zE : ↥s.fr.E := ⟨s.fr.z, y56_z_mem_E hH⟩
  have hzE1 : zE ≠ 1 := fun h => (y56_v0 hH).2.2.2.1 (Subtype.ext_iff.mp h)
  have hcardOrbit : Nat.card ↥(MulAction.orbit (MulAut ↥s.fr.E) zE) = 7 := by
    have horbit : MulAction.orbit (MulAut ↥s.fr.E) zE = {x : ↥s.fr.E | x ≠ 1} := by
      ext x
      rw [MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨β, rfl⟩
        intro h
        exact hzE1 (by simpa [MulAut.smul_def] using congrArg β.symm h)
      · intro hx
        obtain ⟨β, hβ⟩ := gl_trans1 hE (a := zE) (a' := x) hzE1 hx
        exact ⟨β, by rwa [MulAut.smul_def]⟩
    haveI : Fintype ↥s.fr.E := Fintype.ofFinite _
    rw [Nat.card_coe_set_eq, horbit]
    have hset : ({x : ↥s.fr.E | x ≠ 1} : Set ↥s.fr.E) = Set.univ \ ({1} : Set ↥s.fr.E) := by
      ext x; simp
    rw [hset, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ (1 : ↥s.fr.E)), Set.ncard_univ,
      hE.2]
    norm_num
  have hcardStab : Nat.card (MulAction.stabilizer (MulAut ↥s.fr.E) zE) = 24 := by
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (G := MulAut ↥s.fr.E) zE)
    rw [Nat.card_prod, hcardOrbit, gl_card hE] at h
    omega
  have hle : ρ.range ≤ MulAction.stabilizer (MulAut ↥s.fr.E) zE := by
    rintro β ⟨n, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [MulAut.smul_def, y56Conj_apply]
    exact y56_NE_le_Cz hH (n : G) n.2
  have heq : ρ.range = MulAction.stabilizer (MulAut ↥s.fr.E) zE :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardStab, hrange])
  have hαstab : α ∈ MulAction.stabilizer (MulAut ↥s.fr.E) zE := by
    rw [MulAction.mem_stabilizer_iff]
    exact Subtype.ext (by
      show ((α • zE : ↥s.fr.E) : G) = ((zE : ↥s.fr.E) : G)
      rw [MulAut.smul_def]
      exact hα zE rfl)
  rw [← heq] at hαstab
  obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hαstab
  exact ⟨n, n.2, fun f => by rw [← hn]; exact hρ n f⟩

theorem y56_NE_pairs {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ a ∈ s.fr.E, ∀ b ∈ s.fr.E, ∀ a' ∈ s.fr.E, ∀ b' ∈ s.fr.E,
      a ≠ 1 → a ≠ s.fr.z → b ≠ 1 → b ≠ s.fr.z → a ≠ b → a ≠ b * s.fr.z →
      a' ≠ 1 → a' ≠ s.fr.z → b' ≠ 1 → b' ≠ s.fr.z → a' ≠ b' → a' ≠ b' * s.fr.z →
      ∃ n ∈ normIn L s.fr.E, n * a * n⁻¹ = a' ∧ n * b * n⁻¹ = b' := by
  have hE : IsE 3 ↥s.fr.E := y56_E_isE3 hH
  have hzE : s.fr.z ∈ s.fr.E := y56_z_mem_E hH
  have hz1 : s.fr.z ≠ 1 := (y56_v0 hH).2.2.2.1
  have hsq : ∀ x ∈ s.fr.E, x * x = 1 := fun x hx => by
    have := y56_E_sq hH x hx; simpa [pow_two] using this
  have hcommE : ∀ x ∈ s.fr.E, x * s.fr.z = s.fr.z * x :=
    fun x hx => y56_E_comm hH x hx s.fr.z hzE
  have key : ∀ {x y : G}, x ∈ s.fr.E → y ∈ s.fr.E → x * y = s.fr.z →
      x ≠ s.fr.z * y → False := by
    intro x y hx hy hxy_z hne
    exact hne (calc x = x * (y * y) := by rw [hsq y hy, mul_one]
      _ = (x * y) * y := by group
      _ = s.fr.z * y := by rw [hxy_z])
  intro a ha b hb a' ha' b' hb' ha1 haz hb1 hbz hab habz ha'1 ha'z hb'1 hb'z hab' hab'z
  have habc : (⟨a, ha⟩ : ↥s.fr.E) * ⟨b, hb⟩ ≠ ⟨s.fr.z, hzE⟩ :=
    fun h => key ha hb (Subtype.ext_iff.mp h) (fun h' => habz (h'.trans (hcommE b hb).symm))
  have hab'c' : (⟨a', ha'⟩ : ↥s.fr.E) * ⟨b', hb'⟩ ≠ ⟨s.fr.z, hzE⟩ :=
    fun h => key ha' hb' (Subtype.ext_iff.mp h) (fun h' => hab'z (h'.trans (hcommE b' hb').symm))
  obtain ⟨α, hαa, hαb, hαz⟩ := mulAut_triple hE
    (a := (⟨a, ha⟩ : ↥s.fr.E)) (b := ⟨b, hb⟩) (c := ⟨s.fr.z, hzE⟩)
    (a' := ⟨a', ha'⟩) (b' := ⟨b', hb'⟩) (c' := ⟨s.fr.z, hzE⟩)
    (fun h => ha1 (Subtype.ext_iff.mp h)) (fun h => hb1 (Subtype.ext_iff.mp h))
    (fun h => hz1 (Subtype.ext_iff.mp h)) (fun h => hab (Subtype.ext_iff.mp h))
    (fun h => haz (Subtype.ext_iff.mp h)) (fun h => hbz (Subtype.ext_iff.mp h)) habc
    (fun h => ha'1 (Subtype.ext_iff.mp h)) (fun h => hb'1 (Subtype.ext_iff.mp h))
    (fun h => hz1 (Subtype.ext_iff.mp h)) (fun h => hab' (Subtype.ext_iff.mp h))
    (fun h => ha'z (Subtype.ext_iff.mp h)) (fun h => hb'z (Subtype.ext_iff.mp h)) hab'c'
  have hfix : ∀ f : ↥s.fr.E, (f : G) = s.fr.z → ((α f : ↥s.fr.E) : G) = s.fr.z := by
    intro f hf
    have hfz : f = ⟨s.fr.z, hzE⟩ := Subtype.ext (by simpa using hf)
    rw [hfz, hαz]
  obtain ⟨n, hn, hconj⟩ := y56_aut_surj hH α hfix
  refine ⟨n, hn, ?_, ?_⟩
  · have := hconj ⟨a, ha⟩; rw [hαa] at this; exact this.symm
  · have := hconj ⟨b, hb⟩; rw [hαb] at this; exact this.symm

theorem y56_stab_v0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ n ∈ normIn L s.fr.E, n * (s.fr.b₁ * s.fr.b₂) * n⁻¹ = s.fr.b₁ * s.fr.b₂ → n ∈ s.fr.B := by
  classical
  intro n hn hfix
  have hE : IsE 3 ↥s.fr.E := y56_E_isE3 hH
  have hcardH : Nat.card ↥(normIn L s.fr.E) = 192 := y56_card_NE hH
  let v0 : G := s.fr.b₁ * s.fr.b₂
  have hv0E : v0 ∈ s.fr.E := y56_V_le_E hH (y56_v0 hH).1
  have hv01 : v0 ≠ 1 := (y56_v0 hH).2.2.1
  have hv0z : v0 ≠ s.fr.z := (y56_v0 hH).2.2.2.2.1
  let v0E : ↥s.fr.E := ⟨v0, hv0E⟩
  let zE : ↥s.fr.E := ⟨s.fr.z, y56_z_mem_E hH⟩
  have hv0E1 : v0E ≠ 1 := fun h => hv01 (Subtype.ext_iff.mp h)
  have hv0Ez : v0E ≠ zE := fun h => hv0z (Subtype.ext_iff.mp h)
  have hzE1 : zE ≠ 1 := fun h => (y56_v0 hH).2.2.2.1 (Subtype.ext_iff.mp h)
  letI : MulAction ↥(normIn L s.fr.E) ↥s.fr.E := MulAction.compHom ↥s.fr.E (y56Conj s)
  have horbit : MulAction.orbit ↥(normIn L s.fr.E) v0E =
      {x : ↥s.fr.E | x ≠ 1 ∧ x ≠ zE} := by
    ext x
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨m, rfl⟩
      constructor
      · intro h
        exact hv0E1 ((y56Conj s m).injective (by
          rw [map_one]
          rwa [MulAction.compHom_smul_def, MulAut.smul_def] at h))
      · intro h
        have h' : (m : G) * v0 * (m : G)⁻¹ = s.fr.z := by
          have h2 := congrArg Subtype.val h
          rwa [MulAction.compHom_smul_def, MulAut.smul_def, y56Conj_apply] at h2
        have hmz := y56_NE_le_Cz hH (m : G) m.2
        exact hv0z (calc v0 = (m : G)⁻¹ * ((m : G) * v0 * (m : G)⁻¹) * (m : G) := by group
          _ = (m : G)⁻¹ * s.fr.z * (m : G) := by rw [h']
          _ = (m : G)⁻¹ * ((m : G) * s.fr.z * (m : G)⁻¹) * (m : G) := by
                nth_rewrite 1 [← hmz]; rfl
          _ = s.fr.z := by group)
    · rintro ⟨hx1, hxz⟩
      obtain ⟨m, hm, hconj⟩ := y56_NE_trans hH v0 hv0E hv01 hv0z (x : G) x.2
        (fun h => hx1 (Subtype.ext h)) (fun h => hxz (Subtype.ext h))
      refine ⟨⟨m, hm⟩, ?_⟩
      rw [MulAction.compHom_smul_def, MulAut.smul_def]
      apply Subtype.ext
      rw [y56Conj_apply]
      exact hconj
  have hcardOrbit : Nat.card ↥(MulAction.orbit ↥(normIn L s.fr.E) v0E) = 6 := by
    haveI : Fintype ↥s.fr.E := Fintype.ofFinite _
    rw [Nat.card_coe_set_eq, horbit]
    have hset : ({x : ↥s.fr.E | x ≠ 1 ∧ x ≠ zE} : Set ↥s.fr.E) =
        (Set.univ \ ({1} : Set ↥s.fr.E)) \ ({zE} : Set ↥s.fr.E) := by ext x; simp
    rw [hset, Set.ncard_sdiff_singleton_of_mem (by simpa using hzE1),
      Set.ncard_sdiff_singleton_of_mem (Set.mem_univ (1 : ↥s.fr.E)), Set.ncard_univ, hE.2]
    norm_num
  have hcardstab : Nat.card (MulAction.stabilizer ↥(normIn L s.fr.E) v0E) = 32 := by
    have h := Nat.card_congr
      (MulAction.orbitProdStabilizerEquivGroup (G := ↥(normIn L s.fr.E)) v0E)
    rw [Nat.card_prod, hcardOrbit, hcardH] at h
    omega
  let Bsub : Subgroup ↥(normIn L s.fr.E) := s.fr.B.subgroupOf (normIn L s.fr.E)
  have hBcard : Nat.card ↥Bsub = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (y56_B_le_NE hH)).toEquiv]
    exact y54_card_B hH
  have hBle : Bsub ≤ MulAction.stabilizer ↥(normIn L s.fr.E) v0E := by
    intro b hb
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [MulAction.compHom_smul_def, MulAut.smul_def, y56Conj_apply]
    have hcomm : (b : G) * v0 = v0 * (b : G) :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp
        (Subgroup.mem_subgroupOf.mp hb)).2 v0 (Subgroup.subset_closure
          (Set.mem_singleton_iff.mpr rfl))).symm
    calc (b : G) * v0 * (b : G)⁻¹ = v0 * (b : G) * (b : G)⁻¹ := by rw [hcomm]
      _ = v0 := by group
  have heq : Bsub = MulAction.stabilizer ↥(normIn L s.fr.E) v0E :=
    Subgroup.eq_of_le_of_card_ge hBle (by rw [hcardstab, hBcard])
  have hmem : (⟨n, hn⟩ : ↥(normIn L s.fr.E)) ∈
      MulAction.stabilizer ↥(normIn L s.fr.E) v0E := by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [MulAction.compHom_smul_def, MulAut.smul_def, y56Conj_apply]
    exact hfix
  rw [← heq] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

end CFSG.OddStandard.HigherRank.YamadaG23
