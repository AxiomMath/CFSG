module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExtCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

open CFSG.QuasithinUnique.Unc25K1.Six
open scoped commutatorElement

section DiagExt

variable {G H : Type} [Group G] [Group H] {R S : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]
  [Mul S] [One S] [DecidableEq S] [Hashable S]

theorem exists_ext_of_diagExt [Finite G] [Finite H] {e₁ : G → R} {e₂ : H → S} (h₁ : IsEnc e₁)
    (h₂ : IsEnc e₂) {depth : ℕ} {a : List G} {b : List H} {n m : ℕ}
    (hc : diagExtOK e₁ e₂ depth a b n m = true) :
    Nat.card (Subgroup.closure {g | g ∈ a}) = n ∧ Nat.card (Subgroup.closure {g | g ∈ b}) = m ∧
      ∃ (V : Subgroup ↥(Subgroup.closure {g | g ∈ a})) (_ : V.Normal),
        (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x * x = 1) ∧
        Nonempty (↥(Subgroup.closure {g | g ∈ a}) ⧸ V ≃* ↥(Subgroup.closure {g | g ∈ b})) := by
  simp only [diagExtOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hca, hsa⟩, hcb⟩, hsb⟩, hcd⟩, hsd⟩, hlen⟩, hker⟩ := hc
  unfold elts at hca hsa hcb hsb hcd hsd hker
  have hA := card_closure_of_closedH h₁ a depth hca
  have hB := card_closure_of_closedH h₂ b depth hcb
  have hD := card_closure_of_closedH (isEnc_prod h₁ h₂) (a.zip b) depth hcd
  set D := Subgroup.closure {p : G × H | p ∈ a.zip b} with hDdef
  have hDA : Nat.card D = Nat.card (Subgroup.closure {g | g ∈ a}) := by
    rw [hD, hsd, hA, hsa]
  have hfst : D.map (MonoidHom.fst G H) = Subgroup.closure {g | g ∈ a} := by
    rw [hDdef, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq, MonoidHom.coe_fst]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (List.of_mem_zip hp).1
    · intro hg
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
      exact ⟨(a[k], b[k]'(by omega)), List.mem_iff_getElem.mpr ⟨k, by simp [List.length_zip]; omega,
        by simp⟩, rfl⟩
  have hsnd : D.map (MonoidHom.snd G H) = Subgroup.closure {h | h ∈ b} := by
    rw [hDdef, MonoidHom.map_closure]
    congr 1
    ext h
    simp only [Set.mem_image, Set.mem_ofPred_eq, MonoidHom.coe_snd]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (List.of_mem_zip hp).2
    · intro hh
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hh
      exact ⟨(a[k]'(by omega), b[k]), List.mem_iff_getElem.mpr ⟨k, by simp [List.length_zip]; omega,
        by simp⟩, rfl⟩
  let π₁ : ↥D →* ↥(Subgroup.closure {g | g ∈ a}) :=
    ((MonoidHom.fst G H).comp D.subtype).codRestrict _ (fun d => by
      rw [← hfst]
      exact ⟨d.1, d.2, rfl⟩)
  let π₂ : ↥D →* ↥(Subgroup.closure {h | h ∈ b}) :=
    ((MonoidHom.snd G H).comp D.subtype).codRestrict _ (fun d => by
      rw [← hsnd]
      exact ⟨d.1, d.2, rfl⟩)
  have h1 : Function.Surjective π₁ := by
    rintro ⟨x, hx⟩
    rw [← hfst] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact ⟨⟨d, hd⟩, rfl⟩
  have h2 : Function.Surjective π₂ := by
    rintro ⟨x, hx⟩
    rw [← hsnd] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact ⟨⟨d, hd⟩, rfl⟩
  have hb1 : Function.Bijective π₁ := h1.bijective_of_nat_card_le hDA.le
  let e₁' := MulEquiv.ofBijective π₁ hb1
  let ρ : ↥(Subgroup.closure {g | g ∈ a}) →* ↥(Subgroup.closure {h | h ∈ b}) :=
    π₂.comp e₁'.symm.toMonoidHom
  have hρ : Function.Surjective ρ := h2.comp e₁'.symm.surjective
  have hρx : ∀ x : ↥(Subgroup.closure {g | g ∈ a}),
      ((x : G), ((ρ x : ↥(Subgroup.closure {h | h ∈ b})) : H)) ∈ D := by
    intro x
    have hx : π₁ (e₁'.symm x) = x := e₁'.apply_symm_apply x
    have h1' : ((e₁'.symm x : ↥D) : G × H).1 = (x : G) := congrArg Subtype.val hx
    have h2' : ((e₁'.symm x : ↥D) : G × H).2 = ((ρ x : ↥(Subgroup.closure {h | h ∈ b})) : H) := rfl
    have := (e₁'.symm x : ↥D).2
    rw [← h1', ← h2'] at *
    exact this
  refine ⟨hA.trans hsa, hB.trans hsb, ρ.ker, inferInstance, ?_, ?_, ?_⟩
  · intro x hx y hy
    have hxD := hρx x
    have hyD := hρx y
    rw [MonoidHom.mem_ker] at hx hy
    rw [hx] at hxD
    rw [hy] at hyD
    simp only [OneMemClass.coe_one] at hxD hyD
    have hxE := (mem_closure_iff_H (isEnc_prod h₁ h₂) (a.zip b) depth hcd _).mp hxD
    have hyE := (mem_closure_iff_H (isEnc_prod h₁ h₂) (a.zip b) depth hcd _).mp hyD
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, List.mem_filter] at hker
    have hxK : ((e₁ (x : G), e₂ 1) : R × S) ∈ (bfsSet ((a.zip b).map fun p => (e₁ p.1, e₂ p.2))
        depth).toList ∧ ((e₁ (x : G), e₂ 1) : R × S).2 = 1 :=
      ⟨Std.HashSet.mem_toList.mpr hxE, by simp [h₂.map_one]⟩
    have hyK : ((e₁ (y : G), e₂ 1) : R × S) ∈ (bfsSet ((a.zip b).map fun p => (e₁ p.1, e₂ p.2))
        depth).toList ∧ ((e₁ (y : G), e₂ 1) : R × S).2 = 1 :=
      ⟨Std.HashSet.mem_toList.mpr hyE, by simp [h₂.map_one]⟩
    have := (hker _ hxK).2 _ hyK
    have h3 : e₁ ((x : G) * (y : G)) = e₁ ((y : G) * (x : G)) := by
      rw [h₁.map_mul, h₁.map_mul]
      exact this
    exact Subtype.ext (h₁.inj h3)
  · intro x hx
    have hxD := hρx x
    rw [MonoidHom.mem_ker] at hx
    rw [hx] at hxD
    simp only [OneMemClass.coe_one] at hxD
    have hxE := (mem_closure_iff_H (isEnc_prod h₁ h₂) (a.zip b) depth hcd _).mp hxD
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, List.mem_filter] at hker
    have hxK : ((e₁ (x : G), e₂ 1) : R × S) ∈ (bfsSet ((a.zip b).map fun p => (e₁ p.1, e₂ p.2))
        depth).toList ∧ ((e₁ (x : G), e₂ 1) : R × S).2 = 1 :=
      ⟨Std.HashSet.mem_toList.mpr hxE, by simp [h₂.map_one]⟩
    have := (hker _ hxK).1
    have h3 : e₁ ((x : G) * (x : G)) = e₁ 1 := by
      rw [h₁.map_mul, h₁.map_one]
      exact this
    exact Subtype.ext (h₁.inj h3)
  · exact ⟨QuotientGroup.quotientKerEquivOfSurjective ρ hρ⟩

end DiagExt

section Perfect

variable {G : Type} [Group G] {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]
  (enc : G → R)

variable {enc}

omit [DecidableEq R] [Hashable R] in
theorem commProd_mem (h : IsEnc enc) (gens : List G) (l : List CommWord)
    (hl : ∀ q ∈ l, evalW (gens.map enc) q.1 * evalW (gens.map enc) q.2.2.1 = 1 ∧
      evalW (gens.map enc) q.2.1 * evalW (gens.map enc) q.2.2.2 = 1) :
    enc (commProd gens l) = commProd (gens.map enc) l ∧
      commProd gens l ∈ ⁅Subgroup.closure {g | g ∈ gens}, Subgroup.closure {g | g ∈ gens}⁆ := by
  induction l with
  | nil => exact ⟨h.map_one, Subgroup.one_mem _⟩
  | cons q l ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun q' hq' => hl q' (List.mem_cons_of_mem _ hq'))
    obtain ⟨hq1, hq2⟩ := hl q List.mem_cons_self
    refine ⟨?_, ?_⟩
    · simp only [commProd, h.map_mul, ih1, enc_evalW h]
    · simp only [commProd]
      have hx : evalW gens q.2.2.1 = (evalW gens q.1)⁻¹ := by
        refine eq_inv_of_mul_eq_one_right (h.inj ?_)
        rw [h.map_mul, enc_evalW h, enc_evalW h, h.map_one]
        exact hq1
      have hy : evalW gens q.2.2.2 = (evalW gens q.2.1)⁻¹ := by
        refine eq_inv_of_mul_eq_one_right (h.inj ?_)
        rw [h.map_mul, enc_evalW h, enc_evalW h, h.map_one]
        exact hq2
      refine Subgroup.mul_mem _ ?_ ih2
      rw [hx, hy]
      exact Subgroup.commutator_mem_commutator (evalW_mem_closure gens q.1)
        (evalW_mem_closure gens q.2.1)

omit [Hashable R] in
theorem perfect_of_perfOK (h : IsEnc enc) {gens : List G} {cert : List (List CommWord)}
    (hc : perfOK enc gens cert = true) :
    ⁅Subgroup.closure {g | g ∈ gens}, Subgroup.closure {g | g ∈ gens}⁆ =
      Subgroup.closure {g | g ∈ gens} := by
  simp only [perfOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨hlen, hgen⟩, hinv⟩ := hc
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx))
      (Subgroup.inv_mem _ hy)
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    have hk' : k < cert.length := by omega
    have hmem : (gens[k], cert[k]) ∈ gens.zip cert :=
      List.mem_iff_getElem.mpr ⟨k, by simp [List.length_zip]; omega, by simp⟩
    have h1 := hgen _ hmem
    obtain ⟨he, hcomm⟩ := commProd_mem h gens cert[k]
      (fun q hq => hinv cert[k] (List.getElem_mem hk') q hq)
    have : commProd gens cert[k] = gens[k] := h.inj (by rw [he]; exact h1)
    rw [← this]
    exact hcomm

end Perfect

theorem commutator_self_le {G : Type*} [Group G] (L : Subgroup G) : ⁅L, L⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx))
    (Subgroup.inv_mem _ hy)

theorem isElemAbelianOfRank_of_card {V : Type*} [Group V] [Finite V]
    (hc : ∀ x y : V, x * y = y * x) (hsq : ∀ x : V, x * x = 1) {n : ℕ}
    (hcard : Nat.card V = 2 ^ n) : CFSG.Quasithin.IsElemAbelianOfRank 2 n V := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have h2 : ∀ x : Additive V, (2 : ℕ) • x = 0 := by
    intro x
    have : (2 : ℕ) • Additive.ofMul (Additive.toMul x) = Additive.ofMul (Additive.toMul x ^ 2) := by
      rw [ofMul_pow]
    have hx : Additive.ofMul (Additive.toMul x) = x := rfl
    rw [hx] at this
    rw [this, pow_two, hsq]
    rfl
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  let b := Module.finBasis (ZMod 2) (Additive V)
  have hd : Module.finrank (ZMod 2) (Additive V) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    have hcard' : Nat.card (Additive V) = 2 ^ n := hcard
    rw [hcard', Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let e : Additive V ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    b.equivFun.trans (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr hd.symm))
  exact ⟨AddEquiv.toMultiplicativeRight e.toAddEquiv⟩

open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem isExt_of_perfectCore_ext {G : Type} [Group G] [Finite G] {M L A : Subgroup G}
    {U B : Subgroup ↥M} (hB : B ∈ lFamily U) (hAL : A ≤ L) (hLM : L ≤ M) (hcomm : ⁅L, L⁆ ≤ A)
    (hperf : ⁅A, A⁆ = A) (hPL : B ⊔ U = L.subgroupOf M) {k : ℕ}
    [IsSimpleGroup (alternatingGroup (Fin k))]
    (hnab : ∃ a b : alternatingGroup (Fin k), a * b ≠ b * a) (V : Subgroup ↥A) [V.Normal]
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVsq : ∀ x ∈ V, x * x = 1)
    (hVcard : Nat.card V = 2 ^ 4) (e : ↥A ⧸ V ≃* alternatingGroup (Fin k)) :
    IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt k Y) := by
  have hAM : A ≤ M := hAL.trans hLM
  have hpc : perfectCore (B ⊔ U) = A.subgroupOf M := by
    rw [hPL]
    exact perfectCore_subgroupOf_eq hAL hLM hcomm hperf
  let eP : ↥(perfectCore (B ⊔ U)) ≃* ↥A :=
    (MulEquiv.subgroupCongr hpc).trans (Subgroup.subgroupOfEquivOfLe hAM)
  let g : ↥(perfectCore (B ⊔ U)) →* alternatingGroup (Fin k) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' V).comp eP.toMonoidHom)
  have hg : Function.Surjective g :=
    e.surjective.comp ((QuotientGroup.mk'_surjective V).comp eP.surjective)
  have hVsolv : Group.IsSolvable ↥V :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hVc a.1 a.2 b.1 b.2)
  have hsolv : Group.IsSolvable g.ker := by
    let φ : g.ker →* ↥V :=
      (eP.toMonoidHom.comp g.ker.subtype).codRestrict V fun x => by
        have hx := x.2
        rw [MonoidHom.mem_ker] at hx
        have : (QuotientGroup.mk' V) (eP (x : ↥(perfectCore (B ⊔ U)))) = 1 := by
          have := e.injective (hx.trans e.map_one.symm)
          exact this
        exact (QuotientGroup.eq_one_iff _).mp this
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 : eP (x : ↥(perfectCore (B ⊔ U))) = eP (y : ↥(perfectCore (B ⊔ U))) :=
        congrArg Subtype.val hxy
      exact Subtype.ext (eP.injective h1)
    exact Group.isSolvable_of_isSolvable_injective hφ
  have hBeq : B = perfectCore (B ⊔ U) := lFamily_eq_perfectCore hB hnab g hg hsolv
  let eB : ↥B ≃* ↥A := (MulEquiv.subgroupCongr hBeq).trans eP
  refine ⟨V.comap eB.toMonoidHom, inferInstance, ?_, ?_⟩
  · have hE2 : IsE2 4 ↥V :=
      isElemAbelianOfRank_of_card (fun a b => Subtype.ext (hVc a.1 a.2 b.1 b.2))
        (fun a => Subtype.ext (hVsq a.1 a.2)) hVcard
    have hcongr : V.comap eB.toMonoidHom = V.map eB.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm eB V
    exact IsE2.of_mulEquiv
      ((MulEquiv.subgroupCongr hcongr).trans (eB.symm.subgroupMap V).symm).symm hE2
  · refine ⟨(QuotientGroup.congr (V.comap eB.toMonoidHom) V eB ?_).trans e⟩
    exact Subgroup.map_comap_eq_self_of_surjective eB.surjective V

end CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
