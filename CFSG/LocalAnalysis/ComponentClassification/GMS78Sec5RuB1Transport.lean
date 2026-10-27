module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Conj
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Plane
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSylow
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Classes
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Stage3
public import CFSG.Sporadic.Schreier.RuB1Facts

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Sporadic.RuSchreier
open scoped Pointwise

section Ident

variable {G M : Type*} [Group G] [Group M] {L₀ : Subgroup G} {P : Subgroup M}

theorem mem_map_comap_subgroupOf_iff (φ : L₀ ≃* P) {Y : Subgroup M} {x : G} :
    x ∈ ((Y.subgroupOf P).comap φ.toMonoidHom).map L₀.subtype ↔
      ∃ hx : x ∈ L₀, ((φ ⟨x, hx⟩ : P) : M) ∈ Y := by
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨x'.2, hx'⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem card_map_comap_subgroupOf (φ : L₀ ≃* P) {Y : Subgroup M} (hY : Y ≤ P) :
    Nat.card (((Y.subgroupOf P).comap φ.toMonoidHom).map L₀.subtype) = Nat.card Y := by
  rw [card_map_of_injective L₀.subtype_injective, comap_equiv_eq_map_symm',
    card_map_of_injective φ.symm.injective, Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv]

theorem mem_map_subgroupOf_iff (φ : L₀ ≃* P) {Q : Subgroup G} {x : G} (hx : x ∈ L₀) :
    ((φ ⟨x, hx⟩ : P) : M) ∈ (Q.subgroupOf L₀).map (P.subtype.comp φ.toMonoidHom) ↔ x ∈ Q := by
  constructor
  · rintro ⟨x', hx', h⟩
    have e : x' = ⟨x, hx⟩ := φ.injective (Subtype.ext h)
    rw [e] at hx'
    exact hx'
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem card_map_subgroupOf (φ : L₀ ≃* P) {Q : Subgroup G} (hQ : Q ≤ L₀) :
    Nat.card ((Q.subgroupOf L₀).map (P.subtype.comp φ.toMonoidHom)) = Nat.card Q := by
  rw [card_map_of_injective (fun a b h => φ.injective (Subtype.ext h)),
    Nat.card_congr (subgroupOfEquivOfLe hQ).toEquiv]

theorem coe_equiv_mul (φ : L₀ ≃* P) {x x' : G} (hx : x ∈ L₀) (hx' : x' ∈ L₀) :
    ((φ ⟨x * x', mul_mem hx hx'⟩ : P) : M) = (φ ⟨x, hx⟩ : M) * (φ ⟨x', hx'⟩ : M) := by
  rw [← coe_mul, ← map_mul]
  rfl

theorem coe_equiv_inv (φ : L₀ ≃* P) {x : G} (hx : x ∈ L₀) :
    ((φ ⟨x⁻¹, inv_mem hx⟩ : P) : M) = (φ ⟨x, hx⟩ : M)⁻¹ := by
  rw [← coe_inv, ← map_inv]
  rfl

theorem eq_of_coe_equiv_eq (φ : L₀ ≃* P) {x x' : G} (hx : x ∈ L₀) (hx' : x' ∈ L₀)
    (h : ((φ ⟨x, hx⟩ : P) : M) = (φ ⟨x', hx'⟩ : M)) : x = x' :=
  congrArg Subtype.val (φ.injective (Subtype.ext h))

theorem commute_iff_coe_equiv (φ : L₀ ≃* P) {x x' : G} (hx : x ∈ L₀) (hx' : x' ∈ L₀) :
    x * x' = x' * x ↔
      (φ ⟨x, hx⟩ : M) * (φ ⟨x', hx'⟩ : M) = (φ ⟨x', hx'⟩ : M) * (φ ⟨x, hx⟩ : M) := by
  rw [← coe_equiv_mul φ hx hx', ← coe_equiv_mul φ hx' hx]
  constructor
  · intro h
    simp only [h]
  · intro h
    exact eq_of_coe_equiv_eq φ _ _ h

theorem coe_equiv_symm (φ : L₀ ≃* P) {m : M} (hm : m ∈ P) :
    ((φ ⟨((φ.symm ⟨m, hm⟩ : L₀) : G), (φ.symm ⟨m, hm⟩).2⟩ : P) : M) = m := by
  simp

theorem orderOf_coe_equiv (φ : L₀ ≃* P) {x : G} (hx : x ∈ L₀) :
    orderOf ((φ ⟨x, hx⟩ : P) : M) = orderOf x := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]

theorem card_inf_centralizer_equiv (φ : L₀ ≃* P) {x : G} (hx : x ∈ L₀) :
    Nat.card ↥(L₀ ⊓ centralizer ({x} : Set G)) =
      Nat.card ↥(P ⊓ centralizer ({((φ ⟨x, hx⟩ : P) : M)} : Set M)) := by
  have heq : L₀ ⊓ centralizer ({x} : Set G) =
      (((P ⊓ centralizer ({((φ ⟨x, hx⟩ : P) : M)} : Set M)).subgroupOf P).comap
        φ.toMonoidHom).map L₀.subtype := by
    ext y
    rw [mem_map_comap_subgroupOf_iff]
    constructor
    · intro hy
      obtain ⟨hyL₀, hyC⟩ := mem_inf.mp hy
      refine ⟨hyL₀, mem_inf.mpr ⟨(φ _).2, mem_centralizer_singleton_iff.mpr ?_⟩⟩
      exact (commute_iff_coe_equiv φ hyL₀ hx).mp (mem_centralizer_singleton_iff.mp hyC)
    · rintro ⟨hyL₀, hy⟩
      exact mem_inf.mpr ⟨hyL₀, mem_centralizer_singleton_iff.mpr
        ((commute_iff_coe_equiv φ hyL₀ hx).mpr
          (mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2))⟩
  rw [heq, card_map_comap_subgroupOf φ inf_le_left]

end Ident

theorem exists_conj_mem_of_isSylowOf {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    {C S Q : Subgroup M} (hS : IsSylowOf p S C) (hQ : IsPGroup p Q) (hQC : Q ≤ C) :
    ∃ c ∈ C, ∀ m ∈ Q, c * m * c⁻¹ ∈ S := by
  obtain ⟨Sy, hSy⟩ := hS
  have hQ' : IsPGroup p (Q.subgroupOf C) := hQ.comap_subtype
  obtain ⟨S', hS'⟩ := hQ'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C S' Sy
  refine ⟨c, c.2, fun m hm => ?_⟩
  have h1 : (⟨m, hQC hm⟩ : C) ∈ (S' : Set C) :=
    hS' (show (⟨m, hQC hm⟩ : C) ∈ Q.subgroupOf C from hm)
  have h2 : MulAut.conj c • (⟨m, hQC hm⟩ : C) ∈ MulAut.conj c • (S' : Set C) :=
    Set.smul_mem_smul_set h1
  rw [← Sylow.coe_smul, hc] at h2
  rw [← hSy]
  exact ⟨_, h2, rfl⟩


theorem ruZ_comm
    {s : Equiv.Perm (Fin 4060)} (hs : s ∈ ruS) :
    s * ruZ = ruZ * s := by
  have h : ruZ ∈ (Subgroup.center ruS).map ruS.subtype := by
    rw [center_ruS]
    exact mem_zpowers _
  obtain ⟨z', hz', hz'z⟩ := h
  rw [← hz'z]
  exact congrArg Subtype.val (mem_center_iff.mp hz' ⟨s, hs⟩)

namespace SzMinCounter

variable {G : Type} [Group G] [Finite G] {L T L₀ R R₂ : Subgroup G} {y d : G}

theorem exists_equiv_normalized
    (hM : SzMinCounter G L 1) (hS : Sec3.SzR G L T R 1 y d) (hR₂ : Sec3.IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) (hfr : Sec3.B1Frame L T L₀)
    {f : G} (hfA : f ∈ gmsA L T) (hof : orderOf f = 2) :
    ∃ φ : L₀ ≃* ruP, (∀ hf : f ∈ L₀, ((φ ⟨f, hf⟩ : ruP) : Equiv.Perm (Fin 4060)) = ruZ) ∧
      ∀ x (hx : x ∈ L₀), x ∈ R → ((φ ⟨x, hx⟩ : ruP) : Equiv.Perm (Fin 4060)) ∈ ruS := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRL₀ : R ≤ L₀ := hfr.R_le hM hS h4
  have hAL₀ : gmsA L T ≤ L₀ := (inf_le_left.trans inf_le_right).trans hfr.le
  have hfL₀ : f ∈ L₀ := hAL₀ hfA
  have hcR : Nat.card R = 2048 := by
    rw [hS.card_R hR₂, hS.card_T_eq h4]
    norm_num
  obtain ⟨e⟩ := hfr.ru
  set φ₁ : L₀ ≃* ruP := e.trans ruEquivP with hφ₁def
  set f₀ : G := ((φ₁.symm ⟨ruZ, ruZ_mem⟩ : L₀) : G) with hf₀def
  have hf₀L₀ : f₀ ∈ L₀ := (φ₁.symm ⟨ruZ, ruZ_mem⟩).2
  have hφ₁f₀ : ((φ₁ ⟨f₀, hf₀L₀⟩ : ruP) : Equiv.Perm (Fin 4060)) = ruZ :=
    coe_equiv_symm φ₁ ruZ_mem
  have hof₀ : orderOf f₀ = 2 := by
    rw [← orderOf_coe_equiv φ₁ hf₀L₀, hφ₁f₀, orderOf_ruZ]
  have hcf₀ : Nat.card ↥(L₀ ⊓ centralizer ({f₀} : Set G)) = 245760 := by
    rw [card_inf_centralizer_equiv φ₁ hf₀L₀, hφ₁f₀, ← ruC_eq_centralizer, card_ruC]
  have hcf : Nat.card ↥(L₀ ⊓ centralizer ({f} : Set G)) = 245760 := by
    rcases (RuB1.ru_involution_classes_sub hfr.ru hfL₀ hfL₀ hof hof).1 with h | h
    · exact h
    · exfalso
      have hdvd : Nat.card R ∣ Nat.card ↥(L₀ ⊓ centralizer ({f} : Set G)) :=
        Subgroup.card_dvd_of_le (le_inf hRL₀ fun r hr =>
          mem_centralizer_singleton_iff.mpr (hS.commute_gmsA hr hfA))
      rw [h, hcR] at hdvd
      norm_num at hdvd
  obtain ⟨c, hcL₀, hcf'⟩ :=
    (RuB1.ru_involution_classes_sub hfr.ru hfL₀ hf₀L₀ hof hof₀).2.mpr (hcf.trans hcf₀.symm)
  set φ₂ : L₀ ≃* ruP := (MulAut.conj (⟨c, hcL₀⟩ : L₀)).trans φ₁ with hφ₂def
  have hφ₂f : ((φ₂ ⟨f, hfL₀⟩ : ruP) : Equiv.Perm (Fin 4060)) = ruZ := by
    rw [← hφ₁f₀]
    show ((φ₁ (⟨c, hcL₀⟩ * ⟨f, hfL₀⟩ * (⟨c, hcL₀⟩ : L₀)⁻¹) : ruP) : Equiv.Perm (Fin 4060)) = _
    congr 2
    exact Subtype.ext hcf'
  have hCP : ruC ≤ ruP := by
    rw [ruC_eq_centralizer]
    exact inf_le_left
  set Rn := (R.subgroupOf L₀).map (ruP.subtype.comp φ₂.toMonoidHom) with hRndef
  have hRn2 : IsPGroup 2 Rn := (hS.isR.isPGroup.comap_subtype (K := L₀)).map _
  have hRnC : Rn ≤ ruC := by
    rintro _ ⟨x, hx, rfl⟩
    rw [ruC_eq_centralizer]
    refine mem_inf.mpr ⟨(φ₂ x).2, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← hφ₂f]
    exact (commute_iff_coe_equiv φ₂ x.2 hfL₀).mp (hS.commute_gmsA hx hfA)
  have hSC : IsSylowOf 2 ruS ruC := by
    refine isSylowOf_iff.mpr ⟨ruS_leC, IsPGroup.of_card (n := 14) (by rw [card_ruS]; norm_num),
      ?_⟩
    have h1 := (ruS.subgroupOf ruC).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe ruS_leC).toEquiv, card_ruS, card_ruC] at h1
    have h2 : ruS.relIndex ruC = 15 := by
      rw [relIndex]
      omega
    rw [h2]
    decide
  obtain ⟨c', hc'C, hc'⟩ := exists_conj_mem_of_isSylowOf hSC hRn2 hRnC
  refine ⟨φ₂.trans (MulAut.conj (⟨c', hCP hc'C⟩ : ruP)), fun hf => ?_, fun x hx hxR => ?_⟩
  · show c' * ((φ₂ ⟨f, hf⟩ : ruP) : Equiv.Perm (Fin 4060)) * c'⁻¹ = ruZ
    rw [hφ₂f]
    have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp (ruC_eq_centralizer ▸ hc'C)).2
    rw [h1, mul_inv_cancel_right]
  · exact hc' _ ⟨⟨x, hx⟩, hxR, rfl⟩

theorem exists_b1Transport
    (hM : SzMinCounter G L 1) (hS : Sec3.SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : Sec3.IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) (hfr : Sec3.B1Frame L T L₀)
    {f : G} (hfA : f ∈ gmsA L T) (hf1 : f ≠ 1)
    {A₁n Xn : Subgroup (Equiv.Perm (Fin 4060))} {g₅n : Equiv.Perm (Fin 4060)}
    (hN : RuB1NativeFacts A₁n Xn g₅n) :
    ∃ (S₀ X : Subgroup G) (g₅ : G),
      IsSylowOf 2 S₀ L₀ ∧ IsSylowOf 2 S₀ ⊤ ∧ IsSylowOf 2 S₀ (centralizer ({f} : Set G)) ∧
      R ≤ S₀ ∧ S₀ ≤ L₀ ∧ orderOf f = 2 ∧ (∀ s ∈ S₀, s * f = f * s) ∧
      X = closure {x | ∃ c ∈ L₀ ⊓ centralizer ({f} : Set G), ∃ a ∈ gmsA L T,
        x = c * a * c⁻¹} ∧
      (∀ l ∈ L₀ ⊓ centralizer ({f} : Set G), ∀ x ∈ X, l⁻¹ * x * l ∈ X) ∧
      (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) ∧ (∀ x ∈ X, x * x = 1) ∧ Nat.card X = 32 ∧
      gmsA L T ≤ X ∧ X ≤ S₀ ∧
      X ≤ centralizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) ∧
      g₅ ∈ L₀ ⊓ centralizer ({f} : Set G) ∧ orderOf g₅ = 5 ∧
      (∀ x ∈ X, g₅ * x = x * g₅ → x = 1 ∨ x = f) ∧
      (∀ U : Subgroup G, f ∈ U → U ≤ X → g₅ ∈ normalizer (U : Set G) →
        U = zpowers f ∨ U = X) ∧
      (∀ y ∈ S₀, y * y = 1 → y ∉ R → ∃ l ∈ L₀,
        (gmsA L T).map (MulAut.conj l).toMonoidHom ≤ S₀ ⊓ centralizer ({y} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := AS76b.oddCoreIn (centralizer (L : Set G)) with hW
  have hRL₀ : R ≤ L₀ := hfr.R_le hM hS h4
  have hL₀W : L₀ ≤ centralizer (W : Set G) := hfr.le_centralizer_oddCoreIn
  have hAL₀ : gmsA L T ≤ L₀ := (inf_le_left.trans inf_le_right).trans hfr.le
  have hfL₀ : f ∈ L₀ := hAL₀ hfA
  obtain ⟨hAel, hA8⟩ := hS.isElemAbelian_gmsA_and_card
  have hAsq : ∀ a ∈ gmsA L T, a * a = 1 := fun a ha => by rw [← pow_two]; exact hAel.2 a ha
  have hof : orderOf f = 2 := orderOf_eq_prime (by rw [pow_two]; exact hAsq f hfA) hf1
  obtain ⟨φ, hφf', hφR⟩ := hM.exists_equiv_normalized hS hR₂ h4 hfr hfA hof
  have hφf : ((φ ⟨f, hfL₀⟩ : ruP) : Equiv.Perm (Fin 4060)) = ruZ := hφf' hfL₀
  set S₀ := ((ruS.subgroupOf ruP).comap φ.toMonoidHom).map L₀.subtype with hS₀def
  have hmemS₀ : ∀ {x : G}, x ∈ S₀ ↔ ∃ hx : x ∈ L₀,
      ((φ ⟨x, hx⟩ : ruP) : Equiv.Perm (Fin 4060)) ∈ ruS :=
    mem_map_comap_subgroupOf_iff φ
  have hS₀L₀ : S₀ ≤ L₀ := map_subtype_le _
  have hcS₀ : Nat.card S₀ = 16384 := (card_map_comap_subgroupOf φ ruS_le).trans card_ruS
  have hS₀2 : IsPGroup 2 S₀ := IsPGroup.of_card (n := 14) (by rw [hcS₀]; norm_num)
  have hRS₀ : R ≤ S₀ := fun x hx => hmemS₀.mpr ⟨hRL₀ hx, hφR x (hRL₀ hx) hx⟩
  have hcL₀ : Nat.card L₀ = 145926144000 := by
    rw [Nat.card_congr φ.toEquiv, card_ruP']
  have hS₀syl : IsSylowOf 2 S₀ L₀ := by
    refine isSylowOf_iff.mpr ⟨hS₀L₀, hS₀2, ?_⟩
    have h1 := (S₀.subgroupOf L₀).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hS₀L₀).toEquiv, hcS₀, hcL₀] at h1
    have h2 : S₀.relIndex L₀ = 8906625 := by
      rw [relIndex]
      omega
    rw [h2]
    decide
  have hfc : ∀ s ∈ S₀, s * f = f * s := by
    intro s hs
    obtain ⟨hsL₀, hsS⟩ := hmemS₀.mp hs
    rw [commute_iff_coe_equiv φ hsL₀ hfL₀, hφf]
    exact ruZ_comm hsS
  have hAS₀ : gmsA L T ≤ S₀ :=
    ((inf_le_left.trans inf_le_left : gmsA L T ≤ T).trans hS.T_le).trans hRS₀
  have hRC : R ≤ centralizer (gmsA L T : Set G) := hS.le_centralizer_gmsA
  have hWodd : Odd (Nat.card W) := AS76b.odd_card_oddCoreIn _
  have hRW : R ⊓ W = ⊥ := by
    obtain ⟨k, hk⟩ := hS.isR.isPGroup.exists_card_eq
    refine disjoint_iff.mp (disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hWodd)
  have hWR : W ≤ centralizer (R : Set G) := le_centralizer_iff.mp (hRL₀.trans hL₀W)
  have hS₀C : S₀ ⊓ centralizer (gmsA L T : Set G) = R := by
    refine le_antisymm (fun s hs => ?_) (le_inf hRS₀ hRC)
    obtain ⟨hsS₀, hsC⟩ := mem_inf.mp hs
    have hsRW : s ∈ R ⊔ W := by
      rw [← hM.centralizer_gmsA_eq_sup hS h34 hR₂ h4]
      exact hsC
    obtain ⟨k, hk⟩ := hS₀2 ⟨s, hsS₀⟩
    have hsk : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact mem_of_mem_sup_of_pow_two_pow_eq_one hWodd hRW hWR hsRW hsk
  set A₁' := ((gmsA L T).subgroupOf L₀).map (ruP.subtype.comp φ.toMonoidHom) with hA₁'def
  have hA₁'mem : ∀ {a : G} (ha : a ∈ L₀),
      ((φ ⟨a, ha⟩ : ruP) : Equiv.Perm (Fin 4060)) ∈ A₁' ↔ a ∈ gmsA L T :=
    fun ha => mem_map_subgroupOf_iff φ ha
  have hA₁'le : A₁' ≤ ruP := by
    rintro _ ⟨a, -, rfl⟩
    exact (φ a).2
  have hA₁'eq : A₁' = A₁n := by
    refine hN.A1_char A₁' ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact (hmemS₀.mp (hAS₀ ha)).2
    · rw [← hφf]
      exact (hA₁'mem hfL₀).mpr hfA
    · rw [card_map_subgroupOf φ hAL₀, hA8]
    · rintro _ ⟨a, ha, rfl⟩
      have h1 := coe_equiv_mul φ a.2 a.2
      simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype,
        MulEquiv.coe_toMonoidHom]
      rw [← h1]
      have h2 : (⟨(a : G) * a, mul_mem a.2 a.2⟩ : L₀) = 1 := Subtype.ext (hAsq a ha)
      rw [h2, map_one, coe_one]
    ·
      have heq : ruS ⊓ centralizer (A₁' : Set (Equiv.Perm (Fin 4060))) =
          ((S₀ ⊓ centralizer (gmsA L T : Set G)).subgroupOf L₀).map
            (ruP.subtype.comp φ.toMonoidHom) := by
        ext m
        constructor
        · intro hm
          obtain ⟨hmS, hmC⟩ := mem_inf.mp hm
          have hmP : m ∈ ruP := ruS_le hmS
          set x : G := ((φ.symm ⟨m, hmP⟩ : L₀) : G) with hxdef
          have hxL₀ : x ∈ L₀ := (φ.symm ⟨m, hmP⟩).2
          have hφx : ((φ ⟨x, hxL₀⟩ : ruP) : Equiv.Perm (Fin 4060)) = m := coe_equiv_symm φ hmP
          refine ⟨⟨x, hxL₀⟩, mem_inf.mpr ⟨hmemS₀.mpr ⟨hxL₀, by
            show ((φ ⟨x, hxL₀⟩ : ruP) : Equiv.Perm (Fin 4060)) ∈ ruS
            rw [hφx]
            exact hmS⟩, mem_centralizer_iff.mpr fun a ha => ?_⟩, hφx⟩
          have h1 := mem_centralizer_iff.mp hmC _ ((hA₁'mem (hAL₀ ha)).mpr ha)
          rw [← hφx] at h1
          exact (commute_iff_coe_equiv φ (hAL₀ ha) hxL₀).mpr h1
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨hxS₀, hxC⟩ := mem_inf.mp hx
          refine mem_inf.mpr ⟨(hmemS₀.mp hxS₀).2, mem_centralizer_iff.mpr ?_⟩
          rintro _ ⟨a, ha, rfl⟩
          exact (commute_iff_coe_equiv φ a.2 x.2).mp (mem_centralizer_iff.mp hxC a ha)
      rw [heq, card_map_subgroupOf φ (inf_le_left.trans hS₀L₀), hS₀C, hS.card_R hR₂,
        hS.card_T_eq h4]
      norm_num
  set X := closure {x | ∃ c ∈ L₀ ⊓ centralizer ({f} : Set G), ∃ a ∈ gmsA L T,
    x = c * a * c⁻¹} with hXdef
  have hXL₀ : X ≤ L₀ := by
    rw [closure_le]
    rintro _ ⟨c, hc, a, ha, rfl⟩
    exact mul_mem (mul_mem (mem_inf.mp hc).1 (hAL₀ ha)) (inv_mem (mem_inf.mp hc).1)
  have hAX : gmsA L T ≤ X := fun a ha =>
    subset_closure ⟨1, mem_inf.mpr ⟨one_mem _, one_mem _⟩, a, ha, by group⟩
  have hF4 : ∀ l ∈ L₀ ⊓ centralizer ({f} : Set G), ∀ x ∈ X, l⁻¹ * x * l ∈ X := by
    intro l hl x hx
    have hle : X.map (MulAut.conj l⁻¹).toMonoidHom ≤ X := by
      rw [hXdef, MonoidHom.map_closure, closure_le]
      rintro _ ⟨_, ⟨c, hc, a, ha, rfl⟩, rfl⟩
      refine subset_closure ⟨l⁻¹ * c, mul_mem (inv_mem hl) hc, a, ha, ?_⟩
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
    have := hle ⟨x, hx, rfl⟩
    simpa using this
  have hCcent : ∀ c ∈ ruC, c ∈ ruP ∧ c * ruZ = ruZ * c := by
    intro c hc
    rw [ruC_eq_centralizer] at hc
    exact ⟨(mem_inf.mp hc).1, (mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2)⟩
  have hφC : ∀ {c : G} (hc : c ∈ L₀ ⊓ centralizer ({f} : Set G)),
      ((φ ⟨c, (mem_inf.mp hc).1⟩ : ruP) : Equiv.Perm (Fin 4060)) ∈ ruC := by
    intro c hc
    rw [ruC_eq_centralizer]
    refine mem_inf.mpr ⟨(φ _).2, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← hφf]
    exact (commute_iff_coe_equiv φ (mem_inf.mp hc).1 hfL₀).mp
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2)
  set X' := (X.subgroupOf L₀).map (ruP.subtype.comp φ.toMonoidHom) with hX'def
  have hX'mem : ∀ {x : G} (hx : x ∈ L₀),
      ((φ ⟨x, hx⟩ : ruP) : Equiv.Perm (Fin 4060)) ∈ X' ↔ x ∈ X :=
    fun hx => mem_map_subgroupOf_iff φ hx
  have hX'eq : X' = Xn := by
    refine le_antisymm ?_ ?_
    ·
      have hpull : X ≤ ((Xn.subgroupOf ruP).comap φ.toMonoidHom).map L₀.subtype := by
        rw [hXdef, closure_le]
        rintro _ ⟨c, hc, a, ha, rfl⟩
        have hcL₀ := (mem_inf.mp hc).1
        refine (mem_map_comap_subgroupOf_iff φ).mpr ⟨mul_mem (mul_mem hcL₀ (hAL₀ ha))
          (inv_mem hcL₀), ?_⟩
        rw [coe_equiv_mul φ (mul_mem hcL₀ (hAL₀ ha)) (inv_mem hcL₀),
          coe_equiv_mul φ hcL₀ (hAL₀ ha), coe_equiv_inv φ hcL₀, hN.X_eq]
        refine subset_closure ⟨_, hφC hc, _, ?_, rfl⟩
        rw [← hA₁'eq]
        exact (hA₁'mem (hAL₀ ha)).mpr ha
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨_, h⟩ := (mem_map_comap_subgroupOf_iff φ).mp (hpull hx)
      exact h
    · rw [hN.X_eq, closure_le]
      rintro _ ⟨c', hc', a', ha', rfl⟩
      obtain ⟨hc'P, hc'z⟩ := hCcent c' hc'
      have ha'P : a' ∈ ruP := hA₁'le (hA₁'eq ▸ ha')
      set c : G := ((φ.symm ⟨c', hc'P⟩ : L₀) : G) with hcdef
      set a : G := ((φ.symm ⟨a', ha'P⟩ : L₀) : G) with hadef
      have hcL₀ : c ∈ L₀ := (φ.symm ⟨c', hc'P⟩).2
      have haL₀ : a ∈ L₀ := (φ.symm ⟨a', ha'P⟩).2
      have hφc : ((φ ⟨c, hcL₀⟩ : ruP) : Equiv.Perm (Fin 4060)) = c' := coe_equiv_symm φ hc'P
      have hφa : ((φ ⟨a, haL₀⟩ : ruP) : Equiv.Perm (Fin 4060)) = a' := coe_equiv_symm φ ha'P
      have hcf : c ∈ L₀ ⊓ centralizer ({f} : Set G) := by
        refine mem_inf.mpr ⟨hcL₀, mem_centralizer_singleton_iff.mpr ?_⟩
        rw [commute_iff_coe_equiv φ hcL₀ hfL₀, hφf, hφc]
        exact hc'z
      have haA : a ∈ gmsA L T := by
        rw [← hA₁'mem haL₀, hφa, hA₁'eq]
        exact ha'
      have hmem : c * a * c⁻¹ ∈ X := subset_closure ⟨c, hcf, a, haA, rfl⟩
      have hxL₀ : c * a * c⁻¹ ∈ L₀ := hXL₀ hmem
      have h1 := (hX'mem hxL₀).mpr hmem
      rw [coe_equiv_mul φ (mul_mem hcL₀ haL₀) (inv_mem hcL₀), coe_equiv_mul φ hcL₀ haL₀,
        coe_equiv_inv φ hcL₀, hφc, hφa] at h1
      exact h1
  have hXX : ∀ {x : G} (hx : x ∈ X), ((φ ⟨x, hXL₀ hx⟩ : ruP) : Equiv.Perm (Fin 4060)) ∈ Xn :=
    fun hx => hX'eq ▸ (hX'mem (hXL₀ hx)).mpr hx
  have hXS₀ : X ≤ S₀ := fun x hx => hmemS₀.mpr ⟨hXL₀ hx, hN.X_le (hXX hx)⟩
  have hφ1 : ((φ ⟨1, one_mem _⟩ : ruP) : Equiv.Perm (Fin 4060)) = 1 := by
    rw [show (⟨1, one_mem _⟩ : L₀) = 1 from rfl, map_one, coe_one]
  have hg5P : g₅n ∈ ruP := (hCcent g₅n hN.g5_mem).1
  set g₅ : G := ((φ.symm ⟨g₅n, hg5P⟩ : L₀) : G) with hg5def
  have hg5L₀ : g₅ ∈ L₀ := (φ.symm ⟨g₅n, hg5P⟩).2
  have hφg5 : ((φ ⟨g₅, hg5L₀⟩ : ruP) : Equiv.Perm (Fin 4060)) = g₅n := coe_equiv_symm φ hg5P
  have hg5f : g₅ ∈ L₀ ⊓ centralizer ({f} : Set G) := by
    refine mem_inf.mpr ⟨hg5L₀, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [commute_iff_coe_equiv φ hg5L₀ hfL₀, hφf, hφg5]
    exact (hCcent g₅n hN.g5_mem).2
  have hφpow : ∀ (k : ℕ),
      ((φ ⟨g₅ ^ k, pow_mem hg5L₀ k⟩ : ruP) : Equiv.Perm (Fin 4060)) = g₅n ^ k := by
    intro k
    have h1 : (⟨g₅ ^ k, pow_mem hg5L₀ k⟩ : L₀) = ⟨g₅, hg5L₀⟩ ^ k := Subtype.ext (by simp)
    rw [h1, map_pow, coe_pow, hφg5]
  have htop : IsSylowOf 2 S₀ ⊤ := hM.isSylowOf_top_of_isSylowOf hS.sec3 hS.foundation
    hS.oddCenter h4 hfr.inf_eq hfr.centralizer_eq.ge hfr.normalizer_eq.le
    (fun t ht ht1 => hM.centralizer_le_normalizer_oddCoreIn hS.sec3 hS.foundation ht ht1)
    hS₀syl (hS.T_le.trans hRS₀)
  refine ⟨S₀, X, g₅, hS₀syl, htop, ?_, hRS₀, hS₀L₀, hof, hfc, rfl, hF4, ?_, ?_, ?_, hAX,
    hXS₀, hXL₀.trans hL₀W, hg5f, ?_, ?_, ?_, ?_⟩
  · obtain ⟨-, -, hidx⟩ := isSylowOf_iff.mp htop
    have hS₀Cf : S₀ ≤ centralizer ({f} : Set G) := fun s hs =>
      mem_centralizer_singleton_iff.mpr (hfc s hs)
    refine isSylowOf_iff.mpr ⟨hS₀Cf, hS₀2, fun h2 => hidx ?_⟩
    rw [relIndex_top_right]
    exact h2.trans (relIndex_dvd_index_of_le hS₀Cf)
  · intro a ha b hb
    exact (commute_iff_coe_equiv φ (hXL₀ ha) (hXL₀ hb)).mpr (hN.X_comm _ (hXX ha) _ (hXX hb))
  · intro x hx
    have h1 := hN.X_sq _ (hXX hx)
    rw [← coe_equiv_mul φ (hXL₀ hx) (hXL₀ hx), ← hφ1] at h1
    exact eq_of_coe_equiv_eq φ _ _ h1
  · rw [← card_map_subgroupOf φ hXL₀, ← hX'def, hX'eq, hN.card_X]
  · rw [← orderOf_coe_equiv φ hg5L₀, hφg5, hN.g5_order]
  · intro x hx hcx
    have h1 := (commute_iff_coe_equiv φ hg5L₀ (hXL₀ hx)).mp hcx
    rw [hφg5] at h1
    rcases hN.g5_cent _ (hXX hx) h1 with h | h
    · left
      rw [← hφ1] at h
      exact eq_of_coe_equiv_eq φ _ _ h
    · right
      rw [← hφf] at h
      exact eq_of_coe_equiv_eq φ _ _ h
  · intro U hfU hUX hgU
    by_cases hU : U ≤ zpowers f
    · exact Or.inl (le_antisymm hU (zpowers_le.mpr hfU))
    right
    refine le_antisymm hUX ?_
    obtain ⟨u, huU, hu⟩ := IsConcreteLE.not_le_iff_exists.mp hU
    have huX := hUX huU
    have hu1 : ((φ ⟨u, hXL₀ huX⟩ : ruP) : Equiv.Perm (Fin 4060)) ≠ 1 := by
      intro h
      apply hu
      rw [← hφ1] at h
      rw [eq_of_coe_equiv_eq φ _ _ h]
      exact one_mem _
    have huz : ((φ ⟨u, hXL₀ huX⟩ : ruP) : Equiv.Perm (Fin 4060)) ≠ ruZ := by
      intro h
      apply hu
      rw [← hφf] at h
      rw [eq_of_coe_equiv_eq φ _ _ h]
      exact mem_zpowers f
    have hgen := hN.g5_gen _ (hXX huX) hu1 huz
    set U' := (U.subgroupOf L₀).map (ruP.subtype.comp φ.toMonoidHom) with hU'def
    have hU'mem : ∀ {x : G} (hx : x ∈ L₀),
        ((φ ⟨x, hx⟩ : ruP) : Equiv.Perm (Fin 4060)) ∈ U' ↔ x ∈ U :=
      fun hx => mem_map_subgroupOf_iff φ hx
    have hcl : closure (insert ruZ (Set.range fun i : Fin 5 =>
        g₅n ^ (i : ℕ) * (φ ⟨u, hXL₀ huX⟩ : Equiv.Perm (Fin 4060)) * (g₅n ^ (i : ℕ))⁻¹)) ≤
          U' := by
      rw [closure_le]
      rintro _ (rfl | ⟨i, rfl⟩)
      · rw [← hφf]
        exact (hU'mem hfL₀).mpr hfU
      · have hgi : g₅ ^ (i : ℕ) ∈ normalizer (U : Set G) := pow_mem hgU _
        have hc : g₅ ^ (i : ℕ) * u * (g₅ ^ (i : ℕ))⁻¹ ∈ U :=
          (mem_normalizer_iff.mp hgi u).mp huU
        have hcL₀ : g₅ ^ (i : ℕ) * u * (g₅ ^ (i : ℕ))⁻¹ ∈ L₀ :=
          mul_mem (mul_mem (pow_mem hg5L₀ _) (hXL₀ huX)) (inv_mem (pow_mem hg5L₀ _))
        have h1 := (hU'mem hcL₀).mpr hc
        rw [coe_equiv_mul φ (mul_mem (pow_mem hg5L₀ _) (hXL₀ huX)) (inv_mem (pow_mem hg5L₀ _)),
          coe_equiv_mul φ (pow_mem hg5L₀ _) (hXL₀ huX), coe_equiv_inv φ (pow_mem hg5L₀ _),
          hφpow] at h1
        exact h1
    intro x hx
    exact (hU'mem (hXL₀ hx)).mp (hcl (hgen (hXX hx)))
  ·
    intro y hy hy2 hyR
    obtain ⟨hyL₀, hyS⟩ := hmemS₀.mp hy
    have hy2' : (φ ⟨y, hyL₀⟩ : Equiv.Perm (Fin 4060)) * (φ ⟨y, hyL₀⟩ : Equiv.Perm (Fin 4060)) =
        1 := by
      rw [← coe_equiv_mul φ hyL₀ hyL₀]
      have h1 : (⟨y * y, mul_mem hyL₀ hyL₀⟩ : L₀) = 1 := Subtype.ext hy2
      rw [h1, map_one, coe_one]
    have hyC : (φ ⟨y, hyL₀⟩ : Equiv.Perm (Fin 4060)) ∉
        centralizer (A₁n : Set (Equiv.Perm (Fin 4060))) := by
      intro h
      apply hyR
      rw [← hS₀C]
      refine mem_inf.mpr ⟨hy, mem_centralizer_iff.mpr fun a ha => ?_⟩
      have h1 := mem_centralizer_iff.mp h _ (hA₁'eq ▸ (hA₁'mem (hAL₀ ha)).mpr ha)
      exact (commute_iff_coe_equiv φ (hAL₀ ha) hyL₀).mpr h1
    obtain ⟨l', hl'P, hl'⟩ := hN.F8 _ hyS hy2' hyC
    set l : G := ((φ.symm ⟨l', hl'P⟩ : L₀) : G) with hldef
    have hlL₀ : l ∈ L₀ := (φ.symm ⟨l', hl'P⟩).2
    have hφl : ((φ ⟨l, hlL₀⟩ : ruP) : Equiv.Perm (Fin 4060)) = l' := coe_equiv_symm φ hl'P
    refine ⟨l, hlL₀, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have haL₀ := hAL₀ ha
    have hxL₀ : l * a * l⁻¹ ∈ L₀ := mul_mem (mul_mem hlL₀ haL₀) (inv_mem hlL₀)
    have h1 : ((φ ⟨l * a * l⁻¹, hxL₀⟩ : ruP) : Equiv.Perm (Fin 4060)) ∈
        ruS ⊓ centralizer ({(φ ⟨y, hyL₀⟩ : Equiv.Perm (Fin 4060))} : Set _) := by
      refine hl' ⟨_, hA₁'eq ▸ (hA₁'mem haL₀).mpr ha, ?_⟩
      rw [coe_equiv_mul φ (mul_mem hlL₀ haL₀) (inv_mem hlL₀), coe_equiv_mul φ hlL₀ haL₀,
        coe_equiv_inv φ hlL₀, hφl]
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    obtain ⟨h1S, h1C⟩ := mem_inf.mp h1
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    refine mem_inf.mpr ⟨hmemS₀.mpr ⟨hxL₀, h1S⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    exact (commute_iff_coe_equiv φ hxL₀ hyL₀).mpr
      (mem_centralizer_singleton_iff.mp h1C)

end SzMinCounter

theorem b1Stage3Transport_of_native
    {A₁n Xn : Subgroup (Equiv.Perm (Fin 4060))} {g₅n : Equiv.Perm (Fin 4060)}
    (hN : RuB1NativeFacts A₁n Xn g₅n) : B1Stage3Transport := by
  intro G _ _ L T L₀ R R₂ y d f hM hS h34 hR₂ h4 hfr hfA hf1
  obtain ⟨S₀, X, g₅, hS₀, -, -, hRS₀, -, -, hfc, -, hF4, hcomm, hsq, hcard, hAX, hXS₀, -, hg5,
    ho5, -, hirr, hF8⟩ := hM.exists_b1Transport hS h34 hR₂ h4 hfr hfA hf1 hN
  exact ⟨S₀, X, g₅, hS₀, hRS₀, hfc, hAX, hXS₀, hcomm, hsq, hcard, hF4, hg5,
    by rw [ho5]; decide, hirr, hF8⟩

theorem b1Stage3Alpha :
    B1Stage3Alpha :=
  fun _ _ _ _ _ _ _ _ _ hM hS h34 hR₂ h4 _ hg =>
    hM.mem_normalizer_of_map_gmsA_le_centralizer hS h34 hR₂ h4 hg

end CFSG.ComponentClassification.GMS78
