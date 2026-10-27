module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cFix
public import CFSG.GH74.GLS.C3.Layer1.Thm1Layer
public import CFSG.ClassicalInvolution.PerfectCase.Basic
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerSL2

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.ComponentClassification CFSG.ClassicalInvolution CFSG.GH74.GLS
  CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P31c

section LayerLift

theorem le_ker_of_odd_normal {A B : Type} [Group A] [Group B] (ρ : A →* B)
    (hρ : Function.Surjective ρ) (hB : pPrimeCore 2 B = ⊥) {N : Subgroup A} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ ρ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a ha
  have hNB : (N.map ρ).Normal := Subgroup.Normal.map hN ρ hρ
  have hdvd : Nat.card (N.map ρ) ∣ Nat.card N :=
    Subgroup.card_dvd_of_surjective (f := ρ.subgroupMap N) (ρ.subgroupMap_surjective N)
  have hcop : Nat.Coprime 2 (Nat.card (N.map ρ)) :=
    Nat.coprime_two_left.2 (Odd.of_dvd_nat hodd hdvd)
  have hle := GroupTheory.le_pPrimeCore_of_normal hNB hcop
  rw [hB] at hle
  have h1 : ρ a ∈ (⊥ : Subgroup B) := hle ⟨a, ha, rfl⟩
  exact Subgroup.mem_bot.1 h1

theorem pPrimeCore_eq_ker_of_odd {A B : Type} [Group A] [Finite A] [Group B] (ρ : A →* B)
    (hρ : Function.Surjective ρ) (hodd : Odd (Nat.card ρ.ker)) (hB : pPrimeCore 2 B = ⊥) :
    pPrimeCore 2 A = ρ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hodd' : Odd (Nat.card (pPrimeCore 2 A)) :=
      Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := A))
    exact le_ker_of_odd_normal ρ hρ hB pPrimeCore_normal hodd'
  · exact GroupTheory.le_pPrimeCore_of_normal (MonoidHom.normal_ker ρ) (Nat.coprime_two_left.2 hodd)

theorem pPrimeCore_eq_bot_of_simple {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) : pPrimeCore 2 S = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hS.eq_bot_or_eq_top_of_normal (pPrimeCore 2 S) with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card S) := by
      have h1 := Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := S))
      rwa [h, Subgroup.card_top] at h1
    have hsolv : Group.IsSolvable S := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hq : CFSG.IsQuasisimple S := (LocalCores.isQuasisimple_of_isSimpleGroup hna).1
    exact not_isSolvable_of_open_isQuasisimple (CatalogueBAlternating.quasisimple_iff_native.1 hq) hsolv

theorem exists_twoComponent_of_surj {A Y₁ : Type} [Group A] [Finite A] [Group Y₁] (ρ : A →* Y₁)
    (hρ : Function.Surjective ρ) (hodd : Odd (Nat.card ρ.ker))
    (S : Subgroup Y₁) [S.Normal] (hS : IsSimpleGroup ↥S) (hSna : ∃ a b : ↥S, a * b ≠ b * a) :
    ∃ L : Subgroup A, TwoComponents.IsTwoComponent L ∧ L ≤ S.comap ρ ∧
      (∀ m ∈ S.comap ρ, orderOf m = 2 → m ∈ L) ∧
      Nonempty ((↥L ⧸ pPrimeCore 2 ↥L) ≃* ↥S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Y₁ := Finite.of_surjective ρ hρ
  have : Finite ↥S := inferInstance
  set M : Subgroup A := S.comap ρ with hMdef
  have hMn : M.Normal := inferInstance
  have hMsub : Open.IsSubnormal M ⊤ :=
    Components.chain_of_mathlib_subnormal (Subgroup.Normal.isSubnormal hMn)
  let ρM : ↥M →* ↥S := (ρ.comp M.subtype).codRestrict S (fun m => m.2)
  have hρM : Function.Surjective ρM := by
    intro s
    obtain ⟨a, ha⟩ := hρ (s : Y₁)
    exact ⟨⟨a, by rw [hMdef, Subgroup.mem_comap, ha]; exact s.2⟩, Subtype.ext ha⟩
  let ι : ↥ρM.ker →* ↥ρ.ker :=
    ((M.subtype.comp ρM.ker.subtype).codRestrict ρ.ker (fun m => by
      have h := MonoidHom.mem_ker.1 m.2
      exact MonoidHom.mem_ker.2 (congrArg Subtype.val h)))
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 : (ι a).val = (ι b).val := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  have hkerModd : Odd (Nat.card ρM.ker) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective ι hι)
  have hMcore : pPrimeCore 2 ↥M = ρM.ker :=
    pPrimeCore_eq_ker_of_odd ρM hρM hkerModd (pPrimeCore_eq_bot_of_simple hS hSna)
  let eM : (↥M ⧸ pPrimeCore 2 ↥M) ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hMcore).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρM hρM)
  have hqS : CFSG.IsQuasisimple ↥S := (LocalCores.isQuasisimple_of_isSimpleGroup hSna).1
  let eM₀ : (↥M ⧸ Open.componentClassificationOddCore ↥M) ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq (CatalogueBAlternating.primeCore_two_eq_oddCore ↥M).symm).trans eM
  have hq : Open.IsQuasisimple (↥M ⧸ Open.componentClassificationOddCore ↥M) :=
    Components.quasisimple_of_equiv eM₀ (CatalogueBAlternating.quasisimple_iff_native.1 hqS)
  obtain ⟨L, hLM, hL, hmap⟩ := exists_isTwoComponent_le M hMsub hq
  refine ⟨L, hL, hLM, fun m hm hm2 => ?_, ?_⟩
  · exact mem_of_orderOf_eq_two_of_map_eq hLM hL.1 hMsub hmap hm hm2
  · obtain ⟨e1⟩ := nonempty_oddCoreQuotientEquiv_of_map_eq hL.1 hMsub hmap
    exact ⟨(QuotientGroup.quotientMulEquivOfEq
      (CatalogueBAlternating.primeCore_two_eq_oddCore ↥L)).trans (e1.trans eM₀)⟩

end LayerLift

section LayerComp

variable {G : Type} [Group G] [Finite G]

theorem exists_noncomm_of_quasisimple {Q : Type} [Group Q] (hK : CFSG.IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hK.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', b', fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem center_eq_bot_of_simple' {S : Type} [Group S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a

theorem exists_layer_comp {x w z u : G} {K : Subgroup G}
    (hKC : K ≤ centralizer ({x} : Set G))
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hwC : w ∈ centralizer ({x} : Set G)) (hw2 : orderOf w = 2)
    {F₀ : Type} [Field F₀] [Finite F₀] (hodd : Odd (Nat.card F₀)) (h3 : 3 < Nat.card F₀)
    (e₀ : ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨w, hwC⟩)) ≃* GorensteinWalter.PGL2 F₀)
    (hzK : z ∈ K) (hzw : z * w = w * z) (hz2 : orderOf z = 2)
    (huK : u ∈ K) (huw : u * w = w * u) (huz : u * u = z) :
    ∃ Λ : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({w} : Set G)) Λ ∧
      Λ ≤ K ∧ z ∈ Λ ∧ HasL2Model (kBar Λ) (fun q => q = Nat.card F₀) ∧
        Subgroup.center (kBar Λ) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H₀ : Subgroup G := K ⊓ centralizer ({w} : Set G) with hH₀
  let ρ : ↥H₀ →* GorensteinWalter.PGL2 F₀ := e₀.toMonoidHom.comp (centMap hKN hwC)
  have hρ : Function.Surjective ρ := e₀.surjective.comp (centMap_surjective hKN hwC hw2)
  have hker : ρ.ker = (centMap hKN hwC).ker := by
    ext h
    simp only [MonoidHom.mem_ker, ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact ⟨fun h1 => e₀.injective (by rw [h1, map_one]), fun h1 => by rw [h1, map_one]⟩
  have hkodd : Odd (Nat.card ρ.ker) := hker ▸ centMap_ker_odd hKN hwC
  have hoddpp := isOddPrimePower_of_odd F₀ hodd
  let S : Subgroup (GorensteinWalter.PGL2 F₀) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range
  have hSn : S.Normal := Glauberman.Dickson.MaxSubfield.toPGL_range_normal hoddpp h3
  have hSq : CFSG.IsQuasisimple ↥S := ComponentClassification.CatalogueBLinearTwo.pglPSLRange_quasisimple F₀ h3
  have hSna : ∃ a b : ↥S, a * b ≠ b * a := exists_noncomm_of_quasisimple hSq
  let eS : GorensteinWalter.PSL2 F₀ ≃* ↥S :=
    MonoidHom.ofInjective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hSs : IsSimpleGroup ↥S := by
    have : IsSimpleGroup (GorensteinWalter.PSL2 F₀) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact eS.symm.isSimpleGroup
  obtain ⟨L₀, hL₀, hL₀M, hinv, ⟨eL⟩⟩ := exists_twoComponent_of_surj ρ hρ hkodd S hSs hSna
  have hzH : z ∈ H₀ := ⟨hzK, mem_centralizer_singleton_iff.2 hzw⟩
  have huH : u ∈ H₀ := ⟨huK, mem_centralizer_singleton_iff.2 huw⟩
  have hzM : (⟨z, hzH⟩ : ↥H₀) ∈ S.comap ρ := by
    have h1 : (⟨z, hzH⟩ : ↥H₀) = (⟨u, huH⟩ : ↥H₀) ^ 2 := Subtype.ext (by
      rw [Subgroup.coe_pow, sq, huz])
    rw [Subgroup.mem_comap, h1, map_pow]
    obtain ⟨s, hs⟩ := QuasiDihedralFusion.sq_mem_range_toPGL (F := F₀) (ρ ⟨u, huH⟩)
    exact ⟨(QuotientGroup.mk s : GorensteinWalter.PSL2 F₀), by
      rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]; exact hs⟩
  have hz2' : orderOf (⟨z, hzH⟩ : ↥H₀) = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
  have hzL : (⟨z, hzH⟩ : ↥H₀) ∈ L₀ := hinv _ hzM hz2'
  set W : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({w} : Set G) with hW
  have hH₀W : H₀ ≤ W := fun h hh => ⟨hKC hh.1, hh.2⟩
  have hΛH₀ : L₀.map H₀.subtype ≤ H₀ := Subgroup.map_subtype_le L₀
  have hΛ2 : TwoComponents.IsTwoComponent ((L₀.map H₀.subtype).subgroupOf H₀) := by
    have : (L₀.map H₀.subtype).subgroupOf H₀ = L₀ :=
      Subgroup.comap_map_eq_self_of_injective H₀.subtype_injective L₀
    rw [this]
    exact hL₀
  have hnorm : (H₀.subgroupOf W).Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ H₀ := hn
    refine Subgroup.mem_subgroupOf.2 ⟨hKN (g : G) g.2.1 (n : G) hn'.1, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2.2 hn'.2) (Subgroup.inv_mem _ g.2.2)⟩
  have hΛW := TwoComponentTransport.extend_nested (L₀.map H₀.subtype) H₀ W hΛH₀ hH₀W
    (Subgroup.Normal.isSubnormal hnorm) hΛ2
  refine ⟨L₀.map H₀.subtype, TwoThin.isPCompIn_two_iff.2 ⟨hΛH₀.trans hH₀W, hΛW⟩, ?_,
    ⟨⟨z, hzH⟩, hzL, rfl⟩, ?_, ?_⟩
  · intro g hg
    obtain ⟨l, -, rfl⟩ := hg
    exact l.2.1
  · let eΛ : ↥L₀ ≃* ↥(L₀.map H₀.subtype) :=
      Subgroup.equivMapOfInjective L₀ H₀.subtype H₀.subtype_injective
    let eq1 : (↥L₀ ⧸ pPrimeCore 2 ↥L₀) ≃* kBar (L₀.map H₀.subtype) :=
      QuotientGroup.congr _ _ eΛ (pPrimeCore_map_iso 2 eΛ)
    exact hasL2Model_of_l2 ⟨hodd, h3⟩ (eq1.symm.trans (eL.trans (eS.symm.trans (L2.equivPSL F₀).symm)))
  · let eΛ : ↥L₀ ≃* ↥(L₀.map H₀.subtype) :=
      Subgroup.equivMapOfInjective L₀ H₀.subtype H₀.subtype_injective
    let eq1 : (↥L₀ ⧸ pPrimeCore 2 ↥L₀) ≃* kBar (L₀.map H₀.subtype) :=
      QuotientGroup.congr _ _ eΛ (pPrimeCore_map_iso 2 eΛ)
    let eK : kBar (L₀.map H₀.subtype) ≃* ↥S := eq1.symm.trans eL
    have hSc : Subgroup.center ↥S = ⊥ := center_eq_bot_of_simple' hSs hSna
    have hmap : (Subgroup.center (kBar (L₀.map H₀.subtype))).map eK.toMonoidHom =
        Subgroup.center ↥S := Subgroup.map_center_eq eK
    rw [hSc] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ eK.injective).1 hmap

end LayerComp

end CFSG.GH74.GLS.C3.Layer1.Thm1P31c
