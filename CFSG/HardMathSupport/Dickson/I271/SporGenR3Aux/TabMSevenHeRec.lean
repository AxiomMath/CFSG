module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenRec
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.StrongHSHe
public import CFSG.Sporadic.HeldB.InnerClass
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG.Blueprint CFSG.Open CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Dickson.I271.TabMFive
open CFSG.Sporadic.HeldB (heP card_heP heGenPerm heGenPerm_mem heT1P heT1P_mem orderOf_heA0
  orderOf_heT1P heA0_ne_one heT1P_ne_one card_heP_cent0 card_heP_cent1 involution_conj_cases
  heCentralizerEquiv centralizerEquiv heEquivP heP_simple heP_center_eq_bot)
open CFSG.Sporadic.Bridge (wordProd presHom presGen presHom_presGen coe_wordProd)
open CFSG.Sporadic.Bridge.TwoGen (img2)

@[expose] def HePE8 : Prop :=
  ∃ A : Subgroup (Equiv.Perm (Fin 8330)), A ≤ CFSG.Sporadic.HeldB.heP ∧
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧ 8 ≤ Nat.card ↥A

section Data

variable {G : Type} [Group G]

structure HeInvolutions (H : Subgroup G) : Prop where
  card : Nat.card ↥H = 4030387200
  cases : ∀ t ∈ H, orderOf t = 2 →
    Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) = 161280 ∨
      Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) = 21504
  conj : ∀ t ∈ H, ∀ u ∈ H, orderOf t = 2 → orderOf u = 2 →
    Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({u} : Set G)) → ∃ g ∈ H, g * u * g⁻¹ = t
  exists_A : ∃ t ∈ H, orderOf t = 2 ∧
    Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) = 161280
  exists_B : ∃ t ∈ H, orderOf t = 2 ∧
    Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) = 21504
  exists_E8 : ∃ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧
    8 ≤ Nat.card ↥A ∧ A ≤ H

structure HeClassData (K : Type) [Group K] : Prop where
  card : Nat.card K = 4030387200
  e8 : ∃ A : Subgroup K, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧
    8 ≤ Nat.card ↥A
  cls : ∃ tA tB : K, tA ^ 2 = 1 ∧ tA ≠ 1 ∧ tB ^ 2 = 1 ∧ tB ≠ 1 ∧
    (∀ g : K, g ^ 2 = 1 → g ≠ 1 → IsConj tA g ∨ IsConj tB g) ∧
    Nat.card ↥(Subgroup.centralizer ({tA} : Set K)) = 161280 ∧
    Nat.card ↥(Subgroup.centralizer ({tB} : Set K)) = 21504

theorem HeInvolutions.of_classData {K : Type} [Group K] (hK : HeClassData K) {H : Subgroup G}
    (e : ↥H ≃* K) : HeInvolutions H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard, ⟨A, hAc, hAs, hA8⟩, tA, tB, sqA, neA, sqB, neB, hcov, hcA, hcB⟩ := hK
  have hcent : ∀ s : ↥H, Nat.card ↥(H ⊓ Subgroup.centralizer ({(s : G)} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({e s} : Set K)) := fun s =>
    (card_centralizer_subtype s).symm.trans (Nat.card_congr (centralizerEquiv e s).toEquiv)
  have hcls : ∀ u : K, orderOf u = 2 →
      (IsConj tA u ∧ Nat.card ↥(Subgroup.centralizer ({u} : Set K)) = 161280) ∨
      (IsConj tB u ∧ Nat.card ↥(Subgroup.centralizer ({u} : Set K)) = 21504) := by
    intro u hu
    have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    have hu1 : u ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hu
      norm_num at hu
    rcases hcov u hu2 hu1 with h | h
    · exact Or.inl ⟨h, by rw [← card_centralizer_eq_of_isConj h]; exact hcA⟩
    · exact Or.inr ⟨h, by rw [← card_centralizer_eq_of_isConj h]; exact hcB⟩
  have hord : ∀ (t : G) (ht : t ∈ H), orderOf t = 2 → orderOf (e ⟨t, ht⟩) = 2 := by
    intro t ht ho
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact ho
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv]
    exact hcard
  · intro t ht ho
    have h1 := hcent ⟨t, ht⟩
    rcases hcls _ (hord t ht ho) with ⟨-, hc⟩ | ⟨-, hc⟩
    · exact Or.inl (h1.trans hc)
    · exact Or.inr (h1.trans hc)
  · intro t ht u hu hto huo hcard'
    have h1 := hcent ⟨t, ht⟩
    have h2 := hcent ⟨u, hu⟩
    have key : IsConj (e ⟨u, hu⟩) (e ⟨t, ht⟩) := by
      rcases hcls _ (hord t ht hto) with ⟨hct, hct'⟩ | ⟨hct, hct'⟩ <;>
        rcases hcls _ (hord u hu huo) with ⟨hcu, hcu'⟩ | ⟨hcu, hcu'⟩
      · exact hcu.symm.trans hct
      · exfalso
        rw [h1, h2, hct', hcu'] at hcard'
        norm_num at hcard'
      · exfalso
        rw [h1, h2, hct', hcu'] at hcard'
        norm_num at hcard'
      · exact hcu.symm.trans hct
    obtain ⟨c, hc⟩ := isConj_iff.1 key
    refine ⟨((e.symm c : ↥H) : G), (e.symm c).2, ?_⟩
    have h3 : e.symm c * ⟨u, hu⟩ * (e.symm c)⁻¹ = ⟨t, ht⟩ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hc
    exact congrArg Subtype.val h3
  · have ho : orderOf (e.symm tA) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime sqA neA
    refine ⟨((e.symm tA : ↥H) : G), (e.symm tA).2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe]
      exact ho
    · rw [hcent (e.symm tA), MulEquiv.apply_symm_apply]
      exact hcA
  · have ho : orderOf (e.symm tB) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime sqB neB
    refine ⟨((e.symm tB : ↥H) : G), (e.symm tB).2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe]
      exact ho
    · rw [hcent (e.symm tB), MulEquiv.apply_symm_apply]
      exact hcB
  · let ψ : K →* G := H.subtype.comp e.symm.toMonoidHom
    have hψ : Function.Injective ψ := H.subtype_injective.comp e.symm.injective
    refine ⟨A.map ψ, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      calc ψ a * ψ b = ψ (a * b) := (map_mul ψ a b).symm
        _ = ψ (b * a) := by rw [hAc a ha b hb]
        _ = ψ b * ψ a := map_mul ψ b a
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hAs a ha, map_one]
    · rw [Subgroup.card_map_of_injective hψ]
      exact hA8
    · rintro _ ⟨a, -, rfl⟩
      exact (e.symm a).2

end Data

section ClassData


theorem heClassData (hE8 : HePE8) : HeClassData ↥heP := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hAP, hAc, hAs, hA8⟩ := hE8
  have hA2 : heGenPerm 0 ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (heGenPerm 0)
    rwa [orderOf_heA0] at h
  have hB2 : heT1P ^ 2 = 1 := by
    have h := pow_orderOf_eq_one heT1P
    rwa [orderOf_heT1P] at h
  refine ⟨card_heP, ⟨A.subgroupOf heP, ?_, ?_, ?_⟩,
    ⟨heGenPerm 0, heGenPerm_mem (by norm_num)⟩, ⟨heT1P, heT1P_mem⟩,
    Subtype.ext hA2, fun h => heA0_ne_one (congrArg Subtype.val h),
    Subtype.ext hB2, fun h => heT1P_ne_one (congrArg Subtype.val h), ?_, ?_, ?_⟩
  · intro a ha b hb
    exact Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
  · intro a ha
    exact Subtype.ext (hAs _ (Subgroup.mem_subgroupOf.1 ha))
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv]
    exact hA8
  · intro g hg2 hg1
    have ho : orderOf (g : Equiv.Perm (Fin 8330)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime hg2 hg1
    rcases involution_conj_cases g.2 ho with ⟨c, hc, hgc⟩ | ⟨c, hc, hgc⟩
    · exact Or.inl (isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hgc.symm⟩)
    · exact Or.inr (isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hgc.symm⟩)
  · rw [Nat.card_congr (heCentralizerEquiv _).toEquiv]
    exact card_heP_cent0
  · rw [Nat.card_congr (heCentralizerEquiv _).toEquiv]
    exact card_heP_cent1

theorem HeInvolutions.of_equiv (hE8 : HePE8) {G : Type} [Group G] {H : Subgroup G}
    (e : ↥H ≃* ↥CFSG.Sporadic.HeldB.heP) : HeInvolutions H :=
  HeInvolutions.of_classData (heClassData hE8) e

end ClassData

section Center


theorem center_eq_bot_of_equiv_heP {K : Type*} [Group K] (e : K ≃* ↥heP) :
    Subgroup.center K = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : e z ∈ Subgroup.center ↥heP := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro b
    have h2 := congrArg e (hz (e.symm b))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  rw [heP_center_eq_bot, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (h1.trans (map_one e).symm)

end Center

section Bound


theorem centSevenA_of_bounds (hE8 : HePE8) {G : Type} [Group G] [Finite G]
    (hcls : ∀ t : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * monsterBabyOrder ∨
        Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder)
    (h2A : ∀ t k : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * monsterBabyOrder →
      orderOf k = 7 → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
        1128960)
    (h2B : ∀ t k : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder →
      orderOf k = 7 → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
        150528)
    (hG5 : ∀ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card ↥A → ∃ u ∈ A, orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = twoBCentralizerOrder)
    {k : G} (hk : orderOf k = 7) {H : Subgroup G}
    (hHk : H ≤ Subgroup.centralizer ({k} : Set G)) (e : ↥H ≃* ↥CFSG.Sporadic.HeldB.heP) :
    Nat.card ↥(Subgroup.centralizer ({k} : Set G)) ≤ 7 * 4030387200 := by
  have hHI : HeInvolutions H := HeInvolutions.of_equiv hE8 e
  have hKH : ∀ g ∈ Subgroup.zpowers k, g ∈ H → g = 1 := fun _ hg hgH =>
    eq_one_of_mem_zpowers_of_center hHk (center_eq_bot_of_equiv_heP e) hg hgH
  have hcomm : ∀ t ∈ H, t * k = k * t := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.1 (hHk ht)
  have hlow : ∀ t ∈ H, 7 * Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) ≤
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) :=
    fun t ht => mul_card_le_cent_inf' hk hHk hKH ht
  have hnotA : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder →
      Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) = 21504 := by
    intro t ht ho hc
    rcases hHI.cases t ht ho with h | h
    · exfalso
      have h1 := hlow t ht
      have h2 := h2B t k ho hc hk (hcomm t ht)
      rw [h] at h1
      omega
    · exact h
  obtain ⟨A, hAc, hAs, hA8, hAH⟩ := hHI.exists_E8
  obtain ⟨u, huA, huo, huc⟩ := hG5 A hAc hAs hA8
  have huH : u ∈ H := hAH huA
  have hu3 : Nat.card ↥(H ⊓ Subgroup.centralizer ({u} : Set G)) = 21504 :=
    hnotA u huH huo huc
  have hBcls : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) = 21504 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder := by
    intro t ht ho hc
    obtain ⟨g, -, hgu⟩ := hHI.conj t ht u huH ho huo (hc.trans hu3.symm)
    rw [← hgu, card_centralizer_conj]
    exact huc
  have hup : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
        7 * Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) := by
    intro t ht ho
    rcases hHI.cases t ht ho with h | h
    · rw [h]
      rcases hcls t ho with hta | htb
      · exact (h2A t k ho hta hk (hcomm t ht)).trans (by norm_num)
      · exact (h2B t k ho htb hk (hcomm t ht)).trans (by norm_num)
    · rw [h]
      exact (h2B t k ho (hBcls t ht ho h) hk (hcomm t ht)).trans (by norm_num)
  obtain ⟨t₀, ht₀, ho₀, hc₀⟩ := hHI.exists_A
  obtain ⟨t₁, ht₁, ho₁, hc₁⟩ := hHI.exists_B
  have hrec := card_centralizer_le_of_involutions' (by norm_num) (by norm_num) hk hKH hHk hup
    hHI.conj ht₀ ht₁ ho₀ ho₁ (by rw [hc₀, hc₁]; norm_num)
  have h7 := hrec.2
  rw [hHI.card] at h7
  exact h7

end Bound

section Shape


theorem tabMSeven_shapeRkAt'_of_heP (hOut : SporadicOuterLeTwo) {G : Type} [Group G] [Finite G]
    {k : G} (hk : orderOf k = 7) {H : Subgroup G}
    (hHk : H ≤ Subgroup.centralizer ({k} : Set G)) (e : ↥H ≃* ↥CFSG.Sporadic.HeldB.heP)
    (hbound : Nat.card ↥(Subgroup.centralizer ({k} : Set G)) ≤ 7 * 4030387200) :
    ShapeRkAt' 7 (GoodSpor 7 [.He]) (RkSpor 7 [.He]) k := by
  have hcard : Nat.card ↥H = 4030387200 := (Nat.card_congr e.toEquiv).trans card_heP
  have hZ : Subgroup.center ↥H = ⊥ := center_eq_bot_of_equiv_heP e
  haveI : IsSimpleGroup ↥heP := heP_simple
  have hs : IsSimpleGroup ↥H := MulEquiv.isSimpleGroup e
  have hnab : ∃ a b : ↥H, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have htop : Subgroup.center ↥H = ⊤ :=
      eq_top_iff.2 fun z _ => Subgroup.mem_center_iff.2 fun g => hc g z
    have h1 : Nat.card ↥H = 1 := by
      rw [← Subgroup.card_top (G := ↥H), ← htop, hZ, Subgroup.card_bot]
    rw [hcard] at h1
    norm_num at h1
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b₀ : NativeSporadic.He ≃* (TauCeti.CFSGIndex.sporadic .He).Group := b
  exact tabMSeven_shapeRkAt'_of_simple (by norm_num)
    (fun T T' _ _ f h => GoodSpor.of_equiv f h) (fun T T' _ _ f h => RkSpor.of_equiv f h)
    hk hHk hs hnab (by rw [hcard]; norm_num) (by rw [hcard]; exact hbound)
    (Or.inr (Or.inr ⟨.He, List.mem_singleton_self _, ⟨e.trans (heEquivP.symm.trans b₀)⟩⟩))
    (rkSpor_He_seven hOut hZ)

end Shape

section Relators


theorem tabMSeven_nonempty_mulEquiv_heP_of_relators {G : Type} [Group G] {x y : G}
    (hrel : ∀ v ∈ TauCeti.Sporadic.hePresentation.relatorLetters,
      CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 x y) v = 1)
    (hx : x ≠ 1) :
    Nonempty (↥(Subgroup.closure ({x, y} : Set G)) ≃* ↥CFSG.Sporadic.HeldB.heP) := by
  set P := TauCeti.Sporadic.hePresentation with hP
  set K := Subgroup.closure ({x, y} : Set G) with hK
  let x' : ↥K := ⟨x, Subgroup.subset_closure (by simp)⟩
  let y' : ↥K := ⟨y, Subgroup.subset_closure (by simp)⟩
  have himg : (fun i => ((img2 x' y' i : ↥K) : G)) = img2 x y := by
    funext i
    unfold img2
    split_ifs <;> rfl
  have hrel' : ∀ v ∈ P.relatorLetters, wordProd (img2 x' y') v = 1 := fun v hv =>
    Subtype.ext (((coe_wordProd (img2 x' y') v).trans
      (congrArg (fun f => wordProd f v) himg)).trans (hrel v hv))
  set ψ := presHom P (img2 x' y') hrel' with hψ
  have h0 : 0 < P.generatorCount := by
    rw [hP, CFSG.Sporadic.Bridge.He.generatorCount_eq]
    norm_num
  have h1 : 1 < P.generatorCount := by
    rw [hP, CFSG.Sporadic.Bridge.He.generatorCount_eq]
    norm_num
  have hψ0 : ψ (presGen P 0) = x' := by
    rw [hψ, presHom_presGen P _ hrel' h0]
    simp [img2]
  have hψ1 : ψ (presGen P 1) = y' := by
    rw [hψ, presHom_presGen P _ hrel' h1]
    simp [img2]
  have hclosure : Subgroup.closure ({x', y'} : Set ↥K) = ⊤ := by
    have hpre : ((↑) : ↥K → G) ⁻¹' ({x, y} : Set G) = ({x', y'} : Set ↥K) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff]
      rfl
    rw [← hpre]
    exact Subgroup.closure_closure_coe_preimage
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hclosure, Subgroup.closure_le]
    rintro g (h | h)
    · exact ⟨presGen P 0, by rw [hψ0, h]⟩
    · rw [Set.mem_singleton_iff] at h
      exact ⟨presGen P 1, by rw [hψ1, h]⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b' : NativeSporadic.He ≃* P.Group := b
  haveI : IsSimpleGroup P.Group :=
    @MulEquiv.isSimpleGroup _ _ _ Units.instGroup CFSG.Sporadic.He.isSimpleGroup_He b'.symm
  have hker : ψ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      have hmem : presGen P 0 ∈ ψ.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hψ0] at hmem
      exact hx (congrArg Subtype.val hmem)
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hker
  exact ⟨(MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm.trans (b'.symm.trans heEquivP)⟩

end Relators

section Main


theorem tabMSeven_shape_and_bound_of_heP (hOut : SporadicOuterLeTwo) (hE8 : HePE8) {G : Type}
    [Group G] [Finite G]
    (hcls : ∀ t : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * monsterBabyOrder ∨
        Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder)
    (h2A : ∀ t k : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * monsterBabyOrder →
      orderOf k = 7 → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
        1128960)
    (h2B : ∀ t k : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder →
      orderOf k = 7 → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
        150528)
    (hG5 : ∀ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card ↥A → ∃ u ∈ A, orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = twoBCentralizerOrder)
    {k : G} (hk : orderOf k = 7) {H : Subgroup G}
    (hHk : H ≤ Subgroup.centralizer ({k} : Set G)) (e : ↥H ≃* ↥CFSG.Sporadic.HeldB.heP) :
    ShapeRkAt' 7 (GoodSpor 7 [.He]) (RkSpor 7 [.He]) k ∧
      Nat.card ↥(Subgroup.centralizer ({k} : Set G)) ≤ 7 * 4030387200 := by
  have hb := centSevenA_of_bounds hE8 hcls h2A h2B hG5 hk hHk e
  exact ⟨tabMSeven_shapeRkAt'_of_heP hOut hk hHk e hb, hb⟩

end Main

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
