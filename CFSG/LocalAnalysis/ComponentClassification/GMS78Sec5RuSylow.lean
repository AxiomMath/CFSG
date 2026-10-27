module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSimAct
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNormA

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim

namespace RuSimCode

theorem linApply_linId (t : Fin 8) : linApply linId t = t := by
  revert t
  decide

end RuSimCode

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

theorem card_T_eq
    (hS : SzR G L T R 1 y d) (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) :
    Nat.card T = 2 ^ 8 := by
  obtain ⟨hT₁, -, -⟩ := sylow_of_benderBorel hS.oddCenter (by norm_num)
    (Asc76X.fusionBenderBorel_of_mulEquiv_sz hS.one_le hS.iso.some) hS.sec3.isSylowOf_T₁
  have hN : T ⊓ centralizer (L : Set G) ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    fun x hx => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht =>
      (mem_centralizer_iff.mp (mem_inf.mp hx).2 t (mem_inf.mp ht).2))
  have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hN
  rw [hS.sec3.inf_eq_bot_of_odd hS.oddCenter, card_bot, mul_one, hT₁, h4] at h1
  rw [hS.eq_gmsW]
  rw [h1]
  norm_num

theorem inf_centralizer_eq_T
    (hS : SzR G L T R 1 y d)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hTS : T ≤ S) {e : G}
    (he : e ∈ T ⊓ centralizer (L : Set G)) (he1 : e ≠ 1) :
    S ⊓ centralizer ({e} : Set G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTC : T ≤ centralizer ({e} : Set G) := by
    intro t ht
    rw [mem_centralizer_singleton_iff]
    have hW : t ∈ gmsW L T := by rw [← hS.eq_gmsW]; exact ht
    obtain ⟨-, -, -, hVC, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
    exact (mem_centralizer_iff.mp (hVC (mem_sup_right he)) t hW)
  have hle : S ⊓ centralizer ({e} : Set G) ≤ normalizer (L : Set G) := by
    intro x hx
    have hx' := (mem_inf.mp hx).2
    rw [hCe e he he1] at hx'
    exact (sup_le (inf_le_right.trans hS.sec3.centralizer_le_normalizer) le_normalizer) hx'
  exact hS.sec3.sylow.eq_of_le (le_inf hTS hTC) hle (hS2.to_le inf_le_left)

theorem exists_sq_eq
    (hS : SzR G L T R 1 y d) {a : G} (ha : a ∈ gmsA L T) : ∃ t ∈ T ⊓ L, t ^ 2 = a := by
  by_cases ha1 : a = 1
  · exact ⟨1, one_mem _, by rw [ha1, one_pow]⟩
  obtain ⟨t₀, ht₀, ht₀A⟩ := hS.exists_mem_T₁_not_mem_gmsA
  have h2 : t₀ ^ 2 ∈ gmsA L T := hS.facts.sq_mem t₀ ht₀
  have h21 : t₀ ^ 2 ≠ 1 := fun h => ht₀A ((hS.facts.sylow hS.sec3).2.2 t₀ ht₀ h)
  obtain ⟨m, hm⟩ := hS.torus.trans _ h2 a ha h21 ha1
  have hyN : y ^ m ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    pow_mem (mem_inf.mp hS.torus.mem).2 m
  refine ⟨(y ^ m)⁻¹ * t₀ * y ^ m, ?_, ?_⟩
  · have := (mem_normalizer_iff.mp (inv_mem hyN) t₀).mp ht₀
    simpa using this
  · rw [← hm, sq, sq]
    group

theorem le_card_inf_centralizer
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d) {w : G}
    (hw : w ∈ R) : Nat.card T ≤ Nat.card (R ⊓ centralizer ({w} : Set G) : Subgroup G) := by
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  have hcomm : ∀ z ∈ R, w * z * w⁻¹ * z⁻¹ ∈ gmsA L T := fun z hz =>
    hS.commutator_mem_gmsA_of_isX h34 hX hw hz
  have hcent : ∀ b ∈ gmsA L T, ∀ z ∈ R, z * b = b * z := fun b hb z hz =>
    hS.commute_gmsA hz hb
  let f : R →* gmsA L T :=
    { toFun := fun z => ⟨w * (z : G) * w⁻¹ * (z : G)⁻¹, hcomm z z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun z z' => Subtype.ext (by
        show w * ((z : G) * (z' : G)) * w⁻¹ * ((z : G) * (z' : G))⁻¹ =
          (w * (z : G) * w⁻¹ * (z : G)⁻¹) * (w * (z' : G) * w⁻¹ * (z' : G)⁻¹)
        have h1 := hcent _ (hcomm z' z'.2) _ (inv_mem z.2)
        calc w * ((z : G) * (z' : G)) * w⁻¹ * ((z : G) * (z' : G))⁻¹ =
            (w * (z : G) * w⁻¹) * ((w * (z' : G) * w⁻¹ * (z' : G)⁻¹) * (z : G)⁻¹) := by group
          _ = (w * (z : G) * w⁻¹) * ((z : G)⁻¹ * (w * (z' : G) * w⁻¹ * (z' : G)⁻¹)) := by
            rw [h1]
          _ = (w * (z : G) * w⁻¹ * (z : G)⁻¹) * (w * (z' : G) * w⁻¹ * (z' : G)⁻¹) := by
            group) }
  have hker : f.ker = (R ⊓ centralizer ({w} : Set G)).subgroupOf R := by
    ext z
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : w * (z : G) * w⁻¹ * (z : G)⁻¹ = 1 := congrArg Subtype.val h
      refine ⟨z.2, ?_⟩
      calc (z : G) * w = (w * (z : G) * w⁻¹ * (z : G)⁻¹)⁻¹ * (w * z) := by group
        _ = w * z := by rw [h1, inv_one, one_mul]
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show w * (z : G) * w⁻¹ * (z : G)⁻¹ = 1
      rw [← h]
      group
  have h1 := Subgroup.index_ker f
  rw [hker] at h1
  have h2 : Nat.card f.range ≤ Nat.card (gmsA L T) := card_le_card_group _ |>.trans le_rfl
  have hRc := hS.card_R hR₂
  obtain ⟨hA₁c, -, -⟩ := hS.facts.sylow hS.sec3
  have h3 := ((R ⊓ centralizer ({w} : Set G)).subgroupOf R).card_mul_index
  rw [h1, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h3
  have h5 : Nat.card ((R ⊓ centralizer ({w} : Set G) : Subgroup G)) * Nat.card (gmsA L T) ≥
      Nat.card R := by
    rw [← h3]
    exact Nat.mul_le_mul_left _ h2
  rw [hRc, hA₁c] at h5
  have hq : 0 < 2 ^ (2 * 1 + 1) := by positivity
  nlinarith [h5]

@[expose] def IsAct (L T : Subgroup G) (v : G → BinaryGaloisField (2 * 1 + 1)) (g : G)
    (r : Lin8) : Prop :=
  ∀ b ∈ gmsA L T, ∀ t, v b = RuCode.toGF t → v (g * b * g⁻¹) = RuCode.toGF (linApply r t)

section IsAct

variable {v : G → BinaryGaloisField (2 * 1 + 1)}
  {φ : G → BinaryGaloisField (2 * 1 + 1) × BinaryGaloisField (2 * 1 + 1) ×
    BinaryGaloisField (2 * 1 + 1)}
  {c e : BinaryGaloisField (2 * 1 + 1)} {Λ : AddSubgroup (BinaryGaloisField (2 * 1 + 1))}

omit [Finite G] in
theorem eq_of_v_eq (hC : RCoords L T R R₂ 1 v φ c e Λ) {b b' : G} (hb : b ∈ gmsA L T)
    (hb' : b' ∈ gmsA L T) (h : v b = v b') : b = b' := by
  have hv1 : v 1 = 0 := by
    have h2 := hC.v_mul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one (1 : G)] at h2
    linear_combination -h2
  have h1 : v (b * b'⁻¹) = 0 := by
    rw [hC.v_mul _ hb _ (inv_mem hb'), h, ← hC.v_mul _ hb' _ (inv_mem hb'), mul_inv_cancel, hv1]
  exact mul_inv_eq_one.mp (hC.v_inj _ (mul_mem hb (inv_mem hb')) h1)

omit [Finite G] in
theorem IsAct.unique (hC : RCoords L T R R₂ 1 v φ c e Λ) {g : G} {r r' : Lin8}
    (h : IsAct L T v g r) (h' : IsAct L T v g r') : r = r' := by
  have key : ∀ t, linApply r t = linApply r' t := by
    intro t
    obtain ⟨b, hb, hbt⟩ := hC.v_surj (RuCode.toGF t)
    exact RuCode.toGF_injective ((h b hb t hbt).symm.trans (h' b hb t hbt))
  obtain ⟨a₁, a₂, a₃⟩ := r
  obtain ⟨a₁', a₂', a₃'⟩ := r'
  have h1 := key 1
  have h2 := key 2
  have h4 := key 4
  rw [RuSimCode.linApply_one, RuSimCode.linApply_one] at h1
  rw [RuSimCode.linApply_two, RuSimCode.linApply_two] at h2
  rw [RuSimCode.linApply_four, RuSimCode.linApply_four] at h4
  simp only at h1 h2 h4
  rw [h1, h2, h4]

omit [Finite G] in
theorem IsAct.mul {g h : G} {r r' : Lin8} (hh : h ∈ normalizer (gmsA L T : Set G))
    (hg : IsAct L T v g r) (hh' : IsAct L T v h r') : IsAct L T v (g * h) (linComp r r') := by
  intro b hb t hbt
  have hhb : h * b * h⁻¹ ∈ gmsA L T := (mem_normalizer_iff.mp hh b).mp hb
  have h1 := hh' b hb t hbt
  have h2 := hg _ hhb _ h1
  rw [RuSimCode.linApply_linComp, ← h2]
  congr 1
  group

omit [Finite G] in
theorem isAct_one : IsAct L T v 1 linId := by
  intro b _ t hbt
  rw [show (1 : G) * b * 1⁻¹ = b by group, hbt, RuSimCode.linApply_linId]

omit [Finite G] in
theorem IsAct.inv_mul_mem_centralizer (hC : RCoords L T R R₂ 1 v φ c e Λ) {g h : G} {r : Lin8}
    (hgN : g ∈ normalizer (gmsA L T : Set G)) (hhN : h ∈ normalizer (gmsA L T : Set G))
    (hg : IsAct L T v g r) (hh : IsAct L T v h r) : g⁻¹ * h ∈ centralizer (gmsA L T : Set G) := by
  rw [mem_centralizer_iff]
  intro b hb
  obtain ⟨t, ht⟩ := RuCode.toGF_surjective (v b)
  have hgb : g * b * g⁻¹ ∈ gmsA L T := (mem_normalizer_iff.mp hgN b).mp hb
  have hhb : h * b * h⁻¹ ∈ gmsA L T := (mem_normalizer_iff.mp hhN b).mp hb
  have h1 := eq_of_v_eq hC hgb hhb ((hg b hb t ht.symm).trans (hh b hb t ht.symm).symm)
  calc b * (g⁻¹ * h) = g⁻¹ * (g * b * g⁻¹) * h := by group
    _ = g⁻¹ * (h * b * h⁻¹) * h := by rw [h1]
    _ = g⁻¹ * h * b := by group

end IsAct

omit [Finite G] in
theorem card_le_length_mul_card {α : Type*} [DecidableEq α] {H K : Subgroup G} (hKH : K ≤ H)
    (f : G → α) (l : List α) (hf : ∀ a ∈ H, f a ∈ l)
    (hinj : ∀ a ∈ H, ∀ b ∈ H, f a = f b → a⁻¹ * b ∈ K) : Nat.card H ≤ l.length * Nat.card K := by
  have hF : ∀ q : H ⧸ K.subgroupOf H, f ((q.out : H) : G) ∈ l.toFinset := fun q =>
    List.mem_toFinset.mpr (hf _ (q.out).2)
  have hinj' : Function.Injective
      (fun q : H ⧸ K.subgroupOf H => (⟨f ((q.out : H) : G), hF q⟩ : l.toFinset)) := by
    intro q q' h
    have h1 : f ((q.out : H) : G) = f ((q'.out : H) : G) := congrArg Subtype.val h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, mem_subgroupOf]
    exact hinj _ (q.out).2 _ (q'.out).2 h1
  have hidx : (K.subgroupOf H).index ≤ l.length :=
    calc (K.subgroupOf H).index = Nat.card (H ⧸ K.subgroupOf H) := rfl
      _ ≤ Nat.card l.toFinset := Nat.card_le_card_of_injective _ hinj'
      _ = l.toFinset.card := Nat.card_eq_finsetCard _
      _ ≤ l.length := List.toFinset_card_le l
  have h1 := (K.subgroupOf H).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv] at h1
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul_right _ hidx

theorem isSylowOf_top_of_isSylowOf_normalizer
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCV : centralizer (gmsV L T : Set G) = T)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G))) {S : Subgroup G}
    (hSN : IsSylowOf 2 S (normalizer (R : Set G))) : IsSylowOf 2 S ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hST
  obtain ⟨P, -, x, hxP, hxS, hxnS⟩ := exists_mem_normalizer_of_not_isSylowOf hSN.isPGroup hST
  have hRS : R ≤ S := by
    have hP : IsPGroup 2 (S ⊔ R : Subgroup G) :=
      hSN.isPGroup.to_sup_of_normal_right' hS.isR.isPGroup hSN.le
    exact le_sup_right.trans (hSN.eq_of_le le_sup_left (sup_le hSN.le le_normalizer) hP).le
  have hxR : x ∉ normalizer (R : Set G) := by
    intro hxR
    have hP : IsPGroup 2 (S ⊔ zpowers x : Subgroup G) :=
      hSN.isPGroup.to_sup_of_normal_left' (P.isPGroup'.to_le (zpowers_le.mpr hxP))
        (zpowers_le.mpr hxS)
    have heq := hSN.eq_of_le le_sup_left (sup_le hSN.le (zpowers_le.mpr hxR)) hP
    have h1 : x ∈ S ⊔ zpowers x := (le_sup_right : zpowers x ≤ S ⊔ zpowers x) (mem_zpowers x)
    rw [heq] at h1
    exact hxnS h1
  have hT₀el := hS.sec3.isElemAbelian_T₀ hS.foundation
  have hTS : T ≤ S := hS.T_le.trans hRS
  have hxSmem : ∀ s ∈ S, x * s * x⁻¹ ∈ S := fun s hs => (mem_normalizer_iff.mp hxS s).mp hs
  have hxSmem' : ∀ s ∈ S, x⁻¹ * s * x ∈ S := fun s hs => by
    simpa using (mem_normalizer_iff.mp (inv_mem hxS) s).mp hs
  obtain ⟨-, -, -, hVC, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have hTE : ∀ t ∈ T, ∀ e ∈ T ⊓ centralizer (L : Set G), t * e = e * t := by
    intro t ht e he
    have hW : t ∈ gmsW L T := by rw [← hS.eq_gmsW]; exact ht
    exact mem_centralizer_iff.mp (hVC (mem_sup_right he)) t hW
  set C := rightConjugate T x⁻¹ with hCdef
  have hmemC : ∀ z, z ∈ C ↔ x⁻¹ * z * x ∈ T := fun z => by
    rw [hCdef, mem_rightConjugate_iff, inv_inv]
  have hcardC : Nat.card C = 2 ^ 8 := by rw [hCdef, rightConjugate_card, card_T_eq hS h4]
  by_cases hA : ∃ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 ∧ x * e * x⁻¹ ∈ R
  ·
    obtain ⟨e, he, he1, hxe⟩ := hA
    have hle : R ⊓ centralizer ({x * e * x⁻¹} : Set G) ≤ C := by
      intro s hs
      obtain ⟨hsR, hsc⟩ := mem_inf.mp hs
      rw [hmemC, ← inf_centralizer_eq_T hS hCe hSN.isPGroup hTS he he1]
      refine mem_inf.mpr ⟨hxSmem' s (hRS hsR), ?_⟩
      rw [mem_centralizer_singleton_iff] at hsc ⊢
      calc x⁻¹ * s * x * e = x⁻¹ * (s * (x * e * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * e * x⁻¹) * s) * x := by rw [hsc]
        _ = e * (x⁻¹ * s * x) := by group
    have heq : R ⊓ centralizer ({x * e * x⁻¹} : Set G) = C :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [hcardC, ← card_T_eq hS h4]
        exact le_card_inf_centralizer hS h34 hR₂ hxe)
    have hxT : ∀ t ∈ T, x * t * x⁻¹ ∈ R := by
      intro t ht
      have h1 : x * t * x⁻¹ ∈ C := by
        rw [hmemC]
        simpa [mul_assoc] using ht
      rw [← heq] at h1
      exact (mem_inf.mp h1).1
    obtain ⟨X, hX⟩ := hS.exists_isX h34
    have hxA : x ∈ normalizer (gmsA L T : Set G) := by
      refine mem_normalizer_of_conj_mem_of_finite fun a ha => ?_
      obtain ⟨t, ht, rfl⟩ := exists_sq_eq hS ha
      have h1 := hS.sq_mem_gmsA_of_mem_R h34 hX (hxT t (mem_inf.mp ht).1)
      have h2 : (x * t * x⁻¹) ^ 2 = x * t ^ 2 * x⁻¹ := by
        simp only [sq]
        group
      rwa [h2] at h1
    rw [normalizer_gmsA_eq hS h34 hR₂ h4 hCV hCe hCL hNS] at hxA
    exact hxR hxA
  push Not at hA
  obtain ⟨u, hu, w, hw, hu1, hw1, huw⟩ := exists_two_ne_one_of_four_le h4.ge
  have hsq : ∀ s ∈ T ⊓ centralizer (L : Set G), s * s = 1 := fun s hs => by
    rw [← sq]
    exact hT₀el.2 s hs
  have huw1 : u * w ≠ 1 := by
    intro h
    apply huw
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (hsq u hu)]
  have hcuw : u * w = w * u := by
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hsq u hu)
    have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hsq w hw)
    have huw' : (u * w)⁻¹ = u * w := inv_eq_of_mul_eq_one_right (hsq _ (mul_mem hu hw))
    rw [← huw', mul_inv_rev, hu', hw']
  have h0 := ruSim0_check
  obtain ⟨v, φ, c, e, Λ, hC⟩ := hS.exists_rCoords h34 hR₂
  obtain ⟨dd, hdd, hΛ, -, -, hact⟩ := hS.exists_action h34 hR₂ h4 hNS hC
  choose! rOf hrGL hrA hrR using hact
  have hNA : ∀ g ∈ normalizer (R : Set G), g ∈ normalizer (gmsA L T : Set G) :=
    fun g hg => hS.normalizer_le_normalizer_gmsA hR₂ hg
  have hNRC := normalizer_inf_centralizer_eq hS h34 hR₂ h4 hCV
  have hmul : ∀ g ∈ normalizer (R : Set G), ∀ h ∈ normalizer (R : Set G),
      rOf (g * h) = linComp (rOf g) (rOf h) := fun g hg h hh =>
    IsAct.unique hC (hrA _ (mul_mem hg hh)) (IsAct.mul (hNA h hh) (hrA g hg) (hrA h hh))
  have hone : rOf 1 = linId := IsAct.unique hC (hrA 1 (one_mem _)) isAct_one
  have hRof : ∀ a ∈ normalizer (R : Set G), ∀ b ∈ normalizer (R : Set G), rOf a = rOf b →
      a⁻¹ * b ∈ R := by
    intro a ha b hb h
    rw [← hNRC]
    refine mem_inf.mpr ⟨mul_mem (inv_mem ha) hb, ?_⟩
    have hb' : IsAct L T v b (rOf a) := by rw [h]; exact hrA b hb
    exact IsAct.inv_mul_mem_centralizer hC (hNA a ha) (hNA b hb) (hrA a ha) hb'
  have hinv : ∀ g ∈ normalizer (R : Set G), g * g = 1 → g ∉ R → rOf g ∈ invList := by
    intro g hg hgg hgR
    have h1 : linComp (rOf g) (rOf g) = linId := by rw [← hmul g hg g hg, hgg, hone]
    have h2 : rOf g ≠ linId := fun h => hgR (by
      have := hRof 1 (one_mem _) g hg (by rw [hone, h])
      rwa [inv_one, one_mul] at this)
    simp only [invList, List.mem_filter]
    exact ⟨hrGL g hg, by simp [h1, h2]⟩
  have hcomm : ∀ g ∈ normalizer (R : Set G), ∀ h ∈ normalizer (R : Set G), g * h = h * g →
      linComp (rOf g) (rOf h) = linComp (rOf h) (rOf g) := by
    intro g hg h hh hgh
    rw [← hmul g hg h hh, ← hmul h hh g hg, hgh]
  have hu' : u ∈ S := hTS (mem_inf.mp hu).1
  have hw' : w ∈ S := hTS (mem_inf.mp hw).1
  have hg₁N : x * u * x⁻¹ ∈ normalizer (R : Set G) := hSN.le (hxSmem u hu')
  have hg₂N : x * w * x⁻¹ ∈ normalizer (R : Set G) := hSN.le (hxSmem w hw')
  have he₁₂ : (x * u * x⁻¹) * (x * w * x⁻¹) = x * (u * w) * x⁻¹ := by group
  have he₂₁ : (x * w * x⁻¹) * (x * u * x⁻¹) = x * (u * w) * x⁻¹ := by
    rw [hcuw]
    group
  have hr₁ : rOf (x * u * x⁻¹) ∈ invList := hinv _ hg₁N
    (by rw [show x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ by group, hsq u hu]; group)
    (hA u hu hu1)
  have hr₂ : rOf (x * w * x⁻¹) ∈ invList := hinv _ hg₂N
    (by rw [show x * w * x⁻¹ * (x * w * x⁻¹) = x * (w * w) * x⁻¹ by group, hsq w hw]; group)
    (hA w hw hw1)
  have hr₁₂ : linComp (rOf (x * u * x⁻¹)) (rOf (x * w * x⁻¹)) ≠ linId := by
    intro h
    apply hA (u * w) (mul_mem hu hw) huw1
    rw [← he₁₂]
    have := hRof 1 (one_mem _) _ (mul_mem hg₁N hg₂N) (by rw [hone, hmul _ hg₁N _ hg₂N, h])
    rwa [inv_one, one_mul] at this
  have hne : rOf (x * u * x⁻¹) ≠ rOf (x * w * x⁻¹) := by
    intro h
    apply hr₁₂
    rw [← h, ← hmul _ hg₁N _ hg₁N,
      show x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ by group, hsq u hu,
      show x * 1 * x⁻¹ = 1 by group, hone]
  have hc₁₂ : linComp (rOf (x * u * x⁻¹)) (rOf (x * w * x⁻¹)) =
      linComp (rOf (x * w * x⁻¹)) (rOf (x * u * x⁻¹)) :=
    hcomm _ hg₁N _ hg₂N (he₁₂.trans he₂₁.symm)
  have hCS : ∀ z ∈ C, z ∈ S := by
    intro z hz
    have h1 := hxSmem _ (hTS ((hmemC z).mp hz))
    simpa [mul_assoc] using h1
  have hCN : ∀ z ∈ C, z ∈ normalizer (R : Set G) := fun z hz => hSN.le (hCS z hz)
  have hCc : ∀ z ∈ C, ∀ s ∈ T ⊓ centralizer (L : Set G),
      z * (x * s * x⁻¹) = (x * s * x⁻¹) * z := by
    intro z hz s hs
    have h1 := hTE _ ((hmemC z).mp hz) s hs
    calc z * (x * s * x⁻¹) = x * ((x⁻¹ * z * x) * s) * x⁻¹ := by group
      _ = x * (s * (x⁻¹ * z * x)) * x⁻¹ := by rw [h1]
      _ = (x * s * x⁻¹) * z := by group
  have hcount1 : Nat.card C ≤ 4 * Nat.card (C ⊓ R : Subgroup G) := by
    refine card_le_length_mul_card inf_le_left rOf
      [linId, rOf (x * u * x⁻¹), rOf (x * w * x⁻¹),
        linComp (rOf (x * u * x⁻¹)) (rOf (x * w * x⁻¹))] (fun z hz => ?_)
      (fun a ha b hb h => mem_inf.mpr ⟨mul_mem (inv_mem ha) hb, hRof a (hCN a ha) b (hCN b hb) h⟩)
    exact RuSimCode.mem_of_commute_four hr₁ hr₂ hne hc₁₂ (hrGL z (hCN z hz))
      (hcomm _ (hCN z hz) _ hg₁N (hCc z hz u hu))
      (hcomm _ (hCN z hz) _ hg₂N (hCc z hz w hw))
  set code3 := Function.surjInv RuCode.toGF3_surjective with hcode3
  have hc3 : ∀ z, RuCode.toGF3 (code3 z) = z := Function.surjInv_eq RuCode.toGF3_surjective
  have hW : ∀ z ∈ R, code3 (φ z) ∈ wList dd.1.2.2.1 dd.1.2.2.2 := by
    intro z hz
    rw [RuCode.mem_wList, ← hΛ]
    have h1 := hC.mem z hz
    rw [← hc3 (φ z)] at h1
    exact h1
  have hfix : ∀ z ∈ C ⊓ R, ∀ g ∈ normalizer (R : Set G), g * z * g⁻¹ = z →
      maskApply (adMat (rOf g)) (xApply dd.2.1 dd.1.2.2.1 dd.1.2.2.2 (code3 (φ z))) =
        xApply dd.2.1 dd.1.2.2.1 dd.1.2.2.2 (code3 (φ z)) := by
    intro z hz g hg hgz
    have h1 := hrR g hg z (mem_inf.mp hz).2 (code3 (φ z)) (hc3 _).symm
    rw [hgz] at h1
    have h2 : RuSimCode.nMap dd (rOf g) (code3 (φ z)) = code3 (φ z) := by
      apply RuCode.toGF3_injective
      rw [← h1, hc3]
    rw [← RuSimCode.xApply_nMap h0 hdd, h2]
  have hcount2 : Nat.card (C ⊓ R : Subgroup G) ≤
      4 * Nat.card (gmsA L T ⊓ (C ⊓ R) : Subgroup G) := by
    refine (card_le_length_mul_card inf_le_right
      (fun z => xApply dd.2.1 dd.1.2.2.1 dd.1.2.2.2 (code3 (φ z)))
      (all256.filter fun m => maskApply (adMat (rOf (x * u * x⁻¹))) m == m &&
        maskApply (adMat (rOf (x * w * x⁻¹))) m == m) (fun z hz => ?_)
      (fun a ha b hb h => ?_)).trans
      (Nat.mul_le_mul_right _ (RuSimCode.card_fix_le_four hr₁ hr₂ hne hc₁₂))
    · have hzC := (mem_inf.mp hz).1
      have h1 := hfix z hz _ hg₁N (by rw [← hCc z hzC u hu]; group)
      have h2 := hfix z hz _ hg₂N (by rw [← hCc z hzC w hw]; group)
      refine List.mem_filter.mpr ⟨RuSimCode.mem_all256.mpr ?_, by simp [h1, h2]⟩
      exact RuSimCode.xApply_lt (RuSimCode.steinData_lt _ hdd) _ _ _
    · refine mem_inf.mpr ⟨?_, mul_mem (inv_mem ha) hb⟩
      have haR := (mem_inf.mp ha).2
      have hbR := (mem_inf.mp hb).2
      have h1 : code3 (φ a) = code3 (φ b) := by
        rw [← RuSimCode.xiApply_xApply h0 hdd (hW a haR),
          ← RuSimCode.xiApply_xApply h0 hdd (hW b hbR)]
        exact congrArg _ h
      have h2 : φ a = φ b := by rw [← hc3 (φ a), h1, hc3]
      have hφ1 : φ 1 = 0 := (hC.ker 1 (one_mem _)).mpr (one_mem _)
      rw [← hC.ker _ (mul_mem (inv_mem haR) hbR), hC.mul _ (inv_mem haR) _ hbR, ← h2,
        ← hC.mul _ (inv_mem haR) _ haR, inv_mul_cancel, hφ1]
  obtain ⟨hA₁c, -, -⟩ := hS.facts.sylow hS.sec3
  have hcount3 : Nat.card (gmsA L T ⊓ (C ⊓ R) : Subgroup G) ≤ 8 := by
    have := Subgroup.card_le_of_le (inf_le_left : gmsA L T ⊓ (C ⊓ R) ≤ gmsA L T)
    rw [hA₁c] at this
    simpa using this
  have := hcount1.trans (Nat.mul_le_mul_left 4 (hcount2.trans (Nat.mul_le_mul_left 4 hcount3)))
  rw [hcardC] at this
  norm_num at this

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
