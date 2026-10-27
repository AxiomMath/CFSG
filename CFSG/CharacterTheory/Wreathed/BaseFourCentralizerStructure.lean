module

public import CFSG.CharacterTheory.Wreathed.ActualLocalActions
public import CFSG.CharacterTheory.Wreathed.CyclicWeakClosure

public noncomputable section

namespace CFSG.Wreathed.BaseFourCentralizerStructure

open scoped Classical

universe u v

variable {G : Type u} [Group G]

theorem odd_subgroup_le_normal_of_two_quotient [Finite G]
    (W N : Subgroup G) [N.Normal] (hodd : Odd (Nat.card W))
    (hquot : IsPGroup 2 (G ⧸ N)) : W ≤ N := by
  let f := QuotientGroup.mk' N
  let A := W.map f
  have hAodd : Odd (Nat.card A) := hodd.of_dvd_nat (W.card_map_dvd f)
  have hAp : IsPGroup 2 A := hquot.to_subgroup A
  have hAcard : Nat.card A = 1 := by
    rcases hAp.card_eq_or_dvd with hone | htwo
    · exact hone
    · exact (hAodd.not_two_dvd_nat htwo).elim
  have hAbot : A = ⊥ := (Subgroup.eq_bot_iff_card A).mpr hAcard
  intro w hw
  apply (QuotientGroup.eq_one_iff w).mp
  apply Subgroup.mem_bot.mp
  rw [← hAbot]
  exact Subgroup.mem_map_of_mem f hw

theorem normal_odd_two_quotient_eq_oddCore [Finite G]
    (N : Subgroup G) [N.Normal] (hodd : Odd (Nat.card N))
    (hquot : IsPGroup 2 (G ⧸ N)) : N = CFSG.oddCore G := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, hodd⟩
  · exact odd_subgroup_le_normal_of_two_quotient (CFSG.oddCore G) N
      (weakClosure_oddCore_card G) hquot

theorem oddCore_characteristic [Finite G] : (CFSG.oddCore G).Characteristic := by
  rw [weakClosure_oddCore_eq_pPrimeCore]
  exact CFSG.pPrimeCore_characteristic

theorem oddCore_isComplement_of_normalizer_le_centralizer [Finite G]
    (S : Sylow 2 G)
    (hNC : Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G)) :
    (CFSG.oddCore G).IsComplement' (S : Subgroup G) := by
  let N := (MonoidHom.transferSylow S hNC).ker
  have hcomp : N.IsComplement' (S : Subgroup G) :=
    MonoidHom.ker_transferSylow_isComplement' S hNC
  have hodd : Odd (Nat.card N) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    intro h
    exact S.not_dvd_index (by rw [hcomp.index_eq_card]; exact h)
  have hquot : IsPGroup 2 (G ⧸ N) :=
    S.isPGroup'.of_equiv hcomp.symm.QuotientMulEquiv.symm
  exact normal_odd_two_quotient_eq_oddCore N hodd hquot ▸ hcomp

@[expose] def directMulEquiv (H K : Subgroup G) (hcomp : H.IsComplement' K)
    (hcomm : H ≤ Subgroup.centralizer (K : Set G)) : H × K ≃* G := by
  let f : H × K →* G := {
    toFun x := (x.1 : G) * (x.2 : G)
    map_one' := by simp
    map_mul' := by
      intro x y
      have hc := Subgroup.mem_centralizer_iff.mp (hcomm y.1.property)
        (x.2 : G) x.2.property
      change ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
        ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
      calc
        _ = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by group
        _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by rw [← hc]
        _ = _ := by group }
  exact MulEquiv.ofBijective f hcomp

@[simp] theorem directMulEquiv_apply (H K : Subgroup G) (hcomp : H.IsComplement' K)
    (hcomm : H ≤ Subgroup.centralizer (K : Set G)) (x : H × K) :
    directMulEquiv H K hcomp hcomm x = (x.1 : G) * (x.2 : G) := rfl

@[expose] def sylowCenter (S : Sylow 2 G) : Subgroup G :=
  (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype

theorem sylowCenter_le_sylow (S : Sylow 2 G) : sylowCenter S ≤ (S : Subgroup G) :=
  Subgroup.map_subtype_le _

theorem sylowCenter_le_centralizer (S : Sylow 2 G) :
    sylowCenter S ≤ Subgroup.centralizer (S : Set G) := by
  rintro z ⟨a, ha, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha ⟨s, hs⟩)

@[expose] def sylowCentralizerCenter (S : Sylow 2 G) :
    Sylow 2 (Subgroup.centralizer (S : Set G)) := by
  let C := Subgroup.centralizer (S : Set G)
  let Z := (sylowCenter S).subgroupOf C
  have hZp : IsPGroup 2 Z :=
    (S.isPGroup'.to_le (sylowCenter_le_sylow S)).comap_subtype
  refine { Z with isPGroup' := hZp, is_maximal' := ?_ }
  intro Q hQ hZQ
  let P := Q.map C.subtype
  have hPp : IsPGroup 2 P := hQ.map C.subtype
  have hPN : P ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.map_subtype_le Q).trans (Subgroup.centralizer_le_normalizer _)
  have hjoin := S.isPGroup'.to_sup_of_normal_left' hPp hPN
  have hPS : P ≤ (S : Subgroup G) := by
    have hmax := S.is_maximal' hjoin le_sup_left
    exact le_sup_right.trans_eq hmax
  have hPZ : P ≤ sylowCenter S := by
    intro p hp
    have hpC : p ∈ C := Subgroup.map_subtype_le Q hp
    refine ⟨⟨p, hPS hp⟩, ?_, rfl⟩
    apply (Subgroup.mem_center_iff (G := (S : Subgroup G))).mpr
    intro s
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hpC s.val s.property
  apply le_antisymm _ hZQ
  intro q hq
  exact hPZ (Subgroup.mem_map_of_mem C.subtype hq)

theorem sylowCentralizerCenter_coe (S : Sylow 2 G) :
    (sylowCentralizerCenter S : Subgroup (Subgroup.centralizer (S : Set G))) =
      (sylowCenter S).subgroupOf (Subgroup.centralizer (S : Set G)) := rfl

theorem sylowCentralizerCenter_le_center (S : Sylow 2 G) :
    (sylowCentralizerCenter S : Subgroup (Subgroup.centralizer (S : Set G))) ≤
      Subgroup.center (Subgroup.centralizer (S : Set G)) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro c
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp c.property z.val
    (sylowCenter_le_sylow S hz)).symm

theorem sylowCentralizer_oddCore_complement [Finite G] (S : Sylow 2 G) :
    (CFSG.oddCore (Subgroup.centralizer (S : Set G))).IsComplement'
      ((sylowCenter S).subgroupOf (Subgroup.centralizer (S : Set G))) := by
  have hNC : Subgroup.normalizer
      (sylowCentralizerCenter S : Set (Subgroup.centralizer (S : Set G))) ≤
      Subgroup.centralizer
        (sylowCentralizerCenter S : Set (Subgroup.centralizer (S : Set G))) := by
    intro c _hc z hz
    exact (Subgroup.mem_center_iff.mp (sylowCentralizerCenter_le_center S hz) c).symm
  exact oddCore_isComplement_of_normalizer_le_centralizer (sylowCentralizerCenter S) hNC

end CFSG.Wreathed.BaseFourCentralizerStructure

namespace CFSG.Wreathed.BaseFourCentralizerStructure

open scoped Classical Pointwise

universe u

variable {G : Type u} [Group G]

@[expose] def ambientOddCore (H : Subgroup G) : Subgroup G :=
  (CFSG.oddCore H).map H.subtype

theorem ambientOddCore_le (H : Subgroup G) : ambientOddCore H ≤ H :=
  Subgroup.map_subtype_le _

theorem ambientOddCore_subgroupOf (H : Subgroup G) :
    (ambientOddCore H).subgroupOf H = CFSG.oddCore H :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem ambientOddCore_odd [Finite G] (H : Subgroup G) :
    Odd (Nat.card (ambientOddCore H)) := by
  rw [ambientOddCore, Subgroup.card_map_of_injective H.subtype_injective]
  exact weakClosure_oddCore_card H

@[expose] def ambientDirectMulEquiv (C H K : Subgroup G) (hHC : H ≤ C) (hKC : K ≤ C)
    (hcomp : (H.subgroupOf C).IsComplement' (K.subgroupOf C))
    (hcomm : H ≤ Subgroup.centralizer (K : Set G)) : H × K ≃* C :=
  ((Subgroup.subgroupOfEquivOfLe hHC).symm.prodCongr
    (Subgroup.subgroupOfEquivOfLe hKC).symm).trans
    (directMulEquiv (H.subgroupOf C) (K.subgroupOf C) hcomp (by
      intro h hh k hk
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hcomm hh) k.val hk))

@[simp] theorem ambientDirectMulEquiv_coe (C H K : Subgroup G)
    (hHC : H ≤ C) (hKC : K ≤ C)
    (hcomp : (H.subgroupOf C).IsComplement' (K.subgroupOf C))
    (hcomm : H ≤ Subgroup.centralizer (K : Set G)) (h : H) (k : K) :
    (ambientDirectMulEquiv C H K hHC hKC hcomp hcomm (h,k) : G) =
      (h : G) * (k : G) := rfl

theorem sylowCenter_eq_original (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : sylowCenter S = modelCenter S e := by
  have hcent : (Original.Z (2 ^ n)).map e.symm.toMonoidHom =
      Subgroup.center (S : Subgroup G) := by
    rw [← (wreath_center_involution_and_quaternion_coordinates n hn).center]
    exact Subgroup.map_center_eq e.symm
  unfold sylowCenter modelCenter wreathModelHom
  rw [← Subgroup.map_map, hcent]

@[expose] def originalSylowCentralizerDirectEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelCenter S e × ambientOddCore (Subgroup.centralizer (S : Set G)) ≃*
      Subgroup.centralizer (S : Set G) := by
  let C := Subgroup.centralizer (S : Set G)
  have hZC : modelCenter S e ≤ C := by
    rw [← sylowCenter_eq_original n hn S e]
    exact sylowCenter_le_centralizer S
  have hcomp : ((modelCenter S e).subgroupOf C).IsComplement'
      ((ambientOddCore C).subgroupOf C) := by
    rw [ambientOddCore_subgroupOf, ← sylowCenter_eq_original n hn S e]
    exact (sylowCentralizer_oddCore_complement S).symm
  have hcomm : modelCenter S e ≤ Subgroup.centralizer (ambientOddCore C : Set G) := by
    apply Subgroup.le_centralizer_iff.mp
    exact (ambientOddCore_le C).trans (by
      intro c hc z hz
      exact Subgroup.mem_centralizer_iff.mp hc z
        (by rw [← sylowCenter_eq_original n hn S e] at hz; exact sylowCenter_le_sylow S hz))
  exact ambientDirectMulEquiv C (modelCenter S e) (ambientOddCore C)
    hZC (ambientOddCore_le C) hcomp hcomm

@[simp] theorem originalSylowCentralizerDirectEquiv_coe [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (z : modelCenter S e) (a : ambientOddCore (Subgroup.centralizer (S : Set G))) :
    (originalSylowCentralizerDirectEquiv n hn S e (z,a) : G) = (z : G) * (a : G) := rfl

theorem originalSylowNormalizer_factorization [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : G) (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    ∃ s ∈ (S : Subgroup G), ∃ c ∈ Subgroup.centralizer (S : Set G), g = s * c := by
  let N := Subgroup.normalizer (S : Set G)
  let f := (S : Subgroup G).normalizerMonoidHom
  let Q : Sylow 2 N := S.subtype Subgroup.le_normalizer
  have hAut : IsPGroup 2 (MulAut (S : Subgroup G)) :=
    (wreath_center_involution_and_quaternion_coordinates n hn).automorphisms.of_equiv
      (MulAut.congr e.symm)
  obtain ⟨s, hs, heq⟩ := CFSG.GorensteinWalter.hom_to_pGroup_image_on_sylow
    hAut f Q ⟨g,hg⟩
  have hsS : s.val ∈ (S : Subgroup G) := by
    change s ∈ (S : Subgroup G).subgroupOf N at hs
    exact hs
  have hker : s⁻¹ * ⟨g,hg⟩ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  refine ⟨s.val, hsS, s.val⁻¹ * g, hker, ?_⟩
  group

theorem originalSylowNormalizer_complement [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    let N := Subgroup.normalizer (S : Set G)
    let E := ambientOddCore (Subgroup.centralizer (S : Set G))
    ((S : Subgroup G).subgroupOf N).IsComplement' (E.subgroupOf N) := by
  let N := Subgroup.normalizer (S : Set G)
  let C := Subgroup.centralizer (S : Set G)
  let E := ambientOddCore C
  have hEN : E ≤ N := (ambientOddCore_le C).trans (Subgroup.centralizer_le_normalizer _)
  have hodd : Odd (Nat.card (E.subgroupOf N)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv]
    exact ambientOddCore_odd C
  have hdis : Disjoint ((S : Subgroup G).subgroupOf N) (E.subgroupOf N) := by
    apply (Subgroup.disjoint_of_coprime_natCard ?_)
    obtain ⟨k,hk⟩ := (S.isPGroup'.comap_subtype (K := N)).exists_card_eq
    change (Nat.card ((S : Subgroup G).comap N.subtype)).Coprime
      (Nat.card (E.subgroupOf N))
    rw [hk]
    exact (Nat.coprime_two_left.mpr hodd).pow_left k
  change Function.Bijective (fun x : ((S : Subgroup G).subgroupOf N) × (E.subgroupOf N) =>
    (x.1 : N) * (x.2 : N))
  refine ⟨Subgroup.mul_injective_of_disjoint hdis, ?_⟩
  intro g
  obtain ⟨s,hs,c,hc,hg⟩ := originalSylowNormalizer_factorization n hn S e g.val g.property
  let f := originalSylowCentralizerDirectEquiv n hn S e
  let za := f.symm ⟨c,hc⟩
  have hza : (za.1 : G) * (za.2 : G) = c := by
    have h := congrArg Subtype.val (f.apply_symm_apply ⟨c,hc⟩)
    exact h
  have hzS : (za.1 : G) ∈ (S : Subgroup G) := by
    apply sylowCenter_le_sylow S
    rw [sylowCenter_eq_original n hn S e]
    exact za.1.property
  have hsN := Subgroup.le_normalizer hs
  have hzN := Subgroup.le_normalizer hzS
  refine ⟨(⟨⟨s*(za.1:G), N.mul_mem hsN hzN⟩, (S : Subgroup G).mul_mem hs hzS⟩,
    ⟨⟨za.2, hEN za.2.property⟩, za.2.property⟩), ?_⟩
  apply Subtype.ext
  change s * (za.1 : G) * (za.2 : G) = g.val
  rw [mul_assoc, hza, hg]

@[expose] def originalSylowNormalizerDirectEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ↥(S : Subgroup G) × ambientOddCore (Subgroup.centralizer (S : Set G)) ≃*
      Subgroup.normalizer (S : Set G) :=
  ambientDirectMulEquiv _ _ _ Subgroup.le_normalizer
    ((ambientOddCore_le _).trans (Subgroup.centralizer_le_normalizer _))
    (originalSylowNormalizer_complement n hn S e)
    (Subgroup.le_centralizer_iff.mp (ambientOddCore_le _))

@[simp] theorem originalSylowNormalizerDirectEquiv_coe [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (s : S) (a : ambientOddCore (Subgroup.centralizer (S : Set G))) :
    (originalSylowNormalizerDirectEquiv n hn S e (s,a) : G) = (s : G) * (a : G) := rfl

end CFSG.Wreathed.BaseFourCentralizerStructure

namespace CFSG.Wreathed.BaseFourCentralizerStructure

open scoped Classical Pointwise

universe u

variable {G : Type u} [Group G]

@[expose] def originalT (n : ℕ) : Subgroup (Wreath (2 ^ n)) :=
  Subgroup.closure {Original.s (2 ^ n) ^ ((2 ^ n) / 2),
    Original.t (2 ^ n) ^ ((2 ^ n) / 2)}

@[expose] def modelT (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : Subgroup G :=
  (originalT n).map (wreathModelHom S e)

theorem half_two_pow_eq (n : ℕ) (hn : 1 ≤ n) : 2 ^ n / 2 = 2 ^ (n-1) := by
  rw [← twice_half_two_pow n hn]
  omega

theorem originalT_eq_baseOmega (n : ℕ) (hn : 1 ≤ n) :
    originalT n = (baseOmega (2 ^ n)).map (baseSubgroup (2 ^ n)).subtype := by
  let B := baseSubgroup (2 ^ n)
  let s : B := ⟨Original.s (2 ^ n), by simp [B,Original.s]⟩
  let t : B := ⟨Original.t (2 ^ n), by simp [B,Original.t]⟩
  have hgen : Subgroup.closure {s,t} = (⊤ : Subgroup B) := by
    apply Subgroup.map_injective B.subtype_injective
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
    simpa [s,t,B,Original.s,Original.t] using (base_eq_generated (2 ^ n)).symm
  have himage := congrArg (Subgroup.map (baseHalfPower n)) hgen
  rw [MonoidHom.map_closure, Subgroup.map_top, baseHalfPower_range n hn] at himage
  have hambient := congrArg (Subgroup.map B.subtype) himage
  rw [MonoidHom.map_closure] at hambient
  symm
  rw [← hambient]
  simp [originalT, s,t,B,half_two_pow_eq n hn]

@[expose] def modelTEquiv (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    baseOmega (2 ^ n) ≃* modelT n S e :=
  ((baseOmega (2 ^ n)).equivMapOfInjective
    ((wreathModelHom S e).comp (baseSubgroup (2 ^ n)).subtype)
    ((wreathModelHom_injective S e).comp (baseSubgroup (2 ^ n)).subtype_injective)).trans
    (MulEquiv.subgroupCongr (by rw [← Subgroup.map_map, ← originalT_eq_baseOmega n hn]; rfl))

@[simp] theorem modelTEquiv_coe (n : ℕ) (hn : 1 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (t : baseOmega (2 ^ n)) :
    (modelTEquiv n hn S e t : G) = wreathModelHom S e t.val.val := rfl

theorem modelT_le_base (n : ℕ) (hn : 1 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : modelT n S e ≤ modelBase S e := by
  unfold modelT modelBase
  rw [originalT_eq_baseOmega n hn]
  exact Subgroup.map_mono (Subgroup.map_subtype_le _)

theorem modelT_isKleinFour (n : ℕ) (hn : 1 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : IsKleinFour (modelT n S e) := by
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_congr (modelTEquiv n hn S e).toEquiv, baseOmega_card n hn]
  · rw [Monoid.exponent_eq_of_mulEquiv (modelTEquiv n hn S e).symm]
    exact (baseOmega_isKleinFour n hn).exponent_two

theorem modelBase_normalizer_le_modelT_normalizer (n : ℕ) (hn : 1 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelBase S e : Set G) ≤
      Subgroup.normalizer (modelT n S e : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  unfold modelT
  rw [originalT_eq_baseOmega n hn, Subgroup.map_map, Subgroup.map_map]
  let a := modelBaseAction S e ⟨g,hg⟩
  have hcomp : (MulAut.conj g).toMonoidHom.comp
      ((wreathModelHom S e).comp (baseSubgroup (2 ^ n)).subtype) =
      ((wreathModelHom S e).comp (baseSubgroup (2 ^ n)).subtype).comp a.toMonoidHom := by
    ext b
    exact (modelBaseAction_coe S e ⟨g,hg⟩ b).symm
  rw [Subgroup.map_map, MonoidHom.comp_assoc]
  change (baseOmega (2 ^ n)).map ((MulAut.conj g).toMonoidHom.comp
    ((wreathModelHom S e).comp (baseSubgroup (2 ^ n)).subtype)) =
    (baseOmega (2 ^ n)).map ((wreathModelHom S e).comp (baseSubgroup (2 ^ n)).subtype)
  rw [hcomp, ← Subgroup.map_map,
    Subgroup.characteristic_iff_map_eq.mp (baseOmega_characteristic _) a]

theorem modelBaseAction_eq_one_of_centralizes_modelT [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelBase S e : Set G))
    (hg : g.val ∈ Subgroup.centralizer (modelT n S e : Set G)) :
    modelBaseAction S e g = 1 := by
  let a := modelBaseAction S e g
  have hfix : baseOmegaAutAction (2 ^ n) a = 1 := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    apply Subtype.ext
    apply wreathModelHom_injective S e
    change wreathModelHom S e (a b.val).val = wreathModelHom S e b.val.val
    rw [modelBaseAction_coe]
    have hc := Subgroup.mem_centralizer_iff.mp hg
      (modelTEquiv n hn S e b : G) (modelTEquiv n hn S e b).property
    rw [modelTEquiv_coe] at hc
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have hred : CFSG.LargeEvenClassification.Helpers.frattiniAutAction
      (baseSubgroup (2 ^ n)) a = 1 := by
    rw [baseOmegaAutAction_eq_congr_frattini n hn] at hfix
    exact (MulAut.congr (baseFrattiniOmegaEquiv n hn)).injective
      (hfix.trans (map_one _).symm)
  have hinj := modelBaseAction_range_reduction_injective n hn S e
  have hpoint : (⟨a,⟨g,rfl⟩⟩ : (modelBaseAction S e).range) = 1 :=
    hinj (by simpa only [MonoidHom.domRestrict_apply, Subgroup.coe_one, map_one] using hred)
  exact congrArg Subtype.val hpoint

theorem modelBaseNormalizer_inter_modelTCentralizer [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelBase S e : Set G) ⊓
      Subgroup.centralizer (modelT n S e : Set G) =
      Subgroup.centralizer (modelBase S e : Set G) := by
  apply le_antisymm
  · intro g hg
    have h := modelBaseAction_eq_one_of_centralizes_modelT n hn S e ⟨g,hg.1⟩ hg.2
    have hk : (⟨g,hg.1⟩ : Subgroup.normalizer (modelBase S e : Set G)) ∈
        (modelBaseAction S e).ker := h
    rw [modelBaseAction_ker] at hk
    exact hk
  · exact le_inf (Subgroup.centralizer_le_normalizer _)
      (Subgroup.centralizer_le (modelT_le_base n hn S e))

theorem modelBase_le_modelTCentralizer (n : ℕ) (hn : 1 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelBase S e ≤ Subgroup.centralizer (modelT n S e : Set G) := by
  intro b hb t ht
  let : IsMulCommutative (modelBase S e) :=
    by
      apply IsMulCommutative.of_comm
      intro x y
      apply (modelBaseEquiv S e).symm.injective
      rw [map_mul,map_mul]
      exact (base_is_abelian _).is_comm.comm _ _
  exact congrArg Subtype.val
    ((IsMulCommutative.is_comm.comm (⟨t,modelT_le_base n hn S e ht⟩ : modelBase S e)
      (⟨b,hb⟩ : modelBase S e)))

theorem no_kleinFour_le_center_of_center_cyclic
    {A : Type u} [Group A] [IsCyclic (Subgroup.center A)]
    (V : Subgroup A) (hV : IsKleinFour V) : ¬ (V ≤ Subgroup.center A) := by
  intro hVC
  let := hV
  let : IsCyclic V := Subgroup.isCyclic_of_le hVC
  exact IsKleinFour.not_isCyclic (G := V) inferInstance

theorem eq_or_top_of_contains_index_two {A : Type u} [Group A]
    (U W : Subgroup A) (hU : U.index = 2) (hUW : U ≤ W) : W = U ∨ W = ⊤ := by
  have hdiv : W.index ∣ 2 := hU ▸ Subgroup.index_dvd_of_le hUW
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
  · exact Or.inr (Subgroup.index_eq_one.mp hone)
  · apply Or.inl
    apply le_antisymm _ hUW
    apply Subgroup.relIndex_eq_one.mp
    have htower := Subgroup.relIndex_mul_index hUW
    rw [hU,htwo] at htower
    omega

@[expose] def modelBaseFourCentralizerSylow [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Sylow 2 (Subgroup.centralizer (modelT n S e : Set G)) := by
  let C := Subgroup.centralizer (modelT n S e : Set G)
  let U := modelBase S e
  have hn1 : 1 ≤ n := by omega
  have hUC : U ≤ C := modelBase_le_modelTCentralizer n hn1 S e
  have hUS : U ≤ (S : Subgroup G) := modelBase_le_sylow S e
  have hUp : IsPGroup 2 (U.subgroupOf C) := (S.isPGroup'.to_le hUS).comap_subtype
  refine { U.subgroupOf C with isPGroup' := hUp, is_maximal' := ?_ }
  intro Q hQ hUQ
  let P := Q.map C.subtype
  have hPp : IsPGroup 2 P := hQ.map C.subtype
  have hUP : U ≤ P := by
    have h := Subgroup.map_mono (f := C.subtype) hUQ
    rwa [Subgroup.map_subgroupOf_eq_of_le hUC] at h
  obtain ⟨R,hPR⟩ := hPp.exists_le_sylow
  let eR := (Sylow.equiv S R).symm.trans e
  let Ui := U.subgroupOf (R : Subgroup G)
  let Pi := P.subgroupOf (R : Subgroup G)
  have hUR : U ≤ (R : Subgroup G) := hUP.trans hPR
  have hUi : Ui.index = 2 := by
    have hcardU : Nat.card Ui = (2 ^ n) ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUR).toEquiv,
        ← Nat.card_congr (modelBaseEquiv S e).toEquiv, card_base]
    have hcardR : Nat.card (R : Subgroup G) = 2 * (2 ^ n) ^ 2 :=
      (Nat.card_congr eR.toEquiv).trans
        (wreath_center_involution_and_quaternion_coordinates n hn).card
    have h := Ui.card_mul_index
    rw [hcardU,hcardR] at h
    have hpos : 0 < (2 ^ n) ^ 2 := pow_pos (pow_pos (by decide) _) _
    nlinarith
  have hUiPi : Ui ≤ Pi := by intro a ha; exact hUP ha
  have hPU : P ≤ U := by
    rcases eq_or_top_of_contains_index_two Ui Pi hUi hUiPi with heq | htop
    · intro p hp
      exact (show (⟨p,hPR hp⟩ : R) ∈ Ui from heq ▸ hp)
    · have hRP : (R : Subgroup G) ≤ P := by
        intro r hr
        have hmem : (⟨r,hr⟩ : R) ∈ Pi := by rw [htop]; trivial
        exact hmem
      have hTR : modelT n S e ≤ (R : Subgroup G) :=
        (modelT_le_base n hn1 S e).trans hUR
      let Ti := (modelT n S e).subgroupOf (R : Subgroup G)
      have hTi : IsKleinFour Ti := by
        have he := Subgroup.subgroupOfEquivOfLe hTR
        refine ⟨?_, ?_⟩
        · rw [Nat.card_congr he.toEquiv]
          exact (modelT_isKleinFour n hn1 S e).card_four
        · rw [Monoid.exponent_eq_of_mulEquiv he]
          exact (modelT_isKleinFour n hn1 S e).exponent_two
      have hcycW : IsCyclic (Subgroup.center (Wreath (2 ^ n))) := by
        rw [(wreath_center_involution_and_quaternion_coordinates n hn).center]
        unfold Original.Z
        infer_instance
      let := hcycW
      let : IsCyclic (Subgroup.center (R : Subgroup G)) :=
        isCyclic_of_injective (Subgroup.centerCongr eR).toMonoidHom
          (Subgroup.centerCongr eR).injective
      have hTiC : Ti ≤ Subgroup.center (R : Subgroup G) := by
        intro t ht
        rw [Subgroup.mem_center_iff]
        intro r
        apply Subtype.ext
        have hrC : r.val ∈ C := Subgroup.map_subtype_le Q (hRP r.property)
        exact (Subgroup.mem_centralizer_iff.mp hrC t.val ht).symm
      exact (no_kleinFour_le_center_of_center_cyclic Ti hTi hTiC).elim
  apply le_antisymm _ hUQ
  intro q hq
  exact hPU (Subgroup.mem_map_of_mem C.subtype hq)

theorem modelBaseFourCentralizerSylow_coe [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelBaseFourCentralizerSylow n hn S e :
      Subgroup (Subgroup.centralizer (modelT n S e : Set G))) =
      (modelBase S e).subgroupOf (Subgroup.centralizer (modelT n S e : Set G)) := rfl

theorem modelBaseFourCentralizer_internal_normalizer [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    let C := Subgroup.centralizer (modelT n S e : Set G)
    let U := (modelBase S e).subgroupOf C
    Subgroup.normalizer (U : Set C) =
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf C := by
  let C := Subgroup.centralizer (modelT n S e : Set G)
  let U := (modelBase S e).subgroupOf C
  have hUC : modelBase S e ≤ C := modelBase_le_modelTCentralizer n (by omega) S e
  apply le_antisymm
  · intro c hc
    have hambient : c.val ∈ Subgroup.normalizer (modelBase S e : Set G) := by
      have h := Subgroup.le_normalizer_map (H := U) C.subtype
      rw [Subgroup.map_subgroupOf_eq_of_le hUC] at h
      exact h (Subgroup.mem_map_of_mem C.subtype hc)
    have h := modelBaseNormalizer_inter_modelTCentralizer n (by omega) S e
    exact (h ▸ (show c.val ∈ Subgroup.normalizer (modelBase S e : Set G) ⊓ C
      from ⟨hambient,c.property⟩))
  · intro c hc
    apply Subgroup.centralizer_le_normalizer (U : Set C)
    intro u hu
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc u.val hu

theorem modelBaseFourCentralizer_internal_centralizer
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    let C := Subgroup.centralizer (modelT n S e : Set G)
    let U := (modelBase S e).subgroupOf C
    Subgroup.centralizer (U : Set C) =
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf C := by
  let C := Subgroup.centralizer (modelT n S e : Set G)
  have hUC : modelBase S e ≤ C := modelBase_le_modelTCentralizer n hn S e
  ext c
  constructor
  · intro hc u hu
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc (⟨u,hUC hu⟩ : C) hu)
  · intro hc u hu
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc u.val hu

theorem modelBaseFourCentralizer_oddCore_complement [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    let C := Subgroup.centralizer (modelT n S e : Set G)
    (CFSG.oddCore C).IsComplement' ((modelBase S e).subgroupOf C) := by
  apply oddCore_isComplement_of_normalizer_le_centralizer (modelBaseFourCentralizerSylow n hn S e)
  change Subgroup.normalizer
    ((modelBase S e).subgroupOf (Subgroup.centralizer (modelT n S e : Set G)) :
      Set (Subgroup.centralizer (modelT n S e : Set G))) ≤
    Subgroup.centralizer
    ((modelBase S e).subgroupOf (Subgroup.centralizer (modelT n S e : Set G)) :
      Set (Subgroup.centralizer (modelT n S e : Set G)))
  rw [modelBaseFourCentralizer_internal_normalizer n hn S e,
    modelBaseFourCentralizer_internal_centralizer n (by omega) S e]

end CFSG.Wreathed.BaseFourCentralizerStructure

namespace CFSG.Wreathed.BaseFourCentralizerStructure
open scoped Classical Pointwise
universe u
variable {G : Type u} [Group G]

theorem normalizer_le_ambientOddCore_normalizer [Finite G] (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (ambientOddCore H : Set G) := by
  intro g hg
  let a := H.normalizerMonoidHom ⟨g, hg⟩
  let := oddCore_characteristic (G := H)
  have ha : (CFSG.oddCore H).map a.toMonoidHom = CFSG.oddCore H :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance a
  have hcomp : (↑(MulAut.conj g) : G →* G).comp H.subtype =
      H.subtype.comp a.toMonoidHom := by
    ext h
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨g, hg⟩ h).symm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  unfold ambientOddCore
  rw [Subgroup.map_map, hcomp,← Subgroup.map_map, ha]

theorem normalizer_le_centralizer_normalizer (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (H : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  have hle (a : MulAut G) (ha : H.map a.toMonoidHom = H) :
      (Subgroup.centralizer (H : Set G)).map a.toMonoidHom ≤
        Subgroup.centralizer (H : Set G) := by
    have h := Subgroup.map_centralizer_le_centralizer_image (H : Set G) a.toMonoidHom
    change _ ≤ Subgroup.centralizer ((H.map a.toMonoidHom) : Set G) at h
    rwa [ha] at h
  apply le_antisymm
  · exact hle (MulAut.conj g) hg
  · have hginv : H.map (MulAut.conj g).symm.toMonoidHom = H := by
      have h := congrArg (Subgroup.map (MulAut.conj g).symm.toMonoidHom) hg
      rw [Subgroup.map_map] at h
      have hid : (MulAut.conj g).symm.toMonoidHom.comp (↑(MulAut.conj g) : G →* G) =
          MonoidHom.id G := by ext x; exact (MulAut.conj g).symm_apply_apply x
      rw [hid, Subgroup.map_id] at h
      exact h.symm
    have h := Subgroup.map_mono (f := (↑(MulAut.conj g) : G →* G))
      (hle (MulAut.conj g).symm hginv)
    rw [Subgroup.map_map] at h
    have hid : (↑(MulAut.conj g) : G →* G).comp (MulAut.conj g).symm.toMonoidHom =
        MonoidHom.id G := by ext x; exact (MulAut.conj g).apply_symm_apply x
    rwa [hid, Subgroup.map_id] at h

theorem modelTNormalizer_normalizes_oddCore [Finite G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelT n S e : Set G) ≤
      Subgroup.normalizer
        (ambientOddCore (Subgroup.centralizer (modelT n S e : Set G)) : Set G) :=
  (normalizer_le_centralizer_normalizer _).trans (normalizer_le_ambientOddCore_normalizer _)

theorem modelBaseFourCentralizer_ambient_complement [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    let C := Subgroup.centralizer (modelT n S e : Set G)
    ((ambientOddCore C).subgroupOf C).IsComplement' ((modelBase S e).subgroupOf C) := by
  dsimp only
  rw [ambientOddCore_subgroupOf]
  exact modelBaseFourCentralizer_oddCore_complement n hn S e

theorem modelBaseFourCentralizer_split_and_unique [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    let C := Subgroup.centralizer (modelT n S e : Set G)
    let C0 := ambientOddCore C
    C = C0 ⊔ modelBase S e ∧ C0 ⊓ modelBase S e = ⊥ ∧ Odd (Nat.card C0) ∧
      (C0.subgroupOf C).Normal ∧
      (∀ c : C, ∃ a : C0, ∃ b : modelBase S e, c.val = (a : G) * (b : G)) ∧
      (∀ J : Subgroup C, ∀ hJ : J.Normal, Odd (Nat.card J) →
        (letI := hJ; IsPGroup 2 (C ⧸ J)) → J = CFSG.oddCore C) := by
  let C := Subgroup.centralizer (modelT n S e : Set G)
  let C0 := ambientOddCore C
  have hUC : modelBase S e ≤ C := modelBase_le_modelTCentralizer n (by omega) S e
  have hcomp := modelBaseFourCentralizer_ambient_complement n hn S e
  have hsup := congrArg (Subgroup.map C.subtype) hcomp.sup_eq_top
  rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le (ambientOddCore_le C),
    Subgroup.map_subgroupOf_eq_of_le hUC,Subgroup.map_top,Subgroup.range_subtype] at hsup
  have hinf := congrArg (Subgroup.map C.subtype) hcomp.disjoint.eq_bot
  rw [Subgroup.map_inf (f := C.subtype) _ _ C.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le (ambientOddCore_le C),
    Subgroup.map_subgroupOf_eq_of_le hUC,Subgroup.map_bot] at hinf
  have hnormal : (C0.subgroupOf C).Normal := by
    rw [ambientOddCore_subgroupOf]
    infer_instance
  refine ⟨hsup.symm, hinf, ambientOddCore_odd C, hnormal,?_,?_⟩
  · intro c
    obtain ⟨p,hp⟩ := hcomp.surjective c
    exact ⟨(Subgroup.subgroupOfEquivOfLe (ambientOddCore_le C)) p.1,
      (Subgroup.subgroupOfEquivOfLe hUC) p.2,congrArg Subtype.val hp.symm⟩
  · intro J hJ hodd hquot
    let := hJ
    exact normal_odd_two_quotient_eq_oddCore J hodd hquot

@[expose] def originalBaseOddCoreQuotientEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelBase S e ≃*
      (Subgroup.centralizer (modelT n S e : Set G) ⧸
        CFSG.oddCore (Subgroup.centralizer (modelT n S e : Set G))) :=
  (Subgroup.subgroupOfEquivOfLe (modelBase_le_modelTCentralizer n (by omega) S e)).symm.trans
    (modelBaseFourCentralizer_oddCore_complement n hn S e).symm.QuotientMulEquiv.symm

@[simp] theorem originalBaseOddCoreQuotientEquiv_apply [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (b : modelBase S e) :
    originalBaseOddCoreQuotientEquiv n hn S e b =
      (QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer (modelT n S e : Set G))))
        ⟨b.val, modelBase_le_modelTCentralizer n (by omega) S e b.property⟩ := rfl

@[expose] def originalBaseOddCoreAction [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelBase S e →* MulAut
      (ambientOddCore (Subgroup.centralizer (modelT n S e : Set G))) :=
  (ambientOddCore (Subgroup.centralizer (modelT n S e : Set G))).normalizerMonoidHom.comp
    (Subgroup.inclusion (by
      have hUC := modelBase_le_modelTCentralizer n (by omega) S e
      exact hUC.trans ((Subgroup.le_normalizer).trans
        (normalizer_le_ambientOddCore_normalizer _))))

@[simp] theorem originalBaseOddCoreAction_coe [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (b : modelBase S e) (a : ambientOddCore (Subgroup.centralizer (modelT n S e : Set G))) :
    (originalBaseOddCoreAction n hn S e b a : G) = (b : G) * (a : G) * (b : G)⁻¹ := rfl

@[expose] def originalBaseFourCentralizerSemidirectEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (ambientOddCore (Subgroup.centralizer (modelT n S e : Set G))) ⋊[
      originalBaseOddCoreAction n hn S e] modelBase S e ≃*
      Subgroup.centralizer (modelT n S e : Set G) := by
  let C := Subgroup.centralizer (modelT n S e : Set G)
  let C0 := ambientOddCore C
  let fA : C0 →* C := Subgroup.inclusion (ambientOddCore_le C)
  let fB : modelBase S e →* C :=
    Subgroup.inclusion (modelBase_le_modelTCentralizer n (by omega) S e)
  let f := SemidirectProduct.lift (φ := originalBaseOddCoreAction n hn S e) fA fB (by
    intro b
    apply DFunLike.ext
    intro a
    apply Subtype.ext
    rfl)
  have hcomp := modelBaseFourCentralizer_ambient_complement n hn S e
  let aE := Subgroup.subgroupOfEquivOfLe (ambientOddCore_le C)
  let bE := Subgroup.subgroupOfEquivOfLe
    (modelBase_le_modelTCentralizer n (by omega) S e)
  let eProd := aE.symm.toEquiv.prodCongr bE.symm.toEquiv
  have hbij : Function.Bijective f := by
    have hmult : (f : _ → C) =
        (fun p : (C0.subgroupOf C) × ((modelBase S e).subgroupOf C) =>
          (p.1 : C) * (p.2 : C)) ∘ eProd ∘ SemidirectProduct.equivProd := rfl
    rw [hmult]
    exact hcomp.comp (eProd.bijective.comp SemidirectProduct.equivProd.bijective)
  exact MulEquiv.ofBijective f hbij

@[simp] theorem originalBaseFourCentralizerSemidirectEquiv_coe [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p : (ambientOddCore (Subgroup.centralizer (modelT n S e : Set G))) ⋊[
      originalBaseOddCoreAction n hn S e] modelBase S e) :
    (originalBaseFourCentralizerSemidirectEquiv n hn S e p : G) =
      (p.left : G) * (p.right : G) := rfl

end CFSG.Wreathed.BaseFourCentralizerStructure

namespace CFSG.Wreathed.BaseFourCentralizerStructure
open scoped Classical Pointwise
universe u
variable {G : Type u} [Group G]

theorem normal_subgroup_sylow_factorization [Finite G]
    (N C U : Subgroup G) (hCN : C ≤ N) (hUC : U ≤ C)
    (hCnormal : (C.subgroupOf N).Normal) (T : Sylow 2 C)
    (hT : (T : Subgroup C) = U.subgroupOf C) :
    N = (Subgroup.normalizer (U : Set G) ⊓ N) ⊔ C := by
  let D := C.subgroupOf N
  let := hCnormal
  let eC : C ≃* D := (Subgroup.subgroupOfEquivOfLe hCN).symm
  let Q := T.mapSurjective (f := eC.toMonoidHom) eC.surjective
  have hQ : (Q : Subgroup D).map D.subtype = U.subgroupOf N := by
    ext n
    constructor
    · rintro ⟨d,hd,rfl⟩
      change d ∈ (T : Subgroup C).map eC.toMonoidHom at hd
      obtain ⟨c,hc,heq⟩ := hd
      rw [hT] at hc
      have hv := congrArg (fun x : D => x.val.val) heq
      change c.val = d.val.val at hv
      change d.val.val ∈ U
      rw [← hv]
      exact hc
    · intro hn
      refine ⟨⟨n,hUC hn⟩,?_,rfl⟩
      change (⟨n,hUC hn⟩ : D) ∈ (T : Subgroup C).map eC.toMonoidHom
      refine ⟨⟨n.val,hUC hn⟩,?_,?_⟩
      · rw [hT]; exact hn
      · rfl
  have hfrat := Q.normalizer_sup_eq_top
  rw [hQ] at hfrat
  have hNU : Subgroup.normalizer (U.subgroupOf N : Set N) =
      (Subgroup.normalizer (U : Set G)).subgroupOf N :=
    (Subgroup.subgroupOf_normalizer_eq (hUC.trans hCN)).symm
  rw [hNU] at hfrat
  have hambient := congrArg (Subgroup.map N.subtype) hfrat
  rw [Subgroup.map_sup,Subgroup.subgroupOf_map_subtype,
    Subgroup.map_subgroupOf_eq_of_le hCN,Subgroup.map_top,Subgroup.range_subtype] at hambient
  exact hambient.symm

end CFSG.Wreathed.BaseFourCentralizerStructure

namespace CFSG.Wreathed.BaseFourCentralizerStructure
open scoped Classical Pointwise
universe u
variable {G : Type u} [Group G]

theorem modelTNormalizer_factorization [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelT n S e : Set G) =
      Subgroup.normalizer (modelBase S e : Set G) ⊔
        Subgroup.centralizer (modelT n S e : Set G) := by
  let N := Subgroup.normalizer (modelT n S e : Set G)
  let C := Subgroup.centralizer (modelT n S e : Set G)
  have hNU : Subgroup.normalizer (modelBase S e : Set G) ≤ N :=
    modelBase_normalizer_le_modelT_normalizer n (by omega) S e
  have h := normal_subgroup_sylow_factorization N C (modelBase S e)
    (Subgroup.centralizer_le_normalizer _) (modelBase_le_modelTCentralizer n (by omega) S e)
    inferInstance (modelBaseFourCentralizerSylow n hn S e) rfl
  rw [inf_eq_left.mpr hNU] at h
  exact h

theorem modelTNormalizer_set_product [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (Subgroup.normalizer (modelT n S e : Set G) : Set G) =
      (Subgroup.centralizer (modelT n S e : Set G) : Set G) *
        (Subgroup.normalizer (modelBase S e : Set G) : Set G) := by
  have hNC := (modelBase_normalizer_le_modelT_normalizer n (by omega) S e).trans
    (normalizer_le_centralizer_normalizer (modelT n S e))
  rw [modelTNormalizer_factorization n hn S e,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hNC,
    Subgroup.set_mul_normalizer_comm _ _ hNC]

@[expose] def originalBaseToFourNormalizerQuotient
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelBase S e : Set G) →*
      (Subgroup.normalizer (modelT n S e : Set G) ⧸
        (Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
          (Subgroup.normalizer (modelT n S e : Set G))) :=
  (QuotientGroup.mk' _).comp
    (Subgroup.inclusion (modelBase_normalizer_le_modelT_normalizer n hn S e))

theorem originalBaseToFourNormalizerQuotient_ker [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (originalBaseToFourNormalizerQuotient n hn S e).ker =
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) := by
  ext g
  rw [MonoidHom.mem_ker]
  change ((Subgroup.inclusion (modelBase_normalizer_le_modelT_normalizer n hn S e) g :
    Subgroup.normalizer (modelT n S e : Set G)) :
      Subgroup.normalizer (modelT n S e : Set G) ⧸
        (Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
          (Subgroup.normalizer (modelT n S e : Set G))) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  have h := modelBaseNormalizer_inter_modelTCentralizer n hn S e
  change g.val ∈ Subgroup.centralizer (modelT n S e : Set G) ↔
    g.val ∈ Subgroup.centralizer (modelBase S e : Set G)
  constructor
  · intro hg
    exact h ▸ (show g.val ∈ Subgroup.normalizer (modelBase S e : Set G) ⊓
      Subgroup.centralizer (modelT n S e : Set G) from ⟨g.property,hg⟩)
  · intro hg
    exact Subgroup.centralizer_le (modelT_le_base n hn S e) hg

theorem originalBaseToFourNormalizerQuotient_surjective [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Surjective (originalBaseToFourNormalizerQuotient n (by omega) S e) := by
  let N := Subgroup.normalizer (modelT n S e : Set G)
  let C := Subgroup.centralizer (modelT n S e : Set G)
  let B := Subgroup.normalizer (modelBase S e : Set G)
  have hBN : B ≤ N := modelBase_normalizer_le_modelT_normalizer n (by omega) S e
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf N) q
  have hg : g.val ∈ B ⊔ C := by
    rw [← modelTNormalizer_factorization n hn S e]
    exact g.property
  have hBC : B ≤ Subgroup.normalizer (C : Set G) := hBN.trans
    (normalizer_le_centralizer_normalizer _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right B C hBC] at hg
  obtain ⟨b,hb,c,hc,hbc⟩ := hg
  refine ⟨⟨b,hb⟩,?_⟩
  let bn : N := ⟨b,hBN hb⟩
  let cn : N := ⟨c,hCN hc⟩
  have heq : bn * cn = g := Subtype.ext hbc
  have hcz : (QuotientGroup.mk' (C.subgroupOf N)) cn = 1 :=
    (QuotientGroup.eq_one_iff cn).mpr hc
  change (QuotientGroup.mk' (C.subgroupOf N)) bn = _
  rw [← heq,map_mul,hcz,mul_one]

@[expose] def originalBaseToFourNormalizerQuotientEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃*
      Subgroup.normalizer (modelT n S e : Set G) ⧸
        (Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
          (Subgroup.normalizer (modelT n S e : Set G)) :=
  QuotientGroup.liftEquiv _ (originalBaseToFourNormalizerQuotient_surjective n hn S e)
    (originalBaseToFourNormalizerQuotient_ker n (by omega) S e).symm

@[simp] theorem originalBaseToFourNormalizerQuotientEquiv_mk [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelBase S e : Set G)) :
    originalBaseToFourNormalizerQuotientEquiv n hn S e
      ((QuotientGroup.mk' _) g) =
        (QuotientGroup.mk' _)
          (Subgroup.inclusion (modelBase_normalizer_le_modelT_normalizer n (by omega) S e) g) :=
  QuotientGroup.liftEquiv_mk _ _ _ g

@[expose] def originalFourToBaseNormalizerQuotientEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelT n S e : Set G) ⧸
      (Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelT n S e : Set G)) ≃*
      Subgroup.normalizer (modelBase S e : Set G) ⧸
        (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
          (Subgroup.normalizer (modelBase S e : Set G)) :=
  (originalBaseToFourNormalizerQuotientEquiv n hn S e).symm

@[simp] theorem originalFourToBaseNormalizerQuotientEquiv_mk_inclusion [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelBase S e : Set G)) :
    originalFourToBaseNormalizerQuotientEquiv n hn S e
      ((QuotientGroup.mk' _)
        (Subgroup.inclusion (modelBase_normalizer_le_modelT_normalizer n (by omega) S e) g)) =
      (QuotientGroup.mk' _) g := by
  rw [← originalBaseToFourNormalizerQuotientEquiv_mk n hn S e]
  exact (originalBaseToFourNormalizerQuotientEquiv n hn S e).symm_apply_apply _

theorem modelTNormalizerQuotient_alternatives [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (Subgroup.normalizer (modelT n S e : Set G) ⧸
      (Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelT n S e : Set G))) = 2 ∨
      Nonempty (Subgroup.normalizer (modelT n S e : Set G) ⧸
        (Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
          (Subgroup.normalizer (modelT n S e : Set G)) ≃* Equiv.Perm (Fin 3)) := by
  let f := originalFourToBaseNormalizerQuotientEquiv n hn S e
  rcases modelBaseNormalizerQuotient_alternatives n (by omega) S e with htwo | hsix
  · exact Or.inl ((Nat.card_congr f.toEquiv).trans htwo)
  · obtain ⟨e3⟩ := hsix
    exact Or.inr ⟨f.trans e3⟩

end CFSG.Wreathed.BaseFourCentralizerStructure

namespace CFSG.Wreathed.BaseFourCentralizerStructure
open scoped Classical Pointwise
universe u
variable {G : Type u} [Group G]

@[expose] def originalFourNormalizerAction
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelT n S e : Set G) →* MulAut (modelT n S e) :=
  (modelT n S e).normalizerMonoidHom

@[simp] theorem originalFourNormalizerAction_coe
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelT n S e : Set G)) (t : modelT n S e) :
    (originalFourNormalizerAction n S e g t : G) = g.val * t.val * g.val⁻¹ := rfl

theorem originalFourNormalizerAction_ker
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (originalFourNormalizerAction n S e).ker =
      (Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelT n S e : Set G)) :=
  Subgroup.normalizerMonoidHom_ker _

@[expose] def originalFourNormalizerQuotientAction
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (Subgroup.normalizer (modelT n S e : Set G) ⧸
      (Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelT n S e : Set G))) →* MulAut (modelT n S e) :=
  QuotientGroup.lift _ (originalFourNormalizerAction n S e)
    (by rw [originalFourNormalizerAction_ker])

@[simp] theorem originalFourNormalizerQuotientAction_mk
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelT n S e : Set G)) :
    originalFourNormalizerQuotientAction n S e ((QuotientGroup.mk' _) g) =
      originalFourNormalizerAction n S e g := rfl

theorem originalFourNormalizerQuotientAction_injective
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Injective (originalFourNormalizerQuotientAction n S e) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  unfold originalFourNormalizerQuotientAction
  rw [QuotientGroup.ker_lift, originalFourNormalizerAction_ker,
    QuotientGroup.map_mk'_self]

@[expose] def originalBaseOnFourAction
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelBase S e : Set G) →* MulAut (modelT n S e) :=
  (originalFourNormalizerAction n S e).comp
    (Subgroup.inclusion (modelBase_normalizer_le_modelT_normalizer n hn S e))

theorem originalBaseOnFourAction_eq_congr
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    originalBaseOnFourAction n hn S e =
      (MulAut.congr (modelTEquiv n hn S e)).toMonoidHom.comp
        ((baseOmegaAutAction (2 ^ n)).comp (modelBaseAction S e)) := by
  apply DFunLike.ext
  intro g
  apply MulEquiv.ext
  intro t
  obtain ⟨b,rfl⟩ := (modelTEquiv n hn S e).surjective t
  apply Subtype.ext
  have hright :
      (((MulAut.congr (modelTEquiv n hn S e)).toMonoidHom.comp
        ((baseOmegaAutAction (2 ^ n)).comp (modelBaseAction S e))) g)
        (modelTEquiv n hn S e b) =
      modelTEquiv n hn S e ((baseOmegaAutAction (2 ^ n)) (modelBaseAction S e g) b) := by
    change modelTEquiv n hn S e
      ((baseOmegaAutAction (2 ^ n)) (modelBaseAction S e g)
        ((modelTEquiv n hn S e).symm (modelTEquiv n hn S e b))) = _
    rw [MulEquiv.symm_apply_apply]
  rw [hright]
  change (originalFourNormalizerAction n S e
      (Subgroup.inclusion (modelBase_normalizer_le_modelT_normalizer n hn S e) g)
      (modelTEquiv n hn S e b) : G) = _
  rw [originalFourNormalizerAction_coe]
  change g.val * (modelTEquiv n hn S e b : G) * g.val⁻¹ =
    (modelTEquiv n hn S e ((baseOmegaAutAction (2 ^ n)) (modelBaseAction S e g) b) : G)
  rw [modelTEquiv_coe,modelTEquiv_coe]
  exact (modelBaseAction_coe S e g b.val).symm

theorem originalBaseImageOnFour_injective [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Injective
      (((MulAut.congr (modelTEquiv n hn S e)).toMonoidHom.comp
        (baseOmegaAutAction (2 ^ n))).domRestrict (modelBaseAction S e).range) := by
  intro a b hab
  have homega := (MulAut.congr (modelTEquiv n hn S e)).injective hab
  rw [baseOmegaAutAction_eq_congr_frattini n hn] at homega
  have hred := (MulAut.congr (baseFrattiniOmegaEquiv n hn)).injective homega
  exact modelBaseAction_range_reduction_injective n hn S e hred

theorem originalBaseOnFourAction_order [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelBase S e : Set G)) :
    orderOf (originalBaseOnFourAction n hn S e g) = orderOf (modelBaseAction S e g) := by
  let a : (modelBaseAction S e).range := ⟨modelBaseAction S e g,⟨g,rfl⟩⟩
  have h := orderOf_injective _ (originalBaseImageOnFour_injective n hn S e) a
  rw [originalBaseOnFourAction_eq_congr]
  exact h.trans (Subgroup.orderOf_coe a).symm

theorem originalBaseNormalizer_order_three_cycles [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (eta : Subgroup.normalizer (modelBase S e : Set G))
    (horder : orderOf (modelBaseAction S e eta) = 3)
    (t : modelT n S e) (ht : t ≠ 1) :
    originalBaseOnFourAction n (by omega) S e eta t ≠ t ∧
      originalBaseOnFourAction n (by omega) S e eta
        (originalBaseOnFourAction n (by omega) S e eta t) ≠ t ∧
      originalBaseOnFourAction n (by omega) S e eta
        (originalBaseOnFourAction n (by omega) S e eta t) ≠
          originalBaseOnFourAction n (by omega) S e eta t ∧
      (originalBaseOnFourAction n (by omega) S e eta)^3 = 1 ∧
      (∀ v : modelT n S e, v ≠ 1 →
        v = t ∨ v = originalBaseOnFourAction n (by omega) S e eta t ∨
          v = originalBaseOnFourAction n (by omega) S e eta
            (originalBaseOnFourAction n (by omega) S e eta t)) := by
  let : IsKleinFour (modelT n S e) := modelT_isKleinFour n (by omega) S e
  have hthree : orderOf (originalBaseOnFourAction n (by omega) S e eta) = 3 :=
    (originalBaseOnFourAction_order n (by omega) S e eta).trans horder
  obtain ⟨h1,h2,h3,hall⟩ := CFSG.kleinFour_order_three_cycle _ _ hthree t ht
  refine ⟨h1,h2,h3,?_,hall⟩
  have h := pow_orderOf_eq_one (originalBaseOnFourAction n (by omega) S e eta)
  rwa [hthree] at h

end CFSG.Wreathed.BaseFourCentralizerStructure

namespace CFSG.Wreathed.BaseFourCentralizerStructure
open scoped Classical Pointwise IsKleinFour
universe u v

theorem kleinFour_automorphisms_generated_by_two_and_three
    {T : Type u} [Group T] [IsKleinFour T]
    (a b : MulAut T) (ha : orderOf a = 2) (hb : orderOf b = 3) :
    Subgroup.closure {a,b} = (⊤ : Subgroup (MulAut T)) := by
  let H := Subgroup.closure {a,b}
  have haH : a ∈ H := Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := Subgroup.subset_closure (by simp)
  have htwo : 2 ∣ Nat.card H := by
    have h := orderOf_dvd_natCard (⟨a,haH⟩ : H)
    rwa [← Subgroup.orderOf_coe,ha] at h
  have hthree : 3 ∣ Nat.card H := by
    have h := orderOf_dvd_natCard (⟨b,hbH⟩ : H)
    rwa [← Subgroup.orderOf_coe,hb] at h
  have hdvd : Nat.card H ∣ 6 := (CFSG.kleinFour_automorphism_card T) ▸
    H.card_subgroup_dvd_card
  have hle : Nat.card H ≤ 6 := Nat.le_of_dvd (by decide) hdvd
  have hfinite : ∀ d : ℕ, d ≤ 6 → d ∣ 6 → 2 ∣ d → 3 ∣ d → d = 6 := by decide
  apply H.eq_top_of_card_eq
  rw [CFSG.kleinFour_automorphism_card T]
  exact hfinite (Nat.card H) hle hdvd htwo hthree

theorem subgroup_eq_top_of_kernel_and_full_image
    {A : Type u} {B : Type v} [Group A] [Group B]
    (f : A →* B) (D : Subgroup A) (hker : f.ker ≤ D) (himage : D.map f = ⊤) : D = ⊤ := by
  apply top_unique
  intro a _
  have ha : f a ∈ D.map f := by rw [himage]; trivial
  obtain ⟨d,hd,heq⟩ := ha
  have hda : d⁻¹ * a ∈ f.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,heq,inv_mul_cancel]
  have h := D.mul_mem hd (hker hda)
  simpa only [mul_inv_cancel_left] using h

end CFSG.Wreathed.BaseFourCentralizerStructure

namespace CFSG.Wreathed.BaseFourCentralizerStructure
open scoped Classical Pointwise IsKleinFour
universe u
variable {G : Type u} [Group G]

theorem originalBaseNormalizer_normalizes_actual_oddCore [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (eta : Subgroup.normalizer (modelBase S e : Set G)) :
    eta.val ∈ Subgroup.normalizer
      (ambientOddCore (Subgroup.centralizer (modelT n S e : Set G)) : Set G) :=
  modelTNormalizer_normalizes_oddCore n S e
    (modelBase_normalizer_le_modelT_normalizer n hn S e eta.property)

theorem originalBaseNormalizer_order_three_generation [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (eta : Subgroup.normalizer (modelBase S e : Set G))
    (horder : orderOf (modelBaseAction S e eta) = 3) :
    Subgroup.normalizer (modelT n S e : Set G) =
      Subgroup.centralizer (modelT n S e : Set G) ⊔
        Subgroup.closure {wreathModelHom S e (Original.z (2 ^ n)), eta.val} := by
  let N := Subgroup.normalizer (modelT n S e : Set G)
  let C := Subgroup.centralizer (modelT n S e : Set G)
  let B := Subgroup.normalizer (modelBase S e : Set G)
  have hBN : B ≤ N := modelBase_normalizer_le_modelT_normalizer n (by omega) S e
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  let wN : N := Subgroup.inclusion hBN (modelBaseSwapActor S e)
  let etaN : N := Subgroup.inclusion hBN eta
  let D : Subgroup N := C.subgroupOf N ⊔ Subgroup.closure {wN,etaN}
  let f := originalFourNormalizerAction n S e
  let : IsKleinFour (modelT n S e) := modelT_isKleinFour n (by omega) S e
  have hw : orderOf (f wN) = 2 :=
    (originalBaseOnFourAction_order n (by omega) S e (modelBaseSwapActor S e)).trans
      (modelBaseSwapAction_order n (by omega) S e)
  have heta : orderOf (f etaN) = 3 :=
    (originalBaseOnFourAction_order n (by omega) S e eta).trans horder
  have hgen := kleinFour_automorphisms_generated_by_two_and_three (f wN) (f etaN) hw heta
  have hle : Subgroup.closure {f wN,f etaN} ≤ D.map f := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact Subgroup.mem_map_of_mem f ((show Subgroup.closure {wN,etaN} ≤ D from le_sup_right)
      (Subgroup.subset_closure (by simp)))
    · exact Subgroup.mem_map_of_mem f ((show Subgroup.closure {wN,etaN} ≤ D from le_sup_right)
      (Subgroup.subset_closure (by simp)))
  have himage : D.map f = ⊤ := top_unique (hgen ▸ hle)
  have hker : f.ker ≤ D := by
    rw [originalFourNormalizerAction_ker]
    exact le_sup_left
  have hD := subgroup_eq_top_of_kernel_and_full_image f D hker himage
  have h := congrArg (Subgroup.map N.subtype) hD
  change (C.subgroupOf N ⊔ Subgroup.closure {wN,etaN}).map N.subtype = _ at h
  rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hCN,MonoidHom.map_closure,
    Subgroup.map_top,Subgroup.range_subtype] at h
  have hvalues : N.subtype '' {wN,etaN} =
      {wreathModelHom S e (Original.z (2 ^ n)),eta.val} := by
    simp only [Set.image_insert_eq,Set.image_singleton]
    rfl
  rw [hvalues] at h
  exact h.symm

end CFSG.Wreathed.BaseFourCentralizerStructure
namespace CFSG.Wreathed.BaseFourCentralizerStructure
open scoped Classical Pointwise IsKleinFour
universe u
variable {G : Type u} [Group G]

theorem modelBase_eq_actual_generated {m : ℕ}
    (S : Sylow 2 G) (e : S ≃* Wreath m) :
    modelBase S e = Subgroup.closure
      {wreathModelHom S e (Original.s m),wreathModelHom S e (Original.t m)} := by
  unfold modelBase
  rw [base_eq_generated,MonoidHom.map_closure]
  simp [Original.s,Original.t]

theorem modelCenter_eq_actual_zpowers {m : ℕ}
    (S : Sylow 2 G) (e : S ≃* Wreath m) :
    modelCenter S e = Subgroup.zpowers
      (wreathModelHom S e (Original.s m) * wreathModelHom S e (Original.t m)) := by
  unfold modelCenter Original.Z Original.a
  rw [MonoidHom.map_zpowers,map_mul]

theorem modelT_eq_actual_generated
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelT n S e = Subgroup.closure
      {(wreathModelHom S e (Original.s (2 ^ n))) ^ ((2 ^ n)/2),
       (wreathModelHom S e (Original.t (2 ^ n))) ^ ((2 ^ n)/2)} := by
  unfold modelT originalT
  rw [MonoidHom.map_closure]
  simp only [Set.image_insert_eq,Set.image_singleton,map_pow]

theorem modelT_nonidentity_order
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (t : modelT n S e) (ht : t ≠ 1) : orderOf (t : G) = 2 := by
  let hV := modelT_isKleinFour n hn S e
  have hpow : t ^ 2 = 1 := by
    have h := Monoid.pow_exponent_eq_one t
    rwa [hV.exponent_two] at h
  have horder : orderOf t = 2 := orderOf_eq_prime_iff.mpr ⟨hpow,ht⟩
  exact (Subgroup.orderOf_coe t).trans horder

theorem modelBaseFourCentralizer_unique_normal_odd_complement [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (J : Subgroup (Subgroup.centralizer (modelT n S e : Set G))) [J.Normal]
    (hodd : Odd (Nat.card J))
    (hcomp : J.IsComplement' ((modelBase S e).subgroupOf
      (Subgroup.centralizer (modelT n S e : Set G)))) :
    J = CFSG.oddCore (Subgroup.centralizer (modelT n S e : Set G)) := by
  apply normal_odd_two_quotient_eq_oddCore J hodd
  exact (modelBaseFourCentralizerSylow n hn S e).isPGroup'.of_equiv
    hcomp.symm.QuotientMulEquiv.symm

end CFSG.Wreathed.BaseFourCentralizerStructure

namespace CFSG.Wreathed.BaseFourCentralizerStructure
open scoped Classical Pointwise IsKleinFour
universe u
variable {G : Type u} [Group G]

theorem originalSylowCentralizer_split [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    let C := Subgroup.centralizer (S : Set G)
    let Z := modelCenter S e
    let E := ambientOddCore C
    C = Z ⊔ E ∧ Z ⊓ E = ⊥ ∧ Z ≤ Subgroup.centralizer (E : Set G) := by
  let C := Subgroup.centralizer (S : Set G)
  let Z := modelCenter S e
  let E := ambientOddCore C
  have hZC : Z ≤ C := by
    change modelCenter S e ≤ Subgroup.centralizer (S : Set G)
    rw [← sylowCenter_eq_original n hn S e]
    exact sylowCenter_le_centralizer S
  have hcomp : (Z.subgroupOf C).IsComplement' (E.subgroupOf C) := by
    dsimp only [Z,E]
    rw [ambientOddCore_subgroupOf,← sylowCenter_eq_original n hn S e]
    exact (sylowCentralizer_oddCore_complement S).symm
  have hsup := congrArg (Subgroup.map C.subtype) hcomp.sup_eq_top
  rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hZC,
    Subgroup.map_subgroupOf_eq_of_le (ambientOddCore_le C),Subgroup.map_top,
    Subgroup.range_subtype] at hsup
  have hinf := congrArg (Subgroup.map C.subtype) hcomp.disjoint.eq_bot
  rw [Subgroup.map_inf _ _ C.subtype C.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hZC,
    Subgroup.map_subgroupOf_eq_of_le (ambientOddCore_le C),Subgroup.map_bot] at hinf
  refine ⟨hsup.symm,hinf,?_⟩
  apply Subgroup.le_centralizer_iff.mp
  exact (ambientOddCore_le C).trans (by
    intro c hc z hz
    exact Subgroup.mem_centralizer_iff.mp hc z (by
      rw [← sylowCenter_eq_original n hn S e] at hz
      exact sylowCenter_le_sylow S hz))

theorem originalSylowNormalizer_split [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    let N := Subgroup.normalizer (S : Set G)
    let E := ambientOddCore (Subgroup.centralizer (S : Set G))
    N = (S : Subgroup G) ⊔ E ∧ (S : Subgroup G) ⊓ E = ⊥ ∧
      (S : Subgroup G) ≤ Subgroup.centralizer (E : Set G) := by
  let N := Subgroup.normalizer (S : Set G)
  let E := ambientOddCore (Subgroup.centralizer (S : Set G))
  have hEN : E ≤ N := (ambientOddCore_le _).trans (Subgroup.centralizer_le_normalizer _)
  have hSN : (S : Subgroup G) ≤ N := Subgroup.le_normalizer
  have hcomp := originalSylowNormalizer_complement n hn S e
  change ((S : Subgroup G).subgroupOf N).IsComplement' (E.subgroupOf N) at hcomp
  have hsup := congrArg (Subgroup.map N.subtype) hcomp.sup_eq_top
  rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hSN,
    Subgroup.map_subgroupOf_eq_of_le hEN,Subgroup.map_top,Subgroup.range_subtype] at hsup
  have hinf := congrArg (Subgroup.map N.subtype) hcomp.disjoint.eq_bot
  rw [Subgroup.map_inf _ _ N.subtype N.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hSN,
    Subgroup.map_subgroupOf_eq_of_le hEN,Subgroup.map_bot] at hinf
  exact ⟨hsup.symm,hinf,Subgroup.le_centralizer_iff.mp (ambientOddCore_le _)⟩

theorem originalBaseFourCentralizer_quotient_isPGroup [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsPGroup 2 (Subgroup.centralizer (modelT n S e : Set G) ⧸
      CFSG.oddCore (Subgroup.centralizer (modelT n S e : Set G))) :=
  ((modelBaseFourCentralizerSylow n hn S e).isPGroup').of_equiv
    (modelBaseFourCentralizer_oddCore_complement n hn S e).symm.QuotientMulEquiv.symm

end CFSG.Wreathed.BaseFourCentralizerStructure

namespace CFSG.Wreathed.BaseFourCentralizerStructure
open scoped Classical Pointwise IsKleinFour
universe u
variable {G : Type u} [Group G]

theorem originalBaseFourCentralizer_set_product [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (Subgroup.centralizer (modelT n S e : Set G) : Set G) =
      (ambientOddCore (Subgroup.centralizer (modelT n S e : Set G)) : Set G) *
        (modelBase S e : Set G) := by
  let C := Subgroup.centralizer (modelT n S e : Set G)
  have h := modelBaseFourCentralizer_split_and_unique n hn S e
  ext c
  constructor
  · intro hc
    obtain ⟨a,b,hab⟩ := h.2.2.2.2.1 ⟨c,hc⟩
    exact ⟨a.val,a.property,b.val,b.property,hab.symm⟩
  · rintro ⟨a,ha,b,hb,rfl⟩
    exact C.mul_mem (ambientOddCore_le C ha)
      (modelBase_le_modelTCentralizer n (by omega) S e hb)

theorem modelBaseFourCentralizer_ambient_internal_normalizer [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    let C := Subgroup.centralizer (modelT n S e : Set G)
    (Subgroup.normalizer ((modelBase S e).subgroupOf C : Set C)).map C.subtype =
      Subgroup.centralizer (modelBase S e : Set G) := by
  dsimp only
  rw [modelBaseFourCentralizer_internal_normalizer n hn S e,
    Subgroup.map_subgroupOf_eq_of_le
      (Subgroup.centralizer_le (modelT_le_base n (by omega) S e))]

theorem modelT_order_two_iff_ne_one
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (t : modelT n S e) :
    orderOf (t : G) = 2 ↔ t ≠ 1 := by
  constructor
  · intro h ht
    rw [ht,Subgroup.coe_one,orderOf_one] at h
    omega
  · exact modelT_nonidentity_order n hn S e t

theorem modelT_involutions_card
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card {t : modelT n S e // orderOf (t : G) = 2} = 3 := by
  let : IsKleinFour (modelT n S e) := modelT_isKleinFour n hn S e
  have he := Equiv.subtypeEquivRight (modelT_order_two_iff_ne_one n hn S e)
  exact (Nat.card_congr he).trans (CFSG.kleinFour_nonidentity_card _)

theorem originalBaseAction_actual_order {m : ℕ}
    (S : Sylow 2 G) (e : S ≃* Wreath m)
    (eta : Subgroup.normalizer (modelBase S e : Set G)) :
    orderOf (modelBaseAction S e eta) =
      orderOf ((modelBase S e).normalizerMonoidHom eta) :=
  (MulAut.congr (modelBaseEquiv S e).symm).orderOf_eq _

structure SylowAndBaseFourCentralizerStructure [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : Prop where
  base_coordinates : modelBase S e = Subgroup.closure
    {wreathModelHom S e (Original.s (2 ^ n)),wreathModelHom S e (Original.t (2 ^ n))}
  center_coordinates : modelCenter S e = Subgroup.zpowers
    (wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n)))
  four_coordinates : modelT n S e = Subgroup.closure
    {(wreathModelHom S e (Original.s (2 ^ n))) ^ ((2 ^ n)/2),
     (wreathModelHom S e (Original.t (2 ^ n))) ^ ((2 ^ n)/2)}
  kleinFour : IsKleinFour (modelT n S e)
  involutions : Nat.card {t : modelT n S e // orderOf (t : G) = 2} = 3
  centralizer_split : Subgroup.centralizer (S : Set G) =
    modelCenter S e ⊔ ambientOddCore (Subgroup.centralizer (S : Set G))
  centralizer_disjoint : modelCenter S e ⊓
    ambientOddCore (Subgroup.centralizer (S : Set G)) = ⊥
  centralizer_commuting : modelCenter S e ≤
    Subgroup.centralizer (ambientOddCore (Subgroup.centralizer (S : Set G)) : Set G)
  centralizer_direct : ∃ d : modelCenter S e ×
      ambientOddCore (Subgroup.centralizer (S : Set G)) ≃* Subgroup.centralizer (S : Set G),
    ∀ p, (d p : G) = (p.1 : G) * (p.2 : G)
  normalizer_split : Subgroup.normalizer (S : Set G) = (S : Subgroup G) ⊔
    ambientOddCore (Subgroup.centralizer (S : Set G))
  normalizer_disjoint : (S : Subgroup G) ⊓
    ambientOddCore (Subgroup.centralizer (S : Set G)) = ⊥
  normalizer_commuting : (S : Subgroup G) ≤
    Subgroup.centralizer (ambientOddCore (Subgroup.centralizer (S : Set G)) : Set G)
  normalizer_direct : ∃ d : ↥(S : Subgroup G) ×
      ambientOddCore (Subgroup.centralizer (S : Set G)) ≃* Subgroup.normalizer (S : Set G),
    ∀ p, (d p : G) = (p.1 : G) * (p.2 : G)
  base_sylow : ∃ P : Sylow 2 (Subgroup.centralizer (modelT n S e : Set G)),
    (P : Subgroup (Subgroup.centralizer (modelT n S e : Set G))) =
      (modelBase S e).subgroupOf (Subgroup.centralizer (modelT n S e : Set G))
  oddCore_normal : ((ambientOddCore (Subgroup.centralizer (modelT n S e : Set G))).subgroupOf
    (Subgroup.centralizer (modelT n S e : Set G))).Normal
  oddCore_odd : Odd (Nat.card (ambientOddCore (Subgroup.centralizer (modelT n S e : Set G))))
  oddCore_complement : (CFSG.oddCore (Subgroup.centralizer (modelT n S e : Set G))).IsComplement'
    ((modelBase S e).subgroupOf (Subgroup.centralizer (modelT n S e : Set G)))
  base_split : Subgroup.centralizer (modelT n S e : Set G) =
    ambientOddCore (Subgroup.centralizer (modelT n S e : Set G)) ⊔ modelBase S e
  base_set_product : (Subgroup.centralizer (modelT n S e : Set G) : Set G) =
    (ambientOddCore (Subgroup.centralizer (modelT n S e : Set G)) : Set G) *
      (modelBase S e : Set G)
  base_disjoint : ambientOddCore (Subgroup.centralizer (modelT n S e : Set G)) ⊓
    modelBase S e = ⊥
  base_semidirect : ∃ d :
      (ambientOddCore (Subgroup.centralizer (modelT n S e : Set G))) ⋊[
        originalBaseOddCoreAction n hn S e] modelBase S e ≃*
          Subgroup.centralizer (modelT n S e : Set G),
    ∀ p, (d p : G) = (p.left : G) * (p.right : G)
  base_conjugation : ∀ b : modelBase S e,
    ∀ a : ambientOddCore (Subgroup.centralizer (modelT n S e : Set G)),
      (originalBaseOddCoreAction n hn S e b a : G) = (b : G) * (a : G) * (b : G)⁻¹
  base_quotient : ∃ q : modelBase S e ≃*
      (Subgroup.centralizer (modelT n S e : Set G) ⧸
        CFSG.oddCore (Subgroup.centralizer (modelT n S e : Set G))),
    ∀ b, q b = (QuotientGroup.mk' _)
      ⟨b.val,modelBase_le_modelTCentralizer n (by omega) S e b.property⟩
  base_quotient_isPGroup : IsPGroup 2 (Subgroup.centralizer (modelT n S e : Set G) ⧸
    CFSG.oddCore (Subgroup.centralizer (modelT n S e : Set G)))
  complement_unique : ∀ J : Subgroup (Subgroup.centralizer (modelT n S e : Set G)),
    ∀ _hJ : J.Normal, Odd (Nat.card J) →
      J.IsComplement' ((modelBase S e).subgroupOf
        (Subgroup.centralizer (modelT n S e : Set G))) →
          J = CFSG.oddCore (Subgroup.centralizer (modelT n S e : Set G))
  normal_odd_two_quotient_unique :
    ∀ J : Subgroup (Subgroup.centralizer (modelT n S e : Set G)),
      ∀ hJ : J.Normal, Odd (Nat.card J) →
        (letI := hJ; IsPGroup 2 (Subgroup.centralizer (modelT n S e : Set G) ⧸ J)) →
          J = CFSG.oddCore (Subgroup.centralizer (modelT n S e : Set G))
  normalizer_in_centralizer :
    let C := Subgroup.centralizer (modelT n S e : Set G)
    Subgroup.normalizer ((modelBase S e).subgroupOf C : Set C) =
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf C
  ambient_normalizer_in_centralizer :
    let C := Subgroup.centralizer (modelT n S e : Set G)
    (Subgroup.normalizer ((modelBase S e).subgroupOf C : Set C)).map C.subtype =
      Subgroup.centralizer (modelBase S e : Set G)
  four_normalizer : (Subgroup.normalizer (modelT n S e : Set G) : Set G) =
    (Subgroup.centralizer (modelT n S e : Set G) : Set G) *
      (Subgroup.normalizer (modelBase S e : Set G) : Set G)
  normalizer_quotient : ∃ q :
      Subgroup.normalizer (modelT n S e : Set G) ⧸
        (Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
          (Subgroup.normalizer (modelT n S e : Set G)) ≃*
      Subgroup.normalizer (modelBase S e : Set G) ⧸
        (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
          (Subgroup.normalizer (modelBase S e : Set G)),
    ∀ g : Subgroup.normalizer (modelBase S e : Set G),
      q ((QuotientGroup.mk' _)
        (Subgroup.inclusion (modelBase_normalizer_le_modelT_normalizer n (by omega) S e) g)) =
      (QuotientGroup.mk' _) g
  faithful_action : Function.Injective (originalFourNormalizerQuotientAction n S e)
  action_values : ∀ g : Subgroup.normalizer (modelT n S e : Set G), ∀ t : modelT n S e,
    (originalFourNormalizerQuotientAction n S e ((QuotientGroup.mk' _) g) t : G) =
      (g : G) * (t : G) * (g : G)⁻¹
  quotient_alternatives :
    Nat.card (Subgroup.normalizer (modelT n S e : Set G) ⧸
      (Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelT n S e : Set G))) = 2 ∨
      Nonempty (Subgroup.normalizer (modelT n S e : Set G) ⧸
        (Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
          (Subgroup.normalizer (modelT n S e : Set G)) ≃* Equiv.Perm (Fin 3))
  order_three_cycle : ∀ eta : Subgroup.normalizer (modelBase S e : Set G),
    orderOf ((modelBase S e).normalizerMonoidHom eta) = 3 →
      ∀ t : modelT n S e, t ≠ 1 →
        originalBaseOnFourAction n (by omega) S e eta t ≠ t ∧
        originalBaseOnFourAction n (by omega) S e eta
          (originalBaseOnFourAction n (by omega) S e eta t) ≠ t ∧
        originalBaseOnFourAction n (by omega) S e eta
          (originalBaseOnFourAction n (by omega) S e eta t) ≠
            originalBaseOnFourAction n (by omega) S e eta t ∧
        (originalBaseOnFourAction n (by omega) S e eta)^3 = 1 ∧
        (∀ v : modelT n S e, v ≠ 1 →
          v = t ∨ v = originalBaseOnFourAction n (by omega) S e eta t ∨
            v = originalBaseOnFourAction n (by omega) S e eta
              (originalBaseOnFourAction n (by omega) S e eta t))
  order_three_normalizes_oddCore : ∀ eta : Subgroup.normalizer (modelBase S e : Set G),
    orderOf ((modelBase S e).normalizerMonoidHom eta) = 3 →
      eta.val ∈ Subgroup.normalizer
        (ambientOddCore (Subgroup.centralizer (modelT n S e : Set G)) : Set G)
  order_three_generation : ∀ eta : Subgroup.normalizer (modelBase S e : Set G),
    orderOf ((modelBase S e).normalizerMonoidHom eta) = 3 →
      Subgroup.normalizer (modelT n S e : Set G) =
        Subgroup.centralizer (modelT n S e : Set G) ⊔
          Subgroup.closure {wreathModelHom S e (Original.z (2 ^ n)),eta.val}

theorem sylow_and_base_four_group_centralizer_structure [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    SylowAndBaseFourCentralizerStructure n hn S e := by
  have hCS := originalSylowCentralizer_split n hn S e
  have hNS := originalSylowNormalizer_split n hn S e
  have hCT := modelBaseFourCentralizer_split_and_unique n hn S e
  refine {
    base_coordinates := modelBase_eq_actual_generated S e
    center_coordinates := modelCenter_eq_actual_zpowers S e
    four_coordinates := modelT_eq_actual_generated n S e
    kleinFour := modelT_isKleinFour n (by omega) S e
    involutions := modelT_involutions_card n (by omega) S e
    centralizer_split := hCS.1
    centralizer_disjoint := hCS.2.1
    centralizer_commuting := hCS.2.2
    centralizer_direct := ⟨originalSylowCentralizerDirectEquiv n hn S e,?_⟩
    normalizer_split := hNS.1
    normalizer_disjoint := hNS.2.1
    normalizer_commuting := hNS.2.2
    normalizer_direct := ⟨originalSylowNormalizerDirectEquiv n hn S e,?_⟩
    base_sylow := ⟨modelBaseFourCentralizerSylow n hn S e,rfl⟩
    oddCore_normal := hCT.2.2.2.1
    oddCore_odd := hCT.2.2.1
    oddCore_complement := modelBaseFourCentralizer_oddCore_complement n hn S e
    base_split := hCT.1
    base_set_product := originalBaseFourCentralizer_set_product n hn S e
    base_disjoint := hCT.2.1
    base_semidirect := ⟨originalBaseFourCentralizerSemidirectEquiv n hn S e,?_⟩
    base_conjugation := originalBaseOddCoreAction_coe n hn S e
    base_quotient := ⟨originalBaseOddCoreQuotientEquiv n hn S e,
      originalBaseOddCoreQuotientEquiv_apply n hn S e⟩
    base_quotient_isPGroup := originalBaseFourCentralizer_quotient_isPGroup n hn S e
    complement_unique := ?_
    normal_odd_two_quotient_unique := hCT.2.2.2.2.2
    normalizer_in_centralizer := modelBaseFourCentralizer_internal_normalizer n hn S e
    ambient_normalizer_in_centralizer :=
      modelBaseFourCentralizer_ambient_internal_normalizer n hn S e
    four_normalizer := modelTNormalizer_set_product n hn S e
    normalizer_quotient := ⟨originalFourToBaseNormalizerQuotientEquiv n hn S e,
      originalFourToBaseNormalizerQuotientEquiv_mk_inclusion n hn S e⟩
    faithful_action := originalFourNormalizerQuotientAction_injective n S e
    action_values := ?_
    quotient_alternatives := modelTNormalizerQuotient_alternatives n hn S e
    order_three_cycle := ?_
    order_three_normalizes_oddCore := ?_
    order_three_generation := ?_ }
  · intro p
    exact originalSylowCentralizerDirectEquiv_coe n hn S e p.1 p.2
  · intro p
    exact originalSylowNormalizerDirectEquiv_coe n hn S e p.1 p.2
  · exact originalBaseFourCentralizerSemidirectEquiv_coe n hn S e
  · intro J hJ hodd hcomp
    let := hJ
    exact modelBaseFourCentralizer_unique_normal_odd_complement n hn S e J hodd hcomp
  · intro g t
    rw [originalFourNormalizerQuotientAction_mk]
    exact originalFourNormalizerAction_coe n S e g t
  · intro eta horder
    exact originalBaseNormalizer_order_three_cycles n hn S e eta
      ((originalBaseAction_actual_order S e eta).trans horder)
  · intro eta _
    exact originalBaseNormalizer_normalizes_actual_oddCore n (by omega) S e eta
  · intro eta horder
    exact originalBaseNormalizer_order_three_generation n hn S e eta
      ((originalBaseAction_actual_order S e eta).trans horder)

end CFSG.Wreathed.BaseFourCentralizerStructure
