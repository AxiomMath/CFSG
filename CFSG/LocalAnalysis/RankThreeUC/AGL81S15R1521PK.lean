module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftLeaves
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512E
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PG

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open KFactsSmall
open scoped commutatorElement Pointwise

theorem exists_centralizing_pGroup_aux_pow_mem {G : Type*} [Group G] (H : Subgroup G) {x : G}
    {a b : ℕ} (hab : Nat.Coprime a b) (ha : x ^ a ∈ H) (hb : x ^ b = 1) : x ∈ H := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  have e : x = (x ^ a) ^ u := by
    calc x = x ^ (1 : ℤ) := (zpow_one x).symm
      _ = x ^ ((a : ℤ) * u + (b : ℤ) * v) := by
        rw [mul_comm (a : ℤ) u, mul_comm (b : ℤ) v, huv]
      _ = (x ^ (a : ℤ)) ^ u * (x ^ (b : ℤ)) ^ v := by rw [zpow_add, zpow_mul, zpow_mul]
      _ = (x ^ a) ^ u := by rw [zpow_natCast, zpow_natCast, hb, one_zpow, mul_one]
  rw [e]
  exact H.zpow_mem ha u

theorem exists_centralizing_pGroup_aux_conjAut {Y : Type} [Group Y] {K : Subgroup Y} {y : Y}
    (hy : y ∈ Subgroup.normalizer (K : Set Y)) :
    ∃ α : MulAut ↥K, ∀ k : ↥K, ((α k : ↥K) : Y) = y * (k : Y) * y⁻¹ := by
  have hmap : K.map (MulAut.conj y).toMonoidHom = K := liftOf_conj_aux1 hy
  exact ⟨((MulAut.conj y : Y ≃* Y).subgroupMap K).trans (MulEquiv.subgroupCongr hmap),
    fun k => rfl⟩

theorem exists_centralizing_pGroup_aux_conjAut_pow {Y : Type} [Group Y] {K : Subgroup Y} {y : Y}
    {α : MulAut ↥K} (hα : ∀ k : ↥K, ((α k : ↥K) : Y) = y * (k : Y) * y⁻¹) (n : ℕ) (k : ↥K) :
    (((α ^ n) k : ↥K) : Y) = y ^ n * (k : Y) * (y ^ n)⁻¹ := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, hα, pow_succ, mul_inv_rev]
    group

theorem exists_centralizing_pGroup_aux_out {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    (hK : CFSG.Open.IsQuasisimple ↥K) (hS : IsOutTwoGroupList (↥K ⧸ Subgroup.center ↥K))
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card ↥K)
    {y : Y} (hy : y ∈ Subgroup.normalizer (K : Set Y)) (hym : y ^ (p ^ m) = 1) :
    y ∈ Subgroup.centralizer (K : Set Y) := by
  haveI : Group.IsPerfect ↥K := ⟨hK.1⟩
  obtain ⟨α, hα⟩ := exists_centralizing_pGroup_aux_conjAut hy
  have hα1 : α ^ (p ^ m) = 1 := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    rw [exists_centralizing_pGroup_aux_conjAut_pow hα, hym]
    simp
  set π₀ := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K with hπ₀
  have hinj : Function.Injective π₀ :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥K
  have hβ1 : (π₀ α) ^ (p ^ m) = 1 := by rw [← map_pow, hα1, map_one]
  obtain ⟨k₂, hk₂⟩ := KOut_holds (↥K ⧸ Subgroup.center ↥K) hS (π₀ α)
  have hcop2 : Nat.Coprime (2 ^ k₂) (p ^ m) :=
    Nat.Coprime.pow k₂ m ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hβ : π₀ α ∈ (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →* MulAut (↥K ⧸ Subgroup.center ↥K)).range :=
    exists_centralizing_pGroup_aux_pow_mem _ hcop2 hk₂ hβ1
  obtain ⟨sb, hsb⟩ := hβ
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective sb
  have hconj : π₀ (MulAut.conj s) = MulAut.conj (QuotientGroup.mk s : ↥K ⧸ Subgroup.center ↥K) := by
    ext z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 := CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
      (MulAut.conj s) z
    simp only [QuotientGroup.mk'_apply] at h1
    simp [hπ₀, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom, h1,
      MulAut.conj_apply]
  have hαs : α = MulAut.conj s := hinj (by rw [hconj, hsb])
  have hys : ∀ k : ↥K, y * (k : Y) * y⁻¹ = (s : Y) * (k : Y) * (s : Y)⁻¹ := by
    intro k
    rw [← hα k, hαs]
    rfl
  set c : Y := (s : Y)⁻¹ * y with hc
  have hcc : ∀ k ∈ K, k * c = c * k := by
    intro k hk
    have h1 := hys ⟨k, hk⟩
    simp only at h1
    rw [hc]
    calc k * ((s : Y)⁻¹ * y) = (s : Y)⁻¹ * ((s : Y) * k * (s : Y)⁻¹) * y := by group
      _ = (s : Y)⁻¹ * (y * k * y⁻¹) * y := by rw [h1]
      _ = (s : Y)⁻¹ * y * k := by group
  have hcmem : c ∈ Subgroup.centralizer (K : Set Y) := Subgroup.mem_centralizer_iff.2 hcc
  have hcomm : Commute (s : Y) c := hcc s s.2
  have hy' : y = (s : Y) * c := by rw [hc]; group
  have hspow : (s : Y) ^ (p ^ m) ∈ Subgroup.centralizer (K : Set Y) := by
    have h1 : (s : Y) ^ (p ^ m) * c ^ (p ^ m) = 1 := by
      rw [← hcomm.mul_pow, ← hy']
      exact hym
    have h2 : (s : Y) ^ (p ^ m) = (c ^ (p ^ m))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hcmem _)
  have hsK : (s : Y) ^ (Nat.card ↥K) = 1 := by
    have := pow_card_eq_one' (G := ↥K) (x := s)
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime (p ^ m) (Nat.card ↥K) :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK)
  have hsmem : (s : Y) ∈ Subgroup.centralizer (K : Set Y) :=
    exists_centralizing_pGroup_aux_pow_mem _ hcop hspow hsK
  rw [hy']
  exact Subgroup.mul_mem _ hsmem hcmem

theorem exists_centralizing_pGroup_aux_comp_eq {Y : Type} [Group Y] [Finite Y] {K A B : Subgroup Y}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hA : CFSG.Open.IsComponentOf A ⊤)
    (hB : CFSG.Open.IsComponentOf B ⊤) (hle : K ≤ A ⊔ B) : K = A ∨ K = B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hKA, hKB⟩ := hcon
  have h1 : ⁅K, A⁆ = ⊥ := kComp_holds.1 Y K A hK hA hKA
  have h2 : ⁅K, B⁆ = ⊥ := kComp_holds.1 Y K B hK hB hKB
  apply liftOf_unique_aux1 hK
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro k hk
  have hkA := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1 hk
  have hkB := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2 hk
  rw [Subgroup.mem_centralizer_iff] at hkA hkB
  have hsup : A ⊔ B ≤ Subgroup.centralizer ({k} : Set Y) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
      rw [Set.mem_singleton_iff.1 hh]
      exact (hkA a ha).symm
    · refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
      rw [Set.mem_singleton_iff.1 hh]
      exact (hkB b hb).symm
  rw [Subgroup.mem_centralizer_iff]
  intro k' hk'
  have := Subgroup.mem_centralizer_iff.1 (hsup (hle hk')) k rfl
  exact this.symm

theorem exists_centralizing_pGroup_aux_normalClosure {X : Type} [Group X] [Finite X] {L : Subgroup X}
    {y : X}
    (h : ∀ (x : X), ∀ l ∈ L, QuotientGroup.mk' (CFSG.pCore 2 X) y *
        QuotientGroup.mk' (CFSG.pCore 2 X) (x * l * x⁻¹) =
      QuotientGroup.mk' (CFSG.pCore 2 X) (x * l * x⁻¹) * QuotientGroup.mk' (CFSG.pCore 2 X) y) :
    ∀ j ∈ Subgroup.normalClosure (L : Set X), y * j * y⁻¹ * j⁻¹ ∈ CFSG.pCore 2 X := by
  set D : Subgroup X := (Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pCore 2 X) y} :
    Set (X ⧸ CFSG.pCore 2 X))).comap (QuotientGroup.mk' (CFSG.pCore 2 X)) with hD
  have hnc : Subgroup.normalClosure (L : Set X) ≤ D := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro b hb
    obtain ⟨a, ha, hab⟩ := Group.mem_conjugatesOfSet_iff.1 hb
    obtain ⟨c, rfl⟩ := isConj_iff.1 hab
    rw [SetLike.mem_coe, hD, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    exact h c a ha
  intro j hj
  have hjD := hnc hj
  rw [hD, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hjD
  have hc := hjD _ rfl
  refine (QuotientGroup.eq_one_iff _).1 ?_
  change (QuotientGroup.mk' (CFSG.pCore 2 X)) (y * j * y⁻¹ * j⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
  group

theorem exists_centralizing_pGroup_aux_normalizes {X : Type} [Group X] [Finite X]
    (S : Set (Subgroup X)) {N : ℕ} (hS : S.ncard ≤ N)
    (hstab : ∀ (g : X) (K : Subgroup X), K ∈ S → K.map (MulAut.conj g).toMonoidHom ∈ S)
    {y : X} {p m : ℕ} (hym : y ^ (p ^ m) = 1)
    (hcop : ∀ d : ℕ, 0 < d → d ≤ N → Nat.Coprime d (p ^ m))
    {K : Subgroup X} (hK : K ∈ S) : y ∈ Subgroup.normalizer (K : Set X) := by
  classical
  set f : ℕ → Subgroup X := fun i => K.map (MulAut.conj (y ^ i)).toMonoidHom with hf
  have hfS : ∀ i, f i ∈ S := fun i => hstab _ _ hK
  have hkey : ∀ i j : ℕ, i < j → j ≤ N → f i = f j → y ∈ Subgroup.normalizer (K : Set X) := by
    intro i j hij hjN hfij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have hcomp : (MulAut.conj (y ^ i)).toMonoidHom.comp (MulAut.conj (y ^ (d + 1))).toMonoidHom =
        (MulAut.conj (y ^ (i + d + 1))).toMonoidHom := by
      ext a
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show i + d + 1 = i + (d + 1) by omega, pow_add]
      group
    have h1 : (K.map (MulAut.conj (y ^ (d + 1))).toMonoidHom).map (MulAut.conj (y ^ i)).toMonoidHom =
        K.map (MulAut.conj (y ^ i)).toMonoidHom := by
      rw [Subgroup.map_map, hcomp]
      exact hfij.symm
    have h2 : K.map (MulAut.conj (y ^ (d + 1))).toMonoidHom = K :=
      Subgroup.map_injective (MulAut.conj (y ^ i)).injective h1
    have hd : y ^ (d + 1) ∈ Subgroup.normalizer (K : Set X) :=
      mem_normalizer_of_map_conj_eq_s15 h2
    exact exists_centralizing_pGroup_aux_pow_mem (Subgroup.normalizer (K : Set X))
      (hcop (d + 1) (by omega) (by omega)) hd hym
  have hfin : S.Finite := Set.toFinite S
  have hcard : hfin.toFinset.card < (Finset.range (N + 1)).card := by
    rw [Finset.card_range, ← Set.ncard_eq_toFinset_card S hfin]
    omega
  obtain ⟨i, hi, j, hj, hij, hfij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (f := f) (fun i _ => hfin.mem_toFinset.2 (hfS i))
  have hiN : i ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hjN : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hkey i j h hjN hfij
  · exact hkey j i h hiN hfij.symm

theorem exists_centralizing_pGroup_aux_map_normalizer {X Z : Type} [Group X] [Group Z] (f : X →* Z)
    {K : Subgroup X} {y : X} (hy : y ∈ Subgroup.normalizer (K : Set X)) :
    f y ∈ Subgroup.normalizer ((K.map f : Subgroup Z) : Set Z) := by
  have h : (K.map f).map (MulAut.conj (f y)).toMonoidHom = K.map f := by
    have h1 : K.map (MulAut.conj y).toMonoidHom = K := liftOf_conj_aux1 hy
    have h2 : (K.map f).map (MulAut.conj (f y)).toMonoidHom =
        (K.map (MulAut.conj y).toMonoidHom).map f := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext a
      simp [MulAut.conj_apply]
    rw [h2, h1]
  exact mem_normalizer_of_map_conj_eq_s15 h

theorem exists_centralizing_pGroup_aux_key {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsC2 L) {p m N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpJ : ¬ p ∣ Nat.card ↥(Subgroup.normalClosure (L : Set X)))
    (hS : Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} ≤ N)
    (hcop : ∀ d : ℕ, 0 < d → d ≤ N → Nat.Coprime d (p ^ m))
    (hout : ∀ L' : Subgroup X, IsC2 L' → L' ≤ Subgroup.normalClosure (L : Set X) →
      IsOutTwoGroupList (↥(barO2 L') ⧸ Subgroup.center ↥(barO2 L')))
    {y : X} (hym : y ^ (p ^ m) = 1) :
    ∀ j ∈ Subgroup.normalClosure (L : Set X), y * j * y⁻¹ * j⁻¹ ∈ CFSG.pCore 2 X := by
  set J : Subgroup X := Subgroup.normalClosure (L : Set X) with hJ
  set S : Set (Subgroup X) := {L' : Subgroup X | IsC2 L' ∧ L' ≤ J} with hSdef
  have hstab : ∀ (g : X) (K : Subgroup X), K ∈ S → K.map (MulAut.conj g).toMonoidHom ∈ S := by
    intro g K hK
    refine ⟨liftOf_conj_aux4 hK.1 g, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.normalClosure_normal (s := (L : Set X))).conj_mem a (hK.2 ha) g
  have hLS : ∀ x : X, L.map (MulAut.conj x).toMonoidHom ∈ S := by
    intro x
    refine ⟨liftOf_conj_aux4 hL x, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.normalClosure_normal (s := (L : Set X))).conj_mem a
      (Subgroup.le_normalClosure ha) x
  apply exists_centralizing_pGroup_aux_normalClosure
  intro x l hl
  set K' : Subgroup X := L.map (MulAut.conj x).toMonoidHom with hK'
  have hK'S : K' ∈ S := hLS x
  have hnorm : y ∈ Subgroup.normalizer (K' : Set X) :=
    exists_centralizing_pGroup_aux_normalizes S hS hstab hym hcop hK'S
  have hnorm' := exists_centralizing_pGroup_aux_map_normalizer
    (QuotientGroup.mk' (CFSG.pCore 2 X)) hnorm
  have hpK : ¬ p ∣ Nat.card ↥(barO2 K') := fun h =>
    hpJ (h.trans ((Subgroup.card_map_dvd _ _).trans (Subgroup.card_dvd_of_le hK'S.2)))
  have hym' : (QuotientGroup.mk' (CFSG.pCore 2 X) y) ^ (p ^ m) = 1 := by
    rw [← map_pow, hym, map_one]
  have hcent := exists_centralizing_pGroup_aux_out hK'S.1.component.2.2 (hout K' hK'S.1 hK'S.2)
    hp hp2 hpK hnorm' hym'
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 X) (x * l * x⁻¹) ∈ barO2 K' :=
    ⟨x * l * x⁻¹, ⟨l, hl, rfl⟩, rfl⟩
  have := Subgroup.mem_centralizer_iff.1 hcent _ hmem
  exact this.symm

theorem exists_centralizing_pGroup_aux_centerIn_map {Y Z : Type} [Group Y] [Group Z] (f : Y →* Z)
    (hf : Function.Injective f) (K : Subgroup Y) :
    KFactsPair.centerIn (K.map f) = (KFactsPair.centerIn K).map f := by
  ext z
  rw [mem_centerIn_iff_s15, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hc⟩
    refine ⟨k, (mem_centerIn_iff_s15 K k).2 ⟨hk, fun g hg => ?_⟩, rfl⟩
    have := hc (f g) ⟨g, hg, rfl⟩
    exact hf (by rw [map_mul, map_mul]; exact this)
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hkK, hkc⟩ := (mem_centerIn_iff_s15 K k).1 hk
    refine ⟨⟨k, hkK, rfl⟩, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, hkc g hg]

theorem exists_centralizing_pGroup_aux_subnormal {Y : Type} [Group Y] {A B : Subgroup Y}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hN : (A ⊔ B).Normal) :
    CFSG.Open.IsSubnormal A ⊤ := by
  have hBA : B ≤ Subgroup.normalizer (A : Set Y) := by
    refine le_trans (fun b hb => ?_) (Subgroup.centralizer_le_normalizer (A : Set Y))
    exact Subgroup.mem_centralizer_iff.2 (fun a ha => hc a ha b hb)
  have h1 : (A.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hBA)
  have h2 : ((A ⊔ B).subgroupOf ⊤).Normal := inferInstance
  exact CFSG.Open.IsSubnormal.step le_sup_left h1
    (CFSG.Open.IsSubnormal.step le_top h2 (CFSG.Open.IsSubnormal.refl ⊤))

theorem exists_centralizing_pGroup_aux_centralProd {X : Type} [Group X] [Finite X] {J : Subgroup X}
    (hJ : J.Normal) (hcp : IsCentralProdA6Z3 ↥(barO2 J)) :
    ∃ A B : Subgroup (X ⧸ CFSG.pCore 2 X), IsAltSixCoverThree ↥A ∧ IsAltSixCoverThree ↥B ∧
      A ⊔ B = barO2 J ∧ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧
      KFactsPair.centerIn A = A ⊓ B ∧ KFactsPair.centerIn B = A ⊓ B ∧
      CFSG.Open.IsComponentOf A ⊤ ∧ CFSG.Open.IsComponentOf B ⊤ := by
  obtain ⟨K₁, K₂, h1, h2, hsup, hcomm, hin1, hin2⟩ := hcp
  rw [← centerIn_eq_cfsg] at hin1 hin2
  set f : ↥(barO2 J) →* (X ⧸ CFSG.pCore 2 X) := (barO2 J).subtype with hfdef
  have hf : Function.Injective f := (barO2 J).subtype_injective
  have hA : IsAltSixCoverThree ↥(K₁.map f) :=
    isAltSixCoverThree_of_mulEquiv (K₁.equivMapOfInjective f hf).symm h1
  have hB : IsAltSixCoverThree ↥(K₂.map f) :=
    isAltSixCoverThree_of_mulEquiv (K₂.equivMapOfInjective f hf).symm h2
  have hsupAB : K₁.map f ⊔ K₂.map f = barO2 J := by
    rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype _
  have hcAB : ∀ a ∈ K₁.map f, ∀ b ∈ K₂.map f, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 (hcomm ha) b hb
    rw [← map_mul, ← map_mul, this]
  have hNJ : (K₁.map f ⊔ K₂.map f).Normal := by
    rw [hsupAB]
    exact Subgroup.Normal.map hJ _ (QuotientGroup.mk'_surjective _)
  refine ⟨K₁.map f, K₂.map f, hA, hB, hsupAB, hcAB, ?_, ?_, ?_, ?_⟩
  · rw [exists_centralizing_pGroup_aux_centerIn_map f hf, ← hin1, Subgroup.map_inf_eq _ _ f hf]
  · rw [exists_centralizing_pGroup_aux_centerIn_map f hf, ← hin2, Subgroup.map_inf_eq _ _ f hf]
  · exact ⟨le_top, exists_centralizing_pGroup_aux_subnormal hcAB hNJ, hA.1⟩
  · refine ⟨le_top, exists_centralizing_pGroup_aux_subnormal (A := K₂.map f) (B := K₁.map f) ?_ ?_,
      hB.1⟩
    · exact fun b hb a ha => (hcAB a ha b hb).symm
    · rwa [sup_comm]

theorem exists_centralizing_pGroup_aux_outList_of_eq {Y : Type} [Group Y] {K A : Subgroup Y} (h : K = A)
    (hA : IsAltSixCoverThree ↥A) : IsOutTwoGroupList (↥K ⧸ Subgroup.center ↥K) := by
  subst h
  exact Or.inl hA.2.2

theorem exists_centralizing_pGroup_aux_lThree_of_mulEquiv {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (h : IsLThreeOfExp 1 S') : IsLThreeOfExp 1 S := by
  rcases h with ⟨h1, d, q, hq, hd, ⟨e'⟩⟩ | ⟨h2, -⟩
  · exact Or.inl ⟨h1, d, q, hq, hd, ⟨e.trans e'⟩⟩
  · omega

theorem exists_centralizing_pGroup_aux_outList_lThree {S : Type} [Group S]
    (h : IsLThreeOfExp 1 S) : IsOutTwoGroupList (S ⧸ Subgroup.center S) := by
  obtain ⟨hs, hc⟩ := small1522_simple_center_aux3 (isLThreeTwo_iff_isLThreeOfExp_one.2 h)
  haveI := hs
  have hZ : Subgroup.center S = ⊥ := small1522_simple_center_aux1 (by rw [hc]; norm_num)
  have e : (S ⧸ Subgroup.center S) ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  rcases h with ⟨-, d, q, hq, hd, ⟨e'⟩⟩ | ⟨h2, -⟩
  · exact Or.inr (Or.inr ⟨d, Or.inr (Or.inr ⟨q, hq, hd⟩), ⟨e.trans e'⟩⟩)
  · omega

theorem exists_centralizing_pGroup_aux_branch1 {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsC2 L) (hcp : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set X))))
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpJ : ¬ p ∣ Nat.card ↥(Subgroup.normalClosure (L : Set X))) {y : X} (hym : y ^ (p ^ m) = 1) :
    ∀ j ∈ Subgroup.normalClosure (L : Set X), y * j * y⁻¹ * j⁻¹ ∈ CFSG.pCore 2 X := by
  obtain ⟨A, B, hA, hB, hsup, hcAB, -, -, hAc, hBc⟩ :=
    exists_centralizing_pGroup_aux_centralProd Subgroup.normalClosure_normal hcp
  have hcomp : ∀ L' : Subgroup X, IsC2 L' → L' ≤ Subgroup.normalClosure (L : Set X) →
      barO2 L' = A ∨ barO2 L' = B := by
    intro L' hL' hLJ
    refine exists_centralizing_pGroup_aux_comp_eq hL'.component hAc hBc ?_
    rw [hsup]
    exact Subgroup.map_mono hLJ
  have hS : Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} ≤ 2 := by
    have hfin : ({A, B} : Set (Subgroup (X ⧸ CFSG.pCore 2 X))).Finite := Set.toFinite _
    calc Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)}
        ≤ Set.ncard ({A, B} : Set (Subgroup (X ⧸ CFSG.pCore 2 X))) := by
          refine Set.ncard_le_ncard_of_injOn (fun L' => barO2 L') (fun L' hL' => ?_) ?_ hfin
          · rcases hcomp L' hL'.1 hL'.2 with h | h
            · exact Or.inl h
            · exact Or.inr h
          · intro L₁ hL₁ L₂ hL₂ h
            exact isC2_eq_of_barO2_eq hL₁.1 hL₂.1 h
      _ ≤ 2 := by
          calc Set.ncard ({A, B} : Set (Subgroup (X ⧸ CFSG.pCore 2 X)))
              ≤ Set.ncard ({B} : Set (Subgroup (X ⧸ CFSG.pCore 2 X))) + 1 := Set.ncard_insert_le _ _
            _ = 2 := by rw [Set.ncard_singleton]
  have hcop : ∀ d : ℕ, 0 < d → d ≤ 2 → Nat.Coprime d (p ^ m) := by
    intro d hd hd2
    refine Nat.Coprime.pow_right m ?_
    interval_cases d
    · exact Nat.coprime_one_left p
    · exact (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  refine exists_centralizing_pGroup_aux_key hL hp hp2 hpJ hS hcop ?_ hym
  intro L' hL' hLJ
  rcases hcomp L' hL' hLJ with h | h
  · exact exists_centralizing_pGroup_aux_outList_of_eq h hA
  · exact exists_centralizing_pGroup_aux_outList_of_eq h hB

theorem exists_centralizing_pGroup_aux_branch2 {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsC2 L) (hL3 : IsLThreeOfExp 1 ↥(barO2 L))
    (hr3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpJ : ¬ p ∣ Nat.card ↥(Subgroup.normalClosure (L : Set X))) {y : X} (hym : y ^ (p ^ m) = 1) :
    ∀ j ∈ Subgroup.normalClosure (L : Set X), y * j * y⁻¹ * j⁻¹ ∈ CFSG.pCore 2 X := by
  obtain ⟨hs, hc⟩ := small1522_simple_center_aux3 (isLThreeTwo_iff_isLThreeOfExp_one.2 hL3)
  haveI := hs
  have hZ : Subgroup.center ↥(barO2 L) = ⊥ := small1522_simple_center_aux1 (by rw [hc]; norm_num)
  have hcenter : KFactsPair.centerIn (barO2 L) = ⊥ := by
    unfold KFactsPair.centerIn
    rw [hZ, Subgroup.map_bot]
  have h3L : 3 ∣ Nat.card L := by
    have h1 : Nat.card ↥(barO2 L) ∣ Nat.card L := Subgroup.card_map_dvd _ _
    rw [hc] at h1
    exact (show 3 ∣ 168 by norm_num).trans h1
  have h3J : 3 ∣ Nat.card ↥(Subgroup.normalClosure (L : Set X)) :=
    h3L.trans (Subgroup.card_dvd_of_le Subgroup.le_normalClosure)
  have hp3 : p ≠ 3 := fun h => hpJ (h ▸ h3J)
  have hm1 : 1 ≤ CFSG.Open.pRank 3 L := (one_le_pRank_iff_dvd L Nat.prime_three).2 h3L
  have hbound := pRank_normalClosure_ge hL Nat.prime_three (by norm_num) (s := 0) (by
    rw [hcenter]
    exact (pRank_eq_zero_of_not_dvd_s15 Nat.prime_three (by rw [Subgroup.card_bot]; norm_num)).le)
  have hJ3 : CFSG.Open.pRank 3 (Subgroup.normalClosure (L : Set X)) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt le_top).trans hr3
  have hS : Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} ≤ 3 := by
    set k := Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)}
    have : k ≤ k * CFSG.Open.pRank 3 L := Nat.le_mul_of_pos_right k hm1
    simp only [mul_zero, add_zero] at hbound
    omega
  have hcop : ∀ d : ℕ, 0 < d → d ≤ 3 → Nat.Coprime d (p ^ m) := by
    intro d hd hd3
    refine Nat.Coprime.pow_right m ?_
    interval_cases d
    · exact Nat.coprime_one_left p
    · exact (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    · exact (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  refine exists_centralizing_pGroup_aux_key hL hp hp2 hpJ hS hcop ?_ hym
  intro L' hL' hLJ
  obtain ⟨x, rfl⟩ := isC2_le_normalClosure_conj hL hL' hLJ
  refine exists_centralizing_pGroup_aux_outList_lThree ?_
  rw [barO2_map_conj]
  exact exists_centralizing_pGroup_aux_lThree_of_mulEquiv
    ((barO2 L).equivMapOfInjective (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 X) x)).toMonoidHom
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 X) x)).injective).symm hL3

theorem exists_centralizing_pGroup_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (hr3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) ≤ 3)
    (h20 : Row1520 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    {p : ℕ} (hp : p ∈ sigmaM G M) (hpJ : ¬ p ∣ Nat.card (Subgroup.normalClosure (L : Set ↥M)))
    (hsh : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set ↥M))) ∨
      IsLThreeOfExp 1 ↥(barO2 L)) :
    ∃ P₀ : Subgroup ↥M, IsPGroup p P₀ ∧ 2 ≤ CFSG.Open.pRank p P₀ ∧
      ∀ y ∈ P₀, ∀ j ∈ Subgroup.normalClosure (L : Set ↥M), ⁅y, j⁆ ∈ CFSG.pCore 2 ↥M := by
  have hpP : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hrk : 1 < CFSG.Open.pRank p (cMBar L) := (h20 p hp Ls L hLs hL).2.1
  have hrk2 : 2 ≤ CFSG.Open.pRank p (cMHat L) := by
    refine two_le_pRank_of_map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) hpP hp2 (cMHat L) ?_
    have h1 : (cMHat L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) = cMBar L :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) (cMBar L)
    rw [h1]
    exact hrk
  obtain ⟨P₀, hP₀le, hP₀a, hP₀c⟩ := CFSG.SectionRank.exists_pRank hpP.one_lt (cMHat L)
  have hP₀p : IsPGroup p P₀ := IsPGroup.of_card hP₀c
  have hP₀rk : 2 ≤ CFSG.Open.pRank p P₀ :=
    hrk2.trans (CFSG.SectionRank.le_pRank hpP.one_lt le_rfl hP₀a hP₀c)
  refine ⟨P₀, hP₀p, hP₀rk, fun y hy j hj => ?_⟩
  obtain ⟨m, hm⟩ := hP₀p ⟨y, hy⟩
  have hym : y ^ (p ^ m) = 1 := congrArg Subtype.val hm
  rw [commutatorElement_def]
  rcases hsh with hcp | hL3
  · exact exists_centralizing_pGroup_aux_branch1 hL.1 hcp hpP hp2 hpJ hym j hj
  · exact exists_centralizing_pGroup_aux_branch2 hL.1 hL3 hr3 hpP hp2 hpJ hym j hj

theorem exists_centralizing_pGroup {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    {p : ℕ} (hp : p ∈ sigmaM G M) (hpJ : ¬ p ∣ Nat.card (Subgroup.normalClosure (L : Set ↥M)))
    (hsh : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set ↥M))) ∨
      IsLThreeOfExp 1 ↥(barO2 L)) :
    ∃ P₀ : Subgroup ↥M, IsPGroup p P₀ ∧ 2 ≤ CFSG.Open.pRank p P₀ ∧
      ∀ y ∈ P₀, ∀ j ∈ Subgroup.normalClosure (L : Set ↥M), ⁅y, j⁆ ∈ CFSG.pCore 2 ↥M :=
  exists_centralizing_pGroup_gen (ctx.rank_odd 3 Nat.prime_three (by norm_num)) h20 hLs hL hp hpJ hsh

section ExistsE9

variable {X : Type} [Group X] [Finite X]

theorem exists_E9_of_ne_aux_Y0_gen {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L) :
    Y0 T T₁ T₂ ≤ Subgroup.normalizer (L : Set X) := by
  intro y hy
  have hY : Ystar T T₁ T₂ ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) := by
    unfold Ystar
    refine iSup₂_le (fun Ls' hLs' => ?_)
    by_cases h : Ls' = Ls
    · rw [h]
      exact Subgroup.le_normalizer
    · have hc : ⁅Ls', Ls⁆ = ⊥ := kComp_holds.1 (X ⧸ gnC T) Ls' Ls hLs'.1 hl.comp.1 h
      intro z hz
      exact Subgroup.centralizer_le_normalizer (Ls : Set (X ⧸ gnC T))
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc hz)
  exact mem_normalizer_of_map_conj_eq_s15 (liftOf_conj hl.gn hl.comp.1 hl.lift y (hY hy))

theorem exists_E9_of_ne_aux_Y0 {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hl : LiftCtx X T T₁ T₂ Ls L) : Y0 T T₁ T₂ ≤ Subgroup.normalizer (L : Set X) :=
  exists_E9_of_ne_aux_Y0_gen hl.toGen

theorem exists_E9_of_ne_aux_move_gen {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L)
    (hne : L ≠ Subgroup.normalClosure (L : Set X)) :
    ∃ g : X, (g ∈ Subgroup.normalizer (T₁ : Set X) ∨ g ∈ Subgroup.normalizer (T₂ : Set X)) ∧
      g ∉ Subgroup.normalizer (L : Set X) := by
  by_contra hcon
  push Not at hcon
  apply hne
  have htop : ∀ x : X, x ∈ Subgroup.normalizer (L : Set X) := by
    intro x
    obtain ⟨a, ha, y, hy, b, hb, rfl⟩ := hl.good.factor x
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact hcon a (Or.inl (Subgroup.centralizer_le_normalizer (T₁ : Set X) ha))
    · exact exists_E9_of_ne_aux_Y0_gen hl hy
    · exact hcon b (Or.inr hb)
  haveI : L.Normal := ⟨fun n hn g => ((Subgroup.mem_normalizer_iff.1 (htop g)) n).1 hn⟩
  exact (Subgroup.normalClosure_eq_self L).symm

theorem exists_E9_of_ne_aux_move {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hl : LiftCtx X T T₁ T₂ Ls L) (hne : L ≠ Subgroup.normalClosure (L : Set X)) :
    ∃ g : X, (g ∈ Subgroup.normalizer (T₁ : Set X) ∨ g ∈ Subgroup.normalizer (T₂ : Set X)) ∧
      g ∉ Subgroup.normalizer (L : Set X) :=
  exists_E9_of_ne_aux_move_gen hl.toGen hne

theorem exists_E9_of_ne_aux_ppart {G H : Type*} [Group G] [Group H] (f : G →* H) {x₀ : G} {y : H}
    (hy : f x₀ = y) {k : ℕ} (hk : y ^ (3 ^ k) = 1) (hfin : 0 < orderOf x₀) :
    ∃ x ∈ Subgroup.zpowers x₀, (∃ a : ℕ, x ^ (3 ^ a) = 1) ∧ f x = y := by
  obtain ⟨a, n', hn', hn_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hfin.ne' 3 (by norm_num)
  have hcop : Nat.Coprime n' (3 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hn').symm
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  refine ⟨x₀ ^ ((n' : ℤ) * u), Subgroup.zpow_mem _ (Subgroup.mem_zpowers x₀) _, ⟨a, ?_⟩, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul]
    have : (n' : ℤ) * u * ((3 ^ a : ℕ) : ℤ) = (orderOf x₀ : ℤ) * u := by
      rw [hn_eq]
      push_cast
      ring
    rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · rw [map_zpow, hy]
    have e1 : (n' : ℤ) * u = 1 - v * ((3 ^ k : ℕ) : ℤ) := by linarith [huv]
    have e2 : y ^ (v * ((3 ^ k : ℕ) : ℤ)) = 1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    rw [e1, zpow_sub, zpow_one, e2, inv_one, mul_one]

theorem exists_E9_of_ne_aux_gnC_le {T T₁ T₂ : Subgroup X} (hg : GNGood T T₁ T₂) :
    gnC T ≤ Subgroup.centralizer (T₁ : Set X) := by
  have h1 : T₁ ≤ gnV T := fun x hx => Subgroup.le_normalClosure (hg.pair.le_center hx)
  exact Subgroup.centralizer_le (fun x hx => h1 hx)

theorem exists_E9_of_ne_aux_good3 {T T₁ T₂ : Subgroup X} (hg : GNGood T T₁ T₂)
    {Ls' : Subgroup (X ⧸ gnC T)} {L' : Subgroup X} (hLs' : GNYComponent T T₁ T₂ Ls')
    (hL' : LiftOf T L' Ls') :
    ∃ x ∈ Subgroup.normalizer (T₁ : Set X) ⊓ L', (∃ a : ℕ, x ^ (3 ^ a) = 1) ∧
      ∃ l ∈ L', toStar T (x * l) ≠ toStar T (l * x) := by
  have h3 := (hg.three Ls' hLs').1
  have hex : ∃ y ∈ gnA T T₁ Ls', (∃ k : ℕ, orderOf y = 3 ^ k) ∧
      y ∉ (Subgroup.center ↥Ls').map Ls'.subtype := by
    by_contra hcon
    push Not at hcon
    apply h3
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyA, hk⟩
    exact hcon y hyA hk
  obtain ⟨y, hyA, ⟨k, hk⟩, hyz⟩ := hex
  obtain ⟨x₀, ⟨hx₀N, hx₀L⟩, hx₀y⟩ := gnA_le_map_normalizer_one hg hL' hyA
  have hyk : y ^ (3 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
  obtain ⟨x, hxz, ⟨a, hxa⟩, hxy⟩ :=
    exists_E9_of_ne_aux_ppart (toStar T) hx₀y hyk (orderOf_pos x₀)
  have hxNL : x ∈ Subgroup.normalizer (T₁ : Set X) ⊓ L' := by
    have : Subgroup.zpowers x₀ ≤ Subgroup.normalizer (T₁ : Set X) ⊓ L' :=
      (Subgroup.zpowers_le).2 ⟨hx₀N, hx₀L⟩
    exact this hxz
  refine ⟨x, hxNL, ⟨a, hxa⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hyz
  have hyLs : y ∈ Ls' := (inf_le_right : gnA T T₁ Ls' ≤ Ls') hyA
  refine ⟨⟨y, hyLs⟩, ?_, rfl⟩
  show (⟨y, hyLs⟩ : ↥Ls') ∈ Subgroup.center ↥Ls'
  rw [Subgroup.mem_center_iff]
  intro g
  have hg' : (g : X ⧸ gnC T) ∈ L'.map (toStar T) := by rw [hL'.2]; exact g.2
  obtain ⟨l, hl, hlg⟩ := hg'
  apply Subtype.ext
  show (g : X ⧸ gnC T) * y = y * (g : X ⧸ gnC T)
  rw [← hlg, ← hxy, ← map_mul, ← map_mul]
  exact (hcon l hl).symm

theorem exists_E9_of_ne_aux_nc {Y : Type} [Group Y] [Finite Y] {u v : Y} (huv : Commute u v)
    {a b : ℕ} (hu : u ^ (3 ^ a) = 1) (hv : v ^ (3 ^ b) = 1)
    (h1 : u ∉ Subgroup.zpowers v) (h2 : v ∉ Subgroup.zpowers u) :
    2 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers u ⊔ Subgroup.zpowers v) := by
  set A := Subgroup.zpowers u with hA
  set B := Subgroup.zpowers v with hB
  have hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (huv.zpow_zpow i j).eq
  obtain ⟨α, -, hα⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hu)
  obtain ⟨β, -, hβ⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hv)
  have hAcard : Nat.card A = 3 ^ α := by rw [hA, Nat.card_zpowers, hα]
  have hBcard : Nat.card B = 3 ^ β := by rw [hB, Nat.card_zpowers, hβ]
  have hcardAB := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hAB).1
  have hpg : IsPGroup 3 ↥(A ⊔ B) := by
    have hdvd : Nat.card ↥(A ⊔ B) ∣ 3 ^ (α + β) := by
      rw [pow_add, ← hAcard, ← hBcard]
      exact Dvd.intro _ hcardAB
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact IsPGroup.of_card hc
  have huAB : u ∈ A ⊔ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  have hvAB : v ∈ A ⊔ B := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  have hnc : ¬ IsCyclic ↥(A ⊔ B) := by
    intro hcyc
    haveI := hcyc
    have hc1 : Nat.card (A.subgroupOf (A ⊔ B)) = 3 ^ α := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B)).toEquiv]
      exact hAcard
    have hc2 : Nat.card (B.subgroupOf (A ⊔ B)) = 3 ^ β := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : B ≤ A ⊔ B)).toEquiv]
      exact hBcard
    rcases le_total α β with h | h
    · have hle : A.subgroupOf (A ⊔ B) ≤ B.subgroupOf (A ⊔ B) :=
        IsCyclic.subgroup_le_iff_card_dvd.2 (by rw [hc1, hc2]; exact Nat.pow_dvd_pow 3 h)
      apply h1
      have hu' : (⟨u, huAB⟩ : ↥(A ⊔ B)) ∈ A.subgroupOf (A ⊔ B) :=
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers u)
      exact Subgroup.mem_subgroupOf.1 (hle hu')
    · have hle : B.subgroupOf (A ⊔ B) ≤ A.subgroupOf (A ⊔ B) :=
        IsCyclic.subgroup_le_iff_card_dvd.2 (by rw [hc1, hc2]; exact Nat.pow_dvd_pow 3 h)
      apply h2
      have hv' : (⟨v, hvAB⟩ : ↥(A ⊔ B)) ∈ B.subgroupOf (A ⊔ B) :=
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers v)
      exact Subgroup.mem_subgroupOf.1 (hle hv')
  exact CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic Nat.prime_three
    (by norm_num) hpg hnc

theorem exists_E9_of_ne_gen {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L)
    (hne : L ≠ Subgroup.normalClosure (L : Set X))
    (hsh : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set X))) ∨
      (IsLThreeOfExp 1 ↥(barO2 L) ∧
        Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} ≤ 3)) :
    ∃ E : Subgroup X, E ≤ Subgroup.normalClosure (L : Set X) ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      E ≤ Subgroup.normalizer (T₁ : Set X) := by
  clear hsh
  set J : Subgroup X := Subgroup.normalClosure (L : Set X) with hJ
  set π : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  obtain ⟨g, hgN, hgL⟩ := exists_E9_of_ne_aux_move_gen hl hne
  set L' : Subgroup X := L.map (MulAut.conj g).toMonoidHom with hL'
  have hL'ne : L' ≠ L := fun h => hgL (mem_normalizer_of_map_conj_eq_s15 h)
  have hL'C : IsC2 L' := liftOf_conj_aux4 hl.lift.1 g
  have hL'J : L' ≤ J := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.normalClosure_normal (s := (L : Set X))).conj_mem a
      (Subgroup.le_normalClosure ha) g
  obtain ⟨x₁, hx₁, ⟨a₁, hx₁a⟩, l₁, hl₁, hx₁nc⟩ :=
    exists_E9_of_ne_aux_good3 hl.good hl.comp hl.lift
  have hconj_el : g * x₁ * g⁻¹ ∈ L' := ⟨x₁, (Subgroup.mem_inf.1 hx₁).2, rfl⟩
  have hconj_pow : (g * x₁ * g⁻¹) ^ (3 ^ a₁) = 1 := by rw [conj_pow, hx₁a]; group
  have hconj_nc : ∃ l ∈ L', toStar T ((g * x₁ * g⁻¹) * l) ≠ toStar T (l * (g * x₁ * g⁻¹)) := by
    refine ⟨g * l₁ * g⁻¹, ⟨l₁, hl₁, rfl⟩, fun h => hx₁nc ?_⟩
    have e1 : g * x₁ * g⁻¹ * (g * l₁ * g⁻¹) = g * (x₁ * l₁) * g⁻¹ := by group
    have e2 : g * l₁ * g⁻¹ * (g * x₁ * g⁻¹) = g * (l₁ * x₁) * g⁻¹ := by group
    rw [e1, e2] at h
    simp only [map_mul, map_inv] at h
    simpa only [map_mul] using mul_left_cancel (mul_right_cancel h)
  have hx₂ : ∃ x₂ ∈ Subgroup.normalizer (T₁ : Set X) ⊓ L', (∃ a : ℕ, x₂ ^ (3 ^ a) = 1) ∧
      ∃ l ∈ L', toStar T (x₂ * l) ≠ toStar T (l * x₂) := by
    rcases hgN with hg1 | hg2
    · refine ⟨g * x₁ * g⁻¹, Subgroup.mem_inf.2 ⟨?_, hconj_el⟩, ⟨a₁, hconj_pow⟩, hconj_nc⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg1 (Subgroup.mem_inf.1 hx₁).1)
        (Subgroup.inv_mem _ hg1)
    · set Ls' : Subgroup (X ⧸ gnC T) := L'.map (toStar T) with hLs'
      have hLs'eq : Ls' = Ls.map (MulAut.conj (toStar T g)).toMonoidHom := by
        have hcomp : (toStar T).comp (MulAut.conj g).toMonoidHom =
            (MulAut.conj (toStar T g)).toMonoidHom.comp (toStar T) := by
          ext a
          simp [MulAut.conj_apply]
        rw [hLs', hL', Subgroup.map_map, hcomp, ← Subgroup.map_map, hl.lift.2]
      have hcomp' : CFSG.Open.IsComponentOf Ls' ⊤ := by
        rw [hLs'eq]
        exact liftOf_conj_aux3 hl.comp.1 (MulAut.conj (toStar T g))
      have hlift' : LiftOf T L' Ls' := ⟨hL'C, rfl⟩
      have hnN : ¬ Ls' ≤ gnImg T (Subgroup.normalizer (T₂ : Set X)) := by
        intro hle
        apply hl.comp.2.2
        intro s hs
        have hmem : toStar T g * s * (toStar T g)⁻¹ ∈ Ls' := by
          rw [hLs'eq]
          exact ⟨s, hs, rfl⟩
        obtain ⟨n, hn, hns⟩ := hle hmem
        refine ⟨g⁻¹ * n * g, ?_, ?_⟩
        · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg2) hn) hg2
        · have h1 : toStar T n = toStar T g * s * (toStar T g)⁻¹ := hns
          show toStar T (g⁻¹ * n * g) = s
          rw [map_mul, map_mul, map_inv, h1]
          group
      by_cases hc : Ls' ≤ gnImg T (Subgroup.centralizer (T₁ : Set X))
      · have hL'C1 : L' ≤ Subgroup.centralizer (T₁ : Set X) := by
          intro l' hl'
          have hmem : toStar T l' ∈ Ls' := ⟨l', hl', rfl⟩
          obtain ⟨c, hc1, hcl⟩ := hc hmem
          have h1 : c⁻¹ * l' ∈ gnC T := QuotientGroup.eq.1 hcl
          have h2 : c⁻¹ * l' ∈ Subgroup.centralizer (T₁ : Set X) :=
            exists_E9_of_ne_aux_gnC_le hl.good h1
          have h3 : l' = c * (c⁻¹ * l') := by group
          rw [h3]
          exact Subgroup.mul_mem _ hc1 h2
        refine ⟨g * x₁ * g⁻¹, Subgroup.mem_inf.2 ⟨?_, hconj_el⟩, ⟨a₁, hconj_pow⟩, hconj_nc⟩
        exact Subgroup.centralizer_le_normalizer (T₁ : Set X) (hL'C1 hconj_el)
      · exact exists_E9_of_ne_aux_good3 hl.good ⟨hcomp', hc, hnN⟩ hlift'
  obtain ⟨x₂, hx₂mem, ⟨a₂, hx₂a⟩, l₂, hl₂, hx₂nc⟩ := hx₂
  have hx₁N : x₁ ∈ Subgroup.normalizer (T₁ : Set X) := (Subgroup.mem_inf.1 hx₁).1
  have hx₁L : x₁ ∈ L := (Subgroup.mem_inf.1 hx₁).2
  have hx₂N : x₂ ∈ Subgroup.normalizer (T₁ : Set X) := (Subgroup.mem_inf.1 hx₂mem).1
  have hx₂L : x₂ ∈ L' := (Subgroup.mem_inf.1 hx₂mem).2
  have hcomm := isC2_commute_of_ne hl.lift.1 hL'C hL'ne.symm
  have hcomm' : ∀ a ∈ barO2 L, ∀ b ∈ barO2 L', a * b = b * a := by
    intro a ha b hb
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm ha
    exact (Subgroup.mem_centralizer_iff.1 this b hb).symm
  have htoStar : ∀ a b : X, π a = π b → toStar T a = toStar T b := fun a b h =>
    congrArg (barToStar T (pCore_le_gnC hl.gn)) h
  have hπx₁ : π x₁ ∈ barO2 L := ⟨x₁, hx₁L, rfl⟩
  have hπx₂ : π x₂ ∈ barO2 L' := ⟨x₂, hx₂L, rfl⟩
  have hcu : Commute (π x₁) (π x₂) := hcomm' _ hπx₁ _ hπx₂
  have hn1 : π x₁ ∉ Subgroup.zpowers (π x₂) := by
    intro hmem
    have hmem' : π x₁ ∈ barO2 L' := (Subgroup.zpowers_le.2 hπx₂) hmem
    have hl₁' : π l₁ ∈ barO2 L := ⟨l₁, hl₁, rfl⟩
    have := hcomm' _ hl₁' _ hmem'
    apply hx₁nc
    exact htoStar _ _ (by rw [map_mul, map_mul]; exact this.symm)
  have hn2 : π x₂ ∉ Subgroup.zpowers (π x₁) := by
    intro hmem
    have hmem' : π x₂ ∈ barO2 L := (Subgroup.zpowers_le.2 hπx₁) hmem
    have hl₂' : π l₂ ∈ barO2 L' := ⟨l₂, hl₂, rfl⟩
    have := hcomm' _ hmem' _ hl₂'
    apply hx₂nc
    exact htoStar _ _ (by rw [map_mul, map_mul]; exact this)
  have hnc := exists_E9_of_ne_aux_nc hcu (a := a₁) (b := a₂)
    (by rw [← map_pow, hx₁a, map_one]) (by rw [← map_pow, hx₂a, map_one]) hn1 hn2
  set U : Subgroup X := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ with hU
  have hUmap : U.map π = Subgroup.zpowers (π x₁) ⊔ Subgroup.zpowers (π x₂) := by
    rw [hU, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  have hU2 : 2 ≤ CFSG.Open.pRank 3 U :=
    two_le_pRank_of_map π Nat.prime_three (by norm_num) U (by rw [hUmap]; exact hnc)
  obtain ⟨E, hEU, hEa, hEc⟩ := exists_elemAbelian_sq Nat.prime_three hU2
  have hUle : U ≤ J ⊓ Subgroup.normalizer (T₁ : Set X) := by
    refine sup_le (Subgroup.zpowers_le.2 ⟨Subgroup.le_normalClosure hx₁L, hx₁N⟩)
      (Subgroup.zpowers_le.2 ⟨hL'J hx₂L, hx₂N⟩)
  refine ⟨E, (hEU.trans hUle).trans inf_le_left, hEa, ?_, (hEU.trans hUle).trans inf_le_right⟩
  rw [hEc]
  norm_num

theorem exists_E9_of_ne {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hl : LiftCtx X T T₁ T₂ Ls L) (hne : L ≠ Subgroup.normalClosure (L : Set X))
    (hsh : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set X))) ∨
      (IsLThreeOfExp 1 ↥(barO2 L) ∧
        Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} ≤ 3)) :
    ∃ E : Subgroup X, E ≤ Subgroup.normalClosure (L : Set X) ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      E ≤ Subgroup.normalizer (T₁ : Set X) :=
  exists_E9_of_ne_gen hl.toGen hne hsh

end ExistsE9

section Exponent

theorem exponent_three_of_isAltSixCoverThree_aux_alt {k : ℕ} {σ : alternatingGroup (Fin 6)}
    (h : σ ^ (3 ^ k) = 1) : σ ^ 3 = 1 := by
  have hτ : ((σ : Equiv.Perm (Fin 6))) ^ (3 ^ k) = 1 := by
    have := congrArg Subtype.val h
    simpa using this
  have hall : ∀ n ∈ (σ : Equiv.Perm (Fin 6)).cycleType, n ∣ 3 := by
    intro n hn
    have h1 : n ∣ 3 ^ k :=
      (Equiv.Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one hτ)
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
    have h3 : 3 ^ i ≤ 6 := by
      have := Multiset.le_sum_of_mem hn
      rw [Equiv.Perm.sum_cycleType] at this
      exact this.trans (by simpa using Finset.card_le_univ (σ : Equiv.Perm (Fin 6)).support)
    rcases i with _ | _ | i
    · omega
    · simp
    · have : 3 ^ (i + 2) ≥ 9 := by
        calc 3 ^ (i + 2) = 3 ^ i * 9 := by ring
          _ ≥ 1 * 9 := Nat.mul_le_mul_right 9 (Nat.one_le_pow _ _ (by norm_num))
          _ = 9 := by norm_num
      omega
  have hlcm : orderOf (σ : Equiv.Perm (Fin 6)) ∣ 3 := by
    rw [← Equiv.Perm.lcm_cycleType]
    exact Multiset.lcm_dvd.2 hall
  apply Subtype.ext
  simpa using orderOf_dvd_iff_pow_eq_one.1 hlcm

theorem exponent_three_of_isAltSixCoverThree_aux_real {σ : alternatingGroup (Fin 6)} (h : σ ^ 3 = 1) :
    ∃ ρ : alternatingGroup (Fin 6), ρ * σ * ρ⁻¹ = σ⁻¹ := by
  set τ : Equiv.Perm (Fin 6) := (σ : Equiv.Perm (Fin 6)) with hτ
  have hτ3 : τ ^ 3 = 1 := by
    have := congrArg Subtype.val h
    simpa using this
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin 6), π * τ * π⁻¹ = τ⁻¹ :=
    isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 (Equiv.Perm.cycleType_inv τ).symm)
  by_cases hτ1 : τ = 1
  · refine ⟨1, ?_⟩
    have : σ = 1 := Subtype.ext hτ1
    simp [this]
  · have hall : ∀ n ∈ τ.cycleType, n = 3 := by
      intro n hn
      have h3 : n ∣ 3 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one hτ3)
      have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
      rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
      · omega
      · exact h
    have hrep : τ.cycleType = Multiset.replicate (Multiset.card τ.cycleType) 3 :=
      Multiset.eq_replicate_card.2 hall
    have hnotle : ¬ Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin 6))) ≤
        alternatingGroup (Fin 6) := by
      intro hc
      have h1 := Equiv.Perm.card_le_of_centralizer_le_alternating hc
      have h2 := Equiv.Perm.count_le_one_of_centralizer_le_alternating hc 3
      rw [hrep, Multiset.sum_replicate, Multiset.count_replicate_self, smul_eq_mul] at *
      simp only [Fintype.card_fin] at h1
      omega
    obtain ⟨τ', hτ'c, hτ'sign⟩ : ∃ τ' ∈ Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin 6))),
        τ' ∉ alternatingGroup (Fin 6) := by
      by_contra hcon
      push Not at hcon
      exact hnotle (fun x hx => hcon x hx)
    have hs' : Equiv.Perm.sign τ' = -1 := by
      have hne : ¬ Equiv.Perm.sign τ' = 1 := fun h1 => hτ'sign (Equiv.Perm.mem_alternatingGroup.2 h1)
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ') with h1 | h1
      · exact absurd h1 hne
      · exact h1
    have hcomm : τ' * τ = τ * τ' := Subgroup.mem_centralizer_singleton_iff.1 hτ'c
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs
    · exact ⟨⟨π, Equiv.Perm.mem_alternatingGroup.2 hs⟩, Subtype.ext (by simpa using hπ)⟩
    · refine ⟨⟨π * τ', ?_⟩, Subtype.ext ?_⟩
      · rw [Equiv.Perm.mem_alternatingGroup, map_mul, hs, hs']
        decide
      · have e1 : π * τ' * τ * (π * τ')⁻¹ = π * τ * π⁻¹ := by
          rw [mul_inv_rev, mul_assoc π τ' τ, hcomm]
          group
        simpa [mul_assoc] using (e1.trans hπ)

theorem exponent_three_of_isAltSixCoverThree {S : Type} [Group S] (h : IsAltSixCoverThree S) {g : S}
    {k : ℕ} (hg : g ^ (3 ^ k) = 1) : g ^ 3 = 1 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  have hgz : ∀ z ∈ Subgroup.center S, z ^ 3 = 1 := by
    intro z hz
    have := pow_card_eq_one' (G := ↥(Subgroup.center S)) (x := ⟨z, hz⟩)
    rw [hZ] at this
    exact congrArg Subtype.val this
  set gb : alternatingGroup (Fin 6) := e (QuotientGroup.mk g) with hgb
  have hgb3 : gb ^ 3 = 1 := by
    refine exponent_three_of_isAltSixCoverThree_aux_alt (k := k) ?_
    rw [hgb, ← map_pow, ← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one, map_one]
  have hc3 : g ^ 3 ∈ Subgroup.center S := by
    have h1 : e (QuotientGroup.mk (g ^ 3)) = 1 := by
      rw [QuotientGroup.mk_pow, map_pow]
      exact hgb3
    have h2 : (QuotientGroup.mk (g ^ 3) : S ⧸ Subgroup.center S) = 1 := by
      simpa using (e.map_eq_one_iff).1 h1
    exact (QuotientGroup.eq_one_iff _).1 h2
  obtain ⟨ρ, hρ⟩ := exponent_three_of_isAltSixCoverThree_aux_real hgb3
  obtain ⟨q, hq⟩ := e.surjective ρ
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
  have hsg : (QuotientGroup.mk (s * g * s⁻¹) : S ⧸ Subgroup.center S) = QuotientGroup.mk g⁻¹ := by
    apply e.injective
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv,
      QuotientGroup.mk_inv, map_inv, hq, ← hgb]
    exact hρ
  have hz0 : (s * g * s⁻¹)⁻¹ * g⁻¹ ∈ Subgroup.center S := QuotientGroup.eq.1 hsg
  have hz : g * (s * g * s⁻¹) ∈ Subgroup.center S := by
    have := Subgroup.inv_mem _ hz0
    convert this using 1
    group
  have hcomm : Commute g⁻¹ (g * (s * g * s⁻¹)) := by
    have := Subgroup.mem_center_iff.1 hz g⁻¹
    exact this
  have hsg' : s * g * s⁻¹ = g⁻¹ * (g * (s * g * s⁻¹)) := by group
  have h1 : (s * g * s⁻¹) ^ 3 = g ^ 3 := by
    rw [conj_pow]
    have := Subgroup.mem_center_iff.1 hc3 s
    calc s * g ^ 3 * s⁻¹ = g ^ 3 * s * s⁻¹ := by rw [this]
      _ = g ^ 3 := by group
  have h2 : (s * g * s⁻¹) ^ 3 = (g ^ 3)⁻¹ := by
    rw [hsg', hcomm.mul_pow, hgz _ hz, mul_one, inv_pow]
  have hinv : g ^ 3 = (g ^ 3)⁻¹ := h1.symm.trans h2
  have h6 : g ^ 3 * g ^ 3 = 1 := by
    nth_rewrite 1 [hinv]
    exact inv_mul_cancel _
  have hcc : (g ^ 3) ^ 3 = 1 := hgz _ hc3
  have hcube : (g ^ 3) ^ 3 = g ^ 3 := by
    calc (g ^ 3) ^ 3 = (g ^ 3 * g ^ 3) * g ^ 3 := by group
      _ = g ^ 3 := by rw [h6, one_mul]
  exact hcube.symm.trans hcc

end Exponent

section CentralProd

variable {X : Type} [Group X] [Finite X]

theorem isCentralProdA6Z3_gnImg_aux_inj_gen {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L) {A B : Subgroup (X ⧸ CFSG.pCore 2 X)}
    (hA : IsAltSixCoverThree ↥A) (hcAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hsup : A ⊔ B = barO2 (Subgroup.normalClosure (L : Set X)))
    (hAc : KFactsPair.centerIn A = A ⊓ B) (hBc : KFactsPair.centerIn B = A ⊓ B)
    (hLA : barO2 L = A)
    (hQ : CFSG.Open.pRank 3 (Subgroup.normalizer (T₁ : Set X) ⊓ L) ≤ 1) :
    ∀ n ∈ barO2 (Subgroup.normalClosure (L : Set X)),
      barToStar T (pCore_le_gnC hl.gn) n = 1 → n = 1 := by
  intro n hnJ hn1
  set π : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  set φb := barToStar T (pCore_le_gnC hl.gn) with hφb
  have hφπ : ∀ x : X, φb (π x) = toStar T x := fun x => rfl
  obtain ⟨⟨s₀, hs₀⟩, hs₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (liftOf_unique_aux2 hl.comp.1)
  obtain ⟨l₀', hl₀', hl₀'s⟩ : ∃ l ∈ L, toStar T l ≠ 1 := by
    have hs₀' : s₀ ∈ L.map (toStar T) := by rw [hl.lift.2]; exact hs₀
    obtain ⟨l, hl, hls⟩ := hs₀'
    exact ⟨l, hl, fun h => hs₀1 (Subtype.ext (hls.symm.trans h))⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) n
  have hconj : ∀ x : X, ∀ l ∈ L, π y * π (x * l * x⁻¹) = π (x * l * x⁻¹) * π y := by
    intro x l hlL
    have hK₀ : CFSG.Open.IsComponentOf (barO2 (L.map (MulAut.conj x).toMonoidHom)) ⊤ :=
      (liftOf_conj_aux4 hl.lift.1 x).component
    rcases kComp_holds.2 (X ⧸ CFSG.pCore 2 X) _ φb.ker φb.normal_ker hK₀ with hle | hcomm
    · exfalso
      have hmem : π (x * l₀' * x⁻¹) ∈ barO2 (L.map (MulAut.conj x).toMonoidHom) :=
        ⟨x * l₀' * x⁻¹, ⟨l₀', hl₀', rfl⟩, rfl⟩
      have h1 : φb (π (x * l₀' * x⁻¹)) = 1 := MonoidHom.mem_ker.1 (hle hmem)
      rw [hφπ, map_mul, map_mul, map_inv] at h1
      apply hl₀'s
      calc toStar T l₀' = (toStar T x)⁻¹ * (toStar T x * toStar T l₀' * (toStar T x)⁻¹) *
            toStar T x := by group
        _ = 1 := by rw [h1]; group
    · have hmem : π (x * l * x⁻¹) ∈ barO2 (L.map (MulAut.conj x).toMonoidHom) :=
        ⟨x * l * x⁻¹, ⟨l, hlL, rfl⟩, rfl⟩
      have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hmem
      exact Subgroup.mem_centralizer_iff.1 h1 (π y) hn1
  have hcentJ := exists_centralizing_pGroup_aux_normalClosure hconj
  have hcomm_nJ : ∀ j ∈ barO2 (Subgroup.normalClosure (L : Set X)), π y * j = j * π y := by
    rintro _ ⟨j, hj, rfl⟩
    have h1 : π (y * j * y⁻¹ * j⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 (hcentJ j hj)
    simp only [map_mul, map_inv] at h1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have hAJ : A ≤ barO2 (Subgroup.normalClosure (L : Set X)) := hsup ▸ le_sup_left
  have hBJ : B ≤ barO2 (Subgroup.normalClosure (L : Set X)) := hsup ▸ le_sup_right
  have hnAB : π y ∈ A ⊔ B := hsup ▸ hnJ
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hcAB).2
  have hnmul : π y ∈ ((A : Set (X ⧸ CFSG.pCore 2 X)) * (B : Set (X ⧸ CFSG.pCore 2 X))) := by
    rw [← hset]
    exact hnAB
  obtain ⟨a, ha, b, hb, hab⟩ := hnmul
  have ha1 : a ∈ KFactsPair.centerIn A := by
    refine (mem_centerIn_iff_s15 A a).2 ⟨ha, fun a' ha' => ?_⟩
    have h1 := hcomm_nJ a' (hAJ ha')
    rw [← hab] at h1
    have h2 : a' * b = b * a' := hcAB a' ha' b hb
    have h3 : a' * a * b = a * a' * b := by
      calc a' * a * b = a' * (a * b) := by rw [mul_assoc]
        _ = a * b * a' := h1.symm
        _ = a * (b * a') := by rw [mul_assoc]
        _ = a * (a' * b) := by rw [h2]
        _ = a * a' * b := by rw [mul_assoc]
    exact mul_right_cancel h3
  have hb1 : b ∈ KFactsPair.centerIn B := by
    refine (mem_centerIn_iff_s15 B b).2 ⟨hb, fun b' hb' => ?_⟩
    have h1 := hcomm_nJ b' (hBJ hb')
    rw [← hab] at h1
    have h2 : a * b' = b' * a := hcAB a ha b' hb'
    have h3 : a * (b' * b) = a * (b * b') := by
      calc a * (b' * b) = a * b' * b := by rw [mul_assoc]
        _ = b' * a * b := by rw [h2]
        _ = b' * (a * b) := by rw [mul_assoc]
        _ = a * b * b' := h1.symm
        _ = a * (b * b') := by rw [mul_assoc]
    exact mul_left_cancel h3
  rw [hAc] at ha1
  rw [hBc] at hb1
  have hnZ : π y ∈ A ⊓ B := by
    rw [← hab]
    exact ⟨A.mul_mem ha hb1.1, B.mul_mem ha1.2 hb⟩
  by_contra hne1
  have hcardZ : Nat.card ↥(A ⊓ B) = 3 := by
    calc Nat.card ↥(A ⊓ B) = Nat.card ↥(KFactsPair.centerIn A) := by rw [hAc]
      _ = Nat.card (Subgroup.center ↥A) := card_centerIn_s15 A
      _ = 3 := hA.2.1
  have hn3 : (π y) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(A ⊓ B)) (x := ⟨π y, hnZ⟩)
    rw [hcardZ] at this
    exact congrArg Subtype.val this
  obtain ⟨l₀, hl₀, hl₀y⟩ : π y ∈ barO2 L := by rw [hLA]; exact hnZ.1
  have hl₀C : l₀ ∈ gnC T := by
    have h1 : toStar T l₀ = 1 := by
      have : φb (π l₀) = 1 := by rw [hl₀y]; exact hn1
      exact this
    exact (QuotientGroup.eq_one_iff l₀).1 h1
  obtain ⟨z', hz'mem, ⟨a₂, hz'a⟩, hz'y⟩ :=
    exists_E9_of_ne_aux_ppart π (x₀ := l₀) hl₀y (k := 1) (by simpa using hn3) (orderOf_pos l₀)
  have hz'LC : z' ∈ L ⊓ gnC T := by
    have hle : Subgroup.zpowers l₀ ≤ L ⊓ gnC T := Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hl₀, hl₀C⟩)
    exact hle hz'mem
  obtain ⟨x₁, hx₁, ⟨a₁, hx₁a⟩, l₁, hl₁, hnc⟩ := exists_E9_of_ne_aux_good3 hl.good hl.comp hl.lift
  have hx₁L : x₁ ∈ L := (Subgroup.mem_inf.1 hx₁).2
  have hu_A : π x₁ ∈ A := by rw [← hLA]; exact ⟨x₁, hx₁L, rfl⟩
  have hπl₁ : π l₁ ∈ A := by rw [← hLA]; exact ⟨l₁, hl₁, rfl⟩
  have hnZA : π y ∈ KFactsPair.centerIn A := by rw [hAc]; exact hnZ
  have hcu : Commute (π x₁) (π y) := ((mem_centerIn_iff_s15 A _).1 hnZA).2 _ hu_A
  have hu3 : (π x₁) ^ 3 = 1 := by
    have := exponent_three_of_isAltSixCoverThree hA (g := (⟨π x₁, hu_A⟩ : ↥A)) (k := a₁)
      (Subtype.ext (by simp [← map_pow, hx₁a]))
    exact congrArg Subtype.val this
  have hφx₁ : ∀ z : X, π z = 1 → toStar T z = 1 := fun z hz => by
    have : φb (π z) = 1 := by rw [hz]; exact map_one _
    exact this
  have hu1 : π x₁ ≠ 1 := by
    intro h
    apply hnc
    have := hφx₁ x₁ h
    rw [map_mul, map_mul, this, one_mul, mul_one]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hordu : orderOf (π x₁) = 3 := orderOf_eq_prime hu3 hu1
  have hordv : orderOf (π y) = 3 := orderOf_eq_prime hn3 hne1
  have h1 : π x₁ ∉ Subgroup.zpowers (π y) := by
    intro hmem
    have hzle : Subgroup.zpowers (π y) ≤ KFactsPair.centerIn A := Subgroup.zpowers_le.2 hnZA
    have hc := ((mem_centerIn_iff_s15 A _).1 (hzle hmem)).2 (π l₁) hπl₁
    apply hnc
    have := congrArg φb hc
    rw [← map_mul, ← map_mul] at this
    exact this.symm
  have h2 : π y ∉ Subgroup.zpowers (π x₁) := by
    intro hmem
    have hle : Subgroup.zpowers (π y) ≤ Subgroup.zpowers (π x₁) := Subgroup.zpowers_le.2 hmem
    have heq : Subgroup.zpowers (π y) = Subgroup.zpowers (π x₁) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hordu, hordv])
    exact h1 (heq ▸ Subgroup.mem_zpowers _)
  have hnc2 := exists_E9_of_ne_aux_nc hcu (a := a₁) (b := 1)
    (by rw [← map_pow, hx₁a, map_one]) (by simpa using hn3) h1 h2
  set U : Subgroup X := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers z' with hU
  have hUmap : U.map π = Subgroup.zpowers (π x₁) ⊔ Subgroup.zpowers (π y) := by
    rw [hU, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hz'y]
  have hU2 : 2 ≤ CFSG.Open.pRank 3 U :=
    two_le_pRank_of_map π Nat.prime_three (by norm_num) U (by rw [hUmap]; exact hnc2)
  have hUle : U ≤ Subgroup.normalizer (T₁ : Set X) ⊓ L := by
    refine sup_le (Subgroup.zpowers_le.2 hx₁) (Subgroup.zpowers_le.2 ⟨?_, hz'LC.1⟩)
    exact gnC_le_normalizer_one hl.good hz'LC.2
  have := CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hUle
  omega

theorem isCentralProdA6Z3_gnImg_aux_inj {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L) {A B : Subgroup (X ⧸ CFSG.pCore 2 X)}
    (hA : IsAltSixCoverThree ↥A) (hcAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hsup : A ⊔ B = barO2 (Subgroup.normalClosure (L : Set X)))
    (hAc : KFactsPair.centerIn A = A ⊓ B) (hBc : KFactsPair.centerIn B = A ⊓ B)
    (hLA : barO2 L = A)
    (hQ : CFSG.Open.pRank 3 (Subgroup.normalizer (T₁ : Set X) ⊓ L) ≤ 1) :
    ∀ n ∈ barO2 (Subgroup.normalClosure (L : Set X)),
      barToStar T (pCore_le_gnC hl.gn) n = 1 → n = 1 :=
  isCentralProdA6Z3_gnImg_aux_inj_gen hl.toGen hA hcAB hsup hAc hBc hLA hQ

theorem isCentralProdA6Z3_gnImg_aux_cp_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : IsCentralProdA6Z3 S) : IsCentralProdA6Z3 S' := by
  obtain ⟨K₁, K₂, h1, h2, hsup, hcomm, hin1, hin2⟩ := h
  rw [← centerIn_eq_cfsg] at hin1 hin2
  have hf : Function.Injective e.toMonoidHom := e.injective
  refine ⟨K₁.map e.toMonoidHom, K₂.map e.toMonoidHom,
    isAltSixCoverThree_of_mulEquiv (K₁.equivMapOfInjective e.toMonoidHom hf).symm h1,
    isAltSixCoverThree_of_mulEquiv (K₂.equivMapOfInjective e.toMonoidHom hf).symm h2, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ e.surjective]
  · rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 (hcomm ha) b hb
    show e b * e a = e a * e b
    rw [← map_mul, ← map_mul, this]
  · rw [← centerIn_eq_cfsg, exists_centralizing_pGroup_aux_centerIn_map e.toMonoidHom hf, ← hin1,
      Subgroup.map_inf_eq _ _ _ hf]
  · rw [← centerIn_eq_cfsg, exists_centralizing_pGroup_aux_centerIn_map e.toMonoidHom hf, ← hin2,
      Subgroup.map_inf_eq _ _ _ hf]

theorem isCentralProdA6Z3_gnImg_aux_core_gen {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L)
    (hcp : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set X))))
    (hQ : CFSG.Open.pRank 3 (Subgroup.normalizer (T₁ : Set X) ⊓ L) ≤ 1) :
    IsCentralProdA6Z3 ↥(gnImg T (Subgroup.normalClosure (L : Set X))) := by
  set J : Subgroup X := Subgroup.normalClosure (L : Set X) with hJ
  obtain ⟨A, B, hA, hB, hsup, hcAB, hAc, hBc, hAcomp, hBcomp⟩ :=
    exists_centralizing_pGroup_aux_centralProd (Subgroup.normalClosure_normal (s := (L : Set X))) hcp
  have hLJ : barO2 L ≤ A ⊔ B := by
    rw [hsup]
    exact Subgroup.map_mono Subgroup.le_normalClosure
  have hinj : ∀ n ∈ barO2 J, barToStar T (pCore_le_gnC hl.gn) n = 1 → n = 1 := by
    rcases exists_centralizing_pGroup_aux_comp_eq hl.lift.1.component hAcomp hBcomp hLJ with
      hLA | hLB
    · exact isCentralProdA6Z3_gnImg_aux_inj_gen hl hA hcAB hsup hAc hBc hLA hQ
    · refine isCentralProdA6Z3_gnImg_aux_inj_gen hl hB
        (fun b hb a ha => (hcAB a ha b hb).symm)
        (by rw [sup_comm]; exact hsup) (by rw [inf_comm]; exact hBc) (by rw [inf_comm]; exact hAc)
        hLB hQ
  have hmem : ∀ k : ↥(barO2 J), barToStar T (pCore_le_gnC hl.gn) (k : X ⧸ CFSG.pCore 2 X) ∈
      gnImg T J := by
    intro k
    obtain ⟨j, hj, hjk⟩ := k.2
    rw [← hjk]
    exact ⟨j, hj, rfl⟩
  let f : ↥(barO2 J) →* ↥(gnImg T J) :=
    ((barToStar T (pCore_le_gnC hl.gn)).comp (barO2 J).subtype).codRestrict (gnImg T J) hmem
  have hfinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).2 (fun k hk => ?_)
    have h1 : barToStar T (pCore_le_gnC hl.gn) (k : X ⧸ CFSG.pCore 2 X) = 1 :=
      congrArg Subtype.val hk
    exact Subtype.ext (hinj k k.2 h1)
  have hfsurj : Function.Surjective f := by
    rintro ⟨s, j, hj, rfl⟩
    exact ⟨⟨QuotientGroup.mk' (CFSG.pCore 2 X) j, j, hj, rfl⟩, rfl⟩
  exact isCentralProdA6Z3_gnImg_aux_cp_of_mulEquiv (MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩) hcp

theorem isCentralProdA6Z3_gnImg_aux_core {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L)
    (hcp : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set X))))
    (hQ : CFSG.Open.pRank 3 (Subgroup.normalizer (T₁ : Set X) ⊓ L) ≤ 1) :
    IsCentralProdA6Z3 ↥(gnImg T (Subgroup.normalClosure (L : Set X))) :=
  isCentralProdA6Z3_gnImg_aux_core_gen hl.toGen hcp hQ

theorem isCentralProdA6Z3_gnImg_of_Q_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (hR : LiftRankBound G M T T₁ T₂)
    (hgn : GNSetting ↥M (T.subgroupOf M)) (hg : GNGood (T.subgroupOf M) T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hcp : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set ↥M))))
    (hQ : CFSG.Open.pRank 3 (Subgroup.normalizer (T₁ : Set ↥M) ⊓ L) ≤ 1) :
    IsCentralProdA6Z3 ↥(gnImg (T.subgroupOf M) (Subgroup.normalClosure (L : Set ↥M))) :=
  isCentralProdA6Z3_gnImg_aux_core_gen (hR.liftCtxGen hgn hg hLs hL) hcp hQ

theorem isCentralProdA6Z3_gnImg_of_Q {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hcp : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set ↥M))))
    (hQ : CFSG.Open.pRank 3 (Subgroup.normalizer (T₁ : Set ↥M) ⊓ L) ≤ 1) :
    IsCentralProdA6Z3 ↥(gnImg (T.subgroupOf M) (Subgroup.normalClosure (L : Set ↥M))) :=
  isCentralProdA6Z3_gnImg_of_Q_gen (liftRankBound_of_ctx2 ctx) ctx.gn ctx.good hLs hL hcp hQ

end CentralProd

end CFSG.LocalAnalysis.RankThreeUC.S15
