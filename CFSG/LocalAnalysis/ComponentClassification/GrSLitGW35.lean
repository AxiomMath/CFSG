module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWCore
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open scoped Pointwise

section Defs

variable (X : Type*) [Group X]

@[expose] def oTwoPrimeTwo : Subgroup X :=
  (pCore 2 (X ⧸ pPrimeCore 2 X)).comap (QuotientGroup.mk' (pPrimeCore 2 X))

@[expose] def lTwoPrimeTwo : Subgroup X := pLayer X 2 ⊔ oTwoPrimeTwo X

variable {X}

@[expose] def lStar (T : Subgroup X) : Subgroup X :=
  pLayer X 2 ⊔ pPrimeCore 2 X ⊔ (pPrimeCore 2 (centralizer (T : Set X))).map
    (centralizer (T : Set X)).subtype

end Defs

variable {X : Type} [Group X] [Finite X]

instance oTwoPrimeTwo_normal : (oTwoPrimeTwo X).Normal := by
  unfold oTwoPrimeTwo
  infer_instance

theorem pLayer_two_normal' : (pLayer X 2).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CatalogueBPrimeJoin.pLayer_characteristic (G := X) (p := 2)
  infer_instance

instance lTwoPrimeTwo_normal : (lTwoPrimeTwo X).Normal := by
  have := pLayer_two_normal' (X := X)
  unfold lTwoPrimeTwo
  infer_instance

omit [Finite X] in
theorem pPrimeCore_le_oTwoPrimeTwo : pPrimeCore 2 X ≤ oTwoPrimeTwo X := by
  intro x hx
  change QuotientGroup.mk' (pPrimeCore 2 X) x ∈ pCore 2 (X ⧸ pPrimeCore 2 X)
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
  exact one_mem _

theorem map_lTwoPrimeTwo :
    (lTwoPrimeTwo X).map (QuotientGroup.mk' (pPrimeCore 2 X)) =
      generalizedFitting (X ⧸ pPrimeCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [lTwoPrimeTwo, Subgroup.map_sup, LBalance.Quot.map_pLayer_eq_layer_quotient, oTwoPrimeTwo,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _), generalizedFitting,
    Fitting_eq_pcore (X ⧸ pPrimeCore 2 X) 2 (pPrimeCore_quotient_pPrimeCore_eq_bot 2), sup_comm]

theorem not_two_dvd_card_ker_mk : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 X)).ker := by
  rw [QuotientGroup.ker_mk']
  intro h
  exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
    (even_iff_two_dvd.mpr h)

theorem odd_orderOf_of_map_odd {x : X} (h : Odd (orderOf (QuotientGroup.mk' (pPrimeCore 2 X) x))) :
    Odd (orderOf x) := by
  set m := orderOf (QuotientGroup.mk' (pPrimeCore 2 X) x)
  have h1 : x ^ m ∈ pPrimeCore 2 X := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact pow_orderOf_eq_one _
  have h2 : Odd (orderOf (x ^ m)) := by
    have hdvd : orderOf (x ^ m) ∣ Nat.card (pPrimeCore 2 X) := by
      rw [← Subgroup.orderOf_mk (x ^ m) h1]
      exact orderOf_dvd_natCard _
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card.coprime_dvd_right hdvd)
  have h3 : x ^ (m * orderOf (x ^ m)) = 1 := by rw [pow_mul, pow_orderOf_eq_one]
  exact (h.mul h2).of_dvd_nat (orderOf_dvd_of_pow_eq_one h3)

theorem odd_card_of_forall_odd_orderOf {U : Subgroup X} (h : ∀ u ∈ U, Odd (orderOf u)) :
    Odd (Nat.card U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hne
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 hne
  have := h g g.2
  rw [Subgroup.orderOf_coe, hg] at this
  exact (Nat.not_odd_iff_even.mpr even_two) this

theorem mem_oddCore_centralizer_of_odd (T : Sylow 2 (lTwoPrimeTwo X)) {c : X}
    (hc : c ∈ centralizer (((T : Subgroup _).map (lTwoPrimeTwo X).subtype : Subgroup X) : Set X))
    (hodd : Odd (orderOf c)) :
    c ∈ (pPrimeCore 2 (centralizer (((T : Subgroup _).map (lTwoPrimeTwo X).subtype :
      Subgroup X) : Set X))).map (centralizer (((T : Subgroup _).map (lTwoPrimeTwo X).subtype :
        Subgroup X) : Set X)).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  set T' : Subgroup X := (T : Subgroup (lTwoPrimeTwo X)).map (lTwoPrimeTwo X).subtype with hT'
  set C : Subgroup X := centralizer (T' : Set X) with hC
  have hT'2 : IsPGroup 2 T' := T.isPGroup'.map (lTwoPrimeTwo X).subtype
  set Yb : Subgroup (X ⧸ pPrimeCore 2 X) := (lTwoPrimeTwo X).map π with hYb
  let S : Sylow 2 Yb := T.mapSurjective (MonoidHom.subgroupMap_surjective π (lTwoPrimeTwo X))
  have hS : (S : Subgroup Yb).map Yb.subtype = T'.map π := by
    change ((T : Subgroup (lTwoPrimeTwo X)).map (π.subgroupMap (lTwoPrimeTwo X))).map Yb.subtype = _
    rw [Subgroup.map_map, hT', Subgroup.map_map]
    rfl
  set Cb : Subgroup (X ⧸ pPrimeCore 2 X) := centralizer ((T'.map π : Subgroup _) : Set _) with hCb
  have hCmap : C.map π = Cb := map_centralizer_eq_of_odd_ker π (QuotientGroup.mk'_surjective _)
    not_two_dvd_card_ker_mk hT'2
  set Ob : Subgroup (X ⧸ pPrimeCore 2 X) := (pPrimeCore 2 Cb).map Cb.subtype with hOb
  set U : Subgroup X := C ⊓ Ob.comap π with hU
  have hUodd : Odd (Nat.card U) := by
    refine odd_card_of_forall_odd_orderOf fun u hu => odd_orderOf_of_map_odd ?_
    exact odd_orderOf_of_mem_map_pPrimeCore (Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hu).2)
  have hUnorm : ∀ h ∈ C, ∀ u ∈ U, h * u * h⁻¹ ∈ U := by
    intro h hh u hu
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hh hu1) (inv_mem hh), ?_⟩
    have hhb : π h ∈ Cb := hCmap ▸ Subgroup.mem_map_of_mem π hh
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_comap.mp hu2
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv, ← hvu]
    have hn : (pPrimeCore 2 Cb).Normal := inferInstance
    exact ⟨⟨π h, hhb⟩ * v * ⟨π h, hhb⟩⁻¹, hn.conj_mem v hv ⟨π h, hhb⟩, rfl⟩
  have hUO : U ≤ (pPrimeCore 2 C).map C.subtype := le_map_pPrimeCore inf_le_left hUnorm hUodd
  refine hUO (Subgroup.mem_inf.mpr ⟨hc, Subgroup.mem_comap.mpr ?_⟩)
  have hcb : π c ∈ centralizer (((S : Subgroup Yb).map Yb.subtype : Subgroup _) : Set _) := by
    rw [hS, ← hCb, ← hCmap]
    exact Subgroup.mem_map_of_mem π hc
  have hcodd : Odd (orderOf (π c)) := hodd.of_dvd_nat (orderOf_map_dvd π c)
  have key := mem_oddCore_centralizer_of_corefree (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
    map_lTwoPrimeTwo S hcb hcodd
  rw [hS] at key
  exact key

theorem mem_pLayer_sup_of_mem_lTwoPrimeTwo {x : X} (hx : x ∈ lTwoPrimeTwo X)
    (hodd : Odd (orderOf x)) : x ∈ pLayer X 2 ⊔ pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := pLayer_two_normal' (X := X)
  set N₀ := pLayer X 2 ⊔ pPrimeCore 2 X with hN₀
  obtain ⟨l, hl, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  set ρ := QuotientGroup.mk' N₀ with hρ
  have hρl : ρ l = 1 := (QuotientGroup.eq_one_iff l).mpr (Subgroup.mem_sup_left hl)
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := X ⧸ pPrimeCore 2 X))
    ⟨QuotientGroup.mk' (pPrimeCore 2 X) o, ho⟩
  have hok : o ^ 2 ^ k ∈ N₀ := by
    have h1 : QuotientGroup.mk' (pPrimeCore 2 X) (o ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    exact Subgroup.mem_sup_right ((QuotientGroup.eq_one_iff _).mp h1)
  have h2 : ρ (l * o) ^ 2 ^ k = 1 := by
    rw [map_mul, hρl, one_mul, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hok
  have h3 : orderOf (ρ (l * o)) = 1 := Nat.Coprime.eq_one_of_dvd
    ((Nat.coprime_two_right.mpr (hodd.of_dvd_nat (orderOf_map_dvd ρ _))).pow_right k)
    (orderOf_dvd_of_pow_eq_one h2)
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff _).mp h3

theorem lTwoPrimeTwo_le_sup (T : Sylow 2 (lTwoPrimeTwo X)) :
    lTwoPrimeTwo X ≤
      pLayer X 2 ⊔ pPrimeCore 2 X ⊔ (T : Subgroup _).map (lTwoPrimeTwo X).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := pLayer_two_normal' (X := X)
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  set T' : Subgroup X := (T : Subgroup (lTwoPrimeTwo X)).map (lTwoPrimeTwo X).subtype with hT'
  intro x hx
  obtain ⟨l, hl, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  set Yb : Subgroup (X ⧸ pPrimeCore 2 X) := (lTwoPrimeTwo X).map π with hYb
  let S : Sylow 2 Yb := T.mapSurjective (MonoidHom.subgroupMap_surjective π (lTwoPrimeTwo X))
  have hS : (S : Subgroup Yb).map Yb.subtype = T'.map π := by
    change ((T : Subgroup (lTwoPrimeTwo X)).map (π.subgroupMap (lTwoPrimeTwo X))).map Yb.subtype = _
    rw [Subgroup.map_map, hT', Subgroup.map_map]
    rfl
  have hPY : pCore 2 (X ⧸ pPrimeCore 2 X) ≤ Yb := by
    rw [hYb, lTwoPrimeTwo, Subgroup.map_sup, oTwoPrimeTwo,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    exact le_sup_right
  have hPS : pCore 2 (X ⧸ pPrimeCore 2 X) ≤ T'.map π := by
    have hn : ((pCore 2 (X ⧸ pPrimeCore 2 X)).subgroupOf Yb).Normal :=
      Subgroup.Normal.subgroupOf inferInstance Yb
    have hp : IsPGroup 2 ((pCore 2 (X ⧸ pPrimeCore 2 X)).subgroupOf Yb) :=
      (pCore_isPGroup (p := 2) (G := X ⧸ pPrimeCore 2 X)).comap_of_injective Yb.subtype
        Yb.subtype_injective
    have hle := hp.le_sylow_of_normal S
    rw [← hS]
    intro y hy
    exact ⟨⟨y, hPY hy⟩, hle hy, rfl⟩
  obtain ⟨t, ht, hto⟩ := hPS ho
  have hot : t⁻¹ * o ∈ pPrimeCore 2 X := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv]
    change (π t)⁻¹ * π o = 1
    rw [hto, inv_mul_cancel]
  have h1 : l ∈ pLayer X 2 ⊔ pPrimeCore 2 X ⊔ T' :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left hl)
  have h2 : t ∈ pLayer X 2 ⊔ pPrimeCore 2 X ⊔ T' := Subgroup.mem_sup_right ht
  have h3 : t⁻¹ * o ∈ pLayer X 2 ⊔ pPrimeCore 2 X ⊔ T' :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right hot)
  have h' := mul_mem (mul_mem h1 h2) h3
  rwa [show l * t * (t⁻¹ * o) = l * o by group] at h'

omit [Finite X] in
theorem conj_mem_centralizer_of_mem_normalizer' {B : Subgroup X} {g : X}
    (hg : g ∈ normalizer (B : Set X)) {c : X} (hc : c ∈ centralizer (B : Set X)) :
    g * c * g⁻¹ ∈ centralizer (B : Set X) := by
  rw [mem_centralizer_iff]
  intro h hh
  have hh1 : g⁻¹ * h * g ∈ B := by
    have := (mem_normalizer_iff.mp (inv_mem hg) h).mp hh
    simpa using this
  have hcomm : (g⁻¹ * h * g) * c = c * (g⁻¹ * h * g) := mem_centralizer_iff.mp hc _ hh1
  calc h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * c * g⁻¹) * h := by group

theorem conj_mem_oddCore_centralizer {B : Subgroup X} {g : X}
    (hg : g ∈ normalizer (B : Set X)) {d : X}
    (hd : d ∈ (pPrimeCore 2 (centralizer (B : Set X))).map (centralizer (B : Set X)).subtype) :
    g * d * g⁻¹ ∈
      (pPrimeCore 2 (centralizer (B : Set X))).map (centralizer (B : Set X)).subtype := by
  set C := centralizer (B : Set X) with hC
  set D := (pPrimeCore 2 C).map C.subtype with hD
  have hgC : ∀ c ∈ C, g * c * g⁻¹ ∈ C := fun c hc =>
    conj_mem_centralizer_of_mem_normalizer' hg hc
  have hgC' : ∀ c ∈ C, g⁻¹ * c * g ∈ C := fun c hc => by
    have := conj_mem_centralizer_of_mem_normalizer' (inv_mem hg) hc
    simpa using this
  have key : D.map (MulAut.conj g).toMonoidHom ≤ D := by
    apply le_map_pPrimeCore
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨v', -, rfl⟩ := hv
      exact hgC _ v'.2
    · rintro c hc _ ⟨v, hv, rfl⟩
      have hc' := hgC' c hc
      obtain ⟨v', hv', rfl⟩ := hv
      have hn : (pPrimeCore 2 C).Normal := inferInstance
      refine ⟨_, ⟨⟨g⁻¹ * c * g, hc'⟩ * v' * ⟨g⁻¹ * c * g, hc'⟩⁻¹,
        hn.conj_mem v' hv' _, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype,
        Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact odd_card_map_pPrimeCore C
  exact key ⟨d, hd, rfl⟩

omit [Finite X] in
theorem mem_normalizer_sup_of_mem {H K : Subgroup X} {g : X} (hH : g ∈ normalizer (H : Set X))
    (hK : g ∈ normalizer (K : Set X)) : g ∈ normalizer ((H ⊔ K : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

omit [Finite X] in
theorem exists_mul_of_mem_sup_of_le_normalizer {H K : Subgroup X}
    (hK : K ≤ normalizer (H : Set X)) {y : X} (hy : y ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = y := by
  set N := normalizer (H : Set X) with hN
  have hHN : H ≤ N := le_normalizer
  have hn : (H.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hyN : y ∈ N := sup_le hHN hK hy
  have hmem : (⟨y, hyN⟩ : N) ∈ H.subgroupOf N ⊔ K.subgroupOf N := by
    have h1 : (H.subgroupOf N ⊔ K.subgroupOf N).map N.subtype = H ⊔ K := by
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hHN, map_subgroupOf_eq_of_le hK]
    rw [← h1] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = ⟨y, hyN⟩ := Subtype.ext hzy
    rwa [← this]
  obtain ⟨h, hh, k, hk, hhk⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  exact ⟨h, hh, k, hk, congrArg Subtype.val hhk⟩

omit [Finite X] in
theorem mem_normalizer_of_conj_mem {B : Subgroup X} {t : X} (h1 : ∀ y ∈ B, t * y * t⁻¹ ∈ B)
    (h2 : ∀ y ∈ B, t⁻¹ * y * t ∈ B) : t ∈ normalizer (B : Set X) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h1 y, fun hy => ?_⟩
  have := h2 _ hy
  rwa [show t⁻¹ * (t * y * t⁻¹) * t = y by group] at this

theorem le_of_inf_normalizer_le {T B : Subgroup X} (hT : IsPGroup 2 T) (hB : IsPGroup 2 B)
    (hBT : B ≤ normalizer (T : Set X)) (hQB : T ⊓ normalizer (B : Set X) ≤ B) : T ≤ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hP2 : IsPGroup 2 (T ⊔ B : Subgroup X) := hT.to_sup_of_normal_left' hB hBT
  set P : Subgroup X := T ⊔ B with hP
  have hBP : B.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun heq => hne ?_
    have : P ≤ B := by
      intro y hy
      have : (⟨y, hy⟩ : P) ∈ B.subgroupOf P := heq ▸ mem_top _
      exact this
    exact le_sup_left.trans this
  have : Group.IsNilpotent P := hP2.isNilpotent
  obtain ⟨-, g, hgN, hgB⟩ := IsConcreteLE.lt_iff_le_and_exists.mp
    (Group.normalizerCondition_of_isNilpotent (B.subgroupOf P) hBP)
  have hBP' : B ≤ P := le_sup_right
  have hg1 : ∀ y ∈ B, (g : X) * y * (g : X)⁻¹ ∈ B := fun y hy =>
    (mem_normalizer_iff.mp hgN ⟨y, hBP' hy⟩).mp hy
  have hg2 : ∀ y ∈ B, (g : X)⁻¹ * y * (g : X) ∈ B := fun y hy => by
    have h := (mem_normalizer_iff.mp (inv_mem hgN) ⟨y, hBP' hy⟩).mp hy
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  obtain ⟨t, ht, b, hb, htb⟩ := exists_mul_of_mem_sup_of_le_normalizer hBT g.2
  have htn : t ∈ normalizer (B : Set X) := by
    have ht' : t = (g : X) * b⁻¹ := by rw [← htb, mul_inv_cancel_right]
    refine mem_normalizer_of_conj_mem (fun y hy => ?_) (fun y hy => ?_)
    · rw [ht', show (g : X) * b⁻¹ * y * ((g : X) * b⁻¹)⁻¹ = (g : X) * (b⁻¹ * y * b) * (g : X)⁻¹
        by group]
      exact hg1 _ (mul_mem (mul_mem (inv_mem hb) hy) hb)
    · rw [ht', show ((g : X) * b⁻¹)⁻¹ * y * ((g : X) * b⁻¹) = b * ((g : X)⁻¹ * y * (g : X)) * b⁻¹
        by group]
      exact mul_mem (mul_mem hb (hg2 y hy)) (inv_mem hb)
  have htB : t ∈ B := hQB ⟨ht, htn⟩
  apply hgB
  change (g : X) ∈ B
  rw [← htb]
  exact mul_mem htB hb

theorem oddCore_centralizer_le_lStar_of_le_normalizer (T : Sylow 2 (lTwoPrimeTwo X)) :
    ∀ B : Subgroup X, IsPGroup 2 B →
      B ≤ normalizer (((T : Subgroup _).map (lTwoPrimeTwo X).subtype : Subgroup X) : Set X) →
      (pPrimeCore 2 (centralizer (B : Set X))).map (centralizer (B : Set X)).subtype ≤
        lStar ((T : Subgroup _).map (lTwoPrimeTwo X).subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := pLayer_two_normal' (X := X)
  set T' : Subgroup X := (T : Subgroup (lTwoPrimeTwo X)).map (lTwoPrimeTwo X).subtype with hT'
  have hT'2 : IsPGroup 2 T' := T.isPGroup'.map (lTwoPrimeTwo X).subtype
  have hT'L : T' ≤ (lTwoPrimeTwo X) := Subgroup.map_subtype_le _
  intro B
  induction h : Nat.card X - Nat.card B using Nat.strong_induction_on generalizing B with
  | _ n ih =>
  intro hB hBT
  set D := (pPrimeCore 2 (centralizer (B : Set X))).map (centralizer (B : Set X)).subtype with hD
  set Q : Subgroup X := T' ⊓ normalizer (B : Set X) with hQ
  have hQ2 : IsPGroup 2 Q := hT'2.to_le inf_le_left
  have hQD : Q ≤ normalizer (D : Set X) := fun q hq => by
    have hqB := (Subgroup.mem_inf.mp hq).2
    refine mem_normalizer_of_conj_mem (fun d hd => conj_mem_oddCore_centralizer hqB hd)
      (fun d hd => ?_)
    have := conj_mem_oddCore_centralizer (inv_mem hqB) hd
    rwa [inv_inv] at this
  have hDodd : Odd (Nat.card D) := odd_card_map_pPrimeCore _
  have hdec := le_commutator_sup_inf_centralizer_of_odd hQ2 hQD hDodd
  have hcomm : ⁅D, Q⁆ ≤ pLayer X 2 ⊔ pPrimeCore 2 X := by
    intro x hx
    have hxD : x ∈ D := by
      have hle : ⁅D, Q⁆ ≤ D := by
        rw [commutator_le]
        intro a ha q hq
        have h1 : q * a⁻¹ * q⁻¹ ∈ D := (mem_normalizer_iff.mp (hQD hq) a⁻¹).mp (inv_mem ha)
        have h2 := mul_mem ha h1
        rw [commutatorElement_def]
        simpa [mul_assoc] using h2
      exact hle hx
    have hxY : x ∈ (lTwoPrimeTwo X) := by
      have hle : ⁅D, Q⁆ ≤ (lTwoPrimeTwo X) :=
        (Subgroup.commutator_mono le_rfl (inf_le_left.trans hT'L)).trans
          (Subgroup.commutator_le_right D (lTwoPrimeTwo X))
      exact hle hx
    exact mem_pLayer_sup_of_mem_lTwoPrimeTwo hxY (odd_orderOf_of_mem_map_pPrimeCore hxD)
  set R : Subgroup X := Q ⊔ B with hR
  have hRcen : ∀ x : X, x ∈ centralizer (R : Set X) ↔
      x ∈ centralizer (Q : Set X) ∧ x ∈ centralizer (B : Set X) := by
    intro x
    constructor
    · intro hx
      exact ⟨centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hx,
        centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) hx⟩
    · rintro ⟨hxQ, hxB⟩
      have hle : R ≤ centralizer ({x} : Set X) := sup_le
        (fun q hq => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxQ q hq))
        (fun b hb => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxB b hb))
      exact mem_centralizer_iff.mpr fun r hr => mem_centralizer_singleton_iff.mp (hle hr)
  have hDQ : D ⊓ centralizer (Q : Set X) ≤
      (pPrimeCore 2 (centralizer (R : Set X))).map (centralizer (R : Set X)).subtype := by
    apply le_map_pPrimeCore
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      exact (hRcen x).mpr ⟨hx2, Subgroup.map_subtype_le _ hx1⟩
    · intro c hc x hx
      obtain ⟨hcQ, hcB⟩ := (hRcen c).mp hc
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem hcQ hx2) (inv_mem hcQ)⟩
      obtain ⟨x', hx', hxx⟩ := hx1
      have hn : (pPrimeCore 2 (centralizer (B : Set X))).Normal := inferInstance
      refine ⟨⟨c, hcB⟩ * x' * ⟨c, hcB⟩⁻¹, hn.conj_mem x' hx' _, ?_⟩
      rw [← hxx]
      rfl
    · exact hDodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hL : pLayer X 2 ⊔ pPrimeCore 2 X ≤ lStar T' := le_sup_left
  by_cases hQB : Q ≤ B
  ·
    have hTB : T' ≤ B := le_of_inf_normalizer_le hT'2 hB hBT hQB
    intro d hd
    have hdT : d ∈ centralizer (T' : Set X) :=
      centralizer_le (SetLike.coe_subset_coe.mpr hTB) (Subgroup.map_subtype_le _ hd)
    exact Subgroup.mem_sup_right
      (mem_oddCore_centralizer_of_odd T hdT (odd_orderOf_of_mem_map_pPrimeCore hd))
  ·
    have hBR : B < R := lt_of_le_of_ne le_sup_right fun heq => hQB (heq ▸ le_sup_left)
    have hR2 : IsPGroup 2 R := hQ2.to_sup_of_normal_right' hB inf_le_right
    have hRT : R ≤ normalizer (T' : Set X) := sup_le (inf_le_left.trans le_normalizer) hBT
    have hlt : Nat.card X - Nat.card R < n := by
      have h1 : Nat.card B < Nat.card R := Subgroup.card_lt_of_lt hBR
      have h2 : Nat.card R ≤ Nat.card X := Subgroup.card_le_card_group R
      omega
    have hRle := ih _ hlt R rfl hR2 hRT
    exact hdec.trans (sup_le (hcomm.trans hL) (hDQ.trans hRle))

theorem oddCore_centralizer_le_lStar {B : Subgroup X} (hB : IsPGroup 2 B)
    (T : Sylow 2 (lTwoPrimeTwo X)) :
    (pPrimeCore 2 (centralizer (B : Set X))).map (centralizer (B : Set X)).subtype ≤
      lStar ((T : Subgroup _).map (lTwoPrimeTwo X).subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := pLayer_two_normal' (X := X)
  obtain ⟨S, hBS⟩ := hB.exists_le_sylow
  obtain ⟨T₀, hT₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    (Subgroup.Normal.isSubnormal (inferInstance : (lTwoPrimeTwo X).Normal))
  have hBT₀ : B ≤ normalizer (((T₀ : Subgroup (lTwoPrimeTwo X)).map (lTwoPrimeTwo X).subtype :
      Subgroup X) : Set X) := by
    intro b hb
    rw [hT₀]
    refine mem_normalizer_of_conj_mem (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (hBS hb) hy1) (inv_mem (hBS hb)),
        (inferInstance : (lTwoPrimeTwo X).Normal).conj_mem y hy2 b⟩
    · obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem (hBS hb)) hy1) (hBS hb), ?_⟩
      have := (inferInstance : (lTwoPrimeTwo X).Normal).conj_mem y hy2 b⁻¹
      simpa using this
  have h₀ := oddCore_centralizer_le_lStar_of_le_normalizer T₀ B hB hBT₀
  refine h₀.trans ?_
  set T' : Subgroup X := (T : Subgroup (lTwoPrimeTwo X)).map (lTwoPrimeTwo X).subtype with hT'
  set T₀' : Subgroup X := (T₀ : Subgroup (lTwoPrimeTwo X)).map (lTwoPrimeTwo X).subtype with hT₀'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (lTwoPrimeTwo X) T T₀
  have hconj : ∀ t ∈ T', (g : X) * t * (g : X)⁻¹ ∈ T₀' := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 : (MulAut.conj g) • t ∈ (MulAut.conj g) • (T : Subgroup (lTwoPrimeTwo X)) :=
      Subgroup.smul_mem_pointwise_smul t (MulAut.conj g) _ ht
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    exact ⟨_, h1, by simp [MulAut.smul_def]⟩
  have hYN : lTwoPrimeTwo X ≤ normalizer ((lStar T' : Subgroup X) : Set X) := by
    refine (lTwoPrimeTwo_le_sup T).trans (sup_le (sup_le ?_ ?_) ?_)
    · exact (le_sup_left.trans le_sup_left : pLayer X 2 ≤ lStar T').trans le_normalizer
    · exact (le_sup_right.trans le_sup_left : pPrimeCore 2 X ≤ lStar T').trans le_normalizer
    · intro t ht
      have htN : t ∈ normalizer (T' : Set X) := le_normalizer ht
      refine mem_normalizer_sup_of_mem (mem_normalizer_sup_of_mem ?_ ?_) ?_
      · exact mem_normalizer_of_conj_mem (fun z hz => pLayer_two_normal'.conj_mem z hz t)
          (fun z hz => by simpa using pLayer_two_normal'.conj_mem z hz t⁻¹)
      · exact mem_normalizer_of_conj_mem
          (fun z hz => (inferInstance : (pPrimeCore 2 X).Normal).conj_mem z hz t)
          (fun z hz => by simpa using (inferInstance : (pPrimeCore 2 X).Normal).conj_mem z hz t⁻¹)
      · refine mem_normalizer_of_conj_mem (fun d hd => conj_mem_oddCore_centralizer htN hd)
          (fun d hd => ?_)
        have := conj_mem_oddCore_centralizer (inv_mem htN) hd
        rwa [inv_inv] at this
  have hgN := hYN g.2
  refine sup_le le_sup_left ?_
  intro f hf
  have hfC : f ∈ centralizer (T₀' : Set X) := Subgroup.map_subtype_le _ hf
  have hfodd := odd_orderOf_of_mem_map_pPrimeCore hf
  set f' := (g : X)⁻¹ * f * (g : X) with hf'
  have hf'C : f' ∈ centralizer (T' : Set X) := by
    rw [mem_centralizer_iff]
    intro t ht
    have h2 := mem_centralizer_iff.mp hfC _ (hconj t ht)
    rw [hf']
    calc t * ((g : X)⁻¹ * f * (g : X)) =
        (g : X)⁻¹ * (((g : X) * t * (g : X)⁻¹) * f) * (g : X) := by group
      _ = (g : X)⁻¹ * (f * ((g : X) * t * (g : X)⁻¹)) * (g : X) := by rw [h2]
      _ = (g : X)⁻¹ * f * (g : X) * t := by group
  have hf'odd : Odd (orderOf f') := by
    have h1 := orderOf_injective (MulAut.conj (g : X)⁻¹).toMonoidHom (MulAut.conj _).injective f
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    rw [hf', h1]
    exact hfodd
  have hf'F := mem_oddCore_centralizer_of_odd T hf'C hf'odd
  have hf'J : f' ∈ lStar T' := Subgroup.mem_sup_right hf'F
  have := (mem_normalizer_iff.mp hgN f').mp hf'J
  rwa [hf', show (g : X) * ((g : X)⁻¹ * f * (g : X)) * (g : X)⁻¹ = f by group] at this

end CFSG.ComponentClassification.GrSLit
