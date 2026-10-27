module

public import CFSG.FeitThompson.Local.PLengthOneSubgroupInheritance
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
import CFSG.FeitThompson.Foundations.HallImageQuotient

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p : ℕ} {X : Type*} [Group X]

theorem natCard_subgroupOf_eq_natCard_inf (D E : Subgroup X) :
    Nat.card (D.subgroupOf E) = Nat.card (D ⊓ E : Subgroup X) := by
  rw [← Subgroup.inf_subgroupOf_right]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right (a := D) (b := E))).toEquiv

theorem index_subgroupOf_eq_natCard_map_mk' [Finite X] (D E : Subgroup X) [D.Normal] :
    (D.subgroupOf E).index = Nat.card (E.map (QuotientGroup.mk' D)) := by
  have h1 : (D.subgroupOf E).index * Nat.card (D ⊓ E : Subgroup X) = Nat.card E := by
    rw [← natCard_subgroupOf_eq_natCard_inf]; exact Subgroup.index_mul_card _
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos
    (h1.trans (natCard_map_mk'_mul_natCard_inf E D).symm)

def pElements (p : ℕ) (X : Type*) [Group X] : Set X := {x : X | ∃ n : ℕ, orderOf x = p ^ n}

theorem mem_pElements {x : X} : x ∈ pElements p X ↔ ∃ n : ℕ, orderOf x = p ^ n := Iff.rfl

theorem one_mem_pElements : (1 : X) ∈ pElements p X := ⟨0, by simp⟩

def pElementSubgroup (p : ℕ) (X : Type*) [Group X] : Subgroup X :=
  Subgroup.closure (pElements p X)

theorem pElementSubgroup_eq_closure (p : ℕ) (X : Type*) [Group X] :
    pElementSubgroup p X = Subgroup.closure (pElements p X) := (rfl)

theorem mem_pElementSubgroup_of_mem_pElements {x : X} (hx : x ∈ pElements p X) :
    x ∈ pElementSubgroup p X := Subgroup.subset_closure hx

theorem pElementSubgroup_le_iff {H : Subgroup X} :
    pElementSubgroup p X ≤ H ↔ pElements p X ⊆ (H : Set X) := Subgroup.closure_le H

instance pElementSubgroup_characteristic (p : ℕ) (X : Type*) [Group X] :
    (pElementSubgroup p X).Characteristic := by
  refine Subgroup.characteristic_iff_map_le.2 fun ϕ => ?_
  rw [pElementSubgroup_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro y ⟨x, ⟨n, hn⟩, rfl⟩
  exact mem_pElementSubgroup_of_mem_pElements
    ⟨n, (orderOf_injective ϕ.toMonoidHom ϕ.injective x).trans hn⟩

theorem pElementSubgroup_normal (p : ℕ) (X : Type*) [Group X] :
    (pElementSubgroup p X).Normal := Subgroup.normal_of_characteristic _

theorem pElementSubgroup_eq_top_of_isPGroup [Finite X] (hp : p.Prime) (h : IsPGroup p X) :
    pElementSubgroup p X = ⊤ :=
  have : Fact p.Prime := ⟨hp⟩
  eq_top_iff.2 fun x _ => mem_pElementSubgroup_of_mem_pElements (h.exists_orderOf_eq_pow x)

theorem sylow_le_pElementSubgroup [Finite X] [Fact p.Prime] (P : Sylow p X) :
    (P : Subgroup X) ≤ pElementSubgroup p X := by
  intro x hx
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_orderOf_eq_pow (⟨x, hx⟩ : (P : Subgroup X))
  exact mem_pElementSubgroup_of_mem_pElements
    ⟨n, (Subgroup.orderOf_coe (⟨x, hx⟩ : (P : Subgroup X))).trans hn⟩

theorem not_dvd_index_pElementSubgroup [Finite X] [Fact p.Prime] :
    ¬ p ∣ (pElementSubgroup p X).index := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p X))
  exact fun h => P.not_dvd_index (h.trans
    (Subgroup.index_dvd_of_le (sylow_le_pElementSubgroup P)))

theorem mem_of_coprime_orderOf_index {T : Subgroup X} [T.Normal] {x : X}
    (h : (orderOf x).Coprime T.index) : x ∈ T := by
  have h1 : orderOf (QuotientGroup.mk x : X ⧸ T) ∣ orderOf x :=
    orderOf_map_dvd (QuotientGroup.mk' T) x
  have h2 : orderOf (QuotientGroup.mk x : X ⧸ T) ∣ T.index := by
    rw [T.index_eq_card]; exact orderOf_dvd_natCard _
  exact (QuotientGroup.eq_one_iff x).1
    (orderOf_eq_one_iff.1 ((h.coprime_dvd_left h1).eq_one_of_dvd h2))

theorem pElementSubgroup_le_of_not_dvd_index {T : Subgroup X} [T.Normal] (hp : p.Prime)
    (h : ¬ p ∣ T.index) : pElementSubgroup p X ≤ T := by
  refine pElementSubgroup_le_iff.2 fun x hx => ?_
  obtain ⟨n, hn⟩ := hx
  exact mem_of_coprime_orderOf_index
    (hn ▸ Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 h))

def tCore (p : ℕ) (X : Type*) [Group X] [Finite X] : Subgroup X :=
  (pCore p (X ⧸ pComplCore p X)).comap (QuotientGroup.mk' (pComplCore p X))

theorem tCore_eq_comap (p : ℕ) (X : Type*) [Group X] [Finite X] :
    tCore p X = (pCore p (X ⧸ pComplCore p X)).comap (QuotientGroup.mk' (pComplCore p X)) := (rfl)

theorem mem_tCore_iff [Finite X] {x : X} :
    x ∈ tCore p X ↔ (QuotientGroup.mk x : X ⧸ pComplCore p X) ∈ pCore p (X ⧸ pComplCore p X) :=
  Iff.rfl

instance tCore_normal (p : ℕ) (X : Type*) [Group X] [Finite X] : (tCore p X).Normal :=
  (pCore_normal p (X ⧸ pComplCore p X)).comap _

theorem pComplCore_le_tCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    pComplCore p X ≤ tCore p X := by
  intro x hx
  rw [mem_tCore_iff, (QuotientGroup.eq_one_iff x).2 hx]
  exact one_mem _

theorem index_tCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (tCore p X).index = (pCore p (X ⧸ pComplCore p X)).index :=
  Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem hasPLengthLeOne_iff_not_dvd_index_tCore [Finite X] [Fact p.Prime] :
    HasPLengthLeOne p X ↔ ¬ p ∣ (tCore p X).index := by
  rw [hasPLengthLeOne_iff_not_dvd_index, index_tCore]

theorem le_tCore_iff [Finite X] {H : Subgroup X} :
    H ≤ tCore p X ↔ H.map (QuotientGroup.mk' (pComplCore p X)) ≤ pCore p (X ⧸ pComplCore p X) :=
  (Subgroup.map_le_iff_le_comap).symm

def HasNormalPComplement (p : ℕ) (Y : Type*) [Group Y] : Prop :=
  ∃ K : Subgroup Y, IsNormalPComplement p K

variable {Y : Type*} [Group Y]

theorem hasNormalPComplement_iff :
    HasNormalPComplement p Y ↔ ∃ K : Subgroup Y, IsNormalPComplement p K := Iff.rfl

theorem IsNormalPComplement.mem_iff_not_dvd_orderOf (hp : p.Prime) {K : Subgroup Y}
    (hK : IsNormalPComplement p K) {x : Y} : x ∈ K ↔ ¬ p ∣ orderOf x := by
  have := hK.normal
  refine ⟨fun hx hdvd => hK.not_dvd_natCard (hdvd.trans (K.orderOf_dvd_natCard hx)),
    fun hx => ?_⟩
  obtain ⟨n, hn⟩ := hK.exists_index_eq_pow
  refine mem_of_coprime_orderOf_index (T := K) ?_
  rw [hn]
  exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hx).symm

theorem IsNormalPComplement.coe_eq (hp : p.Prime) {K : Subgroup Y}
    (hK : IsNormalPComplement p K) : (K : Set Y) = {x : Y | ¬ p ∣ orderOf x} :=
  Set.ext fun _ => hK.mem_iff_not_dvd_orderOf hp

theorem IsNormalPComplement.unique (hp : p.Prime) {K L : Subgroup Y}
    (hK : IsNormalPComplement p K) (hL : IsNormalPComplement p L) : K = L :=
  SetLike.ext fun _ =>
    (hK.mem_iff_not_dvd_orderOf hp).trans (hL.mem_iff_not_dvd_orderOf hp).symm

theorem IsNormalPComplement.characteristic (hp : p.Prime) {K : Subgroup Y}
    (hK : IsNormalPComplement p K) : K.Characteristic := by
  refine Subgroup.characteristic_iff_map_le.2 fun ϕ => ?_
  rintro y ⟨x, hx, rfl⟩
  rw [hK.mem_iff_not_dvd_orderOf hp, orderOf_injective ϕ.toMonoidHom ϕ.injective x]
  exact (hK.mem_iff_not_dvd_orderOf hp).1 hx

theorem isNormalPComplement_top [Finite Y] (h : ¬ p ∣ Nat.card Y) :
    IsNormalPComplement p (⊤ : Subgroup Y) :=
  isNormalPComplement_of inferInstance
    (by rwa [Nat.card_eq_of_bijective _ (Subgroup.topEquiv (G := Y)).bijective])
    ⟨0, by simp⟩

theorem isNormalPComplement_bot (hp : p.Prime) [Finite Y] (h : IsPGroup p Y) :
    IsNormalPComplement p (⊥ : Subgroup Y) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h
  refine isNormalPComplement_of inferInstance ?_ ⟨n, by rw [Subgroup.index_bot, hn]⟩
  rw [Subgroup.card_bot]
  exact fun hd => hp.ne_one (Nat.dvd_one.1 hd)

theorem hasPLengthLeOne_iff_hasNormalPComplement [Finite X] [Fact p.Prime] :
    HasPLengthLeOne p X ↔ HasNormalPComplement p (pElementSubgroup p X) := by
  have hp : p.Prime := Fact.out
  set D := pComplCore p X with hD
  set E := pElementSubgroup p X with hE
  constructor
  ·
    intro h
    have hET : E ≤ tCore p X :=
      pElementSubgroup_le_of_not_dvd_index hp (hasPLengthLeOne_iff_not_dvd_index_tCore.1 h)
    refine ⟨D.subgroupOf E, isNormalPComplement_of Subgroup.normal_subgroupOf ?_ ?_⟩
    · intro hdvd
      refine not_dvd_natCard_pComplCore hp X (hdvd.trans ?_)
      rw [natCard_subgroupOf_eq_natCard_inf]
      exact Subgroup.card_dvd_of_le inf_le_left
    · obtain ⟨m, hm⟩ := exists_card_pCore_eq_pow hp (X ⧸ D)
      have hdvd : Nat.card (E.map (QuotientGroup.mk' D)) ∣ p ^ m :=
        hm ▸ Subgroup.card_dvd_of_le (le_tCore_iff.1 hET)
      obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      exact ⟨k, by rw [index_subgroupOf_eq_natCard_map_mk', hk]⟩
  ·
    rintro ⟨K, hK⟩
    have hKchar : K.Characteristic := hK.characteristic hp
    have hsub : (K.map E.subtype).subgroupOf E = K :=
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective K
    have hchar : ((K.map E.subtype).subgroupOf E).Characteristic := by rw [hsub]; exact hKchar
    have hK'normal : (K.map E.subtype).Normal :=
      normal_of_characteristic_subgroupOf_of_normal (Subgroup.map_subtype_le K)
    have hK'D : K.map E.subtype ≤ D := by
      refine le_pComplCore hK'normal ?_
      rw [Subgroup.card_map_of_injective E.subtype_injective]
      exact fun hmem => hK.not_dvd_natCard (Nat.dvd_of_mem_primeFactors hmem)
    have hKle : K ≤ D.subgroupOf E := fun x hx => Subgroup.mem_subgroupOf.2 (hK'D ⟨x, hx, rfl⟩)
    obtain ⟨n, hn⟩ := hK.exists_index_eq_pow
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).1 (hn ▸ Subgroup.index_dvd_of_le hKle)
    have hcardmap : Nat.card (E.map (QuotientGroup.mk' D)) = p ^ k := by
      rw [← index_subgroupOf_eq_natCard_map_mk', hk]
    have hEle : E ≤ tCore p X :=
      le_tCore_iff.2 (le_pCore hp ((pElementSubgroup_normal p X).map _
        (QuotientGroup.mk'_surjective _)) (IsPGroup.of_card hcardmap))
    exact hasPLengthLeOne_iff_not_dvd_index_tCore.2 fun hdvd =>
      not_dvd_index_pElementSubgroup (p := p) (X := X)
        (hdvd.trans (Subgroup.index_dvd_of_le hEle))

end

end CFSG.FeitThompson
