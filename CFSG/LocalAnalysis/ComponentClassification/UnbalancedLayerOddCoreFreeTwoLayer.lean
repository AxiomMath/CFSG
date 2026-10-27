module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddFixedNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalPComponentCore
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
public import CFSG.LocalAnalysis.ComponentInitial.PerfectNormalizerLayer

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H]

def displacementSubgroup (Z : Subgroup H) (t : H) : Subgroup H where
  carrier := {c | c ∈ centralizer (Z : Set H) ∧ c⁻¹ * (t⁻¹ * c * t) ∈ Z}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨haC, haZ⟩ ⟨hbC, hbZ⟩
    refine ⟨mul_mem haC hbC, ?_⟩
    have hb : b⁻¹ * (a⁻¹ * (t⁻¹ * a * t)) * b = a⁻¹ * (t⁻¹ * a * t) := by
      rw [mul_assoc, mem_centralizer_iff.mp hbC _ haZ, inv_mul_cancel_left]
    rw [show (a * b)⁻¹ * (t⁻¹ * (a * b) * t) =
      b⁻¹ * (a⁻¹ * (t⁻¹ * a * t)) * b * (b⁻¹ * (t⁻¹ * b * t)) by group, hb]
    exact mul_mem haZ hbZ
  inv_mem' := by
    rintro a ⟨haC, haZ⟩
    refine ⟨inv_mem haC, ?_⟩
    have ha : a * (a⁻¹ * (t⁻¹ * a * t))⁻¹ * a⁻¹ = (a⁻¹ * (t⁻¹ * a * t))⁻¹ := by
      rw [← mem_centralizer_iff.mp haC _ (inv_mem haZ), mul_inv_cancel_right]
    rw [show a⁻¹⁻¹ * (t⁻¹ * a⁻¹ * t) = a * (a⁻¹ * (t⁻¹ * a * t))⁻¹ * a⁻¹ by group, ha]
    exact inv_mem haZ

theorem mem_displacementSubgroup {Z : Subgroup H} {t c : H} :
    c ∈ displacementSubgroup Z t ↔ c ∈ centralizer (Z : Set H) ∧ c⁻¹ * (t⁻¹ * c * t) ∈ Z :=
  Iff.rfl

theorem centralizer_inf_le_displacementSubgroup (Z : Subgroup H) (t : H) :
    centralizer (Z : Set H) ⊓ centralizer ({t} : Set H) ≤ displacementSubgroup Z t := by
  intro c hc
  obtain ⟨hcZ, hct⟩ := Subgroup.mem_inf.mp hc
  refine mem_displacementSubgroup.mpr ⟨hcZ, ?_⟩
  rw [mem_centralizer_singleton_iff_conj.mp hct, inv_mul_cancel]
  exact one_mem _

theorem centralizer_inf_normal_displacementSubgroup (Z : Subgroup H) (t : H) :
    ((centralizer (Z : Set H) ⊓ centralizer ({t} : Set H)).subgroupOf
      (displacementSubgroup Z t)).Normal := by
  have key : ∀ w ∈ displacementSubgroup Z t,
      ∀ x ∈ centralizer (Z : Set H) ⊓ centralizer ({t} : Set H),
      w * x * w⁻¹ ∈ centralizer (Z : Set H) ⊓ centralizer ({t} : Set H) := by
    intro w hw x hx
    obtain ⟨hwC, hwZ⟩ := mem_displacementSubgroup.mp hw
    obtain ⟨hxC, hxt⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hwC hxC) (inv_mem hwC), ?_⟩
    rw [mem_centralizer_singleton_iff_conj] at hxt ⊢
    have hzx : x * (w⁻¹ * (t⁻¹ * w * t)) = w⁻¹ * (t⁻¹ * w * t) * x :=
      (mem_centralizer_iff.mp hxC _ hwZ).symm
    calc t⁻¹ * (w * x * w⁻¹) * t
        = w * (w⁻¹ * (t⁻¹ * w * t)) * (t⁻¹ * x * t) * (w⁻¹ * (t⁻¹ * w * t))⁻¹ * w⁻¹ := by
          group
      _ = w * ((w⁻¹ * (t⁻¹ * w * t)) * x) * (w⁻¹ * (t⁻¹ * w * t))⁻¹ * w⁻¹ := by
          rw [hxt, mul_assoc w]
      _ = w * (x * (w⁻¹ * (t⁻¹ * w * t))) * (w⁻¹ * (t⁻¹ * w * t))⁻¹ * w⁻¹ := by rw [hzx]
      _ = w * x * w⁻¹ := by group
  rw [normal_subgroupOf_iff_le_normalizer (centralizer_inf_le_displacementSubgroup Z t)]
  intro w hw
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key w hw x, fun hx => ?_⟩
  have h := key w⁻¹ (inv_mem hw) _ hx
  rwa [show w⁻¹ * (w * x * w⁻¹) * w⁻¹⁻¹ = x by group] at h

theorem map_conj_eq_conjugate (K : Subgroup H) (g : H) :
    K.map (MulAut.conj g).toMonoidHom = conjugate K g⁻¹ := by
  unfold conjugate
  rw [inv_inv]

variable [Finite H]

theorem fittingSubgroup_le_pCore_two (hO : pPrimeCore 2 H = ⊥) :
    fittingSubgroup H ≤ pCore 2 H := by
  rw [fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun p => ?_
  have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
  by_cases h2 : (p : ℕ) = 2
  · rw [h2]
  · have : Fact (p : ℕ).Prime := ⟨hp⟩
    have hle : pCore (p : ℕ) H ≤ pPrimeCore 2 H := by
      refine le_sSup ⟨pCore_normal, ?_⟩
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := (p : ℕ)) (G := H)).exists_card_eq
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm h2))
    rw [hO] at hle
    exact hle.trans bot_le

omit [Finite H] in
theorem center_layer_le_fittingSubgroup :
    (center (layer H)).map (layer H).subtype ≤ fittingSubgroup H := by
  have : (layer H).Characteristic := layer_characteristic
  have hE : (layer H).Normal := inferInstance
  have hZn : ((center (layer H)).map (layer H).subtype).Normal := by
    constructor
    intro z hz h
    obtain ⟨hzE, hzc⟩ := (mem_map_center_iff _).mp hz
    refine (mem_map_center_iff _).mpr ⟨hE.conj_mem z hzE h, ?_⟩
    rw [mem_centralizer_iff]
    intro e he
    have he' : h⁻¹ * e * h ∈ layer H := by simpa using hE.conj_mem e he h⁻¹
    have hez := mem_centralizer_iff.mp hzc _ he'
    calc e * (h * z * h⁻¹) = h * ((h⁻¹ * e * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * e * h)) * h⁻¹ := by rw [hez]
      _ = h * z * h⁻¹ * e := by group
  have hZc : IsMulCommutative ((center (layer H)).map (layer H).subtype) := by
    refine isMulCommutative_iff.mpr fun x y => Subtype.ext ?_
    obtain ⟨-, hxc⟩ := (mem_map_center_iff _).mp x.2
    obtain ⟨hyE, -⟩ := (mem_map_center_iff _).mp y.2
    exact (mem_centralizer_iff.mp hxc _ hyE).symm
  exact fitting_characteristic.2.2 _ hZn inferInstance

theorem two_component_le_layer (hO : pPrimeCore 2 H = ⊥) {t : H} (ht : orderOf t = 2)
    (hout : ∀ K : Subgroup H, IsComponent K →
      Group.IsSolvable (OuterAutomorphisms.Outer (K ⧸ center K)))
    {L : Subgroup H} (hLC : L ≤ centralizer ({t} : Set H))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set H)))) : L ≤ layer H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have : (layer H).Characteristic := layer_characteristic
  have hE : (layer H).Normal := inferInstance
  set Z := (center (layer H)).map (layer H).subtype with hZdef
  have hLperf : Group.IsPerfect L := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hL
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLC).toMonoidHom)
      (subgroupOfEquivOfLe hLC).surjective
  have hLP : ⁅L, pCore 2 H⁆ = ⊥ := by
    have hS : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, ht, pow_one])
    have hCS : centralizer ((zpowers t : Subgroup H) : Set H) ≤ centralizer ({t} : Set H) :=
      centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers t))
    have hLS : (L.subgroupOf (centralizer ({t} : Set H))).map (centralizer ({t} : Set H)).subtype
        ≤ centralizer ((zpowers t : Subgroup H) : Set H) := by
      rw [map_subgroupOf_eq_of_le hLC, le_centralizer_iff, zpowers_le, mem_centralizer_iff]
      intro l hl
      exact mem_centralizer_singleton_iff.mp (hLC hl)
    have h := LiteratureLocal.p_component_commutator_eq_bot_of_le_centralizer hS pCore_normal
      pCore_isPGroup hCS hL hLS
    rwa [map_subgroupOf_eq_of_le hLC] at h
  have hLF : ⁅L, fittingSubgroup H⁆ = ⊥ :=
    le_bot_iff.mp (hLP ▸ commutator_mono le_rfl (fittingSubgroup_le_pCore_two hO))
  have hLZ : L ≤ centralizer (Z : Set H) := commutator_eq_bot_iff_le_centralizer.mp
    (le_bot_iff.mp (hLF ▸ commutator_mono le_rfl center_layer_le_fittingSubgroup))
  set U := displacementSubgroup Z t with hUdef
  have hCU := centralizer_inf_le_displacementSubgroup Z t
  have hLCC : L ≤ centralizer (Z : Set H) ⊓ centralizer ({t} : Set H) := le_inf hLZ hLC
  have hLU : IsPComponent 2 (L.subgroupOf U) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hLCC hCU
      (centralizer_inf_normal_displacementSubgroup Z t).isSubnormal).mpr
      (CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hLCC inf_le_right hL)
  have hNn : ((layer H ⊓ U).subgroupOf U).Normal := by
    rw [inf_subgroupOf_right]
    exact hE.subgroupOf U
  rcases CatalogueBPrimeJoin.contains_or_normalizes_core 2 (L.subgroupOf U)
      ((layer H ⊓ U).subgroupOf U) hLU hNn.isSubnormal with hLN | ⟨-, hcore⟩
  · exact (le_of_subgroupOf_le (hLCC.trans hCU) hLN).trans inf_le_left
  set O : Subgroup H := ((pPrimeCore 2 (L.subgroupOf U)).map (L.subgroupOf U).subtype).map
    U.subtype with hOdef
  have hOodd : Odd (Nat.card O) := by
    rw [hOdef, card_map_of_injective U.subtype_injective,
      card_map_of_injective (L.subgroupOf U).subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hdisp : ∀ l ∈ L, ∀ n ∈ layer H ⊓ U, l * n * l⁻¹ * n⁻¹ ∈ O := by
    intro l hl n hn
    have hlU : l ∈ U := hCU (hLCC hl)
    have hmem : ⁅(⟨l, hlU⟩ : U), (⟨n, (Subgroup.mem_inf.mp hn).2⟩ : U)⁆ ∈
        ⁅L.subgroupOf U, (layer H ⊓ U).subgroupOf U⁆ :=
      commutator_mem_commutator (mem_subgroupOf.mpr hl) (mem_subgroupOf.mpr hn)
    have h := mem_map_of_mem U.subtype (hcore hmem)
    simpa only [commutatorElement_def, coe_subtype, coe_mul, coe_inv] using h
  have heven : ∀ K : Subgroup H, IsComponent K → Even (Nat.card (K ⧸ center K)) := by
    intro K hK
    have : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
    exact (SimpleEvenOrder.nonabelian_simple_even hK.1.2.2).1
  have hnorm : ∀ K : Subgroup H, IsComponent K → L ≤ normalizer (K : Set H) := by
    intro K hK
    obtain ⟨u, huK, ⟨a, hua⟩, ⟨k₀, hk₀, hk₀u⟩, hz⟩ :=
      exists_two_element_witness hK (heven K hK) htt
    have huE : u ∈ layer H :=
      sup_le (component_le_layer hK) (component_le_layer (isComponent_conjugate hK t)) huK
    have huC : u ∈ centralizer (Z : Set H) := by
      rw [mem_centralizer_iff]
      intro z hzZ
      exact (mem_centralizer_iff.mp ((mem_map_center_iff _).mp hzZ).2 u huE).symm
    have huN : u ∈ layer H ⊓ U := Subgroup.mem_inf.mpr
      ⟨huE, mem_displacementSubgroup.mpr ⟨huC, center_component_le_center_layer hK hz⟩⟩
    have hpair : ∀ l ∈ L, conjugate K l⁻¹ = K ∨ conjugate K l⁻¹ = conjugate K t := by
      intro l hl
      by_contra hcon
      push Not at hcon
      obtain ⟨hne1, hne2⟩ := hcon
      have hl't : l⁻¹ * t = t * l⁻¹ := by
        have hlt : l * t = t * l := mem_centralizer_singleton_iff.mp (hLC hl)
        calc l⁻¹ * t = l⁻¹ * (t * l) * l⁻¹ := by group
          _ = l⁻¹ * (l * t) * l⁻¹ := by rw [hlt]
          _ = t * l⁻¹ := by group
      have hc := pair_le_centralizer_pair hK (isComponent_conjugate hK l⁻¹) htt hne1 hne2
      have hlu : l * u * l⁻¹ ∈ conjugate K l⁻¹ ⊔ conjugate (conjugate K l⁻¹) t := by
        rw [← conjugate_conjugate_comm K hl't, ← conjugate_sup]
        have h := conj_mem_conjugate huK l⁻¹
        rwa [inv_inv] at h
      have hcomm : Commute u (l * u * l⁻¹) := (mem_centralizer_iff.mp (hc huK) _ hlu).symm
      have hδa : (l * u * l⁻¹ * u⁻¹) ^ 2 ^ a = 1 := by
        rw [hcomm.symm.inv_right.mul_pow, conj_pow, inv_pow, hua]
        simp
      have hδ := eq_one_of_mem_of_pow_two_pow hOodd (hdisp l hl u huN) hδa
      have hlu' : l * u * l⁻¹ = u := mul_inv_eq_one.mp hδ
      apply hk₀u
      have hk₀c := mem_centralizer_iff.mp (hc (mem_sup_left hk₀)) _ hlu
      rwa [hlu'] at hk₀c
    let action : L →* MulAut H := MulAut.conj.comp L.subtype
    let permutationAction := ComponentAutomorphisms.subgroupAction action
    let latticeAction : MulAut H →* Equiv.Perm (Subgroup H) :=
      ComponentAutomorphisms.subgroupAction (MonoidHom.id (MulAut H))
    let involution := latticeAction (MulAut.conj t)
    have hinvolution : Function.Involutive involution := by
      intro X
      change (X.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = X
      rw [map_conj_eq_conjugate, map_conj_eq_conjugate, htinv,
        conjugate_conjugate_self_of_mul_self htt]
    have hcommutes : ∀ l : L, Commute involution (permutationAction l) := fun l =>
      ((show Commute t (l : H) from (mem_centralizer_singleton_iff.mp (hLC l.2)).symm).map
        MulAut.conj).map latticeAction
    have hpair' : ∀ l : L, permutationAction l K = K ∨ permutationAction l K = involution K := by
      intro l
      change K.map (MulAut.conj (l : H)).toMonoidHom = K ∨
        K.map (MulAut.conj (l : H)).toMonoidHom = K.map (MulAut.conj t).toMonoidHom
      rw [map_conj_eq_conjugate, map_conj_eq_conjugate, htinv]
      exact hpair l l.2
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact PerfectPermutationActions.fixed_of_involutive_pair permutationAction involution
      hinvolution hcommutes K hpair' ⟨x, hx⟩
  exact LocalAnalysis.ComponentInitial.unique_perfect_component_normalizer_enters_layer hLperf
    hLF hnorm hout

theorem odd_core_free_schreier_fixed_two_layer_containment (hO : pPrimeCore 2 H = ⊥) {t : H}
    (ht : orderOf t = 2)
    (hout : ∀ K : Subgroup H, IsComponent K →
      Group.IsSolvable (OuterAutomorphisms.Outer (K ⧸ center K))) :
    (∀ L : Subgroup H, L ≤ centralizer ({t} : Set H) →
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set H))) → L ≤ layer H) ∧
    (pLayer (centralizer ({t} : Set H)) 2).map (centralizer ({t} : Set H)).subtype ≤
      layer H := by
  have hmain : ∀ L : Subgroup H, L ≤ centralizer ({t} : Set H) →
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set H))) → L ≤ layer H :=
    fun L hLC hL => two_component_le_layer hO ht hout hLC hL
  refine ⟨hmain, ?_⟩
  rw [map_le_iff_le_comap]
  refine sSup_le fun L' hL' => ?_
  rw [← map_le_iff_le_comap]
  have hL'eq : (L'.map (centralizer ({t} : Set H)).subtype).subgroupOf
      (centralizer ({t} : Set H)) = L' :=
    comap_map_eq_self_of_injective (centralizer ({t} : Set H)).subtype_injective L'
  exact hmain _ (map_subtype_le L') (by rw [hL'eq]; exact hL')

end CFSG.ComponentClassification.UnbalancedLayer
