module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpType
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpSylowGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpSylowAlt8
public import CFSG.Sporadic.HS
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

section QuotAut

variable {M : Type*} [Group M]

theorem map_center_eq_center (e : MulAut M) : (center M).map e.toMonoidHom = center M := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨z, hz, rfl⟩ g
    obtain ⟨h, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hz h]
  · intro hy
    refine ⟨e.symm y, fun g => ?_, by simp⟩
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hy (e g)

@[expose] def sylowQuotAut (e : MulAut M) : MulAut (M ⧸ center M) :=
  QuotientGroup.congr (center M) (center M) e (map_center_eq_center e)

theorem sylowQuotAut_mk (e : MulAut M) (m : M) :
    sylowQuotAut e (m : M ⧸ center M) = ((e m : M) : M ⧸ center M) := rfl

@[expose] def sylowQuotAutHom : MulAut M →* MulAut (M ⧸ center M) where
  toFun := sylowQuotAut
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H m => rfl
  map_mul' e f := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H m => rfl

theorem sylowQuotAutHom_mk (e : MulAut M) (m : M) :
    sylowQuotAutHom e (m : M ⧸ center M) = ((e m : M) : M ⧸ center M) := rfl

theorem commutator_mul_central_left {x y c : M} (hc : c ∈ center M) :
    ⁅x * c, y⁆ = ⁅x, y⁆ := by
  have h := Subgroup.mem_center_iff.mp hc
  have h1 : c * y * c⁻¹ = y := by rw [← h y]; simp
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * c * y * (c⁻¹ * x⁻¹) * y⁻¹ = x * (c * y * c⁻¹) * x⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h1]

theorem commutator_mul_central_right {x y c : M} (hc : c ∈ center M) :
    ⁅x, y * c⁆ = ⁅x, y⁆ := by
  have h := Subgroup.mem_center_iff.mp hc
  have h1 : c * x⁻¹ * c⁻¹ = x⁻¹ := by rw [← h x⁻¹]; simp
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * (y * c) * x⁻¹ * (c⁻¹ * y⁻¹) = x * y * (c * x⁻¹ * c⁻¹) * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h1]

theorem eq_one_of_sylowQuotAut_eq_one (hperf : commutator M = ⊤) (σ : MulAut M)
    (h : sylowQuotAutHom σ = 1) : σ = 1 := by
  have hc : ∀ x : M, x⁻¹ * σ x ∈ center M := by
    intro x
    have := congrArg (fun f : MulAut (M ⧸ center M) => f (x : M ⧸ center M)) h
    simp only [sylowQuotAutHom_mk, MulAut.one_apply] at this
    exact QuotientGroup.eq.mp this.symm
  have hσ : ∀ x : M, σ x = x * (x⁻¹ * σ x) := fun x => by group
  let F : Subgroup M := MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id M)
  have hF : commutator M ≤ F := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    show σ ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, hσ a, hσ b, commutator_mul_central_left (hc a),
      commutator_mul_central_right (hc b)]
  rw [hperf] at hF
  ext x
  exact hF (Subgroup.mem_top x)

end QuotAut

section Action

variable {G : Type*} [Group G]

@[expose] def barRho (M Q : Subgroup G) (hQ : Q ≤ normalizer (M : Set G)) :
    ↥Q →* MulAut (M ⧸ center M) :=
  sylowQuotAutHom.comp (M.normalizerMonoidHom.comp (Subgroup.inclusion hQ))

theorem barRho_mk (M Q : Subgroup G) (hQ : Q ≤ normalizer (M : Set G)) (q : Q) (m : M) :
    barRho M Q hQ q (m : M ⧸ center M) =
      ((M.normalizerMonoidHom (Subgroup.inclusion hQ q) m : M) : M ⧸ center M) := rfl

theorem coe_normalizerMonoidHom (M : Subgroup G) (d : normalizer (M : Set G)) (m : M) :
    ((M.normalizerMonoidHom d m : M) : G) = (d : G) * m * (d : G)⁻¹ := rfl

theorem mem_centralizer_of_barRho_eq_one {M Q : Subgroup G} (hperf : commutator ↥M = ⊤)
    (hQ : Q ≤ normalizer (M : Set G)) {q : Q} (h : barRho M Q hQ q = 1) :
    (q : G) ∈ centralizer (M : Set G) := by
  have hσ := eq_one_of_sylowQuotAut_eq_one hperf _ h
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have h1 : ((M.normalizerMonoidHom (Subgroup.inclusion hQ q) ⟨m, hm⟩ : M) : G) = m :=
    congrArg (fun f : MulAut M => ((f ⟨m, hm⟩ : M) : G)) hσ
  have h2 : (q : G) * m * (q : G)⁻¹ = m := by
    have := coe_normalizerMonoidHom M (Subgroup.inclusion hQ q) ⟨m, hm⟩
    rw [h1] at this
    exact this.symm
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

theorem barRho_apply_of_mem_centralizer (M Q K : Subgroup G) (hQ : Q ≤ normalizer (M : Set G))
    (hQK : Q ≤ centralizer (K : Set G)) (q : Q) (k : M) (hk : (k : G) ∈ K) :
    barRho M Q hQ q (k : M ⧸ center M) = (k : M ⧸ center M) := by
  rw [barRho_mk]
  congr 1
  apply Subtype.ext
  rw [coe_normalizerMonoidHom]
  have := Subgroup.mem_centralizer_iff.mp (hQK q.2) k hk
  show (q : G) * k * (q : G)⁻¹ = k
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

end Action

section Key

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_alt8_image {M K : Subgroup G} (hKM : K ≤ M)
    (hK : Nonempty (↥K ≃* alternatingGroup (Fin 8))) :
    ∃ A : Subgroup (M ⧸ center M), Nonempty (↥A ≃* alternatingGroup (Fin 8)) ∧
      ∀ a ∈ A, ∃ k : M, (k : G) ∈ K ∧ (k : M ⧸ center M) = a := by
  obtain ⟨e⟩ := hK
  let K' : Subgroup M := K.subgroupOf M
  let f : ↥K' →* M ⧸ center M := (QuotientGroup.mk' (center M)).comp K'.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkc : ((k : M)) ∈ center M := (QuotientGroup.eq_one_iff _).mp hk
    have hkK : ((k : M) : G) ∈ K := Subgroup.mem_subgroupOf.mp k.2
    have hk1 : e ⟨((k : M) : G), hkK⟩ ∈ Subgroup.center (alternatingGroup (Fin 8)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨h, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have := Subgroup.mem_center_iff.mp hkc ⟨(h : G), hKM h.2⟩
      simpa using congrArg Subtype.val this
    rw [alternatingGroup.center_eq_bot (by norm_num), Subgroup.mem_bot] at hk1
    have h2 : (⟨((k : M) : G), hkK⟩ : K) = 1 := e.injective (by rw [hk1, map_one])
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : K => (y : G)) h2
  refine ⟨f.range, ⟨?_⟩, ?_⟩
  · exact ((MonoidHom.ofInjective hinj).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hKM).trans e))
  · rintro _ ⟨k, rfl⟩
    exact ⟨k, Subgroup.mem_subgroupOf.mp k.2, rfl⟩

omit [Finite G] in
theorem mem_normalizer_of_commute_sylow {M : Subgroup G}
    (hM : CFSG.Open.standardComponentIsStandard M) {u g : G}
    (hu : u ∈ centralizer (M : Set G)) (hu2 : orderOf u = 2) (hg : g * u = u * g) :
    g ∈ normalizer (M : Set G) :=
  CFSG.Open.standardComponentIsStandard.mem_normalizer_of_commute hM hu hu2 hg

theorem card_le_two_of_le_centralizer {M : Subgroup G}
    (hC : ∀ S : Sylow 2 (centralizer (M : Set G)), Nat.card S = 2)
    {R : Subgroup G} (hR : R ≤ centralizer (M : Set G)) (hRp : IsPGroup 2 R) :
    Nat.card R ≤ 2 := by
  let R' := R.subgroupOf (centralizer (M : Set G))
  have hR'p : IsPGroup 2 R' := hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hR).symm
  obtain ⟨S, hS⟩ := hR'p.exists_le_sylow
  have h1 : Nat.card R' ≤ Nat.card S := Subgroup.card_le_of_le hS
  rw [hC S] at h1
  have : Nat.card R' = Nat.card R := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv
  omega

theorem card_le_four_of_two_subgroup (hKG : KGHSA8) {M K : Subgroup G}
    (hperf : commutator ↥M = ⊤) (hcat : Catalog (M ⧸ center M))
    (hsimple : IsSimpleGroup (M ⧸ center M)) (hcard : Nat.card (M ⧸ center M) = 44352000)
    (hKM : K ≤ M) (hK : Nonempty (↥K ≃* alternatingGroup (Fin 8)))
    (hC2 : ∀ R : Subgroup G, R ≤ centralizer (M : Set G) → IsPGroup 2 R → Nat.card R ≤ 2)
    {Q : Subgroup G} (hQN : Q ≤ normalizer (M : Set G)) (hQK : Q ≤ centralizer (K : Set G))
    (hQ : IsPGroup 2 Q) : Nat.card Q ≤ 4 := by
  obtain ⟨A, hA, hAK⟩ := exists_alt8_image hKM hK
  set ρ := barRho M Q hQN with hρ
  have hfix : ∀ s : ρ.range, ∀ a ∈ A, (s : MulAut (M ⧸ center M)) a = a := by
    rintro ⟨_, q, rfl⟩ a ha
    obtain ⟨k, hk, rfl⟩ := hAK a ha
    exact barRho_apply_of_mem_centralizer M Q K hQN hQK q k hk
  have hrange : Nat.card ρ.range ≤ 2 := by
    have hle := hKG (M ⧸ center M) hcat hsimple hcard A hA
    let φ : ρ.range → {σ : MulAut (M ⧸ center M) // ∀ a ∈ A, σ a = a} :=
      fun s => ⟨s, hfix s⟩
    have hφ : Function.Injective φ := by
      intro s t h
      have h' := congrArg
        (fun z : {σ : MulAut (M ⧸ center M) // ∀ a ∈ A, σ a = a} => z.val) h
      exact Subtype.ext h'
    exact (Nat.card_le_card_of_injective φ hφ).trans hle
  have hker : Nat.card ρ.ker ≤ 2 := by
    let R : Subgroup G := ρ.ker.map Q.subtype
    have hRle : R ≤ centralizer (M : Set G) := by
      rintro _ ⟨q, hq, rfl⟩
      exact mem_centralizer_of_barRho_eq_one hperf hQN hq
    have hRp : IsPGroup 2 R :=
      (hQ.to_subgroup ρ.ker).of_equiv (Subgroup.equivMapOfInjective ρ.ker Q.subtype Q.subtype_injective)
    have := hC2 R hRle hRp
    have hc : Nat.card R = Nat.card ρ.ker := Subgroup.card_map_of_injective Q.subtype_injective
    omega
  have h1 := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker] at h1
  calc Nat.card Q = Nat.card ρ.ker * Nat.card ρ.range := h1.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul hker hrange
    _ = 4 := by norm_num

theorem false_of_sylow_trick_core (hKG : KGHSA8) {M K J : Subgroup G}
    (hM : CFSG.Open.standardComponentIsStandard M) (hcat : Catalog (M ⧸ center M))
    (hsimple : IsSimpleGroup (M ⧸ center M)) (hcard : Nat.card (M ⧸ center M) = 44352000)
    (hC : ∀ S : Sylow 2 (centralizer (M : Set G)), Nat.card S = 2)
    (hKM : K ≤ M) (hK : Nonempty (↥K ≃* alternatingGroup (Fin 8)))
    (hJ : J ≤ centralizer (K : Set G)) (hJ8 : Nonempty (↥J ≃* alternatingGroup (Fin 8))) :
    False := by
  have hperf : commutator ↥M = ⊤ := hM.1.1
  have hC2 := fun R : Subgroup G => card_le_two_of_le_centralizer hC (R := R)
  have hCK : centralizer (M : Set G) ≤ centralizer (K : Set G) :=
    Subgroup.centralizer_le (fun k hk => hKM hk)
  have heven : Even (Nat.card (centralizer (M : Set G))) := hM.2.1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (M : Set G)) 2
    (even_iff_two_dvd.mp heven)
  have hxo : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxY : (x : G) ∈ centralizer (K : Set G) := hCK x.2
  let xH : centralizer (K : Set G) := ⟨x, hxY⟩
  have hxH : orderOf xH = 2 := by rw [Subgroup.orderOf_mk]; exact hxo
  have hQ : ∀ Q : Subgroup (centralizer (K : Set G)), Q ≤ centralizer ({xH} : Set _) →
      IsPGroup 2 Q → Nat.card Q ≤ 4 := by
    intro Q hQc hQp
    let QG : Subgroup G := Q.map (centralizer (K : Set G)).subtype
    have hcomm : ∀ g ∈ QG, g * x = x * g := by
      rintro _ ⟨y, hy, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp (hQc hy) xH (Set.mem_singleton _)
      exact congrArg Subtype.val this.symm
    have hQN : QG ≤ normalizer (M : Set G) := fun g hg =>
      mem_normalizer_of_commute_sylow hM x.2 hxo (hcomm g hg)
    have hQK : QG ≤ centralizer (K : Set G) := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have hQGp : IsPGroup 2 QG := hQp.of_equiv
      (Subgroup.equivMapOfInjective Q (centralizer (K : Set G)).subtype
        (centralizer (K : Set G)).subtype_injective)
    have h4 := card_le_four_of_two_subgroup hKG hperf hcat hsimple hcard hKM hK (hC2 · · ·) hQN hQK hQGp
    have hc : Nat.card QG = Nat.card Q :=
      Subgroup.card_map_of_injective (centralizer (K : Set G)).subtype_injective
    omega
  obtain ⟨E, hEJ, hE16, hEsq⟩ := exists_elemAbelian_sixteen_of_equiv_alt8 hJ8.some
  have hEY : E ≤ centralizer (K : Set G) := hEJ.trans hJ
  have h4 := card_le_four_of_centralizer_two_subgroups hxH hQ (E.subgroupOf (centralizer (K : Set G)))
    (by
      intro e he
      apply Subtype.ext
      exact hEsq _ (Subgroup.mem_subgroupOf.mp he))
  have hcE : Nat.card (E.subgroupOf (centralizer (K : Set G))) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv
  omega

section HS


theorem false_of_sylow_trick (hKG : KGHSA8) {M K J : Subgroup G}
    (hM : CFSG.Open.standardComponentIsStandard M)
    (hHS : IsSporadic (↥M ⧸ center ↥M) .HS)
    (hC : ∀ S : Sylow 2 (centralizer (M : Set G)), Nat.card S = 2)
    (hKM : K ≤ M) (hK : Nonempty (↥K ≃* alternatingGroup (Fin 8)))
    (hJ : J ≤ centralizer (K : Set G)) (hJ8 : Nonempty (↥J ≃* alternatingGroup (Fin 8))) :
    False := by
  obtain ⟨e₀⟩ := hHS
  have e : (↥M ⧸ center ↥M) ≃* NativeSporadic.HS := e₀
  have hs : IsSimpleGroup NativeSporadic.HS := CFSG.Sporadic.HS.isSimpleGroup_HS
  have hsimple : IsSimpleGroup (↥M ⧸ center ↥M) :=
    @MulEquiv.isSimpleGroup _ _ NativeSporadic.HS _ hs e
  have hcard : Nat.card (↥M ⧸ center ↥M) = 44352000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS
  exact false_of_sylow_trick_core hKG hM (Or.inr (Or.inr (Or.inr (Or.inr ⟨.HS, ⟨e₀⟩⟩))))
    hsimple hcard hC hKM hK hJ hJ8

end HS

end Key

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
