module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTType

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def FixerBound (Q : Type) [Group Q] : Prop :=
  ∀ A : Subgroup Q, Nonempty (↥A ≃* alternatingGroup (Fin 8)) →
    Nat.card {σ : MulAut Q // ∀ a ∈ A, σ a = a} ≤ 2

theorem fixerBound_of_a10 (hKG : KGA10A8) {Q : Type} [Group Q] [Finite Q]
    (e : Nonempty (Q ≃* alternatingGroup (Fin 10))) : FixerBound Q :=
  fun A hA => hKG Q e A hA

section Key

variable {G : Type} [Group G] [Finite G]

theorem card_le_four_of_two_subgroup_gen {M K : Subgroup G}
    (hfix : FixerBound (M ⧸ center M)) (hperf : commutator ↥M = ⊤)
    (hKM : K ≤ M) (hK : Nonempty (↥K ≃* alternatingGroup (Fin 8)))
    (hC2 : ∀ R : Subgroup G, R ≤ centralizer (M : Set G) → IsPGroup 2 R → Nat.card R ≤ 2)
    {Q : Subgroup G} (hQN : Q ≤ normalizer (M : Set G)) (hQK : Q ≤ centralizer (K : Set G))
    (hQ : IsPGroup 2 Q) : Nat.card Q ≤ 4 := by
  obtain ⟨A, hA, hAK⟩ := exists_alt8_image hKM hK
  set ρ := barRho M Q hQN with hρ
  have hfixed : ∀ s : ρ.range, ∀ a ∈ A, (s : MulAut (M ⧸ center M)) a = a := by
    rintro ⟨_, q, rfl⟩ a ha
    obtain ⟨k, hk, rfl⟩ := hAK a ha
    exact barRho_apply_of_mem_centralizer M Q K hQN hQK q k hk
  have hrange : Nat.card ρ.range ≤ 2 := by
    have hle := hfix A hA
    let φ : ρ.range → {σ : MulAut (M ⧸ center M) // ∀ a ∈ A, σ a = a} :=
      fun s => ⟨s, hfixed s⟩
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
      (hQ.to_subgroup ρ.ker).of_equiv
        (Subgroup.equivMapOfInjective ρ.ker Q.subtype Q.subtype_injective)
    have := hC2 R hRle hRp
    have hc : Nat.card R = Nat.card ρ.ker := Subgroup.card_map_of_injective Q.subtype_injective
    omega
  have h1 := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker] at h1
  calc Nat.card Q = Nat.card ρ.ker * Nat.card ρ.range := h1.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul hker hrange
    _ = 4 := by norm_num

theorem false_of_sylow_trick_gen {M K J : Subgroup G}
    (hM : CFSG.Open.standardComponentIsStandard M) (hfix : FixerBound (M ⧸ center M))
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
    have h4 := card_le_four_of_two_subgroup_gen hfix hperf hKM hK (hC2 · · ·) hQN hQK hQGp
    have hc : Nat.card QG = Nat.card Q :=
      Subgroup.card_map_of_injective (centralizer (K : Set G)).subtype_injective
    omega
  obtain ⟨E, hEJ, hE16, hEsq⟩ := exists_elemAbelian_sixteen_of_equiv_alt8 hJ8.some
  have hEY : E ≤ centralizer (K : Set G) := hEJ.trans hJ
  have h4 := card_le_four_of_centralizer_two_subgroups hxH hQ
    (E.subgroupOf (centralizer (K : Set G)))
    (by
      intro e he
      apply Subtype.ext
      exact hEsq _ (Subgroup.mem_subgroupOf.mp he))
  have hcE : Nat.card (E.subgroupOf (centralizer (K : Set G))) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv
  omega

theorem false_of_sylow_trick_a10 (hKG : KGA10A8) {M K J : Subgroup G}
    (hM : CFSG.Open.standardComponentIsStandard M)
    (hA10 : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 10)))
    (hC : ∀ S : Sylow 2 (centralizer (M : Set G)), Nat.card S = 2)
    (hKM : K ≤ M) (hK : Nonempty (↥K ≃* alternatingGroup (Fin 8)))
    (hJ : J ≤ centralizer (K : Set G)) (hJ8 : Nonempty (↥J ≃* alternatingGroup (Fin 8))) :
    False :=
  false_of_sylow_trick_gen hM (fixerBound_of_a10 hKG hA10) hC hKM hK hJ hJ8

end Key

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
