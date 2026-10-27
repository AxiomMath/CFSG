module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Numeric
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.FixedPoint
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def fixClass (L V : Subgroup G) (y : G) : Subgroup G where
  carrier := {l | l ∈ L ∧ l * y * l⁻¹ * y⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G)}
  one_mem' := ⟨L.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haL, ha⟩ ⟨hbL, hb⟩
    refine ⟨L.mul_mem haL hbL, ?_⟩
    have hfix : a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ = b * y * b⁻¹ * y⁻¹ := by
      have := (Subgroup.mem_centralizer_iff.mp hb.2) a haL
      calc a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ = (b * y * b⁻¹ * y⁻¹) * a * a⁻¹ := by rw [this]
        _ = b * y * b⁻¹ * y⁻¹ := by group
    have e : a * b * y * (a * b)⁻¹ * y⁻¹ =
        (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
    rw [e, hfix]
    exact Subgroup.mul_mem _ hb ha
  inv_mem' := by
    rintro a ⟨haL, ha⟩
    refine ⟨L.inv_mem haL, ?_⟩
    have hfix : a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a = (a * y * a⁻¹ * y⁻¹)⁻¹ := by
      have := (Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ ha).2) a⁻¹ (L.inv_mem haL)
      calc a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a = ((a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹) * a := by
            rw [← this]
        _ = (a * y * a⁻¹ * y⁻¹)⁻¹ := by group
    have e : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a := by group
    rw [e, hfix]
    exact Subgroup.inv_mem _ ha

theorem conj_comm_mem {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {y l : G}
    (hy : y ∈ V) (hl : l ∈ L) : l * y * l⁻¹ * y⁻¹ ∈ V :=
  V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLV hl) y).mp hy) (V.inv_mem hy)

theorem index_fixClass_le [Finite G] {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    {y : G} (hy : y ∈ V) :
    ((fixClass L V y).subgroupOf L).index ≤
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex
        (⁅V, L⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G))) := by
  set C : Subgroup G := V ⊓ Subgroup.centralizer (L : Set G) with hC
  set K : Subgroup G := ⁅V, L⁆ ⊔ C with hK
  set H' := (fixClass L V y).subgroupOf L with hH'
  have hCfix : ∀ c ∈ C, ∀ l ∈ L, l * c * l⁻¹ = c := by
    intro c hc l hl
    have := (Subgroup.mem_centralizer_iff.mp hc.2) l hl
    calc l * c * l⁻¹ = (c * l) * l⁻¹ := by rw [this]
      _ = c := by group
  have hmemX : ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ (⁅V, L⁆ : Subgroup G) := fun l hl => by
    have e : l * y * l⁻¹ * y⁻¹ = (y * l * y⁻¹ * l⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hy hl)
  have hmemK : ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ K := fun l hl => Subgroup.mem_sup_left (hmemX l hl)
  have hid : ∀ a u : G, a * u * y * (a * u)⁻¹ * y⁻¹ =
      (a * (u * y * u⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) := by intro a u; group
  have hVmem : ∀ a ∈ L, ∀ u ∈ L, a * (u * y * u⁻¹ * y⁻¹) * a⁻¹ ∈ V := by
    intro a ha u hu
    exact (Subgroup.mem_normalizer_iff.mp (hLV ha) _).mp (conj_comm_mem hLV hy hu)
  have hcmp : ∀ a ∈ L, ∀ u ∈ L,
      (a * y * a⁻¹ * y⁻¹)⁻¹ * (a * u * y * (a * u)⁻¹ * y⁻¹) ∈ C ↔
        u * y * u⁻¹ * y⁻¹ ∈ C := by
    intro a ha u hu
    have hxa : a * y * a⁻¹ * y⁻¹ ∈ V := conj_comm_mem hLV hy ha
    have hv := hVmem a ha u hu
    have e : (a * y * a⁻¹ * y⁻¹)⁻¹ * (a * u * y * (a * u)⁻¹ * y⁻¹) =
        a * (u * y * u⁻¹ * y⁻¹) * a⁻¹ := by
      rw [hid]
      have hcomm := hVc _ hxa _ hv
      calc (a * y * a⁻¹ * y⁻¹)⁻¹ * (a * (u * y * u⁻¹ * y⁻¹) * a⁻¹ * (a * y * a⁻¹ * y⁻¹))
          = (a * y * a⁻¹ * y⁻¹)⁻¹ * ((a * y * a⁻¹ * y⁻¹) *
              (a * (u * y * u⁻¹ * y⁻¹) * a⁻¹)) := by rw [← hcomm]
        _ = a * (u * y * u⁻¹ * y⁻¹) * a⁻¹ := by group
    rw [e]
    constructor
    · intro hc
      have := hCfix _ hc a⁻¹ (L.inv_mem ha)
      have h2 : a⁻¹ * (a * (u * y * u⁻¹ * y⁻¹) * a⁻¹) * a⁻¹⁻¹ = u * y * u⁻¹ * y⁻¹ := by group
      rw [h2] at this
      rw [this]
      exact hc
    · intro hc
      rw [hCfix _ hc a ha]
      exact hc
  let F : L ⧸ H' → ↥K ⧸ C.subgroupOf K :=
    Quotient.lift (fun l : L => (QuotientGroup.mk (⟨(l : G) * y * (l : G)⁻¹ * y⁻¹,
      hmemK l l.2⟩ : ↥K) : ↥K ⧸ C.subgroupOf K))
      (fun a b hab => by
        have hab' : (a : L)⁻¹ * b ∈ H' := QuotientGroup.leftRel_apply.mp hab
        have h1 : ((a : G)⁻¹ * (b : G)) ∈ fixClass L V y := hab'
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        have hau : (a : G) * ((a : G)⁻¹ * (b : G)) = b := by group
        have := (hcmp (a : G) a.2 ((a : G)⁻¹ * (b : G))
          (L.mul_mem (L.inv_mem a.2) b.2)).mpr h1.2
        rw [hau] at this
        simpa using this)
  have hF : Function.Injective F := by
    intro p q hpq
    induction p using Quotient.inductionOn with
    | _ a =>
    induction q using Quotient.inductionOn with
    | _ b =>
    have h := QuotientGroup.eq.mp hpq
    rw [Subgroup.mem_subgroupOf] at h
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    show ((a : G)⁻¹ * (b : G)) ∈ fixClass L V y
    refine ⟨(L.mul_mem (L.inv_mem a.2) b.2), ?_⟩
    have hau : (a : G) * ((a : G)⁻¹ * (b : G)) = b := by group
    have h' := (hcmp (a : G) a.2 ((a : G)⁻¹ * (b : G))
      (L.mul_mem (L.inv_mem a.2) b.2)).mp (by rw [hau]; simpa using h)
    exact h'
  have := Nat.card_le_card_of_injective F hF
  rw [Subgroup.relIndex, Subgroup.index]
  exact this

theorem three_dvd_card_inf_centralizer_of_relIndex_bound [Finite G] {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {y : G} (hy : y ∈ V) {n : ℕ}
    (hn : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex
      (⁅V, L⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G))) ≤ n)
    (hb : ∀ Y : Subgroup G, Y ≤ L → ¬ 3 ∣ Nat.card Y → n * Nat.card Y < Nat.card L) :
    3 ∣ Nat.card (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  set H := fixClass L V y with hH
  have hHL : H ≤ L := fun l hl => hl.1
  by_cases h3 : 3 ∣ Nat.card H
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hgord : orderOf (g : G) = 3 ^ (0 + 1) := by
      rw [Subgroup.orderOf_coe, hg]; norm_num
    exact three_dvd_card_inf_centralizer_of_comm_mem_centralizer hLV hV2 hy (hHL g.2)
      (k := 0) hgord g.2.2.2
  · have hlt := hb H hHL h3
    have hidx := (index_fixClass_le hLV hVc hy).trans hn
    have hcard := Subgroup.index_mul_card (H.subgroupOf L)
    have hH' : Nat.card (H.subgroupOf L) = Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
    rw [hH'] at hcard
    have : (H.subgroupOf L).index * Nat.card H ≤ n * Nat.card H := Nat.mul_le_mul_right _ hidx
    omega

theorem three_dvd_card_inf_centralizer_of_alt_six [Finite G] {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {y : G} (hy : y ∈ V)
    (F : ↥L →* alternatingGroup (Fin 6)) (hF : Function.Surjective F)
    (hn : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex
      (⁅V, L⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G))) ≤ 16) :
    3 ∣ Nat.card (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  refine three_dvd_card_inf_centralizer_of_relIndex_bound hLV hV2 hVc hy hn fun Y hYL hY3 => ?_
  have h := mul_card_lt_card_of_surjective F hF (c := 10) (n := 16)
    (fun H hH => card_le_of_not_three_dvd_alt_six H hH)
    (by rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; decide)
    (Y.subgroupOf L)
    (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv])
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv] at h

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
