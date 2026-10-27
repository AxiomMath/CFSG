module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentOrd
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Ch1
open Equiv Equiv.Perm

section Involutions

variable {n : ℕ}

theorem involution_cycleType {σ : Perm (Fin n)} (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ σ.cycleType = Multiset.replicate k 2 := by
  have hsq : σ ^ 2 = 1 := by rw [sq]; exact h2
  have hord : orderOf σ = 2 := orderOf_eq_prime hsq h1
  refine ⟨Multiset.card σ.cycleType, ?_, Multiset.eq_replicate.mpr ⟨rfl, fun a ha => ?_⟩⟩
  · rw [Nat.one_le_iff_ne_zero]
    intro h0
    apply h1
    rw [← Equiv.Perm.cycleType_eq_zero]
    exact Multiset.card_eq_zero.mp h0
  · have h2le := Equiv.Perm.two_le_of_mem_cycleType ha
    have hdvd : a ∣ 2 := hord ▸ Equiv.Perm.dvd_of_mem_cycleType ha
    exact le_antisymm (Nat.le_of_dvd two_pos hdvd) h2le

theorem two_mul_le_of_cycleType {σ : Perm (Fin n)} {k : ℕ}
    (hc : σ.cycleType = Multiset.replicate k 2) : 2 * k ≤ n := by
  have := Equiv.Perm.sum_cycleType_le σ
  rw [hc, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at this
  omega

theorem card_centralizer_involution {σ : Perm (Fin n)} {k : ℕ} (hk : 1 ≤ k)
    (hc : σ.cycleType = Multiset.replicate k 2) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) =
      Nat.factorial (n - 2 * k) * 2 ^ k * Nat.factorial k := by
  have hk0 : k ≠ 0 := by omega
  have hset : (Multiset.replicate k 2).toFinset = {2} := by
    ext a
    simp [hk0]
  rw [Equiv.Perm.nat_card_centralizer, hc, hset]
  simp [Multiset.sum_replicate, Multiset.prod_replicate, Multiset.count_replicate_self,
    mul_comm 2 k]

theorem sign_involution {σ : Perm (Fin n)} {k : ℕ} (hc : σ.cycleType = Multiset.replicate k 2) :
    Perm.sign σ = (-1) ^ k := by
  rw [Equiv.Perm.sign_of_cycleType, hc, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul, pow_add, pow_mul]
  simp

theorem two_mul_card_le_of_odd {σ : Perm (Fin n)} (hodd : σ ∉ alternatingGroup (Fin n))
    {B : Subgroup (Perm (Fin n))} (hB : B ≤ Subgroup.centralizer ({σ} : Set (Perm (Fin n))))
    (hBA : B ≤ alternatingGroup (Fin n)) :
    2 * Nat.card B ≤ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) := by
  set C := Subgroup.centralizer ({σ} : Set (Perm (Fin n))) with hC
  have hσC : σ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hne : B.subgroupOf C ≠ ⊤ := by
    intro htop
    have : (⟨σ, hσC⟩ : ↥C) ∈ B.subgroupOf C := by rw [htop]; exact Subgroup.mem_top _
    exact hodd (hBA this)
  have hidx : (B.subgroupOf C).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hidx0 : (B.subgroupOf C).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcard := Subgroup.card_mul_index (B.subgroupOf C)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv] at hcard
  nlinarith [Nat.pos_of_ne_zero hidx0, show 2 ≤ (B.subgroupOf C).index by omega]

end Involutions

section Action

variable {G : Type} [Group G] {X K : Subgroup G} {t : G}

theorem IdentSetting.exists_perm (hs : IdentSetting X K t) {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (φ : (↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin n)) :
    ∃ σ : Perm (Fin n), ∀ y : ↥X,
      (φ (QuotientGroup.mk (hs.conjAut y)) : Perm (Fin n)) =
        σ * (φ (QuotientGroup.mk y) : Perm (Fin n)) * σ⁻¹ := by
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le hn
    (φ.symm.trans (hs.quotAut.trans φ))
  refine ⟨σ, fun y => ?_⟩
  have := hσ (φ (QuotientGroup.mk y))
  simpa [MulEquiv.trans_apply, IdentSetting.quotAut_mk] using this

theorem IdentSetting.perm_sq (hs : IdentSetting X K t) {n : ℕ} (hn : 4 ≤ n)
    (φ : (↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin n)) {σ : Perm (Fin n)}
    (hσ : ∀ y : ↥X, (φ (QuotientGroup.mk (hs.conjAut y)) : Perm (Fin n)) =
      σ * (φ (QuotientGroup.mk y) : Perm (Fin n)) * σ⁻¹) : σ * σ = 1 := by
  have hc := CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
    (α := Fin n) (by simpa using hn)
  have hmem : σ * σ ∈ Subgroup.centralizer (alternatingGroup (Fin n) : Set (Perm (Fin n))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (φ.symm ⟨g, hg⟩)
    have h1 : (φ (QuotientGroup.mk y) : Perm (Fin n)) = g := by rw [hy]; simp
    have h2 := hσ (hs.conjAut y)
    rw [hs.conjAut_conjAut, hσ y, h1] at h2
    calc g * (σ * σ) = (σ * (σ * g * σ⁻¹) * σ⁻¹) * (σ * σ) := by rw [← h2]
      _ = σ * σ * g := by group
  rw [hc, Subgroup.mem_bot] at hmem
  exact hmem

theorem IdentSetting.perm_ne_one (hs : IdentSetting X K t) {n : ℕ}
    (φ : (↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin n)) {σ : Perm (Fin n)}
    (hσ : ∀ y : ↥X, (φ (QuotientGroup.mk (hs.conjAut y)) : Perm (Fin n)) =
      σ * (φ (QuotientGroup.mk y) : Perm (Fin n)) * σ⁻¹) : σ ≠ 1 := by
  intro h1
  refine hs.false_of_comm_central fun y => ?_
  have h2 := hσ y
  rw [h1, inv_one, one_mul, mul_one] at h2
  have hq : (QuotientGroup.mk (hs.conjAut y) : ↥X ⧸ Subgroup.center ↥X) = QuotientGroup.mk y :=
    φ.injective (Subtype.ext h2)
  simpa [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hq

@[expose] def psiOf (X : Subgroup G) {n : ℕ}
    (φ : (↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin n)) {Y : Subgroup G} (hY : Y ≤ X) :
    ↥Y →* Perm (Fin n) :=
  ((alternatingGroup (Fin n)).subtype.comp φ.toMonoidHom).comp
    ((QuotientGroup.mk' (Subgroup.center ↥X)).comp (Subgroup.inclusion hY))

theorem psiOf_apply (X : Subgroup G) {n : ℕ}
    (φ : (↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin n)) {Y : Subgroup G} (hY : Y ≤ X)
    (k : ↥Y) :
    psiOf X φ hY k = (φ (QuotientGroup.mk (Subgroup.inclusion hY k)) : Perm (Fin n)) := rfl

theorem IdentSetting.psiOf_injective_K
    [Finite G] (hs : IdentSetting X K t) (hK : IsKType K)
    {n : ℕ} (φ : (↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin n)) :
    Function.Injective (psiOf X φ hs.K_le) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  rw [psiOf_apply] at hk
  have h1 : φ (QuotientGroup.mk (Subgroup.inclusion hs.K_le k)) = 1 :=
    Subtype.ext (by simpa using hk)
  have h2 : (QuotientGroup.mk (Subgroup.inclusion hs.K_le k) : ↥X ⧸ Subgroup.center ↥X) = 1 := by
    apply φ.injective
    rw [h1, map_one]
  have hz : Subgroup.inclusion hs.K_le k ∈ Subgroup.center ↥X := (QuotientGroup.eq_one_iff _).mp h2
  have hmem : Subgroup.inclusion hs.K_le k ∈ K.subgroupOf X ⊓ Subgroup.center ↥X := ⟨k.2, hz⟩
  rw [hs.inf_center hK, Subgroup.mem_bot] at hmem
  exact Subgroup.inclusion_injective hs.K_le (by rw [hmem, map_one])

theorem psiOf_injective_of_center_eq_bot (hc : Subgroup.center ↥X = ⊥) {n : ℕ}
    (φ : (↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin n)) {Y : Subgroup G} (hY : Y ≤ X) :
    Function.Injective (psiOf X φ hY) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  rw [psiOf_apply] at hk
  have h1 : φ (QuotientGroup.mk (Subgroup.inclusion hY k)) = 1 :=
    Subtype.ext (by simpa using hk)
  have h2 : (QuotientGroup.mk (Subgroup.inclusion hY k) : ↥X ⧸ Subgroup.center ↥X) = 1 := by
    apply φ.injective
    rw [h1, map_one]
  have hz : Subgroup.inclusion hY k ∈ Subgroup.center ↥X := (QuotientGroup.eq_one_iff _).mp h2
  rw [hc, Subgroup.mem_bot] at hz
  exact Subgroup.inclusion_injective hY (by rw [hz, map_one])

theorem IdentSetting.psiOf_comm (hs : IdentSetting X K t) {n : ℕ}
    (φ : (↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin n)) {σ : Perm (Fin n)}
    (hσ : ∀ y : ↥X, (φ (QuotientGroup.mk (hs.conjAut y)) : Perm (Fin n)) =
      σ * (φ (QuotientGroup.mk y) : Perm (Fin n)) * σ⁻¹) {Y : Subgroup G} (hY : Y ≤ X)
    (hYt : Y ≤ Subgroup.centralizer ({t} : Set G)) (k : ↥Y) :
    σ * psiOf X φ hY k = psiOf X φ hY k * σ := by
  have h1 := hσ (Subgroup.inclusion hY k)
  rw [hs.conjAut_of_mem_cent (hYt k.2)] at h1
  rw [psiOf_apply]
  calc σ * (φ (QuotientGroup.mk (Subgroup.inclusion hY k)) : Perm (Fin n))
      = (σ * (φ (QuotientGroup.mk (Subgroup.inclusion hY k)) : Perm (Fin n)) * σ⁻¹) * σ := by
        group
    _ = (φ (QuotientGroup.mk (Subgroup.inclusion hY k)) : Perm (Fin n)) * σ := by rw [← h1]

theorem IdentSetting.psiOf_range_le (hs : IdentSetting X K t) {n : ℕ}
    (φ : (↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin n)) {σ : Perm (Fin n)}
    (hσ : ∀ y : ↥X, (φ (QuotientGroup.mk (hs.conjAut y)) : Perm (Fin n)) =
      σ * (φ (QuotientGroup.mk y) : Perm (Fin n)) * σ⁻¹) {Y : Subgroup G} (hY : Y ≤ X)
    (hYt : Y ≤ Subgroup.centralizer ({t} : Set G)) :
    (psiOf X φ hY).range ≤ Subgroup.centralizer ({σ} : Set (Perm (Fin n))) ∧
      (psiOf X φ hY).range ≤ alternatingGroup (Fin n) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨k, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hs.psiOf_comm φ hσ hY hYt k).symm
  · rintro _ ⟨k, rfl⟩
    exact (φ (QuotientGroup.mk (Subgroup.inclusion hY k))).2

theorem IdentSetting.card_dvd_cent (hs : IdentSetting X K t) {n : ℕ}
    (φ : (↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin n)) {σ : Perm (Fin n)}
    (hσ : ∀ y : ↥X, (φ (QuotientGroup.mk (hs.conjAut y)) : Perm (Fin n)) =
      σ * (φ (QuotientGroup.mk y) : Perm (Fin n)) * σ⁻¹) {Y : Subgroup G} (hY : Y ≤ X)
    (hYt : Y ≤ Subgroup.centralizer ({t} : Set G)) (hinj : Function.Injective (psiOf X φ hY)) :
    Nat.card ↥Y ∣ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) := by
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Subgroup.card_dvd_of_le (hs.psiOf_range_le φ hσ hY hYt).1

theorem IdentSetting.two_mul_card_le (hs : IdentSetting X K t) {n : ℕ}
    (φ : (↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin n)) {σ : Perm (Fin n)}
    (hσ : ∀ y : ↥X, (φ (QuotientGroup.mk (hs.conjAut y)) : Perm (Fin n)) =
      σ * (φ (QuotientGroup.mk y) : Perm (Fin n)) * σ⁻¹)
    (hodd : σ ∉ alternatingGroup (Fin n)) {Y : Subgroup G} (hY : Y ≤ X)
    (hYt : Y ≤ Subgroup.centralizer ({t} : Set G)) (hinj : Function.Injective (psiOf X φ hY)) :
    2 * Nat.card ↥Y ≤ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) := by
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact two_mul_card_le_of_odd hodd (hs.psiOf_range_le φ hσ hY hYt).1
    (hs.psiOf_range_le φ hσ hY hYt).2

end Action

section Alt7

open Ident

theorem tabIdentFor_alt7
    : TabIdentFor @FamAlt7 := by
  intro G _ _ X K t hs hX
  exfalso
  obtain ⟨⟨φ⟩, -⟩ := hX
  obtain ⟨σ, hσ⟩ := hs.exists_perm (n := 7) (Or.inr le_rfl) φ
  have hsq : σ * σ = 1 := hs.perm_sq (by norm_num) φ hσ
  have hne : σ ≠ 1 := hs.perm_ne_one φ hσ
  obtain ⟨k, hk1, hc⟩ := involution_cycleType hsq hne
  have hk2 : 2 * k ≤ 7 := two_mul_le_of_cycleType hc
  have hcard := card_centralizer_involution hk1 hc
  have h168 := isKType_card_ge hs.ktype
  have hinj := hs.psiOf_injective_K hs.ktype φ
  have hKt : K ≤ Subgroup.centralizer ({t} : Set G) := hs.K_le_cent
  have hdvd := hs.card_dvd_cent φ hσ hs.K_le hKt hinj
  have hle := Nat.le_of_dvd Nat.card_pos hdvd
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · have hodd : σ ∉ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup, sign_involution hc]
      decide
    have := hs.two_mul_card_le φ hσ hodd hs.K_le hKt hinj
    rw [hcard] at this
    norm_num [Nat.factorial] at this
    omega
  · rw [hcard] at hle
    norm_num [Nat.factorial] at hle
    omega
  · rw [hcard] at hle
    norm_num [Nat.factorial] at hle
    omega

end Alt7

end CFSG.QuasithinUnique.Id2519
