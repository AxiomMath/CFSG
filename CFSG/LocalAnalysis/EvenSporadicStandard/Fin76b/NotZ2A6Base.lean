
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaTransfer

@[expose] public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Schreier (j2P j2PermEquiv j3P j3PermEquiv)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {z t : G} {T₀ : Subgroup G}

theorem centralizer_quotient_of_innerConfig (h : InnerConfig G A z t T₀) {β : G}
    {K : Subgroup G} (hK : K = centralizer ({β} : Set G))
    (hD : Nonempty (↥(A ⊓ K) ⧸ fusionOddCore ↥(A ⊓ K) ≃* alternatingGroup (Fin 6)))
    (hO : fusionOddCoreOf (A ⊓ K) ≤ zpowers β) {zK : ↥K} (hzK : (zK : G) = z) :
    Nonempty (centralizer ({(QuotientGroup.mk zK : ↥K ⧸ fusionOddCore ↥K)} :
      Set (↥K ⧸ fusionOddCore ↥K)) ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 6)) := by
  set DK : Subgroup K := (A ⊓ K).subgroupOf K with hDK
  have hcommβ : ∀ x : K, (x : G) * β = β * x := fun x =>
    mem_centralizer_singleton_iff.1 ((congrArg (fun S : Subgroup G => (x : G) ∈ S) hK).mp x.2)
  have hzK2 : orderOf zK = 2 := by
    rw [← Subgroup.orderOf_coe, hzK]
    exact h.z_order
  have hzβ : z * β = β * z := by
    rw [← hzK]
    exact hcommβ zK
  have hcent : centralizer ({zK} : Set K) = zpowers zK ⊔ DK := by
    refine le_antisymm (fun x hx => ?_) (sup_le ?_ ?_)
    · have hx1 : (x : G) * z = z * x := by
        have := mem_centralizer_singleton_iff.1 hx
        rw [← hzK]
        exact congrArg Subtype.val this
      have hx2 : (x : G) ∈ A ⊔ zpowers z := by
        rw [← h.cent_eq]
        exact mem_centralizer_singleton_iff.2 hx1
      obtain ⟨a, ha, c, hc, hxac⟩ := exists_mul_of_mem_sup_of_le_centralizer
        (zpowers_le.2 h.z_cent) hx2
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
      have hcK : z ^ k ∈ K := by
        rw [hK, mem_centralizer_singleton_iff]
        exact (Commute.zpow_left (show Commute z β from hzβ) k).eq
      have haK : a ∈ K := by
        have : a = (x : G) * (z ^ k)⁻¹ := by rw [hxac]; group
        rw [this]
        exact mul_mem x.2 (inv_mem hcK)
      have hxe : x = (⟨a, haK⟩ : K) * zK ^ k := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_zpow, hzK]
        exact hxac
      rw [hxe]
      exact mul_mem (mem_sup_right (mem_subgroupOf.2 ⟨ha, haK⟩))
        (mem_sup_left (zpow_mem (mem_zpowers zK) k))
    · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
    · intro d hd
      rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hzK]
      exact h.z_comm_of_mem_A (mem_subgroupOf.1 hd).1
  have hdisj : Disjoint (zpowers zK) DK := by
    rw [Subgroup.disjoint_def]
    intro x hxz hxD
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxz
    have h1 : z ^ k ∈ A := by
      have := (mem_subgroupOf.1 hxD).1
      simpa [hzK] using this
    have h2 : z ^ k ∈ A ⊓ zpowers z := ⟨h1, mem_zpowers_iff.2 ⟨k, rfl⟩⟩
    rw [h.disjoint.eq_bot, mem_bot] at h2
    apply Subtype.ext
    simpa [hzK] using h2
  let e : DK ≃* ↥(A ⊓ K) := Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ K ≤ K)
  have hmap : (fusionOddCore DK).map e.toMonoidHom = fusionOddCore ↥(A ⊓ K) :=
    map_fusionOddCore_mulEquiv e
  obtain ⟨eD⟩ := hD
  have hD' : DK ⧸ fusionOddCore DK ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr (fusionOddCore DK) (fusionOddCore ↥(A ⊓ K)) e hmap).trans eD
  have hDc : fusionOddCoreOf DK ≤ center K := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_center_iff]
    intro g
    have h1 : e y ∈ fusionOddCore ↥(A ⊓ K) := hmap ▸ ⟨y, hy, rfl⟩
    have h2 : ((e y : ↥(A ⊓ K)) : G) ∈ zpowers β := hO ⟨e y, h1, rfl⟩
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hy' : ((y : K) : G) = β ^ j := by rw [hj]; rfl
    show (g : G) * ((y : K) : G) = ((y : K) : G) * g
    rw [hy']
    exact (Commute.zpow_right (show Commute (g : G) β from hcommβ g) j).eq
  exact centralizer_quotient_equiv hzK2 hcent hdisj hDc hD'

theorem not_z2a6_of_betaData (h : InnerConfig G A z t T₀) {β y : G}
    (hD : Nonempty (↥(A ⊓ centralizer ({β} : Set G)) ⧸
      fusionOddCore ↥(A ⊓ centralizer ({β} : Set G)) ≃* alternatingGroup (Fin 6)))
    (hO : fusionOddCoreOf (A ⊓ centralizer ({β} : Set G)) ≤ zpowers β)
    (hβA : β ∈ A) (hβt : β * t = t * β) (hyβ : y * β = β * y) (hyz : y * z * y⁻¹ = z * t) :
    ¬ Nonempty (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G)) ≃*
      Multiplicative (ZMod 2) × alternatingGroup (Fin 6)) := by
  rintro ⟨e'⟩
  set K : Subgroup G := centralizer ({β} : Set G) with hK
  have hz : z ∈ K := mem_centralizer_singleton_iff.2 (h.z_comm_of_mem_A hβA).symm
  have ht : t ∈ K := mem_centralizer_singleton_iff.2 hβt.symm
  have hy : y ∈ K := mem_centralizer_singleton_iff.2 hyβ
  let zK : ↥K := ⟨z, hz⟩
  let tK : ↥K := ⟨t, ht⟩
  let yK : ↥K := ⟨y, hy⟩
  obtain ⟨c⟩ := centralizer_quotient_of_innerConfig h hK hD hO (zK := zK) rfl
  have hcard : Nat.card (centralizer ({(QuotientGroup.mk zK : ↥K ⧸ fusionOddCore ↥K)} :
      Set (↥K ⧸ fusionOddCore ↥K))) = Nat.card (↥K ⧸ fusionOddCore ↥K) := by
    rw [Nat.card_congr c.toEquiv, Nat.card_congr e'.toEquiv]
  have htop := Subgroup.eq_top_of_card_eq _ hcard
  have hcen : ∀ w : ↥K ⧸ fusionOddCore ↥K,
      w * QuotientGroup.mk zK = QuotientGroup.mk zK * w := fun w =>
    mem_centralizer_singleton_iff.1 (htop ▸ mem_top w)
  have hyzK : yK * zK * yK⁻¹ = zK * tK := Subtype.ext hyz
  have h1 : (QuotientGroup.mk zK : ↥K ⧸ fusionOddCore ↥K) =
      QuotientGroup.mk zK * QuotientGroup.mk tK := by
    have h2 := congrArg (QuotientGroup.mk (s := fusionOddCore ↥K)) hyzK
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcen,
      mul_inv_cancel_right] at h2
    rw [← QuotientGroup.mk_mul]
    exact h2
  have h3 : (QuotientGroup.mk tK : ↥K ⧸ fusionOddCore ↥K) = 1 := by
    have h4 : (QuotientGroup.mk zK : ↥K ⧸ fusionOddCore ↥K) * 1 =
        QuotientGroup.mk zK * QuotientGroup.mk tK := by rw [mul_one]; exact h1
    exact (mul_left_cancel h4).symm
  have h5 : tK ∈ fusionOddCore ↥K := (QuotientGroup.eq_one_iff tK).1 h3
  have h6 : orderOf tK ∣ Nat.card (fusionOddCore ↥K) := Subgroup.orderOf_dvd_natCard _ h5
  have h7 : orderOf tK = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact h.t_order
  rw [h7] at h6
  exact (Nat.not_even_iff_odd.2 (odd_natCard_fusionOddCore ↥K)) (even_iff_two_dvd.2 h6)

theorem betaData_of_model {L : Subgroup G} (h : InnerConfig G L z t T₀) {X : Type*} [Group X]
    [Finite X] (φ : X ≃* L) (hB : BetaDataSq X) (hR : RootFactsClass X) {β : G} (hβL : β ∈ L)
    (hβt : β * t = t * β) (hβ3 : orderOf β = 3) :
    Nonempty (↥(L ⊓ centralizer ({β} : Set G)) ⧸
      fusionOddCore ↥(L ⊓ centralizer ({β} : Set G)) ≃* alternatingGroup (Fin 6)) ∧
      fusionOddCoreOf (L ⊓ centralizer ({β} : Set G)) ≤ zpowers β := by
  let tL : ↥L := ⟨t, h.t_mem_A⟩
  have htL2 : orderOf tL = 2 := by rw [← Subgroup.orderOf_coe]; exact h.t_order
  obtain ⟨g, hgA, hg⟩ := h.t_square
  have hsq : ∃ g' : X, g' * g' = φ.symm tL :=
    ⟨φ.symm ⟨g, hgA⟩, by rw [← map_mul]; congr 1; exact Subtype.ext hg⟩
  have ht2 : orderOf (φ.symm tL) = 2 := by rw [MulEquiv.orderOf_eq]; exact htL2
  obtain ⟨β₀, hcomm, hβ₀⟩ := hB (φ.symm tL) ht2 hsq
  let βL : ↥L := ⟨β, hβL⟩
  have hβ'3 : orderOf (φ.symm βL) = 3 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hβ3
  have hβ't : φ.symm βL * φ.symm tL = φ.symm tL * φ.symm βL := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hβt
  have hF : BetaFor X (φ.symm βL) :=
    betaFor_of_order_three (hR _ ht2 hsq).card_cent hcomm.symm hβ₀ hβ't hβ'3
  obtain ⟨-, hD, hO⟩ := hF.transport φ
  have hβeq : ((φ (φ.symm βL) : L) : G) = β := by simp [βL]
  have key : ∀ x y : G, x = y →
      Nonempty (↥(L ⊓ centralizer ({x} : Set G)) ⧸
        fusionOddCore ↥(L ⊓ centralizer ({x} : Set G)) ≃* alternatingGroup (Fin 6)) ∧
        fusionOddCoreOf (L ⊓ centralizer ({x} : Set G)) ≤ zpowers x →
      Nonempty (↥(L ⊓ centralizer ({y} : Set G)) ⧸
        fusionOddCore ↥(L ⊓ centralizer ({y} : Set G)) ≃* alternatingGroup (Fin 6)) ∧
        fusionOddCoreOf (L ⊓ centralizer ({y} : Set G)) ≤ zpowers y := by
    rintro x y rfl hx
    exact hx
  exact key _ _ hβeq ⟨hD, hO⟩

end CFSG.EvenSporadicStandard.Fin76b
