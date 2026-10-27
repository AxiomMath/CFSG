module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PKLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PKSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PKType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PKGen

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sec5pk_pocket {L K R K' : Subgroup G} {z : G}
    (hK' : K' = (K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G))
    (hK : Sl23PocketIn L z K) (hOc : ∀ o ∈ oddCoreIn L, ∀ l ∈ L, l * o * l⁻¹ = o)
    (hOK : oddCoreIn K ≤ oddCoreIn L) (hO3 : IsPGroup 3 (oddCoreIn L))
    (hR2 : IsPGroup 2 R) (hRz : ∀ x ∈ R, x * z = z * x)
    (hRN : R ≤ normalizer (L : Set G)) (hRQ : ∀ x ∈ R, ∀ q ∈ twoCoreIn K, x * q = q * x)
    (hQ : Nonempty (↥(twoCoreIn K) ≃* QuaternionGroup 2))
    (hFF4 : ∀ x ∈ R, ∀ n ∈ twoRes (L ⊓ centralizer ({z} : Set G)),
      x * n * x⁻¹ * n⁻¹ ∈ oddCoreIn L) :
    Sl23PocketIn L z K' ∧ twoCoreIn K' = twoCoreIn K ∧
      oddCoreIn K' = oddCoreIn L ⊓ centralizer (R : Set G) ∧
      (∀ k ∈ K', Odd (orderOf k) → ∃ n : ℕ, orderOf k = 3 ^ n) ∧ twoRes K' = K' := by
  obtain ⟨hKz, hKX, hKsn, hKsl⟩ := hK
  subst hK'
  have hO : Odd (Nat.card (oddCoreIn L)) := odd_card_oddCoreIn L
  have hOL : oddCoreIn L ≤ L := (oddCoreIn_normal L).1
  have hKL : K ≤ L := hKX.trans inf_le_left
  have hOcM : ∀ o ∈ oddCoreIn L, ∀ m ∈ K ⊔ oddCoreIn L, m * o * m⁻¹ = o :=
    fun o ho m hm => hOc o ho m (sup_le hKL hOL hm)
  have hOnM : ∀ m ∈ K ⊔ oddCoreIn L, ∀ o ∈ oddCoreIn L, m * o * m⁻¹ ∈ oddCoreIn L :=
    fun m hm o ho => by rw [hOcM o ho m hm]; exact ho
  have hOz : oddCoreIn L ≤ centralizer ({z} : Set G) := by
    intro o ho
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hOc o ho z (hKL hKz)
    calc o * z = (z * o * z⁻¹) * z := by rw [h]
      _ = z * o := by group
  have hOX : oddCoreIn L ≤ L ⊓ centralizer ({z} : Set G) := le_inf hOL hOz
  have hMX : K ⊔ oddCoreIn L ≤ L ⊓ centralizer ({z} : Set G) := sup_le hKX hOX
  have hKtwoResX : K ≤ twoRes (L ⊓ centralizer ({z} : Set G)) := by
    rw [← sec5pk_twoRes_eq hKsl]
    rw [twoRes]
    exact Subgroup.closure_mono fun g hg => ⟨hKX hg.1, hg.2⟩
  have hRK : ∀ x ∈ R, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ oddCoreIn L :=
    fun x hx k hk => hFF4 x hx k (hKtwoResX hk)
  have hRO : ∀ x ∈ R, ∀ o ∈ oddCoreIn L, x * o * x⁻¹ ∈ oddCoreIn L :=
    fun x hx o ho => conj_mem_oddCoreIn (hRN hx) ho
  have hRM : ∀ x ∈ R, ∀ m ∈ K ⊔ oddCoreIn L,
      x * m * x⁻¹ * m⁻¹ ∈ oddCoreIn L :=
    sec5pk_comm_sup hOnM hRO hRK
  have hdec : ∀ m ∈ K ⊔ oddCoreIn L,
      ∃ c ∈ (K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G), c⁻¹ * m ∈ oddCoreIn L :=
    sec5pk_lift hR2 hO le_sup_right hOnM hRM
  have hKM : ((K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G)) ≤ K ⊔ oddCoreIn L :=
    inf_le_left
  have hK'norm : ∀ m ∈ K ⊔ oddCoreIn L,
      ∀ c ∈ (K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G),
      m * c * m⁻¹ ∈ (K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G) :=
    sec5pk_cent_normal hOcM hdec
  have hKsn' : (((K ⊔ oddCoreIn L).subgroupOf
      (L ⊓ centralizer ({z} : Set G)))).IsSubnormal :=
    sec5pk_isSubnormal_sup (X := L ⊓ centralizer ({z} : Set G)) hKX hOX hKsn
      (fun x hx o ho => by rw [hOc o ho x hx.1]; exact ho)
  have hK'sn : (((K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G)).subgroupOf
      (L ⊓ centralizer ({z} : Set G))).IsSubnormal :=
    sec5pk_isSubnormal_of_normal hKM hMX hK'norm hKsn'
  have hOcK : ∀ o ∈ oddCoreIn L, ∀ k ∈ K, k * o * k⁻¹ = o :=
    fun o ho k hk => hOcM o ho k (Subgroup.mem_sup_left hk)
  have hMsl : IsSL23Mod ↥(K ⊔ oddCoreIn L) :=
    isSL23Mod_sup_odd hKsl (fun k hk n hn => by rw [hOcK n hn k hk]; exact hn) hO
  have hK'sl : IsSL23Mod ↥((K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G)) :=
    sec5pk_isSL23Mod_cent hKM le_sup_right hO hOcM hdec hMsl
  have hzcent : z ∈ centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    exact hRz
  have hzK' : z ∈ (K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G) :=
    ⟨Subgroup.mem_sup_left hKz, hzcent⟩
  have hK'L : ((K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G)) ≤
      L ⊓ centralizer ({z} : Set G) := hKM.trans hMX
  have hK'core : oddCoreIn ((K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G)) =
      oddCoreIn L ⊓ centralizer (R : Set G) := by
    have hcent := sec5pk_oddCoreIn_cent hKM le_sup_right hO hOcM hdec
    have hsup := sec5pk_oddCoreIn_sup hO hOcK hOK
    rw [hcent, hsup]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨-, hxc⟩, hxO⟩
      exact ⟨hxO, hxc⟩
    · rintro ⟨hxO, hxc⟩
      exact ⟨⟨Subgroup.mem_sup_right hxO, hxc⟩, hxO⟩
  have hQK' : twoCoreIn K ≤ (K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G) := by
    intro q hq
    have hqc : q ∈ centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      exact fun x hx => hRQ x hx q hq
    exact ⟨Subgroup.mem_sup_left (twoCoreIn_le_self K hq), hqc⟩
  have hK'two : twoCoreIn ((K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G)) =
      twoCoreIn K :=
    sec5pk_twoCoreIn_cent hO hOcK hKM hdec hKsl hK'sl hQ hQK'
  have hK'gen : twoRes ((K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G)) =
      (K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G) := sec5pk_twoRes_eq hK'sl
  have hO3' : IsPGroup 3
      (oddCoreIn ((K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G))) :=
    hO3.to_le (by rw [hK'core]; exact inf_le_left)
  have hK'ord : ∀ k ∈ (K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G),
      Odd (orderOf k) → ∃ n : ℕ, orderOf k = 3 ^ n :=
    sec5pk_orderOf_three_pow hK'sl hO3'
  exact ⟨⟨hzK', hK'L, hK'sn, hK'sl⟩, hK'two, hK'core, hK'ord, hK'gen⟩

end CFSG.OddStandard.SmallF3.Omega
