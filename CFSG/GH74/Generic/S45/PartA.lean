module

public import CFSG.GH74.Generic.S45.GLevel2
public import CFSG.GH74.Generic.S45.XLevel

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools Subgroup

theorem sq_eq_one_of_card_two {X : Type*} [Group X] {D : Subgroup X} (hD : Nat.card ↥D = 2) {d : X}
    (hd : d ∈ D) : d * d = 1 := by
  have h := pow_card_eq_one' (G := ↥D) (x := ⟨d, hd⟩)
  rw [hD] at h
  have := congrArg Subtype.val h
  simpa [pow_two] using this

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}

theorem KData.centralizer_eq_zpowers (hd : KData (CentralizerBar x) K (xbar x))
    (hD : Nat.card ↥(centralizer (K : Set (CentralizerBar x))) = 2) :
    centralizer (K : Set (CentralizerBar x)) = zpowers (xbar x) := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [zpowers_le]
    exact hd.z_mem_centralizer
  · have h2 : orderOf (xbar x) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact hd.sq) hd.ne
    have h3 : Nat.card ↥(zpowers (xbar x)) = 2 := by rw [Nat.card_zpowers, h2]
    omega

theorem KData.exists_conf2 (hd : KData (CentralizerBar x) K (xbar x))
    (hD : Nat.card ↥(centralizer (K : Set (CentralizerBar x))) = 2) :
    ∃ (R₀ : Subgroup (CentralizerBar x)) (T : Subgroup G), R₀ ≤ K ∧
      Conf2 (R₀ ⊔ centralizer (K : Set (CentralizerBar x))) R₀ T := by
  have hKn := hd.normal
  have hDn : (centralizer (K : Set (CentralizerBar x))).Normal := inferInstance
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨hS2, hSidx⟩ := hd.sup_isSylow' R
  let S₀' : Sylow 2 (CentralizerBar x) := hS2.toSylow hSidx
  have hS₀eq : (S₀' : Subgroup (CentralizerBar x)) =
      (R : Subgroup ↥K).map K.subtype ⊔ centralizer (K : Set (CentralizerBar x)) := rfl
  obtain ⟨T, hT⟩ := exists_sylowLift x S₀'
  have hR₀K : (R : Subgroup ↥K).map K.subtype ≤ K := Subgroup.map_subtype_le _
  obtain ⟨-, hR₀sq, hR₀card⟩ := hd.R_facts R
  have hinf : (R : Subgroup ↥K).map K.subtype ⊓ centralizer (K : Set (CentralizerBar x)) = ⊥ := by
    have h1 : (R : Subgroup ↥K).map K.subtype ⊓ centralizer (K : Set (CentralizerBar x)) ≤
        K ⊓ centralizer (K : Set (CentralizerBar x)) := inf_le_inf_right _ hR₀K
    rw [hd.inf_centralizer_eq_bot] at h1
    exact le_bot_iff.1 h1
  have hDz := hd.centralizer_eq_zpowers hD
  have hIso : IsSylowOf 2 ((R : Subgroup ↥K).map K.subtype) K := ⟨R, rfl⟩
  have hkf := KBase.xlevel hd.facts hd.central hd.sq hd.notin hIso
  rw [← hDz] at hkf
  refine ⟨(R : Subgroup ↥K).map K.subtype, T, hR₀K, ?_⟩
  refine ⟨by rw [← hS₀eq]; exact hT, le_sup_left, hR₀card, fun h => hd.notin (hR₀K h), ?_, ?_, ?_,
    hkf.1, hkf.2⟩
  · intro a ha b hb
    exact hd.S_comm R ha hb
  · intro a ha
    obtain ⟨r, hr, d, hd', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ha
    have hcomm : r * d = d * r := mem_centralizer_iff.1 hd' r (hR₀K hr)
    have hrr : r * r = 1 := hR₀sq r hr
    have hdd : d * d = 1 := sq_eq_one_of_card_two hD hd'
    calc (r * d) * (r * d) = r * (d * r) * d := by group
      _ = r * (r * d) * d := by rw [← hcomm]
      _ = (r * r) * (d * d) := by group
      _ = 1 := by rw [hrr, hdd, one_mul]
  · rw [card_sup_normal hinf, hR₀card, hD]

theorem KData.Rg_eq (hd : KData (CentralizerBar x) K (xbar x)) {R₀ : Subgroup (CentralizerBar x)}
    {T : Subgroup G} (hR₀K : R₀ ≤ K)
    (hc : Conf2 (R₀ ⊔ centralizer (K : Set (CentralizerBar x))) R₀ T) :
    Rg x R₀ T = T ⊓ Pre x K := by
  have hKn := hd.normal
  have hDn : (centralizer (K : Set (CentralizerBar x))).Normal := inferInstance
  ext t
  constructor
  · rintro ⟨htT, htC, htR⟩
    exact ⟨htT, htC, hR₀K htR⟩
  · rintro ⟨htT, htC, htK⟩
    refine ⟨htT, htC, ?_⟩
    have hmem := hc.lift.piC_mem htT
    obtain ⟨r, hr, d, hd', hrd⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
    have hdK : d ∈ K := by
      have : d = r⁻¹ * piC x t := by rw [← hrd]; group
      rw [this]
      exact mul_mem (inv_mem (hR₀K hr)) htK
    have hd1 : d = 1 := by
      have : d ∈ K ⊓ centralizer (K : Set (CentralizerBar x)) := ⟨hdK, hd'⟩
      rw [hd.inf_centralizer_eq_bot, Subgroup.mem_bot] at this
      exact this
    rw [hd1, mul_one] at hrd
    rw [← hrd]
    exact hr

end CFSG.GH74.Generic.S45
