module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Cent
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Graph

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace Q81

section Odd

variable {G G' : Type} [Group G] [Group G']

theorem map_oddPart_le (f : G →* G') (H : Subgroup G) :
    (oddPart H).map f ≤ oddPart (H.map f) := by
  rw [oddPart, MonoidHom.map_closure, closure_le]
  rintro _ ⟨x, ⟨hx, hodd⟩, rfl⟩
  exact mem_oddPart (mem_map_of_mem f hx) (Odd.of_dvd_nat hodd (orderOf_map_dvd f x))

theorem oddPart_map_of_injective (f : G →* G') (hf : Function.Injective f) (H : Subgroup G) :
    oddPart (H.map f) = (oddPart H).map f := by
  refine le_antisymm ?_ (map_oddPart_le f H)
  refine (closure_le _).mpr ?_
  rintro _ ⟨⟨x, hx, rfl⟩, hodd⟩
  exact mem_map_of_mem f (mem_oddPart hx (by rwa [orderOf_injective f hf] at hodd))

theorem exists_odd_preimage [Finite G] (f : G →* G') {H : Subgroup G} {y : G'}
    (hy : y ∈ H.map f) (hodd : Odd (orderOf y)) : ∃ x ∈ H, Odd (orderOf x) ∧ f x = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hcop : Nat.Coprime (2 ^ a) (orderOf (f x)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp
    (mem_zpowers_pow_iff.mpr hcop : f x ∈ zpowers (f x ^ 2 ^ a))
  refine ⟨(x ^ 2 ^ a) ^ k, zpow_mem (pow_mem hx _) k, ?_, ?_⟩
  · have h0 : (x ^ 2 ^ a) ^ m = 1 := by rw [← pow_mul, ← hxm, pow_orderOf_eq_one]
    have h1 : ((x ^ 2 ^ a) ^ k) ^ m = 1 := by
      rw [← zpow_natCast ((x ^ 2 ^ a) ^ k) m, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        h0, one_zpow]
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)
  · rw [map_zpow, map_pow, hk]

theorem oddPart_map_le [Finite G] (f : G →* G') (H : Subgroup G) :
    oddPart (H.map f) ≤ (oddPart H).map f := by
  refine (closure_le _).mpr ?_
  rintro y ⟨hy, hodd⟩
  obtain ⟨x, hx, hxo, rfl⟩ := exists_odd_preimage f hy hodd
  exact mem_map_of_mem f (mem_oddPart hx hxo)

end Odd

theorem conj_eq_of_mem_normalizer_map {X : Type} [Group X] [Finite X] {M : Subgroup X}
    {N : Subgroup ↥M} [N.Normal] (hN : Odd (Nat.card N)) {z : X} (hzM : z ∈ M)
    (hz2 : orderOf z = 2) {X₁ X₂ : Subgroup (↥M ⧸ N)}
    (hO : oddPart (centralizer {(QuotientGroup.mk ⟨z, hzM⟩ : ↥M ⧸ N)}) = X₁ ⊔ X₂)
    (hc : X₁ ≤ centralizer (X₂ : Set (↥M ⧸ N)))
    (hi : X₁ ⊓ X₂ = zpowers (QuotientGroup.mk ⟨z, hzM⟩ : ↥M ⧸ N))
    (hX₁ : IsSLTwoOver 3 ↥X₁) (hX₂ : IsSLTwoOver 3 ↥X₂) {g : X}
    (hg : g ∈ normalizer
      (((centralizer ({⟨z, hzM⟩} : Set ↥M)).map M.subtype : Subgroup X) : Set X)) :
    g * z * g⁻¹ = z := by
  set z' : ↥M := ⟨z, hzM⟩ with hz'
  set π := QuotientGroup.mk' N with hπ
  set C' := centralizer ({z'} : Set ↥M) with hC'
  have hz'2 : z' * z' = 1 := Subtype.ext (by
    change z * z = 1
    rw [← sq, ← hz2, pow_orderOf_eq_one])
  have hπC : C'.map π = centralizer {(QuotientGroup.mk z' : ↥M ⧸ N)} :=
    map_centralizer_eq hN hz'2
  have hNodd : ∀ n ∈ N, Odd (orderOf n) := fun n hn =>
    Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N hn)
  have hz'N : z' ∉ N := by
    intro h1
    have h2 := hNodd z' h1
    rw [hz', Subgroup.orderOf_mk, hz2] at h2
    exact absurd h2 (by decide)
  have hπz2 : orderOf (QuotientGroup.mk z' : ↥M ⧸ N) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← QuotientGroup.mk_mul, hz'2, QuotientGroup.mk_one]
    · intro h1
      exact hz'N ((QuotientGroup.eq_one_iff z').mp h1)
  have hz'O : z' ∈ oddPart C' := by
    have hmem : π z' ∈ (oddPart C').map π := by
      apply oddPart_map_le π C'
      rw [hπC, hO]
      exact mem_sup_left ((inf_le_left : X₁ ⊓ X₂ ≤ X₁) (hi ▸ mem_zpowers _))
    obtain ⟨a, ha, hax⟩ := hmem
    have haN : a⁻¹ * z' ∈ N := QuotientGroup.eq.mp hax
    have haC : a ∈ C' := oddPart_le C' ha
    have hz'C : z' ∈ C' := mem_centralizer_singleton_iff.mpr rfl
    have h1 : a⁻¹ * z' ∈ oddPart C' :=
      mem_oddPart (mul_mem (inv_mem haC) hz'C) (hNodd _ haN)
    have h2 : z' = a * (a⁻¹ * z') := by group
    rw [h2]
    exact mul_mem ha h1
  have hzO : z ∈ oddPart (C'.map M.subtype) := by
    rw [oddPart_map_of_injective M.subtype M.subtype_injective]
    exact mem_map_of_mem M.subtype hz'O
  have hyO : g * z * g⁻¹ ∈ oddPart (C'.map M.subtype) :=
    (mem_normalizer_iff.mp (mem_normalizer_oddPart hg) z).mp hzO
  rw [oddPart_map_of_injective M.subtype M.subtype_injective] at hyO
  obtain ⟨y', hy'O, hy'y⟩ := hyO
  have hy'y' : (y' : X) = g * z * g⁻¹ := hy'y
  have hy'C : y' ∈ C' := oddPart_le C' hy'O
  have hcent : ∀ c ∈ C', y' * c = c * y' := by
    intro c hc
    have hcA : (c : X) ∈ C'.map M.subtype := mem_map_of_mem M.subtype hc
    have h1 : g⁻¹ * c * g ∈ C'.map M.subtype := by
      have := (mem_normalizer_iff.mp (inv_mem hg) c).mp hcA
      rwa [inv_inv] at this
    obtain ⟨d, hd, hdc⟩ := h1
    have hdc' : (d : X) = g⁻¹ * c * g := hdc
    have h2 : (d : X) * z = z * d := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hd)
    apply Subtype.ext
    change (y' : X) * c = c * y'
    have hc' : (c : X) = g * d * g⁻¹ := by rw [hdc']; group
    rw [hy'y', hc']
    calc g * z * g⁻¹ * (g * ↑d * g⁻¹) = g * (z * d) * g⁻¹ := by group
      _ = g * (d * z) * g⁻¹ := by rw [h2]
      _ = g * ↑d * g⁻¹ * (g * z * g⁻¹) := by group
  have hπy : π y' ∈ X₁ ⊔ X₂ := by
    rw [← hO, ← hπC]
    exact map_oddPart_le π C' (mem_map_of_mem π hy'O)
  have hπyc : ∀ x ∈ X₁ ⊔ X₂, π y' * x = x * π y' := by
    intro x hx
    have hx' : x ∈ C'.map π := by
      rw [hπC]
      exact oddPart_le _ (by rw [hO]; exact hx)
    obtain ⟨c, hc, rfl⟩ := hx'
    rw [← map_mul, ← map_mul, hcent c hc]
  have hz1 := mem_zpowers_of_mem_center_sup hc hi hπz2 hX₁ hX₂ hπy hπyc
  have hy2 : y' * y' = 1 := Subtype.ext (by
    change (y' : X) * y' = 1
    rw [hy'y']
    have h1 : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  rcases eq_one_or_eq_of_mem_zpowers_two hπz2 hz1 with h1 | h1
  · exfalso
    have hy'N : y' ∈ N := (QuotientGroup.eq_one_iff y').mp h1
    have hy'1 : y' ≠ 1 := by
      intro h2
      have h3 : (y' : X) = 1 := by rw [h2]; rfl
      rw [hy'y'] at h3
      have h4 : z = 1 := by
        calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
          _ = 1 := by rw [h3]; group
      rw [h4, orderOf_one] at hz2
      exact absurd hz2 (by decide)
    have hord : orderOf y' = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy'1
    have h2 := hNodd y' hy'N
    rw [hord] at h2
    exact absurd h2 (by decide)
  · have h2 : y'⁻¹ * z' ∈ N := QuotientGroup.eq.mp h1
    have h3 : y' * z' = z' * y' := mem_centralizer_singleton_iff.mp hy'C
    have h4 : (y'⁻¹ * z') ^ 2 = 1 := by
      have hyi : y'⁻¹ = y' := inv_eq_of_mul_eq_one_left hy2
      rw [hyi, sq, show y' * z' * (y' * z') = y' * (z' * y') * z' by group, ← h3,
        show y' * (y' * z') * z' = (y' * y') * (z' * z') by group, hy2, hz'2, one_mul]
    have h5 : orderOf (y'⁻¹ * z') ∣ 2 := orderOf_dvd_of_pow_eq_one h4
    have h6 := hNodd _ h2
    have h7 : orderOf (y'⁻¹ * z') = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h5 with h8 | h8
      · exact h8
      · rw [h8] at h6
        exact absurd h6 (by decide)
    rw [orderOf_eq_one_iff, inv_mul_eq_one] at h7
    rw [← hy'y', h7]

end Q81

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Standing.Setup42

variable {h : Standing t L 3 4} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem mk_z_mem_KBar (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    (QuotientGroup.mk ⟨z, hσ.z_mem_centralizer_beta hFC hKC i j⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈ KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
  ⟨⟨z, hσ.z_mem_centralizer_beta hFC hKC i j⟩, (hσ.z_mem_Dstar hFC hKC i j).2, rfl⟩

theorem orderOf_mk_z (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    orderOf (QuotientGroup.mk ⟨z, hσ.z_mem_centralizer_beta hFC hKC i j⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 2 := by
  have hz2' : z ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rwa [hσ.z_order] at h1
  have hsq : (⟨z, hσ.z_mem_centralizer_beta hFC hKC i j⟩ :
      ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) ^ 2 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hz2')
  refine orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hsq, QuotientGroup.mk_one]) ?_
  intro h1
  rw [QuotientGroup.eq_one_iff] at h1
  have hdvd := Subgroup.orderOf_dvd_natCard _ h1
  rw [Subgroup.orderOf_mk, hσ.z_order] at hdvd
  exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)

variable {hσ : Setup42 h hS w z} {i j : ℕ}

theorem Q81Data.KBar_le (hD : Q81Data hσ i j) :
    KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hσ.tBar i j} := by
  rw [← hD.layerIn_eq]
  exact map_subtype_le _

theorem Q81Data.card_center_dvd (hD : Q81Data hσ i j) :
    Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ∣ 2 ∧
      (Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSL 4 3 1 ∨
        Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSU 4 3 1) := by
  rcases hD.center_cases with ⟨hL, hZ⟩ | ⟨hU, hZ⟩
  · refine ⟨?_, .inl hL⟩
    rcases hZ with hZ | ⟨hZ, -⟩ <;> simp [hZ]
  · refine ⟨?_, .inr hU⟩
    rcases hZ with hZ | ⟨hZ, -⟩ <;> simp [hZ]

theorem Q81Data.exists_sl2_z (hD : Q81Data hσ i j) (hF : L4U4ThreeInvolutionFacts)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput) :
    ∃ X₁ X₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), X₁ ≠ X₂ ∧
      X₁ ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {QuotientGroup.mk ⟨z, hσ.z_mem_centralizer_beta hFC hKC i j⟩} ∧
      X₂ ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {QuotientGroup.mk ⟨z, hσ.z_mem_centralizer_beta hFC hKC i j⟩} ∧
      X₁ ≤ centralizer (X₂ : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
      X₁ ⊓ X₂ = zpowers (QuotientGroup.mk ⟨z, hσ.z_mem_centralizer_beta hFC hKC i j⟩) ∧
      IsSLTwoOver 3 ↥X₁ ∧ IsSLTwoOver 3 ↥X₂ ∧
      Q81.oddPart (centralizer {(QuotientGroup.mk ⟨z, hσ.z_mem_centralizer_beta hFC hKC i j⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}) = X₁ ⊔ X₂ := by
  have hEn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := by
    have := LocalCores.layer_characteristic (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    infer_instance
  have hzK := hσ.mk_z_mem_KBar hFC hKC i j
  have hz2 := hσ.orderOf_mk_z hFC hKC i j
  obtain ⟨X₁, X₂, hne, h₁, h₂, hs₁, hs₂, hc, hi, hX₁, hX₂⟩ := hD.sl2 _ hzK hz2
  obtain ⟨hZ, hP⟩ := hD.card_center_dvd
  refine ⟨X₁, X₂, hne, h₁, h₂, hc, hi, hX₁, hX₂, ?_⟩
  exact Q81.oddPart_centralizer_eq hF hD.quasisimple hP hZ hD.isPGroup_centralizer
    (hD.KBar_le hzK).1 hz2 hne h₁ h₂ hs₁ hs₂ hc hi hX₁ hX₂

theorem Q81Data.conj_z_eq (hD : Q81Data hσ i j) (hF : L4U4ThreeInvolutionFacts)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput) {g : X}
    (hg : g ∈ normalizer ((centralizer ({z} : Set X) ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} : Subgroup X) : Set X)) :
    g * z * g⁻¹ = z := by
  obtain ⟨X₁, X₂, -, -, -, hc, hi, hX₁, hX₂, hO⟩ := hD.exists_sl2_z hF hFC hKC
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(centralizer
      ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  refine Q81.conj_eq_of_mem_normalizer_map hodd (hσ.z_mem_centralizer_beta hFC hKC i j)
    hσ.z_order hO hc hi hX₁ hX₂ ?_
  rwa [map_subtype_centralizer]

theorem Q81Data.conj_z_eq_of_normalizes (hD : Q81Data hσ i j) (hF : L4U4ThreeInvolutionFacts)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput) {g : X}
    (hg : g ∈ normalizer ((closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Subgroup X) :
      Set X)) : g * z * g⁻¹ = z := by
  refine hD.conj_z_eq hF hFC hKC ?_
  have hC : centralizer ((closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Subgroup X) :
      Set X) = centralizer ({z} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} := by
    rw [centralizer_closure]
    ext y
    simp only [mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
      forall_eq, mem_inf]
    tauto
  rw [← hC, mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [mem_centralizer_iff] at hy ⊢
    intro a ha
    have ha' : g⁻¹ * a * g ∈ closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} := by
      have := (mem_normalizer_iff.mp (inv_mem hg) a).mp ha
      rwa [inv_inv] at this
    have h1 := hy _ ha'
    calc a * (g * y * g⁻¹) = g * ((g⁻¹ * a * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * a := by group
  · intro hy
    rw [mem_centralizer_iff] at hy ⊢
    intro a ha
    have ha' : g * a * g⁻¹ ∈ closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} :=
      (mem_normalizer_iff.mp hg a).mp ha
    have h1 := hy _ ha'
    have h2 : g * (a * y) * g⁻¹ = g * (y * a) * g⁻¹ := by
      calc g * (a * y) * g⁻¹ = g * a * g⁻¹ * (g * y * g⁻¹) := by group
        _ = g * y * g⁻¹ * (g * a * g⁻¹) := h1
        _ = g * (y * a) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
