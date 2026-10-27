module

public import CFSG.Goldschmidt.Steps.G310TypeID
public import CFSG.Goldschmidt.Steps.G3b35
public import CFSG.Goldschmidt.Steps.G74Basic

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open

section Coprime

variable {X : Type*} [Group X] [Finite X]

theorem le_commutator_sup_inf_centralizer {R A : Subgroup X}
    (hAR : A ≤ Subgroup.normalizer (R : Set X)) (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hsolv : Group.IsSolvable R) :
    R ≤ ⁅R, A⁆ ⊔ R ⊓ Subgroup.centralizer (A : Set X) := by
  have : Subgroup.Normalizes A R := ⟨hAR⟩
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := R) (A := A) hsolv hcop
  have hcomm : (CFSG.commutatorAction (A := A) (G := R)).map R.subtype = ⁅R, A⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator R A hAR
  have hfix : CFSG.fixedPointSubgroup A R = (CFSG.subgroupCentralizerIn R A).subgroupOf R :=
    CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn R A hAR
  intro x hx
  have h1 : (⟨x, hx⟩ : R) ∈ CFSG.fixedPointSubgroup A R ⊔ CFSG.commutatorAction A R := by
    rw [hsup]
    exact Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem R.subtype h1
  rw [Subgroup.map_sup, hcomm, hfix, CFSG.subgroupCentralizerIn,
    Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h2
  rw [sup_comm]
  exact h2

end Coprime

section OddCent

variable {M : Type} [Group M] [Finite M]

@[expose] def oddCent (A : Subgroup M) : Subgroup M :=
  oddCoreOf (⊤ ⊓ Subgroup.centralizer (A : Set M))

omit [Finite M] in
theorem oddCent_le (A : Subgroup M) : oddCent A ≤ Subgroup.centralizer (A : Set M) :=
  (oddCoreOf_le _).trans inf_le_right

omit [Finite M] in
theorem centralizer_le_normalizer_oddCent (A : Subgroup M) :
    Subgroup.centralizer (A : Set M) ≤ Subgroup.normalizer (oddCent A : Set M) := fun c hc =>
  le_normalizer_oddCoreOf (⊤ ⊓ Subgroup.centralizer (A : Set M)) ⟨Subgroup.mem_top c, hc⟩

theorem odd_card_oddCent (A : Subgroup M) : Odd (Nat.card (oddCent A)) :=
  Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (not_two_dvd_card_oddCoreOf _))

theorem normalizer_le_normalizer_oddCent (A : Subgroup M) :
    Subgroup.normalizer (A : Set M) ≤ Subgroup.normalizer (oddCent A : Set M) := by
  intro n hn
  have hnC : n ∈ Subgroup.normalizer
      ((⊤ ⊓ Subgroup.centralizer (A : Set M) : Subgroup M) : Set M) := by
    rw [top_inf_eq]
    exact normalizer_le_normalizer_centralizer' A hn
  apply mem_normalizer_of_map_le
  rintro _ ⟨d, hd, rfl⟩
  have hd' : d ∈ (pPrimeCore 2 (⊤ ⊓ Subgroup.centralizer (A : Set M) : Subgroup M)).map
      (⊤ ⊓ Subgroup.centralizer (A : Set M)).subtype := by
    rw [← goldschmidtOddCore_eq_pPrimeCore]
    exact hd
  have := CFSG.Walter.conj_mem_map_of_characteristic hnC hd'
  rw [← goldschmidtOddCore_eq_pPrimeCore] at this
  exact this

end OddCent

section H0

variable {M : Type} [Group M] [Finite M]

@[expose] def h0 (A : Subgroup M) : Subgroup M := layerII A ⊔ oddCent A

theorem top_le_sup_normalizer {A : Subgroup M} (hS : IsSStarIn ⊤ A) :
    (⊤ : Subgroup M) ≤ normalClosureIn ⊤ A ⊔ Subgroup.normalizer (A : Set M) := by
  obtain ⟨-, -, T, hT, hAT, hcl, -⟩ := hS
  let S : Sylow 2 M := ⟨T, hT.2.1, fun {Q} hQ hTQ => hT.2.2 Q le_top hQ hTQ⟩
  have hcl' : CFSG.Open.fusionStronglyClosed (A : Set M) (S : Subgroup M) :=
    fun a ha g hg => hcl a ha g (Subgroup.mem_top g) hg
  have hKn := normalClosureIn_top_normal A
  exact G74.le_sup_normalizer (S := S) hAT hcl' le_top
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hKn]) (le_normalClosureIn_top A)

theorem h0_normal
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A) :
    (h0 A).Normal := by
  have hLn := layerII_normal A
  have hLN : (⊤ : Subgroup M) ≤ Subgroup.normalizer (layerII A : Set M) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
  obtain ⟨Z₂, hZA, -, hgen⟩ := exists_gen hO hS
  have hK : normalClosureIn ⊤ A ≤ Subgroup.normalizer (h0 A : Set M) := by
    refine hgen _ ?_ fun L hL => ?_
    · refine le_normalizer_sup (le_top.trans hLN) ?_
      exact (hZA.trans (Subgroup.le_centralizer_iff.mp (oddCent_le A))).trans
        (Subgroup.centralizer_le_normalizer _)
    · rcases (compFacts hO hS hL).types with hI | hII
      · refine le_normalizer_sup (le_top.trans hLN) ?_
        have hR := le_centralizer_typeI hO hS hL hI (oddCent_le A)
          (centralizer_le_normalizer_oddCent A) (odd_card_oddCent A)
        exact (Subgroup.le_centralizer_iff.mp hR).trans (Subgroup.centralizer_le_normalizer _)
      · exact (le_layerII ⟨hL, hII⟩).trans (le_sup_left.trans Subgroup.le_normalizer)
  have hN : Subgroup.normalizer (A : Set M) ≤ Subgroup.normalizer (h0 A : Set M) :=
    le_normalizer_sup (le_top.trans hLN) (normalizer_le_normalizer_oddCent A)
  have htop := (top_le_sup_normalizer hS).trans (sup_le hK hN)
  exact Subgroup.normalizer_eq_top_iff.mp (top_unique htop)

end H0

section Abelian

variable {M : Type} [Group M] [Finite M]

theorem commutator_oddCent_le_sup_centralizer
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : L ∈ typeIISet A) :
    ⁅oddCent A, oddCent A⁆ ≤ L ⊔ Subgroup.centralizer (L : Set M) := by
  have hF := compFacts hO hS hL.1
  set D := oddCent A with hD
  set N := Subgroup.normalizer (L : Set M) with hN
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hDN : D ≤ N := fun d hd => mem_normalizer_of_mem_centralizer hO hS hL.1 (oddCent_le A hd)
  have hLn : (L.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hq : CFSG.Open.IsQuasisimple (L.subgroupOf N) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hLN) hL.1.2.2
  have hII : IsGoldTypeII (L.subgroupOf N) :=
    SStarTransport.isGoldTypeII_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLN).symm hL.2
  have hS' := SStarTransport.isSStarIn_subgroupOf hF.sstar hLN
  have hne : (A ⊓ L).subgroupOf N ≠ ⊥ := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hF.noncentral
    intro hb
    have h1 : (⟨x, hLN hx.2⟩ : N) ∈ (A ⊓ L).subgroupOf N := hx
    rw [hb, Subgroup.mem_bot] at h1
    have h2 : x = 1 := congrArg Subtype.val h1
    rw [h2, one_mul, mul_one] at hxy
    exact hxy rfl
  have hYA : ⁅D.subgroupOf N, (A ⊓ L).subgroupOf N⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (oddCent_le A hd) a ha.1)
  obtain ⟨y, -, hYle⟩ := ((G35 N _ _ (D.subgroupOf N) hLn hq hII hS' hne).1 hYA).2
  set W : Subgroup N := L.subgroupOf N ⊔ Subgroup.centralizer ((L.subgroupOf N : Subgroup N) :
    Set N) with hW
  have : (Subgroup.centralizer ((L.subgroupOf N : Subgroup N) : Set N)).Normal :=
    Subgroup.normal_centralizer
  have hWn : W.Normal := Subgroup.sup_normal _ _
  have hcomm : ⁅D.subgroupOf N, D.subgroupOf N⁆ ≤ W := by
    rw [← QuotientGroup.ker_mk' W, ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator]
    have hWbot : W.map (QuotientGroup.mk' W) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have h1 : (D.subgroupOf N).map (QuotientGroup.mk' W) ≤
        Subgroup.zpowers (QuotientGroup.mk' W y) := by
      calc (D.subgroupOf N).map (QuotientGroup.mk' W)
          ≤ (Subgroup.zpowers y ⊔ W).map (QuotientGroup.mk' W) := Subgroup.map_mono hYle
        _ = Subgroup.zpowers (QuotientGroup.mk' W y) := by
          rw [Subgroup.map_sup, MonoidHom.map_zpowers, hWbot, sup_bot_eq]
    have h2 : ⁅Subgroup.zpowers (QuotientGroup.mk' W y),
        Subgroup.zpowers (QuotientGroup.mk' W y)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
    exact le_bot_iff.mp (h2 ▸ Subgroup.commutator_mono h1 h1)
  have hmap := Subgroup.map_mono (f := N.subtype) hcomm
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hDN, hW, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hLN] at hmap
  refine hmap.trans (sup_le_sup_left ?_ _)
  rintro _ ⟨c, hc, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc ⟨z, hLN hz⟩ hz)

theorem eq_one_of_mem_h0_centralizer
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {x : M} (hx : x ∈ h0 A)
    (hxc : x ∈ Subgroup.centralizer (layerII A : Set M)) : x = 1 := by
  set C₀ := h0 A ⊓ Subgroup.centralizer (layerII A : Set M) with hC₀
  have hLn := layerII_normal A
  have hHn := h0_normal hO hS
  have : (Subgroup.centralizer (layerII A : Set M)).Normal := Subgroup.normal_centralizer
  have hC₀n : C₀.Normal := Subgroup.normal_inf_normal _ _
  have hdisj : layerII A ⊓ C₀ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    refine eq_one_of_mem_layerII hO hS hz.1 fun L hL y hy => ?_
    exact (Subgroup.mem_centralizer_iff.mp hz.2.2 y (le_layerII hL hy)).symm
  have hcard : Nat.card C₀ = (layerII A).relIndex C₀ := by
    rw [Subgroup.relIndex, show (layerII A).subgroupOf C₀ = ⊥ from by
      rw [eq_bot_iff]
      intro z hz
      have : (z : M) ∈ layerII A ⊓ C₀ := ⟨hz, z.2⟩
      rw [hdisj, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact Subtype.ext this, Subgroup.index_bot]
  have hdvd : (layerII A).relIndex C₀ ∣ Nat.card (oddCent A) := by
    have h1 : (layerII A).relIndex (layerII A ⊔ C₀) = (layerII A).relIndex C₀ :=
      Subgroup.relIndex_sup_left C₀ (layerII A)
    have h2 := Subgroup.relIndex_mul_relIndex (H := layerII A) (K := layerII A ⊔ C₀) (L := h0 A)
      le_sup_left (sup_le le_sup_left inf_le_left)
    have h3 : (layerII A).relIndex (h0 A) = (layerII A).relIndex (oddCent A) :=
      Subgroup.relIndex_sup_left (oddCent A) (layerII A)
    rw [← h1]
    refine (Dvd.intro _ h2).trans ?_
    rw [h3]
    exact Subgroup.relIndex_dvd_card _ _
  have hodd : Odd (Nat.card C₀) := by
    rw [hcard]
    exact Odd.of_dvd_nat (odd_card_oddCent A) hdvd
  have hle : C₀ ≤ goldschmidtOddCore M := le_sSup ⟨hC₀n, hodd⟩
  rw [hO] at hle
  exact (Subgroup.mem_bot).mp (hle ⟨hx, hxc⟩)

theorem commutator_oddCent_le
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) : ⁅oddCent A, oddCent A⁆ ≤ layerII A := by
  intro d hd
  have hact : ∀ L ∈ typeIISet A, ∃ ℓ ∈ L, ∀ y ∈ L, d⁻¹ * y * d = ℓ⁻¹ * y * ℓ := by
    intro L hL
    have h1 := commutator_oddCent_le_sup_centralizer hO hS hL hd
    have hle : L ⊔ Subgroup.centralizer (L : Set M) ≤ G3a.actsBy L L le_rfl := by
      refine sup_le (fun ℓ hℓ => G3a.mem_actsBy.mpr ⟨ℓ, hℓ, fun _ _ => rfl⟩) fun c hc =>
        G3a.mem_actsBy.mpr ⟨1, L.one_mem, fun y hy => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hc y hy
      calc c⁻¹ * y * c = c⁻¹ * (y * c) := by group
        _ = c⁻¹ * (c * y) := by rw [this]
        _ = 1⁻¹ * y * 1 := by group
    exact G3a.mem_actsBy.mp (hle h1)
  obtain ⟨w, hw, hwc⟩ := exists_mul_inv_mem_centralizer_layerII (A := A) (fun L => L)
    (fun L _ => le_rfl) d hact
  have hwL : w ∈ layerII A := by
    have : (⨆ L ∈ typeIISet A, L) = layerII A := by rw [layerII, sSup_eq_iSup]
    rwa [this] at hw
  have hdD : d ∈ oddCent A := by
    refine (Subgroup.commutator_le.mpr fun a ha b hb => ?_) hd
    rw [commutatorElement_def]
    exact (oddCent A).mul_mem ((oddCent A).mul_mem ((oddCent A).mul_mem ha hb)
      ((oddCent A).inv_mem ha)) ((oddCent A).inv_mem hb)
  have h1 : d * w⁻¹ = 1 := eq_one_of_mem_h0_centralizer hO hS
    ((h0 A).mul_mem (Subgroup.mem_sup_right hdD) ((h0 A).inv_mem (Subgroup.mem_sup_left hwL)))
    hwc
  rw [mul_inv_eq_one] at h1
  rw [h1]
  exact hwL

theorem commutator_h0_le
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) : ⁅h0 A, h0 A⁆ ≤ layerII A := by
  have hLn := layerII_normal A
  rw [← QuotientGroup.ker_mk' (layerII A), ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator]
  have hLbot : (layerII A).map (QuotientGroup.mk' (layerII A)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hmap : (h0 A).map (QuotientGroup.mk' (layerII A)) =
      (oddCent A).map (QuotientGroup.mk' (layerII A)) := by
    rw [h0, Subgroup.map_sup, hLbot, bot_sup_eq]
  rw [hmap, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact commutator_oddCent_le hO hS

end Abelian

section LeH0

variable {M : Type} [Group M] [Finite M]

omit [Finite M] in
theorem mem_zpowers_pow_of_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : M} {k : ℕ}
    (hc : c ^ 2 ^ k = 1) (n : ℕ) : c ∈ Subgroup.zpowers (c ^ p ^ n) := by
  rw [mem_zpowers_pow_iff]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hc)
  rw [hi]
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)

theorem isPGroup_center_normalClosureIn (hO : goldschmidtOddCore M = ⊥) (A : Subgroup M) :
    IsPGroup 2 ↥(normalClosureIn ⊤ A ⊓
      Subgroup.centralizer (normalClosureIn ⊤ A : Set M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn := normalClosureIn_top_normal A
  have : (Subgroup.centralizer (normalClosureIn ⊤ A : Set M)).Normal := Subgroup.normal_centralizer
  refine CFSG.isPGroup_of_nilpotent_normal _ (Subgroup.normal_inf_normal _ _) ?_ (by
    rw [← goldschmidtOddCore_eq_pPrimeCore]
    exact hO)
  have : IsMulCommutative ↥(normalClosureIn ⊤ A ⊓
      Subgroup.centralizer (normalClosureIn ⊤ A : Set M)) :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1)⟩⟩
  infer_instance

theorem le_h0
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup M} (hP : P ∈ sigN ⊤ A p) :
    P ≤ h0 A ∧ ∀ L, IsComponentOf L (normalClosureIn ⊤ A) →
      P ≤ Subgroup.normalizer (L : Set M) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hPp, hAP, hPC⟩ := hP
  set K := normalClosureIn ⊤ A with hK
  have hKn := normalClosureIn_top_normal A
  have hA2 := isPGroup_two_of_isSStarIn hS
  have hcop : Nat.Coprime (Nat.card A) (Nat.card P) := by
    obtain ⟨m, hm⟩ := hA2.exists_card_eq
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hm, hn]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hdec := le_commutator_sup_inf_centralizer hAP hcop
    (by have := hPp.isNilpotent; exact IsNilpotent.to_isSolvable)
  have hWK : ⁅P, A⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro x _ a ha
    rw [commutatorElement_def]
    exact K.mul_mem (hKn.conj_mem a (le_normalClosureIn_top A ha) x)
      (K.inv_mem (le_normalClosureIn_top A ha))
  have hPC' : P ⊓ Subgroup.centralizer (A : Set M) ≤ oddCent A := hPC
  have hPN : ∀ L, IsComponentOf L K → P ≤ Subgroup.normalizer (L : Set M) := by
    intro L hL
    refine hdec.trans (sup_le (fun w hw => mem_normalizer_of_mem hO hS hL (hWK hw))
      fun c hc => mem_normalizer_of_mem_centralizer hO hS hL hc.2)
  refine ⟨?_, hPN⟩
  have hWP : ⁅P, A⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro x hx a ha
    rw [commutatorElement_def]
    have h1 : a * x⁻¹ * a⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hAP ha) x⁻¹).mp (P.inv_mem hx)
    have := P.mul_mem hx h1
    rwa [show x * (a * x⁻¹ * a⁻¹) = x * a * x⁻¹ * a⁻¹ by group] at this
  have hWL : ⁅P, A⁆ ≤ layerII A := by
    intro w hw
    have hwK := hWK hw
    have hwP := hWP hw
    obtain ⟨v, hv, hvc⟩ := exists_mul_inv_mem_centralizer_layerII (A := A) (fun L => L)
      (fun L _ => le_rfl) w (fun L hL => exists_act_of_mem hO hS hL.1 hwK)
    have hvL : v ∈ layerII A := by
      have : (⨆ L ∈ typeIISet A, L) = layerII A := by rw [layerII, sSup_eq_iSup]
      rwa [this] at hv
    set c := w * v⁻¹ with hc
    have hcK : c ∈ K := K.mul_mem hwK (K.inv_mem (layerII_le A hvL))
    have hcomp : ∀ L, IsComponentOf L K → L ≤ Subgroup.centralizer ({c} : Set M) := by
      intro L hL y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hLII : L ∈ typeIISet A
      · exact Subgroup.mem_centralizer_iff.mp hvc y (le_layerII hLII hy)
      · have hI : IsGoldTypeI L := by
          rcases (compFacts hO hS hL).types with hI | hII
          · exact hI
          · exact absurd ⟨hL, hII⟩ hLII
        have hwC := commutator_le_centralizer_typeI hO hS hL hI hp hp2 hPp (hPN L hL) hAP hw
        have hvC : v ∈ Subgroup.centralizer (L : Set M) := by
          have : layerII A ≤ Subgroup.centralizer (L : Set M) := by
            refine sSup_le fun L' hL' => le_centralizer_of_ne hL'.1 hL ?_
            rintro rfl
            exact hLII hL'
          exact this hvL
        have h1 := Subgroup.mem_centralizer_iff.mp hwC y hy
        have h2 := Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hvC) y hy
        calc y * c = y * w * v⁻¹ := by rw [hc, mul_assoc]
          _ = w * y * v⁻¹ := by rw [h1]
          _ = w * (y * v⁻¹) := by rw [mul_assoc]
          _ = w * (v⁻¹ * y) := by rw [h2]
          _ = c * y := by rw [hc]; group
    obtain ⟨Z₂, -, hZc, hgen⟩ := exists_gen hO hS
    have hKc : K ≤ Subgroup.centralizer ({c} : Set M) := by
      refine hgen _ (fun z hz => ?_) hcomp
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hZc z hz c hcK
    have hcZ : c ∈ K ⊓ Subgroup.centralizer (K : Set M) := by
      refine ⟨hcK, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hKc hy))
    obtain ⟨k, hk⟩ := isPGroup_center_normalClosureIn hO A ⟨c, hcZ⟩
    have hck : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨n, hn⟩ := hPp ⟨w, hwP⟩
    have hwn : w ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hcv : c * v = v * c := (Subgroup.mem_centralizer_iff.mp hvc v hvL).symm
    have hwcv : w = c * v := by rw [hc]; group
    have hcpow : c ^ p ^ n ∈ layerII A := by
      have h1 : c ^ p ^ n * v ^ p ^ n = 1 := by
        rw [← Commute.mul_pow hcv, ← hwcv, hwn]
      rw [eq_inv_of_mul_eq_one_left h1]
      exact (layerII A).inv_mem ((layerII A).pow_mem hvL _)
    have hcL : c ∈ layerII A :=
      Subgroup.zpowers_le.mpr hcpow (mem_zpowers_pow_of_two hp hp2 hck n)
    rw [hwcv]
    exact (layerII A).mul_mem hcL hvL
  exact hdec.trans (sup_le_sup hWL (hPC'.trans le_rfl))

end LeH0

end CFSG.Goldschmidt.G310
