module

public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonInputs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace Thompson

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem normalizer_inf_normalizer_conjE {K : Subgroup G} {a : G} (haK : conjSub a K = K)
    (haN : a ∈ Subgroup.normalizer (W : Set G)) :
    a ∈ Subgroup.normalizer ((K ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hK : x ∈ K ↔ a * x * a⁻¹ ∈ K := by
    have := mem_normalizer_iff_conjSub_eq.mpr haK
    exact Subgroup.mem_normalizer_iff.mp this x
  have hN : x ∈ Subgroup.normalizer (W : Set G) ↔
      a * x * a⁻¹ ∈ Subgroup.normalizer (W : Set G) := by
    constructor
    · intro hx
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haN hx) (Subgroup.inv_mem _ haN)
    · intro hx
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ haN) hx) haN
      simpa [mul_assoc] using this
  simp only [Subgroup.mem_inf, hK, hN]

section Fixed

variable [Finite G] {p f : ℕ} [Fact p.Prime]

structure OmegaBase (Ω : Set (Subgroup G)) (W : Subgroup G) : Prop where
  conjInv : ∀ (g : G) (K : Subgroup G), K ∈ Ω → conjSub g K ∈ Ω
  conjD : ∀ {R : Subgroup G}, R ∈ DSet Ω W → ∀ {n : G}, n ∈ Subgroup.normalizer (W : Set G) →
    conjSub n R ∈ DSet Ω W
  eight : ∀ {R : Subgroup G}, R ∈ RSet Ω → 8 ≤ Nat.card R
  quat : ∀ {R : Subgroup G}, R ∈ RSet Ω → IsQuatSub R
  eqLeLe : ∀ {K J : Subgroup G}, K ∈ Ω → J ∈ Ω → ∀ {A : Subgroup G}, IsPGroup 2 A →
    4 ≤ Nat.card A → A ≤ K → A ≤ J → K = J
  eqUSet : ∀ {U : Subgroup G}, U ∈ USet Ω → ∀ {K K' : Subgroup G}, K ∈ Ω → K' ∈ Ω → U ≤ K →
    U ≤ K' → K = K'

structure OmegaHooks (Ω : Set (Subgroup G)) (W : Subgroup G) : Prop extends OmegaBase Ω W where
  comm_W : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x
  infW : ∀ {R K : Subgroup G}, R ∈ DSet Ω W → K ∈ Ω → IsSylow2In R K →
    R ⊓ W = K ⊓ W ∧ K ⊓ W ∈ USet Ω ∧ IsCyclic ↥(R ⊓ W) ∧ 4 ≤ Nat.card ↥(R ⊓ W) ∧
      Nat.card R = 2 * Nat.card ↥(R ⊓ W)
  notMem : ∀ {R : Subgroup G}, R ∈ DSet Ω W → ∃ r ∈ R, r ∉ W
  zpow : ∀ {R : Subgroup G}, R ∈ DSet Ω W → ∃ u : G, Subgroup.zpowers u = R ⊓ W
  uniq : ∀ {K : Subgroup G}, K ∈ Ω → ∃ z : G, IsUniqueInvolution K z
  l67 : ∀ S : Sylow 2 G, ∀ R ∈ RSet Ω, ∀ R' ∈ RSet Ω, R ≤ (S : Subgroup G) →
    R' ≤ (S : Subgroup G) → R ≠ R' → Commutes R R'
  DpiG : ∀ {R : Subgroup G}, R ∈ DSet Ω W → ∀ {r r' : G}, r ∈ R → r' ∈ R → r ∉ W → r' ∉ W →
    piG W r = piG W r'
  piGle : ∀ {R T : Subgroup G}, R ∈ DSet Ω W → T ∈ DSet Ω W → T ≤ R ⊔ W ⊔ OCW W →
    ∀ {r t : G}, r ∈ R → t ∈ T → r ∉ W → t ∉ W → piG W t = piG W r

theorem OmegaBase.ofHyp (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) : OmegaBase Ω W where
  conjInv := fun g K hK => hΩ.conjInvariant g K hK
  conjD := fun hR => fun hn => conjSub_mem_D hΩ hR hn
  eight := fun hR => hΩ.eight_le_of_mem_RSet hp hR
  quat := fun hR => hΩ.isQuatSub_of_mem_RSet hp hR
  eqLeLe := fun hK hJ => fun hA h4 hAK hAJ => hΩ.eq_of_le_of_le hK hJ hA h4 hAK hAJ
  eqUSet := fun hU => fun hK hK' hUK hUK' => hΩ.eq_of_mem_USet hp hU hK hK' hUK hUK'

theorem OmegaHooks.ofHyp (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) : OmegaHooks Ω W where
  toOmegaBase := OmegaBase.ofHyp hp hΩ
  comm_W := commutes_of_mem_WSet hp hq hΩ hW
  infW := fun hR => fun hK hRK => inf_W_of_mem_D hp hq hΩ hW hR hK hRK
  notMem := fun hR => exists_not_mem_of_mem_D hp hq hΩ hW hR
  zpow := fun hR => exists_zpowers_eq_inf_W hp hq hΩ hW hR
  uniq := fun hK => hΩ.exists_uniqueInvolution hp hq hK
  l67 := fun S R hR R' hR' hRS hR'S hne => l6_7_proved p f hp hq G Ω hΩ S R hR R' hR' hRS hR'S hne
  DpiG := fun hR => fun hr hr' hrW hr'W => D_piG_eq hp hq hΩ hW hR hr hr' hrW hr'W
  piGle := fun hR hT hTR => fun hr ht hrW htW =>
    piG_eq_of_le_sup hp hq hΩ hW hR hT hTR hr ht hrW htW

theorem exists_fixed_memberE (H : OmegaBase Ω W) {R₀ : Subgroup G}
    (hR₀ : R₀ ∈ DSet Ω W) {a : G} (haN : a ∈ Subgroup.normalizer (W : Set G)) (ha2 : a * a = 1)
    {K : Subgroup G} (hK : K ∈ Ω) (hR₀K : R₀ ≤ K) (hR₁K : conjSub a R₀ ≤ K) :
    ∃ R ∈ DSet Ω W, conjSub a R = R := by
  by_cases ha1 : a = 1
  · exact ⟨R₀, hR₀, by rw [ha1, conjSub_one]⟩
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR₀.1
  have h8 : 8 ≤ Nat.card R₀ := H.eight hR₀.1
  have hJK : J = K := H.eqLeLe hJ hK hRJ.2.1 (by omega) hRJ.1 hR₀K
  subst hJK
  have hcard : Nat.card (conjSub a R₀) = Nat.card R₀ := natCard_conjSub R₀ a
  have haK : conjSub a J = J :=
    H.eqLeLe (H.conjInv a J hK) hK (isPGroup_conjSub a hRJ.2.1) (by omega)
      (conjSub_mono hRJ.1) hR₁K
  set N₁ : Subgroup G := J ⊓ Subgroup.normalizer (W : Set G) with hN₁
  have ha2g : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_mul_self_eq_one ha2 ha1
  have hzN : Subgroup.zpowers a ≤ Subgroup.normalizer (N₁ : Set G) :=
    Subgroup.zpowers_le.mpr (normalizer_inf_normalizer_conjE haK haN)
  obtain ⟨R, hRN, hRfix⟩ := AscL62.exists_sylow_normalized ha2g hzN
  have hR₀N₁ : R₀ ≤ N₁ := le_inf hR₀K hR₀.2
  have hle : Nat.card R₀ ≤ Nat.card R := hRN.natCard_le hRJ.2.1 hR₀N₁
  have hRJ' : IsSylow2In R J := hRJ.of_natCard_le hRN.2.1 (hRN.1.trans inf_le_left) hle
  exact ⟨R, ⟨mem_RSet_of_isSylow2In hK hRJ', hRN.1.trans inf_le_right⟩,
    hRfix a (Subgroup.mem_zpowers a)⟩

theorem exists_member_of_D_sameE (H : OmegaHooks Ω W)
    (hW : W ∈ WSet Ω) {R T : Subgroup G} (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    (hTR : T ≤ R ⊔ W ⊔ OCW W) : ∃ K ∈ Ω, R ≤ K ∧ T ≤ K := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨K', hK', hTK'⟩ := exists_isSylow2In_of_mem_RSet hT.1
  suffices hKK : K = K' from ⟨K, hK, hRK.1, hKK ▸ hTK'.1⟩
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  have hWab := H.comm_W
  have hPN : R ⊔ W ≤ Subgroup.normalizer (OCW W : Set G) :=
    sup_le (hR.2.trans (normalizer_le_normalizer_OCW W))
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_OCW W))
  have hP2 : IsPGroup 2 ↥(R ⊔ W) := hRK.2.1.to_sup_of_normal_right' hW2 hR.2
  have hPZ : IsSylow2In (R ⊔ W) (R ⊔ W ⊔ OCW W) := by
    refine ⟨le_sup_left, hP2, fun V hVZ hV2 hPV => ?_⟩
    refine le_antisymm (fun v hv => ?_) hPV
    have hvZ : v ∈ ((R ⊔ W ⊔ OCW W : Subgroup G) : Set G) := hVZ hv
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (R ⊔ W) (OCW W) hPN] at hvZ
    obtain ⟨p', hp', c, hc, rfl⟩ := hvZ
    have hcV : c ∈ V := by
      have := V.mul_mem (V.inv_mem (hPV hp')) hv
      simpa using this
    have hc1 : c = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hc
      (hV2.to_le (Subgroup.zpowers_le.mpr hcV))
    subst hc1
    simpa using hp'
  obtain ⟨V, hVZ, hTV⟩ := IsSylow2In.exists_ge hTK'.2.1 hTR
  obtain ⟨x, hxZ, hxV⟩ := exists_conj_of_isSylow2In hPZ hVZ
  have hxZ' : x ∈ ((OCW W ⊔ (R ⊔ W) : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hxZ
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (OCW W) (R ⊔ W) hPN] at hxZ'
  obtain ⟨c, hc, p', hp', rfl⟩ := hxZ'
  have hV : V = conjSub c (R ⊔ W) := by
    rw [← hxV, conjSub_mul, conjSub_eq_self_of_mem hp']
  have hcN : c ∈ Subgroup.normalizer (W : Set G) := OCW_le_normalizer W hc
  have hT' : conjSub c⁻¹ T ∈ DSet Ω W := H.conjD hT (Subgroup.inv_mem _ hcN)
  have hT'P : conjSub c⁻¹ T ≤ R ⊔ W := by
    have h1 : conjSub c⁻¹ T ≤ conjSub c⁻¹ (conjSub c (R ⊔ W)) := conjSub_mono (hV ▸ hTV)
    rwa [conjSub_inv_conjSub] at h1
  obtain ⟨S', hS'⟩ := hP2.exists_le_sylow
  have hh4 : 4 ≤ Nat.card T := by
    have := H.eight hT.1
    omega
  by_cases hRT : R = conjSub c⁻¹ T
  · have hTeq : T = conjSub c R := by rw [hRT, conjSub_conjSub_inv]
    have hK'' : conjSub c K ∈ Ω := H.conjInv c K hK
    have hTcK : T ≤ conjSub c K := hTeq ▸ conjSub_mono hRK.1
    have hKK' : K' = conjSub c K := H.eqLeLe hK' hK'' hTK'.2.1 hh4 hTK'.1 hTcK
    have hU := H.infW hR hK hRK
    have hUK : K ⊓ W ≤ conjSub c K := fun u hu => by
      have hcu : u * c = c * u := Subgroup.mem_centralizer_iff.mp (OCW_le_centralizer W hc) u hu.2
      have hc' : c * u * c⁻¹ = u := by
        rw [← hcu]
        group
      have := conj_mem_conjSub (n := c) hu.1
      rwa [hc'] at this
    have hKc : K = conjSub c K :=
      H.eqUSet hU.2.1 hK hK'' inf_le_left hUK
    exact hKc.trans hKK'.symm
  · exfalso
    have hcomm : Commutes R (conjSub c⁻¹ T) :=
      H.l67 S' R hR.1 _ hT'.1 (le_sup_left.trans hS') (hT'P.trans hS') hRT
    obtain ⟨t', ht'T, ht'W⟩ := H.notMem hT'
    have ht'P : t' ∈ ((W ⊔ R : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hT'P ht'T
    rw [Subgroup.coe_mul_of_right_le_normalizer_left W R hR.2] at ht'P
    obtain ⟨w, hw, r', hr', rfl⟩ := ht'P
    obtain ⟨K'', hK'', hT''K''⟩ := exists_isSylow2In_of_mem_RSet hT'.1
    have hinfo := H.infW hT' hK'' hT''K''
    have hquat : IsQuatSub (conjSub c⁻¹ T) := H.quat hT'.1
    obtain ⟨z, hz⟩ := H.uniq hK''
    have hzT : z ∈ conjSub c⁻¹ T := AscL62.mem_of_uniqueInvolution_of_pGroup hz hT''K''.1
      hT''K''.2.1 (by have := hquat.eight_le; omega)
    have hzT'' : IsUniqueInvolution (conjSub c⁻¹ T) z :=
      AscL62.isUniqueInvolution_of_le hz hT''K''.1 hzT
    obtain ⟨g, hg⟩ := H.zpow hT'
    have hgm : g ∈ conjSub c⁻¹ T ⊓ W := hg ▸ Subgroup.mem_zpowers g
    have hinv := AscL62.conj_eq_inv_of_not_mem hquat hzT'' (inf_le_left : conjSub c⁻¹ T ⊓ W ≤ _)
      hinfo.2.2.1 hinfo.2.2.2.2 ht'T (fun h => ht'W h.2) hgm
    have hr'g : r' * g = g * r' := hcomm r' hr' g hgm.1
    have hwg : w * g = g * w := hWab w hw g hgm.2
    have hcen : w * r' * g * (w * r')⁻¹ = g := by
      calc w * r' * g * (w * r')⁻¹ = w * (r' * g) * r'⁻¹ * w⁻¹ := by group
        _ = w * (g * r') * r'⁻¹ * w⁻¹ := by rw [hr'g]
        _ = w * g * w⁻¹ := by group
        _ = g * w * w⁻¹ := by rw [hwg]
        _ = g := by group
    have hgi : g = g⁻¹ := hcen.symm.trans hinv
    have hg2 : g * g = 1 := by
      calc g * g = g * g⁻¹ := by rw [← hgi]
        _ = 1 := mul_inv_cancel g
    have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
    have hcard : Nat.card ↥(conjSub c⁻¹ T ⊓ W) ≤ 2 := by
      rw [← hg, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) hord
    have := hinfo.2.2.2.1
    omega

theorem dComm_of_commuteE (H : OmegaHooks Ω W)
    {R₁ R₂ : Subgroup G} (h₁ : R₁ ∈ DSet Ω W) (h₂ : R₂ ∈ DSet Ω W) {r₁ r₂ : G}
    (hr₁ : r₁ ∈ R₁) (hr₂ : r₂ ∈ R₂) (hr₁W : r₁ ∉ W) (hr₂W : r₂ ∉ W)
    (hcomm : piG W r₁ * piG W r₂ = piG W r₂ * piG W r₁) (hne : piG W r₁ ≠ piG W r₂) :
    DComm W R₁ R₂ := by
  refine ⟨fun hle => hne ?_, fun x hx x' hx' => ?_⟩
  · exact (H.piGle h₁ h₂ hle hr₁ hr₂ hr₁W hr₂W).symm
  · by_cases hxW : x ∈ W
    · exact Subgroup.mem_sup_left (comm_mem_of_mem hxW (h₂.2 hx'))
    · by_cases hx'W : x' ∈ W
      · have h2 : x * x' * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (h₁.2 hx) x').mp hx'W
        exact Subgroup.mem_sup_left (W.mul_mem h2 (W.inv_mem hx'W))
      · have hc' : piG W x * piG W x' = piG W x' * piG W x := by
          rw [H.DpiG h₁ hx hr₁ hxW hr₁W, H.DpiG h₂ hx' hr₂ hx'W hr₂W]
          exact hcomm
        exact (piG_comm_iff (h₁.2 hx) (h₂.2 hx')).mp hc'

theorem conj_mul_conj_eqE (H : OmegaHooks Ω W)
    {a : G} (ha2 : a * a = 1) {w v : G} (hw : w ∈ W) (hv : v ∈ W)
    (hvd : v = a * w * a⁻¹) : a * (w * v) * a⁻¹ = w * v := by
  have hWab := H.comm_W
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
  have e1 : a * v * a⁻¹ = w := by
    rw [hvd, hai]
    calc a * (a * w * a) * a = (a * a) * w * (a * a) := by simp only [mul_assoc]
      _ = w := by rw [ha2, one_mul, mul_one]
  calc a * (w * v) * a⁻¹ = (a * w * a⁻¹) * (a * v * a⁻¹) := by group
    _ = v * w := by rw [e1, ← hvd]
    _ = w * v := hWab _ hv _ hw

end Fixed

end Thompson

end CFSG.ClassicalInvolution.Asc77
