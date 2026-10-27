module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma34LPlus
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Lemma34

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem aux_eq_one_or_eq_of_mem_zpowers {s t : X} (hs2 : s ^ 2 = 1)
    (ht : t ∈ Subgroup.zpowers s) : t = 1 ∨ t = s := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have h2 : s ^ (2 : ℤ) = 1 := by simpa using hs2
  have hk : s ^ k = s ^ (k % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 2, zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rw [hk]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

theorem exists_mem_inf_of_twoElt_mem_inf {D B Y : Subgroup X} {s y : X} {j : ℕ}
    (hBD : B ≤ D) (hDB : D ≤ pPrimeCoreOf 2 D ⊔ B) (hs : s ∈ B) (hs2 : s ^ 2 = 1)
    (hYs : Y ≤ centralizer ({s} : Set X)) (hYn : centralizer ({s} : Set X) ≤ normalizer (Y : Set X))
    (hyY : y ∈ Y) (hyD : y ∈ D) (hyj : y ^ (2 ^ j) = 1) :
    ∃ m ∈ B ⊓ Y, y * m⁻¹ ∈ pPrimeCoreOf 2 D := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcov : B ⊔ pPrimeCoreOf 2 D = D :=
    le_antisymm (sup_le hBD (oddCoreOf_le D)) (by rw [sup_comm]; exact hDB)
  have hOB : pPrimeCoreOf 2 B = B ⊓ pPrimeCoreOf 2 D := pPrimeCoreOf_eq_inf_of_covers hBD hcov
  have hODn : ∀ d ∈ D, d ∈ normalizer (pPrimeCoreOf 2 D : Set X) := fun d hd =>
    mem_normalizer_pPrimeCoreOf_of_mem hd
  have hyBO : y ∈ B ⊔ pPrimeCoreOf 2 D := by rw [hcov]; exact hyD
  obtain ⟨o₁, ho₁, a, haB, ha2, hya⟩ := exists_conj_twoElt_of_mem_sup_odd_X (A := B)
    (N := pPrimeCoreOf 2 D) (fun b hb => hODn b (hBD hb)) (odd_card_oddCoreOf D) hyBO hyj
  have hw : y * a⁻¹ ∈ pPrimeCoreOf 2 D := by
    have : y * a⁻¹ = o₁ * (a * o₁⁻¹ * a⁻¹) := by rw [hya]; group
    rw [this]
    exact (pPrimeCoreOf 2 D).mul_mem ho₁
      ((Subgroup.mem_normalizer_iff.1 (hODn a (hBD haB)) o₁⁻¹).1 ((pPrimeCoreOf 2 D).inv_mem ho₁))
  have hsy : s * y = y * s := (Subgroup.mem_centralizer_singleton_iff.1 (hYs hyY)).symm
  have has : ⁅a, s⁆ ∈ pPrimeCoreOf 2 D := by
    have hsD : s ∈ D := hBD hs
    set w := y * a⁻¹ with hwdef
    have hya' : y = w * a := by rw [hwdef]; group
    have h1 : s * a * s⁻¹ * a⁻¹ = (s * w * s⁻¹)⁻¹ * w := by
      have h2 : s * (w * a) * s⁻¹ = w * a := by
        rw [← hya']
        calc s * y * s⁻¹ = y * s * s⁻¹ := by rw [hsy]
          _ = y := by group
      have h3 : s * (w * a) * s⁻¹ = (s * w * s⁻¹) * (s * a * s⁻¹) := by group
      rw [h3] at h2
      calc s * a * s⁻¹ * a⁻¹ = (s * w * s⁻¹)⁻¹ * ((s * w * s⁻¹) * (s * a * s⁻¹)) * a⁻¹ := by group
        _ = (s * w * s⁻¹)⁻¹ * (w * a) * a⁻¹ := by rw [h2]
        _ = (s * w * s⁻¹)⁻¹ * w := by group
    have h4 : ⁅s, a⁆ ∈ pPrimeCoreOf 2 D := by
      have : ⁅s, a⁆ = s * a * s⁻¹ * a⁻¹ := rfl
      rw [this, h1]
      exact (pPrimeCoreOf 2 D).mul_mem ((pPrimeCoreOf 2 D).inv_mem
        ((Subgroup.mem_normalizer_iff.1 (hODn s hsD) w).1 hw)) hw
    have : ⁅a, s⁆ = (⁅s, a⁆)⁻¹ := (commutatorElement_inv s a).symm
    rw [this]
    exact (pPrimeCoreOf 2 D).inv_mem h4
  have hasB : ⁅a, s⁆ ∈ B ⊓ pPrimeCoreOf 2 D := by
    refine ⟨?_, has⟩
    rw [commutatorElement_def]
    exact B.mul_mem (B.mul_mem (B.mul_mem haB hs) (B.inv_mem haB)) (B.inv_mem hs)
  have has' : ⁅a, s⁆ ∈ pPrimeCoreOf 2 B := inf_pPrimeCoreOf_le_pPrimeCoreOf hBD hasB
  have hT : IsPGroup 2 ↥(Subgroup.zpowers s) := aux_isPGroup_zpowers_of_sq hs2
  have hTO : Subgroup.zpowers s ≤ normalizer (pPrimeCoreOf 2 B : Set X) :=
    (Subgroup.zpowers_le).2 (mem_normalizer_pPrimeCoreOf_of_mem hs)
  have hyt : ∀ t ∈ Subgroup.zpowers s, ⁅a, t⁆ ∈ pPrimeCoreOf 2 B := by
    intro t ht
    rcases aux_eq_one_or_eq_of_mem_zpowers hs2 ht with rfl | rfl
    · simp
    · exact has'
  obtain ⟨c, hc, hc2, hca⟩ :=
    exists_twoElt_centralizer_of_comm_mem_pgroup hT hTO haB hyt ha2
  have hcB : c ∈ B := hc.1
  have hcs : c ∈ centralizer ({s} : Set X) := by rw [← aux_centralizer_zpowers]; exact hc.2
  have hcD : c ∈ D := hBD hcB
  have hca' : c⁻¹ * a ∈ pPrimeCoreOf 2 D := by
    have := hca
    rw [hOB] at this
    exact this.2
  have hcy : c⁻¹ * y ∈ pPrimeCoreOf 2 D := by
    have h1 : c⁻¹ * y = (c⁻¹ * (y * a⁻¹) * c) * (c⁻¹ * a) := by group
    rw [h1]
    refine (pPrimeCoreOf 2 D).mul_mem ?_ hca'
    have := (Subgroup.mem_normalizer_iff.1 (hODn c⁻¹ (D.inv_mem hcD)) (y * a⁻¹)).1 hw
    simpa [mul_assoc] using this
  set Q : Subgroup X := pPrimeCoreOf 2 D ⊓ centralizer ({s} : Set X) with hQ
  have hQodd : Odd (Nat.card Q) :=
    Odd.of_dvd_nat (odd_card_oddCoreOf D) (Subgroup.card_dvd_of_le inf_le_left)
  have hcQ : Subgroup.zpowers c ≤ normalizer (Q : Set X) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_inf (hODn c hcD) (aux_mem_normalizer_centralizer_singleton
      (Subgroup.mem_centralizer_singleton_iff.1 hcs))
  have hyQ : y ∈ Subgroup.zpowers c ⊔ Q := by
    have h1 : c⁻¹ * y ∈ Q := by
      refine ⟨hcy, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have hcs' : Commute c s := Subgroup.mem_centralizer_singleton_iff.1 hcs
      have hys' : Commute y s := Subgroup.mem_centralizer_singleton_iff.1 (hYs hyY)
      exact (hcs'.inv_left.mul_left hys').eq
    have : y = c * (c⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers c) h1
  obtain ⟨o₂, ho₂, a', ha', ha'2, hya'⟩ :=
    exists_conj_twoElt_of_mem_sup_odd_X hcQ hQodd hyQ hyj
  have hmB : a' ∈ B := (Subgroup.zpowers_le.2 hcB) ha'
  have ho₂C : o₂ ∈ centralizer ({s} : Set X) := ho₂.2
  have hmY : a' ∈ Y := by
    have h1 : a' = o₂⁻¹ * y * o₂ := by rw [hya']; group
    rw [h1]
    have := (Subgroup.mem_normalizer_iff.1 (hYn ((centralizer ({s} : Set X)).inv_mem ho₂C)) y).1 hyY
    simpa using this
  refine ⟨a', ⟨hmB, hmY⟩, ?_⟩
  have h1 : y * a'⁻¹ = o₂ * (a' * o₂⁻¹ * a'⁻¹) := by rw [hya']; group
  rw [h1]
  exact (pPrimeCoreOf 2 D).mul_mem ho₂.1
    ((Subgroup.mem_normalizer_iff.1 (hODn a' (hBD hmB)) o₂⁻¹).1
      ((pPrimeCoreOf 2 D).inv_mem ho₂.1))

section Sec5

variable {n : ℕ} {z : X} {Z : Subgroup X}

theorem IsSec5Pair.exists_witness_mem_of_K0_ne_bot (hA : HypA X) (hn : IsMaxAhatDeg X n)
    (hp : IsSec5Pair X n z Z) {s : X}
    (hJ : K0 X n (K0 X n (normalizer (Z : Set X)) ⊓ centralizer ({s} : Set X)) ≠ ⊥) :
    ∃ (M : Subgroup X) (z₀ : X), z₀ ∈ Z ∧ z₀ ∈ centralizer ({s} : Set X) ∧
      IsIntrinsicIn X (K0 X n (normalizer (Z : Set X)) ⊓ centralizer ({s} : Set X)) M z₀ ∧
      IsDoubleCoverOfAlt (↥M ⧸ pPrimeCore 2 ↥M) n := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hex : ∃ M : Subgroup X, (∃ u, IsIntrinsicIn X
      (K0 X n (normalizer (Z : Set X)) ⊓ centralizer ({s} : Set X)) M u) ∧
      IsDoubleCoverOfAlt (↥M ⧸ pPrimeCore 2 ↥M) n := by
    by_contra hcon
    apply hJ
    have : {L : Subgroup X | (∃ u, IsIntrinsicIn X
        (K0 X n (normalizer (Z : Set X)) ⊓ centralizer ({s} : Set X)) L u) ∧
        IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n} = ∅ :=
      Set.eq_empty_of_forall_notMem fun L hL => hcon ⟨L, hL⟩
    exact (congrArg sSup this).trans sSup_empty
  obtain ⟨M, ⟨u, hu⟩, hMn⟩ := hex
  set F := K0 X n (normalizer (Z : Set X)) with hF
  set Kz := K0 X n (centralizer ({z} : Set X)) with hKz
  have hFK : F ≤ Kz := hp.K0_normalizer_le hA hn
  have hFC : F ⊓ centralizer ({s} : Set X) ≤ centralizer ({z} : Set X) :=
    inf_le_left.trans (hFK.trans (K0_le n _))
  obtain ⟨M₂, hM₂, hM₂n, -⟩ :=
    exists_isIntrinsicIn_centralizer hA hn (s := z) hp.orderOf_z hFC hu hMn
  have hMle : M ≤ F ⊓ centralizer ({s} : Set X) := hu.2.2.1.1
  have huM : u ∈ F ⊓ centralizer ({s} : Set X) := hMle hu.2.1
  have hu2 : u ^ (2 ^ 1) = 1 := by
    have : u ^ 2 = 1 := by rw [← hu.1]; exact pow_orderOf_eq_one u
    simpa using this
  have hcov : F ⊔ pPrimeCoreOf 2 Kz = Kz :=
    le_antisymm (sup_le hFK (oddCoreOf_le Kz)) (by rw [sup_comm]; exact hp.K0_centralizer_le_sup)
  have hZF : Z ≤ F := hp.le_K0_normalizer
  have hZK : Z ≤ Kz := hZF.trans hFK
  have hZN : Z ≤ normalizer (pPrimeCoreOf 2 Kz : Set X) := fun x hx =>
    mem_normalizer_pPrimeCoreOf_of_mem (hZK hx)
  have hu_zs : u ∈ zStar Kz := hM₂.mem_zStar_K0 hM₂n
  have hu_sup : u ∈ Z ⊔ pPrimeCoreOf 2 Kz := by
    rw [sup_comm]; exact zStar_le_pPrimeCoreOf_sup hp.sylow hu_zs
  obtain ⟨o₁, ho₁, ζ, hζ, -, hueq⟩ :=
    exists_conj_twoElt_of_mem_sup_odd_X hZN (odd_card_oddCoreOf Kz) hu_sup hu2
  have h1 : u * ζ⁻¹ ∈ pPrimeCoreOf 2 Kz := by
    have e : u * ζ⁻¹ = o₁ * (ζ * o₁⁻¹ * ζ⁻¹) := by rw [hueq]; group
    rw [e]
    exact (pPrimeCoreOf 2 Kz).mul_mem ho₁
      ((Subgroup.mem_normalizer_iff.1 (hZN hζ) o₁⁻¹).1 ((pPrimeCoreOf 2 Kz).inv_mem ho₁))
  have h2 : u * ζ⁻¹ ∈ pPrimeCoreOf 2 F := by
    rw [pPrimeCoreOf_eq_inf_of_covers hFK hcov]
    exact ⟨F.mul_mem huM.1 (F.inv_mem (hZF hζ)), h1⟩
  have hZNF : Z ≤ normalizer (pPrimeCoreOf 2 F : Set X) := fun x hx =>
    mem_normalizer_pPrimeCoreOf_of_mem (hZF hx)
  have hu_sup' : u ∈ Z ⊔ pPrimeCoreOf 2 F := by
    have e : u = (u * ζ⁻¹) * ζ := by group
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup h2 hζ
  obtain ⟨o₂, ho₂, ζ', hζ', -, hueq'⟩ :=
    exists_conj_twoElt_of_mem_sup_odd_X hZNF (odd_card_oddCoreOf F) hu_sup' hu2
  have ho₂N : o₂ ∈ normalizer (Z : Set X) := K0_le n _ (oddCoreOf_le F ho₂)
  have huZ : u ∈ Z := by
    rw [hueq']
    exact (Subgroup.mem_normalizer_iff.1 ho₂N ζ').1 hζ'
  exact ⟨M, u, huZ, huM.2, hu, hMn⟩

theorem lemma34_oTwoPrimeOf (hA : HypA X) (hn : IsMaxAhatDeg X n) (hp : IsSec5Pair X n z Z)
    {s : X} (hsN : s ∈ normalizer (Z : Set X)) (hs2 : orderOf s = 2)
    (hJ : K0 X n (K0 X n (normalizer (Z : Set X)) ⊓ centralizer ({s} : Set X)) ≠ ⊥) :
    oTwoPrimeOf (LPlusIn (centralizer ({s} : Set X))) ≤
      pPrimeCoreOf 2 (LPlusIn (centralizer ({s} : Set X))) ⊔
        (normalizer (Z : Set X) ⊓ LPlusIn (centralizer ({s} : Set X))) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, z₀, hz₀Z, hz₀C, hM, hMn⟩ := hp.exists_witness_mem_of_K0_ne_bot hA hn hJ
  set F := K0 X n (normalizer (Z : Set X)) with hF
  set Kz := K0 X n (centralizer ({z} : Set X)) with hKz
  set C := centralizer ({s} : Set X) with hC
  set Y := LPlusIn C with hY
  obtain ⟨M₁, hM₁, hM₁n, -⟩ :=
    exists_isIntrinsicIn_centralizer hA hn hs2 (inf_le_right : F ⊓ C ≤ C) hM hMn
  have hzY : z₀ ∈ zStar Y := hM₁.mem_zStar_LPlusIn
  have hz02 : z₀ ^ 2 = 1 := by rw [← hM.1]; exact pow_orderOf_eq_one z₀
  have hz₀N : z₀ ∈ normalizer (Z : Set X) := Subgroup.le_normalizer hz₀Z
  have hFKz : F ≤ Kz := hp.K0_normalizer_le hA hn
  have hcovF : F ⊔ pPrimeCoreOf 2 Kz = Kz :=
    le_antisymm (sup_le hFKz (oddCoreOf_le Kz)) (by rw [sup_comm]; exact hp.K0_centralizer_le_sup)
  have hz₀F : ∀ k ∈ F, ⁅k, z₀⁆ ∈ pPrimeCoreOf 2 F := by
    intro k hk
    have h1 : ⁅k, z₀⁆ ∈ pPrimeCoreOf 2 Kz := (hp.sylow.1 hz₀Z).2.2.2 k (hFKz hk)
    have h2 : ⁅k, z₀⁆ ∈ F := by
      rw [commutatorElement_def]
      exact F.mul_mem (F.mul_mem (F.mul_mem hk (hp.le_K0_normalizer hz₀Z)) (F.inv_mem hk))
        (F.inv_mem (hp.le_K0_normalizer hz₀Z))
    rw [pPrimeCoreOf_eq_inf_of_covers hFKz hcovF]
    exact ⟨h2, h1⟩
  have hDB := lemma33a_of_isSec5Pair hA hn hp z₀ hz₀N hM.1 hz₀F
  set D := centralizer ({z₀} : Set X) with hD
  set B := normalizer (Z : Set X) ⊓ D with hB
  have hsD : s ∈ D := Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_singleton_iff.1 hz₀C).symm
  have hsB : s ∈ B := ⟨hsN, hsD⟩
  have hs_sq : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
  have hBD : B ≤ D := inf_le_right
  have hDB' : D ≤ pPrimeCoreOf 2 D ⊔ B := hDB.le
  have hYs : Y ≤ C := LPlusIn_le C
  have hYn : C ≤ normalizer (Y : Set X) := le_normalizer_LPlusIn C
  set R := Y ⊓ D with hR
  have hRY : R ⊔ pPrimeCoreOf 2 Y = Y := by
    refine le_antisymm (sup_le inf_le_left (oddCoreOf_le Y)) fun y hy => ?_
    obtain ⟨o, ho, r, hr, rfl⟩ := exists_mul_eq_of_mem_zStar_involution hzY hz02 hy
    rw [sup_comm]
    exact Subgroup.mul_mem_sup ho hr
  have hOR : pPrimeCoreOf 2 R = R ⊓ pPrimeCoreOf 2 Y :=
    pPrimeCoreOf_eq_inf_of_covers inf_le_left hRY
  have hRO : R ⊓ pPrimeCoreOf 2 D ≤ pPrimeCoreOf 2 Y := fun x hx =>
    (hOR ▸ inf_pPrimeCoreOf_le_pPrimeCoreOf (inf_le_right : R ≤ D) hx : x ∈ R ⊓ pPrimeCoreOf 2 Y).2
  rw [oTwoPrimeOf_le_iff]
  rintro y hyY ⟨j, hyj⟩
  have hyRO : y ∈ R ⊔ pPrimeCoreOf 2 Y := by rw [hRY]; exact hyY
  obtain ⟨o', ho', a, haR, ha2, hya⟩ := exists_conj_twoElt_of_mem_sup_odd_X (A := R)
    (N := pPrimeCoreOf 2 Y) (fun r hr => mem_normalizer_pPrimeCoreOf_of_mem hr.1)
    (odd_card_oddCoreOf Y) hyRO hyj
  obtain ⟨m, hmBY, ham⟩ := exists_mem_inf_of_twoElt_mem_inf hBD hDB' hsB hs_sq hYs hYn
    haR.1 haR.2 ha2
  have hmR : m ∈ R := ⟨hmBY.2, hBD hmBY.1⟩
  have hw : a * m⁻¹ ∈ pPrimeCoreOf 2 Y :=
    hRO ⟨R.mul_mem haR (R.inv_mem hmR), ham⟩
  have hmn : m ∈ normalizer (pPrimeCoreOf 2 Y : Set X) := mem_normalizer_pPrimeCoreOf_of_mem hmBY.2
  have hy : y = (o' * (a * m⁻¹) * o'⁻¹) * (o' * (m * o'⁻¹ * m⁻¹)) * m := by rw [hya]; group
  rw [hy]
  refine Subgroup.mul_mem_sup ?_ (show m ∈ normalizer (Z : Set X) ⊓ Y from ⟨hmBY.1.1, hmBY.2⟩)
  refine (pPrimeCoreOf 2 Y).mul_mem ((pPrimeCoreOf 2 Y).mul_mem
    ((pPrimeCoreOf 2 Y).mul_mem ho' hw) ((pPrimeCoreOf 2 Y).inv_mem ho')) ?_
  exact (pPrimeCoreOf 2 Y).mul_mem ho'
    ((Subgroup.mem_normalizer_iff.1 hmn o'⁻¹).1 ((pPrimeCoreOf 2 Y).inv_mem ho'))

end Sec5

end Lemma34

end CFSG.OddStandard.Solomon75
