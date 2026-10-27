module

public import CFSG.ClassicalInvolution.Asc77.AscT7HLayer
public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


section Lie

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_local_of_layerLieType {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (hL : LayerLieType p f Ω c t n) :
    ∃ D : LocalLieSystemAt p f (exactFamily Ω c) c, D.card = 1 ∧
      ∃ i : Fin D.card, D.tag i = t ∧ D.rank i = n := by
  obtain ⟨D, hcard, i, ht, hn⟩ := hL
  have h : centralizingMembers (exactFamily Ω c) {c} = exactFamily Ω c :=
    centMembers_exactFamily Ω c
  unfold LocalLieSystemAt
  rw [h]
  exact ⟨D, hcard, i, ht, hn⟩

omit [Finite G] in
theorem eq_of_card_one {Φ : Set (Subgroup G)} {a : G} {D : LocalLieSystemAt p f Φ a}
    (hD : D.card = 1) (i j : Fin D.card) : i = j := by
  apply Fin.ext
  have := i.2
  have := j.2
  omega

theorem exists_fund_of_mem' (hΩ : HypOmegaMod p f Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hne : (tqMembers Ω c).Nonempty) (D : LocalLieSystemAt p f (exactFamily Ω c) c)
    (hD : D.card = 1) {N : Subgroup G} (hN : N ∈ tqMembers Ω c) (j : Fin D.card) :
    ∃ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
      R.map (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j) =
        modOdd c (exactCore c N) := by
  have hs : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 hne
  have hM : exactCore c N ∈ centMembers (exactFamily Ω c) c :=
    ⟨exactCore_mem_exactFamily hN, exactCore_le_centralizer c N⟩
  have hMY : exactCore c N ≤ centralizingLayer (exactFamily Ω c) {c} := le_centralizingLayer hM
  have hMfam : modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c N) ∈
      localFamily (exactFamily Ω c) c := ⟨(exactCore c N).subgroupOf _, ⟨_, hM, hMY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  obtain rfl : i = j := eq_of_card_one hD i j
  refine ⟨R, hR, ?_⟩
  have h1 : (R.map (D.hom i)).map (sectionQuotientHom hs.normalizes) =
      R.map (secComponentHom hs.normalizes D i) := Subgroup.map_map _ _ _
  rw [← h1, ← hMR]
  exact map_sectionQuotientHom_modOddIn hs.normalizes hM

theorem fund_perfect' (hp : p ≠ 2) {Φ : Set (Subgroup G)} {a : G}
    (D : LocalLieSystemAt p f Φ a) (j : Fin D.card) (h4 : 4 ≤ p ^ D.exp j)
    {R : Subgroup (compModel D j).K}
    (hR : R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D) : ⁅R, R⁆ = R :=
  commutator_self_eq_of_le (ModelFacts.fundPerfect_core (D.tag j) (D.rank j) p (D.exp j)
    hp (D.isFundTag j) (D.admissible j) h4 R hR)


theorem oddQuotMk_involution' (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (D : LocalLieSystemAt p f (exactFamily Ω c) c)
    (j : Fin D.card) (h4 : 4 ≤ p ^ D.exp j) {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω c)
    (hw : IsClassicalMember p f N w) {R : Subgroup (compModel D j).K}
    (hR : R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D) {τ : (compModel D j).K}
    (hτ : ∀ x ∈ R, (∀ r ∈ R, x * r = r * x) → x = 1 ∨ x = τ)
    (hmod : modOdd c (exactCore c N) =
      R.map (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j)) :
    oddQuotMk c ⟨w, exactCore_le_centralizer c N (mem_exactCore hw hc2 hN.2)⟩ =
      secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j τ := by
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j with hψ
  have hwE : w ∈ exactCore c N := mem_exactCore hw hc2 hN.2
  have hwC : w ∈ Subgroup.centralizer ({c} : Set G) := exactCore_le_centralizer c N hwE
  have hker : ψ.ker ≤ Subgroup.center (compModel D j).K :=
    secComponentHom_ker_le_center (normalizesLayer_exactFamily hΩ.conjInvariant) D j
  have hmem : oddQuotMk c ⟨w, hwC⟩ ∈ R.map ψ := hmod ▸ oddQuotMk_mem_modOdd hwE hwC
  obtain ⟨r, hrR, hr⟩ := hmem
  have hcw := isCentralInvolution_of_isClassicalMember hw
  have hcent : ∀ s ∈ R, ψ r * ψ s = ψ s * ψ r := by
    intro s hs
    have hsm : ψ s ∈ modOdd c (exactCore c N) := hmod ▸ ⟨s, hs, rfl⟩
    obtain ⟨k, hk, hks⟩ := hsm
    rw [hr, ← hks, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk c) (Subtype.ext (hcw.central _ (exactCore_le_left c N hk)))
  have hperf : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr (fund_perfect' hp D j h4 hR)
  have hrc : ∀ s ∈ R, r * s = s * r := by
    have key : (⟨r, hrR⟩ : ↥R) ∈ Subgroup.center ↥R :=
      FrameVertex.mem_center_of_commutators_central fun t => by
        rw [Subgroup.mem_center_iff]
        intro u
        have h1 : ψ (r * (t : (compModel D j).K) * r⁻¹ * (t : (compModel D j).K)⁻¹) = 1 := by
          have := hcent t t.2
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, this]
          group
        have h2 : r * (t : (compModel D j).K) * r⁻¹ * (t : (compModel D j).K)⁻¹ ∈
            Subgroup.center (compModel D j).K := hker (MonoidHom.mem_ker.mpr h1)
        apply Subtype.ext
        have := Subgroup.mem_center_iff.mp h2 u
        simpa [commutatorElement_def] using this
    intro s hs
    have := Subgroup.mem_center_iff.mp key ⟨s, hs⟩
    exact congrArg Subtype.val this.symm
  rcases hτ r hrR hrc with rfl | rfl
  · exfalso
    rw [map_one] at hr
    have h1 : (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 :=
      eq_one_of_oddQuotMk_eq_one (Subtype.ext hcw.sq) hr.symm
    exact hcw.ne_one (congrArg Subtype.val h1)
  · exact hr.symm

theorem exists_tau (hp : p ≠ 2) {Φ : Set (Subgroup G)} {a : G} (D : LocalLieSystemAt p f Φ a)
    (j : Fin D.card) (h5 : 5 ≤ p ^ D.exp j) (hG2 : D.tag j ≠ .G2)
    (hD4 : D.tag j ≠ .trialityD4) {R : Subgroup (compModel D j).K}
    (hR : R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D) :
    ∃ τ ∈ R, τ * τ = 1 ∧ τ ≠ 1 ∧ ∀ x ∈ R, (∀ r ∈ R, x * r = r * x) → x = 1 ∨ x = τ := by
  obtain ⟨e⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp (D.isFundTag j)
    (D.admissible j) hG2 hD4 hR
  have hodd := (ModelFacts.odd_and_five_le_card_galoisField (p := p) hp h5).1
  refine ⟨(e.symm (-1) : (compModel D j).K), (e.symm (-1)).2, ?_, ?_, ?_⟩
  · have h1 : (-1 : SL(2, GaloisField p (D.exp j))) * -1 = 1 := by
      calc (-1 : SL(2, GaloisField p (D.exp j))) * -1 = -1 * (-1)⁻¹ := by rw [neg_one_inv]
        _ = 1 := mul_inv_cancel _
    have h2 : e.symm (-1) * e.symm (-1) = 1 := by rw [← map_mul, h1, map_one]
    exact congrArg Subtype.val h2
  · intro h
    have h1 : e.symm (-1) = 1 := Subtype.ext h
    have h2 : (-1 : SL(2, GaloisField p (D.exp j))) = 1 := by
      have := congrArg e h1
      simpa using this
    exact sl2_neg_one_ne_one hodd h2
  · intro x hx hxc
    have hc : e ⟨x, hx⟩ ∈ Subgroup.center SL(2, GaloisField p (D.exp j)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨⟨y', hy'⟩, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hxc y' hy').symm
    rcases (mem_center_sl2_iff _).mp hc with h | h
    · left
      have : (⟨x, hx⟩ : ↥R) = 1 := by
        apply e.injective
        rw [h, map_one]
      exact congrArg Subtype.val this
    · right
      have : (⟨x, hx⟩ : ↥R) = e.symm (-1) := by
        rw [← h]
        simp
      exact congrArg Subtype.val this

theorem commute_of_map_commute {K Y : Type*} [Group K] [Group Y] [Finite K] (ψ : K →* Y)
    (hker : ψ.ker ≤ Subgroup.center K) (hodd : Odd (Nat.card (Subgroup.center K)))
    {a b : K} (ha : a * a = 1) (hb : b * b = 1) (hab : ψ a * ψ b = ψ b * ψ a) :
    a * b = b * a := by
  set d := a * b * a⁻¹ * b⁻¹ with hd
  have hdk : d ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hd, map_mul, map_mul, map_mul, map_inv, map_inv, hab]
    group
  have hdc : d ∈ Subgroup.center K := hker hdk
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have h1 : a * b * a⁻¹ = d * b := by
    rw [hd]
    calc a * b * a⁻¹ = a * b * a⁻¹ * (b⁻¹ * b) := by group
      _ = a * b * a⁻¹ * b⁻¹ * b := by group
  have h2 : (a * b * a⁻¹) * (a * b * a⁻¹) = 1 := by
    calc (a * b * a⁻¹) * (a * b * a⁻¹) = a * (b * b) * a⁻¹ := by group
      _ = 1 := by rw [hb]; group
  rw [h1] at h2
  have hdb : d * b = b * d := (Subgroup.mem_center_iff.mp hdc b).symm
  have hd2 : d * d = 1 := by
    calc d * d = d * d * (b * b) := by rw [hb, mul_one]
      _ = (d * b) * (d * b) := by rw [mul_assoc d b, ← mul_assoc b d, ← hdb]; group
      _ = 1 := h2
  have hd1 : d = 1 := by
    have hsub : Subgroup.zpowers d ≤ Subgroup.center K := Subgroup.zpowers_le.mpr hdc
    have hdvd : Nat.card (Subgroup.zpowers d) ∣ Nat.card (Subgroup.center K) :=
      Subgroup.card_dvd_of_le hsub
    rw [Nat.card_zpowers] at hdvd
    have hord : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hd2)
    have hodd' : Odd (orderOf d) := Odd.of_dvd_nat hodd hdvd
    have : orderOf d = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
      · exact h
      · rw [h] at hodd'; exact absurd hodd' (by decide)
    exact orderOf_eq_one_iff.mp this
  have : a * b * a⁻¹ * b⁻¹ = 1 := hd1
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [this, one_mul]

end Lie

end CFSG.ClassicalInvolution.Asc77.S24
