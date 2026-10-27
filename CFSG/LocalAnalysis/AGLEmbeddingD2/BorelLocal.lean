module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.TorusCase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairMaximal

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem exists_mem_inf_centralizer_of_isPGroup [Fact p.Prime] {T U : Subgroup X}
    (hT : IsPGroup p T) (hUT : U ≤ T) (hUn : T ≤ Subgroup.normalizer (U : Set X)) (hU : U ≠ ⊥) :
    ∃ a ∈ U, a ∈ Subgroup.centralizer (T : Set X) ∧ a ≠ 1 := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hyU, hyZ⟩ := Subgroup.mem_inf.1 hy
  refine ⟨y, Subgroup.mem_subgroupOf.1 hyU,
    Subgroup.mem_centralizer_iff.2 fun s hs => ?_, fun h1 => hy1 ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hyZ ⟨s, hs⟩)
  · exact Subtype.ext (Subtype.ext h1)

theorem D2AlmostSimple.heisBorel_of_local_of_eq {R : Sylow p X} {A X₀ K : Subgroup X}
    (hK : D2AlmostSimple p X R A X₀ K) (hout : ¬ p ∣ Nat.card (Outer K))
    (hcard : Nat.card (R : Subgroup X) = p ^ 3)
    (hX₀ : X₀ = Subgroup.normalizer ((R : Subgroup X) : Set X))
    (hC : Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R)
    (hZ : Nat.card ((R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) :
      Subgroup X) = p)
    (hcomm : ⁅(R : Subgroup X), (R : Subgroup X)⁆ =
      (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X))
    (hexp : ∀ r ∈ (R : Subgroup X), r ^ p = 1)
    (hsolv : Group.IsSolvable (Subgroup.normalizer ((R : Subgroup X) : Set X)))
    (hlines : ∃ t, t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) ∧
      ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
      (∀ x ∈ (R : Subgroup X),
        ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
          t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
      (∀ x ∈ (R : Subgroup X),
        ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
          t ^ e * x * (t ^ e)⁻¹ = x⁻¹ * z) ∧
      ∀ j : ℕ, 0 < j → j < m → ∀ F : Subgroup X,
        (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ F →
          F ≤ (R : Subgroup X) → F.relIndex (R : Subgroup X) = p →
            t ^ j ∉ Subgroup.normalizer (F : Set X)) :
    D2HeisBorel p R X₀ K := by
  have : Fact p.Prime := ⟨hK.prime⟩
  set Z : Subgroup X := (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X)
  have hcore : primeComplementCore (G := X₀) p = ⊥ := by
    subst hX₀
    exact primeComplementCore_normalizer_eq_bot R.isPGroup' hC
  refine ⟨hK.sylow_le_of_not_dvd_card_outer hout, hcard, hX₀.symm, hC, hZ, hcomm, hexp,
    ?_, ?_, hX₀ ▸ hsolv, hcore, hlines⟩
  ·
    intro W hWX₀ hX₀W
    have hRN : (R : Subgroup X) ≤ Subgroup.normalizer (W : Set X) := hK.sylow_le.trans hX₀W
    have hWN : W ≤ Subgroup.normalizer ((R : Subgroup X) : Set X) := hX₀ ▸ hWX₀
    by_cases hWR : W ⊓ (R : Subgroup X) = ⊥
    · left
      rw [eq_bot_iff]
      intro w hw
      have hwC : w ∈ Subgroup.centralizer ((R : Subgroup X) : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have hc : w * r * w⁻¹ * r⁻¹ ∈ W ⊓ (R : Subgroup X) := by
          refine ⟨?_, (R : Subgroup X).mul_mem
            ((Subgroup.mem_normalizer_iff.mp (hWN hw) r).mp hr) ((R : Subgroup X).inv_mem hr)⟩
          have h1 : r * w⁻¹ * r⁻¹ ∈ W :=
            (Subgroup.mem_normalizer_iff.mp (hRN hr) w⁻¹).mp (W.inv_mem hw)
          simpa [mul_assoc] using W.mul_mem hw h1
        rw [hWR, Subgroup.mem_bot] at hc
        have : w * r = r * w := by
          calc w * r = (w * r * w⁻¹ * r⁻¹) * r * w := by group
            _ = r * w := by rw [hc, one_mul]
        exact this.symm
      have : w ∈ W ⊓ (R : Subgroup X) := ⟨hw, hC hwC⟩
      rwa [hWR] at this
    · right
      have hUn : (R : Subgroup X) ≤ Subgroup.normalizer ((W ⊓ (R : Subgroup X) : Subgroup X) :
          Set X) := by
        intro r hr
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · rintro ⟨hxW, hxR⟩
          exact ⟨(Subgroup.mem_normalizer_iff.mp (hRN hr) x).mp hxW,
            (R : Subgroup X).mul_mem ((R : Subgroup X).mul_mem hr hxR)
              ((R : Subgroup X).inv_mem hr)⟩
        · rintro ⟨hxW, hxR⟩
          refine ⟨(Subgroup.mem_normalizer_iff.mp (hRN hr) x).mpr hxW, ?_⟩
          have : x = r⁻¹ * (r * x * r⁻¹) * r := by group
          rw [this]
          exact (R : Subgroup X).mul_mem
            ((R : Subgroup X).mul_mem ((R : Subgroup X).inv_mem hr) hxR) hr
      obtain ⟨a, ⟨haW, haR⟩, haC, ha1⟩ :=
        exists_mem_inf_centralizer_of_isPGroup R.isPGroup' inf_le_right hUn hWR
      have haZ : a ∈ Z := ⟨haR, haC⟩
      have hord : orderOf a = p := by
        have hdvd : orderOf a ∣ p := hZ ▸ Subgroup.orderOf_dvd_natCard Z haZ
        rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) ha1
        · exact h1
      have hZeq : Subgroup.zpowers a = Z :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haZ)
          (by rw [hZ, Nat.card_zpowers, hord])
      have hZW : Z ≤ W := hZeq ▸ Subgroup.zpowers_le.mpr haW
      exact hZW
  ·
    intro W hX₀W hWp
    have hle : (R : Subgroup X) ≤ Subgroup.normalizer (W : Set X) := hK.sylow_le.trans hX₀W
    have hsup : IsPGroup p (W ⊔ (R : Subgroup X) : Subgroup X) :=
      IsPGroup.to_sup_of_normal_left' hWp R.isPGroup' hle
    have := R.is_maximal' hsup le_sup_right
    exact le_sup_left.trans this.le

theorem D2AlmostSimple.eq_normalizer_of_maximal {R : Sylow p X} {A X₀ K : Subgroup X}
    (hK : D2AlmostSimple p X R A X₀ K)
    (hmax : ∀ Y : Subgroup X, Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ Y →
      Y = Subgroup.normalizer ((R : Subgroup X) : Set X) ∨ Y = ⊤) :
    X₀ = Subgroup.normalizer ((R : Subgroup X) : Set X) := by
  have : Fact p.Prime := ⟨hK.prime⟩
  have hNX₀ : Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ X₀ :=
    hK.normalizer_le_of_rank _ hK.sylow_le R.isPGroup' (by rw [hK.pRank_eq])
  rcases hmax X₀ hNX₀ with hX | hX
  · exact hX
  · exact absurd hX hK.ne_top

theorem D2AlmostSimple.heisBorel_of_local {R : Sylow p X} {A X₀ K : Subgroup X}
    (hK : D2AlmostSimple p X R A X₀ K) (hout : ¬ p ∣ Nat.card (Outer K))
    (hcard : Nat.card (R : Subgroup X) = p ^ 3)
    (hmax : ∀ Y : Subgroup X, Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ Y →
      Y = Subgroup.normalizer ((R : Subgroup X) : Set X) ∨ Y = ⊤)
    (hC : Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R)
    (hZ : Nat.card ((R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) :
      Subgroup X) = p)
    (hcomm : ⁅(R : Subgroup X), (R : Subgroup X)⁆ =
      (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X))
    (hexp : ∀ r ∈ (R : Subgroup X), r ^ p = 1)
    (hsolv : Group.IsSolvable (Subgroup.normalizer ((R : Subgroup X) : Set X)))
    (hlines : ∃ t, t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) ∧
      ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
      (∀ x ∈ (R : Subgroup X),
        ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
          t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
      (∀ x ∈ (R : Subgroup X),
        ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
          t ^ e * x * (t ^ e)⁻¹ = x⁻¹ * z) ∧
      ∀ j : ℕ, 0 < j → j < m → ∀ F : Subgroup X,
        (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ F →
          F ≤ (R : Subgroup X) → F.relIndex (R : Subgroup X) = p →
            t ^ j ∉ Subgroup.normalizer (F : Set X)) :
    D2HeisBorel p R X₀ K :=
  hK.heisBorel_of_local_of_eq hout hcard (hK.eq_normalizer_of_maximal hmax) hC hZ hcomm hexp hsolv
    hlines

@[expose] def D2HeisLocalAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    Subgroup.centralizer (K : Set X) = ⊥ → Nonempty (K ≃* i.Group) → ∀ p, Pp p →
    ∀ R : Sylow p X, ¬ p ∣ Nat.card (Outer K) ∧ Nat.card (R : Subgroup X) = p ^ 3 ∧
      (∀ Y : Subgroup X, Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ Y →
        Y = Subgroup.normalizer ((R : Subgroup X) : Set X) ∨ Y = ⊤) ∧
      Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R ∧
      Nat.card ((R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) :
        Subgroup X) = p ∧
      ⁅(R : Subgroup X), (R : Subgroup X)⁆ =
        (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ∧
      (∀ r ∈ (R : Subgroup X), r ^ p = 1) ∧
      Group.IsSolvable (Subgroup.normalizer ((R : Subgroup X) : Set X)) ∧
      ∃ t, t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) ∧
        ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
        (∀ x ∈ (R : Subgroup X),
          ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
            t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
        (∀ x ∈ (R : Subgroup X),
          ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
            t ^ e * x * (t ^ e)⁻¹ = x⁻¹ * z) ∧
        ∀ j : ℕ, 0 < j → j < m → ∀ F : Subgroup X,
          (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ F →
            F ≤ (R : Subgroup X) → F.relIndex (R : Subgroup X) = p →
              t ^ j ∉ Subgroup.normalizer (F : Set X)

theorem d2HeisBorelAt_of_local {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : D2HeisLocalAt i Pp) : D2HeisBorelAt i Pp := by
  intro X _ _ p hp R A X₀ K hK he
  obtain ⟨hout, hcard, hmax, hC, hZ, hcomm, hexp, hsolv, hlines⟩ :=
    h X K hK.normal hK.centralizer_eq_bot he p hp R
  exact hK.heisBorel_of_local hout hcard hmax hC hZ hcomm hexp hsolv hlines

theorem D2AlmostSimple.torusBorel_of_local {R : Sylow p X} {A X₀ K : Subgroup X}
    (hK : D2AlmostSimple p X R A X₀ K) (hout : ¬ p ∣ Nat.card (Outer K))
    (hcard : Nat.card (R : Subgroup X) = p ^ 2)
    (hmax : ∀ Y : Subgroup X, Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ Y →
      Y = Subgroup.normalizer ((R : Subgroup X) : Set X) ∨ Y = ⊤)
    (hC : Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R)
    (hsolv : Group.IsSolvable (Subgroup.normalizer ((R : Subgroup X) : Set X)))
    (htorus : ∃ t, t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) ∧
      ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
      (∀ x ∈ (R : Subgroup X), t ^ m * x * (t ^ m)⁻¹ = x ^ lam) ∧
      (∀ x ∈ (R : Subgroup X), t ^ e * x * (t ^ e)⁻¹ = x⁻¹) ∧
      ∀ k : ℕ, 0 < k → k < m → ∀ Y₀ : Subgroup X, Y₀ ≤ (R : Subgroup X) → Nat.card Y₀ = p →
        t ^ k ∉ Subgroup.normalizer (Y₀ : Set X)) :
    D2TorusBorel p R A X₀ K := by
  have : Fact p.Prime := ⟨hK.prime⟩
  have hRA : (R : Subgroup X) = A :=
    (Subgroup.eq_of_le_of_card_ge hK.A_le (by rw [hcard, hK.card_A])).symm
  have hNX₀ : Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ X₀ :=
    hK.normalizer_le_of_rank _ hK.sylow_le R.isPGroup' (by rw [hK.pRank_eq])
  have hX₀ : X₀ = Subgroup.normalizer ((R : Subgroup X) : Set X) := by
    rcases hmax X₀ hNX₀ with hX | hX
    · exact hX
    · exact absurd hX hK.ne_top
  obtain ⟨t, htN, m, lam, e, hm, hlam, he, hpow, hinv, hlines⟩ := htorus
  refine ⟨hRA, hRA ▸ hK.sylow_le_of_not_dvd_card_outer hout, ?_, ?_, ?_, hX₀ ▸ hsolv, ?_⟩
  ·
    intro W hWX₀ hX₀W
    have hRN : (R : Subgroup X) ≤ Subgroup.normalizer (W : Set X) := hK.sylow_le.trans hX₀W
    have hWN : W ≤ Subgroup.normalizer ((R : Subgroup X) : Set X) := hX₀ ▸ hWX₀
    by_cases hWR : W ⊓ (R : Subgroup X) = ⊥
    · left
      rw [eq_bot_iff]
      intro w hw
      have hwC : w ∈ Subgroup.centralizer ((R : Subgroup X) : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have hc : w * r * w⁻¹ * r⁻¹ ∈ W ⊓ (R : Subgroup X) := by
          refine ⟨?_, (R : Subgroup X).mul_mem
            ((Subgroup.mem_normalizer_iff.mp (hWN hw) r).mp hr) ((R : Subgroup X).inv_mem hr)⟩
          have h1 : r * w⁻¹ * r⁻¹ ∈ W :=
            (Subgroup.mem_normalizer_iff.mp (hRN hr) w⁻¹).mp (W.inv_mem hw)
          simpa [mul_assoc] using W.mul_mem hw h1
        rw [hWR, Subgroup.mem_bot] at hc
        have : w * r = r * w := by
          calc w * r = (w * r * w⁻¹ * r⁻¹) * r * w := by group
            _ = r * w := by rw [hc, one_mul]
        exact this.symm
      have : w ∈ W ⊓ (R : Subgroup X) := ⟨hw, hC hwC⟩
      rwa [hWR] at this
    · right
      rw [← hRA]
      have htW : t ∈ Subgroup.normalizer ((W ⊓ (R : Subgroup X) : Subgroup X) : Set X) := by
        have htX₀ : t ∈ X₀ := hX₀ ▸ htN
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · rintro ⟨hxW, hxR⟩
          exact ⟨(Subgroup.mem_normalizer_iff.mp (hX₀W htX₀) x).mp hxW,
            (Subgroup.mem_normalizer_iff.mp htN x).mp hxR⟩
        · rintro ⟨hxW, hxR⟩
          exact ⟨(Subgroup.mem_normalizer_iff.mp (hX₀W htX₀) x).mpr hxW,
            (Subgroup.mem_normalizer_iff.mp htN x).mpr hxR⟩
      have hdvd : Nat.card (W ⊓ (R : Subgroup X) : Subgroup X) ∣ p ^ 2 :=
        hcard ▸ Subgroup.card_dvd_of_le inf_le_right
      obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
      interval_cases k
      · exfalso
        exact hWR (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
      · exfalso
        exact hlines 1 one_pos hm _ inf_le_right (by simpa using hk) (by simpa using htW)
      · have heq : W ⊓ (R : Subgroup X) = (R : Subgroup X) :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hk, hcard])
        exact heq ▸ inf_le_left
  ·
    exact inf_le_right.trans (hRA ▸ hC)
  ·
    intro W _ hX₀W hWp
    have hle : (R : Subgroup X) ≤ Subgroup.normalizer (W : Set X) := hK.sylow_le.trans hX₀W
    have hsup : IsPGroup p (W ⊔ (R : Subgroup X) : Subgroup X) :=
      IsPGroup.to_sup_of_normal_left' hWp R.isPGroup' hle
    have := R.is_maximal' hsup le_sup_right
    exact hRA ▸ le_sup_left.trans this.le
  · exact ⟨t, hRA ▸ htN, m, lam, e, hm, hlam, he, hRA ▸ hpow, hRA ▸ hinv,
      fun k hk0 hkm Y₀ hY₀ hY₀c => hlines k hk0 hkm Y₀ (hRA ▸ hY₀) hY₀c⟩

@[expose] def D2TorusLocalAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    Subgroup.centralizer (K : Set X) = ⊥ → Nonempty (K ≃* i.Group) → ∀ p, Pp p →
    ∀ R : Sylow p X, ¬ p ∣ Nat.card (Outer K) ∧ Nat.card (R : Subgroup X) = p ^ 2 ∧
      (∀ Y : Subgroup X, Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ Y →
        Y = Subgroup.normalizer ((R : Subgroup X) : Set X) ∨ Y = ⊤) ∧
      Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R ∧
      Group.IsSolvable (Subgroup.normalizer ((R : Subgroup X) : Set X)) ∧
      ∃ t, t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) ∧
        ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
        (∀ x ∈ (R : Subgroup X), t ^ m * x * (t ^ m)⁻¹ = x ^ lam) ∧
        (∀ x ∈ (R : Subgroup X), t ^ e * x * (t ^ e)⁻¹ = x⁻¹) ∧
        ∀ k : ℕ, 0 < k → k < m → ∀ Y₀ : Subgroup X, Y₀ ≤ (R : Subgroup X) → Nat.card Y₀ = p →
          t ^ k ∉ Subgroup.normalizer (Y₀ : Set X)

theorem d2TorusBorelAt_of_local {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : D2TorusLocalAt i Pp) : D2TorusBorelAt i Pp := by
  intro X _ _ p hp R A X₀ K hK he
  obtain ⟨hout, hcard, hmax, hC, hsolv, htorus⟩ :=
    h X K hK.normal hK.centralizer_eq_bot he p hp R
  exact hK.torusBorel_of_local hout hcard hmax hC hsolv htorus

end CFSG.AGLEmbeddingD2
