module

public import CFSG.ClassicalInvolution.Asc77.AscE187P1a
public import CFSG.ClassicalInvolution.Asc77.AscE187Basic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem E187C.exists_delta_of (hc : ConjInvariant Ω)
    (h8R : ∀ {Q : Subgroup G}, Q ∈ RSet Ω → 8 ≤ Nat.card Q)
    (hle2 : ∀ {K J A : Subgroup G}, K ∈ Ω → J ∈ Ω → K ≠ J → IsPGroup 2 A → A ≤ K → A ≤ J →
      Nat.card A ≤ 2)
    (hsyl : ∀ {K Q : Subgroup G}, K ∈ Ω → Q ∈ RSet Ω → Q ≤ K → IsSylow2In Q K)
    (hnorm : ∀ {K J : Subgroup G} {z : G} {A : Subgroup G}, K ∈ Ω → J ∈ Ω → K ≠ J →
      IsUniqueInvolution K z → A ≤ J → IsPGroup 2 A → 3 ≤ Nat.card A →
      A ≤ Subgroup.centralizer ({z} : Set G) → A ≤ Subgroup.normalizer (K : Set G))
    (hl67 : ∀ {R' : Subgroup G}, R' ∈ RSet Ω → R' ≤ (S : Subgroup G) → R ≠ R' → Commutes R R')
    (hcent : ∀ {J R₂ : Subgroup G}, J ∈ KPerp Ω K → R₂ ∈ RSet Ω → R₂ ≤ J → Commutes R R₂ →
      ∀ a ∈ R ⊔ R₂, a ∈ W → a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H)
    (hK : K ∈ Ω) (hRR : R ∈ RSet Ω) (hRK : R ≤ K)
    (hRS : R ≤ (S : Subgroup G)) (hW : ∀ s ∈ (S : Subgroup G), conjSub s W = W) {z t : G}
    (hz : IsUniqueInvolution K z) (hzW : z ∈ W) (ht2 : t * t = 1)
    (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t) :
    ∃ B : Subgroup G, ∃ b : G, B ≤ (S : Subgroup G) ∧ B ≤ Subgroup.centralizer ({t} : Set G) ∧
      IsUniqueInvolution B b ∧ 8 ≤ Nat.card B ∧ b = z * (t * z * t⁻¹) ∧ b ∈ W ∧
      Subgroup.centralizer ({b} : Set G) ≤ H := by
  have hR8 : 8 ≤ Nat.card R := h8R hRR
  have hR2 : IsPGroup 2 R := by
    obtain ⟨J, -, -, h2, -⟩ := mem_RSet_iff.mp hRR
    exact h2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hnK : conjSub t K ≠ K := by
    intro hK'
    apply hnc
    have := hz.conj_eq hK'
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [this]
  have hK'Ω : conjSub t K ∈ Ω := hc t K hK
  have hz' : IsUniqueInvolution (conjSub t K) (t * z * t⁻¹) := hz.conj t
  have hR'mem : conjSub t R ∈ RSet Ω := RSet.conj hc hRR t
  have hR'K' : conjSub t R ≤ conjSub t K := conjSub_mono hRK
  have hR'S : conjSub t R ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : t⁻¹ * x * t ∈ (S : Subgroup G) := hRS hx
    have : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [this]
    exact S.mul_mem (S.mul_mem htS h1) (S.inv_mem htS)
  have hne : R ≠ conjSub t R := by
    intro hRR'
    have := hle2 hK hK'Ω (Ne.symm hnK) hR2 hRK (hRR' ▸ hR'K')
    omega
  have hcomm : Commutes R (conjSub t R) :=
    hl67 hR'mem hR'S hne
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hRK hR2 (by omega)
  have hz'R' : t * z * t⁻¹ ∈ conjSub t R := conj_mem_conjSub hzR
  have hzz' : z * (t * z * t⁻¹) = (t * z * t⁻¹) * z := hcomm z hzR _ hz'R'
  have hz'ne : t * z * t⁻¹ ≠ z := by
    intro h1
    apply hnc
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [h1]
  have hb2 : (z * (t * z * t⁻¹)) * (z * (t * z * t⁻¹)) = 1 := by
    calc (z * (t * z * t⁻¹)) * (z * (t * z * t⁻¹))
        = z * ((t * z * t⁻¹) * z) * (t * z * t⁻¹) := by group
      _ = z * (z * (t * z * t⁻¹)) * (t * z * t⁻¹) := by rw [hzz']
      _ = (z * z) * ((t * z * t⁻¹) * (t * z * t⁻¹)) := by group
      _ = 1 := by rw [hz.sq, hz'.sq]; group
  have hb1 : z * (t * z * t⁻¹) ≠ 1 := by
    intro h1
    apply hz'ne
    have h2 : t * z * t⁻¹ = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_right hz.sq
  have hz'W : t * z * t⁻¹ ∈ W := by
    have := conj_mem_conjSub (n := t) hzW
    rwa [hW t htS] at this
  have hbW : z * (t * z * t⁻¹) ∈ W := W.mul_mem hzW hz'W
  have hR'N : conjSub t R ≤ Subgroup.normalizer (K : Set G) := by
    have hR'syl : IsSylow2In (conjSub t R) (conjSub t K) :=
      hsyl hK'Ω hR'mem hR'K'
    refine hnorm hK hK'Ω (Ne.symm hnK) hz hR'K'
      hR'syl.2.1 (by have := h8R hR'mem; omega) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm z hzR x hx).symm
  have hperp : conjSub t K ∈ KPerp Ω K :=
    Set.mem_insert_of_mem _ ⟨hK'Ω, hnK, conjSub t R, hR'mem, hR'K', hR'N⟩
  have hbcent : Subgroup.centralizer ({z * (t * z * t⁻¹)} : Set G) ≤ H :=
    hcent hperp hR'mem hR'K' hcomm _ (Subgroup.mul_mem_sup hzR hz'R') hbW hb1 hb2
  let φ : ↥R →* G :=
    MonoidHom.mk' (fun x => (x : G) * (t * (x : G) * t⁻¹)) (fun x y => by
      have hy : (y : G) * (t * (x : G) * t⁻¹) = (t * (x : G) * t⁻¹) * y :=
        hcomm y y.2 _ (conj_mem_conjSub x.2)
      show (x : G) * y * (t * ((x : G) * y) * t⁻¹) =
        ((x : G) * (t * x * t⁻¹)) * ((y : G) * (t * y * t⁻¹))
      calc (x : G) * y * (t * ((x : G) * y) * t⁻¹)
          = (x : G) * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) := by group
        _ = (x : G) * ((t * x * t⁻¹) * y) * (t * y * t⁻¹) := by rw [hy]
        _ = ((x : G) * (t * x * t⁻¹)) * ((y : G) * (t * y * t⁻¹)) := by group)
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (x : G) * (t * (x : G) * t⁻¹) = 1 := hx
    have hxR' : (x : G) ∈ conjSub t R := by
      have : (x : G) = (t * (x : G) * t⁻¹)⁻¹ := (inv_eq_of_mul_eq_one_left h1).symm
      rw [this]
      exact (conjSub t R).inv_mem (conj_mem_conjSub x.2)
    by_contra hx1
    have hx1' : (x : G) ≠ 1 := fun hh => hx1 (Subtype.ext hh)
    have hx2 : IsPGroup 2 (Subgroup.zpowers (x : G)) :=
      hR2.to_le (Subgroup.zpowers_le.mpr x.2)
    have hzx : z ∈ Subgroup.zpowers (x : G) :=
      mem_zpowers_of_isUniqueInvolution hz (hRK x.2) hx1' hx2
    have hz'x : t * z * t⁻¹ ∈ Subgroup.zpowers (x : G) :=
      mem_zpowers_of_isUniqueInvolution hz' (hR'K' hxR') hx1' hx2
    have hcard : Nat.card (Subgroup.zpowers (x : G)) ≤ 2 :=
      hle2 hK hK'Ω (Ne.symm hnK) hx2
        (Subgroup.zpowers_le.mpr (hRK x.2)) (Subgroup.zpowers_le.mpr (hR'K' hxR'))
    have hord : orderOf (x : G) = 2 := by
      have hdvd : orderOf (x : G) ∣ 2 ^ 1 := by
        obtain ⟨n, hn⟩ := hx2.exists_card_eq
        rw [Nat.card_zpowers] at hn hcard
        have : n ≤ 1 := by
          by_contra hn1
          have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        rw [hn]
        exact pow_dvd_pow 2 this
      rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨k, hk, hk'⟩
      interval_cases k
      · exfalso
        exact hx1' (orderOf_eq_one_iff.mp (by simpa using hk'))
      · simpa using hk'
    have hxsq : (x : G) * (x : G) = 1 := by
      have := pow_orderOf_eq_one (x : G)
      rwa [hord, pow_two] at this
    have hxz : (x : G) = z := by
      rcases hz.unique x (hRK x.2) hxsq with h' | h'
      · exact absurd h' hx1'
      · exact h'
    have hxz' : (x : G) = t * z * t⁻¹ := by
      rcases hz'.unique x (hR'K' hxR') hxsq with h' | h'
      · exact absurd h' hx1'
      · exact h'
    exact hz'ne (hxz'.symm.trans hxz)
  refine ⟨φ.range, z * (t * z * t⁻¹), ?_, ?_, ?_, ?_, rfl, hbW, hbcent⟩
  · rintro _ ⟨x, rfl⟩
    exact S.mul_mem (hRS x.2) (hR'S (conj_mem_conjSub x.2))
  · rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx : (x : G) * (t * (x : G) * t⁻¹) = (t * (x : G) * t⁻¹) * x :=
      hcomm x x.2 _ (conj_mem_conjSub x.2)
    show (x : G) * (t * x * t⁻¹) * t = t * ((x : G) * (t * x * t⁻¹))
    have e : t * ((x : G) * (t * x * t⁻¹)) * t⁻¹ = (x : G) * (t * x * t⁻¹) := by
      calc t * ((x : G) * (t * x * t⁻¹)) * t⁻¹
          = (t * x * t⁻¹) * ((t * t) * x * (t * t)⁻¹) := by group
        _ = (t * x * t⁻¹) * x := by rw [ht2]; group
        _ = (x : G) * (t * x * t⁻¹) := hx.symm
    exact (mul_inv_eq_iff_eq_mul.mp e).symm
  · refine ⟨⟨⟨z, hzR⟩, rfl⟩, hb1, hb2, ?_⟩
    rintro _ ⟨x, rfl⟩ hsq
    have h1 : φ (x * x) = 1 := by rw [map_mul]; exact hsq
    have h2 : x * x = 1 := hφinj (by rw [h1, map_one])
    have h3 : (x : G) * (x : G) = 1 := congrArg Subtype.val h2
    rcases hz.unique x (hRK x.2) h3 with h' | h'
    · left
      have : x = 1 := Subtype.ext h'
      rw [this, map_one]
    · right
      have : x = ⟨z, hzR⟩ := Subtype.ext h'
      rw [this]
      rfl
  · have : Nat.card φ.range = Nat.card R :=
      Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm
    omega

theorem MinCex.exists_delta (h : E187Hyps p f) (c : MinCex p f Ω K S R W H) {z t : G}
    (hz : IsUniqueInvolution K z) (hzW : z ∈ W) (ht2 : t * t = 1)
    (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t) :
    ∃ B : Subgroup G, ∃ b : G, B ≤ (S : Subgroup G) ∧ B ≤ Subgroup.centralizer ({t} : Set G) ∧
      IsUniqueInvolution B b ∧ 8 ≤ Nat.card B ∧ b = z * (t * z * t⁻¹) ∧ b ∈ W ∧
      Subgroup.centralizer ({b} : Set G) ≤ H := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  exact E187C.exists_delta_of hΩ.conjInvariant (fun hR => hΩ.eight_le_of_mem_RSet hp hR)
    (fun hK hJ hKJ hA hAK hAJ => hΩ.card_le_two_of_le_inf hK hJ hKJ hA hAK hAJ)
    (fun hK hR hRK => hΩ.isSylow2In_of_mem_RSet_of_le hp hK hR hRK)
    (fun hK hJ hKJ hz hAJ hA2 hA3 hAc =>
      hΩ.le_normalizer_of_le_centralizer hp hq hK hJ hKJ hz hAJ hA2 hA3 hAc)
    (fun hR' hR'S hne => h.l67 hp hq G Ω hΩ S R hRR _ hR' hRS hR'S hne)
    (fun hJ hR₂ hR₂J hcomm a ha _ ha1 ha2 =>
      c.hyp.cent K ⟨c.stand.mem, z, hz, hz⟩ _ hJ R _ hRR hRK hR₂ hR₂J (Or.inl hcomm) a ha ha1 ha2)
    c.stand.mem hRR hRK hRS c.stand.hW.2.2 hz hzW ht2 htS hnc

end CFSG.ClassicalInvolution.Asc77
