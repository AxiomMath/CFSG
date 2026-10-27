module

public import CFSG.GH74.Generic.BProg.B2.T3S1Abs
import CFSG.GH74.Generic.BProg.B1.PilotS1
public import CFSG.GH74.Generic.BProg.B1.Lift0
public import CFSG.GH74.Generic.BProg.B2.T1Basic
public import CFSG.GH74.Generic.BProg.B2.T3Sect13Aux
public import CFSG.GH74.Generic.BProg.B2.T3Sect13Sylow

public section

namespace CFSG.GH74.Generic.BProg.B2.T3S1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

variable {G : Type} [Group G] [Finite G]

section Quot

variable {M : Subgroup G}

theorem odd_orderOf_of_mk_eq_one (n : ↥M) (hn : QuotientGroup.mk' (pPrimeCore 2 ↥M) n = 1) :
    Odd (orderOf n) := by
  have hmem : n ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff n).1 hn
  have hdvd : orderOf n ∣ Nat.card (pPrimeCore 2 ↥M) := Subgroup.orderOf_dvd_natCard _ hmem
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥M)) := pPrimeCore_coprime_card
  exact Nat.coprime_two_left.1 (hcop.coprime_dvd_right hdvd)

theorem cent_lift {u : ↥M} (hu2 : u * u = 1) (z : Mbar M)
    (hz : z * QuotientGroup.mk' (pPrimeCore 2 ↥M) u = QuotientGroup.mk' (pPrimeCore 2 ↥M) u * z) :
    ∃ g : ↥M, g * u = u * g ∧ QuotientGroup.mk' (pPrimeCore 2 ↥M) g = z := by
  classical
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  have hfact : Fact (IsPGroup 2 ↥(zpowers u)) :=
    ⟨isPGroup_zpowers_of_pow_two_pow_eq_one (n := 1) (by simpa [pow_two] using hu2)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOn : (pPrimeCore 2 ↥M).Normal := pPrimeCore_normal
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥M)) := pPrimeCore_coprime_card
  have hcen : centralizer (((zpowers u).map ρ : Subgroup (Mbar M)) : Set (Mbar M)) =
      (centralizer ((zpowers u : Subgroup ↥M) : Set ↥M)).map ρ :=
    centralizer_map_quotient_eq_map_centralizer 2 (zpowers u) (pPrimeCore 2 ↥M) hOn hOcop
  have hmapz : (zpowers u).map ρ = zpowers (ρ u) := MonoidHom.map_zpowers _ u
  rw [hmapz] at hcen
  have hcenv : centralizer ({ρ u} : Set (Mbar M)) =
      (centralizer ({u} : Set ↥M)).map ρ := by
    have h1 : centralizer ((zpowers (ρ u) : Subgroup (Mbar M)) : Set (Mbar M)) =
        centralizer ({ρ u} : Set (Mbar M)) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h2 : centralizer ((zpowers u : Subgroup ↥M) : Set ↥M) = centralizer ({u} : Set ↥M) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [← h1, hcen, h2]
  have hz' : z ∈ centralizer ({ρ u} : Set (Mbar M)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hz
  rw [hcenv] at hz'
  obtain ⟨g, hg, hgz⟩ := hz'
  exact ⟨g, Subgroup.mem_centralizer_singleton_iff.1 hg, hgz⟩

theorem not_two_dvd_card_ker (C : Subgroup ↥M) :
    ¬ 2 ∣ Nat.card ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp C.subtype).ker := by
  have hker : ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp C.subtype).ker =
      (pPrimeCore 2 ↥M).comap C.subtype := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rw [hker]
  intro h2
  have hdvd := Subgroup.card_comap_dvd_of_injective (pPrimeCore 2 ↥M) C.subtype C.subtype_injective
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥M)) := pPrimeCore_coprime_card
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop (h2.trans hdvd)

end Quot

section Center

variable {x : G} {K A M P Q : Subgroup G}

theorem isE8_barA {K A M : Subgroup G} (hKM : K ≤ M) (hAK : A ≤ K)
    (hAel : IsElementaryAbelian 2 ↥A) (hA8 : Nat.card ↥A = 8) :
    IsE8 (((A.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M))).subgroupOf (barIn M K)) ∧
      (A.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤ barIn M K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAM : A ≤ M := hAK.trans hKM
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  have hA₀el : IsElementaryAbelian 2 ↥(A.subgroupOf M) := IsElementaryAbelian.subgroupOf hAM
  have hA₀2 : IsPGroup 2 ↥(A.subgroupOf M) := IsElementaryAbelian.isPGroup 2 _
  have hĀK : (A.subgroupOf M).map ρ ≤ barIn M K := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, mem_subgroupOf.2 (hAK (mem_subgroupOf.1 ha)), rfl⟩
  have hĀel : IsElementaryAbelian 2 ↥((A.subgroupOf M).map ρ) := IsElementaryAbelian.map ρ
  refine ⟨⟨IsElementaryAbelian.subgroupOf hĀK, ?_⟩, hĀK⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hĀK).toEquiv,
    B1.PilotS1.card_map_eq_of_inj ρ _ (Thm2Comp.eq_one_of_isPGroup hA₀2),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, hA8]

theorem x_mem_and_center (hF : S1Facts ↥(barIn M K)) (hs : Stage2Setup G x K A M P Q)
    (hKM : K ≤ M) {H : Subgroup G} (hH : IsMinSubnormalIn K M H) (hc1 : barIn M H = barIn M K)
    (hr : pRank 2 (CMbar M K) ≤ 1) (hAK : A ≤ K) :
    ∃ hxK : x ∈ K, ∀ g : ↥(barIn M K), g ∈ Subgroup.center ↥(barIn M K) ↔
      g = 1 ∨ (g : Mbar M) = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x, hKM hxK⟩ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAx, hAel, hA8, -⟩ := hs.src
  obtain ⟨z, hz1, hzc, hzE⟩ := hF.center
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  obtain ⟨hĀE8, hĀK⟩ := isE8_barA hKM hAK hAel hA8
  have hzĀ := hzE _ hĀE8
  obtain ⟨a, ha, haz⟩ : ∃ a : ↥M, a ∈ A.subgroupOf M ∧ ρ a = (z : Mbar M) := by
    have hz' : (z : Mbar M) ∈ (A.subgroupOf M).map ρ := mem_subgroupOf.1 hzĀ
    obtain ⟨a, ha, h⟩ := hz'
    exact ⟨a, ha, h⟩
  have haA : (a : G) ∈ A := mem_subgroupOf.1 ha
  have hx2 : orderOf x = 2 := hs.pair.1.1.1.1
  have hax : (a : G) = x := by
    by_contra hne
    have haC : (a : G) ∈ CMbar M K := by
      rw [Thm2Comp.mem_CMbar_iff hKM a, haz, Subgroup.mem_centralizer_iff]
      intro k hk
      have hzc' : z ∈ Subgroup.center ↥(barIn M K) := (hzc z).2 (Or.inr rfl)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc' ⟨k, hk⟩)
    have hxC : x ∈ CMbar M K := T3Rank.Q_le_CMbar hs hKM hH hc1 (x_mem_Q hs)
    have ha1 : (a : G) ≠ 1 := by
      intro h1
      apply hz1
      apply Subtype.ext
      rw [← haz, show a = 1 from Subtype.ext h1, map_one]
      rfl
    have ha2 : orderOf (a : G) = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) _ haA) ha1
    have hcomm : (a : G) * x = x * (a : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hAx haA)
    have := T3Sect13Sylow.two_le_pRank_of_commuting_involutions haC hxC ha2 hx2 hcomm hne
    omega
  have hxK : x ∈ K := hax ▸ hAK haA
  refine ⟨hxK, fun g => ?_⟩
  have hzx : (z : Mbar M) = ρ ⟨x, hKM hxK⟩ := by
    rw [← haz]
    congr 1
    exact Subtype.ext hax
  rw [hzc g]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h, hzx]
  · rintro (h | h)
    · exact Or.inl h
    · right
      exact Subtype.ext (h.trans hzx.symm)

theorem cent_invol (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M) {H : Subgroup G}
    (hH : IsMinSubnormalIn K M H) (hc1 : barIn M H = barIn M K) (hr : pRank 2 (CMbar M K) ≤ 1)
    (hxM : x ∈ M) (hxK : x ∈ K) {c : Mbar M}
    (hc : c ∈ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M))) (hcc : c * c = 1) :
    c = 1 ∨ c = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x, hxM⟩ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  set x' : ↥M := ⟨x, hxM⟩ with hx'
  have hx2 : orderOf x = 2 := hs.pair.1.1.1.1
  have hxx : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
  have hx'x' : x' * x' = 1 := Subtype.ext hxx
  have hxbK : ρ x' ∈ barIn M K := ⟨x', mem_subgroupOf.2 hxK, rfl⟩
  have hcx : c * ρ x' = ρ x' * c := (Subgroup.mem_centralizer_iff.1 hc _ hxbK).symm
  obtain ⟨g, hgx, hgc⟩ := cent_lift hx'x' c hcx
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  set g₂ : ↥M := g ^ m with hg₂def
  have hg₂ : g₂ ^ (2 ^ k) = 1 := by
    rw [hg₂def, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hcm : c ^ m = c := by
    obtain ⟨j, rfl⟩ := hm
    rw [pow_succ, pow_mul, sq, hcc, one_pow, one_mul]
  have hρg₂ : ρ g₂ = c := by rw [hg₂def, map_pow, hgc, hcm]
  have hg₂x : g₂ * x' = x' * g₂ := ((Commute.pow_left hgx m)).eq
  have hg₂sq : g₂ * g₂ = 1 := by
    have h1 : ρ (g₂ * g₂) = 1 := by rw [map_mul, hρg₂, hcc]
    have hmem : g₂ * g₂ ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 h1
    have hpow : (g₂ * g₂) ^ (2 ^ k) = 1 := by
      rw [← sq, ← pow_mul, mul_comm, pow_mul, hg₂, one_pow]
    exact eq_one_of_isPGroup_of_mem_pPrimeCore (isPGroup_zpowers_of_pow_two_pow_eq_one hpow)
      (mem_zpowers _) hmem
  by_cases hg1 : g₂ = 1
  · left
    rw [← hρg₂, hg1, map_one]
  by_cases hgxe : (g₂ : G) = x
  · right
    rw [← hρg₂]
    congr 1
    exact Subtype.ext hgxe
  exfalso
  have hgC : (g₂ : G) ∈ CMbar M K := by
    rw [Thm2Comp.mem_CMbar_iff hKM g₂, hρg₂]
    exact hc
  have hxC : x ∈ CMbar M K := T3Rank.Q_le_CMbar hs hKM hH hc1 (x_mem_Q hs)
  have hg2 : orderOf (g₂ : G) = 2 := by
    refine orderOf_eq_prime ?_ (fun h => hg1 (Subtype.ext h))
    rw [sq]
    exact congrArg Subtype.val hg₂sq
  have := T3Sect13Sylow.two_le_pRank_of_commuting_involutions hgC hxC hg2 hx2
    (congrArg Subtype.val hg₂x) hgxe
  omega

end Center

theorem exists_conj_centralized_E8 {K A M : Subgroup G} (hF : S1Facts ↥(barIn M K))
    (hKM : K ≤ M) (hAK : A ≤ K) (hAel : IsElementaryAbelian 2 ↥A) (hA8 : Nat.card ↥A = 8)
    {y : G} (hyM : y ∈ M) (hy2 : orderOf y = 2) {E₀ : Subgroup ↥(barIn M K)} (hE₀ : IsE8 E₀)
    (hc : ∀ e ∈ E₀, QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨y, hyM⟩ * (e : Mbar M) =
      (e : Mbar M) * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨y, hyM⟩) :
    ∃ u ∈ M, ∀ a ∈ A, y * (u * a * u⁻¹) = (u * a * u⁻¹) * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  have hAM : A ≤ M := hAK.trans hKM
  obtain ⟨hĀE8, hĀK⟩ := isE8_barA hKM hAK hAel hA8
  obtain ⟨kb, hkb⟩ := hF.conj _ _ hĀE8 hE₀
  obtain ⟨k', hk'K, hk'⟩ := kb.2
  set y' : ↥M := ⟨y, hyM⟩ with hy'
  have hy'2 : orderOf y' = 2 := (Subgroup.orderOf_mk y hyM).trans hy2
  have hy'p : IsPGroup 2 ↥(zpowers y') := B1.isPGroup_two_zpowers_of_orderOf hy'2
  set B : Subgroup ↥M := (A.subgroupOf M).map (MulAut.conj k').toMonoidHom with hB
  have hA2 : IsPGroup 2 ↥(A.subgroupOf M) := (IsElementaryAbelian.isPGroup 2 A).comap_subtype
  have hB2 : IsPGroup 2 ↥B := hA2.map _
  have hcomm : ∀ b ∈ B, ρ y' * ρ b = ρ b * ρ y' := by
    rintro _ ⟨a', ha', rfl⟩
    have hmem : (⟨ρ a', hĀK ⟨a', ha', rfl⟩⟩ : ↥(barIn M K)) ∈
        ((A.subgroupOf M).map ρ).subgroupOf (barIn M K) := mem_subgroupOf.2 ⟨a', ha', rfl⟩
    have hE : (MulAut.conj kb).toMonoidHom ⟨ρ a', hĀK ⟨a', ha', rfl⟩⟩ ∈ E₀ := by
      rw [hkb]
      exact Subgroup.mem_map_of_mem _ hmem
    have h1 := hc _ hE
    have h2 : (((MulAut.conj kb).toMonoidHom ⟨ρ a', hĀK ⟨a', ha', rfl⟩⟩ : ↥(barIn M K)) : Mbar M) =
        ρ ((MulAut.conj k').toMonoidHom a') := by
      have hk'' : ρ k' = (kb : Mbar M) := hk'
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
        Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hk'']
    rw [h2] at h1
    exact h1
  have hOodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) :=
    Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have := (pPrimeCore_normal : (pPrimeCore 2 ↥M).Normal)
  obtain ⟨n, hn, hnB⟩ := T3Sect13Aux.exists_conj_commute (pPrimeCore 2 ↥M) hOodd hy'p hB2 hcomm
  refine ⟨((n * k' : ↥M) : G), (n * k' : ↥M).2, fun a ha => ?_⟩
  have haM : a ∈ M := hAM ha
  have h1 := hnB (k' * ⟨a, haM⟩ * k'⁻¹) ⟨⟨a, haM⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
  have e1 : n * (k' * ⟨a, haM⟩ * k'⁻¹) * n⁻¹ = (n * k') * ⟨a, haM⟩ * (n * k')⁻¹ := by group
  rw [e1] at h1
  exact congrArg Subtype.val h1

theorem mem_normalizer_zpowers_of_conj_inv {X : Type*} [Group X] {a b : X}
    (h : b * a * b⁻¹ = a⁻¹) : b ∈ normalizer ((zpowers a : Subgroup X) : Set X) := by
  have h' : b⁻¹ * a * b = a⁻¹ := by
    have e : a = b⁻¹ * (b * a * b⁻¹) * b := by group
    rw [h] at e
    calc b⁻¹ * a * b = (b⁻¹ * a⁻¹ * b)⁻¹ := by group
      _ = a⁻¹ := by rw [← e]
  have hc : ∀ c : X, c * a * c⁻¹ = a⁻¹ → ∀ k : ℤ, c * a ^ k * c⁻¹ = a ^ (-k) := by
    intro c hc k
    have e : c * a ^ k * c⁻¹ = (c * a * c⁻¹) ^ k := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rw [e, hc, zpow_neg, inv_zpow]
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact Subgroup.mem_zpowers_iff.2 ⟨-k, (hc b h k).symm⟩
  · intro hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hg' : g = b⁻¹ * a ^ k * b⁻¹⁻¹ := by
      rw [hk]; group
    rw [hg', hc b⁻¹ (by rw [inv_inv]; exact h') k]
    exact Subgroup.zpow_mem _ (mem_zpowers a) _

@[expose] noncomputable def conjToM {x : G} {M : Subgroup G} (hCx : centralizer ({x} : Set G) ≤ M) {h : G}
    (hyM : h * x * h⁻¹ ∈ M) :
    ↥(centralizer ({(⟨h * x * h⁻¹, hyM⟩ : ↥M)} : Set ↥M)) →* ↥M :=
  MonoidHom.mk' (fun g => ⟨h⁻¹ * ((g : ↥M) : G) * h, hCx (by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hg := Subgroup.mem_centralizer_singleton_iff.1 g.2
    have hg' : ((g : ↥M) : G) * (h * x * h⁻¹) = (h * x * h⁻¹) * ((g : ↥M) : G) :=
      congrArg Subtype.val hg
    calc h⁻¹ * ((g : ↥M) : G) * h * x
        = h⁻¹ * (((g : ↥M) : G) * (h * x * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x * h⁻¹) * ((g : ↥M) : G)) * h := by rw [hg']
      _ = x * (h⁻¹ * ((g : ↥M) : G) * h) := by group)⟩)
    (fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group))

theorem transfer_mem {x : G} {K M : Subgroup G} [hN : (barIn M K).Normal]
    (hshape : ShapeModel ↥(barIn M K)) (hCx : centralizer ({x} : Set G) ≤ M) (hxM : x ∈ M)
    (hx2 : orderOf x = 2)
    (hzc : ∀ g : ↥(barIn M K), g ∈ Subgroup.center ↥(barIn M K) ↔
      g = 1 ∨ (g : Mbar M) = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x, hxM⟩)
    (hLC : ∀ g ∈ barIn M K, g ∈ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)) →
      g = 1 ∨ g = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x, hxM⟩)
    (hCinv : ∀ c ∈ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)), c * c = 1 →
      c = 1 ∨ c = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x, hxM⟩)
    (hxK : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x, hxM⟩ ∈ barIn M K)
    {h : G} (hyM : h * x * h⁻¹ ∈ M) (hy2 : orderOf (h * x * h⁻¹) = 2)
    (hcomm : (h * x * h⁻¹) * x = x * (h * x * h⁻¹))
    (hQ8 : GoodFixedQ8 (ThreeModel ↥(barIn M K))
      (MulAut.conjNormal (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨h * x * h⁻¹, hyM⟩) :
        MulAut ↥(barIn M K))) :
    QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨h⁻¹ * x * h, hCx (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc h⁻¹ * x * h * x = h⁻¹ * (x * (h * x * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * x * h⁻¹) * x) * h := by rw [hcomm]
        _ = x * (h⁻¹ * x * h) := by group)⟩ ∈ barIn M K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  set y' : ↥M := ⟨h * x * h⁻¹, hyM⟩ with hy'
  set xb : Mbar M := ρ ⟨x, hxM⟩ with hxb
  have hxx : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
  have hyy : (h * x * h⁻¹) * (h * x * h⁻¹) = 1 := by rw [← sq, ← hy2, pow_orderOf_eq_one]
  have hy'y' : y' * y' = 1 := Subtype.ext hyy
  have hxbxb : xb * xb = 1 := by rw [hxb, ← map_mul]; rw [show (⟨x, hxM⟩ : ↥M) * ⟨x, hxM⟩ = 1 from
    Subtype.ext hxx, map_one]
  obtain ⟨H₀, hfix, hgood, a, ha, b, hb, hac, ha1, hbb, hab⟩ := hQ8
  have haa : ((a * a : ↥(barIn M K)) : Mbar M) = xb := ((hzc _).1 hac).resolve_left ha1
  set aM : Mbar M := (a : Mbar M) with haM
  set bM : Mbar M := (b : Mbar M) with hbM
  have haaM : aM * aM = xb := haa
  have hbbM : bM * bM = xb := by
    rw [hbM, ← Subgroup.coe_mul, hbb]
    exact haa
  have habM : aM * bM = xb * (bM * aM) := by
    have := congrArg (fun g : ↥(barIn M K) => (g : Mbar M)) hab
    simp only [Subgroup.coe_mul] at this
    rw [haM, hbM, this, ← haa]
    simp only [Subgroup.coe_mul, mul_assoc]
  have hfixc : ∀ g ∈ H₀, (g : Mbar M) * ρ y' = ρ y' * (g : Mbar M) := by
    intro g hg
    have h1 := congrArg (fun k : ↥(barIn M K) => (k : Mbar M)) (hfix g hg)
    simp only [MulAut.conjNormal_apply] at h1
    calc (g : Mbar M) * ρ y' = (ρ y' * (g : Mbar M) * (ρ y')⁻¹) * ρ y' := by rw [h1]
      _ = ρ y' * (g : Mbar M) := by group
  have haC : aM * ρ y' = ρ y' * aM := hfixc a ha
  have hbC : bM * ρ y' = ρ y' * bM := hfixc b hb
  have ha4 : aM ^ (2 ^ 2) = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, sq aM, haaM, sq, hxbxb]
  have hb4 : bM ^ (2 ^ 2) = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, sq bM, hbbM, sq, hxbxb]
  have hbab : bM * aM * bM⁻¹ = aM⁻¹ := by
    have hxa : xb * aM = aM * xb := by rw [← haaM]; group
    have hainv : aM⁻¹ = xb * aM := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv]
      rw [mul_assoc, haaM, hxbxb]
    have h1 : bM * aM = xb * (aM * bM) := by
      rw [habM, ← mul_assoc, hxbxb, one_mul]
    calc bM * aM * bM⁻¹ = xb * (aM * bM) * bM⁻¹ := by rw [h1]
      _ = xb * aM := by group
      _ = aM⁻¹ := hainv.symm
  set E : Subgroup (Mbar M) := zpowers bM ⊔ zpowers aM with hE
  have hE2 : IsPGroup 2 ↥E :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_two_pow_eq_one hb4)
      (isPGroup_zpowers_of_pow_two_pow_eq_one ha4)
      ((Subgroup.zpowers_le).2 (mem_normalizer_zpowers_of_conj_inv hbab))
  set Cy : Subgroup ↥M := centralizer ({y'} : Set ↥M) with hCy
  set ρ' : ↥Cy →* Mbar M := ρ.comp Cy.subtype with hρ'
  have hEC : E ≤ centralizer ({ρ y'} : Set (Mbar M)) := by
    refine sup_le ((Subgroup.zpowers_le).2 ?_) ((Subgroup.zpowers_le).2 ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hbC
    · exact Subgroup.mem_centralizer_singleton_iff.2 haC
  have hErange : E ≤ ρ'.range := by
    intro e he
    obtain ⟨g, hg, hge⟩ := cent_lift hy'y' e (Subgroup.mem_centralizer_singleton_iff.1 (hEC he))
    exact ⟨⟨g, Subgroup.mem_centralizer_singleton_iff.2 hg⟩, hge⟩
  have hxCy : (⟨x, hxM⟩ : ↥M) ∈ Cy := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hcomm.symm
  set xt : ↥Cy := ⟨⟨x, hxM⟩, hxCy⟩ with hxt
  have hxt2 : xt ^ (2 ^ 1) = 1 := by
    rw [pow_one, sq]
    exact Subtype.ext (Subtype.ext hxx)
  have hxtE : ρ' xt ∈ E := by
    show xb ∈ E
    rw [← haaM]
    exact Subgroup.mem_sup_right (Subgroup.mul_mem _ (mem_zpowers aM) (mem_zpowers aM))
  obtain ⟨S, hxS, hSE, hSinj⟩ :=
    exists_lift_two ρ' (not_two_dvd_card_ker Cy) E hErange hE2 hxt2 hxtE
  have hinj : ∀ s ∈ S, ∀ s' ∈ S, ρ' s = ρ' s' → s = s' := by
    intro s hs s' hs' hss'
    have : s * s'⁻¹ = 1 := hSinj _ (S.mul_mem hs (S.inv_mem hs'))
      (by rw [map_mul, map_inv, hss', mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  obtain ⟨it, hitS, hit⟩ : ∃ it ∈ S, ρ' it = aM := by
    have : aM ∈ S.map ρ' := hSE ▸ Subgroup.mem_sup_right (mem_zpowers aM)
    obtain ⟨it, hit, h⟩ := this
    exact ⟨it, hit, h⟩
  obtain ⟨jt, hjtS, hjt⟩ : ∃ jt ∈ S, ρ' jt = bM := by
    have : bM ∈ S.map ρ' := hSE ▸ Subgroup.mem_sup_left (mem_zpowers bM)
    obtain ⟨jt, hjt, h⟩ := this
    exact ⟨jt, hjt, h⟩
  have hiit : it * it = xt := hinj _ (S.mul_mem hitS hitS) _ hxS (by rw [map_mul, hit, haaM]; rfl)
  have hjjt : jt * jt = xt := hinj _ (S.mul_mem hjtS hjtS) _ hxS (by rw [map_mul, hjt, hbbM]; rfl)
  have hijt : it * jt = xt * (jt * it) := hinj _ (S.mul_mem hitS hjtS) _
    (S.mul_mem hxS (S.mul_mem hjtS hitS)) (by
      rw [map_mul, map_mul, map_mul, hit, hjt]
      exact habM)
  set Ψ : ↥Cy →* Mbar M := ρ.comp (conjToM hCx hyM) with hΨ
  have hsolv := outerSolvableStatement ↥(barIn M K) hshape
  have hoddT := outerThreeStatement ↥(barIn M K) hshape
  have hSch : ∀ P : Subgroup (Mbar M), GoodSub (ThreeModel ↥(barIn M K)) P →
      P ≤ barIn M K ⊔ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)) :=
    goodSub_le_sup_centralizer hsolv hoddT
  have hHgood : GoodSub (ThreeModel ↥(barIn M K)) (H₀.map (barIn M K).subtype) :=
    goodSub_map _ hgood
  have hHc : ∀ g ∈ H₀.map (barIn M K).subtype, g * ρ y' = ρ y' * g := by
    rintro _ ⟨g, hg, rfl⟩
    exact hfixc g hg
  have htr := transfer_good ρ odd_orderOf_of_mk_eq_one y'
    (fun z hz => cent_lift hy'y' z hz) Ψ (ThreeModel ↥(barIn M K))
    (barIn M K ⊔ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M))) hSch
    (H₀.map (barIn M K).subtype) hHgood hHc
  have hit4 : (it : ↥M) ^ (2 ^ 2) = 1 := by
    have h1 : (it : ↥M) * (it : ↥M) = ⟨x, hxM⟩ := congrArg Subtype.val hiit
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, sq (it : ↥M), h1, sq]
    exact Subtype.ext hxx
  have hjt4 : (jt : ↥M) ^ (2 ^ 2) = 1 := by
    have h1 : (jt : ↥M) * (jt : ↥M) = ⟨x, hxM⟩ := congrArg Subtype.val hjjt
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, sq (jt : ↥M), h1, sq]
    exact Subtype.ext hxx
  have hiL := htr it ⟨a, ha, hit.symm⟩ ⟨2, hit4⟩
  have hjL := htr jt ⟨b, hb, hjt.symm⟩ ⟨2, hjt4⟩
  have hdecomp : ∀ g ∈ barIn M K ⊔ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)),
      ∃ l ∈ barIn M K, ∃ c ∈ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)),
        g = l * c := by
    intro g hg
    have hg' : g ∈ ((barIn M K ⊔ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)) :
        Subgroup (Mbar M)) : Set (Mbar M)) := hg
    rw [Subgroup.normal_mul] at hg'
    obtain ⟨l, hl, c, hc, rfl⟩ := hg'
    exact ⟨l, hl, c, hc, rfl⟩
  have hLCcomm : ∀ l ∈ barIn M K,
      ∀ c ∈ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)), l * c = c * l :=
    fun l hl c hc => Subgroup.mem_centralizer_iff.1 hc l hl
  have hxb1 : xb ≠ 1 := by
    intro h1
    have hx'2 : orderOf (⟨x, hxM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk x hxM).trans hx2
    have h2 := Thm2Comp.eq_one_of_isPGroup (B1.isPGroup_two_zpowers_of_orderOf hx'2) _
      (mem_zpowers _) h1
    rw [h2, orderOf_one] at hx'2
    omega
  have hres := mem_of_quaternion hLCcomm hxK hxb1 hLC hCinv
    (hdecomp _ hiL) (hdecomp _ hjL) (t := Ψ xt)
    (by rw [← map_mul, hiit]) (by rw [← map_mul, hjjt])
    (by rw [← map_mul, show xt * xt = 1 from Subtype.ext (Subtype.ext hxx), map_one])
    (by rw [← map_mul, ← map_mul, ← map_mul, hijt])
  exact hres

end CFSG.GH74.Generic.BProg.B2.T3S1
