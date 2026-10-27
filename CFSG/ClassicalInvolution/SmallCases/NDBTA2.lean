module

public import CFSG.ClassicalInvolution.SmallCases.NDBTA1
public import CFSG.ClassicalInvolution.SmallCases.NDBH2T5
public import CFSG.ClassicalInvolution.Asc77.WP3SCUNGa
public import CFSG.ClassicalInvolution.Asc77.WP3ChainVRank3
public import CFSG.ClassicalInvolution.Asc77.WP3ChainVToral
public import CFSG.ClassicalInvolution.Q3.TL3Lift
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ComponentClassification
open scoped MatrixGroups

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace TA

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem nonempty_equiv_sl2_modelUniv {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m e : ℕ}
    (ht : t = .PSL) (hm : m = 2) :
    Nonempty ((Generic.modelUniv t m p e Fact.out).K ≃* SL(2, GaloisField p e)) := by
  subst ht hm
  exact ⟨MulEquiv.refl _⟩

theorem nonempty_sl2_equiv_of_eq {e e' : ℕ} (h : e = e') :
    Nonempty (SL(2, GaloisField p e) ≃* SL(2, GaloisField p e')) := by
  subst h
  exact ⟨MulEquiv.refl _⟩

theorem nonempty_equiv_sl2_of_A1 {Ω : Set (Subgroup G)} {z : G} (C : Asc77.XCtx p f Ω z)
    (j : Fin C.D.card) (hj : C.D.tag j = .PSL ∧ C.D.rank j = 2) :
    Nonempty ((compModel C.D j).K ≃* SL(2, GaloisField p f)) := by
  obtain ⟨E₁⟩ := nonempty_equiv_sl2_modelUniv (p := p) (e := C.D.exp j) hj.1 hj.2
  obtain ⟨E₂⟩ := nonempty_sl2_equiv_of_eq (p := p) (C.exp_eq j (by rw [hj.1]; decide))
  exact ⟨E₁.trans E₂⟩

theorem exists_partner_at_z (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hΩ : ConjInvariant (𝒞 K)) {M : Subgroup G} (hM : M ∈ 𝒞 K)
    {x : G} (hx : IsClassicalMember p f M x) {L : Subgroup G} (hL : L ∈ 𝒞 K) {l : G}
    (hl : IsClassicalMember p f L l) (hlx : l ≠ x) (hc : l * x = x * l)
    (hLx : L ∉ tqMembers (𝒞 K) x) :
    ∃ g : G, g * z * g⁻¹ ≠ z ∧ g * z * g⁻¹ * z = z * (g * z * g⁻¹) ∧
      conjSub g K ∉ tqMembers (𝒞 K) z := by
  obtain ⟨k, rfl⟩ := hM
  obtain ⟨h, rfl⟩ := hL
  have hxk : x = k * z * k⁻¹ :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hx).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq (hz.conj k))
  have hlh : l = h * z * h⁻¹ :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hl).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq (hz.conj h))
  subst hxk hlh
  refine ⟨k⁻¹ * h, fun e => hlx ?_, ?_, fun hmem => hLx ?_⟩
  · calc h * z * h⁻¹ = k * ((k⁻¹ * h) * z * (k⁻¹ * h)⁻¹) * k⁻¹ := by group
      _ = k * z * k⁻¹ := by rw [e]
  · calc (k⁻¹ * h) * z * (k⁻¹ * h)⁻¹ * z = k⁻¹ * ((h * z * h⁻¹) * (k * z * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * z * k⁻¹) * (h * z * h⁻¹)) * k := by rw [hc]
      _ = z * ((k⁻¹ * h) * z * (k⁻¹ * h)⁻¹) := by group
  · rw [tqMembers_conj hΩ k z]
    exact ⟨conjSub (k⁻¹ * h) K, hmem, by rw [← conjSub_mul, mul_inv_cancel_left]⟩

theorem mem_normalizer_of_noTwin (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hnt : ¬ HasTwin p f K z) {L : Subgroup G} (hL : L ∈ 𝒞 K)
    {l : G} (hl : IsClassicalMember p f L l) :
    Subgroup.centralizer ({l} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro c hc
  have hcl : c * l * c⁻¹ = l := Bootstrap.conj_eq_of_mem_centralizer_singleton hc
  have hcL : conjSub c L ∈ 𝒞 K := by
    obtain ⟨k, rfl⟩ := hL
    exact ⟨c * k, conjSub_mul _ _ _⟩
  have h1 := hl.conj c
  rw [hcl] at h1
  exact mem_normalizer_iff_conjSub_eq.mpr
    (NDBH2.eq_of_isClassicalMember hp hq hz hnt hcL hL h1 hl)

theorem mem_tqMembers_symm (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaMod p f Ω) {A B : Subgroup G} {a b : G} (hA : A ∈ Ω) (hB : B ∈ Ω)
    (ha : IsClassicalMember p f A a) (hb : IsClassicalMember p f B b) (hba : b ≠ a)
    (h : B ∈ tqMembers Ω a) : A ∈ tqMembers Ω b := by
  have h1 : B ∈ omegaNbr Ω A := NDBG.mem_omegaNbr_of_tq hp hq hΩ hA
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq ha) h hb hba
  have h2 : A ∈ omegaNbr Ω B := T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hA hB h1
  exact NDBH2.mem_tqMembers_of_mem_omegaNbr hp hq hΩ hB h2 hb

theorem not_mem_tqMembers_of_partner {K : Subgroup G} {z : G} (C : Asc77.XCtx p f (𝒞 K) z)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) (hz : IsClassicalMember p f K z)
    (hnt : ¬ HasTwin p f K z) {L : Subgroup G} (hL : L ∈ 𝒞 K) {l : G}
    (hl : IsClassicalMember p f L l) (hlz : l ≠ z) (hcl : l * z = z * l)
    (hLz : L ∉ tqMembers (𝒞 K) z) {M : Subgroup G} (hM : M ∈ 𝒞 K) {x : G}
    (hx : IsClassicalMember p f M x) (hKx : K ∈ tqMembers (𝒞 K) x) :
    L ∉ tqMembers (𝒞 K) x := by
  intro hLx
  have hp := C.hp
  have hq := C.hq
  obtain ⟨k, rfl⟩ := hM
  have hxk : x = k * z * k⁻¹ :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hx).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq (hz.conj k))
  subst hxk
  have hΩ := C.hΩ.conjInvariant
  have hK₁ : conjSub k⁻¹ K ∈ tqMembers (𝒞 K) z := by
    rw [tqMembers_conj hΩ k z] at hKx
    obtain ⟨K₁, hK₁, e⟩ := hKx
    have e' : conjSub k⁻¹ K = K₁ := by rw [← e, conjSub_inv_conjSub]
    rw [e']
    exact hK₁
  have hL₁ : conjSub k⁻¹ L ∈ tqMembers (𝒞 K) z := by
    rw [tqMembers_conj hΩ k z] at hLx
    obtain ⟨L₁, hL₁, e⟩ := hLx
    have e' : conjSub k⁻¹ L = L₁ := by rw [← e, conjSub_inv_conjSub]
    rw [e']
    exact hL₁
  have hz₁ : IsClassicalMember p f (conjSub k⁻¹ K) (k⁻¹ * z * k) := by
    have h1 := hz.conj k⁻¹
    rwa [inv_inv] at h1
  have hl₁ : IsClassicalMember p f (conjSub k⁻¹ L) (k⁻¹ * l * k) := by
    have h1 := hl.conj k⁻¹
    rwa [inv_inv] at h1
  have hz₁C := C.involution_mem_centralizer hK₁ hz₁
  have hl₁C := C.involution_mem_centralizer hL₁ hl₁
  have hc₁ : k⁻¹ * z * k * (k⁻¹ * l * k) = k⁻¹ * l * k * (k⁻¹ * z * k) := by
    calc k⁻¹ * z * k * (k⁻¹ * l * k) = k⁻¹ * (z * l) * k := by group
      _ = k⁻¹ * (l * z) * k := by rw [hcl]
      _ = k⁻¹ * l * k * (k⁻¹ * z * k) := by group
  obtain ⟨j₁, e₁⟩ := NDBG.exists_range_eq C hall hK₁
  obtain ⟨j₂, e₂⟩ := NDBG.exists_range_eq C hall hL₁
  have u₁ := C.isUniqueInvolution_modOdd hK₁ hz₁
  have u₂ := C.isUniqueInvolution_modOdd hL₁ hl₁
  by_cases hj : j₁ = j₂
  · subst hj
    rw [e₁] at u₁
    rw [e₂] at u₂
    apply hlz
    have h1 := Asc77.eq_of_oddQuotMk_eq' hz₁C hl₁C hz₁.isCentralInvolution.sq
      hl₁.isCentralInvolution.sq hc₁ (u₁.eq u₂)
    calc l = k * (k⁻¹ * l * k) * k⁻¹ := by group
      _ = k * (k⁻¹ * z * k) * k⁻¹ := by rw [h1]
      _ = z := by group
  · have hcomm : ∀ y ∈ modOdd z (exactCore z (conjSub k⁻¹ L)),
        oddQuotMk z ⟨k⁻¹ * z * k, hz₁C⟩ * y = y * oddQuotMk z ⟨k⁻¹ * z * k, hz₁C⟩ := by
      intro y hy
      rw [e₂] at hy
      have hzm : oddQuotMk z ⟨k⁻¹ * z * k, hz₁C⟩ ∈ (C.psi j₁).range := by
        rw [← e₁]
        exact u₁.mem
      obtain ⟨a, ha⟩ := hzm
      obtain ⟨b, rfl⟩ := hy
      rw [← ha]
      exact C.psi_commute hj a b
    have hz₁N : k⁻¹ * z * k ∈ Subgroup.normalizer (conjSub k⁻¹ L : Set G) :=
      mem_normalizer_of_noTwin hp hq hz hnt hL₁.1 hl₁
        (Subgroup.mem_centralizer_singleton_iff.mpr hc₁)
    have htq := Asc77.mem_trivialOnQuot_of_centralizes_modOdd hl₁ C.hc2 hL₁.2 hz₁C hz₁N hcomm
    apply hLz
    refine ⟨hL, ?_⟩
    have h1 := trivialOnQuot_conjSub htq k
    rwa [conjSub_conjSub_inv, show k * (k⁻¹ * z * k) * k⁻¹ = z by group] at h1

theorem caseA_or_caseB {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {z : G}
    {N N' : Subgroup G} (hN : N ∈ tqMembers Ω z) {n : G} (hn : IsClassicalMember p f N n)
    (hnz : n ≠ z)
    (hshape : ∀ M ∈ tqMembers Ω z, ∀ m : G, IsClassicalMember p f M m → m ≠ z →
      modOdd z (exactCore z M) = modOdd z (exactCore z N) ∨
        modOdd z (exactCore z M) = modOdd z (exactCore z N'))
    {l : G} (hl : l ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub (oddQuotMk z ⟨l, hl⟩) (modOdd z (exactCore z N)) = modOdd z (exactCore z N) ∨
      conjSub (oddQuotMk z ⟨l, hl⟩) (modOdd z (exactCore z N)) =
        modOdd z (exactCore z N') := by
  have hlz : l * z * l⁻¹ = z := Bootstrap.conj_eq_of_mem_centralizer_singleton hl
  have hM : conjSub l N ∈ tqMembers Ω z := conjSub_mem_tqMembers hΩ hl hN
  have hmz : l * n * l⁻¹ ≠ z := by
    intro h
    apply hnz
    calc n = l⁻¹ * (l * n * l⁻¹) * l := by group
      _ = l⁻¹ * (l * z * l⁻¹) * l := by rw [h, hlz]
      _ = z := by group
  have himg : modOdd z (exactCore z (conjSub l N)) =
      conjSub (oddQuotMk z ⟨l, hl⟩) (modOdd z (exactCore z N)) := by
    have h1 := exactCore_conjSub l z N
    rw [hlz] at h1
    rw [h1, modOdd_conjSub_of_mem_centralizer hl]
  rw [← himg]
  exact hshape _ hM _ (hn.conj l) hmz

theorem mem_trivialOnQuot_of_caseB {Ω : Set (Subgroup G)} {z : G} (C : Asc77.XCtx p f Ω z)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) {N N' : Subgroup G}
    (hN : N ∈ tqMembers Ω z) (hN' : N' ∈ tqMembers Ω z) {n n' : G}
    (hn : IsClassicalMember p f N n) (hn' : IsClassicalMember p f N' n') (hnz : n ≠ z)
    (hn'z : n' ≠ z) (hne : modOdd z (exactCore z N') ≠ modOdd z (exactCore z N))
    (hprod : ∃ (h : n ∈ Subgroup.centralizer ({z} : Set G))
      (h' : n' ∈ Subgroup.centralizer ({z} : Set G)),
      oddQuotMk z ⟨n, h⟩ * oddQuotMk z ⟨n', h'⟩ = oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩)
    {L : Subgroup G} {l : G} (hL : IsClassicalMember p f L l)
    (hlC : l ∈ Subgroup.centralizer ({z} : Set G))
    (hCl : Subgroup.centralizer ({l} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hB : conjSub (oddQuotMk z ⟨l, hlC⟩) (modOdd z (exactCore z N)) =
      modOdd z (exactCore z N')) :
    z ∈ trivialOnQuot L := by
  classical
  have hs := NDBH2.axisSeed_of_triangle C hall hN hN' hn hn' hnz hn'z hne hprod
  obtain ⟨hnC, hn'C, hpr⟩ := hprod
  obtain ⟨j, eN⟩ := NDBG.exists_range_eq C hall hN
  obtain ⟨E⟩ := nonempty_equiv_sl2_of_A1 C j (hall j)
  have hl2 : oddQuotMk z ⟨l, hlC⟩ * oddQuotMk z ⟨l, hlC⟩ = 1 := by
    rw [← map_mul]
    have e : (⟨l, hlC⟩ * ⟨l, hlC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
      Subtype.ext hL.isCentralInvolution.sq
    rw [e, map_one]
  have un : IsUniqueInvolution (modOdd z (exactCore z N)) (oddQuotMk z ⟨n, hnC⟩) :=
    C.isUniqueInvolution_modOdd hN hn
  have un' : IsUniqueInvolution (modOdd z (exactCore z N')) (oddQuotMk z ⟨n', hn'C⟩) :=
    C.isUniqueInvolution_modOdd hN' hn'
  set lb : OddQuot z := oddQuotMk z ⟨l, hlC⟩ with hlb
  have hinv : lb⁻¹ = lb := inv_eq_of_mul_eq_one_right hl2
  set ψ : SL(2, GaloisField p f) →* OddQuot z := (C.psi j).comp E.symm.toMonoidHom with hψdef
  have hψ : ∀ a, ψ a ∈ modOdd z (exactCore z N) := fun a => by
    rw [eN]
    exact ⟨E.symm a, rfl⟩
  have hψ' : ∀ a, lb * ψ a * lb⁻¹ ∈ modOdd z (exactCore z N') := fun a => by
    rw [← hB]
    exact Generic.conj_mem_conjSub (hψ a)
  have hcomm : ∀ a b, ψ b * (lb * ψ a * lb⁻¹) = lb * ψ a * lb⁻¹ * ψ b :=
    fun a b => hs.comm₂₃ _ (hψ b) _ (hψ' a)
  let σ : SL(2, GaloisField p f) →* OddQuot z :=
    MonoidHom.mk' (fun a => ψ a * (lb * ψ a * lb⁻¹)) fun a b => by
      simp only [map_mul]
      calc ψ a * ψ b * (lb * (ψ a * ψ b) * lb⁻¹)
          = ψ a * (ψ b * (lb * ψ a * lb⁻¹)) * (lb * ψ b * lb⁻¹) := by group
        _ = ψ a * (lb * ψ a * lb⁻¹ * ψ b) * (lb * ψ b * lb⁻¹) := by rw [hcomm a b]
        _ = ψ a * (lb * ψ a * lb⁻¹) * (ψ b * (lb * ψ b * lb⁻¹)) := by group
  have hσ : ∀ a, σ a = ψ a * (lb * ψ a * lb⁻¹) := fun a => rfl
  have hσt : ∀ a, σ a * lb = lb * σ a := by
    intro a
    rw [hσ]
    calc ψ a * (lb * ψ a * lb⁻¹) * lb = ψ a * lb * ψ a := by group
      _ = ψ a * lb⁻¹ * ψ a := by rw [hinv]
      _ = lb * lb * ψ a * lb⁻¹ * ψ a := by rw [hl2, one_mul]
      _ = lb * (lb * ψ a * lb⁻¹ * ψ a) := by group
      _ = lb * (ψ a * (lb * ψ a * lb⁻¹)) := by rw [← hcomm a a]
  have hσz : oddQuotMk z ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈ σ.range := by
    have hconj := un.conj lb
    rw [hB] at hconj
    have hn' : lb * oddQuotMk z ⟨n, hnC⟩ * lb⁻¹ = oddQuotMk z ⟨n', hn'C⟩ := hconj.eq un'
    have hmem : oddQuotMk z ⟨n, hnC⟩ ∈ (C.psi j).range := by
      rw [← eN]
      exact un.mem
    obtain ⟨k, hk⟩ := hmem
    have hψk : ψ (E k) = oddQuotMk z ⟨n, hnC⟩ := by
      show C.psi j (E.symm (E k)) = _
      rw [E.symm_apply_apply]
      exact hk
    refine ⟨E k, ?_⟩
    rw [hσ, hψk, hn']
    exact hpr
  exact mem_trivialOnQuot_of_sl2_cent C.hp C.hq hL C.hz2 hlC hCl σ hσt hσz

end TA

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TriangleA2CaseA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → Disconnected.DConnected (𝒞 K) →
      (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) →
      ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, (∀ i, D.tag i = .PSL ∧ D.rank i = 2) →
      ∀ N ∈ tqMembers (𝒞 K) z, ∀ n : G, IsClassicalMember p f N n → n ≠ z →
        ¬ HasTwin p f K z → ∀ N' ∈ tqMembers (𝒞 K) z, ∀ n' : G, IsClassicalMember p f N' n' →
          n' ≠ z → modOdd z (exactCore z N') ≠ modOdd z (exactCore z N) →
          (∃ (h : n ∈ Subgroup.centralizer ({z} : Set G))
            (h' : n' ∈ Subgroup.centralizer ({z} : Set G)),
            oddQuotMk z ⟨n, h⟩ * oddQuotMk z ⟨n', h'⟩ = oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩) →
          (∀ M ∈ tqMembers (𝒞 K) z, ∀ m : G, IsClassicalMember p f M m → m ≠ z →
            modOdd z (exactCore z M) = modOdd z (exactCore z N) ∨
              modOdd z (exactCore z M) = modOdd z (exactCore z N')) →
          ∀ g : G, g * z * g⁻¹ ≠ z →
          ∀ (hl : g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G))
            (hl' : g⁻¹ * z * g ∈ Subgroup.centralizer ({z} : Set G)),
          (∀ x ∈ ({z, n, n'} : Set G),
            conjSub g K ∉ tqMembers (𝒞 K) x ∧ conjSub g⁻¹ K ∉ tqMembers (𝒞 K) x) →
          conjSub (oddQuotMk z ⟨g * z * g⁻¹, hl⟩) (modOdd z (exactCore z N)) =
            modOdd z (exactCore z N) →
          conjSub (oddQuotMk z ⟨g⁻¹ * z * g, hl'⟩) (modOdd z (exactCore z N)) =
            modOdd z (exactCore z N) → False

variable {p f}

theorem triangleA2Partner_of_caseA (h : TriangleA2CaseA p f) : TriangleA2Partner p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz hT N' hN' n' hn' hn'z
    hne hprod hshape hA2
  let C := Cover.toXCtx hnab hp2 hq hz hBelow D
  have hall' : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2 := hall
  have hΩ : HypOmegaMod p f (𝒞 K) := C.hΩ
  have hKK : K ∈ 𝒞 K := mem_conjClass_self K
  obtain ⟨x, hx, L, hL, l, hl, hlx, hc, hLx⟩ := hA2
  obtain ⟨M, hM, hMx⟩ : ∃ M ∈ 𝒞 K, IsClassicalMember p f M x := by
    rcases hx with e | e | e
    · exact ⟨K, hKK, by rw [e]; exact hz⟩
    · exact ⟨N, hN.1, by rw [e]; exact hn⟩
    · exact ⟨N', hN'.1, by rw [e]; exact hn'⟩
  obtain ⟨g, hgz, hgc, hgK⟩ :=
    TA.exists_partner_at_z hp2 hq hz hΩ.conjInvariant hM hMx hL hl hlx hc hLx
  have hl₁C : g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgc
  have hgc' : g⁻¹ * z * g * z = z * (g⁻¹ * z * g) := by
    calc g⁻¹ * z * g * z = g⁻¹ * (z * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹ * z) * g := by rw [hgc]
      _ = z * (g⁻¹ * z * g) := by group
  have hl₂C : g⁻¹ * z * g ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgc'
  have hgz' : g⁻¹ * z * g ≠ z := by
    intro e
    apply hgz
    calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [e]
      _ = z := by group
  have hL₁ : conjSub g K ∈ 𝒞 K := ⟨g, rfl⟩
  have hL₂ : conjSub g⁻¹ K ∈ 𝒞 K := ⟨g⁻¹, rfl⟩
  have hl₁ : IsClassicalMember p f (conjSub g K) (g * z * g⁻¹) := hz.conj g
  have hl₂ : IsClassicalMember p f (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
    have h1 := hz.conj g⁻¹
    rwa [inv_inv] at h1
  have hgK' : conjSub g⁻¹ K ∉ tqMembers (𝒞 K) z := by
    intro hmem
    apply hgK
    refine TA.mem_tqMembers_symm hp2 hq hΩ hL₁ hKK hl₁ hz (Ne.symm hgz) ?_
    rw [tqMembers_conj hΩ.conjInvariant g z]
    exact ⟨_, hmem, conjSub_conjSub_inv g K⟩
  have hKn : K ∈ tqMembers (𝒞 K) n := TA.mem_tqMembers_symm hp2 hq hΩ hKK hN.1 hz hn hnz hN
  have hKn' : K ∈ tqMembers (𝒞 K) n' :=
    TA.mem_tqMembers_symm hp2 hq hΩ hKK hN'.1 hz hn' hn'z hN'
  have hpart : ∀ x ∈ ({z, n, n'} : Set G),
      conjSub g K ∉ tqMembers (𝒞 K) x ∧ conjSub g⁻¹ K ∉ tqMembers (𝒞 K) x := by
    intro y hy
    rcases hy with e | e | e
    · rw [e]
      exact ⟨hgK, hgK'⟩
    · rw [e]
      exact ⟨TA.not_mem_tqMembers_of_partner C hall' hz hT hL₁ hl₁ hgz hgc hgK hN.1 hn hKn,
        TA.not_mem_tqMembers_of_partner C hall' hz hT hL₂ hl₂ hgz' hgc' hgK' hN.1 hn hKn⟩
    · rw [e]
      exact ⟨TA.not_mem_tqMembers_of_partner C hall' hz hT hL₁ hl₁ hgz hgc hgK hN'.1 hn' hKn',
        TA.not_mem_tqMembers_of_partner C hall' hz hT hL₂ hl₂ hgz' hgc' hgK' hN'.1 hn' hKn'⟩
  have hA₁ : conjSub (oddQuotMk z ⟨g * z * g⁻¹, hl₁C⟩) (modOdd z (exactCore z N)) =
      modOdd z (exactCore z N) := by
    rcases TA.caseA_or_caseB hΩ.conjInvariant hN hn hnz hshape hl₁C with hA | hB
    · exact hA
    · exact (hgK ⟨hL₁, TA.mem_trivialOnQuot_of_caseB C hall' hN hN' hn hn' hnz hn'z hne hprod
        hl₁ hl₁C (TA.mem_normalizer_of_noTwin hp2 hq hz hT hL₁ hl₁) hB⟩).elim
  have hA₂ : conjSub (oddQuotMk z ⟨g⁻¹ * z * g, hl₂C⟩) (modOdd z (exactCore z N)) =
      modOdd z (exactCore z N) := by
    rcases TA.caseA_or_caseB hΩ.conjInvariant hN hn hnz hshape hl₂C with hA | hB
    · exact hA
    · exact (hgK' ⟨hL₂, TA.mem_trivialOnQuot_of_caseB C hall' hN hN' hn hn' hnz hn'z hne hprod
        hl₂ hl₂C (TA.mem_normalizer_of_noTwin hp2 hq hz hT hL₂ hl₂) hB⟩).elim
  exact h G hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz hT N' hN' n' hn' hn'z hne
    hprod hshape g hgz hl₁C hl₂C hpart hA₁ hA₂

end CFSG.ClassicalInvolution.NDB
