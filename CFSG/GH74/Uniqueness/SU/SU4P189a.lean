module

public import CFSG.GH74.Uniqueness.SU.SU4Quot2
public import CFSG.GH74.Uniqueness.SU.SU4L185
public import CFSG.GH74.Uniqueness.SU.KInputs

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup CFSG.Blueprint

theorem eq_one_or_eq_of_sq_of_isCyclic {C : Type} [Group C] [Finite C] [IsCyclic C] {a b : C}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) : b = 1 ∨ b = a := by
  classical
  have : Fintype C := Fintype.ofFinite C
  by_contra h
  push Not at h
  have hcard := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset C) ⊆ Finset.univ.filter (fun x : C => x ^ 2 = 1) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hy with rfl | rfl | rfl
    · simp
    · exact ha
    · exact hb
  have h3 : ({1, a, b} : Finset C).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, a, b, ha1.symm, h.1.symm, h.2.symm, rfl⟩
  have := Finset.card_le_card hsub
  omega

theorem thompson_cyclic_hom {G : Type} [Group G] [Finite G] {S : Sylow 2 G} (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) {C : Type} [Group C] [Finite C] [IsCyclic C]
    (φ : ↥(S : Subgroup G) →* C) {Q : Subgroup G} (hQS : Q ≤ (S : Subgroup G))
    (hQ : ∀ t : ↥(S : Subgroup G), (t : G) ∈ Q ↔ φ t = 1) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsQ : s ∉ Q) (hs2 : s * s = 1) :
    ∃ g : G, g⁻¹ * s * g ∈ Q ∧ ∀ c ∈ (S : Subgroup G) ⊓ centralizer ({s} : Set G),
      g⁻¹ * c * g ∈ (S : Subgroup G) ⊓ centralizer ({g⁻¹ * s * g} : Set G) := by
  have hQn : ∀ t ∈ (S : Subgroup G), ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro t ht q hq
    have hq1 : φ ⟨q, hQS hq⟩ = 1 := (hQ ⟨q, hQS hq⟩).mp hq
    have hmem : t * q * t⁻¹ ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ht (hQS hq))
        ((S : Subgroup G).inv_mem ht)
    refine (hQ ⟨t * q * t⁻¹, hmem⟩).mpr ?_
    have : (⟨t * q * t⁻¹, hmem⟩ : ↥(S : Subgroup G)) =
        ⟨t, ht⟩ * ⟨q, hQS hq⟩ * ⟨t, ht⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hq1]
    simp
  have hcyc : ∃ b ∈ (S : Subgroup G), ∀ t ∈ (S : Subgroup G), ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Q := by
    obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := ↥φ.range)
    obtain ⟨b, hb⟩ := g₀.2
    refine ⟨(b : G), b.2, fun t ht => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ ⟨φ ⟨t, ht⟩, ⟨_, rfl⟩⟩)
    have hk' : (g₀ : C) ^ k = φ ⟨t, ht⟩ := congrArg Subtype.val hk
    refine ⟨k, (hQ ⟨((b : G) ^ k)⁻¹ * t, (S : Subgroup G).mul_mem
      ((S : Subgroup G).inv_mem ((S : Subgroup G).zpow_mem b.2 k)) ht⟩).mpr ?_⟩
    have : (⟨((b : G) ^ k)⁻¹ * t, (S : Subgroup G).mul_mem
        ((S : Subgroup G).inv_mem ((S : Subgroup G).zpow_mem b.2 k)) ht⟩ : ↥(S : Subgroup G)) =
        (b ^ k)⁻¹ * ⟨t, ht⟩ := rfl
    rw [this, map_mul, map_inv, map_zpow, hb, hk']
    simp
  have hb2 : ∀ (g : G) (k : ℕ), g⁻¹ * s ^ (2 * k) * g ∈ (S : Subgroup G) →
      g⁻¹ * s ^ (2 * k) * g ∈ Q := by
    intro g k _
    have : s ^ (2 * k) = 1 := by rw [pow_mul, pow_two, hs2, one_pow]
    rw [this]; simp
  have hσ2 : φ ⟨s, hsS⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨s, hsS⟩ : ↥(S : Subgroup G)) ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact hs2)
    rw [this, map_one]
  have hσ : φ ⟨s, hsS⟩ ≠ 1 := fun h => hsQ ((hQ ⟨s, hsS⟩).mpr h)
  have hc : ∀ g : G, g⁻¹ * s * g ∈ (S : Subgroup G) →
      CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 (S : Subgroup G) (g⁻¹ * s * g) →
        g⁻¹ * s * g ∈ Q ∨ s⁻¹ * (g⁻¹ * s * g) ∈ Q := by
    intro g hg _
    have hw2 : (⟨g⁻¹ * s * g, hg⟩ : ↥(S : Subgroup G)) ^ 2 = 1 := by
      apply Subtype.ext
      show (g⁻¹ * s * g) ^ 2 = 1
      calc (g⁻¹ * s * g) ^ 2 = g⁻¹ * (s * s) * g := by rw [pow_two]; group
        _ = 1 := by rw [hs2]; group
    have hω2 : φ ⟨g⁻¹ * s * g, hg⟩ ^ 2 = 1 := by rw [← map_pow, hw2, map_one]
    rcases eq_one_or_eq_of_sq_of_isCyclic hσ2 hω2 hσ with h | h
    · left
      exact (hQ ⟨g⁻¹ * s * g, hg⟩).mpr h
    · right
      have hmem : s⁻¹ * (g⁻¹ * s * g) ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hsS) hg
      refine (hQ ⟨s⁻¹ * (g⁻¹ * s * g), hmem⟩).mpr ?_
      have : (⟨s⁻¹ * (g⁻¹ * s * g), hmem⟩ : ↥(S : Subgroup G)) =
          ⟨s, hsS⟩⁻¹ * ⟨g⁻¹ * s * g, hg⟩ := rfl
      rw [this, map_mul, map_inv, h]
      simp
  rcases CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) S.isPGroup' S.not_dvd_index
    hQn hcyc hsS hsQ hb2 hc with ⟨N, hN, hcycN, -, hsN⟩ | ⟨g, hg, -, hcg⟩
  · exfalso
    rcases hs.eq_bot_or_eq_top_of_normal N with h0 | h0
    · obtain ⟨a, b, hab⟩ := hn
      obtain ⟨g₀, hg₀⟩ := hcycN.exists_generator
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ (QuotientGroup.mk a))
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ (QuotientGroup.mk b))
      have hcomm : (QuotientGroup.mk (a * b) : G ⧸ N) = QuotientGroup.mk (b * a) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, ← hi, ← hj]
        exact ((Commute.refl g₀).zpow_zpow i j).eq
      have := QuotientGroup.eq.mp hcomm
      rw [h0, Subgroup.mem_bot] at this
      exact hab (inv_mul_eq_one.mp this)
    · exact hsN (by rw [h0]; exact Subgroup.mem_top s)
  · exact ⟨g, hg, hcg⟩

section CaseB

variable {G : Type} [Group G] [Finite G] (M : Subgroup G)

theorem isElemAbelian_barImage {X : Subgroup G} (hX : IsPGroup 2 X) (hXM : X ≤ M)
    (hel : Open.IsElemAbelian 2 X) :
    Open.IsElemAbelian 2 (barImage M X) ∧ Nat.card (barImage M X) = Nat.card X := by
  refine ⟨?_, (Nat.card_congr (mulEquivBarImage M hX hXM).toEquiv).symm⟩
  rw [barImage_eq]
  apply isElemAbelian_map
  rw [SU1.isElemAbelian_iff] at hel ⊢
  exact ⟨fun a ha b hb => Subtype.ext (hel.1 _ ha _ hb),
    fun a ha => Subtype.ext (by rw [Subgroup.coe_pow]; exact hel.2 _ ha)⟩

omit [Finite G] in
theorem mem_normalizer_of_conjSub_eq {n : G} {E : Subgroup G} (h : conjSub n E = E) :
    n ∈ normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact mem_conjSub_of_mem hy
  · intro hy
    rw [← h, mem_conjSub] at hy
    have e : n⁻¹ * (n * y * n⁻¹) * n = y := by group
    rwa [e] at hy

theorem caseB_false_of_transfer {S : Sylow 2 G} {U M : Subgroup G} (h : Hyp184Core S U M)
    {xb : Mbar M} (_hxb2 : orderOf xb = 2)
    (hYrank : Open.pRank 2 (generalizedFitting (Mbar M) ⊔ zpowers xb) = 2)
    (hYn : (generalizedFitting (Mbar M) ⊔ zpowers xb).Normal)
    (hYcyc : IsCyclic (Mbar M ⧸ (generalizedFitting (Mbar M) ⊔ zpowers xb)))
    (hE8 : ∀ E₁ E₂ : Subgroup (Mbar M), Open.IsElemAbelian 2 E₁ → Nat.card E₁ = 8 →
      Open.IsElemAbelian 2 E₂ → Nat.card E₂ = 8 →
        ∃ h : Mbar M, E₂ = E₁.map (MulAut.conj h).toMonoidHom) :
    False := by
  have hSM : (S : Subgroup G) ≤ M := h.S_le
  set Y : Subgroup (Mbar M) := generalizedFitting (Mbar M) ⊔ zpowers xb with hYdef
  obtain ⟨E, hES, hEel, hEcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two h.rank
  have hEM : E ≤ M := hES.trans hSM
  have hEp : IsPGroup 2 E := IsPGroup.of_card hEcard
  obtain ⟨hEbel, hEbcard⟩ := isElemAbelian_barImage M hEp hEM hEel
  have hnot : ¬ barImage M E ≤ Y := by
    intro hle
    have := SU1.le_pRank (p := 2) (by norm_num) hle hEbel
      (by rw [hEbcard, hEcard] : Nat.card (barImage M E) = 2 ^ 3)
    omega
  obtain ⟨eb, hebE, hebY⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨m₀, hm₀E, hm₀⟩ := (mem_barImage M).mp hebE
  have hsE : (m₀ : G) ∈ E := hm₀E
  have hsS : (m₀ : G) ∈ (S : Subgroup G) := hES hsE
  have hs2 : (m₀ : G) * (m₀ : G) = 1 := by
    rw [← pow_two]; exact (SU1.isElemAbelian_iff.mp hEel).2 _ hsE
  have hYnorm : Y.Normal := hYn
  let Qg : Subgroup G := (S : Subgroup G) ⊓ (Y.comap (proj M)).map M.subtype
  have hQmem : ∀ t : ↥M, (t : G) ∈ Qg ↔ (t : G) ∈ (S : Subgroup G) ∧ proj M t ∈ Y := by
    intro t
    simp only [Qg, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap]
    constructor
    · rintro ⟨hS', t', ht', htt'⟩
      have : t' = t := Subtype.ext htt'
      exact ⟨hS', this ▸ ht'⟩
    · rintro ⟨hS', hY⟩
      exact ⟨hS', t, hY, rfl⟩
  have hQS : Qg ≤ (S : Subgroup G) := inf_le_left
  let φ : ↥(S : Subgroup G) →* Mbar M ⧸ Y :=
    (QuotientGroup.mk' Y).comp ((proj M).comp (Subgroup.inclusion hSM))
  have hQφ : ∀ t : ↥(S : Subgroup G), (t : G) ∈ Qg ↔ φ t = 1 := by
    intro t
    have hφeq : φ t = QuotientGroup.mk (proj M ⟨t, hSM t.2⟩) := rfl
    rw [hQmem ⟨t, hSM t.2⟩, hφeq, QuotientGroup.eq_one_iff]
    exact ⟨fun h => h.2, fun h => ⟨t.2, h⟩⟩
  have hsQ : (m₀ : G) ∉ Qg := by
    intro hQ
    have := ((hQmem m₀).mp hQ).2
    rw [hm₀] at this
    exact hebY this
  obtain ⟨g, hgQ, hgc⟩ :=
    @thompson_cyclic_hom G _ _ S h.simple h.nonab (Mbar M ⧸ Y) _ _ hYcyc
      φ Qg hQS hQφ (m₀ : G) hsS hsQ hs2
  have hE'S : conjSub g⁻¹ E ≤ (S : Subgroup G) := by
    intro y hy
    rw [mem_conjSub] at hy
    have hyE : g * y * g⁻¹ ∈ E := by simpa using hy
    have hcs : g * y * g⁻¹ ∈ (S : Subgroup G) ⊓ centralizer ({(m₀ : G)} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hES hyE, Subgroup.mem_centralizer_singleton_iff.mpr
        ((SU1.isElemAbelian_iff.mp hEel).1 _ hyE _ hsE)⟩
    have := (Subgroup.mem_inf.mp (hgc _ hcs)).1
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this
  have hE'M : conjSub g⁻¹ E ≤ M := hE'S.trans hSM
  have hE'p : IsPGroup 2 (conjSub g⁻¹ E) := isPGroup_conjSub hEp
  obtain ⟨hEb'el, hEb'card⟩ := isElemAbelian_barImage M hE'p hE'M (isElemAbelian_conjSub hEel)
  have hE8c : Nat.card E = 8 := by rw [hEcard]; norm_num
  obtain ⟨hh, hhE⟩ := hE8 (barImage M E) (barImage M (conjSub g⁻¹ E)) hEbel
    (by rw [hEbcard, hE8c]) hEb'el (by rw [hEb'card, card_conjSub, hE8c])
  obtain ⟨m, rfl⟩ := proj_surjective M hh
  rw [barImage_conj] at hhE
  have hmE : conjSub (m : G) E ≤ M := by
    have := conjSub_mono (g := (m : G)) hEM
    rwa [conjSub_self_of_mem m.2] at this
  obtain ⟨c, hc⟩ := exists_conj_of_barImage_eq M hE'p (isPGroup_conjSub hEp) hE'M hmE hhE
  have hn : conjSub ((m : G)⁻¹ * (c : G) * g⁻¹) E = E := by
    rw [conjSub_mul, conjSub_mul, hc, conjSub_inv_conjSub]
  have hnN := mem_normalizer_of_conjSub_eq hn
  have hE2 : 2 ≤ Open.pRank 2 E := by
    have := SU1.le_pRank (p := 2) (by norm_num) le_rfl hEel hEcard
    omega
  have hE3 : 3 ≤ Open.pRank 2 (centralizer (E : Set G) ⊓ (S : Subgroup G)) := by
    refine SU1.le_pRank (p := 2) (by norm_num) (E := E) (le_inf ?_ hES) hEel hEcard
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (SU1.isElemAbelian_iff.mp hEel).1 f hf e he
  have hnM : (m : G)⁻¹ * (c : G) * g⁻¹ ∈ M :=
    h.gamma_le (normalizer_le_gammaElem hES hEel hE2 hE3 hnN)
  have hgM : g ∈ M := by
    have : g⁻¹ = (c : G)⁻¹ * (m : G) * ((m : G)⁻¹ * (c : G) * g⁻¹) := by group
    have h1 : g⁻¹ ∈ M := by
      rw [this]
      exact M.mul_mem (M.mul_mem (M.inv_mem c.2) m.2) hnM
    simpa using M.inv_mem h1
  have hsM : (m₀ : G) ∈ M := m₀.2
  have hmem' : g⁻¹ * (m₀ : G) * g ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hgM) hsM) hgM
  have hs'Y : proj M ⟨g⁻¹ * (m₀ : G) * g, hmem'⟩ ∈ Y := ((hQmem ⟨_, hmem'⟩).mp hgQ).2
  have hconj : proj M m₀ ∈ Y := by
    have h1 := hYnorm.conj_mem _ hs'Y (proj M ⟨g, hgM⟩)
    have h2 : (⟨g, hgM⟩ : ↥M) * ⟨g⁻¹ * (m₀ : G) * g, hmem'⟩ * (⟨g, hgM⟩ : ↥M)⁻¹ = m₀ := by
      apply Subtype.ext
      show g * (g⁻¹ * (m₀ : G) * g) * g⁻¹ = m₀
      group
    rwa [← map_inv, ← map_mul, ← map_mul, h2] at h1
  rw [hm₀] at hconj
  exact hebY hconj

theorem caseB_false (hKI2 : K.KI2) {S : Sylow 2 G} {U : Subgroup G} (h : Hyp184 S U M)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : LieModel ↥(generalizedFitting (Mbar M)) .PSL 2 p f) {xb : Mbar M}
    (hxb2 : orderOf xb = 2) (hPGL : K.IsPGL2 ↥(generalizedFitting (Mbar M) ⊔ zpowers xb) p f) :
    False := by
  have hGH : SU0.GHGroup (Mbar M) :=
    SU0.GHGroup.of_kgh_quotient h.kgh h.maximal.1 (pPrimeCore 2 ↥M)
  have hO : pPrimeCore 2 (Mbar M) = ⊥ := GLS.pPrimeCore_quotient_eq_bot (↥M)
  obtain ⟨hYrank, ⟨hYn, hYcyc⟩, hE8⟩ :=
    hKI2 (Mbar M) hGH hO p f hp hp2 hL xb hxb2 hPGL
  exact caseB_false_of_transfer h.toHyp184Core hxb2 hYrank hYn hYcyc hE8

end CaseB

end CFSG.GH74.Uniqueness.SU.SU4
