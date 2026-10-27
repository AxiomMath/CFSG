module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.Open.StatedDefs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open

@[expose] def L34Fact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], StatedClassicalModel Y .PSL 3 2 2 →
    Nat.card Y = 20160 ∧
    ∀ E : Subgroup Y, IsElemAbelian 2 E → Nat.card E = 16 →
      (∀ R W : Subgroup Y, E < R → R ≤ Subgroup.normalizer (E : Set Y) → R ≤ W →
        (∀ g ∈ Subgroup.normalizer (E : Set Y), ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
          Subgroup.normalizer (E : Set Y) ≤ W) ∧
      ∀ y ∈ E, (∀ g ∈ Subgroup.normalizer (E : Set Y), g * y * g⁻¹ = y) → y = 1

section Transfer

variable {G : Type} [Group G] [Finite G]

@[expose] def L34Props (Y : Type) [Group Y] : Prop :=
  Nat.card Y = 20160 ∧
    ∀ E : Subgroup Y, IsElemAbelian 2 E → Nat.card E = 16 →
      (∀ R W : Subgroup Y, E < R → R ≤ Subgroup.normalizer (E : Set Y) → R ≤ W →
        (∀ g ∈ Subgroup.normalizer (E : Set Y), ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
          Subgroup.normalizer (E : Set Y) ≤ W) ∧
      ∀ y ∈ E, (∀ g ∈ Subgroup.normalizer (E : Set Y), g * y * g⁻¹ = y) → y = 1

omit [Finite G] in
theorem l34_card {K P : Subgroup G} {N : Subgroup ↥K} [hNn : N.Normal]
    (hN : ∀ k : ↥K, k ∈ N ↔ (k : G) ∈ P) (hPK : P ≤ K) (hY : L34Props (↥K ⧸ N)) :
    Nat.card K = 20160 * Nat.card P := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hNP : Nat.card N = Nat.card P :=
    Nat.card_congr
      { toFun := fun x => ⟨(x : ↥K), (hN _).1 x.2⟩
        invFun := fun p => ⟨⟨(p : G), hPK p.2⟩, (hN _).2 p.2⟩
        left_inv := fun x => rfl
        right_inv := fun p => rfl }
  rw [hY.1, hNP] at h1
  exact h1

theorem l34_transfer {K P Q : Subgroup G} {N : Subgroup ↥K} [hNn : N.Normal]
    (hN : ∀ k : ↥K, k ∈ N ↔ (k : G) ∈ P)
    (hPQ : P ≤ Q) (hQK : Q ≤ K) (hQe : IsElemAbelian 2 Q) (hQcard : Nat.card Q = Nat.card P * 16)
    (hY : L34Props (↥K ⧸ N)) :
    Nat.card K = 20160 * Nat.card P ∧
    (∀ R W : Subgroup G, Q < R → R ≤ K ⊓ Subgroup.normalizer (Q : Set G) → R ≤ W →
      (∀ g ∈ K ⊓ Subgroup.normalizer (Q : Set G), ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
        K ⊓ Subgroup.normalizer (Q : Set G) ≤ W) ∧
    ∀ y ∈ Q, (∀ g ∈ K ⊓ Subgroup.normalizer (Q : Set G), g * y * g⁻¹ = y) → y ∈ P := by
  classical
  set π : ↥K →* ↥K ⧸ N := QuotientGroup.mk' N with hπ
  set Q' : Subgroup ↥K := Q.subgroupOf K with hQ'
  set E : Subgroup (↥K ⧸ N) := Q'.map π with hE
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hE1 : ∀ k : ↥K, π k ∈ E ↔ (k : G) ∈ Q := by
    intro k
    constructor
    · rintro ⟨q, hq, hqk⟩
      have h1 : q⁻¹ * k ∈ N := by
        rw [← QuotientGroup.eq]
        exact hqk
      have h2 : ((q⁻¹ * k : ↥K) : G) ∈ P := (hN _).1 h1
      have h3 : (k : G) = (q : G) * ((q⁻¹ * k : ↥K) : G) := by
        simp
      rw [h3]
      exact Q.mul_mem hq (hPQ h2)
    · intro hk
      exact ⟨k, hk, rfl⟩
  have hE2 : ∀ k : ↥K, π k ∈ Subgroup.normalizer (E : Set (↥K ⧸ N)) ↔
      (k : G) ∈ Subgroup.normalizer (Q : Set G) := by
    intro k
    constructor
    · intro hk
      rw [Subgroup.mem_normalizer_iff] at hk ⊢
      intro g
      constructor
      · intro hg
        have hgK : g ∈ K := hQK hg
        have h1 := (hk (π ⟨g, hgK⟩)).1 ((hE1 ⟨g, hgK⟩).2 hg)
        have h2 : π (k * ⟨g, hgK⟩ * k⁻¹) ∈ E := by
          simpa using h1
        exact (hE1 _).1 h2
      · intro hg
        have hgK : g ∈ K := by
          have : g = (k : G)⁻¹ * ((k : G) * g * (k : G)⁻¹) * (k : G) := by group
          rw [this]
          exact K.mul_mem (K.mul_mem (K.inv_mem k.2) (hQK hg)) k.2
        have h2 : π (k * ⟨g, hgK⟩ * k⁻¹) ∈ E := (hE1 _).2 hg
        have h1 : π k * π ⟨g, hgK⟩ * (π k)⁻¹ ∈ E := by
          simpa using h2
        have := (hk (π ⟨g, hgK⟩)).2 h1
        exact (hE1 _).1 this
    · intro hk
      rw [Subgroup.mem_normalizer_iff] at hk ⊢
      intro y
      obtain ⟨k', rfl⟩ := hπs y
      have e : π k * π k' * (π k)⁻¹ = π (k * k' * k⁻¹) := by simp
      rw [e, hE1, hE1]
      exact hk (k' : G)
  have hEe : IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      show (a : ↥K ⧸ N) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact IsElemAbelian.comm hQe ha' hb'
    · obtain ⟨x', hx', rfl⟩ := hx
      rw [← map_pow]
      have : x' ^ 2 = 1 := by
        apply Subtype.ext
        simpa using hQe.2 (x' : G) hx'
      rw [this, map_one]
  have hEcard : Nat.card E = 16 := by
    let φ : ↥Q →* ↥K ⧸ N := π.comp (Subgroup.inclusion hQK)
    have hrange : φ.range = E := by
      show (π.comp (Subgroup.inclusion hQK)).range = E
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    have hker : φ.ker = P.subgroupOf Q := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show π (Subgroup.inclusion hQK x) = 1 ↔ _
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN]
      rfl
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPQ).toEquiv, hQcard] at h1
    have hPpos : 0 < Nat.card P := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hPpos h1
  obtain ⟨hcardY, hEprops⟩ := hY
  obtain ⟨hE3, hE4⟩ := hEprops E hEe hEcard
  refine ⟨?_, ?_, ?_⟩
  · exact l34_card hN (hPQ.trans hQK) ⟨hcardY, hEprops⟩
  · intro R W hQR hRN hRW hW g hg
    set R' : Subgroup (↥K ⧸ N) := (R.subgroupOf K).map π with hR'
    set W' : Subgroup (↥K ⧸ N) := (W.subgroupOf K).map π with hW'
    have hRK : R ≤ K := hRN.trans inf_le_left
    have hER : E < R' := by
      refine lt_of_le_of_ne (Subgroup.map_mono (Subgroup.subgroupOf_mono K hQR.le)) ?_
      intro heq
      obtain ⟨r, hr, hrQ⟩ := IsConcreteLE.exists_of_lt hQR
      have hrE : π ⟨r, hRK hr⟩ ∈ R' := ⟨⟨r, hRK hr⟩, hr, rfl⟩
      rw [← heq] at hrE
      exact hrQ ((hE1 _).1 hrE)
    have hRn : R' ≤ Subgroup.normalizer (E : Set (↥K ⧸ N)) := by
      rintro _ ⟨r, hr, rfl⟩
      exact (hE2 r).2 (hRN hr).2
    have hRW' : R' ≤ W' := Subgroup.map_mono (Subgroup.subgroupOf_mono K hRW)
    have hWn : ∀ g ∈ Subgroup.normalizer (E : Set (↥K ⧸ N)), ∀ w ∈ W', g * w * g⁻¹ ∈ W' := by
      intro g' hg' w' hw'
      obtain ⟨k, rfl⟩ := hπs g'
      obtain ⟨w, hw, rfl⟩ := hw'
      refine ⟨k * w * k⁻¹, ?_, by simp⟩
      exact hW k ⟨k.2, (hE2 k).1 hg'⟩ w hw
    have hfin := hE3 R' W' hER hRn hRW' hWn
    have hgE : π ⟨g, hg.1⟩ ∈ Subgroup.normalizer (E : Set (↥K ⧸ N)) := (hE2 _).2 hg.2
    obtain ⟨w, hw, hwg⟩ := hfin hgE
    have h1 : w⁻¹ * ⟨g, hg.1⟩ ∈ N := by
      rw [← QuotientGroup.eq]
      exact hwg
    have h2 : (((w⁻¹ * ⟨g, hg.1⟩ : ↥K)) : G) ∈ P := (hN _).1 h1
    have h3 : g = (w : G) * (((w⁻¹ * ⟨g, hg.1⟩ : ↥K)) : G) := by simp
    rw [h3]
    exact W.mul_mem hw (hRW (hQR.le (hPQ h2)))
  · intro y hy hfix
    have hyK : y ∈ K := hQK hy
    have hyE : π ⟨y, hyK⟩ ∈ E := (hE1 _).2 hy
    have h1 := hE4 (π ⟨y, hyK⟩) hyE (fun g' hg' => by
      obtain ⟨k, rfl⟩ := hπs g'
      have hkN := (hE2 k).1 hg'
      have hk := hfix k ⟨k.2, hkN⟩
      have e : π k * π ⟨y, hyK⟩ * (π k)⁻¹ = π (k * ⟨y, hyK⟩ * k⁻¹) := by simp
      rw [e]
      congr 1
      apply Subtype.ext
      simpa using hk)
    have : (⟨y, hyK⟩ : ↥K) ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      exact h1
    exact (hN _).1 this

end Transfer

end CFSG.QuasithinUnique.Lin2
