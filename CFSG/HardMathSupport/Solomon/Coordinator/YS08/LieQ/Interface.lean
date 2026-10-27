module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.GenCoreBT
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Skeleton
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.RadicalQuot

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits

@[expose] def LieQConstrainedInner (q : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevOfChar q S → ∀ Q : Subgroup S, Q ≠ ⊥ → IsPGroup q ↥Q →
      ∀ h ∈ Subgroup.normalizer (Q : Set S),
        (∀ r ∈ pCoreOf q (Subgroup.normalizer (Q : Set S)), h * r = r * h) →
        h ∈ pCoreOf q (Subgroup.normalizer (Q : Set S))

theorem LieQConstrainedInner.of_lieQConstrained {q : ℕ} (hL : LieQConstrained q) :
    LieQConstrainedInner q := fun S _ _ hS hnab hChev Q hQ hQp =>
  lieQConstrained_inner hL hS hnab hChev hQ hQp

theorem lieQConstrained_of_families {q : ℕ} [Fact q.Prime]
    (hBT : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      IsChevOfChar q S → HoldsTits S q)
    (hRR : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      IsChevOfChar q S → RadRigid q S) : LieQConstrained q := by
  intro H _ _ S hSn hS hnab hChev hC Q hQS hQ hQp
  haveI := hSn
  exact lieQ_of_radRigid S (hBT ↥S hS hnab hChev) (hRR ↥S hS hnab hChev) hC hQS hQ hQp

theorem lieQConstrainedInner_of_families {q : ℕ} [Fact q.Prime]
    (hBT : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      IsChevOfChar q S → HoldsTits S q)
    (hRR : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      IsChevOfChar q S → RadRigidInner q S) : LieQConstrainedInner q := by
  intro S _ _ hS hnab hChev Q hQ hQp
  exact lieQ_inner_of_radRigidInner (hBT S hS hnab hChev) (hRR S hS hnab hChev) hQ hQp

theorem borelTits_of_constrainedInner {q : ℕ} (hq : q.Prime) (hL : LieQConstrainedInner q)
    (Y : Type) [Group Y] [Finite Y] (K A Q : Subgroup Y) :
    CFSG.Open.IsQuasisimple ↥K → IsChevOfChar q (↥K ⧸ Subgroup.center ↥K) →
    A ≤ Subgroup.normalizer (K : Set Y) → IsMaxInvSub A K q Q → ¬ Q ≤ centerIn K →
    ∀ y ∈ K, y ∈ Subgroup.centralizer (Q : Set Y) → y ∈ centerIn K ⊔ Q := by
  intro hKq hChev hAK hmax hQc y hyK hyC
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hQK, hQp, hAQ, hmaxQ⟩ := hmax
  let Γ : Subgroup (MulAut ↥K) :=
    (A.subgroupOf (Subgroup.normalizer (K : Set Y))).map K.normalizerMonoidHom
  have hΓ : ∀ g ∈ Γ, ∃ a ∈ A, ∃ ha : a ∈ Subgroup.normalizer (K : Set Y),
      g = K.normalizerMonoidHom ⟨a, ha⟩ := by
    rintro g ⟨a, ha, rfl⟩
    exact ⟨a, ha, a.2, rfl⟩
  have hconj : ∀ (a : Y) (ha : a ∈ Subgroup.normalizer (K : Set Y)) (k : ↥K),
      (((K.normalizerMonoidHom ⟨a, ha⟩ k : ↥K)) : Y) = a * k * a⁻¹ := fun a ha k => rfl
  set Q' : Subgroup ↥K := Q.subgroupOf K with hQ'
  have hQ'p : IsPGroup q ↥Q' := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  have hmapeq : ∀ (a : Y) (ha : a ∈ Subgroup.normalizer (K : Set Y)) (T : Subgroup Y), T ≤ K →
      a ∈ Subgroup.normalizer (T : Set Y) →
      (T.subgroupOf K).map (K.normalizerMonoidHom ⟨a, ha⟩).toMonoidHom = T.subgroupOf K := by
    intro a ha T hTK haT
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : (t : Y) ∈ T := ht
      have := (Subgroup.mem_normalizer_iff.1 haT (t : Y)).1 ht'
      show ((K.normalizerMonoidHom ⟨a, ha⟩ t : ↥K) : Y) ∈ T
      rw [hconj]
      exact this
    · intro hx
      have hx' : (x : Y) ∈ T := hx
      have hainv : a⁻¹ ∈ Subgroup.normalizer (T : Set Y) := Subgroup.inv_mem _ haT
      have hainvK : a⁻¹ ∈ Subgroup.normalizer (K : Set Y) := Subgroup.inv_mem _ ha
      have h1 : a⁻¹ * (x : Y) * a⁻¹⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hainv (x : Y)).1 hx'
      have h1K : a⁻¹ * (x : Y) * a⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hainvK (x : Y)).1 x.2
      refine ⟨⟨a⁻¹ * (x : Y) * a⁻¹⁻¹, h1K⟩, h1, ?_⟩
      apply Subtype.ext
      show a * (a⁻¹ * (x : Y) * a⁻¹⁻¹) * a⁻¹ = x
      group
  have hinv : ∀ g ∈ Γ, Q'.map g.toMonoidHom = Q' := by
    intro g hg
    obtain ⟨a, haA, ha, rfl⟩ := hΓ g hg
    exact hmapeq a ha Q hQK (hAQ haA)
  have hmax' : ∀ T : Subgroup ↥K, IsPGroup q ↥T → (∀ g ∈ Γ, T.map g.toMonoidHom = T) → Q' ≤ T →
      T = Q' := by
    intro T hTp hTinv hQT
    let TY : Subgroup Y := T.map K.subtype
    have hTY : T = TY.subgroupOf K :=
      (Subgroup.comap_map_eq_self_of_injective K.subtype_injective T).symm
    have hTYK : TY ≤ K := Subgroup.map_subtype_le T
    have hTYp : IsPGroup q ↥TY := hTp.map K.subtype
    have hQTY : Q ≤ TY := by
      intro x hx
      exact ⟨⟨x, hQK hx⟩, hQT (show (⟨x, hQK hx⟩ : ↥K) ∈ Q' from hx), rfl⟩
    have hconjT : ∀ a ∈ A, ∀ x ∈ TY, a * x * a⁻¹ ∈ TY := by
      intro a haA x hx
      obtain ⟨t, ht, rfl⟩ := hx
      have hg := hTinv (K.normalizerMonoidHom ⟨a, hAK haA⟩) ⟨⟨a, hAK haA⟩, haA, rfl⟩
      have hgt : K.normalizerMonoidHom ⟨a, hAK haA⟩ t ∈ T := by
        rw [← hg]
        exact ⟨t, ht, rfl⟩
      exact ⟨_, hgt, hconj a (hAK haA) t⟩
    have hAT : A ≤ Subgroup.normalizer (TY : Set Y) := fun a haA =>
      Subgroup.mem_normalizer_iff.2 fun x =>
        ⟨fun hx => hconjT a haA x hx, fun hx => by
          have := hconjT a⁻¹ (A.inv_mem haA) _ hx
          simpa [mul_assoc] using this⟩
    have := hmaxQ TY hTYK hTYp hAT hQTY
    rw [hTY, this]
  have hrad := pCoreOf_normalizer_map_center (q := q) Γ hQ'p hinv hmax'
  set Z := Subgroup.center ↥K with hZ
  set π : ↥K →* ↥K ⧸ Z := QuotientGroup.mk' Z with hπ
  set Qb : Subgroup (↥K ⧸ Z) := Q'.map π with hQb
  have hQbp : IsPGroup q ↥Qb := hQ'p.map π
  have hQbne : Qb ≠ ⊥ := by
    intro hbot
    apply hQc
    intro x hx
    have h1 : π ⟨x, hQK hx⟩ ∈ Qb := ⟨⟨x, hQK hx⟩, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have : (⟨x, hQK hx⟩ : ↥K) ∈ Z := (QuotientGroup.eq_one_iff _).1 h1
    exact ⟨⟨x, hQK hx⟩, this, rfl⟩
  haveI := hKq.2
  obtain ⟨a, b, hab⟩ :=
    ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥K hKq
  set yb : ↥K ⧸ Z := π ⟨y, hyK⟩ with hyb
  have hcomm : ∀ r ∈ Qb, yb * r = r * yb := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : (x : Y) ∈ Q := hx
    have := Subgroup.mem_centralizer_iff.1 hyC (x : Y) hxQ
    show π ⟨y, hyK⟩ * π x = π x * π ⟨y, hyK⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext this.symm
  have hconj : ∀ z ∈ Qb, yb * z * yb⁻¹ = z := fun z hz => by rw [hcomm z hz]; group
  have hconj' : ∀ z ∈ Qb, yb⁻¹ * z * yb = z := fun z hz => by
    have h := hcomm z hz
    calc yb⁻¹ * z * yb = yb⁻¹ * (z * yb) := by group
      _ = yb⁻¹ * (yb * z) := by rw [h]
      _ = z := by group
  have hnorm : yb ∈ Subgroup.normalizer (Qb : Set (↥K ⧸ Z)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hconj x hx]
      exact hx
    · intro hx
      have h2 := hconj' _ hx
      have h3 : yb⁻¹ * (yb * x * yb⁻¹) * yb = x := by group
      rw [h3] at h2
      rw [h2]
      exact hx
  have hmem := hL (↥K ⧸ Z) hKq.2 ⟨a, b, hab⟩ hChev Qb hQbne hQbp yb hnorm
    (fun r hr => hcomm r (hrad ▸ hr))
  rw [hrad] at hmem
  obtain ⟨x, hxQ, hxy⟩ := hmem
  have hz : x⁻¹ * ⟨y, hyK⟩ ∈ Z := QuotientGroup.eq.1 hxy
  have hzY : ((x⁻¹ * ⟨y, hyK⟩ : ↥K) : Y) ∈ centerIn K := ⟨_, hz, rfl⟩
  have hxY : (x : Y) ∈ Q := hxQ
  have h2 := Subgroup.mul_mem_sup hzY hxY
  have hcz : x * (x⁻¹ * ⟨y, hyK⟩) = (x⁻¹ * ⟨y, hyK⟩) * x := Subgroup.mem_center_iff.1 hz x
  have h3 : (⟨y, hyK⟩ : ↥K) = (x⁻¹ * ⟨y, hyK⟩) * x := by
    rw [← hcz]
    group
  have hyx : y = ((x⁻¹ * ⟨y, hyK⟩ : ↥K) : Y) * (x : Y) := congrArg Subtype.val h3
  rw [hyx]
  exact h2

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
