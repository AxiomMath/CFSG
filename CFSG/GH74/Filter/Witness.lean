module

public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.Filter

open Subgroup

theorem not_gen4_of_elementary {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (hsq : ∀ a : A, a ^ 2 = 1)
    (hcard : 2 ^ 4 < Nat.card A) : ¬ Gen4 A := by
  intro h
  have hE : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup A) :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩, fun x _ => hsq x⟩
  have := SectionalTwoRankLE.card_le_of_elementary h ⊤ hE
  rw [Subgroup.card_top] at this
  omega

theorem not_gen4_of_surjection {G K A : Type*} [Group G] [Group K] [Finite K] [Group A]
    (α : K →* G) (β : K →* A) (hβ : Function.Surjective β)
    (hcomm : ∀ a b : A, a * b = b * a) (hsq : ∀ a : A, a ^ 2 = 1)
    (hcard : 2 ^ 4 < Nat.card A) (hker : α.ker ≤ β.ker) : ¬ Gen4 G := by
  intro hG
  have : Finite A := Finite.of_surjective β hβ
  obtain ⟨S⟩ : Nonempty (Sylow 2 K) := inferInstance
  let P : Subgroup G := (S : Subgroup K).map α
  have hGP : Gen4 P := Gen4.subgroup P hG
  let f : (S : Subgroup K) →* P :=
    (α.comp (S : Subgroup K).subtype).codRestrict P fun s => ⟨s, s.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have : Finite P := Finite.of_surjective f hf
  have hA2 : IsPGroup 2 A := fun a => ⟨1, by simpa using hsq a⟩
  have hSβ : (⊤ : Subgroup A) = (S : Subgroup K).map β := by
    have h2 := (S.mapSurjective hβ).is_maximal' (hA2.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h2
    exact h2
  let ψ : (S : Subgroup K) →* A := β.comp (S : Subgroup K).subtype
  have hψ : Function.Surjective ψ := by
    intro a
    have : a ∈ (S : Subgroup K).map β := hSβ ▸ Subgroup.mem_top a
    obtain ⟨s, hs, rfl⟩ := this
    exact ⟨⟨s, hs⟩, rfl⟩
  have hkerψ : f.ker ≤ ψ.ker := by
    intro s hs
    have h1 : α s = 1 := by
      have h0 : f s = 1 := MonoidHom.mem_ker.1 hs
      exact congrArg Subtype.val h0
    exact hker (MonoidHom.mem_ker.2 h1)
  let φ : P →* A := (MonoidHom.liftOfSurjective f hf) ⟨ψ, hkerψ⟩
  have hφf : ∀ s, φ (f s) = ψ s := fun s => by
    simp [φ]
  have hφ : Function.Surjective φ := by
    intro a
    obtain ⟨s, rfl⟩ := hψ a
    exact ⟨f s, hφf s⟩
  exact not_gen4_of_elementary hcomm hsq hcard (Gen4.of_surjective φ hφ hGP)

theorem not_gen4_of_injective {G A : Type*} [Group G] [Group A] [Finite A] (α : A →* G)
    (hα : Function.Injective α) (hcomm : ∀ a b : A, a * b = b * a) (hsq : ∀ a : A, a ^ 2 = 1)
    (hcard : 2 ^ 4 < Nat.card A) : ¬ Gen4 G :=
  not_gen4_of_surjection α (MonoidHom.id A) Function.surjective_id hcomm hsq hcard
    (by rw [(MonoidHom.ker_eq_bot_iff α).2 hα]; exact bot_le)

theorem not_gen4_of_elemAbelian {G : Type*} [Group G] (E : Subgroup G)
    (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : 2 ^ 4 < Nat.card E) : ¬ Gen4 G :=
  fun h => absurd (SectionalTwoRankLE.card_le_of_elementary h E hE) (by omega)

theorem not_gen4_of_twoRank {G : Type*} [Group G] [Finite G] (h : 4 < CFSG.Open.twoRank G) :
    ¬ Gen4 G :=
  fun hG => absurd (Gen4.twoRank_le hG) (by omega)

theorem not_gen4_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    ¬ Gen4 G → ¬ Gen4 G' :=
  fun h h' => h (Gen4.of_mulEquiv e.symm h')

end CFSG.GH74.Filter
