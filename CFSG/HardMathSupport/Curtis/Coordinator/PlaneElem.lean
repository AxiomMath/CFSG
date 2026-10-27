module

public import CFSG.HardMathSupport.Curtis.Coordinator.PlaneAut
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.Plane

open CFSG.Open

theorem exists_elemAbelian_of_two {X : Type*} [Group X] {p : ℕ} (hp : p.Prime) {u v : X}
    (hc : Commute u v) (hu : u ^ p = 1) (hv : v ^ p = 1) (hu1 : u ≠ 1)
    (hvu : v ∉ Subgroup.zpowers u) :
    ∃ E : Subgroup X, IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ u ∈ E ∧ v ∈ E ∧
      (∀ T : Subgroup X, u ∈ T → v ∈ T → E ≤ T) ∧
      ∀ e ∈ E, ∃ a ∈ Subgroup.zpowers u, ∃ b ∈ Subgroup.zpowers v, e = a * b := by
  have : Fact p.Prime := ⟨hp⟩
  have hv1 : v ≠ 1 := fun h => hvu (h ▸ Subgroup.one_mem _)
  have ho₁ : orderOf u = p := orderOf_eq_prime hu hu1
  have ho₂ : orderOf v = p := orderOf_eq_prime hv hv1
  have hcard₁ : Nat.card (Subgroup.zpowers u) = p := by rw [Nat.card_zpowers, ho₁]
  have hcard₂ : Nat.card (Subgroup.zpowers v) = p := by rw [Nat.card_zpowers, ho₂]
  have hcomm : ∀ (a : ↥(Subgroup.zpowers u)) (b : ↥(Subgroup.zpowers v)),
      Commute ((Subgroup.zpowers u).subtype a) ((Subgroup.zpowers v).subtype b) := by
    intro a b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change Commute (a : X) (b : X)
    rw [← hk, ← hl]
    exact hc.zpow_zpow k l
  let f : ↥(Subgroup.zpowers u) × ↥(Subgroup.zpowers v) →* X :=
    MonoidHom.noncommCoprod (Subgroup.zpowers u).subtype (Subgroup.zpowers v).subtype hcomm
  have hf_apply : ∀ x, f x = (x.1 : X) * x.2 := fun x => rfl
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have hab' : (a : X) * b = 1 := hab
    have hbu : (b : X) ∈ Subgroup.zpowers u := by
      have : (b : X) = (a : X)⁻¹ := eq_inv_of_mul_eq_one_right hab'
      rw [this]
      exact Subgroup.inv_mem _ a.2
    have hb1 : (b : X) = 1 := by
      by_contra hb1
      have := eq_zpowers_of_card_prime hp hcard₂ b.2 hb1
      apply hvu
      have hz : Subgroup.zpowers (b : X) ≤ Subgroup.zpowers u := by
        rw [Subgroup.zpowers_le]; exact hbu
      rw [← this] at hz
      exact hz (Subgroup.mem_zpowers v)
    have ha1 : (a : X) = 1 := by rwa [hb1, mul_one] at hab'
    rw [Subgroup.mem_bot]
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  have hcard : Nat.card f.range = p ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_prod, hcard₁, hcard₂, sq]
  have hpow : ∀ (x : X) (w : X), x ^ p = 1 → ∀ a ∈ Subgroup.zpowers x, a ^ p = 1 := by
    intro x w hx a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  refine ⟨f.range, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, hcard, ?_, ?_, ?_, ?_⟩
  · rcases x with ⟨_, ⟨s, rfl⟩⟩
    rcases y with ⟨_, ⟨t, rfl⟩⟩
    apply Subtype.ext
    show f s * f t = f t * f s
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (mul_comm' _ _) (mul_comm' _ _)
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    show ((a : X) * (b : X)) ^ p = 1
    rw [(show Commute (a : X) (b : X) from hcomm a b).mul_pow, hpow u v hu a a.2,
      hpow v u hv b b.2, one_mul]
  · exact ⟨(⟨u, Subgroup.mem_zpowers u⟩, 1), by simp [hf_apply]⟩
  · exact ⟨(1, ⟨v, Subgroup.mem_zpowers v⟩), by simp [hf_apply]⟩
  · intro T huT hvT
    rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [hf_apply]
    exact T.mul_mem (Subgroup.zpowers_le.mpr huT a.2) (Subgroup.zpowers_le.mpr hvT b.2)
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact ⟨a, a.2, b, b.2, hf_apply _⟩

theorem mem_normalizer_of_conj {X : Type*} [Group X] {u v y : X} {E : Subgroup X} [Finite E]
    (huE : u ∈ E) (hvE : v ∈ E)
    (hmem : ∀ e ∈ E, ∃ a ∈ Subgroup.zpowers u, ∃ b ∈ Subgroup.zpowers v, e = a * b)
    (hyv : y * v * y⁻¹ = v) (hyu : y * u * y⁻¹ = u * v) :
    y ∈ Subgroup.normalizer (E : Set X) := by
  have hmap : ∀ e ∈ E, y * e * y⁻¹ ∈ E := by
    intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have : y * (u ^ k * v ^ l) * y⁻¹ = (u * v) ^ k * v ^ l := by
      rw [show y * (u ^ k * v ^ l) * y⁻¹ = (y * u ^ k * y⁻¹) * (y * v ^ l * y⁻¹) by group,
        ← conj_zpow, ← conj_zpow, hyu, hyv]
    rw [this]
    exact E.mul_mem (E.zpow_mem (E.mul_mem huE hvE) k) (E.zpow_mem hvE l)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hmap h hh, fun hh => ?_⟩
  let g : E → E := fun e => ⟨y * e * y⁻¹, hmap e e.2⟩
  have hginj : Function.Injective g := fun a b hab => by
    have : y * (a : X) * y⁻¹ = y * (b : X) * y⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using this)
  obtain ⟨e, he⟩ := (Finite.injective_iff_surjective.mp hginj) ⟨y * h * y⁻¹, hh⟩
  have : y * (e : X) * y⁻¹ = y * h * y⁻¹ := congrArg Subtype.val he
  have h' : (e : X) = h := by simpa using this
  rw [← h']
  exact e.2

end CFSG.HardMathSupport.Curtis.Coordinator.Plane
