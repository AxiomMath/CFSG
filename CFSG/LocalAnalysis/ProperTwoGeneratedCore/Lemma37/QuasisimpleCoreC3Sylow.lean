module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Centralizers
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Normalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Unique

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

variable {G : Type} [Group G] [Finite G] {T Q P₁ : Subgroup G} {e u y : G}

namespace CaseC3

@[expose] def MaxInNormalizer (T : Subgroup G) (u : G) : Prop :=
  ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G),
    n ∈ Subgroup.normalizer (T : Set G) → (∃ k : ℕ, n ^ 2 ^ k = 1) → n ∈ T

omit [Finite G] in
theorem exists_pow_eq_one_of_mem {S : Subgroup G} (hS : IsPGroup 2 S) {s : G} (hs : s ∈ S) :
    ∃ k : ℕ, s ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem mul_mem_of_not_mem (h : CaseC3 T Q P₁ e u y) (hmax : MaxInNormalizer T u)
    {S : Subgroup G} (hS : IsPGroup 2 S) {x s : G} (hxS : x ∈ S)
    (hxT : x ∈ Subgroup.normalizer (T : Set G)) (hx : x ∉ T) (hsS : s ∈ S)
    (hsT : s ∈ Subgroup.normalizer (T : Set G)) (hs : s ∉ T) : s * x ∈ T := by
  have hxP : ∀ p ∈ P₁, x * p * x⁻¹ ∈ Q :=
    (h.conj_swap hmax hxT hx (exists_pow_eq_one_of_mem hS hxS)).1
  have hsQ : ∀ q ∈ Q, s * q * s⁻¹ ∈ P₁ :=
    (h.conj_swap hmax hsT hs (exists_pow_eq_one_of_mem hS hsS)).2
  have hnP : s * x ∈ Subgroup.normalizer (P₁ : Set G) := by
    refine mem_normalizer_of_conj_mem fun p hp => ?_
    rw [show s * x * p * (s * x)⁻¹ = s * (x * p * x⁻¹) * s⁻¹ by group]
    exact hsQ _ (hxP p hp)
  have hnT : s * x ∈ Subgroup.normalizer (T : Set G) := Subgroup.mul_mem _ hsT hxT
  exact hmax _ (h.mem_normalizer_zpowers hnT hnP) hnT
    (exists_pow_eq_one_of_mem hS (S.mul_mem hsS hxS))

variable (Z : Subgroup G) [Z.Normal]

theorem conj_mem_sup_of_mem_normalizer_inf (h : CaseC3 T Q P₁ e u y)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) (hmax : MaxInNormalizer T u) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hTS : T ≤ S) {x : G} (hxS : x ∈ S)
    (hxT : x ∈ Subgroup.normalizer (T : Set G)) (hx : x ∉ T) {n : G}
    (hn : n ∈ Subgroup.normalizer ((S ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G))
    {w : G} (hw : w ∈ Q ⊔ P₁) : n * w * n⁻¹ ∈ Q ⊔ P₁ := by
  have hc := h.partC
  obtain ⟨φ⟩ := h.quaternion_right
  set S₀ := S ⊓ Subgroup.normalizer (T : Set G) with hS₀
  have hZW := hc.le_sup_of_mem_iff Z hZ
  have hZT : Z ≤ T := hZW.trans hc.sup_le
  have hTS₀ : T ≤ S₀ := le_inf hTS Subgroup.le_normalizer
  have hWS₀ : Q ⊔ P₁ ≤ S₀ := hc.sup_le.trans hTS₀
  have hswap : ∀ s ∈ S₀, s ∉ T →
      (∀ p ∈ P₁, s * p * s⁻¹ ∈ Q) ∧ (∀ q ∈ Q, s * q * s⁻¹ ∈ P₁) := fun s hs hsT =>
    h.conj_swap hmax hs.2 hsT (exists_pow_eq_one_of_mem hS hs.1)
  set π := QuotientGroup.mk' Z with hπ
  have hWT : (Q ⊔ P₁).map π ≤ T.map π := Subgroup.map_mono hc.sup_le
  have hTS' : T.map π ≤ S₀.map π := Subgroup.map_mono hTS₀
  have hWT2 := hc.relIndex_map_sup Z hZ h.mem h.not_mem
  have hTS2 : (T.map π).relIndex (S₀.map π) = 2 :=
    PartC.relIndex_map_eq_two Z hZT ⟨hxS, hxT⟩ hx fun s hs hsT =>
      h.mul_mem_of_not_mem hmax hS hxS hxT hx hs.1 hs.2 hsT
  have h1 : ∀ a ∈ S₀.map π, a ∉ (Q ⊔ P₁).map π →
      Nat.card ((Q ⊔ P₁).map π ⊓ Subgroup.centralizer {a} : Subgroup (G ⧸ Z)) ≤ 4 := by
    intro a ha haW
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ha
    have hsW : s ∉ Q ⊔ P₁ := fun h' => haW (Subgroup.mem_map_of_mem _ h')
    by_cases hsT : s ∈ T
    · exact (Subgroup.card_le_of_le (h.map_sup_inf_centralizer_le Z hZ hsT hsW)).trans
        (h.card_map_sup_inf_centralizer Z hZ).le
    · exact h.card_map_sup_inf_centralizer_le_of_swap Z hZ (hswap s hs hsT).1
  have h2 : ∀ a₁ ∈ T.map π, a₁ ∉ (Q ⊔ P₁).map π → ∀ a₂ ∈ S₀.map π, a₂ ∉ T.map π →
      Nat.card ((Q ⊔ P₁).map π ⊓ Subgroup.centralizer {a₁} ⊓ Subgroup.centralizer {a₂} :
        Subgroup (G ⧸ Z)) ≤ 2 := by
    intro a₁ ha₁ ha₁W a₂ ha₂ ha₂T
    obtain ⟨s₁, hs₁, rfl⟩ := Subgroup.mem_map.mp ha₁
    obtain ⟨s₂, hs₂, rfl⟩ := Subgroup.mem_map.mp ha₂
    have hs₁W : s₁ ∉ Q ⊔ P₁ := fun h' => ha₁W (Subgroup.mem_map_of_mem _ h')
    have hs₂T : s₂ ∉ T := fun h' => ha₂T (Subgroup.mem_map_of_mem _ h')
    exact h.card_map_sup_inf_inf_le_two Z hZ hs₁ hs₁W (hswap s₂ hs₂ hs₂T).1
      (hswap s₂ hs₂ hs₂T).2
  set A := ((Q ⊔ P₁).map π).map (MulAut.conj (π n)).toMonoidHom with hA
  have hmk : ∀ g : G, (MulAut.conj (π n)).toMonoidHom (π g) = π (n * g * n⁻¹) := fun g => by
    simp [hπ, MulAut.conj_apply]
  have hAS : A ≤ S₀.map π := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    rw [hmk]
    exact Subgroup.mem_map_of_mem _ ((Subgroup.mem_normalizer_iff.mp hn g).mp (hWS₀ hg))
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc.mul_comm_of_mem_map_sup Z φ hZ ha hb]
  have hA16 : Nat.card A = 16 := by
    rw [hA, Subgroup.card_map_of_injective (MulAut.conj (π n)).injective,
      hc.card_map_sup Z φ hZ]
  have hAW := caseC3_le_of_abelian hWT hTS' hWT2 hTS2 h1 h2 hAS hAab hA16
  have hmem : π (n * w * n⁻¹) ∈ (Q ⊔ P₁).map π := by
    rw [← hmk]
    exact hAW ⟨π w, Subgroup.mem_map_of_mem _ hw, rfl⟩
  exact (PartC.mk_mem_map_iff_of_le Z hZW _).mp hmem

theorem exists_two_group_structure (h : CaseC3 T Q P₁ e u y)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) (hmax : MaxInNormalizer T u) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hTS : T ≤ S) (hne : T ≠ S) :
    ∃ x ∈ S, x ∉ T ∧ S ≤ Subgroup.normalizer (T : Set G) ∧
      (∀ p ∈ P₁, x * p * x⁻¹ ∈ Q) ∧ (∀ q ∈ Q, x * q * x⁻¹ ∈ P₁) ∧
      ∀ s ∈ S, s ∉ T → s * x ∈ T := by
  have hc := h.partC
  obtain ⟨x, hxS, hxT, hx⟩ := caseC3_exists_mem_normalizer_not_mem hS hTS hne
  set S₀ := S ⊓ Subgroup.normalizer (T : Set G) with hS₀
  have hTS₀ : T ≤ S₀ := le_inf hTS Subgroup.le_normalizer
  have hxS₀ : x ∈ S₀ := ⟨hxS, hxT⟩
  obtain ⟨hxP, hxQ⟩ := h.conj_swap hmax hxT hx (exists_pow_eq_one_of_mem hS hxS)
  have hkey : ∀ n ∈ S, n ∈ Subgroup.normalizer (S₀ : Set G) →
      (∀ p ∈ P₁, n * p * n⁻¹ ∈ P₁) → n ∈ S₀ := by
    intro n hnS hnN hnP
    have hnP' : n ∈ Subgroup.normalizer (P₁ : Set G) := mem_normalizer_of_conj_mem hnP
    refine ⟨hnS, mem_normalizer_of_conj_mem fun t ht => ?_⟩
    have htS₀ : n * t * n⁻¹ ∈ S₀ := (Subgroup.mem_normalizer_iff.mp hnN t).mp (hTS₀ ht)
    by_contra hntT
    obtain ⟨hsw, -⟩ := h.conj_swap hmax htS₀.2 hntT (exists_pow_eq_one_of_mem hS htS₀.1)
    have hQ' := hsw u hc.self_mem
    have hP' : n * t * n⁻¹ * u * (n * t * n⁻¹)⁻¹ ∈ P₁ := by
      rw [show n * t * n⁻¹ * u * (n * t * n⁻¹)⁻¹ = n * (t * (n⁻¹ * u * n⁻¹⁻¹) * t⁻¹) * n⁻¹ by
        group]
      exact hnP _ (hc.normal_right t ht _
        ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnP') u).mp hc.self_mem))
    rcases hc.mem_inf _ hQ' hP' with h1 | h1
    · rw [mul_inv_eq_one, mul_eq_left] at h1
      exact hc.self_ne.1 h1
    · rw [← hc.conj_centralElt (n * t * n⁻¹)] at h1
      exact hc.self_ne.2 (mul_left_cancel (mul_right_cancel h1))
  have hnorm : ∀ n ∈ S, n ∈ Subgroup.normalizer (S₀ : Set G) → n ∈ S₀ := by
    intro n hnS hnN
    have hnW := fun w (hw : w ∈ Q ⊔ P₁) =>
      h.conj_mem_sup_of_mem_normalizer_inf Z hZ hmax hS hTS hxS hxT hx hnN hw
    obtain ⟨φ⟩ := h.quaternion_right
    obtain ⟨φQ⟩ := hc.quaternion
    have hmem : ∀ {R : Subgroup G} {g : G}, g ∈ R →
        n * g * n⁻¹ ∈ R.map (MulAut.conj n).toMonoidHom := fun {R g} hg =>
      ⟨g, hg, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have hP := h.map_conj_eq_or_eq_of_conj_mem hnW (R := P₁) le_sup_right
      (by rw [Nat.card_congr φ.toEquiv, PartC.card_quaternionGroup_two])
      (fun r hr h1 h2 => quaternion_mul_self_of_ne φ hc.mem_right hc.order hr h1 h2)
    rcases hP with hP | hP
    · exact hkey n hnS hnN fun p hp => hP ▸ hmem hp
    · have hQ := h.map_conj_eq_or_eq_of_conj_mem hnW (R := Q) le_sup_left
        (by rw [Nat.card_congr φQ.toEquiv, PartC.card_quaternionGroup_two])
        (fun r hr h1 h2 => quaternion_mul_self_of_ne φQ hc.mem_left hc.order hr h1 h2)
      have hQP : Q.map (MulAut.conj n).toMonoidHom = P₁ := by
        refine hQ.resolve_right fun hQ' => ?_
        have hu := hmem (R := P₁) hc.self_mem
        rw [hP, ← hQ'] at hu
        obtain ⟨q, hq, hqu⟩ := hu
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hqu
        have hqu' : q = u := mul_left_cancel (mul_right_cancel hqu)
        rcases hc.mem_inf u (hqu' ▸ hq) hc.self_mem with h1 | h1
        exacts [hc.self_ne.1 h1, hc.self_ne.2 h1]
      have hnx := hkey (n * x) (S.mul_mem hnS hxS)
        (Subgroup.mul_mem _ hnN (Subgroup.le_normalizer hxS₀)) fun p hp => by
          rw [show n * x * p * (n * x)⁻¹ = n * (x * p * x⁻¹) * n⁻¹ by group]
          exact hQP ▸ hmem (hxP p hp)
      rw [show n = n * x * x⁻¹ by group]
      exact S₀.mul_mem hnx (S₀.inv_mem hxS₀)
  have hS₀S : S₀ = S := by
    by_contra hne'
    obtain ⟨n, hnS, hnN, hnS₀⟩ := caseC3_exists_mem_normalizer_not_mem hS inf_le_left hne'
    exact hnS₀ (hnorm n hnS hnN)
  have hSN : S ≤ Subgroup.normalizer (T : Set G) := hS₀S ▸ inf_le_right
  exact ⟨x, hxS, hx, hSN, hxP, hxQ, fun s hs hsT =>
    h.mul_mem_of_not_mem hmax hS hxS hxT hx hs (hSN hs) hsT⟩

end CaseC3

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
