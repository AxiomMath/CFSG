module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Aux

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Delta

variable {G : Type} [Group G]

theorem mem_normalizer_sup_of_mem {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
  have h1 : CFSG.conjugate A g = A := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hA
  have h2 : CFSG.conjugate B g = B := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hB
  unfold CFSG.conjugate at h1 h2 ⊢
  rw [Subgroup.map_sup, h1, h2]

theorem T_le_normalizer [Finite G] (he : CFSG.Assembly.evenRank G ≤ 2) {A B S T : Subgroup G}
    {s₀ : G} (hs₀S : s₀ ∈ S) (hs₀ : s₀ ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G))
    (hBA : B = CFSG.conjugate A s₀)
    (hA : L2pAmb A) (hB : L2pAmb B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hcompAB : ∀ i ∈ B, orderOf i = 2 → IsComponentIn A (Subgroup.centralizer ({i} : Set G)))
    (hcompBA : ∀ j ∈ A, orderOf j = 2 → IsComponentIn B (Subgroup.centralizer ({j} : Set G)))
    (hSA : IsSylowTwoOf (S ⊓ A) A) (hSB : IsSylowTwoOf (S ⊓ B) B)
    (hT : IsPGroup 2 T) (hST : S ≤ T) :
    T ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have heq := normalizer_eq_of_pair he hA hB hAB hcompAB hcompBA
  have htight := tightlyEmbedded_of_pair he hA hB hAB heq hcompAB
  set Q : Subgroup G := S ⊓ B with hQ
  set Q₁ : Subgroup G := S ⊓ A with hQ₁
  have hQΦ : ∃ y ∈ Q, y ^ 2 ≠ 1 := hB.nonab Q hSB
  have hQbot : Q ≠ ⊥ := by
    obtain ⟨y, hyQ, hy2⟩ := hQΦ
    intro e
    rw [e, Subgroup.mem_bot] at hyQ
    exact hy2 (by rw [hyQ]; simp)
  have hQT : Q ≤ T := inf_le_left.trans hST
  have hsetup : Tight.Setup B ⊤ Q T :=
    ⟨htight, by rw [top_inf_eq]; exact hSB, hQbot, hT, le_top, hQT⟩
  have hs₀inv : s₀⁻¹ ∈ S := S.inv_mem hs₀S
  have hQ₁eq : Q₁ = CFSG.conjugate Q s₀⁻¹ := by
    have hS : CFSG.conjugate S s₀⁻¹ = S :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hs₀inv)
    have hB' : CFSG.conjugate B s₀⁻¹ = A := by
      rw [hBA, BenderBranch.conjugate_conjugate]; simp [BenderBranch.conjugate_one]
    rw [hQ, BenderBranch.conjugate_inf, hS, hB']
  have hQΔ : Q ∈ Tight.Delta ⊤ Q T := hsetup.mem_delta_self
  have hQ₁Δ : Q₁ ∈ Tight.Delta ⊤ Q T :=
    ⟨⟨s₀⁻¹, Subgroup.mem_top _, hQ₁eq⟩, inf_le_left.trans hST⟩
  have hΔ : ∀ R ∈ Tight.Delta ⊤ Q T, R = Q ∨ R = Q₁ := by
    intro R hR
    by_contra hcon
    have hRQ : R ≠ Q := fun e => hcon (Or.inl e)
    have hRQ₁ : R ≠ Q₁ := fun e => hcon (Or.inr e)
    have hc1 := hsetup.delta_commute hQΦ R hR Q hQΔ hRQ
    have hc2 := hsetup.delta_commute hQΦ R hR Q₁ hQ₁Δ hRQ₁
    have hR0 : R ∈ Tight.Delta ⊤ Q T := hR
    obtain ⟨⟨g, -, hRg⟩, hRT⟩ := hR
    have hR2 : IsPGroup 2 R := hT.to_le hRT
    obtain ⟨y, hyR, hy2⟩ := Tight.nonelem_of_mem_delta (H := ⊤) (S := T) hQΦ hR0
    have hRNB : ∀ r ∈ R, r ∈ Subgroup.normalizer (B : Set G) := fun r hr => by
      have hrQ : r ∈ Subgroup.normalizer (Q : Set G) :=
        Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.mpr fun q hq => (hc1 r hr q hq).symm)
      exact (hsetup.normalizer_le (X := Q) le_rfl hQbot).1 hrQ
    have hRNA : ∀ r ∈ R, r ∈ Subgroup.normalizer (A : Set G) := fun r hr => by
      rw [heq]; exact hRNB r hr
    have hsqA : ∀ r ∈ R, ∀ x ∈ A, (r * r) * x * (r * r)⁻¹ = x := fun r hr x hx => by
      have := hA.aut_two Q₁ hSA r (hRNA r hr) (fun z hz => by
        have := hc2 r hr z hz
        calc r * z * r⁻¹ = (z * r) * r⁻¹ := by rw [this]
          _ = z := by group) x hx
      calc (r * r) * x * (r * r)⁻¹ = r * (r * x * r⁻¹) * r⁻¹ := by group
        _ = x := this
    have hsqB : ∀ r ∈ R, ∀ x ∈ B, (r * r) * x * (r * r)⁻¹ = x := fun r hr x hx => by
      have := hB.aut_two Q hSB r (hRNB r hr) (fun z hz => by
        have := hc1 r hr z hz
        calc r * z * r⁻¹ = (z * r) * r⁻¹ := by rw [this]
          _ = z := by group) x hx
      calc (r * r) * x * (r * r)⁻¹ = r * (r * x * r⁻¹) * r⁻¹ := by group
        _ = x := this
    have hy2' : y * y ∈ R := R.mul_mem hyR hyR
    have hyy1 : y * y ≠ 1 := by rw [← sq]; exact hy2
    obtain ⟨n, hn1, hn2⟩ := Tight.exists_involution_pow hR2 hy2' hyy1
    obtain ⟨j, hj⟩ : ∃ j : G, j = (y * y) ^ n := ⟨_, rfl⟩
    have hjR : j ∈ R := by rw [hj]; exact R.pow_mem hy2' n
    have hj1 : j ≠ 1 := by rw [hj]; exact hn1
    have hjo : orderOf j = 2 := by rw [hj]; exact orderOf_eq_prime hn2 hn1
    have hjcomm : ∀ x, (y * y) * x * (y * y)⁻¹ = x → j * x * j⁻¹ = x := by
      intro x hx
      have h1 : Commute (y * y) x := by
        have : (y * y) * x = x * (y * y) := by
          calc (y * y) * x = ((y * y) * x * (y * y)⁻¹) * (y * y) := by group
            _ = x * (y * y) := by rw [hx]
        exact this
      have h2 := (h1.pow_left n).eq
      rw [← hj] at h2
      calc j * x * j⁻¹ = (x * j) * j⁻¹ := by rw [h2]
        _ = x := by group
    have hjA : ∀ x ∈ A, j * x * j⁻¹ = x := fun x hx => hjcomm x (hsqA y hyR x hx)
    have hjB : ∀ x ∈ B, j * x * j⁻¹ = x := fun x hx => hjcomm x (hsqB y hyR x hx)
    have hj'Q : g * j * g⁻¹ ∈ Q := by
      have := hjR
      rw [hRg, BenderBranch.mem_conjugate_iff] at this
      exact this
    have hj'B : g * j * g⁻¹ ∈ B := hj'Q.2
    have hj'o : orderOf (g * j * g⁻¹) = 2 := by rw [orderOf_conj_mul]; exact hjo
    have hcomp' := hcompAB _ hj'B hj'o
    have h3 : ∀ x : G, (x ∈ A ∨ x ∈ B) → (∃ m : ℕ, orderOf x = 3 ^ m) →
        g * x * g⁻¹ ∈ A := by
      intro x hx hx3
      refine three_elt_centralizer he hA hB hAB heq hj'B hj'o hcomp' ?_ ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        have hxj : j * x = x * j := by
          rcases hx with hx | hx
          · have := hjA x hx
            calc j * x = (j * x * j⁻¹) * j := by group
              _ = x * j := by rw [this]
          · have := hjB x hx
            calc j * x = (j * x * j⁻¹) * j := by group
              _ = x * j := by rw [this]
        calc (g * j * g⁻¹) * (g * x * g⁻¹) = g * (j * x) * g⁻¹ := by group
          _ = g * (x * j) * g⁻¹ := by rw [hxj]
          _ = (g * x * g⁻¹) * (g * j * g⁻¹) := by group
      · obtain ⟨m, hm⟩ := hx3
        exact ⟨m, by rw [orderOf_conj_mul]; exact hm⟩
    have hAle : A ≤ CFSG.conjugate A g := by
      apply hA.gen_three
      intro x hxA hx3
      rw [BenderBranch.mem_conjugate_iff]
      exact h3 x (Or.inl hxA) hx3
    have hBle : B ≤ CFSG.conjugate A g := by
      apply hB.gen_three
      intro x hxB hx3
      rw [BenderBranch.mem_conjugate_iff]
      exact h3 x (Or.inr hxB) hx3
    have hcard : A = CFSG.conjugate A g :=
      Subgroup.eq_of_le_of_card_ge hAle (BenderBranch.card_conjugate A g).le
    have hBA' : B ≤ A := by rw [hcard]; exact hBle
    obtain ⟨i, hiB, hi⟩ := hB.involution
    have hi1 : i = 1 := hA.center_trivial i (hBA' hiB) fun y hy => (hAB y hy i hiB)
    rw [hi1] at hi
    simp at hi
  intro t ht
  have hRT : CFSG.conjugate Q t ≤ T := by
    intro x hx
    rw [BenderBranch.mem_conjugate_iff] at hx
    have := T.mul_mem (T.mul_mem (T.inv_mem ht) (hQT hx)) ht
    simpa [mul_assoc] using this
  have hRΔ : CFSG.conjugate Q t ∈ Tight.Delta ⊤ Q T := ⟨⟨t, Subgroup.mem_top _, rfl⟩, hRT⟩
  rcases hΔ _ hRΔ with h1 | h1
  · have htN : t ∈ Subgroup.normalizer (Q : Set G) :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.mp h1
    have htB := (hsetup.normalizer_le (X := Q) le_rfl hQbot).1 htN
    exact mem_normalizer_sup_of_mem (by rw [heq]; exact htB) htB
  · have h2 : CFSG.conjugate Q (t * s₀) = Q := by
      rw [← BenderBranch.conjugate_conjugate, h1, hQ₁eq, BenderBranch.conjugate_conjugate]
      simp [BenderBranch.conjugate_one]
    have htsN : t * s₀ ∈ Subgroup.normalizer (Q : Set G) :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.mp h2
    have htsB := (hsetup.normalizer_le (X := Q) le_rfl hQbot).1 htsN
    have hts : t * s₀ ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
      mem_normalizer_sup_of_mem (by rw [heq]; exact htsB) htsB
    have : t = (t * s₀) * s₀⁻¹ := by group
    rw [this]
    exact (Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G)).mul_mem hts
      ((Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G)).inv_mem hs₀)

end Delta

end CFSG.QuasithinUnique
