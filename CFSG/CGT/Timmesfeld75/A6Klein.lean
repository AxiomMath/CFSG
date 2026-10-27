module

public import CFSG.CGT.Timmesfeld75.A6Model
public import CFSG.CGT.Timmesfeld75.WCBasic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open A6Model

@[expose] def A6KleinOrbit : Prop :=
  ∀ (K : Type) [Group K], Nonempty (K ≃* alternatingGroup (Fin 6)) →
    ∀ V V₂ V₃ : Subgroup K, IsElemAbelian 2 V → 2 < Nat.card V →
      (∃ k : K, V₂ = conjSubgroup k V) → (∃ k : K, V₃ = conjSubgroup k V) → V₂ ≠ V → V₃ ≠ V →
      Nat.card ↥(V ⊓ Subgroup.normalizer (V₂ : Set K)) =
        Nat.card ↥(V ⊓ Subgroup.normalizer (V₃ : Set K)) →
        ∃ k ∈ Subgroup.normalizer (V : Set K), conjSubgroup k V₂ = V₃

section Transfer

variable {K : Type} [Group K]

private def psi (φ : K ≃* alternatingGroup (Fin 6)) : K →* P6 :=
  (alternatingGroup (Fin 6)).subtype.comp φ.toMonoidHom

private theorem psi_injective (φ : K ≃* alternatingGroup (Fin 6)) :
    Function.Injective (psi φ) :=
  Subtype.val_injective.comp φ.injective

private theorem psi_sign (φ : K ≃* alternatingGroup (Fin 6)) (k : K) :
    Equiv.Perm.sign (psi φ k) = 1 :=
  Equiv.Perm.mem_alternatingGroup.1 (φ k).2

private theorem psi_surj (φ : K ≃* alternatingGroup (Fin 6)) {σ : P6}
    (h : Equiv.Perm.sign σ = 1) : ∃ k, psi φ k = σ :=
  ⟨φ.symm ⟨σ, Equiv.Perm.mem_alternatingGroup.2 h⟩, by simp [psi]⟩

private theorem exists_klein_gens [Finite K] {V : Subgroup K} (h : 2 < Nat.card V) :
    ∃ a b : K, a ∈ V ∧ b ∈ V ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have h1 : 2 < (V : Set K).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact h
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 h1
  by_cases hx1 : x = 1
  · exact ⟨y, z, hy, hz, fun h => hxy (hx1.trans h.symm), fun h => hxz (hx1.trans h.symm), hyz⟩
  · by_cases hy1 : y = 1
    · exact ⟨x, z, hx, hz, hx1, fun h => hyz (hy1.trans h.symm), hxz⟩
    · exact ⟨x, y, hx, hy, hx1, hy1, hxy⟩

private structure KData (V : Subgroup K) (a b : K) : Prop where
  elem : IsElemAbelian 2 V
  ha : a ∈ V
  hb : b ∈ V
  ha1 : a ≠ 1
  hb1 : b ≠ 1
  hab : a ≠ b

private theorem KData.klein_pair (φ : K ≃* alternatingGroup (Fin 6)) {V : Subgroup K} {a b : K}
    (d : KData V a b) : KleinPair (psi φ a) (psi φ b) where
  ea := psi_sign φ a
  eb := psi_sign φ b
  a1 := fun h => d.ha1 ((map_eq_one_iff (psi φ) (psi_injective φ)).1 h)
  b1 := fun h => d.hb1 ((map_eq_one_iff (psi φ) (psi_injective φ)).1 h)
  ab := fun h => d.hab (psi_injective φ h)
  sa := by rw [← map_mul, ← pow_two, d.elem.2 a d.ha, map_one]
  sb := by rw [← map_mul, ← pow_two, d.elem.2 b d.hb, map_one]
  comm := by rw [← map_mul, ← map_mul, elemAbelian_mul_comm d.elem d.ha d.hb]

private theorem KData.mem_iff (φ : K ≃* alternatingGroup (Fin 6)) {V : Subgroup K} {a b : K}
    (d : KData V a b) (v : K) : v ∈ V ↔ v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by
  have hP := d.klein_pair φ
  constructor
  · intro hv
    have hmem := klein_closed hP (e := psi φ v) (psi_sign φ v)
      (by rw [← map_mul, ← pow_two, d.elem.2 v hv, map_one])
      (by rw [← map_mul, ← map_mul, elemAbelian_mul_comm d.elem hv d.ha])
      (by rw [← map_mul, ← map_mul, elemAbelian_mul_comm d.elem hv d.hb])
    simp only [kleinList, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h
    · exact Or.inl ((map_eq_one_iff _ (psi_injective φ)).1 h)
    · exact Or.inr (Or.inl (psi_injective φ h))
    · exact Or.inr (Or.inr (Or.inl (psi_injective φ h)))
    · exact Or.inr (Or.inr (Or.inr (psi_injective φ (by rw [map_mul]; exact h))))
  · rintro (h | h | h | h)
    · rw [h]; exact V.one_mem
    · rw [h]; exact d.ha
    · rw [h]; exact d.hb
    · rw [h]; exact V.mul_mem d.ha d.hb

private theorem KData.mem_S (φ : K ≃* alternatingGroup (Fin 6)) {V : Subgroup K} {a b : K}
    (d : KData V a b) (s : P6) :
    s ∈ kleinList (psi φ a) (psi φ b) ↔ ∃ v ∈ V, psi φ v = s := by
  simp only [kleinList, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (h | h | h | h)
    · exact ⟨1, V.one_mem, by rw [map_one, h]⟩
    · exact ⟨a, d.ha, h.symm⟩
    · exact ⟨b, d.hb, h.symm⟩
    · exact ⟨a * b, V.mul_mem d.ha d.hb, by rw [map_mul, h]⟩
  · rintro ⟨v, hv, rfl⟩
    rcases (d.mem_iff φ v).1 hv with h | h | h | h
    · exact Or.inl (by rw [h, map_one])
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h, map_mul])))

private theorem KData.mem_V_iff (φ : K ≃* alternatingGroup (Fin 6)) {V : Subgroup K} {a b : K}
    (d : KData V a b) (v : K) : v ∈ V ↔ psi φ v ∈ kleinList (psi φ a) (psi φ b) := by
  rw [d.mem_S φ]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    rw [psi_injective φ hwv] at hw
    exact hw

private theorem KData.normalizer_iff (φ : K ≃* alternatingGroup (Fin 6)) {V : Subgroup K}
    {a b : K} (d : KData V a b) (k : K) :
    k ∈ Subgroup.normalizer (V : Set K) ↔ Nrm (kleinList (psi φ a) (psi φ b)) (psi φ k) := by
  unfold Nrm
  rw [Subgroup.mem_set_normalizer_iff, Subgroup.mem_set_normalizer_iff]
  constructor
  · intro hk s
    show s ∈ kleinList (psi φ a) (psi φ b) ↔
      psi φ k * s * (psi φ k)⁻¹ ∈ kleinList (psi φ a) (psi φ b)
    constructor
    · intro hs
      obtain ⟨v, hv, rfl⟩ := (d.mem_S φ s).1 hs
      have h1 : k * v * k⁻¹ ∈ V := (hk v).1 hv
      have h2 := (d.mem_V_iff φ _).1 h1
      simpa [map_mul, map_inv] using h2
    · intro hs
      obtain ⟨h', hh', hh'e⟩ := (d.mem_S φ _).1 hs
      have h1 : k⁻¹ * h' * k ∈ V := by
        have h3 : k * (k⁻¹ * h' * k) * k⁻¹ ∈ V := by
          have : k * (k⁻¹ * h' * k) * k⁻¹ = h' := by group
          rw [this]
          exact hh'
        exact (hk (k⁻¹ * h' * k)).2 h3
      have h2 := (d.mem_V_iff φ _).1 h1
      have : psi φ (k⁻¹ * h' * k) = s := by
        simp only [map_mul, map_inv, hh'e]
        group
      rwa [this] at h2
  · intro hn h
    show h ∈ V ↔ k * h * k⁻¹ ∈ V
    rw [d.mem_V_iff φ h, d.mem_V_iff φ (k * h * k⁻¹)]
    have := hn (psi φ h)
    simpa [map_mul, map_inv] using this

private theorem mem_normalizer_conjSubgroup {V : Subgroup K} {k v : K} :
    v ∈ Subgroup.normalizer ((conjSubgroup k V : Subgroup K) : Set K) ↔
      k⁻¹ * v * k ∈ Subgroup.normalizer (V : Set K) := by
  rw [mem_normalizer_iff_conjSubgroup_eq, mem_normalizer_iff_conjSubgroup_eq,
    conjSubgroup_conjSubgroup]
  constructor
  · intro h
    have := congrArg (conjSubgroup k⁻¹) h
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one, ← mul_assoc] at this
    exact this
  · intro h
    have := congrArg (conjSubgroup k) h
    rw [conjSubgroup_conjSubgroup] at this
    have e : k * (k⁻¹ * v * k) = v * k := by group
    rwa [e] at this

private theorem conjSubgroup_eq_of_mem_normalizer {V : Subgroup K} {a b : K}
    (h : b⁻¹ * a ∈ Subgroup.normalizer (V : Set K)) :
    conjSubgroup a V = conjSubgroup b V := by
  have h1 := mem_normalizer_iff_conjSubgroup_eq.1 h
  calc conjSubgroup a V = conjSubgroup (b * (b⁻¹ * a)) V := by rw [mul_inv_cancel_left]
    _ = conjSubgroup b (conjSubgroup (b⁻¹ * a) V) := (conjSubgroup_conjSubgroup _ _ _).symm
    _ = conjSubgroup b V := by rw [h1]

private theorem card_ne_one_iff {V : Subgroup K} (k : K) :
    Nat.card ↥(V ⊓ Subgroup.normalizer ((conjSubgroup k V : Subgroup K) : Set K)) ≠ 1 ↔
      ∃ v ∈ V, v ≠ 1 ∧ k⁻¹ * v * k ∈ Subgroup.normalizer (V : Set K) := by
  rw [Ne, Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
  push Not
  constructor
  · rintro ⟨x, hx, hx1⟩
    exact ⟨x, (Subgroup.mem_inf.1 hx).1, hx1,
      mem_normalizer_conjSubgroup.1 (Subgroup.mem_inf.1 hx).2⟩
  · rintro ⟨v, hv, hv1, hn⟩
    exact ⟨v, Subgroup.mem_inf.2 ⟨hv, mem_normalizer_conjSubgroup.2 hn⟩, hv1⟩

end Transfer

theorem a6KleinOrbit : A6KleinOrbit := by
  intro K _ hK V V₂ V₃ hV hcard hV₂ hV₃ h₂ h₃ hcards
  obtain ⟨φ⟩ := hK
  have : Finite K := Finite.of_equiv _ φ.symm.toEquiv
  obtain ⟨k₂, rfl⟩ := hV₂
  obtain ⟨k₃, rfl⟩ := hV₃
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := exists_klein_gens hcard
  have d : KData V a b := ⟨hV, ha, hb, ha1, hb1, hab⟩
  have hP := d.klein_pair φ
  have hN := d.normalizer_iff φ
  have hnrm : ∀ k : K, conjSubgroup k V ≠ V →
      ¬ Nrm (kleinList (psi φ a) (psi φ b)) (psi φ k) := by
    intro k hk hn
    exact hk (mem_normalizer_iff_conjSubgroup_eq.1 ((hN k).2 hn))
  have hnt : ∀ k : K, ntP (kleinList (psi φ a) (psi φ b)) (psi φ k) ↔
      ∃ v ∈ V, v ≠ 1 ∧ k⁻¹ * v * k ∈ Subgroup.normalizer (V : Set K) := by
    intro k
    unfold ntP
    constructor
    · rintro ⟨s, hs, hs1, hsn⟩
      obtain ⟨v, hv, rfl⟩ := (d.mem_S φ s).1 hs
      refine ⟨v, hv, fun h => hs1 (by rw [h, map_one]), ?_⟩
      rw [hN]
      simpa [map_mul, map_inv] using hsn
    · rintro ⟨v, hv, hv1, hn⟩
      refine ⟨psi φ v, (d.mem_V_iff φ v).1 hv,
        fun h => hv1 ((map_eq_one_iff _ (psi_injective φ)).1 h), ?_⟩
      have := (hN _).1 hn
      simpa [map_mul, map_inv] using this
  have hntiff : ntP (kleinList (psi φ a) (psi φ b)) (psi φ k₂) ↔
      ntP (kleinList (psi φ a) (psi φ b)) (psi φ k₃) := by
    rw [hnt, hnt, ← card_ne_one_iff, ← card_ne_one_iff, hcards]
  obtain ⟨n, hn1, hn2, hn3⟩ := klein_orbit hP (hnrm k₂ h₂) (hnrm k₃ h₃) hntiff
  obtain ⟨k₀, rfl⟩ := psi_surj φ hn1
  refine ⟨k₀, (hN k₀).2 hn2, ?_⟩
  have hk : k₃⁻¹ * (k₀ * k₂) ∈ Subgroup.normalizer (V : Set K) := by
    rw [hN]
    simpa [map_mul, map_inv, mul_assoc] using hn3
  rw [conjSubgroup_conjSubgroup]
  exact conjSubgroup_eq_of_mem_normalizer hk

end CFSG.CGT.Timmesfeld75
