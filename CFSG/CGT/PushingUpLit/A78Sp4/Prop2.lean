module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

variable {G : Type*} [Group G]

theorem prop2_aux {Z V W T : Subgroup G} (U : Subgroup G)
    (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x ∧ x * x = 1)
    (hcardU : Nat.card V ≤ Nat.card U)
    (hZV : Z ≤ V) (hZW : Z ≤ W)
    (hA : ∀ E : Subgroup G, E ≤ T → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x ∧ x * x = 1) →
        Nat.card V ≤ Nat.card E → E = V ∨ E = W)
    (hTI : ∀ g h : G, Z.map (MulAut.conj g).toMonoidHom ⊓ Z.map (MulAut.conj h).toMonoidHom ≠ ⊥ →
        Z.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj h).toMonoidHom)
    (hT : ∀ P : Subgroup G, P ≤ Subgroup.normalizer (Z : Set G) → IsPGroup 2 P →
        ∃ n ∈ Subgroup.normalizer (Z : Set G), ∀ x ∈ P, n * x * n⁻¹ ∈ T)
    {g x : G} (hxA : x ∈ Z.map (MulAut.conj g).toMonoidHom) (hx1 : x ≠ 1) (hxU : x ∈ U) :
    Z.map (MulAut.conj g).toMonoidHom ≤ U := by
  have memA : ∀ {a : G}, a ∈ Z.map (MulAut.conj g).toMonoidHom ↔ ∃ z ∈ Z, g * z * g⁻¹ = a := by
    intro a
    simp [Subgroup.mem_map]
  have hnorm : ∀ v ∈ U, ∀ a ∈ Z.map (MulAut.conj g).toMonoidHom,
      v * a * v⁻¹ ∈ Z.map (MulAut.conj g).toMonoidHom := by
    intro v hv a ha
    have hxA' : x ∈ Z.map (MulAut.conj (v * g)).toMonoidHom := by
      obtain ⟨z, hz, hzx⟩ := memA.1 hxA
      refine Subgroup.mem_map.2 ⟨z, hz, ?_⟩
      have hvx : v * x = x * v := (hU v hv x hxU).1
      have : (v * g) * z * (v * g)⁻¹ = v * x * v⁻¹ := by
        rw [← hzx]; group
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [this, hvx]; group
    have hne : Z.map (MulAut.conj g).toMonoidHom ⊓ Z.map (MulAut.conj (v * g)).toMonoidHom ≠ ⊥ := by
      intro hbot
      apply hx1
      have : x ∈ Z.map (MulAut.conj g).toMonoidHom ⊓ Z.map (MulAut.conj (v * g)).toMonoidHom :=
        ⟨hxA, hxA'⟩
      rw [hbot] at this
      simpa using this
    have heq := hTI g (v * g) hne
    obtain ⟨z₁, hz₁, rfl⟩ := memA.1 ha
    rw [heq]
    refine Subgroup.mem_map.2 ⟨z₁, hz₁, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hconj : ∀ v ∈ U, ∀ h ∈ Z, (g⁻¹ * v * g) * h * (g⁻¹ * v * g)⁻¹ ∈ Z := by
    intro v hv h hh
    have ha : g * h * g⁻¹ ∈ Z.map (MulAut.conj g).toMonoidHom := memA.2 ⟨h, hh, rfl⟩
    obtain ⟨z', hz', hz'e⟩ := memA.1 (hnorm v hv _ ha)
    have : (g⁻¹ * v * g) * h * (g⁻¹ * v * g)⁻¹ = z' := by
      calc (g⁻¹ * v * g) * h * (g⁻¹ * v * g)⁻¹ = g⁻¹ * (v * (g * h * g⁻¹) * v⁻¹) * g := by group
        _ = g⁻¹ * (g * z' * g⁻¹) * g := by rw [hz'e]
        _ = z' := by group
    rw [this]; exact hz'
  have hnormZ : ∀ v ∈ U, (g⁻¹ * v * g) ∈ Subgroup.normalizer (Z : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hconj v hv h hh
    · intro hh
      have := hconj v⁻¹ (U.inv_mem hv) _ hh
      have e : (g⁻¹ * v⁻¹ * g) * ((g⁻¹ * v * g) * h * (g⁻¹ * v * g)⁻¹) * (g⁻¹ * v⁻¹ * g)⁻¹ = h := by
        group
      rw [e] at this; exact this
  let U₁ : Subgroup G := U.map (MulAut.conj g⁻¹).toMonoidHom
  have hU₁n : U₁ ≤ Subgroup.normalizer (Z : Set G) := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hnormZ v hv
  have hU₁p : IsPGroup 2 U₁ := by
    rintro ⟨y, hy⟩
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
    refine ⟨1, Subtype.ext ?_⟩
    have hvv := (hU v hv v hv).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, pow_one, Subgroup.coe_pow,
      Subgroup.coe_one]
    calc (g⁻¹ * v * g) ^ 2 = g⁻¹ * (v * v) * g := by rw [pow_two]; group
      _ = 1 := by rw [hvv]; group
  obtain ⟨n, hn, hnT⟩ := hT U₁ hU₁n hU₁p
  let φ : G →* G := (MulAut.conj (n * g⁻¹)).toMonoidHom
  let E : Subgroup G := U.map φ
  have hET : E ≤ T := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
    have h1 : g⁻¹ * v * g ∈ U₁ := Subgroup.mem_map.2 ⟨v, hv, by simp⟩
    have := hnT _ h1
    have e : n * (g⁻¹ * v * g) * n⁻¹ = φ v := by
      simp only [φ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rwa [e] at this
  have hEab : ∀ y ∈ E, ∀ y' ∈ E, y * y' = y' * y ∧ y * y = 1 := by
    intro y hy y' hy'
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.1 hy'
    obtain ⟨h1, h2⟩ := hU v hv v' hv'
    refine ⟨?_, ?_⟩
    · rw [← φ.map_mul, ← φ.map_mul, h1]
    · rw [← φ.map_mul, (hU v hv v hv).2, φ.map_one]
  have hEcard : Nat.card V ≤ Nat.card E := by
    have : Nat.card E = Nat.card U := by
      apply Subgroup.card_map_of_injective
      exact (MulAut.conj (n * g⁻¹)).injective
    rw [this]; exact hcardU
  have hZE : Z ≤ E := by
    rcases hA E hET hEab hEcard with hE | hE
    · rw [hE]; exact hZV
    · rw [hE]; exact hZW
  intro a ha
  obtain ⟨z, hz, rfl⟩ := memA.1 ha
  have hz' : n * z * n⁻¹ ∈ Z := ((Subgroup.mem_normalizer_iff.1 hn) z).1 hz
  obtain ⟨v, hv, hve⟩ := Subgroup.mem_map.1 (hZE hz')
  have e1 : φ v = (n * g⁻¹) * v * (n * g⁻¹)⁻¹ := by
    simp only [φ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have : g * z * g⁻¹ = v := by
    have h3 : (n * g⁻¹) * v * (n * g⁻¹)⁻¹ = n * z * n⁻¹ := by rw [← e1]; exact hve
    calc g * z * g⁻¹ = (g * n⁻¹) * (n * z * n⁻¹) * (g * n⁻¹)⁻¹ := by group
      _ = (g * n⁻¹) * ((n * g⁻¹) * v * (n * g⁻¹)⁻¹) * (g * n⁻¹)⁻¹ := by rw [h3]
      _ = v := by group
  rw [this]; exact hv

theorem prop2 {Z V W T J S : Subgroup G}
    (hZV : Z ≤ V) (hZW : Z ≤ W)
    (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x ∧ x * x = 1)
    (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x ∧ x * x = 1)
    (hcard : Nat.card V = Nat.card W)
    (hA : ∀ E : Subgroup G, E ≤ T → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x ∧ x * x = 1) →
        Nat.card V ≤ Nat.card E → E = V ∨ E = W)
    (hTI : ∀ g h : G, Z.map (MulAut.conj g).toMonoidHom ⊓ Z.map (MulAut.conj h).toMonoidHom ≠ ⊥ →
        Z.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj h).toMonoidHom)
    (hT : ∀ P : Subgroup G, P ≤ Subgroup.normalizer (Z : Set G) → IsPGroup 2 P →
        ∃ n ∈ Subgroup.normalizer (Z : Set G), ∀ x ∈ P, n * x * n⁻¹ ∈ T)
    (hinv : ∀ x ∈ J, x ≠ 1 → x * x = 1 → x ∈ V ∨ x ∈ W)
    (hAJ : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ S →
      ∃ x ∈ Z.map (MulAut.conj g).toMonoidHom ⊓ J, x ≠ 1) :
    ∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ S →
      Z.map (MulAut.conj g).toMonoidHom ≤ V ∨ Z.map (MulAut.conj g).toMonoidHom ≤ W := by
  intro g hgS
  obtain ⟨x, ⟨hxA, hxJ⟩, hx1⟩ := hAJ g hgS
  have hxx : x * x = 1 := by
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hxA
    have hzz := (hV z (hZV hz) z (hZV hz)).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  rcases hinv x hxJ hx1 hxx with hxV | hxW
  · exact Or.inl (prop2_aux V hV le_rfl hZV hZW hA hTI hT hxA hx1 hxV)
  · exact Or.inr (prop2_aux W hW hcard.le hZV hZW hA hTI hT hxA hx1 hxW)

end CFSG.CGT.PushingUpLit.A78Sp4
