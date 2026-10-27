module

public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

@[expose] def cj (g : Y) (H : Subgroup Y) : Subgroup Y := H.map (MulAut.conj g).toMonoidHom

theorem mem_cj {g : Y} {H : Subgroup Y} {z : Y} : z ∈ cj g H ↔ g⁻¹ * z * g ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [cj, MulAut.conj_apply, mul_assoc] using hh
  · intro hz
    exact ⟨g⁻¹ * z * g, hz, by simp [cj, MulAut.conj_apply, mul_assoc]⟩

theorem cj_mul (g h : Y) (H : Subgroup Y) : cj (g * h) H = cj g (cj h H) := by
  ext z
  simp only [mem_cj, mul_inv_rev, mul_assoc]

theorem cj_one (H : Subgroup Y) : cj 1 H = H := by
  ext z
  simp [mem_cj]

theorem cj_sup (g : Y) (A C : Subgroup Y) : cj g (A ⊔ C) = cj g A ⊔ cj g C :=
  Subgroup.map_sup _ _ _

theorem cj_mono (g : Y) {A C : Subgroup Y} (h : A ≤ C) : cj g A ≤ cj g C :=
  Subgroup.map_mono h

@[expose] def ElemCommute (A C : Subgroup Y) : Prop := ∀ a ∈ A, ∀ c ∈ C, a * c = c * a

theorem commutes_symm {A C : Subgroup Y} (h : ElemCommute A C) : ElemCommute C A :=
  fun c hc a ha => (h a ha c hc).symm

theorem commutes_iff_le_centralizer {A C : Subgroup Y} :
    ElemCommute A C ↔ C ≤ Subgroup.centralizer (A : Set Y) := by
  constructor
  · intro h c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact h a ha c hc
  · intro h a ha c hc
    exact Subgroup.mem_centralizer_iff.1 (h hc) a ha

theorem commutes_sup_right {A C C' : Subgroup Y} (h : ElemCommute A C) (h' : ElemCommute A C') :
    ElemCommute A (C ⊔ C') :=
  commutes_iff_le_centralizer.2 (sup_le (commutes_iff_le_centralizer.1 h)
    (commutes_iff_le_centralizer.1 h'))

theorem commutes_sup_left {A A' C : Subgroup Y} (h : ElemCommute A C) (h' : ElemCommute A' C) :
    ElemCommute (A ⊔ A') C :=
  commutes_symm (commutes_sup_right (commutes_symm h) (commutes_symm h'))

theorem commutes_cj (g : Y) {A C : Subgroup Y} (h : ElemCommute A C) :
    ElemCommute (cj g A) (cj g C) := by
  intro a ha c hc
  have hx : g⁻¹ * a * g ∈ A := mem_cj.1 ha
  have hy : g⁻¹ * c * g ∈ C := mem_cj.1 hc
  have e := h _ hx _ hy
  calc a * c = g * ((g⁻¹ * a * g) * (g⁻¹ * c * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * c * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [e]
    _ = c * a := by group

theorem commutes_normalizer {A C : Subgroup Y} (h : ElemCommute A C) :
    C ≤ Subgroup.normalizer (A : Set Y) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have e := h a ha c hc
    have h1 : c * a * c⁻¹ = a := by rw [← e]; group
    rw [h1]
    exact ha
  · intro ha'
    have e := h _ ha' c⁻¹ (C.inv_mem hc)
    have h2 : c⁻¹ * (c * a * c⁻¹) * c = c * a * c⁻¹ := by
      calc c⁻¹ * (c * a * c⁻¹) * c = (c * a * c⁻¹) * c⁻¹ * c := by rw [e]
        _ = c * a * c⁻¹ := by group
    have h4 : a = c * a * c⁻¹ := by
      calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
        _ = c * a * c⁻¹ := h2
    rw [h4]
    exact ha'

theorem mem_sup_of_commutes {A C : Subgroup Y} (h : ElemCommute A C) :
    ∀ t ∈ A ⊔ C, ∃ a ∈ A, ∃ c ∈ C, t = a * c := by
  let Q : Subgroup Y :=
    { carrier := {t | ∃ a ∈ A, ∃ c ∈ C, t = a * c}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, c₁, hc₁, rfl⟩ ⟨a₂, ha₂, c₂, hc₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, c₁ * c₂, C.mul_mem hc₁ hc₂, ?_⟩
        have e := h a₂ ha₂ c₁ hc₁
        calc a₁ * c₁ * (a₂ * c₂) = a₁ * (c₁ * a₂) * c₂ := by group
          _ = a₁ * (a₂ * c₁) * c₂ := by rw [← e]
          _ = a₁ * a₂ * (c₁ * c₂) := by group
      one_mem' := ⟨1, A.one_mem, 1, C.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, c, hc, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, c⁻¹, C.inv_mem hc, ?_⟩
        have e := h a ha c hc
        have e' : c⁻¹ * a⁻¹ = a⁻¹ * c⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, e]
        rw [mul_inv_rev]
        exact e' }
  have hle : A ⊔ C ≤ Q :=
    sup_le (fun a ha => ⟨a, ha, 1, C.one_mem, by simp⟩)
      (fun c hc => ⟨1, A.one_mem, c, hc, by simp⟩)
  intro t ht
  exact hle ht

theorem mem_normalizer_iff_cj {g : Y} {Q : Subgroup Y} :
    g ∈ Subgroup.normalizer (Q : Set Y) ↔ cj g Q = Q := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hN
    ext z
    rw [mem_cj]
    have h1 := hN (g⁻¹ * z * g)
    rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at h1
    exact h1
  · intro hc h
    have h1 := @mem_cj Y _ g Q (g * h * g⁻¹)
    rw [hc, show g⁻¹ * (g * h * g⁻¹) * g = h by group] at h1
    exact h1.symm

theorem isElemAbelian_of (p : ℕ) {E : Subgroup Y} (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hp : ∀ x ∈ E, x ^ p = 1) : IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2)⟩⟩, hp⟩

theorem isElemAbelian_sup {p : ℕ} {A C : Subgroup Y} (hA : IsElemAbelian p A)
    (hC : IsElemAbelian p C) (hAC : ElemCommute A C) : IsElemAbelian p (A ⊔ C) := by
  apply isElemAbelian_of p
  · intro s hs t ht
    obtain ⟨a, ha, c, hc, rfl⟩ := mem_sup_of_commutes hAC s hs
    obtain ⟨a', ha', c', hc', rfl⟩ := mem_sup_of_commutes hAC t ht
    have e3 := hAC a' ha' c hc
    have e4 := hAC a ha c' hc'
    have e1 := isElemAbelian_commute hA ha ha'
    have e2 := isElemAbelian_commute hC hc hc'
    calc a * c * (a' * c') = a * (c * a') * c' := by group
      _ = a * (a' * c) * c' := by rw [← e3]
      _ = (a * a') * (c * c') := by group
      _ = (a' * a) * (c' * c) := by rw [e1, e2]
      _ = a' * (a * c') * c := by group
      _ = a' * (c' * a) * c := by rw [e4]
      _ = a' * c' * (a * c) := by group
  · intro x hx
    obtain ⟨a, ha, c, hc, rfl⟩ := mem_sup_of_commutes hAC x hx
    have hcomm : Commute a c := hAC a ha c hc
    rw [hcomm.mul_pow, hA.2 a ha, hC.2 c hc, one_mul]

theorem isElemAbelian_zpowers (p : ℕ) {y : Y} (hy : y ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers y) := by
  apply isElemAbelian_of p
  · intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow_self y m n).eq
  · intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]

theorem isPGroup_sup {A C : Subgroup Y} (hA : IsPGroup 2 A) (hC : IsPGroup 2 C)
    (hAC : ElemCommute A C) : IsPGroup 2 ↥(A ⊔ C) := by
  intro g
  obtain ⟨a, ha, c, hc, hg⟩ := mem_sup_of_commutes hAC g.1 g.2
  obtain ⟨n₁, hn₁⟩ := hA ⟨a, ha⟩
  obtain ⟨n₂, hn₂⟩ := hC ⟨c, hc⟩
  have hn₁' : a ^ 2 ^ n₁ = 1 := by
    have := congrArg Subtype.val hn₁
    simpa using this
  have hn₂' : c ^ 2 ^ n₂ = 1 := by
    have := congrArg Subtype.val hn₂
    simpa using this
  have hE : 2 ^ (n₁ + n₂) = 2 ^ n₁ * 2 ^ n₂ := pow_add 2 n₁ n₂
  have ha1 : a ^ 2 ^ (n₁ + n₂) = 1 := by rw [hE, pow_mul, hn₁', one_pow]
  have hc1 : c ^ 2 ^ (n₁ + n₂) = 1 := by rw [hE, mul_comm, pow_mul, hn₂', one_pow]
  refine ⟨n₁ + n₂, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, hg, (show Commute a c from hAC a ha c hc).mul_pow,
    ha1, hc1, one_mul]

end CFSG.LocalAnalysis.GLTheoremA.I114
