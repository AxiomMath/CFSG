module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoPar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSuzuki

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

section Abstract

variable {S : Type} [Group S] [Finite S]

theorem eq_of_isPGroup_of_sylow {T Y : Subgroup S} (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y)
    (hY : IsPGroup 2 Y) : Y = T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 hT.2.1)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card.1 hY)
  have hSidx : Nat.card T * (T.subgroupOf ⊤).index = Nat.card S := by
    have := Subgroup.card_mul_index (T.subgroupOf ⊤)
    rwa [show Nat.card (T.subgroupOf ⊤ : Subgroup (⊤ : Subgroup S)) = Nat.card T from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv, Subgroup.card_top] at this
  have hOdvd : Nat.card Y ∣ Nat.card S := Subgroup.card_subgroup_dvd_card Y
  rw [← hSidx, hm, hk] at hOdvd
  have hcop : Nat.Coprime (2 ^ m) ((T.subgroupOf ⊤).index) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hT.2.2)
  have hdvd : 2 ^ m ∣ 2 ^ k := hcop.dvd_of_dvd_mul_right hOdvd
  have hmk : m ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hle : Nat.card Y ≤ Nat.card T := by
    rw [hm, hk]; exact Nat.pow_le_pow_right (by norm_num) hmk
  exact (Subgroup.eq_of_le_of_card_ge hTY hle).symm

theorem mem_of_two_element_of_mem_normalizer {U : Subgroup S} (hU : IsSylowTwoOf U ⊤) {x : S}
    (hx : x ∈ Subgroup.normalizer (U : Set S)) (h2 : ∃ k : ℕ, orderOf x = 2 ^ k) : x ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2
  have hp : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.iff_orderOf.2 fun ⟨y, hy⟩ => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hd : orderOf (x ^ m) ∣ 2 ^ k := hk ▸ orderOf_dvd_of_pow_eq_one (by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow])
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact ⟨j, by rw [← hj, ← Subgroup.orderOf_coe]⟩
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set S) := by
    rw [Subgroup.zpowers_le]; exact hx
  have h3 : IsPGroup 2 (U ⊔ Subgroup.zpowers x : Subgroup S) :=
    hU.2.1.to_sup_of_normal_left' hp hle
  have h4 := eq_of_isPGroup_of_sylow hU le_sup_left h3
  have : x ∈ (U ⊔ Subgroup.zpowers x : Subgroup S) := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rwa [h4] at this

theorem exists_conj_mem_of_two_element_sub {P U : Subgroup S} (hUP : U ≤ P)
    (hU : IsSylowTwoOf U ⊤) {x : S} (hx : x ∈ P) (h2 : ∃ k : ℕ, orderOf x = 2 ^ k) :
    ∃ g ∈ P, g⁻¹ * x * g ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ U.index := by
    have := hU.2.2
    rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at this
  have hS : IsSylowTwoOf (U.subgroupOf P) (⊤ : Subgroup ↥P) := by
    refine ⟨le_top, hU.2.1.comap_subtype, ?_⟩
    rw [show ((U.subgroupOf P).subgroupOf ⊤).index = (U.subgroupOf P).index from
      Subgroup.relIndex_top_right _]
    intro hd
    exact hidx (hd.trans (Subgroup.relIndex_dvd_index_of_le hUP))
  obtain ⟨k, hk⟩ := h2
  obtain ⟨h, hh⟩ := exists_conj_mem_of_two_element hS (g := (⟨x, hx⟩ : ↥P))
    ⟨k, by rw [← Subgroup.orderOf_coe] at *; exact hk⟩
  exact ⟨h, h.2, Subgroup.mem_subgroupOf.1 hh⟩

structure TwoCell (U H : Subgroup S) (n : S) (P : Subgroup S) : Prop where
  hHU : H ≤ Subgroup.normalizer (U : Set S)
  hn : n ∈ Subgroup.normalizer (H : Set S)
  hUP : U ≤ P
  hP : ∀ g ∈ P, g ∈ H ⊔ U ∨ ∃ b ∈ H ⊔ U, ∃ b' ∈ H ⊔ U, g = b * n * b'

variable {U H : Subgroup S} {n : S} {P : Subgroup S}

theorem TwoCell.mem_conj_normalizer (h : TwoCell U H n P) {h₁ : S} (hh : h₁ ∈ H) :
    n⁻¹ * h₁ * n ∈ H := by
  have := (Subgroup.mem_normalizer_iff.1 h.hn (n⁻¹ * h₁ * n)).2 (by simpa [mul_assoc] using hh)
  exact this

theorem TwoCell.conj_mem (h : TwoCell U H n P) {h₁ : S} (hh : h₁ ∈ H) {u : S} (hu : u ∈ U) :
    h₁ * u * h₁⁻¹ ∈ U :=
  (Subgroup.mem_normalizer_iff.1 (h.hHU hh) u).1 hu

theorem TwoCell.mem_mul (h : TwoCell U H n P) {b : S} (hb : b ∈ H ⊔ U) :
    ∃ u ∈ U, ∃ h₁ ∈ H, b = u * h₁ := by
  have : b ∈ ((U ⊔ H : Subgroup S) : Set S) := by rwa [sup_comm]
  rw [Subgroup.coe_mul_of_right_le_normalizer_left U H h.hHU] at this
  obtain ⟨u, hu, h₁, hh, rfl⟩ := this
  exact ⟨u, hu, h₁, hh, rfl⟩

theorem TwoCell.mem_mul' (h : TwoCell U H n P) {b : S} (hb : b ∈ H ⊔ U) :
    ∃ h₁ ∈ H, ∃ u ∈ U, b = h₁ * u := by
  have : b ∈ ((H ⊔ U : Subgroup S) : Set S) := hb
  rw [Subgroup.coe_mul_of_left_le_normalizer_right H U h.hHU] at this
  obtain ⟨h₁, hh, u, hu, rfl⟩ := this
  exact ⟨h₁, hh, u, hu, rfl⟩

theorem TwoCell.conj_conj_mem (h : TwoCell U H n P) {h₁ : S} (hh : h₁ ∈ H) {u : S} (hu : u ∈ U) :
    h₁ * (n * u * n⁻¹) * h₁⁻¹ ∈ U.map (MulAut.conj n).toMonoidHom := by
  have hh' := h.mem_conj_normalizer hh
  refine ⟨(n⁻¹ * h₁ * n) * u * (n⁻¹ * h₁ * n)⁻¹, h.conj_mem hh' hu, ?_⟩
  show n * ((n⁻¹ * h₁ * n) * u * (n⁻¹ * h₁ * n)⁻¹) * n⁻¹ = h₁ * (n * u * n⁻¹) * h₁⁻¹
  group

theorem TwoCell.conj_le (h : TwoCell U H n P) {X : Subgroup S} (hUX : U ≤ X) (hXP : X ≤ P)
    (hXB : ¬ X ≤ H ⊔ U) : U.map (MulAut.conj n).toMonoidHom ≤ X := by
  obtain ⟨g, hgX, hgB⟩ := Set.not_subset.1 hXB
  rcases h.hP g (hXP hgX) with hB | ⟨b, hb, b', hb', rfl⟩
  · exact absurd hB hgB
  obtain ⟨u₁, hu₁, h₁, hh₁, rfl⟩ := h.mem_mul hb
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := h.mem_mul' hb'
  have hm : h₁ * n * h₂ ∈ X := by
    have e : h₁ * n * h₂ = u₁⁻¹ * (u₁ * h₁ * n * (h₂ * u₂)) * u₂⁻¹ := by group
    rw [e]
    exact X.mul_mem (X.mul_mem (X.inv_mem (hUX hu₁)) hgX) (X.inv_mem (hUX hu₂))
  rintro _ ⟨u, hu, rfl⟩
  have hht := h.mem_conj_normalizer (H.inv_mem hh₁)
  set ht := n⁻¹ * h₁⁻¹ * n with hhtdef
  have hu'' : ht * u * ht⁻¹ ∈ U := h.conj_mem hht hu
  have hmem : h₂⁻¹ * (ht * u * ht⁻¹) * h₂ ∈ U := by
    have := h.conj_mem (H.inv_mem hh₂) hu''
    simpa using this
  have e : (MulAut.conj n).toMonoidHom u = (h₁ * n * h₂) * (h₂⁻¹ * (ht * u * ht⁻¹) * h₂) *
      (h₁ * n * h₂)⁻¹ := by
    show n * u * n⁻¹ = _
    rw [hhtdef]
    group
  rw [e]
  exact X.mul_mem (X.mul_mem hm (hUX hmem)) (X.inv_mem hm)

theorem TwoCell.pElement_le (h : TwoCell U H n P) (hU : IsSylowTwoOf U ⊤) :
    pElementSubgroup 2 P ≤ U ⊔ U.map (MulAut.conj n).toMonoidHom := by
  unfold pElementSubgroup
  rw [Subgroup.closure_le]
  rintro x ⟨hxP, k, hk⟩
  obtain ⟨g, hgP, hgu⟩ := exists_conj_mem_of_two_element_sub h.hUP hU hxP ⟨k, hk⟩
  have hx : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  set u := g⁻¹ * x * g with hu
  rw [hx]
  rcases h.hP g hgP with hB | ⟨b, hb, b', hb', rfl⟩
  · have hgN : g ∈ Subgroup.normalizer (U : Set S) :=
      (sup_le h.hHU Subgroup.le_normalizer : H ⊔ U ≤ _) hB
    exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hgN u).1 hgu)
  obtain ⟨u₁, hu₁, h₁, hh₁, rfl⟩ := h.mem_mul hb
  have hb'N : b' ∈ Subgroup.normalizer (U : Set S) :=
    (sup_le h.hHU Subgroup.le_normalizer : H ⊔ U ≤ _) hb'
  have hu₂ : b' * u * b'⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hb'N u).1 hgu
  have hz := h.conj_conj_mem hh₁ hu₂
  have e : u₁ * h₁ * n * b' * u * (u₁ * h₁ * n * b')⁻¹ =
      u₁ * (h₁ * (n * (b' * u * b'⁻¹) * n⁻¹) * h₁⁻¹) * u₁⁻¹ := by group
  rw [e]
  exact (U ⊔ U.map (MulAut.conj n).toMonoidHom).mul_mem
    ((U ⊔ U.map (MulAut.conj n).toMonoidHom).mul_mem (Subgroup.mem_sup_left hu₁)
      (Subgroup.mem_sup_right hz)) ((U ⊔ U.map (MulAut.conj n).toMonoidHom).inv_mem
        (Subgroup.mem_sup_left hu₁))

theorem TwoCell.ov (h : TwoCell U H n P) (hU : IsSylowTwoOf U ⊤) {X : Subgroup S} (hUX : U ≤ X)
    (hXP : X ≤ P) (hXB : ¬ X ≤ H ⊔ U) : pElementSubgroup 2 P ≤ X :=
  (h.pElement_le hU).trans (sup_le hUX (h.conj_le hUX hXP hXB))

theorem TwoCell.not_conj_le (h : TwoCell U H n P) (hU : IsSylowTwoOf U ⊤)
    (hNB : Subgroup.normalizer (U : Set S) = H ⊔ U) (hnB : n ∉ H ⊔ U) :
    ¬ U.map (MulAut.conj n).toMonoidHom ≤ H ⊔ U := by
  intro hle
  have h1 : U.map (MulAut.conj n).toMonoidHom ≤ U := by
    rintro y hy
    obtain ⟨u, hu, rfl⟩ := hy
    have hyB : (MulAut.conj n).toMonoidHom u ∈ Subgroup.normalizer (U : Set S) :=
      hNB ▸ hle ⟨u, hu, rfl⟩
    refine mem_of_two_element_of_mem_normalizer hU hyB ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hU.2.1 ⟨u, hu⟩
    refine ⟨k, ?_⟩
    rw [orderOf_injective _ (MulAut.conj n).injective u, ← hk, ← Subgroup.orderOf_coe]
  have h2 : U.map (MulAut.conj n).toMonoidHom = U := by
    refine (Subgroup.eq_of_le_of_card_ge h1 ?_)
    exact (Nat.card_congr (U.equivMapOfInjective _ (MulAut.conj n).injective).toEquiv).le
  apply hnB
  rw [← hNB, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h2]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h2] at hx
    obtain ⟨u, hu, hux⟩ := hx
    have : u = x := by
      have h3 : n * u * n⁻¹ = n * x * n⁻¹ := hux
      simpa using h3
    exact this ▸ hu

theorem TwoCell.gen (h : TwoCell U H n P) (hU : IsSylowTwoOf U ⊤)
    (hNB : Subgroup.normalizer (U : Set S) = H ⊔ U) (hnB : n ∉ H ⊔ U) (hnP : n ∈ P)
    (hBP : H ⊔ U ≤ P)
    (hatom : ∀ Q : Subgroup S, H ⊔ U ≤ Q → Q ≤ P → Q = H ⊔ U ∨ Q = P) :
    P ≤ (H ⊔ U) ⊔ pElementSubgroup 2 P := by
  have hUp : U ≤ pElementSubgroup 2 P := le_pElementSubgroup_of_isPGroup h.hUP hU.2.1
  have hU'' : U.map (MulAut.conj n).toMonoidHom ≤ pElementSubgroup 2 P := by
    refine le_pElementSubgroup_of_isPGroup ?_ (hU.2.1.map _)
    rintro _ ⟨u, hu, rfl⟩
    exact P.mul_mem (P.mul_mem hnP (h.hUP hu)) (P.inv_mem hnP)
  rcases hatom ((H ⊔ U) ⊔ pElementSubgroup 2 P) le_sup_left
      (sup_le hBP (pElementSubgroup_le P)) with e | e
  · exfalso
    apply h.not_conj_le hU hNB hnB
    rw [← e]
    exact hU''.trans le_sup_right
  · exact e.ge

theorem hover_of_minimal {B U P₁ P₂ : Subgroup S} (hUB : U ≤ B)
    (lt₁ : B < P₁) (lt₂ : B < P₂)
    (atom₁ : ∀ Q : Subgroup S, B ≤ Q → Q ≤ P₁ → Q = B ∨ Q = P₁)
    (atom₂ : ∀ Q : Subgroup S, B ≤ Q → Q ≤ P₂ → Q = B ∨ Q = P₂)
    (hcover : ∀ X : Subgroup S, U ≤ X → X ≠ ⊤ → X ≤ P₁ ∨ X ≤ P₂)
    (hmin : ∀ Y : Subgroup S, B ≤ Y → Y ≠ B → P₁ ≤ Y ∨ P₂ ≤ Y) :
    ∀ Y : Subgroup S, B ≤ Y → Y = B ∨ Y = P₁ ∨ Y = P₂ ∨ Y = ⊤ := by
  intro Y hBY
  by_cases hYB : Y = B
  · exact Or.inl hYB
  by_cases hYt : Y = ⊤
  · exact Or.inr (Or.inr (Or.inr hYt))
  right
  have hc := hcover Y (hUB.trans hBY) hYt
  rcases hmin Y hBY hYB with h1 | h2
  · rcases hc with hc | hc
    · exact Or.inl (le_antisymm hc h1)
    ·
      rcases atom₂ P₁ lt₁.le (h1.trans hc) with e | e
      · exact absurd e lt₁.ne'
      · exact Or.inr (Or.inl (le_antisymm hc (e ▸ h1)))
  · rcases hc with hc | hc
    · rcases atom₁ P₂ lt₂.le (h2.trans hc) with e | e
      · exact absurd e lt₂.ne'
      · exact Or.inl (le_antisymm hc (e ▸ h2))
    · exact Or.inr (Or.inl (le_antisymm hc h2))


end Abstract

section Assembly

variable {S : Type} [Group S] [Finite S] {U H : Subgroup S} {n₁ n₂ : S} {P₁ P₂ : Subgroup S}

theorem twoPar_of_twoCell (hU : IsSylowTwoOf U ⊤)
    (hNB : Subgroup.normalizer (U : Set S) = H ⊔ U)
    (hc₁ : TwoCell U H n₁ P₁) (hc₂ : TwoCell U H n₂ P₂)
    (hn₁P : n₁ ∈ P₁) (hn₂P : n₂ ∈ P₂) (hn₁B : n₁ ∉ H ⊔ U) (hn₂B : n₂ ∉ H ⊔ U)
    (hBP₁ : H ⊔ U ≤ P₁) (hBP₂ : H ⊔ U ≤ P₂)
    (atom₁ : ∀ Q : Subgroup S, H ⊔ U ≤ Q → Q ≤ P₁ → Q = H ⊔ U ∨ Q = P₁)
    (atom₂ : ∀ Q : Subgroup S, H ⊔ U ≤ Q → Q ≤ P₂ → Q = H ⊔ U ∨ Q = P₂)
    (hne : P₁ ≠ P₂) (top₁ : P₁ ≠ ⊤) (top₂ : P₂ ≠ ⊤)
    (hover : ∀ Y : Subgroup S, H ⊔ U ≤ Y → Y = H ⊔ U ∨ Y = P₁ ∨ Y = P₂ ∨ Y = ⊤)
    (hcover : ∀ X : Subgroup S, U ≤ X → X ≠ ⊤ → X ≤ P₁ ∨ X ≤ P₂)
    (ct₁ : CharTwo P₁) (ct₂ : CharTwo P₂) : TwoPar S U P₁ P₂ := by
  have lt₁ : H ⊔ U < P₁ := lt_of_le_of_ne hBP₁ fun e => hn₁B (e ▸ hn₁P)
  have lt₂ : H ⊔ U < P₂ := lt_of_le_of_ne hBP₂ fun e => hn₂B (e ▸ hn₂P)
  refine ⟨hU, ?_, ?_, ?_, ?_, hne, top₁, top₂, ?_, hcover, ?_, ?_, ?_, ?_, ct₁, ct₂⟩
  · rw [hNB]; exact lt₁
  · rw [hNB]; exact lt₂
  · rw [hNB]; exact atom₁
  · rw [hNB]; exact atom₂
  · rw [hNB]; exact hover
  · intro X hUX hXP hXn
    rw [hNB] at hXn
    exact hc₁.ov hU hUX hXP hXn
  · intro X hUX hXP hXn
    rw [hNB] at hXn
    exact hc₂.ov hU hUX hXP hXn
  · rw [hNB]; exact hc₁.gen hU hNB hn₁B hn₁P hBP₁ atom₁
  · rw [hNB]; exact hc₂.gen hU hNB hn₂B hn₂P hBP₂ atom₂

end Assembly

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
