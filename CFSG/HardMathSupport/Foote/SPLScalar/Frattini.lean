module

public import CFSG.HardMathSupport.Foote.SPLScalar.Basic

public section

namespace CFSG.HardMathSupport.Foote.SPLScalar

open CFSG.Open

variable {K L : Type} [Group K] [Group L]

theorem not_three_dvd_card_ker [Finite K] {W : Subgroup K} (f : ↥W →* L)
    (hker : ∀ w : ↥W, f w = 1 → Nat.Coprime 3 (orderOf w)) : ¬ 3 ∣ Nat.card f.ker := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hx' : orderOf (x : ↥W) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have := hker x (f.mem_ker.mp x.2)
  rw [hx'] at this
  norm_num at this

theorem exists_normalizer_lift [Finite K] {W : Subgroup K}
    (f : ↥W →* L) (hf : Function.Surjective f)
    (hker : ∀ w : ↥W, f w = 1 → Nat.Coprime 3 (orderOf w)) {E : Subgroup K} (hEW : E ≤ W)
    (hE : IsPGroup 3 ↥E) {TL : Subgroup L} (hmap : (E.subgroupOf W).map f = TL) {t : L}
    (ht : t ∈ Subgroup.normalizer (TL : Set L)) :
    ∃ w : ↥W, f w = t ∧ (w : K) ∈ Subgroup.normalizer (E : Set K) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E' : Subgroup ↥W := E.subgroupOf W with hE'
  set M : Subgroup ↥W := TL.comap f with hM
  obtain ⟨w₀, hw₀⟩ := hf t
  have hE'p : IsPGroup 3 ↥E' := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEW).symm
  obtain ⟨φ⟩ := nonempty_mulEquiv_of_map_eq f hker hEW hE hmap
  have : Finite ↥TL := Finite.of_equiv _ φ.toEquiv
  have hcardE' : Nat.card E' = Nat.card TL := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEW).toEquiv, Nat.card_congr φ.toEquiv]
  have hE'M : E' ≤ M := fun x hx => by
    show f x ∈ TL
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hNM : f.ker ≤ M := fun x hx => by
    show f x ∈ TL
    rw [f.mem_ker.mp hx]
    exact TL.one_mem
  have hcardM : Nat.card M = Nat.card TL * Nat.card f.ker := by
    let g : ↥M →* ↥TL := (f.comp M.subtype).codRestrict TL fun x => x.2
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨x, hx⟩ := hf y
      exact ⟨⟨x, show f x ∈ TL by rw [hx]; exact y.2⟩, Subtype.ext hx⟩
    have hgker : g.ker = f.ker.subgroupOf M := by
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, g]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv, hgker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv] at h1
    exact h1
  have hidx : ¬ 3 ∣ (E'.subgroupOf M).index := by
    have h1 := Subgroup.card_mul_index (E'.subgroupOf M)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'M).toEquiv, hcardE', hcardM] at h1
    have hpos : 0 < Nat.card TL := Nat.card_pos
    have h2 : (E'.subgroupOf M).index = Nat.card f.ker := by
      have := Nat.eq_of_mul_eq_mul_left hpos h1
      exact this
    rw [h2]
    exact not_three_dvd_card_ker f hker
  set E'' : Subgroup ↥W := E'.map (MulAut.conj w₀).toMonoidHom with hE''
  have hE''M : E'' ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    show f (w₀ * x * w₀⁻¹) ∈ TL
    rw [map_mul, map_mul, map_inv, hw₀]
    exact (Subgroup.mem_normalizer_iff.mp ht (f x)).mp (hE'M hx)
  have hE''p : IsPGroup 3 ↥E'' := hE'p.map _
  have hidx' : ¬ 3 ∣ (E''.subgroupOf M).index := by
    have hc : Nat.card E'' = Nat.card E' :=
      Nat.card_congr (E'.equivMapOfInjective (MulAut.conj w₀).toMonoidHom
        (MulAut.conj w₀).injective).symm.toEquiv
    have h1 := Subgroup.card_mul_index (E''.subgroupOf M)
    have h2 := Subgroup.card_mul_index (E'.subgroupOf M)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE''M).toEquiv, hc] at h1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'M).toEquiv] at h2
    have hpos : 0 < Nat.card E' := Nat.card_pos
    have h3 : (E''.subgroupOf M).index = (E'.subgroupOf M).index :=
      Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rw [h3]
    exact hidx
  let P₁ : Sylow 3 ↥M := (hE'p.of_equiv (Subgroup.subgroupOfEquivOfLe hE'M).symm).toSylow hidx
  let P₂ : Sylow 3 ↥M := (hE''p.of_equiv (Subgroup.subgroupOfEquivOfLe hE''M).symm).toSylow hidx'
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq ↥M P₂ P₁
  have hfwd : ∀ x ∈ E', (m : ↥W) * w₀ * x * ((m : ↥W) * w₀)⁻¹ ∈ E' := by
    have hm' : ((m • P₂ : Sylow 3 ↥M) : Subgroup ↥M) = (P₁ : Subgroup ↥M) := congrArg _ hm
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at hm'
    intro x hx
    have h1 : (⟨w₀ * x * w₀⁻¹, hE''M ⟨x, hx, rfl⟩⟩ : ↥M) ∈ (P₂ : Subgroup ↥M) :=
      Subgroup.mem_subgroupOf.mpr ⟨x, hx, rfl⟩
    have h2 : MulAut.conj m (⟨w₀ * x * w₀⁻¹, hE''M ⟨x, hx, rfl⟩⟩ : ↥M) ∈
        (P₁ : Subgroup ↥M) := by
      rw [← hm']
      exact ⟨_, h1, rfl⟩
    have h3 := Subgroup.mem_subgroupOf.mp h2
    simpa [mul_assoc] using h3
  have hmTL : f m ∈ TL := m.2
  rw [← hmap] at hmTL
  obtain ⟨e, he, hfe⟩ := hmTL
  set w : ↥W := e⁻¹ * ((m : ↥W) * w₀) with hw
  have hfwd' : ∀ x ∈ E', w * x * w⁻¹ ∈ E' := fun x hx => by
    have h1 := hfwd x hx
    have h2 : w * x * w⁻¹ = e⁻¹ * ((m : ↥W) * w₀ * x * ((m : ↥W) * w₀)⁻¹) * e := by
      rw [hw]
      group
    rw [h2]
    exact E'.mul_mem (E'.mul_mem (E'.inv_mem he) h1) he
  have hmapw : E'.map (MulAut.conj w).toMonoidHom = E' := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hfwd' x hx
    · exact (Nat.card_congr (E'.equivMapOfInjective (MulAut.conj w).toMonoidHom
        (MulAut.conj w).injective).toEquiv).le
  have hwN : ∀ x : ↥W, x ∈ E' ↔ w * x * w⁻¹ ∈ E' := by
    intro x
    constructor
    · exact hfwd' x
    · intro hx
      rw [← hmapw] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := (MulAut.conj w).injective hyx
      exact this ▸ hy
  refine ⟨w, ?_, ?_⟩
  · rw [hw, map_mul, map_mul, map_inv, hfe, hw₀, inv_mul_cancel_left]
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxW : x ∈ W := hEW hx
      have h1 := (hwN ⟨x, hxW⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
      have h2 := Subgroup.mem_subgroupOf.mp h1
      simpa using h2
    · intro hx
      have hgx : (w : K) * x * (w : K)⁻¹ ∈ W := hEW hx
      have hxW : x ∈ W := by
        have := W.mul_mem (W.mul_mem (W.inv_mem w.2) hgx) w.2
        simpa [mul_assoc] using this
      have h1 : w * ⟨x, hxW⟩ * w⁻¹ ∈ E' := Subgroup.mem_subgroupOf.mpr (by simpa using hx)
      exact Subgroup.mem_subgroupOf.mp ((hwN ⟨x, hxW⟩).mpr h1)

end CFSG.HardMathSupport.Foote.SPLScalar
