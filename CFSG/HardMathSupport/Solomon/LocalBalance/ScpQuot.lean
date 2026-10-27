module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type*} [Group G]

theorem eq_barX_of_isSCp [Finite G] {p : ℕ} (hp : p.Prime) {B C : Subgroup G} (hBC : B ≤ C)
    (hB : IsSCp p ⊤ B) {E : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)} (hE : IsElemAbelian p E)
    (hle : barX p C B ≤ E) : E = barX p C B := by
  have : Fact p.Prime := ⟨hp⟩
  set P := GLAPPrimeCore p ↥C with hPdef
  set π : ↥C →* ↥C ⧸ P := QuotientGroup.mk' P with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective P
  have hcop : Nat.Coprime p (Nat.card P) := coprime_card_gLAPPrimeCore_aux p ↥C
  have hPnd : ¬ p ∣ Nat.card P := (Nat.Prime.coprime_iff_not_dvd hp).1 hcop
  set H : Subgroup ↥C := E.comap π with hH
  set B' : Subgroup ↥C := B.subgroupOf C with hB'
  have hB'H : B' ≤ H := by
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  have hB'p : IsPGroup p (B'.subgroupOf H) := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    have h2 : ((g : H) : ↥C) ∈ B.subgroupOf C := g.2
    rw [Subgroup.mem_subgroupOf] at h2
    have h3 := hB.2.1.2 _ h2
    exact Subtype.ext (Subtype.ext (Subtype.ext (by simpa using h3)))
  have hEp : IsPGroup p E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hB'p
  set T : Subgroup ↥C := (S : Subgroup H).map H.subtype with hT
  have hTH : T ≤ H := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hB'T : B' ≤ T := by
    intro x hx
    exact ⟨⟨x, hB'H hx⟩, hS hx, rfl⟩
  set φ : H →* ↥C ⧸ P := π.comp H.subtype with hφ
  have hφrange : φ.range = E := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    exact Subgroup.map_comap_eq_self_of_surjective hπsurj E
  have hkerdvd : Nat.card φ.ker ∣ Nat.card P := by
    have hle' : φ.ker.map H.subtype ≤ P := by
      rintro _ ⟨y, hy, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 hy
    rw [← Subgroup.card_map_of_injective (f := H.subtype) H.subtype_injective]
    exact Subgroup.card_dvd_of_le hle'
  have hkernd : ¬ p ∣ Nat.card φ.ker := fun h => hPnd (h.trans hkerdvd)
  have hcardH : Nat.card H = Nat.card E * Nat.card φ.ker := by
    rw [mul_comm, ← hφrange, Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    rw [mul_comm]
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hfac : (Nat.card H).factorization p = k := by
    rw [hcardH, hk]
    have h1 : Nat.card φ.ker ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) h1, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hkernd, add_zero]
  have hcardT : Nat.card T = p ^ k := by
    rw [hT, Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity, hfac]
  have hinj : ∀ x ∈ T, ∀ y ∈ T, π x = π y → x = y := by
    intro x hx y hy hxy
    have hz : x⁻¹ * y ∈ T ⊓ P := by
      refine ⟨T.mul_mem (T.inv_mem hx) hy, ?_⟩
      have : π (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 this
    have hd1 : Nat.card (T ⊓ P : Subgroup ↥C) ∣ p ^ k :=
      hcardT ▸ Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card (T ⊓ P : Subgroup ↥C) ∣ Nat.card P := Subgroup.card_dvd_of_le inf_le_right
    have hcop' : Nat.Coprime (p ^ k) (Nat.card P) := Nat.Coprime.pow_left k hcop
    have h1 : Nat.card (T ⊓ P : Subgroup ↥C) = 1 :=
      Nat.dvd_one.1 (hcop'.gcd_eq_one ▸ Nat.dvd_gcd hd1 hd2)
    have h2 : (T ⊓ P : Subgroup ↥C) = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    rw [h2] at hz
    have : x⁻¹ * y = 1 := hz
    exact (inv_mul_eq_one.1 this)
  have hmapT : T.map π = E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hTH hx
    · have hψ : Function.Injective (π.comp T.subtype) := fun x y hxy =>
        Subtype.ext (hinj x x.2 y y.2 hxy)
      have h1 : Nat.card T = Nat.card (π.comp T.subtype).range :=
        Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv
      have h2 : (π.comp T.subtype).range = T.map π := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [h2] at h1
      rw [hk, ← hcardT, h1]
  have hTel : IsElemAbelian p T := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj _ (T.mul_mem x.2 y.2) _ (T.mul_mem y.2 x.2)
      have hx' : π x ∈ E := by rw [← hmapT]; exact ⟨x, x.2, rfl⟩
      have hy' : π y ∈ E := by rw [← hmapT]; exact ⟨y, y.2, rfl⟩
      have := hE.1.is_comm.comm (⟨π x, hx'⟩ : E) ⟨π y, hy'⟩
      have h := congrArg Subtype.val this
      simpa using h
    · apply hinj _ (T.pow_mem hx p) _ T.one_mem
      have hx' : π x ∈ E := by rw [← hmapT]; exact ⟨x, hx, rfl⟩
      rw [map_pow, map_one]
      exact hE.2 _ hx'
  set T' : Subgroup G := T.map C.subtype with hT'
  have hT'el : IsElemAbelian p T' := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨x0, hx0, hxe⟩ := x.2
      obtain ⟨y0, hy0, hye⟩ := y.2
      have h := congrArg (fun z : T => (z : ↥C)) (hTel.1.is_comm.comm ⟨x0, hx0⟩ ⟨y0, hy0⟩)
      apply Subtype.ext
      have h' : x0 * y0 = y0 * x0 := h
      show (x : G) * y = y * x
      rw [← hxe, ← hye]
      show ((x0 * y0 : ↥C) : G) = ((y0 * x0 : ↥C) : G)
      rw [h']
    · rintro _ ⟨x0, hx0, rfl⟩
      have := hTel.2 x0 hx0
      show ((x0 : ↥C) : G) ^ p = 1
      rw [← Subgroup.coe_pow, this]
      rfl
  have hBT' : B ≤ T' := by
    intro b hb
    exact ⟨⟨b, hBC hb⟩, hB'T hb, rfl⟩
  have hT'B : T' = B := hB.2.2 T' le_top hT'el hBT'
  have hTB' : T ≤ B' := by
    intro x hx
    have : (x : G) ∈ T' := ⟨x, hx, rfl⟩
    rw [hT'B] at this
    exact this
  have h5 : E ≤ B'.map π := hmapT ▸ Subgroup.map_mono hTB'
  exact le_antisymm h5 hle

end CFSG.HardMathSupport.Solomon.LocalBalance
