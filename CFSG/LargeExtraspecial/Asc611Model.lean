module

public import CFSG.LargeExtraspecial.Asc611Defs
public import CFSG.LargeExtraspecial.Asc611Out

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary

namespace S14

@[expose] def UnitaryInnerCentStmt : Prop :=
  ∀ m : ℕ, 6 ≤ m → ∀ e : SUid frob m, e * e = 1 → (QuotientGroup.mk e : PG m) ≠ 1 →
    (QuotientGroup.mk e : PG m) ∉ DG m →
    ∀ U : Subgroup (PG m), IsPGroup 2 U → (QuotientGroup.mk e : PG m) ∈ U →
      U ≤ centralizer ({(QuotientGroup.mk e : PG m)} : Set (PG m)) →
      (∀ c ∈ centralizer ({(QuotientGroup.mk e : PG m)} : Set (PG m)), ∀ u ∈ U,
        c * u * c⁻¹ ∈ U) →
      (∀ u ∈ U, u ∉ DG m) → Nat.card U ≤ 2

@[expose] def UnitaryOuterCentStmt : Prop :=
  ∀ m : ℕ, ∀ hm : 6 ≤ m, ∀ β : MulAut (PG m), β * β = 1 →
    Asc611.fieldFactor (m := m) (by omega) β ≠ 1 →
    ∀ U : Subgroup (PG m), IsPGroup 2 U → (∀ u ∈ U, β u = u) →
      (∀ c : PG m, β c = c → ∀ u ∈ U, c * u * c⁻¹ ∈ U) → (∀ u ∈ U, u ∉ DG m) → U = ⊥

theorem card_map_comap_eq {H : Type} [Group H] {L : Subgroup H} {m : ℕ} (ψ : L ≃* PG m)
    (U : Subgroup H) :
    Nat.card ↥((U.comap L.subtype).map ψ.toMonoidHom) = Nat.card ↥(U ⊓ L) := by
  rw [Subgroup.card_map_of_injective ψ.injective,
    ← Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective,
    Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]

theorem mem_map_comap_iff {H : Type} [Group H] {L : Subgroup H} {m : ℕ} (ψ : L ≃* PG m)
    (U : Subgroup H) {u : PG m} :
    u ∈ (U.comap L.subtype).map ψ.toMonoidHom ↔ ((ψ.symm u : L) : H) ∈ U := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    simpa [Subgroup.mem_subgroupOf] using hl
  · intro h
    exact ⟨ψ.symm u, h, by simp⟩

theorem aschbacherUnitaryCentStmt_of (hI : UnitaryInnerCentStmt) (hO : UnitaryOuterCentStmt) :
    AschbacherUnitaryCentStmt := by
  intro H _ _ L hLn m hm ψ hC a ha2 ha1 haL U hU2 haU hUC hUN hUL
  have := hLn
  set V := (U.comap L.subtype).map ψ.toMonoidHom with hV
  have hVp : IsPGroup 2 V :=
    (hU2.comap_of_injective L.subtype L.subtype_injective).map ψ.toMonoidHom
  have hVDG : ∀ u ∈ V, u ∉ DG m := fun u hu => by
    have h1 := hUL (ψ.symm u) ((mem_map_comap_iff ψ U).mp hu)
    rwa [MulEquiv.apply_symm_apply] at h1
  have hcard : Nat.card U ≤ 2 * Nat.card V := by
    rw [hV, card_map_comap_eq ψ U]
    exact Asc611.card_le_two_mul_card_inf L (m := m) (by omega) ψ hC hU2
  by_cases haL' : a ∈ L
  · set al : L := ⟨a, haL'⟩ with hal
    set ℓ := ψ al with hℓ
    obtain ⟨e₀, he₀⟩ := QuotientGroup.mk_surjective ℓ
    have hℓℓ : ℓ * ℓ = 1 := by
      rw [hℓ, ← map_mul]
      have : al * al = 1 := Subtype.ext (by simpa [hal] using ha2)
      rw [this, map_one]
    have hcen : e₀ * e₀ ∈ center (SUid frob m) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, he₀, hℓℓ]
    set e₁ := e₀ * e₀ * e₀ with he₁
    have he₁e₁ : e₁ * e₁ = 1 := by
      have h := AS35U.pow_three_eq_one_of_mem_center (m := m) (by omega) hcen
      rw [show e₁ * e₁ = (e₀ * e₀) ^ 3 by
        rw [he₁]; simp only [pow_succ, pow_zero, one_mul, mul_assoc], h]
    have hmk : (QuotientGroup.mk e₁ : PG m) = ℓ := by
      rw [he₁, QuotientGroup.mk_mul, QuotientGroup.mk_mul, he₀, hℓℓ, one_mul]
    have hℓ1 : ℓ ≠ 1 := fun h => ha1 (by
      have : al = 1 := ψ.injective (by rw [← hℓ, h, map_one])
      simpa [hal] using congrArg Subtype.val this)
    have hcomm : ∀ l : L, (l : H) * a = a * (l : H) → ψ l * ℓ = ℓ * ψ l := fun l hl => by
      rw [hℓ, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simpa [hal] using hl)
    have hle : V ≤ centralizer ({ℓ} : Set (PG m)) := fun u hu => by
      rw [mem_centralizer_singleton_iff]
      have h1 := mem_centralizer_singleton_iff.mp (hUC ((mem_map_comap_iff ψ U).mp hu))
      have h2 := hcomm (ψ.symm u) h1
      rw [MulEquiv.apply_symm_apply] at h2
      exact h2
    have hnorm : ∀ c ∈ centralizer ({ℓ} : Set (PG m)), ∀ u ∈ V, c * u * c⁻¹ ∈ V := by
      intro c hc u hu
      rw [mem_centralizer_singleton_iff] at hc
      set lc := ψ.symm c with hlc
      have hca : (lc : H) * a = a * (lc : H) := by
        have h1 : lc * al = al * lc := ψ.injective (by
          rw [map_mul, map_mul, hlc, MulEquiv.apply_symm_apply, ← hℓ]
          exact hc)
        simpa [hal] using congrArg Subtype.val h1
      have h2 := hUN lc (mem_centralizer_singleton_iff.mpr hca) _
        ((mem_map_comap_iff ψ U).mp hu)
      rw [mem_map_comap_iff]
      simpa [hlc] using h2
    have hI' := hI m hm e₁ he₁e₁ (by rw [hmk]; exact hℓ1) (by rw [hmk]; exact haL al rfl) V hVp
      (by rw [hmk]; exact ⟨al, haU, rfl⟩) (by rw [hmk]; exact hle) (by rw [hmk]; exact hnorm)
      hVDG
    omega
  · set β := Asc611.actPG L ψ a with hβ
    have hββ : β * β = 1 := by rw [hβ, ← map_mul, ha2, map_one]
    have hβ1 : Asc611.fieldFactor (m := m) (by omega) β ≠ 1 := fun h =>
      haL' (Asc611.mem_of_fieldFactor_eq_one L (by omega) ψ hC h (k := 1) (by
        rw [pow_one, sq]; exact ha2))
    have hβapp : ∀ l : L, β (ψ l) = ψ (MulAut.conjNormal a l) := fun l => by
      rw [hβ, Asc611.actPG]
      simp [MulAut.congr_apply]
    have hfix : ∀ u ∈ V, β u = u := by
      intro u hu
      have h1 := mem_centralizer_singleton_iff.mp (hUC ((mem_map_comap_iff ψ U).mp hu))
      rw [← MulEquiv.apply_symm_apply ψ u, hβapp]
      congr 1
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, ← h1]
      group
    have hnorm : ∀ c : PG m, β c = c → ∀ u ∈ V, c * u * c⁻¹ ∈ V := by
      intro c hc u hu
      set lc := ψ.symm c with hlc
      have h1 : MulAut.conjNormal a lc = lc := ψ.injective (by
        rw [← hβapp, hlc, MulEquiv.apply_symm_apply]
        exact hc)
      have hca : (lc : H) * a = a * (lc : H) := by
        have h2 := congrArg Subtype.val h1
        rw [MulAut.conjNormal_apply] at h2
        calc (lc : H) * a = a * (lc : H) * a⁻¹ * a := by rw [h2]
          _ = a * (lc : H) := by group
      have h2 := hUN lc (mem_centralizer_singleton_iff.mpr hca) _
        ((mem_map_comap_iff ψ U).mp hu)
      rw [mem_map_comap_iff]
      simpa [hlc] using h2
    have hO' := hO m hm β hββ hβ1 V hVp hfix hnorm hVDG
    have hV1 : Nat.card V = 1 := by rw [hO']; exact Subgroup.card_bot
    omega

end S14

end CFSG.LargeExtraspecial
