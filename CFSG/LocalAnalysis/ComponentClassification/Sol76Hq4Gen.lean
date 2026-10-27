module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Walter.W67.Section5.MaxClass

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open CFSG Subgroup

variable {Q : Type} [Group Q] [Finite Q]

@[expose] def omegaCenter (Q : Type) [Group Q] : Subgroup Q where
  carrier := {z | z ∈ center Q ∧ z * z = 1}
  one_mem' := ⟨one_mem _, mul_one 1⟩
  mul_mem' := by
    rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨mul_mem ha hb, ?_⟩
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [(mem_center_iff.mp ha b).symm]
      _ = a * a * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  inv_mem' := by
    rintro a ⟨ha, ha2⟩
    refine ⟨inv_mem ha, ?_⟩
    rw [← mul_inv_rev, ha2, inv_one]

theorem factorization_add_le {x : Q} (hx : x * x = 1) :
    (Nat.card ↥(centralizer ({(x : Q ⧸ center Q)} : Set (Q ⧸ center Q)))).factorization 2 +
        (Nat.card ↥(center Q)).factorization 2 ≤
      (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2 +
        (Nat.card ↥(omegaCenter Q)).factorization 2 := by
  classical
  set H := centralizer ({(x : Q ⧸ center Q)} : Set (Q ⧸ center Q)) with hH
  obtain ⟨D, hD⟩ : ∃ D : Subgroup Q, D = H.comap (QuotientGroup.mk' (center Q)) := ⟨_, rfl⟩
  have hmemD : ∀ g : Q, g ∈ D ↔ (g : Q ⧸ center Q) * x = x * (g : Q ⧸ center Q) := by
    intro g
    rw [hD, mem_comap, hH, mem_centralizer_singleton_iff]
    rfl
  have hDc : ∀ g ∈ D, g * x * g⁻¹ * x⁻¹ ∈ center Q := fun g hg =>
    Walter.W67.MaxClass.commutator_mem_center ((hmemD g).mp hg)
  set φ := Walter.W67.MaxClass.commHom x D hDc with hφ
  have h1 := card_ker_mul_card_range φ
  have hcard : Nat.card D = Nat.card H * Nat.card (center Q) :=
    hD ▸ Walter.W67.MaxClass.card_comap_mk H
  have hker : Nat.card φ.ker = Nat.card ↥(centralizer ({x} : Set Q)) := by
    have hmap : φ.ker.map D.subtype = centralizer ({x} : Set Q) := by
      ext y
      constructor
      · rintro ⟨g, hg, rfl⟩
        have hg' : (g : Q) * x * (g : Q)⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hg
        rw [mem_centralizer_singleton_iff]
        calc (g : Q) * x = (g : Q) * x * (g : Q)⁻¹ * x⁻¹ * (x * g) := by group
          _ = x * g := by rw [hg', one_mul]
      · intro hy
        have hyx := mem_centralizer_singleton_iff.mp hy
        have hyD : y ∈ D := by
          rw [hmemD]
          change ((y * x : Q) : Q ⧸ center Q) = ((x * y : Q) : Q ⧸ center Q)
          rw [hyx]
        refine ⟨⟨y, hyD⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, MonoidHom.mem_ker]
        apply Subtype.ext
        change y * x * y⁻¹ * x⁻¹ = 1
        rw [hyx]
        group
    rw [← hmap, card_map_of_injective D.subtype_injective]
  have hsq : ∀ c ∈ φ.range, ((c : center Q) : Q) * c = 1 := by
    rintro c ⟨g, rfl⟩
    have hc : (g : Q) * x * (g : Q)⁻¹ * x⁻¹ ∈ center Q := hDc g g.2
    change ((g : Q) * x * (g : Q)⁻¹ * x⁻¹) * ((g : Q) * x * (g : Q)⁻¹ * x⁻¹) = 1
    set c' := (g : Q) * x * (g : Q)⁻¹ * x⁻¹ with hc'
    have e : (g : Q) * x * (g : Q)⁻¹ = c' * x := by rw [hc']; group
    have e2 : ((g : Q) * x * (g : Q)⁻¹) * ((g : Q) * x * (g : Q)⁻¹) = 1 := by
      calc ((g : Q) * x * (g : Q)⁻¹) * ((g : Q) * x * (g : Q)⁻¹) = (g : Q) * (x * x) * (g : Q)⁻¹ :=
            by group
        _ = 1 := by rw [hx]; group
    rw [e] at e2
    have hcx : x * c' = c' * x := mem_center_iff.mp hc x
    have e3 : (c' * x) * (c' * x) = c' * c' * (x * x) := by
      calc (c' * x) * (c' * x) = c' * (x * c') * x := by group
        _ = c' * (c' * x) * x := by rw [hcx]
        _ = c' * c' * (x * x) := by group
    rw [hx, mul_one] at e3
    rw [← e3]
    exact e2
  have hrange : Nat.card φ.range ∣ Nat.card ↥(omegaCenter Q) := by
    have hle : φ.range.map (center Q).subtype ≤ omegaCenter Q := by
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨(c : center Q).2, hsq c hc⟩
    rw [← card_map_of_injective (center Q).subtype_injective]
    exact card_dvd_of_le hle
  have hD' : Nat.card H * Nat.card ↥(center Q) =
      Nat.card ↥(centralizer ({x} : Set Q)) * Nat.card φ.range := by
    rw [← hcard, ← h1, hker]
  have hv := congrArg (fun n => n.factorization 2) hD'
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hv
  simp only [Finsupp.add_apply] at hv
  have hr : (Nat.card φ.range).factorization 2 ≤ (Nat.card ↥(omegaCenter Q)).factorization 2 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hrange 2
  omega

theorem two_add_le_of_sixteen (h4 : Nat.card ↥(omegaCenter Q) = 4) {x : Q} (hx : x * x = 1)
    (h16 : 4 ≤
      (Nat.card ↥(centralizer ({(x : Q ⧸ center Q)} : Set (Q ⧸ center Q)))).factorization 2) :
    (Nat.card ↥(center Q)).factorization 2 + 2 ≤
      (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2 := by
  have h := factorization_add_le hx
  have h2 : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  rw [h4, h2] at h
  omega

end CFSG.ComponentClassification.Sol76T13.Hq4
