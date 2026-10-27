module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLT0
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open scoped MatrixGroups

namespace LTTwin

theorem eq_of_involutions_of_equiv_sl2 {G : Type} [Group G] {R : Subgroup G}
    (e : R ≃* SL(2, GaloisField 3 1)) {r r' : G} (hr : r ∈ R) (hr' : r' ∈ R)
    (h2 : r * r = 1) (h2' : r' * r' = 1) (h1 : r ≠ 1) (h1' : r' ≠ 1) : r = r' := by
  have h2F : (2 : GaloisField 3 1) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have key : ∀ {s : G} (hs : s ∈ R), s * s = 1 → s ≠ 1 →
      ((e ⟨s, hs⟩ : SL(2, GaloisField 3 1)) : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) =
        Matrix.scalar (Fin 2) (-1 : GaloisField 3 1) := by
    intro s hs hs2 hs1
    have hy2 : (e ⟨s, hs⟩) ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨s, hs⟩ : R) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hs2)
      rw [this, map_one]
    have hcen := sl2_center_of_sq_eq_one h2F hy2
    obtain ⟨a, ha, hay⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
    rw [Fintype.card_fin, pow_two] at ha
    rcases mul_self_eq_one_iff.mp ha with rfl | rfl
    · exfalso
      apply hs1
      have : e ⟨s, hs⟩ = 1 := by
        apply Subtype.ext
        rw [← hay]
        simp
      have h' := e.injective (this.trans (map_one e).symm)
      exact congrArg Subtype.val h'
    · exact hay.symm
  have h := (key hr h2 h1).trans (key hr' h2' h1').symm
  have h' : e ⟨r, hr⟩ = e ⟨r', hr'⟩ := Subtype.ext h
  exact congrArg Subtype.val (e.injective h')

theorem involution_of_family {K X : Type} [Group K] [Group X] (ψ : K →* X)
    (hker : ψ.ker = Subgroup.center K) (𝓕 : Set (Subgroup K))
    (hsl2 : ∀ R ∈ 𝓕, Nonempty (R ≃* SL(2, GaloisField 3 1)))
    (hnc : ∀ R ∈ 𝓕, ∀ r ∈ R, (∀ y : K, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center K) → r = 1)
    {R₀ : Subgroup K} (hcls : ∀ R ∈ 𝓕, ∃ y : K, R = R₀.map (MulAut.conj y).toMonoidHom)
    {z₀ : K} (hz₀R : z₀ ∈ R₀) (hz₀2 : z₀ * z₀ = 1) (hz₀1 : z₀ ≠ 1) :
    ∀ R ∈ 𝓕, ∀ t : X, t ∈ R.map ψ → orderOf t = 2 →
      ∃ y : K, R = R₀.map (MulAut.conj y).toMonoidHom ∧ t = ψ (y * z₀ * y⁻¹) := by
  intro R hR t ht ht2
  obtain ⟨y, hy⟩ := hcls R hR
  obtain ⟨e⟩ := hsl2 R hR
  have hconj : ∀ x : K, (MulAut.conj y).toMonoidHom x = y * x * y⁻¹ := fun x => rfl
  have hmemR : ∀ x ∈ R₀, y * x * y⁻¹ ∈ R := fun x hx => by
    rw [hy]
    exact ⟨x, hx, hconj x⟩
  have hzR : y * z₀ * y⁻¹ ∈ R := hmemR z₀ hz₀R
  have hzz : (y * z₀ * y⁻¹) * (y * z₀ * y⁻¹) = 1 := by
    calc (y * z₀ * y⁻¹) * (y * z₀ * y⁻¹) = y * (z₀ * z₀) * y⁻¹ := by group
      _ = 1 := by rw [hz₀2]; group
  have hz1 : y * z₀ * y⁻¹ ≠ 1 := fun h => hz₀1 (by
    have : z₀ = y⁻¹ * (y * z₀ * y⁻¹) * y := by group
    rw [this, h]
    group)
  obtain ⟨r, hrR, rfl⟩ := Subgroup.mem_map.mp ht
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hψr2, hψr1⟩ := orderOf_eq_prime_iff.mp ht2
  have hrr : r * r = 1 := by
    refine hnc R hR (r * r) (R.mul_mem hrR hrR) fun y' => ?_
    have hc : r * r ∈ Subgroup.center K := by
      rw [← hker, MonoidHom.mem_ker, map_mul]
      simpa [pow_two] using hψr2
    have : r * r * y' * (r * r)⁻¹ * y'⁻¹ = 1 := by
      rw [(Subgroup.mem_center_iff.mp hc y').symm]
      group
    rw [this]
    exact one_mem _
  have hr1 : r ≠ 1 := fun h => hψr1 (by rw [h, map_one])
  exact ⟨y, hy, by rw [eq_of_involutions_of_equiv_sl2 e hrR hzR hrr hzz hr1 hz1]⟩

theorem twin_of_family {K X : Type} [Group K] [Group X] (ψ : K →* X)
    (hker : ψ.ker = Subgroup.center K) (𝓕 : Set (Subgroup K))
    (hsl2 : ∀ R ∈ 𝓕, Nonempty (R ≃* SL(2, GaloisField 3 1)))
    (hnc : ∀ R ∈ 𝓕, ∀ r ∈ R, (∀ y : K, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center K) → r = 1)
    {R₀ : Subgroup K} (hcls : ∀ R ∈ 𝓕, ∃ y : K, R = R₀.map (MulAut.conj y).toMonoidHom)
    {z₀ w₀ : K} (hz₀R : z₀ ∈ R₀) (hz₀2 : z₀ * z₀ = 1) (hz₀1 : z₀ ≠ 1)
    (hzw : w₀ * z₀ * w₀⁻¹ * z₀⁻¹ ∈ Subgroup.center K)
    (hcomm : ∀ a ∈ R₀, ∀ b ∈ R₀, Commute (w₀ * a * w₀⁻¹) b) :
    ∀ R ∈ 𝓕, ∀ t : X, t ∈ R.map ψ → orderOf t = 2 →
      ∃ w ∈ Subgroup.centralizer ({t} : Set X), ∀ a ∈ R.map ψ, ∀ b ∈ R.map ψ,
        a * (w * b * w⁻¹) = (w * b * w⁻¹) * a := by
  intro R hR t ht ht2
  obtain ⟨y, hy, rfl⟩ := involution_of_family ψ hker 𝓕 hsl2 hnc hcls hz₀R hz₀2 hz₀1 R hR t ht ht2
  have hconj : ∀ x : K, (MulAut.conj y).toMonoidHom x = y * x * y⁻¹ := fun x => rfl
  have h1 : ψ (w₀ * z₀ * w₀⁻¹ * z₀⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact hzw
  have h2 : ψ w₀ * ψ z₀ = ψ z₀ * ψ w₀ := by
    simp only [map_mul, map_inv] at h1
    calc ψ w₀ * ψ z₀ = (ψ w₀ * ψ z₀ * (ψ w₀)⁻¹ * (ψ z₀)⁻¹) * (ψ z₀ * ψ w₀) := by group
      _ = ψ z₀ * ψ w₀ := by rw [h1, one_mul]
  refine twin_of_lift ψ (R := R) (w := y * w₀ * y⁻¹) ?_ ?_
  · rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [map_mul, map_inv]
    calc ψ y * ψ w₀ * (ψ y)⁻¹ * (ψ y * ψ z₀ * (ψ y)⁻¹)
        = ψ y * (ψ w₀ * ψ z₀) * (ψ y)⁻¹ := by group
      _ = ψ y * (ψ z₀ * ψ w₀) * (ψ y)⁻¹ := by rw [h2]
      _ = ψ y * ψ z₀ * (ψ y)⁻¹ * (ψ y * ψ w₀ * (ψ y)⁻¹) := by group
  · intro a ha b hb
    rw [hy] at ha hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    have hc := (hcomm a₀ ha₀ b₀ hb₀).map ψ
    have e1 : y * w₀ * y⁻¹ * (y * a₀ * y⁻¹) * (y * w₀ * y⁻¹)⁻¹ = y * (w₀ * a₀ * w₀⁻¹) * y⁻¹ := by
      group
    rw [hconj, hconj, e1]
    simp only [map_mul, map_inv]
    have h3 : Commute (ψ y * ψ (w₀ * a₀ * w₀⁻¹) * (ψ y)⁻¹) (ψ y * ψ b₀ * (ψ y)⁻¹) := by
      have := hc.map (MulAut.conj (ψ y))
      simpa [MulAut.conj_apply] using this
    simpa using h3

end LTTwin

end CFSG.CGT.PushingUpLit.SolKNA
