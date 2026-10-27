module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Planes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open Subgroup

section Centralizer

variable {X : Type*} [Group X] [Finite X]

theorem card_le_three_mul_card_inf_centralizer {P T : Subgroup X} {z : X} (hTP : T ≤ P)
    (hzo : orderOf z = 3) (hzP : ∀ y ∈ P, y * z = z * y)
    (hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ zpowers z) {t : X} (ht : t ∈ T) :
    Nat.card T ≤ 3 * Nat.card (T ⊓ centralizer {t} : Subgroup X) := by
  have hcen : ∀ g ∈ P, ∀ w ∈ zpowers z, g * w = w * g := by
    intro g hg w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    exact ((show Commute g z from hzP g hg).zpow_right k).eq
  let c : T → zpowers z := fun g => ⟨t * g * t⁻¹ * (g : X)⁻¹, hTcomm t ht g g.2⟩
  have hc : ∀ g h : T, c (g * h) = c g * c h := by
    intro g h
    apply Subtype.ext
    have e := hcen (g : X)⁻¹ (P.inv_mem (hTP g.2)) _ (hTcomm t ht h h.2)
    show t * ((g : X) * h) * t⁻¹ * ((g : X) * h)⁻¹ =
      t * g * t⁻¹ * (g : X)⁻¹ * (t * h * t⁻¹ * (h : X)⁻¹)
    calc t * ((g : X) * h) * t⁻¹ * ((g : X) * h)⁻¹
        = t * g * t⁻¹ * ((t * h * t⁻¹ * (h : X)⁻¹) * (g : X)⁻¹) := by group
      _ = t * g * t⁻¹ * ((g : X)⁻¹ * (t * h * t⁻¹ * (h : X)⁻¹)) := by rw [e]
      _ = t * g * t⁻¹ * (g : X)⁻¹ * (t * h * t⁻¹ * (h : X)⁻¹) := by simp only [mul_assoc]
  let φ : T →* zpowers z := MonoidHom.mk' c hc
  have hker : φ.ker.map T.subtype ≤ T ⊓ centralizer {t} := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨g.2, mem_centralizer_iff.2 fun s hs => ?_⟩
    rw [Set.mem_singleton_iff.1 hs]
    have h1 : t * (g : X) * t⁻¹ * (g : X)⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hg)
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have hrange : Nat.card φ.range ≤ 3 := by
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rw [Nat.card_zpowers, hzo] at h
    exact Nat.le_of_dvd (by norm_num) h
  have hkerle : Nat.card φ.ker ≤ Nat.card (T ⊓ centralizer {t} : Subgroup X) := by
    rw [← Subgroup.card_subtype T φ.ker]
    exact Subgroup.card_le_of_le hker
  calc Nat.card T = Nat.card φ.ker * Nat.card φ.range := (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ Nat.card (T ⊓ centralizer {t} : Subgroup X) * 3 := Nat.mul_le_mul hkerle hrange
    _ = 3 * Nat.card (T ⊓ centralizer {t} : Subgroup X) := mul_comm _ _

theorem pow_three_le_card_of_not_commutative {p : ℕ} (hp : p.Prime) {T : Subgroup X}
    (hT : IsPGroup p T) (hnc : ¬ ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) : p ^ 3 ≤ Nat.card T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  by_contra hlt
  have hn3 : n < 3 := by
    by_contra h
    exact hlt (hn ▸ Nat.pow_le_pow_right hp.pos (not_lt.1 h))
  refine hnc fun x hx y hy => ?_
  have hcomm : IsMulCommutative T := by
    interval_cases n
    · have : Subsingleton T := (Nat.card_eq_one_iff_unique.1 (by simpa using hn)).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    · have : IsCyclic T := isCyclic_of_prime_card (by simpa using hn)
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hn
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : T) ⟨y, hy⟩)

end Centralizer

section CentralProduct

set_option linter.unusedVariables false in
theorem false_of_plane_in_central_product {X : Type*} [Group X] [Finite X]
    {P T R D : Subgroup X} {z : X}
    (hP : IsPGroup 3 P) (hTP : T ≤ P) (hRP : R ≤ P)
    (hdec : ∀ u ∈ P, ∃ t ∈ T, ∃ r ∈ R, u = t * r)
    (hTR : ∀ t ∈ T, ∀ r ∈ R, t * r = r * t)
    (hzo : orderOf z = 3) (hzT : z ∈ T) (hzR : z ∈ R) (hzP : ∀ y ∈ P, y * z = z * y)
    (hTR_le : ∀ x ∈ T, x ∈ R → x ∈ Subgroup.zpowers z)
    (hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z)
    (hTnc : ¬ ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hDP : D ≤ P) (hDe : CFSG.Open.IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2) (hzD : z ∈ D)
    (hDself : ∀ x ∈ P, x ∈ Subgroup.centralizer (D : Set X) → x ∈ D)
    (hrank : CFSG.Open.pRank 3 P = 3) : False := by
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hD9 : Nat.card D = 9 := by rw [hDc]; norm_num
  have hz1 : ∀ y ∈ P, Commute z y := fun y hy => (hzP y hy).symm
  obtain ⟨x, hxD, hxz⟩ := exists_mem_notMem_zpowers hp3 hzo hDc
  obtain ⟨t, htT, r, hrR, hxtr⟩ := hdec x (hDP hxD)
  have hCx : ∀ y ∈ P, y * x = x * y → y ∈ D := by
    intro y hy hyx
    refine hDself y hy ?_
    rw [mem_centralizer_iff]
    intro d hd
    obtain ⟨a, b, rfl⟩ := exists_zpow_mul_zpow_of_card_eq_sq hp3 hDe hDc hzo hzD hxD hxz hd
    have h1 : Commute (z ^ a) y := (hz1 y hy).zpow_left a
    have h2 : Commute (x ^ b) y := (show Commute x y from hyx.symm).zpow_left b
    exact (h1.mul_left h2).eq
  have hCD : (T ⊓ centralizer {t} : Subgroup X) ≤ D := by
    intro a ha
    have haT : a ∈ T := ha.1
    have hat : t * a = a * t := mem_centralizer_iff.1 ha.2 t rfl
    refine hCx a (hTP haT) ?_
    rw [hxtr]
    calc a * (t * r) = (a * t) * r := (mul_assoc _ _ _).symm
      _ = (t * a) * r := by rw [hat]
      _ = t * (a * r) := mul_assoc _ _ _
      _ = t * (r * a) := by rw [hTR a haT r hrR]
      _ = (t * r) * a := (mul_assoc _ _ _).symm
  have hT27 : 27 ≤ Nat.card T := by
    have h := pow_three_le_card_of_not_commutative hp3 (hP.to_le hTP) hTnc
    norm_num at h
    exact h
  have hidx := card_le_three_mul_card_inf_centralizer hTP hzo hzP hTcomm htT
  have hCle : Nat.card (T ⊓ centralizer {t} : Subgroup X) ≤ 9 := hD9 ▸ Subgroup.card_le_of_le hCD
  have hCeq : T ⊓ centralizer {t} = D :=
    Subgroup.eq_of_le_of_card_ge hCD (by rw [hD9]; omega)
  have hDT : D ≤ T := hCeq ▸ inf_le_left
  have hRD : R ≤ D := by
    intro r' hr'
    refine hDself r' (hRP hr') ?_
    rw [mem_centralizer_iff]
    intro d hd
    exact hTR d (hDT hd) r' hr'
  have hPT : P ≤ T := by
    intro u hu
    obtain ⟨t', ht', r', hr', rfl⟩ := hdec u hu
    exact mul_mem ht' (hDT (hRD hr'))
  obtain ⟨E, hEP, hEe, hEc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 hp3 P
  rw [hrank] at hEc
  have hET : E = T := Subgroup.eq_of_le_of_card_ge (hEP.trans hPT) (by rw [hEc]; omega)
  refine hTnc fun a ha b hb => ?_
  rw [← hET] at ha hb
  exact hEe.comm ha hb

end CentralProduct

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
