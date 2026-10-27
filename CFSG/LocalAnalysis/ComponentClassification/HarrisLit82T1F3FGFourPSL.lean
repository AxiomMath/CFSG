module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCData
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieInputs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups commutatorElement

theorem mul_self_eq_neg_one_of_conj_eq_neg {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {g h : SL(2, F)} (hgh : h * g * h⁻¹ = -g) : h * h = -1 := by
  have h1 : g⁻¹ * h * g = -h := by
    have hhg : h * g = -g * h := by
      calc h * g = h * g * h⁻¹ * h := by group
        _ = -g * h := by rw [hgh]
    calc g⁻¹ * h * g = g⁻¹ * (h * g) := by group
      _ = g⁻¹ * (-g * h) := by rw [hhg]
      _ = -h := by rw [neg_mul, mul_neg, ← mul_assoc, inv_mul_cancel, one_mul]
  set H : Matrix (Fin 2) (Fin 2) F := (h : Matrix (Fin 2) (Fin 2) F) with hH
  have htr : H 0 0 + H 1 1 = 0 := by
    have h3 := congrArg (fun x : SL(2, F) => Matrix.trace (x : Matrix (Fin 2) (Fin 2) F)) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.trace_neg] at h3
    rw [Matrix.trace_mul_comm, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, one_mul, Matrix.trace_fin_two] at h3
    have h4 : 2 * (H 0 0 + H 1 1) = 0 := by linear_combination h3
    exact (mul_eq_zero.mp h4).resolve_left h2
  have hdet : H 0 0 * H 1 1 - H 0 1 * H 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact h.2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, ← hH]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination H 0 0 * htr - hdet
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination H 0 1 * htr
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination H 1 0 * htr
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination H 1 1 * htr - hdet

theorem commutatorElement_mul_eq_of_conj {M : Type*} [Group M] {g a b ε δ : M}
    (hε : ε ∈ center M) (hδ : δ ∈ center M) (ha : a * g * a⁻¹ = ε * g)
    (hb : b * g * b⁻¹ = δ * g) : ⁅a, b⁆ * g = g * ⁅a, b⁆ := by
  have hpull : ∀ z ∈ center M, ∀ c y : M, c * (z * y) * c⁻¹ = z * (c * y * c⁻¹) := by
    intro z hz c y
    rw [← mul_assoc, mem_center_iff.mp hz c]
    group
  have hinv : ∀ x z : M, z ∈ center M → x * g * x⁻¹ = z * g → x⁻¹ * g * x = z⁻¹ * g := by
    intro x z hz hx
    have h1 : x⁻¹ * (z * g) * x⁻¹⁻¹ = z * (x⁻¹ * g * x⁻¹⁻¹) := hpull z hz x⁻¹ g
    rw [← hx, inv_inv] at h1
    have h2 : x⁻¹ * (x * g * x⁻¹) * x = g := by group
    rw [h2] at h1
    calc x⁻¹ * g * x = z⁻¹ * (z * (x⁻¹ * g * x)) := by group
      _ = z⁻¹ * g := by rw [← h1]
  have hb' := hinv b δ hδ hb
  have ha' := hinv a ε hε ha
  have hconj : ⁅a, b⁆ * g * ⁅a, b⁆⁻¹ = g := by
    calc ⁅a, b⁆ * g * ⁅a, b⁆⁻¹ = a * (b * (a⁻¹ * (b⁻¹ * g * b) * a⁻¹⁻¹) * b⁻¹) * a⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = a * (b * (a⁻¹ * (δ⁻¹ * g) * a⁻¹⁻¹) * b⁻¹) * a⁻¹ := by rw [hb']
      _ = a * (b * (δ⁻¹ * (a⁻¹ * g * a⁻¹⁻¹)) * b⁻¹) * a⁻¹ := by
          rw [hpull δ⁻¹ (inv_mem hδ) a⁻¹ g]
      _ = a * (b * (δ⁻¹ * (ε⁻¹ * g)) * b⁻¹) * a⁻¹ := by rw [inv_inv, ha']
      _ = a * (δ⁻¹ * (b * (ε⁻¹ * g) * b⁻¹)) * a⁻¹ := by
          rw [hpull δ⁻¹ (inv_mem hδ) b (ε⁻¹ * g)]
      _ = a * (δ⁻¹ * (ε⁻¹ * (b * g * b⁻¹))) * a⁻¹ := by
          rw [hpull ε⁻¹ (inv_mem hε) b g]
      _ = a * (δ⁻¹ * (ε⁻¹ * (δ * g))) * a⁻¹ := by rw [hb]
      _ = a * ((δ⁻¹ * ε⁻¹ * δ) * g) * a⁻¹ := by group
      _ = (δ⁻¹ * ε⁻¹ * δ) * (a * g * a⁻¹) := by
          rw [hpull _ (mul_mem (mul_mem (inv_mem hδ) (inv_mem hε)) hδ) a g]
      _ = (δ⁻¹ * ε⁻¹ * δ) * (ε * g) := by rw [ha]
      _ = δ⁻¹ * (ε⁻¹ * δ) * (ε * g) := by group
      _ = δ⁻¹ * (δ * ε⁻¹) * (ε * g) := by rw [mem_center_iff.mp hδ ε⁻¹]
      _ = g := by group
  calc ⁅a, b⁆ * g = ⁅a, b⁆ * g * ⁅a, b⁆⁻¹ * ⁅a, b⁆ := by group
    _ = g * ⁅a, b⁆ := by rw [hconj]

theorem exists_abelian_of_psl2 {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    (hO : pPrimeCore 2 X = ⊥) {f : ℕ} (hm : Blueprint.LieModel (X ⧸ center X) .PSL 2 3 f)
    {t : X} (ht2 : orderOf t = 2) (htZ : t ∉ center X) :
    ∃ S : Subgroup X, (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) ∧
      (∀ u ∈ centralizer {t}, ∀ v ∈ centralizer {t}, ⁅u, v⁆ ∈ S) ∧
      ∀ u ∈ centralizer {t}, u * u ≠ 1 → u ∈ S := by
  have : Group.IsPerfect X := hX.1
  obtain ⟨-, hf, -, -, h23⟩ := N36.admissible_of_lieModel' hm
  obtain ⟨F, _, _, hFc, ⟨θ⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hm
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F 3]; norm_num
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hq2 : Nat.card F ≠ 2 := by
    intro h
    rw [hFc] at h
    have h3 : 3 ∣ 2 := h ▸ dvd_pow_self 3 (by omega)
    omega
  have hq3 : Nat.card F ≠ 3 := by
    intro h
    rw [hFc] at h
    exact h23 (by rw [h])
  have hG := CatalogueBGeneralLinear.specialLinear_quasisimple 2 F le_rfl (Or.inr hq2)
    (Or.inr hq3)
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* SL(2, F)),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : SL(2, F) →* E, ∀ x, π (s x) = x := fun E _ _ π hπ hker h2 => by
    obtain ⟨s, hs, -⟩ := CFSG.LieType.Steinberg.sl_central_two_extension_splitting 1 hF hπ hker h2
    exact ⟨s, hs⟩
  set β : SL(2, F) →* X ⧸ center X := θ.symm.toMonoidHom.comp (LinearFlag.proj 2 F)
  have hβ : Function.Surjective β := θ.symm.surjective.comp (LinearFlag.proj_surjective 2 F)
  have hη : (QuotientGroup.mk' (center X)).ker = center X := QuotientGroup.ker_mk' _
  obtain ⟨α, hαβ, hαs, -⟩ := CFSG.LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβ
    (QuotientGroup.mk'_surjective (center X)) hη.le
    (by rw [hη]; exact Sol78.center_isPGroup_two hO)
  have hnt : ∃ g, β g ≠ 1 := by
    obtain ⟨a, b, hab⟩ := hX.2.2
    by_contra hall
    have hall' : ∀ g, β g = 1 := fun g => by
      by_contra h
      exact hall ⟨g, h⟩
    apply hab
    obtain ⟨a, rfl⟩ := hβ a
    obtain ⟨b, rfl⟩ := hβ b
    rw [hall' a, hall' b]
  have hβZ := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hG hnt
  have hpm : ∀ z ∈ β.ker, z = 1 ∨ z = -1 := fun z hz =>
    Burgoyne.C.eq_one_or_eq_neg_one hF2 z (by
      rw [← pow_two]; exact Burgoyne.C.sq_eq_one_of_mem_center_SL (hβZ hz))
  have hαk : ∀ x : SL(2, F), α x = 1 → x = 1 ∨ x = -1 := fun x hx =>
    hpm x (by rw [MonoidHom.mem_ker, ← hαβ, hx, map_one])
  have hneg : (-1 : SL(2, F)) ∈ center SL(2, F) := by
    rw [mem_center_iff]
    intro y
    rw [mul_neg_one, neg_one_mul]
  obtain ⟨g, rfl⟩ := hαs t
  have hgZ : ¬ ∃ c : F, (g : Matrix (Fin 2) (Fin 2) F) = c • 1 := by
    rintro ⟨c, hc⟩
    apply htZ
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := hαs y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hc,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hαg2 : α (g * g) = 1 := by
    have h1 := pow_orderOf_eq_one (α g)
    rw [ht2, sq] at h1
    rw [map_mul]
    exact h1
  have hg2 : g * g = -1 := by
    rcases hαk _ hαg2 with h | h
    · exfalso
      rcases Burgoyne.C.eq_one_or_eq_neg_one hF2 g h with rfl | rfl
      · exact hgZ ⟨1, by rw [Matrix.SpecialLinearGroup.coe_one, one_smul]⟩
      · exact hgZ ⟨-1, by rw [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_one, neg_one_smul]⟩
    · exact h
  have hα1 : α (-1) = 1 := by rw [← hg2]; exact hαg2
  have hsign : ∀ h : SL(2, F), α h ∈ centralizer {α g} →
      h * g * h⁻¹ = g ∨ h * g * h⁻¹ = -g := by
    intro h hh
    have hc : α h * α g = α g * α h := mem_centralizer_singleton_iff.mp hh
    have h1 : α (h * g * h⁻¹ * g⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    rcases hαk _ h1 with h2 | h2
    · left
      calc h * g * h⁻¹ = h * g * h⁻¹ * g⁻¹ * g := by group
        _ = g := by rw [h2, one_mul]
    · right
      calc h * g * h⁻¹ = h * g * h⁻¹ * g⁻¹ * g := by group
        _ = -g := by rw [h2, neg_one_mul]
  have hconjc : ∀ h : SL(2, F), (h * g * h⁻¹ = g ∨ h * g * h⁻¹ = -g) →
      ∃ ε ∈ center SL(2, F), h * g * h⁻¹ = ε * g := by
    rintro h (h1 | h1)
    · exact ⟨1, one_mem _, by rw [h1, one_mul]⟩
    · exact ⟨-1, hneg, by rw [h1, neg_one_mul]⟩
  refine ⟨(centralizer {g}).map α, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    have ha' := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F))
      (mem_centralizer_singleton_iff.mp ha)
    have hb' := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F))
      (mem_centralizer_singleton_iff.mp hb)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at ha' hb'
    exact SectionRank.Ccomm.commute_of_commute_nonscalar hgZ ha'.symm hb'.symm
  ·
    intro u hu v hv
    obtain ⟨a, rfl⟩ := hαs u
    obtain ⟨b, rfl⟩ := hαs v
    obtain ⟨ε, hε, ha⟩ := hconjc a (hsign a hu)
    obtain ⟨δ, hδ, hb⟩ := hconjc b (hsign b hv)
    refine ⟨⁅a, b⁆, ?_, by rw [map_commutatorElement]⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact commutatorElement_mul_eq_of_conj hε hδ ha hb
  ·
    intro u hu hu1
    obtain ⟨a, rfl⟩ := hαs u
    rcases hsign a hu with ha | ha
    · refine ⟨a, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      calc a * g = a * g * a⁻¹ * a := by group
        _ = g * a := by rw [ha]
    · exfalso
      apply hu1
      rw [← map_mul, mul_self_eq_neg_one_of_conj_eq_neg hF2 ha, hα1]

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
