module

public import CFSG.GH74.GLS.Stage4.T2RemProofL
public import CFSG.GH74.GLS.Stage4.T2RemProofAut
public import CFSG.GH74.GLS.Stage4.T2RemProofAut3
public import CFSG.GH74.GLS.Stage4.T2RemProofSwap

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.BNPair CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl CFSG.Blueprint

namespace CFSG.GH74.GLS.Stage4.Rest.Rem

section Glue

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem exists_big_two_subgroup (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) {n : ℕ} (hn : 2 ≤ n)
    (hv₁ : (Nat.card ↥K₁).factorization 2 = n + 1) :
    ∃ P : Subgroup G, P ≤ K₁ ∧ z ∈ P ∧ IsPGroup 2 ↥P ∧ 8 ≤ Nat.card ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 K₁
  have hcard : Nat.card P = 2 ^ (n + 1) := by rw [hP.card_eq, hv₁]
  have hzz := t2C_zz hSet
  have hzK₂ : Subgroup.zpowers z ≤ K₂ := (Subgroup.zpowers_le).2 hSet.z_mem₂
  have hQ2 : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers z) := by
    intro g
    obtain ⟨p, hp, w, hw, hg⟩ := (mem_sup_iff_of_comm (K₁ := P) (K₂ := Subgroup.zpowers z)
      (fun x hx y hy => hSet.comm x (hP.le hx) y (hzK₂ hy)) g).1 g.2
    obtain ⟨k, hk⟩ := hP.isPGroup ⟨p, hp⟩
    have hk' : p ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hw2 : w * w = 1 := by
      rcases t2C_zpowers_cases hzz hw with h | h
      · rw [h, one_mul]
      · rw [h]; exact hzz
    refine ⟨k + 1, ?_⟩
    apply Subtype.ext
    have hcom : Commute p w := hSet.comm p (hP.le hp) w (hzK₂ hw)
    have : (g : G) ^ (2 ^ (k + 1)) = 1 := by
      have hw2' : w ^ 2 = 1 := by rw [pow_two]; exact hw2
      rw [hg, hcom.mul_pow, pow_succ, pow_mul, hk', one_pow, one_mul, pow_mul, ← pow_mul, mul_comm,
        pow_mul, hw2', one_pow]
    simpa using this
  have hPQ : P ≤ P ⊔ Subgroup.zpowers z := le_sup_left
  have hQK : P ⊔ Subgroup.zpowers z ≤ K₁ := sup_le hP.le ((Subgroup.zpowers_le).2 hSet.z_mem₁)
  have hEq := hP.eq_of_le hPQ hQK hQ2
  refine ⟨P, hP.le, ?_, hP.isPGroup, ?_⟩
  · rw [← hEq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  · rw [hcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Glue

section Act

variable {G : Type} [Group G]

theorem actsAsConj_of_fix {K : Subgroup G} {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {t : G} (htt : t * t = 1)
    (hn : ∀ x ∈ K, t * x * t⁻¹ ∈ K)
    (hfix : ∀ x ∈ K, x * t = t * x → x ^ 4 = 1 → x * x = 1) :
    ∃ (e' : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) (g : GL (Fin 2) F),
      ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ∧ ActsAsConj t K e' g := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hcc : ∀ x : G, t * (t * x * t⁻¹) * t⁻¹ = x := fun x => by
    rw [hti]
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [htt]; group
  let c : MulAut ↥K :=
    { toFun := fun x => ⟨t * x * t⁻¹, hn x x.2⟩
      invFun := fun x => ⟨t * x * t⁻¹, hn x x.2⟩
      left_inv := fun x => Subtype.ext (hcc x)
      right_inv := fun x => Subtype.ext (hcc x)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcx : ∀ x : ↥K, ((c x : ↥K) : G) = t * (x : G) * t⁻¹ := fun x => rfl
  let α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) := MulAut.congr e c
  have hαe : ∀ y : ↥K, α (e y) = e (c y) := fun y => by simp [α, MulAut.congr_apply]
  have hα2 : α * α = 1 := by
    apply MulEquiv.ext
    intro X
    obtain ⟨y, rfl⟩ := e.surjective X
    rw [MulAut.mul_apply, hαe, hαe, MulAut.one_apply]
    congr 1
    exact Subtype.ext (hcc y)
  have hfixα : ∀ x : Matrix.SpecialLinearGroup (Fin 2) F, α x = x → x ^ 4 = 1 → x * x = 1 := by
    intro x hx hx4
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [hαe] at hx
    have hy : c y = y := e.injective hx
    have hyt : (y : G) * t = t * (y : G) := by
      have h1 : t * (y : G) * t⁻¹ = y := by rw [← hcx, hy]
      calc (y : G) * t = (t * (y : G) * t⁻¹) * t := by rw [h1]
        _ = t * (y : G) := by group
    have hy4 : (y : G) ^ 4 = 1 := by
      have : y ^ 4 = 1 := e.injective (by rw [map_pow, hx4, map_one])
      simpa using congrArg Subtype.val this
    have h2 : y * y = 1 := Subtype.ext (by simpa using hfix y y.2 hyt hy4)
    rw [← map_mul, h2, map_one]
  have hF3 : 3 ≤ Nat.card F := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨g, hgdet, hg⟩ : ∃ g : GL (Fin 2) F,
      ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ∧
      ∀ x : Matrix.SpecialLinearGroup (Fin 2) F,
        ((α x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          (g : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
            ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    by_cases h3 : 3 < Nat.card F
    · exact exists_outer_diag_of_involution hodd h3 α hα2 hfixα
    · exact exists_outer_diag_of_involution_three (by omega) α hα2 hfixα
  refine ⟨e, g, hgdet, fun x => ⟨c x, hcx x, ?_⟩⟩
  have := hg (e x)
  rw [hαe] at this
  exact this

end Act

section Certs


variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem fix_of_lemmaL (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) {t : G} (htt : t * t = 1)
    (htC : t ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G))) (htK : t ∉ K₁ ⊔ K₂)
    {x : G} (hx : x ∈ K₁ ⊔ K₂) (hxt : x * t = t * x) (hx4 : x ^ 4 = 1) : x * x = 1 := by
  classical
  set s : Set G := {x, t} with hs
  have hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    intro a ha b hb
    simp only [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hxt
    · exact hxt.symm
    · rfl
  have ht4 : t ^ 4 = 1 := by
    have : t ^ 4 = (t * t) * (t * t) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [this, htt, mul_one]
  have hexp : ∀ g ∈ Subgroup.closure s, g ^ 4 = 1 := by
    refine t2S_closure_pow hcomm ?_
    intro a ha
    simp only [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hx4
    · exact ht4
  have hW : IsPGroup 2 ↥(Subgroup.closure s) := by
    intro g
    refine ⟨2, ?_⟩
    apply Subtype.ext
    simpa using hexp g g.2
  have hxW : x ∈ Subgroup.closure s := Subgroup.subset_closure (by simp [hs])
  have htW : t ∈ Subgroup.closure s := Subgroup.subset_closure (by simp [hs])
  have hWC : Subgroup.closure s ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    rw [Subgroup.closure_le]
    intro a ha
    simp only [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hSet.le_residual hx
    · exact htC
  obtain ⟨U, -, hU2, hU⟩ := lemmaL hSet htt htK _ hW hWC htW
  exact hU2 x (hU x hxW hx hxt)

theorem normalizes_K (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) {t : G} (htt : t * t = 1)
    (htC : t ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G))) (htK : t ∉ K₁ ⊔ K₂) :
    (∀ x ∈ K₁, t * x * t⁻¹ ∈ K₁) ∧ (∀ x ∈ K₂, t * x * t⁻¹ ∈ K₂) := by
  have := hSet.finite₁
  have := hSet.finite₂
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  obtain ⟨e₁⟩ := hSet.iso₁
  obtain ⟨e₂⟩ := hSet.iso₂
  have hC : T2Comp z K₁ K₂ :=
    t2C_comp_of hSet (gen_odd_of_sl2 hodd₁ e₁) (gen_odd_of_sl2 hodd₂ e₂)
  have hzz := t2C_zz hSet
  have hz1 := t2C_z_ne hSet
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htz : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.1
    ((Subgroup.map_subtype_le _ : oPrimeResidualOf 2 (centralizer ({z} : Set G)) ≤
      centralizer ({z} : Set G)) htC)
  have hK : ∀ x ∈ K₁ ⊔ K₂, t * x * t⁻¹ ∈ K₁ ⊔ K₂ :=
    conj_mem_of_relIndex_two hSet.le_residual hSet.index_two t htC
  have hK' : ∀ x ∈ K₁ ⊔ K₂, t⁻¹ * x * t ∈ K₁ ⊔ K₂ := by
    intro x hx
    have := hK x hx
    rw [hti] at this ⊢
    exact this
  have hn₁ : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₁ := by
    rcases t2C_conj_K₁ hC htz hK hK' with h | h
    · intro x hx
      have : t * x * t⁻¹ ∈ K₁.map (MulAut.conj t).toMonoidHom :=
        ⟨x, hx, by simp [MulAut.conj_apply]⟩
      rwa [h] at this
    · exfalso
      obtain ⟨n, hn, hv₁, -, -⟩ := exists_shape_equiv hSet
      obtain ⟨P, hPK, hzP, hP2, hP8⟩ := exists_big_two_subgroup hSet hn hv₁
      refine swap_contradiction hzz hz1 hSet.z_mem₁ hSet.z_mem₂ hSet.comm hSet.inter_eq.le htt htz
        (fun x hx => ?_) P hPK hzP hP2 hP8 (fun W hW htW hWle => ?_)
      · have : t * x * t⁻¹ ∈ K₁.map (MulAut.conj t).toMonoidHom :=
          ⟨x, hx, by simp [MulAut.conj_apply]⟩
        rwa [h] at this
      · obtain ⟨U, hU, -, hU3⟩ := lemmaL hSet htt htK W hW
          (hWle.trans (sup_le hSet.le_residual ((Subgroup.zpowers_le).2 htC))) htW
        exact ⟨U, hU, hU3⟩
  refine ⟨hn₁, ?_⟩
  intro y hy
  have hyK : t * y * t⁻¹ ∈ K₁ ⊔ K₂ := hK y (Subgroup.mem_sup_right hy)
  have hcomm' : ∀ k ∈ K₁, (t * y * t⁻¹) * k = k * (t * y * t⁻¹) := by
    intro k hk
    have hk' : t⁻¹ * k * t ∈ K₁ := by
      rw [hti]
      have := hn₁ k hk
      rwa [hti] at this
    have h1 := hSet.comm (t⁻¹ * k * t) hk' y hy
    calc t * y * t⁻¹ * k = t * (y * (t⁻¹ * k * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * k * t) * y) * t⁻¹ := by rw [← h1]
      _ = k * (t * y * t⁻¹) := by group
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_comm hSet.comm _).1 hyK
  have haz : a ∈ Subgroup.zpowers z := by
    refine hC.Z₁ a ha (fun k' hk' => ?_)
    have h1 := hcomm' k' hk'
    have h2 : b * k' = k' * b := (hSet.comm k' hk' b hb).symm
    rw [hab] at h1
    have : a * k' * b = k' * a * b := by
      calc a * k' * b = a * (k' * b) := by group
        _ = a * (b * k') := by rw [← (hSet.comm k' hk' b hb)]
        _ = a * b * k' := by group
        _ = k' * (a * b) := h1
        _ = k' * a * b := by group
    exact mul_right_cancel this
  rw [hab]
  exact K₂.mul_mem ((Subgroup.zpowers_le).2 hSet.z_mem₂ haz) hb

theorem ch6T2RemDiag_proved : Ch6T2RemDiag := by
  intro G _ _ hStd hr Gs _ q₁ q₂ z K₁ K₂ F₁ F₂ _ _ hSet t htt htC htK
  have := hSet.finite₁
  have := hSet.finite₂
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  obtain ⟨e₁⟩ := hSet.iso₁
  obtain ⟨e₂⟩ := hSet.iso₂
  obtain ⟨hn₁, hn₂⟩ := normalizes_K hSet htt htC htK
  exact ⟨actsAsConj_of_fix hodd₁ e₁ htt hn₁ (fun x hx hxt hx4 =>
      fix_of_lemmaL hSet htt htC htK (Subgroup.mem_sup_left hx) hxt hx4),
    actsAsConj_of_fix hodd₂ e₂ htt hn₂ (fun x hx hxt hx4 =>
      fix_of_lemmaL hSet htt htC htK (Subgroup.mem_sup_right hx) hxt hx4)⟩

theorem ch6T2Rem_proved : Ch6T2Rem := ch6T2Rem_of_diag ch6T2RemDiag_proved

end Certs

end CFSG.GH74.GLS.Stage4.Rest.Rem
