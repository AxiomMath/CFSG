module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Zc
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpFinal
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecTransport

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section

variable {G : Type} [Group G] {z : G} {k : Kind}
variable {A : Type} [Group A] [Finite A] {a : A} {p : ℕ} {X : Subgroup A}

omit [Finite A] in
theorem mem_map_conj_iff' {K : Subgroup A} {g y : A} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp

omit [Finite A] in
theorem map_conj_map_conj' (K : Subgroup A) (g h : A) :
    (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      K.map (MulAut.conj (g * h)).toMonoidHom := by
  ext y
  rw [mem_map_conj_iff', mem_map_conj_iff', mem_map_conj_iff']
  have : (g * h)⁻¹ * y * (g * h) = h⁻¹ * (g⁻¹ * y * g) * h := by group
  rw [this]

omit [Finite A] in
theorem mem_normalizer_of_map_conj_eq' {K : Subgroup A} {g : A}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ normalizer (K : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.ext_iff.mp h (g * y * g⁻¹)
  rw [mem_map_conj_iff'] at h1
  have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
  rw [this] at h1
  exact h1

omit [Finite A] in
theorem map_conj_eq_of_mem_normalizer {K : Subgroup A} {g : A} (h : g ∈ normalizer (K : Set A)) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  ext y
  rw [mem_map_conj_iff']
  have := (Subgroup.mem_normalizer_iff.mp (inv_mem h) y)
  simpa [mul_assoc] using this.symm

theorem E4Ctx.a_ne_one (c : E4Ctx G z A a p X) : a ≠ 1 := by
  intro h
  have := c.A4.comm
  rw [h, Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right] at this
  exact c.A4.ne_bot this.symm

omit [Finite A] in
theorem hat_equiv_conj (J : Subgroup A) (g : A) :
    Nonempty (Hat (J.map (MulAut.conj g).toMonoidHom) ≃* Hat J) := by
  let e : ↥J ≃* ↥(J.map (MulAut.conj g).toMonoidHom) := Transport.subEquiv (MulAut.conj g) rfl
  exact ⟨(QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)).symm⟩

omit [Finite A] in
theorem map_conj_one' (K : Subgroup A) : K.map (MulAut.conj (1 : A)).toMonoidHom = K := by
  ext y
  rw [mem_map_conj_iff']
  simp

omit [Finite A] in
theorem mem_zpowers_involution {a : A} (h : a * a = 1) {y : A} (hy : y ∈ zpowers a) : y = 1 ∨ y = a := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
  rcases Int.emod_two_eq_zero_or_one m with h0 | h1
  · left
    obtain ⟨t, ht⟩ : ∃ t : ℤ, m = 2 * t := ⟨m / 2, by omega⟩
    rw [ht, zpow_mul, h2, one_zpow]
  · right
    obtain ⟨t, ht⟩ : ∃ t : ℤ, m = 2 * t + 1 := ⟨m / 2, by omega⟩
    rw [ht, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem pPrimeCoreOf_le_centralizer {J : Subgroup A} (hJ : IsQuasisimple ↥J) :
    pPrimeCoreOf 2 J ≤ centralizer (J : Set A) := by
  rintro _ ⟨m, hm, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have := Subgroup.mem_center_iff.mp (pPrimeCore_le_center_comp hJ hm) ⟨j, hj⟩
  exact congrArg Subtype.val this

theorem centralizes_of_trivial_hat {J : Subgroup A} (hJ : IsComponent J) {a : A} (ha2 : a * a = 1)
    (haJ : a ∈ normalizer (J : Set A))
    (h : ∀ j ∈ J, a * j * a⁻¹ * j⁻¹ ∈ pPrimeCoreOf 2 J) : ∀ j ∈ J, a * j = j * a := by
  have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ.1.1
  have hle : ⁅J, zpowers a⁆ ≤ centralizer (J : Set A) := by
    rw [Subgroup.commutator_le]
    intro j hj y hy
    rcases mem_zpowers_involution ha2 hy with rfl | rfl
    · simp
    · rw [← commutatorElement_inv y j]
      refine inv_mem (pPrimeCoreOf_le_centralizer hJ.1 ?_)
      simpa [commutatorElement_def] using h j hj
  have hbot := comm_eq_bot_of_central hperf (zpowers_le.mpr haJ) hle
  intro j hj
  have h1 : ⁅j, a⁆ ∈ ⁅J, zpowers a⁆ := Subgroup.commutator_mem_commutator hj (Subgroup.mem_zpowers a)
  rw [hbot] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)).symm

theorem a_mem_normalizer_comp₂ (F : E4Hyp G z k) {c : E4Ctx G z A a p X} {J₁ J₂ : Subgroup A}
    (hJ₁ : IsComponent J₁) (haJ₁ : a ∈ normalizer (J₁ : Set A)) (hJ₂ : IsComponent J₂) (hne : J₁ ≠ J₂) :
    a ∈ normalizer (J₂ : Set A) := by
  by_cases h2 : J₂.map (MulAut.conj a).toMonoidHom = J₂
  · exact mem_normalizer_of_map_conj_eq' h2
  · exfalso
    have hJa : IsComponent (J₂.map (MulAut.conj a).toMonoidHom) := isComponent_conj hJ₂ a
    by_cases h1 : J₂.map (MulAut.conj a).toMonoidHom = J₁
    · apply hne
      have h3 := congrArg (fun K => K.map (MulAut.conj a).toMonoidHom) h1
      simp only [map_conj_map_conj', c.z2, map_conj_one', map_conj_eq_of_mem_normalizer haJ₁] at h3
      exact h3.symm
    · exact F.two A a c.sec J₁ J₂ _ hJ₁ hJ₂ hJa hne (Ne.symm h1) (fun h => h2 h.symm)

omit [Finite A] in
theorem commutator_conj_ne_bot {J₂ X : Subgroup A} {g : A}
    (h : ⁅J₂, X.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) : ⁅J₂.map (MulAut.conj g⁻¹).toMonoidHom, X⁆ ≠ ⊥ := by
  intro hb
  apply h
  have h1 := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hb
  rw [Subgroup.map_commutator, map_conj_map_conj', mul_inv_cancel, map_conj_one', Subgroup.map_bot] at h1
  exact h1

theorem sl2_two (F : E4Hyp G z k) {c : E4Ctx G z A a p X} {J₁ : Subgroup A} (d₁ : SubData c J₁)
    (h₁ : Sl2Cl p (secZ a X J₁) (secX a X J₁) (secJ a X J₁)) {J₂ : Subgroup A}
    (hJ₂ : IsComponent J₂) (hne : J₁ ≠ J₂) (hK : J₂ ≤ ncl X) : False := by
  have hcomp2 : ∀ J₃ : Subgroup A, IsComponent J₃ → J₃ = J₁ ∨ J₃ = J₂ := by
    intro J₃ h3
    by_contra hcon
    push Not at hcon
    exact F.two A a c.sec J₁ J₂ J₃ d₁.comp hJ₂ h3 hne hcon.1.symm hcon.2.symm
  have hX₂ : X ≤ normalizer (J₂ : Set A) :=
    X_le_normalizer_comp c.A4.prime c.A4.odd c.A4.pgroup hJ₂
      (fun J₁ J₂ J₃ => F.two A a c.sec J₁ J₂ J₃)
  have haJ₂ : a ∈ normalizer (J₂ : Set A) := a_mem_normalizer_comp₂ F (c := c) d₁.comp d₁.zJ hJ₂ hne
  have hcomm12 : J₂ ≤ centralizer (J₁ : Set A) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (comp_comm_of_ne hJ₂ d₁.comp hne.symm)
  have hcomm21 : J₁ ≤ centralizer (J₂ : Set A) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (comp_comm_of_ne d₁.comp hJ₂ hne)
  obtain ⟨y₁, hy₁, hy₁sq, hy₁4, hy₁c, hy₁z⟩ := d₁.exists_y h₁
  obtain ⟨F₀, hF₀, hFin, hodd, h3, ⟨eK⟩, -⟩ := Sl2Cl.model c.A4.prime c.A4.odd h₁
  obtain ⟨eS⟩ := secJ_equiv d₁.hyp
  have e₁ : Hat J₁ ≃* IVK.SL2 F₀ := eS.symm.trans eK
  have hcen₁ : center (Hat J₁) ≠ ⊥ := center_ne_bot_of_sl2 hodd e₁
  have hs₁C : y₁ * y₁ ∈ centralizer (J₁ : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (hy₁c j hj).symm
  have key : ∃ y₂ ∈ J₂, y₂ * y₂ ≠ 1 ∧ (y₂ * y₂) * (y₂ * y₂) = 1 ∧ a * y₂ * a⁻¹ = y₂⁻¹ := by
    by_cases hJ₂X : ⁅J₂, X⁆ = ⊥
    ·
      have hconj : ∃ g : A, J₂ = J₁.map (MulAut.conj g).toMonoidHom := by
        by_contra hno
        push Not at hno
        have hall : ∀ g : A, ⁅J₂, X.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
          intro g
          by_contra hg
          have hne3 := commutator_conj_ne_bot hg
          rcases hcomp2 _ (isComponent_conj hJ₂ g⁻¹) with h31 | h32
          · apply hno g
            have h4 := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h31
            rw [map_conj_map_conj', mul_inv_cancel, map_conj_one'] at h4
            exact h4
          · exact hne3 (by rw [h32]; exact hJ₂X)
        have hcent : ncl X ≤ centralizer (J₂ : Set A) := by
          unfold ncl
          rw [Subgroup.normalClosure, Subgroup.closure_le]
          intro y hy
          obtain ⟨b, hb, hbg⟩ := Group.mem_conjugatesOfSet_iff.mp hy
          obtain ⟨g, rfl⟩ := isConj_iff.mp hbg
          have hyX : g * b * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom :=
            Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
          have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hall g)
          rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
          intro j hj
          exact (Subgroup.mem_centralizer_iff.mp (hle hj) _ hyX).symm
        exact comp_not_le_centralizer hJ₂ (hK.trans hcent)
      obtain ⟨g, hg⟩ := hconj
      obtain ⟨eH⟩ := hat_equiv_conj J₁ g
      have e₂ : Hat J₂ ≃* IVK.SL2 F₀ := by rw [hg]; exact eH.trans e₁
      have hcen₂ : center (Hat J₂) ≠ ⊥ := center_ne_bot_of_sl2 hodd e₂
      have hnt₂ : ∃ j ∈ J₂, a * j * a⁻¹ * j⁻¹ ∉ pPrimeCoreOf 2 J₂ := by
        by_contra hcon
        push Not at hcon
        have haC : ∀ j ∈ J₂, a * j = j * a := centralizes_of_trivial_hat hJ₂ c.z2 haJ₂ hcon
        have haC' : a ∈ centralizer (J₂ : Set A) := by
          rw [Subgroup.mem_centralizer_iff]
          intro j hj
          exact (haC j hj).symm
        have hcommas : a * (y₁ * y₁) = (y₁ * y₁) * a := by
          have h1 : a * (y₁ * y₁) * a⁻¹ = y₁ * y₁ := by
            calc a * (y₁ * y₁) * a⁻¹ = (a * y₁ * a⁻¹) * (a * y₁ * a⁻¹) := by group
              _ = y₁⁻¹ * y₁⁻¹ := by rw [hy₁z]
              _ = (y₁ * y₁)⁻¹ := by group
              _ = y₁ * y₁ := inv_eq_of_mul_eq_one_right hy₁4
          calc a * (y₁ * y₁) = (a * (y₁ * y₁) * a⁻¹) * a := by group
            _ = (y₁ * y₁) * a := by rw [h1]
        have hae : a = y₁ * y₁ :=
          F.uinv A a c.sec J₂ hJ₂ hcen₂ a (y₁ * y₁) c.z2 hy₁4 c.a_ne_one hy₁sq haC'
            (hcomm21 (J₁.mul_mem hy₁ hy₁)) hcommas
        obtain ⟨j, hj, hjn⟩ := d₁.exists_nt h₁
        apply hjn
        have h5 : a * j * a⁻¹ * j⁻¹ = 1 := by
          have : a * j = j * a := by rw [hae]; exact (hy₁c j hj)
          rw [this]; group
        rw [h5]
        exact one_mem _
      obtain ⟨y₂, hy₂, h1, h2, -, h4⟩ := exists_inverted_lift hJ₂ haJ₂ c.z2 F₀ hodd h3 e₂ hnt₂
      exact ⟨y₂, hy₂, h1, h2, h4⟩
    ·
      have d₂ : SubData c J₂ := ⟨hJ₂, hX₂, haJ₂, hJ₂X⟩
      rcases d₂.cases F with ha | hb | hc' | hd
      · obtain ⟨y₂, hy₂, h1, h2, -, h4⟩ := d₂.exists_y (Or.inl ha)
        exact ⟨y₂, hy₂, h1, h2, h4⟩
      · obtain ⟨y₂, hy₂, h1, h2, -, h4⟩ := d₂.exists_y (Or.inr hb)
        exact ⟨y₂, hy₂, h1, h2, h4⟩
      · exfalso
        obtain ⟨n, hn1, hLie, -⟩ := hc'
        obtain ⟨c', hc'J, hc'o⟩ := exists_involution_comp d₁.comp
        have hLieHat : LieModel (Hat J₂) .PSL 3 p n :=
          Transport.lieModel_of_mulEquiv (secJ_equiv d₂.hyp).some hLie
        exact F.f3 A a c.sec J₂ hJ₂ p n c.A4.prime hn1
          (Or.inl ((c.A4.prime.odd_of_ne_two c.A4.odd).pow)) hLieHat c' hc'o (hcomm21 hc'J)
      · exfalso
        obtain ⟨-, -, hLie, -⟩ := hd
        obtain ⟨c', hc'J, hc'o⟩ := exists_involution_comp d₁.comp
        have hLieHat : LieModel (Hat J₂) .PSL 3 2 2 :=
          Transport.lieModel_of_mulEquiv (secJ_equiv d₂.hyp).some hLie
        exact F.f3 A a c.sec J₂ hJ₂ 2 2 Nat.prime_two (by norm_num) (Or.inr (by norm_num)) hLieHat
          c' hc'o (hcomm21 hc'J)
  obtain ⟨y₂, hy₂, hy₂sq, hy₂4, hy₂z⟩ := key
  have hs₂C : y₂ * y₂ ∈ centralizer (J₁ : Set A) := hcomm12 (J₂.mul_mem hy₂ hy₂)
  have hs : y₂ * y₂ = y₁ * y₁ := by
    refine F.uinv A a c.sec J₁ d₁.comp hcen₁ (y₂ * y₂) (y₁ * y₁) hy₂4 hy₁4 hy₂sq hy₁sq hs₂C hs₁C ?_
    exact (Subgroup.mem_centralizer_iff.mp hs₂C (y₁ * y₁) (J₁.mul_mem hy₁ hy₁)).symm
  exact d₁.zcontra h₁ hy₁ hy₁sq hy₁4 hy₁z (hcomm12 hy₂) hs hy₂z

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
