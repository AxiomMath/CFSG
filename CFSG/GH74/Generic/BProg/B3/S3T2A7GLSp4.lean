module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLCent
public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLSp4A
public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLSp4B
public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLBasic

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank
  Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.GH74.Filter.ClassicalOdd

namespace GLR

variable {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y} {z : Y}

theorem rankCertified_q8q8 : RankCertified (Q8 × Q8) 3 := by
  refine ⟨Q8 × Q8, V4 × V4, inferInstance, inferInstance, inferInstance, MonoidHom.id _,
    q8Frattini.prodMap q8Frattini, q8Frattini_surjective.prodMap q8Frattini_surjective,
    fun a b => mul_comm a b, by decide, by rw [card_V4_sq]; norm_num, ?_⟩
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
  rw [hx]
  exact one_mem _

omit [Finite Y] in
theorem false_of_q8q8 (hs : Setting125 Y L B X₀ z) {φ : Q8 × Q8 →* Y}
    (hφ : Function.Injective φ) {b : Y} (hb2 : b * b = 1) (hbφ : ∀ g, φ g ≠ b)
    (hcomm : ∀ g, b * φ g = φ g * b) : False := by
  set C : Subgroup Y := centralizer ({b} : Set Y) with hC
  have hφC : ∀ g, φ g ∈ C := fun g => mem_centralizer_singleton_iff.mpr (hcomm g).symm
  let ψ : Q8 × Q8 →* ↥C := φ.codRestrict C hφC
  have hψ : Function.Injective ψ := fun g h e => hφ (congrArg Subtype.val e)
  let c : ↥C := ⟨b, mem_centralizer_singleton_iff.mpr rfl⟩
  have hcc : ∀ x : ↥C, x * c = c * x := fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp x.2)
  have hc2 : c * c = 1 := Subtype.ext hb2
  have hcK : c ∉ ψ.range := by
    rintro ⟨g, hg⟩
    exact hbφ g (congrArg Subtype.val hg)
  have hK : RankCertified ↥ψ.range 3 :=
    rankCertified_q8q8.of_injective ψ.rangeRestrict fun g h e => hψ (congrArg Subtype.val e)
  exact (RankCertified.of_central_involution hcc hc2 hcK hK).of_subgroup.not_sectionalTwoRankLE
    hs.sec4

theorem isEA_of_forall {X : Type*} [Group X] {U : Subgroup X}
    (hab : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hsq : ∀ u ∈ U, u * u = 1) :
    CFSG.IsElementaryAbelian 2 ↥U := by
  have : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, sq]
  exact hsq a a.2

theorem exists_units_sq {F : Type} [Field F] {μ : Fˣ} (h : IsSquare (μ : F)) :
    ∃ l : Fˣ, μ = l * l := by
  obtain ⟨c, hc⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact μ.ne_zero (by rw [hc, mul_zero])
  exact ⟨Units.mk0 c hc0, Units.ext (by rw [hc, Units.val_mul, Units.val_mk0])⟩

end GLR

theorem cell125_sp4 (hF : GenericKnownFacts) : Cell125 OddSp4 := by
  intro Y _ _ L B X₀ z hs hP _ _
  classical
  obtain ⟨p, f, hp, hp2, -, hm⟩ := hP
  obtain ⟨-, -, F₀, _, _, hF₀c, ⟨e₀⟩⟩ := lieModel_psp_data hm
  have hc3 : RankCertified (↥L ⧸ center ↥L) 3 :=
    (rankCertified_PSp4 (ringChar_ne_two_of_card_eq hp hp2 hF₀c)).of_mulEquiv e₀.symm
  have hZ := GLR.center_ne_bot_of_mem hs (mem_of_rankCertified_three hs hc3)
  obtain ⟨F, _, _, hFc, ⟨ψ⟩⟩ :=
    (hF.psp4_cover p f hp hp2 ↥L hs.comp.1 (GLR.isPGroup_center hs) hm).resolve_left hZ
  have hFodd : Odd (Nat.card F) := by rw [hFc]; exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hFodd
  have hN : ∀ b : Y, b ∈ normalizer (L : Set Y) :=
    normal_of_rankCertified hs.sec4 hs.comp (hc3.mono (by norm_num))
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hs.B_el
  set α : ↥(normalizer (L : Set Y)) →* MulAut ↥(StatedSp 2 F) := B2.actOn L ψ with hα
  have hact : ∀ b : Y, ∀ y : ↥(StatedSp 2 F),
      ((ψ.symm (α ⟨b, hN b⟩ y) : ↥L) : Y) = b * (ψ.symm y : Y) * b⁻¹ :=
    fun b y => B2.coe_symm_actOn L ψ ⟨b, hN b⟩ y
  have hαmul : ∀ b₁ b₂ : Y, α ⟨b₁ * b₂, hN _⟩ = α ⟨b₁, hN b₁⟩ * α ⟨b₂, hN b₂⟩ :=
    fun b₁ b₂ => by rw [← map_mul]; rfl
  have hinner : ∀ b ∈ B, ∀ g : ↥(StatedSp 2 F), α ⟨b, hN b⟩ = MulAut.conj g → b ∈ L := by
    intro b hb g hg
    refine GLR.mem_of_inner hs hc3 (ψ.symm g).2 (hBsq b hb) fun x hx => ?_
    have h1 := hact b (ψ ⟨x, hx⟩)
    rw [hg, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply] at h1
    simpa using h1.symm
  by_cases hlin : ∀ b ∈ B, ∃ A : gsp 2 F, α ⟨b, hN b⟩ = conjSp 2 F A
  ·
    have hns : ∀ b ∈ B, ∀ A : gsp 2 F, α ⟨b, hN b⟩ = conjSp 2 F A → b ∉ L →
        ¬ IsSquare ((multiplier 2 F A : Fˣ) : F) := by
      intro b hb A hA hbL hsq
      obtain ⟨l, hl⟩ := GLR.exists_units_sq hsq
      obtain ⟨g, hg⟩ := GLR.conjSp_eq_conj_of_multiplier hl
      exact hbL (hinner b hb g (hA.trans hg))
    have hmulL : ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ∉ L → b₂ ∉ L → b₁ * b₂ ∈ L := by
      intro b₁ hb₁ b₂ hb₂ h₁ h₂
      obtain ⟨A₁, hA₁⟩ := hlin b₁ hb₁
      obtain ⟨A₂, hA₂⟩ := hlin b₂ hb₂
      have hsq := GLR.isSquare_mul_of_not_isSquare (Units.ne_zero _) (Units.ne_zero _)
        (hns b₁ hb₁ A₁ hA₁ h₁) (hns b₂ hb₂ A₂ hA₂ h₂)
      rw [← Units.val_mul, ← map_mul] at hsq
      obtain ⟨l, hl⟩ := GLR.exists_units_sq hsq
      obtain ⟨g, hg⟩ := GLR.conjSp_eq_conj_of_multiplier hl
      exact hinner (b₁ * b₂) (mul_mem hb₁ hb₂) g (by rw [hαmul, hA₁, hA₂, ← map_mul, hg])
    set H : Subgroup ↥L := B.subgroupOf L with hH
    have hcardB : Nat.card ↥B = 16 := by
      rw [C3.Layer1.Back.card_eq_two_pow_pRank hs.B_el, hs.B_rank]
      norm_num
    have hcardH : 8 ≤ Nat.card ↥H := by
      by_cases hBL : ∀ b ∈ B, b ∈ L
      · have h1 : Nat.card ↥H = Nat.card ↥B :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe fun b hb => hBL b hb).toEquiv
        omega
      · push Not at hBL
        obtain ⟨b₀, hb₀B, hb₀L⟩ := hBL
        let j : ↥B → ↥H ⊕ ↥H := fun b =>
          if hb : (b : Y) ∈ L then Sum.inl ⟨⟨b, hb⟩, Subgroup.mem_subgroupOf.mpr b.2⟩
          else Sum.inr ⟨⟨b * b₀, hmulL b b.2 b₀ hb₀B hb hb₀L⟩,
            Subgroup.mem_subgroupOf.mpr (mul_mem b.2 hb₀B)⟩
        have hj : Function.Injective j := by
          intro x y hxy
          by_cases hx : (x : Y) ∈ L <;> by_cases hy : (y : Y) ∈ L
          · simp only [j, hx, hy, ↓reduceDIte, Sum.inl.injEq] at hxy
            exact Subtype.ext (congrArg (fun w : ↥H => ((w : ↥L) : Y)) hxy)
          · simp [j, hx, hy] at hxy
          · simp [j, hx, hy] at hxy
          · simp only [j, hx, hy, ↓reduceDIte, Sum.inr.injEq] at hxy
            exact Subtype.ext (mul_right_cancel (congrArg (fun w : ↥H => ((w : ↥L) : Y)) hxy))
        have h1 := Nat.card_le_card_of_injective j hj
        rw [Nat.card_sum] at h1
        omega
    set E : Subgroup ↥(StatedSp 2 F) := H.map ψ.toMonoidHom with hE
    have hEel : CFSG.IsElementaryAbelian 2 ↥E := by
      refine GLR.isEA_of_forall ?_ ?_
      · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg _ (Subtype.ext (hBc _ (Subgroup.mem_subgroupOf.mp hu) _
          (Subgroup.mem_subgroupOf.mp hv)))
      · rintro _ ⟨u, hu, rfl⟩
        rw [← map_mul, show u * u = 1 from Subtype.ext (hBsq _ (Subgroup.mem_subgroupOf.mp hu)),
          map_one]
    have hcardE : Nat.card ↥E = Nat.card ↥H :=
      Subgroup.card_map_of_injective ψ.injective
    have h4 := GLR.card_le_four_sp4 h2 hEel
    omega
  ·
    push Not at hlin
    obtain ⟨b, hb, hbA⟩ := hlin
    obtain ⟨A, σ, hAσ⟩ := aut_statedSp2 hFodd (α ⟨b, hN b⟩)
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      exact hbA A (by rw [hAσ, map_one, mul_one])
    have hsq : ∀ k, (conjSp 2 F A * fieldSp 2 F σ) ((conjSp 2 F A * fieldSp 2 F σ) k) = k := by
      intro k
      have h1 : α ⟨b * b, hN _⟩ = 1 := by
        rw [show (⟨b * b, hN _⟩ : ↥(normalizer (L : Set Y))) = 1 from Subtype.ext (hBsq b hb),
          map_one]
      rw [hαmul, hAσ] at h1
      rw [← MulAut.mul_apply, h1, MulAut.one_apply]
    obtain ⟨hσ2, c, hc⟩ := sq_one_consequences A σ hsq
    obtain ⟨φ, hφ, hfix⟩ := GLR.exists_q8q8_fixed hFodd σ hσ1 hσ2 A c hc
    have hbL : b ∉ L := by
      intro hbL
      apply hσ1
      refine GLR.eq_one_of_conjSp_mul_fieldSp_eq (A := A)
        (C := ⟨((ψ ⟨b, hbL⟩ : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F),
          statedSp_le_gsp (ψ ⟨b, hbL⟩).2⟩) ?_
      rw [← hAσ]
      refine MulEquiv.ext fun y => ψ.symm.injective (Subtype.ext ?_)
      rw [hact]
      have h1 : conjSp 2 F ⟨((ψ ⟨b, hbL⟩ : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F),
          statedSp_le_gsp (ψ ⟨b, hbL⟩).2⟩ y = ψ ⟨b, hbL⟩ * y * (ψ ⟨b, hbL⟩)⁻¹ :=
        Subtype.ext (by rw [coe_conjSp]; rfl)
      rw [h1, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
      rfl
    refine GLR.false_of_q8q8 hs (φ := L.subtype.comp (ψ.symm.toMonoidHom.comp φ))
      (L.subtype_injective.comp (ψ.symm.injective.comp hφ)) (hBsq b hb) ?_ ?_
    · intro g hg
      exact hbL (hg ▸ (ψ.symm (φ g)).2)
    · intro g
      have h1 := hact b (φ g)
      rw [hAσ, hfix g] at h1
      change b * (ψ.symm (φ g) : Y) = (ψ.symm (φ g) : Y) * b
      calc b * (ψ.symm (φ g) : Y) = b * (ψ.symm (φ g) : Y) * b⁻¹ * b := by group
        _ = (ψ.symm (φ g) : Y) * b := by rw [← h1]

end CFSG.GH74.Generic.BProg.B3.S3T2A7
