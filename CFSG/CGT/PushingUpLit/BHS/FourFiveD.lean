module

public import CFSG.CGT.PushingUpLit.BHS.FourFiveC

public section

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

namespace Hyp413Comm

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
  {T M L A B : Subgroup (MulAut V)} {n : ℕ}

theorem kerW_centralizes (h : Hyp43 P D T M) (hV : ∀ v : V, v ^ 2 = 1)
    (d : Hyp413Comm P D M L A B n) (hAT : A ≤ T) (hBT : B ≤ T) (hLM : ¬ L ≤ M) :
    ∀ k ∈ kerW L B, ∀ w ∈ commV L ⊔ fixV (L ⊔ B), k w = w := by
  have hKM : kerW L B ≤ M := d.kerW_le_M h hV hAT hBT
  have hK2 : IsPGroup 2 (kerW L B) := d.isPGroup_kerW hV
  have hcen : cenIn P (fixV (kerW L B)) ≤ M := h.toHyp42.cenIn_le_of_le_M le_rfl hKM hK2
  obtain ⟨l, hl, c, hc, hlc⟩ : ∃ l ∈ L, ∃ c ∈ fixV (kerW L B), l c ≠ c := by
    by_contra hcon
    push Not at hcon
    exact hLM fun l hl => hcen ⟨d.lam.1 hl, fun c hc => hcon l hl c hc⟩
  have hnormK : ∀ g ∈ L, ∀ k ∈ kerW L B, g⁻¹ * k * g ∈ kerW L B := fun g hg k hk => by
    have := d.kerW_normal (g := g⁻¹) ((L ⊔ B).inv_mem (Subgroup.mem_sup_left hg)) hk
    rwa [inv_inv] at this
  have hKfix : ∀ g ∈ L, ∀ u ∈ fixV (kerW L B), g u ∈ fixV (kerW L B) := by
    intro g hg u hu k hk
    have h1 : (g⁻¹ * k * g) u = u := hu _ (hnormK g hg k hk)
    calc k (g u) = g ((g⁻¹ * k * g) u) := by simp [MulAut.mul_apply]
      _ = g u := by rw [h1]
  have hcV : c ∈ (commV L ⊔ fixV (L ⊔ B)) ⊔ fixV L := by
    rw [d.sup_fixV_eq_top]
    exact Subgroup.mem_top c
  obtain ⟨w₁, hw₁, f₁, hf₁, rfl⟩ := Subgroup.mem_sup.1 hcV
  set N₀ : Subgroup V := (commV L ⊔ fixV (L ⊔ B)) ⊓ fixV (kerW L B)
  have hN₀inv : ∀ g ∈ L, ∀ u ∈ N₀, g u ∈ N₀ := fun g hg u hu =>
    ⟨d.invariant g (Subgroup.mem_sup_left hg) u hu.1, hKfix g hg u hu.2⟩
  have hcomm : ∀ l' ∈ L, l' w₁ * w₁⁻¹ ∈ N₀ := by
    intro l' hl'
    have e : l' w₁ * w₁⁻¹ = l' (w₁ * f₁) * (w₁ * f₁)⁻¹ := by
      rw [map_mul, hf₁ l' hl']
      comm_group
    refine Subgroup.mem_inf.2 ⟨mul_mem (d.invariant l' (Subgroup.mem_sup_left hl') w₁ hw₁)
      (inv_mem hw₁), ?_⟩
    rw [e]
    exact mul_mem (hKfix l' hl' _ hc) (inv_mem hc)
  have hex : ∃ l' ∈ L, l' w₁ * w₁⁻¹ ∉ fixV (L ⊔ B) := by
    by_contra hcon
    push Not at hcon
    have hw₁F : w₁ ∈ fixV (L ⊔ B) := d.sectionW.mem_of_forall_fixed d.one_le hw₁ hcon
    apply hlc
    have h1 : l w₁ = w₁ := fixV_anti (le_sup_left : L ≤ L ⊔ B) hw₁F l hl
    rw [map_mul, h1, hf₁ l hl]
  obtain ⟨l', hl', hl'F⟩ := hex
  have hN₀F : ¬ N₀ ≤ fixV (L ⊔ B) := fun hle => hl'F (hle (hcomm l' hl'))
  have hsup : N₀ ⊔ fixV (L ⊔ B) = commV L ⊔ fixV (L ⊔ B) :=
    d.sectionW.sup_eq_of_invariant d.one_le le_sup_right inf_le_left hN₀inv hN₀F
  have hWfix : commV L ⊔ fixV (L ⊔ B) ≤ fixV (kerW L B) := by
    rw [← hsup]
    exact sup_le inf_le_right fun z hz k hk => hz k (kerW_le L B hk)
  exact fun k hk w hw => hWfix hw k hk

theorem card_kerW_le (h : Hyp43 P D T M) (hV : ∀ v : V, v ^ 2 = 1)
    (d : Hyp413Comm P D M L A B n) (hAT : A ≤ T) (hBT : B ≤ T) (hLM : ¬ L ≤ M) :
    Nat.card ↥(kerW L B) ≤ 2 ^ n := by
  have hcen := d.kerW_centralizes h hV hAT hBT hLM
  have hWfix : commV L ⊔ fixV (L ⊔ B) ≤ fixV (kerW L B) := fun w hw k hk => hcen k hk w hw
  have hquad : IsQuadratic (kerW L B) := d.commV_kerW_le.trans hWfix
  have hel : IsElemAbelian2 (kerW L B) := isElemAbelian2_of_isQuadratic hV hquad
  have hKP : kerW L B ≤ P := (kerW_le L B).trans (sup_le d.lam.1 (h.le B d.memB))
  have hmax := h.max A d.memA (kerW L B) hel hKP
  have hWle : Nat.card ↥(commV L ⊔ fixV (L ⊔ B)) ≤ Nat.card ↥(fixV (kerW L B)) :=
    Subgroup.card_le_of_le hWfix
  have h1 : Nat.card ↥(kerW L B) * ((2 ^ n) ^ 2 * Nat.card ↥(fixV (L ⊔ B))) ≤
      2 ^ n * ((2 ^ n) ^ 2 * Nat.card ↥(fixV (L ⊔ B))) :=
    calc Nat.card ↥(kerW L B) * ((2 ^ n) ^ 2 * Nat.card ↥(fixV (L ⊔ B)))
        = Nat.card ↥(kerW L B) * Nat.card ↥(commV L ⊔ fixV (L ⊔ B)) := by rw [d.card_W]
      _ ≤ Nat.card ↥(kerW L B) * Nat.card ↥(fixV (kerW L B)) := Nat.mul_le_mul_left _ hWle
      _ ≤ Nat.card A * Nat.card ↥(fixV A) := hmax
      _ = Nat.card V := (h.card_eq A d.memA).symm
      _ = (2 ^ n) ^ 3 * Nat.card ↥(fixV (L ⊔ B)) := d.card_V_star
      _ = 2 ^ n * ((2 ^ n) ^ 2 * Nat.card ↥(fixV (L ⊔ B))) := by ring
  exact Nat.le_of_mul_le_mul_right h1 (Nat.mul_pos (by positivity) Nat.card_pos)

end Hyp413Comm

theorem four_fifteen {P : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)} (h : Hyp43 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) {A B L : Subgroup (MulAut V)} (hA : A ∈ dInter D T)
    (hB : B ∈ dInter D T) (hne : A ≠ B) (hL : L ∈ lamSet P D M) (hAL : A ≤ L) (hLM : ¬ L ≤ M) :
    ∀ l ∈ L, ∀ b ∈ B, l * b = b * l := by
  by_contra hno
  push Not at hno
  obtain ⟨l, hl, b, hb, hlb⟩ := hno
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    h.toHyp41.four_seven_pairs h.syl A hA B hB a ha b hb
  have hABab : IsElemAbelian2 (A ⊔ B) :=
    isElemAbelian2_sup (h.elemAb A hA.1) (h.elemAb B hB.1) hcomm
  have hL' := hL
  obtain ⟨-, ⟨n, hn1, hSL⟩, hΛ2, -⟩ := hL'
  have hAsyl : IsSylowOf 2 A L := (hΛ2 A).1 ⟨hA.1, hAL⟩
  have hBL : ¬ B ≤ L := by
    intro hBL
    have hBsyl : IsSylowOf 2 B L := (hΛ2 B).1 ⟨hB.1, hBL⟩
    have hsup : A ⊔ B = L := hSL.sylow_sup_eq hn1 hAsyl hBsyl hne
    rw [hsup] at hABab
    exact hlb (hABab.1 l hl b (hBL hb))
  have d : Hyp413Comm P D M L A B n :=
    ⟨h.toHyp41, hL, hn1, hSL, hA.1, hAL, hB.1, hBL, hcomm, ⟨l, hl, b, hb, hlb⟩⟩
  have hAT : A ≤ T := hA.2
  have hBT : B ≤ T := hB.2
  have hLBle : A ⊔ B ≤ L ⊔ B := sup_le_sup_right hAL B
  set C₀ : Subgroup (MulAut V) :=
    (A ⊔ B) ⊓ cenSection (commV L ⊔ fixV (L ⊔ B)) (fixV (L ⊔ B))
  have hC₀K : C₀ ≤ kerW L B := fun x hx => ⟨hLBle hx.1, hx.2⟩
  have hC₀AB : C₀ ≤ A ⊔ B := inf_le_left
  have hAC : A ⊓ C₀ = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    exact Subgroup.mem_bot.2 (d.sectionW.eq_one_of_trivial d.one_le (d.leA ha.1) ha.2.2.2)
  have hAsup : A ⊔ C₀ = A ⊔ B := by
    refine le_antisymm (sup_le le_sup_left hC₀AB) (sup_le le_sup_left ?_)
    intro b' hb'
    obtain ⟨a, ha, c, hc, rfl⟩ :=
      d.exists_mul_mem_cenSection h.toHyp42 hV (Subgroup.mem_sup_right hb')
    exact Subgroup.mul_mem_sup ha hc
  have hinf : A ⊓ B = ⊥ := (h.toHyp41.eq_or_inf_eq_bot hA.1 hB.1).resolve_left hne
  have hcardAB : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
    have := card_sup_mul_card_inf' (X := A) (Y := B) hcomm
    rwa [hinf, Subgroup.card_bot, mul_one] at this
  have hcommAC : ∀ a ∈ A, ∀ c ∈ C₀, a * c = c * a := fun a ha c hc =>
    hABab.1 a (Subgroup.mem_sup_left ha) c (hC₀AB hc)
  have hcardC₀ : Nat.card ↥C₀ = 2 ^ n := by
    have h1 := card_sup_mul_card_inf' (X := A) (Y := C₀) hcommAC
    rw [hAsup, hAC, Subgroup.card_bot, mul_one, hcardAB] at h1
    have h2 : Nat.card B = Nat.card ↥C₀ := Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    rw [← h2]
    exact d.card_B
  have hKC : kerW L B = C₀ :=
    (Subgroup.eq_of_le_of_card_ge hC₀K
      ((d.card_kerW_le h hV hAT hBT hLM).trans hcardC₀.ge)).symm
  have hKAB : kerW L B ≤ A ⊔ B := by
    rw [hKC]
    exact hC₀AB
  have hKL : ∀ k ∈ kerW L B, ∀ x ∈ L, k * x = x * k := by
    intro k hk
    obtain ⟨D', hD', hD'ne⟩ := d.sl.exists_sylow_ne d.one_le hAsyl
    obtain ⟨x, hxL, hD'x⟩ := IsSLNatSection.sylow_conj hAsyl hD'
    have hsup : A ⊔ D' = L := d.sl.sylow_sup_eq d.one_le hAsyl hD' hD'ne.symm
    have hkA : ∀ a ∈ A, k * a = a * k := fun a ha =>
      hABab.1 k (hKAB hk) a (Subgroup.mem_sup_left ha)
    have hkD' : ∀ y ∈ D', k * y = y * k := by
      intro y hy
      rw [hD'x] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      have hk' : x⁻¹ * k * x ∈ kerW L B := by
        have := d.kerW_normal (g := x⁻¹) ((L ⊔ B).inv_mem (Subgroup.mem_sup_left hxL)) hk
        rwa [inv_inv] at this
      have h2 := hABab.1 _ (hKAB hk') a (Subgroup.mem_sup_left ha)
      show k * (x * a * x⁻¹) = x * a * x⁻¹ * k
      calc k * (x * a * x⁻¹) = x * ((x⁻¹ * k * x) * a) * x⁻¹ := by group
        _ = x * (a * (x⁻¹ * k * x)) * x⁻¹ := by rw [h2]
        _ = x * a * x⁻¹ * k := by group
    have hle : A ⊔ D' ≤ Subgroup.centralizer ({k} : Set (MulAut V)) :=
      sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun z hz => by
          rw [Set.mem_singleton_iff.1 hz]
          exact hkA a ha)
        (fun y hy => Subgroup.mem_centralizer_iff.2 fun z hz => by
          rw [Set.mem_singleton_iff.1 hz]
          exact hkD' y hy)
    intro x' hx'
    rw [← hsup] at hx'
    exact Subgroup.mem_centralizer_iff.1 (hle hx') k (Set.mem_singleton k)
  have hB4 : ∀ b ∈ B, ∀ v : V, b v * v⁻¹ ∈ fixV (L ⊔ B) := by
    intro b hb v
    obtain ⟨a, ha, c, hc, hbac⟩ :=
      d.exists_mul_mem_cenSection h.toHyp42 hV (Subgroup.mem_sup_right hb)
    have hcK : c ∈ kerW L B := hC₀K hc
    have hv : v ∈ fixV A ⊔ fixV B := by
      rw [(four_six d.hyp d.memA d.memB d.ne d.comm).1]
      exact Subgroup.mem_top v
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [d.sl.fixV_sylow_eq d.one_le d.sylowGood hAsyl] at hv₁
    obtain ⟨u, hu, f, hf, rfl⟩ := Subgroup.mem_sup.1 hv₁
    have hub : b u = u := fixV_anti (le_sup_right : B ≤ A ⊔ B) (d.commV_A_le hu) b hb
    have hbv₂ : b v₂ = v₂ := hv₂ b hb
    have e1 : b (u * f * v₂) * (u * f * v₂)⁻¹ = b f * f⁻¹ := by
      rw [map_mul, map_mul, hub, hbv₂]
      comm_group
    rw [e1]
    have hcf : c f ∈ fixV L := by
      intro l' hl'
      calc l' (c f) = (l' * c) f := rfl
        _ = (c * l') f := by rw [← hKL c hcK l' hl']
        _ = c (l' f) := rfl
        _ = c f := by rw [hf l' hl']
    have hbf : b f = c f := by
      rw [hbac, MulAut.mul_apply]
      exact hcf a (d.leA ha)
    rw [hbf, ← d.inf_fixV_eq]
    exact Subgroup.mem_inf.2 ⟨d.commV_kerW_le (G6.mem_commV_of_mem hcK f),
      mul_mem hcf (inv_mem hf)⟩
  have hcB : commV B ≤ fixV (L ⊔ B) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, v, rfl⟩
    exact hB4 x hx v
  have hX : fixV (A ⊔ B) ≤ fixV (L ⊔ B) := by
    rw [← d.commV_B_sup_eq]
    exact sup_le hcB le_rfl
  have hle := Subgroup.card_le_of_le hX
  rw [← d.commV_sup_eq, d.card_commV_sup] at hle
  have hpos : 0 < Nat.card ↥(fixV (L ⊔ B)) := Nat.card_pos
  have h3 : 2 ^ n * Nat.card ↥(fixV (L ⊔ B)) ≤ 1 * Nat.card ↥(fixV (L ⊔ B)) := by
    rwa [one_mul]
  have h4 := Nat.le_of_mul_le_mul_right h3 hpos
  have h5 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  omega

end CFSG.CGT.PushingUpLit.BHS
