module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012NFModel
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Fus3
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012NFOuter

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound

section Outer

variable {Y : Type} [Group Y]

@[expose] def OuterOK (L : Subgroup Y) (t : Y) (r : ℕ) : Prop :=
  ∃ (ht : t ∈ normalizer (L : Set Y)), t * t = 1 ∧
    (¬ ∃ a ∈ L, ∀ k ∈ L, t * k * t⁻¹ = a * k * a⁻¹) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
      (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F),
      Nat.card F = r ∧ (gammaOf hodd h3 (MulAut.congr e (conjAut L t ht))).right = 1

theorem OuterOK.cyclic_card {L : Subgroup Y} {t : Y} {r : ℕ} (h : OuterOK L t r) :
    IsCyclic ↥(L ⊓ centralizer ({t} : Set Y)) ∧
      Nat.card ↥(L ⊓ centralizer ({t} : Set Y)) = if r % 4 = 1 then r + 1 else r - 1 := by
  obtain ⟨ht, ht2, hout, F, _, _, e, hodd, h3, hFr, hfld⟩ := h
  have := outer_inf_cyclic e hodd h3 ht ht2 hout hfld
  rw [hFr] at this
  exact this

theorem OuterOK.fit [Finite Y] {L : Subgroup Y} {t : Y} {r : ℕ} (h : OuterOK L t r) (M : Subgroup Y)
    (hMN : M ≤ normalizer (L : Set Y)) (hMt : ∀ m ∈ M, m * t = t * m) (W : Subgroup Y) (hWM : W ≤ M)
    (hWodd : Odd (Nat.card ↥W)) (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hX : ∀ k ∈ L, Odd (orderOf k) → k * t = t * k →
      ∃ m ∈ M, (∀ x ∈ L, m * x * m⁻¹ = k * x * k⁻¹) ∧ ∀ w ∈ W, m * w * m⁻¹ ∈ W) :
    ∀ w ∈ W, ∃ k ∈ L, Odd (orderOf k) ∧ k * t = t * k ∧ ∀ x ∈ L, w * x * w⁻¹ = k * x * k⁻¹ := by
  obtain ⟨ht, ht2, hout, F, _, _, e, hodd, h3, hFr, hfld⟩ := h
  exact fit_G_outer hodd h3 e ht ht2 hout hfld M hMN hMt W hWM hWodd hWab hX

theorem outerOK_of_pgl [Finite Y] {L : Subgroup Y} {t : Y} {r : ℕ} (hodd : Odd r) (hr3 : 3 < r)
    (hsl : HasSL2Model ↥L (fun q => q = r)) (ht : t ∈ normalizer (L : Set Y)) (ht2 : t * t = 1)
    (hpgl : PGLOver L (zpowers t) r) : OuterOK L t r := by
  obtain ⟨hn, hPGL⟩ := hpgl
  obtain ⟨F, hF, hFin, hFr, ⟨e₀⟩⟩ := hsl
  have hFr' : Nat.card F = r := hFr
  let e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F := e₀.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hodd' : Odd (Nat.card F) := hFr' ▸ hodd
  have h3' : 3 < Nat.card F := hFr' ▸ hr3
  have hcen2 : Nat.card ↥(center ↥L) = 2 := (sl2_model_center_inv hodd ⟨F, hF, hFin, hFr, ⟨e₀⟩⟩).1
  have hnt : Nontrivial ↥(center ↥L) := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcen2]; norm_num)
  obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(center ↥L))
  have hcsq : c * c = 1 := by
    have h1 : orderOf c ∣ Nat.card ↥(center ↥L) := orderOf_dvd_natCard c
    rw [hcen2] at h1
    have := orderOf_dvd_iff_pow_eq_one.1 h1
    simpa [sq] using this
  set cY : Y := ((c : ↥L) : Y) with hcY
  have hcL : cY ∈ L := (c : ↥L).2
  have hcc : ∀ a ∈ L, a * cY = cY * a := fun a ha => by
    have := Subgroup.mem_center_iff.1 c.2 ⟨a, ha⟩
    exact congrArg Subtype.val this
  have hc1Y : cY ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  have hZ : (center ↥L).map L.subtype = zpowers cY := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (⟨y, hy⟩ : ↥(center ↥L)) = 1 ∨ (⟨y, hy⟩ : ↥(center ↥L)) = c := by
        have h2 := Nat.card_eq_two_iff' (1 : ↥(center ↥L)) |>.1 hcen2
        obtain ⟨u, -, hu⟩ := h2
        have e1 := hu c hc1
        by_cases hy1 : (⟨y, hy⟩ : ↥(center ↥L)) = 1
        · exact Or.inl hy1
        · exact Or.inr ((hu _ hy1).trans e1.symm)
      rcases hy' with h | h
      · have hyy : y = 1 := congrArg Subtype.val h
        rw [hyy, map_one]; exact one_mem _
      · have hyc : y = (c : ↥L) := congrArg Subtype.val h
        rw [hyc]
        exact mem_zpowers cY
    · intro hx
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
      exact (center ↥L).map L.subtype |>.zpow_mem ⟨c, c.2, rfl⟩ n
  have hn₂ : ((zpowers cY).subgroupOf (L ⊔ zpowers t)).Normal := hZ ▸ hn
  have hPGL₂ : IsPGL2 (↥(L ⊔ zpowers t) ⧸ (zpowers cY).subgroupOf (L ⊔ zpowers t))
      (fun r' => r' = Nat.card F) := by
    obtain ⟨F₀, hF₀, hFin₀, hF₀r, ⟨e₁⟩⟩ := hPGL
    refine ⟨F₀, hF₀, hFin₀, by rw [hFr']; exact hF₀r, ⟨?_⟩⟩
    exact (QuotientGroup.quotientMulEquivOfEq (by rw [hZ])).trans e₁
  have := outer_of_pgl e hodd' h3' ht ht2 hcL hcc hc1Y hn₂ hPGL₂
  exact ⟨ht, ht2, this.1, F, hF, hFin, e, hodd', h3', hFr', this.2⟩

omit [Group Y] in
theorem eq_one_of_sq_odd_nf {X : Type} [Group X] {y : X} (h2 : y * y = 1) (hodd : Odd (orderOf y)) : y = 1 := by
  have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  have h3 : Odd (orderOf y) := hodd
  have : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · rw [h] at h3; exact absurd h3 (by decide)
  exact orderOf_eq_one_iff.1 this

end Outer

section Pairs

open CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

variable {Y : Type} [Group Y] [Finite Y] {L₁ L₂ : Subgroup Y} {r : ℕ}

omit [Finite Y] in
theorem exists_inv_a {t : Y} (hO : OuterOK L₁ t r) (hp : Pair L₁ L₂ r r) {z₀ : Y} (hz₀ : z₀ ∈ L₁ ⊓ L₂)
    (hz₀1 : z₀ ≠ 1) : ∃ a ∈ L₁, a * a = z₀ ∧ t * a * t⁻¹ = a⁻¹ := by
  obtain ⟨ht, ht2, hout, F, hF, hFin, e, hodd, h3, hFr, hfld⟩ := hO
  set α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) := MulAut.congr e (conjAut L₁ t ht) with hα
  have hα2 : α * α = 1 := by
    rw [hα, ← map_mul, conjAut_mul_self ht ht2, map_one]
  have hα1 : α ≠ 1 := by
    intro h
    apply hout
    refine ⟨1, L₁.one_mem, fun k hk => ?_⟩
    have h1 : conjAut L₁ t ht = 1 := by
      apply (MulAut.congr e).injective
      rw [← hα, h, map_one]
    have := congrArg (fun ψ => ((ψ ⟨k, hk⟩ : ↥L₁) : Y)) h1
    simpa [conjAut_apply] using this
  obtain ⟨x, hx2, hxα⟩ := CFSG.GH74.GLS.IVK.exists_inverted_sl hodd h3 α hα2 hα1
  have hodd_r : Odd r := hFr ▸ hodd
  have hF2 : ringChar F ≠ 2 := CFSG.GH74.GLS.SP.Local.ringChar_ne_two ⟨hodd, h3⟩
  have hneg : (-1 : Matrix (Fin 2) (Fin 2) F) ≠ 1 := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp only [Matrix.neg_apply, Matrix.one_apply_eq] at this
    exact Ring.neg_one_ne_one_of_char_ne_two hF2 this
  have hxx1 : (x * x : Matrix.SpecialLinearGroup (Fin 2) F) * (x * x) = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    rw [← mul_assoc, mul_assoc (x : Matrix (Fin 2) (Fin 2) F) x x, hx2]
    simp [hx2]
  set a : ↥L₁ := e.symm x with ha
  have hu1 : (a * a) * (a * a) = 1 := by
    apply e.injective
    simp only [map_mul, ha, MulEquiv.apply_symm_apply, map_one]
    exact hxx1
  have hu2 : a * a ≠ 1 := by
    intro h
    have h1 : x * x = 1 := by
      have := congrArg e h
      simpa [map_mul, ha] using this
    have hm := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 2) F => (y : Matrix (Fin 2) (Fin 2) F)) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at hm
    rw [hx2] at hm
    exact hneg hm
  have hsl : HasSL2Model ↥L₁ (fun q => q = r) :=
    ⟨F, hF, hFin, hFr, ⟨e.trans (specialLinearGroupEquivStatedSL 2 F)⟩⟩
  obtain ⟨-, huniq⟩ := sl2_model_center_inv hodd_r hsl
  have hord : ∀ u : Y, u * u = 1 → u ≠ 1 → orderOf u = 2 := fun u hu hu1 =>
    orderOf_eq_prime (by rw [← sq] at hu; exact hu) hu1
  refine ⟨(a : Y), a.2, ?_, ?_⟩
  · have hz02 : z₀ * z₀ = 1 := hp.sq_of_mem_inf hz₀
    have hA1 : ((a : Y) * (a : Y)) * ((a : Y) * (a : Y)) = 1 := congrArg Subtype.val hu1
    have hA2 : (a : Y) * (a : Y) ≠ 1 := fun h => hu2 (Subtype.ext h)
    exact huniq _ (L₁.mul_mem a.2 a.2) _ hz₀.1 (hord _ hA1 hA2) (hord _ hz02 hz₀1)
  · have h1 : conjAut L₁ t ht a = a⁻¹ := by
      apply e.injective
      have := hxα
      rw [hα] at this
      simpa [MulAut.congr_apply, ha] using this
    have := congrArg (fun y : ↥L₁ => (y : Y)) h1
    simpa [conjAut_apply] using this

omit [Finite Y] in
theorem card_inf_centralizer_sq (hp : Pair L₁ L₂ r r) {z₀ : Y} (hz₀ : z₀ ∈ L₁ ⊓ L₂) (hz₀1 : z₀ ≠ 1) {a : Y}
    (ha : a ∈ L₁) (haz : a * a = z₀) :
    Nat.card ↥(L₁ ⊓ centralizer ({a} : Set Y)) = if r % 4 = 1 then r - 1 else r + 1 := by
  obtain ⟨F, hF, hFin, hFr, ⟨e₀⟩⟩ := hp.hm
  have hFr' : Nat.card F = r := hFr
  let e : ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F := e₀.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hodd : Odd (Nat.card F) := hFr' ▸ hp.odd
  have hz₀c : ∀ k ∈ L₁, k * z₀ = z₀ * k := fun k hk => hp.comm k hk z₀ hz₀.2
  have ha2c : (⟨a, ha⟩ : ↥L₁) * ⟨a, ha⟩ ∈ center ↥L₁ := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    show (k : Y) * (a * a) = (a * a) * k
    rw [haz]
    exact hz₀c k k.2
  have hac : (⟨a, ha⟩ : ↥L₁) ∉ center ↥L₁ := by
    intro hc
    have hc' : ∀ c ∈ L₁, c * a = a * c := fun c hc'' => by
      have := Subgroup.mem_center_iff.1 hc ⟨c, hc''⟩
      exact congrArg Subtype.val this
    have ha2 : a ∈ L₂ := hp.cen ha hc'
    have : a * a = 1 := hp.sq_of_mem_inf ⟨ha, ha2⟩
    rw [haz] at this
    exact hz₀1 this
  have hmap : (centralizer ({(⟨a, ha⟩ : ↥L₁)} : Set ↥L₁)).map L₁.subtype =
      L₁ ⊓ centralizer ({a} : Set Y) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k.2, ?_⟩
      have hk' : k ∈ centralizer ({(⟨a, ha⟩ : ↥L₁)} : Set ↥L₁) := hk
      rw [Subgroup.mem_centralizer_singleton_iff] at hk'
      show (k : Y) ∈ centralizer ({a} : Set Y)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hk'
    · rintro ⟨hxL, hxc⟩
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      have hxc' : x ∈ centralizer ({a} : Set Y) := hxc
      rw [Subgroup.mem_centralizer_singleton_iff] at hxc'
      show (⟨x, hxL⟩ : ↥L₁) ∈ centralizer ({(⟨a, ha⟩ : ↥L₁)} : Set ↥L₁)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hxc'
  rw [← hmap, Subgroup.card_map_of_injective L₁.subtype_injective,
    card_centralizer_of_sq_mem_center e hodd ha2c hac, hFr']

theorem B_act {L : Subgroup Y} {t : Y} (hO : OuterOK L t r) {B : Subgroup Y}
    (hBodd : ∀ b ∈ B, Odd (orderOf b)) (hBN : ∀ b ∈ B, b ∈ normalizer (L : Set Y))
    (hBt : ∀ b ∈ B, b * t = t * b) (hBn : ∀ c : Y, c * t = t * c → ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hBL : ∀ b ∈ B, b ∈ L → b = 1) :
    ∀ b ∈ B, ∃ k ∈ L, Odd (orderOf k) ∧ k * t = t * k ∧ ∀ x ∈ L, b * x * b⁻¹ = k * x * k⁻¹ := by
  intro b hb
  set M : Subgroup Y := normalizer (L : Set Y) ⊓ centralizer ({t} : Set Y) with hM
  have hbM : b ∈ M := ⟨hBN b hb, Subgroup.mem_centralizer_singleton_iff.2 (hBt b hb)⟩
  have hWM : zpowers b ≤ M := zpowers_le.2 hbM
  have hWodd : Odd (Nat.card ↥(zpowers b)) := by rw [Nat.card_zpowers]; exact hBodd b hb
  have hWab : ∀ x ∈ zpowers b, ∀ y ∈ zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self b m n).eq
  have hmain := hO.fit M inf_le_left (fun m hm => Subgroup.mem_centralizer_singleton_iff.1 hm.2)
    (zpowers b) hWM hWodd hWab (by
      intro k hk hkodd hkt
      have hkM : k ∈ M := ⟨Subgroup.le_normalizer hk, Subgroup.mem_centralizer_singleton_iff.2 hkt⟩
      refine ⟨k, hkM, fun x _ => rfl, ?_⟩
      have hcomm : k * b = b * k := by
        have h1 : k * b * k⁻¹ ∈ B := hBn k hkt b hb
        have h2 : k * b * k⁻¹ * b⁻¹ ∈ B := B.mul_mem h1 (B.inv_mem hb)
        have h3 : k * b * k⁻¹ * b⁻¹ ∈ L := by
          have hbk : b * k⁻¹ * b⁻¹ ∈ L := by
            have := (Subgroup.mem_normalizer_iff.1 (hBN b hb) k⁻¹).1 (L.inv_mem hk)
            exact this
          have := L.mul_mem hk hbk
          simpa [mul_assoc] using this
        have h4 := hBL _ h2 h3
        calc k * b = (k * b * k⁻¹ * b⁻¹) * b * k := by group
          _ = b * k := by rw [h4]; group
      intro w hw
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
      have : k * b ^ n * k⁻¹ = b ^ n := by
        rw [(Commute.zpow_right (show Commute k b from hcomm) n).eq]; group
      rw [this]
      exact mem_zpowers_iff.2 ⟨n, rfl⟩) b (mem_zpowers b)
  exact hmain

omit [Finite Y] in
theorem odd_eq_one_of_cent (hp : Pair L₁ L₂ r r) {z₀ : Y} (hz₀ : z₀ ∈ L₁ ⊓ L₂) (hz₀1 : z₀ ≠ 1) {t : Y}
    (hO : OuterOK L₁ t r) {a : Y} (ha : a ∈ L₁) (haz : a * a = z₀) {k : Y} (hk : k ∈ L₁)
    (hkodd : Odd (orderOf k)) (hka : k * a = a * k) (hkt : k * t = t * k) : k = 1 := by
  have h1 := card_inf_centralizer_sq hp hz₀ hz₀1 ha haz
  obtain ⟨-, h2⟩ := hO.cyclic_card
  have hk1 : k ∈ L₁ ⊓ centralizer ({a} : Set Y) := ⟨hk, Subgroup.mem_centralizer_singleton_iff.2 hka⟩
  have hk2 : k ∈ L₁ ⊓ centralizer ({t} : Set Y) := ⟨hk, Subgroup.mem_centralizer_singleton_iff.2 hkt⟩
  have d1 : orderOf k ∣ Nat.card ↥(L₁ ⊓ centralizer ({a} : Set Y)) := by
    have := Subgroup.orderOf_dvd_natCard _ hk1
    simpa using this
  have d2 : orderOf k ∣ Nat.card ↥(L₁ ⊓ centralizer ({t} : Set Y)) := by
    have := Subgroup.orderOf_dvd_natCard _ hk2
    simpa using this
  rw [h1] at d1
  rw [h2] at d2
  have hr3 := hp.gt
  have hd : orderOf k ∣ 2 := by
    by_cases h4 : r % 4 = 1
    · simp only [h4, ↓reduceIte] at d1 d2
      have := Nat.dvd_sub d2 d1
      have e : r + 1 - (r - 1) = 2 := by omega
      rwa [e] at this
    · simp only [h4, ↓reduceIte] at d1 d2
      have := Nat.dvd_sub d1 d2
      have e : r + 1 - (r - 1) = 2 := by omega
      rwa [e] at this
  have h3 : Odd (orderOf k) := hkodd
  have : orderOf k = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact h
    · rw [h] at h3; exact absurd h3 (by decide)
  exact orderOf_eq_one_iff.1 this

theorem yo_embed (hp : Pair L₁ L₂ r r) (hp' : Pair L₂ L₁ r r)
    (hC : ∀ x : Y, (∀ y ∈ L₁ ⊔ L₂, x * y = y * x) → x ∈ L₁ ⊔ L₂) {t : Y} (hO : OuterOK L₁ t r)
    {B : Subgroup Y} (hBodd : ∀ b ∈ B, Odd (orderOf b)) (hBN : ∀ b ∈ B, b ∈ normalizer (L₁ : Set Y))
    (hBt : ∀ b ∈ B, b * t = t * b) (hBn : ∀ c : Y, c * t = t * c → ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    {e : Y} (he₁ : ∀ a ∈ L₁, e * a * e⁻¹ ∈ L₂) (he₂ : ∀ a ∈ L₂, e * a * e⁻¹ ∈ L₁)
    (hec : ∀ b ∈ B, e * b = b * e) :
    ∃ φ : ↥B →* ↥(pPrimeCoreOf 2 (L₁ ⊓ centralizer ({t} : Set Y))), Function.Injective φ := by
  have hBL : ∀ b ∈ B, b ∈ L₁ → b = 1 := by
    intro b hb hbL
    have hbe : e * b * e⁻¹ = b := by rw [hec b hb]; group
    have hb₂ : b ∈ L₂ := by
      have := he₁ b hbL
      rwa [hbe] at this
    exact eq_one_of_sq_odd_nf (hp.sq_of_mem_inf ⟨hbL, hb₂⟩) (hBodd b hb)
  have hact := B_act hO hBodd hBN hBt hBn hBL
  obtain ⟨hcyc, -⟩ := hO.cyclic_card
  set T : Subgroup Y := L₁ ⊓ centralizer ({t} : Set Y) with hT
  set X : Subgroup Y := pPrimeCoreOf 2 T with hX
  have hXT : X ≤ T := Subgroup.map_subtype_le _
  have hXK : X ≤ L₁ := fun x hx => (hXT hx).1
  have hXodd : ∀ x ∈ X, Odd (orderOf x) := fun x hx => CFSG.GH74.GLS.Stage2.Final.Thm6.L20.odd_orderOf_of_mem_pPrimeCoreOf (F := T) hx
  refine exists_inj_hom hXK ?_ ?_ ?_
  · intro k hk hc
    have hkL : k ∈ L₁ := hXK hk
    have hk2 : k ∈ L₂ := hp.cen hkL (fun c hc' => (hc c hc').symm)
    exact eq_one_of_sq_odd_nf (hp.sq_of_mem_inf ⟨hkL, hk2⟩) (hXodd k hk)
  · intro b hb
    obtain ⟨k, hkL, hkodd, hkt, hkact⟩ := hact b hb
    exact ⟨k, odd_mem_pPrimeCoreOf hcyc ⟨hkL, Subgroup.mem_centralizer_singleton_iff.2 hkt⟩ hkodd, hkact⟩
  · intro b hb hcen
    have hbe : e⁻¹ * b * e = b := by
      calc e⁻¹ * b * e = e⁻¹ * (b * e) := by group
        _ = e⁻¹ * (e * b) := by rw [hec b hb]
        _ = b := by group
    have hc2 : ∀ y ∈ L₂, b * y = y * b := by
      intro y hy
      have h1 := hcen _ (he₂ y hy)
      calc b * y = (e⁻¹ * b * e) * (e⁻¹ * (e * y * e⁻¹) * e) := by rw [hbe]; group
        _ = e⁻¹ * (b * (e * y * e⁻¹)) * e := by group
        _ = e⁻¹ * ((e * y * e⁻¹) * b) * e := by rw [h1]
        _ = (e⁻¹ * (e * y * e⁻¹) * e) * (e⁻¹ * b * e) := by group
        _ = y * b := by rw [hbe]; group
    have hbS : b ∈ L₁ ⊔ L₂ := by
      apply hC
      intro y hy
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hp.exists_mul hy
      calc b * (a₁ * a₂) = (b * a₁) * a₂ := by group
        _ = (a₁ * b) * a₂ := by rw [hcen a₁ ha₁]
        _ = a₁ * (b * a₂) := by group
        _ = a₁ * (a₂ * b) := by rw [hc2 a₂ ha₂]
        _ = (a₁ * a₂) * b := by group
    have hbL₁ : b ∈ L₁ := hp'.mem_of_cen (by rwa [sup_comm] at hbS) hc2
    exact hBL b hb hbL₁

theorem yo_noL (hp : Pair L₁ L₂ r r) (hp' : Pair L₂ L₁ r r)
    (hC : ∀ x : Y, (∀ y ∈ L₁ ⊔ L₂, x * y = y * x) → x ∈ L₁ ⊔ L₂)
    {z₀ : Y} (hz₀ : z₀ ∈ L₁ ⊓ L₂) (hz₀1 : z₀ ≠ 1) (hz₀c : ∀ y : Y, y * z₀ = z₀ * y) {t : Y}
    (hO₁ : OuterOK L₁ t r) (hO₂ : OuterOK L₂ t r) {B : Subgroup Y}
    (hBodd : ∀ b ∈ B, Odd (orderOf b)) (hB₁ : ∀ b ∈ B, b ∈ normalizer (L₁ : Set Y))
    (hB₂ : ∀ b ∈ B, b ∈ normalizer (L₂ : Set Y)) (hBt : ∀ b ∈ B, b * t = t * b)
    (hBn : ∀ c : Y, c * t = t * c → ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    {e : Y} (he2 : e * e = 1) (heL : e ∈ L₁ ⊔ L₂) (he0 : e ∉ L₁ ⊓ L₂)
    (hec : ∀ b ∈ B, e * b = b * e) : ∀ b ∈ B, b = 1 := by
  have hz₀' : z₀ ∈ L₂ ⊓ L₁ := by rw [inf_comm]; exact hz₀
  obtain ⟨a₁, ha₁, a₂, ha₂, hea⟩ := hp.exists_mul heL
  have hc12 : a₁ * a₂ = a₂ * a₁ := hp.comm a₁ ha₁ a₂ ha₂
  have hprod : (a₁ * a₁) * (a₂ * a₂) = 1 := by
    calc (a₁ * a₁) * (a₂ * a₂) = a₁ * (a₁ * a₂) * a₂ := by group
      _ = a₁ * (a₂ * a₁) * a₂ := by rw [hc12]
      _ = (a₁ * a₂) * (a₁ * a₂) := by group
      _ = 1 := by rw [← hea]; exact he2
  have hI : a₁ * a₁ ∈ L₁ ⊓ L₂ := by
    refine ⟨L₁.mul_mem ha₁ ha₁, ?_⟩
    have : a₁ * a₁ = (a₂ * a₂)⁻¹ := eq_inv_of_mul_eq_one_left hprod
    rw [this]
    exact L₂.inv_mem (L₂.mul_mem ha₂ ha₂)
  have hsq : a₁ * a₁ = a₂ * a₂ := by
    have h1 := hp.sq_of_mem_inf hI
    have : a₂ * a₂ = (a₁ * a₁)⁻¹ := eq_inv_of_mul_eq_one_right hprod
    rw [this]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have hcases : ∀ x ∈ L₁ ⊓ L₂, x = 1 ∨ x = z₀ := fun x hx => hp.inf_cases hz₀ hz₀1 hx
  have ha₁2 : a₁ * a₁ ≠ 1 := by
    intro h1
    have h2 : a₂ * a₂ = 1 := by rw [← hsq]; exact h1
    have h3 : a₂ ∈ L₁ ⊓ L₂ := hp.mem_inf_of_sq ha₂ h2
    have h4 : a₁ ∈ L₂ ⊓ L₁ := hp'.mem_inf_of_sq ha₁ h1
    rw [inf_comm] at h4
    exact he0 (hea ▸ (L₁ ⊓ L₂).mul_mem h4 h3)
  have ha₁z : a₁ * a₁ = z₀ := (hcases _ hI).resolve_left ha₁2
  have ha₂z : a₂ * a₂ = z₀ := hsq.symm.trans ha₁z
  have hodd_pow : ∀ (b : Y) (u : Y), Odd (orderOf b) → b * u * b⁻¹ = u * z₀ → False := by
    intro b u hbo hbu
    have hpow : ∀ k : ℕ, b ^ k * u * (b ^ k)⁻¹ = u * z₀ ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc b ^ (k + 1) * u * (b ^ (k + 1))⁻¹ = b * (b ^ k * u * (b ^ k)⁻¹) * b⁻¹ := by
              rw [pow_succ', mul_inv_rev]; group
          _ = b * (u * z₀ ^ k) * b⁻¹ := by rw [ih]
          _ = (b * u * b⁻¹) * (b * z₀ ^ k * b⁻¹) := by group
          _ = (u * z₀) * z₀ ^ k := by
              rw [hbu]
              congr 1
              rw [(Commute.pow_right (hz₀c b : Commute b z₀) k).eq]; group
          _ = u * z₀ ^ (k + 1) := by rw [pow_succ']; group
    have h1 := hpow (orderOf b)
    rw [pow_orderOf_eq_one] at h1
    simp only [inv_one, mul_one, one_mul] at h1
    have hz2 : z₀ * z₀ = 1 := hp.sq_of_mem_inf hz₀
    obtain ⟨m, hm⟩ := hbo
    have : z₀ ^ orderOf b = z₀ := by
      rw [hm, pow_succ, pow_mul, show z₀ ^ 2 = 1 by rw [pow_two]; exact hz2, one_pow, one_mul]
    rw [this] at h1
    have h3 : u = u * z₀ := h1
    exact hz₀1 (by simpa using h3)
  have hBa : ∀ b ∈ B, b * a₁ = a₁ * b ∧ b * a₂ = a₂ * b := by
    intro b hb
    have hbe : b * e * b⁻¹ = e := by
      have := hec b hb
      calc b * e * b⁻¹ = (e * b) * b⁻¹ := by rw [this]
        _ = e := by group
    set u := b * a₁ * b⁻¹ with hu
    set v := b * a₂ * b⁻¹ with hv
    have hu₁ : u ∈ L₁ := (Subgroup.mem_normalizer_iff.1 (hB₁ b hb) a₁).1 ha₁
    have hv₂ : v ∈ L₂ := (Subgroup.mem_normalizer_iff.1 (hB₂ b hb) a₂).1 ha₂
    have huv : u * v = a₁ * a₂ := by
      calc u * v = b * (a₁ * a₂) * b⁻¹ := by simp only [hu, hv]; group
        _ = a₁ * a₂ := by rw [← hea]; exact hbe
    have hk : a₁⁻¹ * u = a₂ * v⁻¹ := by
      calc a₁⁻¹ * u = a₁⁻¹ * (u * v) * v⁻¹ := by group
        _ = a₁⁻¹ * (a₁ * a₂) * v⁻¹ := by rw [huv]
        _ = a₂ * v⁻¹ := by group
    have hkI : a₁⁻¹ * u ∈ L₁ ⊓ L₂ :=
      ⟨L₁.mul_mem (L₁.inv_mem ha₁) hu₁, hk ▸ L₂.mul_mem ha₂ (L₂.inv_mem hv₂)⟩
    rcases hcases _ hkI with h1 | h1
    · have hu1 : u = a₁ := by
        have h1' : a₁⁻¹ * u = 1 := h1
        calc u = a₁ * (a₁⁻¹ * u) := by group
          _ = a₁ := by rw [h1']; group
      have hv1 : v = a₂ := by
        have h1' : a₂ * v⁻¹ = 1 := hk ▸ h1
        calc v = (a₂ * v⁻¹)⁻¹ * a₂ := by group
          _ = a₂ := by rw [h1']; group
      constructor
      · calc b * a₁ = u * b := by simp only [hu]; group
          _ = a₁ * b := by rw [hu1]
      · calc b * a₂ = v * b := by simp only [hv]; group
          _ = a₂ * b := by rw [hv1]
    · exfalso
      refine hodd_pow b a₁ (hBodd b hb) ?_
      have h1' : a₁⁻¹ * u = z₀ := h1
      calc b * a₁ * b⁻¹ = u := rfl
        _ = a₁ * (a₁⁻¹ * u) := by group
        _ = a₁ * z₀ := by rw [h1']
  have hBL₁ : ∀ b ∈ B, b ∈ L₁ → b = 1 := fun b hb hbL =>
    odd_eq_one_of_cent hp hz₀ hz₀1 hO₁ ha₁ ha₁z hbL (hBodd b hb) (hBa b hb).1 (hBt b hb)
  have hBL₂ : ∀ b ∈ B, b ∈ L₂ → b = 1 := fun b hb hbL =>
    odd_eq_one_of_cent hp' hz₀' hz₀1 hO₂ ha₂ ha₂z hbL (hBodd b hb) (hBa b hb).2 (hBt b hb)
  have hact₁ := B_act hO₁ hBodd hB₁ hBt hBn hBL₁
  have hact₂ := B_act hO₂ hBodd hB₂ hBt hBn hBL₂
  intro b hb
  have hc₁ : ∀ x ∈ L₁, b * x = x * b := by
    obtain ⟨k, hkL, hkodd, hkt, hkact⟩ := hact₁ b hb
    have hka : k * a₁ = a₁ * k := by
      have h1 := hkact a₁ ha₁
      have h2 : b * a₁ * b⁻¹ = a₁ := by rw [(hBa b hb).1]; group
      rw [h2] at h1
      calc k * a₁ = (k * a₁ * k⁻¹) * k := by group
        _ = a₁ * k := by rw [← h1]
    have hk1 : k = 1 := odd_eq_one_of_cent hp hz₀ hz₀1 hO₁ ha₁ ha₁z hkL hkodd hka hkt
    intro x hx
    have h1 := hkact x hx
    rw [hk1] at h1
    simp only [one_mul, inv_one, mul_one] at h1
    calc b * x = (b * x * b⁻¹) * b := by group
      _ = x * b := by rw [h1]
  have hc₂ : ∀ y ∈ L₂, b * y = y * b := by
    obtain ⟨k, hkL, hkodd, hkt, hkact⟩ := hact₂ b hb
    have hka : k * a₂ = a₂ * k := by
      have h1 := hkact a₂ ha₂
      have h2 : b * a₂ * b⁻¹ = a₂ := by rw [(hBa b hb).2]; group
      rw [h2] at h1
      calc k * a₂ = (k * a₂ * k⁻¹) * k := by group
        _ = a₂ * k := by rw [← h1]
    have hk1 : k = 1 := odd_eq_one_of_cent hp' hz₀' hz₀1 hO₂ ha₂ ha₂z hkL hkodd hka hkt
    intro x hx
    have h1 := hkact x hx
    rw [hk1] at h1
    simp only [one_mul, inv_one, mul_one] at h1
    calc b * x = (b * x * b⁻¹) * b := by group
      _ = x * b := by rw [h1]
  have hbS : b ∈ L₁ ⊔ L₂ := by
    apply hC
    intro y hy
    obtain ⟨c₁, hc₁', c₂, hc₂', rfl⟩ := hp.exists_mul hy
    calc b * (c₁ * c₂) = (b * c₁) * c₂ := by group
      _ = (c₁ * b) * c₂ := by rw [hc₁ c₁ hc₁']
      _ = c₁ * (b * c₂) := by group
      _ = c₁ * (c₂ * b) := by rw [hc₂ c₂ hc₂']
      _ = (c₁ * c₂) * b := by group
  have hbL₁ : b ∈ L₁ := hp'.mem_of_cen (by rwa [sup_comm] at hbS) hc₂
  exact hBL₁ b hb hbL₁

end Pairs

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
