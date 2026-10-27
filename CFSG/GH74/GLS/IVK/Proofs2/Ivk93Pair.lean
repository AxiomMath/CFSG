module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift

public section

open scoped MatrixGroups

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint


theorem exists_involution_lift {A B : Type} [Group A] [Finite A] [Group B] (f : A →* B)
    (hodd : ∀ y ∈ f.ker, Odd (orderOf y)) {b : B} (hb : orderOf b = 2) (hbr : b ∈ f.range) :
    ∃ a : A, orderOf a = 2 ∧ f a = b := by
  obtain ⟨h, rfl⟩ := hbr
  have hn : orderOf h ≠ 0 := (orderOf_pos h).ne'
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  have hdvd : m ∣ orderOf h := ⟨2 ^ a, by rw [hord]; ring⟩
  have ht : orderOf (h ^ m) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hm0 hdvd, hord]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  have hu2 : (f h) ^ 2 = 1 := by
    have h' := pow_orderOf_eq_one (f h)
    rw [hb] at h'
    exact h'
  have hmk : f (h ^ m) = f h := by
    obtain ⟨k, hk⟩ := hm
    rw [map_pow, hk, pow_succ, pow_mul, hu2, one_pow, one_mul]
  have hu1 : f h ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hb
    omega
  refine ⟨h ^ m, ?_, hmk⟩
  have ht2 : (h ^ m) ^ 2 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, hmk, hu2]
  have hodd2 := hodd _ ht2
  have hd1 : orderOf ((h ^ m) ^ 2) ∣ 2 ^ a := ht ▸ orderOf_pow_dvd 2
  have hcop : Nat.Coprime (orderOf ((h ^ m) ^ 2)) (2 ^ a) :=
    (Nat.coprime_two_right.2 hodd2).pow_right a
  have hone : orderOf ((h ^ m) ^ 2) = 1 := Nat.Coprime.eq_one_of_dvd hcop hd1
  have hsq : (h ^ m) ^ 2 = 1 := orderOf_eq_one_iff.1 hone
  have hne : h ^ m ≠ 1 := by
    intro h1
    apply hu1
    rw [← hmk, h1, map_one]
  exact orderOf_eq_prime hsq hne

theorem index_odd_of_sylow_le {X : Type} [Group X] [Finite X] {J : Subgroup X} (T : Sylow 2 X)
    (hTJ : (T : Subgroup X) ≤ J) : ¬ 2 ∣ J.index := by
  intro h
  exact T.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hTJ))

theorem involution_mem_of_odd_index {X : Type} [Group X] [Finite X] {J : Subgroup X} [J.Normal]
    (hJ : ¬ 2 ∣ J.index) {u : X} (hu : orderOf u = 2) : u ∈ J := by
  have hodd : Odd (Nat.card (X ⧸ J)) := by
    rw [← Subgroup.index_eq_card]
    exact Nat.odd_iff.2 (by
      rcases Nat.even_or_odd J.index with he | ho
      · exact absurd (even_iff_two_dvd.1 he) hJ
      · exact Nat.odd_iff.1 ho)
  have h1 : orderOf (QuotientGroup.mk u : X ⧸ J) ∣ 2 := by
    rw [← hu]
    exact orderOf_map_dvd (QuotientGroup.mk' J) u
  have h2 : orderOf (QuotientGroup.mk u : X ⧸ J) ∣ Nat.card (X ⧸ J) := orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk u : X ⧸ J) = 1 := by
    have hc : Nat.Coprime 2 (Nat.card (X ⧸ J)) := Nat.coprime_two_left.2 hodd
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc) h2
  exact (QuotientGroup.eq_one_iff u).1 (orderOf_eq_one_iff.1 h3)


theorem fus_of_classes {G : Type} [Group G] [Finite G] {H : Subgroup G} {z x : G}
    (hzH : z ∈ H) (hxH : x ∈ H) (hz2 : orderOf z = 2) (hx2 : orderOf x = 2)
    (hzx : ¬ IsConj z x) (hcl : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj x u)
    (hX : ∀ ū : HBar H, orderOf ū = 2 →
      IsConj ū (mkH H ⟨z, hzH⟩) ∨ IsConj ū (mkH H ⟨x, hxH⟩)) : FUS H := by
  have hzH2 : orderOf (⟨z, hzH⟩ : ↥H) = 2 := by rw [← Subgroup.orderOf_coe]; exact hz2
  have hxH2 : orderOf (⟨x, hxH⟩ : ↥H) = 2 := by rw [← Subgroup.orderOf_coe]; exact hx2
  have toG : ∀ {a b : ↥H}, IsConj a b → IsConj (a : G) (b : G) := fun {a b} h =>
    MonoidHom.map_isConj H.subtype h
  have hz : ∀ w : ↥H, orderOf w = 2 → IsConj (w : G) z → IsConj (mkH H w) (mkH H ⟨z, hzH⟩) := by
    intro w hw hwz
    have hw2 : orderOf (mkH H w) = 2 := orderOf_mk_eq_two H hw
    rcases hX _ hw2 with h | h
    · exact h
    · exfalso
      have h1 : IsConj w ⟨x, hxH⟩ := isConj_of_mk_isConj H hw hxH2 h
      exact hzx (hwz.symm.trans ((toG h1)))
  have hx : ∀ w : ↥H, orderOf w = 2 → IsConj (w : G) x → IsConj (mkH H w) (mkH H ⟨x, hxH⟩) := by
    intro w hw hwx
    have hw2 : orderOf (mkH H w) = 2 := orderOf_mk_eq_two H hw
    rcases hX _ hw2 with h | h
    · exfalso
      have h1 : IsConj w ⟨z, hzH⟩ := isConj_of_mk_isConj H hw hzH2 h
      exact hzx ((toG h1).symm.trans hwx)
    · exact h
  intro u v hu hv huv
  have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  rcases hcl (u : G) hu' with h | h
  ·
    have huz : IsConj (u : G) z := h.symm
    have hvz : IsConj (v : G) z := huv.symm.trans huz
    exact (hz u hu huz).trans (hz v hv hvz).symm
  · have hux : IsConj (u : G) x := h.symm
    have hvx : IsConj (v : G) x := huv.symm.trans hux
    exact (hx u hu hux).trans (hx v hv hvx).symm


section PairG

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem center_map_eq_inf {Y : Type} [Group Y] [Finite Y] {L M : Subgroup Y} {q : ℕ} (hq : Odd q)
    (hLM : ∀ a ∈ L, ∀ b ∈ M, a * b = b * a) (hW : Nat.card ↥(L ⊓ M) = 2)
    (hsl : HasSL2Model ↥L (fun r => r = q)) : (center ↥L).map L.subtype = L ⊓ M := by
  have hZc : Nat.card ↥((center ↥L).map L.subtype) = 2 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact card_center_of_hasSL2Model hq hsl
  have hle : L ⊓ M ≤ (center ↥L).map L.subtype := by
    intro w hw
    refine Subgroup.mem_map.2 ⟨⟨w, hw.1⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (hLM c.1 c.2 w hw.2)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hW, hZc])).symm

theorem sl2_exists_sq_neg_one (F : Type) [Field F] : ∃ w : SL(2, F), w * w = -1 := by
  let M : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]
  have hM : M.det = 1 := by simp [M, Matrix.det_fin_two]
  refine ⟨⟨M, hM⟩, ?_⟩
  ext i j
  show (M * M) i j = (-(1 : Matrix (Fin 2) (Fin 2) F)) i j
  fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_neg_one_ne_one (F : Type) [Field F] (hc : ringChar F ≠ 2) : (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have h00 := congrArg (fun A : SL(2, F) => A.val 0 0) h
  simp at h00
  exact Ring.neg_one_ne_one_of_char_ne_two hc h00

theorem sl2_neg_one_mem_inf {Y : Type} [Group Y] {L M : Subgroup Y} {F : Type} [Field F]
    (e : SL(2, F) ≃* ↥L) (hZ : (center ↥L).map L.subtype = L ⊓ M) :
    ((e (-1) : ↥L) : Y) ∈ L ⊓ M := by
  rw [← hZ]
  refine Subgroup.mem_map.2 ⟨e (-1), ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro c
  obtain ⟨d, rfl⟩ := e.surjective c
  rw [← map_mul, ← map_mul]
  congr 1
  simp

theorem exists_involution_LBar (hz2 : orderOf z = 2) (hp : Stage1Pair G z S q L₁ L₂) :
    ∃ b : CentralizerBar z, b ∈ LBar z ∧ orderOf b = 2 ∧ b ≠ toBar z ⟨z, mem_Cen_self z⟩ := by
  have hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := hp.prod.2.1
  have hZ₁ := center_map_eq_inf hp.odd hcomm hp.prod.2.2 hp.sl₁
  have hZ₂ := center_map_eq_inf hp.odd (fun a ha b hb => (hcomm b hb a ha).symm)
    (by rw [inf_comm]; exact hp.prod.2.2) hp.sl₂
  obtain ⟨F₁, hF₁, hF₁fin, hF₁q, ⟨e₁⟩⟩ := exists_sl2_equiv_of_hasSL2Model hp.sl₁
  obtain ⟨F₂, hF₂, hF₂fin, hF₂q, ⟨e₂⟩⟩ := exists_sl2_equiv_of_hasSL2Model hp.sl₂
  have hchar₁ : ringChar F₁ ≠ 2 :=
    CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card (hF₁q ▸ hp.odd)
  have hchar₂ : ringChar F₂ ≠ 2 :=
    CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card (hF₂q ▸ hp.odd)
  obtain ⟨w₁, hw₁⟩ := sl2_exists_sq_neg_one F₁
  obtain ⟨w₂, hw₂⟩ := sl2_exists_sq_neg_one F₂
  set a₁ : CentralizerBar z := ((e₁ w₁ : ↥L₁) : CentralizerBar z) with ha₁
  set a₂ : CentralizerBar z := ((e₂ w₂ : ↥L₂) : CentralizerBar z) with ha₂
  have ha₁L : a₁ ∈ L₁ := (e₁ w₁).2
  have ha₂L : a₂ ∈ L₂ := (e₂ w₂).2
  set ζ₁ : CentralizerBar z := ((e₁ (-1) : ↥L₁) : CentralizerBar z) with hζ₁
  set ζ₂ : CentralizerBar z := ((e₂ (-1) : ↥L₂) : CentralizerBar z) with hζ₂
  have hsq₁ : a₁ * a₁ = ζ₁ := by
    rw [ha₁, hζ₁, ← Subgroup.coe_mul, ← map_mul, hw₁]
  have hsq₂ : a₂ * a₂ = ζ₂ := by
    rw [ha₂, hζ₂, ← Subgroup.coe_mul, ← map_mul, hw₂]
  have hζ₁inf : ζ₁ ∈ L₁ ⊓ L₂ := sl2_neg_one_mem_inf e₁ hZ₁
  have hζ₂inf : ζ₂ ∈ L₁ ⊓ L₂ := by
    rw [inf_comm]
    exact sl2_neg_one_mem_inf e₂ hZ₂
  have hζ₁ne : ζ₁ ≠ 1 := by
    intro h
    have : e₁ (-1) = 1 := Subtype.ext (by rw [Subgroup.coe_one]; exact h)
    exact sl2_neg_one_ne_one F₁ hchar₁ (e₁.injective (this.trans (map_one e₁).symm))
  have hζ₂ne : ζ₂ ≠ 1 := by
    intro h
    have : e₂ (-1) = 1 := Subtype.ext (by rw [Subgroup.coe_one]; exact h)
    exact sl2_neg_one_ne_one F₂ hchar₂ (e₂.injective (this.trans (map_one e₂).symm))
  have huniq : ∀ g h : CentralizerBar z, g ∈ L₁ ⊓ L₂ → h ∈ L₁ ⊓ L₂ → g ≠ 1 → h ≠ 1 → g = h := by
    intro g h hg hh hg1 hh1
    obtain ⟨y, -, huy⟩ := (Nat.card_eq_two_iff' (1 : ↥(L₁ ⊓ L₂))).1 hp.prod.2.2
    have h1 := huy ⟨g, hg⟩ (fun h' => hg1 (congrArg Subtype.val h'))
    have h2 := huy ⟨h, hh⟩ (fun h' => hh1 (congrArg Subtype.val h'))
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hζeq : ζ₁ = ζ₂ := huniq _ _ hζ₁inf hζ₂inf hζ₁ne hζ₂ne
  have hζsq : ζ₁ * ζ₁ = 1 := by
    rw [hζ₁, ← Subgroup.coe_mul, ← map_mul]
    simp
  have hexp : ∀ g ∈ L₁ ⊓ L₂, g * g = 1 := by
    intro g hg
    by_cases hg1 : g = 1
    · rw [hg1, mul_one]
    · rw [huniq g ζ₁ hg hζ₁inf hg1 hζ₁ne]
      exact hζsq
  have hcomm12 : a₁ * a₂ = a₂ * a₁ := hcomm a₁ ha₁L a₂ ha₂L
  have hbsq : a₁ * a₂ * (a₁ * a₂) = 1 := by
    calc a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by simp only [mul_assoc]
      _ = a₁ * (a₁ * a₂) * a₂ := by rw [← hcomm12]
      _ = (a₁ * a₁) * (a₂ * a₂) := by simp only [mul_assoc]
      _ = 1 := by rw [hsq₁, hsq₂, ← hζeq, hζsq]
  have ha₁nL₂ : a₁ ∉ L₂ := by
    intro h
    have := hexp a₁ ⟨ha₁L, h⟩
    rw [hsq₁] at this
    exact hζ₁ne this
  have hb1 : a₁ * a₂ ≠ 1 := by
    intro h
    apply ha₁nL₂
    have : a₁ = a₂⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact L₂.inv_mem ha₂L
  have hzinf := zbarC_mem_inf hp
  have hz1 : toBar z ⟨z, mem_Cen_self z⟩ ≠ 1 := by
    intro h
    have h1 : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) :=
      (QuotientGroup.eq_one_iff _).1 h
    have h2 := odd_orderOf_of_mem_pPrimeCore h1
    rw [← Subgroup.orderOf_coe] at h2
    change Odd (orderOf z) at h2
    rw [hz2] at h2
    exact absurd h2 (by decide)
  have hzζ : toBar z ⟨z, mem_Cen_self z⟩ = ζ₁ := huniq _ _ hzinf hζ₁inf hz1 hζ₁ne
  refine ⟨a₁ * a₂, ?_, ?_, ?_⟩
  · rw [← hp.prod.1]
    exact (L₁ ⊔ L₂).mul_mem (Subgroup.mem_sup_left ha₁L) (Subgroup.mem_sup_right ha₂L)
  · exact orderOf_eq_prime (by rw [sq]; exact hbsq) hb1
  · intro h
    rw [hzζ] at h
    apply ha₁nL₂
    have : a₁ = ζ₁ * a₂⁻¹ := by rw [← h]; group
    rw [this]
    exact L₂.mul_mem hζ₁inf.2 (L₂.inv_mem ha₂L)


theorem exists_lift_LBar (hz2 : orderOf z = 2) {H : Subgroup G} (hCH : Cen z ≤ H) (hPerf : PerfInJ H)
    (hp : Stage1Pair G z S q L₁ L₂) :
    ∃ M : Subgroup (HBar H), M ≤ generalizedFitting (HBar H) ∧ M ≤ barIn H (Cen z) ∧
      (M.subgroupOf (barIn H (Cen z))).map (cenToBar H hCH) = LBar z := by
  have hc₁ : IsComponent L₁ := (Set.ext_iff.1 hp.comps L₁).2 (Or.inl rfl)
  have hc₂ : IsComponent L₂ := (Set.ext_iff.1 hp.comps L₂).2 (Or.inr rfl)
  have hzbar := zbarC_mem_inf hp
  obtain ⟨B₁, hB₁J, hB₁C, -, -, hB₁map⟩ := lift_comp hz2 hCH hPerf hc₁ hzbar.1
  obtain ⟨B₂, hB₂J, hB₂C, -, -, hB₂map⟩ := lift_comp hz2 hCH hPerf hc₂ hzbar.2
  refine ⟨B₁ ⊔ B₂, sup_le hB₁J hB₂J, sup_le hB₁C hB₂C, ?_⟩
  rw [Subgroup.subgroupOf_sup hB₁C hB₂C, Subgroup.map_sup, hB₁map, hB₂map, hp.prod.1]

theorem mem_J_of_two_power (hz2 : orderOf z = 2) {H : Subgroup G} (hCH : Cen z ≤ H)
    (hPerf : PerfInJ H) (hp : Stage1Pair G z S q L₁ L₂) {y : HBar H}
    (hyC : y ∈ barIn H (Cen z)) (hy : cenToBar H hCH ⟨y, hyC⟩ ∈ LBar z) {n : ℕ}
    (hyn : y ^ (2 ^ n) = 1) : y ∈ generalizedFitting (HBar H) := by
  obtain ⟨M, hMJ, hMC, hMmap⟩ := exists_lift_LBar hz2 hCH hPerf hp
  have hy' : cenToBar H hCH ⟨y, hyC⟩ ∈
      (M.subgroupOf (barIn H (Cen z))).map (cenToBar H hCH) := by rw [hMmap]; exact hy
  obtain ⟨m, hm, hmy⟩ := hy'
  have hmM : (m : HBar H) ∈ M := hm
  have hk : cenToBar H hCH (m⁻¹ * ⟨y, hyC⟩) = 1 := by
    rw [map_mul, map_inv, hmy, inv_mul_cancel]
  have hkodd := odd_orderOf_of_cenToBar_eq_one H hCH _ hk
  have : (generalizedFitting (HBar H)).Normal := LocalCores.generalized_fitting_characteristic.2
  let π := QuotientGroup.mk' (generalizedFitting (HBar H))
  have hmJ : π (m : HBar H) = 1 := (QuotientGroup.eq_one_iff _).2 (hMJ hmM)
  have h1 : π y = π (((m⁻¹ * ⟨y, hyC⟩ : ↥(barIn H (Cen z))) : HBar H)) := by
    have : ((m⁻¹ * ⟨y, hyC⟩ : ↥(barIn H (Cen z))) : HBar H) = (m : HBar H)⁻¹ * y := rfl
    rw [this, map_mul, map_inv, hmJ, inv_one, one_mul]
  have h2 : orderOf (π y) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hyn, map_one])
  have h3 : orderOf (π y) ∣ orderOf (m⁻¹ * ⟨y, hyC⟩ : ↥(barIn H (Cen z))) := by
    rw [h1]
    refine (orderOf_map_dvd π _).trans ?_
    rw [Subgroup.orderOf_coe]
  have h4 : orderOf (π y) = 1 := by
    have hc : Nat.Coprime (2 ^ n) (orderOf (m⁻¹ * ⟨y, hyC⟩ : ↥(barIn H (Cen z)))) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hkodd)
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hc) h3
  exact (QuotientGroup.eq_one_iff y).1 (orderOf_eq_one_iff.1 h4)

theorem exists_involution_L (hz2 : orderOf z = 2) {H : Subgroup G} (hCH : Cen z ≤ H)
    (hPerf : PerfInJ H) (hp : Stage1Pair G z S q L₁ L₂) :
    ∃ (u : G) (hu : u ∈ H), u ∈ LC z ∧ orderOf u = 2 ∧ u ≠ z ∧
      mkH H ⟨u, hu⟩ ∈ generalizedFitting (HBar H) := by
  obtain ⟨b, hbL, hb2, hbz⟩ := exists_involution_LBar hz2 hp
  let A : Subgroup ↥(Cen z) := (LC z).subgroupOf (Cen z)
  let f : ↥A →* CentralizerBar z := (toBar z).comp A.subtype
  have hodd : ∀ y ∈ f.ker, Odd (orderOf y) := by
    intro y hy
    have h1 : (y : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).1 hy
    have h2 := odd_orderOf_of_mem_pPrimeCore h1
    rwa [Subgroup.orderOf_coe] at h2
  have hbr : b ∈ f.range := by
    obtain ⟨c, hc, hcb⟩ := hbL
    exact ⟨⟨c, hc⟩, hcb⟩
  obtain ⟨a₀, ha₀2, ha₀b⟩ := exists_involution_lift f hodd hb2 hbr
  set c : ↥(Cen z) := (a₀ : ↥(Cen z)) with hc
  have hcL : (c : G) ∈ LC z := a₀.2
  have hcH : (c : G) ∈ H := hCH c.2
  have hc2 : orderOf (c : G) = 2 := by
    rw [Subgroup.orderOf_coe, hc, Subgroup.orderOf_coe]
    exact ha₀2
  have hbc : toBar z c = b := ha₀b
  refine ⟨(c : G), hcH, hcL, hc2, ?_, ?_⟩
  · intro h
    apply hbz
    rw [← hbc]
    congr 1
    exact Subtype.ext h
  · have hcH2 : orderOf (⟨(c : G), hcH⟩ : ↥H) = 2 := by
      rw [← Subgroup.orderOf_coe]; exact hc2
    have hy2 : orderOf (mkH H ⟨(c : G), hcH⟩) = 2 := orderOf_mk_eq_two H hcH2
    refine mem_J_of_two_power hz2 hCH hPerf hp (y := mkH H ⟨(c : G), hcH⟩) (cenMk_mem H hCH c) ?_
      (n := 1) ?_
    · show cenToBar H hCH ⟨cenMk H hCH c, cenMk_mem H hCH c⟩ ∈ LBar z
      rw [cenToBar_cenMk, hbc]
      exact hbL
    · have h := pow_orderOf_eq_one (mkH H ⟨(c : G), hcH⟩)
      rw [hy2] at h
      simpa using h


theorem false_of_J_one_class (hctx : Stage2Ctx G z k S) {H : Subgroup G} (hCH : Cen z ≤ H)
    (hPerf : PerfInJ H) (hp : Stage1Pair G z S q L₁ L₂) {x : G}
    (hx : TwoClassData G z S L₁ L₂ q x)
    (hone : ∀ a b : ↥(generalizedFitting (HBar H)), orderOf a = 2 → orderOf b = 2 →
      IsConj a b) : False := by
  have hz2 := hctx.orderOf_z
  have hzmem : z ∈ H := hCH (mem_Cen_self z)
  obtain ⟨u, huH, huL, hu2, huz, huJ⟩ := exists_involution_L hz2 hCH hPerf hp
  obtain ⟨hzJ, -⟩ := exists_cfg hz2 hCH hPerf hp
  have huH2 : orderOf (⟨u, huH⟩ : ↥H) = 2 := by rw [← Subgroup.orderOf_coe]; exact hu2
  have hzH2 : orderOf (⟨z, hzmem⟩ : ↥H) = 2 := by rw [← Subgroup.orderOf_coe]; exact hz2
  have hub2 : orderOf (mkH H ⟨u, huH⟩) = 2 := orderOf_mk_eq_two H huH2
  have hzb2 : orderOf (mkH H ⟨z, hzmem⟩) = 2 := orderOf_mk_eq_two H hzH2
  have hconj : IsConj (⟨mkH H ⟨u, huH⟩, huJ⟩ : ↥(generalizedFitting (HBar H)))
      ⟨mkH H ⟨z, hzmem⟩, hzJ⟩ := by
    refine hone _ _ ?_ ?_
    · rw [← Subgroup.orderOf_coe]; exact hub2
    · rw [← Subgroup.orderOf_coe]; exact hzb2
  have hconj' : IsConj (mkH H ⟨u, huH⟩) (mkH H ⟨z, hzmem⟩) :=
    MonoidHom.map_isConj (generalizedFitting (HBar H)).subtype hconj
  have hH : IsConj (⟨u, huH⟩ : ↥H) ⟨z, hzmem⟩ := isConj_of_mk_isConj H huH2 hzH2 hconj'
  have hG : IsConj u z := MonoidHom.map_isConj H.subtype hH
  have hxu := (hx.invol_L u huL hu2 huz).1
  have hxz : IsConj x z := hxu.trans hG
  apply hx.x_nonCentral
  obtain ⟨c, hc⟩ := isConj_iff.1 hxz
  have hzc : IsCentralInvolution z := hctx.central
  have := isCentralInvolution_of_equiv (MulAut.conj c⁻¹) hzc
  have hx' : (MulAut.conj c⁻¹) z = x := by
    show c⁻¹ * z * c⁻¹⁻¹ = x
    rw [← hc]
    group
  rwa [hx'] at this

end PairG


theorem exists_index_two_of_sylow_card {X : Type} [Group X] [Finite X] {J : Subgroup X} [J.Normal]
    (T : Sylow 2 X) (h : Nat.card ↥(T : Subgroup X) = 2 * Nat.card ↥((T : Subgroup X) ⊓ J)) :
    ∃ N : Subgroup X, N.Normal ∧ J ≤ N ∧ N.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := Glauberman.sylow_inf_normal T (N := J)
  have hP1 : Nat.card ↥P = Nat.card ↥((T : Subgroup X) ⊓ J) := by
    have : Nat.card ↥((T : Subgroup X) ⊓ J) = Nat.card ↥(((T : Subgroup X) ⊓ J).subgroupOf J) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
    rw [this, ← hP]
    rfl
  have hTcard : Nat.card ↥(T : Subgroup X) = 2 ^ (Nat.card X).factorization 2 :=
    Sylow.card_eq_multiplicity T
  have hPcard : Nat.card ↥P = 2 ^ (Nat.card ↥J).factorization 2 := Sylow.card_eq_multiplicity P
  have hXQ : Nat.card X = Nat.card (X ⧸ J) * Nat.card ↥J := Subgroup.card_eq_card_quotient_mul_card_subgroup J
  have hQpos : Nat.card (X ⧸ J) ≠ 0 := Nat.card_pos.ne'
  have hJpos : Nat.card ↥J ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card X).factorization 2 = (Nat.card (X ⧸ J)).factorization 2 + (Nat.card ↥J).factorization 2 := by
    rw [hXQ, Nat.factorization_mul hQpos hJpos]
    rfl
  have h2 : 2 ^ (Nat.card X).factorization 2 = 2 * 2 ^ (Nat.card ↥J).factorization 2 := by
    rw [← hTcard, h, hP1.symm.trans hPcard]
  have hq1 : (Nat.card (X ⧸ J)).factorization 2 = 1 := by
    have : 2 ^ ((Nat.card (X ⧸ J)).factorization 2 + (Nat.card ↥J).factorization 2) =
        2 ^ (1 + (Nat.card ↥J).factorization 2) := by
      rw [← hfac, h2, pow_add, pow_one]
    have := Nat.pow_right_injective (le_refl 2) this
    omega
  obtain ⟨R⟩ : Nonempty (Sylow 2 (X ⧸ J)) := inferInstance
  have hR : Nat.card ↥(R : Subgroup (X ⧸ J)) = 2 := by
    have := Sylow.card_eq_multiplicity R
    rw [hq1] at this
    simpa using this
  have hcyc : IsCyclic ↥(R : Subgroup (X ⧸ J)) := isCyclic_of_prime_card (p := 2) hR
  have : Fintype (X ⧸ J) := Fintype.ofFinite _
  have hQeven : Even (Fintype.card (X ⧸ J)) := by
    rw [← Nat.card_eq_fintype_card]
    exact even_iff_two_dvd.2 (Nat.dvd_of_factorization_pos (by omega))
  obtain ⟨-, hsurj, hnorm, hidx⟩ := LinearGroups.cyclic_sylow_index_two hQeven R hcyc
  let ε := Equiv.Perm.sign.comp (MulAction.toPermHom (X ⧸ J) (X ⧸ J))
  refine ⟨ε.ker.comap (QuotientGroup.mk' J), ?_, ?_, ?_⟩
  · exact Subgroup.Normal.comap hnorm _
  · intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    have : (QuotientGroup.mk' J) x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [this, map_one]
  · rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective J)]
    exact hidx


theorem O2Of_ne_of_index_two {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {N : Subgroup (HBar H)} (hN : N.Normal) (hidx : N.index = 2) : O2Of H ≠ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hO2
  let N₀ : Subgroup ↥H := N.comap (mkH H)
  have hN₀ : N₀.Normal := Subgroup.Normal.comap hN _
  have hidx₀ : N₀.index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hidx
  have hpg : IsPGroup 2 (↥H ⧸ N₀) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [← Subgroup.index_eq_card, hidx₀]
    norm_num
  have hres : oResidual 2 ↥H ≤ N₀ :=
    CFSG.GH74.GLS.Stage1.Thm6.Prod.oResidual_le_of_isPGroup_quotient hpg
  have htop : oResidual 2 ↥H = ⊤ := by
    refine eq_top_iff.2 fun h _ => ?_
    have : (h : G) ∈ (oResidual 2 ↥H).map H.subtype := by
      change (h : G) ∈ O2Of H
      rw [hO2]
      exact h.2
    obtain ⟨x, hx, hxh⟩ := this
    have hxh' : x = h := Subtype.ext hxh
    rwa [hxh'] at hx
  have : N₀ = ⊤ := eq_top_iff.2 (htop ▸ hres)
  rw [this, Subgroup.index_top] at hidx₀
  exact absurd hidx₀ (by norm_num)


end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
