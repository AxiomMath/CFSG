module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U3CoreRegular
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Coprime

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSU3Core

open CFSG.Open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.HeisSmall HuppertU38F CFSG.RankThree.PartTwo.Sec19.U38F
  CFSG.RankThree.PartTwo.Sec19 Matrix
  CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

section R

variable {F : Type} [Field F]

theorem inf_centralizer_eq_bot_of_fieldType
    (h : UnitaryFieldData 2 3 F) {a : MulAut (unitarySU 2 3 F 3)} (ha3 : a ^ 3 = 1)
    (ha : a ∉ (suConj h).range)
    (T : Subgroup (MulAut (unitarySU 2 3 F 3))) (hT : ¬ 3 ∣ Nat.card T)
    (hTZ : ∀ t ∈ T, ∀ z ∈ Subgroup.center (unitarySU 2 3 F 3), t z = z)
    {c : MulAut (unitarySU 2 3 F 3)} (hcT : c ∈ Subgroup.normalizer (T : Set (MulAut (unitarySU 2 3 F 3))))
    (hca : c * a = a * c) (hfix : ∀ t ∈ T, c * t = t * c → t = 1) :
    T ⊓ Subgroup.centralizer ({a} : Set (MulAut (unitarySU 2 3 F 3))) = ⊥ := by
  have := h.finite
  have hq : 2 < 2 ^ 3 := by norm_num
  obtain ⟨σ', hσ', H, haH⟩ := CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.eq_conj_suField_of_not_mem hq ha3 ha
  set cH : MulAut (unitarySU 2 3 F 3) := suConj h H with hcH
  set Dc : Subgroup (MulAut (unitarySU 2 3 F 3)) :=
    (Dsub h σ').map (MulAut.conj cH).toMonoidHom with hDc
  have hmemDc : ∀ d, d ∈ Dc ↔ cH⁻¹ * d * cH ∈ Dsub h σ' := by
    intro d
    constructor
    · rintro ⟨d', hd', rfl⟩
      have : cH⁻¹ * (MulAut.conj cH).toMonoidHom d' * cH = d' := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [this]
      exact hd'
    · intro hd
      refine ⟨cH⁻¹ * d * cH, hd, ?_⟩
      simp [MulAut.conj_apply]
      group
  have hTD : T ⊓ Subgroup.centralizer ({a} : Set (MulAut (unitarySU 2 3 F 3))) ≤ Dc := by
    intro t ht
    obtain ⟨htT, hta⟩ := Subgroup.mem_inf.1 ht
    have hta' : t * a = a * t := Subgroup.mem_centralizer_singleton_iff.1 hta
    have hcop : Nat.Coprime 3 (orderOf t) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
        (fun h3 => hT (h3.trans (Subgroup.orderOf_dvd_natCard T htT)))
    obtain ⟨W, hW⟩ := mem_range_suConj_of_coprime h hcop (hTZ t htT)
    rw [hmemDc]
    have hcomm' : cH⁻¹ * t * cH * suField h σ' = suField h σ' * (cH⁻¹ * t * cH) := by
      have h1 : t * (cH * suField h σ' * cH⁻¹) = (cH * suField h σ' * cH⁻¹) * t := by
        rw [← haH]; exact hta'
      calc cH⁻¹ * t * cH * suField h σ' = cH⁻¹ * (t * (cH * suField h σ' * cH⁻¹)) * cH := by group
        _ = cH⁻¹ * ((cH * suField h σ' * cH⁻¹) * t) * cH := by rw [h1]
        _ = suField h σ' * (cH⁻¹ * t * cH) := by group
    have hcent : cH⁻¹ * t * cH ∈
        Subgroup.centralizer ({suField h σ'} : Set (MulAut (unitarySU 2 3 F 3))) :=
      Subgroup.mem_centralizer_singleton_iff.2 hcomm'
    exact ⟨⟨H⁻¹ * W * H, by rw [map_mul, map_mul, map_inv, hW]⟩, hcent⟩
  have hexp : ∀ d ∈ Dc, d ^ 12 = 1 := by
    intro d hd
    have h1 := pow_twelve_eq_one_of_mem_Dsub h hσ' ((hmemDc d).1 hd)
    have : (cH⁻¹ * d * cH) ^ 12 = cH⁻¹ * d ^ 12 * cH := by
      have := conj_pow (a := cH⁻¹) (b := d) (i := 12)
      simpa using this
    rw [this] at h1
    have h2 : d ^ 12 = cH * (cH⁻¹ * d ^ 12 * cH) * cH⁻¹ := by group
    rw [h2, h1]
    group
  have hV : ∀ u ∈ Dc, ∀ v ∈ Dc, u ^ 2 = 1 → v ^ 2 = 1 → u * v = v * u → u = 1 ∨ v = 1 ∨ u = v := by
    intro u hu v hv hu2 hv2 huv
    have hu' := (hmemDc u).1 hu
    have hv' := (hmemDc v).1 hv
    have key : ∀ w : MulAut (unitarySU 2 3 F 3), w ^ 2 = 1 → (cH⁻¹ * w * cH) ^ 2 = 1 := by
      intro w hw
      have := conj_pow (a := cH⁻¹) (b := w) (i := 2)
      simp only [inv_inv] at this
      rw [this, hw]
      group
    have hcomm : cH⁻¹ * u * cH * (cH⁻¹ * v * cH) = cH⁻¹ * v * cH * (cH⁻¹ * u * cH) := by
      calc cH⁻¹ * u * cH * (cH⁻¹ * v * cH) = cH⁻¹ * (u * v) * cH := by group
        _ = cH⁻¹ * (v * u) * cH := by rw [huv]
        _ = cH⁻¹ * v * cH * (cH⁻¹ * u * cH) := by group
    rcases eq_of_commute_involutions_of_mem_Dsub h hσ' hu' hv' (key u hu2) (key v hv2) hcomm with
      h1 | h1 | h1
    · left
      have : u = cH * (cH⁻¹ * u * cH) * cH⁻¹ := by group
      rw [this, h1]
      group
    · right; left
      have : v = cH * (cH⁻¹ * v * cH) * cH⁻¹ := by group
      rw [this, h1]
      group
    · right; right
      have e1 : u = cH * (cH⁻¹ * u * cH) * cH⁻¹ := by group
      have e2 : v = cH * (cH⁻¹ * v * cH) * cH⁻¹ := by group
      rw [e1, e2, h1]
  set Ta : Subgroup (MulAut (unitarySU 2 3 F 3)) :=
    T ⊓ Subgroup.centralizer ({a} : Set (MulAut (unitarySU 2 3 F 3))) with hTa
  have hT3 : ¬ 3 ∣ Nat.card Ta :=
    fun h3 => hT (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hcN : c ∈ Subgroup.normalizer (Ta : Set (MulAut (unitarySU 2 3 F 3))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      obtain ⟨htT, hta⟩ := Subgroup.mem_inf.1 ht
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hcT t).1 htT, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hta ⊢
      calc c * t * c⁻¹ * a = c * t * (c⁻¹ * a) := by group
        _ = c * t * (a * c⁻¹) := by
            have : c⁻¹ * a = a * c⁻¹ := by
              calc c⁻¹ * a = c⁻¹ * (a * c) * c⁻¹ := by group
                _ = c⁻¹ * (c * a) * c⁻¹ := by rw [hca]
                _ = a * c⁻¹ := by group
            rw [this]
        _ = c * (t * a) * c⁻¹ := by group
        _ = c * (a * t) * c⁻¹ := by rw [hta]
        _ = a * (c * t * c⁻¹) := by
            calc c * (a * t) * c⁻¹ = (c * a) * t * c⁻¹ := by group
              _ = (a * c) * t * c⁻¹ := by rw [hca]
              _ = a * (c * t * c⁻¹) := by group
    · intro ht
      obtain ⟨htT, hta⟩ := Subgroup.mem_inf.1 ht
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hcT t).2 htT, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hta ⊢
      have hcc : (c * t * c⁻¹) * a = a * (c * t * c⁻¹) := hta
      calc t * a = c⁻¹ * ((c * t * c⁻¹) * a) * c := by
              calc t * a = c⁻¹ * (c * t * c⁻¹) * c * a := by group
                _ = c⁻¹ * (c * t * c⁻¹) * (c * a) := by group
                _ = c⁻¹ * (c * t * c⁻¹) * (a * c) := by rw [hca]
                _ = c⁻¹ * ((c * t * c⁻¹) * a) * c := by group
        _ = c⁻¹ * (a * (c * t * c⁻¹)) * c := by rw [hcc]
        _ = a * t := by
              calc c⁻¹ * (a * (c * t * c⁻¹)) * c = (c⁻¹ * a) * (c * t * c⁻¹) * c := by group
                _ = (a * c⁻¹) * (c * t * c⁻¹) * c := by
                    have : c⁻¹ * a = a * c⁻¹ := by
                      calc c⁻¹ * a = c⁻¹ * (a * c) * c⁻¹ := by group
                        _ = c⁻¹ * (c * a) * c⁻¹ := by rw [hca]
                        _ = a * c⁻¹ := by group
                    rw [this]
                _ = a * t := by group
  exact eq_bot_of_fixedPointFree hexp hV hTD hT3 hcN
    (fun t ht hct => hfix t ht.1 hct)

theorem eq_bot_of_regular_field
    (h : UnitaryFieldData 2 3 F) {σ : F ≃+* F} (hσ : orderOf σ = 3) {Y : unitaryIsom3 h}
    (hY : RegularU38 (Y : GL (Fin 3) F))
    (hcomm : suConj h Y * suField h σ = suField h σ * suConj h Y)
    (T : Subgroup (MulAut (unitarySU 2 3 F 3))) (hT : ¬ 3 ∣ Nat.card T)
    (hTf : suField h σ ∈ Subgroup.normalizer (T : Set (MulAut (unitarySU 2 3 F 3))))
    (hTc : suConj h Y ∈ Subgroup.normalizer (T : Set (MulAut (unitarySU 2 3 F 3))))
    (hTZ : ∀ t ∈ T, ∀ z ∈ Subgroup.center (unitarySU 2 3 F 3), t z = z) : T = ⊥ := by
  have := h.finite
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ
    omega
  have hσpow : ∀ i : ℕ, ¬ 3 ∣ i → σ ^ i ≠ 1 := by
    intro i hi h1
    exact hi (hσ ▸ orderOf_dvd_of_pow_eq_one h1)
  have hf3 : suField h σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  obtain ⟨κ, hκ3, hYκ⟩ := hY.1
  have hc3 : suConj h Y ^ 3 = 1 := suConj_pow_eq_one_of_scalar h Y 3 (c := κ) hYκ
  have hc1 : suConj h Y ≠ 1 := by
    intro hc1
    obtain ⟨lam, hlam⟩ := scalar_of_suConj_eq_one h hc1
    apply hY.2
    refine ⟨0, lam ^ 2, ?_⟩
    rw [hlam, pow_two, zero_smul, zero_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      smul_smul, pow_two]
  have hTc1 := inf_centralizer_eq_bot_of_regular h hY T hT hTZ
  set f := suField h σ with hf
  set c := suConj h Y with hc
  have hfc : Commute f c := hcomm.symm
  set A₁ : Subgroup (MulAut (unitarySU 2 3 F 3)) := Subgroup.closure ({f, c} : Set _) with hA₁
  have hA₁el : IsElemAbelian 3 A₁ := by
    refine IsElemAbelian.closure_of_commute (p := 3) (s := {f, c}) ?_ ?_
    · intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hfc.eq
      · exact hfc.eq.symm
      · rfl
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact hf3
      · exact hc3
  have hfA : f ∈ A₁ := Subgroup.subset_closure (by simp)
  have hcA : c ∈ A₁ := Subgroup.subset_closure (by simp)
  have hA₁T : A₁ ≤ Subgroup.normalizer (T : Set (MulAut (unitarySU 2 3 F 3))) := by
    rw [hA₁, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hTf
    · exact hTc
  have hf1 : f ≠ 1 := fun h1 => hσ1 (by
    have := suField_not_mem_range h hσ1
    exact absurd ⟨1, by rw [map_one]; exact h1.symm⟩ this)
  have hforder : orderOf f = 3 := orderOf_eq_prime hf3 hf1
  have hA₁card : 3 ^ 2 ≤ Nat.card A₁ := by
    obtain ⟨k, hk⟩ := i271_exists_card_eq Nat.prime_three hA₁el
    by_contra hlt
    push Not at hlt
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) hk2
      omega
    have hzf : Subgroup.zpowers f ≤ A₁ := (Subgroup.zpowers_le).2 hfA
    have hcardz : Nat.card (Subgroup.zpowers f) = 3 := by rw [Nat.card_zpowers, hforder]
    have hcardA : Nat.card A₁ ≤ 3 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk1 with rfl | rfl <;> rw [hk] <;> norm_num
    have heq : Subgroup.zpowers f = A₁ :=
      Subgroup.eq_of_le_of_card_ge hzf (by rw [hcardz]; exact hcardA)
    rw [← heq] at hcA
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hcA
    apply hc1
    have hm' : suField h (σ ^ m) = c := by rw [map_zpow, ← hf]; exact hm
    have hσm : σ ^ m = 1 := by
      by_contra hne
      exact suField_not_mem_range h hne ⟨Y, by rw [← hc, hm']⟩
    rw [hσm, map_one] at hm'
    exact hm'.symm
  have hform : ∀ a ∈ A₁, ∃ i j : ℕ, a = f ^ i * c ^ j := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, j, rfl⟩ := hx
      obtain ⟨i', j', rfl⟩ := hy
      refine ⟨i + i', j + j', ?_⟩
      rw [pow_add, pow_add]
      calc f ^ i * c ^ j * (f ^ i' * c ^ j') = f ^ i * (c ^ j * f ^ i') * c ^ j' := by group
        _ = f ^ i * (f ^ i' * c ^ j) * c ^ j' := by rw [← (hfc.pow_pow i' j).eq]
        _ = f ^ i * f ^ i' * (c ^ j * c ^ j') := by group
    | inv x _ hx =>
      obtain ⟨i, j, rfl⟩ := hx
      refine ⟨2 * i, 2 * j, ?_⟩
      apply inv_eq_of_mul_eq_one_right
      calc f ^ i * c ^ j * (f ^ (2 * i) * c ^ (2 * j))
          = f ^ i * (c ^ j * f ^ (2 * i)) * c ^ (2 * j) := by group
        _ = f ^ i * (f ^ (2 * i) * c ^ j) * c ^ (2 * j) := by rw [← (hfc.pow_pow (2 * i) j).eq]
        _ = f ^ (i + 2 * i) * c ^ (j + 2 * j) := by rw [pow_add, pow_add]; group
        _ = 1 := by
          have e1 : i + 2 * i = 3 * i := by ring
          have e2 : j + 2 * j = 3 * j := by ring
          rw [e1, e2, pow_mul, pow_mul, hf3, hc3, one_pow, one_pow, one_mul]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CFSG.IsElementaryAbelian 3 ↥A₁ :=
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.isElementaryAbelian_of_isElemAbelian hA₁el
  have hgen := le_iSup_centralizer_of_coprime (p := 3) (A := A₁) (U := T) hA₁card hT hA₁T
  rw [eq_bot_iff]
  refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
  obtain ⟨i, j, rfl⟩ := hform a ha
  by_cases hi : 3 ∣ i
  ·
    have hfi : f ^ i = 1 := by
      obtain ⟨m, rfl⟩ := hi
      rw [pow_mul, hf3, one_pow]
    rw [hfi, one_mul] at ha1 ⊢
    have hj : ¬ 3 ∣ j := by
      rintro ⟨m, rfl⟩
      apply ha1
      rw [pow_mul, hc3, one_pow]
    have hcj : c = (c ^ j) ^ j := by
      rw [← pow_mul]
      have h3 : j * j % 3 = 1 := by
        have := Nat.mod_lt j (show 0 < 3 by norm_num)
        have h0 : j % 3 ≠ 0 := fun h0 => hj (Nat.dvd_of_mod_eq_zero h0)
        have : j % 3 = 1 ∨ j % 3 = 2 := by omega
        rcases this with h1 | h1 <;> simp [Nat.mul_mod, h1]
      have : j * j = 3 * (j * j / 3) + 1 := by omega
      rw [this, pow_add, pow_mul, hc3, one_pow, one_mul, pow_one]
    intro t ht
    obtain ⟨htT, htc⟩ := Subgroup.mem_inf.1 ht
    have htc' : t * c ^ j = c ^ j * t := Subgroup.mem_centralizer_singleton_iff.1 htc
    have htc'' : t * c = c * t := by
      have := (Commute.pow_right (show Commute t (c ^ j) from htc') j).eq
      rw [← hcj] at this
      exact this
    have : t ∈ T ⊓ Subgroup.centralizer ({c} : Set (MulAut (unitarySU 2 3 F 3))) :=
      Subgroup.mem_inf.2 ⟨htT, Subgroup.mem_centralizer_singleton_iff.2 htc''⟩
    rw [hTc1] at this
    exact this
  ·
    have ha3 : (f ^ i * c ^ j) ^ 3 = 1 := by
      rw [(hfc.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3, pow_mul,
        pow_mul, hf3, hc3, one_pow, one_pow, one_mul]
    have hnot : f ^ i * c ^ j ∉ (suConj h).range := by
      rintro ⟨W, hW⟩
      have hfi : suField h (σ ^ i) = suConj h (W * (Y ^ j)⁻¹) := by
        rw [map_pow, map_mul, map_inv, map_pow, hW]
        simp only [hf, hc]
        group
      exact suField_not_mem_range h (hσpow i hi) ⟨_, hfi.symm⟩
    have hca : c * (f ^ i * c ^ j) = (f ^ i * c ^ j) * c :=
      (Commute.mul_right (Commute.pow_right hcomm i)
        ((Commute.refl c).pow_right j)).eq
    exact (inf_centralizer_eq_bot_of_fieldType h ha3 hnot T hT hTZ hTc hca
      (fun t ht hct => by
        have : t ∈ T ⊓ Subgroup.centralizer ({c} : Set (MulAut (unitarySU 2 3 F 3))) :=
          Subgroup.mem_inf.2 ⟨ht, Subgroup.mem_centralizer_singleton_iff.2 hct.symm⟩
        rw [hTc1] at this
        exact this)).le

end R

end KSU3Core

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
