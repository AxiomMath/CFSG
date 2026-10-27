module

public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank Module
open scoped Matrix


section Basic

variable {r : ℕ} {K : Type} [Field K]

theorem form_comm_zero {u v : Fin r ⊕ Fin r → K} (h : spForm r K u v = 0) :
    spForm r K v u = 0 := by
  rw [← spForm_isAlt.neg_eq, h, neg_zero]

theorem spTransvection_comm_of_form_zero {u v : Fin r ⊕ Fin r → K}
    (h : spForm r K u v = 0) (s t : K) :
    spTransvection u s * spTransvection v t = spTransvection v t * spTransvection u s := by
  have h' := form_comm_zero h
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spTransvection u s * spTransvection v t) y =
    spEnd (spTransvection v t * spTransvection u s) y
  rw [spEnd_mul, spEnd_mul, Module.End.mul_apply, Module.End.mul_apply, spEnd_spTransvection,
    spEnd_spTransvection, spEnd_spTransvection, spEnd_spTransvection]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, h, h',
    mul_zero, add_zero]
  abel

theorem form_self_zero (v : Fin r ⊕ Fin r → K) : spForm r K v v = 0 :=
  spForm_isAlt.self_eq_zero v

theorem form_neg_left (u v : Fin r ⊕ Fin r → K) : spForm r K v u = -spForm r K u v :=
  (spForm_isAlt.neg_eq u v).symm

variable {J : StatedSp r K}

theorem linearIndependent_pair_of_sq_neg_one
    (hJ : ∀ v, spEnd J (spEnd J v) = -v) (hno : ∀ a : K, a * a ≠ -1)
    {x : Fin r ⊕ Fin r → K} (hx0 : x ≠ 0) : LinearIndependent K ![x, spEnd J x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hx0, rfl⟩
  · exfalso
    have h1 : spEnd J x = (-(s / t)) • x := by
      have : t • spEnd J x = (-s) • x := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_right hst
      calc spEnd J x = t⁻¹ • (t • spEnd J x) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = t⁻¹ • ((-s) • x) := by rw [this]
        _ = (-(s / t)) • x := by rw [smul_smul]; congr 1; field_simp
    have h2 : spEnd J (spEnd J x) = ((-(s / t)) * (-(s / t))) • x := by
      rw [h1, map_smul, h1, smul_smul]
    rw [hJ x] at h2
    have h3 : (((-(s / t)) * (-(s / t))) + 1) • x = 0 := by
      rw [add_smul, one_smul, ← h2]; simp
    have h4 := (smul_eq_zero.mp h3).resolve_right hx0
    exact hno (-(s / t)) (by linear_combination h4)


theorem form_self_apply_ne_zero
    (hJ : ∀ v, spEnd J (spEnd J v) = -v) (hno : ∀ a : K, a * a ≠ -1)
    {P : Submodule K (Fin r ⊕ Fin r → K)} (hd : finrank K P = 2)
    (hnd : ∀ v ∈ P, (∀ u ∈ P, spForm r K v u = 0) → v = 0)
    (hJP : ∀ v ∈ P, spEnd J v ∈ P) {x : Fin r ⊕ Fin r → K} (hx : x ∈ P) (hx0 : x ≠ 0) :
    spForm r K x (spEnd J x) ≠ 0 := by
  intro h0
  have hind := linearIndependent_pair_of_sq_neg_one hJ hno hx0
  have hspan : Submodule.span K {x, spEnd J x} = P := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact hx
      · exact hJP x hx
    · rw [hd, ← Matrix.range_cons_cons_empty x (spEnd J x) ![],
        finrank_span_eq_card hind, Fintype.card_fin]
  apply hx0
  refine hnd x hx fun u hu => ?_
  rw [← hspan] at hu
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  simp only [map_add, map_smul, smul_eq_mul, form_self_zero, h0, mul_zero, add_zero]

end Basic

section Gen

variable {r : ℕ} {K : Type} [Field K]

theorem sp_gen (h2 : (2 : K) ≠ 0) (hno : ∀ a : K, a * a ≠ -1)
    (hsq : ∀ t : K, t ≠ 0 → ∃ a b : K, a * a + b * b = t)
    (i J : StatedSp r K) (hi : i * i = 1) (hiJ : i * J = J * i)
    (hJ : ∀ v, spEnd J (spEnd J v) = -v)
    (P₁ P₂ : Submodule K (Fin r ⊕ Fin r → K))
    (hP₁ : ∀ v, v ∈ P₁ ↔ spEnd i v = -v) (hP₂ : ∀ v, v ∈ P₂ ↔ spEnd i v = v)
    (hd₁ : finrank K P₁ = 2) (hd₂ : finrank K P₂ = 2)
    (hnd₁ : ∀ v ∈ P₁, (∀ u ∈ P₁, spForm r K v u = 0) → v = 0)
    (hnd₂ : ∀ v ∈ P₂, (∀ u ∈ P₂, spForm r K v u = 0) → v = 0) :
    Subgroup.centralizer ({i} : Set (StatedSp r K)) ⊔
      Subgroup.centralizer ({J} : Set (StatedSp r K)) = ⊤ := by
  classical
  set H : Subgroup (StatedSp r K) :=
    Subgroup.centralizer ({i} : Set (StatedSp r K)) ⊔
      Subgroup.centralizer ({J} : Set (StatedSp r K)) with hH
  have hiv : ∀ v, spEnd i (spEnd i v) = v := fun v => by
    rw [← Module.End.mul_apply, ← spEnd_mul, hi, spEnd_one, Module.End.one_apply]
  have hiJv : ∀ v, spEnd i (spEnd J v) = spEnd J (spEnd i v) := fun v => by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← spEnd_mul, ← spEnd_mul, hiJ]
  have hJ₁ : ∀ v ∈ P₁, spEnd J v ∈ P₁ := fun v hv => by
    rw [hP₁] at hv ⊢
    rw [hiJv, hv, map_neg]
  have hJ₂ : ∀ v ∈ P₂, spEnd J v ∈ P₂ := fun v hv => by
    rw [hP₂] at hv ⊢
    rw [hiJv, hv]
  have horth : ∀ u ∈ P₁, ∀ v ∈ P₂, spForm r K u v = 0 := fun u hu v hv => by
    have h1 := spEnd_isometry i u v
    rw [(hP₁ u).mp hu, (hP₂ v).mp hv, map_neg, LinearMap.neg_apply] at h1
    have h3 : (2 : K) * spForm r K u v = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h3).resolve_left h2
  have horth' : ∀ u ∈ P₂, ∀ v ∈ P₁, spForm r K u v = 0 := fun u hu v hv =>
    form_comm_zero (horth v hv u hu)
  have htop : P₁ ⊔ P₂ = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hu : (2 : K)⁻¹ • (v - spEnd i v) ∈ P₁ := by
      rw [hP₁, map_smul, map_sub, hiv, ← smul_neg, neg_sub]
    have hw : (2 : K)⁻¹ • (v + spEnd i v) ∈ P₂ := by
      rw [hP₂, map_smul, map_add, hiv, add_comm]
    have hv : v = (2 : K)⁻¹ • (v - spEnd i v) + (2 : K)⁻¹ • (v + spEnd i v) := by
      rw [← smul_add]
      have : v - spEnd i v + (v + spEnd i v) = (2 : K) • v := by module
      rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [hv]
    exact Submodule.add_mem_sup hu hw
  have hpure₂ : ∀ c ∈ P₂, TransCenter H c := fun c hc t => by
    refine Subgroup.mem_sup_left ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_spTransvection ((hP₂ c).mp hc) t
  have hpure₁ : ∀ c ∈ P₁, TransCenter H c := fun c hc t => by
    refine Subgroup.mem_sup_left ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := spTransvection_conj i c t
    have e : spTransvection (-c) t = spTransvection c t := by
      rw [← neg_one_smul K c, spTransvection_smul]
      simp
    rw [(hP₁ c).mp hc, e] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ P₁, x ≠ 0 := by
    have : 0 < finrank K P₁ := by rw [hd₁]; norm_num
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp this
    exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
  obtain ⟨x₂, hx₂, hx₂0⟩ : ∃ x ∈ P₂, x ≠ 0 := by
    have : 0 < finrank K P₂ := by rw [hd₂]; norm_num
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp this
    exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
  have hν : spForm r K x (spEnd J x) ≠ 0 :=
    form_self_apply_ne_zero hJ hno hd₁ hnd₁ hJ₁ hx hx0
  have hν₂ : spForm r K x₂ (spEnd J x₂) ≠ 0 :=
    form_self_apply_ne_zero hJ hno hd₂ hnd₂ hJ₂ hx₂ hx₂0
  have hind := linearIndependent_pair_of_sq_neg_one hJ hno hx0
  set ν := spForm r K x (spEnd J x) with hνdef
  set ν₂ := spForm r K x₂ (spEnd J x₂) with hν₂def
  obtain ⟨a, b, hab⟩ := hsq (-ν / ν₂) (div_ne_zero (neg_ne_zero.mpr hν) hν₂)
  set c₂ : Fin r ⊕ Fin r → K := a • x₂ + b • spEnd J x₂ with hc₂def
  have hc₂ : c₂ ∈ P₂ := P₂.add_mem (P₂.smul_mem a hx₂) (P₂.smul_mem b (hJ₂ x₂ hx₂))
  have hJc₂ : spEnd J c₂ = a • spEnd J x₂ - b • x₂ := by
    rw [hc₂def, map_add, map_smul, map_smul, hJ x₂]
    rw [smul_neg, sub_eq_add_neg, add_comm]
  have hνc₂ : spForm r K c₂ (spEnd J c₂) = -ν := by
    have h1 : spForm r K c₂ (spEnd J c₂) = (a * a + b * b) * ν₂ := by
      rw [hJc₂, hc₂def]
      simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, form_self_zero]
      rw [form_neg_left x₂ (spEnd J x₂), ← hν₂def]
      ring
    rw [h1, hab, div_mul_cancel₀ _ hν₂]
  have hc₂0 : c₂ ≠ 0 := by
    intro h0
    rw [h0, map_zero, LinearMap.zero_apply] at hνc₂
    exact hν (neg_eq_zero.mp hνc₂.symm)
  set c : Fin r ⊕ Fin r → K := spEnd J x + c₂ with hcdef
  have hJc : spEnd J c = -x + spEnd J c₂ := by
    rw [hcdef, map_add, hJ x]
  have hJxP : spEnd J x ∈ P₁ := hJ₁ x hx
  have hJc₂P : spEnd J c₂ ∈ P₂ := hJ₂ c₂ hc₂
  have hωc : spForm r K c (spEnd J c) = 0 := by
    rw [hJc, hcdef]
    simp only [map_add, map_neg, LinearMap.add_apply]
    rw [horth _ hJxP _ hJc₂P, horth' c₂ hc₂ x hx, form_neg_left x (spEnd J x), hνc₂, ← hνdef]
    ring
  set T : StatedSp r K := spTransvection c 1 * spTransvection (spEnd J c) 1 with hT
  have hTJ : T ∈ Subgroup.centralizer ({J} : Set (StatedSp r K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 := spTransvection_conj J c 1
    have e2 := spTransvection_conj J (spEnd J c) 1
    have e3 : spTransvection (spEnd J (spEnd J c)) 1 = spTransvection c 1 := by
      rw [hJ c, ← neg_one_smul K c, spTransvection_smul]
      simp
    rw [e3] at e2
    have hcomm := spTransvection_comm_of_form_zero hωc 1 1
    have h : J * T * J⁻¹ = T := by
      calc J * T * J⁻¹ = (J * spTransvection c 1 * J⁻¹) *
            (J * spTransvection (spEnd J c) 1 * J⁻¹) := by rw [hT]; group
        _ = spTransvection (spEnd J c) 1 * spTransvection c 1 := by rw [e1, e2]
        _ = T := hcomm.symm
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hTH : T ∈ H := Subgroup.mem_sup_right hTJ
  have hmix : TransCenter H (spEnd T x) := (hpure₁ x hx).map hTH
  have hxJc : spForm r K x (spEnd J c) = 0 := by
    rw [hJc]
    simp only [map_add, map_neg, form_self_zero, neg_zero, zero_add]
    exact horth x hx _ hJc₂P
  have hxc : spForm r K x c = ν := by
    rw [hcdef]
    simp only [map_add]
    rw [horth x hx c₂ hc₂, add_zero]
  have hX : spEnd (spTransvection (spEnd J c) 1) x = x := by
    rw [spEnd_spTransvection, hxJc]
    simp
  have hTx : spEnd T x = (x + ν • spEnd J x) + ν • c₂ := by
    rw [hT, spEnd_mul, Module.End.mul_apply, hX, spEnd_spTransvection, hxc, hcdef]
    simp only [one_mul, smul_add]
    abel
  set y : Fin r ⊕ Fin r → K := x + ν • spEnd J x with hydef
  set y' : Fin r ⊕ Fin r → K := ν • c₂ with hy'def
  have hy : y ∈ P₁ := P₁.add_mem hx (P₁.smul_mem ν hJxP)
  have hy' : y' ∈ P₂ := P₂.smul_mem ν hc₂
  have hy0 : y ≠ 0 := by
    intro h0
    have := (LinearIndependent.pair_iff.mp hind) 1 ν (by rw [one_smul]; exact h0)
    exact one_ne_zero this.1
  have hy'0 : y' ≠ 0 := smul_ne_zero hν hc₂0
  have hmix' : TransCenter H (y + y') := by
    rw [← hTx]
    exact hmix
  have hnd₁' : ((spForm r K).restrict P₁).Nondegenerate := by
    refine ⟨fun m hm => Subtype.ext (hnd₁ m m.2 fun u hu => hm ⟨u, hu⟩), fun m hm => ?_⟩
    refine Subtype.ext (hnd₁ m m.2 fun u hu => ?_)
    have := hm ⟨u, hu⟩
    change spForm r K u m = 0 at this
    exact form_comm_zero this
  have hnd₂' : ((spForm r K).restrict P₂).Nondegenerate := by
    refine ⟨fun m hm => Subtype.ext (hnd₂ m m.2 fun u hu => hm ⟨u, hu⟩), fun m hm => ?_⟩
    refine Subtype.ext (hnd₂ m m.2 fun u hu => ?_)
    have := hm ⟨u, hu⟩
    change spForm r K u m = 0 at this
    exact form_comm_zero this
  have hpair : ∀ Y ∈ P₁, ∀ Y' ∈ P₂, Y ≠ 0 → Y' ≠ 0 → TransCenter H (Y + Y') := by
    intro Y hY Y' hY' hY0 hY'0
    obtain ⟨g₁, hg₁, hg₁y, hg₁z⟩ := exists_mem_fixing_eq (U := P₁) hnd₁' hpure₁ hy hY hy0 hY0
    obtain ⟨g₂, hg₂, hg₂y, hg₂z⟩ :=
      exists_mem_fixing_eq (U := P₂) hnd₂' hpure₂ hy' hY' hy'0 hY'0
    have h1 : spEnd g₁ y' = y' := hg₁z y' fun c hc => horth' y' hy' c hc
    have h2 : spEnd g₂ Y = Y := hg₂z Y fun c hc => horth Y hY c hc
    have := hmix'.map (H.mul_mem hg₂ hg₁)
    rwa [spEnd_mul, Module.End.mul_apply, map_add, hg₁y, h1, map_add, h2, hg₂y] at this
  have hall : ∀ v, TransCenter H v := by
    refine transCenter_of_pairs (Vs := ![P₁, P₂]) ?_ ?_ ?_ ?_ ?_
    · rw [← htop]
      apply le_antisymm
      · exact iSup_le fun i => by
          fin_cases i
          · exact le_sup_left
          · exact le_sup_right
      · exact sup_le (le_iSup (![P₁, P₂] : Fin 2 → Submodule K (Fin r ⊕ Fin r → K)) 0)
          (le_iSup (![P₁, P₂] : Fin 2 → Submodule K (Fin r ⊕ Fin r → K)) 1)
    · intro i j hij u hu v hv
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact horth u hu v hv
      · exact horth' u hu v hv
      · exact absurd rfl hij
    · intro i
      fin_cases i
      · exact hnd₁'
      · exact hnd₂'
    · intro i
      fin_cases i
      · exact hpure₁
      · exact hpure₂
    · intro i j hij u hu v hv hu0 hv0
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hpair u hu v hv hu0 hv0
      · rw [add_comm]
        exact hpair v hv u hu hv0 hu0
      · exact absurd rfl hij
  exact eq_top_of_transCenter hall

end Gen

end CFSG.ClassicalInvolution.ModelFacts.TG3
