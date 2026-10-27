module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInnerCore
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AE9
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AField
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.LocalAnalysis.GLTheoremB

section Inner

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem mem_statedScalars_of_comm_mod (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) {g : GL (Fin 3) K}
    (hg : ∀ s ∈ slPi π 3 (p ^ f) K, s ∈ centMod (slPi π 3 (p ^ f) K) g) :
    g ∈ StatedScalars (Fin 3) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hperf : commutator ↥(slPi π 3 (p ^ f) K) = ⊤ :=
    (isQuasisimple_slPi hK (fun _ h => by omega)).1
  have hLL : slPi π 3 (p ^ f) K ≤ ⁅slPi π 3 (p ^ f) K, slPi π 3 (p ^ f) K⁆ := by
    intro s hs
    have h1 : (⟨s, hs⟩ : ↥(slPi π 3 (p ^ f) K)) ∈ commutator ↥(slPi π 3 (p ^ f) K) := by
      rw [hperf]; exact Subgroup.mem_top _
    have h2 : (commutator ↥(slPi π 3 (p ^ f) K)).map (slPi π 3 (p ^ f) K).subtype =
        ⁅slPi π 3 (p ^ f) K, slPi π 3 (p ^ f) K⁆ := by
      change ((⁅(⊤ : Subgroup ↥(slPi π 3 (p ^ f) K)), (⊤ : Subgroup ↥(slPi π 3 (p ^ f) K))⁆ :
        Subgroup ↥(slPi π 3 (p ^ f) K))).map _ = _
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← h2]
    exact ⟨_, h1, rfl⟩
  refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun m hm => ?_
  have h3 : m ∈ Subgroup.centralizer ({g} : Set (GL (Fin 3) K)) :=
    commutator_centMod_le (slPi π 3 (p ^ f) K) g
      (Subgroup.commutator_mono (fun s hs => hg s hs) (fun s hs => hg s hs) (hLL hm))
  rw [Subgroup.mem_centralizer_singleton_iff] at h3
  exact h3.symm

theorem isFieldAutThree_of_frob {Y : Type} [Group Y] (hK : PiField π p f K) (hq2 : 2 < p ^ f)
    (e : (Y ⧸ Subgroup.center Y) ≃*
      (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)))
    {α : MulAut Y} {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (h : MulAut.congr e (centerDescend Y α) = centerDescend _ (frobSL hK σ)) :
    IsFieldAutThree α := by
  have := hK.finite
  right
  cases π
  · right
    refine isFieldAutPSU3_of_data hK.unitary (e.trans (etaFalse hK hq2)) σ
      (by rw [hσ]; decide) 1 ?_
    rw [congr_trans', h, congr_eta_false_frob, inv_one, mul_one, one_mul]
  · left
    refine isFieldAutPSL3_of_data (e.trans (etaTrue (p ^ f) K)) σ 1 ?_
    rw [congr_trans', h, congr_etaTrue_frob, inv_one, mul_one, one_mul]

@[expose] def InnerAutAt {Y : Type} [Group Y] (π : Bool) (p f : ℕ) (K : Type) [Field K]
    (β : MulAut Y) : Prop :=
  ∃ ν : ↥(slPi π 3 (p ^ f) K) →* Y, Function.Surjective ν ∧
    (∀ s ∈ ν.ker, ((s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K) ∧
    ∃ x : GL (Fin 3) K, x ∈ glPi π 3 (p ^ f) K ∧ x ∉ zPi π 3 (p ^ f) K ∧
      x ^ 3 ∈ zPi π 3 (p ^ f) K ∧ ∀ s t : ↥(slPi π 3 (p ^ f) K),
        (t : GL (Fin 3) K) = x * s * x⁻¹ → β (ν s) = ν t

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem dichot_cover (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (e : Y ≃* ↥(slPi π 3 (p ^ f) K)) {β : MulAut Y} (hβ3 : β ^ 3 = 1) :
    IsFieldAutThree β ∨ InnerAutAt π p f K β := by
  by_cases hβ1 : β = 1
  · exact Or.inl (Or.inl hβ1)
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hζ3 : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  rcases exists_conj_or_field_of_pow_three_eq_one hK hq2 hζ3 with
    ⟨y, hy, hS⟩ | ⟨σ, hσ, H, hH, hζ⟩
  · have hconj := semiAct_one_iff.1 hS
    have hyZ : y ∉ zPi π 3 (p ^ f) K := by
      intro hz
      apply hβ1
      rw [zPi_eq hπ hq' hτ hτ1] at hz
      have hz' := (Subgroup.mem_inf.1 hz).2
      apply (MulAut.congr e).injective
      rw [map_one]
      refine MulEquiv.ext fun s => Subtype.ext ?_
      rw [hconj s]
      have := commute_of_mem_statedScalars hz' (s : GL (Fin 3) K)
      calc y * (s : GL (Fin 3) K) * y⁻¹ = (s : GL (Fin 3) K) * y * y⁻¹ := by rw [this]
        _ = s := mul_inv_cancel_right _ _
    have hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K := by
      rw [zPi_eq hπ hq' hτ hτ1]
      refine Subgroup.mem_inf.2 ⟨pow_mem hy 3, ?_⟩
      refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun m hm => ?_
      have h3 : ((((MulAut.congr e β) ^ 3) ⟨m, hm⟩ : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) =
          y ^ 3 * m * (y ^ 3)⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
        rw [hconj, hconj, hconj]
        group
      rw [hζ3] at h3
      change m = _ at h3
      calc y ^ 3 * m = (y ^ 3 * m * (y ^ 3)⁻¹) * y ^ 3 := by group
        _ = m * y ^ 3 := by rw [← h3]
    refine Or.inr ⟨e.symm.toMonoidHom, e.symm.surjective, ?_, y, hy, hyZ, hy3, fun s t ht => ?_⟩
    · intro s hs
      have : s = 1 := e.symm.injective (by simpa using hs)
      rw [this]
      exact one_mem _
    have h1 : (MulAut.congr e β) s = t := Subtype.ext ((hconj s).trans ht.symm)
    have h2 : e (β (e.symm s)) = t := h1
    change β (e.symm s) = e.symm t
    rw [← h2]
    simp
  · have hc : MulAut.congr (conjSL' hπ hH) (MulAut.congr e β) = frobSL hK σ := by
      refine MulEquiv.ext fun s => Subtype.ext ?_
      rw [coe_frobSL]
      have h1 : (((conjSL' hπ hH).symm s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) =
          H * s * H⁻¹ := rfl
      have h2 : ((conjSL' hπ hH ((MulAut.congr e β) ((conjSL' hπ hH).symm s)) :
          ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) =
          H⁻¹ * (((MulAut.congr e β) ((conjSL' hπ hH).symm s) : ↥(slPi π 3 (p ^ f) K)) :
            GL (Fin 3) K) * H := rfl
      show ((conjSL' hπ hH ((MulAut.congr e β) ((conjSL' hπ hH).symm s)) :
          ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) = _
      rw [h2, hζ, h1]
      have h3 : H⁻¹ * (H * (s : GL (Fin 3) K) * H⁻¹) * H = s := by group
      rw [h3]
      group
    exact Or.inl (isFieldAutThree_of_frob hK hq2 (barEquiv (e.trans (conjSL' hπ hH))) hσ
      (by rw [congr_barEquiv, congr_trans', hc]))

omit [Finite Y] in
theorem dichot_proj (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (e : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)))
    {β : MulAut Y} (hβ3 : β ^ 3 = 1) : IsFieldAutThree β ∨ InnerAutAt π p f K β := by
  by_cases hβ1 : β = 1
  · exact Or.inl (Or.inl hβ1)
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨pkg⟩ := exists_etaPkg hK hq2
  have hGq : CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ f) K) :=
    isQuasisimple_slPi hK (fun _ h => by omega)
  have hGp : Group.IsPerfect ↥(slPi π 3 (p ^ f) K) := (Group.isPerfect_def).2 hGq.1
  have hcQ : Subgroup.center (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) =
      ⊥ := Group.IsPerfect.center_quotient_center_eq_bot _
  have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_mulEquiv_of_center_eq_bot e hcQ
  set ε : Y ≃* pkg.M := e.trans pkg.η with hε
  have hβ3' : MulAut.congr ε β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  rcases pkg.dich _ hβ3' with hin | ⟨σ, hσ, κ, hκ, hβ'⟩
  · obtain ⟨x, hx, hxs⟩ := pkg.conj_of_inndiag _ hin
    have hxs' : ∀ s t : ↥(slPi π 3 (p ^ f) K), (t : GL (Fin 3) K) = x * s * x⁻¹ →
        β (e.symm (QuotientGroup.mk s)) = e.symm (QuotientGroup.mk t) := by
      intro s t ht
      have h1 := hxs s t ht
      rw [hε, congr_trans', congr_symm_congr, MulAut.congr_apply] at h1
      rw [← h1]
      simp
    let ν : ↥(slPi π 3 (p ^ f) K) →* Y :=
      e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(slPi π 3 (p ^ f) K)))
    have hνker : ∀ s ∈ ν.ker, ((s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈
        StatedScalars (Fin 3) K := by
      intro s hs
      have h1 : (QuotientGroup.mk s : ↥(slPi π 3 (p ^ f) K) ⧸
          Subgroup.center ↥(slPi π 3 (p ^ f) K)) = 1 :=
        e.symm.injective (by simpa [ν] using hs)
      have h2 : s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) := (QuotientGroup.eq_one_iff s).1 h1
      rw [center_slPi_eq hK hq, Subgroup.mem_subgroupOf] at h2
      exact h2
    have hνsurj : Function.Surjective ν := by
      intro y
      obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (e y)
      exact ⟨s, by simp [ν, hs]⟩
    have hνβ : ∀ s t : ↥(slPi π 3 (p ^ f) K), (t : GL (Fin 3) K) = x * s * x⁻¹ →
        β (ν s) = ν t := fun s t ht => hxs' s t ht
    have hxZ : x ∉ zPi π 3 (p ^ f) K := by
      intro hz
      apply hβ1
      rw [zPi_eq hπ hq' (exists_tau hK hq).choose_spec.1 (exists_tau hK hq).choose_spec.2] at hz
      have hz' := (Subgroup.mem_inf.1 hz).2
      ext y
      obtain ⟨s, rfl⟩ := hνsurj y
      have := commute_of_mem_statedScalars hz' (s : GL (Fin 3) K)
      have h1 := hνβ s s (by
        calc (s : GL (Fin 3) K) = (s : GL (Fin 3) K) * x * x⁻¹ := (mul_inv_cancel_right _ _).symm
          _ = x * s * x⁻¹ := by rw [this])
      simpa using h1
    have hx3 : x ^ 3 ∈ zPi π 3 (p ^ f) K := by
      obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
      rw [zPi_eq hπ hq' hτ hτ1]
      refine Subgroup.mem_inf.2 ⟨pow_mem hx 3, ?_⟩
      refine mem_statedScalars_of_comm_mod hK hq hq2 fun s hs => ?_
      let s0 : ↥(slPi π 3 (p ^ f) K) := ⟨s, hs⟩
      let t1 : ↥(slPi π 3 (p ^ f) K) := ⟨x * s0 * x⁻¹, conj_mem_slPi hπ hx s0.2⟩
      let t2 : ↥(slPi π 3 (p ^ f) K) := ⟨x * t1 * x⁻¹, conj_mem_slPi hπ hx t1.2⟩
      let t3 : ↥(slPi π 3 (p ^ f) K) := ⟨x * t2 * x⁻¹, conj_mem_slPi hπ hx t2.2⟩
      have h1 : β (ν s0) = ν t1 := hνβ s0 t1 rfl
      have h2 : β (ν t1) = ν t2 := hνβ t1 t2 rfl
      have h3 : β (ν t2) = ν t3 := hνβ t2 t3 rfl
      have hβν : (β ^ 3) (ν s0) = ν s0 := by rw [hβ3]; rfl
      have h4 : ν s0 = ν t3 := by
        rw [← hβν]
        simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
        rw [h1, h2, h3]
      exact mem_centMod_of_nu_eq hνker t3 (by
        change x * (x * (x * (s0 : GL (Fin 3) K) * x⁻¹) * x⁻¹) * x⁻¹ = _
        rw [pow_three']
        group) h4
    exact Or.inr ⟨ν, hνsurj, hνker, x, hx, hxZ, hx3, hνβ⟩
  · let e2 : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) :=
      (ε.trans κ⁻¹).trans pkg.η.symm
    have hc : MulAut.congr e2 β = centerDescend _ (frobSL hK σ) := by
      have h1 : MulAut.congr e2 β =
          MulAut.congr pkg.η.symm (MulAut.congr κ⁻¹ (MulAut.congr ε β)) := by
        rw [congr_trans', congr_trans']
      rw [h1, hβ', congr_self, inv_inv]
      have h2 : κ⁻¹ * (κ * MulAut.congr pkg.η (centerDescend _ (frobSL hK σ)) * κ⁻¹) * κ =
          MulAut.congr pkg.η (centerDescend _ (frobSL hK σ)) := by group
      rw [h2]
      ext x
      simp [MulAut.congr_apply]
    refine Or.inl (isFieldAutThree_of_frob hK hq2 ((barEquivBot hZ).trans e2) hσ ?_)
    rw [congr_trans', congr_barEquivBot, hc]


theorem inner_cover (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (e : Y ≃* ↥(slPi π 3 (p ^ f) K)) {β : MulAut Y} (hβ3 : β ^ 3 = 1) {J : Subgroup Y}
    (hJβ : ∀ j ∈ J, β j = j) (hQ : CFSG.Open.IsQuasisimple (↥J ⧸ CFSG.Open.GLAPPrimeCore 3 ↥J))
    (hE9 : ∃ E : Subgroup (↥J ⧸ CFSG.Open.GLAPPrimeCore 3 ↥J),
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9) : IsFieldAutThree β := by
  rcases dichot_cover hK hq hq2 e hβ3 with h | ⟨ν, hνs, hνker, x, hx, hxZ, hx3, hνβ⟩
  · exact h
  · exact (false_of_inner hK hq ν hνker hx hxZ hx3 J (fun j _ => hνs j) β hνβ hJβ hQ hE9).elim

theorem inner_proj (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (e : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)))
    {β : MulAut Y} (hβ3 : β ^ 3 = 1) {J : Subgroup Y}
    (hJβ : ∀ j ∈ J, β j = j) (hQ : CFSG.Open.IsQuasisimple (↥J ⧸ CFSG.Open.GLAPPrimeCore 3 ↥J))
    (hE9 : ∃ E : Subgroup (↥J ⧸ CFSG.Open.GLAPPrimeCore 3 ↥J),
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9) : IsFieldAutThree β := by
  rcases dichot_proj hK hq hq2 e hβ3 with h | ⟨ν, hνs, hνker, x, hx, hxZ, hx3, hνβ⟩
  · exact h
  · exact (false_of_inner hK hq ν hνker hx hxZ hx3 J (fun j _ => hνs j) β hνβ hJβ hQ hE9).elim

end Inner

theorem gap510_Inner_holds : LocalBalance.Lemma510Ns.Gap510_Inner := by
  intro Y _ _ hq hT β hβ3 J hJ hJt
  have hQ : CFSG.Open.IsQuasisimple (↥J ⧸ CFSG.Open.GLAPPrimeCore 3 ↥J) :=
    isQuasisimple_quotient_of_glaPComponent hJ
  have hJβ : ∀ j ∈ J, β j = j := fun j hj => hJ.1 hj
  rcases model_of_type hq hT with ⟨π, p, f, K, _, hK, hmod, -, h2, ⟨e⟩⟩ |
      ⟨π, p, f, K, _, hK, hmod, -, h2, ⟨e⟩⟩
  · exact inner_cover hK hmod h2 e hβ3 hJβ hQ (exists_elemAbelian_nine_of_isL3Type hJt)
  · exact inner_proj hK hmod h2 e hβ3 hJβ hQ (exists_elemAbelian_nine_of_isL3Type hJt)

end CFSG.HardMathSupport.Solomon.Coordinator
