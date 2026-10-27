module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE6Aux4
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE6Aux2

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredE6Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


theorem Qθ_le_adjointGroup {F : Type} [Field F] : Qθ Tag.E6 F ≤ adjointGroup Tag.E6 F :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem one_not_mem_J₂ : (1 : Fin Tag.E6.rank).val ∉ TwClass.e6Six.J₂ := by decide

theorem twIrred_core {K : Type} [Field K] [Finite K] (hK : 3 ≤ Nat.card K)
    (D : LangLevi Tag.E6 K wE) :
    TwIrred (D.frame TwClass.e6Six.S₁) (D.frame TwClass.e6Six.S₂) := by
  classical
  intro W hWM hWstab
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hq2 : 2 ≤ Nat.card K := by omega
  have hspecK := heisCoord_spec Tag.E6 K
  have hspecL := heisCoord_spec Tag.E6 D.L
  obtain ⟨f, hf⟩ := levi_action (τ := Tag.E6) (L := D.L) (inv_mem D.g_mem)
  obtain ⟨f', hf'⟩ := levi_action (τ := Tag.E6) (L := D.L) D.g_mem
  simp only [inv_inv] at hf
  let alg : (V6 → K) → (V6 → D.L) := fun v β => algebraMap K D.L (v β)
  let ι : (V6 → K) → (V6 → D.L) := fun v => f (alg v)
  have halg_add : ∀ x y : V6 → K, alg (x + y) = alg x + alg y := fun x y =>
    funext fun β => by simp [alg]
  have halg_smul : ∀ (c : K) (x : V6 → K), alg (c • x) = algebraMap K D.L c • alg x :=
    fun c x => funext fun β => by simp [alg]
  have hι_add : ∀ x y : V6 → K, ι (x + y) = ι x + ι y := fun x y => by
    simp only [ι, halg_add, map_add]
  have hι_smul : ∀ (c : K) (x : V6 → K), ι (c • x) = algebraMap K D.L c • ι x := fun c x => by
    simp only [ι, halg_smul, map_smul]
  have hι_zero : ι 0 = 0 := by
    have h := hι_smul 0 0
    rwa [zero_smul, map_zero, zero_smul] at h
  have hι : ∀ q₀ ∈ Qθ Tag.E6 K,
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g ∈ Qθ Tag.E6 D.L ∧
      heisCoord Tag.E6 D.L (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g) =
        ι (heisCoord Tag.E6 K q₀) := by
    intro q₀ hq₀
    obtain ⟨hb, hbc⟩ := coord_baseChange (algebraMap K D.L) hq₀
    obtain ⟨h1, h2⟩ := hf _ hb
    exact ⟨h1, by rw [h2, hbc]⟩
  have hVMdeg : ∀ v ∈ VM (D.frame TwClass.e6Six.S₁ ⊔ D.frame TwClass.e6Six.S₂), ∀ β,
      β ∉ Deg1 Tag.E6 → v β = 0 := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => ∀ β, β ∉ Deg1 Tag.E6 → v β = 0)
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨q₀, hq₀, rfl⟩ β hβ
      exact hspecK.support q₀ hq₀.1 β hβ
    · intro β _
      rfl
    · intro x y _ _ hx hy β hβ
      simp [hx β hβ, hy β hβ]
    · intro c x _ hx β hβ
      simp [hx β hβ]
  have hWq : ∀ v ∈ W, ∃ q₀ ∈ Qθ Tag.E6 K, heisCoord Tag.E6 K q₀ = v := fun v hv =>
    hspecK.surj v (hVMdeg v (hWM hv))
  have hff : ∀ x : V6 → D.L, (∀ β, β ∉ Deg1 Tag.E6 → x β = 0) → f' (f x) = x := by
    intro x hx
    obtain ⟨q', hq', rfl⟩ := hspecL.surj x hx
    obtain ⟨h1, h2⟩ := hf q' hq'
    obtain ⟨h3, h4⟩ := hf' _ h1
    rw [← h2, ← h4]
    congr 1
    group
  have halgdeg : ∀ v : V6 → K, (∀ β, β ∉ Deg1 Tag.E6 → v β = 0) →
      ∀ β, β ∉ Deg1 Tag.E6 → alg v β = 0 := by
    intro v hv β hβ
    simp [alg, hv β hβ]
  obtain ⟨e, A, he, hA, hAf⟩ := exists_sigFix_S1 D hK
  obtain ⟨a₁, ha₁, a₂, ha₂, hdet⟩ := exists_two_indep (Nat.card K) hq2 e he A hA
  have hR : ∀ a ∈ A, ∃ (c : D.L) (r : ModGL Tag.E6 K),
      r ∈ Rθ (D.frame TwClass.e6Six.S₁ ⊔ D.frame TwClass.e6Six.S₂) ∧
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) r * D.g =
        pinnedX Tag.E6 D.L (highRoot Tag.E6) c * pinnedX Tag.E6 D.L a2 a *
          pinnedX Tag.E6 D.L b2 (e * a ^ Nat.card K) := by
    intro a ha
    obtain ⟨c, hc⟩ := hAf a ha
    have hu : pinnedX Tag.E6 D.L (highRoot Tag.E6) c * pinnedX Tag.E6 D.L a2 a *
        pinnedX Tag.E6 D.L b2 (e * a ^ Nat.card K) ∈ Qθ Tag.E6 D.L :=
      mul_mem (mul_mem (pinnedX_highRoot_mem_Qθ c) (pinnedX_mem_Qθ_of_Deg1 a2_mem_Deg1 a))
        (pinnedX_mem_Qθ_of_Deg1 b2_mem_Deg1 _)
    obtain ⟨r, hr, hre⟩ := exists_rational_Qθ_sig D hu hc
    have hgr : D.g⁻¹ * baseChangeGL (algebraMap K D.L) r * D.g =
        pinnedX Tag.E6 D.L (highRoot Tag.E6) c * pinnedX Tag.E6 D.L a2 a *
          pinnedX Tag.E6 D.L b2 (e * a ^ Nat.card K) := by
      rw [hre]
      group
    have huS : pinnedX Tag.E6 D.L (highRoot Tag.E6) c * pinnedX Tag.E6 D.L a2 a *
        pinnedX Tag.E6 D.L b2 (e * a ^ Nat.card K) ∈
          rootSpan Tag.E6 D.L TwClass.e6Six.S₁ :=
      mul_mem (mul_mem (pinnedX_mem_rootSpan (mem_S₁ (by simp)) c)
        (pinnedX_mem_rootSpan (mem_S₁ (by simp)) a)) (pinnedX_mem_rootSpan (mem_S₁ (by simp)) _)
    have hrX : r ∈ D.frame TwClass.e6Six.S₁ :=
      (TwBasicAux.mem_frame_iff D _ r).2 ⟨Qθ_le_adjointGroup hr, by rw [hgr]; exact huS⟩
    exact ⟨c, r, ⟨le_sup_left (a := D.frame TwClass.e6Six.S₁) hrX, hr⟩, hgr⟩
  obtain ⟨c₁, r₁, hr₁, hr₁e⟩ := hR a₁ ha₁
  obtain ⟨c₂, r₂, hr₂, hr₂e⟩ := hR a₂ ha₂
  have hsuppC : ∀ q₀ ∈ CQθ (D.frame TwClass.e6Six.S₁ ⊔ D.frame TwClass.e6Six.S₂), ∀ ν,
      ν ∉ Mlist → ι (heisCoord Tag.E6 K q₀) ν = 0 := by
    intro q₀ hq₀ ν hν
    obtain ⟨hq₀Q, hq₀C⟩ := hq₀
    obtain ⟨hq', hq'e⟩ := hι q₀ hq₀Q
    rw [← hq'e]
    have hcomm : ∀ r ∈ Rθ (D.frame TwClass.e6Six.S₁ ⊔ D.frame TwClass.e6Six.S₂),
        (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g) *
            (D.g⁻¹ * baseChangeGL (algebraMap K D.L) r * D.g) =
          (D.g⁻¹ * baseChangeGL (algebraMap K D.L) r * D.g) *
            (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g) := by
      intro r hr
      have h := Subgroup.mem_centralizer_iff.1 hq₀C r hr
      have h' : baseChangeGL (algebraMap K D.L) q₀ * baseChangeGL (algebraMap K D.L) r =
          baseChangeGL (algebraMap K D.L) r * baseChangeGL (algebraMap K D.L) q₀ := by
        rw [← map_mul, ← map_mul, h]
      calc (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g) *
            (D.g⁻¹ * baseChangeGL (algebraMap K D.L) r * D.g)
          = D.g⁻¹ * (baseChangeGL (algebraMap K D.L) q₀ * baseChangeGL (algebraMap K D.L) r) *
              D.g := by group
        _ = D.g⁻¹ * (baseChangeGL (algebraMap K D.L) r * baseChangeGL (algebraMap K D.L) q₀) *
              D.g := by rw [h']
        _ = (D.g⁻¹ * baseChangeGL (algebraMap K D.L) r * D.g) *
              (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g) := by group
    have l₁ := lin_of_commute hq' c₁ a₁ (e * a₁ ^ Nat.card K) (by rw [← hr₁e]; exact hcomm r₁ hr₁)
    have l₂ := lin_of_commute hq' c₂ a₂ (e * a₂ ^ Nat.card K) (by rw [← hr₂e]; exact hcomm r₂ hr₂)
    have hN₁ := NC_ne_zero (F := D.L) a2_mem_Deg1
    have hN₂ := NC_ne_zero (F := D.L) b2_mem_Deg1
    have hX0 : heisCoord Tag.E6 D.L (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g) b2 = 0 := by
      have h : (NC a2 : D.L) *
          heisCoord Tag.E6 D.L (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g) b2 *
          (a₁ * (e * a₂ ^ Nat.card K) - a₂ * (e * a₁ ^ Nat.card K)) = 0 := by
        linear_combination (e * a₂ ^ Nat.card K) * l₁ - (e * a₁ ^ Nat.card K) * l₂
      rcases mul_eq_zero.1 h with h | h
      · exact (mul_eq_zero.1 h).resolve_left hN₁
      · exact absurd h hdet
    have hY0 : heisCoord Tag.E6 D.L (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g) a2 = 0 := by
      have h : (NC b2 : D.L) *
          heisCoord Tag.E6 D.L (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g) a2 *
          (a₁ * (e * a₂ ^ Nat.card K) - a₂ * (e * a₁ ^ Nat.card K)) = 0 := by
        linear_combination a₁ * l₂ - a₂ * l₁
      rcases mul_eq_zero.1 h with h | h
      · exact (mul_eq_zero.1 h).resolve_left hN₂
      · exact absurd h hdet
    rcases not_mem_Mlist hν with h | h | h
    · exact hspecL.support _ hq' ν h
    · rw [h]
      exact hY0
    · rw [h]
      exact hX0
  have hsuppVM : ∀ v ∈ VM (D.frame TwClass.e6Six.S₁ ⊔ D.frame TwClass.e6Six.S₂), ∀ ν,
      ν ∉ Mlist → ι v ν = 0 := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => ∀ ν, ν ∉ Mlist → ι v ν = 0)
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨q₀, hq₀, rfl⟩
      exact hsuppC q₀ hq₀
    · intro ν _
      rw [hι_zero]
      rfl
    · intro x y _ _ hx hy ν hν
      rw [hι_add, Pi.add_apply, hx ν hν, hy ν hν, add_zero]
    · intro c x _ hx ν hν
      rw [hι_smul, Pi.smul_apply, hx ν hν, smul_zero]
  set Wb : Submodule D.L (V6 → D.L) := Submodule.span D.L (ι '' (W : Set (V6 → K))) with hWb
  have hWbsupp : ∀ v ∈ Wb, ∀ ν, ν ∉ Mlist → v ν = 0 := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => ∀ ν, ν ∉ Mlist → v ν = 0) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨w, hw, rfl⟩
      exact hsuppVM w (hWM hw)
    · intro ν _
      rfl
    · intro x y _ _ hx hy ν hν
      simp [hx ν hν, hy ν hν]
    · intro c x _ hx ν hν
      simp [hx ν hν]
  have hstab_of : ∀ P : (V6 → D.L) →ₗ[D.L] (V6 → D.L), (∀ w ∈ W, P (ι w) ∈ Wb) →
      ∀ v ∈ Wb, P v ∈ Wb := by
    intro P hP v hv
    have h : Wb ≤ Wb.comap P := Submodule.span_le.2 (by
      rintro _ ⟨w, hw, rfl⟩
      exact hP w hw)
    exact h hv
  have hact : ∀ {γ₁ γ₂ δ₁ δ₂ : V6}, wE • γ₁ = δ₁ → wE • γ₂ = δ₂ → PairFacts γ₁ γ₂ δ₁ δ₂ →
      (∀ v ∈ Wb, opT (γ₁ + γ₂) v ∈ Wb) ∧ (∀ v ∈ Wb, opT (δ₁ + δ₂) v ∈ Wb) := by
    intro γ₁ γ₂ δ₁ δ₂ hw₁ hw₂ hP
    obtain ⟨α, β, U, hα, hβ, hU, hUl⟩ := exists_rational_S2 D hK hw₁ hw₂ hP
    have hγ : γ₁ + γ₂ ∈ rootFinset Tag.E6 ∧ (γ₁ + γ₂) 1 = 0 :=
      ⟨hP.2.1.2.2, (hP.2.2.2.2 1 one_not_mem_J₂).1⟩
    have hδ : δ₁ + δ₂ ∈ rootFinset Tag.E6 ∧ (δ₁ + δ₂) 1 = 0 :=
      ⟨hP.2.2.1.2.2, (hP.2.2.2.2 1 one_not_mem_J₂).2⟩
    refine algebraize Wb (opT (γ₁ + γ₂)) (opT (δ₁ + δ₂)) (Nat.card K) hq2 α β hα hβ U
      (by nlinarith) ?_
    intro u hu v hv
    obtain ⟨l, hl, hle⟩ := hUl u hu
    have hlL : l ∈ (D.frame TwClass.e6Six.S₁ ⊔ D.frame TwClass.e6Six.S₂) ⊓ Lθ Tag.E6 K :=
      ⟨le_sup_right (a := D.frame TwClass.e6Six.S₁) hl, frame_S₂_le_Lθ D hl⟩
    let P : (V6 → D.L) →ₗ[D.L] (V6 → D.L) :=
      (LinearMap.id + (α * u) • opT (γ₁ + γ₂)) ∘ₗ
        (LinearMap.id + (β * u ^ Nat.card K) • opT (δ₁ + δ₂))
    have hPv : ∀ v, P v = (v + (β * u ^ Nat.card K) • opT (δ₁ + δ₂) v) +
        (α * u) • opT (γ₁ + γ₂) (v + (β * u ^ Nat.card K) • opT (δ₁ + δ₂) v) := by
      intro v
      simp [P]
    rw [← hPv]
    refine hstab_of P (fun w hw => ?_) v hv
    obtain ⟨q₀, hq₀, rfl⟩ := hWq w hw
    have hW1 := hWstab l hlL q₀ hq₀ hw
    have hlq : l * q₀ * l⁻¹ ∈ Qθ Tag.E6 K := Lθ_conj_mem_Qθ (frame_S₂_le_Lθ D hl) hq₀
    obtain ⟨h1, h2⟩ := hι _ hlq
    obtain ⟨h3, h4⟩ := hι q₀ hq₀
    have htr : D.g⁻¹ * baseChangeGL (algebraMap K D.L) (l * q₀ * l⁻¹) * D.g =
        pinnedX Tag.E6 D.L (γ₁ + γ₂) (α * u) *
          (pinnedX Tag.E6 D.L (δ₁ + δ₂) (β * u ^ Nat.card K) *
            (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g) *
            (pinnedX Tag.E6 D.L (δ₁ + δ₂) (β * u ^ Nat.card K))⁻¹) *
          (pinnedX Tag.E6 D.L (γ₁ + γ₂) (α * u))⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      calc D.g⁻¹ * (baseChangeGL (algebraMap K D.L) l * baseChangeGL (algebraMap K D.L) q₀ *
            (baseChangeGL (algebraMap K D.L) l)⁻¹) * D.g
          = (D.g⁻¹ * baseChangeGL (algebraMap K D.L) l * D.g) *
              (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g) *
              (D.g⁻¹ * baseChangeGL (algebraMap K D.L) l * D.g)⁻¹ := by group
        _ = _ := by
          rw [hle]
          group
    obtain ⟨h5, h6⟩ := conj_deg0 hδ.1 hδ.2 (β * u ^ Nat.card K) _ h3
    obtain ⟨_, h8⟩ := conj_deg0 hγ.1 hγ.2 (α * u) _ h5
    have hP' : P (ι (heisCoord Tag.E6 K q₀)) = ι (heisCoord Tag.E6 K (l * q₀ * l⁻¹)) := by
      rw [← h2, htr, h8, h6, h4, hPv]
    rw [hP']
    exact Submodule.subset_span ⟨_, hW1, rfl⟩
  have H1 := hact wE_e02 (by rw [smul_neg, wE_e2]) pf1
  have H2 := hact wE_e02 (by rw [smul_neg, wE_e0]) pf2
  have H3 := hact (by rw [smul_neg, wE_e02]) wE_e2 pf3
  have H4 := hact (by rw [smul_neg, wE_e02]) wE_e0 pf4
  rw [sum1.1, sum1.2] at H1
  rw [sum2.1, sum2.2] at H2
  rw [sum3.1, sum3.2] at H3
  rw [sum4.1, sum4.2] at H4
  have hWbT : ∀ γ ∈ gam0, ∀ v ∈ Wb, opT γ v ∈ Wb := by
    intro γ hγ
    simp only [gam0, List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [H1.1, H2.1, H1.2, H2.2, H3.1, H4.1, H3.2, H4.2]
  obtain ⟨ε, hε, hn⟩ := coord_conj_n (L := D.L) wE_theta
  let Φ : (V6 → D.L) → (V6 → D.L) := fun v ν => ε (wE • ν) * D.Fr (v (wE • ν))
  have hDeg1w : ∀ ν, ν ∈ Deg1 Tag.E6 → wE • ν ∈ Deg1 Tag.E6 := fun ν hν =>
    CoordAux.mem_Deg1.2 ⟨IsRoot.smul (CoordAux.mem_Deg1.1 hν).1 wE, by
      rw [degθ_smul_of_fix wE_theta]; exact (CoordAux.mem_Deg1.1 hν).2⟩
  have hΦfix : ∀ w ∈ W, Φ (ι w) = ι w := by
    intro w hw
    obtain ⟨q₀, hq₀, rfl⟩ := hWq w hw
    obtain ⟨h1, h2⟩ := hι q₀ hq₀
    have hs := sigFix_transport D q₀
    unfold SigFix at hs
    generalize D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g = q' at h1 h2 hs
    have hFq : Units.map (entrywiseHom D.Fr) q' =
        (canonicalRep (coxeterSystem Tag.E6) D.L wE)⁻¹ * q' *
          canonicalRep (coxeterSystem Tag.E6) D.L wE := by
      calc Units.map (entrywiseHom D.Fr) q'
          = (canonicalRep (coxeterSystem Tag.E6) D.L wE)⁻¹ *
              (canonicalRep (coxeterSystem Tag.E6) D.L wE * Units.map (entrywiseHom D.Fr) q' *
                (canonicalRep (coxeterSystem Tag.E6) D.L wE)⁻¹) *
              canonicalRep (coxeterSystem Tag.E6) D.L wE := by group
        _ = _ := by rw [hs]
    obtain ⟨_, h4⟩ := coord_frob D.Fr h1
    obtain ⟨_, h6⟩ := hn _ h1
    have key : ∀ μ ∈ Deg1 Tag.E6,
        D.Fr (heisCoord Tag.E6 D.L q' μ) = ε μ * heisCoord Tag.E6 D.L q' (wE • μ) := by
      intro μ hμ
      have h := congrFun h4 μ
      rw [hFq, h6 μ, if_pos hμ] at h
      exact h.symm
    rw [← h2]
    funext ν
    show ε (wE • ν) * D.Fr (heisCoord Tag.E6 D.L q' (wE • ν)) = _
    by_cases hν : ν ∈ Deg1 Tag.E6
    · rw [key _ (hDeg1w ν hν), wE_invol, ← mul_assoc,
        hε _ (CoordAux.mem_Deg1.1 (hDeg1w ν hν)).1, one_mul]
    · have hwν : wE • ν ∉ Deg1 Tag.E6 := fun h => hν (by
        have := hDeg1w _ h
        rwa [wE_invol] at this)
      rw [hspecL.support _ h1 _ hwν, hspecL.support _ h1 ν hν, map_zero, mul_zero]
  have hΦWb : ∀ v ∈ Wb, Φ v ∈ Wb := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => Φ v ∈ Wb) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨w, hw, rfl⟩
      rw [hΦfix w hw]
      exact Submodule.subset_span ⟨w, hw, rfl⟩
    · have h0 : Φ 0 = 0 := by
        funext ν
        simp [Φ]
      rw [h0]
      exact Wb.zero_mem
    · intro x y _ _ hx hy
      have h : Φ (x + y) = Φ x + Φ y := by
        funext ν
        simp [Φ, mul_add]
      rw [h]
      exact Wb.add_mem hx hy
    · intro c x _ hx
      have h : Φ (c • x) = D.Fr c • Φ x := by
        funext ν
        simp [Φ]
        ring
      rw [h]
      exact Wb.smul_mem _ hx
  have hΦsingle : ∀ μ : V6, Φ (Pi.single μ 1) = Pi.single (wE • μ) (ε μ) := by
    intro μ
    funext ν
    show ε (wE • ν) * D.Fr ((Pi.single μ (1 : D.L) : V6 → D.L) (wE • ν)) = _
    by_cases h : ν = wE • μ
    · subst h
      rw [wE_invol, Pi.single_eq_same, Pi.single_eq_same, map_one, mul_one]
    · have h' : wE • ν ≠ μ := fun e => h (by rw [← e, wE_invol])
      rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h, map_zero, mul_zero]
  have hWbΦ : ∀ μ ∈ Mlist, (Pi.single μ (1 : D.L) : V6 → D.L) ∈ Wb →
      (Pi.single (wE • μ) (1 : D.L) : V6 → D.L) ∈ Wb := by
    intro μ hμ h
    have h1 := hΦWb _ h
    rw [hΦsingle] at h1
    have hεμ : ε μ ≠ 0 := by
      intro h0
      have := hε μ (mem_rootFinset.1 (Mlist_facts μ hμ).1)
      rw [h0, mul_zero] at this
      exact zero_ne_one this
    have h2 := Wb.smul_mem (ε μ)⁻¹ h1
    rwa [← Pi.single_smul', smul_eq_mul, inv_mul_cancel₀ hεμ] at h2
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  have hWb0 : Wb ≠ ⊥ := by
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).1 hW0
    intro hbot
    have h1 : ι w ∈ Wb := Submodule.subset_span ⟨w, hw, rfl⟩
    rw [hbot, Submodule.mem_bot] at h1
    have h2 : f' (ι w) = alg w := hff _ (halgdeg w (hVMdeg w (hWM hw)))
    rw [h1, map_zero] at h2
    apply hw0
    funext β
    have h3 := congrFun h2 β
    simp only [alg, Pi.zero_apply] at h3
    rw [Pi.zero_apply]
    exact (algebraMap K D.L).injective (by rw [← h3, map_zero])
  have hall := core Wb hWbsupp hWbT hWbΦ hWb0
  refine le_antisymm hWM (fun v hv => ?_)
  have hιv : ι v ∈ Wb := by
    have e : ι v = ∑ μ ∈ Mlist.toFinset, ι v μ • (Pi.single μ 1 : V6 → D.L) := by
      funext ν
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, List.mem_toFinset]
      split_ifs with h
      · rfl
      · exact hsuppVM v hv ν h
    rw [e]
    exact Submodule.sum_mem _ fun μ hμ => Wb.smul_mem _ (hall μ (List.mem_toFinset.1 hμ))
  have h1 : f' (ι v) = alg v := hff _ (halgdeg v (hVMdeg v hv))
  have h2 : f' (ι v) ∈ Submodule.span D.L (alg '' (W : Set (V6 → K))) := by
    have h3 : f' (ι v) ∈ Wb.map f' := Submodule.mem_map_of_mem hιv
    rw [Submodule.map_span] at h3
    have h4 : f' '' (ι '' (W : Set (V6 → K))) = alg '' (W : Set (V6 → K)) := by
      rw [Set.image_image]
      exact Set.image_congr fun w hw => hff _ (halgdeg w (hVMdeg w (hWM hw)))
    rwa [h4] at h3
  rw [h1] at h2
  exact mem_of_mem_span_map W h2

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredE6Aux
