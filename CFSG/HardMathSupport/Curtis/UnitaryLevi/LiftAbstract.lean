module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftAct
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockCentGlue

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi.Lift

open scoped commutatorElement

variable {G Y : Type*} [Group G] [Group Y]

@[expose] def actD (Lb Pb D : Subgroup Y) (hPL : Pb ≤ Lb) : Subgroup Y where
  carrier := {p | p ∈ Pb ∧ ∃ y ∈ D, Act Lb y p}
  mul_mem' := by
    rintro a b ⟨ha, y, hy, hya⟩ ⟨hb, y', hy', hyb⟩
    exact ⟨Pb.mul_mem ha hb, y * y', D.mul_mem hy hy', act_mul (hPL hb) hya hyb⟩
  one_mem' := ⟨Pb.one_mem, 1, D.one_mem, act_one⟩
  inv_mem' := by
    rintro a ⟨ha, y, hy, hya⟩
    exact ⟨Pb.inv_mem ha, y⁻¹, D.inv_mem hy, act_inv (hPL ha) hya⟩

@[expose] def actSub (Lb E : Subgroup Y) (hE : E ≤ Lb) : Subgroup Y where
  carrier := {y | ∃ p ∈ E, Act Lb y p}
  mul_mem' := by
    rintro a b ⟨p, hp, ha⟩ ⟨p', hp', hb⟩
    exact ⟨p * p', E.mul_mem hp hp', act_mul (hE hp') ha hb⟩
  one_mem' := ⟨1, E.one_mem, act_one⟩
  inv_mem' := by
    rintro a ⟨p, hp, ha⟩
    exact ⟨p⁻¹, E.inv_mem hp, act_inv (hE hp) ha⟩

theorem commutator_le_self' (H : Subgroup Y) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun _ ha _ hb =>
    H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem exists_mul_of_mem_sup_of_commute {s t : Subgroup Y}
    (hc : ∀ a ∈ s, ∀ b ∈ t, a * b = b * a) {x : Y} (hx : x ∈ s ⊔ t) :
    ∃ a ∈ s, ∃ b ∈ t, a * b = x := by
  let T : Subgroup Y :=
    { carrier := {x | ∃ a ∈ s, ∃ b ∈ t, a * b = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', s.mul_mem ha ha', b * b', t.mul_mem hb hb', ?_⟩
        have := hc a' ha' b hb
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [this]
          _ = _ := by group
      one_mem' := ⟨1, s.one_mem, 1, t.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, s.inv_mem ha, b⁻¹, t.inv_mem hb, ?_⟩
        have := hc a ha b hb
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = _ := by rw [← this] }
  have : s ⊔ t ≤ T := sup_le (fun a ha => ⟨a, ha, 1, t.one_mem, by simp⟩)
    (fun b hb => ⟨1, s.one_mem, b, hb, by simp⟩)
  exact this hx

theorem exists_act_of_mem {Lb Pb D : Subgroup Y} (hPL : Pb ≤ Lb)
    (hDle : D ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y)) {y : Y} (hy : y ∈ D) :
    ∃ p ∈ Pb, Act Lb y p := by
  obtain ⟨p, hp, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun a ha b hb => (Subgroup.mem_centralizer_iff.1 hb a (hPL ha))) (hDle hy)
  refine ⟨p, hp, fun l hl => ?_⟩
  have h1 : l * c = c * l := Subgroup.mem_centralizer_iff.1 hc l hl
  calc p * c * l * (p * c)⁻¹ = p * (c * l * c⁻¹) * p⁻¹ := by group
    _ = p * l * p⁻¹ := by rw [← h1]; group

theorem exists_mem_commutator_actD {Lb Pb D : Subgroup Y} (hPL : Pb ≤ Lb) (hDperf : ⁅D, D⁆ = D)
    (hDle : D ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y)) {p : Y} (hp : p ∈ actD Lb Pb D hPL) :
    ∃ p' ∈ ⁅actD Lb Pb D hPL, actD Lb Pb D hPL⁆, p⁻¹ * p' ∈ ZL Lb := by
  obtain ⟨hpP, y, hy, hya⟩ := hp
  have hle : ⁅actD Lb Pb D hPL, actD Lb Pb D hPL⁆ ≤ Lb :=
    (commutator_le_self' _).trans (fun q hq => hPL hq.1)
  have hsub : ⁅D, D⁆ ≤ actSub Lb ⁅actD Lb Pb D hPL, actD Lb Pb D hPL⁆ hle := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨pa, hpa, haa⟩ := exists_act_of_mem hPL hDle ha
    obtain ⟨pb, hpb, hbb⟩ := exists_act_of_mem hPL hDle hb
    have hpa' : pa ∈ actD Lb Pb D hPL := ⟨hpa, a, ha, haa⟩
    have hpb' : pb ∈ actD Lb Pb D hPL := ⟨hpb, b, hb, hbb⟩
    refine ⟨⁅pa, pb⁆, Subgroup.commutator_mem_commutator hpa' hpb', ?_⟩
    rw [commutatorElement_def, commutatorElement_def]
    exact act_mul (hPL (Pb.inv_mem hpb)) (act_mul (hPL (Pb.inv_mem hpa)) (act_mul (hPL hpb) haa hbb)
      (act_inv (hPL hpa) haa)) (act_inv (hPL hpb) hbb)
  obtain ⟨p', hp', hyp'⟩ := hsub (hDperf ▸ hy)
  exact ⟨p', hp', act_comm (hPL hpP) (hle hp') hya hyp'⟩

theorem commutator_perfect_of_le_sup_center (H : Subgroup G)
    (h : H ≤ ⁅H, H⁆ ⊔ Subgroup.center G) : ⁅⁅H, H⁆, ⁅H, H⁆⁆ = ⁅H, H⁆ := by
  refine le_antisymm (commutator_le_self' _) ?_
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (h ha)
  obtain ⟨n', hn', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (h hb)
  have e : ⁅n * z, n' * z'⁆ = ⁅n, n'⁆ := by
    have cz : ∀ w, z * w * z⁻¹ = w := fun w => by
      rw [← Subgroup.mem_center_iff.1 hz w]; group
    have cz' : ∀ w, z' * w * z'⁻¹ = w := fun w => by
      rw [← Subgroup.mem_center_iff.1 hz' w]; group
    calc ⁅n * z, n' * z'⁆ = n * (z * (n' * z') * z⁻¹) * n⁻¹ * (z'⁻¹ * n'⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = n * n' * (z' * n⁻¹ * z'⁻¹) * n'⁻¹ := by rw [cz]; group
      _ = ⁅n, n'⁆ := by rw [cz', commutatorElement_def]
  rw [e]
  exact Subgroup.commutator_mem_commutator hn hn'

theorem commutator_mul_central {p q c c' : Y} (hcq : c * q = q * c)
    (hc'p : c' * p = p * c') (hcc : c * c' = c' * c) :
    ⁅p * c, q * c'⁆ = ⁅p, q⁆ := by
  have h1 : c * (q * c') * c⁻¹ = q * c' := by
    have : c * (q * c') = (q * c') * c := by
      rw [← mul_assoc, hcq, mul_assoc, mul_assoc, hcc]
    rw [this]; group
  have h2 : c' * p⁻¹ * c'⁻¹ = p⁻¹ := by
    have : c' * p⁻¹ = p⁻¹ * c' := by
      have := congrArg (fun t => p⁻¹ * t * p⁻¹) hc'p
      simp only [mul_assoc, inv_mul_cancel_left] at this
      simpa [mul_assoc] using this.symm
    rw [this]; group
  calc ⁅p * c, q * c'⁆ = p * (c * (q * c') * c⁻¹) * p⁻¹ * (q * c')⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = p * q * (c' * p⁻¹ * c'⁻¹) * q⁻¹ := by rw [h1]; group
    _ = ⁅p, q⁆ := by rw [h2, commutatorElement_def]

theorem exists_lifted_abstract [Finite G] [Finite Y] (ρ : G →* Y) {Lb Pb D : Subgroup Y} {x : Y}
    (hPL : Pb ≤ Lb) (hρL : ∀ g, ρ g ∈ Lb) (hsurj : ∀ l ∈ Lb, ∃ g, ρ g = l)
    (hcY : ∀ g, ρ g ∈ ZL Lb ↔ g ∈ Subgroup.center G)
    (hrank3 : CFSG.Open.pRank 3 Pb ≤ 3)
    (hcycY : ∀ V : Subgroup Y, V ≤ Pb → ⁅V, V⁆ = V → ∀ A : Subgroup Y, A ≤ V → IsPGroup 3 A →
      IsCyclic A)
    (hDperf : ⁅D, D⁆ = D) (hDle : D ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y))
    (hx : x ∈ D) (hx3 : x ^ 3 = 1) (hxC : x ∉ Subgroup.centralizer (Lb : Set Y))
    (hfreeY : ∀ W : Subgroup Y, W ≤ Lb → ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({x} : Set Y) → W = ⊥) :
    ∃ Dt : Subgroup G, Dt ≤ Pb.comap ρ ∧ ⁅Dt, Dt⁆ = Dt ∧ ∃ d ∈ Dt,
      d ∉ Subgroup.center G ∧ d ^ 3 ∈ Subgroup.center G ∧
      (∀ H : Subgroup G, ⁅H, H⁆ = H → (∀ w ∈ H, Commute w d) → H = ⊥) ∧
      (∀ V : Subgroup G, V ≤ Pb.comap ρ → ⁅V, V⁆ = V → ∀ A : Subgroup G, A ≤ V → IsPGroup 3 A →
        IsCyclic (A.map (QuotientGroup.mk' (Subgroup.center G)))) ∧
      (∀ A : Subgroup G, A ≤ Pb.comap ρ → CFSG.Open.IsElemAbelian 3 A →
        A ⊓ Subgroup.center G = ⊥ → ∀ j : ℕ, Nat.card A = 3 ^ j → j ≤ 3) ∧
      (∀ u : Y, u ∈ Subgroup.normalizer (Lb : Set Y) → u ∈ Subgroup.centralizer (D : Set Y) →
        ∀ g ∈ Dt, u * ρ g * u⁻¹ = ρ g) := by
  classical
  set D₁ := actD Lb Pb D hPL with hD₁
  set Dt₁ : Subgroup G := D₁.comap ρ with hDt₁
  have hD1P : ∀ p ∈ D₁, p ∈ Pb := fun p hp => hp.1
  have hD1L : D₁ ≤ Lb := fun p hp => hPL hp.1
  have hker : ∀ g ∈ ρ.ker, g ∈ Subgroup.center G := fun g hg => by
    rw [← hcY, MonoidHom.mem_ker.1 hg]; exact (ZL Lb).one_mem
  have hmapDt : (⁅Dt₁, Dt₁⁆).map ρ = ⁅D₁, D₁⁆ := by
    have hle : D₁ ≤ ρ.range := fun p hp => by
      obtain ⟨g, hg⟩ := hsurj p (hD1L hp)
      exact ⟨g, hg⟩
    have h1 : Dt₁.map ρ = D₁ := by
      rw [hDt₁, Subgroup.map_comap_eq, inf_eq_right.2 hle]
    rw [Subgroup.map_commutator, h1]
  have hDt1 : Dt₁ ≤ ⁅Dt₁, Dt₁⁆ ⊔ Subgroup.center G := by
    intro g hg
    obtain ⟨p', hp', hz⟩ := exists_mem_commutator_actD hPL hDperf hDle (show ρ g ∈ D₁ from hg)
    rw [← hmapDt] at hp'
    obtain ⟨n, hn, hnp⟩ := hp'
    refine Subgroup.mem_sup_of_normal_right.2 ⟨n, hn, n⁻¹ * g, ?_, by group⟩
    rw [← hcY, map_mul, map_inv, hnp]
    have := (ZL Lb).inv_mem hz
    simpa using this
  have hperf : ⁅⁅Dt₁, Dt₁⁆, ⁅Dt₁, Dt₁⁆⁆ = ⁅Dt₁, Dt₁⁆ := commutator_perfect_of_le_sup_center _ hDt1
  set Dt : Subgroup G := ⁅Dt₁, Dt₁⁆ with hDt
  have hDtD1 : Dt ≤ Dt₁ := commutator_le_self' _
  obtain ⟨p, hpP, hxp⟩ := exists_act_of_mem hPL hDle hx
  have hpD1 : p ∈ D₁ := ⟨hpP, x, hx, hxp⟩
  obtain ⟨g0, hg0⟩ := hsurj p (hPL hpP)
  have hg0Dt1 : g0 ∈ Dt₁ := by show ρ g0 ∈ D₁; rw [hg0]; exact hpD1
  obtain ⟨n, hn, z, hz, hnz⟩ := Subgroup.mem_sup_of_normal_right.1 (hDt1 hg0Dt1)
  have hxd : Act Lb x (ρ n) := by
    refine act_of_central ?_ hxp
    have : p⁻¹ * ρ n = (ρ z)⁻¹ := by
      rw [← hg0, ← hnz, map_mul]; group
    rw [this]
    exact (ZL Lb).inv_mem ((hcY z).2 hz)
  have hρn : ρ n ∈ Lb := hρL n
  refine ⟨Dt, fun g hg => hD1P _ (hDtD1 hg), hperf, n, hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hc
    apply hxC
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := act_one_of_mem_ZL ((hcY n).2 hc) l hl
    have h2 := hxd l hl
    have : x * l * x⁻¹ = l := by rw [h2, ← h1]; simp
    calc l * x = (x * l * x⁻¹) * x := by rw [this]
      _ = x * l := by group
  · have h3 := act_pow hρn hxd 3
    rw [hx3] at h3
    rw [← hcY, map_pow]
    exact mem_ZL_of_act_one (Lb.pow_mem hρn 3) h3
  · intro H hH hcomm
    have hW : (H.map ρ) ≤ Lb := by rintro _ ⟨w, -, rfl⟩; exact hρL w
    have hWperf : ⁅H.map ρ, H.map ρ⁆ = H.map ρ := by rw [← Subgroup.map_commutator, hH]
    have hWc : H.map ρ ≤ Subgroup.centralizer ({x} : Set Y) := by
      rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have h1 := hxd (ρ w) (hρL w)
      have h2 : ρ n * ρ w * (ρ n)⁻¹ = ρ w := by
        rw [← map_mul, ← map_inv, ← map_mul]
        have : n * w * n⁻¹ = w := by
          have := (hcomm w hw).eq
          calc n * w * n⁻¹ = w * n * n⁻¹ := by rw [this]
            _ = w := by group
        rw [this]
      rw [h2] at h1
      calc x * ρ w = (x * ρ w * x⁻¹) * x := by group
        _ = ρ w * x := by rw [h1]
    have hbot := hfreeY _ hW hWperf hWc
    have hHc : H ≤ Subgroup.center G := fun w hw => hker w (by
      have : ρ w ∈ H.map ρ := ⟨w, hw, rfl⟩
      rw [hbot] at this
      exact this)
    rw [← le_bot_iff, ← hH]
    refine Subgroup.commutator_le.2 fun a ha b _ => ?_
    have := Subgroup.mem_center_iff.1 (hHc ha) b
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact this.symm
  ·
    intro V hV hVp A hAV hA3
    have hVP : V.map ρ ≤ Pb := by rintro _ ⟨v, hv, rfl⟩; exact hV hv
    have hVperf : ⁅V.map ρ, V.map ρ⁆ = V.map ρ := by rw [← Subgroup.map_commutator, hVp]
    have hcyc : IsCyclic (A.map ρ) :=
      hcycY _ hVP hVperf _ (Subgroup.map_mono hAV) (hA3.map ρ)
    let ψ₁ : A →* A.map ρ := ρ.subgroupMap A
    let ψ₂ : A →* A.map (QuotientGroup.mk' (Subgroup.center G)) :=
      (QuotientGroup.mk' (Subgroup.center G)).subgroupMap A
    have hs1 : Function.Surjective ψ₁ := MonoidHom.subgroupMap_surjective ρ A
    have hs2 : Function.Surjective ψ₂ := MonoidHom.subgroupMap_surjective _ A
    have hk : ψ₁.ker ≤ ψ₂.ker := by
      intro a ha
      rw [MonoidHom.mem_ker] at ha ⊢
      have h1 : ρ (a : G) = 1 := congrArg Subtype.val ha
      have h2 := hker _ h1
      apply Subtype.ext
      show QuotientGroup.mk' (Subgroup.center G) (a : G) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h2
    let φ : A.map ρ →* A.map (QuotientGroup.mk' (Subgroup.center G)) :=
      MonoidHom.liftOfRightInverse ψ₁ (Function.surjInv hs1) (Function.rightInverse_surjInv hs1) ⟨ψ₂, hk⟩
    have hφ : Function.Surjective φ := by
      intro t
      obtain ⟨a, ha⟩ := hs2 t
      refine ⟨ψ₁ a, ?_⟩
      show (MonoidHom.liftOfRightInverse ψ₁ (Function.surjInv hs1)
        (Function.rightInverse_surjInv hs1) ⟨ψ₂, hk⟩) (ψ₁ a) = t
      rw [MonoidHom.liftOfRightInverse_comp_apply]
      exact ha
    exact isCyclic_of_surjective φ hφ
  · intro A hA hAe hAZ j hj
    exact card_le_of_pRank_of_comap ρ hker Pb hrank3 hA hAe hAZ hj
  · intro u hu huD g hg
    have hnorm : ∀ l, l ∈ Lb → u⁻¹ * l * u ∈ Lb := fun l hl => by
      have := (Subgroup.mem_normalizer_iff.1 hu (u⁻¹ * l * u)).2
        (by rwa [show u * (u⁻¹ * l * u) * u⁻¹ = l by group])
      exact this
    have hnorm' : ∀ l, l ∈ Lb → u * l * u⁻¹ ∈ Lb := fun l hl =>
      (Subgroup.mem_normalizer_iff.1 hu l).1 hl
    have hcent : ∀ a ∈ Dt₁, (ρ a)⁻¹ * (u * ρ a * u⁻¹) ∈ ZL Lb := by
      intro a ha
      obtain ⟨hpa, y, hy, hya⟩ : ρ a ∈ D₁ := ha
      have hyu : y * u = u * y := Subgroup.mem_centralizer_iff.1 huD y hy
      refine act_comm (hPL hpa) (hnorm' _ (hPL hpa)) hya ?_
      intro l hl
      have h1 := hya (u⁻¹ * l * u) (hnorm l hl)
      have hy' : u * y * u⁻¹ = y := by rw [← hyu]; group
      calc y * l * y⁻¹ = (u * y * u⁻¹) * l * (u * y * u⁻¹)⁻¹ := by rw [hy']
        _ = u * (y * (u⁻¹ * l * u) * y⁻¹) * u⁻¹ := by group
        _ = u * (ρ a * (u⁻¹ * l * u) * (ρ a)⁻¹) * u⁻¹ := by rw [h1]
        _ = (u * ρ a * u⁻¹) * l * (u * ρ a * u⁻¹)⁻¹ := by group
    let T : Subgroup G := Dt ⊓ (Subgroup.centralizer ({u} : Set Y)).comap ρ
    have hDtT : Dt ≤ T := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      refine ⟨Subgroup.commutator_mem_commutator ha hb, ?_⟩
      show ρ ⁅a, b⁆ ∈ Subgroup.centralizer ({u} : Set Y)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      obtain ⟨hca, hcaL⟩ := mem_ZL.1 (hcent a ha)
      obtain ⟨hcb, hcbL⟩ := mem_ZL.1 (hcent b hb)
      set ca := (ρ a)⁻¹ * (u * ρ a * u⁻¹) with hcadef
      set cb := (ρ b)⁻¹ * (u * ρ b * u⁻¹) with hcbdef
      have ea : u * ρ a * u⁻¹ = ρ a * ca := by rw [hcadef]; group
      have eb : u * ρ b * u⁻¹ = ρ b * cb := by rw [hcbdef]; group
      have hcomm : u * ρ ⁅a, b⁆ * u⁻¹ = ρ ⁅a, b⁆ := by
        have : u * ρ ⁅a, b⁆ * u⁻¹ = ⁅u * ρ a * u⁻¹, u * ρ b * u⁻¹⁆ := by
          rw [map_commutatorElement]; simp only [commutatorElement_def]; group
        rw [this, ea, eb, commutator_mul_central (hcaL _ (hρL b)).symm
          (hcbL _ (hρL a)).symm (hcbL _ hca), map_commutatorElement]
      calc u * ρ ⁅a, b⁆ = (u * ρ ⁅a, b⁆ * u⁻¹) * u := by group
        _ = ρ ⁅a, b⁆ * u := by rw [hcomm]
    exact (hDtT hg).2 |> fun h => by
      have := Subgroup.mem_centralizer_iff.1 h u rfl
      calc u * ρ g * u⁻¹ = (ρ g * u) * u⁻¹ := by rw [this]
        _ = ρ g := by group

end CFSG.HardMathSupport.Curtis.UnitaryLevi.Lift
