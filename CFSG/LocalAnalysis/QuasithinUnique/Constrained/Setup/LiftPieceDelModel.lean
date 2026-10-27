module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelPerm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelVec
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilySplit

public section

namespace CFSG.QuasithinUnique.Setup.Lift.Piece

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.Lift
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement

universe v

section Reduction

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_displacement_in_Ii {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {F : Type} [Field F] {r : ℕ}
    {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)} (layer : EvenSL2LayerOutput H T r F Lc)
    (common : EvenSL2FamilyCommon H T r Lc) (i : Fin r) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ Lc i)
    (u : V) : ∃ u' ∈ commGL (Lc i) ⊤, g u - u = g u' - u' := by
  have hu : u ∈ (⨆ j, commGL (Lc j) ⊤) ⊔ fixGL (oddGen H) := by
    rw [common.V_sum]
    exact Submodule.mem_top
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hu
  have hgK : g ∈ oddGen H := by
    rw [layer.K_eq]
    exact (le_iSup Lc i) hg
  have hgc : g c = c := hc g hgK
  suffices h : ∃ u' ∈ commGL (Lc i) ⊤, g a - a = g u' - u' by
    obtain ⟨u', hu', h⟩ := h
    refine ⟨u', hu', ?_⟩
    rw [map_add, hgc]
    rw [← h]
    abel
  refine Submodule.iSup_induction (fun j => commGL (Lc j) ⊤)
    (motive := fun a => ∃ u' ∈ commGL (Lc i) ⊤, g a - a = g u' - u') ha ?_ ?_ ?_
  · intro j a haj
    by_cases hji : j = i
    · subst hji
      exact ⟨a, haj, rfl⟩
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [layer.others_fix j i (Ne.symm hji) g hg a haj]
      simp
  · exact ⟨0, Submodule.zero_mem _, by simp⟩
  · rintro a₁ a₂ ⟨u₁, hu₁, h₁⟩ ⟨u₂, hu₂, h₂⟩
    refine ⟨u₁ + u₂, Submodule.add_mem _ hu₁ hu₂, ?_⟩
    rw [map_add, map_add]
    have : g a₁ + g a₂ - (a₁ + a₂) = (g a₁ - a₁) + (g a₂ - a₂) := by abel
    rw [this, h₁, h₂]
    abel

theorem commGL_eq_commGL_Ii {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {F : Type} [Field F] {r : ℕ}
    {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)} (layer : EvenSL2LayerOutput H T r F Lc)
    (common : EvenSL2FamilyCommon H T r Lc) (i : Fin r) {Fs : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hFs : Fs ≤ Lc i) : commGL Fs ⊤ = commGL Fs (commGL (Lc i) ⊤) := by
  refine le_antisymm ?_ (commSub_mono_right _ le_top)
  rw [commSub_le_iff]
  intro g hg u _
  obtain ⟨u', hu', h⟩ := exists_displacement_in_Ii layer common i (hFs hg) u
  show g u - u ∈ _
  rw [h]
  exact mem_commSub_of hg hu'

end Reduction

section Vectors

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] in
theorem permAct_pair {σ : Equiv.Perm Ω} {p : Ω} (hp : σ p = p) (s : Ω) :
    permAct σ (delta s + delta p) - (delta s + delta p) = delta (σ s) - delta s := by
  rw [permAct_add, permAct_delta, permAct_delta, hp]
  abel

omit [Fintype Ω] [DecidableEq Ω] in
theorem permAct_sub_apply_of_fix {g : Equiv.Perm Ω} {t : Ω} (ht : g t = t) (y : Ω → ZMod 2) :
    (permAct g y - y) t = 0 := by
  rw [Pi.sub_apply, permAct_apply, (Equiv.symm_apply_eq g).2 ht.symm]
  exact sub_self _

theorem sum_five {f : Ω → ZMod 2} {x y z p q : Ω}
    (hall : ∀ t : Ω, t = x ∨ t = y ∨ t = z ∨ t = p ∨ t = q) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hpq : p ≠ q) (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z) (hqx : q ≠ x)
    (hqy : q ≠ y) (hqz : q ≠ z) : ∑ t, f t = f x + f y + f z + f p + f q := by
  have hU : (Finset.univ : Finset Ω) = {x, y, z, p, q} := by
    ext t
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hall t
  rw [hU, Finset.sum_insert (by simp [hxy, hxz, Ne.symm hpx, Ne.symm hqx]),
    Finset.sum_insert (by simp [hyz, Ne.symm hpy, Ne.symm hqy]),
    Finset.sum_insert (by simp [Ne.symm hpz, Ne.symm hqz]),
    Finset.sum_insert (by simp [hpq]), Finset.sum_singleton]
  abel

end Vectors

section Main

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

theorem deleted_cycle_module [Finite V] {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {F : Type} [Field F] {r : ℕ}
    {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)} (layer : EvenSL2LayerOutput H T r F Lc)
    (common : EvenSL2FamilyCommon H T r Lc) (i : Fin r)
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (h5 : Fintype.card Ω = 5)
    (ψi : ↥(blockB H (Lc i)) ≃* Equiv.Perm Ω)
    (βi : ↥(commGL (Lc i) ⊤) ≃ₗ[ZMod 2] ↥(SL2Modules.evenWeight Ω))
    (hcompat : ∀ (b : ↥(blockB H (Lc i))) (u u' : ↥(commGL (Lc i) ⊤)),
      (u' : V) = (b : V ≃ₗ[ZMod 2] V) (u : V) →
        ((βi u' : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2) =
          permAct (ψi b) ((βi u : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2))
    {a b c d ω : Ω} (hall : ∀ t : Ω, t = a ∨ t = b ∨ t = c ∨ t = d ∨ t = ω) (hab : a ≠ b)
    (hcd : c ≠ d) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : (A.subgroupOf (blockB H (Lc i))).map ψi.toMonoidHom =
      Subgroup.closure {Equiv.swap a b, Equiv.swap c d})
    {Fs : Subgroup (V ≃ₗ[ZMod 2] V)} (hFs : Fs ≤ Lc i) (hcard : Nat.card Fs = 3) :
    Nat.card ↥(commGL Fs ⊤) = 4 ∧
      (∃ f ∈ Fs, f ≠ 1 ∧ ∀ w ∈ commGL Fs ⊤, f w = w → w = 0) ∧
      ∃ x ∈ A, ∃ w ∈ commGL Fs ⊤, x w ≠ w := by
  classical
  have hLB : Lc i ≤ blockB H (Lc i) := common.L_le_B i
  have hFB : Fs ≤ blockB H (Lc i) := hFs.trans hLB
  set Fs₀ : Subgroup (Equiv.Perm Ω) := (Fs.subgroupOf (blockB H (Lc i))).map ψi.toMonoidHom
    with hFs₀def
  have hFs₀ : Nat.card Fs₀ = 3 := by
    rw [hFs₀def, Subgroup.card_map_of_injective ψi.injective, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFB).toEquiv
  have hFne : Fs₀ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hFs₀
    omega
  obtain ⟨⟨σ, hσ⟩, hσ1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hFne
  have hσ1 : σ ≠ 1 := fun h => hσ1' (Subtype.ext h)
  have hσ3 : σ ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥Fs₀) (x := (⟨σ, hσ⟩ : ↥Fs₀))
    rw [hFs₀] at h
    exact congrArg Subtype.val h
  have hFs₀gen : Subgroup.zpowers σ = Fs₀ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hσ) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hσ3 hσ1, hFs₀]
  obtain ⟨x, y, z, p, q, hxy, hxz, hyz, hpq, hpx, hpy, hpz, hqx, hqy, hqz, hσx, hσy, hσz, hσp,
    hσq, hallxyz⟩ := exists_cycle_points h5 σ hσ3 hσ1
  have hfixpq : ∀ g' ∈ Fs₀, g' p = p ∧ g' q = q := by
    intro g' hg'
    rw [← hFs₀gen] at hg'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg'
    exact ⟨Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hσp k,
      Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hσq k⟩
  obtain ⟨f', hf', hf'σ⟩ := Subgroup.mem_map.1 hσ
  have hfFs : (f' : V ≃ₗ[ZMod 2] V) ∈ Fs := hf'
  have hfLc : (f' : V ≃ₗ[ZMod 2] V) ∈ Lc i := hFs hfFs
  have hInv : ∀ g ∈ Lc i, ∀ u ∈ commGL (Lc i) ⊤, g u ∈ commGL (Lc i) ⊤ := fun g hg u hu =>
    isInvariant_commGL_self (Lc i) g hg u hu
  have hWI : commGL Fs ⊤ ≤ commGL (Lc i) ⊤ := by
    rw [commGL_eq_commGL_Ii layer common i hFs]
    exact commSub_le_of_isInvariant (fun g hg u hu => hInv g (hFs hg) u hu)
  have hvec : ∀ s : Ω, ∃ (u : ↥(commGL (Lc i) ⊤)) (hw : (f' : V ≃ₗ[ZMod 2] V) (u : V) - (u : V) ∈ commGL (Lc i) ⊤),
      ((βi ⟨(f' : V ≃ₗ[ZMod 2] V) (u : V) - (u : V), hw⟩ : ↥(SL2Modules.evenWeight Ω)) :
        Ω → ZMod 2) = delta (σ s) - delta s := by
    intro s
    let u : ↥(commGL (Lc i) ⊤) := βi.symm ⟨delta s + delta p, delta_add_delta_mem s p⟩
    have hfu : (f' : V ≃ₗ[ZMod 2] V) (u : V) ∈ commGL (Lc i) ⊤ := hInv _ hfLc _ u.2
    have hw : (f' : V ≃ₗ[ZMod 2] V) (u : V) - (u : V) ∈ commGL (Lc i) ⊤ :=
      (commGL (Lc i) ⊤).sub_mem hfu u.2
    refine ⟨u, hw, ?_⟩
    have hc := hcompat ⟨f', hFB hfFs⟩ u ⟨(f' : V ≃ₗ[ZMod 2] V) (u : V), hfu⟩ rfl
    have hψ : ψi ⟨f', hFB hfFs⟩ = σ := hf'σ
    rw [hψ] at hc
    have hβu : ((βi u : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2) = delta s + delta p := by
      simp [u]
    have e1 : (⟨(f' : V ≃ₗ[ZMod 2] V) (u : V), hfu⟩ : ↥(commGL (Lc i) ⊤)) =
        ⟨(f' : V ≃ₗ[ZMod 2] V) (u : V) - (u : V), hw⟩ + u :=
      Subtype.ext (by simp)
    have hadd := congrArg (fun t : ↥(commGL (Lc i) ⊤) => ((βi t : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2)) e1
    simp only [map_add, Submodule.coe_add] at hadd
    rw [hc, hβu] at hadd
    rw [eq_sub_of_add_eq hadd.symm]
    exact permAct_pair hσp s
  choose us hws hβws using hvec
  have hmem : ∀ s : Ω, (f' : V ≃ₗ[ZMod 2] V) (us s : V) - (us s : V) ∈ commGL Fs ⊤ := fun s =>
    commSub_mono_right _ le_top (mem_commSub_of hfFs (us s).2)
  let cl : ↥(commGL Fs ⊤) →ₗ[ZMod 2] (Ω → ZMod 2) :=
    (SL2Modules.evenWeight Ω).subtype ∘ₗ βi.toLinearMap ∘ₗ Submodule.inclusion hWI
  have hcl : ∀ w : ↥(commGL Fs ⊤), cl w = ((βi ⟨w.1, hWI w.2⟩ : ↥(SL2Modules.evenWeight Ω)) :
      Ω → ZMod 2) := fun w => rfl
  have hclinj : Function.Injective cl := by
    intro w₁ w₂ h
    rw [hcl, hcl] at h
    have h1 : βi ⟨w₁.1, hWI w₁.2⟩ = βi ⟨w₂.1, hWI w₂.2⟩ := Subtype.ext h
    have h2 := βi.injective h1
    exact Subtype.ext (Subtype.mk.inj h2)
  have hclsum : ∀ w : ↥(commGL Fs ⊤), cl w x + cl w y + cl w z + cl w p + cl w q = 0 := by
    intro w
    rw [← sum_five hallxyz hxy hxz hyz hpq hpx hpy hpz hqx hqy hqz]
    exact (βi ⟨w.1, hWI w.2⟩).2
  have hvan : ∀ w ∈ commGL Fs ⊤, ∃ hw : w ∈ commGL (Lc i) ⊤,
      ((βi ⟨w, hw⟩ : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2) p = 0 ∧
      ((βi ⟨w, hw⟩ : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2) q = 0 := by
    intro w hw
    rw [commGL_eq_commGL_Ii layer common i hFs] at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, hg, u, hu, rfl⟩ := hw
      have hgu : g u ∈ commGL (Lc i) ⊤ := hInv g (hFs hg) u hu
      have hw' : (MonoidHom.id (V ≃ₗ[ZMod 2] V)) g u - u ∈ commGL (Lc i) ⊤ :=
        (commGL (Lc i) ⊤).sub_mem hgu hu
      refine ⟨hw', ?_⟩
      have hγ : ψi ⟨g, hFB hg⟩ ∈ Fs₀ :=
        Subgroup.mem_map_of_mem ψi.toMonoidHom (Subgroup.mem_subgroupOf.2 hg)
      obtain ⟨hγp, hγq⟩ := hfixpq _ hγ
      have hc := hcompat ⟨g, hFB hg⟩ ⟨u, hu⟩ ⟨g u, hgu⟩ rfl
      have e1 : (⟨g u, hgu⟩ : ↥(commGL (Lc i) ⊤)) =
          ⟨(MonoidHom.id (V ≃ₗ[ZMod 2] V)) g u - u, hw'⟩ + ⟨u, hu⟩ := Subtype.ext (by simp)
      have hadd := congrArg
        (fun t : ↥(commGL (Lc i) ⊤) => ((βi t : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2)) e1
      simp only [map_add, Submodule.coe_add] at hadd
      rw [hc] at hadd
      rw [eq_sub_of_add_eq hadd.symm]
      exact ⟨permAct_sub_apply_of_fix hγp _, permAct_sub_apply_of_fix hγq _⟩
    | zero =>
      have e : (⟨0, Submodule.zero_mem _⟩ : ↥(commGL (Lc i) ⊤)) = 0 := rfl
      refine ⟨Submodule.zero_mem _, ?_, ?_⟩ <;> rw [e, map_zero] <;> rfl
    | add x y _ _ ih₁ ih₂ =>
      obtain ⟨hx', hxp, hxq⟩ := ih₁
      obtain ⟨hy', hyp, hyq⟩ := ih₂
      have e : (⟨x + y, (commGL (Lc i) ⊤).add_mem hx' hy'⟩ : ↥(commGL (Lc i) ⊤)) =
          ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
      refine ⟨(commGL (Lc i) ⊤).add_mem hx' hy', ?_, ?_⟩
      · rw [e, map_add, Submodule.coe_add, Pi.add_apply, hxp, hyp, add_zero]
      · rw [e, map_add, Submodule.coe_add, Pi.add_apply, hxq, hyq, add_zero]
    | smul c x _ ih =>
      obtain ⟨hx', hxp, hxq⟩ := ih
      have e : (⟨c • x, (commGL (Lc i) ⊤).smul_mem c hx'⟩ : ↥(commGL (Lc i) ⊤)) =
          c • ⟨x, hx'⟩ := rfl
      refine ⟨(commGL (Lc i) ⊤).smul_mem c hx', ?_, ?_⟩
      · rw [e, map_smul, Submodule.coe_smul, Pi.smul_apply, hxp, smul_zero]
      · rw [e, map_smul, Submodule.coe_smul, Pi.smul_apply, hxq, smul_zero]
  have hclpq : ∀ w : ↥(commGL Fs ⊤), cl w p = 0 ∧ cl w q = 0 := fun w => by
    obtain ⟨_, h1, h2⟩ := hvan w.1 w.2
    exact ⟨h1, h2⟩
  have hcard4 : Nat.card (ZMod 2 × ZMod 2) = 4 := by
    rw [Nat.card_prod]
    simp
  have hcardle : Nat.card ↥(commGL Fs ⊤) ≤ 4 := by
    let Φ : ↥(commGL Fs ⊤) → ZMod 2 × ZMod 2 := fun w => (cl w x, cl w y)
    have hΦ : Function.Injective Φ := by
      intro w₁ w₂ h
      obtain ⟨hx, hy⟩ := Prod.mk.inj h
      obtain ⟨hp1, hq1⟩ := hclpq w₁
      obtain ⟨hp2, hq2⟩ := hclpq w₂
      have hz : cl w₁ z = cl w₂ z := by
        linear_combination hclsum w₁ - hclsum w₂ - hx - hy - hp1 + hp2 - hq1 + hq2
      apply hclinj
      funext t
      rcases hallxyz t with rfl | rfl | rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz
      · rw [hp1, hp2]
      · rw [hq1, hq2]
    calc Nat.card ↥(commGL Fs ⊤) ≤ Nat.card (ZMod 2 × ZMod 2) :=
          Nat.card_le_card_of_injective Φ hΦ
      _ = 4 := hcard4
  have hcardge : 4 ≤ Nat.card ↥(commGL Fs ⊤) := by
    let wv : Ω → ↥(commGL Fs ⊤) := fun s =>
      ⟨(f' : V ≃ₗ[ZMod 2] V) (us s : V) - (us s : V), hmem s⟩
    have hclwv : ∀ s, cl (wv s) = delta (σ s) - delta s := fun s => by
      rw [hcl]
      exact hβws s
    let Ψ : ZMod 2 × ZMod 2 → ↥(commGL Fs ⊤) := fun st => st.1 • wv x + st.2 • wv y
    have hΨ : Function.Injective Ψ := by
      intro st st' h
      have h1 := congrArg cl h
      simp only [Ψ, map_add, map_smul, hclwv, hσx, hσy] at h1
      have hx' := congrFun h1 x
      have hz' := congrFun h1 z
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, delta, Pi.single_apply, smul_eq_mul]
        at hx' hz'
      simp [hxy, hxz, Ne.symm hxz, Ne.symm hyz] at hx' hz'
      exact Prod.ext hx' (hz'.resolve_right (by decide))
    calc 4 = Nat.card (ZMod 2 × ZMod 2) := hcard4.symm
      _ ≤ Nat.card ↥(commGL Fs ⊤) := Nat.card_le_card_of_injective Ψ hΨ
  refine ⟨le_antisymm hcardle hcardge, ?_, ?_⟩
  ·
    refine ⟨(f' : V ≃ₗ[ZMod 2] V), hfFs, ?_, ?_⟩
    · intro h1
      apply hσ1
      have hψ : ψi ⟨f', hFB hfFs⟩ = σ := hf'σ
      rw [← hψ]
      have : (⟨f', hFB hfFs⟩ : ↥(blockB H (Lc i))) = 1 := Subtype.ext h1
      rw [this, map_one]
    · intro w hw hfix
      obtain ⟨hwI, hwp, hwq⟩ := hvan w hw
      have hfw : (f' : V ≃ₗ[ZMod 2] V) w ∈ commGL (Lc i) ⊤ := hInv _ hfLc _ hwI
      have hc := hcompat ⟨f', hFB hfFs⟩ ⟨w, hwI⟩ ⟨(f' : V ≃ₗ[ZMod 2] V) w, hfw⟩ rfl
      have e : (⟨(f' : V ≃ₗ[ZMod 2] V) w, hfw⟩ : ↥(commGL (Lc i) ⊤)) = ⟨w, hwI⟩ :=
        Subtype.ext hfix
      have hψ : ψi ⟨f', hFB hfFs⟩ = σ := hf'σ
      rw [e, hψ] at hc
      set yv : Ω → ZMod 2 := ((βi ⟨w, hwI⟩ : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2) with hyv
      have h1 : yv y = yv x := by
        have := congrFun hc y
        rw [permAct_apply] at this
        have hs : σ.symm y = x := (Equiv.symm_apply_eq σ).2 hσx.symm
        rw [hs] at this
        exact this
      have h2 : yv z = yv y := by
        have := congrFun hc z
        rw [permAct_apply] at this
        have hs : σ.symm z = y := (Equiv.symm_apply_eq σ).2 hσy.symm
        rw [hs] at this
        exact this
      have hsum : yv x + yv y + yv z + yv p + yv q = 0 := by
        rw [← sum_five hallxyz hxy hxz hyz hpq hpx hpy hpz hqx hqy hqz]
        exact (βi ⟨w, hwI⟩).2
      have ha : yv x = 0 := by
        rw [h2, h1, hwp, hwq] at hsum
        have h22 : (2 : ZMod 2) = 0 := by decide
        linear_combination hsum - yv x * h22
      have hyv0 : yv = 0 := by
        funext t
        rcases hallxyz t with rfl | rfl | rfl | rfl | rfl
        · exact ha
        · rw [h1]; exact ha
        · rw [h2, h1]; exact ha
        · exact hwp
        · exact hwq
      have h0 : βi ⟨w, hwI⟩ = 0 := Subtype.ext hyv0
      have h00 : (⟨w, hwI⟩ : ↥(commGL (Lc i) ⊤)) = 0 := by
        apply βi.injective
        rw [h0, map_zero]
      exact congrArg Subtype.val h00
  by_contra hcon
  push Not at hcon
  have hs1 : Equiv.swap a b ∈ (A.subgroupOf (blockB H (Lc i))).map ψi.toMonoidHom := by
    rw [hA]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hs2 : Equiv.swap c d ∈ (A.subgroupOf (blockB H (Lc i))).map ψi.toMonoidHom := by
    rw [hA]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨x₁, hx₁, hx₁s⟩ := Subgroup.mem_map.1 hs1
  obtain ⟨x₂, hx₂, hx₂s⟩ := Subgroup.mem_map.1 hs2
  have key : ∀ g : ↥(blockB H (Lc i)), (g : V ≃ₗ[ZMod 2] V) ∈ A → ∀ s : Ω,
      permAct (ψi g) (delta (σ s) - delta s) = delta (σ s) - delta s := by
    intro g hgA s
    have hfix := hcon g hgA _ (hmem s)
    have hgw : (g : V ≃ₗ[ZMod 2] V) ((f' : V ≃ₗ[ZMod 2] V) (us s : V) - (us s : V)) ∈
        commGL (Lc i) ⊤ := by
      rw [hfix]
      exact hws s
    have hc := hcompat g ⟨(f' : V ≃ₗ[ZMod 2] V) (us s : V) - (us s : V), hws s⟩
      ⟨(g : V ≃ₗ[ZMod 2] V) ((f' : V ≃ₗ[ZMod 2] V) (us s : V) - (us s : V)), hgw⟩ rfl
    have e : (⟨(g : V ≃ₗ[ZMod 2] V) ((f' : V ≃ₗ[ZMod 2] V) (us s : V) - (us s : V)), hgw⟩ :
        ↥(commGL (Lc i) ⊤)) = ⟨(f' : V ≃ₗ[ZMod 2] V) (us s : V) - (us s : V), hws s⟩ :=
      Subtype.ext hfix
    rw [e, hβws s] at hc
    exact hc.symm
  have hfix1 : Equiv.swap a b x = x ∧ Equiv.swap a b y = y ∧ Equiv.swap a b z = z := by
    have hψ : ψi x₁ = Equiv.swap a b := hx₁s
    rw [← hψ]
    refine perm_fix_of_pairs hxy hxz hyz ?_ ?_ ?_
    · simpa [hσx] using key x₁ (Subgroup.mem_subgroupOf.1 hx₁) x
    · simpa [hσy] using key x₁ (Subgroup.mem_subgroupOf.1 hx₁) y
    · simpa [hσz] using key x₁ (Subgroup.mem_subgroupOf.1 hx₁) z
  have hfix2 : Equiv.swap c d x = x ∧ Equiv.swap c d y = y ∧ Equiv.swap c d z = z := by
    have hψ : ψi x₂ = Equiv.swap c d := hx₂s
    rw [← hψ]
    refine perm_fix_of_pairs hxy hxz hyz ?_ ?_ ?_
    · simpa [hσx] using key x₂ (Subgroup.mem_subgroupOf.1 hx₂) x
    · simpa [hσy] using key x₂ (Subgroup.mem_subgroupOf.1 hx₂) y
    · simpa [hσz] using key x₂ (Subgroup.mem_subgroupOf.1 hx₂) z
  rcases exists_moved_point hall hab hcd hxy with (h | h) | (h | h)
  · exact h hfix1.1
  · exact h hfix1.2.1
  · exact h hfix2.1
  · exact h hfix2.2.1

end Main

end CFSG.QuasithinUnique.Setup.Lift.Piece
