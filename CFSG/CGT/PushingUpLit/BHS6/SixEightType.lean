module

public import CFSG.CGT.PushingUpLit.BHS6.SixEightBlock
public import CFSG.CGT.PushingUpLit.BHS6.SixEightBridge

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {n : ℕ} {p : Fin 3 → Fin n}

@[expose] noncomputable def triEquiv (hp : Function.Injective p) : Fin 3 ≃ ↥(triSet p) :=
  Equiv.ofBijective (fun i => ⟨p i, p_mem_triSet i⟩)
    ⟨fun i j h => hp (congrArg Subtype.val h), fun x => by
      obtain ⟨i, hi⟩ := mem_triSet.1 x.2
      exact ⟨i, Subtype.ext hi⟩⟩

@[expose] noncomputable def resHom (hp : Function.Injective p) :
    ↥(setStab (triSet p)) →* Equiv.Perm (Fin 3) where
  toFun σ := (Equiv.permCongrHom (triEquiv hp)).symm
    ((σ : Equiv.Perm (Fin n)).subtypePerm (fun x => mem_setStab.1 σ.2 x))
  map_one' := by
    apply (Equiv.permCongrHom (triEquiv hp)).injective
    rw [MulEquiv.apply_symm_apply, map_one]
    exact Equiv.ext fun x => Subtype.ext rfl
  map_mul' σ τ := by
    rw [← map_mul]
    congr 1

theorem p_resHom (hp : Function.Injective p) (σ : ↥(setStab (triSet p))) (i : Fin 3) :
    p (resHom hp σ i) = (σ : Equiv.Perm (Fin n)) (p i) := by
  have h1 : ∀ x : ↥(triSet p), p ((triEquiv hp).symm x) = (x : Fin n) := fun x =>
    congrArg Subtype.val ((triEquiv hp).apply_symm_apply x)
  show p ((triEquiv hp).symm (((σ : Equiv.Perm (Fin n)).subtypePerm
    (fun x => mem_setStab.1 σ.2 x)) ((triEquiv hp) i))) = _
  rw [h1]
  rfl

theorem three_dvd_of_triCyc_zpow_apply_eq (hp : Function.Injective p) {k : ℤ} {i : Fin 3}
    (h : (triCyc p ^ k) (p i) = p i) : (3 : ℤ) ∣ k := by
  have hd3 : triCyc p ^ k = triCyc p ^ (k % 3) := by
    rw [← zpow_mod_orderOf, (triCyc_isThreeCycle hp).orderOf]
    rfl
  have hne : ∀ i : Fin 3, i + 1 ≠ i := by decide
  have hne2 : ∀ i : Fin 3, i + 1 + 1 ≠ i := by decide
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with h0 | h1 | h2
  · exact Int.dvd_of_emod_eq_zero h0
  · exfalso
    rw [hd3, h1, zpow_one, triCyc_apply hp] at h
    exact hne i (hp h)
  · exfalso
    rw [hd3, h2, zpow_two, Equiv.Perm.mul_apply, triCyc_apply hp, triCyc_apply hp] at h
    exact hne2 i (hp h)

namespace AltSetup

variable {E : Subgroup Γ} {M : AltSetup E n}

theorem zpowers_triCyc_le_setStab (hp : Function.Injective p) :
    Subgroup.zpowers (triCyc p) ≤ setStab (triSet p) :=
  (Subgroup.zpowers_le).2 (triCyc_mem_setStab hp)

theorem Ψ_mem_zpowers_of_mem_blockSub (hp : Function.Injective p) {g : ↥E}
    (hgd : M.Ψ g = triCyc p) {x : Γ} (hx : x ∈ M.blockSub p g) (hxE : x ∈ E) :
    M.Ψ ⟨x, hxE⟩ ∈ Subgroup.zpowers (triCyc p) := by
  obtain ⟨w, hw, k, hxk⟩ := (mem_blockSub_iff hp hgd).1 hx
  have h := Ψ_mul_zpow hgd hw k (hxk ▸ hxE)
  have e : (⟨x, hxE⟩ : ↥E) = ⟨w * (g : Γ) ^ k, hxk ▸ hxE⟩ := Subtype.ext hxk
  rw [e, h]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

theorem inf_centralizer_wSub_blockSub (hp : Function.Injective p) {g : ↥E} (hg3 : g ^ 3 = 1)
    (hgd : M.Ψ g = triCyc p) :
    M.blockSub p g ⊓ Subgroup.centralizer (M.wSub p : Set Γ) = M.wSub p := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxF, hxC⟩ := hx
    obtain ⟨w, hw, k, rfl⟩ := (mem_blockSub_iff hp hgd).1 hxF
    obtain ⟨w', hw'W, hw'S, hw'β⟩ := M.exists_wSub_of_mem_suppSub
      (pairVec_mem_suppSub (p := p) (p_mem_triSet 0) (p_mem_triSet 1))
    have hcomm := Subgroup.mem_centralizer_iff.mp hxC w' hw'S
    have hm : (g : Γ) ^ k * w' * ((g : Γ) ^ k)⁻¹ ∈ M.wSub p := conj_zpow_mem_wSub hp hgd k hw'S
    have h1 : (g : Γ) ^ k * w' * ((g : Γ) ^ k)⁻¹ = w' := by
      have h2 : w * (g : Γ) ^ k * w' * (w * (g : Γ) ^ k)⁻¹ = w' := by
        calc w * (g : Γ) ^ k * w' * (w * (g : Γ) ^ k)⁻¹ =
            (w * (g : Γ) ^ k * w') * (w * (g : Γ) ^ k)⁻¹ := rfl
          _ = (w' * (w * (g : Γ) ^ k)) * (w * (g : Γ) ^ k)⁻¹ := by rw [hcomm]
          _ = w' := by group
      have h3 : w * (g : Γ) ^ k * w' * (w * (g : Γ) ^ k)⁻¹ =
          w * ((g : Γ) ^ k * w' * ((g : Γ) ^ k)⁻¹) * w⁻¹ := by group
      rw [h3, M.hWab w (M.wSub_le_W hw) _ (M.wSub_le_W hm)] at h2
      simpa using h2
    have hw' : (w' : Γ) ∈ M.W := hw'W
    have h4 : coreAct n (triCyc p ^ k) (pairVec (p 0) (p 1)) = pairVec (p 0) (p 1) := by
      have h5 := M.βe_conjW (g ^ k) ⟨w', hw'W⟩
      rw [Ψ_zpow hgd, hw'β] at h5
      have h6 : (M.conjW (g ^ k) ⟨w', hw'W⟩ : ↥M.W) = ⟨w', hw'W⟩ := by
        apply Subtype.ext
        show ((g ^ k : ↥E) : Γ) * w' * ((g ^ k : ↥E) : Γ)⁻¹ = w'
        simpa using h1
      rw [h6, hw'β] at h5
      exact h5.symm
    set σ := triCyc p ^ k with hσ
    have hσs : σ ∈ setStab (triSet p) :=
      zpowers_triCyc_le_setStab hp (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k)
    have hfix := congrArg (fun v => vcoord v (p 2)) h4
    simp only [vcoord_coreAct] at hfix
    obtain ⟨i, hi⟩ := mem_triSet.1 (mem_setStab.1 ((setStab (triSet p)).inv_mem hσs) (p 2) |>.2
      (p_mem_triSet 2))
    have h3k : (3 : ℤ) ∣ k := by
      fin_cases i
      · exfalso
        rw [← hi] at hfix
        simp [vcoord_pairVec, hp.eq_iff] at hfix
      · exfalso
        rw [← hi] at hfix
        simp [vcoord_pairVec, hp.eq_iff] at hfix
      · have : σ (p 2) = p 2 := by
          have := congrArg σ hi
          simpa using this
        exact three_dvd_of_triCyc_zpow_apply_eq hp this
    have hgk : (g : Γ) ^ k = 1 := by
      have := congrArg (fun y : ↥E => (y : Γ)) (zpow_eq_one_of_dvd hg3 h3k)
      simpa using this
    rw [hgk, mul_one]
    exact hw
  · intro w hw
    refine ⟨wSub_le_blockSub hw, Subgroup.mem_centralizer_iff.mpr fun w' hw' => ?_⟩
    exact M.hWab w' (M.wSub_le_W hw') w (M.wSub_le_W hw)

section Hom

variable (hp : Function.Injective p) {g : ↥E} (hgd : M.Ψ g = triCyc p)

@[expose] noncomputable def ΨF : ↥(M.blockSub p g) →* ↥(setStab (triSet p)) :=
  (M.Ψ.comp (Subgroup.inclusion (blockSub_le_E hp hgd))).codRestrict (setStab (triSet p))
    (fun x => zpowers_triCyc_le_setStab hp
      (Ψ_mem_zpowers_of_mem_blockSub hp hgd x.2 (blockSub_le_E hp hgd x.2)))

@[expose] noncomputable def φF₀ : ↥(M.blockSub p g) →* Equiv.Perm (Fin 3) :=
  (resHom hp).comp (ΨF hp hgd)

theorem p_φF₀ (x : ↥(M.blockSub p g)) (i : Fin 3) :
    p (φF₀ hp hgd x i) = M.Ψ ⟨(x : Γ), blockSub_le_E hp hgd x.2⟩ (p i) :=
  p_resHom hp (ΨF hp hgd x) i

theorem φF₀_cube (x : ↥(M.blockSub p g)) : φF₀ hp hgd x ^ 3 = 1 := by
  have h1 : ((ΨF hp hgd x) ^ 3 : ↥(setStab (triSet p))) = 1 := by
    apply Subtype.ext
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
      (Ψ_mem_zpowers_of_mem_blockSub hp hgd x.2 (blockSub_le_E hp hgd x.2))
    show (M.Ψ ⟨(x : Γ), blockSub_le_E hp hgd x.2⟩) ^ 3 = 1
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have := triCyc_pow_three hp
    simp [this]
  rw [φF₀, MonoidHom.comp_apply, ← map_pow, h1, map_one]

@[expose] noncomputable def φF : ↥(M.blockSub p g) →* ↥(alternatingGroup (Fin 3)) :=
  (φF₀ hp hgd).codRestrict (alternatingGroup (Fin 3)) fun x => by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h := congrArg Equiv.Perm.sign (φF₀_cube hp hgd x)
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign (φF₀ hp hgd x)) with h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd h (by decide)

@[expose] noncomputable def βW (p : Fin 3 → Fin n) :
    ↥(M.wSub p) →* ↥(suppSub (triSet p)) where
  toFun w := ⟨M.βe ⟨(w : Γ), w.2.1⟩, w.2.2⟩
  map_one' := Subtype.ext (map_one M.βe)
  map_mul' x y := Subtype.ext (map_mul M.βe (⟨(x : Γ), x.2.1⟩ : ↥M.W) ⟨(y : Γ), y.2.1⟩)

theorem βW_injective : Function.Injective (βW (M := M) (p := p)) := by
  intro x y h
  apply Subtype.ext
  exact M.eq_of_βe_eq x.2.1 y.2.1 (congrArg Subtype.val h)

theorem βW_surjective : Function.Surjective (βW (M := M) (p := p)) := by
  intro v
  obtain ⟨w, hwW, hwS, hwβ⟩ := M.exists_wSub_of_mem_suppSub v.2
  refine ⟨⟨w, hwS⟩, Subtype.ext ?_⟩
  exact hwβ

theorem isNatAlt_blockSub (hp : Function.Injective p) {g : ↥E} (hg3 : g ^ 3 = 1)
    (hgd : M.Ψ g = triCyc p) : IsNatAlt (M.blockSub p g) (M.wSub p) 3 := by
  classical
  have hgF : (g : Γ) ∈ M.blockSub p g := g_mem_blockSub
  have hcard : Nat.card ↥(alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨φF hp hgd, (coordHom hp).comp (βW (M := M) p), ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hne : φF hp hgd ⟨(g : Γ), hgF⟩ ≠ 1 := by
      intro h1
      have hφ₀ : φF₀ hp hgd ⟨(g : Γ), hgF⟩ = 1 := congrArg Subtype.val h1
      have h2 := p_φF₀ hp hgd ⟨(g : Γ), hgF⟩ 0
      rw [hφ₀, Equiv.Perm.one_apply] at h2
      have h3 : M.Ψ ⟨(g : Γ), blockSub_le_E hp hgd hgF⟩ = triCyc p := hgd
      rw [h3, triCyc_apply hp] at h2
      exact (by decide : (0 : Fin 3) + 1 ≠ 0) (hp h2.symm)
    have htop := zpowers_eq_top_of_prime_card hcard hne
    intro a
    have ha : a ∈ Subgroup.zpowers (φF hp hgd ⟨(g : Γ), hgF⟩) := by rw [htop]; trivial
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact ⟨(⟨(g : Γ), hgF⟩ : ↥(M.blockSub p g)) ^ k, by rw [map_zpow, hk]⟩
  ·
    rw [inf_centralizer_wSub_blockSub hp hg3 hgd]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hφ₀ : φF₀ hp hgd x = 1 := congrArg Subtype.val hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
        (Ψ_mem_zpowers_of_mem_blockSub hp hgd x.2 (blockSub_le_E hp hgd x.2))
      have h1 := p_φF₀ hp hgd x 0
      rw [hφ₀, Equiv.Perm.one_apply, ← hk] at h1
      have h3k : (3 : ℤ) ∣ k := three_dvd_of_triCyc_zpow_apply_eq hp h1.symm
      have hΨ1 : M.Ψ ⟨(x : Γ), blockSub_le_E hp hgd x.2⟩ = 1 := by
        rw [← hk]
        apply orderOf_dvd_iff_zpow_eq_one.1
        rw [(triCyc_isThreeCycle hp).orderOf]
        exact h3k
      have hxW : (x : Γ) ∈ M.W := (M.mem_W_iff ⟨(x : Γ), blockSub_le_E hp hgd x.2⟩).2 hΨ1
      exact mem_wSub_of_mem_blockSub_W hp hg3 hgd x.2 hxW
    · intro hx
      have hΨ1 : M.Ψ ⟨(x : Γ), blockSub_le_E hp hgd x.2⟩ = 1 :=
        M.Ψ_eq_one_of_mem (M.wSub_le_W hx)
      apply Subtype.ext
      apply Equiv.ext
      intro i
      apply hp
      show p (φF₀ hp hgd x i) = p ((1 : Equiv.Perm (Fin 3)) i)
      rw [p_φF₀ hp hgd x i, hΨ1]
      rfl
  ·
    intro v
    obtain ⟨u, hu⟩ := (coordHom_bijective hp).2 v
    obtain ⟨w, hw⟩ := (βW_surjective (M := M) (p := p)) u
    exact ⟨w, by rw [MonoidHom.comp_apply, hw, hu]⟩
  ·
    have hbot : M.wSub p ⊓ Subgroup.centralizer (M.blockSub p g : Set Γ) = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨hwS, hwC⟩ := hw
      have h1 := Subgroup.mem_centralizer_iff.mp hwC (g : Γ) hgF
      have h2 : coreAct n (triCyc p) (M.βe ⟨w, hwS.1⟩) = M.βe ⟨w, hwS.1⟩ := by
        have h3 := M.βe_conjW g ⟨w, hwS.1⟩
        rw [hgd] at h3
        have e : M.conjW g ⟨w, hwS.1⟩ = ⟨w, hwS.1⟩ := by
          apply Subtype.ext
          show (g : Γ) * w * (g : Γ)⁻¹ = w
          rw [h1]
          group
        rw [e] at h3
        exact h3.symm
      have h4 := eq_one_of_coreAct_triCyc_eq hp hwS.2 h2
      exact Subgroup.mem_bot.2 (M.eq_of_βe_eq hwS.1 M.W.one_mem (by
        rw [h4]
        exact (map_one M.βe).symm))
    rw [hbot, Subgroup.bot_subgroupOf, eq_bot_iff]
    intro w hw
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hw
    have h5 : βW (M := M) p w = 1 := (coordHom_bijective hp).1 (by rw [map_one]; exact hw)
    have h6 : w = 1 := βW_injective (by rw [h5, map_one])
    exact Subgroup.mem_bot.2 h6
  ·
    intro e w hw
    set eE : ↥E := ⟨(e : Γ), blockSub_le_E hp hgd e.2⟩ with heE
    have hΨe : M.Ψ eE ∈ setStab (triSet p) :=
      zpowers_triCyc_le_setStab hp
        (Ψ_mem_zpowers_of_mem_blockSub hp hgd e.2 (blockSub_le_E hp hgd e.2))
    have h1 := M.hΨ eE ⟨(w : Γ), w.2.1⟩ (M.conj_mem eE w.2.1)
    have hv : coreAct n (M.Ψ eE) ((βW (M := M) p w : ↥(suppSub (triSet p))) : ↥(coreMod n)) ∈
        suppSub (triSet p) := coreAct_mem_suppSub hΨe (βW (M := M) p w).2
    have h2 : βW (M := M) p ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ =
        ⟨coreAct n (M.Ψ eE) ((βW (M := M) p w : ↥(suppSub (triSet p))) : ↥(coreMod n)), hv⟩ :=
      Subtype.ext h1
    rw [MonoidHom.comp_apply, h2]
    exact coordHom_coreAct hp (σ := M.Ψ eE) (τ := φF₀ hp hgd e)
      (fun i => (p_φF₀ hp hgd e i).symm) (βW (M := M) p w) hv

theorem charTwo_blockSub (hp : Function.Injective p) {g : ↥E} (hg3 : g ^ 3 = 1)
    (hgd : M.Ψ g = triCyc p) : CharTwo (M.blockSub p g) := by
  unfold CharTwo
  rw [pCoreOf_blockSub hp hg3 hgd]
  exact (inf_centralizer_wSub_blockSub hp hg3 hgd).le

theorem isNaturalAltModule_blockSub (hp : Function.Injective p) {g : ↥E} (hg3 : g ^ 3 = 1)
    (hgd : M.Ψ g = triCyc p) : IsNaturalAltModule ↥(M.blockSub p g) 1 := by
  have hpc := pCoreOf_blockSub hp hg3 hgd
  refine isNaturalAltModule_of_isNatAlt (m := 1) (charTwo_blockSub hp hg3 hgd) ?_ ?_ ?_
  · rw [hpc]
    intro x hx y hy
    exact M.hWab x (M.wSub_le_W hx) y (M.wSub_le_W hy)
  · rw [hpc]
    exact commutator_wSub_blockSub hp hgd
  · rw [hpc, show (2 * 1 + 1 : ℕ) = 3 from rfl]
    exact isNatAlt_blockSub hp hg3 hgd

end Hom

end AltSetup

end CFSG.CGT.PushingUpLit.BHS6
