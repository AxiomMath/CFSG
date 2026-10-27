module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269Red
public import CFSG.LocalAnalysis.GLTheoremA.PartI.U42

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Helpers

theorem conj_eq_one_iff_mem_center' {G : Type} [Group G] {g : G} :
    MulAut.conj g = 1 ↔ g ∈ Subgroup.center G := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun φ : MulAut G => φ z) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hz
    rw [mul_inv_eq_iff_eq_mul] at hz
    exact hz.symm
  · intro h
    ext z
    rw [Subgroup.mem_center_iff] at h
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h z, mul_inv_cancel_right]

theorem pow_eq_one_of_conj_pow_eq_one {G : Type} [Group G] (hZ : Subgroup.center G = ⊥) {g : G}
    {n : ℕ} (h : MulAut.conj g ^ n = 1) : g ^ n = 1 := by
  rw [← map_pow] at h
  have hc := conj_eq_one_iff_mem_center'.1 h
  rw [hZ] at hc
  exact Subgroup.mem_bot.1 hc

theorem conj_injective_of_center' {G : Type} [Group G] (hZ : Subgroup.center G = ⊥) {x y : G}
    (h : MulAut.conj x = MulAut.conj y) : x = y := by
  have h1 : MulAut.conj (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hc := conj_eq_one_iff_mem_center'.1 h1
  rw [hZ] at hc
  exact inv_mul_eq_one.1 (Subgroup.mem_bot.1 hc)

private theorem fixSubgroup_conj_eq_centralizer' {G : Type} [Group G] (g : G) :
    fixSubgroup (MulAut.conj g) = Subgroup.centralizer ({g} : Set G) := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_iff]
  simp only [MulAut.conj_apply, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [h]
  · intro h
    calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [h]
      _ = x := by group

theorem congr_conj' {G H : Type} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr, MulAut.conj_apply]

theorem fixSubgroup_congr' {S T : Type} [Group S] [Group T] (e : S ≃* T) (α : MulAut S) :
    fixSubgroup (MulAut.congr e α) = (fixSubgroup α).map e.toMonoidHom := by
  ext y
  rw [mem_fixSubgroup, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [mem_fixSubgroup]
    apply e.injective
    simpa [MulAut.congr] using h
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixSubgroup] at hx
    simp [MulAut.congr, hx]

theorem fixSubgroup_solvable_of_mulEquiv' {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (hT : ∀ β : MulAut T, β ^ 3 = 1 → β ≠ 1 → Group.IsSolvable ↥(fixSubgroup β))
    (α : MulAut S) (hα : α ^ 3 = 1) (hα1 : α ≠ 1) : Group.IsSolvable ↥(fixSubgroup α) := by
  have hβ : MulAut.congr e α ^ 3 = 1 := by
    rw [← map_pow, hα, map_one]
  have hβ1 : MulAut.congr e α ≠ 1 := by
    intro h
    apply hα1
    ext x
    have := congrArg (fun φ : MulAut T => φ (e x)) h
    simp only [MulAut.congr, MulAut.one_apply] at this
    simpa using this
  have h := hT _ hβ hβ1
  rw [fixSubgroup_congr'] at h
  haveI := h
  exact isSolvable_of_mulEquiv' (Subgroup.equivMapOfInjective (fixSubgroup α) e.toMonoidHom e.injective)

theorem center_eq_bot_of_simple_nonabelian' {K : Type} [Group K] [IsSimpleGroup K]
    (hnc : ¬ IsMulCommutative K) : Subgroup.center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha : a ∈ Subgroup.center K := by
      rw [h]
      exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem isElemAbelian_map_congr' {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (E : Subgroup (MulAut S)) (hE : IsElemAbelian 3 E) :
    IsElemAbelian 3 (E.map (MulAut.congr e).toMonoidHom) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨α, hα, hαa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨β, hβ, hβb⟩ := Subgroup.mem_map.1 b.2
    have hc : α * β = β * α := congrArg Subtype.val (hE.1.is_comm.comm ⟨α, hα⟩ ⟨β, hβ⟩)
    apply Subtype.ext
    show (a : MulAut T) * (b : MulAut T) = (b : MulAut T) * (a : MulAut T)
    rw [← hαa, ← hβb, ← map_mul, ← map_mul, hc]
  · rintro _ ⟨α, hα, rfl⟩
    show (MulAut.congr e α) ^ 3 = 1
    rw [← map_pow, hE.2 α hα, map_one]

end Helpers

section FixSolv

theorem fixSolv_of_conj_yM5 (E : Subgroup (MulAut M5))
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 9) (hy : MulAut.conj yM5 ∈ E) :
    Group.IsSolvable ↥(i269Fix E) := by
  classical
  obtain ⟨Kb, hKbC, hsup, -, hsimp, hnc, -, hcat⟩ := m5_u4_layer
  haveI := hsimp
  have hZM : Subgroup.center M5 = ⊥ := center_M5_eq_bot
  have hy3 : yM5 ^ 3 = 1 := pow_eq_one_of_conj_pow_eq_one hZM (hE.2 _ hy)
  have hK : ∀ k ∈ Kb, k * yM5 = yM5 * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (hKbC hk)
  have hdec : ∀ x ∈ Subgroup.centralizer ({yM5} : Set M5), ∃ k ∈ Kb, ∃ n : ℤ, x = k * yM5 ^ n := by
    intro x hx
    have hle : Subgroup.centralizer ({yM5} : Set M5) ≤ decompSub Kb yM5 hK := by
      rw [hsup]
      apply sup_le
      · intro k hk
        exact ⟨k, hk, 0, by simp⟩
      · rw [Subgroup.zpowers_le]
        exact ⟨1, Kb.one_mem, 1, by simp⟩
    obtain ⟨k, hk, n, rfl⟩ := hle hx
    exact ⟨k, hk, n, rfl⟩
  obtain ⟨α₂, hα₂E, hα₂⟩ : ∃ α₂ ∈ E, α₂ ∉ Subgroup.zpowers (MulAut.conj yM5) := by
    by_contra hcon
    have hle : E ≤ Subgroup.zpowers (MulAut.conj yM5) := fun α hα =>
      by_contra fun h => hcon ⟨α, hα, h⟩
    have h1 : Nat.card E ≤ Nat.card (Subgroup.zpowers (MulAut.conj yM5)) :=
      Subgroup.card_le_of_le hle
    have h2 : orderOf (MulAut.conj yM5) ∣ 3 := orderOf_dvd_of_pow_eq_one (hE.2 _ hy)
    have h3' : Nat.card (Subgroup.zpowers (MulAut.conj yM5)) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) h2
    omega
  obtain ⟨s₂, hs₂⟩ := exists_conj_of_pow_three α₂ (hE.2 _ hα₂E)
  have hs₂3 : s₂ ^ 3 = 1 := pow_eq_one_of_conj_pow_eq_one hZM (hs₂ ▸ hE.2 _ hα₂E)
  have hcomm12 : MulAut.conj yM5 * α₂ = α₂ * MulAut.conj yM5 :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨MulAut.conj yM5, hy⟩ ⟨α₂, hα₂E⟩)
  have hys₂ : yM5 * s₂ = s₂ * yM5 := by
    apply conj_injective_of_center' hZM
    rw [hs₂, ← map_mul, ← map_mul] at hcomm12
    exact hcomm12
  obtain ⟨k, hk, m, hkm⟩ := hdec s₂ (Subgroup.mem_centralizer_singleton_iff.2 hys₂.symm)
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply hα₂
    rw [one_mul] at hkm
    rw [hs₂, hkm, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m
  have hkc : Commute k yM5 := hK k hk
  have hk3 : k ^ 3 = 1 := by
    have hpy : (yM5 ^ m) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
    have hcm : Commute k (yM5 ^ m) := hkc.zpow_right m
    have h4 : s₂ ^ 3 = k ^ 3 * (yM5 ^ m) ^ 3 := by
      rw [hkm, hcm.mul_pow]
    rw [hpy, mul_one] at h4
    rw [← h4, hs₂3]
  let kk : Kb := ⟨k, hk⟩
  have hcenter : Subgroup.center Kb = ⊥ := center_eq_bot_of_simple_nonabelian' hnc
  have hkk3 : (MulAut.conj kk) ^ 3 = 1 := by
    rw [← map_pow]
    have h5 : kk ^ 3 = 1 := Subtype.ext (by simpa using hk3)
    rw [h5, map_one]
  have hkk1 : MulAut.conj kk ≠ 1 := by
    intro h
    have h6 := conj_eq_one_iff_mem_center'.1 h
    rw [hcenter] at h6
    apply hk1
    exact congrArg Subtype.val (Subgroup.mem_bot.1 h6)
  obtain ⟨q, hv, hq, ⟨eK⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU4two hcat
  have hsolvKk : Group.IsSolvable ↥(fixSubgroup (MulAut.conj kk)) :=
    fixSubgroup_solvable_of_mulEquiv' eK (fun β h3 h1 => u42_fixSubgroup_solvable q hv hq β h3 h1)
      (MulAut.conj kk) hkk3 hkk1
  rw [fixSubgroup_conj_eq_centralizer'] at hsolvKk
  let A : Subgroup M5 := (Subgroup.centralizer ({kk} : Set Kb)).map Kb.subtype
  have hAsolv : Group.IsSolvable ↥A :=
    isSolvable_of_mulEquiv' ((Subgroup.equivMapOfInjective _ Kb.subtype Kb.subtype_injective).symm)
  have hAC : ∀ a ∈ A, a * yM5 = yM5 * a := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := Subgroup.mem_map.1 ha
    exact hK b.1 b.2
  have hcomm : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers yM5, Commute a b := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (show Commute a yM5 from hAC a ha).zpow_right n
  haveI hZsolv : Group.IsSolvable ↥(Subgroup.zpowers yM5) := by
    refine Group.isSolvable_of_comm (fun a b => Subtype.ext ?_)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    show (a : M5) * (b : M5) = (b : M5) * (a : M5)
    rw [← hi, ← hj]
    exact Commute.zpow_zpow_self yM5 i j
  let Φ : (↥A × ↥(Subgroup.zpowers yM5)) →* M5 :=
    { toFun := fun p => (p.1 : M5) * (p.2 : M5)
      map_one' := by simp
      map_mul' := by
        intro p q
        have hc : (q.1 : M5) * (p.2 : M5) = (p.2 : M5) * (q.1 : M5) :=
          hcomm _ q.1.2 _ p.2.2
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        calc (p.1 : M5) * (q.1 : M5) * ((p.2 : M5) * (q.2 : M5))
            = (p.1 : M5) * ((q.1 : M5) * (p.2 : M5)) * (q.2 : M5) := by simp only [mul_assoc]
          _ = (p.1 : M5) * ((p.2 : M5) * (q.1 : M5)) * (q.2 : M5) := by rw [hc]
          _ = (p.1 : M5) * (p.2 : M5) * ((q.1 : M5) * (q.2 : M5)) := by simp only [mul_assoc] }
  have hTsolv : Group.IsSolvable ↥Φ.range :=
    Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective Φ)
  have hsub : i269Fix E ≤ Φ.range := by
    intro x hx
    rw [mem_i269Fix] at hx
    have hx1 : MulAut.conj yM5 x = x := hx _ hy
    have hxC : x ∈ Subgroup.centralizer ({yM5} : Set M5) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hx1
      exact hx1.symm
    obtain ⟨k', hk', n, hxk⟩ := hdec x hxC
    have hx2 : MulAut.conj s₂ x = x := by
      have h9 := hx α₂ hα₂E
      rw [hs₂] at h9
      exact h9
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hx2
    rw [hkm, hxk] at hx2
    have hk'd : Commute k' (yM5 ^ m) := (show Commute k' yM5 from hK k' hk').zpow_right m
    have hck : Commute (yM5 ^ n) k := ((show Commute k yM5 from hkc).zpow_right n).symm
    have hcd : Commute (yM5 ^ n) (yM5 ^ m) := Commute.zpow_zpow_self yM5 n m
    have e1 : k * k' * (yM5 ^ n * yM5 ^ m) = k * yM5 ^ m * (k' * yM5 ^ n) := by
      rw [hcd.eq, mul_assoc k k', ← mul_assoc k' (yM5 ^ m) (yM5 ^ n), hk'd.eq]
      simp only [mul_assoc]
    have e2 : k' * yM5 ^ n * (k * yM5 ^ m) = k' * k * (yM5 ^ n * yM5 ^ m) := by
      rw [mul_assoc k' (yM5 ^ n) (k * yM5 ^ m), ← mul_assoc (yM5 ^ n) k (yM5 ^ m), hck.eq]
      simp only [mul_assoc]
    have h8 : k * k' * (yM5 ^ n * yM5 ^ m) = k' * k * (yM5 ^ n * yM5 ^ m) := by
      rw [e1, hx2, e2]
    have hkk' : k * k' = k' * k := mul_right_cancel h8
    have hcent : (⟨k', hk'⟩ : Kb) ∈ Subgroup.centralizer ({kk} : Set Kb) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hkk'.symm)
    have hmemA : k' ∈ A := Subgroup.mem_map.2 ⟨⟨k', hk'⟩, hcent, rfl⟩
    refine ⟨((⟨k', hmemA⟩ : ↥A), (⟨yM5 ^ n, Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n⟩ :
      ↥(Subgroup.zpowers yM5))), ?_⟩
    exact hxk.symm
  exact isSolvable_of_le_isSolvable hsub

end FixSolv

theorem E9Solv_M5 : E9Solv M5 := by
  intro E hE hcard
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num)
  obtain ⟨α₁, hα₁1⟩ := exists_ne (1 : E)
  have hα₁3 : (α₁.1 : MulAut M5) ^ 3 = 1 := hE.2 α₁.1 α₁.2
  obtain ⟨s₁, hs₁⟩ := exists_conj_of_pow_three α₁.1 hα₁3
  have hs₁3 : s₁ ^ 3 = 1 := pow_eq_one_of_conj_pow_eq_one center_M5_eq_bot (hs₁ ▸ hα₁3)
  have hα₁1' : α₁.1 ≠ 1 := fun h => hα₁1 (Subtype.ext h)
  have hs₁1 : s₁ ≠ 1 := by
    rintro rfl
    apply hα₁1'
    rw [hs₁, map_one]
  rcases normal_form s₁ hs₁3 with h1 | ⟨τ, hτ⟩ | ⟨τ, d, hd, hcnt⟩
  · exact absurd h1 hs₁1
  ·
    have hinj : Function.Injective (MulAut.congr τ).toMonoidHom := (MulAut.congr τ).injective
    have hE' := isElemAbelian_map_congr' τ E hE
    have hcard' : Nat.card (E.map (MulAut.congr τ).toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective hinj, hcard]
    have hyE' : MulAut.conj yM5 ∈ E.map (MulAut.congr τ).toMonoidHom := by
      have hmem : MulAut.congr τ α₁.1 ∈ E.map (MulAut.congr τ).toMonoidHom :=
        Subgroup.mem_map_of_mem _ α₁.2
      rw [hs₁, congr_conj'] at hmem
      rcases hτ with h | h
      · rw [h] at hmem
        exact hmem
      · rw [h, map_inv] at hmem
        have h10 := Subgroup.inv_mem _ hmem
        rwa [inv_inv] at h10
    have hS := fixSolv_of_conj_yM5 _ hE' hcard' hyE'
    rw [i269Fix_map] at hS
    haveI := hS
    exact isSolvable_of_mulEquiv' (Subgroup.equivMapOfInjective (i269Fix E) τ.toMonoidHom τ.injective)
  ·
    have hC : Group.IsSolvable ↥(Subgroup.centralizer ({s₁} : Set M5)) :=
      isSolvable_centralizer_of_equiv τ s₁ (centralizer_diag_solvable (τ s₁) d hd hcnt)
    have hle : i269Fix E ≤ Subgroup.centralizer ({s₁} : Set M5) := by
      intro x hx
      rw [← fixSubgroup_conj_eq_centralizer', ← hs₁]
      exact (mem_i269Fix.1 hx) α₁.1 α₁.2
    haveI := hC
    exact isSolvable_of_le_isSolvable hle

theorem layer_eq_bot_of_u5 {G : Type} [Group G] [Finite G]
    {X L D : Subgroup G} (hL : GLAPComponent 3 X L)
    (hcat : catalogIs (PSimple 3 L) S9.isU5two)
    (hDN : D ≤ Subgroup.normalizer (L : Set G)) (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 2 * Nat.card ↥(D ⊓ centModSubgroup 3 L)) :
    GLAPLayer 3 (L ⊓ Subgroup.centralizer (D : Set G)) = ⊥ := by
  obtain ⟨e⟩ := bridge_u5two_stated hcat
  exact layer_eq_bot_of_E9 hL (E9Solv.of_mulEquiv E9Solv_M5 e) hDN hD hcard

end CFSG.LocalAnalysis.GLTheoremA

end
