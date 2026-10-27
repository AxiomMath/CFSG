module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM7Lin
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM7Omega

open CFSG.RankThree.OrthogonalInvolutions QuadraticMap

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
theorem eq_one_of_pow_seven_eq_one_of_fixed_singular {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Q : QuadraticForm (ZMod 2) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hV : Nat.card V = 256)
    (hZ : Nat.card {v : V // Q v = 0} = 120) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h7 : g ^ 7 = 1) {v : V} (hv : v ≠ 0)
    (hQv : Q v = 0) (hgv : g v = v) : g = 1 := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hfin : Module.finrank (ZMod 2) V = 8 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [hV, Nat.card_zmod] at h
    refine Nat.pow_right_injective (le_refl 2) ?_
    calc
      2 ^ Module.finrank (ZMod 2) V = 256 := h.symm
      _ = 2 ^ 8 := by norm_num
  have hbot : fixSpace g ⊓ commSpace g = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxC, hxD⟩ := Submodule.mem_inf.mp hx
    obtain ⟨y, hy⟩ := mem_commSpace.mp hxD
    have hxC' : g x = x := mem_fixSpace.mp hxC
    have hgy : g y = y + x := by
      rw [← hy]
      abel
    have hiter : ∀ k : ℕ, (g ^ k) y = y + k • x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, hgy, map_nsmul, hxC',
          add_nsmul, one_nsmul]
        abel
    have h7iter := hiter 7
    rw [h7] at h7iter
    simp only [LinearEquiv.coe_one, id_eq] at h7iter
    have h7x : (7 : ℕ) • x = x := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2) 7 x,
        show ((7 : ℕ) : ZMod 2) = 1 by decide, one_smul]
    rw [h7x] at h7iter
    rw [Submodule.mem_bot]
    exact add_left_cancel (a := y) (by simpa using h7iter.symm)
  have hsup : fixSpace g ⊔ commSpace g = ⊤ := by
    have h1 := finrank_commSpace_add_finrank_fixSpace g
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (fixSpace g) (commSpace g)
    rw [hbot, finrank_bot] at h2
    apply Submodule.eq_top_of_finrank_eq
    omega
  have hpolar_fixed : ∀ (c : V), c ∈ fixSpace g → ∀ y : V, polar Q c (g y - y) = 0 := by
    intro c hc y
    have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg c y
    rw [mem_fixSpace.mp hc] at h
    rw [QuadraticMap.polar_sub_right, h, sub_self]
  have hndC : (LinearMap.BilinForm.restrict Q.polarBilin (fixSpace g)).Nondegenerate := by
    let B := LinearMap.BilinForm.restrict Q.polarBilin (fixSpace g)
    have hsep : B.SeparatingLeft := by
      intro c hc
      apply Subtype.ext
      apply hQ.1 c.1
      intro w
      rw [QuadraticMap.polarBilin_apply_apply]
      have hw : w ∈ fixSpace g ⊔ commSpace g := by
        rw [hsup]
        exact Submodule.mem_top
      obtain ⟨c', hc', d, hd, rfl⟩ := Submodule.mem_sup.mp hw
      rw [QuadraticMap.polar_add_right]
      have h1 : polar Q c.1 c' = 0 := by
        have h := hc ⟨c', hc'⟩
        simpa [B, LinearMap.BilinForm.restrict_apply, QuadraticMap.polarBilin_apply_apply] using h
      have h2 : polar Q c.1 d = 0 := by
        obtain ⟨y, rfl⟩ := mem_commSpace.mp hd
        exact hpolar_fixed c.1 c.2 y
      rw [h1, h2, add_zero]
    have hsymm : ∀ x y : fixSpace g, B x y = B y x := by
      intro x y
      simp [B, LinearMap.BilinForm.restrict_apply, QuadraticMap.polarBilin_apply_apply,
        QuadraticMap.polar_comm]
    have hndB : B.Nondegenerate := by
      refine ⟨hsep, ?_⟩
      intro c hc
      apply hsep c
      intro c'
      rw [hsymm c c']
      exact hc c'
    exact hndB
  have halt : (LinearMap.BilinForm.restrict Q.polarBilin (fixSpace g)).IsAlt := by
    intro c
    simpa [LinearMap.BilinForm.restrict_apply, QuadraticMap.polarBilin_apply_apply] using
      polar_self_eq_zero Q c.1
  have heven : Even (Module.finrank (ZMod 2) (fixSpace g)) :=
    LinearMap.BilinForm.IsAlt.even_finrank halt hndC
  set fd := Module.finrank (ZMod 2) (fixSpace g) with hfd
  have hd8 : fd ≤ 8 := by
    rw [hfd, ← hfin]
    exact Submodule.finrank_le _
  have heven' : Even fd := by
    rw [hfd]
    exact heven
  have hCcard : Nat.card (fixSpace g) = 2 ^ fd := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixSpace g), Nat.card_zmod, ← hfd]
  have htoEquiv_pow_apply : ∀ (n : ℕ) (e : V ≃ₗ[ZMod 2] V) (x : V),
      (e.toEquiv ^ n) x = (e ^ n) x := by
    intro n
    induction n with
    | zero => intro e x; simp
    | succ n ih =>
      intro e x
      rw [pow_succ', Equiv.Perm.mul_apply, ih e, pow_succ', LinearEquiv.mul_apply]
      rfl
  have hσ7 : (g.toEquiv : Equiv.Perm V) ^ 7 = 1 := by
    ext x
    rw [htoEquiv_pow_apply 7 g x, h7]
    rfl
  have hfixV : Nat.card {x : V // g.toEquiv x = x} = Nat.card (fixSpace g) := by
    let e : {x : V // g.toEquiv x = x} ≃ fixSpace g :=
      { toFun := fun x => ⟨x.1, mem_fixSpace.mpr (by simpa using x.2)⟩
        invFun := fun x => ⟨x.1, by simpa using mem_fixSpace.mp x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    exact Nat.card_congr e
  have hmodV := CFSG.LocalAnalysis.GLTheoremA.SFM7Lin.card_perm_modEq
    (g.toEquiv : Equiv.Perm V) (p := 7) hσ7
  rw [hV, hfixV, hCcard] at hmodV
  have hdmod : 2 ^ fd ≡ 4 [MOD 7] := by
    have h256 : (256 : ℕ) ≡ 4 [MOD 7] := by norm_num [Nat.ModEq]
    exact (h256.symm.trans hmodV).symm
  have hcases : fd = 2 ∨ fd = 8 := by
    obtain ⟨k, hk⟩ := heven'
    interval_cases fd
    · norm_num at hdmod
    · norm_num at hdmod
    · exact Or.inl rfl
    · norm_num at hdmod
    · norm_num at hdmod
    · norm_num at hdmod
      omega
    · norm_num at hdmod
    · norm_num at hdmod
    · exact Or.inr rfl
  rcases hcases with hfd2 | hfd8
  · exfalso
    let Z := {x : V // Q x = 0}
    let fZ : Z → Z := fun z =>
      ⟨g z.1, by
        rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg z.1, z.2]⟩
    let σ' : Equiv.Perm Z := Equiv.ofBijective fZ (by
      refine Finite.injective_iff_bijective.1 ?_
      intro x y hxy
      apply Subtype.ext
      exact g.injective (congrArg Subtype.val hxy))
    have hpow : ∀ (n : ℕ) (z : Z), (((σ' ^ n) z : Z) : V) = (g ^ n) z.1 := by
      intro n
      induction n with
      | zero => intro z; simp
      | succ n ih =>
        intro z
        rw [pow_succ', Equiv.Perm.mul_apply]
        change g (((σ' ^ n) z : Z) : V) = _
        rw [ih z, pow_succ', LinearEquiv.mul_apply]
    have hσ'7 : σ' ^ 7 = 1 := by
      ext z
      rw [hpow 7 z, h7]
      rfl
    have hCcard4 : Nat.card (fixSpace g) = 4 := by
      rw [hCcard, hfd2]
      norm_num
    have hfix_le : Nat.card {z : Z // σ' z = z} ≤ 4 := by
      let toC : {z : Z // σ' z = z} → fixSpace g := fun z =>
        ⟨z.1.1, mem_fixSpace.mpr (by
          have h := congrArg Subtype.val z.2
          simpa [σ'] using h)⟩
      have htoC : Function.Injective toC := by
        intro z w hzw
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun y : fixSpace g => y.1) hzw
      have hle : Nat.card {z : Z // σ' z = z} ≤ Nat.card (fixSpace g) :=
        Nat.card_le_card_of_injective toC htoC
      rwa [hCcard4] at hle
    have hfix_ge : 2 ≤ Nat.card {z : Z // σ' z = z} := by
      let z0 : Z := ⟨0, by simp⟩
      let zv : Z := ⟨v, hQv⟩
      have h0 : σ' z0 = z0 := by
        apply Subtype.ext
        change g 0 = 0
        simp
      have hv' : σ' zv = zv := by
        apply Subtype.ext
        change g v = v
        exact hgv
      let emb : Fin 2 → {z : Z // σ' z = z} := fun i =>
        if i = 0 then ⟨z0, h0⟩ else ⟨zv, hv'⟩
      have hemb : Function.Injective emb := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp [emb, z0, zv] at hij ⊢
        all_goals
          have h : v = 0 := by
            simpa [eq_comm] using congrArg Subtype.val hij
          exact hv h
      have := Nat.card_le_card_of_injective emb hemb
      simpa using this
    have hmodZ := CFSG.LocalAnalysis.GLTheoremA.SFM7Lin.card_perm_modEq σ' (p := 7) hσ'7
    change Nat.card {x : V // Q x = 0} ≡ Nat.card {z : Z // σ' z = z} [MOD 7] at hmodZ
    rw [hZ] at hmodZ
    set N := Nat.card {z : Z // σ' z = z} with hN
    have hNle : N ≤ 4 := hfix_le
    have hNge : 2 ≤ N := hfix_ge
    have hNmod : N ≡ 1 [MOD 7] := by
      have h120 : (120 : ℕ) ≡ 1 [MOD 7] := by norm_num [Nat.ModEq]
      exact (h120.symm.trans hmodZ).symm
    interval_cases N <;> norm_num at hNmod
  · have htop : fixSpace g = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← hfd, hfd8, hfin]
    apply LinearEquiv.ext
    intro x
    have hx : x ∈ fixSpace g := by
      rw [htop]
      exact Submodule.mem_top
    simpa using mem_fixSpace.mp hx

end CFSG.LocalAnalysis.GLTheoremA.SFM7Omega

