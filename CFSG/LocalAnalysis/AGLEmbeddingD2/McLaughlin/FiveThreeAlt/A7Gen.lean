module

public import CFSG.RankThree.FFModules.FixSubConj
public import CFSG.RankThree.FFModules.ChiefFactors
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Orb
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs
public import CFSG.RankThree.FFModules.RepMulAut
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open Equiv Equiv.Perm CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

theorem exists_conj_embedding7 {K : Type*} [Group K] (Ls : Subgroup K) [Ls.Normal]
    (φ : ↥Ls ≃* alternatingGroup (Fin 7)) :
    ∃ e : K →* Perm (Fin 7),
      (∀ x : ↥Ls, e (x : K) = (φ x : Perm (Fin 7))) ∧
      (∀ (g : K) (x : ↥Ls), (φ (MulAut.conjNormal g x) : Perm (Fin 7)) =
        e g * (φ x : Perm (Fin 7)) * (e g)⁻¹) ∧
      (∀ g : K, e g = 1 → ∀ x : ↥Ls, g * (x : K) * g⁻¹ = (x : K)) ∧
      (∀ g : K, (∀ x : ↥Ls, g * (x : K) * g⁻¹ = (x : K)) → e g = 1) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  let cEquiv : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective _ hbij
  let ec : K →* MulAut (alternatingGroup (Fin 7)) :=
    (MulAut.congr φ).toMonoidHom.comp (MulAut.conjNormal (H := Ls))
  let e : K →* Perm (Fin 7) := cEquiv.symm.toMonoidHom.comp ec
  have hce : ∀ g : K, MulAut.conjNormal (e g) = ec g := fun g => by
    show cEquiv (cEquiv.symm (ec g)) = ec g
    exact cEquiv.apply_symm_apply _
  have hconj : ∀ (g : K) (x : ↥Ls),
      (φ (MulAut.conjNormal g x) : Perm (Fin 7)) = e g * (φ x : Perm (Fin 7)) * (e g)⁻¹ := by
    intro g x
    have h1 := congrArg (fun f : MulAut (alternatingGroup (Fin 7)) =>
      ((f (φ x) : alternatingGroup (Fin 7)) : Perm (Fin 7))) (hce g)
    simp only [MulAut.conjNormal_apply] at h1
    rw [h1]
    simp [ec, MulAut.congr_apply]
  have hL : ∀ x : ↥Ls, e (x : K) = (φ x : Perm (Fin 7)) := by
    intro x
    apply hbij.1
    rw [hce]
    ext a
    obtain ⟨y, rfl⟩ := φ.surjective a
    have h1 : (ec (x : K)) (φ y) = φ (MulAut.conjNormal (x : K) y) := by
      simp [ec, MulAut.congr_apply]
    rw [h1]
    have e1 : MulAut.conjNormal (x : K) y = x * y * x⁻¹ := by
      apply Subtype.ext
      simp
    rw [e1, map_mul, map_mul, map_inv]
    simp
  refine ⟨e, hL, hconj, ?_, ?_⟩
  · intro g hg x
    have h1 := hconj g x
    rw [hg] at h1
    simp only [one_mul, inv_one, mul_one] at h1
    have h2 : MulAut.conjNormal g x = x := φ.injective (Subtype.ext h1)
    have h3 := congrArg Subtype.val h2
    simpa using h3
  · intro g hg
    have h1 : (MulAut.conjNormal (H := Ls) g) = 1 := by
      ext x
      simp [hg x]
    have h2 : ec g = 1 := by
      show (MulAut.congr φ) (MulAut.conjNormal (H := Ls) g) = 1
      rw [h1]
      exact map_one _
    show cEquiv.symm (ec g) = 1
    rw [h2, map_one]

theorem four_le_finrank_of_alt7 {K : Type*} [Group K] (eK : K ≃* alternatingGroup (Fin 7))
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (τ : Representation (ZMod 2) K M) (hnt : ∃ k : K, τ k ≠ 1) :
    4 ≤ Module.finrank (ZMod 2) M := by
  classical
  have : Finite K := Finite.of_equiv _ eK.symm.toEquiv
  have hsimple : IsSimpleGroup K := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact eK.isSimpleGroup
  have hinj : ∀ k : K, τ k = 1 → k = 1 := by
    intro k hk
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal τ.asGroupHom.ker with h | h
    · have hk' : k ∈ τ.asGroupHom.ker := by
        rw [MonoidHom.mem_ker]
        apply Units.ext
        rw [Representation.asGroupHom_apply, Units.val_one]
        exact hk
      rw [h, Subgroup.mem_bot] at hk'
      exact hk'
    · exfalso
      obtain ⟨k₀, hk₀⟩ := hnt
      apply hk₀
      have : k₀ ∈ τ.asGroupHom.ker := h ▸ Subgroup.mem_top k₀
      rw [MonoidHom.mem_ker] at this
      have h2 := congrArg Units.val this
      rwa [Representation.asGroupHom_apply, Units.val_one] at h2
  have h5 : 5 ∣ Nat.card K := by
    have h1 : Nat.card K = Nat.card (alternatingGroup (Fin 7)) := Nat.card_congr eK.toEquiv
    rw [h1, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 h5
  have hx5 : x ^ 5 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hτx : τ x ≠ 1 := fun h => hx1 (hinj x h)
  let g : MulAut (Multiplicative M) := repMulAut τ x
  have hg5 : g ^ 5 = 1 := by
    show (repMulAut τ x) ^ 5 = 1
    rw [← map_pow, hx5, map_one]
  have hg1 : g ≠ 1 := by
    intro h
    apply hτx
    ext v
    have := congrArg (fun φ : MulAut (Multiplicative M) =>
      Multiplicative.toAdd (φ (Multiplicative.ofAdd v))) h
    simpa [g, repMulAut_apply] using this
  have h16 := CFSG.QuasithinUnique.B42A57.card_ge_sixteen_of_order_five
    (W := Multiplicative M) (fun w => by rw [← pow_two]; exact multiplicative_sq w) g hg5 hg1
  have hcard : Nat.card (Multiplicative M) = 2 ^ Module.finrank (ZMod 2) M := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative M ≃ M),
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcard] at h16
  by_contra hlt
  push Not at hlt
  have : 2 ^ Module.finrank (ZMod 2) M ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem invariant_fixSub {Hs : Type*} [Group Hs] {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) Hs Q) {P : Subgroup Hs} (hP : P.Normal) :
    ∀ h : Hs, ∀ q ∈ fixSub σ P, σ h q ∈ fixSub σ P :=
  fun h _ hq => CFSG.RankThree.FFModules.rep_apply_mem_fixSub_of_normal σ hP h hq

theorem rep_trivial_of_normal_two {Hs : Type*} [Group Hs] {Q : Type*} [AddCommGroup Q]
    [Module (ZMod 2) Q] [Finite Q] [Nontrivial Q] (σ : Representation (ZMod 2) Hs Q)
    (hirr : ∀ N : Submodule (ZMod 2) Q, (∀ h : Hs, ∀ q ∈ N, σ h q ∈ N) → N = ⊥ ∨ N = ⊤)
    {P : Subgroup Hs} (hP : P.Normal) (hP2 : IsPGroup 2 P) : ∀ p ∈ P, σ p = 1 := by
  obtain ⟨x, hx0, hxfix⟩ := exists_fixed_ne_zero_of_isPGroup σ hP2
  rcases hirr _ (invariant_fixSub σ hP) with h | h
  · exfalso
    have : x ∈ fixSub σ P := mem_fixSub.2 hxfix
    rw [h, Submodule.mem_bot] at this
    exact hx0 this
  · intro p hp
    ext q
    have : q ∈ fixSub σ P := by rw [h]; exact Submodule.mem_top
    rw [Module.End.one_apply]
    exact mem_fixSub.1 this p hp

theorem finrank_le_sum_codim {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q] {k : ℕ}
    (F : Fin k → Submodule (ZMod 2) Q) (hF : ⨅ i, F i = ⊥) :
    Module.finrank (ZMod 2) Q ≤
      ∑ i, (Module.finrank (ZMod 2) Q - Module.finrank (ZMod 2) (F i)) := by
  classical
  have key : ∀ s : Finset (Fin k), Module.finrank (ZMod 2) Q ≤
      ∑ i ∈ s, (Module.finrank (ZMod 2) Q - Module.finrank (ZMod 2) (F i)) +
        Module.finrank (ZMod 2) ↥(s.inf F) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.inf_empty, finrank_top, zero_add]
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.inf_insert]
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq (F j) (s.inf F)
      have h2 : Module.finrank (ZMod 2) ↥(F j ⊔ s.inf F) ≤ Module.finrank (ZMod 2) Q :=
        Submodule.finrank_le _
      have h3 : Module.finrank (ZMod 2) ↥(F j) ≤ Module.finrank (ZMod 2) Q :=
        Submodule.finrank_le _
      omega
  have := key Finset.univ
  rw [Finset.inf_univ_eq_iInf, hF] at this
  simpa using this

theorem finrank_le_of_generation {Hs : Type*} [Group Hs] {Q : Type*} [AddCommGroup Q]
    [Module (ZMod 2) Q] [Finite Q] (σ : Representation (ZMod 2) Hs Q) (e : Hs →* Perm (Fin 7))
    (Ls B' : Subgroup Hs) (hker : ∀ h : Hs, e h = 1 → ∀ q, σ h q = q)
    (hfixL : ∀ v : Q, (∀ l ∈ Ls, σ l v = v) → v = 0)
    (hLA : ∀ l ∈ Ls, e l ∈ alternatingGroup (Fin 7)) {k : ℕ} (g : Fin k → Hs)
    (f : Fin k → Perm (Fin 7)) (hg : ∀ i, e (g i) = f i)
    (hcl : alternatingGroup (Fin 7) ≤
      Subgroup.closure {x | ∃ i, ∃ b ∈ B'.map e, x = f i * b * (f i)⁻¹}) :
    Module.finrank (ZMod 2) Q ≤
      k * (Module.finrank (ZMod 2) Q - Module.finrank (ZMod 2) ↥(fixSub σ B')) := by
  classical
  set C := fixSub σ B' with hC
  have hinj : ∀ i, Function.Injective (σ (g i)) := by
    intro i x y hxy
    have h1 : σ (g i)⁻¹ (σ (g i) x) = σ (g i)⁻¹ (σ (g i) y) := by rw [hxy]
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
  let F : Fin k → Submodule (ZMod 2) Q := fun i => C.map (σ (g i))
  have hFbot : ⨅ i, F i = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_iInf] at hv
    have hfix : ∀ i, ∀ b ∈ B', σ (g i * b * (g i)⁻¹) v = v := by
      intro i b hb
      obtain ⟨c, hc, hcv⟩ := Submodule.mem_map.1 (hv i)
      have hcb : σ b c = c := mem_fixSub.1 hc b hb
      rw [← hcv, ← Module.End.mul_apply, ← map_mul, show g i * b * (g i)⁻¹ * g i = g i * b by group,
        map_mul, Module.End.mul_apply, hcb]
    let Stab : Subgroup Hs :=
      { carrier := {h | σ h v = v}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          have hx' : σ x v = v := hx
          have hy' : σ y v = v := hy
          show σ (x * y) v = v
          rw [map_mul, Module.End.mul_apply, hy', hx']
        inv_mem' := fun {x} hx => by
          have hx' : σ x v = v := hx
          show σ x⁻¹ v = v
          have := congrArg (fun w => σ x⁻¹ w) hx'
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
          exact this.symm }
    let Dg : Subgroup Hs := Subgroup.closure {x | ∃ i, ∃ b ∈ B', x = g i * b * (g i)⁻¹}
    have hDS : Dg ≤ Stab := by
      refine (Subgroup.closure_le Stab).2 ?_
      rintro _ ⟨i, b, hb, rfl⟩
      exact hfix i b hb
    have hAle : alternatingGroup (Fin 7) ≤ Dg.map e := by
      refine hcl.trans ?_
      rw [Subgroup.closure_le]
      rintro _ ⟨i, x, hx, rfl⟩
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
      rw [← hg i, ← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map.2 ⟨_, Subgroup.subset_closure ⟨i, b, hb, rfl⟩, rfl⟩
    apply hfixL v
    intro l hl
    obtain ⟨d, hd, hde⟩ := Subgroup.mem_map.1 (hAle (hLA l hl))
    have hdl : e (d⁻¹ * l) = 1 := by rw [map_mul, map_inv, hde, inv_mul_cancel]
    have h1 := hker _ hdl v
    have hdv : σ d v = v := hDS hd
    calc σ l v = σ d (σ (d⁻¹ * l) v) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = v := by rw [h1, hdv]
  have hsum := finrank_le_sum_codim F hFbot
  have hFeq : ∀ i, Module.finrank (ZMod 2) ↥(F i) = Module.finrank (ZMod 2) ↥C := fun i =>
    (Submodule.equivMapOfInjective (σ (g i)) (hinj i) C).finrank_eq.symm
  simp only [hFeq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
