module

public import CFSG.CGT.PushingUpLit.SolK.PermCore
public import CFSG.CGT.PushingUpLit.BHS.AltCore

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

variable {n : ℕ}

theorem alt_cocycle_coboundary (hn : Odd n) (h5 : 5 ≤ n)
    (c : alternatingGroup (Fin n) → ↥(coreMod n))
    (hc : ∀ a b : alternatingGroup (Fin n),
      c (a * b) = c a * coreAct n (a : Perm (Fin n)) (c b)) :
    ∃ u : ↥(coreMod n), ∀ a : alternatingGroup (Fin n),
      c a = u * coreAct n (a : Perm (Fin n)) u := by
  classical
  have h3 : 3 ≤ n := by omega
  have hn0 : 0 < n := by omega
  set o : Fin n := ⟨0, hn0⟩ with ho
  have hcc : ∀ (a b : alternatingGroup (Fin n)) (k : Fin n),
      vcoord (c (a * b)) k = vcoord (c a) k + vcoord (c b) ((a : Perm (Fin n))⁻¹ k) := by
    intro a b k
    rw [hc, vcoord_mul, vcoord_coreAct]
  have hc1 : ∀ k, vcoord (c 1) k = 0 := by
    intro k
    have h := hcc 1 1 k
    rw [mul_one] at h
    have h' : vcoord (c 1) k = vcoord (c 1) k + vcoord (c 1) k := by
      simpa using h
    have : vcoord (c 1) k + vcoord (c 1) k = 0 := CharTwo.add_self_eq_zero _
    rw [← h'] at this
    exact this
  choose τ hτA hτo using fun i : Fin n => exists_alt_apply_eq h3 o i
  let T : Fin n → alternatingGroup (Fin n) := fun i => ⟨τ i, hτA i⟩
  have hTo : ∀ i, (T i : Perm (Fin n)) o = i := hτo
  let hA : ↥(stabAlt o) → alternatingGroup (Fin n) := fun h =>
    ⟨h.1, mem_alternatingGroup.2 (mem_stabAlt.1 h.2).1⟩
  have hAmul : ∀ h h', hA (h * h') = hA h * hA h' := fun h h' => Subtype.ext rfl
  have hAone : hA 1 = 1 := Subtype.ext rfl
  let f : ↥(stabAlt o) →* Multiplicative (ZMod 2) :=
    { toFun := fun h => Multiplicative.ofAdd (vcoord (c (hA h)) o)
      map_one' := by
        show Multiplicative.ofAdd (vcoord (c (hA 1)) o) = 1
        rw [hAone, hc1]
        rfl
      map_mul' := by
        intro h h'
        have hho : (hA h : Perm (Fin n))⁻¹ o = o := by
          rw [Equiv.Perm.inv_eq_iff_eq]
          exact ((mem_stabAlt.1 h.2).2).symm
        show Multiplicative.ofAdd (vcoord (c (hA (h * h'))) o) = _
        rw [hAmul, hcc, hho]
        rfl }
  have hf : ∀ h : ↥(stabAlt o), vcoord (c (hA h)) o = 0 := by
    intro h
    have := hom_stabAlt_eq_one o (K := Multiplicative (ZMod 2))
      (fun k => by
        have : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by decide
        exact this k) f h
    exact Multiplicative.ofAdd.injective this
  have key : ∀ (σ : alternatingGroup (Fin n)) (i : Fin n),
      vcoord (c σ) i = vcoord (c (T i)) i + vcoord (c (T ((σ : Perm (Fin n))⁻¹ i)))
        ((σ : Perm (Fin n))⁻¹ i) := by
    intro σ i
    set j : Fin n := (σ : Perm (Fin n))⁻¹ i with hj
    have hσj : (σ : Perm (Fin n)) j = i := by simp [hj]
    let ρ : alternatingGroup (Fin n) := (T i)⁻¹ * (σ * T j)
    have hρo : (ρ : Perm (Fin n)) o = o := by
      show ((T i : Perm (Fin n))⁻¹) ((σ : Perm (Fin n)) ((T j : Perm (Fin n)) o)) = o
      rw [hTo, hσj, Equiv.Perm.inv_eq_iff_eq]
      exact (hTo i).symm
    have hρmem : (ρ : Perm (Fin n)) ∈ stabAlt o :=
      mem_stabAlt.2 ⟨mem_alternatingGroup.1 ρ.2, hρo⟩
    have h0 := hf ⟨ρ.1, hρmem⟩
    have e1 : vcoord (c ρ) o = vcoord (c (T i)⁻¹) o +
        (vcoord (c σ) i + vcoord (c (T j)) j) := by
      show vcoord (c ((T i)⁻¹ * (σ * T j))) o = _
      rw [hcc, hcc]
      have : ((T i)⁻¹ : alternatingGroup (Fin n)).1⁻¹ o = i := by
        show ((T i : Perm (Fin n))⁻¹)⁻¹ o = i
        rw [inv_inv]
        exact hTo i
      rw [this]
    have e2 : vcoord (c (T i)⁻¹) o + vcoord (c (T i)) i = 0 := by
      have := hcc (T i)⁻¹ (T i) o
      rw [inv_mul_cancel] at this
      rw [hc1] at this
      have h2 : ((T i)⁻¹ : alternatingGroup (Fin n)).1⁻¹ o = i := by
        show ((T i : Perm (Fin n))⁻¹)⁻¹ o = i
        rw [inv_inv]
        exact hTo i
      rw [h2] at this
      exact this.symm
    have h0' : vcoord (c ρ) o = 0 := h0
    rw [h0'] at e1
    have key2 : ∀ a b x y : ZMod 2, a + b = 0 → 0 = a + (x + y) → x = b + y := by decide
    exact key2 _ _ _ _ e2 e1
  let u₀ : Fin n → ZMod 2 := fun i => vcoord (c (T i)) i
  refine ⟨mkEven (fun i => u₀ i + ∑ y, u₀ y) (sum_shift hn u₀), fun σ => ?_⟩
  refine vcoord_ext fun i => ?_
  rw [vcoord_mul, vcoord_coreAct, vcoord_mkEven, vcoord_mkEven, key σ i]
  have : ∀ a b t : ZMod 2, a + b = (a + t) + (b + t) := by decide
  exact this _ _ _

theorem cocycle_coboundary_of_surj (hn : Odd n) (h5 : 5 ≤ n) {X : Type*} [Group X]
    (ρ : X →* Perm (Fin n)) (hρ : ∀ x, ρ x ∈ alternatingGroup (Fin n))
    (hρs : ∀ a ∈ alternatingGroup (Fin n), ∃ x, ρ x = a)
    (c : X → ↥(coreMod n)) (hc : ∀ x y, c (x * y) = c x * coreAct n (ρ x) (c y))
    (hker : ∀ x, ρ x = 1 → c x = 1) :
    ∃ u : ↥(coreMod n), ∀ x, c x = u * coreAct n (ρ x) u := by
  classical
  let ρ' : X →* ↥(alternatingGroup (Fin n)) := ρ.codRestrict _ hρ
  have hρ's : Function.Surjective ρ' := fun a => by
    obtain ⟨x, hx⟩ := hρs a a.2
    exact ⟨x, Subtype.ext hx⟩
  let lift : alternatingGroup (Fin n) → X := Function.surjInv hρ's
  have hlift : ∀ a, ρ' (lift a) = a := Function.surjInv_eq hρ's
  have hliftρ : ∀ a, ρ (lift a) = (a : Perm (Fin n)) := fun a => congrArg Subtype.val (hlift a)
  have hcongr : ∀ x y, ρ x = ρ y → c x = c y := by
    intro x y hxy
    have hk : ρ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have h1 := hc x (x⁻¹ * y)
    rw [mul_inv_cancel_left, hker _ hk, map_one, mul_one] at h1
    exact h1.symm
  obtain ⟨u, hu⟩ := alt_cocycle_coboundary hn h5 (fun a => c (lift a)) (fun a b => by
    have h1 : ρ (lift (a * b)) = ρ (lift a * lift b) := by
      rw [map_mul, hliftρ, hliftρ, hliftρ]
      rfl
    rw [hcongr _ _ h1, hc, hliftρ])
  exact ⟨u, fun x =>
    (hcongr x _ (hliftρ (ρ' x)).symm).trans (hu (ρ' x))⟩

section Fix

@[expose] def epsVec (hn : Odd n) (i : Fin n) : ↥(coreMod n) :=
  mkEven (fun m => 1 + if m = i then 1 else 0) (by
    have h1 : ∑ m : Fin n, (1 + if m = i then (1 : ZMod 2) else 0) = (n : ZMod 2) + 1 := by
      rw [Finset.sum_add_distrib]
      simp
    rw [h1, hn.natCast_zmod_two]
    exact CharTwo.add_self_eq_zero _)

theorem vcoord_epsVec (hn : Odd n) (i m : Fin n) :
    vcoord (epsVec hn i) m = 1 + if m = i then 1 else 0 := rfl

theorem coreAct_epsVec (hn : Odd n) (σ : Perm (Fin n)) (i : Fin n) :
    coreAct n σ (epsVec hn i) = epsVec hn (σ i) := by
  refine vcoord_ext fun m => ?_
  rw [vcoord_coreAct, vcoord_epsVec, vcoord_epsVec]
  have : (σ⁻¹ m = i) ↔ (m = σ i) := by
    rw [Equiv.Perm.inv_eq_iff_eq]
  simp only [this]

theorem exists_equivariant_section {W : Type*} [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1)
    (hn : Odd n) (h5 : 5 ≤ n) (act : alternatingGroup (Fin n) →* MulAut W)
    (β : W →* ↥(coreMod n)) (hβ : Function.Surjective β)
    (hequiv : ∀ (σ : alternatingGroup (Fin n)) (w : W),
      β (act σ w) = coreAct n (σ : Perm (Fin n)) (β w))
    (hfix : ∀ w : W, β w = 1 → ∀ σ, act σ w = w) :
    ∃ s : ↥(coreMod n) →* W, (∀ v, β (s v) = v) ∧
      ∀ (σ : alternatingGroup (Fin n)) v, act σ (s v) = s (coreAct n (σ : Perm (Fin n)) v) := by
  classical
  have h3 : 3 ≤ n := by omega
  have hn0 : 0 < n := by omega
  set o : Fin n := ⟨0, hn0⟩ with ho
  obtain ⟨b₀, hb₀⟩ := hβ (epsVec hn o)
  let hA : ↥(stabAlt o) → alternatingGroup (Fin n) := fun h =>
    ⟨h.1, mem_alternatingGroup.2 (mem_stabAlt.1 h.2).1⟩
  have hAmul : ∀ h h', hA (h * h') = hA h * hA h' := fun h h' => Subtype.ext rfl
  have hAone : hA 1 = 1 := Subtype.ext rfl
  have hχker : ∀ h : ↥(stabAlt o), β (act (hA h) b₀ * b₀⁻¹) = 1 := by
    intro h
    rw [map_mul, map_inv, hequiv, hb₀, coreAct_epsVec]
    have : (hA h : Perm (Fin n)) o = o := (mem_stabAlt.1 h.2).2
    rw [this]
    exact mul_inv_cancel _
  let χ : ↥(stabAlt o) →* W :=
    { toFun := fun h => act (hA h) b₀ * b₀⁻¹
      map_one' := by simp [hAone]
      map_mul' := by
        intro h h'
        set u : W := act (hA h') b₀ * b₀⁻¹ with hu
        have hf : act (hA h) u = u := hfix _ (hχker h') _
        have hx : act (hA h') b₀ = u * b₀ := by rw [hu, inv_mul_cancel_right]
        have e : act (hA h) (act (hA h') b₀) = u * act (hA h) b₀ := by
          rw [hx, map_mul, hf]
        simp only [hAmul, map_mul, MulAut.mul_apply]
        rw [e]
        ac_rfl }
  have hχ : ∀ h : ↥(stabAlt o), act (hA h) b₀ = b₀ := by
    intro h
    have := hom_stabAlt_eq_one o hW χ h
    have h' : act (hA h) b₀ * b₀⁻¹ = 1 := this
    exact mul_inv_eq_one.1 h'
  choose τ hτA hτo using fun i : Fin n => exists_alt_apply_eq h3 o i
  let T : Fin n → alternatingGroup (Fin n) := fun i => ⟨τ i, hτA i⟩
  have hTo : ∀ i, (T i : Perm (Fin n)) o = i := hτo
  let Y : Fin n → W := fun i => act (T i) b₀
  have hY1 : ∀ i, β (Y i) = epsVec hn i := by
    intro i
    show β (act (T i) b₀) = _
    rw [hequiv, hb₀, coreAct_epsVec, hTo]
  have hY2 : ∀ (σ : alternatingGroup (Fin n)) i, act σ (Y i) = Y ((σ : Perm (Fin n)) i) := by
    intro σ i
    have hmem : ((T ((σ : Perm (Fin n)) i))⁻¹ * σ * T i : alternatingGroup (Fin n)).1 ∈
        stabAlt o := by
      refine mem_stabAlt.2 ⟨mem_alternatingGroup.1 (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ (T _).2) σ.2) (T i).2), ?_⟩
      show ((T ((σ : Perm (Fin n)) i) : Perm (Fin n))⁻¹) ((σ : Perm (Fin n))
        ((T i : Perm (Fin n)) o)) = o
      rw [hTo, Equiv.Perm.inv_eq_iff_eq]
      exact (hTo _).symm
    have h1 := hχ ⟨_, hmem⟩
    have h2 : act ((T ((σ : Perm (Fin n)) i))⁻¹ * σ * T i) b₀ = b₀ := h1
    show act σ (act (T i) b₀) = act (T ((σ : Perm (Fin n)) i)) b₀
    have h3' : act σ (act (T i) b₀) = act (σ * T i) b₀ := by rw [map_mul]; rfl
    rw [h3']
    have h4 : σ * T i = T ((σ : Perm (Fin n)) i) * ((T ((σ : Perm (Fin n)) i))⁻¹ * σ * T i) := by
      group
    rw [h4, map_mul, MulAut.mul_apply, h2]
  let s : ↥(coreMod n) →* W :=
    { toFun := vsum Y
      map_one' := vsum_one Y
      map_mul' := vsum_mul hW Y }
  have hs1 : ∀ v, β (s v) = v := by
    intro v
    refine vcoord_ext fun q => ?_
    show vcoord (β (vsum Y v)) q = _
    rw [vcoord_map_vsum]
    simp only [hY1, vcoord_epsVec]
    have h1 : ∑ m : Fin n, vcoord v m * (1 + if q = m then (1 : ZMod 2) else 0) =
        ∑ m, vcoord v m + vcoord v q := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib]
      congr 1
      simp [mul_ite]
    rw [h1, sum_vcoord, zero_add]
  refine ⟨s, hs1, fun σ v => ?_⟩
  show act σ (vsum Y v) = vsum Y (coreAct n (σ : Perm (Fin n)) v)
  simp only [vsum, map_prod, map_pow, hY2]
  refine Fintype.prod_equiv (σ : Perm (Fin n)) _ _ fun m => ?_
  simp [vcoord_coreAct]

variable {W : Type} [CommGroup W] {E : Subgroup (MulAut W)}

theorem altNatData_fixV_eq_bot (hW : ∀ w : W, w ^ 2 = 1) (hn : Odd n) (h5 : 5 ≤ n)
    (D : AltNatData E n) : fixV E = ⊥ := by
  classical
  have h3 : 3 ≤ n := by omega
  let act : alternatingGroup (Fin n) →* MulAut W := E.subtype.comp D.θ.symm.toMonoidHom
  have act_eq : ∀ x : E, act (D.θ x) = (x : MulAut W) := fun x => by simp [act]
  have act_equivar : ∀ σ w, D.β (act σ w) = coreAct n (σ : Perm (Fin n)) (D.β w) := by
    intro σ w
    have := D.equivar (D.θ.symm σ) w
    simpa [act] using this
  have hfixE : ∀ w, D.β w = 1 → ∀ σ, act σ w = w := fun w hw σ =>
    D.ker_fix w hw _ (D.θ.symm σ).2
  obtain ⟨s, hs1, hs2⟩ := exists_equivariant_section hW hn h5 act D.β D.surj act_equivar hfixE
  have hs3 : ∀ (x : E) v, (x : MulAut W) (s v) = s (coreAct n ((D.θ x : alternatingGroup (Fin n)) :
      Perm (Fin n)) v) := by
    intro x v
    rw [← act_eq x, hs2]
  have hcomm : commV E ≤ s.range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨x, hx, v, rfl⟩
    have hc : (s (D.β v))⁻¹ * v ∈ fixV E := by
      have : D.β ((s (D.β v))⁻¹ * v) = 1 := by
        rw [map_mul, map_inv, hs1]
        exact inv_mul_cancel _
      exact (D.ker_iff hn h3 _).1 this
    have hxc : x ((s (D.β v))⁻¹ * v) = (s (D.β v))⁻¹ * v := hc x hx
    have hv : v = s (D.β v) * ((s (D.β v))⁻¹ * v) := by group
    have hxv : x v = x (s (D.β v)) * ((s (D.β v))⁻¹ * v) := by
      conv_lhs => rw [hv]
      rw [map_mul, hxc]
    have : x v * v⁻¹ = x (s (D.β v)) * (s (D.β v))⁻¹ := by
      conv_lhs => rw [hxv]
      group
    rw [this]
    refine s.range.mul_mem ?_ (s.range.inv_mem ?_)
    · have := hs3 ⟨x, hx⟩ (D.β v)
      exact ⟨_, this.symm⟩
    · exact ⟨_, rfl⟩
  rw [eq_bot_iff]
  intro c hc
  have hβ : D.β c = 1 := (D.ker_iff hn h3 c).2 hc
  have hmem : c ∈ s.range := hcomm (by rw [D.comm_top]; exact Subgroup.mem_top _)
  obtain ⟨u, rfl⟩ := hmem
  have hu : u = 1 := by rw [← hs1 u]; exact hβ
  rw [hu, map_one]
  exact Subgroup.one_mem _

end Fix

end CFSG.CGT.PushingUpLit.SolK
