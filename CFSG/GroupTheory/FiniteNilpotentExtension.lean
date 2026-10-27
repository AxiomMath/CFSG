module

public import CFSG.GroupTheory.FiniteNilpotentCocycle

public section

namespace CFSG.GroupTheory

universe u v

section AbelianKernel

variable {P : Type u} {F : Type v} [Group P] [Group F] [Finite F]

theorem exists_section_of_abelian_kernel
    (π : P →* F) (hπ : Function.Surjective π)
    (hcomm : ∀ a b : π.ker, a * b = b * a)
    (hdiv : Function.Bijective (fun k : π.ker => k ^ Nat.card F)) :
    ∃ s : F →* P, π.comp s = MonoidHom.id F := by
  classical
  let commK : CommMonoid π.ker := CommMonoid.mk hcomm
  let fintypeF : Fintype F := Fintype.ofFinite F
  let n : ℕ := Nat.card F
  let σ0 : F → P := Function.surjInv hπ
  have hσ0 : ∀ f : F, π (σ0 f) = f := fun f => Function.surjInv_eq hπ f
  let σ : F → P := fun f => σ0 f * (σ0 1)⁻¹
  have hσ : ∀ f : F, π (σ f) = f := by
    intro f
    dsimp only [σ]
    simp [map_mul, hσ0]
  have hσ1 : σ 1 = 1 := by
    dsimp only [σ]
    group
  let aFun : F → π.ker → π.ker := fun f k =>
    ⟨σ f * (k : P) * (σ f)⁻¹, by
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_mul, map_inv, hσ f, k.2, mul_one, mul_inv_cancel]⟩
  let aAut : F → MulAut π.ker := fun f =>
    { toFun := aFun f
      invFun := fun k =>
        ⟨(σ f)⁻¹ * (k : P) * σ f, by
          rw [MonoidHom.mem_ker]
          rw [map_mul, map_mul, map_inv, hσ f, k.2, mul_one, inv_mul_cancel]⟩
      left_inv := by
        intro k
        apply Subtype.ext
        dsimp only [aFun]
        group
      right_inv := by
        intro k
        apply Subtype.ext
        dsimp only [aFun]
        group
      map_mul' := by
        intro k l
        apply Subtype.ext
        dsimp only [aFun]
        simp only [Subgroup.coe_mul]
        group }
  have aAut_one : aAut 1 = 1 := by
    ext k
    dsimp only [aAut, aFun]
    simp only [hσ1]
    change (1 : P) * (k : P) * (1 : P)⁻¹ = (k : P)
    group
  have aAut_mul : ∀ f g : F, aAut (f * g) = aAut f * aAut g := by
    intro f g
    ext k
    dsimp only [aAut, aFun]
    let d : π.ker :=
      ⟨(σ (f * g))⁻¹ * (σ f * σ g), by
        rw [MonoidHom.mem_ker]
        rw [map_mul, map_mul, map_inv, hσ, hσ, hσ]
        group⟩
    have hσfg : σ (f * g) = σ f * σ g * (d : P)⁻¹ := by
      dsimp only [d]
      group
    have hd_comm : (d : P)⁻¹ * (k : P) = (k : P) * (d : P)⁻¹ := by
      have h := congrArg Subtype.val (hcomm d k)
      have h' : (d : P) * (k : P) = (k : P) * (d : P) := by
        simpa only [Subgroup.coe_mul] using h
      have hcalc : (k : P) * (d : P)⁻¹ = (d : P)⁻¹ * (k : P) := by
        calc
          (k : P) * (d : P)⁻¹ =
              (d : P)⁻¹ * ((d : P) * (k : P)) * (d : P)⁻¹ := by group
          _ = (d : P)⁻¹ * ((k : P) * (d : P)) * (d : P)⁻¹ := by rw [h']
          _ = (d : P)⁻¹ * (k : P) := by group
      exact hcalc.symm
    change σ (f * g) * (k : P) * (σ (f * g))⁻¹ =
      σ f * (σ g * (k : P) * (σ g)⁻¹) * (σ f)⁻¹
    rw [hσfg]
    rw [show σ f * σ g * (d : P)⁻¹ * (k : P) =
        σ f * σ g * ((d : P)⁻¹ * (k : P)) by group]
    rw [hd_comm]
    group
  let α : F →* MulAut π.ker :=
    { toFun := aAut
      map_one' := aAut_one
      map_mul' := aAut_mul }
  have hα_apply : ∀ (g : F) (k : π.ker),
      (α g k : P) = σ g * (k : P) * (σ g)⁻¹ := by
    intro g k
    rfl
  let c : F × F → π.ker := fun p =>
    ⟨σ p.1 * σ p.2 * (σ (p.1 * p.2))⁻¹, by
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_mul, map_inv, hσ, hσ, hσ, mul_inv_cancel]⟩
  let f : F × F → π.ker := fun p => (c p)⁻¹
  have hc_cocycle : ∀ g h j : F,
      c (g, h) * c (g * h, j) = α g (c (h, j)) * c (g, h * j) := by
    intro g h j
    apply Subtype.ext
    change (c (g, h) : P) * (c (g * h, j) : P) =
      (aFun g (c (h, j)) : P) * (c (g, h * j) : P)
    dsimp only [aFun, c]
    group
  have hf_cocycle : ∀ g h j : F,
      f (g, h) * f (g * h, j) = f (g, h * j) * α g (f (h, j)) := by
    intro g h j
    calc
      f (g, h) * f (g * h, j) = (c (g, h) * c (g * h, j))⁻¹ := by
        dsimp only [f]
        rw [mul_inv_rev]
        exact hcomm (c (g, h))⁻¹ (c (g * h, j))⁻¹
      _ = (α g (c (h, j)) * c (g, h * j))⁻¹ := by rw [hc_cocycle]
      _ = f (g, h * j) * α g (f (h, j)) := by
        dsimp only [f]
        rw [mul_inv_rev, map_inv]
  let Fsum : F → π.ker := fun g => ∏ h : F, f (g, h)
  let b : F → π.ker := fun g => Classical.choose (hdiv.2 (Fsum g))
  have hb : ∀ g : F, b g ^ n = Fsum g := by
    intro g
    exact Classical.choose_spec (hdiv.2 (Fsum g))
  have hprod : ∀ g h : F, f (g, h) ^ n * Fsum (g * h) = α g (Fsum h) * Fsum g := by
    intro g h
    calc
      f (g, h) ^ n * Fsum (g * h) =
          (∏ _ : F, f (g, h)) * (∏ j : F, f (g * h, j)) := by
            rw [Finset.prod_const]
            congr 1
            dsimp only [n]
            rw [Nat.card_eq_fintype_card]
            rfl
      _ = ∏ j : F, f (g, h) * f (g * h, j) := by
            rw [Finset.prod_mul_distrib]
      _ = ∏ j : F, f (g, h * j) * α g (f (h, j)) := by
            apply Finset.prod_congr rfl
            intro j _
            rw [hf_cocycle]
      _ = (∏ j : F, f (g, h * j)) * (∏ j : F, α g (f (h, j))) := by
            rw [Finset.prod_mul_distrib]
      _ = Fsum g * α g (Fsum h) := by
            congr 1
            · dsimp only [Fsum]
              exact Equiv.prod_comp (Equiv.mulLeft h) (fun j : F => f (g, j))
            · dsimp only [Fsum]
              rw [map_prod]
      _ = α g (Fsum h) * Fsum g := by
            rw [mul_comm (Fsum g) (α g (Fsum h))]
  have hdelta : ∀ g h : F,
      α g (b h) * b g * (b (g * h))⁻¹ = f (g, h) := by
    intro g h
    apply hdiv.1
    calc
      (α g (b h) * b g * (b (g * h))⁻¹) ^ n =
          (α g (b h)) ^ n * (b g) ^ n * ((b (g * h)) ^ n)⁻¹ := by
            rw [mul_pow, mul_pow, inv_pow]
      _ = α g (Fsum h) * Fsum g * (Fsum (g * h))⁻¹ := by
            rw [← map_pow, hb h, hb g, hb (g * h)]
      _ = f (g, h) ^ n := by
            rw [← hprod g h]
            group
      _ = (f (g, h)) ^ n := rfl
  have hdelta' : ∀ g h : F,
      (b g : P) * (α g (b h) : P) = (b (g * h) : P) * (f (g, h) : P) := by
    intro g h
    have hproof : (α g (b h) : P) * (b g : P) * (b (g * h) : P)⁻¹ =
        (f (g, h) : P) := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        congrArg Subtype.val (hdelta g h)
    have hbg : (b g : P) * (α g (b h) : P) =
        (α g (b h) : P) * (b g : P) :=
      congrArg Subtype.val (hcomm (b g) (α g (b h)))
    have hfb : (f (g, h) : P) * (b (g * h) : P) =
        (b (g * h) : P) * (f (g, h) : P) :=
      congrArg Subtype.val (hcomm (f (g, h)) (b (g * h)))
    calc
      (b g : P) * (α g (b h) : P) =
          (α g (b h) : P) * (b g : P) := hbg
      _ = ((α g (b h) : P) * (b g : P) * (b (g * h) : P)⁻¹) * (b (g * h) : P) := by
            group
      _ = (f (g, h) : P) * (b (g * h) : P) := by rw [hproof]
      _ = (b (g * h) : P) * (f (g, h) : P) := hfb
  have hb1 : b 1 = 1 := by
    apply hdiv.1
    change (b 1) ^ n = (1 : π.ker) ^ n
    rw [hb 1, one_pow]
    dsimp only [Fsum]
    apply Finset.prod_eq_one
    intro h _
    apply Subtype.ext
    dsimp only [f, c]
    change (σ 1 * σ h * (σ (1 * h))⁻¹)⁻¹ = (1 : P)
    simp only [hσ1, one_mul]
    group
  let s : F →* P :=
    MonoidHom.mk' (fun g => (b g : P) * σ g) (by
      intro g h
      symm
      calc
        ((b g : P) * σ g) * ((b h : P) * σ h) =
            (b g : P) * (σ g * (b h : P) * (σ g)⁻¹) * (σ g * σ h) := by group
        _ = (b g : P) * (α g (b h) : P) * (σ g * σ h) := rfl
        _ = (b g : P) * (α g (b h) : P) *
            ((c (g, h) : P) * σ (g * h)) := by
              rw [show σ g * σ h = (c (g, h) : P) * σ (g * h) by
                dsimp only [c]
                group]
        _ = ((b g : P) * (α g (b h) : P) * (c (g, h) : P)) * σ (g * h) := by group
        _ = (((b (g * h) : P) * (f (g, h) : P)) * (c (g, h) : P)) * σ (g * h) := by
              rw [hdelta']
        _ = (b (g * h) : P) * σ (g * h) := by
              dsimp only [f]
              calc
                (b (g * h) : P) * (c (g, h) : P)⁻¹ * (c (g, h) : P) *
                    σ (g * h) =
                    (b (g * h) : P) * ((c (g, h) : P)⁻¹ * (c (g, h) : P)) *
                      σ (g * h) := by group
                _ = (b (g * h) : P) * σ (g * h) := by
                    rw [inv_mul_cancel, mul_one])
  refine ⟨s, ?_⟩
  ext g
  change π ((b g : P) * σ g) = g
  rw [map_mul, (b g).2, hσ g, one_mul]

end AbelianKernel


section GenericAux

private theorem center_normal_of_normal {G : Type u} [Group G] {K : Subgroup G} [K.Normal] :
    ((Subgroup.center K).map K.subtype).Normal := by
  refine ⟨fun z hz g => ?_⟩
  obtain ⟨z', hz', rfl⟩ := hz
  have hgz : g * (z' : G) * g⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem _ z'.2 g
  refine ⟨⟨g * (z' : G) * g⁻¹, hgz⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro k
  apply Subtype.ext
  have hk : g⁻¹ * (k : G) * g ∈ K := by
    have := (inferInstance : K.Normal).conj_mem _ k.2 g⁻¹
    simpa using this
  have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz' ⟨g⁻¹ * (k : G) * g, hk⟩)
  show (k : G) * (g * (z' : G) * g⁻¹) = g * (z' : G) * g⁻¹ * (k : G)
  have h2 : g⁻¹ * (k : G) * g * (z' : G) = (z' : G) * (g⁻¹ * (k : G) * g) := h1
  calc
    (k : G) * (g * (z' : G) * g⁻¹) = g * (g⁻¹ * (k : G) * g * (z' : G)) * g⁻¹ := by group
    _ = g * ((z' : G) * (g⁻¹ * (k : G) * g)) * g⁻¹ := by rw [h2]
    _ = g * (z' : G) * g⁻¹ * (k : G) := by group

private noncomputable def quotientImageEquiv {E : Type u} [Group E]
    (A T : Subgroup E) [A.Normal] :
    T ⧸ A.subgroupOf T ≃* T.map (QuotientGroup.mk' A) := by
  have hk : ((QuotientGroup.mk' A).subgroupMap T).ker = A.subgroupOf T := by
    ext t
    change (QuotientGroup.mk' A).subgroupMap T t = 1 ↔ (t : E) ∈ A
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  exact QuotientGroup.liftEquiv (A.subgroupOf T)
    ((QuotientGroup.mk' A).subgroupMap_surjective T) hk.symm

private theorem bijective_pow_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) {n : ℕ} (h : Function.Bijective (fun a : A => a ^ n)) :
    Function.Bijective (fun b : B => b ^ n) := by
  constructor
  · intro x y hxy
    apply e.symm.injective
    apply h.1
    apply e.injective
    simpa using hxy
  · intro y
    obtain ⟨a, ha⟩ := h.2 (e.symm y)
    refine ⟨e a, ?_⟩
    change (e a) ^ n = y
    have ha' : a ^ n = e.symm y := by simpa using ha
    rw [← map_pow e a n, ha', e.apply_symm_apply]

end GenericAux

section NilpotentInduction

theorem exists_section_of_nilpotencyClass_le (n : ℕ) :
    ∀ (E F : Type*) [Group E] [Group F] [Finite F]
      (π : E →* F) (_hπ : Function.Surjective π)
      (_hnil : Group.IsNilpotent π.ker)
      (_hclass : Group.nilpotencyClass π.ker ≤ n)
      (_hdiv : Function.Bijective (fun k : π.ker => k ^ Nat.card F)),
      ∃ s : F →* E, π.comp s = MonoidHom.id F := by
  induction n with
  | zero =>
      intro E F _ _ _ π hπ hnil hclass hdiv
      have hsub : Subsingleton π.ker :=
        (Group.nilpotencyClass_zero_iff_subsingleton).mp (Nat.le_zero.mp hclass)
      have hinj : Function.Injective π := by
        intro x y hxy
        have hmem : x * y⁻¹ ∈ π.ker := by
          rw [MonoidHom.mem_ker]
          rw [map_mul, map_inv, hxy, mul_inv_cancel]
        have h1 : x * y⁻¹ = 1 := by
          have hsub1 : (⟨x * y⁻¹, hmem⟩ : π.ker) = 1 := Subsingleton.elim _ _
          simpa using congrArg Subtype.val hsub1
        exact (mul_inv_eq_one).mp h1
      let e : E ≃* F := MulEquiv.ofBijective π ⟨hinj, hπ⟩
      refine ⟨e.symm.toMonoidHom, ?_⟩
      ext x
      exact e.apply_symm_apply x
  | succ n ih =>
      intro E F _ _ _ π hπ hnil hclass hdiv
      let N : Subgroup E := π.ker
      let nNil : Group.IsNilpotent N := hnil
      let ZN : Subgroup N := Subgroup.center N
      let Z : Subgroup E := ZN.map N.subtype
      have hZnormal : Z.Normal := center_normal_of_normal (K := N)
      let q : E →* E ⧸ Z := QuotientGroup.mk' Z
      have hZ_le_ker : Z ≤ π.ker := by
        intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨n, hn, rfl⟩
        exact n.2
      let π' : E ⧸ Z →* F := QuotientGroup.lift Z π hZ_le_ker
      have hπ' : Function.Surjective π' := by
        intro f
        obtain ⟨e, he⟩ := hπ f
        exact ⟨q e, by
          change π e = f
          exact he⟩
      have hNmap : π'.ker = N.map q := by
        change (QuotientGroup.lift Z π hZ_le_ker).ker = N.map q
        rw [QuotientGroup.ker_lift]
      let N' : Subgroup (E ⧸ Z) := π'.ker
      have hZsub : Z.subgroupOf N = ZN := by
        ext n
        change ((n : N) : E) ∈ Z ↔ n ∈ ZN
        dsimp only [Z]
        rw [Subgroup.mem_map]
        constructor
        · rintro ⟨z, hz, hzn⟩
          exact (Subtype.ext hzn.symm) ▸ hz
        · intro hn
          exact ⟨n, hn, rfl⟩
      let eNZ : N ⧸ ZN ≃* N' :=
        (QuotientGroup.quotientMulEquivOfEq hZsub.symm).trans
          ((quotientImageEquiv Z N).trans (MulEquiv.subgroupCongr hNmap.symm))
      have hN'nil : Group.IsNilpotent N' := by
        have hqnil : Group.IsNilpotent (N ⧸ ZN) :=
          Group.nilpotent_quotient_of_nilpotent ZN
        exact Group.nilpotent_of_mulEquiv eNZ
      have hclassN' : Group.nilpotencyClass N' ≤ n := by
        have hle := Group.nilpotencyClass_le_of_surjective eNZ.toMonoidHom eNZ.surjective
        rw [Group.nilpotencyClass_quotient_center] at hle
        exact hle.trans (Nat.sub_le_iff_le_add.mpr hclass)
      have hdivZN : Function.Bijective (fun z : ZN => z ^ Nat.card F) := by
        constructor
        · intro x y hxy
          apply Subtype.ext
          exact hdiv.1 (congrArg Subtype.val hxy)
        · intro z
          obtain ⟨k, hk⟩ := hdiv.2 (z : N)
          have hk' : k ^ Nat.card F = (z : N) := hk
          have hkZ : k ∈ ZN :=
            mem_center_of_pow_mem_center (n := Nat.card F) hdiv (by rw [hk']; exact z.2)
          exact ⟨⟨k, hkZ⟩, Subtype.ext hk'⟩
      have hdivN' : Function.Bijective (fun z : N' => z ^ Nat.card F) := by
        have hdivNZ : Function.Bijective (fun z : N ⧸ ZN => z ^ Nat.card F) :=
          bijective_pow_quotient_center (n := Nat.card F) hdiv
        exact bijective_pow_of_mulEquiv eNZ hdivNZ
      obtain ⟨sbar, hsbar⟩ := ih (E ⧸ Z) F π' hπ' hN'nil hclassN' hdivN'
      let P : Subgroup E := (sbar.range).comap q
      have hZP : Z ≤ P := by
        intro z hz
        rw [Subgroup.mem_comap]
        have hzq : q z = 1 := by
          change QuotientGroup.mk' Z z = 1
          exact (QuotientGroup.eq_one_iff z).mpr hz
        rw [hzq]
        exact sbar.range.one_mem
      let πP : P →* F := π.comp P.subtype
      have hπP : Function.Surjective πP := by
        intro f
        obtain ⟨e, he⟩ := QuotientGroup.mk'_surjective Z (sbar f)
        have heP : e ∈ P := by
          rw [Subgroup.mem_comap]
          rw [he]
          exact ⟨f, rfl⟩
        refine ⟨⟨e, heP⟩, ?_⟩
        have hqe : q e = sbar f := he
        have hpi' : π' (q e) = f := by
          rw [hqe]
          exact DFunLike.congr_fun hsbar f
        change π e = f
        simpa [π', q] using hpi'
      have hdisj : sbar.range ⊓ N' = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨f, rfl⟩ := hy.1
        have hyN' : π' (sbar f) = 1 := hy.2
        rw [show π' (sbar f) = f from DFunLike.congr_fun hsbar f] at hyN'
        simp [hyN']
      have hkerP : πP.ker = Z.subgroupOf P := by
        ext x
        constructor
        · intro hx
          rw [Subgroup.mem_subgroupOf]
          have hxN : (x : E) ∈ N := by
            change π (x : E) = 1 at hx
            exact hx
          have hxP : (x : E) ∈ P := x.2
          have hxrange : q (x : E) ∈ sbar.range :=
            (Subgroup.mem_comap.mp (by simpa only [P] using hxP))
          have hxNpi : π (x : E) = 1 := by
            exact MonoidHom.mem_ker.mp (by simpa only [N] using hxN)
          have hxN' : q (x : E) ∈ N' := by
            change π' (q (x : E)) = 1
            simpa [π', q] using hxNpi
          have hxbot : q (x : E) = 1 := by
            have hmem : q (x : E) ∈ sbar.range ⊓ N' := ⟨hxrange, hxN'⟩
            rw [hdisj] at hmem
            exact Subgroup.mem_bot.mp hmem
          exact (QuotientGroup.eq_one_iff (x : E)).mp hxbot
        · intro hx
          have hxZ : (x : E) ∈ Z :=
            (Subgroup.mem_subgroupOf (H := Z) (K := P)).mp hx
          change π (x : E) = 1
          exact hZ_le_ker hxZ
      have hcommP : ∀ a b : πP.ker, a * b = b * a := by
        intro a b
        have haZ : (a : E) ∈ Z := by
          have ha : (a : P) ∈ Z.subgroupOf P := by
            rw [← hkerP]
            exact a.2
          exact (Subgroup.mem_subgroupOf (H := Z) (K := P)).mp ha
        have hbZ : (b : E) ∈ Z := by
          have hb : (b : P) ∈ Z.subgroupOf P := by
            rw [← hkerP]
            exact b.2
          exact (Subgroup.mem_subgroupOf (H := Z) (K := P)).mp hb
        apply Subtype.ext
        apply Subtype.ext
        change (a : E) * (b : E) = (b : E) * (a : E)
        rcases Subgroup.mem_map.mp haZ with ⟨a', ha', haeq⟩
        rcases Subgroup.mem_map.mp hbZ with ⟨b', hb', hbeq⟩
        rw [← haeq, ← hbeq]
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp ha' b')).symm
      let eP : πP.ker ≃* ZN :=
        (MulEquiv.subgroupCongr hkerP).trans
          ((Subgroup.subgroupOfEquivOfLe hZP).trans
            (Subgroup.equivMapOfInjective ZN N.subtype N.subtype_injective).symm)
      have hdivP : Function.Bijective (fun k : πP.ker => k ^ Nat.card F) :=
        bijective_pow_of_mulEquiv eP.symm hdivZN
      obtain ⟨s, hs⟩ := exists_section_of_abelian_kernel πP hπP hcommP hdivP
      refine ⟨P.subtype.comp s, ?_⟩
      ext f
      change π (s f : E) = f
      simpa [πP, MonoidHom.comp_apply] using DFunLike.congr_fun hs f

end NilpotentInduction

theorem exists_section_of_finite_nilpotent_extension
    {E F : Type*} [Group E] [Group F] [Finite F]
    (π : E →* F) (hπ : Function.Surjective π)
    [Group.IsNilpotent π.ker]
    (hdiv : Function.Bijective (fun k : π.ker => k ^ Nat.card F)) :
    ∃ s : F →* E, π.comp s = MonoidHom.id F :=
  exists_section_of_nilpotencyClass_le (Group.nilpotencyClass π.ker) E F π hπ
    (inferInstance) (le_refl _) hdiv

end CFSG.GroupTheory
