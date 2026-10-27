module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.L145Cls
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.L145Cases
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.L145Back
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12L144

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod.L145

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6.M12Facts
  CFSG.GH74.GLS.Stage1.Thm6.Sec13 CFSG.GH74.GLS.Stage1.Thm6.Sec14 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage1.Thm6.Prod DihedralGroup

@[expose] def d8NF : DihedralGroup 4 → NF
  | .r i => ![(0, 0, 0, 0), (0, 2, 1, 0), (2, 2, 0, 0), (2, 0, 1, 0)] i
  | .sr i => ![(0, 0, 1, 0), (2, 0, 0, 0), (2, 2, 1, 0), (0, 2, 0, 0)] i

theorem d8NF_mul : ∀ g h : DihedralGroup 4, d8NF (g * h) = nfMul (d8NF g) (d8NF h) := by
  decide +kernel

theorem d8NF_one : d8NF 1 = (0, 0, 0, 0) := by decide +kernel

theorem d8NF_inj : Function.Injective d8NF := by
  intro g h
  revert g h
  decide +kernel

theorem d8NF_ne_x : ∀ g : DihedralGroup 4, d8NF g ≠ xNF := by decide +kernel

theorem d8NF_comm_x : ∀ g : DihedralGroup 4, nfMul (d8NF g) xNF = nfMul xNF (d8NF g) := by
  decide +kernel

theorem comm_x_even : ∀ p : NF, nfMul p xNF = nfMul xNF p →
    ∃ g : DihedralGroup 4, ∃ l : Fin 2, p = nfMul (d8NF g) (0, 0, 0, l) := by decide +kernel

section Wrap

variable {G : Type} [Group G] [Finite G] {S T V : Subgroup G} {a b y x : G}

@[expose] def psiG (h : M12Data S a b y x) : DihedralGroup 4 →* G where
  toFun g := nu a b y x (d8NF g)
  map_one' := by rw [d8NF_one, nu_zero]
  map_mul' g g' := by rw [d8NF_mul, nu_mul h]

omit [Finite G] in
theorem psiG_apply (h : M12Data S a b y x) (g : DihedralGroup 4) :
    psiG h g = nu a b y x (d8NF g) := rfl

omit [Finite G] in
theorem psiG_inj (h : M12Data S a b y x) : Function.Injective (psiG h) := fun _ _ hg =>
  d8NF_inj (nu_injective h hg)

omit [Finite G] in
theorem nu_x (_h : M12Data S a b y x) : nu a b y x xNF = x := by simp [nu, xNF]

omit [Finite G] in
theorem psiG_mem_C (h : M12Data S a b y x) (g : DihedralGroup 4) :
    psiG h g ∈ centralizer ({x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, psiG_apply]
  have hx := nu_x h
  calc nu a b y x (d8NF g) * x = nu a b y x (d8NF g) * nu a b y x xNF := by rw [hx]
    _ = nu a b y x (nfMul (d8NF g) xNF) := nu_mul h _ _
    _ = nu a b y x (nfMul xNF (d8NF g)) := by rw [d8NF_comm_x]
    _ = nu a b y x xNF * nu a b y x (d8NF g) := (nu_mul h _ _).symm
    _ = x * nu a b y x (d8NF g) := by rw [hx]

instance centralInv_centralizer (x : G) [hx : Fact (x * x = 1 ∧ x ≠ 1)] :
    CentralInv (⟨x, mem_centralizer_self' x⟩ : ↥(centralizer ({x} : Set G))) where
  comm g := Subtype.ext ((Subgroup.mem_centralizer_singleton_iff).1 g.2)
  sq := Subtype.ext hx.out.1
  ne h := hx.out.2 (congrArg Subtype.val h)

@[expose] def psiC (h : M12Data S a b y x) : DihedralGroup 4 →* ↥(centralizer ({x} : Set G)) :=
  (psiG h).codRestrict _ (psiG_mem_C h)

omit [Finite G] in
theorem psiC_coe (h : M12Data S a b y x) (g : DihedralGroup 4) :
    ((psiC h g : ↥(centralizer ({x} : Set G))) : G) = nu a b y x (d8NF g) := rfl

omit [Finite G] in
theorem psiC_inj (h : M12Data S a b y x) : Function.Injective (psiC h) := fun _ _ hg =>
  psiG_inj h (congrArg Subtype.val hg)

omit [Finite G] in
theorem mem_T_iff (o : Out13 G x T V S a b y) {g : G} :
    g ∈ T ↔ g ∈ S ∧ g ∈ centralizer ({x} : Set G) := by
  rw [o.T_eq, Subgroup.mem_inf]

@[expose] noncomputable def sylowC (o : Out13 G x T V S a b y) :
    Sylow 2 ↥(centralizer ({x} : Set G)) :=
  have hT := o.out12.T_sylow
  IsPGroup.toSylow (P := T.subgroupOf (centralizer ({x} : Set G)))
    (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm) hT.2.2

omit [Finite G] in
theorem coe_sylowC (o : Out13 G x T V S a b y) :
    ((sylowC o : Sylow 2 ↥(centralizer ({x} : Set G))) : Subgroup ↥(centralizer ({x} : Set G))) =
      T.subgroupOf (centralizer ({x} : Set G)) := rfl

omit [Finite G] in
theorem dihData_of_out13 (o : Out13 G x T V S a b y) [Fact (x * x = 1 ∧ x ≠ 1)] :
    DihData (⟨x, mem_centralizer_self' x⟩ : ↥(centralizer ({x} : Set G))) (psiC o.data) (sylowC o) := by
  have h := o.data
  refine ⟨psiC_inj h, ?_, ?_⟩
  · rw [coe_sylowC]
    apply le_antisymm
    · intro g hg
      have hgT : (g : G) ∈ T := hg
      obtain ⟨hgS, hgC⟩ := (mem_T_iff o).1 hgT
      obtain ⟨p, hp⟩ := exists_nf h hgS
      have hcomm : (g : G) * x = x * (g : G) := Subgroup.mem_centralizer_singleton_iff.1 hgC
      have hpx : nfMul p xNF = nfMul xNF p := by
        apply nu_injective h
        rw [← nu_mul h, ← nu_mul h, nu_x h, ← hp]
        exact hcomm
      obtain ⟨δ, l, hδ⟩ := comm_x_even p hpx
      have hg' : g = psiC h δ * (⟨x, mem_centralizer_self' x⟩ : ↥(centralizer ({x} : Set G))) ^ l.val := by
        apply Subtype.ext
        rw [hp, hδ, ← nu_mul h]
        simp [psiC_coe, nu]
      rw [hg']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨δ, rfl⟩)
        (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact (mem_T_iff o).2 ⟨x_mem h, mem_centralizer_self' x⟩
      · rintro _ ⟨δ, rfl⟩
        exact (mem_T_iff o).2 ⟨nu_mem h _, psiG_mem_C h δ⟩
  · rw [eq_bot_iff]
    rintro g ⟨hgx, δ, rfl⟩
    rcases CentralInv.mem_zpowers hgx with h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · exfalso
      have h2 : nu a b y x (d8NF δ) = x := congrArg Subtype.val h1
      have h3 : nu a b y x (d8NF δ) = nu a b y x xNF := by rw [nu_x h]; exact h2
      exact d8NF_ne_x δ (nu_injective h h3)

theorem d8NF_r2 : d8NF (r 2) = (2, 2, 0, 0) := rfl
theorem d8NF_sr0 : d8NF (sr 0) = (0, 0, 1, 0) := rfl
theorem d8NF_sr1 : d8NF (sr 1) = (2, 0, 0, 0) := rfl
theorem d8NF_sr3 : d8NF (sr 3) = (0, 2, 0, 0) := rfl

omit [Finite G] in
theorem nu_zNF (_h : M12Data S a b y x) : nu a b y x (2, 2, 0, 0) = a ^ 2 * b ^ 2 := by
  simp [nu]

omit [Finite G] in
theorem exists_conj_psi (o : Out13 G x T V S a b y) {p : NF} (hp : pU p) (hp1 : p ≠ (0, 0, 0, 0)) :
    ∃ c : ↥(centralizer ({x} : Set G)),
      (c : G) * (a ^ 2 * b ^ 2) * (c : G)⁻¹ = nu a b y x p := by
  have h := o.data
  obtain ⟨f, hf3, hf, hfx, v, hv, hfv⟩ := o.f3
  have hvU : v ∈ nfSub h pU closed_pU := by rw [← U_eq h, ← o.V_eq]; exact hv
  have hu : nu a b y x p ∈ nfSub h pU closed_pU := (nu_mem_nfSub h closed_pU p).2 hp
  have hu1 : nu a b y x p ≠ 1 := fun e => hp1 (nu_injective h (e.trans nu_zero.symm))
  obtain ⟨n, -, hnx, hn⟩ := exists_conj_U_to_z_comm o hf3 hf hfx hvU hfv hu hu1
  have hnx' : n⁻¹ * x = x * n⁻¹ := by
    calc n⁻¹ * x = n⁻¹ * (x * n) * n⁻¹ := by group
      _ = n⁻¹ * (n * x) * n⁻¹ := by rw [← hnx]
      _ = x * n⁻¹ := by group
  refine ⟨⟨n⁻¹, Subgroup.mem_centralizer_singleton_iff.2 hnx'⟩, ?_⟩
  show n⁻¹ * (a ^ 2 * b ^ 2) * n⁻¹⁻¹ = _
  rw [← hn]; group

theorem cfg_of_out13 (o : Out13 G x T V S a b y) [Fact (x * x = 1 ∧ x ≠ 1)] :
    Cfg (⟨x, mem_centralizer_self' x⟩ : ↥(centralizer ({x} : Set G))) (psiC o.data) (sylowC o)
      (fun u => IsConj x (u : G)) := by
  have h := o.data
  have hz : ((psiC h (r 2) : ↥(centralizer ({x} : Set G))) : G) = a ^ 2 * b ^ 2 := by
    rw [psiC_coe, d8NF_r2, nu_zNF h]
  have hy : ((psiC h (sr 0) : ↥(centralizer ({x} : Set G))) : G) = y := by
    rw [psiC_coe, d8NF_sr0]; simp [nu]
  refine ⟨dihData_of_out13 o, ?_, ?_, o.out12.nonsolv, IsConj.refl x, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := exists_conj_psi o (p := (2, 0, 0, 0)) (by decide) (by decide)
    refine ⟨c, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hz, hc, psiC_coe, d8NF_sr1]
  · obtain ⟨c, hc⟩ := exists_conj_psi o (p := (0, 2, 0, 0)) (by decide) (by decide)
    refine ⟨c, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hz, hc, psiC_coe, d8NF_sr3]
  · obtain ⟨g, hg⟩ := o.y_conj
    show IsConj x ((psiC h (sr 0) : ↥(centralizer ({x} : Set G))) : G)
    rw [hy]
    exact isConj_iff.2 ⟨g, hg.symm⟩
  · obtain ⟨g, hg⟩ := x_conj_yx o
    show IsConj x ((psiC h (sr 0) * ⟨x, mem_centralizer_self' x⟩ : ↥(centralizer ({x} : Set G))) : G)
    rw [Subgroup.coe_mul, hy]
    exact isConj_iff.2 ⟨g, hg⟩
  · show IsConj x ((psiC h (r 2) * ⟨x, mem_centralizer_self' x⟩ : ↥(centralizer ({x} : Set G))) : G)
    rw [Subgroup.coe_mul, psiC_coe, d8NF_r2]
    obtain ⟨q, hq⟩ := pXU_conj (2, 2, 0, 1) (by decide)
    refine isConj_iff.2 ⟨nu a b y x q, ?_⟩
    have hxx : nu a b y x xNF = x := nu_x h
    have key : nu a b y x (2, 2, 0, 0) * x = nu a b y x (2, 2, 0, 1) := by
      have h1 := nu_mul h (2, 2, 0, 0) xNF
      rw [hxx] at h1
      rw [h1]
      have : nfMul (2, 2, 0, 0) xNF = (2, 2, 0, 1) := by decide
      rw [this]
    show nu a b y x q * x * (nu a b y x q)⁻¹ = nu a b y x (2, 2, 0, 0) * x
    rw [key]
    calc nu a b y x q * x * (nu a b y x q)⁻¹
        = nu a b y x q * nu a b y x xNF * nu a b y x (nfInv q) := by rw [hxx, nu_inv h]
      _ = nu a b y x (nfMul (nfMul q xNF) (nfInv q)) := by rw [← nu_mul h, ← nu_mul h]
      _ = nu a b y x (2, 2, 0, 1) := by rw [hq]
  · rintro hc
    obtain ⟨g, hg⟩ := isConj_iff.1 hc
    rw [hz] at hg
    exact x_not_conj_z o g⁻¹ (by rw [← hg]; group)
  · intro g u hu
    show IsConj x ((g : G) * (u : G) * (g : G)⁻¹)
    exact hu.trans (isConj_iff.2 ⟨(g : G), rfl⟩)


end Wrap

section CfgMap

variable {X X' : Type} [Group X] [Finite X] [Group X'] [Finite X'] {x : X} [CentralInv x]
  {ψ : DihedralGroup 4 →* X} {T : Sylow 2 X} {P : X → Prop}

theorem Cfg.map (hc : Cfg x ψ T P) (θ : X ≃* X') {x' : X'} [CentralInv x'] (hx' : θ x = x')
    {P' : X' → Prop} (hP : ∀ c, P c ↔ P' (θ c)) :
    Cfg x' (θ.toMonoidHom.comp ψ)
      (T.mapSurjective (f := θ.toMonoidHom) (by rw [MulEquiv.coe_toMonoidHom]; exact θ.surjective)) P' := by
  have hD := hc.dih
  have hmapc : ∀ (g c : X), θ (g * c * g⁻¹) = θ g * θ c * (θ g)⁻¹ := fun g c => by
    simp only [map_mul, map_inv]
  have hz : (zpowers x).map θ.toMonoidHom = zpowers x' := by
    rw [MonoidHom.map_zpowers]; exact congrArg _ hx'
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact θ.injective.comp hD.inj
  · rw [Sylow.coe_mapSurjective, hD.sup, Subgroup.map_sup, hz, MonoidHom.range_comp]
  · rw [MonoidHom.range_comp, ← hz, ← Subgroup.map_inf _ _ _ θ.injective, hD.disj, Subgroup.map_bot]
  · obtain ⟨c, hc'⟩ := hc.fa
    have h1 := congrArg θ hc'
    rw [hmapc] at h1
    exact ⟨θ c, h1⟩
  · obtain ⟨c, hc'⟩ := hc.fb
    have h1 := congrArg θ hc'
    rw [hmapc] at h1
    exact ⟨θ c, h1⟩
  · intro hs
    exact hc.nonsolv (by
      have := hs
      exact Group.isSolvable_of_isSolvable_injective (f := θ.toMonoidHom) θ.injective)
  · rw [← hx']; exact (hP x).1 hc.Px
  · exact (hP _).1 hc.Py
  · have := (hP _).1 hc.Pyx
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, hx'] using this
  · have := (hP _).1 hc.Pzx
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, hx'] using this
  · intro hpz
    exact hc.nPz ((hP _).2 hpz)
  · intro g' u' hu'
    have h1 : P (θ.symm u') := (hP _).2 (by simpa using hu')
    have h2 := hc.Pconj (θ.symm g') (θ.symm u') h1
    have := (hP _).1 h2
    simpa only [hmapc, MulEquiv.apply_symm_apply] using this

end CfgMap


section Conj

variable {G : Type} [Group G] [Finite G]

@[expose] def conjCentralizer (g x : G) :
    ↥(centralizer ({x} : Set G)) ≃* ↥(centralizer ({g * x * g⁻¹} : Set G)) where
  toFun c := ⟨g * c * g⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 c.2
    calc g * (c : G) * g⁻¹ * (g * x * g⁻¹) = g * ((c : G) * x) * g⁻¹ := by group
      _ = g * (x * (c : G)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * (g * (c : G) * g⁻¹) := by group⟩
  invFun c := ⟨g⁻¹ * c * g, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 c.2
    have h2 : (c : G) * (g * x * g⁻¹) = g * x * g⁻¹ * (c : G) := this
    calc g⁻¹ * (c : G) * g * x = g⁻¹ * ((c : G) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * (c : G)) * g := by rw [h2]
      _ = x * (g⁻¹ * (c : G) * g) := by group⟩
  left_inv c := Subtype.ext (by simp [mul_assoc])
  right_inv c := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

omit [Finite G] in
theorem isConj_conj_iff (g x c : G) : IsConj x c ↔ IsConj (g * x * g⁻¹) (g * c * g⁻¹) := by
  constructor
  · rintro h
    obtain ⟨h', hh⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨g * h' * g⁻¹, ?_⟩
    rw [← hh]; group
  · rintro h
    obtain ⟨h', hh⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨g⁻¹ * h' * g, ?_⟩
    have : g⁻¹ * h' * g * x * (g⁻¹ * h' * g)⁻¹ = g⁻¹ * (h' * (g * x * g⁻¹) * h'⁻¹) * g := by group
    rw [this, hh]; group

end Conj


section Final

variable {G : Type} [Group G] [Finite G] {S T V : Subgroup G} {a b y x : G}

theorem m12NonCentral_conj (hGW : GorensteinWalter.gorensteinWalterStatement.{0})
    (o : Out13 G x T V S a b y) (g : G) :
    M12NonCentral (g * x * g⁻¹) := by
  have hF : Fact (x * x = 1 ∧ x ≠ 1) := ⟨⟨o.out12.x_sq, o.out12.x_ne⟩⟩
  have hu2 : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [o.out12.x_sq]; group
  have hu1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply o.out12.x_ne
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hFu : Fact (g * x * g⁻¹ * (g * x * g⁻¹) = 1 ∧ g * x * g⁻¹ ≠ 1) := ⟨⟨hu2, hu1⟩⟩
  let θ := conjCentralizer g x
  have hθx : θ ⟨x, mem_centralizer_self' x⟩ = ⟨g * x * g⁻¹, mem_centralizer_self' _⟩ :=
    Subtype.ext rfl
  have hcfg := Cfg.map (cfg_of_out13 o) θ hθx (P' := fun u' => IsConj (g * x * g⁻¹) (u' : G))
    (fun c => isConj_conj_iff g x c)
  exact m12NonCentral_of_NC _ (main_abstract hGW hcfg)

end Final

end CFSG.GH74.GLS.Stage1.Thm6.Prod.L145
