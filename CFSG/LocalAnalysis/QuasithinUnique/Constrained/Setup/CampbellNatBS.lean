module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatNI

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Open CFSG.Quasithin CFSG.Quasithin.B6 CFSG.Quasithin.BlueprintB2
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Offender
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

variable {H : Type*} [Group H] [Finite H] {k : Type*} [Field k] [Finite k] [CharP k 2]

namespace IsNatQuotSetting

variable {R M V : Subgroup H} {ρ : H →* Gamma k} {φ : V →* Multiplicative (Fin 2 → k)}

omit [CharP k 2] in
theorem exists_L_moves_line (h : IsNatQuotSetting R M V ρ φ)
    (hHLR : oddOrderSubgroup (⊤ : Subgroup H) ⊔ R = ⊤) {ℓ : ℙ k (Fin 2 → k)}
    (hJρ : (elemThompsonIn 2 R).map ρ = rootGamma ℓ) :
    ∃ g ∈ oddOrderSubgroup (⊤ : Subgroup H), ∃ B : Matrix.SpecialLinearGroup (Fin 2) k,
      ((ρ g : Gamma k) : Equiv.Perm (Fin 2 → k)) = slPerm k B ∧ B • ℓ ≠ ℓ := by
  classical
  have hLn := h.normal_L
  by_contra hcon
  push Not at hcon
  set ρp : H →* Equiv.Perm (Fin 2 → k) := (Gamma k).subtype.comp ρ with hρp
  have hU : (elemThompsonIn 2 R).map ρp = rootPerm ℓ := by
    rw [← map_subtype_rootGamma, ← hJρ, Subgroup.map_map]
  have hRinv : ∀ r ∈ R, ∀ x : Equiv.Perm (Fin 2 → k),
      (ρp r)⁻¹ * x * ρp r ∈ rootPerm ℓ ↔ x ∈ rootPerm ℓ := by
    intro r hr x
    have hn : (elemThompsonIn 2 R).map (MulAut.conj r).toMonoidHom = elemThompsonIn 2 R :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_map_elemThompson R hr)
    have hcomp : (MulAut.conj (ρp r)).toMonoidHom.comp ρp = ρp.comp (MulAut.conj r).toMonoidHom := by
      refine MonoidHom.ext fun y => ?_
      simp [MulAut.conj_apply]
    have hRn : (rootPerm ℓ).map (MulAut.conj (ρp r)).toMonoidHom = rootPerm ℓ := by
      rw [← hU, Subgroup.map_map, hcomp, ← Subgroup.map_map, hn]
    rw [← mem_map_conj, hRn]
  have hall : ∀ B' : Matrix.SpecialLinearGroup (Fin 2) k, B' • ℓ = ℓ := by
    intro B'
    obtain ⟨h', hh'⟩ := h.sl_le B'
    have hh'mem : h' ∈ oddOrderSubgroup (⊤ : Subgroup H) ⊔ R := by
      rw [hHLR]; exact Subgroup.mem_top h'
    obtain ⟨l, hl, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hh'mem
    obtain ⟨Bl, hBl⟩ := mem_slGamma_iff.mp (h.map_L_le ⟨l, hl, rfl⟩)
    have hBlℓ : Bl • ℓ = ℓ := hcon l hl Bl hBl
    apply rootPerm_injective
    ext x
    rw [mem_rootPerm_smul_iff]
    have hsl : slPerm k B' = ρp l * ρp r := by
      rw [← hh']
      simp [hρp]
    have e1 : (slPerm k B')⁻¹ * x * slPerm k B' =
        (ρp r)⁻¹ * ((ρp l)⁻¹ * x * ρp l) * ρp r := by
      rw [hsl]; group
    rw [e1, hRinv r hr]
    have hρl : ρp l = slPerm k Bl := hBl
    rw [hρl, ← mem_rootPerm_smul_iff, hBlℓ]
  obtain ⟨m, hm⟩ := exists_ne_point ℓ
  obtain ⟨B', hB'⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) k) ℓ m
  exact hm (hB'.symm.trans (hall B'))

omit [Finite H] [Finite k] [CharP k 2] in
theorem map_cj_eq_rootGamma {ℓ : ℙ k (Fin 2 → k)}
    (hJρ : (elemThompsonIn 2 R).map ρ = rootGamma ℓ) {g : H}
    {B : Matrix.SpecialLinearGroup (Fin 2) k}
    (hgB : ((ρ g : Gamma k) : Equiv.Perm (Fin 2 → k)) = slPerm k B) :
    (cj (elemThompsonIn 2 R) g).map ρ = rootGamma (B⁻¹ • ℓ) := by
  classical
  set ρp : H →* Equiv.Perm (Fin 2 → k) := (Gamma k).subtype.comp ρ with hρp
  have hU : (elemThompsonIn 2 R).map ρp = rootPerm ℓ := by
    rw [← map_subtype_rootGamma, ← hJρ, Subgroup.map_map]
  have hρg : ρp g = slPerm k B := hgB
  apply Subgroup.map_injective (Gamma k).subtype_injective
  rw [map_subtype_rootGamma, Subgroup.map_map]
  show (cj (elemThompsonIn 2 R) g).map ρp = rootPerm (B⁻¹ • ℓ)
  ext x
  rw [mem_rootPerm_smul_iff, ← hU]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyJ : g * y * g⁻¹ ∈ elemThompsonIn 2 R := mem_cj.mp hy
    refine ⟨g * y * g⁻¹, hyJ, ?_⟩
    have : (slPerm k B⁻¹)⁻¹ * ρp y * slPerm k B⁻¹ = ρp g * ρp y * (ρp g)⁻¹ := by
      rw [hρg, map_inv, inv_inv]
    rw [this]
    simp [map_mul, map_inv]
  · rintro ⟨j, hj, hjx⟩
    refine ⟨g⁻¹ * j * g, mem_cj.mpr (by simpa [mul_assoc] using hj), ?_⟩
    have h1 : ρp j = (slPerm k B⁻¹)⁻¹ * x * slPerm k B⁻¹ := hjx
    have e1 : ρp (g⁻¹ * j * g) = (ρp g)⁻¹ * ρp j * ρp g := by simp [map_mul, map_inv]
    rw [e1, h1, hρg]
    simp only [map_inv]
    group

omit [Finite H] [Finite k] [CharP k 2] in
theorem L_le_sup_ker (h : IsNatQuotSetting R M V ρ φ) {ℓ : ℙ k (Fin 2 → k)}
    (hJρ : (elemThompsonIn 2 R).map ρ = rootGamma ℓ) {g : H}
    {B : Matrix.SpecialLinearGroup (Fin 2) k}
    (hgB : ((ρ g : Gamma k) : Equiv.Perm (Fin 2 → k)) = slPerm k B) (hBℓ : B • ℓ ≠ ℓ) :
    oddOrderSubgroup (⊤ : Subgroup H) ≤
      (elemThompsonIn 2 R ⊔ cj (elemThompsonIn 2 R) g) ⊔ ρ.ker := by
  classical
  set ρp : H →* Equiv.Perm (Fin 2 → k) := (Gamma k).subtype.comp ρ with hρp
  set ℓ' : ℙ k (Fin 2 → k) := B⁻¹ • ℓ with hℓ'
  have hℓ'ne : ℓ' ≠ ℓ := by
    intro heq
    apply hBℓ
    rw [hℓ', inv_smul_eq_iff] at heq
    exact heq.symm
  have hU : (elemThompsonIn 2 R).map ρp = rootPerm ℓ := by
    rw [← map_subtype_rootGamma, ← hJρ, Subgroup.map_map]
  have hU' : (cj (elemThompsonIn 2 R) g).map ρp = rootPerm ℓ' := by
    rw [← map_subtype_rootGamma, ← map_cj_eq_rootGamma hJρ hgB, Subgroup.map_map]
  intro x hx
  have hρx : ρ x ∈ slGamma k := h.map_L_le ⟨x, hx, rfl⟩
  obtain ⟨B'', hB''⟩ := mem_slGamma_iff.mp hρx
  have hsup : (elemThompsonIn 2 R ⊔ cj (elemThompsonIn 2 R) g).map ρp =
      rootPerm ℓ ⊔ rootPerm ℓ' := by
    rw [Subgroup.map_sup, hU, hU']
  have hB''mem : slPerm k B'' ∈ rootPerm ℓ ⊔ rootPerm ℓ' := by
    have hmem : B'' ∈ rootGrp ℓ ⊔ rootGrp ℓ' := by
      rw [rootGrp_sup_rootGrp hℓ'ne.symm]; trivial
    have : slPerm k B'' ∈ (rootGrp ℓ ⊔ rootGrp ℓ').map (slPerm k) := ⟨B'', hmem, rfl⟩
    rwa [Subgroup.map_sup] at this
  rw [← hsup] at hB''mem
  obtain ⟨y, hy, hyx⟩ := hB''mem
  have hyx' : ρp y = ρp x := hyx.trans hB''.symm
  have hker : y⁻¹ * x ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have : ρp (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hyx', inv_mul_cancel]
    simpa [hρp] using this
  have hxy : x = y * (y⁻¹ * x) := by group
  rw [hxy]
  exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hker)

omit [Finite H] [Finite k] [CharP k 2] in
theorem conjNormal_eq_one_of_mem_centralizer [Finite H] {V : Subgroup H} [V.Normal] {c : H}
    (hc : c ∈ Subgroup.centralizer (V : Set H)) : MulAut.conjNormal (H := V) c = 1 := by
  refine MulEquiv.ext fun v => Subtype.ext ?_
  have h1 : (v : H) * c = c * (v : H) := Subgroup.mem_centralizer_iff.mp hc (v : H) v.2
  show c * (v : H) * c⁻¹ = (v : H)
  rw [← h1]; group

omit [Finite H] [Finite k] in
theorem V_le_commutator_sup (h : IsNatQuotSetting R M V ρ φ) {g : H}
    (hgL : g ∈ oddOrderSubgroup (⊤ : Subgroup H))
    (hg1 : ((ρ g : Gamma k) : Equiv.Perm (Fin 2 → k)) ≠ 1) :
    V ≤ ⁅V, oddOrderSubgroup (⊤ : Subgroup H)⁆ ⊔
      (V ⊓ Subgroup.centralizer ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H)) := by
  classical
  have hVn : V.Normal := h.normal_V
  have hLn : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := h.normal_L
  set L : Subgroup H := oddOrderSubgroup (⊤ : Subgroup H) with hLdef
  have hcn : (⁅V, L⁆ : Subgroup H).Normal := inferInstance
  set Vc : Subgroup V := (⁅V, L⁆ : Subgroup H).subgroupOf V with hVc
  set W' : Subgroup (Multiplicative (Fin 2 → k)) := Vc.map φ with hW'
  have hinv : ∀ h' : H, ∀ w ∈ W', Multiplicative.ofAdd
      (((ρ h' : Gamma k) : Equiv.Perm (Fin 2 → k)) (Multiplicative.toAdd w)) ∈ W' := by
    rintro h' w ⟨x, hx, rfl⟩
    have hx' : h' * (x : H) * h'⁻¹ ∈ V := hVn.conj_mem x x.2 h'
    refine ⟨⟨h' * (x : H) * h'⁻¹, hx'⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (hcn.conj_mem _ (Subgroup.mem_subgroupOf.mp hx) h')
    · apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      exact h.φ_equiv h' x ⟨_, hx'⟩ rfl
  have hne : ∃ w ∈ W', w ≠ 1 := by
    obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Fin 2 → k,
        ((ρ g : Gamma k) : Equiv.Perm (Fin 2 → k)) w₀ ≠ w₀ := by
      by_contra hall
      push Not at hall
      exact hg1 (Equiv.ext hall)
    obtain ⟨u, hu⟩ := h.φ_surj (Multiplicative.ofAdd w₀)
    have hu' : g * ((u⁻¹ : V) : H) * g⁻¹ ∈ V := hVn.conj_mem _ (u⁻¹).2 g
    let u₁ : V := ⟨g * ((u⁻¹ : V) : H) * g⁻¹, hu'⟩
    have hφu₁ : Multiplicative.toAdd (φ u₁) =
        ((ρ g : Gamma k) : Equiv.Perm (Fin 2 → k)) (Multiplicative.toAdd (φ u⁻¹)) :=
      h.φ_equiv g u⁻¹ u₁ rfl
    have hφuinv : Multiplicative.toAdd (φ u⁻¹) = w₀ := by
      rw [map_inv, hu, toAdd_inv, toAdd_ofAdd]
      exact neg_eq_self_of_char_two_module k w₀
    let c : V := u * u₁
    have hcval : (c : H) = ⁅(u : H), g⁆ := by
      show (u : H) * (g * ((u⁻¹ : V) : H) * g⁻¹) = _
      simp only [commutatorElement_def, Subgroup.coe_inv]
      group
    have hcmem : c ∈ Vc := by
      rw [hVc, Subgroup.mem_subgroupOf, hcval]
      exact Subgroup.commutator_mem_commutator u.2 hgL
    refine ⟨φ c, ⟨c, hcmem, rfl⟩, ?_⟩
    intro hc1
    have hsum : Multiplicative.toAdd (φ c) =
        w₀ + ((ρ g : Gamma k) : Equiv.Perm (Fin 2 → k)) w₀ := by
      rw [map_mul, toAdd_mul, hφu₁, hφuinv, hu, toAdd_ofAdd]
    rw [hc1, toAdd_one] at hsum
    apply hw₀
    have h2 := eq_neg_of_add_eq_zero_right hsum.symm
    rw [h2]
    exact neg_eq_self_of_char_two_module k w₀
  have htop : W' = ⊤ := by
    obtain ⟨w₁, hw₁, hw₁1⟩ := hne
    rw [eq_top_iff]
    intro w _
    by_cases hw0 : Multiplicative.toAdd w = 0
    · have : w = 1 := by
        apply Multiplicative.toAdd.injective
        simpa using hw0
      rw [this]
      exact one_mem _
    · have h1 : Multiplicative.toAdd w₁ ≠ 0 := by
        intro h0
        apply hw₁1
        apply Multiplicative.toAdd.injective
        simpa using h0
      obtain ⟨B₁, hB₁⟩ := exists_smul_e0 h1
      obtain ⟨B₂, hB₂⟩ := exists_smul_e0 hw0
      obtain ⟨h', hh'⟩ := h.sl_le (B₂ * B₁⁻¹)
      have hmem := hinv h' w₁ hw₁
      have hval : ((ρ h' : Gamma k) : Equiv.Perm (Fin 2 → k)) (Multiplicative.toAdd w₁) =
          Multiplicative.toAdd w := by
        rw [hh', slPerm_apply, mul_smul]
        have : B₁⁻¹ • Multiplicative.toAdd w₁ = Pi.single 0 1 := by
          rw [← hB₁]; exact inv_smul_smul B₁ _
        rw [this, hB₂]
      rw [hval] at hmem
      simpa using hmem
  intro v hv
  have hφv : φ ⟨v, hv⟩ ∈ W' := htop ▸ Subgroup.mem_top _
  obtain ⟨x, hx, hxv⟩ := hφv
  have hxk : (⟨v, hv⟩ : V) * x⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxv, mul_inv_cancel]
  have hmem : v * (x : H)⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set H) :=
    ⟨(⟨v, hv⟩ * x⁻¹ : V).2, Subgroup.mem_subgroupOf.mp (h.φ_ker ▸ hxk)⟩
  have hvx : v = (v * (x : H)⁻¹) * x := by group
  rw [hvx]
  exact mul_mem (Subgroup.mem_sup_right hmem) (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))

omit [Finite H] [Finite k] [CharP k 2] in
theorem V_le_iSup_cj (h : IsNatQuotSetting R M V ρ φ) {J : Subgroup H} {ℓ : ℙ k (Fin 2 → k)}
    (hline : ∀ w : Fin 2 → k, w ∈ ℓ.submodule ↔ ∃ v : V,
      (v : H) ∈ Subgroup.centralizer (J : Set H) ∧ Multiplicative.toAdd (φ v) = w)
    (hker : ∀ v : V, φ v = 1 → (v : H) ∈ Subgroup.centralizer (J : Set H)) {g : H}
    (hgL : g ∈ oddOrderSubgroup (⊤ : Subgroup H)) {B : Matrix.SpecialLinearGroup (Fin 2) k}
    (hgB : ((ρ g : Gamma k) : Equiv.Perm (Fin 2 → k)) = slPerm k B) (hBℓ : B • ℓ ≠ ℓ) :
    V ≤ ⨆ l ∈ oddOrderSubgroup (⊤ : Subgroup H),
      cj (V ⊓ Subgroup.centralizer (J : Set H)) l := by
  classical
  have hVn : V.Normal := h.normal_V
  set L : Subgroup H := oddOrderSubgroup (⊤ : Subgroup H) with hLdef
  set D : Subgroup H := V ⊓ Subgroup.centralizer (J : Set H) with hD
  set T : Subgroup H := ⨆ l ∈ L, cj D l with hT
  have hDT : D ≤ T := by
    refine le_iSup₂_of_le (f := fun (l : H) (_ : l ∈ L) => cj D l) 1 (one_mem L) ?_
    rw [cj_one]
  have hcjT : cj D g ≤ T := le_iSup₂ (f := fun (l : H) (_ : l ∈ L) => cj D l) g hgL
  have hℓ' : B⁻¹ • ℓ ≠ ℓ := by
    intro heq
    apply hBℓ
    rw [inv_smul_eq_iff] at heq
    exact heq.symm
  have hsup := submodule_sup_eq_top hℓ'
  intro v hv
  have hw : Multiplicative.toAdd (φ ⟨v, hv⟩) ∈ (B⁻¹ • ℓ).submodule ⊔ ℓ.submodule := by
    rw [hsup]; trivial
  obtain ⟨z, hz, y, hy, hzy⟩ := Submodule.mem_sup.mp hw
  obtain ⟨d, hdC, hdφ⟩ := (hline y).mp hy
  have hz' : B • z ∈ ℓ.submodule := by
    rw [PSL.smul_submodule, Submodule.mem_smul_pointwise_iff_exists] at hz
    obtain ⟨b, hb, hbz⟩ := hz
    rw [← hbz, smul_inv_smul]
    exact hb
  obtain ⟨d', hd'C, hd'φ⟩ := (hline _).mp hz'
  have hv₂V : g⁻¹ * (d' : H) * g ∈ V := by
    simpa using hVn.conj_mem (d' : H) d'.2 g⁻¹
  let v₂ : V := ⟨g⁻¹ * (d' : H) * g, hv₂V⟩
  have hφv₂ : Multiplicative.toAdd (φ v₂) = z := by
    have e0 := h.φ_equiv g⁻¹ d' v₂ (by simp [v₂])
    have e1 : ((ρ g⁻¹ : Gamma k) : Equiv.Perm (Fin 2 → k)) = slPerm k B⁻¹ := by
      rw [map_inv, Subgroup.coe_inv, hgB, map_inv]
    rw [e0, e1, hd'φ, slPerm_apply, inv_smul_smul]
  have hv₂ : (v₂ : H) ∈ cj D g := by
    rw [mem_cj]
    have : g * (g⁻¹ * (d' : H) * g) * g⁻¹ = (d' : H) := by group
    show g * (g⁻¹ * (d' : H) * g) * g⁻¹ ∈ D
    rw [this]
    exact ⟨d'.2, hd'C⟩
  let t : V := d * v₂
  have htT : (t : H) ∈ T := mul_mem (hDT ⟨d.2, hdC⟩) (hcjT hv₂)
  have hφt : Multiplicative.toAdd (φ t) = Multiplicative.toAdd (φ ⟨v, hv⟩) := by
    show Multiplicative.toAdd (φ (d * v₂)) = _
    rw [map_mul, toAdd_mul, hdφ, hφv₂, add_comm, hzy]
  have hker' : (⟨v, hv⟩ : V) * t⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← Multiplicative.toAdd.injective.eq_iff.mp hφt.symm]
    exact mul_inv_cancel _
  have hDmem : v * (t : H)⁻¹ ∈ D := ⟨(⟨v, hv⟩ * t⁻¹ : V).2, hker _ hker'⟩
  have hvt : v = (v * (t : H)⁻¹) * t := by group
  rw [hvt]
  exact mul_mem (hDT hDmem) htT

theorem Baumann_Sylow (h : IsNatQuotSetting R M V ρ φ) (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    ∃ ℓ : ℙ k (Fin 2 → k),
      IsSylowIn 2 (elemBaumannIn 2 R) (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ∧
      (CFSG.pCore 2 (oddOrderSubgroup (⊤ : Subgroup H))).map
          (oddOrderSubgroup (⊤ : Subgroup H)).subtype ≤ elemBaumannIn 2 R ∧
      (elemThompsonIn 2 R).map ρ = rootGamma ℓ ∧ (elemBaumannIn 2 R).map ρ = rootGamma ℓ ∧
      (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R).map ρ = slGamma k ∧
      elemCenterIn 2 R =
        (elemCenterIn 2 R ⊓ Subgroup.centralizer ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H)) ⊔
          (V ⊓ Subgroup.centralizer ((elemThompsonIn 2 R : Subgroup H) : Set H)) ∧
      ⁅elemThompsonIn 2 R, V ⊓ Subgroup.centralizer
        ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H)⁆ = ⊥ ∧
      (⨆ l ∈ oddOrderSubgroup (⊤ : Subgroup H), cj (elemCenterIn 2 R) l) =
        ⁅V, oddOrderSubgroup (⊤ : Subgroup H)⁆ ⊔ (elemCenterIn 2 R ⊓
          Subgroup.centralizer ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H)) := by
  classical
  have hVH := h.not_le_centralizer hJ
  have hVR : V ≤ R := h.V_le_R
  have hVn : V.Normal := h.normal_V
  have hLn : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := h.normal_L
  have hQn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  obtain ⟨hHLR, hCR, hQC, hCJ, hPL, hfr, hFJ⟩ :=
    minimal_parabolic_reduced_module_Frattini_kernel_production h.sylow h.nonnormal h.le_M h.M_lt
      h.M_max h.reduced hVH
  obtain ⟨ℓ, hJρ, hSρ, hJcent, hline, hidx, hineq⟩ := h.NI_data hJ
  obtain ⟨g, hgL, B, hgB, hBℓ⟩ := h.exists_L_moves_line hHLR hJρ
  have hLsup := h.L_le_sup_ker hJρ hgB hBℓ
  set L : Subgroup H := oddOrderSubgroup (⊤ : Subgroup H) with hLdef
  set J : Subgroup H := elemThompsonIn 2 R with hJdef
  set S : Subgroup H := elemBaumannIn 2 R with hSdef
  set E : Subgroup H := elemCenterIn 2 R with hEdef
  have hL2 : ∀ x : H ⧸ L, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x
    obtain ⟨h', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := exists_pow_mem_oddOrderSubgroup (H := (⊤ : Subgroup H)) (h := h') trivial
    exact ⟨k, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).mpr hk⟩
  have hNfr : ρ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 H)) ≤
      frattini (H ⧸ CFSG.pCore 2 H) := hfr ▸ Subgroup.map_mono h.ker_le_kerIn
  have hLIQ : L ≤ (J ⊔ cj J g) ⊔ CFSG.pCore 2 H :=
    le_sup_pCore_of_le_sup L hL2 hNfr hLsup
  have hρV : L.map (MulAut.conjNormal (H := V)) ≤ (J ⊔ cj J g).map (MulAut.conjNormal (H := V)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, q, hq, hyq⟩ := Subgroup.mem_sup_of_normal_right.mp (hLIQ hx)
    refine ⟨y, hy, ?_⟩
    rw [← hyq, map_mul, conjNormal_eq_one_of_mem_centralizer (hQC hq), mul_one]
  have hVe : IsElementaryAbelian 2 V :=
    (isElemAbelian_iff_isElementaryAbelian 2).mp h.reduced.2.2.1
  have hR2 : IsPGroup 2 R := h.sylow.2.1
  have hLclosure : L = Subgroup.closure {x : H | Nat.Coprime (orderOf x) 2} := by
    rw [hLdef, oddOrderSubgroup]
    congr 1
    ext x
    simp [Nat.coprime_two_right]
  have hPQ : L ⊓ CFSG.pCore 2 H ≤ R ⊓ Subgroup.centralizer (V : Set H) := by
    rw [hCR]; exact inf_le_right
  have hLQ : L ≤ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (V : Set H) : Subgroup H) : Set H) := by
    rw [hCR]
    intro x _
    exact mem_normalizer_of_normal _ x
  have hΦ : ((Subgroup.centralizer (V : Set H)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 L)) ≤ frattini (L ⧸ CFSG.pCore 2 L) := hFJ _ hCJ
  let X : Fin 2 → Subgroup H := ![J, cj J g]
  have hXI : (⨆ i, X i) = J ⊔ cj J g :=
    le_antisymm (iSup_le (Fin.forall_fin_two.mpr ⟨le_sup_left, le_sup_right⟩))
      (sup_le (le_iSup X 0) (le_iSup X 1))
  have hJR : J ≤ R := elemThompsonIn_le 2 R
  have hXL : ∀ i, ∃ l ∈ L, conjugate (X i) l ≤ R := by
    refine Fin.forall_fin_two.mpr ⟨⟨1, one_mem _, ?_⟩, ⟨g⁻¹, inv_mem hgL, ?_⟩⟩
    · show cj J 1 ≤ R
      rw [cj_one]; exact hJR
    · show cj (cj J g) g⁻¹ ≤ R
      rw [cj_inv_cj]; exact hJR
  have hXJ : ∀ i, (elemThompson (X i) 2).map (X i).subtype = X i := by
    refine Fin.forall_fin_two.mpr ⟨elemThompson_map_subtype_self 2 R, ?_⟩
    show elemThompsonIn 2 (cj J g) = cj J g
    rw [elemThompsonIn_cj, hJdef, elemThompsonIn_elemThompsonIn]
  have hXe : ∀ i, pRank 2 (X i) = pRank 2 R := by
    refine Fin.forall_fin_two.mpr ⟨pRank_elemThompsonIn 2 R, ?_⟩
    show pRank 2 (cj J g) = pRank 2 R
    rw [pRank_cj]
    exact pRank_elemThompsonIn 2 R
  have hq2 : (V ⊓ Subgroup.centralizer (L : Set H)).relIndex V = Nat.card k ^ 2 := by
    have h1 : (V ⊓ Subgroup.centralizer (L : Set H)).relIndex V = φ.ker.index := by
      rw [h.φ_ker]
      show ((V ⊓ Subgroup.centralizer (L : Set H)).subgroupOf V).index =
        ((Subgroup.centralizer (L : Set H)).subgroupOf V).index
      rw [inf_comm, Subgroup.inf_subgroupOf_right]
    rw [h1, Subgroup.index_ker, MonoidHom.range_eq_top.mpr h.φ_surj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, card_fin_two_pi]
  have hidx' : (V ⊓ Subgroup.centralizer ((cj J g : Subgroup H) : Set H)).relIndex V =
      Nat.card k := by
    have e1 : V ⊓ Subgroup.centralizer ((cj J g : Subgroup H) : Set H) =
        cj (V ⊓ Subgroup.centralizer (J : Set H)) g := by
      rw [cj_inf, cj_eq_self_of_normal (Y := V), centralizer_cj]
    rw [e1]
    have e2 : (cj (V ⊓ Subgroup.centralizer (J : Set H)) g).relIndex V =
        (cj (V ⊓ Subgroup.centralizer (J : Set H)) g).relIndex (cj V g) := by
      rw [cj_eq_self_of_normal (Y := V)]
    rw [e2]
    unfold cj
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hidx
  have hcodim : ∏ i, (V ⊓ Subgroup.centralizer (X i : Set H)).relIndex V ≤
      (V ⊓ Subgroup.centralizer (L : Set H)).relIndex V := by
    rw [Fin.prod_univ_two]
    show (V ⊓ Subgroup.centralizer (J : Set H)).relIndex V *
      (V ⊓ Subgroup.centralizer ((cj J g : Subgroup H) : Set H)).relIndex V ≤ _
    rw [hidx, hidx', hq2, ← pow_two]
  have hRsyl : IsSylowIn 2 R (⊤ : Subgroup H) := h.sylow
  have hQsyl : IsSylowIn 2 (R ⊓ Subgroup.centralizer (V : Set H))
      (Subgroup.centralizer (V : Set H)) :=
    hRsyl.inf_normal (N := Subgroup.centralizer (V : Set H)) le_top inferInstance
  obtain ⟨hPS, hE2, hSyl⟩ := Baumann_central_splitting_and_Sylow_transfer 2 V hVe R hR2 hVR L
    hLclosure hHLR (R ⊓ Subgroup.centralizer (V : Set H)) (L ⊓ CFSG.pCore 2 H) rfl hPL.symm hPQ hLQ
    hΦ hineq 2 (by norm_num) X hXL hXJ hXe (J ⊔ cj J g) hXI.symm hρV J rfl
    le_sup_left hcodim S E rfl rfl
  obtain ⟨hSyl1, -⟩ := hSyl hQsyl
  have hc2 : (CFSG.pCore 2 L).map L.subtype ≤ S := by
    rw [hPL]; exact hPS
  have hJS : J ≤ S := elemThompsonIn_le_elemBaumannIn 2 R
  have hK : ∀ v : V, v ∈ φ.ker → (v : H) ∈ Subgroup.centralizer (J : Set H) ∧ (v : H) ∈ Subgroup.centralizer (L : Set H) := by
    intro v hv
    refine ⟨hJcent v hv, ?_⟩
    have := h.φ_ker ▸ hv
    exact Subgroup.mem_subgroupOf.mp this
  have hc5 : ⁅J, V ⊓ Subgroup.centralizer (L : Set H)⁆ = ⊥ := by
    apply commutator_eq_bot_of_commute
    intro w hw y hy
    have hyker : (⟨y, hy.1⟩ : V) ∈ φ.ker := by
      rw [h.φ_ker]; exact Subgroup.mem_subgroupOf.mpr hy.2
    exact Subgroup.mem_centralizer_iff.mp (hJcent ⟨y, hy.1⟩ hyker) w hw
  have hℓ'ne : B⁻¹ • ℓ ≠ ℓ := by
    intro heq
    apply hBℓ
    rw [inv_smul_eq_iff] at heq
    exact heq.symm
  have hcjρ : (cj J g).map ρ = rootGamma (B⁻¹ • ℓ) := map_cj_eq_rootGamma hJρ hgB
  have hc3 : (L ⊔ S).map ρ = slGamma k := by
    apply le_antisymm
    · rw [Subgroup.map_sup]
      exact sup_le h.map_L_le (hSρ ▸ rootGamma_le_slGamma ℓ)
    · intro x hx
      obtain ⟨B'', hB''⟩ := mem_slGamma_iff.mp hx
      have hmem : B'' ∈ rootGrp ℓ ⊔ rootGrp (B⁻¹ • ℓ) := by
        rw [rootGrp_sup_rootGrp hℓ'ne.symm]; trivial
      have hperm : ((x : Gamma k) : Equiv.Perm (Fin 2 → k)) ∈
          rootPerm ℓ ⊔ rootPerm (B⁻¹ • ℓ) := by
        rw [hB'']
        have : slPerm k B'' ∈ (rootGrp ℓ ⊔ rootGrp (B⁻¹ • ℓ)).map (slPerm k) := ⟨B'', hmem, rfl⟩
        rwa [Subgroup.map_sup] at this
      have hx' : x ∈ rootGamma ℓ ⊔ rootGamma (B⁻¹ • ℓ) := by
        have hmap : (rootGamma ℓ ⊔ rootGamma (B⁻¹ • ℓ)).map (Gamma k).subtype =
            rootPerm ℓ ⊔ rootPerm (B⁻¹ • ℓ) := by
          rw [Subgroup.map_sup, map_subtype_rootGamma, map_subtype_rootGamma]
        rw [← hmap] at hperm
        obtain ⟨y, hy, hyx⟩ := hperm
        have : y = x := Subtype.ext hyx
        rwa [this] at hy
      have hle : rootGamma ℓ ⊔ rootGamma (B⁻¹ • ℓ) ≤ (L ⊔ S).map ρ := by
        refine sup_le ?_ ?_
        · rw [← hJρ]; exact Subgroup.map_mono (hJS.trans le_sup_right)
        · rw [← hcjρ]
          apply Subgroup.map_mono
          intro y hy
          have hyJ : g * y * g⁻¹ ∈ J := mem_cj.mp hy
          have hy' : y = g⁻¹ * (g * y * g⁻¹) * g := by group
          rw [hy']
          exact mul_mem (mul_mem (inv_mem (Subgroup.mem_sup_left hgL))
            (Subgroup.mem_sup_right (hJS hyJ))) (Subgroup.mem_sup_left hgL)
      exact hle hx'
  have hc1 : IsSylowIn 2 S (L ⊔ S) := by
    have hCN : Subgroup.centralizer (V : Set H) ≤ ρ.ker := h.centralizer_le_ker
    have hodd : ¬ 2 ∣ (Subgroup.centralizer (V : Set H)).relIndex ρ.ker :=
      h.not_two_dvd_relIndex_ker hVH
    have hSR : S ≤ R := elemBaumannIn_le 2 R
    have hSN : S ⊓ ρ.ker = S ⊓ Subgroup.centralizer (V : Set H) := by
      apply le_antisymm
      · rintro x ⟨hxS, hxN⟩
        have : x ∈ R ⊓ ρ.ker := ⟨hSR hxS, hxN⟩
        rw [h.inf_ker_eq hVH, ← hCR] at this
        exact ⟨hxS, this.2⟩
      · exact inf_le_inf_left _ hCN
    have hv : (Nat.card ((L ⊔ S) ⊓ ρ.ker : Subgroup H)).factorization 2 =
        (Nat.card ((L ⊔ S) ⊓ Subgroup.centralizer (V : Set H) : Subgroup H)).factorization 2 := by
      set A : Subgroup H := (L ⊔ S) ⊓ Subgroup.centralizer (V : Set H) with hA
      set B' : Subgroup H := (L ⊔ S) ⊓ ρ.ker with hB'
      have hAB : A ≤ B' := inf_le_inf_left _ hCN
      have hmul := Subgroup.relIndex_mul_card A B'
      rw [inf_of_le_left hAB] at hmul
      have hr0 : A.relIndex B' ≠ 0 := relIndex_ne_zero_of_finite _ _
      have hrodd : ¬ 2 ∣ A.relIndex B' := by
        have e1 : A = Subgroup.centralizer (V : Set H) ⊓ B' := by
          ext x
          constructor
          · rintro ⟨hx1, hx2⟩
            exact ⟨hx2, hx1, hCN hx2⟩
          · rintro ⟨hx2, hx1, -⟩
            exact ⟨hx1, hx2⟩
        rw [e1, Subgroup.inf_relIndex_right]
        have hCnormal : (Subgroup.centralizer (V : Set H)).Normal := inferInstance
        rw [← Subgroup.relIndex_sup_right (K := Subgroup.centralizer (V : Set H)) (H := B')]
        have hle1 : Subgroup.centralizer (V : Set H) ≤ B' ⊔ Subgroup.centralizer (V : Set H) :=
          le_sup_right
        have hle2 : B' ⊔ Subgroup.centralizer (V : Set H) ≤ ρ.ker :=
          sup_le inf_le_right hCN
        have := Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
        intro hd
        exact hodd (hd.trans (Dvd.intro _ this))
      have hfac := congrArg (fun n => n.factorization 2) hmul.symm
      simp only [Nat.factorization_mul hr0 Nat.card_pos.ne', Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hrodd, zero_add] at hfac
      exact hfac
    have c1 := card_eq_card_map_mul_card_inf_ker ρ (L ⊔ S)
    have c2 := card_eq_card_map_mul_card_inf_ker ρ S
    rw [hc3] at c1
    rw [hSρ, card_rootGamma, hSN] at c2
    have hs1 := hSyl1.card_eq
    have hsl := card_eq_two_pow_factorization_slGamma (k := k)
    refine isSylowIn_of_card_eq le_sup_right ?_
    have hpos1 : Nat.card (slGamma k) ≠ 0 := Nat.card_pos.ne'
    have hpos2 : Nat.card ((L ⊔ S) ⊓ ρ.ker : Subgroup H) ≠ 0 := Nat.card_pos.ne'
    rw [c2, hs1, c1, Nat.factorization_mul hpos1 hpos2, Finsupp.add_apply, hv, pow_add, ← hsl]
  refine ⟨ℓ, hc1, hc2, hJρ, hSρ, hc3, hE2, hc5, ?_⟩
  set U : Subgroup H := E ⊓ Subgroup.centralizer (L : Set H) with hU
  set D : Subgroup H := V ⊓ Subgroup.centralizer (J : Set H) with hD
  have hDE : D ≤ E := by
    rw [hE2]; exact le_sup_right
  have hKD : V ⊓ Subgroup.centralizer (L : Set H) ≤ U := by
    intro x hx
    have hxker : (⟨x, hx.1⟩ : V) ∈ φ.ker := by
      rw [h.φ_ker]; exact Subgroup.mem_subgroupOf.mpr hx.2
    exact ⟨hDE ⟨hx.1, hJcent _ hxker⟩, hx.2⟩
  have hg1 : ((ρ g : Gamma k) : Equiv.Perm (Fin 2 → k)) ≠ 1 := by
    intro h1
    rw [hgB] at h1
    have : B = 1 := slPerm_injective (by rw [h1, map_one])
    apply hBℓ
    rw [this, one_smul]
  have hVsub : V ≤ ⁅V, L⁆ ⊔ U :=
    (h.V_le_commutator_sup hgL hg1).trans (sup_le_sup_left hKD _)
  have hVT : V ≤ ⨆ l ∈ L, cj D l := h.V_le_iSup_cj hline hJcent hgL hgB hBℓ
  apply le_antisymm
  · refine iSup₂_le fun l hl => ?_
    have h1 : cj E l ≤ cj U l ⊔ cj D l := by
      rw [← cj_sup]
      exact cj_mono hE2.le
    refine h1.trans (sup_le ?_ ?_)
    · refine le_sup_of_le_right ?_
      intro x hx
      have hxU : l * x * l⁻¹ ∈ U := mem_cj.mp hx
      have hc : l⁻¹ * (l * x * l⁻¹) = (l * x * l⁻¹) * l⁻¹ :=
        Subgroup.mem_centralizer_iff.mp hxU.2 l⁻¹ (inv_mem hl)
      have hxeq : x = l * x * l⁻¹ := by
        calc x = l⁻¹ * (l * x * l⁻¹) * l := by group
          _ = (l * x * l⁻¹) * l⁻¹ * l := by rw [hc]
          _ = l * x * l⁻¹ := by group
      rw [hxeq]
      exact hxU
    · refine le_trans ?_ hVsub
      intro x hx
      have hxD : l * x * l⁻¹ ∈ D := mem_cj.mp hx
      have : x = l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ := by group
      rw [this]
      exact hVn.conj_mem _ hxD.1 l⁻¹
  · refine sup_le ?_ ?_
    · have hTE : (⨆ l ∈ L, cj D l) ≤ ⨆ l ∈ L, cj E l :=
        iSup₂_le fun l hl => le_iSup₂_of_le (f := fun (l : H) (_ : l ∈ L) => cj E l) l hl
          (cj_mono hDE)
      exact ((Subgroup.commutator_le_left V L).trans hVT).trans hTE
    · calc U ≤ E := inf_le_left
        _ = cj E 1 := cj_one.symm
        _ ≤ ⨆ l ∈ L, cj E l := le_iSup₂ (f := fun (l : H) (_ : l ∈ L) => cj E l) 1 (one_mem L)

end IsNatQuotSetting

end CFSG.QuasithinUnique.Setup.Campbell
