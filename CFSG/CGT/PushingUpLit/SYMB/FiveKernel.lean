module

public import CFSG.CGT.PushingUpLit.SYMB.SevenSchur

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

theorem mem_of_oResidualTwo {Γ : Type} [Group Γ] {E M Z : Subgroup Γ}
    (hE : oResidualTwo ↥E = ⊤) (hM2 : IsPGroup 2 ↥M) (hZ : (Z.subgroupOf M).Normal)
    (d : ↥E → ↥M)
    (hd : ∀ e e' : ↥E, (QuotientGroup.mk (d (e * e')) : ↥M ⧸ Z.subgroupOf M) =
      QuotientGroup.mk (d e) * QuotientGroup.mk (d e')) (e : ↥E) :
    d e ∈ Z.subgroupOf M := by
  have hQ : IsPGroup 2 (↥M ⧸ Z.subgroupOf M) := hM2.to_quotient _
  let f : ↥E →* ↥M ⧸ Z.subgroupOf M := MonoidHom.mk' (fun e => QuotientGroup.mk (d e)) hd
  have h1 : f e = 1 := hom_eq_one_of_oResidualTwo_eq_top' hE hQ f e
  exact (QuotientGroup.eq_one_iff _).1 h1

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ} {n : ℕ}
  {φ : ↥G →* Equiv.Perm (Fin n)} {ψ : ↥V →* ↥(G6.coreMod n)} {T' : Set (Equiv.Perm (Fin n))}

omit [Finite Γ] in
theorem comm_V_E_mem (S : SymSetting G T V n φ ψ T') {E : Subgroup Γ} (hEG : E ≤ G)
    (hnorm : G ≤ Subgroup.normalizer (E : Set Γ)) {v e : Γ} (hv : v ∈ V) (he : e ∈ E) :
    ⁅v, e⁆ ∈ E ⊓ Subgroup.centralizer (V : Set Γ) := by
  have hvG : v ∈ G := (sym_V_le_pCore S |>.trans (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 G)) hv
  have heG : e ∈ G := hEG he
  have h1 : ⁅v, e⁆ ∈ E := by
    have e1 : ⁅v, e⁆ = (v * e * v⁻¹) * e⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e1]
    exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp (hnorm hvG) e).mp he) (E.inv_mem he)
  have h2 : ⁅v, e⁆ ∈ V := by
    have e1 : ⁅v, e⁆ = v * (e * v⁻¹ * e⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e1]
    exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (S.data.normal heG) v⁻¹).mp (V.inv_mem hv))
  have h3 : ⁅v, e⁆ ∈ Subgroup.centralizer (V : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := S.data.elemAbelian.1.is_comm.comm (⟨w, hw⟩ : ↥V) ⟨⁅v, e⁆, h2⟩
    exact congrArg Subtype.val this
  exact ⟨h1, h3⟩

omit [Finite Γ] in
theorem comm_V_E_le_K (S : SymSetting G T V n φ ψ T') {E : Subgroup Γ} (hEG : E ≤ G)
    (hnorm : G ≤ Subgroup.normalizer (E : Set Γ)) :
    ⁅V, E⁆ ≤ E ⊓ Subgroup.centralizer (V : Set Γ) := by
  rw [Subgroup.commutator_le]
  exact fun v hv e he => comm_V_E_mem S hEG hnorm hv he

omit [Finite Γ] in
theorem comm_V_E_le_V (S : SymSetting G T V n φ ψ T') {E : Subgroup Γ} (hEG : E ≤ G) :
    ⁅V, E⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv e he
  have e1 : ⁅v, e⁆ = v * (e * v⁻¹ * e⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [e1]
  exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (S.data.normal (hEG he)) v⁻¹).mp
    (V.inv_mem hv))

omit [Finite Γ] in
theorem comm_K_E_le_V₁ (S : SymSetting G T V n φ ψ T') {E : Subgroup Γ}
    (hEG : E ≤ G) (hres : oResidualTwo ↥E = ⊤) (hcomm : ⁅E, pCoreOf 2 G⁆ ≤ V)
    {K : Subgroup Γ} (hKQ : K ≤ pCoreOf 2 G) : ⁅K, E⁆ ≤ ⁅V, E⁆ := by
  classical
  rw [Subgroup.commutator_le]
  intro k hk e he
  set V₁ : Subgroup Γ := ⁅V, E⁆ with hV₁
  have hV1V : V₁ ≤ V := comm_V_E_le_V S hEG
  have hV2 : IsPGroup 2 ↥V :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 G).to_le (sym_V_le_pCore S)
  have hcommV : ∀ x y : ↥V, x * y = y * x := fun x y => S.data.elemAbelian.1.is_comm.comm x y
  have hZ : (V₁.subgroupOf V).Normal := ⟨fun x hx g => by
    have : g * x * g⁻¹ = x := by
      rw [hcommV g x]
      group
    rw [this]
    exact hx⟩
  have hmemV : ∀ e' ∈ E, ⁅k, e'⁆ ∈ V := by
    intro e' he'
    have h1 : ⁅e', k⁆ ∈ V := hcomm (Subgroup.commutator_mem_commutator he' (hKQ hk))
    have e1 : ⁅k, e'⁆ = ⁅e', k⁆⁻¹ := (commutatorElement_inv e' k).symm
    rw [e1]
    exact V.inv_mem h1
  let d : ↥E → ↥V := fun e' => ⟨⁅k, e'⁆, hmemV e' e'.2⟩
  have hd : ∀ e1 e2 : ↥E, (QuotientGroup.mk (d (e1 * e2)) : ↥V ⧸ V₁.subgroupOf V) =
      QuotientGroup.mk (d e1) * QuotientGroup.mk (d e2) := by
    intro e1 e2
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hcV : ⁅k, (e2 : Γ)⁆ ∈ V := hmemV _ e2.2
    have hmem : ⁅(e1 : Γ), (⁅k, (e2 : Γ)⁆)⁻¹⁆ ∈ V₁ := by
      have h1 : ⁅(⁅k, (e2 : Γ)⁆)⁻¹, (e1 : Γ)⁆ ∈ ⁅V, E⁆ :=
        Subgroup.commutator_mem_commutator (V.inv_mem hcV) e1.2
      have := V₁.inv_mem h1
      rwa [commutatorElement_inv] at this
    have e3 : ((d (e1 * e2))⁻¹ * (d e1 * d e2) : ↥V) = ⟨⁅(e1 : Γ), (⁅k, (e2 : Γ)⁆)⁻¹⁆, by
        have := V₁.inv_mem hmem
        exact hV1V hmem⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, d, commutatorElement_def]
      group
    rw [e3]
    exact hmem
  have := mem_of_oResidualTwo hres hV2 hZ d hd ⟨e, he⟩
  rw [Subgroup.mem_subgroupOf] at this
  exact this

section Dichotomy

variable {E : Subgroup Γ}

omit [Finite Γ] in
theorem map_comm_subgroupOf_top {K : Subgroup Γ} (hKE : K ≤ E) :
    (⁅K.subgroupOf E, (⊤ : Subgroup ↥E)⁆).map E.subtype = ⁅K, E⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKE, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

omit [Finite Γ] in
theorem altRestrict_ker_eq (S : SymSetting G T V n φ ψ T') (h : SymJoin G T V φ ψ E) :
    (altRestrict φ h.le fun _ he => h.map_mem_alt he).ker =
      (E ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf E := by
  ext e
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h1
    have h2 : φ ⟨e, h.le e.2⟩ = 1 := congrArg Subtype.val h1
    have h3 : (⟨e, h.le e.2⟩ : ↥G) ∈ φ.ker := h2
    rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h3
    exact ⟨e.2, h3.2⟩
  · rintro ⟨-, hec⟩
    have h3 : (⟨e, h.le e.2⟩ : ↥G) ∈ φ.ker := by
      rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨h.le e.2, hec⟩
    have h4 : φ ⟨e, h.le e.2⟩ = 1 := h3
    exact Subtype.ext h4

theorem exists_ker_gen (S : SymSetting G T V n φ ψ T') (h : SymJoin G T V φ ψ E) (h5 : 5 ≤ n)
    (hK2 : IsPGroup 2 ↥(E ⊓ Subgroup.centralizer (V : Set Γ))) :
    ∃ (e₀ : Γ) (he₀ : e₀ ∈ E), (φ ⟨e₀, h.le he₀⟩) ^ 2 = 1 ∧ φ ⟨e₀, h.le he₀⟩ ≠ 1 ∧
      e₀ ^ 2 ∈ E ⊓ Subgroup.centralizer (V : Set Γ) ∧
      E ⊓ Subgroup.centralizer (V : Set Γ) ≤
        Subgroup.zpowers (e₀ ^ 2) ⊔ ⁅E ⊓ Subgroup.centralizer (V : Set Γ), E⁆ ∧
      (e₀ ^ 2) ^ 2 ∈ ⁅E ⊓ Subgroup.centralizer (V : Set Γ), E⁆ := by
  classical
  have hEG : E ≤ G := h.le
  have hKE : E ⊓ Subgroup.centralizer (V : Set Γ) ≤ E := inf_le_left
  let η : ↥E →* alternatingGroup (Fin n) := altRestrict φ hEG fun _ he => h.map_mem_alt he
  have hηs : Function.Surjective η := SymJoin.altRestrict_surjective h
  have hηker := altRestrict_ker_eq S h
  have hK2η : IsPGroup 2 ↥η.ker := by
    rw [hηker]
    exact hK2.of_equiv (Subgroup.subgroupOfEquivOfLe hKE).symm
  let p : Fin 4 → Fin n := fun i => ⟨i.val, by omega⟩
  have hp : Function.Injective p := fun i j hij => Fin.ext (by simpa [p] using congrArg Fin.val hij)
  have h01 : p 0 ≠ p 1 := hp.ne (by decide)
  have h02 : p 0 ≠ p 2 := hp.ne (by decide)
  have h03 : p 0 ≠ p 3 := hp.ne (by decide)
  have h12 : p 1 ≠ p 2 := hp.ne (by decide)
  have h13 : p 1 ≠ p 3 := hp.ne (by decide)
  have h23 : p 2 ≠ p 3 := hp.ne (by decide)
  have hc₁ : (⟨cyc (p 0) (p 2) (p 1), cyc_mem_alternatingGroup h02 h01 h12.symm⟩ :
      alternatingGroup (Fin n)) ^ 3 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one (cyc (p 0) (p 2) (p 1))
    rw [(cyc_isThreeCycle h02 h01 h12.symm).orderOf] at this
    simpa using this
  have hc₂ : (⟨cyc (p 0) (p 3) (p 1), cyc_mem_alternatingGroup h03 h01 h13.symm⟩ :
      alternatingGroup (Fin n)) ^ 3 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one (cyc (p 0) (p 3) (p 1))
    rw [(cyc_isThreeCycle h03 h01 h13.symm).orderOf] at this
    simpa using this
  obtain ⟨a, ha, ha3⟩ := exists_order_three_lift η hηs hK2η hc₁
  obtain ⟨b, hb, hb3⟩ := exists_order_three_lift η hηs hK2η hc₂
  obtain ⟨hker, hy2⟩ := ker_le_sq_sup_of_lifts h5 η hηs h.residual hK2η hp ha3 hb3
    (by rw [ha]; rfl) (by rw [hb]; rfl)
  have hcomm := map_comm_subgroupOf_top (E := E) hKE
  have hηab : (η (a * b) : Equiv.Perm (Fin n)) =
      Equiv.swap (p 0) (p 2) * Equiv.swap (p 1) (p 3) := by
    rw [map_mul]
    simp only [Subgroup.coe_mul, ha, hb]
    exact swap_mul_eq h03 h13
  have hφab : φ ⟨((a * b : ↥E) : Γ), hEG (a * b).2⟩ = Equiv.swap (p 0) (p 2) * Equiv.swap (p 1) (p 3) :=
    hηab
  refine ⟨((a * b : ↥E) : Γ), (a * b).2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφab]
    have := swap_mul_sq_eq_one h01 h03 h12 h13 h23
    rwa [swap_mul_eq h03 h13] at this
  · rw [hφab]
    intro h1
    have h2 := congrArg (fun σ : Equiv.Perm (Fin n) => σ (p 0)) h1
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h01 h03,
      Equiv.Perm.coe_one, id] at h2
    exact h02 h2.symm
  ·
    have : (a * b) ^ 2 ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_pow, map_mul, ha, hb]
      apply Subtype.ext
      simpa [cyc] using swap_mul_sq_eq_one h01 h03 h12 h13 h23
    rw [hηker, Subgroup.mem_subgroupOf] at this
    simpa using this
  · intro k hk
    have hk' : (⟨k, hKE hk⟩ : ↥E) ∈ η.ker := by
      rw [hηker, Subgroup.mem_subgroupOf]
      exact hk
    have h1 := hker hk'
    have h2 : k ∈ (Subgroup.zpowers ((a * b) ^ 2) ⊔ ⁅η.ker, (⊤ : Subgroup ↥E)⁆).map E.subtype :=
      ⟨⟨k, hKE hk⟩, h1, rfl⟩
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hηker, hcomm] at h2
    simpa using h2
  · have h1 : (((a * b) ^ 2) ^ 2 : ↥E) ∈ ⁅η.ker, (⊤ : Subgroup ↥E)⁆ := hy2
    have h2 : (((((a * b) ^ 2) ^ 2 : ↥E)) : Γ) ∈ (⁅η.ker, (⊤ : Subgroup ↥E)⁆).map E.subtype :=
      ⟨_, h1, rfl⟩
    rw [hηker, hcomm] at h2
    simpa using h2

end Dichotomy

end CFSG.CGT.PushingUpLit.SYMB
