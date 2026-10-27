module

public import CFSG.FeitThompson.Representations.ScalarCoreDetectingFamilyCoherent
public import CFSG.FeitThompson.OddOrder.PConfigChiefFactorLinearModel

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Module ChiefFactorLinearAction ChiefFactorFaithfulImage

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Dictionary

variable {p : ℕ} {E : Type*} [Group E] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

def submoduleOrderIsoSubgroup (p : ℕ) {E : Type*} [Group E] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (e : E ≃* Multiplicative V) : Submodule (ZMod p) V ≃o Subgroup E :=
  ((AddSubgroup.toZModSubmodule p (M := V)).symm.trans AddSubgroup.toSubgroup).trans
    e.comapSubgroup

theorem submoduleOrderIsoSubgroup_apply (e : E ≃* Multiplicative V)
    (W : Submodule (ZMod p) V) :
    submoduleOrderIsoSubgroup p e W = subgroupOfSubmodule e W := by
  ext y
  rw [mem_subgroupOfSubmodule]
  simp [submoduleOrderIsoSubgroup, MulEquiv.comapSubgroup]

theorem natCard_subgroupOfSubmodule (e : E ≃* Multiplicative V) (W : Submodule (ZMod p) V) :
    Nat.card (subgroupOfSubmodule e W) = Nat.card W :=
  Nat.card_congr
    { toFun := fun y => ⟨Multiplicative.toAdd (e y.1), (mem_subgroupOfSubmodule e W _).1 y.2⟩
      invFun := fun v => ⟨e.symm (Multiplicative.ofAdd v.1), by
        rw [mem_subgroupOfSubmodule]; simp [v.2]⟩
      left_inv := fun y => by ext; simp
      right_inv := fun v => by ext; simp }

theorem iSupIndep_subgroupOfSubmodule (e : E ≃* Multiplicative V) {ι : Type*}
    {W : ι → Submodule (ZMod p) V} (h : iSupIndep W) :
    iSupIndep fun i => subgroupOfSubmodule e (W i) := by
  have h2 := (iSupIndep_map_orderIso_iff (submoduleOrderIsoSubgroup p e)).mpr h
  simpa [Function.comp_def, submoduleOrderIsoSubgroup_apply] using h2

theorem iSup_subgroupOfSubmodule_eq_top (e : E ≃* Multiplicative V) {ι : Type*}
    {W : ι → Submodule (ZMod p) V} (h : ⨆ i, W i = ⊤) :
    ⨆ i, subgroupOfSubmodule e (W i) = ⊤ := by
  have h2 : ⨆ i, submoduleOrderIsoSubgroup p e (W i)
      = submoduleOrderIsoSubgroup p e (⨆ i, W i) :=
    (map_iSup (submoduleOrderIsoSubgroup p e) W).symm
  simp only [submoduleOrderIsoSubgroup_apply] at h2
  rw [h2, h, subgroupOfSubmodule_top]

end Dictionary

section Action

variable {L : Type*} [Group L] {H H0 U : Subgroup L} [H.Normal] [H0.Normal] {p : ℕ}
  {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem conjQuotientAut_eq_factorConjAut (H H0 : Subgroup L) [H.Normal] [H0.Normal] :
    conjQuotientAut H H0 = factorConjAut H H0 := by
  ext g y
  induction y using QuotientGroup.induction_on with
  | _ h => rw [conjQuotientAut_apply_mk, factorConjAut_mk]

theorem toAdd_conjQuotientAut (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative V) (g : L) (x : ↥H ⧸ H0.subgroupOf H) :
    Multiplicative.toAdd (e (conjQuotientAut H H0 g x))
      = factorLinearAut p H H0 e g (Multiplicative.toAdd (e x)) := by
  rw [conjQuotientAut_eq_factorConjAut, factorLinearAut_apply]

theorem map_conjQuotientAut_subgroupOfSubmodule
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative V) (g : L) (W : Submodule (ZMod p) V) :
    Subgroup.map (conjQuotientAut H H0 g : MulEquiv _ _).toMonoidHom (subgroupOfSubmodule e W)
      = subgroupOfSubmodule e (W.map (factorLinearAut p H H0 e g : V →ₗ[ZMod p] V)) := by
  ext y
  simp only [Subgroup.mem_map, mem_subgroupOfSubmodule, Submodule.mem_map,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Multiplicative.toAdd (e x), hx, (toAdd_conjQuotientAut p e g x).symm⟩
  · rintro ⟨w, hw, hwy⟩
    refine ⟨e.symm (Multiplicative.ofAdd w), ?_, ?_⟩
    · simpa using hw
    · refine e.injective (Multiplicative.toAdd.injective ?_)
      rw [toAdd_conjQuotientAut p e g (e.symm (Multiplicative.ofAdd w))]
      simpa using hwy

theorem mem_lineFixer_subgroupOfSubmodule_iff
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative V) (W : Submodule (ZMod p) V) {u : L} :
    u ∈ lineFixer H H0 U (subgroupOfSubmodule e W) ↔
      u ∈ U ∧ ∀ w ∈ W, factorLinearAut p H H0 e u w = w := by
  rw [mem_lineFixer]
  refine and_congr_right fun _ => ⟨fun h w hw => ?_, fun h v hv => ?_⟩
  · have hmem : e.symm (Multiplicative.ofAdd w) ∈ subgroupOfSubmodule e W := by
      rw [mem_subgroupOfSubmodule]; simpa using hw
    have hfix := h _ hmem
    have h2 := toAdd_conjQuotientAut p e u (e.symm (Multiplicative.ofAdd w))
    rw [hfix] at h2
    simpa using h2.symm
  · refine e.injective (Multiplicative.toAdd.injective ?_)
    rw [toAdd_conjQuotientAut p e u v]
    exact h _ ((mem_subgroupOfSubmodule e W v).1 hv)

theorem lineFixerInf_eq_chiefActionKer {q : ℕ} [Nonempty (ZMod q)]
    {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} (hsup : ⨆ i, Eline i = ⊤) :
    lineFixerInf H H0 U Eline = chiefActionKer H H0 U := by
  obtain ⟨i0⟩ := ‹Nonempty (ZMod q)›
  refine le_antisymm (fun u hu => ?_) (le_lineFixerInf fun i => fun u hu => ?_)
  · have hall : ∀ i, u ∈ lineFixer H H0 U (Eline i) := fun i =>
      lineFixerInf_le_lineFixer H H0 U Eline i hu
    refine (mem_chiefActionKer_iff_mem_ker H H0 U).2 ⟨(mem_lineFixer.1 (hall i0)).1, ?_⟩
    rw [MonoidHom.mem_ker]
    have hle : (⊤ : Subgroup (↥H ⧸ H0.subgroupOf H)) ≤
        (conjQuotientAut H H0 u : MulEquiv _ _).toMonoidHom.eqLocus (MonoidHom.id _) := by
      rw [← hsup]
      exact iSup_le fun i => fun v hv => (mem_lineFixer.1 (hall i)).2 v hv
    ext v
    exact hle (Subgroup.mem_top v)
  · obtain ⟨huU, hker⟩ := (mem_chiefActionKer_iff_mem_ker H H0 U).1 hu
    exact mem_lineFixer.2 ⟨huU, fun v _ => by rw [MonoidHom.mem_ker.1 hker]; rfl⟩

end Action

namespace ScalarLineSystem

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {q : ℕ}

theorem forall_lineScalar_eq_one (S : ScalarLineSystem k V q) {i : ZMod q}
    (h : ∀ a : S.A, S.lineScalar i a = 1) (j : ZMod q) (a : S.A) : S.lineScalar j a = 1 := by
  have := S.neZero_index
  have step : ∀ l : ZMod q, (∀ a : S.A, S.lineScalar l a = 1) →
      ∀ a : S.A, S.lineScalar (l + 1) a = 1 := by
    intro l hl a
    have ha' : S.b⁻¹ * (a : V ≃ₗ[k] V) * S.b ∈ S.A := S.conj_inv_mem a.2
    have hconj := S.lineScalar_conj l ⟨S.b⁻¹ * (a : V ≃ₗ[k] V) * S.b, ha'⟩
    rw [hl ⟨S.b⁻¹ * (a : V ≃ₗ[k] V) * S.b, ha'⟩] at hconj
    have heq : (⟨S.b * (S.b⁻¹ * (a : V ≃ₗ[k] V) * S.b) * S.b⁻¹, S.conj_mem ha'⟩ : S.A) = a := by
      refine Subtype.ext ?_
      simp only
      group
    rwa [heq] at hconj
  have key : ∀ m : ℕ, ∀ a : S.A, S.lineScalar (i + (m : ZMod q)) a = 1 := by
    intro m
    induction m with
    | zero => simpa using h
    | succ n ih =>
      have hstep := step (i + (n : ZMod q)) ih
      intro a
      have heq : i + ((n + 1 : ℕ) : ZMod q) = i + (n : ZMod q) + 1 := by push_cast; ring
      rw [heq]
      exact hstep a
  have hj : i + (((j - i).val : ℕ) : ZMod q) = j := by
    rw [ZMod.natCast_val, ZMod.cast_id]
    ring
  rw [← hj]
  exact key _ a

theorem exists_lineScalar_ne_one (S : ScalarLineSystem k V q) (i : ZMod q) :
    ∃ a : S.A, S.lineScalar i a ≠ 1 := by
  by_contra hcon
  push Not at hcon
  refine S.A_ne_bot ((Subgroup.eq_bot_iff_forall S.A).2 fun a ha => ?_)
  have hall : ∀ j, S.lineScalar j (⟨a, ha⟩ : S.A) = 1 :=
    fun j => S.forall_lineScalar_eq_one hcon j ⟨a, ha⟩
  simpa using S.eq_one_of_forall_lineScalar_eq (c := 1) hall

end ScalarLineSystem

theorem eq_zero_of_apply_eq_of_isIrreducible {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] {A : Subgroup (V ≃ₗ[k] V)} [IsMulCommutative ↥A]
    [(linearGroupRep A).IsIrreducible] {a : V ≃ₗ[k] V} (ha : a ∈ A) (ha1 : a ≠ 1)
    {v : V} (hv : a v = v) : v = 0 := by
  have hx : ((a : V →ₗ[k] V) - 1) ∈ envelopingSubalgebra A :=
    sub_mem (coe_mem_envelopingSubalgebra ha) (one_mem _)
  have hx0 : ((a : V →ₗ[k] V) - 1) ≠ 0 := by
    intro h
    refine ha1 (LinearEquiv.toLinearMap_injective ?_)
    have h2 : (a : V →ₗ[k] V) = (1 : Module.End k V) := by rwa [sub_eq_zero] at h
    rw [h2]
    rfl
  exact injective_of_mem_envelopingSubalgebra (A := A) hx hx0
    (by simp [hv] : ((a : V →ₗ[k] V) - 1) v = ((a : V →ₗ[k] V) - 1) 0)

theorem fixedFree_of_isIrreducible {L : Type*} [Group L] {H H0 U : Subgroup L} [H.Normal]
    [H0.Normal] {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative V)
    (hab : IsMulCommutative ↥(factorLinearImage p H H0 U e))
    (hirr : (linearGroupRep (factorLinearImage p H H0 U e)).IsIrreducible) :
    ∀ u ∈ U, u ∉ chiefActionKer H H0 U → ∀ h ∈ H,
      ((u⁻¹ * h * u : L) : L ⧸ H0) = (h : L ⧸ H0) → h ∈ H0 := by
  have := hab
  have := hirr
  intro u hu hnot h hh hfix
  set x : ↥H ⧸ H0.subgroupOf H := QuotientGroup.mk ⟨h, hh⟩ with hx
  have hufix : conjQuotientAut H H0 u⁻¹ x = x := by
    rw [hx, conjQuotientAut_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [MulAut.conjNormal_apply] using QuotientGroup.eq.1 hfix
  set a := factorLinearAut p H H0 e u⁻¹ with ha
  have haD : a ∈ factorLinearImage p H H0 U e :=
    factorLinearAut_mem_factorLinearImage p e (U.inv_mem hu)
  by_cases ha1 : a = 1
  · exfalso
    refine hnot ((mem_chiefActionKer_iff_mem_ker H H0 U).2 ⟨hu, ?_⟩)
    rw [MonoidHom.mem_ker, conjQuotientAut_eq_factorConjAut]
    have h1 : factorConjAut H H0 u⁻¹ = 1 := (factorLinearAut_eq_one_iff p e).1 ha1
    rw [map_inv, inv_eq_one] at h1
    exact h1
  · have hfixlin : a (Multiplicative.toAdd (e x)) = Multiplicative.toAdd (e x) := by
      rw [ha, ← toAdd_conjQuotientAut p e u⁻¹ x, hufix]
    have hzero := eq_zero_of_apply_eq_of_isIrreducible haD ha1 hfixlin
    have hx1 : x = 1 := by
      refine e.injective ?_
      rw [map_one]
      exact Multiplicative.toAdd.injective (by simpa using hzero)
    rw [hx, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx1
    exact hx1

open ScalarCoreCoherence in
theorem isScalarCoreConfig_of_scalarLineSystem {L : Type*} [Group L] [Finite L]
    [Group.IsSolvable L] {H J U B F W2 H0 : Subgroup L} [H.Normal] [H0.Normal] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    {A : Set L}
    (hcfg : IsPTypeConfig H J U B F W2) (hodd : Odd (Nat.card L)) (hq : Nat.card ↥B = q)
    (hchief : IsChiefFactor H H0) (hCU : H ⊓ centralizer (U : Set L) ≤ H0)
    {b : L} (hb : b ∈ B) (hb1 : b ≠ 1) (hbgen : Subgroup.zpowers b = B)
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative V)
    (S : ScalarLineSystem (ZMod p) V q)
    (hSA : S.A = factorLinearImage p H H0 U e) (hSb : S.b = factorLinearAut p H H0 e b)
    (hAsub : A ⊆ (J : Set L) \ {1}) (hAinv : ∀ g : L, ∀ x ∈ A, g⁻¹ * x * g ∈ A)
    (hAcent : ∀ h ∈ H, h ≠ 1 →
      ((J ⊓ centralizer ({h} : Set L) : Subgroup L) : Set L) \ {1} ⊆ A) :
    IsScalarCoreConfig p q J H U B H0 (fun i => subgroupOfSubmodule e (S.L i)) A := by
  have hs := hcfg.isFaithfulImageSetup hq hchief hCU hb hb1
  have hqp : q.Prime := Fact.out
  have hpp : p.Prime := Fact.out
  have hcard : Nat.card (↥H ⧸ H0.subgroupOf H) = p ^ q := hs.natCard_quotient_eq p e hpp
  refine
    { solvable := ‹_›
      odd_card := hodd
      q_prime := hqp
      p_prime := hpp
      p_odd := ?_
      p_ne_q := hs.ne_q p e hpp
      isComplement_K_B := hcfg.isComplement'_J_B
      H_le_K := hcfg.le_J_H
      U_le_K := hcfg.le_J_U
      disjoint_H_U := hcfg.disjoint_H_U
      sup_H_U := hcfg.sup_eq_J
      card_B := hq
      exists_gen_B := ⟨b, hb, hbgen.symm, ?_⟩
      B_le_normalizer_U := hcfg.le_normalizer_U
      coprime_H_U := Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le (le_sup_left : U ≤ U ⊔ B)) hcfg.coprime_natCard_H_sup
      coprime_q_K := ?_
      inf_centralizer_U_B := ?_
      H0_le_H := hchief.le
      card_quotient := hcard
      indep_Eline := iSupIndep_subgroupOfSubmodule e S.indep_L
      iSup_Eline := iSup_subgroupOfSubmodule_eq_top e S.iSup_L
      card_Eline := ?_
      map_U_Eline := ?_
      lineFixer_ne := ?_
      A_subset := hAsub
      A_invariant := hAinv
      centralizer_subset_A := hAcent }
  ·
    have hpdvd : p ∣ Nat.card (↥H ⧸ H0.subgroupOf H) := by
      rw [hcard]; exact dvd_pow_self p hqp.pos.ne'
    have hpL : p ∣ Nat.card L :=
      hpdvd.trans ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card H))
    rcases Nat.even_or_odd p with he | ho
    · exact absurd (he.two_dvd.trans hpL)
        (by simpa [Nat.two_dvd_ne_zero] using Nat.odd_iff.1 hodd)
    · exact ho
  ·
    intro i
    rw [show ((conjQuotientAut H H0 b : MulEquiv _ _) : _ →* _)
        = (conjQuotientAut H H0 b : MulEquiv _ _).toMonoidHom from rfl,
      map_conjQuotientAut_subgroupOfSubmodule]
    congr 1
    rw [← hSb]
    exact S.map_b_L i
  ·
    have hhall := hcfg.hall_B
    rw [hq] at hhall
    have hidx : B.index = Nat.card J := hcfg.isComplement'_J_B.index_eq_card
    rwa [hidx] at hhall
  ·
    rw [centralizer_coe_eq_centralizer_singleton hbgen]
    exact hcfg.inf_centralizer_U_eq_bot b hb hb1
  ·
    intro i
    rw [natCard_subgroupOfSubmodule]
    have hfin : Module.Finite (ZMod p) (S.L i) := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := (S.L i)), S.finrank_L i, pow_one,
      Nat.card_zmod]
  ·
    intro u hu i
    rw [show ((conjQuotientAut H H0 u : MulEquiv _ _) : _ →* _)
        = (conjQuotientAut H H0 u : MulEquiv _ _).toMonoidHom from rfl,
      map_conjQuotientAut_subgroupOfSubmodule]
    congr 1
    exact S.map_L _ (hSA ▸ factorLinearAut_mem_factorLinearImage p e hu) i
  ·
    intro i
    obtain ⟨a, ha⟩ := S.exists_lineScalar_ne_one i
    have ha2 : (a : V ≃ₗ[ZMod p] V) ∈ factorLinearImage p H H0 U e := hSA ▸ a.2
    obtain ⟨u, hu, hueq⟩ := (mem_factorLinearImage p e).1 ha2
    intro heq
    have hmem : u ∈ lineFixer H H0 U (subgroupOfSubmodule e (S.L i)) := by rw [heq]; exact hu
    rw [mem_lineFixer_subgroupOfSubmodule_iff] at hmem
    refine ha ((S.eq_lineScalar i a (c := 1) ?_).symm)
    intro v hv
    rw [Units.val_one, one_smul]
    have h2 := hmem.2 v hv
    rw [hueq] at h2
    exact h2

end CFSG.FeitThompson
