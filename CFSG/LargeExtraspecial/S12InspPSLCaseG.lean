module

public import CFSG.LargeExtraspecial.S12InspPSLLbar
public import CFSG.LargeExtraspecial.S12Fifteen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Submodule QuadraticMap CFSG.RankThree.OrthogonalInvolutions S12InspPSL

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem psl_exists_ne_zero_polar_eq_zero {U : Submodule (ZMod 2) S.Qt}
    (hU : 3 ≤ finrank (ZMod 2) U) (y₁ y₂ : S.Qt) :
    ∃ a ∈ U, a ≠ 0 ∧ polar S.q y₁ a = 0 ∧ polar S.q y₂ a = 0 := by
  set f : U →ₗ[ZMod 2] ZMod 2 × ZMod 2 :=
    (S.q.polarBilin y₁ ∘ₗ U.subtype).prod (S.q.polarBilin y₂ ∘ₗ U.subtype)
  have hlt : finrank (ZMod 2) (ZMod 2 × ZMod 2) < finrank (ZMod 2) U := by
    rw [Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt
    (f := f) hlt)
  rw [LinearMap.mem_ker] at ha
  refine ⟨a, a.2, fun h => ha0 (Subtype.ext h), ?_, ?_⟩
  · have := congrArg Prod.fst ha
    exact this
  · have := congrArg Prod.snd ha
    exact this

theorem psl_relIndex_fixVec12_add_one (H : Subgroup S.O) {v : S.Qt} (hv : v ≠ 0)
    {W : Submodule (ZMod 2) S.Qt} (hW : ∀ h ∈ H, (h : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W)
    (htr : ∀ w ∈ W, w ≠ 0 → ∃ h ∈ H, (h : S.Qt ≃ₗ[ZMod 2] S.Qt) v = w) :
    (S.fixVec12 v).relIndex H + 1 = 2 ^ finrank (ZMod 2) W := by
  classical
  have : Finite S.Qt := Module.finite_of_finite (ZMod 2)
  set K := (S.fixVec12 v).subgroupOf H
  have hK : ∀ h₁ h₂ : H, ((h₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((h₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ↔ h₁⁻¹ * h₂ ∈ K := fun h₁ h₂ => s12_apply_eq_iff
  let φ : H ⧸ K → {w : W // w ≠ 0} := Quotient.lift
    (fun h : H => ⟨⟨((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, hW h h.2⟩, fun e =>
      hv (((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).map_eq_zero_iff.mp (congrArg Subtype.val e))⟩)
    (fun h₁ h₂ hh => Subtype.ext (Subtype.ext
      ((hK h₁ h₂).mpr (QuotientGroup.leftRel_apply.mp hh))))
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y hxy => ?_, fun w => ?_⟩
    · induction x using QuotientGroup.induction_on with | H h₁ => ?_
      induction y using QuotientGroup.induction_on with | H h₂ => ?_
      exact QuotientGroup.eq.mpr ((hK h₁ h₂).mp
        (congrArg (fun w : {w : W // w ≠ 0} => ((w : W) : S.Qt)) hxy))
    · obtain ⟨h, hh, hhv⟩ := htr w w.1.2 fun e => w.2 (Subtype.ext e)
      exact ⟨QuotientGroup.mk ⟨h, hh⟩, Subtype.ext (Subtype.ext hhv)⟩
  have h1 : Nat.card (H ⧸ K) = Nat.card {w : W // w ≠ 0} := Nat.card_eq_of_bijective φ hφ
  have h2 : Nat.card {w : W // w ≠ 0} + 1 = Nat.card W := by
    have : Fintype W := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
    have : 0 < Fintype.card W := Fintype.card_pos
    omega
  have h3 : Nat.card W = 2 ^ finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  show Nat.card (H ⧸ K) + 1 = _
  omega

namespace PSLPair

variable {g : G} {t : S.O} (P : S.PSLPair g t)

theorem apply_c_of_commute {x : S.O} (hx : x ∈ S.Xbar12 g) (hxt : x * t = t * x) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c = P.c := by
  have hcT : P.c ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [P.commSpace_eq]
    exact subset_span (by simp)
  have hxc := apply_mem_commSpace_of_commute hxt hcT
  have hxW : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c ∈ P.W := P.apply_mem hx P.hc
  have hne : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]
    exact P.c_ne
  have hc'W : P.c' ∉ P.W := fun h => P.c'_ne (by
    have : P.c' ∈ P.W ⊓ P.W' := ⟨h, P.hc'⟩
    rwa [P.inf_eq, Submodule.mem_bot] at this)
  rcases P.eq_of_mem_commSpace hxc hne with h | h | h
  · exact h
  · exact absurd (h ▸ hxW) hc'W
  · exfalso
    apply hc'W
    have : P.c' = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c - P.c := by rw [h, add_sub_cancel_left]
    rw [this]
    exact P.W.sub_mem hxW P.hc

theorem apply_c'_of_commute {x : S.O} (hx : x ∈ S.Xbar12 g) (hxt : x * t = t * x) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c' = P.c' :=
  P.swap.apply_c_of_commute hx hxt

include P in
theorem normal (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width)
    (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    ∀ x ∈ S.Xbar12 g, x * t * x⁻¹ = t → x ∈ normalizer (S.Lbar g : Set S.O) := by
  intro x hx hxt
  have hxt' : x * t = t * x := by
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [hxt]
  rw [mem_normalizer_Lbar_iff_fix haQ hne hn (Xbar12_le_Mbar hx)]
  obtain ⟨-, u, -, -, hspan, -⟩ := S.timmesfeld_12_6 haQ hne ht htA
  have haT : S.cl (g * S.z * g⁻¹) ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [hspan]
    exact subset_span (by simp)
  rw [P.commSpace_eq, mem_span_pair_iff] at haT
  rcases haT with h | h | h | h <;> rw [h]
  · exact map_zero _
  · exact P.apply_c_of_commute hx hxt'
  · exact P.apply_c'_of_commute hx hxt'
  · rw [map_add, P.apply_c_of_commute hx hxt', P.apply_c'_of_commute hx hxt']

theorem Lbar_le_of_eq_c (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) (hS : S.S12Standing g t) (hred : ¬ S.IsReducible12)
    (ha : S.cl (g * S.z * g⁻¹) = P.c) :
    ∀ ℓ ∈ S.Lbar g, ℓ ∈ S.Xbar12 g ∧
      ∀ w ∈ P.W, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ span (ZMod 2) {P.c} := by
  have hLc : ∀ ℓ ∈ S.Lbar g, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c = P.c := fun ℓ hℓ => by
    rw [← ha]
    exact S.s12_Lbar_apply_cl_a haQ hℓ
  have hLX : ∀ ℓ ∈ S.Lbar g, ℓ ∈ S.Xbar12 g := fun ℓ hℓ =>
    P.mem_Xbar12_of_apply_mem hS hn hred (S.Lbar_le_Mbar g hℓ) P.hc P.c_ne
      ((hLc ℓ hℓ).symm ▸ P.hc)
  refine fun ℓ hℓ => ⟨hLX ℓ hℓ, ?_⟩
  refine psl_Lbar_comm_le_of_transitive haQ hne (H := P.W) (c := P.c)
    (L₁ := (S.Lbar g : Set S.O)) (K := {k | k ∈ S.Xbar12 g ∧
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c = P.c}) ?_ ?_ (fun ℓ hℓ => hℓ)
    (fun ℓ hℓ w hw => P.apply_mem (hLX ℓ hℓ) hw) hLc (fun k hk w hw => P.apply_mem hk.1 hw) ?_ ?_
    ℓ hℓ
  · intro h hh
    rw [ha]
    exact psl_polar_eq_zero_of_sing P.sing P.hc hh
  · intro v _ hv
    rwa [ha] at hv
  · rintro k ⟨hk, hkc⟩ ℓ' hℓ'
    have hkN : k ∈ normalizer (S.Lbar g : Set S.O) :=
      (mem_normalizer_Lbar_iff_fix haQ hne hn (Xbar12_le_Mbar hk)).mpr (ha ▸ hkc)
    exact (mem_normalizer_iff.mp hkN ℓ').mp hℓ'
  · intro h₁ hh₁ h₂ hh₂ hh₁c hh₂c
    obtain ⟨x, hx, hxc, hxh, -⟩ := P.exists_move le_rfl P.hc hh₁ hh₂ hh₁c hh₂c
    exact ⟨x, ⟨hx, hxc⟩, hxh⟩

theorem card_Lbar_le_of_eq_c (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) (hS : S.S12Standing g t) (hred : ¬ S.IsReducible12)
    (ha : S.cl (g * S.z * g⁻¹) = P.c) : Nat.card (S.Lbar g) ≤ 2 ^ (S.width - 1) := by
  have hL := P.Lbar_le_of_eq_c haQ hne hn hS hred ha
  have hLc : ∀ ℓ ∈ S.Lbar g, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c = P.c := fun ℓ hℓ => by
    rw [← ha]
    exact S.s12_Lbar_apply_cl_a haQ hℓ
  obtain ⟨e, he, he1⟩ := P.swap.exists_polar_c'
  change e ∈ P.W' at he
  change polar S.q e P.c = 1 at he1
  set U := P.W' ⊓ LinearMap.ker (S.q.polarBilin P.c)
  have hmem : ∀ ℓ : S.Lbar g, ((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e - e ∈ U := by
    intro ℓ
    refine ⟨P.W'.sub_mem (P.apply_mem' (hL ℓ ℓ.2).1 he) he, ?_⟩
    change (S.q.polarBilin P.c) (((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e - e) = 0
    rw [map_sub]
    change polar S.q P.c (((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e) - polar S.q P.c e = 0
    rw [← hLc ℓ ℓ.2, psl_polar_apply_apply, hLc ℓ ℓ.2, sub_self]
  let f : S.Lbar g → U := fun ℓ => ⟨_, hmem ℓ⟩
  have hf : Function.Injective f := by
    intro ℓ₁ ℓ₂ h12
    have h12' : ((ℓ₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e = ((ℓ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e :=
      sub_left_injective (congrArg Subtype.val h12)
    set ℓ : S.O := (ℓ₁ : S.O)⁻¹ * ℓ₂
    have hℓ : ℓ ∈ S.Lbar g := (S.Lbar g).mul_mem ((S.Lbar g).inv_mem ℓ₁.2) ℓ₂.2
    have hℓe : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) e = e := by
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, ← h12', psl_inv_apply_apply]
    have hfix : ∀ w ∈ P.W, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
      intro w hw
      have h := (hL ℓ hℓ).2 w hw
      rw [mem_span_singleton_iff] at h
      rcases h with h | h
      · exact sub_eq_zero.mp h
      · exfalso
        have hiso := psl_polar_apply_apply ℓ w e
        rw [hℓe, sub_eq_iff_eq_add.mp h, polar_add_left, polar_comm S.q P.c e, he1] at hiso
        exact one_ne_zero (add_eq_right.mp hiso)
    have h1 := P.eq_one (hL ℓ hℓ).1 hfix
    apply Subtype.ext
    calc (ℓ₁ : S.O) = ℓ₁ * ℓ := by rw [h1, mul_one]
      _ = ℓ₂ := by rw [mul_inv_cancel_left]
  have hlt : U < P.W' := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    have : e ∈ U := h ▸ he
    have h2 : polar S.q P.c e = 0 := this.2
    rw [polar_comm S.q, he1] at h2
    exact one_ne_zero h2
  have hfin := Submodule.finrank_lt_finrank_of_lt hlt
  rw [P.dim'] at hfin
  calc Nat.card (S.Lbar g) ≤ Nat.card U := Nat.card_le_card_of_injective f hf
    _ = 2 ^ finrank (ZMod 2) U := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    _ ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem relIndex_normalizer_of_eq_c (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) (ha : S.cl (g * S.z * g⁻¹) = P.c) :
    (normalizer (S.Lbar g : Set S.O)).relIndex (S.Xbar12 g) = 2 ^ S.width - 1 := by
  have hsub : (normalizer (S.Lbar g : Set S.O)).subgroupOf (S.Xbar12 g) =
      (S.fixVec12 P.c).subgroupOf (S.Xbar12 g) := by
    ext x
    rw [mem_subgroupOf, mem_subgroupOf, ← ha]
    exact mem_normalizer_Lbar_iff_fix haQ hne hn (Xbar12_le_Mbar x.2)
  have h := psl_relIndex_fixVec12_add_one (S.Xbar12 g) P.c_ne (W := P.W)
    (fun x hx => P.apply_mem hx P.hc) fun w hw hw0 => P.exists_apply_eq P.hc hw P.c_ne hw0
  rw [P.dim] at h
  rw [Subgroup.relIndex, hsub, ← Subgroup.relIndex]
  omega

theorem meet_of_eq_c (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (ha : S.cl (g * S.z * g⁻¹) = P.c) :
    ∀ x ∈ S.Xbar12 g, (S.Lbar g).map (MulAut.conj x).toMonoidHom ⊓
      normalizer (S.Lbar g : Set S.O) ≠ ⊥ := by
  intro x hx
  set y := ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c
  have hNiff : ∀ k ∈ S.Mbar, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c = P.c →
      k ∈ normalizer (S.Lbar g : Set S.O) := fun k hk hkc =>
    (mem_normalizer_Lbar_iff_fix haQ hne hn hk).mpr (ha ▸ hkc)
  have hℓ : ∃ ℓ ∈ S.Lbar g, ℓ ≠ 1 ∧ (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) y = y := by
    obtain ⟨a, haW, ha0, hca, hya⟩ :=
      psl_exists_ne_zero_polar_eq_zero (U := P.W') (by rw [P.dim']; omega) P.c y
    have hta : t ≠ 1 := fun h => htA.2.1 (by rw [h]; rfl)
    by_cases hac : a = P.c'
    · refine ⟨t, ht, hta, ?_⟩
      rw [P.tW y (P.apply_mem ((S.Xbar12 g).inv_mem hx) P.hc), ← hac, hya, zero_smul,
        add_zero]
    · have hnot : P.c' ∉ span (ZMod 2) {a - P.c'} := by
        rw [mem_span_singleton_iff]
        rintro (h | h)
        · exact P.c'_ne h
        · apply ha0
          have : a = P.c' + P.c' := by
            calc a = (a - P.c') + P.c' := (sub_add_cancel a P.c').symm
              _ = P.c' + P.c' := by rw [← h]
          rw [this, self_add_self]
      obtain ⟨ψ, hψ, hψ1⟩ := exists_functional hnot
      obtain ⟨k, hk, hkw⟩ := P.lift' ψ (a - P.c') (P.W'.sub_mem haW P.hc')
        (hψ _ (mem_span_singleton_self _))
      have hkc' : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c' = a := by
        rw [hkw P.c' P.hc', hψ1, one_smul, add_sub_cancel]
      have hkc : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c = P.c := by
        refine P.swap.apply_c'_eq hk fun w hw => ?_
        change polar S.q ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) w) P.c = polar S.q w P.c
        change w ∈ P.W' at hw
        rw [hkw w hw, polar_add_left, polar_smul_left, polar_sub_left, polar_comm S.q a P.c,
          hca, polar_comm S.q P.c' P.c, P.polar_c_c', sub_zero, smul_zero, add_zero]
      refine ⟨k * t * k⁻¹, ?_, ?_, ?_⟩
      · exact (mem_normalizer_iff.mp (hNiff k (Xbar12_le_Mbar hk) hkc) t).mp ht
      · intro h
        apply hta
        calc t = k⁻¹ * (k * t * k⁻¹) * k := by group
          _ = 1 := by rw [h, mul_one, inv_mul_cancel]
      · rw [P.conj_apply hk (P.apply_mem ((S.Xbar12 g).inv_mem hx) P.hc), hkc', hkc, hya,
          zero_smul, add_zero]
  obtain ⟨ℓ, hℓL, hℓ1, hℓy⟩ := hℓ
  rw [Ne, Subgroup.eq_bot_iff_forall]
  push Not
  refine ⟨x * ℓ * x⁻¹, ⟨⟨ℓ, hℓL, rfl⟩, ?_⟩, ?_⟩
  · refine hNiff _ (S.Mbar.mul_mem (S.Mbar.mul_mem (Xbar12_le_Mbar hx)
      (S.Lbar_le_Mbar g hℓL)) (S.Mbar.inv_mem (Xbar12_le_Mbar hx))) ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hℓy,
      psl_apply_inv_apply]
  · intro h
    apply hℓ1
    calc ℓ = x⁻¹ * (x * ℓ * x⁻¹) * x := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]

theorem case1_of_eq_c (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 4 ≤ S.width) (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hS : S.S12Standing g t) (hred : ¬ S.IsReducible12) (ha : S.cl (g * S.z * g⁻¹) = P.c) :
    S.S12Case1 g t where
  normal := P.normal haQ hne (by omega) ht htA
  index := P.relIndex_le_two hS (by omega)
  model := ⟨S.width, by omega, P.model, Or.inl ⟨le_antisymm
    (P.card_Lbar_le_of_eq_c haQ hne (by omega) hS hred ha) (S.card_Lbar_ge haQ hne),
    P.relIndex_normalizer_of_eq_c haQ hne (by omega) ha,
    P.meet_of_eq_c haQ hne (by omega) ht htA ha⟩⟩

end PSLPair

end Setting

end CFSG.LargeExtraspecial
