module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128CentW
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Nat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

structure Sec128Two (V V1 V2 X : Subgroup G) (phi1 phi2 : (Fin 5 → ZMod 2) → G) : Prop where
  comm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x
  sup : V1 ⊔ V2 = V
  inf : V1 ⊓ V2 = ⊥
  c1 : Sec127NatCoord V1 X phi1
  c2 : Sec127NatCoord V2 X phi2

theorem sec128_mem_sup {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
        refine ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, ?_⟩
        have h : b1 * a2 = a2 * b1 := (hAB a2 ha2 b1 hb1).symm
        calc a1 * b1 * (a2 * b2) = a1 * (b1 * a2) * b2 := by group
          _ = a1 * (a2 * b1) * b2 := by rw [h]
          _ = a1 * a2 * (b1 * b2) := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have hc : Commute a b := hAB a ha b hb
        rw [mul_inv_rev]
        exact hc.inv_inv.eq.symm }
  have hle : A ⊔ B ≤ P :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  exact hle hg

variable {V V1 V2 X : Subgroup G} {phi1 phi2 : (Fin 5 → ZMod 2) → G}

@[expose] def sec128Psi (phi1 phi2 : (Fin 5 → ZMod 2) → G) (p : EvW × EvW) : G :=
  phi1 p.1.1 * phi2 p.2.1

namespace Sec128Two

theorem le1 (hd : Sec128Two V V1 V2 X phi1 phi2) : V1 ≤ V := hd.sup ▸ le_sup_left

theorem le2 (hd : Sec128Two V V1 V2 X phi1 phi2) : V2 ≤ V := hd.sup ▸ le_sup_right

theorem mem1 (hd : Sec128Two V V1 V2 X phi1 phi2) (a : EvW) : phi1 a.1 ∈ V :=
  hd.le1 (hd.c1.mem _ a.2)

theorem mem2 (hd : Sec128Two V V1 V2 X phi1 phi2) (b : EvW) : phi2 b.1 ∈ V :=
  hd.le2 (hd.c2.mem _ b.2)

theorem psi_mem (hd : Sec128Two V V1 V2 X phi1 phi2) (p : EvW × EvW) :
    sec128Psi phi1 phi2 p ∈ V :=
  V.mul_mem (hd.mem1 p.1) (hd.mem2 p.2)

theorem psi_add (hd : Sec128Two V V1 V2 X phi1 phi2) (p q : EvW × EvW) :
    sec128Psi phi1 phi2 (p + q) = sec128Psi phi1 phi2 p * sec128Psi phi1 phi2 q := by
  have h1 : phi1 (p.1.1 + q.1.1) = phi1 p.1.1 * phi1 q.1.1 := hd.c1.mul _ _ p.1.2 q.1.2
  have h2 : phi2 (p.2.1 + q.2.1) = phi2 p.2.1 * phi2 q.2.1 := hd.c2.mul _ _ p.2.2 q.2.2
  have hc : phi2 p.2.1 * phi1 q.1.1 = phi1 q.1.1 * phi2 p.2.1 :=
    hd.comm _ (hd.mem2 p.2) _ (hd.mem1 q.1)
  show phi1 (p.1.1 + q.1.1) * phi2 (p.2.1 + q.2.1) = _
  rw [h1, h2]
  unfold sec128Psi
  calc phi1 p.1.1 * phi1 q.1.1 * (phi2 p.2.1 * phi2 q.2.1)
      = phi1 p.1.1 * (phi1 q.1.1 * phi2 p.2.1) * phi2 q.2.1 := by group
    _ = phi1 p.1.1 * (phi2 p.2.1 * phi1 q.1.1) * phi2 q.2.1 := by rw [hc]
    _ = phi1 p.1.1 * phi2 p.2.1 * (phi1 q.1.1 * phi2 q.2.1) := by group

theorem psi_inj (hd : Sec128Two V V1 V2 X phi1 phi2) {p q : EvW × EvW}
    (h : sec128Psi phi1 phi2 p = sec128Psi phi1 phi2 q) : p = q := by
  have hA : phi1 p.1.1 ∈ V1 := hd.c1.mem _ p.1.2
  have hA' : phi1 q.1.1 ∈ V1 := hd.c1.mem _ q.1.2
  have hB : phi2 p.2.1 ∈ V2 := hd.c2.mem _ p.2.2
  have hB' : phi2 q.2.1 ∈ V2 := hd.c2.mem _ q.2.2
  have h' : phi1 p.1.1 * phi2 p.2.1 = phi1 q.1.1 * phi2 q.2.1 := h
  have e : (phi1 q.1.1)⁻¹ * phi1 p.1.1 = phi2 q.2.1 * (phi2 p.2.1)⁻¹ := by
    calc (phi1 q.1.1)⁻¹ * phi1 p.1.1
        = (phi1 q.1.1)⁻¹ * (phi1 p.1.1 * phi2 p.2.1) * (phi2 p.2.1)⁻¹ := by group
      _ = (phi1 q.1.1)⁻¹ * (phi1 q.1.1 * phi2 q.2.1) * (phi2 p.2.1)⁻¹ := by rw [h']
      _ = phi2 q.2.1 * (phi2 p.2.1)⁻¹ := by group
  have hmem : (phi1 q.1.1)⁻¹ * phi1 p.1.1 ∈ V1 ⊓ V2 :=
    ⟨V1.mul_mem (V1.inv_mem hA') hA, e ▸ V2.mul_mem hB' (V2.inv_mem hB)⟩
  rw [hd.inf, Subgroup.mem_bot] at hmem
  have hA1 : phi1 p.1.1 = phi1 q.1.1 := (inv_mul_eq_one.mp hmem).symm
  have hB1 : phi2 p.2.1 = phi2 q.2.1 := by
    rw [hmem] at e
    exact (mul_inv_eq_one.mp e.symm).symm
  exact Prod.ext (Subtype.ext ((hd.c1.eq_iff p.1.2 q.1.2).mp hA1))
    (Subtype.ext ((hd.c2.eq_iff p.2.2 q.2.2).mp hB1))

theorem psi_surj (hd : Sec128Two V V1 V2 X phi1 phi2) {x : G} (hx : x ∈ V) :
    ∃ p : EvW × EvW, sec128Psi phi1 phi2 p = x := by
  rw [← hd.sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    sec128_mem_sup (fun a ha b hb => hd.comm a (hd.le1 ha) b (hd.le2 hb)) hx
  obtain ⟨u, hu, rfl⟩ := hd.c1.surj a ha
  obtain ⟨w, hw, rfl⟩ := hd.c2.surj b hb
  exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), rfl⟩

@[expose] noncomputable def psiE (hd : Sec128Two V V1 V2 X phi1 phi2) : EvW × EvW ≃ ↥V :=
  Equiv.ofBijective (fun p => ⟨sec128Psi phi1 phi2 p, hd.psi_mem p⟩)
    ⟨fun _ _ h => hd.psi_inj (congrArg Subtype.val h), fun x => by
      obtain ⟨p, hp⟩ := hd.psi_surj x.2
      exact ⟨p, Subtype.ext hp⟩⟩

theorem psiE_val (hd : Sec128Two V V1 V2 X phi1 phi2) (p : EvW × EvW) :
    ((hd.psiE p : ↥V) : G) = phi1 p.1.1 * phi2 p.2.1 := rfl

theorem psiE_add (hd : Sec128Two V V1 V2 X phi1 phi2) (p q : EvW × EvW) :
    hd.psiE (p + q) = hd.psiE p * hd.psiE q :=
  Subtype.ext (hd.psi_add p q)

end Sec128Two

structure AddCoord (V : Subgroup G) where
  Ψ : EvW × EvW ≃ ↥V
  add : ∀ p q, Ψ (p + q) = Ψ p * Ψ q

@[expose] noncomputable def Sec128Two.coord (hd : Sec128Two V V1 V2 X phi1 phi2) : AddCoord V where
  Ψ := hd.psiE
  add p q := Subtype.ext (hd.psi_add p q)

theorem Sec128Two.coord_Ψ (hd : Sec128Two V V1 V2 X phi1 phi2) (p : EvW × EvW) :
    hd.coord.Ψ p = hd.psiE p := rfl

namespace AddCoord

variable (K : AddCoord V)

theorem zero : K.Ψ 0 = 1 := by
  have h := K.add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem symm_mul (x y : ↥V) : K.Ψ.symm (x * y) = K.Ψ.symm x + K.Ψ.symm y := by
  apply K.Ψ.injective
  rw [K.add, K.Ψ.apply_symm_apply, K.Ψ.apply_symm_apply, K.Ψ.apply_symm_apply]

noncomputable def kapW (c : MulAut ↥V) : EvW × EvW →+ EvW × EvW :=
  AddMonoidHom.mk' (fun p => K.Ψ.symm (c (K.Ψ p))) (fun p q => by
    rw [K.add, map_mul, K.symm_mul])

theorem kapW_spec (c : MulAut ↥V) (p : EvW × EvW) : K.Ψ (K.kapW c p) = c (K.Ψ p) :=
  K.Ψ.apply_symm_apply _

theorem kapW_mul (c c' : MulAut ↥V) : K.kapW (c * c') = (K.kapW c).comp (K.kapW c') := by
  refine AddMonoidHom.ext fun p => K.Ψ.injective ?_
  rw [AddMonoidHom.comp_apply, K.kapW_spec, K.kapW_spec, MulAut.mul_apply, K.kapW_spec]

theorem kapW_one : K.kapW 1 = AddMonoidHom.id (EvW × EvW) := by
  refine AddMonoidHom.ext fun p => K.Ψ.injective ?_
  rw [K.kapW_spec]
  rfl

theorem kapW_inj {c c' : MulAut ↥V} (h : K.kapW c = K.kapW c') : c = c' := by
  refine MulEquiv.ext fun v => ?_
  obtain ⟨p, rfl⟩ := K.Ψ.surjective v
  rw [← K.kapW_spec, ← K.kapW_spec, h]

theorem kapW_injective (c : MulAut ↥V) : Function.Injective (K.kapW c) := by
  intro p q h
  apply K.Ψ.injective
  apply c.injective
  rw [← K.kapW_spec, ← K.kapW_spec, h]

theorem kapW_comm (r : ↥X → EvW × EvW → EvW × EvW)
    (hr : ∀ (h : ↥X) (p : EvW × EvW), ((K.Ψ (r h p) : ↥V) : G) = (h : G) * (K.Ψ p : G) * (h : G)⁻¹)
    {c : MulAut ↥V} (hc : c ∈ Subgroup.centralizer (autIn X V : Set (MulAut ↥V))) (h : ↥X)
    (p : EvW × EvW) : K.kapW c (r h p) = r h (K.kapW c p) := by
  have hmapV : ∀ h : ↥X, ∀ x ∈ V, (h : G) * x * (h : G)⁻¹ ∈ V := by
    intro h x hx
    obtain ⟨q, hq⟩ := K.Ψ.surjective ⟨x, hx⟩
    have := hr h q
    rw [hq] at this
    rw [← this]
    exact (K.Ψ (r h q)).2
  have hN : (h : G) ∈ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hmapV h x hx, fun hx => ?_⟩
    have := hmapV ⟨(h : G)⁻¹, X.inv_mem h.2⟩ _ hx
    simpa [mul_assoc] using this
  set y : MulAut ↥V := V.normalizerMonoidHom ⟨(h : G), hN⟩ with hy
  have hyA : y ∈ autIn X V :=
    Subgroup.mem_map.mpr ⟨⟨(h : G), hN⟩, Subgroup.mem_subgroupOf.mpr h.2, rfl⟩
  have hcomm : y * c = c * y := Subgroup.mem_centralizer_iff.mp hc y hyA
  have hyv : ∀ v : ↥V, (y v : G) = (h : G) * (v : G) * (h : G)⁻¹ := fun v => rfl
  have hyΨ : ∀ p, y (K.Ψ p) = K.Ψ (r h p) := fun p => Subtype.ext (by rw [hyv, hr])
  apply K.Ψ.injective
  rw [K.kapW_spec, ← hyΨ, ← MulAut.mul_apply, ← hcomm, MulAut.mul_apply, ← K.kapW_spec, hyΨ]

end AddCoord

theorem sec128_exists_act {V1 X : Subgroup G} {phi : (Fin 5 → ZMod 2) → G}
    (hc : Sec127NatCoord V1 X phi) :
    ∃ s : ↥X → EvW →+ EvW, (∀ (h : ↥X) (a : EvW), (h : G) * phi a.1 * (h : G)⁻¹ = phi (s h a).1) ∧
      OntoAct s := by
  choose σ hσA hσ using fun h : ↥X => hc.act h h.2
  refine ⟨fun h => permW (σ h), fun h a => hσ h a.1 a.2, fun τ hτ => ?_⟩
  obtain ⟨h, hh, hτh⟩ := hc.onto τ hτ
  refine ⟨⟨h, hh⟩, AddMonoidHom.ext fun a => Subtype.ext ?_⟩
  have e1 := hσ ⟨h, hh⟩ a.1 a.2
  have e2 := hτh a.1 a.2
  have e3 : phi (permVec (σ ⟨h, hh⟩) a.1) = phi (permVec τ a.1) := by rw [← e1, ← e2]
  exact (hc.eq_iff (sec128_isEven_permVec _ a.2) (sec128_isEven_permVec _ a.2)).mp e3

end CFSG.OddStandard.SmallF3.Omega
