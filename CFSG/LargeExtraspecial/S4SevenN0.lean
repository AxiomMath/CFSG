module

public import CFSG.LargeExtraspecial.S4FiveConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] noncomputable def N0bar (g : G) (t : S.O) : Subgroup S.O :=
  ⨆ (k : S.M) (_ : S.ρ k ∈ Rbar S g t), S.Lbar ((k : G) * g) ⊓ Nbar S g t

theorem N0bar_le_Nbar {t : S.O} : N0bar S g t ≤ Nbar S g t :=
  iSup₂_le fun _ _ => inf_le_right

theorem Lbar_mul_inf_Nbar_le_N0bar {t : S.O} {k : S.M} (hk : S.ρ k ∈ Rbar S g t) :
    S.Lbar ((k : G) * g) ⊓ Nbar S g t ≤ N0bar S g t :=
  le_iSup₂_of_le k hk le_rfl

theorem Lbar_inf_Nbar_le_N0bar {t : S.O} : S.Lbar g ⊓ Nbar S g t ≤ N0bar S g t := by
  have h := Lbar_mul_inf_Nbar_le_N0bar (S := S) (g := g) (t := t) (k := 1)
    (by rw [map_one]; exact one_mem _)
  simpa using h

theorem conj_mem_N0bar (haQ : g * S.z * g⁻¹ ∈ S.QG) {t r x : S.O} (hr : r ∈ Rbar S g t)
    (hx : x ∈ N0bar S g t) : r * x * r⁻¹ ∈ N0bar S g t := by
  obtain ⟨k', rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
  have hle : (N0bar S g t).map (MulAut.conj (S.ρ k')).toMonoidHom ≤ N0bar S g t := by
    rw [N0bar, Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hk => ?_
    rintro _ ⟨y, ⟨hyL, hyN⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hk'k : S.ρ (k' * k) ∈ Rbar S g t := by rw [map_mul]; exact mul_mem hr hk
    refine Lbar_mul_inf_Nbar_le_N0bar hk'k ⟨?_, conj_mem_Nbar haQ (commute_of_mem_Rbar haQ hr) hyN⟩
    have := conj_mem_Lbar_mul S k' hyL
    rwa [← mul_assoc, ← Subgroup.coe_mul] at this
  exact hle ⟨x, hx, rfl⟩

theorem normal_N0bar_subgroupOf (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} :
    ((N0bar S g t).subgroupOf (Rbar S g t)).Normal :=
  ⟨fun x hx r => by
    rw [mem_subgroupOf] at hx ⊢
    exact conj_mem_N0bar haQ r.2 hx⟩

theorem isPGroup_N0bar (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) :
    IsPGroup 2 (N0bar S g t) := by
  set N := Nbar S g t with hN
  set P : Subgroup S.O := (CFSG.pCore 2 N).map N.subtype with hP
  have hPp : IsPGroup 2 P := (CFSG.pCore_isPGroup).map _
  refine hPp.to_le (iSup₂_le fun k hk => ?_)
  intro x hx
  have hmem : (⟨x, hx.2⟩ : N) ∈ CFSG.pCore 2 N := by
    refine le_sSup (s := {K : Subgroup N | K.Normal ∧ IsPGroup 2 K})
      (a := (S.Lbar ((k : G) * g)).subgroupOf N) ⟨⟨fun y hy n => ?_⟩, ?_⟩ hx.1
    · rw [mem_subgroupOf] at hy ⊢
      have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
      have hnorm := Nbar_le_normalizer H.conj_mem H.conj_ne (Lbar_mul_mem_Dset htk) n.2
      exact (mem_normalizer_iff.mp hnorm _).mp hy
    · exact (isPGroup_Lbar S (H.mul k).conj_mem).comap_of_injective N.subtype N.subtype_injective
  exact ⟨_, hmem, rfl⟩

variable (S) in
@[expose] def DtEqConj (g : G) (t : S.O) : Prop :=
  ∀ h : S.M, t ∈ S.Lbar ((h : G) * g) →
    ∃ k : S.M, S.ρ k ∈ Rbar S g t ∧ S.Lbar ((h : G) * g) = S.Lbar ((k : G) * g)

theorem dtEqConj_of_forall_mem_orbitOf (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hD : ∀ (h : S.M) (hth : t ∈ S.Lbar ((h : G) * g)),
      bV hth ∈ orbitOf (RmodN S g t) (aV ht)) : DtEqConj S g t := by
  intro h hth
  obtain ⟨e, ⟨x, hx, hex⟩, hea⟩ := hD h hth
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hx)
  refine ⟨k, hx, ?_⟩
  have hcl : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) =
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_z S k H.conj_mem, ← coe_bV hth, ← hea, hex]
    rfl
  exact (Lbar_eq_of_cl_eq S (H.mul h).conj_mem (H.mul h).conj_ne (H.mul k).conj_mem hcl).symm

theorem commutator_mem_N0bar (H : Hyp4 S g) {t : S.O} (hD : DtEqConj S g t) {n r : S.O}
    (hn : n ∈ Nbar S g t) (hr : r ∈ Rbar S g t) : n * r * n⁻¹ * r⁻¹ ∈ N0bar S g t := by
  let K : Subgroup S.O :=
    { carrier := {r | r ∈ Rbar S g t ∧ ∀ n ∈ Nbar S g t, n * r * n⁻¹ * r⁻¹ ∈ N0bar S g t}
      mul_mem' := by
        rintro r₁ r₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
        refine ⟨mul_mem h₁ h₂, fun n hn => ?_⟩
        have e : n * (r₁ * r₂) * n⁻¹ * (r₁ * r₂)⁻¹ =
            (n * r₁ * n⁻¹ * r₁⁻¹) * (r₁ * (n * r₂ * n⁻¹ * r₂⁻¹) * r₁⁻¹) := by group
        rw [e]
        exact mul_mem (h₁' n hn) (conj_mem_N0bar H.conj_mem h₁ (h₂' n hn))
      one_mem' := ⟨one_mem _, fun n _ => by simp⟩
      inv_mem' := by
        rintro r ⟨h, h'⟩
        refine ⟨inv_mem h, fun n hn => ?_⟩
        have e : n * r⁻¹ * n⁻¹ * r⁻¹⁻¹ = r⁻¹ * (n * r * n⁻¹ * r⁻¹)⁻¹ * r⁻¹⁻¹ := by group
        rw [e]
        exact conj_mem_N0bar H.conj_mem (inv_mem h) (inv_mem (h' n hn)) }
  have hRK : Rbar S g t ≤ K := by
    refine sSup_le fun X hX => ?_
    obtain ⟨h, rfl, hth⟩ := hX
    intro y hy'
    have hy : y ∈ S.Lbar ((h : G) * g) := hy'
    have hyR := Lbar_mul_le_Rbar hth hy
    refine ⟨hyR, fun n hn => ?_⟩
    obtain ⟨k, hk, hhk⟩ := hD h hth
    have hnorm := Nbar_le_normalizer H.conj_mem H.conj_ne (Lbar_mul_mem_Dset hth) hn
    have h1 : y * n⁻¹ * y⁻¹ ∈ Nbar S g t := by
      obtain ⟨k', rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hyR)
      exact conj_mem_Nbar H.conj_mem (commute_of_mem_Rbar H.conj_mem hyR) (inv_mem hn)
    refine Lbar_mul_inf_Nbar_le_N0bar hk (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · rw [← hhk]
      have h2 : n * y * n⁻¹ ∈ S.Lbar ((h : G) * g) := (mem_normalizer_iff.mp hnorm y).mp hy
      exact mul_mem h2 (inv_mem hy)
    · have e : n * y * n⁻¹ * y⁻¹ = n * (y * n⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem hn h1
  exact (hRK hr).2 n hn

theorem Rbar_le_closure_conj {t : S.O} (hD : DtEqConj S g t) :
    Rbar S g t ≤ closure {u | ∃ r ∈ Rbar S g t, ∃ l ∈ S.Lbar g, u = r * l * r⁻¹} := by
  refine sSup_le fun X hX => ?_
  obtain ⟨h, rfl, hth⟩ := hX
  obtain ⟨k, hk, hhk⟩ := hD h hth
  rw [hhk, Lbar_mul S k g]
  rintro _ ⟨l, hl, rfl⟩
  exact subset_closure ⟨_, hk, l, hl, rfl⟩

theorem Lbar_conj_eq_of_le_normalizer (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) {k : S.M}
    (hle : S.Lbar ((k : G) * g) ≤ normalizer ((S.Lbar g ⊔ N0bar S g t : Subgroup S.O) :
      Set S.O)) : S.Lbar ((k : G) * g) = S.Lbar g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwc : WeaklyClosed S g := C.weaklyClosed
  have hP : IsPGroup 2 (S.Lbar g ⊔ N0bar S g t : Subgroup S.O) := by
    refine IsPGroup.to_sup_of_normal_right' (isPGroup_Lbar S H.conj_mem)
      (isPGroup_N0bar H ht) fun l hl => ?_
    rw [mem_normalizer_iff]
    intro x
    exact ⟨fun hx => conj_mem_N0bar H.conj_mem (Lbar_le_Rbar ht hl) hx, fun hx => by
      have := conj_mem_N0bar H.conj_mem (inv_mem (Lbar_le_Rbar ht hl)) hx
      rwa [show l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x by group] at this⟩
  have hT : IsPGroup 2 (S.Lbar ((k : G) * g) ⊔ (S.Lbar g ⊔ N0bar S g t) : Subgroup S.O) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_Lbar S (H.mul k).conj_mem) hP hle
  have hTM : S.Lbar ((k : G) * g) ⊔ (S.Lbar g ⊔ N0bar S g t) ≤ S.Mbar :=
    sup_le (S.Lbar_le_Mbar _) (sup_le (S.Lbar_le_Mbar _)
      (N0bar_le_Nbar.trans (Nbar_le_Rbar.trans Rbar_le_Mbar)))
  have hN := le_normalizer_of_weaklyClosed hwc hT hTM (le_sup_left.trans le_sup_right)
  exact hwc _ k.2 (le_sup_left.trans hN)

end CFSG.LargeExtraspecial.S4
