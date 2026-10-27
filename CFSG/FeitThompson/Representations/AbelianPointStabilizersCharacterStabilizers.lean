module

public import CFSG.FeitThompson.Representations.BrauerPermutationLemma
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
import CFSG.FeitThompson.Foundations.OrbitStabilizerIndex
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup MulAction

variable {L : Type*} [Group L]

theorem mem_inertiaGroup_iff_forall_conj {H : Subgroup L} [H.Normal] {lam : H → ℂ} {u : L} :
    u ∈ inertiaGroup H lam ↔ ∀ h : H, lam (MulAut.conjNormal u⁻¹ h) = lam h := by
  rw [mem_inertiaGroup, funext_iff]
  exact forall_congr' fun h => by rw [NormalInduction.conjClassFun_apply]

theorem eq_one_of_mul_comm_of_notMem {H U U₁ : Subgroup L}
    (hC : ∀ h ∈ H, h ≠ 1 → U ⊓ centralizer {h} ≤ U₁)
    {u : L} (huU : u ∈ U) (hu₁ : u ∉ U₁) {h : L} (hh : h ∈ H) (hcomm : h * u = u * h) :
    h = 1 := by
  by_contra hne
  exact hu₁ (hC h hh hne (mem_inf.mpr ⟨huU, mem_centralizer_singleton_iff.mpr hcomm.symm⟩))

theorem exists_conj_eq_mul_right {H : Subgroup L} [H.Normal] [Finite H] {u : L}
    (hu : ∀ h ∈ H, h * u = u * h → h = 1) {t : L} (ht : t ∈ H) :
    ∃ s ∈ H, u * t = s * u * s⁻¹ := by
  classical
  set S : Subgroup (ConjAct L) := H.map ConjAct.toConjAct.toMonoidHom with hS
  have eHS : (H : Type _) ≃ (S : Type _) :=
    (Subgroup.equivMapOfInjective H _ ConjAct.toConjAct.injective).toEquiv
  have : Finite (S : Type _) := Finite.of_equiv _ eHS
  have hmemS : ∀ x : ConjAct L, x ∈ S ↔ ConjAct.ofConjAct x ∈ H := fun x => by
    rw [hS, Subgroup.mem_map]
    exact ⟨fun ⟨h, hh, hx⟩ => by simpa [← hx] using hh,
      fun hx => ⟨ConjAct.ofConjAct x, hx, by simp⟩⟩
  have hsmul : ∀ (c : ConjAct L) (hc : c ∈ S),
      (⟨c, hc⟩ : S) • u = ConjAct.ofConjAct c * u * (ConjAct.ofConjAct c)⁻¹ := fun c hc => by
    rw [Subgroup.smul_def, ConjAct.smul_def]
  have hstab : Nat.card (stabilizer S u) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    have key : ∀ x : stabilizer S u, (x : S) = 1 := by
      intro x
      have h1 : ConjAct.ofConjAct ((x : S) : ConjAct L) * u
          * (ConjAct.ofConjAct ((x : S) : ConjAct L))⁻¹ = u := by
        rw [← hsmul _ (x : S).2]; exact x.2
      have h2 := hu _ ((hmemS _).mp (x : S).2) (mul_inv_eq_iff_eq_mul.mp h1)
      exact Subtype.ext (by simpa using congrArg ConjAct.toConjAct h2)
    exact ⟨⟨fun a b => Subtype.ext ((key a).trans (key b).symm)⟩, ⟨1⟩⟩
  have hcard : Nat.card (orbit S u) = Nat.card (H : Type _) := by
    have h := natCard_orbit_mul_natCard_stabilizer (G := (S : Type _)) (X := L) u
    rw [hstab, mul_one] at h
    rw [h, Nat.card_congr eHS]
  have hinj : Function.Injective fun h : L => h * u := fun a b hab => by simpa using hab
  set T : Set L := (fun h : L => h * u) '' (H : Set L) with hT
  have hTcard : Nat.card T = Nat.card (H : Type _) :=
    (Nat.card_congr (Equiv.Set.image _ (H : Set L) hinj)).symm
  have hTfin : T.Finite := Set.Finite.image _ (Set.toFinite _)
  have hsub : orbit S u ⊆ T := by
    rintro x ⟨⟨c, hc⟩, rfl⟩
    refine ⟨ConjAct.ofConjAct c * (u * (ConjAct.ofConjAct c)⁻¹ * u⁻¹), ?_, ?_⟩
    · exact mul_mem ((hmemS c).mp hc)
        (by simpa [mul_assoc] using ‹H.Normal›.conj_mem _ (inv_mem ((hmemS c).mp hc)) u)
    · change ConjAct.ofConjAct c * (u * (ConjAct.ofConjAct c)⁻¹ * u⁻¹) * u = (⟨c, hc⟩ : S) • u
      rw [hsmul c hc]; group
  have hEq : orbit S u = T := hTfin.eq_of_subset_of_card_le hsub (by rw [hcard, hTcard])
  have hut : u * t ∈ T := ⟨u * t * u⁻¹, ‹H.Normal›.conj_mem t ht u, by group⟩
  obtain ⟨⟨c, hc⟩, hcu⟩ := hEq ▸ hut
  have hcu' : (⟨c, hc⟩ : S) • u = u * t := hcu
  exact ⟨ConjAct.ofConjAct c, (hmemS c).mp hc, by rw [← hcu', hsmul c hc]⟩

theorem card_fixed_conjClassesAut_eq_one {H U U₁ : Subgroup L} [H.Normal] [Finite H]
    (hC : ∀ h ∈ H, h ≠ 1 → U ⊓ centralizer {h} ≤ U₁)
    {u : L} (huU : u ∈ U) (hu₁ : u ∉ U₁) :
    Nat.card {K : ConjClasses H // conjClassesAut (MulAut.conjNormal (H := H) u⁻¹) K = K} = 1 := by
  have hcent : ∀ h ∈ H, h * u = u * h → h = 1 := fun h hh hcomm =>
    eq_one_of_mul_comm_of_notMem hC huU hu₁ hh hcomm
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨ConjClasses.mk 1, by simp⟩, ?_⟩
  rintro ⟨K, hK⟩
  obtain ⟨h, rfl⟩ := ConjClasses.mk_surjective K
  rw [conjClassesAut_mk] at hK
  obtain ⟨c, hc⟩ := isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.1 hK)
  have hcL : (c : L) * (u⁻¹ * (h : L) * u) * (c : L)⁻¹ = (h : L) := by
    have := congrArg (fun x : H => (x : L)) hc
    simpa [MulAut.conjNormal_apply, mul_assoc] using this
  have hv0 : (u * (c : L)⁻¹)⁻¹ * (h : L) * (u * (c : L)⁻¹) = (h : L) := by
    rw [show (u * (c : L)⁻¹)⁻¹ * (h : L) * (u * (c : L)⁻¹)
      = (c : L) * (u⁻¹ * (h : L) * u) * (c : L)⁻¹ by group]
    exact hcL
  have hv : (h : L) * (u * (c : L)⁻¹) = (u * (c : L)⁻¹) * (h : L) :=
    calc (h : L) * (u * (c : L)⁻¹)
        = (u * (c : L)⁻¹) * ((u * (c : L)⁻¹)⁻¹ * (h : L) * (u * (c : L)⁻¹)) := by group
      _ = (u * (c : L)⁻¹) * (h : L) := by rw [hv0]
  obtain ⟨s, hs, hus⟩ := exists_conj_eq_mul_right (H := H) hcent (inv_mem c.2)
  rw [hus] at hv
  have hsh : s⁻¹ * (h : L) * s * u = u * (s⁻¹ * (h : L) * s) :=
    calc s⁻¹ * (h : L) * s * u = s⁻¹ * ((h : L) * (s * u * s⁻¹)) * s := by group
      _ = s⁻¹ * ((s * u * s⁻¹) * (h : L)) * s := by rw [hv]
      _ = u * (s⁻¹ * (h : L) * s) := by group
  have h1 : s⁻¹ * (h : L) * s = 1 := eq_one_of_mul_comm_of_notMem hC huU hu₁
    (mul_mem (mul_mem (inv_mem hs) h.2) hs) hsh
  have hh1 : (h : L) = 1 := by
    calc (h : L) = s * (s⁻¹ * (h : L) * s) * s⁻¹ := by group
      _ = 1 := by rw [h1]; group
  exact Subtype.ext (congrArg ConjClasses.mk (Subtype.ext hh1))

theorem eq_one_of_mem_inertiaGroup {H U U₁ : Subgroup L} [H.Normal] [Finite H]
    (hC : ∀ h ∈ H, h ≠ 1 → U ⊓ centralizer {h} ≤ U₁)
    {u : L} (huU : u ∈ U) (hu₁ : u ∉ U₁) {lam : H → ℂ} (hlam : lam ∈ Irr H)
    (hfix : u ∈ inertiaGroup H lam) : lam = 1 := by
  set α : MulAut H := MulAut.conjNormal u⁻¹ with hα
  have hcard : Nat.card {ψ : Irr H // irrAut α ψ = ψ} = 1 := by
    rw [card_fixed_irrAut_eq_card_fixed_conjClassesAut α]
    exact card_fixed_conjClassesAut_eq_one hC huU hu₁
  have hsub : Subsingleton {ψ : Irr H // irrAut α ψ = ψ} :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  have hone : irrAut α ⟨(1 : H → ℂ), one_mem_Irr⟩ = ⟨(1 : H → ℂ), one_mem_Irr⟩ :=
    (irrAut_eq_self_iff α _).2 fun _ => rfl
  have hfix' : irrAut α (⟨lam, hlam⟩ : Irr H) = ⟨lam, hlam⟩ :=
    (irrAut_eq_self_iff α _).2 (mem_inertiaGroup_iff_forall_conj.mp hfix)
  exact congrArg (fun x => ((x.1 : Irr H) : H → ℂ))
    (hsub.allEq ⟨⟨lam, hlam⟩, hfix'⟩ ⟨⟨(1 : H → ℂ), one_mem_Irr⟩, hone⟩)

theorem inf_inertiaGroup_le_of_centralizer_le {H U U₁ : Subgroup L} [H.Normal] [Finite H]
    (hC : ∀ h ∈ H, h ≠ 1 → U ⊓ centralizer {h} ≤ U₁)
    {lam : H → ℂ} (hlam : lam ∈ Irr H) (hne : lam ≠ 1) :
    U ⊓ inertiaGroup H lam ≤ U₁ := by
  intro u hu
  by_contra hu₁
  obtain ⟨huU, huI⟩ := mem_inf.mp hu
  exact hne (eq_one_of_mem_inertiaGroup hC huU hu₁ hlam huI)

theorem setOf_fixes_subset_of_centralizer_le {H U U₁ : Subgroup L} [H.Normal] [Finite H]
    (hC : ∀ h ∈ H, h ≠ 1 → U ⊓ centralizer {h} ≤ U₁)
    {lam : H → ℂ} (hlam : lam ∈ Irr H) (hne : lam ≠ 1) :
    {u : L | u ∈ U ∧ ∀ h : H, lam (MulAut.conjNormal u⁻¹ h) = lam h} ⊆ (U₁ : Set L) := by
  rintro u ⟨huU, hfix⟩
  exact inf_inertiaGroup_le_of_centralizer_le hC hlam hne
    (mem_inf.mpr ⟨huU, mem_inertiaGroup_iff_forall_conj.mpr hfix⟩)

theorem isMulCommutative_inf_inertiaGroup {H U U₁ : Subgroup L} [H.Normal] [Finite H]
    [IsMulCommutative (U₁ : Type _)]
    (hC : ∀ h ∈ H, h ≠ 1 → U ⊓ centralizer {h} ≤ U₁)
    {lam : H → ℂ} (hlam : lam ∈ Irr H) (hne : lam ≠ 1) :
    IsMulCommutative ((U ⊓ inertiaGroup H lam : Subgroup L) : Type _) :=
  isMulCommutative_iff_of_setLike.mpr fun _ ha _ hb =>
    setLike_mul_comm (s := U₁) (inf_inertiaGroup_le_of_centralizer_le hC hlam hne ha)
      (inf_inertiaGroup_le_of_centralizer_le hC hlam hne hb)

end CFSG.FeitThompson
