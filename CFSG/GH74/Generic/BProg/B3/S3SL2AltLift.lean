module

public import CFSG.GH74.Generic.BProg.B3.S3SL2AltSetup
public import CFSG.GH74.Generic.BProg.B3.S3SL2AltX

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.Blueprint Subgroup Equiv Equiv.Perm
open scoped commutatorElement

namespace S3SL2AltLift

open S3SL2AltX

variable {Y : Type} [Group Y] {H : Subgroup Y} {s : Y} {hsN : s ∈ normalizer (H : Set Y)}

@[expose] def Xt (S : AltSetting H 9 hsN) (a b : Fin 9) : Subgroup ↥H := (Xs a b).comap S.π

@[expose] def Dsub (S : AltSetting H 9 hsN) (a b : Fin 9) : Subgroup ↥H := ⁅Xt S a b, Xt S a b⁆

theorem Xs_perfect {a b : Fin 9} (hab : a ≠ b) : ⁅Xs a b, Xs a b⁆ = Xs a b := by
  have := Xs_isSimple hab
  have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := Xs a b)
    (Xs_nonabelian hab)).1
  exact Subgroup.isPerfect_iff.mp hq.1

theorem Xs_quasisimple {a b : Fin 9} (hab : a ≠ b) : CFSG.IsQuasisimple ↥(Xs a b) := by
  have := Xs_isSimple hab
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := Xs a b) (Xs_nonabelian hab)).1

variable (S : AltSetting H 9 hsN) {a b : Fin 9}

theorem Dsub_map (hab : a ≠ b) : (Dsub S a b).map S.π = Xs a b := by
  unfold Dsub Xt
  have hXr : Xs a b ≤ S.π.range := fun x _ => S.surj x
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq, inf_eq_right.2 hXr, Xs_perfect hab]

theorem Dsub_le_Xt : Dsub S a b ≤ Xt S a b := Subgroup.commutator_le_self _

theorem Dsub_perfect (hab : a ≠ b) : ⁅Dsub S a b, Dsub S a b⁆ = Dsub S a b := by
  have hker : S.π.ker ≤ center ↥H := S.ker_eq.le
  have hXt : Xt S a b = Dsub S a b ⊔ S.π.ker := by
    show (Xs a b).comap S.π = _
    rw [← Subgroup.comap_map_eq, Dsub_map S hab]
  have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central
    (Dsub S a b) S.π.ker hker
  rw [← hXt] at h
  exact h.symm

theorem Dsub_fixed (hab : a ≠ b) (hσ : S.σ = swap a b) : ∀ k ∈ Dsub S a b, S3SL2Basic.actH H hsN k = k := by
  refine S45.LAlt.fixed_of_perfect (S3SL2Basic.actH H hsN) S.π S.ker_eq.le (Dsub_perfect S hab) ?_
  intro k hk
  have hkX : S.π k ∈ Xs a b := Dsub_le_Xt S hk
  apply Subtype.ext
  rw [S.act k, hσ]
  have hc := Xs_comm_swap hkX
  calc swap a b * (S.π k : Perm (Fin 9)) * (swap a b)⁻¹
      = (S.π k : Perm (Fin 9)) * swap a b * (swap a b)⁻¹ := by rw [← hc]
    _ = (S.π k : Perm (Fin 9)) := by group

theorem Xt_conj (hab : a ≠ b) (hσ : S.σ = swap a b) {g : ↥H} (hg : S3SL2Basic.actH H hsN g = g) :
    ∀ u ∈ Xt S a b, g * u * g⁻¹ ∈ Xt S a b := by
  intro u hu
  have hgs : s * (g : Y) = (g : Y) * s := (S3SL2Basic.actH_eq_iff H hsN g).1 hg
  have hc := S.commute_of_centralizes hgs
  rw [hσ] at hc
  have hc' : ((S.π g : alternatingGroup (Fin 9)) : Perm (Fin 9)) * swap a b =
      swap a b * ((S.π g : alternatingGroup (Fin 9)) : Perm (Fin 9)) := hc.symm
  have := Xs_normalized hc' hab hu
  show S.π (g * u * g⁻¹) ∈ Xs a b
  rw [map_mul, map_mul, map_inv]
  exact this

theorem Dsub_conj (hab : a ≠ b) (hσ : S.σ = swap a b) {g : ↥H} (hg : S3SL2Basic.actH H hsN g = g) :
    ∀ d ∈ Dsub S a b, g * d * g⁻¹ ∈ Dsub S a b := by
  intro d hd
  have h1 : (Dsub S a b).map (MulAut.conj g).toMonoidHom ≤ Dsub S a b := by
    unfold Dsub
    rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_ <;>
    · rintro _ ⟨u, hu, rfl⟩
      exact Xt_conj S hab hσ hg u hu
  exact h1 ⟨d, hd, rfl⟩

theorem Dsub_quasisimple (hab : a ≠ b) : CFSG.IsQuasisimple ↥(Dsub S a b) := by
  have hP : Group.IsPerfect ↥(Dsub S a b) := Subgroup.isPerfect_iff.mpr (Dsub_perfect S hab)
  let f : ↥(Dsub S a b) →* ↥(Xs a b) :=
    (S.π.comp (Dsub S a b).subtype).codRestrict (Xs a b) (fun k => Dsub_le_Xt S k.2)
  have hf : Function.Surjective f := by
    intro x
    have : (x : alternatingGroup (Fin 9)) ∈ (Dsub S a b).map S.π := by
      rw [Dsub_map S hab]; exact x.2
    obtain ⟨k, hk, hkx⟩ := this
    exact ⟨⟨k, hk⟩, Subtype.ext hkx⟩
  have hker : f.ker ≤ center ↥(Dsub S a b) := by
    intro k hk
    have h1 : S.π (k : ↥H) = 1 := by
      have h := MonoidHom.mem_ker.1 hk
      have h' : ((f k : ↥(Xs a b)) : alternatingGroup (Fin 9)) = 1 := congrArg Subtype.val h
      exact h'
    have h2 : (k : ↥H) ∈ center ↥H := (S.mem_ker_iff _).1 h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro d
    exact Subtype.ext (h2 d)
  exact (CFSG.LocalCores.isQuasisimple_iff_of_surjective hP f hf hker).2
    (Xs_quasisimple hab)


theorem Dsub_center_sq (hab : a ≠ b) (hZ : Nat.card (center ↥H) = 2) {z : ↥H} (hz : z ∈ Dsub S a b)
    (hcomm : ∀ d ∈ Dsub S a b, z * d = d * z) : z ^ 2 = 1 := by
  have := Xs_isSimple hab
  have hXz : center ↥(Xs a b) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := Xs a b) (Xs_nonabelian hab)).2
  have hπz : S.π z ∈ Xs a b := Dsub_le_Xt S hz
  have hc : (⟨S.π z, hπz⟩ : ↥(Xs a b)) ∈ center ↥(Xs a b) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have : (y : alternatingGroup (Fin 9)) ∈ (Dsub S a b).map S.π := by
      rw [Dsub_map S hab]; exact y.2
    obtain ⟨d, hd, hdy⟩ := this
    apply Subtype.ext
    show (y : alternatingGroup (Fin 9)) * S.π z = S.π z * y
    rw [← hdy, ← map_mul, ← map_mul, hcomm d hd]
  rw [hXz, Subgroup.mem_bot] at hc
  have h1 : S.π z = 1 := congrArg Subtype.val hc
  have h2 : z ∈ center ↥H := (S.mem_ker_iff z).1 h1
  have h3 : (⟨z, h2⟩ : ↥(center ↥H)) ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ↥(center ↥H)) (x := ⟨z, h2⟩)
    rwa [hZ] at this
  exact congrArg Subtype.val h3

end S3SL2AltLift

end CFSG.GH74.Generic.BProg.B3
