module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Def

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Equiv

@[expose] def sec11InU (w : Fin 6 → ZMod 2) : Prop :=
  w = 0 ∨ w = (fun _ => 1) ∨ w = Pi.single 0 1 + Pi.single 1 1 ∨
    w = Pi.single 0 1 + Pi.single 1 1 + (fun _ => 1)

instance (w : Fin 6 → ZMod 2) : Decidable (sec11InU w) := by
  unfold sec11InU
  infer_instance

theorem sec11_v4_card : sec11V4.card = 4 := by
  decide +kernel

theorem sec11_stab_pointwise : ∀ σ : Perm (Fin 6),
    (∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → v 0 = v 1 →
      permVec σ v = v ∨ permVec σ v = v + (fun _ => 1)) → σ = 1 ∨ σ = swap 0 1 := by
  decide +kernel

theorem sec11_v4_fixed : ∀ v : Fin 6 → ZMod 2,
    (∀ s ∈ sec11V4, permVec s v = v ∨ permVec s v = v + (fun _ => 1)) →
      v 2 = v 3 ∧ v 3 = v 4 ∧ v 4 = v 5 := by
  decide +kernel

@[expose] def sec11Cls (v : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  if v 0 = 1 then v + (fun _ => 1) else v

@[expose] def sec11L3 : Finset (Perm (Fin 6)) :=
  Finset.univ.filter fun σ => Equiv.Perm.sign σ = 1 ∧ (Finset.univ.filter fun i => σ i ≠ i).card ≤ 3

theorem sec11_cls_zero : ∀ v : Fin 6 → ZMod 2, sec11Cls v 0 = 0 := by
  decide +kernel

theorem sec11_orbit_ge7 : ∀ v : Fin 6 → ZMod 2, v ≠ 0 → v ≠ (fun _ => 1) →
    (∀ a, v ≠ Pi.single a 1 ∧ v ≠ Pi.single a 1 + (fun _ => 1)) →
    7 ≤ (sec11L3.image fun σ => sec11Cls (permVec σ v)).card := by
  decide +kernel

theorem sec11_trans : ∀ a k : Fin 6, ∃ σ : Perm (Fin 6), Equiv.Perm.sign σ = 1 ∧ σ a = k := by
  decide +kernel

theorem sec11_relabel_exists : ∀ a b : Fin 6, a ≠ b → ∃ π : Perm (Fin 6), π 0 = a ∧ π 1 = b := by
  decide +kernel

@[expose] def sec11Lam (c : Fin 5 → ZMod 2) (v : Fin 6 → ZMod 2) : ZMod 2 :=
  ∑ i : Fin 5, c i * v i.succ

@[expose] def sec11Uc (c : Fin 5 → ZMod 2) : Finset (Fin 6 → ZMod 2) :=
  Finset.univ.filter fun v => ∑ i, v i = 0 ∧ sec11Lam c v = 0 ∧ v 5 = 0

@[expose] def sec11Yc (c : Fin 5 → ZMod 2) : Finset (Perm (Fin 6)) :=
  Finset.univ.filter fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
    ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → sec11Lam c v = 0 → sec11InU (permVec σ v + v)

theorem sec11_c_good : ∀ c : Fin 5 → ZMod 2, c 0 = 0 → ∑ i, c i = 0 →
    32 ≤ (sec11Uc c).card * (sec11Yc c).card → c = ![0, 1, 1, 1, 1] := by
  decide +kernel

theorem sec11_Uc_good_card : (sec11Uc ![0, 1, 1, 1, 1]).card = 8 := by
  decide +kernel

theorem sec11_Yc_good_sub : ∀ σ ∈ sec11Yc ![0, 1, 1, 1, 1], σ ∈ sec11V4 := by
  decide +kernel

theorem sec11_lam_good : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 →
    (sec11Lam ![0, 1, 1, 1, 1] v = 0 ↔ v 0 = v 1) := by
  decide +kernel

theorem sec11_decomp : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 →
    v = ∑ i : Fin 5, v i.succ • (Pi.single 0 1 + Pi.single i.succ 1 : Fin 6 → ZMod 2) := by
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
