module

public import CFSG.GH74.GLS.C3.Layer2.L5C4c
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C4a
public import CFSG.GH74.GLS.C3.Layer2.L5C4Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C4Inputs
public import Certificates.Certificate5045
public import Certificates.Certificate5051
public import Certificates.Certificate5061
public import Certificates.Certificate5062
public import Certificates.Certificate5063
public import Certificates.Certificate5064

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Rec1

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem cr_cocycle : ∀ (j k : Fin 8) (r : Fin 16),
    xor16 (xor16 (cr j r) (Dg j (cr k r))) (cr (mulIdx j k) r) = 0 :=
  Certificates.certificate5061.1

theorem fix_im :
    ∀ z : Fin 16, xor16 z (Dg 1 z) = 0 → ∃ r : Fin 16, z = cr 1 r :=
  Certificates.certificate5061.2

theorem bool_adj1 (a1 a2 a3 b1 b2 b3 c1 c2 : Bool)
    (hA : xor a1 (xor a2 c1) = false) (hB : xor b1 (xor b2 c2) = false)
    (hb : xor c1 c2 = xor a3 b3) :
    xor (xor (xor a1 b1) a3) (xor (xor a2 b2) b3) = false := by
  revert a1 a2 a3 b1 b2 b3 c1 c2
  decide

theorem bool_adj2 (bj y bjk cj w cjk : Bool) (hz : xor (xor cj w) cjk = false) :
    xor bj (xor y bjk) = xor (xor bj cj) (xor (xor y w) (xor bjk cjk)) := by
  revert bj y bjk cj w cjk
  decide

theorem bool_adj3 (v v' b : Bool) : xor v (xor b (xor (xor v v') b)) = v' := by
  revert v v' b
  decide

structure RecData
    (S : Type*) [Group S] where
  ι : ↥T5 →* S
  ρ : S →* Perm (Fin 16)
  inj : Function.Injective ι
  act : ∀ (s : S) (i : Fin 16), s * ι (elT i) * s⁻¹ = ι (elT (ρ s i))
  mem : ∀ s, ρ s ∈ d8L
  surj : ∀ d ∈ d8L, ∃ s, ρ s = d
  ker : ∀ s, ρ s = 1 → ∃ i, s = ι (elT i)

theorem elT_xor
    (u v : Fin 16) : elT (xor16 u v) = elT u * elT v := Subtype.ext (el16_xor u v)

theorem elT_inj
    {u v : Fin 16} (h : elT u = elT v) : u = v := by
  have h1 : el16 u = el16 v := congrArg Subtype.val h
  have := congrArg idx16 h1
  rwa [idx16_el16, idx16_el16] at this

@[expose] def yT : ↥T5 := ⟨yy5, yy5_mem⟩

theorem yT_sq : yT * yT = 1 := Subtype.ext yy5_sq

theorem yT_act
    (i : Fin 16) : yT * elT i * yT⁻¹ = elT (yHat i) := by
  apply Subtype.ext
  have h : el16 (actF yy5 i) = yy5 * el16 i * yy5⁻¹ := by
    unfold actF
    exact el16_idx16 (T5_norm_Rm yy5_mem (el16_mem i))
  rw [actF_yy5] at h
  exact h.symm

theorem elT_comm
    (v i : Fin 16) : elT v * elT i * (elT v)⁻¹ = elT i := by
  apply Subtype.ext
  show el16 v * el16 i * (el16 v)⁻¹ = el16 i
  rw [Rm_comm _ (el16_mem v) _ (el16_mem i), mul_inv_cancel_right]

section RecData

variable
  {S : Type*} [Group S] (R : RecData S)

theorem RecData.rho_tr
    (v : Fin 16) : R.ρ (R.ι (elT v)) = 1 := by
  refine Equiv.ext (fun i => ?_)
  have h := R.act (R.ι (elT v)) i
  have h2 : R.ι (elT v) * R.ι (elT i) * (R.ι (elT v))⁻¹ = R.ι (elT i) := by
    rw [← map_mul, ← map_inv, ← map_mul, elT_comm]
  rw [h2] at h
  exact (elT_inj (R.inj h)).symm

theorem RecData.rho_yT :
    R.ρ (R.ι yT) = yHat := by
  refine Equiv.ext (fun i => ?_)
  have h := R.act (R.ι yT) i
  have h2 : R.ι yT * R.ι (elT i) * (R.ι yT)⁻¹ = R.ι (elT (yHat i)) := by
    rw [← map_mul, ← map_inv, ← map_mul, yT_act]
  rw [h2] at h
  exact (elT_inj (R.inj h)).symm

noncomputable def RecData.secS
    (k : Fin 8) : S :=
  if k = 0 then 1 else (R.surj (Dg k) (Dg_mem k)).choose

theorem RecData.rho_secS
    (k : Fin 8) : R.ρ (R.secS k) = Dg k := by
  unfold RecData.secS
  split_ifs with hk
  · rw [hk, Dg_zero, map_one]
  · exact (R.surj (Dg k) (Dg_mem k)).choose_spec

theorem RecData.secS_zero :
    R.secS 0 = 1 := by
  simp [RecData.secS]

theorem RecData.secS_conj
    (j : Fin 8) (w : Fin 16) :
    R.secS j * R.ι (elT w) = R.ι (elT (Dg j w)) * R.secS j := by
  have h := R.act (R.secS j) w
  rw [R.rho_secS, mul_inv_eq_iff_eq_mul] at h
  exact h

theorem RecData.kerEx
    (j k : Fin 8) :
    ∃ i, R.secS j * R.secS k * (R.secS (mulIdx j k))⁻¹ = R.ι (elT i) := by
  apply R.ker
  rw [map_mul, map_inv, map_mul, R.rho_secS, R.rho_secS, R.rho_secS, Dg_mul]
  simp

noncomputable def RecData.cS
    (j k : Fin 8) : Fin 16 := (R.kerEx j k).choose

theorem RecData.secS_mul
    (j k : Fin 8) :
    R.secS j * R.secS k = R.ι (elT (R.cS j k)) * R.secS (mulIdx j k) :=
  mul_inv_eq_iff_eq_mul.1 (R.kerEx j k).choose_spec

theorem RecData.decompS
    (g : S) : ∃ (v : Fin 16) (k : Fin 8), g = R.ι (elT v) * R.secS k := by
  obtain ⟨k, hk⟩ := Dg_exists (R.mem g)
  have h : R.ρ (g * (R.secS k)⁻¹) = 1 := by
    rw [map_mul, map_inv, R.rho_secS, hk]
    simp
  obtain ⟨i, hi⟩ := R.ker _ h
  exact ⟨i, k, by rw [← hi]; simp⟩

theorem RecData.uniqS
    (v : Fin 16) (k : Fin 8) (v' : Fin 16) (k' : Fin 8)
    (h : R.ι (elT v) * R.secS k = R.ι (elT v') * R.secS k') : v = v' ∧ k = k' := by
  have h1 := congrArg R.ρ h
  rw [map_mul, map_mul, R.rho_tr, R.rho_tr, one_mul, one_mul, R.rho_secS, R.rho_secS] at h1
  have hk : k = k' := Dg_inj h1
  subst hk
  have h2 : R.ι (elT v) = R.ι (elT v') := mul_right_cancel h
  exact ⟨elT_inj (R.inj h2), rfl⟩

@[expose] noncomputable def RecData.ext :
    ExtDat S where
  tr v := R.ι (elT v)
  sec := R.secS
  coc := R.cS
  tr_xor u v := by rw [elT_xor, map_mul]
  sec_zero := R.secS_zero
  conj := R.secS_conj
  sec_mul := R.secS_mul
  decomp := R.decompS
  uniq := R.uniqS

theorem RecData.yT_decomp :
    ∃ v : Fin 16, R.ι yT = R.ι (elT v) * R.secS 1 := by
  obtain ⟨v, k, hvk⟩ := R.decompS (R.ι yT)
  have h1 := congrArg R.ρ hvk
  rw [map_mul, R.rho_tr, one_mul, R.rho_secS, R.rho_yT, ← Dg_one] at h1
  have hk : (1 : Fin 8) = k := Dg_inj h1
  subst hk
  exact ⟨v, hvk⟩

end RecData

theorem b_zero
    {G H : Type*} [Group G] [Group H] (A : ExtDat G) (B : ExtDat H)
    (b : Fin 8 → Fin 16)
    (hb : ∀ j k, xor16 (A.coc j k) (B.coc j k) = xor16 (b j) (xor16 (Dg j (b k)) (b (mulIdx j k)))) :
    b 0 = 0 := by
  have h := hb 0 0
  simp only [A.coc_zero_left, B.coc_zero_left, Dg_zero, Perm.one_apply, mulIdx_zero_zero, x16_self,
    x16_zero] at h
  exact h.symm

theorem adjust
    {G H : Type*} [Group G] [Group H] (A : ExtDat G) (B : ExtDat H)
    (b : Fin 8 → Fin 16)
    (hb : ∀ j k, xor16 (A.coc j k) (B.coc j k) = xor16 (b j) (xor16 (Dg j (b k)) (b (mulIdx j k))))
    (v₀ v₀' : Fin 16)
    (hA : xor16 v₀ (xor16 (Dg 1 v₀) (A.coc 1 1)) = 0)
    (hB : xor16 v₀' (xor16 (Dg 1 v₀') (B.coc 1 1)) = 0) :
    ∃ b' : Fin 8 → Fin 16,
      (∀ j k, xor16 (A.coc j k) (B.coc j k) =
        xor16 (b' j) (xor16 (Dg j (b' k)) (b' (mulIdx j k)))) ∧ xor16 v₀ (b' 1) = v₀' := by
  have hb0 := b_zero A B b hb
  have hb11 := hb 1 1
  rw [mulIdx_one_one, hb0, x16_zero] at hb11
  have hzy : xor16 (xor16 (xor16 v₀ v₀') (b 1)) (Dg 1 (xor16 (xor16 v₀ v₀') (b 1))) = 0 := by
    rw [Dg_lin, Dg_lin]
    apply x16_ext
    intro i
    have e1 := congrArg (fun a : Fin 16 => a.val.testBit i) hA
    have e2 := congrArg (fun a : Fin 16 => a.val.testBit i) hB
    have e3 := congrArg (fun a : Fin 16 => a.val.testBit i) hb11
    simp only [x16_testBit, Fin.val_zero, Nat.zero_testBit] at e1 e2 e3 ⊢
    exact bool_adj1 _ _ _ _ _ _ _ _ e1 e2 e3
  obtain ⟨r, hr⟩ := fix_im _ hzy
  refine ⟨fun k => xor16 (b k) (cr k r), fun j k => ?_, ?_⟩
  · rw [hb j k]
    have hc := cr_cocycle j k r
    show _ = xor16 (xor16 (b j) (cr j r)) (xor16 (Dg j (xor16 (b k) (cr k r)))
      (xor16 (b (mulIdx j k)) (cr (mulIdx j k) r)))
    rw [Dg_lin]
    apply x16_ext
    intro i
    have e1 := congrArg (fun a : Fin 16 => a.val.testBit i) hc
    simp only [x16_testBit, Fin.val_zero, Nat.zero_testBit] at e1 ⊢
    exact bool_adj2 _ _ _ _ _ _ e1
  · show xor16 v₀ (xor16 (b 1) (cr 1 r)) = v₀'
    rw [← hr]
    apply x16_ext
    intro i
    simp only [x16_testBit]
    exact bool_adj3 _ _ _

theorem rec1_core
    {S : Type*} [Group S] (R : RecData S) {H : Subgroup (Perm (Fin 16))}
    (B : ExtDat ↥H) (Tr : Fin 16 → Perm (Fin 16)) (yy : Perm (Fin 16))
    (hTr : ∀ v, ((B.tr v : ↥H) : Perm (Fin 16)) = Tr v) (v₀' : Fin 16)
    (hyy : ((B.tr v₀' * B.sec 1 : ↥H) : Perm (Fin 16)) = yy) (hyy2 : yy * yy = 1)
    (b : Fin 8 → Fin 16)
    (hb : ∀ j k, xor16 (R.ext.coc j k) (B.coc j k) =
      xor16 (b j) (xor16 (Dg j (b k)) (b (mulIdx j k)))) :
    ∃ ψ : S ≃* ↥H, ∀ t : ↥T5, (ψ (R.ι t) : Perm (Fin 16)) = emb48 Tr yy t := by
  obtain ⟨v₀, hv₀⟩ := R.yT_decomp
  have hsq : (R.ι (elT v₀) * R.secS 1) * (R.ι (elT v₀) * R.secS 1) = 1 := by
    rw [← hv₀, ← map_mul, yT_sq, map_one]
  have hA : xor16 v₀ (xor16 (Dg 1 v₀) (R.ext.coc 1 1)) = 0 :=
    R.ext.invol mulIdx_one_one hsq
  have hsqB : (B.tr v₀' * B.sec 1) * (B.tr v₀' * B.sec 1) = 1 := by
    apply Subtype.ext
    have h1 : (((B.tr v₀' * B.sec 1) * (B.tr v₀' * B.sec 1) : ↥H) : Perm (Fin 16)) = yy * yy := by
      rw [Subgroup.coe_mul, hyy]
    rw [h1, hyy2]
    rfl
  have hB : xor16 v₀' (xor16 (Dg 1 v₀') (B.coc 1 1)) = 0 := B.invol mulIdx_one_one hsqB
  obtain ⟨b', hb', hb'1⟩ := adjust R.ext B b hb v₀ v₀' hA hB
  have hb'0 : b' 0 = 0 := b_zero R.ext B b' hb'
  obtain ⟨ψ, hψ⟩ := ExtDat.iso R.ext B b' hb'
  refine ⟨ψ, fun t => ?_⟩
  have hψR : ∀ i, ψ (R.ι (elT i)) = B.tr i := by
    intro i
    have h1 : R.ι (elT i) = R.ext.tr i * R.ext.sec 0 := by
      show R.ι (elT i) = R.ι (elT i) * R.secS 0
      rw [R.secS_zero, mul_one]
    rw [h1, hψ, hb'0, x16_zero, B.sec_zero, mul_one]
  have hψy : ψ (R.ι yT) = B.tr v₀' * B.sec 1 := by
    rw [hv₀]
    have h1 : R.ι (elT v₀) * R.secS 1 = R.ext.tr v₀ * R.ext.sec 1 := rfl
    rw [h1, hψ, hb'1]
  rcases T5_cases t.2 with hR | hR
  · have ht : t = elT (idx16 t.1) := Subtype.ext (el16_idx16 hR).symm
    have h1 : ψ (R.ι t) = B.tr (idx16 t.1) := by
      calc ψ (R.ι t) = ψ (R.ι (elT (idx16 t.1))) := by rw [← ht]
        _ = B.tr (idx16 t.1) := hψR _
    rw [h1, hTr]
    unfold emb48
    split_ifs with hmem
    · rfl
    · exact absurd (mem_Rm.1 hR) hmem
  · have hnot : t.1 ∉ Rm := by
      intro hR'
      apply yy5_not_mem
      have : (t.1)⁻¹ * (t.1 * yy5) ∈ Rm := Rm.mul_mem (Rm.inv_mem hR') hR
      simpa using this
    have ht : t = elT (idx16 (t.1 * yy5)) * yT := by
      apply Subtype.ext
      show t.1 = el16 (idx16 (t.1 * yy5)) * yy5
      rw [el16_idx16 hR, mul_assoc, yy5_sq, mul_one]
    have h1 : ψ (R.ι t) = B.tr (idx16 (t.1 * yy5)) * (B.tr v₀' * B.sec 1) := by
      calc ψ (R.ι t) = ψ (R.ι (elT (idx16 (t.1 * yy5)) * yT)) := by rw [← ht]
        _ = B.tr (idx16 (t.1 * yy5)) * (B.tr v₀' * B.sec 1) := by
          rw [map_mul, map_mul, hψR, hψy]
    have h2 : (((B.tr (idx16 (t.1 * yy5)) * (B.tr v₀' * B.sec 1) : ↥H)) : Perm (Fin 16)) =
        Tr (idx16 (t.1 * yy5)) * yy := by
      rw [Subgroup.coe_mul, hyy, hTr]
    rw [h1, h2]
    unfold emb48
    split_ifs with hmem
    · exact absurd (mem_Rm.2 hmem) hnot
    · rfl

theorem rec1_of
    (S : Type*) [Group S] (R : RecData S) :
    (∃ ψ : S ≃* ↥Sh0, ∀ t, (ψ (R.ι t) : Perm (Fin 16)) = emb48 tr16 yHat t) ∨
    (∃ ψ : S ≃* ↥Sh1, ∀ t, (ψ (R.ι t) : Perm (Fin 16)) = emb48 tr1 yHat1 t) := by
  obtain ⟨ε, b, hb⟩ := fs_cc1 R.ext.coc R.ext.isCocyc
  cases ε
  · left
    refine rec1_core R ext0 tr16 yHat (fun v => ext0_tr v) 0 sh0_yHat yHat_sq b (fun j k => ?_)
    have h : R.ext.coc j k = xor16 0 (xor16 (b j) (xor16 (Dg j (b k)) (b (mulIdx j k)))) := hb j k
    rw [x16_zero_left] at h
    rw [h, ext0_coc, x16_zero]
  · right
    obtain ⟨v₀', hv₀'⟩ := sh1_yHat1
    refine rec1_core R ext1 tr1 yHat1 (fun v => ext1_tr v) v₀' hv₀' yHat1_sq b (fun j k => ?_)
    have h := hb j k
    have h' : R.ext.coc j k = xor16 (cc1 j k) (xor16 (b j) (xor16 (Dg j (b k)) (b (mulIdx j k)))) :=
      h
    rw [h', ext1_coc, x16_comm (cc1 j k), x16_cancel]

end CFSG.GH74.GLS.C3.Layer2.L5.Rec1

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5.Rec1

theorem rec1
    (S : Type) [Group S] [Finite S] (ι : ↥T5 →* S) (ρ : S →* Perm (Fin 16))
    (_hcard : Nat.card S = 128) (hinj : Function.Injective ι)
    (hact : ∀ s i, s * ι (elT i) * s⁻¹ = ι (elT (ρ s i))) (hD : ∀ s, ρ s ∈ d8L)
    (hsurj : ∀ d ∈ d8L, ∃ s, ρ s = d) (hker : ∀ s, ρ s = 1 → ∃ i, s = ι (elT i)) :
    (∃ ψ : S ≃* ↥Sh0, ∀ t, (ψ (ι t) : Perm (Fin 16)) = emb48 tr16 yHat t) ∨
    (∃ ψ : S ≃* ↥Sh1, ∀ t, (ψ (ι t) : Perm (Fin 16)) = emb48 tr1 yHat1 t) :=
  rec1_of S ⟨ι, ρ, hinj, hact, hD, hsurj, hker⟩

end CFSG.GH74.GLS.C3.Layer2.L5
