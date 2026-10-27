module

public import CFSG.CGT.PushingUpLit.SolKR2.WeakSigAlg
public import CFSG.CGT.PushingUpLit.SolKR2.WeakOmega
public import CFSG.CGT.PushingUpLit.SolKR2.PartitionWitness
public import CFSG.CGT.PushingUpLit.SolKR2.TorusData
public import CFSG.CGT.PushingUpLit.SolKR2.WeakNames
public import CFSG.CGT.PushingUpLit.SolKR2.WeakF0
public import CFSG.CGT.PushingUpLit.SolKR2.WeakA
public import CFSG.CGT.PushingUpLit.SolKR2.WeakEnd
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen
import CFSG.Timmesfeld.Moufang.Three
import CFSG.Timmesfeld.RankOne
import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim78
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup BenderCenterInput
  UnitaryTwoGenerationInput)
open CFSG.RankThree.GF2n (conjSubgroup_mul conjSubgroup_one conjSubgroup_eq_self_iff
  card_conjSubgroup exists_mul_of_mem_sup le_normalizer_of_comm)
open CFSG.CGT.Timmesfeld75 (conjSubgroup_inj conj_mem_conjSubgroup)
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)

variable {G : Type} [Group G]

theorem elemAbelian_comm {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem elemAbelian_sq {E : Subgroup G} (hE : IsElemAbelian 2 E) : ∀ x ∈ E, x * x = 1 :=
  fun x hx => by
    have := hE.2 x hx
    rwa [sq] at this

structure F0Facts (B : Subgroup G) (g m x : G) : Prop where
  card_C0 : Nat.card ↥(sC0 B g x) = 4
  card_C1 : Nat.card ↥(sC1 B g x) = 16
  exists_C1_not_C0 : ∃ c ∈ sC1 B g x, c ∉ sC0 B g x
  card_F0 : Nat.card ↥(sF0 B g m x) = 4
  elem_F0 : IsElemAbelian 2 (sF0 B g m x)
  F0_inf_X : sF0 B g m x ⊓ sX B g x = ⊥
  exists_mul_S_F0 : ∀ a ∈ sA0 B m, ∃ s ∈ sS B g m x, ∃ f ∈ sF0 B g m x, a = s * f
  exists_A0_of_F0 : ∀ f ∈ sF0 B g m x, ∃ a ∈ sA0 B m, ∃ s ∈ sS B g m x, a = s * f
  S_mul_F0 : ∀ s ∈ sS B g m x, ∀ f ∈ sF0 B g m x, s * f ∈ sA0 B m → s * f ≠ 1 →
    s ∉ sC0 B g x ∧ f ≠ 1
  S_inf_F0 : sS B g m x ⊓ sF0 B g m x = ⊥
  elem_S : IsElemAbelian 2 (sS B g m x)
  card_S : Nat.card ↥(sS B g m x) = 16
  card_N : Nat.card ↥(sN B g x) = 16
  card_S2 : Nat.card ↥(sS2 B g x) = 64
  S_inf_N : sS B g m x ⊓ sN B g x = sC0 B g x
  elem_E : IsElemAbelian 2 (sE B g m x)
  card_E : Nat.card ↥(sE B g m x) = 64
  comm_C1_E : ∀ c ∈ sC1 B g x, ∀ e ∈ sE B g m x, c * e * c⁻¹ * e⁻¹ ∈ sC0 B g x
  cent_E : ∀ c ∈ sC1 B g x, c ∉ sC0 B g x → ∀ e ∈ sE B g m x, c * e = e * c →
    e ∈ sV B g m x
  F0_faithful : ∀ f ∈ sF0 B g m x, f ∈ Subgroup.centralizer (omegaTwoSub B : Set G) → f = 1

structure TorusFacts (B : Subgroup G) (g x hh : G) : Prop where
  pow_three : hh ^ 3 = 1
  ne_one : hh ≠ 1
  mem_X : hh ∈ sX B g x
  norm_C1 : hh ∈ Subgroup.normalizer (sC1 B g x : Set G)
  fpf_C0 : ∀ c ∈ sC0 B g x, hh * c * hh⁻¹ = c → c = 1
  fpf_S2 : ∀ s ∈ sS2 B g x, hh * s * hh⁻¹ * s⁻¹ ∈ sN B g x → s ∈ sN B g x


section Config

variable {M B : Subgroup G} {h : R2 M B} {g m α x : G}

theorem sX_le_cent (d : R2StarData h g m α x) :
    sX B g x ≤ Subgroup.centralizer (omegaTwoSub B : Set G) :=
  sup_le d.centr d.cent_C

theorem sS2_le_sX : sS2 B g x ≤ sX B g x := dS2_le_dX _ x

theorem sS_le_sS2 : sS B g m x ≤ sS2 B g x := inf_le_left

theorem A0_eq_one_of_mem_S (d : R2StarData h g m α x) {a : G} (ha : a ∈ sA0 B m)
    (haS : a ∈ sS B g m x) : a = 1 :=
  d.inf_cent a ha (sX_le_cent d (sS2_le_sX (sS_le_sS2 haS)))

theorem sC0_le_sC1 : sC0 B g x ≤ sC1 B g x := omegaOneSub_le _

theorem sC1_le_sX : sC1 B g x ≤ sX B g x := C_le_dX _ x

theorem sN_le_sS2 : sN B g x ≤ sS2 B g x := dN_le_dS2 _ x

theorem sC1_le_sS2 : sC1 B g x ≤ sS2 B g x := C_le_dS2 _ x

theorem sC0_le_sN : sC0 B g x ≤ sN B g x := le_sup_right

theorem sC0_inf_sF0 (F : F0Facts B g m x) : sC0 B g x ⊓ sF0 B g m x = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : z ∈ sF0 B g m x ⊓ sX B g x :=
    ⟨hz.2, sC1_le_sX (sC0_le_sC1 hz.1)⟩
  rw [F.F0_inf_X, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr this

theorem hh_norm_C0 {hh : G} (d : R2StarData h g m α x) (T : TorusFacts B g x hh) {c : G}
    (hc : c ∈ sC0 B g x) : hh * c * hh⁻¹ ∈ sC0 B g x := by
  have hab := d.data31.core.comm_conj' x
  rw [mem_omegaOneSub_iff hab] at hc ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp T.norm_C1 c).mp hc.1, ?_⟩
  calc hh * c * hh⁻¹ * (hh * c * hh⁻¹) = hh * (c * c) * hh⁻¹ := by group
    _ = 1 := by rw [hc.2]; group


theorem hh_cent_F0 {hh : G} (T : TorusFacts B g x hh) {f : G} (hf : f ∈ sF0 B g m x) :
    hh * f * hh⁻¹ = f := by
  have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hf).2 hh T.mem_X
  rw [this]
  group

theorem sS_le_sE : sS B g m x ≤ sE B g m x := le_sup_left

theorem sF0_le_sE : sF0 B g m x ≤ sE B g m x := le_sup_right

theorem isSig_sA0 : IsSig B (sA0 B m) := ⟨m, rfl⟩

theorem sA0_le_sE (F : F0Facts B g m x) : sA0 B m ≤ sE B g m x := fun a ha => by
  obtain ⟨s, hs, f, hf, rfl⟩ := F.exists_mul_S_F0 a ha
  exact (sE B g m x).mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hf)

theorem sF0_le_sV : sF0 B g m x ≤ sV B g m x := le_sup_right

theorem sC0_le_sS (F : F0Facts B g m x) : sC0 B g x ≤ sS B g m x := by
  have : sS B g m x ⊓ sN B g x = sC0 B g x := F.S_inf_N
  rw [← this]
  exact inf_le_left

theorem sV_le_sE (F : F0Facts B g m x) : sV B g m x ≤ sE B g m x :=
  sup_le_sup_right (sC0_le_sS F) _

theorem sC0_le_sV : sC0 B g x ≤ sV B g m x := le_sup_left

theorem sA0_exists_ne_one [Finite G] (h : R2 M B) : ∃ a ∈ sA0 B m, a ≠ 1 := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Pair.conj_B0_ne_bot h m)
  exact ⟨a, ha, fun e => ha1 (Subtype.ext e)⟩

theorem sA0_decomp (F : F0Facts B g m x) {a : G} (ha : a ∈ sA0 B m) :
    ∃ s ∈ sS B g m x, ∃ f ∈ sF0 B g m x, a = s * f ∧
      (a ≠ 1 → s ∉ sC0 B g x ∧ f ≠ 1) := by
  obtain ⟨s, hs, f, hf, rfl⟩ := F.exists_mul_S_F0 a ha
  exact ⟨s, hs, f, hf, rfl, fun h1 => F.S_mul_F0 s hs f hf ha h1⟩

theorem sA0_eq_of_same_F0 (d : R2StarData h g m α x) {s s' f : G} (hs : s ∈ sS B g m x)
    (hs' : s' ∈ sS B g m x) (ha : s * f ∈ sA0 B m) (hb : s' * f ∈ sA0 B m) :
    s * f = s' * f := by
  have h1 : (s * f) * (s' * f)⁻¹ ∈ sA0 B m := (sA0 B m).mul_mem ha ((sA0 B m).inv_mem hb)
  have h2 : (s * f) * (s' * f)⁻¹ = s * s'⁻¹ := by group
  rw [h2] at h1
  have h3 : s * s'⁻¹ ∈ sS B g m x := (sS B g m x).mul_mem hs ((sS B g m x).inv_mem hs')
  have h4 : s * s'⁻¹ = 1 := A0_eq_one_of_mem_S d h1 h3
  rw [mul_inv_eq_one.mp h4]


theorem mul_three_eq_one {hh : G} (h3 : hh ^ 3 = 1) : hh * hh * hh = 1 := by
  rw [← pow_three']
  exact h3

theorem sq_eq_inv_of_pow_three {hh : G} (h3 : hh ^ 3 = 1) : hh * hh = hh⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  exact mul_three_eq_one h3

theorem conj_conj_conj_eq {hh : G} (h3 : hh ^ 3 = 1) (X : Subgroup G) :
    conjSubgroup hh (conjSubgroup hh (conjSubgroup hh X)) = X := by
  ext z
  simp only [mem_conjSubgroup]
  rw [show hh⁻¹ * (hh⁻¹ * (hh⁻¹ * z * hh) * hh) * hh = (hh * hh * hh)⁻¹ * z * (hh * hh * hh)
    by group, mul_three_eq_one h3]
  simp

theorem conjSubgroup_le_of_norm {k : G} {X E : Subgroup G} (hn : ∀ e ∈ E, k * e * k⁻¹ ∈ E)
    (hX : X ≤ E) : conjSubgroup k X ≤ E := fun z hz => by
  have := hn _ (hX (mem_conjSubgroup.mp hz))
  rwa [show k * (k⁻¹ * z * k) * k⁻¹ = z by group] at this

theorem comm_of_conj_comm {k a b : G}
    (h : (k * a * k⁻¹) * (k * b * k⁻¹) = (k * b * k⁻¹) * (k * a * k⁻¹)) : a * b = b * a :=
  calc a * b = k⁻¹ * ((k * a * k⁻¹) * (k * b * k⁻¹)) * k := by group
    _ = k⁻¹ * ((k * b * k⁻¹) * (k * a * k⁻¹)) * k := by rw [h]
    _ = b * a := by group

theorem hh_fix_S {hh : G} (F : F0Facts B g m x) (T : TorusFacts B g x hh) {s : G}
    (hs : s ∈ sS B g m x) (hfix : hh * s * hh⁻¹ = s) : s = 1 := by
  have h1 : hh * s * hh⁻¹ * s⁻¹ ∈ sN B g x := by
    rw [hfix, mul_inv_cancel]
    exact (sN B g x).one_mem
  have h2 : s ∈ sN B g x := T.fpf_S2 s (sS_le_sS2 hs) h1
  have h3 : s ∈ sC0 B g x := by
    have : s ∈ sS B g m x ⊓ sN B g x := ⟨hs, h2⟩
    rwa [F.S_inf_N] at this
  exact T.fpf_C0 s h3 hfix

theorem conj_sC0_eq [Finite G] {hh : G} (d : R2StarData h g m α x)
    (T : TorusFacts B g x hh) : conjSubgroup hh (sC0 B g x) = sC0 B g x := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_conjSubgroup])
  intro z hz
  have := hh_norm_C0 d T (mem_conjSubgroup.mp hz)
  rwa [show hh * (hh⁻¹ * z * hh) * hh⁻¹ = z by group] at this

theorem sV_decomp (F : F0Facts B g m x) {v : G} (hv : v ∈ sV B g m x) :
    ∃ c ∈ sC0 B g x, ∃ f ∈ sF0 B g m x, v = c * f := by
  have hN : sF0 B g m x ≤ Subgroup.normalizer (sC0 B g x : Set G) :=
    le_normalizer_of_comm fun f hf c hc =>
      elemAbelian_comm F.elem_E f (sF0_le_sE hf) c (sV_le_sE F (sC0_le_sV hc))
  exact exists_mul_of_mem_sup hN hv

theorem hh_norm_V {hh : G} (d : R2StarData h g m α x) (F : F0Facts B g m x)
    (T : TorusFacts B g x hh) {v : G} (hv : v ∈ sV B g m x) : hh * v * hh⁻¹ ∈ sV B g m x := by
  obtain ⟨c, hc, f, hf, rfl⟩ := sV_decomp F hv
  have e1 : hh * (c * f) * hh⁻¹ = (hh * c * hh⁻¹) * (hh * f * hh⁻¹) := by group
  rw [e1, hh_cent_F0 T hf]
  exact (sV B g m x).mul_mem (sC0_le_sV (hh_norm_C0 d T hc)) (sF0_le_sV hf)

theorem card_sV (F : F0Facts B g m x) : Nat.card ↥(sV B g m x) = 16 := by
  have hcomm : ∀ a ∈ sC0 B g x, ∀ b ∈ sF0 B g m x, a * b = b * a := fun a ha b hb =>
    elemAbelian_comm F.elem_E a (sV_le_sE F (sC0_le_sV ha)) b (sF0_le_sE hb)
  show Nat.card ↥(sC0 B g x ⊔ sF0 B g m x) = 16
  rw [card_sup_of_commute hcomm (sC0_inf_sF0 F), F.card_C0, F.card_F0]

theorem sV_le_cent_C1 (d : R2StarData h g m α x) :
    sV B g m x ≤ Subgroup.centralizer (sC1 B g x : Set G) := by
  refine sup_le (fun v hv => ?_) (fun f hf => ?_)
  · refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
    exact d.data31.core.comm_conj' x c hc v (omegaOneSub_le _ hv)
  · refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hf).2 c (sC1_le_sX hc)

theorem sC0_eq_conj (h : R2 M B) (g x : G) :
    sC0 B g x = conjSubgroup (x * g) (omegaOneSub B) := by
  show omegaOneSub (conjSubgroup x (conjSubgroup g (omegaTwoSub B))) = _
  rw [← conjSubgroup_mul, Pair.omegaOne_conj_U h (x * g)]

theorem sC1_eq_conj (g x : G) : sC1 B g x = conjSubgroup (x * g) (omegaTwoSub B) := by
  show conjSubgroup x (conjSubgroup g (omegaTwoSub B)) = _
  rw [← conjSubgroup_mul]

theorem isSig_ti [Finite G] (h : R2 M B) {Q Q' : Subgroup G} (hQ : IsSig B Q)
    (hQ' : IsSig B Q') : Q = Q' ∨ Q ⊓ Q' = ⊥ := by
  by_cases heq : Q = Q'
  · exact Or.inl heq
  · exact Or.inr (IsSig.inf_eq_bot h hQ hQ' heq)

theorem eq_of_card_sixteen [Finite G] {L W E C₀ : Subgroup G} (hLW : L ≤ W) (hWE : W ≤ E)
    (hC₀E : C₀ ≤ E) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE : Nat.card ↥E = 64)
    (hC₀ : Nat.card ↥C₀ = 4) (hL : Nat.card ↥L = 16) (hWC : W ⊓ C₀ = ⊥) : L = W := by
  have hcomm : ∀ a ∈ W, ∀ b ∈ C₀, a * b = b * a := fun a ha b hb => hEc a (hWE ha) b (hC₀E hb)
  have h1 := SYMB.card_sup_mul_card_inf_of_commute hcomm
  rw [hWC, Subgroup.card_bot, hC₀, mul_one] at h1
  have h2 : Nat.card ↥(W ⊔ C₀) ≤ 64 := hE ▸ Subgroup.card_le_of_le (sup_le hWE hC₀E)
  exact Subgroup.eq_of_le_of_card_ge hLW (by omega)

theorem lc_member [Finite G] (d : R2StarData h g m α x) (F : F0Facts B g m x)
    {L : Subgroup G} (hLE : L ≤ sE B g m x) (hL : Nat.card ↥L = 16)
    (hLC0 : L ⊓ sC0 B g x = ⊥) (hcov : SigCover B L) :
    IsSig B (L ⊓ sV B g m x) ∧ Nat.card ↥(L ⊓ sV B g m x) = 4 := by
  obtain ⟨c, hc, hcC0⟩ := F.exists_C1_not_C0
  refine lc_generic (IsSig B) (fun Q Q' hQ hQ' => ?_) (fun Q k hQ => hQ.conj k)
    (fun Q hQ => IsSig.card h hQ) (elemAbelian_comm F.elem_E) F.card_E hLE hL
    sC0_le_sV F.card_C0 (sV_le_sE F) (card_sV F) hLC0
    (fun e he => F.comm_C1_E c hc e he) (fun e he hce => F.cent_E c hc hcC0 e he hce)
    (fun v hv => Subgroup.mem_centralizer_iff.mp (sV_le_cent_C1 d hv) c hc) hcov
  by_cases heq : Q = Q'
  · exact Or.inl heq
  · exact Or.inr (IsSig.inf_eq_bot h hQ hQ' heq)

theorem sup3_le_cent_A1 (h : R2 M B) {hh : G} (T : TorusFacts B g x hh)
    (hcomm1 : ∀ a ∈ conjSubgroup m (omegaTwoSub B), ∀ b ∈ conjSubgroup (hh * m) (omegaTwoSub B),
      a * b = b * a) :
    sA0 B m ⊔ conjSubgroup hh (sA0 B m) ⊔ conjSubgroup hh (conjSubgroup hh (sA0 B m)) ≤
      Subgroup.centralizer (conjSubgroup m (omegaTwoSub B) : Set G) := by
  have hA1 : sA0 B m ≤ conjSubgroup m (omegaTwoSub B) := Pair.conj_B0_le_U h m
  have hcomm := Pair.comm_conj_U h m
  have hA1h : conjSubgroup hh (sA0 B m) ≤ conjSubgroup (hh * m) (omegaTwoSub B) := by
    rw [conjSubgroup_mul]
    intro z hz
    exact mem_conjSubgroup.mpr (hA1 (mem_conjSubgroup.mp hz))
  refine sup_le (sup_le (fun a ha => ?_) (fun a ha => ?_)) (fun a ha => ?_)
  · exact Subgroup.mem_centralizer_iff.mpr fun u hu => hcomm u hu a (hA1 ha)
  · exact Subgroup.mem_centralizer_iff.mpr fun u hu => hcomm1 u hu a (hA1h ha)
  · have ha' : hh⁻¹ * (hh⁻¹ * a * hh) * hh ∈ sA0 B m :=
      mem_conjSubgroup.mp (mem_conjSubgroup.mp ha)
    have hsq := sq_eq_inv_of_pow_three T.pow_three
    have e : hh * a * hh⁻¹ = hh⁻¹ * (hh⁻¹ * a * hh) * hh :=
      calc hh * a * hh⁻¹ = (hh⁻¹)⁻¹ * a * hh⁻¹ := by group
        _ = (hh * hh)⁻¹ * a * (hh * hh) := by rw [hsq]
        _ = hh⁻¹ * (hh⁻¹ * a * hh) * hh := by group
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have h1 := hcomm1 _ (hA1 ha') (hh * u * hh⁻¹) (by
      rw [conjSubgroup_mul]
      exact conj_mem_conjSubgroup hh hu)
    rw [← e] at h1
    exact (comm_of_conj_comm h1).symm


section Cert

variable [Finite G]
  (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
include hCen hU

theorem X_conj_N_iff (d : R2StarData h g m α x) {z : G} (hz : z ∈ sX B g x) (n : G) :
    z * n * z⁻¹ ∈ sN B g x ↔ n ∈ sN B g x := by
  refine ⟨fun hn => ?_, fun hn => Inner.X_normalizes_N d.data31 hCen hU hz hn⟩
  have := Inner.X_normalizes_N d.data31 hCen hU ((sX B g x).inv_mem hz) hn
  simpa [mul_assoc] using this


variable {hh : G}

theorem sC1_le_normalizer_N (d : R2StarData h g m α x) :
    sC1 B g x ≤ Subgroup.normalizer (sN B g x : Set G) := fun c hc => by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  exact (X_conj_N_iff hCen hU d (sC1_le_sX hc) n).symm

theorem sS2_le_normalizer_N (d : R2StarData h g m α x) :
    sS2 B g x ≤ Subgroup.normalizer (sN B g x : Set G) := fun z hz => by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  exact (X_conj_N_iff hCen hU d (sS2_le_sX hz) n).symm

theorem hh_norm_N (d : R2StarData h g m α x) (T : TorusFacts B g x hh) {n : G}
    (hn : n ∈ sN B g x) : hh * n * hh⁻¹ ∈ sN B g x :=
  (X_conj_N_iff hCen hU d T.mem_X n).mpr hn

theorem hh_norm_S2 (d : R2StarData h g m α x) (T : TorusFacts B g x hh) {s : G}
    (hs : s ∈ sS2 B g x) : hh * s * hh⁻¹ ∈ sS2 B g x := by
  obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_of_mem_sup (sC1_le_normalizer_N hCen hU d) hs
  have e : hh * (n * c) * hh⁻¹ = (hh * n * hh⁻¹) * (hh * c * hh⁻¹) := by group
  rw [e]
  exact (sS2 B g x).mul_mem (sN_le_sS2 (hh_norm_N hCen hU d T hn))
    (sC1_le_sS2 ((Subgroup.mem_normalizer_iff.mp T.norm_C1 c).mp hc))

theorem cent_N_of_not_mem (d : R2StarData h g m α x) {s : G} (hs : s ∈ sS2 B g x)
    (hsN : s ∉ sN B g x) {n : G} (hn : n ∈ sN B g x) (hsn : s * n = n * s) :
    n ∈ sC0 B g x := by
  obtain ⟨n₁, hn₁, c, hc, rfl⟩ := exists_mul_of_mem_sup (sC1_le_normalizer_N hCen hU d) hs
  have hcN : c ∉ sC0 B g x := fun hc0 => hsN ((sN B g x).mul_mem hn₁ (sC0_le_sN hc0))
  refine Inner.cent_C d.data31 hCen hU hc hcN hn ?_
  have h1 : n * n₁ = n₁ * n := Inner.N_comm d.data31 hCen hU hn hn₁
  calc c * n = n₁⁻¹ * (n₁ * c * n) := by group
    _ = n₁⁻¹ * (n * (n₁ * c)) := by rw [hsn]
    _ = n₁⁻¹ * (n * n₁) * c := by group
    _ = n * c := by rw [h1]; group

theorem hh_norm_S (d : R2StarData h g m α x) (F : F0Facts B g m x) (T : TorusFacts B g x hh)
    {s : G} (hs : s ∈ sS B g m x) : hh * s * hh⁻¹ ∈ sS B g m x := by
  have hSc := elemAbelian_comm F.elem_S
  have hSsq := elemAbelian_sq F.elem_S
  have hinv : ∀ z ∈ conjSubgroup hh (sS B g m x), hh⁻¹ * z * hh ∈ sS B g m x :=
    fun z hz => mem_conjSubgroup.mp hz
  have hE'S2 : conjSubgroup hh (sS B g m x) ≤ sS2 B g x := fun z hz => by
    have := hh_norm_S2 hCen hU d T (sS_le_sS2 (hinv z hz))
    rwa [show hh * (hh⁻¹ * z * hh) * hh⁻¹ = z by group] at this
  have hE'c : ∀ y ∈ conjSubgroup hh (sS B g m x), ∀ z ∈ conjSubgroup hh (sS B g m x),
      y * z = z * y := fun y hy z hz => by
    have h1 := hSc _ (hinv y hy) _ (hinv z hz)
    calc y * z = hh * ((hh⁻¹ * y * hh) * (hh⁻¹ * z * hh)) * hh⁻¹ := by group
      _ = hh * ((hh⁻¹ * z * hh) * (hh⁻¹ * y * hh)) * hh⁻¹ := by rw [h1]
      _ = z * y := by group
  have hE'2 : ∀ y ∈ conjSubgroup hh (sS B g m x), y * y = 1 := fun y hy => by
    have h1 := hSsq _ (hinv y hy)
    calc y * y = hh * ((hh⁻¹ * y * hh) * (hh⁻¹ * y * hh)) * hh⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hne : conjSubgroup hh (sS B g m x) ≠ sN B g x := by
    intro heq
    have hSN : sS B g m x ≤ sN B g x := fun z hz => by
      have : hh * z * hh⁻¹ ∈ conjSubgroup hh (sS B g m x) := by
        rw [mem_conjSubgroup, show hh⁻¹ * (hh * z * hh⁻¹) * hh = z by group]
        exact hz
      rw [heq] at this
      exact (X_conj_N_iff hCen hU d T.mem_X z).mp this
    have h1 : sS B g m x ⊓ sN B g x = sS B g m x := inf_of_le_left hSN
    rw [F.S_inf_N] at h1
    have := F.card_S
    rw [← h1, F.card_C0] at this
    omega
  have key := e16_unique_generic (N := sN B g x) (S₂ := sS2 B g x) (S := sS B g m x)
    (C₀ := sC0 B g x) (E' := conjSubgroup hh (sS B g m x))
    (fun n hn => Inner.N_sq d.data31 hCen hU hn) (sS2_le_normalizer_N hCen hU d) F.card_N
    F.card_S2 F.card_C0 sS_le_sS2 hSsq F.S_inf_N F.card_S
    (fun s hs hsN n hn hsn => cent_N_of_not_mem hCen hU d hs hsN hn hsn) sN_le_sS2 hE'S2 hE'c
    hE'2 (by rw [card_conjSubgroup]; exact F.card_S) hne
  have : hh * s * hh⁻¹ ∈ conjSubgroup hh (sS B g m x) := by
    rw [mem_conjSubgroup, show hh⁻¹ * (hh * s * hh⁻¹) * hh = s by group]
    exact hs
  rwa [key] at this


theorem conj_sA0_le_sE (d : R2StarData h g m α x) (F : F0Facts B g m x)
    (T : TorusFacts B g x hh) : conjSubgroup hh (sA0 B m) ≤ sE B g m x := by
  intro z hz
  have hz' : hh⁻¹ * z * hh ∈ sA0 B m := mem_conjSubgroup.mp hz
  obtain ⟨s, hs, f, hf, he⟩ := F.exists_mul_S_F0 _ hz'
  have hz2 : z = (hh * s * hh⁻¹) * f := by
    calc z = hh * (hh⁻¹ * z * hh) * hh⁻¹ := by group
      _ = hh * (s * f) * hh⁻¹ := by rw [he]
      _ = (hh * s * hh⁻¹) * (hh * f * hh⁻¹) := by group
      _ = (hh * s * hh⁻¹) * f := by rw [hh_cent_F0 T hf]
  rw [hz2]
  exact (sE B g m x).mul_mem (sS_le_sE (hh_norm_S hCen hU d F T hs)) (sF0_le_sE hf)

theorem conj_sA0_ne (d : R2StarData h g m α x) (F : F0Facts B g m x)
    (T : TorusFacts B g x hh) : conjSubgroup hh (sA0 B m) ≠ sA0 B m := by
  intro heq
  obtain ⟨a, ha, ha1⟩ := sA0_exists_ne_one (m := m) h
  obtain ⟨s, hs, f, hf, rfl, hsf⟩ := sA0_decomp F ha
  have hmem : hh * (s * f) * hh⁻¹ ∈ sA0 B m := by
    have : hh * (s * f) * hh⁻¹ ∈ conjSubgroup hh (sA0 B m) := by
      rw [mem_conjSubgroup, show hh⁻¹ * (hh * (s * f) * hh⁻¹) * hh = s * f by group]
      exact ha
    rwa [heq] at this
  have h1 : (hh * (s * f) * hh⁻¹) * (s * f)⁻¹ ∈ sA0 B m :=
    (sA0 B m).mul_mem hmem ((sA0 B m).inv_mem ha)
  have h2 : (hh * (s * f) * hh⁻¹) * (s * f)⁻¹ = (hh * s * hh⁻¹) * s⁻¹ := by
    calc (hh * (s * f) * hh⁻¹) * (s * f)⁻¹
        = (hh * s * hh⁻¹) * (hh * f * hh⁻¹) * f⁻¹ * s⁻¹ := by group
      _ = (hh * s * hh⁻¹) * f * f⁻¹ * s⁻¹ := by rw [hh_cent_F0 T hf]
      _ = (hh * s * hh⁻¹) * s⁻¹ := by group
  rw [h2] at h1
  have h3 : (hh * s * hh⁻¹) * s⁻¹ ∈ sS B g m x :=
    (sS B g m x).mul_mem (hh_norm_S hCen hU d F T hs) ((sS B g m x).inv_mem hs)
  have h4 := A0_eq_one_of_mem_S d h1 h3
  have h5 : hh * s * hh⁻¹ * s⁻¹ ∈ sN B g x := by
    rw [h4]
    exact (sN B g x).one_mem
  have h6 : s ∈ sN B g x := T.fpf_S2 s (sS_le_sS2 hs) h5
  have h7 : s ∈ sC0 B g x := by
    have : s ∈ sS B g m x ⊓ sN B g x := ⟨hs, h6⟩
    rwa [F.S_inf_N] at this
  exact (hsf ha1).1 h7

theorem sA0_comm_conj (d : R2StarData h g m α x) (F : F0Facts B g m x)
    (T : TorusFacts B g x hh) :
    ∀ a ∈ sA0 B m, ∀ b ∈ conjSubgroup hh (sA0 B m), a * b = b * a :=
  fun a ha b hb => elemAbelian_comm F.elem_E a (sA0_le_sE F ha) b
    (conj_sA0_le_sE hCen hU d F T hb)

theorem card_L (d : R2StarData h g m α x) (F : F0Facts B g m x) (T : TorusFacts B g x hh) :
    Nat.card ↥(sA0 B m ⊔ conjSubgroup hh (sA0 B m)) = 16 := by
  have hs0 : IsSig B (sA0 B m) := isSig_sA0
  have hs1 : IsSig B (conjSubgroup hh (sA0 B m)) := hs0.conj hh
  have hinf : sA0 B m ⊓ conjSubgroup hh (sA0 B m) = ⊥ :=
    IsSig.inf_eq_bot h hs0 hs1 (conj_sA0_ne hCen hU d F T).symm
  rw [card_sup_of_commute (sA0_comm_conj hCen hU d F T) hinf, IsSig.card h hs0,
    IsSig.card h hs1]


theorem hh_norm_E (d : R2StarData h g m α x) (F : F0Facts B g m x) (T : TorusFacts B g x hh)
    {e : G} (he : e ∈ sE B g m x) : hh * e * hh⁻¹ ∈ sE B g m x := by
  have hN : sF0 B g m x ≤ Subgroup.normalizer (sS B g m x : Set G) :=
    le_normalizer_of_comm fun f hf s hs =>
      elemAbelian_comm F.elem_E f (sF0_le_sE hf) s (sS_le_sE hs)
  obtain ⟨s, hs, f, hf, rfl⟩ := exists_mul_of_mem_sup hN he
  have e1 : hh * (s * f) * hh⁻¹ = (hh * s * hh⁻¹) * (hh * f * hh⁻¹) := by group
  rw [e1, hh_cent_F0 T hf]
  exact (sE B g m x).mul_mem (sS_le_sE (hh_norm_S hCen hU d F T hs)) (sF0_le_sE hf)

theorem conj2_sA0_le_sE (d : R2StarData h g m α x) (F : F0Facts B g m x)
    (T : TorusFacts B g x hh) :
    conjSubgroup hh (conjSubgroup hh (sA0 B m)) ≤ sE B g m x :=
  conjSubgroup_le_of_norm (fun _ he => hh_norm_E hCen hU d F T he)
    (conj_sA0_le_sE hCen hU d F T)

theorem conj2_sA0_ne (d : R2StarData h g m α x) (F : F0Facts B g m x)
    (T : TorusFacts B g x hh) :
    conjSubgroup hh (conjSubgroup hh (sA0 B m)) ≠ sA0 B m := by
  intro heq
  apply conj_sA0_ne hCen hU d F T
  have := congrArg (conjSubgroup hh) heq
  rw [conj_conj_conj_eq T.pow_three] at this
  exact this.symm

theorem conj2_sA0_ne_conj (d : R2StarData h g m α x) (F : F0Facts B g m x)
    (T : TorusFacts B g x hh) :
    conjSubgroup hh (conjSubgroup hh (sA0 B m)) ≠ conjSubgroup hh (sA0 B m) := fun heq =>
  conj_sA0_ne hCen hU d F T (conjSubgroup_inj.1 heq)

theorem exists_triple (d : R2StarData h g m α x) (F : F0Facts B g m x)
    (T : TorusFacts B g x hh) {f : G} (hf : f ∈ sF0 B g m x) :
    ∃ a ∈ sA0 B m, f = a * (hh * a * hh⁻¹) * (hh * (hh * a * hh⁻¹) * hh⁻¹) := by
  obtain ⟨a, ha, s, hs, rfl⟩ := F.exists_A0_of_F0 f hf
  refine ⟨s * f, ha, ?_⟩
  have hs1 : hh * s * hh⁻¹ ∈ sS B g m x := hh_norm_S hCen hU d F T hs
  have hnorm := norm_identity (elemAbelian_comm F.elem_S) T.pow_three
    (fun s hs => hh_norm_S hCen hU d F T hs) (fun s hs hfix => hh_fix_S F T hs hfix) hs
  have e1 : hh * (s * f) * hh⁻¹ = (hh * s * hh⁻¹) * f := by
    calc hh * (s * f) * hh⁻¹ = (hh * s * hh⁻¹) * (hh * f * hh⁻¹) := by group
      _ = (hh * s * hh⁻¹) * f := by rw [hh_cent_F0 T hf]
  have e2 : hh * (hh * (s * f) * hh⁻¹) * hh⁻¹ = (hh * (hh * s * hh⁻¹) * hh⁻¹) * f := by
    rw [e1]
    calc hh * ((hh * s * hh⁻¹) * f) * hh⁻¹
        = (hh * (hh * s * hh⁻¹) * hh⁻¹) * (hh * f * hh⁻¹) := by group
      _ = (hh * (hh * s * hh⁻¹) * hh⁻¹) * f := by rw [hh_cent_F0 T hf]
  have hff : f * f = 1 := elemAbelian_sq F.elem_F0 f hf
  have hfs1 : f * (hh * s * hh⁻¹) = (hh * s * hh⁻¹) * f :=
    elemAbelian_comm F.elem_E f (sF0_le_sE hf) _ (sS_le_sE hs1)
  rw [e2, e1]
  generalize hs1def : hh * s * hh⁻¹ = s1 at hnorm hfs1 ⊢
  generalize hs2def : hh * s1 * hh⁻¹ = s2 at hnorm ⊢
  calc f = (s * s1 * s2) * f := by rw [hnorm, one_mul]
    _ = s * s1 * (f * f) * (s2 * f) := by rw [hff]; group
    _ = s * (s1 * f) * f * (s2 * f) := by group
    _ = s * (f * s1) * f * (s2 * f) := by rw [hfs1]
    _ = s * f * (s1 * f) * (s2 * f) := by group

theorem sF0_le_sup3 (d : R2StarData h g m α x) (F : F0Facts B g m x)
    (T : TorusFacts B g x hh) :
    sF0 B g m x ≤ sA0 B m ⊔ conjSubgroup hh (sA0 B m) ⊔
      conjSubgroup hh (conjSubgroup hh (sA0 B m)) := by
  intro f hf
  obtain ⟨a, ha, hfa⟩ := exists_triple hCen hU d F T hf
  rw [hfa]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (conj_mem_conjSubgroup hh ha))))
    (Subgroup.mem_sup_right (conj_mem_conjSubgroup hh (conj_mem_conjSubgroup hh ha)))

theorem L_inf_C0 (d : R2StarData h g m α x) (F : F0Facts B g m x) (T : TorusFacts B g x hh) :
    (sA0 B m ⊔ conjSubgroup hh (sA0 B m)) ⊓ sC0 B g x = ⊥ := by
  rw [eq_bot_iff]
  intro l hl
  obtain ⟨hlL, hlC⟩ := Subgroup.mem_inf.mp hl
  rw [Subgroup.mem_bot]
  have hnorm : conjSubgroup hh (sA0 B m) ≤ Subgroup.normalizer (sA0 B m : Set G) :=
    le_normalizer_of_comm fun b hb a ha => (sA0_comm_conj hCen hU d F T a ha b hb).symm
  obtain ⟨a, ha, b', hb', rfl⟩ := exists_mul_of_mem_sup hnorm hlL
  obtain ⟨s, hs, f, hf, hsf, hne⟩ := sA0_decomp F ha
  have hb : hh⁻¹ * b' * hh ∈ sA0 B m := mem_conjSubgroup.mp hb'
  obtain ⟨t, ht, f', hf', htf, -⟩ := sA0_decomp F hb
  have hb'eq : b' = (hh * t * hh⁻¹) * f' := by
    calc b' = hh * (hh⁻¹ * b' * hh) * hh⁻¹ := by group
      _ = hh * (t * f') * hh⁻¹ := by rw [htf]
      _ = (hh * t * hh⁻¹) * (hh * f' * hh⁻¹) := by group
      _ = (hh * t * hh⁻¹) * f' := by rw [hh_cent_F0 T hf']
  have ht' : hh * t * hh⁻¹ ∈ sS B g m x := hh_norm_S hCen hU d F T ht
  have hSc := elemAbelian_comm F.elem_S
  have hEc := elemAbelian_comm F.elem_E
  have hl2 : a * b' = (s * (hh * t * hh⁻¹)) * (f * f') := by
    rw [hsf, hb'eq]
    have hft : f * (hh * t * hh⁻¹) = (hh * t * hh⁻¹) * f :=
      hEc f (sF0_le_sE hf) _ (sS_le_sE ht')
    calc s * f * (hh * t * hh⁻¹ * f') = s * (f * (hh * t * hh⁻¹)) * f' := by group
      _ = s * ((hh * t * hh⁻¹) * f) * f' := by rw [hft]
      _ = (s * (hh * t * hh⁻¹)) * (f * f') := by group
  have hlS : a * b' ∈ sS B g m x := sC0_le_sS F hlC
  have hss : s * (hh * t * hh⁻¹) ∈ sS B g m x := (sS B g m x).mul_mem hs ht'
  have hff' : f * f' ∈ sS B g m x ⊓ sF0 B g m x := by
    refine ⟨?_, (sF0 B g m x).mul_mem hf hf'⟩
    have : f * f' = (s * (hh * t * hh⁻¹))⁻¹ * (a * b') := by
      rw [hl2]
      group
    rw [this]
    exact (sS B g m x).mul_mem ((sS B g m x).inv_mem hss) hlS
  rw [F.S_inf_F0, Subgroup.mem_bot] at hff'
  have hff : f * f = 1 := elemAbelian_sq F.elem_F0 f hf
  have hf'f : f' = f := by
    rw [eq_inv_of_mul_eq_one_right hff']
    exact inv_eq_of_mul_eq_one_right hff
  have hsa : s * f ∈ sA0 B m := hsf ▸ ha
  have hb2 : t * f ∈ sA0 B m := by
    rw [← hf'f, ← htf]
    exact hb
  have hst : s * f = t * f := sA0_eq_of_same_F0 d hs ht hsa hb2
  have hst' : s = t := mul_right_cancel hst
  subst hst'
  have hlC0 : s * (hh * s * hh⁻¹) ∈ sC0 B g x := by
    have : s * (hh * s * hh⁻¹) = a * b' := by
      rw [hl2, hff', mul_one]
    rw [this]
    exact hlC
  have hs2 : s * s = 1 := elemAbelian_sq F.elem_S s hs
  have hcomm_N : hh * s * hh⁻¹ * s⁻¹ ∈ sN B g x := by
    have e : hh * s * hh⁻¹ * s⁻¹ = s * (hh * s * hh⁻¹) := by
      rw [inv_eq_of_mul_eq_one_right hs2]
      exact hSc _ ht' s hs
    rw [e]
    exact sC0_le_sN hlC0
  have hsN : s ∈ sN B g x := T.fpf_S2 s (sS_le_sS2 hs) hcomm_N
  have hsC0 : s ∈ sC0 B g x := by
    have : s ∈ sS B g m x ⊓ sN B g x := ⟨hs, hsN⟩
    rwa [F.S_inf_N] at this
  have ha1 : a = 1 := by
    by_contra ha1
    exact (hne ha1).1 hsC0
  have hb1 : hh⁻¹ * b' * hh = 1 := by
    rw [htf, hf'f, ← hsf, ha1]
  have hb'1 : b' = 1 := by
    calc b' = hh * (hh⁻¹ * b' * hh) * hh⁻¹ := by group
      _ = 1 := by rw [hb1]; group
  rw [ha1, hb'1, one_mul]

theorem eq_one_of_cent_A1 (d : R2StarData h g m α x) {w : G} (hw : w ∈ sC0 B g x)
    (hc : ∀ u ∈ conjSubgroup m (omegaTwoSub B), u * w = w * u) : w = 1 := by
  have P := d.data31.pairAC hCen hU
  obtain ⟨u, hu, hu2⟩ := Pair.exists_sq_ne_conj h m
  have hu' : u ∈ conjSubgroup (m * g⁻¹) (sD1 B g) := by
    have : conjSubgroup (m * g⁻¹) (sD1 B g) = conjSubgroup m (omegaTwoSub B) := by
      show conjSubgroup (m * g⁻¹) (conjSubgroup g (omegaTwoSub B)) = _
      rw [← conjSubgroup_mul, inv_mul_cancel_right]
    rw [this]
    exact hu
  have hu0 : u ∉ omegaOneSub (conjSubgroup (m * g⁻¹) (sD1 B g)) := by
    rw [omega_conj_sD1 h g m]
    intro hu0
    apply hu2
    rw [sq]
    exact Pair.sq_conj_B0 h hu0
  have hn : w ∈ omegaOneSub (conjSubgroup (m * g⁻¹) (sD1 B g)) ⊔
      omegaOneSub (conjSubgroup x (sD1 B g)) := Subgroup.mem_sup_right hw
  have h1 := P.cent hCen hU hu' hu0 hn (hc u hu)
  have h2 : w ∈ conjSubgroup (m * g⁻¹) (sD1 B g) ⊓ conjSubgroup x (sD1 B g) :=
    Subgroup.mem_inf.mpr ⟨omegaOneSub_le _ h1, omegaOneSub_le _ hw⟩
  rw [d.data31.inf_AC hCen hU, Subgroup.mem_bot] at h2
  exact h2

theorem sup3_inf_C0 (d : R2StarData h g m α x) (T : TorusFacts B g x hh)
    (hcomm1 : ∀ a ∈ conjSubgroup m (omegaTwoSub B), ∀ b ∈ conjSubgroup (hh * m) (omegaTwoSub B),
      a * b = b * a) :
    (sA0 B m ⊔ conjSubgroup hh (sA0 B m) ⊔ conjSubgroup hh (conjSubgroup hh (sA0 B m))) ⊓
      sC0 B g x = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwW, hwC⟩ := Subgroup.mem_inf.mp hw
  exact Subgroup.mem_bot.mpr (eq_one_of_cent_A1 hCen hU d hwC fun u hu =>
    Subgroup.mem_centralizer_iff.mp (sup3_le_cent_A1 h T hcomm1 hwW) u hu)

theorem sup3_eq_L (d : R2StarData h g m α x) (F : F0Facts B g m x) (T : TorusFacts B g x hh)
    (hcomm1 : ∀ a ∈ conjSubgroup m (omegaTwoSub B), ∀ b ∈ conjSubgroup (hh * m) (omegaTwoSub B),
      a * b = b * a) :
    sA0 B m ⊔ conjSubgroup hh (sA0 B m) =
      sA0 B m ⊔ conjSubgroup hh (sA0 B m) ⊔ conjSubgroup hh (conjSubgroup hh (sA0 B m)) :=
  eq_of_card_sixteen le_sup_left
    (sup_le (sup_le (sA0_le_sE F) (conj_sA0_le_sE hCen hU d F T)) (conj2_sA0_le_sE hCen hU d F T))
    (sC0_le_sV.trans (sV_le_sE F)) (elemAbelian_comm F.elem_E) F.card_E F.card_C0
    (card_L hCen hU d F T) (sup3_inf_C0 hCen hU d T hcomm1)

theorem conj2_sA0_le_L (d : R2StarData h g m α x) (F : F0Facts B g m x)
    (T : TorusFacts B g x hh)
    (hcomm1 : ∀ a ∈ conjSubgroup m (omegaTwoSub B), ∀ b ∈ conjSubgroup (hh * m) (omegaTwoSub B),
      a * b = b * a) :
    conjSubgroup hh (conjSubgroup hh (sA0 B m)) ≤ sA0 B m ⊔ conjSubgroup hh (sA0 B m) :=
  le_sup_right.trans (sup3_eq_L hCen hU d F T hcomm1).symm.le

theorem F0_isSig_case2 (d : R2StarData h g m α x) (F : F0Facts B g m x)
    (T : TorusFacts B g x hh)
    (hcomm1 : ∀ a ∈ conjSubgroup m (omegaTwoSub B), ∀ b ∈ conjSubgroup (hh * m) (omegaTwoSub B),
      a * b = b * a) :
    IsSig B (sF0 B g m x) := by
  have hne : conjSubgroup (hh * m) (omegaTwoSub B) ≠ conjSubgroup m (omegaTwoSub B) := by
    intro heq
    apply conj_sA0_ne hCen hU d F T
    have := congrArg omegaOneSub heq
    rw [Pair.omegaOne_conj_U h, Pair.omegaOne_conj_U h, conjSubgroup_mul] at this
    exact this
  obtain ⟨w, hw, hwnc⟩ := h.exists_noncomm_delta (f := m) (g' := hh * m)
    (fun z hz => Subgroup.mem_centralizer_iff.mpr fun u hu => hcomm1 u hu z hz) hne
  have hsig : SigCover B
      (conjSubgroup m (omegaOneSub B) ⊔ conjSubgroup (hh * m) (omegaOneSub B)) :=
    sigCover_of_witness hCen hU h d.gamma_comm (e := m) (e' := hh * m) (w := w)
      (fun heq => conj_sA0_ne hCen hU d F T (by rw [conjSubgroup_mul] at heq; exact heq.symm))
      hcomm1 hw hwnc (F'' := conjSubgroup hh (conjSubgroup hh (sA0 B m)))
      ((isSig_sA0.conj hh).conj hh)
      (by rw [conjSubgroup_mul]; exact conj2_sA0_le_L hCen hU d F T hcomm1)
      (conj2_sA0_ne hCen hU d F T)
      (by rw [conjSubgroup_mul]; exact conj2_sA0_ne_conj hCen hU d F T)
  rw [conjSubgroup_mul] at hsig
  obtain ⟨hZsig, hZcard⟩ := lc_member d F (L := sA0 B m ⊔ conjSubgroup hh (sA0 B m))
    (sup_le (sA0_le_sE F) (conj_sA0_le_sE hCen hU d F T)) (card_L hCen hU d F T)
    (L_inf_C0 hCen hU d F T) hsig
  have hF0Z : sF0 B g m x ≤ (sA0 B m ⊔ conjSubgroup hh (sA0 B m)) ⊓ sV B g m x :=
    le_inf ((sF0_le_sup3 hCen hU d F T).trans (sup3_eq_L hCen hU d F T hcomm1).symm.le)
      sF0_le_sV
  have heq : sF0 B g m x = (sA0 B m ⊔ conjSubgroup hh (sA0 B m)) ⊓ sV B g m x :=
    Subgroup.eq_of_le_of_card_ge hF0Z (by rw [hZcard, F.card_F0])
  rw [heq]
  exact hZsig


theorem F0_isSig_of_Z (d : R2StarData h g m α x) (F : F0Facts B g m x) (T : TorusFacts B g x hh)
    {Z : Subgroup G} (hZsig : IsSig B Z) (hZV : Z ≤ sV B g m x)
    (hZC : Z ⊓ sC0 B g x = ⊥) (hZcard : Nat.card ↥Z = 4) : IsSig B (sF0 B g m x) := by
  by_cases hZF : Z = sF0 B g m x
  · rw [← hZF]
    exact hZsig
  have hZnbot : Z ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hZcard
    omega
  have hZC' : ¬ Z = sC0 B g x := fun hq => hZnbot (by rw [← hZC, ← hq, inf_idem])
  obtain ⟨z0, hz0⟩ := hZsig
  have hZsig' : IsSig B Z := ⟨z0, hz0⟩
  have hZh : conjSubgroup hh Z ≠ Z := by
    intro hzz
    apply hZF
    refine Subgroup.eq_of_le_of_card_ge (fun z hz => ?_) (by rw [hZcard, F.card_F0])
    obtain ⟨c, hc, f, hf, rfl⟩ := sV_decomp F (hZV hz)
    have h1 : hh * (c * f) * hh⁻¹ ∈ Z := by
      have : hh * (c * f) * hh⁻¹ ∈ conjSubgroup hh Z := conj_mem_conjSubgroup hh hz
      rwa [hzz] at this
    have h2 : (hh * c * hh⁻¹) * c⁻¹ ∈ Z ⊓ sC0 B g x := by
      refine ⟨?_, (sC0 B g x).mul_mem (hh_norm_C0 d T hc) ((sC0 B g x).inv_mem hc)⟩
      have e : (hh * c * hh⁻¹) * c⁻¹ = (hh * (c * f) * hh⁻¹) * (c * f)⁻¹ := by
        calc (hh * c * hh⁻¹) * c⁻¹ = (hh * c * hh⁻¹) * f * f⁻¹ * c⁻¹ := by group
          _ = (hh * c * hh⁻¹) * (hh * f * hh⁻¹) * f⁻¹ * c⁻¹ := by rw [hh_cent_F0 T hf]
          _ = (hh * (c * f) * hh⁻¹) * (c * f)⁻¹ := by group
      rw [e]
      exact Z.mul_mem h1 (Z.inv_mem hz)
    rw [hZC, Subgroup.mem_bot, mul_inv_eq_one] at h2
    have hc1 : c = 1 := T.fpf_C0 c hc h2
    rw [hc1, one_mul]
    exact hf
  have hZcomm : ∀ a ∈ sC0 B g x, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    elemAbelian_comm F.elem_E a (sV_le_sE F (sC0_le_sV ha)) b (sV_le_sE F (hZV hb))
  have hV_eq : sC0 B g x ⊔ Z = sV B g m x := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le sC0_le_sV hZV) ?_
    rw [card_sup_of_commute hZcomm (by rw [inf_comm]; exact hZC), F.card_C0, hZcard, card_sV F]
  have hcomm1 : ∀ a ∈ conjSubgroup (x * g) (omegaTwoSub B),
      ∀ b ∈ conjSubgroup z0 (omegaTwoSub B), a * b = b * a := by
    by_contra hnc
    have hcommB0 : ∀ a ∈ conjSubgroup (x * g) (omegaOneSub B),
        ∀ b ∈ conjSubgroup z0 (omegaOneSub B), a * b = b * a := fun a ha b hb => by
      rw [← sC0_eq_conj h g x] at ha
      rw [← hz0] at hb
      exact hZcomm a ha b hb
    have P := ncpair_of_noncomm h hcommB0 hnc
    obtain ⟨c, hc, hcC0⟩ := F.exists_C1_not_C0
    obtain ⟨⟨ζ, hζ⟩, hζ1⟩ : ∃ a : ↥Z, a ≠ 1 := by
      apply Subgroup.ne_bot_iff_exists_ne_one.mp
      exact hZnbot
    have hζ1' : ζ ≠ 1 := fun e => hζ1 (Subtype.ext e)
    rw [sC1_eq_conj] at hc
    have hcC0' : c ∉ omegaOneSub (conjSubgroup (x * g) (omegaTwoSub B)) := by
      rw [Pair.omegaOne_conj_U h, ← sC0_eq_conj h g x]
      exact hcC0
    have hζn : ζ ∈ omegaOneSub (conjSubgroup (x * g) (omegaTwoSub B)) ⊔
        omegaOneSub (conjSubgroup z0 (omegaTwoSub B)) := by
      refine Subgroup.mem_sup_right ?_
      rw [Pair.omegaOne_conj_U h, ← hz0]
      exact hζ
    have hcζ : c * ζ = ζ * c := by
      have := sV_le_cent_C1 d (hZV hζ)
      rw [sC1_eq_conj] at this
      exact Subgroup.mem_centralizer_iff.mp this c hc
    have h1 := P.cent hCen hU hc hcC0' hζn hcζ
    rw [Pair.omegaOne_conj_U h, ← sC0_eq_conj h g x] at h1
    have h2 : ζ ∈ Z ⊓ sC0 B g x := ⟨hζ, h1⟩
    rw [hZC, Subgroup.mem_bot] at h2
    exact hζ1' h2
  have hw : conjSubgroup 1 (omegaTwoSub B) ≤
      Subgroup.centralizer (conjSubgroup (x * g) (omegaTwoSub B) : Set G) := by
    rw [conjSubgroup_one]
    intro u hu
    refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
    have hc' : c ∈ conjSubgroup x (conjSubgroup g (omegaTwoSub B)) := by
      rw [← conjSubgroup_mul]
      exact hc
    exact (Subgroup.mem_centralizer_iff.mp (d.cent_C hc') u hu).symm
  have hwnc : ¬ ∀ a ∈ conjSubgroup 1 (omegaTwoSub B), ∀ b ∈ conjSubgroup z0 (omegaTwoSub B),
      a * b = b * a := by
    intro hall
    rw [conjSubgroup_one] at hall
    have hZU : ∀ ζ ∈ Z, ∀ u ∈ omegaTwoSub B, u * ζ = ζ * u := fun ζ hζ u hu =>
      hall u hu ζ (by rw [hz0] at hζ; exact Pair.conj_B0_le_U h z0 hζ)
    have hZbot : Z = ⊥ := by
      rw [eq_bot_iff]
      intro ζ hζ
      obtain ⟨c, hc, f, hf, rfl⟩ := sV_decomp F (hZV hζ)
      have hcU : ∀ u ∈ omegaTwoSub B, u * c = c * u := fun u hu =>
        Subgroup.mem_centralizer_iff.mp (d.cent_C (omegaOneSub_le _ hc)) u hu
      have hfU : ∀ u ∈ omegaTwoSub B, u * f = f * u := fun u hu => by
        have h1 := hZU _ hζ u hu
        have h2 := hcU u hu
        calc u * f = c⁻¹ * (c * u) * f := by group
          _ = c⁻¹ * (u * c) * f := by rw [h2]
          _ = c⁻¹ * (u * (c * f)) := by group
          _ = c⁻¹ * ((c * f) * u) := by rw [h1]
          _ = f * u := by group
      obtain ⟨a, ha, s, hs, has⟩ := F.exists_A0_of_F0 f hf
      have hsU : ∀ u ∈ omegaTwoSub B, u * s = s * u := fun u hu =>
        Subgroup.mem_centralizer_iff.mp (sX_le_cent d (sS2_le_sX (sS_le_sS2 hs))) u hu
      have haU : a ∈ Subgroup.centralizer (omegaTwoSub B : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        rw [has]
        calc u * (s * f) = (u * s) * f := by group
          _ = (s * u) * f := by rw [hsU u hu]
          _ = s * (u * f) := by group
          _ = s * (f * u) := by rw [hfU u hu]
          _ = (s * f) * u := by group
      have ha1 : a = 1 := d.inf_cent a ha haU
      have hf1 : f = 1 := by
        have h1 : s * f = 1 := by rw [← has]; exact ha1
        have hfs : f = s⁻¹ := eq_inv_of_mul_eq_one_right h1
        have hmem : f ∈ sS B g m x ⊓ sF0 B g m x :=
          ⟨by rw [hfs]; exact (sS B g m x).inv_mem hs, hf⟩
        rw [F.S_inf_F0, Subgroup.mem_bot] at hmem
        exact hmem
      subst hf1
      rw [mul_one] at hζ ⊢
      have h2 : c ∈ Z ⊓ sC0 B g x := ⟨hζ, hc⟩
      rw [hZC] at h2
      exact h2
    exact hZnbot hZbot
  have hZhV : conjSubgroup hh Z ≤ conjSubgroup (x * g) (omegaOneSub B) ⊔
      conjSubgroup z0 (omegaOneSub B) := by
    rw [← sC0_eq_conj h g x, ← hz0, hV_eq]
    intro z hz
    have := hh_norm_V d F T (hZV (mem_conjSubgroup.mp hz))
    rwa [show hh * (hh⁻¹ * z * hh) * hh⁻¹ = z by group] at this
  have hsigV : SigCover B (conjSubgroup (x * g) (omegaOneSub B) ⊔
      conjSubgroup z0 (omegaOneSub B)) :=
    sigCover_of_witness hCen hU h d.gamma_comm (e := x * g) (e' := z0) (w := 1)
      (fun heq => hZC' (by rw [← sC0_eq_conj h g x, ← hz0] at heq; exact heq.symm))
      hcomm1 hw hwnc (F'' := conjSubgroup hh Z) (hZsig'.conj hh) hZhV
      (fun heq => hZC' (by
        rw [← sC0_eq_conj h g x, ← conj_sC0_eq d T] at heq
        exact conjSubgroup_inj.1 heq))
      (fun heq => hZh (by rw [← hz0] at heq; exact heq))
  rw [← sC0_eq_conj h g x, ← hz0, hV_eq] at hsigV
  exact fin_generic (IsSig B) (fun Q Q' hQ hQ' => isSig_ti h hQ hQ') (fun Q k hQ => hQ.conj k)
    (fun Q hQ => IsSig.card h hQ) (V := sV B g m x) (C₀ := sC0 B g x) (F₀ := sF0 B g m x)
    (h := hh) ⟨x * g, sC0_eq_conj h g x⟩ F.card_F0 (sC0_inf_sF0 F) (fun v hv => sV_decomp F hv)
    (fun c hc => hh_norm_C0 d T hc) (fun f hf => hh_cent_F0 T hf) T.fpf_C0 hsigV sF0_le_sV

theorem F0_isSig_case1 (d : R2StarData h g m α x) (F : F0Facts B g m x)
    (T : TorusFacts B g x hh)
    (hnc : ¬ ∀ a ∈ conjSubgroup m (omegaTwoSub B), ∀ b ∈ conjSubgroup (hh * m) (omegaTwoSub B),
      a * b = b * a) :
    IsSig B (sF0 B g m x) := by
  have hcov : SigCover B (sA0 B m ⊔ conjSubgroup hh (sA0 B m)) := by
    have := sigCover_of_ncpair hCen hU h (e := m) (e' := hh * m) (fun a ha b hb =>
      sA0_comm_conj hCen hU d F T a ha b (by rwa [conjSubgroup_mul] at hb)) hnc
    rwa [conjSubgroup_mul] at this
  obtain ⟨hZsig, hZcard⟩ := lc_member d F (L := sA0 B m ⊔ conjSubgroup hh (sA0 B m))
    (sup_le (sA0_le_sE F) (conj_sA0_le_sE hCen hU d F T)) (card_L hCen hU d F T)
    (L_inf_C0 hCen hU d F T) hcov
  refine F0_isSig_of_Z hCen hU d F T hZsig inf_le_right ?_ hZcard
  rw [eq_bot_iff]
  intro z hz
  have : z ∈ (sA0 B m ⊔ conjSubgroup hh (sA0 B m)) ⊓ sC0 B g x := ⟨hz.1.1, hz.2⟩
  rw [L_inf_C0 hCen hU d F T] at this
  exact this

theorem F0_isSig_of_facts (d : R2StarData h g m α x) (F : F0Facts B g m x)
    (T : TorusFacts B g x hh) : IsSig B (sF0 B g m x) := by
  by_cases hc : ∀ a ∈ conjSubgroup m (omegaTwoSub B), ∀ b ∈ conjSubgroup (hh * m) (omegaTwoSub B),
      a * b = b * a
  · exact F0_isSig_case2 hCen hU d F T hc
  · exact F0_isSig_case1 hCen hU d F T hc


end Cert

end Config

section Wire

variable {M B : Subgroup G} {h : R2 M B} {g m α x : G}

variable [Finite G]

theorem R2StarData.f0Facts (d : R2StarData h g m α x) : F0Facts B g m x :=
  ⟨d.card_C0, d.card_C1, d.exists_C1_not_C0, d.card_F0, d.isElemAbelian_F0, d.F0_inf_X,
    d.exists_mul_S_F0, d.exists_A0_of_F0, d.S_mul_F0, d.S_inf_F0, d.isElemAbelian_S, d.card_S,
    d.card_N, d.card_S2, d.S_inf_N, d.isElemAbelian_E, d.card_E, d.comm_C1_E, d.cent_E,
    d.F0_faithful⟩

theorem R2StarData.exists_torusFacts (d : R2StarData h g m α x) :
    ∃ hh : G, TorusFacts B g x hh := by
  have hCen := CFSG.CGT.T75N.benderCenterInput
  have hU := CFSG.CGT.T75N.unitaryTwoGenerationInput
  obtain ⟨K, hKX, hK3, -, hKC, hfC, -, -, hS2C⟩ := d.data31.exists_torus hCen hU
  have hKne : K ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hK3
    omega
  obtain ⟨⟨k, hk⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
  have hk1' : k ≠ 1 := fun e => hk1 (Subtype.ext e)
  have hk3 : k ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := ↥K) (x := ⟨k, hk⟩)
    rw [hK3] at h1
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  refine ⟨k, hk3, hk1', hKX hk, hKC hk, fun c hc hkc => hfC k hk hk1' c hc hkc, ?_⟩
  intro s hs hsN
  obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_of_mem_sup (sC1_le_normalizer_N hCen hU d) hs
  have hkn : k * n * k⁻¹ ∈ sN B g x := (X_conj_N_iff hCen hU d (hKX hk) n).mpr hn
  have hkc : k * c * k⁻¹ * c⁻¹ ∈ sN B g x := by
    have e : k * c * k⁻¹ * c⁻¹ =
        (k * n * k⁻¹)⁻¹ * (k * (n * c) * k⁻¹ * (n * c)⁻¹) * n := by group
    rw [e]
    exact (sN B g x).mul_mem ((sN B g x).mul_mem ((sN B g x).inv_mem hkn) hsN) hn
  have hc0 : c ∈ sC0 B g x := hS2C k hk hk1' c hc hkc
  exact (sN B g x).mul_mem hn (sC0_le_sN hc0)

theorem R2StarData.F0_isSig (d : R2StarData h g m α x) : IsSig B (sF0 B g m x) := by
  obtain ⟨hh, T⟩ := d.exists_torusFacts
  exact F0_isSig_of_facts CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput d d.f0Facts T

end Wire

section Final


theorem r2StarLocal_holds : R2StarLocal := by
  intro G _ _ M B h g m α x d
  obtain ⟨y, hy⟩ := d.F0_isSig
  exact weakEnd_core CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput d (X := sX B g x) (F₀ := sF0 B g m x)
    (d.data31.sup_eq CFSG.CGT.T75N.benderCenterInput CFSG.CGT.T75N.unitaryTwoGenerationInput
      d.data31.mem d.data31.ne_one).symm ⟨y, hy⟩ inf_le_right d.exists_mul_X_F0

theorem r2Weak_holds : R2Weak := r2Weak_of_local r2StarLocal_holds

end Final

end CFSG.CGT.PushingUpLit.SolKR2
