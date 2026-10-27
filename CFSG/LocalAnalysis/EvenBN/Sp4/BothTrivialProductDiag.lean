module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProduct
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialProduct

open Subgroup CFSG.Blueprint CFSG.Open
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer BothTrivialRankOne BothTrivialSlice BothTrivialField
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.LocalAnalysis.EvenBN.Common (prodFst prodFstHom)
open scoped MatrixGroups

section Abstract

variable {G : Type*} [Group G] {S : Type*} [Group S]

structure ProductDiagData (N X P : Subgroup G) (t : G) (ρ : N →* S × S) : Prop where
  surj : Function.Surjective ρ
  ker : ρ.ker = X.subgroupOf N
  X_le : X ≤ N
  X_sq : ∀ x ∈ X, x * x = 1
  X_comm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x
  t_mem : t ∈ normalizer (N : Set G)
  t_sq : t * t = 1
  swap : ∀ x y : N, (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap
  le_prodFst : P ≤ prodFst ρ
  perfect : ⁅P, P⁆ = P
  sup_X : P ⊔ X = prodFst ρ
  comm_conj : ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥
  max : ∀ Q : Subgroup G, Q ≤ prodFst ρ → ⁅Q, Q⁆ = Q → Q ≤ P

theorem diag_mem_map_conj_iff {t : G} (ht2 : t * t = 1) {H : Subgroup G} {y : G} :
    y ∈ H.map (MulAut.conj t).toMonoidHom ↔ t * y * t⁻¹ ∈ H := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, hti]

theorem diag_conj_conj {t : G} (ht2 : t * t = 1) (x : G) :
    t * (t * x * t⁻¹) * t⁻¹ = x := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [hti]
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
    _ = x := by rw [ht2]; group

theorem diag_exists_mul_of_mem_sup {Y Y' : Subgroup G} (h : ∀ a ∈ Y, ∀ b ∈ Y', a * b = b * a)
    {g : G} (hg : g ∈ Y ⊔ Y') : ∃ a ∈ Y, ∃ b ∈ Y', g = a * b := by
  have hle : Y ≤ normalizer (Y' : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer (Y' : Set G)
      (mem_centralizer_iff.2 fun b hb => (h a ha b hb).symm)
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right Y Y' hle] at hg
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  exact ⟨a, ha, b, hb, rfl⟩

namespace ProductDiagData

variable {N X P : Subgroup G} {t : G} {ρ : N →* S × S} (d : ProductDiagData N X P t ρ)
include d

theorem P_le : P ≤ N := d.le_prodFst.trans (Common.prodFst_le ρ)

theorem t_mem_X : t ∈ normalizer (X : Set G) :=
  Common.mem_normalizer_ker_of_swap d.t_mem d.swap d.X_le d.ker

theorem N_le_normalizer : N ≤ normalizer (X : Set G) := Common.le_normalizer_of_ker d.X_le d.ker

theorem conj_mem_P {n p : G} (hn : n ∈ N) (hp : p ∈ P) : n * p * n⁻¹ ∈ P := by
  have hQ : P.map (MulAut.conj n).toMonoidHom ≤ P := by
    refine d.max _ ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact Common.conj_mem_prodFst ρ hn (d.le_prodFst hq)
    · rw [← Subgroup.map_commutator, d.perfect]
  exact hQ ⟨p, hp, rfl⟩

theorem conj_mem_X {n x : G} (hn : n ∈ N) (hx : x ∈ X) : n * x * n⁻¹ ∈ X :=
  (mem_normalizer_iff.1 (d.N_le_normalizer hn) x).1 hx

theorem conj_t_mem_N {n : G} (hn : n ∈ N) : t * n * t⁻¹ ∈ N :=
  (mem_normalizer_iff.1 d.t_mem n).1 hn

theorem conj_t_mem_X {x : G} (hx : x ∈ X) : t * x * t⁻¹ ∈ X :=
  (mem_normalizer_iff.1 d.t_mem_X x).1 hx

theorem mem_X_of_mem_inf {z : G} (hz : z ∈ P) (hz' : z ∈ P.map (MulAut.conj t).toMonoidHom) :
    z ∈ X := by
  have h1 : z ∈ prodFst ρ := d.le_prodFst hz
  have h2 : z ∈ (prodFst ρ).map (MulAut.conj t).toMonoidHom := Subgroup.map_mono d.le_prodFst hz'
  obtain ⟨hzN, hz2⟩ := (Common.mem_prodFst_iff ρ).1 h1
  obtain ⟨_, hz1⟩ := (Common.mem_map_conj_prodFst_iff d.t_mem d.t_sq d.swap).1 h2
  have hk : (⟨z, hzN⟩ : N) ∈ ρ.ker := Prod.ext hz1 hz2
  rw [d.ker, mem_subgroupOf] at hk
  exact hk

theorem mem_centralizer_of_mem_inf {z : G} (hz : z ∈ P)
    (hz' : z ∈ P.map (MulAut.conj t).toMonoidHom) : z ∈ centralizer (N : Set G) := by
  have hzX := d.mem_X_of_mem_inf hz hz'
  have hPz : P ≤ centralizer ({z} : Set G) := fun p hp =>
    mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 d.comm_conj hp) z hz').symm
  have hPtz : P.map (MulAut.conj t).toMonoidHom ≤ centralizer ({z} : Set G) := fun p hp =>
    mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 d.comm_conj hz) p hp)
  have hXz : X ≤ centralizer ({z} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.2 (d.X_comm x hx z hzX)
  have hΛ : prodFst ρ ≤ centralizer ({z} : Set G) := d.sup_X.ge.trans (sup_le hPz hXz)
  have hΛt : (prodFst ρ).map (MulAut.conj t).toMonoidHom ≤ centralizer ({z} : Set G) := by
    refine (Subgroup.map_mono d.sup_X.ge).trans ?_
    rw [Subgroup.map_sup, Common.map_conj_eq_of_mem_normalizer d.t_mem_X]
    exact sup_le hPtz hXz
  have hN : N ≤ centralizer ({z} : Set G) :=
    (Common.prodFst_sup_map_conj d.t_mem d.t_sq d.swap d.surj).ge.trans (sup_le hΛ hΛt)
  exact mem_centralizer_iff.2 fun n hn => mem_centralizer_singleton_iff.1 (hN hn)

theorem delta_comm {p : G} (hp : p ∈ P) :
    t * (p * (t * p * t⁻¹)) = (p * (t * p * t⁻¹)) * t := by
  have hq : t * p * t⁻¹ ∈ P.map (MulAut.conj t).toMonoidHom := ⟨p, hp, rfl⟩
  have hc := mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 d.comm_conj hp) _ hq
  have h1 : t * (p * (t * p * t⁻¹)) * t⁻¹ = p * (t * p * t⁻¹) := by
    calc t * (p * (t * p * t⁻¹)) * t⁻¹ = (t * p * t⁻¹) * (t * (t * p * t⁻¹) * t⁻¹) := by group
      _ = (t * p * t⁻¹) * p := by rw [diag_conj_conj d.t_sq]
      _ = p * (t * p * t⁻¹) := hc
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem delta_mem_N {p : G} (hp : p ∈ P) : p * (t * p * t⁻¹) ∈ N :=
  mul_mem (d.P_le hp) (d.conj_t_mem_N (d.P_le hp))

theorem delta_mul {a b : G} (ha : a ∈ P) (hb : b ∈ P) :
    (a * b) * (t * (a * b) * t⁻¹) = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by
  have hq : t * a * t⁻¹ ∈ P.map (MulAut.conj t).toMonoidHom := ⟨a, ha, rfl⟩
  have hc := mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 d.comm_conj hb) _ hq
  calc (a * b) * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
    _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [hc]
    _ = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by group

@[expose] def delta : P →* G :=
  MonoidHom.mk' (fun a => (a : G) * (t * a * t⁻¹)) fun a b => d.delta_mul a.2 b.2

theorem delta_apply (a : P) : d.delta a = (a : G) * (t * a * t⁻¹) := rfl

theorem rho_delta {p : G} (hp : p ∈ P) :
    ρ ⟨p * (t * p * t⁻¹), d.delta_mem_N hp⟩ =
      ((ρ ⟨p, d.P_le hp⟩).1, (ρ ⟨p, d.P_le hp⟩).1) := by
  have hpN := d.P_le hp
  have h1 : ρ ⟨t * p * t⁻¹, d.conj_t_mem_N hpN⟩ = (ρ ⟨p, hpN⟩).swap := d.swap _ _ rfl
  obtain ⟨_, h2⟩ := (Common.mem_prodFst_iff ρ).1 (d.le_prodFst hp)
  change ρ (⟨p, hpN⟩ * ⟨t * p * t⁻¹, d.conj_t_mem_N hpN⟩) = _
  rw [map_mul, h1]
  refine Prod.ext ?_ ?_
  · simp [h2]
  · simp [h2]

theorem rho_eq_diag {c : G} (hc : c ∈ N) (hct : t * c = c * t) :
    ρ ⟨c, hc⟩ = ((ρ ⟨c, hc⟩).1, (ρ ⟨c, hc⟩).1) := by
  have hcc : c = t * c * t⁻¹ := by rw [hct]; group
  have h1 := d.swap ⟨c, hc⟩ ⟨c, hc⟩ hcc
  have h2 : (ρ ⟨c, hc⟩).2 = (ρ ⟨c, hc⟩).1 := congrArg Prod.snd h1
  exact Prod.ext rfl h2

theorem mem_CU_of_comm {CU A : Subgroup G} (hXA : X ⊓ centralizer ({t} : Set G) = A)
    (hACU : A ≤ CU) (hCUt : ∀ c ∈ CU, t * c = c * t)
    (hdiag : ∀ a : S, ∃ s ∈ CU, ∃ hs : s ∈ N, ρ ⟨s, hs⟩ = (a, a))
    {c : G} (hc : c ∈ N) (hct : t * c = c * t) : c ∈ CU := by
  obtain ⟨s, hsCU, hsN, hρs⟩ := hdiag (ρ ⟨c, hc⟩).1
  have hk : (⟨s, hsN⟩ : N)⁻¹ * ⟨c, hc⟩ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρs]
    exact inv_mul_eq_one.2 (d.rho_eq_diag hc hct).symm
  rw [d.ker, mem_subgroupOf] at hk
  have hts : Commute t s := hCUt s hsCU
  have hcent : s⁻¹ * c ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc s⁻¹ * c * t = s⁻¹ * (c * t) := by group
      _ = s⁻¹ * (t * c) := by rw [hct]
      _ = (s⁻¹ * t) * c := by group
      _ = (t * s⁻¹) * c := by rw [(hts.inv_right).eq.symm]
      _ = t * (s⁻¹ * c) := by group
  have hw : s⁻¹ * c ∈ A := by
    rw [← hXA]
    exact mem_inf.2 ⟨hk, hcent⟩
  have := mul_mem hsCU (hACU hw)
  rwa [mul_inv_cancel_left] at this

theorem exists_delta_mul {CU A : Subgroup G} (hXA : X ⊓ centralizer ({t} : Set G) = A)
    (hCUN : CU ≤ N) (hCUt : ∀ c ∈ CU, t * c = c * t) {y : G} (hy : y ∈ CU) :
    ∃ p ∈ P, ∃ w ∈ A, y = (p * (t * p * t⁻¹)) * w := by
  have hyN := hCUN hy
  have hyd := d.rho_eq_diag hyN (hCUt y hy)
  obtain ⟨n, hn⟩ := d.surj ((ρ ⟨y, hyN⟩).1, 1)
  have hnΛ : (n : G) ∈ prodFst ρ := (Common.mem_prodFst_iff ρ).2 ⟨n.2, congrArg Prod.snd hn⟩
  have hnPX : (n : G) ∈ P ⊔ X := d.sup_X ▸ hnΛ
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right P X
    (fun p hp => d.N_le_normalizer (d.P_le hp))] at hnPX
  obtain ⟨p, hp, z, hz, hpz⟩ := hnPX
  have hpN := d.P_le hp
  have hzN : z ∈ N := d.X_le hz
  have hρz : ρ ⟨z, hzN⟩ = 1 := by
    have : (⟨z, hzN⟩ : N) ∈ ρ.ker := by rw [d.ker]; exact mem_subgroupOf.2 hz
    exact this
  have hρp : ρ ⟨p, hpN⟩ = ((ρ ⟨y, hyN⟩).1, 1) := by
    have e : (⟨p, hpN⟩ : N) * ⟨z, hzN⟩ = n := Subtype.ext hpz
    rw [← mul_one (ρ ⟨p, hpN⟩), ← hρz, ← map_mul, e]
    exact hn
  have hρδ := d.rho_delta hp
  rw [hρp] at hρδ
  have hk : (⟨p * (t * p * t⁻¹), d.delta_mem_N hp⟩ : N)⁻¹ * ⟨y, hyN⟩ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρδ]
    exact inv_mul_eq_one.2 hyd.symm
  rw [d.ker, mem_subgroupOf] at hk
  have hδt := d.delta_comm hp
  have hyt := hCUt y hy
  have hcent : (p * (t * p * t⁻¹))⁻¹ * y ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hts : Commute t (p * (t * p * t⁻¹)) := hδt
    calc (p * (t * p * t⁻¹))⁻¹ * y * t = (p * (t * p * t⁻¹))⁻¹ * (y * t) := by group
      _ = (p * (t * p * t⁻¹))⁻¹ * (t * y) := by rw [hyt]
      _ = ((p * (t * p * t⁻¹))⁻¹ * t) * y := by group
      _ = (t * (p * (t * p * t⁻¹))⁻¹) * y := by rw [(hts.inv_right).eq.symm]
      _ = t * ((p * (t * p * t⁻¹))⁻¹ * y) := by group
  have hw : (p * (t * p * t⁻¹))⁻¹ * y ∈ A := by
    rw [← hXA]
    exact mem_inf.2 ⟨hk, hcent⟩
  exact ⟨p, hp, _, hw, (mul_inv_cancel_left _ y).symm⟩

theorem comm_mem_P_inf_X {α p : G} (hα : α ∈ X) (hp : p ∈ P) :
    α * p * α⁻¹ * p⁻¹ ∈ P ⊓ X := by
  refine mem_inf.2 ⟨mul_mem (d.conj_mem_P (d.X_le hα) hp) (inv_mem hp), ?_⟩
  have e : α * p * α⁻¹ * p⁻¹ = α * (p * α⁻¹ * p⁻¹) := by group
  rw [e]
  exact mul_mem hα (d.conj_mem_X (d.P_le hp) (inv_mem hα))

theorem comm_mem_Pt_inf_X {α p : G} (hα : α ∈ X) (hp : p ∈ P) :
    α * (t * p * t⁻¹) * α⁻¹ * (t * p * t⁻¹)⁻¹ ∈ P.map (MulAut.conj t).toMonoidHom ⊓ X := by
  have hq : t * p * t⁻¹ ∈ P.map (MulAut.conj t).toMonoidHom := ⟨p, hp, rfl⟩
  have hqN : t * p * t⁻¹ ∈ N := d.conj_t_mem_N (d.P_le hp)
  have h1 : α * (t * p * t⁻¹) * α⁻¹ ∈ P.map (MulAut.conj t).toMonoidHom := by
    rw [diag_mem_map_conj_iff d.t_sq]
    have e : t * (α * (t * p * t⁻¹) * α⁻¹) * t⁻¹ = (t * α * t⁻¹) * p * (t * α * t⁻¹)⁻¹ := by
      calc t * (α * (t * p * t⁻¹) * α⁻¹) * t⁻¹
          = (t * α * t⁻¹) * (t * (t * p * t⁻¹) * t⁻¹) * (t * α * t⁻¹)⁻¹ := by group
        _ = (t * α * t⁻¹) * p * (t * α * t⁻¹)⁻¹ := by rw [diag_conj_conj d.t_sq]
    rw [e]
    exact d.conj_mem_P (d.X_le (d.conj_t_mem_X hα)) hp
  refine mem_inf.2 ⟨mul_mem h1 (inv_mem hq), ?_⟩
  have e : α * (t * p * t⁻¹) * α⁻¹ * (t * p * t⁻¹)⁻¹ =
      α * ((t * p * t⁻¹) * α⁻¹ * (t * p * t⁻¹)⁻¹) := by group
  rw [e]
  exact mul_mem hα (d.conj_mem_X hqN (inv_mem hα))

theorem comm_delta_mul {α p w : G} (hα : α ∈ X) (hp : p ∈ P) (hw : w ∈ X) :
    ∃ y₁ ∈ P ⊓ X, ∃ y₂ ∈ P.map (MulAut.conj t).toMonoidHom ⊓ X,
      α * ((p * (t * p * t⁻¹)) * w) * α⁻¹ * ((p * (t * p * t⁻¹)) * w)⁻¹ = y₁ * y₂ := by
  refine ⟨_, d.comm_mem_P_inf_X hα hp, _, d.comm_mem_Pt_inf_X hα hp, ?_⟩
  have hvP := (d.comm_mem_Pt_inf_X hα hp).1
  have hc := mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 d.comm_conj hp) _ hvP
  have hwα : w * α⁻¹ * w⁻¹ = α⁻¹ := by
    rw [d.X_comm w hw α⁻¹ (inv_mem hα)]
    group
  calc α * ((p * (t * p * t⁻¹)) * w) * α⁻¹ * ((p * (t * p * t⁻¹)) * w)⁻¹
      = α * (p * (t * p * t⁻¹)) * (w * α⁻¹ * w⁻¹) * (p * (t * p * t⁻¹))⁻¹ := by group
    _ = α * (p * (t * p * t⁻¹)) * α⁻¹ * (p * (t * p * t⁻¹))⁻¹ := by rw [hwα]
    _ = (α * p * α⁻¹ * p⁻¹) *
          (p * (α * (t * p * t⁻¹) * α⁻¹ * (t * p * t⁻¹)⁻¹) * p⁻¹) := by group
    _ = (α * p * α⁻¹ * p⁻¹) * (α * (t * p * t⁻¹) * α⁻¹ * (t * p * t⁻¹)⁻¹) := by
      rw [← hc]
      group

theorem A_le_sup {CU A : Subgroup G} (hXA : X ⊓ centralizer ({t} : Set G) = A)
    (hCUN : CU ≤ N) (hCUt : ∀ c ∈ CU, t * c = c * t) (hA3 : A ≤ ⁅A, CU⁆) :
    A ≤ (P ⊓ X) ⊔ (P.map (MulAut.conj t).toMonoidHom ⊓ X) := by
  have hAX : A ≤ X := by rw [← hXA]; exact inf_le_left
  refine hA3.trans (commutator_le.2 fun α hα c hc => ?_)
  obtain ⟨p, hp, w, hw, rfl⟩ := d.exists_delta_mul hXA hCUN hCUt hc
  obtain ⟨y₁, h1, y₂, h2, he⟩ := d.comm_delta_mul (hAX hα) hp (hAX hw)
  rw [commutatorElement_def, he]
  exact mul_mem (mem_sup_left h1) (mem_sup_right h2)

theorem delta_mem_A {A : Subgroup G} (hXA : X ⊓ centralizer ({t} : Set G) = A) {b : G}
    (hb : b ∈ P ⊓ X) : b * (t * b * t⁻¹) ∈ A := by
  rw [← hXA]
  refine mem_inf.2 ⟨mul_mem hb.2 (d.conj_t_mem_X hb.2), ?_⟩
  rw [mem_centralizer_singleton_iff]
  exact (d.delta_comm hb.1).symm

theorem exists_decomp {CU A : Subgroup G} (hXA : X ⊓ centralizer ({t} : Set G) = A)
    (hCUN : CU ≤ N) (hCUt : ∀ c ∈ CU, t * c = c * t) (hA3 : A ≤ ⁅A, CU⁆) {c : G} (hc : c ∈ A) :
    ∃ e ∈ P ⊓ P.map (MulAut.conj t).toMonoidHom, ∃ b ∈ P ⊓ X,
      c = e * (b * (t * b * t⁻¹)) := by
  have hcomm : ∀ a ∈ P ⊓ X, ∀ b ∈ P.map (MulAut.conj t).toMonoidHom ⊓ X, a * b = b * a :=
    fun a ha b hb => d.X_comm a ha.2 b hb.2
  obtain ⟨a, ha, b, hb, hab⟩ := diag_exists_mul_of_mem_sup hcomm (d.A_le_sup hXA hCUN hCUt hA3 hc)
  have hct : t * c * t⁻¹ = c :=
    mul_inv_eq_iff_eq_mul.2 (mem_centralizer_singleton_iff.1 (hXA.ge hc).2).symm
  have hb₀ : t * b * t⁻¹ ∈ P ⊓ X :=
    ⟨(diag_mem_map_conj_iff d.t_sq).1 hb.1, d.conj_t_mem_X hb.2⟩
  have ha' : t * a * t⁻¹ ∈ P.map (MulAut.conj t).toMonoidHom ⊓ X :=
    ⟨⟨a, ha.1, rfl⟩, d.conj_t_mem_X ha.2⟩
  have h1 : a * b = (t * a * t⁻¹) * (t * b * t⁻¹) := by
    calc a * b = t * c * t⁻¹ := by rw [hct, hab]
      _ = (t * a * t⁻¹) * (t * b * t⁻¹) := by rw [hab]; group
  have hbb : (t * b * t⁻¹) * b⁻¹ = b⁻¹ * (t * b * t⁻¹) := d.X_comm _ hb₀.2 _ (inv_mem hb.2)
  have h2 : a * (t * b * t⁻¹)⁻¹ = (t * a * t⁻¹) * b⁻¹ := by
    calc a * (t * b * t⁻¹)⁻¹ = (a * b) * b⁻¹ * (t * b * t⁻¹)⁻¹ := by group
      _ = ((t * a * t⁻¹) * (t * b * t⁻¹)) * b⁻¹ * (t * b * t⁻¹)⁻¹ := by rw [h1]
      _ = (t * a * t⁻¹) * ((t * b * t⁻¹) * b⁻¹) * (t * b * t⁻¹)⁻¹ := by group
      _ = (t * a * t⁻¹) * (b⁻¹ * (t * b * t⁻¹)) * (t * b * t⁻¹)⁻¹ := by rw [hbb]
      _ = (t * a * t⁻¹) * b⁻¹ := by group
  refine ⟨a * (t * b * t⁻¹)⁻¹, mem_inf.2 ⟨mul_mem (mem_inf.1 ha).1 (inv_mem (mem_inf.1 hb₀).1), ?_⟩,
    t * b * t⁻¹, hb₀, ?_⟩
  · rw [h2]
    exact mul_mem (mem_inf.1 ha').1 (inv_mem (mem_inf.1 hb).1)
  · calc c = a * b := hab
      _ = (a * (t * b * t⁻¹)⁻¹) * ((t * b * t⁻¹) * b) := by group
      _ = (a * (t * b * t⁻¹)⁻¹) * ((t * b * t⁻¹) * (t * (t * b * t⁻¹) * t⁻¹)) := by
        rw [diag_conj_conj d.t_sq]

theorem diagonal {CU A U : Subgroup G} (hXA : X ⊓ centralizer ({t} : Set G) = A)
    (hACU : A ≤ CU) (hCUN : CU ≤ N) (hCUt : ∀ c ∈ CU, t * c = c * t)
    (hdiag : ∀ a : S, ∃ s ∈ CU, ∃ hs : s ∈ N, ρ ⟨s, hs⟩ = (a, a))
    (hA3 : A ≤ ⁅A, CU⁆) (hA4 : ∀ z ∈ A, z ∈ centralizer (CU : Set G) → z ∈ U)
    (hA5 : ∀ V : Subgroup G, V ≤ A → (∀ g ∈ CU, ∀ v ∈ V, g * v * g⁻¹ ∈ V) → ¬ V ≤ U → V = A)
    (hA6 : ¬ A ≤ U) :
    (∀ x ∈ P, x * (t * x * t⁻¹) ∈ CU) ∧ (∀ y ∈ CU, ∃ x ∈ P, x * (t * x * t⁻¹) = y) ∧
      (∀ x ∈ P, x * (t * x * t⁻¹) = 1 → x ∈ U) := by
  refine ⟨fun x hx => d.mem_CU_of_comm hXA hACU hCUt hdiag (d.delta_mem_N hx) (d.delta_comm hx),
    ?_, ?_⟩
  ·
    let V : Subgroup G := ((P ⊓ X).subgroupOf P).map d.delta
    have hmemV : ∀ v, v ∈ V ↔ ∃ b : G, b ∈ P ⊓ X ∧ b * (t * b * t⁻¹) = v := by
      intro v
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b, mem_subgroupOf.1 hb, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨b, (mem_inf.1 hb).1⟩, mem_subgroupOf.2 hb, rfl⟩
    have hVA : V ≤ A := by
      intro v hv
      obtain ⟨b, hb, rfl⟩ := (hmemV v).1 hv
      exact d.delta_mem_A hXA hb
    have hVn : ∀ g ∈ CU, ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
      intro g hg v hv
      obtain ⟨b, hb, rfl⟩ := (hmemV v).1 hv
      obtain ⟨p, hp, w, hw, rfl⟩ := d.exists_delta_mul hXA hCUN hCUt hg
      have hbP := (mem_inf.1 hb).1
      have hbX := (mem_inf.1 hb).2
      have hwX : w ∈ X := (mem_inf.1 (hXA.ge hw)).1
      have hδbX : b * (t * b * t⁻¹) ∈ X := mul_mem hbX (d.conj_t_mem_X hbX)
      have hpb : p * b * p⁻¹ ∈ P ⊓ X :=
        mem_inf.2 ⟨mul_mem (mul_mem hp hbP) (inv_mem hp), d.conj_mem_X (d.P_le hp) hbX⟩
      refine (hmemV _).2 ⟨p * b * p⁻¹, hpb, ?_⟩
      have hδ : d.delta (⟨p, hp⟩ * ⟨b, hbP⟩ * ⟨p, hp⟩⁻¹) =
          d.delta ⟨p, hp⟩ * d.delta ⟨b, hbP⟩ * (d.delta ⟨p, hp⟩)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      have hwδ := d.X_comm w hwX _ hδbX
      calc (p * b * p⁻¹) * (t * (p * b * p⁻¹) * t⁻¹)
          = (p * (t * p * t⁻¹)) * (b * (t * b * t⁻¹)) * (p * (t * p * t⁻¹))⁻¹ := hδ
        _ = (p * (t * p * t⁻¹)) * (w * (b * (t * b * t⁻¹)) * w⁻¹) * (p * (t * p * t⁻¹))⁻¹ := by
          rw [hwδ]
          group
        _ = (p * (t * p * t⁻¹) * w) * (b * (t * b * t⁻¹)) * (p * (t * p * t⁻¹) * w)⁻¹ := by
          group
    have hVU : ¬ V ≤ U := by
      intro hle
      obtain ⟨c, hcA, hcU⟩ := SetLike.not_le_iff_exists.1 hA6
      obtain ⟨e, he, b, hb, hceb⟩ := d.exists_decomp hXA hCUN hCUt hA3 hcA
      have hδbA := d.delta_mem_A hXA hb
      have hδbV : b * (t * b * t⁻¹) ∈ V := (hmemV _).2 ⟨b, hb, rfl⟩
      have heA : e ∈ A := by
        have : e = c * (b * (t * b * t⁻¹))⁻¹ := by rw [hceb]; group
        rw [this]
        exact mul_mem hcA (inv_mem hδbA)
      have heC : e ∈ centralizer (CU : Set G) :=
        centralizer_le (SetLike.coe_subset_coe.2 hCUN)
          (d.mem_centralizer_of_mem_inf (mem_inf.1 he).1 (mem_inf.1 he).2)
      have heU : e ∈ U := hA4 e heA heC
      apply hcU
      rw [hceb]
      exact mul_mem heU (hle hδbV)
    have hVeq : V = A := hA5 V hVA hVn hVU
    intro y hy
    obtain ⟨p, hp, w, hw, rfl⟩ := d.exists_delta_mul hXA hCUN hCUt hy
    obtain ⟨b, hb, hbw⟩ := (hmemV w).1 (hVeq.ge hw)
    exact ⟨p * b, mul_mem hp (mem_inf.1 hb).1, by
      rw [d.delta_mul hp (mem_inf.1 hb).1, hbw]⟩
  · intro x hx hδ
    have hq : t * x * t⁻¹ = x⁻¹ := eq_inv_of_mul_eq_one_right hδ
    have hxt : x ∈ P.map (MulAut.conj t).toMonoidHom := by
      rw [diag_mem_map_conj_iff d.t_sq, hq]
      exact inv_mem hx
    have hxX := d.mem_X_of_mem_inf hx hxt
    have hxC := d.mem_centralizer_of_mem_inf hx hxt
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (d.X_sq x hxX)
    have hxA : x ∈ A := by
      rw [← hXA]
      refine mem_inf.2 ⟨hxX, mem_centralizer_singleton_iff.2 ?_⟩
      have : t * x * t⁻¹ = x := by rw [hq, hxinv]
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    exact hA4 x hxA (centralizer_le (SetLike.coe_subset_coe.2 hCUN) hxC)

end ProductDiagData

end Abstract

section RootAxis

variable {H : Type*} [Group H] {K : Type} [Field K]

open scoped Matrix in
theorem rootAxis_mem_of_comm {U A : Subgroup H} {s : SL₂ K →* H} {d : Kˣ →* H} {coord : K → H}
    {vec : H → Fin 2 → K} (hS : RootAxisStructure U A s d coord vec) {z : H} (hz : z ∈ A)
    (hc : ∀ M : SL₂ K, s M * z = z * s M) : z ∈ U := by
  rw [← hS.vec_ker z hz]
  have h : ∀ M : SL₂ K, (M : Matrix (Fin 2) (Fin 2) K) *ᵥ vec z = vec z := fun M => by
    rw [← hS.vec_conj M z hz, hc M, mul_inv_cancel_right]
  have h₁ := congrFun (h ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩) 0
  have h₂ := congrFun (h ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩) 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h₁ h₂
  funext i
  fin_cases i
  · simpa using h₂
  · simpa using h₁

theorem rootAxis_exists_not_mem {U A : Subgroup H} {s : SL₂ K →* H} {d : Kˣ →* H} {coord : K → H}
    {vec : H → Fin 2 → K} (hS : RootAxisStructure U A s d coord vec) : ∃ z ∈ A, z ∉ U := by
  obtain ⟨z, hz, hzv⟩ := hS.vec_surj ![1, 0]
  refine ⟨z, hz, fun hzU => ?_⟩
  have h := congrFun ((hS.vec_ker z hz).2 hzU) 0
  rw [hzv] at h
  simp at h

open scoped Matrix in
theorem rootAxis_A_le_commutator {U A : Subgroup H} {s : SL₂ K →* H} {d : Kˣ →* H}
    {coord : K → H} {vec : H → Fin 2 → K} (hS : RootAxisStructure U A s d coord vec) :
    A ≤ ⁅A, Subgroup.centralizer (U : Set H)⁆ := by
  have hEA : ⁅A, Subgroup.centralizer (U : Set H)⁆ ≤ A := commutator_le.2 fun a ha c hc => by
    rw [commutatorElement_def]
    have h1 := hS.A_normal_C c hc a⁻¹ (inv_mem ha)
    have e : a * c * a⁻¹ * c⁻¹ = a * (c * a⁻¹ * c⁻¹) := by group
    rw [e]
    exact mul_mem ha h1
  refine (hS.normal_eq_A _ (hEA.trans hS.A_le_C) (fun g hg v hv => ?_) hEA ?_).ge
  · exact (mem_normalizer_iff.1 (normalizer_commutator_ge_right _ _ hg) v).1 hv
  · intro hle
    obtain ⟨z, hz, hzv⟩ := hS.vec_surj ![0, 1]
    let M : SL₂ K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hsz := hS.A_normal_C (s M) (hS.s_mem_C M) z hz
    have hw : z⁻¹ * (s M * z * (s M)⁻¹) ∈ ⁅A, Subgroup.centralizer (U : Set H)⁆ := by
      have h := commutator_mem_commutator (inv_mem hz) (hS.s_mem_C M)
      rw [commutatorElement_def] at h
      have e : z⁻¹ * s M * z⁻¹⁻¹ * (s M)⁻¹ = z⁻¹ * (s M * z * (s M)⁻¹) := by group
      rwa [e] at h
    have hw0 : vec (z⁻¹ * (s M * z * (s M)⁻¹)) = 0 :=
      (hS.vec_ker _ (hEA hw)).2 (hle hw)
    have h1 : vec 1 = 0 := (hS.vec_ker 1 (one_mem A)).2 (one_mem U)
    have h2 : vec z⁻¹ + vec z = 0 := by
      rw [← hS.vec_add z⁻¹ (inv_mem hz) z hz, inv_mul_cancel, h1]
    rw [hS.vec_add _ (inv_mem hz) _ hsz, hS.vec_conj M z hz, eq_neg_of_add_eq_zero_left h2,
      hzv] at hw0
    have h3 := congrFun hw0 0
    simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h3

variable {G : Type*} [Group G]

theorem rootAxis_map_facts {U A : Subgroup H} {s : SL₂ K →* H} {d : Kˣ →* H} {coord : K → H}
    {vec : H → Fin 2 → K} (hS : RootAxisStructure U A s d coord vec) (ψ : H →* G)
    (hψ : Function.Injective ψ) :
    A.map ψ ≤ ⁅A.map ψ, (Subgroup.centralizer (U : Set H)).map ψ⁆ ∧
    (∀ z ∈ A.map ψ,
      z ∈ Subgroup.centralizer (((Subgroup.centralizer (U : Set H)).map ψ : Subgroup G) : Set G) →
        z ∈ U.map ψ) ∧
    (∀ V : Subgroup G, V ≤ A.map ψ →
      (∀ g ∈ (Subgroup.centralizer (U : Set H)).map ψ, ∀ v ∈ V, g * v * g⁻¹ ∈ V) →
        ¬ V ≤ U.map ψ → V = A.map ψ) ∧
    ¬ A.map ψ ≤ U.map ψ := by
  refine ⟨(Subgroup.map_mono (rootAxis_A_le_commutator hS)).trans
    (Subgroup.map_commutator _ _ ψ).le, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ hc
    refine ⟨a, rootAxis_mem_of_comm hS ha fun M => hψ ?_, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hc (ψ (s M)) ⟨s M, hS.s_mem_C M, rfl⟩
  · intro V hVA hVn hVU
    have hV'A : V.comap ψ ≤ A := fun a ha => by
      obtain ⟨a', ha', e⟩ := hVA ha
      rwa [← hψ e]
    have hV'eq : V.comap ψ = A := by
      refine hS.normal_eq_A _ (hV'A.trans hS.A_le_C) (fun g hg v hv => ?_) hV'A fun hle => hVU ?_
      · show ψ (g * v * g⁻¹) ∈ V
        rw [map_mul, map_mul, map_inv]
        exact hVn _ ⟨g, hg, rfl⟩ _ hv
      · intro x hx
        obtain ⟨a, ha, rfl⟩ := hVA hx
        exact ⟨a, hle (show a ∈ V.comap ψ from hx), rfl⟩
    refine le_antisymm hVA fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := hx
    exact (show a ∈ V.comap ψ by rw [hV'eq]; exact ha)
  · obtain ⟨z, hz, hzU⟩ := rootAxis_exists_not_mem hS
    intro hle
    obtain ⟨u, hu, e⟩ := hle ⟨z, hz, rfl⟩
    exact hzU (hψ e ▸ hu)

theorem diag_pull_eq_map {L : Subgroup G} (φ : L ≃* H) (S : Subgroup H) :
    pull φ S = S.map (L.subtype.comp φ.symm.toMonoidHom) := by
  rw [pull, comap_equiv_eq_map_symm', map_map]

theorem rootAxis_pull_facts {L : Subgroup G} (φ : L ≃* H) {U A : Subgroup H} {s : SL₂ K →* H}
    {d : Kˣ →* H} {coord : K → H} {vec : H → Fin 2 → K}
    (hS : RootAxisStructure U A s d coord vec) {CU : Subgroup G}
    (hCU : CU = pull φ (Subgroup.centralizer (U : Set H))) :
    pull φ A ≤ ⁅pull φ A, CU⁆ ∧ (∀ z ∈ pull φ A, z ∈ centralizer (CU : Set G) → z ∈ pull φ U) ∧
    (∀ V : Subgroup G, V ≤ pull φ A → (∀ g ∈ CU, ∀ v ∈ V, g * v * g⁻¹ ∈ V) →
      ¬ V ≤ pull φ U → V = pull φ A) ∧ ¬ pull φ A ≤ pull φ U := by
  subst hCU
  rw [diag_pull_eq_map φ A, diag_pull_eq_map φ U, diag_pull_eq_map φ (Subgroup.centralizer _)]
  exact rootAxis_map_facts hS _ (L.subtype_injective.comp φ.symm.injective)

end RootAxis

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (𝐗[Axis.one] ⊔ 𝐗[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐍𝐂[" i "]" => closure {x : G | ∃ g ∈ normalizer (𝐗[i] : Set G),
  ∃ y ∈ (L ⊓ centralizer (𝐔[i] : Set G) : Subgroup G) ⊔ 𝐗[i], x = g⁻¹ * y * g}

theorem diagonal_eq_CU (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis)
    (ρ : 𝐍𝐂[i] →* SL(2, K) × SL(2, K)) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = 𝐗[i].subgroupOf 𝐍𝐂[i])
    (hswap : ∀ x y : 𝐍𝐂[i], (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap)
    (β : SL(2, K) ≃* SL(2, K))
    (hβ : ∀ (M : SL(2, K)) (hM : ((φ.symm (sHom K i M) : L) : G) ∈ 𝐍𝐂[i]),
      ρ ⟨_, hM⟩ = (β M, β M))
    {P : Subgroup G} (hPΛ : P ≤ prodFst ρ) (hP : ⁅P, P⁆ = P) (hPX : P ⊔ 𝐗[i] = prodFst ρ)
    (hPt : ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hPmax : ∀ Q : Subgroup G, Q ≤ prodFst ρ → ⁅Q, Q⁆ = Q → Q ≤ P) :
    (∀ x ∈ P, x * (t * x * t⁻¹) ∈ L ⊓ centralizer (𝐔[i] : Set G)) ∧
    (∀ y ∈ L ⊓ centralizer (𝐔[i] : Set G), ∃ x ∈ P, x * (t * x * t⁻¹) = y) ∧
    (∀ x ∈ P, x * (t * x * t⁻¹) = 1 → x ∈ 𝐔[i]) := by
  have hsup := sup_le_NC (φ := φ) (t := t) i
  obtain ⟨hA3, hA4, hA5, hA6⟩ := rootAxis_pull_facts φ (h.twoCore.axisStr i) (CU_eq i)
  have d := ProductDiagData.mk hρ hker (le_sup_right.trans hsup)
    (fun x hx => X_mul_self h hbt i hx)
    (fun x hx y hy => comm_of_mul_self (fun _ hz => X_mul_self h hbt i hz) hx hy)
    (mem_normalizer_of_conj_le fun z hz => conj_mem_NC i (t_mem_normalizer_X h i) hz)
    h.setup.t_mul_t hswap hPΛ hP hPX hPt hPmax
  refine d.diagonal (X_inf_C h i) (fun a ha => ((X_inf_CU h i).ge ha).2) (le_sup_left.trans hsup)
    (fun c hc => (mem_centralizer_singleton_iff.1 (CU_le_C h i hc)).symm) (fun a => ?_)
    hA3 hA4 hA5 hA6
  have hs := s_mem_CU h i (β.symm a)
  have hsN : ((φ.symm (sHom K i (β.symm a)) : L) : G) ∈ _ := hsup (mem_sup_left hs)
  refine ⟨_, hs, hsN, ?_⟩
  rw [hβ (β.symm a) hsN, MulEquiv.apply_symm_apply]

end Setting

end BothTrivialProduct

end CFSG.LocalAnalysis.EvenBN.Sp4
