module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Cut
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift
public import CFSG.Quasithin.Background.D2Offenders

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Engine

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.KCut

section Cut

variable {W : Type} [CommGroup W]

theorem disp_symm {X Y : MulAut W} (hXY : Y * X = X * Y)
    (h : ∀ w : W, X (Y w * w⁻¹) = Y w * w⁻¹) : ∀ w : W, Y (X w * w⁻¹) = X w * w⁻¹ := by
  intro w
  have h1 : Y (X w) = X (Y w) := by
    have := congrArg (fun f : MulAut W => f w) hXY
    simpa [MulAut.mul_apply] using this
  have h2 := h w
  rw [map_mul, map_inv] at h2
  rw [map_mul, map_inv, h1]
  have h3 : X (Y w) = Y w * w⁻¹ * X w := (mul_inv_eq_iff_eq_mul).1 h2
  rw [h3]
  have h4 : Y w * w⁻¹ * X w * (Y w)⁻¹ = (Y w * (Y w)⁻¹) * (X w * w⁻¹) := by
    simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [h4, mul_inv_cancel, one_mul]

theorem mem_Kgrp_of_cent_eq {L : Subgroup (MulAut W)} {t y : MulAut W} (hyL : y ∈ L)
    (htL : t ∈ L) (hy2 : y * y = 1) (hyt : y ≠ t) (hty : y * t = t * y)
    (hKy : Kgrp L y = L ⊓ Subgroup.centralizer {y}) : y ∈ Kgrp L t := by
  refine Subgroup.subset_closure ⟨hyL, hy2, hyt, hty, ?_⟩
  have htK : t ∈ Kgrp L y := by
    rw [hKy]
    exact ⟨htL, Subgroup.mem_centralizer_singleton_iff.2 hty.symm⟩
  exact disp_symm hty (fun w => Kgrp_fixes_disp htK w)

theorem conj_mem_Kgrp_prod {L : Subgroup (MulAut W)} {u v c : MulAut W} (hu : u ∈ L)
    (hv : v ∈ L) (hv1 : v ≠ 1) (hu2 : u * u = 1) (huv : u * v = v * u)
    (hKu : Kgrp L u = L ⊓ Subgroup.centralizer {u})
    (hc : c ∈ L ⊓ Subgroup.centralizer {u * v}) : c * u * c⁻¹ ∈ Kgrp L (u * v) := by
  obtain ⟨hcL, hcc⟩ := hc
  have hct : c * (u * v) = (u * v) * c := Subgroup.mem_centralizer_singleton_iff.1 hcc
  have ht' : c * (u * v) * c⁻¹ = u * v := by rw [hct]; group
  have hut : u * (u * v) = (u * v) * u := by
    calc u * (u * v) = u * (v * u) := by rw [huv]
      _ = (u * v) * u := by group
  refine mem_Kgrp_of_cent_eq (L.mul_mem (L.mul_mem hcL hu) (L.inv_mem hcL)) (L.mul_mem hu hv)
    ?_ ?_ ?_ (Kgrp_eq_cent_conj hcL hKu)
  · calc c * u * c⁻¹ * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  · intro h
    apply hv1
    have h1 : u = u * v := by
      calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
        _ = c⁻¹ * (u * v) * c := by rw [h]
        _ = c⁻¹ * ((u * v) * c) := by group
        _ = c⁻¹ * (c * (u * v)) := by rw [hct]
        _ = u * v := by group
    have h2 : u * v = u * 1 := by rw [mul_one]; exact h1.symm
    exact mul_left_cancel h2
  · calc c * u * c⁻¹ * (u * v) = c * u * c⁻¹ * (c * (u * v) * c⁻¹) := by rw [ht']
      _ = c * (u * (u * v)) * c⁻¹ := by group
      _ = c * ((u * v) * u) * c⁻¹ := by rw [hut]
      _ = (c * (u * v) * c⁻¹) * (c * u * c⁻¹) := by group
      _ = (u * v) * (c * u * c⁻¹) := by rw [ht']

variable [Finite W]

theorem co2_Kgrp_le [Nontrivial W] (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hfix : fixV L = ⊥) {z0 a b : MulAut W} {Q Dab : Subgroup (MulAut W)}
    (hz0 : z0 ∈ L) (hz02 : z0 * z0 = 1) (hz01 : z0 ≠ 1)
    (ha : ∃ g ∈ L, a = g * z0 * g⁻¹) (hb : ∃ g ∈ L, b = g * z0 * g⁻¹)
    (hab : a * b = b * a) (hne : a ≠ b)
    (hgen₁ : (L ⊓ Subgroup.centralizer {a}) ⊔ (L ⊓ Subgroup.centralizer {b}) = L)
    (hDab : Dab ≤ Subgroup.closure
      {y | ∃ c ∈ L ⊓ Subgroup.centralizer {a * b}, y = c * a * c⁻¹ ∨ y = c * b * c⁻¹})
    (hgen₂ : (L ⊓ Subgroup.centralizer {a}) ⊔ Dab = L)
    (hgen₃ : (L ⊓ Subgroup.centralizer {b}) ⊔ Dab = L)
    (hdich : Kgrp L z0 ≤ Q ∨ Kgrp L z0 = L ⊓ Subgroup.centralizer {z0}) : Kgrp L z0 ≤ Q := by
  rcases hdich with h | hK0
  · exact h
  exfalso
  have hconj : ∀ {u : MulAut W}, (∃ g ∈ L, u = g * z0 * g⁻¹) →
      u ∈ L ∧ u * u = 1 ∧ u ≠ 1 := by
    rintro u ⟨g, hg, rfl⟩
    refine ⟨L.mul_mem (L.mul_mem hg hz0) (L.inv_mem hg), ?_, ?_⟩
    · calc g * z0 * g⁻¹ * (g * z0 * g⁻¹) = g * (z0 * z0) * g⁻¹ := by group
        _ = 1 := by rw [hz02]; group
    · intro h
      apply hz01
      calc z0 = g⁻¹ * (g * z0 * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
  obtain ⟨haL, ha2, ha1⟩ := hconj ha
  obtain ⟨hbL, hb2, hb1⟩ := hconj hb
  have hKa : Kgrp L a = L ⊓ Subgroup.centralizer {a} := by
    obtain ⟨g, hg, rfl⟩ := ha
    exact Kgrp_eq_cent_conj hg hK0
  have hKb : Kgrp L b = L ⊓ Subgroup.centralizer {b} := by
    obtain ⟨g, hg, rfl⟩ := hb
    exact Kgrp_eq_cent_conj hg hK0
  have hS : ∀ y ∈ {y | ∃ c ∈ L ⊓ Subgroup.centralizer {a * b},
      y = c * a * c⁻¹ ∨ y = c * b * c⁻¹}, y ∈ Kgrp L (a * b) := by
    rintro y ⟨c, hc, rfl | rfl⟩
    · exact conj_mem_Kgrp_prod haL hbL hb1 ha2 hab hKa hc
    · have hc' : c ∈ L ⊓ Subgroup.centralizer {b * a} := by rw [← hab]; exact hc
      have := conj_mem_Kgrp_prod (u := b) (v := a) hbL haL ha1 hb2 hab.symm hKb hc'
      rwa [← hab] at this
  have hNK : Dab ≤ Kgrp L (a * b) := hDab.trans ((Subgroup.closure_le _).2 hS)
  exact KCut.false_of_sub_Kgrp hW hirr hfix ha2 hb2 ha1 hb1 hab hne hKa.ge hKb.ge hNK hgen₁
    hgen₂ hgen₃

end Cut

section Transport

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {G : Type} [Group G]

@[expose] def psi (φ : ↥L ≃* G) : G →* MulAut W := L.subtype.comp φ.symm.toMonoidHom

theorem psi_apply (φ : ↥L ≃* G) (g : G) : psi φ g = ((φ.symm g : ↥L) : MulAut W) := rfl

theorem psi_mem (φ : ↥L ≃* G) (g : G) : psi φ g ∈ L := (φ.symm g).2

theorem psi_inj (φ : ↥L ≃* G) : Function.Injective (psi φ) :=
  L.subtype_injective.comp φ.symm.injective

theorem psi_phi (φ : ↥L ≃* G) (k : MulAut W) (hk : k ∈ L) : psi φ (φ ⟨k, hk⟩) = k := by
  rw [psi_apply, MulEquiv.symm_apply_apply]

theorem psi_range (φ : ↥L ≃* G) : (psi φ).range = L := by
  ext k
  constructor
  · rintro ⟨g, rfl⟩
    exact psi_mem φ g
  · intro hk
    exact ⟨φ ⟨k, hk⟩, psi_phi φ k hk⟩

theorem card_comap_psi (φ : ↥L ≃* G) {E : Subgroup (MulAut W)} (hE : E ≤ L) :
    Nat.card (E.comap (psi φ)) = Nat.card E := by
  have h := Subgroup.card_map_of_injective (f := psi φ) (K := E.comap (psi φ)) (psi_inj φ)
  rw [Subgroup.map_comap_eq_self (by rw [psi_range]; exact hE)] at h
  exact h.symm

theorem map_psi_cent (φ : ↥L ≃* G) (u : G) :
    (Subgroup.centralizer {u}).map (psi φ) = L ⊓ Subgroup.centralizer {psi φ u} := by
  ext k
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨psi_mem φ g, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hg]
  · rintro ⟨hkL, hkc⟩
    refine ⟨φ ⟨k, hkL⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_, psi_phi φ k hkL⟩
    apply psi_inj φ
    rw [map_mul, map_mul, psi_phi φ k hkL]
    exact Subgroup.mem_centralizer_singleton_iff.1 hkc

theorem map_psi_top (φ : ↥L ≃* G) : (⊤ : Subgroup G).map (psi φ) = L := by
  rw [Subgroup.map_top, psi_range]

theorem kgrp_dich (φ : ↥L ≃* G) {z0 : G} {Q0 : Subgroup G}
    (hdich : ∀ N : Subgroup G, N ≤ Subgroup.centralizer {z0} →
      (∀ c ∈ Subgroup.centralizer {z0}, ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
        N ≤ Q0 ∨ N = Subgroup.centralizer {z0}) :
    Kgrp L (psi φ z0) ≤ Q0.map (psi φ) ∨
      Kgrp L (psi φ z0) = L ⊓ Subgroup.centralizer {psi φ z0} := by
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup G, N = (Kgrp L (psi φ z0)).comap (psi φ) := ⟨_, rfl⟩
  have hNmem : ∀ g, g ∈ N ↔ psi φ g ∈ Kgrp L (psi φ z0) := fun g => by rw [hNdef]; rfl
  have hN1 : N ≤ Subgroup.centralizer {z0} := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk : psi φ g ∈ Kgrp L (psi φ z0) := (hNmem g).1 hg
    have := Subgroup.mem_centralizer_singleton_iff.1 (Kgrp_le_centralizer L _ hk)
    apply psi_inj φ
    rw [map_mul, map_mul]
    exact this
  have hN2 : ∀ c ∈ Subgroup.centralizer {z0}, ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    intro c hc n hn
    have hcc : c * z0 = z0 * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    have hcy : psi φ c * psi φ z0 = psi φ z0 * psi φ c := by
      rw [← map_mul, ← map_mul, hcc]
    have := Kgrp_cent_mem (psi_mem φ c) hcy ((hNmem n).1 hn)
    rw [hNmem, map_mul, map_mul, map_inv]
    exact this
  rcases hdich N hN1 hN2 with h | h
  · left
    intro k hk
    have hkL := Kgrp_le L _ hk
    refine ⟨φ ⟨k, hkL⟩, h ((hNmem _).2 ?_), psi_phi φ k hkL⟩
    rw [psi_phi φ k hkL]
    exact hk
  · right
    refine le_antisymm (Kgrp_le_cent L _) fun k hk => ?_
    have hmem : φ ⟨k, hk.1⟩ ∈ Subgroup.centralizer {z0} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply psi_inj φ
      rw [map_mul, map_mul, psi_phi φ k hk.1]
      exact Subgroup.mem_centralizer_singleton_iff.1 hk.2
    rw [← h] at hmem
    have := (hNmem _).1 hmem
    rwa [psi_phi φ k hk.1] at this

end Transport

theorem heis_conj {G : Type} [Group G] {p n : ℕ} {t0 t : G} (ht : IsConj t0 t)
    (h : ∃ (x y : Fin (n + 1) → G) (w : G), HeisCfg p (n + 1) x y w ∧ (∀ i, y i ^ p = 1) ∧
      t0 * x 0 * t0⁻¹ = (x 0)⁻¹) :
    ∃ (x y : Fin (n + 1) → G) (w : G), HeisCfg p (n + 1) x y w ∧ (∀ i, y i ^ p = 1) ∧
      t * x 0 * t⁻¹ = (x 0)⁻¹ := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 ht
  obtain ⟨x, y, w, hc, hy, hinv⟩ := h
  let f : G →* G := (MulAut.conj g).toMonoidHom
  have e1 : ∀ u : G, f u = g * u * g⁻¹ := fun u => by simp [f, MulAut.conj_apply]
  have hfz : f w ≠ 1 := by
    intro h1
    apply hc.z1
    rw [e1] at h1
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  refine ⟨fun i => f (x i), fun i => f (y i), f w, hc.map f hfz, fun i => ?_, ?_⟩
  · rw [← map_pow, hy i, map_one]
  · simp only [e1]
    calc g * t0 * g⁻¹ * (g * x 0 * g⁻¹) * (g * t0 * g⁻¹)⁻¹ = g * (t0 * x 0 * t0⁻¹) * g⁻¹ := by
          group
      _ = g * (x 0)⁻¹ * g⁻¹ := by rw [hinv]
      _ = (g * x 0 * g⁻¹)⁻¹ := by group

@[expose] def Nconj {G : Type} [Group G] (a b : G) : Subgroup G :=
  Subgroup.closure {y | ∃ c ∈ Subgroup.centralizer {a * b}, y = c * a * c⁻¹ ∨ y = c * b * c⁻¹}

structure Co2CutData (G : Type) [Group G] where
  z0 : G
  Q0 : Subgroup G
  a : G
  b : G
  t1 : G
  t2 : G
  z0_inv : z0 * z0 = 1 ∧ z0 ≠ 1
  ha : IsConj z0 a
  hb : IsConj z0 b
  hab_comm : a * b = b * a
  hab_ne : a ≠ b
  gen₁ : Subgroup.centralizer {a} ⊔ Subgroup.centralizer {b} = ⊤
  gen₂ : Subgroup.centralizer {a} ⊔ Nconj a b = ⊤
  gen₃ : Subgroup.centralizer {b} ⊔ Nconj a b = ⊤
  dich : ∀ N : Subgroup G, N ≤ Subgroup.centralizer {z0} →
    (∀ c ∈ Subgroup.centralizer {z0}, ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
      N ≤ Q0 ∨ N = Subgroup.centralizer {z0}
  Q_rank : ∀ B : Subgroup G, B ≤ Q0 → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 5
  noA_rank : ∀ B : Subgroup G, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
    (∀ x ∈ B, x ≠ 1 → ¬ IsConj z0 x) → Nat.card B ≤ 2 ^ 7
  classes : ∀ t : G, t * t = 1 → t ≠ 1 → ¬ IsConj z0 t → IsConj t1 t ∨ IsConj t2 t
  heisA : ∃ (x y : Fin (1 + 1) → G) (w : G), HeisCfg 3 (1 + 1) x y w ∧ (∀ i, y i ^ 3 = 1) ∧
    z0 * x 0 * z0⁻¹ = (x 0)⁻¹
  heisB : ∃ (x y : Fin (0 + 1) → G) (w : G), HeisCfg 5 (0 + 1) x y w ∧ (∀ i, y i ^ 5 = 1) ∧
    t1 * x 0 * t1⁻¹ = (x 0)⁻¹
  heisC : ∃ (x y : Fin (0 + 1) → G) (w : G), HeisCfg 5 (0 + 1) x y w ∧ (∀ i, y i ^ 5 = 1) ∧
    t2 * x 0 * t2⁻¹ = (x 0)⁻¹

theorem orderOf_two_zmod_three_co2 : orderOf (2 : ZMod 3) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m
  decide

theorem orderOf_two_zmod_five_co2 : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem conj_inj_co2 {G : Type*} [Group G] (c : G) :
    Function.Injective (MulAut.conj c).toMonoidHom := fun a b h => by
  simpa using h

theorem noIrrFFOffender_of_co2CutData {G : Type} [Group G] (D : Co2CutData G)
    (hAut : ∀ φ : G ≃* G, ∃ s : G, ∀ x, φ x = s * x * s⁻¹)
    (hZ : ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
      Nonempty (L ⧸ Subgroup.center L ≃* G) → Nat.card (Subgroup.center L) = 1) :
    NoIrrFFOffender G := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel hquad
  have : Nontrivial W := hirr.1
  have hperf : Group.IsPerfect ↥L := hq.1
  have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := hZ ↥L hperf ⟨e⟩
  have hZbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
  let π : ↥L →* G := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπi : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (QuotientGroup.mk x : CQ L) = 1 := by
      apply e.injective
      simpa [π] using hx
    rw [QuotientGroup.eq_one_iff, hZbot, Subgroup.mem_bot] at h1
    exact h1
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let φ : ↥L ≃* G := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  have hL : L ≠ ⊥ := ne_bot_of_isQuasisimple hq
  have hfix : fixV L = ⊥ := fixV_eq_bot_of_irr hirr hL
  have hEL : E ≤ L := le_of_autInner hW hperf hirr hEN hel e hAut
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hel.2 x hx
  have hz02 : psi φ D.z0 * psi φ D.z0 = 1 := by rw [← map_mul, D.z0_inv.1, map_one]
  have hz01 : psi φ D.z0 ≠ 1 := fun h => D.z0_inv.2 (psi_inj φ (by rw [h, map_one]))
  have hconjL : ∀ {u : G}, IsConj D.z0 u → ∃ g ∈ L, psi φ u = g * psi φ D.z0 * g⁻¹ := by
    intro u hu
    obtain ⟨h, hh⟩ := isConj_iff.1 hu
    refine ⟨psi φ h, psi_mem φ h, ?_⟩
    rw [← hh, map_mul, map_mul, map_inv]
  have hKz : Kgrp L (psi φ D.z0) ≤ D.Q0.map (psi φ) := by
    refine co2_Kgrp_le hW hirr.2 hfix (z0 := psi φ D.z0) (a := psi φ D.a) (b := psi φ D.b)
      (Dab := (Nconj D.a D.b).map (psi φ)) (psi_mem φ _) hz02 hz01 (hconjL D.ha) (hconjL D.hb)
      ?_ ?_ ?_ ?_ ?_ ?_ (kgrp_dich φ D.dich)
    · rw [← map_mul, ← map_mul, D.hab_comm]
    · intro h
      exact D.hab_ne (psi_inj φ h)
    · rw [← map_psi_cent, ← map_psi_cent, ← Subgroup.map_sup, D.gen₁, map_psi_top]
    · rw [Nconj, MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨y, ⟨c, hc, hy⟩, rfl⟩
      refine ⟨psi φ c, ?_, ?_⟩
      · refine ⟨psi_mem φ c, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have := congrArg (psi φ) (Subgroup.mem_centralizer_singleton_iff.1 hc)
        simpa only [map_mul] using this
      · rcases hy with rfl | rfl
        · left
          rw [map_mul, map_mul, map_inv]
        · right
          rw [map_mul, map_mul, map_inv]
    · rw [← map_psi_cent, ← Subgroup.map_sup, D.gen₂, map_psi_top]
    · rw [← map_psi_cent, ← Subgroup.map_sup, D.gen₃, map_psi_top]
  obtain ⟨Eb, hEbdef⟩ : ∃ Eb : Subgroup G, Eb = E.comap (psi φ) := ⟨_, rfl⟩
  have hEbmem : ∀ g, g ∈ Eb ↔ psi φ g ∈ E := fun g => by rw [hEbdef]; rfl
  have hEbcard : Nat.card Eb = Nat.card E := by rw [hEbdef]; exact card_comap_psi φ hEL
  have hcommEb : ∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x := fun x hx y hy =>
    psi_inj φ (by rw [map_mul, map_mul]; exact hel.1 _ ((hEbmem _).1 hx) _ ((hEbmem _).1 hy))
  have hsqEb : ∀ x ∈ Eb, x * x = 1 := fun x hx =>
    psi_inj φ (by rw [map_mul, map_one]; exact hEsq _ ((hEbmem _).1 hx))
  have hindex : ∀ b : MulAut W, (∃ m, (fixV (Subgroup.zpowers b)).index = 2 ^ m) :=
    fun b => index_fixV_eq_two_pow hW _
  have hdispA : ∀ g : G, IsConj D.z0 g → 2 ^ 6 ≤ (fixV (Subgroup.zpowers (psi φ g))).index := by
    intro g hg
    obtain ⟨x, y, w, hc, hy, hinv⟩ := heis_conj hg D.heisA
    have hfz : psi φ w ≠ 1 := fun h1 => hc.z1 (psi_inj φ (by rw [h1, map_one]))
    have hg2 : psi φ g * psi φ g = 1 := by
      obtain ⟨h, hh⟩ := isConj_iff.1 hg
      have h' : g * g = 1 := by
        rw [← hh]
        calc h * D.z0 * h⁻¹ * (h * D.z0 * h⁻¹) = h * (D.z0 * D.z0) * h⁻¹ := by group
          _ = 1 := by rw [D.z0_inv.1]; group
      rw [← map_mul, h', map_one]
    have hinvb : psi φ g * psi φ (x 0) * (psi φ g)⁻¹ = (psi φ (x 0))⁻¹ := by
      have := congrArg (psi φ) hinv
      rw [map_mul, map_mul, map_inv, map_inv] at this
      exact this
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have h1 := two_pow_le_index_sq_of_heisCfg hW (p := 3) (n := 1) (by norm_num)
      (hc.map (psi φ) hfz) hg2 hinvb
    rw [orderOf_two_zmod_three_co2] at h1
    exact two_pow_le_of_pow_le (index_fixV_eq_two_pow hW _) h1 (by norm_num)
  have hdispN : ∀ g : G, g * g = 1 → g ≠ 1 → ¬ IsConj D.z0 g →
      2 ^ 8 ≤ (fixV (Subgroup.zpowers (psi φ g))).index := by
    intro g hg2' hg1 hgA
    have hg2 : psi φ g * psi φ g = 1 := by rw [← map_mul, hg2', map_one]
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rcases D.classes g hg2' hg1 hgA with hB | hC
    · obtain ⟨x, y, w, hc, hy, hinv⟩ := heis_conj hB D.heisB
      have hfz : psi φ w ≠ 1 := fun h1 => hc.z1 (psi_inj φ (by rw [h1, map_one]))
      have hinvb : psi φ g * psi φ (x 0) * (psi φ g)⁻¹ = (psi φ (x 0))⁻¹ := by
        have := congrArg (psi φ) hinv
        rw [map_mul, map_mul, map_inv, map_inv] at this
        exact this
      have h1 := two_pow_le_index_sq_of_heisCfg hW (p := 5) (n := 0) (by norm_num)
        (hc.map (psi φ) hfz) hg2 hinvb
      rw [orderOf_two_zmod_five_co2] at h1
      exact two_pow_le_of_pow_le (index_fixV_eq_two_pow hW _) h1 (by norm_num)
    · obtain ⟨x, y, w, hc, hy, hinv⟩ := heis_conj hC D.heisC
      have hfz : psi φ w ≠ 1 := fun h1 => hc.z1 (psi_inj φ (by rw [h1, map_one]))
      have hinvb : psi φ g * psi φ (x 0) * (psi φ g)⁻¹ = (psi φ (x 0))⁻¹ := by
        have := congrArg (psi φ) hinv
        rw [map_mul, map_mul, map_inv, map_inv] at this
        exact this
      have h1 := two_pow_le_index_sq_of_heisCfg hW (p := 5) (n := 0) (by norm_num)
        (hc.map (psi φ) hfz) hg2 hinvb
      rw [orderOf_two_zmod_five_co2] at h1
      exact two_pow_le_of_pow_le (index_fixV_eq_two_pow hW _) h1 (by norm_num)
  have hmono : ∀ b ∈ E, (fixV (Subgroup.zpowers b)).index ≤ (fixV E).index := by
    intro b hbE
    apply Subgroup.index_antitone
    apply CFSG.Quasithin.fixV_anti
    rw [Subgroup.zpowers_le]
    exact hbE
  have hpos : 0 < Nat.card (fixV E) := Nat.card_pos
  suffices h4 : Nat.card E < (fixV E).index by
    calc Nat.card E * Nat.card (fixV E) < (fixV E).index * Nat.card (fixV E) :=
          Nat.mul_lt_mul_of_pos_right h4 hpos
      _ = Nat.card W := by rw [mul_comm, Subgroup.card_mul_index]
  by_cases hA : ∃ x ∈ E, x ≠ 1 ∧ ∃ g : G, psi φ g = x ∧ IsConj D.z0 g
  · obtain ⟨x, hxE, hx1, g, hgx, hg⟩ := hA
    have hcard : Nat.card E ≤ 2 ^ 5 := by
      by_cases hsmall : Nat.card E ≤ 3
      · omega
      push Not at hsmall
      have hc : (E : Set (MulAut W)).ncard = Nat.card E := (Nat.card_coe_set_eq _).symm
      have hfall : ∃ f ∈ E, f ≠ 1 ∧ f ≠ x := by
        by_contra hcon
        push Not at hcon
        have hsub : (E : Set (MulAut W)) ⊆ {1, x} := fun y hy => by
          by_cases h1 : y = 1
          · exact Or.inl h1
          · exact Or.inr (hcon y hy h1)
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        have h2 : ({1, x} : Set (MulAut W)).ncard ≤ 2 :=
          (Set.ncard_insert_le 1 {x}).trans (by simp)
        rw [hc] at this
        omega
      obtain ⟨f, hfE, hf1, hfx⟩ := hfall
      have hEK : E ≤ Kgrp L x := le_Kgrp_of_isQuadratic hEL hel hquad hxE hx1 hfE hf1 hfx
      obtain ⟨h, hh⟩ := isConj_iff.1 hg
      have hxeq : x = psi φ h * psi φ D.z0 * (psi φ h)⁻¹ := by
        rw [← hgx, ← hh, map_mul, map_mul, map_inv]
      obtain ⟨B, hBdef⟩ : ∃ B : Subgroup G, B = Eb.map (MulAut.conj h⁻¹).toMonoidHom := ⟨_, rfl⟩
      have hBmem : ∀ y, y ∈ B ↔ ∃ e' ∈ Eb, h⁻¹ * e' * h = y := fun y => by
        rw [hBdef, Subgroup.mem_map]
        constructor
        · rintro ⟨e', he', rfl⟩
          exact ⟨e', he', by simp⟩
        · rintro ⟨e', he', rfl⟩
          exact ⟨e', he', by simp⟩
      have hBQ : B ≤ D.Q0 := by
        intro y hy
        obtain ⟨e', he', rfl⟩ := (hBmem y).1 hy
        have h1 : psi φ e' ∈ Kgrp L (psi φ h * psi φ D.z0 * (psi φ h)⁻¹) := by
          rw [← hxeq]
          exact hEK ((hEbmem e').1 he')
        have h2 := (mem_Kgrp_conj (psi_mem φ h) (psi φ D.z0) (psi φ e')).1 h1
        obtain ⟨q, hq, hqe⟩ := hKz h2
        have : q = h⁻¹ * e' * h := by
          apply psi_inj φ
          rw [hqe, map_mul, map_mul, map_inv]
        rw [← this]
        exact hq
      have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
        intro u hu v hv
        obtain ⟨e1, he1, rfl⟩ := (hBmem u).1 hu
        obtain ⟨e2, he2, rfl⟩ := (hBmem v).1 hv
        calc h⁻¹ * e1 * h * (h⁻¹ * e2 * h) = h⁻¹ * (e1 * e2) * h := by group
          _ = h⁻¹ * (e2 * e1) * h := by rw [hcommEb e1 he1 e2 he2]
          _ = h⁻¹ * e2 * h * (h⁻¹ * e1 * h) := by group
      have hsqB : ∀ x ∈ B, x * x = 1 := by
        intro u hu
        obtain ⟨e1, he1, rfl⟩ := (hBmem u).1 hu
        calc h⁻¹ * e1 * h * (h⁻¹ * e1 * h) = h⁻¹ * (e1 * e1) * h := by group
          _ = 1 := by rw [hsqEb e1 he1]; group
      have hBcard : Nat.card B = Nat.card Eb := by
        rw [hBdef]
        exact Subgroup.card_map_of_injective (conj_inj_co2 h⁻¹)
      have := D.Q_rank B hBQ hcommB hsqB
      rw [hBcard, hEbcard] at this
      exact this
    have hd := hdispA g hg
    rw [hgx] at hd
    have := hmono x hxE
    have h64 : 2 ^ 5 < 2 ^ 6 := by norm_num
    exact lt_of_le_of_lt hcard (lt_of_lt_of_le h64 (hd.trans this))
  · push Not at hA
    have hcard : Nat.card E ≤ 2 ^ 7 := by
      rw [← hEbcard]
      refine D.noA_rank Eb hcommEb hsqEb ?_
      intro g hg hg1 hgc
      exact hA (psi φ g) ((hEbmem g).1 hg) (fun h => hg1 (psi_inj φ (by rw [h, map_one])))
        g rfl hgc
    obtain ⟨⟨b, hbE⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hbL : b ∈ L := hEL hbE
    obtain ⟨g, hg⟩ : ∃ g : G, psi φ g = b := ⟨φ ⟨b, hbL⟩, psi_phi φ b hbL⟩
    have hg2 : g * g = 1 := by
      apply psi_inj φ
      rw [map_mul, map_one, hg]
      rw [← sq]
      exact hel.2 b hbE
    have hg1 : g ≠ 1 := fun h => hb1' (by rw [← hg, h, map_one])
    have hgA : ¬ IsConj D.z0 g := fun hgc => hA b hbE hb1' g hg hgc
    have hd := hdispN g hg2 hg1 hgA
    rw [hg] at hd
    have := hmono b hbE
    have h64 : 2 ^ 7 < 2 ^ 8 := by norm_num
    exact lt_of_le_of_lt hcard (lt_of_lt_of_le h64 (hd.trans this))

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Engine
