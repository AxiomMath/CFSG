module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj DEdgeless)

namespace OctaSys

variable {ι V : Type*} [CommGroup V] (S : OctaSys ι V)

theorem nn_eq_zero_of_reach {p₀ q t : ι} (hq : ¬ S.Reach p₀ q) (ht : S.Reach p₀ t) :
    S.nn p₀ t = 0 := by
  induction ht with
  | refl => exact S.nn_self _
  | tail hb hbc ih =>
    rename_i b c
    have hbq : ¬ S.Reach b q := fun hbq => hq (S.reach_trans hb hbq)
    exact S.nn_eq_zero_of_far hbq (by rw [S.nn_symm]; exact ih) hbc

end OctaSys

section Graph

variable {X : Type} [Group X] [Finite X] {r : ℕ} {Φ : Set (Subgroup X)}

namespace SetE

variable (h : SetE r Φ)
include h

theorem reflTransGen_of_nnv_eq_zero {a b : ↥Φ} (hab : nnv a b = 0) :
    Relation.ReflTransGen (fun M N : Subgroup X => N ∈ Φ ∧ dAdj Φ M N) a.1 b.1 := by
  by_cases e : a = b
  · rw [e]
  · have hnc : ¬ NC a.1 b.1 := nnv_eq_zero_iff.mp hab
    have hc : Commutes a.1 b.1 := by
      by_contra hc'
      exact hnc ⟨fun e' => e (Subtype.ext e'), hc'⟩
    refine Relation.ReflTransGen.single ⟨b.2, Or.inl ?_⟩
    exact (h.omegaNbr_iff a.2).mpr ⟨b.2, fun e' => e (Subtype.ext e'.symm), hc.symm⟩

theorem dConnected_of_reach (p₀ : ↥Φ) (hr : ∀ q : ↥Φ, h.octa.Reach p₀ q) : DConnected Φ := by
  intro K hK J hJ
  have e2 := h.octa.reach_trans (h.octa.reach_symm (hr ⟨K, hK⟩)) (hr ⟨J, hJ⟩)
  exact Relation.ReflTransGen.lift' (p := fun M N : Subgroup X => N ∈ Φ ∧ dAdj Φ M N)
    Subtype.val (fun a b hab => h.reflTransGen_of_nnv_eq_zero hab) _ _ e2

theorem exists_far (hd : ¬ DConnected Φ) (p₀ : ↥Φ) : ∃ q : ↥Φ, ¬ h.octa.Reach p₀ q := by
  by_contra hall
  push Not at hall
  exact hd (h.dConnected_of_reach p₀ hall)

theorem nnv_eq_zero_of_omegaNbr {K J : Subgroup X} (hK : K ∈ Φ) (hJ : J ∈ omegaNbr Φ K) :
    nnv (⟨K, hK⟩ : ↥Φ) ⟨J, hJ.1⟩ = 0 := by
  rw [nnv_eq_zero_iff]
  intro hnc
  exact hnc.2 (((h.omegaNbr_iff hK).mp hJ).2.2.symm)

theorem dConnected_of_five (B : Fin 5 → Subgroup X) (hB : ∀ i, B i ∈ Φ)
    (hinj : Function.Injective B) (hadj : ∀ i j, i ≠ j → B j ∈ omegaNbr Φ (B i)) :
    DConnected Φ := by
  by_contra hd
  obtain ⟨q, hq⟩ := h.exists_far hd ⟨B 0, hB 0⟩
  refine h.octa.five_clique_false (fun a => ⟨B a, hB a⟩)
    (fun a b e => hinj (congrArg Subtype.val e)) (fun a b => ?_) q hq
  by_cases hab : a = b
  · rw [hab]
    exact nnv_self _
  · exact h.nnv_eq_zero_of_omegaNbr (hB a) (hadj a b hab)

theorem commutes_of_nnv_eq_zero {a b : ↥Φ} (hab : nnv a b = 0) (hne : a ≠ b) :
    Commutes a.1 b.1 := by
  by_contra hc
  exact nnv_eq_zero_iff.mp hab ⟨fun e => hne (Subtype.ext e), hc⟩

theorem nnv_eq_of_adj (hd : ¬ DConnected Φ) (p₀ p₁ : ↥Φ) (h01 : nnv p₀ p₁ = 0) (t : ↥Φ) :
    nnv t p₀ = nnv t p₁ := by
  obtain ⟨q, hq⟩ := h.exists_far hd p₀
  by_cases ht : h.octa.Reach p₀ t
  · have h0t : nnv p₀ t = 0 := h.octa.nn_eq_zero_of_reach hq ht
    have h1 : nnv t p₁ = 0 := h.octa.nn_eq_zero_of_far hq h0t h01
    rw [h1, nnv_symm, h0t]
  · have h0 : h.octa.nn p₀ p₀ = 0 := nnv_self p₀
    have e0 : nnv t p₀ = 1 := h.octa.nn_eq_one_of_far ht h0
    have e1 : nnv t p₁ = 1 := h.octa.nn_eq_one_of_far ht h01
    rw [e0, e1]

theorem commute_of_mem (hd : ¬ DConnected Φ) (p₀ p₁ : ↥Φ) (h01 : nnv p₀ p₁ = 0) (T : ↥Φ)
    {x : X} (hx : x ∈ T.1) : x * (h.zi p₀ * h.zi p₁) = (h.zi p₀ * h.zi p₁) * x := by
  have hc : ∀ {y : X}, y ∈ h.Ui T → y * (h.zi p₀ * h.zi p₁) = (h.zi p₀ * h.zi p₁) * y := by
    intro y hy
    have e0 : y * h.zi p₀ = h.zi p₀ * y :=
      h.cyc2_comm T.2 p₀.2 (h.gen_spec T).cyc (h.gen_spec p₀).cyc hy
        ((h.gen_spec p₀).z_mem_U (h.isQuatSub p₀.2))
    have e1 : y * h.zi p₁ = h.zi p₁ * y :=
      h.cyc2_comm T.2 p₁.2 (h.gen_spec T).cyc (h.gen_spec p₁).cyc hy
        ((h.gen_spec p₁).z_mem_U (h.isQuatSub p₁.2))
    calc y * (h.zi p₀ * h.zi p₁) = (y * h.zi p₀) * h.zi p₁ := by group
      _ = h.zi p₀ * (y * h.zi p₁) := by rw [e0]; group
      _ = h.zi p₀ * (h.zi p₁ * y) := by rw [e1]
      _ = (h.zi p₀ * h.zi p₁) * y := by group
  rcases (h.gen_spec T).gen_K hx with hxU | hw
  · exact hc hxU
  · have hb : h.bi T * (h.zi p₀ * h.zi p₁) = (h.zi p₀ * h.zi p₁) * h.bi T := by
      have := h.refl_mul_eq T p₀ p₁ (h.nnv_eq_of_adj hd p₀ p₁ h01 T)
      calc h.bi T * (h.zi p₀ * h.zi p₁) = h.bi T * (h.zi p₀ * h.zi p₁) * (h.bi T)⁻¹ * h.bi T := by
            group
        _ = (h.zi p₀ * h.zi p₁) * h.bi T := by rw [this]
    have hx' : x = h.bi T * ((h.bi T)⁻¹ * x) := by group
    have hcw := hc hw
    rw [hx']
    calc h.bi T * ((h.bi T)⁻¹ * x) * (h.zi p₀ * h.zi p₁)
        = h.bi T * (((h.bi T)⁻¹ * x) * (h.zi p₀ * h.zi p₁)) := by group
      _ = h.bi T * ((h.zi p₀ * h.zi p₁) * ((h.bi T)⁻¹ * x)) := by rw [hcw]
      _ = (h.bi T * (h.zi p₀ * h.zi p₁)) * ((h.bi T)⁻¹ * x) := by group
      _ = ((h.zi p₀ * h.zi p₁) * h.bi T) * ((h.bi T)⁻¹ * x) := by rw [hb]
      _ = (h.zi p₀ * h.zi p₁) * (h.bi T * ((h.bi T)⁻¹ * x)) := by group

theorem frame_of_setE (hgen : omegaGen Φ = ⊤) (hd : ¬ DConnected Φ) (B : Fin 3 → Subgroup X)
    (hB : ∀ i, B i ∈ Φ) (hinj : Function.Injective B)
    (hadj : ∀ i j, i ≠ j → B j ∈ omegaNbr Φ (B i)) (u : Fin 3 → X)
    (hu : ∀ i, IsUniqueInvolution (B i) (u i)) :
    u 0 * u 1 ∈ Subgroup.center X ∧
      ∃ B₃ ∈ omegaNbr Φ (B 0), B₃ ≠ B 1 ∧ B₃ ≠ B 2 ∧
        ∀ M ∈ omegaNbr Φ (B 0), M = B 1 ∨ M = B 2 ∨ M = B₃ := by
  have hnn : ∀ i j : Fin 3, nnv (⟨B i, hB i⟩ : ↥Φ) ⟨B j, hB j⟩ = 0 := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
      exact nnv_self _
    · exact h.nnv_eq_zero_of_omegaNbr (hB i) (hadj i j hij)
  have hne : ∀ i j : Fin 3, i ≠ j → (⟨B i, hB i⟩ : ↥Φ) ≠ ⟨B j, hB j⟩ := fun i j hij e =>
    hij (hinj (congrArg Subtype.val e))
  refine ⟨?_, ?_⟩
  · rw [h.inv_eq_zi (hB 0) (hu 0), h.inv_eq_zi (hB 1) (hu 1)]
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ omegaGen Φ := by rw [hgen]; exact Subgroup.mem_top g
    have hle : omegaGen Φ ≤
        Subgroup.centralizer ({h.zi ⟨B 0, hB 0⟩ * h.zi ⟨B 1, hB 1⟩} : Set X) := by
      refine iSup₂_le fun L hL x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h.commute_of_mem hd _ _ (hnn 0 1) ⟨L, hL⟩ hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  · obtain ⟨q, hq⟩ := h.exists_far hd ⟨B 0, hB 0⟩
    have hadj3 : ∀ a b : ↥Φ, a ∈ ({⟨B 0, hB 0⟩, ⟨B 1, hB 1⟩, ⟨B 2, hB 2⟩} : Set ↥Φ) →
        b ∈ ({⟨B 0, hB 0⟩, ⟨B 1, hB 1⟩, ⟨B 2, hB 2⟩} : Set ↥Φ) → h.octa.nn a b = 0 := by
      intro a b ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> exact hnn _ _
    obtain ⟨s, hs, hs0, hs1, hs2, hn0, hn1, hn2⟩ := h.octa.exists_fourth (q := q)
      (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide)) hadj3 hq
    have hs3 : ∀ a b : ↥Φ, a ∈ ({⟨B 0, hB 0⟩, ⟨B 1, hB 1⟩, ⟨B 2, hB 2⟩, s} : Set ↥Φ) →
        b ∈ ({⟨B 0, hB 0⟩, ⟨B 1, hB 1⟩, ⟨B 2, hB 2⟩, s} : Set ↥Φ) → h.octa.nn a b = 0 := by
      intro a b ha hb
      have hsn : ∀ i : Fin 3, h.octa.nn s ⟨B i, hB i⟩ = 0 := by
        intro i
        fin_cases i
        · rw [h.octa.nn_symm]; exact hn0
        · rw [h.octa.nn_symm]; exact hn1
        · rw [h.octa.nn_symm]; exact hn2
      have hns : ∀ i : Fin 3, h.octa.nn ⟨B i, hB i⟩ s = 0 := fun i => by
        rw [h.octa.nn_symm]; exact hsn i
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
        first | exact hnn _ _ | exact hsn _ | exact hns _ | exact h.octa.nn_self _
    have hcs : Commutes s.1 (B 0) := by
      have := h.commutes_of_nnv_eq_zero (a := ⟨B 0, hB 0⟩) (b := s) hn0 (hs0.symm)
      exact this.symm
    refine ⟨s.1, (h.omegaNbr_iff (hB 0)).mpr ⟨s.2, fun e => hs0 (Subtype.ext e), hcs⟩,
      fun e => hs1 (Subtype.ext e), fun e => hs2 (Subtype.ext e), ?_⟩
    intro M hM
    have hM' := (h.omegaNbr_iff (hB 0)).mp hM
    have hm0 : nnv (⟨B 0, hB 0⟩ : ↥Φ) ⟨M, hM'.1⟩ = 0 := h.nnv_eq_zero_of_omegaNbr (hB 0) hM
    rcases h.octa.eq_of_nn_eq_zero_of_far (p₀ := ⟨B 0, hB 0⟩) (p₁ := ⟨B 1, hB 1⟩)
      (p₂ := ⟨B 2, hB 2⟩) (s := s) (q := q) (m := ⟨M, hM'.1⟩) (hne 0 1 (by decide))
      (hne 0 2 (by decide)) (hne 1 2 (by decide)) hs0 hs1 hs2 hs3 hq
      (fun e => hM'.2.1 (congrArg Subtype.val e)) hm0 with hm | hm | hm
    · exact Or.inl (congrArg Subtype.val hm)
    · exact Or.inr (Or.inl (congrArg Subtype.val hm))
    · exact Or.inr (Or.inr (congrArg Subtype.val hm))

end SetE

end Graph

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
