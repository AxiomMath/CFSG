module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB5

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer Seven

namespace Eight2

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

theorem conj_mem_conjugate_D {u t x : X} (hu : u ∈ normalizer (h.S : Set X)) (ht : t ∈ h.S)
    (hx : x ∈ conjugate h.D u) : t * x * t⁻¹ ∈ conjugate h.D u := by
  rw [mem_conjugate_iff] at hx ⊢
  have htu : u * t * u⁻¹ ∈ h.S := (mem_normalizer_iff.mp hu t).mp ht
  have := h.sec8_conj_mem_D htu hx
  rwa [show u * t * u⁻¹ * (u * x * u⁻¹) * (u * t * u⁻¹)⁻¹ = u * (t * x * t⁻¹) * u⁻¹ by group]
    at this

theorem conjugate_D_le_S {u : X} (hu : u ∈ normalizer (h.S : Set X)) : conjugate h.D u ≤ h.S :=
  (map_mono h.D_le_S).trans (conjugate_le_of_mem_normalizer' hu)

theorem D_inf_conjugate_D (Z : ZData h) {u : X} (hu : u ∈ normalizer (h.S : Set X))
    (huz : u⁻¹ * Z.z * u = h.a) : h.D ⊓ conjugate h.D u = ⊥ := by
  by_contra hne
  obtain ⟨w, hw, hw1, hwZ⟩ := exists_mem_center_of_normal h.isPGroup_S
    (inf_le_left.trans h.D_le_S)
    (fun t ht v hv => mem_inf.mpr ⟨h.sec8_conj_mem_D ht (mem_inf.mp hv).1,
      conj_mem_conjugate_D hu ht (mem_inf.mp hv).2⟩) hne
  obtain ⟨hwD, hwu⟩ := mem_inf.mp hw
  rw [mem_conjugate_iff] at hwu
  have hwz : w = Z.z :=
    (Z.hZDz w hwD fun d hd => (hwZ d (h.D_le_S hd)).symm).resolve_left hw1
  have hpZ : ∀ t ∈ h.S, t * (u * w * u⁻¹) = u * w * u⁻¹ * t := by
    intro t ht
    have htg : u⁻¹ * t * u ∈ h.S := by
      have := (mem_normalizer_iff.mp (inv_mem hu) t).mp ht
      rwa [inv_inv] at this
    have h1 := hwZ _ htg
    calc t * (u * w * u⁻¹) = u * ((u⁻¹ * t * u) * w) * u⁻¹ := by group
      _ = u * (w * (u⁻¹ * t * u)) * u⁻¹ := by rw [h1]
      _ = u * w * u⁻¹ * t := by group
  have hp1 : u * w * u⁻¹ ≠ 1 := fun h1 => hw1 (by
    calc w = u⁻¹ * (u * w * u⁻¹) * u := by group
      _ = 1 := by rw [h1]; group)
  have hpz : u * w * u⁻¹ = Z.z :=
    (Z.hZDz _ hwu fun d hd => (hpZ d (h.D_le_S hd)).symm).resolve_left hp1
  apply Z.hzP
  have h2 : u * Z.z * u⁻¹ = Z.z := hwz ▸ hpz
  have : Z.z = h.a := by
    calc Z.z = u⁻¹ * (u * Z.z * u⁻¹) * u := by group
      _ = u⁻¹ * Z.z * u := by rw [h2]
      _ = h.a := huz
  rw [this]
  exact h.a_mem_P

theorem D_comm_conjugate_D (Z : ZData h) {u : X} (hu : u ∈ normalizer (h.S : Set X))
    (huz : u⁻¹ * Z.z * u = h.a) {d x : X} (hd : d ∈ h.D) (hx : x ∈ conjugate h.D u) :
    d * x = x * d := by
  have hxS := conjugate_D_le_S hu hx
  have h1 : d * x * d⁻¹ * x⁻¹ ∈ h.D ⊓ conjugate h.D u := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [show d * x * d⁻¹ * x⁻¹ = d * (x * d⁻¹ * x⁻¹) by group]
      exact mul_mem hd (h.sec8_conj_mem_D hxS (inv_mem hd))
    · exact mul_mem (conj_mem_conjugate_D hu (h.D_le_S hd) hx) (inv_mem hx)
  rw [D_inf_conjugate_D Z hu huz, mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem rhoE_comm_innOf {x : X} (hxS : x ∈ h.S) (hxD : ∀ d ∈ h.D, x * d = d * x) :
    ∀ σ ∈ innOf (Dbar h), σ * rhoE h.J x = rhoE h.J x * σ := by
  intro σ hσ
  rw [← rhoImg_eq_innOf h.D_le_J] at hσ
  obtain ⟨d, hd, hdN, rfl⟩ := exists_of_mem_rhoImg hσ
  have hxN := h.S_le_normalizer hxS
  rw [← rhoE_mul hdN hxN, ← rhoE_mul hxN hdN, hxD d hd]

theorem rhoE_b'_comm {u b : X} (hbuS : u⁻¹ * b * u ∈ h.S)
    (hbD : ∀ d ∈ h.D, u⁻¹ * b * u * d = d * (u⁻¹ * b * u)) :
    ∀ σ ∈ innOf (Dbar h), σ * rhoE h.J (u⁻¹ * b * u) = rhoE h.J (u⁻¹ * b * u) * σ :=
  rhoE_comm_innOf hbuS hbD

theorem innOf_le_rhoImg (Z : ZData h) (hC : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a)
    {u : X} (hu : u ∈ normalizer (h.S : Set X)) (hua : u⁻¹ * h.a * u = Z.z)
    (huz : u⁻¹ * Z.z * u = h.a) (huu : u * u ∈ h.S) {b : X} (hbP : b ∈ h.P) (hbb : b * b = 1)
    (hb1 : b ≠ 1) (hba : b ≠ h.a) (hbD : ∀ d ∈ h.D, u⁻¹ * b * u * d = d * (u⁻¹ * b * u)) :
    innOf (Dbar h) ≤ rhoImg h.J (conjugate h.P u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hua' : u⁻¹ * h.a * u ≠ h.a := by
    rw [hua]
    exact fun h1 => Z.hzP (h1 ▸ h.a_mem_P)
  set W := conjugate h.P u with hWdef
  have hWS : W ≤ h.S := h.sec8_conjugate_P_le_S hu
  have hWN : W ≤ normalizer (h.J : Set X) := hWS.trans h.S_le_normalizer
  have hWK := conjugate_P_inf_kernel' hC hu hua'
  have hinj : ∀ x ∈ W, ∀ y ∈ W, rhoE h.J x = rhoE h.J y → x = y := by
    intro x hx y hy hxy
    have h1 : rhoE h.J (x * y⁻¹) = 1 := by
      rw [rhoE_mul (hWN hx) (inv_mem (hWN hy)), rhoE_inv (hWN hy), hxy, mul_inv_cancel]
    rw [rhoE_eq_one_iff (mul_mem (hWN hx) (inv_mem (hWN hy)))] at h1
    have h2 : x * y⁻¹ ∈ W ⊓ coreActionKernel h.J := mem_inf.mpr ⟨mul_mem hx (inv_mem hy), h1⟩
    rw [hWK, mem_bot, mul_inv_eq_one] at h2
    exact h2
  have hzW : Z.z ∈ W := by
    rw [mem_conjugate_iff, ← hua, show u * (u⁻¹ * h.a * u) * u⁻¹ = h.a by group]
    exact h.a_mem_P
  have hbW : u⁻¹ * b * u ∈ W := by
    rw [mem_conjugate_iff, show u * (u⁻¹ * b * u) * u⁻¹ = b by group]
    exact hbP
  have hzN := hWN hzW
  have hbN := hWN hbW
  set e := rhoE h.J (u⁻¹ * b * u) with he_def
  set ζ := rhoE h.J Z.z with hζ_def
  have he := rhoE_b'_comm (hWS hbW) hbD
  have hζc := rhoE_comm_innOf (h.D_le_S Z.hzD) fun d hd => (Z.hzS d (h.D_le_S hd)).symm
  set R := rhoImg h.J h.S ⊓ centralizer (innOf (Dbar h) : Set (MulAut (Jbar h))) with hR
  have hR2 : IsPGroup 2 R :=
    ((h.isPGroup_S.of_equiv (subgroupOfEquivOfLe h.S_le_normalizer).symm).map _).to_le
      inf_le_left
  have hR4 := Z.hC4 R hR2 inf_le_right
  have hζ2 : ζ * ζ = 1 := by rw [← rhoE_mul hzN hzN, Z.hzz, rhoE_one]
  have hζ1 : ζ ≠ 1 := fun h1 =>
    Z.hzP (mem_inf.mpr ⟨h.D_le_S Z.hzD, (rhoE_eq_one_iff hzN).mp h1⟩)
  have hbb' : u⁻¹ * b * u * (u⁻¹ * b * u) = 1 := by
    rw [show u⁻¹ * b * u * (u⁻¹ * b * u) = u⁻¹ * (b * b) * u by group, hbb]
    group
  have he2 : e * e = 1 := by rw [← rhoE_mul hbN hbN, hbb', rhoE_one]
  have he1 : e ≠ 1 := by
    intro h1
    have h2 := hinj _ hbW 1 (one_mem _) (h1.trans (rhoE_one _).symm)
    apply hb1
    calc b = u * (u⁻¹ * b * u) * u⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have heζ : e ≠ ζ := by
    intro h1
    have h2 := hinj _ hbW _ hzW h1
    apply hba
    calc b = u * (u⁻¹ * b * u) * u⁻¹ := by group
      _ = u * (u⁻¹ * h.a * u) * u⁻¹ := by rw [h2, hua]
      _ = h.a := by group
  have hζmem : ζ ∈ innOf (Dbar h) := by
    rw [← rhoImg_eq_innOf h.D_le_J]
    exact rhoE_mem_rhoImg (h.D_le_S.trans h.S_le_normalizer) Z.hzD
  have hcomm : ∀ x ∈ zpowers ζ, ∀ y ∈ zpowers e, x * y = y * x := by
    intro x hx y hy
    rcases eq_one_or_of_mem_zpowers (orderOf_eq_two_of hζ2 hζ1) hx with rfl | rfl
    · rw [one_mul, mul_one]
    · rcases eq_one_or_of_mem_zpowers (orderOf_eq_two_of he2 he1) hy with rfl | rfl
      · rw [one_mul, mul_one]
      · exact he _ hζmem
  have hdisj : zpowers ζ ⊓ zpowers e = ⊥ :=
    zpowers_inf_eq_bot hζ2 hζ1 he2 he1 heζ.symm
  have hK4 : Nat.card ↥(zpowers ζ ⊔ zpowers e) = 4 := by
    rw [card_sup_of_commute hcomm hdisj, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_two_of hζ2 hζ1, orderOf_eq_two_of he2 he1]
  have hKR : zpowers ζ ⊔ zpowers e ≤ R := by
    refine sup_le ?_ ?_ <;> rw [zpowers_le] <;> refine mem_inf.mpr ⟨?_, ?_⟩
    · exact rhoE_mem_rhoImg h.S_le_normalizer (h.D_le_S Z.hzD)
    · rw [mem_centralizer_iff]
      exact hζc
    · exact rhoE_mem_rhoImg h.S_le_normalizer (hWS hbW)
    · rw [mem_centralizer_iff]
      exact he
  have hKeq : zpowers ζ ⊔ zpowers e = R := eq_of_le_of_card_ge hKR (by rw [hK4]; exact hR4)
  intro σ hσ
  rw [← rhoImg_eq_innOf h.D_le_J] at hσ
  obtain ⟨d, hd, hdN, rfl⟩ := exists_of_mem_rhoImg hσ
  have hxD : u⁻¹ * d * u ∈ conjugate h.D u := by
    rw [mem_conjugate_iff, show u * (u⁻¹ * d * u) * u⁻¹ = d by group]
    exact hd
  have hxS : u⁻¹ * d * u ∈ h.S := conjugate_D_le_S hu hxD
  have hxN := h.S_le_normalizer hxS
  have hxR : rhoE h.J (u⁻¹ * d * u) ∈ R := by
    refine mem_inf.mpr ⟨rhoE_mem_rhoImg h.S_le_normalizer hxS, ?_⟩
    rw [mem_centralizer_iff]
    exact rhoE_comm_innOf hxS fun d' hd' => (D_comm_conjugate_D Z hu huz hd' hxD).symm
  rw [← hKeq] at hxR
  obtain ⟨α, hα, β, hβ, hαβ⟩ := exists_mul_of_mem_sup hcomm hxR
  have hw : ∃ w ∈ W, rhoE h.J w = rhoE h.J (u⁻¹ * d * u) := by
    rcases eq_one_or_of_mem_zpowers (orderOf_eq_two_of hζ2 hζ1) hα with rfl | rfl <;>
      rcases eq_one_or_of_mem_zpowers (orderOf_eq_two_of he2 he1) hβ with rfl | rfl
    · exact ⟨1, one_mem _, by rw [rhoE_one, hαβ, mul_one]⟩
    · exact ⟨u⁻¹ * b * u, hbW, by rw [hαβ, one_mul]⟩
    · exact ⟨Z.z, hzW, by rw [hαβ, mul_one]⟩
    · exact ⟨Z.z * (u⁻¹ * b * u), mul_mem hzW hbW, by rw [rhoE_mul hzN hbN, hαβ]⟩
  obtain ⟨w, hwW, hwx⟩ := hw
  have hwN := hWN hwW
  have hxw : u⁻¹ * d * u * w⁻¹ ∈ h.P := by
    refine mem_inf.mpr ⟨mul_mem hxS (inv_mem (hWS hwW)), (rhoE_eq_one_iff
      (mul_mem hxN (inv_mem hwN))).mp ?_⟩
    rw [rhoE_mul hxN (inv_mem hwN), rhoE_inv hwN, hwx, mul_inv_cancel]
  have h1 : u * (u⁻¹ * d * u * w⁻¹) * u⁻¹ ∈ W := by
    rw [mem_conjugate_iff, show u * (u * (u⁻¹ * d * u * w⁻¹) * u⁻¹) * u⁻¹ =
      (u * u) * (u⁻¹ * d * u * w⁻¹) * (u * u)⁻¹ by group]
    exact h.conj_mem_P huu hxw
  have h2 : u * w * u⁻¹ ∈ h.P := mem_conjugate_iff.mp hwW
  have h2N : u * w * u⁻¹ ∈ normalizer (h.J : Set X) := h.S_le_normalizer (h.P_le_S h2)
  have hd' : d = (u * (u⁻¹ * d * u * w⁻¹) * u⁻¹) * (u * w * u⁻¹) := by group
  rw [hd', rhoE_mul (hWN h1) h2N, (rhoE_eq_one_iff h2N).mpr (mem_inf.mp h2).2, mul_one]
  exact rhoE_mem_rhoImg hWN h1

end Eight2

end CFSG.ComponentClassification.GSThmB
