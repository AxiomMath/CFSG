module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.E32NormF
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S14Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section S14B

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem liftSub_inf' {X Y : Subgroup (Equiv.Perm (Fin 1755))} (hX : X ≤ titsD) (hY : Y ≤ titsD) :
    d.liftSub (X ⊓ Y) = d.liftSub X ⊓ d.liftSub Y := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx, hxD, rfl⟩ := Data.mem_liftSub.1 hg
    exact ⟨Data.mem_liftSub.2 ⟨x, hx.1, hxD, rfl⟩, Data.mem_liftSub.2 ⟨x, hx.2, hxD, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨x, hx, hxD, rfl⟩ := Data.mem_liftSub.1 h1
    obtain ⟨y, hy, hyD, hyx⟩ := Data.mem_liftSub.1 h2
    have := d.lift_inj hyD hxD hyx
    exact Data.mem_liftSub.2 ⟨x, ⟨hx, this ▸ hy⟩, hxD, rfl⟩

theorem mem_normalizer_of_lift {X Y : Subgroup (Equiv.Perm (Fin 1755))} (hX : X ≤ titsD)
    (hY : Y ≤ titsD) {x : Equiv.Perm (Fin 1755)} (hx : x ∈ X)
    (h : d.lift x ∈ normalizer ((d.liftSub Y : Subgroup G) : Set G)) :
    x ∈ normalizer (Y : Set (Equiv.Perm (Fin 1755))) := by
  have key : ∀ x ∈ X, d.lift x ∈ normalizer ((d.liftSub Y : Subgroup G) : Set G) →
      ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := by
    intro x hx h y hy
    have hxD : x ∈ titsD := hX hx
    have hyD : y ∈ titsD := hY hy
    have h1 : d.lift y ∈ d.liftSub Y := Data.mem_liftSub.2 ⟨y, hy, hyD, rfl⟩
    have h2 := (mem_normalizer_iff.1 h (d.lift y)).1 h1
    rw [← d.lift_inv hxD, ← d.lift_mul hxD hyD, ← d.lift_mul (mul_mem hxD hyD) (inv_mem hxD)] at h2
    obtain ⟨z, hz, hzD, hzx⟩ := Data.mem_liftSub.1 h2
    have := d.lift_inj hzD (mul_mem (mul_mem hxD hyD) (inv_mem hxD)) hzx
    exact this ▸ hz
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => key x hx h y hy
  · intro hy
    have hxinv : d.lift x⁻¹ ∈ normalizer ((d.liftSub Y : Subgroup G) : Set G) := by
      rw [d.lift_inv (hX hx)]
      exact inv_mem h
    have h3 := key x⁻¹ (inv_mem hx) hxinv _ hy
    rwa [inv_inv, show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h3

theorem lift_mem_M (hd : d.Hyp) {x : Equiv.Perm (Fin 1755)} (hxD : x ∈ titsD)
    (hxN : x ∈ normalizer (Model.hatE : Set (Equiv.Perm (Fin 1755)))) : d.lift x ∈ d.M := by
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  have hyC : d.lift x ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem x)
  show d.lift x ∈ normalizer ((d.liftSub Model.hatE ⊔ zpowers d.t : Subgroup G) : Set G)
  rw [hd.mem_normalizer_tSup_iff hED hyC, hd.ρ_lift hxD]
  exact hxN

theorem parrottV_mem_normalizer_hatE (i : ℕ) :
    Model.parrottV i ∈ normalizer (Model.hatE : Set (Equiv.Perm (Fin 1755))) :=
  Model.twoF4H_le_normalizer_hatE (Model.twoF4S_le_twoF4H (Model.parrottV_mem_twoF4S i))

theorem parrottV_seven_mem_titsD : Model.parrottV 7 ∈ titsD :=
  (Model.parrottV_mem_titsD_iff (by norm_num)).2 (by decide)

theorem parrottV_two_mem_titsD : Model.parrottV 2 ∈ titsD :=
  (Model.parrottV_mem_titsD_iff (by norm_num)).2 (by decide)

theorem pv7_mem_F : d.pv 7 ∈ d.F :=
  Data.mem_liftSub.2 ⟨Model.parrottV 7, Model.parrottV_seven_mem_parrottF, parrottV_seven_mem_titsD, rfl⟩

theorem pv7_mem_M (hd : d.Hyp) : d.pv 7 ∈ d.M :=
  lift_mem_M hd parrottV_seven_mem_titsD (parrottV_mem_normalizer_hatE 7)

theorem pv2_mem_M (hd : d.Hyp) : d.pv 2 ∈ d.M :=
  lift_mem_M hd parrottV_two_mem_titsD (parrottV_mem_normalizer_hatE 2)

theorem pv7_not_mem_E : d.pv 7 ∉ d.E := by
  intro h
  obtain ⟨x, hx, hxD, hxe⟩ := Data.mem_liftSub.1 h
  have := d.lift_inj hxD parrottV_seven_mem_titsD hxe
  exact Model.parrottV_seven_not_mem_hatE (this ▸ hx)

theorem pv_mem_L (i : ℕ) : d.pv i ∈ d.L := d.lift_mem _

theorem pv2_mul_self : d.pv 2 * d.pv 2 = 1 := (Data.five_facts d).2.2.2.1

theorem pv2_mem_zL : d.pv 2 ∈ d.zL := (Data.five_facts d).2.2.2.2.2.1

theorem t_mul_pv2_mem_tG (hd : d.Hyp) : d.t * d.pv 2 ∈ d.tG :=
  hd.t_mul_mem_tG_of_zL pv2_mem_zL

theorem exists_P1_conj_t_mul_pv7 (h13 : Node13 d) :
    ∃ g ∈ P1 d, g * d.t * g⁻¹ = d.t * d.pv 7 := by
  obtain ⟨⟨-, hcl⟩, -⟩ := h13
  have : d.t * d.pv 7 ∈ {x | ∃ p ∈ P1 d, p * d.t * p⁻¹ = x} := by
    rw [hcl]
    exact ⟨d.pv 7, pv7_mem_F, rfl⟩
  obtain ⟨p, hp, hpe⟩ := this
  exact ⟨p, hp, hpe⟩

theorem F_le_P1 (h11 : Node11 d z₀) : d.F ≤ P1 d :=
  (le_sup_right : d.F ≤ (d.s56Q2 ⊓ d.s56P ⊓ centralizer ({z₀} : Set G)) ⊔ d.F).trans h11.1.2.1

theorem t_not_mem_P1 (hd : d.Hyp) (h13 : Node13 d) (hP1a : IsElemAbelian 2 (P1 d)) :
    d.t ∉ P1 d := by
  intro ht
  obtain ⟨⟨-, hcl⟩, -⟩ := h13
  have hF32 : Nat.card d.F = 32 := hd.B_facts.1
  obtain ⟨f, hfF, hf1⟩ : ∃ f ∈ d.F, f ≠ 1 := by
    by_contra hall
    push Not at hall
    have : d.F = ⊥ := eq_bot_iff.2 fun f hf => by rw [mem_bot]; exact hall f hf
    rw [this, Subgroup.card_bot] at hF32
    norm_num at hF32
  have hmem : d.t * f ∈ {x | ∃ p ∈ P1 d, p * d.t * p⁻¹ = x} := by
    rw [hcl]
    exact ⟨f, hfF, rfl⟩
  obtain ⟨p, hp, hpe⟩ := hmem
  have hpt : p * d.t * p⁻¹ = d.t := by
    rw [elemAbelian_comm hP1a hp ht]
    group
  rw [hpt] at hpe
  exact hf1 (mul_left_cancel (hpe.symm.trans (mul_one _).symm))

theorem B_inf_P1_le_F (hd : d.Hyp) (h11 : Node11 d z₀) (hP1t : d.t ∉ P1 d) :
    d.B ⊓ P1 d ≤ d.F := by
  rintro x ⟨hxB, hxP⟩
  rcases ((hd.tSup_facts (d.liftSub_le Model.parrottF)).1 x).1 hxB with h | h
  · exact h
  · exfalso
    apply hP1t
    have e : d.t = (d.t * x) * x⁻¹ := by group
    rw [e]
    exact mul_mem (F_le_P1 h11 h) (inv_mem hxP)

theorem mem_normalizer_centralizer_singleton {f s : G} (h : f * s = s * f) :
    f ∈ normalizer ((centralizer ({s} : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  have h1 : f⁻¹ * s = s * f⁻¹ := by
    calc f⁻¹ * s = f⁻¹ * s * f * f⁻¹ := by group
      _ = f⁻¹ * (s * f) * f⁻¹ := by group
      _ = f⁻¹ * (f * s) * f⁻¹ := by rw [h]
      _ = s * f⁻¹ := by group
  constructor
  · intro hx
    calc f * x * f⁻¹ * s = f * x * (f⁻¹ * s) := by group
      _ = f * x * (s * f⁻¹) := by rw [h1]
      _ = f * (x * s) * f⁻¹ := by group
      _ = f * (s * x) * f⁻¹ := by rw [hx]
      _ = (f * s) * x * f⁻¹ := by group
      _ = (s * f) * x * f⁻¹ := by rw [h]
      _ = s * (f * x * f⁻¹) := by group
  · intro hx
    have h2 : f * x * f⁻¹ * s = s * (f * x * f⁻¹) := hx
    calc x * s = f⁻¹ * (f * x * f⁻¹ * s) * f := by
          rw [show f⁻¹ * (f * x * f⁻¹ * s) * f = x * (f⁻¹ * s * f) by group, h1]; group
      _ = f⁻¹ * (s * (f * x * f⁻¹)) * f := by rw [h2]
      _ = (f⁻¹ * s * f) * x := by group
      _ = s * x := by rw [h1]; group

theorem inf_centralizer_eq_conj_F (hd : d.Hyp) (h11 : Node11 d z₀) {s k : G}
    (hkt : k * d.t * k⁻¹ = s) (hP1t : d.t ∉ P1 d)
    (hDB : zpowers s ⊔ (d.s56V ⊓ centralizer ({s} : Set G)) = d.B.map (MulAut.conj k).toMonoidHom)
    (hVP : d.s56V = (P1 d).map (MulAut.conj k).toMonoidHom) :
    d.s56V ⊓ centralizer ({s} : Set G) = d.F.map (MulAut.conj k).toMonoidHom := by
  refine Subgroup.ext fun u => ?_
  rw [mem_inf]
  constructor
  · rintro ⟨huV, huC⟩
    have huD : u ∈ d.B.map (MulAut.conj k).toMonoidHom :=
      hDB ▸ mem_sup_right (mem_inf.2 ⟨huV, huC⟩)
    rw [hVP] at huV
    rw [mem_map_conj_iff'] at huV huD
    rw [mem_map_conj_iff']
    exact B_inf_P1_le_F hd h11 hP1t ⟨huD, huV⟩
  · intro hu
    rw [mem_map_conj_iff'] at hu
    refine ⟨?_, ?_⟩
    · rw [hVP, mem_map_conj_iff']
      exact F_le_P1 h11 hu
    · rw [mem_centralizer_singleton_iff]
      have hft : (k⁻¹ * u * k) * d.t = d.t * (k⁻¹ * u * k) :=
        hd.L_comm_t (d.liftSub_le _ hu)
      rw [← hkt]
      calc u * (k * d.t * k⁻¹) = k * ((k⁻¹ * u * k) * d.t) * k⁻¹ := by group
        _ = k * (d.t * (k⁻¹ * u * k)) * k⁻¹ := by rw [hft]
        _ = k * d.t * k⁻¹ * u := by group

end S14B

end CFSG.LocalAnalysis.EvenBN.Tits.N
