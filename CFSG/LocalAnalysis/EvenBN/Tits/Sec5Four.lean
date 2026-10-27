module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Classes
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.E32Pairs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.mem_centralizer_tSup_iff (hd : d.Hyp) {X : Subgroup (Equiv.Perm (Fin 1755))}
    (hXD : X ≤ titsD) {x : G} (hx : x ∈ centralizer ({d.t} : Set G)) :
    x ∈ centralizer ((d.liftSub X ⊔ zpowers d.t : Subgroup G) : Set G) ↔
      (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) ∈ centralizer (X : Set (Equiv.Perm (Fin 1755))) := by
  have hxt : x * d.t = d.t * x := mem_centralizer_singleton_iff.1 hx
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro y hy
    have hyl : d.lift y ∈ d.liftSub X ⊔ zpowers d.t :=
      mem_sup_left (mem_liftSub.2 ⟨y, hy, hXD hy, rfl⟩)
    have h1 := mem_centralizer_iff.1 h _ hyl
    exact ((hd.commute_lift_iff hx (hXD hy)).1 h1.symm).symm
  · intro h
    rw [mem_centralizer_iff]
    intro a ha
    rcases ((hd.tSup_facts (d.liftSub_le X)).1 a).1 ha with ha' | ha'
    · obtain ⟨y, hy, hyD, rfl⟩ := mem_liftSub.1 ha'
      exact ((hd.commute_lift_iff hx hyD).2 (mem_centralizer_iff.1 h y hy).symm).symm
    · obtain ⟨y, hy, hyD, hya⟩ := mem_liftSub.1 ha'
      have h1 := ((hd.commute_lift_iff hx hyD).2 (mem_centralizer_iff.1 h y hy).symm)
      rw [hya] at h1
      have ht2 := hd.t_mul_self
      have e : a = d.t * (d.t * a) := by rw [← mul_assoc, ht2, one_mul]
      rw [e]
      calc d.t * (d.t * a) * x = d.t * ((d.t * a) * x) := by group
        _ = d.t * (x * (d.t * a)) := by rw [h1]
        _ = (d.t * x) * (d.t * a) := by group
        _ = x * (d.t * (d.t * a)) := by rw [← hxt]; group

omit [Finite G] in
theorem centralizer_tSup_le (d : Data G) (X : Subgroup (Equiv.Perm (Fin 1755))) :
    centralizer ((d.liftSub X ⊔ zpowers d.t : Subgroup G) : Set G) ≤
      centralizer ({d.t} : Set G) := fun _ hx =>
  mem_centralizer_singleton_iff.2
    (mem_centralizer_iff.1 hx _ (mem_sup_right (mem_zpowers _))).symm

theorem Hyp.centralizer_B
    (hd : d.Hyp) : centralizer (d.B : Set G) = d.B := by
  have hFD := Model.parrottF_le_titsD
  apply le_antisymm
  · intro x hx
    have hxC : x ∈ centralizer ({d.t} : Set G) := d.centralizer_tSup_le _ hx
    have hρ := (hd.mem_centralizer_tSup_iff hFD hxC).1 hx
    have hρF : (d.ρ ⟨x, hxC⟩ : Equiv.Perm (Fin 1755)) ∈ Model.parrottF := by
      rw [← Model.titsA_centralizer_parrottF]
      exact mem_inf.2 ⟨(d.ρ ⟨x, hxC⟩).2, hρ⟩
    have hmem : d.lift (d.ρ ⟨x, hxC⟩ : Equiv.Perm (Fin 1755)) ∈ d.F :=
      mem_liftSub.2 ⟨_, hρF, hFD hρF, rfl⟩
    rcases hd.eq_lift_or hxC (hFD hρF) with h | h
    · rw [h]
      exact mem_sup_left hmem
    · rw [h]
      exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hmem)
  · intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hd.B_facts.2.2.1.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)

theorem parrottV_five_mem_centralizer_hatE
    : Model.parrottV 5 ∈ centralizer (Model.hatE : Set (Equiv.Perm (Fin 1755))) := by
  rw [Model.hatE_eq_parrottU_eight]
  have hle : Model.parrottU 8 ≤ centralizer ({Model.parrottV 5} : Set (Equiv.Perm (Fin 1755))) := by
    rw [Model.parrottU, closure_le]
    rintro _ ⟨i, ⟨hi1, hi2⟩, rfl⟩
    have hi : i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by omega
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      exact (Model.parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by decide) (by decide))
  rw [mem_centralizer_iff]
  intro y hy
  exact mem_centralizer_singleton_iff.1 (hle hy)

theorem Hyp.centralizer_A
    (hd : d.Hyp) :
    (d.ρ.range = titsD.subgroupOf titsA ∧ centralizer (d.A : Set G) = d.A) ∨
      (d.ρ.range = ⊤ ∧ ∀ y (hy : y ∈ centralizer ({d.t} : Set G)),
        (d.ρ ⟨y, hy⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 5 →
          centralizer (d.A : Set G) = d.A ⊔ zpowers y) := by
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  obtain ⟨hAF, -, -, hFD, -, -⟩ := Model.titsA_centralizer_hatE
  have hmemA : ∀ x (hx : x ∈ centralizer ({d.t} : Set G)),
      (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) ∈ titsD →
      (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) ∈ Model.hatF → x ∈ d.A := by
    intro x hx hD hF
    have hE : (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) ∈ Model.hatE := hFD ▸ mem_inf.2 ⟨hF, hD⟩
    have hmem : d.lift (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) ∈ d.E :=
      mem_liftSub.2 ⟨_, hE, hD, rfl⟩
    rcases hd.eq_lift_or hx hD with h | h
    · rw [h]
      exact mem_sup_left hmem
    · rw [h]
      exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hmem)
  have hcF : ∀ x (hx : x ∈ centralizer (d.A : Set G)),
      (d.ρ ⟨x, d.centralizer_tSup_le _ hx⟩ : Equiv.Perm (Fin 1755)) ∈ Model.hatF := by
    intro x hx
    rw [← hAF]
    exact mem_inf.2 ⟨(d.ρ _).2, (hd.mem_centralizer_tSup_iff hED _).1 hx⟩
  have hAle : d.A ≤ centralizer (d.A : Set G) := fun x hx => by
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hd.A_facts.2.2.1.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  rcases hd.range_ρ with hR | hR
  · refine Or.inl ⟨hR, le_antisymm (fun x hx => ?_) hAle⟩
    have hxC := d.centralizer_tSup_le _ hx
    have hD : (d.ρ ⟨x, hxC⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
      have h : d.ρ ⟨x, hxC⟩ ∈ d.ρ.range := ⟨_, rfl⟩
      rw [hR, mem_subgroupOf] at h
      exact h
    exact hmemA x hxC hD (hcF x hx)
  · refine Or.inr ⟨hR, fun y hy hy5 => le_antisymm (fun x hx => ?_) (sup_le hAle ?_)⟩
    · have hxC := d.centralizer_tSup_le _ hx
      have hxF := hcF x hx
      by_cases hD : (d.ρ ⟨x, hxC⟩ : Equiv.Perm (Fin 1755)) ∈ titsD
      · exact mem_sup_left (hmemA x hxC hD hxF)
      ·
        have hyx : y⁻¹ * x ∈ centralizer ({d.t} : Set G) := mul_mem (inv_mem hy) hxC
        have hρyx : (d.ρ ⟨y⁻¹ * x, hyx⟩ : Equiv.Perm (Fin 1755)) =
            (Model.parrottV 5)⁻¹ * d.ρ ⟨x, hxC⟩ := by
          have e : (⟨y⁻¹ * x, hyx⟩ : centralizer ({d.t} : Set G)) = (⟨y, hy⟩)⁻¹ * ⟨x, hxC⟩ :=
            rfl
          rw [e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hy5]
        have h5F : Model.parrottV 5 ∈ Model.hatF := by
          rw [← hAF]
          exact mem_inf.2 ⟨by rw [← hy5]; exact (d.ρ _).2, parrottV_five_mem_centralizer_hatE⟩
        have h5D : Model.parrottV 5 ∉ titsD := by
          rw [Model.parrottV_mem_titsD_iff (by norm_num)]
          decide
        have hA5 : Model.parrottV 5 ∈ titsA := by rw [← hy5]; exact (d.ρ _).2
        have hyxD : (d.ρ ⟨y⁻¹ * x, hyx⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
          rw [hρyx]
          exact (Model.mul_mem_titsD_iff (inv_mem hA5) (d.ρ ⟨x, hxC⟩).2).2
            (iff_of_false (fun h => h5D (by simpa using inv_mem h)) hD)
        have hyxF : (d.ρ ⟨y⁻¹ * x, hyx⟩ : Equiv.Perm (Fin 1755)) ∈ Model.hatF := by
          rw [hρyx]
          exact mul_mem (inv_mem h5F) hxF
        have h1 := hmemA _ hyx hyxD hyxF
        have e : x = y * (y⁻¹ * x) := by group
        rw [e]
        exact mul_mem (mem_sup_right (mem_zpowers y)) (mem_sup_left h1)
    · rw [zpowers_le]
      refine (hd.mem_centralizer_tSup_iff hED hy).2 ?_
      rw [hy5]
      exact parrottV_five_mem_centralizer_hatE

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
