module

public import CFSG.CGT.T75A.RootAbs
public import CFSG.CGT.Timmesfeld75.ListWCSzU3
public import CFSG.Timmesfeld.Bridge.Asc72YU3

public section

namespace CFSG.CGT.T75A

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75
open CFSG.ComponentClassification.AschbacherToolkit.Bender

theorem sylowCenter_map_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (S : Subgroup G) :
    sylowCenter (S.map e.toMonoidHom) = (sylowCenter S).map e.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [AutTransport.mem_sylowCenter_map e]
  exact (Subgroup.mem_map_iff_mem e.injective).symm

theorem exists_sylow_center_conj {D : Type*} [Group D] [Finite D] (S : Sylow 2 D) (g : D) :
    ∃ S' : Sylow 2 D, sylowCenter (S' : Subgroup D) =
      (sylowCenter (S : Subgroup D)).map (MulAut.conj g).toMonoidHom :=
  ⟨S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective,
    sylowCenter_map_equiv (MulAut.conj g) (S : Subgroup D)⟩

theorem benderBorel_of_model {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) : fusionBenderBorel D (2 ^ f) 3 := by
  obtain ⟨e⟩ := exists_psu3_of_statedClassicalModel hf hD
  have : Finite (CFSG.Open.PSU3 2 f) := Finite.of_equiv D e.toEquiv
  exact (bender_psu3_borel_full f hf).map_mulEquiv e.symm

theorem map_sylow_of_center {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) (α : MulAut D) {S : Sylow 2 D}
    (hαT : ∀ x ∈ sylowCenter (S : Subgroup D), α x ∈ sylowCenter (S : Subgroup D)) :
    ∀ s ∈ (S : Subgroup D), α s ∈ (S : Subgroup D) := by
  have hB := benderBorel_of_model hf hD
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  let S' : Sylow 2 D := S.mapSurjective (f := α.toMonoidHom) α.surjective
  have hS' : (S' : Subgroup D) = (S : Subgroup D).map α.toMonoidHom := rfl
  have hmap : (sylowCenter (S : Subgroup D)).map α.toMonoidHom = sylowCenter (S : Subgroup D) := by
    have hle : (sylowCenter (S : Subgroup D)).map α.toMonoidHom ≤
        sylowCenter (S : Subgroup D) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hαT x hx
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective α.injective]
  have hcen : sylowCenter (S' : Subgroup D) = sylowCenter (S : Subgroup D) := by
    ext y
    obtain ⟨x, rfl⟩ := α.surjective y
    rw [hS']
    have h1 := AutTransport.mem_sylowCenter_map α (S := (S : Subgroup D)) (g := x)
    constructor
    · intro h
      exact hαT x (h1.1 h)
    · intro h
      rw [← hmap] at h
      obtain ⟨x', hx', hxx⟩ := h
      have : x' = x := α.injective hxx
      rw [this] at hx'
      exact h1.2 hx'
  have hSS : S' = S := sylow_eq_of_center_eq hq hB (by
    rw [map_center_eq_sylowCenter, map_center_eq_sylowCenter]
    exact hcen.symm)
  have h2 : (S : Subgroup D).map α.toMonoidHom = (S : Subgroup D) := by
    rw [← hS']
    exact congrArg (fun T : Sylow 2 D => (T : Subgroup D)) hSS
  intro s hs
  rw [← h2]
  exact ⟨s, hs, rfl⟩

theorem fix_sylowCenter {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) (α : MulAut D) (hαα : α * α = 1) {S : Sylow 2 D}
    (hαT : ∀ x ∈ sylowCenter (S : Subgroup D), α x ∈ sylowCenter (S : Subgroup D)) :
    ∀ x ∈ sylowCenter (S : Subgroup D), α x = x := by
  have hαS := map_sylow_of_center hf hD α hαT
  obtain ⟨e⟩ := exists_psu3_of_statedClassicalModel hf hD
  intro x hx
  obtain ⟨hxS, hxc⟩ := mem_sylowCenter.1 hx
  exact CFSG.Timmesfeld.Bridge.Asc72.YU3.fix_center_of_mulEquiv_psu3 hf e S α hαα hαS hxS
    (fun y hy => (hxc y hy).symm)

theorem fix_root_group {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) (α : MulAut D) (hαα : α * α = 1) {S : Sylow 2 D}
    (hαT : ∀ x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype,
      α x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype) :
    ∀ x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype, α x = x := by
  rw [map_center_eq_sylowCenter] at hαT ⊢
  exact fix_sylowCenter hf hD α hαα hαT

end CFSG.CGT.T75A
