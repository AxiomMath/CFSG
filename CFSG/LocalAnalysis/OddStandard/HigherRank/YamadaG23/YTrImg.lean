module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YJS
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocB

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma jSub_eq_map_jOn (s : Setting3 G L) {X : Subgroup G} (hX : X ≤ s.fr.S) :
    jSub L X = (X.subgroupOf s.fr.S).map (jOn L (s3_S_le_N s)) := by
  ext α
  rw [mem_jSub L, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hxX, hxα⟩
    exact ⟨⟨x, hX hxX⟩, by rwa [Subgroup.mem_subgroupOf],
      actsAs_unique L (jOn_actsAs L (s3_S_le_N s) ⟨x, hX hxX⟩) hxα⟩
  · rintro ⟨t, ht, htα⟩
    rw [Subgroup.mem_subgroupOf] at ht
    exact ⟨t, ht, htα ▸ jOn_actsAs L (s3_S_le_N s) t⟩

private lemma jSub_closure_of_actsAs' (S : Set G) (hS : ∀ x ∈ S, x ∈ normalizer (L : Set G))
    (f : G → MulAut (L ⧸ center L)) (hf : ∀ x ∈ S, ActsAs L x (f x)) :
    jSub L (closure S) = closure (f '' S) := by
  refine le_antisymm ?_ ?_
  · intro α hα
    rw [mem_jSub L] at hα
    obtain ⟨g, hgS, hgα⟩ := hα
    have key : ∀ g ∈ closure S, ∃ β ∈ closure (f '' S), ActsAs L g β := by
      intro g hg
      refine Subgroup.closure_induction
        (p := fun g _ => ∃ β ∈ closure (f '' S), ActsAs L g β) ?_ ?_ ?_ ?_ hg
      · intro x hx
        exact ⟨f x, Subgroup.subset_closure ⟨x, hx, rfl⟩, hf x hx⟩
      · exact ⟨1, one_mem _, actsAs_one L⟩
      · intro x y _ _ ihx ihy
        obtain ⟨β, hβ, hβacts⟩ := ihx
        obtain ⟨γ, hγ, hγacts⟩ := ihy
        exact ⟨β * γ, mul_mem hβ hγ, actsAs_mul L hβacts hγacts⟩
      · intro x _ ihx
        obtain ⟨β, hβ, hβacts⟩ := ihx
        exact ⟨β⁻¹, inv_mem hβ, actsAs_inv L hβacts⟩
    obtain ⟨β, hβ, hβacts⟩ := key g hgS
    rwa [actsAs_unique L hgα hβacts]
  · rw [Subgroup.closure_le]
    rintro β ⟨x, hxS, rfl⟩
    exact (mem_jSub L).mpr ⟨x, Subgroup.subset_closure hxS, hf x hxS⟩

private lemma jSub_sup' {V W : Subgroup G} (hV : V ≤ normalizer (L : Set G))
    (hW : W ≤ normalizer (L : Set G)) : jSub L (V ⊔ W) = jSub L V ⊔ jSub L W := by
  rw [jSub, jSub, jSub, Subgroup.subgroupOf_sup hV hW, Subgroup.map_sup]

private lemma image_pair_eq_of_values {α β : Type} (f : α → β) {x y : α} {x' y' : β}
    (hx : f x = x') (hy : f y = y') :
    f '' ({x, y} : Set α) = ({x', y'} : Set β) := by
  rw [Set.image_pair f x y, hx, hy]

private lemma image_triple_eq_of_values {α β : Type} (f : α → β) {x y z : α} {x' y' z' : β}
    (hx : f x = x') (hy : f y = y') (hz : f z = z') :
    f '' ({x, y, z} : Set α) = ({x', y', z'} : Set β) := by
  simp only [Set.image_insert_eq, Set.image_singleton, hx, hy, hz]

private lemma comm_iff_of_actsAs (s : Setting3 G L) (hS : HRSetting G L)
    (hZ : Odd (Nat.card ↥(center ↥L))) {x y : G} (hx : x ∈ s.fr.S) (hy : y ∈ s.fr.S)
    {α β : MulAut (L ⧸ center L)} (hxα : ActsAs L x α) (hyβ : ActsAs L y β) :
    x * y = y * x ↔ α * β = β * α := by
  have h₁ : ActsAs L (x * y) (α * β) := actsAs_mul L hxα hyβ
  have h₂ : ActsAs L (y * x) (β * α) := actsAs_mul L hyβ hxα
  constructor
  · intro h
    rw [h] at h₁
    exact actsAs_unique L h₁ h₂
  · intro h
    rw [h] at h₁
    exact s3_inj_on_S s hS hZ (mul_mem hx hy) (mul_mem hy hx) h₁ h₂

private lemma mem_jSub_iff_of_le_S (s : Setting3 G L) (hS : HRSetting G L)
    (hZ : Odd (Nat.card ↥(center ↥L))) {X : Subgroup G} (hX : X ≤ s.fr.S) {x : G}
    (hx : x ∈ s.fr.S) {α : MulAut (L ⧸ center L)} (hxα : ActsAs L x α) :
    α ∈ jSub L X ↔ x ∈ X := by
  constructor
  · intro hα
    rw [mem_jSub L] at hα
    obtain ⟨y, hyX, hyα⟩ := hα
    rwa [s3_inj_on_S s hS hZ hx (hX hyX) hxα hyα]
  · intro hxX
    exact (mem_jSub L).mpr ⟨x, hxX, hxα⟩

private lemma mem_centralizer_pair_iff (s : Setting3 G L) (hS : HRSetting G L)
    (hZ : Odd (Nat.card ↥(center ↥L))) {x : G} (hx : x ∈ s.fr.S)
    {α : MulAut (L ⧸ center L)} (hxα : ActsAs L x α) :
    x ∈ centralizer (closure ({s.fr.b₁ * s.fr.b₂} : Set G)) ↔
      α ∈ centralizer (closure ({s.fr'.b₁ * s.fr'.b₂} :
        Set (MulAut (L ⧸ center L)))) := by
  obtain ⟨-, hb₁, -, hb₂, -, -⟩ := s3_actsAs_gens s
  have hc : ActsAs L (s.fr.b₁ * s.fr.b₂) (s.fr'.b₁ * s.fr'.b₂) := actsAs_mul L hb₁ hb₂
  have hcS : s.fr.b₁ * s.fr.b₂ ∈ s.fr.S := mul_mem (s3_b₁_mem_S s) (s3_b₂_mem_S s)
  have hxc : x ∈ centralizer (closure ({s.fr.b₁ * s.fr.b₂} : Set G)) ↔
      (s.fr.b₁ * s.fr.b₂) * x = x * (s.fr.b₁ * s.fr.b₂) := by
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    simp
  have hαc : α ∈ centralizer (closure ({s.fr'.b₁ * s.fr'.b₂} :
      Set (MulAut (L ⧸ center L)))) ↔
      (s.fr'.b₁ * s.fr'.b₂) * α = α * (s.fr'.b₁ * s.fr'.b₂) := by
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    simp
  rw [hxc, hαc]
  exact ⟨fun h => ((comm_iff_of_actsAs s hS hZ hx hcS hxα hc).mp h.symm).symm,
    fun h => ((comm_iff_of_actsAs s hS hZ hx hcS hxα hc).mpr h.symm).symm⟩

theorem s3_jSub_B (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) (s : Setting3 G L) :
    jSub L s.fr.B = s.fr'.B := by
  apply le_antisymm
  · intro α hα
    rw [mem_jSub L] at hα
    obtain ⟨x, hxB, hxα⟩ := hα
    have hxS : x ∈ s.fr.S := s3_B_le_S s hxB
    have hxBc : x ∈ centralizer (closure ({s.fr.b₁ * s.fr.b₂} : Set G)) := by
      have h := hxB
      rw [SFrame.B, centIn, Subgroup.mem_inf] at h
      exact h.2
    rw [SFrame.B, centIn, Subgroup.mem_inf]
    exact ⟨by
        rw [← s3_jSub_S s]
        exact (mem_jSub L).mpr ⟨x, hxS, hxα⟩,
      (mem_centralizer_pair_iff s hS hZ hxS hxα).mp hxBc⟩
  · intro α hα
    rw [SFrame.B, centIn, Subgroup.mem_inf] at hα
    obtain ⟨hαS, hαc⟩ := hα
    rw [← s3_jSub_S s, mem_jSub L] at hαS
    obtain ⟨x, hxS, hxα⟩ := hαS
    rw [mem_jSub L]
    refine ⟨x, ?_, hxα⟩
    have hxBc : x ∈ centralizer (closure ({s.fr.b₁ * s.fr.b₂} : Set G)) :=
      (mem_centralizer_pair_iff s hS hZ hxS hxα).mpr hαc
    rw [SFrame.B, centIn, Subgroup.mem_inf]
    exact ⟨hxS, hxBc⟩

private lemma mem_cen_iff (s : Setting3 G L) (hS : HRSetting G L)
    (hZ : Odd (Nat.card ↥(center ↥L))) {x : G} (hx : x ∈ s.fr.S)
    {α : MulAut (L ⧸ center L)} (hxα : ActsAs L x α) :
    x ∈ cen s.fr.B ↔ α ∈ cen s.fr'.B := by
  have hB : α ∈ s.fr'.B ↔ x ∈ s.fr.B := by
    rw [← s3_jSub_B hS hZ s]
    exact mem_jSub_iff_of_le_S s hS hZ (s3_B_le_S s) hx hxα
  rw [cen, cen, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨hxB, hxC⟩
    rw [Subgroup.mem_centralizer_iff] at hxC
    refine ⟨hB.mpr hxB, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro β hβ
    rw [← s3_jSub_B hS hZ s] at hβ
    change β ∈ jSub L s.fr.B at hβ
    rw [mem_jSub L] at hβ
    obtain ⟨y, hyB, hyβ⟩ := hβ
    have hyS : y ∈ s.fr.S := s3_B_le_S s hyB
    exact (comm_iff_of_actsAs s hS hZ hyS hx hyβ hxα).mp (hxC y hyB)
  · rintro ⟨hαB, hαC⟩
    rw [Subgroup.mem_centralizer_iff] at hαC
    refine ⟨hB.mp hαB, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hyB
    have hyS : y ∈ s.fr.S := s3_B_le_S s hyB
    let β : MulAut (L ⧸ center L) := jOn L (s3_S_le_N s) ⟨y, hyS⟩
    have hyβ : ActsAs L y β := jOn_actsAs L (s3_S_le_N s) ⟨y, hyS⟩
    have hβB : β ∈ s.fr'.B := by
      rw [← s3_jSub_B hS hZ s]
      exact (mem_jSub L).mpr ⟨y, hyB, hyβ⟩
    exact (comm_iff_of_actsAs s hS hZ hyS hx hyβ hxα).mpr (hαC β hβB)

theorem s3_jSub_cenB (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : jSub L (cen s.fr.B) = cen s.fr'.B := by
  apply le_antisymm
  · intro α hα
    rw [mem_jSub L] at hα
    obtain ⟨x, hxB, hxα⟩ := hα
    have hxS : x ∈ s.fr.S := (s3_cenB_le_B s).trans (s3_B_le_S s) hxB
    exact (mem_cen_iff s hS hZ hxS hxα).mp hxB
  · intro α hα
    have hαB : α ∈ s.fr'.B := (Subgroup.mem_inf.mp hα).1
    rw [← s3_jSub_B hS hZ s, mem_jSub L] at hαB
    obtain ⟨x, hxB, hxα⟩ := hαB
    have hxS : x ∈ s.fr.S := s3_B_le_S s hxB
    exact (mem_jSub L).mpr ⟨x, (mem_cen_iff s hS hZ hxS hxα).mpr hα, hxα⟩

theorem s3_jSub_J0B (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : jSub L (thompsonSubgroup s.fr.B) = thompsonSubgroup s.fr'.B := by
  let B₀ : Subgroup ↥s.fr.S := (s.fr.B).subgroupOf s.fr.S
  have hBS : s.fr.B ≤ s.fr.S := s3_B_le_S s
  have hJ0S : thompsonSubgroup s.fr.B ≤ s.fr.S := (s3_J0B_le_B s).trans hBS
  have hφinj : Function.Injective (jOn L (s3_S_le_N s)) := s3_jOn_S_injective s hS hZ
  have hJmap : thompsonSubgroup s.fr.B = (thompsonSubgroup B₀).map s.fr.S.subtype := by
    have h := thompsonSubgroup_map (f := s.fr.S.subtype) s.fr.S.subtype_injective B₀
    rwa [Subgroup.map_subgroupOf_eq_of_le hBS] at h
  have hsub : (thompsonSubgroup s.fr.B).subgroupOf s.fr.S = thompsonSubgroup B₀ := by
    rw [hJmap, ← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective s.fr.S.subtype_injective _
  calc jSub L (thompsonSubgroup s.fr.B)
      = ((thompsonSubgroup s.fr.B).subgroupOf s.fr.S).map (jOn L (s3_S_le_N s)) :=
        jSub_eq_map_jOn s hJ0S
    _ = (thompsonSubgroup B₀).map (jOn L (s3_S_le_N s)) := by rw [hsub]
    _ = thompsonSubgroup (B₀.map (jOn L (s3_S_le_N s))) :=
        (thompsonSubgroup_map (f := jOn L (s3_S_le_N s)) hφinj B₀).symm
    _ = thompsonSubgroup s.fr'.B := by
        rw [show B₀.map (jOn L (s3_S_le_N s)) = jSub L s.fr.B from
          (jSub_eq_map_jOn s hBS).symm, s3_jSub_B hS hZ s]

theorem s3_jSub_E (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) (s : Setting3 G L) :
    jSub L s.fr.E = s.fr'.E := by
  obtain ⟨ha₁, hb₁, ha₂, hb₂, -, hz⟩ := s3_actsAs_gens s
  have hT : ({s.fr.b₁ * s.fr.b₂, s.fr.a₁ * s.fr.b₁ * s.fr.a₂, s.fr.z} : Set G) ⊆ s.fr.S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact mul_mem (s3_b₁_mem_S s) (s3_b₂_mem_S s)
    · exact mul_mem (mul_mem (s3_a₁_mem_S s) (s3_b₁_mem_S s)) (s3_a₂_mem_S s)
    · exact s3_z_mem_S s
  let f : G → MulAut (L ⧸ center L) :=
    Function.extend (Subtype.val : ↥s.fr.S → G) (jOn L (s3_S_le_N s)) (fun _ => 1)
  have hfval : ∀ x (hx : x ∈ ({s.fr.b₁ * s.fr.b₂, s.fr.a₁ * s.fr.b₁ * s.fr.a₂,
      s.fr.z} : Set G)), f x = jOn L (s3_S_le_N s) ⟨x, hT hx⟩ := by
    intro x hx
    exact Subtype.val_injective.extend_apply (jOn L (s3_S_le_N s)) (fun _ => 1) ⟨x, hT hx⟩
  have hf : ∀ x ∈ ({s.fr.b₁ * s.fr.b₂, s.fr.a₁ * s.fr.b₁ * s.fr.a₂, s.fr.z} : Set G),
      ActsAs L x (f x) := by
    intro x hx
    rw [hfval x hx]
    exact jOn_actsAs L (s3_S_le_N s) ⟨x, hT hx⟩
  have h1 : f (s.fr.b₁ * s.fr.b₂) = s.fr'.b₁ * s.fr'.b₂ := by
    rw [hfval _ (by simp)]
    exact actsAs_unique L (jOn_actsAs L (s3_S_le_N s) _) (actsAs_mul L hb₁ hb₂)
  have h2 : f (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) = s.fr'.a₁ * s.fr'.b₁ * s.fr'.a₂ := by
    rw [hfval _ (by simp)]
    exact actsAs_unique L (jOn_actsAs L (s3_S_le_N s) _)
      (actsAs_mul L (actsAs_mul L ha₁ hb₁) ha₂)
  have h3 : f s.fr.z = s.fr'.z := by
    rw [hfval _ (by simp)]
    exact actsAs_unique L (jOn_actsAs L (s3_S_le_N s) _) hz
  have hstep : jSub L s.fr.E =
      closure (f '' ({s.fr.b₁ * s.fr.b₂, s.fr.a₁ * s.fr.b₁ * s.fr.a₂, s.fr.z} : Set G)) := by
    rw [SFrame.E]
    exact jSub_closure_of_actsAs' _ (fun x hx => s3_S_le_N s (hT hx)) f hf
  rw [hstep, image_triple_eq_of_values f h1 h2 h3, SFrame.E]

theorem s3_jSub_F (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) (s : Setting3 G L) :
    jSub L s.fr.F = s.fr'.F := by
  obtain ⟨ha₁, hb₁, ha₂, hb₂, -, hz⟩ := s3_actsAs_gens s
  have hT : ({s.fr.a₁ * s.fr.a₂, s.fr.b₁ * s.fr.b₂, s.fr.z} : Set G) ⊆ s.fr.S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact mul_mem (s3_a₁_mem_S s) (s3_a₂_mem_S s)
    · exact mul_mem (s3_b₁_mem_S s) (s3_b₂_mem_S s)
    · exact s3_z_mem_S s
  let f : G → MulAut (L ⧸ center L) :=
    Function.extend (Subtype.val : ↥s.fr.S → G) (jOn L (s3_S_le_N s)) (fun _ => 1)
  have hfval : ∀ x (hx : x ∈ ({s.fr.a₁ * s.fr.a₂, s.fr.b₁ * s.fr.b₂,
      s.fr.z} : Set G)), f x = jOn L (s3_S_le_N s) ⟨x, hT hx⟩ := by
    intro x hx
    exact Subtype.val_injective.extend_apply (jOn L (s3_S_le_N s)) (fun _ => 1) ⟨x, hT hx⟩
  have hf : ∀ x ∈ ({s.fr.a₁ * s.fr.a₂, s.fr.b₁ * s.fr.b₂, s.fr.z} : Set G),
      ActsAs L x (f x) := by
    intro x hx
    rw [hfval x hx]
    exact jOn_actsAs L (s3_S_le_N s) ⟨x, hT hx⟩
  have h1 : f (s.fr.a₁ * s.fr.a₂) = s.fr'.a₁ * s.fr'.a₂ := by
    rw [hfval _ (by simp)]
    exact actsAs_unique L (jOn_actsAs L (s3_S_le_N s) _) (actsAs_mul L ha₁ ha₂)
  have h2 : f (s.fr.b₁ * s.fr.b₂) = s.fr'.b₁ * s.fr'.b₂ := by
    rw [hfval _ (by simp)]
    exact actsAs_unique L (jOn_actsAs L (s3_S_le_N s) _) (actsAs_mul L hb₁ hb₂)
  have h3 : f s.fr.z = s.fr'.z := by
    rw [hfval _ (by simp)]
    exact actsAs_unique L (jOn_actsAs L (s3_S_le_N s) _) hz
  have hstep : jSub L s.fr.F =
      closure (f '' ({s.fr.a₁ * s.fr.a₂, s.fr.b₁ * s.fr.b₂, s.fr.z} : Set G)) := by
    rw [SFrame.F]
    exact jSub_closure_of_actsAs' _ (fun x hx => s3_S_le_N s (hT hx)) f hf
  rw [hstep, image_triple_eq_of_values f h1 h2 h3, SFrame.F]

theorem s3_jSub_EF (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : jSub L (s.fr.E ⊔ s.fr.F) = s.fr'.E ⊔ s.fr'.F := by
  have hE : s.fr.E ≤ normalizer (L : Set G) := (s3_E_le_A s).trans (s3_A_le_N s)
  have hF : s.fr.F ≤ normalizer (L : Set G) := (s3_F_le_A s).trans (s3_A_le_N s)
  rw [jSub_sup' hE hF, s3_jSub_E hS hZ s, s3_jSub_F hS hZ s]

theorem s3_jSub_K1 (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) (s : Setting3 G L) :
    jSub L (closure {s.fr.a₁, s.fr.b₁}) = closure {s.fr'.a₁, s.fr'.b₁} := by
  obtain ⟨ha₁, hb₁, -, -, -, -⟩ := s3_actsAs_gens s
  have hT : ({s.fr.a₁, s.fr.b₁} : Set G) ⊆ s.fr.S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact s3_a₁_mem_S s
    · exact s3_b₁_mem_S s
  let f : G → MulAut (L ⧸ center L) :=
    Function.extend (Subtype.val : ↥s.fr.S → G) (jOn L (s3_S_le_N s)) (fun _ => 1)
  have hfval : ∀ x (hx : x ∈ ({s.fr.a₁, s.fr.b₁} : Set G)),
      f x = jOn L (s3_S_le_N s) ⟨x, hT hx⟩ := by
    intro x hx
    exact Subtype.val_injective.extend_apply (jOn L (s3_S_le_N s)) (fun _ => 1) ⟨x, hT hx⟩
  have hf : ∀ x ∈ ({s.fr.a₁, s.fr.b₁} : Set G), ActsAs L x (f x) := by
    intro x hx
    rw [hfval x hx]
    exact jOn_actsAs L (s3_S_le_N s) ⟨x, hT hx⟩
  have h1 : f s.fr.a₁ = s.fr'.a₁ := by
    rw [hfval _ (by simp)]
    exact actsAs_unique L (jOn_actsAs L (s3_S_le_N s) _) ha₁
  have h2 : f s.fr.b₁ = s.fr'.b₁ := by
    rw [hfval _ (by simp)]
    exact actsAs_unique L (jOn_actsAs L (s3_S_le_N s) _) hb₁
  have hstep : jSub L (closure ({s.fr.a₁, s.fr.b₁} : Set G)) =
      closure (f '' ({s.fr.a₁, s.fr.b₁} : Set G)) :=
    jSub_closure_of_actsAs' _ (fun x hx => s3_S_le_N s (hT hx)) f hf
  rw [hstep, image_pair_eq_of_values f h1 h2]

theorem s3_jSub_K2 (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) (s : Setting3 G L) :
    jSub L (closure {s.fr.a₂, s.fr.b₂}) = closure {s.fr'.a₂, s.fr'.b₂} := by
  obtain ⟨-, -, ha₂, hb₂, -, -⟩ := s3_actsAs_gens s
  have hT : ({s.fr.a₂, s.fr.b₂} : Set G) ⊆ s.fr.S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact s3_a₂_mem_S s
    · exact s3_b₂_mem_S s
  let f : G → MulAut (L ⧸ center L) :=
    Function.extend (Subtype.val : ↥s.fr.S → G) (jOn L (s3_S_le_N s)) (fun _ => 1)
  have hfval : ∀ x (hx : x ∈ ({s.fr.a₂, s.fr.b₂} : Set G)),
      f x = jOn L (s3_S_le_N s) ⟨x, hT hx⟩ := by
    intro x hx
    exact Subtype.val_injective.extend_apply (jOn L (s3_S_le_N s)) (fun _ => 1) ⟨x, hT hx⟩
  have hf : ∀ x ∈ ({s.fr.a₂, s.fr.b₂} : Set G), ActsAs L x (f x) := by
    intro x hx
    rw [hfval x hx]
    exact jOn_actsAs L (s3_S_le_N s) ⟨x, hT hx⟩
  have h1 : f s.fr.a₂ = s.fr'.a₂ := by
    rw [hfval _ (by simp)]
    exact actsAs_unique L (jOn_actsAs L (s3_S_le_N s) _) ha₂
  have h2 : f s.fr.b₂ = s.fr'.b₂ := by
    rw [hfval _ (by simp)]
    exact actsAs_unique L (jOn_actsAs L (s3_S_le_N s) _) hb₂
  have hstep : jSub L (closure ({s.fr.a₂, s.fr.b₂} : Set G)) =
      closure (f '' ({s.fr.a₂, s.fr.b₂} : Set G)) :=
    jSub_closure_of_actsAs' _ (fun x hx => s3_S_le_N s (hT hx)) f hf
  rw [hstep, image_pair_eq_of_values f h1 h2]

theorem s3_actsAs_a₁b₁b₂ (s : Setting3 G L) :
    ActsAs L (s.fr.a₁ * s.fr.b₁ * s.fr.b₂) (s.fr'.a₁ * s.fr'.b₁ * s.fr'.b₂) := by
  obtain ⟨ha₁, hb₁, -, hb₂, -, -⟩ := s3_actsAs_gens s
  exact actsAs_mul L (actsAs_mul L ha₁ hb₁) hb₂

end CFSG.OddStandard.HigherRank.YamadaG23
