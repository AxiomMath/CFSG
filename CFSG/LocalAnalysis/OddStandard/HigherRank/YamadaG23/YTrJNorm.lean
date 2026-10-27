module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJKer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem isPGroup_zpowers_mul_conj {X : Subgroup G} (hX : IsPGroup 2 ↥X) {y : G}
    (hy : y ∈ X) (x : G) : IsPGroup 2 ↥(zpowers (x * y * x⁻¹)) := by
  have hle : zpowers y ≤ X := zpowers_le.mpr hy
  have hy2 : IsPGroup 2 ↥(zpowers y) :=
    hX.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  let f : G →* G := (MulAut.conj x).toMonoidHom
  have hfy : f y = x * y * x⁻¹ := by
    show (MulAut.conj x) y = x * y * x⁻¹
    rw [MulAut.conj_apply]
  have hmap := hy2.map f
  have hz : (zpowers y).map f = zpowers (x * y * x⁻¹) := by
    rw [MonoidHom.map_zpowers, hfy]
  rwa [hz] at hmap

private theorem eq_one_of_mem_zL_of_isPGroup_two (hZ : Odd (Nat.card ↥(center ↥L)))
    {X : Subgroup G} (hX : IsPGroup 2 ↥X) {c : G} (hc : c ∈ zL L) (hcX : c ∈ X) : c = 1 := by
  have hcard : Nat.card (zL L) = Nat.card ↥(center ↥L) := by
    simpa [zL] using
      Subgroup.card_map_of_injective (K := center ↥L) (f := L.subtype) L.subtype_injective
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hcop : (Nat.card (zL L)).Coprime (Nat.card X) := by
    rw [hcard, hn]
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp
    · exact (Nat.coprime_pow_right_iff hnpos _ _).mpr hZ.coprime_two_right
  have hdisj : Disjoint (zL L) X := Subgroup.disjoint_of_coprime_natCard hcop
  have hmem : c ∈ zL L ⊓ X := ⟨hc, hcX⟩
  rw [disjoint_iff.mp hdisj] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem mul_conj_mem_of_actsAs [Group.IsPerfect ↥L] (hZ : Odd (Nat.card ↥(center ↥L)))
    {X : Subgroup G} (hXL : X ≤ L) (hX : IsPGroup 2 ↥X) {x : G}
    {α : MulAut (L ⧸ center L)} (hxα : ActsAs L x α)
    (hαN : α ∈ normalizer (jSub L X : Set (MulAut (L ⧸ center L)))) :
    ∀ y ∈ X, x * y * x⁻¹ ∈ X := by
  intro y hy
  let β : MulAut (L ⧸ center L) := MulAut.conj (QuotientGroup.mk (⟨y, hXL hy⟩ : ↥L))
  have hyβ : ActsAs L y β := actsAs_of_mem L (hXL hy)
  have hβmem : β ∈ jSub L X := (mem_jSub L).mpr ⟨y, hy, hyβ⟩
  have hγα : α * β * α⁻¹ ∈ jSub L X := (Subgroup.mem_normalizer_iff.mp hαN β).mp hβmem
  have hzα : ActsAs L (x * y * x⁻¹) (α * β * α⁻¹) := by
    have h := actsAs_mul L (actsAs_mul L hxα hyβ) (actsAs_inv L hxα)
    simpa using h
  have hzL : x * y * x⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_actsAs L hxα) y).mp (hXL hy)
  have hz2 : IsPGroup 2 ↥(zpowers (x * y * x⁻¹)) := isPGroup_zpowers_mul_conj hX hy x
  exact (mem_jSub_iff_mem (L := L) hZ hXL hX hzL hz2 hzα).mp hγα

theorem zL_le_normIn {X : Subgroup G} (hX : X ≤ L) : zL L ≤ normIn L X := by
  intro c hc
  rw [normIn, Subgroup.mem_inf]
  refine ⟨zL_le hc, ?_⟩
  exact Subgroup.centralizer_le_normalizer (X : Set G) (by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (mem_zL_iff.mp hc).2) y (hX hy))

theorem zL_le_centIn {X : Subgroup G} (hX : X ≤ L) : zL L ≤ centIn L X := by
  intro c hc
  rw [centIn, Subgroup.mem_inf]
  refine ⟨zL_le hc, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (mem_zL_iff.mp hc).2) y (hX hy)

theorem zL_le_centEl {y : G} (hy : y ∈ L) : zL L ≤ centEl L y := by
  intro c hc
  rw [centEl, Subgroup.mem_inf]
  refine ⟨zL_le hc, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact (Subgroup.mem_centralizer_iff.mp (mem_zL_iff.mp hc).2) y hy

theorem mem_normalizer_iff_jSub [Group.IsPerfect ↥L] (hZ : Odd (Nat.card ↥(center ↥L)))
    {X : Subgroup G} (hXL : X ≤ L) (hX : IsPGroup 2 ↥X) {x : G} {α : MulAut (L ⧸ center L)}
    (hxα : ActsAs L x α) :
    x ∈ normalizer (X : Set G) ↔ α ∈ normalizer (jSub L X : Set (MulAut (L ⧸ center L))) := by
  constructor
  · intro hxXN
    rw [Subgroup.mem_normalizer_iff]
    intro β
    constructor
    · intro hβ
      rw [mem_jSub] at hβ
      obtain ⟨y, hy, hyβ⟩ := hβ
      refine (mem_jSub L).mpr ⟨x * y * x⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hxXN y).mp hy
      · have h := actsAs_mul L (actsAs_mul L hxα hyβ) (actsAs_inv L hxα)
        simpa using h
    · intro hβ
      have hxinvN : x⁻¹ ∈ normalizer (X : Set G) := (normalizer (X : Set G)).inv_mem hxXN
      rw [mem_jSub] at hβ
      obtain ⟨z, hz, hzβ⟩ := hβ
      refine (mem_jSub L).mpr ⟨x⁻¹ * z * x, ?_, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.mp hxinvN z).mp hz
      · have hact := actsAs_mul L (actsAs_mul L (actsAs_inv L hxα) hzβ) hxα
        have heq : α⁻¹ * (α * β * α⁻¹) * α = β := by group
        rwa [heq] at hact
  · intro hαN
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact mul_conj_mem_of_actsAs (L := L) hZ hXL hX hxα hαN y hy
    · intro hy
      have hαinvN : α⁻¹ ∈ normalizer (jSub L X : Set (MulAut (L ⧸ center L))) :=
        Subgroup.inv_mem _ hαN
      have h := mul_conj_mem_of_actsAs (L := L) hZ hXL hX (actsAs_inv L hxα) hαinvN
        (x * y * x⁻¹) hy
      have hy' : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
      rwa [hy'] at h

theorem mem_normIn_iff_jSub [Group.IsPerfect ↥L] (hZ : Odd (Nat.card ↥(center ↥L)))
    {X : Subgroup G} (hXL : X ≤ L) (hX : IsPGroup 2 ↥X) {x : G} (hx : x ∈ L)
    {α : MulAut (L ⧸ center L)} (hxα : ActsAs L x α) :
    x ∈ normIn L X ↔ α ∈ normalizer (jSub L X : Set (MulAut (L ⧸ center L))) := by
  rw [normIn, Subgroup.mem_inf]
  constructor
  · rintro ⟨_, hxN⟩
    exact (mem_normalizer_iff_jSub (L := L) hZ hXL hX hxα).mp hxN
  · intro h
    exact ⟨hx, (mem_normalizer_iff_jSub (L := L) hZ hXL hX hxα).mpr h⟩

theorem jSub_normIn [Group.IsPerfect ↥L] (hZ : Odd (Nat.card ↥(center ↥L)))
    {X : Subgroup G} (hXL : X ≤ L) (hX : IsPGroup 2 ↥X) :
    jSub L (normIn L X) = normIn (jSub L L) (jSub L X) := by
  apply le_antisymm
  · intro α hα
    rw [mem_jSub] at hα
    obtain ⟨x, hx, hxα⟩ := hα
    have hxL : x ∈ L := (Subgroup.mem_inf.mp hx).1
    rw [normIn, Subgroup.mem_inf]
    exact ⟨(mem_jSub L).mpr ⟨x, hxL, hxα⟩,
      (mem_normIn_iff_jSub (L := L) hZ hXL hX hxL hxα).mp hx⟩
  · intro α hα
    rw [normIn, Subgroup.mem_inf] at hα
    obtain ⟨hαL, hαN⟩ := hα
    rw [mem_jSub] at hαL ⊢
    obtain ⟨x, hxL, hxα⟩ := hαL
    exact ⟨x, (mem_normIn_iff_jSub (L := L) hZ hXL hX hxL hxα).mpr hαN, hxα⟩

theorem jSub_centIn [Group.IsPerfect ↥L] (hZ : Odd (Nat.card ↥(center ↥L)))
    {X : Subgroup G} (hXL : X ≤ L) (hX : IsPGroup 2 ↥X) :
    jSub L (centIn L X) = centIn (jSub L L) (jSub L X) := by
  apply le_antisymm
  · intro α hα
    rw [mem_jSub] at hα
    obtain ⟨x, hx, hxα⟩ := hα
    have hxL : x ∈ L := (Subgroup.mem_inf.mp hx).1
    rw [centIn, Subgroup.mem_inf]
    refine ⟨(mem_jSub L).mpr ⟨x, hxL, hxα⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro β hβ
    change β ∈ jSub L X at hβ
    rw [mem_jSub] at hβ
    obtain ⟨y, hy, hyβ⟩ := hβ
    have hcomm : y * x = x * y :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2) y hy
    have h1 : ActsAs L (x * y) (α * β) := actsAs_mul L hxα hyβ
    have h2 : ActsAs L (y * x) (β * α) := actsAs_mul L hyβ hxα
    have heq : α * β = β * α := actsAs_unique L (hcomm.symm ▸ h1) h2
    exact heq.symm
  · intro α hα
    rw [centIn, Subgroup.mem_inf] at hα
    obtain ⟨hαL, hαC⟩ := hα
    rw [mem_jSub] at hαL ⊢
    obtain ⟨x, hxL, hxα⟩ := hαL
    refine ⟨x, ?_, hxα⟩
    rw [centIn, Subgroup.mem_inf]
    refine ⟨hxL, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let β : MulAut (L ⧸ center L) := MulAut.conj (QuotientGroup.mk (⟨y, hXL hy⟩ : ↥L))
    have hyβ : ActsAs L y β := actsAs_of_mem L (hXL hy)
    have hβmem : β ∈ jSub L X := (mem_jSub L).mpr ⟨y, hy, hyβ⟩
    have hcommAB : β * α = α * β := (Subgroup.mem_centralizer_iff.mp hαC) β hβmem
    have hcActs : ActsAs L (x * y * x⁻¹ * y⁻¹) 1 := by
      have h := actsAs_mul L (actsAs_mul L (actsAs_mul L hxα hyβ) (actsAs_inv L hxα))
        (actsAs_inv L hyβ)
      have hone : (α * β * α⁻¹) * β⁻¹ = 1 := by
        rw [← hcommAB]
        group
      rwa [hone] at h
    have hcL : x * y * x⁻¹ * y⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem hxL (hXL hy)) (L.inv_mem hxL)) (L.inv_mem (hXL hy))
    have hczL : x * y * x⁻¹ * y⁻¹ ∈ zL L := (actsAs_one_iff_mem_zL hcL).mp hcActs
    have hcyEq : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
    have hcy2 : IsPGroup 2 ↥(zpowers ((x * y * x⁻¹ * y⁻¹) * y)) := by
      rw [← hcyEq]
      exact isPGroup_zpowers_mul_conj hX hy x
    have hcyL : (x * y * x⁻¹ * y⁻¹) * y ∈ L := by
      rw [← hcyEq]
      exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_actsAs L hxα) y).mp (hXL hy)
    have hcyβ : ActsAs L ((x * y * x⁻¹ * y⁻¹) * y) β := by
      have h := actsAs_mul L hcActs hyβ
      simpa using h
    have hcyX : (x * y * x⁻¹ * y⁻¹) * y ∈ X :=
      (mem_jSub_iff_mem (L := L) hZ hXL hX hcyL hcy2 hcyβ).mp hβmem
    have hcX : x * y * x⁻¹ * y⁻¹ ∈ X := by
      have heq : x * y * x⁻¹ * y⁻¹ = ((x * y * x⁻¹ * y⁻¹) * y) * y⁻¹ := by group
      rw [heq]
      exact X.mul_mem hcyX (X.inv_mem hy)
    have hc1 : x * y * x⁻¹ * y⁻¹ = 1 := eq_one_of_mem_zL_of_isPGroup_two hZ hX hczL hcX
    have hxy : x * y * x⁻¹ = y := by
      rw [hcyEq, hc1, one_mul]
    have hcomm : x * y = y * x := by
      have h := congrArg (fun z => z * x) hxy
      rw [mul_assoc (x * y) x⁻¹ x, inv_mul_cancel, mul_one] at h
      exact h
    exact hcomm.symm

theorem jSub_centEl [Group.IsPerfect ↥L] (hZ : Odd (Nat.card ↥(center ↥L)))
    {y : G} (hy : y ∈ L) (hy2 : IsPGroup 2 ↥(zpowers y)) {α : MulAut (L ⧸ center L)}
    (hα : ActsAs L y α) : jSub L (centEl L y) = centEl (jSub L L) α := by
  have hXL : (zpowers y : Subgroup G) ≤ L := zpowers_le.mpr hy
  have hjz : jSub L (zpowers y) = zpowers α := by
    rw [Subgroup.zpowers_eq_closure]
    have h := jSub_closure_of_actsAs (L := L) ({y} : Set G)
      (fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact mem_normalizer_of_actsAs L hα)
      (fun _ => α)
      (fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hα)
    rw [h, Set.image_singleton, Subgroup.zpowers_eq_closure]
  have hcy : centralizer ((zpowers y : Subgroup G) : Set G) = centralizer ({y} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hca : centralizer ((zpowers α : Subgroup (MulAut (L ⧸ center L))) :
      Set (MulAut (L ⧸ center L))) =
      centralizer ({α} : Set (MulAut (L ⧸ center L))) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcent : centEl L y = centIn L (zpowers y) := by
    rw [centEl, centIn, hcy]
  have hcent' : centIn (jSub L L) (zpowers α) = centEl (jSub L L) α := by
    rw [centEl, centIn, hca]
  rw [hcent, ← hcent']
  have h := jSub_centIn (L := L) hZ hXL hy2
  rwa [hjz] at h

end CFSG.OddStandard.HigherRank.YamadaG23
