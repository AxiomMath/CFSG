module

public import CFSG.ClassicalInvolution.Phan.PhanG4Chain
public import CFSG.ClassicalInvolution.Phan.PhanD9Tits
public import CFSG.ClassicalInvolution.Phan.PhanG1Cover
public import CFSG.ClassicalInvolution.Phan.PhanG2Frames

public section

namespace CFSG.ClassicalInvolution.PhanG

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] {S : PhanFamilyD4 K p f G} {e : Fin 3 → Fin 4} {ψ : Su K p f 4 →* G}

theorem exists_mul_of_mem_parab (hK : Nat.card K = (p ^ f) ^ 2) (j : Fin 4) {x : G}
    (hx : x ∈ parab S {j}) : ∃ r ∈ (S.ι j).range, ∃ t ∈ torusSub S, x = r * t := by
  have hN := Subgroup.coe_mul_of_right_le_normalizer_left (S.ι j).range (torusSub S)
    (torusSub_le_normalizer_range hK j)
  have hx' : x ∈ (((S.ι j).range ⊔ torusSub S : Subgroup G) : Set G) := by
    rw [parab, sup_comm, Lsup_singleton] at hx
    exact hx
  rw [hN] at hx'
  obtain ⟨r, hr, t, ht, rfl⟩ := hx'
  exact ⟨r, hr, t, ht, rfl⟩

theorem PhanChain.twoHomotopic_nil (hK : Nat.card K = (p ^ f) ^ 2) (hq : 4 ≤ p ^ f)
    (hg : GoodFamily S) (h2 : (2 : K) ≠ 0) (hch : PhanChain S e ψ) (x : G ⧸ torusSub S)
    (γ : List (Fin 4 × G ⧸ torusSub S)) (hγ : (phanSystem S).IsGallery x γ)
    (hJ : ∀ j ∈ galleryType γ, j ∈ Set.range e) (hend : galleryEnd x γ = x) :
    (phanSystem S).TwoHomotopic x γ [] := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hm := phanSystem_isMorphism_smul (S := S) g⁻¹
  have hmg := phanSystem_isMorphism_smul (S := S) g
  have hbase : (g⁻¹ • (g : G ⧸ torusSub S)) = ((ψ 1 : G) : G ⧸ torusSub S) := by
    rw [smul_mk, inv_mul_cancel, map_one]
  have h1 : (phanSystem S).IsGallery ((ψ 1 : G) : G ⧸ torusSub S)
      (galleryMap (g⁻¹ • ·) γ) := by
    rw [← hbase]
    exact hm.isGallery hγ
  have hJ' : ∀ j ∈ galleryType (galleryMap (g⁻¹ • ·) γ), j ∈ Set.range e := by
    intro j hj
    apply hJ
    simpa [galleryType, galleryMap] using hj
  have hend' : galleryEnd ((ψ 1 : G) : G ⧸ torusSub S) (galleryMap (g⁻¹ • ·) γ) =
      ((ψ 1 : G) : G ⧸ torusSub S) := by
    rw [← hbase, galleryEnd_galleryMap, hend]
  have hT : (torus (unitaryInvolution K p f) 4).map ψ ≤ torusSub S := by
    rintro _ ⟨t, ht, rfl⟩
    exact hch.psi_mem_torusSub hg ht
  have h1' : ∀ i : Fin 3, ((torus (unitaryInvolution K p f) 4 ⊔
      (blockEmb2 K p f 3 i).range).map ψ) ≤ parab S {e i} := by
    rintro i _ ⟨q, hq', rfl⟩
    have hnorm : torus (unitaryInvolution K p f) 4 ≤
        Subgroup.normalizer ((blockEmb2 K p f 3 i).range : Set (Su K p f 4)) :=
      torus_le_normalizer_range_blockEmb hK (by omega)
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (torus (unitaryInvolution K p f) 4)
      (blockEmb2 K p f 3 i).range hnorm
    have hq'' : q ∈ ((torus (unitaryInvolution K p f) 4 ⊔ (blockEmb2 K p f 3 i).range :
        Subgroup (Su K p f 4)) : Set (Su K p f 4)) := hq'
    rw [hmul] at hq''
    obtain ⟨a, ha, b, ⟨A, rfl⟩, rfl⟩ := hq''
    rw [map_mul]
    refine mul_mem (torusSub_le_parab _ (hch.psi_mem_torusSub hg ha)) ?_
    have := hch.le_range i A
    rw [← Lsup_singleton] at this
    exact Lsup_le_parab _ this
  have h2' : ∀ i : Fin 3, ∀ x ∈ parab S {e i}, ∃ q ∈ torus (unitaryInvolution K p f) 4 ⊔
      (blockEmb2 K p f 3 i).range, ∃ t ∈ torusSub S, x = ψ q * t := by
    intro i x hx
    obtain ⟨r, hr, t, ht, rfl⟩ := exists_mul_of_mem_parab hK (e i) hx
    obtain ⟨A, hA⟩ := hch.range_le i r hr
    exact ⟨blockEmb2 K p f 3 i A, Subgroup.mem_sup_right ⟨A, rfl⟩, t, ht, by rw [hA]⟩
  have h3' : ∀ h : Su K p f 4, ψ h ∈ torusSub S → h ∈ torus (unitaryInvolution K p f) 4 :=
    fun h hh => hch.mem_torus_of_psi_mem hK hg h2 hh
  have hnull := twoHomotopic_nil_of_coset_cover (ψ := ψ) (TG := torusSub S)
    (QG := fun j => parab S {j}) (hQG := fun j => torusSub_le_parab {j})
    (TH := torus (unitaryInvolution K p f) 4)
    (QH := fun i : Fin 3 => torus (unitaryInvolution K p f) 4 ⊔ (blockEmb2 K p f 3 i).range)
    (hQH := fun _ => le_sup_left) (e := e) hT h1' h2' h3'
    (frameCoset_simplyTwoConnected hK hq 3) 1 (galleryMap (g⁻¹ • ·) γ) h1 hJ' hend'
  have hback := hnull.map hmg
  rw [← hbase, smul_inv_smul, galleryMap_galleryMap] at hback
  have hid : ((g • ·) ∘ (g⁻¹ • ·) : G ⧸ torusSub S → G ⧸ torusSub S) = id := by
    funext y
    simp
  rw [hid, galleryMap_id] at hback
  simpa using hback

end CFSG.ClassicalInvolution.PhanG
