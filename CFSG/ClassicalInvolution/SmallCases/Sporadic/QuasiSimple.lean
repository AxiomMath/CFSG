module

public import CFSG.Assembly.Defs
public import CFSG.Open.Defs
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

namespace CFSG.ClassicalInvolution

open CFSG.Sporadic.Schreier (conjClass)

variable {M : Type*} [Group M]

theorem normal_eq_top_of_cover {K : Subgroup M} {z : M} (reps : List M)
    (hcover : ∀ x ∈ K, x = 1 ∨ x = z ∨ ∃ r ∈ reps, ∃ c ∈ K, x = c * r * c⁻¹)
    (hgen : ∀ r ∈ reps, K ≤ Subgroup.closure (conjClass K r)) (N : Subgroup K) [N.Normal]
    {x : K} (hxN : x ∈ N) (hx1 : (x : M) ≠ 1) (hxz : (x : M) ≠ z) : N = ⊤ := by
  rcases hcover x x.2 with h | h | ⟨r, hr, c, hc, hxr⟩
  · exact absurd h hx1
  · exact absurd h hxz
  · set N' := N.map K.subtype
    have hN'n : ∀ c ∈ K, ∀ y ∈ N', c * y * c⁻¹ ∈ N' := by
      intro c hc y hy
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map.mpr
        ⟨⟨c, hc⟩ * y' * ⟨c, hc⟩⁻¹, Subgroup.Normal.conj_mem inferInstance _ hy' _, by simp⟩
    have hxN' : (x : M) ∈ N' := Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩
    have hrN' : r ∈ N' := by
      have := hN'n c⁻¹ (K.inv_mem hc) _ hxN'
      rwa [hxr, show c⁻¹ * (c * r * c⁻¹) * c⁻¹⁻¹ = r by group] at this
    have hcl : conjClass K r ⊆ N' := by
      rintro _ ⟨g, hg, rfl⟩
      exact hN'n g hg r hrN'
    have hKN : K ≤ N' := (hgen r hr).trans ((Subgroup.closure_le N').mpr hcl)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.mp (hKN y.2)
    rwa [show y' = y from Subtype.ext hyy'] at hy'

theorem isQuasisimple_of_cover {K : Subgroup M} {z : M} (hzK : z ∈ K)
    (hzc : ∀ k ∈ K, k * z = z * k) (reps : List M)
    (hcover : ∀ x ∈ K, x = 1 ∨ x = z ∨ ∃ r ∈ reps, ∃ c ∈ K, x = c * r * c⁻¹)
    (hgen : ∀ r ∈ reps, K ≤ Subgroup.closure (conjClass K r)) {x y : M} (hx : x ∈ K)
    (hy : y ∈ K) (hxy1 : x * y * x⁻¹ * y⁻¹ ≠ 1) (hxyz : x * y * x⁻¹ * y⁻¹ ≠ z) :
    CFSG.Open.IsQuasisimple ↥K ∧ Subgroup.center ↥K = Subgroup.zpowers (⟨z, hzK⟩ : K) := by
  set z' : K := ⟨z, hzK⟩ with hz'
  set x' : K := ⟨x, hx⟩
  set y' : K := ⟨y, hy⟩
  have hcomm : (x' * y' * x'⁻¹ * y'⁻¹ : K) ∈ commutator K := by
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hcomm1 : ((x' * y' * x'⁻¹ * y'⁻¹ : K) : M) ≠ 1 := hxy1
  have hcommz : ((x' * y' * x'⁻¹ * y'⁻¹ : K) : M) ≠ z := hxyz
  have hz'c : z' ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2)
  have hxy : x' * y' ≠ y' * x' := by
    intro h
    apply hxy1
    have h1 := congrArg Subtype.val h
    simp only [x', y', Subgroup.coe_mul] at h1
    rw [h1]
    group
  have hnc : ¬ ∀ g h : K, g * h = h * g := fun h => hxy (h x' y')
  have hcenter : ∀ w : K, w ∈ Subgroup.center K → w = 1 ∨ w = z' := by
    intro w hw
    by_contra hne
    push Not at hne
    have hw1 : (w : M) ≠ 1 := fun h => hne.1 (Subtype.ext h)
    have hwz : (w : M) ≠ z := fun h => hne.2 (Subtype.ext h)
    have hle : Subgroup.zpowers w ≤ Subgroup.center K := (Subgroup.zpowers_le).2 hw
    have hnorm : (Subgroup.zpowers w).Normal := Subgroup.normal_of_le_center hle
    have htop := normal_eq_top_of_cover reps hcover hgen (Subgroup.zpowers w)
      (Subgroup.mem_zpowers w) hw1 hwz
    apply hnc
    intro g h
    have hg : g ∈ Subgroup.center K := hle (by rw [htop]; exact Subgroup.mem_top _)
    rw [Subgroup.mem_center_iff] at hg
    exact (hg h).symm
  have hcen_eq : Subgroup.center K = Subgroup.zpowers z' := by
    apply le_antisymm
    · intro w hw
      rcases hcenter w hw with rfl | rfl
      · exact one_mem _
      · exact Subgroup.mem_zpowers _
    · exact (Subgroup.zpowers_le).2 hz'c
  refine ⟨⟨?_, ?_⟩, hcen_eq⟩
  · have hnormal : (commutator K).Normal := inferInstance
    exact normal_eq_top_of_cover reps hcover hgen (commutator K) hcomm hcomm1 hcommz
  · have hnt : Nontrivial (K ⧸ Subgroup.center K) := by
      refine ⟨⟨QuotientGroup.mk x', 1, fun hh => ?_⟩⟩
      have hc : x' ∈ Subgroup.center K := (QuotientGroup.eq_one_iff x').1 hh
      rw [Subgroup.mem_center_iff] at hc
      exact hxy (hc y').symm
    refine @IsSimpleGroup.mk _ _ hnt fun H hH => ?_
    · set N : Subgroup K := H.comap (QuotientGroup.mk' (Subgroup.center K))
      have hNn : N.Normal := hH.comap _
      by_cases hle : ∀ k ∈ N, k ∈ Subgroup.center K
      · left
        rw [eq_bot_iff]
        intro q hq
        obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
        have hkN : k ∈ N := hq
        have := hle k hkN
        rw [Subgroup.mem_bot]
        exact (QuotientGroup.eq_one_iff k).2 this
      · right
        push Not at hle
        obtain ⟨k, hkN, hkc⟩ := hle
        have hk1 : (k : M) ≠ 1 := fun h => hkc (by
          rw [show k = 1 from Subtype.ext h]; exact one_mem _)
        have hkz : (k : M) ≠ z := fun h => hkc (by
          rw [show k = z' from Subtype.ext h]; exact hz'c)
        have htop := normal_eq_top_of_cover reps hcover hgen N hkN hk1 hkz
        rw [eq_top_iff]
        intro q _
        obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective q
        have : k' ∈ N := by rw [htop]; exact Subgroup.mem_top _
        exact this

end CFSG.ClassicalInvolution
