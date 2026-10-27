module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDesc
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.GroupActions (subgroupStabAut)
open scoped commutatorElement

section Descent

variable {G : Type} [Group G] [Finite G]

theorem ker_piCenterQuot {L : Subgroup G} {C : Type} [Group C] (θ : ↥L ⧸ Subgroup.center ↥L ≃* C) :
    (T171Sh.piCenterQuot θ).ker = Subgroup.center ↥L := by
  dsimp only [T171Sh.piCenterQuot]
  rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center ↥L)) θ.toMonoidHom θ.injective,
    QuotientGroup.ker_mk']

theorem piCenterQuot_surjective {L : Subgroup G} {C : Type} [Group C] (θ : ↥L ⧸ Subgroup.center ↥L ≃* C) :
    Function.Surjective (T171Sh.piCenterQuot θ) := by
  intro x
  obtain ⟨q, rfl⟩ := θ.surjective x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨l, rfl⟩

theorem glaPComponent_fixSubgroup_map_piCenterQuot {p : ℕ} (hp : p.Prime) {L J : Subgroup G} {d : G}
    (hdL : d ∈ Subgroup.normalizer (L : Set G))
    (hJ : GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G)) J)
    {C : Type} [Group C] [Finite C] (θ : ↥L ⧸ Subgroup.center ↥L ≃* C) {β : MulAut C}
    (hind : CFSG.Assembly.LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = d⁻¹ * (l : G) * d) β) :
    GLAPComponent p (fixSubgroup β) ((J.subgroupOf L).map (T171Sh.piCenterQuot θ)) := by
  classical
  let α : MulAut ↥L := L.normalizerMonoidHom ⟨d⁻¹, Subgroup.inv_mem _ hdL⟩
  have hα : ∀ x : ↥L, ((α x : ↥L) : G) = d⁻¹ * (x : G) * d := fun x => by
    simp [α]
  have hfixα : fixSubgroup α = (L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L := by
    ext x
    rw [mem_fixSubgroup, Subtype.ext_iff, hα]
    exact T171Sh.mem_centralizerInL.symm
  have hαβ : ∀ k, T171Sh.piCenterQuot θ (α k) = β (T171Sh.piCenterQuot θ k) := fun k =>
    (hind k (α k) (hα k)).symm
  have hJ' := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf hp inf_le_left hJ
  rw [← hfixα] at hJ'
  exact CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup _
    (ker_piCenterQuot θ).le α β hαβ (piCenterQuot_surjective θ) hp hJ'

theorem map_piCenterQuot_eq_of_normalizes {L J : Subgroup G} {b : G}
    (hbL : b ∈ Subgroup.normalizer (L : Set G)) (hbJ : b ∈ Subgroup.normalizer (J : Set G))
    {C : Type} [Group C] [Finite C] (θ : ↥L ⧸ Subgroup.center ↥L ≃* C) {φ : MulAut C}
    (hind : CFSG.Assembly.LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ) :
    ((J.subgroupOf L).map (T171Sh.piCenterQuot θ)).map φ.toMonoidHom =
      (J.subgroupOf L).map (T171Sh.piCenterQuot θ) := by
  have hle : ((J.subgroupOf L).map (T171Sh.piCenterQuot θ)).map φ.toMonoidHom ≤
      (J.subgroupOf L).map (T171Sh.piCenterQuot θ) := by
    rintro _ ⟨x, ⟨l, hl, rfl⟩, rfl⟩
    have hlJ : (l : G) ∈ J := Subgroup.mem_subgroupOf.1 hl
    have hmemJ : b⁻¹ * (l : G) * b ∈ J := by
      simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hbJ) (l : G)).1 hlJ
    have hmemL : b⁻¹ * (l : G) * b ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hbL) (l : G)).1 l.2
    exact ⟨⟨b⁻¹ * (l : G) * b, hmemL⟩, Subgroup.mem_subgroupOf.2 hmemJ,
      (hind l ⟨b⁻¹ * (l : G) * b, hmemL⟩ rfl).symm⟩
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective).symm)

theorem conj_mem_subgroupStabAut_map {C H : Type} [Group C] [Group H] (ι : C →* H) {φ : MulAut C} {y : H}
    (hφ : ∀ c, ι (φ c) = y * ι c * y⁻¹) {Jc : Subgroup C} (hJc : Jc.map φ.toMonoidHom = Jc) :
    MulAut.conj y ∈ subgroupStabAut (Jc.map ι) := by
  change (Jc.map ι).map (MulAut.conj y).toMonoidHom = Jc.map ι
  have hcomp : (MulAut.conj y).toMonoidHom.comp ι = ι.comp φ.toMonoidHom :=
    MonoidHom.ext fun c => by simp [hφ]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hJc]

theorem exists_centralSurjection {L J : Subgroup G} (hJL : J ≤ L) {C H : Type} [Group C] [Group H]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* C) (ι : C →* H) (hι : Function.Injective ι) {K : Subgroup H}
    (hK : ((J.subgroupOf L).map (T171Sh.piCenterQuot θ)).map ι = K) :
    ∃ f : ↥J →* ↥K, Function.Surjective f ∧ f.ker ≤ Subgroup.center ↥J ∧
      ∀ j : ↥J, (f j : H) = ι (T171Sh.piCenterQuot θ (Subgroup.inclusion hJL j)) := by
  subst hK
  let g : ↥J →* H := ι.comp ((T171Sh.piCenterQuot θ).comp (Subgroup.inclusion hJL))
  have hg : ∀ j, g j ∈ ((J.subgroupOf L).map (T171Sh.piCenterQuot θ)).map ι := fun j =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 j.2))
  refine ⟨g.codRestrict _ hg, ?_, ?_, fun j => rfl⟩
  · rintro ⟨_, _, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨⟨(l : G), Subgroup.mem_subgroupOf.1 hl⟩, rfl⟩
  · intro j hj
    have h1 : g j = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hj)
    have h2 : Subgroup.inclusion hJL j ∈ (T171Sh.piCenterQuot θ).ker := by
      rw [MonoidHom.mem_ker]
      exact hι (h1.trans ι.map_one.symm)
    rw [ker_piCenterQuot] at h2
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro k
    exact Subtype.ext (congrArg (fun t : ↥L => (t : G)) (h2 (Subgroup.inclusion hJL k)))

theorem le_of_map_piCenterQuot_le {L J K : Subgroup G} (hJL : J ≤ L) (hKL : K ≤ L) (hKperf : ⁅K, K⁆ = K)
    {C : Type} [Group C] (θ : ↥L ⧸ Subgroup.center ↥L ≃* C)
    (hle : (K.subgroupOf L).map (T171Sh.piCenterQuot θ) ≤ (J.subgroupOf L).map (T171Sh.piCenterQuot θ)) :
    K ≤ J := by
  have hdecomp : ∀ k ∈ K, ∃ j ∈ J, ∃ z ∈ L, (∀ x ∈ L, Commute x z) ∧ k = j * z := by
    intro k hk
    have hk' : (⟨k, hKL hk⟩ : ↥L) ∈ K.subgroupOf L := Subgroup.mem_subgroupOf.2 hk
    obtain ⟨l, hl, hπl⟩ := hle (Subgroup.mem_map_of_mem _ hk')
    have hz : l⁻¹ * ⟨k, hKL hk⟩ ∈ Subgroup.center ↥L := by
      rw [← ker_piCenterQuot θ, MonoidHom.mem_ker, map_mul, map_inv, hπl, inv_mul_cancel]
    refine ⟨l, Subgroup.mem_subgroupOf.1 hl, ((l⁻¹ * ⟨k, hKL hk⟩ : ↥L) : G), (l⁻¹ * ⟨k, hKL hk⟩).2,
      fun x hx => congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨x, hx⟩), ?_⟩
    simp
  rw [← hKperf, Subgroup.commutator_le]
  intro k₁ hk₁ k₂ hk₂
  obtain ⟨j₁, hj₁, z₁, hz₁L, hz₁, rfl⟩ := hdecomp k₁ hk₁
  obtain ⟨j₂, hj₂, z₂, hz₂L, hz₂, rfl⟩ := hdecomp k₂ hk₂
  rw [CFSG.HardMathSupport.Solomon.Coordinator.commutatorElement_mul_mul' (hz₁ _ (hJL hj₂)).symm
    (hz₂ _ hz₁L) (hz₂ _ (hJL hj₁)).symm, commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem hj₁ hj₂) (J.inv_mem hj₁)) (J.inv_mem hj₂)

end Descent

end CFSG.LocalAnalysis.GLTheoremA.T158

end
