module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5ZSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5FBDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510R
public import CFSG.GroupTheory.ElemAbelianClosure

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5z_vecWeight_single_add (v : Fin 6 → ZMod 2) (i : Fin 6) (hv : vecWeight v = 4) :
    vecWeight (Pi.single i 1 + v) = 3 ∨ vecWeight (Pi.single i 1 + v) = 5 := by
  revert v i
  decide +kernel

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {Q₁ Q₂ : Subgroup G}

theorem sec5z_claimZ (hy : Sec5B59Hyp) (h55 : Asc82Lemma55) (h58d : Asc82Lemma58d)
    (hFB : Asc82Sec5FactB5z) (h4 : Asc82FactReflCentQ6) (h : Sec5Ctx G t L S z)
    (hnc : ¬ ∃ g : G, g⁻¹ * t * g = t * z) (hQ : Sec510Q G L z Q₁ Q₂) {x : G}
    (hxt : ∃ g : G, g⁻¹ * t * g = x) (hne : x ≠ t) (hxc : x * t = t * x) (hxz : x * z = z * x)
    (hxQ : x ∉ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G)) :
    ∃ g : G, g⁻¹ * z * g = x * z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g₀, hg₀⟩ := hxt
  have hxC : x ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hxc
  have hty : ∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 1 α := by
    rcases h55 G t L S z h with h5 | h5
    · exact absurd h5 hnc
    · have h5' := h5 g₀ (by rw [hg₀]; exact hxC) (by rw [hg₀]; exact hne)
      rwa [hg₀] at h5'
  have hx2 : orderOf x = 2 := by
    rw [← hg₀, orderOf_conjugate_eq]
    exact h.involution
  have hxx : x * x = 1 := by
    have h1 := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at h1
  have hxN : x ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer hy.h36 h.toSec5Setting.toSec3SettingLB x hxC
  obtain ⟨B, hBle, hBE, htB, hzB, hinf, hBeq⟩ :=
    hFB G L h.toSec5Setting.isOm6Z2 t (sec5_t_mem_centerIn hy.h52b h.toSec5Setting) h.involution z
      h.pocket x hx2 hxz hty
  have h2x : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2]; norm_num)
  have hB2 : IsPGroup 2 B := IsPGroup.of_card (n := 5) hBE.2
  have hxB : ∀ a ∈ zpowers x, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbx : Commute b x := Subgroup.mem_centralizer_singleton_iff.mp (hBle hb).2
    exact hbx.symm.zpow_left k
  have hA2 : IsPGroup 2 ↥(zpowers x ⊔ B) :=
    CFSG.OddStandard.SmallF3.HarrisU33.isPGroup_sup_of_commute hxB h2x hB2
  have hAt : zpowers x ⊔ B ≤ centralizer ({t} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hxC) ((hBle.trans inf_le_left).trans h.component.le)
  have hAz : zpowers x ⊔ B ≤ centralizer ({z} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxz))
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr
        (CFSG.Open.IsElemAbelian.comm hBE.1 hb hzB))
  obtain ⟨S', hAS', hnot⟩ := sec5z_exists_sylow_ctx h hA2 hAt hAz
  have hR : Sec5RCtx G t L S' z x B (zpowers x ⊔ B) :=
    { toSec5Ctx := { toSec5Setting := h.toSec5Setting, toAsc82Notation := hnot }
      conj_r := ⟨g₀, hg₀⟩
      type_r := hty
      B_le := hBle
      B_E32 := hBE
      B_split := ⟨htB, hinf, hBeq⟩
      A_eq := rfl
      A_le := hAS' }
  obtain ⟨φ, hm⟩ := sec5b_model58_of h58d hR
  obtain ⟨i, hi⟩ := hm.r_mem
  obtain ⟨v, hv4, hvz⟩ := hm.z_mem
  have hxz' : x * z = φ (Pi.single i 1 + v) := by rw [hm.perm.map_add, hi, hvz]
  rcases sec5z_vecWeight_single_add v i hv4 with h3 | h5
  ·
    have hW3 : x * z ∈ wclass φ 3 := ⟨_, h3, hxz'.symm⟩
    have hmem : x * z ∈ conjClassIn (normalizer ((zpowers x ⊔ B : Subgroup G) : Set G)) z := by
      rw [sec5b_zM_eq hy hR hm]
      exact Or.inl hW3
    obtain ⟨m, -, hmx⟩ := hmem
    exact ⟨m⁻¹, by rw [hmx]; group⟩
  ·
    exfalso
    apply hxQ
    have ht2 : ∃ α : ℤˣ, InducesTypeSome L (x * z) 6 (-1) 1 α := by
      rw [hxz']
      exact hm.type_one _ (Or.inr h5)
    exact h4 G L z h.toSec5Setting.isOm6Z2 h.pocket Q₁ Q₂ hQ.le₁ hQ.le₂ hQ.iso₁ hQ.iso₂ hQ.comm
      hQ.card hQ.center hQ.not_central x hxN hxx hxz hty ht2

end CFSG.OddStandard.SmallF3.Omega
