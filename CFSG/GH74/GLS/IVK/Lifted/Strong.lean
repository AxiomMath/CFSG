module

public import CFSG.GH74.GLS.IVK.Lifted.Out
public import CFSG.GH74.GLS.IVK.Lifted.SwapNorm

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.ABGDGroups CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

section CmapLemmas

variable {G : Type} [Group G]

theorem cmap_eq_iff_normalizer (K : Subgroup G) (g : G) :
    cmap g K = K ↔ g ∈ normalizer (K : Set G) := by
  rw [← Subgroup.inv_mem_iff (x := g) (H := normalizer (K : Set G)), Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have := SetLike.ext_iff.1 h x
    rw [mem_cmap] at this
    simpa using this.symm
  · intro h
    ext x
    rw [mem_cmap]
    have := h x
    simpa using this.symm

theorem mem_cSec_cmap {K : Subgroup G} {x : G} (hx : x ∈ cSec K) (c : G) :
    c * x * c⁻¹ ∈ cSec (cmap c K) := by
  have h1 := cmap_mem_centralizerSection hx c
  rw [← pPrimeCoreOf_cmap] at h1
  exact h1

theorem std4_perm_cmap [Finite G] {z : G} {S K₁ K₂ : Subgroup G} (h : Std4 G z S K₁ K₂) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) :
    (cmap c K₁ = K₁ ∧ cmap c K₂ = K₂) ∨ (cmap c K₁ = K₂ ∧ cmap c K₂ = K₁) := by
  have hA : cmap c K₁ ∈ ({K₁, K₂} : Set (Subgroup G)) := by
    rw [← h.comps]
    exact isRigidRankOneComp_cmap (h.comp_rigid (Or.inl rfl)) hc
  have hB : cmap c K₂ ∈ ({K₁, K₂} : Set (Subgroup G)) := by
    rw [← h.comps]
    exact isRigidRankOneComp_cmap (h.comp_rigid (Or.inr rfl)) hc
  have hinj : cmap c K₁ ≠ cmap c K₂ := fun he => h.ne (by
    have := congrArg (cmap c⁻¹) he
    rwa [cmap_inv_cancel, cmap_inv_cancel] at this)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (hA.trans hB.symm) hinj
  · exact Or.inl ⟨hA, hB⟩
  · exact Or.inr ⟨hA, hB⟩
  · exact absurd (hA.trans hB.symm) hinj

end CmapLemmas

section Strong

theorem ivk_3_2a_strong_of_II4 (h44 : II4_44) (h2A7 : II4_2A7) : IVK_3_2a_strong := by
  intro G _ _ z S K₁ K₂ a h haS ha2 haz haF hac hcomm
  have hstd := h.std
  have hK₁ : K₁ ∈ ({K₁, K₂} : Set (Subgroup G)) := Set.mem_insert _ _
  have hOK := std4_hatOK h44 hstd hK₁
  obtain ⟨haN, hF⟩ := haF
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha2, sq] at this
  have hφ1 : phi K₁ a haN ≠ 1 := fun h1 => hac ((phi_eq_one_iff K₁ haN).1 h1)
  have hφ2 : phi K₁ a haN * phi K₁ a haN = 1 := by
    rw [← phi_mul K₁ haN haN]
    exact (phi_eq_one_iff K₁ (mul_mem haN haN)).2 (by rw [haa]; exact (cSec K₁).one_mem)
  have haC : a ∈ Cz z := hstd.sylow.le haS
  by_cases hA : ∀ c ∈ Cz z, c ∈ normalizer (K₁ : Set G)
  · exfalso
    have hin := commBar_phi_inner h2A7 hOK.sl2 (fun c hc => hA c hc) haN haa hcomm
    obtain ⟨c, hc⟩ := hin
    have hcz : c ∈ Subgroup.center (Hat K₁) := dict_inner h2A7 hOK.sl2 c (by rw [hc]; exact hF)
    exact hφ1 (by rw [← hc]; exact conj_eq_one_of_mem_center hcz)
  · push Not at hA
    obtain ⟨t, htC, htn⟩ := hA
    have hperm : ∀ c ∈ Cz z, (cmap c K₁ = K₁ ∧ cmap c K₂ = K₂) ∨
        (cmap c K₁ = K₂ ∧ cmap c K₂ = K₁) := fun c hc => std4_perm_cmap hstd hc
    have hsw : cmap t K₁ = K₂ ∧ cmap t K₂ = K₁ := by
      rcases hperm t htC with ⟨h1, _⟩ | h2
      · exact absurd ((cmap_eq_iff_normalizer K₁ t).1 h1) htn
      · exact h2
    set C₁ : Subgroup G := Cz z ⊓ normalizer (K₁ : Set G) with hC₁
    have hfix : ∀ c ∈ C₁, cmap c K₁ = K₁ ∧ cmap c K₂ = K₂ := by
      intro c hc
      rcases hperm c hc.1 with h1 | ⟨h1, _⟩
      · exact h1
      · exact absurd (((cmap_eq_iff_normalizer K₁ c).2 hc.2).symm.trans h1) hstd.ne
    have hswap : ∀ x ∈ Cz z, x ∉ C₁ → cmap x K₁ = K₂ ∧ cmap x K₂ = K₁ := by
      intro x hx hx1
      rcases hperm x hx with ⟨h1, _⟩ | h2
      · exact absurd ⟨hx, (cmap_eq_iff_normalizer K₁ x).1 h1⟩ hx1
      · exact h2
    have hnorm : ∀ x ∈ Cz z, ∀ c ∈ C₁, x * c * x⁻¹ ∈ C₁ := by
      intro x hx c hc
      have hxc : x * c * x⁻¹ ∈ Cz z := mul_mem (mul_mem hx hc.1) (inv_mem hx)
      refine Subgroup.mem_inf.2 ⟨hxc, (cmap_eq_iff_normalizer K₁ _).1 ?_⟩
      have hK' : cmap x⁻¹ K₁ = K₁ ∨ cmap x⁻¹ K₁ = K₂ := by
        rcases hperm x⁻¹ (inv_mem hx) with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inl h1
        · exact Or.inr h1
      have hcK' : cmap c (cmap x⁻¹ K₁) = cmap x⁻¹ K₁ := by
        rcases hK' with h1 | h1
        · rw [h1]
          exact (hfix c hc).1
        · rw [h1]
          exact (hfix c hc).2
      calc cmap (x * c * x⁻¹) K₁ = cmap x (cmap c (cmap x⁻¹ K₁)) := by
            rw [cmap_cmap, cmap_cmap]
        _ = cmap x (cmap x⁻¹ K₁) := by rw [hcK']
        _ = K₁ := cmap_cancel x K₁
    have hidx : ∀ x ∈ Cz z, ∀ y ∈ Cz z, x ∉ C₁ → y ∉ C₁ → x * y ∈ C₁ := by
      intro x hx y hy hx1 hy1
      refine Subgroup.mem_inf.2 ⟨mul_mem hx hy, (cmap_eq_iff_normalizer K₁ _).1 ?_⟩
      rw [← cmap_cmap, (hswap y hy hy1).1, (hswap x hx hx1).2]
    have : (innOf (Hat K₁)).Normal := innOf_normal _
    have hOutComm : ∀ x y : MulAut (Hat K₁) ⧸ innOf (Hat K₁), x * y = y * x := by
      intro x y
      induction x using QuotientGroup.induction_on with | H α => ?_
      induction y using QuotientGroup.induction_on with | H β => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have := dict_out_abelian h2A7 hOK.sl2 β⁻¹ α⁻¹
      simpa [mul_assoc] using this
    let _ : CommGroup (MulAut (Hat K₁) ⧸ innOf (Hat K₁)) :=
      { (inferInstance : Group (MulAut (Hat K₁) ⧸ innOf (Hat K₁))) with mul_comm := hOutComm }
    let ρ : ↥C₁ →* (MulAut (Hat K₁) ⧸ innOf (Hat K₁)) :=
      (QuotientGroup.mk' (innOf (Hat K₁))).comp ((phiHom K₁).comp
        (Subgroup.inclusion (inf_le_right : C₁ ≤ normalizer (K₁ : Set G))))
    obtain ⟨N, hNdef, hNker⟩ := swap_norm_exists (Cz z) C₁ hnorm hidx htC (fun h => htn h.2) ρ
    have hmodd : Odd (Nat.card ↥(Oz z)) := card_Oz_odd
    set m := Nat.card ↥(Oz z) with hm
    let ν : ↥C₁ →* (MulAut (Hat K₁) ⧸ innOf (Hat K₁)) := (powMonoidHom m).comp N
    let M : Subgroup G := ν.ker.map C₁.subtype
    have hM1 : ⁅Cz z, Cz z⁆ ≤ M := by
      intro x hx
      obtain ⟨hx1, hN1⟩ := hNker x hx
      refine Subgroup.mem_map.2 ⟨⟨x, hx1⟩, ?_, rfl⟩
      show (N ⟨x, hx1⟩) ^ m = 1
      rw [hN1, one_pow]
    have hM2 : Oz z ≤ M := by
      intro o ho
      have hoC : o ∈ Cz z := TwoThin.pPrimeCoreOf_le (Cz z) ho
      have h1 : (⟨o, ho⟩ : ↥(Oz z)) ^ m = 1 := pow_card_eq_one'
      have h2 : o ^ m = 1 := by simpa using congrArg Subtype.val h1
      have hoC₁ : o ∈ C₁ := by
        by_contra hoC₁
        have h3 : o * o ∈ C₁ := hidx o hoC o hoC hoC₁ hoC₁
        have hmodd' := hmodd
        obtain ⟨k, hk⟩ := hmodd'
        have h4 : o = (o * o) ^ (k + 1) := by
          have h5 : o ^ (2 * k + 1) = 1 := by rw [← hk]; exact h2
          calc o = o * o ^ (2 * k + 1) := by rw [h5, mul_one]
            _ = (o * o) ^ (k + 1) := by
              rw [← pow_succ', show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, sq]
        have h6 : (o * o) ^ (k + 1) ∈ C₁ := C₁.pow_mem h3 (k + 1)
        rw [← h4] at h6
        exact hoC₁ h6
      refine Subgroup.mem_map.2 ⟨⟨o, hoC₁⟩, ?_, rfl⟩
      show (N ⟨o, hoC₁⟩) ^ m = 1
      rw [← map_pow]
      have : (⟨o, hoC₁⟩ : ↥C₁) ^ m = 1 := Subtype.ext (by simpa using h2)
      rw [this, map_one]
    have hM3 : commBar z ≤ M := sup_le hM1 hM2
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 (hM3 hcomm)
    have hxa' : (x : G) = a := hxa
    have hNm : (N x) ^ m = 1 := hx
    have hN2 : N x * N x = 1 := by
      rw [← map_mul]
      have : x * x = 1 := Subtype.ext (by simp [hxa', haa])
      rw [this, map_one]
    have hN1 : N x = 1 := by
      have hmodd' := hmodd
      obtain ⟨k, hk⟩ := hmodd'
      have : (N x) ^ (2 * k + 1) = N x := by
        rw [pow_succ, pow_mul, sq, hN2, one_pow, one_mul]
      rw [← this, ← hk]
      exact hNm
    subst hxa'
    have hty : t⁻¹ * (x : G) * t ∈ C₁ := by simpa using hnorm t⁻¹ (inv_mem htC) x x.2
    have hNx := hNdef x hty
    rw [hN1] at hNx
    have hyN : t⁻¹ * (x : G) * t ∈ normalizer (K₁ : Set G) := hty.2
    have hρx : ρ x = QuotientGroup.mk (phi K₁ (x : G) haN) := rfl
    have hρy : ρ ⟨t⁻¹ * (x : G) * t, hty⟩ = QuotientGroup.mk (phi K₁ (t⁻¹ * (x : G) * t) hyN) := rfl
    rw [hρx, hρy] at hNx
    have hin : phi K₁ (t⁻¹ * (x : G) * t) hyN * (phi K₁ (x : G) haN)⁻¹ ∈ innOf (Hat K₁) := by
      have h1 : QuotientGroup.mk (phi K₁ (t⁻¹ * (x : G) * t) hyN * phi K₁ (x : G) haN) =
          (1 : MulAut (Hat K₁) ⧸ innOf (Hat K₁)) := by
        rw [QuotientGroup.mk_mul, mul_comm]
        exact hNx.symm
      have h2 := (QuotientGroup.eq_one_iff _).1 h1
      rwa [inv_eq_of_mul_eq_one_right hφ2]
    have hψ2 : phi K₁ (t⁻¹ * (x : G) * t) hyN * phi K₁ (t⁻¹ * (x : G) * t) hyN = 1 := by
      rw [← phi_mul K₁ hyN hyN]
      refine (phi_eq_one_iff K₁ (mul_mem hyN hyN)).2 ?_
      have e : (t⁻¹ * (x : G) * t) * (t⁻¹ * (x : G) * t) = 1 := by
        calc (t⁻¹ * (x : G) * t) * (t⁻¹ * (x : G) * t) = t⁻¹ * ((x : G) * (x : G)) * t := by group
          _ = 1 := by rw [haa]; group
      rw [e]
      exact (cSec K₁).one_mem
    have hψf : IsFAutomorphism (Hat K₁) (phi K₁ (t⁻¹ * (x : G) * t) hyN) :=
      dict_coset h2A7 hOK _ _ hF hφ1 hφ2 hψ2 hin
    have hFψ : InducesFAut (t⁻¹ * (x : G) * t) K₁ := ⟨hyN, hψf⟩
    have h2 := inducesFAut_conj t hFψ
    have e1 : t * (t⁻¹ * (x : G) * t) * t⁻¹ = (x : G) := by group
    have e2 : K₁.map (MulAut.conj t).toMonoidHom = K₂ := hsw.1
    rw [e1, e2] at h2
    refine ⟨h2, fun hcs => ?_⟩
    have h3 := mem_cSec_cmap hcs t⁻¹
    have e3 : cmap t⁻¹ K₂ = K₁ := by
      rw [← hsw.1, cmap_inv_cancel]
    rw [e3, inv_inv] at h3
    have h4 : phi K₁ (t⁻¹ * (x : G) * t) hyN = 1 := (phi_eq_one_iff K₁ hyN).2 h3
    rw [h4, one_mul] at hin
    obtain ⟨c, hc⟩ := (innOf (Hat K₁)).inv_mem_iff.1 hin
    have hcz : c ∈ Subgroup.center (Hat K₁) := dict_inner h2A7 hOK.sl2 c (by rw [hc]; exact hF)
    exact hφ1 (by rw [← hc]; exact conj_eq_one_of_mem_center hcz)

end Strong

end CFSG.GH74.GLS.IVK.Lifted
