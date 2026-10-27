module

public import CFSG.GH74.GLS.IVK.Lifted.Strong

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.ABGDGroups CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

theorem inducesInner_cmap {G : Type} [Group G] {s : G} {K : Subgroup G} (h : InducesInner s K)
    (t : G) : InducesInner (t * s * t⁻¹) (cmap t K) := by
  obtain ⟨k, hk, hks⟩ := h
  refine ⟨t * k * t⁻¹, ?_, ?_⟩
  · rw [mem_cmap]
    have e : t⁻¹ * (t * k * t⁻¹) * t = k := by group
    rw [e]
    exact hk
  · have e : t * s * t⁻¹ * (t * k * t⁻¹)⁻¹ = t * (s * k⁻¹) * t⁻¹ := by group
    rw [e]
    exact mem_cSec_cmap hks t

theorem iii2_9_5_r2_of_II4 (h44 : II4_44) (h2A7 : II4_2A7) : III2_9_5_r2 := by
  intro G _ _ z S K₁ K₂ h hQ a haS ha2 hcomm haN₁ haN₂ hin
  have hstd := h
  have hK₂ : K₂ ∈ ({K₁, K₂} : Set (Subgroup G)) := Set.mem_insert_of_mem _ rfl
  have hK₁ : K₁ ∈ ({K₁, K₂} : Set (Subgroup G)) := Set.mem_insert _ _
  have hOK₁ := std4_hatOK h44 hstd hK₁
  have hOK₂ := std4_hatOK h44 hstd hK₂
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha2, sq] at this
  have hperm : ∀ c ∈ Cz z, (cmap c K₁ = K₁ ∧ cmap c K₂ = K₂) ∨
      (cmap c K₁ = K₂ ∧ cmap c K₂ = K₁) := fun c hc => std4_perm_cmap hstd hc
  by_cases hA : ∀ c ∈ Cz z, c ∈ normalizer (K₁ : Set G)
  · have hA₂ : ∀ c ∈ Cz z, c ∈ normalizer (K₂ : Set G) := by
      intro c hc
      rcases hperm c hc with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact (cmap_eq_iff_normalizer K₂ c).1 h2
      · exact absurd (((cmap_eq_iff_normalizer K₁ c).2 (hA c hc)).symm.trans h1) hstd.ne
    have hin2 := commBar_phi_inner h2A7 hOK₂.sl2 (fun c hc => hA₂ c hc) haN₂ haa hcomm
    exact (phi_mem_inn_iff K₂ haN₂).1 hin2
  · push Not at hA
    obtain ⟨t, htC, htn⟩ := hA
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
      have := dict_out_abelian h2A7 hOK₁.sl2 β⁻¹ α⁻¹
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
    have hρx : ρ x = QuotientGroup.mk (phi K₁ (x : G) haN₁) := rfl
    have hρy : ρ ⟨t⁻¹ * (x : G) * t, hty⟩ = QuotientGroup.mk (phi K₁ (t⁻¹ * (x : G) * t) hyN) := rfl
    rw [hρx, hρy] at hNx
    have hx1 : phi K₁ (x : G) haN₁ ∈ innOf (Hat K₁) := (phi_mem_inn_iff K₁ haN₁).2 hin
    have hmk1 : (QuotientGroup.mk (phi K₁ (x : G) haN₁) : MulAut (Hat K₁) ⧸ innOf (Hat K₁)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hx1
    rw [hmk1, one_mul] at hNx
    have hy1 : phi K₁ (t⁻¹ * (x : G) * t) hyN ∈ innOf (Hat K₁) :=
      (QuotientGroup.eq_one_iff _).1 hNx.symm
    have hInn : InducesInner (t⁻¹ * (x : G) * t) K₁ := (phi_mem_inn_iff K₁ hyN).1 hy1
    have h2 := inducesInner_cmap hInn t
    have e1 : t * (t⁻¹ * (x : G) * t) * t⁻¹ = (x : G) := by group
    rw [e1, hsw.1] at h2
    exact h2


end CFSG.GH74.GLS.IVK.Lifted
