module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs11b
public import CFSG.GH74.GLS.Stage2.Signalizer.L48Stmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs11
public import CFSG.GH74.GLS.Stage2.Local.Lemma23eRes

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section CaseB

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {Q T U : Subgroup G} {t g : G}

omit [Finite G] in
theorem mem_centralizer_U {y : G} (hU : U = zpowers z ⊔ zpowers t) (hz : y * z = z * y) (ht : y * t = t * y) :
    y ∈ centralizer (U : Set G) := by
  have hle : U ≤ centralizer ({y} : Set G) := by
    rw [hU]
    exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hz.symm))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr ht.symm))
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

theorem Ctx10.cen_eq_one_of_Op_bot (h : Ctx10 G z k S M p Q T U t g) (hbot : Op p (centralizer (U : Set G)) = ⊥)
    {x : G} (hx : x ∈ Op p M) (hxc : x ∈ centralizer (U : Set G)) : x = 1 := by
  have hn : centralizer (U : Set G) ≤ normalizer ((Op p M ⊓ centralizer (U : Set G) : Subgroup G) : Set G) :=
    fun c hc => mem_normalizer_inf (le_normalizer_Op' p M (h.cenU_le_M hc)) (Subgroup.le_normalizer hc)
  have hle := le_Op_of_normal inf_le_right hn ((op_isPGroup M).to_le inf_le_left)
  rw [hbot] at hle
  exact Subgroup.mem_bot.mp (hle ⟨hx, hxc⟩)

theorem Ctx10.eq_one_of_cen_z (h : Ctx10 G z k S M p Q T U t g) (hone : TypeOneCase G k)
    (hbot : Op p (centralizer (U : Set G)) = ⊥) {x : G} (hx : x ∈ Op p M) (hxz : x * z = z * x) : x = 1 := by
  by_contra hx1
  let P₁ : Subgroup G := Op p M ⊓ Cen z
  have hxP₁ : x ∈ P₁ := ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxz⟩
  have hzc : ∀ y ∈ P₁, z * y * z⁻¹ = y := by
    intro y hy
    have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    rw [← hyz]
    group
  have hCn : ∀ c ∈ Cen z, c ∈ normalizer (P₁ : Set G) := fun c hc =>
    mem_normalizer_inf (le_normalizer_Op' p M (h.ctx9.cen_le hc)) (Subgroup.le_normalizer hc)
  have htN : t ∈ normalizer (P₁ : Set G) := hCn t (h.U_le_Cen h.t_mem_U)
  have hfix : ∀ y ∈ P₁, t * y * t⁻¹ = y → y = 1 := by
    intro y hy hty
    have hty' : t * y = y * t := by
      calc t * y = (t * y * t⁻¹) * t := by group
        _ = y * t := by rw [hty]
    have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    exact h.cen_eq_one_of_Op_bot hbot hy.1 (mem_centralizer_U h.choice.U_gen hyz hty'.symm)
  have hinv := inverts_of_fpf h.t_mul_t htN hfix
  have hcomm := commutator_le_centralizer_of_inverts h.t_mul_t hzc hinv h.z_comm_t hCn
  rw [← h.choice.U_gen] at hcomm
  have hlem := h.ctx9.ctx.lemma23e U h.choice.U_le h.choice.U_four (h.choice.T_one hone).2
  have htC : t ∈ centralizer (P₁ : Set G) := hcomm (hlem.1 h.t_mem_U).2
  apply hx1
  apply hfix x hxP₁
  have hxt : x * t = t * x := Subgroup.mem_centralizer_iff.mp htC x hxP₁
  rw [← hxt, mul_inv_cancel_right]

theorem prop_11_2_caseB (h48 : L48.Lemma4_8w) (h : Ctx10 G z k S M p Q T U t g) (hone : TypeOneCase G k)
    (hbot : Op p (centralizer (U : Set G)) = ⊥) : False := by
  have hp := h.ctx9.prime
  have hp2 := h.ctx9.odd
  have hzN : z ∈ normalizer ((Op p M : Subgroup G) : Set G) := le_normalizer_Op' p M h.ctx9.z_mem
  have htM : t ∈ M := h.U_le_M h.t_mem_U
  have htN : t ∈ normalizer ((Op p M : Subgroup G) : Set G) := le_normalizer_Op' p M htM
  have hzinv : ∀ x ∈ Op p M, z * x * z⁻¹ = x⁻¹ := by
    refine inverts_of_fpf h.ctx9.z_mul_z hzN fun x hx hxz => ?_
    refine h.eq_one_of_cen_z hone hbot hx ?_
    calc x * z = (z * x * z⁻¹) * z := by rw [hxz]
      _ = z * x := by group
  have hA : ∃ a ∈ Op p M, t * a = a * t ∧ a ≠ 1 := by
    by_contra hnone
    have hfix : ∀ x ∈ Op p M, t * x * t⁻¹ = x → x = 1 := by
      intro x hx hxt
      by_contra hx1
      refine hnone ⟨x, hx, ?_, hx1⟩
      calc t * x = (t * x * t⁻¹) * t := by group
        _ = x * t := by rw [hxt]
    have htinv := inverts_of_fpf h.t_mul_t htN hfix
    have hztc : z * t ∈ centralizer ((Op p M : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have e : z * t * x * (z * t)⁻¹ = x := by
        calc z * t * x * (z * t)⁻¹ = z * (t * x * t⁻¹) * z⁻¹ := by group
          _ = z * x⁻¹ * z⁻¹ := by rw [htinv x hx]
          _ = (z * x * z⁻¹)⁻¹ := by group
          _ = x := by rw [hzinv x hx, inv_inv]
      exact (mul_inv_eq_iff_eq_mul.mp e).symm
    have hsq : z * t * (z * t) = 1 := by
      calc z * t * (z * t) = z * (t * z) * t := by group
        _ = z * (z * t) * t := by rw [← h.z_comm_t]
        _ = (z * z) * (t * t) := by group
        _ = 1 := by rw [h.ctx9.z_mul_z, h.t_mul_t, one_mul]
    have hzt1 : z * t = 1 := h.ctx9.eq_one_of_cen (mul_mem h.ctx9.z_mem htM) hsq hztc
    exact h.t_ne_z ((eq_inv_of_mul_eq_one_right hzt1).trans (inv_eq_of_mul_eq_one_right h.ctx9.z_mul_z))
  obtain ⟨a, haP, hta, ha1⟩ := hA
  obtain ⟨n, hnU, hnz⟩ := h.exists_swap hone
  have hUS : U ≤ S := h.choice.U_le
  set H : Subgroup G := M.map (MulAut.conj n).toMonoidHom with hHdef
  have hHmem : ∀ x, x ∈ H ↔ n⁻¹ * x * n ∈ M := fun x => mem_map_conj_iff M n x
  have hnU' : ∀ u ∈ U, n⁻¹ * u * n ∈ U := by
    intro u hu
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hnU) u).mp hu
    simpa using this
  have hzH : z ∈ H := (hHmem z).mpr (h.U_le_M (hnU' z h.z_mem_U))
  have hHtop : H ≠ ⊤ := by
    intro hH
    apply h.ctx9.coatom.1
    rw [eq_top_iff]
    intro y _
    have h1 : n * y * n⁻¹ ∈ H := by rw [hH]; exact Subgroup.mem_top _
    have h2 := (hHmem _).mp h1
    have e : n⁻¹ * (n * y * n⁻¹) * n = y := by group
    rwa [e] at h2
  have hCtH : centralizer ({t} : Set G) ≤ H := by
    intro x hx
    have hx' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [hHmem]
    apply h.ctx9.cen_le
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : n⁻¹ * x * n * z = n⁻¹ * (x * t) * n := by
      rw [← hnz]
      group
    have e2 : z * (n⁻¹ * x * n) = n⁻¹ * (t * x) * n := by
      rw [← hnz]
      group
    rw [e1, e2, hx']
  have htZ : t ∈ zStar H := by
    have := zStar_map_of_mem (MulAut.conj n) (h.choice.z_star_one hone)
    rw [MulAut.conj_apply, hnz] at this
    exact this
  have hzNPH : z ∈ normalizer (((Op p M ⊓ H : Subgroup G)) : Set G) :=
    mem_normalizer_inf hzN (Subgroup.le_normalizer hzH)
  have hXle : ⁅Op p M ⊓ H, zpowers z⁆ ≤ Op p M ⊓ H :=
    commutator_le_of_normalizes (Subgroup.zpowers_le.mpr hzNPH)
  have hnormX : ∀ c : G, c ∈ M → c ∈ H → c * z = z * c →
      c ∈ normalizer ((⁅Op p M ⊓ H, zpowers z⁆ : Subgroup G) : Set G) := fun c hcM hcH hcz =>
    mem_normalizer_commutator (mem_normalizer_inf (le_normalizer_Op' p M hcM) (Subgroup.le_normalizer hcH))
      (mem_normalizer_zpowers_of_comm hcz)
  have haH : a ∈ H := hCtH (Subgroup.mem_centralizer_singleton_iff.mpr hta.symm)
  have haX : a ∈ ⁅Op p M ⊓ H, zpowers z⁆ :=
    mem_commutator_of_inverts (hzinv a haP) (odd_orderOf_of_pgroup hp h.ctx9.odd_p (op_isPGroup M) a haP)
      ⟨haP, haH⟩
  have hSig : Sig4Sub G z H p ⁅Op p M ⊓ H, zpowers z⁆ := by
    refine ⟨hHtop, hp, hp2, hzH, hXle.trans inf_le_right, (op_isPGroup M).to_le (hXle.trans inf_le_left), ?_, ?_, ?_⟩
    · intro hb
      apply ha1
      rw [hb] at haX
      exact Subgroup.mem_bot.mp haX
    · intro c hcH hcz
      exact hnormX c (h.ctx9.cen_le hcz) hcH (Subgroup.mem_centralizer_singleton_iff.mp hcz)
    · exact commutator_zpowers_idem h.ctx9.orderOf_z hp hp2 ((op_isPGroup M).to_le inf_le_left) hzNPH
  have hUg := h.choice.U_gen
  have hSinv : ∀ s ∈ S ⊓ centralizer (((zpowers z ⊔ zpowers t : Subgroup G)) : Set G),
      s ∈ normalizer ((⁅Op p M ⊓ H, zpowers z⁆ : Subgroup G) : Set G) := by
    intro s hs
    have hsU : s ∈ centralizer (U : Set G) := by rw [hUg]; exact hs.2
    have hzs : z * s = s * z := (Subgroup.mem_centralizer_iff.mp hsU z h.z_mem_U)
    have hts : t * s = s * t := (Subgroup.mem_centralizer_iff.mp hsU t h.t_mem_U)
    exact hnormX s (h.ctx9.S_le_M hs.1) (hCtH (Subgroup.mem_centralizer_singleton_iff.mpr hts.symm)) hzs.symm
  have h4 : ⁅Op p M ⊓ H, zpowers z⁆ ≤ Op p H :=
    h48 G z k S h.ctx9.ctx hone t H _ p (by rw [← hUg]; exact h.choice.U_four) (by rw [← hUg]; exact hUS)
      (by rw [← hUg]; exact (h.choice.T_one hone).2) hCtH htZ hSig hSinv
  have haOp : a ∈ Op p H := h4 haX
  rw [hHdef, Op_map] at haOp
  obtain ⟨w, hwP, hwa⟩ := haOp
  have hwa' : n * w * n⁻¹ = a := by simpa [MulAut.conj_apply] using hwa
  have h1 : t * a * t⁻¹ = a⁻¹ := by
    calc t * a * t⁻¹ = n * (z * w * z⁻¹) * n⁻¹ := by rw [← hnz, ← hwa']; group
      _ = n * w⁻¹ * n⁻¹ := by rw [hzinv w hwP]
      _ = a⁻¹ := by rw [← hwa']; group
  apply ha1
  refine eq_one_of_inverts_fixed hp hp2 (op_isPGroup M) haP h1 ?_
  rw [hta]
  group

end CaseB

section Prop112

variable {G : Type} [Group G] [Finite G]

theorem prop_11_2 (h103 : Prop10_3) (h48 : L48.Lemma4_8w) : Prop11_2 := by
  intro G _ _ z k S M p Q T U t g ctx hone
  have hp := ctx.ctx9.prime
  have hR : ∃ R : Subgroup G, Rp z k p T U Q M R ∧
      Covers (normalizer (R : Set G)) (normalizer (U : Set G)) (centralizer (U : Set G)) := by
    by_cases hbot : Op p (centralizer (U : Set G)) = ⊥
    · exact (prop_11_2_caseB h48 ctx hone hbot).elim
    · exact exists_R_of_Op_ne_bot ctx hone hbot
  obtain ⟨R, hRp, hcov⟩ := hR
  have hnot : ¬ normalizer (R : Set G) ≤ M := by
    intro hle
    apply ctx.not_normalizer_U_le_M hone
    intro x hx
    have h2 : (normalizer (R : Set G) ⊓ normalizer (U : Set G)) ⊔ centralizer (U : Set G) ≤ M :=
      sup_le (inf_le_left.trans hle) ctx.cenU_le_M
    exact h2 (hcov hx)
  refine ⟨⟨R, hRp, hcov, hnot⟩, ?_⟩
  rcases h103 G z k S M p Q T U t g ctx with hall | hLy
  · exact absurd ((normalizer_le_kInfty R).trans (hall R hRp)) hnot
  · exact hLy

end Prop112

end CFSG.GH74.GLS.Stage2.Bender.Thm2
