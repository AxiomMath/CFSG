module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR5A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4ST2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {Ng : Subgroup G} [(hz.z4iSub Ng).Normal]

include hz

@[expose] def z4jT (u : ↥(ctxNQ t tau x₁ x₂ rho) ⧸ hz.z4iSub Ng) : Prop :=
  ∃ x : ↥(ctxNQ t tau x₁ x₂ rho), S4B.z4iπ (hz.z4iSub Ng) x = u ∧
    ∃ g : G, (x : G) = g * t * g⁻¹

private theorem z4j_odd (hN : Z4IOdd t tau x₁ x₂ rho Ng) :
    Odd (Nat.card (hz.z4iSub Ng)) := by
  rw [hz.z4i_card_sub hN.le_NQ]; exact hN.odd

private theorem z4j_witness_invol (hN : Z4IOdd t tau x₁ x₂ rho Ng)
    {x : ↥(ctxNQ t tau x₁ x₂ rho)} (hx : ∃ g : G, (x : G) = g * t * g⁻¹) :
    x * x = 1 ∧ x ≠ 1 := by
  obtain ⟨g, hg⟩ := hx
  constructor
  · apply Subtype.ext
    show (x : G) * (x : G) = (1 : G)
    rw [hg]
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hz.t_mul_self]; group
  · intro hx1
    apply hz.t_ne_one
    have hx1' : (x : G) = 1 := by rw [hx1]; rfl
    rw [hg] at hx1'
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [hx1']
      _ = 1 := by group

private theorem z4jT_ne_one (hN : Z4IOdd t tau x₁ x₂ rho Ng)
    {u : ↥(ctxNQ t tau x₁ x₂ rho) ⧸ hz.z4iSub Ng} (hu : hz.z4jT (Ng := Ng) u) : u ≠ 1 := by
  obtain ⟨x, hxu, hxconj⟩ := hu
  obtain ⟨hx2, hx1⟩ := z4j_witness_invol hz hN hxconj
  have hne : S4B.z4iπ (hz.z4iSub Ng) x ≠ 1 :=
    S4B.z4i_map_ne_one (hz.z4iSub Ng) (z4j_odd hz hN) hx2 hx1
  rw [← hxu]; exact hne

private lemma z4j_tau_sq : hz.z4iTau * hz.z4iTau = 1 := by
  apply Subtype.ext; show tau * tau = (1 : G); exact hz.tau_mul_self

private lemma z4j_lam_sq : hz.z4iLam * hz.z4iLam = 1 := by
  apply Subtype.ext; show lam * lam = (1 : G); exact hz.lam_mul_self

omit hz

private lemma z4j_mul_self_of_comm {a b : ↥(ctxNQ t tau x₁ x₂ rho)}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) : (a * b) * (a * b) = 1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab.symm]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

private lemma z4j_prod3_sq {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    (a * b * c) * (a * b * c) = 1 := by
  rw [show a * b * c = (a * b) * c from rfl, ← pow_two]
  have hcomm : Commute (a * b) c := (show Commute a c from hac).mul_left (show Commute b c from hbc)
  rw [hcomm.mul_pow, (show Commute a b from hab).mul_pow]
  simp only [pow_two, ha, hb, hc, mul_one, one_mul]

include hz

theorem z4jT_map_iff (hN : Z4IOdd t tau x₁ x₂ rho Ng) {a : ↥(ctxNQ t tau x₁ x₂ rho)}
    (ha : a * a = 1) (ha1 : a ≠ 1) :
    hz.z4jT (Ng := Ng) (S4B.z4iπ (hz.z4iSub Ng) a) ↔ ∃ g : G, (a : G) = g * t * g⁻¹ := by
  constructor
  · rintro ⟨x, hxπ, hxconj⟩
    obtain ⟨hx2, hx1⟩ := z4j_witness_invol hz hN hxconj
    obtain ⟨g', hg'⟩ := S4B.z4i_exists_conj_of_map_eq (hz.z4iSub Ng) (z4j_odd hz hN)
      ha ha1 hx2 hxπ.symm
    obtain ⟨g, hg⟩ := hxconj
    refine ⟨(g' : G) * g, ?_⟩
    have hcoe : (a : G) = (g' : G) * (x : G) * (g' : G)⁻¹ := by rw [hg']; rfl
    rw [hcoe, hg]
    group
  · rintro ⟨g, hg⟩
    exact ⟨a, rfl, g, hg⟩

theorem z4j_class (hN : Z4IOdd t tau x₁ x₂ rho Ng) :
    S4B.ZJClass (hz.z4jT (Ng := Ng))
      ((hz.z4iSub (ctxQ t tau x₁ x₂ rho)).map (S4B.z4iπ (hz.z4iSub Ng)))
      (S4B.z4iπ (hz.z4iSub Ng) hz.z4iT) (S4B.z4iπ (hz.z4iSub Ng) hz.z4iTau)
      (S4B.z4iπ (hz.z4iSub Ng) hz.z4iLam) := by
  refine
    { conj := ?_
      invol := ?_
      not_Q := ?_
      not_Qtau := ?_
      not_l := ?_
      not_ltau := ?_
      not_lttau := ?_ }
  · intro u g hu
    obtain ⟨x, hxu, hxconj⟩ := hu
    obtain ⟨g₀, hg₀⟩ := S4B.z4iπ_surjective (hz.z4iSub Ng) g
    refine ⟨g₀ * x * g₀⁻¹, ?_, ?_⟩
    · simp only [map_mul, map_inv, hxu, hg₀]
    · obtain ⟨gx, hgx⟩ := hxconj
      refine ⟨(g₀ : G) * gx, ?_⟩
      have hcoe : ((g₀ * x * g₀⁻¹ : ↥(ctxNQ t tau x₁ x₂ rho)) : G)
          = (g₀ : G) * (x : G) * (g₀ : G)⁻¹ := rfl
      rw [hcoe, hgx]
      group
  · intro u hu
    have hne : u ≠ 1 := z4jT_ne_one hz hN hu
    obtain ⟨x, hxu, hxconj⟩ := hu
    obtain ⟨hx2, hx1⟩ := z4j_witness_invol hz hN hxconj
    exact ⟨by rw [← hxu, ← map_mul, hx2, map_one], hne⟩
  · intro q hq hT
    obtain ⟨q₀, hq₀mem, hq₀eq⟩ := hq
    have hq₀Q : (q₀ : G) ∈ ctxQ t tau x₁ x₂ rho := (hz.z4i_mem_sub _ q₀).mp hq₀mem
    have hTq₀ : hz.z4jT (Ng := Ng) (S4B.z4iπ (hz.z4iSub Ng) q₀) := by rw [hq₀eq]; exact hT
    obtain ⟨x, hxπ, hxconj⟩ := hT
    obtain ⟨hx2, hx1⟩ := z4j_witness_invol hz hN hxconj
    have hker : S4B.z4iπ (hz.z4iSub Ng) (q₀ * q₀) = 1 := by
      rw [map_mul, hq₀eq, ← hxπ, ← map_mul, hx2, map_one]
    have hkerN : q₀ * q₀ ∈ hz.z4iSub Ng := by
      rw [← S4B.z4iπ_ker (hz.z4iSub Ng)]
      exact MonoidHom.mem_ker.mpr hker
    have hq₀sq : q₀ * q₀ = 1 := by
      apply Subtype.ext
      have hmem : ((q₀ * q₀ : ↥(ctxNQ t tau x₁ x₂ rho)) : G) ∈
          Ng ⊓ ctxQ t tau x₁ x₂ rho :=
        ⟨(hz.z4i_mem_sub Ng (q₀ * q₀)).mp hkerN, by
          show (q₀ : G) * (q₀ : G) ∈ ctxQ t tau x₁ x₂ rho
          exact mul_mem hq₀Q hq₀Q⟩
      rw [hN.inf_Q] at hmem
      simpa using Subgroup.mem_bot.mp hmem
    have hq₀ne : q₀ ≠ 1 := by
      intro h
      exact z4jT_ne_one hz hN hTq₀ (by rw [h, map_one])
    obtain ⟨g, hg⟩ := (z4jT_map_iff hz hN hq₀sq hq₀ne).mp hTq₀
    exact hz.tG_Qtau g (q₀ : G) (Subgroup.mem_sup_left hq₀Q) hg.symm
  · intro q hq hT
    obtain ⟨q₀, hq₀mem, hq₀eq⟩ := hq
    have hq₀Q : (q₀ : G) ∈ ctxQ t tau x₁ x₂ rho := (hz.z4i_mem_sub _ q₀).mp hq₀mem
    let a : ↥(ctxNQ t tau x₁ x₂ rho) := q₀ * hz.z4iTau
    have haπ : S4B.z4iπ (hz.z4iSub Ng) a =
        q * S4B.z4iπ (hz.z4iSub Ng) hz.z4iTau := by
      show S4B.z4iπ (hz.z4iSub Ng) (q₀ * hz.z4iTau) = _
      simp only [map_mul, hq₀eq]
    have hTa : hz.z4jT (Ng := Ng) (S4B.z4iπ (hz.z4iSub Ng) a) := by rw [haπ]; exact hT
    have htauq : tau * (q₀ : G) = (q₀ : G)⁻¹ * tau := by
      have h := hz.tau_inv_Q (q₀ : G) hq₀Q
      calc tau * (q₀ : G) = tau * (q₀ : G) * tau⁻¹ * tau := by group
        _ = (q₀ : G)⁻¹ * tau := by rw [h]
    have ha2 : a * a = 1 := by
      apply Subtype.ext
      show (q₀ : G) * tau * ((q₀ : G) * tau) = (1 : G)
      rw [show (q₀ : G) * tau * ((q₀ : G) * tau) = (q₀ : G) * (tau * (q₀ : G)) * tau by group,
        htauq]
      rw [show (q₀ : G) * ((q₀ : G)⁻¹ * tau) * tau =
          ((q₀ : G) * (q₀ : G)⁻¹) * (tau * tau) by group,
        mul_inv_cancel, one_mul, hz.tau_mul_self]
    have ha1 : a ≠ 1 := by
      intro h
      exact z4jT_ne_one hz hN hTa (by rw [h, map_one])
    obtain ⟨g, hg⟩ := (z4jT_map_iff hz hN ha2 ha1).mp hTa
    exact hz.tG_Qtau g ((q₀ : G) * tau)
      (Subgroup.mul_mem_sup hq₀Q (Subgroup.mem_zpowers tau)) hg.symm
  · intro hT
    have ha2 : hz.z4iLam * hz.z4iLam = 1 := by
      apply Subtype.ext
      show lam * lam = (1 : G)
      exact hz.lam_mul_self
    have ha1 : hz.z4iLam ≠ 1 := by
      intro h
      exact z4jT_ne_one hz hN hT (by rw [h, map_one])
    obtain ⟨g, hg⟩ := (z4jT_map_iff hz hN ha2 ha1).mp hT
    exact hz.not_conj_t_lam g hg.symm
  · intro hT
    let a : ↥(ctxNQ t tau x₁ x₂ rho) := hz.z4iLam * hz.z4iTau
    have haπ : S4B.z4iπ (hz.z4iSub Ng) a =
        S4B.z4iπ (hz.z4iSub Ng) hz.z4iLam * S4B.z4iπ (hz.z4iSub Ng) hz.z4iTau := by
      show S4B.z4iπ (hz.z4iSub Ng) (hz.z4iLam * hz.z4iTau) = _
      simp only [map_mul]
    have hTa : hz.z4jT (Ng := Ng) (S4B.z4iπ (hz.z4iSub Ng) a) := by rw [haπ]; exact hT
    have hcomm : hz.z4iLam * hz.z4iTau = hz.z4iTau * hz.z4iLam := by
      apply Subtype.ext
      show lam * tau = tau * lam
      rw [hz.tau_lam]
    have ha2 : a * a = 1 := by
      show (hz.z4iLam * hz.z4iTau) * (hz.z4iLam * hz.z4iTau) = 1
      exact z4j_mul_self_of_comm (z4j_lam_sq hz) (z4j_tau_sq hz) hcomm
    have ha1 : a ≠ 1 := by
      intro h
      exact z4jT_ne_one hz hN hTa (by rw [h, map_one])
    obtain ⟨g, hg⟩ := (z4jT_map_iff hz hN ha2 ha1).mp hTa
    exact hz.not_conj_t_lamtau g hg.symm
  · intro hT
    let a : ↥(ctxNQ t tau x₁ x₂ rho) := hz.z4iLam * hz.z4iT * hz.z4iTau
    have haπ : S4B.z4iπ (hz.z4iSub Ng) a = S4B.z4iπ (hz.z4iSub Ng) hz.z4iLam *
        S4B.z4iπ (hz.z4iSub Ng) hz.z4iT * S4B.z4iπ (hz.z4iSub Ng) hz.z4iTau := by
      show S4B.z4iπ (hz.z4iSub Ng) (hz.z4iLam * hz.z4iT * hz.z4iTau) = _
      simp only [map_mul]
    have hTa : hz.z4jT (Ng := Ng) (S4B.z4iπ (hz.z4iSub Ng) a) := by rw [haπ]; exact hT
    have ha2 : a * a = 1 := by
      apply Subtype.ext
      show (lam * t * tau) * (lam * t * tau) = (1 : G)
      exact z4j_prod3_sq hz.lam_mul_self hz.t_mul_self hz.tau_mul_self
        hz.t_lam_comm.symm hz.tau_lam.symm hz.t_comm_tau
    have ha1 : a ≠ 1 := by
      intro h
      exact z4jT_ne_one hz hN hTa (by rw [h, map_one])
    obtain ⟨g, hg⟩ := (z4jT_map_iff hz hN ha2 ha1).mp hTa
    obtain ⟨c, hcL, hctau⟩ := hz.tau_lam_conj_tau
    have hct : c * t = t * c := S4A.mem_invCent_iff.mp (S4A.L_le_invCent hz.hyp hcL)
    have hctau' : c * (t * tau) * c⁻¹ = lam * t * tau := by
      calc c * (t * tau) * c⁻¹ = (c * t * c⁻¹) * (c * tau * c⁻¹) := by group
        _ = t * (tau * lam) := by
              rw [show c * t * c⁻¹ = t from by rw [hct]; group, hctau]
        _ = lam * t * tau := by
              rw [hz.tau_lam]
              calc t * (lam * tau) = (t * lam) * tau := by group
                _ = (lam * t) * tau := by rw [hz.t_lam_comm]
                _ = lam * t * tau := rfl
    have hkey : (c⁻¹ * g) * t * (c⁻¹ * g)⁻¹ = t * tau := by
      calc (c⁻¹ * g) * t * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * t * g⁻¹) * c := by group
        _ = c⁻¹ * (lam * t * tau) * c := by rw [← hg]; rfl
        _ = t * tau := by rw [← hctau']; group
    exact hz.nPre.tau_ttau_not_conj.2 (c⁻¹ * g) hkey

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
