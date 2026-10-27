module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23A02

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
    CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore IsSubnormal)
namespace T7K
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7K
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}
variable [IsSimpleGroup G]

theorem hyp51At_of_commuting (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u
    e g) {c : G}
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hzc : z ≠ c)
    (hcB : c ∈ Subgroup.closure ({u * e, u, z} : Set G))
    (hBgen : Subgroup.closure ({u * e, u, z} : Set G) = Subgroup.closure ({z, u, c} : Set G))
    (hcomm : ∀ x : G, (x ∈ K ∨ x ∈ K') → x ∈ Subgroup.normalizer (W : Set G) → x * c = c * x) :
    Hyp51At (Subgroup.closure ({u * e, u, z} : Set G)) c := by
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', a, b, r, hR, hR', hRR', hRN, hR'N, ha, hb, haW, hbW, hab, haa, hbb, hrR, hr⟩ :=
    Q3T8.Asc77.T7K.exists_decomp hs hd
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x (Or.inl (hR.1 hx)) (hRN hx))
  have hR'c : R' ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x (Or.inr (hR'.1 hx)) (hR'N hx))
  have hMK : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c :=
    ⟨hKΩ, (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hc2' hKΩ).mpr ⟨R, hR, hRc⟩⟩
  have hMK' : K' ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c :=
    ⟨hK'Ω, (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hc2' hK'Ω).mpr ⟨R', hR',
        hR'c⟩⟩
  have haE : a ∈ Q3T8.Asc77.ExactLayer.exactCore c K :=
    ((Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hc2' hKΩ hMK.2).mpr ⟨hR, hRc⟩).1 ha
  have hbE : b ∈ Q3T8.Asc77.ExactLayer.exactCore c K' :=
    ((Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hc2' hK'Ω hMK'.2).mpr ⟨hR', hR'c⟩).1 hb
  have hdsup : u ∈ Q3T8.Asc77.ExactLayer.exactCore c K ⊔ Q3T8.Asc77.ExactLayer.exactCore c K' := by
    rw [hab]
    exact Subgroup.mul_mem_sup haE hbE
  exact Q3T8.Asc77.T7K.hyp51At_of_twin_inner hst hKΩ hK'Ω hs.hne hs.hz hzK' hMK hMK'
    (Q3T8.Asc77.T7K.B_isElemAbelian hs hd) (z_mem_B z u e) (u_mem_B z u e) hcB hBgen hc1 hzc hd.hu1
        hd.huz hd.hu2
    hdsup
omit [IsSimpleGroup G] in

theorem hyp51At_z
    [IsSimpleGroup G] (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K'
    W z u e g) :
    Hyp51At (Subgroup.closure ({u * e, u, z} : Set G)) z := by
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', a, b, r, hR, hR', hRR', hRN, hR'N, ha, hb, haW, hbW, hab, haa, hbb, hrR, hr⟩ :=
    Q3T8.Asc77.T7K.exists_decomp hs hd
  have he2' : IsPGroup 2 (Subgroup.zpowers e) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  have hRe : R ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_e hd (hRN hx))
  have hR'e : R' ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_e hd (hR'N hx))
  have heK : e ∈ trivialOnQuot K :=
    (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ he2' hKΩ).mpr ⟨R, hR, hRe⟩
  have heK' : e ∈ trivialOnQuot K' :=
    (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ he2' hK'Ω).mpr ⟨R', hR', hR'e⟩
  have hez : e ≠ z := fun h => Q3T8.Asc77.T7K.e_not_mem_sup hs hd (h ▸ Subgroup.mem_sup_left
      hs.hz.mem)
  have hxyB : a * b ∈ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [← hab]
    exact u_mem_B z u e
  exact Q3T8.Asc77.T7K.hyp51At_of_twin_vertex_z hst hKΩ hK'Ω hs.hz hzK'
      (Q3T8.Asc77.T7K.B_isElemAbelian hs hd) (z_mem_B z u e)
    (hR.1 ha) (hR'.1 hb) hxyB (by rw [← hab]; exact hd.hu1) (by rw [← hab]; exact hd.huz)
    (e_mem_B z u e) hd.he1 hez heK heK'

theorem hyp51_B (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    Hyp51 (Subgroup.closure ({u * e, u, z} : Set G)) := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hz2 : z * z = 1 := hs.hz.sq
  have hez : e ≠ z := fun h => Q3T8.Asc77.T7K.e_not_mem_sup hs hd (h ▸ Subgroup.mem_sup_left
      hs.hz.mem)
  have hcommK : ∀ x : G, (x ∈ K ∨ x ∈ K') → z * x = x * z := by
    rintro x (hx | hx)
    · exact hs.hz.commute_of_mem hx
    · exact hzK'.commute_of_mem hx
  have h51z := Q3T8.Asc77.T7K.hyp51At_z hs hd
  have h51e : Hyp51At (Subgroup.closure ({u * e, u, z} : Set G)) e :=
    Q3T8.Asc77.T7K.hyp51At_of_commuting hs hd hd.he2 hd.he1 (Ne.symm hez) (e_mem_B z u e)
      (closure_eq_e z u e) (fun x _ hx => comm_e hd hx)
  have hze2 : (z * e) * (z * e) = 1 := by
    have hce : z * e = e * z := comm_e_of_mem_W hd hd.hzW
    calc (z * e) * (z * e) = z * (e * z) * e := by group
      _ = z * (z * e) * e := by rw [← hce]
      _ = (z * z) * (e * e) := by group
      _ = 1 := by rw [hz2, hd.he2]; group
  have h51ze : Hyp51At (Subgroup.closure ({u * e, u, z} : Set G)) (z * e) := by
    refine Q3T8.Asc77.T7K.hyp51At_of_commuting hs hd hze2 ?_ ?_ (Subgroup.mul_mem _ (z_mem_B z u e)
      (e_mem_B z u e)) (closure_eq_ze z u e) ?_
    · intro h
      exact hez (by
        have : e = z⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [this]
        exact inv_eq_of_mul_eq_one_right hz2)
    · intro h
      exact hd.he1 (by simpa using h.symm)
    · intro x hx hxN
      calc x * (z * e) = (x * z) * e := by group
        _ = (z * x) * e := by rw [(hcommK x hx).symm]
        _ = z * (x * e) := by group
        _ = z * (e * x) := by rw [comm_e hd hxN]
        _ = (z * e) * x := by group
  obtain ⟨R, R', a, b, r, hR, hR', hRR', hRN, hR'N, ha, hb, haW, hbW, hab, haa, hbb, hrR, hr⟩ :=
    Q3T8.Asc77.T7K.exists_decomp hs hd
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := g_mem_normalizer hd
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hRN hrR
  have hgB := Q3T8.Asc77.T7K.mem_normalizer_B hs hd hgN
  have hrgB : r * g ∈ Subgroup.normalizer ((Subgroup.closure ({u * e, u, z} : Set G) :
      Subgroup G) : Set G) := Subgroup.mul_mem _ (Q3T8.Asc77.T7K.mem_normalizer_B hs hd hrN) hgB
  have hge : g * e * g⁻¹ = e := by
    rw [comm_e hd hgN]
    group
  have hre : r * e * r⁻¹ = e := by
    rw [comm_e hd hrN]
    group
  have hgz : g * z * g⁻¹ = u * e := hd.hgt
  have hgze : g * (z * e) * g⁻¹ = u := by
    calc g * (z * e) * g⁻¹ = (g * z * g⁻¹) * (g * e * g⁻¹) := by group
      _ = (u * e) * e := by rw [hgz, hge]
      _ = u * (e * e) := by group
      _ = u := by rw [hd.he2]; group
  have hcU : u * e = e * u := comm_e_of_mem_W hd hd.huW
  refine hyp51_of_orbitReps (Q3T8.Asc77.T7K.B_isElemAbelian hs hd) (Q3T8.Asc77.T7K.B_natCard hs hd)
      (R := {z, z * e, e})
    ?_ ?_
  · intro c hc
    rcases hc with rfl | rfl | rfl
    · exact h51z
    · exact h51ze
    · exact h51e
  · intro c hc hc1
    rcases mem_cases_of_commuting_involutions hd.hu2 hz2 hd.he2 (Q3T8.Asc77.T7K.comm_uz hs hd)
      (comm_e_of_mem_W hd hd.huW) (comm_e_of_mem_W hd hd.hzW) hc with
      h | h | h | h | h | h | h | h
    · exact absurd h hc1
    · exact ⟨z, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨z * e, by simp, g, hgB, by rw [h, hgze]⟩
    · refine ⟨z * e, by simp, r * g, hrgB, ?_⟩
      calc c = u * z := h
        _ = r * u * r⁻¹ := hr.symm
        _ = r * (g * (z * e) * g⁻¹) * r⁻¹ := by rw [hgze]
        _ = r * g * (z * e) * (r * g)⁻¹ := by group
    · exact ⟨e, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨z * e, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨z, by simp, g, hgB, by rw [h, hgz]⟩
    · refine ⟨z, by simp, r * g, hrgB, ?_⟩
      calc c = u * z * e := h
        _ = (r * u * r⁻¹) * (r * e * r⁻¹) := by rw [hr, hre]
        _ = r * (u * e) * r⁻¹ := by group
        _ = r * (g * z * g⁻¹) * r⁻¹ := by rw [hgz]
        _ = r * g * z * (r * g)⁻¹ := by group

theorem c23_5X_one (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u, z} : Set G)))) ∧
      ∀ A : Subgroup G, A ≤ Subgroup.closure ({u * e, u, z} : Set G) → IsElemAbelian2 A 2 →
        alphaOf A = alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hD : IsElemAbelian2 (Subgroup.closure ({u, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hd.hu2 hs.hz.sq hd.hu1 hs.hz.ne_one hd.huz
        (Q3T8.Asc77.T7K.comm_uz hs hd)
  have hDB : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact u_mem_B z x e
    · exact z_mem_B x u e
  exact lemma54_odd_and_eq (Q3T8.Asc77.T7K.hyp51_B hs hd) hDB hD
end T7K
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7K
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7K
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

theorem c23_5X_one_proved (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e
    g) :
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u, z} : Set G)))) ∧
      ∀ A : Subgroup G, A ≤ Subgroup.closure ({u * e, u, z} : Set G) → IsElemAbelian2 A 2 →
        alphaOf A = alphaOf (Subgroup.closure ({u, z} : Set G)) :=
  Q3T8.Asc77.T7K.c23_5X_one hs hd
end T7K
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
    CFSG.ClassicalInvolution.Asc77.ExactLayer

@[expose] def C23_5X_type
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23b Ω K K' W z u e g →
      (u * e ∈ zStarOf (ExactLayer.exactLayer Ω u) ∨ Q3T8.Asc77.LayerOrthType Ω u 5 true ∨
        Q3T8.Asc77.LayerOrthType Ω u 6 (!piSign 3 1))

@[expose] def C23_GammaU
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23Setting Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        Subgroup.centralizer ({u} : Set G) ≤
          gamma2 (Subgroup.closure {u * e, u, z}) (Subgroup.centralizer ({u} : Set G))
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
    CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal

theorem c23_9_ofK (h2 : Q3T8.Asc77.C23_2) (h4 : Q3T8.Asc77.C23_4X) (h5 : Q3T8.Asc77.C23_5X_type)
    (h7 : Q3T8.Asc77.C23_7)
    (hΓu : Q3T8.Asc77.C23_GammaU) (hnoZ : Q3T8.Asc77.C23_9_noZX) (hgen : Q3T8.Asc77.C23_9_genX) :
        Q3T8.Asc77.C23_9X := by
  intro G _ _ _ Ω K K' W z u e g h
  have hE : Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1) :=
    (h4 G Ω K K' W z u e g h).resolve_left (h7 G Ω K K' W z u e g h)
  have hset : Q3T8.Asc77.Hyp23Setting Ω K K' z := h.std.setting
  obtain ⟨hodd, halpha⟩ := Q3T8.Asc77.T7K.c23_5X_one_proved hset h.data
  have hY : u * e ∈ zStarOf (ExactLayer.exactLayer Ω u) ∨ Q3T8.Asc77.LayerOrthType Ω u 5 true ∨
      Q3T8.Asc77.LayerOrthType Ω u 6 (!piSign 3 1) := h5 G Ω K K' W z u e g h
  have hY' : Q3T8.Asc77.LayerOrthType Ω u 5 true ∨ Q3T8.Asc77.LayerOrthType Ω u 6 (!piSign 3 1) :=
    hY.resolve_left (hnoZ G Ω K K' W z u e g hset h.data hE)
  have hΓz := Q3T8.Asc77.T7K.centralizer_z_le_gamma2 hset h.data
  have hΓu' := hΓu G Ω K K' W z u e g hset h.data
  have hG := h2 G Ω K K' z h.std W h.hW h.hzW u h.hu h.huW h.hu1 h.huz h.hu2
  have hN : Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hG]
    exact sup_le (hΓu'.trans (gamma2_le_normalizer_alphaOf halpha _))
      (hΓz.trans (gamma2_le_normalizer_alphaOf halpha _))
  have hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ :=
    T7B.eq_bot_of_normalizer_eq_top hodd hN (T7B.two_dvd_natCard h.std.1.hz)
  exact ⟨⟨hα, hgen G Ω K K' W z u e g hset h.data hE hY'⟩, hE, hY'⟩
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace T7L
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7L
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z u e g : G}
section Twins
omit [IsSimpleGroup G] in

theorem twin_le_trivialOnQuot
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω) {J J' : Subgroup G} {w : G}
    (hJ : J ∈ Ω) (hJ' : J' ∈ Ω) (hne : J ≠ J') (hz : IsUniqueInvolution J w)
    (hz' : IsUniqueInvolution J' w) : J ≤ trivialOnQuot J' := by
  have h4 := hΩ.omega4 J hJ J' hJ' hne
  have hmem : w ∈ J ⊓ J' := ⟨hz.mem, hz'.mem⟩
  have hz2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hdvd : 2 ∣ Nat.card ↥(J ⊓ J') := by
    have := Subgroup.orderOf_dvd_natCard (J ⊓ J') hmem
    rwa [hz2] at this
  have hpos : Nat.card ↥(J ⊓ J') ≠ 0 := Nat.card_pos.ne'
  have h1 : 1 ≤ padicValNat 2 (Nat.card ↥(J ⊓ J')) :=
    (padicValNat_dvd_iff_le (p := 2) hpos).mp (by simpa using hdvd)
  have heq : padicValNat 2 (Nat.card ↥(J ⊓ J')) = 1 := le_antisymm h4.1 h1
  exact le_trivialOnQuot_of_commutator_le ((h4.2 heq).trans inf_le_right)
omit [IsSimpleGroup G] in

theorem not_mem_tqMembers_of_mul
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω)
    {J : Subgroup G} (hJ : J ∈ Ω) {w a b c : G} (hw : IsUniqueInvolution J w) (haJ : a ∈ J)
    (ha4 : orderOf a = 4) (hb : b ∈ trivialOnQuot J) (hc : c = a * b) : J ∉
        Q3T8.Asc77.ExactLayer.tqMembers Ω c := by
  intro hJt
  have hcJ : c ∈ trivialOnQuot J := hJt.2
  have ha : a ∈ trivialOnQuot J := by
    have : a = c * b⁻¹ := by rw [hc]; group
    rw [this]
    exact Subgroup.mul_mem _ hcJ (Subgroup.inv_mem _ hb)
  have hcomm : ∀ y ∈ J, ⁅a, y⁆ ∈ oddCoreOf J := fun y hy =>
    (mem_trivialOnQuot_iff.mp ha).2 y hy
  have ha2 : IsPGroup 2 (Subgroup.zpowers a) := T7A.isPGroup_zpowers_of_orderOf_four ha4
  rcases hΩ.center_two hJ hw a haJ ha2 hcomm with h | h
  · rw [h, orderOf_one] at ha4
    omega
  · rw [h] at ha4
    have : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw.sq) hw.ne_one
    omega
end Twins
section Frame

theorem exists_uFrame
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    ∃ (R₂ R₂' : Subgroup G) (a₂ b₂ v' : G),
      conjSub g K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u ∧ conjSub g K' ∈
          Q3T8.Asc77.ExactLayer.tqMembers Ω u ∧
      IsSylow2In R₂ (Q3T8.Asc77.ExactLayer.exactCore u (conjSub g K)) ∧ IsSylow2In R₂'
          (Q3T8.Asc77.ExactLayer.exactCore u (conjSub g K')) ∧
      Commutes R₂ R₂' ∧ a₂ ∈ R₂ ∧ b₂ ∈ R₂' ∧ a₂ * a₂ = u * e ∧ b₂ * b₂ = u * e ∧
      (v' = a₂ * b₂ ∨ v' = a₂ * b₂ * (u * e)) ∧ (z = v' ∨ z = u * v') := by
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', a, b, r, hR, hR', hRR', hRN, hR'N, haR, hbR', haW, hbW, hab, haa, hbb, hrR, hr⟩ :=
    Q3T8.Asc77.T7K.exists_decomp hs hd
  have hu2' : IsPGroup 2 (Subgroup.zpowers u) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have hz2 : z * z = 1 := hzK.sq
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := T7K.g_mem_normalizer hd
  have hge : g * e * g⁻¹ = e := by
    rw [T7K.comm_e hd hgN]
    group
  have hgze : g * (z * e) * g⁻¹ = u := by
    calc g * (z * e) * g⁻¹ = (g * z * g⁻¹) * (g * e * g⁻¹) := by group
      _ = (u * e) * e := by rw [hd.hgt, hge]
      _ = u * (e * e) := by group
      _ = u := by rw [hd.he2, mul_one]

  have hRze : ∀ x ∈ R, x * (z * e) = (z * e) * x := by
    intro x hx
    have h1 : x * z = z * x := (hzK.commute_of_mem (hR.1 hx)).symm
    have h2 : x * e = e * x := T7K.comm_e hd (hRN hx)
    calc x * (z * e) = (x * z) * e := by rw [mul_assoc]
      _ = (z * x) * e := by rw [h1]
      _ = z * (x * e) := by rw [mul_assoc]
      _ = z * (e * x) := by rw [h2]
      _ = (z * e) * x := by rw [mul_assoc]
  have hR'ze : ∀ x ∈ R', x * (z * e) = (z * e) * x := by
    intro x hx
    have h1 : x * z = z * x := (hzK'.commute_of_mem (hR'.1 hx)).symm
    have h2 : x * e = e * x := T7K.comm_e hd (hR'N hx)
    calc x * (z * e) = (x * z) * e := by rw [mul_assoc]
      _ = (z * x) * e := by rw [h1]
      _ = z * (x * e) := by rw [mul_assoc]
      _ = z * (e * x) := by rw [h2]
      _ = (z * e) * x := by rw [mul_assoc]

  have hconjc : ∀ (R₀ : Subgroup G), (∀ x ∈ R₀, x * (z * e) = (z * e) * x) →
      conjSub g R₀ ≤ Subgroup.centralizer ({u} : Set G) := by
    intro R₀ hR₀ y hy
    rw [mem_conjSub_iff] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hR₀ _ hy
    refine Eq.symm ?_
    calc u * y = (g * (z * e) * g⁻¹) * y := by rw [hgze]
      _ = g * ((z * e) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (z * e)) * g⁻¹ := by rw [← h1]
      _ = y * (g * (z * e) * g⁻¹) := by group
      _ = y * u := by rw [hgze]
  have hRc := hconjc R hRze
  have hR'c := hconjc R' hR'ze
  have hK₂ : conjSub g K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
    (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hu2').mpr
      ⟨hΩ.conjInvariant g K hKΩ, conjSub g R, hR.conj g, hRc⟩
  have hK₂' : conjSub g K' ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
    (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hu2').mpr
      ⟨hΩ.conjInvariant g K' hK'Ω, conjSub g R', hR'.conj g, hR'c⟩
  have hS₂ : IsSylow2In (conjSub g R) (Q3T8.Asc77.ExactLayer.exactCore u (conjSub g K)) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hu2' (hΩ.conjInvariant g K hKΩ) hK₂.2).mpr
        ⟨hR.conj g, hRc⟩
  have hS₂' : IsSylow2In (conjSub g R') (Q3T8.Asc77.ExactLayer.exactCore u (conjSub g K')) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hu2' (hΩ.conjInvariant g K' hK'Ω) hK₂'.2).mpr
      ⟨hR'.conj g, hR'c⟩
  have hcomm : Commutes (conjSub g R) (conjSub g R') := by
    intro x hx y hy
    rw [mem_conjSub_iff] at hx hy
    have h1 := hRR' _ hx _ hy
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = y * x := by group
  have ha₂ : g * a * g⁻¹ ∈ conjSub g R := conj_mem_conjSub haR
  have hb₂ : g * b * g⁻¹ ∈ conjSub g R' := conj_mem_conjSub hbR'
  have ha₂sq : (g * a * g⁻¹) * (g * a * g⁻¹) = u * e := by
    calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [haa]
      _ = u * e := hd.hgt
  have hb₂sq : (g * b * g⁻¹) * (g * b * g⁻¹) = u * e := by
    calc (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hbb]
      _ = u * e := hd.hgt
  have hv1 : g * u * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by rw [hab]; group

  have hcuz : u * z = z * u := Q3T8.Asc77.T7K.comm_uz hs hd
  have hcue : u * e = e * u := T7K.comm_e_of_mem_W hd hd.huW
  have hv1B : g * u * g⁻¹ ∈ Subgroup.closure ({u * e, u, z} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (Q3T8.Asc77.T7K.mem_normalizer_B hs hd hgN) u).mp (T7K.u_mem_B
        z u e)
  have hinj : ∀ x y : G, g * x * g⁻¹ = g * y * g⁻¹ → x = y := fun x y h =>
    mul_left_cancel (mul_right_cancel h)
  have hzsup : z ∈ K ⊔ K' := Subgroup.mem_sup_left hzK.mem
  have heK : ∀ x : G, x ∈ K ⊔ K' → e = x → False := fun x hx hex =>
    Q3T8.Asc77.T7K.e_not_mem_sup hs hd (hex ▸ hx)
  have hKe : u = z * e → False := fun h => by
    refine Q3T8.Asc77.T7K.e_not_mem_sup hs hd ?_
    have : e = z * u := by rw [h, ← mul_assoc, hz2, one_mul]
    rw [this]
    exact (K ⊔ K').mul_mem hzsup hd.hu
  obtain ⟨i1, i2, i3, i4⟩ := alg_aux hd.hu2 hcuz hcue hd.he2
  rcases T7K.mem_cases_of_commuting_involutions hd.hu2 hz2 hd.he2 hcuz hcue
    (T7K.comm_e_of_mem_W hd hd.hzW) hv1B with h | h | h | h | h | h | h | h
  · exact absurd (hinj u 1 (by rw [h]; group)) hd.hu1
  · refine ⟨_, _, _, _, z, hK₂, hK₂', hS₂, hS₂', hcomm, ha₂, hb₂, ha₂sq, hb₂sq, Or.inl ?_,
      Or.inl rfl⟩
    rw [← hv1, h]
  · exact absurd (hKe (hinj u (z * e) (by rw [h, hgze]))) id
  · refine ⟨_, _, _, _, (g * a * g⁻¹) * (g * b * g⁻¹), hK₂, hK₂', hS₂, hS₂', hcomm, ha₂, hb₂,
      ha₂sq, hb₂sq, Or.inl rfl, Or.inr ?_⟩
    rw [← hv1, h]
    exact i3.symm
  · exact absurd (hinj u e (by rw [h, hge])) (fun h' => heK u hd.hu h'.symm)
  · refine ⟨_, _, _, _, ((g * a * g⁻¹) * (g * b * g⁻¹)) * (u * e), hK₂, hK₂', hS₂, hS₂', hcomm, ha₂,
      hb₂, ha₂sq, hb₂sq, Or.inr rfl, Or.inr ?_⟩
    rw [← hv1, h]
    exact i4.symm
  · exact absurd (hinj u z (by rw [h, hd.hgt])) hd.huz
  · refine ⟨_, _, _, _, ((g * a * g⁻¹) * (g * b * g⁻¹)) * (u * e), hK₂, hK₂', hS₂, hS₂', hcomm, ha₂,
      hb₂, ha₂sq, hb₂sq, Or.inr rfl, Or.inl ?_⟩
    rw [← hv1, h]
    exact i2.symm
omit [IsSimpleGroup G] in

theorem not_mem_tqMembers_u
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e
    g) :
    K ∉ Q3T8.Asc77.ExactLayer.tqMembers Ω u ∧ K' ∉ Q3T8.Asc77.ExactLayer.tqMembers Ω u := by
  have hst := hs.stand
  have hΩ : Q3T8.Asc77.HypOmegaMod Ω := hst.hyp
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', a, b, r, hR, hR', hRR', hRN, hR'N, haR, hbR', haW, hbW, hab, haa, hbb, hrR, hr⟩ :=
    Q3T8.Asc77.T7K.exists_decomp hs hd
  have ha4 : orderOf a = 4 := orderOf_four_of_sq haa hzK.ne_one hzK.sq
  have hb4 : orderOf b = 4 := orderOf_four_of_sq hbb hzK.ne_one hzK.sq
  have hbK' : b ∈ K' := hR'.1 hbR'
  have haK : a ∈ K := hR.1 haR
  have hbt : b ∈ trivialOnQuot K :=
    Q3T8.Asc77.T7L.twin_le_trivialOnQuot hΩ hK'Ω hKΩ hs.hne hzK' hzK hbK'
  have hat : a ∈ trivialOnQuot K' :=
    Q3T8.Asc77.T7L.twin_le_trivialOnQuot hΩ hKΩ hK'Ω hs.hne.symm hzK hzK' haK
  refine ⟨Q3T8.Asc77.T7L.not_mem_tqMembers_of_mul hΩ hKΩ hzK haK ha4 hbt hab, ?_⟩
  exact Q3T8.Asc77.T7L.not_mem_tqMembers_of_mul hΩ hK'Ω hzK' hbK' hb4 hat
    (by rw [hab]; exact hRR' a haR b hbR')
end Frame
end T7L
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace T7L
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7L
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
section NoMember

theorem no_member_commutes
    (hΩ : Q3T7M.HM Ω)
    {K K' : Subgroup G} {z u v' : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hperp : KPerp Ω K = {K, K'}) (hKt : K ∉ Q3T8.Asc77.ExactLayer.tqMembers Ω u) (hK't : K' ∉
        Q3T8.Asc77.ExactLayer.tqMembers Ω u)
    (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hzv : ∀ y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u, z * y * z⁻¹ = v' * y * v'⁻¹)
    {M : Subgroup G} (hM : M ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u) :
    ∃ m ∈ Q3T8.Asc77.ExactLayer.exactCore u M, ⁅v', m⁆ ∉ oddCoreOf
        (Q3T8.Asc77.ExactLayer.exactLayer Ω u) := by
  by_contra hcon
  push Not at hcon
  have hu2' : IsPGroup 2 (Subgroup.zpowers u) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hu2
  obtain ⟨hMΩ, R₀, hR₀, hR₀c⟩ := (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hu2').mp
      hM
  have hR₀core : IsSylow2In R₀ (Q3T8.Asc77.ExactLayer.exactCore u M) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hu2' hMΩ hM.2).mpr ⟨hR₀, hR₀c⟩
  have hR₀Y : R₀ ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω u := hR₀core.1.trans
      (Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hM)
  have hzC : z ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzu
  have hzY : z ∈ Subgroup.normalizer ((Q3T8.Asc77.ExactLayer.exactLayer Ω u : Subgroup G) : Set G)
      :=
    mem_normalizer_iff_conjSub_eq.mpr (Q3T8.Asc77.ExactLayer.conjSub_exactLayer hΩ.conjInvariant
        hzC)
  have hNodd : Odd (Nat.card ↥(oddCoreOf (Q3T8.Asc77.ExactLayer.exactLayer Ω u))) :=
      oddCoreOf_odd_natCard _
  have hRN : R₀ ≤ Subgroup.normalizer (oddCoreOf (Q3T8.Asc77.ExactLayer.exactLayer Ω u) : Set G) :=
      fun r hr =>
    normalizer_oddCoreIn (Q3T8.Asc77.ExactLayer.exactLayer Ω u) (hR₀Y hr)
  obtain ⟨n, hn, hnR⟩ := exists_conj_centralizes hz.sq hNodd hR₀core.2.1 hRN
    (mem_normalizer_oddCoreOf hzY) (fun r hr => by
      have h1 := hzv r (hR₀Y hr)
      have h2 : ⁅z, r⁆ = ⁅v', r⁆ := by
        simp only [commutatorElement_def]
        rw [h1]
      rw [h2]
      exact hcon r (hR₀core.1 hr))
  have hnY : n ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u := oddCoreIn_le _ hn
  have hnC : n ∈ Subgroup.centralizer ({u} : Set G) :=
      Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u hnY
  have hM₁ : conjSub n M ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
      Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hnC hM
  have hS : IsSylow2In (conjSub n R₀) (conjSub n M) := hR₀.conj n
  have hRset : conjSub n R₀ ∈ RSet Ω := mem_RSet_of_isSylow2In hM₁.1 hS
  have hne : conjSub n M ≠ K := fun h => hKt (h ▸ hM₁)
  have hnbr : conjSub n M ∈ omegaNbr Ω K :=
    Q3T8.Asc77.mem_omegaNbr_of_sylow_le_centralizer hΩ hK hM₁.1 hne hz hS hRset hnR
  have hperp' : conjSub n M ∈ KPerp Ω K := Or.inr hnbr
  rw [hperp] at hperp'
  rcases hperp' with h | h
  · exact hne h
  · exact hK't (h ▸ hM₁)
end NoMember
end T7L
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement
namespace T7L
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7L
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}
variable [IsSimpleGroup G]

theorem layer_u_frame
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    ∃ (a₂ b₂ v' : G) (ha₂Y : a₂ ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u) (hb₂Y : b₂ ∈
        Q3T8.Asc77.ExactLayer.exactLayer Ω u)
      (hv'Y : v' ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u) (htY : u * e ∈
          Q3T8.Asc77.ExactLayer.exactLayer Ω u),
      (v' = z ∨ v' = u * z) ∧
      Q3T8.Asc77.GenSection (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u)) ∧
      Nat.card (↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) ⧸ classicalInvolutionOddCore
          ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u)) < Nat.card G ∧
      TwinSect (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u)) (Q3T8.Asc77.T7H.exactImg Ω
          u (conjSub g K))
        (Q3T8.Asc77.T7H.exactImg Ω u (conjSub g K')) (Q3T8.Asc77.T7H.toBar Ω u (u * e) htY)
            (Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y)
        (Q3T8.Asc77.T7H.toBar Ω u b₂ hb₂Y) (Q3T8.Asc77.T7H.toBar Ω u v' hv'Y) ∧
      (∀ h ∈ Subgroup.centralizer ({u} : Set G), ∃ B ∈ oddQuotientFamily
          (Q3T8.Asc77.ExactLayer.exactPair Ω u),
        ∃ hmem : h * (u * e) * h⁻¹ ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u,
          IsUniqueInvolution B (Q3T8.Asc77.T7H.toBar Ω u (h * (u * e) * h⁻¹) hmem)) := by
  classical
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hzK : IsUniqueInvolution K z := hs.hz
  have hcpg : IsPGroup 2 (Subgroup.zpowers u) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  obtain ⟨R₂, R₂', a₂, b₂, v', hK₂, hK₂', hS₂, hS₂', hcomm₂, ha₂, hb₂, ha₂sq, hb₂sq, hv'def,
    hzv'⟩ := Q3T8.Asc77.T7L.exists_uFrame hs hd
  obtain ⟨hKnt, hK'nt⟩ := Q3T8.Asc77.T7L.not_mem_tqMembers_u hs hd
  have hzK₂ : IsUniqueInvolution (conjSub g K) (u * e) := by
    have := hzK.conj g
    rwa [hd.hgt] at this
  have hzK₂' : IsUniqueInvolution (conjSub g K') (u * e) := by
    have := (isUniqueInvolution_of_mem_twinSet hs.hz hs.hK').conj g
    rwa [hd.hgt] at this
  have hperp₂ : KPerp Ω (conjSub g K) = {conjSub g K, conjSub g K'} :=
    kPerp_conj_pair hΩ.conjInvariant hs.perp g
  have hperp' : KPerp Ω K' = {K', K} := by rw [hs.perp_of_twin hs.hK', Set.pair_comm]
  have hperp₂' : KPerp Ω (conjSub g K') = {conjSub g K', conjSub g K} :=
    kPerp_conj_pair hΩ.conjInvariant hperp' g
  set Y := Q3T8.Asc77.ExactLayer.exactLayer Ω u with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : Q3T7M.HM (Q3T8.Asc77.ExactLayer.exactPair Ω u) :=
      Q3T8.Asc77.ExactLayer.hypOmegaMod_exactPair hΩ hcpg
  have hΦ : Q3T7M.HM (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u)) :=
    Q3T8.Asc77.oddQuotHyp ↥Y (Q3T8.Asc77.ExactLayer.exactPair Ω u) hΛ N₀ hN₀odd

  have ht₂ : u * e ∈ Q3T8.Asc77.ExactLayer.exactCore u (conjSub g K) :=
    (Q3T8.Asc77.T7H.isUniqueInvolution_exactCore hΩ hcpg hK₂ hzK₂).mem
  have htY : u * e ∈ Y := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK₂ ht₂
  have ha₂c : a₂ ∈ Q3T8.Asc77.ExactLayer.exactCore u (conjSub g K) := hS₂.1 ha₂
  have hb₂c : b₂ ∈ Q3T8.Asc77.ExactLayer.exactCore u (conjSub g K') := hS₂'.1 hb₂
  have ha₂Y : a₂ ∈ Y := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK₂ ha₂c
  have hb₂Y : b₂ ∈ Y := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK₂' hb₂c
  have hv'Y : v' ∈ Y := by
    rcases hv'def with h | h
    · rw [h]
      exact Y.mul_mem ha₂Y hb₂Y
    · rw [h]
      exact Y.mul_mem (Y.mul_mem ha₂Y hb₂Y) htY
  have hzu : z * u = u * z := (Q3T8.Asc77.T7K.comm_uz hs hd).symm
  have hzv : ∀ y ∈ Y, z * y * z⁻¹ = v' * y * v'⁻¹ := by
    intro y hy
    rcases hzv' with h | h
    · rw [h]
    · have hw : v' * y * v'⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hv'Y hy) (Y.inv_mem hv'Y)
      have hcw : (v' * y * v'⁻¹) * u = u * (v' * y * v'⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer
            Ω u hw)
      rw [h]
      calc u * v' * y * (u * v')⁻¹ = u * (v' * y * v'⁻¹) * u⁻¹ := by group
        _ = v' * y * v'⁻¹ := by rw [← hcw]; group

  have hA : Q3T8.Asc77.T7H.exactImg Ω u (conjSub g K) ∈ oddQuotientFamily
      (Q3T8.Asc77.ExactLayer.exactPair Ω u) :=
    Q3T8.Asc77.T7H.exactImg_mem hK₂
  have hA' : Q3T8.Asc77.T7H.exactImg Ω u (conjSub g K') ∈ oddQuotientFamily
      (Q3T8.Asc77.ExactLayer.exactPair Ω u) :=
    Q3T8.Asc77.T7H.exactImg_mem hK₂'
  have hzA := Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hK₂ hzK₂ htY
  have hzA' := Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hK₂' hzK₂' htY
  have hne : Q3T8.Asc77.T7H.exactImg Ω u (conjSub g K) ≠ Q3T8.Asc77.T7H.exactImg Ω u (conjSub g K')
      := by
    refine Q3T8.Asc77.map_ne_of_commutes_sylow (N := N₀) hΦ hN₀odd
      (M₁ := (Q3T8.Asc77.ExactLayer.exactCore u (conjSub g K)).subgroupOf Y)
      (M₂ := (Q3T8.Asc77.ExactLayer.exactCore u (conjSub g K')).subgroupOf Y)
      (V₁ := R₂.subgroupOf Y) (V₂ := R₂'.subgroupOf Y)
      ⟨_, Q3T8.Asc77.ExactLayer.exactCore_mem_exactFamily hK₂,
          Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK₂, rfl⟩
      (hS₂.subgroupOf (Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK₂))
      (hS₂'.subgroupOf (Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK₂')) ?_
    intro x hx y hy
    exact Subtype.ext (hcomm₂ x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  have hnbA : ∀ M ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u),
      M ∈ omegaNbr (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u))
          (Q3T8.Asc77.T7H.exactImg Ω u (conjSub g K)) →
        M = Q3T8.Asc77.T7H.exactImg Ω u (conjSub g K') := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := Q3T8.Asc77.T7H.exists_exactImg_of_mem hM
    exact Q3T8.Asc77.T7H.exactImg_nbr_eq hΩ hcpg hK₂ hperp₂ hJ hMn
  have hnbA' : ∀ M ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u),
      M ∈ omegaNbr (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u))
          (Q3T8.Asc77.T7H.exactImg Ω u (conjSub g K')) →
        M = Q3T8.Asc77.T7H.exactImg Ω u (conjSub g K) := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := Q3T8.Asc77.T7H.exists_exactImg_of_mem hM
    exact Q3T8.Asc77.T7H.exactImg_nbr_eq hΩ hcpg hK₂' hperp₂' hJ hMn
  have hgen : omegaGen (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u)) = ⊤ :=
    omegaGen_quotFamily_eq_top (Q3T8.Asc77.ExactLayer.exactPair Ω u) N₀
      (omegaGen_restrictFamily_eq_top (Q3T8.Asc77.ExactLayer.exactFamily Ω u) Y
          (Q3T8.Asc77.ExactLayer.exactLayer_eq_iSup Ω u).symm)
  have hAΩ : ∀ M ∈ Ω, AEmpty Ω M := hst.aEmpty
  have hAΛ : ∀ L ∈ Q3T8.Asc77.ExactLayer.exactPair Ω u, AEmpty (Q3T8.Asc77.ExactLayer.exactPair Ω
      u) L := by
    have h0 := Q3T8.Asc77.aEmpty_exactPair hΩ hAΩ hcpg
    have e0 : centralizingMembers (Q3T8.Asc77.ExactLayer.exactFamily Ω u) {u} =
        Q3T8.Asc77.ExactLayer.exactFamily Ω u :=
      Q3T8.Asc77.ExactLayer.centMembers_exactFamily Ω u
    rw [e0] at h0
    exact h0
  have hAΦ : ∀ L ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u),
      AEmpty (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u)) L :=
    Q3T8.Asc77.aEmpty_quotFamily hΛ hΦ hN₀odd hAΛ
  have hnc : ¬ ({u} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    obtain ⟨z₀, hz₀⟩ := hΩ.classical K hKΩ
    obtain ⟨x, -, y, -, hxy⟩ := Q3T8.Asc77.ih8_exists_noncomm hz₀
    have hucen : u ∈ Subgroup.center G := hsub (Set.mem_singleton u)
    exact hd.hu1 (T7B.eq_one_of_central ⟨x, y, hxy⟩
      (fun g' => Subgroup.mem_center_iff.mp hucen g'))
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    have h2 : Nat.card ↥Y < Nat.card G := Q3T8.Asc77.ExactLayer.card_exactLayer_lt hnc
    omega

  have haB : Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y ∈ Q3T8.Asc77.T7H.exactImg Ω u (conjSub g K) :=
      Q3T8.Asc77.T7H.mem_exactImg ha₂c ha₂Y
  have hbB : Q3T8.Asc77.T7H.toBar Ω u b₂ hb₂Y ∈ Q3T8.Asc77.T7H.exactImg Ω u (conjSub g K') :=
    Q3T8.Asc77.T7H.mem_exactImg hb₂c hb₂Y
  have haBsq : Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y * Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y =
      Q3T8.Asc77.T7H.toBar Ω u (u * e) htY := by
    have h1 : (⟨a₂, ha₂Y⟩ : ↥Y) * ⟨a₂, ha₂Y⟩ = ⟨u * e, htY⟩ := Subtype.ext ha₂sq
    unfold Q3T8.Asc77.T7H.toBar
    rw [← map_mul, h1]
  have hbBsq : Q3T8.Asc77.T7H.toBar Ω u b₂ hb₂Y * Q3T8.Asc77.T7H.toBar Ω u b₂ hb₂Y =
      Q3T8.Asc77.T7H.toBar Ω u (u * e) htY := by
    have h1 : (⟨b₂, hb₂Y⟩ : ↥Y) * ⟨b₂, hb₂Y⟩ = ⟨u * e, htY⟩ := Subtype.ext hb₂sq
    unfold Q3T8.Asc77.T7H.toBar
    rw [← map_mul, h1]
  have hzB2 : Q3T8.Asc77.T7H.toBar Ω u (u * e) htY * Q3T8.Asc77.T7H.toBar Ω u (u * e) htY = 1 :=
      hzA.sq
  have hainv : (Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y)⁻¹ =
      Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y * Q3T8.Asc77.T7H.toBar Ω u (u * e) htY := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y * (Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y *
        Q3T8.Asc77.T7H.toBar Ω u (u * e) htY)
        = (Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y * Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y) *
            Q3T8.Asc77.T7H.toBar Ω u (u * e) htY := by
          rw [mul_assoc]
      _ = 1 := by rw [haBsq, hzB2]
  have hw : Q3T8.Asc77.T7H.toBar Ω u v' hv'Y = Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y *
      Q3T8.Asc77.T7H.toBar Ω u b₂ hb₂Y ∨
      Q3T8.Asc77.T7H.toBar Ω u v' hv'Y = (Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y)⁻¹ *
          Q3T8.Asc77.T7H.toBar Ω u b₂ hb₂Y := by
    rcases hv'def with h | h
    · left
      subst h
      exact Q3T8.Asc77.T7H.toBar_mul ha₂Y hb₂Y
    · right
      subst h
      have h1 := Q3T8.Asc77.T7H.toBar_mul (Y.mul_mem ha₂Y hb₂Y) htY
      have h2 := Q3T8.Asc77.T7H.toBar_mul ha₂Y hb₂Y
      rw [h1, h2, hainv]
      have hc : Q3T8.Asc77.T7H.toBar Ω u (u * e) htY * Q3T8.Asc77.T7H.toBar Ω u b₂ hb₂Y =
          Q3T8.Asc77.T7H.toBar Ω u b₂ hb₂Y * Q3T8.Asc77.T7H.toBar Ω u (u * e) htY :=
        hzA'.commute_of_mem hbB
      calc Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y * Q3T8.Asc77.T7H.toBar Ω u b₂ hb₂Y *
          Q3T8.Asc77.T7H.toBar Ω u (u * e) htY
          = Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y * (Q3T8.Asc77.T7H.toBar Ω u b₂ hb₂Y *
              Q3T8.Asc77.T7H.toBar Ω u (u * e) htY) := by
            rw [mul_assoc]
        _ = Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y * (Q3T8.Asc77.T7H.toBar Ω u (u * e) htY *
            Q3T8.Asc77.T7H.toBar Ω u b₂ hb₂Y) := by
            rw [hc]
        _ = Q3T8.Asc77.T7H.toBar Ω u a₂ ha₂Y * Q3T8.Asc77.T7H.toBar Ω u (u * e) htY *
            Q3T8.Asc77.T7H.toBar Ω u b₂ hb₂Y := by
            rw [mul_assoc]

  have hF : ∀ L ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u),
      ∃ m ∈ L, Q3T8.Asc77.T7H.toBar Ω u v' hv'Y * m ≠ m * Q3T8.Asc77.T7H.toBar Ω u v' hv'Y := by
    intro L hL
    obtain ⟨J, hJ, rfl⟩ := Q3T8.Asc77.T7H.exists_exactImg_of_mem hL
    obtain ⟨m, hm, hmn⟩ := Q3T8.Asc77.T7L.no_member_commutes hΩ hKΩ hzK hs.perp hKnt hK'nt hd.hu2
        hzu
      hzv hJ
    have hmY : m ∈ Y := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hJ hm
    refine ⟨Q3T8.Asc77.T7H.toBar Ω u m hmY, Q3T8.Asc77.T7H.mem_exactImg hm hmY, fun h => hmn ?_⟩
    have h1 : (⟨v', hv'Y⟩ : ↥Y) * ⟨m, hmY⟩ * ((⟨m, hmY⟩ : ↥Y) * ⟨v', hv'Y⟩)⁻¹ ∈ N₀ := by
      have h2 : QuotientGroup.mk' N₀
          ((⟨v', hv'Y⟩ : ↥Y) * ⟨m, hmY⟩ * ((⟨m, hmY⟩ : ↥Y) * ⟨v', hv'Y⟩)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul]
        exact mul_inv_eq_one.mpr h
      exact (QuotientGroup.eq_one_iff _).mp h2
    exact Subgroup.mem_map.mpr ⟨_, h1, by simp [commutatorElement_def, mul_assoc]⟩
  have hv'z : v' = z ∨ v' = u * z := by
    rcases hzv' with h | h
    · exact Or.inl h.symm
    · right
      rw [h, ← mul_assoc, hd.hu2, one_mul]
  have hconj : ∀ h ∈ Subgroup.centralizer ({u} : Set G), ∃ B ∈ oddQuotientFamily
      (Q3T8.Asc77.ExactLayer.exactPair Ω u),
      ∃ hmem : h * (u * e) * h⁻¹ ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u,
        IsUniqueInvolution B (Q3T8.Asc77.T7H.toBar Ω u (h * (u * e) * h⁻¹) hmem) := by
    intro h hh
    have hY' : conjSub h (Q3T8.Asc77.ExactLayer.exactLayer Ω u) = Q3T8.Asc77.ExactLayer.exactLayer
        Ω u :=
      Q3T8.Asc77.ExactLayer.conjSub_exactLayer hΩ.conjInvariant hh
    have hmem : h * (u * e) * h⁻¹ ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u := by
      have := conj_mem_conjSub (n := h) htY
      rwa [hY'] at this
    have hK₂h : conjSub h (conjSub g K) ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
      Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hh hK₂
    have hzh : IsUniqueInvolution (conjSub h (conjSub g K)) (h * (u * e) * h⁻¹) := hzK₂.conj h
    exact ⟨Q3T8.Asc77.T7H.exactImg Ω u (conjSub h (conjSub g K)), Q3T8.Asc77.T7H.exactImg_mem hK₂h,
        hmem,
      Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hK₂h hzh hmem⟩
  exact ⟨a₂, b₂, v', ha₂Y, hb₂Y, hv'Y, htY, hv'z,
    ⟨hΦ, CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y, hgen, hAΦ⟩, hlt,
    ⟨hA, hA', hne, hzA, hzA', haB, hbB, haBsq, hbBsq, hw, hF, hnbA, hnbA'⟩, hconj⟩

theorem layer_u_tag (htcf : Q3T8.Asc77.TwinCentralFact3) (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) :
    u * e ∈ zStarOf (Q3T8.Asc77.ExactLayer.exactLayer Ω u) ∨ Q3T8.Asc77.LayerOrthType Ω u 5 true ∨
      Q3T8.Asc77.LayerOrthType Ω u 6 (!piSign 3 1) := by
  classical
  have hst := hs.stand
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := hst.below
  obtain ⟨a₂, b₂, v', ha₂Y, hb₂Y, hv'Y, htY, -, hS, hlt, T, -⟩ := Q3T8.Asc77.T7L.layer_u_frame hs hd
  rcases Q3T8.Asc77.T7L.twinSection_cases htcf hBelow hlt hS T with hconn | ⟨D, hcard, i, hE4⟩
  · left
    exact Subgroup.mem_map.mpr ⟨⟨u * e, htY⟩, twinSection_central T.hzA T.hzA' hconn hS.gen, rfl⟩
  · right
    rcases hE4 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left
      exact sectionOrthType_of_hasOrthType hS.gen
        ⟨_, _, Or.inl ⟨rfl, h1, h2⟩, D, hcard, i, rfl, rfl⟩
    · right
      have hπ : piSign 3 1 = false := by
        unfold piSign
        simp [h3]
      rw [hπ]
      exact sectionOrthType_of_hasOrthType hS.gen
        ⟨_, _, Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩), D, hcard, i, rfl, rfl⟩
    · right
      have hπ : piSign 3 1 = true := by
        unfold piSign
        simp [h3]
      rw [hπ]
      exact sectionOrthType_of_hasOrthType hS.gen
        ⟨_, _, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩)), D, hcard, i, rfl, rfl⟩
end T7L
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
    CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal

theorem c23_5X_type_of_tcf (htcf : Q3T8.Asc77.TwinCentralFact3) : Q3T8.Asc77.C23_5X_type := by
  intro G _ _ _ Ω K K' W z u e g h
  have hs : Q3T8.Asc77.Hyp23Setting Ω K K' z := h.std.setting
  have hd : Hyp23bData Ω K K' W z u e g := h.data
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  exact Q3T8.Asc77.T7L.layer_u_tag htcf hs hd
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace T7L
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7L
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}
section GammaB

theorem inf_centralizer_le_gamma2
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) {s : G}
    (hsB : s ∈ Subgroup.closure ({u * e, u, z} : Set G)) (hs1 : s ≠ 1) (hsu : s ≠ u)
    {Y : Subgroup G} (hY : Y ≤ Subgroup.centralizer ({u} : Set G)) :
    Y ⊓ Subgroup.centralizer ({s} : Set G) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)) := by
  have hB := Q3T8.Asc77.T7K.B_isElemAbelian hs hd
  have hcomm := T7A.commutes_closure (Q3T8.Asc77.T7K.comm_gen hs hd)
  obtain ⟨-, huB, -⟩ := T7K.generators_mem_B z u e
  have hs2 : s * s = 1 := by
    have := hB.2 s hsB
    rwa [pow_two] at this
  have hus : u * s = s * u := hcomm u huB s hsB
  have hA := T7A.isElemAbelian2_closure_pair hd.hu2 hs2 hd.hu1 hs1 (Ne.symm hsu) hus
  have hAB : Subgroup.closure ({u, s} : Set G) ≤ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact huB
    · exact hsB
  rintro y ⟨hyY, hys⟩
  have hyu : u * y = y * u := (Subgroup.mem_centralizer_singleton_iff.mp (hY hyY)).symm
  have hys' : s * y = y * s := (Subgroup.mem_centralizer_singleton_iff.mp hys).symm
  exact T7K.le_gamma2 hAB hA ⟨hY hyY, T7B.mem_centralizer_closure_pair hyu hys'⟩

theorem oddCore_layer_le_gamma2
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) :
    oddCoreOf (Q3T8.Asc77.ExactLayer.exactLayer Ω u) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)) := by
  have hB := Q3T8.Asc77.T7K.B_isElemAbelian hs hd
  have hB8 := Q3T8.Asc77.T7K.B_natCard hs hd
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hBu : Subgroup.closure ({u * e, u, z} : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Q3T8.Asc77.T7K.comm_gen hs hd x hx u (by
        simp))
  have hBN : ∀ b ∈ Subgroup.closure ({u * e, u, z} : Set G),
      b ∈ Subgroup.normalizer (oddCoreOf (Q3T8.Asc77.ExactLayer.exactLayer Ω u) : Set G) := fun b
          hb =>
    mem_normalizer_oddCoreOf (mem_normalizer_iff_conjSub_eq.mpr
      (Q3T8.Asc77.ExactLayer.conjSub_exactLayer hΩ.conjInvariant (hBu hb)))
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two (Subgroup.closure ({u * e, u, z} : Set G)) (oddCoreOf
        (Q3T8.Asc77.ExactLayer.exactLayer Ω u)) hB
    (by rw [hB8]; norm_num) hBN (Nat.coprime_two_left.mpr (oddCoreOf_odd_natCard _))
  have hNH : oddCoreOf (Q3T8.Asc77.ExactLayer.exactLayer Ω u) ≤ Subgroup.centralizer ({u} : Set G)
      :=
    (oddCoreIn_le _).trans (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u)
  conv_lhs => rw [← hgen]
  refine iSup₂_le fun E hE => ?_
  have hE2 : IsElemAbelian2 E 2 :=
    ⟨hE.2, fun x hx => by rw [← pow_two]; exact hB.2 x (hE.1 hx)⟩
  exact (inf_le_inf_right _ hNH).trans (T7K.le_gamma2 hE.1 hE2)

theorem B_ne
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    (u * e ≠ 1 ∧ u * e ≠ u) ∧ (z ≠ 1 ∧ z ≠ u) ∧ (u * z ≠ 1 ∧ u * z ≠ u) ∧
      (u * e * z ≠ 1 ∧ u * e * z ≠ u) ∧ (u * e * (u * z) ≠ 1 ∧ u * e * (u * z) ≠ u) := by
  have hee : e ∉ K ⊔ K' := Q3T8.Asc77.T7K.e_not_mem_sup hs hd
  have huS : u ∈ K ⊔ K' := hd.hu
  have hzS : z ∈ K ⊔ K' := Subgroup.mem_sup_left hs.hz.mem
  have hue : u * e = e * u := T7K.comm_e_of_mem_W hd hd.huW
  have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hd.hu2
  have hez : u * e * (u * z) = e * z := by
    calc u * e * (u * z) = (e * u) * (u * z) := by rw [hue]
      _ = e * (u * u) * z := by group
      _ = e * z := by rw [hd.hu2]; group
  have a1 : u * e ≠ 1 := by
    intro h
    apply hee
    rw [eq_inv_of_mul_eq_one_right h]
    exact (K ⊔ K').inv_mem huS
  have a2 : u * e ≠ u := by
    intro h
    exact hd.he1 (mul_left_cancel (h.trans (mul_one u).symm))
  have a3 : u * z ≠ 1 := by
    intro h
    apply hd.huz
    have := eq_inv_of_mul_eq_one_right h
    rw [this, hu1]
  have a4 : u * z ≠ u := by
    intro h
    exact hs.hz.ne_one (mul_left_cancel (h.trans (mul_one u).symm))
  have a5 : u * e * z ≠ 1 := by
    intro h
    apply hee
    have h1 : e * z = u⁻¹ := by
      calc e * z = u⁻¹ * (u * e * z) := by group
        _ = u⁻¹ := by rw [h, mul_one]
    have : e = u⁻¹ * z⁻¹ := by
      calc e = (e * z) * z⁻¹ := by group
        _ = u⁻¹ * z⁻¹ := by rw [h1]
    rw [this]
    exact (K ⊔ K').mul_mem ((K ⊔ K').inv_mem huS) ((K ⊔ K').inv_mem hzS)
  have a6 : u * e * z ≠ u := by
    intro h
    apply hee
    have h1 : e * z = 1 := by
      have : u * (e * z) = u * 1 := by rw [← mul_assoc, h, mul_one]
      exact mul_left_cancel this
    rw [eq_inv_of_mul_eq_one_left h1]
    exact (K ⊔ K').inv_mem hzS
  have a7 : u * e * (u * z) ≠ 1 := by
    intro h
    apply hee
    rw [hez] at h
    rw [eq_inv_of_mul_eq_one_left h]
    exact (K ⊔ K').inv_mem hzS
  have a8 : u * e * (u * z) ≠ u := by
    intro h
    apply hee
    rw [hez] at h
    have : e = u * z⁻¹ := by
      calc e = (e * z) * z⁻¹ := by group
        _ = u * z⁻¹ := by rw [h]
    rw [this]
    exact (K ⊔ K').mul_mem huS ((K ⊔ K').inv_mem hzS)
  exact ⟨⟨a1, a2⟩, ⟨hs.hz.ne_one, fun h => hd.huz h.symm⟩, ⟨a3, a4⟩, ⟨a5, a6⟩, ⟨a7, a8⟩⟩
end GammaB
end T7L

theorem c23_GammaU_of_facts (htcf : Q3T8.Asc77.TwinCentralFact3) (hgen : Q3T8.Asc77.E4TwinGen3) :
    Q3T8.Asc77.C23_GammaU := by
  intro G _ _ _ Ω K K' W z u e g hs hd
  classical
  have hst := hs.stand
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := hst.below
  obtain ⟨a₂, b₂, v', ha₂Y, hb₂Y, hv'Y, htY, hv'z, hS, hlt, T, hconj⟩ :=
    Q3T8.Asc77.T7L.layer_u_frame hs hd
  obtain ⟨hsplit, hCI⟩ := Q3T8.Asc77.T7L.twinSection_gen_conj htcf hgen hBelow hlt hS T

  have hBel := Q3T8.Asc77.T7K.B_isElemAbelian hs hd
  obtain ⟨hzB, huB, heB⟩ := T7K.generators_mem_B z u e
  have htB : u * e ∈ Subgroup.closure ({u * e, u, z} : Set G) :=
    Subgroup.mul_mem _ huB heB
  have hv'B : v' ∈ Subgroup.closure ({u * e, u, z} : Set G) := by
    rcases hv'z with h | h
    · rw [h]
      exact hzB
    · rw [h]
      exact Subgroup.mul_mem _ huB hzB
  have htv'B : u * e * v' ∈ Subgroup.closure ({u * e, u, z} : Set G) := Subgroup.mul_mem _ htB hv'B
  have sq : ∀ x ∈ Subgroup.closure ({u * e, u, z} : Set G), x * x = 1 := fun x hx => by
    have := hBel.2 x hx
    rwa [pow_two] at this
  obtain ⟨⟨ht1, htu⟩, ⟨hz1, hzu⟩, ⟨huz1, huzu⟩, ⟨htz1, htzu⟩, ⟨htuz1, htuzu⟩⟩ :=
    Q3T8.Asc77.T7L.B_ne hs hd
  have hv'1 : v' ≠ 1 ∧ v' ≠ u := by
    rcases hv'z with h | h <;> rw [h]
    · exact ⟨hz1, hzu⟩
    · exact ⟨huz1, huzu⟩
  have htv'1 : u * e * v' ≠ 1 ∧ u * e * v' ≠ u := by
    rcases hv'z with h | h <;> rw [h]
    · exact ⟨htz1, htzu⟩
    · exact ⟨htuz1, htuzu⟩
  have hYH : Q3T8.Asc77.ExactLayer.exactLayer Ω u ≤ Subgroup.centralizer ({u} : Set G) :=
      Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u

  have hYΓ : Q3T8.Asc77.ExactLayer.exactLayer Ω u ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)) := by
    rw [← Q3T8.Asc77.T7H.toBar_mul htY hv'Y] at hsplit
    have hgenY := T7L.layer_le_of_quot_gen htY hv'Y ((Q3T8.Asc77.ExactLayer.exactLayer Ω u).mul_mem
        htY hv'Y)
      (sq _ htB) (sq _ hv'B) (sq _ htv'B) ht1 hv'1.1 htv'1.1 hsplit
    exact hgenY.trans (sup_le (sup_le (sup_le (Q3T8.Asc77.T7L.oddCore_layer_le_gamma2 hs hd)
      (Q3T8.Asc77.T7L.inf_centralizer_le_gamma2 hs hd htB ht1 htu hYH))
      (Q3T8.Asc77.T7L.inf_centralizer_le_gamma2 hs hd hv'B hv'1.1 hv'1.2 hYH))
      (Q3T8.Asc77.T7L.inf_centralizer_le_gamma2 hs hd htv'B htv'1.1 htv'1.2 hYH))
  have hHt : Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({u * e} : Set G) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)) :=
    Q3T8.Asc77.T7L.inf_centralizer_le_gamma2 hs hd htB ht1 htu le_rfl

  intro h hh
  obtain ⟨B₀, hB₀, hmem, huniq⟩ := hconj h hh
  obtain ⟨yb, hyb⟩ := hCI B₀ hB₀ _ huniq
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
  have hcongr := T7L.mem_oddCore_of_mk_conj htY hmem y hyb
  obtain ⟨y', hy', c, hc, rfl⟩ := T7L.eq_mul_of_conj_mod hYH (oddCoreIn_le _)
    (oddCoreOf_odd_natCard _) (fun y hy => normalizer_oddCoreIn _ hy) htY (sq _ htB) ht1 hh y.2
    hcongr
  exact Subgroup.mul_mem _ (hYΓ hy') (hHt hc)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
    CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal

theorem c23_5X_type_proved : Q3T8.Asc77.C23_5X_type :=
  Q3T8.Asc77.c23_5X_type_of_tcf Q3T8.Asc77.twinCentralFact3_proved

theorem c23_GammaU_of_e4 (hgen : Q3T8.Asc77.E4TwinGen3) : Q3T8.Asc77.C23_GammaU :=
  Q3T8.Asc77.c23_GammaU_of_facts Q3T8.Asc77.twinCentralFact3_proved hgen
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
