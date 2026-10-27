module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21B02

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.AscE184Sect CFSG.ClassicalInvolution.Asc77.ExactLayer
section Frame
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' J W :
    Subgroup G} {z u t : G}

theorem Hyp21.sectionHull_u_ne_top
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) :
    Q3T8.Asc77.ExactLayer.exactLayer Ω u ≠ ⊤ := by
  have hΩ : Q3T8.Asc77.HypOmegaMod Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  intro htop
  have hle : Q3T8.Asc77.ExactLayer.exactLayer Ω u ≤ Subgroup.centralizer ({u} : Set G) :=
    Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u
  rw [htop, top_le_iff] at hle
  have hcomm : ∀ g : G, g * u = u * g := fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle ▸ Subgroup.mem_top g)
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
  obtain ⟨x, -, y, -, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hVR).exists_not_commute
  exact h.hu1 (T7A.eq_one_of_central ⟨x, y, hxy⟩ hcomm)

theorem Hyp21.centralizer_u_le_of_disc
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (h3s : ∀ n, Q3T8.Generic.CITBelowU n → Q3T8.Asc77.T3.Thm3SectBelow n) (hconn : ¬
        Q3T8.Asc77.SectionConnected Ω u)
    {H : Subgroup G} (hY : Q3T8.Asc77.ExactLayer.exactLayer Ω u ≤ H)
    (hN : ∀ J₀ ∈ dComp Ω K, Subgroup.normalizer (J₀ : Set G) ≤ H) :
    Subgroup.centralizer ({u} : Set G) ≤ H := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := h.std.stand.below
  have hcA : IsPGroup 2 (Subgroup.zpowers u) := Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one
      h.hu2
  obtain ⟨g₀, -, hJ₀nbr, hJ₀t⟩ := Q3T8.Asc77.exists_mem_tqMembers_u hΩ hK hz h.std.hK' h.std.hne
      h.hu
    h.hu2 h.hu1 h.hJ h.ht
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hK hz))
  have horb := (Q3T8.Asc77.section_connected_or_orbit hΩ hcA h.sectionHull_u_ne_top
    h.std.stand.ih (h3s _ hBelow) hJ₀t).resolve_left hconn
  intro c' hc'
  have h1 : conjSub c' (conjSub g₀ J) ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hc' hJ₀t
  obtain ⟨g, hg, hgeq⟩ := Q3T8.Asc77.exists_mem_sectionHull_conj_of_orbit hΩ hcA hJ₀t horb h1
  have hgY : g ∈ H := hY hg
  set m : G := g⁻¹ * c' with hmdef
  have hm : conjSub m (conjSub g₀ J) = conjSub g₀ J := by
    rw [hmdef, conjSub_mul, hgeq, conjSub_inv_conjSub]
  have hmN : m ∈ Subgroup.normalizer ((conjSub g₀ J : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hm
  have e : c' = g * m := by rw [hmdef]; group
  rw [e]
  exact Subgroup.mul_mem _ hgY (hN _ hJ₀d hmN)

omit [IsSimpleGroup G] in

theorem Hyp21.centralizer_u_le_of_conn
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hconn : Q3T8.Asc77.SectionConnected Ω u) {H : Subgroup G}
    (hO : oddCoreOf (Subgroup.centralizer ({u} : Set G)) ≤ H)
    (hN : Subgroup.normalizer (K : Set G) ≤ H)
    (htrans : ∀ L ∈ dstarComp Ω K, ∃ x ∈ H, conjSub x K = L) :
    Subgroup.centralizer ({u} : Set G) ≤ H := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  obtain ⟨g₀, -, hJ₀nbr, hJ₀t⟩ := Q3T8.Asc77.exists_mem_tqMembers_u hΩ hK hz h.std.hK' h.std.hne
      h.hu
    h.hu2 h.hu1 h.hJ h.ht
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hK hz))
  have hJ₀ds : conjSub g₀ J ∈ dstarComp Ω K := Q3T8.Asc77.T7A.mem_dstarComp_of_mem_dComp (hΩ :
      Q3T8.Asc77.HypOmegaMod Ω) hJ₀d
  intro c' hc'
  have h1 : conjSub c' (conjSub g₀ J) ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hc' hJ₀t
  obtain ⟨n, hn, J', -, hJ'd, hMeq⟩ :=
    Q3T8.Asc77.exists_conj_tqMembers_of_connected hΩ h.hu2 hJ₀t hconn _ h1
  have hJ'ds : J' ∈ dstarComp Ω K := by
    rw [T7A.dstarComp_eq_of_mem hK hJ₀ds] at hJ'd
    exact hJ'd
  obtain ⟨x', hx'H, hx'⟩ := htrans J' hJ'ds
  obtain ⟨x₀, hx₀H, hx₀⟩ := htrans _ hJ₀ds
  have hc'eq : conjSub (c' * x₀) K = conjSub (n * x') K := by
    rw [conjSub_mul, hx₀, hMeq, ← hx', conjSub_mul]
  have hm : conjSub ((n * x')⁻¹ * (c' * x₀)) K = K := by
    rw [conjSub_mul, hc'eq, conjSub_inv_conjSub]
  have hmH : (n * x')⁻¹ * (c' * x₀) ∈ H := hN (mem_normalizer_iff_conjSub_eq.mpr hm)
  have e : c' = ((n * x') * ((n * x')⁻¹ * (c' * x₀))) * x₀⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hO hn) hx'H) hmH)
    (Subgroup.inv_mem _ hx₀H)
end Frame
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.AscE184Sect CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Asc77.T7R
section Frame
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' J W :
    Subgroup G} {z u t : G}

theorem Hyp21.alpha_u_tz
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) (hC3 : Q3T8.Asc77.C21_3) :
    alphaOf (Subgroup.closure ({u, t * z} : Set G)) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hfr := h.twinFrameData
  have hzt : z * t = t * z := hfr.comm_zt hΩ
  have hne : u ≠ t * z := by
    intro h1
    apply hfr.t_not_mem_closure hΩ
    have hz' : z ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
    have hu' : u ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
    have : t = u * z := by
      calc t = (t * z) * z := by rw [mul_assoc, h.std.hz.sq, mul_one]
        _ = u * z := by rw [← h1]
    rw [this]
    exact Subgroup.mul_mem _ hu' hz'
  have hcomm : u * (t * z) = (t * z) * u := by
    calc u * (t * z) = (u * t) * z := by group
      _ = (t * u) * z := by rw [← h.htu]
      _ = t * (u * z) := by group
      _ = t * (z * u) := by rw [h.u_comm_z]
      _ = (t * z) * u := by group
  have hA : IsElemAbelian2 (Subgroup.closure ({u, t * z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair h.hu2 h.tz_sq h.hu1 h.tz_ne_one hne hcomm
  have hle : Subgroup.closure ({u, t * z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  exact (hC3 G Ω K K' z u J t W h).2 _ hle hA

theorem Hyp21.normalizer_le_normalizer_alpha_of_mem_dComp
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hs : Q3T8.Asc77.AlphaSteps) {J₀ : Subgroup G} (hJ₀ : J₀ ∈ dComp Ω K) :
    Subgroup.normalizer (J₀ : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  obtain ⟨x₀, hx₀N, hx₀⟩ := hs.exists_mem_normalizer h hJ₀
  intro m hm
  have hmK : x₀⁻¹ * m * x₀ ∈ Subgroup.normalizer (K : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, conjSub_mul, hx₀,
      mem_normalizer_iff_conjSub_eq.mp hm, ← hx₀, conjSub_inv_conjSub]
  have h2 := h.normalizer_le_normalizer_alpha hs hmK
  have e : m = x₀ * (x₀⁻¹ * m * x₀) * x₀⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx₀N h2) (Subgroup.inv_mem _ hx₀N)
end Frame

@[expose] def C21_14_Y_disc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      ¬ Q3T8.Asc77.SectionConnected Ω u →
        ExactLayer.exactLayer Ω u ≤ Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)
            ∧
          (alphaOf (Subgroup.closure {u, z}) = ⊥ →
            ExactLayer.exactLayer Ω u ≤ sigmaGen Ω K ∨
 ExactLayer.exactLayer Ω u ≤ Subgroup.centralizer ({t * z} : Set G))

theorem c21_14_N_disc_of_Ydisc
    (hC3 : Q3T8.Asc77.C21_3) (hY : Q3T8.Asc77.C21_14_Y_disc) :
    Q3T8.Asc77.C21_14_N_disc := by
  intro G _ _ _ Ω K K' z u J t W h hconn
  have hs : Q3T8.Asc77.AlphaSteps := ⟨hC3, Q3T8.Asc77.twinNormAlpha_of hC3⟩
  have h3s : ∀ n, Q3T8.Generic.CITBelowU n → Q3T8.Asc77.T3.Thm3SectBelow n :=
    (fun _ h => Q3T7E.thm3SectBelow3_of_ih h)
  exact h.centralizer_u_le_of_disc h3s hconn (hY G Ω K K' z u J t W h hconn).1 fun _ hJ₀ =>
    h.normalizer_le_normalizer_alpha_of_mem_dComp hs hJ₀
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.AscE184Sect CFSG.ClassicalInvolution.Asc77.ExactLayer
section Frame
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' J W :
    Subgroup G} {z u t : G}

theorem Hyp21.rLayer_tz_le_sigmaGen_of_eq
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) (hC3 : Q3T8.Asc77.C21_3)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) (heq : dComp Ω K = dstarComp Ω K) :
    rLayer Ω (t * z) ≤ sigmaGen Ω K := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hMF : Q3T8.Asc77.DStarConnectedTwinGen :=
    Q3T8.Asc77.dstarConnectedTwinGen_of
  have h3s : ∀ n, Q3T8.Generic.CITBelowU n → Q3T8.Asc77.T3.Thm3SectBelow n :=
    (fun _ h => Q3T7E.thm3SectBelow3_of_ih h)
  have hcA : IsPGroup 2 (Subgroup.zpowers (t * z)) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one h.tz_sq
  refine iSup₂_le fun R hR => iSup_le fun hRc => ?_
  obtain ⟨J₁, hJ₁Ω, hRJ₁⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJ₁t : J₁ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (t * z) :=
    (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mpr ⟨hJ₁Ω, R, hRJ₁, hRc⟩
  have hJ₁d : J₁ ∈ dComp Ω K := by
    rw [heq]
    exact Q3T8.Asc77.tqMembers_subset_dstarComp_gen h hMF h3s hC3 hα J₁ hJ₁t
  exact hRJ₁.1.trans (le_iSup₂_of_le J₁ hJ₁d le_rfl)
end Frame

@[expose] def C21_NormCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer ({t * z} : Set G)

theorem c21_15_of_normCent
    (hC3 : Q3T8.Asc77.C21_3) (hN : Q3T8.Asc77.C21_NormCent) : Q3T8.Asc77.C21_15 := by
  intro G _ _ _ Ω K K' z u J t W h hα hD M hM
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hne : dComp Ω K ≠ dstarComp Ω K := fun heq =>
    hD (h.rLayer_tz_le_sigmaGen_of_eq hC3 hα heq)
  have hNK := hN G Ω K K' z u J t W h hα hD
  have hMW : MGrp Ω W ≤ Subgroup.centralizer ({t * z} : Set G) :=
    (h.mGrp_le_rLayer_tz hne).trans (rLayer_le_centralizer Ω (t * z))
  have hMd : M ∈ dstarComp Ω K := Q3T8.Asc77.T7A.mem_dstarComp_of_mem_dComp (hΩ :
      Q3T8.Asc77.HypOmegaMod Ω) hM
  obtain ⟨x, hx, rfl⟩ := h.exists_mem_conj_of_dstarComp hne hMW hNK M hMd
  have hKc : K ≤ Subgroup.centralizer ({t * z} : Set G) := le_trans Subgroup.le_normalizer hNK
  intro y hy
  rw [mem_conjSub_iff] at hy
  have hy' := hKc hy
  have hyx : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
  rw [hyx]
  exact (Subgroup.centralizer ({t * z} : Set G)).mul_mem
    ((Subgroup.centralizer ({t * z} : Set G)).mul_mem hx hy')
    ((Subgroup.centralizer ({t * z} : Set G)).inv_mem hx)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.AscE184Sect CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Asc77.T7R
section Frame
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' J W :
    Subgroup G} {z u t : G}

theorem Hyp21.oddCore_centralizer_u_comm_tz
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) (hC3 : Q3T8.Asc77.C21_3)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {n : G}
    (hn : n ∈ oddCoreOf (Subgroup.centralizer ({u} : Set G))) : n * (t * z) = (t * z) * n := by
  have hA : alphaOf (Subgroup.closure ({u, t * z} : Set G)) = ⊥ := by
    rw [h.alpha_u_tz hC3]
    exact hα
  have huA : u ∈ Subgroup.closure ({u, t * z} : Set G) := Subgroup.subset_closure (by simp)
  have htzA : t * z ∈ Subgroup.closure ({u, t * z} : Set G) := Subgroup.subset_closure (by simp)
  exact T8.oddCoreOf_centralizer_commutes hA huA h.hu1 htzA n hn

theorem Hyp21.exists_mem_centralizer_tz_conj
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hN : Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer ({t * z} : Set G)) :
    ∀ L ∈ dstarComp Ω K, ∃ x ∈ Subgroup.centralizer ({t * z} : Set G), conjSub x K = L :=
  h.exists_mem_conj_of_dstarComp hne
    ((h.mGrp_le_rLayer_tz hne).trans (rLayer_le_centralizer Ω (t * z))) hN

theorem Hyp21.centralizer_u_le_centralizer_tz_of_conn
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hC3 : Q3T8.Asc77.C21_3) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hN : Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer ({t * z} : Set G))
    (hconn : Q3T8.Asc77.SectionConnected Ω u) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t * z} : Set G) :=
  h.centralizer_u_le_of_conn hconn
    (fun _ hn => Subgroup.mem_centralizer_singleton_iff.mpr
      (h.oddCore_centralizer_u_comm_tz hC3 hα hn)) hN (h.exists_mem_centralizer_tz_conj hne hN)

theorem Hyp21.centralizer_u_le_centralizer_tz_of_disc
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (h3s : ∀ n, Q3T8.Generic.CITBelowU n → Q3T8.Asc77.T3.Thm3SectBelow n)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hN : Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer ({t * z} : Set G))
    (hconn : ¬ Q3T8.Asc77.SectionConnected Ω u) (hY : ExactLayer.exactLayer Ω u ≤
        Subgroup.centralizer ({t * z} : Set G)) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t * z} : Set G) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  refine h.centralizer_u_le_of_disc h3s hconn hY fun J₀ hJ₀ m hm => ?_
  obtain ⟨x₀, hx₀H, hx₀⟩ := h.exists_mem_centralizer_tz_conj hne hN J₀
    (Q3T8.Asc77.T7A.mem_dstarComp_of_mem_dComp (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hJ₀)
  have hmK : x₀⁻¹ * m * x₀ ∈ Subgroup.normalizer (K : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, conjSub_mul, hx₀,
      mem_normalizer_iff_conjSub_eq.mp hm, ← hx₀, conjSub_inv_conjSub]
  have e : m = x₀ * (x₀⁻¹ * m * x₀) * x₀⁻¹ := by group
  rw [e]
  exact (Subgroup.centralizer ({t * z} : Set G)).mul_mem
    ((Subgroup.centralizer ({t * z} : Set G)).mul_mem hx₀H (hN hmK))
    ((Subgroup.centralizer ({t * z} : Set G)).inv_mem hx₀H)
end Frame
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
