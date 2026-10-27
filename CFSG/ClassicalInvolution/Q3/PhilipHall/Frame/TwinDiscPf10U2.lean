module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc


section Trans

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_conj_of_transitive (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {B : Subgroup G} (hB : B ∈ tqMembers3 Ω c)
    (horb : ∀ M ∈ secFam Ω c, ∃ y, conjSub y (secImg Ω c B) = M) :
    ∀ M ∈ tqMembers3 Ω c, ∃ g ∈ coreLayer Ω c, M = conjSub g B := by
  intro M hM
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set X := coreHull Ω c with hX
  set N₀ : Subgroup ↥X := classicalInvolutionOddCore ↥X with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ : HypOmegaGen (hullFam Ω c) :=
    hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) X
  obtain ⟨y, hy⟩ := horb _ (secImg_mem_secFam hM)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N₀ y
  have hBΛ := subgroupOf_mem_hullFam hB
  have hMΛ := subgroupOf_mem_hullFam hM
  have himg : (conjSub x (((TwinADescent.coreAt c B).subgroupOf C).subgroupOf X)).map
      (QuotientGroup.mk' N₀) =
      (((TwinADescent.coreAt c M).subgroupOf C).subgroupOf X).map (QuotientGroup.mk' N₀) := by
    rw [AscQuot.map_conjSub]
    exact hy
  obtain ⟨n, hn, hn'⟩ := Q3T6.exists_conj_of_map_eq_gen hΛ hN₀odd
    (hΛ.conjInvariant x _ hBΛ) hMΛ himg
  rw [← conjSub_mul] at hn'
  exact ⟨_, ⟨_, (n * x).2, rfl⟩, eq_conjSub_of_hull_eq hΩ hc2 hB hM (n * x) hn'⟩

end Trans

section Frame

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem normalizer_le_normalizer_alpha_of_mem_dComp
    (hs : AlphaSteps (CoreAssembly.conjClass (tightCore R)))
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t)
    {J₀ : Subgroup Y} (hJ₀ : J₀ ∈ dComp (CoreAssembly.conjClass (tightCore R)) K) :
    Subgroup.normalizer (J₀ : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) := by
  obtain ⟨x₀, hx₀N, hx₀⟩ := hs.exists_mem_normalizer hf hJ₀
  have hNK : Subgroup.normalizer (K : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) := fun g hg =>
    hs.centralizer_le hf
      (T7A.mem_centralizer_of_conj_eq (hf.hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hg)))
  intro m hm
  have hmK : x₀⁻¹ * m * x₀ ∈ Subgroup.normalizer (K : Set Y) := by
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, conjSub_mul, hx₀,
      mem_normalizer_iff_conjSub_eq.mp hm, ← hx₀, conjSub_inv_conjSub]
  have h2 := hNK hmK
  have e : m = x₀ * (x₀⁻¹ * m * x₀) * x₀⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx₀N h2) (Subgroup.inv_mem _ hx₀N)

theorem centralizer_u_le_of_disc (hT4 : Thm4RTwinBelow 3 n)
    (s : Setting n R S t₀ K K' z u J t W)
    (hdisc : ¬ SecConnU (CoreAssembly.conjClass (tightCore R)) u) {H : Subgroup Y}
    (hY : coreLayer (CoreAssembly.conjClass (tightCore R)) u ≤ H)
    (hN : ∀ J₀ ∈ dComp (CoreAssembly.conjClass (tightCore R)) K, Subgroup.normalizer (J₀ : Set Y) ≤ H) :
    Subgroup.centralizer ({u} : Set Y) ≤ H := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  obtain ⟨g₀, -, hJ₀nbr, hJ₀⟩ := exists_sylCent_u hΩ hf
  have hJ₀tq : conjSub g₀ J ∈ tqMembers3 Ω u :=
    ⟨hJ₀.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₀.1 hJ₀.2⟩
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hf.mem hf.hz))
  have hlt : Nat.card (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_one s hf.hu1)
  have horb : ∀ M ∈ secFam Ω u, ∃ y, conjSub y (secImg Ω u (conjSub g₀ J)) = M := by
    rcases dichotomy_secFam hT4 hlt hΩ hc2 h2 hq hA hJ₀tq with hconn | horb
    · exact absurd (T3.dstarConnected_of_pivot (secImg_mem_secFam hJ₀tq) hconn) hdisc
    · exact horb
  intro c' hc'
  have h1 : conjSub c' (conjSub g₀ J) ∈ tqMembers3 Ω u :=
    conjSub_mem_tqMembers3 hΩ.conjInvariant hc' hJ₀tq
  obtain ⟨g, hg, hgeq⟩ := exists_conj_of_transitive hΩ hc2 hJ₀tq horb _ h1
  have hgH : g ∈ H := hY hg
  have hm : conjSub (g⁻¹ * c') (conjSub g₀ J) = conjSub g₀ J := by
    rw [conjSub_mul, hgeq, conjSub_inv_conjSub]
  have hmN : g⁻¹ * c' ∈ Subgroup.normalizer ((conjSub g₀ J : Subgroup Y) : Set Y) :=
    mem_normalizer_iff_conjSub_eq.mpr hm
  have e : c' = g * (g⁻¹ * c') := by group
  rw [e]
  exact Subgroup.mul_mem _ hgH (hN _ hJ₀d hmN)

theorem centralizer_u_le_of_conn (s : Setting n R S t₀ K K' z u J t W)
    (hconnU : SecConnU (CoreAssembly.conjClass (tightCore R)) u) {H : Subgroup Y}
    (hO : oddCoreOf (Subgroup.centralizer ({u} : Set Y)) ≤ H)
    (hN : Subgroup.normalizer (K : Set Y) ≤ H)
    (htrans : ∀ L ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K, ∃ x ∈ H, conjSub x K = L) :
    Subgroup.centralizer ({u} : Set Y) ≤ H := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  obtain ⟨g₀, -, hJ₀nbr, hJ₀⟩ := exists_sylCent_u hΩ hf
  have hJ₀tq : conjSub g₀ J ∈ tqMembers3 Ω u :=
    ⟨hJ₀.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₀.1 hJ₀.2⟩
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hf.mem hf.hz))
  have hJ₀ds : conjSub g₀ J ∈ dstarComp Ω K := mem_dstarComp_of_mem_dComp_gen hΩ hJ₀d
  intro c' hc'
  have h1 : conjSub c' (conjSub g₀ J) ∈ tqMembers3 Ω u :=
    conjSub_mem_tqMembers3 hΩ.conjInvariant hc' hJ₀tq
  obtain ⟨m, hm, J', -, hJ'd, hMeq⟩ := exists_conj_tq_of_connected hΩ hc2 hJ₀tq
    (fun M hM => hconnU _ (secImg_mem_secFam hJ₀tq) M hM) _ h1
  have hJ'ds : J' ∈ dstarComp Ω K := by
    rw [T7A.dstarComp_eq_of_mem hf.mem hJ₀ds] at hJ'd
    exact hJ'd
  obtain ⟨x', hx'H, hx'⟩ := htrans J' hJ'ds
  obtain ⟨x₀, hx₀H, hx₀⟩ := htrans _ hJ₀ds
  have hc'eq : conjSub (c' * x₀) K = conjSub (m * x') K := by
    rw [conjSub_mul, hx₀, hMeq, ← hx', conjSub_mul]
  have hmm : conjSub ((m * x')⁻¹ * (c' * x₀)) K = K := by
    rw [conjSub_mul, hc'eq, conjSub_inv_conjSub]
  have hmH : (m * x')⁻¹ * (c' * x₀) ∈ H := hN (mem_normalizer_iff_conjSub_eq.mpr hmm)
  have e : c' = ((m * x') * ((m * x')⁻¹ * (c' * x₀))) * x₀⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hO hm) hx'H) hmH)
    (Subgroup.inv_mem _ hx₀H)

end Frame

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
