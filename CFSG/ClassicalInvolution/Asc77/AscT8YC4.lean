module

public import CFSG.ClassicalInvolution.Asc77.AscT8YC2
import CFSG.ClassicalInvolution.Asc77.AscT8YC4Eng
import CFSG.ClassicalInvolution.Asc77.AscT8YAEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Balance.Theorem5

namespace T8YY


variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

namespace FrameData

theorem zz_comm (c : Ctx p f Ω W) (F : FrameData Ω W K J z t) (i j : Fin 4) :
    F.zz i * F.zz j = F.zz j * F.zz i :=
  c.comm_W _ (F.hW i) _ (F.hW j)

theorem zz0_mul_mem_vGroup (c : Ctx p f Ω W) (F : FrameData Ω W K J z t) (j : Fin 4) :
    F.zz 0 * F.zz j ∈ F.vGroup := by
  exact F.zz0_mul_mem_vGroupE_of c.comm_W j

theorem mul_mem_vGroup (c : Ctx p f Ω W) (F : FrameData Ω W K J z t) (i j : Fin 4) :
    F.zz i * F.zz j ∈ F.vGroup := by
  exact F.mul_mem_vGroupE_of c.comm_W i j

theorem vGroup_eq_of_members {W' K' J' : Subgroup G} {z' t' : G} (c : Ctx p f Ω W)
    (c' : Ctx p f Ω W') (F : FrameData Ω W K J z t) (F' : FrameData Ω W' K' J' z' t')
    (hmem : ∀ j, ∃ i, (F'.ρ j).K = (F.ρ i).K) : F'.vGroup = F.vGroup := by
  exact vGroupE_eq_of_members_of c.comm_W c'.comm_W F F' hmem

end FrameData

theorem alphaOf_vGroup_eq [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (F : FrameData Ω W K J z t) :
    IsElemAbelian2 F.vGroup 2 ∧
      alphaOf F.vGroup = alphaOf (Subgroup.closure ({t, z} : Set G)) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨R₃, hF, hind⟩ := F.exists_triFrame hs
  have hHyp : Hyp51 (Subgroup.closure ({z, t, F.zz 2} : Set G)) :=
    T8T.hyp51Tri_proved p f G Ω ![K, J, (F.ρ 2).K] ![z, t, F.zz 2] R₃ hs.stand hnt hF
      (by simpa using hind)
  have hc01 : z * t = t * z := hF.comm hp hΩ 0 1
  have hc02 : z * F.zz 2 = F.zz 2 * z := hF.comm hp hΩ 0 2
  have hc12 : t * F.zz 2 = F.zz 2 * t := hF.comm hp hΩ 1 2
  exact alphaOf_vGroup_eqE F hnt hF hHyp hc01 hc02 hc12
    F.vGroup rfl



theorem mem_normalizer_of_conjSub_le {V : Subgroup G} {n : G} (h1 : conjSub n V ≤ V)
    (h2 : conjSub n⁻¹ V ≤ V) : n ∈ Subgroup.normalizer (V : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  refine le_antisymm h1 fun v hv => ?_
  have hx : n⁻¹ * v * n ∈ conjSub n⁻¹ V := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hv
  have := h2 hx
  rw [mem_conjSub_iff]
  exact this

theorem false_of_singleFrame [IsSimpleGroup G] (hV : LayerFrattiniFact p f)
    (hs : Std8 p f Ω K J S R T W z t) (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      ¬ DConnected (T8.layerFamQ Ω (z * s)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : FrameData Ω W K J z t)
    (hsingle : ∀ i : Fin 4, ∀ M ∈ omegaNbr Ω (F.ρ i).K, ∃ j, M = (F.ρ j).K) : False := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  obtain ⟨hVab, hαV'⟩ := alphaOf_vGroup_eq hs F
  have hαV : alphaOf F.vGroup = ⊥ := hαV'.trans hα
  have hSig : ∀ L ∈ dComp Ω K, ∃ i, L = (F.ρ i).K := by
    intro L hL
    induction hL with
    | refl => exact ⟨0, F.h0.symm⟩
    | @tail b c hbk hbc ih =>
      obtain ⟨i, rfl⟩ := ih
      obtain ⟨hcΩ, hadj⟩ := hbc
      rcases hadj with h | h
      · exact hsingle i c h
      · exact hsingle i c (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hcΩ (F.ρ i).hK h)
  have hFm : ∀ i, (F.ρ i).K ∈ dComp Ω K := by
    intro i
    by_cases h0 : i = 0
    · rw [h0, F.h0]
      exact Relation.ReflTransGen.refl
    · have := F.hadj 0 i (Ne.symm h0)
      rw [F.h0] at this
      exact T8.mem_dComp_of_mem_omegaNbr this
  have hNle : ∀ n ∈ sigmaNorm Ω K, conjSub n F.vGroup ≤ F.vGroup := by
    intro n hn
    have hKn : conjSub n K ∈ dComp Ω K := (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).mp hn
    have hdeq : dComp Ω (conjSub n K) = dComp Ω K := T8.dComp_eq_of_mem hK hKn
    have hperm : ∀ i, ∃ j, conjSub n (F.ρ i).K = (F.ρ j).K := by
      intro i
      have h1 := mem_dComp_conjSub hΩ.conjInvariant (hFm i) n
      rw [hdeq] at h1
      exact hSig _ h1
    choose π hπ using hperm
    have hzπ : ∀ i, n * F.zz i * n⁻¹ = F.zz (π i) := fun i =>
      ((F.hz i).conj n).eq (by rw [hπ i]; exact F.hz (π i))
    unfold FrameData.vGroup
    rw [conjSub_closure_pair, Subgroup.closure_le]
    intro y hy
    have hconj : ∀ i j, n * (F.zz i * F.zz j) * n⁻¹ = F.zz (π i) * F.zz (π j) := by
      intro i j
      rw [← hzπ i, ← hzπ j]
      group
    rcases hy with rfl | rfl
    · rw [hconj 0 1]
      exact F.mul_mem_vGroup c _ _
    · rw [hconj 0 2]
      exact F.mul_mem_vGroup c _ _
  have hN : sigmaNorm Ω K ≤ Subgroup.normalizer (F.vGroup : Set G) := fun n hn =>
    mem_normalizer_of_conjSub_le (hNle n hn) (hNle n⁻¹ ((sigmaNorm Ω K).inv_mem hn))
  have hC : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      Subgroup.centralizer ({z * s} : Set G) ≤ Subgroup.normalizer (F.vGroup : Set G) := by
    intro M hM s hs'
    have hnconn := huni M hM s hs'
    obtain ⟨S', R', T', W', hstd⟩ :=
      c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
    have hμ' := muIsoWylD4_transfer hp hq hΩ hs.hW.1 hstd.hW.1 hμ
    have hnc' : ¬ DbarConnected Ω W' := T8X.not_dbarConnected_of_ne hstd hne
    obtain ⟨F'⟩ := exists_frameData hstd hμ' hnc'
    have c' := T8.ctxOf (T8.partIHyp_of_std8 hstd) hstd.hW.1
    have hmemF' : ∀ j, ∃ i, (F'.ρ j).K = (F.ρ i).K := by
      intro j
      by_cases h0 : j = 0
      · exact ⟨0, by rw [h0, F'.h0, F.h0]⟩
      by_cases h1 : j = 1
      · obtain ⟨i, hi⟩ := hsingle 0 M (by rw [F.h0]; exact hM)
        exact ⟨i, by rw [h1, F'.h1, hi]⟩
      · have h' := F'.hadj 0 j (Ne.symm h0)
        rw [F'.h0] at h'
        obtain ⟨i, hi⟩ := hsingle 0 _ (by rw [F.h0]; exact h')
        exact ⟨i, hi⟩
    have hVeq : F'.vGroup = F.vGroup := FrameData.vGroup_eq_of_members c c' F F' hmemF'
    have hfr := hV G Ω K M S' R' T' W' z s hstd hdisc hμ' hne hnconn F'
    have hzsV : z * s ∈ F.vGroup := by
      rw [← hVeq]
      have h01 : F'.zz 0 * F'.zz 1 ∈ F'.vGroup := Subgroup.subset_closure (Set.mem_insert _ _)
      rwa [F'.hz0, F'.hz1] at h01
    have hzs1 : z * s ≠ 1 := by
      have := F'.mul_ne_one 0 1 (by decide)
      rwa [F'.hz0, F'.hz1] at this
    intro x hx
    obtain ⟨o, ho, hconj⟩ := hfr x hx
    have hocomm : ∀ y ∈ F.vGroup, o * y = y * o := fun y hy =>
      T8.oddCoreOf_centralizer_commutes hαV hzsV hzs1 hy o
        (T8T.oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ (z * s) ho)
    have hoN : o ∈ Subgroup.normalizer (F.vGroup : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have e : ∀ y ∈ F.vGroup, o * y * o⁻¹ = y := fun y hy => by
        rw [hocomm y hy]
        group
      constructor
      · intro hy
        rw [e y hy]
        exact hy
      · intro hy'
        have hc := hocomm _ hy'
        have e2 : o * y * o⁻¹ = y := by
          calc o * y * o⁻¹ = o⁻¹ * (o * (o * y * o⁻¹)) := by group
            _ = o⁻¹ * ((o * y * o⁻¹) * o) := by rw [hc]
            _ = y := by group
        rw [e2] at hy'
        exact hy'
    have hoxN : o * x ∈ Subgroup.normalizer (F.vGroup : Set G) := by
      rw [← hVeq, mem_normalizer_iff_conjSub_eq]
      exact hconj
    have hx' : x = o⁻¹ * (o * x) := by group
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hoN) hoxN
  have hH : T8.H274 Ω K z ≤ Subgroup.normalizer (F.vGroup : Set G) :=
    sup_le hN (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => hC M hM s hs')
  have htop : T8.H274 Ω K z = ⊤ := h274_eq_top hs hdisc hμ hne
  rw [htop, top_le_iff] at hH
  have hnorm : F.vGroup.Normal := Subgroup.normalizer_eq_top_iff.mp hH
  rcases hnorm.eq_bot_or_eq_top with h | h
  · have h01 : F.zz 0 * F.zz 1 ∈ F.vGroup := Subgroup.subset_closure (Set.mem_insert _ _)
    rw [h, Subgroup.mem_bot] at h01
    exact F.mul_ne_one 0 1 (by decide) h01
  · have hall : ∀ x : G, x * x = 1 := fun x => hVab.2 x (h ▸ Subgroup.mem_top x)
    have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
      calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hall (a * b))).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by
          rw [inv_eq_of_mul_eq_one_right (hall a), inv_eq_of_mul_eq_one_right (hall b)]
    have : Group.IsSolvable G := Group.isSolvable_of_comm hcomm
    exact not_isSolvable_of_mem_mod hΩ hK hs.hz
      (Group.isSolvable_of_isSolvable_injective (f := K.subtype) K.subtype_injective)

end T8YY

end CFSG.ClassicalInvolution.Asc77
