module

public import CFSG.ClassicalInvolution.Asc77.AscT8Y3
public import CFSG.ClassicalInvolution.Asc77.AscT8Y
public import CFSG.ClassicalInvolution.Asc77.AscT8Y1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8

section Conj

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem exists_conj_mul_of_aEmpty {K L : Subgroup G} (hAE : AEmpty Ω K)
    (hLs : L ∈ omegaStarNbr Ω K) (hLn : L ∉ omegaNbr Ω K) {z b : G}
    (hz : IsUniqueInvolution K z) (hb : IsUniqueInvolution L b) (hzb : z * b = b * z)
    (hne : b ≠ z) : ∃ c ∈ K ⊔ L, c * z * c⁻¹ = z * b := by
  obtain ⟨y, hy, hyK⟩ := hAE L hLs hLn z b hz hb
  have hyz : y * z * y⁻¹ = b := by
    have := hz.conj y
    rw [hyK] at this
    exact (hb.eq this).symm
  have hyKL : y ∈ K ⊔ L :=
    (sup_le_sup inf_le_left inf_le_left : pairNormalizers K L z b ≤ K ⊔ L) hy
  have hZ : ∀ w ∈ Subgroup.closure ({z, b} : Set G), w = 1 ∨ w = z ∨ w = b ∨ w = z * b :=
    fun w hw => mem_closure_pair_involutions hz.sq hb.sq hzb hw
  have hbZ : b ∈ Subgroup.closure ({z, b} : Set G) := Subgroup.subset_closure (by simp)
  have hzZ : z ∈ Subgroup.closure ({z, b} : Set G) := Subgroup.subset_closure (by simp)
  by_contra hcon
  push Not at hcon
  have hKfix : ∀ k ∈ K ⊓ Subgroup.normalizer
      ((Subgroup.closure ({z, b} : Set G) : Subgroup G) : Set G), k * b * k⁻¹ = b := by
    intro k hk
    by_contra hkb
    have hkz : k * z * k⁻¹ = z := hz.conj_eq (conjSub_eq_self_of_mem hk.1)
    have hkbZ : k * b * k⁻¹ ∈ Subgroup.closure ({z, b} : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hk.2 b).mp hbZ
    rcases hZ _ hkbZ with h | h | h | h
    · exact hb.ne_one (by simpa using h)
    · apply hne
      calc b = k⁻¹ * (k * b * k⁻¹) * k := by group
        _ = k⁻¹ * z * k := by rw [h]
        _ = k⁻¹ * (k * z * k⁻¹) * k := by rw [hkz]
        _ = z := by group
    · exact hkb h
    · refine hcon (k * y) ((K ⊔ L).mul_mem (Subgroup.mem_sup_left hk.1) hyKL) ?_
      calc k * y * z * (k * y)⁻¹ = k * (y * z * y⁻¹) * k⁻¹ := by group
        _ = k * b * k⁻¹ := by rw [hyz]
        _ = z * b := h
  have hLfix : ∀ l ∈ L ⊓ Subgroup.normalizer
      ((Subgroup.closure ({z, b} : Set G) : Subgroup G) : Set G), l * z * l⁻¹ = z := by
    intro l hl
    by_contra hlz
    have hlb : l * b * l⁻¹ = b := hb.conj_eq (conjSub_eq_self_of_mem hl.1)
    have hlzZ : l * z * l⁻¹ ∈ Subgroup.closure ({z, b} : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hl.2 z).mp hzZ
    rcases hZ _ hlzZ with h | h | h | h
    · exact hz.ne_one (by simpa using h)
    · exact hlz h
    · apply hne
      calc b = l⁻¹ * (l * b * l⁻¹) * l := by group
        _ = l⁻¹ * b * l := by rw [hlb]
        _ = l⁻¹ * (l * z * l⁻¹) * l := by rw [h]
        _ = z := by group
    · exact hcon l (Subgroup.mem_sup_right hl.1) h
  have hcommk : ∀ (k x : G), k * x * k⁻¹ = x → x * k = k * x := by
    intro k x h
    calc x * k = (k * x * k⁻¹) * k := by rw [h]
      _ = k * x := by group
  have hyC : y ∈ Subgroup.centralizer ({z, b} : Set G) := by
    have hle : pairNormalizers K L z b ≤ Subgroup.centralizer ({z, b} : Set G) := by
      unfold pairNormalizers
      refine sup_le (fun k hk => ?_) (fun l hl => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        rintro w (rfl | rfl)
        · exact hcommk k _ (hz.conj_eq (conjSub_eq_self_of_mem hk.1))
        · exact hcommk k _ (hKfix k hk)
      · rw [Subgroup.mem_centralizer_iff]
        rintro w (rfl | rfl)
        · exact hcommk l _ (hLfix l hl)
        · exact hcommk l _ (hb.conj_eq (conjSub_eq_self_of_mem hl.1))
    exact hle hy
  have h1 := (Subgroup.mem_centralizer_iff.mp hyC) z (by simp)
  apply hne
  rw [← hyz]
  calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [h1]
    _ = z := by group

end Conj

section Cases

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem mem_dComp_of_rep (hs : Std8 p f Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    (ρ : Rep Ω W) : ρ.K ∈ dComp Ω K := by
  have hc := ctxOf (partIHyp_of_std8 hs) hs.hW.1
  rw [hcomp]
  by_cases h : K = ρ.K
  · rw [← h]
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      ⟨ρ.hK, Or.inl (repElt_omegaStar hc (stdRepK hs) ρ h)⟩

theorem oddCoreOf_layerJoin_le_of_nonabelian (hs : Std8 p f Ω K J S R T W z t)
    (hcomp : dComp Ω K = dstarComp Ω K)
    (hab : ¬ ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) :
    oddCoreOf (layerJoin Ω (z * t)) ≤ sigmaNorm Ω K := by
  have hP := partIHyp_of_std8 hs
  have hc := ctxOf hP hs.hW.1
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨d, hd, e, he, hde⟩ := exists_noncomm_of_not_abelian hab
  obtain ⟨ρ, rfl⟩ := exists_rep_of_mem_muDelta hd
  obtain ⟨σ, rfl⟩ := exists_rep_of_mem_muDelta he
  have hKne : ρ.K ≠ σ.K := fun h => hde (by rw [(repElt_eq_iff hc ρ σ).mpr h])
  have hnonbr : σ.K ∉ omegaNbr Ω ρ.K := fun h => hde ((repElt_commute_iff hc ρ σ hKne).mpr h)
  have hstar : σ.K ∈ omegaStarNbr Ω ρ.K := repElt_omegaStar hc ρ σ hKne
  obtain ⟨zρ, hzρ⟩ := hΩ.exists_uniqueInvolution hp hq ρ.hK
  obtain ⟨zσ, hzσ⟩ := hΩ.exists_uniqueInvolution hp hq σ.hK
  have hzρW : zρ ∈ W := (uniqueInvolution_mem_W hp hq hΩ hs.hW.1 ρ.hK ρ.hR ρ.hRK hzρ).2
  have hzσW : zσ ∈ W := (uniqueInvolution_mem_W hp hq hΩ hs.hW.1 σ.hK σ.hR σ.hRK hzσ).2
  have hzW : z ∈ W :=
    (uniqueInvolution_mem_W hp hq hΩ hs.hW.1 hK (stdRepK hs).hR (stdRepK hs).hRK hs.hz).2
  have htW : t ∈ W :=
    (uniqueInvolution_mem_W hp hq hΩ hs.hW.1 hs.hJ.1 (stdRepJ hs).hR (stdRepJ hs).hRK hs.ht).2
  have haW : z * t ∈ W := W.mul_mem hzW htW
  have hcomm : zρ * zσ = zσ * zρ := hc.comm_W _ hzρW _ hzσW
  have hzne : zσ ≠ zρ := by
    intro h
    have hj : IsUniqueInvolution σ.K zρ := by rw [← h]; exact hzσ
    exact hKne (hnt _ ρ.hK _ ⟨σ.hK, zρ, hzρ, hj⟩).symm
  have hmρ := mem_dComp_of_rep hs hcomp ρ
  have hmσ := mem_dComp_of_rep hs hcomp σ
  have hKρ : ρ.K ≤ sigmaNorm Ω K :=
    Subgroup.le_normalizer.trans (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hmρ)
  have hKσ : σ.K ≤ sigmaNorm Ω K :=
    Subgroup.le_normalizer.trans (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hmσ)
  have hg1 : Subgroup.centralizer ({zρ} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant ρ.hK (hnt _ ρ.hK) hzρ).trans
      (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hmρ)
  have hg2 : Subgroup.centralizer ({zσ} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant σ.hK (hnt _ σ.hK) hzσ).trans
      (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hmσ)
  obtain ⟨c, hcmem, hcz⟩ := exists_conj_mul_of_aEmpty (hs.stand.aEmpty ρ.K ρ.hK) hstar hnonbr hzρ
    hzσ hcomm hzne
  have hcN : c ∈ sigmaNorm Ω K := (sup_le hKρ hKσ) hcmem
  have hg3 : Subgroup.centralizer ({zρ * zσ} : Set G) ≤ sigmaNorm Ω K := by
    refine centralizer_le_of_conj hcN ?_
    have : c⁻¹ * (zρ * zσ) * c = zρ := by rw [← hcz]; group
    rw [this]
    exact hg1
  exact oddCoreOf_layerJoin_le_of_good_pair hΩ hzρ.sq hzσ.sq hcomm hzρ.ne_one hzσ.ne_one
    (Ne.symm hzne) (mem_cenZ_iff.mpr (hc.comm_W _ hzρW _ haW))
    (mem_cenZ_iff.mpr (hc.comm_W _ hzσW _ haW)) hg1 hg2 hg3

theorem oddCoreOf_layerJoin_le_of_alpha (hs : Std8 p f Ω K J S R T W z t)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) :
    oddCoreOf (layerJoin Ω (z * t)) ≤ sigmaNorm Ω K := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have ha1 : z * t ≠ 1 := zt_ne_one hs.noTwins hs.hJ hs.hz hs.ht
  have hzA : z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have htA : t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have haA : z * t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.mul_mem _ hzA htA
  intro x hx
  have hYC : layerJoin Ω (z * t) ≤ Subgroup.centralizer ({z * t} : Set G) := by
    rw [← cenZ_eq_centralizer]
    exact layerJoin_le_cenZ _
  have hxC := oddCoreOf_le_oddCoreOf_of_normalized hYC
    (fun c hc => layerJoin_conjSub_eq hΩ (by rw [cenZ_eq_centralizer]; exact hc)) hx
  have hxz : x * z = z * x := oddCoreOf_centralizer_commutes hα haA ha1 hzA x hxC
  exact normalizer_le_sigmaNorm hΩ.conjInvariant hK
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hxz))

theorem layerJoin_le_sigmaNorm_of_lift (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {x : G} (hx : x * x = 1) {K₀ : Subgroup G} (hK : XMem Ω x K₀)
    (hcomp : dComp Ω K₀ = dstarComp Ω K₀) (hO : oddCoreOf (layerJoin Ω x) ≤ sigmaNorm Ω K₀)
    (hconn : T3.DStarConnected (layerFamQ Ω x)) : layerJoin Ω x ≤ sigmaNorm Ω K₀ := by
  refine iSup₂_le fun L hL => ?_
  obtain ⟨K', hK', rfl⟩ := hL
  obtain ⟨ν, hν, hνK⟩ := exists_oddCore_conj_mem_dstarComp hp hq hΩ hx hK hconn hK'
  rw [← hcomp] at hνK
  have hle : conjSub ν K' ≤ sigmaNorm Ω K₀ :=
    Subgroup.le_normalizer.trans (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK.1 hνK)
  have hνN : ν ∈ sigmaNorm Ω K₀ := hO hν
  intro y hy
  have hyK : y ∈ K' := layerRes_le x K' hy
  have h1 : ν * y * ν⁻¹ ∈ sigmaNorm Ω K₀ :=
    hle (mem_conjSub_iff.mpr (by simpa [mul_assoc] using hyK))
  have h2 := (sigmaNorm Ω K₀).mul_mem ((sigmaNorm Ω K₀).mul_mem ((sigmaNorm Ω K₀).inv_mem hνN) h1)
    hνN
  simpa [mul_assoc] using h2

theorem dstarConnected_layerFamQ_of_abelian [IsSimpleGroup G] (hD4 : Ih8D4Star p f)
    (hs : Std8 p f Ω K J S R T W z t) (hE4 : ¬ MuIsoE4 Ω W)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) :
    T3.DStarConnected (layerFamQ Ω (z * t)) := by
  have hP := partIHyp_of_std8 hs
  have hc := ctxOf hP hs.hW.1
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨τ, hτK, hτJ⟩ := exists_third_of_abelian hs hE4 hab
  obtain ⟨z₂, hz₂⟩ := hΩ.exists_uniqueInvolution hs.stand.odd hs.stand.five τ.hK
  let ρ : Fin 3 → Rep Ω W := ![stdRepK hs, stdRepJ hs, τ]
  let zz : Fin 3 → G := ![z, t, z₂]
  have hzz : ∀ i, IsUniqueInvolution (ρ i).K (zz i) := by
    intro i
    fin_cases i
    · exact hs.hz
    · exact hs.ht
    · exact hz₂
  have hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hs.hJ.2.1.symm
    · exact hτK.symm
    · exact hs.hJ.2.1
    · exact absurd rfl hij
    · exact hτJ.symm
    · exact hτK
    · exact hτJ
    · exact absurd rfl hij
  have hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j hij
    refine (repElt_commute_iff hc (ρ i) (ρ j) (hne i j hij)).mp ?_
    exact Subtype.ext (hab _ (repElt (ρ i)).2 _ (repElt (ρ j)).2)
  exact dstarConnected_layerFamQ_of_reps hD4 hP hs.hW.1 (hs.stand.below f hs.stand.five) hnt ρ zz
    hzz hne hnbr (zt_not_central hs)

theorem rLayer_le_layerJoin (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {x : G} (hx : x * x = 1) :
    rLayer Ω x ≤ layerJoin Ω x := by
  unfold rLayer
  refine iSup₂_le fun X hX => iSup_le fun hXc => ?_
  have hxX : ∀ y ∈ X, x * y = y * x := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hXc hy)).symm
  obtain ⟨M, z', hM, hXM, -, -⟩ := exists_xMem_of_mem_RSet hp hq hΩ hnt hX hxX
  have hXx : X ≤ cenZ x := fun y hy => mem_cenZ_iff.mpr (hxX y hy).symm
  exact (hM.isSylow2In_layerRes_of_le hp hq hΩ hx hXM hXx).1.trans (le_layerJoin ⟨M, hM, rfl⟩)

theorem centralizer_le_sigmaNorm_of_layerJoin_le [IsSimpleGroup G]
    (hs : Std8 p f Ω K J S R T W z t) (hY : layerJoin Ω (z * t) ≤ sigmaNorm Ω K) :
    Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have ha2 : z * t * (z * t) = 1 := mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hKx : XMem Ω (z * t) K := xMem_zt hs
  have hn : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  have hlt := card_layerQuot_lt (Ω := Ω) (zt_not_central hs)
  intro c hc
  have hcz : c ∈ cenZ (z * t) := by
    rw [cenZ_eq_centralizer]
    exact hc
  have hKc : XMem Ω (z * t) (conjSub c K) := hKx.conj hΩ hcz
  rw [mem_sigmaNorm_iff hΩ.conjInvariant hK]
  rcases layer_dichotomy hp hq hΩ hnt ha2 hn hlt hKx hKc with ⟨y, hy, hyc⟩ | ⟨m, hm, hmc⟩
  · rw [hyc]
    exact (mem_sigmaNorm_iff hΩ.conjInvariant hK).1 (hY hy)
  · have hmK := (mem_sigmaNorm_iff hΩ.conjInvariant hK).1 (hY hm)
    exact hmK.trans (Relation.ReflTransGen.single ⟨hKc.1, Or.inl hmc⟩)

end Cases

end T8

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C27_7ab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoE4 Ω W →
        (∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) →
          alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥

@[expose] def C27_Ysmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoE4 Ω W →
        (¬ ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) →
          ¬ T3.DStarConnected (T8.layerFamQ Ω (z * t)) →
            T8.layerJoin Ω (z * t) ≤ sigmaNorm Ω K

@[expose] def C27_YnE4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoE4 Ω W → rLayer Ω (z * t) ≤ sigmaNorm Ω K

@[expose] def C27_YE4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoE4 Ω W → rLayer Ω (z * t) ≤ sigmaNorm Ω K

variable {p f}

theorem c27_YnE4_of_core (hD4 : Ih8D4Star p f) (h2 : C27_2 p f) (h7 : C27_7ab p f)
    (hY : C27_Ysmall p f) : C27_YnE4 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hKx : T8.XMem Ω (z * t) K := T8.xMem_zt hs
  have hcomp := h2 G Ω K J S R T W z t hs hdisc
  have hlayer : T8.layerJoin Ω (z * t) ≤ sigmaNorm Ω K := by
    by_cases hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x
    · exact T8.layerJoin_le_sigmaNorm_of_lift hp hq hΩ hx hKx hcomp
        (T8.oddCoreOf_layerJoin_le_of_alpha hs (h7 G Ω K J S R T W z t hs hdisc hE4 hab))
        (T8.dstarConnected_layerFamQ_of_abelian hD4 hs hE4 hab)
    · by_cases hconn : T3.DStarConnected (T8.layerFamQ Ω (z * t))
      · exact T8.layerJoin_le_sigmaNorm_of_lift hp hq hΩ hx hKx hcomp
          (T8.oddCoreOf_layerJoin_le_of_nonabelian hs hcomp hab) hconn
      · exact hY G Ω K J S R T W z t hs hdisc hE4 hab hconn
  exact (T8.rLayer_le_layerJoin hp hq hΩ hnt hx).trans hlayer

theorem c27_Y_of_split (hE : C27_YE4 p f) (hn : C27_YnE4 p f) : C27_Y p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  by_cases hE4 : MuIsoE4 Ω W
  · exact hE G Ω K J S R T W z t hs hdisc hE4
  · exact hn G Ω K J S R T W z t hs hdisc hE4


end CFSG.ClassicalInvolution.Asc77
