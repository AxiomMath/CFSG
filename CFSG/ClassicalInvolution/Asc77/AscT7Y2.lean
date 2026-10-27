module

public import CFSG.ClassicalInvolution.Asc77.AscT7Y1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace T7Y

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

section Basic

omit [IsSimpleGroup G] in
theorem exists_noncomm (hst : AscStand p f Ω K) : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  obtain ⟨x, -, y, -, hxy⟩ :=
    (hst.hyp.isQuatSub_of_mem_RSet hst.odd (mem_RSet_of_isSylow2In hst.mem hV)).exists_not_commute
  exact ⟨x, y, hxy⟩

omit [IsSimpleGroup G] in
theorem mem_normalizer_exactLayer {c h : G} (hΩ : ConjInvariant Ω)
    (hh : h ∈ Subgroup.centralizer ({c} : Set G)) :
    h ∈ Subgroup.normalizer (exactLayer Ω c : Set G) :=
  mem_normalizer_iff_conjSub_eq.mpr (conjSub_exactLayer hΩ hh)

end Basic

theorem not_mem_zStar (htcf : TwinCentralFact p) (hgen : E4TwinGen p)
    (hG : Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤)
    (hΓu : Subgroup.centralizer ({u} : Set G) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)))
    (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    u * e ∉ zStarOf (rLayer Ω u) := by
  intro htZ
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hα := alphaOf_eq_bot hG hΓu hs hd
  obtain ⟨-, halpha⟩ := T7K.c23_5X_one_proved hs hd
  rw [rLayer_eq_exactLayer hp hq hΩ hd.hu2] at htZ
  obtain ⟨hzB, huB, heB⟩ := T7K.generators_mem_B z u e
  have hBel := T7K.B_isElemAbelian hs hd
  have htB : u * e ∈ Subgroup.closure ({u * e, u, z} : Set G) := Subgroup.mul_mem _ huB heB
  have sq : ∀ x ∈ Subgroup.closure ({u * e, u, z} : Set G), x * x = 1 := fun x hx => by
    have := hBel.2 x hx
    rwa [pow_two] at this
  obtain ⟨⟨ht1, htu⟩, -⟩ := T7L.B_ne hs hd
  have ht2 : (u * e) * (u * e) = 1 := sq _ htB
  have hcomm := T7A.commutes_closure (T7K.comm_gen hs hd)
  have hut : u * (u * e) = (u * e) * u := hcomm u huB (u * e) htB
  have hA : IsElemAbelian2 (Subgroup.closure ({u, u * e} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hd.hu2 ht2 hd.hu1 ht1 (Ne.symm htu) hut
  have hAB : Subgroup.closure ({u, u * e} : Set G) ≤
      Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact huB
    · exact htB
  have hαA : alphaOf (Subgroup.closure ({u, u * e} : Set G)) = ⊥ := (halpha _ hAB hA).trans hα
  have hBN : ∀ b ∈ Subgroup.centralizer ({u} : Set G),
      b ∈ Subgroup.normalizer (oddCoreOf (exactLayer Ω u) : Set G) := fun b hb =>
    T7L.mem_normalizer_oddCoreOf (mem_normalizer_exactLayer hΩ.conjInvariant hb)
  have hOY : oddCoreOf (exactLayer Ω u) ≤ oddCoreOf (Subgroup.centralizer ({u} : Set G)) :=
    le_oddCoreIn_of_normalizes ((oddCoreIn_le _).trans (exactLayer_le_centralizer Ω u)) hBN
      (oddCoreOf_odd_natCard _)
  obtain ⟨x₀, hx₀, hx₀t⟩ := Subgroup.mem_map.mp htZ
  have htY : u * e ∈ exactLayer Ω u := hx₀t ▸ x₀.2
  have hYt : ∀ y ∈ exactLayer Ω u, y * (u * e) = (u * e) * y := by
    intro y hy
    set N₀ := classicalInvolutionOddCore ↥(exactLayer Ω u) with hN₀
    have hcen := Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hx₀)
      (QuotientGroup.mk' N₀ ⟨y⁻¹, Subgroup.inv_mem _ hy⟩)
    have hx₀' : x₀ = ⟨u * e, htY⟩ := Subtype.ext hx₀t
    rw [hx₀'] at hcen
    have hmk : QuotientGroup.mk' N₀ ⟨y⁻¹, Subgroup.inv_mem _ hy⟩ *
        QuotientGroup.mk' N₀ ⟨u * e, htY⟩ *
        (QuotientGroup.mk' N₀ ⟨y⁻¹, Subgroup.inv_mem _ hy⟩)⁻¹ =
        QuotientGroup.mk' N₀ ⟨u * e, htY⟩ := by
      rw [hcen, mul_inv_cancel_right]
    have ho := T7L.mem_oddCore_of_mk_conj htY htY ⟨y⁻¹, Subgroup.inv_mem _ hy⟩ hmk
    simp only [inv_inv] at ho
    set o : G := (u * e)⁻¹ * (y * (u * e) * y⁻¹) with hodef
    have hoN : o ∈ oddCoreOf (Subgroup.centralizer ({u} : Set G)) := hOY ho
    have hot : o * (u * e) = (u * e) * o :=
      commute_of_alphaOf_eq_bot (Subgroup.subset_closure (by simp)) hd.hu1 hαA hoN
        (Subgroup.subset_closure (by simp))
    have hyt : y * (u * e) * y⁻¹ = (u * e) * o := by simp only [hodef]; group
    have hsq : ((u * e) * o) * ((u * e) * o) = 1 := by
      rw [← hyt]
      calc (y * (u * e) * y⁻¹) * (y * (u * e) * y⁻¹) = y * ((u * e) * (u * e)) * y⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have hoo : o * o = 1 := by
      have h1 : ((u * e) * o) * ((u * e) * o) = o * o := by
        calc ((u * e) * o) * ((u * e) * o) = (u * e) * (o * (u * e)) * o := by group
          _ = (u * e) * ((u * e) * o) * o := by rw [hot]
          _ = ((u * e) * (u * e)) * (o * o) := by group
          _ = o * o := by rw [ht2, one_mul]
      exact h1.symm.trans hsq
    have ho1 : o = 1 := eq_one_of_sq_eq_one_of_mem_odd (oddCoreOf_odd_natCard _) ho hoo
    rw [ho1, mul_one] at hyt
    exact mul_inv_eq_iff_eq_mul.mp hyt
  have hCue : ∀ h ∈ Subgroup.centralizer ({u} : Set G), h * e = e * h := by
    intro h hh
    obtain ⟨y, hy, c, hc, rfl⟩ := exists_mul_centralizer_u htcf hgen hs hd hh
    have hct : c * (u * e) = (u * e) * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hyt := hYt y hy
    have hht : (y * c) * (u * e) = (u * e) * (y * c) := by
      calc (y * c) * (u * e) = y * (c * (u * e)) := mul_assoc _ _ _
        _ = y * ((u * e) * c) := by rw [hct]
        _ = (y * (u * e)) * c := (mul_assoc _ _ _).symm
        _ = ((u * e) * y) * c := by rw [hyt]
        _ = (u * e) * (y * c) := mul_assoc _ _ _
    have hhu : (y * c) * u = u * (y * c) := Subgroup.mem_centralizer_singleton_iff.mp hh
    exact comm_e_of_comm_u_ue hd.hu2 hhu hht
  obtain ⟨R, R', hR, hR', -, hRN, hR'N⟩ := T7K.exists_sylow_D hs hd
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hKe := le_centralizer_e hs hd hα hst.mem hs.hz hR hRN
  have hK'e := le_centralizer_e hs hd hα hs.hK'.1 hzK' hR' hR'N
  have hCze : ∀ c ∈ Subgroup.centralizer ({z} : Set G), c * e = e * c := by
    intro c hc
    obtain ⟨r, hr, c₀, hc₀, hcm, rfl⟩ :=
      T7K.centralizer_eq_sup_mul hs hd.hu hd.hu1 hd.huz hd.hu2 hc
    have hre : r * e = e * r := Subgroup.mem_centralizer_singleton_iff.mp ((sup_le hKe hK'e) hr)
    have hc₀e : c₀ * e = e * c₀ := hCue c₀ (Subgroup.mem_centralizer_singleton_iff.mpr hcm)
    calc (r * c₀) * e = r * (c₀ * e) := mul_assoc _ _ _
      _ = r * (e * c₀) := by rw [hc₀e]
      _ = (r * e) * c₀ := (mul_assoc _ _ _).symm
      _ = (e * r) * c₀ := by rw [hre]
      _ = e * (r * c₀) := mul_assoc _ _ _
  refine hd.he1 (T7B.eq_one_of_central (exists_noncomm hst) (fun x => ?_))
  have hle : Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.centralizer ({e} : Set G) :=
    sup_le (fun h hh => Subgroup.mem_centralizer_singleton_iff.mpr (hCue h hh))
      (fun c hc => Subgroup.mem_centralizer_singleton_iff.mpr (hCze c hc))
  have hx : x ∈ Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) :=
    hG ▸ Subgroup.mem_top x
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem sup_layers_eq_top (htcf : TwinCentralFact p) (hgen : E4TwinGen p)
    (hG : Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤)
    (hΓu : Subgroup.centralizer ({u} : Set G) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)))
    (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    rLayer Ω e ⊔ rLayer Ω u = ⊤ := by
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hα := alphaOf_eq_bot hG hΓu hs hd
  rw [rLayer_eq_exactLayer hp hq hΩ hd.he2, rLayer_eq_exactLayer hp hq hΩ hd.hu2]
  obtain ⟨R, R', hR, hR', -, hRN, hR'N⟩ := T7K.exists_sylow_D hs hd
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hLE : ∀ {L : Subgroup G} {R₀ : Subgroup G}, L ∈ Ω → IsUniqueInvolution L z →
      IsSylow2In R₀ L → R₀ ≤ Subgroup.normalizer (W : Set G) → L ≤ exactLayer Ω e := by
    intro L R₀ hLΩ hzL hR₀ hR₀N
    have hLe : L ≤ Subgroup.centralizer ({e} : Set G) :=
      le_centralizer_e hs hd hα hLΩ hzL hR₀ hR₀N
    have hcl : IsClassicalMember p f L z := isClassicalMember_of_twin hΩ hLΩ hzL
    have hLt : L ∈ tqMembers Ω e := ⟨hLΩ, mem_trivialOnQuot_of_le_centralizer hLe⟩
    have h1 := exactCore_le_exactLayer hLt
    rwa [exactCore_eq_self hcl.perfect hLe] at h1
  have hKE : K ≤ exactLayer Ω e := hLE hst.mem hs.hz hR hRN
  have hK'E : K' ≤ exactLayer Ω e := hLE hs.hK'.1 hzK' hR' hR'N
  set E := exactLayer Ω e with hEdef
  set Y := exactLayer Ω u with hYdef
  have hCu : ∀ h ∈ Subgroup.centralizer ({u} : Set G),
      h ∈ Subgroup.normalizer ((E ⊔ Y : Subgroup G) : Set G) := by
    intro h hh
    obtain ⟨y, hy, c, hc, rfl⟩ := exists_mul_centralizer_u htcf hgen hs hd hh
    refine Subgroup.mul_mem _ (Subgroup.le_normalizer ((le_sup_right : Y ≤ E ⊔ Y) hy)) ?_
    have hce : c ∈ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (comm_e_of_comm_u_ue hd.hu2 (Subgroup.mem_centralizer_singleton_iff.mp hc.1)
          (Subgroup.mem_centralizer_singleton_iff.mp hc.2))
    exact Subgroup.inf_normalizer_le_normalizer_sup E Y
      ⟨mem_normalizer_exactLayer hΩ.conjInvariant hce,
        mem_normalizer_exactLayer hΩ.conjInvariant hc.1⟩
  have hCz : ∀ c ∈ Subgroup.centralizer ({z} : Set G),
      c ∈ Subgroup.normalizer ((E ⊔ Y : Subgroup G) : Set G) := by
    intro c hc
    obtain ⟨r, hr, c₀, hc₀, hcm, rfl⟩ :=
      T7K.centralizer_eq_sup_mul hs hd.hu hd.hu1 hd.huz hd.hu2 hc
    refine Subgroup.mul_mem _ ?_ (hCu c₀ (Subgroup.mem_centralizer_singleton_iff.mpr hcm))
    exact Subgroup.le_normalizer ((le_sup_left : E ≤ E ⊔ Y) (sup_le hKE hK'E hr))
  have hN : Subgroup.normalizer ((E ⊔ Y : Subgroup G) : Set G) = ⊤ := by
    rw [eq_top_iff, ← hG]
    exact sup_le hCu hCz
  have hnormal : (E ⊔ Y).Normal := Subgroup.normalizer_eq_top_iff.mp hN
  rcases hnormal.eq_bot_or_eq_top with h | h
  · exfalso
    have hzE : z ∈ E ⊔ Y := (le_sup_left : E ≤ E ⊔ Y) (hKE hs.hz.mem)
    rw [h] at hzE
    exact hs.hz.ne_one (Subgroup.mem_bot.mp hzE)
  · exact h

end T7Y

end CFSG.ClassicalInvolution.Asc77
