module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWQuotCent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf182
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW189a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf4Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmQ8CentEng
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf16Orbit

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section QuotCentPf

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

private theorem relIndex_two_of_card' {U R : Subgroup G} (hUR : U ≤ R)
    (hcard : Nat.card R = 2 * Nat.card U) : U.relIndex R = 2 := by
  have h := Subgroup.relIndex_mul_card (H := U) (K := R)
  rw [inf_eq_left.mpr hUR] at h
  have hpos : 0 < Nat.card U := Nat.card_pos
  have : (U.relIndex R) * Nat.card U = 2 * Nat.card U := by rw [hcard] at h; rw [h]
  exact Nat.eq_of_mul_eq_mul_right hpos this

private theorem natCard_map_of_inf_eq_bot {A : Subgroup G} (h : A ⊓ N = ⊥) :
    Nat.card ↥(A.map (QuotientGroup.mk' N)) = Nat.card A :=
  (Nat.card_congr (AscQuot.quotRestrictEquiv h).toEquiv).symm

private theorem inf_eq_bot_of_le_member (c : CentQuotGen Ω N) {A J : Subgroup G} (hJ : J ∈ Ω)
    (hAJ : A ≤ J) : A ⊓ N = ⊥ :=
  eq_bot_iff.mpr ((inf_le_inf_right N hAJ).trans (c.meet J hJ).le)

private theorem mem_of_map_mem_of_le {T : Subgroup G} (hNT : N ≤ T) {x : G}
    (hx : QuotientGroup.mk' N x ∈ T.map (QuotientGroup.mk' N)) : x ∈ T := by
  have h2 := (Subgroup.mem_comap).mpr hx
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNT] at h2

theorem quotCent_map_mem_USet (c : CentQuotGen Ω N) {U : Subgroup G} (hU : U ∈ USet Ω) :
    U.map (QuotientGroup.mk' N) ∈ USet (quotFamily Ω N) := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hRN : R ⊓ N = ⊥ := inf_eq_bot_of_le_member c hJ hRJ.1
  have hUN : U ⊓ N = ⊥ := inf_eq_bot_of_le_member c hJ (hUR.trans hRJ.1)
  have hcard : Nat.card R = 2 * Nat.card U := by
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR] at h1
    have : U.relIndex R = 2 := hidx
    rw [this] at h1
    omega
  refine ⟨R.map (QuotientGroup.mk' N), mem_RSet_of_isSylow2In (map_mem_quotFamily hJ)
    (CentEng.isSylow2In_map_cent c hJ hRJ), Subgroup.map_mono hUR, ?_, ?_⟩
  · exact ((AscQuot.quotRestrictEquiv hUN).isCyclic).mp hcyc
  · refine relIndex_two_of_card' (Subgroup.map_mono hUR) ?_
    rw [natCard_map_of_inf_eq_bot hRN, natCard_map_of_inf_eq_bot hUN, hcard]

theorem quotCent_lift_USet (c : CentQuotGen Ω N) {T : Subgroup G} (hNT : N ≤ T)
    {Ub : Subgroup (G ⧸ N)} (hUb : Ub ∈ USet (quotFamily Ω N))
    (hle : Ub ≤ T.map (QuotientGroup.mk' N)) {J : Subgroup G} (hJ : J ∈ Ω)
    (hUbJ : Ub ≤ J.map (QuotientGroup.mk' N)) :
    ∃ U ∈ USet Ω, U ≤ J ∧ U ≤ T ∧ U.map (QuotientGroup.mk' N) = Ub := by
  obtain ⟨U, hU, hUJ, hUmap⟩ := c.exists_lift_USet hJ hUb hUbJ
  refine ⟨U, hU, hUJ, fun x hx => ?_, hUmap⟩
  refine mem_of_map_mem_of_le hNT ?_
  exact hle (hUmap ▸ Subgroup.mem_map_of_mem _ hx)

theorem quotCent_exists_member_of_map_le (c : CentQuotGen Ω N) {U : Subgroup G} (hU : U ∈ USet Ω)
    {J : Subgroup G} (hJ : J ∈ Ω) (h : U.map (QuotientGroup.mk' N) ≤ J.map (QuotientGroup.mk' N)) :
    U ≤ J := by
  obtain ⟨J₁, hJ₁, hUJ₁⟩ := Sec6Gen.exists_member_of_mem_USet c.hyp hU
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := c.hyp.exists_data_of_mem_USet hU
  have h4' : 4 ≤ Nat.card ↥(U.map (QuotientGroup.mk' N)) := by
    rw [natCard_map_of_inf_eq_bot (inf_eq_bot_of_le_member c hJ₁ hUJ₁)]; exact h4
  have hJ12 : J₁.map (QuotientGroup.mk' N) = J.map (QuotientGroup.mk' N) :=
    c.hyp'.eq_of_le_of_le (map_mem_quotFamily hJ₁) (map_mem_quotFamily hJ)
      (c.hyp'.isPGroup_of_mem_USet (quotCent_map_mem_USet c hU)) h4' (Subgroup.map_mono hUJ₁) h
  have : J₁ = J := c.eq_of_map J₁ hJ₁ J hJ hJ12
  exact this ▸ hUJ₁

theorem quotCent_map_mem_WSet (c : CentQuotGen Ω N) (hN2 : IsPGroup 2 ↥N) {W : Subgroup G}
    (hW : W ∈ WSet Ω) : W.map (QuotientGroup.mk' N) ∈ WSet (quotFamily Ω N) := by
  obtain ⟨η, ⟨T, hη, hinv⟩, rfl⟩ := hW
  set π := QuotientGroup.mk' N with hπ
  have hNT : N ≤ (T : Subgroup G) := hN2.le_sylow_of_normal T
  let Tb : Sylow 2 (G ⧸ N) := Sylow.mapSurjective (f := π) (QuotientGroup.mk'_surjective N) T
  have hTb : (Tb : Subgroup (G ⧸ N)) = (T : Subgroup G).map π :=
    Sylow.coe_mapSurjective (f := π) (QuotientGroup.mk'_surjective N) T
  have hUle : ∀ U ∈ η, U ≤ (T : Subgroup G) := fun U hU => (hη.1 hU).2
  set ηb : Set (Subgroup (G ⧸ N)) := (fun U => U.map π) '' η with hηb
  have hηb_set : ηb ∈ etaSet (quotFamily Ω N) (Tb : Subgroup (G ⧸ N)) := by
    refine Sec6Gen.mem_etaSet_of_cover c.hyp' ?_ ?_ ?_
    · rintro _ ⟨U, hU, rfl⟩
      exact ⟨quotCent_map_mem_USet c (hη.1 hU).1, hTb ▸ Subgroup.map_mono (hUle U hU)⟩
    · rintro _ ⟨U₁, hU₁, rfl⟩ _ ⟨U₂, hU₂, rfl⟩ hne _ ⟨J₀, hJ₀, rfl⟩ ⟨h1, h2⟩
      have hne' : U₁ ≠ U₂ := fun h => hne (by rw [h])
      exact hη.2.1 U₁ hU₁ U₂ hU₂ hne' J₀ hJ₀
        ⟨quotCent_exists_member_of_map_le c (hη.1 hU₁).1 hJ₀ h1,
          quotCent_exists_member_of_map_le c (hη.1 hU₂).1 hJ₀ h2⟩
    · rintro _ ⟨J₀, hJ₀, rfl⟩ ⟨Ub, hUb, hUbJ⟩
      obtain ⟨U, hU, hUJ, hUT, -⟩ := quotCent_lift_USet c hNT hUb.1 (hTb ▸ hUb.2) hJ₀ hUbJ
      obtain ⟨V, hV, hVJ⟩ := Sec6Gen.exists_mem_of_mem_etaSet c.hyp hη hJ₀ ⟨hU, hUT⟩ hUJ
      exact ⟨V.map π, ⟨V, hV, rfl⟩, Subgroup.map_mono hVJ⟩
  refine ⟨ηb, ⟨Tb, hηb_set, ?_⟩, ?_⟩
  · rintro sb hsb _ ⟨U, hU, rfl⟩
    rw [hTb] at hsb
    obtain ⟨s, hs, rfl⟩ := hsb
    exact ⟨conjSub s U, hinv s hs U hU, AscQuot.map_conjSub π s U⟩
  · rw [hηb, Subgroup.map_iSup]
    simp only [Subgroup.map_iSup, iSup_image]

theorem quotCent_mem_of_commutes (hΩ : HypOmegaGen Ω) {M R' U : Subgroup G} (hM : M ∈ Ω)
    (hR' : IsSylow2In R' M) (hUR : U ≤ R') (hUc : IsCyclic ↥U)
    (hcard : Nat.card R' = 2 * Nat.card U) (h4 : 4 ≤ Nat.card U) {a : G} (ha : a ∈ R')
    (hcomm : ∀ u ∈ U, a * u = u * a) : a ∈ U := by
  have hq := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hM hR')
  have hUC : U ≤ Subgroup.centralizer (U : Set G) ⊓ R' := fun u hu =>
    ⟨Subgroup.mem_centralizer_iff.mpr fun v hv => AscL62.cyclic_comm hUc hv hu, hUR hu⟩
  rcases eq_or_eq_of_natCard_eq_two_mul hUC (inf_le_right : _ ≤ R') hcard with h | h
  · rw [← h]
    exact ⟨Subgroup.mem_centralizer_iff.mpr fun v hv => (hcomm v hv).symm, ha⟩
  · exfalso
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥U)
    have hgord : orderOf g = Nat.card U := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgR : (g : G) ∈ R' := hUR g.2
    have hcen : ∀ y ∈ R', (g : G) * y = y * g := by
      intro y hy
      have : y ∈ Subgroup.centralizer (U : Set G) ⊓ R' := by rw [h]; exact hy
      exact Subgroup.mem_centralizer_iff.mp this.1 g g.2
    have hgg := hq.sq_eq_one_of_central hgR hcen
    have h2 : orderOf (g : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgg)
    have h3 : orderOf (g : G) ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    rw [Subgroup.orderOf_coe, hgord] at h3
    omega

private theorem inf_sylow_eq {S : Sylow 2 G} {M R' : Subgroup G} (hR' : IsSylow2In R' M)
    (hR'S : R' ≤ (S : Subgroup G)) : M ⊓ (S : Subgroup G) = R' :=
  hR'.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left (le_inf hR'.1 hR'S)

theorem quotCent_mem_inf_W_of_commutes (hΩ : HypOmegaGen Ω) {S : Sylow 2 G} {W M R' : Subgroup G}
    (hM : M ∈ Ω) (hR'M : IsSylow2In R' M) (hR'S : R' ≤ (S : Subgroup G)) (hWS : W ≤ (S : Subgroup G))
    (hMW : M ⊓ W ∈ USet Ω) {a : G} (ha : a ∈ R') (hcomm : ∀ x ∈ M ⊓ W, a * x = x * a) :
    a ∈ M ⊓ W := by
  obtain ⟨R₂, -, J₂, hJ₂, hR₂, hUR₂, hUc, hcard₂, h4⟩ := hΩ.exists_data_of_mem_USet hMW
  have hJ₂M : J₂ = M :=
    Sec6Gen.eq_of_mem_USet hΩ hMW hJ₂ hM (hUR₂.trans hR₂.1) inf_le_left
  subst hJ₂M
  have hUR' : J₂ ⊓ W ≤ R' := by
    intro x hx
    have : x ∈ J₂ ⊓ (S : Subgroup G) := ⟨hx.1, hWS hx.2⟩
    rwa [inf_sylow_eq hR'M hR'S] at this
  have hRcard : Nat.card ↥R' = 2 * Nat.card ↥(J₂ ⊓ W) := by
    rw [← hR₂.natCard_eq hR'M]
    exact hcard₂
  exact quotCent_mem_of_commutes hΩ hM hR'M hUR' hUc hRcard h4 ha hcomm

section MinCexLemmas

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem quotCent_mem_of_mem_dstarComp {K M : Subgroup G} (hK : K ∈ Ω) (hM : M ∈ dstarComp Ω K) : M ∈ Ω := by
  rcases Relation.ReflTransGen.cases_tail hM with rfl | ⟨b, -, hb⟩
  · exact hK
  · exact hb.1

theorem MinCexQ8.quotCent_centralizer_le_mul (c : MinCexQ8 Ω K S R W H) {M : Subgroup G}
    (hM : M ∈ dstarComp Ω K) {J : Subgroup G} (hJ : J ∈ omegaNbr Ω M) {z t : G}
    (hz : IsUniqueInvolution M z) (ht : IsUniqueInvolution J t) (ha1 : z * t ≠ 1)
    (ha2 : (z * t) * (z * t) = 1) : Subgroup.centralizer ({z * t} : Set G) ≤ H := by
  obtain ⟨h, hhH, hh⟩ := c.hyp.trans M hM
  subst hh
  have c' := c.conj_of_mem hhH
  exact centralizer_le_mul_of_omegaNbr c'.stand.hyp c'.stand.mem c'.hyp.trans hz
    (c'.centralizer_le hz) c'.stand.hR.1 c'.stand.hR.2.1 c'.stand.hR.2.2 c'.stand.hW.1
    c'.stand.hW.2.1 c'.stand.hW.2.2 c'.hyp.cent hJ ht ha1 ha2

theorem quotCent_central_involution_cases (hΩ : HypOmegaGen Ω) {M J R' T' : Subgroup G} (hM : M ∈ Ω)
    (hJ : J ∈ Ω) (hR' : IsSylow2In R' M) (hT' : IsSylow2In T' J) (hcomm : Commutes R' T') {z t : G}
    (hz : IsUniqueInvolution M z) (ht : IsUniqueInvolution J t) {e : G} (he : e ∈ R' ⊔ T')
    (he1 : e ≠ 1) (he2 : e * e = 1) (hcen : ∀ g : G, g * e = e * g) :
    e = z ∨ e = t ∨ e = z * t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hcomm he
  have hqR := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hM hR')
  have hqT := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ hT')
  have haa : a * a = 1 := by
    refine hqR.sq_eq_one_of_central ha fun r hr => ?_
    have h1 := hcen r
    have h2 : r * b = b * r := hcomm r hr b hb
    have h3 : r * a * b = a * r * b := by
      calc r * a * b = r * (a * b) := by group
        _ = a * b * r := h1
        _ = a * (b * r) := by group
        _ = a * (r * b) := by rw [h2]
        _ = a * r * b := by group
    exact (mul_right_cancel h3).symm
  have hbb : b * b = 1 := by
    refine hqT.sq_eq_one_of_central hb fun r hr => ?_
    have h1 := hcen r
    have h2 : a * r = r * a := hcomm a ha r hr
    have h3 : a * (r * b) = a * (b * r) := by
      calc a * (r * b) = a * r * b := by group
        _ = r * a * b := by rw [h2]
        _ = r * (a * b) := by group
        _ = a * b * r := h1
        _ = a * (b * r) := by group
    exact (mul_left_cancel h3).symm
  rcases hz.unique a (hR'.1 ha) haa with rfl | rfl <;>
    rcases ht.unique b (hT'.1 hb) hbb with rfl | rfl
  · exact absurd (by simp) he1
  · right; left; simp
  · left; simp
  · right; right; rfl

end MinCexLemmas

section Lift

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem quotCent_sup_inf_eq_bot (c : MinCexQ8 Ω K S R W H) (hN2 : IsPGroup 2 ↥N)
    (hNc : N ≤ Subgroup.center G) (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥) {M J R₁ R₂ : Subgroup G}
    (hM : M ∈ dstarComp Ω K) (hJ : J ∈ KPerp Ω M) (hR₁ : R₁ ∈ RSet Ω) (hR₁M : R₁ ≤ M)
    (hR₂ : R₂ ∈ RSet Ω) (hR₂J : R₂ ≤ J) (hcomm : Commutes R₁ R₂ ∨ R₂ = R₁) :
    (R₁ ⊔ R₂) ⊓ N = ⊥ := by
  by_contra hne
  have hΩ := c.stand.hyp
  have hMΩ : M ∈ Ω := quotCent_mem_of_mem_dstarComp c.stand.mem hM
  obtain ⟨e, he, he1, he2⟩ := AscE186.exists_involution_of_ne_bot (hN2.to_le inf_le_right) hne
  have hcen : ∀ g : G, g * e = e * g := Subgroup.mem_center_iff.mp (hNc he.2)
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hMΩ
  rcases hJ with hJM | hJn
  ·
    have heM : e ∈ M ⊓ N := ⟨(sup_le hR₁M (hJM ▸ hR₂J)) he.1, he.2⟩
    rw [hmeet M hMΩ, Subgroup.mem_bot] at heM
    exact he1 heM
  · have hJΩ : J ∈ Ω := hJn.1
    obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJΩ
    have hR₁syl : IsSylow2In R₁ M := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hMΩ hR₁ hR₁M
    have hR₂syl : IsSylow2In R₂ J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hR₂ hR₂J
    have hcm : Commutes R₁ R₂ := by
      rcases hcomm with h | h
      · exact h
      · exfalso
        have h2 := Sec6Gen.card_le_two_of_le_inf hΩ hMΩ hJΩ hJn.2.1.symm hR₁syl.2.1 hR₁M
          (h ▸ hR₂J)
        have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR₁
        omega
    rcases quotCent_central_involution_cases hΩ hMΩ hJΩ hR₁syl hR₂syl hcm hz ht he.1 he1 he2
      hcen with h | h | h
    · have h' : e ∈ M ⊓ N := ⟨h ▸ hz.mem, he.2⟩
      rw [hmeet M hMΩ, Subgroup.mem_bot] at h'
      exact he1 h'
    · have h' : e ∈ J ⊓ N := ⟨h ▸ ht.mem, he.2⟩
      rw [hmeet J hJΩ, Subgroup.mem_bot] at h'
      exact he1 h'
    · subst h
      have hC := c.quotCent_centralizer_le_mul hM hJn hz ht he1 he2
      apply c.proper
      rw [eq_top_iff]
      intro g _
      exact hC (Subgroup.mem_centralizer_singleton_iff.mpr (hcen g))

theorem quotCent_exists_lift (c : MinCexQ8 Ω K S R W H)
    (hN2 : IsPGroup 2 ↥N) (hNc : N ≤ Subgroup.center G) (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥)
    {M J R₁ R₂ : Subgroup G} (hMΩ : M ∈ Ω) (hMW : M ⊓ W ∈ USet Ω) (hJ : J ∈ KPerp Ω M)
    (hR₁ : R₁ ∈ RSet Ω) (hR₁M : R₁ ≤ M) (hR₁S : R₁ ≤ (S : Subgroup G))
    (hR₂ : R₂ ∈ RSet Ω) (hR₂J : R₂ ≤ J) (hR₂S : R₂ ≤ (S : Subgroup G))
    (hcomm : Commutes R₁ R₂ ∨ R₂ = R₁) {y w : G} (hy : y ∈ R₁ ⊔ R₂) (hw : w ∈ W)
    (hyw : QuotientGroup.mk' N y = QuotientGroup.mk' N w) (hy1 : QuotientGroup.mk' N y ≠ 1)
    (hy2 : QuotientGroup.mk' N y * QuotientGroup.mk' N y = 1) :
    y ≠ 1 ∧ y * y = 1 ∧ y ∈ W ∧ Subgroup.centralizer ({y} : Set G) ≤ H ∧
      ∃ u ∈ M, orderOf u = 4 ∧ u * y = y * u := by
  have hΩ := c.stand.hyp
  obtain ⟨hWmem, hWS, hWn⟩ := c.stand.hW
  have hK := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have habel := habel_of_WSet hΩ hWmem
  have hKW : K ⊓ W ∈ USet Ω := inf_W_mem_USet' hΩ hWmem hWS hK hRR hRK hRS
  have hMsg : M ∈ dstarComp Ω K := mem_dstarComp_of_inf_W hΩ hWmem hK hMΩ hKW hMW
  have hJΩ : J ∈ Ω := by
    rcases hJ with rfl | hJn
    · exact hMΩ
    · exact hJn.1
  have hR₁syl : IsSylow2In R₁ M := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hMΩ hR₁ hR₁M
  have hR₂syl : IsSylow2In R₂ J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hR₂ hR₂J
  have hbot : (R₁ ⊔ R₂) ⊓ N = ⊥ :=
    quotCent_sup_inf_eq_bot c hN2 hNc hmeet hMsg hJ hR₁ hR₁M hR₂ hR₂J hcomm
  obtain ⟨-, -, -, -, -, -, hUc, -, h4⟩ := hΩ.exists_data_of_mem_USet hMW
  have hU2 : IsPGroup 2 ↥(M ⊓ W) := hΩ.isPGroup_of_mem_USet hMW
  obtain ⟨u, huMW, hu4⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic hU2 hUc h4
  have hn' : w⁻¹ * y ∈ N := by
    have h0 : QuotientGroup.mk' N (w⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hyw, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h0
  have hy' : y = w * (w⁻¹ * y) := by group
  have hycomm : ∀ v ∈ W, y * v = v * y := by
    intro v hv
    calc y * v = w * ((w⁻¹ * y) * v) := by rw [hy']; group
      _ = w * (v * (w⁻¹ * y)) := by rw [← Subgroup.mem_center_iff.mp (hNc hn') v]
      _ = (w * v) * (w⁻¹ * y) := by group
      _ = (v * w) * (w⁻¹ * y) := by rw [habel w hw v hv]
      _ = v * (w * (w⁻¹ * y)) := by group
      _ = v * y := by rw [← hy']
  have hy1' : y ≠ 1 := fun h => hy1 (by rw [h, map_one])
  have hyyN : y * y ∈ N := by
    have h0 : QuotientGroup.mk' N (y * y) = 1 := by rw [map_mul]; exact hy2
    exact (QuotientGroup.eq_one_iff _).mp h0
  have hyy : y * y = 1 := by
    have h : y * y ∈ (R₁ ⊔ R₂) ⊓ N := ⟨(R₁ ⊔ R₂).mul_mem hy hy, hyyN⟩
    rwa [hbot, Subgroup.mem_bot] at h
  have hyW : y ∈ W := by
    rcases hcomm with hcm | hR₂R₁
    · obtain ⟨a, ha, b, hb, hyab⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hcm hy
      have hUR₁ : M ⊓ W ≤ R₁ := fun x hx => by
        have : x ∈ M ⊓ (S : Subgroup G) := ⟨hx.1, hWS hx.2⟩
        rwa [inf_sylow_eq hR₁syl hR₁S] at this
      have hacomm : ∀ x ∈ M ⊓ W, a * x = x * a := by
        intro x hx
        have h1 := hycomm x hx.2
        have h2 : x * b = b * x := hcm x (hUR₁ hx) b hb
        rw [← hyab] at h1
        have h3 : a * x * b = x * a * b := by
          calc a * x * b = a * (x * b) := by group
            _ = a * (b * x) := by rw [h2]
            _ = a * b * x := by group
            _ = x * (a * b) := h1
            _ = x * a * b := by group
        exact mul_right_cancel h3
      have haU : a ∈ M ⊓ W :=
        quotCent_mem_inf_W_of_commutes hΩ hMΩ hR₁syl hR₁S hWS hMW ha hacomm
      have hJW : J ⊓ W ∈ USet Ω := inf_W_mem_USet' hΩ hWmem hWS hJΩ hR₂ hR₂J hR₂S
      have hUR₂ : J ⊓ W ≤ R₂ := fun x hx => by
        have : x ∈ J ⊓ (S : Subgroup G) := ⟨hx.1, hWS hx.2⟩
        rwa [inf_sylow_eq hR₂syl hR₂S] at this
      have hbcomm : ∀ x ∈ J ⊓ W, b * x = x * b := by
        intro x hx
        have h1 := hycomm x hx.2
        have h2 : a * x = x * a := hcm a ha x (hUR₂ hx)
        rw [← hyab] at h1
        have h3 : a * (b * x) = a * (x * b) := by
          calc a * (b * x) = a * b * x := by group
            _ = x * (a * b) := h1
            _ = x * a * b := by group
            _ = a * x * b := by rw [h2]
            _ = a * (x * b) := by group
        exact mul_left_cancel h3
      have hbU : b ∈ J ⊓ W :=
        quotCent_mem_inf_W_of_commutes hΩ hJΩ hR₂syl hR₂S hWS hJW hb hbcomm
      rw [← hyab]
      exact W.mul_mem haU.2 hbU.2
    · have hyR₁ : y ∈ R₁ := by
        rw [hR₂R₁, sup_idem] at hy
        exact hy
      exact (quotCent_mem_inf_W_of_commutes hΩ hMΩ hR₁syl hR₁S hWS hMW hyR₁
        fun x hx => hycomm x hx.2).2
  have hCy : Subgroup.centralizer ({y} : Set G) ≤ H :=
    c.hyp.cent M hMΩ hMW J hJ R₁ R₂ hR₁ hR₁M hR₁S hR₂ hR₂J hR₂S hcomm y hy hyW hy1' hyy
  exact ⟨hy1', hyy, hyW, hCy, u, huMW.1, hu4, (hycomm u huMW.2).symm⟩

end Lift

section Main

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

private theorem mem_of_conj_mem_dstar' (c : MinCexQ8 Ω K S R W H) {M : Subgroup G}
    (hMS : M ∈ dstarComp Ω K) {u : G} (hu : u ∈ M) (hu4 : orderOf u = 4) {x : G}
    (hx : x * u * x⁻¹ ∈ H) : x ∈ H :=
  E187C.mem_of_conj_mem_dstar_of c.hyp.trans
    (fun hu hu4 hx => e18_2Q8 G Ω K S R W H c _ hu hu4 _ hx) hMS hu hu4 hx

theorem quotCent_exists_W (c : MinCexQ8 Ω K S R W H)
    (hNc : N ≤ Subgroup.center G) (hN2 : IsPGroup 2 ↥N) (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥) :
    ∃ Wb ∈ WSet (quotFamily Ω N), Wb ≤ (S : Subgroup G).map (QuotientGroup.mk' N) ∧
      (∀ s ∈ (S : Subgroup G).map (QuotientGroup.mk' N), conjSub s Wb = Wb) ∧
      CentPairs (quotFamily Ω N) ((S : Subgroup G).map (QuotientGroup.mk' N)) Wb
        (H.map (QuotientGroup.mk' N)) := by
  have hΩ := c.stand.hyp
  obtain ⟨hWmem, hWS, hWn⟩ := c.stand.hW
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hK := c.stand.mem
  have cq : CentQuotGen Ω N := TwinThmE.centQuotGen hΩ c.stand.q8 hNc hmeet
  have hNS : N ≤ (S : Subgroup G) := hN2.le_sylow_of_normal S
  refine ⟨W.map (QuotientGroup.mk' N), quotCent_map_mem_WSet cq hN2 hWmem, Subgroup.map_mono hWS,
    ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [← AscQuot.map_conjSub, hWn s hs]
  intro Mb hMb hMbW Jb hJb Rb₁ Rb₂ hRb₁ hRb₁M hRb₁S hRb₂ hRb₂J hRb₂S hcb ab habR habW hab1 hab2
  obtain ⟨M, hMΩ, rfl⟩ := hMb
  have hMW : M ⊓ W ∈ USet Ω := by
    obtain ⟨U, hU, hUM, hUS, -⟩ := quotCent_lift_USet cq hNS hMbW
      (inf_le_right.trans (Subgroup.map_mono hWS)) hMΩ inf_le_left
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hU
    refine inf_W_mem_USet_of_card hΩ hWmem hWS hMΩ ?_
    have := Subgroup.card_le_of_le (le_inf hUM hUS)
    omega
  obtain ⟨J, hJ, rfl⟩ := CentEng.exists_lift_kperp_cent cq hMΩ hJb
  obtain ⟨R₁, R₂, hR₁, hR₁M, hR₂, hR₂J, rfl, rfl, hcomm⟩ :=
    CentEng.exists_lift_sylow_pair_cent hN2 cq hMΩ hJ hRb₁ hRb₁M hRb₂ hRb₂J hcb
  have hR₁S : R₁ ≤ (S : Subgroup G) := fun x hx =>
    mem_of_map_mem_of_le hNS (hRb₁S (Subgroup.mem_map_of_mem _ hx))
  have hR₂S : R₂ ≤ (S : Subgroup G) := fun x hx =>
    mem_of_map_mem_of_le hNS (hRb₂S (Subgroup.mem_map_of_mem _ hx))
  have habX : ab ∈ (R₁ ⊔ R₂).map (QuotientGroup.mk' N) := by rwa [Subgroup.map_sup]
  obtain ⟨y, hy, rfl⟩ := habX
  obtain ⟨w, hw, hwy⟩ := habW
  obtain ⟨hy1, hyy, -, hCy, u, huM, hu4, huy⟩ :=
    quotCent_exists_lift c hN2 hNc hmeet hMΩ hMW hJ hR₁ hR₁M hR₁S hR₂ hR₂J hR₂S hcomm hy hw hwy.symm
      hab1 hab2
  have hMsg : M ∈ dstarComp Ω K := mem_dstarComp_of_inf_W hΩ hWmem hK hMΩ
    (inf_W_mem_USet' hΩ hWmem hWS hK hRR hRK hRS) hMW
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hnN : y⁻¹ * (g * y * g⁻¹) ∈ N := by
    have h0 : QuotientGroup.mk' N (y⁻¹ * (g * y * g⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      have h1 : QuotientGroup.mk' N g * QuotientGroup.mk' N y * (QuotientGroup.mk' N g)⁻¹ =
          QuotientGroup.mk' N y := by
        rw [hx]
        group
      rw [h1, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h0
  have hgu : g * u * g⁻¹ ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : (g * u * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * u * g⁻¹) := by
      calc (g * u * g⁻¹) * (g * y * g⁻¹) = g * (u * y) * g⁻¹ := by group
        _ = g * (y * u) * g⁻¹ := by rw [huy]
        _ = (g * y * g⁻¹) * (g * u * g⁻¹) := by group
    set n : G := y⁻¹ * (g * y * g⁻¹) with hndef
    have hgy : g * y * g⁻¹ = y * n := by rw [hndef]; group
    rw [hgy] at e
    have hcn : ∀ t : G, t * n = n * t := fun t => Subgroup.mem_center_iff.mp (hNc hnN) t
    have e2 : ((g * u * g⁻¹) * y) * n = (y * (g * u * g⁻¹)) * n := by
      calc ((g * u * g⁻¹) * y) * n = (g * u * g⁻¹) * (y * n) := by group
        _ = (y * n) * (g * u * g⁻¹) := e
        _ = y * (n * (g * u * g⁻¹)) := by group
        _ = y * ((g * u * g⁻¹) * n) := by rw [hcn]
        _ = (y * (g * u * g⁻¹)) * n := by group
    exact mul_right_cancel e2
  have hgH : g * u * g⁻¹ ∈ H := hCy hgu
  exact Subgroup.mem_map_of_mem _ (mem_of_conj_mem_dstar' c hMsg huM hu4 hgH)

theorem printedQuotCent_proved : PrintedQuotCent :=
  ⟨fun G _ _ Ω K S R W H N _ c hNc hN2 _ hmeet => quotCent_exists_W c hNc hN2 hmeet⟩

end Main

end QuotCentPf

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
