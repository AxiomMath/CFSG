module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Lift
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Graph
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCollapse
public import CFSG.ClassicalInvolution.Asc77.AscT8S26Hull
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyC
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_sup_of_le_normalizer {H N : Subgroup G} (hH : H ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ H ⊔ N) : ∃ h ∈ H, ∃ n ∈ N, x = h * n := by
  let S : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ n ∈ N, x = h * n}
      one_mem' := ⟨1, H.one_mem, 1, N.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, n₁, hn₁, rfl⟩ ⟨h₂, hh₂, n₂, hn₂, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, (h₂⁻¹ * n₁ * h₂) * n₂, ?_, by group⟩
        refine N.mul_mem ?_ hn₂
        have := (Subgroup.mem_normalizer_iff.mp (hH (H.inv_mem hh₂)) n₁).mp hn₁
        simpa using this
      inv_mem' := by
        rintro _ ⟨h, hh, n, hn, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, h * n⁻¹ * h⁻¹, ?_, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (hH hh) n⁻¹).mp (N.inv_mem hn)
        exact this }
  have hle : H ⊔ N ≤ S := sup_le (fun h hh => ⟨h, hh, 1, N.one_mem, by simp⟩)
    (fun n hn => ⟨1, H.one_mem, n, hn, by simp⟩)
  exact hle hx

theorem conjSub_mem_omegaNbr_of_normalizes (hΩ : HypOmegaGen Ω) {K J' : Subgroup G} {b : G}
    (hb : conjSub b K = K) (hJ' : J' ∈ omegaNbr Ω K) : conjSub b J' ∈ omegaNbr Ω K := by
  obtain ⟨hJΩ, hJK, R', hR', hR'J, hR'N⟩ := hJ'
  have hbN : b ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr hb
  refine ⟨hΩ.conjInvariant b J' hJΩ, ?_, conjSub b R', Q3.Q3CL.Thompson.conjSub_mem_RSet hΩ hR' b,
    conjSub_mono hR'J, ?_⟩
  · intro h
    apply hJK
    have h2 : conjSub b⁻¹ (conjSub b J') = conjSub b⁻¹ K := by rw [h]
    rw [conjSub_inv_conjSub] at h2
    calc J' = conjSub b⁻¹ K := h2
      _ = conjSub b⁻¹ (conjSub b K) := by rw [hb]
      _ = K := conjSub_inv_conjSub b K
  · intro x hx
    rw [mem_conjSub_iff] at hx
    have hy := hR'N hx
    have e : x = b * (b⁻¹ * x * b) * b⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbN hy) (Subgroup.inv_mem _ hbN)

end Basic

section Img

variable {G : Type} [Group G]

theorem map_mk_subgroupOf_conjSub {Y M : Subgroup G} {o : G} (ho : o ∈ Balance.oddCoreIn Y) :
    ((conjSub o M).subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) =
      (M.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) := by
  have hoY : o ∈ Y := Balance.oddCoreIn_le Y ho
  have ho' : (⟨o, hoY⟩ : ↥Y) ∈ classicalInvolutionOddCore ↥Y := by
    obtain ⟨o'', ho'', hoeq⟩ := ho
    have : o'' = ⟨o, hoY⟩ := Subtype.ext hoeq
    rw [← this]
    exact ho''
  have hkill : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) (⟨o, hoY⟩ : ↥Y) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ho'
  have hconj : ∀ y : ↥Y, QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)
      (⟨o, hoY⟩ * y * (⟨o, hoY⟩ : ↥Y)⁻¹) = QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) y := by
    intro y
    rw [map_mul, map_mul, map_inv, hkill]
    simp
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ conjSub o M := Subgroup.mem_subgroupOf.mp hy
    rw [mem_conjSub_iff] at hy'
    refine ⟨(⟨o, hoY⟩ : ↥Y)⁻¹ * y * ⟨o, hoY⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · simpa using hy'
    · have := hconj ((⟨o, hoY⟩ : ↥Y)⁻¹ * y * ⟨o, hoY⟩)
      rw [← this]
      congr 1
      group
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ M := Subgroup.mem_subgroupOf.mp hy
    refine ⟨⟨o, hoY⟩ * y * (⟨o, hoY⟩ : ↥Y)⁻¹, Subgroup.mem_subgroupOf.mpr ?_, hconj y⟩
    rw [mem_conjSub_iff]
    convert hy' using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

end Img

section Tri

open CFSG.ClassicalInvolution.Hat2A7S

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_triangle (hs : Std8A7 Ω K J S R T W z t) (hdisc : ¬ DConnected Ω)
    (h261 : omegaNbrGen Ω K ≠ J ⊔ oddCoreOf (omegaNbrGen Ω K)) :
    ∃ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J := by
  classical
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hJ : J ∈ omegaNbr Ω K := hs.hJ
  have hJΩ : J ∈ Ω := hJ.1
  have hw : ∀ L ∈ Ω, A7Witness L := fun L hL => (hs.stand.classical L hL).choose_spec.witness
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  set Y : Subgroup G := K ⊔ X with hYdef
  have hKY : K ≤ Y := le_sup_left
  have hXY : X ≤ Y := le_sup_right
  have hJX : J ≤ X := le_iSup₂ (f := fun M (_ : M ∈ omegaNbr Ω K) => M) J hJ
  have hYle : Y ≤ sigmaNorm Ω K := by
    refine sup_le (s26_le_sigmaNorm_of_mem_dComp hΩ.conjInvariant hKΩ
      Relation.ReflTransGen.refl) ?_
    exact iSup₂_le fun M hM => s26_le_sigmaNorm_of_mem_dComp hΩ.conjInvariant hKΩ
      (T8.mem_dComp_of_mem_omegaNbr hM)
  have hYne : Y ≠ ⊤ := by
    intro h
    rw [h, top_le_iff] at hYle
    exact hdisc (dConnected_of_sigmaNorm_eq_top hKΩ hs.stand.trans hYle)
  let Λ : Set (Subgroup G) := {M | M ∈ Ω ∧ M ≤ Y}
  have hΛne : Λ.Nonempty := ⟨K, hKΩ, hKY⟩
  have hMΛ : ∀ M ∈ omegaNbr Ω K, M ∈ Λ := fun M hM =>
    ⟨hM.1, (le_iSup₂ (f := fun M (_ : M ∈ omegaNbr Ω K) => M) M hM).trans hXY⟩
  have hΛY : (⨆ M ∈ Λ, M) = Y := by
    refine le_antisymm (iSup₂_le fun M hM => hM.2) (sup_le ?_ ?_)
    · exact le_iSup₂ (f := fun M (_ : M ∈ Λ) => M) K ⟨hKΩ, hKY⟩
    · exact iSup₂_le fun M hM => le_iSup₂ (f := fun M (_ : M ∈ Λ) => M) M (hMΛ M hM)
  have hinv : ∀ y ∈ Y, ∀ L ∈ Λ, L.map (MulAut.conj y).toMonoidHom ∈ Λ := by
    intro y hy L hL
    refine ⟨hΩ.conjInvariant y L hL.1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact Y.mul_mem (Y.mul_mem hy (hL.2 hx)) (Y.inv_mem hy)
  have hcls : ∀ L ∈ Λ, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u := fun L hL =>
    hs.stand.classical L hL.1
  have hB : Hat2A7.CITBelow2A7 (Nat.card G) := hs.stand.below
  let img : Subgroup G → Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y) := fun L =>
    (L.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))
  have hex : ∃ M ∈ omegaNbr Ω K, img M ≠ img J := by
    by_contra hall
    push Not at hall
    apply h261
    have h1 : X ≤ J ⊔ Balance.oddCoreIn Y := by
      refine iSup₂_le fun M hM a ha => ?_
      have haY : a ∈ Y := (hMΛ M hM).2 ha
      have hmem : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) (⟨a, haY⟩ : ↥Y) ∈ img M :=
        ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      rw [hall M hM] at hmem
      obtain ⟨b, hb, hba⟩ := hmem
      have hq : (b : ↥Y)⁻¹ * ⟨a, haY⟩ ∈ classicalInvolutionOddCore ↥Y := QuotientGroup.eq.mp hba
      have hbJ : (b : G) ∈ J := Subgroup.mem_subgroupOf.mp hb
      have hc : (b : G)⁻¹ * a ∈ Balance.oddCoreIn Y := ⟨_, hq, rfl⟩
      have ha' : a = (b : G) * ((b : G)⁻¹ * a) := by group
      rw [ha']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbJ) (Subgroup.mem_sup_right hc)
    have hJnorm : J ≤ Subgroup.normalizer (Balance.oddCoreIn Y : Set G) := fun j hj =>
      Balance.normalizer_oddCoreIn Y ((hJX.trans hXY) hj)
    have h2 : X ≤ J ⊔ oddCoreOf X := by
      intro x hx
      obtain ⟨j, hj, n, hn, rfl⟩ := mem_sup_of_le_normalizer hJnorm (h1 hx)
      have hjX : j ∈ X := hJX hj
      have hnX : n ∈ X := by
        have : j⁻¹ * (j * n) ∈ X := X.mul_mem (X.inv_mem hjX) hx
        simpa using this
      have hnS : n ∈ X ⊓ Balance.oddCoreIn Y := ⟨hnX, hn⟩
      have hS : X ⊓ Balance.oddCoreIn Y ≤ Balance.oddCoreIn X := by
        refine Balance.le_oddCoreIn_of_normalizes inf_le_left ?_ ?_
        · intro g hg
          exact Sec7.mem_normalizer_inf (Subgroup.le_normalizer hg)
            (Balance.normalizer_oddCoreIn Y (hXY hg))
        · exact (Balance.odd_card_oddCoreIn Y).of_dvd_nat
            (Subgroup.card_dvd_of_le inf_le_right)
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right (hS hnS))
    exact le_antisymm h2 (sup_le hJX (oddCoreOf_le_self X))
  obtain ⟨M, hMK, himg⟩ := hex
  have hMΩ : M ∈ Ω := hMK.1
  have hMΛ' : M ∈ Λ := hMΛ M hMK
  have hJΛ : J ∈ Λ := hMΛ J hJ
  have hcomm : ∀ a ∈ J, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ Balance.oddCoreIn Y := by
    rcases Hat2A7.images_eq_or_commute_of_collapse hB hYne hΛne hΛY hinv hcls hJΛ hMΛ' with h | h
    · exact absurd h.symm himg
    · exact h
  obtain ⟨zM, hzM⟩ := Sec6Gen.exists_uniqueInvolution hΩ hMΩ
  have hzMi : zM⁻¹ = zM := inv_eq_of_mul_eq_one_right hzM.sq
  have hzMY : zM ∈ Y := hMΛ'.2 hzM.mem
  have hKle : Balance.oddCoreIn K ≤ Balance.oddCoreIn Y :=
    Hat2A7.oddCoreIn_le_oddCoreIn_of_collapse hB hYne hΛne hΛY hinv hcls (L := K) ⟨hKΩ, hKY⟩
  obtain ⟨-, hMKne, RM, hRM, hRMM, hRMN⟩ := id hMK
  have hRM2 : IsPGroup 2 RM := Sec7.isPGroup_of_mem_RSet hRM
  have h8M := Sec6Gen.eight_le_of_mem_RSet hΩ hRM
  have hzRM : zM ∈ RM := T3.mem_of_isPGroup hzM hRMM hRM2 (by omega)
  have hgt : zM ∈ Subgroup.normalizer (K : Set G) := hRMN hzRM
  have huniq : ∀ x ∈ RM, orderOf x = 2 → x = zM := by
    intro x hx hx2
    have hxx : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx2, pow_two] at this
    rcases hzM.unique x (hRMM hx) hxx with h | h
    · exfalso
      rw [h, orderOf_one] at hx2
      omega
    · exact h
  have htriv := Hat2A7.oddQuotAut_conjOn_eq_one_of_card (hw K hKΩ) hRMN hRM2 hzRM huniq
    (by omega)
  have hca : ∀ r ∈ R, zM⁻¹ * (r * zM * r⁻¹) ∈ Balance.oddCoreIn Y := by
    intro r hr
    have hrK : r ∈ K := hs.hR.2.1 hr
    have hmem := commutator_mem_oddCore_of_action_eq_one hgt htriv ⟨r, hrK⟩
    have hmemG : r⁻¹ * (zM * r * zM⁻¹) ∈ Balance.oddCoreIn K := ⟨_, hmem, rfl⟩
    have e : zM⁻¹ * (r * zM * r⁻¹) = r * (r⁻¹ * (zM * r * zM⁻¹)) * r⁻¹ := by
      rw [hzMi]
      group
    rw [e]
    exact Balance.conj_mem_oddCoreIn (hKY hrK) (hKle hmemG)
  have hcb : ∀ r ∈ T, zM⁻¹ * (r * zM * r⁻¹) ∈ Balance.oddCoreIn Y := by
    intro r hr
    have hrJ : r ∈ J := hs.hT.2.1 hr
    have h1 := hcomm r hrJ zM hzM.mem
    have e : zM⁻¹ * (r * zM * r⁻¹) = zM⁻¹ * (r * zM * r⁻¹ * zM⁻¹) * zM⁻¹⁻¹ := by group
    rw [e]
    exact Balance.conj_mem_oddCoreIn (Y.inv_mem hzMY) h1
  have hMA : ∀ o ∈ Balance.oddCoreIn Y, conjSub o M ≠ K := by
    intro o ho hEq
    have h1 : IsUniqueInvolution (conjSub o M) (o * zM * o⁻¹) := hzM.conj o
    rw [hEq] at h1
    have hz' : z = o * zM * o⁻¹ := hs.hz.eq h1
    have hcomz : zM * z = z * zM := by
      have := hs.hz.conj_eq (n := zM) (mem_normalizer_iff_conjSub_eq.mp hgt)
      calc zM * z = zM * z * zM⁻¹ * zM := by group
        _ = z * zM := by rw [this]
    have hmem : z⁻¹ * zM ∈ Balance.oddCoreIn Y := by
      rw [hz']
      have e : (o * zM * o⁻¹)⁻¹ * zM = o * (zM⁻¹ * o⁻¹ * zM⁻¹⁻¹) := by group
      rw [e]
      exact (Balance.oddCoreIn Y).mul_mem ho
        (Balance.conj_mem_oddCoreIn (Y.inv_mem hzMY) ((Balance.oddCoreIn Y).inv_mem ho))
    have hzz : z = zM := eq_of_commute_of_inv_mul_mem_odd hs.hz.sq hzM.sq hcomz.symm
      (Balance.oddCoreIn Y) (Balance.odd_card_oddCoreIn Y) hmem
    exact hMKne (hs.noTwins M ⟨hMΩ, z, hs.hz, by rw [hzz]; exact hzM⟩)
  have hMB : ∀ o ∈ Balance.oddCoreIn Y, conjSub o M ≠ J := by
    intro o ho hEq
    apply himg
    have h1 := map_mk_subgroupOf_conjSub (Y := Y) (M := M) ho
    rw [hEq] at h1
    exact h1.symm
  have hE : IsPGroup 2 ↥(R ⊔ T) := S.isPGroup'.to_le (sup_le hs.hR.2.2 hs.hT.2.2)
  have hOn : ∀ e ∈ R ⊔ T, ∀ o ∈ Balance.oddCoreIn Y, e * o * e⁻¹ ∈ Balance.oddCoreIn Y :=
    fun e he o ho => Balance.conj_mem_oddCoreIn
      (sup_le (hs.hR.2.1.trans hKY) ((hs.hT.2.1.trans hJX).trans hXY) he) ho
  obtain ⟨o, -, h1, h2⟩ := exists_common_nbr_conj hΩ hKΩ hJΩ hMΩ hzM hs.hR.1 hs.hR.2.1 hs.hT.1
    hs.hT.2.1 hE (Balance.odd_card_oddCoreIn Y) hOn hca hcb hMA hMB
  exact ⟨conjSub o M, h1, h2⟩

end Tri

end CFSG.ClassicalInvolution.Hat2A7S8
