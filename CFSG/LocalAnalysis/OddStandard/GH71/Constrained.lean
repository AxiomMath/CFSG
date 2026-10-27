module

public import CFSG.LocalAnalysis.OddStandard.GH71.UFrame3
public import CFSG.LocalAnalysis.OddStandard.GH71.UnbalancedSylow
public import CFSG.LocalAnalysis.OddStandard.GH71.HBarLift
public import CFSG.LocalAnalysis.OddStandard.GH71.CenterBar

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

theorem not_T₂_le_centralizer (h : Ctx71 G z S U u) (hB : AlternatingBalanceData 11)
    (hB1 : SpecB1) (hB2' : SpecB2') (hB3 : SpecB3)
    (hD : ¬ pPrimeCoreOf 2 (Cen z) ⊓ Cen u ≤ pPrimeCoreOf 2 (Cen u))
    {P₁ : Subgroup G} (hP₁ : Open.fusionIsSylowIn 3 P₁ (pPrimeCoreOf 2 (Cen z)))
    (hP₁S : S ≤ normalizer (P₁ : Set G)) :
    ¬ S ⊓ centralizer ({u} : Set G) ≤ centralizer ((P₁ ⊓ Cen u : Subgroup G) : Set G) := by
  intro hT
  obtain ⟨g, ⟨hgU, hgT⟩, hgz⟩ := h.exists_conj_u
  set Su := S.map (MulAut.conj g).toMonoidHom with hSu
  have hfr := h.frame_u hgU hgz
  obtain ⟨X, hX3, hXS, -⟩ := hB1 _ _ hfr.cover hfr.sylow hfr.card
  have hzu : z ∈ Cen u := (h.U_le_Su hgU).trans (h.Su_le hgz) h.z_mem
  set πu := QuotientGroup.mk' (pPrimeCore 2 ↥(Cen u)) with hπu
  set zb : HBar (Cen u) := πu ⟨z, hzu⟩ with hzb
  have hzbU : zb ∈ barIn (Cen u) U := ⟨⟨z, hzu⟩, h.z_mem, rfl⟩
  have hzz : z * z = 1 := h.sq_eq_one_of_mem_U h.z_mem
  have huu : u * u = 1 := h.sq_eq_one_of_mem_U h.u_mem
  have hzbc : zb ∉ center (HBar (Cen u)) :=
    not_mem_center_bar (h.cover_of_involution h.orderOf_u).2.1 huu h.u_ne_one hzu hzz
      h.z_ne_one (Ne.symm h.u_ne_z)
      (h.sq_eq_one_of_mem_U (U.mul_mem h.z_mem h.u_mem))
  set D := pPrimeCoreOf 2 (Cen z) ⊓ Cen u with hDdef
  have hDu : D ≤ Cen u := inf_le_right
  have hDodd : Odd (Nat.card D) := odd_card_of_le inf_le_left (odd_card_pPrimeCoreOf' _)
  have hDbar : barIn (Cen u) D ≤ X := by
    refine le_trans ?_ (hB2' _ _ _ hfr X hX3 hXS zb hzbU hzbc)
    refine le_pPrimeCoreOf_of_odd ?_ ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp
        (pPrimeCoreOf_le' _ (Subgroup.mem_subgroupOf.mp hw).1)
    · have hd : (D ⊓ pPrimeCoreOf 2 (Cen u)).relIndex D ∣ Nat.card D := relIndex_dvd_card _ _
      rw [IVK812.relIndex_eq_card_barIn hDu] at hd
      exact Odd.of_dvd_nat hDodd hd
    · have h1 := centralizer_bar_le hzu h.orderOf_z
      have h2 : barIn (Cen u) (centralizer ({z} : Set G)) =
          barIn (Cen u) (Cen u ⊓ centralizer ({z} : Set G)) := by
        unfold barIn; congr 1; ext x; simp [Subgroup.mem_subgroupOf]
      rw [h2] at h1
      refine h1.trans (IVK812.barIn_le_normalizer ?_)
      intro y hy
      exact inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pPrimeCoreOf' _ hy.2, le_normalizer hy.1⟩
  set Q₀ := P₁ ⊓ Cen u with hQ₀
  have hQ₀u : Q₀ ≤ Cen u := inf_le_right
  have hQne : barIn (Cen u) Q₀ ≠ ⊥ := fun hb =>
    h.not_le_of_unbalanced hB hD hP₁ hP₁S ((IVK812.barIn_eq_bot_iff hQ₀u).mp hb)
  have hQD : barIn (Cen u) Q₀ ≤ barIn (Cen u) D :=
    map_mono (fun x hx => ⟨hP₁.1 hx.1, hx.2⟩)
  have hQX : barIn (Cen u) Q₀ = X := by
    have hle : barIn (Cen u) Q₀ ≤ X := hQD.trans hDbar
    have hdvd : Nat.card (barIn (Cen u) Q₀) ∣ 3 := hX3 ▸ card_dvd_of_le hle
    have h1 : Nat.card (barIn (Cen u) Q₀) ≠ 1 := fun e => hQne (card_eq_one.mp e)
    have h3 : Nat.card (barIn (Cen u) Q₀) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with e | e
      · exact absurd e h1
      · exact e
    exact eq_of_le_of_card_ge hle (by rw [h3, hX3])
  have hTX : barIn (Cen u) (S ⊓ centralizer ({u} : Set G)) ≤
      centralizer (X : Set (HBar (Cen u))) := by
    rw [← hQX]
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hT (Subgroup.mem_subgroupOf.mp ht)) q
      (Subgroup.mem_subgroupOf.mp hq)
  have hST : barIn (Cen u) Su ⊓ centralizer ({zb} : Set (HBar (Cen u))) ≤
      barIn (Cen u) (S ⊓ centralizer ({u} : Set G)) := by
    rintro _ ⟨⟨s, hs, rfl⟩, hsz⟩
    have hsSu : (s : G) ∈ Su := Subgroup.mem_subgroupOf.mp hs
    have hcomm : πu s * zb = zb * πu s := mem_centralizer_singleton_iff.mp hsz
    have hszs : (s : G) * z * (s : G)⁻¹ ∈ U :=
      (mem_normalizer_iff.mp (h.Su_norm hgU hsSu) z).mp h.z_mem
    have hmem : s * ⟨z, hzu⟩ * s⁻¹ * ⟨z, hzu⟩ ∈ pPrimeCore 2 ↥(Cen u) := by
      rw [← QuotientGroup.eq_one_iff]
      show πu (s * ⟨z, hzu⟩ * s⁻¹ * ⟨z, hzu⟩) = 1
      rw [map_mul, map_mul, map_mul, map_inv]
      have hz1 : (⟨z, hzu⟩ * ⟨z, hzu⟩ : ↥(Cen u)) = 1 := Subtype.ext hzz
      calc πu s * πu ⟨z, hzu⟩ * (πu s)⁻¹ * πu ⟨z, hzu⟩
          = πu ⟨z, hzu⟩ * πu s * (πu s)⁻¹ * πu ⟨z, hzu⟩ := by rw [hcomm]
        _ = πu (⟨z, hzu⟩ * ⟨z, hzu⟩) := by rw [map_mul]; group
        _ = 1 := by rw [hz1, map_one]
    have hsc : (s : G) * z * (s : G)⁻¹ = z := by
      by_contra hne
      have hU2 : (s : G) * z * (s : G)⁻¹ * z ∈ U := U.mul_mem hszs h.z_mem
      refine not_mem_pPrimeCore_of_involution
        (Subtype.ext (h.sq_eq_one_of_mem_U hU2)) ?_ hmem
      intro h1
      apply hne
      have h2 : (s : G) * z * (s : G)⁻¹ * z = 1 := congrArg Subtype.val h1
      calc (s : G) * z * (s : G)⁻¹ = (s : G) * z * (s : G)⁻¹ * z * z := by
            rw [mul_assoc ((s : G) * z * (s : G)⁻¹), hzz, mul_one]
        _ = z := by rw [h2, one_mul]
    have hsC : (s : G) ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc (s : G) * z = (s : G) * z * (s : G)⁻¹ * s := by group
        _ = z * s := by rw [hsc]
    have hsT : (s : G) ∈ S ⊓ centralizer ({u} : Set G) := by
      rw [← h.Su_inf hgT hgz]; exact ⟨hsSu, hsC⟩
    exact ⟨s, Subgroup.mem_subgroupOf.mpr hsT, rfl⟩
  exact hB3 _ _ _ hfr X hX3 hXS zb hzbU hzbc (hST.trans hTX)

end Ctx71

end CFSG.OddStandard.GH71
