module

public import CFSG.GH74.GLS.IVK.Lifted.DSDGroup
public import CFSG.GH74.GLS.IVK.Lifted.OddFrattini
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Lem510

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip

section QSylow

variable {G : Type} [Group G] [Finite G] {z : G} {S K : Subgroup G}

theorem isSylowOf_Qof (h : Std6r1 G z S K) :
    CFSG.ABGLocalTools.IsSylowOf 2 (Qof S K) (cSec K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 := h.z_sq
  have hz1 := h.z_ne
  have hzK : z ∈ K := h.z_mem_zStar.1
  set C := centralizer ({z} : Set G) with hC
  set Y := cSec K with hY
  set Y₀ := Y ⊓ C with hY₀
  have hSC : S ≤ C := h.sylow.le
  have hCY : C ≤ normalizer (Y₀ : Set G) := by
    intro c hc
    have hcK : c ∈ normalizer (K : Set G) := h.normalizes_K hc
    have hcY : c ∈ normalizer (Y : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact cSec_conj K hcK hy
      · intro hy
        have := cSec_conj K ((normalizer (K : Set G)).inv_mem hcK) hy
        simpa [mul_assoc] using this
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hcY, Subgroup.le_normalizer hc⟩
  have hsylY₀ : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ Y₀) Y₀ :=
    h.sylow.inf_of_le_normalizer inf_le_right hCY
  have hQeq : S ⊓ Y₀ = Qof S K := by
    ext x
    constructor
    · rintro ⟨hxS, hxY, -⟩
      exact ⟨hxS, hxY⟩
    · rintro ⟨hxS, hxY⟩
      exact ⟨hxS, hxY, hSC hxS⟩
  rw [hQeq] at hsylY₀
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨inf_le_right, h.S_pgroup.to_le inf_le_left, ?_⟩
  have h1 : ¬ 2 ∣ (Qof S K).relIndex Y₀ := (CFSG.ABGLocalTools.isSylowOf_iff.1 hsylY₀).2.2
  have h2 : Odd (Y₀.relIndex Y) := relIndex_centralizer_odd K hz2 hz1 hzK
  have hQY₀ : Qof S K ≤ Y₀ := by
    rw [← hQeq]
    exact inf_le_right
  have h3 : (Qof S K).relIndex Y = (Qof S K).relIndex Y₀ * Y₀.relIndex Y :=
    (Subgroup.relIndex_mul_relIndex (Qof S K) Y₀ Y hQY₀ inf_le_left).symm
  rw [h3]
  have hodd1 : Odd ((Qof S K).relIndex Y₀) := Nat.odd_iff.2 (by omega)
  exact fun hdvd => (Nat.not_even_iff_odd.2 (hodd1.mul h2)) (even_iff_two_dvd.2 hdvd)

end QSylow


section QDSD

@[expose] def conjQ {G : Type} [Group G] [Finite G] {z : G} {S K : Subgroup G} (h : Std6r1 G z S K) {s : G}
    (hs : s ∈ S) : ↥(Qof S K) ≃* ↥(Qof S K) where
  toFun q := ⟨s * q * s⁻¹, conj_mem_Qof hs (h.normalizes_K (h.sylow.le hs)) q.2⟩
  invFun q := ⟨s⁻¹ * q * s⁻¹⁻¹, by
    have := conj_mem_Qof (S.inv_mem hs) ((normalizer (K : Set G)).inv_mem
      (h.normalizes_K (h.sylow.le hs))) q.2
    exact this⟩
  left_inv q := Subtype.ext (by simp [mul_assoc])
  right_inv q := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem q_dsd : Q_DSD := by
  intro G _ _ z S K h hrank
  classical
  have hsyl := isSylowOf_Qof h
  have hY : rigidSectionCentralizer z = cSec K := by
    unfold rigidSectionCentralizer
    rw [h.rigidProduct_eq]
    rfl
  have hsyl' : CFSG.ABGLocalTools.IsSylowOf 2 (Qof S K) (rigidSectionCentralizer z) := by
    rw [hY]
    exact hsyl
  obtain ⟨Q', hQ'⟩ := hsyl'
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.thm2
  have hcl := h.classical.2 t₀ ht₀C ht₀z ht₀n
  have hcard1 : Set.ncard {K' : Subgroup G | IsRigidRankOneComp z K'} = 1 := by
    rw [h.comps]
    exact Set.ncard_singleton K
  have hf := hcl.2.2.2.2.2 hcard1 Q'
  let e0 : ↥(Q' : Subgroup ↥(rigidSectionCentralizer z)) ≃* ↥(Qof S K) :=
    (Subgroup.equivMapOfInjective (Q' : Subgroup ↥(rigidSectionCentralizer z))
      (rigidSectionCentralizer z).subtype (rigidSectionCentralizer z).subtype_injective).trans
      (MulEquiv.subgroupCongr hQ')
  obtain ⟨E, hE, hEc⟩ := exists_four_of_pRank hrank
  have hnc : ¬ IsCyclic ↥(Qof S K) := by
    intro hcyc
    obtain ⟨v, hv, w, hw, hv1, hw1, hvw⟩ := exists_two_ne_one_aux (E := E) (by rw [hEc]; norm_num)
    have hv2 : ((v : ↥(Qof S K)) : G) * ((v : ↥(Qof S K)) : G) = 1 := by
      have := congrArg Subtype.val (hE v hv)
      simpa using this
    have hw2 : ((w : ↥(Qof S K)) : G) * ((w : ↥(Qof S K)) : G) = 1 := by
      have := congrArg Subtype.val (hE w hw)
      simpa using this
    exact hvw (Subtype.ext (B.cyclic_invol_unique hcyc (v : ↥(Qof S K)).2 (w : ↥(Qof S K)).2 hv2 hw2
      (fun h1 => hv1 (Subtype.ext h1)) (fun h1 => hw1 (Subtype.ext h1))))
  have hmax : IsNonabelianMaximalClassTwoGroup ↥(Q' : Subgroup ↥(rigidSectionCentralizer z)) := by
    rcases hf with hcyc | hmax
    · exact absurd (e0.isCyclic.1 hcyc) hnc
    · exact hmax
  have hD : DSDData ↥(Q' : Subgroup ↥(rigidSectionCentralizer z)) := by
    refine dsdData_of_maxClass hmax ⟨E.map e0.symm.toMonoidHom, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, hE x hx, map_one]
    · rw [Subgroup.card_map_of_injective e0.symm.injective, hEc]
  obtain ⟨A, u, hA, hu, hu4, hout, hinv⟩ := DSDData.congr e0 hD
  have hz2 := h.z_sq
  have hzQ : z ∈ Qof S K := h.z_mem_Q
  have hcore := dsd_core hA hu hu4 hout hinv (z := (⟨z, hzQ⟩ : ↥(Qof S K)))
    (Subtype.ext (by simpa using hz2)) (fun hz1 => h.z_ne (congrArg Subtype.val hz1))
    (fun g => Subtype.ext (by
      show (g : G) * z = z * (g : G)
      exact (h.z_cent g.2.1).symm))
  obtain ⟨hsq, hφ, hb⟩ := hcore
  refine ⟨(u : G), u.2, congrArg Subtype.val hsq, ?_, ?_⟩
  · intro s hs
    rcases hφ (conjQ h hs) with h1 | h1
    · left
      exact congrArg Subtype.val h1
    · right
      exact congrArg Subtype.val h1
  · intro b hbQ hb2 hb1 hbz
    have := hb ⟨b, hbQ⟩ (Subtype.ext (by simpa using hb2)) (fun e => hb1 (congrArg Subtype.val e))
      (fun e => hbz (congrArg Subtype.val e))
    exact congrArg Subtype.val this

end QDSD

end CFSG.GH74.GLS.IVK.Lifted
