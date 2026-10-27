module

public import CFSG.CGT.Stroth77.Arch76Frame
public import CFSG.CGT.Stroth77.StrothFrameD
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.CGT.Stroth77.Section41
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.Stroth77.AmbientSplit
public import CFSG.Foundations
public import CFSG.GH74.Defs
import CFSG.CGT.Stroth77.Extension22FourC4
import CFSG.CGT.Stroth77.StrothFrameAmbient
import CFSG.CGT.Stroth77.TorusCard
import CFSG.GroupTheory.FixedCosetCommutator
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.CGT.Stroth77

open CFSG.ABGLocalTools (IsSylowOf)

namespace Arch76

theorem nonsq_two_torsion_cases : ∀ v : Co, 2 • v = 0 → (∀ u : Co, 2 • u ≠ v) →
    v = (1, 0, 0) ∨ v = (1, 2, 2) ∨ v = (1, 2, 0) ∨ v = (1, 0, 2) := by
  decide +kernel

theorem two_nsmul_ne_w : ∀ u : Co, 2 • u ≠ (1, 0, 0) := by decide +kernel

theorem fixed_two_torsion_cases : ∀ v : Co, 2 • v = 0 → fuv v = v → ft v = v → fu v = v →
    v = 0 ∨ v = (0, 2, 2) := by
  decide +kernel

end Arch76

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame

variable (F : StrothFrame G)

theorem xy_sq_ne_one : (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2 ≠ 1 := by
  set K := F.dA.toConfig
  have h : K.ev (0, 2, 2) = (K.x * K.y) ^ 2 := by
    rw [K.xy_sq]
    simp [Arch76.Config.ev, show (2 : ZMod 4).val = 2 from rfl]
  rw [← h, Ne, K.ev_eq_one_iff]
  decide

theorem uv_not_mem_centralizer_w :
    F.dA.uv ∉ Subgroup.centralizer ({(F.dA.c : G)} : Set G) := by
  set K := F.dA.toConfig
  intro h
  have h1 : F.dA.uv * K.w = K.w * F.dA.uv := Subgroup.mem_centralizer_singleton_iff.mp h
  have h2 : K.uv⁻¹ * K.w * K.uv = K.w := by
    show F.dA.uv⁻¹ * K.w * F.dA.uv = K.w
    rw [mul_assoc, ← h1]; group
  rw [K.huv_w] at h2
  exact F.xy_sq_ne_one (mul_eq_left.mp h2)

theorem exists_conj_eq_w {g : G} (hg : g ∈ Subgroup.normalizer (F.A : Set G)) :
    ∃ s ∈ ({1, F.dA.uv, F.dA.t, F.dA.uv * F.dA.t} : Set G),
      s⁻¹ * (g⁻¹ * (F.dA.c : G) * g) * s = F.dA.c := by
  set K := F.dA.toConfig with hK
  have hw : K.w = (F.dA.c : G) := rfl
  have hconj : ∀ a ∈ F.A, g⁻¹ * a * g ∈ F.A := fun a ha =>
    (Subgroup.mem_normalizer_iff''.mp hg a).mp ha
  have hconj' : ∀ a ∈ F.A, g * a * g⁻¹ ∈ F.A := fun a ha => by
    have := (Subgroup.mem_normalizer_iff''.mp (inv_mem hg) a).mp ha
    rwa [inv_inv] at this
  obtain ⟨v, hv⟩ := K.exists_ev (hconj _ K.w_mem)
  have h2 : 2 • v = 0 := by
    rw [← K.ev_eq_one_iff, K.ev_nsmul, hv, ← Arch76.Config.conj_pow_eq, K.hw]
    group
  have hsq : ∀ u : Arch76.Co, 2 • u ≠ v := by
    intro u hu
    obtain ⟨u', hu'⟩ := K.exists_ev (hconj' _ (K.ev_mem u))
    have h1 : K.w = (g * K.ev u * g⁻¹) ^ 2 := by
      rw [conj_pow, ← K.ev_nsmul, hu, hv]; group
    rw [← hu', ← K.ev_nsmul, ← K.ev_w] at h1
    exact Arch76.two_nsmul_ne_w u' (K.ev_injective h1).symm
  have hsub : ∀ s : G, s⁻¹ * (g⁻¹ * (F.dA.c : G) * g) * s = s⁻¹ * K.ev v * s := fun s => by
    rw [hv, hw]
  rcases Arch76.nonsq_two_torsion_cases v h2 hsq with rfl | rfl | rfl | rfl
  · refine ⟨1, by simp, ?_⟩
    rw [hsub, inv_one, one_mul, mul_one, K.ev_w, hw]
  · refine ⟨F.dA.uv, by simp, ?_⟩
    rw [hsub]
    show K.uv⁻¹ * K.ev (1, 2, 2) * K.uv = K.w
    rw [K.conj_uv_ev, show Arch76.fuv (1, 2, 2) = (1, 0, 0) by decide, K.ev_w]
  · refine ⟨F.dA.t, by simp, ?_⟩
    rw [hsub]
    show K.t⁻¹ * K.ev (1, 2, 0) * K.t = K.w
    rw [K.conj_t_ev, show Arch76.ft (1, 2, 0) = (1, 0, 0) by decide, K.ev_w]
  · refine ⟨F.dA.uv * F.dA.t, by simp, ?_⟩
    rw [hsub]
    show (K.uv * K.t)⁻¹ * K.ev (1, 0, 2) * (K.uv * K.t) = K.w
    rw [show (K.uv * K.t)⁻¹ * K.ev (1, 0, 2) * (K.uv * K.t) =
        K.t⁻¹ * (K.uv⁻¹ * K.ev (1, 0, 2) * K.uv) * K.t by group,
      K.conj_uv_ev, K.conj_t_ev, show Arch76.ft (Arch76.fuv (1, 0, 2)) = (1, 0, 0) by decide,
      K.ev_w]

end StrothFrame

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem commute_xy_sq (h : F.IsD D dD) {s : G} (hs : s ∈ (F.S : Subgroup G)) :
    s * (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2 =
      (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2 * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := F.dA.toConfig with hK
  set S : Subgroup G := (F.S : Subgroup G) with hSdef
  have hSp : IsPGroup 2 S := F.S.isPGroup'
  have hwS : K.w ∈ S := F.A_le_S K.w_mem
  have hw1 : K.w ≠ 1 := by
    rw [← K.ev_w, Ne, K.ev_eq_one_iff]; decide
  have : Nontrivial S := ⟨⟨⟨K.w, hwS⟩, 1, fun h1 => hw1 (congrArg Subtype.val h1)⟩⟩
  have : Nontrivial (Subgroup.center S) := hSp.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    obtain ⟨n, hn⟩ := (hSp.to_subgroup (Subgroup.center S)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center S) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hn] at h1 ⊢
    rcases n with _ | n
    · simp at h1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  set e₀ : G := ((e : S) : G) with he₀
  have he₀S : e₀ ∈ S := (e : S).2
  have hcomm : ∀ x ∈ S, x * e₀ = e₀ * x := fun x hx => by
    have := Subgroup.mem_center_iff.mp e.2 ⟨x, hx⟩
    exact congrArg Subtype.val this
  have he2 : e₀ * e₀ = 1 := by
    have h1 : (e : S) ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, he]
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, pow_two, Subgroup.coe_one] at h2
  have he1 : e₀ ≠ 1 := by
    intro h1
    have h2 : (e : S) = 1 := Subtype.ext h1
    have h3 : e = 1 := Subtype.ext h2
    rw [h3, orderOf_one] at he
    exact absurd he (by norm_num)
  have he₀D : e₀ ∈ D := by
    rw [← h.cent]
    exact ⟨he₀S, Subgroup.mem_centralizer_iff.mpr fun d hd => hcomm d (h.le_S hd)⟩
  have he₀A : e₀ ∈ F.A := by
    have h1 : e₀ ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self he₀D he2
    rw [h.omegaIn_one_eq] at h1
    exact omegaIn_le 1 F.A h1
  obtain ⟨v, hv⟩ := K.exists_ev he₀A
  have hv2 : 2 • v = 0 := by
    rw [← K.ev_eq_one_iff, K.ev_nsmul, hv, pow_two, he2]
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact he1 (by rw [← hv, K.ev_zero])
  have hfix : ∀ g ∈ S, ∀ f : Arch76.Co → Arch76.Co,
      g⁻¹ * K.ev v * g = K.ev (f v) → f v = v := by
    intro g hg f hf
    apply K.ev_injective
    rw [← hf, hv, mul_assoc, ← hcomm g hg]
    group
  have hfuv := hfix _ F.uv_mem_S Arch76.fuv (K.conj_uv_ev v)
  have hft := hfix _ F.t_mem_S Arch76.ft (K.conj_t_ev v)
  have hfu := hfix _ F.u_mem_S Arch76.fu (K.conj_u_ev v)
  rcases Arch76.fixed_two_torsion_cases v hv2 hfuv hft hfu with h0 | h022
  · exact absurd h0 hv0
  · have hz : (K.x * K.y) ^ 2 = e₀ := by
      rw [← hv, h022, K.xy_sq]
      simp [Arch76.Config.ev, show (2 : ZMod 4).val = 2 from rfl]
    rw [hz]
    exact hcomm s hs

end StrothFrame.IsD

namespace StrothFrame

variable (F : StrothFrame G)

theorem isSylowOf_inf_centralizer {N P : Subgroup G} (hP : IsSylowOf 2 P N)
    (hNA : N ≤ Subgroup.normalizer (F.A : Set G)) (huv : F.dA.uv ∈ P) (ht : F.dA.t ∈ P) :
    IsSylowOf 2 (P ⊓ Subgroup.centralizer ({(F.dA.c : G)} : Set G))
      (N ⊓ Subgroup.centralizer ({(F.dA.c : G)} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set w : G := (F.dA.c : G) with hw
  set C := Subgroup.centralizer ({w} : Set G) with hC
  set Q := P ⊓ C with hQ
  have hQK : Q ≤ N ⊓ C := inf_le_inf_right C hP.le
  have hQp : IsPGroup 2 Q := hP.isPGroup.to_le inf_le_left
  obtain ⟨R, hR⟩ := (hQp.comap_subtype (K := N ⊓ C)).exists_le_sylow
  set T : Subgroup G := (R : Subgroup (N ⊓ C : Subgroup G)).map (N ⊓ C).subtype with hT
  have hTsyl : IsSylowOf 2 T (N ⊓ C) := ⟨R, rfl⟩
  have hQT : Q ≤ T := fun q hq => ⟨⟨q, hQK hq⟩, hR (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  have hTN : T ≤ N := hTsyl.le.trans inf_le_left
  have hTC : T ≤ C := hTsyl.le.trans inf_le_right
  obtain ⟨R', hR'⟩ := (hTsyl.isPGroup.comap_subtype (K := N)).exists_le_sylow
  set T' : Subgroup G := (R' : Subgroup N).map N.subtype with hT'
  have hT'syl : IsSylowOf 2 T' N := ⟨R', rfl⟩
  have hTT' : T ≤ T' := fun q hq => ⟨⟨q, hTN hq⟩, hR' (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  obtain ⟨k, hkN, hk⟩ := hP.exists_mem_conj hT'syl
  obtain ⟨s, hs, hsw⟩ := F.exists_conj_eq_w (hNA hkN)
  have hsP : s ∈ P := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    exacts [one_mem P, huv, ht, mul_mem huv ht]
  obtain ⟨g, hg⟩ : ∃ g : G, g = k * s := ⟨_, rfl⟩
  have hgw : g⁻¹ * w * g = w := by
    rw [hg, show (k * s)⁻¹ * w * (k * s) = s⁻¹ * (k⁻¹ * w * k) * s by group, hsw]
  have hgw' : g * w * g⁻¹ = w := by
    calc g * w * g⁻¹ = g * (g⁻¹ * w * g) * g⁻¹ := by rw [hgw]
      _ = w := by group
  have hmap : T.map (MulAut.conj g⁻¹).toMonoidHom ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : k⁻¹ * x * k ∈ P := (hk x).mp (hTT' hx)
    have hxC : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.mp (hTC hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [show g⁻¹ * x * g = s⁻¹ * (k⁻¹ * x * k) * s by rw [hg]; group]
      exact mul_mem (mul_mem (inv_mem hsP) hxP) hsP
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * x * g * w = g⁻¹ * x * (g * w * g⁻¹) * g := by group
        _ = g⁻¹ * (x * w) * g := by rw [hgw']; group
        _ = g⁻¹ * (w * x) * g := by rw [hxC]
        _ = g⁻¹ * w * g * (g⁻¹ * x * g) := by group
        _ = w * (g⁻¹ * x * g) := by rw [hgw]
  have hcard : Nat.card T ≤ Nat.card Q := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective]
    exact Subgroup.card_le_of_le hmap
  have hTQ : Q = T := Subgroup.eq_of_le_of_card_ge hQT hcard
  rw [hTQ]
  exact hTsyl

theorem not_isSylowOf_centralizer
    (hz : ∀ s ∈ (F.S : Subgroup G), s * (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2 =
      (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2 * s)
    (hall : IsConj (F.dA.c : G) ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2)) {Q : Subgroup G}
    (hQ : Q ≤ (F.S : Subgroup G) ⊓ Subgroup.centralizer ({(F.dA.c : G)} : Set G)) :
    ¬ IsSylowOf 2 Q (Subgroup.centralizer ({(F.dA.c : G)} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hQs
  set w : G := (F.dA.c : G) with hw
  set z : G := (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2 with hzdef
  set C := Subgroup.centralizer ({w} : Set G) with hC
  set S : Subgroup G := (F.S : Subgroup G) with hSdef
  obtain ⟨c, hc⟩ := isConj_iff.mp hall
  set S' : Subgroup G := S.map (MulAut.conj c⁻¹).toMonoidHom with hS'
  have hS'C : S' ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hwz : w = c⁻¹ * z * c := by rw [← hc]; group
    rw [hwz]
    calc c⁻¹ * x * c * (c⁻¹ * z * c) = c⁻¹ * (x * z) * c := by group
      _ = c⁻¹ * (z * x) * c := by rw [hz x hx]
      _ = c⁻¹ * z * c * (c⁻¹ * x * c) := by group
  have hS'p : IsPGroup 2 S' := F.S.isPGroup'.map _
  obtain ⟨R, hR⟩ := (hS'p.comap_subtype (K := C)).exists_le_sylow
  set T : Subgroup G := (R : Subgroup C).map C.subtype with hT
  have hTsyl : IsSylowOf 2 T C := ⟨R, rfl⟩
  have hS'T : S' ≤ T := fun q hq => ⟨⟨q, hS'C hq⟩, hR (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  have hTQ : Nat.card T = Nat.card Q := by rw [hTsyl.card_eq, hQs.card_eq]
  have hle : Nat.card S ≤ Nat.card Q := by
    rw [← hTQ, ← Subgroup.card_map_of_injective (f := (MulAut.conj c⁻¹).toMonoidHom)
      (MulAut.conj c⁻¹).injective]
    exact Subgroup.card_le_of_le hS'T
  have hlt : Q < S := by
    refine lt_of_le_of_ne (hQ.trans inf_le_left) fun hQS => ?_
    have huvQ : F.dA.uv ∈ Q := by rw [hQS]; exact F.uv_mem_S
    exact F.uv_not_mem_centralizer_w (hQ huvQ).2
  exact absurd (Subgroup.card_lt_of_lt hlt) (not_lt.mpr hle)

theorem exists_mem_normalizer_not_mem {N P : Subgroup G} (hP : IsSylowOf 2 P N)
    (hPS : P ≤ (F.S : Subgroup G)) (hNA : N ≤ Subgroup.normalizer (F.A : Set G))
    (huv : F.dA.uv ∈ P) (ht : F.dA.t ∈ P)
    (hz : ∀ s ∈ (F.S : Subgroup G), s * (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2 =
      (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2 * s)
    (hall : IsConj (F.dA.c : G) ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2)) :
    ∃ p ∈ Subgroup.normalizer
        ((P ⊓ Subgroup.centralizer ({(F.dA.c : G)} : Set G) : Subgroup G) : Set G),
      p ∈ Subgroup.centralizer ({(F.dA.c : G)} : Set G) ∧ p ∉ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  have hQ := F.isSylowOf_inf_centralizer hP hNA huv ht
  have hle : Subgroup.normalizer
      ((P ⊓ Subgroup.centralizer ({(F.dA.c : G)} : Set G) : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ({(F.dA.c : G)} : Set G) ≤ N := fun p hp => hne p hp.1 hp.2
  exact F.not_isSylowOf_centralizer hz hall (inf_le_inf_right _ hPS)
    (CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hQ hle)

end StrothFrame

end CFSG.CGT.Stroth77
