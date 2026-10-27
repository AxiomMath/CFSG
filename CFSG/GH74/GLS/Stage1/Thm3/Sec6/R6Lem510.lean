module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Lem62
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed3
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510Stmt
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Lem510

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

namespace Std6r1

variable {G : Type} [Group G] [Finite G] {z : G} {S K : Subgroup G}

theorem comp_rigid (h : Std6r1 G z S K) : IsRigidRankOneComp z K := by
  have : K ∈ {K' | IsRigidRankOneComp z K'} := by rw [h.comps]; exact Set.mem_singleton K
  exact this

theorem rigidProduct_eq (h : Std6r1 G z S K) : rigidProduct z = K := by
  unfold rigidProduct; rw [h.comps, sSup_singleton]

theorem cmap_eq (h : Std6r1 G z S K) {c : G} (hc : c ∈ centralizer ({z} : Set G)) :
    cmap c K = K := by
  have h1 : IsRigidRankOneComp z (cmap c K) := isRigidRankOneComp_cmap h.comp_rigid hc
  have h2 : cmap c K ∈ {K' | IsRigidRankOneComp z K'} := h1
  rw [h.comps] at h2
  exact h2

theorem normalizes_K (h : Std6r1 G z S K) {c : G} (hc : c ∈ centralizer ({z} : Set G)) :
    c ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  have h1 := h.cmap_eq ((centralizer ({z} : Set G)).inv_mem hc)
  have h2 : x ∈ cmap c⁻¹ K ↔ c⁻¹⁻¹ * x * c⁻¹ ∈ K := mem_cmap
  rw [h1, inv_inv] at h2
  exact h2

theorem z_mem_zStar (h : Std6r1 G z S K) : z ∈ zStar K := by
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.thm2
  have hcl := h.classical.2 t₀ ht₀C ht₀z ht₀n
  have hb : M.Syl2In (zpowers z) (zStar (rigidProduct z)) := syl2In_of_isSylowOf hcl.2.1
  rw [h.rigidProduct_eq] at hb
  exact hb.1 (mem_zpowers z)

theorem z_mem_Q (h : Std6r1 G z S K) : z ∈ Qof S K := ⟨h.z_mem_S, h.z_mem_zStar.2⟩

theorem eq_z_of_Q (h : Std6r1 G z S K) (hr : pRank 2 ↥(Qof S K) = 1) {a : G} (ha : a ∈ Qof S K)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) : a = z := by
  have hcomm : a * z = z * a := (h.z_cent ha.1).symm
  rcases rk1_of_pRank_one hr a ha z h.z_mem_Q ha2 h.z_sq hcomm with e | e | e
  · exact absurd e ha1
  · exact absurd e h.z_ne
  · exact e

theorem Pz_eq (h : Std6r1 G z S K) : Pz S z = S ⊓ K := by
  unfold Pz; rw [h.rigidProduct_eq]

theorem Qz_eq (h : Std6r1 G z S K) : Qz S z = S ⊓ cSec K := by
  unfold Qz rigidSectionCentralizer; rw [h.rigidProduct_eq]; rfl

theorem Rz_eq (h : Std6r1 G z S K) : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := by
  unfold Rz; rw [h.Pz_eq, h.Qz_eq]

end Std6r1

theorem prop_5_9_r1 (hIG : IG_15_16_ext) (hQ : Q_DSD) : Prop5_9_r1 := by
  intro G _ _ z S K h hrank a haQ ha2 haz hcomm
  obtain ⟨u₀, hu₀Q, hu₀sq, hu₀n, hinv⟩ := hQ G z S K h hrank
  have hz2 := h.z_sq
  have hz1 := h.z_ne
  have haS : a ∈ S := haQ.1
  have ha2' : a * a = 1 := R1.sq_one_of_orderOf_two ha2
  have ha1 : a ≠ 1 := ne_one_of_orderOf_eq_two ha2
  have hz' : ∀ s ∈ S, s * z * s⁻¹ = z := fun s hs => by
    rw [← h.z_cent hs]; group
  have hidx := relIndex_centralizer_le_two hz' hz2 hz1 hu₀n
  obtain ⟨x, hxC, hxQ0, -⟩ := hIG G (Cz z) S (S ⊓ centralizer ({u₀} : Set G)) (Oz z) a h.sylow
    inf_le_left hidx (TwoThin.pPrimeCoreOf_le (Cz z)) (fun y hy n hn => Oz_conj hy hn)
    card_Oz_odd haS ha2 hcomm
  have hxn : x ∈ normalizer (K : Set G) := h.normalizes_K hxC
  have hxin : x⁻¹ ∈ normalizer (K : Set G) := (normalizer (K : Set G)).inv_mem hxn
  have hycS : x⁻¹ * a * x ∈ cSec K := by
    have := cSec_conj K hxin haQ.2
    simpa using this
  have hyS : x⁻¹ * a * x ∈ S := hxQ0.1
  have hy2 : (x⁻¹ * a * x) * (x⁻¹ * a * x) = 1 := by
    calc (x⁻¹ * a * x) * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x := by group
      _ = 1 := by rw [ha2']; group
  have hy1 : x⁻¹ * a * x ≠ 1 := by
    intro e
    apply ha1
    calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
      _ = 1 := by rw [e]; group
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 hxC
  have hyz : x⁻¹ * a * x ≠ z := by
    intro e
    apply haz
    calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
      _ = x * z * x⁻¹ := by rw [e]
      _ = z := by rw [hxz]; group
  have hinvy := hinv (x⁻¹ * a * x) ⟨hyS, hycS⟩ hy2 hy1 hyz
  have hcent : (x⁻¹ * a * x) * u₀ = u₀ * (x⁻¹ * a * x) :=
    Subgroup.mem_centralizer_singleton_iff.1 hxQ0.2
  have e1 : (x⁻¹ * a * x) * u₀ * (x⁻¹ * a * x)⁻¹ = u₀ := by rw [hcent]; group
  rw [e1] at hinvy
  apply hz1
  calc z = u₀⁻¹ * (u₀ * z) := by group
    _ = u₀⁻¹ * u₀ := by rw [← hinvy]
    _ = 1 := by group

theorem lemma_5_10_r1 (h46 : Prop4_6) (hf : IVK_fAut_r1) (hq : TwoGroup_coset_sq_gen)
    (h32 : IVK_3_2a_r1) (hcyc : Lem510_cyc') : Lemma5_10_r1 := by
  intro G _ _ z S K h hm b hbS hb2 hfb hnb
  obtain ⟨hin, hsq, hco, hce⟩ := hf G z S K h
  have hz2 := h.z_sq
  have hbn : b ∈ normalizer (K : Set G) := hfb.1
  have hbR : b * b ∈ (S ⊓ K) ⊔ (S ⊓ cSec K) := by
    have := hb2
    rwa [h.Rz_eq] at this
  have hbb : b * b ∈ innSub K :=
    (sup_le (inf_le_right.trans (le_innSub K)) (inf_le_right.trans (cSec_le_innSub K))) hbR
  have hbbc : b * b ∈ cSec K := hsq b hfb hbb
  have hbbQ : b * b ∈ Qof S K := ⟨S.mul_mem hbS hbS, hbbc⟩
  have hbQ : b ∉ Qof S K := fun hmem => hnb hmem.2
  have hb_norm : b ∈ normalizer ((Qof S K : Subgroup G) : Set G) :=
    M.mem_normalizer_of_both (fun q hq => conj_mem_Qof hbS hbn hq) (fun q hq => by
      have := conj_mem_Qof (S.inv_mem hbS) ((normalizer (K : Set G)).inv_mem hbn) hq
      simpa using this)
  set X : Subgroup G := Qof S K ⊔ zpowers b with hX
  have hXS : X ≤ S := sup_le inf_le_left (zpowers_le.2 hbS)
  have hXp : IsPGroup 2 ↥X := h.S_pgroup.to_le hXS
  have hQX : Qof S K ≤ X := le_sup_left
  have hbX : b ∈ X := mem_sup_right (mem_zpowers b)
  have hcov : ∀ x ∈ X, x ∈ Qof S K ∨ x * b⁻¹ ∈ Qof S K := fun x hx =>
    mem_or_mul_inv_mem hb_norm hbbQ hx
  have hzQ : z ∈ Qof S K := h.z_mem_Q
  suffices H : ∃ a₀ ∈ S, orderOf a₀ = 2 ∧ InducesFAut a₀ K ∧ a₀ ∉ cSec K by
    obtain ⟨a₀, ha₀S, ha₀2, ha₀f, ha₀n⟩ := H
    refine ⟨a₀, ha₀S, ha₀2, ha₀f, ?_⟩
    have haz : a₀ ≠ z := fun e => ha₀n (e ▸ hzQ.2)
    exact h32 G z S K h a₀ ha₀S ha₀2 haz ha₀f ha₀n
  by_cases hcase : ∃ u ∈ X, u ∉ Qof S K ∧ u * u = 1
  · obtain ⟨u, huX, huQ, hu2⟩ := hcase
    have hub : u * b⁻¹ ∈ Qof S K := (hcov u huX).resolve_left huQ
    have hu1 : u ≠ 1 := fun e => huQ (e ▸ Subgroup.one_mem _)
    exact ⟨u, hXS huX, orderOf_eq_two_of_mul_self_eq_one hu2 hu1,
      inducesFAut_of_mul_cSec hfb hub.2, fun hc => huQ ⟨hXS huX, hc⟩⟩
  · push Not at hcase
    have huniq : ∀ u ∈ X, u * u = 1 → u = 1 ∨ u = z := by
      intro u huX hu2
      by_cases huQ : u ∈ Qof S K
      · by_cases hu1 : u = 1
        · exact Or.inl hu1
        · exact Or.inr (h.eq_z_of_Q hm huQ hu2 hu1)
      · exact absurd hu2 (hcase u huX huQ)
    by_cases hXc : IsCyclic ↥X
    · rcases hcyc G z S K h hm b hbS hbbQ hfb hnb hXc with ⟨F, hF, hFc⟩ | hH
      · exact absurd hFc (h46 G z S K F hF)
      · exact hH
    · obtain ⟨t, htX, htQ, ht2⟩ := hq G X (Qof S K) z b hXp hQX hbX hbQ hbbQ hcov huniq hXc
      have htS : t ∈ S := hXS htX
      have htb : t * b⁻¹ ∈ Qof S K := (hcov t htX).resolve_left htQ
      have hFAt : InducesFAut t K := inducesFAut_of_mul_cSec hfb htb.2
      have htn : t ∉ cSec K := fun hc => htQ ⟨htS, hc⟩
      have htz : t * t ∈ cSec K := by rw [ht2]; exact hzQ.2
      obtain ⟨y, hyP, hy2, hyt⟩ := hce t htS hFAt htn htz
      have ha2 : (y * t) * (y * t) = 1 := by
        calc (y * t) * (y * t) = y * (t * y) * t := by group
          _ = y * (y * t) * t := by rw [← hyt]
          _ = (y * y) * (t * t) := by group
          _ = 1 := by rw [hy2, ht2, hz2]
      have hancs : y * t ∉ cSec K := by
        intro hc
        have hy1 : y⁻¹ ∈ innSub K := (innSub K).inv_mem (le_innSub K hyP.2)
        have hc1 : y * t ∈ innSub K := cSec_le_innSub K hc
        have ht1 : t ∈ innSub K := by
          have := (innSub K).mul_mem hy1 hc1
          simpa using this
        exact htn (hin t hFAt ht1)
      have hnorm_a : y * t ∈ normalizer (K : Set G) :=
        (normalizer (K : Set G)).mul_mem (le_normalizer hyP.2) hFAt.1
      have hFA : InducesFAut (y * t) K := by
        refine hco (y * t) t hnorm_a hFAt.1 ?_ htz htn ?_ hFAt
        · rw [ha2]; exact (cSec K).one_mem
        · have : y * t * t⁻¹ = y := by group
          rw [this]; exact le_innSub K hyP.2
      have ha1 : y * t ≠ 1 := fun e => hancs (e ▸ (cSec K).one_mem)
      exact ⟨y * t, S.mul_mem hyP.1 htS, orderOf_eq_two_of_mul_self_eq_one ha2 ha1, hFA, hancs⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
