module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Cls
public import CFSG.GH74.GLS.Stage1.Main.NoFAutProof
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93OrdG2
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29NonTriv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section G2

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {r₁ r₂ : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem isComponent_of_normal_LBar {L : Subgroup (CentralizerBar z)} (hL : L ≤ LBar z)
    (hN : (L.subgroupOf (LBar z)).Normal) (hq : IsQuasisimple ↥L) : IsComponent L := by
  have hLBn : (LBar z).Normal := Stage1.Thm6.Prod.LBar_isNormal z
  exact ⟨hq, Subgroup.IsSubnormal.step L (LBar z) hL (Subgroup.Normal.isSubnormal hLBn) hN⟩

theorem PairShape.of_g2 (hsh : G2Shape z S r₁ r₂ L₁ L₂) (h3 : 3 < r₂) :
    PairShape z r₁ r₂ L₁ L₂ := by
  have hcomps := Stage1.Main.components_of_g2Shape hsh
  obtain ⟨ho₁, ho₂, hg₁, hcp, hs₁, hs₂, -, -, h4, -, -, -⟩ := hsh
  obtain ⟨hsup, hcomm, hcard⟩ := hcp
  have h4₁ : 4 ≤ r₁ := by omega
  have h4₂ : 4 ≤ r₂ := by omega
  obtain ⟨hq₁, -, -⟩ := Stage2.Local.sl2_model_facts ho₁ h4₁ hs₁
  obtain ⟨hq₂, -, -⟩ := Stage2.Local.sl2_model_facts ho₂ h4₂ hs₂
  have hL₁le : L₁ ≤ LBar z := hsup ▸ le_sup_left
  have hL₂le : L₂ ≤ LBar z := hsup ▸ le_sup_right
  have hN₁ : (L₁.subgroupOf (LBar z)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hL₁le, ← hsup]
    exact sup_le_normalizer_aux hcomm
  have hN₂ : (L₂.subgroupOf (LBar z)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hL₂le, ← hsup, sup_comm]
    exact sup_le_normalizer_aux (fun b hb a ha => (hcomm a ha b hb).symm)
  have hc₁ : IsComponent L₁ := isComponent_of_normal_LBar hL₁le hN₁ hq₁
  have hc₂ : IsComponent L₂ := isComponent_of_normal_LBar hL₂le hN₂ hq₂
  refine ⟨ho₁, ho₂, hg₁, h3, ?_, ⟨hsup, hcomm, hcard⟩, hs₁, hs₂, ?_, (h4 h3).2⟩
  · intro h
    subst h
    rw [inf_idem] at hcard
    have h1 := card_of_sl2_model_aux hs₁
    rw [hcard] at h1
    have h16 : 16 ≤ r₁ ^ 2 := by nlinarith
    have : 15 ≤ r₁ ^ 2 - 1 := by omega
    nlinarith
  · ext K
    constructor
    · intro hK
      rcases hcomps K hK with rfl | rfl <;> simp
    · intro hK
      rcases hK with rfl | rfl
      · exact hc₁
      · exact hc₂

omit [Finite G] in
theorem exists_noncomm_of_quasisimple {Q : Type*} [Group Q] (h : IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := h
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem S_le_cen {k : Kind} (ctx : Stage2Ctx G z k S) : S ≤ Cen z := by
  obtain ⟨Q, rfl⟩ := ctx.sylow
  exact Subgroup.map_subtype_le _

theorem not_swaps_g2 (hsh : G2Shape z S r₁ r₂ L₁ L₂) (h3 : 3 < r₂) {s : G} (hsS : s ∈ S)
    (hs : s ∈ Cen z) : ¬ Swaps z s L₁ L₂ := by
  have hp := PairShape.of_g2 hsh h3
  intro hsw
  obtain ⟨hs', h1, h2⟩ := hsw
  have hsT : toBar z ⟨s, hs⟩ ∈ SBar S z := ⟨⟨s, hs⟩, hsS, rfl⟩
  have h12 : L₁.map (MulAut.conj (toBar z ⟨s, hs⟩)).toMonoidHom = L₂ := by
    have := map_conj_map_conj_inv L₂ (toBar z ⟨s, hs⟩)⁻¹
    rw [inv_inv] at this
    have h2' : L₂.map (MulAut.conj (toBar z ⟨s, hs⟩)⁻¹).toMonoidHom = L₁ := h2
    rw [h2'] at this
    exact this
  have h21 : L₂.map (MulAut.conj (toBar z ⟨s, hs⟩)).toMonoidHom = L₁ := by
    have := map_conj_map_conj_inv L₁ (toBar z ⟨s, hs⟩)⁻¹
    rw [inv_inv] at this
    have h1' : L₁.map (MulAut.conj (toBar z ⟨s, hs⟩)⁻¹).toMonoidHom = L₂ := h1
    rw [h1'] at this
    exact this
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_quasisimple hp.isComponent₁.1
  exact IVK.Proofs2.Ivk93Adapt.false_of_swap (L₁ := L₁) (L₂ := L₂) (T := SBar S z) hp.prod.2.1
    ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩ hsh.2.2.2.2.2.2.2.2.2.2.1 hsT h12 h21

theorem nonswap_nontriv_g2 {k : Kind} (ctx : Stage2Ctx G z k S)
    (hsh : G2Shape z S r₁ r₂ L₁ L₂) (h3 : 3 < r₂) (hz2 : orderOf z = 2) {u : G} (huS : u ∈ S)
    (hu : u ∈ Cen z) (hu2 : u * u = 1) (hu1 : u ∉ zpowers z)
    (hn₁ : toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (hn₂ : toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))) :
    Stage1.Main.actOnK L₁ (toBar z ⟨u, hu⟩) hn₁ ≠ 1 ∧
      Stage1.Main.actOnK L₂ (toBar z ⟨u, hu⟩) hn₂ ≠ 1 := by
  have hp := PairShape.of_g2 hsh h3
  obtain ⟨-, -, -, -, -, -, -, -, -, hidx, hpgl₁, hpgl₂⟩ := hsh
  by_cases huR : u ∈ RC S z
  · exact actOnK_ne_one_of_mem_LBar hp hz2 hu hu2 hu1 (toBar_mem_LBar huR.2) hn₁ hn₂
  · exact actOnK_ne_one_of_index_two hp (R := RC S z) (M := S) (inf_le_right) (S_le_cen ctx)
      hidx.le huS huR hpgl₁ hpgl₂ hn₁ hn₂

theorem lemma29FirstAt_of_g2_gt3 {k : Kind} (ctx : Stage2Ctx G z k S) (hk : k = Kind.g2)
    (hsh : G2Shape z S r₁ r₂ L₁ L₂) (h3 : 3 < r₂) : Lemma29FirstAt z k := by
  subst hk
  have hz2 : orderOf z = 2 := ctx.central.1
  have hp := PairShape.of_g2 hsh h3
  cases ctx.data with
  | g2 hg =>
    refine lemma29FirstAt_of_pair ctx hp ?_ ?_ ?_
    · intro U hU hno
      exfalso
      obtain ⟨x, hxU, hx1⟩ : ∃ x ∈ U, x ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : U = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
        have h4 := hU.2
        rw [this, Subgroup.card_bot] at h4
        omega
      have hxo : orderOf x = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact four_sq_eq_one hU hxU) hx1
      exact hno x hxU (hg.one_class z x hz2 hxo)
    · intro u huS hu hu2 hu1 hsw
      exact absurd hsw (not_swaps_g2 hsh h3 huS hu)
    · intro u huS hu hu2 hu1 hn₁ hn₂
      exact nonswap_nontriv_g2 ctx hsh h3 hz2 huS hu hu2 hu1 hn₁ hn₂

end G2

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
