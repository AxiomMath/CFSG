module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29First
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29PairCore
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Bar
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29G3Aut

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank

section G3

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {r₁ : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem g3_components (hsh : G2Shape z S r₁ 3 L₁ L₂) :
    IsComponent L₁ ∧ ∀ K : Subgroup (CentralizerBar z), IsComponent K → K = L₁ := by
  have hcomps := Stage1.Main.components_of_g2Shape hsh
  obtain ⟨ho₁, -, hg₁, hcp, hs₁, hs₂, -, -, -, -, -, -⟩ := hsh
  obtain ⟨hsup, hcomm, -⟩ := hcp
  have h4₁ : 4 ≤ r₁ := by omega
  obtain ⟨hq₁, -, -⟩ := Stage2.Local.sl2_model_facts ho₁ h4₁ hs₁
  have hL₁le : L₁ ≤ LBar z := hsup ▸ le_sup_left
  have hN₁ : (L₁.subgroupOf (LBar z)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hL₁le, ← hsup]
    exact sup_le_normalizer_aux hcomm
  have hc₁ : IsComponent L₁ := isComponent_of_normal_LBar hL₁le hN₁ hq₁
  refine ⟨hc₁, fun K hK => ?_⟩
  rcases hcomps K hK with h | h
  · exact h
  · exfalso
    subst h
    exact LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hK.1
      (Stage1.Main.isSolvable_of_hasSL2Model_three hs₂)

omit [Finite G] in
theorem g3_pairCore (hsh : G2Shape z S r₁ 3 L₁ L₂) : PairCore z r₁ 3 L₁ L₂ := by
  obtain ⟨ho₁, -, hg₁, hcp, hs₁, hs₂, -, h3, -, -, -, -⟩ := hsh
  have h4₁ : 4 ≤ r₁ := by omega
  obtain ⟨-, hZ₁, hinv₁⟩ := Stage2.Local.sl2_model_facts ho₁ h4₁ hs₁
  obtain ⟨hZ₂, hinv₂⟩ := L29G3.sl2_three_center_inv hs₂
  refine ⟨hcp, hZ₁, hZ₂, hinv₁, hinv₂, card_of_sl2_model_aux hs₁, card_of_sl2_model_aux hs₂, ?_⟩
  rw [(h3 rfl).2]
  exact Subgroup.map_subtype_le _

theorem g3_mem_normalizer₁ (hsh : G2Shape z S r₁ 3 L₁ L₂) (c : CentralizerBar z) :
    c ∈ normalizer (L₁ : Set (CentralizerBar z)) := by
  obtain ⟨hc₁, hall⟩ := g3_components hsh
  rw [mem_normalizer_iff_map_conj_eq]
  exact hall _ (L29Pair.isComponent_map_conj hc₁ c)

omit [Finite G] in
theorem g3_mem_L₂_iff (hsh : G2Shape z S r₁ 3 L₁ L₂) (w : CentralizerBar z) :
    w ∈ L₂ ↔ w ∈ LBar z ∧ ∀ a ∈ L₁, w * a = a * w := by
  have hp := g3_pairCore hsh
  obtain ⟨hsup, hcomm, hcard⟩ := hp.prod
  constructor
  · intro hw
    exact ⟨hsup ▸ (le_sup_right : L₂ ≤ L₁ ⊔ L₂) hw, fun a ha => (hcomm a ha w hw).symm⟩
  · rintro ⟨hwL, hwc⟩
    rw [← hsup] at hwL
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute_aux hcomm hwL
    have hac : ∀ x ∈ L₁, x * a = a * x := by
      intro x hx
      have h1 := hwc x hx
      rw [hab] at h1
      have h2 := hcomm x hx b hb
      have h3 : a * x * b = x * a * b := by
        calc a * x * b = a * (x * b) := by group
          _ = a * (b * x) := by rw [h2]
          _ = a * b * x := by group
          _ = x * (a * b) := h1
          _ = x * a * b := by group
      exact (mul_right_cancel h3).symm
    have haL₂ : a ∈ L₂ := central_mem_of_card_inf hcomm hp.zc₁ hcard ha hac
    rw [hab]
    exact L₂.mul_mem haL₂ hb

theorem g3_mem_normalizer₂ (hsh : G2Shape z S r₁ 3 L₁ L₂) (c : CentralizerBar z) :
    c ∈ normalizer (L₂ : Set (CentralizerBar z)) := by
  have key : ∀ c : CentralizerBar z, ∀ x ∈ L₂, c * x * c⁻¹ ∈ L₂ := by
    intro c x hx
    rw [g3_mem_L₂_iff hsh] at hx ⊢
    obtain ⟨hxL, hxc⟩ := hx
    refine ⟨?_, fun a ha => ?_⟩
    · have hn := (LBar_normal z).conj_mem x hxL c
      exact hn
    · have hca : c⁻¹ * a * c⁻¹⁻¹ ∈ L₁ := by
        have := (Subgroup.mem_normalizer_iff.mp (g3_mem_normalizer₁ hsh c⁻¹) a).mp ha
        exact this
      have h1 := hxc _ hca
      calc c * x * c⁻¹ * a = c * (x * (c⁻¹ * a * c⁻¹⁻¹)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * a * c⁻¹⁻¹) * x) * c⁻¹ := by rw [h1]
        _ = a * (c * x * c⁻¹) := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key c x, fun h => ?_⟩
  have := key c⁻¹ _ h
  simpa [mul_assoc] using this

theorem g3_actOnK_ne_one {k : Kind} (ctx : Stage2Ctx G z k S) (hsh : G2Shape z S r₁ 3 L₁ L₂)
    {u : G} (huS : u ∈ S) (hu : u ∈ Cen z) (hu2 : u * u = 1) (hu1 : u ∉ zpowers z) :
    Stage1.Main.actOnK L₁ (toBar z ⟨u, hu⟩) (g3_mem_normalizer₁ hsh _) ≠ 1 ∧
      Stage1.Main.actOnK L₂ (toBar z ⟨u, hu⟩) (g3_mem_normalizer₂ hsh _) ≠ 1 := by
  have hp := g3_pairCore hsh
  have hz2 : orderOf z = 2 := ctx.central.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hidx, hpgl₁, hpgl₂⟩ := id hsh
  by_cases huR : u ∈ RC S z
  · exact hp.actOnK_ne_one_of_mem_LBar hz2 hu hu2 hu1 (toBar_mem_LBar huR.2) _ _
  · exact hp.actOnK_ne_one_of_index_two (R := RC S z) (M := S) inf_le_right (S_le_cen ctx)
      hidx.le huS huR hpgl₁ hpgl₂ _ _

theorem twoNilp_centralizer_bar_g2_three {k : Kind} (ctx : Stage2Ctx G z k S)
    (hsh : G2Shape z S r₁ 3 L₁ L₂) {u : G} (huS : u ∈ S) (hu : u ∈ Cen z) (hu2 : u * u = 1)
    (hu1 : u ∉ zpowers z) :
    TwoNilp ↥(centralizer ({toBar z ⟨u, hu⟩} : Set (CentralizerBar z))) := by
  have hp := g3_pairCore hsh
  obtain ⟨hc₁, -⟩ := g3_components hsh
  have hsq : (⟨u, hu⟩ : ↥(Cen z)) * ⟨u, hu⟩ = 1 := Subtype.ext hu2
  have hu2' : toBar z ⟨u, hu⟩ * toBar z ⟨u, hu⟩ = 1 := by rw [← map_mul, hsq, map_one]
  have hn₁ := g3_mem_normalizer₁ hsh (toBar z ⟨u, hu⟩)
  have hn₂ := g3_mem_normalizer₂ hsh (toBar z ⟨u, hu⟩)
  obtain ⟨ht₁, ht₂⟩ := g3_actOnK_ne_one ctx hsh huS hu hu2 hu1
  obtain ⟨ho₁, -, hg₁, -, hs₁, hs₂, -, -, -, -, -, -⟩ := id hsh
  have h₁ : TwoNilp ↥(centralizer ({Stage1.Main.actOnK L₁ (toBar z ⟨u, hu⟩) hn₁} :
      Set (MulAut ↥L₁))) := by
    obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := hs₁
    have hq' : Nat.card F = r₁ := hq
    have hL2 : IVK.L2Field F := ⟨hq' ▸ ho₁, hq' ▸ hg₁⟩
    exact twoNilp_centralizer_sl2 hL2 (e.trans (specialLinearGroupEquivStatedSL 2 F).symm) _
      (actOnK_mul_self hn₁ hu2') ht₁
      (not_fixedCond_actOnK ctx ho₁ (by omega) hc₁ ⟨F, hF, hFin, hq, ⟨e⟩⟩ huS hu hu2 hn₁ ht₁)
  have h₂ : TwoNilp ↥(centralizer ({Stage1.Main.actOnK L₂ (toBar z ⟨u, hu⟩) hn₂} :
      Set (MulAut ↥L₂))) :=
    L29G3.twoNilp_centralizer_aut_sl3 hs₂ _ (actOnK_mul_self hn₂ hu2') ht₂
  have hD := L29Pair.twoNilp_inf_normalizers L₁ L₂ hp.prod.2.2.le
    (fun c h₁ h₂ => hp.centralizer_le_inf c h₁ h₂) (toBar z ⟨u, hu⟩) hn₁ hn₂ h₁ h₂
  have hall : centralizer ({toBar z ⟨u, hu⟩} : Set (CentralizerBar z)) ⊓
      normalizer (L₁ : Set (CentralizerBar z)) ⊓ normalizer (L₂ : Set (CentralizerBar z)) =
      centralizer ({toBar z ⟨u, hu⟩} : Set (CentralizerBar z)) := by
    ext c
    constructor
    · exact fun hc => hc.1.1
    · intro hc
      exact ⟨⟨hc, g3_mem_normalizer₁ hsh c⟩, g3_mem_normalizer₂ hsh c⟩
  rw [hall] at hD
  exact hD

end G3

theorem l29G2Three_proved : L29G2Three := by
  intro G _ _ z S ctx r₁ L₁ L₂ hsh
  have hz2 : orderOf z = 2 := ctx.central.1
  cases ctx.data with
  | g2 hg =>
    refine lemma29FirstAt_of_bar ctx ?_ ?_
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
    · intro u huS hu hu2 hu1
      exact twoNilp_centralizer_bar_g2_three ctx hsh huS hu hu2 hu1

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
