module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenUnique
import CFSG.LargeExtraspecial.S5Comp
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen

open CFSG.Open CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem barM_map_conj {X L : Subgroup G} (hLX : L ≤ X) {t : G} (htX : t ∈ X) :
    barM X (L.map (MulAut.conj t).toMonoidHom) =
      (barM X L).map (MulAut.conj (QuotientGroup.mk (⟨t, htX⟩ : ↥X) :
        ↥X ⧸ CFSG.pCore 2 ↥X)).toMonoidHom := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    obtain ⟨l, hl, hlx⟩ := hx
    refine ⟨QuotientGroup.mk' _ ⟨l, hLX hl⟩, ⟨⟨l, hLX hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩, ?_⟩
    have hx' : x = ⟨t, htX⟩ * ⟨l, hLX hl⟩ * (⟨t, htX⟩ : ↥X)⁻¹ := Subtype.ext hlx.symm
    rw [hx', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    rfl
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    refine ⟨⟨t, htX⟩ * x * (⟨t, htX⟩ : ↥X)⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact ⟨x, hx, rfl⟩
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
      rfl

theorem isTwoPrimeComponent_map_conj {X L : Subgroup G} (hL : IsTwoPrimeComponent X L) {t : G}
    (htX : t ∈ X) : IsTwoPrimeComponent X (L.map (MulAut.conj t).toMonoidHom) := by
  have hX : X.map (MulAut.conj t).toMonoidHom = X := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact X.mul_mem (X.mul_mem htX hy) (X.inv_mem htX)
    · intro hx
      refine ⟨t⁻¹ * x * t, X.mul_mem (X.mul_mem (X.inv_mem htX) hx) htX, ?_⟩
      simp [mul_assoc]
  refine ⟨hX ▸ Subgroup.map_mono hL.le, hX ▸ hL.subnormal.map _, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hL.perfect]
  · rw [barM_map_conj hL.le htX]
    exact CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hL.component (Subgroup.mem_top _)

theorem eq_of_barM_eq {X L₁ L₂ : Subgroup G} (h₁ : IsSubnormal L₁ X) (h₂ : IsSubnormal L₂ X)
    (hp₁ : ⁅L₁, L₁⁆ = L₁) (hp₂ : ⁅L₂, L₂⁆ = L₂) (h₁X : L₁ ≤ X) (h₂X : L₂ ≤ X)
    (he : barM X L₁ = barM X L₂) : L₁ = L₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := pCoreOf 2 X with hT
  have hT2 : IsPGroup 2 T := (CFSG.pCore_isPGroup (G := ↥X) (p := 2)).map X.subtype
  have hTX : T ≤ X := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hXT : X ≤ normalizer (T : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨x, hx⟩ * w * (⟨x, hx⟩ : ↥X)⁻¹,
        (CFSG.pCore_normal (G := ↥X) (p := 2)).conj_mem w hw _, rfl⟩
    · intro hy
      obtain ⟨w, hw, hwy⟩ := hy
      have hyX : y ∈ X := by
        have h2 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
        rw [← h2, ← hwy]
        exact X.mul_mem (X.mul_mem (X.inv_mem hx) w.2) hx
      refine ⟨⟨y, hyX⟩, ?_, rfl⟩
      have h3 := (CFSG.pCore_normal (G := ↥X) (p := 2)).conj_mem w hw (⟨x, hx⟩ : ↥X)⁻¹
      have h4 : (⟨x, hx⟩ : ↥X)⁻¹ * w * ((⟨x, hx⟩ : ↥X)⁻¹)⁻¹ = ⟨y, hyX⟩ := by
        apply Subtype.ext
        have hwy' : (w : G) = x * y * x⁻¹ := hwy
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [hwy']
        group
      rwa [h4] at h3
  have hle : ∀ {A B : Subgroup G}, A ≤ X → barM X A ≤ barM X B → A ≤ B ⊔ T := by
    intro A B hAX hAB a ha
    obtain ⟨b, hb, hba⟩ := hAB ⟨⟨a, hAX ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hb
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hba
    have hw : ((b⁻¹ * ⟨a, hAX ha⟩ : ↥X) : G) ∈ T := ⟨_, hba, rfl⟩
    have : a = (b : G) * ((b⁻¹ * ⟨a, hAX ha⟩ : ↥X) : G) := by simp
    rw [this]
    exact Subgroup.mul_mem_sup hb hw
  have h12 := hle h₁X he.le
  have h21 := hle h₂X he.ge
  set R := L₁ ⊔ T with hR
  have hRX : R ≤ X := sup_le h₁X hTX
  have hR₂ : R ≤ L₂ ⊔ T := sup_le h12 le_sup_right
  have hs₁ : IsSubnormal L₁ R := by
    have := h₁.inf_of_le hRX
    rwa [inf_eq_left.mpr le_sup_left] at this
  have hs₂ : IsSubnormal L₂ R := by
    have hL₂R : L₂ ≤ R := h21.trans (sup_le le_sup_left le_sup_right)
    have := h₂.inf_of_le hRX
    rwa [inf_eq_left.mpr hL₂R] at this
  exact eq_of_perfect_of_isSubnormal hT2 (hRX.trans hXT) hs₁ hs₂ hp₁ hp₂ le_rfl hR₂

theorem barM_map_conj_ne {X L : Subgroup G} (hL : IsTwoPrimeComponent X L) {t : G} (htX : t ∈ X)
    (htL : L.map (MulAut.conj t).toMonoidHom ≠ L) :
    barM X L ≠ barM X (L.map (MulAut.conj t).toMonoidHom) := by
  intro he
  have hL' := isTwoPrimeComponent_map_conj hL htX
  exact htL (eq_of_barM_eq hL.subnormal hL'.subnormal hL.perfect hL'.perfect hL.le hL'.le he).symm

theorem four_le_pRank_of_two_blocks_of_inf {X L : Subgroup G} (hL : IsTwoPrimeComponent X L)
    {t : G} (htX : t ∈ X) (htL : L.map (MulAut.conj t).toMonoidHom ≠ L)
    {E : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} (hEL : E ≤ barM X L) (hE : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 3 ^ 2) (hEL' : E ⊓ barM X (L.map (MulAut.conj t).toMonoidHom) = ⊥) :
    4 ≤ Open.pRank 3 X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set tb : ↥X ⧸ CFSG.pCore 2 ↥X := QuotientGroup.mk (⟨t, htX⟩ : ↥X) with htb
  set L' := L.map (MulAut.conj t).toMonoidHom with hL'
  have hL'c := isTwoPrimeComponent_map_conj hL htX
  have hne := barM_map_conj_ne hL htX htL
  have hcomm := CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hL.component
    hL'c.component hne
  set E' := E.map (MulAut.conj tb).toMonoidHom with hE'
  have hE'L : E' ≤ barM X L' := by
    rw [hL', barM_map_conj hL.le htX]
    exact Subgroup.map_mono hEL
  have hEE : ∀ a ∈ E, ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have h1 := Subgroup.commutator_mem_commutator (hEL ha) (hE'L hb)
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hEE' : E ⊓ E' = ⊥ := by
    rw [eq_bot_iff, ← hEL']
    exact inf_le_inf_left E hE'L
  let φ : ↥E × ↥E' →* ↥X ⧸ CFSG.pCore 2 ↥X :=
    MonoidHom.noncommCoprod E.subtype E'.subtype fun a b => hEE a a.2 b b.2
  have hφ : Function.Injective φ := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    change (a₁ : ↥X ⧸ CFSG.pCore 2 ↥X) * (b₁ : ↥X ⧸ CFSG.pCore 2 ↥X) =
      (a₂ : ↥X ⧸ CFSG.pCore 2 ↥X) * (b₂ : ↥X ⧸ CFSG.pCore 2 ↥X) at h
    have h1 : (a₂ : ↥X ⧸ CFSG.pCore 2 ↥X)⁻¹ * a₁ = b₂ * (b₁ : ↥X ⧸ CFSG.pCore 2 ↥X)⁻¹ := by
      calc (a₂ : ↥X ⧸ CFSG.pCore 2 ↥X)⁻¹ * a₁
          = (a₂ : ↥X ⧸ CFSG.pCore 2 ↥X)⁻¹ * (a₁ * b₁) * (b₁ : ↥X ⧸ CFSG.pCore 2 ↥X)⁻¹ := by
            group
        _ = b₂ * (b₁ : ↥X ⧸ CFSG.pCore 2 ↥X)⁻¹ := by rw [h]; group
    have hmem : (a₂ : ↥X ⧸ CFSG.pCore 2 ↥X)⁻¹ * a₁ ∈ E ⊓ E' :=
      ⟨E.mul_mem (E.inv_mem a₂.2) a₁.2, h1 ▸ E'.mul_mem b₂.2 (E'.inv_mem b₁.2)⟩
    rw [hEE', Subgroup.mem_bot] at hmem
    have ha : a₁ = a₂ := Subtype.ext (by
      have := congrArg (fun z => (a₂ : ↥X ⧸ CFSG.pCore 2 ↥X) * z) hmem
      simpa using this)
    have hb : b₁ = b₂ := Subtype.ext (by
      rw [hmem] at h1
      have := congrArg (fun z => z * (b₁ : ↥X ⧸ CFSG.pCore 2 ↥X)) h1
      simpa using this)
    rw [ha, hb]
  obtain ⟨⟨hEcomm⟩, hEexp⟩ := hE
  have hE'card : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj tb).injective, hE9]
  have hE'comm : ∀ b₁ b₂ : ↥E', b₁ * b₂ = b₂ * b₁ := by
    rintro ⟨_, c₁, hc₁, rfl⟩ ⟨_, c₂, hc₂, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hEcomm.comm ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩)
  have hE'pow : ∀ b : ↥E', b ^ 3 = 1 := by
    rintro ⟨_, c, hc, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hEexp c hc, map_one]
  have hcomm' : ∀ a b : ↥E × ↥E', a * b = b * a := fun a b =>
    Prod.ext (hEcomm.comm a.1 b.1) (hE'comm a.2 b.2)
  have hpow : ∀ a : ↥E × ↥E', a ^ 3 = 1 := fun a =>
    Prod.ext (Subtype.ext (by simpa using hEexp a.1 a.1.2)) (hE'pow a.2)
  have hcard : Nat.card (↥E × ↥E') = 3 ^ 4 := by
    rw [Nat.card_prod, hE9, hE'card]
    norm_num
  have h4 : 4 ≤ Open.pRank 3 (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) :=
    CFSG.SectionRank.le_pRank_of_injective (by norm_num) hcomm' hpow hcard φ hφ le_top
  have hO : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥X) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥X) (p := 2)).exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup X,
    ← CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥X) hO]
  exact h4

theorem four_le_pRank_of_two_blocks {X L : Subgroup G} (hL : IsTwoPrimeComponent X L) {t : G}
    (htX : t ∈ X) (htL : L.map (MulAut.conj t).toMonoidHom ≠ L)
    {E : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} (hEL : E ≤ barM X L) (hE : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 3 ^ 2)
    (hEC : E ⊓ Subgroup.centralizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) = ⊥) :
    4 ≤ Open.pRank 3 X := by
  have hcomm := CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hL.component
    (isTwoPrimeComponent_map_conj hL htX).component (barM_map_conj_ne hL htX htL)
  refine four_le_pRank_of_two_blocks_of_inf hL htX htL hEL hE hE9 ?_
  rw [eq_bot_iff, ← hEC]
  intro z ⟨hz, hz'⟩
  refine ⟨hz, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  have h1 := Subgroup.commutator_mem_commutator hl hz'
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem exists_elemAbelian_nine {Y : Type*} [Group Y] [Finite Y] {H : Subgroup Y}
    (h2 : 2 ≤ Open.pRank 3 H) :
    ∃ E : Subgroup Y, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E', hE'H, hE', hcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) H
  obtain ⟨⟨hcomm⟩, hexp⟩ := hE'
  have hdvd : 3 ^ 2 ∣ Nat.card E' := by
    rw [hcard]
    exact pow_dvd_pow 3 h2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  have hcommK : ∀ a b : ↥(K.map E'.subtype), a * b = b * a := by
    rintro ⟨_, a', -, rfl⟩ ⟨_, b', -, rfl⟩
    apply Subtype.ext
    change ((a' : ↥E') : Y) * ((b' : ↥E') : Y) = ((b' : ↥E') : Y) * ((a' : ↥E') : Y)
    exact congrArg Subtype.val (hcomm.comm (a' : ↥E') (b' : ↥E'))
  refine ⟨K.map E'.subtype, (Subgroup.map_subtype_le K).trans hE'H, ⟨⟨⟨hcommK⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨a', -, rfl⟩
    exact hexp _ a'.2
  · rw [Subgroup.card_map_of_injective E'.subtype_injective, hK]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen
