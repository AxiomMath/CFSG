module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEight
public import CFSG.CGT.PushingUpLit.CGT6.EmbTY

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit
open scoped commutatorElement Pointwise

section Small

variable {Γ : Type} [Group Γ]

theorem noTwoQuotient_of_card_three {Y : Subgroup Γ} (h3 : Nat.card ↥Y = 3) :
    SubTwo.NoTwoQuotient Y := by
  intro N hNY _ hpow
  refine le_antisymm hNY fun y hy => ?_
  obtain ⟨k, hk⟩ := hpow y hy
  have hy3 : y ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥Y) (x := ⟨y, hy⟩)
    rw [h3] at this
    exact congrArg Subtype.val this
  have h4 : 4 ^ k % 3 = 1 := by simp [Nat.pow_mod]
  have h44 : 2 ^ k * 2 ^ k = 3 * (4 ^ k / 3) + 1 := by
    have h1 : 2 ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; norm_num
    have h2 := Nat.div_add_mod (4 ^ k) 3
    rw [h4] at h2
    rw [h1]
    exact h2.symm
  have hyy : (y ^ 2 ^ k) ^ 2 ^ k = y := by
    rw [← pow_mul, h44, pow_add, pow_mul, hy3, one_pow, one_mul, pow_one]
  rw [← hyy]
  exact N.pow_mem hk _

theorem oTwoIn_eq_bot_of_card_three {Y : Subgroup Γ} (h3 : Nat.card ↥Y = 3) : oTwoIn Y = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxY : x ∈ Y := oTwoIn_le Y hx
  obtain ⟨k, hk⟩ := SixThree.isPGroup_oTwoIn Y ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hy3 : x ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥Y) (x := ⟨x, hxY⟩)
    rw [h3] at this
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have hord : orderOf x ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk')
    (orderOf_dvd_of_pow_eq_one hy3)
  rw [hcop] at hord
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord))

theorem le_oTwoIn_of_normal {M N : Subgroup Γ} (hNM : N ≤ M)
    (hMN : M ≤ Subgroup.normalizer (N : Set Γ)) (hN : IsPGroup 2 ↥N) : N ≤ oTwoIn M := by
  have hn : (N.subgroupOf M).Normal := by
    refine ⟨fun n hn m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hMN m.2) n).1 hn
  have hp : IsPGroup 2 ↥(N.subgroupOf M) := hN.comap_of_injective M.subtype M.subtype_injective
  have hle : N.subgroupOf M ≤ CFSG.pCore 2 ↥M := le_sSup ⟨hn, hp⟩
  intro x hx
  exact ⟨⟨x, hNM hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem oTwoIn_le_of_isSubnormal {K H : Subgroup Γ} (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsSubnormal) : oTwoIn K ≤ oTwoIn H := by
  have key : ∀ Z : Subgroup ↥H, Z.IsSubnormal → oTwoIn (Z.map H.subtype) ≤ oTwoIn H := by
    intro Z hZ
    induction hZ with
    | top => rw [Subgroup.map_top, Subgroup.range_subtype]
    | step Z Z' hle hZ' hN ih =>
      refine le_trans ?_ ih
      have hle' : Z.map H.subtype ≤ Z'.map H.subtype := Subgroup.map_mono hle
      refine le_oTwoIn_of_normal ((oTwoIn_le _).trans hle') ?_ (SixThree.isPGroup_oTwoIn _)
      have hn : Z' ≤ Subgroup.normalizer (Z : Set ↥H) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
      exact ((Subgroup.map_mono hn).trans (Subgroup.le_normalizer_map _)).trans
        (normalizer_le_normalizer_oTwoIn _)
  have := key _ hK
  rwa [Subgroup.map_subgroupOf_eq_of_le hKH] at this

theorem not_isPGroup_two_of_card_three {Y : Subgroup Γ} (h3 : Nat.card ↥Y = 3) :
    ¬ IsPGroup 2 ↥Y := by
  intro hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥Y := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  rw [h3] at hk
  rcases k with _ | k
  · simp at hk
  · rw [pow_succ] at hk
    omega

end Small

section Prime

variable {V : Type} [CommGroup V] [Finite V]

theorem Lift5.subnormal_of_not_perfect (hV : ∀ v : V, v ^ 2 = 1) {H Y X₁ : Subgroup (MulAut V)}
    (h3 : Nat.card ↥Y = 3) (h : Lift5 H Y X₁) (hnp : ⁅X₁, X₁⁆ ≠ X₁)
    (hQY : ⁅oTwoIn H, Y⁆ = ⊥) : (Y.subgroupOf H).IsSubnormal := by
  obtain ⟨hYX, hXH, hsubX, hc, harr⟩ := h
  by_cases hYeq : Y = X₁
  · rw [hYeq]
    exact hsubX
  have hprime : (Nat.card (↥(yuHol X₁) ⧸ pCore 2 ↥(yuHol X₁))).Prime := by
    rcases hc.1.quotient_type with hq | hp
    · exact absurd (commutator_eq_of_yuHol (inClassX_commutator_eq_self hc hq)) hnp
    · exact hp
  have : Fact (Nat.card (↥(yuHol X₁) ⧸ pCore 2 ↥(yuHol X₁))).Prime := ⟨hprime⟩
  have hYX' : yuHol Y ≤ yuHol X₁ := by
    rcases harr with heq | ⟨-, -, -, -, -, -, -, -, h, -⟩
    · exact heq ▸ le_rfl
    · exact h
  set I := ((yuHol Y).subgroupOf (yuHol X₁)).map (QuotientGroup.mk' (pCore 2 ↥(yuHol X₁))) with hI
  have hItop : I = ⊤ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card I with hbot | htop
    · exfalso
      have hle : (yuHol Y).subgroupOf (yuHol X₁) ≤ pCore 2 ↥(yuHol X₁) := by
        intro z hz
        have h1 : QuotientGroup.mk' (pCore 2 ↥(yuHol X₁)) z ∈ I := ⟨_, hz, rfl⟩
        rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
      have hY2 : IsPGroup 2 ↥(yuHol Y) := by
        have := pCore_isPGroup (p := 2) (G := ↥(yuHol X₁))
        have h2 : IsPGroup 2 ↥((yuHol Y).subgroupOf (yuHol X₁)) := this.to_le hle
        exact IsPGroup.of_surjective h2 (Subgroup.subgroupOfEquivOfLe hYX').toMonoidHom
          (Subgroup.subgroupOfEquivOfLe hYX').surjective
      exact not_isPGroup_two_of_card_three h3
        (IsPGroup.of_surjective hY2 (yuProj Y) (yuProj_surjective Y))
    · exact htop
  have hdec : ∀ x ∈ X₁, ∃ y ∈ Y, ∃ q ∈ oTwoIn X₁, x = y * q := by
    intro x hx
    have hmem : QuotientGroup.mk' (pCore 2 ↥(yuHol X₁)) (yuSec X₁ ⟨x, hx⟩) ∈ I := by
      rw [hItop]
      trivial
    obtain ⟨w, hw, hwz⟩ := hmem
    have hwz' : w⁻¹ * yuSec X₁ ⟨x, hx⟩ ∈ pCore 2 ↥(yuHol X₁) :=
      QuotientGroup.eq.mp hwz
    rw [pCore_yuHol X₁ hV, Subgroup.mem_comap] at hwz'
    have hwY : (w : Hol V) ∈ yuHol Y := hw
    refine ⟨(w : Hol V).right, hwY.2, (((w : Hol V).right)⁻¹ * x), ?_, by group⟩
    refine ⟨⟨((w : Hol V).right)⁻¹ * x, ?_⟩, ?_, rfl⟩
    · exact X₁.mul_mem (X₁.inv_mem (w.2).2) hx
    · have : yuProj X₁ (w⁻¹ * yuSec X₁ ⟨x, hx⟩) =
          ⟨((w : Hol V).right)⁻¹ * x, X₁.mul_mem (X₁.inv_mem (w.2).2) hx⟩ := by
        apply Subtype.ext
        simp [yuProj, yuSec]
      rw [this] at hwz'
      exact hwz'
  have hP : oTwoIn X₁ ≤ oTwoIn H := oTwoIn_le_of_isSubnormal hXH hsubX
  have hcomm : ∀ q ∈ oTwoIn H, ∀ t ∈ Y, q * t = t * q := fun q hq t ht =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQY hq) t
      ht).symm
  have hconj : ∀ q ∈ oTwoIn H, ∀ t ∈ Y, q * t * q⁻¹ = t := fun q hq t ht => by
    rw [hcomm q hq t ht]
    group
  have hnorm : X₁ ≤ Subgroup.normalizer (Y : Set (MulAut V)) := by
    intro x hx
    obtain ⟨y, hy, q, hq, rfl⟩ := hdec x hx
    refine Subgroup.mem_normalizer_iff.mpr fun t => ?_
    have hq' : q ∈ oTwoIn H := hP hq
    have hqi : q⁻¹ ∈ oTwoIn H := (oTwoIn H).inv_mem hq'
    constructor
    · intro ht
      have h1 : y * q * t * (y * q)⁻¹ = y * t * y⁻¹ := by
        calc y * q * t * (y * q)⁻¹ = y * (q * t * q⁻¹) * y⁻¹ := by group
          _ = y * t * y⁻¹ := by rw [hconj q hq' t ht]
      rw [h1]
      exact Y.mul_mem (Y.mul_mem hy ht) (Y.inv_mem hy)
    · intro hmem
      have h1 : q * t * q⁻¹ ∈ Y := by
        have : q * t * q⁻¹ = y⁻¹ * (y * q * t * (y * q)⁻¹) * y := by group
        rw [this]
        exact Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hmem) hy
      have h2 := hconj q⁻¹ hqi (q * t * q⁻¹) h1
      have h3' : q⁻¹ * (q * t * q⁻¹) * q⁻¹⁻¹ = t := by group
      rw [h3'] at h2
      rw [h2]
      exact h1
  have hYN : (Y.subgroupOf X₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hnorm
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans hYX hXH hYN.isSubnormal hsubX

theorem Emb5Pre.core (hV : ∀ v : V, v ^ 2 = 1) (h4 : Emb4All) (hM6 : Omega4OrderThree)
    {G T Y : Subgroup (MulAut V)} (h : Emb5Pre G T Y) (ho2 : pCore 2 ↥G = ⊥) {u : MulAut V}
    (huG : u ∈ G) (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1) {S : Subgroup (MulAut V)} (hS1 : S ≠ ⊥)
    (hS2 : IsPGroup 2 ↥S) (hSH : S ≤ G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)))
    (hYH : Y ≤ G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)) ⊓
      Subgroup.centralizer (S : Set (MulAut V)))
    (hsub : (Y.subgroupOf (G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)) ⊓
      Subgroup.centralizer (S : Set (MulAut V)))).IsSubnormal) :
    (Y.subgroupOf (G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)))).IsSubnormal := by
  set H := G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)) with hH
  have hHG : H ≤ G := inf_le_left
  have hHne : H ≠ G := inf_centralizer_ne_of_pCore_bot ho2 huG hu1 hu2
  have hsm : Smaller H G :=
    Or.inl (lt_of_not_ge fun hge => hHne (Subgroup.eq_of_le_of_card_ge hHG hge))
  have hadm : Adm5 H S Y := ⟨hSH, hS1, hS2, hYH, hsub, h.adm.h3, h.adm.h4⟩
  obtain ⟨X₁, hX₁⟩ := h.ih V hV H hsm (isKGroup_of_le h.kgroup hHG) S Y hadm
  by_cases hYX : Y = X₁
  · rw [hYX]
    exact hX₁.2.2.1
  by_cases hperf : ⁅X₁, X₁⁆ = X₁
  ·
    exfalso
    have hcent := centralizer_zpowers_eq u
    have hadmG : Adm4 G (Subgroup.zpowers u) X₁ :=
      { hTG := Subgroup.zpowers_le.mpr huG
        hT1 := zpowers_ne_bot hu1
        hT2 := isPGroup_zpowers_of_sq hu2
        hYC := by rw [hcent]; exact hX₁.2.1
        hsub := by rw [hcent]; exact hX₁.2.2.1
        hperf := hperf
        hcls := classX4_iff.mpr (Or.inl hX₁.2.2.2.1) }
    obtain ⟨X', hX'⟩ := h4 V hV G h.kgroup _ X₁ hadmG
    exact h.nolift ⟨X', Lift5.trans hV hM6 h.adm.h3 h.adm.h4 (Or.inr hperf) hX₁ hHG hX'⟩
  ·
    have hHN : H ≤ Subgroup.normalizer (oTwoIn H : Set (MulAut V)) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn H)
    have hYH' : Y ≤ H := fun y hy => (hYH hy).1
    have hO : ⁅oTwoIn Y, Y⁆ = ⊥ := by
      rw [oTwoIn_eq_bot_of_card_three h.adm.h3]
      exact Subgroup.commutator_bot_left Y
    have hQY : ⁅oTwoIn H, Y⁆ = ⊥ :=
      commutator_eq_bot_of_centralizer (G₀ := H) (T := S) (Y := Y) (Q := oTwoIn H)
        (noTwoQuotient_of_card_three h.adm.h3) (Or.inr h.adm.h3) hO hS2
        (SixThree.isPGroup_oTwoIn H) (oTwoIn_le H) (hSH.trans hHN) (hYH'.trans hHN) hYH hsub
    exact Lift5.subnormal_of_not_perfect hV h.adm.h3 hX₁ hperf hQY

theorem Emb5Pre.cent (hV : ∀ v : V, v ^ 2 = 1) (h4 : Emb4All) (hM6 : Omega4OrderThree)
    {G T Y : Subgroup (MulAut V)} (h : Emb5Pre G T Y) (ho2 : pCore 2 ↥G = ⊥) :
    ∀ t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)), t ≠ 1 → t ^ 2 = 1 →
      (Y.subgroupOf (G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)))).IsSubnormal :=
  CentHyp.cent ⟨h.adm.hTG, h.adm.hT1, h.adm.hT2, h.adm.hYC, h.adm.hsub, h.sylow,
    fun {_} huG hu1 hu2 {_} hS1 hS2 hSH hYH hsub =>
      h.core hV h4 hM6 ho2 huG hu1 hu2 hS1 hS2 hSH hYH hsub⟩

end Prime

end CFSG.CGT.PushingUpLit.CGT6
