module

public import CFSG.CGT.PushingUpLit.T2KR.FusS
public import CFSG.CGT.PushingUpLit.T2KR.FusBurnside
public import CFSG.LocalAnalysis.SeitzReduction.Endgame
public import CFSG.CGT.PushingUpLit.T2KR.FusInv
public import CFSG.CGT.PushingUpLit.T2KR.GenFourGrp

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall CFSG.CGT.Timmesfeld75
open scoped commutatorElement LinearAlgebra.Projectivization
open MData (QM)

variable {G : Type} [Group G] [Finite G]

structure FusConfig {L M : Subgroup G} {n : ℕ} (H : MData G L M n) (T' : Subgroup G)
    (x ε b g : G) : Prop where
  n_eq : n = 2
  QL : QM L M ⊓ L ≤ blockU L
  Q_eq : ∀ q ∈ QM L M, q ∈ blockU L ∨ x⁻¹ * q ∈ blockU L
  x_Q : x ∈ QM L M
  x_V : x ∉ blockU L
  x_sq : x * x = 1
  ε_L : ε ∈ L
  ε_Q : ε ∉ QM L M
  ε_sq : ε * ε = 1
  b_M : b ∈ M
  b_sq : b * b = 1
  b_LQ : b ∉ L ⊔ QM L M
  εb : ε * b = b * ε
  xb : x * b = b * x
  T'_M : T' ≤ M
  T'_2 : IsPGroup 2 T'
  x_T : x ∈ T'
  ε_T : ε ∈ T'
  b_T : b ∈ T'
  g_ε : g⁻¹ * ε * g ∈ blockU L
  g_b : g⁻¹ * b * g ∈ blockU L

namespace FusConfig

variable {L M : Subgroup G} {n : ℕ} {H : MData G L M n} {T' : Subgroup G} {x ε b g : G}
  (c : FusConfig H T' x ε b g)

include c in
theorem ε_M : ε ∈ M := c.T'_M c.ε_T

include c in
theorem b_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right c.b_sq

include c in
theorem conj_b_mem {y : G} (hy : y ∈ T' ⊓ L) : b * y * b⁻¹ ∈ T' ⊓ L := by
  refine ⟨T'.mul_mem (T'.mul_mem c.b_T hy.1) (T'.inv_mem c.b_T), ?_⟩
  exact (Subgroup.mem_normalizer_iff.1 (H.normal c.b_M) y).1 hy.2

include c in
theorem conj_b_mem' {y : G} (hy : y ∈ T' ⊓ L) : b⁻¹ * y * b ∈ T' ⊓ L := by
  have h := c.conj_b_mem hy
  rw [c.b_inv] at h ⊢
  exact h

noncomputable def S : Subgroup G where
  carrier := {y | y ∈ T' ⊓ L ∨ y * b ∈ T' ⊓ L}
  one_mem' := Or.inl (T' ⊓ L).one_mem
  mul_mem' := by
    rintro y y' (hy | hy) (hy' | hy')
    · exact Or.inl ((T' ⊓ L).mul_mem hy hy')
    · right
      have : y * y' * b = y * (y' * b) := by group
      rw [this]; exact (T' ⊓ L).mul_mem hy hy'
    · right
      have : y * y' * b = (y * b) * (b⁻¹ * y' * b) := by group
      rw [this]
      exact (T' ⊓ L).mul_mem hy (c.conj_b_mem' hy')
    · left
      have e : (y * b) * (b⁻¹ * (y' * b) * b) = y * y' * (b * b) := by group
      have : y * y' = (y * b) * (b⁻¹ * (y' * b) * b) := by rw [e, c.b_sq, mul_one]
      rw [this]
      exact (T' ⊓ L).mul_mem hy (c.conj_b_mem' hy')
  inv_mem' := by
    rintro y (hy | hy)
    · exact Or.inl ((T' ⊓ L).inv_mem hy)
    · right
      have e : y⁻¹ * b = b * (y * b)⁻¹ * b := by group
      rw [e]
      have h := c.conj_b_mem ((T' ⊓ L).inv_mem hy)
      rw [c.b_inv] at h
      exact h

include c in
theorem mem_S_iff {y : G} : y ∈ c.S ↔ y ∈ T' ⊓ L ∨ y * b ∈ T' ⊓ L := Iff.rfl

include c in
theorem b_χ : H.chi ⟨b, c.b_M⟩ ≠ 1 :=
  H.chi_ne_one_of_not_mem (x := ⟨b, c.b_M⟩) (Subtype.ext c.b_sq) c.b_LQ

include c in
theorem exists_conj_into_V {y : G} (hy : y ∈ c.S) (hy2 : y * y = 1) :
    ∃ h : G, h⁻¹ * y * h ∈ blockU L := by
  have finish : ∀ β v : G, β ∈ M → β * β = 1 → β ∉ QM L M → v ∈ blockU L →
      g⁻¹ * β * g ∈ blockU L → y = β * v → ∃ h : G, h⁻¹ * y * h ∈ blockU L := by
    intro β v hβM hβ2 hβQ hv hβg hyβ
    have h2 : (β * v) ^ 2 = 1 := by rw [← hyβ, pow_two]; exact hy2
    obtain ⟨s, hs, hsβ⟩ := H.exists_conj_of_involution_mem_coset hβM hβ2 hβQ hv h2
    refine ⟨s⁻¹ * g, ?_⟩
    have : y = s⁻¹ * β * s := by rw [hyβ, hsβ]
    have e : (s⁻¹ * g)⁻¹ * y * (s⁻¹ * g) = g⁻¹ * β * g := by rw [this]; group
    rw [e]; exact hβg
  rcases (c.mem_S_iff).1 hy with hyL | hyb
  · by_cases hyV : y ∈ blockU L
    · exact ⟨1, by simpa using hyV⟩
    · obtain ⟨c₀, hc₀L, hyc⟩ := H.exists_conj_of_involution_in_L c.QL c.ε_L c.ε_sq c.ε_M
        c.ε_Q hyL.2 hy2 hyV
      refine ⟨c₀⁻¹ * g, ?_⟩
      have : (c₀⁻¹ * g)⁻¹ * y * (c₀⁻¹ * g) = g⁻¹ * ε * g := by rw [hyc]; group
      rw [this]; exact c.g_ε
  ·
    set l := y * b with hl
    have hlT : l ∈ T' := hyb.1
    have hlL : l ∈ L := hyb.2
    have hlM : l ∈ M := H.le hlL
    set N : Subgroup G := T' ⊓ (L ⊔ QM L M) with hN
    have hNLQ : N ≤ L ⊔ QM L M := inf_le_right
    have hN2 : IsPGroup 2 N := c.T'_2.to_le inf_le_left
    have hlN : l ∈ N := ⟨hlT, (le_sup_left : L ≤ L ⊔ QM L M) hlL⟩
    have hεN : ε ∈ N := ⟨c.ε_T, (le_sup_left : L ≤ L ⊔ QM L M) c.ε_L⟩
    have hbinv : b⁻¹ = b := c.b_inv
    have hyl : y = l * b := by
      rw [hl, mul_assoc, c.b_sq, mul_one]
    have hblb : b * l * b⁻¹ = l⁻¹ := by
      have h1 : l * b * (l * b) = 1 := by rw [← hyl]; exact hy2
      calc b * l * b⁻¹ = b * l * b := by rw [hbinv]
        _ = l⁻¹ * (l * b * (l * b)) := by group
        _ = l⁻¹ := by rw [h1, mul_one]
    obtain ⟨p, hp⟩ := H.exists_root_point_of_isPGroup N hNLQ hN2
    have hρl : H.rho ⟨l, hNLQ hlN⟩ ∈ rootGrp p := hp ⟨⟨l, hlN⟩, rfl⟩
    have hρl2 := mul_self_eq_one_of_mem_rootGrp hρl
    have hαl : H.actHom ⟨l, hlM⟩ * H.actHom ⟨l, hlM⟩ = 1 := by
      have e : H.actHom ⟨l, hlM⟩ = slPerm (Fq n) (H.rho ⟨l, hNLQ hlN⟩) :=
        (H.slPerm_rho ⟨l, hNLQ hlN⟩).symm
      rw [e, ← map_mul, hρl2, map_one]
    have hlb : H.actHom ⟨b, c.b_M⟩ * H.actHom ⟨l, hlM⟩ =
        H.actHom ⟨l, hlM⟩ * H.actHom ⟨b, c.b_M⟩ := by
      have e : (⟨b, c.b_M⟩ * ⟨l, hlM⟩ * ⟨b, c.b_M⟩⁻¹ : ↥M) = ⟨l⁻¹, M.inv_mem hlM⟩ :=
        Subtype.ext hblb
      have h1 := congrArg H.actHom e
      rw [map_mul, map_mul, map_inv] at h1
      have h2 : (H.actHom ⟨l⁻¹, M.inv_mem hlM⟩) = (H.actHom ⟨l, hlM⟩)⁻¹ := by
        have : (⟨l⁻¹, M.inv_mem hlM⟩ : ↥M) = ⟨l, hlM⟩⁻¹ := rfl
        rw [this, map_inv]
      rw [h2] at h1
      have h3 : (H.actHom ⟨l, hlM⟩)⁻¹ = H.actHom ⟨l, hlM⟩ := inv_eq_of_mul_eq_one_right hαl
      rw [h3] at h1
      calc H.actHom ⟨b, c.b_M⟩ * H.actHom ⟨l, hlM⟩
          = (H.actHom ⟨b, c.b_M⟩ * H.actHom ⟨l, hlM⟩ * (H.actHom ⟨b, c.b_M⟩)⁻¹) *
            H.actHom ⟨b, c.b_M⟩ := by group
        _ = H.actHom ⟨l, hlM⟩ * H.actHom ⟨b, c.b_M⟩ := by rw [h1]
    have key := H.rho_mem_of_commute c.n_eq hNLQ hN2 c.b_M c.b_χ hεN c.ε_Q c.εb hlN hlM hlb
    have hbQ : b ∉ QM L M := fun h => c.b_LQ ((le_sup_right : QM L M ≤ L ⊔ QM L M) h)
    have hconjV : ∀ v ∈ blockU L, b⁻¹ * v * b ∈ blockU L := by
      intro v hv
      have := conj_mem_blockU (H.normal (M.inv_mem c.b_M)) hv
      simpa using this
    rcases key with hlQ | hεlQ
    · have hlV : l ∈ blockU L := c.QL ⟨hlQ, hlL⟩
      refine finish b (b⁻¹ * l * b) c.b_M c.b_sq hbQ (hconjV l hlV) c.g_b ?_
      rw [hyl]; group
    · have hvV : ε⁻¹ * l ∈ blockU L := c.QL ⟨hεlQ, L.mul_mem (L.inv_mem c.ε_L) hlL⟩
      have hεb2 : (ε * b) * (ε * b) = 1 := by
        calc (ε * b) * (ε * b) = ε * (b * ε) * b := by group
          _ = ε * (ε * b) * b := by rw [c.εb]
          _ = (ε * ε) * (b * b) := by group
          _ = 1 := by rw [c.ε_sq, c.b_sq, mul_one]
      have hεbQ : ε * b ∉ QM L M := by
        intro h
        apply c.b_LQ
        have : b = ε⁻¹ * (ε * b) := by group
        rw [this]
        exact Subgroup.mul_mem _ ((le_sup_left : L ≤ L ⊔ QM L M) (L.inv_mem c.ε_L))
          ((le_sup_right : QM L M ≤ L ⊔ QM L M) h)
      have hgεb : g⁻¹ * (ε * b) * g ∈ blockU L := by
        have : g⁻¹ * (ε * b) * g = (g⁻¹ * ε * g) * (g⁻¹ * b * g) := by group
        rw [this]; exact Subgroup.mul_mem _ c.g_ε c.g_b
      refine finish (ε * b) (b⁻¹ * (ε⁻¹ * l) * b) (M.mul_mem c.ε_M c.b_M) hεb2 hεbQ
        (hconjV _ hvV) hgεb ?_
      rw [hyl]; group

include c in
theorem x_not_mem_S : x ∉ c.S := by
  intro hx
  rcases (c.mem_S_iff).1 hx with h | h
  · exact c.x_V (c.QL ⟨c.x_Q, h.2⟩)
  · apply c.b_LQ
    have hxLQ : x ∈ L ⊔ QM L M := (le_sup_right : QM L M ≤ L ⊔ QM L M) c.x_Q
    have hxbLQ : x * b ∈ L ⊔ QM L M := (le_sup_left : L ≤ L ⊔ QM L M) h.2
    have : b = x⁻¹ * (x * b) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxLQ) hxbLQ

include c in
theorem x_mem_normalizer_S : x ∈ Subgroup.normalizer (c.S : Set G) := by
  have hxM : x ∈ M := c.T'_M c.x_T
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right c.x_sq
  have key : ∀ y ∈ c.S, x * y * x⁻¹ ∈ c.S := by
    intro y hy
    rcases (c.mem_S_iff).1 hy with h | h
    · left
      exact ⟨T'.mul_mem (T'.mul_mem c.x_T h.1) (T'.inv_mem c.x_T),
        (Subgroup.mem_normalizer_iff.1 (H.normal hxM) y).1 h.2⟩
    · right
      have e : (x * y * x⁻¹) * b = x * (y * b) * x⁻¹ := by
        have hxb' : x⁻¹ * b = b * x⁻¹ := by
          rw [hxinv]; exact c.xb
        calc (x * y * x⁻¹) * b = x * y * (x⁻¹ * b) := by group
          _ = x * y * (b * x⁻¹) := by rw [hxb']
          _ = x * (y * b) * x⁻¹ := by group
      rw [e]
      exact ⟨T'.mul_mem (T'.mul_mem c.x_T h.1) (T'.inv_mem c.x_T),
        (Subgroup.mem_normalizer_iff.1 (H.normal hxM) (y * b)).1 h.2⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key y hy, fun hy => ?_⟩
  have := key _ hy
  have e : x * (x * y * x⁻¹) * x⁻¹ = y := by
    calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x⁻¹ * x⁻¹) := by group
      _ = y := by rw [c.x_sq, hxinv, c.x_sq]; group
  rwa [e] at this

include c in
theorem T'_le_S_sup : T' ≤ c.S ⊔ Subgroup.zpowers x := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right c.x_sq
  set N : Subgroup G := T' ⊓ (L ⊔ QM L M) with hN
  have hbS : b ∈ c.S := by
    right
    refine ⟨T'.mul_mem c.b_T c.b_T, ?_⟩
    rw [c.b_sq]; exact L.one_mem
  have claim : ∀ u ∈ N, u ∈ c.S ∨ u * x ∈ c.S := by
    rintro u ⟨huT, huLQ⟩
    obtain ⟨l, hl, q, hq, rfl⟩ := H.mem_LQ_iff.1 huLQ
    rcases c.Q_eq q hq with hqV | hxqV
    · left
      exact Or.inl ⟨huT, L.mul_mem hl (CFSG.CGT.PushingUpLit.blockU_le L hqV)⟩
    · right
      left
      refine ⟨T'.mul_mem huT c.x_T, ?_⟩
      have hv := CFSG.CGT.PushingUpLit.blockU_le L hxqV
      have hcomm : x * (x⁻¹ * q) = (x⁻¹ * q) * x :=
        H.Q_comm x c.x_Q _ (H.blockU_le_QM hxqV)
      have e : l * q * x = l * (x⁻¹ * q) := by
        have hq' : q = x * (x⁻¹ * q) := by group
        calc l * q * x = l * (x * (x⁻¹ * q)) * x := by rw [← hq']
          _ = l * ((x⁻¹ * q) * x) * x := by rw [hcomm]
          _ = l * (x⁻¹ * q) * (x * x) := by group
          _ = l * (x⁻¹ * q) := by rw [c.x_sq, mul_one]
      rw [e]
      exact L.mul_mem hl hv
  have hmem : ∀ u ∈ N, u ∈ c.S ⊔ Subgroup.zpowers x := by
    intro u hu
    rcases claim u hu with h | h
    · exact (le_sup_left : c.S ≤ c.S ⊔ Subgroup.zpowers x) h
    · have : u = (u * x) * x⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ ((le_sup_left : c.S ≤ c.S ⊔ Subgroup.zpowers x) h)
        ((le_sup_right : Subgroup.zpowers x ≤ c.S ⊔ Subgroup.zpowers x)
          (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)))
  intro t ht
  by_cases htN : t ∈ N
  · exact hmem t htN
  · have hbN : b ∉ N := fun h => c.b_LQ h.2
    have hidx : N.relIndex T' = 2 := by
      have h1 : N.relIndex T' ≤ 2 := by
        have := H.relIndex_le_card_aut c.T'_M c.T'_2
        rw [c.n_eq] at this
        exact this
      have hne : N.relIndex T' ≠ 1 := fun h => hbN (Subgroup.relIndex_eq_one.1 h c.b_T)
      have hpos := relIndex_pos_of_finite N T'
      omega
    have hbt : b⁻¹ * t ∈ N := inv_mul_mem_of_relIndex_two hidx c.b_T ht hbN htN
    have hu := hmem _ hbt
    have : t = b * (b⁻¹ * t) := by group
    rw [this]
    exact Subgroup.mul_mem _ ((le_sup_left : c.S ≤ c.S ⊔ Subgroup.zpowers x) hbS) hu

end FusConfig

theorem fusion_false {L M T : Subgroup G} {n : ℕ} (hs : Sec6 G L M T n) {H : MData G L M n}
    [IsSimpleGroup G] (hG2 : 2 < Nat.card G) {T' : Subgroup G} {x ε b g : G}
    (hT'syl : CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤) (c : FusConfig H T' x ε b g) : False := by
  have hburn : ∀ h : G, h * x * h⁻¹ ∉ blockU L :=
    not_conj_mem_of_not_mem hs (W := blockU L) H.blockU_le_QM
      (fun m hm w hw => conj_mem_blockU (H.normal hm) hw) c.x_Q c.x_V
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hidx⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).1 hT'syl
  rw [Subgroup.relIndex_top_right] at hidx
  let T₀ : Sylow 2 G := c.T'_2.toSylow hidx
  have hT₀ : (T₀ : Subgroup G) ≤ c.S ⊔ Subgroup.zpowers x := by
    have : (T₀ : Subgroup G) = T' := rfl
    rw [this]
    exact c.T'_le_S_sup
  refine CFSG.SeitzReduction.false_of_simple_of_not_fused_of_sylow_le hG2 (Y := c.S) (t := x) ?_
    c.x_mem_normalizer_S c.x_not_mem_S ⟨T₀, hT₀⟩ ?_
  · refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]; exact c.x_sq
    · intro h1
      exact c.x_V (h1 ▸ (blockU L).one_mem)
  · intro h hfus
    have hy2 : (h⁻¹ * x * h) * (h⁻¹ * x * h) = 1 := by
      calc (h⁻¹ * x * h) * (h⁻¹ * x * h) = h⁻¹ * (x * x) * h := by group
        _ = 1 := by rw [c.x_sq]; group
    obtain ⟨h', hh'⟩ := c.exists_conj_into_V hfus hy2
    apply hburn ((h * h')⁻¹)
    have : (h * h')⁻¹ * x * ((h * h')⁻¹)⁻¹ = h'⁻¹ * (h⁻¹ * x * h) * h' := by group
    rw [this]
    exact hh'

end CFSG.CGT.PushingUpLit.T2KR
