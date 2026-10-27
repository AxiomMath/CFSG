module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterMuOneWeight

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem muOne_exists_sq_comm_eq (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {w : G} (hwT : w ∈ T)
    (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t) {z : G} (hz : z ∈ szA₁ (szT₁ L T)) :
    ∃ y ∈ szT₁ L T, (y⁻¹ * (w * y * w⁻¹)) ^ 2 = z := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hT₁card, hA₁card, hA₁comm, hsqT, hinvT, -, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨W, -, hAW, hWcard, hWab, -, -, hWiff⟩ := h.exists_W_of_card_sylow hS2 hwT hw2 hwS
  have hww : w * w = 1 := by rw [← sq, hw2]
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hwN : ∀ y ∈ szT₁ L T, w * y * w⁻¹ ∈ szT₁ L T := fun y hy =>
    (mem_normalizer_iff.mp (hTN₁ hwT) y).mp hy
  have hδT : ∀ y ∈ szT₁ L T, y⁻¹ * (w * y * w⁻¹) ∈ szT₁ L T := fun y hy =>
    mul_mem (inv_mem hy) (hwN y hy)
  have hδW : ∀ y ∈ szT₁ L T, y⁻¹ * (w * y * w⁻¹) ∈ W := by
    intro y hy
    refine (hWiff _ (hδT y hy)).mp ?_
    have e1 : w * (y⁻¹ * (w * y * w⁻¹)) * w⁻¹ = w * y⁻¹ * w * y := by
      calc w * (y⁻¹ * (w * y * w⁻¹)) * w⁻¹ = w * y⁻¹ * w * y * (w * w)⁻¹ := by group
        _ = w * y⁻¹ * w * y := by rw [hww, inv_one, mul_one]
    have e2 : (y⁻¹ * (w * y * w⁻¹))⁻¹ = w * y⁻¹ * w * y := by
      calc (y⁻¹ * (w * y * w⁻¹))⁻¹ = w * y⁻¹ * w⁻¹ * y := by group
        _ = w * y⁻¹ * w * y := by rw [hwinv]
    rw [e1, ← e2, ← mul_inv_rev, ← sq]
    exact inv_mem (hsqT _ (hδT y hy))
  have hcomm : ∀ a ∈ szT₁ L T, ∀ b ∈ szT₁ L T, a * b * a⁻¹ * b⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro a ha b hb
    rw [hA₁comm]
    have := commutator_mem_commutator ha hb
    rwa [commutatorElement_def] at this
  have hψmul : ∀ a ∈ szT₁ L T, ∀ b ∈ szT₁ L T,
      ((a * b)⁻¹ * (w * (a * b) * w⁻¹)) ^ 2 =
        (a⁻¹ * (w * a * w⁻¹)) ^ 2 * (b⁻¹ * (w * b * w⁻¹)) ^ 2 := by
    intro a ha b hb
    set δa := a⁻¹ * (w * a * w⁻¹) with hδa
    set δb := b⁻¹ * (w * b * w⁻¹) with hδb
    have e : (a * b)⁻¹ * (w * (a * b) * w⁻¹) = (b⁻¹ * δa * b) * δb := by
      rw [hδa, hδb]; group
    have hcA : δa⁻¹ * b⁻¹ * δa⁻¹⁻¹ * b⁻¹⁻¹ ∈ szA₁ (szT₁ L T) :=
      hcomm _ (inv_mem (hδT a ha)) _ (inv_mem hb)
    have hbW : b⁻¹ * δa * b ∈ W := by
      rw [show b⁻¹ * δa * b = δa * (δa⁻¹ * b⁻¹ * δa⁻¹⁻¹ * b⁻¹⁻¹) by group]
      exact mul_mem (hδW a ha) (hAW hcA)
    have hsq : (b⁻¹ * δa * b) ^ 2 = δa ^ 2 := by
      have hc := mem_centralizer_iff.mp (mem_szA₁.mp (hsqT _ (hδT a ha))).2 _ (inv_mem hb)
      calc (b⁻¹ * δa * b) ^ 2 = b⁻¹ * δa ^ 2 * b := by rw [sq, sq]; group
        _ = δa ^ 2 := by rw [hc, inv_mul_cancel_right]
    rw [e, (Commute.mul_pow (hWab _ hbW _ (hδW b hb)) 2), hsq]
  let ψ : szT₁ L T →* szA₁ (szT₁ L T) :=
    { toFun := fun y => ⟨((y : G)⁻¹ * (w * y * w⁻¹)) ^ 2, hsqT _ (hδT y y.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (hψmul a a.2 b b.2) }
  have hker : Nat.card ψ.ker ≤ (2 ^ f) ^ 2 := by
    rw [← hWcard]
    refine Nat.card_le_card_of_injective (fun a : ψ.ker => (⟨((a : szT₁ L T) : G), ?_⟩ : W)) ?_
    · have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp a.2)
      change (((a : szT₁ L T) : G)⁻¹ * (w * (a : szT₁ L T) * w⁻¹)) ^ 2 = 1 at h1
      exact (hWiff _ (a : szT₁ L T).2).mp (hinvT _ (hδT _ (a : szT₁ L T).2) h1)
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : W => (x : G)) hab))
  have hrange : ψ.range = ⊤ := by
    refine Subgroup.eq_top_of_le_card _ ?_
    have h1 := card_mul_index ψ.ker
    rw [Subgroup.index_ker, hT₁card] at h1
    rw [hA₁card]
    have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
    by_contra hlt
    push Not at hlt
    have h3 : Nat.card ψ.ker * Nat.card ψ.range < (2 ^ f) ^ 2 * 2 ^ f :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hker)
        (Nat.mul_lt_mul_of_pos_left hlt (pow_pos hq0 2))
    rw [h1, show (2 ^ f) ^ 2 * 2 ^ f = (2 ^ f) ^ 3 by ring] at h3
    exact lt_irrefl _ h3
  have hzr : (⟨z, hz⟩ : szA₁ (szT₁ L T)) ∈ ψ.range := by rw [hrange]; exact mem_top _
  obtain ⟨y, hy⟩ := hzr
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

end U3Start

namespace U3C1OuterLevelData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G}

section Core

variable (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1)
  (hL : U3C1OuterLevelData G L f t T D V U U₁ 1)
include hS hL

theorem muOne_sup_le_normalizer : U ⊔ T ≤ normalizer (U₁ : Set G) :=
  sup_le hL.U₁_normal hL.T_le

theorem muOne_comm_mem_U₁ : ∀ a ∈ U ⊔ T, ∀ b ∈ U ⊔ T, a * b * a⁻¹ * b⁻¹ ∈ U₁ := by
  have hcommT := hS.start.commutator_le_szT₁_of_card_sylow hS.card_sylow
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hTU₁ : ∀ s ∈ T, ∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁ := fun s hs u hu =>
    (mem_normalizer_iff.mp (hL.T_le hs) u).mp hu
  refine SzC1.comm_mem_of_generators_normal (P := fun g => g ∈ U₁ ∨ g ∈ T) (fun S hSS => ?_)
    (fun g hg => hg.elim (fun hg => mem_sup_left (hL.U₁_le hg)) (fun hg => mem_sup_right hg))
    (fun y hy b hb => (mem_normalizer_iff.mp (hL.muOne_sup_le_normalizer hS hy) b).mp hb) ?_
  · have htT := (hS.start.start_of_card_sylow hS.card_sylow).1
    refine sup_le ?_ (fun s hs => hSS s (Or.inr hs))
    rw [← hL.sup_eq]
    exact sup_le (fun u hu => hSS u (Or.inl hu)) (zpowers_le.mpr (hSS t (Or.inr htT)))
  · rintro g (hg | hg) g' (hg' | hg')
    · exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')
    · rw [show g * g' * g⁻¹ * g'⁻¹ = g * (g' * g⁻¹ * g'⁻¹) by group]
      exact mul_mem hg (hTU₁ g' hg' _ (inv_mem hg))
    · exact mul_mem (hTU₁ g hg g' hg') (inv_mem hg')
    · have := hcommT (commutator_mem_commutator hg hg')
      rw [commutatorElement_def] at this
      exact hT₁U₁ this

theorem muOne_card_U₁ : Nat.card U₁ = (2 ^ f) ^ 5 := by
  have h2 := RankOne.Endings.relIndex_sup_zpowers_eq_two hL.t_not_mem (hL.U₁_normal hL.t_mem_U)
    (hL.muOne_t_mul_self hS)
  rw [hL.sup_eq] at h2
  have h3 := relIndex_mul_card (H := U₁) (K := U)
  rw [h2, inf_of_le_left hL.U₁_le, hL.card_U, show (1 + 4 : ℕ) = 5 from rfl] at h3
  omega

theorem muOne_mem_T₁_of_mem_T {u : G} (hu : u ∈ U₁) (huT : u ∈ T) : u ∈ szT₁ L T := by
  have hut : u ∈ U ⊓ centralizer ({t} : Set G) := mem_inf.mpr ⟨hL.U₁_le hu, hS.start.le huT⟩
  rw [hL.inf_centralizer] at hut
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers hS.start.mem_centralizer_szT₁ hut
  rcases mem_zpowers_involution_eq_one_or_eq hS.start.sq_eq_one hz with rfl | rfl
  · rw [← hyz, mul_one]
    exact hy
  · exfalso
    apply hL.t_not_mem
    rw [show z = y⁻¹ * u by rw [← hyz]; group]
    exact mul_mem (inv_mem ((le_sup_left.trans hL.sup_le_U₁) hy)) hu

theorem muOne_sup_eq : U ⊔ T = T ⊔ U₁ := by
  have htT := (hS.start.start_of_card_sylow hS.card_sylow).1
  refine le_antisymm (sup_le ?_ le_sup_left) (sup_le le_sup_right (hL.U₁_le.trans le_sup_left))
  rw [← hL.sup_eq]
  exact sup_le le_sup_right (zpowers_le.mpr (mem_sup_left htT))

theorem muOne_classify {x : G} (hx : x ∈ U ⊔ T) (hx2 : x * x = 1) :
    x ∈ U₁ ∨ x * t⁻¹ ∈ U₁ ∨
      ∃ w ∈ T, w ^ 2 = 1 ∧ w ∉ szT₁ L T ⊔ zpowers t ∧ x * w⁻¹ ∈ U₁ := by
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hTU₁ : ∀ s ∈ T, ∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁ := fun s hs u hu =>
    (mem_normalizer_iff.mp (hL.T_le hs) u).mp hu
  have htC := hS.start.mem_centralizer_szT₁
  rw [hL.muOne_sup_eq hS] at hx
  obtain ⟨s, hs, u, hu, rfl⟩ := ncyc_exists_mul_of_mem_sup hL.T_le hx
  have hs2U : s ^ 2 ∈ U₁ := by
    have e : s ^ 2 = (s⁻¹ * u * s * u)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      calc s ^ 2 * (s⁻¹ * u * s * u) = s * u * (s * u) := by rw [sq]; group
        _ = 1 := hx2
    rw [e]
    refine inv_mem (mul_mem ?_ hu)
    have := hTU₁ _ (inv_mem hs) u hu
    rwa [inv_inv] at this
  have hs2 : s ^ 2 ∈ szT₁ L T ⊔ zpowers t :=
    mem_sup_left (hL.muOne_mem_T₁_of_mem_T hS hs2U (pow_mem hs 2))
  by_cases hsH : s ∈ szT₁ L T ⊔ zpowers t
  · obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers htC hsH
    rcases mem_zpowers_involution_eq_one_or_eq hS.start.sq_eq_one hz with rfl | rfl
    · left
      rw [← hyz, mul_one]
      exact mul_mem (hT₁U₁ hy) hu
    · right; left
      rw [← hyz, show y * z * u * z⁻¹ = y * (z * u * z⁻¹) by group]
      exact mul_mem (hT₁U₁ hy) (hTU₁ z (hS.start.start_of_card_sylow hS.card_sylow).1 u hu)
  · right; right
    obtain ⟨v₀, hv₀T, hv₀2, hv₀S⟩ := hS.outer
    have h1 := hS.start.mul_inv_mem_of_sq_mem_of_card_sylow hS.card_sylow hs hv₀T hs2
      (by rw [hv₀2]; exact one_mem _) hsH hv₀S
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers htC h1
    have hsyz : s = y * z * v₀ := by rw [hyz]; group
    have htT := (hS.start.start_of_card_sylow hS.card_sylow).1
    have hzT : z ∈ T := zpowers_le.mpr htT hz
    have hzv : z * v₀ = v₀ * z := by
      rcases mem_zpowers_involution_eq_one_or_eq hS.start.sq_eq_one hz with rfl | rfl
      · group
      · exact (mem_centralizer_singleton_iff.mp (hS.start.le hv₀T)).symm
    have hz2 : z ^ 2 = 1 := by
      rcases mem_zpowers_involution_eq_one_or_eq hS.start.sq_eq_one hz with rfl | rfl
      · exact one_pow 2
      · exact hS.start.sq_eq_one
    refine ⟨z * v₀, mul_mem hzT hv₀T, ?_, fun hzvS => hv₀S ?_, ?_⟩
    · rw [(Commute.mul_pow hzv 2), hz2, hv₀2, mul_one]
    · rw [show v₀ = z⁻¹ * (z * v₀) by group]
      exact mul_mem (inv_mem (mem_sup_right hz)) hzvS
    · rw [hsyz, show y * z * v₀ * u * (z * v₀)⁻¹ = y * ((z * v₀) * u * (z * v₀)⁻¹) by group]
      exact mul_mem (hT₁U₁ hy) (hTU₁ _ (mul_mem hzT hv₀T) u hu)

section Coords

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {v : G → K} {μ : K}
  (hc : U3A₁Coords (szA₁ (szT₁ L T)) d v μ)
include hc

theorem muOne_comm_mem_szA₁ (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hK : Fintype.card K = 2 ^ f) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) :
    ∀ x ∈ U₁, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) := by
  intro x hx y hy
  have hx2 := hL.muOne_sq_mem_szA₁ hS hc hμV hK hμ hx
  have hy2 := hL.muOne_sq_mem_szA₁ hS hc hμV hK hμ hy
  have hxy2 := hL.muOne_sq_mem_szA₁ hS hc hμV hK hμ (mul_mem hx hy)
  rw [show x * y * x⁻¹ * y⁻¹ = (x * y) ^ 2 * (y⁻¹ * (x ^ 2)⁻¹ * y⁻¹⁻¹) * (y ^ 2)⁻¹ by
    rw [sq, sq, sq]; group]
  refine mul_mem (mul_mem hxy2 ?_) (inv_mem hy2)
  rw [hL.muOne_conj_szA₁ hS (inv_mem hy) (inv_mem hx2)]
  exact inv_mem hx2

theorem muOne_false_of_conj_mem_U₁ (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hK : Fintype.card K = 2 ^ f) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {g : G}
    (hgT : ∀ s ∈ T, g * s * g⁻¹ ∈ U ⊔ T) (hx : g * t * g⁻¹ ∈ U₁) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨htT, -, -, -, -, hMn, -⟩ := hS.start.start_of_card_sylow hS.card_sylow
  obtain ⟨hT₁card, hA₁card, -, -, -, -, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  obtain ⟨v₀, hv₀T, hv₀2, hv₀S⟩ := hS.outer
  obtain ⟨W, -, -, hWcard, -, -, -, hWiff⟩ :=
    hS.start.exists_W_of_card_sylow hS.card_sylow hv₀T hv₀2 hv₀S
  have hcomm := hL.muOne_comm_mem_U₁ hS
  have hcommA := hL.muOne_comm_mem_szA₁ hS hc hμV hK hμ
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hS.start.two_le
  set x := g * t * g⁻¹ with hxdef
  set C := (centralizer ({x} : Set G)).subgroupOf U₁ with hCdef
  have hbound := card_le_card_centralizer_mul_card_of_comm_mem (H := U₁)
    (A := szA₁ (szT₁ L T)) (x := x) fun w hw => hcommA w hw x hx
  rw [hL.muOne_card_U₁ hS, hA₁card] at hbound
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  have hCcard : (2 ^ f) ^ 4 ≤ Nat.card C := by
    have h2 : (2 ^ f) ^ 4 * 2 ^ f ≤ Nat.card C * 2 ^ f := by rw [← pow_succ]; exact hbound
    exact Nat.le_of_mul_le_mul_right h2 hq0
  set P : Subgroup G := C.map U₁.subtype with hPdef
  set N : Subgroup G := P.map (MulAut.conj g⁻¹).toMonoidHom with hNdef
  have hNcard : Nat.card N = Nat.card C := by
    rw [hNdef, card_map_of_injective (MulAut.conj g⁻¹).injective, hPdef,
      card_map_of_injective U₁.subtype_injective]
  have hNmem : ∀ n ∈ N, g * n * g⁻¹ ∈ U₁ ∧ g * n * g⁻¹ * x = x * (g * n * g⁻¹) := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw' := mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp hw)
    have e : g * ((MulAut.conj g⁻¹).toMonoidHom (U₁.subtype w)) * g⁻¹ = (w : G) := by
      simp; group
    rw [e]
    exact ⟨w.2, hw'⟩
  have hTsyl : IsSylowOf 2 T (centralizer ({t} : Set G)) := by
    obtain ⟨P₀, hP₀⟩ := hS.start.sylow
    exact ⟨P₀, by rw [hP₀, subgroupOf_map_subtype, inf_eq_left.mpr hS.start.le]⟩
  set Q : Subgroup G := (U ⊔ T).map (MulAut.conj g⁻¹).toMonoidHom with hQdef
  have hQ2 : IsPGroup 2 Q := hL.isSylowOf.isPGroup.map _
  have hmemQ : ∀ y : G, g * y * g⁻¹ ∈ U ⊔ T → y ∈ Q := fun y hy =>
    ⟨g * y * g⁻¹, hy, by simp; group⟩
  have hNT : N ≤ T := by
    intro n hn
    obtain ⟨hnU, hnx⟩ := hNmem n hn
    have hnt : n * t = t * n := by
      have e1 : g * (n * t) * g⁻¹ = g * (t * n) * g⁻¹ := by
        calc g * (n * t) * g⁻¹ = (g * n * g⁻¹) * x := by rw [hxdef]; group
          _ = x * (g * n * g⁻¹) := hnx
          _ = g * (t * n) * g⁻¹ := by rw [hxdef]; group
      simpa using e1
    have hH : T ⊔ zpowers n ≤ centralizer ({t} : Set G) :=
      sup_le hS.start.le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hnt))
    have hHQ : T ⊔ zpowers n ≤ Q :=
      sup_le (fun s hs => hmemQ s (hgT s hs))
        (zpowers_le.mpr (hmemQ n (mem_sup_left (hL.U₁_le hnU))))
    have heq := hTsyl.eq_of_le le_sup_left hH (hQ2.to_le hHQ)
    rw [← heq]
    exact mem_sup_right (mem_zpowers n)
  have hgA' : ∀ z ∈ szA₁ (szT₁ L T), g * z * g⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hS.start.muOne_exists_sq_comm_eq hS.card_sylow hv₀T hv₀2 hv₀S hz
    have hyT : y ∈ T := szT₁_le_left L T hy
    have hc1 : g * (y⁻¹ * (v₀ * y * v₀⁻¹)) * g⁻¹ ∈ U₁ := by
      have := hcomm _ (hgT _ (inv_mem hyT)) _ (hgT _ hv₀T)
      rw [show g * y⁻¹ * g⁻¹ * (g * v₀ * g⁻¹) * (g * y⁻¹ * g⁻¹)⁻¹ * (g * v₀ * g⁻¹)⁻¹ =
        g * (y⁻¹ * (v₀ * y * v₀⁻¹)) * g⁻¹ by group] at this
      exact this
    have h2 := hL.muOne_sq_mem_szA₁ hS hc hμV hK hμ hc1
    rwa [conj_pow, hyz] at h2
  have hgA : ∀ z ∈ szA₁ (szT₁ L T), g⁻¹ * z * g ∈ szA₁ (szT₁ L T) := by
    intro z hz
    have hinj : Function.Injective (fun a : szA₁ (szT₁ L T) =>
        (⟨g * a * g⁻¹, hgA' a a.2⟩ : szA₁ (szT₁ L T))) := by
      intro a b hab
      have e := congrArg Subtype.val hab
      exact Subtype.ext (by simpa using e)
    obtain ⟨a, ha⟩ := Finite.injective_iff_surjective.mp hinj ⟨z, hz⟩
    have e := congrArg Subtype.val ha
    simp only at e
    rw [← e, show g⁻¹ * (g * (a : G) * g⁻¹) * g = a by group]
    exact a.2
  have hNsq : ∀ n ∈ N, n ^ 2 ∈ szA₁ (szT₁ L T) := by
    intro n hn
    have h1 := hL.muOne_sq_mem_szA₁ hS hc hμV hK hμ (hNmem n hn).1
    rw [conj_pow] at h1
    have h2 := hgA _ h1
    rwa [show g⁻¹ * (g * n ^ 2 * g⁻¹) * g = n ^ 2 by group] at h2
  have hNcomm : ∀ n ∈ N, ∀ n' ∈ N, n * n' * n⁻¹ * n'⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro n hn n' hn'
    have h1 := hcommA _ (hNmem n hn).1 _ (hNmem n' hn').1
    rw [show g * n * g⁻¹ * (g * n' * g⁻¹) * (g * n * g⁻¹)⁻¹ * (g * n' * g⁻¹)⁻¹ =
      g * (n * n' * n⁻¹ * n'⁻¹) * g⁻¹ by group] at h1
    have h2 := hgA _ h1
    rwa [show g⁻¹ * (g * (n * n' * n⁻¹ * n'⁻¹) * g⁻¹) * g = n * n' * n⁻¹ * n'⁻¹ by group] at h2
  set H := szT₁ L T ⊔ zpowers t with hHdef
  have hHT : H ≤ T := sup_le (szT₁_le_left L T) (zpowers_le.mpr htT)
  have hv₀N : v₀ ∈ normalizer (H : Set G) := by
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun m hm => ?_
    have := hMn.conj_mem ⟨m, hHT hm⟩ (mem_subgroupOf.mpr hm) ⟨v₀⁻¹, inv_mem hv₀T⟩
    simpa using mem_subgroupOf.mp this
  have hv₀v₀ : v₀ * v₀ = 1 := by rw [← sq, hv₀2]
  have hNT₂ : N ≤ H ⊔ zpowers v₀ := by
    intro n hn
    have hnT := hNT hn
    have hn2 : n ^ 2 ∈ H := mem_sup_left (szA₁_le _ (hNsq n hn))
    by_cases hnH : n ∈ H
    · exact mem_sup_left hnH
    · have h1 := hS.start.mul_inv_mem_of_sq_mem_of_card_sylow hS.card_sylow hnT hv₀T hn2
        (by rw [hv₀2]; exact one_mem _) hnH hv₀S
      rw [show n = (n * v₀⁻¹) * v₀ by group]
      exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers v₀))
  have hT₂card : Nat.card (H ⊔ zpowers v₀ : Subgroup G) = 4 * (2 ^ f) ^ 3 := by
    have h2 := RankOne.Endings.relIndex_sup_zpowers_eq_two hv₀S hv₀N hv₀v₀
    have h3 := relIndex_mul_card (H := H) (K := H ⊔ zpowers v₀)
    rw [h2, inf_of_le_left le_sup_left,
      hS.start.card_szT₁_sup_of_card_sylow hS.card_sylow] at h3
    omega
  have hle := Subgroup.card_le_of_le hNT₂
  rw [hT₂card, hNcard] at hle
  have hge : 4 * (2 ^ f) ^ 3 ≤ Nat.card N := by
    rw [hNcard]
    calc 4 * (2 ^ f) ^ 3 ≤ 2 ^ f * (2 ^ f) ^ 3 := Nat.mul_le_mul_right _ hq4
      _ = (2 ^ f) ^ 4 := by ring
      _ ≤ Nat.card C := hCcard
  have hNeq : N = H ⊔ zpowers v₀ := eq_of_le_of_card_ge hNT₂ (by rw [hT₂card]; exact hge)
  have hv₀N' : v₀ ∈ N := by rw [hNeq]; exact mem_sup_right (mem_zpowers v₀)
  have hT₁W : szT₁ L T ≤ W := by
    intro y hy
    have hyN : y⁻¹ ∈ N := by rw [hNeq]; exact mem_sup_left (mem_sup_left (inv_mem hy))
    have h1 := hNcomm _ hyN _ hv₀N'
    rw [inv_inv, show y⁻¹ * v₀ * y * v₀⁻¹ = y⁻¹ * (v₀ * y * v₀⁻¹) by group] at h1
    exact (hWiff y hy).mp h1
  have h1 := Subgroup.card_le_of_le hT₁W
  rw [hT₁card, hWcard] at h1
  have h2 : (2 ^ f) ^ 2 < (2 ^ f) ^ 3 :=
    Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

end Coords

end Core

end U3C1OuterLevelData

end CFSG.SeitzReduction.RankOne
