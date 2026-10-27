module

public import CFSG.Quasithin.H13.L32NSet14
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.L32NSet14

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G]

section Inputs

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem hyp1223_F4 (h1332 : Stmt13_3_2_F4) (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) : Hyp1223 G T L V where
  simple := hH.simple
  nonabelian := hH.nonabelian
  qtke := hH.qtke
  sylow := hH.sylow
  notAlt := fun hA => hH.not_excluded (Hyp14310One.qt13Excluded_of_alt hA)
  maximal := (h1332 G T L hH L hH.faithful).2.1.2.1
  faithful := hH.faithful
  quasisimple := ((h1332 G T L hH L hH.faithful).2.2.1.2 V hV).2.2.1.quasisimple
  normalizes := (h1332 G T L hH L hH.faithful).2.1.1
  irrPlus := hV

theorem hyp1281One_F4 (h1332 : Stmt13_3_2_F4) (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) [IsMulCommutative ↥V]
    (hlin : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1)
    (hnat : BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 1) : Hyp1281One G T L V 3 where
  hyp := hyp1223_F4 h1332 hH hV
  n_mem := Or.inl rfl
  quot := nonempty_equiv_SL32_of_lieModel hlin
  natural := ⟨inferInstance, hnat⟩
  not_linear := fun hL => hH.not_excluded (Or.inr (Or.inl (Or.inl hL)))
  not_alt9 := fun hA => hH.not_excluded (Or.inr (Or.inr (Or.inl hA)))
  not_m24 := fun hM => hH.not_excluded (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl hM))))))

theorem isTSub_V1_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ centralizer (L : Set G) = ⊥) : IsTSub T V (fsuV1 T V) 1 := by
  have hTV : T ≤ normalizer (V : Set G) := ((h1332 G T L hH L hH.faithful).2.2.1.2 V hV).2.1
  have hTZ : T ≤ normalizer (quasithinOmegaOneCenter T : Set G) := by
    have hZ : quasithinOmegaOneCenter T ≤ T ⊓ centralizer (T : Set G) :=
      (closure_le _).mpr fun _ hz => hz.1
    exact (le_centralizer_iff.mp (hZ.trans inf_le_right)).trans
      (centralizer_le_normalizer _)
  obtain ⟨⟨-, hV1, -⟩, -, -⟩ := h1334 G T L V hH hV
  refine ⟨inf_le_left, by rw [hV1, hZV, card_bot]; norm_num, fun t ht => ?_⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxV, hxZ⟩
    exact ⟨(mem_normalizer_iff.mp (hTV ht) x).mp hxV, (mem_normalizer_iff.mp (hTZ ht) x).mp hxZ⟩
  · rintro ⟨hxV, hxZ⟩
    exact ⟨(mem_normalizer_iff.mp (hTV ht) x).mpr hxV,
      (mem_normalizer_iff.mp (hTZ ht) x).mpr hxZ⟩

end Inputs

structure Setting_F4 (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ : Subgroup G)
    [IsMulCommutative ↥V] : Prop where
  h1222 : Stmt12_2_2_F4
  h1332 : Stmt13_3_2_F4
  h1334 : A6.Stmt13_3_4_F4
  hH : QTH13 G T L
  hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V
  hZV : V ⊓ centralizer (L : Set G) = ⊥
  hV2 : A6.IsV2 T V V₂
  hlin : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1
  hnat : BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 1

namespace Setting_F4
open CFSG.Quasithin.H13.L32NSet14.Setting_F4

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V] (S : Setting_F4 G T L V V₂)
include S

theorem h1281_F4 : Hyp1281One G T L V 3 := hyp1281One_F4 S.h1332 S.hH S.hV S.hlin S.hnat

theorem hV1_F4 : IsTSub T V (fsuV1 T V) 1 := isTSub_V1_F4 S.h1332 S.h1334 S.hH S.hV S.hZV

theorem card_V_F4 : Nat.card V = 8 := S.h1281_F4.card_sq.1

theorem sq_V_F4 {v : G} (hv : v ∈ V) : v ^ 2 = 1 := S.h1281_F4.card_sq.2.1 v hv

theorem mul_self_V_F4 {v : G} (hv : v ∈ V) : v * v = 1 := by rw [← sq]; exact S.sq_V_F4 hv

theorem comm_V_F4 {x y : G} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x :=
  S.h1281_F4.card_sq.2.2 x hx y hy

theorem TV_F4 : T ≤ normalizer (V : Set G) := ((S.h1332 G T L S.hH L S.hH.faithful).2.2.1.2 V S.hV).2.1

theorem VT_F4 : V ≤ T := ((S.h1332 G T L S.hH L S.hH.faithful).2.2.1.2 V S.hV).1

theorem TL_F4 : T ≤ normalizer (L : Set G) := (S.h1332 G T L S.hH L S.hH.faithful).2.1.1

theorem LV_F4 : L ≤ normalizer (V : Set G) := S.hV.2.2.1

theorem card_V1_F4 : Nat.card (fsuV1 T V) = 2 := by simpa using S.hV1_F4.2.1

theorem T_V1_F4 : T ≤ normalizer (fsuV1 T V : Set G) := S.hV1_F4.2.2

theorem card_L_F4 : Nat.card L = 168 * Nat.card (pCoreOf 2 L) := by
  obtain ⟨θ, hθ, hker⟩ := exists_surj_SL32_of_lieModel S.hlin
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv,
    HSType.card_SL_three_two, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).toEquiv] at h1
  exact h1

theorem card_autOn_F4 : Nat.card (autOn L V) = 168 := by
  rw [card_eq_of_binaryNaturalSL S.hnat (by norm_num)]
  decide

theorem cent_eq_F4 : L ⊓ centralizer (V : Set G) = pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrel := Subgroup.relIndex_mul_card (L ⊓ centralizer (V : Set G)) L
  rw [← card_autOn_eq_relIndex S.LV_F4, inf_right_comm, inf_idem, S.card_autOn_F4, S.card_L_F4] at hrel
  have hc : Nat.card ↥(L ⊓ centralizer (V : Set G)) = Nat.card (pCoreOf 2 L) := by omega
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_card_eq
  have hp : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G)) := IsPGroup.of_card (by rw [hc, hk])
  have hle : L ⊓ centralizer (V : Set G) ≤ pCoreOf 2 L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun l hl => ?_) hp
    refine mem_normalizer_iff.mpr fun c => ⟨fun ⟨hcL, hcV⟩ => ?_, fun ⟨hcL, hcV⟩ => ?_⟩
    · refine ⟨L.mul_mem (L.mul_mem hl hcL) (L.inv_mem hl), mem_centralizer_iff.mpr fun v hv => ?_⟩
      have hv' : l⁻¹ * v * l ∈ V := by
        have := (mem_normalizer_iff.mp (S.LV_F4 (L.inv_mem hl)) v).mp hv
        rwa [inv_inv] at this
      have := mem_centralizer_iff.mp hcV _ hv'
      calc v * (l * c * l⁻¹) = l * ((l⁻¹ * v * l) * c) * l⁻¹ := by group
        _ = l * (c * (l⁻¹ * v * l)) * l⁻¹ := by rw [this]
        _ = l * c * l⁻¹ * v := by group
    · have hcL' : c ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem hl) hcL) hl
        rwa [show l⁻¹ * (l * c * l⁻¹) * l = c by group] at this
      refine ⟨hcL', mem_centralizer_iff.mpr fun v hv => ?_⟩
      have hv' : l * v * l⁻¹ ∈ V := (mem_normalizer_iff.mp (S.LV_F4 hl) v).mp hv
      have := mem_centralizer_iff.mp hcV _ hv'
      calc v * c = l⁻¹ * ((l * v * l⁻¹) * (l * c * l⁻¹)) * l := by group
        _ = l⁻¹ * ((l * c * l⁻¹) * (l * v * l⁻¹)) * l := by rw [this]
        _ = c * v := by group
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc])

theorem isPGroup_cent_sup_F4 : IsPGroup 2 ↥((L ⊔ T) ⊓ centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTV : L ⊔ T ≤ normalizer (V : Set G) := sup_le S.LV_F4 S.TV_F4
  have hA : autOn (L ⊔ T) V = autOn L V := by
    have h1 : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One S.h1281_F4
    rw [h1, eq_top_iff, ← h1]
    exact autOn_mono le_sup_left
  have hrel := Subgroup.relIndex_mul_card ((L ⊔ T) ⊓ centralizer (V : Set G)) (L ⊔ T)
  rw [← card_autOn_eq_relIndex hLTV, inf_right_comm, inf_idem, hA, S.card_autOn_F4] at hrel
  have hsup := card_sup_mul_card_inf S.TL_F4
  rw [sup_comm T L, S.card_L_F4] at hsup
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_card_eq
  obtain ⟨b, hb⟩ := S.hH.sylow.1.exists_card_eq
  rw [ha, hb] at hsup
  have hdvd : Nat.card ↥((L ⊔ T) ⊓ centralizer (V : Set G)) ∣ 2 ^ (b + a) := by
    refine ⟨Nat.card ↥(T ⊓ L), ?_⟩
    have : 168 * (Nat.card ↥((L ⊔ T) ⊓ centralizer (V : Set G)) * Nat.card ↥(T ⊓ L)) =
        168 * 2 ^ (b + a) := by
      rw [← mul_assoc, hrel, hsup, pow_add]
      ring
    omega
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact IsPGroup.of_card hk

theorem eq_of_mem_V1_F4 {z v : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hv : v ∈ fsuV1 T V) :
    v = 1 ∨ v = z := by
  by_contra h
  push Not at h
  have hvz := mul_mem_of_card_eq_two_mul (W := (⊥ : Subgroup G)) (X := fsuV1 T V) bot_le
    (by rw [S.card_V1_F4, card_bot]) (by rw [card_bot]; norm_num) hv hz
    (by rw [mem_bot]; exact h.1) (by rw [mem_bot]; exact hz1)
  rw [mem_bot] at hvz
  apply h.2
  calc v = v * z * z := by rw [mul_assoc, S.mul_self_V_F4 (Subgroup.mem_inf.mp hz).1, mul_one]
    _ = z := by rw [hvz, one_mul]

theorem mem_g1_F4 {z g : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hg : g * z * g⁻¹ = z) :
    g ∈ normalizer (fsuV1 T V : Set G) := by
  rw [normalizer_eq_centralizer_of_card_eq_two S.card_V1_F4, mem_centralizer_iff]
  intro v hv
  rcases S.eq_of_mem_V1_F4 hz hz1 hv with rfl | rfl
  · group
  · calc v * g = g * v * g⁻¹ * g := by rw [hg]
      _ = g * v := by group

theorem mem_V2_F4 {a v : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) (hv : v ∈ V₂) :
    v ∈ fsuV1 T V ∨ a * v ∈ fsuV1 T V := by
  by_cases h : v ∈ fsuV1 T V
  · exact Or.inl h
  · exact Or.inr (mul_mem_of_card_eq_two_mul S.hV2.1 (by rw [S.hV2.2.2.2, S.card_V1_F4])
      (by rw [S.card_V1_F4]; norm_num) ha hv haV h)

theorem mem_V_F4 {b v : G} (hb : b ∈ V) (hbV : b ∉ V₂) (hv : v ∈ V) : v ∈ V₂ ∨ b * v ∈ V₂ := by
  by_cases h : v ∈ V₂
  · exact Or.inl h
  · exact Or.inr (mul_mem_of_card_eq_two_mul S.hV2.2.1 (by rw [S.card_V_F4, S.hV2.2.2.2])
      (by rw [S.hV2.2.2.2]; norm_num) hb hv hbV h)

theorem exists_basis_F4 : ∃ z a b : G, z ∈ fsuV1 T V ∧ z ≠ 1 ∧ a ∈ V₂ ∧ a ∉ fsuV1 T V ∧ b ∈ V ∧
    b ∉ V₂ := by
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ fsuV1 T V, z ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : fsuV1 T V = ⊥ := (eq_bot_iff_forall _).mpr h
    have h2 := S.card_V1_F4
    rw [h1, card_bot] at h2
    omega
  obtain ⟨a, ha, haV⟩ : ∃ a ∈ V₂, a ∉ fsuV1 T V := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show V₂ ≤ fsuV1 T V from h)
    rw [S.hV2.2.2.2, S.card_V1_F4] at h1
    omega
  obtain ⟨b, hb, hbV⟩ : ∃ b ∈ V, b ∉ V₂ := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show V ≤ V₂ from h)
    rw [S.card_V_F4, S.hV2.2.2.2] at h1
    omega
  exact ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩

theorem exists_lift_F4 [Module (ZMod 2) (Additive ↥V)] (β : Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :
    ∃ l ∈ L, ∀ v (hv : v ∈ V),
      l * v * l⁻¹ = ((Additive.toMul (β (Additive.ofMul ⟨v, hv⟩)) : ↥V) : G) := by
  have hαL : mulAutOfLin β ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One S.h1281_F4]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
  refine ⟨l, Subgroup.mem_subgroupOf.1 hlL, fun v hv => ?_⟩
  rw [← mulAutOfLin_apply, ← hlα]
  rfl

theorem exists_odd_pow_F4 {l : G} (hl : l ∈ L) (h3 : ∀ v ∈ V, l ^ 3 * v * (l ^ 3)⁻¹ = v) :
    ∃ k : ℕ, (l ^ k) ^ 3 = 1 ∧ ∀ v ∈ V, l ^ k * v * (l ^ k)⁻¹ = l * v * l⁻¹ := by
  have hcV : l ^ 3 ∈ centralizer (V : Set G) := mem_centralizer_iff.mpr fun v hv => by
    calc v * l ^ 3 = (l ^ 3 * v * (l ^ 3)⁻¹) * l ^ 3 := by rw [h3 v hv]
      _ = l ^ 3 * v := by group
  have hc : l ^ 3 ∈ pCoreOf 2 L := by
    rw [← S.cent_eq_F4]
    exact ⟨L.pow_mem hl 3, hcV⟩
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨_, hc⟩
  have hm' : (l ^ 3) ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    rwa [Subgroup.coe_pow] at this
  obtain ⟨q, hq⟩ := exists_four_pow m
  refine ⟨4 ^ m, ?_, fun v hv => ?_⟩
  · rw [← pow_mul, show 4 ^ m * 3 = 3 * 2 ^ m * 2 ^ m by
      rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]; ring, pow_mul, pow_mul, hm', one_pow]
  · have hcv : (l ^ 3) ^ q * v * ((l ^ 3) ^ q)⁻¹ = v := by
      have := mem_centralizer_iff.mp ((centralizer (V : Set G)).pow_mem hcV q) v hv
      rw [← this]
      group
    rw [← hq, pow_add, pow_one, pow_mul]
    calc l * (l ^ 3) ^ q * v * (l * (l ^ 3) ^ q)⁻¹ =
        l * ((l ^ 3) ^ q * v * ((l ^ 3) ^ q)⁻¹) * l⁻¹ := by group
      _ = l * v * l⁻¹ := by rw [hcv]

theorem exists_rot_F4 {p u w : G} (hp : p ∈ V) (hu : u ∈ V) (hw : w ∈ V)
    (hu1 : u ≠ 1) (hw1 : w ≠ 1) (hup : u ≠ p) (hwp : w ≠ p) (huw : u ≠ w) (hwpu : w ≠ p * u) :
    ∃ l ∈ L, l ^ 3 = 1 ∧ l * p * l⁻¹ = p ∧ l * u * l⁻¹ = w ∧ l * w * l⁻¹ = u * w := by
  let _ := zmodModuleOf (fun v hv => S.sq_V_F4 hv)
  let c : Additive ↥V → G := fun q => ((Additive.toMul q : ↥V) : G)
  set p' : Additive ↥V := Additive.ofMul ⟨p, hp⟩
  set u' : Additive ↥V := Additive.ofMul ⟨u, hu⟩
  set w' : Additive ↥V := Additive.ofMul ⟨w, hw⟩
  have hc0 : c 0 = 1 := rfl
  have hcadd : ∀ q r, c (q + r) = c q * c r := fun _ _ => rfl
  have hupw : u ≠ p * w := fun h => hwpu (by
    rw [h, ← mul_assoc, S.mul_self_V_F4 hp, one_mul])
  have h1 : u' ∉ (ZMod 2) ∙ p' ⊔ (ZMod 2) ∙ w' := fun h => by
    rcases mem_span_pair_zmod2 h with h | h | h | h
    · exact hu1 (congrArg c h)
    · exact hup (congrArg c h)
    · exact huw (congrArg c h)
    · exact hupw ((congrArg c h).trans (hcadd _ _))
  have h2 : w' ∉ (ZMod 2) ∙ p' ⊔ (ZMod 2) ∙ u' := fun h => by
    rcases mem_span_pair_zmod2 h with h | h | h | h
    · exact hw1 (congrArg c h)
    · exact hwp (congrArg c h)
    · exact huw (congrArg c h).symm
    · exact hwpu ((congrArg c h).trans (hcadd _ _))
  obtain ⟨ρ, hρ3, hρu, hρw, hρP⟩ := exists_rotation h1 h2
  obtain ⟨l₀, hl₀, hconj⟩ := S.exists_lift_F4 ρ
  have hconj' : ∀ v : ↥V, l₀ * (v : G) * l₀⁻¹ = c (ρ (Additive.ofMul v)) :=
    fun v => hconj v v.2
  have h3 : ∀ v ∈ V, l₀ ^ 3 * v * (l₀ ^ 3)⁻¹ = v := by
    intro v hv
    have e : l₀ ^ 3 * v * (l₀ ^ 3)⁻¹ = l₀ * (l₀ * (l₀ * v * l₀⁻¹) * l₀⁻¹) * l₀⁻¹ := by
      rw [pow_three]
      group
    rw [e, hconj v hv, hconj' (Additive.toMul (ρ (Additive.ofMul ⟨v, hv⟩))),
      hconj' (Additive.toMul (ρ (Additive.ofMul (Additive.toMul (ρ (Additive.ofMul ⟨v, hv⟩))))))]
    show c (ρ (ρ (ρ (Additive.ofMul ⟨v, hv⟩)))) = v
    rw [hρ3]
    rfl
  obtain ⟨k, hk3, hk⟩ := S.exists_odd_pow_F4 hl₀ h3
  refine ⟨l₀ ^ k, L.pow_mem hl₀ k, hk3, ?_, ?_, ?_⟩
  · rw [hk p hp, hconj p hp, hρP _ (Submodule.mem_span_singleton_self _)]
    rfl
  · rw [hk u hu, hconj u hu]
    show c (ρ u') = w
    rw [hρu]
    rfl
  · rw [hk w hw, hconj w hw]
    show c (ρ w') = u * w
    rw [hρw]
    show (((Additive.toMul u' : ↥V) : G))⁻¹ / ((Additive.toMul w' : ↥V) : G) = u * w
    show u⁻¹ / w = u * w
    rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_right (S.mul_self_V_F4 hu),
      inv_eq_of_mul_eq_one_right (S.mul_self_V_F4 hw)]

end Setting_F4

end CFSG.Quasithin.H13.L32NSet14
