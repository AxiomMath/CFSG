module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsF

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

@[expose] def U3C1GmsLangInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P →
      IsSylowOf 2 (T ⊓ centralizer ({t * w} : Set G))
        (centralizer ({t} : Set G) ⊓ centralizer ({t * w} : Set G))

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem exists_sq_eq_of_mem_szA₁ {a : G} (ha : a ∈ szA₁ (szT₁ L T)) : ∃ r ∈ V, r ^ 2 = a := by
  have hS := hW.step
  have hL := hW.level
  obtain ⟨-, hA₁card, -, -, -, -, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  let ψ : V →* V := MonoidHom.mk' (fun x => x ^ 2) (fun a b => by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
    exact (show Commute (a : G) (b : G) from hS.conf.comm a a.2 b b.2).mul_pow 2)
  have hψ : ∀ x : V, ((ψ x : V) : G) = (x : G) ^ 2 := fun x => by simp [ψ]
  have hker : Nat.card ψ.ker ≤ 2 ^ f := by
    rw [← hA₁card]
    refine Nat.card_le_card_of_injective (fun k : ψ.ker =>
      (⟨((k : V) : G), hS.conf.omega _ (k : V).2 (by
        rw [← hψ]; exact congrArg Subtype.val (MonoidHom.mem_ker.mp k.2))⟩ :
          szA₁ (szT₁ L T))) ?_
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  have hrange : ψ.range.map V.subtype ≤ szA₁ (szT₁ L T) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    change ((ψ x : V) : G) ∈ _
    rw [hψ]
    exact hL.muOne_sq_mem_szA₁_of_mem_V hS x.2
  have hcard := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hS.conf.card] at hcard
  have hrc : 2 ^ f ≤ Nat.card ψ.range := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card ψ.ker * Nat.card ψ.range < 2 ^ f * 2 ^ f :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hker) (Nat.mul_lt_mul_of_pos_left hlt hq0)
    rw [hcard, show 2 ^ f * 2 ^ f = (2 ^ f) ^ (1 + 1) by ring] at h1
    exact lt_irrefl _ h1
  have heq : ψ.range.map V.subtype = szA₁ (szT₁ L T) := by
    refine eq_of_le_of_card_ge hrange ?_
    rw [card_map_of_injective V.subtype_injective, hA₁card]
    exact hrc
  rw [← heq] at ha
  obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := ha
  exact ⟨x, x.2, (hψ x).symm⟩

theorem exists_F_conj_eq {a : G} (ha : a ∈ szA₁ (szT₁ L T)) :
    ∃ x ∈ U₁ ⊓ centralizer ({t * w} : Set G), x * t * x⁻¹ = a * t := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  obtain ⟨-, -, -, -, -, hA₁2, -⟩ := h.facts_of_card_sylow hS.card_sylow
  obtain ⟨W', hW'T₁, -, -, hW'ab, hW'inv, hW'sq, -⟩ :=
    h.exists_W_of_card_sylow hS.card_sylow hW.tw_mem hW.tw_sq hW.tw_not_mem
  obtain ⟨r, hrV, hr2⟩ := hW.exists_sq_eq_of_mem_szA₁ ha
  obtain ⟨y, hyW, hyy⟩ := hW'sq a ha
  have hyT₁ := hW'T₁ hyW
  have hyr : y * r = r * y := hL.muOne_T₁_comm hS hyT₁ hrV
  have hVU₁ : V ≤ U₁ := le_sup_right.trans hL.sup_le_U₁
  have hyrU : y * r ∈ U₁ := mul_mem (hW.T₁_le_U₁ hyT₁) (hVU₁ hrV)
  have hsq : (y * r) ^ 2 = 1 := by
    rw [(show Commute y r from hyr).mul_pow, hr2, sq y, hyy, ← sq]
    exact hA₁2 a ha
  have hinv : (t * w) * (y * r) * (t * w)⁻¹ = (y * r)⁻¹ := by
    rw [show (t * w) * (y * r) * (t * w)⁻¹ =
      ((t * w) * y * (t * w)⁻¹) * ((t * w) * r * (t * w)⁻¹) by group, hW'inv y hyW,
      hW.tw_inv hrV, mul_inv_rev, (Commute.inv_inv hyr.symm).eq]
  have hyrinv : (y * r)⁻¹ = y * r := by rw [inv_eq_iff_mul_eq_one, ← sq, hsq]
  refine ⟨y * r, mem_inf.mpr ⟨hyrU, mem_centralizer_singleton_iff.mpr ?_⟩, ?_⟩
  · rw [hyrinv] at hinv
    calc y * r * (t * w) = (t * w) * (y * r) * (t * w)⁻¹ * (t * w) := by rw [hinv]
      _ = (t * w) * (y * r) := by group
  · have hrt : t * r⁻¹ * t⁻¹ = r := by
      rw [show t * r⁻¹ * t⁻¹ = (t * r * t⁻¹)⁻¹ by group, hS.conf.inv r hrV, inv_inv]
    have hyt : y * t = t * y := mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hyT₁
    have hya : y * (r * r) = (r * r) * y := by
      have := hL.muOne_T₁_comm hS hyT₁ (mul_mem hrV hrV)
      exact this
    calc y * r * t * (y * r)⁻¹ = y * (r * (t * r⁻¹ * t⁻¹) * t) * y⁻¹ := by group
      _ = y * (r * r * t) * y⁻¹ := by rw [hrt]
      _ = (y * (r * r)) * t * y⁻¹ := by group
      _ = (r * r) * (y * t) * y⁻¹ := by rw [hya]; group
      _ = (r * r) * (t * y) * y⁻¹ := by rw [hyt]
      _ = r ^ 2 * t := by rw [sq]; group
      _ = a * t := by rw [hr2]

theorem isSylowOf_S₀
    (hc : ∀ g : G, g * t * g⁻¹ ∈ swapS₂ P U T → g * t * g⁻¹ ∈ U ⊔ T)
    (hLang : IsSylowOf 2 (T ⊓ centralizer ({t * w} : Set G))
        (centralizer ({t} : Set G) ⊓ centralizer ({t * w} : Set G))) :
    IsSylowOf 2 (swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
      (centralizer ({t * w} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  set I := centralizer ({t * w} : Set G) with hIdef
  set S₀ := swapS₂ P U T ⊓ I with hS₀def
  have hS₀I : S₀ ≤ I := inf_le_right
  have hS₀2 : IsPGroup 2 S₀ := hW.isPGroup_S₂.to_le inf_le_left
  have hwt := hW.wt_comm
  have htv : t * (t * w) = (t * w) * t := by rw [mul_assoc t w t, hwt]
  have htS₀ : t ∈ S₀ :=
    mem_inf.mpr ⟨hW.le_S₂ (mem_sup_right hW.t_mem), mem_centralizer_singleton_iff.mpr htv⟩
  have hsS₀ : s ∈ S₀ := by
    refine mem_inf.mpr ⟨hW.s_mem_S₂, mem_centralizer_singleton_iff.mpr ?_⟩
    calc s * (t * w) = s * (t * w) * s⁻¹ * s := by group
      _ = (t * w) * s := by rw [hW.conj_tw]
  by_contra hns
  have hns' : ¬ ∃ Q : Sylow 2 I, (Q : Subgroup I) = S₀.subgroupOf I := by
    rintro ⟨Q, hQ⟩
    apply hns
    refine ⟨Q, ?_⟩
    rw [hQ, subgroupOf_map_subtype, inf_eq_left.mpr hS₀I]
  obtain ⟨z, hzN, hzS, Q', hQ'2, hSQ', hzQ'⟩ :=
    exists_normalizer_not_mem_of_not_isSylow (hS₀2.comap_subtype (K := I)) hns'
  have hyI : (z : G) ∈ I := z.2
  have hyN : ∀ a ∈ S₀, (z : G) * a * (z : G)⁻¹ ∈ S₀ := by
    intro a ha
    have h1 : (⟨a, hS₀I ha⟩ : I) ∈ S₀.subgroupOf I := ha
    exact (mem_normalizer_iff.mp hzN _).mp h1
  have hyS : (z : G) ∉ S₀ := fun h' => hzS h'
  set P'' : Subgroup G := Q'.map I.subtype with hP''def
  have hP''2 : IsPGroup 2 P'' := hQ'2.map _
  have hS₀P'' : S₀ ≤ P'' := fun a ha => ⟨⟨a, hS₀I ha⟩, hSQ' ha, rfl⟩
  have hyP'' : (z : G) ∈ P'' := ⟨z, hzQ', rfl⟩
  set y : G := (z : G) with hydef
  have hyt : y * t * y⁻¹ ∈ S₀ := hyN t htS₀
  have hytU : y * t * y⁻¹ ∈ U ⊔ T := hc y (mem_inf.mp hyt).1
  have hytv : y * t * y⁻¹ * (t * w) = (t * w) * (y * t * y⁻¹) :=
    mem_centralizer_singleton_iff.mp (mem_inf.mp hyt).2
  obtain ⟨σ, hσS₀, hσ⟩ : ∃ σ ∈ S₀, σ * t * σ⁻¹ = y * t * y⁻¹ := by
    have hFS₀ : ∀ x ∈ U₁ ⊓ centralizer ({t * w} : Set G), x ∈ S₀ := fun x hx =>
      mem_inf.mpr ⟨hW.le_S₂ (mem_sup_left (hL.U₁_le (mem_inf.mp hx).1)), (mem_inf.mp hx).2⟩
    rcases hW.conj_t_mem_of_commute_tw y hytU hytv with h1 | h1
    · obtain ⟨x, hxF, hx⟩ := hW.exists_F_conj_eq h1
      refine ⟨x, hFS₀ x hxF, ?_⟩
      rw [hx]
      group
    · have hsN' : s⁻¹ ∈ normalizer ((U ⊔ T : Subgroup G) : Set G) :=
        inv_mem hW.s_mem_normalizer
      have ha' := hL.gms_conj_szA₁ hS hsN' h1
      rw [inv_inv] at ha'
      obtain ⟨x, hxF, hx⟩ := hW.exists_F_conj_eq ha'
      refine ⟨s * x, mul_mem hsS₀ (hFS₀ x hxF), ?_⟩
      calc s * x * t * (s * x)⁻¹ = s * (x * t * x⁻¹) * s⁻¹ := by group
        _ = s * (s⁻¹ * (y * t * y⁻¹ * w⁻¹) * s * t) * s⁻¹ := by rw [hx]
        _ = (y * t * y⁻¹ * w⁻¹) * (s * t * s⁻¹) := by group
        _ = y * t * y⁻¹ := by rw [hW.conj_t]; group
  have hy't : (σ⁻¹ * y) * t = t * (σ⁻¹ * y) := by
    calc (σ⁻¹ * y) * t = σ⁻¹ * (y * t * y⁻¹) * y := by group
      _ = σ⁻¹ * (σ * t * σ⁻¹) * y := by rw [hσ]
      _ = t * (σ⁻¹ * y) := by group
  have hy'S : σ⁻¹ * y ∉ S₀ := fun h' => hyS (by
    rw [show y = σ * (σ⁻¹ * y) by group]
    exact mul_mem hσS₀ h')
  have hy'P : σ⁻¹ * y ∈ P'' := mul_mem (inv_mem (hS₀P'' hσS₀)) hyP''
  have hy'I : σ⁻¹ * y ∈ I := mul_mem (inv_mem (hS₀I hσS₀)) hyI
  set T₀ := T ⊓ I with hT₀def
  have hT₀S₀ : T₀ ≤ S₀ := inf_le_inf_right _ (le_sup_right.trans hW.le_S₂)
  have hHK : T₀ ⊔ zpowers (σ⁻¹ * y) ≤ centralizer ({t} : Set G) ⊓ I :=
    sup_le (inf_le_inf_right _ h.le)
      (zpowers_le.mpr (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hy't, hy'I⟩))
  have hH2 : IsPGroup 2 (T₀ ⊔ zpowers (σ⁻¹ * y) : Subgroup G) :=
    hP''2.to_le (sup_le (hT₀S₀.trans hS₀P'') (zpowers_le.mpr hy'P))
  have heq := hLang.eq_of_le le_sup_left hHK hH2
  apply hy'S
  apply hT₀S₀
  rw [← heq]
  exact mem_sup_right (mem_zpowers _)

end U3C1OuterSwapHigh

theorem u3C1GmsExtremalInput_of_lang (hLang : U3C1GmsLangInput) :
    U3C1GmsExtremalInput :=
  fun G _ _ L f t T R₂ D d V U U₁ w s P hW _ _ hc _ =>
    hW.isSylowOf_S₀ hc (hLang G L f t T R₂ D d V U U₁ w s P hW)

end CFSG.SeitzReduction.RankOne
