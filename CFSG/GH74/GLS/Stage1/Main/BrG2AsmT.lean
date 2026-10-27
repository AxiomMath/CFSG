module

public import CFSG.GH74.GLS.Stage1.Main.BrG2Quat
public import CFSG.GH74.GLS.Stage1.Main.BrG2TStr
public import CFSG.GH74.GLS.Stage1.Main.BrG2NoOut
public import CFSG.GH74.GLS.Stage1.Main.BrG2Swap

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.IVK.Lifted

open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Main

section Asm

theorem four_le_pRank_of_elemAbelian {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : Y →* X) (hf : Function.Injective f) {E : Subgroup Y} (hE : IsElementaryAbelian 2 ↥E)
    (hcard : 16 ≤ Nat.card ↥E) : 4 ≤ pRank 2 X := by
  obtain ⟨r, hr⟩ := (IsElementaryAbelian.isPGroup 2 ↥E).exists_card_eq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr4 : 4 ≤ r := by
    rw [hr] at hcard
    by_contra h
    push Not at h
    have : 2 ^ r ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hA : IsElementaryAbelian 2 ↥(E.map f) := IsElementaryAbelian.map f
  have hAc : Nat.card ↥(E.map f) = 2 ^ r := by
    rw [Subgroup.card_map_of_injective hf, hr]
  unfold CFSG.pRank
  refine hr4.trans (le_csSup ?_ ⟨E.map f, hA, hAc⟩)
  refine ⟨Nat.card X, ?_⟩
  rintro s ⟨B, -, hB⟩
  have h1 : Nat.card ↥B ≤ Nat.card X := Subgroup.card_le_card_group B
  have h2 : s < 2 ^ s := Nat.lt_two_pow_self
  omega

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.mul_mem_K_iff (hcen : Cen2 G z S) {x y : CentralizerBar z} (hx : x ∈ barOf z S)
    (hy : y ∈ barOf z S) :
    x * y ∈ C.K₁ ⊔ C.K₂ ↔ (x ∈ C.K₁ ⊔ C.K₂ ↔ y ∈ C.K₁ ⊔ C.K₂) := by
  obtain ⟨-, hrel⟩ := C.sylow_inf hcen
  have hidx : ((C.K₁ ⊔ C.K₂).subgroupOf (barOf z S)).index = 2 := hrel
  have := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
  simpa [Subgroup.mem_subgroupOf] using this

include C in
theorem G2Ctx.exists_invol (hcen : Cen2 G z S) (hinv : ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) :
    ∃ u ∈ barOf z S, u * u = 1 ∧ u ∉ C.K₁ ⊔ C.K₂ := by
  obtain ⟨s, hsS, hsR, hs2⟩ := hinv
  have hSC : S ≤ Cen z := hcen.sylow.le
  refine ⟨toBar z ⟨s, hSC hsS⟩, ⟨⟨s, hSC hsS⟩, hsS, rfl⟩, ?_, ?_⟩
  · have hsq : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hs2, pow_two] at this
    rw [← map_mul]
    have : (⟨s, hSC hsS⟩ * ⟨s, hSC hsS⟩ : ↥(Cen z)) = 1 := Subtype.ext hsq
    rw [this, map_one]
  · intro hmem
    apply hsR
    exact ⟨hsS, (C.mem_LC_iff hcen hsS (hSC hsS)).2 hmem⟩

end Asm

section Asm2

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.P₁_conj (hcen : Cen2 G z S) {u : CentralizerBar z} (huT : u ∈ barOf z S)
    (hu : C.K₁.map (MulAut.conj u).toMonoidHom = C.K₂) :
    C.P₁.map (MulAut.conj u).toMonoidHom = C.P₂ := by
  have hKn := C.normal_K hcen
  have hle : C.P₁.map (MulAut.conj u).toMonoidHom ≤ C.P₂ := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (barOf z S).mul_mem ((barOf z S).mul_mem huT (hp.1.1)) ((barOf z S).inv_mem huT)
    · exact hKn.conj_mem p (Subgroup.mem_sup_left hp.2) u
    · rw [← hu]
      exact ⟨p, hp.2, rfl⟩
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective (MulAut.conj u).injective, C.card_P₁ hcen, C.card_P₂ hcen]

include C in
theorem G2Ctx.T_normalizes (hcen : Cen2 G z S) (h5 : 5 ≤ Nat.card C.F₂)
    (hq₁ : IVK.IsQuaternionTwoGroup ↥C.P₁ (C.n + 1))
    (hq₂ : IVK.IsQuaternionTwoGroup ↥C.P₂ (C.n + 1))
    (hrank : pRank 2 ↥S ≤ 3) (hinv : ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) :
    ∀ x ∈ barOf z S, x ∈ normalizer (C.K₁ : Set (CentralizerBar z)) := by
  intro x hx
  by_contra hxN
  obtain ⟨u, huT, hu2, huK⟩ := C.exists_invol hcen hinv
  have hcomps := C.comps hcen h5
  have hK₁c : IsComponent C.K₁ := by
    have : C.K₁ ∈ {K | IsComponent K} := by rw [hcomps]; exact Or.inl rfl
    exact this
  have hconj : IsComponent (C.K₁.map (MulAut.conj x).toMonoidHom) :=
    isComponent_map_of_isComponent (MulAut.conj x) hK₁c
  have hmem : C.K₁.map (MulAut.conj x).toMonoidHom ∈
      ({C.K₁, C.K₂} : Set (Subgroup (CentralizerBar z))) := by
    rw [← hcomps]; exact hconj
  have hx2 : C.K₁.map (MulAut.conj x).toMonoidHom = C.K₂ := by
    rcases hmem with h | h
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h) hxN
    · exact h
  have hxK : x ∉ C.K₁ ⊔ C.K₂ := fun h => hxN (C.normalizer_K₁ h)
  have hxiK : x⁻¹ ∉ C.K₁ ⊔ C.K₂ := fun h => hxK (by simpa using (C.K₁ ⊔ C.K₂).inv_mem h)
  have hr : x⁻¹ * u ∈ C.K₁ ⊔ C.K₂ :=
    (C.mul_mem_K_iff hcen ((barOf z S).inv_mem hx) huT).2 (by
      constructor <;> intro h <;> contradiction)
  have hrN : x⁻¹ * u ∈ normalizer (C.K₁ : Set (CentralizerBar z)) := C.normalizer_K₁ hr
  have hu1 : C.K₁.map (MulAut.conj u).toMonoidHom = C.K₂ := by
    have hr' : C.K₁.map (MulAut.conj (x⁻¹ * u)).toMonoidHom = C.K₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hrN
    have : C.K₁.map (MulAut.conj u).toMonoidHom =
        (C.K₁.map (MulAut.conj (x⁻¹ * u)).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext y
      show u * y * u⁻¹ = x * ((x⁻¹ * u) * y * (x⁻¹ * u)⁻¹) * x⁻¹
      group
    rw [this, hr', hx2]
  have hP := C.P₁_conj hcen huT hu1
  obtain ⟨E, hEle, hEel, hE16⟩ := swap_elementary_abelian_sixteen C.two_le hq₁ hq₂ C.P_comm
    (C.card_P_inf hcen) hu2 hP
  have hET : E ≤ barOf z S := by
    refine hEle.trans (sup_le (sup_le ?_ ?_) ?_)
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_left
    · exact Subgroup.zpowers_le.2 huT
  set β := barEquiv z S hcen.sylow.le (cen2_S_inf_oddCore hcen) with hβ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEs : IsElementaryAbelian 2 ↥(E.subgroupOf (barOf z S)) :=
    IsElementaryAbelian.subgroupOf hET
  have hEc : 16 ≤ Nat.card ↥(E.subgroupOf (barOf z S)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv]
    exact hE16
  have h4 := four_le_pRank_of_elemAbelian β.symm.toMonoidHom β.symm.injective hEs hEc
  omega

end Asm2

section Asm3

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.no_outside (hcen : Cen2 G z S)
    (hq₁ : IVK.IsQuaternionTwoGroup ↥C.P₁ (C.n + 1))
    (hq₂ : IVK.IsQuaternionTwoGroup ↥C.P₂ (C.n + 1)) {g : CentralizerBar z} (hg : g ∈ barOf z S)
    (hgK : g ∉ C.K₁ ⊔ C.K₂) :
    (¬ ∀ p ∈ C.P₁, g * p = p * g) ∧ (¬ ∀ p ∈ C.P₂, g * p = p * g) := by
  have hR : C.R ≤ barOf z S := inf_le_left
  have hP₁ : C.P₁ ≤ barOf z S := inf_le_left.trans hR
  have hP₂ : C.P₂ ≤ barOf z S := inf_le_left.trans hR
  obtain ⟨hT2, -⟩ := C.sylow_bar hcen
  obtain ⟨-, hrel⟩ := C.sylow_inf hcen
  have hgen := C.three_gen hcen
  have h₁ : IVK.IsQuaternionTwoGroup ↥(C.P₁.subgroupOf (barOf z S)) (C.n + 1) := by
    obtain ⟨h3, ⟨e⟩⟩ := hq₁
    exact ⟨h3, ⟨(Subgroup.subgroupOfEquivOfLe hP₁).trans e⟩⟩
  have h₂ : IVK.IsQuaternionTwoGroup ↥(C.P₂.subgroupOf (barOf z S)) (C.n + 1) := by
    obtain ⟨h3, ⟨e⟩⟩ := hq₂
    exact ⟨h3, ⟨(Subgroup.subgroupOfEquivOfLe hP₂).trans e⟩⟩
  have hc : ∀ a ∈ C.P₁.subgroupOf (barOf z S), ∀ b ∈ C.P₂.subgroupOf (barOf z S), a * b = b * a :=
    fun a ha b hb => Subtype.ext (C.P_comm _ ha _ hb)
  have hinf : Nat.card ↥(C.P₁.subgroupOf (barOf z S) ⊓ C.P₂.subgroupOf (barOf z S)) = 2 := by
    have h1 : C.P₁.subgroupOf (barOf z S) ⊓ C.P₂.subgroupOf (barOf z S) =
        (C.P₁ ⊓ C.P₂).subgroupOf (barOf z S) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left.trans hP₁ : C.P₁ ⊓ C.P₂ ≤ barOf z S)).toEquiv]
    exact C.card_P_inf hcen
  have hsup : C.P₁.subgroupOf (barOf z S) ⊔ C.P₂.subgroupOf (barOf z S) =
      (C.K₁ ⊔ C.K₂).subgroupOf (barOf z S) := by
    rw [← Subgroup.subgroupOf_sup hP₁ hP₂, C.P_sup hcen]
    exact Subgroup.inf_subgroupOf_left _ _
  have hidx : (C.P₁.subgroupOf (barOf z S) ⊔ C.P₂.subgroupOf (barOf z S)).index = 2 := by
    rw [hsup]; exact hrel
  have hg' : (⟨g, hg⟩ : ↥(barOf z S)) ∉
      C.P₁.subgroupOf (barOf z S) ⊔ C.P₂.subgroupOf (barOf z S) := by
    rw [hsup]
    exact hgK
  refine ⟨fun hgc => ?_, fun hgc => ?_⟩
  · exact no_outside_centralizer hT2 hgen C.two_le h₁ h₂ hc hinf hidx hg'
      (fun p hp => Subtype.ext (hgc p hp))
  · refine no_outside_centralizer hT2 hgen C.two_le h₂ h₁ (fun a ha b hb => (hc b hb a ha).symm)
      (by rw [inf_comm]; exact hinf) (by rw [sup_comm]; exact hidx) ?_ ?_ (g := ⟨g, hg⟩)
    · rw [sup_comm]; exact hg'
    · exact fun p hp => Subtype.ext (hgc p hp)

end Asm3

section Asm5

theorem mod8_of_factorization {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (hv : (Nat.card ↥(StatedSL 2 F)).factorization 2 = 2 + 1) :
    Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5 := by
  have hc := card_statedSL_two' F
  set q := Nat.card F with hq
  have hqodd : q % 2 = 1 := Nat.odd_iff.1 hodd
  by_contra h
  push Not at h
  have h17 : q % 8 = 1 ∨ q % 8 = 7 := by omega
  have h16 : 16 ∣ q ^ 2 - 1 := by
    obtain ⟨k, hk⟩ : ∃ k, q = 8 * k + (q % 8) := ⟨q / 8, by omega⟩
    rcases h17 with h1 | h7
    · rw [h1] at hk
      refine ⟨4 * k ^ 2 + k, ?_⟩
      have : q ^ 2 = 64 * k ^ 2 + 16 * k + 1 := by rw [hk]; ring
      have h2 : q ^ 2 - 1 = 64 * k ^ 2 + 16 * k := by omega
      rw [h2]; ring
    · rw [h7] at hk
      refine ⟨4 * k ^ 2 + 7 * k + 3, ?_⟩
      have : q ^ 2 = 64 * k ^ 2 + 112 * k + 49 := by rw [hk]; ring
      have h2 : q ^ 2 - 1 = 64 * k ^ 2 + 112 * k + 48 := by omega
      rw [h2]; ring
  have hdvd : 2 ^ 4 ∣ Nat.card ↥(StatedSL 2 F) := by
    rw [hc]
    exact Dvd.dvd.mul_left (by simpa using h16) q
  have hne : Nat.card ↥(StatedSL 2 F) ≠ 0 := Nat.card_pos.ne'
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 hdvd
  omega

end Asm5

section Asm6

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.K₂_eq_centralizer (hcen : Cen2 G z S) :
    C.K₂ = (C.K₁ ⊔ C.K₂) ⊓ centralizer (C.K₁ : Set (CentralizerBar z)) := by
  obtain ⟨ζ, hζ₁, hζ₂, hζo, -, -⟩ := C.exists_zeta hcen
  apply le_antisymm
  · refine le_inf le_sup_right (fun b hb => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact C.comm a ha b hb
  · rintro y ⟨hy, hyc⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := y_mem_sup_of_commute C.comm hy
    have hac : (⟨a, ha⟩ : ↥C.K₁) ∈ Subgroup.center ↥C.K₁ := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 := Subgroup.mem_centralizer_iff.1 hyc (g : CentralizerBar z) g.2
      have h2 := C.comm g g.2 b hb
      have h3 : (g : CentralizerBar z) * a * b = a * g * b := by
        calc (g : CentralizerBar z) * a * b = (g : CentralizerBar z) * (a * b) := by rw [mul_assoc]
          _ = (a * b) * g := h1
          _ = a * (b * g) := by rw [mul_assoc]
          _ = a * (g * b) := by rw [← h2]
          _ = a * g * b := by rw [mul_assoc]
      exact mul_right_cancel h3
    have hζo' : orderOf (⟨ζ, hζ₁⟩ : ↥C.K₁) = 2 := by rw [orderOf_mk]; exact hζo
    have ha' : a = 1 ∨ a = ζ := by
      rcases kabs_center_cases C.odd₁ (C.e₁.trans (specialLinearGroupEquivStatedSL 2 C.F₁).symm)
        hζo' hac with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    rcases ha' with rfl | rfl
    · rw [one_mul]; exact hb
    · exact mul_mem hζ₂ hb

include C in
theorem G2Ctx.conj_K₂ (hcen : Cen2 G z S) {x : CentralizerBar z}
    (hx : x ∈ normalizer (C.K₁ : Set (CentralizerBar z))) {h : CentralizerBar z} (hh : h ∈ C.K₂) :
    x * h * x⁻¹ ∈ C.K₂ := by
  have hKn := C.normal_K hcen
  rw [C.K₂_eq_centralizer hcen] at hh ⊢
  obtain ⟨hK, hc⟩ := hh
  refine ⟨hKn.conj_mem h hK x, ?_⟩
  show x * h * x⁻¹ ∈ centralizer (C.K₁ : Set (CentralizerBar z))
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' : x⁻¹ * a * x ∈ C.K₁ := by
    have := (Subgroup.mem_normalizer_iff.1 ((normalizer _).inv_mem hx) a).1 ha
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hc _ ha'
  calc a * (x * h * x⁻¹) = x * ((x⁻¹ * a * x) * h) * x⁻¹ := by group
    _ = x * (h * (x⁻¹ * a * x)) * x⁻¹ := by rw [h1]
    _ = (x * h * x⁻¹) * a := by group

include C in
theorem G2Ctx.normalizer_K₂_of (hcen : Cen2 G z S) {x : CentralizerBar z}
    (hx : x ∈ normalizer (C.K₁ : Set (CentralizerBar z))) :
    x ∈ normalizer (C.K₂ : Set (CentralizerBar z)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => C.conj_K₂ hcen hx hh, fun hh => ?_⟩
  have := C.conj_K₂ hcen ((normalizer _).inv_mem hx) hh
  have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
  rwa [e] at this

end Asm6

section Asm7

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.P₁_normalizes (hcen : Cen2 G z S) {u : CentralizerBar z} (huT : u ∈ barOf z S)
    (huN : u ∈ normalizer (C.K₁ : Set (CentralizerBar z))) (hu2 : u * u = 1) :
    u ∈ normalizer (C.P₁ : Set (CentralizerBar z)) := by
  have hKn := C.normal_K hcen
  have key : ∀ v ∈ barOf z S, v ∈ normalizer (C.K₁ : Set (CentralizerBar z)) →
      ∀ p ∈ C.P₁, v * p * v⁻¹ ∈ C.P₁ := by
    intro v hv hvN p hp
    refine ⟨⟨(barOf z S).mul_mem ((barOf z S).mul_mem hv hp.1.1) ((barOf z S).inv_mem hv),
      hKn.conj_mem p hp.1.2 v⟩, ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 hvN p).1 hp.2
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key u huT huN h hh, fun hh => ?_⟩
  have := key u⁻¹ ((barOf z S).inv_mem huT) (by rw [hui]; exact huN) _ hh
  have e : u⁻¹ * (u * h * u⁻¹) * u⁻¹⁻¹ = h := by group
  rwa [e] at this

end Asm7

section Asm9

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.P₂_normalizes (hcen : Cen2 G z S) {u : CentralizerBar z} (huT : u ∈ barOf z S)
    (huN : u ∈ normalizer (C.K₂ : Set (CentralizerBar z))) (hu2 : u * u = 1) :
    u ∈ normalizer (C.P₂ : Set (CentralizerBar z)) := by
  have hKn := C.normal_K hcen
  have key : ∀ v ∈ barOf z S, v ∈ normalizer (C.K₂ : Set (CentralizerBar z)) →
      ∀ p ∈ C.P₂, v * p * v⁻¹ ∈ C.P₂ := by
    intro v hv hvN p hp
    refine ⟨⟨(barOf z S).mul_mem ((barOf z S).mul_mem hv hp.1.1) ((barOf z S).inv_mem hv),
      hKn.conj_mem p hp.1.2 v⟩, ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 hvN p).1 hp.2
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key u huT huN h hh, fun hh => ?_⟩
  have := key u⁻¹ ((barOf z S).inv_mem huT) (by rw [hui]; exact huN) _ hh
  have e : u⁻¹ * (u * h * u⁻¹) * u⁻¹⁻¹ = h := by group
  rwa [e] at this

end Asm9

end CFSG.GH74.GLS.Stage1.Main
