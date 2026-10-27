module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step218Closed
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Sec2V4

namespace Sec2

variable {G : Type} [Group G] [Finite G]

theorem alt5_derivedSeries_eq_top (n : ℕ) : derivedSeries (alternatingGroup (Fin 5)) n = ⊤ := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hnab : ¬ IsMulCommutative (alternatingGroup (Fin 5)) := by
    intro h
    have h1 := alternatingGroup.center_eq_bot (α := Fin 5) (by simp)
    rw [Subgroup.center_eq_top_iff.mpr h] at h1
    exact bot_ne_top h1.symm
  have hperf := CFSG.GroupTheory.commutator_eq_top_of_isSimpleGroup hs hnab
  induction n with
  | zero => exact derivedSeries_zero _
  | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def, hperf]

omit [Finite G] in
theorem derivedSeries_sup_eq_of_alt5 {Y M : Subgroup G} (φ : ↥Y →* alternatingGroup (Fin 5))
    (hφ : Function.Surjective φ) (hker : φ.ker = M.subgroupOf Y) (n : ℕ) :
    (derivedSeries ↥Y n).map Y.subtype ⊔ (M ⊓ Y) = Y := by
  have hmap : (derivedSeries ↥Y n).map φ = ⊤ := by
    rw [map_derivedSeries_eq hφ, alt5_derivedSeries_eq_top]
  have hsup : derivedSeries ↥Y n ⊔ M.subgroupOf Y = ⊤ := by
    have := congrArg (Subgroup.comap φ) hmap
    rwa [comap_map_eq, comap_top, hker] at this
  have := congrArg (Subgroup.map Y.subtype) hsup
  rwa [Subgroup.map_sup, subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype] at this

theorem alt5_eq_top_of_index_le {K : Subgroup (alternatingGroup (Fin 5))} (hK : K.index ≤ 4) :
    K = ⊤ := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases K.normalCore_normal.eq_bot_or_eq_top with h | h
  · exfalso
    have h1 := K.index_normalCore_le_factorial_index
    rw [h, Subgroup.index_bot, card_alternatingGroup_five] at h1
    have h2 : K.index.factorial ≤ (4 : ℕ).factorial := Nat.factorial_le hK
    have h3 : (4 : ℕ).factorial = 24 := rfl
    omega
  · exact eq_top_iff.mpr (h ▸ K.normalCore_le)

theorem le_centralizer_of_coord {S Z H : Subgroup G} (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) : H ≤ centralizer (Z : Set G) := by
  intro h hh
  rw [mem_centralizer_iff]
  intro c hc
  set K := (centralizer ({c} : Set G)).subgroupOf H with hKdef
  have hKidx : K.index ≤ 4 := by
    let f : ↥H ⧸ K → ↥Z := Quotient.lift
      (fun k : ↥H => (⟨(k : G) * c * (k : G)⁻¹, conj_mem_Z_of_normS hS (hHS k.2) hc⟩ : ↥Z))
      (by
        intro a b hab
        have hab' : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.mp hab
        rw [hKdef, mem_subgroupOf, mem_centralizer_singleton_iff] at hab'
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hab' ⊢
        calc (a : G) * c * (a : G)⁻¹ = (a : G) * ((a : G)⁻¹ * b * c * ((a : G)⁻¹ * b)⁻¹) *
              (a : G)⁻¹ := by rw [hab']; group
          _ = (b : G) * c * (b : G)⁻¹ := by group)
    have hf : Function.Injective f := by
      intro p q hpq
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
      have h1 : (a : G) * c * (a : G)⁻¹ = (b : G) * c * (b : G)⁻¹ := congrArg Subtype.val hpq
      rw [QuotientGroup.eq, hKdef, mem_subgroupOf, mem_centralizer_singleton_iff]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (a : G)⁻¹ * b * c = (a : G)⁻¹ * ((b : G) * c * (b : G)⁻¹) * b := by group
        _ = (a : G)⁻¹ * ((a : G) * c * (a : G)⁻¹) * b := by rw [h1]
        _ = c * ((a : G)⁻¹ * b) := by group
    rw [Subgroup.index_eq_card]
    have h1 := Nat.card_le_card_of_injective f hf
    rwa [hS.card] at h1
  have hKpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hKtop : K.map C.φ = ⊤ :=
    alt5_eq_top_of_index_le ((Nat.le_of_dvd hKpos (Subgroup.index_map_dvd K C.surj)).trans hKidx)
  have hφh : C.φ ⟨h, hh⟩ ∈ K.map C.φ := by
    rw [hKtop]
    exact mem_top _
  obtain ⟨k, hk, hkh⟩ := hφh
  have hks : k⁻¹ * ⟨h, hh⟩ ∈ C.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkh, inv_mul_cancel]
  rw [C.ker, mem_subgroupOf] at hks
  have hk : (k : G) * c = c * k :=
    mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp (show k ∈ K from hk))
  have hsc : ((k⁻¹ * ⟨h, hh⟩ : ↥H) : G) * c = c * ((k⁻¹ * ⟨h, hh⟩ : ↥H) : G) :=
    (hS.comm_Z hc hks).symm
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hsc
  calc c * h = (c * k) * ((k : G)⁻¹ * h) := by group
    _ = (k * c) * ((k : G)⁻¹ * h) := by rw [hk]
    _ = k * (c * ((k : G)⁻¹ * h)) := by group
    _ = k * ((k : G)⁻¹ * h * c) := by rw [hsc]
    _ = h * c := by group

section Setting

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem le_normalizer_sup_oddCoreIn_sec2Z (hQO : GoldschmidtQO) (h24 : Step24) (h26 : Step26)
    (h26ii : Step26ii) (h212 : Step212) (hS : Sec2Setting G A R g E F) {T₀ : Subgroup G}
    (hT₀ : sec2P E ⊔ sec2S A R E F ≤ T₀)
    (hT₀s : IsSylowOf 2 T₀ (normalizer (sec2S A R E F : Set G))) :
    centralizer (sec2Z A E F : Set G) ≤ normalizer ((sec2S A R E F ⊔
      AS76b.oddCoreIn (centralizer (sec2Z A E F : Set G)) : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := sec2S A R E F with hSdef
  set Z := sec2Z A E F with hZdef
  set H := sec2H E F with hHdef
  set CZ := centralizer (Z : Set G) with hCZdef
  have hSp : Special S Z := special_of h24 hS
  obtain ⟨C⟩ := nonempty_coord h26 hS
  obtain ⟨-, -, -, -, -, -, -, hHS, -⟩ := h26 G A R g E F hS
  have hS1024 : Nat.card S = 1024 := C.card_S hSp
  have hZS : Z ≤ S := hSp.le
  have hSCZ : S ≤ CZ := fun s hs => mem_centralizer_iff.mpr fun c hc => hSp.comm_Z hc hs
  have hZCZ : Z ≤ CZ := hZS.trans hSCZ
  have hHCZ : H ≤ CZ := le_centralizer_of_coord C hSp hHS
  have hST₀ : S ≤ T₀ := le_sup_right.trans hT₀
  have hT₀N : T₀ ≤ normalizer (S : Set G) := hT₀s.le
  obtain ⟨c₀, hc₀Z, hc₀1⟩ : ∃ c₀ ∈ Z, c₀ ≠ 1 := by
    by_contra hcon
    have hbot : Z = ⊥ := eq_bot_iff.mpr fun x hx =>
      mem_bot.mpr (by_contra fun hx1 => hcon ⟨x, hx, hx1⟩)
    have h1 := hSp.card
    rw [hbot, card_bot] at h1
    norm_num at h1
  have hc₀2 : orderOf c₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hSp.elem c₀ hc₀Z) hc₀1
  obtain ⟨z₀, hz₀Z, hz₀c⟩ : ∃ z₀ ∈ Z, z₀ ∉ zpowers c₀ := by
    by_contra hcon
    have hle : Z ≤ zpowers c₀ := fun x hx => by_contra fun h => hcon ⟨x, hx, h⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [hSp.card, Nat.card_zpowers, hc₀2] at h1
    norm_num at h1
  have hc₀C : c₀ ∈ CZ := hZCZ hc₀Z
  have hz₀C : z₀ ∈ CZ := hZCZ hz₀Z
  set Cc : Subgroup ↥CZ := (zpowers c₀).subgroupOf CZ with hCcdef
  have hCcn : Cc.Normal := ⟨fun n hn k => by
    rw [hCcdef, mem_subgroupOf] at hn ⊢
    have h1 : (n : G) * k = k * n := mem_centralizer_iff.mp k.2 n (zpowers_le.mpr hc₀Z hn)
    have e : ((k * n * k⁻¹ : ↥CZ) : G) = n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h1]
      group
    rw [e]
    exact hn⟩
  set ρ : ↥CZ →* ↥CZ ⧸ Cc := QuotientGroup.mk' Cc with hρdef
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective Cc
  have hker : ρ.ker = Cc := QuotientGroup.ker_mk' Cc
  have hρeq : ∀ x y : ↥CZ, ρ x = ρ y → ((x⁻¹ * y : ↥CZ) : G) ∈ zpowers c₀ := fun x y hxy => by
    have h1 : x⁻¹ * y ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    rw [hker, hCcdef, mem_subgroupOf] at h1
    exact h1
  have hρ1 : ∀ x : ↥CZ, (x : G) ∈ zpowers c₀ → ρ x = 1 := fun x hx => by
    rw [← MonoidHom.mem_ker, hker, hCcdef, mem_subgroupOf]
    exact hx
  set z' : ↥CZ ⧸ Cc := ρ ⟨z₀, hz₀C⟩ with hz'def
  have hz'2 : orderOf z' = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hz'def, ← map_pow]
      refine hρ1 _ ?_
      have h1 : z₀ ^ 2 = 1 := by rw [sq]; exact hSp.elem z₀ hz₀Z
      rw [Subgroup.coe_pow]
      show z₀ ^ 2 ∈ zpowers c₀
      rw [h1]
      exact one_mem _
    · intro h1
      apply hz₀c
      have h2 := hρeq 1 ⟨z₀, hz₀C⟩ (by rw [map_one]; exact h1.symm)
      simpa using h2
  have hCz' : centralizer ({z'} : Set (↥CZ ⧸ Cc)) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    rw [mem_centralizer_singleton_iff]
    obtain ⟨k, rfl⟩ := hρs w
    rw [hz'def, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_iff.mp k.2 z₀ hz₀Z).symm
  have hρZ : ∀ w : ↥CZ, (w : G) ∈ Z → ρ w ∈ zpowers z' := by
    intro w hw
    have hab : (1 : G) ≠ c₀ := hc₀1.symm
    have hac : (1 : G) ≠ z₀ := fun h => hz₀c (h ▸ one_mem _)
    have had : (1 : G) ≠ c₀ * z₀ := by
      intro h
      apply hz₀c
      have e : z₀ = c₀⁻¹ := by
        calc z₀ = c₀⁻¹ * (c₀ * z₀) := by group
          _ = c₀⁻¹ := by rw [← h, mul_one]
      rw [e]
      exact inv_mem (mem_zpowers c₀)
    have hbc : c₀ ≠ z₀ := fun h => hz₀c (h ▸ mem_zpowers c₀)
    have hbd : c₀ ≠ c₀ * z₀ := fun h => hac (left_eq_mul.mp h).symm
    have hcd : z₀ ≠ c₀ * z₀ := fun h => hc₀1 (right_eq_mul.mp h)
    rcases hSp.eq_of_four (one_mem _) hc₀Z hz₀Z (Z.mul_mem hc₀Z hz₀Z) hw hab hac had hbc hbd hcd
      with h | h | h | h
    · rw [hρ1 w (by rw [h]; exact one_mem _)]
      exact one_mem _
    · rw [hρ1 w (by rw [h]; exact mem_zpowers c₀)]
      exact one_mem _
    · have e : ρ w = z' := by
        rw [hz'def]
        congr 1
        exact Subtype.ext h
      rw [e]
      exact mem_zpowers z'
    · have e : ρ w = z' := by
        have e1 : w = ⟨c₀, hc₀C⟩ * ⟨z₀, hz₀C⟩ := Subtype.ext h
        rw [e1, map_mul, hρ1 ⟨c₀, hc₀C⟩ (mem_zpowers c₀), one_mul]
      rw [e]
      exact mem_zpowers z'
  set Q' : Subgroup (↥CZ ⧸ Cc) := (S.subgroupOf CZ).map ρ with hQ'def
  set T' : Subgroup (↥CZ ⧸ Cc) := ((T₀ ⊓ CZ).subgroupOf CZ).map ρ with hT'def
  set N' : Subgroup (↥CZ ⧸ Cc) := (H.subgroupOf CZ).map ρ with hN'def
  have hT₀G : IsSylowOf 2 T₀ ⊤ := ((h212 G A R g E F hS).2 T₀ hT₀ hT₀s).1
  have hT₀NZ : IsSylowOf 2 T₀ (normalizer (Z : Set G)) :=
    hT₀G.of_le (hT₀N.trans (normalizer_le_normalizer_sec2Z hSp)) le_top
  have hT₁ : IsSylowOf 2 (T₀ ⊓ CZ) CZ := hT₀NZ.inf_of_le_normalizer
    (centralizer_le_normalizer _) (normalizer_le_normalizer_centralizer_of Z)
  obtain ⟨Q₁, hQ₁⟩ := hT₁.exists_sylow_eq_subgroupOf
  have hT'syl : IsSylowOf 2 T' (centralizer ({z'} : Set (↥CZ ⧸ Cc))) := by
    rw [hCz']
    have hT'eq : T' = ((Q₁.mapSurjective hρs : Sylow 2 (↥CZ ⧸ Cc)) : Subgroup (↥CZ ⧸ Cc)) := by
      rw [Sylow.coe_mapSurjective, hQ₁]
    rw [hT'eq, isSylowOf_iff]
    refine ⟨le_top, (Q₁.mapSurjective hρs).isPGroup', ?_⟩
    rw [relIndex_top_right]
    exact (Q₁.mapSurjective hρs).not_dvd_index
  have hQ'T' : Q' ≤ T' := map_mono fun a ha =>
    mem_subgroupOf.mpr ⟨hST₀ (mem_subgroupOf.mp ha), a.2⟩
  have hz'Q' : z' ∈ Q' := ⟨⟨z₀, hz₀C⟩, mem_subgroupOf.mpr (hZS hz₀Z), rfl⟩
  have hQ'card : Nat.card Q' = 2 ^ 9 := by
    have h1 := relIndex_mul_card (H := ρ.ker) (K := S.subgroupOf CZ)
    rw [relIndex_ker, hker] at h1
    have h2 : Cc ⊓ S.subgroupOf CZ = Cc := inf_eq_left.mpr fun x hx =>
      mem_subgroupOf.mpr (hZS (zpowers_le.mpr hc₀Z (mem_subgroupOf.mp hx)))
    have h3 : Nat.card Cc = 2 := by
      rw [hCcdef, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr hc₀C)).toEquiv,
        Nat.card_zpowers, hc₀2]
    have h4 : Nat.card (S.subgroupOf CZ) = 1024 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hSCZ).toEquiv, hS1024]
    rw [h2, h3, h4] at h1
    show Nat.card ↥((S.subgroupOf CZ).map ρ) = 2 ^ 9
    omega
  have hQ'comm : ∀ x ∈ Q', ∀ y ∈ Q', x * y * x⁻¹ * y⁻¹ ∈ zpowers z' := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    refine hρZ _ ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hSp.comm_mem (mem_subgroupOf.mp ha) (mem_subgroupOf.mp hb)
  have hQ'cl : ∀ x ∈ Q', ∀ h ∈ centralizer ({z'} : Set (↥CZ ⧸ Cc)), h⁻¹ * x * h ∈ T' →
      h⁻¹ * x * h ∈ Q' := by
    rintro _ ⟨a, ha, rfl⟩ h' - hT
    obtain ⟨k, rfl⟩ := hρs h'
    rw [← map_inv, ← map_mul, ← map_mul] at hT ⊢
    obtain ⟨t, ht, hte⟩ := hT
    have h1 := hρeq t _ hte
    have ht' : (t : G) ∈ T₀ := (mem_subgroupOf.mp ht).1
    have hkak : ((k⁻¹ * a * k : ↥CZ) : G) ∈ T₀ := by
      have e : ((k⁻¹ * a * k : ↥CZ) : G) = t * ((t⁻¹ * (k⁻¹ * a * k) : ↥CZ) : G) := by simp
      rw [e]
      exact T₀.mul_mem ht' (hST₀ (hZS (zpowers_le.mpr hc₀Z h1)))
    have hmem := conj_mem_sec2S_of_mem h24 h26ii h212 hS hT₀ hT₀s (mem_subgroupOf.mp ha) k.2
      (by simpa using hkak)
    exact ⟨k⁻¹ * a * k, mem_subgroupOf.mpr (by simpa using hmem), rfl⟩
  have hN'Q' : N' ≤ normalizer (Q' : Set (↥CZ ⧸ Cc)) := by
    refine le_trans (map_mono ?_) (le_normalizer_map ρ)
    intro k hk
    rw [mem_subgroupOf] at hk
    rw [mem_normalizer_iff]
    intro a
    rw [mem_subgroupOf, mem_subgroupOf]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using mem_normalizer_iff.mp (hHS hk) a
  have hder : ∀ B' : Subgroup (↥CZ ⧸ Cc), zpowers z' ≤ B' → B' < Q' →
      N' ≤ normalizer (B' : Set (↥CZ ⧸ Cc)) → ∀ n : ℕ,
        ∃ k ∈ (derivedSeries ↥N' n).map N'.subtype, ∃ x ∈ Q', k⁻¹ * x * k * x⁻¹ ∉ B' := by
    intro B' hzB' hB'Q' hN'B' n
    by_contra hcon
    push Not at hcon
    set B : Subgroup G := (B'.comap ρ).map CZ.subtype with hBdef
    have hmemB : ∀ w : ↥CZ, ρ w ∈ B' → (w : G) ∈ B := fun w hw => ⟨w, hw, rfl⟩
    have hBmem : ∀ w : ↥CZ, (w : G) ∈ B → ρ w ∈ B' := by
      rintro w ⟨w', hw', hww'⟩
      have e : w' = w := Subtype.ext hww'
      rw [← e]
      exact hw'
    have hZB : Z ≤ B := fun w hw => hmemB ⟨w, hZCZ hw⟩ (hzB' (hρZ _ hw))
    have hBS : B ≤ S := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨a, ha, hae⟩ := hB'Q'.le hw
      have h1 := hρeq a w hae
      have e : (w : G) = a * ((a⁻¹ * w : ↥CZ) : G) := by simp
      show (w : G) ∈ S
      rw [e]
      exact S.mul_mem (mem_subgroupOf.mp ha) (hZS (zpowers_le.mpr hc₀Z h1))
    have hHB : ∀ h ∈ H, ∀ b ∈ B, h * b * h⁻¹ ∈ B := by
      rintro h hh _ ⟨w, hw, rfl⟩
      have hk : ρ ⟨h, hHCZ hh⟩ ∈ N' := ⟨⟨h, hHCZ hh⟩, mem_subgroupOf.mpr hh, rfl⟩
      have h1 := (mem_normalizer_iff.mp (hN'B' hk) (ρ w)).mp hw
      rw [← map_inv, ← map_mul, ← map_mul] at h1
      exact hmemB _ h1
    let ι : ↥H →* ↥N' := (ρ.comp (Subgroup.inclusion hHCZ)).codRestrict N'
      fun k => ⟨Subgroup.inclusion hHCZ k, mem_subgroupOf.mpr k.2, rfl⟩
    have hDn : ∀ y ∈ derivedSeries ↥H n, ∀ s ∈ S, ((y : G))⁻¹ * s * y * s⁻¹ ∈ B := by
      intro y hy s hs
      have hyN : ι y ∈ derivedSeries ↥N' n :=
        map_derivedSeries_le_derivedSeries ι n ⟨y, hy, rfl⟩
      have h1 := hcon (N'.subtype (ι y)) ⟨ι y, hyN, rfl⟩ (ρ ⟨s, hSCZ hs⟩)
        ⟨⟨s, hSCZ hs⟩, mem_subgroupOf.mpr hs, rfl⟩
      have e : (N'.subtype (ι y) : ↥CZ ⧸ Cc) = ρ (Subgroup.inclusion hHCZ y) := rfl
      have e2 : (ρ (Subgroup.inclusion hHCZ y))⁻¹ * ρ ⟨s, hSCZ hs⟩ * ρ (Subgroup.inclusion hHCZ y) *
          (ρ ⟨s, hSCZ hs⟩)⁻¹ = ρ ((Subgroup.inclusion hHCZ y)⁻¹ * ⟨s, hSCZ hs⟩ *
            Subgroup.inclusion hHCZ y * (⟨s, hSCZ hs⟩ : ↥CZ)⁻¹) := by
        simp only [map_mul, map_inv]
      rw [e, e2] at h1
      have h2 := hmemB _ h1
      simpa [mul_assoc] using h2
    let K : Subgroup G :=
      { carrier := {y | y ∈ normalizer (S : Set G) ∧ y ∈ normalizer (B : Set G) ∧
          ∀ x ∈ S, y⁻¹ * x * y * x⁻¹ ∈ B}
        mul_mem' := by
          rintro a b ⟨haS, haB, ha⟩ ⟨hbS, hbB, hb⟩
          refine ⟨mul_mem haS hbS, mul_mem haB hbB, fun x hx => ?_⟩
          have e : (a * b)⁻¹ * x * (a * b) * x⁻¹ =
              b⁻¹ * (a⁻¹ * x * a * x⁻¹) * b * (b⁻¹ * x * b * x⁻¹) := by group
          rw [e]
          refine B.mul_mem ?_ (hb x hx)
          have := (mem_normalizer_iff.mp (inv_mem hbB) _).mp (ha x hx)
          simpa [mul_assoc] using this
        one_mem' := ⟨one_mem _, one_mem _, fun x _ => by simp [one_mem]⟩
        inv_mem' := by
          rintro a ⟨haS, haB, ha⟩
          refine ⟨inv_mem haS, inv_mem haB, fun x hx => ?_⟩
          have hx' : a * x * a⁻¹ ∈ S := (mem_normalizer_iff.mp haS x).mp hx
          have h1 := ha _ hx'
          have e : a⁻¹ * (a * x * a⁻¹) * a * (a * x * a⁻¹)⁻¹ = (a⁻¹⁻¹ * x * a⁻¹ * x⁻¹)⁻¹ := by
            group
          rw [e] at h1
          exact inv_mem_iff.mp h1 }
    have hDK : (derivedSeries ↥H n).map H.subtype ≤ K := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨hHS y.2, mem_normalizer_iff.mpr fun b => ⟨fun hb => hHB _ y.2 _ hb, fun hb => ?_⟩,
        fun x hx => hDn y hy x hx⟩
      have h1 := hHB _ (H.inv_mem y.2) _ hb
      simpa [mul_assoc] using h1
    have hSK : S ⊓ H ≤ K := by
      intro q hq
      refine ⟨le_normalizer hq.1, mem_normalizer_iff.mpr fun b => ⟨fun hb => ?_, fun hb => ?_⟩,
        fun x hx => hZB (by simpa [mul_assoc] using hSp.comm_mem (S.inv_mem hq.1) hx)⟩
      · have hc := hZB (hSp.comm_mem hq.1 (hBS hb))
        have e : q * b * q⁻¹ = q * b * q⁻¹ * b⁻¹ * b := by group
        rw [e]
        exact B.mul_mem hc hb
      · have hc := hZB (hSp.comm_mem (S.inv_mem hq.1) (hBS hb))
        have e : b = q⁻¹ * (q * b * q⁻¹) * q⁻¹⁻¹ * (q * b * q⁻¹)⁻¹ * (q * b * q⁻¹) := by group
        rw [e]
        exact B.mul_mem hc hb
    have hHK : H ≤ K :=
      (derivedSeries_sup_eq_of_alt5 C.φ C.surj C.ker n).ge.trans (sup_le hDK hSK)
    have hcomm : ∀ h ∈ H, ∀ s ∈ S, h⁻¹ * s * h * s⁻¹ ∈ B := fun h hh s hs => (hHK hh).2.2 s hs
    have hS₂ : C.S₂ ≤ B := by
      obtain ⟨a₁, ha₁, hψa₁⟩ := C.onto₂ (pair 0 3) (isEven_pair 0 3)
      obtain ⟨k, hkσ⟩ := C.surj ⟨_, cycle_mem_alternatingGroup⟩
      have hka := C.conj₂ k a₁ ha₁
      refine le_of_invariant_coord hZB C.add₂ C.ker₂ C.even₂ ?_
        (a₀ := (k : G) * a₁ * (k : G)⁻¹ * a₁⁻¹)
        (Subgroup.mem_inf.mpr ⟨C.S₂.mul_mem hka.1 (C.S₂.inv_mem ha₁), ?_⟩) ?_
      · intro σ hσ a ha
        obtain ⟨ha₂, haB⟩ := Subgroup.mem_inf.mp ha
        obtain ⟨k', hk'σ⟩ := C.surj ⟨σ, hσ⟩
        have hk'a := C.conj₂ k' a ha₂
        exact ⟨(k' : G) * a * (k' : G)⁻¹, Subgroup.mem_inf.mpr ⟨hk'a.1, hHB _ k'.2 _ haB⟩,
          by rw [hk'a.2, hk'σ]⟩
      · have h1 := hcomm (k : G)⁻¹ (H.inv_mem k.2) a₁ (C.le₂ ha₁)
        simpa using h1
      · rw [C.add₂ _ hka.1 _ (C.S₂.inv_mem ha₁), hka.2, hkσ, psi_inv_of_add C.add₂ ha₁, hψa₁]
        exact act_cycle_pair_ne
    have hS₃ : C.S₃ ≤ B := by
      obtain ⟨a₁, ha₁, hψa₁⟩ := C.onto₃ (pair 0 3) (isEven_pair 0 3)
      obtain ⟨k, hkσ⟩ := C.surj ⟨_, cycle_mem_alternatingGroup⟩
      have hka := C.conj₃ k a₁ ha₁
      refine le_of_invariant_coord hZB C.add₃ C.ker₃ C.even₃ ?_
        (a₀ := (k : G) * a₁ * (k : G)⁻¹ * a₁⁻¹)
        (Subgroup.mem_inf.mpr ⟨C.S₃.mul_mem hka.1 (C.S₃.inv_mem ha₁), ?_⟩) ?_
      · intro σ hσ a ha
        obtain ⟨ha₂, haB⟩ := Subgroup.mem_inf.mp ha
        obtain ⟨k', hk'σ⟩ := C.surj ⟨σ, hσ⟩
        have hk'a := C.conj₃ k' a ha₂
        exact ⟨(k' : G) * a * (k' : G)⁻¹, Subgroup.mem_inf.mpr ⟨hk'a.1, hHB _ k'.2 _ haB⟩,
          by rw [hk'a.2, hk'σ]⟩
      · have h1 := hcomm (k : G)⁻¹ (H.inv_mem k.2) a₁ (C.le₃ ha₁)
        simpa using h1
      · rw [C.add₃ _ hka.1 _ (C.S₃.inv_mem ha₁), hka.2, hkσ, psi_inv_of_add C.add₃ ha₁, hψa₁]
        exact act_cycle_pair_ne
    have hSB : sec2S A R E F ≤ B := by
      rw [← C.sup]
      exact sup_le hS₂ hS₃
    apply (lt_iff_le_not_ge.mp hB'Q').2
    rintro _ ⟨a, ha, rfl⟩
    exact hBmem a (hSB (mem_subgroupOf.mp ha))
  have hgold := hQO (↥CZ ⧸ Cc) z' Q' T' N' hz'2 hT'syl hQ'T' hz'Q' (Or.inr hQ'card) hQ'comm
    hQ'cl (by rw [hCz']; exact le_top) hN'Q' hder
  rw [hCz'] at hgold
  set O' : Subgroup (↥CZ ⧸ Cc) := AS76b.oddCoreIn ⊤ with hO'def
  have hO'n : O'.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff,
      ← normalizer_eq_top_iff.mpr (inferInstance : (⊤ : Subgroup (↥CZ ⧸ Cc)).Normal)]
    exact AS76b.normalizer_le_normalizer_oddCoreIn ⊤
  set L' : Subgroup ↥CZ := O'.comap ρ with hL'def
  have hL'n : L'.Normal := hO'n.comap ρ
  set L : Subgroup G := L'.map CZ.subtype with hLdef
  have hCcL : ρ.ker ≤ L' := fun x hx => by
    rw [hL'def, mem_comap, MonoidHom.mem_ker.mp hx]
    exact one_mem _
  have hc₀L : zpowers c₀ ≤ L := by
    rw [zpowers_le]
    refine ⟨⟨c₀, hc₀C⟩, hCcL ?_, rfl⟩
    rw [hker, hCcdef, mem_subgroupOf]
    exact mem_zpowers c₀
  have hLCZ : L ≤ CZ := map_subtype_le _
  have hrel : (zpowers c₀).relIndex L = Nat.card O' := by
    have h1 : zpowers c₀ = Cc.map CZ.subtype := by
      rw [hCcdef, subgroupOf_map_subtype, inf_eq_left.mpr (zpowers_le.mpr hc₀C)]
    have h2 := relIndex_ker (f := ρ) (K := L')
    rw [hker, hL'def, map_comap_eq_self_of_surjective hρs] at h2
    rw [h1, hLdef, relIndex_map_map_of_injective _ _ CZ.subtype_injective, h2]
  have hLeq : L = zpowers c₀ ⊔ AS76b.oddCoreIn L := by
    refine eq_sup_oddCoreIn_of_central ?_ hc₀L ?_ ?_
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc₀2, pow_one])
    · rw [zpowers_le]
      exact mem_centralizer_iff.mpr fun w hw => (mem_centralizer_iff.mp (hLCZ hw) c₀ hc₀Z).symm
    · rw [hrel]
      exact AS76b.odd_card_oddCoreIn _
  have hCZL : CZ ≤ normalizer (L : Set G) := AS76b.le_normalizer_map_subtype_of_normal CZ L'
  have hOL : AS76b.oddCoreIn L ≤ AS76b.oddCoreIn CZ :=
    le_oddCoreIn_of_odd_normal ((AS76b.oddCoreIn_le L).trans hLCZ)
      (hCZL.trans (AS76b.normalizer_le_normalizer_oddCoreIn L)) (AS76b.odd_card_oddCoreIn L)
  have hLle : L ≤ S ⊔ AS76b.oddCoreIn CZ := by
    rw [hLeq]
    exact sup_le_sup (zpowers_le.mpr (hZS hc₀Z)) hOL
  have hcomap : (Q' ⊔ O').comap ρ = S.subgroupOf CZ ⊔ L' := by
    have e : Q' ⊔ O' = (S.subgroupOf CZ ⊔ L').map ρ := by
      rw [Subgroup.map_sup, hL'def, map_comap_eq_self_of_surjective hρs]
    rw [e, comap_map_eq, sup_eq_left.mpr (hCcL.trans le_sup_right)]
  intro c hc
  apply AS76b.mem_normalizer_of_map_conj_le
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    have hgs : ρ ⟨c, hc⟩ * ρ ⟨s, hSCZ hs⟩ * (ρ ⟨c, hc⟩)⁻¹ ∈ Q' ⊔ O' :=
      (mem_normalizer_iff.mp (hgold (mem_top _)) _).mp
        (mem_sup_left ⟨⟨s, hSCZ hs⟩, mem_subgroupOf.mpr hs, rfl⟩)
    rw [← map_inv, ← map_mul, ← map_mul] at hgs
    have h1 : (⟨c, hc⟩ * ⟨s, hSCZ hs⟩ * (⟨c, hc⟩ : ↥CZ)⁻¹ : ↥CZ) ∈ S.subgroupOf CZ ⊔ L' := by
      rw [← hcomap]
      exact hgs
    have h2 := mem_map_of_mem CZ.subtype h1
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr hSCZ] at h2
    have h3 : c * s * c⁻¹ ∈ S ⊔ L := by simpa using h2
    exact (sup_le le_sup_left hLle) (by simpa [MulAut.conj_apply] using h3)
  · rintro _ ⟨o, ho, rfl⟩
    exact mem_sup_right ((mem_normalizer_iff.mp (AS76b.le_normalizer_oddCoreIn CZ hc) o).mp ho)

end Setting

end Sec2

end CFSG.ComponentClassification.AS81
