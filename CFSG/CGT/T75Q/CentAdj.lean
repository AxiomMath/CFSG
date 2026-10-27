module

public import CFSG.CGT.T75Q.Cent
public import CFSG.CGT.T75Q.Sec64Eight
public import CFSG.CGT.T75I.CenFacts
public import CFSG.CGT.T75I.CenX1
public import CFSG.CGT.T75I.CenCM
public import CFSG.CGT.T75I.Cen2
public import CFSG.CGT.T75I.CenBasic
public import CFSG.CGT.T75I.DMax
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
public import CFSG.CGT.Timmesfeld75.Sec4CaseITheoremX
public import CFSG.CGT.Timmesfeld75.Sec4Three
public import CFSG.CGT.Timmesfeld75.Sec68Stmt
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75P CFSG.CGT.T75I

variable {G : Type} [Group G]

theorem conjSubgroup_eq_of_mem {T : Subgroup G} (hT : IsWC T) {a b d : G}
    (ha : d ∈ conjSubgroup a T) (hb : d ∈ conjSubgroup b T) (hd : d ≠ 1) :
    conjSubgroup a T = conjSubgroup b T := by
  have h1 : b⁻¹ * d * b ∈ T := mem_conjSubgroup.1 hb
  have h2 : b⁻¹ * d * b ∈ conjSubgroup (b⁻¹ * a) T := by
    rw [mem_conjSubgroup]
    have := mem_conjSubgroup.1 ha
    have e : (b⁻¹ * a)⁻¹ * (b⁻¹ * d * b) * (b⁻¹ * a) = a⁻¹ * d * a := by group
    rw [e]
    exact this
  have hne : T ⊓ conjSubgroup (b⁻¹ * a) T ≠ ⊥ := by
    intro hbot
    have hm : b⁻¹ * d * b ∈ T ⊓ conjSubgroup (b⁻¹ * a) T := ⟨h1, h2⟩
    rw [hbot, Subgroup.mem_bot] at hm
    apply hd
    have : d = b * (b⁻¹ * d * b) * b⁻¹ := by group
    rw [this, hm]
    group
  have h3 := hT.conj_eq_of_inf_ne_bot hne
  calc conjSubgroup a T = conjSubgroup (b * (b⁻¹ * a)) T := by congr 1; group
    _ = conjSubgroup b (conjSubgroup (b⁻¹ * a) T) := (conjSubgroup_conjSubgroup b _ T).symm
    _ = conjSubgroup b T := by rw [h3]

section Core

variable {T T₂ : Subgroup G} [hN : ((cfgM T T₂).subgroupOf (T ⊔ T₂)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₂) ⧸ (cfgM T T₂).subgroupOf (T ⊔ T₂)

set_option quotPrecheck false in
local notation "TQ" =>
  (T.subgroupOf (T ⊔ T₂)).map (QuotientGroup.mk' ((cfgM T T₂).subgroupOf (T ⊔ T₂)))

theorem centralizes_of_adj [Finite G] (hS : Sec3 T T₂) {f : ℕ} (hf : 2 ≤ f)
    (hX : IsL2Pair XQ TQ (2 ^ f)) {c : G} (hcT : c ∈ Subgroup.centralizer (T : Set G))
    (hcT₂ : conjSubgroup c T₂ = T₂)
    (hSfix : ∀ s ∈ T ⊔ T₂, s ∈ Subgroup.normalizer (T : Set G) →
      c⁻¹ * (s * c * s⁻¹) ∈ cfgM T T₂ → s * c * s⁻¹ = c) :
    ∀ x ∈ T ⊔ T₂, x * c = c * x := by
  classical
  have hcinv : c⁻¹ ∈ Subgroup.centralizer (T : Set G) := Subgroup.inv_mem _ hcT
  have hcinvT₂ : conjSubgroup c⁻¹ T₂ = T₂ :=
    mem_normalizer_iff_conjSubgroup_eq.1
      (Subgroup.inv_mem _ (mem_normalizer_iff_conjSubgroup_eq.2 hcT₂))
  have hcomm' := comm_mem_cfgM_of_centralizer hS hX hcinv hcinvT₂
  have hu : ∀ x ∈ T ⊔ T₂, c⁻¹ * (x * c * x⁻¹) ∈ cfgM T T₂ := by
    intro x hx
    have h2 := hS.cfg.conj_mem_cfgM hx (hcomm' x hx)
    have e : x * (x⁻¹ * (c⁻¹ * x * c⁻¹⁻¹)) * x⁻¹ = c⁻¹ * (x * c * x⁻¹) := by group
    rw [e] at h2
    exact h2
  have hS' : ∀ s ∈ (Subgroup.normalizer (T : Set G)).subgroupOf (T ⊔ T₂),
      (s : G) * c * (s : G)⁻¹ = c := fun s hs =>
    hSfix s s.2 (Subgroup.mem_subgroupOf.1 hs) (hu s s.2)
  have hodd : Odd ((Subgroup.normalizer (T : Set G)).subgroupOf (T ⊔ T₂)).index := by
    have hle : (TQ).comap (QuotientGroup.mk' ((cfgM T T₂).subgroupOf (T ⊔ T₂))) ≤
        (Subgroup.normalizer (T : Set G)).subgroupOf (T ⊔ T₂) := by
      intro x hx
      exact Subgroup.mem_subgroupOf.2
        (mem_normalizer_of_map_mem hS x.2 (Subgroup.le_normalizer hx))
    have hdvd := Subgroup.index_dvd_of_le hle
    have hidx : ((TQ).comap (QuotientGroup.mk' ((cfgM T T₂).subgroupOf (T ⊔ T₂)))).index =
        (TQ).index := Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [hidx] at hdvd
    exact Odd.of_dvd_nat (odd_index_of_pair hX) hdvd
  obtain ⟨a, haM, hafix⟩ := exists_fixed_of_odd_index (X := T ⊔ T₂) (A := cfgM T T₂)
    (fun a ha => elemAbelian_mul_self hS.cfg.isElemAbelian_cfgM ha)
    (fun a ha b hb => elemAbelian_mul_comm hS.cfg.isElemAbelian_cfgM ha hb)
    (fun x hx a ha => hS.cfg.conj_mem_cfgM hx ha) hu hS' hodd
  obtain ⟨k, hkX, hkN, hkodd, hk1⟩ := exists_odd_normalizer hS hf hX
  have hkc : k * c * k⁻¹ = c := hSfix k hkX hkN (hu k hkX)
  have hka : k * a * k⁻¹ = a := by
    have h1 := hafix k hkX
    have e : k * (c * a) * k⁻¹ = (k * c * k⁻¹) * (k * a * k⁻¹) := by group
    rw [e, hkc] at h1
    exact mul_left_cancel h1
  have ha1 : a = 1 := Sec3.centralizer_cfgM_eq_bot_of_odd hS hX hkX hkodd hk1 a haM hka
  intro x hx
  have h1 := hafix x hx
  rw [ha1, mul_one] at h1
  calc x * c = (x * c * x⁻¹) * x := by group
    _ = c * x := by rw [h1]

end Core

variable {T T₁ : Subgroup G} {n : ℕ}

theorem centralizer_hSub_le_centralizer_adj_four (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n 1) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1) {k : ℕ}
    (ch : TransvChain n k) {g : G} (hne : conjSubgroup g T ≠ T)
    (hbot : normIn T (conjSubgroup g T) ≠ ⊥) (hT16 : Nat.card T = 16)
    (hL4 : Nat.card ↥(normIn T (conjSubgroup g T)) = 4) {c : G}
    (hcC : c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) :
    c ∈ Subgroup.centralizer (conjSubgroup g T : Set G) := by
  classical
  have : Finite G := hc.finite
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  have hTwc : IsWC T := hc.hy.pair.wc
  have hcfg : Cfg T (conjSubgroup g T) :=
    cfg_of_conj_conj hTwc ⟨1, (conjSubgroup_one T).symm⟩ ⟨g, rfl⟩ hne hbot
  have hS3 : Sec3 T (conjSubgroup g T) := hc.hS g hne hbot
  obtain ⟨hNM, f, hf, hiso⟩ := hc.hI g hne hbot
  have := hNM
  have h2f : (2 : ℕ) ^ f = 2 ^ 2 := by
    have h := hS3.card_eq_mul hf hiso
    rw [hT16, hL4] at h
    omega
  have hf2 : f = 2 := Nat.pow_right_injective (le_refl 2) h2f
  subst hf2
  have hX := hS3.isL2Pair_quotient hf hiso
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ normIn (conjSubgroup g T) T, b ≠ 1 := by
    obtain ⟨⟨d, hd⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcfg.ne₁
    exact ⟨d, hd, fun h => hne1 (Subtype.ext h)⟩
  have hbT' : b ∈ conjSubgroup g T := (mem_normIn.1 hbB).1
  have hbD : b ∈ normD T := mem_normD_of_mem_conjSubgroup hbT' hb1 (mem_normIn.1 hbB).2
  have hbH : b ∈ hSub T (normIn T₁ T) :=
    Sec6Ctx.normD_le_hSub h1 h63 (sec64Eight_of h62 h63) hc hbD
  have hcb : c * b = b * c := (Subgroup.mem_centralizer_iff.1 hcC b hbH).symm
  have hcN' : c ∈ Subgroup.normalizer (conjSubgroup g T : Set G) :=
    hcfg.wc₁.centralizer_le_normalizer hbT' hb1 (Subgroup.mem_centralizer_singleton_iff.2 hcb)
  have hcT : c ∈ Subgroup.centralizer (T : Set G) := Subgroup.centralizer_le hTH hcC
  have hcT' : conjSubgroup c (conjSubgroup g T) = conjSubgroup g T :=
    mem_normalizer_iff_conjSubgroup_eq.1 hcN'
  have hMC : ∀ m ∈ cfgM T (conjSubgroup g T),
      m ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) → m = 1 := by
    intro m hm hmC
    obtain ⟨l, hl, y, hy, rfl⟩ := hcfg.mem_cfgM_iff.1 hm
    have hlT : l ∈ T := (mem_normIn.1 hl).1
    have hmT : ∀ t ∈ T, l * y * t = t * (l * y) := fun t ht =>
      (Subgroup.mem_centralizer_iff.1 (Subgroup.centralizer_le hTH hmC) t ht).symm
    have hyT : ∀ t ∈ T, y * t = t * y := by
      intro t ht
      have hlt : l * t = t * l := elemAbelian_mul_comm hTwc.1 hlT ht
      have h2 : l * (y * t) = l * (t * y) := by
        calc l * (y * t) = l * y * t := by group
          _ = t * (l * y) := hmT t ht
          _ = (t * l) * y := by group
          _ = (l * t) * y := by rw [hlt]
          _ = l * (t * y) := by group
      exact mul_left_cancel h2
    have hyX : y ∈ T ⊔ conjSubgroup g T := Subgroup.mem_sup_right (mem_normIn.1 hy).1
    have hyT' : y ∈ T := mem_left_of_centralizes hS3 hX hyX hyT
    have hy1 : y = 1 := by
      have : y ∈ T ⊓ conjSubgroup g T := ⟨hyT', (mem_normIn.1 hy).1⟩
      rw [hcfg.inf, Subgroup.mem_bot] at this
      exact this
    subst hy1
    have hl' : l ∈ T ⊓ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) :=
      ⟨hlT, by simpa using hmC⟩
    rw [inf_centralizer_hSub_eq_bot hc hnat, Subgroup.mem_bot] at hl'
    simp [hl']
  have hSfix : ∀ s ∈ T ⊔ conjSubgroup g T, s ∈ Subgroup.normalizer (T : Set G) →
      c⁻¹ * (s * c * s⁻¹) ∈ cfgM T (conjSubgroup g T) → s * c * s⁻¹ = c := by
    intro s _ hsN hM'
    obtain ⟨hh, hhH, cs, hcsC, hsd⟩ := normalizer_eq_mul h62 h63 hc hnat ch hsN
    have hq : cs * c * cs⁻¹ ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hcsC hcC) (Subgroup.inv_mem _ hcsC)
    have hhq : hh * (cs * c * cs⁻¹) * hh⁻¹ = cs * c * cs⁻¹ := by
      have := Subgroup.mem_centralizer_iff.1 hq hh hhH
      rw [this]
      group
    have hsc : s * c * s⁻¹ = cs * c * cs⁻¹ := by
      rw [hsd]
      calc hh * cs * c * (hh * cs)⁻¹ = hh * (cs * c * cs⁻¹) * hh⁻¹ := by group
        _ = cs * c * cs⁻¹ := hhq
    have hC' : c⁻¹ * (s * c * s⁻¹) ∈
        Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) := by
      rw [hsc]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcC) hq
    have h1' := hMC _ hM' hC'
    calc s * c * s⁻¹ = c * (c⁻¹ * (s * c * s⁻¹)) := by group
      _ = c := by rw [h1', mul_one]
  have hcomm := centralizes_of_adj hS3 (le_refl 2) hX hcT hcT' hSfix
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact hcomm z (Subgroup.mem_sup_right hz)

theorem centralizer_hSub_le_centralizer_adj_eight (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n 1) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1) {k : ℕ}
    (ch : TransvChain n k) (hn : 3 ≤ n) {g : G} (hne : conjSubgroup g T ≠ T)
    (hbot : normIn T (conjSubgroup g T) ≠ ⊥)
    (hcard : Nat.card ↥(normIn T (conjSubgroup g T)) = Nat.card ↥(normIn T T₁)) {c : G}
    (hcC : c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) :
    c ∈ Subgroup.centralizer (conjSubgroup g T : Set G) := by
  classical
  have : Finite G := hc.finite
  have hTwc : IsWC T := hc.hy.pair.wc
  have hcfg : Cfg T (conjSubgroup g T) :=
    cfg_of_conj_conj hTwc ⟨1, (conjSubgroup_one T).symm⟩ ⟨g, rfl⟩ hne hbot
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ normIn (conjSubgroup g T) T, b ≠ 1 := by
    obtain ⟨⟨d, hd⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcfg.ne₁
    exact ⟨d, hd, fun h => hne1 (Subtype.ext h)⟩
  have hbT' : b ∈ conjSubgroup g T := (mem_normIn.1 hbB).1
  have hbN : b ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hbB).2
  have hbD : b ∈ normD T := mem_normD_of_mem_conjSubgroup hbT' hb1 hbN
  have hbT : b ∉ T := fun hbT => by
    have : b ∈ T ⊓ conjSubgroup g T := ⟨hbT, hbT'⟩
    rw [hcfg.inf, Subgroup.mem_bot] at this
    exact hb1 this
  have hcardb : Nat.card ↥(T ⊓ Subgroup.centralizer ({b} : Set G)) = Nat.card ↥(normIn T T₁) := by
    rw [hcfg.inf_centralizer_eq_normIn hbB hb1]
    exact hcard
  obtain ⟨ℓ₀, hℓ₀, hℓ₀1⟩ := exists_ne_one_mem_normIn hc
  obtain ⟨hℓD, hℓN, hℓT⟩ := mem_normD_of_mem_normIn hc hℓ₀ hℓ₀1
  have hcardℓ : Nat.card ↥(T ⊓ Subgroup.centralizer ({ℓ₀} : Set G)) =
      Nat.card ↥(normIn T T₁) := by
    rw [hc.sec3.cfg.inf_centralizer_eq_normIn hℓ₀ hℓ₀1]
  obtain ⟨g', hg', hbg'⟩ := sec67_conj_of_card h1 h62 h63 hc hnat ⟨hℓD, hℓN⟩ hℓT hbD
    hbT hcardℓ hcardb
  obtain ⟨h, hh, c', hc'C, hgh⟩ := normalizer_eq_mul h62 h63 hc hnat ch hg'
  have hℓH : ℓ₀ ∈ hSub T (normIn T₁ T) := le_hSub hℓ₀
  have hcomm : ℓ₀ * c' = c' * ℓ₀ := Subgroup.mem_centralizer_iff.1 hc'C ℓ₀ hℓH
  have hbh : b = h * ℓ₀ * h⁻¹ := by
    rw [hbg', hgh]
    calc h * c' * ℓ₀ * (h * c')⁻¹ = h * (c' * ℓ₀) * c'⁻¹ * h⁻¹ := by group
      _ = h * (ℓ₀ * c') * c'⁻¹ * h⁻¹ := by rw [hcomm]
      _ = h * ℓ₀ * h⁻¹ := by group
  obtain ⟨x₀, hx₀⟩ := hc.hy.pair.conj
  have hℓT₁ : ℓ₀ ∈ T₁ := (mem_normIn.1 hℓ₀).1
  have hbhx : b ∈ conjSubgroup (h * x₀) T := by
    rw [mem_conjSubgroup]
    have hℓ' : x₀⁻¹ * ℓ₀ * x₀ ∈ T := by
      have : ℓ₀ ∈ conjSubgroup x₀ T := hx₀ ▸ hℓT₁
      exact mem_conjSubgroup.1 this
    have e : (h * x₀)⁻¹ * b * (h * x₀) = x₀⁻¹ * ℓ₀ * x₀ := by rw [hbh]; group
    rw [e]
    exact hℓ'
  have hTT' : conjSubgroup g T = conjSubgroup (h * x₀) T :=
    conjSubgroup_eq_of_mem hTwc hbT' hbhx hb1
  have hcT₁ : c ∈ Subgroup.centralizer (T₁ : Set G) :=
    centralizer_hSub_le_centralizer_T₁ h1 h62 h63 hc hnat ch hn hcC
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [hTT'] at hz
  have hw : (h * x₀)⁻¹ * z * (h * x₀) ∈ T := mem_conjSubgroup.1 hz
  have ht₁ : x₀ * ((h * x₀)⁻¹ * z * (h * x₀)) * x₀⁻¹ ∈ T₁ := by
    rw [hx₀, mem_conjSubgroup]
    have e : x₀⁻¹ * (x₀ * ((h * x₀)⁻¹ * z * (h * x₀)) * x₀⁻¹) * x₀ =
        (h * x₀)⁻¹ * z * (h * x₀) := by group
    rw [e]
    exact hw
  have hz' : z = h * (x₀ * ((h * x₀)⁻¹ * z * (h * x₀)) * x₀⁻¹) * h⁻¹ := by group
  have hch : Commute c h := (Subgroup.mem_centralizer_iff.1 hcC h hh).symm
  have hct : Commute c (x₀ * ((h * x₀)⁻¹ * z * (h * x₀)) * x₀⁻¹) :=
    (Subgroup.mem_centralizer_iff.1 hcT₁ _ ht₁).symm
  have hcz : Commute c z := by
    rw [hz']
    exact (hch.mul_right hct).mul_right hch.inv_right
  exact hcz.eq.symm

theorem centralizer_hSub_le_centralizer_adj (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n 1) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1) {k : ℕ}
    (ch : TransvChain n k) (hn : 3 ≤ n) {g : G} (hne : conjSubgroup g T ≠ T)
    (hbot : normIn T (conjSubgroup g T) ≠ ⊥) {c : G}
    (hcC : c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) :
    c ∈ Subgroup.centralizer (conjSubgroup g T : Set G) := by
  classical
  have : Finite G := hc.finite
  have hTwc : IsWC T := hc.hy.pair.wc
  have hcfg : Cfg T (conjSubgroup g T) :=
    cfg_of_conj_conj hTwc ⟨1, (conjSubgroup_one T).symm⟩ ⟨g, rfl⟩ hne hbot
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ normIn (conjSubgroup g T) T, b ≠ 1 := by
    obtain ⟨⟨d, hd⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcfg.ne₁
    exact ⟨d, hd, fun h => hne1 (Subtype.ext h)⟩
  have hbT' : b ∈ conjSubgroup g T := (mem_normIn.1 hbB).1
  have hbN : b ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hbB).2
  have hbD : b ∈ normD T := mem_normD_of_mem_conjSubgroup hbT' hb1 hbN
  have hbT : b ∉ T := fun hbT => by
    have : b ∈ T ⊓ conjSubgroup g T := ⟨hbT, hbT'⟩
    rw [hcfg.inf, Subgroup.mem_bot] at this
    exact hb1 this
  have hcen : T ⊓ Subgroup.centralizer ({b} : Set G) = normIn T (conjSubgroup g T) :=
    hcfg.inf_centralizer_eq_normIn hbB hb1
  rcases h63 G T T₁ n 1 hc b hbD hbT with hcard | ⟨h16, -, h4⟩
  · rw [hcen] at hcard
    exact centralizer_hSub_le_centralizer_adj_eight h1 h62 h63 hc hnat ch hn hne hbot hcard hcC
  · rw [hcen] at h4
    exact centralizer_hSub_le_centralizer_adj_four h1 h62 h63 hc hnat ch hne hbot h16 h4 hcC

end CFSG.CGT.T75Q
