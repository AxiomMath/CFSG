module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma36
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma33
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma27Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6AutCent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma35

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

@[expose] def Lemma2_4_36_claim1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    A3A3K T M H S L s x z₁ z₂ K →
      ∀ r ∈ baum S ⊓ Subgroup.centralizer (K : Set G), r * r = 1 → r = 1 ∨ r = z₂

section Config

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s x z₁ z₂ : G} {K : Subgroup G}

theorem blockU2_le_blockU0 (hcfg : A3A3 T M H S L s)
    (hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L)) : blockU2 L s ≤ blockU0 S L := by
  rw [hcfg.blockU0_eq hU0]; exact le_sup_right

theorem A3A3K.exists_u_cases
    (h34 : Lemma2_4_34_used) (hK : A3A3K T M H S L s x z₁ z₂ K) :
    ∃ u ∈ blockU2 L s, u ∉ Subgroup.centralizer (K : Set G) ∧ u ∈ centralizerElem z₂ ∧
      ∀ t ∈ Subgroup.normalizer (K : Set G), (∀ l ∈ L, t * l = l * t) →
        (∀ k ∈ K, t * k = k * t) ∨ (∀ k ∈ K, t⁻¹ * k * t = u⁻¹ * k * u) := by
  obtain ⟨e₀⟩ := hK.nonempty_alt6 h34
  obtain ⟨u, huU, hu, huG, α, hα, hα2, hα1, hαL⟩ := hK.exists_alpha h34
  have hcard : Nat.card ↥(L.subgroupOf K) = 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.L_le_K).toEquiv]
    exact hK.isA4.card_L
  refine ⟨u, huU, hu, huG, fun t htN htL => ?_⟩
  obtain ⟨β, hβ⟩ := exists_conjAut htN
  have hβL : ∀ l ∈ L.subgroupOf K, β l = l := by
    intro l hl
    apply Subtype.ext
    rw [hβ]
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
    calc t⁻¹ * (l : G) * t = t⁻¹ * ((l : G) * t) := by group
      _ = t⁻¹ * (t * (l : G)) := by rw [(htL (l : G) hlL).symm]
      _ = (l : G) := by group
  rcases aut_eq_of_fixes_A4 e₀ α hα2 hα1 (L.subgroupOf K) hcard
      (fun l hl => hαL (l : G) (Subgroup.mem_subgroupOf.mp hl)) β hβL with h | h
  · left
    intro k hk
    have h1 := congrArg Subtype.val (DFunLike.congr_fun h ⟨k, hk⟩)
    rw [hβ] at h1
    have h2 : t⁻¹ * k * t = k := h1
    calc t * k = t * (t⁻¹ * k * t) := by rw [h2]
      _ = k * t := by group
  · right
    intro k hk
    have h1 := congrArg Subtype.val (DFunLike.congr_fun h ⟨k, hk⟩)
    rw [hβ, hα] at h1
    exact h1

theorem A3A3K.blockTC_eq_bot
    (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (h34 : Lemma2_4_34_used)
    (hclaim : ∀ r ∈ baum S ⊓ Subgroup.centralizer (K : Set G), r * r = 1 → r = 1 ∨ r = z₂)
    (hK : A3A3K T M H S L s x z₁ z₂ K) : blockTC T S L = ⊥ := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  obtain ⟨⟨hTCabel, hQ, hTCU, -⟩, -⟩ :=
    lemma2_4_27A3_part34 hD h27_1 hcs hK.a3 hK.conjJoin_ne
  obtain ⟨u, huU, hu, huG, hucases⟩ := hK.exists_u_cases h34
  have hU0 := hB.hU0
  have hU20 : blockU2 L s ≤ blockU0 S L := blockU2_le_blockU0 hK.toA3A3 hU0
  have hTCR : blockTC T S L ≤ baum S :=
    (le_sup_left.trans hQ.symm.le).trans hB.Q_le_R
  have hLle : L ≤ conjJoin S L := by rw [hK.join]; exact le_sup_left
  have hLsle : conjR L s ≤ conjJoin S L := by rw [hK.join]; exact le_sup_right
  have hz₂C : z₂ ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (hK.K_comp.1 hk)
  have hz₂U : z₂ ∈ blockU2 L s := hK.toA3A3x.z₂_mem.1
  have hu2 : u * u = 1 := by
    have := hK.isA4s.sq_U u huU
    rwa [pow_two] at this
  have hu1 : u ≠ 1 := fun h => hu (h ▸ one_mem _)
  rw [eq_bot_iff]
  intro t ht
  have htR : t ∈ baum S := hTCR ht
  have htG₂ : t ∈ centralizerElem z₂ := hK.toA3A3x.baum_le_cent₂ htR
  have htN : t ∈ Subgroup.normalizer (K : Set G) := hK.K_norm htG₂
  have htL0 : ∀ y ∈ conjJoin S L, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp ht.2 y hy).symm
  have ht2 : t * t = 1 := by
    have := hTCabel.2 t ht
    rwa [pow_two] at this
  have hbot : ∀ w ∈ blockU0 S L, w ∈ blockTC T S L → w = 1 := fun w hw hw' => by
    have : w ∈ blockTC T S L ⊓ blockU0 S L := ⟨hw', hw⟩
    rw [hTCU] at this
    exact Subgroup.mem_bot.mp this
  rcases hucases t htN (fun l hl => htL0 l (hLle hl)) with hcomm | hact
  ·
    have htC : t ∈ Subgroup.centralizer (K : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk => (hcomm k hk).symm
    rcases hclaim t ⟨htR, htC⟩ ht2 with h | h
    · rw [h]; exact one_mem _
    · exfalso
      exact hK.toA3A3x.z₂_ne (hbot z₂ (hU20 hz₂U) (h ▸ ht))
  ·
    have htu : t * u = u * t := htL0 u (hLsle (hK.isA4s.le huU))
    have hvC : t * u ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := hact k hk
      calc k * (t * u) = (t * u) * ((t * u)⁻¹ * k * (t * u)) := by group
        _ = (t * u) * (u⁻¹ * (t⁻¹ * k * t) * u) := by group
        _ = (t * u) * (u⁻¹ * (u⁻¹ * k * u) * u) := by rw [h1]
        _ = (t * u) * ((u * u)⁻¹ * k * (u * u)) := by group
        _ = (t * u) * k := by rw [hu2]; group
    have hUB : blockU L ≤ baum S := blockU_le_baum hcs hK.a3
    have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hK.s_mem
    have hU₂B : blockU2 L s ≤ baum S :=
      (C5.conjSubgroup_mono hUB s).trans (le_of_eq (C5.conjSubgroup_eq_self hsB))
    have hvR : t * u ∈ baum S := (baum S).mul_mem htR (hU₂B huU)
    have hv2 : (t * u) * (t * u) = 1 := by
      calc (t * u) * (t * u) = t * (u * t) * u := by group
        _ = t * (t * u) * u := by rw [← htu]
        _ = (t * t) * (u * u) := by group
        _ = 1 := by rw [ht2, hu2]; group
    have hz₂sq : z₂ * z₂ = 1 := by
      have := hK.toA3A3x.sq₂
      rwa [pow_two] at this
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    rcases hclaim (t * u) ⟨hvR, hvC⟩ hv2 with h | h
    · exfalso
      have htu' : t = u := by
        have : t = u⁻¹ := eq_inv_of_mul_eq_one_left h
        rw [this, huinv]
      have := hbot t (hU20 (htu' ▸ huU)) ht
      exact hu1 (htu' ▸ this)
    · exfalso
      have htz : t = z₂ * u := by
        calc t = (t * u) * u⁻¹ := by group
          _ = z₂ * u := by rw [h, huinv]
      have htU : t ∈ blockU2 L s := by
        rw [htz]; exact (blockU2 L s).mul_mem hz₂U huU
      have ht1 := hbot t (hU20 htU) ht
      have hzu : z₂ * u = 1 := by rw [← htz]; exact ht1
      have huz : u = z₂ := by
        have : u = z₂⁻¹ := eq_inv_of_mul_eq_one_right hzu
        rw [this]; exact inv_eq_of_mul_eq_one_right hz₂sq
      exact hu (huz ▸ hz₂C)

theorem A3A3K.card_baum_le (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hTC : blockTC T S L = ⊥) (hK : A3A3K T M H S L s x z₁ z₂ K) : Nat.card (baum S) ≤ 64 := by
  have hcs := hK.cs
  obtain ⟨-, -, -, h4, -⟩ := lemma2_4_30 hD h27_1 G T M H S L s hK.toA3A3
  obtain ⟨hsup, -, -, -, ⟨e⟩⟩ := h4 x hK.x_mem hK.x_not_mem
  have hDbot : blockD S L = ⊥ := by
    rw [eq_bot_iff, ← hTC]
    exact inf_le_inf_right _ hcs.le_T
  rw [hDbot, bot_sup_eq] at hsup
  have hle : baum S ≤ conjJoin S L ⊔ conjR (blockU0 S L) x :=
    (le_sup_left : baum S ≤ baum S ⊔ conjJoin S L).trans hsup.le
  have hdvd : Nat.card (baum S) ∣ 576 := by
    have h1 := Subgroup.card_dvd_of_le hle
    have h2 : Nat.card ↥(conjJoin S L ⊔ conjR (blockU0 S L) x) = 576 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_prod,
        Fintype.card_perm, Fintype.card_fin]
      decide
    rwa [h2] at h1
  obtain ⟨n, hn⟩ := (isPGroup_baum hcs).exists_card_eq
  rw [hn] at hdvd ⊢
  have hn6 : n ≤ 6 := by
    by_contra hcon
    have h4 : 2 ^ 7 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := h4.trans hdvd
    norm_num at this
  calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn6
    _ = 64 := by norm_num

theorem A3A3K.mem_rK_iff_conj (hK : A3A3K T M H S L s x z₁ z₂ K) {r : G} (hr : r ∈ baum S)
    (y : G) : y ∈ baum S ⊓ K ↔ r * y * r⁻¹ ∈ baum S ⊓ K := by
  have hrB : r ∈ normalizer (baum S : Set G) := Subgroup.le_normalizer hr
  have hrK : r ∈ normalizer (K : Set G) := hK.K_norm (hK.toA3A3x.baum_le_cent₂ hr)
  constructor
  · rintro ⟨hy1, hy2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hrB y).mp hy1,
      (Subgroup.mem_normalizer_iff.mp hrK y).mp hy2⟩
  · rintro ⟨hy1, hy2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hrB y).mpr hy1,
      (Subgroup.mem_normalizer_iff.mp hrK y).mpr hy2⟩

theorem A3A3K.mem_rKs_iff_conj (hK : A3A3K T M H S L s x z₁ z₂ K) {r : G} (hr : r ∈ baum S)
    (y : G) : y ∈ conjR (baum S ⊓ K) s ↔ r * y * r⁻¹ ∈ conjR (baum S ⊓ K) s := by
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hK.s_mem
  have hr' : s * r * s⁻¹ ∈ baum S := (Subgroup.mem_normalizer_iff.mp hsB r).mp hr
  rw [mem_conjR, mem_conjR]
  have e : s * (r * y * r⁻¹) * s⁻¹ = (s * r * s⁻¹) * (s * y * s⁻¹) * (s * r * s⁻¹)⁻¹ := by group
  rw [e]
  exact hK.mem_rK_iff_conj hr' (s * y * s⁻¹)

theorem dihedral4_center_unique : ∀ a b : DihedralGroup 4, (∀ f, f * a = a * f) →
    (∀ f, f * b = b * f) → a ≠ 1 → b ≠ 1 → a = b := by
  decide +kernel

theorem A3A3K.rK_inf_rKs
    (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (h34 : Lemma2_4_34_used)
    (hK : A3A3K T M H S L s x z₁ z₂ K) :
    baum S ⊓ K ⊓ conjR (baum S ⊓ K) s = ⊥ := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  obtain ⟨e₀⟩ := hK.nonempty_alt6 h34
  obtain ⟨e⟩ := hK.rK_dihedral hD h27_1 e₀
  by_contra hne
  have hS2 : IsPGroup 2 S := hcs.sylow.isPGroup
  have hss : s * s ∈ baum S := (s_mul_self_mem_baum hB hK.toA3A3).2
  have hNS : S ≤ normalizer ((baum S ⊓ K ⊓ conjR (baum S ⊓ K) s : Subgroup G) : Set G) := by
    refine hB.S_eq.le.trans (sup_le (fun r hr => ?_) (Subgroup.zpowers_le.mpr ?_))
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      exact and_congr (hK.mem_rK_iff_conj hr y) (hK.mem_rKs_iff_conj hr y)
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hy1, hy2⟩
        have h2 : s * y * s⁻¹ ∈ baum S ⊓ K := mem_conjR.mp hy2
        refine ⟨h2, mem_conjR.mpr ?_⟩
        have e1 : s * (s * y * s⁻¹) * s⁻¹ = (s * s) * y * (s * s)⁻¹ := by group
        rw [e1]
        exact (hK.mem_rK_iff_conj hss y).mp hy1
      · rintro ⟨hy1, hy2⟩
        have h2 : s * (s * y * s⁻¹) * s⁻¹ ∈ baum S ⊓ K := mem_conjR.mp hy2
        have e1 : s * (s * y * s⁻¹) * s⁻¹ = (s * s) * y * (s * s)⁻¹ := by group
        rw [e1] at h2
        exact ⟨(hK.mem_rK_iff_conj hss y).mpr h2, mem_conjR.mpr hy1⟩
  have hNle : baum S ⊓ K ⊓ conjR (baum S ⊓ K) s ≤ S :=
    (inf_le_left.trans (inf_le_left.trans inf_le_left))
  obtain ⟨z, hzN, hz1, hzc⟩ := exists_central_of_normal hne hNle hNS hS2
  have hzRK : z ∈ baum S ⊓ K := hzN.1
  have hz₁R : z₁ ∈ baum S ⊓ K :=
    ⟨blockU_le_baum hcs hK.a3 hK.toA3A3x.z₁_mem.1, hK.z₁_mem_K⟩
  have hRKS : baum S ⊓ K ≤ S := inf_le_left.trans inf_le_left
  have hzc' : ∀ f : ↥(baum S ⊓ K), f * ⟨z, hzRK⟩ = ⟨z, hzRK⟩ * f := fun f =>
    Subtype.ext (hzc (f : G) (hRKS f.2))
  have hz₁c' : ∀ f : ↥(baum S ⊓ K), f * ⟨z₁, hz₁R⟩ = ⟨z₁, hz₁R⟩ * f := fun f =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hK.toA3A3x.z₁_mem.2 (f : G) f.2.1)
  have hdz : ∀ f : DihedralGroup 4, f * e ⟨z, hzRK⟩ = e ⟨z, hzRK⟩ * f := fun f => by
    have := congrArg e (hzc' (e.symm f))
    simpa using this
  have hdz₁ : ∀ f : DihedralGroup 4, f * e ⟨z₁, hz₁R⟩ = e ⟨z₁, hz₁R⟩ * f := fun f => by
    have := congrArg e (hz₁c' (e.symm f))
    simpa using this
  have hd1 : e ⟨z, hzRK⟩ ≠ 1 := fun h => hz1 (by
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this)
  have hd₁1 : e ⟨z₁, hz₁R⟩ ≠ 1 := fun h => hK.z₁_ne (by
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this)
  have heq := dihedral4_center_unique _ _ hdz hdz₁ hd1 hd₁1
  have hzz₁ : z = z₁ := congrArg Subtype.val (e.injective heq)
  have hsz : s * z = z * s := hzc s hK.s_mem
  rw [hzz₁] at hsz
  have hz₂z₁ : z₂ = z₁ := by
    calc z₂ = s⁻¹ * z₁ * s := hK.z₂_def
      _ = s⁻¹ * (z₁ * s) := by group
      _ = s⁻¹ * (s * z₁) := by rw [hsz]
      _ = z₁ := by group
  exact hK.toA3A3x.z₁_ne_z₂ hz₂z₁.symm

theorem A3A3K.part_one
    (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (h34 : Lemma2_4_34_used)
    (hclaim : ∀ r ∈ baum S ⊓ Subgroup.centralizer (K : Set G), r * r = 1 → r = 1 ∨ r = z₂)
    (hK : A3A3K T M H S L s x z₁ z₂ K) :
    ((IsSylowTwoOf (baum S ⊓ K) K ∧ Nonempty (↥(baum S ⊓ K) ≃* DihedralGroup 4)) ∧
      baum S = (baum S ⊓ K) ⊔ conjR (baum S ⊓ K) s ∧
      (baum S ⊓ K) ⊓ conjR (baum S ⊓ K) s = ⊥ ∧
      ∀ a ∈ baum S ⊓ K, ∀ b ∈ conjR (baum S ⊓ K) s, a * b = b * a) ∧
      Nat.card (baum S) = 64 := by
  have hcs := hK.cs
  have hTC := hK.blockTC_eq_bot hD h27_1 h34 hclaim
  have hle64 := hK.card_baum_le hD h27_1 hTC
  obtain ⟨e₀⟩ := hK.nonempty_alt6 h34
  have hcard8 : Nat.card ↥(baum S ⊓ K) = 8 := (hK.rK_eq hD h27_1 e₀).2
  have hN := hK.rK_inf_rKs hD h27_1 h34
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hK.s_mem
  have hcards : Nat.card ↥(conjR (baum S ⊓ K) s) = 8 := by
    have : Nat.card ↥(conjR (baum S ⊓ K) s) = Nat.card ↥(baum S ⊓ K) :=
      Subgroup.card_map_of_injective (MulAut.conj s⁻¹).injective
    rw [this, hcard8]
  have hbR : ∀ b ∈ conjR (baum S ⊓ K) s, b ∈ baum S := by
    intro b hb
    have h1 : s * b * s⁻¹ ∈ baum S := (mem_conjR.mp hb).1
    have hsi : s⁻¹ ∈ normalizer (baum S : Set G) := (normalizer (baum S : Set G)).inv_mem hsB
    have := (Subgroup.mem_normalizer_iff.mp hsi (s * b * s⁻¹)).mp h1
    have e : s⁻¹ * (s * b * s⁻¹) * s⁻¹⁻¹ = b := by group
    rwa [e] at this
  let f : ↥(baum S ⊓ K) × ↥(conjR (baum S ⊓ K) s) → ↥(baum S) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), (baum S).mul_mem p.1.2.1 (hbR _ p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
    have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have hmem : (a' : G)⁻¹ * a ∈ baum S ⊓ K ⊓ conjR (baum S ⊓ K) s :=
      ⟨(baum S ⊓ K).mul_mem ((baum S ⊓ K).inv_mem a'.2) a.2,
        h2 ▸ (conjR (baum S ⊓ K) s).mul_mem b'.2 ((conjR (baum S ⊓ K) s).inv_mem b.2)⟩
    rw [hN] at hmem
    have h3 : (a' : G)⁻¹ * a = 1 := Subgroup.mem_bot.mp hmem
    have h4 : (a : G) = a' := by
      calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
        _ = a' := by rw [h3]; group
    have h5 : b' * (b : G)⁻¹ = 1 := by rw [← h2]; exact h3
    have h6 : (b : G) = b' := by
      calc (b : G) = (b' * (b : G)⁻¹)⁻¹ * b' := by group
        _ = b' := by rw [h5]; group
    exact Prod.ext (Subtype.ext h4) (Subtype.ext h6)
  have hcardprod : Nat.card (↥(baum S ⊓ K) × ↥(conjR (baum S ⊓ K) s)) = 64 := by
    rw [Nat.card_prod, hcard8, hcards]
  have hRge : 64 ≤ Nat.card (baum S) := by
    have := Nat.card_le_card_of_injective f hinj
    rwa [hcardprod] at this
  have hR64 : Nat.card (baum S) = 64 := le_antisymm hle64 hRge
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hcardprod, hR64])
  refine ⟨⟨⟨?_, hK.rK_dihedral hD h27_1 e₀⟩, ?_, hN, ?_⟩, hR64⟩
  ·
    have hKcard : Nat.card ↥K = 360 := (Nat.card_congr e₀.toEquiv).trans card_alt6'
    refine ⟨inf_le_right, (isPGroup_baum hcs).to_le inf_le_left, ?_⟩
    have h1 : Nat.card ↥((baum S ⊓ K).subgroupOf K) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : baum S ⊓ K ≤ K)).toEquiv]
      exact hcard8
    have h2 := Subgroup.index_mul_card ((baum S ⊓ K).subgroupOf K)
    rw [h1, hKcard] at h2
    omega
  ·
    refine le_antisymm (fun r hr => ?_) (sup_le inf_le_left fun b hb => hbR b hb)
    obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 ⟨r, hr⟩
    have : (a : G) * b = r := congrArg Subtype.val hab
    rw [← this]
    exact Subgroup.mul_mem_sup a.2 b.2
  ·
    intro a ha b hb
    have haR : a ∈ baum S := ha.1
    have hbR' : b ∈ baum S := hbR b hb
    have h1 : b * a⁻¹ * b⁻¹ ∈ baum S ⊓ K :=
      (hK.mem_rK_iff_conj hbR' a⁻¹).mp ((baum S ⊓ K).inv_mem ha)
    have h2 : a * b * a⁻¹ ∈ conjR (baum S ⊓ K) s := (hK.mem_rKs_iff_conj haR b).mp hb
    have hc1 : a * (b * a⁻¹ * b⁻¹) ∈ baum S ⊓ K := (baum S ⊓ K).mul_mem ha h1
    have hc2 : (a * b * a⁻¹) * b⁻¹ ∈ conjR (baum S ⊓ K) s :=
      (conjR (baum S ⊓ K) s).mul_mem h2 ((conjR (baum S ⊓ K) s).inv_mem hb)
    have e : a * (b * a⁻¹ * b⁻¹) = (a * b * a⁻¹) * b⁻¹ := by group
    have hmem : a * (b * a⁻¹ * b⁻¹) ∈ baum S ⊓ K ⊓ conjR (baum S ⊓ K) s :=
      ⟨hc1, e ▸ hc2⟩
    rw [hN] at hmem
    have h3 : a * (b * a⁻¹ * b⁻¹) = 1 := Subgroup.mem_bot.mp hmem
    calc a * b = (a * (b * a⁻¹ * b⁻¹)) * b * a := by group
      _ = b * a := by rw [h3]; group

end Config

end CFSG.QuasithinUnique.DoubleA3
