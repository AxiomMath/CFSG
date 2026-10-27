module

public import CFSG.CGT.T75H.LocalA
public import CFSG.CGT.T75H.D8Data

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem D8Data.toLocalCfg {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) (hc4 : Nat.card T = 4) {x₁ : G}
    (hx₁ : T₁ = conjSubgroup x₁ T) : LocalCfg T ℓ a b y x₁ where
  card_four := hc4
  ha := D.haT
  hb := D.hb
  hT := D.hT
  ha1 := D.ha1
  aa := D.aa
  ℓℓ := D.ℓℓ
  yy := D.yy
  comm_aℓ := D.comm_aℓ
  conj_ℓ_b := D.conj_ℓ_b
  conj_b_ℓ := D.conj_b_ℓ
  conj_a_y := D.conj_a_y
  hℓN := fun t ht => conj_mem_of_mem_normalizer D.hℓN ht
  hℓ := hx₁ ▸ D.hℓT₁
  hy := hx₁ ▸ D.hy
  haN := fun u hu => by
    have := conj_mem_of_mem_normalizer D.haN (show u ∈ T₁ from hx₁ ▸ hu)
    exact hx₁ ▸ this

theorem LocalCfg.subgroupOf {ℓ a b y x₁ : G} (C : LocalCfg T ℓ a b y x₁) (M : Subgroup G)
    (hTM : T ≤ M) (hℓ : ℓ ∈ M) (ha : a ∈ M) (hb : b ∈ M) (hy : y ∈ M) (hx₁ : x₁ ∈ M) :
    LocalCfg (T.subgroupOf M) ⟨ℓ, hℓ⟩ ⟨a, ha⟩ ⟨b, hb⟩ ⟨y, hy⟩ ⟨x₁, hx₁⟩ where
  card_four := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv]
    exact C.card_four
  ha := Subgroup.mem_subgroupOf.2 C.ha
  hb := Subgroup.mem_subgroupOf.2 C.hb
  hT := fun t ht => by
    rcases C.hT (t : G) (Subgroup.mem_subgroupOf.1 ht) with h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
  ha1 := fun h => C.ha1 (congrArg Subtype.val h)
  aa := Subtype.ext C.aa
  ℓℓ := Subtype.ext C.ℓℓ
  yy := Subtype.ext C.yy
  comm_aℓ := Subtype.ext C.comm_aℓ
  conj_ℓ_b := Subtype.ext C.conj_ℓ_b
  conj_b_ℓ := Subtype.ext C.conj_b_ℓ
  conj_a_y := Subtype.ext C.conj_a_y
  hℓN := fun t ht => Subgroup.mem_subgroupOf.2 (C.hℓN (t : G) (Subgroup.mem_subgroupOf.1 ht))
  hℓ := by
    rw [conjSubgroup_subgroupOf]
    exact Subgroup.mem_subgroupOf.2 C.hℓ
  hy := by
    rw [conjSubgroup_subgroupOf]
    exact Subgroup.mem_subgroupOf.2 C.hy
  haN := fun u hu => by
    rw [conjSubgroup_subgroupOf] at hu ⊢
    exact Subgroup.mem_subgroupOf.2 (C.haN (u : G) (Subgroup.mem_subgroupOf.1 hu))

theorem card_centralizer_lt [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a) {γ : G}
    (hγ1 : γ ≠ 1) : Nat.card (Subgroup.centralizer ({γ} : Set G)) < Nat.card G := by
  have hW : Subgroup.centralizer ({γ} : Set G) ≠ ⊤ := by
    intro htop
    have hmem : γ ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({γ} : Set G) := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 hg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h, Subgroup.mem_bot] at hmem
      exact hγ1 hmem
    · obtain ⟨a, b, hab⟩ := hna
      apply hab
      have := (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a
      exact this
  have hidx : (Subgroup.centralizer ({γ} : Set G)).index ≠ 1 := fun h =>
    hW (Subgroup.index_eq_one.1 h)
  have hmul := (Subgroup.centralizer ({γ} : Set G)).card_mul_index
  have hpos : 0 < Nat.card (Subgroup.centralizer ({γ} : Set G)) := Nat.card_pos
  have hidx2 : 2 ≤ (Subgroup.centralizer ({γ} : Set G)).index := by
    have : (Subgroup.centralizer ({γ} : Set G)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  nlinarith

theorem local_A_G [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    (hInd : SimpleCaseUpTo (Nat.card G)) (h215 : Lemma215Stmt) (hI : ListWCIdentification)
    (hc4 : Nat.card T = 4) {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) {γ : G} (hγ1 : γ ≠ 1)
    (hγT : ∀ t ∈ T, t * γ = γ * t) (hγT₁ : ∀ t ∈ T₁, t * γ = γ * t) {h : G}
    (hhγ : h * γ = γ * h) (hhT : ∀ t ∈ T, h * t = t * h) {q k : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) (hz : orderOf (ℓ * (h * ℓ * h⁻¹)) = q ^ k) : h * ℓ * h⁻¹ = ℓ := by
  classical
  set W : Subgroup G := Subgroup.centralizer ({γ} : Set G) with hW
  have hmemW : ∀ x : G, x * γ = γ * x → x ∈ W := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 hx
  have hTW : T ≤ W := fun t ht => hmemW t (hγT t ht)
  have hT₁W : T₁ ≤ W := fun t ht => hmemW t (hγT₁ t ht)
  have hhW : h ∈ W := hmemW h hhγ
  obtain ⟨x₁, hx₁S, hx₁⟩ := D.sec3.conj
  have hx₁W : x₁ ∈ W := (sup_le hTW hT₁W) hx₁S
  have hCG := D.toLocalCfg hc4 hx₁
  have hℓW : ℓ ∈ W := hT₁W D.hℓT₁
  have haW : a ∈ W := hTW D.haT
  have hbW : b ∈ W := hTW D.hb
  have hyW : y ∈ W := hT₁W D.hy
  have CW := hCG.subgroupOf W hTW hℓW haW hbW hyW hx₁W
  set TW : Subgroup W := T.subgroupOf W with hTWdef
  have hTWwc : IsWC TW := isWC_subgroupOf D.sec3.cfg.wc W hTW
  set K : Subgroup W := Subgroup.normalClosure (TW : Set W) with hK
  have hTK : TW ≤ K := Subgroup.le_normalClosure
  have hconjK : ∀ u : G, ∀ hu : u ∈ W, u ∈ T₁ → (⟨u, hu⟩ : W) ∈ K := by
    intro u hu huT₁
    have hmem : (⟨u, hu⟩ : W) ∈ conjSubgroup (⟨x₁, hx₁W⟩ : W) TW := by
      rw [hTWdef, conjSubgroup_subgroupOf]
      exact Subgroup.mem_subgroupOf.2 (hx₁ ▸ huT₁)
    exact conjSubgroup_le_normalClosure TW _ hmem
  have hℓK : (⟨ℓ, hℓW⟩ : W) ∈ K := hconjK ℓ hℓW D.hℓT₁
  have hyK : (⟨y, hyW⟩ : W) ∈ K := hconjK y hyW D.hy
  have haK : (⟨a, haW⟩ : W) ∈ K := hTK (Subgroup.mem_subgroupOf.2 D.haT)
  have hbK : (⟨b, hbW⟩ : W) ∈ K := hTK (Subgroup.mem_subgroupOf.2 D.hb)
  have hx₁K : (⟨x₁, hx₁W⟩ : W) ∈ K := by
    have hsup : T ⊔ T₁ ≤ K.map W.subtype := by
      refine sup_le (fun t ht => ?_) (fun t ht => ?_)
      · exact ⟨⟨t, hTW ht⟩, hTK (Subgroup.mem_subgroupOf.2 ht), rfl⟩
      · exact ⟨⟨t, hT₁W ht⟩, hconjK t (hT₁W ht) ht, rfl⟩
    obtain ⟨k', hk', hke⟩ := hsup hx₁S
    have : k' = ⟨x₁, hx₁W⟩ := Subtype.ext hke
    rwa [this] at hk'
  have CK := CW.subgroupOf K hTK hℓK haK hbK hyK hx₁K
  have hwcK : IsWC (TW.subgroupOf K) := isWC_subgroupOf_normalClosure hTWwc
  have hclK : Subgroup.normalClosure ((TW.subgroupOf K : Subgroup K) : Set K) = ⊤ :=
    normalClosure_subgroupOf_eq_top hTWwc
  have hKn : K.Normal := Subgroup.normalClosure_normal
  let φ : K ≃* K := (MulAut.conjNormal : W →* MulAut K) ⟨h, hhW⟩
  have hφ : ∀ x : K, ((φ x : K) : W) = ⟨h, hhW⟩ * (x : W) * ⟨h, hhW⟩⁻¹ := fun x =>
    MulAut.conjNormal_apply _ _
  have hφT : ∀ t ∈ TW.subgroupOf K, φ t = t := by
    intro t ht
    apply Subtype.ext
    rw [hφ]
    apply Subtype.ext
    have ht' : ((t : W) : G) ∈ T := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 ht)
    have := hhT _ ht'
    show h * ((t : W) : G) * h⁻¹ = ((t : W) : G)
    rw [this]; group
  have hn : Nat.card K < Nat.card G := by
    have h1 : Nat.card K ≤ Nat.card W := Nat.card_le_card_of_injective K.subtype K.subtype_injective
    exact lt_of_le_of_lt h1 (card_centralizer_lt hna hγ1)
  have hz' : orderOf ((⟨⟨ℓ, hℓW⟩, hℓK⟩ : K) * φ ⟨⟨ℓ, hℓW⟩, hℓK⟩) = q ^ k := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    convert hz using 2
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    show ℓ * (((φ ⟨⟨ℓ, hℓW⟩, hℓK⟩ : K) : W) : G) = ℓ * (h * ℓ * h⁻¹)
    rw [hφ]
    rfl
  have key := local_A hInd h215 hI hn hwcK hclK CK φ hφT hq hq5 hz'
  have := congrArg (fun x : K => ((x : W) : G)) key
  simpa [hφ] using this

end CFSG.CGT.T75H
