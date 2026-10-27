module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma73AuxN11

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isChevSimple_two_of_L62 {K : Subgroup G} (h : IsL62Type 3 K) : IsChevSimple 2 (PSimple 3 K) := by
  obtain ⟨⟨i, hi, hiso⟩, -⟩ := h
  refine Or.inl ⟨i, ?_, hiso⟩
  cases i with
  | lie j =>
    simp only [onLie] at hi ⊢
    rw [hi]
    simp [gfTwoPP]
  | cyclic _ _ => exact absurd hi (by simp [onLie])
  | alternating _ _ => exact absurd hi (by simp [onLie])
  | sporadic _ => exact absurd hi (by simp [onLie])

theorem le_normalizer_of_isDirectZpowersInf {B K : Subgroup G} {a : G} (hdir : IsDirectZpowersInf B a K)
    (hKa : K ≤ Subgroup.centralizer ({a} : Set G)) : B ≤ Subgroup.normalizer (K : Set G) := by
  have ha : a ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKa hk)
  rw [hdir.1]
  refine sup_le ?_ (inf_le_right.trans Subgroup.le_normalizer)
  rw [Subgroup.zpowers_le]
  exact Subgroup.centralizer_le_normalizer (K : Set G) ha

theorem isKGroup_of_component (hc : S6Ctx G 3) {a : G} (ha1 : a ≠ 1) {K : Subgroup G}
    (hK : GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) K) : CFSG.Open.IsKGroup ↥K := by
  refine isKGroup_of_isKProper hc.kProper ?_
  intro htop
  have := hK.1
  rw [htop] at this
  exact centralizer_ne_top_of_ne_one hc.simple hc.nonabelian ha1 (top_le_iff.1 this)

theorem l71_facts (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {y : G} {J : Subgroup G}
    (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L 11 y J) (hyB : y ∈ B) {a : G}
    {K T I Sg : Subgroup G} (D : Lemma73Data 3 B x L y J a K T I Sg) :
    IsPGroup 2 Sg ∧ I ≤ Subgroup.normalizer (T : Set G) ∧ I ≤ Subgroup.centralizer (altDxy x y : Set G) ∧
      Sg ≤ Subgroup.centralizer ({a} : Set G) ∧ I ≤ Subgroup.normalizer (Sg : Set G) ∧
      altDxy x y ≤ Subgroup.normalizer (Sg : Set G) ∧ B ≤ Subgroup.normalizer (Sg : Set G) ∧
      Sg ≤ ⁅Sg, I⁆ ∧ GenByPElts 3 I ∧ Sg ≤ Subgroup.normalizer (T : Set G) := by
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := (IsSStarMax.component hB).1
  have hxB : x ∈ B := (IsSStarMax.essential hB).1
  have hDB : altDxy x y ≤ B :=
    sup_le ((Subgroup.zpowers_le).2 hxB) ((Subgroup.zpowers_le).2 hyB)
  have hBD : B ≤ Subgroup.centralizer (altDxy x y : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 (fun d hd => isElemAbelian_commute (IsSStarMax.bmax hB).1 (hDB hd) hb)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (T : Set G) with hNdef
  set C := Subgroup.centralizer ({a} : Set G) ⊓ pCoreOf 2 N with hCdef
  have hgen : GenByPElts 3 I := by rw [D.I_eq]; exact genByPElts_layer hc.prime _
  have hIX : I ≤ N ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓ L := by
    rw [D.I_eq]
    exact sSup_le fun K hK => hK.1
  have hIN : I ≤ N := hIX.trans (inf_le_left.trans inf_le_left)
  have hID : I ≤ Subgroup.centralizer (altDxy x y : Set G) := hIX.trans (inf_le_left.trans inf_le_right)
  have hIa : I ≤ Subgroup.centralizer ({a} : Set G) :=
    hID.trans (Subgroup.centralizer_le (by simpa using D.a_mem))
  have hC2 : IsPGroup 2 C := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le inf_le_right
  have hIC : I ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_gLBConj_eq, hCdef, gLBConj_inf,
      mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_pCoreOf 2 N (hIN hg)),
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hIa hg))]
  have hSC : Sg ≤ C := by
    rw [D.S_eq, Subgroup.commutator_comm]
    exact commutator_le_left_of_normalizes hIC
  have hS2 : IsPGroup 2 Sg := hC2.to_le hSC
  have hSI : Sg ≤ ⁅Sg, I⁆ := by
    rw [D.S_eq]
    exact (le_commutator_of_genByPElts hc.prime hc.odd hC2 hIC hgen)
  have hIS : I ≤ Subgroup.normalizer (Sg : Set G) := by
    rw [D.S_eq]; exact le_normalizer_commutator Subgroup.le_normalizer hIC
  have hBS : B ≤ Subgroup.normalizer (Sg : Set G) :=
    D.S_eq ▸ l73_norm_S D.I_eq D.a_mem D.B_le_N (IsSStarMax.normalizes hB) hBD
  have hDS : altDxy x y ≤ Subgroup.normalizer (Sg : Set G) := by
    rw [D.S_eq]
    exact l73_norm_S D.I_eq D.a_mem (hDB.trans D.B_le_N) (altDxy_le_normalizer_L hxL S.y_mem)
      (fun d hd e he => isElemAbelian_commute S.isElemAbelian_D he hd)
  exact ⟨hS2, hIN, hID, hSC.trans inf_le_left, hIS, hDS, hBS, hSI, hgen,
    hSC.trans (inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 N))⟩

private theorem y5x_covers_of_imageMod_eq_top {p : ℕ} {L T : Subgroup G} (hT : T ≤ L)
    (h : imageMod p L T = ⊤) : CoversMod p T L := by
  unfold CoversMod
  refine le_antisymm (sup_le inf_le_right (primeCoreOf_le_self p L)) ?_
  intro l hl
  have hmem : (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : PQuot p L) ∈ imageMod p L T := by
    rw [h]
    exact Subgroup.mem_top _
  obtain ⟨⟨t, htL⟩, ht, hteq⟩ := Subgroup.mem_map.1 hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hteq
  have ho : t⁻¹ * l ∈ GLAPPrimeCoreOf p L := Subgroup.mem_map.2 ⟨_, hteq, rfl⟩
  have hl' : l = t * (t⁻¹ * l) := by group
  rw [hl']
  exact Subgroup.mul_mem_sup ⟨Subgroup.mem_subgroupOf.1 ht, htL⟩ ho

private theorem y5x_conj_mem_centralizer {S : Subgroup G} {m c : G} (hm : m ∈ Subgroup.normalizer (S : Set G))
    (hc : c ∈ Subgroup.centralizer (S : Set G)) : m * c * m⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
  refine Subgroup.mem_centralizer_iff.2 fun s hs => ?_
  have ht : m⁻¹ * s * m ∈ S := (Subgroup.mem_normalizer_iff.1 hm (m⁻¹ * s * m)).2 (by group; exact hs)
  have hct := Subgroup.mem_centralizer_iff.1 hc _ ht
  calc s * (m * c * m⁻¹) = m * ((m⁻¹ * s * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * s * m)) * m⁻¹ := by rw [hct]
    _ = (m * c * m⁻¹) * s := by group

private theorem y5x_map_eq_bot_of_simple {Γ Q : Type} [Group Γ] [Group Q] [Finite Γ] [Finite Q] [IsSimpleGroup Q]
    {W : Subgroup Γ} [W.Normal] (hW : Nat.Coprime 3 (Nat.card ↥W)) (f : Γ →* Q)
    (hf : Function.Surjective f) (h3 : 3 ∣ Nat.card Q) : W.map f = ⊥ := by
  haveI : (W.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.map f) with h | h
  · exact h
  · exfalso
    have hcard : Nat.card ↥(W.map f) = Nat.card Q := by
      rw [h, Subgroup.card_top]
    have h1 : 3 ∣ Nat.card ↥W := by
      have := Subgroup.card_map_dvd W f
      rw [hcard] at this
      exact h3.trans this
    have := Nat.Coprime.eq_one_of_dvd hW h1
    exact absurd this (by norm_num)

private theorem y5x_eq_one_of_two_group_pow {T : Subgroup G} (hT2 : IsPGroup 2 ↥T) {c : G} (hcT : c ∈ T)
    {N : ℕ} (hN : c ^ N = 1) (hcop : Nat.Coprime 2 N) : c = 1 := by
  obtain ⟨m, hm⟩ := hT2 ⟨c, hcT⟩
  have hc2 : c ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hcop' : Nat.Coprime (2 ^ m) N := Nat.Coprime.pow_left m hcop
  have h1 : orderOf c ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hc2
  have h2 : orderOf c ∣ N := orderOf_dvd_of_pow_eq_one hN
  have h3 : orderOf c ∣ Nat.gcd (2 ^ m) N := Nat.dvd_gcd h1 h2
  rw [hcop'.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

private theorem y5x_mem_sup_zpowers {K : Subgroup G} {a : G} (hKa : K ≤ Subgroup.centralizer ({a} : Set G)) {h : G}
    (hh : h ∈ K ⊔ Subgroup.zpowers a) : ∃ k ∈ K, ∃ j : ℤ, h = k * a ^ j := by
  have hcomm : ∀ k ∈ K, ∀ j : ℤ, k * a ^ j = a ^ j * k := fun k hk j =>
    (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hKa hk) : Commute k a) j).eq
  rw [Subgroup.sup_eq_closure] at hh
  induction hh using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · exact ⟨z, hz, 0, by simp⟩
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact ⟨1, K.one_mem, j, by simp⟩
  | one => exact ⟨1, K.one_mem, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k₁, hk₁, i, rfl⟩ := hx
    obtain ⟨k₂, hk₂, j, rfl⟩ := hy
    refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, i + j, ?_⟩
    have e : a ^ i * k₂ = k₂ * a ^ i := (hcomm k₂ hk₂ i).symm
    calc k₁ * a ^ i * (k₂ * a ^ j) = k₁ * (a ^ i * k₂) * a ^ j := by simp only [mul_assoc]
      _ = k₁ * (k₂ * a ^ i) * a ^ j := by rw [e]
      _ = (k₁ * k₂) * (a ^ i * a ^ j) := by simp only [mul_assoc]
      _ = (k₁ * k₂) * a ^ (i + j) := by rw [zpow_add]
  | inv x _ hx =>
    obtain ⟨k, hk, i, rfl⟩ := hx
    refine ⟨k⁻¹, K.inv_mem hk, -i, ?_⟩
    rw [mul_inv_rev, ← zpow_neg]
    exact (hcomm k⁻¹ (K.inv_mem hk) (-i)).symm

private theorem y5x_genByPElts_layer {p : ℕ} (hp : p.Prime) (X : Subgroup G) : GenByPElts p (GLAPLayer p X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Λ : Subgroup G := GLAPLayer p X with hΛ
  set S : Set G := {g : G | g ∈ Λ ∧ IsPGroup p (Subgroup.zpowers g)} with hS
  set N : Subgroup G := Subgroup.closure S with hN
  have hNΛ : N ≤ Λ := (Subgroup.closure_le Λ).2 fun g hg => hg.1
  have hconjS : ∀ x ∈ Λ, ∀ g ∈ S, x * g * x⁻¹ ∈ S := by
    intro x hx g hg
    refine ⟨Λ.mul_mem (Λ.mul_mem hx hg.1) (Λ.inv_mem hx), ?_⟩
    obtain ⟨m, hm⟩ := (isPGroup_zpowers_iff_exists_pow).1 hg.2
    refine (isPGroup_zpowers_iff_exists_pow).2 ⟨m, ?_⟩
    rw [conj_pow, hm, mul_one, mul_inv_cancel]
  have hNconj : ∀ x ∈ Λ, ∀ h ∈ N, x * h * x⁻¹ ∈ N := by
    intro x hx h hh
    rw [hN] at hh ⊢
    induction hh using Subgroup.closure_induction with
    | mem g hg => exact Subgroup.subset_closure (hconjS x hx g hg)
    | one => simp
    | mul a b _ _ ha hb =>
      have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  have hNnorm : (N.subgroupOf Λ).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNΛ).2 fun x hx => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hNconj x hx h, fun hh => ?_⟩
    have h2 := hNconj x⁻¹ (Λ.inv_mem hx) _ hh
    have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
    rwa [e] at h2
  have hidx : Nat.Coprime p (N.subgroupOf Λ).index := by
    obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥Λ))
    have hPN : (P : Subgroup ↥Λ) ≤ N.subgroupOf Λ := by
      intro x hx
      have hxp : IsPGroup p (Subgroup.zpowers x) := P.isPGroup'.to_le (Subgroup.zpowers_le.2 hx)
      obtain ⟨m, hm⟩ := (isPGroup_zpowers_iff_exists_pow).1 hxp
      have hm' : (x : G) ^ p ^ m = 1 := congrArg Subtype.val hm
      have hxG : IsPGroup p (Subgroup.zpowers (x : G)) := (isPGroup_zpowers_iff_exists_pow).2 ⟨m, hm'⟩
      exact Subgroup.subset_closure ⟨x.2, hxG⟩
    have h1 : (N.subgroupOf Λ).index ∣ (P : Subgroup ↥Λ).index := Subgroup.index_dvd_of_le hPN
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => Sylow.not_dvd_index P (hd.trans h1)
  have hEq : N = Λ := layer_isOPrimeResidual hp X N hNΛ hNnorm hidx
  unfold GenByPElts
  exact le_of_eq hEq.symm

private theorem y5x_exists_fixed {Γ α : Type} [Group Γ] [MulAction Γ α] [Finite α] (hΓ : IsPGroup 3 Γ)
    (h3 : ¬ 3 ∣ Nat.card α) : ∃ a : α, ∀ g : Γ, g • a = a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := hΓ.card_modEq_card_fixedPoints α
  have hne : Nat.card (MulAction.fixedPoints Γ α) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact h3 (Nat.modEq_zero_iff_dvd.1 hmod)
  obtain ⟨⟨a, ha⟩, -⟩ := Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hne)
  exact ⟨a, fun g => (MulAction.mem_fixedPoints).1 ha g⟩

private theorem y5x_two_eq_of_card {SW S W Q : Subgroup G} (hW : Odd (Nat.card ↥W))
    (hSW : Nat.card ↥SW = Nat.card ↥S * Nat.card ↥W) (hQ : Q ≤ SW) (hQ2 : IsPGroup 2 Q) (hSQ : S ≤ Q) :
    Q = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ2
  have hdvd : Nat.card ↥Q ∣ Nat.card ↥S * Nat.card ↥W := hSW ▸ Subgroup.card_dvd_of_le hQ
  rw [hn] at hdvd
  have hcop : Nat.Coprime (2 ^ n) (Nat.card ↥W) := Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hW)
  have h2 : 2 ^ n ∣ Nat.card ↥S := hcop.dvd_of_dvd_mul_right hdvd
  have hpos : 0 < Nat.card ↥S := Nat.card_pos
  have hle1 : 2 ^ n ≤ Nat.card ↥S := Nat.le_of_dvd hpos h2
  have hle2 : Nat.card ↥S ≤ Nat.card ↥Q := Subgroup.card_le_of_le hSQ
  exact (Subgroup.eq_of_le_of_card_ge hSQ (by rw [hn]; omega)).symm

private theorem y5x_frattini {A S M : Subgroup G} (hSA : S ≤ A) (hAM : A ≤ M)
    (hMN : M ≤ Subgroup.normalizer (A : Set G)) (hS : IsPGroup 2 S)
    (hmax : ∀ Q : Subgroup G, Q ≤ A → IsPGroup 2 Q → S ≤ Q → Q = S) (g : G) (hg : g ∈ M) :
    ∃ n ∈ M, ∃ h ∈ A, g = n * h ∧ n ∈ Subgroup.normalizer (S : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSM : S ≤ M := hSA.trans hAM
  let Mn : Subgroup ↥M := A.subgroupOf M
  haveI hMn : Mn.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAM).2 hMN
  let Pc : Subgroup ↥Mn := (S.subgroupOf M).subgroupOf Mn
  have hPc' : ∀ y : ↥Mn, y ∈ Pc ↔ ((y : ↥M) : G) ∈ S := fun y =>
    Subgroup.mem_subgroupOf.trans Subgroup.mem_subgroupOf
  have hPgroup : IsPGroup 2 ↥Pc := by
    intro y
    have hyS : ((((y : ↥Mn) : ↥M)) : G) ∈ S := (hPc' y.1).1 y.2
    obtain ⟨m, hm⟩ := hS ⟨_, hyS⟩
    refine ⟨m, Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩
    have h2 := congrArg Subtype.val hm
    simpa using h2
  have hPmax : ∀ {Q : Subgroup ↥Mn}, IsPGroup 2 ↥Q → Pc ≤ Q → Q = Pc := by
    intro Q hQ hle
    set Qg : Subgroup G := (Q.map Mn.subtype).map M.subtype with hQg
    have hQgA : Qg ≤ A := by
      rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact Subgroup.mem_subgroupOf.1 q.2
    have hQg2 : IsPGroup 2 ↥Qg := by
      intro x
      obtain ⟨_, ⟨q, hq, rfl⟩, hyx⟩ := Subgroup.mem_map.1 x.2
      obtain ⟨m, hm⟩ := hQ ⟨q, hq⟩
      refine ⟨m, Subtype.ext ?_⟩
      have hq1 : q ^ 2 ^ m = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      show (x : G) ^ 2 ^ m = 1
      rw [← hyx]
      have h2 := congrArg (fun z : ↥Mn => (((z : ↥M)) : G)) hq1
      simpa using h2
    have hSQg : S ≤ Qg := by
      intro s hs
      have hsM : s ∈ M := hSM hs
      have hsA : s ∈ A := hSA hs
      have hyQ : (⟨⟨s, hsM⟩, Subgroup.mem_subgroupOf.2 hsA⟩ : ↥Mn) ∈ Q :=
        hle ((hPc' _).2 hs)
      exact Subgroup.mem_map.2 ⟨_, Subgroup.mem_map.2 ⟨_, hyQ, rfl⟩, rfl⟩
    have hQgS : Qg = S := hmax Qg hQgA hQg2 hSQg
    refine Subgroup.ext fun q => ?_
    rw [hPc' q]
    constructor
    · intro hq
      rw [← hQgS]
      exact Subgroup.mem_map.2 ⟨_, Subgroup.mem_map.2 ⟨q, hq, rfl⟩, rfl⟩
    · intro hqS
      rw [← hQgS] at hqS
      obtain ⟨_, ⟨q', hq', rfl⟩, hq'eq⟩ := Subgroup.mem_map.1 hqS
      have hqq : q' = q := Subtype.ext (Subtype.ext hq'eq)
      rw [← hqq]
      exact hq'
  have hfr := Sylow.normalizer_sup_eq_top (⟨Pc, hPgroup, hPmax⟩ : Sylow 2 ↥Mn)
  have hgM : (⟨g, hg⟩ : ↥M) ∈ (⊤ : Subgroup ↥M) := Subgroup.mem_top _
  rw [← hfr] at hgM
  have hgM' : (⟨g, hg⟩ : ↥M) ∈ ((_ ⊔ Mn : Subgroup ↥M) : Set ↥M) := hgM
  rw [Subgroup.mul_normal] at hgM'
  obtain ⟨a, ha, b, hb, hab⟩ := hgM'
  have hnorm : ∀ c : ↥M, c ∈ Subgroup.normalizer ((Pc.map Mn.subtype : Subgroup ↥M) : Set ↥M) →
      ∀ x ∈ S, (c : G) * x * (c : G)⁻¹ ∈ S := by
    intro c hc x hx
    have hxM : x ∈ M := hSM hx
    have hxA : x ∈ A := hSA hx
    have hu : (⟨x, hxM⟩ : ↥M) ∈ (Pc.map Mn.subtype : Subgroup ↥M) := by
      refine Subgroup.mem_map.2 ⟨⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hxA⟩, (hPc' _).2 hx, rfl⟩
    obtain ⟨y, hyP, hy⟩ := Subgroup.mem_map.1 ((Subgroup.mem_normalizer_iff.1 hc _).1 hu)
    have hyS := (hPc' y).1 hyP
    have hyv : ((((y : ↥Mn) : ↥M)) : G) = (c : G) * x * (c : G)⁻¹ := by
      have := congrArg (fun z : ↥M => (z : G)) hy
      simpa using this
    rw [← hyv]
    exact hyS
  have hna : ((a : ↥M) : G) ∈ Subgroup.normalizer (S : Set G) := by
    refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => hnorm a ha x hx, fun hx => ?_⟩
    have h2 := hnorm a⁻¹ (Subgroup.inv_mem _ ha) _ hx
    have e : ((a⁻¹ : ↥M) : G) * (((a : ↥M) : G) * x * ((a : ↥M) : G)⁻¹) * ((a⁻¹ : ↥M) : G)⁻¹ = x := by
      simp only [Subgroup.coe_inv]
      group
    rwa [e] at h2
  refine ⟨((a : ↥M) : G), (a : ↥M).2, ((b : ↥M) : G), Subgroup.mem_subgroupOf.1 hb, ?_, hna⟩
  have := congrArg (fun z : ↥M => (z : G)) hab
  simpa using this.symm

private theorem y5x_primeCore_le (X : Subgroup G) : GLAPPrimeCoreOf 3 X ≤ X := fun x hx => by
  obtain ⟨g, _, rfl⟩ := Subgroup.mem_map.1 hx
  exact g.2

private theorem y5x_primeCore_coprime (X : Subgroup G) : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCoreOf 3 X)) := by
  rw [GLAPPrimeCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
  exact CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥X

private theorem y5x_sup_card {K Sg : Subgroup G} (hS2 : IsPGroup 2 Sg) (hodd : Odd (Nat.card ↥(GLAPPrimeCoreOf 3 K)))
    (hSgW : Sg ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 K : Subgroup G) : Set G)) :
    Nat.card ↥(Sg ⊔ GLAPPrimeCoreOf 3 K) = Nat.card ↥Sg * Nat.card ↥(GLAPPrimeCoreOf 3 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup G := GLAPPrimeCoreOf 3 K with hW
  have hWSg : W ⊓ Sg = ⊥ := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (hS2.to_le (inf_le_right : W ⊓ Sg ≤ Sg))
    have hdvd : Nat.card ↥(W ⊓ Sg) ∣ Nat.card ↥W := Subgroup.card_dvd_of_le inf_le_left
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ Nat.card ↥W := (dvd_pow_self 2 hk0).trans hdvd
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.1 hk
  have h := card_sup_mul_card_inf_of_le_normalizer (A := W) (B := Sg) hSgW
  rw [hWSg, Subgroup.card_bot, mul_one, sup_comm] at h
  rw [h, mul_comm]

theorem l71_maxRank (hc : S6Ctx G 3) (i106 : I106L62At G) {B : Subgroup G} {a : G} {K : Subgroup G}
    (hdir : IsDirectZpowersInf B a K) (hKa : K ≤ Subgroup.centralizer ({a} : Set G))
    (hL62 : IsL62Type 3 K) (hB : Nat.card ↥B = 3 ^ 4) : IsMaxRankIn 3 B (K ⊔ B) := by
  classical
  intro E hE hEel
  set H : Subgroup G := K ⊔ Subgroup.zpowers a with hHdef
  have hBH : B ≤ H := by
    have h1 : B ≤ Subgroup.zpowers a ⊔ (B ⊓ K) := le_of_eq hdir.1
    exact h1.trans (sup_le le_sup_right (inf_le_right.trans le_sup_left))
  have hEH : E ≤ H := hE.trans (sup_le le_sup_left hBH)
  have ha_cent : a ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKa hk)
  have hHN : H ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer
      (Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer (K : Set G) ha_cent))
  have hKH : K ≤ H := le_sup_left
  haveI hKn : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHN
  have hzH : Subgroup.zpowers a ≤ H := le_sup_right
  have haH : a ∈ H := hzH (Subgroup.mem_zpowers a)
  set π : ↥H →* ↥H ⧸ K.subgroupOf H := QuotientGroup.mk' (K.subgroupOf H) with hπ
  have hπK : ∀ (k : G) (hk : k ∈ K) (hkH : k ∈ H), π ⟨k, hkH⟩ = 1 := fun k hk hkH =>
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hk)
  set q0 : ↥H ⧸ K.subgroupOf H := π ⟨a, haH⟩ with hq0
  have hsurj : ∀ q : ↥H ⧸ K.subgroupOf H, ∃ n : ℤ, q0 ^ n = q := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, j, hkj⟩ := y5x_mem_sup_zpowers hKa h.2
    refine ⟨j, ?_⟩
    have hkH : k ∈ H := hKH hk
    have hhe : h = ⟨k, hkH⟩ * ⟨a, haH⟩ ^ j := Subtype.ext (by simp [hkj])
    have hpi : π h = q0 ^ j := by
      rw [hhe, map_mul, map_zpow, hπK k hk hkH, one_mul, hq0]
    exact hpi.symm
  haveI : IsCyclic (↥H ⧸ K.subgroupOf H) := ⟨⟨q0, hsurj⟩⟩
  set f : ↥E →* ↥H ⧸ K.subgroupOf H := π.comp (Subgroup.inclusion hEH) with hf
  have hrange : Nat.card f.range ≤ 3 := by
    have hexp : Monoid.exponent f.range ∣ 3 := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      rintro ⟨r, hr⟩
      obtain ⟨e, he⟩ := MonoidHom.mem_range.1 hr
      have he3 : e ^ 3 = 1 := Subtype.ext (hEel.2 e.1 e.2)
      apply Subtype.ext
      show r ^ 3 = 1
      rw [← he, ← map_pow, he3, map_one]
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by norm_num) hexp
  have hker : Nat.card f.ker ≤ 3 ^ 3 := by
    have hmap : Nat.card ↥(f.ker.map E.subtype) = Nat.card ↥f.ker :=
      Subgroup.card_map_of_injective Subtype.val_injective
    rw [← hmap]
    refine (i106 K hL62).1 _ ?_ (isElemAbelian_mono hEel (Subgroup.map_subtype_le _))
    rintro _ ⟨e, he, rfl⟩
    have h1 : (QuotientGroup.mk (⟨e.1, hEH e.2⟩ : ↥H) : ↥H ⧸ K.subgroupOf H) = 1 := by
      have h2 : f e = 1 := he
      exact h2
    have h3 : (⟨e.1, hEH e.2⟩ : ↥H) ∈ K.subgroupOf H := (QuotientGroup.eq_one_iff _).1 h1
    exact Subgroup.mem_subgroupOf.1 h3
  have hcardE : Nat.card ↥E = Nat.card f.range * Nat.card f.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
    exact h1
  rw [hB, hcardE]
  calc Nat.card f.range * Nat.card f.ker ≤ 3 * 3 ^ 3 := Nat.mul_le_mul hrange hker
    _ = 3 ^ 4 := by norm_num

theorem l71_core_odd (i61 : I61L62At) {X K : Subgroup G} (hK : GLAPComponent 3 X K) (hL62 : IsL62Type 3 K)
    (hodd : Odd (Nat.card ↥(⁅K, GLAPPrimeCoreOf 3 K⁆ : Subgroup G))) :
    Odd (Nat.card ↥(GLAPPrimeCoreOf 3 K)) := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  set W : Subgroup G := GLAPPrimeCoreOf 3 K with hW
  let W' : Subgroup ↥K := GLAPPrimeCore 3 ↥K
  haveI : W'.Normal := GLAPPrimeCore.normal 3 ↥K
  let N' : Subgroup ↥K := ⁅(⊤ : Subgroup ↥K), W'⁆
  haveI : N'.Normal := Subgroup.commutator_normal _ _
  have hN'W' : N' ≤ W' := by
    refine Subgroup.commutator_le.2 fun g _ w hw => ?_
    rw [commutatorElement_def]
    exact W'.mul_mem (Subgroup.Normal.conj_mem inferInstance w hw g) (W'.inv_mem hw)
  have hK_top : Subgroup.map K.subtype (⊤ : Subgroup ↥K) = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmapN : Subgroup.map K.subtype N' = ⁅K, W⁆ := by
    show Subgroup.map K.subtype ⁅(⊤ : Subgroup ↥K), W'⁆ = ⁅K, W⁆
    rw [Subgroup.map_commutator, hK_top]
    rfl
  have hperfK : (⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ : Subgroup ↥K) = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, hK_top, glaPComponent_perfect hK]
  have hZP : Subgroup.center (PQuot 3 K) = ⊥ := hL62.2
  let eP : PSimple 3 K ≃* PQuot 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hZP).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (PSimple 3 K) := (isQuasisimple_pQuot_of_glaPComponent hp hK).2
  haveI : IsSimpleGroup (PQuot 3 K) := eP.symm.isSimpleGroup
  haveI : Nontrivial (PQuot 3 K) := isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent hp hK)
  let Q := ↥K ⧸ N'
  let π₁ : Q →* PQuot 3 K := QuotientGroup.map N' W' (MonoidHom.id ↥K) hN'W'
  have hπ₁ : ∀ x : ↥K, π₁ (QuotientGroup.mk x) = QuotientGroup.mk x := fun x =>
    QuotientGroup.map_mk N' W' (MonoidHom.id ↥K) hN'W' x
  have hπs : Function.Surjective π₁ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk x, hπ₁ x⟩
  have hsurjQ : Function.Surjective (QuotientGroup.mk' N' : ↥K →* Q) := QuotientGroup.mk'_surjective N'
  have hcommQ : commutator Q = ⊤ := by
    rw [commutator_def]
    have := Subgroup.map_commutator (⊤ : Subgroup ↥K) (⊤ : Subgroup ↥K) (QuotientGroup.mk' N')
    rw [Subgroup.map_top_of_surjective _ hsurjQ, hperfK, Subgroup.map_top_of_surjective _ hsurjQ] at this
    exact this.symm
  haveI : Nontrivial Q := hπs.nontrivial
  have hA : π₁.ker ≤ Subgroup.center Q := by
    intro z hz
    obtain ⟨w, rfl⟩ := hsurjQ z
    have hw : w ∈ W' := by
      have h1 : π₁ (QuotientGroup.mk w : Q) = 1 := MonoidHom.mem_ker.1 hz
      rw [hπ₁ w] at h1
      exact (QuotientGroup.eq_one_iff w).1 h1
    refine Subgroup.mem_center_iff.2 fun q => ?_
    obtain ⟨g, rfl⟩ := hsurjQ q
    show (QuotientGroup.mk g : Q) * QuotientGroup.mk w = QuotientGroup.mk w * QuotientGroup.mk g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hm : ⁅g⁻¹, w⁻¹⁆ ∈ N' := Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (W'.inv_mem hw)
    have e : (g * w)⁻¹ * (w * g) = (⁅g⁻¹, w⁻¹⁆)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact N'.inv_mem hm
  have hB : Subgroup.center Q ≤ π₁.ker := by
    haveI hZm : ((Subgroup.center Q).map π₁).Normal := Subgroup.Normal.map inferInstance π₁ hπs
    intro z hz
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.center Q).map π₁) with h | h
    · rw [MonoidHom.mem_ker]
      have hzm : π₁ z ∈ (Subgroup.center Q).map π₁ := Subgroup.mem_map_of_mem π₁ hz
      rw [h, Subgroup.mem_bot] at hzm
      exact hzm
    · exfalso
      have hcen_top : (⊤ : Subgroup Q) ≤ Subgroup.center Q := by
        intro q _
        have hq : π₁ q ∈ (Subgroup.center Q).map π₁ := by
          rw [h]
          exact Subgroup.mem_top _
        obtain ⟨z', hz', hzq⟩ := Subgroup.mem_map.1 hq
        have hker : z'⁻¹ * q ∈ π₁.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hzq, inv_mul_cancel]
        have hq' : q = z' * (z'⁻¹ * q) := by group
        rw [hq']
        exact Subgroup.mul_mem _ hz' (hA hker)
      have hcomm_bot : (⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ : Subgroup Q) = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro q hq
        exact Subgroup.mem_centralizer_iff.2 fun h _ => Subgroup.mem_center_iff.1 (hcen_top hq) h
      rw [← commutator_def, hcommQ] at hcomm_bot
      obtain ⟨q, hq⟩ := exists_ne (1 : Q)
      exact hq (Subgroup.mem_bot.1 (hcomm_bot ▸ Subgroup.mem_top q))
  have hcen : Subgroup.center Q = π₁.ker := le_antisymm hB hA
  have hiso : Q ⧸ Subgroup.center Q ≃* PSimple 3 K :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientKerEquivOfSurjective π₁ hπs)).trans eP.symm
  have hcat : catalogIs (Q ⧸ Subgroup.center Q) (onLie fun d => d = TauCeti.LieTypeIndex.A 5 gfTwoPP) :=
    (catalogIs_congr hiso).2 hL62.1
  have hcard : Nat.card ↥(Subgroup.center Q) = 1 := i61 Q hcommQ hcat
  have hcenbot : Subgroup.center Q = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  have hkerbot : π₁.ker = ⊥ := by rw [← hcen]; exact hcenbot
  have hW'N' : W' ≤ N' := by
    intro w hw
    have h1 : π₁ (QuotientGroup.mk w : Q) = 1 := by
      rw [hπ₁ w]
      exact (QuotientGroup.eq_one_iff w).2 hw
    have h2 : (QuotientGroup.mk w : Q) ∈ π₁.ker := MonoidHom.mem_ker.2 h1
    rw [hkerbot, Subgroup.mem_bot] at h2
    exact (QuotientGroup.eq_one_iff w).1 h2
  have hWle : W ≤ ⁅K, W⁆ := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← hmapN]
    exact Subgroup.mem_map_of_mem _ (hW'N' hw)
  have hle2 : ⁅K, W⁆ ≤ W := by
    rw [← hmapN]
    exact Subgroup.map_mono hN'W'
  have hWeq : W = ⁅K, W⁆ := le_antisymm hWle hle2
  rw [hWeq]
  exact hodd

theorem mem_sup_of_commute {A C : Subgroup G} (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) {d : G}
    (hd : d ∈ A ⊔ C) : ∃ a ∈ A, ∃ c ∈ C, d = a * c := by
  rw [Subgroup.sup_eq_closure] at hd
  induction hd using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · exact ⟨z, hz, 1, C.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, z, hz, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, C.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a₁, ha₁, c₁, hc₁, rfl⟩ := hx
    obtain ⟨a₂, ha₂, c₂, hc₂, rfl⟩ := hy
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, c₁ * c₂, C.mul_mem hc₁ hc₂, ?_⟩
    have h := hAC a₂ ha₂ c₁ hc₁
    calc a₁ * c₁ * (a₂ * c₂) = a₁ * (c₁ * a₂) * c₂ := by group
      _ = a₁ * (a₂ * c₁) * c₂ := by rw [← h]
      _ = a₁ * a₂ * (c₁ * c₂) := by group
  | inv x _ hx =>
    obtain ⟨a, ha, c, hc, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, c⁻¹, C.inv_mem hc, ?_⟩
    have h := hAC a ha c hc
    calc (a * c)⁻¹ = c⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * c⁻¹ := by
        have : a⁻¹ * c⁻¹ = c⁻¹ * a⁻¹ := by
          calc a⁻¹ * c⁻¹ = (c * a)⁻¹ := by group
            _ = (a * c)⁻¹ := by rw [h]
            _ = c⁻¹ * a⁻¹ := by group
        exact this.symm

theorem l71_Do_card {B K D : Subgroup G} {a : G} (hBel : IsElemAbelian 3 B) (hdir : IsDirectZpowersInf B a K)
    (hDB : D ≤ B) (haD : a ∈ D) (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) (hD : Nat.card ↥D = 3 ^ 2) :
    Nat.card ↥(D ⊓ K : Subgroup G) = 3 ∧ D = Subgroup.zpowers a ⊔ (D ⊓ K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAD : Subgroup.zpowers a ≤ D := (Subgroup.zpowers_le).2 haD
  have hAB : Subgroup.zpowers a ≤ B := hAD.trans hDB
  have hsplit : D = Subgroup.zpowers a ⊔ (D ⊓ K) := by
    refine le_antisymm ?_ (sup_le hAD inf_le_left)
    intro d hd
    have hdB : d ∈ Subgroup.zpowers a ⊔ (B ⊓ K) := by rw [← hdir.1]; exact hDB hd
    obtain ⟨a', ha', c, hc, rfl⟩ := mem_sup_of_commute (A := Subgroup.zpowers a) (C := B ⊓ K)
      (fun a'' ha'' c' hc' => isElemAbelian_commute hBel (hAB ha'') hc'.1) hdB
    have hcD : c ∈ D := by
      have : c = a'⁻¹ * (a' * c) := by group
      rw [this]
      exact D.mul_mem (D.inv_mem (hAD ha')) hd
    exact Subgroup.mul_mem_sup ha' ⟨hcD, hc.2⟩
  refine ⟨?_, hsplit⟩
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hN : D ⊓ K ≤ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun d hd =>
      isElemAbelian_commute hBel (hAB hd) (hDB hg.1))
  have h1 := card_sup_mul_card_inf_of_le_normalizer hN
  have hinf : Subgroup.zpowers a ⊓ (D ⊓ K) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ Subgroup.zpowers a ⊓ (B ⊓ K) := ⟨hg.1, hDB hg.2.1, hg.2.2⟩
    rw [hdir.2] at this
    exact this
  rw [← hsplit, hinf, Subgroup.card_bot, Nat.card_zpowers, hao, hD] at h1
  omega

theorem l71_J_comp (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) {K : Subgroup G} (hJK : J ≤ K) :
    GLAPComponent 3 (K ⊓ Subgroup.centralizer (altDxy x y : Set G)) J := by
  have hJD := l72_pComponent_centralizer hc.prime hB S
  have hJC : J ≤ Subgroup.centralizer (altDxy x y : Set G) := hJD.1
  exact glaPComponent_of_le hc.prime hJD (le_inf hJK hJC) inf_le_right

theorem l71_frattini_cent {K Sg Dd : Subgroup G} (hDK : Dd ≤ Subgroup.normalizer (K : Set G))
    (hDS : Dd ≤ Subgroup.normalizer (Sg : Set G)) (hDel : IsElemAbelian 3 Dd) (hSK : Sg ≤ K)
    (hS2 : IsPGroup 2 Sg) (hodd : Odd (Nat.card ↥(GLAPPrimeCoreOf 3 K))) :
    imageMod 3 K (K ⊓ Subgroup.centralizer (Dd : Set G)) ⊓
        Subgroup.normalizer ((imageMod 3 K Sg : Subgroup (PQuot 3 K)) : Set (PQuot 3 K)) ≤
      imageMod 3 K (K ⊓ Subgroup.centralizer (Dd : Set G) ⊓ Subgroup.normalizer (Sg : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W : Subgroup G := GLAPPrimeCoreOf 3 K with hW
  have hWK : W ≤ K := y5x_primeCore_le K
  have hWcop : Nat.Coprime 3 (Nat.card ↥W) := y5x_primeCore_coprime K
  have hKN : K ≤ Subgroup.normalizer (W : Set G) := le_normalizer_glaPPrimeCoreOf 3 K
  have hDN : Dd ≤ Subgroup.normalizer (W : Set G) :=
    hDK.trans (CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_glaPPrimeCoreOf 3 K)
  have hSgW : Sg ≤ Subgroup.normalizer (W : Set G) := hSK.trans hKN
  have hWn : ∀ g ∈ K, ∀ w ∈ W, g * w * g⁻¹ ∈ W := fun g hg w hw =>
    (Subgroup.mem_normalizer_iff.1 (hKN hg) w).1 hw
  have hDW : ∀ d ∈ Dd, ∀ w ∈ W, d * w * d⁻¹ ∈ W := fun d hd w hw =>
    (Subgroup.mem_normalizer_iff.1 (hDN hd) w).1 hw
  set SW : Subgroup G := Sg ⊔ W with hSWdef
  have hSWK : SW ≤ K := sup_le hSK hWK
  have hSWcard : Nat.card ↥SW = Nat.card ↥Sg * Nat.card ↥W := y5x_sup_card hS2 hodd hSgW
  intro xb hxb
  obtain ⟨hx1, hx2⟩ := hxb
  obtain ⟨z0, hz0Z, hz0⟩ := Subgroup.mem_map.1 hx1
  have hz0Z' : (z0 : G) ∈ K ⊓ Subgroup.centralizer (Dd : Set G) := Subgroup.mem_subgroupOf.1 hz0Z
  have hzK : (z0 : G) ∈ K := hz0Z'.1
  have hzC : (z0 : G) ∈ Subgroup.centralizer (Dd : Set G) := hz0Z'.2
  have hgz : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) z0 : PQuot 3 K) ∈
      Subgroup.normalizer ((imageMod 3 K Sg : Subgroup (PQuot 3 K)) : Set (PQuot 3 K)) := by
    rw [hz0]
    exact hx2
  have hA1 : ∀ g : ↥K, (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) g : PQuot 3 K) ∈
      Subgroup.normalizer ((imageMod 3 K Sg : Subgroup (PQuot 3 K)) : Set (PQuot 3 K)) →
      ∀ s ∈ Sg, (g : G) * s * (g : G)⁻¹ ∈ SW := by
    intro g hg s hs
    have hsK : (⟨s, hSK hs⟩ : ↥K) ∈ Sg.subgroupOf K := Subgroup.mem_subgroupOf.2 hs
    have hmem : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨s, hSK hs⟩ : PQuot 3 K) ∈ imageMod 3 K Sg :=
      Subgroup.mem_map.2 ⟨_, hsK, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff.1 hg _).1 hmem
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 hconj
    have hte' : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) t : PQuot 3 K) =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) (g * ⟨s, hSK hs⟩ * g⁻¹) := by
      rw [hte, map_mul, map_mul, map_inv]
    have hq : t⁻¹ * (g * ⟨s, hSK hs⟩ * g⁻¹) ∈ GLAPPrimeCore 3 ↥K := (QuotientGroup.eq).1 hte'
    have hw : ((t⁻¹ * (g * ⟨s, hSK hs⟩ * g⁻¹) : ↥K) : G) ∈ W := Subgroup.mem_map.2 ⟨_, hq, rfl⟩
    have ht' : (t : G) ∈ Sg := Subgroup.mem_subgroupOf.1 ht
    have e : (g : G) * s * (g : G)⁻¹ = (t : G) * ((t⁻¹ * (g * ⟨s, hSK hs⟩ * g⁻¹) : ↥K) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact SW.mul_mem (Subgroup.mem_sup_left ht') (Subgroup.mem_sup_right hw)
  have hA3 : ∀ g : ↥K, (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) g : PQuot 3 K) ∈
      Subgroup.normalizer ((imageMod 3 K Sg : Subgroup (PQuot 3 K)) : Set (PQuot 3 K)) →
      ∀ h ∈ SW, (g : G) * h * (g : G)⁻¹ ∈ SW := by
    intro g hg h hh
    obtain ⟨s, hs, w, hw, rfl⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_mul_of_mem_sup_of_le_normalizer hSgW hh
    have h2 : (g : G) * w * (g : G)⁻¹ ∈ W := hWn g g.2 w hw
    have e : (g : G) * (s * w) * (g : G)⁻¹ = ((g : G) * s * (g : G)⁻¹) * ((g : G) * w * (g : G)⁻¹) := by
      group
    rw [e]
    exact SW.mul_mem (hA1 g hg s hs) (Subgroup.mem_sup_right h2)
  have hz_SW : (z0 : G) ∈ Subgroup.normalizer (SW : Set G) := by
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hA3 z0 hgz h hh, fun hh => ?_⟩
    have hinv : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) z0⁻¹ : PQuot 3 K) ∈
        Subgroup.normalizer ((imageMod 3 K Sg : Subgroup (PQuot 3 K)) : Set (PQuot 3 K)) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hgz
    have h2 := hA3 z0⁻¹ hinv _ hh
    have e : ((z0⁻¹ : ↥K) : G) * ((z0 : G) * h * (z0 : G)⁻¹) * ((z0⁻¹ : ↥K) : G)⁻¹ = h := by
      simp only [Subgroup.coe_inv]
      group
    rwa [e] at h2
  obtain ⟨n, hnM, h, hhSW, hzn, hnN⟩ := y5x_frattini (A := SW) (S := Sg) (M := K ⊓ Subgroup.normalizer (SW : Set G))
    le_sup_left (le_inf hSWK Subgroup.le_normalizer) inf_le_right hS2
    (fun Q hQ hQ2 hSQ => y5x_two_eq_of_card (SW := SW) (S := Sg) (W := W) hodd hSWcard hQ hQ2 hSQ)
    (z0 : G) ⟨hzK, hz_SW⟩
  obtain ⟨s, hs, w, hw, hhsw⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_mul_of_mem_sup_of_le_normalizer hSgW hhSW
  have hnK : n ∈ K := hnM.1
  have hzeq : (z0 : G) = n * s * w := by rw [hzn, hhsw, mul_assoc]
  have hsK : s ∈ K := hSK hs
  have hnsN : n * s ∈ K ⊓ Subgroup.normalizer (Sg : Set G) :=
    ⟨K.mul_mem hnK hsK, Subgroup.mul_mem _ hnN (Subgroup.le_normalizer hs)⟩
  let T : Subgroup G := (K ⊓ Subgroup.normalizer (Sg : Set G)) ⊓ W
  let Xs : Set G := {m | m ∈ K ⊓ Subgroup.normalizer (Sg : Set G) ∧ (z0 : G)⁻¹ * m ∈ W}
  have hXs_eq : Xs = (fun u : G => (n * s) * u) '' (T : Set G) := by
    ext m
    constructor
    · rintro ⟨⟨hmK, hmN⟩, hmz⟩
      refine ⟨(n * s)⁻¹ * m, ⟨⟨K.mul_mem (K.inv_mem hnsN.1) hmK,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hnsN.2) hmN⟩, ?_⟩, ?_⟩
      · have e : (n * s)⁻¹ * m = w * ((z0 : G)⁻¹ * m) := by
          rw [hzeq]
          group
        rw [e]
        exact W.mul_mem hw hmz
      · simp only
        group
    · rintro ⟨u, ⟨⟨huK, huN⟩, huW⟩, rfl⟩
      refine ⟨⟨K.mul_mem hnsN.1 huK, Subgroup.mul_mem _ hnsN.2 huN⟩, ?_⟩
      have e : (z0 : G)⁻¹ * ((n * s) * u) = w⁻¹ * u := by
        rw [hzeq]
        group
      rw [e]
      exact W.mul_mem (W.inv_mem hw) huW
  have hXs_card : Nat.card ↥Xs = Nat.card ↥T := by
    rw [Nat.card_coe_set_eq, hXs_eq, Set.ncard_image_of_injective _ (mul_right_injective (n * s)),
      ← Nat.card_coe_set_eq]
    rfl
  have hcopT : ¬ 3 ∣ Nat.card ↥T := by
    intro h3
    have hdvd : Nat.card ↥T ∣ Nat.card ↥W := Subgroup.card_dvd_of_le inf_le_right
    have := Nat.Coprime.eq_one_of_dvd hWcop (h3.trans hdvd)
    exact absurd this (by norm_num)
  have hXs_dd : ∀ d ∈ Dd, ∀ m ∈ Xs, d * m * d⁻¹ ∈ Xs := by
    intro d hd m hm
    obtain ⟨⟨hmK, hmN⟩, hmz⟩ := hm
    have hdz : d * (z0 : G) = (z0 : G) * d := Subgroup.mem_centralizer_iff.1 hzC d hd
    have hzd : (z0 : G)⁻¹ * d = d * (z0 : G)⁻¹ := by
      calc (z0 : G)⁻¹ * d = (z0 : G)⁻¹ * (d * z0) * (z0 : G)⁻¹ := by group
        _ = (z0 : G)⁻¹ * ((z0 : G) * d) * (z0 : G)⁻¹ := by rw [hdz]
        _ = d * (z0 : G)⁻¹ := by group
    refine ⟨⟨(Subgroup.mem_normalizer_iff.1 (hDK hd) m).1 hmK,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hDS hd) hmN) (Subgroup.inv_mem _ (hDS hd))⟩, ?_⟩
    have e : (z0 : G)⁻¹ * (d * m * d⁻¹) = d * ((z0 : G)⁻¹ * m) * d⁻¹ := by
      calc (z0 : G)⁻¹ * (d * m * d⁻¹) = ((z0 : G)⁻¹ * d) * m * d⁻¹ := by group
        _ = (d * (z0 : G)⁻¹) * m * d⁻¹ := by rw [hzd]
        _ = d * ((z0 : G)⁻¹ * m) * d⁻¹ := by group
    show (z0 : G)⁻¹ * (d * m * d⁻¹) ∈ W
    rw [e]
    exact hDW d hd _ hmz
  have hΓ : IsPGroup 3 ↥Dd := fun d => ⟨1, Subtype.ext (by simpa using hDel.2 d.1 d.2)⟩
  let act : MulAction ↥Dd ↥Xs :=
    { smul := fun d x => ⟨(d : G) * (x : G) * (d : G)⁻¹, hXs_dd d d.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by show (1 : G) * (x : G) * (1 : G)⁻¹ = x; group)
      mul_smul := fun a b x => Subtype.ext (by
        show ((a : G) * (b : G)) * (x : G) * ((a : G) * (b : G))⁻¹ =
          (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹
        group) }
  letI := act
  obtain ⟨a, ha⟩ := y5x_exists_fixed hΓ (by rw [hXs_card]; exact hcopT)
  have hfix : ∀ d ∈ Dd, d * a.1 * d⁻¹ = a.1 := fun d hd => congrArg Subtype.val (ha ⟨d, hd⟩)
  obtain ⟨⟨hxK, hxN⟩, hxz⟩ := a.2
  have hxC : a.1 ∈ Subgroup.centralizer (Dd : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun d hd => ?_
    calc d * a.1 = (d * a.1 * d⁻¹) * d := by group
      _ = a.1 * d := by rw [hfix d hd]
  refine Subgroup.mem_map.2 ⟨⟨a.1, hxK⟩, Subgroup.mem_subgroupOf.2 ⟨⟨hxK, hxC⟩, hxN⟩, ?_⟩
  rw [← hz0]
  have hq : ((z0⁻¹ * ⟨a.1, hxK⟩ : ↥K)) ∈ GLAPPrimeCore 3 ↥K := by
    obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.1 hxz
    have : q = z0⁻¹ * ⟨a.1, hxK⟩ := Subtype.ext hqe
    rw [← this]
    exact hq
  refine (QuotientGroup.eq).2 ?_
  have e : (⟨a.1, hxK⟩ : ↥K)⁻¹ * z0 = (z0⁻¹ * ⟨a.1, hxK⟩)⁻¹ := by group
  rw [e]
  exact (GLAPPrimeCore 3 ↥K).inv_mem hq

theorem l71_image_cover {K J Sg Dd : Subgroup G} (hDK : Dd ≤ Subgroup.normalizer (K : Set G))
    (hDS : Dd ≤ Subgroup.normalizer (Sg : Set G)) (hDel : IsElemAbelian 3 Dd) (hSK : Sg ≤ K)
    (hS2 : IsPGroup 2 Sg) (hodd : Odd (Nat.card ↥(GLAPPrimeCoreOf 3 K)))
    (hJ : GLAPLayer 3 (K ⊓ Subgroup.centralizer (Dd : Set G)) = J)
    (hnorm : imageMod 3 K J ≤ Subgroup.normalizer ((imageMod 3 K Sg : Subgroup (PQuot 3 K)) : Set (PQuot 3 K))) :
    imageMod 3 K J ≤ imageMod 3 K (GLAPLayer 3 (K ⊓ Subgroup.centralizer (Dd : Set G) ⊓
      Subgroup.normalizer (Sg : Set G))) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  set Z := K ⊓ Subgroup.centralizer (Dd : Set G) with hZ
  set Y := Z ⊓ Subgroup.normalizer (Sg : Set G) with hY
  have hZK : Z ≤ K := inf_le_left
  have hYZ : Y ≤ Z := inf_le_left
  have hYK : Y ≤ K := hYZ.trans hZK
  have hJim : imageMod 3 K J = GLAPLayer 3 (imageMod 3 K Z) := by
    rw [← hJ]; exact imageMod_glaPLayer hp hZK
  have hΛZ : GLAPLayer 3 (imageMod 3 K Z) ≤ imageMod 3 K Z := sSup_le fun M hM => hM.1
  have hΛN : GLAPLayer 3 (imageMod 3 K Z) ≤
      Subgroup.normalizer ((imageMod 3 K Sg : Subgroup (PQuot 3 K)) : Set (PQuot 3 K)) := by
    rw [← hJim]; exact hnorm
  have hΛY : GLAPLayer 3 (imageMod 3 K Z) ≤ imageMod 3 K Y := fun q hq =>
    l71_frattini_cent hDK hDS hDel hSK hS2 hodd ⟨hΛZ hq, hΛN hq⟩
  have h2 : GLAPLayer 3 (imageMod 3 K Z) ≤ GLAPLayer 3 (imageMod 3 K Y) :=
    glaPLayer_le_layer_of_le hp (imageMod_mono hYZ) hΛY
  rw [hJim, imageMod_glaPLayer hp hYK]
  exact h2

theorem l71_perfect_le_L_cent {x : G} {L P : Subgroup G} {n : ℕ} (hL : IsAltPType 3 L n) (hn : 7 < n)
    (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (hPx : P ≤ Subgroup.centralizer ({x} : Set G)) (hperf : ⁅P, P⁆ = P) :
    P ≤ L ⊔ (centModSubgroup 3 L ⊓ Subgroup.centralizer ({x} : Set G)) := by
  set C := centModSubgroup 3 L with hC
  have hCN : C ≤ Subgroup.normalizer (L : Set G) := fun g hg => (mem_centModSubgroup.1 hg).1
  intro g hg
  have hgM : g ∈ L ⊔ C := perfect_le_sup_centMod hL (by omega) hPN hperf hg
  obtain ⟨c, hc, l, hl, hgcl⟩ := exists_mul_of_mem_sup_of_le_normalizer hCN (by rwa [sup_comm] at hgM)
  have hcx : c ∈ Subgroup.centralizer ({x} : Set G) := by
    have hc' : c = g * l⁻¹ := by rw [hgcl]; group
    rw [hc']
    exact Subgroup.mul_mem _ (hPx hg) (Subgroup.inv_mem _ (hxL hl))
  have hlc : c * l * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hCN hc) l).1 hl
  have hg' : g = (c * l * c⁻¹) * c := by rw [hgcl]; group
  rw [hg']
  exact Subgroup.mul_mem_sup hlc ⟨hc, hcx⟩
@[expose] def cbarOf (X L : Subgroup G) : Subgroup (PQuot 3 X) :=
  Subgroup.centralizer ((imageMod 3 X L : Subgroup (PQuot 3 X)) : Set (PQuot 3 X))

theorem l71_cbar_layer (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) :
    CFSG.ComponentClassification.Layer.subgroup ↥(cbarOf (Subgroup.centralizer ({x} : Set G)) L) = ⊥ := by
  classical
  set X := Subgroup.centralizer ({x} : Set G) with hXdef
  set C := cbarOf X L with hCdef
  have hxL : L ≤ X := (IsSStarMax.component hB).1
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := l73_Cx_le_normalizer hc hB
  have hCn : C.Normal := by
    have hLn : (imageMod 3 X L).Normal := by
      have h1 : (L.subgroupOf X).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hxL).2 hXN
      exact Subgroup.Normal.map h1 _ (QuotientGroup.mk'_surjective _)
    rw [hCdef]
    unfold cbarOf
    exact Subgroup.normal_centralizer
  have hlay : GLAPLayer 3 X = L := sstarMax_layer_eq hc hB
  have hnone : ∀ K : Subgroup ↥C, ¬ IsComponentOf K ⊤ := by
    intro K hK
    have hK' : K ≤ ⊤ ∧ IsSubnormal K ⊤ ∧ CFSG.Open.IsQuasisimple ↥K := hK
    have hCtop : (⊤ : Subgroup ↥C).map C.subtype = C := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hCsn : IsSubnormal C ⊤ :=
      IsSubnormal.step le_top (Subgroup.Normal.subgroupOf hCn ⊤) (IsSubnormal.refl _)
    have hK'sn : IsSubnormal (K.map C.subtype) ⊤ := by
      have h1 := IsSubnormal.map C.subtype hK'.2.1
      rw [hCtop] at h1
      exact IsSubnormal.trans h1 hCsn
    have hK'q : CFSG.Open.IsQuasisimple ↥(K.map C.subtype) :=
      CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective K C.subtype Subtype.val_injective) hK'.2.2
    have hK'comp : IsComponentOf (K.map C.subtype) ⊤ := ⟨le_top, hK'sn, hK'q⟩
    obtain ⟨L', hL', hbar⟩ := exists_glaPComponent_barX_eq (p := 3) X hK'comp
    have hL'L : L' ≤ L := by
      have h1 : L' ≤ GLAPLayer 3 X := le_sSup hL'
      rwa [hlay] at h1
    have hK'C : K.map C.subtype ≤ C := by
      rintro _ ⟨k, -, rfl⟩
      exact k.2
    have hK'I : K.map C.subtype ≤ imageMod 3 X L := by
      rw [← hbar]
      exact Subgroup.map_mono (Subgroup.comap_mono hL'L)
    have hcomm : ∀ a ∈ K.map C.subtype, ∀ b ∈ K.map C.subtype, a * b = b * a := by
      intro a ha b hb
      have haC : a ∈ Subgroup.centralizer
          ((imageMod 3 X L : Subgroup (PQuot 3 X)) : Set (PQuot 3 X)) := hK'C ha
      exact (Subgroup.mem_centralizer_iff.1 haC b (hK'I hb)).symm
    have hinj : Function.Injective (C.subtype.comp K.subtype) :=
      Subtype.val_injective.comp Subtype.val_injective
    have hKc : ∀ a b : ↥K, a * b = b * a := by
      intro a b
      apply hinj
      have ha' := Subgroup.mem_map_of_mem C.subtype a.2
      have hb' := Subgroup.mem_map_of_mem C.subtype b.2
      simp only [MonoidHom.comp_apply, map_mul]
      exact hcomm _ ha' _ hb'
    have hbotK : commutator ↥K = ⊥ := by
      unfold commutator
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      exact Subgroup.mem_centralizer_iff.2 (fun h _ => hKc h a)
    have hq : commutator ↥K = ⊤ ∧ IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK'.2.2
    obtain ⟨htop, hsimp⟩ := hq
    rw [hbotK] at htop
    have hall : ∀ a : ↥K, a = 1 := by
      intro a
      have : a ∈ (⊥ : Subgroup ↥K) := by
        rw [htop]
        exact Subgroup.mem_top a
      exact Subgroup.mem_bot.1 this
    haveI hnt : Nontrivial ↥K :=
      Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    exact hab ((hall a).trans (hall b).symm)
  rw [CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
  have hempty : {component : Subgroup ↥C | IsComponentOf component ⊤} = ∅ := by
    ext K
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact hnone K
  rw [hempty, sSup_empty]

theorem l71_fitting_pGroup (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) :
    IsPGroup 3 ↥(CFSG.ComponentClassification.Fitting.subgroup ↥(cbarOf (Subgroup.centralizer ({x} : Set G)) L)) := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set X := Subgroup.centralizer ({x} : Set G) with hXdef
  set C := cbarOf X L with hCdef
  have hxL : L ≤ X := (IsSStarMax.component hB).1
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := l73_Cx_le_normalizer hc hB
  have hCn : C.Normal := by
    have hLn : (imageMod 3 X L).Normal := by
      have h1 : (L.subgroupOf X).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hxL).2 hXN
      exact Subgroup.Normal.map h1 _ (QuotientGroup.mk'_surjective _)
    rw [hCdef]
    unfold cbarOf
    exact Subgroup.normal_centralizer
  haveI hFc : (CFSG.ComponentClassification.Fitting.subgroup ↥C).Characteristic :=
    CFSG.ComponentClassification.Fitting.characteristic _
  haveI hF'n : ((CFSG.ComponentClassification.Fitting.subgroup ↥C).map C.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hFnil : Group.IsNilpotent ↥(CFSG.ComponentClassification.Fitting.subgroup ↥C) :=
    CFSG.fittingSubgroup_nilpotent
  haveI hF'nil : Group.IsNilpotent
      ↥((CFSG.ComponentClassification.Fitting.subgroup ↥C).map C.subtype) :=
    (Group.isNilpotent_congr
      (Subgroup.equivMapOfInjective _ C.subtype Subtype.val_injective)).1 hFnil
  have hF'le : (CFSG.ComponentClassification.Fitting.subgroup ↥C).map C.subtype ≤
      CFSG.fittingSubgroup (PQuot 3 X) :=
    CFSG.ComponentClassification.Fitting.maximal _
  have hO : CFSG.pPrimeCore 3 (PQuot 3 X) = ⊥ := pQuot_primeCore_eq_bot hp X
  have hpc : CFSG.fittingSubgroup (PQuot 3 X) = CFSG.pCore 3 (PQuot 3 X) :=
    CFSG.Fitting_eq_pcore (PQuot 3 X) 3 hO
  intro f
  have hmem : C.subtype f.1 ∈ CFSG.pCore 3 (PQuot 3 X) := by
    rw [← hpc]
    exact hF'le (Subgroup.mem_map_of_mem C.subtype f.2)
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 3) (G := PQuot 3 X) ⟨C.subtype f.1, hmem⟩
  refine ⟨k, ?_⟩
  have h2 : C.subtype (f.1 ^ 3 ^ k) = C.subtype 1 := by
    rw [map_pow, map_one]
    exact congrArg Subtype.val hk
  apply Subtype.ext
  exact Subtype.val_injective h2

private theorem y5x_index_ker_of_surj {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) : f.ker.index = Nat.card B := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv

private theorem y5x_lift_centMod {X L : Subgroup G} (hxL : L ≤ X)
    (hXN : X ≤ Subgroup.normalizer (L : Set G)) (hsn : IsSubnormal L X) (g : ↥X)
    (hg : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) g : PQuot 3 X) ∈ cbarOf X L) :
    CentMod 3 L (g : G) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  rw [centMod_iff, mem_centModSubgroup]
  refine ⟨hXN g.2, fun l hl => ?_⟩
  set l' : ↥X := ⟨l, hxL hl⟩ with hl'def
  have hmem : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) l' : PQuot 3 X) ∈ imageMod 3 X L :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hl)
  have hg' : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) g : PQuot 3 X) ∈
      Subgroup.centralizer ((imageMod 3 X L : Subgroup (PQuot 3 X)) : Set (PQuot 3 X)) := hg
  have hcomm : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) l' : PQuot 3 X) *
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) g =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) g * QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) l' :=
    (Subgroup.mem_centralizer_iff.1 hg') _ hmem
  have hker : ⁅l', g⁆ ∈ GLAPPrimeCore 3 ↥X := by
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⁅l', g⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 hcomm
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hX : ⁅(l : G), (g : G)⁆ ∈ GLAPPrimeCoreOf 3 X := ⟨⁅l', g⁆, hker, rfl⟩
  have hLc : ⁅(l : G), (g : G)⁆ ∈ L := by
    have e : ⁅(l : G), (g : G)⁆ = (l : G) * ((g : G) * (l : G) * (g : G)⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact L.mul_mem hl (L.inv_mem ((Subgroup.mem_normalizer_iff.1 (hXN g.2) l).1 hl))
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn]
  exact ⟨hLc, hX⟩

private theorem y5x_threeSub_gen {X L : Subgroup G} (hxL : L ≤ X)
    (hXN : X ≤ Subgroup.normalizer (L : Set G)) (hsn : IsSubnormal L X)
    (hcyc : CycModSylow 3 L) (P : Subgroup ↥(cbarOf X L)) (hP : IsPGroup 3 ↥P) :
    IsCyclic ↥P := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set P' : Subgroup (PQuot 3 X) := P.map (cbarOf X L).subtype with hP'def
  have hP'3 : IsPGroup 3 ↥P' := hP.map (cbarOf X L).subtype
  have hP'C : P' ≤ cbarOf X L := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  obtain ⟨k₀, hk₀⟩ : ∃ k : ℕ, Nat.card ↥P' ∣ 3 ^ k := isPGroup_iff_card_dvd_pow.1 hP'3
  set qX : ↥X →* PQuot 3 X := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hqX
  set Y : Subgroup ↥X := P'.comap qX with hYdef
  have hNY : GLAPPrimeCore 3 ↥X ≤ Y := by
    intro g hg
    have h1 : qX g = 1 := (QuotientGroup.eq_one_iff g).2 hg
    show qX g ∈ P'
    rw [h1]
    exact P'.one_mem
  set ψ : ↥Y →* ↥P' := (qX.comp Y.subtype).codRestrict P' (fun y => y.2) with hψdef
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨p, hp'⟩
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥X) p
    have huY : u ∈ Y := by
      show qX u ∈ P'
      rw [hqX, hu]
      exact hp'
    exact ⟨⟨u, huY⟩, Subtype.ext hu⟩
  have hψker : ψ.ker = (GLAPPrimeCore 3 ↥X).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcop : Nat.Coprime (Nat.card ↥ψ.ker) ψ.ker.index := by
    rw [y5x_index_ker_of_surj ψ hψsurj]
    have hNk : Nat.card ↥ψ.ker = Nat.card ↥(GLAPPrimeCore 3 ↥X) := by
      rw [hψker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv
    rw [hNk]
    exact Nat.Coprime.coprime_dvd_right hk₀
      (Nat.Coprime.pow_right _ (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥X)).symm)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hsup : ψ.ker ⊔ H = ⊤ := hH.sup_eq_top
  have hbot : ψ.ker ⊓ H = ⊥ := disjoint_iff.1 hH.disjoint
  set S₀ : Subgroup ↥X := H.map Y.subtype with hS₀def
  have hS₀Y : ∀ s ∈ S₀, s ∈ Y := by
    rintro _ ⟨h, -, rfl⟩
    exact h.2
  have hS₀p : IsPGroup 3 ↥S₀ := by
    intro s
    obtain ⟨h, hhH, hhs⟩ := Subgroup.mem_map.1 s.2
    obtain ⟨k, hk⟩ := hP'3 (ψ h)
    have hkerh : h ^ 3 ^ k ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hk
    have h1 : h ^ 3 ^ k = 1 := by
      have hmem : h ^ 3 ^ k ∈ ψ.ker ⊓ H := ⟨hkerh, H.pow_mem hhH _⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.1 hmem
    refine ⟨k, ?_⟩
    apply Subtype.ext
    have h2 : Y.subtype (h ^ 3 ^ k) = 1 := by rw [h1, map_one]
    rw [map_pow] at h2
    show (s : ↥X) ^ 3 ^ k = 1
    rw [← hhs]
    exact h2
  set S : Subgroup G := S₀.map X.subtype with hSdef
  have hSp : IsPGroup 3 ↥S := hS₀p.map X.subtype
  have hScent : ∀ g ∈ S, CentMod 3 L g := by
    rintro _ ⟨s, hs, rfl⟩
    have hqP : qX s ∈ P' := hS₀Y s hs
    exact y5x_lift_centMod hxL hXN hsn s (hP'C hqP)
  have hcycS : IsCyclic ↥S := hcyc S hScent hSp
  have hS₀cyc : IsCyclic ↥S₀ :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective S₀ X.subtype Subtype.val_injective)).2 hcycS
  set f : ↥S₀ →* ↥P' := (qX.comp S₀.subtype).codRestrict P' (fun s => hS₀Y s.1 s.2) with hfdef
  have hfsurj : Function.Surjective f := by
    rintro ⟨p, hp'⟩
    obtain ⟨u, hu⟩ := hψsurj ⟨p, hp'⟩
    have hu_top : u ∈ ψ.ker ⊔ H := by
      rw [hsup]
      exact Subgroup.mem_top u
    obtain ⟨n', hn', h, hh, hnh⟩ := Subgroup.mem_sup_of_normal_left.1 hu_top
    refine ⟨⟨Y.subtype h, Subgroup.mem_map_of_mem _ hh⟩, ?_⟩
    apply Subtype.ext
    show qX (h : ↥X) = p
    have hval : qX (u : ↥X) = p := congrArg Subtype.val hu
    have hnq : qX (n' : ↥X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hn')
    have hsplit : (u : ↥X) = (n' : ↥X) * (h : ↥X) := by
      rw [← hnh]
      rfl
    rw [← hval, hsplit, map_mul, hnq, one_mul]
  have hP'cyc : IsCyclic ↥P' := by
    haveI := hS₀cyc
    exact isCyclic_of_surjective f hfsurj
  exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective P (cbarOf X L).subtype
    Subtype.val_injective)).2 hP'cyc

theorem l71_threeSubgroup_cyclic (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J)
    (P : Subgroup ↥(cbarOf (Subgroup.centralizer ({x} : Set G)) L)) (hP : IsPGroup 3 ↥P) : IsCyclic ↥P := by
  exact y5x_threeSub_gen (IsSStarMax.component hB).1 (l73_Cx_le_normalizer hc hB)
    (IsSStarMax.component hB).2.1 (IsSStarMax.cycMod hB) P hP

theorem l71_cbar_solvable (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) :
    Group.IsSolvable ↥(cbarOf (Subgroup.centralizer ({x} : Set G)) L) := by
  set Γ := ↥(cbarOf (Subgroup.centralizer ({x} : Set G)) L) with hΓ
  have hLay := l71_cbar_layer hc hB S
  have hPg := l71_fitting_pGroup hc hB S
  have hcyc : IsCyclic ↥(CFSG.ComponentClassification.Fitting.subgroup Γ) :=
    l71_threeSubgroup_cyclic hc hB S _ hPg
  have hcent : Subgroup.centralizer ((CFSG.ComponentClassification.Fitting.subgroup Γ : Subgroup Γ) : Set Γ) ≤
      CFSG.ComponentClassification.Fitting.subgroup Γ := by
    have h := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le Γ
    rwa [CFSG.ComponentClassification.GeneralizedFitting.subgroup.eq_sup, hLay, sup_bot_eq] at h
  haveI : (CFSG.ComponentClassification.Fitting.subgroup Γ).Normal :=
    CFSG.ComponentClassification.Fitting.normal Γ
  haveI : IsCyclic ↥(CFSG.ComponentClassification.Fitting.subgroup Γ) := hcyc
  haveI hFs : Group.IsSolvable ↥(CFSG.ComponentClassification.Fitting.subgroup Γ) :=
    inferInstance
  haveI hAut : Group.IsSolvable (MulAut ↥(CFSG.ComponentClassification.Fitting.subgroup Γ)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (IsCyclic.mulAutMulEquiv ↥(CFSG.ComponentClassification.Fitting.subgroup Γ)).toMonoidHom)
      (IsCyclic.mulAutMulEquiv ↥(CFSG.ComponentClassification.Fitting.subgroup Γ)).injective
  refine solvable_of_ker_le_range (CFSG.ComponentClassification.Fitting.subgroup Γ).subtype
    (MulAut.conjNormal : Γ →* MulAut ↥(CFSG.ComponentClassification.Fitting.subgroup Γ)) ?_
  intro g hg
  have hg' : ∀ h ∈ CFSG.ComponentClassification.Fitting.subgroup Γ, h * g = g * h := by
    intro h hh
    have h1 : MulAut.conjNormal g = 1 := hg
    have h2 := congrArg (fun φ : MulAut ↥(CFSG.ComponentClassification.Fitting.subgroup Γ) =>
      ((φ ⟨h, hh⟩ : ↥(CFSG.ComponentClassification.Fitting.subgroup Γ)) : Γ)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    have : g * h = h * g := by
      calc g * h = (g * h * g⁻¹) * g := by group
        _ = h * g := by rw [h2]
    exact this.symm
  have hgF : g ∈ CFSG.ComponentClassification.Fitting.subgroup Γ :=
    hcent (Subgroup.mem_centralizer_iff.2 hg')
  exact ⟨⟨g, hgF⟩, rfl⟩

theorem imageMod_centMod_le_cbar (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hB : IsSStarMax 3 B x L) :
    imageMod 3 (Subgroup.centralizer ({x} : Set G))
        (centModSubgroup 3 L ⊓ Subgroup.centralizer ({x} : Set G)) ≤
      cbarOf (Subgroup.centralizer ({x} : Set G)) L := by
  set X := Subgroup.centralizer ({x} : Set G) with hXdef
  have hsn : IsSubnormal L X := (IsSStarMax.component hB).2.1
  have hOle : GLAPPrimeCoreOf 3 L ≤ GLAPPrimeCoreOf 3 X := glaPPrimeCoreOf_le_of_isSubnormal hc.prime hsn
  rintro _ ⟨g, hg, rfl⟩
  have hgC : (g : G) ∈ centModSubgroup 3 L := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hg)).1
  rw [cbarOf, Subgroup.mem_centralizer_iff]
  rintro _ ⟨l, hl, rfl⟩
  have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
  have hcomm := (mem_centModSubgroup.1 hgC).2 (l : G) hlL
  obtain ⟨w, hw, hwe⟩ := hOle hcomm
  have hw1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) w = 1 := (QuotientGroup.eq_one_iff _).2 hw
  have hwe' : w = l * g * l⁻¹ * g⁻¹ := Subtype.ext (by simpa [commutatorElement_def] using hwe)
  rw [hwe', map_mul, map_mul, map_mul, map_inv, map_inv] at hw1
  have h2 := mul_inv_eq_one.1 hw1
  exact (mul_inv_eq_iff_eq_mul.1 h2)

theorem l71_cent_solvable (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) :
    Group.IsSolvable ↥(imageMod 3 (Subgroup.centralizer ({x} : Set G))
      (centModSubgroup 3 L ⊓ Subgroup.centralizer ({x} : Set G))) := by
  haveI := l71_cbar_solvable hc hB S
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (imageMod_centMod_le_cbar hc hB))

theorem l71_layer_le_L (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) {Y : Subgroup G}
    (hY : Y ≤ Subgroup.centralizer ({x} : Set G)) : GLAPLayer 3 Y ≤ L := by
  have hp := hc.prime
  set X := Subgroup.centralizer ({x} : Set G) with hX
  set Λ := GLAPLayer 3 Y with hΛ
  have hΛX : Λ ≤ X := (sSup_le fun M hM => hM.1 : Λ ≤ Y).trans hY
  have hxL : L ≤ X := (IsSStarMax.component hB).1
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := l73_Cx_le_normalizer hc hB
  have hperf : ⁅Λ, Λ⁆ = Λ := layer_perfect Y
  have hgen : GenByPElts 3 Λ := genByPElts_layer hp Y
  have hA1 := l71_perfect_le_L_cent S.alt (by have := S.seven_lt; omega) hxL (hΛX.trans hXN) hΛX hperf
  have hsol := l71_cent_solvable hc hB S
  haveI hLn : (imageMod 3 X L).Normal := by
    have h1 : (L.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hxL).2 hXN
    exact Subgroup.Normal.map h1 _ (QuotientGroup.mk'_surjective _)
  have himg : imageMod 3 X Λ ≤ imageMod 3 X (GLAPLayer 3 X) := by
    rw [sstarMax_layer_eq hc hB]
    refine perfect_le_of_sup_solvable hsol (imageMod_perfect hΛX hperf) ?_
    rw [← imageMod_sup hxL inf_le_right]
    exact imageMod_mono hA1
  have := le_layer_of_imageMod_le hp (le_refl X) hΛX hgen himg
  rwa [sstarMax_layer_eq hc hB] at this

theorem l71_cover_of_image {K L J Sg Dd : Subgroup G} (hJK : J ≤ K)
    (hJ : GLAPLayer 3 (K ⊓ Subgroup.centralizer (Dd : Set G)) = J)
    (hker : J ⊓ GLAPPrimeCoreOf 3 K = GLAPPrimeCoreOf 3 J)
    (himg : imageMod 3 K J ≤ imageMod 3 K (GLAPLayer 3 (K ⊓ Subgroup.centralizer (Dd : Set G) ⊓
      Subgroup.normalizer (Sg : Set G))))
    (hYL : GLAPLayer 3 (K ⊓ Subgroup.centralizer (Dd : Set G) ⊓ Subgroup.normalizer (Sg : Set G)) ≤ L) :
    CoversMod 3 (Subgroup.normalizer (Sg : Set G) ⊓ L) J := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hlayer_le : ∀ X : Subgroup G, GLAPLayer 3 X ≤ X := fun X => sSup_le fun M hM => hM.1
  have hJZ : J ≤ K ⊓ Subgroup.centralizer (Dd : Set G) := hJ ▸ hlayer_le _
  have hJK' : J ≤ K := hJZ.trans inf_le_left
  have hJC : J ≤ Subgroup.centralizer (Dd : Set G) := hJZ.trans inf_le_right
  have hY₀ := hlayer_le (K ⊓ Subgroup.centralizer (Dd : Set G) ⊓ Subgroup.normalizer (Sg : Set G))
  have hY₀K : GLAPLayer 3 (K ⊓ Subgroup.centralizer (Dd : Set G) ⊓ Subgroup.normalizer (Sg : Set G)) ≤ K :=
    hY₀.trans (inf_le_left.trans inf_le_left)
  have hY₀C : GLAPLayer 3 (K ⊓ Subgroup.centralizer (Dd : Set G) ⊓ Subgroup.normalizer (Sg : Set G)) ≤
      Subgroup.centralizer (Dd : Set G) := hY₀.trans (inf_le_left.trans inf_le_right)
  have hY₀N : GLAPLayer 3 (K ⊓ Subgroup.centralizer (Dd : Set G) ⊓ Subgroup.normalizer (Sg : Set G)) ≤
      Subgroup.normalizer (Sg : Set G) := hY₀.trans inf_le_right
  have hJnorm : (J.subgroupOf (K ⊓ Subgroup.centralizer (Dd : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJZ).2
      (hJ ▸ CFSG.LocalAnalysis.GLTheoremA.L62.le_normalizer_glaPLayer 3 (K ⊓ Subgroup.centralizer (Dd : Set G)))
  have hO_coprime : ∀ X : Subgroup G, Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCoreOf 3 X)) := fun X => by
    rw [GLAPPrimeCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
    exact CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥X
  have hO_le : ∀ X : Subgroup G, GLAPPrimeCoreOf 3 X ≤ X := fun X x hx => by
    obtain ⟨g, _, rfl⟩ := Subgroup.mem_map.1 hx
    exact g.2
  have h3 : ∀ j ∈ J, IsPGroup 3 (Subgroup.zpowers j) →
      j ∈ ((Subgroup.normalizer (Sg : Set G) ⊓ L) ⊓ J) ⊔ GLAPPrimeCoreOf 3 J := by
    intro j hjJ hjp
    have hjK : j ∈ K := hJK' hjJ
    have hjC : j ∈ Subgroup.centralizer (Dd : Set G) := hJC hjJ
    let πK : ↥K →* PQuot 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)
    let jk : ↥K := ⟨j, hjK⟩
    have hmemq : πK jk ∈ imageMod 3 K J := Subgroup.mem_map.2 ⟨jk, Subgroup.mem_subgroupOf.2 hjJ, rfl⟩
    obtain ⟨yk, hyY, hyeq⟩ := Subgroup.mem_map.1 (himg hmemq)
    have hyY' : (yk : G) ∈ GLAPLayer 3 (K ⊓ Subgroup.centralizer (Dd : Set G) ⊓ Subgroup.normalizer (Sg : Set G)) :=
      Subgroup.mem_subgroupOf.1 hyY
    obtain ⟨c, hc⟩ := (isPGroup_zpowers_iff_exists_pow).1 hjp
    have hqc : (πK jk) ^ 3 ^ c = 1 := by
      rw [← map_pow]
      have : jk ^ 3 ^ c = 1 := Subtype.ext (by simpa using hc)
      rw [this, map_one]
    have hyeq' : πK yk = πK jk := hyeq
    obtain ⟨a, b, hb3, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos yk).ne' 3 (by norm_num)
    have hord_q : orderOf (πK yk) ∣ 3 ^ a * b := hab ▸ orderOf_map_dvd πK yk
    have hord_q3 : orderOf (πK yk) ∣ 3 ^ c := by
      rw [hyeq']
      exact orderOf_dvd_iff_pow_eq_one.2 hqc
    obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hord_q3
    have hcop : Nat.Coprime (3 ^ e) b :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb3)
    have hdvd : orderOf (πK yk) ∣ 3 ^ a := by
      rw [he] at hord_q ⊢
      exact hcop.dvd_of_dvd_mul_right hord_q
    have hqa : (πK yk) ^ 3 ^ a = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd
    have hcop2 : Nat.Coprime (3 ^ a) b :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb3)
    obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.2 hcop2
    have htb : t * (b : ℤ) = 1 + ((3 ^ a : ℕ) : ℤ) * (-s) := by linear_combination hst
    let y3k : ↥K := yk ^ (t * (b : ℤ))
    have hyk_ord : yk ^ (((3 ^ a * b : ℕ)) : ℤ) = 1 := by
      rw [← hab, zpow_natCast, pow_orderOf_eq_one]
    have hy3pow : y3k ^ 3 ^ a = 1 := by
      have h1 : y3k ^ 3 ^ a = yk ^ (((3 ^ a * b : ℕ) : ℤ) * t) := by
        show (yk ^ (t * (b : ℤ))) ^ 3 ^ a = _
        rw [← zpow_natCast, ← zpow_mul]
        congr 1
        push_cast
        ring
      rw [h1, zpow_mul, hyk_ord, one_zpow]
    have hy3q : πK y3k = πK jk := by
      rw [← hyeq', map_zpow, htb, zpow_add, zpow_mul, zpow_natCast, hqa, one_zpow, mul_one, zpow_one]
    have hy3Y : (y3k : G) ∈ GLAPLayer 3 (K ⊓ Subgroup.centralizer (Dd : Set G) ⊓ Subgroup.normalizer (Sg : Set G)) :=
      Subgroup.zpow_mem _ hyY' _
    have hy3K : (y3k : G) ∈ K := y3k.2
    have hy3C : (y3k : G) ∈ Subgroup.centralizer (Dd : Set G) := hY₀C hy3Y
    have hy3N : (y3k : G) ∈ Subgroup.normalizer (Sg : Set G) := hY₀N hy3Y
    have hy3L : (y3k : G) ∈ L := hYL hy3Y
    have hy3pow' : (y3k : G) ^ 3 ^ a = 1 := congrArg Subtype.val hy3pow
    have hoK : (y3k : G)⁻¹ * j ∈ K := K.mul_mem (K.inv_mem hy3K) hjK
    have hoC : (y3k : G)⁻¹ * j ∈ Subgroup.centralizer (Dd : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hy3C) hjC
    have hoO : (y3k : G)⁻¹ * j ∈ GLAPPrimeCoreOf 3 K := by
      have e1 : (⟨(y3k : G)⁻¹ * j, hoK⟩ : ↥K) = y3k⁻¹ * jk := Subtype.ext rfl
      have h1 : πK ⟨(y3k : G)⁻¹ * j, hoK⟩ = 1 := by
        rw [e1, map_mul, map_inv, hy3q, inv_mul_cancel]
      have h2 : (⟨(y3k : G)⁻¹ * j, hoK⟩ : ↥K) ∈ GLAPPrimeCore 3 ↥K := (QuotientGroup.eq_one_iff _).1 h1
      exact Subgroup.mem_map.2 ⟨_, h2, rfl⟩
    have hoN : ((y3k : G)⁻¹ * j) ^ Nat.card ↥(GLAPPrimeCoreOf 3 K) = 1 := by
      have h := pow_card_eq_one' (x := (⟨(y3k : G)⁻¹ * j, hoO⟩ : ↥(GLAPPrimeCoreOf 3 K)))
      exact congrArg Subtype.val h
    let Z : Subgroup G := K ⊓ Subgroup.centralizer (Dd : Set G)
    have hjinv : j⁻¹ ∈ J := J.inv_mem hjJ
    have hoinv : ((y3k : G)⁻¹ * j)⁻¹ = j⁻¹ * (y3k : G) := by group
    let zy : ↥Z := ⟨(y3k : G), ⟨hy3K, hy3C⟩⟩
    let zj : ↥Z := ⟨j⁻¹, ⟨K.inv_mem hjK, Subgroup.inv_mem _ hjC⟩⟩
    let zo : ↥Z := ⟨((y3k : G)⁻¹ * j)⁻¹, ⟨K.inv_mem hoK, Subgroup.inv_mem _ hoC⟩⟩
    have hzj : zj ∈ J.subgroupOf Z := Subgroup.mem_subgroupOf.2 hjinv
    have hzo : zo = zj * zy := Subtype.ext hoinv
    have hzy_pow : zy ^ 3 ^ a = 1 := Subtype.ext hy3pow'
    let mkZ : ↥Z →* ↥Z ⧸ J.subgroupOf Z := QuotientGroup.mk' (J.subgroupOf Z)
    have hzj1 : mkZ zj = 1 := (QuotientGroup.eq_one_iff zj).2 hzj
    have hmkz : mkZ zo = mkZ zy := by
      rw [hzo, map_mul, hzj1, one_mul]
    have hmkz_pow : mkZ (zo ^ 3 ^ a) = 1 := by
      rw [map_pow, hmkz, ← map_pow, hzy_pow, map_one]
    have hPJ : ((y3k : G)⁻¹ * j) ^ 3 ^ a ∈ J := by
      have h1 : zo ^ 3 ^ a ∈ J.subgroupOf Z := (QuotientGroup.eq_one_iff _).1 hmkz_pow
      have h2 : ((zo ^ 3 ^ a : ↥Z) : G) ∈ J := Subgroup.mem_subgroupOf.1 h1
      have h3' : ((zo ^ 3 ^ a : ↥Z) : G) = (((y3k : G)⁻¹ * j) ^ 3 ^ a)⁻¹ := by
        rw [Subgroup.coe_pow, inv_pow]
      rw [h3'] at h2
      exact (Subgroup.inv_mem_iff J).1 h2
    have hoJ' : (y3k : G)⁻¹ * j ∈ J := by
      have hcop3 : Nat.Coprime (3 ^ a) (Nat.card ↥(GLAPPrimeCoreOf 3 K)) :=
        Nat.Coprime.pow_left a (hO_coprime K)
      obtain ⟨s2, t2, hst2⟩ := Nat.isCoprime_iff_coprime.2 hcop3
      have hst2' : ((3 ^ a : ℕ) : ℤ) * s2 + (Nat.card ↥(GLAPPrimeCoreOf 3 K) : ℤ) * t2 = 1 := by
        linear_combination hst2
      have e1 : ((y3k : G)⁻¹ * j) ^ (((3 ^ a : ℕ) : ℤ) * s2 + (Nat.card ↥(GLAPPrimeCoreOf 3 K) : ℤ) * t2) =
          (y3k : G)⁻¹ * j := by
        rw [hst2', zpow_one]
      rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hoN, one_zpow, mul_one] at e1
      have h4 : (((y3k : G)⁻¹ * j) ^ 3 ^ a) ^ s2 ∈ J := J.zpow_mem hPJ s2
      rw [e1] at h4
      exact h4
    have hoJO : (y3k : G)⁻¹ * j ∈ GLAPPrimeCoreOf 3 J := by
      rw [← hker]
      exact ⟨hoJ', hoO⟩
    have hy3J : (y3k : G) ∈ J := by
      have e2 : (y3k : G) = j * ((y3k : G)⁻¹ * j)⁻¹ := by group
      rw [e2]
      exact J.mul_mem hjJ (J.inv_mem hoJ')
    have hjeq : j = (y3k : G) * ((y3k : G)⁻¹ * j) := by group
    rw [hjeq]
    exact Subgroup.mul_mem_sup ⟨⟨hy3N, hy3L⟩, hy3J⟩ hoJO
  have hgen : GenByPElts 3 J := hJ ▸ y5x_genByPElts_layer hp (K ⊓ Subgroup.centralizer (Dd : Set G))
  have hgen' : J ≤ Subgroup.closure {g : G | g ∈ J ∧ IsPGroup 3 (Subgroup.zpowers g)} := hgen
  have hJM : J ≤ ((Subgroup.normalizer (Sg : Set G) ⊓ L) ⊓ J) ⊔ GLAPPrimeCoreOf 3 J :=
    hgen'.trans ((Subgroup.closure_le _).2 fun g hg => h3 g hg.1 hg.2)
  unfold CoversMod
  exact le_antisymm (sup_le inf_le_right (hO_le J)) hJM

theorem l71_kernel_L {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    (S : AltSetup 3 B x L n y J) : GLAPPrimeCoreOf 3 J ≤ GLAPPrimeCoreOf 3 L := by
  classical
  have hJL : J ≤ L := S.J_comp.1.trans inf_le_left
  obtain ⟨e, hcyc, himg⟩ := S.cycle
  have hσ3 : (permOfMod 3 L n e y).support.card = 3 := card_support_eq_of_cycleType hcyc.2
  have hn7 : 7 < n := S.seven_lt
  have hF : (imageMod 3 L J).map e.toMonoidHom = altFix (permOfMod 3 L n e y) := by
    rw [himg, altFix_eq_fixingSubgroup]
  obtain ⟨eA⟩ := nonempty_altFix_equiv (permOfMod 3 L n e y) (m := n - 3) (by rw [hσ3])
  have hcardA : 5 ≤ n - 3 := by omega
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin (n - 3))) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hcardA)
  haveI : IsSimpleGroup ↥(altFix (permOfMod 3 L n e y)) := eA.isSimpleGroup
  let eF : ↥(imageMod 3 L J) ≃* ↥(altFix (permOfMod 3 L n e y)) :=
    (Subgroup.equivMapOfInjective _ _ e.injective).trans (MulEquiv.subgroupCongr hF)
  haveI : IsSimpleGroup ↥(imageMod 3 L J) := eF.isSimpleGroup
  have h3F : 3 ∣ Nat.card ↥(imageMod 3 L J) := by
    rw [Nat.card_congr eF.toEquiv, Nat.card_congr eA.toEquiv]
    exact p_dvd_card_alternatingGroup Nat.prime_three (by norm_num)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hmemF : ∀ j : ↥J, (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (Subgroup.inclusion hJL j) : PQuot 3 L) ∈
      imageMod 3 L J :=
    fun j => Subgroup.mem_map.2 ⟨Subgroup.inclusion hJL j, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
  let f0 : ↥J →* PQuot 3 L := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp (Subgroup.inclusion hJL)
  let φ : ↥J →* ↥(imageMod 3 L J) := f0.codRestrict (imageMod 3 L J) hmemF
  have hφsurj : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  haveI : (GLAPPrimeCore 3 ↥J).Normal := GLAPPrimeCore.normal 3 ↥J
  have hcopW : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥J)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥J
  have hWbot : (GLAPPrimeCore 3 ↥J).map φ = ⊥ := y5x_map_eq_bot_of_simple hcopW φ hφsurj h3F
  have hw : ∀ w ∈ GLAPPrimeCore 3 ↥J, (w : G) ∈ GLAPPrimeCoreOf 3 L := by
    intro w hw
    have h1 : φ w ∈ (GLAPPrimeCore 3 ↥J).map φ := Subgroup.mem_map.2 ⟨w, hw, rfl⟩
    rw [hWbot, Subgroup.mem_bot] at h1
    have h2 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (Subgroup.inclusion hJL w) : PQuot 3 L) = 1 :=
      congrArg Subtype.val h1
    have h3 : Subgroup.inclusion hJL w ∈ GLAPPrimeCore 3 ↥L := (QuotientGroup.eq_one_iff _).1 h2
    exact Subgroup.mem_map.2 ⟨_, h3, rfl⟩
  intro x hx
  obtain ⟨w, hw', rfl⟩ := Subgroup.mem_map.1 hx
  exact hw w hw'

theorem coversMod_trans {L T J M₀ : Subgroup G} (hcov : CoversMod 3 (T ⊔ J) L) (hTM : T ≤ M₀) (hTL : T ≤ L)
    (hJL : J ≤ L) (hJM : CoversMod 3 M₀ J) (hkerL : GLAPPrimeCoreOf 3 J ≤ GLAPPrimeCoreOf 3 L) :
    CoversMod 3 M₀ L := by
  unfold CoversMod at hcov hJM ⊢
  have hTJ : T ⊔ J ≤ (M₀ ⊓ L) ⊔ GLAPPrimeCoreOf 3 L := by
    refine sup_le (le_sup_of_le_left (le_inf hTM hTL)) ?_
    calc J = (M₀ ⊓ J) ⊔ GLAPPrimeCoreOf 3 J := hJM.symm
      _ ≤ (M₀ ⊓ L) ⊔ GLAPPrimeCoreOf 3 L := sup_le_sup (inf_le_inf_left _ hJL) hkerL
  refine le_antisymm (sup_le inf_le_right (primeCoreOf_le_self 3 L)) ?_
  calc L = ((T ⊔ J) ⊓ L) ⊔ GLAPPrimeCoreOf 3 L := hcov.symm
    _ ≤ (M₀ ⊓ L) ⊔ GLAPPrimeCoreOf 3 L := sup_le (inf_le_left.trans hTJ) le_sup_right

theorem l71_cover_M_o {L T Sg : Subgroup G} {n : ℕ} (hn : 5 ≤ n) (hL : IsAltPType 3 L n) (hTL : T ≤ L)
    (hT : T ≤ Subgroup.centralizer (Sg : Set G)) (hTn : ¬ T ≤ GLAPPrimeCoreOf 3 L)
    (hcov : CoversMod 3 (Subgroup.normalizer (Sg : Set G) ⊓ L) L) :
    CoversMod 3 (Subgroup.centralizer (Sg : Set G) ⊓ L) L := by
  classical
  set N : Subgroup G := Subgroup.normalizer (Sg : Set G) with hN
  set C : Subgroup G := Subgroup.centralizer (Sg : Set G) with hC
  set O : Subgroup G := GLAPPrimeCoreOf 3 L with hO
  have hcov' : (N ⊓ L) ⊔ O = L := by
    have h := hcov
    unfold CoversMod at h
    rwa [inf_eq_left.2 (inf_le_right : N ⊓ L ≤ L)] at h
  have hAn : imageMod 3 L (N ⊓ L) = ⊤ := imageMod_eq_top_of_sup inf_le_right hcov'
  obtain ⟨e⟩ := hL
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
  haveI : IsSimpleGroup (PQuot 3 L) := e.isSimpleGroup
  obtain ⟨t, htT, htO⟩ : ∃ t ∈ T, t ∉ O := by
    by_contra hcon
    apply hTn
    intro t ht
    by_contra htO
    exact hcon ⟨t, ht, htO⟩
  have hAcN : (imageMod 3 L (C ⊓ L)).Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 ha
    have hg : g ∈ imageMod 3 L (N ⊓ L) := hAn ▸ Subgroup.mem_top g
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hg
    have hmul : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) m * QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) c *
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) m)⁻¹ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (m * c * m⁻¹) := by
      simp only [map_mul, map_inv]
    rw [hmul]
    have hmN : (m : G) ∈ N := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hm)).1
    have hcC : (c : G) ∈ C := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hc)).1
    refine Subgroup.mem_map.2 ⟨m * c * m⁻¹, Subgroup.mem_subgroupOf.2 ⟨?_, (m * c * m⁻¹).2⟩, rfl⟩
    exact y5x_conj_mem_centralizer hmN hcC
  have hAc_ne : imageMod 3 L (C ⊓ L) ≠ ⊥ := by
    intro hbot
    have htL : t ∈ L := hTL htT
    have hmem : (QuotientGroup.mk (⟨t, htL⟩ : ↥L) : PQuot 3 L) ∈ imageMod 3 L (C ⊓ L) :=
      Subgroup.mem_map.2 ⟨⟨t, htL⟩, Subgroup.mem_subgroupOf.2 ⟨hT htT, htL⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact htO (Subgroup.mem_map.2 ⟨⟨t, htL⟩, hmem, rfl⟩)
  haveI := hAcN
  have hAc_top : imageMod 3 L (C ⊓ L) = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hAc_ne
  exact y5x_covers_of_imageMod_eq_top inf_le_right hAc_top

theorem l71_I_le_M_o {L I Sg : Subgroup G} (hcov : CoversMod 3 (Subgroup.centralizer (Sg : Set G) ⊓ L) L)
    (hIL : I ≤ L) (hIS : I ≤ Subgroup.normalizer (Sg : Set G)) (hgen : GenByPElts 3 I) :
    I ≤ Subgroup.centralizer (Sg : Set G) := by
  classical
  set C : Subgroup G := Subgroup.centralizer (Sg : Set G) with hC
  set O : Subgroup G := GLAPPrimeCoreOf 3 L with hO
  have hcopO : Nat.Coprime 3 (Nat.card ↥O) := by
    rw [hO, GLAPPrimeCoreOf, Subgroup.card_map_of_injective L.subtype_injective]
    exact CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥L
  have hOL : L ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 L
  have hdec : ∀ g ∈ L, ∃ c ∈ C, ∃ o ∈ O, g = c * o := by
    intro g hg
    have hg' : g ∈ ((C ⊓ L) ⊓ L) ⊔ O := by
      have h := hcov
      unfold CoversMod at h
      rw [h]
      exact hg
    obtain ⟨c, hc, o, ho, hco⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (A := (C ⊓ L) ⊓ L) (N := O) (inf_le_right.trans hOL) hg'
    exact ⟨c, hc.1.1, o, ho, hco⟩
  refine hgen.trans ((Subgroup.closure_le _).2 ?_)
  rintro g ⟨hgI, hgp⟩
  obtain ⟨k, hk⟩ := (isPGroup_zpowers_iff_exists_pow).1 hgp
  obtain ⟨c, hcC, o, hoO, hgco⟩ := hdec g (hIL hgI)
  have hoN : o ∈ Subgroup.normalizer (Sg : Set G) := by
    have hco : o = c⁻¹ * g := by rw [hgco]; group
    rw [hco]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hcC)) (hIS hgI)
  have hconj : ∀ s ∈ Sg, g * s * g⁻¹ = o * s * o⁻¹ := by
    intro s hs
    have hos : o * s * o⁻¹ ∈ Sg := (Subgroup.mem_normalizer_iff.1 hoN s).1 hs
    have hcomm : (o * s * o⁻¹) * c = c * (o * s * o⁻¹) := Subgroup.mem_centralizer_iff.1 hcC _ hos
    have e : g * s * g⁻¹ = c * (o * s * o⁻¹) * c⁻¹ := by rw [hgco]; group
    rw [e, ← hcomm, mul_inv_cancel_right]
  have hpow : ∀ n : ℕ, ∀ s ∈ Sg, g ^ n * s * (g ^ n)⁻¹ = o ^ n * s * (o ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro s _; simp
    | succ n ih =>
      intro s hs
      have hmem : o ^ n * s * (o ^ n)⁻¹ ∈ Sg := by
        have hon : o ^ n ∈ Subgroup.normalizer (Sg : Set G) := Subgroup.pow_mem _ hoN n
        exact (Subgroup.mem_normalizer_iff.1 hon s).1 hs
      have h1 : g ^ (n + 1) * s * (g ^ (n + 1))⁻¹ = g * (g ^ n * s * (g ^ n)⁻¹) * g⁻¹ := by
        rw [pow_succ]; group
      rw [h1, ih s hs, hconj _ hmem, pow_succ]
      group
  have hou : o ^ Nat.card ↥O = 1 := by
    have h := orderOf_dvd_natCard (⟨o, hoO⟩ : ↥O)
    have h2 : (⟨o, hoO⟩ : ↥O) ^ Nat.card ↥O = 1 := orderOf_dvd_iff_pow_eq_one.1 h
    exact congrArg Subtype.val h2
  have hcopk : Nat.Coprime (Nat.card ↥O) (3 ^ k) := Nat.Coprime.pow_right k hcopO.symm
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcopk)
  have hcent : ∀ s ∈ Sg, g * s = s * g := by
    intro s hs
    have hu : g ^ Nat.card ↥O * s * (g ^ Nat.card ↥O)⁻¹ = s := by
      rw [hpow _ s hs, hou, one_mul, inv_one, mul_one]
    have hus : g ^ Nat.card ↥O * s = s * g ^ Nat.card ↥O := mul_inv_eq_iff_eq_mul.1 hu
    have hgu : g ^ Nat.card ↥O ∈ Subgroup.centralizer ({s} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hus
    have hgr : g ^ (3 ^ k) = 1 := hk
    have hab' : a * (Nat.card ↥O : ℤ) + ((3 ^ k : ℕ) : ℤ) * b = 1 := by
      rw [mul_comm (((3 ^ k : ℕ)) : ℤ) b]
      exact hab
    have hA : g ^ (a * (Nat.card ↥O : ℤ)) = (g ^ Nat.card ↥O) ^ a := by
      rw [mul_comm, zpow_mul, zpow_natCast]
    have hB : g ^ (((3 ^ k : ℕ) : ℤ) * b) = 1 := by
      rw [zpow_mul, zpow_natCast, hgr, one_zpow]
    have e : g = (g ^ Nat.card ↥O) ^ a := by
      have h1 : g ^ (a * (Nat.card ↥O : ℤ) + ((3 ^ k : ℕ) : ℤ) * b) = g := by
        rw [hab', zpow_one]
      rw [zpow_add, hA, hB, mul_one] at h1
      exact h1.symm
    have hz : g ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [e]
      exact Subgroup.zpow_mem _ hgu a
    exact Subgroup.mem_centralizer_singleton_iff.1 hz
  exact Subgroup.mem_centralizer_iff.2 fun s hs => (hcent s hs).symm

theorem l71_I_cent_T (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {y : G} {J : Subgroup G}
    (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L 11 y J) {a : G} {K T I Sg : Subgroup G}
    (D : Lemma73Data 3 B x L y J a K T I Sg) (hIN : I ≤ Subgroup.normalizer (T : Set G))
    (hgen : GenByPElts 3 I) : (⁅I, T⁆ : Subgroup G) = ⊥ := by
  classical
  have hJL : J ≤ L := S.J_comp.1.trans inf_le_left
  have hIL : I ≤ L := D.I_le_J.trans hJL
  set O : Subgroup G := GLAPPrimeCoreOf 3 L with hO
  have hsn : IsSubnormal L (Subgroup.centralizer ({x} : Set G)) := (IsSStarMax.component hB).2.1
  have hOle : O ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) :=
    glaPPrimeCoreOf_le_of_isSubnormal hc.prime hsn
  have hodd4 : Odd (Nat.card ↥(⁅L, GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G))⁆ : Subgroup G)) :=
    hc.stage4.1 B x L hB.1.1
  have hoddLO : Odd (Nat.card ↥(⁅L, O⁆ : Subgroup G)) :=
    hodd4.of_dvd_nat (Subgroup.card_dvd_of_le (Subgroup.commutator_mono le_rfl hOle))
  have hT2 : IsPGroup 2 ↥T := D.T_two
  have hF1 : ∀ g ∈ I, ∀ t ∈ T ⊓ O, g * t = t * g := by
    intro g hgI t htTO
    have htT : t ∈ T := htTO.1
    have htO : t ∈ O := htTO.2
    have hgL : g ∈ L := hIL hgI
    have hcT : g * t * g⁻¹ * t⁻¹ ∈ T :=
      T.mul_mem ((Subgroup.mem_normalizer_iff.1 (hIN hgI) t).1 htT) (T.inv_mem htT)
    have hgtO : g * t * g⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 L hgL) t).1 htO
    have hcO : g * t * g⁻¹ * t⁻¹ ∈ O := O.mul_mem hgtO (O.inv_mem htO)
    have hcLO : g * t * g⁻¹ * t⁻¹ ∈ (⁅L, O⁆ : Subgroup G) := by
      have e : ⁅g, t⁆ = g * t * g⁻¹ * t⁻¹ := commutatorElement_def g t
      rw [← e]
      exact Subgroup.commutator_mem_commutator hgL htO
    have hN : (⟨_, hcLO⟩ : ↥(⁅L, O⁆ : Subgroup G)) ^ Nat.card ↥(⁅L, O⁆ : Subgroup G) = 1 := pow_card_eq_one'
    have hN' : (g * t * g⁻¹ * t⁻¹) ^ Nat.card ↥(⁅L, O⁆ : Subgroup G) = 1 := congrArg Subtype.val hN
    have hc1 := y5x_eq_one_of_two_group_pow hT2 hcT hN' (Nat.coprime_two_left.2 hoddLO)
    have e2 : g * t * g⁻¹ = t := mul_inv_eq_one.1 hc1
    exact mul_inv_eq_iff_eq_mul.1 e2
  have hF2 : ∀ g ∈ I, IsPGroup 3 (Subgroup.zpowers g) → ∀ t ∈ T, g * t = t * g := by
    intro g hgI hgp t htT
    obtain ⟨k, hk⟩ := (isPGroup_zpowers_iff_exists_pow).1 hgp
    have hcT : g * t * g⁻¹ * t⁻¹ ∈ T :=
      T.mul_mem ((Subgroup.mem_normalizer_iff.1 (hIN hgI) t).1 htT) (T.inv_mem htT)
    have hcO : g * t * g⁻¹ * t⁻¹ ∈ O := by
      have e : ⁅g, t⁆ = g * t * g⁻¹ * t⁻¹ := commutatorElement_def g t
      rw [← e]
      exact D.comm_T (Subgroup.commutator_mem_commutator hgI htT)
    have hcomm : Commute g (g * t * g⁻¹ * t⁻¹) := hF1 g hgI _ ⟨hcT, hcO⟩
    have hgt1 : g * t = (g * t * g⁻¹ * t⁻¹) * t * g := by group
    have hgt : ∀ j : ℕ, g ^ j * t = (g * t * g⁻¹ * t⁻¹) ^ j * t * g ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hc' : g * (g * t * g⁻¹ * t⁻¹) ^ j = (g * t * g⁻¹ * t⁻¹) ^ j * g := (hcomm.pow_right j).eq
        calc g ^ (j + 1) * t = g * (g ^ j * t) := by rw [pow_succ', mul_assoc]
          _ = g * ((g * t * g⁻¹ * t⁻¹) ^ j * t * g ^ j) := by rw [ih]
          _ = (g * (g * t * g⁻¹ * t⁻¹) ^ j) * t * g ^ j := by simp only [mul_assoc]
          _ = ((g * t * g⁻¹ * t⁻¹) ^ j * g) * t * g ^ j := by rw [hc']
          _ = (g * t * g⁻¹ * t⁻¹) ^ j * (g * t) * g ^ j := by simp only [mul_assoc]
          _ = (g * t * g⁻¹ * t⁻¹) ^ j * (g * t * g⁻¹ * t⁻¹ * t * g) * g ^ j := by rw [← hgt1]
          _ = (g * t * g⁻¹ * t⁻¹) ^ (j + 1) * t * g ^ (j + 1) := by
            rw [pow_succ, pow_succ']
            simp only [mul_assoc]
    have hN : (g * t * g⁻¹ * t⁻¹) ^ 3 ^ k = 1 := by
      have h := hgt (3 ^ k)
      rw [hk, one_mul, mul_one] at h
      exact mul_right_cancel (h.symm.trans (one_mul t).symm)
    have hc1 := y5x_eq_one_of_two_group_pow hT2 hcT hN
      (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3))
    have e2 : g * t * g⁻¹ = t := mul_inv_eq_one.1 hc1
    exact mul_inv_eq_iff_eq_mul.1 e2
  have hIC : I ≤ Subgroup.centralizer (T : Set G) := by
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro g ⟨hgI, hgp⟩
    exact Subgroup.mem_centralizer_iff.2 fun t ht => (hF2 g hgI hgp t ht).symm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hIC

theorem l71_S_cent_T {I T Sg : Subgroup G} (hIT : (⁅I, T⁆ : Subgroup G) = ⊥)
    (hST : Sg ≤ Subgroup.normalizer (T : Set G)) (hSI : Sg ≤ ⁅Sg, I⁆) :
    Sg ≤ Subgroup.centralizer (T : Set G) := by
  have h1 : (⁅⁅I, T⁆, Sg⁆ : Subgroup G) = ⊥ := by rw [hIT, Subgroup.commutator_bot_left]
  have h2 : (⁅⁅T, Sg⁆, I⁆ : Subgroup G) = ⊥ := by
    have hle : (⁅T, Sg⁆ : Subgroup G) ≤ T := commutator_le_left_of_normalizes hST
    refine le_bot_iff.1 ?_
    calc (⁅⁅T, Sg⁆, I⁆ : Subgroup G) ≤ ⁅T, I⁆ := Subgroup.commutator_mono hle le_rfl
      _ = ⁅I, T⁆ := Subgroup.commutator_comm _ _
      _ = ⊥ := hIT
  have h3 : (⁅⁅Sg, I⁆, T⁆ : Subgroup G) = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have h4 : (⁅Sg, T⁆ : Subgroup G) ≤ ⁅⁅Sg, I⁆, T⁆ := Subgroup.commutator_mono hSI le_rfl
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact le_bot_iff.1 (h4.trans h3.le)

theorem inf_centralizer_sup_eq_of_comm {K A Dd : Subgroup G} (hKA : ∀ g ∈ K, ∀ a ∈ A, a * g = g * a) :
    K ⊓ Subgroup.centralizer ((A ⊔ Dd : Subgroup G) : Set G) = K ⊓ Subgroup.centralizer (Dd : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (Subgroup.centralizer_le (by exact_mod_cast (le_sup_right : Dd ≤ A ⊔ Dd)))
  · intro g hg
    refine ⟨hg.1, ?_⟩
    have hle : A ⊔ Dd ≤ Subgroup.centralizer ({g} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun d hd => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hKA g hg.1 a ha)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hg.2 d hd)
    exact Subgroup.mem_centralizer_iff.2 fun h hh => Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem l71_false (hc : S6Ctx G 3) (i264 : I264ChevTwoAt G 3) (i61 : I61L62At) (i106 : I106L62At G)
    (i131 : I131L62At G) (i182 : I182At G) {B : Subgroup G} {x : G} {L : Subgroup G}
    {y : G} {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L 11 y J) (hyB : y ∈ B)
    (hB81 : Nat.card ↥B = 3 ^ 4) {a : G} {K T I Sg : Subgroup G}
    (D : Lemma73Data 3 B x L y J a K T I Sg) : False := by
  obtain ⟨hS2, hIN, hID, hSa, hIS, hDS, hBS, hSI, hgen, hST⟩ := l71_facts hc hB S hyB D
  have hxB : x ∈ B := (IsSStarMax.essential hB).1
  have hDB : altDxy x y ≤ B :=
    sup_le ((Subgroup.zpowers_le).2 hxB) ((Subgroup.zpowers_le).2 hyB)
  have haB : a ∈ B := hDB D.a_mem
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := D.K_comp.1
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_isDirectZpowersInf D.B_eq_K hKa
  have hXK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) := kGroup_centralizer hc D.a_ne_one
  have hKgrp : CFSG.Open.IsKGroup ↥K := isKGroup_of_component hc D.a_ne_one D.K_comp
  have hJK : J ≤ K := by rw [D.K_eq]; exact le_closureIn_self J _
  have hIK : I ≤ K := D.I_le_J.trans hJK
  have hIL : I ≤ L := D.I_le_J.trans (S.J_comp.1.trans inf_le_left)
  have hmax := l71_maxRank hc i106 D.B_eq_K hKa D.K_type hB81
  have hGB : IsGB 3 B K := i264 hc.prime hc.odd B a K (IsSStarMax.bmax hB).1 haB D.a_ne_one D.K_comp hKgrp
    hBK (by rw [hB81]) hmax (isChevSimple_two_of_L62 D.K_type) ⟨Sg, D.S_le_K, hS2, hBS, D.S_not_le⟩
  have hGS : IsGStar 3 B K := by
    obtain ⟨E, hEB, hEel, hE27, -, hne⟩ := hGB
    exact ⟨E, hEB, hEel, hE27, by rwa [closureIn_eq_self hBK]⟩
  have h413 := hc.stage4.2.1 B a K (IsSStarMax.bmax hB) haB D.a_ne_one D.K_comp hGS
  rw [closureIn_eq_self hBK] at h413
  have hOK : GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) :=
    glaPPrimeCoreOf_le_of_isSubnormal hc.prime D.K_comp.2.1
  have hodd1 : Odd (Nat.card ↥(⁅K, GLAPPrimeCoreOf 3 K⁆ : Subgroup G)) :=
    h413.of_dvd_nat (Subgroup.card_dvd_of_le (Subgroup.commutator_mono le_rfl hOK))
  have hOdd : Odd (Nat.card ↥(GLAPPrimeCoreOf 3 K)) := l71_core_odd i61 D.K_comp D.K_type hodd1
  obtain ⟨hDo, hDsplit⟩ := l71_Do_card (IsSStarMax.bmax hB).1 D.B_eq_K hDB D.a_mem D.a_ne_one (S.isElemAbelian_D.2 a D.a_mem) S.card_D
  have hJ8 := D.J_alt8
  have hI7 := D.I_alt7
  have hker : J ⊓ GLAPPrimeCoreOf 3 K = GLAPPrimeCoreOf 3 J := by
    obtain ⟨e8⟩ := hJ8
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin 8)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    haveI : IsSimpleGroup ↥(imageMod 3 K J) := e8.isSimpleGroup
    have hdvd : 3 ∣ Nat.card ↥(imageMod 3 K J) := by
      rw [Nat.card_congr e8.toEquiv]
      exact p_dvd_card_alternatingGroup Nat.prime_three (by norm_num)
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact le_antisymm (inf_primeCoreOf_le Nat.prime_three hJK)
      (le_inf (primeCoreOf_le_self 3 J) (primeCore_le_of_imageMod_simple Nat.prime_three hJK inferInstance hdvd))
  have hJcomp := l71_J_comp hc hB S hJK
  have hlayer : GLAPLayer 3 (K ⊓ Subgroup.centralizer (altDxy x y : Set G)) = J :=
    l73_layer_KD hc i182 hB S D.a_mem D.K_comp.2.1 hJK hJcomp
  have hCeq : K ⊓ Subgroup.centralizer ((altDxy x y ⊓ K : Subgroup G) : Set G) =
      K ⊓ Subgroup.centralizer (altDxy x y : Set G) := by
    conv_rhs => rw [hDsplit]
    exact (inf_centralizer_sup_eq_of_comm (fun g hg a ha => by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 ha
      subst hm
      exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hKa hg) : Commute g a) m).eq.symm)).symm
  have hlayerDo : GLAPLayer 3 (K ⊓ Subgroup.centralizer ((altDxy x y ⊓ K : Subgroup G) : Set G)) = J := by
    rw [hCeq]; exact hlayer
  have hcommDo : ∀ d ∈ altDxy x y ⊓ K, ∀ i ∈ I, d * i = i * d := fun d hd i hi =>
    Subgroup.mem_centralizer_iff.1 (hID hi) d hd.1
  have hnorm := i131 (Subgroup.centralizer ({a} : Set G)) K (altDxy x y ⊓ K) J I Sg hXK D.K_comp
    D.K_type D.S_le_K hS2 D.S_not_le inf_le_right hDo hIK hcommDo hI7
    (sup_le (inf_le_left.trans hDS) hIS) hJK D.I_le_J hlayerDo hJ8
  have hDK : altDxy x y ≤ Subgroup.normalizer (K : Set G) := hDB.trans hBK
  have himg := l71_image_cover hDK hDS S.isElemAbelian_D D.S_le_K hS2 hOdd hlayer hnorm
  have hxD : x ∈ altDxy x y := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hYx : K ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓ Subgroup.normalizer (Sg : Set G) ≤
      Subgroup.centralizer ({x} : Set G) :=
    (inf_le_left.trans inf_le_right).trans (Subgroup.centralizer_le (by simpa using hxD))
  have hYL := l71_layer_le_L hc hB S hYx
  have hcov1 := l71_cover_of_image hJK hlayer hker himg hYL
  have hIT := l71_I_cent_T hc hB S D hIN hgen
  have hSCT : Sg ≤ Subgroup.centralizer (T : Set G) := l71_S_cent_T hIT hST hSI
  have hTSg : T ≤ Subgroup.centralizer (Sg : Set G) := Subgroup.le_centralizer_iff.1 hSCT
  have hTN : T ≤ Subgroup.normalizer (Sg : Set G) :=
    hTSg.trans (Subgroup.centralizer_le_normalizer (Sg : Set G))
  have hJL : J ≤ L := S.J_comp.1.trans inf_le_left
  have hcovL : CoversMod 3 (Subgroup.normalizer (Sg : Set G) ⊓ L) L :=
    coversMod_trans D.covers (le_inf hTN D.T_le) D.T_le hJL hcov1 (l71_kernel_L S)
  have hcovMo : CoversMod 3 (Subgroup.centralizer (Sg : Set G) ⊓ L) L :=
    l71_cover_M_o (by norm_num) S.alt D.T_le hTSg D.T_not_le hcovL
  have hIM : I ≤ Subgroup.centralizer (Sg : Set G) := l71_I_le_M_o hcovMo hIL hIS hgen
  have hbot : (⁅I, Sg⁆ : Subgroup G) = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hIM
  apply D.S_ne
  rw [← le_bot_iff]
  calc Sg ≤ ⁅Sg, I⁆ := hSI
    _ = ⁅I, Sg⁆ := Subgroup.commutator_comm _ _
    _ = ⊥ := hbot

end CFSG.LocalAnalysis.GLTheoremA
