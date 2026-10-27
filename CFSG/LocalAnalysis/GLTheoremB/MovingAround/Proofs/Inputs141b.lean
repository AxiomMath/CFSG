module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open scoped commutatorElement

@[expose] def Input14_1CoreCyc : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), CFSG.Open.IsQuasisimple ↥K →
    CFSG.Open.IsKGroup ↥K → GLAPPrimeCore 3 ↥K = ⊥ → IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K) →
    ∀ b : Y, b ∈ Subgroup.normalizer (K : Set Y) → b ^ 3 = 1 → b ∉ Subgroup.centralizer (K : Set Y) →
    ∀ J : Subgroup Y, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) J →
      IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) →
    ∀ k : Y, k ∈ K → k ∈ Subgroup.centralizer ({b} : Set Y) → IsPGroup 2 ↥(Subgroup.zpowers k) →
      InducesInner 3 J k

theorem input14_1CoreCyc_of_core (h : Input14_1Core) : Input14_1CoreCyc := by
  intro Y _ _ K hKq hKK hKO hchev b hbN hb3 hbK J hJ hJt k hk hkb hk2
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hbK (Subgroup.one_mem _)
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hel : IsElemAbelian 3 (Subgroup.zpowers b) := by
    refine ⟨⟨⟨fun u w => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 u.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 w.2
      show (u : Y) * w = w * u
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hfaith : Subgroup.zpowers b ⊓ Subgroup.centralizer (K : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgb, hgK⟩
    rw [Subgroup.mem_bot]
    by_contra hg1
    have hgo : orderOf g = 3 := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgb
      refine orderOf_eq_prime ?_ hg1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    have heq : Subgroup.zpowers g = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hgb)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hgo, hbo])
    exact hbK ((Subgroup.zpowers_le.2 hgK) (heq ▸ Subgroup.mem_zpowers b))
  have hne : Subgroup.zpowers b ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hb1
  have hcz : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup Y) : Set Y) =
      Subgroup.centralizer ({b} : Set Y) := Claims1245b.centralizer_zpowers_eq b
  refine h Y K hKq hKK hKO (Subgroup.zpowers b) (Subgroup.zpowers_le.2 hbN) hel hfaith hne (fun _ => hchev) J
    ?_ hJt k hk ?_ hk2
  · rw [hcz]
    exact hJ
  · rw [hcz]
    exact hkb

section CycConfig

variable {G : Type} [Group G] [Finite G]

theorem config_base_cyc (hI1417 : Claims1245c.Input14_17) (hcore : Input14_1CoreCyc) {𝒞 : Set (Subgroup G)}
    {B J : Subgroup G} {k : G} (hC : IsConfig 𝒞 B)
    (hcyc : ∃ b₀ ∈ B, ∀ b ∈ B, ∃ i : ℕ, b * b₀ ^ i ∈ Subgroup.centralizer ((sSup 𝒞 : Subgroup G) : Set G))
    (hJ : GLAPComponent 3 (sSup 𝒞 ⊓ Subgroup.centralizer (B : Set G)) J)
    (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)))
    (hk : k ∈ sSup 𝒞) (hkB : k ∈ Subgroup.centralizer (B : Set G))
    (hk2 : IsPGroup 2 ↥(Subgroup.zpowers k))
    (hfix : ∀ s ∈ B, ∀ X ∈ 𝒞, s ∈ Subgroup.normalizer (X : Set G)) : InducesInner 3 J k := by
  obtain ⟨K, hK, hLK⟩ := hC.eq_singleton hJ hfix
  rw [hLK] at hJ hk hcyc
  obtain ⟨b₀, hb₀B, hb₀⟩ := hcyc
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := fun b hb => hfix b hb K hK
  by_cases hb₀K : b₀ ∈ Subgroup.centralizer (K : Set G)
  · have hBK : B ≤ Subgroup.centralizer (K : Set G) := fun b hb => by
      obtain ⟨i, hi⟩ := hb₀ b hb
      have e : b = (b * b₀ ^ i) * (b₀ ^ i)⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hi (Subgroup.inv_mem _ (Subgroup.pow_mem _ hb₀K i))
    exact inducesInner_of_le_centralizer (hC.quasisimple K hK) hBK hJ hk
  · have hcent : K ⊓ Subgroup.centralizer (B : Set G) = K ⊓ Subgroup.centralizer ({b₀} : Set G) := by
      refine le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hb₀B)))
        (fun x hx => ⟨hx.1, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩)
      obtain ⟨i, hi⟩ := hb₀ b hb
      have h1 : x * (b * b₀ ^ i) = (b * b₀ ^ i) * x := Subgroup.mem_centralizer_iff.1 hi x hx.1
      have h2 : Commute x b₀ := Subgroup.mem_centralizer_singleton_iff.1 hx.2
      have h3 : x * (b₀ ^ i)⁻¹ = (b₀ ^ i)⁻¹ * x := ((h2.pow_right i).inv_right).eq
      calc b * x = (b * b₀ ^ i) * (b₀ ^ i)⁻¹ * x := by group
        _ = (b * b₀ ^ i) * (x * (b₀ ^ i)⁻¹) := by rw [mul_assoc, h3]
        _ = (b * b₀ ^ i) * x * (b₀ ^ i)⁻¹ := by group
        _ = x * (b * b₀ ^ i) * (b₀ ^ i)⁻¹ := by rw [h1]
        _ = x * b := by group
    have hb₀3 : b₀ ^ 3 = 1 := hC.elem.2 b₀ hb₀B
    have h3 : 3 ∣ Nat.card ↥K :=
      (three_dvd_card_of_isLThreeFour hJt).trans (Subgroup.card_dvd_of_le (hJ.1.trans inf_le_left))
    rw [hcent] at hJ
    have hKO : GLAPPrimeCore 3 ↥K = ⊥ :=
      glaPPrimeCore_eq_bot_of_center (hC.quasisimple K hK) (hC.center K hK) h3
    have hchev := isChevSimple_of_input14_17 hI1417 (hC.quasisimple K hK) (hC.kgroup K hK) hKO (hBN hb₀B)
      hb₀3 hJ hJt
    exact hcore G K (hC.quasisimple K hK) (hC.kgroup K hK) hKO hchev b₀ (hBN hb₀B) hb₀3 hb₀K J hJ hJt k hk
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hb₀B) hkB) hk2

theorem config_inner_cyc (hI1417 : Claims1245c.Input14_17) (hcore : Input14_1CoreCyc) (n : ℕ) :
    ∀ (𝒞 : Set (Subgroup G)) (B J : Subgroup G) (k : G), Nat.card ↥(sSup 𝒞) ≤ n → IsConfig 𝒞 B →
      (∃ b₀ ∈ B, ∀ b ∈ B, ∃ i : ℕ, b * b₀ ^ i ∈ Subgroup.centralizer ((sSup 𝒞 : Subgroup G) : Set G)) →
      GLAPComponent 3 (sSup 𝒞 ⊓ Subgroup.centralizer (B : Set G)) J →
      IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) →
      k ∈ sSup 𝒞 → k ∈ Subgroup.centralizer (B : Set G) → IsPGroup 2 ↥(Subgroup.zpowers k) →
      InducesInner 3 J k := by
  induction n with
  | zero =>
    intro 𝒞 B J k hn
    have h := Nat.card_pos (α := ↥(sSup 𝒞))
    omega
  | succ n ih =>
    intro 𝒞 B J k hn hC hcyc hJ hJt hk hkB hk2
    by_cases hmove : ∃ s ∈ B, ∃ X ∈ 𝒞, s ∉ Subgroup.normalizer (X : Set G)
    · obtain ⟨s, hsB, X₀, hX₀, hsX₀⟩ := hmove
      obtain ⟨𝒞', hcard, hle, hC', hJ', hk'⟩ := config_step hC hJ hk hkB hk2 hsB hX₀ hsX₀
      obtain ⟨b₀, hb₀B, hb₀⟩ := hcyc
      refine ih 𝒞' B J k (by omega) hC' ⟨b₀, hb₀B, fun b hb => ?_⟩ hJ' hJt hk' hkB hk2
      obtain ⟨i, hi⟩ := hb₀ b hb
      exact ⟨i, Subgroup.centralizer_le hle hi⟩
    · push Not at hmove
      exact config_base_cyc hI1417 hcore hC hcyc hJ hJt hk hkB hk2 hmove

end CycConfig

@[expose] def Input14_1InnerCyc : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsKGroup Y → GLAPPrimeCore 3 Y = ⊥ →
    ∀ B : Subgroup Y, IsElemAbelian 3 B →
      (∃ b₀ ∈ B, ∀ b ∈ B, ∃ i : ℕ, b * b₀ ^ i ∈ Subgroup.center Y) →
    ∀ J : Subgroup Y, GLAPComponent 3 (Subgroup.centralizer (B : Set Y)) J →
      IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) →
    ∀ v : Y, IsPGroup 2 ↥(Subgroup.zpowers v) → v ∈ Subgroup.centralizer (B : Set Y) →
      (∀ L : Subgroup Y, IsComponentOf L ⊤ → v ∈ Subgroup.normalizer (L : Set Y) ∧
        ∃ l ∈ L, l⁻¹ * v ∈ Subgroup.centralizer (L : Set Y)) →
      InducesInner 3 J v

theorem input14_1InnerCyc_of_coreCyc
    (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (hI1417 : Claims1245c.Input14_17) (hcore : Input14_1CoreCyc) : Input14_1InnerCyc := by
  intro Y _ _ hYK hYO B hB hcyc J hJ hJt v hv2 hvB hv
  obtain ⟨𝒞, k, hC, hJc, hJM, hkM, hkB, hk2, hkv⟩ := exists_config hSch hYK hYO hB hJ hv2 hvB hv
  obtain ⟨b₀, hb₀B, hb₀⟩ := hcyc
  have hcyc' : ∃ b₀ ∈ B, ∀ b ∈ B, ∃ i : ℕ,
      b * b₀ ^ i ∈ Subgroup.centralizer ((sSup 𝒞 : Subgroup Y) : Set Y) := by
    refine ⟨b₀, hb₀B, fun b hb => ?_⟩
    obtain ⟨i, hi⟩ := hb₀ b hb
    exact ⟨i, Subgroup.mem_centralizer_iff.2 fun y _ => (Subgroup.mem_center_iff.1 hi y)⟩
  exact inducesInner_of_mul_centralizer hJM hkv
    (config_inner_cyc hI1417 hcore (Nat.card ↥(sSup 𝒞)) 𝒞 B J k le_rfl hC hcyc' hJc hJt hkM hkB hk2)

section Rank

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_four_of_cex {m : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m 3 B M E A a)
    (hEA : Nat.card (E ⊓ A : Subgroup G) = 9) : CFSG.Open.pRank 3 A ≤ 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hk : CFSG.Open.pRank 3 (E ⊓ A) = 2 :=
    Lemma124.pRank_eq_two_of_card_nine (Lemma124.isElemAbelian_of_le inf_le_right hAel) hEA
  by_contra hlt
  push Not at hlt
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hcardA : Nat.card A = 3 ^ CFSG.Open.pRank 3 A := Lemma124.card_eq_pow_pRank hAel
  obtain ⟨R, hR, hAR⟩ :=
    Lemma124.exists_isSylowIn_above_aux hAM (Lemma124.isPGroup_three_of_isElemAbelian hAel)
  obtain ⟨H5, hH5⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) 3 (n := 5)
    (by rw [hcardA]; exact pow_dvd_pow 3 hlt)
  set E5 : Subgroup G := H5.map A.subtype with hE5def
  have hE5A : E5 ≤ A := Subgroup.map_subtype_le _
  have hE5card : Nat.card E5 = 3 ^ 5 := by
    rw [hE5def, Subgroup.card_map_of_injective A.subtype_injective, hH5]
  have hE5el : IsElemAbelian 3 E5 := Lemma124.isElemAbelian_of_le hE5A hAel
  obtain ⟨H3, hH3⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E5) 3 (n := 3)
    (by rw [hE5card]; exact pow_dvd_pow 3 (by norm_num))
  set E3 : Subgroup G := H3.map E5.subtype with hE3def
  have hE3E5 : E3 ≤ E5 := Subgroup.map_subtype_le _
  have hE3card : Nat.card E3 = 3 ^ 3 := by
    rw [hE3def, Subgroup.card_map_of_injective E5.subtype_injective, hH3]
  have hE3el : IsElemAbelian 3 E3 := Lemma124.isElemAbelian_of_le hE3E5 hE5el
  have hE5R : IsEkIn 3 5 R E5 := ⟨hE5A.trans hAR, hE5el, hE5card⟩
  obtain ⟨hinD0, -, -⟩ := lemma104_iv_holds h.toSec11.toSec10Fails h.pair hk hR
  obtain ⟨-, -, A', hA'D, hE5A'⟩ := hinD0 E5 hE5R
  have hA'el : IsElemAbelian 3 A' := hA'D.1.1.2.1
  have hSCA : IsSCp 3 ⊤ A := (lemma104_ii_holds h.toSec11.toSec10Fails h.pair).2
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    CFSG.Open.IsElemAbelian.comm hAel hx hy
  have hcommA' : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := fun x hx y hy =>
    CFSG.Open.IsElemAbelian.comm hA'el hx hy
  have hconn : IsKConnectedIn 3 (CFSG.Open.pRank 3 (E ⊓ A) + 1) ⊤ A A' := by
    rw [hk]
    refine ⟨le_top, hAel, ?_, le_top, hA'el, ?_, Or.inr ⟨E3, E3, ⟨le_top, hE3el, hE3card⟩,
      ⟨le_top, hE3el, hE3card⟩, ?_, Relation.ReflTransGen.refl, ?_⟩⟩
    · rw [hcardA]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · have h1 : Nat.card E5 ≤ Nat.card A' := Subgroup.card_le_of_le hE5A'
      rw [hE5card] at h1
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h1
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hcommA y (hE3E5.trans hE5A hy) x hx
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hcommA' y hy x (hE5A' (hE3E5 hx))
  have hDA : inD 3 M A := lemma104_iii_holds h.toSec11.toSec10Fails h.pair hSCA hA'D hconn
  exact h.pair.1.2.1.2 hDA.2

theorem card_FF_le_nine {m : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m 3 B M E A a) {K : Subgroup G}
    (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K) :
    Nat.card (Lemma1245.FF A K) ≤ 9 := by
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hA4 := pRank_le_four_of_cex h hA0.1
  have hA81 : Nat.card A ≤ 81 := by
    rw [Lemma124.card_eq_pow_pRank hAel]
    calc 3 ^ CFSG.Open.pRank 3 A ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hA4
      _ = 81 := by norm_num
  have hFA : Lemma1245.FF A K ≤ A := inf_le_right
  have hA0A : E ⊓ A ≤ A := inf_le_right
  have hcomm : ∀ u ∈ E ⊓ A, ∀ f ∈ Lemma1245.FF A K, u * f = f * u := fun u hu f hf =>
    CFSG.Open.IsElemAbelian.comm hAel (hA0A hu) (hFA hf)
  have hdisj : E ⊓ A ⊓ Lemma1245.FF A K = ⊥ := by
    rw [eq_bot_iff]
    rintro b ⟨hb, hbF⟩
    exact (Subgroup.mem_bot).2 (hA0.2.2.1 b hb ⟨hbF.1, Subgroup.mem_top _⟩)
  have hprod := Lemma124.card_eq_mul_of_sup_eq hcomm rfl hdisj
  have hle : Nat.card (E ⊓ A ⊔ Lemma1245.FF A K : Subgroup G) ≤ Nat.card A :=
    Subgroup.card_le_of_le (sup_le hA0A hFA)
  rw [hprod, hA0.1] at hle
  omega

theorem exists_gen_of_card_le_nine {F : Subgroup G} (hF : IsElemAbelian 3 F) (hF9 : Nat.card F ≤ 9) {x : G}
    (hx : x ∈ F) (hx1 : x ≠ 1) : ∃ f ∈ F, ∀ y ∈ F, ∃ i : ℕ, y * f ^ i ∈ Subgroup.zpowers x := by
  classical
  by_cases hle : F ≤ Subgroup.zpowers x
  · exact ⟨1, F.one_mem, fun y hy => ⟨0, by simpa using hle hy⟩⟩
  · obtain ⟨f, hfF, hfx⟩ := Set.not_subset.1 hle
    refine ⟨f, hfF, fun y hy => ?_⟩
    have hx3 : x ^ 3 = 1 := hF.2 x hx
    have hf3 : f ^ 3 = 1 := hF.2 f hfF
    have hf1 : f ≠ 1 := fun h => hfx (h ▸ Subgroup.one_mem _)
    have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hfo : orderOf f = 3 := orderOf_eq_prime hf3 hf1
    have hcomm : ∀ u ∈ Subgroup.zpowers x, ∀ w ∈ Subgroup.zpowers f, u * w = w * u := fun u hu w hw =>
      hF.comm ((Subgroup.zpowers_le.2 hx) hu) ((Subgroup.zpowers_le.2 hfF) hw)
    have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers f = ⊥ := by
      rw [eq_bot_iff]
      rintro g ⟨hgx, hgf⟩
      rw [Subgroup.mem_bot]
      by_contra hg1
      have hgo : orderOf g = 3 := by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgf
        refine orderOf_eq_prime ?_ hg1
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hf3, one_zpow]
      have heq : Subgroup.zpowers g = Subgroup.zpowers f :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hgf)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hgo, hfo])
      exact hfx ((Subgroup.zpowers_le.2 hgx) (heq ▸ Subgroup.mem_zpowers f))
    have hcard : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers f : Subgroup G) = 9 := by
      rw [Lemma124.card_eq_mul_of_sup_eq hcomm rfl hdisj, Nat.card_zpowers, Nat.card_zpowers, hxo, hfo]
    have hsupF : Subgroup.zpowers x ⊔ Subgroup.zpowers f ≤ F :=
      sup_le (Subgroup.zpowers_le.2 hx) (Subgroup.zpowers_le.2 hfF)
    have heqF : Subgroup.zpowers x ⊔ Subgroup.zpowers f = F :=
      Subgroup.eq_of_le_of_card_ge hsupF (by rw [hcard]; exact hF9)
    rw [← heqF] at hy
    obtain ⟨u, hu, w, hw, rfl⟩ := Input183.mem_sup_of_commute hcomm hy
    have hw' : w⁻¹ ∈ Submonoid.powers f := (mem_powers_iff_mem_zpowers).2 (Subgroup.inv_mem _ hw)
    obtain ⟨i, hi⟩ := hw'
    have hi' : f ^ i = w⁻¹ := hi
    refine ⟨i, ?_⟩
    rw [hi', mul_inv_cancel_right]
    exact hu

end Rank

section VxCyc

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1245b

theorem vxClaim_of_coreCyc (hSch' : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hI1417 : Claims1245c.Input14_17)
    (hcore : Input14_1CoreCyc) : Lemma1245.VxClaim := by
  have h141 : Input14_1InnerCyc := input14_1InnerCyc_of_coreCyc hSch' hI1417 hcore
  intro G _ _ m B M E A a h K hK hK3 _hKM hA0 _hAN hcov x hx hx1 V hVT hVD
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hA3 : IsPGroup 3 ↥A := Lemma124.isPGroup_three_of_isElemAbelian hAel
  have hFA : Lemma1245.FF A K ≤ A := inf_le_right
  have hFel : IsElemAbelian 3 (Lemma1245.FF A K) := Lemma124.isElemAbelian_of_le hFA hAel
  have hF3 : IsPGroup 3 ↥(Lemma1245.FF A K) := Lemma124.isPGroup_three_of_isElemAbelian hFel
  have haF : a ∈ Lemma1245.FF A K := Lemma1245.mem_centBar_of_component h.ha.1 hK.1
  have hACA : A ≤ Subgroup.centralizer (A : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun w hw => CFSG.Open.IsElemAbelian.comm hAel hw hu
  have hCAF : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (Lemma1245.FF A K : Set G) :=
    Subgroup.centralizer_le hFA
  have hCFx : Subgroup.centralizer (Lemma1245.FF A K : Set G) ≤ Cg x :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hx)
  have hCFa : Subgroup.centralizer (Lemma1245.FF A K : Set G) ≤ Cg a :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 haF)
  have hAx : A ≤ Cg x := hACA.trans (hCAF.trans hCFx)
  have hAa : A ≤ Cg a := hACA.trans (hCAF.trans hCFa)
  have hFX : Lemma1245.FF A K ≤ Cg x := hFA.trans hAx
  have hVC : V ≤ Subgroup.centralizer (A : Set G) := hVT.trans inf_le_right
  have hV2 : IsPGroup 2 ↥V :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le (hVT.trans inf_le_left)
  obtain ⟨e, he, he1⟩ : ∃ e ∈ E ⊓ A, e ≠ 1 := by
    have hne : E ⊓ A ≠ ⊥ := by
      intro hbot
      have h9 := hA0.1
      rw [hbot, Subgroup.card_bot] at h9
      omega
    obtain ⟨⟨e, he⟩, hne1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    exact ⟨e, he, fun h => hne1 (Subtype.ext h)⟩
  have hVW : V ≤ pCoreOf 2 (Subgroup.centralizer (A : Set G)) := by
    have h1 := (Claims122.lemma122_i_ii_holds h).1 e he he1
    have hCe : Subgroup.centralizer (A : Set G) ≤ Cg e :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 he.2)
    have hV1 : V ≤ pCoreOf 2 (Cg2 e a) := (le_inf (hVT.trans inf_le_left) (hVC.trans hCe)).trans h1
    have hCA2 : Subgroup.centralizer (A : Set G) ≤ Cg2 e a :=
      Subgroup.centralizer_le (Set.insert_subset_iff.2 ⟨he.2, Set.singleton_subset_iff.2 h.ha.1⟩)
    exact (le_inf hV1 hVC).trans (pCoreOf_two_inf_le hCA2)
  have hVK : V ≤ Subgroup.normalizer (K : Set G) :=
    hVW.trans (pCoreOf_two_cent_le_normalizer hA3 hAa (hCAF.trans hCFa) hK)
  have hVJ : V ≤ Subgroup.normalizer (Lemma1245.JJ A K : Set G) := fun v hv =>
    Lemma1245.mem_normalizer_JJ (hVK hv) (hCAF (hVC hv))
  have hXK : CFSG.Open.IsKGroup ↥(Cg x) :=
    isKGroup_of_isKProper h.standing.kProper (Sec12b.cent_ne_top h.standing hx1)
  have hVX : V ≤ Cg x := hVC.trans (hCAF.trans hCFx)
  have hVL : ∀ L : Subgroup G, GLAPComponent 3 (Cg x) L → V ≤ Subgroup.normalizer (L : Set G) :=
    fun L hL => hVW.trans (pCoreOf_two_cent_le_normalizer hA3 hAx (hCAF.trans hCFx) hL)
  have hD'L : ∀ L : Subgroup G, GLAPComponent 3 (Cg x) L →
      (⨆ g ∈ (alphaOf 3 M ⊓ Cg x), GLBConj g V) ≤ Subgroup.normalizer (L : Set G) :=
    fun L hL => iSup₂_le fun g hg => gLBConj_le_normalizer hg.2 hVL hL
  have hD'X : (⨆ g ∈ (alphaOf 3 M ⊓ Cg x), GLBConj g V) ≤ Cg x := iSup₂_le fun g hg => by
    have h1 := gLBConj_mono g hVX
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg.2)] at h1
  have hDD' := derivedInf_le' (⨆ g ∈ (alphaOf 3 M ⊓ Cg x), GLBConj g V)
  have hDX := hDD'.trans hD'X
  have hDperf := derivedInf_perfect (⨆ g ∈ (alphaOf 3 M ⊓ Cg x), GLBConj g V)
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg x)) with hπ
  have hYK : CFSG.Open.IsKGroup (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x)) := isKGroup_barX_quotient hXK
  have hYO : GLAPPrimeCore 3 (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x)) = ⊥ :=
    glaPPrimeCore_quotient_eq_bot hp3
  have hinner : ∀ v (hv : v ∈ V), ∀ Lt : Subgroup (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x)),
      IsComponentOf Lt ⊤ →
      π ⟨v, hVX hv⟩ ∈ Subgroup.normalizer (Lt : Set (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x))) ∧
        ∃ l ∈ Lt, l⁻¹ * π ⟨v, hVX hv⟩ ∈
          Subgroup.centralizer (Lt : Set (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x))) := by
    intro v hv Lt hLt
    obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq (Cg x) hLt
    have hDN := barX_le_normalizer (C := Cg x) (p := 3) (hDD'.trans (hD'L L hL))
    have hvD : π ⟨v, hVX hv⟩ ∈
        barX 3 (Cg x) (derivedInf (⨆ g ∈ (alphaOf 3 M ⊓ Cg x), GLBConj g V)) :=
      ⟨⟨v, hVX hv⟩, (Subgroup.mem_subgroupOf).2 (hVD hv), rfl⟩
    exact ⟨hDN hvD, exists_inner_of_perfect' (outer_solvable_of_component hSch hYK hLt)
      (barX_perfect 3 hDX hDperf) hDN hvD⟩
  have hJK : Lemma1245.JJ A K ≤ K := (Sec12b.layer_le 3 _).trans inf_le_left
  have hJCF : Lemma1245.JJ A K ≤ Subgroup.centralizer (Lemma1245.FF A K : Set G) :=
    (Sec12b.layer_le 3 _).trans inf_le_right
  have hJX : Lemma1245.JJ A K ≤ Cg x := hJCF.trans hCFx
  obtain ⟨eJK, heJK⟩ := Lemma1245.exists_barOf_equiv_of_cover hp3 hJK hcov
  have hKq : CFSG.Open.IsQuasisimple (barOf 3 K) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivBarX hp3 hK.1 hK.2.1).symm hK.2.2.1.2.2
  have hJq : CFSG.Open.IsQuasisimple (barOf 3 (Lemma1245.JJ A K)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eJK.symm hKq
  have hJcomp0 : GLAPComponent 3 (K ⊓ Subgroup.centralizer (Lemma1245.FF A K : Set G))
      (Lemma1245.JJ A K) := by
    refine glaPComponent_of_normal (Sec12b.layer_le 3 _) ?_
      (fun N₀ O hON hO hle => layer_le_of_le_sup hO hON hle) hJq
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Sec12b.layer_le 3 _)).2
      (fun g hg => Lemma1245.mem_normalizer_glaPLayer' (Subgroup.le_normalizer hg))
  have hsnKF : IsSubnormal (K ⊓ Subgroup.centralizer (Lemma1245.FF A K : Set G))
      (Cg x ⊓ Subgroup.centralizer (Lemma1245.FF A K : Set G)) := by
    have h1 := hK.2.1.inf (Subgroup.centralizer (Lemma1245.FF A K : Set G))
    have e1 : Cg a ⊓ Subgroup.centralizer (Lemma1245.FF A K : Set G) =
        Cg x ⊓ Subgroup.centralizer (Lemma1245.FF A K : Set G) := by
      rw [inf_eq_right.2 hCFa, inf_eq_right.2 hCFx]
    rwa [e1] at h1
  have hJcomp : GLAPComponent 3 (Cg x ⊓ Subgroup.centralizer (Lemma1245.FF A K : Set G))
      (Lemma1245.JJ A K) :=
    l119_glaPComponent_of_isSubnormal hp3 hsnKF hJcomp0
  have hJt : GLAPComponent 3 (Subgroup.centralizer (barX 3 (Cg x) (Lemma1245.FF A K) :
      Set (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x)))) (barX 3 (Cg x) (Lemma1245.JJ A K)) := by
    have h1 := Prop126b.glaPComponent_subgroupOf hp3
      (inf_le_left : Cg x ⊓ Subgroup.centralizer (Lemma1245.FF A K : Set G) ≤ Cg x) hJcomp
    have hker : Nat.Coprime 3 (Nat.card ↥(((Cg x ⊓ Subgroup.centralizer (Lemma1245.FF A K : Set G)).subgroupOf
        (Cg x)) ⊓ π.ker)) := by
      rw [hπ, QuotientGroup.ker_mk']
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        CFSG.pPrimeCore_coprime_card
    have h2 := glaPComponent_map hp3 π hker h1
    have heq : ((Cg x ⊓ Subgroup.centralizer (Lemma1245.FF A K : Set G)).subgroupOf (Cg x)).map π =
        Subgroup.centralizer (barX 3 (Cg x) (Lemma1245.FF A K) :
          Set (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x))) := by
      refine le_antisymm ?_
        (CFSG.HardMathSupport.Solomon.Coordinator.i183_centralizer_barX_le hp3 hFX hF3)
      show barX 3 (Cg x) (Cg x ⊓ Subgroup.centralizer (Lemma1245.FF A K : Set G)) ≤ _
      refine barX_le_centralizer fun s hs t ht _ _ => ?_
      have hst : t * s = s * t := Subgroup.mem_centralizer_iff.1 hs.2 t ht
      have : s * t * s⁻¹ * t⁻¹ = 1 := by
        rw [← hst]
        group
      rw [this]
      exact Subgroup.one_mem _
    rw [heq] at h2
    exact h2
  have hJtt : IsLThreeFour (barOf 3 (barX 3 (Cg x) (Lemma1245.JJ A K)) ⧸
      Subgroup.center (barOf 3 (barX 3 (Cg x) (Lemma1245.JJ A K)))) :=
    Lemma1245.isLThreeFour_modCenter_congr (eJK.symm.trans (Prop126b.barOfBarX hp3 hJX)) hK3
  have hFb : IsElemAbelian 3 (barX 3 (Cg x) (Lemma1245.FF A K)) := isElemAbelian_barX hFel
  have hVb2 : IsPGroup 2 ↥(barX 3 (Cg x) V) :=
    (hV2.comap_of_injective (Cg x).subtype (Cg x).subtype_injective).map π
  have hVbF : barX 3 (Cg x) V ≤ Subgroup.centralizer (barX 3 (Cg x) (Lemma1245.FF A K) :
      Set (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x))) := by
    refine barX_le_centralizer fun s hs t ht _ _ => ?_
    have hst : t * s = s * t := Subgroup.mem_centralizer_iff.1 (hCAF (hVC hs)) t ht
    have : s * t * s⁻¹ * t⁻¹ = 1 := by
      rw [← hst]
      group
    rw [this]
    exact Subgroup.one_mem _
  have hA0N : E ⊓ A ≤ Subgroup.normalizer (K : Set G) := hA0.2.1
  have hA0el : IsElemAbelian 3 (E ⊓ A) := Lemma124.isElemAbelian_of_le inf_le_right hAel
  have hA0f : ∀ b (hb : b ∈ E ⊓ A), barAut 3 K ⟨b, hA0N hb⟩ = 1 → b = 1 := fun b hb h1 =>
    hA0.2.2.1 b hb ((Lemma129.mem_centBar_top_iff (hA0N hb)).2 h1)
  have hA0i : ∀ b (hb : b ∈ E ⊓ A), ∃ z : barOf 3 K, barAut 3 K ⟨b, hA0N hb⟩ = MulAut.conj z :=
    fun b hb => Lemma1245.exists_conj_of_inducesInner (hA0N hb) (hA0.2.2.2 b hb)
  intro v hv
  have hvX := hVX hv
  have hvJ := hVJ hv
  have hvK := hVK hv
  have hvmem : π ⟨v, hvX⟩ ∈ barX 3 (Cg x) V := ⟨⟨v, hvX⟩, (Subgroup.mem_subgroupOf).2 hv, rfl⟩
  have hFcyc : ∃ b₀ ∈ barX 3 (Cg x) (Lemma1245.FF A K), ∀ b ∈ barX 3 (Cg x) (Lemma1245.FF A K), ∃ i : ℕ,
      b * b₀ ^ i ∈ Subgroup.center (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x)) := by
    obtain ⟨f, hfF, hgen⟩ := exists_gen_of_card_le_nine hFel (card_FF_le_nine h hA0) hx hx1
    refine ⟨π ⟨f, hFX hfF⟩, ⟨⟨f, hFX hfF⟩, Subgroup.mem_subgroupOf.2 hfF, rfl⟩, ?_⟩
    rintro _ ⟨⟨y, hyX⟩, hyF, rfl⟩
    obtain ⟨i, hi⟩ := hgen y (Subgroup.mem_subgroupOf.1 hyF)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hi
    refine ⟨i, ?_⟩
    have hxX : x ∈ Cg x := Subgroup.mem_centralizer_singleton_iff.2 rfl
    have e : π ⟨y, hyX⟩ * π ⟨f, hFX hfF⟩ ^ i = π ⟨x, hxX⟩ ^ j := by
      rw [← map_pow, ← map_mul, ← map_zpow]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, SubgroupClass.coe_pow, SubgroupClass.coe_zpow]
      exact hj.symm
    rw [e]
    refine Subgroup.zpow_mem _ ?_ j
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥(Cg x)) g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 g'.2
  obtain ⟨kt, hkt, hktv⟩ := h141 (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x)) hYK hYO _ hFb hFcyc _ hJt hJtt
    (π ⟨v, hvX⟩) (hVb2.to_le (Subgroup.zpowers_le.2 hvmem)) (hVbF hvmem)
    (fun Lt hLt => hinner v hv Lt hLt)
  obtain ⟨⟨j, hjX⟩, hjJ, rfl⟩ := Subgroup.mem_map.1 hkt
  have hjJ' : j ∈ Lemma1245.JJ A K := (Subgroup.mem_subgroupOf).1 hjJ
  have hw : j⁻¹ * v ∈ centBar 3 ⊤ (Lemma1245.JJ A K) := by
    obtain ⟨-, -, hwt⟩ := (mem_centBar_forall_iff).1 hktv
    have hwN : j⁻¹ * v ∈ Subgroup.normalizer (Lemma1245.JJ A K : Set G) :=
      (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer hjJ')) hvJ
    refine (mem_centBar_forall_iff).2 ⟨Subgroup.mem_top _, hwN, fun l hl => ?_⟩
    have hlX : l ∈ Cg x := hJX hl
    have hc1 : j⁻¹ * v * l * (j⁻¹ * v)⁻¹ ∈ Lemma1245.JJ A K := (Subgroup.mem_normalizer_iff.1 hwN l).1 hl
    have hcJ : j⁻¹ * v * l * (j⁻¹ * v)⁻¹ * l⁻¹ ∈ Lemma1245.JJ A K :=
      (Lemma1245.JJ A K).mul_mem hc1 ((Lemma1245.JJ A K).inv_mem hl)
    refine mem_core_of_barX hJX hcJ ?_
    have h1 := hwt (π ⟨l, hlX⟩) ⟨⟨l, hlX⟩, (Subgroup.mem_subgroupOf).2 hl, rfl⟩
    have e : (⟨j⁻¹ * v * l * (j⁻¹ * v)⁻¹ * l⁻¹, hJX hcJ⟩ : ↥(Cg x)) =
        (⟨j, hjX⟩ : ↥(Cg x))⁻¹ * ⟨v, hvX⟩ * ⟨l, hlX⟩ * ((⟨j, hjX⟩ : ↥(Cg x))⁻¹ * ⟨v, hvX⟩)⁻¹ *
          (⟨l, hlX⟩ : ↥(Cg x))⁻¹ := Subtype.ext rfl
    rw [e]
    simp only [map_mul, map_inv]
    exact h1
  obtain ⟨zJ, hzJ⟩ := Lemma1245.exists_conj_of_inducesInner hvJ ⟨j, hjJ', hw⟩
  have hcong := Lemma1245.congr_barAut_of_cover hJK eJK heJK hvJ hvK
  have hvKz : barAut 3 K ⟨v, hvK⟩ = MulAut.conj (eJK zJ) := by
    rw [← hcong, hzJ, mulAut_congr_conj]
  obtain ⟨n, hn⟩ := hV2 ⟨v, hv⟩
  have hn' : v ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hvA : ∀ b ∈ E ⊓ A, b * v = v * b := fun b hb =>
    Subgroup.mem_centralizer_iff.1 (hVC hv) b hb.2
  have hK1 := barAut_eq_one_of_inner hK3 hKq.1 hA0N hA0.1 hA0el hA0f hA0i hvK hn' hvA hvKz
  rw [Lemma129.mem_centBar_top_iff hvJ]
  apply (MulAut.congr eJK).injective
  rw [hcong, hK1, map_one]


end VxCyc

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141

end
