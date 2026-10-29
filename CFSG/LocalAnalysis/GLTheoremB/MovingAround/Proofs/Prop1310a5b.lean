module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut barAut_mk)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

namespace Prop1310a5b

@[expose] def IsAltOrChev (K : Type) [Group K] : Prop :=
  (∃ n : ℕ, IsAltType n (K ⧸ Subgroup.center K)) ∨ IsLieChar (fun q => q ≠ 3) K

@[expose] def Good2319 (K : Type) [Group K] [Finite K] : Prop :=
  (∃ n : ℕ, IsAltType n (K ⧸ Subgroup.center K)) ∨ (∃ q : ℕ, q ≠ 3 ∧ IsLieChar (· = q) K) ∨
    (∀ A : Subgroup (MulAut K), IsElemAbelian 3 A → CFSG.Open.pRank 3 A ≤ 2)

@[expose] def IsPumpupOrSelf (J : Type) [Group J] (H : Type) [Group H] : Prop :=
  ∃ σ : MulAut H, σ ^ 3 = 1 ∧ ∃ J₁ : Subgroup H, GLAPComponent 3 (Prop1310a5.fixedSub σ) J₁ ∧
    Nonempty (barOf 3 J₁ ≃* J)

@[expose] def Agrp {K : Type} [Group K] (x : MulAut K) (y : K) : Subgroup (MulAut K) :=
  Subgroup.closure {x, MulAut.conj y}

@[expose] def Kstar {K : Type} [Group K] (A : Subgroup (MulAut K)) (S : MulAut K → Set (Subgroup K)) :
    Subgroup K :=
  ⨆ (a : MulAut K) (_ : a ∈ A ∧ a ≠ 1) (J : Subgroup K) (_ : J ∈ S a), J

@[expose] def Input25_6A5 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K →
    GLAPPrimeCore 3 K = ⊥ → ¬ IsPiGroup 3 K →
    ∀ x : MulAut K, orderOf x = 3 → ∀ L : Subgroup K, GLAPComponent 3 (Prop1310a5.fixedSub x) L →
      IsAltType 5 (barOf 3 L) → ∀ y ∈ L, orderOf y = 3 →
      ∃ S : MulAut K → Set (Subgroup K),
        (∀ a ∈ Agrp x y, a ≠ 1 → ∀ J ∈ S a, GLAPComponent 3 (Prop1310a5.fixedSub a) J) ∧
        (∀ Y : Subgroup K, CFSG.Open.IsSubnormal Y (Kstar (Agrp x y) S) → L ≤ Y →
          ¬ IsAltType 5 (barOf 3 Y)) ∧
        (∀ a ∈ Agrp x y, a ≠ 1 → ∀ J ∈ S a, IsAltOrChev (barOf 3 J) ∧
          ∀ (H : Type) [Group H] [Finite H], CFSG.LocalAnalysis.GLTheoremA.IsKHat H →
            GLAPPrimeCore 3 H = ⊥ → IsPumpupOrSelf (barOf 3 J) H → Good2319 H) ∧
        L ≤ ⨆ (J : Subgroup K) (_ : J ∈ S x), J

section Types

theorem center_eq_bot_of_altType5 {X : Type} [Group X] (h : IsAltType 5 X) : Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  exact CFSG.LocalAnalysis.GLTheoremB.center_eq_bot_of_mulEquiv_alt (by norm_num) e

theorem isPiGroup_of_altType5 {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X)
    (hcore : GLAPPrimeCore 3 X = ⊥) (h5 : IsAltType 5 X) : IsPiGroup 3 X := by
  have hcen : Subgroup.center X = ⊥ := center_eq_bot_of_altType5 h5
  obtain ⟨e'⟩ := h5
  have e0 : (X ⧸ Subgroup.center X) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  refine ⟨hq, hcore, Or.inl ⟨1, ⟨?_⟩⟩⟩
  have h1 : 1 * 3 + 2 = 5 := by norm_num
  exact e0.trans (e'.trans (Equiv.altCongrHom (finCongr h1.symm)))

theorem isLieChar_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (P : ℕ → Prop)
    (h : IsLieChar P X) : IsLieChar P Y := by
  obtain ⟨idx, ⟨f⟩, hP⟩ := h
  exact ⟨idx, ⟨(QuotientGroup.congr (Subgroup.center Y) (Subgroup.center X) e.symm
    (Subgroup.map_center_eq e.symm)).trans f⟩, hP⟩

theorem isAltOrChev_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsAltOrChev X) :
    IsAltOrChev Y := by
  rcases h with ⟨n, ⟨f⟩⟩ | h
  · exact Or.inl ⟨n, ⟨(QuotientGroup.congr (Subgroup.center Y) (Subgroup.center X) e.symm
      (Subgroup.map_center_eq e.symm)).trans f⟩⟩
  · exact Or.inr (isLieChar_of_equiv e _ h)

theorem good2319_of_isAltOrChev {X : Type} [Group X] [Finite X] (h : IsAltOrChev X) : Good2319 X := by
  rcases h with h | ⟨idx, hf, hP⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨idx.1.characteristic, hP, idx, hf, rfl⟩)

theorem good2319_of_equiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y)
    (h : Good2319 X) : Good2319 Y := by
  rcases h with ⟨n, ⟨f⟩⟩ | ⟨q, hq, hL⟩ | hA
  · exact Or.inl ⟨n, ⟨(QuotientGroup.congr (Subgroup.center Y) (Subgroup.center X) e.symm
      (Subgroup.map_center_eq e.symm)).trans f⟩⟩
  · exact Or.inr (Or.inl ⟨q, hq, isLieChar_of_equiv e _ hL⟩)
  · refine Or.inr (Or.inr fun A hAel => ?_)
    set ψ : MulAut Y →* MulAut X := (MulAut.congr e.symm).toMonoidHom with hψ
    have hinj : Function.Injective ψ := (MulAut.congr e.symm).injective
    have h1 := hA (A.map ψ) (Prop115.isElemAbelian_map_of_injective ψ hinj hAel)
    rwa [pRank_map_eq_of_injective (by norm_num : 1 < 3) ψ hinj A] at h1

theorem isAltOrChev_of_quotCenter {X Y : Type} [Group X] [Group Y]
    (e : (X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y)) (h : IsAltOrChev X) : IsAltOrChev Y := by
  rcases h with ⟨n, ⟨f⟩⟩ | ⟨idx, ⟨f⟩, hP⟩
  · exact Or.inl ⟨n, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨idx, ⟨e.symm.trans f⟩, hP⟩

end Types

section Calculus

variable {G : Type} [Group G] [Finite G]

theorem glaPLayer_gLBConj' (p : ℕ) (g : G) (X : Subgroup G) :
    GLAPLayer p (GLBConj g X) = GLBConj g (GLAPLayer p X) := by
  refine gLBConj_eq_of_forall_ge (F := GLAPLayer p) (fun g X => ?_) g X
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (glaPComponent_gLBConj hL g)

theorem mem_normalizer_hull {X H : Subgroup G} {c : G}
    (hcH : c ∈ Subgroup.normalizer (H : Set G)) (hcX : c ∈ Subgroup.normalizer (X : Set G)) :
    c ∈ Subgroup.normalizer ((⨆ g ∈ X, GLBConj g H : Subgroup G) : Set G) := by
  have key : ∀ c : G, c ∈ Subgroup.normalizer (H : Set G) → c ∈ Subgroup.normalizer (X : Set G) →
      GLBConj c (⨆ g ∈ X, GLBConj g H) ≤ ⨆ g ∈ X, GLBConj g H := by
    intro c hcH hcX
    have hcH' : GLBConj c H = H := mem_normalizer_iff_gLBConj_eq.1 hcH
    have hcX' : ∀ g ∈ X, c⁻¹ * g * c ∈ X := by
      intro g hg
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hcX) g).1 hg
      simpa [mul_assoc] using this
    rw [gLBConj_iSup_eq]
    refine iSup_le fun g => ?_
    by_cases hg : g ∈ X
    · rw [iSup_pos hg, gLBConj_gLBConj]
      have e : GLBConj (g * c) H = GLBConj (c⁻¹ * g * c) H := by
        have : g * c = c * (c⁻¹ * g * c) := by group
        rw [this, ← gLBConj_gLBConj, hcH']
      rw [e]
      exact le_iSup₂_of_le (c⁻¹ * g * c) (hcX' g hg) le_rfl
    · rw [iSup_neg hg]
      unfold GLBConj
      rw [Subgroup.map_bot]
      exact bot_le
  rw [mem_normalizer_iff_gLBConj_eq]
  apply le_antisymm (key c hcH hcX)
  have h1 := key c⁻¹ (Subgroup.inv_mem _ hcH) (Subgroup.inv_mem _ hcX)
  have h2 := gLBConj_mono c h1
  rwa [gLBConj_gLBConj_inv] at h2

theorem isSubnormal_barX_of {p : ℕ} {X J K : Subgroup G} (h : CFSG.Open.IsSubnormal J K) :
    CFSG.Open.IsSubnormal (barX p X J) (barX p X K) := by
  have h1 := isSubnormal_comap' X.subtype h
  exact isSubnormal_map' (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) h1

theorem mem_of_le_iSup_comp {Q : Type} [Group Q] [Finite Q] {X : Subgroup Q} {S : Set (Subgroup Q)}
    (hS : ∀ J ∈ S, GLAPComponent 3 X J) {L : Subgroup Q} (hL : GLAPComponent 3 X L)
    (hle : L ≤ ⨆ J ∈ S, J) : L ∈ S := by
  have hSX : ∀ J ∈ S, J ≤ X := fun J hJ => (hS J hJ).1
  have e : (⨆ J ∈ S, J : Subgroup Q) = ⨆ j : S, (j : Subgroup Q) := iSup_subtype'
  have hle' : L ≤ ⨆ j : S, j.1 := by
    rw [← e]
    exact hle
  have hbar : barX 3 X L ≤ ⨆ j : S, barX 3 X j.1 :=
    (CFSG.LocalAnalysis.GLTheoremB.barX_mono 3 hle').trans
      (barX_iSup_le_iSup (p := 3) (C := X) (ι := S) (fun j => j.1) (fun j => hSX j.1 j.2))
  obtain ⟨j, hj⟩ := layer_mem hL.2.2.1 (fun j : S => (hS j.1 j.2).2.2.1) hbar
  have := glaPComponent_unique (hS j.1 j.2) hL hj
  rw [← this]
  exact j.2

theorem exists_lift {L H : Subgroup G} (hHL : H ≤ L) {J' : Subgroup (barOf 3 L)}
    (hJ' : GLAPComponent 3 (barX 3 L H) J') :
    ∃ J : Subgroup G, GLAPComponent 3 H J ∧ barX 3 L J = J' ∧ Nonempty (barOf 3 J ≃* barOf 3 J') := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  set ψ₁ : ↥L →* barOf 3 L := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) with hψ₁
  have hker1 : ∀ S : Subgroup ↥L, Nat.Coprime 3 (Nat.card ↥(S ⊓ ψ₁.ker)) := by
    intro S
    have hkr : ψ₁.ker = GLAPPrimeCore 3 ↥L := QuotientGroup.ker_mk' _
    have h1 : Nat.card ↥(S ⊓ ψ₁.ker) ∣ Nat.card ↥(GLAPPrimeCore 3 ↥L) := by
      rw [hkr]
      exact Subgroup.card_dvd_of_le inf_le_right
    exact Nat.Coprime.coprime_dvd_right h1 (coprime_card_glaPPrimeCore L)
  have hker2 : ∀ S : Subgroup ↥L, Nat.Coprime 3 (Nat.card ↥(S ⊓ L.subtype.ker)) := by
    intro S
    rw [L.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  obtain ⟨K, hK, hKmap⟩ := exists_glaPComponent_map_eq hp ψ₁ (A := H.subgroupOf L) (hker1 _)
    (K' := J') hJ'
  subst hKmap
  have hK2 := glaPComponent_map hp L.subtype (hker2 _) hK
  have hA : (H.subgroupOf L).map L.subtype = H := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hHL]
  rw [hA] at hK2
  have hsub : (K.map L.subtype).subgroupOf L = K :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective K
  refine ⟨K.map L.subtype, hK2, ?_, ⟨?_⟩⟩
  · show ((K.map L.subtype).subgroupOf L).map ψ₁ = K.map ψ₁
    rw [hsub]
  · exact (lcEquiv hp L.subtype K (hker2 K)).symm.trans (lcEquiv hp ψ₁ K (hker1 K))

theorem barOf_equiv_of_cover {p : ℕ} [Fact p.Prime] {Y L0 : Subgroup G} (hYL : Y ≤ L0)
    (hcov : ∀ x ∈ L0, ∃ y ∈ Y, ∃ n ∈ GLAPPrimeCoreOf p L0, x = y * n)
    (hquasi : CFSG.Open.IsQuasisimple (barOf p L0)) : Nonempty (barOf p Y ≃* barOf p L0) := by
  classical
  let f : ↥Y →* (↥L0 ⧸ GLAPPrimeCore p ↥L0) :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥L0)).comp (Subgroup.inclusion hYL)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hyY, n, hn, hxyn⟩ := hcov (x : G) x.2
    refine ⟨⟨y, hyY⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hYL ⟨y, hyY⟩) : ↥L0 ⧸ GLAPPrimeCore p ↥L0) =
      QuotientGroup.mk x
    rw [QuotientGroup.eq]
    have hn' : n ∈ (GLAPPrimeCore p ↥L0).map L0.subtype := hn
    obtain ⟨n', hn'mem, hn'eq⟩ := Subgroup.mem_map.1 hn'
    have key : (Subgroup.inclusion hYL ⟨y, hyY⟩ : ↥L0)⁻¹ * x = n' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, Subtype.coe_mk]
      have hn'val : (n' : G) = n := hn'eq
      rw [hxyn, hn'val]
      group
    rw [key]
    exact hn'mem
  have hkerle : f.ker ≤ GLAPPrimeCore p ↥Y := by
    have hcop : Nat.Coprime p (Nat.card ↥f.ker) := by
      have hmap : f.ker.map (Subgroup.inclusion hYL) ≤ GLAPPrimeCore p ↥L0 := by
        rintro _ ⟨k, hk, rfl⟩
        have hk1 : f k = 1 := hk
        have hk2 : QuotientGroup.mk (Subgroup.inclusion hYL k) =
            (1 : ↥L0 ⧸ GLAPPrimeCore p ↥L0) := hk1
        exact (QuotientGroup.eq_one_iff _).1 hk2
      have hcard : Nat.card ↥(f.ker.map (Subgroup.inclusion hYL)) = Nat.card ↥f.ker :=
        Subgroup.card_map_of_injective (f := Subgroup.inclusion hYL)
          (Subgroup.inclusion_injective hYL)
      have hdvd : Nat.card ↥(f.ker.map (Subgroup.inclusion hYL)) ∣
          Nat.card ↥(GLAPPrimeCore p ↥L0) := Subgroup.card_dvd_of_le hmap
      have h2 := Nat.Coprime.coprime_dvd_right hdvd
        (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥L0))
      rw [hcard] at h2
      exact h2
    exact Lemma1313.le_glaPPrimeCore_of_normal (p := p) ↥Y (K := f.ker) inferInstance hcop
  have hkerge : GLAPPrimeCore p ↥Y ≤ f.ker := by
    intro t ht
    have hTn : (GLAPPrimeCore p ↥Y).Normal := inferInstance
    have hmapN : ((GLAPPrimeCore p ↥Y).map f).Normal := hTn.map f hsurj
    have hcop : Nat.Coprime p (Nat.card ↥((GLAPPrimeCore p ↥Y).map f)) := by
      have hdvd := Subgroup.card_map_dvd (GLAPPrimeCore p ↥Y) f
      exact Nat.Coprime.coprime_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥Y))
    have hle := Lemma1313.le_glaPPrimeCore_of_normal (p := p) (↥L0 ⧸ GLAPPrimeCore p ↥L0) hmapN hcop
    rw [Lemma1311.glaPPrimeCore_quot_eq_bot p ↥L0] at hle
    have hft : f t ∈ (GLAPPrimeCore p ↥Y).map f := Subgroup.mem_map_of_mem f ht
    exact (Subgroup.mem_bot).1 (hle hft)
  have hker : GLAPPrimeCore p ↥Y = f.ker := le_antisymm hkerge hkerle
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

theorem mem_layer_of_three_element {L0 : Subgroup G} {b u0 : G} (hbord : orderOf b = 3)
    (hnorm : GLBConj b L0 = L0) (hcomm : ∀ x ∈ L0, b * x * b⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 L0)
    (hquasi : CFSG.Open.IsQuasisimple (barOf 3 L0))
    (hu0 : u0 ∈ L0 ⊓ Subgroup.centralizer ({b} : Set G)) (hu0ord : orderOf u0 = 3) :
    u0 ∈ GLAPLayer 3 (L0 ⊓ Subgroup.centralizer ({b} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y : Subgroup G := L0 ⊓ Subgroup.centralizer ({b} : Set G) with hY
  set Z : Subgroup G := GLAPLayer 3 Y with hZ
  have hZY : Z ≤ Y := by
    rw [hZ]
    unfold GLAPLayer
    exact sSup_le fun K hK => hK.1
  obtain ⟨-, htop⟩ := Lemma1313.covering_data hbord hnorm hcomm hquasi
  obtain ⟨k, hkZ, hkn⟩ := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barX_eq_top_iff 3 hZY).1
    htop u0 hu0
  have hZn : ∀ y ∈ Y, GLBConj y Z = Z := by
    intro y hy
    rw [hZ, ← glaPLayer_gLBConj', gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hy)]
  haveI hnormal : (Z.subgroupOf Y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (n : G) ∈ GLBConj (g : G) Z := by
      rw [hZn g g.2]
      exact hn
    have h2 := mem_gLBConj.1 h1
    simpa using h2
  set n : G := k⁻¹ * u0 with hn
  have hkY : k ∈ Y := hZY hkZ
  have hnO : n ∈ GLAPPrimeCoreOf 3 Y := hkn
  have hnY : n ∈ Y := Lemma1313.glaPPrimeCoreOf_le_self Y hnO
  have hcopm : Nat.Coprime 3 (orderOf n) := by
    have hd : orderOf (⟨n, hnO⟩ : ↥(GLAPPrimeCoreOf 3 Y)) ∣ Nat.card ↥(GLAPPrimeCoreOf 3 Y) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hd
    exact Nat.Coprime.coprime_dvd_right hd (Lemma1313.coprime_card_glaPPrimeCoreOf 3 Y)
  set π := QuotientGroup.mk' (Z.subgroupOf Y) with hπ
  have hu0Y : u0 ∈ Y := hu0
  have hk1 : π ⟨k, hkY⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hkZ)
  have hsplit : π ⟨u0, hu0Y⟩ = π ⟨n, hnY⟩ := by
    have : (⟨u0, hu0Y⟩ : ↥Y) = ⟨k, hkY⟩ * ⟨n, hnY⟩ := by
      apply Subtype.ext
      simp [hn]
    rw [this, map_mul, hk1, one_mul]
  have h3 : (π ⟨u0, hu0Y⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨u0, hu0Y⟩ : ↥Y) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using (hu0ord ▸ pow_orderOf_eq_one u0)
    rw [this, map_one]
  have hm : (π ⟨u0, hu0Y⟩) ^ (orderOf n) = 1 := by
    rw [hsplit, ← map_pow]
    have : (⟨n, hnY⟩ : ↥Y) ^ (orderOf n) = 1 := by
      apply Subtype.ext
      simpa using pow_orderOf_eq_one n
    rw [this, map_one]
  have hone : orderOf (π ⟨u0, hu0Y⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcopm (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hm)
  have hπ1 : π ⟨u0, hu0Y⟩ = 1 := orderOf_eq_one_iff.1 hone
  have hmem := (QuotientGroup.eq_one_iff _).1 hπ1
  exact Subgroup.mem_subgroupOf.1 hmem

theorem isKHat_barOf_of_comp {C K : Subgroup G} (hC : CFSG.Open.IsKGroup ↥C)
    (hK : GLAPComponent 3 C K) : CFSG.LocalAnalysis.GLTheoremA.IsKHat (barOf 3 K) :=
  CFSG.LocalAnalysis.GLTheoremA.IsKHat.of_mulEquiv (quotEquivBarX Nat.prime_three hK.1 hK.2.1).symm
    (isKHat_of_component (isKGroup_barX_quotient hC) hK.2.2.1)

end Calculus

section LiftM

variable {G : Type} [Group G] [Finite G]

theorem le_cg_of_mem {B : Subgroup G} {u : G} (hBel : IsElemAbelian 3 B) (huB : u ∈ B) : B ≤ Cg u :=
  fun x hx => Subgroup.mem_centralizer_iff.2 fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]
    exact elemAbelian_comm hBel huB hx

theorem comp_le_M_of_gamma {B M : Subgroup G} {u : G} {Kc : Subgroup G}
    (hBel : IsElemAbelian 3 B) (huB : u ∈ B)
    (hnorm : ∀ E : Subgroup G, E ≤ B → 2 ≤ CFSG.Open.pRank 3 E → Subgroup.normalizer (E : Set G) ≤ M)
    (hcore : GLAPPrimeCoreOf 3 (Cg u) ≤ M) (hKc : GLAPComponent 3 (Cg u) Kc)
    (hgam : barX 3 (Cg u) Kc ≤ GLBCore 3 2 (barX 3 (Cg u) B)) : Kc ≤ M :=
  le_of_barX_le_glbCore Nat.prime_three 2 (CFSG.LocalAnalysis.GLTheoremB.isPGroup_of_isElemAbelian' hBel)
    (le_cg_of_mem hBel huB) hKc.1 hnorm hcore hgam

theorem center_eq_bot_of_standing {m p : ℕ} (hS : GLStanding G m p) : Subgroup.center G = ⊥ := by
  haveI := hS.simple
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a', b', hab⟩ := hS.nonabelian
    apply hab
    have hz : a' ∈ Subgroup.center G := by rw [h1]; exact Subgroup.mem_top a'
    exact ((Subgroup.mem_center_iff.1 hz) b').symm

theorem isKGroup_centralizer_of_standing {m p : ℕ} (hS : GLStanding G m p) {u : G} (hu : u ≠ 1) :
    CFSG.Open.IsKGroup ↥(Cg u) := by
  have hCne : Cg u ≠ ⊤ := by
    intro htop
    have hz : u ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Cg u := by rw [htop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.1 hg u (Set.mem_singleton u)).symm
    rw [center_eq_bot_of_standing hS, Subgroup.mem_bot] at hz
    exact hu hz
  exact isKGroup_of_isKProper hS.kProper hCne

theorem closure_pair_induction {H : Type*} [Group H] {P : H → Prop} {a b : H} (ha : P a) (hb : P b)
    (h1 : P 1) (hmul : ∀ x y, P x → P y → P (x * y)) (hinv : ∀ x, P x → P x⁻¹) {x : H}
    (hx : x ∈ Subgroup.closure {a, b}) : P x := by
  refine Subgroup.closure_induction (p := fun x _ => P x) ?_ h1 (fun x y _ _ => hmul x y)
    (fun x _ => hinv x) hx
  rintro x (rfl | rfl)
  · exact ha
  · exact hb

namespace Cfg

variable {m : ℕ} {B M L0 L L0b : Subgroup G} {d b u0 : G}

theorem normalizer_layer {c : G} (hc : d * c = c * d) :
    c ∈ Subgroup.normalizer (GLAPLayer 3 (Cg d) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq, ← glaPLayer_gLBConj',
    Lemma1313.gLBConj_centralizer_singleton_of_comm hc]

end Cfg

theorem barAut_inner {L : Subgroup G} {u : G} (huL : u ∈ L) (huN : u ∈ Subgroup.normalizer (L : Set G)) :
    barAut 3 L ⟨u, huN⟩ = MulAut.conj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨u, huL⟩) := by
  apply MulEquiv.ext
  intro z
  induction z using QuotientGroup.induction_on with
  | H l =>
    rw [barAut_mk, MulAut.conj_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
    all_goals (apply Subtype.ext; simp)

theorem barAut_ne_one {L L0b : Subgroup G} {b : G} (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hb3 : b ^ 3 = 1) (hq : CFSG.Open.IsQuasisimple (barOf 3 L))
    (hL0bc : GLAPComponent 3 (L ⊓ Cg b) L0b) (h5 : IsAltType 5 (barOf 3 L0b))
    (hnotPi : ¬ IsPiGroup 3 (barOf 3 L)) : barAut 3 L ⟨b, hbN⟩ ≠ 1 := by
  intro h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  set Y : Subgroup G := L ⊓ Cg b with hY
  have hYL : Y ≤ L := inf_le_left
  have hfix := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.fixedSub_barAut_eq hb3 hbN
  have htop : barX 3 L Y = ⊤ := by
    have h2 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.fixedSub (barAut 3 L ⟨b, hbN⟩) = ⊤ := by
      rw [h1]
      ext y
      simp [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.fixedSub]
    rw [h2] at hfix
    exact hfix.symm
  have hcov : ∀ x ∈ L, ∃ y ∈ Y, ∃ n ∈ GLAPPrimeCoreOf 3 L, x = y * n := by
    intro x hx
    obtain ⟨k, hk, hkn⟩ := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barX_eq_top_iff 3 hYL).1
      htop x hx
    exact ⟨k, hk, k⁻¹ * x, hkn, by group⟩
  obtain ⟨eY⟩ := barOf_equiv_of_cover hYL hcov hq
  have hYq : CFSG.Open.IsQuasisimple (barOf 3 Y) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eY.symm hq
  have hbarTop : barX 3 Y L0b = ⊤ := Lemma1313.eq_top_of_isComponentOf_quasisimple hYq hL0bc.2.2.1
  have e1 : barOf 3 L0b ≃* ↥(barX 3 Y L0b) := quotEquivBarX hp hL0bc.1 hL0bc.2.1
  have e2 : ↥(barX 3 Y L0b) ≃* barOf 3 Y :=
    (MulEquiv.subgroupCongr hbarTop).trans Subgroup.topEquiv
  have h5L : IsAltType 5 (barOf 3 L) := by
    obtain ⟨f⟩ := h5
    exact ⟨(e1.trans (e2.trans eY)).symm.trans f⟩
  exact hnotPi (isPiGroup_of_altType5 hq (Lemma1311.glaPPrimeCore_quot_eq_bot 3 ↥L) h5L)

end LiftM

theorem exists_pComp_istar {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G}
    {d : G} (h : Cex1310 G m p B M E A D T R L0 d) :
    ∃ L' : Subgroup G, GLAPComponent p (Istar p M D) L' := by
  have hp : p.Prime := GLStanding.prime h.standing
  by_contra hno
  push Not at hno
  have hempty : IsEmpty {L0 : Subgroup G // Lemma1311.SummandP p M D L0} :=
    ⟨fun x => hno _ (Lemma1311.summand_conj_pComp hp (one_mem M) x)⟩
  have hIof : Iof p M D = ⊥ := by
    rw [Lemma1311.Iof_eq_iSup_summand]
    exact iSup_of_empty _
  have hIstar : Istar p M D = ⊥ := by
    unfold Istar
    rw [hIof]
    refine le_antisymm (iSup₂_le fun g _ => ?_) bot_le
    unfold GLBConj
    rw [Subgroup.map_bot]
  have hL0I : L0 ≤ Istar p M D :=
    (h.hL0.1.trans (Sec13f.piLayer_le p _)).trans inf_le_left
  have hL0bot : L0 = ⊥ := by
    rw [hIstar] at hL0I
    exact le_bot_iff.1 hL0I
  have hcomp : IsComponentOf (barX p (piLayer p (Istar p M D ⊓ Cg d)) L0) ⊤ := h.hL0.2.2.1
  have hne := isComponentOf_ne_bot' hcomp
  apply hne
  rw [hL0bot]
  unfold barX
  rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]

end Prop1310a5b

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
