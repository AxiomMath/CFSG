module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBTwin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open CFSG Subgroup CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement MatrixGroups

variable {J : Type} [Group J] (K : Subgroup J) [K.Normal]

theorem liftHom_range_eq [Finite J] (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range))
    (hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a) :
    (liftHom K).range = GeneralizedFitting.subgroup (rhoZ K).range := by
  set X := (rhoZ K).range with hX
  set N := (liftHom K).range with hN
  set F := GeneralizedFitting.subgroup X with hF
  have hFn : F.Normal := GeneralizedFitting.normal X
  have hNn : N.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨x, rfl⟩ g
    obtain ⟨j, rfl⟩ : ∃ j : J, (rhoZ K).rangeRestrict j = g := by
      obtain ⟨_, ⟨j, rfl⟩⟩ := g
      exact ⟨j, rfl⟩
    exact ⟨phiO K j x, liftHom_conj K j x⟩
  have : IsSimpleGroup ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)) := hq.2.1
  have eN : (K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K) ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq (ker_liftHom K hq).symm).trans
      (QuotientGroup.quotientKerEquivRange (liftHom K))
  have hNs : IsSimpleGroup N := eN.symm.isSimpleGroup
  have hNF : N ⊓ F ≠ ⊥ := by
    intro h
    have hc : ⁅N, F⁆ = ⊥ := le_bot_iff.mp (h ▸ commutator_le_inf N F)
    have hNC : N ≤ centralizer (F : Set X) := by
      intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := commutator_mem_commutator hx hy
      rw [hc, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    rw [centralizer_generalizedFitting_eq_bot hsimple hnab] at hNC
    obtain ⟨a, b, hab⟩ : ∃ a b : N, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hq.2.2
      exact ⟨eN a, eN b, fun h => hab (eN.injective (by rw [map_mul, map_mul, h]))⟩
    apply hab
    have ha : (a : X) = 1 := (mem_bot.mp (hNC a.2))
    have hb : (b : X) = 1 := (mem_bot.mp (hNC b.2))
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, hb]
  have hNFn : (N ⊓ F).Normal := inferInstance
  have hn₁ : ((N ⊓ F).subgroupOf N).Normal := hNFn.subgroupOf N
  have hn₂ : ((N ⊓ F).subgroupOf F).Normal := hNFn.subgroupOf F
  have hne₁ : (N ⊓ F).subgroupOf N ≠ ⊥ := by
    rw [Ne, subgroupOf_eq_bot]
    intro h
    apply hNF
    rw [eq_bot_iff]
    intro x hx
    exact (h.le_bot ⟨hx, (mem_inf.mp hx).1⟩ : x ∈ (⊥ : Subgroup X))
  have hne₂ : (N ⊓ F).subgroupOf F ≠ ⊥ := by
    rw [Ne, subgroupOf_eq_bot]
    intro h
    apply hNF
    rw [eq_bot_iff]
    intro x hx
    exact (h.le_bot ⟨hx, (mem_inf.mp hx).2⟩ : x ∈ (⊥ : Subgroup X))
  have h₁ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ F).subgroupOf N)).resolve_left hne₁
  have h₂ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ F).subgroupOf F)).resolve_left hne₂
  rw [subgroupOf_eq_top] at h₁ h₂
  exact le_antisymm (h₁.trans inf_le_right) (h₂.trans inf_le_left)

theorem exists_cover [Finite J] {G : Type} [Group G] [Finite G]
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* G),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : G →* E, ∀ x, π (s x) = x)
    (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K)) {β : G →* (rhoZ K).range}
    (hβ : β.range = (liftHom K).range) :
    ∃ α : G →* K ⧸ pPrimeCore 2 K, (∀ g, liftHom K (α g) = β g) ∧ Function.Surjective α ∧
      center (K ⧸ pPrimeCore 2 K) = β.ker.map α := by
  have : Group.IsPerfect (K ⧸ pPrimeCore 2 K) := hq.1
  have hβm : ∀ g, β g ∈ (liftHom K).range := fun g => hβ ▸ ⟨g, rfl⟩
  let β' : G →* (liftHom K).range := β.codRestrict _ hβm
  have hβ' : Function.Surjective β' := by
    rintro ⟨x, hx⟩
    rw [← hβ] at hx
    obtain ⟨g, rfl⟩ := hx
    exact ⟨g, rfl⟩
  have hker : (liftHom K).rangeRestrict.ker = center (K ⧸ pPrimeCore 2 K) := by
    rw [MonoidHom.ker_rangeRestrict, ker_liftHom K hq]
  obtain ⟨α, hα, hsurj, he⟩ := CFSG.LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβ'
    (liftHom K).rangeRestrict_surjective (hker.le) (hker ▸ isPGroup_center K)
  refine ⟨α, fun g => congrArg Subtype.val (hα g), hsurj, ?_⟩
  have hk : β'.ker = β.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [← hker, he, hk]

variable {Q B : Type} [Group Q] [Group B]

omit [K.Normal] in
theorem map_mem_sup_of_cover {G : Type} [Group G] (σ : Q →* B) (α : G →* Q) {β : G →* B}
    (hαβ : ∀ g, σ (α g) = β g) {S₁ S₂ : Subgroup B} {R₁ R₂ : Subgroup G} (hR₁ : ⁅R₁, R₁⁆ = R₁)
    (hR₂ : ⁅R₂, R₂⁆ = R₂) (hβ₁ : ∀ g ∈ R₁, β g ∈ S₁) (hβ₂ : ∀ g ∈ R₂, β g ∈ S₂) {c : G}
    (hc : c ∈ R₁ ⊔ R₂) : α c ∈ ⁅S₁.comap σ, S₁.comap σ⁆ ⊔ ⁅S₂.comap σ, S₂.comap σ⁆ := by
  have hle : ∀ {R : Subgroup G} {S : Subgroup B}, ⁅R, R⁆ = R → (∀ g ∈ R, β g ∈ S) →
      R.map α ≤ ⁅S.comap σ, S.comap σ⁆ := by
    intro R S hR hβ
    have h1 : R.map α ≤ S.comap σ := by
      rintro _ ⟨g, hg, rfl⟩
      rw [mem_comap, hαβ]
      exact hβ g hg
    calc R.map α = ⁅R.map α, R.map α⁆ := by rw [← map_commutator, hR]
      _ ≤ ⁅S.comap σ, S.comap σ⁆ := commutator_mono h1 h1
  have h2 : (R₁ ⊔ R₂).map α ≤ ⁅S₁.comap σ, S₁.comap σ⁆ ⊔ ⁅S₂.comap σ, S₂.comap σ⁆ := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (hle hR₁ hβ₁) (hle hR₂ hβ₂)
  exact h2 (mem_map_of_mem α hc)

theorem propB_of_twin [Finite J] (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K)) {t : J}
    {Y : Subgroup J} {ū : (rhoZ K).range} {S₁ S₂ : Subgroup (rhoZ K).range}
    (hS₁r : S₁ ≤ (liftHom K).range) (hS₂r : S₂ ≤ (liftHom K).range)
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ n)
    (e₁ : S₁ ≃* SL(2, GaloisField p n)) (e₂ : S₂ ≃* SL(2, GaloisField p n))
    (hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b = b * a) (hū : orderOf ū = 2) (hū₁ : ū ∈ S₁)
    (hū₂ : ū ∈ S₂) (hint : ∀ x, x ∈ S₁ → x ∈ S₂ → x = 1 ∨ x = ū)
    (hs₁ : S₁ ≤ centralizer ({ū} : Set (rhoZ K).range))
    (hs₁s : (S₁.subgroupOf (centralizer ({ū} : Set (rhoZ K).range))).IsSubnormal)
    (hs₂ : S₂ ≤ centralizer ({ū} : Set (rhoZ K).range))
    (hs₂s : (S₂.subgroupOf (centralizer ({ū} : Set (rhoZ K).range))).IsSubnormal)
    (hprop₁ : ActsProperly ((rhoZ K).rangeRestrict t) (Y.map (rhoZ K).rangeRestrict) S₁ ⊥)
    (hprop₂ : ActsProperly ((rhoZ K).rangeRestrict t) (Y.map (rhoZ K).rangeRestrict) S₂ ⊥)
    {c : K ⧸ pPrimeCore 2 K} (hcZ : c ∈ center (K ⧸ pPrimeCore 2 K)) (hc1 : c ≠ 1)
    (hcT : c ∈ ⁅S₁.comap (liftHom K), S₁.comap (liftHom K)⁆ ⊔
      ⁅S₂.comap (liftHom K), S₂.comap (liftHom K)⁆) :
    ∃ u : K ⧸ pPrimeCore 2 K, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (K ⧸ pPrimeCore 2 K),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₁ ⊥ ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₂ ⊥ := by
  have hker : (liftHom K).ker ≤ center (K ⧸ pPrimeCore 2 K) := (ker_liftHom K hq).le
  have hker2 : IsPGroup 2 (liftHom K).ker := ker_liftHom K hq ▸ isPGroup_center K
  have hc : liftHom K c = 1 := by
    rw [← MonoidHom.mem_ker, ker_liftHom K hq]
    exact hcZ
  obtain ⟨u, hu, -, hT₁C, hT₁c, hT₂C, hT₂c, ⟨f₁⟩, ⟨f₂⟩, hTT, hinter, hZ⟩ :=
    twin_of_lift (liftHom K) hker hker2 hS₁r hS₂r hp2 h5 e₁ e₂ hcomm hū hū₁ hū₂ hint hc hc1 hcT
      hs₁ hs₁s hs₂ hs₂s
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at h5
    · exact h
  have hF : ringChar (GaloisField p n) ≠ 2 := by
    rw [ringChar.eq (GaloisField p n) p]
    exact hp2
  have h4 : 4 ≤ Nat.card (GaloisField p n) := by
    rw [GaloisField.card p n hn.ne']
    omega
  obtain ⟨hT₁S, -⟩ := exists_sl_lift_of_split (liftHom K) hker hker2 hS₁r hF h4 e₁
  obtain ⟨hT₂S, -⟩ := exists_sl_lift_of_split (liftHom K) hker hker2 hS₂r hF h4 e₂
  exact ⟨u, hu, _, _, hT₁C, hT₁c, hT₂C, hT₂c, ⟨p, n, inferInstance, hp2, hn, ⟨f₁⟩, ⟨f₂⟩⟩, hTT,
    hinter, hZ, actsProperlyVia_lift K hq hT₁S hprop₁, actsProperlyVia_lift K hq hT₂S hprop₂⟩

end CFSG.ComponentClassification.Burgoyne.B
