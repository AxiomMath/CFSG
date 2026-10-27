module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Blocks

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbedding.LieOut
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open scoped commutatorElement

@[expose] def AltIbBarAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ Jb : Subgroup G, (∃ T : Subgroup G, IsSylowTwoOf T ⊤ ∧
      Subgroup.normalizer (T : Set G) ≤ Jb) → Jb ≠ ⊤ → (p = 5 ∨ p = 7) →
    (∀ X : Subgroup G, X ≤ Jb → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X) →
    (∀ X₁ X₂ : Subgroup G, X₁ ≤ Jb → X₂ ≤ Jb → CFSG.Open.IsQuasisimple ↥X₁ →
      CFSG.Open.IsQuasisimple ↥X₂ → X₂ ≤ Subgroup.centralizer (X₁ : Set G) →
      p ∣ Nat.card X₁ → p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False) →
    ∀ x : G, x ^ p = 1 → (∀ g : G, g * x = x * g → g ∈ Jb) →
    ∀ V E : Subgroup G, V ≤ Jb → V ≤ Subgroup.centralizer ({x} : Set G) → ⁅V, V⁆ = V →
      E ≤ V → IsElemAbelian p E → Nat.card E = p ^ 2 → False

theorem altIb_reduce_to_bar (hSch : KFactCatalogSchreier) {Y : Type} [Group Y] [Finite Y]
    {L J : Subgroup Y} (hcomp : CompParabE L J) {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSqC p J) (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    {x : Y} (hxL : x ∈ L) (hxp : x ^ p = 1) (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J)
    {W : Subgroup Y} (hW : ⁅W, W⁆ = W) (hWN : W ≤ Subgroup.normalizer (L : Set Y))
    (hWx : W ≤ Subgroup.centralizer ({x} : Set Y)) {E : Subgroup Y} (hEW : E ≤ W ⊓ L)
    (hEel : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hbar : AltIbBarAt (↥L ⧸ Subgroup.center ↥L) p) : False := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  have hpar := hcomp.parab
  obtain ⟨V, hVle, hV, hEV⟩ := exists_perfect_core_of_comp hSch hp hcomp.comp hcomp.type hpZ hxL
    hW hWN hWx hEW hEp
  obtain ⟨S₀, hNS, -, hJtop⟩ := exists_sylow_parab_central hcomp
  have hVC : V ≤ Subgroup.centralizer ({x} : Set Y) := fun v hv => (hVle hv).2
  have hVJ : V ≤ J := fun v hv => by
    refine hfix v (hVle hv).1 ?_
    have := Subgroup.mem_centralizer_iff.1 (hVC hv) x (Set.mem_singleton x)
    rw [this, mul_inv_cancel_right]
  have hVL : V ≤ L := hVJ.trans hpar.1
  have hEL : E ≤ L := fun e he => (hEW he).2
  set ψ : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hψ
  set x' : ↥L := ⟨x, hxL⟩ with hx'
  have hx'p : x' ^ p = 1 := Subtype.ext (by simpa using hxp)
  refine hbar (jBar L J) ⟨_, isSylowTwoOf_top_of_sylow' S₀, hNS⟩ hJtop hp57 ?_ ?_
    (QuotientGroup.mk x') ?_ ?_ ((V.subgroupOf L).map ψ) ((E.subgroupOf L).map ψ) ?_ ?_ ?_ ?_ ?_ ?_
  ·
    intro Xb hXJ hq hd
    obtain ⟨X, hXJ', -, hXq, -, hk⟩ := exists_quasisimple_lift_of_not_dvd hpar hp hpZ hXJ hq
    exact not_sq_dvd_card_of_quasisimple hp57 hAlt hXJ' hXq ((hk 2).2 hd)
  ·
    intro Xb₁ Xb₂ h₁ h₂ hq₁ hq₂ hc hp₁ hp₂ hn₁ hn₂
    obtain ⟨X₁, h₁J, h₁L, hq₁', hm₁, hk₁⟩ := exists_quasisimple_lift_of_not_dvd hpar hp hpZ h₁ hq₁
    obtain ⟨X₂, h₂J, h₂L, hq₂', hm₂, hk₂⟩ := exists_quasisimple_lift_of_not_dvd hpar hp hpZ h₂ hq₂
    have hcomm : ∀ a ∈ X₁.subgroupOf L, ∀ b ∈ X₂.subgroupOf L,
        (QuotientGroup.mk a : ↥L ⧸ Subgroup.center ↥L) * QuotientGroup.mk b =
          QuotientGroup.mk b * QuotientGroup.mk a := by
      intro a ha b hb
      have ha' : (QuotientGroup.mk a : ↥L ⧸ Subgroup.center ↥L) ∈ Xb₁ :=
        hm₁ ▸ Subgroup.mem_map_of_mem ψ ha
      have hb' : (QuotientGroup.mk b : ↥L ⧸ Subgroup.center ↥L) ∈ Xb₂ :=
        hm₂ ▸ Subgroup.mem_map_of_mem ψ hb
      exact Subgroup.mem_centralizer_iff.1 (hc hb') _ ha'
    have hX₁perf : ⁅X₁.subgroupOf L, X₁.subgroupOf L⁆ = X₁.subgroupOf L :=
      commutator_subgroupOf_eq h₁L (commutator_eq_self_of_open_isQuasisimple hq₁')
    have hcX : X₂ ≤ Subgroup.centralizer (X₁ : Set Y) := by
      intro y₂ hy₂
      rw [Subgroup.mem_centralizer_iff]
      intro y₁ hy₁
      have := commute_of_map_commute hX₁perf hcomm ⟨y₁, h₁L hy₁⟩
        (Subgroup.mem_subgroupOf.2 hy₁) ⟨y₂, h₂L hy₂⟩ (Subgroup.mem_subgroupOf.2 hy₂)
      exact congrArg Subtype.val this
    obtain ⟨f₁, hf₁⟩ := exists_surjective_to_image h₁L hm₁
    obtain ⟨f₂, hf₂⟩ := exists_surjective_to_image h₂L hm₂
    exact false_of_commuting_noAp hp57 hAlt h₁J h₂J hq₁' hq₂' hcX
      (by simpa using (hk₁ 1).2 (by simpa using hp₁)) (by simpa using (hk₂ 1).2 (by simpa using hp₂))
      (noAp_center_quotient_of_surjective f₁ hf₁ hn₁)
      (noAp_center_quotient_of_surjective f₂ hf₂ hn₂)
  ·
    rw [← QuotientGroup.mk_pow, hx'p, QuotientGroup.mk_one]
  ·
    intro g hg
    exact fix_all_bar hp hpZ hxL hxp hfix g hg
  ·
    exact Subgroup.map_mono fun v hv => hVJ hv
  ·
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    show ψ x' * ψ v = ψ v * ψ x'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hVC (Subgroup.mem_subgroupOf.1 hv)) x
      (Set.mem_singleton x))
  ·
    rw [← Subgroup.map_commutator, commutator_subgroupOf_eq hVL hV]
  · exact Subgroup.map_mono fun e he => Subgroup.mem_subgroupOf.2 (hEV (Subgroup.mem_subgroupOf.1 he))
  ·
    have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hEel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, a, ha, rfl⟩ := a
      obtain ⟨_, b, hb, rfl⟩ := b
      apply Subtype.ext
      show ψ a * ψ b = ψ b * ψ a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm a (Subgroup.mem_subgroupOf.1 ha) b (Subgroup.mem_subgroupOf.1 hb))
    · rintro _ ⟨e, he, rfl⟩
      show ψ e ^ p = 1
      rw [← map_pow]
      have : (e : Y) ^ p = 1 := hEel.2 _ (Subgroup.mem_subgroupOf.1 he)
      have : e ^ p = 1 := Subtype.ext (by simpa using this)
      rw [this, map_one]
  ·
    rw [card_map_mk_of_pGroup hp hpZ (E := E.subgroupOf L) (fun e he => by
      have : (e : Y) ^ p = 1 := hEel.2 _ (Subgroup.mem_subgroupOf.1 he)
      exact Subtype.ext (by simpa using this)), ← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv

section Lift

variable {S G : Type*} [Group S] [Group G] {p : ℕ}

theorem exists_lift_pow_eq_one (hp : p.Prime) {π : S →* G} (hπ : Function.Surjective π)
    (hpk : ¬ p ∣ Nat.card π.ker) {v : G} (hv : v ^ p = 1) :
    ∃ t : S, π t = v ∧ t ^ p = 1 := by
  obtain ⟨t₀, rfl⟩ := hπ v
  have hzk : t₀ ^ p ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hv
  have hord : orderOf (t₀ ^ p) ∣ Nat.card π.ker := by
    have := orderOf_dvd_natCard (⟨t₀ ^ p, hzk⟩ : ↥π.ker)
    simpa [Subgroup.orderOf_mk] using this
  have hcop : Nat.Coprime p (orderOf (t₀ ^ p)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpk (h.trans hord)
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (orderOf (t₀ ^ p) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 hcop
  refine ⟨t₀ ^ ((orderOf (t₀ ^ p) : ℤ) * b), ?_, ?_⟩
  · have h1 : (π t₀) ^ (a * (p : ℤ)) = 1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, hv, one_zpow]
    have h3 : (π t₀) ^ (a * (p : ℤ) + b * (orderOf (t₀ ^ p) : ℤ)) = π t₀ := by
      rw [hab, zpow_one]
    rw [zpow_add, h1, one_mul] at h3
    rw [map_zpow, mul_comm]
    exact h3
  · calc (t₀ ^ ((orderOf (t₀ ^ p) : ℤ) * b)) ^ p
        = t₀ ^ (((orderOf (t₀ ^ p) : ℤ) * b) * (p : ℤ)) := by rw [← zpow_natCast, ← zpow_mul]
      _ = (t₀ ^ p) ^ ((orderOf (t₀ ^ p) : ℤ) * b) := by
          rw [mul_comm, zpow_mul, zpow_natCast]
      _ = ((t₀ ^ p) ^ (orderOf (t₀ ^ p) : ℤ)) ^ b := by rw [zpow_mul]
      _ = 1 := by rw [zpow_natCast, pow_orderOf_eq_one, one_zpow]

theorem exists_perfect_lift_centralizer {π : S →* G} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center S) {t : S} {V : Subgroup G} (hV : ⁅V, V⁆ = V)
    (hVC : V ≤ Subgroup.centralizer ({π t} : Set G)) :
    ∃ W : Subgroup S, ⁅W, W⁆ = W ∧ W ≤ Subgroup.centralizer ({t} : Set S) ∧ W.map π = V := by
  obtain ⟨W, hW, hWle, hWmap⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq π hker hV
    (by rw [MonoidHom.range_eq_top.2 hπ]; exact le_top)
  have hcentral : ∀ w ∈ W, ⁅w, t⁆ ∈ Subgroup.center S := by
    intro w hw
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    have hwV : π w ∈ V := by rw [← hWmap]; exact ⟨w, hw, rfl⟩
    exact (Subgroup.mem_centralizer_iff.1 (hVC hwV) (π t) (Set.mem_singleton _)).symm
  have hWC : W ≤ Subgroup.centralizer ({t} : Set S) := by
    rw [← hW]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h1 := commutator_commutator_eq_one_of_central (hcentral a ha) (hcentral b hb)
    rw [commutatorElement_eq_one_iff_commute] at h1
    exact h1.symm
  exact ⟨W, hW, hWC, hWmap⟩

variable [Finite S]

theorem exists_pLift_injective (hp : p.Prime) {π : S →* G} (hpk : ¬ p ∣ Nat.card π.ker)
    {P : Subgroup S} {Q : Subgroup G} (hP : P.map π = Q) (hQ : IsPGroup p Q) :
    ∃ R : Subgroup S, R ≤ P ∧ IsPGroup p R ∧ R.map π = Q ∧ ∀ r ∈ R, π r = 1 → r = 1 := by
  obtain ⟨R, hRP, hRp, hRmap⟩ := exists_pSubgroup_map_eq hp hP hQ
  refine ⟨R, hRP, hRp, hRmap, fun r hr h1 => ?_⟩
  obtain ⟨k, hk⟩ := hRp ⟨r, hr⟩
  have hk' : r ^ p ^ k = 1 := congrArg Subtype.val hk
  have h1' : orderOf r ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf r ∣ Nat.card π.ker := by
    have := orderOf_dvd_natCard (⟨r, MonoidHom.mem_ker.2 h1⟩ : ↥π.ker)
    simpa [Subgroup.orderOf_mk] using this
  have hcop : Nat.Coprime (orderOf r) (p ^ k) :=
    Nat.Coprime.pow_right k (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
      fun h => hpk (h.trans h2)))
  exact orderOf_eq_one_iff.1 (hcop.eq_one_of_dvd h1')

theorem exists_elemAbelian_lift (hp : p.Prime) {π : S →* G} (hpk : ¬ p ∣ Nat.card π.ker)
    {P : Subgroup S} {E : Subgroup G} (hP : P.map π = E) (hE : IsElemAbelian p E) :
    ∃ R : Subgroup S, R ≤ P ∧ IsElemAbelian p R ∧ R.map π = E ∧ Nat.card R = Nat.card E := by
  have hEp : IsPGroup p E := isPGroup_of_pow_eq_one hE.2
  obtain ⟨R, hRP, hRp, hRmap, hinj⟩ := exists_pLift_injective hp hpk hP hEp
  have hinj' : Function.Injective (π.subgroupMap R) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    have h1 : π (r : S) = 1 := congrArg Subtype.val hr
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hinj r r.2 h1)
  have hmem : ∀ a ∈ R, ∀ b ∈ R, π a = π b → a = b := by
    intro a ha b hb hab
    have h1 : π (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have := hinj _ (R.mul_mem (R.inv_mem ha) hb) h1
    exact inv_mul_eq_one.1 this
  have hπE : ∀ r ∈ R, π r ∈ E := fun r hr => hRmap ▸ Subgroup.mem_map_of_mem π hr
  refine ⟨R, hRP, ⟨⟨⟨fun a b => ?_⟩⟩, fun r hr => ?_⟩, hRmap, ?_⟩
  · apply Subtype.ext
    apply hmem _ (R.mul_mem a.2 b.2) _ (R.mul_mem b.2 a.2)
    have := hE.1.is_comm.comm ⟨π a, hπE a a.2⟩ ⟨π b, hπE b b.2⟩
    have h2 := congrArg Subtype.val this
    simpa using h2
  · apply hmem _ (R.pow_mem hr p) _ R.one_mem
    rw [map_pow, map_one]
    exact hE.2 _ (hπE r hr)
  · rw [← hRmap]
    exact Nat.card_congr (Equiv.ofBijective _ ⟨hinj', MonoidHom.subgroupMap_surjective _ R⟩)

theorem exists_lift_data (hp : p.Prime) {π : S →* G} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center S) (hpk : ¬ p ∣ Nat.card π.ker) {v : G} (hv : v ^ p = 1)
    {V E : Subgroup G} (hVC : V ≤ Subgroup.centralizer ({v} : Set G)) (hV : ⁅V, V⁆ = V)
    (hEV : E ≤ V) (hE : IsElemAbelian p E) :
    ∃ t : S, π t = v ∧ t ^ p = 1 ∧ ∃ Vh Eh : Subgroup S, ⁅Vh, Vh⁆ = Vh ∧
      Vh ≤ Subgroup.centralizer ({t} : Set S) ∧ Vh.map π = V ∧ Eh ≤ Vh ∧ IsElemAbelian p Eh ∧
      Eh.map π = E ∧ Nat.card Eh = Nat.card E := by
  obtain ⟨t, htv, htp⟩ := exists_lift_pow_eq_one hp hπ hpk hv
  obtain ⟨Vh, hVh, hVhC, hVhmap⟩ := exists_perfect_lift_centralizer hπ hker (t := t) hV
    (htv ▸ hVC)
  have hP : (Vh ⊓ E.comap π).map π = E := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      have hyV : y ∈ Vh.map π := by rw [hVhmap]; exact hEV hy
      obtain ⟨w, hw, rfl⟩ := hyV
      exact ⟨w, ⟨hw, hy⟩, rfl⟩
  obtain ⟨R, hRP, hRel, hRmap, hRcard⟩ := exists_elemAbelian_lift hp hpk hP hE
  exact ⟨t, htv, htp, Vh, R, hVh, hVhC, hVhmap, fun r hr => (hRP hr).1, hRel, hRmap, hRcard⟩

end Lift

section CentralQuotient

variable {A B : Type*} [Group A] [Group B]

noncomputable def centerQuotientEquiv (hA : Group.IsPerfect A) (f : A →* B)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center A) :
    (A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B) := by
  have hc : Subgroup.center A = ((QuotientGroup.mk' (Subgroup.center B)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hA f hf hker]
  exact (QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))

end CentralQuotient

theorem isQuasisimple_map_of_ker_le_center {S G : Type*} [Group S] [Group G] {π : S →* G}
    (hker : π.ker ≤ Subgroup.center S) {B : Subgroup S} (hB : CFSG.Open.IsQuasisimple ↥B) :
    CFSG.Open.IsQuasisimple ↥(B.map π) := by
  have hBp : Group.IsPerfect ↥B := Group.isPerfect_def.mpr hB.1
  have hf := MonoidHom.subgroupMap_surjective π B
  have hk : (π.subgroupMap B).ker ≤ Subgroup.center ↥B := fun b hb => by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker (congrArg Subtype.val hb)) (g : S))
  have : Group.IsPerfect ↥(B.map π) := Group.IsPerfect.ofSurjective hf
  have : IsSimpleGroup (↥B ⧸ Subgroup.center ↥B) := hB.2
  exact ⟨Group.IsPerfect.commutator_eq_top,
    (centerQuotientEquiv hBp (π.subgroupMap B) hf hk).symm.isSimpleGroup⟩

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
