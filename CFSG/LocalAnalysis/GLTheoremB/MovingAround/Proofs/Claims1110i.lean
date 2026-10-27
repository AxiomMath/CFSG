module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110f

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110i

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  (mem_gLAPPrimeCoreOf_iff le_normalizer_gLAPPrimeCoreOf mem_normalizer_gLAPPrimeCoreOf
    card_gLAPPrimeCoreOf_coprime)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Generic

theorem eq_one_of_comm_mem_coprime {K₁ O : Subgroup G} (hO : Nat.Coprime 5 (Nat.card O))
    (hKO : K₁ ≤ Subgroup.normalizer (O : Set G)) (hs : IsSimpleGroup (barOf 5 K₁))
    (hnab : ∃ u v : barOf 5 K₁, u * v ≠ v * u) {x : G} (hxK : x ∈ K₁) (hx5 : x ^ 5 = 1)
    (hc : ∀ k ∈ K₁, x * k * x⁻¹ * k⁻¹ ∈ O) : x = 1 := by
  set O' : Subgroup ↥K₁ := O.subgroupOf K₁ with hO'
  have hO'n : O'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (hKO g.2) (n : G)).1 (Subgroup.mem_subgroupOf.1 hn)
    exact Subgroup.mem_subgroupOf.2 (by simpa using h1)
  have hO'c : Nat.Coprime 5 (Nat.card O') := by
    refine Nat.Coprime.coprime_dvd_right ?_ hO
    rw [← Subgroup.card_map_of_injective K₁.subtype_injective]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.1 hy
  have hle : O' ≤ GLAPPrimeCore 5 ↥K₁ := le_sSup ⟨hO'n, hO'c⟩
  haveI := hs
  have hZ : Subgroup.center (barOf 5 K₁) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  set π := QuotientGroup.mk' (GLAPPrimeCore 5 ↥K₁) with hπ
  have hcen : π ⟨x, hxK⟩ ∈ Subgroup.center (barOf 5 K₁) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 5 ↥K₁) w
    have hk : (⟨x, hxK⟩ * k * (⟨x, hxK⟩ : ↥K₁)⁻¹ * k⁻¹ : ↥K₁) ∈ GLAPPrimeCore 5 ↥K₁ :=
      hle (Subgroup.mem_subgroupOf.2 (by simpa using hc k k.2))
    have h1 : π (⟨x, hxK⟩ * k * (⟨x, hxK⟩ : ↥K₁)⁻¹ * k⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hk
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π k * π ⟨x, hxK⟩
        = (π ⟨x, hxK⟩ * π k * (π ⟨x, hxK⟩)⁻¹ * (π k)⁻¹)⁻¹ * (π ⟨x, hxK⟩ * π k) := by group
      _ = π ⟨x, hxK⟩ * π k := by rw [h1, inv_one, one_mul]
  rw [hZ, Subgroup.mem_bot] at hcen
  have hxO : (⟨x, hxK⟩ : ↥K₁) ∈ GLAPPrimeCore 5 ↥K₁ := (QuotientGroup.eq_one_iff _).1 hcen
  have hx5' : (⟨x, hxK⟩ : ↥K₁) ^ 5 = 1 := Subtype.ext (by simpa using hx5)
  have h1 := Claims1110.eq_one_of_dvd_coprime
    (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥K₁)
    (orderOf_dvd_of_pow_eq_one hx5') (Subgroup.orderOf_dvd_natCard _ hxO)
  exact congrArg Subtype.val h1

theorem comm_mem_core_of_ne_pComponent {X L L' : Subgroup G} (hL : GLAPComponent 5 X L) (hL' : GLAPComponent 5 X L')
    (hne : L ≠ L') {x y : G} (hx : x ∈ L) (hy : y ∈ L') :
    x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 5 X := by
  have hbne : barX 5 X L ≠ barX 5 X L' := fun h => hne (glaPComponent_unique hL hL' h)
  have hc : ⁅barX 5 X L, barX 5 X L'⁆ = ⊥ := Sec13e.commute_of_isComponentOf hL.2.2.1 hL'.2.2.1 hbne
  have hxX : x ∈ X := hL.1 hx
  have hyX : y ∈ X := hL'.1 hy
  set π := QuotientGroup.mk' (GLAPPrimeCore 5 ↥X) with hπ
  have hmem : ⁅π ⟨x, hxX⟩, π ⟨y, hyX⟩⁆ ∈ ⁅barX 5 X L, barX 5 X L'⁆ :=
    Subgroup.commutator_mem_commutator ⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      ⟨⟨y, hyX⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  rw [hc, Subgroup.mem_bot, commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
    ← map_mul] at hmem
  have h1 : (⟨x, hxX⟩ * ⟨y, hyX⟩ * (⟨x, hxX⟩ : ↥X)⁻¹ * (⟨y, hyX⟩ : ↥X)⁻¹ : ↥X) ∈ GLAPPrimeCore 5 ↥X :=
    (QuotientGroup.eq_one_iff _).1 hmem
  rw [mem_gLAPPrimeCoreOf_iff]
  exact ⟨_, h1⟩

@[expose] def centModIn (R L : Subgroup G) : Subgroup G where
  carrier := {r | r ∈ R ∧ r ∈ Subgroup.normalizer (L : Set G) ∧
    ∀ l ∈ L, l * r * l⁻¹ * r⁻¹ ∈ GLAPPrimeCoreOf 5 L}
  mul_mem' := by
    rintro r s ⟨hrR, hrN, hr⟩ ⟨hsR, hsN, hs⟩
    refine ⟨R.mul_mem hrR hsR, Subgroup.mul_mem _ hrN hsN, fun l hl => ?_⟩
    have h2 : r * (l * s * l⁻¹ * s⁻¹) * r⁻¹ ∈ GLAPPrimeCoreOf 5 L :=
      (Subgroup.mem_normalizer_iff.1 (mem_normalizer_gLAPPrimeCoreOf 5 hrN) _).1 (hs l hl)
    have e : l * (r * s) * l⁻¹ * (r * s)⁻¹ =
        (l * r * l⁻¹ * r⁻¹) * (r * (l * s * l⁻¹ * s⁻¹) * r⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hr l hl) h2
  one_mem' := ⟨R.one_mem, Subgroup.one_mem _, fun l _ => by
    rw [mul_one, mul_inv_cancel, inv_one, mul_one]
    exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro r ⟨hrR, hrN, hr⟩
    refine ⟨R.inv_mem hrR, Subgroup.inv_mem _ hrN, fun l hl => ?_⟩
    have h1 : r⁻¹ * (l * r * l⁻¹ * r⁻¹)⁻¹ * r⁻¹⁻¹ ∈ GLAPPrimeCoreOf 5 L :=
      (Subgroup.mem_normalizer_iff.1 (mem_normalizer_gLAPPrimeCoreOf 5 (Subgroup.inv_mem _ hrN)) _).1
        (Subgroup.inv_mem _ (hr l hl))
    have e : l * r⁻¹ * l⁻¹ * r⁻¹⁻¹ = r⁻¹ * (l * r * l⁻¹ * r⁻¹)⁻¹ * r⁻¹⁻¹ := by group
    rw [e]
    exact h1

theorem mem_centModIn {R L : Subgroup G} {r : G} :
    r ∈ centModIn R L ↔ r ∈ R ∧ r ∈ Subgroup.normalizer (L : Set G) ∧
      ∀ l ∈ L, l * r * l⁻¹ * r⁻¹ ∈ GLAPPrimeCoreOf 5 L := Iff.rfl

theorem conj_mem_centModIn {R L : Subgroup G} (hRL : R ≤ Subgroup.normalizer (L : Set G)) {g c : G}
    (hg : g ∈ R) (hc : c ∈ centModIn R L) : g * c * g⁻¹ ∈ centModIn R L := by
  obtain ⟨hcR, hcN, hcL⟩ := mem_centModIn.1 hc
  refine mem_centModIn.2 ⟨R.mul_mem (R.mul_mem hg hcR) (R.inv_mem hg),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hRL hg) hcN) (Subgroup.inv_mem _ (hRL hg)), fun l hl => ?_⟩
  have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hRL hg)) l).1 hl
  have h1 : g * ((g⁻¹ * l * g⁻¹⁻¹) * c * (g⁻¹ * l * g⁻¹⁻¹)⁻¹ * c⁻¹) * g⁻¹ ∈ GLAPPrimeCoreOf 5 L :=
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_gLAPPrimeCoreOf 5 (hRL hg)) _).1 (hcL _ hl')
  have e : l * (g * c * g⁻¹) * l⁻¹ * (g * c * g⁻¹)⁻¹ =
      g * ((g⁻¹ * l * g⁻¹⁻¹) * c * (g⁻¹ * l * g⁻¹⁻¹)⁻¹ * c⁻¹) * g⁻¹ := by group
  rw [e]
  exact h1

theorem le_normalizer_pComponent_of_centralizes {M L K₁ A₀ R : Subgroup G} (hL : GLAPComponent 5 M L)
    (hK₁L : K₁ ≤ L) (hK₁M : K₁ ≤ M) (hs : IsSimpleGroup (barOf 5 K₁))
    (hnab : ∃ u v : barOf 5 K₁, u * v ≠ v * u) (hA₀K₁ : A₀ ≤ K₁) (hA₀el : IsElemAbelian 5 A₀)
    (hA₀ : A₀ ≠ ⊥) (hRM : R ≤ M) (hRA₀ : ∀ r ∈ R, ∀ x ∈ A₀, r * x = x * r) :
    R ≤ Subgroup.normalizer (L : Set G) := by
  intro r hr
  rw [mem_normalizer_iff_gLBConj_eq]
  by_contra hne
  have hL' : GLAPComponent 5 M (GLBConj r L) := by
    have h1 := glaPComponent_gLBConj hL r
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hRM hr))] at h1
  obtain ⟨⟨x, hxA⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA₀
  have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hxL' : x ∈ GLBConj r L := by
    rw [mem_gLBConj]
    have e : r * x * r⁻¹ = x := by rw [hRA₀ r hr x hxA, mul_inv_cancel_right]
    rw [e]
    exact hK₁L (hA₀K₁ hxA)
  exact hx1' (eq_one_of_comm_mem_coprime (card_gLAPPrimeCoreOf_coprime 5 M)
    (hK₁M.trans (le_normalizer_gLAPPrimeCoreOf 5 M)) hs hnab (hA₀K₁ hxA) (hA₀el.2 x hxA)
    (fun k hk => comm_mem_core_of_ne_pComponent hL' hL hne hxL' (hK₁L hk)))

theorem eq_one_of_centralizes_bar {L K₁ A₀ R : Subgroup G} (hK₁L : K₁ ≤ L) (hs : IsSimpleGroup (barOf 5 K₁))
    (hnab : ∃ u v : barOf 5 K₁, u * v ≠ v * u) (hA₀K₁ : A₀ ≤ K₁) (hA₀el : IsElemAbelian 5 A₀)
    (hRp : IsPGroup 5 ↥R) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hZ : omegaOne 5 (centerOf R) ≤ A₀) {r : G} (hr : r ∈ R)
    (hc : ∀ l ∈ L, l * r * l⁻¹ * r⁻¹ ∈ GLAPPrimeCoreOf 5 L) : r = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set C := centModIn R L with hC
  have hCR : C ≤ R := fun x hx => hx.1
  have hCn : (C.subgroupOf R).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCR]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact fun hc => conj_mem_centModIn hRL hg hc
    · intro hc
      have := conj_mem_centModIn hRL (R.inv_mem hg) hc
      simpa [mul_assoc] using this
  by_contra hr1
  have hCne : C ≠ ⊥ := by
    intro hb
    have hrC : r ∈ C := mem_centModIn.2 ⟨hr, hRL hr, hc⟩
    rw [hb, Subgroup.mem_bot] at hrC
    exact hr1 hrC
  obtain ⟨z, hzC, hzZ, hz1⟩ := Claims1110b.exists_mem_omegaOne_centerOf hRp hCR hCn hCne
  have hzA : z ∈ A₀ := hZ hzZ
  refine hz1 (eq_one_of_comm_mem_coprime (card_gLAPPrimeCoreOf_coprime 5 L)
    (hK₁L.trans (le_normalizer_gLAPPrimeCoreOf 5 L)) hs hnab (hA₀K₁ hzA) (hA₀el.2 z hzA) fun k hk => ?_)
  have h1 := Subgroup.inv_mem _ ((mem_centModIn.1 hzC).2.2 k (hK₁L hk))
  have e : (k * z * k⁻¹ * z⁻¹)⁻¹ = z * k * z⁻¹ * k⁻¹ := by group
  rwa [e] at h1

theorem comm_mem_of_centMod {L : Subgroup G} {r : G} (h : CFSG.Yardstones.Md0ec50421ce4.CentMod 5 L r) :
    ∀ l ∈ L, l * r * l⁻¹ * r⁻¹ ∈ GLAPPrimeCoreOf 5 L := fun l hl => by
  have h1 : ⁅l, r⁆ ∈ (⁅L, Subgroup.zpowers r⁆ : Subgroup G) :=
    Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers r)
  have h2 := h.2 h1
  rwa [commutatorElement_def] at h2

end Generic

section Single

@[expose] def InputD4UpRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), CFSG.Open.IsKGroup ↥Y →
    ∀ L : Subgroup G, GLAPComponent 5 Y L →
    ∀ x : G, x ∈ Y → x ∈ Subgroup.normalizer (L : Set G) → x ^ 5 = 1 →
      ¬ CFSG.Yardstones.Md0ec50421ce4.CentMod 5 L x →
    ∀ K₁ : Subgroup G, GLAPComponent 5 (L ⊓ Subgroup.centralizer ({x} : Set G)) K₁ →
      IsSimpleGroup (barOf 5 K₁) → CFSG.Models.LieModel (barOf 5 K₁) .POmegaPlus 4 2 1 →
    ∀ R : Subgroup G, R ≤ Y → R ≤ Subgroup.normalizer (L : Set G) → IsPGroup 5 ↥R → x ∈ R →
      (∀ r ∈ R, CFSG.Yardstones.Md0ec50421ce4.CentMod 5 L r → r = 1) → 4 ≤ CFSG.Open.pRank 5 R →
    ∃ F : Subgroup G, F ≤ Y ∧ IsElemAbelian 5 F ∧ x ∈ F ∧ 5 ^ 4 ≤ Nat.card ↥F

theorem step6_false_of_single (h119 : Lemma119Statement) (hres : InputD4UpRank) {m p : ℕ} {B M E A : Subgroup G}
    {a : G} {K : Subgroup G} (h : Cex117 G m p B M E A a K) (hb : Type117b p K) {R : Subgroup G}
    (hR : IsSylowIn 5 M R) (hEAR : E ⊔ A ≤ R) (hZ : omegaOne 5 (centerOf R) = E ⊓ A)
    (hAeq : A = (E ⊓ A) ⊔ Subgroup.zpowers a) (hASyl : IsSylowIn 5 (Cg a) A) {K₁ : Subgroup G}
    (hK₁ : GLAPComponent 5 (M ⊓ Cg a) K₁) (hA0K₁ : E ⊓ A ≤ K₁) (hs : IsSimpleGroup (barOf 5 K₁))
    (hnab : ∃ x y : barOf 5 K₁, x * y ≠ y * x) (hlie : CFSG.Models.LieModel (barOf 5 K₁) .POmegaPlus 4 2 1)
    {L : Subgroup G} (hL : GLAPComponent 5 M L) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (hK₁L : K₁ ≤ L) : False := by
  obtain ⟨rfl, -⟩ := hb
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  obtain ⟨hrk, -, -, -⟩ := h119 h
  have hAel : IsElemAbelian 5 A := hsc.2.2.1
  have hA0el : IsElemAbelian 5 (E ⊓ A) := l1110_isElemAbelian_of_le hsc.1.2.1 inf_le_left
  have hA0c : Nat.card ↥(E ⊓ A) = 5 ^ 2 := by rw [l1110_card_eq_pow_pRank hA0el, hrk]
  have hA0ne : E ⊓ A ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hA0c
    norm_num at hA0c
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have haA : a ∈ A := h.ha.1
  have ha5 : a ^ 5 = 1 := hAel.2 a haA
  have haR : a ∈ R := hEAR (Subgroup.mem_sup_right haA)
  have hK₁M : K₁ ≤ M := hK₁.1.trans inf_le_left
  have hRA₀ : ∀ r ∈ R, ∀ x ∈ E ⊓ A, r * x = x * r := by
    intro r hr x hx
    rw [← hZ] at hx
    exact Claims1110.comm_of_mem_centerOf (Claims1110.omegaOne_le' 5 _ hx) hr
  have hRL : R ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_pComponent_of_centralizes hL hK₁L hK₁M hs hnab hA0K₁ hA0el hA0ne hR.1 hRA₀
  have hfaith : ∀ r ∈ R, CFSG.Yardstones.Md0ec50421ce4.CentMod 5 L r → r = 1 := fun r hr hc =>
    eq_one_of_centralizes_bar hK₁L hs hnab hA0K₁ hA0el hR.2.1 hRL hZ.le hr (comm_mem_of_centMod hc)
  have hnc : ¬ CFSG.Yardstones.Md0ec50421ce4.CentMod 5 L a := fun hc => h.ha.2 (hfaith a haR hc)
  have hK₁' : GLAPComponent 5 (L ⊓ Subgroup.centralizer ({a} : Set G)) K₁ :=
    glaPComponent_of_le hp hK₁ (le_inf hK₁L (hK₁.1.trans inf_le_right)) (inf_le_inf_right _ hL.1)
  have hrank : 4 ≤ CFSG.Open.pRank 5 R := by
    have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS.standing hS.bOne hS.pre
    have hBel : IsElemAbelian 5 B := hS.bOne.1.1
    obtain ⟨y, -, T, hTp, hTM, hRT, hBT⟩ :=
      exists_conj_le_pGroup' hR.1 hR.2.1 hBM (Claims1110.isPGroup_of_elemAb hBel)
    have hTR : T = R := hR.2.2 T hTM hTp hRT
    rw [hTR] at hBT
    have hF₀el : IsElemAbelian 5 (GLBConj y B) := Claims1110.isElemAbelian_conj y hBel
    have hF₀c : Nat.card ↥(GLBConj y B) = 5 ^ m := by
      rw [Claims1110.card_conj, hS.standing.card_eq hS.bOne]
    exact hS.standing.four_le.trans (CFSG.SectionRank.le_pRank (by norm_num) hBT hF₀el hF₀c)
  have hMK : CFSG.Open.IsKGroup ↥M :=
    h.standing.kProper.isKGroup M (isTwoLocal_ne_top h.standing h.pre.1.1)
  obtain ⟨F, -, hFel, haF, hF4⟩ :=
    hres G M hMK L hL a (hAM haA) haL ha5 hnc K₁ hK₁' hs hlie R hR.1 hRL hR.2.1 haR hfaith hrank
  have hFC : F ≤ Cg a := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hFel hf haF)
  have hFA := Claims1110.card_le_of_isSylowIn hASyl hFC (Claims1110.isPGroup_of_elemAb hFel)
  have hcomm : ∀ x ∈ E ⊓ A, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := fun x hx y hy =>
    elemAbelian_comm hAel (Subgroup.mem_inf.1 hx).2 ((Subgroup.zpowers_le.2 haA) hy)
  have hAc := Claims1110e.card_sup_mul_card_inf_of_commute' (E ⊓ A) (Subgroup.zpowers a) hcomm
  rw [← hAeq, hA0c, Nat.card_zpowers, Claims1110.orderOf_a h] at hAc
  have hpos : 0 < Nat.card ↥((E ⊓ A) ⊓ Subgroup.zpowers a) := Nat.card_pos
  have hA125 : Nat.card A ≤ 5 ^ 3 := by nlinarith
  have : (5 : ℕ) ^ 4 ≤ 5 ^ 3 := hF4.trans (hFA.trans hA125)
  norm_num at this

end Single

section Main

@[expose] def Step6WreathClaim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G},
    Cex117 G m p B M E A a K → Type117b p K →
    ∀ R : Subgroup G, IsSylowIn 5 M R → E ⊔ A ≤ R → IsSylowIn 5 ⊤ R →
      omegaOne 5 (centerOf R) = E ⊓ A → A = (E ⊓ A) ⊔ Subgroup.zpowers a → E ⊓ A = A ⊓ K →
      IsSylowIn 5 (Cg a) A → Cg a ≤ Subgroup.normalizer (K : Set G) →
      Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M →
      (∀ e ∈ E ⊓ A, e ≠ 1 → GLAPLayer 5 (K ⊓ Cg e) ≤ M) → GLAPPrimeCoreOf 5 K ≤ M →
      ((K ⊓ M).subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K)) =
        Claims1110b.gammaK0 (((E ⊓ A).subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K))) →
      ∀ K₁ : Subgroup G, GLAPComponent 5 (M ⊓ Cg a) K₁ → K₁ ≤ K ⊓ M → E ⊓ A ≤ K₁ →
        IsSimpleGroup (barOf 5 K₁) → (∃ x y : barOf 5 K₁, x * y ≠ y * x) →
        CFSG.Models.LieModel (barOf 5 K₁) .POmegaPlus 4 2 1 →
      ∀ 𝒞 : Set (Subgroup G), (∀ L ∈ 𝒞, GLAPComponent 5 M L) → K₁ ≤ ⨆ L ∈ 𝒞, L →
        (∀ L ∈ 𝒞, ∀ e ∈ Subgroup.zpowers a, GLBConj e L ∈ 𝒞) →
        (∀ L ∈ 𝒞, ∀ L' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers a, GLBConj e L = L') →
        (∀ L ∈ 𝒞, GLBConj a L ≠ L) → False

theorem step6K1Claim_of_wreath (h119 : Lemma119Statement)
    (h1834 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4) (hres : InputD4UpRank)
    (hW : Step6WreathClaim) : Claims1110f.Step6K1Claim := by
  intro G _ _ m p B M E A a K h hb R hR hEAR hRG hZ hAeq hA2 hASyl hCaN hN0 hKe hOK hY K₁ hK₁ hK₁le hA0K₁ hs
    hnab hlie
  obtain ⟨rfl, hfi⟩ := hb
  have hp : Nat.Prime 5 := by norm_num
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have haM : a ∈ M := hAM h.ha.1
  have ha5 : a ^ 5 = 1 := hsc.2.2.1.2 a h.ha.1
  have hMK : CFSG.Open.IsKGroup ↥M :=
    h.standing.kProper.isKGroup M (isTwoLocal_ne_top h.standing h.pre.1.1)
  have hcent : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨𝒞, h𝒞, h𝒞eq, h𝒞st, h𝒞tr⟩ := h1834 G M hMK 5 hp (Subgroup.zpowers a)
    (Subgroup.zpowers_le.2 haM) (CFSG.Open.isElemAbelian_zpowers ha5) K₁ (by rw [hcent]; exact hK₁)
  have hK₁𝒞 : K₁ ≤ ⨆ L ∈ 𝒞, L := by
    rw [h𝒞eq]
    refine le_trans ?_ (le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) le_rfl)
    rw [gLBConj_one]
  by_cases hcase : ∃ L ∈ 𝒞, GLBConj a L = L
  · obtain ⟨L, hL𝒞, haL⟩ := hcase
    have haN : a ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_gLBConj_eq.2 haL
    have hall : ∀ L' ∈ 𝒞, L' = L := by
      intro L' hL'
      obtain ⟨e, he, heL⟩ := h𝒞tr L hL𝒞 L' hL'
      rw [← heL]
      exact mem_normalizer_iff_gLBConj_eq.1 ((Subgroup.zpowers_le.2 haN) he)
    have hK₁L : K₁ ≤ L := hK₁𝒞.trans (iSup₂_le fun L' hL' => (hall L' hL').le)
    exact step6_false_of_single h119 hres h ⟨rfl, hfi⟩ hR hEAR hZ hAeq hASyl hK₁ hA0K₁ hs hnab hlie
      (h𝒞 L hL𝒞) haN hK₁L
  · push Not at hcase
    exact hW h ⟨rfl, hfi⟩ R hR hEAR hRG hZ hAeq hA2 hASyl hCaN hN0 hKe hOK hY K₁ hK₁ hK₁le hA0K₁ hs hnab hlie
      𝒞 h𝒞 hK₁𝒞 h𝒞st h𝒞tr hcase

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110i
