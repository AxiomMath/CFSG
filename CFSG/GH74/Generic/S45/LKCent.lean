module

public import CFSG.GH74.Generic.S45.KFactsProof
public import CFSG.GH74.GLS.TwoThin.ClassCongr
public import CFSG.Timmesfeld.Final.Simple

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint CFSG.GH74.GLS Subgroup
open scoped commutatorElement

@[expose] def GoodL2 (F : Type) [Group F] : Prop :=
  IsSimpleGroup F ∧ (∃ a b : F, a * b ≠ b * a) ∧ HasL2Model F Odd

theorem GoodL2.of_mulEquiv {F F' : Type} [Group F] [Group F'] (e : F ≃* F') (h : GoodL2 F) :
    GoodL2 F' := by
  obtain ⟨hs, ⟨a, b, hab⟩, hL⟩ := h
  refine ⟨?_, ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul]; exact h'))⟩,
    CFSG.GH74.GLS.TwoThin.hasL2Model_of_mulEquiv e hL⟩
  exact (MulEquiv.isSimpleGroup_congr e).1 hs

@[expose] def KCent (K : Type) [Group K] : Prop :=
  ∀ s : K, orderOf s = 2 →
    GoodL2 ↥⁅centralizer ({s} : Set K), centralizer ({s} : Set K)⁆

section Data

variable {K : Type} [Group K]

theorem map_conj_centralizer (g s : K) :
    (centralizer ({s} : Set K)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * s * g⁻¹} : Set K) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y * s = s * y := mem_centralizer_singleton_iff.1 hy
    rw [mem_centralizer_singleton_iff]
    show g * y * g⁻¹ * (g * s * g⁻¹) = g * s * g⁻¹ * (g * y * g⁻¹)
    calc g * y * g⁻¹ * (g * s * g⁻¹) = g * (y * s) * g⁻¹ := by group
      _ = g * (s * y) * g⁻¹ := by rw [hy']
      _ = g * s * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hx
    have hx' : x * (g * s * g⁻¹) = g * s * g⁻¹ * x := mem_centralizer_singleton_iff.1 hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      calc g⁻¹ * x * g * s = g⁻¹ * (x * (g * s * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * s * g⁻¹) * x) * g := by rw [hx']
        _ = s * (g⁻¹ * x * g) := by group
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem comm_mul_left_of_commute {t a b : K} (hta : t * a = a * t) (htb : t * b = b * t) :
    ⁅t * a, b⁆ = ⁅a, b⁆ := by
  have hc : t * (a * b * a⁻¹) = (a * b * a⁻¹) * t :=
    (((show Commute t a from hta).mul_right (show Commute t b from htb)).mul_right
      (show Commute t a from hta).inv_right).eq
  simp only [commutatorElement_def]
  calc t * a * b * (t * a)⁻¹ * b⁻¹ = (t * (a * b * a⁻¹) * t⁻¹) * b⁻¹ := by group
    _ = ((a * b * a⁻¹) * t * t⁻¹) * b⁻¹ := by rw [hc]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_mul_right_of_commute {t a b : K} (hta : t * a = a * t) (htb : t * b = b * t) :
    ⁅a, t * b⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv (t * b) a, comm_mul_left_of_commute htb hta, commutatorElement_inv]

theorem mem_or_mul_mem_of_data {t : K} (ht : orderOf t = 2) {F : Subgroup K}
    (hF : F ≤ centralizer ({t} : Set K)) (hC : centralizer ({t} : Set K) = zpowers t ⊔ F)
    {g : K} (hg : g ∈ centralizer ({t} : Set K)) : g ∈ F ∨ t * g ∈ F := by
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht, pow_two] at this
    exact this
  have h1 : ∀ f' ∈ F, t * f' * t⁻¹ = f' := fun f' hf' => by
    have := mem_centralizer_singleton_iff.1 (hF hf')
    calc t * f' * t⁻¹ = f' * t * t⁻¹ := by rw [← this]
      _ = f' := by group
  have hnorm : zpowers t ≤ normalizer (F : Set K) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro f
    constructor
    · intro hf
      rw [h1 f hf]
      exact hf
    · intro hf
      have h2 := h1 _ hf
      have h3 : t * (t * f * t⁻¹) * t⁻¹ = f := by
        calc t * (t * f * t⁻¹) * t⁻¹ = (t * t) * f * (t⁻¹ * t⁻¹) := by group
          _ = f := by rw [← mul_inv_rev, ht2, inv_one]; group
      rw [h3] at h2
      rw [h2]
      exact hf
  rw [hC, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hnorm, Set.mem_mul] at hg
  obtain ⟨a, ha, f, hf, rfl⟩ := hg
  rcases (CFSG.Walter.JT.mem_zpowers_of_orderOf_eq_two ht).1 ha with rfl | rfl
  · left
    rwa [one_mul]
  · right
    rwa [← mul_assoc, ht2, one_mul]

theorem commutator_centralizer_eq_of_data {t : K} (ht : orderOf t = 2) {F : Subgroup K}
    (hF : F ≤ centralizer ({t} : Set K)) (hC : centralizer ({t} : Set K) = zpowers t ⊔ F)
    (hperf : ⁅F, F⁆ = F) : ⁅centralizer ({t} : Set K), centralizer ({t} : Set K)⁆ = F := by
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht, pow_two] at this
    exact this
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hcomm : ∀ g ∈ centralizer ({t} : Set K), t * g = g * t := fun g hg =>
      (mem_centralizer_singleton_iff.1 hg).symm
    have key : ∀ g ∈ centralizer ({t} : Set K), ∃ f ∈ F, g = f ∨ g = t * f := by
      intro g hg
      rcases mem_or_mul_mem_of_data ht hF hC hg with h | h
      · exact ⟨g, h, Or.inl rfl⟩
      · exact ⟨t * g, h, Or.inr (by rw [← mul_assoc, ht2, one_mul])⟩
    obtain ⟨f₁, hf₁, h₁⟩ := key g₁ hg₁
    obtain ⟨f₂, hf₂, h₂⟩ := key g₂ hg₂
    have hf₁c : t * f₁ = f₁ * t := hcomm f₁ (hF hf₁)
    have hf₂c : t * f₂ = f₂ * t := hcomm f₂ (hF hf₂)
    have e1 : ⁅g₁, g₂⁆ = ⁅f₁, g₂⁆ := by
      rcases h₁ with rfl | rfl
      · rfl
      · exact comm_mul_left_of_commute hf₁c (hcomm g₂ hg₂)
    have e2 : ⁅f₁, g₂⁆ = ⁅f₁, f₂⁆ := by
      rcases h₂ with rfl | rfl
      · rfl
      · exact comm_mul_right_of_commute hf₁c hf₂c
    rw [e1, e2]
    have : ⁅f₁, f₂⁆ ∈ ⁅F, F⁆ := commutator_mem_commutator hf₁ hf₂
    rwa [hperf] at this
  · calc F = ⁅F, F⁆ := hperf.symm
      _ ≤ _ := Subgroup.commutator_mono hF hF


theorem isPerfect_of_isSimpleGroup_of_nonabelian {F : Type} [Group F] (hs : IsSimpleGroup F)
    (hnab : ∃ a b : F, a * b ≠ b * a) : Group.IsPerfect F := by
  refine ⟨?_⟩
  rcases hs.eq_bot_or_eq_top_of_normal (commutator F) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (((commutator_eq_bot_iff F).1 h).is_comm.comm a b)
  · exact h

theorem kCent_of_data {t : K} (ht : orderOf t = 2) {F : Subgroup K}
    (hF : F ≤ centralizer ({t} : Set K)) (hC : centralizer ({t} : Set K) = zpowers t ⊔ F)
    (hgood : GoodL2 ↥F) (hconj : ∀ s : K, orderOf s = 2 → ∃ g : K, g * s * g⁻¹ = t) :
    KCent K := by
  intro s hs
  obtain ⟨g, hg⟩ := hconj s hs
  have hperf : ⁅F, F⁆ = F := by
    have := isPerfect_of_isSimpleGroup_of_nonabelian hgood.1 hgood.2.1
    exact Subgroup.isPerfect_iff.1 this
  have hcomm := commutator_centralizer_eq_of_data ht hF hC hperf
  have hmap : (⁅centralizer ({s} : Set K), centralizer ({s} : Set K)⁆).map
      (MulAut.conj g).toMonoidHom = F := by
    rw [Subgroup.map_commutator, map_conj_centralizer, hg, hcomm]
  let e : ↥⁅centralizer ({s} : Set K), centralizer ({s} : Set K)⁆ ≃* ↥F :=
    (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact GoodL2.of_mulEquiv e.symm hgood

theorem KCent.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (h : KCent K) :
    KCent K' := by
  intro s' hs'
  set s : K := e.symm s' with hsdef
  have hs : orderOf s = 2 := by
    rw [hsdef, MulEquiv.orderOf_eq]
    exact hs'
  have hmapC : (centralizer ({s} : Set K)).map e.toMonoidHom = centralizer ({s'} : Set K') := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y * s = s * y := mem_centralizer_singleton_iff.1 hy
      rw [mem_centralizer_singleton_iff]
      show e y * s' = s' * e y
      have : e y * e s = e s * e y := by rw [← map_mul, ← map_mul, hy']
      simpa [hsdef] using this
    · intro hx
      have hx' : x * s' = s' * x := mem_centralizer_singleton_iff.1 hx
      refine ⟨e.symm x, ?_, by simp⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul]
      simpa [hsdef] using hx'
  have hmapComm : (⁅centralizer ({s} : Set K), centralizer ({s} : Set K)⁆).map e.toMonoidHom =
      ⁅centralizer ({s'} : Set K'), centralizer ({s'} : Set K')⁆ := by
    rw [Subgroup.map_commutator, hmapC]
  let e' : ↥⁅centralizer ({s} : Set K), centralizer ({s} : Set K)⁆ ≃*
      ↥⁅centralizer ({s'} : Set K'), centralizer ({s'} : Set K')⁆ :=
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmapComm)
  exact GoodL2.of_mulEquiv e' (h s hs)

theorem lieModel_of_mulEquiv_psl2 {F : Type} [Group F] (p f : ℕ) [Fact p.Prime] (h5 : 5 ≤ p ^ f)
    (e : F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) :
    LieModel F .PSL 2 p f :=
  Or.inl ⟨by decide, CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv F p f h5 e⟩

theorem goodL2_of_mulEquiv_psl2
    {F : Type} [Group F] (p f : ℕ) [hp : Fact p.Prime] (hodd : Odd p)
    (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (e : F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) : GoodL2 F := by
  have hL := lieModel_of_mulEquiv_psl2 p f h5 e
  have hs : IsSimpleGroup F := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hL
  refine ⟨hs, ?_, p, f, hp.out, hf, hodd.pow, hL⟩
  by_contra hcon
  push Not at hcon
  let _ : CommGroup F := { ‹Group F› with mul_comm := fun a b => hcon a b }
  have hprime := IsSimpleGroup.prime_card (α := F)
  have hKc : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hOdd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, hp.out, hodd, hf, hKc⟩
  rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.psl2_card_formula _ hOdd, hKc] at hprime
  obtain ⟨k, hk⟩ := hodd.pow (n := f)
  have hk2 : 2 ≤ k := by omega
  have hsq : (p ^ f) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    apply Nat.sub_eq_of_eq_add
    rw [hk]
    ring
  have e2 : p ^ f * ((p ^ f) ^ 2 - 1) = 2 * (p ^ f * (2 * (k * (k + 1)))) := by
    rw [hsq]
    ring
  rw [e2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at hprime
  refine Nat.not_prime_mul (a := p ^ f) (b := 2 * (k * (k + 1))) (by omega) ?_ hprime
  have : 12 ≤ 2 * (k * (k + 1)) := by nlinarith
  omega

end Data

theorem goodL2_alt5 :
    GoodL2 (alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hGF : Nat.card (GaloisField 5 1) = 5 := by
    rw [GaloisField.card 5 1 one_ne_zero, pow_one]
  obtain ⟨e⟩ := (CFSG.LinearGroups.five_field_linear_two_alternating_five_model (GaloisField 5 1)
    hGF).1
  exact goodL2_of_mulEquiv_psl2 5 1 (by decide) le_rfl (by norm_num) e.symm

theorem kCent_walterJ1 :
    KCent ↥CFSG.Open.walterJ1 := by
  have h := CFSG.Walter.J1Props.jankoHyp
  have hF : GoodL2 ↥h.F := GoodL2.of_mulEquiv h.iso.symm goodL2_alt5
  exact kCent_of_data h.orderOf_t h.le_centralizer h.centralizer_eq hF
    (fun s hs => h.exists_conj_eq_t hs)

theorem kCent_of_isSporadic_J1
    {K : Type} [Group K] (h : NativeSporadic.IsSporadic K .J1) :
    KCent K := by
  obtain ⟨e⟩ := h
  exact KCent.of_mulEquiv (CFSG.Walter.walterJ1EquivNative.trans e.symm) kCent_walterJ1

open CFSG.LieType.Ree in
theorem kCent_reeGamma
    (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    KCent (ReeTag.G2.reeGamma K a) := by
  obtain ⟨h, hp3, hf3, -⟩ := CFSG.Walter.Ree.Model.small_Ree_jtHyp a ha K hK
  have hp : h.p ≠ 2 := by rw [hp3]; norm_num
  have hodd : Odd h.p := by rw [hp3]; decide
  have hF : GoodL2 ↥h.F :=
    goodL2_of_mulEquiv_psl2 h.p h.f hodd (by rw [hf3]; omega) h.five_lt.le h.iso
  exact kCent_of_data h.orderOf_t h.le_centralizer h.centralizer_eq hF
    (fun s hs => h.exists_conj_eq_t hp hs)

open CFSG.LieType.Ree in
theorem kCent_of_reeModel
    {K : Type} [Group K] [Finite K] {f : ℕ}
    (hm : ReeTitsModel K .twistedG2 3 f) : KCent K := by
  obtain ⟨-, -, -, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier K 3 f hm
  obtain ⟨-, a', hfa', K', _, _, hK', hw⟩ := hm
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K' ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hK'
  obtain ⟨E⟩ := hiso a' K' hfa hK' hw
  have hK'' : Nat.card K' = 3 ^ (2 * a' + 1) := by rw [hK', hfa]
  exact KCent.of_mulEquiv E.symm (kCent_reeGamma a' ha K' hK'')

theorem kCent_of_isJ1OrRee
    {K : Type} [Group K] [Finite K] (h : IsJ1OrRee K) : KCent K := by
  rcases h with h | ⟨f, hf⟩
  · exact kCent_of_isSporadic_J1 h
  · exact kCent_of_reeModel (reeTitsModel_of_lieModel hf)

end CFSG.GH74.Generic.S45
