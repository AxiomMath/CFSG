module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2323
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311c
import CFSG.SignalizerFunctorTheorem.Inheritance.CosetFixed
import CFSG.GH74.GLS.Balance.OResidual

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2323b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup map_fixSubgroup_le PerfectInLayer)

@[expose] def TwoInCoreLayer (p : ℕ) {S : Type*} [Group S] (β : MulAut S) : Prop :=
  ∀ x ∈ fixSubgroup β, IsPGroup 2 ↥(Subgroup.zpowers x) →
    x ∈ GLAPPrimeCoreOf p (fixSubgroup β) ⊔ GLAPLayer p (fixSubgroup β)

section GroupTheory

variable {G : Type} [Group G]

theorem isPGroup_zpowers_of_pow_eq_one {p : ℕ} {g : G} {m : ℕ} (h : g ^ (p ^ m) = 1) :
    IsPGroup p ↥(Subgroup.zpowers g) := by
  rintro ⟨y, hy⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨m, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

open scoped Pointwise in
theorem exists_mul_of_mem_sup_of_normalizes [Finite G] {A B : Subgroup G}
    (hBA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hle : B ≤ Subgroup.normalizer (A : Set G) := fun b hb =>
    Subgroup.mem_normalizer_fintype fun a ha => hBA b hb a ha
  have hx' : x ∈ ((A : Set G) * (B : Set G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hle]
    exact hx
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hx'
  exact ⟨a, ha, b, hb, hab⟩

variable [Finite G]

theorem le_glaPPrimeCoreOf_of_isSubnormal {p : ℕ} (hp : p.Prime) {L C : Subgroup G} (h : IsSubnormal L C)
    (hcop : Nat.Coprime p (Nat.card L)) : L ≤ GLAPPrimeCoreOf p C :=
  (CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal le_rfl
    (fun g hg x hx => L.mul_mem (L.mul_mem hg hx) (L.inv_mem hg)) hcop).trans
    (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal hp h)

theorem le_core_sup_layer_of_isComponentOf {p : ℕ} (hp : p.Prime) {L C : Subgroup G} (hL : IsComponentOf L C) :
    L ≤ GLAPPrimeCoreOf p C ⊔ GLAPLayer p C := by
  refine (Inputs2323.le_core_sup_layer_of_isQuasisimple p hL.2.2).trans (sup_le_sup ?_ ?_)
  · exact CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1
  · exact sSup_le fun J hJ => le_sSup (CFSG.LocalAnalysis.GLTheoremA.glaPComponent_of_isSubnormal' hp hL.2.1 hJ)

theorem glaLayer_le_core_sup_layer {p : ℕ} (hp : p.Prime) (C : Subgroup G) :
    GLALayer C ≤ GLAPPrimeCoreOf p C ⊔ GLAPLayer p C :=
  sSup_le fun _ hL => le_core_sup_layer_of_isComponentOf hp hL

theorem map_core_sup_layer_le {G' : Type} [Group G'] {p : ℕ} (hp : p.Prime) (ψ : G →* G')
    (hψ : Function.Injective ψ) (H : Subgroup G) :
    (GLAPPrimeCoreOf p H ⊔ GLAPLayer p H).map ψ ≤ GLAPPrimeCoreOf p (H.map ψ) ⊔ GLAPLayer p (H.map ψ) := by
  rw [Subgroup.map_sup]
  refine sup_le_sup ?_ ?_
  · rw [CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p ψ hψ]
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hker : Nat.Coprime p (Nat.card ↥(H ⊓ ψ.ker)) := by
      rw [(MonoidHom.ker_eq_bot_iff _).2 hψ, inf_bot_eq, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    exact le_sSup (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp ψ hker hJ)

end GroupTheory

theorem twoInCoreLayer_of_congr {S T : Type} [Group S] [Group T] [Finite S] [Finite T] (e : S ≃* T) {p : ℕ}
    (hp : p.Prime) {β : MulAut S} (h : TwoInCoreLayer p (MulAut.congr e β)) : TwoInCoreLayer p β := by
  intro x hx hx2
  have hfix := Inputs141c.fixSubgroup_congr e β
  have hex : e x ∈ fixSubgroup (MulAut.congr e β) := by
    rw [hfix]
    exact ⟨x, hx, rfl⟩
  have hex2 : IsPGroup 2 ↥(Subgroup.zpowers (e x)) := by
    have h1 := hx2.map e.toMonoidHom
    rwa [MonoidHom.map_zpowers] at h1
  have h1 := h (e x) hex hex2
  rw [hfix] at h1
  have h2 := map_core_sup_layer_le hp e.symm.toMonoidHom e.symm.injective _
    (Subgroup.mem_map_of_mem e.symm.toMonoidHom h1)
  rw [Inputs141c.map_map_symm] at h2
  simpa using h2

theorem twoInCoreLayer_of_conj {S : Type} [Group S] [Finite S] (γ : MulAut S) {p : ℕ} (hp : p.Prime)
    {β : MulAut S} (h : TwoInCoreLayer p (γ * β * γ⁻¹)) : TwoInCoreLayer p β := by
  refine twoInCoreLayer_of_congr (γ : S ≃* S) hp ?_
  have e1 : MulAut.congr (γ : S ≃* S) β = γ * β * γ⁻¹ := by
    ext y
    rfl
  rw [e1]
  exact h

section Lift

variable {K Q : Type} [Group K] [Group Q] [Finite K] [Finite Q]
  (π : K →* Q) (hker : π.ker ≤ Subgroup.center K) (α : MulAut K) (β : MulAut Q)
  (hαβ : ∀ k, π (α k) = β (π k))
include hker hαβ

omit hker hαβ in
theorem eq_one_of_pow_mem_of_coprime {G : Type} [Group G] [Finite G] {p : ℕ} {O : Subgroup G} {u : G}
    (hu : u ∈ O) (hO : Nat.Coprime p (Nat.card O)) {e : ℕ} (he : u ^ (p ^ e) = 1) : u = 1 := by
  have h1 : orderOf u ∣ Nat.card O := by
    rw [← Subgroup.orderOf_mk u hu]
    exact orderOf_dvd_natCard _
  have h2 : orderOf u ∣ p ^ e := orderOf_dvd_of_pow_eq_one he
  have h3 : Nat.Coprime (p ^ e) (Nat.card O) := Nat.Coprime.pow_left e hO
  have h4 : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes h3 h2 h1
  exact orderOf_eq_one_iff.1 h4

omit hker hαβ in
theorem coprime_card_closure_coprime {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (hc : ∀ u : N, (∃ e : ℕ, u ^ (p ^ e) = 1) → u ∈ Subgroup.center N) :
    Nat.Coprime p (Nat.card (Subgroup.closure {y : N | Nat.Coprime (orderOf y) p})) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p N) := inferInstance
  have hPc : ∀ u ∈ (P : Subgroup N), u ∈ Subgroup.center N := by
    intro u hu
    obtain ⟨e, he⟩ := P.2 ⟨u, hu⟩
    exact hc u ⟨e, by simpa using congrArg Subtype.val he⟩
  have hP : Subgroup.normalizer ((P : Subgroup N) : Set N) ≤ Subgroup.centralizer ((P : Subgroup N) : Set N) := by
    intro n _
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_center_iff.1 (hPc u hu) n).symm
  set τ := MonoidHom.transferSylow P hP with hτ
  have hle : Subgroup.closure {y : N | Nat.Coprime (orderOf y) p} ≤ τ.ker := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    obtain ⟨e, he⟩ := P.2 (τ y)
    have h1 : orderOf (τ y) ∣ orderOf y := orderOf_map_dvd τ y
    have h2 : orderOf (τ y) ∣ p ^ e := orderOf_dvd_of_pow_eq_one he
    have h3 : Nat.Coprime (orderOf y) (p ^ e) := Nat.Coprime.pow_right e hy
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes h3 h1 h2)
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  exact MonoidHom.not_dvd_card_ker_transferSylow P hP (hdvd.trans (Subgroup.card_dvd_of_le hle))

theorem mem_glaPPrimeCoreOf_of_coprime {p : ℕ} (hp : p.Prime) {x : K} (hx : x ∈ fixSubgroup α)
    (hxO : π x ∈ GLAPPrimeCoreOf p (fixSubgroup β)) (hcop : Nat.Coprime (orderOf x) p) :
    x ∈ GLAPPrimeCoreOf p (fixSubgroup α) := by
  classical
  set O := GLAPPrimeCoreOf p (fixSubgroup β) with hO
  have hOcop : Nat.Coprime p (Nat.card O) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp _
  set N : Subgroup K := fixSubgroup α ⊓ O.comap π with hN
  set s : Set K := {y | y ∈ N ∧ Nat.Coprime (orderOf y) p} with hs
  set T : Subgroup K := Subgroup.closure s with hT
  have hxT : x ∈ T := Subgroup.subset_closure ⟨⟨hx, hxO⟩, hcop⟩
  have hTN : T ≤ N := (Subgroup.closure_le N).2 fun y hy => hy.1
  have hNconj : ∀ c ∈ fixSubgroup α, ∀ y ∈ N, c * y * c⁻¹ ∈ N := by
    intro c hc y hy
    refine ⟨(fixSubgroup α).mul_mem ((fixSubgroup α).mul_mem hc hy.1) ((fixSubgroup α).inv_mem hc), ?_⟩
    show π (c * y * c⁻¹) ∈ O
    rw [map_mul, map_mul, map_inv]
    exact CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem (π c)
      (map_fixSubgroup_le π hker α β hαβ ⟨c, hc, rfl⟩) (π y) hy.2
  have hTconj : ∀ c ∈ fixSubgroup α, ∀ t ∈ T, c * t * c⁻¹ ∈ T := by
    intro c hc t ht
    have hle : T ≤ T.comap (MulAut.conj c).toMonoidHom := by
      rw [hT, Subgroup.closure_le]
      intro y hy
      show (MulAut.conj c).toMonoidHom y ∈ T
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · simpa [MulAut.conj_apply] using hNconj c hc y hy.1
      · rw [orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective y]
        exact hy.2
    have := hle ht
    simpa [MulAut.conj_apply] using this
  have hTcop : Nat.Coprime p (Nat.card T) := by
    have hc : ∀ u : ↥N, (∃ e : ℕ, u ^ (p ^ e) = 1) → u ∈ Subgroup.center ↥N := by
      rintro u ⟨e, he⟩
      have he' : (u : K) ^ (p ^ e) = 1 := by simpa using congrArg Subtype.val he
      have h1 : π (u : K) = 1 :=
        eq_one_of_pow_mem_of_coprime (u.2.2 : π (u : K) ∈ O) hOcop
          (by rw [← map_pow, he', map_one])
      have h2 : (u : K) ∈ Subgroup.center K := hker h1
      rw [Subgroup.mem_center_iff]
      intro n
      exact Subtype.ext (Subgroup.mem_center_iff.1 h2 n)
    have h1 := coprime_card_closure_coprime (N := ↥N) hp hc
    have h2 : T ≤ (Subgroup.closure {y : ↥N | Nat.Coprime (orderOf y) p}).map N.subtype := by
      rw [hT, Subgroup.closure_le]
      intro y hy
      exact ⟨⟨y, hy.1⟩, Subgroup.subset_closure (by simpa using hy.2), rfl⟩
    have h3 : Nat.card T ∣ Nat.card ↥(Subgroup.closure {y : ↥N | Nat.Coprime (orderOf y) p}) := by
      refine (Subgroup.card_dvd_of_le h2).trans ?_
      rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact Nat.Coprime.coprime_dvd_right h3 h1
  exact CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal (hTN.trans inf_le_left) hTconj
    hTcop hxT

theorem mem_core_sup_layer_of_twoInCoreLayer (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : TwoInCoreLayer p β) {g : K} (hg : g ∈ fixSubgroup α) (hg2 : IsPGroup 2 ↥(Subgroup.zpowers g)) :
    g ∈ GLAPPrimeCoreOf p (fixSubgroup α) ⊔ GLAPLayer p (fixSubgroup α) := by
  classical
  set Cα := fixSubgroup α with hCα
  set Cβ := fixSubgroup β with hCβ
  have hπg : π g ∈ Cβ := map_fixSubgroup_le π hker α β hαβ ⟨g, hg, rfl⟩
  have hπg2 : IsPGroup 2 ↥(Subgroup.zpowers (π g)) := by
    have h1 := hg2.map π
    rwa [MonoidHom.map_zpowers] at h1
  have hmem := h (π g) hπg hπg2
  obtain ⟨y, hy, l, hl, hyl⟩ := exists_mul_of_mem_sup_of_normalizes (fun b hb a ha =>
    CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem b
      (CFSG.HardMathSupport.Solomon.Coordinator.glaPLayer_le Cβ hb) a ha) hmem
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.map_glaPLayer_fixSubgroup_eq π hker α β hαβ hπ hp] at hl
  obtain ⟨l₀, hl₀, rfl⟩ := hl
  have hl₀C : l₀ ∈ Cα := CFSG.HardMathSupport.Solomon.Coordinator.glaPLayer_le Cα hl₀
  set h₀ := g * l₀⁻¹ with hh₀
  have hh₀C : h₀ ∈ Cα := Cα.mul_mem hg (Cα.inv_mem hl₀C)
  have hπh₀ : π h₀ = y := by
    rw [hh₀, map_mul, map_inv, ← hyl]
    group
  obtain ⟨a, b, e, ha, hb, hab, hprod, hord, hcop⟩ :=
    CFSG.TwoRankLowerBound.Helpers.finite_prime_primary_factorization h₀ p hp
  have hzpow : Subgroup.zpowers h₀ ≤ Cα := Subgroup.zpowers_le.2 hh₀C
  have hzpowO : ∀ c ∈ Subgroup.zpowers h₀, π c ∈ GLAPPrimeCoreOf p Cβ := by
    intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    rw [map_zpow, hπh₀]
    exact zpow_mem hy k
  have hape : a ^ (p ^ e) = 1 := orderOf_dvd_iff_pow_eq_one.1 hord
  have hπa : π a = 1 :=
    eq_one_of_pow_mem_of_coprime (hzpowO a ha)
      (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp Cβ)
      (by rw [← map_pow, hape, map_one])
  have haZ : a ∈ Subgroup.center K := hker hπa
  have hbO : b ∈ GLAPPrimeCoreOf p Cα :=
    mem_glaPPrimeCoreOf_of_coprime π hker α β hαβ hp (hzpow hb) (hzpowO b hb) hcop.symm
  set w := b * l₀ with hw
  have hwQ : w ∈ GLAPPrimeCoreOf p Cα ⊔ GLAPLayer p Cα :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hbO) (Subgroup.mem_sup_right hl₀)
  have hgaw : g = a * w := by
    rw [hw, ← mul_assoc, hprod, hh₀, inv_mul_cancel_right]
  have hgpow : g ^ (p ^ e) = w ^ (p ^ e) := by
    rw [hgaw, (Commute.symm (Subgroup.mem_center_iff.1 haZ w)).mul_pow, hape, one_mul]
  obtain ⟨k, hk⟩ := hg2 ⟨g, Subgroup.mem_zpowers g⟩
  have hgk : g ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hcop2 : Nat.Coprime (p ^ e) (orderOf g) := by
    have h1 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hgk) (Nat.Coprime.pow e k h1)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop2
  rw [← hm, hgpow]
  exact pow_mem (pow_mem hwQ _) _

end Lift

section Component

variable {X : Type} [Group X] [Finite X]

theorem fixSubgroup_normalizerMonoidHom_eq {K : Subgroup X} {z : X} (hzN : z ∈ Subgroup.normalizer (K : Set X)) :
    fixSubgroup (K.normalizerMonoidHom ⟨z, hzN⟩) = (K ⊓ Subgroup.centralizer ({z} : Set X)).subgroupOf K := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_subgroupOf]
  have hαx : (((K.normalizerMonoidHom ⟨z, hzN⟩) x : ↥K) : X) = z * x * z⁻¹ := rfl
  constructor
  · intro hx
    have e : z * (x : X) * z⁻¹ = x := by rw [← hαx, hx]
    refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc (x : X) * z = z * x * z⁻¹ * z := by rw [e]
      _ = z * x := by group
  · rintro ⟨-, hx⟩
    have e : (x : X) * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 hx
    apply Subtype.ext
    rw [hαx]
    calc z * (x : X) * z⁻¹ = x * z * z⁻¹ := by rw [e]
      _ = x := by group

theorem oPrimeResidualOf_le_of_twoInCoreLayer {K : Subgroup X} {z : X} (hzN : z ∈ Subgroup.normalizer (K : Set X))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : TwoInCoreLayer p (QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K)
      (K.normalizerMonoidHom ⟨z, hzN⟩) (Subgroup.map_center_eq _))) :
    CFSG.GH74.GLS.oPrimeResidualOf 2 (K ⊓ Subgroup.centralizer ({z} : Set X)) ≤
      GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({z} : Set X)) ⊔
        GLAPLayer p (K ⊓ Subgroup.centralizer ({z} : Set X)) := by
  classical
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨z, hzN⟩ with hα
  set C := K ⊓ Subgroup.centralizer ({z} : Set X) with hC
  have hfix : fixSubgroup α = C.subgroupOf K := fixSubgroup_normalizerMonoidHom_eq hzN
  have hCmap : (fixSubgroup α).map K.subtype = C := by
    rw [hfix, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 inf_le_left
  refine CFSG.GH74.GLS.Balance.oPrimeResidualOf_le_of_two_elements fun v hv hv2 => ?_
  obtain ⟨k, hk⟩ := hv2
  have hvK : v ∈ K := (Subgroup.mem_inf.1 hv).1
  set g : ↥K := ⟨v, hvK⟩ with hg
  have hgC : g ∈ fixSubgroup α := by
    rw [hfix]
    exact Subgroup.mem_subgroupOf.2 hv
  have hg2 : IsPGroup 2 ↥(Subgroup.zpowers g) :=
    isPGroup_zpowers_of_pow_eq_one (m := k) (Subtype.ext (by simpa [hg] using hk))
  have hmem := mem_core_sup_layer_of_twoInCoreLayer (QuotientGroup.mk' (Subgroup.center ↥K))
    (by rw [QuotientGroup.ker_mk']) α
    (QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) α (Subgroup.map_center_eq _))
    (fun _ => rfl) (QuotientGroup.mk'_surjective _) hp hp2 h hgC hg2
  have hmap := map_core_sup_layer_le hp K.subtype K.subtype_injective _ (Subgroup.mem_map_of_mem K.subtype hmem)
  rw [hCmap] at hmap
  exact hmap

end Component

@[expose] def Input14_1BadOn (R : ℕ → TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (K Z : Subgroup X),
    CFSG.Open.IsQuasisimple ↥K → ∀ d : TauCeti.ValidLieTypeIndex, R p d.1 → d.1.characteristic = 2 →
    Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
    IsElemAbelian p Z → Nat.card Z = p ^ 2 → Z ≤ Subgroup.normalizer (K : Set X) →
    Z ⊓ Subgroup.centralizer (K : Set X) = ⊥ → (p = 5 → ¬ Lemma1314.I2310Exc5 K) →
    ∀ z ∈ Z, z ≠ 1 →
      CFSG.GH74.GLS.oPrimeResidualOf 2 (K ⊓ Subgroup.centralizer ({z} : Set X)) ≤
        GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({z} : Set X)) ⊔
          GLAPLayer p (K ⊓ Subgroup.centralizer ({z} : Set X)) ⊔
          ⨆ (L : Subgroup X) (_ : Inputs2323.BadFactor p K Z z L), L

@[expose] def Input14_1BadSimpleOn (R : ℕ → TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, R p d.1 → d.1.characteristic = 2 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → TwoInCoreLayer p β

theorem input14_1Bad_of_on (h : Input14_1BadOn fun _ _ => True) : Inputs2323.Input14_1Bad := by
  intro p hp hp5 X _ _ K Z hK hlie hZ hZc hZN hfaith hexc z hz hz1
  obtain ⟨d, he, hchar⟩ := hlie
  exact h p hp hp5 X K Z hK d trivial hchar he hZ hZc hZN hfaith hexc z hz hz1

theorem input14_1BadOn_or {R R' : ℕ → TauCeti.LieTypeIndex → Prop} (h : Input14_1BadOn R)
    (h' : Input14_1BadOn R') : Input14_1BadOn fun p d => R p d ∨ R' p d := by
  intro p hp hp5 X _ _ K Z hK d hd
  rcases hd with hd | hd
  · exact h p hp hp5 X K Z hK d hd
  · exact h' p hp hp5 X K Z hK d hd

theorem Input14_1BadOn.mono {R R' : ℕ → TauCeti.LieTypeIndex → Prop} (hRR' : ∀ p d, R p d → R' p d)
    (h : Input14_1BadOn R') : Input14_1BadOn R :=
  fun p hp hp5 X _ _ K Z hK d hd => h p hp hp5 X K Z hK d (hRR' p d.1 hd)

theorem input14_1BadOn_of_simple {R : ℕ → TauCeti.LieTypeIndex → Prop} (h : Input14_1BadSimpleOn R) :
    Input14_1BadOn R := by
  intro p hp hp5 X _ _ K Z hKq d hR hchar he hZel _ hZN hfaith _ z hz hz1
  classical
  have hzN : z ∈ Subgroup.normalizer (K : Set X) := hZN hz
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨z, hzN⟩ with hαdef
  have hαx : ∀ x : ↥K, ((α x : ↥K) : X) = z * x * z⁻¹ := fun x => rfl
  set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := (QuotientGroup.ker_mk' _).le
  set β : MulAut (↥K ⧸ Subgroup.center ↥K) :=
    QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) α (Subgroup.map_center_eq α) with hβdef
  have hαβ : ∀ x, π (α x) = β (π x) := fun x => rfl
  have hβn : ∀ (n : ℕ) (x : ↥K), (β ^ n) (π x) = π ((α ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ← hαβ, ih]
  have hzp : z ^ p = 1 := hZel.2 z hz
  have hαp : α ^ p = 1 := by
    have e : (⟨z, hzN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ p = 1 := Subtype.ext hzp
    rw [hαdef, ← map_pow, e, map_one]
  have hβp : β ^ p = 1 := by
    ext w
    obtain ⟨x, rfl⟩ := hπ w
    rw [hβn, hαp]
    rfl
  have hβ1 : β ≠ 1 := by
    intro hβ
    apply hz1
    have hα1 : α = 1 := Inputs141c.eq_one_of_mul_inv_mem_center hKq.1 α fun x => hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hαβ, hβ, MulAut.one_apply, mul_inv_cancel])
    have hzC : z ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have e1 : α ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [hα1, MulAut.one_apply]
      have e : z * y * z⁻¹ = y := by
        have := congrArg Subtype.val e1
        rw [hαx] at this
        exact this
      calc y * z = z * y * z⁻¹ * z := by rw [e]
        _ = z * y := by group
    have hmem : z ∈ Z ⊓ Subgroup.centralizer (K : Set X) := Subgroup.mem_inf.2 ⟨hz, hzC⟩
    rw [hfaith, Subgroup.mem_bot] at hmem
    exact hmem
  have hSs : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKq.2
  have hSnc : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hKq
  have hT := h p hp hp5 _ hSs hSnc d hR hchar he β hβp hβ1
  have hp2 : p ≠ 2 := by omega
  exact le_sup_of_le_left (oPrimeResidualOf_le_of_twoInCoreLayer hzN hp hp2 hT)

section Criterion

variable {X Q : Type} [Group X] [Group Q] [Finite X] [Finite Q]

theorem twoInCoreLayer_of_cover (π : X →* Q) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X)
    (hodd : Nat.Coprime 2 (Nat.card π.ker)) (α : MulAut X) (β : MulAut Q) (hαβ : ∀ x, π (α x) = β (π x))
    {p : ℕ} (hp : p.Prime) (hlay : PerfectInLayer β) {ι : Type*} (B : ι → Subgroup X)
    (hBC : ∀ i, B i ≤ fixSubgroup α)
    (hB : ∀ i, ⁅B i, B i⁆ = B i ∨
      (Nat.Coprime p (Nat.card (B i)) ∧ ∀ c ∈ fixSubgroup α, ∀ b ∈ B i, c * b * c⁻¹ ∈ B i))
    (h2 : ∀ g ∈ fixSubgroup α, IsPGroup 2 ↥(Subgroup.zpowers g) → g ∈ ⨆ i, B i) :
    TwoInCoreLayer p β := by
  intro x hx hx2
  obtain ⟨g, hg, hg2, rfl⟩ := Inputs141c.exists_two_lift π hπ hker hodd α β hαβ hx hx2
  have hgB := h2 g hg hg2
  have hle : (⨆ i, B i).map π ≤ GLAPPrimeCoreOf p (fixSubgroup β) ⊔ GLAPLayer p (fixSubgroup β) := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rcases hB i with hperf | ⟨hcop, hnorm⟩
    · have hP : ⁅(B i).map π, (B i).map π⁆ = (B i).map π := by rw [← Subgroup.map_commutator, hperf]
      have hPC : (B i).map π ≤ fixSubgroup β :=
        (Subgroup.map_mono (hBC i)).trans (map_fixSubgroup_le π hker α β hαβ)
      exact (hlay _ hPC hP).trans (glaLayer_le_core_sup_layer hp _)
    · refine le_sup_of_le_left (le_glaPPrimeCoreOf_of_isSubnormal hp ?_ ?_)
      ·
        have hn1 : (((B i).map π).subgroupOf ((fixSubgroup α).map π)).Normal := by
          refine ⟨fun y hy c => ?_⟩
          rw [Subgroup.mem_subgroupOf] at hy ⊢
          obtain ⟨b, hb, hby⟩ := hy
          obtain ⟨c₀, hc₀, hc₀c⟩ := c.2
          refine ⟨c₀ * b * c₀⁻¹, hnorm c₀ hc₀ b hb, ?_⟩
          simp only [map_mul, map_inv, hby, hc₀c]
          rfl
        have hn2 := CFSG.HardMathSupport.Solomon.Coordinator.normal_map_fixSubgroup π hker α β hαβ hπ
        exact CFSG.Open.IsSubnormal.step (Subgroup.map_mono (hBC i)) hn1
          (CFSG.Open.IsSubnormal.step (map_fixSubgroup_le π hker α β hαβ) hn2 (CFSG.Open.IsSubnormal.refl _))
      · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) hcop
  exact hle ⟨g, hgB, rfl⟩

end Criterion

section Generation

@[expose] def centerTwoPart {X : Type} [Group X] (K : Subgroup X) (M : ℕ) : Subgroup X where
  carrier := {x | x ∈ K ∧ (∀ k ∈ K, x * k = k * x) ∧ x ^ (2 ^ M) = 1}
  mul_mem' := by
    rintro x y ⟨hxK, hxc, hx2⟩ ⟨hyK, hyc, hy2⟩
    refine ⟨K.mul_mem hxK hyK, fun k hk => ?_, ?_⟩
    · rw [mul_assoc, hyc k hk, ← mul_assoc, hxc k hk, mul_assoc]
    · rw [Commute.mul_pow (hxc y hyK), hx2, hy2, one_mul]
  one_mem' := ⟨K.one_mem, fun k _ => by rw [one_mul, mul_one], one_pow _⟩
  inv_mem' := by
    rintro x ⟨hxK, hxc, hx2⟩
    refine ⟨K.inv_mem hxK, fun k hk => ?_, by rw [inv_pow, hx2, inv_one]⟩
    have h := hxc k hk
    calc x⁻¹ * k = x⁻¹ * (k * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * k) * x⁻¹ := by rw [h]
      _ = k * x⁻¹ := by group

theorem mem_centerTwoPart {X : Type} [Group X] {K : Subgroup X} {M : ℕ} {x : X} :
    x ∈ centerTwoPart K M ↔ x ∈ K ∧ (∀ k ∈ K, x * k = k * x) ∧ x ^ (2 ^ M) = 1 :=
  Iff.rfl

variable {X : Type} [Group X] [Finite X]

@[expose] def centerQuotAct (K : Subgroup X) :
    ↥(Subgroup.normalizer (K : Set X)) →* MulAut (↥K ⧸ Subgroup.center ↥K) :=
  (quotientCenterAut' ↥K).comp K.normalizerMonoidHom

theorem centerQuotAct_mk (K : Subgroup X) (x : ↥(Subgroup.normalizer (K : Set X))) (k : ↥K) :
    centerQuotAct K x (QuotientGroup.mk k) = QuotientGroup.mk (K.normalizerMonoidHom x k) :=
  rfl

theorem exists_two_lift_fixed {K : Subgroup X} {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hbp : b ^ p = 1) {s : ↥K ⧸ Subgroup.center ↥K} {n : ℕ}
    (hs : s ^ (2 ^ n) = 1) (hfix : centerQuotAct K ⟨b, hb⟩ s = s) :
    ∃ k : ↥K, (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) = s ∧ (∃ m : ℕ, k ^ (2 ^ m) = 1) ∧
      b * (k : X) * b⁻¹ = k := by
  classical
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨a, u, hu, hcu⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := ↥(Subgroup.center ↥K))).ne'
  have hcop : Nat.Coprime u (orderOf (QuotientGroup.mk k₀ : ↥K ⧸ Subgroup.center ↥K)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hs)
      (Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hu))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  set t : ↥K := (k₀ ^ u) ^ m with ht
  have htmk : (QuotientGroup.mk t : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk k₀ := by
    rw [ht, QuotientGroup.mk_pow, QuotientGroup.mk_pow]
    exact hm
  have hcen : ∀ z ∈ Subgroup.center ↥K, z ^ Nat.card (Subgroup.center ↥K) = 1 := fun z hz => by
    have h : (⟨z, hz⟩ : ↥(Subgroup.center ↥K)) ^ Nat.card (Subgroup.center ↥K) = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h
  have hk₀ : k₀ ^ (2 ^ n) ∈ Subgroup.center ↥K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hs
  set M := n + a with hM
  have ht2 : t ^ (2 ^ M) = 1 := by
    have h : t ^ (2 ^ M) = ((k₀ ^ (2 ^ n)) ^ Nat.card (Subgroup.center ↥K)) ^ m := by
      rw [ht, hcu, hM]
      simp only [← pow_mul]
      congr 1
      rw [pow_add]
      ring
    rw [h, hcen _ hk₀, one_pow]
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨b, hb⟩ with hα
  have hαx : ∀ x : ↥K, ((α x : ↥K) : X) = b * x * b⁻¹ := fun x => rfl
  have hfix' : (QuotientGroup.mk (α t) : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk t := by
    have h1 : (QuotientGroup.mk (α t) : ↥K ⧸ Subgroup.center ↥K) =
        centerQuotAct K ⟨b, hb⟩ (QuotientGroup.mk t) := rfl
    rw [h1, htmk, hfix]
  have hζ : α t * t⁻¹ ∈ Subgroup.center ↥K := by
    have h := QuotientGroup.eq.1 hfix'.symm
    have h3 : t * (t⁻¹ * α t) * t⁻¹ = α t * t⁻¹ := by group
    rw [← h3]
    exact Subgroup.Normal.conj_mem inferInstance _ h t
  have hζc : ∀ y : ↥K, (α t * t⁻¹) * y = y * (α t * t⁻¹) := fun y => ((Subgroup.mem_center_iff.1 hζ) y).symm
  have hζ2 : (α t * t⁻¹) ^ (2 ^ M) = 1 := by
    have h1 : α t = (α t * t⁻¹) * t := by group
    have h2 : (α t) ^ (2 ^ M) = 1 := by rw [← map_pow, ht2, map_one]
    rw [h1, (show Commute (α t * t⁻¹) t from hζc t).mul_pow, ht2, mul_one] at h2
    exact h2
  set Nm : Subgroup X := Subgroup.normalizer (K : Set X) with hNm
  have hKNm : K ≤ Nm := Subgroup.le_normalizer
  haveI hNn : ((centerTwoPart K M).subgroupOf Nm).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf, mem_centerTwoPart] at hx ⊢
    obtain ⟨hxK, hxc, hx2⟩ := hx
    have hg : ∀ h : X, h ∈ (K : Set X) ↔ (g : X) * h * (g : X)⁻¹ ∈ (K : Set X) :=
      Subgroup.mem_normalizer_iff.1 g.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨(hg _).1 hxK, fun k hk => ?_, ?_⟩
    · have hk' : (g : X)⁻¹ * k * (g : X) ∈ K := by
        refine (hg _).2 ?_
        have he : (g : X) * ((g : X)⁻¹ * k * (g : X)) * (g : X)⁻¹ = k := by group
        rw [SetLike.mem_coe, he]
        exact hk
      have h := hxc _ hk'
      calc (g : X) * x * (g : X)⁻¹ * k = (g : X) * (x * ((g : X)⁻¹ * k * g)) * (g : X)⁻¹ := by group
        _ = (g : X) * (((g : X)⁻¹ * k * g) * x) * (g : X)⁻¹ := by rw [h]
        _ = k * ((g : X) * x * (g : X)⁻¹) := by group
    · rw [conj_pow, hx2, mul_one, mul_inv_cancel]
  have hZ2p : IsPGroup 2 ↥((centerTwoPart K M).subgroupOf Nm) := by
    intro x
    refine ⟨M, ?_⟩
    have h : ((x : ↥Nm) : X) ^ (2 ^ M) = 1 := (mem_centerTwoPart.1 (Subgroup.mem_subgroupOf.1 x.2)).2.2
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hZ2p
  have hcop2 : Nat.Coprime p (Nat.card ↥((centerTwoPart K M).subgroupOf Nm)) := by
    rw [hj]
    exact Nat.Coprime.pow_right j ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  set a' : ↥Nm := ⟨b, hb⟩ with ha'
  set w : ↥Nm := ⟨(t : X), hKNm t.2⟩ with hw
  have ha'p : a' ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hbp)
  have hwN : a' * w * a'⁻¹ * w⁻¹ ∈ (centerTwoPart K M).subgroupOf Nm := by
    rw [Subgroup.mem_subgroupOf]
    have he : ((a' * w * a'⁻¹ * w⁻¹ : ↥Nm) : X) = ((α t * t⁻¹ : ↥K) : X) := by
      show b * (t : X) * b⁻¹ * (t : X)⁻¹ = ((α t : ↥K) : X) * (t : X)⁻¹
      rw [hαx]
    rw [he, mem_centerTwoPart]
    refine ⟨(α t * t⁻¹).2, fun k hk => congrArg Subtype.val (hζc ⟨k, hk⟩), ?_⟩
    rw [← SubgroupClass.coe_pow, hζ2, OneMemClass.coe_one]
  obtain ⟨x, hxw, hax⟩ :=
    CFSG.SignalizerFunctorTheorem.exists_fixed_of_coprime hp ha'p _ hcop2 hwN
  have hxw' : (x : X) * (t : X)⁻¹ ∈ centerTwoPart K M := by
    have h := Subgroup.mem_subgroupOf.1 hxw
    have he : ((x * w⁻¹ : ↥Nm) : X) = (x : X) * (t : X)⁻¹ := rfl
    rwa [he] at h
  obtain ⟨hζ'K, hζ'c, hζ'2⟩ := mem_centerTwoPart.1 hxw'
  have hxK : (x : X) ∈ K := by
    have h : (x : X) = ((x : X) * (t : X)⁻¹) * t := by group
    rw [h]
    exact K.mul_mem hζ'K t.2
  have hc : Commute ((x : X) * (t : X)⁻¹) (t : X) := hζ'c t t.2
  have ht2' : (t : X) ^ (2 ^ M) = 1 := by rw [← SubgroupClass.coe_pow, ht2, OneMemClass.coe_one]
  refine ⟨⟨x, hxK⟩, ?_, ⟨M, ?_⟩, ?_⟩
  · have hζ'cen : (⟨(x : X) * (t : X)⁻¹, hζ'K⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (hζ'c g g.2).symm
    have hxeq : (⟨x, hxK⟩ : ↥K) = ⟨(x : X) * (t : X)⁻¹, hζ'K⟩ * t := by
      apply Subtype.ext
      show (x : X) = (x : X) * (t : X)⁻¹ * t
      group
    rw [hxeq, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hζ'cen, one_mul, htmk]
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    show (x : X) ^ (2 ^ M) = 1
    have h : (x : X) = ((x : X) * (t : X)⁻¹) * t := by group
    rw [h, hc.mul_pow, hζ'2, ht2', one_mul]
  · have h := congrArg Subtype.val hax
    exact h

theorem eq_iSup_oPrimeResidualOf_of_uniPlaneGen {Q : Type*} [Group Q] {K B : Subgroup X}
    (hK : CFSG.Open.IsQuasisimple ↥K) (hBN : B ≤ Subgroup.normalizer (K : Set X)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hBp : ∀ b ∈ B, b ^ p = 1) (θ : (↥K ⧸ Subgroup.center ↥K) ≃* Q)
    (hgen : Inputs2311c.UniPlaneGen 2 ((B.subgroupOf (Subgroup.normalizer (K : Set X))).map
      ((MulAut.congr θ).toMonoidHom.comp (centerQuotAct K)))) :
    K = ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1),
      CFSG.GH74.GLS.oPrimeResidualOf 2 (K ⊓ Subgroup.centralizer ({b} : Set X)) := by
  refine le_antisymm ?_ (iSup₂_le fun b _ => iSup_le fun _ =>
    (Subgroup.map_subtype_le _).trans inf_le_left)
  have hcl : Inputs2311c.uniPlaneClosure 2 ((B.subgroupOf (Subgroup.normalizer (K : Set X))).map
      ((MulAut.congr θ).toMonoidHom.comp (centerQuotAct K))) ≤
      (((⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), CFSG.GH74.GLS.oPrimeResidualOf 2
        (K ⊓ Subgroup.centralizer ({b} : Set X))).subgroupOf K).map
        (QuotientGroup.mk' (Subgroup.center ↥K))).map θ.toMonoidHom := by
    rw [Inputs2311c.uniPlaneClosure, Subgroup.closure_le]
    rintro s' ⟨e, he, he1, hes, n, hn⟩
    obtain ⟨x, hxB, rfl⟩ := Subgroup.mem_map.1 he
    have hxB' : (x : X) ∈ B := Subgroup.mem_subgroupOf.1 hxB
    have hx1 : (x : X) ≠ 1 := by
      intro h
      apply he1
      rw [show x = 1 from Subtype.ext h, map_one]
    have hfix : centerQuotAct K ⟨(x : X), x.2⟩ (θ.symm s') = θ.symm s' := by
      apply θ.injective
      rw [MulEquiv.apply_symm_apply]
      exact hes
    have hns : (θ.symm s') ^ (2 ^ n) = 1 := by rw [← map_pow, hn, map_one]
    obtain ⟨k, hks, ⟨m, hkm⟩, hkx⟩ := exists_two_lift_fixed x.2 hp hp2 (hBp _ hxB') hns hfix
    have hkC : (k : X) ∈ K ⊓ Subgroup.centralizer ({(x : X)} : Set X) := by
      refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      exact (mul_inv_eq_iff_eq_mul.1 hkx).symm
    have hmem : (k : X) ∈ CFSG.GH74.GLS.oPrimeResidualOf 2 (K ⊓ Subgroup.centralizer ({(x : X)} : Set X)) := by
      refine ⟨⟨k, hkC⟩, Subgroup.subset_closure ⟨m, ?_⟩, rfl⟩
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      show (k : X) ^ (2 ^ m) = 1
      rw [← SubgroupClass.coe_pow, hkm, OneMemClass.coe_one]
    refine ⟨QuotientGroup.mk k, ⟨k, ?_, rfl⟩, ?_⟩
    · exact Subgroup.mem_subgroupOf.2
        (Subgroup.mem_iSup_of_mem (x : X) (Subgroup.mem_iSup_of_mem hxB' (Subgroup.mem_iSup_of_mem hx1 hmem)))
    · show θ (QuotientGroup.mk k) = s'
      rw [hks, MulEquiv.apply_symm_apply]
  have hTmap : ((⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), CFSG.GH74.GLS.oPrimeResidualOf 2
      (K ⊓ Subgroup.centralizer ({b} : Set X))).subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)) = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have h1 := hcl (by rw [show Inputs2311c.uniPlaneClosure 2 _ = ⊤ from hgen]; exact Subgroup.mem_top (θ u))
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 h1
    rwa [θ.injective hvu] at hv
  have hTZ : ((⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), CFSG.GH74.GLS.oPrimeResidualOf 2
      (K ⊓ Subgroup.centralizer ({b} : Set X))).subgroupOf K) ⊔ Subgroup.center ↥K = ⊤ := by
    have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center ↥K))
      ((⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), CFSG.GH74.GLS.oPrimeResidualOf 2
        (K ⊓ Subgroup.centralizer ({b} : Set X))).subgroupOf K)
    rw [hTmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  have hTtop := Inputs2311c.eq_top_of_sup_center hK.1 hTZ
  intro k hk
  have h : (⟨k, hk⟩ : ↥K) ∈ ((⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), CFSG.GH74.GLS.oPrimeResidualOf 2
      (K ⊓ Subgroup.centralizer ({b} : Set X))).subgroupOf K) := by
    rw [hTtop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 h

end Generation

@[expose] def Input23_11TwoOn (R : ℕ → TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (K B : Subgroup X),
    CFSG.Open.IsQuasisimple ↥K → ∀ d : TauCeti.ValidLieTypeIndex, R p d.1 → d.1.characteristic = 2 →
    Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
    IsElemAbelian p B → Nat.card B = p ^ 2 → B ≤ Subgroup.normalizer (K : Set X) →
    B ⊓ Subgroup.centralizer (K : Set X) = ⊥ → (p = 5 → ¬ Lemma1314.I2310Exc5 K) →
    (∃ b ∈ B, b ≠ 1 ∧ ¬ Group.IsSolvable ↥(K ⊓ Subgroup.centralizer ({b} : Set X))) →
      K = ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1),
        CFSG.GH74.GLS.oPrimeResidualOf 2 (K ⊓ Subgroup.centralizer ({b} : Set X))

theorem input23_11Two_of_on (h : Input23_11TwoOn fun _ _ => True) : Inputs2323.Input23_11Two := by
  intro p hp hp5 X _ _ K B hK hlie hB hBc hBN hfaith hexc hns
  obtain ⟨d, he, hchar⟩ := hlie
  exact h p hp hp5 X K B hK d trivial hchar he hB hBc hBN hfaith hexc hns

theorem input23_11TwoOn_or {R R' : ℕ → TauCeti.LieTypeIndex → Prop} (h : Input23_11TwoOn R)
    (h' : Input23_11TwoOn R') : Input23_11TwoOn fun p d => R p d ∨ R' p d := by
  intro p hp hp5 X _ _ K B hK d hd
  rcases hd with hd | hd
  · exact h p hp hp5 X K B hK d hd
  · exact h' p hp hp5 X K B hK d hd

theorem Input23_11TwoOn.mono {R R' : ℕ → TauCeti.LieTypeIndex → Prop} (hRR' : ∀ p d, R p d → R' p d)
    (h : Input23_11TwoOn R') : Input23_11TwoOn R :=
  fun p hp hp5 X _ _ K B hK d hd => h p hp hp5 X K B hK d (hRR' p d.1 hd)

theorem input23_11TwoOn_exc5 : Input23_11TwoOn fun p d =>
    p = 5 ∧ (d = TauCeti.LieTypeIndex.suzuki 2 ∨ d = TauCeti.LieTypeIndex.reeF4 2 ∨
      d = TauCeti.LieTypeIndex.tits) := by
  intro p _ _ X _ _ K B _ d hd _ he _ _ _ _ hexc _
  exfalso
  obtain ⟨h5, hd⟩ := hd
  apply hexc h5
  rcases hd with hd | hd | hd
  · exact Or.inr (Or.inr ⟨d, hd, he⟩)
  · exact Or.inr (Or.inl ⟨d, hd, he⟩)
  · exact Or.inl ⟨d, hd, he⟩

theorem input23_11TwoOn_char_ne_two : Input23_11TwoOn fun _ d => d.characteristic ≠ 2 :=
  fun _ _ _ _ _ _ _ _ _ _ hd hchar => absurd hchar hd

theorem isElemAbelian_card_map_centerQuotAct {X : Type} [Group X] [Finite X] {Q : Type*} [Group Q] {K B : Subgroup X}
    (hK : CFSG.Open.IsQuasisimple ↥K) {p : ℕ} (hBel : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hfaith : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (θ : (↥K ⧸ Subgroup.center ↥K) ≃* Q) :
    IsElemAbelian p ((B.subgroupOf (Subgroup.normalizer (K : Set X))).map
        ((MulAut.congr θ).toMonoidHom.comp (centerQuotAct K))) ∧
      Nat.card ((B.subgroupOf (Subgroup.normalizer (K : Set X))).map
        ((MulAut.congr θ).toMonoidHom.comp (centerQuotAct K))) = p ^ 2 := by
  have hinj : ∀ x : ↥(Subgroup.normalizer (K : Set X)), (x : X) ∈ B →
      ((MulAut.congr θ).toMonoidHom.comp (centerQuotAct K)) x = 1 → (x : X) = 1 := by
    intro x hxB hx
    have h1 : centerQuotAct K x = 1 := by
      have h2 : (MulAut.congr θ) (centerQuotAct K x) = 1 := hx
      rwa [MulEquiv.map_eq_one_iff] at h2
    have h2 : K.normalizerMonoidHom x = 1 := quotientCenterAut'_injective hK.1 (by rw [map_one]; exact h1)
    have h3 : x ∈ K.normalizerMonoidHom.ker := h2
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h3
    have h4 : (x : X) ∈ B ⊓ Subgroup.centralizer (K : Set X) := ⟨hxB, h3⟩
    rw [hfaith] at h4
    exact h4
  have hinjOn : Set.InjOn ((MulAut.congr θ).toMonoidHom.comp (centerQuotAct K))
      (B.subgroupOf (Subgroup.normalizer (K : Set X)) : Set ↥(Subgroup.normalizer (K : Set X))) := by
    intro x hx y hy hxy
    have h1 : ((MulAut.congr θ).toMonoidHom.comp (centerQuotAct K)) (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hxyB : ((x * y⁻¹ : ↥(Subgroup.normalizer (K : Set X))) : X) ∈ B :=
      B.mul_mem (Subgroup.mem_subgroupOf.1 hx) (B.inv_mem (Subgroup.mem_subgroupOf.1 hy))
    exact mul_inv_eq_one.1 (Subtype.ext (hinj _ hxyB h1))
  refine ⟨CFSG.Open.IsElemAbelian.map (l119_isElemAbelian_subgroupOf hBel _) _, ?_⟩
  have h1 : Nat.card ((B.subgroupOf (Subgroup.normalizer (K : Set X))).map
      ((MulAut.congr θ).toMonoidHom.comp (centerQuotAct K))) =
      Nat.card (((MulAut.congr θ).toMonoidHom.comp (centerQuotAct K)) ''
        (B.subgroupOf (Subgroup.normalizer (K : Set X)) : Set ↥(Subgroup.normalizer (K : Set X)))) := by
    rw [← Subgroup.coe_map]
    rfl
  rw [h1, Nat.card_image_of_injOn hinjOn]
  have h2 : Nat.card ((B.subgroupOf (Subgroup.normalizer (K : Set X)) :
      Subgroup ↥(Subgroup.normalizer (K : Set X))) : Set ↥(Subgroup.normalizer (K : Set X))) =
      Nat.card (B.subgroupOf (Subgroup.normalizer (K : Set X))) := rfl
  rw [h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv, hBc]

theorem input23_11TwoOn_of_uniSeitzPlanes
    {S : ∀ d : TauCeti.ValidLieTypeIndex, ℕ → Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d)) → Prop}
    (hU : Inputs2311c.UniSeitzPlanes S) {R : ℕ → TauCeti.LieTypeIndex → Prop}
    (hRS : ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → 5 ≤ p → R p d.1 → d.1.characteristic = 2 →
      ∀ E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d)), IsElemAbelian p E → Nat.card E = p ^ 2 →
        S d p E) :
    Input23_11TwoOn R := by
  intro p hp hp5 X _ _ K B hK d hR hchar he hBel hBc hBN hfaith hexc _
  obtain ⟨θ⟩ := he
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hEel, hEcard⟩ := isElemAbelian_card_map_centerQuotAct hK hBel hBc hBN hfaith θ
  have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1 := by
    rintro (⟨hp3, -⟩ | ⟨hp5', hd⟩)
    · omega
    · apply hexc hp5'
      rcases hd with hd | hd
      · exact Or.inl ⟨d, hd, ⟨θ⟩⟩
      · exact Or.inr (Or.inr ⟨d, hd, ⟨θ⟩⟩)
  have hpd : p ≠ d.1.characteristic := by rw [hchar]; exact hp2
  have hgen := hU d p hp hp2 hpd hex _ hEel hEcard (hRS d p hp hp5 hR hchar _ hEel hEcard)
  rw [hchar] at hgen
  exact eq_iSup_oPrimeResidualOf_of_uniPlaneGen hK hBN hp hp2 hBel.2 θ hgen

theorem input23_11TwoOn_of_noPlane {R : ℕ → TauCeti.LieTypeIndex → Prop}
    (h : ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → 5 ≤ p → R p d.1 → d.1.characteristic = 2 →
      ∀ E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d)), IsElemAbelian p E → Nat.card E = p ^ 2 → False) :
    Input23_11TwoOn R := by
  intro p hp hp5 X _ _ K B hK d hR hchar he hBel hBc hBN hfaith _ _
  obtain ⟨θ⟩ := he
  obtain ⟨hEel, hEcard⟩ := isElemAbelian_card_map_centerQuotAct hK hBel hBc hBN hfaith θ
  exact (h d p hp hp5 hR hchar _ hEel hEcard).elim

theorem input14_1BadOn_of_noPlane {R : ℕ → TauCeti.LieTypeIndex → Prop}
    (h : ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → 5 ≤ p → R p d.1 → d.1.characteristic = 2 →
      ∀ E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d)), IsElemAbelian p E → Nat.card E = p ^ 2 → False) :
    Input14_1BadOn R := by
  intro p hp hp5 X _ _ K Z hK d hR hchar he hZel hZc hZN hfaith _ _ _ _
  obtain ⟨θ⟩ := he
  obtain ⟨hEel, hEcard⟩ := isElemAbelian_card_map_centerQuotAct hK hZel hZc hZN hfaith θ
  exact (h d p hp hp5 hR hchar _ hEel hEcard).elim

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2323b

end
