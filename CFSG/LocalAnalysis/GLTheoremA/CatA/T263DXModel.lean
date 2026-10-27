module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXSeed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142MThree
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263

@[expose] def ModelSel (p : ℕ) (T : Type) [Group T] [Finite T] : Prop :=
  ∀ r : T, r ^ p = 1 → r ≠ 1 → ∀ P : Subgroup T, P ≤ Subgroup.centralizer ({r} : Set T) →
    IsPGroup 2 ↥P → P ≠ ⊥ →
    ∃ J : Subgroup T, IsComponentOf J (Subgroup.centralizer ({r} : Set T)) ∧
      p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) ∧ ⁅P, J⁆ ≠ ⊥ ∧
      P ≤ J ⊔ (Subgroup.centralizer ({r} : Set T) ⊓ Subgroup.centralizer (J : Set T))

section Transport

variable {A B : Type} [Group A] [Group B]

private theorem nonempty_centerQuot_equiv (e : A ≃* B) :
    Nonempty (A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B) :=
  ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)⟩

end Transport

section CentralCover

theorem perfect_cover {J D : Type*} [Group J] [Group D] (hJ : commutator J = ⊤)
    (hD : CFSG.Open.IsQuasisimple D) (π : J →* D) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center J) :
    CFSG.Open.IsQuasisimple J ∧ Nonempty (J ⧸ Subgroup.center J ≃* D ⧸ Subgroup.center D) := by
  haveI : Group.IsPerfect J := ⟨hJ⟩
  have hcomap := CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel π hπ hker
  let ψ : J →* D ⧸ Subgroup.center D := (QuotientGroup.mk' (Subgroup.center D)).comp π
  have hψsurj : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hπ
  have hψker : ψ.ker = Subgroup.center J := by
    rw [← hcomap]
    ext x
    simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have he : J ⧸ Subgroup.center J ≃* D ⧸ Subgroup.center D :=
    (QuotientGroup.quotientMulEquivOfEq hψker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
  haveI : IsSimpleGroup (D ⧸ Subgroup.center D) := hD.2
  exact ⟨⟨hJ, he.isSimpleGroup⟩, ⟨he⟩⟩

end CentralCover

section Lift

open scoped commutatorElement

variable {G T : Type} [Group G] [Group T]

private theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

private theorem commutator_mul_central {a b z₁ z₂ : G} (h₁ : z₁ ∈ Subgroup.center G)
    (h₂ : z₂ ∈ Subgroup.center G) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ :=
  CFSG.HardMathSupport.Solomon.Coordinator.commutatorElement_mul_mul'
    (Commute.symm (Subgroup.mem_center_iff.1 h₁ b))
    (Commute.symm (Subgroup.mem_center_iff.1 h₁ z₂))
    (Commute.symm (Subgroup.mem_center_iff.1 h₂ a))

private theorem lift_component (σ : G →* T) (hσ : Function.Surjective σ)
    (hker : σ.ker ≤ Subgroup.center G) (l : G) {JT : Subgroup T}
    (hJT : IsComponentOf JT (Subgroup.centralizer ({σ l} : Set T))) :
    ∃ J₀ : Subgroup G, J₀ ≤ Subgroup.centralizer ({l} : Set G) ∧ J₀.map σ = JT ∧
      IsSubnormal J₀ (Subgroup.centralizer ({l} : Set G)) ∧ CFSG.Open.IsQuasisimple ↥J₀ ∧
      Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃* ↥JT ⧸ Subgroup.center ↥JT) ∧
      ∀ d : G, σ d ∈ Subgroup.centralizer (JT : Set T) → d ∈ Subgroup.centralizer (J₀ : Set G) := by
  set H : Subgroup G := JT.comap σ with hH
  have hHmap : H.map σ = JT := Subgroup.map_comap_eq_self_of_surjective hσ JT
  haveI hJTperf : Group.IsPerfect ↥JT := ⟨hJT.2.2.1⟩
  have hJTcomm : ⁅JT, JT⁆ = JT := Subgroup.commutator_eq_self
  have hJ₀map : (⁅H, H⁆ : Subgroup G).map σ = JT := by
    rw [Subgroup.map_commutator, hHmap, hJTcomm]
  have hdecomp : ∀ g ∈ H, ∃ a ∈ (⁅H, H⁆ : Subgroup G), ∃ z ∈ Subgroup.center G, g = a * z := by
    intro g hg
    have : σ g ∈ (⁅H, H⁆ : Subgroup G).map σ := by
      rw [hJ₀map]
      exact hg
    obtain ⟨a, ha, haeq⟩ := this
    refine ⟨a, ha, a⁻¹ * g, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (σ a)⁻¹ * σ g = 1
    rw [haeq, inv_mul_cancel]
  have hJ₀H : (⁅H, H⁆ : Subgroup G) ≤ H := commutator_self_le H
  have hJ₀perf : ⁅(⁅H, H⁆ : Subgroup G), ⁅H, H⁆⁆ = ⁅H, H⁆ := by
    refine le_antisymm (commutator_self_le _) ?_
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := hdecomp g₁ hg₁
    obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := hdecomp g₂ hg₂
    rw [commutator_mul_central hz₁ hz₂]
    exact Subgroup.commutator_mem_commutator ha₁ ha₂
  have hfix : ∀ g ∈ H, σ g ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      (MulAut.conj (σ l)) := by
    intro g hg
    have h1 : σ g ∈ Subgroup.centralizer ({σ l} : Set T) := hJT.1 hg
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    change σ l * σ g * (σ l)⁻¹ = σ g
    rw [← h1]
    group
  have hJ₀C : (⁅H, H⁆ : Subgroup G) ≤ Subgroup.centralizer ({l} : Set G) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have key := CFSG.HardMathSupport.Solomon.Coordinator.comm_mem_fixSubgroup σ hker
      (MulAut.conj l) (MulAut.conj (σ l)) (fun k => by simp [MulAut.conj_apply])
      (hfix g₁ hg₁) (hfix g₂ hg₂)
    have h2 : l * ⁅g₁, g₂⁆ * l⁻¹ = ⁅g₁, g₂⁆ := key
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  have hsub : IsSubnormal (⁅H, H⁆ : Subgroup G) (Subgroup.centralizer ({l} : Set G)) := by
    have h1 : IsSubnormal H ((Subgroup.centralizer ({σ l} : Set T)).comap σ) :=
      hJT.2.1.comap σ
    have h2 := h1.inf (Subgroup.centralizer ({l} : Set G))
    have hle : Subgroup.centralizer ({l} : Set G) ≤
        (Subgroup.centralizer ({σ l} : Set T)).comap σ := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff] at hs
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      change σ s * σ l = σ l * σ s
      rw [← map_mul, ← map_mul, hs]
    rw [inf_eq_right.2 hle] at h2
    refine IsSubnormal.step (M := H ⊓ Subgroup.centralizer ({l} : Set G)) (le_inf hJ₀H hJ₀C) ?_ h2
    rw [Subgroup.normal_subgroupOf_iff (le_inf hJ₀H hJ₀C)]
    intro h m hh hm
    obtain ⟨a, ha, z, hz, rfl⟩ := hdecomp m hm.1
    have hzc : h * z = z * h := Subgroup.mem_center_iff.1 hz h
    have : a * z * h * (a * z)⁻¹ = a * h * a⁻¹ := by
      calc a * z * h * (a * z)⁻¹ = a * (z * h) * z⁻¹ * a⁻¹ := by group
        _ = a * (h * z) * z⁻¹ * a⁻¹ := by rw [hzc]
        _ = a * h * a⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hh) (Subgroup.inv_mem _ ha)
  haveI hJ₀perfect : Group.IsPerfect ↥(⁅H, H⁆ : Subgroup G) := Subgroup.isPerfect_iff.2 hJ₀perf
  let φ : ↥(⁅H, H⁆ : Subgroup G) →* ↥JT :=
    (σ.comp (⁅H, H⁆ : Subgroup G).subtype).codRestrict JT (fun j => hJ₀H j.2)
  have hφsurj : Function.Surjective φ := by
    intro b
    have hb : (b : T) ∈ (⁅H, H⁆ : Subgroup G).map σ := by
      rw [hJ₀map]
      exact b.2
    obtain ⟨a, ha, hab⟩ := hb
    exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  have hφker : φ.ker ≤ Subgroup.center ↥(⁅H, H⁆ : Subgroup G) := by
    intro j hj
    have h1 : σ (j : G) = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hj)
    have h2 : (j : G) ∈ Subgroup.center G := hker h1
    exact Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 h2 y)
  obtain ⟨hq, ⟨he⟩⟩ := perfect_cover hJ₀perfect.commutator_eq_top hJT.2.2 φ hφsurj hφker
  have hcent : ∀ d : G, σ d ∈ Subgroup.centralizer (JT : Set T) →
      d ∈ Subgroup.centralizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
    intro d hd
    have hz : ⁅(⁅H, H⁆ : Subgroup G), (Subgroup.centralizer (JT : Set T)).comap σ⁆ ≤
        Subgroup.center G := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      have hσb : σ b ∈ Subgroup.centralizer (JT : Set T) := hb
      exact Subgroup.mem_centralizer_iff.1 hσb (σ a) (hJ₀H ha)
    have hbot : ⁅(⁅H, H⁆ : Subgroup G), (Subgroup.centralizer (JT : Set T)).comap σ⁆ = ⊥ := by
      refine CFSG.ComponentClassification.Quasisimple.perfect_double_commutator _ _ ?_
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hz.trans (Subgroup.center_le_centralizer _)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.1 (hbot ha) d hd).symm
  exact ⟨⁅H, H⁆, hJ₀C, hJ₀map, hsub, hq, ⟨he⟩, hcent⟩

end Lift

section CenterQuot

variable {Ω : Type} [Group Ω] {S : Subgroup Ω} {T : Type} [Group T]

@[expose] def centerQuotHom (e : ↥S ⧸ Subgroup.center ↥S ≃* T) : ↥S →* T :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))

theorem centerQuotHom_surjective (e : ↥S ⧸ Subgroup.center ↥S ≃* T) :
    Function.Surjective (centerQuotHom e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem centerQuotHom_eq_one_iff (e : ↥S ⧸ Subgroup.center ↥S ≃* T) (s : ↥S) :
    centerQuotHom e s = 1 ↔ s ∈ Subgroup.center ↥S := by
  change e (QuotientGroup.mk s) = 1 ↔ _
  rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]

end CenterQuot

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]

section Setup

theorem exists_conj_of_inducesInner {S : Subgroup Ω} {x : Ω}
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hin : InducesInnerMod p S x) :
    ∃ l ∈ S, ∀ y ∈ S, x⁻¹ * y * x = l⁻¹ * y * l := by
  obtain ⟨l, hl, h⟩ := hin
  refine ⟨l, hl, fun y hy => ?_⟩
  have h1 := h y hy
  have h2 : GLAPPrimeCoreOf p S = ⊥ := by
    show (GLAPPrimeCore p ↥S).map S.subtype = ⊥
    rw [hSp, Subgroup.map_bot]
  rw [h2, Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact h1.symm

theorem commute_x_iff_commute_l_of_conj {S : Subgroup Ω} {x l : Ω}
    (hconj : ∀ y ∈ S, x⁻¹ * y * x = l⁻¹ * y * l) {s : Ω} (hs : s ∈ S) :
    s * x = x * s ↔ s * l = l * s := by
  have h := hconj s hs
  constructor
  · intro hsx
    have h1 : x⁻¹ * s * x = s := by rw [mul_assoc, hsx, inv_mul_cancel_left]
    rw [h1] at h
    calc s * l = l * (l⁻¹ * s * l) := by group
      _ = l * s := by rw [← h]
  · intro hsl
    have h1 : l⁻¹ * s * l = s := by rw [mul_assoc, hsl, inv_mul_cancel_left]
    rw [h1] at h
    calc s * x = x * (x⁻¹ * s * x) := by group
      _ = x * s := by rw [h]

private theorem pow_comm_of_conj {S : Subgroup Ω} {x l : Ω} (hl : l ∈ S)
    (hconj : ∀ y ∈ S, x⁻¹ * y * x = l⁻¹ * y * l) (hxp : x ^ p = 1) :
    ∀ y ∈ S, y * l ^ p = l ^ p * y := by
  have hc : ∀ y ∈ S, y * (x * l⁻¹) = (x * l⁻¹) * y := by
    intro y hy
    calc y * (x * l⁻¹) = x * (x⁻¹ * y * x) * l⁻¹ := by group
      _ = x * (l⁻¹ * y * l) * l⁻¹ := by rw [hconj y hy]
      _ = x * l⁻¹ * y := by group
  have hcomm : Commute (x * l⁻¹) l := (hc l hl).symm
  have h1 : (x * l⁻¹) ^ p * l ^ p = 1 := by
    rw [← hcomm.mul_pow, show x * l⁻¹ * l = x by group]
    exact hxp
  have hl' : l ^ p = ((x * l⁻¹) ^ p)⁻¹ := eq_inv_of_mul_eq_one_right h1
  intro y hy
  rw [hl']
  exact ((Commute.pow_right (hc y hy) p).inv_right).eq

private theorem mem_centralizer_of_central {S : Subgroup Ω} {x l : Ω}
    (hconj : ∀ y ∈ S, x⁻¹ * y * x = l⁻¹ * y * l) (hl : ∀ y ∈ S, y * l = l * y) :
    x ∈ Subgroup.centralizer (S : Set Ω) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h := hconj y hy
  have h1 : l⁻¹ * y * l = y := by rw [mul_assoc, hl y hy, inv_mul_cancel_left]
  rw [h1] at h
  calc y * x = x * (x⁻¹ * y * x) := by group
    _ = x * y := by rw [h]

theorem exists_conj_element {S : Subgroup Ω} {x : Ω} (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hin : InducesInnerMod p S x) (hxp : x ^ p = 1)
    (hxC : x ∉ Subgroup.centralizer (S : Set Ω)) :
    ∃ l₀ : ↥S, (∀ y ∈ S, x⁻¹ * y * x = (l₀ : Ω)⁻¹ * y * (l₀ : Ω)) ∧
      l₀ ^ p ∈ Subgroup.center ↥S ∧ l₀ ∉ Subgroup.center ↥S := by
  obtain ⟨l, hl, hconj⟩ := exists_conj_of_inducesInner hSp hin
  refine ⟨⟨l, hl⟩, hconj, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact pow_comm_of_conj hl hconj hxp y y.2
  · intro hc
    apply hxC
    refine mem_centralizer_of_central hconj fun y hy => ?_
    have := Subgroup.mem_center_iff.1 hc ⟨y, hy⟩
    exact congrArg Subtype.val this

private theorem dvd_card_centerQuot {S : Subgroup Ω} (hp : p.Prime) {l₀ : ↥S}
    (hl₀p : l₀ ^ p ∈ Subgroup.center ↥S) (hl₀ : l₀ ∉ Subgroup.center ↥S) :
    p ∣ Nat.card (↥S ⧸ Subgroup.center ↥S) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : (QuotientGroup.mk l₀ : ↥S ⧸ Subgroup.center ↥S) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hl₀p
  have h2 : (QuotientGroup.mk l₀ : ↥S ⧸ Subgroup.center ↥S) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hl₀
  rw [← orderOf_eq_prime h1 h2]
  exact orderOf_dvd_natCard _

theorem eq_bot_of_isPGroup_two_le_center {G : Type} [Group G] [Finite G] (hp : p.Prime)
    (hp2 : p ≠ 2) (hG : GLAPPrimeCore p G = ⊥) {N : Subgroup G} (hN2 : IsPGroup 2 ↥N)
    (hNz : N ≤ Subgroup.center G) : N = ⊥ := by
  haveI : N.Normal := Subgroup.normal_of_le_center hNz
  obtain ⟨k, hk⟩ := hN2.exists_card_eq
  have hcop : Nat.Coprime p (Nat.card N) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hle : N ≤ GLAPPrimeCore p G :=
    le_sSup (show N ∈ {K : Subgroup G | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
      ⟨inferInstance, hcop⟩)
  rw [hG] at hle
  exact le_bot_iff.1 hle

theorem map_centerQuotHom_ne_bot (hp : p.Prime) (hp2 : p ≠ 2) {S S₁ : Subgroup Ω}
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hS₁ : S₁ ≠ ⊥) (hS₁S : S₁ ≤ S) (hS₁2 : IsPGroup 2 ↥S₁)
    {T : Type} [Group T] (e : ↥S ⧸ Subgroup.center ↥S ≃* T) :
    (S₁.subgroupOf S).map (centerQuotHom e) ≠ ⊥ := by
  intro h
  apply hS₁
  have h1 := Subgroup.map_subgroupOf_eq_of_le hS₁S
  have h2 : S₁.subgroupOf S = ⊥ := by
    refine eq_bot_of_isPGroup_two_le_center hp hp2 hSp hS₁2.comap_subtype fun s hs => ?_
    refine (centerQuotHom_eq_one_iff e s).1 ?_
    have : centerQuotHom e s ∈ (S₁.subgroupOf S).map (centerQuotHom e) :=
      Subgroup.mem_map_of_mem _ hs
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  rw [h2, Subgroup.map_bot] at h1
  exact h1.symm

private theorem mem_sup_of_commute' {G : Type*} [Group G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {g : G} (hg : g ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, g = h * k := by
  let S : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        have := hc h₂ hh₂ k₁ hk₁
        calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
          _ = h₁ * (h₂ * k₁) * k₂ := by rw [this]
          _ = h₁ * h₂ * (k₁ * k₂) := by group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        exact Commute.mul_inv (hc h hh k hk) }
  exact (sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩) : H ⊔ K ≤ S) hg

private theorem centFix_zpowers_eq {X : Type*} [Group X] (β : MulAut X) :
    CFSG.LocalAnalysis.GLTheoremA.I142.centFix (Subgroup.zpowers β) =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β := by
  ext x
  rw [CFSG.LocalAnalysis.GLTheoremA.I142.mem_centFix,
    CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
  constructor
  · intro h
    exact h β (Subgroup.mem_zpowers β)
  · intro hx e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    have hβs : β ∈ MulAction.stabilizer (MulAut X) x := MulAction.mem_stabilizer_iff.2 hx
    exact MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer (MulAut X) x).zpow_mem hβs k)

private theorem fixSubgroup_conj_eq {X : Type*} [Group X] (r : X) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj r) =
      Subgroup.centralizer ({r} : Set X) := by
  ext y
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup,
    Subgroup.mem_centralizer_singleton_iff]
  change r * y * r⁻¹ = y ↔ y * r = r * y
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

private theorem center_eq_bot_of_simple {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases (Subgroup.center X).normal_of_le_center le_rfl |>.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have : a ∈ Subgroup.center X := by rw [h]; trivial
    exact hab (Subgroup.mem_center_iff.1 this b).symm

private theorem rawDatum_twD_two_iff (n : ℕ) (Q : CFSG.Assembly.LargeEvenRawCont) :
    CFSG.Assembly.LargeEvenRawDatum ⟨.twD, 2, n⟩ Q ↔
      CFSG.Assembly.LargeEvenRawDatum ⟨.A, 1, 2 * n⟩ Q := by
  have h : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  simp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeLinear, h]
  rfl

private theorem inLambda2_A_two_mul (n : ℕ) (hn : 1 ≤ n) :
    CFSG.Assembly.LargeEvenInLambda2 ⟨.A, 1, 2 * n⟩ := by
  refine ⟨by simp only; omega, ?_⟩
  simp only
  exact ⟨le_rfl, fun _ => by omega⟩

private theorem two_le_rank_of_twD {lab : CFSG.Assembly.LargeEvenLabel}
    (hlam : CFSG.Assembly.LargeEvenInLambda2 lab) (htag : lab.tag = .twD) : 2 ≤ lab.rank := by
  have := hlam.2
  rw [htag] at this
  exact this

theorem exists_markedInnDiag {S : Subgroup Ω} {x : Ω} (hp : p.Prime)
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hdvd : p ∣ Nat.card (↥S ⧸ Subgroup.center ↥S))
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) : ∃ lab : GLALabel, MarkedInnDiag S x lab := by
  have hPC : GLAPComponent p S S :=
    glaPComponent_of_isComponentOf_of_dvd hp ⟨le_rfl, IsSubnormal.refl S, hSq⟩ hdvd
  obtain ⟨hperf, lab, hlab, hraw⟩ := (S10.innDiagOn_iff hPC hSq).2 hInn
  refine ⟨lab, hperf, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R' _ I' F' ⟨hs', hna', θ', -, hind'⟩
  exact ⟨hs', hna', θ', rfl, hind' x (Subgroup.mem_zpowers x)⟩

private theorem rawDatum_twD_two_one_iff (Q : CFSG.Assembly.LargeEvenRawCont) :
    CFSG.Assembly.LargeEvenRawDatum ⟨.twD, 2, 1⟩ Q ↔ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 4 ∧ Q (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin 2) K))
        (CFSG.Assembly.LargeEvenMatConjImage (CFSG.Assembly.LargeEvenProjMk _) Set.univ)
        (CFSG.Assembly.LargeEvenMatFieldImage (CFSG.Assembly.LargeEvenProjMk _)) := Iff.rfl

private theorem card_proj_sl_two_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nat.card (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin 2) K)) = 60 := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 2)
    (by norm_num)
  rw [hK] at h
  have hEq : CFSG.Assembly.LargeEvenSLGroup (Fin 2) K = CFSG.Open.StatedSL 2 K :=
    (CFSG.Open.StatedAPI.statedSL_eq_ker_det 2 K).symm
  rw [hEq]
  refine h.trans ?_
  decide

theorem card_centerQuot_of_label_twD {J : Type} [Group J]
    {lab : CFSG.Assembly.LargeEvenLabel} (hlab : lab = ⟨.twD, 2, 1⟩)
    (hraw : CFSG.Assembly.LargeEvenRawDatum lab fun R _ _ _ =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ ∃ _ : J ⧸ Subgroup.center J ≃* R, lab.n = 1) :
    Nat.card (J ⧸ Subgroup.center J) = 60 := by
  subst hlab
  obtain ⟨K, _, _, hK, -, -, θ, -⟩ := (rawDatum_twD_two_one_iff _).1 hraw
  rw [Nat.card_congr θ.toEquiv]
  exact card_proj_sl_two_four hK

end Setup

structure SelCompCore (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B₀ T' : Subgroup Ω) (x : Ω)
    (J : Subgroup Ω) : Prop where
  comp : IsComponentOf J (S ⊓ Subgroup.centralizer ({x} : Set Ω))
  pdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)
  act : ⁅(⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω), J⁆ ≠ ⊥
  inn : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
    J ⊔ (S ⊓ Subgroup.centralizer ({x} : Set Ω) ⊓ Subgroup.centralizer (J : Set Ω))
  chev : IsChevSimple 2 (↥J ⧸ Subgroup.center ↥J)

theorem SelCompCore.toSelComp {S B₀ T' : Subgroup Ω} {x : Ω} {J : Subgroup Ω}
    (h : SelCompCore p S B₀ T' x J)
    (hgf : p = 3 → ¬ GLAMarking (↥J) (fun lab _ _ _ _ _ => lab.n = 1)) :
    SelComp p S B₀ T' x J :=
  ⟨h.comp, h.pdvd, h.act, h.inn, h.chev, hgf⟩

section ChevCerts

theorem selCompCore_of_component (hp : p.Prime) (hp2 : p ≠ 2) {S B₀ T' : Subgroup Ω} {x : Ω}
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hSc : IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S))
    {l₀ : ↥S} (hconj : ∀ y ∈ S, x⁻¹ * y * x = (l₀ : Ω)⁻¹ * y * (l₀ : Ω))
    (hl₀p : l₀ ^ p ∈ Subgroup.center ↥S) (hl₀nc : l₀ ∉ Subgroup.center ↥S)
    (hS₁S : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
      S ⊓ Subgroup.centralizer ({x} : Set Ω))
    {T : Type} [Group T] [Finite T] (e : ↥S ⧸ Subgroup.center ↥S ≃* T) {P JT : Subgroup T}
    (hP : P = ((⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω).subgroupOf S).map
      (centerQuotHom e))
    (hJTc : IsComponentOf JT (Subgroup.centralizer ({centerQuotHom e l₀} : Set T)))
    (hJTp : p ∣ Nat.card (↥JT ⧸ Subgroup.center ↥JT)) (hJTa : ⁅P, JT⁆ ≠ ⊥)
    (hJTP : P ≤ JT ⊔ (Subgroup.centralizer ({centerQuotHom e l₀} : Set T) ⊓
      Subgroup.centralizer (JT : Set T))) :
    ∃ J : Subgroup Ω, SelCompCore p S B₀ T' x J := by
  subst hP
  set S₁ : Subgroup Ω := ⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ with hS₁def
  let σ : ↥S →* T := centerQuotHom e
  have hσs : Function.Surjective σ := centerQuotHom_surjective e
  have hσk : ∀ s : ↥S, σ s = 1 ↔ s ∈ Subgroup.center ↥S := centerQuotHom_eq_one_iff e
  have hσker : σ.ker ≤ Subgroup.center ↥S := fun s hs => (hσk s).1 hs
  have hrp : (σ l₀) ^ p = 1 := by
    rw [← map_pow]
    exact (hσk _).2 hl₀p
  have hr1 : σ l₀ ≠ 1 := fun h => hl₀nc ((hσk l₀).1 h)
  set S₁' : Subgroup ↥S := S₁.subgroupOf S with hS₁'
  obtain ⟨J₀, hJ₀C, hJ₀map, hJ₀sub, hJ₀q, ⟨hJ₀e⟩, hJ₀cent⟩ :=
    lift_component σ hσs hσker l₀ hJTc
  let ρ : ↥J₀ ≃* ↥(J₀.map S.subtype) :=
    Subgroup.equivMapOfInjective J₀ S.subtype S.subtype_injective
  have hCeq : Subgroup.centralizer ({l₀} : Set ↥S) =
      (Subgroup.centralizer ({x} : Set Ω)).subgroupOf S := by
    ext s
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    have := (commute_x_iff_commute_l_of_conj hconj s.2).symm
    constructor
    · intro h
      exact this.1 (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext (this.2 h)
  have hmapC : ((Subgroup.centralizer ({x} : Set Ω)).subgroupOf S).map S.subtype =
      S ⊓ Subgroup.centralizer ({x} : Set Ω) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hJX : J₀.map S.subtype ≤ S ⊓ Subgroup.centralizer ({x} : Set Ω) := by
    rw [← hmapC, ← hCeq]
    exact Subgroup.map_mono hJ₀C
  have hJsub : IsSubnormal (J₀.map S.subtype) (S ⊓ Subgroup.centralizer ({x} : Set Ω)) := by
    have := hJ₀sub.map S.subtype
    rwa [hCeq, hmapC] at this
  have hJq : CFSG.Open.IsQuasisimple ↥(J₀.map S.subtype) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv ρ.symm hJ₀q
  obtain ⟨ε₁⟩ := nonempty_centerQuot_equiv ρ.symm
  have ε := ε₁.trans hJ₀e
  refine ⟨J₀.map S.subtype, ⟨⟨hJX, hJsub, hJq⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [Nat.card_congr ε.toEquiv]
    exact hJTp
  · intro hbot
    apply hJTa
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hJ₀map] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot (show (s : Ω) ∈ S₁ from hs)
    have h2 : (j : Ω) * s = s * j :=
      Subgroup.mem_centralizer_iff.1 h1 (j : Ω) (Subgroup.mem_map_of_mem S.subtype hj)
    change σ j * σ s = σ s * σ j
    rw [← map_mul, ← map_mul]
    exact congrArg σ (Subtype.ext h2)
  · intro s hs
    have hsS : s ∈ S := (hS₁S hs).1
    have hsC : s ∈ Subgroup.centralizer ({x} : Set Ω) := (hS₁S hs).2
    have hmem : σ ⟨s, hsS⟩ ∈ JT ⊔ (Subgroup.centralizer ({σ l₀} : Set T) ⊓
        Subgroup.centralizer (JT : Set T)) :=
      hJTP (Subgroup.mem_map_of_mem σ (show (⟨s, hsS⟩ : ↥S) ∈ S₁' from hs))
    obtain ⟨b, hb, c, hc, hbc⟩ := mem_sup_of_commute' (H := JT)
      (K := Subgroup.centralizer ({σ l₀} : Set T) ⊓ Subgroup.centralizer (JT : Set T))
      (fun a ha c hc => Subgroup.mem_centralizer_iff.1 hc.2 a ha) hmem
    rw [← hJ₀map] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    set d : ↥S := j⁻¹ * ⟨s, hsS⟩ with hd
    have hσd : σ d = c := by
      rw [hd, map_mul, map_inv, hbc]
      exact inv_mul_cancel_left _ _
    have hdcent : d ∈ Subgroup.centralizer (J₀ : Set ↥S) :=
      hJ₀cent d (by rw [hσd]; exact hc.2)
    have hjJ : (j : Ω) ∈ J₀.map S.subtype := Subgroup.mem_map_of_mem S.subtype hj
    have hdD : (d : Ω) ∈ S ⊓ Subgroup.centralizer ({x} : Set Ω) ⊓
        Subgroup.centralizer ((J₀.map S.subtype : Subgroup Ω) : Set Ω) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨d.2, ?_⟩, ?_⟩
      · have hjC := (hJX hjJ).2
        have : (d : Ω) = (j : Ω)⁻¹ * s := rfl
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hjC) hsC
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨j', hj', rfl⟩
        exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hdcent j' hj')
    have hs_eq : s = (j : Ω) * (d : Ω) := by
      simp [hd]
    rw [hs_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hjJ) (Subgroup.mem_sup_right hdD)
  · have hTs : IsSimpleGroup T := by
      haveI : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
      exact e.symm.isSimpleGroup
    have hTnc : ∃ a b : T, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := (native_of_open_dx hSq).2.2
      exact ⟨e a, e b, fun h => hab (e.injective (by rwa [map_mul, map_mul]))⟩
    have hβp : (MulAut.conj (σ l₀)) ^ p = 1 := by rw [← map_pow, hrp, map_one]
    have hβ1 : MulAut.conj (σ l₀) ≠ 1 := by
      intro h
      apply hr1
      have hz : σ l₀ ∈ Subgroup.center T := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 : σ l₀ * g * (σ l₀)⁻¹ = g := by
          have := congrArg (fun f : MulAut T => f g) h
          simpa [MulAut.conj_apply] using this
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1.symm
      rw [center_eq_bot_of_simple hTs hTnc] at hz
      exact Subgroup.mem_bot.1 hz
    have hcomp : IsComponentOf JT (CFSG.LocalAnalysis.GLTheoremA.I142.centFix
        (Subgroup.zpowers (MulAut.conj (σ l₀)))) := by
      rw [centFix_zpowers_eq, fixSubgroup_conj_eq]
      exact hJTc
    exact isChevSimple_of_equiv ε.symm
      (CFSG.LocalAnalysis.GLTheoremA.I142M.Three.chevCompTypes_holds T hTs hTnc
        (isChevSimple_of_equiv e hSc) p hp hp2 _ hβp hβ1 JT hcomp)

private theorem selCompCore_of_modelSel (hp : p.Prime) (hp2 : p ≠ 2) {S B₀ T' : Subgroup Ω} {x : Ω}
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hSc : IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S))
    (hxp : x ^ p = 1) (hxC : x ∉ Subgroup.centralizer (S : Set Ω))
    (hin : InducesInnerMod p S x)
    (hS₁ : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≠ ⊥)
    (hS₁S : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
      S ⊓ Subgroup.centralizer ({x} : Set Ω))
    (hS₁2 : IsPGroup 2 ↥(⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω))
    {T : Type} [Group T] [Finite T] (e : ↥S ⧸ Subgroup.center ↥S ≃* T) (hT : ModelSel p T) :
    ∃ J : Subgroup Ω, SelCompCore p S B₀ T' x J := by
  obtain ⟨l₀, hconj, hl₀p, hl₀nc⟩ := exists_conj_element hSp hin hxp hxC
  set S₁ : Subgroup Ω := ⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ with hS₁def
  let σ : ↥S →* T := centerQuotHom e
  have hσk : ∀ s : ↥S, σ s = 1 ↔ s ∈ Subgroup.center ↥S := centerQuotHom_eq_one_iff e
  have hrp : (σ l₀) ^ p = 1 := by
    rw [← map_pow]
    exact (hσk _).2 hl₀p
  have hr1 : σ l₀ ≠ 1 := fun h => hl₀nc ((hσk l₀).1 h)
  set S₁' : Subgroup ↥S := S₁.subgroupOf S with hS₁'
  set P : Subgroup T := S₁'.map σ with hP
  have hPC : P ≤ Subgroup.centralizer ({σ l₀} : Set T) := by
    rintro _ ⟨s, hs, rfl⟩
    have hsx : (s : Ω) * x = x * s :=
      Subgroup.mem_centralizer_singleton_iff.1 (hS₁S (show (s : Ω) ∈ S₁ from hs)).2
    have hsl : (s : Ω) * l₀ = l₀ * s := (commute_x_iff_commute_l_of_conj hconj s.2).1 hsx
    rw [Subgroup.mem_centralizer_singleton_iff]
    change σ s * σ l₀ = σ l₀ * σ s
    rw [← map_mul, ← map_mul]
    exact congrArg σ (Subtype.ext hsl)
  have hS₁'2 : IsPGroup 2 ↥S₁' := hS₁2.comap_subtype
  have hP2 : IsPGroup 2 ↥P := hS₁'2.map σ
  have hPne : P ≠ ⊥ :=
    map_centerQuotHom_ne_bot hp hp2 hSp hS₁ (hS₁S.trans inf_le_left) hS₁2 e
  obtain ⟨JT, hJTc, hJTp, hJTa, hJTP⟩ := hT (σ l₀) hrp hr1 P hPC hP2 hPne
  exact selCompCore_of_component hp hp2 hSq hSc hconj hl₀p hl₀nc hS₁S e rfl hJTc hJTp hJTa hJTP

end ChevCerts

section SubCerts

theorem labS_dvd_of_labelOf (hp : p.Prime) (hp2 : p ≠ 2) {S J : Subgroup Ω} {x : Ω}
    (hSn : S.Normal) (hxp : x ^ p = 1) (hxC : x ∉ Subgroup.centralizer (S : Set Ω))
    {labS lab : GLALabel} (hM : MarkedInnDiag S x labS)
    (hJ : IsComponentOf J (S ⊓ Subgroup.centralizer ({x} : Set Ω)))
    (hlam : CFSG.Assembly.LargeEvenInLambda2 lab) (hlab : LabelOf J lab) :
    labS.n ∣ lab.n ∨ (lab.tag = .twD ∧ lab.rank = 2 ∧ labS.n ∣ 2 * lab.n) := by
  have hN : x ∈ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top x
  by_cases htw : lab.tag = .twD ∧ lab.rank = 2
  · right
    refine ⟨htw.1, htw.2, ?_⟩
    obtain ⟨t, r, n⟩ := lab
    obtain ⟨rfl, rfl⟩ := htw
    have hlabA : LabelOf J ⟨.A, 1, 2 * n⟩ := by
      obtain ⟨hperf, lab', hlam', hraw⟩ := hlab
      obtain ⟨R, _, I, F, hs, hna, θ, hlabeq⟩ :=
        CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
      subst hlabeq
      refine ⟨hperf, ⟨.A, 1, 2 * n⟩, inLambda2_A_two_mul n hlam.1, ?_⟩
      refine (rawDatum_twD_two_iff n _).1 ?_
      exact CFSG.StandardType.Canonical.largeEvenRawDatum_mono
        (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw
    exact CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.subcompField_holds Ω S J x labS
      ⟨.A, 1, 2 * n⟩ p hp hp2 hxp hN hxC hM hJ hlabA (fun h => by cases h)
  · left
    have h3 : lab.tag = .twD → 3 ≤ lab.rank := by
      intro htag
      have h2 := two_le_rank_of_twD hlam htag
      have : lab.rank ≠ 2 := fun hr => htw ⟨htag, hr⟩
      omega
    exact CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.subcompField_holds Ω S J x labS lab p hp hp2
      hxp hN hxC hM hJ hlab h3

theorem selComp_or_a5_of_core (hp : p.Prime) (hp2 : p ≠ 2) {S B₀ T' : Subgroup Ω} {x : Ω}
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hF2 : p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1))
    (hxp : x ^ p = 1) (hxC : x ∉ Subgroup.centralizer (S : Set Ω))
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hin : InducesInnerMod p S x)
    {J : Subgroup Ω} (hJ : SelCompCore p S B₀ T' x J) :
    SelComp p S B₀ T' x J ∨
      (p = 3 ∧ IsComponentOf J (S ⊓ Subgroup.centralizer ({x} : Set Ω)) ∧
        Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) := by
  by_cases h3 : p = 3
  · subst h3
    by_cases hm : GLAMarking (↥J) (fun lab _ _ _ _ _ => lab.n = 1)
    · right
      refine ⟨rfl, hJ.comp, ?_⟩
      obtain ⟨l₀, -, hl₀p, hl₀nc⟩ := exists_conj_element hSp hin hxp hxC
      obtain ⟨labS, hMS⟩ := exists_markedInnDiag hp hSq (dvd_card_centerQuot hp hl₀p hl₀nc) hInn
      obtain ⟨hperf, lab, hlam, hraw⟩ := hm
      obtain ⟨R, _, I, F, hs, hna, θ, hn1⟩ :=
        CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
      have hlabJ : LabelOf J lab := by
        refine ⟨hperf, lab, hlam, ?_⟩
        exact CFSG.StandardType.Canonical.largeEvenRawDatum_mono
          (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw
      rcases labS_dvd_of_labelOf hp hp2 hSn hxp hxC hMS hJ.comp hlam hlabJ with
        h | ⟨htag, hrank, -⟩
      · exfalso
        rw [hn1] at h
        have hS1 : labS.n = 1 := Nat.dvd_one.1 h
        refine hF2 rfl (CFSG.StandardType.Canonical.largeEvenMarking_mono
          (fun lab' R _ I F θ h => ?_) hMS)
        rw [h.1]
        exact hS1
      · refine card_centerQuot_of_label_twD ?_ hraw
        obtain ⟨t, r, n⟩ := lab
        simp only at htag hrank hn1
        subst htag hrank hn1
        rfl
    · exact Or.inl (hJ.toSelComp fun _ => hm)
  · exact Or.inl (hJ.toSelComp fun h => absurd h h3)

end SubCerts

section AllCerts

theorem selComp_or_a5_of_modelSel (hp : p.Prime) (hp2 : p ≠ 2) {S B₀ T' : Subgroup Ω} {x : Ω}
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hSc : IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S))
    (hF2 : p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1))
    (hxp : x ^ p = 1) (hxC : x ∉ Subgroup.centralizer (S : Set Ω))
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hin : InducesInnerMod p S x)
    (hS₁ : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≠ ⊥)
    (hS₁S : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
      S ⊓ Subgroup.centralizer ({x} : Set Ω))
    (hS₁2 : IsPGroup 2 ↥(⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω))
    {T : Type} [Group T] [Finite T] (e : ↥S ⧸ Subgroup.center ↥S ≃* T) (hT : ModelSel p T) :
    ∃ J : Subgroup Ω, SelComp p S B₀ T' x J ∨
      (p = 3 ∧ IsComponentOf J (S ⊓ Subgroup.centralizer ({x} : Set Ω)) ∧
        Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) := by
  obtain ⟨J, hJ⟩ := selCompCore_of_modelSel hp hp2 hSq hSp hSc hxp hxC hin hS₁ hS₁S hS₁2 e hT
  exact ⟨J, selComp_or_a5_of_core hp hp2 hSn hSq hSp hF2 hxp hxC hInn hin hJ⟩

end AllCerts

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
