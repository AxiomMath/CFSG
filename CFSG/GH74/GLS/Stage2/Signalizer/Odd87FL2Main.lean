module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Tools
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Bridge
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Core
public import CFSG.GH74.GLS.Stage2.Signalizer.L48Sl2Facts
public import CFSG.GH74.Generic.Shapes
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage2.Local CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section XData

variable {A : Type} [Group A] (K : Subgroup A)

@[expose] def Ybar (X : Subgroup A) : Subgroup (↥K ⧸ center ↥K) :=
  (X.subgroupOf K).map (QuotientGroup.mk' (center ↥K))

theorem Ybar_mem (X : Subgroup A) (y : ↥K ⧸ center ↥K) :
    y ∈ Ybar K X ↔ ∃ x : ↥K, (x : A) ∈ X ∧ QuotientGroup.mk x = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem pgroup_inf_center_trivial {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ2 : IsPGroup 2 ↥(center ↥K)) (X : Subgroup A) (hX : IsPGroup p ↥X) (x : ↥K)
    (hxX : (x : A) ∈ X) (hxZ : x ∈ center ↥K) : x = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hX ⟨(x : A), hxX⟩
  obtain ⟨b, hb⟩ := IsPGroup.iff_orderOf.mp hZ2 ⟨x, hxZ⟩
  rw [Subgroup.orderOf_mk] at ha hb
  have hxx : orderOf (x : A) = orderOf x := Subgroup.orderOf_coe x
  have hab : p ^ a = 2 ^ b := by rw [← ha, ← hb, hxx]
  by_cases ha0 : a = 0
  · rw [ha0, pow_zero] at ha
    have h1 : (x : A) = 1 := orderOf_eq_one_iff.mp ha
    exact Subtype.ext h1
  · exfalso
    have : p ∣ 2 ^ b := hab ▸ dvd_pow_self p ha0
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem isPGroup_subgroupOf {p : ℕ} {X : Subgroup A} (hX : IsPGroup p ↥X) (hXK : X ≤ K) :
    IsPGroup p ↥(X.subgroupOf K) :=
  hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm

theorem isPGroup_Ybar {p : ℕ} {X : Subgroup A} (hX : IsPGroup p ↥X) (hXK : X ≤ K) :
    IsPGroup p ↥(Ybar K X) :=
  (isPGroup_subgroupOf K hX hXK).map (QuotientGroup.mk' (center ↥K))

theorem card_Ybar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZ2 : IsPGroup 2 ↥(center ↥K))
    {X : Subgroup A} (hX : IsPGroup p ↥X) (hXK : X ≤ K) :
    Nat.card ↥(Ybar K X) = Nat.card ↥X := by
  set Xk : Subgroup ↥K := X.subgroupOf K with hXk
  let ρ : ↥Xk →* ↥K ⧸ center ↥K := (QuotientGroup.mk' (center ↥K)).comp Xk.subtype
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : (x : ↥K) ∈ center ↥K := (QuotientGroup.eq_one_iff _).mp hx
    have hxX : ((x : ↥K) : A) ∈ X := x.2
    have := pgroup_inf_center_trivial K hp hp2 hZ2 X hX (x : ↥K) hxX hxZ
    exact Subtype.ext this
  have hrange : ρ.range = Ybar K X := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv

end XData

section ZData

variable {A : Type} [Group A] (K : Subgroup A) (z : A)

@[expose] def Cbar : Subgroup (↥K ⧸ center ↥K) :=
  ((K ⊓ centralizer ({z} : Set A)).subgroupOf K).map (QuotientGroup.mk' (center ↥K))

theorem Cbar_mem (c : ↥K ⧸ center ↥K) :
    c ∈ Cbar K z ↔ ∃ k : ↥K, (k : A) * z = z * (k : A) ∧ QuotientGroup.mk k = c := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Subgroup.mem_centralizer_singleton_iff.mp hk.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, ⟨k.2, Subgroup.mem_centralizer_singleton_iff.mpr hk⟩, rfl⟩

variable [K.Normal]

theorem Cbar_fix {c : ↥K ⧸ center ↥K} (hc : c ∈ Cbar K z) : actOnQuot K z c = c := by
  obtain ⟨k, hk, rfl⟩ := (Cbar_mem K z c).mp hc
  rw [actOnQuot_mk]
  congr 1
  apply Subtype.ext
  show z * (k : A) * z⁻¹ = k
  calc z * (k : A) * z⁻¹ = ((k : A) * z) * z⁻¹ := by rw [hk]
    _ = k := by group

theorem Ybar_alpha {X : Subgroup A} (hz : z ∈ normalizer (X : Set A)) {y : ↥K ⧸ center ↥K}
    (hy : y ∈ Ybar K X) : actOnQuot K z y ∈ Ybar K X := by
  obtain ⟨x, hx, rfl⟩ := (Ybar_mem K X y).mp hy
  rw [actOnQuot_mk]
  refine (Ybar_mem K X _).mpr ⟨_, ?_, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp hz _).mp hx

theorem mem_normalizer_of_conj {G : Type} [Group G] (Y C : Subgroup G)
    (h : ∀ c ∈ C, ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) : ∀ c ∈ C, c ∈ normalizer (Y : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h c hc y hy, fun hy => ?_⟩
  have := h c⁻¹ (C.inv_mem hc) _ hy
  simpa [mul_assoc] using this

theorem Cbar_normalizes {X : Subgroup A}
    (hinv : ∀ c ∈ centralizer ({z} : Set A), c ∈ normalizer (X : Set A)) :
    ∀ c ∈ Cbar K z, c ∈ normalizer ((Ybar K X : Subgroup (↥K ⧸ center ↥K)) : Set (↥K ⧸ center ↥K)) := by
  refine mem_normalizer_of_conj _ _ ?_
  intro c hc y hy
  obtain ⟨k, hk, rfl⟩ := (Cbar_mem K z c).mp hc
  obtain ⟨x, hx, rfl⟩ := (Ybar_mem K X y).mp hy
  refine (Ybar_mem K X _).mpr ⟨⟨(k : A) * x * (k : A)⁻¹, Subgroup.Normal.conj_mem inferInstance _ x.2 k⟩, ?_, ?_⟩
  · have hkn : (k : A) ∈ normalizer (X : Set A) :=
      hinv k (Subgroup.mem_centralizer_singleton_iff.mpr hk)
    exact (Subgroup.mem_normalizer_iff.mp hkn _).mp hx
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl

theorem Ybar_closure (hz2 : z * z = 1) {X : Subgroup A} (hz : z ∈ normalizer (X : Set A)) (hXK : X ≤ K)
    (hcomm : ⁅X, zpowers z⁆ = X) :
    Subgroup.closure {y : ↥K ⧸ center ↥K | ∃ x ∈ Ybar K X, y = x * (actOnQuot K z x)⁻¹} = Ybar K X := by
  set S : Set (↥K ⧸ center ↥K) := {y | ∃ x ∈ Ybar K X, y = x * (actOnQuot K z x)⁻¹} with hS
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (Ybar_alpha K z hz hx))
  · set W : Subgroup (↥K ⧸ center ↥K) := Subgroup.closure S with hW
    have hXW : X ≤ (W.comap (QuotientGroup.mk' (center ↥K))).map K.subtype := by
      rw [← hcomm, Subgroup.commutator_def, Subgroup.closure_le]
      rintro g ⟨x, hx, w, hw, rfl⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hz2' : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
      have hxK : x ∈ K := hXK hx
      rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
      · rw [zpow_mul, hz2', one_zpow, commutatorElement_one_right]
        exact (Subgroup.one_mem _)
      · rw [zpow_add_one, zpow_mul, hz2', one_zpow, one_mul]
        let x' : ↥K := ⟨x, hxK⟩
        let gx : ↥K := ⟨z * x * z⁻¹, Subgroup.Normal.conj_mem inferInstance _ hxK z⟩
        refine ⟨x' * gx⁻¹, ?_, ?_⟩
        · show QuotientGroup.mk (x' * gx⁻¹) ∈ W
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
          refine Subgroup.subset_closure ⟨QuotientGroup.mk x', (Ybar_mem K X _).mpr ⟨x', hx, rfl⟩, ?_⟩
          rw [actOnQuot_mk]
        · show x * (z * x * z⁻¹)⁻¹ = ⁅x, z⁆
          rw [commutatorElement_def]
          group
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (Ybar_mem K X y).mp hy
    obtain ⟨k, hk, hkx⟩ := hXW hx
    have : k = x := Subtype.ext hkx
    rw [← this]
    exact hk

theorem mk_mem_normalizer_Ybar {X : Subgroup A} {k : ↥K} (hk : (k : A) ∈ normalizer (X : Set A)) :
    (QuotientGroup.mk k : ↥K ⧸ center ↥K) ∈
      normalizer ((Ybar K X : Subgroup (↥K ⧸ center ↥K)) : Set (↥K ⧸ center ↥K)) := by
  have fwd : ∀ k : ↥K, (k : A) ∈ normalizer (X : Set A) → ∀ y ∈ Ybar K X,
      (QuotientGroup.mk k : ↥K ⧸ center ↥K) * y * (QuotientGroup.mk k)⁻¹ ∈ Ybar K X := by
    intro k hk y hy
    obtain ⟨x, hx, rfl⟩ := (Ybar_mem K X y).mp hy
    refine (Ybar_mem K X _).mpr
      ⟨⟨(k : A) * x * (k : A)⁻¹, Subgroup.Normal.conj_mem inferInstance _ x.2 k⟩, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hk _).mp hx
    · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rfl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fwd k hk y, fun hy => ?_⟩
  have hk' : ((k⁻¹ : ↥K) : A) ∈ normalizer (X : Set A) := (normalizer (X : Set A)).inv_mem hk
  have := fwd k⁻¹ hk' _ hy
  simpa [mul_assoc] using this

theorem inf_normalizer_le_of_decomp {X : Subgroup A} (hzZ : ∀ c ∈ center ↥K, z * (c : A) * z⁻¹ = c)
    (hNorm : ∀ m ∈ normalizer ((Ybar K X : Subgroup (↥K ⧸ center ↥K)) : Set (↥K ⧸ center ↥K)),
      ∃ y ∈ Ybar K X, ∃ c ∈ Cbar K z, m = y * c) :
    K ⊓ normalizer (X : Set A) ≤ X ⊔ K ⊓ centralizer ({z} : Set A) := by
  rintro n ⟨hnK, hnN⟩
  let n' : ↥K := ⟨n, hnK⟩
  obtain ⟨y, hy, c, hc, hm⟩ := hNorm (QuotientGroup.mk n') (mk_mem_normalizer_Ybar K (k := n') hnN)
  obtain ⟨x, hxX, rfl⟩ := (Ybar_mem K X y).mp hy
  obtain ⟨k, hk, rfl⟩ := (Cbar_mem K z c).mp hc
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq] at hm
  set ζ : ↥K := n'⁻¹ * (x * k) with hζ
  have hn : n = (x : A) * ((k : A) * ((ζ⁻¹ : ↥K) : A)) := by
    have : n' = x * (k * ζ⁻¹) := by rw [hζ]; group
    exact congrArg Subtype.val this
  have hζz : z * ((ζ⁻¹ : ↥K) : A) = ((ζ⁻¹ : ↥K) : A) * z := by
    have := hzZ (ζ⁻¹) ((center ↥K).inv_mem hm)
    calc z * ((ζ⁻¹ : ↥K) : A) = (z * ((ζ⁻¹ : ↥K) : A) * z⁻¹) * z := by group
      _ = ((ζ⁻¹ : ↥K) : A) * z := by rw [this]
  rw [hn]
  refine Subgroup.mul_mem_sup hxX ⟨K.mul_mem k.2 (ζ⁻¹).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  calc (k : A) * ((ζ⁻¹ : ↥K) : A) * z = (k : A) * (((ζ⁻¹ : ↥K) : A) * z) := by group
    _ = (k : A) * (z * ((ζ⁻¹ : ↥K) : A)) := by rw [hζz]
    _ = ((k : A) * z) * ((ζ⁻¹ : ↥K) : A) := by group
    _ = (z * (k : A)) * ((ζ⁻¹ : ↥K) : A) := by rw [hk]
    _ = z * ((k : A) * ((ζ⁻¹ : ↥K) : A)) := by group

end ZData


section Main

variable {A : Type} [Group A] [Finite A]

theorem isSylowOf_of_card_eq {p : ℕ} [Fact p.Prime] {K X : Subgroup A} (hXK : X ≤ K)
    (hX : IsPGroup p ↥X) {m : ℕ} (hcard : Nat.card ↥X * m = Nat.card ↥K) (hm : ¬ p ∣ m) :
    CFSG.ABGLocalTools.IsSylowOf p X K := by
  have hXk : IsPGroup p ↥(X.subgroupOf K) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
  have hidx : (X.subgroupOf K).index = m := by
    have h1 := Subgroup.card_mul_index (X.subgroupOf K)
    have h2 : Nat.card ↥(X.subgroupOf K) = Nat.card ↥X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv
    rw [h2] at h1
    have hpos : 0 < Nat.card ↥X := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hcard.symm)
  refine ⟨hXk.toSylow (by rw [hidx]; exact hm), ?_⟩
  exact Subgroup.map_subgroupOf_eq_of_le hXK

theorem fl2_core (hF : Generic.GenericKnownFacts) {z : A} (hz2 : z * z = 1) {p : ℕ} {X : Subgroup A}
    (hA : Sig4A z (⊤ : Subgroup A) p X) (hop : CFSG.pCore p A = ⊥)
    (hgen : layer A ⊔ X ⊔ zpowers z = ⊤) (hquasi : IsQuasisimple ↥(layer A))
    (hZcore : center ↥(layer A) = CFSG.pCore 2 ↥(layer A))
    (hL2 : FL2 (↥(layer A) ⧸ center ↥(layer A))) :
    (HasSL2Model ↥(layer A) (fun q => q = 5) ∧ Nat.card ↥X = 3 ∧ p = 3 ∧ X ≤ layer A ∧
        layer A ⊓ normalizer (X : Set A) ≤ X ⊔ layer A ⊓ centralizer ({z} : Set A)) ∨
      (∃ n : ℕ, 3 < p ^ n ∧ HasSL2Model ↥(layer A) (fun q => q = p ^ n) ∧
        CFSG.ABGLocalTools.IsSylowOf p X (layer A) ∧
        layer A ⊓ normalizer (X : Set A) ≤ X ⊔ layer A ⊓ centralizer ({z} : Set A)) := by
  classical
  have hKn : (layer A).Normal := by
    have hc : (layer A).Characteristic := LocalCores.layer_characteristic
    infer_instance
  set K : Subgroup A := layer A with hK
  obtain ⟨p₀, f, hp₀, hf, hp₀2, hLie⟩ := hL2
  obtain ⟨-, -, -, hpf3, F, _, _, hFcard, ⟨e0⟩⟩ :=
    ComponentClassification.AutL2Facts.lieModel_psl2_data hLie
  let e : (↥K ⧸ center ↥K) ≃* L2 F := e0.trans (L2.equivPSL F).symm
  have hoddF : Odd (Nat.card F) := by
    rw [hFcard]; exact (hp₀.odd_of_ne_two hp₀2).pow
  have hF3 : 3 < Nat.card F := by
    have h1 : p₀ ≤ p₀ ^ f := Nat.le_self_pow (by omega) p₀
    have h2 : 3 ≤ p₀ := by have := hp₀.two_le; omega
    have h3 : Nat.card F ≠ 3 := by rw [hFcard]; exact hpf3
    have : 3 ≤ Nat.card F := by rw [hFcard]; exact h2.trans h1
    omega
  have hFL : L2Field F := ⟨hoddF, hF3⟩
  have hZ2 : IsPGroup 2 ↥(center ↥K) := by
    rw [hZcore]; exact CFSG.pCore_isPGroup
  have hperf : commutator ↥K = ⊤ := by
    have := hquasi.1
    exact Group.IsPerfect.commutator_eq_top
  have hXK : X ≤ K := by
    refine x_le_layer_of_comm hz2 hA hop hgen ?_
    intro x _
    exact comm_mem_of_out_abelian K hperf (commutator_mem_innAut hFL e) x z
  have hcover := hF.psl2_cover p₀ f hp₀ hp₀2 ↥K hquasi hZ2 hLie
  have hcen : ∀ u ∈ center ↥K, ∀ v ∈ center ↥K, u ≠ 1 → v ≠ 1 → u = v := by
    rcases hcover with h | ⟨F', _, _, hF'c, ⟨eF'⟩⟩
    · intro u hu v hv hu1 _
      exfalso
      rw [h] at hu
      exact hu1 (by simpa using hu)
    · have hodd' : Odd (Nat.card F') := by
        rw [hF'c]; exact (hp₀.odd_of_ne_two hp₀2).pow
      exact (L48.sl2_facts hodd' eF').2.2.1
  have hZcard : Nat.card ↥(center ↥K) ≤ 2 := by
    have hinj : Function.Injective (fun u : ↥(center ↥K) => decide ((u : ↥K) ≠ 1)) := by
      intro u v huv
      by_cases hu : (u : ↥K) = 1
      · by_cases hv : (v : ↥K) = 1
        · exact Subtype.ext (hu.trans hv.symm)
        · simp [hu, hv] at huv
      · by_cases hv : (v : ↥K) = 1
        · simp [hu, hv] at huv
        · exact Subtype.ext (hcen u u.2 v v.2 hu hv)
    calc Nat.card ↥(center ↥K) ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
      _ = 2 := by simp
  have hc1 : 1 ≤ Nat.card ↥(center ↥K) := Nat.card_pos
  have hzZ : ∀ c ∈ center ↥K, z * (c : A) * z⁻¹ = c := by
    intro c hc
    let γ : MulAut ↥K := MulAut.conjNormal z
    have hγ : ∀ k : ↥K, ((γ k : ↥K) : A) = z * k * z⁻¹ := fun k => rfl
    have hγc : γ c ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := γ.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc g']
    by_cases hc1 : c = 1
    · rw [hc1]; simp
    · have hγ1 : γ c ≠ 1 := fun h => hc1 (by simpa using h)
      have h2 := congrArg Subtype.val (hcen _ hγc c hc hγ1 hc1)
      rw [hγ] at h2
      exact h2
  set α : MulAut (↥K ⧸ center ↥K) := actOnQuot K z with hα
  have hαα : α * α = 1 := by
    rw [hα, ← map_mul, hz2, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have hc : z ∈ centralizer (K : Set A) := centralizes_of_actOnQuot_eq_one K hperf h1
    apply hA.ne_bot
    rw [← hA.comm]
    refine le_bot_iff.mp ?_
    rw [Subgroup.commutator_le]
    intro x hx w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hxz : Commute x z := Subgroup.mem_centralizer_iff.mp hc x (hXK hx)
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_commute.mpr (hxz.zpow_right n)
  have hzn : z ∈ normalizer (X : Set A) := z_mem_normalizer_of_sig4A hA
  have hY : IsPGroup p ↥(Ybar K X) := isPGroup_Ybar K hA.pgroup hXK
  have hcardY : Nat.card ↥(Ybar K X) = Nat.card ↥X :=
    card_Ybar K hA.prime hA.odd hZ2 hA.pgroup hXK
  have hY1 : Ybar K X ≠ ⊥ := by
    intro h
    rw [h] at hcardY
    simp at hcardY
    exact hA.ne_bot (Subgroup.eq_bot_of_card_eq X hcardY.symm)
  have hbar := fl2_barcore hFL e α hαα hα1 hA.prime hA.odd (Ybar K X) hY hY1
    (fun y hy => Ybar_alpha K z hzn hy) (Ybar_closure K z hz2 hzn hXK hA.comm) (Cbar K z)
    (fun c hc => Cbar_fix K z hc)
    (Cbar_normalizes K z (fun c hcz => hA.inv c (Subgroup.mem_top c) hcz))
    hc1 hZcard (card_fixed_le K z hzZ)
  have hcenter_ne : Nat.card ↥(center ↥K) = 2 →
      ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = p₀ ^ f ∧
        Nonempty (↥K ≃* StatedSL 2 F') := by
    intro h2
    rcases hcover with h | h
    · exfalso
      rw [h] at h2
      simp at h2
    · exact h
  rcases hbar with ⟨hpF, hYq, hc2, hNorm⟩ | ⟨hpF, hc2, hq5, hY3, hp3, hNorm⟩
  · right
    obtain ⟨F', fF', finF', hF'c, ⟨eF'⟩⟩ := hcenter_ne hc2
    have hpp₀ : p = p₀ := by
      rw [hFcard] at hpF
      exact (Nat.prime_dvd_prime_iff_eq hA.prime hp₀).mp (hA.prime.dvd_of_dvd_pow hpF)
    subst hpp₀
    refine ⟨f, ?_, ⟨F', fF', finF', hF'c, ⟨eF'⟩⟩, ?_, inf_normalizer_le_of_decomp K z hzZ hNorm⟩
    · rw [← hFcard]; exact hF3
    · have : Fact p.Prime := ⟨hA.prime⟩
      refine isSylowOf_of_card_eq hXK hA.pgroup (m := Nat.card F ^ 2 - 1) ?_ ?_
      · have hXF : Nat.card ↥X = Nat.card F := hcardY.symm.trans hYq
        have hK1 : Nat.card ↥K = Nat.card (↥K ⧸ center ↥K) * Nat.card ↥(center ↥K) :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥K)
        rw [card_eq_of_L2Field e hFL, hc2] at hK1
        have h2 : 2 ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
          obtain ⟨k, hk⟩ := hoddF
          have : Nat.card F ^ 2 - 1 = 2 * (2 * k * k + 2 * k) := by
            apply Nat.sub_eq_of_eq_add
            rw [hk]; ring
          rw [this]
          exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
        rw [hK1, Nat.div_mul_cancel h2, hXF]
      · intro hdvd
        have h1 : p ∣ Nat.card F ^ 2 := by
          rw [hFcard]
          exact dvd_pow (dvd_pow_self p (by omega : f ≠ 0)) (by norm_num)
        have h3 : p ∣ Nat.card F ^ 2 - (Nat.card F ^ 2 - 1) := Nat.dvd_sub h1 hdvd
        have h4 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
        rw [Nat.sub_sub_self h4] at h3
        exact hA.prime.one_lt.ne' (Nat.dvd_one.mp h3)
  · left
    obtain ⟨F', fF', finF', hF'c, ⟨eF'⟩⟩ := hcenter_ne hc2
    refine ⟨⟨F', fF', finF', ?_, ⟨eF'⟩⟩, ?_, hp3, hXK, inf_normalizer_le_of_decomp K z hzZ hNorm⟩
    · rw [hF'c, ← hFcard, hq5]
    · rw [← hcardY, hY3]

end Main

theorem cell87_FL2 (hF : Generic.GenericKnownFacts) : Cell87 FL2 := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hL2
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hctx.central.1, pow_two] at this
  have hz2 : zSec z H₀ hz H₁ * zSec z H₀ hz H₁ = 1 := by
    have h1 : (⟨z, hz⟩ : ↥H₀) * ⟨z, hz⟩ = 1 := Subtype.ext hzz
    show QuotientGroup.mk (⟨z, hz⟩ : ↥H₀) * QuotientGroup.mk (⟨z, hz⟩ : ↥H₀) = 1
    rw [← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one]
  rcases fl2_core hF hz2 hsig.A hsig.op hyp.1 hyp.2.1 hyp.2.2.1 hL2 with h | h
  · first
      | exact Or.inl h
      | exact Or.inl ⟨h.1, h.2.1, h.2.2.1⟩
  · first
      | exact Or.inr (Or.inl h)
      | (obtain ⟨n, h1, h2, h3, -⟩ := h
         exact Or.inr (Or.inl ⟨n, h1, h2, h3⟩))


end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
