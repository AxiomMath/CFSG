module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelSemilinear
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.ShultStronglyClosedTI.CyclicSemiregular CFSG.ShultStronglyClosedTI.LinearChain
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped IsMulCommutative

theorem singerNormalizerCyclic : SingerNormalizerCyclic := by
  intro G _ _ Z D P hZ hZ1 hDN hDc hDreg hP2 hPN hPDC
  classical
  have hZc : IsMulCommutative Z := hZ.1
  let _ : Module (ZMod 2) (Additive Z) := AddCommGroup.zmodModule (n := 2) fun v => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (hZ.2 _ v.toMul.2)
  have : Finite (Additive Z) := inferInstanceAs (Finite Z)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : IsPGroup 2 Z := fun g => ⟨1, Subtype.ext (by simpa using hZ.2 g g.2)⟩
  obtain ⟨e, he⟩ := hZ2.exists_card_eq
  have he1 : 1 ≤ e := by
    by_contra h0
    have : e = 0 := by omega
    rw [this, pow_zero] at he
    exact hZ1 (Subgroup.card_eq_one.mp he)
  set N := normalizer (Z : Set G) with hNdef
  set C := centralizer (Z : Set G) with hCdef
  let ρ₀ : N →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z) :=
    (mulAutGL 2 Z).comp Z.normalizerMonoidHom
  have hρ₀ : ∀ (n : N) (v : Additive Z),
      ((((ρ₀ n : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) :
        Module.End (ZMod 2) (Additive Z)) v).toMul : G) = (n : G) * (v.toMul : G) * (n : G)⁻¹ :=
    fun _ _ => rfl
  have hρ₀ker : ∀ n : N, ρ₀ n = 1 ↔ (n : G) ∈ C := by
    intro n
    rw [hCdef, Subgroup.mem_centralizer_iff]
    constructor
    · intro hn x hx
      have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z) =>
        (((g : Module.End (ZMod 2) (Additive Z)) (Additive.ofMul ⟨x, hx⟩)).toMul : G)) hn
      simp only [hρ₀, toMul_ofMul, Units.val_one, Module.End.one_apply] at h1
      calc x * (n : G) = (n : G) * x * (n : G)⁻¹ * n := by rw [h1]
        _ = n * x := by group
    · intro hn
      apply Units.ext
      apply LinearMap.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hρ₀]
      change (n : G) * (v.toMul : G) * (n : G)⁻¹ = (v.toMul : G)
      rw [← hn _ v.toMul.2, mul_inv_cancel_right]
  have hCN : C ≤ N := by
    intro c hc
    rw [hNdef, Subgroup.mem_normalizer_iff]
    intro z
    have hc' := Subgroup.mem_centralizer_iff.mp hc
    constructor
    · intro hz
      have e : c * z * c⁻¹ = z := by rw [← hc' z hz]; group
      rw [e]
      exact hz
    · intro hz
      have hc'' := Subgroup.mem_centralizer_iff.mp (C.inv_mem hc)
      have h1 := hc'' _ hz
      have h2 : c * z * c⁻¹ * c⁻¹ = z * c⁻¹ := by
        calc c * z * c⁻¹ * c⁻¹ = c⁻¹ * (c * z * c⁻¹) := h1
          _ = z * c⁻¹ := by group
      have h3 : c * z * c⁻¹ = z := mul_right_cancel h2
      rw [← h3]
      exact hz
  have hNC : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
    intro n hn c hc
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : n⁻¹ * z * n⁻¹⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (N.inv_mem hn) z).mp hz
    have hc' := Subgroup.mem_centralizer_iff.mp hc _ hz'
    calc z * (n * c * n⁻¹) = n * ((n⁻¹ * z * n⁻¹⁻¹) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * z * n⁻¹⁻¹)) * n⁻¹ := by rw [hc']
      _ = (n * c * n⁻¹) * z := by group
  have hDC_mem : ∀ k ∈ D ⊔ C, ∃ c ∈ C, ∃ d ∈ D, k = c * d := by
    intro k hk
    have hle : D ≤ normalizer (C : Set G) :=
      le_normalizer_of_conj_mem fun g hg y hy => hNC g (hDN hg) y hy
    rw [sup_comm] at hk
    exact (mem_sup_iff_of_le_normalizer hle).mp hk
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.commGroup (α := D)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨⟨z₀, hz₀⟩, hz₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ1
  have hz₀1 : z₀ ≠ 1 := fun h => hz₀1' (Subtype.ext h)
  have hz₀Δ : z₀ ∈ nonIdentity Z := ⟨hz₀, hz₀1⟩
  set B₁ : Subgroup G := N ⊓ normalizer ((D ⊔ C : Subgroup G) : Set G) with hB₁
  have hB₁N : B₁ ≤ N := inf_le_left
  have hDB₁ : D ≤ B₁ := le_inf hDN (le_sup_left.trans Subgroup.le_normalizer)
  have hPB₁ : P ≤ B₁ := le_inf hPN hPDC
  let ρD : D →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z) :=
    ρ₀.comp (Subgroup.inclusion hDN)
  let ρB : B₁ →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z) :=
    ρ₀.comp (Subgroup.inclusion hB₁N)
  have hρD : ∀ d : D, ρD d = ρ₀ ⟨d, hDN d.2⟩ := fun _ => rfl
  have hρB : ∀ b : B₁, ρB b = ρ₀ ⟨b, hB₁N b.2⟩ := fun _ => rfl
  have hρD_inj : Function.Injective ρD := by
    rw [injective_iff_map_eq_one]
    intro d hd
    rw [hρD] at hd
    have hdC : (d : G) ∈ C := (hρ₀ker _).mp hd
    have hz := Subgroup.mem_centralizer_iff.mp hdC z₀ hz₀
    have hd1 := hDreg.2.2 z₀ hz₀Δ d d.2 (by
      calc (d : G)⁻¹ * z₀ * d = (d : G)⁻¹ * (z₀ * d) := by rw [mul_assoc]
        _ = (d : G)⁻¹ * (d * z₀) := by rw [hz]
        _ = z₀ := by group)
    exact Subtype.ext hd1
  have hDcard : Nat.card D = 2 ^ e - 1 := by
    let f : D → ↥(nonIdentity Z) := fun d => ⟨(d : G)⁻¹ * z₀ * d, hDreg.1 d d.2 z₀ hz₀Δ⟩
    have hf : Function.Bijective f := by
      constructor
      · intro d₁ d₂ h
        have h' : (d₁ : G)⁻¹ * z₀ * d₁ = (d₂ : G)⁻¹ * z₀ * d₂ := congrArg Subtype.val h
        have hfix : ((d₁ : G) * (d₂ : G)⁻¹)⁻¹ * z₀ * ((d₁ : G) * (d₂ : G)⁻¹) = z₀ := by
          calc ((d₁ : G) * (d₂ : G)⁻¹)⁻¹ * z₀ * ((d₁ : G) * (d₂ : G)⁻¹)
              = (d₂ : G) * ((d₁ : G)⁻¹ * z₀ * d₁) * (d₂ : G)⁻¹ := by group
            _ = (d₂ : G) * ((d₂ : G)⁻¹ * z₀ * d₂) * (d₂ : G)⁻¹ := by rw [h']
            _ = z₀ := by group
        have h1 := hDreg.2.2 z₀ hz₀Δ ((d₁ : G) * (d₂ : G)⁻¹)
          (D.mul_mem d₁.2 (D.inv_mem d₂.2)) hfix
        exact Subtype.ext (mul_inv_eq_one.mp h1)
      · rintro ⟨z, hz⟩
        obtain ⟨b, hb, hbz⟩ := hDreg.2.1 z₀ hz₀Δ z hz
        exact ⟨⟨b, hb⟩, Subtype.ext hbz⟩
    have h1 := Nat.card_congr (Equiv.ofBijective f hf)
    have h2 : Nat.card ↥(nonIdentity Z) = Nat.card Z - 1 := by
      have e1 : nonIdentity Z = (Z : Set G) \ {1} := by
        ext z
        simp [nonIdentity]
      rw [Nat.card_coe_set_eq, e1, Set.ncard_sdiff_singleton_of_mem Z.one_mem,
        ← Nat.card_coe_set_eq]
      rfl
    rw [h1, h2, he]
  let T : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) := ρD.range
  let Bgl : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) := ρB.range
  have hTB : T ≤ Bgl := by
    rintro _ ⟨d, rfl⟩
    exact ⟨⟨d, hDB₁ d.2⟩, rfl⟩
  let X : Subgroup Bgl := T.subgroupOf Bgl
  have hXcard : Nat.card X = 2 ^ e - 1 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTB).toEquiv, ← hDcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hρD_inj).toEquiv).symm
  have hXn : X.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨d, hd⟩ := hx
    obtain ⟨b, hb⟩ := g.2
    have hmem : (b : G) * (d : G) * (b : G)⁻¹ ∈ D ⊔ C :=
      (Subgroup.mem_normalizer_iff.mp b.2.2 d).mp (Subgroup.mem_sup_left d.2)
    obtain ⟨c, hc, d', hd', hcd⟩ := hDC_mem _ hmem
    refine ⟨⟨d', hd'⟩, ?_⟩
    have key : ρB b * ρD d * (ρB b)⁻¹ = ρD ⟨d', hd'⟩ := by
      rw [hρB, hρD, hρD, ← map_inv, ← map_mul, ← map_mul]
      have hN : (⟨(b : G), hB₁N b.2⟩ * ⟨(d : G), hDN d.2⟩ * ⟨(b : G), hB₁N b.2⟩⁻¹ : N) =
          ⟨c, hCN hc⟩ * ⟨d', hDN hd'⟩ := Subtype.ext (by simpa using hcd)
      rw [hN, map_mul, (hρ₀ker _).mpr hc, one_mul]
    rw [← key, hb, hd]
    rfl
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    obtain ⟨d₁, hd₁⟩ := ha
    obtain ⟨d₂, hd₂⟩ := hb
    apply Subtype.ext
    change (a : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) * b = b * a
    rw [← hd₁, ← hd₂, ← map_mul, ← map_mul]
    exact congrArg ρD (Subtype.ext (hDcomm _ d₁.2 _ d₂.2))
  have hne : ∀ v : Additive Z, v ≠ 0 → (v.toMul : G) ∈ nonIdentity Z := fun v hv =>
    ⟨v.toMul.2, fun h => hv (congrArg Additive.ofMul (Subtype.ext h))⟩
  have htrans : ∀ v w : Additive Z, v ≠ 0 → w ≠ 0 → ∃ x ∈ X,
      ((x : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) :
        Module.End (ZMod 2) (Additive Z)) v = w := by
    intro v w hv hw
    obtain ⟨b, hb, hbz⟩ := hDreg.2.1 _ (hne v hv) _ (hne w hw)
    refine ⟨⟨ρD ⟨b⁻¹, D.inv_mem hb⟩, hTB ⟨_, rfl⟩⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact ⟨_, rfl⟩
    · apply Additive.toMul.injective
      apply Subtype.ext
      change (((ρ₀ ⟨b⁻¹, hDN (D.inv_mem hb)⟩ : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) :
        Module.End (ZMod 2) (Additive Z)) v).toMul.1 = w.toMul.1
      rw [hρ₀]
      simpa using hbz
  have hXinj : ∀ x ∈ X, (Bgl.subtype x : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) = 1 →
      x = 1 := by
    intro x hx h1
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨d, hd⟩ := hx
    have hx1 : (x : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) = 1 := h1
    rw [← hd] at hx1
    have : d = 1 := hρD_inj (hx1.trans (map_one ρD).symm)
    apply Subtype.ext
    rw [← hd, this, map_one]
    rfl
  have hdim : Module.finrank (ZMod 2) (Additive Z) = e := by
    have h1 := FiniteField.pow_finrank_eq_natCard 2 (Additive Z)
    have h2 : Nat.card (Additive Z) = Nat.card Z := rfl
    rw [h2, he] at h1
    exact Nat.pow_right_injective (le_refl 2) h1
  obtain ⟨k₀, _, _, hk₀, ev, ι, hker, hcompat, himage⟩ :=
    semilinear_of_transitive_commutative (B := Bgl) (V := Additive Z) he1 hdim Bgl.subtype
      (X := X) hXcomm htrans hXinj hXcard
  have hunits : Nat.card k₀ˣ = 2 ^ e - 1 := by
    have : Fintype k₀ := Fintype.ofFinite k₀
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hk₀]
  let πP : P →* N := Subgroup.inclusion hPN
  have hφ0 : ∀ p : P, (ρ₀.comp πP) p ∈ Bgl := fun p => ⟨⟨p, hPB₁ p.2⟩, rfl⟩
  let φ : P →* Bgl := (ρ₀.comp πP).codRestrict Bgl hφ0
  let θ : P →* RingAut k₀ := (SemidirectProduct.rightHom).comp (ι.comp φ)
  have hθ : ∀ p : P, θ p = 1 → ρ₀ (πP p) = 1 := by
    intro p hp
    have hker1 : ι (φ p) ∈
        (SemidirectProduct.rightHom : k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀ →* RingAut k₀).ker := hp
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom] at hker1
    obtain ⟨c, hc⟩ := hker1
    obtain ⟨k, hk⟩ := hP2 p
    have hc1 : c ^ (2 ^ k) = 1 := by
      have h1 : (ι (φ p)) ^ (2 ^ k) = 1 := by
        rw [← map_pow, ← map_pow, hk, map_one, map_one]
      rw [← hc, ← map_pow] at h1
      exact SemidirectProduct.inl_injective (h1.trans (map_one _).symm)
    have hc2 : c = 1 := by
      have hdvd1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc1
      have hdvd2 : orderOf c ∣ 2 ^ e - 1 := hunits ▸ orderOf_dvd_natCard c
      have hodd : Odd (2 ^ e - 1) := by
        have h2 : 2 ^ e = 2 * 2 ^ (e - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        have h3 : 1 ≤ 2 ^ (e - 1) := Nat.one_le_two_pow
        exact ⟨2 ^ (e - 1) - 1, by omega⟩
      have hcop : Nat.Coprime (orderOf c) (2 ^ e - 1) :=
        Nat.Coprime.coprime_dvd_left hdvd1 (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd2)
    have h3 : ι (φ p) = 1 := by rw [← hc, hc2, map_one]
    have h4 : φ p ∈ ι.ker := h3
    rw [hker, Subgroup.ker_subtype] at h4
    exact congrArg Subtype.val (Subgroup.mem_bot.mp h4)
  have hθ_ker : ∀ p : P, θ p = 1 ↔ (p : G) ∈ C := by
    intro p
    constructor
    · intro hp
      exact (hρ₀ker _).mp (hθ p hp)
    · intro hp
      have h1 : ρ₀ (πP p) = 1 := (hρ₀ker (πP p)).mpr hp
      have h2 : φ p = 1 := Subtype.ext h1
      show SemidirectProduct.rightHom (ι (φ p)) = 1
      rw [h2, map_one, map_one]
  have : IsCyclic (RingAut k₀) := (card_ringAut_and_isCyclic Nat.prime_two k₀ hk₀).2
  have hcyc : IsCyclic θ.range := Subgroup.isCyclic θ.range
  obtain ⟨g₀, hg₀⟩ := hcyc.exists_generator
  obtain ⟨t, ht⟩ := g₀.2
  refine ⟨(t : G), t.2, le_antisymm ?_ (sup_le inf_le_left (Subgroup.zpowers_le.mpr t.2))⟩
  intro p hp
  have hmem := hg₀ ⟨θ ⟨p, hp⟩, ⟨_, rfl⟩⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hθk : θ (t ^ k) = θ ⟨p, hp⟩ := by
    rw [map_zpow, ht]
    exact congrArg Subtype.val hk
  have hker' : ((⟨p, hp⟩ * (t ^ k)⁻¹ : P) : G) ∈ C :=
    (hθ_ker _).mp (by rw [map_mul, map_inv, hθk, mul_inv_cancel])
  have hcoe : ((⟨p, hp⟩ * (t ^ k)⁻¹ : P) : G) = p * ((t : G) ^ k)⁻¹ := by simp
  rw [hcoe] at hker'
  have e : p = (p * ((t : G) ^ k)⁻¹) * (t : G) ^ k := by group
  rw [e]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left ⟨P.mul_mem hp (P.inv_mem (P.zpow_mem t.2 k)), hker'⟩)
    (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k))

end CFSG.QuasithinUnique.Lin2
